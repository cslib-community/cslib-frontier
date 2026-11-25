/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Quantum
public import CslibFrontier.Foundations.Data.MvPolynomial.AffineLine
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.EventBind

/-!
# The low individual degree test

The verifier of [Ji, Natarajan, Vidick, Wright and Yuen, Definition 3.2 and Figure 2]
[JNVWY2020LowIndividualDegree] tests assignments on a finite field.
It chooses uniformly among an axis-parallel line check, a point self-consistency check,
and a diagonal line check with a uniformly selected prefix of coordinates. A line question
carries its set of points. It reveals neither the sampled location on the line nor its
parameterization. Line answers are degree-bounded functions on the requested line.

Figure 2 samples the zero diagonal direction with positive probability. In this case its
displayed affine image is a singleton, which uses the same verifier predicate as other lines.
The dimension is positive because both line checks sample a coordinate.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Probability.PMF (uniformOfFintype)
open Finset

variable {F : Type*} {m : ℕ}

/-- An ambient point. -/
abbrev Point (F : Type*) (m : ℕ) := Fin m → F

/-- The query discloses the branch on a line question and only the location on a point question. -/
inductive Question (F : Type*) (m : ℕ) where
  | point (u : Point F m)
  | axis (line : Finset (Point F m))
  | diagonal (line : Finset (Point F m))
  deriving Fintype

/-- Both players use the same finite answer alphabet. A line answer carries its domain so that
the verifier can check it against the question. -/
abbrev Answer (F : Type*) (m : ℕ) := F ⊕ (Σ L : Finset (Point F m), L → F)

variable [Field F] [Fintype F] [DecidableEq F]

/-- The affine image sent to the line player. -/
@[expose] def linePoints (u v : Point F m) : Finset (Point F m) :=
  univ.image fun t : F => u + t • v

theorem mem_linePoints (u v : Point F m) (t : F) : u + t • v ∈ linePoints u v :=
  mem_image.mpr ⟨t, mem_univ t, rfl⟩

/-- Moving the base point along an affine line leaves its set of points unchanged. -/
theorem linePoints_translate_direction (u v : Point F m) (t : F) :
    linePoints (u + t • v) v = linePoints u v := by
  ext x
  simp only [linePoints, mem_image, mem_univ, true_and]
  exact ⟨fun ⟨s, hs⟩ => ⟨t + s, by rw [add_smul, ← add_assoc, hs]⟩,
    fun ⟨s, hs⟩ => ⟨s - t, by rw [← hs, add_assoc, ← add_smul, add_comm t, sub_add_cancel]⟩⟩

/-- A function on a line has degree at most `d` if it admits a parameterization by such a
univariate polynomial. This also describes the constant functions on singleton lines. -/
@[expose] def LineHasDegree {L : Finset (Point F m)} (f : L → F) (d : ℕ) : Prop :=
  ∃ (u v : Point F m) (hL : linePoints u v = L) (p : Polynomial F),
    p.natDegree ≤ d ∧
      ∀ t : F, f ⟨u + t • v, hL ▸ mem_linePoints u v t⟩ = p.eval t

/-- A degree-bounded line function has the same degree bound in any parameterization
of the queried affine image, including the singleton case. -/
theorem LineHasDegree.exists_polynomial {u v : Point F m} {f : linePoints u v → F} {d : ℕ}
    (h : LineHasDegree f d) :
    ∃ p : Polynomial F, p.natDegree ≤ d ∧
      ∀ t : F, f ⟨u + t • v, mem_linePoints u v t⟩ = p.eval t := by
  obtain ⟨u₀, v₀, hL, p, hp, he⟩ := h
  obtain ⟨a, -, ha⟩ := mem_image.mp
    (hL ▸ show u ∈ linePoints u v by simpa using mem_linePoints u v (0 : F))
  obtain ⟨b, -, hb⟩ := mem_image.mp
    (hL ▸ show u + v ∈ linePoints u v by simpa using mem_linePoints u v (1 : F))
  let q : Polynomial F := Polynomial.C a + Polynomial.C (b - a) * Polynomial.X
  have hq : q.natDegree ≤ 1 := Polynomial.natDegree_add_le_of_degree_le (by simp)
    ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
  refine ⟨p.comp q, Polynomial.natDegree_comp_le.trans (by simpa using Nat.mul_le_mul hp hq),
    fun t => ?_⟩
  have ht : u + t • v = u₀ + (a + (b - a) * t) • v₀ := funext fun i => by
    have hai : u₀ i + a * v₀ i = u i := congrFun ha i
    have hbi : u₀ i + b * v₀ i = u i + v i := congrFun hb i
    change u i + t * v i = u₀ i + (a + (b - a) * t) * v₀ i
    rw [show v i = (b - a) * v₀ i by linear_combination hai - hbi, ← hai]; ring
  rw [Polynomial.eval_comp, show q.eval t = a + (b - a) * t by simp [q], ← he]
  exact congrArg f (Subtype.ext ht)

/-- The line answer must have the right domain and degree, and agree with the point answer. -/
@[expose] def lineAgrees (d : ℕ) (L : Finset (Point F m)) (u : Point F m)
    (a : Σ L : Finset (Point F m), L → F) (b : F) : Prop :=
  a.1 = L ∧ LineHasDegree a.2 d ∧ ∃ h : u ∈ a.1, a.2 ⟨u, h⟩ = b

/-- The acceptance predicate with axis degree bound `d` and diagonal degree bound `D`. -/
@[expose] def acceptsWithDiagonalCap (d D : ℕ) :
    Question F m → Question F m → Answer F m → Answer F m → Prop
  | .point _, .point _, .inl a, .inl b => a = b
  | .axis L, .point u, .inr a, .inl b | .point u, .axis L, .inl b, .inr a =>
    lineAgrees d L u a b
  | .diagonal L, .point u, .inr a, .inl b | .point u, .diagonal L, .inl b, .inr a =>
    lineAgrees D L u a b
  | _, _, _, _ => False

/-- The three branches' common acceptance predicate, with the diagonal bound from Figure 2. -/
@[expose] def accepts (d : ℕ) :
    Question F m → Question F m → Answer F m → Answer F m → Prop :=
  acceptsWithDiagonalCap d (m * d)

theorem accepts_eq_withDiagonalCap (d : ℕ) :
    accepts (F := F) (m := m) d = acceptsWithDiagonalCap d (m * d) := rfl

/-- Exchanging the players preserves acceptance with a fixed diagonal cutoff. -/
theorem acceptsWithDiagonalCap_swap (d D : ℕ) (x y : Question F m) (a b : Answer F m) :
    acceptsWithDiagonalCap d D x y a b ↔ acceptsWithDiagonalCap d D y x b a := by
  cases x <;> cases y <;> cases a <;> cases b <;> simp only [acceptsWithDiagonalCap, eq_comm]

/-- Acceptance on an axis question and its paired point is determined by the legal line
answer and its value at the point. -/
theorem exists_legal_of_accepts_axis_point (d : ℕ) (L : Finset (Point F m)) (u : Point F m)
    (a b : Answer F m) (h : accepts d (.axis L) (.point u) a b) :
    ∃ g z, a = .inr g ∧ b = .inl z ∧
      g.1 = L ∧ LineHasDegree g.2 d ∧ ∃ hu : u ∈ g.1, g.2 ⟨u, hu⟩ = z := by
  cases a <;> cases b <;> simp only [accepts, acceptsWithDiagonalCap] at h
  exact ⟨_, _, rfl, rfl, h⟩

/-- Accepted diagonal and point answers agree at the queried point. -/
theorem exists_agree_of_acceptsAtDegrees_point_diagonal (d D : ℕ) (L : Finset (Point F m))
    (u : Point F m) (a b : Answer F m)
    (h : acceptsWithDiagonalCap d D (.point u) (.diagonal L) a b) :
    ∃ g z, a = .inl z ∧ b = .inr g ∧ ∃ hu : u ∈ g.1, g.2 ⟨u, hu⟩ = z := by
  cases a <;> cases b <;> simp only [acceptsWithDiagonalCap] at h
  exact ⟨_, _, rfl, rfl, h.2.2⟩

/-- Accepted diagonal and point answers agree at the queried point. -/
theorem exists_agree_of_accepts_point_diagonal (d : ℕ) (L : Finset (Point F m))
    (u : Point F m) (a b : Answer F m) (h : accepts d (.point u) (.diagonal L) a b) :
    ∃ g z, a = .inl z ∧ b = .inr g ∧ ∃ hu : u ∈ g.1, g.2 ⟨u, hu⟩ = z :=
  exists_agree_of_acceptsAtDegrees_point_diagonal d (m * d) L u a b h

theorem accepts_point_axis_iff (d : ℕ) (L : Finset (Point F m)) (u : Point F m)
    (a b : Answer F m) :
    accepts d (.point u) (.axis L) a b ↔ accepts d (.axis L) (.point u) b a := by
  cases a <;> cases b <;> rfl

/-- Accepted point answers are equal field elements. -/
theorem exists_eq_of_accepts_points (d : ℕ) (u v : Point F m) (a b : Answer F m)
    (h : accepts d (.point u) (.point v) a b) : ∃ c, a = .inl c ∧ b = .inl c := by
  cases a <;> cases b <;> simp only [accepts, acceptsWithDiagonalCap] at h
  exact ⟨_, rfl, congrArg Sum.inl h.symm⟩

/-- Send the line and point to uniformly random opposite roles. -/
@[expose] noncomputable def assignLineRoles (line point : Question F m) :
    PMF (Question F m × Question F m) :=
  (uniformOfFintype Bool).map fun r => if r then (line, point) else (point, line)

/-- Disclose the same uniformly random point to both players. -/
@[expose] noncomputable def consistencyQuestions : PMF (Question F m × Question F m) :=
  (uniformOfFintype (Point F m)).map fun u => (.point u, .point u)

/-- Axis-parallel branch, with a uniform point and independently uniform coordinate. -/
@[expose] noncomputable def axisQuestions (n : ℕ) :
    PMF (Question F (n + 1) × Question F (n + 1)) :=
  (uniformOfFintype (Point F (n + 1))).bind fun u =>
    (uniformOfFintype (Fin (n + 1))).bind fun i =>
      assignLineRoles (.axis (linePoints u (Pi.single i (1 : F)))) (.point u)

/-- Extend a direction in the chosen prefix by zero on all remaining coordinates. -/
@[expose] def prefixDirection (i : Fin m) (v : Fin (i.val + 1) → F) : Point F m :=
  fun j => if h : j.val < i.val + 1 then v ⟨j.val, h⟩ else 0

omit [Fintype F] [DecidableEq F] in
@[simp] theorem prefixDirection_zero (i : Fin m) :
    prefixDirection (F := F) i 0 = 0 := by
  funext j
  simp [prefixDirection]

/-- Zero padding gives every direction in the prefix exactly once. -/
def prefixDirectionEquiv (i : Fin m) :
    (Fin (i.val + 1) → F) ≃ {v : Point F m // ∀ j : Fin m, i.val < j.val → v j = 0} where
  toFun v := ⟨prefixDirection i v, fun j hj => dite_eq_right (by omega)⟩
  invFun v j := v.val ⟨j.val, by omega⟩
  left_inv v := by
    funext j
    simp [prefixDirection, j.isLt]
  right_inv v := by
    apply Subtype.ext
    funext j
    by_cases hj : j.val < i.val + 1
    · simp [prefixDirection, hj]
    · change (if h : j.val < i.val + 1 then v.val ⟨j.val, by omega⟩ else 0) = v.val j
      rw [dite_eq_right hj, v.property j (by omega)]

/-- Diagonal branch, with a uniform point, uniform prefix length and uniform direction within
that prefix. Zero directions occur with the sampling probability specified in Figure 2. -/
@[expose] noncomputable def diagonalQuestions (n : ℕ) :
    PMF (Question F (n + 1) × Question F (n + 1)) :=
  (uniformOfFintype (Point F (n + 1))).bind fun u =>
    (uniformOfFintype (Fin (n + 1))).bind fun i =>
      (uniformOfFintype (Fin (i.val + 1) → F)).bind fun v =>
        assignLineRoles (.diagonal (linePoints u (prefixDirection i v))) (.point u)

omit [Fintype F] [DecidableEq F] in
/-- At the full prefix, extending the direction is the identity. -/
@[simp] theorem prefixDirection_last {n : ℕ} (v : Point F (n + 1)) :
    prefixDirection (Fin.last n) v = v := by
  funext j
  simp [prefixDirection, j.isLt]

/-- Every prefix direction and either role assignment occurs in the diagonal branch. -/
theorem mem_diagonalQuestions_support {n : ℕ} {q : Question F (n + 1) × Question F (n + 1)} :
    q ∈ (diagonalQuestions n).support ↔
      ∃ (u : Point F (n + 1)) (i : Fin (n + 1)) (v : Fin (i.val + 1) → F) (r : Bool),
        (if r then (.diagonal (linePoints u (prefixDirection i v)), .point u)
          else (.point u, .diagonal (linePoints u (prefixDirection i v)))) = q := by
  simp only [diagonalQuestions, PMF.mem_support_bind_iff, assignLineRoles, PMF.support_map,
    Set.mem_image, Cslib.Probability.PMF.mem_support_uniformOfFintype, true_and]

/-- The three verifier branches, selected with equal probability. -/
inductive Branch where
  | axis
  | consistency
  | diagonal
  deriving DecidableEq

instance : Fintype Branch :=
  ⟨{.axis, .consistency, .diagonal}, fun b => by cases b <;> simp⟩

instance : Nonempty Branch := ⟨.axis⟩

/-- The question law conditional on the selected branch. -/
noncomputable def branchQuestions (n : ℕ) :
    Branch → PMF (Question F (n + 1) × Question F (n + 1))
  | .axis => axisQuestions n
  | .consistency => consistencyQuestions
  | .diagonal => diagonalQuestions n

/-- The conditional verifier at an explicit diagonal degree bound. -/
noncomputable def branchGameWithDiagonalCap (n d D : ℕ) (b : Branch) :
    TwoProverGame (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) where
  questions := branchQuestions n b
  accepts := acceptsWithDiagonalCap d D

/-- A verifier with its initial branch choice fixed. -/
noncomputable def branchGame (n d : ℕ) (b : Branch) :
    TwoProverGame (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) :=
  branchGameWithDiagonalCap n d ((n + 1) * d) b

theorem branchGame_eq_withDiagonalCap (n d : ℕ) (b : Branch) :
    branchGame (F := F) n d b = branchGameWithDiagonalCap n d ((n + 1) * d) b := by
  unfold branchGame
  rfl

theorem branchGameWithDiagonalCap_questions (n d D : ℕ) (b : Branch) :
    (branchGameWithDiagonalCap (F := F) n d D b).questions = branchQuestions n b := by
  unfold branchGameWithDiagonalCap
  rfl

theorem branchGameWithDiagonalCap_accepts (n d D : ℕ) (b : Branch) :
    (branchGameWithDiagonalCap (F := F) n d D b).accepts = acceptsWithDiagonalCap d D := by
  unfold branchGameWithDiagonalCap
  rfl

theorem branchGame_questions (n d : ℕ) (b : Branch) :
    (branchGame (F := F) n d b).questions = branchQuestions n b := by
  unfold branchGame
  rfl

theorem branchQuestions_axis (n : ℕ) :
    branchQuestions (F := F) n .axis = axisQuestions n := by
  unfold branchQuestions
  rfl

theorem branchQuestions_diagonal (n : ℕ) :
    branchQuestions (F := F) n .diagonal = diagonalQuestions n := by
  unfold branchQuestions
  rfl

theorem branchQuestions_consistency (n : ℕ) :
    branchQuestions (F := F) n .consistency = consistencyQuestions := by
  unfold branchQuestions
  rfl

theorem branchGame_accepts (n d : ℕ) (b : Branch) :
    (branchGame (F := F) n d b).accepts = accepts d := by unfold branchGame; rfl

/-- The low individual degree game in positive ambient dimension `n + 1`. -/
noncomputable def game (n d : ℕ) :
    TwoProverGame (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) where
  questions := (uniformOfFintype Branch).bind (branchQuestions n)
  accepts := accepts d

private theorem average_branches (f : Branch → ℝ) :
    ∑ b, ((uniformOfFintype Branch) b).toReal * f b =
      (f .axis + f .consistency + f .diagonal) / 3 := by
  have hc : Fintype.card Branch = 3 := by decide
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, hc, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, show (univ : Finset Branch) = {.axis, .consistency, .diagonal} from rfl]
  norm_num [Finset.sum_insert, Finset.sum_singleton]
  ring

/-- Classical winning probability is the exact average of the three branch scores. -/
theorem winProb_game (n d : ℕ) (a b : Question F (n + 1) → Answer F (n + 1)) :
    (game (F := F) n d).winProb a b =
      ((branchGame (F := F) n d .axis).winProb a b +
        (branchGame (F := F) n d .consistency).winProb a b +
        (branchGame (F := F) n d .diagonal).winProb a b) / 3 := by
  unfold TwoProverGame.winProb game branchGame
  rw [Cslib.Probability.PMF.toOuterMeasure_bind_toReal]
  exact average_branches _

/-- The same exact branch decomposition applies to arbitrary conditional answer laws,
in particular to all finite quantum strategies. -/
theorem answersWinProb_game (n d : ℕ)
    (ans : Question F (n + 1) → Question F (n + 1) → PMF (Answer F (n + 1) × Answer F (n + 1))) :
    (game (F := F) n d).answersWinProb ans =
      ((branchGame (F := F) n d .axis).answersWinProb ans +
        (branchGame (F := F) n d .consistency).answersWinProb ans +
        (branchGame (F := F) n d .diagonal).answersWinProb ans) / 3 := by
  simp only [TwoProverGame.answersWinProb_eq, TwoProverGame.acceptsRound_eq]
  unfold game branchGame
  rw [PMF.bind_bind, Cslib.Probability.PMF.toOuterMeasure_bind_toReal]
  exact average_branches _

/-- Each branch loses with probability at most three times the total loss. -/
theorem branch_loss_le_three_mul (n d : ℕ) (b : Branch)
    (ans : Question F (n + 1) → Question F (n + 1) → PMF (Answer F (n + 1) × Answer F (n + 1))) :
    1 - (branchGame (F := F) n d b).answersWinProb ans ≤
      3 * (1 - (game (F := F) n d).answersWinProb ans) := by
  rw [answersWinProb_game]
  have ha := (branchGame (F := F) n d .axis).answersWinProb_le_one ans
  have hc := (branchGame (F := F) n d .consistency).answersWinProb_le_one ans
  have hd := (branchGame (F := F) n d .diagonal).answersWinProb_le_one ans
  cases b <;> linarith

/-- Honest answers give the polynomial's value on point questions and its full restriction
on line questions. -/
def honest (P : MvPolynomial (Fin m) F) : Question F m → Answer F m
  | .point u => .inl (MvPolynomial.eval u P)
  | .axis L | .diagonal L => .inr ⟨L, fun u => MvPolynomial.eval u.val P⟩

omit [Fintype F] [DecidableEq F] in
/-- The honest point answer is the polynomial's value at that point. -/
theorem honest_point (P : MvPolynomial (Fin m) F) (u : Point F m) :
    honest P (.point u) = .inl (MvPolynomial.eval u P) := by
  unfold honest
  rfl

private theorem honest_lineAgrees (P : MvPolynomial (Fin m) F) (u v : Point F m) (d : ℕ)
    (hd : (P.restrictAffineLine u v).natDegree ≤ d) :
    lineAgrees d (linePoints u v) u
      ⟨linePoints u v, fun x => MvPolynomial.eval x.val P⟩ (MvPolynomial.eval u P) :=
  ⟨rfl, ⟨u, v, rfl, P.restrictAffineLine u v, hd,
    fun t => (P.eval_restrictAffineLine u v t).symm⟩,
    by simpa using mem_linePoints u v (0 : F), rfl⟩

omit [Fintype F] [DecidableEq F] in
private theorem honest_axis_degree {n d : ℕ} (P : MvPolynomial (Fin (n + 1)) F)
    (hP : ∀ i, P.degreeOf i ≤ d) (u : Point F (n + 1)) (i : Fin (n + 1)) :
    (P.restrictAffineLine u (Pi.single i (1 : F))).natDegree ≤ d :=
  (P.natDegree_restrictAffineLine_single_le u i).trans (hP i)

omit [Fintype F] [DecidableEq F] in
private theorem honest_diagonal_degree {n d : ℕ} (P : MvPolynomial (Fin (n + 1)) F)
    (hP : ∀ i, P.degreeOf i ≤ d) (u v : Point F (n + 1)) :
    (P.restrictAffineLine u v).natDegree ≤ (n + 1) * d := by
  classical
  refine (P.natDegree_restrictAffineLine_le_sum_degreeOf u v).trans ?_
  calc
    _ ≤ ∑ i : Fin (n + 1), P.degreeOf i :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _
    _ ≤ ∑ _ : Fin (n + 1), d := sum_le_sum fun i _ => hP i
    _ = _ := by simp

/-- Every supported question pair in each branch accepts honest answers for a polynomial with
individual degree at most `d`. -/
theorem accepts_honest_of_mem_branch {n d : ℕ} (P : MvPolynomial (Fin (n + 1)) F)
    (hP : ∀ i, P.degreeOf i ≤ d) (b : Branch)
    {q : Question F (n + 1) × Question F (n + 1)} (hq : q ∈ (branchQuestions n b).support) :
    accepts d q.1 q.2 (honest P q.1) (honest P q.2) := by
  cases b
  · simp only [branchQuestions, axisQuestions, PMF.mem_support_bind_iff,
      assignLineRoles, PMF.support_map, Set.mem_image] at hq
    obtain ⟨u, _, i, _, _ | _, _, rfl⟩ := hq <;>
      exact honest_lineAgrees P u (Pi.single i (1 : F)) d (honest_axis_degree P hP u i)
  · obtain ⟨u, _, rfl⟩ := by simpa [branchQuestions, consistencyQuestions] using hq
    rfl
  · obtain ⟨u, i, v, _ | _, rfl⟩ := mem_diagonalQuestions_support.mp hq <;>
      exact honest_lineAgrees P u (prefixDirection i v) ((n + 1) * d)
        (honest_diagonal_degree P hP u (prefixDirection i v))

/-- Honest play wins each of the three branches with probability one. -/
theorem winProb_branch_honest {n d : ℕ} (P : MvPolynomial (Fin (n + 1)) F)
    (hP : ∀ i, P.degreeOf i ≤ d) (b : Branch) :
    (branchGame (F := F) n d b).winProb (honest P) (honest P) = 1 := by
  rw [TwoProverGame.winProb, branchGame_questions, branchGame_accepts,
    ((branchQuestions n b).toOuterMeasure_apply_eq_one_iff _).mpr
      fun _ => accepts_honest_of_mem_branch P hP b,
    ENNReal.toReal_one]

/-- The honest strategy wins the low individual degree game with probability one. -/
theorem winProb_honest {n d : ℕ} (P : MvPolynomial (Fin (n + 1)) F)
    (hP : ∀ i, P.degreeOf i ≤ d) : (game (F := F) n d).winProb (honest P) (honest P) = 1 := by
  rw [winProb_game, winProb_branch_honest P hP .axis, winProb_branch_honest P hP .consistency,
    winProb_branch_honest P hP .diagonal]
  norm_num

end Cslib.PCP.LowIndividualDegree
