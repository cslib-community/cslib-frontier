/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree
public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Uniform

/-!
# Polynomial measurements for the one-coordinate test

In one coordinate the axis-parallel line is the whole space. Its measurement can be used
as a single global polynomial measurement, the base case in the proof of Theorem 6.1 of
[Ji, Natarajan, Vidick, Wright and Yuen][JNVWY2020LowIndividualDegree].
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset Cslib.Quantum
open Cslib.Probability.PMF (uniformOfFintype)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- There is one axis-parallel line in one coordinate. -/
theorem linePoints_single_eq_univ (u : Point F 1) (i : Fin 1) :
    linePoints u (Pi.single i (1 : F)) = univ := by
  apply eq_univ_of_forall
  intro x
  have h : u + (x i - u i) • Pi.single i (1 : F) = x := by
    funext j
    rw [Subsingleton.elim j i]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    abel
  rw [← h]
  exact mem_linePoints u (Pi.single i 1) (x i - u i)

/-- In one coordinate the geometric line question is deterministic. The point and the
assignment of the two roles remain uniform and independent. -/
theorem axisQuestions_one :
    axisQuestions (F := F) 0 =
      (uniformOfFintype (Point F 1)).bind fun u => assignLineRoles (.axis univ) (.point u) := by
  unfold axisQuestions
  apply congrArg (PMF.bind (uniformOfFintype (Point F 1)))
  funext u
  have h : (fun i : Fin (0 + 1) =>
      assignLineRoles (.axis (linePoints u (Pi.single i (1 : F)))) (.point u)) =
        fun _ => assignLineRoles (.axis univ) (.point u) := by
    funext i
    rw [linePoints_single_eq_univ u i]
  rw [h, PMF.bind_const]

/-- A polynomial answer on the full line, represented as a function on its points. -/
abbrev PolynomialFunction (F : Type*) [Field F] [Fintype F] [DecidableEq F] (d : ℕ) :=
  {f : ↥(univ : Finset (Point F 1)) → F // LineHasDegree f d}

noncomputable instance (d : ℕ) : Fintype (PolynomialFunction F d) := by
  unfold PolynomialFunction
  exact Fintype.ofFinite _

/-- Evaluate the polynomial function at an ambient point. -/
def PolynomialFunction.eval {d : ℕ} (f : PolynomialFunction F d) (u : Point F 1) : F :=
  f.val ⟨u, mem_univ u⟩

/-- A legal answer on the whole line is represented by a univariate polynomial in the sole
coordinate, with the advertised degree bound. -/
theorem PolynomialFunction.exists_polynomial {d : ℕ} (f : PolynomialFunction F d) :
    ∃ p : Polynomial F, p.natDegree ≤ d ∧
      ∀ x : Point F 1, f.eval x = p.eval (x 0) := by
  let e : Point F 1 := Pi.single 0 1
  have hLine : linePoints (0 : Point F 1) e = univ := linePoints_single_eq_univ 0 0
  have hparam (L : Finset (Point F 1)) (hL : linePoints (0 : Point F 1) e = L)
      (g : L → F) (hg : LineHasDegree g d) :
      ∃ p : Polynomial F, p.natDegree ≤ d ∧
        ∀ x : L, g x = p.eval (x.val 0) := by
    subst L
    obtain ⟨p, hp, he⟩ := hg.exists_polynomial
    refine ⟨p, hp, fun x => ?_⟩
    have hx : (0 : Point F 1) + (x.val 0) • e = x.val := by
      funext j
      rw [Subsingleton.elim j 0]
      simp [e, Pi.smul_apply, smul_eq_mul]
    exact (congrArg g (Subtype.ext hx.symm)).trans (he (x.val 0))
  obtain ⟨p, hp, he⟩ := hparam univ hLine f.val f.property
  exact ⟨p, hp, fun x => he ⟨x, mem_univ x⟩⟩

private theorem zero_lineHasDegree (d : ℕ) :
    LineHasDegree (L := (univ : Finset (Point F 1))) (fun _ => (0 : F)) d := by
  refine ⟨0, Pi.single 0 1, linePoints_single_eq_univ 0 0, 0, ?_, ?_⟩ <;> simp

/-- Read a legal full-line answer, using the zero polynomial for malformed answers. -/
noncomputable def decodePolynomial (d : ℕ) (a : Answer F 1) : PolynomialFunction F d := by
  classical
  let zero : PolynomialFunction F d := ⟨fun _ => 0, zero_lineHasDegree d⟩
  cases a with
  | inl _ => exact zero
  | inr a =>
    let ⟨L, f⟩ := a
    exact if h : L = univ then
      if hf : LineHasDegree f d then
        cast (congrArg (fun K : Finset (Point F 1) => {g : K → F // LineHasDegree g d}) h) ⟨f, hf⟩
      else zero
    else zero

/-- Read the point answer, using zero for a line answer sent to a point question. -/
def decodePoint : Answer F 1 → F
  | .inl z => z
  | .inr _ => 0

theorem decodePolynomial_agrees {d : ℕ} {u : Point F 1} {a b : Answer F 1}
    (h : accepts d (.axis univ) (.point u) a b) :
    (decodePolynomial d a).eval u = decodePoint b := by
  classical
  obtain ⟨⟨L, f⟩, z, rfl, rfl, hL, hf, ⟨hu, he⟩⟩ :=
    exists_legal_of_accepts_axis_point d univ u a b h
  change L = univ at hL
  subst L
  simpa [decodePolynomial, hf, PolynomialFunction.eval, decodePoint] using he

section Soundness

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜]
  [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint]
  [NonnegSpectrumClass ℝ 𝒜]

local notation "Q" => Question F 1
local notation "Ans" => Answer F 1

private noncomputable def axisAcceptScore
    (S : CommutingStrategy Q Q Ans Ans 𝒜) (d : ℕ) (x y : Q) : ℝ := by
  classical
  exact ∑ a, ∑ b, if accepts d x y a b then S.prob x y a b else 0

private theorem axisScore_one (S : CommutingStrategy Q Q Ans Ans 𝒜) (d : ℕ) :
    (branchGame (F := F) 0 d .axis).commutingWinProb S =
      ∑ u, (uniformOfFintype (Point F 1) u).toReal *
        ((axisAcceptScore S d (.point u) (.axis univ) +
          axisAcceptScore S d (.axis univ) (.point u)) / 2) := by
  classical
  let G := branchGame (F := F) 0 d .axis
  let W (q : Q × Q) := axisAcceptScore S d q.1 q.2
  have h : G.commutingWinProb S = ∑ x, ∑ y, (G.questions (x, y)).toReal * W (x, y) := by
    rw [G.commutingWinProb_eq_sum S]
    simp only [W, axisAcceptScore, G, branchGame_accepts]
  rw [h, ← Fintype.sum_prod_type (fun q => (G.questions q).toReal * W q)]
  have hG := branchGame_questions (F := F) 0 d .axis
  change G.questions = _ at hG
  rw [hG, branchQuestions_axis, axisQuestions_one, Cslib.Probability.PMF.sum_bind_mul]
  refine sum_congr rfl fun u _ => congrArg ((uniformOfFintype (Point F 1) u).toReal * ·) ?_
  rw [assignLineRoles, Cslib.Probability.PMF.sum_map_mul]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, W,
    Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_bool,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  ring

/-- One-coordinate extraction. Each player's measurement on the unique axis-parallel line
gives a global degree-bounded polynomial measurement. Evaluating it at the other player's
point is at least as consistent, on average over the uniform point and the two roles, as
the axis-parallel test. -/
theorem exists_polynomial_measurements_one (S : CommutingStrategy Q Q Ans Ans 𝒜) (d : ℕ) :
    ∃ (P R : Measurement (PolynomialFunction F d) 𝒜),
      (∀ u p a, Commute (((S.alice (.point u)).map decodePoint).effect a) (R.effect p)) ∧
      (∀ u p a, Commute (P.effect p) (((S.bob (.point u)).map decodePoint).effect a)) ∧
      (∑ u, (uniformOfFintype (Point F 1) u).toReal *
        ((Measurement.agreement S.state ((S.alice (.point u)).map decodePoint)
            (R.map fun f => f.eval u) +
          Measurement.agreement S.state (P.map fun f => f.eval u)
            ((S.bob (.point u)).map decodePoint)) / 2)) ≥
        (branchGame (F := F) 0 d .axis).commutingWinProb S := by
  classical
  let P := (S.alice (.axis univ)).map (decodePolynomial d)
  let R := (S.bob (.axis univ)).map (decodePolynomial d)
  refine ⟨P, R, ?_, ?_, ?_⟩
  · intro u p a
    simp only [R, Measurement.map_effect]
    apply Commute.sum_left
    intro i _
    apply Commute.sum_right
    exact fun j _ => S.commute (.point u) (.axis univ) i j
  · intro u p a
    simp only [P, Measurement.map_effect]
    apply Commute.sum_left
    intro i _
    apply Commute.sum_right
    exact fun j _ => S.commute (.axis univ) (.point u) i j
  · rw [axisScore_one]
    refine sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply add_le_add
    · simp only [axisAcceptScore, R, Measurement.map_map, Measurement.agreement_map_map]
      refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
      by_cases h : accepts d (.point u) (.axis univ) a b
      · have h' := decodePolynomial_agrees ((accepts_point_axis_iff d univ u a b).mp h)
        simp only [ite_eq_left h, Function.comp_apply, h'.symm, ite_true, CommutingStrategy.prob]
        exact le_rfl
      · rw [ite_eq_right h]
        exact ite_nonneg (S.prob_nonneg _ _ _ _) le_rfl
    · simp only [axisAcceptScore, P, Measurement.map_map, Measurement.agreement_map_map]
      refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
      by_cases h : accepts d (.axis univ) (.point u) a b
      · have h' := decodePolynomial_agrees h
        simp only [ite_eq_left h, Function.comp_apply, h', ite_true, CommutingStrategy.prob]
        exact le_rfl
      · rw [ite_eq_right h]
        exact ite_nonneg (S.prob_nonneg _ _ _ _) le_rfl

end Soundness

end Cslib.PCP.LowIndividualDegree
