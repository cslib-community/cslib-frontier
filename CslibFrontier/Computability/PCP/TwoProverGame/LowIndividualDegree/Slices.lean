/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Last-coordinate slices of the low individual degree test

Fixing the last coordinate embeds a lower-dimensional point, line, and question into the
original game. When the chosen axis or prefix omits the last coordinate, the line question
lies in that slice. This section isolates the sampling step in the analysis of restricted
strategies in [Ji, Natarajan, Vidick, Wright and Yuen, Lemma 6.6][JNVWY2020LowIndividualDegree].
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset
open Cslib.Probability.PMF

variable {F : Type*} {m : ℕ}

/-- Append the fixed coordinate to a point. -/
def appendPoint (x : F) : Point F m ↪ Point F (m + 1) where
  toFun u := Fin.snoc (α := fun _ : Fin (m + 1) => F) u x
  inj' := by
    intro u v h
    change Fin.snoc (α := fun _ : Fin (m + 1) => F) u x =
      Fin.snoc (α := fun _ : Fin (m + 1) => F) v x at h
    simpa only [Fin.init_snoc] using congrArg Fin.init h

/-- The slice embedding appends the chosen last coordinate. -/
theorem appendPoint_apply (x : F) (u : Point F m) :
    appendPoint x u = Fin.snoc u x := by
  unfold appendPoint
  rfl

@[simp] theorem appendPoint_apply_castSucc (x : F) (u : Point F m) (i : Fin m) :
    appendPoint x u i.castSucc = u i := by
  change Fin.snoc (α := fun _ : Fin (m + 1) => F) u x i.castSucc = _
  exact Fin.snoc_castSucc (α := fun _ : Fin (m + 1) => F) x u i

@[simp] theorem appendPoint_apply_last (x : F) (u : Point F m) :
    appendPoint x u (Fin.last m) = x := by
  change Fin.snoc (α := fun _ : Fin (m + 1) => F) u x (Fin.last m) = _
  exact Fin.snoc_last (α := fun _ : Fin (m + 1) => F) x u

/-- Append the fixed coordinate to every point on a geometric line. -/
def appendLine (x : F) (L : Finset (Point F m)) : Finset (Point F (m + 1)) :=
  L.map (appendPoint x)

/-- Include a question in the larger game through a fixed last coordinate. -/
@[expose] def appendQuestion (x : F) : Question F m → Question F (m + 1)
  | .point u => .point (appendPoint x u)
  | .axis L => .axis (appendLine x L)
  | .diagonal L => .diagonal (appendLine x L)

variable [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem appendPoint_affine (x t : F) (u v : Point F m) :
    appendPoint x (u + t • v) = appendPoint x u + t • appendPoint 0 v := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Pi.add_apply, Pi.smul_apply]
  · simp [Pi.add_apply, Pi.smul_apply]

theorem appendLine_linePoints (x : F) (u v : Point F m) :
    appendLine x (linePoints u v) = linePoints (appendPoint x u) (appendPoint 0 v) := by
  unfold appendLine linePoints
  rw [Finset.map_eq_image, Finset.image_image]
  exact image_congr fun t _ => appendPoint_affine x t u v

omit [Fintype F] [DecidableEq F] in
theorem appendPoint_single (i : Fin m) :
    appendPoint (0 : F) (Pi.single i (1 : F)) = Pi.single i.castSucc (1 : F) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · by_cases h : k = i
    · subst k
      simp
    · simp [h]

omit [Fintype F] [DecidableEq F] in
theorem appendPoint_prefixDirection (i : Fin m) (v : Fin (i.val + 1) → F) :
    appendPoint (0 : F) (prefixDirection i v) = prefixDirection i.castSucc v := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [appendPoint_apply_last]
    have h : ¬ m < i.val + 1 := by have hi := i.isLt; omega
    simp [prefixDirection, h]
  · simp only [appendPoint_apply_castSucc, prefixDirection, Fin.val_castSucc]

omit [DecidableEq F] in
/-- A uniform point is obtained by independently sampling its last coordinate and its prefix. -/
theorem uniformPoint_succ :
    (uniformOfFintype F).bind (fun x => (uniformOfFintype (Point F m)).map (appendPoint x)) =
      uniformOfFintype (Point F (m + 1)) := by
  let e := Fin.snocEquiv (fun _ : Fin (m + 1) => F)
  calc
    _ = ((uniformOfFintype F).bind fun x =>
        (uniformOfFintype (Point F m)).map fun u => (x, u)).map e := by
      rw [PMF.map_bind]
      simp only [PMF.map_comp]
      rfl
    _ = _ := by rw [uniformOfFintype_prod, uniformOfFintype_map_equiv]

omit [DecidableEq F] in
/-- The score averaged over the self-consistency branch equals the average of its scores
on the slices. -/
theorem consistencyQuestions_slices
    (score : Question F (m + 1) × Question F (m + 1) → ℝ) :
    (∑ q, ((consistencyQuestions (F := F) (m := m + 1)) q).toReal * score q) =
      ∑ x, (uniformOfFintype F x).toReal *
        ∑ q, ((consistencyQuestions (F := F) (m := m)) q).toReal *
          score (appendQuestion x q.1, appendQuestion x q.2) := by
  simp only [consistencyQuestions, sum_map_mul]
  rw [← uniformPoint_succ, sum_bind_mul]
  simp only [sum_map_mul, appendQuestion]

private theorem sum_uniform_fin_split {n : ℕ} (f : Fin (n + 2) → ℝ) :
    (n + 2 : ℝ) * (∑ i, (uniformOfFintype (Fin (n + 2)) i).toReal * f i) =
      (n + 1 : ℝ) * (∑ i : Fin (n + 1), (uniformOfFintype (Fin (n + 1)) i).toReal *
        f i.castSucc) + f (Fin.last (n + 1)) := by
  simp only [uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  push_cast
  rw [← mul_sum, ← mul_sum]
  have h₂ : (n + 2 : ℝ) ≠ 0 := by positivity
  have h₁ : (n + 1 : ℝ) ≠ 0 := by positivity
  simp only [← mul_assoc, mul_inv_cancel₀ h₂, mul_inv_cancel₀ h₁, one_mul]
  exact Fin.sum_univ_castSucc f

omit [DecidableEq F] in
private theorem sum_point_index_slices_le {n : ℕ}
    (f : Point F (n + 2) → Fin (n + 2) → ℝ) (hf : ∀ u i, 0 ≤ f u i) :
    (n + 1 : ℝ) * (∑ x, (uniformOfFintype F x).toReal *
      ∑ u, (uniformOfFintype (Point F (n + 1)) u).toReal *
        ∑ i : Fin (n + 1), (uniformOfFintype (Fin (n + 1)) i).toReal *
          f (appendPoint x u) i.castSucc) ≤
    (n + 2 : ℝ) * (∑ u, (uniformOfFintype (Point F (n + 2)) u).toReal *
      ∑ i, (uniformOfFintype (Fin (n + 2)) i).toReal * f u i) := by
  rw [← uniformPoint_succ (m := n + 1), sum_bind_mul]
  simp only [sum_map_mul]
  have hspread (c : ℝ) (g : F → Point F (n + 1) → ℝ) :
      c * (∑ x, (uniformOfFintype F x).toReal *
        ∑ u, (uniformOfFintype (Point F (n + 1)) u).toReal * g x u) =
      ∑ x, (uniformOfFintype F x).toReal *
        ∑ u, (uniformOfFintype (Point F (n + 1)) u).toReal * (c * g x u) := by
    simp only [mul_sum, mul_left_comm c]
  rw [hspread, hspread]
  refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
    ENNReal.toReal_nonneg
  rw [sum_uniform_fin_split]
  exact le_add_of_nonneg_right (hf _ _)

omit [Field F] [DecidableEq F] in
private theorem roleScore_append (x : F) (L u : Question F m)
    (score : Question F (m + 1) × Question F (m + 1) → ℝ) :
    (∑ q, (assignLineRoles L u q).toReal * score (appendQuestion x q.1, appendQuestion x q.2)) =
      ∑ q, (assignLineRoles (appendQuestion x L) (appendQuestion x u) q).toReal * score q := by
  simp only [assignLineRoles, sum_map_mul]
  exact sum_congr rfl fun r _ => by cases r <;> rfl

/-- The contribution from axes in the prefix equals the average of the corresponding slice
scores, weighted by their probability of being selected. For nonnegative scores it is
bounded by the full axis average. -/
theorem axisQuestions_slices_le {n : ℕ}
    (score : Question F (n + 2) × Question F (n + 2) → ℝ) (hscore : ∀ q, 0 ≤ score q) :
    (n + 1 : ℝ) * (∑ x, (uniformOfFintype F x).toReal *
      ∑ q, ((axisQuestions (F := F) n) q).toReal *
        score (appendQuestion x q.1, appendQuestion x q.2)) ≤
    (n + 2 : ℝ) * (∑ q, ((axisQuestions (F := F) (n + 1)) q).toReal * score q) := by
  let f (u : Point F (n + 2)) (i : Fin (n + 2)) := ∑ q,
    (assignLineRoles (.axis (linePoints u (Pi.single i (1 : F)))) (.point u) q).toReal * score q
  have hf (u : Point F (n + 2)) (i : Fin (n + 2)) : 0 ≤ f u i :=
    sum_nonneg fun q _ => mul_nonneg ENNReal.toReal_nonneg (hscore q)
  simp only [axisQuestions, sum_bind_mul]
  simp_rw [roleScore_append, appendQuestion, appendLine_linePoints, appendPoint_single]
  exact sum_point_index_slices_le f hf

/-- The analogous score bound for diagonal prefixes that omit the last coordinate. It uses
the same degree-independent sampling law even when the sampled direction is zero. -/
theorem diagonalQuestions_slices_le {n : ℕ}
    (score : Question F (n + 2) × Question F (n + 2) → ℝ) (hscore : ∀ q, 0 ≤ score q) :
    (n + 1 : ℝ) * (∑ x, (uniformOfFintype F x).toReal *
      ∑ q, ((diagonalQuestions (F := F) n) q).toReal *
        score (appendQuestion x q.1, appendQuestion x q.2)) ≤
    (n + 2 : ℝ) * (∑ q, ((diagonalQuestions (F := F) (n + 1)) q).toReal * score q) := by
  let f (u : Point F (n + 2)) (i : Fin (n + 2)) := ∑ v,
    (uniformOfFintype (Fin (i.val + 1) → F) v).toReal * ∑ q,
      (assignLineRoles (.diagonal (linePoints u (prefixDirection i v))) (.point u) q).toReal *
        score q
  have hf (u : Point F (n + 2)) (i : Fin (n + 2)) : 0 ≤ f u i :=
    sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg
      (sum_nonneg fun q _ => mul_nonneg ENNReal.toReal_nonneg (hscore q))
  simp only [diagonalQuestions, sum_bind_mul]
  simp_rw [roleScore_append, appendQuestion, appendLine_linePoints, appendPoint_prefixDirection]
  exact sum_point_index_slices_le f hf

/-- The points of a line and its copy in a slice are in bijection. -/
noncomputable def appendLineEquiv (x : F) (L : Finset (Point F m)) : L ≃ appendLine x L :=
  L.equivMap (appendPoint x)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem appendLineEquiv_val (x : F) (L : Finset (Point F m)) (u : L) :
    ((appendLineEquiv x L u).val) = appendPoint x u.val := by
  rfl

private theorem line_polynomial_of_eq {L : Finset (Point F m)} {f : L → F} {d : ℕ}
    {u v : Point F m} (h : LineHasDegree f d) (hL : linePoints u v = L) :
    ∃ p : Polynomial F, p.natDegree ≤ d ∧
      ∀ t : F, f ⟨u + t • v, hL ▸ mem_linePoints u v t⟩ = p.eval t := by
  subst L
  exact h.exists_polynomial

/-- Appending a constant coordinate preserves the degree of the line answer in both
directions. In particular, the degree bound is the same before and after transport. -/
theorem lineHasDegree_append_iff (x : F) (u v : Point F m) (d : ℕ)
    (f : linePoints u v → F) :
    LineHasDegree (f ∘ (appendLineEquiv x (linePoints u v)).symm) d ↔
      LineHasDegree f d := by
  let e := appendLineEquiv x (linePoints u v)
  have hL := (appendLine_linePoints x u v).symm
  let a (t : F) : linePoints u v := ⟨u + t • v, mem_linePoints u v t⟩
  let b (t : F) : appendLine x (linePoints u v) :=
    ⟨appendPoint x u + t • appendPoint 0 v,
      hL ▸ mem_linePoints (appendPoint x u) (appendPoint 0 v) t⟩
  have he (t : F) : e (a t) = b t := by
    apply Subtype.ext
    exact appendPoint_affine x t u v
  constructor
  · intro h
    obtain ⟨p, hp, hpEval⟩ := line_polynomial_of_eq h hL
    refine ⟨u, v, rfl, p, hp, fun t => ?_⟩
    change f (a t) = p.eval t
    have ht := hpEval t
    change f (e.symm (b t)) = p.eval t at ht
    rw [← he, e.symm_apply_apply] at ht
    exact ht
  · intro h
    obtain ⟨p, hp, hpEval⟩ := h.exists_polynomial
    refine ⟨appendPoint x u, appendPoint 0 v, hL, p, hp, fun t => ?_⟩
    change f (e.symm (b t)) = p.eval t
    rw [← he, e.symm_apply_apply]
    exact hpEval t

/-- A line answer is transported by pulling its point values along the slice equivalence. -/
noncomputable def appendLineAnswer (x : F) (answer : Σ L : Finset (Point F m), L → F) :
    Σ L : Finset (Point F (m + 1)), L → F :=
  ⟨appendLine x answer.1, answer.2 ∘ (appendLineEquiv x answer.1).symm⟩

private theorem lineHasDegree_append (x : F) (L : Finset (Point F m)) (d : ℕ)
    (f : L → F) :
    LineHasDegree (f ∘ (appendLineEquiv x L).symm) d ↔ LineHasDegree f d := by
  constructor
  · intro h
    have hgeomWitness := h
    obtain ⟨u, v, hL, _, _, _⟩ := hgeomWitness
    have hinit : (fun p : Point F (m + 1) => Fin.init p) ∘ appendPoint x = id := by
      funext z i
      exact appendPoint_apply_castSucc x z i
    have hproj : (appendLine x L).image (fun p => Fin.init p) = L := by
      unfold appendLine
      rw [map_eq_image, image_image, hinit, image_id]
    have hgeom : linePoints (Fin.init u) (Fin.init v) = L := by
      rw [← hproj, ← hL]
      simp only [linePoints, image_image]
      congr 1
    subst L
    exact (lineHasDegree_append_iff x _ _ d f).mp h
  · intro h
    have hgeomWitness := h
    obtain ⟨u, v, hL, _, _, _⟩ := hgeomWitness
    subst L
    exact (lineHasDegree_append_iff x u v d f).mpr h

/-- Transporting a line answer preserves its agreement with the point at the same degree cap. -/
theorem lineAgrees_appendLineAnswer_iff (x : F) (L : Finset (Point F m)) (w : Point F m)
    (d : ℕ) (answer : Σ K : Finset (Point F m), K → F) (a : F) :
    lineAgrees d (appendLine x L) (appendPoint x w) (appendLineAnswer x answer) a ↔
      lineAgrees d L w answer a := by
  obtain ⟨K, f⟩ := answer
  let e := appendLineEquiv x K
  change (appendLine x K = appendLine x L ∧ LineHasDegree (f ∘ e.symm) d ∧
    ∃ h : appendPoint x w ∈ appendLine x K, f (e.symm ⟨appendPoint x w, h⟩) = a) ↔
    (K = L ∧ LineHasDegree f d ∧ ∃ h : w ∈ K, f ⟨w, h⟩ = a)
  rw [show appendLine x K = appendLine x L ↔ K = L from
    (Finset.map_injective (appendPoint x)).eq_iff,
    lineHasDegree_append]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hw, heval⟩
    obtain ⟨z, hz, he⟩ := mem_map.mp hw
    have hzw := (appendPoint x).injective he
    subst z
    refine ⟨hz, ?_⟩
    have h : e ⟨w, hz⟩ = ⟨appendPoint x w, hw⟩ := Subtype.ext rfl
    rw [← h, e.symm_apply_apply] at heval
    exact heval
  · rintro ⟨hw, heval⟩
    have hm : appendPoint x w ∈ appendLine x K := (e ⟨w, hw⟩).property
    refine ⟨hm, ?_⟩
    have he : e ⟨w, hw⟩ = ⟨appendPoint x w, hm⟩ := Subtype.ext rfl
    rwa [← he, e.symm_apply_apply]

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem appendLineAnswer_injective (x : F) :
    Function.Injective (appendLineAnswer (m := m) x) := by
  rintro ⟨L, f⟩ ⟨K, g⟩ h
  have hLK : L = K := (Finset.map_injective (appendPoint x)) (congrArg Sigma.fst h)
  subst K
  have hfg : f ∘ (appendLineEquiv x L).symm = g ∘ (appendLineEquiv x L).symm :=
    eq_of_heq (Sigma.mk.inj h).2
  have hf : f = g := by
    funext u
    obtain ⟨v, rfl⟩ := (appendLineEquiv x L).symm.surjective u
    exact congrFun hfg v
  rw [hf]

private local instance [Nonempty F] : Nonempty (Σ L : Finset (Point F m), L → F) :=
  ⟨⟨∅, fun _ => Classical.choice inferInstance⟩⟩

omit [Fintype F] [DecidableEq F] in
/-- Restrict an answer to a fixed last coordinate. Point values are unchanged. On line
answers outside the slice the inverse can choose any line answer, since the larger verifier
already rejects those answers on the lifted questions. -/
noncomputable def restrictAnswer (x : F) : Answer F (m + 1) → Answer F m
  | .inl a => .inl a
  | .inr a => .inr (Function.invFun (appendLineAnswer x) a)

omit [Fintype F] [DecidableEq F] in
@[simp] theorem restrictAnswer_inl (x a : F) :
    restrictAnswer (m := m) x (.inl a) = .inl a := by
  unfold restrictAnswer
  rfl

omit [Fintype F] [DecidableEq F] in
/-- Line answers remain line answers under restriction. -/
theorem restrictAnswer_inr_exists (x : F) (a : Σ L : Finset (Point F (m + 1)), L → F) :
    ∃ b, restrictAnswer (m := m) x (.inr a) = .inr b := by
  unfold restrictAnswer
  exact ⟨_, rfl⟩

private theorem restrictAnswer_lineAgrees (x : F) (L : Finset (Point F m)) (u : Point F m)
    (d : ℕ) (g : Σ K : Finset (Point F (m + 1)), K → F) (a : F)
    (h : lineAgrees d (appendLine x L) (appendPoint x u) g a) :
    lineAgrees d L u (Function.invFun (appendLineAnswer x) g) a := by
  have hdomain := h.1
  obtain ⟨K, f⟩ := g
  change K = appendLine x L at hdomain
  subst K
  let e := appendLineEquiv x L
  let g : Σ K : Finset (Point F m), K → F := ⟨L, f ∘ e⟩
  have hg : appendLineAnswer x g = ⟨appendLine x L, f⟩ := by
    unfold appendLineAnswer
    congr 1
    funext u
    change f (e (e.symm u)) = f u
    rw [e.apply_symm_apply]
  rw [← hg] at h ⊢
  rw [Function.leftInverse_invFun (appendLineAnswer_injective x) g]
  exact (lineAgrees_appendLineAnswer_iff x L u d g a).mp h

/-- Every accepted answer pair on two lifted questions remains accepted after restriction,
at unchanged axis and diagonal degree bounds. -/
theorem acceptsWithDiagonalCap_restrict (x : F) (d D : ℕ) (q₁ q₂ : Question F m)
    (a b : Answer F (m + 1))
    (h : acceptsWithDiagonalCap d D (appendQuestion x q₁) (appendQuestion x q₂) a b) :
    acceptsWithDiagonalCap d D q₁ q₂ (restrictAnswer x a) (restrictAnswer x b) := by
  cases q₁ <;> cases q₂ <;> cases a <;> cases b <;>
    simp only [appendQuestion, acceptsWithDiagonalCap, restrictAnswer] at h ⊢ <;>
    first | exact h | exact restrictAnswer_lineAgrees _ _ _ _ _ _ h

omit [Fintype F] [DecidableEq F] in
/-- Ask the lifted questions and restrict the two answers independently. -/
@[expose] noncomputable def restrictAnswerLaw (x : F)
    (ans : Question F (m + 1) → Question F (m + 1) →
      PMF (Answer F (m + 1) × Answer F (m + 1))) (q₁ q₂ : Question F m) :
    PMF (Answer F m × Answer F m) :=
  (ans (appendQuestion x q₁) (appendQuestion x q₂)).map
    (Prod.map (restrictAnswer x) (restrictAnswer x))

private noncomputable def lossAt (d D : ℕ)
    (ans : Question F m → Question F m → PMF (Answer F m × Answer F m))
    (q : Question F m × Question F m) : ℝ :=
  ((ans q.1 q.2).toOuterMeasure {a | ¬ acceptsWithDiagonalCap d D q.1 q.2 a.1 a.2}).toReal

private theorem lossAt_restrict_le (x : F) (d D : ℕ)
    (ans : Question F (m + 1) → Question F (m + 1) →
      PMF (Answer F (m + 1) × Answer F (m + 1))) (q : Question F m × Question F m) :
    lossAt d D (restrictAnswerLaw x ans) q ≤
      lossAt d D ans (appendQuestion x q.1, appendQuestion x q.2) := by
  unfold lossAt restrictAnswerLaw
  rw [PMF.toOuterMeasure_map_apply]
  apply ENNReal.toReal_mono (toOuterMeasure_ne_top _ _)
  exact (PMF.toOuterMeasure _).mono fun a ha h =>
    ha (acceptsWithDiagonalCap_restrict x d D q.1 q.2 a.1 a.2 h)

private theorem branchLoss_eq_sum {n : ℕ} (d D : ℕ) (b : Branch)
    (ans : Question F (n + 1) → Question F (n + 1) →
      PMF (Answer F (n + 1) × Answer F (n + 1))) :
    1 - (branchGameWithDiagonalCap n d D b).answersWinProb ans =
      ∑ q, (branchQuestions n b q).toReal * lossAt d D ans q := by
  unfold TwoProverGame.answersWinProb
  let p := (branchGameWithDiagonalCap n d D b).questions.bind fun q =>
    (ans q.1 q.2).map fun a => (q, a)
  let e := {z | (branchGameWithDiagonalCap (F := F) n d D b).AcceptsRound z}
  change 1 - (p.toOuterMeasure e).toReal = _
  have hcompl : 1 - (p.toOuterMeasure e).toReal = (p.toOuterMeasure eᶜ).toReal := by
    linarith [toOuterMeasure_toReal_add_compl p e]
  rw [hcompl]
  unfold p
  rw [toOuterMeasure_bind_toReal, branchGameWithDiagonalCap_questions]
  refine sum_congr rfl fun q _ => ?_
  rw [PMF.toOuterMeasure_map_apply]
  unfold e lossAt TwoProverGame.AcceptsRound
  rw [branchGameWithDiagonalCap_accepts]
  rfl

/-- Averaged over the last coordinate, restriction at fixed degree caps does not increase
the consistency loss. In the axis and diagonal branches it increases the loss by at most
`(n + 2) / (n + 1)`, the inverse probability that the selected coordinate lies in the prefix. -/
theorem branchLoss_restrict_le (n d D : ℕ) (b : Branch)
    (ans : Question F (n + 2) → Question F (n + 2) →
      PMF (Answer F (n + 2) × Answer F (n + 2))) :
    (if b = .consistency then 1 else (n + 1 : ℝ)) *
        (∑ x, (uniformOfFintype F x).toReal *
          (1 - (branchGameWithDiagonalCap n d D b).answersWinProb (restrictAnswerLaw x ans))) ≤
      (if b = .consistency then 1 else (n + 2 : ℝ)) *
        (1 - (branchGameWithDiagonalCap (n + 1) d D b).answersWinProb ans) := by
  simp only [branchLoss_eq_sum]
  have h := sum_le_sum (s := (univ : Finset F)) fun x _ =>
    mul_le_mul_of_nonneg_left (sum_le_sum (s := univ) fun q _ =>
      mul_le_mul_of_nonneg_left (lossAt_restrict_le x d D ans q)
        (ENNReal.toReal_nonneg (a := branchQuestions n b q)))
      (ENNReal.toReal_nonneg (a := uniformOfFintype F x))
  have hn (q : Question F (n + 2) × Question F (n + 2)) : 0 ≤ lossAt d D ans q :=
    ENNReal.toReal_nonneg
  cases b
  · simp only [branchQuestions_axis] at h ⊢
    simp only [ite_eq_right (by decide : Branch.axis ≠ .consistency)]
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans
      (axisQuestions_slices_le (lossAt d D ans) hn)
  · simp only [branchQuestions_consistency] at h ⊢
    simp only [↓reduceIte, one_mul]
    exact h.trans_eq (consistencyQuestions_slices (lossAt d D ans)).symm
  · simp only [branchQuestions_diagonal] at h ⊢
    simp only [ite_eq_right (by decide : Branch.diagonal ≠ .consistency)]
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans
      (diagonalQuestions_slices_le (lossAt d D ans) hn)

end Cslib.PCP.LowIndividualDegree
