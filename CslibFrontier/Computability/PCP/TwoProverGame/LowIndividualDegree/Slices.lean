/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree
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
def appendQuestion (x : F) : Question F m → Question F (m + 1)
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

/-- The line-versus-point predicate is preserved on a slice at a fixed degree cap. -/
theorem lineAgrees_append_iff (x : F) (u v w : Point F m) (d : ℕ)
    (f : linePoints u v → F) (a : F) :
    lineAgrees d (appendLine x (linePoints u v)) (appendPoint x w)
        (appendLineAnswer x ⟨linePoints u v, f⟩) a ↔
      lineAgrees d (linePoints u v) w ⟨linePoints u v, f⟩ a := by
  let L := linePoints u v
  let e := appendLineEquiv x L
  unfold lineAgrees appendLineAnswer
  change (_ = _ ∧ LineHasDegree (f ∘ e.symm) d ∧
    ∃ h : appendPoint x w ∈ appendLine x L, f (e.symm ⟨appendPoint x w, h⟩) = a) ↔
    (_ = _ ∧ LineHasDegree f d ∧ ∃ h : w ∈ L, f ⟨w, h⟩ = a)
  rw [lineHasDegree_append_iff]
  simp only [true_and]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨hw, heval⟩
    have hp := Finset.mem_map.mp hw
    obtain ⟨z, hz, he⟩ := hp
    have hzw := (appendPoint x).injective he
    subst z
    refine ⟨hz, ?_⟩
    have h : e ⟨w, hz⟩ = ⟨appendPoint x w, hw⟩ := Subtype.ext rfl
    rw [← h, e.symm_apply_apply] at heval
    exact heval
  · rintro ⟨hw, heval⟩
    have h : (e ⟨w, hw⟩).val = appendPoint x w := rfl
    have hm : appendPoint x w ∈ appendLine x L := h ▸ (e ⟨w, hw⟩).property
    refine ⟨hm, ?_⟩
    have he : e ⟨w, hw⟩ = ⟨appendPoint x w, hm⟩ := Subtype.ext h
    rw [← he, e.symm_apply_apply, heval]

end Cslib.PCP.LowIndividualDegree
