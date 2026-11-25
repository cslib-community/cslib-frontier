/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.PrefixCommutator
import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Transferring the first measurement of a sequential transcript

For a score weighted by commuting effects, the first measurement can be replaced
by its commuting copy after paying its copy discrepancy and its commutator
defect with the remaining transcript. If the weights depend on the first
outcome only through a finite class, the estimate depends on the number of
classes. Counting successes uses just the two classes success and failure.
This is the transfer step in [Ji, Natarajan, Vidick, Wright and Yuen, Lemma 12.21]
[JNVWY2020LowIndividualDegree].
-/

public section

namespace Cslib.Quantum

open Finset
open scoped Real

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace Measurement

variable {α β B : Type*} [Fintype α] [Fintype β] [Fintype B]

private theorem sum_norm_weighted_effect_le (φ : AlgState A) (R : Measurement α A)
    (hR : R.IsProjective) (classify : α → B) (W : B → A)
    (hW : ∀ b, star (W b) * W b ≤ 1) (K : A) :
    ∑ a, φ.norm (R.effect a * (W (classify a) * K)) ^ 2 ≤ Fintype.card B * φ.norm K ^ 2 := by
  classical
  rw [← sum_fiberwise univ classify]
  calc
    _ ≤ ∑ b : B, φ.norm K ^ 2 := by
      refine sum_le_sum fun b _ => ?_
      calc
        _ ≤ ∑ a, φ.norm (R.effect a * (W b * K)) ^ 2 := by
          refine (sum_congr rfl fun a ha => ?_).le.trans
            (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _))
          rw [(mem_filter.mp ha).2]
        _ = φ.norm (W b * K) ^ 2 := sum_norm_effect_mul_sq φ R hR _
        _ ≤ _ := pow_le_pow_left₀ (φ.norm_nonneg _)
          (φ.norm_mul_le_of_star_mul_self_le_one (hW b) _) _
    _ = _ := by simp [nsmul_eq_mul]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem transfer_identity (p r K W : A)
    (hp : star p = p) (hr : star r = r) (hW : star W = W)
    (hrr : r * r = r) (hpr : Commute p r) (hKr : Commute K r)
    (hpW : Commute p W) (hKW : Commute K W) :
    p * (star K * K) * p * W - (star K * K) * W * r =
      star (K * p) * (W * K * (p - r)) +
      star (K * p - p * K) * (W * K * r) +
      star (r * (W * K)) * (p * K - K * p) +
      star (r * (W * K)) * (K * (p - r)) := by
  have hleft : p * (star K * K) * p * W = p * star K * W * K * p := by
    simp only [mul_assoc, hpW.eq, hKW.left_comm p]
  have hright : (star K * K) * W * r = star K * (W * K) * r := by
    simp only [mul_assoc, hKW.left_comm r]
  rw [hleft, hright]
  simp only [star_mul, star_sub, hp, hr, hW]
  have he : p * star K * W * K * p - star K * (W * K) * r =
      p * star K * W * K * (p - r) +
      (p * star K - star K * p) * (W * K * r) +
      star K * W * r * (p * K - K * p) +
      star K * W * r * (K * (p - r)) := by
    calc
      _ = p * star K * W * K * (p - r) + (p * star K) * (W * K * r) -
          star K * (W * K) * r := by noncomm_ring
      _ = _ := by
        have h₁ : star K * p * (W * K * r) = star K * W * r * (p * K) := by
          simp only [mul_assoc, hKr.eq, hpW.left_comm (r * K), hpr.left_comm K]
        have h₂ : star K * (W * K) * r = star K * W * r * (K * r) := by
          simp only [mul_assoc, hKr.eq, ← mul_assoc r r K, hrr]
        rw [sub_mul, h₁, h₂]
        noncomm_ring
  simpa only [mul_assoc] using he

/-- Move the first projection of a weighted transcript to its commuting copy. The
weight may also depend on the remaining transcript. The factor involving the finite
class type accounts for using a different weight for each class of first outcomes. -/
theorem abs_first_transcript_score_sub_le {k : ℕ} (φ : AlgState A)
    (P R : Measurement α A) (hP : P.IsProjective) (hR : R.IsProjective)
    (M : Fin k → Measurement β A) (hM : ∀ j, (M j).IsProjective)
    (hPR : ∀ a b, Commute (P.effect a) (R.effect b))
    (hMR : ∀ j a b, Commute ((M j).effect a) (R.effect b))
    (classify : α → B) (W : B → (Fin k → β) → A)
    (hW : ∀ b g, W b g ∈ Set.Icc (0 : A) 1)
    (hPW : ∀ a b g, Commute (P.effect a) (W b g))
    (hMW : ∀ j a b g, Commute ((M j).effect a) (W b g)) :
    |(∑ a, ∑ g, (φ (P.effect a * (sequentialProjective M hM).effect g *
        P.effect a * W (classify a) g)).re) -
      (∑ a, ∑ g, (φ ((sequentialProjective M hM).effect g * W (classify a) g * R.effect a)).re)|
      ≤ (1 + √(Fintype.card B : ℝ)) *
        (√(copyDefect φ P R) + √(transcriptCommutatorDefect φ P M)) := by
  classical
  let K (g : Fin k → β) := star (transcriptProduct M g)
  let p (z : α × (Fin k → β)) := P.effect z.1
  let r (z : α × (Fin k → β)) := R.effect z.1
  let t (z : α × (Fin k → β)) := K z.2
  let w (z : α × (Fin k → β)) := W (classify z.1) z.2
  let X z := t z * p z
  let Y z := w z * t z * r z
  let Z z := r z * (w z * t z)
  let D z := t z * (p z - r z)
  let C z := t z * p z - p z * t z
  have hK (x : A) : ∑ g, φ.norm (K g * x) ^ 2 = φ.norm x ^ 2 :=
    sum_norm_star_transcriptProduct_mul_sq φ M hM x
  have hcontract (b : B) (g : Fin k → β) : star (W b g) * W b g ≤ 1 := by
    rw [(hW b g).1.isSelfAdjoint.star_eq]
    exact (mul_self_le_self_of_nonneg_of_le_one (hW b g).1 (hW b g).2).trans (hW b g).2
  have hX : ∑ z, φ.norm (X z) ^ 2 = 1 := by
    simp only [X, p, t, Fintype.sum_prod_type, hK]
    simpa only [mul_one, AlgState.norm_one, one_pow] using sum_norm_effect_mul_sq φ P hP 1
  have hY : ∑ z, φ.norm (Y z) ^ 2 ≤ 1 := by
    calc
      _ ≤ ∑ a : α, ∑ g, φ.norm (K g * R.effect a) ^ 2 := by
        rw [Fintype.sum_prod_type]
        refine sum_le_sum fun a _ => sum_le_sum fun g _ => ?_
        dsimp only [Y, w, t, r]
        rw [mul_assoc]
        exact pow_le_pow_left₀ (φ.norm_nonneg _)
          (φ.norm_mul_le_of_star_mul_self_le_one (hcontract (classify a) g) _) _
      _ = 1 := by
        simp only [hK]
        simpa only [mul_one, AlgState.norm_one, one_pow] using sum_norm_effect_mul_sq φ R hR 1
  have hZ : ∑ z, φ.norm (Z z) ^ 2 ≤ Fintype.card B := by
    rw [Fintype.sum_prod_type, sum_comm]
    calc
      _ ≤ ∑ g, Fintype.card B * φ.norm (K g) ^ 2 :=
        sum_le_sum fun g _ => sum_norm_weighted_effect_le φ R hR classify
          (fun b => W b g) (fun b => hcontract b g) (K g)
      _ = _ := by
        simpa only [mul_one, AlgState.norm_one, one_pow, ← mul_sum] using
          congrArg ((Fintype.card B : ℝ) * ·) (hK 1)
  have hD : ∑ z, φ.norm (D z) ^ 2 = copyDefect φ P R := by
    simp only [D, p, r, t, Fintype.sum_prod_type, hK, copyDefect]
  have hC : ∑ z, φ.norm (C z) ^ 2 = transcriptCommutatorDefect φ P M := by
    simp only [C, p, t, K, Fintype.sum_prod_type, transcriptCommutatorDefect,
      φ.norm_sub_comm (star (transcriptProduct M _) * P.effect _)]
  have hc (z : α × (Fin k → β)) :
      (φ (p z * (star (t z) * t z) * p z * w z)).re -
      (φ ((star (t z) * t z) * w z * r z)).re =
        (φ (star (X z) * (w z * D z))).re +
        (φ (star (C z) * Y z)).re +
        (φ (star (Z z) * (-C z))).re +
        (φ (star (Z z) * D z)).re := by
    have h := transfer_identity (p z) (r z) (t z) (w z)
      ((P.nonneg z.1).isSelfAdjoint.star_eq) ((R.nonneg z.1).isSelfAdjoint.star_eq)
      ((hW (classify z.1) z.2).1.isSelfAdjoint.star_eq) (hR z.1)
      (hPR z.1 z.1) (star_transcriptProduct_commute M _ (fun j a => hMR j a z.1) z.2)
      (hPW z.1 _ _) (star_transcriptProduct_commute M _ (fun j a => hMW j a _ _) z.2)
    rw [← Complex.sub_re, ← map_sub, h]
    simp only [X, Y, Z, D, C, neg_sub, mul_assoc, map_add, Complex.add_re]
  have hwD : ∑ z, φ.norm (w z * D z) ^ 2 ≤ copyDefect φ P R := by
    rw [← hD]
    exact sum_le_sum fun z _ => pow_le_pow_left₀ (φ.norm_nonneg _)
      (φ.norm_mul_le_of_star_mul_self_le_one (hcontract (classify z.1) z.2) _) _
  have hbound (U V : α × (Fin k → β) → A) {u v : ℝ}
      (hu : ∑ z, φ.norm (U z) ^ 2 ≤ u) (hv : ∑ z, φ.norm (V z) ^ 2 ≤ v) :
      |∑ z, (φ (star (U z) * V z)).re| ≤ √u * √v :=
    (φ.abs_sum_re_star_mul_le U V).trans
      (mul_le_mul (Real.sqrt_le_sqrt hu) (Real.sqrt_le_sqrt hv) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))
  have h₁ := hbound X (fun z => w z * D z) hX.le hwD
  have h₂ := hbound C Y hC.le hY
  have h₃ := hbound Z (fun z => -C z) hZ (by simpa only [φ.norm_neg] using hC.le)
  have h₄ := hbound Z D hZ hD.le
  simp only [Real.sqrt_one, one_mul, mul_one] at h₁ h₂
  suffices h : |(∑ z, (φ (p z * (star (t z) * t z) * p z * w z)).re) -
      (∑ z, (φ ((star (t z) * t z) * w z * r z)).re)| ≤
        (1 + √(Fintype.card B : ℝ)) *
          (√(copyDefect φ P R) + √(transcriptCommutatorDefect φ P M)) by
    simpa only [Fintype.sum_prod_type, sequentialProjective_effect, p, t, K, r, w, star_star]
      using h
  simp only [← sum_sub_distrib, hc, sum_add_distrib]
  exact ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h₁ h₂)) h₃))
    h₄)).trans_eq (by ring)

end Measurement
end Cslib.Quantum
