/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.CompletedMeasurement
public import CslibFrontier.Foundations.Quantum.Algebra.SuccessfulAgreement

/-!
# Agreement restricted to successful outcomes

A projective measurement with failure can be compared with a commuting
projective measurement by multiplying the latter's effects by the success
projection. A separate estimate controls expressions with the complementary
failure projection when the opposing effects have a positive common upper bound.
-/

public section

namespace Cslib.Quantum

open Finset
open scoped BigOperators Real

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace Measurement

variable {α : Type*} [Fintype α]

/-- Successful outcomes are fixed by multiplication by the success projection. -/
theorem IsProjective.successfulEffect_mul_some (P : Measurement (Option α) A)
    (hp : P.IsProjective) (a : α) :
    P.successfulEffect * P.effect (some a) = P.effect (some a) := by
  unfold successfulEffect
  rw [sum_mul, sum_eq_single a (fun b _ hb => hp.mul_eq_zero (fun h => hb (Option.some.inj h)))
    (by simp), hp]

theorem IsProjective.successfulEffect_mul_self (P : Measurement (Option α) A)
    (hp : P.IsProjective) :
    P.successfulEffect * P.successfulEffect = P.successfulEffect := by
  change P.successfulEffect * (∑ a, P.effect (some a)) = _
  rw [mul_sum]
  exact sum_congr rfl fun a _ => hp.successfulEffect_mul_some P a

/-- Gating the second measurement by the first measurement's success projection makes
its squared state distance from the successful outcomes exactly twice their mismatch. -/
theorem sum_norm_sub_success_mul_sq_eq (φ : AlgState A)
    (P : Measurement (Option α) A) (Q : Measurement α A)
    (hp : P.IsProjective) (hq : Q.IsProjective)
    (hc : ∀ a b, Commute (P.effect a) (Q.effect b)) :
    (∑ a, φ.norm (P.effect (some a) - P.successfulEffect * Q.effect a) ^ 2) =
      2 * successfulMismatch φ P Q := by
  let G := P.successfulEffect
  have hG₀ : 0 ≤ G := sum_nonneg fun a _ => P.nonneg (some a)
  have hG := hG₀.isSelfAdjoint.star_eq
  have hGQ (a : α) : Commute G (Q.effect a) :=
    Commute.sum_left _ _ _ fun b _ => hc _ _
  have hPG (a : α) : Commute (P.effect (some a)) G :=
    (Commute.sum_left _ _ _ fun b _ => hp.commute_effect (some b) (some a)).symm
  have h (a : α) : φ.norm (P.effect (some a) - G * Q.effect a) ^ 2 =
      (φ (P.effect (some a))).re + (φ (G * Q.effect a)).re -
        2 * (φ (P.effect (some a) * Q.effect a)).re := by
    let E := P.effect (some a)
    let B := Q.effect a
    have hE : star E = E := (P.nonneg _).isSelfAdjoint.star_eq
    have hGB : star (G * B) = G * B := by
      rw [star_mul, hG, (Q.nonneg a).isSelfAdjoint.star_eq, (hGQ a).eq]
    have hEGB : E * (G * B) = E * B := by
      rw [← mul_assoc, (hPG a).eq, hp.successfulEffect_mul_some P a]
    have hGBE : G * B * E = E * B := by
      rw [mul_assoc, ← (hc (some a) a).eq, ← mul_assoc, hp.successfulEffect_mul_some P a]
    have hGBsq : G * B * (G * B) = G * B := by
      have hBcomm : Commute G B := hGQ a
      calc
        _ = G * (B * G) * B := by simp only [mul_assoc]
        _ = G * (G * B) * B := by rw [← hBcomm.eq]
        _ = (G * G) * (B * B) := by simp only [mul_assoc]
        _ = _ := by rw [hp.successfulEffect_mul_self P, show B * B = B from hq a]
    change φ.norm (E - G * B) ^ 2 = _
    rw [AlgState.norm_sq, star_sub, hE, hGB, sub_mul, mul_sub, mul_sub,
      show E * E = E from hp _, hEGB, hGBE, hGBsq]
    simp only [map_sub, Complex.sub_re]
    ring
  have hsum : (∑ a, (φ (G * Q.effect a)).re) = (φ G).re := by
    simp only [← Complex.re_sum, ← map_sum, ← mul_sum, Q.sum_effect, mul_one]
  change (∑ a, φ.norm (P.effect (some a) - G * Q.effect a) ^ 2) = _
  simp only [h, sum_sub_distrib, sum_add_distrib, ← mul_sum, hsum]
  unfold successfulMismatch
  simp only [mul_sub, mul_one, map_sub, Complex.sub_re, sum_sub_distrib]
  have hGsum : (φ G).re = ∑ a, (φ (P.effect (some a))).re := by
    simp only [G, successfulEffect, map_sum, Complex.re_sum]
  rw [hGsum]
  ring

/-- Products of successful projections of two measurements form a subnormalized family. -/
theorem sum_successful_product_sq_le {β : Type*} [Fintype β]
    (P : Measurement (Option α) A) (N : Measurement (Option β) A)
    (hp : P.IsProjective) (hn : N.IsProjective) :
    (∑ a : β, ∑ g : α, star (P.effect (some g) * N.effect (some a)) *
      (P.effect (some g) * N.effect (some a))) ≤ 1 := by
  have hpSum : P.successfulEffect ≤ 1 := by
    rw [← sub_nonneg, ← P.effect_none_eq_one_sub_successfulEffect]
    exact P.nonneg none
  have hnSum : N.successfulEffect ≤ 1 := by
    rw [← sub_nonneg, ← N.effect_none_eq_one_sub_successfulEffect]
    exact N.nonneg none
  have he (a : β) (g : α) :
      star (P.effect (some g) * N.effect (some a)) * (P.effect (some g) * N.effect (some a)) =
        N.effect (some a) * P.effect (some g) * N.effect (some a) := by
    simp only [star_mul, (P.nonneg _).isSelfAdjoint.star_eq,
      (N.nonneg _).isSelfAdjoint.star_eq, ← mul_assoc]
    rw [mul_assoc (N.effect (some a)), hp]
  simp only [he, ← sum_mul, ← mul_sum]
  change (∑ a : β, N.effect (some a) * P.successfulEffect * N.effect (some a)) ≤ 1
  refine (sum_le_sum fun a _ => ?_).trans hnSum
  simpa only [mul_one, hn (some a)] using
    (N.nonneg (some a)).isSelfAdjoint.conjugate_le_conjugate hpSum

/-- Swapping the order of two point effects in a product with a failure projection costs
at most the square root of their pair commutator defect. Projectivity of the preceding
measurements bounds the normalization of the coefficients. -/
theorem abs_sum_failure_pointOrder_sub_le {β : Type*} [Fintype β]
    (φ : AlgState A) (P : Measurement (Option α) A) (N : Measurement (Option β) A)
    (hp : P.IsProjective) (hn : N.IsProjective) (B : Measurement α A) (C : Measurement β A) :
    |(∑ a, ∑ b, (φ (P.effect (some a) * N.effect (some b) * P.effect none *
        (B.effect a * C.effect b))).re) -
      (∑ a, ∑ b, (φ (P.effect (some a) * N.effect (some b) * P.effect none *
        (C.effect b * B.effect a))).re)| ≤ √(pairCommutatorDefect φ B C) := by
  let X (z : α × β) := P.effect none * (N.effect (some z.2) * P.effect (some z.1))
  let D (z : α × β) := B.effect z.1 * C.effect z.2 - C.effect z.2 * B.effect z.1
  have hF : star (P.effect none) * P.effect none ≤ 1 := by
    rw [(P.nonneg none).isSelfAdjoint.star_eq, hp none]
    exact P.effect_le_one none
  have hX : (∑ z, φ.norm (X z) ^ 2) ≤ 1 := by
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ a : α, ∑ b : β, φ.norm (N.effect (some b) * P.effect (some a)) ^ 2 := by
        refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
        exact pow_le_pow_left₀ (φ.norm_nonneg _)
          (φ.norm_mul_le_of_star_mul_self_le_one hF _) _
      _ ≤ ∑ a : α, φ.norm (P.effect (some a)) ^ 2 :=
        sum_le_sum fun a _ =>
          sum_norm_some_effect_mul_sq_le φ N hn (P.effect (some a))
      _ ≤ 1 := by
        simpa only [mul_one, AlgState.norm_one, one_pow] using
          sum_norm_some_effect_mul_sq_le φ P hp 1
  have h := (φ.abs_sum_re_star_mul_le X D).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hX) (Real.sqrt_nonneg _))
  simpa only [X, D, Fintype.sum_prod_type, star_mul,
    (P.nonneg _).isSelfAdjoint.star_eq, (N.nonneg _).isSelfAdjoint.star_eq, ← mul_assoc,
    mul_sub, map_sub, Complex.sub_re, sum_sub_distrib, pairCommutatorDefect, Real.sqrt_one, one_mul]
    using h

end Measurement

/-- A common upper bound for the middle operators controls the sum of conjugates
by the failure projection and a normalized family. -/
theorem sum_failure_conjugate_le {ι : Type*} [Fintype ι] (K H : ι → A) (F Z : A)
    (hF : IsSelfAdjoint F) (hFsq : F * F = F) (hK : ∑ i, star (K i) * K i ≤ 1)
    (hZ : 0 ≤ Z) (hle : ∀ i, H i ≤ Z) (hKZ : ∀ i, Commute (K i) Z) (hFZ : Commute F Z) :
    (∑ i, star (K i * F) * H i * (K i * F)) ≤ F * Z := by
  refine (sum_le_sum fun i _ => star_left_conjugate_le_conjugate (hle i) (K i * F)).trans ?_
  have hf : F * (∑ i, star (K i) * K i) * F ≤ F := by
    simpa only [hF.star_eq, mul_one, hFsq] using star_right_conjugate_le_conjugate hK F
  have hstar (i : ι) : Commute (star (K i)) Z := by
    simpa only [hZ.isSelfAdjoint.star_eq] using (hKZ i).star_star
  have hsumc : Commute (∑ i, star (K i) * K i) Z :=
    Commute.sum_left _ _ _ fun i _ => (hstar i).mul_left (hKZ i)
  have hc : Commute (F - F * (∑ i, star (K i) * K i) * F) Z :=
    hFZ.sub_left ((hFZ.mul_left hsumc).mul_left hFZ)
  have hprod := Commute.mul_nonneg (sub_nonneg.mpr hf) hZ hc
  simp only [sub_mul, sub_nonneg] at hprod
  have hterm (i : ι) : star (K i * F) * Z * (K i * F) = F * (star (K i) * K i) * F * Z := by
    simp only [star_mul, hF.star_eq, mul_assoc, (hKZ i).symm.left_comm F, ← hFZ.eq]
  simp only [hterm, ← sum_mul, ← mul_sum]
  exact hprod

/-- A common majorant for contracting effects bounds the error from removing a
commuting success projection. The operators `K` need only satisfy the indicated
sum-of-squares bound. -/
theorem AlgState.abs_sum_failure_mul_le {ι : Type*} [Fintype ι] (φ : AlgState A)
    (K H : ι → A) (F Z : A) (hF : IsSelfAdjoint F) (hFsq : F * F = F)
    (hK : ∑ i, star (K i) * K i ≤ 1)
    (hH : ∀ i, H i ∈ Set.Icc (0 : A) 1) (hZ : 0 ≤ Z) (hle : ∀ i, H i ≤ Z)
    (hKH : ∀ i, Commute (K i) (H i)) (hKZ : ∀ i, Commute (K i) Z)
    (hFH : ∀ i, Commute F (H i)) (hFZ : Commute F Z) :
    |∑ i, (φ (star (K i) * K i * F * H i)).re| ≤ √((φ (F * Z)).re) := by
  let X (i : ι) := K i * F
  have hnormK : (∑ i, φ.norm (K i) ^ 2) ≤ 1 := by
    simpa only [AlgState.norm_sq, ← Complex.re_sum, ← map_sum] using φ.re_apply_le_one hK
  have hnormX (i : ι) : φ.norm (X i * H i) ^ 2 ≤
      (φ (star (X i) * Z * X i)).re := by
    have hXH : Commute (X i) (H i) := (hKH i).mul_left (hFH i)
    have hHH : H i * H i ≤ Z :=
      (mul_self_le_self_of_nonneg_of_le_one (hH i).1 (hH i).2).trans (hle i)
    rw [AlgState.norm_sq, hXH.eq, star_mul, (hH i).1.isSelfAdjoint.star_eq,
      mul_assoc, ← mul_assoc (H i)]
    simpa only [mul_assoc] using φ.re_apply_mono (star_left_conjugate_le_conjugate hHH (X i))
  have hsum := sum_failure_conjugate_le K (fun _ => Z) F Z hF hFsq hK hZ
    (fun _ => le_rfl) hKZ hFZ
  have hnorm : (∑ i, φ.norm (X i * H i) ^ 2) ≤ (φ (F * Z)).re :=
    (sum_le_sum fun i _ => hnormX i).trans (by
      simpa only [← Complex.re_sum, ← map_sum] using φ.re_apply_mono hsum)
  have h := φ.abs_sum_re_star_mul_le K (fun i => X i * H i)
  simp only [X, ← mul_assoc] at h
  exact h.trans (by
    simpa only [Real.sqrt_one, one_mul] using
      mul_le_mul (Real.sqrt_le_sqrt hnormK) (Real.sqrt_le_sqrt hnorm)
        (Real.sqrt_nonneg _) (by norm_num))

end Cslib.Quantum
