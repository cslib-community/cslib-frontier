/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily.Matrix
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.ToLin
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.PMF.Expect
import Mathlib.FieldTheory.Finiteness

/-!
# Kernel moments for uniform finite-field matrices

This elementary first-moment argument counts kernel vectors directly.
For a uniform square matrix, each nonzero vector lies in its kernel with probability the
reciprocal of the vector-space cardinality. Summing those probabilities gives the exact first
moment. A nontrivial kernel contains at least one line. This gap above cardinality one sharpens
the resulting square-root moment, which factors for independent coordinate matrices.
-/

public section

namespace Cslib.Probability

open Finset
open scoped BigOperators Matrix

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F]

/-- The expected kernel cardinality of a uniform square matrix is exactly
`2 - 1 / |V|`, including when the vector space has dimension zero. -/
theorem expect_card_ker_mulVecLin :
    (𝔼 A : Matrix ι ι F, (Nat.card (LinearMap.ker A.mulVecLin) : ℝ)) =
      2 - (Fintype.card (ι → F) : ℝ)⁻¹ := by
  classical
  let N : ℝ := Fintype.card (ι → F)
  have hn : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have atom (x : ι → F) (hx : x ≠ 0) :
      (𝔼 A : Matrix ι ι F, if A *ᵥ x = 0 then (1 : ℝ) else 0) = N⁻¹ := by
    rw [Fintype.expect_boole, ← PMF.toReal_uniformOfFintype_map_apply,
      uniformOfFintype_map_mulVec x hx, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
  have kerCount (A : Matrix ι ι F) :
      (Nat.card (LinearMap.ker A.mulVecLin) : ℝ) =
        ∑ x : ι → F, if A *ᵥ x = 0 then 1 else 0 := by
    rw [Finset.sum_boole, Nat.card_eq_fintype_card]
    congr 1
    exact Fintype.card_of_subtype _ (fun x => by simp [LinearMap.mem_ker])
  simp_rw [kerCount]
  rw [expect_sum_comm, ← sum_erase_add _ _ (mem_univ (0 : ι → F))]
  rw [sum_congr rfl (fun x hx => atom x (mem_erase.mp hx).1)]
  simp only [Matrix.mulVec_zero, ↓reduceIte, Fintype.expect_const, sum_const, nsmul_eq_mul,
    card_erase_of_mem (mem_univ _), card_univ, Nat.cast_sub (Fintype.card_pos : 0 < Fintype.card
      (ι → F)), Nat.cast_one]
  change (N - 1) * N⁻¹ + 1 = 2 - N⁻¹
  field_simp
  ring

/-- Over a field of size `q`, the expected square root of the kernel cardinality of a
uniform square matrix is at most `1 + 1/(√q + 1)`. Singular matrices are included. -/
theorem expect_sqrt_card_ker_mulVecLin_le :
    (𝔼 A : Matrix ι ι F, Real.sqrt (Nat.card (LinearMap.ker A.mulVecLin))) ≤
      1 + (Real.sqrt (Fintype.card F) + 1)⁻¹ := by
  classical
  let b := Real.sqrt (Fintype.card F) + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have point (A : Matrix ι ι F) :
      Real.sqrt (Nat.card (LinearMap.ker A.mulVecLin)) ≤
        1 + ((Nat.card (LinearMap.ker A.mulVecLin) : ℝ) - 1) / b := by
    let K := LinearMap.ker A.mulVecLin
    have hk : Nat.card K = Fintype.card F ^ Module.finrank F K := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F)]
    change Real.sqrt (Nat.card K) ≤ 1 + ((Nat.card K : ℝ) - 1) / b
    cases hd : Module.finrank F K with
    | zero => rw [hk, hd]; simp
    | succ n =>
      have hq : (Fintype.card F : ℝ) ≤ (Nat.card K : ℝ) := by
        exact_mod_cast (show Fintype.card F ≤ Nat.card K by
          rw [hk, hd, pow_succ]
          exact Nat.le_mul_of_pos_left _ (pow_pos Fintype.card_pos _))
      have hs := Real.sqrt_le_sqrt hq
      have hone : (1 : ℝ) ≤ Real.sqrt (Nat.card K) :=
        Real.one_le_sqrt.mpr ((by exact_mod_cast Fintype.card_pos :
          (1 : ℝ) ≤ Fintype.card F).trans hq)
      suffices bound : Real.sqrt (Nat.card K) - 1 ≤ ((Nat.card K : ℝ) - 1) / b by linarith
      rw [le_div_iff₀ hb]
      calc (Real.sqrt (Nat.card K) - 1) * b
          ≤ (Real.sqrt (Nat.card K) - 1) * (Real.sqrt (Nat.card K) + 1) := by
            have := sub_nonneg.mpr hone; dsimp only [b]; gcongr
        _ = Real.sqrt (Nat.card K) ^ 2 - 1 := by ring
        _ = (Nat.card K : ℝ) - 1 := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  refine (expect_le_expect fun A _ => point A).trans ?_
  rw [expect_add_distrib, Fintype.expect_const, ← expect_div, expect_sub_distrib,
    Fintype.expect_const, expect_card_ker_mulVecLin]
  change 1 + (2 - (Fintype.card (ι → F) : ℝ)⁻¹ - 1) / b ≤ 1 + b⁻¹
  rw [← one_div b]
  gcongr
  have := inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (ι → F)) : (0 : ℝ) ≤ _)
  linarith

/-- For independent uniform square matrices, count all tuples killed by their respective
matrices. The square-root moment of that joint kernel is at most the product of the individual
bounds. -/
theorem expect_sqrt_card_joint_kernel_le (r : ℕ) :
    (𝔼 A : Fin r → Matrix ι ι F,
      Real.sqrt (Nat.card {v : Fin r → ι → F // ∀ j, A j *ᵥ v j = 0})) ≤
      (1 + (Real.sqrt (Fintype.card F) + 1)⁻¹) ^ r := by
  classical
  let weight (A : Matrix ι ι F) := Real.sqrt (Nat.card (LinearMap.ker A.mulVecLin))
  have factor (A : Fin r → Matrix ι ι F) :
      Real.sqrt (Nat.card {v : Fin r → ι → F // ∀ j, A j *ᵥ v j = 0}) =
        ∏ j, weight (A j) := by
    let e := Equiv.subtypePiEquivPi (p := fun (j : Fin r) (v : ι → F) => A j *ᵥ v = 0)
    rw [Nat.card_congr e, Nat.card_pi, Nat.cast_prod,
      Real.sqrt_prod _ (fun _ _ => Nat.cast_nonneg _)]
    rfl
  simp_rw [factor]
  rw [← Fintype.piFinset_univ, ← Finset.expect_pow]
  exact pow_le_pow_left₀ (expect_nonneg fun _ _ => Real.sqrt_nonneg _)
    expect_sqrt_card_ker_mulVecLin_le r

end Cslib.Probability
