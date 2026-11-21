/-
Copyright (c) 2026 CSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SigningROM
public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Index

/-!
# Counting preimages of an ML-DSA signing commitment

The preimage count of Barbosa et al. [BarbosaEtAl2023, Appendix A.1, equation (21), p. 34], used
in [FallahpourFehrHuang2025, §4.1, equation (6)], bounds the largest atom of the rounded commitment
by counting preimages on the first ℓ rows. Both inequalities use `2γ₁ − 1` per mask coefficient.
The FIPS 204 interval `[1 − γ₁, γ₁]` contains `2γ₁` integers, giving `(2γ₁)^(nℓ)` masks here.
At a prescribed high part, each coefficient has at most `2γ₂ + 1` possible low parts.
Each reconstructed vector has at most as many preimages as the kernel of the square submatrix.
-/

public section

namespace Cslib.Crypto.MLDSA

open Finset
open scoped ENNReal

variable (P : Params)

private abbrev Mask := Fin P.ℓ → Fin P.n → ZMod P.q

/-- The largest commitment probability for a fixed public matrix, in terms of the size of
the kernel on the first ℓ rows. This applies also when the square submatrix is singular. -/
theorem commitmentGuessProbability_le_kernel [NeZero P.q]
    (hγ : 0 < P.γ₁) (h₂ : 0 < P.γ₂) (hq : 2 * P.γ₁ < P.q) (hdim : P.ℓ ≤ P.k)
    (A : Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q)) :
    let top := A.submatrix (Fin.castLE hdim) id
    commitmentGuessProbability P hγ A ≤
      (Nat.card { y : Fin P.ℓ → Fin P.n → ZMod P.q // moduleSISMap top y = 0 } : ℝ≥0∞) *
        ((2 * P.γ₂ + 1 : ℕ) ^ (P.ℓ * P.n) : ℝ≥0∞) /
          ((2 * P.γ₁ : ℕ) ^ (P.ℓ * P.n) : ℝ≥0∞) := by
  classical
  intro top
  let f : Mask P →+ Mask P :=
    { toFun := moduleSISMap top
      map_zero' := moduleSISMap_zero top
      map_add' := moduleSISMap_add top }
  let kernel := univ.filter fun y : Mask P => f y = 0
  have hker : Nat.card { y : Mask P // moduleSISMap top y = 0 } = kernel.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [hker]
  apply iSup_le
  intro w
  let same := univ.filter fun y : Mask P => w = highBitsVec P (moduleSISMap A y)
  let lowBox := Fintype.piFinset fun _ : Fin P.ℓ => Fintype.piFinset fun _ : Fin P.n =>
    Icc (-(P.γ₂ : ℤ)) (P.γ₂ : ℤ)
  let rebuild (v : Fin P.ℓ → Fin P.n → ℤ) : Mask P := fun i j =>
    ((w (Fin.castLE hdim i) j * (2 * P.γ₂ : ℕ) + v i j : ℤ) : ZMod P.q)
  have maps (y) (hy : y ∈ same) : f y ∈ lowBox.image rebuild := by
    have hw := (mem_filter.mp hy).2
    let lows := fun (i : Fin P.ℓ) (j : Fin P.n) => lowBits P.q P.γ₂ (f y i j)
    refine mem_image.mpr ⟨lows, ?_, ?_⟩
    · exact Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mpr fun j =>
        mem_Icc.mpr (abs_le.mp (abs_lowBits_le h₂ _))
    · funext i j
      dsimp only [rebuild, lows]
      rw [hw]
      exact intCast_highBits_mul_add_lowBits (γ₂ := P.γ₂) (f y i j)
  have fibers (v : Mask P) : (same.filter fun y => f y = v).card ≤ kernel.card := by
    by_cases h : (same.filter fun y => f y = v).Nonempty
    · obtain ⟨z, hz⟩ := h
      calc
        _ ≤ (univ.filter fun y : Mask P => f y = v).card :=
          card_le_card (filter_subset_filter _ (subset_univ _))
        _ = kernel.card := AddMonoidHom.card_fiber_eq_of_mem_range f
          ⟨z, (mem_filter.mp hz).2⟩ ⟨0, map_zero f⟩
    · simp [not_nonempty_iff_eq_empty.mp h]
  have hbox : lowBox.card = (2 * P.γ₂ + 1) ^ (P.ℓ * P.n) := by
    have hi : ((P.γ₂ : ℤ) + 1 - -(P.γ₂ : ℤ)).toNat = 2 * P.γ₂ + 1 := by lia
    simp only [lowBox, Fintype.card_piFinset, Int.card_Icc, hi, prod_const, card_univ,
      Fintype.card_fin, ← pow_mul, Nat.mul_comm P.n P.ℓ]
  have hcount := card_le_mul_card_image_of_maps_to maps kernel.card (fun v _ => fibers v)
  have hcount' := hcount.trans (Nat.mul_le_mul_left _ (card_image_le (s := lowBox) (f := rebuild)))
  rw [hbox] at hcount'
  calc
    _ = ∑ y ∈ same, signingMaskLaw P hγ y := by
      simp only [PMF.map_apply, tsum_fintype, same, sum_filter]
      apply sum_congr rfl
      intro y _
      split_ifs <;> rfl
    _ ≤ ∑ _y ∈ same, ((2 * P.γ₁ : ℕ) ^ (P.ℓ * P.n) : ℝ≥0∞)⁻¹ :=
      sum_le_sum fun y _ => signingMaskLaw_apply_le P hγ hq y
    _ = (same.card : ℝ≥0∞) / ((2 * P.γ₁ : ℕ) ^ (P.ℓ * P.n) : ℝ≥0∞) := by
      rw [sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ _ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount') zero_le

namespace FIPS204

/-- The integral exponent in the rounded-commitment preimage bound for each FIPS 204 level.
A kernel of size `K` gives maximum commitment probability at most `K / 2^b`. -/
@[expose] def Level.commitmentBoxBits : Level → ℕ
  | .mlDSA44 => 471
  | .mlDSA65 => 1281
  | .mlDSA87 => 1794

/-- Number of masks that the first ℓ rows of the public matrix send to zero, counted on
the entire coefficient module. This equals one for an invertible square submatrix. -/
@[expose] noncomputable def commitmentKernelSize (s : Level) (A : PublicMatrix s) : ℕ :=
  let h : s.params.ℓ ≤ s.params.k := by cases s <;> decide
  Nat.card { y : Fin s.params.ℓ → Poly // moduleSISMap (A.submatrix (Fin.castLE h) id) y = 0 }

/-- A fixed public matrix costs its actual kernel size in the concrete signing-commitment
bound. The powers of two use the mask intervals and rounding widths from FIPS 204, Table 1. -/
theorem commitmentGuessProbability_le_kernel_div_pow (s : Level) (A : PublicMatrix s) :
    (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal ≤
      (commitmentKernelSize s A : ℝ) / 2 ^ s.commitmentBoxBits := by
  let P := s.params
  have hγ : 0 < P.γ₁ := by cases s <;> decide
  have hdim : P.ℓ ≤ P.k := by cases s <;> decide
  have h := commitmentGuessProbability_le_kernel P hγ (by cases s <;> decide)
    (by cases s <;> decide) hdim A
  change _ ≤ (commitmentKernelSize s A : ℝ≥0∞) * _ / _ at h
  have hf := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast] at hf
  have rounded : (2 * P.γ₂ + 1) ^ (P.ℓ * P.n) * 2 ^ s.commitmentBoxBits ≤
      (2 * P.γ₁) ^ (P.ℓ * P.n) := by cases s <;> decide +kernel
  have ratio : ((2 * P.γ₂ + 1 : ℕ) : ℝ) ^ (P.ℓ * P.n) / ((2 * P.γ₁ : ℕ) : ℝ) ^ (P.ℓ * P.n) ≤
      1 / (2 : ℝ) ^ s.commitmentBoxBits := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    rw [one_mul]
    exact_mod_cast rounded
  rw [mul_div_assoc] at hf
  exact hf.trans (by simpa only [← mul_div_assoc, mul_one] using
    mul_le_mul_of_nonneg_left ratio (Nat.cast_nonneg (commitmentKernelSize s A)))

end FIPS204

end Cslib.Crypto.MLDSA
