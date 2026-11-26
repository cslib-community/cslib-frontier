/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.Monotone
public import CslibFrontier.Foundations.BooleanAnalysis.Peres
public import CslibFrontier.Foundations.BooleanAnalysis.Unate
public import CslibFrontier.Foundations.BooleanAnalysis.NoiseSensitivityInfluence
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Peres's theorem on small threshold functions

The majority of three bits is a threshold function, hence a linear threshold function, so it is
unate, it has total influence at most `√3`, and Peres's theorem bounds its noise sensitivity: at
`δ = 1 / 4`, where `⌊1 / δ⌋ = 4`, by `1 / √4 = 1 / 2`, and by `√(3 / 2) √(1 / 4) = √(3 / 8)`.
Theorem 5.35 for the class of linear threshold functions bounds it at `δ = 1 / 3` by `√3 / 3`, and
the exact identity at `m = 2` bounds it at `δ = 1 / 2` by `√2 / 2`. Negating an input of the
conjunction gives the unate function `¬x₀ ∧ x₁`, which is neither monotone nor antitone, and the
literals `±χᵢ` are linear threshold functions. The
parity of two bits is not unate, hence not a linear threshold function, and the parities of all
lengths are not uniformly noise-stable.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisPeres

open Cslib Cslib.BitString Finset Filter Topology
open scoped BigOperators

/-! ### Linear threshold functions are unate -/

-- The majority of three bits is a threshold function, hence unate.
example : IsUnate (majority 3) := (isPTF_one_threshold 3 2).isUnate

-- Its degree-one coefficients sum to at most `√3` in absolute value: their squared sum is at most
-- `3 σ² ≤ 3`.
example : (∑ i, |fourierCoeff (fun x => signVal (majority 3 x)) {i}|) ^ 2 ≤ 3 := by
  have h := sq_sum_abs_fourierCoeff_singleton_le fun x => signVal (majority 3 x)
  have hv := expect_sub_expect_sq_signVal_le_one (majority 3)
  rw [Fintype.card_fin, Nat.cast_ofNat] at h
  linarith

-- Its total influence is at most `√3`.
example : totalInfluence (fun x => signVal (majority 3 x)) ≤ √3 := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    (show IsPTF 1 (majority 3) from isPTF_one_threshold 3 2).totalInfluence_le_sqrt_card

/-- Negating the first input of the conjunction of two bits, `¬x₀ ∧ x₁`. -/
def notAnd (x : Fin 2 → Bool) : Bool :=
  threshold 2 2 (![true, false] + fun i => x i)

/-- `¬x₀ ∧ x₁` is a linear threshold function: negating an input preserves them. -/
theorem isPTF_one_notAnd : IsPTF 1 notAnd :=
  (isPTF_one_threshold 2 2).comp_add_comp _ _

-- It is unate, so its total influence is at most `√(2 σ²)`, and at most `√2`.
example : totalInfluence (fun x => signVal (notAnd x)) ≤
    √(2 * 𝔼 x, (signVal (notAnd x) - 𝔼 y, signVal (notAnd y)) ^ 2) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    isPTF_one_notAnd.isUnate.totalInfluence_le_sqrt_card_mul

example : totalInfluence (fun x => signVal (notAnd x)) ≤ √2 := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    isPTF_one_notAnd.isUnate.totalInfluence_le_sqrt_card

-- But it is neither monotone nor antitone.
example : ¬ Monotone notAnd ∧ ¬ Antitone notAnd := by
  constructor <;> intro h
  · have := h (show ![false, true] ≤ ![true, true] by decide)
    revert this
    decide
  · have := h (show ![false, false] ≤ ![false, true] by decide)
    revert this
    decide

-- The negated literal `-χ₁` on three bits is a linear threshold function, hence unate, and so is
-- the literal `χ₀`.
example : IsUnate fun x : Fin 3 → Bool => true ^^ x 1 := (isPTF_one_xor true 1).isUnate

example : IsPTF 1 fun x : Fin 3 → Bool => false ^^ x 0 := isPTF_one_xor false 0

-- Identifying the last two inputs of the majority and negating the first gives a linear threshold
-- function of two bits.
example : IsPTF 1 fun w : Fin 2 → Bool =>
    majority 3 (![true, false, false] + fun i => w (![0, 1, 1] i)) :=
  (isPTF_one_threshold 3 2).comp_add_comp _ _

/-- NOR of two bits is antitone. -/
theorem antitone_nor : Antitone fun x : Fin 2 → Bool => !threshold 2 1 x := fun _ _ h => by
  have := monotone_threshold 1 h
  dsimp only
  revert this
  cases threshold 2 1 _ <;> cases threshold 2 1 _ <;> decide

-- A monotone function and an antitone function are unate.
example : IsUnate (threshold 2 2) := (monotone_threshold 2).isUnate

example : IsUnate fun x => !threshold 2 1 x := antitone_nor.isUnate

/-! ### Unate directions and the degree-one coefficients -/

-- The influence of bit `1` of the conjunction is its coefficient on `{1}`, which is nonnegative,
-- since the conjunction is monotone; so by Exercise 2.5(a) the conjunction is unate in
-- direction `1`.
example : IsUnateIn 1 (threshold 2 2) :=
  (abs_fourierCoeff_singleton_eq_influence_iff _ 1).1 <| by
    rw [influence_eq_fourierCoeff_singleton_of_monotone (monotone_threshold 2),
      abs_of_nonneg (fourierCoeff_singleton_nonneg_of_monotone (monotone_threshold 2) 1)]

-- NOR is antitone, so its total influence is at most `√(2 σ²)` and at most `√2`, through the
-- antitone bounds and through the unate bound.
example : totalInfluence (fun x => signVal (!threshold 2 1 x)) ≤
    √(2 * 𝔼 x, (signVal (!threshold 2 1 x) - 𝔼 y, signVal (!threshold 2 1 y)) ^ 2) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    totalInfluence_le_sqrt_card_mul_of_antitone antitone_nor

example : totalInfluence (fun x => signVal (!threshold 2 1 x)) ≤ √2 := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    totalInfluence_le_sqrt_card_of_antitone antitone_nor

example : totalInfluence (fun x => signVal (!threshold 2 1 x)) ≤ √2 := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    antitone_nor.isUnate.totalInfluence_le_sqrt_card

-- The conjunction is monotone, so its total influence is at most `√2`.
example : totalInfluence (fun x => signVal (threshold 2 2 x)) ≤ √2 := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    totalInfluence_le_sqrt_card_of_monotone (monotone_threshold (n := 2) 2)

-- The conjunction is unate in direction `0`, so the influence of bit `0` is the absolute value of
-- its coefficient on `{0}`.
example : |fourierCoeff (fun x => signVal (threshold 2 2 x)) {0}| =
    influence 0 (fun x => signVal (threshold 2 2 x)) :=
  (abs_fourierCoeff_singleton_eq_influence_iff _ 0).2 ((monotone_threshold 2).isUnate 0)

-- Raising bit `0` of the all-`false` string changes the parity of two bits from `false` to `true`,
-- so its derivative there is not nonpositive, but it is nonnegative.
example : ¬ derivative 0 (fun x => signVal (parityOn ({0, 1} : Finset (Fin 2)) x))
      (fun _ => false) ≤ 0 ∧
    0 ≤ derivative 0 (fun x => signVal (parityOn ({0, 1} : Finset (Fin 2)) x)) (fun _ => false) :=
  ⟨fun h => absurd ((derivative_signVal_nonpos_iff _ 0 _).1 h) (by decide),
    (derivative_signVal_nonneg_iff _ 0 _).2 (by decide)⟩

-- The parity of two bits is not unate: its coefficient on `{0}` vanishes, but bit `0` has
-- influence one.
theorem not_isUnate_parity₂ : ¬ IsUnate (parityOn ({0, 1} : Finset (Fin 2))) := by
  intro h
  have h0 := (abs_fourierCoeff_singleton_eq_influence_iff _ 0).2 (h 0)
  have hchi : (fun x => signVal (parityOn ({0, 1} : Finset (Fin 2)) x)) = chi ℝ {0, 1} :=
    funext fun x => (chi_eq_signVal_parityOn _ x).symm
  have hne : ({0, 1} : Finset (Fin 2)) ≠ {0} := by decide
  rw [hchi, fourierCoeff_chi, influence_chi] at h0
  simp [hne] at h0

-- Hence it is not a linear threshold function.
example : ¬ IsPTF 1 (parityOn ({0, 1} : Finset (Fin 2))) :=
  fun h => not_isUnate_parity₂ h.isUnate

/-! ### Noise sensitivity from total influence -/

-- The block of `0` under a uniformly random map to `Fin 4` contains a given coordinate with
-- probability `1 / 4`.
example : 𝔼 π : Fin 3 → Fin 4, (if decide (π 1 = 0) then (1 : ℝ) else 0) = 1 / 4 := by
  rw [expect_comp_eq_bernoulliAverage (fun c : Fin 4 => decide (c = 0))
    (fun P : Fin 3 → Bool => if P 1 then (1 : ℝ) else 0), bernoulliAverage_coordinate]
  simp [filter_eq', dens_singleton]

-- The exact identity at `m = 2`, with `I[g] ≤ √2` for every `g` obtained by negating and
-- identifying inputs: `NS_{1/2}[Maj₃] ≤ √2 / 2`.
example : noiseSensitivity (1 / 2) (majority 3) ≤ √2 / 2 := by
  have h := noiseSensitivity_inv_eq_expect_totalInfluence (majority 3) 2
  have hle : 𝔼 z : Fin 3 → Bool, 𝔼 π : Fin 3 → Fin 2,
      totalInfluence (fun w : Fin 2 → Bool => signVal (majority 3 (z + fun i => w (π i)))) ≤
        √2 :=
    expect_le univ_nonempty fun z _ => expect_le univ_nonempty fun π _ => by
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using
        ((show IsPTF 1 (majority 3) from isPTF_one_threshold 3 2).comp_add_comp z
          π).totalInfluence_le_sqrt_card
  rw [show (1 : ℝ) / 2 = ((2 : ℕ) : ℝ)⁻¹ by norm_num, h]
  push_cast
  linarith

-- Theorem 5.35 at `δ = 1 / 3` for the class of linear threshold functions, closed under negating
-- and identifying variables, with `A(m) = √m`: `NS_{1/3}[Maj₃] ≤ √3 / 3`.
example : noiseSensitivity (1 / 3) (majority 3) ≤ √3 / 3 := by
  have hfloor : ⌊((1 : ℝ) / 3)⁻¹⌋₊ = 3 := by norm_num
  have h := noiseSensitivity_le_div_of_comp_add_comp_mem (B := fun _ => IsPTF 1)
    (A := fun m => √(m : ℝ)) (fun z π hf => hf.comp_add_comp z π)
    (fun {n} _ hf => by simpa only [Fintype.card_fin] using hf.totalInfluence_le_sqrt_card)
    (δ := 1 / 3) (by norm_num) (by norm_num) (isPTF_one_threshold 3 2)
  rwa [hfloor, Nat.cast_ofNat] at h

-- The same argument for the single function `¬x₀ ∧ x₁` at `δ = 1 / 2`, where every `g_{z, π}` is a
-- linear threshold function of two bits: `NS_{1/2}[¬x₀ ∧ x₁] ≤ √2 / 2`.
example : noiseSensitivity (1 / 2) notAnd ≤ √2 / 2 := by
  have hfloor : ⌊((1 : ℝ) / 2)⁻¹⌋₊ = 2 := by norm_num
  have h := noiseSensitivity_le_div_of_totalInfluence_le (δ := 1 / 2) (A := √2) (by norm_num)
    (by norm_num) notAnd fun z π => by
      simpa only [hfloor, Fintype.card_fin, Nat.cast_ofNat] using
        (isPTF_one_notAnd.comp_add_comp z π).totalInfluence_le_sqrt_card
  rwa [hfloor, Nat.cast_ofNat] at h

/-! ### Peres's theorem -/

-- Peres's theorem with the floor at `δ = 1 / 4`: `⌊4⌋ = 4` and `1 / √4 = 1 / 2`.
example : noiseSensitivity (1 / 4) (majority 3) ≤ 1 / 2 := by
  have h := (isPTF_one_threshold 3 2).noiseSensitivity_le_inv_sqrt_floor
    (δ := 1 / 4) (by norm_num) (by norm_num)
  have hfloor : ⌊((1 : ℝ) / 4)⁻¹⌋₊ = 4 := by norm_num
  have hsqrt : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
  rwa [hfloor, Nat.cast_ofNat, hsqrt] at h

-- Peres's theorem at `δ = 1 / 4`: `√(3 / 2) √(1 / 4) = √(3 / 8)`.
example : noiseSensitivity (1 / 4) (majority 3) ≤ √(3 / 8) := by
  have h := (isPTF_one_threshold 3 2).noiseSensitivity_le_sqrt_three_div_two_mul
    (δ := 1 / 4) (by norm_num) (by norm_num)
  rwa [← Real.sqrt_mul (by norm_num), show (3 : ℝ) / 2 * (1 / 4) = 3 / 8 by norm_num] at h

/-! ### Uniform noise stability -/

-- The linear threshold functions are uniformly noise-stable: one `ε(δ) → 0` bounds the noise
-- sensitivity of every majority function.
example : ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧
    ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2), ∀ n, noiseSensitivity δ (majority n) ≤ ε δ := by
  obtain ⟨ε, hε, h⟩ := isUniformlyNoiseStable_isPTF_one
  exact ⟨ε, hε, fun δ hδ n => h δ hδ n _ (isPTF_one_threshold n _)⟩

/-- The parity of `n` bits has noise sensitivity `(1 - (1 - 2 δ) ^ n) / 2`. -/
theorem noiseSensitivity_parityOn_univ (δ : ℝ) (n : ℕ) :
    noiseSensitivity δ (parityOn (univ : Finset (Fin n))) = (1 - (1 - 2 * δ) ^ n) / 2 := by
  rw [noiseSensitivity_eq_sum, sum_eq_single univ]
  · simp [fourierCoeff_signVal_parityOn]
  · intro S _ hS
    simp [fourierCoeff_signVal_parityOn, hS]
  · simp

-- The parities are not uniformly noise-stable: at each `0 < δ ≤ 1 / 2` their noise sensitivities
-- tend to `1 / 2`.
example : ¬ IsUniformlyNoiseStable fun n f => f = parityOn (univ : Finset (Fin n)) := by
  rintro ⟨ε, hε, h⟩
  have hhalf (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 2)) : 1 / 2 ≤ ε δ := by
    have hlim : Tendsto (fun n : ℕ => (1 - (1 - 2 * δ) ^ n) / 2) atTop (𝓝 ((1 - 0) / 2)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [hδ.2]) (by linarith [hδ.1])).const_sub
        1).div_const 2
    rw [sub_zero] at hlim
    exact le_of_tendsto' hlim fun n => noiseSensitivity_parityOn_univ δ n ▸ h δ hδ n _ rfl
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 1 / 2 ≤ ε δ :=
    eventually_of_mem (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)) hhalf
  have := ge_of_tendsto hε hev
  norm_num at this

end CslibFrontierTests.BooleanAnalysisPeres
