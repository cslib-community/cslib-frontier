/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Noise
public import CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Defs.Filter
import CslibFrontier.Foundations.BooleanAnalysis.NoiseSensitivityInfluence
import CslibFrontier.Foundations.BooleanAnalysis.Unate

/-!
# Peres's theorem

**Peres's theorem**: a linear threshold function `f` has noise sensitivity `NS_δ[f] ≤ O(√δ)`
[O'Donnell, Section 5.5][ODonnell2014]. Here a linear threshold function is a polynomial threshold
function of degree at most one, `BitString.IsPTF 1`, on an arbitrary finite coordinate type; the
threshold functions, the majority function among them, and the literals are examples
(`BitString.isPTF_one_threshold`, `BitString.isPTF_one_xor`).

The proof follows the book. Negating and identifying the input variables of a linear threshold
function gives a linear threshold function (`BitString.IsPTF.comp_add_comp`), which is unate and so
has total influence at most `√m` on `m` bits (`BitString.IsPTF.totalInfluence_le_sqrt_card`)
[O'Donnell, Exercises 2.6 and 2.23][ODonnell2014]. The argument of Theorem 5.35
(`BitString.noiseSensitivity_le_div_of_totalInfluence_le`) then gives
`NS_δ[f] ≤ √m / m = 1 / √m` for `0 < δ ≤ 1 / 2` and `m = ⌊1 / δ⌋`
(`BitString.IsPTF.noiseSensitivity_le_inv_sqrt_floor`). Since `3 m ≥ 2 / δ` when `m ≥ 2`, this is
at most `√(3 / 2) √δ` (`BitString.IsPTF.noiseSensitivity_le_sqrt_three_div_two_mul`), the
constant of the second sentence of [O'Donnell, Remark 5.36][ODonnell2014].

So the linear threshold functions form a *uniformly noise-stable* class
(`BitString.IsUniformlyNoiseStable`, `BitString.isUniformlyNoiseStable_isPTF_one`)
[O'Donnell, Definition 5.34][ODonnell2014]. The circuit library's
`Cslib.Circuits.Boolean.WeightedThreshold.IsLTF`, a threshold `θ ≤ ∑ aᵢ xᵢ` with ties
accepted, describes the same class of functions, since perturbing `θ` removes ties on the finite
cube; that equivalence is not proved here, tracked on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131).

## Main definitions

* `Cslib.BitString.IsUniformlyNoiseStable`: a uniformly noise-stable class of Boolean functions.

## Main results

* `Cslib.BitString.IsPTF.noiseSensitivity_le_inv_sqrt_floor`: `NS_δ[f] ≤ 1 / √⌊1 / δ⌋` for a
  linear threshold function and `0 < δ ≤ 1 / 2`.
* `Cslib.BitString.IsPTF.noiseSensitivity_le_sqrt_three_div_two_mul`: **Peres's theorem**,
  `NS_δ[f] ≤ √(3 / 2) √δ` for `0 ≤ δ ≤ 1 / 2`.
* `Cslib.BitString.isUniformlyNoiseStable_isPTF_one`: the linear threshold functions are
  uniformly noise-stable.

## Usage

Open `Cslib.BitString`. A linear threshold function is `IsPTF 1 f` from
`CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold`, on any finite coordinate type;
`Cslib.BitString.isPTF_one_threshold n j` shows that every threshold function `threshold n j` is
one, which covers majority, AND (`threshold n n`), OR (`threshold n 1`) and the constants, and
`Cslib.BitString.isPTF_one_xor b i` covers the literals `±χᵢ`, the remaining examples of
[O'Donnell, Exercise 2.2][ODonnell2014]. For `hf : IsPTF 1 f`,
`hf.noiseSensitivity_le_sqrt_three_div_two_mul hδ hδ'` gives
`noiseSensitivity δ f ≤ √(3 / 2) * √δ` for `0 ≤ δ ≤ 1 / 2`, and
`hf.noiseSensitivity_le_inv_sqrt_floor` gives the sharper `1 / √⌊δ⁻¹⌋₊` for `0 < δ ≤ 1 / 2`.
The rest of Remark 5.36, `NS_δ[f] ≤ √δ + O(δ^(3/2))` for small `δ` and the `√(2/π) √δ` bound
through Theorem 2.33, is not proved; tracked on
[#2131](https://github.com/cslib-community/cslib-frontier/issues/2131).
`IsUniformlyNoiseStable` takes a real-valued `ε` that bounds the noise sensitivities for
`δ ∈ (0, 1 / 2]`, where the book takes `ε : [0, 1 / 2] → [0, 1]`; clamping `ε` to `[0, 1]`
keeps the bound, since noise sensitivities lie in `[0, 1]`, and at `δ = 0` they vanish. The unate
functions behind the proof are in `CslibFrontier.Foundations.BooleanAnalysis.Unate`, and
Theorem 5.35 in `CslibFrontier.Foundations.BooleanAnalysis.NoiseSensitivityInfluence`.

The checked clients in
[CslibFrontierTests/BooleanAnalysisPeres.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisPeres.lean)
apply both bounds to the majority of three bits at `δ = 1 / 4`, check that one `ε` bounds the
noise sensitivity of every `majority n`, and show that the parities of all lengths are not
uniformly noise-stable, since `NS_δ[χ_[n]] = (1 - (1 - 2δ)ⁿ) / 2 → 1 / 2`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Peres's theorem with the floor** [O'Donnell, proof of Peres's theorem][ODonnell2014]: a
linear threshold function has noise sensitivity at most `1 / √m` at `0 < δ ≤ 1 / 2`, for
`m = ⌊1 / δ⌋`. -/
theorem IsPTF.noiseSensitivity_le_inv_sqrt_floor {f : (ι → Bool) → Bool} (hf : IsPTF 1 f)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    noiseSensitivity δ f ≤ 1 / √(⌊δ⁻¹⌋₊ : ℝ) := by
  rw [← Real.sqrt_div_self']
  refine noiseSensitivity_le_div_of_totalInfluence_le hδ hδ' f fun z π => ?_
  simpa only [Fintype.card_fin] using (hf.comp_add_comp z π).totalInfluence_le_sqrt_card

/-- **Peres's theorem** [O'Donnell, Section 5.5 and Remark 5.36][ODonnell2014]: a linear threshold
function `f` has noise sensitivity `NS_δ[f] ≤ √(3 / 2) √δ` for `0 ≤ δ ≤ 1 / 2`. -/
theorem IsPTF.noiseSensitivity_le_sqrt_three_div_two_mul {f : (ι → Bool) → Bool}
    (hf : IsPTF 1 f) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) :
    noiseSensitivity δ f ≤ √(3 / 2) * √δ := by
  rcases hδ.eq_or_lt with rfl | hδ
  · simp
  refine (hf.noiseSensitivity_le_inv_sqrt_floor hδ hδ').trans ?_
  set m := ⌊δ⁻¹⌋₊
  have h2 : (2 : ℝ) ≤ δ⁻¹ := by rw [le_inv_comm₀ two_pos hδ]; linarith
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast Nat.le_floor (n := 2) (by exact_mod_cast h2)
  have hlt : δ⁻¹ < m + 1 := Nat.lt_floor_add_one _
  have h1 : 1 < δ * (m + 1) := by
    have := mul_lt_mul_of_pos_left hlt hδ
    rwa [mul_inv_cancel₀ hδ.ne'] at this
  rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (by norm_num)]
  refine Real.sqrt_le_sqrt ((inv_le_iff_one_le_mul₀' (by positivity)).2 ?_)
  nlinarith

/-- A class `B` of Boolean functions, `B n` on `n` bits, is **uniformly noise-stable** if its
noise sensitivities at `δ` are bounded by a common `ε(δ)` with `ε(δ) → 0` as `δ → 0⁺`
[O'Donnell, Definition 5.34][ODonnell2014]. The book takes `ε : [0, 1/2] → [0, 1]`; here `ε` is
real-valued and bounds the noise sensitivities only for `δ ∈ (0, 1/2]`. Both differences are
immaterial: clamping `ε` to `[0, 1]`, as `max 0 (min ε 1)`, keeps the bound and the limit since
noise sensitivities lie in `[0, 1]`, and at `δ = 0` every noise sensitivity is `0`. -/
@[expose] def IsUniformlyNoiseStable (B : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop) : Prop :=
  ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧
    ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2), ∀ n f, B n f → noiseSensitivity δ f ≤ ε δ

/-- **The linear threshold functions are uniformly noise-stable**, with `ε(δ) = √(3 / 2) √δ`
[O'Donnell, Section 5.5][ODonnell2014]. -/
theorem isUniformlyNoiseStable_isPTF_one : IsUniformlyNoiseStable fun _ => IsPTF 1 := by
  refine ⟨fun δ => √(3 / 2) * √δ, ?_, fun δ hδ n f hf =>
    hf.noiseSensitivity_le_sqrt_three_div_two_mul hδ.1.le hδ.2⟩
  have h : Tendsto (fun δ : ℝ => √(3 / 2) * √δ) (𝓝 0) (𝓝 (√(3 / 2) * √0)) :=
    (continuous_const.mul Real.continuous_sqrt).tendsto 0
  rw [Real.sqrt_zero, mul_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

end Cslib.BitString
