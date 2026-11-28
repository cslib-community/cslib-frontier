/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.SignedDigitStream.Elementary
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Minimum-index dyadic band multiplication of signed-digit streams

This module formalizes the minimum-index dyadic band multiplication algorithm of
[OpenAI2026LogSpace, Section 10.3, Lemma 10.4].

Grouping cross-terms `x_i y_j 2^{-(i+j)}` by `min i j` into a zero band (`min i j = 0`) and
positive dyadic bands `2 ^ k ≤ min i j < 2 ^ (k + 1)` with band-specific truncation margin
`bandMargin k = 16 + bandStart k / 4` achieves three properties simultaneously:

1. **Scaled accuracy `< 2`** (`mulApprox_isScaledApprox`): folding the retained band sums from
   `maxBand t` down to `0` by signed floor shifts approximates `2 ^ t * (streamVal x * streamVal y)`
   within `< 2`.
2. **Diagonal residue locality** (`mulResidue_eq_mulApprox_emod`): modulo `2 ^ q`, `mulApprox x y t`
   depends in band `k` only on diagonals `t - q < i + j ≤ t + bandMargin k`, propagated downward by
   exact signed floor shifts of residues (`ediv_two_pow_emod_eq`).
3. **Clock-drop latency payment** (`three_mul_bandStart_le_four_mul_drop`): for any retained pair
   `(i, j)` in a positive band `k + 1` (`D = 2 ^ k`), both indices satisfy
   `4 * j + 3 * D ≤ 4 * (t + 16)`, so `D ≤ (4 / 3) * (t - j + 16)` pays for the band circuit depth
   out of the clock drop `t - j`.

## Main definitions

* `Cslib.SignedDigitStream.mulBaseMargin`, `Cslib.SignedDigitStream.bandStart`,
  `Cslib.SignedDigitStream.bandEnd`, `Cslib.SignedDigitStream.bandIdx`,
  `Cslib.SignedDigitStream.bandMargin`, `Cslib.SignedDigitStream.maxBand`: dyadic band geometry.
* `Cslib.SignedDigitStream.bandPairs`, `Cslib.SignedDigitStream.bandSum`,
  `Cslib.SignedDigitStream.bandFold`, `Cslib.SignedDigitStream.mulApprox`: exact integer band
  recursion and scaled product approximation.
* `Cslib.SignedDigitStream.bandWindowPairs`, `Cslib.SignedDigitStream.bandWindowSum`,
  `Cslib.SignedDigitStream.bandFoldMod`, `Cslib.SignedDigitStream.mulResidue`: windowed modular
  product residue computation.

## Main results

* `Cslib.SignedDigitStream.mulApprox_isScaledApprox`: `< 2` scaled error bound for `x * y`.
* `Cslib.SignedDigitStream.mulResidue_eq_mulApprox_emod`: equivalence of the windowed residue fold
  with `mulApprox x y t % 2 ^ q`.
* `Cslib.SignedDigitStream.three_mul_bandStart_le_four_mul_drop`,
  `Cslib.SignedDigitStream.index_le_clock_add_baseMargin`: clock-drop latency inequalities.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 10.3, Equations (10.6)--(10.12), and Lemma 10.4 (23 September 2026, revision `7ef5c0cc`,
  not peer reviewed).
-/

public section

namespace Cslib.SignedDigitStream

open Finset

/-- Base margin `h_∘ = 16` for minimum-index dyadic band multiplication. -/
@[expose] def mulBaseMargin : ℕ := 16

/-- Lower inclusive endpoint of dyadic band `k` (`0` at `k = 0`, `2 ^ k` at `k + 1`). -/
@[expose] def bandStart : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ k

/-- Upper exclusive endpoint of dyadic band `k` (`1` at `k = 0`, `2 ^ (k + 1)` at `k + 1`). -/
@[expose] def bandEnd : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 ^ (k + 1)

/-- Width `bandEnd k - bandStart k` of dyadic band `k`. -/
@[expose] def bandWidth (k : ℕ) : ℕ :=
  bandEnd k - bandStart k

/-- Unique band index `k` such that `bandStart k ≤ m < bandEnd k`. -/
@[expose] def bandIdx (m : ℕ) : ℕ :=
  if m = 0 then 0 else Nat.log 2 m + 1

/-- Band margin `h_k = h_∘ + ⌊bandStart k / 4⌋` [OpenAI2026LogSpace, Section 10.3]. -/
@[expose] def bandMargin (k : ℕ) : ℕ :=
  mulBaseMargin + bandStart k / 4

/-- Logarithmic cutoff band count above which all retained bands at clock `t` are empty. -/
@[expose] def maxBand (t : ℕ) : ℕ :=
  Nat.log 2 (t + mulBaseMargin) + 2

/-- Retained index pairs `(i, j)` in band `k` at output clock `t`. -/
@[expose] def bandPairs (t k : ℕ) : Finset (ℕ × ℕ) :=
  (range (t + bandMargin k + 1) ×ˢ range (t + bandMargin k + 1)).filter fun p =>
    bandStart k ≤ min p.1 p.2 ∧ min p.1 p.2 < bandEnd k ∧ p.1 + p.2 ≤ t + bandMargin k

/-- Exact mathematical integer sum `S_k` for band `k` at scale `2 ^ (t + bandMargin k)`
[OpenAI2026LogSpace, (10.6)]. -/
@[expose] def bandSum (x y : ℕ → ℤ) (t k : ℕ) : ℤ :=
  ∑ p ∈ bandPairs t k, x p.1 * y p.2 * (2 : ℤ) ^ (t + bandMargin k - (p.1 + p.2))

/-- Downward signed floor-shift fold across the `rem` highest active bands below `maxBand t`
[OpenAI2026LogSpace, (10.9)]. -/
@[expose] def bandFold (x y : ℕ → ℤ) (t : ℕ) : ℕ → ℤ
  | 0 => 0
  | rem + 1 =>
    let k := maxBand t - (rem + 1)
    let shift := bandMargin (k + 1) - bandMargin k
    bandSum x y t k + bandFold x y t rem / (2 : ℤ) ^ shift

/-- Scaled integer product approximation `⌊2 ^ (-h_0) F_0⌋` [OpenAI2026LogSpace, (10.9)]. -/
@[expose] def mulApprox (x y : ℕ → ℤ) (t : ℕ) : ℤ :=
  bandFold x y t (maxBand t) / (2 : ℤ) ^ mulBaseMargin

/-- Diagonal-windowed band pairs satisfying `t - q < i + j ≤ t + bandMargin k`
[OpenAI2026LogSpace, (10.10)]. -/
@[expose] def bandWindowPairs (t q k : ℕ) : Finset (ℕ × ℕ) :=
  (bandPairs t k).filter fun p => t < p.1 + p.2 + q

/-- Windowed integer sum omitting terms divisible by `2 ^ (q + bandMargin k)`. -/
@[expose] def bandWindowSum (x y : ℕ → ℤ) (t q k : ℕ) : ℤ :=
  ∑ p ∈ bandWindowPairs t q k, x p.1 * y p.2 * (2 : ℤ) ^ (t + bandMargin k - (p.1 + p.2))

/-- Modular downward band fold maintaining only the canonical `(q + bandMargin k)`-bit residue. -/
@[expose] def bandFoldMod (x y : ℕ → ℤ) (t q : ℕ) : ℕ → ℤ
  | 0 => 0
  | rem + 1 =>
    let k := maxBand t - (rem + 1)
    let shift := bandMargin (k + 1) - bandMargin k
    (bandWindowSum x y t q k + bandFoldMod x y t q rem / (2 : ℤ) ^ shift) %
      (2 : ℤ) ^ (q + bandMargin k)

/-- Mod-`2^q` residue of `mulApprox x y t` computed purely from windowed band residues. -/
@[expose] def mulResidue (x y : ℕ → ℤ) (t q : ℕ) : ℤ :=
  bandFoldMod x y t q (maxBand t) / (2 : ℤ) ^ mulBaseMargin

section BandGeometry

@[simp]
theorem bandStart_zero : bandStart 0 = 0 := rfl

@[simp]
theorem bandEnd_zero : bandEnd 0 = 1 := rfl

@[simp]
theorem bandMargin_zero : bandMargin 0 = mulBaseMargin := by
  simp [bandMargin]

theorem bandStart_succ_eq_bandEnd (k : ℕ) : bandStart (k + 1) = bandEnd k := by
  cases k <;> rfl

theorem bandStart_lt_bandEnd (k : ℕ) : bandStart k < bandEnd k := by
  rcases k with _ | k
  · decide
  · exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k)

theorem bandStart_mono : Monotone bandStart :=
  monotone_nat_of_le_succ fun k => bandStart_succ_eq_bandEnd k ▸ (bandStart_lt_bandEnd k).le

theorem bandMargin_mono : Monotone bandMargin :=
  fun _ _ hab => Nat.add_le_add_left (Nat.div_le_div_right (bandStart_mono hab)) _

theorem bandWidth_le_two_pow (k : ℕ) : bandWidth k ≤ 2 ^ k := by
  rcases k with _ | k
  · decide
  · rw [bandWidth, bandEnd, bandStart, pow_succ]
    omega

theorem mem_band_bandIdx (m : ℕ) : bandStart (bandIdx m) ≤ m ∧ m < bandEnd (bandIdx m) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [bandIdx]
  · simp only [bandIdx, hm, ite_false, bandStart, bandEnd]
    exact ⟨Nat.pow_log_le_self 2 hm, Nat.lt_pow_succ_log_self (by decide) m⟩

theorem bandIdx_eq_iff {m k : ℕ} : bandIdx m = k ↔ bandStart k ≤ m ∧ m < bandEnd k := by
  refine ⟨fun h => h ▸ mem_band_bandIdx m, fun ⟨hlo, hhi⟩ => ?_⟩
  have hmem := mem_band_bandIdx m
  rcases lt_trichotomy (bandIdx m) k with hlt | heq | hgt
  · have := bandStart_succ_eq_bandEnd (bandIdx m) ▸ bandStart_mono (Nat.succ_le_of_lt hlt)
    omega
  · exact heq
  · have := bandStart_succ_eq_bandEnd k ▸ bandStart_mono (Nat.succ_le_of_lt hgt)
    omega

theorem ten_add_two_mul_le_bandMargin (k : ℕ) : 10 + 2 * k ≤ bandMargin k := by
  rcases k with _ | _ | _ | m <;> try decide
  dsimp only [bandMargin, mulBaseMargin, bandStart]
  have hm : 2 * m ≤ 2 ^ m := by
    induction m with
    | zero => decide
    | succ n ih =>
      rcases n with _ | n
      · decide
      · have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        calc 2 * (n + 1 + 1) = 2 * (n + 1) + 2 := by ring
          _ ≤ 2 ^ (n + 1) + 2 * 2 ^ n := Nat.add_le_add ih (by omega)
          _ = 2 ^ (n + 1 + 1) := by ring
  rw [pow_add]
  omega

theorem two_mul_bandStart_gt_of_maxBand_le {t k : ℕ} (hk : maxBand t ≤ k) :
    t + bandMargin k < 2 * bandStart k := by
  have hlt : t + mulBaseMargin < bandStart k :=
    (Nat.lt_pow_succ_log_self (by decide) _).trans_le (bandStart_mono hk)
  have hD2 : 2 ≤ bandStart k := bandStart_mono (show 2 ≤ k by rw [maxBand] at hk; omega)
  unfold bandMargin
  omega

/-- **Clock-drop latency inequality** [OpenAI2026LogSpace, (10.12)]: for any retained pair `(i, j)`
in a positive band `k + 1` (`D = 2 ^ k`), `4 * j + 3 * D ≤ 4 * (t + mulBaseMargin)` (and
symmetrically for `i`). -/
theorem three_mul_bandStart_le_four_mul_drop {t k : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ bandPairs t (k + 1)) :
    4 * p.1 + 3 * bandStart (k + 1) ≤ 4 * (t + mulBaseMargin) ∧
      4 * p.2 + 3 * bandStart (k + 1) ≤ 4 * (t + mulBaseMargin) := by
  obtain ⟨_, hlo, _, hsum⟩ := mem_filter.mp hp
  rw [le_min_iff] at hlo
  unfold bandMargin at hsum
  omega

/-- Every retained operand index `i` or `j` across all bands `k` obeys
`i ≤ t + mulBaseMargin` and `j ≤ t + mulBaseMargin`. -/
theorem index_le_clock_add_baseMargin {t k : ℕ} {p : ℕ × ℕ} (hp : p ∈ bandPairs t k) :
    p.1 ≤ t + mulBaseMargin ∧ p.2 ≤ t + mulBaseMargin := by
  rcases k with _ | k
  · have := bandMargin_zero ▸ (mem_filter.mp hp).2.2.2
    omega
  · have := three_mul_bandStart_le_four_mul_drop hp
    omega

end BandGeometry

section ModularResidues

theorem bandSum_emod_eq_bandWindowSum_emod (x y : ℕ → ℤ) (t q k : ℕ) :
    bandSum x y t k % (2 : ℤ) ^ (q + bandMargin k) =
      bandWindowSum x y t q k % (2 : ℤ) ^ (q + bandMargin k) := by
  unfold bandSum bandWindowSum bandWindowPairs
  rw [← sum_filter_add_sum_filter_not (bandPairs t k) (fun p => t < p.1 + p.2 + q)]
  obtain ⟨c, hc⟩ := dvd_sum (s := (bandPairs t k).filter fun p => ¬ t < p.1 + p.2 + q)
    (f := fun p => x p.1 * y p.2 * (2 : ℤ) ^ (t + bandMargin k - (p.1 + p.2))) fun p hp =>
    dvd_mul_of_dvd_right
      (pow_dvd_pow 2 (by have := (mem_filter.mp hp).2; omega : q + bandMargin k ≤ _)) _
  rw [hc, Int.add_mul_emod_self_left]

theorem bandFoldMod_eq_bandFold_emod (x y : ℕ → ℤ) (t q : ℕ) :
    ∀ rem ≤ maxBand t,
      bandFoldMod x y t q rem =
        bandFold x y t rem % (2 : ℤ) ^ (q + bandMargin (maxBand t - rem))
  | 0, _ => by simp [bandFoldMod, bandFold]
  | rem + 1, hrem => by
    simp only [bandFoldMod, bandFold]
    set k := maxBand t - (rem + 1)
    have hk1 : maxBand t - rem = k + 1 := by omega
    have ih := bandFoldMod_eq_bandFold_emod x y t q rem (by omega)
    rw [hk1] at ih
    set shift := bandMargin (k + 1) - bandMargin k
    have hmargin_add : (q + bandMargin k) + shift = q + bandMargin (k + 1) := by
      have hmono : bandMargin k ≤ bandMargin (k + 1) := bandMargin_mono (Nat.le_succ k)
      omega
    rw [ih, ← hmargin_add, ← ediv_two_pow_emod_eq, Int.add_emod,
      ← bandSum_emod_eq_bandWindowSum_emod, Int.emod_emod, ← Int.add_emod]

/-- **Windowed modular product residue theorem** [OpenAI2026LogSpace, Lemma 10.4]:
`mulResidue x y t q` computes the exact mod-`2^q` Euclidean residue of `mulApprox x y t` while
retaining only diagonals `t - q < i + j ≤ t + bandMargin k` in each band. -/
theorem mulResidue_eq_mulApprox_emod (x y : ℕ → ℤ) (t q : ℕ) :
    mulResidue x y t q = mulApprox x y t % (2 : ℤ) ^ q := by
  rw [mulResidue, mulApprox, bandFoldMod_eq_bandFold_emod x y t q (maxBand t) le_rfl,
    Nat.sub_self, bandMargin_zero, ← ediv_two_pow_emod_eq]

end ModularResidues

section ScaledAccuracy

private def retainedUnion (t K : ℕ) : Finset (ℕ × ℕ) :=
  (range K).biUnion (bandPairs t)

private theorem bandPairs_pairwiseDisjoint (t : ℕ) :
    (↑(range (maxBand t)) : Set ℕ).PairwiseDisjoint (bandPairs t) := by
  intro k₁ _ k₂ _ hne
  refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => hne ?_
  obtain ⟨_, hlo₁, hhi₁, _⟩ := mem_filter.mp hp₁
  obtain ⟨_, hlo₂, hhi₂, _⟩ := mem_filter.mp hp₂
  exact (bandIdx_eq_iff.mpr ⟨hlo₁, hhi₁⟩).symm.trans (bandIdx_eq_iff.mpr ⟨hlo₂, hhi₂⟩)

private theorem sum_bandPairs_real (x y : ℕ → ℤ) (t k : ℕ) :
    (bandSum x y t k : ℝ) / (2 : ℝ) ^ bandMargin k =
      ∑ p ∈ bandPairs t k,
        (2 : ℝ) ^ t * ((x p.1 : ℝ) * (y p.2 : ℝ) / (2 : ℝ) ^ (p.1 + p.2)) := by
  unfold bandSum
  rw [Int.cast_sum, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [← div_eq_mul_inv]
  obtain ⟨_, _, _, hle⟩ := mem_filter.mp hp
  push_cast
  have hpow : (2 : ℝ) ^ (t + bandMargin k - (p.1 + p.2)) * (2 : ℝ) ^ (p.1 + p.2) =
      (2 : ℝ) ^ t * (2 : ℝ) ^ bandMargin k := by
    rw [← pow_add, Nat.sub_add_cancel hle, pow_add]
  field_simp
  rw [mul_assoc ((x p.1 : ℝ) * (y p.2 : ℝ)), hpow]
  ring

private theorem abs_bandFold_sub_sum_le (x y : ℕ → ℤ) (t : ℕ) :
    ∀ rem ≤ maxBand t,
      |(bandFold x y t rem : ℝ) / (2 : ℝ) ^ bandMargin (maxBand t - rem) -
          ∑ k ∈ Ico (maxBand t - rem) (maxBand t),
            (bandSum x y t k : ℝ) / (2 : ℝ) ^ bandMargin k| ≤
        ∑ k ∈ Ico (maxBand t - rem) (maxBand t), 1 / (2 : ℝ) ^ bandMargin k
  | 0, _ => by simp [bandFold]
  | rem + 1, hrem => by
    simp only [bandFold]
    set k := maxBand t - (rem + 1)
    have hk_lt : k < maxBand t := by omega
    have hk_succ : maxBand t - rem = k + 1 := by omega
    have ih := abs_bandFold_sub_sum_le x y t rem (by omega)
    rw [hk_succ] at ih
    set s := bandMargin (k + 1) - bandMargin k
    have hs_add : bandMargin k + s = bandMargin (k + 1) :=
      Nat.add_sub_of_le (bandMargin_mono (Nat.le_succ k))
    have hfl := abs_ediv_sub_div_lt_one (bandFold x y t rem)
      (by positivity : (0 : ℤ) < (2 : ℤ) ^ s)
    push_cast at hfl
    rw [sum_eq_sum_Ico_succ_bot hk_lt, sum_eq_sum_Ico_succ_bot hk_lt]
    set Q : ℝ := ((bandFold x y t rem / (2 : ℤ) ^ s : ℤ) : ℝ)
    set R : ℝ := (bandFold x y t rem : ℝ) / (2 : ℝ) ^ s
    set T : ℝ := ∑ j ∈ Ico (k + 1) (maxBand t), (bandSum x y t j : ℝ) / (2 : ℝ) ^ bandMargin j
    have hdiff : ((bandSum x y t k : ℝ) + Q) / (2 : ℝ) ^ bandMargin k -
        ((bandSum x y t k : ℝ) / (2 : ℝ) ^ bandMargin k + T) =
        (Q - R) / (2 : ℝ) ^ bandMargin k + (R / (2 : ℝ) ^ bandMargin k - T) := by ring
    have hR_div : R / (2 : ℝ) ^ bandMargin k =
        (bandFold x y t rem : ℝ) / (2 : ℝ) ^ bandMargin (k + 1) := by
      dsimp [R]
      rw [div_div, ← pow_add, add_comm s, hs_add]
    have hQ_err : |(Q - R) / (2 : ℝ) ^ bandMargin k| ≤ 1 / (2 : ℝ) ^ bandMargin k := by
      rw [abs_div, abs_of_pos (pow_pos (two_pos : (0 : ℝ) < 2) (bandMargin k))]
      exact div_le_div_of_nonneg_right hfl.le (by positivity)
    push_cast
    rw [hdiff]
    calc |(Q - R) / (2 : ℝ) ^ bandMargin k + (R / (2 : ℝ) ^ bandMargin k - T)|
        ≤ |(Q - R) / (2 : ℝ) ^ bandMargin k| + |R / (2 : ℝ) ^ bandMargin k - T| :=
          abs_add_le _ _
      _ ≤ 1 / (2 : ℝ) ^ bandMargin k +
            ∑ j ∈ Ico (k + 1) (maxBand t), 1 / (2 : ℝ) ^ bandMargin j := by
          rw [hR_div]
          exact add_le_add hQ_err ih

private theorem sum_floor_err_le (K : ℕ) :
    ∑ k ∈ range K, 1 / (2 : ℝ) ^ bandMargin k ≤ 1 / 768 := by
  have hterm : ∀ k ∈ range K, 1 / (2 : ℝ) ^ bandMargin k ≤ (1 / 1024) * (1 / 4 : ℝ) ^ k := by
    intro k _
    calc 1 / (2 : ℝ) ^ bandMargin k ≤ 1 / (2 : ℝ) ^ (10 + 2 * k) :=
          one_div_le_one_div_of_le (by positivity)
            (pow_le_pow_right₀ (by norm_num) (ten_add_two_mul_le_bandMargin k))
      _ = _ := by rw [pow_add, pow_mul, one_div_pow, one_div_mul_one_div]; norm_num
  calc ∑ k ∈ range K, 1 / (2 : ℝ) ^ bandMargin k
      ≤ ∑ k ∈ range K, (1 / 1024) * (1 / 4 : ℝ) ^ k := sum_le_sum hterm
    _ = (1 / 1024) * ∑ k ∈ range K, (1 / 4 : ℝ) ^ k := (mul_sum _ _ _).symm
    _ ≤ (1 / 1024) * (1 / (1 - (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Finset.range_eq_Ico, pow_zero] using
            geom_sum_Ico_le_of_lt_one (m := 0) (n := K) (by norm_num) (by norm_num))
          (by norm_num)
    _ = 1 / 768 := by norm_num

private theorem sum_ray_tail_le (N r M : ℕ) :
    ∑ j ∈ (range (N + 1)).filter (fun j => M < r + j), (1 / (2 : ℝ) ^ (r + j)) ≤
      1 / (2 : ℝ) ^ M := by
  set F := (range (N + 1)).filter fun j => M < r + j
  set g : ℕ → ℕ := fun j => r + j - (M + 1)
  have hinj : Set.InjOn g ↑F := fun j₁ hj₁ j₂ hj₂ heq => by
    have h₁ := (mem_filter.mp hj₁).2
    have h₂ := (mem_filter.mp hj₂).2
    simp only [g] at heq
    omega
  have hsub : F.image g ⊆ range (2 * N + r + 1) := fun m hm => by
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
    have hjN := mem_range.mp (mem_filter.mp hj).1
    simp only [mem_range, g]
    omega
  have hrw : ∑ j ∈ F, (1 / (2 : ℝ) ^ (r + j)) =
      ∑ m ∈ F.image g, (1 / (2 : ℝ) ^ (M + 1)) * (1 / 2 : ℝ) ^ m := by
    rw [sum_image hinj]
    refine sum_congr rfl fun j hj => ?_
    have hM : M + 1 ≤ r + j := (mem_filter.mp hj).2
    have hadd : r + j = (M + 1) + g j := by
      dsimp [g]
      omega
    rw [hadd, pow_add, one_div_pow]
    ring
  rw [hrw, ← mul_sum]
  calc (1 / (2 : ℝ) ^ (M + 1)) * ∑ m ∈ F.image g, (1 / 2 : ℝ) ^ m
      ≤ (1 / (2 : ℝ) ^ (M + 1)) * 2 := by
        gcongr
        exact (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
          (sum_geometric_two_le _)
    _ = 1 / (2 : ℝ) ^ M := by rw [pow_succ]; field_simp

private theorem sum_omitted_le {x y : ℕ → ℤ} (hx : IsSignedStream x) (hy : IsSignedStream y)
    (t N : ℕ) (hN : t + bandMargin (maxBand t) ≤ N) :
    |∑ p ∈ range (N + 1) ×ˢ range (N + 1),
        (2 : ℝ) ^ t * ((x p.1 : ℝ) * (y p.2 : ℝ) / (2 : ℝ) ^ (p.1 + p.2)) -
      ∑ p ∈ retainedUnion t (maxBand t),
        (2 : ℝ) ^ t * ((x p.1 : ℝ) * (y p.2 : ℝ) / (2 : ℝ) ^ (p.1 + p.2))| ≤ 9 / 64 := by
  set K := maxBand t
  set Sq := range (N + 1) ×ˢ range (N + 1)
  set term : ℕ × ℕ → ℝ := fun p =>
    (2 : ℝ) ^ t * ((x p.1 : ℝ) * (y p.2 : ℝ) / (2 : ℝ) ^ (p.1 + p.2))
  have hret_sub : retainedUnion t K ⊆ Sq := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := mem_biUnion.mp hp
    have hm_le : bandMargin k ≤ bandMargin K := bandMargin_mono (mem_range.mp hk).le
    obtain ⟨_, _, _, hsum⟩ := mem_filter.mp hpk
    rw [mem_product, mem_range, mem_range]
    omega
  rw [← sum_sdiff_eq_sub hret_sub]
  have hterm_bound : ∀ p : ℕ × ℕ, |term p| ≤ (2 : ℝ) ^ t * 36 * (1 / (2 : ℝ) ^ (p.1 + p.2)) := by
    intro p
    have hx1 := hx.abs_cast_le p.1
    have hy1 := hy.abs_cast_le p.2
    calc |term p| = (2 : ℝ) ^ t * (|(x p.1 : ℝ)| * |(y p.2 : ℝ)| / (2 : ℝ) ^ (p.1 + p.2)) := by
          simp [term, abs_mul, abs_div]
      _ ≤ (2 : ℝ) ^ t * (6 * 6 / (2 : ℝ) ^ (p.1 + p.2)) := by gcongr
      _ = (2 : ℝ) ^ t * 36 * (1 / (2 : ℝ) ^ (p.1 + p.2)) := by ring
  have homit_gt : ∀ p ∈ Sq \ retainedUnion t K,
      t + bandMargin (bandIdx (min p.1 p.2)) < p.1 + p.2 := by
    intro p hp
    obtain ⟨hpSq, hpNot⟩ := mem_sdiff.mp hp
    have hband := mem_band_bandIdx (min p.1 p.2)
    set r := min p.1 p.2 with hr
    set k := bandIdx r
    by_cases hk : k < K
    · refine lt_of_not_ge fun hle => hpNot (mem_biUnion.mpr ⟨k, mem_range.mpr hk, ?_⟩)
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr ?_⟩,
        hband.1, hband.2, hle⟩ <;> omega
    · have hgt := two_mul_bandStart_gt_of_maxBand_le (not_lt.mp hk)
      omega
  set w : ℕ × ℕ → ℝ := fun p => (2 : ℝ) ^ t * 36 * (1 / (2 : ℝ) ^ (p.1 + p.2))
  have habs_sum : |∑ p ∈ Sq \ retainedUnion t K, term p| ≤ ∑ p ∈ Sq \ retainedUnion t K, w p :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => hterm_bound p)
  have hpart := sum_filter_add_sum_filter_not (Sq \ retainedUnion t K) (fun p => p.1 ≤ p.2) w
  -- each row `r` of omitted pairs contributes at most `36 / 2 ^ bandMargin (bandIdx r)`
  have hrow (r : ℕ) :
      ∑ j ∈ (range (N + 1)).filter (fun j => t + bandMargin (bandIdx r) < r + j), w (r, j) ≤
        36 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
    dsimp [w]
    rw [← mul_sum]
    calc (2 : ℝ) ^ t * 36 *
          ∑ j ∈ (range (N + 1)).filter (fun j => t + bandMargin (bandIdx r) < r + j),
            (1 / (2 : ℝ) ^ (r + j))
        ≤ (2 : ℝ) ^ t * 36 * (1 / (2 : ℝ) ^ (t + bandMargin (bandIdx r))) :=
          mul_le_mul_of_nonneg_left (sum_ray_tail_le N r _) (by positivity)
      _ = 36 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
          rw [pow_add]
          field_simp
  -- pairs whose first index governs the omission contribute at most one row bound per row
  have hrows : ∀ T ⊆ Sq.filter (fun p => t + bandMargin (bandIdx p.1) < p.1 + p.2),
      ∑ p ∈ T, w p ≤ ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
    intro T hT
    calc ∑ p ∈ T, w p
        ≤ ∑ p ∈ Sq.filter (fun p => t + bandMargin (bandIdx p.1) < p.1 + p.2), w p :=
          sum_le_sum_of_subset_of_nonneg hT fun _ _ _ => by dsimp [w]; positivity
      _ = ∑ r ∈ range (N + 1),
            ∑ j ∈ (range (N + 1)).filter (fun j => t + bandMargin (bandIdx r) < r + j),
              w (r, j) := by
          simp only [Sq, sum_filter, sum_product]
      _ ≤ ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) :=
          sum_le_sum fun r _ => hrow r
  have hO1 : ∑ p ∈ (Sq \ retainedUnion t K).filter (fun p => p.1 ≤ p.2), w p ≤
      ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
    refine hrows _ fun p hp => ?_
    obtain ⟨hpDiff, hpLe⟩ := mem_filter.mp hp
    have hgt := homit_gt p hpDiff
    rw [min_eq_left hpLe] at hgt
    exact mem_filter.mpr ⟨(mem_sdiff.mp hpDiff).1, hgt⟩
  -- the remaining pairs are the first kind with their two indices swapped
  have hO2 : ∑ p ∈ (Sq \ retainedUnion t K).filter (fun p => ¬ p.1 ≤ p.2), w p ≤
      ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
    have hswap := hrows (((Sq \ retainedUnion t K).filter (fun p => ¬ p.1 ≤ p.2)).image Prod.swap)
      fun p hp => by
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
        obtain ⟨hqDiff, hqGt⟩ := mem_filter.mp hq
        have hgt := homit_gt q hqDiff
        rw [min_eq_right (not_le.mp hqGt).le] at hgt
        have hqSq := (mem_sdiff.mp hqDiff).1
        simp only [Sq, mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hqSq ⊢
        exact ⟨hqSq.symm, by rwa [add_comm q.2 q.1]⟩
    rw [sum_image fun p _ q _ h => Prod.swap_injective h] at hswap
    refine le_of_eq_of_le (sum_congr rfl fun p _ => ?_) hswap
    simp only [w, Prod.fst_swap, Prod.snd_swap, add_comm]
  have hsum_r : ∑ r ∈ range (N + 1), 72 / (2 : ℝ) ^ bandMargin (bandIdx r) ≤ 9 / 64 := by
    set B := bandIdx N + 1
    have hcover : range (N + 1) ⊆ (range B).biUnion fun k => Ico (bandStart k) (bandEnd k) := by
      intro r hr
      have hr_le : r ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hr)
      refine mem_biUnion.mpr ⟨bandIdx r, mem_range.mpr ?_, mem_Ico.mpr (mem_band_bandIdx r)⟩
      by_contra hge
      have := bandStart_succ_eq_bandEnd (bandIdx N) ▸ bandStart_mono (not_lt.mp hge)
      have := mem_band_bandIdx N
      have := mem_band_bandIdx r
      omega
    have hdisj : (↑(range B) : Set ℕ).PairwiseDisjoint fun k => Ico (bandStart k) (bandEnd k) :=
      fun _ _ _ _ hne => Finset.disjoint_left.mpr fun _ hr₁ hr₂ => hne <|
        (bandIdx_eq_iff.mpr (mem_Ico.mp hr₁)).symm.trans (bandIdx_eq_iff.mpr (mem_Ico.mp hr₂))
    calc ∑ r ∈ range (N + 1), 72 / (2 : ℝ) ^ bandMargin (bandIdx r)
        ≤ ∑ r ∈ (range B).biUnion (fun k => Ico (bandStart k) (bandEnd k)),
            72 / (2 : ℝ) ^ bandMargin (bandIdx r) :=
          sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => by positivity
      _ = ∑ k ∈ range B, ∑ r ∈ Ico (bandStart k) (bandEnd k),
            72 / (2 : ℝ) ^ bandMargin (bandIdx r) := sum_biUnion hdisj
      _ = ∑ k ∈ range B, (bandWidth k : ℝ) * (72 / (2 : ℝ) ^ bandMargin k) := by
          refine sum_congr rfl fun k _ => ?_
          rw [sum_congr rfl fun r hr => by rw [bandIdx_eq_iff.mpr (mem_Ico.mp hr)], sum_const,
            Nat.card_Ico, nsmul_eq_mul]
          rfl
      _ ≤ ∑ k ∈ range B, (72 / 1024) * (1 / 2 : ℝ) ^ k := by
          refine sum_le_sum fun k _ => ?_
          have hw_le : (bandWidth k : ℝ) ≤ (2 : ℝ) ^ k := mod_cast bandWidth_le_two_pow k
          have hm_le : (2 : ℝ) ^ (10 + 2 * k) ≤ (2 : ℝ) ^ bandMargin k :=
            pow_le_pow_right₀ (by norm_num) (ten_add_two_mul_le_bandMargin k)
          calc (bandWidth k : ℝ) * (72 / (2 : ℝ) ^ bandMargin k)
              ≤ (2 : ℝ) ^ k * (72 / (2 : ℝ) ^ (10 + 2 * k)) := by gcongr
            _ = (72 / 1024) * (1 / 2 : ℝ) ^ k := by
                rw [pow_add, two_mul, pow_add, one_div_pow]
                field_simp
                ring
      _ = (72 / 1024) * ∑ k ∈ range B, (1 / 2 : ℝ) ^ k := (mul_sum _ _ _).symm
      _ ≤ (72 / 1024) * 2 := by gcongr; exact sum_geometric_two_le B
      _ = 9 / 64 := by norm_num
  have htwo : ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) +
      ∑ r ∈ range (N + 1), 36 / (2 : ℝ) ^ bandMargin (bandIdx r) =
      ∑ r ∈ range (N + 1), 72 / (2 : ℝ) ^ bandMargin (bandIdx r) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun r _ => by ring
  linarith

/-- **Lemma 10.4 (scaled product approximation)** [OpenAI2026LogSpace, Lemma 10.4]: for any two
signed-digit streams `x, y`, `mulApprox x y` approximates `streamVal x * streamVal y` within
scaled error `< 2`. -/
theorem mulApprox_isScaledApprox {x y : ℕ → ℤ}
    (hx : IsSignedStream x) (hy : IsSignedStream y) :
    IsScaledApprox (streamVal x * streamVal y) (mulApprox x y) := by
  intro t
  unfold mulApprox
  set K := maxBand t
  set N := t + bandMargin K + 20
  set term : ℕ × ℕ → ℝ := fun p =>
    (2 : ℝ) ^ t * ((x p.1 : ℝ) * (y p.2 : ℝ) / (2 : ℝ) ^ (p.1 + p.2))
  have hfl := abs_ediv_sub_div_lt_one (bandFold x y t K)
    (by positivity : (0 : ℤ) < (2 : ℤ) ^ mulBaseMargin)
  push_cast at hfl
  have hfold_err : |(bandFold x y t K : ℝ) / (2 : ℝ) ^ mulBaseMargin -
      ∑ p ∈ retainedUnion t K, term p| ≤ 1 / 768 := by
    have h1 := abs_bandFold_sub_sum_le x y t K le_rfl
    rw [Nat.sub_self, bandMargin_zero, ← Finset.range_eq_Ico] at h1
    rw [retainedUnion, sum_biUnion (bandPairs_pairwiseDisjoint t)]
    simpa only [sum_bandPairs_real] using h1.trans (sum_floor_err_le K)
  have hSq_eq : ∑ p ∈ range (N + 1) ×ˢ range (N + 1), term p =
      (2 : ℝ) ^ t * (streamPrefix x N * streamPrefix y N) := by
    simp only [streamPrefix, sum_mul, mul_sum, sum_product, term, pow_add, div_mul_div_comm]
    exact sum_comm
  have homit := sum_omitted_le hx hy t N (by dsimp [N, K]; omega)
  rw [hSq_eq] at homit
  have hpre_err : |(2 : ℝ) ^ t * (streamPrefix x N * streamPrefix y N) -
      (2 : ℝ) ^ t * (streamVal x * streamVal y)| ≤ 144 / (2 : ℝ) ^ 20 := by
    have hx_pre : |streamPrefix x N| ≤ 12 :=
      (abs_streamPrefix_le hx N).trans (sub_le_self 12 (by positivity))
    have hy_val : |streamVal y| ≤ 12 := abs_streamVal_le_twelve hy
    have hx_tail := abs_streamVal_sub_streamPrefix_le hx N
    have hy_tail := abs_streamVal_sub_streamPrefix_le hy N
    rw [abs_sub_comm] at hx_tail hy_tail
    have hdecomp : streamPrefix x N * streamPrefix y N - streamVal x * streamVal y =
        streamPrefix x N * (streamPrefix y N - streamVal y) +
          (streamPrefix x N - streamVal x) * streamVal y := by ring
    have hprod_err : |streamPrefix x N * streamPrefix y N - streamVal x * streamVal y| ≤
        144 / (2 : ℝ) ^ N := by
      rw [hdecomp]
      calc _ ≤ |streamPrefix x N| * |streamPrefix y N - streamVal y| +
              |streamPrefix x N - streamVal x| * |streamVal y| :=
            (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])
        _ ≤ 12 * (6 / (2 : ℝ) ^ N) + (6 / (2 : ℝ) ^ N) * 12 := by gcongr
        _ = 144 / (2 : ℝ) ^ N := by ring
    rw [← mul_sub, abs_mul, abs_of_pos (pow_pos zero_lt_two t)]
    have hpow_ge : (2 : ℝ) ^ t * (2 : ℝ) ^ 20 ≤ (2 : ℝ) ^ N :=
      pow_add (2 : ℝ) t 20 ▸ pow_le_pow_right₀ (by norm_num) (by omega)
    calc (2 : ℝ) ^ t * |streamPrefix x N * streamPrefix y N - streamVal x * streamVal y|
        ≤ (2 : ℝ) ^ t * (144 / (2 : ℝ) ^ N) :=
          mul_le_mul_of_nonneg_left hprod_err (by positivity)
      _ ≤ (2 : ℝ) ^ t * (144 / ((2 : ℝ) ^ t * (2 : ℝ) ^ 20)) := by gcongr
      _ = 144 / (2 : ℝ) ^ 20 := by field_simp
  rw [abs_sub_comm] at homit
  have hnum : (1 : ℝ) + 1 / 768 + 9 / 64 + 144 / (2 : ℝ) ^ 20 < 2 := by norm_num
  linarith [abs_sub_le ((bandFold x y t K / (2 : ℤ) ^ mulBaseMargin : ℤ) : ℝ)
      ((bandFold x y t K : ℝ) / (2 : ℝ) ^ mulBaseMargin) (∑ p ∈ retainedUnion t K, term p),
    abs_sub_le ((bandFold x y t K / (2 : ℤ) ^ mulBaseMargin : ℤ) : ℝ)
      (∑ p ∈ retainedUnion t K, term p) ((2 : ℝ) ^ t * (streamPrefix x N * streamPrefix y N)),
    abs_sub_le ((bandFold x y t K / (2 : ℤ) ^ mulBaseMargin : ℤ) : ℝ)
      ((2 : ℝ) ^ t * (streamPrefix x N * streamPrefix y N))
      ((2 : ℝ) ^ t * (streamVal x * streamVal y))]

end ScaledAccuracy

end Cslib.SignedDigitStream
