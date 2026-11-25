/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
public import CslibFrontier.Foundations.Data.Code.ListDecoding
public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Defs.Filter
import CslibFrontier.Foundations.Data.Code.Johnson
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The real Johnson radius and list-decodability bounds

Building on the integer second-moment Johnson inequalities of
`CslibFrontier.Foundations.Data.Code.Johnson` (`Cslib.Code.card_filter_hammingDist_le_mul_le` and
`Cslib.Code.card_filter_hammingDist_le_mul_le_of_mul_le`) and the combinatorial list-decodability
predicate `Cslib.Code.IsListDecodable` of `CslibFrontier.Foundations.Data.Code.ListDecoding`, this
module formalizes the real-valued Johnson radii and list-size bounds:

* `Cslib.Code.johnsonRadius q δ`: the `q`-ary Johnson radius
  `J_q(δ) = (1 - 1 / q) * (1 - √(1 - q * δ / (q - 1)))`, which decreases in `q`
  (`Cslib.Code.johnsonRadius_antitone`) and tends to
  `Cslib.Code.johnsonRadiusLimit δ = 1 - √(1 - δ)` as `q → ∞`
  (`Cslib.Code.tendsto_johnsonRadius_atTop`).
* `Cslib.Code.mul_le_sub_one_mul_and_lt_of_lt_johnsonRadius`: bridge from the real inequality
  `e / n < J_q(d / n)` to the natural-number hypotheses used by the finite `q`-ary Johnson and
  Elias–Bassalygo bounds.
* `Cslib.Code.isListDecodable_of_le_johnsonRadius`: over any alphabet of `q ≥ 2` letters, a code
  with minimum distance at least `d` and relative distance `δ = d / n` is `(ρ, L)`-list-decodable
  for every `ρ ≤ J_q(δ) - ε` with constant list size
  `L = ⌊(q - 1) * δ / (q * ε ^ 2)⌋₊ ≤ ⌊1 / ε ^ 2⌋₊ ≤ ⌊n / ε ^ 2⌋₊`.
* `Cslib.Code.isListDecodable_of_le_johnsonRadiusLimit` and
  `Cslib.Code.isListDecodable_reedSolomon`: the alphabet-free `1 - √(1 - δ) - ε` Johnson bound
  (`⌊δ / ε ^ 2⌋₊`) and the combinatorial list-decodability of Reed–Solomon codes
  `Cslib.Code.reedSolomon` over arbitrary (possibly infinite) fields. For the explicit algorithmic
  Guruswami–Sudan list decoder, see `CslibFrontier.Foundations.Data.Code.GuruswamiSudan`.

For the finite and asymptotic Elias–Bassalygo rate upper bounds derived from `johnsonRadius`, see
`CslibFrontier.Foundations.Data.Code.EliasBassalygo`.

## Main definitions

* `Cslib.Code.johnsonRadius`: the `q`-ary Johnson radius `J_q(δ)`.
* `Cslib.Code.johnsonRadiusLimit`: the alphabet-free / `q → ∞` limit `1 - √(1 - δ)`.

## Main results

* `Cslib.Code.johnsonRadius_antitone`, `Cslib.Code.tendsto_johnsonRadius_atTop`,
  `Cslib.Code.johnsonRadiusLimit_le_johnsonRadius`: monotonicity and `q → ∞` convergence of
  `J_q(δ)`.
* `Cslib.Code.mul_le_sub_one_mul_and_lt_of_lt_johnsonRadius`: bridge from `e / n < J_q(d / n)` to
  the integer Johnson-radius hypotheses.
* `Cslib.Code.isListDecodable_of_le_johnsonRadius`,
  `Cslib.Code.isListDecodable_of_le_johnsonRadiusLimit`,
  `Cslib.Code.isListDecodable_reedSolomon`: `q`-ary, alphabet-free, and combinatorial Reed–Solomon
  list-decodability up to the Johnson radius.

## References

* [S. M. Johnson, *A new upper bound for error-correcting codes*][Johnson1962] (locator unverified)
* [V. Guruswami, M. Sudan, *Improved Decoding of Reed--Solomon and Algebraic-Geometry Codes*]
  [GuruswamiSudan1999] (locator unverified)
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
  (locator unverified)
-/

public section

namespace Cslib.Code

open Finset Filter
open scoped Topology

/-! ### The Johnson radii `J_q(δ)` and `1 - √(1 - δ)` -/

section Radius

/-- The *q-ary Johnson radius* at relative distance `δ`:
`J_q(δ) = (1 - 1 / q) * (1 - √(1 - q * δ / (q - 1)))`. For `δ > 1 - 1 / q`, `Real.sqrt` of a
negative argument is `0`, so the formula caps at `1 - 1 / q`. -/
@[expose]
noncomputable def johnsonRadius (q δ : ℝ) : ℝ :=
  (1 - 1 / q) * (1 - Real.sqrt (1 - q * δ / (q - 1)))

/-- The *alphabet-free (`q → ∞`) Johnson radius* `1 - √(1 - δ)`. -/
@[expose]
noncomputable def johnsonRadiusLimit (δ : ℝ) : ℝ :=
  1 - Real.sqrt (1 - δ)

@[simp]
theorem johnsonRadius_two (δ : ℝ) :
    johnsonRadius 2 δ = (1 - Real.sqrt (1 - 2 * δ)) / 2 := by
  simp only [johnsonRadius]
  ring_nf

@[simp]
theorem johnsonRadius_zero_right (q : ℝ) : johnsonRadius q 0 = 0 := by
  simp [johnsonRadius]

@[simp]
theorem johnsonRadiusLimit_zero : johnsonRadiusLimit 0 = 0 := by
  simp [johnsonRadiusLimit]

/-- Rewrites `J_q(δ)` as `θ - √(θ ^ 2 - θ * δ)` where `θ = 1 - 1 / q > 0`. -/
private theorem johnsonRadius_eq_sub_sqrt {q : ℝ} (hq : 1 < q) (δ : ℝ) :
    johnsonRadius q δ = (1 - 1 / q) - Real.sqrt ((1 - 1 / q) ^ 2 - (1 - 1 / q) * δ) := by
  have hθ : 0 < 1 - 1 / q := sub_pos.2 (div_lt_one (zero_lt_one.trans hq) |>.2 hq)
  have hmul : (1 - 1 / q) ^ 2 * (1 - q * δ / (q - 1)) =
      (1 - 1 / q) ^ 2 - (1 - 1 / q) * δ := by
    have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
    have hq1 : q - 1 ≠ 0 := sub_ne_zero.2 hq.ne'
    field_simp
  rw [johnsonRadius, mul_sub, mul_one]
  nth_rw 2 [← Real.sqrt_sq hθ.le]
  rw [← Real.sqrt_mul (sq_nonneg _), hmul]

theorem johnsonRadius_nonneg {q δ : ℝ} (hq : 1 < q) (hδ : 0 ≤ δ) :
    0 ≤ johnsonRadius q δ := by
  have hθ : 0 ≤ 1 - 1 / q := sub_nonneg.2 ((div_le_one (zero_lt_one.trans hq)).2 hq.le)
  have hq0 : 0 ≤ q := (zero_lt_one.trans hq).le
  have hq1 : 0 < q - 1 := sub_pos.2 hq
  have hsub : 1 - q * δ / (q - 1) ≤ 1 := by
    have : 0 ≤ q * δ / (q - 1) := by positivity
    linarith
  have hsqrt : Real.sqrt (1 - q * δ / (q - 1)) ≤ 1 := Real.sqrt_le_one.2 hsub
  exact mul_nonneg hθ (sub_nonneg.2 hsqrt)

theorem johnsonRadius_le_one_sub_inv {q δ : ℝ} (hq : 1 < q) :
    johnsonRadius q δ ≤ 1 - 1 / q := by
  have hθ : 0 ≤ 1 - 1 / q := sub_nonneg.2 ((div_le_one (zero_lt_one.trans hq)).2 hq.le)
  have h1 : 1 - Real.sqrt (1 - q * δ / (q - 1)) ≤ 1 := by
    linarith [Real.sqrt_nonneg (1 - q * δ / (q - 1))]
  rw [johnsonRadius]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 hθ

theorem johnsonRadius_mono_right {q δ₁ δ₂ : ℝ} (hq : 1 < q) (hδ : δ₁ ≤ δ₂) :
    johnsonRadius q δ₁ ≤ johnsonRadius q δ₂ := by
  have hθ : 0 ≤ 1 - 1 / q := sub_nonneg.2 ((div_le_one (zero_lt_one.trans hq)).2 hq.le)
  have hq0 : 0 ≤ q := (zero_lt_one.trans hq).le
  have hq1 : 0 < q - 1 := sub_pos.2 hq
  have hrad : 1 - q * δ₂ / (q - 1) ≤ 1 - q * δ₁ / (q - 1) := by
    have : q * δ₁ / (q - 1) ≤ q * δ₂ / (q - 1) := by gcongr
    linarith
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (Real.sqrt_le_sqrt hrad) 1) hθ

/-- For `0 ≤ δ ≤ 1 - 1 / q₁`, the `q`-ary Johnson radius `J_q(δ)` is antitone in `q ≥ q₁`. -/
theorem johnsonRadius_antitone {q₁ q₂ δ : ℝ} (hq₁ : 1 < q₁) (hq : q₁ ≤ q₂)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 - 1 / q₁) : johnsonRadius q₂ δ ≤ johnsonRadius q₁ δ := by
  have hq₂ : 1 < q₂ := hq₁.trans_le hq
  set θ₁ : ℝ := 1 - 1 / q₁
  set θ₂ : ℝ := 1 - 1 / q₂
  have hθ₁ : 0 < θ₁ := sub_pos.2 ((div_lt_one (zero_lt_one.trans hq₁)).2 hq₁)
  have hθ₁₂ : θ₁ ≤ θ₂ := by
    dsimp only [θ₁, θ₂]
    gcongr
  have hrad₁ : 0 ≤ θ₁ ^ 2 - θ₁ * δ := by nlinarith
  set s₁ : ℝ := Real.sqrt (θ₁ ^ 2 - θ₁ * δ)
  have hs₁0 : 0 ≤ s₁ := Real.sqrt_nonneg _
  have hs₁sq : s₁ ^ 2 = θ₁ ^ 2 - θ₁ * δ := Real.sq_sqrt hrad₁
  have hs₁le : s₁ ≤ θ₁ := by
    rw [← Real.sqrt_sq hθ₁.le]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hkey : δ ≤ 2 * (θ₁ - s₁) := by
    have hprod : (θ₁ + s₁) * (θ₁ - s₁) = θ₁ * δ := by nlinarith [hs₁sq]
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : θ₁ + s₁ ≤ 2 * θ₁)
      (sub_nonneg.2 hs₁le)]
  have hsq : ((θ₂ - θ₁) + s₁) ^ 2 ≤ θ₂ ^ 2 - θ₂ * δ := by
    have hu : 0 ≤ θ₂ - θ₁ := sub_nonneg.2 hθ₁₂
    nlinarith [hs₁sq, mul_nonneg hu (sub_nonneg.2 hkey)]
  have hsqrt : (θ₂ - θ₁) + s₁ ≤ Real.sqrt (θ₂ ^ 2 - θ₂ * δ) :=
    (Real.le_sqrt_of_sq_le le_rfl).trans (Real.sqrt_le_sqrt hsq)
  rw [johnsonRadius_eq_sub_sqrt hq₁, johnsonRadius_eq_sub_sqrt hq₂]
  change θ₂ - Real.sqrt (θ₂ ^ 2 - θ₂ * δ) ≤ θ₁ - s₁
  linarith

/-- As the alphabet size `q → ∞`, `J_q(δ)` converges to `1 - √(1 - δ)`. -/
theorem tendsto_johnsonRadius_atTop (δ : ℝ) :
    Tendsto (fun q : ℝ => johnsonRadius q δ) atTop (nhds (johnsonRadiusLimit δ)) := by
  have hdiv : Tendsto (fun q : ℝ => (1 : ℝ) / q) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hθ : Tendsto (fun q : ℝ => 1 - 1 / q) atTop (nhds 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hdiv
  have hqsub : Tendsto (fun q : ℝ => q / (q - 1)) atTop (nhds 1) := by
    refine ((hθ.inv₀ one_ne_zero).congr' ?_).trans (by simp)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with q hq
    have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
    have hq1 : q - 1 ≠ 0 := sub_ne_zero.2 hq.ne'
    field_simp
  have hinner : Tendsto (fun q : ℝ => 1 - q * δ / (q - 1)) atTop (nhds (1 - δ)) := by
    simpa only [div_mul_eq_mul_div, one_mul] using tendsto_const_nhds.sub (hqsub.mul_const δ)
  have hsqrt : Tendsto (fun q : ℝ => Real.sqrt (1 - q * δ / (q - 1))) atTop
      (nhds (Real.sqrt (1 - δ))) :=
    (Real.continuous_sqrt.tendsto (1 - δ)).comp hinner
  have hprod : Tendsto (fun q : ℝ => (1 - 1 / q) * (1 - Real.sqrt (1 - q * δ / (q - 1)))) atTop
      (nhds (1 * (1 - Real.sqrt (1 - δ)))) :=
    hθ.mul (tendsto_const_nhds.sub hsqrt)
  simpa only [johnsonRadius, johnsonRadiusLimit, one_mul] using hprod

/-- For any `1 < q` and `0 ≤ δ ≤ 1 - 1 / q`, the alphabet-free radius `1 - √(1 - δ)` is at most
`J_q(δ)`. -/
theorem johnsonRadiusLimit_le_johnsonRadius {q δ : ℝ} (hq : 1 < q) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 - 1 / q) : johnsonRadiusLimit δ ≤ johnsonRadius q δ :=
  le_of_tendsto (tendsto_johnsonRadius_atTop δ)
    ((eventually_ge_atTop q).mono fun _ hqq' => johnsonRadius_antitone hq hqq' hδ0 hδ)

end Radius

/-! ### The real-valued `q`-ary and alphabet-free Johnson bounds -/

section JohnsonBounds

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-- Algebraic identity for the second-moment denominator of the `q`-ary Johnson bound:
`(q - 1) * (n - e)^2 + e^2 - (q - 1) * n * (n - d) ≥ n^2 * q * ε^2` when
`e / n ≤ J_q(d / n) - ε`. -/
private theorem qary_johnson_denom_ge {q n d e : ℕ} (hq : 2 ≤ q) (hn : 0 < n)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : ρ ≤ johnsonRadius q ((d : ℝ) / n) - ε)
    (heρ : (e : ℝ) ≤ ρ * n) :
    (n : ℝ) ^ 2 * (q : ℝ) * ε ^ 2 ≤
      ((q : ℝ) - 1) * ((n : ℝ) - e) ^ 2 + (e : ℝ) ^ 2 -
        ((q : ℝ) - 1) * n * ((n : ℝ) - d) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  set θ : ℝ := 1 - 1 / (q : ℝ)
  set δ : ℝ := (d : ℝ) / n
  set x : ℝ := (e : ℝ) / n
  have hxρ : x ≤ ρ := (div_le_iff₀ hnR).2 heρ
  have hJ : johnsonRadius q δ = θ - Real.sqrt (θ ^ 2 - θ * δ) :=
    johnsonRadius_eq_sub_sqrt hqR δ
  set s : ℝ := Real.sqrt (θ ^ 2 - θ * δ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs_le : θ ^ 2 - θ * δ ≤ s ^ 2 := by
    rcases le_total (θ ^ 2 - θ * δ) 0 with hle | hge
    · exact hle.trans (sq_nonneg s)
    · exact (Real.sq_sqrt hge).ge
  have hθx : s + ε ≤ θ - x := by linarith
  have hdiff : ε ^ 2 ≤ (θ - x) ^ 2 - (θ ^ 2 - θ * δ) := by
    nlinarith [pow_le_pow_left₀ (by positivity) hθx 2, mul_nonneg hs0 hε.le]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hinner_id :
      ((q : ℝ) - 1) * (1 - x) ^ 2 + x ^ 2 - ((q : ℝ) - 1) * (1 - δ) =
        (q : ℝ) * ((θ - x) ^ 2 - (θ ^ 2 - θ * δ)) := by
    dsimp only [θ]
    field_simp
    ring
  have hid :
      ((q : ℝ) - 1) * ((n : ℝ) - e) ^ 2 + (e : ℝ) ^ 2 -
          ((q : ℝ) - 1) * n * ((n : ℝ) - d) =
        (n : ℝ) ^ 2 * (q : ℝ) * ((θ - x) ^ 2 - (θ ^ 2 - θ * δ)) := by
    have he_eq : (e : ℝ) = x * n := by dsimp only [x]; field_simp
    have hd_eq : (d : ℝ) = δ * n := by dsimp only [δ]; field_simp
    rw [he_eq, hd_eq]
    calc ((q : ℝ) - 1) * ((n : ℝ) - x * n) ^ 2 + (x * n) ^ 2 -
            ((q : ℝ) - 1) * n * ((n : ℝ) - δ * n)
          = (n : ℝ) ^ 2 *
              (((q : ℝ) - 1) * (1 - x) ^ 2 + x ^ 2 - ((q : ℝ) - 1) * (1 - δ)) := by ring
      _ = (n : ℝ) ^ 2 * (q : ℝ) * ((θ - x) ^ 2 - (θ ^ 2 - θ * δ)) := by
          rw [hinner_id, mul_assoc]
  rw [hid]
  have hnq0 : 0 ≤ (n : ℝ) ^ 2 * (q : ℝ) := by positivity
  nlinarith

/-- Bridge from the strict real `q`-ary Johnson radius condition `e / n < J_q(d / n)` (with
`q ≥ 2` and `d ≤ n`) to the natural-number hypotheses `q * e ≤ (q - 1) * n` and
`(q - 1) * n * (n - d) < (q - 1) * (n - e) ^ 2 + e ^ 2` required by
`Cslib.Code.card_filter_hammingDist_le_mul_le_of_mul_le` and
`Cslib.Code.card_mul_sum_choose_le`. -/
theorem mul_le_sub_one_mul_and_lt_of_lt_johnsonRadius {q n d e : ℕ} (hq : 2 ≤ q) (hn : 0 < n)
    (hdn : d ≤ n) (he : (e : ℝ) / n < johnsonRadius q ((d : ℝ) / n)) :
    q * e ≤ (q - 1) * n ∧
      (q - 1) * n * (n - d) < (q - 1) * (n - e) ^ 2 + e ^ 2 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have he_lt : (e : ℝ) < (1 - 1 / (q : ℝ)) * n :=
    (div_lt_iff₀ hnR).1 (he.trans_le (johnsonRadius_le_one_sub_inv hqR))
  have hqe : q * e ≤ (q - 1) * n := by
    have hlt : ((q * e : ℕ) : ℝ) < (((q - 1) * n : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
      calc (q : ℝ) * e < q * ((1 - 1 / (q : ℝ)) * n) :=
            mul_lt_mul_of_pos_left he_lt (by positivity)
        _ = ((q : ℝ) - 1) * n := by field_simp
    exact_mod_cast hlt.le
  have hen : e ≤ n :=
    Nat.le_of_mul_le_mul_left (hqe.trans (Nat.mul_le_mul_right n (Nat.sub_le q 1))) (by omega)
  set ε : ℝ := johnsonRadius q ((d : ℝ) / n) - (e : ℝ) / n
  have hε : 0 < ε := sub_pos.2 he
  have hdenom := qary_johnson_denom_ge hq hn hε (ρ := (e : ℝ) / n)
    (by rw [sub_sub_cancel]) (by rw [div_mul_cancel₀ _ hnR.ne'])
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 * q * ε ^ 2 := by positivity
  have hltR :
      (((q - 1) * n * (n - d) : ℕ) : ℝ) < (((q - 1) * (n - e) ^ 2 + e ^ 2 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub hdn, Nat.cast_sub hen]
    linarith only [hdenom, hpos]
  exact ⟨hqe, by exact_mod_cast hltR⟩

private theorem isListDecodable_of_neg [Nonempty ι] {C : Set (ι → α)} {ρ : ℝ} {L : ℕ}
    (hρ : ρ < 0) : IsListDecodable C ρ L := fun w => by
  have hnR : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hempty : {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} = ∅ := by
    ext c
    simp only [Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro _
    have h1 : ρ * Fintype.card ι < 0 := mul_neg_of_neg_of_pos hρ hnR
    linarith [Nat.cast_nonneg (α := ℝ) (hammingDist c w)]
  rw [hempty, Set.encard_empty]
  exact zero_le

private theorem subsingleton_of_card_lt_of_le_minDist {C : Set (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist C) (hnd : Fintype.card ι < d) : C.Subsingleton := by
  by_contra hnontriv
  have hle : (d : ℕ∞) ≤ Fintype.card ι :=
    hd.trans (minDist_le_card (Set.not_subsingleton_iff.1 hnontriv))
  exact absurd (Nat.cast_le.1 hle) (not_le_of_gt hnd)

private theorem isListDecodable_of_subsingleton {C : Set (ι → α)} {ρ : ℝ} {L : ℕ}
    (hC : C.Subsingleton) (hL : 1 ≤ L) : IsListDecodable C ρ L := fun w =>
  have henc : {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι}.encard ≤ 1 :=
    Set.encard_le_one_iff.2 fun _ _ ha hb => hC ha.1 hb.1
  henc.trans (by exact_mod_cast hL)

private theorem filter_hammingDist_le_floor_eq_self {C : Set (ι → α)} {w : ι → α} {ρ : ℝ}
    {B : Finset (ι → α)}
    (hB : (B : Set (ι → α)) ⊆ {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι}) :
    {c ∈ B | hammingDist c w ≤ ⌊ρ * Fintype.card ι⌋₊} = B := by
  ext c
  simp only [Finset.mem_filter, and_iff_left_iff_imp]
  exact fun hc => Nat.le_floor (hB hc).2

/-- **The real-valued `q`-ary Johnson bound** [Johnson1962] (locator unverified),
[GuruswamiRudraSudan2019] (locator unverified): over an alphabet of `q ≥ 2` letters, a code `C` of
length `n ≥ 1` and minimum distance at least `d` (relative distance `δ = d / n`) is
`(ρ, L)`-list-decodable for every `ε > 0` and `ρ ≤ J_q(δ) - ε`, with constant list size
`L = ⌊(q - 1) * δ / (q * ε ^ 2)⌋₊`.

In particular, since `(q - 1) * δ / q ≤ 1 ≤ n`, the list size satisfies
`L ≤ ⌊1 / ε ^ 2⌋₊ ≤ ⌊n / ε ^ 2⌋₊`. -/
theorem isListDecodable_of_le_johnsonRadius [Nonempty ι] [Fintype α]
    (hq : 2 ≤ Fintype.card α) {C : Set (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist C) {ε ρ : ℝ} (hε : 0 < ε)
    (hρ : ρ ≤ johnsonRadius (Fintype.card α) ((d : ℝ) / Fintype.card ι) - ε) :
    IsListDecodable C ρ
      ⌊((Fintype.card α : ℝ) - 1) * ((d : ℝ) / Fintype.card ι) /
          (Fintype.card α * ε ^ 2)⌋₊ := by
  by_cases hneg : ρ < 0
  · exact isListDecodable_of_neg hneg
  push Not at hneg
  set n : ℕ := Fintype.card ι
  set q : ℕ := Fintype.card α
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  set δ : ℝ := (d : ℝ) / n
  rcases lt_or_ge n d with hnd | hdn
  · refine isListDecodable_of_subsingleton (subsingleton_of_card_lt_of_le_minDist hd hnd)
      (Nat.floor_pos.2 ?_)
    have hδ1 : 1 ≤ δ := (one_le_div hnR).2 (by exact_mod_cast hnd.le)
    have hε_le : ε ≤ 1 - 1 / (q : ℝ) := by
      linarith [johnsonRadius_le_one_sub_inv (δ := δ) hqR]
    have hθ : 0 < 1 - 1 / (q : ℝ) := sub_pos.2 ((div_lt_one (zero_lt_one.trans hqR)).2 hqR)
    have hθ1 : 1 - 1 / (q : ℝ) ≤ 1 := sub_le_self 1 (by positivity)
    have hq0 : (0 : ℝ) < q := by positivity
    have hθq : (1 - 1 / (q : ℝ)) * q = q - 1 := by field_simp
    have hden : ε ^ 2 ≤ 1 - 1 / (q : ℝ) := by
      have : ε ^ 2 ≤ (1 - 1 / (q : ℝ)) ^ 2 := pow_le_pow_left₀ hε.le hε_le 2
      nlinarith
    rw [le_div_iff₀ (by positivity), one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hden hq0.le,
      mul_le_mul_of_nonneg_left hδ1 (sub_pos.2 hqR).le]
  -- Non-degenerate regime `d ≤ n`: apply `Code.card_filter_hammingDist_le_mul_le_of_mul_le`.
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  refine isListDecodable_iff_forall_finset.2 fun w B hB => ?_
  set e : ℕ := ⌊ρ * n⌋₊
  have heρ : (e : ℝ) ≤ ρ * n := Nat.floor_le (mul_nonneg hneg hnR.le)
  have he_lt : (e : ℝ) / n < johnsonRadius q ((d : ℝ) / n) :=
    ((div_le_iff₀ hnR).2 heρ).trans_lt (hρ.trans_lt (sub_lt_self _ hε))
  have hhyp := mul_le_sub_one_mul_and_lt_of_lt_johnsonRadius hq hn0 hdn he_lt
  have hdB : (d : ℕ∞) ≤ minDist (B : Set (ι → α)) :=
    hd.trans (minDist_anti (hB.trans (Set.sep_subset _ _)))
  have hjohn := card_filter_hammingDist_le_mul_le_of_mul_le hdB w hhyp.1
  rw [filter_hammingDist_le_floor_eq_self hB] at hjohn
  have hen : e ≤ n :=
    Nat.le_of_mul_le_mul_left (hhyp.1.trans (Nat.mul_le_mul_right n (Nat.sub_le q 1))) (by omega)
  have hdenom := qary_johnson_denom_ge hq hn0 hε hρ heρ
  have hjohnR : (#B : ℝ) * ((n : ℝ) ^ 2 * q * ε ^ 2) ≤ ((q : ℝ) - 1) * n * d := by
    have h1 : ((#B * ((q - 1) * (n - e) ^ 2 + e ^ 2 - (q - 1) * n * (n - d)) : ℕ) : ℝ) ≤
        (((q - 1) * n * d : ℕ) : ℝ) := by exact_mod_cast hjohn
    push_cast [Nat.cast_sub hhyp.2.le, Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_sub hdn, Nat.cast_sub hen] at h1
    exact (mul_le_mul_of_nonneg_left hdenom (Nat.cast_nonneg _)).trans h1
  have hB_le : (#B : ℝ) ≤ ((q : ℝ) - 1) * δ / (q * ε ^ 2) := by
    have hdn_eq : ((q : ℝ) - 1) * δ * n ^ 2 = ((q : ℝ) - 1) * n * d := by
      dsimp only [δ]
      field_simp
    rw [le_div_iff₀ (by positivity)]
    refine le_of_mul_le_mul_right ?_ (sq_pos_of_pos hnR)
    linarith [hjohnR]
  exact Nat.le_floor hB_le

/-- **The alphabet-free (`q → ∞`) real Johnson bound** [Johnson1962] (locator unverified),
[GuruswamiRudraSudan2019] (locator unverified): whatever the alphabet `α`, a code `C : Set (ι → α)`
of length `n ≥ 1` and minimum distance at least `d` (`δ = d / n`) is `(ρ, L)`-list-decodable for
every `ε > 0` and `ρ ≤ 1 - √(1 - δ) - ε`, with constant list size `L = ⌊δ / ε ^ 2⌋₊`. -/
theorem isListDecodable_of_le_johnsonRadiusLimit [Nonempty ι] {C : Set (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist C) {ε ρ : ℝ} (hε : 0 < ε)
    (hρ : ρ ≤ johnsonRadiusLimit ((d : ℝ) / Fintype.card ι) - ε) :
    IsListDecodable C ρ ⌊((d : ℝ) / Fintype.card ι) / ε ^ 2⌋₊ := by
  by_cases hneg : ρ < 0
  · exact isListDecodable_of_neg hneg
  push Not at hneg
  set n : ℕ := Fintype.card ι
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  set δ : ℝ := (d : ℝ) / n
  have hJL : johnsonRadiusLimit δ ≤ 1 := by
    rw [johnsonRadiusLimit]
    linarith [Real.sqrt_nonneg (1 - δ)]
  rcases lt_or_ge n d with hnd | hdn
  · refine isListDecodable_of_subsingleton (subsingleton_of_card_lt_of_le_minDist hd hnd)
      (Nat.floor_pos.2 ?_)
    have hδ1 : 1 ≤ δ := (one_le_div hnR).2 (by exact_mod_cast hnd.le)
    have hε1 : ε ≤ 1 := by linarith
    rw [le_div_iff₀ (sq_pos_of_pos hε), one_mul]
    exact (pow_le_one₀ hε.le hε1).trans hδ1
  refine isListDecodable_iff_forall_finset.2 fun w B hB => ?_
  set e : ℕ := ⌊ρ * n⌋₊
  have heρ : (e : ℝ) ≤ ρ * n := Nat.floor_le (mul_nonneg hneg hnR.le)
  have hen : e ≤ n := by
    have : (e : ℝ) < n := heρ.trans_lt (by nlinarith)
    exact_mod_cast this.le
  set x : ℝ := (e : ℝ) / n
  have hxρ : x ≤ ρ := (div_le_iff₀ hnR).2 heρ
  set s : ℝ := Real.sqrt (1 - δ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h1δ : 1 - δ = s ^ 2 := (Real.sq_sqrt (sub_nonneg.2 ((div_le_one hnR).2
    (by exact_mod_cast hdn)))).symm
  have h1x : s + ε ≤ 1 - x := by
    have : ρ ≤ 1 - s - ε := hρ
    linarith
  have hdenom : (n : ℝ) ^ 2 * ε ^ 2 ≤ ((n : ℝ) - e) ^ 2 - (n : ℝ) * ((n : ℝ) - d) := by
    have hsq := pow_le_pow_left₀ (by positivity) h1x 2
    have he_eq : (e : ℝ) = x * n := by dsimp only [x]; field_simp
    have hd_eq : (d : ℝ) = δ * n := by dsimp only [δ]; field_simp
    rw [he_eq, hd_eq]
    have hid : ((n : ℝ) - x * n) ^ 2 - (n : ℝ) * ((n : ℝ) - δ * n) =
        (n : ℝ) ^ 2 * ((1 - x) ^ 2 - (1 - δ)) := by ring
    rw [hid, h1δ]
    nlinarith [sq_pos_of_pos hnR, mul_nonneg hs0 hε.le]
  have hdB : (d : ℕ∞) ≤ minDist (B : Set (ι → α)) :=
    hd.trans (minDist_anti (hB.trans (Set.sep_subset _ _)))
  have hjohn := card_filter_hammingDist_le_mul_le hdB w e
  rw [filter_hammingDist_le_floor_eq_self hB] at hjohn
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 * ε ^ 2 := by positivity
  have hle_N : n * (n - d) ≤ (n - e) ^ 2 := by
    have h2 : ((n * (n - d) : ℕ) : ℝ) ≤ ((n - e) ^ 2 : ℕ) := by
      push_cast [Nat.cast_sub hen, Nat.cast_sub hdn]
      linarith
    exact_mod_cast h2
  have hjohnR : (#B : ℝ) * ((n : ℝ) ^ 2 * ε ^ 2) ≤ (n : ℝ) * (d - e : ℕ) := by
    have h1 : ((#B * ((n - e) ^ 2 - n * (n - d)) : ℕ) : ℝ) ≤ ((n * (d - e) : ℕ) : ℝ) := by
      exact_mod_cast hjohn
    push_cast [Nat.cast_sub hle_N, Nat.cast_sub hen, Nat.cast_sub hdn] at h1
    exact (mul_le_mul_of_nonneg_left hdenom (Nat.cast_nonneg _)).trans h1
  have hrhs : (n : ℝ) * ((d - e : ℕ) : ℝ) ≤ (n : ℝ) * d := by
    gcongr
    exact Nat.sub_le d e
  have hB_le : (#B : ℝ) ≤ δ / ε ^ 2 := by
    have hdn_eq : δ * (n : ℝ) ^ 2 = (n : ℝ) * d := by dsimp only [δ]; field_simp
    rw [le_div_iff₀ (sq_pos_of_pos hε)]
    nlinarith [hjohnR.trans hrhs, sq_pos_of_pos hnR]
  exact Nat.le_floor hB_le

/-- **Combinatorial list-decodability of Reed–Solomon codes up to the Johnson radius**
[GuruswamiSudan1999] (locator unverified), [GuruswamiRudraSudan2019] (locator unverified): with
`n ≥ 1` distinct evaluation points `α`, a Reed–Solomon code `reedSolomon α k` of dimension
`1 ≤ k ≤ n` over any field `F` has minimum distance at least `d = n - k + 1`, so for every `ε > 0`
it is combinatorially `(ρ, L)`-list-decodable up to `ρ ≤ 1 - √((k - 1) / n) - ε` with list size
`L = ⌊(1 - (k - 1) / n) / ε ^ 2⌋₊` (in particular for every `ρ ≤ 1 - √(k / n) - ε`).

This is the combinatorial Johnson-radius bound on Hamming-ball intersections obtained from
`isListDecodable_of_le_johnsonRadiusLimit`, **not** an algorithmic Guruswami–Sudan list decoder;
for the explicit bivariate-interpolation decoder, see
`CslibFrontier.Foundations.Data.Code.GuruswamiSudan`. -/
theorem isListDecodable_reedSolomon [Nonempty ι] {F : Type*} [Field F] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    {ε ρ : ℝ} (hε : 0 < ε)
    (hρ : ρ ≤ 1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card ι) - ε) :
    IsListDecodable (reedSolomon α k : Set (ι → F)) ρ
      ⌊(1 - ((k - 1 : ℕ) : ℝ) / Fintype.card ι) / ε ^ 2⌋₊ := by
  set n : ℕ := Fintype.card ι
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  have hd_eq : ((n - k + 1 : ℕ) : ℝ) / n = 1 - ((k - 1 : ℕ) : ℝ) / n := by
    rw [show n - k + 1 = n - (k - 1) by omega, Nat.cast_sub (by omega), sub_div,
      div_self hnR.ne']
  have hρ' : ρ ≤ johnsonRadiusLimit (((n - k + 1 : ℕ) : ℝ) / n) - ε := by
    rwa [johnsonRadiusLimit, hd_eq, sub_sub_cancel]
  have h := isListDecodable_of_le_johnsonRadiusLimit (le_minDist_reedSolomon hα k) hε hρ'
  convert h using 3
  exact hd_eq.symm

end JohnsonBounds

end Cslib.Code
