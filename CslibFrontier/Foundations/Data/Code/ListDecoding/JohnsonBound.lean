/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
public import CslibFrontier.Foundations.Data.Code.Linear
public import CslibFrontier.Foundations.Data.Code.ListDecoding
public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.Code.EliasBassalygo
import CslibFrontier.Foundations.Data.Code.Johnson
import CslibFrontier.Foundations.Data.Nat.Choose.Entropy
-- `import all` only to unfold `Real.qaryEntropy`, whose body Mathlib does not expose.
import all Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# List decodability, the real Johnson bound, and the Elias–Bassalygo rate bound

A code `C : Set (ι → α)` of length `n = |ι|` is *(ρ, L)-list-decodable*
(`Cslib.Code.IsListDecodable`) if every Hamming ball of relative radius `ρ` contains at most `L`
codewords. For injective encoders of finite message spaces, this is equivalent to admitting a
`Cslib.ListCode` that list decodes up to radius `ρ`
(`Cslib.Code.isListDecodable_range_iff_exists_listCode`).

Building on the integer second-moment Johnson inequalities of
`CslibFrontier.Foundations.Data.Code.Johnson` (`Cslib.Code.card_filter_hammingDist_le_mul_le` and
`Cslib.Code.card_filter_hammingDist_le_mul_le_of_mul_le`) and the finite Elias–Bassalygo bound of
`CslibFrontier.Foundations.Data.Code.EliasBassalygo`, this module formalizes the real-valued
Johnson radii and list-size bounds:

* `Cslib.Code.johnsonRadius q δ`: the `q`-ary Johnson radius
  `J_q(δ) = (1 - 1 / q) * (1 - √(1 - q * δ / (q - 1)))`, which decreases in `q`
  (`Cslib.Code.johnsonRadius_antitone`) and tends to
  `Cslib.Code.johnsonRadiusLimit δ = 1 - √(1 - δ)` as `q → ∞`
  (`Cslib.Code.tendsto_johnsonRadius_atTop`).
* `Cslib.Code.isListDecodable_of_le_johnsonRadius`: over any alphabet of `q ≥ 2` letters, a code
  with minimum distance at least `d` and relative distance `δ = d / n` is `(ρ, L)`-list-decodable
  for every `ρ ≤ J_q(δ) - ε` with constant list size
  `L = ⌊(q - 1) * δ / (q * ε ^ 2)⌋₊ ≤ ⌊1 / ε ^ 2⌋₊ ≤ ⌊n / ε ^ 2⌋₊`.
* `Cslib.Code.isListDecodable_binary_of_le_johnsonRadius`: specialization to binary codes `ι → Bool`
  at radius `ρ ≤ (1 - √(1 - 2 * δ)) / 2 - ε` with list size `⌊δ / (2 * ε ^ 2)⌋₊`.
* `Cslib.Code.isListDecodable_of_le_johnsonRadiusLimit` and
  `Cslib.Code.isListDecodable_reedSolomon`: the alphabet-free `1 - √(1 - δ) - ε` Johnson bound
  (`⌊δ / ε ^ 2⌋₊`) and its instantiation for Reed–Solomon codes `Cslib.Code.reedSolomon` over
  arbitrary (possibly infinite) fields.
* `Cslib.Code.rate_le_of_lt_johnsonRadius` and
  `Cslib.Code.eventually_rate_le_one_sub_qaryEntropy_johnsonRadius`: combining the Johnson radius
  with `Cslib.Code.card_mul_sum_choose_le` and the single-term entropy lower bound on Hamming ball
  volume yields the finite and asymptotic **Elias–Bassalygo rate bound**
  `rate C ≤ 1 - H_q(J_q(δ)) / log q + ε` as `n → ∞`.

## Main definitions

* `Cslib.Code.IsListDecodable`: `(ρ, L)`-list-decodability of a code `C : Set (ι → α)`.
* `Cslib.Code.johnsonRadius`: the `q`-ary Johnson radius `J_q(δ)`.
* `Cslib.Code.johnsonRadiusLimit`: the alphabet-free / `q → ∞` limit `1 - √(1 - δ)`.

## Main results

* `Cslib.Code.isListDecodable_range_iff_exists_listCode`: equivalence between combinatorial
  `(ρ, L)`-list-decodability and `Cslib.ListCode.ListDecodes`.
* `Cslib.Code.johnsonRadiusLimit_le_johnsonRadius`, `Cslib.Code.johnsonRadius_antitone`,
  `Cslib.Code.tendsto_johnsonRadius_atTop`: monotonicity and `q → ∞` convergence of `J_q(δ)`.
* `Cslib.Code.isListDecodable_of_le_johnsonRadius`,
  `Cslib.Code.isListDecodable_binary_of_le_johnsonRadius`,
  `Cslib.Code.isListDecodable_of_le_johnsonRadiusLimit`,
  `Cslib.Code.isListDecodable_reedSolomon`: `q`-ary, binary, alphabet-free, and Reed–Solomon
  list-decodability up to the Johnson radius.
* `Cslib.Code.rate_le_of_lt_johnsonRadius`,
  `Cslib.Code.eventually_rate_le_one_sub_qaryEntropy_johnsonRadius`: finite and asymptotic
  Elias–Bassalygo rate upper bounds.

## References

* [S. M. Johnson, *A new upper bound for error-correcting codes*][Johnson1962]
* [L. A. Bassalygo, *New upper bounds for error-correcting codes*][Bassalygo1965]
* [V. Guruswami, M. Sudan, *Improved Decoding of Reed--Solomon and Algebraic-Geometry Codes*]
  [GuruswamiSudan1999]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
-/

public section

namespace Cslib.Code

open Finset Filter
open scoped Topology

section ListDecodable

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-- A code `C : Set (ι → α)` is *(ρ, L)-list-decodable* if every Hamming ball of relative radius
`ρ` contains at most `L` codewords. -/
@[expose]
def IsListDecodable (C : Set (ι → α)) (ρ : ℝ) (L : ℕ) : Prop :=
  ∀ w : ι → α, {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι}.encard ≤ L

/-- A finite code `C : Finset (ι → α)` is `(ρ, L)`-list-decodable iff every Hamming ball of
relative radius `ρ` meets `C` in at most `L` codewords. -/
theorem isListDecodable_finset_iff {C : Finset (ι → α)} {ρ : ℝ} {L : ℕ} :
    IsListDecodable (C : Set (ι → α)) ρ L ↔
      ∀ w : ι → α, #{c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} ≤ L := by
  refine forall_congr' fun w => ?_
  have hset : ({c ∈ (C : Set (ι → α)) | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} : Set _) =
      ((C.filter fun c => (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι : Finset (ι → α)) :
        Set (ι → α)) := by
    ext c
    simp
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]

/-- List decodability is downward closed in the code and radius and upward closed in the list
size. -/
theorem IsListDecodable.mono {C C' : Set (ι → α)} {ρ ρ' : ℝ} {L L' : ℕ}
    (h : IsListDecodable C ρ L) (hC : C' ⊆ C) (hρ : ρ' ≤ ρ) (hL : L ≤ L') :
    IsListDecodable C' ρ' L' := fun w => by
  have hsub : {c ∈ C' | (hammingDist c w : ℝ) ≤ ρ' * Fintype.card ι} ⊆
      {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} := by
    rintro c ⟨hc, hdist⟩
    refine ⟨hC hc, hdist.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _)
  exact (Set.encard_le_encard hsub).trans ((h w).trans (Nat.cast_le.2 hL))

/-- For an injective encoder of a finite nonempty message type, combinatorial `(ρ, L)`-list
decodability of `Set.range enc` is equivalent to the existence of a `ListCode` with encoder `enc`
that list decodes up to radius `ρ`. -/
theorem isListDecodable_range_iff_exists_listCode {M : Type*} [Finite M] [Nonempty M]
    {enc : M → ι → α} (henc : Function.Injective enc) {ρ : ℝ} {L : ℕ} :
    IsListDecodable (Set.range enc) ρ L ↔
      ∃ D : ListCode M ι α L, D.encode = enc ∧ D.ListDecodes ρ := by
  classical
  constructor
  · intro h
    have := Fintype.ofFinite M
    let S : (ι → α) → Finset M := fun w =>
      {x | (hammingDist (enc x) w : ℝ) ≤ ρ * Fintype.card ι}
    have hS (w : ι → α) : #(S w) ≤ L := by
      have himg : ((S w).image enc : Set (ι → α)) ⊆
          {c ∈ Set.range enc | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} := by
        rintro c hc
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and, S] at hc
        obtain ⟨x, hdist, rfl⟩ := hc
        exact ⟨⟨x, rfl⟩, hdist⟩
      have hencard : (((S w).image enc : Finset (ι → α)) : Set (ι → α)).encard ≤ L :=
        (Set.encard_le_encard himg).trans (h w)
      rw [Set.encard_coe_eq_coe_finsetCard, card_image_of_injective _ henc, Nat.cast_le]
        at hencard
      exact hencard
    refine ⟨⟨enc, fun w k => (S w).toList.getD k (Classical.arbitrary M)⟩, rfl, fun x w hx => ?_⟩
    have hxS : x ∈ (S w).toList := by
      rw [Finset.mem_toList, Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hx⟩
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 hxS
    refine ⟨⟨i, hi.trans_le ((Finset.length_toList _).trans_le (hS w))⟩, ?_⟩
    change (S w).toList.getD i _ = x
    rw [List.getD_eq_getElem _ _ hi, hix]
  · rintro ⟨D, rfl, hD⟩ w
    have hsub : {c ∈ Set.range D.encode | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} ⊆
        (((Finset.univ : Finset (Fin L)).image fun k => D.encode (D.decode w k) :
          Finset (ι → α)) : Set (ι → α)) := by
      rintro c ⟨⟨x, rfl⟩, hdist⟩
      obtain ⟨k, hk⟩ := hD x w hdist
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact ⟨k, congrArg D.encode hk⟩
    refine (Set.encard_le_encard hsub).trans ?_
    rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
    exact card_image_le.trans_eq (card_fin L)

private theorem encard_le_coe_of_finset_card_le {γ : Type*} {S : Set γ} {L : ℕ}
    (h : ∀ B : Finset γ, (B : Set γ) ⊆ S → #B ≤ L) :
    S.encard ≤ L := by
  classical
  by_contra! hlt
  have hle : ((L + 1 : ℕ) : ℕ∞) ≤ S.encard := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Order.add_one_le_of_lt hlt
  obtain ⟨t, hts, ht⟩ := Set.exists_subset_encard_eq hle
  have htFin : t.Finite := Set.finite_of_encard_eq_coe ht
  have hcard : #(htFin.toFinset) = L + 1 := by
    rw [← Nat.cast_inj (R := ℕ∞), ← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset, ht]
  have hB := h htFin.toFinset (by simpa using hts)
  omega

end ListDecodable

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

/-- For any `1 < q` and `0 ≤ δ ≤ 1 - 1 / q`, the alphabet-free radius `1 - √(1 - δ)` is at most
`J_q(δ)`. -/
theorem johnsonRadiusLimit_le_johnsonRadius {q δ : ℝ} (hq : 1 < q) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 - 1 / q) : johnsonRadiusLimit δ ≤ johnsonRadius q δ := by
  set θ : ℝ := 1 - 1 / q
  have hθ : 0 < θ := sub_pos.2 ((div_lt_one (zero_lt_one.trans hq)).2 hq)
  have hθ1 : θ ≤ 1 := sub_le_self 1 (by positivity)
  have hrad1 : 0 ≤ θ ^ 2 - θ * δ := by nlinarith
  have hrad2 : 0 ≤ 1 - δ := by linarith
  set s : ℝ := Real.sqrt (θ ^ 2 - θ * δ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hssq : s ^ 2 = θ ^ 2 - θ * δ := Real.sq_sqrt hrad1
  have hsle : s ≤ θ := by
    rw [← Real.sqrt_sq hθ.le]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hkey : δ ≤ 2 * (θ - s) := by
    have hprod : (θ + s) * (θ - s) = θ * δ := by nlinarith [hssq]
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : θ + s ≤ 2 * θ)
      (sub_nonneg.2 hsle)]
  have hsq : ((1 - θ) + s) ^ 2 ≤ 1 - δ := by
    have h1θ : 0 ≤ 1 - θ := sub_nonneg.2 hθ1
    nlinarith [hssq, mul_nonneg h1θ (sub_nonneg.2 hkey)]
  have hsqrt : 1 - θ + s ≤ Real.sqrt (1 - δ) := by
    calc 1 - θ + s ≤ Real.sqrt (((1 - θ) + s) ^ 2) := Real.le_sqrt_of_sq_le le_rfl
      _ ≤ Real.sqrt (1 - δ) := Real.sqrt_le_sqrt hsq
  rw [johnsonRadiusLimit, johnsonRadius_eq_sub_sqrt hq]
  change 1 - Real.sqrt (1 - δ) ≤ θ - s
  linarith

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
  have hrad₂ : 0 ≤ θ₂ ^ 2 - θ₂ * δ := by
    have : δ ≤ θ₂ := hδ.trans hθ₁₂
    nlinarith [hθ₁.trans_le hθ₁₂]
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
  have hsqrt : (θ₂ - θ₁) + s₁ ≤ Real.sqrt (θ₂ ^ 2 - θ₂ * δ) := by
    calc (θ₂ - θ₁) + s₁ ≤ Real.sqrt (((θ₂ - θ₁) + s₁) ^ 2) := Real.le_sqrt_of_sq_le le_rfl
      _ ≤ Real.sqrt (θ₂ ^ 2 - θ₂ * δ) := Real.sqrt_le_sqrt hsq
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
    have hmul : Tendsto (fun q : ℝ => q / (q - 1) * δ) atTop (nhds (1 * δ)) :=
      hqsub.mul_const δ
    simpa only [div_mul_eq_mul_div, one_mul] using tendsto_const_nhds.sub hmul
  have hsqrt : Tendsto (fun q : ℝ => Real.sqrt (1 - q * δ / (q - 1))) atTop
      (nhds (Real.sqrt (1 - δ))) :=
    (Real.continuous_sqrt.tendsto (1 - δ)).comp hinner
  have hprod : Tendsto (fun q : ℝ => (1 - 1 / q) * (1 - Real.sqrt (1 - q * δ / (q - 1)))) atTop
      (nhds (1 * (1 - Real.sqrt (1 - δ)))) :=
    hθ.mul (tendsto_const_nhds.sub hsqrt)
  simpa only [johnsonRadius, johnsonRadiusLimit, one_mul] using hprod

end Radius

/-! ### The real-valued `q`-ary, binary, and alphabet-free Johnson bounds -/

section JohnsonBounds

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-- Algebraic identity for the second-moment denominator of the `q`-ary Johnson bound:
`(q - 1) * (n - e)^2 + e^2 - (q - 1) * n * (n - d) ≥ n^2 * q * ε^2` when
`e / n ≤ J_q(d / n) - ε`. -/
private theorem qary_johnson_denom_ge [Nonempty ι] {q d e : ℕ} (hq : 2 ≤ q)
    {ε ρ : ℝ} (hε : 0 < ε)
    (hρ : ρ ≤ johnsonRadius q ((d : ℝ) / Fintype.card ι) - ε)
    (heρ : (e : ℝ) ≤ ρ * Fintype.card ι) :
    (Fintype.card ι : ℝ) ^ 2 * (q : ℝ) * ε ^ 2 ≤
      ((q : ℝ) - 1) * ((Fintype.card ι : ℝ) - e) ^ 2 + (e : ℝ) ^ 2 -
        ((q : ℝ) - 1) * Fintype.card ι * ((Fintype.card ι : ℝ) - d) := by
  set n : ℕ := Fintype.card ι
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  set θ : ℝ := 1 - 1 / (q : ℝ)
  set δ : ℝ := (d : ℝ) / n
  set x : ℝ := (e : ℝ) / n
  have hθ : 0 < θ := sub_pos.2 ((div_lt_one (zero_lt_one.trans hqR)).2 hqR)
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
  have hsq_step : s ^ 2 + 2 * s * ε + ε ^ 2 ≤ (θ - x) ^ 2 := by
    have h1 : (s + ε) ^ 2 ≤ (θ - x) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hθx 2
    linarith
  have hdiff : ε ^ 2 ≤ (θ - x) ^ 2 - (θ ^ 2 - θ * δ) := by
    have : 0 ≤ 2 * s * ε := by positivity
    linarith
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
    have he_eq : (e : ℝ) = x * n := by
      dsimp only [x]
      field_simp
    have hd_eq : (d : ℝ) = δ * n := by
      dsimp only [δ]
      field_simp
    rw [he_eq, hd_eq]
    calc
      ((q : ℝ) - 1) * ((n : ℝ) - x * n) ^ 2 + (x * n) ^ 2 -
          ((q : ℝ) - 1) * n * ((n : ℝ) - δ * n)
          = (n : ℝ) ^ 2 *
              (((q : ℝ) - 1) * (1 - x) ^ 2 + x ^ 2 - ((q : ℝ) - 1) * (1 - δ)) := by ring
      _ = (n : ℝ) ^ 2 * (q : ℝ) * ((θ - x) ^ 2 - (θ ^ 2 - θ * δ)) := by
          rw [hinner_id, mul_assoc]
  rw [hid]
  have hnq0 : 0 ≤ (n : ℝ) ^ 2 * (q : ℝ) := by positivity
  nlinarith

/-- Integer specialization of the `q`-ary Johnson condition from `e / n ≤ J_q(d / n) - ε`:
both `q * e ≤ (q - 1) * n` and `(q - 1) * n * (n - d) < (q - 1) * (n - e) ^ 2 + e ^ 2` hold. -/
private theorem qary_johnson_nat_hypotheses [Nonempty ι] {q d e : ℕ} (hq : 2 ≤ q)
    (hdn : d ≤ Fintype.card ι) {ε ρ : ℝ} (hε : 0 < ε)
    (hρ : ρ ≤ johnsonRadius q ((d : ℝ) / Fintype.card ι) - ε)
    (heρ : (e : ℝ) ≤ ρ * Fintype.card ι) :
    q * e ≤ (q - 1) * Fintype.card ι ∧
      (q - 1) * Fintype.card ι * (Fintype.card ι - d) <
        (q - 1) * (Fintype.card ι - e) ^ 2 + e ^ 2 := by
  set n : ℕ := Fintype.card ι
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hρ_lt : ρ < 1 - 1 / (q : ℝ) :=
    hρ.trans_lt (by linarith [johnsonRadius_le_one_sub_inv (δ := (d : ℝ) / n) hqR])
  have he_lt : (e : ℝ) < (1 - 1 / (q : ℝ)) * n :=
    heρ.trans_lt (mul_lt_mul_of_pos_right hρ_lt hnR)
  have hqe : q * e ≤ (q - 1) * n := by
    have : ((q * e : ℕ) : ℝ) < (((q - 1) * n : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
      have hq0 : (0 : ℝ) < q := by positivity
      calc (q : ℝ) * e < q * ((1 - 1 / (q : ℝ)) * n) := mul_lt_mul_of_pos_left he_lt hq0
        _ = ((q : ℝ) - 1) * n := by field_simp
    exact_mod_cast this.le
  have hen : e ≤ n := by
    have : (q - 1) * n ≤ q * n := Nat.mul_le_mul_right n (Nat.sub_le q 1)
    have : q * e ≤ q * n := hqe.trans this
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hdenom := qary_johnson_denom_ge (ι := ι) hq hε hρ heρ
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 * q * ε ^ 2 := by positivity
  have hltR :
      (((q - 1) * n * (n - d) : ℕ) : ℝ) < (((q - 1) * (n - e) ^ 2 + e ^ 2 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub hdn, Nat.cast_sub hen]
    linarith
  exact ⟨hqe, by exact_mod_cast hltR⟩

/-- **The real-valued `q`-ary Johnson bound** [Johnson1962], [GuruswamiRudraSudan2019]: over an
alphabet of `q ≥ 2` letters, a code `C` of length `n ≥ 1` and minimum distance at least `d`
(relative distance `δ = d / n`) is `(ρ, L)`-list-decodable for every `ε > 0` and
`ρ ≤ J_q(δ) - ε`, with constant list size `L = ⌊(q - 1) * δ / (q * ε ^ 2)⌋₊`.

In particular, since `(q - 1) * δ / q ≤ 1 ≤ n`, the list size satisfies
`L ≤ ⌊1 / ε ^ 2⌋₊ ≤ ⌊n / ε ^ 2⌋₊`. -/
theorem isListDecodable_of_le_johnsonRadius [Nonempty ι] [Fintype α]
    (hq : 2 ≤ Fintype.card α) {C : Set (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist C) {ε ρ : ℝ} (hε : 0 < ε)
    (hρ : ρ ≤ johnsonRadius (Fintype.card α) ((d : ℝ) / Fintype.card ι) - ε) :
    IsListDecodable C ρ
      ⌊((Fintype.card α : ℝ) - 1) * ((d : ℝ) / Fintype.card ι) /
          (Fintype.card α * ε ^ 2)⌋₊ := by
  set n : ℕ := Fintype.card ι
  set q : ℕ := Fintype.card α
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  set δ : ℝ := (d : ℝ) / n
  set L : ℕ := ⌊((q : ℝ) - 1) * δ / (q * ε ^ 2)⌋₊
  intro w
  by_cases hneg : ρ < 0
  · have hempty : {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * n} = ∅ := by
      ext c
      simp only [Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro _
      have h1 : ρ * n < 0 := mul_neg_of_neg_of_pos hneg hnR
      linarith [Nat.cast_nonneg (α := ℝ) (hammingDist c w)]
    rw [show {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} = ∅ from hempty,
      Set.encard_empty]
    exact zero_le
  push Not at hneg
  rcases lt_or_ge n d with hnd | hdn
  · -- When `n < d`, `minDist C ≥ d` forces `C` to have at most one codeword.
    have hsub : C.Subsingleton := by
      by_contra hnontriv
      have hnontriv' : C.Nontrivial := Set.not_subsingleton_iff.1 hnontriv
      have hle : (d : ℕ∞) ≤ n := hd.trans (minDist_le_card hnontriv')
      exact absurd (Nat.cast_le.1 hle) (not_le_of_gt hnd)
    have hδ1 : 1 ≤ δ := (one_le_div hnR).2 (by exact_mod_cast hnd.le)
    have hε_le : ε ≤ 1 - 1 / (q : ℝ) := by
      linarith [johnsonRadius_le_one_sub_inv (δ := δ) hqR]
    have hθ : 0 < 1 - 1 / (q : ℝ) := sub_pos.2 ((div_lt_one (zero_lt_one.trans hqR)).2 hqR)
    have hθ1 : 1 - 1 / (q : ℝ) ≤ 1 := sub_le_self 1 (by positivity)
    have hq0 : (0 : ℝ) < q := by positivity
    have hL1 : 1 ≤ ((q : ℝ) - 1) * δ / (q * ε ^ 2) := by
      have hnum : (1 - 1 / (q : ℝ)) ≤ ((q : ℝ) - 1) * δ / q := by
        have h1 : (1 - 1 / (q : ℝ)) * 1 ≤ (1 - 1 / (q : ℝ)) * δ :=
          mul_le_mul_of_nonneg_left hδ1 hθ.le
        have h2 : (1 - 1 / (q : ℝ)) * δ = ((q : ℝ) - 1) * δ / q := by
          field_simp [hq0.ne']
        linarith
      have hden : ε ^ 2 ≤ 1 - 1 / (q : ℝ) := by
        have : ε ^ 2 ≤ (1 - 1 / (q : ℝ)) ^ 2 := pow_le_pow_left₀ hε.le hε_le 2
        nlinarith
      calc (1 : ℝ) ≤ (1 - 1 / (q : ℝ)) / ε ^ 2 := (one_le_div (sq_pos_of_pos hε)).2 hden
        _ ≤ (((q : ℝ) - 1) * δ / q) / ε ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg ε)
        _ = ((q : ℝ) - 1) * δ / (q * ε ^ 2) := by ring
    have hL : 1 ≤ L := Nat.floor_pos.2 hL1
    have henc1 : {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * n}.encard ≤ 1 :=
      Set.encard_le_one_iff.2 fun _ _ ha hb => hsub ha.1 hb.1
    exact henc1.trans (by exact_mod_cast hL)
  -- Non-degenerate regime `d ≤ n`: apply `Code.card_filter_hammingDist_le_mul_le_of_mul_le`.
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  refine encard_le_coe_of_finset_card_le fun B hB => ?_
  set e : ℕ := ⌊ρ * n⌋₊
  have heρ : (e : ℝ) ≤ ρ * n := Nat.floor_le (mul_nonneg hneg hnR.le)
  have hhyp := qary_johnson_nat_hypotheses (ι := ι) hq hdn hε hρ heρ
  have hdB : (d : ℕ∞) ≤ minDist (B : Set (ι → α)) :=
    hd.trans (minDist_anti (hB.trans (Set.sep_subset _ _)))
  have hjohn := card_filter_hammingDist_le_mul_le_of_mul_le hdB w hhyp.1
  have hBfilt : {c ∈ B | hammingDist c w ≤ e} = B := by
    ext c
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hcB
    have hdist : (hammingDist c w : ℝ) ≤ ρ * n := (hB hcB).2
    exact Nat.le_floor hdist
  rw [hBfilt] at hjohn
  have hen : e ≤ n := by
    have : (q - 1) * n ≤ q * n := Nat.mul_le_mul_right n (Nat.sub_le q 1)
    exact Nat.le_of_mul_le_mul_left (hhyp.1.trans this) (by omega)
  have hdenom := qary_johnson_denom_ge (ι := ι) hq hε hρ heρ
  have hjohnR : (#B : ℝ) * ((n : ℝ) ^ 2 * q * ε ^ 2) ≤ ((q : ℝ) - 1) * n * d := by
    have h1 : ((#B * ((q - 1) * (n - e) ^ 2 + e ^ 2 - (q - 1) * n * (n - d)) : ℕ) : ℝ) ≤
        (((q - 1) * n * d : ℕ) : ℝ) := by
      exact_mod_cast hjohn
    have hle : ((q - 1) * n * (n - d)) ≤ (q - 1) * (n - e) ^ 2 + e ^ 2 := hhyp.2.le
    push_cast [Nat.cast_sub hle, Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_sub hdn, Nat.cast_sub hen] at h1
    have hmul : (#B : ℝ) * ((n : ℝ) ^ 2 * q * ε ^ 2) ≤
        (#B : ℝ) * (((q : ℝ) - 1) * ((n : ℝ) - e) ^ 2 + (e : ℝ) ^ 2 -
          ((q : ℝ) - 1) * n * ((n : ℝ) - d)) :=
      mul_le_mul_of_nonneg_left hdenom (Nat.cast_nonneg _)
    exact hmul.trans h1
  have hB_le : (#B : ℝ) ≤ ((q : ℝ) - 1) * δ / (q * ε ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have hdn_eq : ((q : ℝ) - 1) * δ * n ^ 2 = ((q : ℝ) - 1) * n * d := by
      dsimp only [δ]
      field_simp
    have hmul : (#B : ℝ) * (q * ε ^ 2) * n ^ 2 ≤ ((q : ℝ) - 1) * δ * n ^ 2 := by
      rw [hdn_eq]
      nlinarith [hjohnR]
    exact le_of_mul_le_mul_right hmul (sq_pos_of_pos hnR)
  exact Nat.le_floor hB_le

/-- **The real-valued binary Johnson bound** [Johnson1962], [GuruswamiRudraSudan2019]: a binary code
`C : Set (ι → Bool)` of length `n ≥ 1` and minimum distance at least `d` (`δ = d / n`) is
`(ρ, L)`-list-decodable for every `ε > 0` and `ρ ≤ (1 - √(1 - 2 * δ)) / 2 - ε`, with list size
`L = ⌊δ / (2 * ε ^ 2)⌋₊`. -/
theorem isListDecodable_binary_of_le_johnsonRadius [Nonempty ι] {C : Set (ι → Bool)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist C) {ε ρ : ℝ} (hε : 0 < ε)
    (hρ : ρ ≤ (1 - Real.sqrt (1 - 2 * ((d : ℝ) / Fintype.card ι))) / 2 - ε) :
    IsListDecodable C ρ ⌊((d : ℝ) / Fintype.card ι) / (2 * ε ^ 2)⌋₊ := by
  have h := isListDecodable_of_le_johnsonRadius (α := Bool) (by decide) hd hε
    (by simpa [Fintype.card_bool, johnsonRadius_two] using hρ)
  simpa only [Fintype.card_bool, Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using h

/-- **The alphabet-free (`q → ∞`) real Johnson bound** [Johnson1962], [GuruswamiRudraSudan2019]:
whatever the alphabet `α`, a code `C : Set (ι → α)` of length `n ≥ 1` and minimum distance at
least `d` (`δ = d / n`) is `(ρ, L)`-list-decodable for every `ε > 0` and `ρ ≤ 1 - √(1 - δ) - ε`,
with constant list size `L = ⌊δ / ε ^ 2⌋₊`. -/
theorem isListDecodable_of_le_johnsonRadiusLimit [Nonempty ι] {C : Set (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist C) {ε ρ : ℝ} (hε : 0 < ε)
    (hρ : ρ ≤ johnsonRadiusLimit ((d : ℝ) / Fintype.card ι) - ε) :
    IsListDecodable C ρ ⌊((d : ℝ) / Fintype.card ι) / ε ^ 2⌋₊ := by
  set n : ℕ := Fintype.card ι
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  set δ : ℝ := (d : ℝ) / n
  set L : ℕ := ⌊δ / ε ^ 2⌋₊
  intro w
  by_cases hneg : ρ < 0
  · have hempty : {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * n} = ∅ := by
      ext c
      simp only [Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro _
      have h1 : ρ * n < 0 := mul_neg_of_neg_of_pos hneg hnR
      linarith [Nat.cast_nonneg (α := ℝ) (hammingDist c w)]
    rw [show {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} = ∅ from hempty,
      Set.encard_empty]
    exact zero_le
  push Not at hneg
  rcases lt_or_ge n d with hnd | hdn
  · have hsub : C.Subsingleton := by
      by_contra hnontriv
      have hnontriv' : C.Nontrivial := Set.not_subsingleton_iff.1 hnontriv
      have hle : (d : ℕ∞) ≤ n := hd.trans (minDist_le_card hnontriv')
      exact absurd (Nat.cast_le.1 hle) (not_le_of_gt hnd)
    have hδ1 : 1 ≤ δ := (one_le_div hnR).2 (by exact_mod_cast hnd.le)
    have hJL : johnsonRadiusLimit δ ≤ 1 := by
      rw [johnsonRadiusLimit]
      linarith [Real.sqrt_nonneg (1 - δ)]
    have hε1 : ε ≤ 1 := by linarith
    have hL1 : 1 ≤ δ / ε ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hε), one_mul]
      exact (pow_le_one₀ hε.le hε1).trans hδ1
    have henc1 : {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * n}.encard ≤ 1 :=
      Set.encard_le_one_iff.2 fun _ _ ha hb => hsub ha.1 hb.1
    exact henc1.trans (by exact_mod_cast Nat.floor_pos.2 hL1)
  refine encard_le_coe_of_finset_card_le fun B hB => ?_
  set e : ℕ := ⌊ρ * n⌋₊
  have heρ : (e : ℝ) ≤ ρ * n := Nat.floor_le (mul_nonneg hneg hnR.le)
  have h1ρ : ρ < 1 := by
    have hJL : johnsonRadiusLimit δ ≤ 1 := by
      rw [johnsonRadiusLimit]
      linarith [Real.sqrt_nonneg (1 - δ)]
    linarith
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
    have hsq : s ^ 2 + 2 * s * ε + ε ^ 2 ≤ (1 - x) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h1x 2
      linarith
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
  have hBfilt : {c ∈ B | hammingDist c w ≤ e} = B := by
    ext c
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hcB
    exact Nat.le_floor (hB hcB).2
  rw [hBfilt] at hjohn
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 * ε ^ 2 := by positivity
  have hle_N : n * (n - d) ≤ (n - e) ^ 2 := by
    have h1 : (0 : ℝ) ≤ ((n - e : ℕ) : ℝ) ^ 2 - (n : ℝ) * ((n - d : ℕ) : ℝ) := by
      rw [Nat.cast_sub hen, Nat.cast_sub hdn]
      linarith
    have h2 : (((n * (n - d) : ℕ) : ℝ)) ≤ (((n - e) ^ 2 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hen, Nat.cast_sub hdn]
      linarith
    exact_mod_cast h2
  have hjohnR : (#B : ℝ) * ((n : ℝ) ^ 2 * ε ^ 2) ≤ (n : ℝ) * (d - e : ℕ) := by
    have h1 : ((#B * ((n - e) ^ 2 - n * (n - d)) : ℕ) : ℝ) ≤ ((n * (d - e) : ℕ) : ℝ) := by
      exact_mod_cast hjohn
    push_cast [Nat.cast_sub hle_N, Nat.cast_sub hen, Nat.cast_sub hdn] at h1
    have hmul : (#B : ℝ) * ((n : ℝ) ^ 2 * ε ^ 2) ≤
        (#B : ℝ) * (((n : ℝ) - e) ^ 2 - (n : ℝ) * ((n : ℝ) - d)) :=
      mul_le_mul_of_nonneg_left hdenom (Nat.cast_nonneg _)
    exact hmul.trans h1
  have hrhs : (n : ℝ) * ((d - e : ℕ) : ℝ) ≤ (n : ℝ) * d := by
    gcongr
    exact Nat.sub_le d e
  have hB_le : (#B : ℝ) ≤ δ / ε ^ 2 := by
    have hmul : (#B : ℝ) * ε ^ 2 ≤ δ := by
      have : (#B : ℝ) * ((n : ℝ) ^ 2 * ε ^ 2) ≤ (n : ℝ) * d := hjohnR.trans hrhs
      have hdn_eq : δ * (n : ℝ) ^ 2 = (n : ℝ) * d := by dsimp only [δ]; field_simp
      rw [← hdn_eq] at this
      have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
      nlinarith
    exact (le_div_iff₀ (sq_pos_of_pos hε)).2 hmul
  exact Nat.le_floor hB_le

/-- **List decodability of Reed–Solomon codes up to the Guruswami–Sudan / Johnson radius**
[GuruswamiSudan1999], [GuruswamiRudraSudan2019]: with `n ≥ 1` distinct evaluation points `α`, a
Reed–Solomon code of degree bound `1 ≤ k ≤ n` over any field `F` has minimum distance at least
`d = n - k + 1`, so for every `ε > 0` it is `(ρ, L)`-list-decodable up to
`ρ ≤ 1 - √((k - 1) / n) - ε` with list size `L = ⌊(1 - (k - 1) / n) / ε ^ 2⌋₊`
(in particular for every `ρ ≤ 1 - √(k / n) - ε`). -/
theorem isListDecodable_reedSolomon [Nonempty ι] {F : Type*} [Field F] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    {ε ρ : ℝ} (hε : 0 < ε)
    (hρ : ρ ≤ 1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card ι) - ε) :
    IsListDecodable (reedSolomon α k : Set (ι → F)) ρ
      ⌊(1 - ((k - 1 : ℕ) : ℝ) / Fintype.card ι) / ε ^ 2⌋₊ := by
  set n : ℕ := Fintype.card ι
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  have hd_eq : ((n - k + 1 : ℕ) : ℝ) / n = 1 - ((k - 1 : ℕ) : ℝ) / n := by
    have hle : k - 1 ≤ n := by omega
    have hcast : ((n - k + 1 : ℕ) : ℝ) = (n : ℝ) - ((k - 1 : ℕ) : ℝ) := by
      have : n - k + 1 = n - (k - 1) := by omega
      rw [this, Nat.cast_sub hle]
    rw [hcast, sub_div, div_self hnR.ne']
  have h1sub : 1 - (((n - k + 1 : ℕ) : ℝ) / n) = ((k - 1 : ℕ) : ℝ) / n := by
    rw [hd_eq]
    ring
  have hρ' : ρ ≤ johnsonRadiusLimit (((n - k + 1 : ℕ) : ℝ) / n) - ε := by
    rw [johnsonRadiusLimit, h1sub]
    exact hρ
  have h := isListDecodable_of_le_johnsonRadiusLimit (le_minDist_reedSolomon hα k) hε hρ'
  convert h using 3
  exact hd_eq.symm

end JohnsonBounds

/-! ### The Elias–Bassalygo rate bound -/

section EliasBassalygoRate

variable {ι α : Type*}

private theorem exp_mul_qaryEntropy_le_succ_mul_choose_mul_pow {q n e : ℕ}
    (hq : 2 ≤ q) (hen : e ≤ n) :
    Real.exp (n * Real.qaryEntropy q ((e : ℝ) / n)) ≤
      (n + 1 : ℝ) * ((n.choose e : ℝ) * ((q : ℝ) - 1) ^ e) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · obtain rfl : e = 0 := by omega
    simp
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hqcast : ((q : ℤ) - 1 : ℤ) = ((q - 1 : ℕ) : ℤ) := by omega
  have hqeq : (((q : ℤ) - 1 : ℤ) : ℝ) = (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    push_cast
    ring
  have hbin := Cslib.exp_mul_binEntropy_le_succ_mul_choose hen
  have hpow : Real.exp ((e : ℝ) * Real.log ((q : ℝ) - 1)) = ((q : ℝ) - 1) ^ e := by
    rw [Real.exp_nat_mul, Real.exp_log hq1]
  have hqent :
      (n : ℝ) * Real.qaryEntropy q ((e : ℝ) / n) =
        (n : ℝ) * Real.binEntropy ((e : ℝ) / n) + (e : ℝ) * Real.log ((q : ℝ) - 1) := by
    rw [Real.qaryEntropy, hqeq]
    field_simp [hnR.ne']
    ring
  rw [hqent, Real.exp_add, hpow]
  calc Real.exp ((n : ℝ) * Real.binEntropy ((e : ℝ) / n)) * ((q : ℝ) - 1) ^ e
      ≤ ((n + 1 : ℝ) * n.choose e) * ((q : ℝ) - 1) ^ e :=
        mul_le_mul_of_nonneg_right hbin (pow_nonneg hq1.le _)
    _ = (n + 1 : ℝ) * ((n.choose e : ℝ) * ((q : ℝ) - 1) ^ e) := by ring

private theorem qaryEntropy_le_log {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.qaryEntropy q p ≤ Real.log q := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  rcases hp0.eq_or_lt with rfl | hp0'
  · simp [Real.log_nonneg (by linarith : (1 : ℝ) ≤ q)]
  rcases hp1.eq_or_lt with rfl | hp1'
  · simp only [Real.qaryEntropy_one]
    have hcast : (((q : ℤ) - 1 : ℤ) : ℝ) = (q : ℝ) - 1 := by push_cast; ring
    rw [hcast]
    exact Real.log_le_log hq1 (by linarith)
  have h1p : 0 < 1 - p := sub_pos.2 hp1'
  have hl1 : Real.log (((q : ℝ) - 1) / (q * p)) ≤ ((q : ℝ) - 1) / (q * p) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hl2 : Real.log (1 / (q * (1 - p))) ≤ 1 / (q * (1 - p)) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hcomb : p * Real.log (((q : ℝ) - 1) / (q * p)) +
      (1 - p) * Real.log (1 / (q * (1 - p))) ≤ 0 := by
    have hmul1 := mul_le_mul_of_nonneg_left hl1 hp0'.le
    have hmul2 := mul_le_mul_of_nonneg_left hl2 h1p.le
    have hid1 : p * (((q : ℝ) - 1) / (q * p) - 1) = ((q : ℝ) - 1) / q - p := by
      field_simp [hp0'.ne', hq0.ne']
    have hid2 : (1 - p) * (1 / (q * (1 - p)) - 1) = 1 / q - (1 - p) := by
      field_simp [h1p.ne', hq0.ne']
    rw [hid1] at hmul1
    rw [hid2] at hmul2
    have hzero : (((q : ℝ) - 1) / q - p) + (1 / q - (1 - p)) = 0 := by
      field_simp [hq0.ne']
      ring
    linarith
  have hcast : (((q : ℤ) - 1 : ℤ) : ℝ) = (q : ℝ) - 1 := by push_cast; ring
  have hrewrite : Real.qaryEntropy q p - Real.log q =
      p * Real.log (((q : ℝ) - 1) / (q * p)) + (1 - p) * Real.log (1 / (q * (1 - p))) := by
    rw [Real.qaryEntropy, hcast, Real.binEntropy, Real.log_inv, Real.log_inv,
      Real.log_div hq1.ne' (by positivity), Real.log_mul hq0.ne' hp0'.ne',
      Real.log_div one_ne_zero (by positivity), Real.log_mul hq0.ne' h1p.ne', Real.log_one]
    ring
  linarith

/-- **Finite Elias–Bassalygo rate bound** [Bassalygo1965], [GuruswamiRudraSudan2019]: for a code
`C` of length `n ≥ 1` and minimum distance at least `d ≤ n` over an alphabet of `q ≥ 2` letters,
any integer radius `e` with `e / n ≤ J_q(d / n) - ε` (`ε > 0`) satisfies
`rate C ≤ 1 - H_q(e / n) / log q + log_q ((q - 1) * n * d * (n + 1)) / n`. -/
theorem rate_le_of_lt_johnsonRadius [Fintype ι] [Nonempty ι] [Fintype α] [DecidableEq α]
    (hq : 2 ≤ Fintype.card α) {C : Finset (ι → α)} {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (hdn : d ≤ Fintype.card ι)
    {ε : ℝ} (hε : 0 < ε)
    (he : (e : ℝ) / Fintype.card ι ≤
      johnsonRadius (Fintype.card α) ((d : ℝ) / Fintype.card ι) - ε) :
    rate (C : Set (ι → α)) ≤
      1 - Real.qaryEntropy (Fintype.card α) ((e : ℝ) / Fintype.card ι) /
          Real.log (Fintype.card α) +
        Real.logb (Fintype.card α)
            (((Fintype.card α : ℝ) - 1) * Fintype.card ι * d * (Fintype.card ι + 1)) /
          Fintype.card ι := by
  set n : ℕ := Fintype.card ι
  set q : ℕ := Fintype.card α
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have heρ : (e : ℝ) ≤ (johnsonRadius q ((d : ℝ) / n) - ε) * n := (div_le_iff₀ hnR).1 he
  have hhyp := qary_johnson_nat_hypotheses (ι := ι) hq hdn hε le_rfl heρ
  have hen : e ≤ n := by
    have : (q - 1) * n ≤ q * n := Nat.mul_le_mul_right n (Nat.sub_le q 1)
    exact Nat.le_of_mul_le_mul_left (hhyp.1.trans this) (by omega)
  have hd0 : 0 < d := by
    by_contra hd0'
    obtain rfl : d = 0 := by omega
    have hzero : johnsonRadius q (((0 : ℕ) : ℝ) / n) = 0 := by simp
    rw [hzero, zero_sub] at he
    have : (0 : ℝ) ≤ ((e : ℕ) : ℝ) / n := by positivity
    linarith
  have hC0_or := Nat.eq_zero_or_pos #C
  rcases hC0_or with hC0 | hCpos
  · have hrate0 : rate (C : Set (ι → α)) = 0 := by
      simp [rate, hC0]
    rw [hrate0]
    have h1 : 0 ≤ 1 - Real.qaryEntropy q ((e : ℝ) / n) / Real.log q := by
      rw [sub_nonneg, div_le_one hlogq]
      exact qaryEntropy_le_log hq (by positivity) ((div_le_one hnR).2 (by exact_mod_cast hen))
    have hfac : 1 ≤ ((q : ℝ) - 1) * n * d * (n + 1) := by
      have hqR2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
      have hq1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by linarith
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
      have hn2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have h12 : 1 ≤ ((q : ℝ) - 1) * n := one_le_mul_of_one_le_of_one_le hq1 hn1
      have h123 : 1 ≤ ((q : ℝ) - 1) * n * d := one_le_mul_of_one_le_of_one_le h12 hd1
      exact one_le_mul_of_one_le_of_one_le h123 hn2
    have hlog_nn : 0 ≤ Real.logb q (((q : ℝ) - 1) * n * d * (n + 1)) / n :=
      div_nonneg (Real.logb_nonneg hqR hfac) hnR.le
    linarith
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  have heb := card_mul_sum_choose_le hd hhyp.1 hhyp.2
  set V : ℕ := ∑ j ∈ range (e + 1), n.choose j * (q - 1) ^ j
  have hV_term : ((n.choose e : ℝ) * ((q : ℝ) - 1) ^ e) ≤ (V : ℝ) := by
    have hsub : n.choose e * (q - 1) ^ e ≤ V :=
      Finset.single_le_sum (f := fun j => n.choose j * (q - 1) ^ j)
        (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.lt_succ_self e))
    have hcast : ((n.choose e * (q - 1) ^ e : ℕ) : ℝ) ≤ (V : ℝ) := by exact_mod_cast hsub
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at hcast
    exact hcast
  have hvol : Real.exp (n * Real.qaryEntropy q ((e : ℝ) / n)) ≤ (n + 1 : ℝ) * V :=
    (exp_mul_qaryEntropy_le_succ_mul_choose_mul_pow hq hen).trans
      (mul_le_mul_of_nonneg_left hV_term (by positivity))
  have hcomb : (#C : ℝ) * Real.exp (n * Real.qaryEntropy q ((e : ℝ) / n)) ≤
      (q : ℝ) ^ n * (((q : ℝ) - 1) * n * d * (n + 1)) := by
    have hebR : ((#C * V : ℕ) : ℝ) ≤ ((q ^ n * ((q - 1) * n * d) : ℕ) : ℝ) := by
      exact_mod_cast heb
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at hebR
    calc (#C : ℝ) * Real.exp (n * Real.qaryEntropy q ((e : ℝ) / n))
        ≤ (#C : ℝ) * ((n + 1 : ℝ) * V) :=
          mul_le_mul_of_nonneg_left hvol (Nat.cast_nonneg _)
      _ = ((#C : ℝ) * V) * (n + 1 : ℝ) := by ring
      _ ≤ ((q : ℝ) ^ n * (((q : ℝ) - 1) * n * d)) * (n + 1 : ℝ) :=
          mul_le_mul_of_nonneg_right hebR (by positivity)
      _ = (q : ℝ) ^ n * (((q : ℝ) - 1) * n * d * (n + 1)) := by ring
  have hCR : (0 : ℝ) < #C := Nat.cast_pos.2 hCpos
  have hqR2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hlog :
      Real.logb q (#C : ℝ) +
          (n : ℝ) * Real.qaryEntropy q ((e : ℝ) / n) / Real.log q ≤
        n + Real.logb q (((q : ℝ) - 1) * n * d * (n + 1)) := by
    have h1 := Real.logb_le_logb_of_le hqR (by positivity) hcomb
    rw [Real.logb_mul hCR.ne' (Real.exp_pos _).ne',
      Real.logb_mul (pow_ne_zero n (by positivity)) (by positivity),
      Real.logb_self_pow (zero_lt_one.trans hqR) hqR.ne'] at h1
    have hexp : Real.logb q (Real.exp (n * Real.qaryEntropy q ((e : ℝ) / n))) =
        (n : ℝ) * Real.qaryEntropy q ((e : ℝ) / n) / Real.log q := by
      rw [Real.logb, Real.log_exp]
    linarith [h1, hexp]
  have hrate_eq : rate (C : Set (ι → α)) = Real.logb q (#C : ℝ) / n := by
    simp only [rate, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    rfl
  rw [hrate_eq]
  have hdiv := div_le_div_of_nonneg_right hlog hnR.le
  rw [add_div, add_div, div_self hnR.ne'] at hdiv
  have hent_div : (n : ℝ) * Real.qaryEntropy q ((e : ℝ) / n) / Real.log q / n =
      Real.qaryEntropy q ((e : ℝ) / n) / Real.log q := by
    field_simp [hnR.ne']
  rw [hent_div] at hdiv
  linarith

/-- **The asymptotic Elias–Bassalygo bound** [Bassalygo1965], [GuruswamiRudraSudan2019]: for any
family of codes `C s` over `q ≥ 2` letters whose block lengths `n_s = |ιs s|` tend to infinity along
a filter `l` and whose relative minimum distances are at least `δ` (`0 ≤ δ ≤ 1 - 1 / q`),
`rate (C s) ≤ 1 - H_q(J_q(δ)) / log q + ε` holds eventually along `l` for every `ε > 0`. -/
theorem eventually_rate_le_one_sub_qaryEntropy_johnsonRadius
    {σ : Type*} {ιs : σ → Type*} [∀ s, Fintype (ιs s)] [Fintype α] [DecidableEq α] [Nontrivial α]
    {l : Filter σ} {C : ∀ s, Finset (ιs s → α)} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : (Fintype.card α : ℝ) * δ ≤ Fintype.card α - 1)
    (hC : ∀ s, ∀ x ∈ C s, ∀ y ∈ C s, x ≠ y → δ * Fintype.card (ιs s) ≤ hammingDist x y)
    (hn : Tendsto (fun s => Fintype.card (ιs s)) l atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in l, rate (C s : Set (ιs s → α)) ≤
      1 - Real.qaryEntropy (Fintype.card α) (johnsonRadius (Fintype.card α) δ) /
        Real.log (Fintype.card α) + ε := by
  classical
  set q : ℕ := Fintype.card α
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have hnR : Tendsto (fun s => (Fintype.card (ιs s) : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  rcases hδ0.eq_or_lt with rfl | hδpos
  · filter_upwards [hn.eventually_ge_atTop 1] with s hs1
    have hnpos : (0 : ℝ) < Fintype.card (ιs s) := Nat.cast_pos.2 hs1
    have htriv : rate (C s : Set (ιs s → α)) ≤ 1 := by
      simp only [rate, Nat.card_coe_set_eq, Set.ncard_coe_finset]
      rcases Nat.eq_zero_or_pos #(C s) with h0 | h0
      · simp [h0]
      have hle : (#(C s) : ℝ) ≤ (q : ℝ) ^ Fintype.card (ιs s) := by
        have := card_le_univ (C s)
        rw [Fintype.card_fun] at this
        exact_mod_cast this
      calc Real.logb q #(C s) / Fintype.card (ιs s)
          ≤ Real.logb q ((q : ℝ) ^ Fintype.card (ιs s)) / Fintype.card (ιs s) :=
            div_le_div_of_nonneg_right (Real.logb_le_logb_of_le hqR (by exact_mod_cast h0) hle)
              hnpos.le
        _ = 1 := by
            rw [Real.logb_self_pow (zero_lt_one.trans hqR) hqR.ne', div_self hnpos.ne']
    simpa [johnsonRadius_zero_right] using htriv.trans (by linarith)
  have hδθ : δ ≤ 1 - 1 / (q : ℝ) := by
    have hq0 : (0 : ℝ) < q := by positivity
    rw [le_sub_iff_add_le, ← mul_le_mul_iff_of_pos_left hq0]
    calc (q : ℝ) * (δ + 1 / q) = q * δ + 1 := by field_simp [hq0.ne']
      _ ≤ q := by linarith
      _ = q * 1 := by ring
  set J : ℝ := johnsonRadius q δ
  have hJpos : 0 < J := by
    have hq1 : 0 < (q : ℝ) - 1 := by linarith
    have hθ : 0 < 1 - 1 / (q : ℝ) := sub_pos.2 ((div_lt_one (zero_lt_one.trans hqR)).2 hqR)
    have hlt : 1 - (q : ℝ) * δ / ((q : ℝ) - 1) < 1 := by
      have : 0 < (q : ℝ) * δ / ((q : ℝ) - 1) := by positivity
      linarith
    have hsqrt : Real.sqrt (1 - (q : ℝ) * δ / ((q : ℝ) - 1)) < 1 := by
      rcases le_or_gt (1 - (q : ℝ) * δ / ((q : ℝ) - 1)) 0 with hle | hpos
      · rw [Real.sqrt_eq_zero_of_nonpos hle]
        exact zero_lt_one
      · have hsq : Real.sqrt (1 - (q : ℝ) * δ / ((q : ℝ) - 1)) ^ 2 =
            1 - (q : ℝ) * δ / ((q : ℝ) - 1) := Real.sq_sqrt hpos.le
        have hnn : 0 ≤ Real.sqrt (1 - (q : ℝ) * δ / ((q : ℝ) - 1)) := Real.sqrt_nonneg _
        nlinarith
    exact mul_pos hθ (sub_pos.2 hsqrt)
  -- Use continuity of `Real.qaryEntropy q` at `J` to keep `H_q(e/n)` within `ε / 2 * log q`.
  have hcont := (Real.qaryEntropy_continuous (q := q)).tendsto J
  rw [Metric.tendsto_nhds_nhds] at hcont
  obtain ⟨η₀, hη₀pos, hη₀⟩ := hcont (ε / 2 * Real.log q) (by positivity)
  set η : ℝ := min (η₀ / 2) J
  have hηpos : 0 < η := lt_min (half_pos hη₀pos) hJpos
  have hη_le_η₀ : η < η₀ := (min_le_left _ _).trans_lt (half_lt_self hη₀pos)
  have hη_le_J : η ≤ J := min_le_right _ _
  have h_n1 : ∀ᶠ s in l, 1 ≤ Fintype.card (ιs s) := hn.eventually_ge_atTop 1
  have h_nη : ∀ᶠ s in l, 2 / η ≤ (Fintype.card (ιs s) : ℝ) := hnR.eventually_ge_atTop _
  have h_nconst :
      ∀ᶠ s in l, Real.log (2 * q) ≤ ε / 4 * Real.log q * (Fintype.card (ιs s) : ℝ) :=
    (hnR.eventually_ge_atTop (Real.log (2 * q) / (ε / 4 * Real.log q))).mono fun s hs => by
      have h1 : Real.log (2 * q) ≤ (Fintype.card (ιs s) : ℝ) * (ε / 4 * Real.log q) :=
        (div_le_iff₀ (by positivity)).1 hs
      linarith
  have h_nlog :
      ∀ᶠ s in l, Real.log (Fintype.card (ιs s)) ≤
        ε / 12 * Real.log q * (Fintype.card (ιs s) : ℝ) := by
    have := (Real.isLittleO_log_id_atTop.bound (c := ε / 12 * Real.log q) (by positivity))
    filter_upwards [hnR.eventually this, hnR.eventually_ge_atTop 1] with s hs hs1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (Real.log_nonneg hs1),
      abs_of_nonneg (by linarith)] at hs
    exact hs
  filter_upwards [h_n1, h_nη, h_nconst, h_nlog] with s hs1 hsη hsconst hslog
  have : Nonempty (ιs s) := Fintype.card_pos_iff.1 hs1
  set n : ℕ := Fintype.card (ιs s)
  have hn0 : 0 < n := hs1
  have hnR' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  set d : ℕ := ⌈δ * n⌉₊
  have hδlt1 : δ < 1 := by
    have : 0 < 1 / (q : ℝ) := by positivity
    linarith
  have hdn : d ≤ n := Nat.ceil_le.2 (by nlinarith)
  have hdmin : (d : ℕ∞) ≤ minDist (C s : Set (ιs s → α)) := by
    rw [le_minDist_iff]
    intro x hx y hy hxy
    exact_mod_cast Nat.ceil_le.2 (hC s x hx y hy hxy)
  have hδd : δ ≤ (d : ℝ) / n := (le_div_iff₀ hnR').2 (Nat.le_ceil _)
  have hJd : J ≤ johnsonRadius q ((d : ℝ) / n) := johnsonRadius_mono_right hqR hδd
  set e : ℕ := ⌊(J - η / 2) * n⌋₊
  have hJη0 : 0 ≤ J - η / 2 := by linarith
  have he_le : (e : ℝ) ≤ (J - η / 2) * n := Nat.floor_le (mul_nonneg hJη0 hnR'.le)
  have he_lt : (J - η / 2) * n - 1 < e := sub_lt_iff_lt_add.2 (Nat.lt_floor_add_one _)
  have h1_le_halfηn : 1 ≤ η / 2 * n := by
    have : 2 / η ≤ n := hsη
    have : 1 ≤ n * (η / 2) := by
      have := mul_le_mul_of_nonneg_left hsη (by positivity : 0 ≤ η / 2)
      have hsimp : η / 2 * (2 / η) = 1 := by field_simp [hηpos.ne']
      linarith
    linarith
  have he_lower : J - η ≤ (e : ℝ) / n := by
    rw [le_div_iff₀ hnR']
    linarith
  have he_upper : (e : ℝ) / n ≤ J - η / 2 := (div_le_iff₀ hnR').2 he_le
  have he_radius : (e : ℝ) / n ≤ johnsonRadius q ((d : ℝ) / n) - η / 2 := by linarith
  have hfinite := rate_le_of_lt_johnsonRadius (C := C s) hq hdmin hdn (half_pos hηpos) he_radius
  have hdistJ : dist ((e : ℝ) / n) J < η₀ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hent : |Real.qaryEntropy q ((e : ℝ) / n) - Real.qaryEntropy q J| < ε / 2 * Real.log q := by
    simpa only [Real.dist_eq] using hη₀ hdistJ
  have hent' :
      1 - Real.qaryEntropy q ((e : ℝ) / n) / Real.log q ≤
        1 - Real.qaryEntropy q J / Real.log q + ε / 2 := by
    have hlt : Real.qaryEntropy q J - Real.qaryEntropy q ((e : ℝ) / n) ≤ ε / 2 * Real.log q := by
      linarith [(abs_lt.1 hent).1]
    have hdiv := div_le_div_of_nonneg_right hlt hlogq.le
    rw [mul_div_cancel_right₀ _ hlogq.ne', sub_div] at hdiv
    linarith
  have hpoly :
      ((q : ℝ) - 1) * n * d * (n + 1) ≤ (2 * q) * (n : ℝ) ^ 3 := by
    have hq1_le : (q : ℝ) - 1 ≤ q := by linarith
    have hd_le : (d : ℝ) ≤ n := by exact_mod_cast hdn
    have hn1_le : (n : ℝ) + 1 ≤ 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      linarith
    have hq1_nn : 0 ≤ (q : ℝ) - 1 := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    calc ((q : ℝ) - 1) * n * d * (n + 1)
        ≤ (q : ℝ) * n * n * (2 * n) := by gcongr
      _ = (2 * q) * (n : ℝ) ^ 3 := by ring
  have hpoly_pos : 0 < ((q : ℝ) - 1) * n * d * (n + 1) := by
    have hd0 : 0 < d := by
      rw [Nat.ceil_pos]
      exact mul_pos hδpos hnR'
    have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    positivity
  have htail :
      Real.logb q (((q : ℝ) - 1) * n * d * (n + 1)) / n ≤ ε / 2 := by
    have hlog_le : Real.logb q (((q : ℝ) - 1) * n * d * (n + 1)) ≤
        Real.logb q ((2 * q) * (n : ℝ) ^ 3) :=
      Real.logb_le_logb_of_le hqR hpoly_pos hpoly
    have hlog_eq : Real.logb q ((2 * q) * (n : ℝ) ^ 3) =
        (Real.log (2 * q) + 3 * Real.log n) / Real.log q := by
      rw [Real.logb, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      ring
    have hnum : Real.log (2 * q) + 3 * Real.log n ≤ ε / 2 * Real.log q * n := by linarith
    calc Real.logb q (((q : ℝ) - 1) * n * d * (n + 1)) / n
        ≤ ((Real.log (2 * q) + 3 * Real.log n) / Real.log q) / n := by
          gcongr
          linarith [hlog_le, hlog_eq]
      _ ≤ (ε / 2 * Real.log q * n / Real.log q) / n := by gcongr
      _ = ε / 2 := by field_simp [hlogq.ne', hnR'.ne']
  dsimp only [q, n] at hent' htail ⊢
  linarith

end EliasBassalygoRate

end Cslib.Code
