/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.ApproximateMembership.QuotientFilter.Basic
public import CslibFrontier.Probability.KWiseIndependent.Reduced
public import CslibFrontier.DataStructure.HashFamily.WordRAM.KWise
public import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Probabilistic Analysis of the Two-Stage Quotient Filter

This file establishes the probabilistic guarantees of the canonical quotient filter when
instantiated with:
1. a two-stage $5$-wise independent reduced polynomial hash `quotHash U w₀ n` mapping keys in
   `Fin U` (`U ≤ 2 ^ w₀`) to `b = tableLog (min n (2 ^ w₀))`-bit quotients (`2 ^ b ≥ 8 * n_eff`,
   where `n_eff = min n (2 ^ w₀)`), and
2. an independent multiply-shift hash `remHash U w₀ k` mapping keys in `Fin U` to
   `remBits w₀ k = min w₀ (k + 1)`-bit remainders.

## Main results

* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.card_quotHash_eq_le`: pairwise
  collision bound for the two-stage quotient hash (`≤ 2 / 2 ^ b`).
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.toOuterMeasure_falsePositive_le`:
  for any set `S : Finset (Fin U)` with `#S ≤ n` and any absent key `u ∉ S`, the false-positive
  probability under `filterSeedLaw w₀ n` is at most `(1 / 2 : ℝ≥0∞) ^ k`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.sum_clusterLen_le`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.tsum_clusterLen_le`: for any set
  `S : Finset (Fin U)` with `#S ≤ n` and any key `u : Fin U`, the expected cluster length around
  `quotHash θ u` is at most `290` (`289` on injective top-level seeds plus at most `1` from the
  non-injective top-level event of probability `≤ (n_eff + 1) * n_eff / 2 ^ (3 * b)`).

## References

* [A. Pagh, R. Pagh and S. S. Rao, *An optimal Bloom filter replacement*][PaghPaghRao2005]
* [M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes,
  P. Shetty, R. P. Spillane and E. Zadok, *Don't thrash: how to cache your hash on
  flash*][BenderEtAl2012]
* [A. Pagh, R. Pagh and M. Ružić, *Linear Probing with Constant Independence*][PaghPaghRuzic2009]
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Finset
open Cslib.Probability
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing
open scoped BigOperators ENNReal NNReal

/-! ## Section 1: Two-stage quotient and remainder hash parameters -/

/-- Effective capacity `min n (2 ^ w₀)`: since `#S ≤ U ≤ 2 ^ w₀` for every `S : Finset (Fin U)`,
any valid state of capacity `n` has `#S ≤ effCap w₀ n`. -/
@[expose] def effCap (w₀ n : ℕ) : ℕ :=
  min n (2 ^ w₀)

/-- Quotient bit-width `b = tableLog (effCap w₀ n) = ⌈log₂ max(8 · effCap w₀ n, 8)⌉`. -/
@[expose] def quotBits (w₀ n : ℕ) : ℕ :=
  tableLog (effCap w₀ n)

/-- Remainder bit-width `f = min w₀ (k + 1)`. -/
@[expose] def remBits (w₀ k : ℕ) : ℕ :=
  min w₀ (k + 1)

theorem three_le_quotBits (w₀ n : ℕ) : 3 ≤ quotBits w₀ n :=
  three_le_tableLog (effCap w₀ n)

theorem eight_le_two_pow_quotBits (w₀ n : ℕ) : 8 ≤ 2 ^ quotBits w₀ n :=
  eight_le_tableSize (effCap w₀ n)

theorem eight_mul_effCap_le_two_pow_quotBits (w₀ n : ℕ) :
    8 * effCap w₀ n ≤ 2 ^ quotBits w₀ n :=
  eight_mul_le_tableSize (effCap w₀ n)

theorem effCap_lt_two_pow_quotBits (w₀ n : ℕ) :
    effCap w₀ n < 2 ^ quotBits w₀ n :=
  n_max_lt_tableSize (effCap w₀ n)

theorem card_le_effCap {U w₀ n : ℕ} (hU : U ≤ 2 ^ w₀) {S : Finset (Fin U)} (hS : #S ≤ n) :
    #S ≤ effCap w₀ n :=
  le_min hS ((Finset.card_le_univ S).trans ((Fintype.card_fin U).le.trans hU))

theorem card_lt_two_pow_quotBits {U w₀ n : ℕ} (hU : U ≤ 2 ^ w₀) {S : Finset (Fin U)}
    (hS : #S ≤ n) :
    #S < 2 ^ quotBits w₀ n :=
  lt_of_le_of_lt (card_le_effCap hU hS) (effCap_lt_two_pow_quotBits w₀ n)

/-- Seed type for the two-stage $5$-wise independent quotient hash. -/
abbrev QuotSeed (w₀ n : ℕ) : Type :=
  ReducedPolySeed w₀ (quotBits w₀ n) (quotBits w₀ n) 5

/-- Seed type for the independent multiply-shift remainder hash. -/
abbrev RemSeed (w₀ : ℕ) : Type :=
  Fin (2 ^ (w₀ - 1))

/-- Combined seed type `QuotSeed w₀ n × RemSeed w₀` for the quotient filter. -/
abbrev FilterSeed (w₀ n : ℕ) : Type :=
  QuotSeed w₀ n × RemSeed w₀

/-- Uniform distribution over `FilterSeed w₀ n`. -/
@[expose] noncomputable def filterSeedLaw (w₀ n : ℕ) : PMF (FilterSeed w₀ n) :=
  PMF.uniformOfFintype (FilterSeed w₀ n)

/-- Two-stage $5$-wise independent quotient hash mapping `Fin U` to `Fin (2 ^ quotBits w₀ n)`. -/
@[expose] noncomputable def quotHash (U w₀ n : ℕ) (θ : QuotSeed w₀ n) (u : Fin U) :
    Fin (2 ^ quotBits w₀ n) :=
  reducedPolyHash U w₀ (quotBits w₀ n) (quotBits w₀ n) 5 θ u

/-- Multiply-shift remainder hash mapping `Fin U` to `Fin (2 ^ remBits w₀ k)`. -/
@[expose] def remHash (U w₀ k : ℕ) (γ : RemSeed w₀) (u : Fin U) :
    Fin (2 ^ remBits w₀ k) :=
  multiplyShiftReduced U w₀ (k + 1) γ u

/-! ## Section 2: Pairwise collision and false-positive probability bounds -/

private theorem card_multiplyShiftReduced_mul_le {U w₀ R m : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    (hm : m + 1 ≤ R) {x y : Fin U} (hxy : x ≠ y) :
    #{α : Fin (2 ^ (w₀ - 1)) |
      multiplyShiftReduced U w₀ R α x = multiplyShiftReduced U w₀ R α y} * 2 ^ m ≤
      Fintype.card (Fin (2 ^ (w₀ - 1))) := by
  have h1 := (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos hm)).trans
    (card_multiplyShiftReduced_eq_le (R := R) hw₀ hU hxy)
  conv at h1 => rhs; rw [← Nat.sub_add_cancel hw₀, pow_succ']
  rw [pow_succ'] at h1
  rw [Fintype.card_fin]
  linarith

/-- For any distinct `x, y : Fin U` (`0 < w₀`, `U ≤ 2 ^ w₀`), the number of remainder seeds
`γ : RemSeed w₀` on which `remHash U w₀ k γ x = remHash U w₀ k γ y` satisfies
`#{γ | remHash U w₀ k γ x = remHash U w₀ k γ y} * 2 ^ k ≤ Fintype.card (RemSeed w₀)`. -/
theorem card_remHash_eq_le {U w₀ k : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {x y : Fin U} (hxy : x ≠ y) :
    #{γ : RemSeed w₀ | remHash U w₀ k γ x = remHash U w₀ k γ y} * 2 ^ k ≤
      Fintype.card (RemSeed w₀) :=
  card_multiplyShiftReduced_mul_le hw₀ hU le_rfl hxy

/-- For any distinct `x, y : Fin U` (`0 < w₀`, `U ≤ 2 ^ w₀`), the number of quotient seeds
`θ : QuotSeed w₀ n` on which `quotHash U w₀ n θ x = quotHash U w₀ n θ y` satisfies
`#{θ | quotHash U w₀ n θ x = quotHash U w₀ n θ y} * 2 ^ quotBits w₀ n ≤
2 * Fintype.card (QuotSeed w₀ n)`. -/
theorem card_quotHash_eq_le {U w₀ n : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {x y : Fin U} (hxy : x ≠ y) :
    #{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ y} * 2 ^ quotBits w₀ n ≤
      2 * Fintype.card (QuotSeed w₀ n) := by
  classical
  let b := quotBits w₀ n
  let Top := ReducedTopSeed w₀
  let Bot := ReducedBotSeed w₀ b b 5
  have hgood (α : Top)
      (hne : multiplyShiftReduced U w₀ (3 * b) α x ≠ multiplyShiftReduced U w₀ (3 * b) α y) :
      #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b ≤
        Fintype.card Bot := by
    let x' := multiplyShiftReduced U w₀ (3 * b) α x
    let y' := multiplyShiftReduced U w₀ (3 * b) α y
    let H := trinomialPolyHash (reducedTrinomialStep w₀ b b) 5 (2 ^ min w₀ (3 * b)) b
    have hk : IsKWiseIndependentHash 5 H :=
      isKWiseIndependentHash_trinomialPolyHash
        (two_pow_min_le_two_pow_reducedTrinomialDeg w₀ b b) (le_reducedTrinomialDeg w₀ b b)
    have hsq : (2 ^ b) ^ 2 * #{β : Bot | H β x' = H β y'} = 2 ^ b * Fintype.card Bot := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun β => H β x') (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _), Finset.mul_sum]
      refine (Finset.sum_congr (g := fun _ => Fintype.card Bot) rfl fun v _ => ?_).trans (by simp)
      have hset : (Finset.univ.filter fun β : Bot => H β x' = H β y').filter
            (fun β => H β x' = v) = Finset.univ.filter fun β : Bot =>
              ({x', y'} : Finset _).restrict (H β) = fun _ => v := by
        ext β
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Subtype.forall,
          Finset.mem_insert, Finset.mem_singleton, Finset.restrict, forall_eq_or_imp, forall_eq]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1.symm.trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1.trans h2.symm, h1⟩⟩
      have hc := hk.card_filter_restrict_eq (T := {x', y'})
        (by rw [Finset.card_pair hne]; decide) (fun _ => v)
      rwa [← hset, Finset.card_pair hne, Fintype.card_fin (2 ^ b)] at hc
    exact (Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos b) (by linear_combination hsq :
      2 ^ b * (#{β : Bot | H β x' = H β y'} * 2 ^ b) = 2 ^ b * Fintype.card Bot)).le
  have hprod : #{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ y} =
      ∑ α : Top, #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} := by
    simp only [Finset.card_filter]
    exact Fintype.sum_prod_type _
  let eqTop (α : Top) : Prop :=
    multiplyShiftReduced U w₀ (3 * b) α x = multiplyShiftReduced U w₀ (3 * b) α y
  rw [hprod, Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ eqTop]
  have hbad : #{α : Top | eqTop α} * 2 ^ b ≤ Fintype.card Top :=
    card_multiplyShiftReduced_mul_le hw₀ hU (by have := three_le_quotBits w₀ n; omega) hxy
  have hsum_bad : (∑ α ∈ Finset.univ.filter eqTop,
      #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b) ≤
      Fintype.card Top * Fintype.card Bot :=
    (Finset.sum_le_sum fun _ _ => Nat.mul_le_mul_right _ (Finset.card_le_univ _)).trans <| by
      rw [Finset.sum_const, smul_eq_mul]; exact (Nat.mul_le_mul_right _ hbad).trans_eq' (by ring)
  have hsum_good : (∑ α ∈ Finset.univ.filter (fun α => ¬eqTop α),
      #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b) ≤
      Fintype.card Top * Fintype.card Bot :=
    (Finset.sum_le_sum fun α hα => hgood α (Finset.mem_filter.mp hα).2).trans <| by
      rw [Finset.sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (Finset.card_le_univ _)
  rw [Fintype.card_prod]
  linarith

/-- Counting false-positive bound over `FilterSeed w₀ n`: for any `S : Finset (Fin U)` with
`#S ≤ n` and any `u ∉ S` (`0 < w₀`, `U ≤ 2 ^ w₀`), the number of seeds `p : FilterSeed w₀ n` for
which `∃ x ∈ S, quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
remHash U w₀ k p.2 x = remHash U w₀ k p.2 u` satisfies
`#{p | ...} * 2 ^ k ≤ Fintype.card (FilterSeed w₀ n)`. -/
theorem card_falsePositive_mul_le {U w₀ n k : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) {u : Fin U} (hu : u ∉ S) :
    #{p : FilterSeed w₀ n |
      ∃ x ∈ S, quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
        remHash U w₀ k p.2 x = remHash U w₀ k p.2 u} * 2 ^ k ≤
      Fintype.card (FilterSeed w₀ n) := by
  classical
  let b := quotBits w₀ n
  set FP : Finset (FilterSeed w₀ n) := {p : FilterSeed w₀ n |
    ∃ x ∈ S, quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
      remHash U w₀ k p.2 x = remHash U w₀ k p.2 u}
  have hFP : #FP ≤ ∑ x ∈ S,
      #{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} *
        #{γ : RemSeed w₀ | remHash U w₀ k γ x = remHash U w₀ k γ u} := by
    refine (Finset.card_le_card (t := S.biUnion fun x =>
      (Finset.univ.filter fun θ : QuotSeed w₀ n => quotHash U w₀ n θ x = quotHash U w₀ n θ u) ×ˢ
        (Finset.univ.filter fun γ : RemSeed w₀ => remHash U w₀ k γ x = remHash U w₀ k γ u))
      fun p hp => ?_).trans
      (Finset.card_biUnion_le.trans_eq (by simp only [Finset.card_product]))
    simpa only [FP, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_product] using hp
  have h2S : 2 * #S ≤ 2 ^ b := by
    have := card_le_effCap hU hS
    have := eight_mul_effCap_le_two_pow_quotBits w₀ n
    dsimp only [b]; omega
  have hmul : (#FP * 2 ^ k) * 2 ^ b ≤ Fintype.card (FilterSeed w₀ n) * 2 ^ b :=
    calc (#FP * 2 ^ k) * 2 ^ b
        = #FP * (2 ^ b * 2 ^ k) := by ring
      _ ≤ (∑ x ∈ S, #{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} *
            #{γ : RemSeed w₀ | remHash U w₀ k γ x = remHash U w₀ k γ u}) *
            (2 ^ b * 2 ^ k) := Nat.mul_le_mul_right _ hFP
      _ = ∑ x ∈ S, (#{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} * 2 ^ b) *
            (#{γ : RemSeed w₀ | remHash U w₀ k γ x = remHash U w₀ k γ u} * 2 ^ k) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ _x ∈ S, (2 * Fintype.card (QuotSeed w₀ n)) * Fintype.card (RemSeed w₀) :=
          Finset.sum_le_sum fun x hx => Nat.mul_le_mul
            (card_quotHash_eq_le hw₀ hU (ne_of_mem_of_not_mem hx hu))
            (card_remHash_eq_le hw₀ hU (ne_of_mem_of_not_mem hx hu))
      _ = Fintype.card (FilterSeed w₀ n) * (2 * #S) := by
          rw [Finset.sum_const, smul_eq_mul, Fintype.card_prod (QuotSeed w₀ n) (RemSeed w₀)]; ring
      _ ≤ Fintype.card (FilterSeed w₀ n) * 2 ^ b := Nat.mul_le_mul_left _ h2S
  exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos b)

/-- **Per-query false-positive probability bound**: for any `S : Finset (Fin U)` with `#S ≤ n` and
any absent key `u ∉ S` (`0 < w₀`, `U ≤ 2 ^ w₀`), the probability under `filterSeedLaw w₀ n` that
`u` collides in both quotient and remainder with some key in `S` is at most `(1 / 2 : ℝ≥0∞) ^ k`. -/
theorem toOuterMeasure_falsePositive_le {U w₀ n k : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) {u : Fin U} (hu : u ∉ S) :
    (filterSeedLaw w₀ n).toOuterMeasure
      {p : FilterSeed w₀ n |
        ∃ x ∈ S, quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
          remHash U w₀ k p.2 x = remHash U w₀ k p.2 u} ≤
      (1 / 2 : ℝ≥0∞) ^ k := by
  classical
  set E : Set (FilterSeed w₀ n) := {p |
    ∃ x ∈ S, quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
      remHash U w₀ k p.2 x = remHash U w₀ k p.2 u}
  rw [← E.coe_toFinset, filterSeedLaw, PMF.toOuterMeasure_apply_finset]
  simp only [E, Set.toFinset_ofPred, PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul,
    one_div]
  rw [← ENNReal.inv_pow, ENNReal.le_inv_iff_mul_le, mul_right_comm, ← div_eq_mul_inv]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact_mod_cast card_falsePositive_mul_le (k := k) hw₀ hU hS hu

/-- Minimum exponent `k = max 1 ⌈log₂(1 / ε)⌉` such that `(1 / 2 : ℝ≥0∞) ^ k ≤ ε` for any
`ε : ℝ≥0∞` with `ε ≠ 0`. -/
@[expose] noncomputable def epsLog (ε : ℝ≥0∞) : ℕ :=
  max 1 (Nat.clog 2 ⌈ε⁻¹.toNNReal⌉₊)

theorem one_le_epsLog (ε : ℝ≥0∞) : 1 ≤ epsLog ε :=
  le_max_left 1 _

theorem two_pow_neg_epsLog_le {ε : ℝ≥0∞} (hε0 : ε ≠ 0) :
    (1 / 2 : ℝ≥0∞) ^ epsLog ε ≤ ε := by
  rw [one_div, ← ENNReal.inv_pow]
  conv_rhs => rw [← inv_inv ε]
  rw [ENNReal.inv_le_inv]
  calc ε⁻¹ = ((ε⁻¹.toNNReal : ℝ≥0) : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hε0)).symm
    _ ≤ ((⌈ε⁻¹.toNNReal⌉₊ : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr (Nat.le_ceil _)
    _ ≤ ((2 ^ epsLog ε : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr <|
        (Nat.le_pow_clog one_lt_two _).trans (Nat.pow_le_pow_right two_pos (le_max_right 1 _))
    _ = (2 : ℝ≥0∞) ^ epsLog ε := by push_cast; rfl

/-! ## Section 3: Expected cluster length bound across the two-stage seed distribution -/

/-- Seed-only upper bound on the cluster length around `quotHash U w₀ n θ u` for any state
representing `S` (`#S ≤ n`). -/
@[expose] noncomputable def seedClusterBound (U w₀ n : ℕ) (S : Finset (Fin U)) (u : Fin U)
    (θ : QuotSeed w₀ n) : ℕ :=
  let b := quotBits w₀ n
  let T : Finset (Fin U) := insert u (S.erase u)
  if θ.1 ∈ reducedGoodTop U w₀ (3 * b) T then
    1 + ∑ j ∈ Finset.Icc 1 b,
      if scaleOverload b (fun β' x => quotHash U w₀ n (θ.1, β') x) (S.erase u) u j θ.2
      then 2 ^ j else 0
  else
    2 ^ b

/-- Pointwise bound of `hinv.clusterLen hS_lt (quotHash U w₀ n θ u)` by the state-independent
quantity `seedClusterBound U w₀ n S u θ`. -/
theorem FilterInv.clusterLen_le_seedClusterBound {U w₀ n f : ℕ}
    {S : Finset (Fin U)} {θ : QuotSeed w₀ n} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState (quotBits w₀ n) f}
    (hinv : FilterInv n S (quotHash U w₀ n θ) rem st)
    (hS_lt : #S < 2 ^ quotBits w₀ n) (u : Fin U) :
    hinv.clusterLen hS_lt (quotHash U w₀ n θ u) ≤ seedClusterBound U w₀ n S u θ := by
  dsimp only [seedClusterBound]
  split_ifs with hgood
  · rw [← Nat.sub_le_iff_le_add', ← Nat.cast_le (α := ℝ)]
    simpa [Nat.cast_ite, mul_ite] using hinv.clusterLen_sub_one_le_sum_scaleOverload
      (fun β' x => quotHash U w₀ n (θ.1, β') x) θ.2 hS_lt u
  · exact (hinv.clusterLen_le_card hS_lt _).trans hS_lt.le

/-- For any top-level seed `α ∈ reducedGoodTop U w₀ (3 * quotBits w₀ n) (insert u (S.erase u))`
that is injective on `insert u (S.erase u)`, summing `seedClusterBound - 1` over all bottom
polynomial seeds `β : ReducedBotSeed w₀ (quotBits w₀ n) (quotBits w₀ n) 5` is bounded by
`288 * Fintype.card Bot`. -/
theorem sum_seedClusterBound_sub_one_goodTop_le {U w₀ n : ℕ} (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (u : Fin U)
    {α : ReducedTopSeed w₀}
    (hα : α ∈ reducedGoodTop U w₀ (3 * quotBits w₀ n) (insert u (S.erase u))) :
    (∑ β : ReducedBotSeed w₀ (quotBits w₀ n) (quotBits w₀ n) 5,
      (seedClusterBound U w₀ n S u (α, β) - 1)) ≤
      288 * Fintype.card (ReducedBotSeed w₀ (quotBits w₀ n) (quotBits w₀ n) 5) := by
  classical
  let b := quotBits w₀ n
  let Bot := ReducedBotSeed w₀ b b 5
  let T : Finset (Fin U) := insert u (S.erase u)
  let u' : T := ⟨u, Finset.mem_insert_self u (S.erase u)⟩
  let S' : Finset T := (S.erase u).subtype (· ∈ T)
  have hu'_notMem : u' ∉ S' := by simp [S', u']
  have hS'_card : #S' ≤ effCap w₀ n := by
    rw [Finset.card_subtype,
      Finset.filter_true_of_mem fun _ hx => Finset.mem_insert_of_mem hx]
    exact Finset.card_erase_le.trans (card_le_effCap hU hS)
  let hT : Bot → T → Fin (2 ^ b) := fun β x => quotHash U w₀ n (α, β) x.val
  have hkT : IsKWiseIndependentHash 5 hT :=
    isKWiseIndependentHash_reducedPolyHash_of_injOn (mem_reducedGoodTop.mp hα)
  have hov_eq (j : ℕ) (β : Bot) :
      scaleOverload b (fun β' x => quotHash U w₀ n (α, β') x) (S.erase u) u j β ↔
        scaleOverload b hT S' u' j β := by
    dsimp only [scaleOverload, hT, u', S']
    have hf : (((S.erase u).subtype (· ∈ T)).filter fun x : T =>
          quotHash U w₀ n (α, β) x.val ∈ scaleWindow b (quotHash U w₀ n (α, β) u) j) =
        ((S.erase u).filter fun x =>
          quotHash U w₀ n (α, β) x ∈ scaleWindow b (quotHash U w₀ n (α, β) u) j).subtype
          (· ∈ T) := by ext ⟨x, hx⟩; simp
    rw [hf, Finset.card_subtype,
      Finset.filter_true_of_mem fun _ hx => Finset.mem_insert_of_mem (Finset.mem_filter.mp hx).1]
  have hpt (β : Bot) :
      ((seedClusterBound U w₀ n S u (α, β) - 1 : ℕ) : ℝ) =
        ∑ j ∈ Finset.Icc 1 b,
          (2 ^ j : ℝ) * (if scaleOverload b hT S' u' j β then (1 : ℝ) else 0) := by
    dsimp only [seedClusterBound]
    rw [ite_eq_left hα, Nat.add_sub_cancel_left, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_congr (hov_eq j β) rfl rfl]
    split_ifs <;> simp
  have hexp :
      (𝔼 β : Bot, ((seedClusterBound U w₀ n S u (α, β) - 1 : ℕ) : ℝ)) ≤ 288 :=
    calc (𝔼 β : Bot, ((seedClusterBound U w₀ n S u (α, β) - 1 : ℕ) : ℝ))
        = ∑ j ∈ Finset.Icc 1 b,
            𝔼 β : Bot, (2 ^ j : ℝ) * (if scaleOverload b hT S' u' j β then (1 : ℝ) else 0) := by
          simp_rw [hpt]; exact Finset.expect_sum_comm _ _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 b, (2 ^ j : ℝ) * (288 / (2 ^ j : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← Finset.mul_expect]
          exact mul_le_mul_of_nonneg_left
            (expect_scaleOverload_le hkT S' hu'_notMem hS'_card
              (eight_mul_effCap_le_two_pow_quotBits w₀ n)) (by positivity)
      _ = 288 * ∑ j ∈ Finset.Ico 1 (b + 1), (2⁻¹ : ℝ) ^ j := by
          rw [show Finset.Icc 1 b = Finset.Ico 1 (b + 1) by ext; simp, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [inv_pow]; field_simp
      _ ≤ 288 := by
          rw [geom_sum_Ico' (by norm_num) (Nat.le_add_left 1 b)]
          have h0 : (0 : ℝ) ≤ (2⁻¹ : ℝ) ^ (b + 1) := by positivity
          linarith [show 288 * (((2⁻¹ : ℝ) ^ 1 - (2⁻¹ : ℝ) ^ (b + 1)) / (1 - 2⁻¹)) =
            288 - 576 * (2⁻¹ : ℝ) ^ (b + 1) by ring]
  rw [Fintype.expect_eq_sum_div_card,
    div_le_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)] at hexp
  exact_mod_cast hexp

/-- **Unconditional sum bound on `seedClusterBound` over `QuotSeed w₀ n`**:
for any `S : Finset (Fin U)` with `#S ≤ n` and any `u : Fin U` (`0 < w₀`, `U ≤ 2 ^ w₀`),
the sum of `seedClusterBound` over all quotient seeds `θ : QuotSeed w₀ n` is at most
`290 * Fintype.card (QuotSeed w₀ n)`. -/
theorem sum_seedClusterBound_le {U w₀ n : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (u : Fin U) :
    (∑ θ : QuotSeed w₀ n, seedClusterBound U w₀ n S u θ) ≤
      290 * Fintype.card (QuotSeed w₀ n) := by
  classical
  let b := quotBits w₀ n
  let Top := ReducedTopSeed w₀
  let Bot := ReducedBotSeed w₀ b b 5
  let T : Finset (Fin U) := insert u (S.erase u)
  let Good : Finset Top := reducedGoodTop U w₀ (3 * b) T
  let Bad : Finset Top := Finset.univ \ Good
  have hgood_each (α : Top) (hα : α ∈ Good) :
      (∑ β : Bot, seedClusterBound U w₀ n S u (α, β)) ≤ 289 * Fintype.card Bot := by
    have hle : (∑ β : Bot, seedClusterBound U w₀ n S u (α, β)) ≤
        (∑ β : Bot, (seedClusterBound U w₀ n S u (α, β) - 1)) + Fintype.card Bot := by
      rw [show Fintype.card Bot = ∑ _ : Bot, 1 by simp, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun _ _ => by omega
    linarith [sum_seedClusterBound_sub_one_goodTop_le hU hS u hα]
  have hsum_good : (∑ α ∈ Good, ∑ β : Bot, seedClusterBound U w₀ n S u (α, β)) ≤
      289 * Fintype.card (QuotSeed w₀ n) :=
    (Finset.sum_le_sum hgood_each).trans <| by
      rw [Finset.sum_const, smul_eq_mul, Fintype.card_prod]
      exact (Nat.mul_le_mul_left 289 (Nat.mul_le_mul_right _ (Finset.card_le_univ Good))).trans_eq'
        (by ring)
  have hT_le : #T ≤ 2 ^ b := by
    have := Finset.card_insert_le u (S.erase u)
    have := Finset.card_erase_le (s := S) (a := u) |>.trans (card_le_effCap hU hS)
    have := eight_mul_effCap_le_two_pow_quotBits w₀ n
    have := eight_le_two_pow_quotBits w₀ n
    dsimp only [T, b]; omega
  have hbad_card : #Bad * 2 ^ b ≤ Fintype.card Top := by
    refine Nat.le_of_mul_le_mul_right (c := 2 ^ (2 * b)) ?_ (Nat.two_pow_pos _)
    calc (#Bad * 2 ^ b) * 2 ^ (2 * b)
        = #Bad * 2 ^ (3 * b) := by rw [mul_assoc, ← pow_add, show b + 2 * b = 3 * b by omega]
      _ ≤ (#T * (#T - 1)) * 2 ^ (w₀ - 1) := card_not_injOn_multiplyShiftReduced_le hw₀ hU T
      _ ≤ (2 ^ b * 2 ^ b) * Fintype.card Top :=
          Nat.mul_le_mul (Nat.mul_le_mul hT_le ((Nat.sub_le _ _).trans hT_le))
            (Fintype.card_fin _).symm.le
      _ = Fintype.card Top * 2 ^ (2 * b) := by rw [← pow_add, ← two_mul, mul_comm]
  have hsum_bad : (∑ α ∈ Bad, ∑ β : Bot, seedClusterBound U w₀ n S u (α, β)) ≤
      Fintype.card (QuotSeed w₀ n) := by
    rw [Finset.sum_congr rfl fun α hα => Finset.sum_congr rfl fun β _ =>
      show seedClusterBound U w₀ n S u (α, β) = 2 ^ b by
        dsimp only [seedClusterBound]; exact ite_eq_right (Finset.mem_sdiff.mp hα).2]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod]
    exact (Nat.mul_le_mul_right _ hbad_card).trans_eq' (by ring)
  rw [Fintype.sum_prod_type, ← Finset.sum_sdiff (Finset.subset_univ Good)]
  linarith

/-- **`ℝ≥0∞` expectation bound on `seedClusterBound` under `filterSeedLaw w₀ n`**:
`∑' p : FilterSeed w₀ n, filterSeedLaw w₀ n p * (seedClusterBound U w₀ n S u p.1 : ℝ≥0∞) ≤ 290`. -/
theorem tsum_seedClusterBound_le {U w₀ n : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (u : Fin U) :
    (∑' p : FilterSeed w₀ n,
      (filterSeedLaw w₀ n) p * (seedClusterBound U w₀ n S u p.1 : ℝ≥0∞)) ≤ 290 := by
  classical
  rw [tsum_fintype]
  simp only [filterSeedLaw, PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ← Nat.cast_sum, mul_comm, ← div_eq_mul_inv]
  refine ENNReal.div_le_of_le_mul ?_
  norm_cast
  rw [Fintype.sum_prod_type_right]
  refine (Finset.sum_le_sum fun _ _ => sum_seedClusterBound_le hw₀ hU hS u).trans ?_
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_prod (QuotSeed w₀ n) (RemSeed w₀)]
  exact (by ring : _ = _).le

/-- **Unconditional sum bound on `clusterLen` over `QuotSeed w₀ n`**:
for any `S : Finset (Fin U)` with `#S ≤ n` and any `u : Fin U` (`0 < w₀`, `U ≤ 2 ^ w₀`),
the sum of `clusterLen` over all quotient seeds `θ : QuotSeed w₀ n` is at most
`290 * Fintype.card (QuotSeed w₀ n)`. -/
theorem sum_clusterLen_le {U w₀ n f : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (hS_lt : #S < 2 ^ quotBits w₀ n) (u : Fin U)
    {rem : Fin U → Fin (2 ^ f)}
    {st : QuotSeed w₀ n → FilterState (quotBits w₀ n) f}
    (hinv : ∀ θ : QuotSeed w₀ n, FilterInv n S (quotHash U w₀ n θ) rem (st θ)) :
    (∑ θ : QuotSeed w₀ n, (hinv θ).clusterLen hS_lt (quotHash U w₀ n θ u)) ≤
      290 * Fintype.card (QuotSeed w₀ n) :=
  (Finset.sum_le_sum fun θ _ => (hinv θ).clusterLen_le_seedClusterBound hS_lt u).trans
    (sum_seedClusterBound_le hw₀ hU hS u)

/-- **`ℝ≥0∞` expectation bound on `clusterLen` under `filterSeedLaw w₀ n`**:
`∑' p : FilterSeed w₀ n, filterSeedLaw w₀ n p * (clusterLen p.1 : ℝ≥0∞) ≤ 290`. -/
theorem tsum_clusterLen_le {U w₀ n f : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (hS_lt : #S < 2 ^ quotBits w₀ n) (u : Fin U)
    {rem : RemSeed w₀ → Fin U → Fin (2 ^ f)}
    {st : FilterSeed w₀ n → FilterState (quotBits w₀ n) f}
    (hinv : ∀ p : FilterSeed w₀ n, FilterInv n S (quotHash U w₀ n p.1) (rem p.2) (st p)) :
    (∑' p : FilterSeed w₀ n,
      (filterSeedLaw w₀ n) p *
        ((hinv p).clusterLen hS_lt (quotHash U w₀ n p.1 u) : ℝ≥0∞)) ≤ 290 := by
  refine le_trans ?_ (tsum_seedClusterBound_le hw₀ hU hS u)
  gcongr with p
  exact Nat.cast_le.mpr ((hinv p).clusterLen_le_seedClusterBound hS_lt u)

end Cslib.DataStructure.ApproximateMembership.QuotientFilter
