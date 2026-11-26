/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.FanInTwo
public import CslibFrontier.Computability.Circuit.Frontier.TwoSidedWitness
public import CslibFrontier.Computability.Complexity.Classes.P.Slices
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.AffineSource
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# From sumset extractors and rectangle bias to frontier lower bounds

This module bridges randomness extraction from independent sources (`RectangleBias` and
`Cslib.AffineDisperser.Li.IsSumsetExtractor`) to the worst-case and average-case frontier circuit
lower bounds (`CslibFrontier/Computability/Circuit/Frontier/FanInTwo.lean`).

## General bias-to-frontier bridge

A family `S_n ⊆ U^n` with eventual rectangle bias `b_n ≤ c < 1 / 2` on rectangles of side size
`K_n ≥ 1` with `log K_n = o(n)` is `DenseRectangleFree`
(`denseRectangleFree_of_eventually_rectangleBias`): `RectangleBias.rectangleFree` gives
eventual `K_n`-rectangle-freeness, and applying `RectangleBias` to a balanced `⌊n / 2⌋` coordinate
split bounds `(S_n).ncard ≥ (1 / 2 - c) |U|^n`, so the logarithmic density deficit
`n log |U| - log |S_n|` is `O(1) = o(n)`.

## Sumset extractor bridge

For a `(k, k, ε)` sumset extractor `ext : BitString n → BitString m`
(`Cslib.AffineDisperser.Li.IsSumsetExtractor`), zero-padding assignments on `X ⊆ Fin n` and `Xᶜ`
into `BitString n` expresses the uniform distribution on any combinatorial rectangle
`rectangle X A B` with `|A|, |B| ≥ 2 ^ k` as the XOR-sum `p_A + p_B` of two independent sources of
min-entropy at least `k`. Consequently:

* every output bit fiber `{x | ext x j = val}` has rectangle bias at most `ε` above threshold
  `2 ^ k` (`rectangleBias_of_isSumsetExtractor`);
* for a family of `(k_n, k_n, ε_n)` sumset extractors with `k_n = o(n)` and `ε_n ≤ c < 1 / 2`,
  every output bit fiber forms a `DenseRectangleFree` family
  (`denseRectangleFree_of_isSumsetExtractor`), hence requires more than `(L₃ - δ) n` multiary gates
  over every fan-in-two signature
  (`eventually_switched_sub_mul_lt_multiarySize_of_isSumsetExtractor`, with
  `L₃ = 1 + 2π / (3 arccos (5 / 6)) ≈ 4.575972`) and satisfies the `(L₃ - δ) n` average-case
  agreement bound (`exists_eventually_agreement_le_of_isSumsetExtractor`).

These theorems are **conditional reduction steps in Lean**: the explicit extractor and its
polynomial-time implementation remain to be formalized, as tracked by
[#7793](https://github.com/cslib-community/cslib-frontier/issues/7793).
Mathematically, [Li2023], ECCC TR23-023 revision 1, Theorem 7.13 (p. 36), already supplies a
polynomial-time one-bit sumset extractor with entropy threshold `c(ε) log n` for each fixed
`ε > 0`. For `ε < 1 / 2`, it meets the hypotheses of
`mem_P_and_eventually_switched_lt_multiarySize_of_isSumsetExtractor` and yields the explicit `P`
worst-case bound. The corresponding average-case bound is
`agreement ≤ 1 / 2 + ε + exp (-γ n)`; that fixed-error theorem alone does not supply a single
family with vanishing error as `n` grows.

## Main results

* `Cslib.Circuits.Frontier.denseRectangleFree_of_eventually_rectangleBias`: subexponential-threshold
  rectangle bias bounded below `1 / 2` implies `DenseRectangleFree`.
* `Cslib.Circuits.Frontier.rectangleBias_of_isSumsetExtractor`: a `(k, k, ε)` sumset extractor has
  `(2 ^ k, ε)` rectangle bias on every output bit.
* `Cslib.Circuits.Frontier.denseRectangleFree_of_isSumsetExtractor`: sublinear-entropy sumset
  extractors with error bounded away from `1 / 2` give `DenseRectangleFree` bit fibers.
* `Cslib.Circuits.Frontier.eventually_switched_sub_mul_lt_multiarySize_of_isSumsetExtractor`,
  `Cslib.Circuits.Frontier.exists_eventually_agreement_le_of_isSumsetExtractor`,
  `Cslib.Circuits.Frontier.mem_P_and_eventually_switched_lt_multiarySize_of_isSumsetExtractor`:
  conditional reduction steps from `IsSumsetExtractor` to worst-case, average-case, and `P` slice
  lower bounds.

## References

* [X. Li, *Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*][Li2023],
  ECCC TR23-023 revision 1, Definition 1.1 (p. 1) and Theorem 7.13 (p. 36)
-/

public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics Real
open Cslib.AffineDisperser.Li Cslib.Probability
open scoped Cslib.Probability.PMF

universe u v

/-! ### From rectangle bias to `DenseRectangleFree` -/

/-- **Subexponential-threshold rectangle bias bounded away from `1 / 2` gives a dense
rectangle-free family.** If eventually `S_n ⊆ U^n` has bias at most `b_n ≤ c < 1 / 2` on
rectangles with sides of size at least `K_n ≥ 1`, where `log K_n = o(n)`, then `S` is
`DenseRectangleFree` with threshold `K`. -/
theorem denseRectangleFree_of_eventually_rectangleBias {U : Type u} [Finite U] [Nontrivial U]
    {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ} {b : ℕ → ℝ}
    (hbias : ∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n))
    (hKpos : ∀ᶠ n in atTop, 1 ≤ K n)
    (hKlog : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hb : ∃ c < 1 / 2, ∀ᶠ n in atTop, b n ≤ c) :
    DenseRectangleFree S K := by
  obtain ⟨c, hc, hbc⟩ := hb
  refine ⟨?_, hKlog, ?_⟩
  · filter_upwards [hbias, hKpos, hbc] with n hbn hKn hbcn
    exact hbn.rectangleFree (hbcn.trans_lt hc) (lt_of_lt_of_le Nat.zero_lt_one hKn)
  · set q := Nat.card U
    have hq1 : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
    have hq_pos : 0 < q := Nat.card_pos
    have hlogq : 0 < Real.log q := Real.log_pos hq1
    have hK_pow : ∀ᶠ n in atTop, K n ≤ q ^ (n / 2) := by
      filter_upwards [hKlog.bound (show 0 < Real.log q / 3 by positivity), hKpos,
        eventually_ge_atTop 6] with n hn hKn hn6
      have hdiv : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : n ≤ 3 * (n / 2))
      simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] at hn
      have hlog_le : Real.log (K n) ≤ Real.log ((q : ℝ) ^ (n / 2)) := by
        rw [Real.log_pow]; nlinarith [le_abs_self (Real.log (K n))]
      exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast hKn) (by positivity)).mp hlog_le
    set c' := max c 0
    have hc'half : c' < 1 / 2 := max_lt hc (by norm_num)
    have hgap : 0 < 1 / 2 - c' := by linarith
    have hdef_bdd : ∀ᶠ n in atTop,
        |n * Real.log q - Real.log (S n).ncard| ≤ -Real.log (1 / 2 - c') := by
      filter_upwards [hbias, hbc, hK_pow] with n hbn hbcn hKpow
      obtain ⟨X, -, hX⟩ := exists_subset_card_eq (s := (univ : Set (Fin n))) (n := n / 2)
        (by rw [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]; exact Nat.div_le_self n 2)
      have hXc : n / 2 ≤ Xᶜ.ncard := by
        have := (ncard_add_ncard_compl X).trans (Fintype.card_fin n ▸ Nat.card_eq_fintype_card)
        omega
      have hA : K n ≤ (univ : Set (X → U)).ncard := by
        rwa [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, hX]
      have hB : K n ≤ (univ : Set (↥Xᶜ → U)).ncard := by
        rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]
        exact hKpow.trans (Nat.pow_le_pow_right hq_pos hXc)
      have hrect_univ : rectangle X (univ : Set (X → U)) univ = univ :=
        Set.ext fun _ => by simp [rectangle]
      have hcard_univ : ((univ : Set (Fin n → U)).ncard : ℝ) = (q : ℝ) ^ n := by
        simp [q, ncard_univ, Nat.card_fun]
      have hbias_n := hbn X univ univ hA hB
      rw [hrect_univ, univ_inter, hcard_univ] at hbias_n
      have hb_le : b n ≤ c' := hbcn.trans (le_max_left c 0)
      have hqn_pos : (0 : ℝ) < (q : ℝ) ^ n := by positivity
      have hS_lower : (1 / 2 - c') * (q : ℝ) ^ n ≤ (S n).ncard := by
        linarith [neg_le_abs ((S n).ncard - (q : ℝ) ^ n / 2),
          mul_le_mul_of_nonneg_right hb_le hqn_pos.le]
      have hS_pos : (0 : ℝ) < (S n).ncard := lt_of_lt_of_le (by positivity) hS_lower
      have hS_upper : ((S n).ncard : ℝ) ≤ (q : ℝ) ^ n :=
        hcard_univ ▸ Nat.cast_le.mpr (ncard_le_ncard (subset_univ (S n)) (toFinite _))
      have hlog_low : Real.log (1 / 2 - c') + n * Real.log q ≤ Real.log (S n).ncard := by
        simpa only [Real.log_mul hgap.ne' hqn_pos.ne', Real.log_pow] using
          (Real.log_le_log_iff (by positivity) hS_pos).mpr hS_lower
      have hlog_high : Real.log (S n).ncard ≤ n * Real.log q := by
        simpa only [Real.log_pow] using (Real.log_le_log_iff hS_pos hqn_pos).mpr hS_upper
      rw [abs_of_nonneg (by linarith)]
      linarith
    rw [isLittleO_iff]
    intro δ hδ
    set B := max (-Real.log (1 / 2 - c')) 0
    filter_upwards [hdef_bdd,
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (B / δ))] with n hbn hRn
    simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    have hBδ : B ≤ δ * n := by rwa [div_le_iff₀ hδ, mul_comm] at hRn
    linarith [le_max_left (-Real.log (1 / 2 - c')) 0]

/-! ### Zero-padding combinatorial rectangles into XOR-sums of independent sources -/

private def padLeft {n : ℕ} (X : Set (Fin n)) [DecidablePred (· ∈ X)]
    (a : X → Bool) (i : Fin n) : Bool :=
  if h : i ∈ X then a ⟨i, h⟩ else false

private def padRight {n : ℕ} (X : Set (Fin n)) [DecidablePred (· ∈ X)]
    (b : ↥Xᶜ → Bool) (i : Fin n) : Bool :=
  if h : i ∈ X then false else b ⟨i, h⟩

private theorem domRestrict_padLeft_add_padRight {n : ℕ} (X : Set (Fin n))
    [DecidablePred (· ∈ X)] (a : X → Bool) (b : ↥Xᶜ → Bool) :
    X.domRestrict (padLeft X a + padRight X b) = a := by
  funext ⟨i, hi⟩
  simp only [Set.domRestrict, Pi.add_apply, padLeft, padRight, dite_eq_left hi,
    ← Bool.zero_eq_false, add_zero]

private theorem domRestrict_compl_padLeft_add_padRight {n : ℕ} (X : Set (Fin n))
    [DecidablePred (· ∈ X)] (a : X → Bool) (b : ↥Xᶜ → Bool) :
    Xᶜ.domRestrict (padLeft X a + padRight X b) = b := by
  funext ⟨i, hi⟩
  have hi' : i ∉ X := hi
  simp only [Set.domRestrict, Pi.add_apply, padLeft, padRight, dite_eq_right hi',
    ← Bool.zero_eq_false, zero_add]

private theorem padLeft_domRestrict_add_padRight_domRestrict {n : ℕ} (X : Set (Fin n))
    [DecidablePred (· ∈ X)] (x : BitString n) :
    padLeft X (X.domRestrict x) + padRight X (Xᶜ.domRestrict x) = x := by
  funext i
  by_cases hi : i ∈ X <;>
    simp [padLeft, padRight, hi, Set.domRestrict, ← Bool.zero_eq_false]

private theorem padLeft_injective {n : ℕ} (X : Set (Fin n)) [DecidablePred (· ∈ X)] :
    Function.Injective (padLeft X) := by
  intro a₁ a₂ h
  funext ⟨i, hi⟩
  simpa only [padLeft, dite_eq_left hi] using congrFun h i

private theorem padRight_injective {n : ℕ} (X : Set (Fin n)) [DecidablePred (· ∈ X)] :
    Function.Injective (padRight X) := by
  intro b₁ b₂ h
  funext ⟨i, hi⟩
  have hi' : i ∉ X := hi
  simpa only [padRight, dite_eq_right hi'] using congrFun h i

private def rectProdEquiv {n : ℕ} (X : Set (Fin n)) [DecidablePred (· ∈ X)]
    (A : Set (X → Bool)) (B : Set (↥Xᶜ → Bool)) :
    (↥A × ↥B) ≃ ↥(rectangle X A B) where
  toFun p := ⟨padLeft X p.1.val + padRight X p.2.val,
    ⟨by rw [domRestrict_padLeft_add_padRight]; exact p.1.property,
     by rw [domRestrict_compl_padLeft_add_padRight]; exact p.2.property⟩⟩
  invFun r := (⟨X.domRestrict r.val, r.property.1⟩, ⟨Xᶜ.domRestrict r.val, r.property.2⟩)
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ =>
    Prod.ext (Subtype.ext (domRestrict_padLeft_add_padRight X _ _))
      (Subtype.ext (domRestrict_compl_padLeft_add_padRight X _ _))
  right_inv := fun ⟨x, _⟩ =>
    Subtype.ext (padLeft_domRestrict_add_padRight_domRestrict X x)

private theorem le_minEntropy_uniformOfFintype_map {α β : Type*} [Fintype α] [Nonempty α]
    {f : α → β} (hf : Function.Injective f) {k : ℕ} (hk : 2 ^ k ≤ Fintype.card α) :
    (k : ℝ) ≤ PMF.minEntropy ((PMF.uniformOfFintype α).map f) := by
  classical
  rw [PMF.le_minEntropy_iff]
  intro y
  by_cases hy : ∃ a, f a = y
  · obtain ⟨a, rfl⟩ := hy
    rw [PMF.map_apply_of_injective _ hf, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Real.rpow_neg (by norm_num)]
    refine inv_anti₀ (by positivity) ?_
    rw [Real.rpow_natCast]
    exact_mod_cast hk
  · push Not at hy
    rw [PMF.map_apply, tsum_eq_zero_iff.2 fun a => ite_eq_right (Ne.symm (hy a)),
      ENNReal.toReal_zero]
    positivity

private def eqBoolEquiv (val : Bool) : Bool ≃ Bool where
  toFun b := decide (b = val)
  invFun b := match val with | true => b | false => !b
  left_inv b := by cases val <;> cases b <;> rfl
  right_inv b := by cases val <;> cases b <;> rfl

/-! ### Sumset extractor bridges -/

/-- **Every output bit of a `(k, k, ε)` sumset extractor has `(2 ^ k, ε)` rectangle bias.**
Zero-padding the two sides of any combinatorial rectangle `rectangle X A B` with
`|A|, |B| ≥ 2 ^ k` produces two independent sources of min-entropy at least `k` whose XOR-sum is
uniform on `rectangle X A B`. -/
theorem rectangleBias_of_isSumsetExtractor {n m k : ℕ} {ε : ℝ}
    {ext : BitString n → BitString m} (hext : IsSumsetExtractor ext k k ε)
    (j : Fin m) (val : Bool) :
    RectangleBias {x : BitString n | ext x j = val} (2 ^ k) ε := by
  classical
  intro X A B hA hB
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype B := Fintype.ofFinite B
  let R := rectangle X A B
  let S : Set (BitString n) := {x | ext x j = val}
  let _ : Fintype R := Fintype.ofFinite R
  have hcard {α : Type} (T : Set α) [Fintype T] : Fintype.card T = T.ncard :=
    Nat.card_eq_fintype_card.symm.trans (Nat.card_coe_set_eq T)
  have hA_pos : 0 < Fintype.card A :=
    hcard A ▸ lt_of_lt_of_le (pow_pos Nat.zero_lt_two k) hA
  have hB_pos : 0 < Fintype.card B :=
    hcard B ▸ lt_of_lt_of_le (pow_pos Nat.zero_lt_two k) hB
  let _ : Nonempty A := Fintype.card_pos_iff.mp hA_pos
  let _ : Nonempty B := Fintype.card_pos_iff.mp hB_pos
  let _ : Nonempty R := ⟨rectProdEquiv X A B (Classical.arbitrary _)⟩
  let pA : PMF (BitString n) := (PMF.uniformOfFintype A).map (fun a => padLeft X a.val)
  let pB : PMF (BitString n) := (PMF.uniformOfFintype B).map (fun b => padRight X b.val)
  have hkA : (k : ℝ) ≤ PMF.minEntropy pA :=
    le_minEntropy_uniformOfFintype_map ((padLeft_injective X).comp Subtype.val_injective)
      (hcard A ▸ hA)
  have hkB : (k : ℝ) ≤ PMF.minEntropy pB :=
    le_minEntropy_uniformOfFintype_map ((padRight_injective X).comp Subtype.val_injective)
      (hcard B ▸ hB)
  have hsum : (pA.bind fun x => pB.map fun y => x + y) =
      (PMF.uniformOfFintype R).map Subtype.val := by
    simp only [pA, pB, PMF.bind_map, PMF.map_comp, Function.comp_def,
      PMF.uniformOfFintype_bind_map]
    have hrect : (fun p : ↥A × ↥B => padLeft X p.1.val + padRight X p.2.val) =
        Subtype.val ∘ rectProdEquiv X A B := rfl
    rw [hrect, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]
  let proj : BitString m → Bool := fun y => eqBoolEquiv val (y j)
  have hunif : (PMF.uniformOfFintype (BitString m)).map proj = PMF.uniformOfFintype Bool := by
    have hproj : proj = ⇑(eqBoolEquiv val) ∘ fun y : BitString m => y j := rfl
    rw [hproj, ← PMF.map_comp, ← PMF.pi_uniformOfFintype (α := fun _ : Fin m => Bool),
      PMF.pi_map_eval, PMF.uniformOfFintype_map_equiv]
  let pOut : PMF Bool := (PMF.uniformOfFintype R).map (fun r : R => decide (ext r.val j = val))
  have hpOut : ((pA.bind fun x => pB.map fun y => x + y).map ext).map proj = pOut := by
    simp only [hsum, PMF.map_comp]; rfl
  have hdist : dist pOut (PMF.uniformOfFintype Bool) ≤ ε := by
    rw [← hpOut, ← hunif]
    exact (PMF.dist_map_le _ _ proj).trans (hext pA pB hkA hkB)
  rw [PMF.dist_uniformOfFintype_bool] at hdist
  have hpOut_true : (pOut true).toReal = ((R ∩ S).ncard : ℝ) / R.ncard := by
    have hcard_fib :
        ({r : R | decide (ext r.val j = val) = true} : Finset R).card = (R ∩ S).ncard := by
      rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq (R ∩ S)]
      exact Nat.card_congr ((Equiv.subtypeEquivRight fun r : R => by simp [S]).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ R) (· ∈ S)))
    change (((PMF.uniformOfFintype R).map _) true).toReal = _
    rw [PMF.toReal_uniformOfFintype_map_apply_true, Finset.dens_eq_card_div_card, hcard_fib,
      hcard R, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast]
  rw [hpOut_true] at hdist
  have hR_pos : (0 : ℝ) < R.ncard := by exact_mod_cast hcard R ▸ Fintype.card_pos (α := R)
  rwa [div_sub' hR_pos.ne', mul_one_div, abs_div, abs_of_pos hR_pos,
    div_le_iff₀ hR_pos] at hdist

private theorem isLittleO_log_two_pow {k : ℕ → ℕ}
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => (n : ℝ)) :
    (fun n => Real.log ((2 ^ k n : ℕ) : ℝ)) =o[atTop] fun n => (n : ℝ) := by
  refine (hk.const_mul_left (Real.log 2)).congr_left fun n => ?_
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  ring

/-- **Bit fibers of sublinear-entropy sumset extractors are `DenseRectangleFree`.** Conditional
reduction step: if `ext n` is eventually a `(k n, k n, ε n)` sumset extractor with `k n = o(n)` and
`ε n ≤ c < 1 / 2`, then `{x | ext n x (j n) = val n}` is `DenseRectangleFree` with threshold
`2 ^ k n`. -/
theorem denseRectangleFree_of_isSumsetExtractor {m k : ℕ → ℕ} {ε : ℕ → ℝ}
    {ext : ∀ n, BitString n → BitString (m n)} (j : ∀ n, Fin (m n)) (val : ℕ → Bool)
    (hext : ∀ᶠ n in atTop, IsSumsetExtractor (ext n) (k n) (k n) (ε n))
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => (n : ℝ))
    (hε : ∃ c < 1 / 2, ∀ᶠ n in atTop, ε n ≤ c) :
    DenseRectangleFree (fun n => {x : BitString n | ext n x (j n) = val n})
      (fun n => 2 ^ k n) :=
  denseRectangleFree_of_eventually_rectangleBias
    (hext.mono fun n hn => rectangleBias_of_isSumsetExtractor hn (j n) (val n))
    (Eventually.of_forall fun _ => Nat.one_le_two_pow) (isLittleO_log_two_pow hk) hε

/-- **Worst-case `(L₃ - δ) n` multiary frontier step from a sumset extractor.** Conditional
reduction step (not an unconditional `P` lower bound): if `ext n` is eventually a
`(k n, k n, ε n)` sumset extractor with `k n = o(n)` and `ε n ≤ c < 1 / 2`, then for every `δ > 0`
and all large `n`, every fan-in-two circuit over any signature `σ` deciding
`{x | ext n x (j n) = val n}` has more than `(1 + 2π / (3 arccos (5 / 6)) - δ) n` multiary gates
(`arity = 2`; constant and unary gates are free). -/
theorem eventually_switched_sub_mul_lt_multiarySize_of_isSumsetExtractor {m k : ℕ → ℕ}
    {ε : ℕ → ℝ} {ext : ∀ n, BitString n → BitString (m n)}
    (j : ∀ n, Fin (m n)) (val : ℕ → Bool)
    (hext : ∀ᶠ n in atTop, IsSumsetExtractor (ext n) (k n) (k n) (ε n))
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => (n : ℝ))
    (hε : ∃ c < 1 / 2, ∀ᶠ n in atTop, ε n ≤ c) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 2 →
        c.Decides I Acc {x : BitString n | ext n x (j n) = val n} →
          (1 + 2 * π / (3 * arccos (5 / 6)) - δ) * n < c.multiarySize :=
  eventually_switched_sub_mul_lt_multiarySize
    (denseRectangleFree_of_isSumsetExtractor j val hext hk hε) hδ

/-- **Average-case `(L₃ - δ) n` multiary frontier step from a sumset extractor.** Conditional
reduction step: if `ext n` is eventually a `(k n, k n, ε n)` sumset extractor with `k n = o(n)`,
then for every `δ > 0` there is `γ > 0` such that, for all large `n`, every fan-in-two circuit
over any signature `σ` with at most `(1 + 2π / (3 arccos (5 / 6)) - δ) n` multiary gates agrees
with `{x | ext n x (j n) = val n}` on at most a `1 / 2 + ε n + exp (-γ n)` fraction of inputs. -/
theorem exists_eventually_agreement_le_of_isSumsetExtractor {m k : ℕ → ℕ} {ε : ℕ → ℝ}
    {ext : ∀ n, BitString n → BitString (m n)} (j : ∀ n, Fin (m n)) (val : ℕ → Bool)
    (hext : ∀ᶠ n in atTop, IsSumsetExtractor (ext n) (k n) (k n) (ε n))
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => (n : ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ γ > 0, ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 2 →
        (c.multiarySize : ℝ) ≤ (1 + 2 * π / (3 * arccos (5 / 6)) - δ) * n →
          agreement {x : BitString n | ext n x (j n) = val n} {x | c.eval I x 0 ∈ Acc} ≤
            1 / 2 + ε n + Real.exp (-γ * n) := by
  obtain ⟨γ, hγ, H⟩ := multiaryAverageCaseBound_switched.{0, v} δ hδ
  refine ⟨γ, hγ, (H Bool (fun n => {x | ext n x (j n) = val n}) (fun n => 2 ^ k n) ε
    (hext.mono fun n hn => rectangleBias_of_isSumsetExtractor hn (j n) (val n))
    (isLittleO_log_two_pow hk)).mono fun n hn σ I Acc c hfan hsize => ?_⟩
  simpa only [neg_mul] using hn σ I Acc c hfan hsize

/-- **Conditional reduction step from a polynomial-time sumset extractor to a language in `P`
requiring `(L₃ - δ) n` multiary gates.** The explicit construction of [Li2023], ECCC TR23-023
revision 1, Theorem 7.13, is not yet formalized (see #7793). Given any
polynomial-time Boolean family `f` whose 1-bit
output is eventually a `(k n, k n, ε n)` sumset extractor with `k n = o(n)` and `ε n ≤ c < 1 / 2`,
`Language.ofSlices f` lies in `P` and its `n`-bit slice requires more than
`(1 + 2π / (3 arccos (5 / 6)) - δ) n` multiary gates over every fan-in-two signature `σ`. -/
theorem mem_P_and_eventually_switched_lt_multiarySize_of_isSumsetExtractor
    {f : ∀ n, BitString n → Bool} {k : ℕ → ℕ} {ε : ℕ → ℝ}
    (hf : Turing.MultiTapeTM.ComputableInPolyTime
      (fun x : List Bool => f x.length (BitString.ofList x.length x))
      Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBool)
    (hext : ∀ᶠ n in atTop,
      IsSumsetExtractor (fun x : BitString n => fun _ : Fin 1 => f n x) (k n) (k n) (ε n))
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => (n : ℝ))
    (hε : ∃ c < 1 / 2, ∀ᶠ n in atTop, ε n ≤ c) :
    (Language.ofSlices f : Set (List Bool)) ∈ Cslib.Complexity.P Turing.MultiTapeTM.encBits ∧
      ∀ δ > 0, ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost 2 →
          c.Decides I Acc {x : BitString n | (Language.ofSlices f).slice n x = true} →
            (1 + 2 * π / (3 * arccos (5 / 6)) - δ) * n < c.multiarySize := by
  refine ⟨Cslib.Complexity.ofSlices_mem_P hf, fun δ hδ => ?_⟩
  exact (eventually_switched_sub_mul_lt_multiarySize_of_isSumsetExtractor.{v}
    (fun _ => 0) (fun _ => true) hext hk hε hδ).mono fun n hn σ I Acc c hfan hdec =>
      hn σ I Acc c hfan (by simpa only [Language.slice_ofSlices] using hdec)

end Cslib.Circuits.Frontier
