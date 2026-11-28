/-
Copyright (c) 2026 Matthew Doty, Vinicius de Padua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Vinicius de Padua
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF.Coin
public import Mathlib.Data.Finset.Basic

import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The von Neumann–Morgenstern expected utility theorem

This module formalizes the von Neumann–Morgenstern expected utility theorem for preferences over
lotteries on a finite nonempty set of outcomes, covering existence, the converse, the full
characterization equivalence, and uniqueness up to positive affine transformation
([vonNeumannMorgenstern1947], [HersteinMilnor1953], [MasColellWhinstonGreen1995]; book and
article locators not verified locally), modeled after the Isabelle/AFP formalization
[ParsertKaliszyk2018].

## Model

* A **lottery** on an outcome set `X : Set α` is a discrete probability distribution `p : PMF α`
  whose support lies in `X` (`lotteriesOn X`).
* The **mixture** `mix a p q` of two lotteries `p, q : PMF α` with weight `a : unitInterval` draws
  from `p` with probability `a` and from `q` with probability `1 - a`, defined by binding
  `Cslib.Probability.PMF.coin a` (avoiding Mathlib's deprecated `PMF.bernoulli`).
* A **preference relation** `rel : PMF α → PMF α → Prop` on `lotteriesOn X` writes `rel p q` for
  "`p` is weakly preferred to `q`" (`p ≽ q`). We define a subset-scoped `IsRationalOn X rel`
  structure rather than reusing `Cslib.GameTheory.SocialChoice.WeakRanking`, since `WeakRanking`
  bundles a total preorder on an entire type whereas lotteries form a subset `lotteriesOn X` of
  `PMF α`.
* For a finite outcome set `X : Finset α` and utility `u : α → ℝ`, `expectedUtility X u p` is
  `∑ x ∈ X, (p x).toReal * u x`, and `IsVNMUtility X rel u` asserts that
  `rel p q ↔ expectedUtility X u q ≤ expectedUtility X u p` for all `p, q ∈ lotteriesOn X`.

## Main definitions

* `Cslib.GameTheory.VonNeumannMorgenstern.lotteriesOn`: lotteries supported on `X`.
* `Cslib.GameTheory.VonNeumannMorgenstern.degenerateLotteriesOn`: point-mass lotteries on `X`.
* `Cslib.GameTheory.VonNeumannMorgenstern.mix`: convex mixture of two lotteries.
* `Cslib.GameTheory.VonNeumannMorgenstern.expectedUtility`: expected utility of a lottery over a
  finite outcome set.
* `Cslib.GameTheory.VonNeumannMorgenstern.strictPref`, `indiff`: strict preference and
  indifference derived from a weak preference relation.
* `Cslib.GameTheory.VonNeumannMorgenstern.IsRationalOn`, `IsIndependentOn`, `IsContinuousOn`,
  `IsArchimedeanOn`: the von Neumann–Morgenstern preference axioms on `lotteriesOn X`.
* `Cslib.GameTheory.VonNeumannMorgenstern.IsVNMUtility`: expected-utility representation of a
  preference relation.

## Main results

* `Cslib.GameTheory.VonNeumannMorgenstern.isContinuousOn_iff_isArchimedeanOn`: equivalence of the
  continuity and Archimedean axioms under rationality and independence.
* `Cslib.GameTheory.VonNeumannMorgenstern.exists_best_overall`,
  `exists_worst_overall`: existence of best and worst lotteries on a finite nonempty outcome set.
* `Cslib.GameTheory.VonNeumannMorgenstern.exists_isVNMUtility`: **von Neumann–Morgenstern
  existence theorem** (AFP `system_U_implies_vNM_utility`; requires `X.Nonempty`).
* `Cslib.GameTheory.VonNeumannMorgenstern.IsVNMUtility.isRationalOn`,
  `IsVNMUtility.isIndependentOn`, `IsVNMUtility.isContinuousOn`: the converse implications (do not
  require `X.Nonempty`).
* `Cslib.GameTheory.VonNeumannMorgenstern.exists_isVNMUtility_iff`: **full characterization**
  (AFP `Von_Neumann_Morgenstern_Utility_Theorem`, `expected_utilty_theorem_form_vnm_utility`;
  requires `X.Nonempty`).
* `Cslib.GameTheory.VonNeumannMorgenstern.IsVNMUtility.exists_posAffine_eq`,
  `isVNMUtility_iff_exists_posAffine_eq`: **uniqueness up to positive affine transformation** (do
  not require `X.Nonempty`).

## References

* [J. von Neumann and O. Morgenstern, *Theory of Games and Economic
  Behavior*][vonNeumannMorgenstern1947] (locator not verified)
* [I. N. Herstein and J. Milnor, *An Axiomatic Approach to Measurable
  Utility*][HersteinMilnor1953] (locator not verified)
* [A. Mas-Colell, M. D. Whinston, and J. R. Green, *Microeconomic
  Theory*][MasColellWhinstonGreen1995] (locator not verified)
* [J. Parsert and C. Kaliszyk, *Von-Neumann-Morgenstern Utility Theorem*][ParsertKaliszyk2018]
-/

public section

namespace Cslib.GameTheory.VonNeumannMorgenstern

open scoped ENNReal unitInterval

variable {α : Type*}

/-! ### Lotteries and mixtures -/

/-- The set of lotteries (discrete probability distributions) supported on `X`. -/
def lotteriesOn (X : Set α) : Set (PMF α) :=
  {p : PMF α | p.support ⊆ X}

@[simp]
theorem mem_lotteriesOn {X : Set α} {p : PMF α} : p ∈ lotteriesOn X ↔ p.support ⊆ X :=
  Iff.rfl

/-- The set of degenerate (point-mass) lotteries on `X`. -/
noncomputable def degenerateLotteriesOn (X : Set α) : Set (PMF α) :=
  PMF.pure '' X

@[simp]
theorem mem_degenerateLotteriesOn {X : Set α} {p : PMF α} :
    p ∈ degenerateLotteriesOn X ↔ ∃ x ∈ X, PMF.pure x = p :=
  Iff.rfl

/-- A point mass `PMF.pure x` is a lottery on `X` iff `x ∈ X`. -/
theorem pure_mem_lotteriesOn_iff {X : Set α} {x : α} :
    PMF.pure x ∈ lotteriesOn X ↔ x ∈ X := by
  simp only [mem_lotteriesOn, PMF.support_pure, Set.singleton_subset_iff]

/-- Every degenerate lottery on `X` lies in `lotteriesOn X`. -/
theorem degenerateLotteriesOn_subset_lotteriesOn (X : Set α) :
    degenerateLotteriesOn X ⊆ lotteriesOn X := by
  rintro _ ⟨x, hx, rfl⟩
  exact pure_mem_lotteriesOn_iff.mpr hx

/-- `PMF.pure` restricts to a bijection between `X` and `degenerateLotteriesOn X`
(AFP `card_degen_lotteries_equals_outcomes`). -/
theorem bijOn_pure_degenerateLotteriesOn (X : Set α) :
    Set.BijOn PMF.pure X (degenerateLotteriesOn X) :=
  ⟨Set.mapsTo_image PMF.pure X,
    fun _ _ _ _ h => by
      have hsupp := congrArg PMF.support h
      simp only [PMF.support_pure, Set.singleton_eq_singleton_iff] at hsupp
      exact hsupp,
    Set.surjOn_image PMF.pure X⟩

/-- The convex mixture `a · p + (1 - a) · q` of two lotteries `p` and `q` with weight `a ∈ [0, 1]`,
defined by binding a Bernoulli coin `Cslib.Probability.PMF.coin a`
(AFP `PMF_Composition.mix_pmf`). -/
noncomputable def mix (a : I) (p q : PMF α) : PMF α :=
  (Cslib.Probability.PMF.coin a).bind fun b => if b then p else q

theorem mix_eq_coin_bind (a : I) (p q : PMF α) :
    mix a p q = (Cslib.Probability.PMF.coin a).bind fun b => if b then p else q := by
  rfl

/-- Pointwise extended-nonnegative mass of a mixture (`ℝ≥0∞` counterpart of AFP
`PMF_Composition.pmf_mix`). -/
theorem mix_apply (a : I) (p q : PMF α) (x : α) :
    mix a p q x = ENNReal.ofReal a * p x + ENNReal.ofReal (1 - a) * q x := by
  rw [mix, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [Cslib.Probability.PMF.coin_apply, ↓reduceIte, Bool.false_eq_true]

/-- Pointwise real-valued mass of a mixture (AFP `PMF_Composition.pmf_mix`). -/
theorem mix_apply_toReal (a : I) (p q : PMF α) (x : α) :
    (mix a p q x).toReal = (a : ℝ) * (p x).toReal + (1 - a) * (q x).toReal := by
  rw [mix, Cslib.Probability.PMF.bind_apply_toReal, Fintype.sum_bool]
  simp only [Cslib.Probability.PMF.coin_apply_toReal, ↓reduceIte, Bool.false_eq_true]

private theorem pmf_ext_toReal {p q : PMF α} (h : ∀ x, (p x).toReal = (q x).toReal) : p = q :=
  PMF.ext fun x =>
    (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top x) (q.apply_ne_top x)).mp (h x)

private theorem mem_support_iff_toReal_pos {p : PMF α} {x : α} :
    x ∈ p.support ↔ 0 < (p x).toReal := by
  rw [p.mem_support_iff, ENNReal.toReal_pos_iff]
  exact ⟨fun h => ⟨pos_iff_ne_zero.mpr h, lt_top_iff_ne_top.mpr (p.apply_ne_top x)⟩,
    fun h => ne_of_gt h.1⟩

/-- Mixing with weight `0` returns the second lottery (AFP `pmf_mix_0`). -/
@[simp]
theorem mix_zero (p q : PMF α) : mix 0 p q = q :=
  pmf_ext_toReal fun x => by
    simp only [mix_apply_toReal, Set.Icc.coe_zero, zero_mul, sub_zero, one_mul, zero_add]

/-- Mixing with weight `1` returns the first lottery (AFP `pmf_mix_1`). -/
@[simp]
theorem mix_one (p q : PMF α) : mix 1 p q = p :=
  pmf_ext_toReal fun x => by
    simp only [mix_apply_toReal, Set.Icc.coe_one, one_mul, sub_self, zero_mul, add_zero]

/-- Mixing a lottery with itself leaves it unchanged (AFP `set_pmf_mix_eq`). -/
@[simp]
theorem mix_self (a : I) (p : PMF α) : mix a p p = p :=
  pmf_ext_toReal fun x => by
    rw [mix_apply_toReal]
    ring

/-- Symmetry of lottery mixtures (AFP `pmf_inverse_switch_eqals`). -/
theorem mix_symm (a : I) (p q : PMF α) : mix a p q = mix (σ a) q p :=
  pmf_ext_toReal fun x => by
    rw [mix_apply_toReal, mix_apply_toReal, unitInterval.coe_symm_eq]
    ring

/-- Reduction of a compound mixture of two mixtures of `p` and `q` to a single mixture. -/
private theorem mix_mix_eq (a b c : I) (p q : PMF α) :
    mix a (mix b p q) (mix c p q) =
      mix ⟨(a : ℝ) * b + (1 - a) * c,
        ⟨add_nonneg (mul_nonneg (unitInterval.nonneg a) (unitInterval.nonneg b))
            (mul_nonneg (unitInterval.one_sub_nonneg a) (unitInterval.nonneg c)),
          by nlinarith [unitInterval.nonneg a, unitInterval.le_one a,
            unitInterval.nonneg b, unitInterval.le_one b,
            unitInterval.nonneg c, unitInterval.le_one c]⟩⟩ p q :=
  pmf_ext_toReal fun x => by
    simp only [mix_apply_toReal]
    ring

/-- Iterated mixture on the left: `mix a (mix b p q) q = mix (a * b) p q`
(AFP `product_mix_pmf_prob_distrib`). -/
theorem mix_mix_left (a b : I) (p q : PMF α) : mix a (mix b p q) q = mix (a * b) p q :=
  pmf_ext_toReal fun x => by
    simp only [mix_apply_toReal, Set.Icc.coe_mul]
    ring

/-- Iterated mixture on the right: `mix a p (mix b p q) = mix (σ (σ a * σ b)) p q`. -/
theorem mix_mix_right (a b : I) (p q : PMF α) :
    mix a p (mix b p q) = mix (σ (σ a * σ b)) p q :=
  pmf_ext_toReal fun x => by
    simp only [mix_apply_toReal, unitInterval.coe_symm_eq, Set.Icc.coe_mul]
    ring

/-- The support of a mixture is contained in the union of the supports. -/
theorem support_mix_subset (a : I) (p q : PMF α) :
    (mix a p q).support ⊆ p.support ∪ q.support := by
  intro x hx
  rw [mem_support_iff_toReal_pos, mix_apply_toReal] at hx
  by_contra h
  rw [Set.mem_union, not_or, mem_support_iff_toReal_pos, mem_support_iff_toReal_pos] at h
  have hp0 : (p x).toReal = 0 := le_antisymm (not_lt.mp h.1) ENNReal.toReal_nonneg
  have hq0 : (q x).toReal = 0 := le_antisymm (not_lt.mp h.2) ENNReal.toReal_nonneg
  rw [hp0, hq0] at hx
  linarith

/-- The support of a proper mixture (`0 < a < 1`) is the union of the supports
(AFP `set_pmf_mix`). -/
theorem support_mix {a : I} (ha0 : 0 < (a : ℝ)) (ha1 : (a : ℝ) < 1) (p q : PMF α) :
    (mix a p q).support = p.support ∪ q.support := by
  refine Set.Subset.antisymm (support_mix_subset a p q) fun x hx => ?_
  rw [mem_support_iff_toReal_pos, mix_apply_toReal]
  have h1a : 0 < 1 - (a : ℝ) := sub_pos.mpr ha1
  rcases hx with hp | hq
  · rw [mem_support_iff_toReal_pos] at hp
    have h1 : 0 < (a : ℝ) * (p x).toReal := mul_pos ha0 hp
    have h2 : 0 ≤ (1 - (a : ℝ)) * (q x).toReal :=
      mul_nonneg (le_of_lt h1a) ENNReal.toReal_nonneg
    linarith
  · rw [mem_support_iff_toReal_pos] at hq
    have h1 : 0 ≤ (a : ℝ) * (p x).toReal := mul_nonneg (le_of_lt ha0) ENNReal.toReal_nonneg
    have h2 : 0 < (1 - (a : ℝ)) * (q x).toReal := mul_pos h1a hq
    linarith

/-- `lotteriesOn X` is closed under mixing (AFP `mix_pmf_in_lotteries`). -/
theorem mix_mem_lotteriesOn {X : Set α} {p q : PMF α} (a : I)
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) : mix a p q ∈ lotteriesOn X :=
  (support_mix_subset a p q).trans (Set.union_subset hp hq)

/-- Every lottery `p` assigning probability strictly between `0` and `1` to `x` decomposes as a
proper mixture of `PMF.pure x` and a lottery supported on `p.support \ {x}`. -/
private theorem exists_mix_pure_of_mem_support {p : PMF α} {x : α}
    (hx : x ∈ p.support) (hpx : p x ≠ 1) :
    ∃ (a : I) (q : PMF α), q.support = p.support \ {x} ∧ p = mix a (PMF.pure x) q := by
  classical
  have hlt1 : p x < 1 := lt_of_le_of_ne (p.coe_le_one x) hpx
  set r : ℝ≥0∞ := 1 - p x
  have hr0 : r ≠ 0 := tsub_pos_iff_lt.mpr hlt1 |>.ne'
  have hrtop : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  let f : α → ℝ≥0∞ := fun y => if y = x then 0 else p y / r
  have hsum_rest : (∑' y, if y = x then (0 : ℝ≥0∞) else p y) = r := by
    have hsplit : p x + ∑' y, (if y = x then (0 : ℝ≥0∞) else p y) = 1 := by
      have h1 : (∑' y, if y = x then p x else (0 : ℝ≥0∞)) = p x := by
        rw [tsum_ite_eq]
      have hadd :
          (∑' y, if y = x then p x else (0 : ℝ≥0∞)) +
            (∑' y, if y = x then (0 : ℝ≥0∞) else p y) = ∑' y, p y := by
        rw [← tsum_add]
        refine tsum_congr fun y => ?_
        by_cases hy : y = x <;> simp [hy]
      rw [h1, p.tsum_coe] at hadd
      exact hadd
    rw [show r = 1 - p x from rfl, ← hsplit, ENNReal.add_sub_cancel_left (p.apply_ne_top x)]
  have hsum_f : HasSum f 1 := by
    rw [CompleteLattice.summable.hasSum_iff]
    have hdiv : (∑' y, f y) = (∑' y, if y = x then (0 : ℝ≥0∞) else p y) / r := by
      simp only [f, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun y => ?_
      by_cases hy : y = x <;> simp [hy]
    rw [hdiv, hsum_rest, ENNReal.div_self hr0 hrtop]
  let q : PMF α := ⟨f, hsum_f⟩
  let a : I := ⟨(p x).toReal, ENNReal.toReal_nonneg,
    Cslib.Probability.PMF.toReal_apply_le_one p x⟩
  have hq_supp : q.support = p.support \ {x} := by
    ext y
    simp only [PMF.mem_support_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    change f y ≠ 0 ↔ p y ≠ 0 ∧ y ≠ x
    by_cases hy : y = x
    · simp [f, hy]
    · simp only [f, hy, ↓reduceIte, ne_eq, ENNReal.div_eq_zero_iff, hrtop, or_false,
        not_false_eq_true, and_true]
  refine ⟨a, q, hq_supp, pmf_ext_toReal fun y => ?_⟩
  rw [mix_apply_toReal]
  have hr_toReal : r.toReal = 1 - (p x).toReal := by
    rw [ENNReal.toReal_sub_of_le (p.coe_le_one x) ENNReal.one_ne_top, ENNReal.toReal_one]
  have hr_pos : 0 < 1 - (p x).toReal := by
    rw [← hr_toReal]
    exact ENNReal.toReal_pos hr0 hrtop
  by_cases hy : y = x
  · subst hy
    have hqx : q y = 0 := by
      change f y = 0
      simp [f]
    simp only [a, PMF.pure_apply_self, ENNReal.toReal_one, mul_one, hqx, ENNReal.toReal_zero,
      mul_zero, add_zero]
  · have hqy : (q y).toReal = (p y).toReal / (1 - (p x).toReal) := by
      change (f y).toReal = _
      simp only [f, hy, ↓reduceIte, ENNReal.toReal_div, hr_toReal]
    simp only [a, PMF.pure_apply_of_ne x y hy, ENNReal.toReal_zero, mul_zero, zero_add, hqy]
    field_simp [ne_of_gt hr_pos]

/-- Expected utility of a lottery `p` with respect to utility function `u` over a finite outcome
set `X`. -/
@[expose] noncomputable def expectedUtility (X : Finset α) (u : α → ℝ) (p : PMF α) : ℝ :=
  ∑ x ∈ X, (p x).toReal * u x

/-- Real-valued probabilities of a lottery supported on `X : Finset α` sum to `1` over `X`. -/
theorem sum_toReal_eq_one_of_mem_lotteriesOn {X : Finset α} {p : PMF α}
    (hp : p ∈ lotteriesOn (X : Set α)) : ∑ x ∈ X, (p x).toReal = 1 := by
  rw [← Cslib.Probability.PMF.tsum_toReal p]
  refine (tsum_eq_sum fun x hx => ?_).symm
  have hx' : x ∉ p.support := fun h => hx (hp h)
  rw [PMF.mem_support_iff, not_not] at hx'
  simp [hx']

/-- Expected utility of a degenerate lottery `PMF.pure x` for `x ∈ X` equals `u x`. -/
@[simp]
theorem expectedUtility_pure {X : Finset α} (u : α → ℝ) {x : α} (hx : x ∈ X) :
    expectedUtility X u (PMF.pure x) = u x := by
  classical
  rw [expectedUtility, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [PMF.pure_apply_of_ne x y hy]
  · intro h
    exact absurd hx h

/-- Expected utility is affine in mixtures (AFP `expected_value_mix_pmf`). -/
theorem expectedUtility_mix (X : Finset α) (u : α → ℝ) (a : I) (p q : PMF α) :
    expectedUtility X u (mix a p q) =
      (a : ℝ) * expectedUtility X u p + (1 - a) * expectedUtility X u q := by
  simp only [expectedUtility, mix_apply_toReal, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- Expected utility commutes with positive or arbitrary affine transformations of `u` for
lotteries supported on `X`. -/
theorem expectedUtility_affine {X : Finset α} (u : α → ℝ) (a b : ℝ) {p : PMF α}
    (hp : p ∈ lotteriesOn (X : Set α)) :
    expectedUtility X (fun x => a * u x + b) p = a * expectedUtility X u p + b := by
  have hsum : ∑ x ∈ X, (p x).toReal = 1 := sum_toReal_eq_one_of_mem_lotteriesOn hp
  calc
    expectedUtility X (fun x => a * u x + b) p
      = ∑ x ∈ X, (a * ((p x).toReal * u x) + (p x).toReal * b) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
    _ = a * (∑ x ∈ X, (p x).toReal * u x) + (∑ x ∈ X, (p x).toReal) * b := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = a * expectedUtility X u p + b := by rw [hsum, one_mul]; rfl

/-! ### Preference relations and von Neumann–Morgenstern axioms -/

/-- Strict preference induced by weak preference `rel`: `p ≻ q` iff `p ≽ q` and `¬ (q ≽ p)`. -/
@[expose] def strictPref (rel : PMF α → PMF α → Prop) (p q : PMF α) : Prop :=
  rel p q ∧ ¬ rel q p

/-- Indifference induced by weak preference `rel`: `p ∼ q` iff `p ≽ q` and `q ≽ p`. -/
@[expose] def indiff (rel : PMF α → PMF α → Prop) (p q : PMF α) : Prop :=
  rel p q ∧ rel q p

@[simp]
theorem strictPref_iff {rel : PMF α → PMF α → Prop} {p q : PMF α} :
    strictPref rel p q ↔ rel p q ∧ ¬ rel q p :=
  Iff.rfl

@[simp]
theorem indiff_iff {rel : PMF α → PMF α → Prop} {p q : PMF α} :
    indiff rel p q ↔ rel p q ∧ rel q p :=
  Iff.rfl

theorem indiff_symm {rel : PMF α → PMF α → Prop} {p q : PMF α}
    (h : indiff rel p q) : indiff rel q p :=
  ⟨h.2, h.1⟩

/-- A preference relation `rel` is **rational** on `lotteriesOn X` if it is complete and
transitive on `lotteriesOn X` (AFP `rational_preference`). -/
structure IsRationalOn (X : Set α) (rel : PMF α → PMF α → Prop) : Prop where
  /-- Any two lotteries on `X` are comparable. -/
  complete : ∀ ⦃p⦄, p ∈ lotteriesOn X → ∀ ⦃q⦄, q ∈ lotteriesOn X → rel p q ∨ rel q p
  /-- Weak preference is transitive on `lotteriesOn X`. -/
  trans : ∀ ⦃p⦄, p ∈ lotteriesOn X → ∀ ⦃q⦄, q ∈ lotteriesOn X → ∀ ⦃r⦄, r ∈ lotteriesOn X →
    rel p q → rel q r → rel p r

namespace IsRationalOn

variable {X : Set α} {rel : PMF α → PMF α → Prop}

theorem refl (hR : IsRationalOn X rel) {p : PMF α} (hp : p ∈ lotteriesOn X) : rel p p :=
  (hR.complete hp hp).elim id id

theorem indiff_refl (hR : IsRationalOn X rel) {p : PMF α} (hp : p ∈ lotteriesOn X) :
    indiff rel p p :=
  ⟨hR.refl hp, hR.refl hp⟩

theorem indiff_trans (hR : IsRationalOn X rel) {p q r : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hr : r ∈ lotteriesOn X)
    (h1 : indiff rel p q) (h2 : indiff rel q r) : indiff rel p r :=
  ⟨hR.trans hp hq hr h1.1 h2.1, hR.trans hr hq hp h2.2 h1.2⟩

theorem strictPref_of_strictPref_of_rel (hR : IsRationalOn X rel) {p q r : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hr : r ∈ lotteriesOn X)
    (h1 : strictPref rel p q) (h2 : rel q r) : strictPref rel p r :=
  ⟨hR.trans hp hq hr h1.1 h2, fun hrp => h1.2 (hR.trans hq hr hp h2 hrp)⟩

theorem strictPref_of_rel_of_strictPref (hR : IsRationalOn X rel) {p q r : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hr : r ∈ lotteriesOn X)
    (h1 : rel p q) (h2 : strictPref rel q r) : strictPref rel p r :=
  ⟨hR.trans hp hq hr h1 h2.1, fun hrp => h2.2 (hR.trans hr hp hq hrp h1)⟩

theorem strictPref_trans (hR : IsRationalOn X rel) {p q r : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hr : r ∈ lotteriesOn X)
    (h1 : strictPref rel p q) (h2 : strictPref rel q r) : strictPref rel p r :=
  hR.strictPref_of_strictPref_of_rel hp hq hr h1 h2.1

private theorem flip (hR : IsRationalOn X rel) : IsRationalOn X (fun p q => rel q p) where
  complete _ hp _ hq := (hR.complete hp hq).symm
  trans _ hp _ hq _ hr h1 h2 := hR.trans hr hq hp h2 h1

end IsRationalOn

/-- **Independence axiom** (AFP `independent_vnm`; [vonNeumannMorgenstern1947],
[MasColellWhinstonGreen1995]): mixing with any third lottery `r` using positive weight `a ∈ (0, 1]`
preserves and reflects weak preference. -/
@[expose] def IsIndependentOn (X : Set α) (rel : PMF α → PMF α → Prop) : Prop :=
  ∀ ⦃p⦄, p ∈ lotteriesOn X → ∀ ⦃q⦄, q ∈ lotteriesOn X → ∀ ⦃r⦄, r ∈ lotteriesOn X →
    ∀ a : I, 0 < (a : ℝ) → (rel p q ↔ rel (mix a p r) (mix a q r))

/-- Independence over `a ∈ (0, 1]` is equivalent to independence over proper weights
`a ∈ (0, 1)`. -/
theorem isIndependentOn_iff_Ioo {X : Set α} {rel : PMF α → PMF α → Prop} :
    IsIndependentOn X rel ↔
      ∀ ⦃p⦄, p ∈ lotteriesOn X → ∀ ⦃q⦄, q ∈ lotteriesOn X → ∀ ⦃r⦄, r ∈ lotteriesOn X →
        ∀ a : I, 0 < (a : ℝ) → (a : ℝ) < 1 → (rel p q ↔ rel (mix a p r) (mix a q r)) := by
  refine ⟨fun hI p hp q hq r hr a ha0 _ => hI hp hq hr a ha0, fun hI p hp q hq r hr a ha0 => ?_⟩
  rcases eq_or_lt_of_le a.property.2 with ha1 | ha1
  · have ha_eq : a = 1 := Subtype.ext ha1
    rw [ha_eq, mix_one, mix_one]
  · exact hI hp hq hr a ha0 ha1

namespace IsIndependentOn

variable {X : Set α} {rel : PMF α → PMF α → Prop}

private theorem flip (hI : IsIndependentOn X rel) : IsIndependentOn X (fun p q => rel q p) :=
  fun _ hp _ hq _ hr a ha => hI hq hp hr a ha

/-- Right-side independence: mixing on the right with weight `a < 1` preserves and reflects weak
preference. -/
theorem mix_right_iff (hI : IsIndependentOn X rel) {p q r : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hr : r ∈ lotteriesOn X)
    {a : I} (ha : (a : ℝ) < 1) : rel p q ↔ rel (mix a r p) (mix a r q) := by
  rw [mix_symm a r p, mix_symm a r q]
  exact hI hp hq hr (σ a) (by rw [unitInterval.coe_symm_eq]; linarith)

/-- Left-side weak preservation for all weights `a ∈ [0, 1]`
(AFP `independent_vnmD4`, `mix_pmf_preferred_independence`). -/
theorem mix_left_of_rel (hR : IsRationalOn X rel) (hI : IsIndependentOn X rel) {p q r : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hr : r ∈ lotteriesOn X)
    (a : I) (h : rel p q) : rel (mix a p r) (mix a q r) := by
  rcases eq_or_lt_of_le a.property.1 with ha0 | ha0
  · have ha_eq : a = 0 := Subtype.ext ha0.symm
    rw [ha_eq, mix_zero, mix_zero]
    exact hR.refl hr
  · exact (hI hp hq hr a ha0).mp h

/-- Right-side weak preservation for all weights `a ∈ [0, 1]`
(right-side counterpart of AFP `mix_pmf_preferred_independence`). -/
theorem mix_right_of_rel (hR : IsRationalOn X rel) (hI : IsIndependentOn X rel) {p q r : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hr : r ∈ lotteriesOn X)
    (a : I) (h : rel p q) : rel (mix a r p) (mix a r q) := by
  rw [mix_symm a r p, mix_symm a r q]
  exact hI.mix_left_of_rel hR hp hq hr (σ a) h

/-- Left-side independence for strict preference
(AFP `mix_pmf_strict_preferred_independence`). -/
theorem mix_strictPref_left_iff (hI : IsIndependentOn X rel) {p q r : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hr : r ∈ lotteriesOn X)
    {a : I} (ha : 0 < (a : ℝ)) :
    strictPref rel p q ↔ strictPref rel (mix a p r) (mix a q r) :=
  and_congr (hI hp hq hr a ha) (not_congr (hI hq hp hr a ha))

/-- Right-side independence for strict preference. -/
theorem mix_strictPref_right_iff (hI : IsIndependentOn X rel) {p q r : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hr : r ∈ lotteriesOn X)
    {a : I} (ha : (a : ℝ) < 1) :
    strictPref rel p q ↔ strictPref rel (mix a r p) (mix a r q) :=
  and_congr (hI.mix_right_iff hp hq hr ha) (not_congr (hI.mix_right_iff hq hp hr ha))

/-- Left-side independence for indifference (AFP `approx_imp_approx_ind`). -/
theorem mix_indiff_left_iff (hI : IsIndependentOn X rel) {p q r : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hr : r ∈ lotteriesOn X)
    {a : I} (ha : 0 < (a : ℝ)) :
    indiff rel p q ↔ indiff rel (mix a p r) (mix a q r) :=
  and_congr (hI hp hq hr a ha) (hI hq hp hr a ha)

/-- Right-side independence for indifference. -/
theorem mix_indiff_right_iff (hI : IsIndependentOn X rel) {p q r : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hr : r ∈ lotteriesOn X)
    {a : I} (ha : (a : ℝ) < 1) :
    indiff rel p q ↔ indiff rel (mix a r p) (mix a r q) :=
  and_congr (hI.mix_right_iff hp hq hr ha) (hI.mix_right_iff hq hp hr ha)

/-- Mixing is monotone in both lottery arguments simultaneously. -/
theorem mix_rel_congr (hR : IsRationalOn X rel) (hI : IsIndependentOn X rel)
    {p p' q q' : PMF α} (hp : p ∈ lotteriesOn X) (hp' : p' ∈ lotteriesOn X)
    (hq : q ∈ lotteriesOn X) (hq' : q' ∈ lotteriesOn X) (a : I)
    (hpp' : rel p p') (hqq' : rel q q') : rel (mix a p q) (mix a p' q') :=
  hR.trans (mix_mem_lotteriesOn a hp hq) (mix_mem_lotteriesOn a hp' hq)
    (mix_mem_lotteriesOn a hp' hq')
    (hI.mix_left_of_rel hR hp hp' hq a hpp')
    (hI.mix_right_of_rel hR hq hq' hp' a hqq')

/-- Mixing preserves indifference in both lottery arguments simultaneously. -/
theorem mix_indiff_congr (hR : IsRationalOn X rel) (hI : IsIndependentOn X rel)
    {p p' q q' : PMF α} (hp : p ∈ lotteriesOn X) (hp' : p' ∈ lotteriesOn X)
    (hq : q ∈ lotteriesOn X) (hq' : q' ∈ lotteriesOn X) (a : I)
    (hpp' : indiff rel p p') (hqq' : indiff rel q q') :
    indiff rel (mix a p q) (mix a p' q') :=
  ⟨hI.mix_rel_congr hR hp hp' hq hq' a hpp'.1 hqq'.1,
    hI.mix_rel_congr hR hp' hp hq' hq a hpp'.2 hqq'.2⟩

/-- Monotonicity of mixtures in the weight when `p ≻ q`: a strictly larger weight on `p` yields a
strictly preferred mixture. -/
private theorem mix_strictPref_mix_of_lt (hI : IsIndependentOn X rel) {p q : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hpq : strictPref rel p q)
    {a b : I} (hba : (b : ℝ) < a) : strictPref rel (mix a p q) (mix b p q) := by
  have ha0 : 0 < (a : ℝ) := lt_of_le_of_lt b.property.1 hba
  have hmix_q : strictPref rel (mix a p q) q := by
    simpa only [mix_self] using (hI.mix_strictPref_left_iff hp hq hq ha0).mp hpq
  let t : I := ⟨(b : ℝ) / a, div_nonneg b.property.1 (le_of_lt ha0),
    (div_le_one ha0).mpr (le_of_lt hba)⟩
  have ht1 : (t : ℝ) < 1 := (div_lt_one ha0).mpr hba
  have hmix_eq : mix t (mix a p q) q = mix b p q := by
    rw [mix_mix_left]
    congr 1
    exact Subtype.ext (div_mul_cancel₀ (b : ℝ) (ne_of_gt ha0))
  have hstrict := (hI.mix_strictPref_right_iff (mix_mem_lotteriesOn a hp hq) hq
    (mix_mem_lotteriesOn a hp hq) ht1).mp hmix_q
  simpa only [mix_self, hmix_eq] using hstrict

/-- Monotonicity of mixtures in the weight: when `p ≻ q`, `mix a p q ≽ mix b p q ↔ b ≤ a`. -/
theorem mix_rel_mix_iff (hR : IsRationalOn X rel) (hI : IsIndependentOn X rel) {p q : PMF α}
    (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hpq : strictPref rel p q)
    (a b : I) : rel (mix a p q) (mix b p q) ↔ (b : ℝ) ≤ a := by
  refine ⟨fun h => ?_, fun hba => ?_⟩
  · by_contra hab
    exact (hI.mix_strictPref_mix_of_lt hp hq hpq (not_le.mp hab)).2 h
  · rcases eq_or_lt_of_le hba with hEq | hLt
    · rw [Subtype.ext hEq]
      exact hR.refl (mix_mem_lotteriesOn a hp hq)
    · exact (hI.mix_strictPref_mix_of_lt hp hq hpq hLt).1

/-- Strict monotonicity of mixtures in the weight: when `p ≻ q`,
`mix a p q ≻ mix b p q ↔ b < a`. -/
theorem mix_strictPref_mix_iff (hI : IsIndependentOn X rel)
    {p q : PMF α} (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hpq : strictPref rel p q)
    (a b : I) : strictPref rel (mix a p q) (mix b p q) ↔ (b : ℝ) < a := by
  refine ⟨fun h => ?_, hI.mix_strictPref_mix_of_lt hp hq hpq⟩
  rcases lt_trichotomy (b : ℝ) a with hlt | heq | hgt
  · exact hlt
  · exfalso
    rw [Subtype.ext heq] at h
    exact h.2 h.1
  · exact absurd (hI.mix_strictPref_mix_of_lt hp hq hpq hgt).1 h.2

/-- Uniqueness of indifference weights: when `p ≻ q`, `mix a p q ∼ mix b p q ↔ a = b`. -/
theorem mix_indiff_mix_iff (hR : IsRationalOn X rel) (hI : IsIndependentOn X rel)
    {p q : PMF α} (hp : p ∈ lotteriesOn X) (hq : q ∈ lotteriesOn X) (hpq : strictPref rel p q)
    (a b : I) : indiff rel (mix a p q) (mix b p q) ↔ a = b := by
  rw [indiff_iff, hI.mix_rel_mix_iff hR hp hq hpq, hI.mix_rel_mix_iff hR hp hq hpq]
  exact ⟨fun ⟨hba, hab⟩ => Subtype.ext (le_antisymm hab hba),
    fun h => by subst h; exact ⟨le_rfl, le_rfl⟩⟩

end IsIndependentOn

/-- **Continuity axiom** (indifference solvability; AFP `continuous_vnm`): whenever
`p ≽ q ≽ r`, some mixture of `p` and `r` is indifferent to `q`. Under `IsRationalOn` and
`IsIndependentOn`, this is equivalent to the closed-set mixture-continuity axiom of
[HersteinMilnor1953] and [MasColellWhinstonGreen1995] (and to `IsArchimedeanOn`). -/
@[expose] def IsContinuousOn (X : Set α) (rel : PMF α → PMF α → Prop) : Prop :=
  ∀ ⦃p⦄, p ∈ lotteriesOn X → ∀ ⦃q⦄, q ∈ lotteriesOn X → ∀ ⦃r⦄, r ∈ lotteriesOn X →
    rel p q → rel q r → ∃ a : I, indiff rel (mix a p r) q

/-- **Archimedean axiom** (order-Archimedean form; [vonNeumannMorgenstern1947]): whenever
`p ≻ q ≻ r`, some proper mixture of `p` and `r` is strictly preferred to `q` and some proper
mixture of `p` and `r` is strictly worse than `q`. -/
@[expose] def IsArchimedeanOn (X : Set α) (rel : PMF α → PMF α → Prop) : Prop :=
  ∀ ⦃p⦄, p ∈ lotteriesOn X → ∀ ⦃q⦄, q ∈ lotteriesOn X → ∀ ⦃r⦄, r ∈ lotteriesOn X →
    strictPref rel p q → strictPref rel q r →
      (∃ a : I, 0 < (a : ℝ) ∧ (a : ℝ) < 1 ∧ strictPref rel (mix a p r) q) ∧
      (∃ b : I, 0 < (b : ℝ) ∧ (b : ℝ) < 1 ∧ strictPref rel q (mix b p r))

/-- Under rationality and independence, the continuity axiom and the Archimedean axiom are
equivalent. -/
theorem isContinuousOn_iff_isArchimedeanOn {X : Set α} {rel : PMF α → PMF α → Prop}
    (hR : IsRationalOn X rel) (hI : IsIndependentOn X rel) :
    IsContinuousOn X rel ↔ IsArchimedeanOn X rel := by
  refine ⟨fun hC p hp q hq r hr hpq hqr => ?_, fun hA p hp q hq r hr hpq hqr => ?_⟩
  · obtain ⟨c, hc⟩ := hC hp hq hr hpq.1 hqr.1
    have hpr : strictPref rel p r := hR.strictPref_trans hp hq hr hpq hqr
    have hc1 : (c : ℝ) < 1 := by
      refine lt_of_le_of_ne c.property.2 fun heq => hpq.2 ?_
      have hc' : c = 1 := Subtype.ext heq
      rw [hc', mix_one] at hc
      exact hc.2
    have hc0 : 0 < (c : ℝ) := by
      refine lt_of_le_of_ne c.property.1 fun heq => hqr.2 ?_
      have hc' : c = 0 := Subtype.ext heq.symm
      rw [hc', mix_zero] at hc
      exact hc.1
    let a : I := ⟨((c : ℝ) + 1) / 2, by linarith, by linarith⟩
    let b : I := ⟨(c : ℝ) / 2, by linarith, by linarith⟩
    refine ⟨⟨a, by dsimp [a]; linarith, by dsimp [a]; linarith, ?_⟩,
      ⟨b, by dsimp [b]; linarith, by dsimp [b]; linarith, ?_⟩⟩
    · have hca : (c : ℝ) < a := by dsimp [a]; linarith
      exact hR.strictPref_of_strictPref_of_rel (mix_mem_lotteriesOn a hp hr)
        (mix_mem_lotteriesOn c hp hr) hq (hI.mix_strictPref_mix_of_lt hp hr hpr hca) hc.1
    · have hbc : (b : ℝ) < c := by dsimp [b]; linarith
      exact hR.strictPref_of_rel_of_strictPref hq (mix_mem_lotteriesOn c hp hr)
        (mix_mem_lotteriesOn b hp hr) hc.2 (hI.mix_strictPref_mix_of_lt hp hr hpr hbc)
  · by_cases hqp : rel q p
    · exact ⟨1, by rw [mix_one]; exact ⟨hpq, hqp⟩⟩
    by_cases hrq : rel r q
    · exact ⟨0, by rw [mix_zero]; exact ⟨hrq, hqr⟩⟩
    have hspq : strictPref rel p q := ⟨hpq, hqp⟩
    have hsqr : strictPref rel q r := ⟨hqr, hrq⟩
    have hspr : strictPref rel p r := hR.strictPref_trans hp hq hr hspq hsqr
    let S : Set ℝ := {t : ℝ | ∃ a : I, (a : ℝ) = t ∧ rel q (mix a p r)}
    have h0S : (0 : ℝ) ∈ S := ⟨0, rfl, by rw [mix_zero]; exact hqr⟩
    have hS_bdd : BddAbove S := ⟨1, fun t ⟨a, hat, _⟩ => hat ▸ a.property.2⟩
    let s : ℝ := sSup S
    have hs0 : 0 ≤ s := le_csSup hS_bdd h0S
    have hs1 : s ≤ 1 := csSup_le ⟨0, h0S⟩ fun t ⟨a, hat, _⟩ => hat ▸ a.property.2
    let astar : I := ⟨s, hs0, hs1⟩
    have hastar_mem : mix astar p r ∈ lotteriesOn X := mix_mem_lotteriesOn astar hp hr
    have hnot_above : ¬ strictPref rel (mix astar p r) q := by
      intro hgt
      have hs_pos : 0 < (astar : ℝ) := by
        refine lt_of_le_of_ne hs0 fun heq => hgt.2 ?_
        have h0 : astar = 0 := Subtype.ext heq.symm
        rw [h0, mix_zero]
        exact hqr
      obtain ⟨⟨b, hb0, hb1, hbmix⟩, _⟩ := hA hastar_mem hq hr hgt hsqr
      rw [mix_mix_left] at hbmix
      have hba_lt : ((b * astar : I) : ℝ) < s := by
        change (b : ℝ) * astar < astar
        nlinarith
      obtain ⟨t, ⟨c, hct, hqc⟩, hlt_t⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ hba_lt
      rw [← hct] at hlt_t
      have hcb : strictPref rel (mix c p r) (mix (b * astar) p r) :=
        hI.mix_strictPref_mix_of_lt hp hr hspr hlt_t
      have hcq : strictPref rel (mix c p r) q :=
        hR.strictPref_trans (mix_mem_lotteriesOn c hp hr)
          (mix_mem_lotteriesOn (b * astar) hp hr) hq hcb hbmix
      exact hcq.2 hqc
    have hnot_below : ¬ strictPref rel q (mix astar p r) := by
      intro hlt
      have hs_lt1 : (astar : ℝ) < 1 := by
        refine lt_of_le_of_ne hs1 fun heq => hlt.2 ?_
        have h1 : astar = 1 := Subtype.ext heq
        rw [h1, mix_one]
        exact hpq
      obtain ⟨_, ⟨b, hb0, hb1, hbmix⟩⟩ := hA hp hq hastar_mem hspq hlt
      rw [mix_mix_right] at hbmix
      set w : I := σ (σ b * σ astar)
      have hwS : (w : ℝ) ∈ S := ⟨w, rfl, hbmix.1⟩
      have hw_le : (w : ℝ) ≤ s := le_csSup hS_bdd hwS
      have hw_gt : s < (w : ℝ) := by
        change (astar : ℝ) < (σ (σ b * σ astar) : ℝ)
        simp only [unitInterval.coe_symm_eq, Set.Icc.coe_mul]
        nlinarith
      linarith
    refine ⟨astar, ?_⟩
    rcases hR.complete hastar_mem hq with h1 | h2
    · refine ⟨h1, ?_⟩
      by_contra h2
      exact hnot_above ⟨h1, h2⟩
    · refine ⟨?_, h2⟩
      by_contra h1
      exact hnot_below ⟨h2, h1⟩

/-! ### Existence of extremal lotteries and vNM utility representation -/

/-- Every finite nonempty outcome set has a most preferred degenerate lottery under a rational
preference relation (used to establish AFP `overall_best_nonempty`). -/
theorem exists_best_degenerate {X : Finset α} (hX : X.Nonempty)
    {rel : PMF α → PMF α → Prop} (hR : IsRationalOn (X : Set α) rel) :
    ∃ x ∈ X, ∀ y ∈ X, rel (PMF.pure x) (PMF.pure y) := by
  classical
  induction hX using Finset.Nonempty.cons_induction with
  | singleton a =>
    refine ⟨a, Finset.mem_singleton_self a, fun y hy => ?_⟩
    rw [Finset.mem_singleton.mp hy]
    exact hR.refl (pure_mem_lotteriesOn_iff.mpr (Finset.mem_singleton_self a))
  | cons a s has hs ih =>
    have hsub : (s : Set α) ⊆ ((Finset.cons a s has : Finset α) : Set α) :=
      Finset.coe_subset.mpr (Finset.subset_cons has)
    have hR_sub : IsRationalOn (s : Set α) rel :=
      { complete := fun _ hp _ hq => hR.complete (hp.trans hsub) (hq.trans hsub)
        trans := fun _ hp _ hq _ hr => hR.trans (hp.trans hsub) (hq.trans hsub) (hr.trans hsub) }
    obtain ⟨b, hbs, hb⟩ := ih hR_sub
    have ha_mem : PMF.pure a ∈ lotteriesOn ((Finset.cons a s has : Finset α) : Set α) :=
      pure_mem_lotteriesOn_iff.mpr (Finset.mem_cons_self a s)
    have hb_mem : PMF.pure b ∈ lotteriesOn ((Finset.cons a s has : Finset α) : Set α) :=
      pure_mem_lotteriesOn_iff.mpr (Finset.mem_cons_of_mem hbs)
    rcases hR.complete ha_mem hb_mem with hab | hba
    · refine ⟨a, Finset.mem_cons_self a s, fun y hy => ?_⟩
      rcases Finset.mem_cons.mp hy with rfl | hys
      · exact hR.refl ha_mem
      · exact hR.trans ha_mem hb_mem
          (pure_mem_lotteriesOn_iff.mpr (Finset.mem_cons_of_mem hys)) hab (hb y hys)
    · refine ⟨b, Finset.mem_cons_of_mem hbs, fun y hy => ?_⟩
      rcases Finset.mem_cons.mp hy with rfl | hys
      · exact hba
      · exact hb y hys

/-- Every finite nonempty outcome set has a least preferred degenerate lottery under a rational
preference relation (used to establish AFP `overall_worst_nonempty`). -/
theorem exists_worst_degenerate {X : Finset α} (hX : X.Nonempty)
    {rel : PMF α → PMF α → Prop} (hR : IsRationalOn (X : Set α) rel) :
    ∃ x ∈ X, ∀ y ∈ X, rel (PMF.pure y) (PMF.pure x) :=
  exists_best_degenerate hX hR.flip

/-- Induction principle on the finite support cardinality of lotteries over `X : Finset α`. -/
private theorem lotteriesOn_induction {X : Finset α} {P : PMF α → Prop}
    (hpure : ∀ x ∈ X, P (PMF.pure x))
    (hmix : ∀ (a : I) (x : α) (q : PMF α),
      x ∈ X → q ∈ lotteriesOn (X : Set α) → P q → P (mix a (PMF.pure x) q))
    {p : PMF α} (hp : p ∈ lotteriesOn (X : Set α)) : P p := by
  classical
  have hgen : ∀ n : ℕ, ∀ p ∈ lotteriesOn (X : Set α),
      (X.filter (fun y => y ∈ p.support)).card ≤ n → P p := by
    intro n
    induction n with
    | zero =>
      intro p hp hcard
      obtain ⟨y, hy⟩ := p.support_nonempty
      have hyf : y ∈ X.filter (fun y => y ∈ p.support) := Finset.mem_filter.mpr ⟨hp hy, hy⟩
      have hpos : 0 < (X.filter (fun y => y ∈ p.support)).card := Finset.card_pos.mpr ⟨y, hyf⟩
      omega
    | succ n ih =>
      intro p hp hcard
      obtain ⟨x, hx_supp⟩ := p.support_nonempty
      have hxX : x ∈ X := hp hx_supp
      by_cases hpx1 : p x = 1
      · have hp_supp : p.support = {x} := (PMF.apply_eq_one_iff p x).mp hpx1
        have hp_eq : p = PMF.pure x := by
          refine PMF.ext fun y => ?_
          by_cases hy : y = x
          · rw [hy, hpx1, PMF.pure_apply_self]
          · have hynot : y ∉ p.support := by rw [hp_supp]; exact hy
            rw [PMF.mem_support_iff, not_not] at hynot
            rw [hynot, PMF.pure_apply_of_ne x y hy]
        rw [hp_eq]
        exact hpure x hxX
      · obtain ⟨a, q, hq_supp, rfl⟩ := exists_mix_pure_of_mem_support hx_supp hpx1
        have hq_mem : q ∈ lotteriesOn (X : Set α) := by
          intro y hy
          rw [hq_supp] at hy
          exact hp hy.1
        have hfilter_eq : X.filter (fun y => y ∈ q.support) =
            (X.filter (fun y => y ∈ (mix a (PMF.pure x) q).support)).erase x := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_erase, hq_supp, Set.mem_sdiff,
            Set.mem_singleton_iff]
          constructor
          · rintro ⟨hyX, hy_supp, hyx⟩
            exact ⟨hyx, hyX, hy_supp⟩
          · rintro ⟨hyx, hyX, hy_supp⟩
            exact ⟨hyX, hy_supp, hyx⟩
        have hx_in_filter : x ∈ X.filter (fun y => y ∈ (mix a (PMF.pure x) q).support) :=
          Finset.mem_filter.mpr ⟨hxX, hx_supp⟩
        have hq_card : (X.filter (fun y => y ∈ q.support)).card ≤ n := by
          rw [hfilter_eq, Finset.card_erase_of_mem hx_in_filter]
          omega
        exact hmix a x q hxX hq_mem (ih q hq_mem hq_card)
  exact hgen _ p hp le_rfl

/-- A most preferred degenerate lottery is weakly preferred to every lottery on `X`
(AFP `best_degenerate_in_best_overall`). -/
theorem best_degenerate_is_best_overall {X : Finset α} {rel : PMF α → PMF α → Prop}
    (hR : IsRationalOn (X : Set α) rel) (hI : IsIndependentOn (X : Set α) rel)
    {x : α} (hx : x ∈ X) (hbest : ∀ y ∈ X, rel (PMF.pure x) (PMF.pure y)) :
    ∀ p ∈ lotteriesOn (X : Set α), rel (PMF.pure x) p := by
  intro p hp
  have hx_mem : PMF.pure x ∈ lotteriesOn (X : Set α) := pure_mem_lotteriesOn_iff.mpr hx
  refine lotteriesOn_induction (fun y hy => hbest y hy) (fun a y q hy hq hrel_q => ?_) hp
  simpa only [mix_self] using hI.mix_rel_congr hR hx_mem (pure_mem_lotteriesOn_iff.mpr hy)
    hx_mem hq a (hbest y hy) hrel_q

/-- A least preferred degenerate lottery is weakly worse than every lottery on `X`
(AFP `worst_degenerate_in_worst_overall`). -/
theorem worst_degenerate_is_worst_overall {X : Finset α} {rel : PMF α → PMF α → Prop}
    (hR : IsRationalOn (X : Set α) rel) (hI : IsIndependentOn (X : Set α) rel)
    {x : α} (hx : x ∈ X) (hworst : ∀ y ∈ X, rel (PMF.pure y) (PMF.pure x)) :
    ∀ p ∈ lotteriesOn (X : Set α), rel p (PMF.pure x) :=
  best_degenerate_is_best_overall hR.flip hI.flip hx hworst

/-- Existence of a globally best lottery on a finite nonempty outcome set
(AFP `overall_best_nonempty`). -/
theorem exists_best_overall {X : Finset α} (hX : X.Nonempty)
    {rel : PMF α → PMF α → Prop} (hR : IsRationalOn (X : Set α) rel)
    (hI : IsIndependentOn (X : Set α) rel) :
    ∃ p ∈ lotteriesOn (X : Set α), ∀ q ∈ lotteriesOn (X : Set α), rel p q := by
  obtain ⟨x, hx, hbest⟩ := exists_best_degenerate hX hR
  exact ⟨PMF.pure x, pure_mem_lotteriesOn_iff.mpr hx,
    best_degenerate_is_best_overall hR hI hx hbest⟩

/-- Existence of a globally worst lottery on a finite nonempty outcome set
(AFP `overall_worst_nonempty`). -/
theorem exists_worst_overall {X : Finset α} (hX : X.Nonempty)
    {rel : PMF α → PMF α → Prop} (hR : IsRationalOn (X : Set α) rel)
    (hI : IsIndependentOn (X : Set α) rel) :
    ∃ p ∈ lotteriesOn (X : Set α), ∀ q ∈ lotteriesOn (X : Set α), rel q p :=
  exists_best_overall hX hR.flip hI.flip

/-- A utility function `u : α → ℝ` is a **von Neumann–Morgenstern utility** representing `rel` on
lotteries over `X` if weak preference agrees with weak inequality of expected utility (AFP locale
`vNM_utility`, except that AFP also bundles
`relation ⊆ lotteries_on outcomes × lotteries_on outcomes` whereas `IsVNMUtility` leaves `rel`
unconstrained outside `lotteriesOn X`). -/
@[expose] def IsVNMUtility (X : Finset α) (rel : PMF α → PMF α → Prop) (u : α → ℝ) : Prop :=
  ∀ ⦃p⦄, p ∈ lotteriesOn (X : Set α) → ∀ ⦃q⦄, q ∈ lotteriesOn (X : Set α) →
    (rel p q ↔ expectedUtility X u q ≤ expectedUtility X u p)

/-- **Von Neumann–Morgenstern expected utility existence theorem**
(AFP `system_U_implies_vNM_utility`; [vonNeumannMorgenstern1947], [HersteinMilnor1953],
[MasColellWhinstonGreen1995]): every rational, independent, and continuous preference relation on
lotteries over a finite nonempty outcome set `X` admits a von Neumann–Morgenstern utility function
`u : α → ℝ`. -/
theorem exists_isVNMUtility {X : Finset α} (hX : X.Nonempty)
    {rel : PMF α → PMF α → Prop} (hR : IsRationalOn (X : Set α) rel)
    (hI : IsIndependentOn (X : Set α) rel) (hC : IsContinuousOn (X : Set α) rel) :
    ∃ u : α → ℝ, IsVNMUtility X rel u := by
  classical
  obtain ⟨pBest, hpBest, hbest⟩ := exists_best_overall hX hR hI
  obtain ⟨pWorst, hpWorst, hworst⟩ := exists_worst_overall hX hR hI
  by_cases hdeg : rel pWorst pBest
  · refine ⟨fun _ => 0, fun p hp q hq => ?_⟩
    have hrel : rel p q :=
      hR.trans hp hpWorst hq (hworst p hp) (hR.trans hpWorst hpBest hq hdeg (hbest q hq))
    simp [expectedUtility, hrel]
  · have hstrict : strictPref rel pBest pWorst := ⟨hbest pWorst hpWorst, hdeg⟩
    have hex : ∀ p, p ∈ lotteriesOn (X : Set α) → ∃ a : I, indiff rel (mix a pBest pWorst) p :=
      fun p hp => hC hpBest hp hpWorst (hbest p hp) (hworst p hp)
    let U : ∀ p, p ∈ lotteriesOn (X : Set α) → I := fun p hp => Classical.choose (hex p hp)
    have hU : ∀ p (hp : p ∈ lotteriesOn (X : Set α)),
        indiff rel (mix (U p hp) pBest pWorst) p :=
      fun p hp => Classical.choose_spec (hex p hp)
    have hU_unique : ∀ p (hp : p ∈ lotteriesOn (X : Set α)) (a : I),
        indiff rel (mix a pBest pWorst) p → a = U p hp := fun p hp a ha =>
      (hI.mix_indiff_mix_iff hR hpBest hpWorst hstrict a (U p hp)).mp
        (hR.indiff_trans (mix_mem_lotteriesOn a hpBest hpWorst) hp
          (mix_mem_lotteriesOn (U p hp) hpBest hpWorst) ha (indiff_symm (hU p hp)))
    have hU_mix : ∀ (a : I) {p q : PMF α} (hp : p ∈ lotteriesOn (X : Set α))
        (hq : q ∈ lotteriesOn (X : Set α)),
        (U (mix a p q) (mix_mem_lotteriesOn a hp hq) : ℝ) =
          (a : ℝ) * (U p hp : ℝ) + (1 - a) * (U q hq : ℝ) := by
      intro a p q hp hq
      have hind : indiff rel (mix a (mix (U p hp) pBest pWorst) (mix (U q hq) pBest pWorst))
          (mix a p q) :=
        hI.mix_indiff_congr hR (mix_mem_lotteriesOn (U p hp) hpBest hpWorst) hp
          (mix_mem_lotteriesOn (U q hq) hpBest hpWorst) hq a (hU p hp) (hU q hq)
      rw [mix_mix_eq] at hind
      have heq := hU_unique (mix a p q) (mix_mem_lotteriesOn a hp hq) _ hind
      exact (congrArg Subtype.val heq).symm
    let u : α → ℝ := fun x =>
      if hx : x ∈ X then (U (PMF.pure x) (pure_mem_lotteriesOn_iff.mpr hx) : ℝ) else 0
    have hU_eq_exp : ∀ p (hp : p ∈ lotteriesOn (X : Set α)),
        (U p hp : ℝ) = expectedUtility X u p := by
      intro p hp
      refine lotteriesOn_induction (P := fun r => ∀ hr : r ∈ lotteriesOn (X : Set α),
          (U r hr : ℝ) = expectedUtility X u r) ?_ ?_ hp hp
      · intro x hx hr
        rw [expectedUtility_pure u hx]
        simp [u, hx]
      · intro a x q hx hq ih hr
        rw [hU_mix a (pure_mem_lotteriesOn_iff.mpr hx) hq, expectedUtility_mix,
          expectedUtility_pure u hx, ih hq]
        simp [u, hx]
    refine ⟨u, fun p hp q hq => ?_⟩
    rw [← hU_eq_exp p hp, ← hU_eq_exp q hq, ← hI.mix_rel_mix_iff hR hpBest hpWorst hstrict]
    refine ⟨fun hpq => ?_, fun hmix => ?_⟩
    · exact hR.trans (mix_mem_lotteriesOn (U p hp) hpBest hpWorst) hp
        (mix_mem_lotteriesOn (U q hq) hpBest hpWorst) (hU p hp).1
        (hR.trans hp hq (mix_mem_lotteriesOn (U q hq) hpBest hpWorst) hpq (hU q hq).2)
    · exact hR.trans hp (mix_mem_lotteriesOn (U p hp) hpBest hpWorst) hq (hU p hp).2
        (hR.trans (mix_mem_lotteriesOn (U p hp) hpBest hpWorst)
          (mix_mem_lotteriesOn (U q hq) hpBest hpWorst) hq hmix (hU q hq).1)

/-! ### Converse and characterization -/

namespace IsVNMUtility

variable {X : Finset α} {rel : PMF α → PMF α → Prop} {u : α → ℝ}

theorem strictPref_iff (hu : IsVNMUtility X rel u) {p q : PMF α}
    (hp : p ∈ lotteriesOn (X : Set α)) (hq : q ∈ lotteriesOn (X : Set α)) :
    strictPref rel p q ↔ expectedUtility X u q < expectedUtility X u p := by
  rw [VonNeumannMorgenstern.strictPref_iff, hu hp hq, hu hq hp, not_le]
  exact ⟨And.right, fun h => ⟨le_of_lt h, h⟩⟩

theorem indiff_iff (hu : IsVNMUtility X rel u) {p q : PMF α}
    (hp : p ∈ lotteriesOn (X : Set α)) (hq : q ∈ lotteriesOn (X : Set α)) :
    indiff rel p q ↔ expectedUtility X u p = expectedUtility X u q := by
  rw [VonNeumannMorgenstern.indiff_iff, hu hp hq, hu hq hp]
  exact ⟨fun ⟨h1, h2⟩ => le_antisymm h2 h1, fun h => ⟨le_of_eq h.symm, le_of_eq h⟩⟩

/-- A vNM utility induces an ordinal utility on degenerate lotteries (restricting
`expectedUtility X u` to `PMF.pure`; cf. AFP `vnm_utility_is_ordinal_utility` on all lotteries). -/
theorem pure_iff (hu : IsVNMUtility X rel u) {x y : α} (hx : x ∈ X) (hy : y ∈ X) :
    rel (PMF.pure x) (PMF.pure y) ↔ u y ≤ u x := by
  rw [hu (pure_mem_lotteriesOn_iff.mpr hx) (pure_mem_lotteriesOn_iff.mpr hy),
    expectedUtility_pure u hx, expectedUtility_pure u hy]

/-- Every preference relation represented by a vNM utility is rational
(AFP `vnm_utility_imp_reational_prefs`). -/
theorem isRationalOn (hu : IsVNMUtility X rel u) : IsRationalOn (X : Set α) rel where
  complete _ hp _ hq := by
    rw [hu hp hq, hu hq hp]
    exact le_total _ _
  trans _ hp _ hq _ hr hpq hqr := by
    rw [hu hp hq] at hpq
    rw [hu hq hr] at hqr
    rw [hu hp hr]
    exact le_trans hqr hpq

/-- Every preference relation represented by a vNM utility satisfies independence
(AFP `vNM_utility_implies_independence`). -/
theorem isIndependentOn (hu : IsVNMUtility X rel u) : IsIndependentOn (X : Set α) rel := by
  intro p hp q hq r hr a ha
  rw [hu hp hq, hu (mix_mem_lotteriesOn a hp hr) (mix_mem_lotteriesOn a hq hr),
    expectedUtility_mix, expectedUtility_mix]
  constructor <;> intro h <;> nlinarith

/-- Every preference relation represented by a vNM utility satisfies continuity
(AFP `vNM_utilty_implies_continuity`). -/
theorem isContinuousOn (hu : IsVNMUtility X rel u) : IsContinuousOn (X : Set α) rel := by
  intro p hp q hq r hr hpq hqr
  rw [hu hp hq] at hpq
  rw [hu hq hr] at hqr
  rcases eq_or_lt_of_le (le_trans hqr hpq) with heq | hlt
  · refine ⟨1, ?_⟩
    rw [mix_one, hu.indiff_iff hp hq]
    linarith
  · have hden : 0 < expectedUtility X u p - expectedUtility X u r := sub_pos.mpr hlt
    let a : I := ⟨(expectedUtility X u q - expectedUtility X u r) /
        (expectedUtility X u p - expectedUtility X u r),
      div_nonneg (sub_nonneg.mpr hqr) (le_of_lt hden),
      (div_le_one hden).mpr (sub_le_sub_right hpq _)⟩
    refine ⟨a, (hu.indiff_iff (mix_mem_lotteriesOn a hp hr) hq).mpr ?_⟩
    rw [expectedUtility_mix]
    dsimp [a]
    field_simp [ne_of_gt hden]
    ring

end IsVNMUtility

/-- **Full characterization of von Neumann–Morgenstern preferences**
(AFP `expected_utilty_theorem_form_vnm_utility`): on a finite nonempty outcome set `X`, a
preference relation admits a vNM utility representation iff it is rational, independent, and
continuous. -/
theorem exists_isVNMUtility_iff {X : Finset α} (hX : X.Nonempty)
    {rel : PMF α → PMF α → Prop} :
    (IsRationalOn (X : Set α) rel ∧ IsIndependentOn (X : Set α) rel ∧
      IsContinuousOn (X : Set α) rel) ↔
      ∃ u : α → ℝ, IsVNMUtility X rel u :=
  ⟨fun ⟨hR, hI, hC⟩ => exists_isVNMUtility hX hR hI hC,
    fun ⟨_, hu⟩ => ⟨hu.isRationalOn, hu.isIndependentOn, hu.isContinuousOn⟩⟩

/-! ### Uniqueness up to positive affine transformation -/

namespace IsVNMUtility

variable {X : Finset α} {rel : PMF α → PMF α → Prop} {u v : α → ℝ}

/-- Positive affine transformations preserve vNM utility representations
(extending AFP `scale_pos_left`). -/
theorem posAffine (hu : IsVNMUtility X rel u) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IsVNMUtility X rel (fun x => a * u x + b) := by
  intro p hp q hq
  rw [hu hp hq, expectedUtility_affine u a b hp, expectedUtility_affine u a b hq]
  constructor <;> intro h <;> nlinarith

/-- Replacing a utility function by one agreeing with it on `X` preserves `IsVNMUtility`. -/
theorem congr_on (hu : IsVNMUtility X rel u) (huv : ∀ x ∈ X, v x = u x) :
    IsVNMUtility X rel v := by
  have hexp : ∀ p, expectedUtility X v p = expectedUtility X u p := fun p =>
    Finset.sum_congr rfl fun x hx => by rw [huv x hx]
  intro p hp q hq
  rw [hexp p, hexp q, hu hp hq]

/-- **Uniqueness up to positive affine transformation** ([vonNeumannMorgenstern1947],
[HersteinMilnor1953], [MasColellWhinstonGreen1995]): any two vNM utility functions representing
the same preference relation on lotteries over a finite set `X` agree on `X` up to a strictly
positive scaling and an additive constant. -/
theorem exists_posAffine_eq (hu : IsVNMUtility X rel u)
    (hv : IsVNMUtility X rel v) :
    ∃ a b : ℝ, 0 < a ∧ ∀ x ∈ X, v x = a * u x + b := by
  rcases X.eq_empty_or_nonempty with rfl | hX
  · exact ⟨1, 0, one_pos, by simp⟩
  obtain ⟨xHi, hxHi, hmax⟩ := Finset.exists_max_image X u hX
  obtain ⟨xLo, hxLo, hmin⟩ := Finset.exists_min_image X u hX
  have hLo_le_Hi : u xLo ≤ u xHi := hmax xLo hxLo
  rcases eq_or_lt_of_le hLo_le_Hi with hconst | hstrict
  · refine ⟨1, v xLo - u xLo, one_pos, fun x hx => ?_⟩
    have hux : u x = u xLo := le_antisymm (hconst ▸ hmax x hx) (hmin x hx)
    have hind : indiff rel (PMF.pure x) (PMF.pure xLo) :=
      (hu.indiff_iff (pure_mem_lotteriesOn_iff.mpr hx) (pure_mem_lotteriesOn_iff.mpr hxLo)).mpr
        (by rw [expectedUtility_pure u hx, expectedUtility_pure u hxLo, hux])
    have hvx : v x = v xLo := by
      have h := (hv.indiff_iff (pure_mem_lotteriesOn_iff.mpr hx)
        (pure_mem_lotteriesOn_iff.mpr hxLo)).mp hind
      rwa [expectedUtility_pure v hx, expectedUtility_pure v hxLo] at h
    linarith
  · have hstrict_rel : strictPref rel (PMF.pure xHi) (PMF.pure xLo) :=
      (hu.strictPref_iff (pure_mem_lotteriesOn_iff.mpr hxHi)
        (pure_mem_lotteriesOn_iff.mpr hxLo)).mpr
        (by rw [expectedUtility_pure u hxHi, expectedUtility_pure u hxLo]; exact hstrict)
    have hv_strict : v xLo < v xHi := by
      have h := (hv.strictPref_iff (pure_mem_lotteriesOn_iff.mpr hxHi)
        (pure_mem_lotteriesOn_iff.mpr hxLo)).mp hstrict_rel
      rwa [expectedUtility_pure v hxHi, expectedUtility_pure v hxLo] at h
    have hdu : 0 < u xHi - u xLo := sub_pos.mpr hstrict
    have hdv : 0 < v xHi - v xLo := sub_pos.mpr hv_strict
    let a : ℝ := (v xHi - v xLo) / (u xHi - u xLo)
    let b : ℝ := v xLo - a * u xLo
    refine ⟨a, b, div_pos hdv hdu, fun x hx => ?_⟩
    let t : I := ⟨(u x - u xLo) / (u xHi - u xLo),
      div_nonneg (sub_nonneg.mpr (hmin x hx)) (le_of_lt hdu),
      (div_le_one hdu).mpr (sub_le_sub_right (hmax x hx) _)⟩
    have hmix_mem : mix t (PMF.pure xHi) (PMF.pure xLo) ∈ lotteriesOn (X : Set α) :=
      mix_mem_lotteriesOn t (pure_mem_lotteriesOn_iff.mpr hxHi)
        (pure_mem_lotteriesOn_iff.mpr hxLo)
    have hu_eq : expectedUtility X u (mix t (PMF.pure xHi) (PMF.pure xLo)) =
        expectedUtility X u (PMF.pure x) := by
      rw [expectedUtility_mix, expectedUtility_pure u hxHi, expectedUtility_pure u hxLo,
        expectedUtility_pure u hx]
      dsimp [t]
      field_simp [ne_of_gt hdu]
      ring
    have hind : indiff rel (mix t (PMF.pure xHi) (PMF.pure xLo)) (PMF.pure x) :=
      (hu.indiff_iff hmix_mem (pure_mem_lotteriesOn_iff.mpr hx)).mpr hu_eq
    have hv_eq := (hv.indiff_iff hmix_mem (pure_mem_lotteriesOn_iff.mpr hx)).mp hind
    rw [expectedUtility_mix, expectedUtility_pure v hxHi, expectedUtility_pure v hxLo,
      expectedUtility_pure v hx] at hv_eq
    rw [← hv_eq]
    dsimp [a, b, t]
    field_simp [ne_of_gt hdu]
    ring

end IsVNMUtility

/-- Complete characterization of all vNM utility functions representing `rel` on a finite outcome
set `X`: `v` represents `rel` iff `v` is a positive affine transformation of `u` on `X`. -/
theorem isVNMUtility_iff_exists_posAffine_eq {X : Finset α}
    {rel : PMF α → PMF α → Prop} {u v : α → ℝ} (hu : IsVNMUtility X rel u) :
    IsVNMUtility X rel v ↔ ∃ a b : ℝ, 0 < a ∧ ∀ x ∈ X, v x = a * u x + b :=
  ⟨fun hv => hu.exists_posAffine_eq hv,
    fun ⟨_, _, ha, huv⟩ => (hu.posAffine ha _).congr_on huv⟩

end Cslib.GameTheory.VonNeumannMorgenstern
