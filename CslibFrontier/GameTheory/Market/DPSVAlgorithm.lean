/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Market.BalancedFlow
import CslibFrontier.Foundations.Analysis.BernoulliInequality
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The DPSV primal-dual algorithm for linear Fisher markets

This module formalizes the main primal-dual algorithm of Devanur–Papadimitriou–Saberi–Vazirani
([Vazirani2007], Chapter 5, Sections 5.8 and 5.10, pp. 115–121) for computing exact market
equilibria in linear Fisher markets, building on the equality-network, balanced-flow, tight-set,
and rationality infrastructure of `CslibFrontier.GameTheory.Market.BalancedFlow`.

## Main definitions

* `Cslib.GameTheory.Market.LinearFisherMarket.dpsvInitPrice`: initial price construction
  ([Vazirani2007], Section 5.8, p. 115) setting baseline prices to `1 / n` and lowering goods
  with no incident equality edge to `max_i (u i g / α i)`.
* `Cslib.GameTheory.Market.LinearFisherMarket.scaleActivePrices`,
  `Cslib.GameTheory.Market.LinearFisherMarket.activeGoods`,
  `Cslib.GameTheory.Market.LinearFisherMarket.event2Ratio`: active-subgraph scaling, active goods,
  and Event 2 new-edge ratio.
* `Cslib.GameTheory.Market.LinearFisherMarket.DPSVPhaseResult`,
  `Cslib.GameTheory.Market.LinearFisherMarket.dpsvPhaseProgram`: one full DPSV phase in
  `Cslib.FreeM (MaxFlowQuery I G)` executing Event-2 iterations until Event 1 terminates the phase.
* `Cslib.GameTheory.Market.LinearFisherMarket.DPSVResult`,
  `Cslib.GameTheory.Market.LinearFisherMarket.dpsvProgram`: full DPSV algorithm in
  `Cslib.FreeM (MaxFlowQuery I G)` returning equilibrium allocations, equilibrium prices, and the
  number of phases executed.

## Main results

* `Cslib.GameTheory.Market.LinearFisherMarket.dpsvInitPrice_spec`: initialized prices are positive,
  bounded above by `1 / n`, give every good an equality edge, and satisfy `SatisfiesInvariant`
  ([Vazirani2007], Section 5.8, p. 115).
* `Cslib.GameTheory.Market.LinearFisherMarket.price_sub_ge_inv_sq_of_isTightSet`: **Lemma 5.13**
  ([Vazirani2007], Section 5.10, p. 119; note the printed typo `r ≤ Δ` where `s ≤ Δ` is meant):
  a strict price increase of a good appearing in tight sets of two phases is at least `1 / Δ ^ 2`.
* `Cslib.GameTheory.Market.LinearFisherMarket.sum_sq_drop_of_transfer` (**Lemma 5.16**, p. 120) and
  `Cslib.GameTheory.Market.LinearFisherMarket.surplusSqNorm_le_sub_sq_of_isBalancedFlow`
  (**Lemma 5.15**, p. 119): any feasible flow whose surplus on buyer `i` differs from a balanced
  flow by `δ` exceeds the balanced squared `ℓ₂` surplus norm by at least `δ ^ 2`.
* `Cslib.GameTheory.Market.LinearFisherMarket.mem_activeGoods`,
  `Cslib.GameTheory.Market.LinearFisherMarket.event2Ratio_eq_none_iff`,
  `Cslib.GameTheory.Market.LinearFisherMarket.one_lt_event2Ratio`, and
  `Cslib.GameTheory.Market.LinearFisherMarket.le_event2Ratio_iff`: membership and bound
  characterizations of `activeGoods` and `event2Ratio` for applying Lemmas 5.17, 5.18, and 5.20.
* `Cslib.GameTheory.Market.LinearFisherMarket.isEqualityFlow_scaleActivePrices`
  (**Lemma 5.17**, p. 120),
  `Cslib.GameTheory.Market.LinearFisherMarket.surplusSqNorm_scaleActivePrices_le`
  (**Corollary 5.18**, p. 120),
  `Cslib.GameTheory.Market.LinearFisherMarket.exists_surplus_drop_of_residual_expand`
  (**Lemma 5.19**, p. 120), and
  `Cslib.GameTheory.Market.LinearFisherMarket.surplusSqNorm_drop_of_minSurplus_lt`
  (**Lemma 5.20**, p. 120): per-iteration flow feasibility, monotone potential decrease, and
  quadratic drop when the active minimum surplus decreases.
* `Cslib.GameTheory.Market.LinearFisherMarket.dpsvPhaseProgram_spec`: **Lemma 5.14** (at most
  `n = Fintype.card G` iterations and `2 * n ^ 2` max-flow oracle calls per phase) and
  **Lemma 5.21** (squared `ℓ₂` surplus norm drops by at least `δ ^ 2 / n`, hence by a factor of
  `1 - 1 / (m * n)`, specializing to `1 - 1 / n ^ 2` when `m ≤ n`; [Vazirani2007], pp. 119, 121).
* `Cslib.GameTheory.Market.LinearFisherMarket.dpsvProgram_spec`: **Theorem 5.22**
  ([Vazirani2007], Section 5.10, p. 121): for every non-degenerate unit-supply linear Fisher
  market with integer utilities `u i g ≤ U` and integer budgets `e i` (`M_tot = ∑ i, e i`,
  `Δ = n * U ^ n`), `dpsvProgram` evaluated with any valid max-flow oracle outputs an exact
  market equilibrium in at most `m * n * (Nat.log 2 (m * Δ ^ 4 * M_tot ^ 2) + 1) + n` phases and
  at most `n + 2 * n ^ 2 * phases` max-flow oracle calls (`O(m * n ^ 3 * (log m + log n +
  n log U + log M_tot))`, matching `O(n ^ 4 * (log n + n log U + log M))` when `m ≤ n`). Note
  that this is a max-flow oracle query bound in `Cslib.FreeM`, matching [Vazirani2007], Theorem
  5.22's count of max-flow computations rather than a machine-level bit-complexity runtime.

## Source notes

Four minor slips in the printed text of [Vazirani2007], Sections 5.8 and 5.10 are addressed
explicitly in this formalization:
1. Section 5.8 (p. 116) states that equilibrium is reached when the Section 5.7.1 balanced-flow
   subroutine terminates in Case 1; in fact Case 1 with positive uniform shift `X > 0` can occur
   far from equilibrium, and the actual halting condition is that all buyer surpluses vanish
   (`∀ i, M.surplus f i = 0`, matching Section 5.5, p. 110 and Section 5.6, p. 111).
2. Section 5.8 (p. 116) claims that for all `x > 1`, buyers in `B \ H` immediately lose all
   equality edges to `J`; this fails for zero-spending buyers in `B \ H` whose equality edges all
   lie in `J`. Running Event 1 on `(J, H)` still preserves the Invariant and the full potential
   drop `δ_{k-1} ^ 2` at Event 1 unconditionally, and once total surplus falls below `1` (hence
   below every integral budget `e i ≥ 1`), every buyer spends positively so no such buyer exists
   and Event 1 yields a genuine tight set in `N(p')`.
3. Section 5.10, Lemma 5.13 (p. 119) prints `q ≤ Δ and r ≤ Δ` for fractions `p/q` and `r/s`,
   where `s ≤ Δ` is meant.
4. Section 5.10, Lemma 5.21 and Theorem 5.22 (p. 121) write `n` for both `|A|` and `|B|`
   (despite Section 5.2, p. 105 writing `|A| = n` and `|B| = n'`). All bounds here track
   `m = Fintype.card I` and `n = Fintype.card G` explicitly.

## References

* [Vazirani2007]
-/

public section

namespace Cslib.GameTheory.Market.LinearFisherMarket

open Cslib (FreeM)

universe u

/-! ### Auxiliary bang-per-buck and equilibrium helpers -/

section Helpers

variable {I G : Type*}

/-- Maximum bang-per-buck `α_i(p) = max_g (M.utility i g / p g)` of buyer `i` at prices `p`
(`0` when `G` is empty). -/
private noncomputable def maxBangPerBuck [Fintype G] (M : LinearFisherMarket I G)
    (p : G → ℝ) (i : I) : ℝ :=
  if hG : (Finset.univ : Finset G).Nonempty then
    Finset.univ.sup' hG fun g => M.bangPerBuck p i g
  else 0

private theorem bangPerBuck_le_maxBangPerBuck [Fintype G] {M : LinearFisherMarket I G}
    {p : G → ℝ} (i : I) (g : G) :
    M.bangPerBuck p i g ≤ maxBangPerBuck M p i := by
  have hG : (Finset.univ : Finset G).Nonempty := ⟨g, Finset.mem_univ g⟩
  simpa only [maxBangPerBuck, hG, ↓reduceDIte] using
    Finset.le_sup' (fun g' => M.bangPerBuck p i g') (Finset.mem_univ g)

private theorem isEqualityEdge_iff_eq_maxBangPerBuck [Fintype G] {M : LinearFisherMarket I G}
    {p : G → ℝ} (i : I) (g : G) :
    M.IsEqualityEdge p i g ↔ M.bangPerBuck p i g = maxBangPerBuck M p i := by
  have hG : (Finset.univ : Finset G).Nonempty := ⟨g, Finset.mem_univ g⟩
  simp only [IsEqualityEdge, maxBangPerBuck, hG, ↓reduceDIte]
  constructor
  · intro h
    exact le_antisymm (Finset.le_sup' (fun g' => M.bangPerBuck p i g') (Finset.mem_univ g))
      (Finset.sup'_le hG _ fun g' _ => h g')
  · intro h g'
    rw [h]
    exact Finset.le_sup' (fun g'' => M.bangPerBuck p i g'') (Finset.mem_univ g')

private theorem maxBangPerBuck_pos [Fintype G] {M : LinearFisherMarket I G} {p : G → ℝ}
    (hp : ∀ g, 0 < p g) {i : I} (hbuyer : ∃ g, 0 < M.utility i g) :
    0 < maxBangPerBuck M p i := by
  obtain ⟨g, hg⟩ := hbuyer
  exact (div_pos hg (hp g)).trans_le (by
    simpa only [bangPerBuck_eq] using bangPerBuck_le_maxBangPerBuck (M := M) (p := p) i g)

private theorem exists_isEqualityEdge [Finite G] [Nonempty G] (M : LinearFisherMarket I G)
    (p : G → ℝ) (i : I) : ∃ g : G, M.IsEqualityEdge p i g := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := G))
    (fun g' => M.bangPerBuck p i g')
  exact ⟨g, (isEqualityEdge_iff_eq_maxBangPerBuck i g).2 (by
    simp only [maxBangPerBuck, Finset.univ_nonempty, ↓reduceDIte]
    exact hg.symm)⟩

/-- **Zero-surplus equilibrium recovery** ([Vazirani2007], Lemma 5.2, p. 109; Section 5.6, p. 111):
if `p` is positive and satisfies the Invariant and `f` is a maximum equality flow in `N(p)` whose
buyer surpluses all vanish, then `(moneyFlowToAlloc f p, p)` is a market equilibrium. -/
private theorem isEquilibrium_of_surplus_eq_zero [Fintype I] [Fintype G]
    [DecidableEq I] [DecidableEq G]
    {M : LinearFisherMarket I G} {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g) (hgood : ∀ g, ∃ i, 0 < M.utility i g)
    (hinv : M.SatisfiesInvariant p) {f : G → I → ℝ}
    (hfmax : M.IsMaxEqualityFlow p f) (hsurp : ∀ i, M.surplus f i = 0) :
    M.IsEquilibrium (moneyFlowToAlloc f p) p := by
  rw [isEquilibrium_iff_bangPerBuck hbuyer hgood]
  refine ⟨hp, fun i g => div_nonneg (hfmax.1.1 g i) (hp g).le, fun g => ?_, fun i => ?_,
    fun i g hpos => hfmax.1.2.1 g i ((div_pos_iff_of_pos_right (hp g)).1 hpos)⟩
  · simp only [moneyFlowToAlloc, ← Finset.sum_div,
      hfmax.sum_buyer_eq (fun g' => (hp g').le) hinv g]
    exact mul_div_cancel_left₀ (M.supply g) (hp g).ne'
  · simp only [expenditure_eq_sum, moneyFlowToAlloc]
    have hsum : ∑ g : G, p g * (f g i / p g) = ∑ g : G, f g i :=
      Finset.sum_congr rfl fun g _ => mul_div_cancel₀ (f g i) (hp g).ne'
    have hs := hsurp i
    unfold surplus at hs
    linarith

private theorem sum_surplus_eq [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]
    {M : LinearFisherMarket I G} {p : G → ℝ} (hp : ∀ g, 0 ≤ p g)
    (hinv : M.SatisfiesInvariant p) {f : G → I → ℝ} (hfmax : M.IsMaxEqualityFlow p f) :
    ∑ i : I, M.surplus f i = (∑ i : I, M.budget i) - ∑ g : G, p g * M.supply g := by
  simp only [surplus, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun g _ => hfmax.sum_buyer_eq hp hinv g

end Helpers

/-! ### Section 5.10: Lemmas 5.13, 5.15, and 5.16 -/

section PotentialLemmas

variable {I G : Type*}

/-- **Lemma 5.13** ([Vazirani2007], Section 5.10, p. 119): in a unit-supply linear Fisher market
with integer utilities `u i g ≤ U` and integer budgets `e i`, if good `g` belongs to tight sets at
two positive Invariant-preserving price vectors `p₁` and `p₂` with `p₁ g < p₂ g`, then
`p₂ g - p₁ g ≥ 1 / Δ ^ 2`, where `Δ = Fintype.card G * U ^ Fintype.card G`.

Note: [Vazirani2007], p. 119 prints `q ≤ Δ and r ≤ Δ` for fractions `p/q` and `r/s`, where
`s ≤ Δ` is intended. -/
theorem price_sub_ge_inv_sq_of_isTightSet [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]
    {M : LinearFisherMarket I G} (hsup : ∀ g, M.supply g = 1)
    {u : I → G → ℕ} (hu : ∀ i g, M.utility i g = (u i g : ℝ))
    {U : ℕ} (hU : ∀ i g, u i g ≤ U)
    {e : I → ℕ} (he : ∀ i, M.budget i = (e i : ℝ))
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g)
    {p₁ p₂ : G → ℝ} (hp₁ : ∀ g, 0 < p₁ g) (hp₂ : ∀ g, 0 < p₂ g)
    (hinv₁ : M.SatisfiesInvariant p₁) (hinv₂ : M.SatisfiesInvariant p₂)
    {S₁ S₂ : Finset G} (hS₁ : M.IsTightSet p₁ S₁) (hS₂ : M.IsTightSet p₂ S₂)
    {g : G} (hg₁ : g ∈ S₁) (hg₂ : g ∈ S₂) (hlt : p₁ g < p₂ g) :
    1 / ((Fintype.card G * U ^ Fintype.card G : ℕ) : ℝ) ^ 2 ≤ p₂ g - p₁ g := by
  obtain ⟨q₁, hq₁, -, hden₁⟩ :=
    exists_rat_price_of_isTightSet hsup hu hU he hbuyer hp₁ hinv₁ hS₁ hg₁
  obtain ⟨q₂, hq₂, -, hden₂⟩ :=
    exists_rat_price_of_isTightSet hsup hu hU he hbuyer hp₂ hinv₂ hS₂ hg₂
  set Δ : ℕ := Fintype.card G * U ^ Fintype.card G
  have hlt_q : q₁ < q₂ := by
    have : (q₁ : ℝ) < (q₂ : ℝ) := by rwa [hq₁, hq₂]
    exact_mod_cast this
  have hd₁_pos : (0 : ℤ) < (q₁.den : ℤ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero q₁.den_nz)
  have hd₂_pos : (0 : ℤ) < (q₂.den : ℤ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero q₂.den_nz)
  have hnum_lt : q₁.num * (q₂.den : ℤ) < q₂.num * (q₁.den : ℤ) := by
    have h1 : (q₁.num : ℚ) / (q₁.den : ℚ) < (q₂.num : ℚ) / (q₂.den : ℚ) := by
      rwa [Rat.num_div_den, Rat.num_div_den]
    have h2 : (q₁.num : ℚ) * (q₂.den : ℚ) < (q₂.num : ℚ) * (q₁.den : ℚ) :=
      (div_lt_div_iff₀ (Nat.cast_pos.2 (Nat.pos_of_ne_zero q₁.den_nz))
        (Nat.cast_pos.2 (Nat.pos_of_ne_zero q₂.den_nz))).1 h1
    exact_mod_cast h2
  have hdiff_int : (1 : ℤ) ≤ q₂.num * (q₁.den : ℤ) - q₁.num * (q₂.den : ℤ) := by omega
  have hdiff_r : (1 : ℝ) ≤ (q₂.num : ℝ) * (q₁.den : ℝ) - (q₁.num : ℝ) * (q₂.den : ℝ) := by
    exact_mod_cast hdiff_int
  have hd₁_pos_r : (0 : ℝ) < (q₁.den : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero q₁.den_nz)
  have hd₂_pos_r : (0 : ℝ) < (q₂.den : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero q₂.den_nz)
  have hΔ_pos : 0 < Δ := Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero q₁.den_nz) hden₁
  have hΔ_pos_r : (0 : ℝ) < (Δ : ℝ) := Nat.cast_pos.2 hΔ_pos
  have hq_diff : p₂ g - p₁ g =
      ((q₂.num : ℝ) * (q₁.den : ℝ) - (q₁.num : ℝ) * (q₂.den : ℝ)) /
        ((q₁.den : ℝ) * (q₂.den : ℝ)) := by
    have hq₁' : p₁ g = (q₁.num : ℝ) / (q₁.den : ℝ) := by
      rw [← hq₁, Rat.cast_def]
    have hq₂' : p₂ g = (q₂.num : ℝ) / (q₂.den : ℝ) := by
      rw [← hq₂, Rat.cast_def]
    rw [hq₁', hq₂']
    field_simp [hd₁_pos_r.ne', hd₂_pos_r.ne']
  rw [hq_diff]
  have hprod_le : (q₁.den : ℝ) * (q₂.den : ℝ) ≤ (Δ : ℝ) ^ 2 := by
    rw [sq]
    exact mul_le_mul (Nat.cast_le.2 hden₁) (Nat.cast_le.2 hden₂) hd₂_pos_r.le hΔ_pos_r.le
  calc
    1 / (Δ : ℝ) ^ 2 ≤ 1 / ((q₁.den : ℝ) * (q₂.den : ℝ)) :=
      one_div_le_one_div_of_le (mul_pos hd₁_pos_r hd₂_pos_r) hprod_le
    _ ≤ ((q₂.num : ℝ) * (q₁.den : ℝ) - (q₁.num : ℝ) * (q₂.den : ℝ)) /
          ((q₁.den : ℝ) * (q₂.den : ℝ)) :=
      div_le_div_of_nonneg_right hdiff_r (mul_pos hd₁_pos_r hd₂_pos_r).le

/-- **Lemma 5.16** ([Vazirani2007], Section 5.10, p. 120): elementary quadratic potential-drop
inequality for shifting `δ ≥ ∑ j ∈ s, δ_vec j` from `a + δ` onto `b j - δ_vec j` with
`0 ≤ b j ≤ a` and `0 ≤ δ_vec j`. -/
theorem sum_sq_drop_of_transfer {ι : Type*} {s : Finset ι} {a δ : ℝ} {b δ_vec : ι → ℝ}
    (ha : 0 ≤ a) (hb : ∀ j ∈ s, 0 ≤ b j ∧ b j ≤ a) (hδ : ∀ j ∈ s, 0 ≤ δ_vec j)
    (hsum : ∑ j ∈ s, δ_vec j ≤ δ) :
    a ^ 2 + ∑ j ∈ s, (b j) ^ 2 ≤
      (a + δ) ^ 2 + ∑ j ∈ s, (b j - δ_vec j) ^ 2 - δ ^ 2 := by
  have hterm : ∑ j ∈ s, ((b j - δ_vec j) ^ 2 - (b j) ^ 2) ≥ ∑ j ∈ s, (-2 * a * δ_vec j) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have h1 := (hb j hj).2
    have h2 := hδ j hj
    nlinarith [sq_nonneg (δ_vec j)]
  have hcomb : ∑ j ∈ s, (-2 * a * δ_vec j) = -2 * a * ∑ j ∈ s, δ_vec j := by
    rw [← Finset.mul_sum]
  have hsub : ((a + δ) ^ 2 + ∑ j ∈ s, (b j - δ_vec j) ^ 2) - (a ^ 2 + ∑ j ∈ s, (b j) ^ 2) =
      2 * a * δ + δ ^ 2 + ∑ j ∈ s, ((b j - δ_vec j) ^ 2 - (b j) ^ 2) := by
    rw [Finset.sum_sub_distrib]
    ring
  nlinarith

/-- **Lemma 5.15** ([Vazirani2007], Section 5.10, p. 119): for any feasible equality flow `f` and
balanced flow `fStar` in `N(p)` and any buyer `i`, the squared `ℓ₂` surplus norm drops by at least
`(M.surplus f i - M.surplus fStar i) ^ 2`.

Proved directly via convexity of the feasible flow polytope: first-order optimality of `fStar`
gives `∑ j, γ*_j * (γ_j - γ*_j) ≥ 0`, hence `‖γ‖² - ‖γ*‖² ≥ ‖γ - γ*‖² ≥ (γ_i - γ*_i)²`. -/
theorem surplusSqNorm_le_sub_sq_of_isBalancedFlow [Fintype I] [Fintype G]
    {M : LinearFisherMarket I G} {p : G → ℝ} {f fStar : G → I → ℝ}
    (hf : M.IsEqualityFlow p f) (hbal : M.IsBalancedFlow p fStar) (i : I) :
    M.surplusSqNorm fStar ≤ M.surplusSqNorm f - (M.surplus f i - M.surplus fStar i) ^ 2 := by
  let d : I → ℝ := fun j => M.surplus f j - M.surplus fStar j
  let inner : ℝ := ∑ j : I, M.surplus fStar j * d j
  let dnorm : ℝ := ∑ j : I, (d j) ^ 2
  have hdnorm_nn : 0 ≤ dnorm := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hinner_nn : 0 ≤ inner := by
    by_contra hneg
    push Not at hneg
    set t : ℝ := min (1 / 2) (-inner / (dnorm + 1))
    have ht_pos : 0 < t := lt_min (by norm_num) (div_pos (neg_pos.2 hneg) (by linarith))
    have ht_le1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have ht_le : t ≤ -inner / (dnorm + 1) := min_le_right _ _
    let ft : G → I → ℝ := fun g j => (1 - t) * fStar g j + t * f g j
    have hft : M.IsEqualityFlow p ft := by
      refine ⟨fun g j => add_nonneg (mul_nonneg (by linarith) (hbal.1.1 g j))
          (mul_nonneg ht_pos.le (hf.1 g j)), fun g j hpos => ?_, fun g => ?_, fun j => ?_⟩
      · rcases (hbal.1.1 g j).eq_or_lt with h0 | h1
        · have h2 : 0 < t * f g j := by
            dsimp only [ft] at hpos
            rw [← h0, mul_zero, zero_add] at hpos
            exact hpos
          exact hf.2.1 g j (pos_of_mul_pos_right h2 ht_pos.le)
        · exact hbal.1.2.1 g j h1
      · simp only [ft, Finset.sum_add_distrib, ← Finset.mul_sum]
        have h1 := mul_le_mul_of_nonneg_left (hbal.1.2.2.1 g) (by linarith : 0 ≤ 1 - t)
        have h2 := mul_le_mul_of_nonneg_left (hf.2.2.1 g) ht_pos.le
        linarith
      · simp only [ft, Finset.sum_add_distrib, ← Finset.mul_sum]
        have h1 := mul_le_mul_of_nonneg_left (hbal.1.2.2.2 j) (by linarith : 0 ≤ 1 - t)
        have h2 := mul_le_mul_of_nonneg_left (hf.2.2.2 j) ht_pos.le
        linarith
    have hsurp_t (j : I) : M.surplus ft j = M.surplus fStar j + t * d j := by
      simp only [surplus, ft, d, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    have hexpand : M.surplusSqNorm ft - M.surplusSqNorm fStar =
        t * (2 * inner + t * dnorm) := by
      simp only [surplusSqNorm, hsurp_t, inner, dnorm, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have htd_le : t * (dnorm + 1) ≤ -inner := (le_div_iff₀ (by linarith)).1 ht_le
    have hneg_step : 2 * inner + t * dnorm < 0 := by nlinarith
    have hlt : M.surplusSqNorm ft < M.surplusSqNorm fStar := by
      nlinarith [mul_neg_of_pos_of_neg ht_pos hneg_step]
    exact not_lt_of_ge (hbal.2 ft hft) hlt
  have hdiff : M.surplusSqNorm f - M.surplusSqNorm fStar = 2 * inner + dnorm := by
    simp only [surplusSqNorm, inner, dnorm, d, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsingle : (d i) ^ 2 ≤ dnorm :=
    Finset.single_le_sum (f := fun j => (d j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  dsimp only [d] at hsingle
  linarith

end PotentialLemmas

/-! ### Section 5.8: Price initialization and the Invariant -/

section Initialization

variable {I G : Type*} [Fintype I] [Fintype G]

/-- **DPSV initial price vector** ([Vazirani2007], Section 5.8, p. 115): starting from uniform
prices `p₀ g = 1 / n` with bang-per-buck `α i = max_g (u i g / p₀ g)`, sets
`p g = max_i (u i g / α i)`. Goods that already have an incident equality edge at `p₀` keep price
`1 / n`, while goods with no incident equality edge are lowered to `max_i (u i g / α i) < 1 / n`.
-/
noncomputable def dpsvInitPrice (M : LinearFisherMarket I G) (g : G) : ℝ :=
  if hG : (Finset.univ : Finset G).Nonempty then
    if hI : (Finset.univ : Finset I).Nonempty then
      let p0 : G → ℝ := fun _ => 1 / (Fintype.card G : ℝ)
      let α : I → ℝ := fun i => Finset.univ.sup' hG fun g' => M.bangPerBuck p0 i g'
      Finset.univ.sup' hI fun i => M.utility i g / α i
    else 0
  else 0

/-- **Initialization correctness** ([Vazirani2007], Section 5.8, p. 115): in a non-degenerate
unit-supply market where every buyer has budget at least `1`, `M.dpsvInitPrice` is strictly
positive, bounded above by `1 / n`, keeps price `1 / n` on every good already having an incident
equality edge at uniform prices `1 / n`, gives every good an incident equality edge, and satisfies
`M.SatisfiesInvariant`. -/
theorem dpsvInitPrice_spec [DecidableEq I] [DecidableEq G] {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) (hsup : ∀ g, M.supply g = 1) (hbud : ∀ i, 1 ≤ M.budget i) :
    (∀ g, 0 < M.dpsvInitPrice g) ∧
      (∀ g, M.dpsvInitPrice g ≤ 1 / (Fintype.card G : ℝ)) ∧
      (∀ g, (∃ i, M.IsEqualityEdge (fun _ => 1 / (Fintype.card G : ℝ)) i g) →
        M.dpsvInitPrice g = 1 / (Fintype.card G : ℝ)) ∧
      (∀ g, ∃ i, M.IsEqualityEdge M.dpsvInitPrice i g) ∧
      M.SatisfiesInvariant M.dpsvInitPrice := by
  by_cases hG : (Finset.univ : Finset G).Nonempty
  · have hG' := hG
    obtain ⟨g_any, -⟩ := hG'
    obtain ⟨i_any, -⟩ := hnd.good_desired g_any
    have hI : (Finset.univ : Finset I).Nonempty := ⟨i_any, Finset.mem_univ i_any⟩
    have hn_pos : (0 : ℝ) < (Fintype.card G : ℝ) := Nat.cast_pos.2 (Finset.card_pos.2 hG)
    let p0 : G → ℝ := fun _ => 1 / (Fintype.card G : ℝ)
    let α : I → ℝ := fun i => Finset.univ.sup' hG fun g' => M.bangPerBuck p0 i g'
    have hp0_pos : ∀ g, 0 < p0 g := fun _ => div_pos one_pos hn_pos
    have hα_pos : ∀ i, 0 < α i := fun i => by
      obtain ⟨g, hg⟩ := hnd.buyer_nonsatiated i
      have hle : M.utility i g / p0 g ≤ α i := by
        rw [← M.bangPerBuck_eq p0 i g]
        exact Finset.le_sup' (fun g' => M.bangPerBuck p0 i g') (Finset.mem_univ g)
      exact (div_pos hg (hp0_pos g)).trans_le hle
    have hinit_eq (g : G) : M.dpsvInitPrice g = Finset.univ.sup' hI fun i => M.utility i g / α i :=
      by simp [dpsvInitPrice, hG, hI, p0, α]
    have hp_pos : ∀ g, 0 < M.dpsvInitPrice g := fun g => by
      obtain ⟨i, hi⟩ := hnd.good_desired g
      rw [hinit_eq g]
      exact (div_pos hi (hα_pos i)).trans_le
        (Finset.le_sup' (fun k => M.utility k g / α k) (Finset.mem_univ i))
    have hp_le : ∀ g, M.dpsvInitPrice g ≤ 1 / (Fintype.card G : ℝ) := fun g => by
      rw [hinit_eq g]
      refine Finset.sup'_le hI _ fun i _ => ?_
      have h1 : M.utility i g / p0 g ≤ α i := by
        rw [← M.bangPerBuck_eq p0 i g]
        exact Finset.le_sup' (fun g' => M.bangPerBuck p0 i g') (Finset.mem_univ g)
      have h2 : M.utility i g ≤ α i * p0 g := (div_le_iff₀ (hp0_pos g)).1 h1
      exact (div_le_iff₀ (hα_pos i)).2 (by linarith)
    have hbb_le (i : I) (g : G) : M.bangPerBuck M.dpsvInitPrice i g ≤ α i := by
      have h1 : M.utility i g / α i ≤ M.dpsvInitPrice g := by
        rw [hinit_eq g]
        exact Finset.le_sup' (fun k => M.utility k g / α k) (Finset.mem_univ i)
      have h2 : M.utility i g ≤ M.dpsvInitPrice g * α i := (div_le_iff₀ (hα_pos i)).1 h1
      rw [bangPerBuck_eq]
      exact (div_le_iff₀ (hp_pos g)).2 (by linarith)
    have hgood_edge : ∀ g, ∃ i, M.IsEqualityEdge M.dpsvInitPrice i g := fun g => by
      obtain ⟨i, -, hi_eq⟩ := Finset.exists_mem_eq_sup' hI (fun k => M.utility k g / α k)
      have hp_eq : M.dpsvInitPrice g = M.utility i g / α i := (hinit_eq g).trans hi_eq
      refine ⟨i, fun g' => ?_⟩
      have hbb_eq : M.bangPerBuck M.dpsvInitPrice i g = α i := by
        rw [bangPerBuck_eq, hp_eq, div_div_eq_mul_div, mul_div_cancel_left₀]
        have hu_pos : 0 < M.utility i g := by
          have := hp_pos g
          rw [hp_eq] at this
          exact (div_pos_iff_of_pos_right (hα_pos i)).1 this
        exact hu_pos.ne'
      rw [hbb_eq]
      exact hbb_le i g'
    have hsum_le_one : ∑ g : G, M.dpsvInitPrice g ≤ 1 := by
      calc
        ∑ g : G, M.dpsvInitPrice g ≤ ∑ _g : G, (1 / (Fintype.card G : ℝ)) :=
          Finset.sum_le_sum fun g _ => hp_le g
        _ = (Fintype.card G : ℝ) * (1 / (Fintype.card G : ℝ)) := by simp
        _ = 1 := mul_one_div_cancel hn_pos.ne'
    have hinv : M.SatisfiesInvariant M.dpsvInitPrice := by
      rw [satisfiesInvariant_iff fun g => (hp_pos g).le]
      intro S
      rcases S.eq_empty_or_nonempty with rfl | ⟨g₀, hg₀⟩
      · simp only [goodValue, budgetSum, Finset.sum_empty]
        exact Finset.sum_nonneg fun i _ => M.budget_nonneg i
      · obtain ⟨i₀, hE₀⟩ := hgood_edge g₀
        have hi₀_mem : i₀ ∈ M.buyerNeighborhood M.dpsvInitPrice S :=
          mem_buyerNeighborhood.2 ⟨g₀, hg₀, hE₀⟩
        calc
          M.goodValue M.dpsvInitPrice S = ∑ g ∈ S, M.dpsvInitPrice g := by simp [goodValue, hsup]
          _ ≤ ∑ g : G, M.dpsvInitPrice g :=
              Finset.sum_le_univ_sum_of_nonneg fun g => (hp_pos g).le
          _ ≤ 1 := hsum_le_one
          _ ≤ M.budget i₀ := hbud i₀
          _ ≤ M.budgetSum (M.buyerNeighborhood M.dpsvInitPrice S) :=
              Finset.single_le_sum (fun i _ => M.budget_nonneg i) hi₀_mem
    have hp_eq_of_edge : ∀ g,
        (∃ i, M.IsEqualityEdge (fun _ => 1 / (Fintype.card G : ℝ)) i g) →
        M.dpsvInitPrice g = 1 / (Fintype.card G : ℝ) := fun g ⟨i, hE⟩ => by
      refine le_antisymm (hp_le g) ?_
      have hα_eq : M.utility i g / p0 g = α i := by
        have h1 : M.bangPerBuck p0 i g = α i := le_antisymm
          (Finset.le_sup' (fun g' => M.bangPerBuck p0 i g') (Finset.mem_univ g))
          (Finset.sup'_le hG _ fun g' _ => hE g')
        rwa [bangPerBuck_eq] at h1
      have hge : p0 g ≤ M.utility i g / α i := by
        rw [← hα_eq, div_div_eq_mul_div, mul_div_cancel_left₀]
        have hu_pos : 0 < M.utility i g := by
          have := hα_pos i
          rw [← hα_eq] at this
          exact (div_pos_iff_of_pos_right (hp0_pos g)).1 this
        exact hu_pos.ne'
      rw [hinit_eq g]
      exact hge.trans (Finset.le_sup' (fun k => M.utility k g / α k) (Finset.mem_univ i))
    exact ⟨hp_pos, hp_le, hp_eq_of_edge, hgood_edge, hinv⟩
  · have : IsEmpty G := ⟨fun g => hG ⟨g, Finset.mem_univ g⟩⟩
    refine ⟨fun g => isEmptyElim g, fun g => isEmptyElim g, fun g => isEmptyElim g,
      fun g => isEmptyElim g, ?_⟩
    rw [satisfiesInvariant_iff fun g => isEmptyElim g]
    intro S
    have hS : S = ∅ := Finset.eq_empty_of_isEmpty S
    subst hS
    simp only [goodValue, budgetSum, Finset.sum_empty]
    exact Finset.sum_nonneg fun i _ => M.budget_nonneg i

end Initialization

/-! ### Section 5.8 & 5.10: Active subgraph, Event 1 / Event 2, and Lemmas 5.17–5.20 -/

section PhaseMechanics

variable {I G : Type u}

/-- Scale prices of goods in `J` by `x` while leaving goods outside `J` unchanged
([Vazirani2007], Section 5.8, p. 116). -/
@[expose] def scaleActivePrices [DecidableEq G] (p : G → ℝ) (J : Finset G) (x : ℝ) (g : G) : ℝ :=
  if g ∈ J then x * p g else p g

private theorem scaleActivePrices_pos [DecidableEq G] {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (J : Finset G) {x : ℝ} (hx : 0 < x) (g : G) :
    0 < scaleActivePrices p J x g := by
  dsimp only [scaleActivePrices]
  split_ifs
  · exact mul_pos hx (hp g)
  · exact hp g

/-- Active goods `J = {g | ∃ i ∈ H, M.IsEqualityEdge p i g}` desired by buyers in `H`
([Vazirani2007], Section 5.8, p. 116). -/
noncomputable def activeGoods [Fintype G] (M : LinearFisherMarket I G) (p : G → ℝ)
    (H : Finset I) : Finset G :=
  open scoped Classical in Finset.univ.filter fun g => ∃ i ∈ H, M.IsEqualityEdge p i g

/-- Membership in `M.activeGoods p H`: good `g` is active iff some buyer `i ∈ H` has an equality
edge to `g` at prices `p`. -/
theorem mem_activeGoods [Fintype G] {M : LinearFisherMarket I G} {p : G → ℝ}
    {H : Finset I} {g : G} :
    g ∈ M.activeGoods p H ↔ ∃ i ∈ H, M.IsEqualityEdge p i g := by
  classical
  simp [activeGoods]

/-- Submarket restricting buyer budgets to `H` (zeroing budgets outside `H`) while keeping supplies
and utilities unchanged, allowing `findTightSetProgram` to run directly on `(J, H)` for Event 1
([Vazirani2007], Sections 5.8–5.9). -/
private noncomputable def activeMarket (M : LinearFisherMarket I G) (H : Finset I) :
    LinearFisherMarket I G where
  budget i := open scoped Classical in if i ∈ H then M.budget i else 0
  supply := M.supply
  utility := M.utility
  budget_nonneg i := by
    classical
    split_ifs
    · exact M.budget_nonneg i
    · exact le_rfl
  supply_nonneg := M.supply_nonneg
  utility_nonneg := M.utility_nonneg

private theorem activeMarket_budgetSum [DecidableEq I] (M : LinearFisherMarket I G)
    (H T : Finset I) :
    (M.activeMarket H).budgetSum T = M.budgetSum (T ∩ H) := by
  simp only [budgetSum, activeMarket]
  rw [← Finset.sum_ite_mem]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ H <;> simp [hi]

private theorem activeMarket_isEqualityEdge (M : LinearFisherMarket I G) (H : Finset I)
    (p : G → ℝ) (i : I) (g : G) :
    (M.activeMarket H).IsEqualityEdge p i g ↔ M.IsEqualityEdge p i g := by
  simp [IsEqualityEdge, bangPerBuck_eq, activeMarket]

private theorem activeMarket_buyerNeighborhood [Fintype I] (M : LinearFisherMarket I G)
    (H : Finset I) (p : G → ℝ) (S : Finset G) :
    (M.activeMarket H).buyerNeighborhood p S = M.buyerNeighborhood p S := by
  ext i
  simp [mem_buyerNeighborhood, activeMarket_isEqualityEdge]

private theorem activeMarket_goodValue (M : LinearFisherMarket I G) (H : Finset I)
    (p : G → ℝ) (S : Finset G) :
    (M.activeMarket H).goodValue p S = M.goodValue p S := rfl

/-- Candidate `(buyer, good)` pairs for Event 2: active buyer `i ∈ H`, inactive good `g ∉ J`, and
strictly positive utility `0 < M.utility i g`. -/
private noncomputable def event2Pairs [Fintype G] [DecidableEq G]
    (M : LinearFisherMarket I G) (H : Finset I) (J : Finset G) : Finset (I × G) :=
  open scoped Classical in
  (H ×ˢ (Finset.univ \ J)).filter fun ig => 0 < M.utility ig.1 ig.2

/-- **Event-2 scale ratio** ([Vazirani2007], Section 5.8, p. 116): the smallest `x > 1` at which
an active buyer `i ∈ H` gains a new equality edge to an inactive good `g ∉ J`, or `none` when no
buyer in `H` derives positive utility from any good outside `J`. -/
noncomputable def event2Ratio [Fintype G] [DecidableEq G]
    (M : LinearFisherMarket I G) (p : G → ℝ) (H : Finset I) (J : Finset G) : Option ℝ :=
  open scoped Classical in
  if h : (event2Pairs M H J).Nonempty then
    some ((event2Pairs M H J).inf' h fun ig =>
      maxBangPerBuck M p ig.1 * p ig.2 / M.utility ig.1 ig.2)
  else none

/-- Closure of an active buyer set `H` under incoming residual paths in `R(p, f) - {s, t}`. -/
private def IsResidualClosed (M : LinearFisherMarket I G)
    (p : G → ℝ) (f : G → I → ℝ) (H : Finset I) : Prop :=
  ∀ u v : I, M.ResidualReachable p f u v → v ∈ H → u ∈ H

private theorem no_flow_from_activeGoods_outside [Fintype I] [Fintype G]
    {M : LinearFisherMarket I G} {p : G → ℝ} {f : G → I → ℝ} {H : Finset I}
    (hf : M.IsEqualityFlow p f) (hclosed : IsResidualClosed M p f H)
    {g : G} (hg : g ∈ M.activeGoods p H) {k : I} (hk : k ∉ H) :
    f g k = 0 := by
  obtain ⟨i, hiH, hE⟩ := mem_activeGoods.1 hg
  refine le_antisymm (not_lt.1 fun hpos => hk ?_) (hf.1 g k)
  exact hclosed k i (Relation.ReflTransGen.single ⟨g, hpos, hE⟩) hiH

/-- `M.event2Ratio p H J = none` iff no buyer `i ∈ H` derives positive utility from any good
`g ∉ J`. -/
theorem event2Ratio_eq_none_iff [Fintype G] [DecidableEq G] {M : LinearFisherMarket I G}
    {p : G → ℝ} {H : Finset I} {J : Finset G} :
    M.event2Ratio p H J = none ↔ ∀ i ∈ H, ∀ g ∉ J, M.utility i g = 0 := by
  classical
  unfold event2Ratio
  constructor
  · intro h i hi g hg
    split_ifs at h with hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hnot : (i, g) ∉ event2Pairs M H J := by rw [hne]; exact Finset.notMem_empty _
    have hle : ¬ 0 < M.utility i g := fun hu => hnot <| Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨hi, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hg⟩⟩, hu⟩
    exact le_antisymm (not_lt.1 hle) (M.utility_nonneg i g)
  · intro h
    have hempty : ¬ (event2Pairs M H J).Nonempty := by
      rintro ⟨⟨i, g⟩, hig⟩
      obtain ⟨hmem, hu⟩ := Finset.mem_filter.1 hig
      obtain ⟨hi, hg⟩ := Finset.mem_product.1 hmem
      exact hu.ne' (h i hi g (Finset.mem_sdiff.1 hg).2)
    simp [hempty]

/-- At positive prices `p`, every Event-2 scale ratio `r` returned by
`M.event2Ratio p H (M.activeGoods p H)` satisfies `1 < r`. -/
theorem one_lt_event2Ratio [Fintype G] [DecidableEq G]
    {M : LinearFisherMarket I G} {p : G → ℝ} (hp : ∀ g, 0 < p g)
    {H : Finset I} {x2 : ℝ} (hx2 : M.event2Ratio p H (M.activeGoods p H) = some x2) :
    1 < x2 := by
  classical
  unfold event2Ratio at hx2
  split_ifs at hx2 with hne
  · injection hx2 with hx2
    rw [← hx2, Finset.lt_inf'_iff]
    intro ig hig
    obtain ⟨hmem, hu_pos⟩ := Finset.mem_filter.1 hig
    obtain ⟨hiH, hgNotJ⟩ := Finset.mem_product.1 hmem
    have hgNot : ig.2 ∉ M.activeGoods p H := (Finset.mem_sdiff.1 hgNotJ).2
    have hnotE : ¬ M.IsEqualityEdge p ig.1 ig.2 := fun hE =>
      hgNot (mem_activeGoods.2 ⟨ig.1, hiH, hE⟩)
    have hlt : M.bangPerBuck p ig.1 ig.2 < maxBangPerBuck M p ig.1 :=
      lt_of_le_of_ne (bangPerBuck_le_maxBangPerBuck ig.1 ig.2)
        (fun heq => hnotE ((isEqualityEdge_iff_eq_maxBangPerBuck ig.1 ig.2).2 heq))
    rw [bangPerBuck_eq, div_lt_iff₀ (hp ig.2)] at hlt
    exact (one_lt_div hu_pos).2 (by linarith)

/-- Characterization of upper bounds on `M.event2Ratio p H J` at positive prices `p`: `x` does not
exceed the Event-2 ratio (vacuously when `M.event2Ratio p H J = none`) iff for every active buyer
`i ∈ H` and inactive good `g ∉ J` with `0 < M.utility i g`, there exists a good `g'` such that
`x * M.bangPerBuck p i g ≤ M.bangPerBuck p i g'`. -/
theorem le_event2Ratio_iff [Fintype G] [DecidableEq G] {M : LinearFisherMarket I G}
    {p : G → ℝ} (hp : ∀ g, 0 < p g) {H : Finset I} {J : Finset G} {x : ℝ} :
    (∀ r, M.event2Ratio p H J = some r → x ≤ r) ↔
      ∀ i ∈ H, ∀ g ∉ J, 0 < M.utility i g →
        ∃ g' : G, x * M.bangPerBuck p i g ≤ M.bangPerBuck p i g' := by
  classical
  constructor
  · intro hx i hi g hg hu
    have hmem : (i, g) ∈ event2Pairs M H J := Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨hi, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hg⟩⟩, hu⟩
    have hne : (event2Pairs M H J).Nonempty := ⟨(i, g), hmem⟩
    have hratio : M.event2Ratio p H J =
        some ((event2Pairs M H J).inf' hne fun ig =>
          maxBangPerBuck M p ig.1 * p ig.2 / M.utility ig.1 ig.2) := by
      simp [event2Ratio, hne]
    have hle : x ≤ maxBangPerBuck M p i * p g / M.utility i g :=
      (hx _ hratio).trans (Finset.inf'_le _ hmem)
    have hmul : x * M.utility i g ≤ maxBangPerBuck M p i * p g := (le_div_iff₀ hu).1 hle
    have : Nonempty G := ⟨g⟩
    obtain ⟨g', hE'⟩ := exists_isEqualityEdge M p i
    refine ⟨g', ?_⟩
    rw [(isEqualityEdge_iff_eq_maxBangPerBuck i g').1 hE', bangPerBuck_eq, ← mul_div_assoc]
    exact (div_le_iff₀ (hp g)).2 hmul
  · intro h r hr
    unfold event2Ratio at hr
    split_ifs at hr with hne
    · injection hr with hr
      rw [← hr, Finset.le_inf'_iff]
      intro ig hig
      obtain ⟨hmem, hu⟩ := Finset.mem_filter.1 hig
      obtain ⟨hi, hg⟩ := Finset.mem_product.1 hmem
      obtain ⟨g', hg'⟩ := h ig.1 hi ig.2 (Finset.mem_sdiff.1 hg).2 hu
      have hmax : x * M.bangPerBuck p ig.1 ig.2 ≤ maxBangPerBuck M p ig.1 :=
        hg'.trans (bangPerBuck_le_maxBangPerBuck ig.1 g')
      rw [bangPerBuck_eq, ← mul_div_assoc, div_le_iff₀ (hp ig.2)] at hmax
      exact (le_div_iff₀ hu).2 hmax

/-- Equality-edge characterization for active buyers `i ∈ H` when scaling `J = M.activeGoods p H`
by `1 ≤ x` not exceeding `event2Ratio`. -/
private theorem active_buyer_equalityEdge_scale [Fintype G] [DecidableEq G]
    {M : LinearFisherMarket I G} {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g) {H : Finset I} {x : ℝ} (hx1 : 1 ≤ x)
    (hx_le : ∀ r, M.event2Ratio p H (M.activeGoods p H) = some r → x ≤ r)
    {i : I} (hi : i ∈ H) :
    let J := M.activeGoods p H
    let p' := scaleActivePrices p J x
    maxBangPerBuck M p' i = maxBangPerBuck M p i / x ∧
      (∀ g ∈ J, M.IsEqualityEdge p' i g ↔ M.IsEqualityEdge p i g) := by
  intro J p'
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hG : (Finset.univ : Finset G).Nonempty := by
    obtain ⟨g, -⟩ := hbuyer i
    exact ⟨g, Finset.mem_univ g⟩
  have hα_pos : 0 < maxBangPerBuck M p i := maxBangPerBuck_pos hp (hbuyer i)
  have hbb_le : ∀ g : G, M.bangPerBuck p' i g ≤ maxBangPerBuck M p i / x := by
    intro g
    by_cases hgJ : g ∈ J
    · have hEq : M.bangPerBuck p' i g = M.bangPerBuck p i g / x := by
        simp only [bangPerBuck_eq, p', scaleActivePrices, hgJ, ↓reduceIte]
        rw [div_mul_eq_div_div_swap]
      rw [hEq]
      exact div_le_div_of_nonneg_right (bangPerBuck_le_maxBangPerBuck i g) hx_pos.le
    · simp only [bangPerBuck_eq, p', scaleActivePrices, hgJ, ↓reduceIte]
      rcases (M.utility_nonneg i g).eq_or_lt with hu0 | hu_pos
      · rw [← hu0, zero_div]
        exact div_nonneg hα_pos.le hx_pos.le
      · obtain ⟨g', hg'⟩ := (le_event2Ratio_iff hp).1 hx_le i hi g hgJ hu_pos
        have h1 : x * M.bangPerBuck p i g ≤ maxBangPerBuck M p i :=
          hg'.trans (bangPerBuck_le_maxBangPerBuck i g')
        rw [bangPerBuck_eq] at h1
        exact (le_div_iff₀ hx_pos).2 (by linarith)
  have hex_att : ∃ g₀ : G, M.bangPerBuck p' i g₀ = maxBangPerBuck M p i / x := by
    have : Nonempty G := by obtain ⟨g, _⟩ := hG; exact ⟨g⟩
    obtain ⟨g₀, hE₀⟩ := exists_isEqualityEdge M p i
    have hg₀J : g₀ ∈ J := mem_activeGoods.2 ⟨i, hi, hE₀⟩
    refine ⟨g₀, ?_⟩
    simp only [bangPerBuck_eq, p', scaleActivePrices, hg₀J, ↓reduceIte]
    rw [div_mul_eq_div_div_swap, ← bangPerBuck_eq,
      (isEqualityEdge_iff_eq_maxBangPerBuck i g₀).1 hE₀]
  have hmax_eq : maxBangPerBuck M p' i = maxBangPerBuck M p i / x := by
    obtain ⟨g₀, hg₀⟩ := hex_att
    refine le_antisymm ?_ (hg₀ ▸ bangPerBuck_le_maxBangPerBuck i g₀)
    have hdef : maxBangPerBuck M p' i = Finset.univ.sup' hG fun g => M.bangPerBuck p' i g := by
      simp [maxBangPerBuck, hG]
    rw [hdef]
    exact Finset.sup'_le hG _ fun g _ => hbb_le g
  refine ⟨hmax_eq, fun g hgJ => ?_⟩
  rw [isEqualityEdge_iff_eq_maxBangPerBuck, isEqualityEdge_iff_eq_maxBangPerBuck, hmax_eq]
  have hEq : M.bangPerBuck p' i g = M.bangPerBuck p i g / x := by
    simp only [bangPerBuck_eq, p', scaleActivePrices, hgJ, ↓reduceIte]
    rw [div_mul_eq_div_div_swap]
  rw [hEq, div_left_inj₀ hx_pos.ne']

/-- Equality-edge characterization for buyers `k` having at least one equality edge outside `J`
when `J` is scaled by `x ≥ 1` (and strictly dropped on `J` when `x > 1`). -/
private theorem outside_buyer_equalityEdge_scale [Fintype G] [DecidableEq G]
    {M : LinearFisherMarket I G} {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g) {J : Finset G} {x : ℝ} (hx1 : 1 ≤ x)
    {k : I} {g_out : G} (hg_out : g_out ∉ J) (hE_out : M.IsEqualityEdge p k g_out) :
    let p' := scaleActivePrices p J x
    maxBangPerBuck M p' k = maxBangPerBuck M p k ∧
      (∀ g ∉ J, M.IsEqualityEdge p' k g ↔ M.IsEqualityEdge p k g) ∧
      (1 < x → ∀ g ∈ J, ¬ M.IsEqualityEdge p' k g) := by
  intro p'
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hG : (Finset.univ : Finset G).Nonempty := ⟨g_out, Finset.mem_univ g_out⟩
  have hα_pos : 0 < maxBangPerBuck M p k := maxBangPerBuck_pos hp (hbuyer k)
  have hbb_le : ∀ g : G, M.bangPerBuck p' k g ≤ maxBangPerBuck M p k := by
    intro g
    by_cases hgJ : g ∈ J
    · have hEq : M.bangPerBuck p' k g = M.bangPerBuck p k g / x := by
        simp only [bangPerBuck_eq, p', scaleActivePrices, hgJ, ↓reduceIte]
        rw [div_mul_eq_div_div_swap]
      rw [hEq]
      have hnn : 0 ≤ M.bangPerBuck p k g := by
        rw [bangPerBuck_eq]; exact div_nonneg (M.utility_nonneg k g) (hp g).le
      exact (div_le_self hnn hx1).trans (bangPerBuck_le_maxBangPerBuck k g)
    · have hEq : M.bangPerBuck p' k g = M.bangPerBuck p k g := by
        simp only [bangPerBuck_eq, p', scaleActivePrices, hgJ, ↓reduceIte]
      rw [hEq]
      exact bangPerBuck_le_maxBangPerBuck k g
  have hbb_out : M.bangPerBuck p' k g_out = maxBangPerBuck M p k := by
    have hEq : M.bangPerBuck p' k g_out = M.bangPerBuck p k g_out := by
      simp only [bangPerBuck_eq, p', scaleActivePrices, hg_out, ↓reduceIte]
    rw [hEq]
    exact (isEqualityEdge_iff_eq_maxBangPerBuck k g_out).1 hE_out
  have hmax_eq : maxBangPerBuck M p' k = maxBangPerBuck M p k := by
    refine le_antisymm ?_ (hbb_out ▸ bangPerBuck_le_maxBangPerBuck k g_out)
    have hdef : maxBangPerBuck M p' k = Finset.univ.sup' hG fun g => M.bangPerBuck p' k g := by
      simp [maxBangPerBuck, hG]
    rw [hdef]
    exact Finset.sup'_le hG _ fun g _ => hbb_le g
  refine ⟨hmax_eq, fun g hgJ => ?_, fun hx_gt g hgJ hE => ?_⟩
  · rw [isEqualityEdge_iff_eq_maxBangPerBuck, isEqualityEdge_iff_eq_maxBangPerBuck, hmax_eq]
    simp only [bangPerBuck_eq, p', scaleActivePrices, hgJ, ↓reduceIte]
  · rw [isEqualityEdge_iff_eq_maxBangPerBuck, hmax_eq] at hE
    have hEq : M.bangPerBuck p' k g = M.bangPerBuck p k g / x := by
      simp only [bangPerBuck_eq, p', scaleActivePrices, hgJ, ↓reduceIte]
      rw [div_mul_eq_div_div_swap]
    rw [hEq] at hE
    have hlt : M.bangPerBuck p k g / x < maxBangPerBuck M p k := by
      have h1 : M.bangPerBuck p k g / x ≤ maxBangPerBuck M p k / x :=
        div_le_div_of_nonneg_right (bangPerBuck_le_maxBangPerBuck k g) hx_pos.le
      exact h1.trans_lt (div_lt_self hα_pos hx_gt)
    linarith

/-- **Lemma 5.17** ([Vazirani2007], Section 5.10, p. 120): if `f` is a feasible equality flow in
`N(p)` and `H` is closed under incoming residual paths in `R(p, f) - {s, t}`, then `f` remains a
feasible equality flow in `N(scaleActivePrices p J x)` for every `x ≥ 1` not exceeding `event2Ratio`
(where `J = M.activeGoods p H`). -/
theorem isEqualityFlow_scaleActivePrices [Fintype I] [Fintype G] [DecidableEq G]
    {M : LinearFisherMarket I G} {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g) {f : G → I → ℝ}
    (hf : M.IsEqualityFlow p f) {H : Finset I}
    (hclosed : ∀ u v, M.ResidualReachable p f u v → v ∈ H → u ∈ H)
    {x : ℝ} (hx1 : 1 ≤ x)
    (hx_le : ∀ r, M.event2Ratio p H (M.activeGoods p H) = some r → x ≤ r) :
    M.IsEqualityFlow (scaleActivePrices p (M.activeGoods p H) x) f := by
  set J := M.activeGoods p H
  set p' := scaleActivePrices p J x
  refine ⟨hf.1, fun g i hpos => ?_, fun g => ?_, hf.2.2.2⟩
  · have hE : M.IsEqualityEdge p i g := hf.2.1 g i hpos
    by_cases hgJ : g ∈ J
    · have hiH : i ∈ H := by
        by_contra hnot
        linarith [no_flow_from_activeGoods_outside hf hclosed hgJ hnot]
      exact (active_buyer_equalityEdge_scale hp hbuyer hx1 hx_le hiH).2 g hgJ |>.2 hE
    · exact (outside_buyer_equalityEdge_scale hp hbuyer hx1 hgJ hE).2.1 g hgJ |>.2 hE
  · by_cases hgJ : g ∈ J
    · simp only [p', scaleActivePrices, hgJ, ↓reduceIte]
      have hle : p g * M.supply g ≤ x * p g * M.supply g := by
        have hnn : 0 ≤ p g * M.supply g := mul_nonneg (hp g).le (M.supply_nonneg g)
        calc
          p g * M.supply g = 1 * (p g * M.supply g) := (one_mul _).symm
          _ ≤ x * (p g * M.supply g) := mul_le_mul_of_nonneg_right hx1 hnn
          _ = x * p g * M.supply g := by ring
      exact (hf.2.2.1 g).trans hle
    · simp only [p', scaleActivePrices, hgJ, ↓reduceIte]
      exact hf.2.2.1 g

/-- **Corollary 5.18** ([Vazirani2007], Section 5.10, p. 120): the squared `ℓ₂` surplus norm is
monotonically nonincreasing across active price-scaling iterations. -/
theorem surplusSqNorm_scaleActivePrices_le [Fintype I] [Fintype G] [DecidableEq G]
    {M : LinearFisherMarket I G} {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g) {f f' : G → I → ℝ}
    (hf : M.IsEqualityFlow p f) {H : Finset I}
    (hclosed : ∀ u v, M.ResidualReachable p f u v → v ∈ H → u ∈ H)
    {x : ℝ} (hx1 : 1 ≤ x)
    (hx_le : ∀ r, M.event2Ratio p H (M.activeGoods p H) = some r → x ≤ r)
    (hbal' : M.IsBalancedFlow (scaleActivePrices p (M.activeGoods p H) x) f') :
    M.surplusSqNorm f' ≤ M.surplusSqNorm f :=
  hbal'.2 f (isEqualityFlow_scaleActivePrices hp hbuyer hf hclosed hx1 hx_le)

/-- **Lemma 5.19** ([Vazirani2007], Section 5.10, p. 120): when `H' = {u | ∃ v ∈ H,
M.ResidualReachable p' f' u v}` expands `H` in the residual graph of a balanced flow `f'` in
`N(p')`, the minimum surplus over `H'` is achieved by some buyer `i ∈ H`. Consequently, if
`δ' < δ` where `δ = min_{i ∈ H} M.surplus f i` and `δ' = min_{u ∈ H'} M.surplus f' u`, then there
exists `i ∈ H` with `M.surplus f i - M.surplus f' i ≥ δ - δ'`. -/
theorem exists_surplus_drop_of_residual_expand [Fintype I] [Fintype G]
    {M : LinearFisherMarket I G} {p' : G → ℝ} (hp' : ∀ g, 0 ≤ p' g)
    {f f' : G → I → ℝ} (hbal' : M.IsBalancedFlow p' f')
    {H : Finset I} (hH : H.Nonempty) :
    let H' : Finset I := open scoped Classical in
      Finset.univ.filter fun u => ∃ v ∈ H, M.ResidualReachable p' f' u v
    have hH' : H'.Nonempty := by
      classical
      obtain ⟨v, hv⟩ := hH
      exact ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ v, v, hv, .refl⟩⟩
    ∃ i ∈ H,
      H.inf' hH (M.surplus f) - H'.inf' hH' (M.surplus f') ≤ M.surplus f i - M.surplus f' i := by
  classical
  intro H' hH'
  have hprop1 : M.SatisfiesPropertyOne p' f' :=
    (isBalancedFlow_iff_satisfiesPropertyOne (hbal'.isMaxEqualityFlow hp')).1 hbal'
  obtain ⟨u, huH', hu_eq⟩ := Finset.exists_mem_eq_inf' hH' (M.surplus f')
  obtain ⟨v, hvH, hreach⟩ := (Finset.mem_filter.1 huH').2
  have hv_le_u : M.surplus f' v ≤ M.surplus f' u := by
    by_contra hlt
    push Not at hlt
    exact hprop1 u v hlt hreach
  have hv_le_inf : M.surplus f' v ≤ H'.inf' hH' (M.surplus f') := hu_eq ▸ hv_le_u
  have hinf_le_v : H.inf' hH (M.surplus f) ≤ M.surplus f v := Finset.inf'_le (M.surplus f) hvH
  exact ⟨v, hvH, by linarith⟩

/-- **Lemma 5.20** ([Vazirani2007], Section 5.10, p. 120): if the minimum active surplus strictly
drops from `δ` to `δ'` across an iteration, the squared `ℓ₂` surplus norm drops by at least
`(δ - δ') ^ 2`. -/
theorem surplusSqNorm_drop_of_minSurplus_lt [Fintype I] [Fintype G] [DecidableEq G]
    {M : LinearFisherMarket I G} {p : G → ℝ} (hp : ∀ g, 0 < p g)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g) {f f' : G → I → ℝ}
    (hf : M.IsEqualityFlow p f) {H : Finset I} (hH : H.Nonempty)
    (hclosed : ∀ u v, M.ResidualReachable p f u v → v ∈ H → u ∈ H)
    {x : ℝ} (hx1 : 1 ≤ x)
    (hx_le : ∀ r, M.event2Ratio p H (M.activeGoods p H) = some r → x ≤ r)
    (hbal' : M.IsBalancedFlow (scaleActivePrices p (M.activeGoods p H) x) f') :
    let p' := scaleActivePrices p (M.activeGoods p H) x
    let H' : Finset I := open scoped Classical in
      Finset.univ.filter fun u => ∃ v ∈ H, M.ResidualReachable p' f' u v
    have hH' : H'.Nonempty := by
      classical
      obtain ⟨v, hv⟩ := hH
      exact ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ v, v, hv, .refl⟩⟩
    H'.inf' hH' (M.surplus f') < H.inf' hH (M.surplus f) →
      M.surplusSqNorm f' ≤
        M.surplusSqNorm f - (H.inf' hH (M.surplus f) - H'.inf' hH' (M.surplus f')) ^ 2 := by
  intro p' H' hH' hlt
  have hp'_nn : ∀ g, 0 ≤ p' g := fun g => by
    dsimp only [p', scaleActivePrices]
    split_ifs
    · exact mul_nonneg (by linarith) (hp g).le
    · exact (hp g).le
  obtain ⟨i, -, hdrop⟩ := exists_surplus_drop_of_residual_expand hp'_nn hbal' hH
  have hf_feas' : M.IsEqualityFlow p' f :=
    isEqualityFlow_scaleActivePrices hp hbuyer hf hclosed hx1 hx_le
  have h515 := surplusSqNorm_le_sub_sq_of_isBalancedFlow hf_feas' hbal' i
  have hsq : (H.inf' hH (M.surplus f) - H'.inf' hH' (M.surplus f')) ^ 2 ≤
      (M.surplus f i - M.surplus f' i) ^ 2 := by
    have hpos : 0 ≤ H.inf' hH (M.surplus f) - H'.inf' hH' (M.surplus f') := sub_nonneg.2 hlt.le
    nlinarith
  linarith

end PhaseMechanics

/-! ### Phase execution, Event 1 / Event 2 invariants, and Lemmas 5.14 & 5.21 -/

section PhaseExecution

variable {I G : Type u} [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]

/-- Output of one phase of the DPSV algorithm ([Vazirani2007], Section 5.8, p. 116). -/
structure DPSVPhaseResult (I G : Type u) where
  /-- Price vector at the end of the phase. -/
  price : G → ℝ
  /-- Balanced equality flow in `N(price)`. -/
  flow : G → I → ℝ
  /-- Active subset `S₁ ⊆ J` achieving Event 1 at the end of the phase. -/
  tightSet : Finset G
  /-- Number of Event-1 / Event-2 iterations executed in the phase. -/
  iters : ℕ

/-- Inner iteration loop of one DPSV phase in `FreeM (MaxFlowQuery I G)` ([Vazirani2007],
Section 5.8, p. 116). -/
private noncomputable def dpsvPhaseLoop (M : LinearFisherMarket I G) :
    ℕ → (G → ℝ) → (G → I → ℝ) → Finset I → FreeM (MaxFlowQuery I G) (DPSVPhaseResult I G)
  | 0, p, f, _ => pure ⟨p, f, ∅, 0⟩
  | k + 1, p, _, H => do
      let J := M.activeGoods p H
      let (x1, S1) ← (M.activeMarket H).findTightSetProgram p J
      match M.event2Ratio p H J with
      | some x2 =>
        if x2 < x1 then
          let p' := scaleActivePrices p J x2
          let f' ← M.balancedFlowProgram p'
          let H' : Finset I := open scoped Classical in
            Finset.univ.filter fun u => ∃ v ∈ H, M.ResidualReachable p' f' u v
          let res ← dpsvPhaseLoop M k p' f' H'
          pure ⟨res.price, res.flow, res.tightSet, res.iters + 1⟩
        else
          let p' := scaleActivePrices p J x1
          let f' ← M.balancedFlowProgram p'
          pure ⟨p', f', S1, 1⟩
      | none =>
        let p' := scaleActivePrices p J x1
        let f' ← M.balancedFlowProgram p'
        pure ⟨p', f', S1, 1⟩

/-- **One full phase of the DPSV algorithm** ([Vazirani2007], Section 5.8, p. 116): given current
prices `p` and balanced flow `f`, returns immediately when all buyer surpluses vanish, and
otherwise initializes `H₀ = {i | M.surplus f i = max_j M.surplus f j}` and runs `dpsvPhaseLoop`
for at most `Fintype.card G` iterations. -/
noncomputable def dpsvPhaseProgram (M : LinearFisherMarket I G) (p : G → ℝ) (f : G → I → ℝ) :
    FreeM (MaxFlowQuery I G) (DPSVPhaseResult I G) :=
  open scoped Classical in
  if ∀ i : I, M.surplus f i = 0 then
    pure ⟨p, f, ∅, 0⟩
  else if hI : (Finset.univ : Finset I).Nonempty then
    let δ := Finset.univ.sup' hI (M.surplus f)
    let H0 := Finset.univ.filter fun i => M.surplus f i = δ
    dpsvPhaseLoop M (Fintype.card G) p f H0
  else
    pure ⟨p, f, ∅, 0⟩

/-- Invariant preservation under scaling `J = M.activeGoods p H` by `1 ≤ x ≤ min x₁ x₂`. -/
private theorem satisfiesInvariant_scaleActivePrices {M : LinearFisherMarket I G} {p : G → ℝ}
    (hp : ∀ g, 0 < p g) (hsup_pos : ∀ g, 0 < M.supply g)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g) (hinv : M.SatisfiesInvariant p)
    {H : Finset I} (hH : H.Nonempty)
    {x : ℝ} (hx1 : 1 ≤ x)
    (hx_le1 : x ≤ (M.activeMarket H).minTightRatio p (M.activeGoods p H)
      (by
        obtain ⟨i₀, hi₀⟩ := hH
        obtain ⟨g₀, -⟩ := hbuyer i₀
        have : Nonempty G := ⟨g₀⟩
        obtain ⟨g, hE⟩ := exists_isEqualityEdge M p i₀
        exact ⟨g, mem_activeGoods.2 ⟨i₀, hi₀, hE⟩⟩))
    (hx_le2 : ∀ r, M.event2Ratio p H (M.activeGoods p H) = some r → x ≤ r) :
    M.SatisfiesInvariant (scaleActivePrices p (M.activeGoods p H) x) := by
  set J := M.activeGoods p H
  set p' := scaleActivePrices p J x
  have hJ : J.Nonempty := by
    obtain ⟨i₀, hi₀⟩ := hH
    obtain ⟨g₀, -⟩ := hbuyer i₀
    have : Nonempty G := ⟨g₀⟩
    obtain ⟨g, hE⟩ := exists_isEqualityEdge M p i₀
    exact ⟨g, mem_activeGoods.2 ⟨i₀, hi₀, hE⟩⟩
  have hp'_pos : ∀ g, 0 < p' g := fun g => by
    dsimp only [p', scaleActivePrices]
    split_ifs
    · exact mul_pos (by linarith) (hp g)
    · exact hp g
  rw [satisfiesInvariant_iff fun g => (hp'_pos g).le]
  intro S
  set SJ := S ∩ J
  set SR := S \ J
  have hS_union : SJ ∪ SR = S := by
    ext g
    by_cases hg : g ∈ J <;> simp [SJ, SR]
  have hS_disj : Disjoint SJ SR := Finset.disjoint_sdiff.mono_left Finset.inter_subset_right
  have hval_split : M.goodValue p' S = x * M.goodValue p SJ + M.goodValue p SR := by
    rw [← hS_union, goodValue, Finset.sum_union hS_disj]
    have h1 : ∑ g ∈ SJ, p' g * M.supply g = x * M.goodValue p SJ := by
      rw [goodValue, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      have hgJ : g ∈ J := (Finset.mem_inter.1 hg).2
      simp only [p', scaleActivePrices, hgJ, ↓reduceIte]
      ring
    have h2 : ∑ g ∈ SR, p' g * M.supply g = M.goodValue p SR := by
      rw [goodValue]
      refine Finset.sum_congr rfl fun g hg => ?_
      have hgJ : g ∉ J := (Finset.mem_sdiff.1 hg).2
      simp only [p', scaleActivePrices, hgJ, ↓reduceIte]
    rw [h1, h2]
  -- Active part `SJ ⊆ J`: bounded by `M.budgetSum (Γ_p(SJ) ∩ H)`.
  have hSJ_bound : x * M.goodValue p SJ ≤ M.budgetSum (M.buyerNeighborhood p SJ ∩ H) := by
    have hgv_nn : 0 ≤ M.goodValue p SJ :=
      Finset.sum_nonneg fun g _ => mul_nonneg (hp g).le (M.supply_nonneg g)
    have hstep1 := mul_le_mul_of_nonneg_right hx_le1 hgv_nn
    have hstep2 := minTightRatio_mul_goodValue_le (M := M.activeMarket H) (p := p) hJ
      (fun g _ => mul_pos (hp g) (hsup_pos g)) (Finset.inter_subset_right (s₁ := S) (s₂ := J))
    rw [activeMarket_goodValue, activeMarket_buyerNeighborhood, activeMarket_budgetSum] at hstep2
    exact hstep1.trans hstep2
  -- Inactive part `SR ⊆ univ \ J`: `Γ_p(SR)` is disjoint from `H` and preserved at `p'`.
  have hSR_bound : M.goodValue p SR ≤ M.budgetSum (M.buyerNeighborhood p SR) :=
    (satisfiesInvariant_iff fun g => (hp g).le).1 hinv SR
  have hSJ_nbr_sub : M.buyerNeighborhood p SJ ∩ H ⊆ M.buyerNeighborhood p' S := by
    intro i hi
    obtain ⟨hiNbr, hiH⟩ := Finset.mem_inter.1 hi
    obtain ⟨g, hgSJ, hE⟩ := mem_buyerNeighborhood.1 hiNbr
    have hgS : g ∈ S := (Finset.mem_inter.1 hgSJ).1
    have hgJ : g ∈ J := (Finset.mem_inter.1 hgSJ).2
    exact mem_buyerNeighborhood.2 ⟨g, hgS,
      (active_buyer_equalityEdge_scale hp hbuyer hx1 hx_le2 hiH).2 g hgJ |>.2 hE⟩
  have hSR_nbr_sub : M.buyerNeighborhood p SR ⊆ M.buyerNeighborhood p' S := by
    intro i hi
    obtain ⟨g, hgSR, hE⟩ := mem_buyerNeighborhood.1 hi
    have hgS : g ∈ S := (Finset.mem_sdiff.1 hgSR).1
    have hgJ : g ∉ J := (Finset.mem_sdiff.1 hgSR).2
    exact mem_buyerNeighborhood.2 ⟨g, hgS,
      (outside_buyer_equalityEdge_scale hp hbuyer hx1 hgJ hE).2.1 g hgJ |>.2 hE⟩
  have hdisj_nbr : Disjoint (M.buyerNeighborhood p SJ ∩ H) (M.buyerNeighborhood p SR) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hiH : i ∈ H := (Finset.mem_inter.1 hi1).2
    obtain ⟨g, hgSR, hE⟩ := mem_buyerNeighborhood.1 hi2
    exact (Finset.mem_sdiff.1 hgSR).2 (mem_activeGoods.2 ⟨i, hiH, hE⟩)
  have hbud_sum :
      M.budgetSum (M.buyerNeighborhood p SJ ∩ H) + M.budgetSum (M.buyerNeighborhood p SR) ≤
      M.budgetSum (M.buyerNeighborhood p' S) := by
    unfold budgetSum
    rw [← Finset.sum_union hdisj_nbr]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hSJ_nbr_sub hSR_nbr_sub)
      fun i _ _ => M.budget_nonneg i
  linarith

/-- Whenever every buyer in `H` has positive surplus (`0 < δ`), the Event-1 scale ratio on
`(M.activeGoods p H, H)` is strictly greater than `1`. -/
private theorem one_lt_active_minTightRatio {M : LinearFisherMarket I G} {p : G → ℝ}
    (hp : ∀ g, 0 < p g) (hsup_pos : ∀ g, 0 < M.supply g) (hinv : M.SatisfiesInvariant p)
    {f : G → I → ℝ} (hbal : M.IsBalancedFlow p f) {H : Finset I}
    (hclosed : IsResidualClosed M p f H) (hpos : ∀ i ∈ H, 0 < M.surplus f i)
    (hJ : (M.activeGoods p H).Nonempty) :
    1 < (M.activeMarket H).minTightRatio p (M.activeGoods p H) hJ := by
  classical
  set J := M.activeGoods p H
  set S := (M.activeMarket H).tightSetAtMinRatio p J hJ
  obtain ⟨hSJ, hSne, hStight, -⟩ :=
    tightSetAtMinRatio_spec (M := M.activeMarket H) (p := p) hJ
      (fun g _ => mul_pos (hp g) (hsup_pos g))
  rw [activeMarket_goodValue, activeMarket_buyerNeighborhood, activeMarket_budgetSum] at hStight
  have hgv_pos : 0 < M.goodValue p S := by
    obtain ⟨g₀, hg₀⟩ := hSne
    exact (mul_pos (hp g₀) (hsup_pos g₀)).trans_le
      (Finset.single_le_sum (fun g _ => mul_nonneg (hp g).le (M.supply_nonneg g)) hg₀)
  obtain ⟨g₀, hg₀⟩ := hSne
  obtain ⟨i₀, hi₀H, hE₀⟩ := mem_activeGoods.1 (hSJ hg₀)
  have hi₀_mem : i₀ ∈ M.buyerNeighborhood p S ∩ H :=
    Finset.mem_inter.2 ⟨mem_buyerNeighborhood.2 ⟨g₀, hg₀, hE₀⟩, hi₀H⟩
  have hfmax := hbal.isMaxEqualityFlow fun g => (hp g).le
  have hsat : M.goodValue p S = ∑ g ∈ S, ∑ i ∈ M.buyerNeighborhood p S ∩ H, f g i := by
    refine Finset.sum_congr rfl fun g hgS => ?_
    rw [← hfmax.sum_buyer_eq (fun g' => (hp g').le) hinv g]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hiNot => ?_
    refine le_antisymm (not_lt.1 fun hpos_f => hiNot ?_) (hbal.1.1 g i)
    have hE := hbal.1.2.1 g i hpos_f
    have hiH : i ∈ H := by
      by_contra hnot
      linarith [no_flow_from_activeGoods_outside hbal.1 hclosed (hSJ hgS) hnot]
    exact Finset.mem_inter.2 ⟨mem_buyerNeighborhood.2 ⟨g, hgS, hE⟩, hiH⟩
  have hsum_le : M.goodValue p S + ∑ i ∈ M.buyerNeighborhood p S ∩ H, M.surplus f i ≤
      M.budgetSum (M.buyerNeighborhood p S ∩ H) := by
    rw [hsat, Finset.sum_comm]
    unfold budgetSum surplus
    rw [Finset.sum_sub_distrib]
    have hle : ∑ i ∈ M.buyerNeighborhood p S ∩ H, ∑ g ∈ S, f g i ≤
        ∑ i ∈ M.buyerNeighborhood p S ∩ H, ∑ g : G, f g i :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_univ_sum_of_nonneg fun g => hbal.1.1 g i
    linarith
  have hsurp_pos : 0 < ∑ i ∈ M.buyerNeighborhood p S ∩ H, M.surplus f i :=
    (hpos i₀ hi₀H).trans_le (Finset.single_le_sum
      (fun i _ => sub_nonneg.2 (hbal.1.2.2.2 i)) hi₀_mem)
  have hlt_mul : 1 * M.goodValue p S <
      (M.activeMarket H).minTightRatio p J hJ * M.goodValue p S := by
    linarith
  exact lt_of_mul_lt_mul_right hlt_mul hgv_pos.le

/-- On an Event-2 step (`x2 < x1`), every active buyer in `H` retains strictly positive surplus in
the new balanced flow `f'`. -/
private theorem surplus_pos_of_event2 {M : LinearFisherMarket I G} {p : G → ℝ}
    (hp : ∀ g, 0 < p g) (hsup_pos : ∀ g, 0 < M.supply g) (hbud_pos : ∀ i, 0 < M.budget i)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g) (hinv : M.SatisfiesInvariant p)
    {H : Finset I} (hJ : (M.activeGoods p H).Nonempty)
    {x2 : ℝ} (hx2_eq : M.event2Ratio p H (M.activeGoods p H) = some x2)
    (hx2_lt : x2 < (M.activeMarket H).minTightRatio p (M.activeGoods p H) hJ)
    {f' : G → I → ℝ} (hinv' : M.SatisfiesInvariant (scaleActivePrices p (M.activeGoods p H) x2))
    (hbal' : M.IsBalancedFlow (scaleActivePrices p (M.activeGoods p H) x2) f')
    {k : I} (hkH : k ∈ H) :
    0 < M.surplus f' k := by
  classical
  set J := M.activeGoods p H
  set p' := scaleActivePrices p J x2
  have hx2_gt1 : 1 < x2 := one_lt_event2Ratio hp hx2_eq
  have hp'_pos : ∀ g, 0 < p' g := scaleActivePrices_pos hp J (by linarith)
  refine lt_of_le_of_ne (sub_nonneg.2 (hbal'.1.2.2.2 k)) fun hzero => ?_
  have hk_surp0 : M.surplus f' k = 0 := hzero.symm
  have hf'max := hbal'.isMaxEqualityFlow fun g => (hp'_pos g).le
  have hprop1 := (isBalancedFlow_iff_satisfiesPropertyOne hf'max).1 hbal'
  -- Build the zero-surplus tight set `S0 = {g | ∃ u, surplus f' u = 0 ∧ 0 < f' g u}`.
  let T0 : Finset I := Finset.univ.filter fun u => M.surplus f' u = 0
  let S0 : Finset G := Finset.univ.filter fun g => ∃ u ∈ T0, 0 < f' g u
  have hnbr_sub_T0 : M.buyerNeighborhood p' S0 ⊆ T0 := by
    intro j hj
    obtain ⟨g, hgS0, hEj⟩ := mem_buyerNeighborhood.1 hj
    obtain ⟨u, huT0, hpos⟩ := (Finset.mem_filter.1 hgS0).2
    have hu0 : M.surplus f' u = 0 := (Finset.mem_filter.1 huT0).2
    have hj_le : M.surplus f' j ≤ 0 := by
      by_contra hgt
      push Not at hgt
      exact hprop1 u j (by linarith) (Relation.ReflTransGen.single ⟨g, hpos, hEj⟩)
    exact Finset.mem_filter.2
      ⟨Finset.mem_univ _, le_antisymm hj_le (sub_nonneg.2 (hbal'.1.2.2.2 j))⟩
  have hS0_tight : M.IsTightSet p' S0 := by
    unfold IsTightSet
    have h1 : M.goodValue p' S0 = ∑ g ∈ S0, ∑ j ∈ M.buyerNeighborhood p' S0, f' g j := by
      refine Finset.sum_congr rfl fun g hgS0 => ?_
      rw [← hf'max.sum_buyer_eq (fun g' => (hp'_pos g').le) hinv' g]
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj =>
        le_antisymm (not_lt.1 fun hpos =>
          hj (mem_buyerNeighborhood.2 ⟨g, hgS0, hbal'.1.2.1 g j hpos⟩))
          (hbal'.1.1 g j)
    have h2 : ∑ j ∈ M.buyerNeighborhood p' S0, ∑ g ∈ S0, f' g j =
        M.budgetSum (M.buyerNeighborhood p' S0) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjT0 : j ∈ T0 := hnbr_sub_T0 hj
      have hj0 : M.surplus f' j = 0 := (Finset.mem_filter.1 hjT0).2
      have hsub : ∑ g ∈ S0, f' g j = ∑ g : G, f' g j :=
        Finset.sum_subset (Finset.subset_univ _) fun g _ hgNot =>
          le_antisymm (not_lt.1 fun hpos =>
            hgNot (Finset.mem_filter.2 ⟨Finset.mem_univ _, j, hjT0, hpos⟩))
            (hbal'.1.1 g j)
      rw [hsub]
      unfold surplus at hj0
      linarith
    rw [h1, Finset.sum_comm, h2]
  have hk_in_nbr : k ∈ M.buyerNeighborhood p' S0 := by
    have hk_spent : 0 < ∑ g : G, f' g k := by
      unfold surplus at hk_surp0; linarith [hbud_pos k]
    obtain ⟨g, -, hpos⟩ :=
      Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) (by simpa using hk_spent)
    have hkT0 : k ∈ T0 := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk_surp0⟩
    exact mem_buyerNeighborhood.2 ⟨g, Finset.mem_filter.2 ⟨Finset.mem_univ _, k, hkT0, hpos⟩,
      hbal'.1.2.1 g k hpos⟩
  -- `S0 ∩ J` must be nonempty; otherwise `k` strictly enlarges `Γ(S0)` while `p'(S0) = p(S0)`.
  set SJ := S0 ∩ J
  set SR := S0 \ J
  have hSR_nbr_sub : M.buyerNeighborhood p SR ⊆ M.buyerNeighborhood p' S0 := by
    intro j hj
    obtain ⟨g, hgSR, hE⟩ := mem_buyerNeighborhood.1 hj
    exact mem_buyerNeighborhood.2 ⟨g, (Finset.mem_sdiff.1 hgSR).1,
      (outside_buyer_equalityEdge_scale hp hbuyer hx2_gt1.le (Finset.mem_sdiff.1 hgSR).2 hE).2.1
        g (Finset.mem_sdiff.1 hgSR).2 |>.2 hE⟩
  have hSJ_ne : SJ.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hSR_eq : SR = S0 := by
      ext g
      simp only [SR, Finset.mem_sdiff, and_iff_left_iff_imp]
      intro hgS0 hgJ
      have : g ∈ SJ := Finset.mem_inter.2 ⟨hgS0, hgJ⟩
      rw [hempty] at this
      exact Finset.notMem_empty g this
    have hk_not_old : k ∉ M.buyerNeighborhood p SR := by
      intro hk_old
      obtain ⟨g, hgSR, hE⟩ := mem_buyerNeighborhood.1 hk_old
      exact (Finset.mem_sdiff.1 hgSR).2 (mem_activeGoods.2 ⟨k, hkH, hE⟩)
    have hgv_eq : M.goodValue p' S0 = M.goodValue p SR := by
      rw [hSR_eq]
      refine Finset.sum_congr rfl fun g hg => ?_
      have hgJ : g ∉ J := by
        rw [← hSR_eq] at hg; exact (Finset.mem_sdiff.1 hg).2
      simp only [p', scaleActivePrices, hgJ, ↓reduceIte]
    have hsub_erase : M.buyerNeighborhood p SR ⊆ (M.buyerNeighborhood p' S0).erase k :=
      Finset.subset_erase.2 ⟨hSR_nbr_sub, hk_not_old⟩
    have hbud_lt :
        M.budgetSum (M.buyerNeighborhood p SR) < M.budgetSum (M.buyerNeighborhood p' S0) := by
      have hle : M.budgetSum (M.buyerNeighborhood p SR) ≤
          M.budgetSum ((M.buyerNeighborhood p' S0).erase k) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_erase fun i _ _ => M.budget_nonneg i
      have hadd := Finset.add_sum_erase _ M.budget hk_in_nbr
      change M.budget k + M.budgetSum ((M.buyerNeighborhood p' S0).erase k) =
        M.budgetSum (M.buyerNeighborhood p' S0) at hadd
      linarith [hbud_pos k]
    have hinv_SR := (satisfiesInvariant_iff fun g => (hp g).le).1 hinv SR
    unfold IsTightSet at hS0_tight
    linarith
  -- Split `S0 = SJ ⊔ SR`: `x2 * p(SJ) ≥ m(Γ_p(SJ) ∩ H)`, contradicting `x2 < x1`!
  have hSJ_nbr_sub : M.buyerNeighborhood p SJ ∩ H ⊆ M.buyerNeighborhood p' S0 := by
    intro j hj
    obtain ⟨hjNbr, hjH⟩ := Finset.mem_inter.1 hj
    obtain ⟨g, hgSJ, hE⟩ := mem_buyerNeighborhood.1 hjNbr
    exact mem_buyerNeighborhood.2 ⟨g, (Finset.mem_inter.1 hgSJ).1,
      (active_buyer_equalityEdge_scale hp hbuyer hx2_gt1.le
        (fun r hr => by rw [hx2_eq] at hr; injection hr with hr; exact hr.le) hjH).2 g
        (Finset.mem_inter.1 hgSJ).2 |>.2 hE⟩
  have hdisj : Disjoint (M.buyerNeighborhood p SJ ∩ H) (M.buyerNeighborhood p SR) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    obtain ⟨g, hgSR, hE⟩ := mem_buyerNeighborhood.1 hj2
    exact (Finset.mem_sdiff.1 hgSR).2 (mem_activeGoods.2 ⟨j, (Finset.mem_inter.1 hj1).2, hE⟩)
  have hbud_ge :
      M.budgetSum (M.buyerNeighborhood p SJ ∩ H) + M.budgetSum (M.buyerNeighborhood p SR) ≤
      M.budgetSum (M.buyerNeighborhood p' S0) := by
    unfold budgetSum
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hSJ_nbr_sub hSR_nbr_sub)
      fun i _ _ => M.budget_nonneg i
  have hval_split : M.goodValue p' S0 = x2 * M.goodValue p SJ + M.goodValue p SR := by
    have hu : SJ ∪ SR = S0 := by ext g; by_cases hg : g ∈ J <;> simp [SJ, SR]
    have hd : Disjoint SJ SR := Finset.disjoint_sdiff.mono_left Finset.inter_subset_right
    rw [← hu, goodValue, Finset.sum_union hd]
    have h1 : ∑ g ∈ SJ, p' g * M.supply g = x2 * M.goodValue p SJ := by
      rw [goodValue, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      simp only [p', scaleActivePrices, (Finset.mem_inter.1 hg).2, ↓reduceIte]
      ring
    have h2 : ∑ g ∈ SR, p' g * M.supply g = M.goodValue p SR := by
      refine Finset.sum_congr rfl fun g hg => ?_
      simp only [p', scaleActivePrices, (Finset.mem_sdiff.1 hg).2, ↓reduceIte]
    rw [h1, h2]
  have hinv_SR := (satisfiesInvariant_iff fun g => (hp g).le).1 hinv SR
  have hle_SJ : M.budgetSum (M.buyerNeighborhood p SJ ∩ H) ≤ x2 * M.goodValue p SJ := by
    unfold IsTightSet at hS0_tight
    linarith
  have hgv_pos : 0 < M.goodValue p SJ := by
    obtain ⟨g₀, hg₀⟩ := hSJ_ne
    exact (mul_pos (hp g₀) (hsup_pos g₀)).trans_le
      (Finset.single_le_sum (fun g _ => mul_nonneg (hp g).le (M.supply_nonneg g)) hg₀)
  have hmin_le := minTightRatio_mul_goodValue_le (M := M.activeMarket H) (p := p) hJ
    (fun g _ => mul_pos (hp g) (hsup_pos g)) (Finset.inter_subset_right (s₁ := S0) (s₂ := J))
  rw [activeMarket_goodValue, activeMarket_buyerNeighborhood, activeMarket_budgetSum] at hmin_le
  have hlt_mul := mul_lt_mul_of_pos_right hx2_lt hgv_pos
  linarith

omit [DecidableEq I] in
/-- On an Event-1 step (`x1 ≤ x2` or `event2Ratio = none`), the squared `ℓ₂` surplus norm drops by
at least `δ ^ 2` where `δ = min_{i ∈ H} M.surplus f i`, even when zero-spending buyers outside `H`
still have equality edges to `J`. -/
private theorem surplusSqNorm_drop_of_event1 {M : LinearFisherMarket I G} {p : G → ℝ}
    (hp : ∀ g, 0 < p g) (hsup_pos : ∀ g, 0 < M.supply g)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g)
    {f f' : G → I → ℝ} (hbal : M.IsBalancedFlow p f)
    {H : Finset I} (hH : H.Nonempty) (hclosed : IsResidualClosed M p f H)
    (hJ : (M.activeGoods p H).Nonempty)
    (hx1_gt1 : 1 < (M.activeMarket H).minTightRatio p (M.activeGoods p H) hJ)
    (hx1_le2 : ∀ r, M.event2Ratio p H (M.activeGoods p H) = some r →
      (M.activeMarket H).minTightRatio p (M.activeGoods p H) hJ ≤ r)
    (hbal' : M.IsBalancedFlow
      (scaleActivePrices p (M.activeGoods p H)
        ((M.activeMarket H).minTightRatio p (M.activeGoods p H) hJ)) f') :
    M.surplusSqNorm f' ≤ M.surplusSqNorm f - (H.inf' hH (M.surplus f)) ^ 2 := by
  classical
  set J := M.activeGoods p H
  set x1 := (M.activeMarket H).minTightRatio p J hJ
  set S1 := (M.activeMarket H).tightSetAtMinRatio p J hJ
  set p' := scaleActivePrices p J x1
  obtain ⟨hS1_sub, hS1_ne, hS1_tight, -⟩ :=
    tightSetAtMinRatio_spec (M := M.activeMarket H) (p := p) hJ
      (fun g _ => mul_pos (hp g) (hsup_pos g))
  rw [activeMarket_goodValue, activeMarket_buyerNeighborhood, activeMarket_budgetSum] at hS1_tight
  set T1 : Finset I := M.buyerNeighborhood p S1 ∩ H
  have hT1_ne : T1.Nonempty := by
    obtain ⟨g₀, hg₀⟩ := hS1_ne
    obtain ⟨i₀, hi₀H, hE₀⟩ := mem_activeGoods.1 (hS1_sub hg₀)
    exact ⟨i₀, Finset.mem_inter.2 ⟨mem_buyerNeighborhood.2 ⟨g₀, hg₀, hE₀⟩, hi₀H⟩⟩
  -- Build a saturating flow `fS` on the subtype market `(T1, S1)` using `exists_isBalancedFlow`
  -- and `IsMaxEqualityFlow.sum_buyer_eq`!
  let Msub : LinearFisherMarket {i : I // i ∈ T1} {g : G // g ∈ S1} := {
    budget := fun i => M.budget i.1
    supply := fun g => M.supply g.1
    utility := fun i g => if M.IsEqualityEdge p i.1 g.1 then p' g.1 else 0
    budget_nonneg := fun i => M.budget_nonneg i.1
    supply_nonneg := fun g => M.supply_nonneg g.1
    utility_nonneg := fun i g => by
      split_ifs
      · simp only [p', scaleActivePrices, hS1_sub g.2, ↓reduceIte]
        exact mul_nonneg (by linarith) (hp g.1).le
      · exact le_rfl
  }
  let psub : {g : G // g ∈ S1} → ℝ := fun g => p' g.1
  have hpsub_pos : ∀ g : {g : G // g ∈ S1}, 0 < psub g := fun g => by
    simp only [psub, p', scaleActivePrices, hS1_sub g.2, ↓reduceIte]
    exact mul_pos (by linarith) (hp g.1)
  have hMsub_edge : ∀ (i : {i : I // i ∈ T1}) (g : {g : G // g ∈ S1}),
      Msub.IsEqualityEdge psub i g ↔ M.IsEqualityEdge p i.1 g.1 := by
    intro i g
    have hex : ∃ g₀ : {g : G // g ∈ S1}, M.IsEqualityEdge p i.1 g₀.1 := by
      obtain ⟨g₀, hg₀S1, hE₀⟩ := mem_buyerNeighborhood.1 (Finset.mem_inter.1 i.2).1
      exact ⟨⟨g₀, hg₀S1⟩, hE₀⟩
    have hbb (g' : {g : G // g ∈ S1}) :
        Msub.bangPerBuck psub i g' = if M.IsEqualityEdge p i.1 g'.1 then 1 else 0 := by
      simp only [bangPerBuck_eq, Msub, psub]
      split_ifs
      · exact div_self (hpsub_pos g').ne'
      · exact zero_div _
    constructor
    · intro h
      obtain ⟨g₀, hg₀⟩ := hex
      have hle := h g₀
      rw [hbb g₀, hbb g, ite_eq_left_iff.2 fun hn => absurd hg₀ hn] at hle
      by_contra hnot
      rw [ite_eq_right_iff.2 fun hp' => absurd hp' hnot] at hle
      linarith
    · intro h g'
      rw [hbb g', hbb g, ite_eq_left_iff.2 fun hn => absurd h hn]
      split_ifs <;> linarith
  have hMsub_inv : Msub.SatisfiesInvariant psub := by
    rw [satisfiesInvariant_iff fun g => (hpsub_pos g).le]
    intro A
    let A' : Finset G := A.map ⟨Subtype.val, Subtype.val_injective⟩
    have hA'_sub : A' ⊆ S1 := by
      intro g hg
      obtain ⟨g', -, rfl⟩ := Finset.mem_map.1 hg
      exact g'.2
    have hgv : Msub.goodValue psub A = x1 * M.goodValue p A' := by
      rw [goodValue, goodValue, Finset.mul_sum, Finset.sum_map]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Function.Embedding.coeFn_mk, Msub, psub, p', scaleActivePrices, hS1_sub g.2,
        ↓reduceIte]
      ring
    have hnbr_eq : (Msub.buyerNeighborhood psub A).map ⟨Subtype.val, Subtype.val_injective⟩ =
        M.buyerNeighborhood p A' ∩ H := by
      ext i
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_inter,
        mem_buyerNeighborhood, A']
      constructor
      · rintro ⟨⟨i', hi'T1⟩, ⟨g', hg'A, hE⟩, rfl⟩
        exact ⟨⟨g'.1, ⟨g', hg'A, rfl⟩, (hMsub_edge ⟨i', hi'T1⟩ g').1 hE⟩,
          (Finset.mem_inter.1 hi'T1).2⟩
      · rintro ⟨⟨g, ⟨g', hg'A, rfl⟩, hE⟩, hiH⟩
        have hiT1 : i ∈ T1 := Finset.mem_inter.2 ⟨mem_buyerNeighborhood.2 ⟨g'.1, g'.2, hE⟩, hiH⟩
        exact ⟨⟨i, hiT1⟩, ⟨g', hg'A, (hMsub_edge ⟨i, hiT1⟩ g').2 hE⟩, rfl⟩
    have hbud : Msub.budgetSum (Msub.buyerNeighborhood psub A) =
        M.budgetSum (M.buyerNeighborhood p A' ∩ H) := by
      rw [← hnbr_eq, budgetSum, budgetSum, Finset.sum_map]
      rfl
    rw [hgv, hbud]
    have hle := minTightRatio_mul_goodValue_le (M := M.activeMarket H) (p := p) hJ
      (fun g _ => mul_pos (hp g) (hsup_pos g)) (hA'_sub.trans hS1_sub)
    rwa [activeMarket_goodValue, activeMarket_buyerNeighborhood, activeMarket_budgetSum] at hle
  obtain ⟨fsub, hfsub_bal⟩ :=
    exists_isBalancedFlow (M := Msub) (p := psub) fun g => (hpsub_pos g).le
  have hfsub_max := hfsub_bal.isMaxEqualityFlow fun g => (hpsub_pos g).le
  have hfsub_satG : ∀ g : {g : G // g ∈ S1}, ∑ i : {i : I // i ∈ T1}, fsub g i =
      p' g.1 * M.supply g.1 := fun g =>
    hfsub_max.sum_buyer_eq (fun g' => (hpsub_pos g').le) hMsub_inv g
  have hfsub_satB : ∀ i : {i : I // i ∈ T1}, ∑ g : {g : G // g ∈ S1}, fsub g i = M.budget i.1 := by
    have hsum_eq :
        ∑ i : {i : I // i ∈ T1}, (M.budget i.1 - ∑ g : {g : G // g ∈ S1}, fsub g i) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_comm]
      have h1 : ∑ g : {g : G // g ∈ S1}, ∑ i : {i : I // i ∈ T1}, fsub g i =
          x1 * M.goodValue p S1 := by
        simp_rw [hfsub_satG]
        rw [goodValue, Finset.mul_sum, ← Finset.sum_attach S1]
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [p', scaleActivePrices, hS1_sub g.2, ↓reduceIte]; ring
      have h2 : ∑ i : {i : I // i ∈ T1}, M.budget i.1 = M.budgetSum T1 := by
        rw [budgetSum, ← Finset.sum_attach T1]; rfl
      rw [h1, h2, hS1_tight, sub_self]
    intro i
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      sub_nonneg.2 (hfsub_bal.1.2.2.2 j)).1 hsum_eq i (Finset.mem_univ i)
    linarith
  -- Patch `f` with `fsub` on `S1 × T1`, zeroing `S1 × (univ \ T1)` and `(univ \ S1) × T1`.
  let ftilde : G → I → ℝ := fun g i =>
    if hg : g ∈ S1 then
      if hi : i ∈ T1 then fsub ⟨g, hg⟩ ⟨i, hi⟩ else 0
    else if i ∈ T1 then 0 else f g i
  have hf_feas' : M.IsEqualityFlow p' f :=
    isEqualityFlow_scaleActivePrices hp hbuyer hbal.1 hclosed hx1_gt1.le hx1_le2
  have hsum_in (i : I) (hi : i ∈ T1) :
      ∑ g : G, ftilde g i = ∑ g : {g : G // g ∈ S1}, fsub g ⟨i, hi⟩ := by
    rw [← Finset.sum_subset (Finset.subset_univ S1) fun g _ hg => by simp [ftilde, hg, hi],
      ← Finset.sum_attach S1]
    exact Finset.sum_congr rfl fun g _ => by simp [ftilde, g.2, hi]
  have hftilde_feas : M.IsEqualityFlow p' ftilde := by
    refine ⟨fun g i => ?_, fun g i hpos => ?_, fun g => ?_, fun i => ?_⟩
    · dsimp only [ftilde]
      split_ifs
      · exact hfsub_bal.1.1 _ _
      · exact le_rfl
      · exact le_rfl
      · exact hbal.1.1 g i
    · dsimp only [ftilde] at hpos
      split_ifs at hpos with hg hi
      · have hE := (hMsub_edge ⟨i, hi⟩ ⟨g, hg⟩).1 (hfsub_bal.1.2.1 ⟨g, hg⟩ ⟨i, hi⟩ hpos)
        exact (active_buyer_equalityEdge_scale hp hbuyer hx1_gt1.le hx1_le2
          (Finset.mem_inter.1 hi).2).2 g (hS1_sub hg) |>.2 hE
      · exact (lt_irrefl (0 : ℝ) hpos).elim
      · exact (lt_irrefl (0 : ℝ) hpos).elim
      · exact hf_feas'.2.1 g i hpos
    · by_cases hg : g ∈ S1
      · have hsum : ∑ i : I, ftilde g i = ∑ i : {i : I // i ∈ T1}, fsub ⟨g, hg⟩ i := by
          rw [← Finset.sum_subset (Finset.subset_univ T1) fun i _ hi => by simp [ftilde, hg, hi],
            ← Finset.sum_attach T1]
          exact Finset.sum_congr rfl fun i _ => by simp [ftilde, hg, i.2]
        rw [hsum, hfsub_satG ⟨g, hg⟩]
      · exact (Finset.sum_le_sum fun i _ => by
          dsimp only [ftilde]; split_ifs
          · exact hbal.1.1 g i
          · exact le_rfl).trans (hf_feas'.2.2.1 g)
    · by_cases hi : i ∈ T1
      · rw [hsum_in i hi, hfsub_satB ⟨i, hi⟩]
      · exact (Finset.sum_le_sum fun g _ => by
          dsimp only [ftilde]; split_ifs
          · exact hbal.1.1 g i
          · exact le_rfl).trans (hbal.1.2.2.2 i)
  -- Compute `M.surplus ftilde i`: `0` for `i ∈ T1`, unchanged `M.surplus f i` for `i ∉ T1`!
  have hsurp_in (i : I) (hi : i ∈ T1) : M.surplus ftilde i = 0 := by
    simp only [surplus, hsum_in i hi, hfsub_satB ⟨i, hi⟩, sub_self]
  have hsurp_out (i : I) (hi : i ∉ T1) : M.surplus ftilde i = M.surplus f i := by
    unfold surplus
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : g ∈ S1
    · simp only [ftilde, hg, hi, ↓reduceDIte]
      symm
      refine le_antisymm (not_lt.1 fun hpos => hi ?_) (hbal.1.1 g i)
      have hE := hbal.1.2.1 g i hpos
      have hiH : i ∈ H := by
        by_contra hnot
        linarith [no_flow_from_activeGoods_outside hbal.1 hclosed (hS1_sub hg) hnot]
      exact Finset.mem_inter.2 ⟨mem_buyerNeighborhood.2 ⟨g, hg, hE⟩, hiH⟩
    · simp [ftilde, hg, hi]
  have hdiff : M.surplusSqNorm f - M.surplusSqNorm ftilde = ∑ i ∈ T1, (M.surplus f i) ^ 2 := by
    rw [surplusSqNorm, surplusSqNorm, ← Finset.sum_sub_distrib,
      ← Finset.sum_subset (Finset.subset_univ T1) fun i _ hi => by rw [hsurp_out i hi, sub_self]]
    refine Finset.sum_congr rfl fun i hi => by rw [hsurp_in i hi]; ring
  obtain ⟨i₀, hi₀T1⟩ := hT1_ne
  have hi₀H : i₀ ∈ H := (Finset.mem_inter.1 hi₀T1).2
  have hinf_le : H.inf' hH (M.surplus f) ≤ M.surplus f i₀ := Finset.inf'_le (M.surplus f) hi₀H
  have hinf_nn : 0 ≤ H.inf' hH (M.surplus f) := by
    rw [Finset.le_inf'_iff]; intro i _; exact sub_nonneg.2 (hbal.1.2.2.2 i)
  have hsq_le : (H.inf' hH (M.surplus f)) ^ 2 ≤ ∑ i ∈ T1, (M.surplus f i) ^ 2 :=
    (show (H.inf' hH (M.surplus f)) ^ 2 ≤ (M.surplus f i₀) ^ 2 by nlinarith).trans
      (Finset.single_le_sum (fun i _ => sq_nonneg _) hi₀T1)
  linarith [hbal'.2 ftilde hftilde_feas]

/-- Inductive specification of `dpsvPhaseLoop`: establishes **Lemma 5.14** (at most
`Fintype.card G` iterations and `2 * n * iters` max-flow queries), invariant preservation,
strict price increase on `tightSet`, genuine tightness when total surplus `< min_i M.budget i`,
and the quadratic potential drop `δ ^ 2 / iters` (**Lemma 5.21**). -/
private theorem dpsvPhaseLoop_spec {M : LinearFisherMarket I G}
    (hsup_pos : ∀ g, 0 < M.supply g) (hbud_pos : ∀ i, 0 < M.budget i)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g)
    {oracle : {ι : Type u} → MaxFlowQuery I G ι → ι}
    (horacle : IsValidMaxFlowOracle oracle) :
    ∀ (k : ℕ) (p : G → ℝ) (f : G → I → ℝ) (H : Finset I) (hH : H.Nonempty),
      (∀ g, 0 < p g) →
      M.SatisfiesInvariant p →
      M.IsBalancedFlow p f →
      IsResidualClosed M p f H →
      (∀ i ∈ H, 0 < M.surplus f i) →
      Fintype.card G - (M.activeGoods p H).card + 1 ≤ k →
      let prog := dpsvPhaseLoop M k p f H
      let res := prog.eval oracle
      (∀ g, 0 < res.price g) ∧
      (∀ g, p g ≤ res.price g) ∧
      M.SatisfiesInvariant res.price ∧
      M.IsBalancedFlow res.price res.flow ∧
      1 ≤ res.iters ∧
      res.iters ≤ Fintype.card G - (M.activeGoods p H).card + 1 ∧
      prog.countQueries oracle ≤ 2 * Fintype.card G * res.iters ∧
      M.surplusSqNorm res.flow ≤
        M.surplusSqNorm f - (H.inf' hH (M.surplus f)) ^ 2 / (res.iters : ℝ) ∧
      res.tightSet.Nonempty ∧
      (∀ g ∈ res.tightSet, p g < res.price g) ∧
      ((∀ i, ∑ j : I, M.surplus f j < M.budget i) → M.IsTightSet res.price res.tightSet) := by
  classical
  intro k
  induction k with
  | zero =>
    intro p f H _ _ _ _ _ _ hk
    omega
  | succ k ih =>
    intro p f H hH hp hinv hbal hclosed hpos hk
    set J := M.activeGoods p H
    have hJ : J.Nonempty := by
      obtain ⟨i₀, hi₀⟩ := hH
      obtain ⟨g₀, -⟩ := hbuyer i₀
      have : Nonempty G := ⟨g₀⟩
      obtain ⟨g, hE⟩ := exists_isEqualityEdge M p i₀
      exact ⟨g, mem_activeGoods.2 ⟨i₀, hi₀, hE⟩⟩
    obtain ⟨hft_eval, hft_q⟩ := findTightSetProgram_spec (M := M.activeMarket H) (p := p) hJ
      (fun g _ => mul_pos (hp g) (hsup_pos g)) horacle
    set x1 := (M.activeMarket H).minTightRatio p J hJ
    set S1 := (M.activeMarket H).tightSetAtMinRatio p J hJ
    have hx1_gt1 : 1 < x1 := one_lt_active_minTightRatio hp hsup_pos hinv hbal hclosed hpos hJ
    have hft_q_le : ((M.activeMarket H).findTightSetProgram p J).countQueries oracle ≤
        Fintype.card G := hft_q.trans (Finset.card_le_univ J)
    -- Helper for the Event-1 branch (used both when `event2Ratio = none` and when `¬ x2 < x1`).
    have hEvent1 :
        (∀ r, M.event2Ratio p H J = some r → x1 ≤ r) →
        let p' := scaleActivePrices p J x1
        let f' := (M.balancedFlowProgram p').eval oracle
        (∀ g, 0 < p' g) ∧
        (∀ g, p g ≤ p' g) ∧
        M.SatisfiesInvariant p' ∧
        M.IsBalancedFlow p' f' ∧
        1 ≤ (1 : ℕ) ∧
        1 ≤ Fintype.card G - J.card + 1 ∧
        ((M.activeMarket H).findTightSetProgram p J).countQueries oracle +
            (M.balancedFlowProgram p').countQueries oracle ≤ 2 * Fintype.card G * 1 ∧
        M.surplusSqNorm f' ≤
          M.surplusSqNorm f - (H.inf' hH (M.surplus f)) ^ 2 / ((1 : ℕ) : ℝ) ∧
        S1.Nonempty ∧
        (∀ g ∈ S1, p g < p' g) ∧
        ((∀ i, ∑ j : I, M.surplus f j < M.budget i) → M.IsTightSet p' S1) := by
      intro hx1_le2 p' f'
      have hp'_pos : ∀ g, 0 < p' g := fun g => by
        dsimp only [p', scaleActivePrices]; split_ifs
        · exact mul_pos (by linarith) (hp g)
        · exact hp g
      have hp_le : ∀ g, p g ≤ p' g := fun g => by
        dsimp only [p', scaleActivePrices]; split_ifs
        · nlinarith [hp g]
        · exact le_rfl
      have hinv' : M.SatisfiesInvariant p' :=
        satisfiesInvariant_scaleActivePrices hp hsup_pos hbuyer hinv hH hx1_gt1.le
          le_rfl hx1_le2
      obtain ⟨-, hbal', hbf_q⟩ :=
        balancedFlowProgram_spec (fun g => (hp'_pos g).le) hinv' horacle
      obtain ⟨hS1_sub, hS1_ne, hS1_tight, -⟩ :=
        tightSetAtMinRatio_spec (M := M.activeMarket H) (p := p) hJ
          (fun g _ => mul_pos (hp g) (hsup_pos g))
      rw [activeMarket_goodValue, activeMarket_buyerNeighborhood,
        activeMarket_budgetSum] at hS1_tight
      have hdrop := surplusSqNorm_drop_of_event1 hp hsup_pos hbuyer hbal hH hclosed hJ
        hx1_gt1 hx1_le2 hbal'
      have hstrict : ∀ g ∈ S1, p g < p' g := fun g hg => by
        simp only [p', scaleActivePrices, hS1_sub hg, ↓reduceIte]
        nlinarith [hp g]
      have htight_low : (∀ i, ∑ j : I, M.surplus f j < M.budget i) → M.IsTightSet p' S1 := by
        intro hlow
        -- Under `∑ j, surplus f j < budget i` for all `i`, every `i ∉ H` spends positively in `f`,
        -- hence must have an equality edge outside `J` (since `f` sends `0` from `J` outside `H`).
        -- Therefore every `i ∉ H` drops all edges to `J` at `x1 > 1`!
        have hnbr_eq : M.buyerNeighborhood p' S1 = M.buyerNeighborhood p S1 ∩ H := by
          ext i
          simp only [Finset.mem_inter, mem_buyerNeighborhood]
          constructor
          · rintro ⟨g, hgS1, hE'⟩
            have hgJ : g ∈ J := hS1_sub hgS1
            have hiH : i ∈ H := by
              by_contra hiNotH
              have hsurp_lt : M.surplus f i < M.budget i :=
                (Finset.single_le_sum (fun j _ => sub_nonneg.2 (hbal.1.2.2.2 j))
                  (Finset.mem_univ i)).trans_lt (hlow i)
              have hspent_pos : 0 < ∑ g' : G, f g' i := by unfold surplus at hsurp_lt; linarith
              obtain ⟨g_out, -, hfg_pos⟩ :=
                Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) (by simpa using hspent_pos)
              have hg_out_notJ : g_out ∉ J := fun hg_outJ =>
                hfg_pos.ne' (no_flow_from_activeGoods_outside hbal.1 hclosed hg_outJ hiNotH)
              exact (outside_buyer_equalityEdge_scale hp hbuyer hx1_gt1.le hg_out_notJ
                (hbal.1.2.1 g_out i hfg_pos)).2.2 hx1_gt1 g hgJ hE'
            exact ⟨⟨g, hgS1,
              (active_buyer_equalityEdge_scale hp hbuyer hx1_gt1.le hx1_le2 hiH).2 g hgJ |>.1 hE'⟩,
              hiH⟩
          · rintro ⟨⟨g, hgS1, hE⟩, hiH⟩
            exact ⟨g, hgS1,
              (active_buyer_equalityEdge_scale hp hbuyer hx1_gt1.le hx1_le2 hiH).2 g
                (hS1_sub hgS1) |>.2 hE⟩
        have hgv_eq : M.goodValue p' S1 = x1 * M.goodValue p S1 := by
          rw [goodValue, goodValue, Finset.mul_sum]
          refine Finset.sum_congr rfl fun g hg => ?_
          simp only [p', scaleActivePrices, hS1_sub hg, ↓reduceIte]; ring
        rw [IsTightSet, hgv_eq, hnbr_eq, hS1_tight]
      refine ⟨hp'_pos, hp_le, hinv', hbal', le_rfl, by omega, by omega, by simpa using hdrop,
        hS1_ne, hstrict, htight_low⟩
    -- Now case split on `M.event2Ratio p H J` and `x2 < x1`!
    cases hratio : M.event2Ratio p H J with
    | none =>
      have hE1 := hEvent1 (fun r hr => by rw [hratio] at hr; cases hr)
      have heval : (dpsvPhaseLoop M (k + 1) p f H).eval oracle =
          ⟨scaleActivePrices p J x1,
            (M.balancedFlowProgram (scaleActivePrices p J x1)).eval oracle, S1, 1⟩ := by
        rw [dpsvPhaseLoop, FreeM.eval_bind, hft_eval]
        simp [J, hratio]
      have hcount : (dpsvPhaseLoop M (k + 1) p f H).countQueries oracle =
          ((M.activeMarket H).findTightSetProgram p J).countQueries oracle +
            (M.balancedFlowProgram (scaleActivePrices p J x1)).countQueries oracle := by
        rw [dpsvPhaseLoop, FreeM.countQueries_bind, hft_eval]
        simp [J, hratio]
      simpa only [heval, hcount] using hE1
    | some x2 =>
      by_cases hlt : x2 < x1
      · -- Event 2: scale by `x2 < x1`, recompute balanced flow `f'`, expand `H` to `H'`, recurse!
        set p' := scaleActivePrices p J x2
        have hx2_gt1 : 1 < x2 := one_lt_event2Ratio hp hratio
        have hx2_le2 : ∀ r, M.event2Ratio p H J = some r → x2 ≤ r := fun r hr => by
          rw [hratio] at hr; injection hr with hr; exact hr.le
        have hp'_pos : ∀ g, 0 < p' g := scaleActivePrices_pos hp J (by linarith)
        have hp_le : ∀ g, p g ≤ p' g := fun g => by
          dsimp only [p', scaleActivePrices]; split_ifs
          · nlinarith [hp g]
          · exact le_rfl
        have hinv' : M.SatisfiesInvariant p' :=
          satisfiesInvariant_scaleActivePrices hp hsup_pos hbuyer hinv hH hx2_gt1.le
            hlt.le hx2_le2
        obtain ⟨hf'max, hbal', hbf_q⟩ :=
          balancedFlowProgram_spec (fun g => (hp'_pos g).le) hinv' horacle
        set f' := (M.balancedFlowProgram p').eval oracle
        let H' : Finset I := Finset.univ.filter fun u => ∃ v ∈ H, M.ResidualReachable p' f' u v
        have hH_sub_H' : H ⊆ H' := fun v hv =>
          Finset.mem_filter.2 ⟨Finset.mem_univ v, v, hv, .refl⟩
        have hH' : H'.Nonempty := hH.mono hH_sub_H'
        have hclosed' : IsResidualClosed M p' f' H' := by
          intro u v huv hvH'
          obtain ⟨w, hwH, hvw⟩ := (Finset.mem_filter.1 hvH').2
          exact Finset.mem_filter.2 ⟨Finset.mem_univ u, w, hwH, huv.trans hvw⟩
        have hprop1' := (isBalancedFlow_iff_satisfiesPropertyOne hf'max).1 hbal'
        have hpos' : ∀ u ∈ H', 0 < M.surplus f' u := by
          intro u hu
          obtain ⟨v, hvH, huv⟩ := (Finset.mem_filter.1 hu).2
          have hv_pos : 0 < M.surplus f' v :=
            surplus_pos_of_event2 hp hsup_pos hbud_pos hbuyer hinv hJ hratio hlt hinv' hbal' hvH
          by_contra hle
          push Not at hle
          exact hprop1' u v (lt_of_le_of_lt hle hv_pos) huv
        -- Show `J ⊂ J' = M.activeGoods p' H'` strictly!
        set J' := M.activeGoods p' H'
        have hJ_sub_J' : J ⊆ J' := by
          intro g hgJ
          obtain ⟨i, hiH, hE⟩ := mem_activeGoods.1 hgJ
          exact mem_activeGoods.2 ⟨i, hH_sub_H' hiH,
            (active_buyer_equalityEdge_scale hp hbuyer hx2_gt1.le hx2_le2 hiH).2 g hgJ |>.2 hE⟩
        have hJ_ssub : J ⊂ J' := by
          refine Finset.ssubset_iff_of_subset hJ_sub_J' |>.2 ?_
          unfold event2Ratio at hratio
          split_ifs at hratio with hne
          · injection hratio with hx2_eq
            obtain ⟨ig, hig_mem, hig_eq⟩ := Finset.exists_mem_eq_inf' hne
              (fun ig : I × G => maxBangPerBuck M p ig.1 * p ig.2 / M.utility ig.1 ig.2)
            obtain ⟨hprod, hu_pos⟩ := Finset.mem_filter.1 hig_mem
            obtain ⟨hiH, hgNotJ⟩ := Finset.mem_product.1 hprod
            have hgNot : ig.2 ∉ J := (Finset.mem_sdiff.1 hgNotJ).2
            refine ⟨ig.2, mem_activeGoods.2 ⟨ig.1, hH_sub_H' hiH, ?_⟩, hgNot⟩
            rw [isEqualityEdge_iff_eq_maxBangPerBuck,
              (active_buyer_equalityEdge_scale hp hbuyer hx2_gt1.le hx2_le2 hiH).1]
            simp only [bangPerBuck_eq, p', scaleActivePrices, hgNot, ↓reduceIte]
            have hx2_val : x2 = maxBangPerBuck M p ig.1 * p ig.2 / M.utility ig.1 ig.2 :=
              hx2_eq.symm.trans hig_eq
            rw [hx2_val]
            have hα_pos := maxBangPerBuck_pos hp (hbuyer ig.1)
            field_simp [hu_pos.ne', (hp ig.2).ne', hα_pos.ne']
        have hcard_lt : J.card < J'.card := Finset.card_lt_card hJ_ssub
        have hJ'_le_n : J'.card ≤ Fintype.card G := Finset.card_le_univ J'
        have hk' : Fintype.card G - J'.card + 1 ≤ k := by omega
        obtain ⟨hih_pos, hih_le, hih_inv, hih_bal, hih_it1, hih_it_le, hih_q, hih_drop,
            hih_Sne, hih_Sstrict, hih_Stight⟩ :=
          ih p' f' H' hH' hp'_pos hinv' hbal' hclosed' hpos' hk'
        -- Combine step drop (Lemma 5.20 / Corollary 5.18) with IH drop `δ'² / r`!
        set δ := H.inf' hH (M.surplus f)
        set δ' := H'.inf' hH' (M.surplus f')
        set r := (dpsvPhaseLoop M k p' f' H').eval oracle |>.iters
        have hδ_pos : 0 < δ := by rw [Finset.lt_inf'_iff]; exact hpos
        have hδ'_pos : 0 < δ' := by rw [Finset.lt_inf'_iff]; exact hpos'
        have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.2 (by omega)
        have hstep_le : M.surplusSqNorm f' ≤ M.surplusSqNorm f :=
          surplusSqNorm_scaleActivePrices_le hp hbuyer hbal.1 hclosed hx2_gt1.le hx2_le2 hbal'
        have htotal_drop : M.surplusSqNorm ((dpsvPhaseLoop M k p' f' H').eval oracle).flow ≤
            M.surplusSqNorm f - δ ^ 2 / ((r + 1 : ℕ) : ℝ) := by
          push_cast
          by_cases hδlt : δ' < δ
          · have h520 := surplusSqNorm_drop_of_minSurplus_lt hp hbuyer hbal.1 hH hclosed
              hx2_gt1.le hx2_le2 hbal' hδlt
            have halg : δ ^ 2 / ((r : ℝ) + 1) ≤ (δ - δ') ^ 2 + δ' ^ 2 / (r : ℝ) := by
              rw [← sub_nonneg]
              have hident : (δ - δ') ^ 2 + δ' ^ 2 / (r : ℝ) - δ ^ 2 / ((r : ℝ) + 1) =
                  ((r : ℝ) * δ - ((r : ℝ) + 1) * δ') ^ 2 / ((r : ℝ) * ((r : ℝ) + 1)) := by
                field_simp [hr_pos.ne', (show (r : ℝ) + 1 ≠ 0 by linarith)]
                ring
              rw [hident]
              positivity
            linarith
          · push Not at hδlt
            have h1 : δ ^ 2 / ((r : ℝ) + 1) ≤ δ' ^ 2 / (r : ℝ) := by
              calc
                δ ^ 2 / ((r : ℝ) + 1) ≤ δ ^ 2 / (r : ℝ) :=
                  div_le_div_of_nonneg_left (sq_nonneg δ) hr_pos (by linarith)
                _ ≤ δ' ^ 2 / (r : ℝ) :=
                  div_le_div_of_nonneg_right (by nlinarith) hr_pos.le
            linarith
        -- Low total surplus is preserved from `f` to `f'` since `p ≤ p'`!
        have hlow_mono : (∀ i, ∑ j : I, M.surplus f j < M.budget i) →
            ∀ i, ∑ j : I, M.surplus f' j < M.budget i := by
          intro hlow i
          have hsum_le : ∑ j : I, M.surplus f' j ≤ ∑ j : I, M.surplus f j := by
            rw [sum_surplus_eq (fun g => (hp'_pos g).le) hinv' hf'max,
              sum_surplus_eq (fun g => (hp g).le) hinv (hbal.isMaxEqualityFlow fun g => (hp g).le)]
            have hgv : ∑ g : G, p g * M.supply g ≤ ∑ g : G, p' g * M.supply g :=
              Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_right (hp_le g) (M.supply_nonneg g)
            linarith
          exact hsum_le.trans_lt (hlow i)
        have heval : (dpsvPhaseLoop M (k + 1) p f H).eval oracle =
            let res := (dpsvPhaseLoop M k p' f' H').eval oracle
            ⟨res.price, res.flow, res.tightSet, res.iters + 1⟩ := by
          rw [dpsvPhaseLoop, FreeM.eval_bind, hft_eval]
          simp [J, hratio, hlt, p', f', H']
        have hcount : (dpsvPhaseLoop M (k + 1) p f H).countQueries oracle =
            ((M.activeMarket H).findTightSetProgram p J).countQueries oracle +
              (M.balancedFlowProgram p').countQueries oracle +
              (dpsvPhaseLoop M k p' f' H').countQueries oracle := by
          rw [dpsvPhaseLoop, FreeM.countQueries_bind, hft_eval]
          simp [J, hratio, hlt, p', f', H', Nat.add_assoc]
        dsimp only
        rw [heval, hcount]
        dsimp only
        have hit_bound : r + 1 ≤ Fintype.card G - J.card + 1 := by
          have : r ≤ Fintype.card G - J'.card + 1 := hih_it_le
          omega
        refine ⟨hih_pos, fun g => (hp_le g).trans (hih_le g), hih_inv, hih_bal, by omega, hit_bound,
          ?_, htotal_drop, hih_Sne, fun g hg => lt_of_le_of_lt (hp_le g) (hih_Sstrict g hg),
          fun hlow => hih_Stight (hlow_mono hlow)⟩
        have hq_rec : (dpsvPhaseLoop M k p' f' H').countQueries oracle ≤
            2 * Fintype.card G * r := hih_q
        have hmul : 2 * Fintype.card G * (r + 1) = 2 * Fintype.card G + 2 * Fintype.card G * r := by
          ring
        change _ ≤ 2 * Fintype.card G * (r + 1)
        omega
      · -- Event 1 (`x1 ≤ x2`)!
        have hE1 := hEvent1 (fun r hr => by rw [hratio] at hr; injection hr with hr; linarith)
        have heval : (dpsvPhaseLoop M (k + 1) p f H).eval oracle =
            ⟨scaleActivePrices p J x1,
              (M.balancedFlowProgram (scaleActivePrices p J x1)).eval oracle, S1, 1⟩ := by
          rw [dpsvPhaseLoop, FreeM.eval_bind, hft_eval]
          simp [J, hratio, hlt]
        have hcount : (dpsvPhaseLoop M (k + 1) p f H).countQueries oracle =
            ((M.activeMarket H).findTightSetProgram p J).countQueries oracle +
              (M.balancedFlowProgram (scaleActivePrices p J x1)).countQueries oracle := by
          rw [dpsvPhaseLoop, FreeM.countQueries_bind, hft_eval]
          simp [J, hratio, hlt]
        simpa only [heval, hcount] using hE1

/-- **Lemmas 5.14 and 5.21** ([Vazirani2007], Section 5.10, pp. 119, 121): when `N(p)` satisfies
the Invariant at positive prices `p` and balanced flow `f` has at least one buyer with positive
surplus, `M.dpsvPhaseProgram p f` executes between `1` and `n = Fintype.card G` iterations using
at most `2 * n * iters ≤ 2 * n ^ 2` max-flow oracle calls, preserves positivity and the Invariant,
never decreases prices, strictly raises prices on a nonempty set `res.tightSet` (which is a genuine
tight set in `N(res.price)` whenever total surplus is strictly smaller than every buyer's budget),
and reduces `M.surplusSqNorm` by at least `δ ^ 2 / n` and by a factor of `1 - 1 / (m * n)`
(specializing to `1 - 1 / n ^ 2` when `m = Fintype.card I ≤ n`). -/
theorem dpsvPhaseProgram_spec {M : LinearFisherMarket I G}
    (hsup_pos : ∀ g, 0 < M.supply g) (hbud_pos : ∀ i, 0 < M.budget i)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g)
    {p : G → ℝ} (hp : ∀ g, 0 < p g) (hinv : M.SatisfiesInvariant p)
    {f : G → I → ℝ} (hbal : M.IsBalancedFlow p f) (hnot_eq : ∃ i, 0 < M.surplus f i)
    {oracle : {ι : Type u} → MaxFlowQuery I G ι → ι}
    (horacle : IsValidMaxFlowOracle oracle) :
    let m := Fintype.card I
    let n := Fintype.card G
    let prog := M.dpsvPhaseProgram p f
    let res := prog.eval oracle
    (∀ g, 0 < res.price g) ∧
    (∀ g, p g ≤ res.price g) ∧
    M.SatisfiesInvariant res.price ∧
    M.IsBalancedFlow res.price res.flow ∧
    1 ≤ res.iters ∧
    res.iters ≤ n ∧
    prog.countQueries oracle ≤ 2 * n * res.iters ∧
    M.surplusSqNorm res.flow ≤ (1 - 1 / ((m : ℝ) * (n : ℝ))) * M.surplusSqNorm f ∧
    res.tightSet.Nonempty ∧
    (∀ g ∈ res.tightSet, p g < res.price g) ∧
    ((∀ i, ∑ j : I, M.surplus f j < M.budget i) → M.IsTightSet res.price res.tightSet) := by
  classical
  intro m n prog res
  obtain ⟨i_pos, hi_pos⟩ := hnot_eq
  have hnot_all0 : ¬ ∀ i : I, M.surplus f i = 0 := fun h => hi_pos.ne' (h i_pos)
  have hI : (Finset.univ : Finset I).Nonempty := ⟨i_pos, Finset.mem_univ i_pos⟩
  set δ := Finset.univ.sup' hI (M.surplus f)
  have hδ_pos : 0 < δ := hi_pos.trans_le (Finset.le_sup' (M.surplus f) (Finset.mem_univ i_pos))
  let H0 : Finset I := Finset.univ.filter fun i => M.surplus f i = δ
  have hH0 : H0.Nonempty := by
    obtain ⟨im, -, him⟩ := Finset.exists_mem_eq_sup' hI (M.surplus f)
    exact ⟨im, Finset.mem_filter.2 ⟨Finset.mem_univ _, him.symm⟩⟩
  have hclosed0 : IsResidualClosed M p f H0 := by
    intro u v huv hvH0
    have hv_eq : M.surplus f v = δ := (Finset.mem_filter.1 hvH0).2
    have hprop1 := (isBalancedFlow_iff_satisfiesPropertyOne
      (hbal.isMaxEqualityFlow fun g => (hp g).le)).1 hbal
    have hu_ge : δ ≤ M.surplus f u := by
      by_contra hlt; push Not at hlt
      exact hprop1 u v (by linarith) huv
    have hu_le : M.surplus f u ≤ δ := Finset.le_sup' (M.surplus f) (Finset.mem_univ u)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, le_antisymm hu_le hu_ge⟩
  have hpos0 : ∀ i ∈ H0, 0 < M.surplus f i := fun i hi =>
    (Finset.mem_filter.1 hi).2.symm ▸ hδ_pos
  have hJ0_ne : (M.activeGoods p H0).Nonempty := by
    obtain ⟨i₀, hi₀⟩ := hH0
    obtain ⟨g₀, -⟩ := hbuyer i₀
    have : Nonempty G := ⟨g₀⟩
    obtain ⟨g, hE⟩ := exists_isEqualityEdge M p i₀
    exact ⟨g, mem_activeGoods.2 ⟨i₀, hi₀, hE⟩⟩
  have hJ0_card : 1 ≤ (M.activeGoods p H0).card := Finset.one_le_card.2 hJ0_ne
  have hJ0_le : (M.activeGoods p H0).card ≤ n := Finset.card_le_univ _
  have hprog_eq : prog = dpsvPhaseLoop M n p f H0 := by
    simp [prog, dpsvPhaseProgram, hnot_all0, hI, δ, H0, n]
  obtain ⟨h1, h2, h3, h4, hit1, hit_le, hq, hdrop, hSne, hSstr, hStight⟩ :=
    dpsvPhaseLoop_spec hsup_pos hbud_pos hbuyer horacle n p f H0 hH0 hp hinv hbal hclosed0
      hpos0 (by omega)
  have hinf0 : H0.inf' hH0 (M.surplus f) = δ := by
    apply le_antisymm
    · obtain ⟨i₀, hi₀⟩ := hH0
      exact (Finset.inf'_le (M.surplus f) hi₀).trans (Finset.mem_filter.1 hi₀).2.le
    · rw [Finset.le_inf'_iff]; intro i hi; exact (Finset.mem_filter.1 hi).2.ge
  have hit_le_n : ((dpsvPhaseLoop M n p f H0).eval oracle).iters ≤ n := by omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 (Finset.card_pos.2 hI)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (by omega)
  have hnorm_le : M.surplusSqNorm f ≤ (m : ℝ) * δ ^ 2 := by
    calc
      M.surplusSqNorm f = ∑ i : I, (M.surplus f i) ^ 2 := rfl
      _ ≤ ∑ _i : I, δ ^ 2 := Finset.sum_le_sum fun i _ => by
            have hnn : 0 ≤ M.surplus f i := sub_nonneg.2 (hbal.1.2.2.2 i)
            have hle : M.surplus f i ≤ δ := Finset.le_sup' (M.surplus f) (Finset.mem_univ i)
            nlinarith
      _ = (m : ℝ) * δ ^ 2 := by simp [m]
  have hdrop_factor : M.surplusSqNorm ((dpsvPhaseLoop M n p f H0).eval oracle).flow ≤
      (1 - 1 / ((m : ℝ) * (n : ℝ))) * M.surplusSqNorm f := by
    rw [hinf0] at hdrop
    have hit_pos_r : (0 : ℝ) < (((dpsvPhaseLoop M n p f H0).eval oracle).iters : ℝ) :=
      Nat.cast_pos.2 (by omega)
    have hit_le_r : (((dpsvPhaseLoop M n p f H0).eval oracle).iters : ℝ) ≤ (n : ℝ) :=
      Nat.cast_le.2 hit_le_n
    have hdiv_ge : δ ^ 2 / (n : ℝ) ≤
        δ ^ 2 / (((dpsvPhaseLoop M n p f H0).eval oracle).iters : ℝ) :=
      div_le_div_of_nonneg_left (sq_nonneg δ) hit_pos_r hit_le_r
    have hmn_pos : 0 < (m : ℝ) * (n : ℝ) := mul_pos hm_pos hn_pos
    have hfrac : M.surplusSqNorm f / ((m : ℝ) * (n : ℝ)) ≤ δ ^ 2 / (n : ℝ) := by
      rw [div_le_div_iff₀ hmn_pos hn_pos]
      nlinarith
    have hlin : (1 - 1 / ((m : ℝ) * (n : ℝ))) * M.surplusSqNorm f =
        M.surplusSqNorm f - M.surplusSqNorm f / ((m : ℝ) * (n : ℝ)) := by ring
    linarith
  simpa only [res, hprog_eq] using
    ⟨h1, h2, h3, h4, hit1, hit_le_n, hq, hdrop_factor, hSne, hSstr, hStight⟩

end PhaseExecution

/-! ### Section 5.10: Full DPSV algorithm and Theorem 5.22 -/

section MainAlgorithm

variable {I G : Type u} [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]

/-- Output of the full DPSV primal-dual algorithm ([Vazirani2007], Sections 5.8 and 5.10). -/
structure DPSVResult (I G : Type u) where
  /-- Market equilibrium allocation `alloc i g = f g i / price g`. -/
  alloc : I → G → ℝ
  /-- Market equilibrium price vector. -/
  price : G → ℝ
  /-- Number of phases executed before reaching equilibrium. -/
  phases : ℕ

/-- Phase-iteration loop of the DPSV algorithm in `FreeM (MaxFlowQuery I G)`. -/
private noncomputable def dpsvLoop (M : LinearFisherMarket I G) :
    ℕ → (G → ℝ) → (G → I → ℝ) → FreeM (MaxFlowQuery I G) (DPSVResult I G)
  | 0, p, f => pure ⟨moneyFlowToAlloc f p, p, 0⟩
  | k + 1, p, f =>
      open scoped Classical in
      if ∀ i : I, M.surplus f i = 0 then
        pure ⟨moneyFlowToAlloc f p, p, 0⟩
      else do
        let res ← M.dpsvPhaseProgram p f
        let final ← dpsvLoop M k res.price res.flow
        pure ⟨final.alloc, final.price, final.phases + 1⟩

/-- Upper bound `T_max(m, n, U, M_tot)` on the number of DPSV phases for a market with `m` buyers,
`n` goods, integer utilities `≤ U`, and total integer budget `M_tot`. -/
@[expose] def dpsvPhaseBound (m n U M_tot : ℕ) : ℕ :=
  m * n * (Nat.log 2 (m * (n * U ^ n) ^ 4 * M_tot ^ 2) + 1) + n

/-- **The DPSV primal-dual algorithm** ([Vazirani2007], Sections 5.8 and 5.10, pp. 115–121) in
`Cslib.FreeM (MaxFlowQuery I G)`: initializes prices via `M.dpsvInitPrice`, computes an initial
balanced flow via `M.balancedFlowProgram`, and executes DPSV phases until all buyer surpluses
vanish (at most `dpsvPhaseBound` phases using the market's own maximum utility and total budget).
-/
noncomputable def dpsvProgram (M : LinearFisherMarket I G) :
    FreeM (MaxFlowQuery I G) (DPSVResult I G) :=
  open scoped Classical in
  if hG : (Finset.univ : Finset G).Nonempty then
    if hI : (Finset.univ : Finset I).Nonempty then do
      let Umax : ℕ := ⌈(Finset.univ ×ˢ Finset.univ).sup' (hI.product hG)
        (fun ig : I × G => M.utility ig.1 ig.2)⌉₊
      let Mtot : ℕ := ⌈∑ i : I, M.budget i⌉₊
      let limit := dpsvPhaseBound (Fintype.card I) (Fintype.card G) Umax Mtot
      let p0 := M.dpsvInitPrice
      let f0 ← M.balancedFlowProgram p0
      dpsvLoop M limit p0 f0
    else pure ⟨0, 0, 0⟩
  else pure ⟨0, 0, 0⟩

/-- Helper for `dpsvLoop_endgame`: under low starting gap `< 1 / Δ^2`, any non-terminal phase
produces a genuine tight set `res.tightSet` at `res.price` whose goods cannot already lie in
`seen` (by Lemma 5.13). -/
private theorem endgame_phase_tight_not_seen {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) (hsup : ∀ g, M.supply g = 1)
    {u : I → G → ℕ} (hu : ∀ i g, M.utility i g = (u i g : ℝ))
    {U : ℕ} (hU : ∀ i g, u i g ≤ U)
    {e : I → ℕ} (he : ∀ i, M.budget i = (e i : ℝ))
    {oracle : {ι : Type u} → MaxFlowQuery I G ι → ι}
    (horacle : IsValidMaxFlowOracle oracle)
    {p_start p_seen p : G → ℝ} {f : G → I → ℝ} {seen : Finset G}
    (hstart_gap : (∑ i : I, M.budget i) - ∑ g : G, p_start g <
      1 / ((Fintype.card G * U ^ Fintype.card G : ℕ) : ℝ) ^ 2)
    (hp : ∀ g, 0 < p g) (hp_start : ∀ g, p_start g ≤ p g)
    (hinv : M.SatisfiesInvariant p) (hbal : M.IsBalancedFlow p f)
    (hnot_eq : ∃ i, 0 < M.surplus f i)
    (hseen : ∀ g ∈ seen, ∃ (p_g : G → ℝ) (S_g : Finset G),
      (∀ g', 0 < p_g g') ∧ M.SatisfiesInvariant p_g ∧ M.IsTightSet p_g S_g ∧
      g ∈ S_g ∧ p_start g ≤ p_g g ∧ p_g g = p_seen g ∧ p_seen g ≤ p g) :
    let res := (M.dpsvPhaseProgram p f).eval oracle
    M.IsTightSet res.price res.tightSet ∧
      ∃ g₀ ∈ res.tightSet, g₀ ∉ seen := by
  classical
  set n := Fintype.card G
  set Δ : ℕ := n * U ^ n
  have hbud_ge1 : ∀ i : I, 1 ≤ M.budget i := fun i => by
    have hpos : (0 : ℝ) < (e i : ℝ) := he i ▸ hnd.budget_pos i
    have hnat : 1 ≤ e i := by exact_mod_cast hpos
    rw [he i]
    exact_mod_cast hnat
  obtain ⟨hp', hp_le, hinv', -, -, -, -, -, hSne, hSstr, hStight⟩ :=
    dpsvPhaseProgram_spec hnd.supply_pos hnd.budget_pos hnd.buyer_nonsatiated
      hp hinv hbal hnot_eq horacle
  set res := (M.dpsvPhaseProgram p f).eval oracle
  have hlow : ∀ i : I, ∑ j : I, M.surplus f j < M.budget i := by
    intro i
    have hsum_eq := sum_surplus_eq (fun g => (hp g).le) hinv
      (hbal.isMaxEqualityFlow fun g => (hp g).le)
    have hsum_p : ∑ g : G, p_start g ≤ ∑ g : G, p g := Finset.sum_le_sum fun g _ => hp_start g
    have hsup_eq : ∑ g : G, p g * M.supply g = ∑ g : G, p g := by simp [hsup]
    have hΔ_ge1 : (1 : ℝ) ≤ (Δ : ℝ) := by
      obtain ⟨g₀, -⟩ := hSne
      obtain ⟨j₀, hj₀⟩ := hnd.good_desired g₀
      rw [hu j₀ g₀] at hj₀
      have hu_pos : 1 ≤ u j₀ g₀ := by exact_mod_cast hj₀
      have hU_ge1 : 1 ≤ U := hu_pos.trans (hU j₀ g₀)
      have hn_ge1 : 1 ≤ n := Fintype.card_pos_iff.2 ⟨g₀⟩
      have : 1 ≤ Δ := Nat.mul_pos hn_ge1 (Nat.pow_pos hU_ge1)
      exact_mod_cast this
    have hinv_le1 : 1 / (Δ : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith [hbud_ge1 i]
  have htight' : M.IsTightSet res.price res.tightSet := hStight hlow
  obtain ⟨g₀, hg₀⟩ := hSne
  refine ⟨htight', g₀, hg₀, fun hg₀_mem => ?_⟩
  obtain ⟨p_g, S_g, hpg_pos, hpg_inv, hpg_tight, hg₀S, hpg_start, hpg_eq, hpg_le⟩ :=
    hseen g₀ hg₀_mem
  have hlt_g : p_g g₀ < res.price g₀ := by linarith [hSstr g₀ hg₀]
  have h513 := price_sub_ge_inv_sq_of_isTightSet hsup hu hU he hnd.buyer_nonsatiated
    hpg_pos hp' hpg_inv hinv' hpg_tight htight' hg₀S hg₀ hlt_g
  have hsum_ub : ∑ g : G, res.price g ≤ ∑ i : I, M.budget i := by
    have h1 := (satisfiesInvariant_iff fun g => (hp' g).le).1 hinv' Finset.univ
    have hgv : M.goodValue res.price Finset.univ = ∑ g : G, res.price g := by
      simp [goodValue, hsup]
    have hbud : M.budgetSum (M.buyerNeighborhood res.price Finset.univ) ≤
        ∑ i : I, M.budget i := Finset.sum_le_univ_sum_of_nonneg M.budget_nonneg
    linarith
  have hgap_ge : res.price g₀ - p_start g₀ ≤ (∑ i : I, M.budget i) - ∑ g : G, p_start g := by
    have hle : res.price g₀ - p_start g₀ ≤ ∑ g : G, (res.price g - p_start g) :=
      Finset.single_le_sum (fun g _ => sub_nonneg.2 ((hp_start g).trans (hp_le g)))
        (Finset.mem_univ g₀)
    rw [Finset.sum_sub_distrib] at hle
    linarith
  linarith

omit [DecidableEq I] [DecidableEq G] in
private theorem exists_surplus_pos_of_not_all_zero
    {M : LinearFisherMarket I G} {p : G → ℝ} {f : G → I → ℝ}
    (hf : M.IsEqualityFlow p f) (h : ¬ ∀ i : I, M.surplus f i = 0) :
    ∃ i : I, 0 < M.surplus f i := by
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, lt_of_le_of_ne (sub_nonneg.2 (hf.2.2.2 i)) (Ne.symm hi)⟩

/-- **Endgame termination** ([Vazirani2007], Theorem 5.22, p. 121): once total surplus drops below
`1 / Δ ^ 2`, every subsequent phase creates a genuine tight set on a good not previously tight
during the endgame (by Lemma 5.13), so `dpsvLoop` reaches exact equilibrium in at most `n` phases.
-/
private theorem dpsvLoop_endgame {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) (hsup : ∀ g, M.supply g = 1)
    {u : I → G → ℕ} (hu : ∀ i g, M.utility i g = (u i g : ℝ))
    {U : ℕ} (hU : ∀ i g, u i g ≤ U)
    {e : I → ℕ} (he : ∀ i, M.budget i = (e i : ℝ))
    {oracle : {ι : Type u} → MaxFlowQuery I G ι → ι}
    (horacle : IsValidMaxFlowOracle oracle)
    {p_start : G → ℝ}
    (hstart_gap : (∑ i : I, M.budget i) - ∑ g : G, p_start g <
      1 / ((Fintype.card G * U ^ Fintype.card G : ℕ) : ℝ) ^ 2) :
    ∀ (k : ℕ) (seen : Finset G) (p_seen p : G → ℝ) (f : G → I → ℝ),
      (∀ g, 0 < p g) →
      (∀ g, p_start g ≤ p g) →
      M.SatisfiesInvariant p →
      M.IsBalancedFlow p f →
      (∀ g ∈ seen, ∃ (p_g : G → ℝ) (S_g : Finset G),
        (∀ g', 0 < p_g g') ∧ M.SatisfiesInvariant p_g ∧ M.IsTightSet p_g S_g ∧
        g ∈ S_g ∧ p_start g ≤ p_g g ∧ p_g g = p_seen g ∧ p_seen g ≤ p g) →
      Fintype.card G - seen.card ≤ k →
      let prog := dpsvLoop M k p f
      let res := prog.eval oracle
      M.IsEquilibrium res.alloc res.price ∧
        res.phases ≤ Fintype.card G - seen.card ∧
        prog.countQueries oracle ≤ 2 * (Fintype.card G) ^ 2 * res.phases := by
  classical
  set n := Fintype.card G
  intro k
  induction k with
  | zero =>
    intro seen p_seen p f hp hp_start hinv hbal hseen hk
    have hall_seen : seen = Finset.univ := by
      apply Finset.eq_univ_of_card
      have := Finset.card_le_univ seen
      omega
    have hsurp0 : ∀ i : I, M.surplus f i = 0 := by
      by_contra hnot
      obtain ⟨i₀, hpos_i₀⟩ := exists_surplus_pos_of_not_all_zero hbal.1 hnot
      obtain ⟨-, g₀, -, hg₀_not_seen⟩ :=
        endgame_phase_tight_not_seen hnd hsup hu hU he horacle hstart_gap hp hp_start hinv hbal
          ⟨i₀, hpos_i₀⟩ hseen
      exact hg₀_not_seen (hall_seen ▸ Finset.mem_univ g₀)
    simp only [dpsvLoop, FreeM.eval_pure, FreeM.countQueries_pure]
    exact ⟨isEquilibrium_of_surplus_eq_zero hp hnd.buyer_nonsatiated hnd.good_desired hinv
      (hbal.isMaxEqualityFlow fun g => (hp g).le) hsurp0, Nat.zero_le _, by simp⟩
  | succ k ih =>
    intro seen p_seen p f hp hp_start hinv hbal hseen hk
    by_cases hsurp0 : ∀ i : I, M.surplus f i = 0
    · have heval : (dpsvLoop M (k + 1) p f).eval oracle = ⟨moneyFlowToAlloc f p, p, 0⟩ := by
        simp [dpsvLoop, hsurp0]
      have hcount : (dpsvLoop M (k + 1) p f).countQueries oracle = 0 := by
        simp [dpsvLoop, hsurp0]
      dsimp only
      rw [heval, hcount]
      dsimp only
      exact ⟨isEquilibrium_of_surplus_eq_zero hp hnd.buyer_nonsatiated hnd.good_desired hinv
        (hbal.isMaxEqualityFlow fun g => (hp g).le) hsurp0, Nat.zero_le _, by simp⟩
    · obtain ⟨i₀, hpos_i₀⟩ := exists_surplus_pos_of_not_all_zero hbal.1 hsurp0
      obtain ⟨hp', hp_le, hinv', hbal', -, hit_le, hq_phase, -, -, -, -⟩ :=
        dpsvPhaseProgram_spec hnd.supply_pos hnd.budget_pos hnd.buyer_nonsatiated
          hp hinv hbal ⟨i₀, hpos_i₀⟩ horacle
      obtain ⟨htight', g₀, hg₀, hg₀_not_seen⟩ :=
        endgame_phase_tight_not_seen hnd hsup hu hU he horacle hstart_gap hp hp_start hinv hbal
          ⟨i₀, hpos_i₀⟩ hseen
      set res := (M.dpsvPhaseProgram p f).eval oracle
      let seen' := insert g₀ seen
      let p_seen' := Function.update p_seen g₀ (res.price g₀)
      have hcard_seen' : seen'.card = seen.card + 1 := Finset.card_insert_of_notMem hg₀_not_seen
      have hcard_lt : seen.card < n := by
        have hle := Finset.card_le_univ seen'
        omega
      have hseen' : ∀ g ∈ seen', ∃ (p_g : G → ℝ) (S_g : Finset G),
          (∀ g', 0 < p_g g') ∧ M.SatisfiesInvariant p_g ∧ M.IsTightSet p_g S_g ∧
          g ∈ S_g ∧ p_start g ≤ p_g g ∧ p_g g = p_seen' g ∧ p_seen' g ≤ res.price g := by
        intro g hg
        rcases Finset.mem_insert.1 hg with rfl | hg_old
        · exact ⟨res.price, res.tightSet, hp', hinv', htight', hg₀,
            (hp_start g).trans (hp_le g), by simp [p_seen'], by simp [p_seen']⟩
        · have hne : g ≠ g₀ := fun h => hg₀_not_seen (h ▸ hg_old)
          obtain ⟨p_g, S_g, h1, h2, h3, h4, h5, h6, h7⟩ := hseen g hg_old
          exact ⟨p_g, S_g, h1, h2, h3, h4, h5, by simp [p_seen', hne, h6],
            by dsimp only [p_seen']; rw [Function.update_of_ne hne]; exact h7.trans (hp_le g)⟩
      obtain ⟨hih_eq, hih_ph, hih_q⟩ := ih seen' p_seen' res.price res.flow hp'
        (fun g => (hp_start g).trans (hp_le g)) hinv' hbal' hseen' (by omega)
      have heval : (dpsvLoop M (k + 1) p f).eval oracle =
          let final := (dpsvLoop M k res.price res.flow).eval oracle
          ⟨final.alloc, final.price, final.phases + 1⟩ := by
        rw [dpsvLoop]
        simp [hsurp0, res]
      have hcount : (dpsvLoop M (k + 1) p f).countQueries oracle =
          (M.dpsvPhaseProgram p f).countQueries oracle +
            (dpsvLoop M k res.price res.flow).countQueries oracle := by
        rw [dpsvLoop]
        simp [hsurp0, res]
      dsimp only
      rw [heval, hcount]
      dsimp only
      have hq_step : (M.dpsvPhaseProgram p f).countQueries oracle ≤ 2 * n ^ 2 := by
        calc
          (M.dpsvPhaseProgram p f).countQueries oracle ≤ 2 * n * res.iters := hq_phase
          _ ≤ 2 * n * n := Nat.mul_le_mul_left _ hit_le
          _ = 2 * n ^ 2 := by ring
      have hq_tot : 2 * n ^ 2 + 2 * n ^ 2 * ((dpsvLoop M k res.price res.flow).eval oracle).phases =
          2 * n ^ 2 * (((dpsvLoop M k res.price res.flow).eval oracle).phases + 1) := by ring
      exact ⟨hih_eq, by omega, by omega⟩

/-- **Geometric decay prefix** for `dpsvLoop`: after at most `t` phases, either `dpsvLoop` has
already terminated at equilibrium, or it continues from `(p_t, f_t)` whose squared `ℓ₂` surplus
norm has decayed by `(1 - 1 / (m * n)) ^ t`. -/
private theorem dpsvLoop_decay {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate)
    {oracle : {ι : Type u} → MaxFlowQuery I G ι → ι}
    (horacle : IsValidMaxFlowOracle oracle) :
    ∀ (t r : ℕ) (p : G → ℝ) (f : G → I → ℝ),
      (∀ g, 0 < p g) →
      M.SatisfiesInvariant p →
      M.IsBalancedFlow p f →
      let m := Fintype.card I
      let n := Fintype.card G
      let prog := dpsvLoop M (t + r) p f
      let res := prog.eval oracle
      (M.IsEquilibrium res.alloc res.price ∧ res.phases ≤ t ∧
        prog.countQueries oracle ≤ 2 * n ^ 2 * res.phases) ∨
      ∃ (p' : G → ℝ) (f' : G → I → ℝ),
        (∀ g, 0 < p' g) ∧
        M.SatisfiesInvariant p' ∧
        M.IsBalancedFlow p' f' ∧
        M.surplusSqNorm f' ≤ (1 - 1 / ((m : ℝ) * (n : ℝ))) ^ t * M.surplusSqNorm f ∧
        res = ⟨((dpsvLoop M r p' f').eval oracle).alloc,
          ((dpsvLoop M r p' f').eval oracle).price,
          ((dpsvLoop M r p' f').eval oracle).phases + t⟩ ∧
        prog.countQueries oracle ≤
          2 * n ^ 2 * t + (dpsvLoop M r p' f').countQueries oracle := by
  classical
  intro t
  induction t with
  | zero =>
    intro r p f hp hinv hbal
    right
    refine ⟨p, f, hp, hinv, hbal, by simp, ?_, by simp⟩
    simp only [Nat.zero_add, Nat.add_zero]
  | succ t ih =>
    intro r p f hp hinv hbal
    set m := Fintype.card I
    set n := Fintype.card G
    by_cases hsurp0 : ∀ i : I, M.surplus f i = 0
    · left
      have heval : (dpsvLoop M (t + 1 + r) p f).eval oracle = ⟨moneyFlowToAlloc f p, p, 0⟩ := by
        rw [show t + 1 + r = (t + r) + 1 by omega]
        simp [dpsvLoop, hsurp0]
      have hcount : (dpsvLoop M (t + 1 + r) p f).countQueries oracle = 0 := by
        rw [show t + 1 + r = (t + r) + 1 by omega]
        simp [dpsvLoop, hsurp0]
      rw [heval, hcount]
      exact ⟨isEquilibrium_of_surplus_eq_zero hp hnd.buyer_nonsatiated hnd.good_desired hinv
        (hbal.isMaxEqualityFlow fun g => (hp g).le) hsurp0, Nat.zero_le _, by simp⟩
    · obtain ⟨i₀, hpos_i₀⟩ := exists_surplus_pos_of_not_all_zero hbal.1 hsurp0
      obtain ⟨hp₁, -, hinv₁, hbal₁, -, hit_le, hq_phase, hdrop₁, -, -, -⟩ :=
        dpsvPhaseProgram_spec hnd.supply_pos hnd.budget_pos hnd.buyer_nonsatiated
          hp hinv hbal ⟨i₀, hpos_i₀⟩ horacle
      set res₁ := (M.dpsvPhaseProgram p f).eval oracle
      have heval_step : (dpsvLoop M (t + 1 + r) p f).eval oracle =
          let final := (dpsvLoop M (t + r) res₁.price res₁.flow).eval oracle
          ⟨final.alloc, final.price, final.phases + 1⟩ := by
        rw [show t + 1 + r = (t + r) + 1 by omega, dpsvLoop]
        simp [hsurp0, res₁]
      have hcount_step : (dpsvLoop M (t + 1 + r) p f).countQueries oracle =
          (M.dpsvPhaseProgram p f).countQueries oracle +
            (dpsvLoop M (t + r) res₁.price res₁.flow).countQueries oracle := by
        rw [show t + 1 + r = (t + r) + 1 by omega, dpsvLoop]
        simp [hsurp0, res₁]
      have hq_step : (M.dpsvPhaseProgram p f).countQueries oracle ≤ 2 * n ^ 2 := by
        calc
          (M.dpsvPhaseProgram p f).countQueries oracle ≤ 2 * n * res₁.iters := hq_phase
          _ ≤ 2 * n * n := Nat.mul_le_mul_left _ hit_le
          _ = 2 * n ^ 2 := by ring
      rcases ih r res₁.price res₁.flow hp₁ hinv₁ hbal₁ with
          ⟨heq, hph, hq⟩ | ⟨p', f', hp', hinv', hbal', hnorm', hres', hq'⟩
      · left
        rw [heval_step, hcount_step]
        dsimp only
        have hmul :
            2 * n ^ 2 * (((dpsvLoop M (t + r) res₁.price res₁.flow).eval oracle).phases + 1) =
            2 * n ^ 2 +
              2 * n ^ 2 * ((dpsvLoop M (t + r) res₁.price res₁.flow).eval oracle).phases :=
          by ring
        exact ⟨heq, by omega, by omega⟩
      · right
        have hfactor_nn : 0 ≤ 1 - 1 / ((m : ℝ) * (n : ℝ)) := by
          obtain ⟨g₀, -⟩ := hnd.buyer_nonsatiated i₀
          have hm1 : 1 ≤ m := Fintype.card_pos_iff.2 ⟨i₀⟩
          have hn1 : 1 ≤ n := Fintype.card_pos_iff.2 ⟨g₀⟩
          have hmn1 : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by
            exact_mod_cast Nat.mul_pos hm1 hn1
          rw [sub_nonneg, div_le_one (by linarith)]
          exact hmn1
        refine ⟨p', f', hp', hinv', hbal', ?_, ?_, ?_⟩
        · calc
            M.surplusSqNorm f' ≤ (1 - 1 / ((m : ℝ) * (n : ℝ))) ^ t * M.surplusSqNorm res₁.flow :=
              hnorm'
            _ ≤ (1 - 1 / ((m : ℝ) * (n : ℝ))) ^ t *
                  ((1 - 1 / ((m : ℝ) * (n : ℝ))) * M.surplusSqNorm f) :=
              mul_le_mul_of_nonneg_left hdrop₁ (pow_nonneg hfactor_nn t)
            _ = (1 - 1 / ((m : ℝ) * (n : ℝ))) ^ (t + 1) * M.surplusSqNorm f := by
              rw [pow_succ]; ring
        · rw [heval_step, hres']
          simp [Nat.add_assoc]
        · rw [hcount_step]
          have hmul : 2 * n ^ 2 * (t + 1) = 2 * n ^ 2 + 2 * n ^ 2 * t := by ring
          omega

/-- **Theorem 5.22** ([Vazirani2007], Section 5.10, p. 121): for every non-degenerate unit-supply
linear Fisher market with integer utilities `u i g ≤ U` and integer budgets `e i`
(`M_tot = ∑ i, e i`, `m = Fintype.card I`, `n = Fintype.card G`, `Δ = n * U ^ n`), the DPSV
primal-dual algorithm `M.dpsvProgram` evaluated with any valid max-flow oracle computes an exact
market equilibrium `(res.alloc, res.price)` in at most
`dpsvPhaseBound m n U M_tot = m * n * (Nat.log 2 (m * Δ ^ 4 * M_tot ^ 2) + 1) + n` phases and at
most `n + 2 * n ^ 2 * res.phases` max-flow oracle calls — yielding
`O(m * n ^ 3 * (log m + log n + n log U + log M_tot))` max-flow computations (and
`O(n ^ 4 * (log n + n log U + log M_tot))` when `m ≤ n`).

Note: this states the max-flow oracle query complexity in `Cslib.FreeM`, matching [Vazirani2007],
Theorem 5.22's count of max-flow computations rather than a machine-level bit-complexity runtime.
-/
theorem dpsvProgram_spec {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) (hsup : ∀ g, M.supply g = 1)
    {u : I → G → ℕ} (hu : ∀ i g, M.utility i g = (u i g : ℝ))
    {U : ℕ} (hU : ∀ i g, u i g ≤ U)
    {e : I → ℕ} (he : ∀ i, M.budget i = (e i : ℝ))
    {oracle : {ι : Type u} → MaxFlowQuery I G ι → ι}
    (horacle : IsValidMaxFlowOracle oracle) :
    let m := Fintype.card I
    let n := Fintype.card G
    let M_tot := ∑ i : I, e i
    let res := M.dpsvProgram.eval oracle
    M.IsEquilibrium res.alloc res.price ∧
      res.phases ≤ dpsvPhaseBound m n U M_tot ∧
      M.dpsvProgram.countQueries oracle ≤ n + 2 * n ^ 2 * res.phases := by
  classical
  intro m n M_tot res
  by_cases hG : (Finset.univ : Finset G).Nonempty
  · have hG' := hG
    obtain ⟨g_any, -⟩ := hG'
    obtain ⟨i_any, -⟩ := hnd.good_desired g_any
    have hI : (Finset.univ : Finset I).Nonempty := ⟨i_any, Finset.mem_univ i_any⟩
    set Umax : ℕ := ⌈(Finset.univ ×ˢ Finset.univ).sup' (hI.product hG)
      (fun ig : I × G => M.utility ig.1 ig.2)⌉₊
    set Mtot : ℕ := ⌈∑ i : I, M.budget i⌉₊
    have hMtot_eq : Mtot = M_tot := by
      have hsum : ∑ i : I, M.budget i = (M_tot : ℝ) := by simp [M_tot, he]
      simp [Mtot, hsum]
    have hu_le_Umax : ∀ i g, u i g ≤ Umax := fun i g => by
      have h1 : (u i g : ℝ) ≤ (Finset.univ ×ˢ Finset.univ).sup' (hI.product hG)
          (fun ig : I × G => M.utility ig.1 ig.2) := by
        rw [← hu i g]
        exact Finset.le_sup' (f := fun ig : I × G => M.utility ig.1 ig.2)
          (show (i, g) ∈ (Finset.univ : Finset I) ×ˢ (Finset.univ : Finset G) from
            Finset.mem_product.2 ⟨Finset.mem_univ i, Finset.mem_univ g⟩)
      have h2 : (u i g : ℝ) ≤ (Umax : ℝ) := h1.trans (Nat.le_ceil _)
      exact_mod_cast h2
    have hUmax_le_U : Umax ≤ U := by
      rw [Nat.ceil_le]
      refine Finset.sup'_le (hI.product hG) _ fun ig _ => ?_
      rw [hu ig.1 ig.2]
      exact_mod_cast hU ig.1 ig.2
    have hbud_ge1 : ∀ i : I, 1 ≤ M.budget i := fun i => by
      have hpos : (0 : ℝ) < (e i : ℝ) := he i ▸ hnd.budget_pos i
      have hnat : 1 ≤ e i := by exact_mod_cast hpos
      rw [he i]
      exact_mod_cast hnat
    -- Initialize prices and initial balanced flow `f0`.
    obtain ⟨hp0_pos, -, -, -, hinv0⟩ := dpsvInitPrice_spec hnd hsup hbud_ge1
    obtain ⟨-, hbal0, hq0⟩ :=
      balancedFlowProgram_spec (M := M) (p := M.dpsvInitPrice) (fun g => (hp0_pos g).le)
        hinv0 horacle
    set f0 := (M.balancedFlowProgram M.dpsvInitPrice).eval oracle
    set Δm : ℕ := n * Umax ^ n
    set K : ℕ := Nat.log 2 (m * Δm ^ 4 * Mtot ^ 2) + 1
    set T1 : ℕ := m * n * K
    have hlimit_eq : dpsvPhaseBound m n Umax Mtot = T1 + n := rfl
    have hprog_eq : M.dpsvProgram = (do
        let f0' ← M.balancedFlowProgram M.dpsvInitPrice
        dpsvLoop M (T1 + n) M.dpsvInitPrice f0') := by
      simp only [dpsvProgram, hG, hI, ↓reduceDIte]
      rfl
    have heval_eq : res = (dpsvLoop M (T1 + n) M.dpsvInitPrice f0).eval oracle := by
      change M.dpsvProgram.eval oracle = _
      rw [hprog_eq, FreeM.eval_bind]
    have hcount_eq : M.dpsvProgram.countQueries oracle =
        (M.balancedFlowProgram M.dpsvInitPrice).countQueries oracle +
          (dpsvLoop M (T1 + n) M.dpsvInitPrice f0).countQueries oracle := by
      rw [hprog_eq, FreeM.countQueries_bind]
    have hbound_mono : dpsvPhaseBound m n Umax Mtot ≤ dpsvPhaseBound m n U M_tot := by
      rw [hMtot_eq]
      unfold dpsvPhaseBound
      have hΔ_le : n * Umax ^ n ≤ n * U ^ n :=
        Nat.mul_le_mul_left n (Nat.pow_le_pow_left hUmax_le_U n)
      have harg_le : m * (n * Umax ^ n) ^ 4 * M_tot ^ 2 ≤ m * (n * U ^ n) ^ 4 * M_tot ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hΔ_le 4))
      have hlog_le : Nat.log 2 (m * (n * Umax ^ n) ^ 4 * M_tot ^ 2) ≤
          Nat.log 2 (m * (n * U ^ n) ^ 4 * M_tot ^ 2) := Nat.log_mono_right harg_le
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog_le 1)) n
    -- Run decay prefix of `T1` phases, followed by endgame of `n` phases!
    rcases dpsvLoop_decay hnd horacle T1 n M.dpsvInitPrice f0 hp0_pos hinv0 hbal0 with
        ⟨heq, hph, hq⟩ | ⟨p1, f1, hp1, hinv1, hbal1, hnorm1, hres1, hq1⟩
    · rw [heval_eq, hcount_eq]
      have hq' : (dpsvLoop M (T1 + n) M.dpsvInitPrice f0).countQueries oracle ≤
          2 * n ^ 2 * ((dpsvLoop M (T1 + n) M.dpsvInitPrice f0).eval oracle).phases := hq
      have hq0' : (M.balancedFlowProgram M.dpsvInitPrice).countQueries oracle ≤ n := hq0
      refine ⟨heq, (hph.trans (Nat.le_add_right T1 n)).trans hbound_mono, by omega⟩
    · -- Show `M.surplusSqNorm f1 < 1 / (m * Δm^4)`, hence `∑ i, surplus f1 i < 1 / Δm^2`!
      have hm_pos : 1 ≤ m := Finset.card_pos.2 hI
      have hn_pos : 1 ≤ n := Finset.card_pos.2 hG
      have hmn_pos : 1 ≤ m * n := Nat.mul_pos hm_pos hn_pos
      have hUmax_pos : 1 ≤ Umax := by
        obtain ⟨i₀, hi₀⟩ := hnd.good_desired g_any
        rw [hu i₀ g_any] at hi₀
        have : 1 ≤ u i₀ g_any := by exact_mod_cast hi₀
        exact this.trans (hu_le_Umax i₀ g_any)
      have hΔm_pos : 1 ≤ Δm := Nat.mul_pos hn_pos (Nat.pow_pos hUmax_pos)
      have hMtot_pos : 1 ≤ Mtot := by
        rw [hMtot_eq]
        have he_ge1 : 1 ≤ e i_any := by
          have : (0 : ℝ) < (e i_any : ℝ) := he i_any ▸ hnd.budget_pos i_any
          exact_mod_cast this
        exact he_ge1.trans
          (Finset.single_le_sum (fun i _ => Nat.zero_le (e i)) (Finset.mem_univ i_any))
      have hnorm0_le : M.surplusSqNorm f0 ≤ (Mtot : ℝ) ^ 2 := by
        have hsum_e : ∑ i : I, M.budget i = (Mtot : ℝ) := by rw [hMtot_eq]; simp [M_tot, he]
        calc
          M.surplusSqNorm f0 = ∑ i : I, (M.surplus f0 i) ^ 2 := rfl
          _ ≤ ∑ i : I, (M.budget i) ^ 2 := Finset.sum_le_sum fun i _ => by
                have h1 : 0 ≤ M.surplus f0 i := sub_nonneg.2 (hbal0.1.2.2.2 i)
                have h2 : M.surplus f0 i ≤ M.budget i := by
                  have hnn : 0 ≤ ∑ g : G, f0 g i := Finset.sum_nonneg fun g _ => hbal0.1.1 g i
                  unfold surplus
                  linarith
                nlinarith
          _ ≤ (∑ i : I, M.budget i) ^ 2 :=
                Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => M.budget_nonneg i
          _ = (Mtot : ℝ) ^ 2 := by rw [hsum_e]
      have hpow_lt : (1 - 1 / ((m : ℝ) * (n : ℝ))) ^ T1 <
          1 / ((m * Δm ^ 4 * Mtot ^ 2 : ℕ) : ℝ) := by
        have hbase_nn : 0 ≤ 1 - 1 / ((m : ℝ) * (n : ℝ)) := by
          have h1 : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by exact_mod_cast hmn_pos
          rw [sub_nonneg, div_le_one (by linarith)]
          exact h1
        have hblock : (1 - 1 / ((m : ℝ) * (n : ℝ))) ^ (m * n) ≤ 1 / 2 := by
          have hmn_r : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by exact_mod_cast hmn_pos
          have hp0 : (0 : ℝ) ≤ 1 / ((m : ℝ) * (n : ℝ)) := by positivity
          have hp1 : 1 / ((m : ℝ) * (n : ℝ)) ≤ 1 := (div_le_one (by linarith)).2 hmn_r
          have h1 := Real.one_sub_pow_le_one_div_one_add_mul hp0 hp1 (m * n)
          have hmul : ((m * n : ℕ) : ℝ) * (1 / ((m : ℝ) * (n : ℝ))) = 1 := by
            push_cast
            exact mul_one_div_cancel (by linarith)
          rw [hmul] at h1
          linarith
        have hlt_pow : ((m * Δm ^ 4 * Mtot ^ 2 : ℕ) : ℝ) < (2 : ℝ) ^ K := by
          have hnat : m * Δm ^ 4 * Mtot ^ 2 < 2 ^ K :=
            Nat.lt_pow_succ_log_self (by decide : 1 < 2) _
          exact_mod_cast hnat
        have hN_pos : (0 : ℝ) < ((m * Δm ^ 4 * Mtot ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast
            Nat.mul_pos (Nat.mul_pos hm_pos (Nat.pow_pos hΔm_pos)) (Nat.pow_pos hMtot_pos)
        calc
          (1 - 1 / ((m : ℝ) * (n : ℝ))) ^ T1
            = ((1 - 1 / ((m : ℝ) * (n : ℝ))) ^ (m * n)) ^ K := by
                dsimp only [T1]; rw [pow_mul]
          _ ≤ (1 / 2 : ℝ) ^ K := pow_le_pow_left₀ (pow_nonneg hbase_nn _) hblock K
          _ = 1 / (2 : ℝ) ^ K := by rw [one_div_pow]
          _ < 1 / ((m * Δm ^ 4 * Mtot ^ 2 : ℕ) : ℝ) :=
              one_div_lt_one_div_of_lt hN_pos hlt_pow
      have hMtot_r_pos : (0 : ℝ) < (Mtot : ℝ) := Nat.cast_pos.2 hMtot_pos
      have hm_r_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm_pos
      have hΔm_r_pos : (0 : ℝ) < (Δm : ℝ) := Nat.cast_pos.2 hΔm_pos
      have hnorm1_lt : M.surplusSqNorm f1 < 1 / ((m : ℝ) * (Δm : ℝ) ^ 4) := by
        have h1 : (1 - 1 / ((m : ℝ) * (n : ℝ))) ^ T1 * M.surplusSqNorm f0 ≤
            (1 - 1 / ((m : ℝ) * (n : ℝ))) ^ T1 * (Mtot : ℝ) ^ 2 := by
          have hbase_nn : 0 ≤ 1 - 1 / ((m : ℝ) * (n : ℝ)) := by
            have h1 : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by exact_mod_cast hmn_pos
            rw [sub_nonneg, div_le_one (by linarith)]; exact h1
          exact mul_le_mul_of_nonneg_left hnorm0_le (pow_nonneg hbase_nn _)
        have h2 : (1 - 1 / ((m : ℝ) * (n : ℝ))) ^ T1 * (Mtot : ℝ) ^ 2 <
            (1 / ((m * Δm ^ 4 * Mtot ^ 2 : ℕ) : ℝ)) * (Mtot : ℝ) ^ 2 :=
          mul_lt_mul_of_pos_right hpow_lt (sq_pos_of_pos hMtot_r_pos)
        have h3 : (1 / ((m * Δm ^ 4 * Mtot ^ 2 : ℕ) : ℝ)) * (Mtot : ℝ) ^ 2 =
            1 / ((m : ℝ) * (Δm : ℝ) ^ 4) := by
          push_cast
          field_simp [hm_r_pos.ne', hΔm_r_pos.ne', hMtot_r_pos.ne']
        linarith
      have hsum_surp_lt : ∑ i : I, M.surplus f1 i < 1 / (Δm : ℝ) ^ 2 := by
        have hcs : (∑ i : I, M.surplus f1 i) ^ 2 ≤ (m : ℝ) * M.surplusSqNorm f1 := by
          simpa [m, surplusSqNorm] using
            sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset I)) (f := M.surplus f1)
        have hsq_lt : (∑ i : I, M.surplus f1 i) ^ 2 < (1 / (Δm : ℝ) ^ 2) ^ 2 := by
          have hmul : (m : ℝ) * M.surplusSqNorm f1 < (m : ℝ) * (1 / ((m : ℝ) * (Δm : ℝ) ^ 4)) :=
            mul_lt_mul_of_pos_left hnorm1_lt hm_r_pos
          have heq_r : (m : ℝ) * (1 / ((m : ℝ) * (Δm : ℝ) ^ 4)) = (1 / (Δm : ℝ) ^ 2) ^ 2 := by
            field_simp [hm_r_pos.ne', hΔm_r_pos.ne']
          linarith
        have hsum_nn : 0 ≤ ∑ i : I, M.surplus f1 i :=
          Finset.sum_nonneg fun i _ => sub_nonneg.2 (hbal1.1.2.2.2 i)
        nlinarith [div_pos one_pos (sq_pos_of_pos hΔm_r_pos)]
      have hgap_p1 : (∑ i : I, M.budget i) - ∑ g : G, p1 g < 1 / (Δm : ℝ) ^ 2 := by
        have hsum_eq := sum_surplus_eq (fun g => (hp1 g).le) hinv1
          (hbal1.isMaxEqualityFlow fun g => (hp1 g).le)
        have hsup_eq : ∑ g : G, p1 g * M.supply g = ∑ g : G, p1 g := by simp [hsup]
        linarith
      obtain ⟨hend_eq, hend_ph, hend_q⟩ :=
        dpsvLoop_endgame hnd hsup hu hu_le_Umax he horacle hgap_p1 n ∅ (fun _ => 0) p1 f1
          hp1 (fun _ => le_rfl) hinv1 hbal1 (fun _ h => absurd h (Finset.notMem_empty _))
          (by simp [n])
      rw [heval_eq, hres1, hcount_eq]
      dsimp only
      simp only [Finset.card_empty, Nat.sub_zero] at hend_ph
      have hq0' : (M.balancedFlowProgram M.dpsvInitPrice).countQueries oracle ≤ n := hq0
      have hq1' : (dpsvLoop M (T1 + n) M.dpsvInitPrice f0).countQueries oracle ≤
          2 * n ^ 2 * T1 + (dpsvLoop M n p1 f1).countQueries oracle := hq1
      have hend_q' : (dpsvLoop M n p1 f1).countQueries oracle ≤
          2 * n ^ 2 * ((dpsvLoop M n p1 f1).eval oracle).phases := hend_q
      have hmul : 2 * n ^ 2 * (((dpsvLoop M n p1 f1).eval oracle).phases + T1) =
          2 * n ^ 2 * T1 + 2 * n ^ 2 * ((dpsvLoop M n p1 f1).eval oracle).phases := by ring
      refine ⟨hend_eq, ?_, by omega⟩
      have hph_le : ((dpsvLoop M n p1 f1).eval oracle).phases + T1 ≤ T1 + n := by omega
      exact hph_le.trans (hlimit_eq ▸ hbound_mono)
  · have : IsEmpty G := ⟨fun g => hG ⟨g, Finset.mem_univ g⟩⟩
    have : IsEmpty I := ⟨fun i => let ⟨g, _⟩ := hnd.buyer_nonsatiated i; isEmptyElim g⟩
    have heval : res = ⟨0, 0, 0⟩ := by simp [res, dpsvProgram]
    have hcount : M.dpsvProgram.countQueries oracle = 0 := by simp [dpsvProgram]
    rw [heval, hcount]
    refine ⟨?_, Nat.zero_le _, by simp⟩
    exact (isEquilibrium_iff_bangPerBuck hnd.buyer_nonsatiated hnd.good_desired).2
      ⟨fun g => isEmptyElim g, fun i => isEmptyElim i, fun g => isEmptyElim g,
        fun i => isEmptyElim i, fun i => isEmptyElim i⟩

end MainAlgorithm

end Cslib.GameTheory.Market.LinearFisherMarket
