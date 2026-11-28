/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.Walrasian
public import CslibFrontier.Algorithms.Lean.Submodular.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Countable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Sequences

/-!
# Gross substitutes, the Kelso–Crawford ascending auction, and Walrasian equilibrium existence

While Example 11.14 of [BlumrosenNisan2007] (`not_exists_isWalrasianEquilibrium_noEquilibriumVal` in
`CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.Walrasian`) shows that complementary items
can rule out Walrasian equilibria, **gross-substitutes valuations** ([KelsoCrawford1982];
[GulStacchetti1999]; [BlumrosenNisan2007], §11.7.1, pp. 289–292) always admit both approximate and
exact Walrasian equilibria.

Building directly on `CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.Walrasian`, this
module formalizes §§11.4.1–11.4.2, §11.7.1, Example 11.32, and Exercise 11.6 of
[BlumrosenNisan2007]:

1. **Gross-substitutes valuations and canonical valuation families**
   (`IsGrossSubstitutes`, `additiveValuation`, `unitDemandValuation`, `downwardSlopingValuation`):
   Definition 11.28 (p. 290) requires that when item prices increase from `p` to `q ≥ p`, every
   demand bundle `A` at `p` admits a demand bundle `D` at `q` retaining all items in `A` whose price
   stayed constant (`p j = q j`). We prove that additive valuations (Definition 11.17, p. 280),
   nonnegative unit-demand valuations (Definition 11.17, p. 280), and downward-sloping symmetric
   valuations (Definition 11.19, p. 281) all satisfy `IsGrossSubstitutes`, and prove **Exercise
   11.6** (p. 299; [GulStacchetti1999]): every gross-substitutes valuation on a finite item set is
   **submodular** (`v (A ∪ B) + v (A ∩ B) ≤ v A + v B`).
2. **The Kelso–Crawford ascending item-price auction (Figure 11.3, Definition 11.29, Claim 11.31,
   Theorem 11.30, pp. 290–291):**
   starting from zero prices and empty bundles, each active round raises by `ε > 0` the prices of
   newly demanded items `D_i \ S_i` for an unsatisfied bidder `i` while maintaining the tentative
   demand-superset invariant (`AuctionState.IsValid`, Claim 11.31 and Footnote 5 on p. 291).
   Because `∑_j p_j` grows by at least `ε` per round and every item price stays bounded by
   `valuationBound v`, the auction (`kelsoCrawford`) halts in at most
   `⌊|M| * valuationBound v / ε⌋` stages at an `ε`-Walrasian equilibrium
   (`IsEpsWalrasianEquilibrium`, Definition 11.29).
3. **Printed welfare bound correction in Theorem 11.30 (p. 291):**
   every `ε`-Walrasian equilibrium achieves social welfare within `|M| * ε` (`m ε`) of the optimal
   allocation (`IsEpsWalrasianEquilibrium.welfare_le`). Note that [BlumrosenNisan2007], Theorem
   11.30 (p. 291) prints `n ε` (`|N| * ε`), conflating item-price surcharges with the bundle-price
   bound of Theorem 11.36 (p. 294): for `|N| = 1, |M| = 2, ε = 1` with additive value `3 / 4` per
   item, Figure 11.3 halts at round `0` with welfare gap `3 / 2 > 1 = |N| * ε` (checked in
   `CslibFrontierTests.GameTheory.KelsoCrawford`). When bidders have at-most-one-item demand
   (`∀ i, (b.bundle i).card ≤ 1`), the `|N| * ε` bound holds
   (`IsEpsWalrasianEquilibrium.welfare_le_of_card_le_one`).
4. **Kelso–Crawford / Gul–Stacchetti exact Walrasian equilibrium existence and zero LPR integrality
   gap (`exists_isWalrasianEquilibrium_of_isGrossSubstitutes`,
   `exists_isIntegral_isLPROptimal_of_isGrossSubstitutes`):**
   passing to a convergent subsequence of `kelsoCrawford` outputs at `ε_k = 1 / (k + 1)` over the
   finite set `Allocation N M` and compact cube `[0, valuationBound v]^M` yields an **exact**
   Walrasian equilibrium `(p, a)` for any finite profile of real-valued gross-substitutes
   valuations (requiring neither monotonicity nor integrality), and hence—via Corollary 11.16—an
   integral (`0–1`) optimal solution to `LPR` whenever `∀ i, 0 ≤ v i ∅`.
5. **Demand-reduction manipulation (`demandReductionVal`, Example 11.32, p. 292):**
   even when all valuations are gross substitutes, a bidder can strictly increase their payoff
   (from at most `2` in *every* truthful Walrasian equilibrium to `5` under a misreported
   unit-demand valuation) by shading multi-item demand.

## Main definitions

* `Cslib.GameTheory.CombinatorialAuction.IsGrossSubstitutes`: gross-substitutes property
  ([BlumrosenNisan2007], Definition 11.28, p. 290; [KelsoCrawford1982]).
* `Cslib.GameTheory.CombinatorialAuction.additiveValuation`,
  `Cslib.GameTheory.CombinatorialAuction.unitDemandValuation`,
  `Cslib.GameTheory.CombinatorialAuction.downwardSlopingValuation`: canonical substitutes valuation
  classes ([BlumrosenNisan2007], Definitions 11.17 and 11.19, pp. 280–281).
* `Cslib.GameTheory.CombinatorialAuction.personalizedPrice`,
  `Cslib.GameTheory.CombinatorialAuction.IsEpsWalrasianEquilibrium`: bidder-specific effective item
  prices and `ε`-Walrasian equilibrium ([BlumrosenNisan2007], Figure 11.3 and Definition 11.29,
  pp. 290–291).
* `Cslib.GameTheory.CombinatorialAuction.AuctionState`,
  `Cslib.GameTheory.CombinatorialAuction.kelsoCrawford`: state, step invariant, and finite-fuel run
  of the Figure 11.3 Kelso–Crawford ascending item-price auction.
* `Cslib.GameTheory.CombinatorialAuction.demandReductionVal`: the two-bidder, two-item substitutes
  profile of Example 11.32 (p. 292).

## Main results

* `Cslib.GameTheory.CombinatorialAuction.isGrossSubstitutes_additiveValuation`,
  `Cslib.GameTheory.CombinatorialAuction.isGrossSubstitutes_unitDemandValuation`,
  `Cslib.GameTheory.CombinatorialAuction.isGrossSubstitutes_downwardSlopingValuation`:
  gross-substitutes instances.
* `Cslib.GameTheory.CombinatorialAuction.IsGrossSubstitutes.submodular`: **Exercise 11.6** (p. 299;
  [GulStacchetti1999]) — every gross-substitutes valuation is submodular.
* `Cslib.GameTheory.CombinatorialAuction.kelsoCrawford_isEpsWalrasianEquilibrium`,
  `Cslib.GameTheory.CombinatorialAuction.IsEpsWalrasianEquilibrium.welfare_le`: **Theorem 11.30**
  and **Claim 11.31** (p. 291), with corrected `|M| * ε` welfare guarantee.
* `Cslib.GameTheory.CombinatorialAuction.exists_isWalrasianEquilibrium_of_isGrossSubstitutes`,
  `Cslib.GameTheory.CombinatorialAuction.exists_isIntegral_isLPROptimal_of_isGrossSubstitutes`:
  **Kelso–Crawford / Gul–Stacchetti Walrasian equilibrium existence** and zero `LPR` integrality gap
  for real-valued gross-substitutes valuations.
* `Cslib.GameTheory.CombinatorialAuction.demandReduction_manipulation`: **Example 11.32** (p. 292)
  strategic demand reduction under gross substitutes.

## References

* [L. Blumrosen and N. Nisan, *Combinatorial Auctions*][BlumrosenNisan2007], Chapter 11,
  §§11.4.1–11.4.2, §11.7.1, §11.8, and Exercise 11.6, pp. 280–281, 289–292, 295–299.
* [A. S. Kelso and V. P. Crawford, *Job matching, coalition formation, and gross
  substitutes*][KelsoCrawford1982] (primary PDF unverified; cited via [BlumrosenNisan2007], §11.8,
  p. 295).
* [F. Gul and E. Stacchetti, *Walrasian equilibrium with gross substitutes*][GulStacchetti1999]
  (primary PDF unverified; cited via [BlumrosenNisan2007], §11.8, pp. 295–296).
-/

public section

namespace Cslib.GameTheory.CombinatorialAuction

open Finset
open scoped Topology

/-! ### Gross substitutes and canonical valuation families -/

section Substitutes

/-- A valuation `v : Finset M → ℝ` satisfies the **gross-substitutes** property
([BlumrosenNisan2007], Definition 11.28, p. 290; [KelsoCrawford1982]) if whenever item prices rise
coordinate-wise from `p` to `q` (`∀ j, p j ≤ q j`), for every demand bundle `A` at `p` there exists
a demand bundle `D` at `q` containing all items `j ∈ A` whose price remained unchanged
(`p j = q j`). -/
@[expose] def IsGrossSubstitutes {M : Type*} (v : Finset M → ℝ) : Prop :=
  ∀ ⦃p q : M → ℝ⦄, (∀ j, p j ≤ q j) → ∀ ⦃A : Finset M⦄, IsDemand v p A →
    ∃ D : Finset M, IsDemand v q D ∧ ∀ j ∈ A, p j = q j → j ∈ D

/-- On a finite item set `M`, for any valuation `v`, prices `q`, and target subset `S₀`, there
exists a demand bundle `D₀` at `q` maximizing `(D₀ ∩ S₀).card` among all demand bundles at `q`. -/
private theorem exists_isDemand_max_inter {M : Type*} [Finite M] [DecidableEq M]
    (v : Finset M → ℝ) (q : M → ℝ) (S₀ : Finset M) :
    ∃ D₀ : Finset M, IsDemand v q D₀ ∧
      ∀ D : Finset M, IsDemand v q D → (D ∩ S₀).card ≤ (D₀ ∩ S₀).card := by
  classical
  have := Fintype.ofFinite M
  obtain ⟨T, hT⟩ := exists_isDemand v q
  let cands : Finset (Finset M) := univ.filter fun D => IsDemand v q D
  have hcands_ne : cands.Nonempty := ⟨T, mem_filter.2 ⟨mem_univ T, hT⟩⟩
  obtain ⟨D₀, hD₀_mem, hD₀_max⟩ := exists_max_image cands (fun D => (D ∩ S₀).card) hcands_ne
  exact ⟨D₀, (mem_filter.1 hD₀_mem).2, fun D hD => hD₀_max D (mem_filter.2 ⟨mem_univ D, hD⟩)⟩

/-- Marginal-price upper bound at a demanded item: if `IsDemand v p A` and `j ∈ A`, then
`p j ≤ v A - v (A.erase j)`. -/
theorem IsDemand.price_le_sub_erase {M : Type*} [DecidableEq M] {v : Finset M → ℝ}
    {p : M → ℝ} {A : Finset M} (hA : IsDemand v p A) {j : M} (hj : j ∈ A) :
    p j ≤ v A - v (A.erase j) := by
  linarith [hA (A.erase j), add_sum_erase A p hj]

/-- Marginal-price lower bound outside a demanded bundle: if `IsDemand v p A` and `j ∉ A`, then
`v (insert j A) - v A ≤ p j`. -/
theorem IsDemand.sub_insert_le_price {M : Type*} [DecidableEq M] {v : Finset M → ℝ}
    {p : M → ℝ} {A : Finset M} (hA : IsDemand v p A) {j : M} (hj : j ∉ A) :
    v (insert j A) - v A ≤ p j := by
  linarith [hA (insert j A), sum_insert (f := p) hj]

/-- **Additive valuation** `S ↦ ∑ j ∈ S, w j` ([BlumrosenNisan2007], Definition 11.17, p. 280),
reducible alias of `Cslib.Algorithms.Lean.Submodular.modularSum`. -/
abbrev additiveValuation {M : Type*} (w : M → ℝ) : Finset M → ℝ :=
  Cslib.Algorithms.Lean.Submodular.modularSum w

/-- Every additive valuation satisfies `IsGrossSubstitutes` ([BlumrosenNisan2007], §11.7.1,
p. 291). -/
theorem isGrossSubstitutes_additiveValuation {M : Type*} [Finite M] (w : M → ℝ) :
    IsGrossSubstitutes (additiveValuation w) := by
  classical
  have := Fintype.ofFinite M
  intro p q hpq A hA
  have hA_nonneg : ∀ j ∈ A, 0 ≤ w j - p j := by
    intro j hj
    have h := hA.price_le_sub_erase hj
    have hsub : additiveValuation w A - additiveValuation w (A.erase j) = w j := by
      simp only [Cslib.Algorithms.Lean.Submodular.modularSum]
      rw [← add_sum_erase _ _ hj]
      ring
    linarith
  let D : Finset M := univ.filter fun j => (j ∈ A ∧ p j = q j) ∨ 0 < w j - q j
  have hD_pos : ∀ j ∈ D, 0 ≤ w j - q j := by
    intro j hj
    rcases (mem_filter.1 hj).2 with ⟨hjA, hpq_eq⟩ | hpos
    · exact hpq_eq ▸ hA_nonneg j hjA
    · exact hpos.le
  have hD_nonpos : ∀ j, j ∉ D → w j - q j ≤ 0 := fun j hj =>
    not_lt.1 fun h => hj (mem_filter.2 ⟨mem_univ j, Or.inr h⟩)
  refine ⟨D, fun S => ?_, fun j hjA hpq_eq => mem_filter.2 ⟨mem_univ j, Or.inl ⟨hjA, hpq_eq⟩⟩⟩
  simp only [Cslib.Algorithms.Lean.Submodular.modularSum]
  rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_inter_add_sum_sdiff S D,
    ← sum_inter_add_sum_sdiff D S, inter_comm D S]
  have hsdiff_le : ∑ j ∈ S \ D, (w j - q j) ≤ 0 :=
    sum_nonpos fun j hj => hD_nonpos j (mem_sdiff.1 hj).2
  have hds_ge : 0 ≤ ∑ j ∈ D \ S, (w j - q j) :=
    sum_nonneg fun j hj => hD_pos j (mem_sdiff.1 hj).1
  linarith

/-- **Unit-demand valuation** `S ↦ S.fold max 0 w`, equal to `0` on `∅` and `max_{j ∈ S} w j` on
nonempty bundles when `w ≥ 0` ([BlumrosenNisan2007], Definitions 11.1 and 11.17, pp. 268, 280). -/
@[expose] def unitDemandValuation {M : Type*} (w : M → ℝ) (S : Finset M) : ℝ :=
  S.fold max 0 w

@[simp] theorem unitDemandValuation_empty {M : Type*} (w : M → ℝ) :
    unitDemandValuation w ∅ = 0 := by rfl

@[simp] theorem unitDemandValuation_insert {M : Type*} [DecidableEq M] (w : M → ℝ)
    (j : M) (S : Finset M) :
    unitDemandValuation w (insert j S) = max (w j) (unitDemandValuation w S) := by
  simp [unitDemandValuation]

@[simp] theorem unitDemandValuation_singleton {M : Type*} (w : M → ℝ) (j : M) :
    unitDemandValuation w {j} = max (w j) 0 := by
  simp [unitDemandValuation]

theorem le_unitDemandValuation {M : Type*} (w : M → ℝ) {S : Finset M} {j : M} (hj : j ∈ S) :
    w j ≤ unitDemandValuation w S := by
  classical
  induction S using Finset.induction with
  | empty => exact (notMem_empty j hj).elim
  | insert a T _ ih =>
    rw [unitDemandValuation_insert]
    rcases mem_insert.1 hj with rfl | hjT
    · exact le_max_left _ _
    · exact (ih hjT).trans (le_max_right _ _)

theorem unitDemandValuation_nonneg {M : Type*} (w : M → ℝ) (S : Finset M) :
    0 ≤ unitDemandValuation w S := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a T _ ih =>
    rw [unitDemandValuation_insert]
    exact ih.trans (le_max_right _ _)

theorem unitDemandValuation_monotone {M : Type*} (w : M → ℝ) :
    Monotone (unitDemandValuation w) := by
  classical
  intro S T hST
  induction S using Finset.induction with
  | empty => exact unitDemandValuation_nonneg w T
  | insert a R _ ih =>
    rw [unitDemandValuation_insert]
    exact max_le (le_unitDemandValuation w (hST (mem_insert_self a R)))
      (ih ((subset_insert a R).trans hST))

/-- On a nonempty bundle `S`, a nonnegative unit-demand valuation `unitDemandValuation w S` attains
its value at some item `j ∈ S`. -/
theorem exists_mem_unitDemandValuation_eq {M : Type*} {w : M → ℝ} (hw : ∀ j, 0 ≤ w j)
    {S : Finset M} (hS : S.Nonempty) :
    ∃ j ∈ S, unitDemandValuation w S = w j := by
  classical
  induction S using Finset.induction with
  | empty => exact (not_nonempty_empty hS).elim
  | insert a T _ ih =>
    rw [unitDemandValuation_insert]
    rcases T.eq_empty_or_nonempty with rfl | hT
    · simp only [unitDemandValuation_empty, max_eq_left (hw a)]
      exact ⟨a, mem_insert_self a ∅, rfl⟩
    · obtain ⟨b, hbT, hb_eq⟩ := ih hT
      rw [hb_eq]
      rcases le_total (w b) (w a) with hba | hab
      · exact ⟨a, mem_insert_self a T, max_eq_left hba⟩
      · exact ⟨b, mem_insert_of_mem hbT, max_eq_right hab⟩

private theorem card_inter_lt_of_subset_of_mem {M : Type*} [DecidableEq M]
    {D₀ D' S₀ : Finset M} {j₀ : M} (hj₀S₀ : j₀ ∈ S₀) (hj₀D₀ : j₀ ∉ D₀)
    (hj₀' : j₀ ∈ D') (hsub : ∀ x ∈ D₀ ∩ S₀, x ∈ D') :
    (D₀ ∩ S₀).card < (D' ∩ S₀).card := by
  refine card_lt_card ⟨fun x hx => mem_inter.2 ⟨hsub x hx, (mem_inter.1 hx).2⟩, ?_⟩
  intro hrev
  exact hj₀D₀ (mem_inter.1 (hrev (mem_inter.2 ⟨hj₀', hj₀S₀⟩))).1

/-- Every nonnegative unit-demand valuation satisfies `IsGrossSubstitutes`
([BlumrosenNisan2007], §11.7.1, p. 291). -/
theorem isGrossSubstitutes_unitDemandValuation {M : Type*} [Finite M] {w : M → ℝ}
    (hw : ∀ j, 0 ≤ w j) : IsGrossSubstitutes (unitDemandValuation w) := by
  classical
  intro p q hpq A hA
  let S₀ : Finset M := A.filter fun j => p j = q j
  obtain ⟨D₀, hD₀, hD₀_max⟩ := exists_isDemand_max_inter (unitDemandValuation w) q S₀
  refine ⟨D₀, hD₀, fun j₀ hj₀A hpq₀ => ?_⟩
  have hj₀S₀ : j₀ ∈ S₀ := mem_filter.2 ⟨hj₀A, hpq₀⟩
  by_contra hj₀D₀
  rcases le_or_gt (q j₀) 0 with hq_nonpos | hq_pos
  · -- Nonpositive price `q j₀ ≤ 0`: inserting `j₀` into `D₀` preserves optimality at `q`.
    let D' := insert j₀ D₀
    have hD'_dem : IsDemand (unitDemandValuation w) q D' := by
      intro S
      rw [sum_insert hj₀D₀]
      linarith [hD₀ S, unitDemandValuation_monotone w (subset_insert j₀ D₀)]
    exact (card_inter_lt_of_subset_of_mem hj₀S₀ hj₀D₀ (mem_insert_self j₀ D₀)
      fun x hx => mem_insert_of_mem (mem_inter.1 hx).1).not_ge (hD₀_max D' hD'_dem)
  · -- Positive price `0 < p j₀ = q j₀`: `j₀` uniquely attains `unitDemandValuation w A = w j₀`.
    have hp_pos : 0 < p j₀ := hpq₀.symm ▸ hq_pos
    have herase_le : unitDemandValuation w (A.erase j₀) ≤ unitDemandValuation w A - p j₀ := by
      linarith [hA.price_le_sub_erase hj₀A]
    have hvA_eq : unitDemandValuation w A = w j₀ := by
      have hmax : unitDemandValuation w A = max (w j₀) (unitDemandValuation w (A.erase j₀)) := by
        rw [← unitDemandValuation_insert, insert_erase hj₀A]
      rcases max_choice (w j₀) (unitDemandValuation w (A.erase j₀)) with h1 | h2
      · exact hmax.trans h1
      · linarith [hmax.trans h2]
    rcases D₀.eq_empty_or_nonempty with rfl | hD₀_ne
    · -- `D₀ = ∅`: `{j₀}` achieves nonnegative utility `w j₀ - q j₀ ≥ v(A.erase j₀) ≥ 0`.
      have hsingle_dem : IsDemand (unitDemandValuation w) q {j₀} := by
        intro S
        have hv_erase_nn : 0 ≤ unitDemandValuation w (A.erase j₀) :=
          unitDemandValuation_nonneg w _
        have hval : unitDemandValuation w {j₀} = w j₀ := by
          rw [unitDemandValuation_singleton, max_eq_left (hw j₀)]
        have h0 := hD₀ S
        simp only [unitDemandValuation_empty, sum_empty, sub_zero] at h0
        rw [hval, sum_singleton, ← hpq₀]
        linarith
      exact (card_inter_lt_of_subset_of_mem hj₀S₀ hj₀D₀ (mem_singleton_self j₀)
        fun _ hx => (notMem_empty _ (mem_inter.1 hx).1).elim).not_ge (hD₀_max {j₀} hsingle_dem)
    · obtain ⟨m, hmD₀, hm_eq⟩ := exists_mem_unitDemandValuation_eq hw hD₀_ne
      by_cases hmA : m ∈ A
      · -- `m ∈ A` with `m ≠ j₀` (`j₀ ∉ D₀`): `w m ≤ v(A.erase j₀) ≤ w j₀ - q j₀`, so `insert j₀ D₀`
        -- pays for `q j₀` directly!
        have hmj₀ : m ≠ j₀ := fun h => hj₀D₀ (h ▸ hmD₀)
        have hwm_le : w m ≤ w j₀ - q j₀ := by
          have := le_unitDemandValuation w (mem_erase.2 ⟨hmj₀, hmA⟩)
          linarith
        let D' := insert j₀ D₀
        have hD'_dem : IsDemand (unitDemandValuation w) q D' := by
          intro S
          have hvD' : unitDemandValuation w D' = w j₀ := by
            rw [unitDemandValuation_insert, hm_eq, max_eq_left (by linarith)]
          rw [hvD', sum_insert hj₀D₀]
          linarith [hD₀ S, hm_eq]
        exact (card_inter_lt_of_subset_of_mem hj₀S₀ hj₀D₀ (mem_insert_self j₀ D₀)
          fun x hx => mem_insert_of_mem (mem_inter.1 hx).1).not_ge (hD₀_max D' hD'_dem)
      · -- `m ∉ A`: swapping `m` for `j₀` in `A` at `p` yields `w m - q m ≤ w j₀ - q j₀`, so
        -- swapping `m` out for `j₀` in `D₀` preserves optimality at `q` and grows `D₀ ∩ S₀`!
        have hm_not_erase : m ∉ A.erase j₀ := fun h => hmA (mem_of_mem_erase h)
        have hswap_A := hA (insert m (A.erase j₀))
        have hwm_le_ins : w m ≤ unitDemandValuation w (insert m (A.erase j₀)) :=
          le_unitDemandValuation w (mem_insert_self m _)
        rw [sum_insert hm_not_erase, hvA_eq, ← add_sum_erase A p hj₀A] at hswap_A
        have hwm_pm : w m - p m ≤ w j₀ - p j₀ := by linarith
        have hwm_qm : w m - q m ≤ w j₀ - q j₀ := by linarith [hpq m]
        let D' := insert j₀ (D₀.erase m)
        have hj₀_not_erase : j₀ ∉ D₀.erase m := fun h => hj₀D₀ (mem_of_mem_erase h)
        have hD'_dem : IsDemand (unitDemandValuation w) q D' := by
          intro S
          have hwj₀_le : w j₀ ≤ unitDemandValuation w D' :=
            le_unitDemandValuation w (mem_insert_self j₀ _)
          rw [sum_insert hj₀_not_erase]
          linarith [hD₀ S, hm_eq, add_sum_erase D₀ q hmD₀]
        have hsub : ∀ x ∈ D₀ ∩ S₀, x ∈ D' := fun x hx =>
          have hxA : x ∈ A := (mem_filter.1 (mem_inter.1 hx).2).1
          mem_insert_of_mem (mem_erase.2 ⟨fun h => hmA (h ▸ hxA), (mem_inter.1 hx).1⟩)
        exact (card_inter_lt_of_subset_of_mem hj₀S₀ hj₀D₀ (mem_insert_self j₀ _) hsub).not_ge
          (hD₀_max D' hD'_dem)

/-- **Downward-sloping symmetric valuation** `S ↦ ∑ k ∈ range S.card, w k`
([BlumrosenNisan2007], Definition 11.19, p. 281, indexing marginal values `0 .. |S| - 1`). -/
@[expose] def downwardSlopingValuation {M : Type*} (w : ℕ → ℝ) (S : Finset M) : ℝ :=
  ∑ k ∈ range S.card, w k

@[simp] theorem downwardSlopingValuation_empty {M : Type*} (w : ℕ → ℝ) :
    downwardSlopingValuation (M := M) w ∅ = 0 := by
  simp [downwardSlopingValuation]

/-- Every downward-sloping symmetric valuation (`Antitone w`) satisfies `IsGrossSubstitutes`
([BlumrosenNisan2007], §11.7.1, p. 291). -/
theorem isGrossSubstitutes_downwardSlopingValuation {M : Type*} [Finite M] {w : ℕ → ℝ}
    (hw : Antitone w) : IsGrossSubstitutes (downwardSlopingValuation (M := M) w) := by
  classical
  intro p q hpq A hA
  let S₀ : Finset M := A.filter fun j => p j = q j
  obtain ⟨D₀, hD₀, hD₀_max⟩ := exists_isDemand_max_inter (downwardSlopingValuation w) q S₀
  refine ⟨D₀, hD₀, fun j₀ hj₀A hpq₀ => ?_⟩
  have hj₀S₀ : j₀ ∈ S₀ := mem_filter.2 ⟨hj₀A, hpq₀⟩
  by_contra hj₀D₀
  by_cases hsubA : D₀ ⊆ A
  · -- `D₀ ⊆ A` and `j₀ ∈ A \ D₀`, so `D₀.card ≤ A.card - 1` and `q j₀ = p j₀ ≤ w (A.card - 1) ≤
    -- w D₀.card`: inserting `j₀` into `D₀` preserves optimality at `q`!
    have hlt_card : D₀.card < A.card := card_lt_card ⟨hsubA, fun hrev => hj₀D₀ (hrev hj₀A)⟩
    have hcard_pos : 1 ≤ A.card := by omega
    have hpj₀_le : p j₀ ≤ w (A.card - 1) := by
      have h := hA.price_le_sub_erase hj₀A
      have hcard_er : (A.erase j₀).card = A.card - 1 := card_erase_of_mem hj₀A
      have hv_diff : downwardSlopingValuation w A =
          downwardSlopingValuation w (A.erase j₀) + w (A.card - 1) := by
        unfold downwardSlopingValuation
        rw [hcard_er, ← sum_range_succ, Nat.sub_add_cancel hcard_pos]
      linarith
    have hle_idx : D₀.card ≤ A.card - 1 := Nat.le_sub_one_of_lt hlt_card
    have hqj₀_le : q j₀ ≤ w D₀.card := by linarith [hw hle_idx]
    let D' := insert j₀ D₀
    have hD'_dem : IsDemand (downwardSlopingValuation w) q D' := by
      intro S
      have hvD' : downwardSlopingValuation w D' = downwardSlopingValuation w D₀ + w D₀.card := by
        unfold downwardSlopingValuation
        rw [card_insert_of_notMem hj₀D₀, sum_range_succ]
      rw [hvD', sum_insert hj₀D₀]
      linarith [hD₀ S]
    exact (card_inter_lt_of_subset_of_mem hj₀S₀ hj₀D₀ (mem_insert_self j₀ D₀)
      fun x hx => mem_insert_of_mem (mem_inter.1 hx).1).not_ge (hD₀_max D' hD'_dem)
  · -- Pick `b ∈ D₀ \ A`: swapping `j₀ ∈ A` with `b ∉ A` preserves cardinality and gives
    -- `p j₀ ≤ p b`, hence `q j₀ = p j₀ ≤ p b ≤ q b`!
    obtain ⟨b, hbD₀, hbA⟩ := not_subset.1 hsubA
    have hb_not_er : b ∉ A.erase j₀ := fun h => hbA (mem_of_mem_erase h)
    have hcard_swapA : (insert b (A.erase j₀)).card = A.card := by
      rw [card_insert_of_notMem hb_not_er, card_erase_of_mem hj₀A,
        Nat.sub_add_cancel (Finset.card_pos.2 ⟨j₀, hj₀A⟩)]
    have hswapA := hA (insert b (A.erase j₀))
    have hv_eqA : downwardSlopingValuation w (insert b (A.erase j₀)) =
        downwardSlopingValuation w A := by
      simp [downwardSlopingValuation, hcard_swapA]
    rw [hv_eqA, sum_insert hb_not_er, ← add_sum_erase A p hj₀A] at hswapA
    have hqj₀_le_qb : q j₀ ≤ q b := by linarith [hpq b]
    let D' := insert j₀ (D₀.erase b)
    have hj₀_not_er : j₀ ∉ D₀.erase b := fun h => hj₀D₀ (mem_of_mem_erase h)
    have hcard_swapD : D'.card = D₀.card := by
      rw [card_insert_of_notMem hj₀_not_er, card_erase_of_mem hbD₀,
        Nat.sub_add_cancel (Finset.card_pos.2 ⟨b, hbD₀⟩)]
    have hD'_dem : IsDemand (downwardSlopingValuation w) q D' := by
      intro S
      have hv_eqD : downwardSlopingValuation w D' = downwardSlopingValuation w D₀ := by
        simp [downwardSlopingValuation, hcard_swapD]
      rw [hv_eqD, sum_insert hj₀_not_er]
      linarith [hD₀ S, add_sum_erase D₀ q hbD₀]
    have hsub : ∀ x ∈ D₀ ∩ S₀, x ∈ D' := fun x hx =>
      have hxA : x ∈ A := (mem_filter.1 (mem_inter.1 hx).2).1
      mem_insert_of_mem (mem_erase.2 ⟨fun h => hbA (h ▸ hxA), (mem_inter.1 hx).1⟩)
    exact (card_inter_lt_of_subset_of_mem hj₀S₀ hj₀D₀ (mem_insert_self j₀ _) hsub).not_ge
      (hD₀_max D' hD'_dem)

/-! ### Exercise 11.6 (Gul–Stacchetti): every gross-substitutes valuation is submodular -/

/-- Two-item marginal diminishing returns for gross-substitutes valuations ([GulStacchetti1999];
[BlumrosenNisan2007], Exercise 11.6, p. 299). -/
theorem IsGrossSubstitutes.insert_insert_add_le {M : Type*} [Finite M] [DecidableEq M]
    {v : Finset M → ℝ} (hgs : IsGrossSubstitutes v)
    (S : Finset M) {x y : M} (hxy : x ≠ y) (hxS : x ∉ S) (hyS : y ∉ S) :
    v (insert x (insert y S)) + v S ≤ v (insert x S) + v (insert y S) := by
  have := Fintype.ofFinite M
  by_contra hlt
  push Not at hlt
  set Sx := insert x S
  set Sy := insert y S
  set Sxy := insert x (insert y S)
  set δ : ℝ := v Sxy + v S - (v Sx + v Sy)
  have hδ_pos : 0 < δ := sub_pos.2 hlt
  set V : ℝ := ∑ T : Finset M, |v T|
  have hV_nn : 0 ≤ V := sum_nonneg fun _ _ => abs_nonneg _
  have habs_v : ∀ B : Finset M, |v B| ≤ V := fun B =>
    single_le_sum (fun T _ => abs_nonneg (v T)) (mem_univ B)
  have hlo : ∀ B : Finset M, -V ≤ v B := fun B => neg_le_of_abs_le (habs_v B)
  have hhi : ∀ B : Finset M, v B ≤ V := fun B => le_of_abs_le (habs_v B)
  set K : ℝ := 20 * V + 1
  let px : ℝ := v Sx - v S + δ / 2
  let py : ℝ := v Sy - v S + δ / 2
  let p : M → ℝ := fun j =>
    if j ∈ S then -K else if j = x then px else if j = y then py else K
  let q : M → ℝ := fun j =>
    if j ∈ S then -K else if j = x then px else if j = y then py + δ else K
  have hpq : ∀ j : M, p j ≤ q j := by
    intro j
    dsimp only [p, q]
    split_ifs <;> linarith
  have hδ_le : δ ≤ 4 * V := by linarith [hhi Sxy, hhi S, hlo Sx, hlo Sy]
  have hpx_abs : |px| ≤ 4 * V := by
    dsimp only [px]
    rw [abs_le]
    constructor <;> linarith [hlo Sx, hhi Sx, hlo S, hhi S]
  have hpy_abs : |py| ≤ 4 * V := by
    dsimp only [py]
    rw [abs_le]
    constructor <;> linarith [hlo Sy, hhi Sy, hlo S, hhi S]
  -- Penalty lemma: for both `r = p` and `r = q`, any bundle `B` violating `S ⊆ B ∧ B ⊆ Sxy`
  -- is strictly dominated by `S`.
  have houtside : ∀ (r : M → ℝ),
      (∀ j ∈ S, r j = -K) → (∀ j, j ∉ Sxy → r j = K) →
      |r x| ≤ 4 * V → |r y| ≤ 8 * V →
      ∀ B : Finset M, ¬ (S ⊆ B ∧ B ⊆ Sxy) →
        v B - ∑ j ∈ B, r j < v S - ∑ j ∈ S, r j := by
    intro r hrS hrOut hrx hry B hnot
    have hsum_S : ∑ j ∈ S, r j = -(S.card : ℝ) * K := by
      rw [sum_congr rfl fun j hj => hrS j hj, sum_const, nsmul_eq_mul]
      ring
    -- Partition `B` into `B ∩ S`, `B ∩ {x, y}`, and `B \ Sxy`.
    have hB_split1 : B = (B \ S) ∪ (B ∩ S) := (sdiff_union_inter B S).symm
    let Bmid := (B \ S) ∩ {x, y}
    let Bout := (B \ S) \ {x, y}
    have hB_split2 : B \ S = Bout ∪ Bmid := (sdiff_union_inter (B \ S) {x, y}).symm
    have hBout_out : ∀ j ∈ Bout, j ∉ Sxy := by
      intro j hj hmem
      rcases mem_insert.1 hmem with rfl | hmem'
      · exact (mem_sdiff.1 hj).2 (by simp)
      · rcases mem_insert.1 hmem' with rfl | hjS
        · exact (mem_sdiff.1 hj).2 (by simp)
        · exact (mem_sdiff.1 (mem_sdiff.1 hj).1).2 hjS
    have hsum_BS : ∑ j ∈ B ∩ S, r j = -((B ∩ S).card : ℝ) * K := by
      rw [sum_congr rfl fun j hj => hrS j (mem_inter.1 hj).2, sum_const, nsmul_eq_mul]
      ring
    have hsum_Bout : ∑ j ∈ Bout, r j = (Bout.card : ℝ) * K := by
      rw [sum_congr rfl fun j hj => hrOut j (hBout_out j hj), sum_const, nsmul_eq_mul]
    have hsum_Bmid : -12 * V ≤ ∑ j ∈ Bmid, r j := by
      have hsub_xy : Bmid ⊆ ({x, y} : Finset M) := inter_subset_right
      calc
        -12 * V ≤ -(∑ j ∈ ({x, y} : Finset M), |r j|) := by
          rw [sum_pair hxy]
          linarith
        _ ≤ -(∑ j ∈ Bmid, |r j|) :=
          neg_le_neg (sum_le_sum_of_subset_of_nonneg hsub_xy fun j _ _ => abs_nonneg (r j))
        _ = ∑ j ∈ Bmid, -|r j| := (sum_neg_distrib _).symm
        _ ≤ ∑ j ∈ Bmid, r j := sum_le_sum fun j _ => neg_abs_le (r j)
    have hsum_B : ∑ j ∈ B, r j =
        (∑ j ∈ Bout, r j + ∑ j ∈ Bmid, r j) + ∑ j ∈ B ∩ S, r j := by
      conv_lhs => rw [hB_split1]
      rw [sum_union (disjoint_sdiff_inter B S)]
      congr 1
      rw [hB_split2, sum_union (disjoint_sdiff_inter (B \ S) {x, y})]
    have hcard_BS : (B ∩ S).card ≤ S.card := card_le_card inter_subset_right
    have hpen_ge_one : 1 ≤ (S.card - (B ∩ S).card) + Bout.card := by
      by_contra hzero
      have hSB : S ⊆ B := inter_eq_right.1 (eq_of_subset_of_card_le inter_subset_right (by omega))
      have hBout_empty : Bout = ∅ := card_eq_zero.1 (by omega)
      have hBSxy : B ⊆ Sxy := by
        intro j hj
        by_cases hjS : j ∈ S
        · exact mem_insert_of_mem (mem_insert_of_mem hjS)
        · have hjBS : j ∈ B \ S := mem_sdiff.2 ⟨hj, hjS⟩
          rw [hB_split2, hBout_empty, empty_union] at hjBS
          rcases mem_insert.1 (mem_inter.1 hjBS).2 with hjx | hjy
          · exact hjx ▸ mem_insert_self x _
          · exact mem_singleton.1 hjy ▸ mem_insert_of_mem (mem_insert_self y S)
      exact hnot ⟨hSB, hBSxy⟩
    have hK_pos : 0 < K := by positivity
    have hpen_real : K ≤ ((S.card : ℝ) - ((B ∩ S).card : ℝ) + (Bout.card : ℝ)) * K := by
      refine le_mul_of_one_le_left hK_pos.le ?_
      rw [← Nat.cast_sub hcard_BS, ← Nat.cast_add]
      exact_mod_cast hpen_ge_one
    have hv_diff : -2 * V ≤ v S - v B := by linarith [hlo S, hhi B]
    rw [hsum_B, hsum_BS, hsum_Bout, hsum_S]
    dsimp only [K] at hpen_real ⊢
    linarith
  -- Evaluate the 4 candidate subsets `B` satisfying `S ⊆ B ⊆ Sxy`!
  have hfour : ∀ B : Finset M, S ⊆ B → B ⊆ Sxy → B = S ∨ B = Sx ∨ B = Sy ∨ B = Sxy := by
    intro B hSB hBSxy
    have hSB' : S ⊆ B.erase x := fun j hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hxS, hSB hj⟩
    have hC : B.erase x = S ∨ B.erase x = insert y S := by
      by_cases hy : y ∈ B.erase x
      · exact Or.inr ((subset_insert_iff.1 hBSxy).antisymm (insert_subset hy hSB'))
      · exact Or.inl
          (((subset_insert_iff_of_notMem hy).1 (subset_insert_iff.1 hBSxy)).antisymm hSB')
    by_cases hxB : x ∈ B
    · rw [← insert_erase hxB]
      rcases hC with hC | hC <;> rw [hC]
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rw [← erase_eq_of_notMem hxB]
      rcases hC with hC | hC <;> rw [hC]
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
  have hpx_val : p x = px := by simp [p, hxS]
  have hpy_val : p y = py := by simp [p, hyS, hxy.symm]
  have hqx_val : q x = px := by simp [q, hxS]
  have hqy_val : q y = py + δ := by simp [q, hyS, hxy.symm]
  have hxSy : x ∉ Sy := by simp [Sy, hxy, hxS]
  have hout : ∀ j, j ∉ Sxy → j ∉ S ∧ j ≠ x ∧ j ≠ y := fun j hj =>
    ⟨fun h => hj (mem_insert_of_mem (mem_insert_of_mem h)), fun h => hj (h ▸ mem_insert_self x _),
      fun h => hj (h ▸ mem_insert_of_mem (mem_insert_self y S))⟩
  -- Check `IsDemand v p Sxy`!
  have hSxy_p : v Sxy - ∑ j ∈ Sxy, p j = v S - ∑ j ∈ S, p j := by
    change v Sxy - ∑ j ∈ insert x Sy, p j = v S - ∑ j ∈ S, p j
    rw [sum_insert hxSy, sum_insert hyS, hpx_val, hpy_val]
    dsimp only [px, py, δ]
    ring
  have hSx_p : v Sx - ∑ j ∈ Sx, p j = v S - ∑ j ∈ S, p j - δ / 2 := by
    dsimp only [Sx]
    rw [sum_insert hxS, hpx_val]
    dsimp only [px]
    ring
  have hSy_p : v Sy - ∑ j ∈ Sy, p j = v S - ∑ j ∈ S, p j - δ / 2 := by
    dsimp only [Sy]
    rw [sum_insert hyS, hpy_val]
    dsimp only [py]
    ring
  have hdem_p : IsDemand v p Sxy := by
    intro B
    rw [hSxy_p]
    by_cases hSB : S ⊆ B ∧ B ⊆ Sxy
    · rcases hfour B hSB.1 hSB.2 with rfl | rfl | rfl | rfl
      · exact le_rfl
      · rw [hSx_p]; linarith
      · rw [hSy_p]; linarith
      · rw [hSxy_p]
    · exact (houtside p (fun j hj => by simp [p, hj]) (fun j hj => by simp [p, hout j hj])
        (by rwa [hpx_val]) (by rw [hpy_val]; linarith) B hSB).le
  -- Apply `IsGrossSubstitutes v` from `p` to `q`: `D` must contain `S` and `x` (`p x = q x`)!
  obtain ⟨D, hD_dem, hD_keep⟩ := hgs hpq hdem_p
  have hSD : S ⊆ D := fun j hj =>
    hD_keep j (mem_insert_of_mem (mem_insert_of_mem hj)) (by simp [p, q, hj])
  have hxD : x ∈ D := hD_keep x (mem_insert_self x _) (by rw [hpx_val, hqx_val])
  have hDSxy : D ⊆ Sxy := by
    by_contra hnot_sub
    have hlt_S := houtside q (fun j hj => by simp [q, hj]) (fun j hj => by simp [q, hout j hj])
      (by rwa [hqx_val])
      (by rw [hqy_val, abs_le]; constructor <;> linarith [abs_le.1 hpy_abs])
      D (fun h => hnot_sub h.2)
    linarith [hD_dem S]
  -- Since `S ⊆ D ⊆ Sxy` and `x ∈ D`, `D` is `Sx` or `Sxy`, both strictly beaten by `S` at `q`!
  have hSx_q : v Sx - ∑ j ∈ Sx, q j = v S - ∑ j ∈ S, q j - δ / 2 := by
    dsimp only [Sx]
    rw [sum_insert hxS, hqx_val]
    dsimp only [px]
    ring
  have hSxy_q : v Sxy - ∑ j ∈ Sxy, q j = v S - ∑ j ∈ S, q j - δ := by
    change v Sxy - ∑ j ∈ insert x Sy, q j = v S - ∑ j ∈ S, q j - δ
    rw [sum_insert hxSy, sum_insert hyS, hqx_val, hqy_val]
    dsimp only [px, py, δ]
    ring
  rcases hfour D hSD hDSxy with rfl | rfl | rfl | rfl
  · exact hxS hxD
  · linarith [hD_dem S, hSx_q]
  · exact hxSy hxD
  · linarith [hD_dem S, hSxy_q]

/-- Antitone marginal values for gross-substitutes valuations: for `S ⊆ T` and `x ∉ T`,
`v (insert x T) - v T ≤ v (insert x S) - v S`. -/
theorem IsGrossSubstitutes.marginal_le_of_subset {M : Type*} [Finite M] [DecidableEq M]
    {v : Finset M → ℝ} (hgs : IsGrossSubstitutes v)
    {S T : Finset M} (hST : S ⊆ T) {x : M} (hxT : x ∉ T) :
    v (insert x T) - v T ≤ v (insert x S) - v S := by
  suffices h : ∀ (K R : Finset M), Disjoint R K → x ∉ R ∪ K →
      v (insert x (R ∪ K)) - v (R ∪ K) ≤ v (insert x R) - v R by
    simpa only [union_sdiff_of_subset hST] using
      h (T \ S) S disjoint_sdiff_self_right (by rwa [union_sdiff_of_subset hST])
  intro K
  induction K using Finset.induction with
  | empty =>
    intro R _ _
    simp
  | insert y K hyK ih =>
    intro R hRK hxRK
    rw [union_insert] at hxRK ⊢
    have hxy : x ≠ y := fun h => hxRK (h ▸ mem_insert_self x _)
    have hx_rest : x ∉ R ∪ K := fun h => hxRK (mem_insert_of_mem h)
    have hyR : y ∉ R := Finset.disjoint_right.1 hRK (mem_insert_self y K)
    have hRK' : Disjoint (insert y R) K := by
      rw [disjoint_insert_left]
      exact ⟨hyK, disjoint_of_subset_right (subset_insert y K) hRK⟩
    have hstep1 : v (insert x (insert y R ∪ K)) - v (insert y R ∪ K) ≤
        v (insert x (insert y R)) - v (insert y R) :=
      ih (insert y R) hRK' (by rwa [insert_union])
    have hxR : x ∉ R := fun h => hx_rest (mem_union_left K h)
    have hstep2 : v (insert x (insert y R)) - v (insert y R) ≤ v (insert x R) - v R := by
      linarith [hgs.insert_insert_add_le R hxy hxR hyR]
    rw [insert_union] at hstep1
    exact hstep1.trans hstep2

/-- **Exercise 11.6 ([BlumrosenNisan2007], p. 299; [GulStacchetti1999]):** every gross-substitutes
valuation on a finite item set is **submodular**. -/
theorem IsGrossSubstitutes.submodular {M : Type*} [Finite M] [DecidableEq M]
    {v : Finset M → ℝ} (hgs : IsGrossSubstitutes v) :
    Cslib.Algorithms.Lean.Submodular.IsSubmodular v :=
  Cslib.Algorithms.Lean.Submodular.isSubmodular_of_insert_add_le fun _ _ _ hAB hx => by
    linarith [hgs.marginal_le_of_subset hAB hx]

end Substitutes

/-! ### `ε`-Walrasian equilibrium and the Kelso–Crawford ascending auction (Figure 11.3) -/

section KelsoCrawford

/-- Personalized item prices faced by a bidder tentatively holding bundle `S` in the Figure 11.3
ascending item-price auction ([BlumrosenNisan2007], Figure 11.3 and Definition 11.29, pp. 290–291):
`p j` on retained items `j ∈ S` and `p j + ε` on new items `j ∉ S`. -/
@[expose] def personalizedPrice {M : Type*} [DecidableEq M] (ε : ℝ) (p : M → ℝ) (S : Finset M)
    (j : M) : ℝ :=
  if j ∈ S then p j else p j + ε

@[simp] theorem personalizedPrice_of_mem {M : Type*} [DecidableEq M] (ε : ℝ) (p : M → ℝ)
    {S : Finset M} {j : M} (hj : j ∈ S) :
    personalizedPrice ε p S j = p j := by
  simp [personalizedPrice, hj]

@[simp] theorem personalizedPrice_of_notMem {M : Type*} [DecidableEq M] (ε : ℝ) (p : M → ℝ)
    {S : Finset M} {j : M} (hj : j ∉ S) :
    personalizedPrice ε p S j = p j + ε := by
  simp [personalizedPrice, hj]

@[simp] theorem sum_personalizedPrice_self {M : Type*} [DecidableEq M] (ε : ℝ) (p : M → ℝ)
    (S : Finset M) :
    ∑ j ∈ S, personalizedPrice ε p S j = ∑ j ∈ S, p j :=
  sum_congr rfl fun _ hj => by simp [personalizedPrice, hj]

/-- An **`ε`-Walrasian equilibrium** ([BlumrosenNisan2007], Definition 11.29, p. 291, paired with
nonnegative item prices as in Definition 11.12): every bidder's assigned bundle `a.bundle i` is a
demand at personalized prices `personalizedPrice ε p (a.bundle i)` and every unallocated item has
price `0`. -/
structure IsEpsWalrasianEquilibrium {N M : Type*} [DecidableEq M]
    (v : N → Finset M → ℝ) (ε : ℝ) (p : M → ℝ) (a : Allocation N M) : Prop where
  /-- Item prices are nonnegative. -/
  price_nonneg (j : M) : 0 ≤ p j
  /-- Each bidder `i`'s bundle is optimal at `personalizedPrice ε p (a.bundle i)`. -/
  demand (i : N) : IsDemand (v i) (personalizedPrice ε p (a.bundle i)) (a.bundle i)
  /-- Unallocated items have price `0` (`⋃ i, a.bundle i ⊇ {j | p j > 0}`). -/
  unallocated_price_zero (j : M) : (∀ i : N, j ∉ a.bundle i) → p j = 0

/-- At `ε = 0`, `IsEpsWalrasianEquilibrium` coincides with `IsWalrasianEquilibrium`. -/
theorem isEpsWalrasianEquilibrium_zero_iff {N M : Type*} [DecidableEq M]
    (v : N → Finset M → ℝ) (p : M → ℝ) (a : Allocation N M) :
    IsEpsWalrasianEquilibrium v 0 p a ↔ IsWalrasianEquilibrium v p a := by
  have hp_eq : ∀ S : Finset M, personalizedPrice 0 p S = p := fun S =>
    funext fun j => by simp [personalizedPrice]
  constructor
  · rintro ⟨hp, hdem, hunalloc⟩
    exact ⟨hp, fun i => hp_eq (a.bundle i) ▸ hdem i, hunalloc⟩
  · rintro ⟨hp, hdem, hunalloc⟩
    exact ⟨hp, fun i => (hp_eq (a.bundle i)).symm ▸ hdem i, hunalloc⟩

/-- Allocated-item welfare bound for an `ε`-Walrasian equilibrium: for `0 ≤ ε` and any allocation
`b`, social welfare at `a` is within `(∑ i, |b_i|) * ε` of `welfare v b`. -/
theorem IsEpsWalrasianEquilibrium.welfare_sub_sum_card_le {N M : Type*} [Fintype N] [Finite M]
    [DecidableEq M] {v : N → Finset M → ℝ} {ε : ℝ} {p : M → ℝ} {a : Allocation N M}
    (heq : IsEpsWalrasianEquilibrium v ε p a) (hε : 0 ≤ ε) (b : Allocation N M) :
    welfare v b - (∑ i : N, ((b.bundle i).card : ℝ)) * ε ≤ welfare v a := by
  have := Fintype.ofFinite M
  have hbidder : ∀ i : N,
      v i (b.bundle i) - ∑ j ∈ b.bundle i, p j - ((b.bundle i).card : ℝ) * ε ≤
        v i (a.bundle i) - ∑ j ∈ a.bundle i, p j := by
    intro i
    have hdem := heq.demand i (b.bundle i)
    rw [sum_personalizedPrice_self] at hdem
    have hq_le : ∑ j ∈ b.bundle i, personalizedPrice ε p (a.bundle i) j ≤
        (∑ j ∈ b.bundle i, p j) + ((b.bundle i).card : ℝ) * ε :=
      calc ∑ j ∈ b.bundle i, personalizedPrice ε p (a.bundle i) j
          ≤ ∑ j ∈ b.bundle i, (p j + ε) := sum_le_sum fun j _ => by
            dsimp only [personalizedPrice]
            split_ifs <;> linarith
        _ = (∑ j ∈ b.bundle i, p j) + ((b.bundle i).card : ℝ) * ε := by
            rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    linarith
  have hsum := sum_le_sum fun i (_ : i ∈ (univ : Finset N)) => hbidder i
  simp only [sum_sub_distrib, ← sum_mul] at hsum
  have hdisj_b : Set.PairwiseDisjoint (univ : Finset N) b.bundle :=
    fun i₁ _ i₂ _ hne => b.disjoint hne
  have hp_b : ∑ i : N, ∑ j ∈ b.bundle i, p j ≤ ∑ j : M, p j := by
    rw [← sum_biUnion hdisj_b]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ => heq.price_nonneg j
  have hdisj_a : Set.PairwiseDisjoint (univ : Finset N) a.bundle :=
    fun i₁ _ i₂ _ hne => a.disjoint hne
  have hp_a : ∑ i : N, ∑ j ∈ a.bundle i, p j = ∑ j : M, p j := by
    rw [← sum_biUnion hdisj_a]
    refine sum_subset (subset_univ _) fun j _ hj => ?_
    exact heq.unallocated_price_zero j fun i hi => hj (mem_biUnion.2 ⟨i, mem_univ i, hi⟩)
  unfold welfare
  linarith

/-- **Approximate First Welfare Theorem for `ε`-Walrasian equilibria**
([BlumrosenNisan2007], Theorem 11.30, p. 291, with corrected `|M| * ε` surcharge bound): for
`0 ≤ ε`, any `ε`-Walrasian equilibrium allocation `a` achieves social welfare within
`(Fintype.card M : ℝ) * ε` of every allocation `b`. -/
theorem IsEpsWalrasianEquilibrium.welfare_le {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq M] {v : N → Finset M → ℝ} {ε : ℝ} {p : M → ℝ} {a : Allocation N M}
    (heq : IsEpsWalrasianEquilibrium v ε p a) (hε : 0 ≤ ε) (b : Allocation N M) :
    welfare v b - (Fintype.card M : ℝ) * ε ≤ welfare v a := by
  have hdisj_b : Set.PairwiseDisjoint (univ : Finset N) b.bundle :=
    fun i₁ _ i₂ _ hne => b.disjoint hne
  have hcard_le : (∑ i : N, ((b.bundle i).card : ℝ)) ≤ (Fintype.card M : ℝ) := by
    exact_mod_cast (card_biUnion hdisj_b).symm.le.trans (card_le_univ (univ.biUnion b.bundle))
  linarith [heq.welfare_sub_sum_card_le hε b, mul_le_mul_of_nonneg_right hcard_le hε]

/-- When comparing against an allocation `b` that assigns each bidder at most one item
(`∀ i, (b.bundle i).card ≤ 1`, as in unit-demand environments), the `|N| * ε` bound printed in
[BlumrosenNisan2007], Theorem 11.30 (p. 291) holds. -/
theorem IsEpsWalrasianEquilibrium.welfare_le_of_card_le_one {N M : Type*} [Fintype N] [Finite M]
    [DecidableEq M] {v : N → Finset M → ℝ} {ε : ℝ} {p : M → ℝ} {a : Allocation N M}
    (heq : IsEpsWalrasianEquilibrium v ε p a) (hε : 0 ≤ ε) {b : Allocation N M}
    (hb : ∀ i : N, (b.bundle i).card ≤ 1) :
    welfare v b - (Fintype.card N : ℝ) * ε ≤ welfare v a := by
  have hcard_le : (∑ i : N, ((b.bundle i).card : ℝ)) ≤ (Fintype.card N : ℝ) :=
    calc (∑ i : N, ((b.bundle i).card : ℝ))
        ≤ ∑ _i : N, (1 : ℝ) := sum_le_sum fun i _ => Nat.cast_le_one.2 (hb i)
      _ = (Fintype.card N : ℝ) := by simp
  linarith [heq.welfare_sub_sum_card_le hε b, mul_le_mul_of_nonneg_right hcard_le hε]

/-- Aggregate valuation bound `∑ i, ∑ S, |v i S|` bounding every item's price throughout the
Kelso–Crawford ascending auction without requiring monotonicity or `[Nonempty]` hypotheses. -/
@[expose] def valuationBound {N M : Type*} [Fintype N] [Fintype M]
    (v : N → Finset M → ℝ) : ℝ :=
  ∑ i : N, ∑ S : Finset M, |v i S|

theorem valuationBound_nonneg {N M : Type*} [Fintype N] [Fintype M] (v : N → Finset M → ℝ) :
    0 ≤ valuationBound v :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

private theorem sub_erase_le_valuationBound {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]
    (v : N → Finset M → ℝ) (i : N) {D : Finset M} {j : M} (hj : j ∈ D) :
    v i D - v i (D.erase j) ≤ valuationBound v := by
  have hne : D ≠ D.erase j := fun h => notMem_erase j D (h ▸ hj)
  have hpair : |v i D| + |v i (D.erase j)| ≤ ∑ S : Finset M, |v i S| := by
    simpa only [sum_pair hne] using
      sum_le_sum_of_subset_of_nonneg (subset_univ ({D, D.erase j} : Finset (Finset M)))
        fun T _ _ => abs_nonneg (v i T)
  have hi_le : ∑ S : Finset M, |v i S| ≤ valuationBound v := by
    unfold valuationBound
    exact single_le_sum (fun k _ => sum_nonneg fun S _ => abs_nonneg (v k S)) (mem_univ i)
  linarith [le_abs_self (v i D), neg_le_abs (v i (D.erase j))]

/-- State `(price, alloc)` of the Figure 11.3 Kelso–Crawford ascending item-price auction
([BlumrosenNisan2007], p. 290). -/
structure AuctionState (N M : Type*) where
  /-- Current item price vector `p_j`. -/
  price : M → ℝ
  /-- Tentative allocation `(S_1, …, S_n)`. -/
  alloc : Allocation N M

/-- Initial Figure 11.3 state: zero prices and empty tentative bundles (`p_j = 0`, `S_i = ∅`). -/
def kelsoCrawfordInit (N M : Type*) : AuctionState N M where
  price _ := 0
  alloc := ⟨fun _ => ∅, fun _ _ _ => disjoint_empty_left _⟩

@[simp] theorem kelsoCrawfordInit_price (N M : Type*) (j : M) :
    (kelsoCrawfordInit N M).price j = 0 := by rfl

@[simp] theorem kelsoCrawfordInit_bundle (N M : Type*) (i : N) :
    (kelsoCrawfordInit N M).alloc.bundle i = ∅ := by rfl

/-- Invariant maintained across every stage of the Figure 11.3 auction ([BlumrosenNisan2007],
Claim 11.31 and Footnote 5, p. 291, paired with price nonnegativity, zero price on unallocated
items, and `valuationBound` upper bound). -/
structure AuctionState.IsValid {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]
    (v : N → Finset M → ℝ) (ε : ℝ) (st : AuctionState N M) : Prop where
  /-- Item prices are nonnegative. -/
  price_nonneg (j : M) : 0 ≤ st.price j
  /-- Every item of positive price is tentatively allocated. -/
  unallocated_price_zero (j : M) : (∀ i : N, j ∉ st.alloc.bundle i) → st.price j = 0
  /-- Claim 11.31 / Footnote 5: each bidder's tentative bundle `S_i` is contained in some demand
  bundle `D_i` at personalized prices `personalizedPrice ε st.price S_i`. -/
  exists_superset_demand (i : N) :
    ∃ D : Finset M,
      IsDemand (v i) (personalizedPrice ε st.price (st.alloc.bundle i)) D ∧
        st.alloc.bundle i ⊆ D
  /-- Every item price is bounded above by `valuationBound v`. -/
  price_le (j : M) : st.price j ≤ valuationBound v

theorem isValid_kelsoCrawfordInit {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]
    (v : N → Finset M → ℝ) (ε : ℝ) :
    (kelsoCrawfordInit N M).IsValid v ε where
  price_nonneg _ := le_rfl
  unallocated_price_zero _ _ := rfl
  exists_superset_demand i := by
    obtain ⟨D, hD⟩ := exists_isDemand (v i) (personalizedPrice ε (fun _ => 0) ∅)
    exact ⟨D, hD, empty_subset D⟩
  price_le _ := valuationBound_nonneg v

/-- One bidder-update transition of Figure 11.3 ([BlumrosenNisan2007], p. 290): bidder `i` moves to
demand bundle `D`, raising prices by `ε` on `D \ S_i` and removing `D` from every other bidder
`k ≠ i`. -/
def kelsoCrawfordUpdate {N M : Type*} [DecidableEq N] [DecidableEq M]
    (st : AuctionState N M) (ε : ℝ) (i : N) (D : Finset M) : AuctionState N M where
  price j := if j ∈ D \ st.alloc.bundle i then st.price j + ε else st.price j
  alloc :=
    { bundle := fun k => if k = i then D else st.alloc.bundle k \ D
      disjoint := fun k₁ k₂ hne => by
        dsimp only [Function.onFun]
        by_cases hk₁ : k₁ = i
        · subst hk₁
          simp only [↓reduceIte, hne.symm]
          exact disjoint_sdiff_self_right
        · by_cases hk₂ : k₂ = i
          · subst hk₂
            simp only [hk₁, ↓reduceIte]
            exact disjoint_sdiff_self_left
          · simp only [hk₁, hk₂, ↓reduceIte]
            exact disjoint_of_subset_left sdiff_subset
              (disjoint_of_subset_right sdiff_subset (st.alloc.disjoint hne)) }

/-- **Claim 11.31 ([BlumrosenNisan2007], p. 291):** under `IsGrossSubstitutes` and `0 < ε`, updating
an unsatisfied bidder `i` to a superset demand bundle `D ⊃ S_i` preserves `AuctionState.IsValid` and
strictly increases `∑ j, price j` by at least `ε`. -/
theorem AuctionState.IsValid.kelsoCrawfordUpdate {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq N] [DecidableEq M] {v : N → Finset M → ℝ}
    (hgs : ∀ k : N, IsGrossSubstitutes (v k)) {ε : ℝ} (hε : 0 < ε)
    {st : AuctionState N M} (hst : st.IsValid v ε) {i : N} {D : Finset M}
    (hD_dem : IsDemand (v i) (personalizedPrice ε st.price (st.alloc.bundle i)) D)
    (hSD : st.alloc.bundle i ⊆ D) (hne : st.alloc.bundle i ≠ D) :
    (CombinatorialAuction.kelsoCrawfordUpdate st ε i D).IsValid v ε ∧
      (∑ j : M, st.price j) + ε ≤
        ∑ j : M, (CombinatorialAuction.kelsoCrawfordUpdate st ε i D).price j := by
  set st' := CombinatorialAuction.kelsoCrawfordUpdate st ε i D
  have hsdiff_ne : (D \ st.alloc.bundle i).Nonempty :=
    sdiff_nonempty.2 fun hDsub => hne (Subset.antisymm hSD hDsub)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- `price_nonneg`
    intro j
    dsimp only [st', CombinatorialAuction.kelsoCrawfordUpdate]
    split_ifs <;> linarith [hst.price_nonneg j]
  · -- `unallocated_price_zero`
    intro j hj_none
    have hjD : j ∉ D := by simpa [st', CombinatorialAuction.kelsoCrawfordUpdate] using hj_none i
    have hj_old : ∀ k : N, j ∉ st.alloc.bundle k := by
      intro k
      by_cases hki : k = i
      · subst hki
        exact fun hjS => hjD (hSD hjS)
      · intro hjSk
        have hk := hj_none k
        simp only [st', CombinatorialAuction.kelsoCrawfordUpdate, hki, ↓reduceIte,
          mem_sdiff] at hk
        exact hk ⟨hjSk, hjD⟩
    have hj_not_sdiff : j ∉ D \ st.alloc.bundle i := fun h => hjD (mem_sdiff.1 h).1
    exact (ite_eq_right hj_not_sdiff).trans (hst.unallocated_price_zero j hj_old)
  · -- `exists_superset_demand` (Claim 11.31!)
    intro k
    by_cases hki : k = i
    · subst hki
      have hq_eq : personalizedPrice ε st'.price (st'.alloc.bundle k) =
          personalizedPrice ε st.price (st.alloc.bundle k) := by
        funext j
        dsimp only [st', CombinatorialAuction.kelsoCrawfordUpdate, personalizedPrice]
        simp only [↓reduceIte, mem_sdiff]
        by_cases hjD : j ∈ D <;> by_cases hjS : j ∈ st.alloc.bundle k <;>
          first | exact (hjD (hSD hjS)).elim | simp [hjD, hjS]
      have hbundle_i : st'.alloc.bundle k = D := by
        simp [st', CombinatorialAuction.kelsoCrawfordUpdate]
      exact ⟨D, hq_eq ▸ hD_dem, hbundle_i.le⟩
    · obtain ⟨Dk, hDk_dem, hSk_sub⟩ := hst.exists_superset_demand k
      have hbundle_k : st'.alloc.bundle k = st.alloc.bundle k \ D := by
        simp [st', CombinatorialAuction.kelsoCrawfordUpdate, hki]
      let qOld := personalizedPrice ε st.price (st.alloc.bundle k)
      let qNew := personalizedPrice ε st'.price (st'.alloc.bundle k)
      have hq_mono : ∀ j : M, qOld j ≤ qNew j := by
        intro j
        dsimp only [qOld, qNew]
        rw [hbundle_k]
        dsimp only [personalizedPrice, st', CombinatorialAuction.kelsoCrawfordUpdate]
        by_cases hjSk : j ∈ st.alloc.bundle k <;> by_cases hjD : j ∈ D <;>
          by_cases hjSi : j ∈ st.alloc.bundle i <;>
          simp only [mem_sdiff, hjSk, hjD, hjSi, not_true_eq_false, not_false_eq_true, and_self,
            and_false, false_and, ↓reduceIte] <;>
          linarith
      have hq_eq_kept : ∀ j ∈ st.alloc.bundle k \ D, qOld j = qNew j := by
        intro j hj
        obtain ⟨hjSk, hjD⟩ := mem_sdiff.1 hj
        dsimp only [qOld, qNew]
        rw [hbundle_k]
        dsimp only [personalizedPrice, st', CombinatorialAuction.kelsoCrawfordUpdate]
        simp [mem_sdiff, hjSk, hjD]
      obtain ⟨Dk', hDk'_dem, hDk'_keep⟩ := hgs k hq_mono hDk_dem
      refine ⟨Dk', hDk'_dem, ?_⟩
      rw [hbundle_k]
      exact fun j hj => hDk'_keep j (hSk_sub (mem_sdiff.1 hj).1) (hq_eq_kept j hj)
  · -- `price_le`
    intro j
    dsimp only [st', CombinatorialAuction.kelsoCrawfordUpdate]
    split_ifs with hjsdiff
    · obtain ⟨hjD, hjSi⟩ := mem_sdiff.1 hjsdiff
      have hle_diff := hD_dem.price_le_sub_erase hjD
      rw [personalizedPrice_of_notMem ε st.price hjSi] at hle_diff
      exact hle_diff.trans (sub_erase_le_valuationBound v i hjD)
    · exact hst.price_le j
  · -- Strict total-price increase `∑ j, st.price j + ε ≤ ∑ j, st'.price j`
    obtain ⟨j₀, hj₀⟩ := hsdiff_ne
    rw [← add_sum_erase univ st.price (mem_univ j₀), ← add_sum_erase univ st'.price (mem_univ j₀)]
    have hj₀_eq : st'.price j₀ = st.price j₀ + ε := ite_eq_left hj₀
    have hrest_le : ∑ j ∈ univ.erase j₀, st.price j ≤ ∑ j ∈ univ.erase j₀, st'.price j := by
      refine sum_le_sum fun j _ => ?_
      dsimp only [st', CombinatorialAuction.kelsoCrawfordUpdate]
      split_ifs <;> linarith
    linarith

open Classical in
/-- Bounded-fuel recursion running the Figure 11.3 Kelso–Crawford ascending auction from `st`. -/
noncomputable def kelsoCrawfordLoop {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq N] [DecidableEq M]
    (v : N → Finset M → ℝ) (ε : ℝ) : ℕ → AuctionState N M → AuctionState N M
  | 0, st => st
  | fuel + 1, st =>
    if h : ∃ i : N, ¬ IsDemand (v i) (personalizedPrice ε st.price (st.alloc.bundle i))
        (st.alloc.bundle i) then
      let i := h.choose
      let D :=
        if hsup : ∃ D : Finset M,
            IsDemand (v i) (personalizedPrice ε st.price (st.alloc.bundle i)) D ∧
              st.alloc.bundle i ⊆ D then
          hsup.choose
        else st.alloc.bundle i
      kelsoCrawfordLoop v ε fuel (kelsoCrawfordUpdate st ε i D)
    else st

/-- Explicit stage bound `⌊|M| * valuationBound v / ε⌋ + 1` for Figure 11.3 ([BlumrosenNisan2007],
p. 291). -/
noncomputable def kelsoCrawfordFuel {N M : Type*} [Fintype N] [Fintype M]
    (v : N → Finset M → ℝ) (ε : ℝ) : ℕ :=
  Nat.floor ((Fintype.card M : ℝ) * valuationBound v / ε) + 1

/-- Complete run of the Figure 11.3 Kelso–Crawford ascending item-price auction from zero prices
and empty bundles ([BlumrosenNisan2007], Figure 11.3, p. 290). -/
noncomputable def kelsoCrawford {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq N] [DecidableEq M]
    (v : N → Finset M → ℝ) (ε : ℝ) : AuctionState N M :=
  kelsoCrawfordLoop v ε (kelsoCrawfordFuel v ε) (kelsoCrawfordInit N M)

open Classical in
/-- Any state `st` in which every bidder already demands their tentative bundle at personalized
prices is a fixed point of `kelsoCrawfordLoop`. -/
private theorem kelsoCrawfordLoop_eq_self {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq N] [DecidableEq M] {v : N → Finset M → ℝ} {ε : ℝ} (fuel : ℕ)
    {st : AuctionState N M}
    (hdem : ∀ i : N, IsDemand (v i) (personalizedPrice ε st.price (st.alloc.bundle i))
      (st.alloc.bundle i)) :
    kelsoCrawfordLoop v ε fuel st = st := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp [kelsoCrawfordLoop, hdem]

/-- When `∅` is already a demand bundle for every bidder at uniform surcharge prices `fun _ => ε`,
`kelsoCrawford v ε` halts immediately at `kelsoCrawfordInit N M`. -/
theorem kelsoCrawford_eq_init {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq N] [DecidableEq M] {v : N → Finset M → ℝ} {ε : ℝ}
    (hdem : ∀ i : N, IsDemand (v i) (fun _ => ε) ∅) :
    kelsoCrawford v ε = kelsoCrawfordInit N M := by
  refine kelsoCrawfordLoop_eq_self (kelsoCrawfordFuel v ε) fun i => ?_
  have hp : personalizedPrice ε (kelsoCrawfordInit N M).price (∅ : Finset M) = fun _ => ε :=
    funext fun j => by simp [personalizedPrice]
  rw [kelsoCrawfordInit_bundle, hp]
  exact hdem i

open Classical in
private theorem kelsoCrawfordLoop_terminates {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq N] [DecidableEq M]
    {v : N → Finset M → ℝ} (hgs : ∀ k : N, IsGrossSubstitutes (v k))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ (fuel : ℕ) (st : AuctionState N M),
      st.IsValid v ε →
      (Fintype.card M : ℝ) * valuationBound v - ∑ j : M, st.price j < (fuel : ℝ) * ε →
      IsEpsWalrasianEquilibrium v ε (kelsoCrawfordLoop v ε fuel st).price
        (kelsoCrawfordLoop v ε fuel st).alloc ∧
      ∀ j : M, (kelsoCrawfordLoop v ε fuel st).price j ≤ valuationBound v := by
  intro fuel
  induction fuel with
  | zero =>
    intro st hst hlt
    exfalso
    have hsum_le : ∑ j : M, st.price j ≤ (Fintype.card M : ℝ) * valuationBound v :=
      calc ∑ j : M, st.price j
          ≤ ∑ _j : M, valuationBound v := sum_le_sum fun j _ => hst.price_le j
        _ = (Fintype.card M : ℝ) * valuationBound v := by rw [sum_const, card_univ, nsmul_eq_mul]
    simp only [Nat.cast_zero, zero_mul] at hlt
    linarith
  | succ fuel ih =>
    intro st hst hlt
    by_cases hex : ∃ i : N,
        ¬ IsDemand (v i) (personalizedPrice ε st.price (st.alloc.bundle i)) (st.alloc.bundle i)
    · set i := hex.choose
      have hi_not :
          ¬ IsDemand (v i) (personalizedPrice ε st.price (st.alloc.bundle i))
            (st.alloc.bundle i) := hex.choose_spec
      have hsup : ∃ D : Finset M,
          IsDemand (v i) (personalizedPrice ε st.price (st.alloc.bundle i)) D ∧
            st.alloc.bundle i ⊆ D := hst.exists_superset_demand i
      have hstep_eq : kelsoCrawfordLoop v ε (fuel + 1) st =
          kelsoCrawfordLoop v ε fuel (kelsoCrawfordUpdate st ε i hsup.choose) := by
        simp only [kelsoCrawfordLoop, hex, ↓reduceDIte, i, hsup]
      rw [hstep_eq]
      obtain ⟨hD_dem, hSD⟩ := hsup.choose_spec
      have hne : st.alloc.bundle i ≠ hsup.choose := fun heq => by
        rw [← heq] at hD_dem
        exact hi_not hD_dem
      obtain ⟨hst', hinc⟩ := hst.kelsoCrawfordUpdate hgs hε hD_dem hSD hne
      refine ih _ hst' ?_
      push_cast at hlt
      linarith
    · push Not at hex
      rw [kelsoCrawfordLoop_eq_self _ hex]
      exact ⟨⟨hst.price_nonneg, hex, hst.unallocated_price_zero⟩, hst.price_le⟩

/-- **Theorem 11.30 ([BlumrosenNisan2007], p. 291; [KelsoCrawford1982]):** for any profile of
gross-substitutes valuations and step size `0 < ε`, the Figure 11.3 ascending auction
`kelsoCrawford v ε` terminates at an `ε`-Walrasian equilibrium with item prices bounded by
`valuationBound v` (hence social welfare within `|M| * ε` of optimal by
`IsEpsWalrasianEquilibrium.welfare_le`). -/
theorem kelsoCrawford_isEpsWalrasianEquilibrium {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq N] [DecidableEq M] {v : N → Finset M → ℝ} (hgs : ∀ i : N, IsGrossSubstitutes (v i))
    {ε : ℝ} (hε : 0 < ε) :
    IsEpsWalrasianEquilibrium v ε (kelsoCrawford v ε).price (kelsoCrawford v ε).alloc ∧
      ∀ j : M, (kelsoCrawford v ε).price j ≤ valuationBound v := by
  refine kelsoCrawfordLoop_terminates hgs hε (kelsoCrawfordFuel v ε) (kelsoCrawfordInit N M)
    (isValid_kelsoCrawfordInit v ε) ?_
  have hinit_sum : ∑ j : M, (kelsoCrawfordInit N M).price j = 0 := by
    simp [kelsoCrawfordInit]
  rw [hinit_sum, sub_zero]
  unfold kelsoCrawfordFuel
  have hlt_div :
      (Fintype.card M : ℝ) * valuationBound v / ε <
        (Nat.floor ((Fintype.card M : ℝ) * valuationBound v / ε) + 1 : ℕ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  exact (div_lt_iff₀ hε).1 hlt_div

/-! ### Exact Walrasian equilibrium existence and zero LPR integrality gap -/

/-- **Kelso–Crawford / Gul–Stacchetti Walrasian equilibrium existence theorem**
([KelsoCrawford1982]; [GulStacchetti1999]; [BlumrosenNisan2007], §§11.7.1 and 11.8, pp. 290–295):
every finite combinatorial auction whose bidders have gross-substitutes valuations admits an
**exact** Walrasian equilibrium `(p, a)`. -/
theorem exists_isWalrasianEquilibrium_of_isGrossSubstitutes {N M : Type*} [Finite N] [Finite M]
    {v : N → Finset M → ℝ} (hgs : ∀ i : N, IsGrossSubstitutes (v i)) :
    ∃ (p : M → ℝ) (a : Allocation N M), IsWalrasianEquilibrium v p a := by
  classical
  have := Fintype.ofFinite N
  have := Fintype.ofFinite M
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε_pos : ∀ k : ℕ, 0 < ε k := fun k => by dsimp only [ε]; positivity
  let run : ℕ → AuctionState N M := fun k => kelsoCrawford v (ε k)
  have hrun : ∀ k : ℕ,
      IsEpsWalrasianEquilibrium v (ε k) (run k).price (run k).alloc ∧
        ∀ j : M, (run k).price j ≤ valuationBound v :=
    fun k => kelsoCrawford_isEpsWalrasianEquilibrium hgs (hε_pos k)
  have hfin : Finite (Allocation N M) :=
    Finite.of_injective Allocation.bundle fun _ _ h => Allocation.ext h
  obtain ⟨a, ha_inf⟩ := Finite.exists_infinite_fiber fun k : ℕ => (run k).alloc
  have ha_set_inf : Set.Infinite ((fun k : ℕ => (run k).alloc) ⁻¹' {a}) :=
    Set.infinite_coe_iff.1 ha_inf
  have hex_gt : ∀ m : ℕ, ∃ k : ℕ, m < k ∧ (run k).alloc = a := fun m => by
    obtain ⟨k, hkS, hknot⟩ := (ha_set_inf.sdiff (Finset.range (m + 1)).finite_toSet).nonempty
    rw [Finset.mem_coe, Finset.mem_range] at hknot
    exact ⟨k, by omega, hkS⟩
  let emb : ℕ → ℕ := Nat.rec (hex_gt 0).choose fun _ prev => (hex_gt prev).choose
  have hemb_mono : StrictMono emb :=
    strictMono_nat_of_lt_succ fun n => (hex_gt (emb n)).choose_spec.1
  have hemb_alloc : ∀ n : ℕ, (run (emb n)).alloc = a := fun n => by
    cases n with
    | zero => exact (hex_gt 0).choose_spec.2
    | succ n => exact (hex_gt (emb n)).choose_spec.2
  have hcompact : IsCompact (Set.pi Set.univ fun _ : M => Set.Icc (0 : ℝ) (valuationBound v)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨p, hp_mem, ψ, hψ_mono, hψ_lim⟩ :=
    IsCompact.tendsto_subseq hcompact (x := fun n : ℕ => (run (emb n)).price) fun n j _ =>
      ⟨(hrun (emb n)).1.price_nonneg j, (hrun (emb n)).2 j⟩
  let φ : ℕ → ℕ := fun n => emb (ψ n)
  have hφ_mono : StrictMono φ := hemb_mono.comp hψ_mono
  have ha_eq : ∀ n : ℕ, (run (φ n)).alloc = a := fun n => hemb_alloc (ψ n)
  have hp_coord : ∀ j : M, Filter.Tendsto (fun n => (run (φ n)).price j) Filter.atTop (𝓝 (p j)) :=
    fun j => (tendsto_pi_nhds.1 hψ_lim) j
  have hε_lim : Filter.Tendsto (fun n => ε (φ n)) Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ_mono.tendsto_atTop
  refine ⟨p, a, fun j => (hp_mem j (Set.mem_univ j)).1, fun i S => ?_, fun j hj_none => ?_⟩
  · -- Pass `IsDemand` at `personalizedPrice (ε (φ n))` to the `n → ∞` limit!
    have hstep : ∀ n : ℕ,
        v i S - ∑ j ∈ S, personalizedPrice (ε (φ n)) (run (φ n)).price (a.bundle i) j ≤
          v i (a.bundle i) - ∑ j ∈ a.bundle i, (run (φ n)).price j := fun n => by
      simpa only [ha_eq n, sum_personalizedPrice_self] using (hrun (φ n)).1.demand i S
    have hq_coord : ∀ j : M,
        Filter.Tendsto (fun n => personalizedPrice (ε (φ n)) (run (φ n)).price (a.bundle i) j)
          Filter.atTop (𝓝 (p j)) := by
      intro j
      by_cases hj : j ∈ a.bundle i <;> simp only [personalizedPrice, hj, ↓reduceIte]
      · exact hp_coord j
      · simpa only [add_zero] using (hp_coord j).add hε_lim
    have hL : Filter.Tendsto
        (fun n => v i S - ∑ j ∈ S, personalizedPrice (ε (φ n)) (run (φ n)).price (a.bundle i) j)
        Filter.atTop (𝓝 (v i S - ∑ j ∈ S, p j)) :=
      tendsto_const_nhds.sub (tendsto_finsetSum S fun j _ => hq_coord j)
    have hR : Filter.Tendsto
        (fun n => v i (a.bundle i) - ∑ j ∈ a.bundle i, (run (φ n)).price j)
        Filter.atTop (𝓝 (v i (a.bundle i) - ∑ j ∈ a.bundle i, p j)) :=
      tendsto_const_nhds.sub (tendsto_finsetSum (a.bundle i) fun j _ => hp_coord j)
    exact le_of_tendsto_of_tendsto hL hR (Filter.Eventually.of_forall hstep)
  · -- Unallocated item has `p_{φ n} j = 0` for all `n`, hence `p j = 0`.
    have hzero_n : ∀ n : ℕ, (run (φ n)).price j = 0 := fun n =>
      (hrun (φ n)).1.unallocated_price_zero j (by rw [ha_eq n]; exact hj_none)
    exact tendsto_nhds_unique (hp_coord j) (by simp only [hzero_n]; exact tendsto_const_nhds)

/-- **Zero `LPR` integrality gap for gross-substitutes valuations**
([BlumrosenNisan2007], Corollary 11.16 and §11.7.1, pp. 279, 290–291): whenever `∀ i, 0 ≤ v i ∅`
and `∀ i, IsGrossSubstitutes (v i)`, the configuration linear programming relaxation `LPR` admits an
integral (`0–1`) optimal solution. -/
theorem exists_isIntegral_isLPROptimal_of_isGrossSubstitutes {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq M] {v : N → Finset M → ℝ} (hv : ∀ i, 0 ≤ v i ∅)
    (hgs : ∀ i, IsGrossSubstitutes (v i)) :
    ∃ x : N → Finset M → ℝ, IsLPROptimal v x ∧ IsIntegral x :=
  (exists_isWalrasianEquilibrium_iff hv).1 (exists_isWalrasianEquilibrium_of_isGrossSubstitutes hgs)

/-! ### Example 11.32: demand-reduction manipulation under gross substitutes -/

/-- Truthful valuation profile of **Example 11.32** ([BlumrosenNisan2007], p. 292): Alice (`false`)
is unit-demand with value `4` on each of the two items `{false, true}`; Bob (`true`) is additive
with value `5` on each item (`10` on `{false, true}`). -/
@[expose] def demandReductionVal (i : Bool) : Finset Bool → ℝ :=
  if i then additiveValuation (fun _ => 5) else unitDemandValuation (fun _ => 4)

theorem demandReductionVal_isGrossSubstitutes (i : Bool) :
    IsGrossSubstitutes (demandReductionVal i) := by
  cases i
  · exact isGrossSubstitutes_unitDemandValuation fun _ => by norm_num
  · exact isGrossSubstitutes_additiveValuation _

/-- Under truthful bidding in Example 11.32, `p = (4, 4)` allocating `{false, true}` to Bob (`true`)
and `∅` to Alice (`false`) is a Walrasian equilibrium giving Bob utility `2`. -/
theorem demandReductionVal_truthful_equilibrium :
    IsWalrasianEquilibrium demandReductionVal (fun _ => 4)
      ⟨fun i => if i then univ else ∅, by
        intro i₁ i₂ hne
        dsimp only [Function.onFun]
        cases i₁ <;> cases i₂
        · exact (hne rfl).elim
        · exact disjoint_empty_left _
        · exact disjoint_empty_right _
        · exact (hne rfl).elim⟩ := by
  refine ⟨fun _ => by norm_num, fun i S => ?_, fun j hj => (hj true (mem_univ j)).elim⟩
  cases i
  · -- Alice (`false`): `unitDemandValuation 4 S - 4 * |S| ≤ 0`.
    simp only [demandReductionVal, Bool.false_eq_true, ↓reduceIte, unitDemandValuation_empty,
      sum_empty, sub_zero]
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp
    · obtain ⟨b, -, hb_eq⟩ := exists_mem_unitDemandValuation_eq
        (w := fun _ : Bool => (4 : ℝ)) (fun _ => by norm_num) hS
      have hcard : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hS
      rw [hb_eq, sum_const, nsmul_eq_mul]
      linarith
  · -- Bob (`true`): `5 * |S| - 4 * |S| = |S| ≤ 2 = 10 - 8`.
    simp only [demandReductionVal, ↓reduceIte, Cslib.Algorithms.Lean.Submodular.modularSum,
      sum_const, nsmul_eq_mul]
    have hcard : (S.card : ℝ) ≤ ((univ : Finset Bool).card : ℝ) := by
      exact_mod_cast card_le_univ S
    have huniv : ((univ : Finset Bool).card : ℝ) = 2 := by simp
    linarith

/-- Stronger Example 11.32 property: in **every** truthful Walrasian equilibrium `(p, a)` of
`demandReductionVal`, Bob's quasilinear payoff is **at most `2`** (`p false ≥ 4` and `p true ≥ 4`),
whereas if Bob misreports the single-item substitutes valuation `unitDemandValuation (fun j => if j
then 0 else 5)`, the zero-price outcome `p = 0` allocating `{false}` to Bob and `{true}` to Alice
is a Walrasian equilibrium giving Bob **true utility `5 > 2`**! -/
theorem demandReduction_manipulation :
    (∀ (p : Bool → ℝ) (a : Allocation Bool Bool),
      IsWalrasianEquilibrium demandReductionVal p a →
        demandReductionVal true (a.bundle true) - ∑ j ∈ a.bundle true, p j ≤ 2) ∧
    ∃ (vMis : Finset Bool → ℝ) (aMis : Allocation Bool Bool),
      IsGrossSubstitutes vMis ∧
      IsWalrasianEquilibrium (fun i => if i then vMis else demandReductionVal false)
        (fun _ => 0) aMis ∧
      demandReductionVal true (aMis.bundle true) - ∑ _j ∈ aMis.bundle true, (0 : ℝ) = 5 := by
  refine ⟨fun p a heq => ?_, ?_⟩
  · -- Any truthful Walrasian equilibrium allocation maximizes welfare (`= 10`), forcing
    -- `a.bundle true = univ` and `a.bundle false = ∅`, hence `p j ≥ 4` by Alice's demand!
    let aOpt : Allocation Bool Bool :=
      ⟨fun i => if i then univ else ∅, fun i₁ i₂ hne => by
        cases i₁ <;> cases i₂ <;> first | exact (hne rfl).elim | decide⟩
    have hw_ge := heq.welfare_le aOpt
    have hwOpt : welfare demandReductionVal aOpt = 10 := by
      norm_num [welfare, aOpt, demandReductionVal, Cslib.Algorithms.Lean.Submodular.modularSum]
    have ha_empty : a.bundle false = ∅ := by
      by_contra hne_emp
      obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.2 hne_emp
      have hd_ab : Disjoint (a.bundle false) (a.bundle true) := a.disjoint Bool.false_ne_true
      have hj_not_bob : j ∉ a.bundle true := Finset.disjoint_left.1 hd_ab hj
      have hbob_le : (a.bundle true).card ≤ 1 := by
        have hsub : a.bundle true ⊆ univ.erase j := fun x hx =>
          mem_erase.2 ⟨fun h => hj_not_bob (h ▸ hx), mem_univ x⟩
        exact (card_le_card hsub).trans (by simp)
      have halice_val : demandReductionVal false (a.bundle false) = 4 := by
        obtain ⟨b, -, hb_eq⟩ := exists_mem_unitDemandValuation_eq (w := fun _ : Bool => (4 : ℝ))
          (fun _ => by norm_num) ⟨j, hj⟩
        simpa [demandReductionVal] using hb_eq
      have hbob_val : demandReductionVal true (a.bundle true) ≤ 5 := by
        simp only [demandReductionVal, ↓reduceIte, Cslib.Algorithms.Lean.Submodular.modularSum,
          sum_const, nsmul_eq_mul]
        have : ((a.bundle true).card : ℝ) ≤ 1 := by exact_mod_cast hbob_le
        linarith
      rw [hwOpt] at hw_ge
      unfold welfare at hw_ge
      rw [Fintype.sum_bool, halice_val] at hw_ge
      linarith
    have hp_ge_4 : ∀ j : Bool, 4 ≤ p j := by
      intro j
      have hd := heq.demand false {j}
      rw [ha_empty] at hd
      norm_num [demandReductionVal] at hd
      exact hd
    by_cases hb_univ : a.bundle true = univ
    · rw [hb_univ, Fintype.sum_bool]
      simp only [demandReductionVal, ↓reduceIte, Cslib.Algorithms.Lean.Submodular.modularSum,
        sum_const, card_univ, Fintype.card_bool, nsmul_eq_mul]
      norm_num
      linarith [hp_ge_4 false, hp_ge_4 true]
    · simp only [demandReductionVal, ↓reduceIte, Cslib.Algorithms.Lean.Submodular.modularSum,
        ← sum_sub_distrib]
      calc
        ∑ j ∈ a.bundle true, (5 - p j) ≤ ∑ _j ∈ a.bundle true, (1 : ℝ) :=
          sum_le_sum fun j _ => by linarith [hp_ge_4 j]
        _ ≤ 2 := by
          rw [sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast card_le_univ (a.bundle true)
  · -- Misreported unit-demand valuation `vMis` valuing `false` at `5` and `true` at `0`.
    let wMis : Bool → ℝ := fun j => if j then 0 else 5
    let aMis : Allocation Bool Bool :=
      ⟨fun i => if i then {false} else {true}, fun i₁ i₂ hne => by
        cases i₁ <;> cases i₂ <;> first | exact (hne rfl).elim | decide⟩
    refine ⟨unitDemandValuation wMis, aMis,
      isGrossSubstitutes_unitDemandValuation (fun j => by cases j <;> simp [wMis]),
      ⟨fun _ => le_rfl, fun i S => ?_, fun _ _ => rfl⟩, ?_⟩
    · cases i
      · simp only [Bool.false_eq_true, ↓reduceIte, demandReductionVal, aMis, sum_const_zero,
          sub_zero, unitDemandValuation_singleton]
        rcases S.eq_empty_or_nonempty with rfl | hS
        · simp
        · obtain ⟨b, -, hb_eq⟩ := exists_mem_unitDemandValuation_eq
            (w := fun _ : Bool => (4 : ℝ)) (fun _ => by norm_num) hS
          rw [hb_eq]
          norm_num
      · simp only [↓reduceIte, aMis, sum_const_zero, sub_zero, unitDemandValuation_singleton, wMis,
          Bool.false_eq_true]
        rcases S.eq_empty_or_nonempty with rfl | hS
        · simp
        · obtain ⟨b, -, hb_eq⟩ := exists_mem_unitDemandValuation_eq
            (w := wMis) (fun j => by cases j <;> simp [wMis]) hS
          rw [hb_eq]
          cases b <;> simp [wMis]
    · simp [aMis, demandReductionVal, Cslib.Algorithms.Lean.Submodular.modularSum]

end KelsoCrawford

end Cslib.GameTheory.CombinatorialAuction
