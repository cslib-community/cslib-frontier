/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.SingleMinded
public import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.GrossSubstitutes
public import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Combinatorial auction bidding languages: `XOR`, `OR`, `OR`/`XOR` formulae, and `OR*`

In a combinatorial auction over a finite item set `M`, specifying an arbitrary valuation requires
`2 ^ |M| - 1` real numbers, so bidders communicate preferences via succinct *bidding languages*
built from single-minded atomic bids `(S, p)` (`SingleMinded.SingleMindedBid`)
([BlumrosenNisan2007], §11.4, pp. 279–283). This module formalizes §11.4 and Exercise 11.5 of
[BlumrosenNisan2007]:

1. **Atomic, `XOR`, and `OR` bids (§11.4.1, pp. 280–281):**
   * `xorBidEval bids S` takes the maximum of `0` and all atomic bid valuations `b.eval S`
     (`b ∈ bids`). Every normalized (`v ∅ = 0`) monotone valuation on a finite item set `M` is
     represented by an `XOR` bid of size `2 ^ |M| - 1` (`exists_xorBid_of_monotone`).
   * `orBidEval bids S` maximizes `∑ i ∈ W, (bids[i]).value` over valid collections `W` of
     pairwise-disjoint atomic bids contained in `S` (`IsValidORCollection`). For normalized
     valuations (`v ∅ = 0`), representability by an `OR` bid is equivalent to monotonicity and
     superadditivity (`IsSuperadditive`, `exists_orBid_iff_monotone_and_isSuperadditive`).
   * **Additive and unit-demand separations (Definition 11.17, pp. 280–281):** reusing
     `additiveValuation` and `unitDemandValuation` from `GrossSubstitutes`, every nonnegative
     additive valuation has an `OR` bid of size `|M|` (`exists_orBid_additiveValuation`) yet every
     `XOR` bid representing a strictly positive additive valuation requires size at least
     `2 ^ |M| - 1` (`xorBid_length_ge_additiveValuation`); conversely, every nonnegative
     unit-demand valuation has an `XOR` bid of size `|M|` (`exists_xorBid_unitDemandValuation`),
     while any unit-demand valuation with two positive-value items fails superadditivity and
     cannot be represented by any `OR` bid (`not_exists_orBid_unitDemandValuation`).
2. **General `OR`/`XOR` formulae and `OR`-of-`XOR`s (§11.4.2, pp. 281–282):**
   * `xorVal` and `orVal` formalize the binary valuation operations of Definition 11.18 (p. 281),
     with commutativity, associativity, monotonicity, and normalization lemmas.
   * `BidFormula M` formalizes general `OR`/`XOR` expressions over atomic bids (together with the
     empty `zero` formula of size `0`), agreeing with `xorBidEval` and `orBidEval` on nonnegative
     lists (`BidFormula.eval_ofXorList`, `BidFormula.eval_ofOrList`).
   * **Downward-sloping symmetric valuations (Definition 11.19, Lemma 11.20, p. 281):** reusing
     `downwardSlopingValuation` from `GrossSubstitutes`, strictly positive marginals force `XOR`
     size at least `2 ^ |M| - 1` (`xorBid_length_ge_downwardSlopingValuation`), strictly decreasing
     first marginals (`w 1 < w 0`, `2 ≤ |M|`) rule out `OR` representation
     (`not_exists_orBid_downwardSlopingValuation`), and **Lemma 11.20**
     (`exists_orOfXor_downwardSlopingValuation`) represents any downward-sloping symmetric
     valuation on `m = |M|` items by an `OR`-of-`XOR`s formula of size `m ^ 2`.
3. **Dummy items and `OR*` simulation (§11.4.3, Theorem 11.21, pp. 282–283):**
   * `ORStarBid M D` represents an `OR` bid on `M ⊕ D` evaluated at `S : Finset M` via
     `orBidEval b.bids (S.disjSum Finset.univ)`.
   * **Theorem 11.21** (`exists_orStarBid_of_bidFormula`): every `OR`/`XOR` formula `f` of size
     `s` with nonnegative atomic prices is represented by an `OR*` bid of size `s` using at most
     `s.choose 2` (hence at most `s ^ 2`) dummy items, constructed via the formula's pairwise
     `XOR`-conflict graph.
4. **Threshold and majority valuation `OR*` lower bound (Exercise 11.5, p. 299):**
   * Every `OR*` bid representing the `k`-threshold valuation `thresholdValuation k` requires size
     at least `(|M|).choose k` (`thresholdValuation_orStarBid_size_ge`).
   * Specializing to `majorityValuation M` (`thresholdValuation ((|M| + 1) / 2)`, matching
     `(|M| : ℝ) / 2 ≤ S.card` for every `|M| : ℕ`) yields **Exercise 11.5**
     (`majorityValuation_orStarBid_size_ge`): every `OR*` representation has size at least
     `(|M|).choose (|M| / 2)`.

## Precision notes on the printed source

1. **Empty atomic bundles in `OR` bids (§11.4.1, p. 280):** an `OR` bid containing a positive-price
   empty-bundle atom `(∅, p)` with `p > 0` has `orBidEval bids ∅ ≥ p > 0` and can fail
   superadditivity (for example `[(∅, 1)]` gives `v {a} = v {b} = v {a, b} = 1`). Under
   normalization `orBidEval bids ∅ = 0` (which holds automatically whenever all atomic bundles are
   nonempty), `orBidEval bids` is always superadditive without even needing nonnegativity of
   atomic prices (`orBidEval_isSuperadditive`).
2. **Superadditivity quantifier (§11.4.1, p. 280 vs. Exercise 11.7, p. 299):** `IsSuperadditive`
   requires `v S + v T ≤ v (S ∪ T)` for **disjoint** bundles `S, T`, as explicitly stated on
   p. 280.
3. **Majority threshold for odd `m` (Exercise 11.5, p. 299):** the printed text assigns value `1`
   to any bundle of at least `m / 2` items; over `ℕ`, `(m : ℝ) / 2 ≤ S.card` is equivalent to
   `(m + 1) / 2 ≤ S.card`, which preserves normalization `v ∅ = 0` for all `m ≥ 1` while sharing
   the identical binomial bound `m.choose ((m + 1) / 2) = m.choose (m / 2)`.

## Main definitions

* `Cslib.GameTheory.CombinatorialAuction.IsSuperadditive`: superadditivity on disjoint bundles
  ([BlumrosenNisan2007], §11.4.1, p. 280).
* `Cslib.GameTheory.CombinatorialAuction.xorBidEval`,
  `Cslib.GameTheory.CombinatorialAuction.IsValidORCollection`,
  `Cslib.GameTheory.CombinatorialAuction.orBidEval`: `XOR` and `OR` bid semantics
  ([BlumrosenNisan2007], §11.4.1, p. 280).
* `Cslib.GameTheory.CombinatorialAuction.xorVal`,
  `Cslib.GameTheory.CombinatorialAuction.orVal`: binary `XOR` and `OR` operations on valuations
  ([BlumrosenNisan2007], Definition 11.18, p. 281).
* `Cslib.GameTheory.CombinatorialAuction.BidFormula`, `BidFormula.eval`, `BidFormula.size`,
  `BidFormula.atoms`, `BidFormula.IsXorFormula`, `BidFormula.IsOrOfXor`, `BidFormula.ofXorList`,
  `BidFormula.ofOrList`, `BidFormula.ofOrFormulaList`: general `OR`/`XOR` formulae and
  `OR`-of-`XOR`s ([BlumrosenNisan2007], §11.4.2, p. 281).
* `Cslib.GameTheory.CombinatorialAuction.ORStarBid`, `ORStarBid.eval`, `ORStarBid.size`: `OR*`
  bids with dummy items ([BlumrosenNisan2007], §11.4.3, p. 282).
* `Cslib.GameTheory.CombinatorialAuction.thresholdValuation`,
  `Cslib.GameTheory.CombinatorialAuction.majorityValuation`: `k`-threshold and majority
  valuations ([BlumrosenNisan2007], Exercise 11.5, p. 299).

## Main results

* `Cslib.GameTheory.CombinatorialAuction.exists_xorBid_of_monotone`: `XOR` universality in size
  `2 ^ |M| - 1` ([BlumrosenNisan2007], §11.4.1, p. 280).
* `Cslib.GameTheory.CombinatorialAuction.exists_orBid_of_isSuperadditive`,
  `Cslib.GameTheory.CombinatorialAuction.exists_orBid_iff_monotone_and_isSuperadditive`: exact
  superadditivity characterization of `OR`-representable normalized valuations
  ([BlumrosenNisan2007], §11.4.1, p. 280).
* `Cslib.GameTheory.CombinatorialAuction.exists_orBid_additiveValuation`,
  `Cslib.GameTheory.CombinatorialAuction.xorBid_length_ge_additiveValuation`,
  `Cslib.GameTheory.CombinatorialAuction.exists_xorBid_unitDemandValuation`,
  `Cslib.GameTheory.CombinatorialAuction.not_exists_orBid_unitDemandValuation`: exponential and
  expressiveness separations between `OR` and `XOR` on additive and unit-demand valuations
  ([BlumrosenNisan2007], §11.4.1, Definition 11.17, pp. 280–281).
* `Cslib.GameTheory.CombinatorialAuction.xorBid_length_ge_downwardSlopingValuation`,
  `Cslib.GameTheory.CombinatorialAuction.not_exists_orBid_downwardSlopingValuation`,
  `Cslib.GameTheory.CombinatorialAuction.exists_orOfXor_downwardSlopingValuation`: **Lemma 11.20**
  ([BlumrosenNisan2007], §11.4.2, p. 281) — downward-sloping symmetric valuations have size `m ^ 2`
  `OR`-of-`XOR`s representations, while escaping `OR` and requiring size `2 ^ m - 1` in `XOR`.
* `Cslib.GameTheory.CombinatorialAuction.exists_orStarBid_of_bidFormula`: **Theorem 11.21**
  ([BlumrosenNisan2007], §11.4.3, pp. 282–283) — every `OR`/`XOR` formula of size `s` is simulated
  by an `OR*` bid of size `s` using at most `s.choose 2` (≤ `s ^ 2`) dummy items.
* `Cslib.GameTheory.CombinatorialAuction.thresholdValuation_orStarBid_size_ge`,
  `Cslib.GameTheory.CombinatorialAuction.majorityValuation_orStarBid_size_ge`: **Exercise 11.5**
  ([BlumrosenNisan2007], p. 299) — `OR*` representation of `majorityValuation M` requires size at
  least `(|M|).choose (|M| / 2)`.

## References

* [L. Blumrosen and N. Nisan, *Combinatorial Auctions*][BlumrosenNisan2007], Chapter 11,
  §11.4 (pp. 279–283) and Exercise 11.5 (p. 299).
-/

public section

namespace Cslib.GameTheory.CombinatorialAuction

open Finset SingleMinded

/-! ### Superadditivity, `XOR` bids, and `OR` bids (§11.4.1) -/

section OrXorBids

variable {M : Type*}

/-- A valuation `v : Finset M → ℝ` is **superadditive** if `v S + v T ≤ v (S ∪ T)` for all
disjoint bundles `S` and `T` ([BlumrosenNisan2007], §11.4.1, p. 280). -/
@[expose] def IsSuperadditive [DecidableEq M] (v : Finset M → ℝ) : Prop :=
  ∀ ⦃S T : Finset M⦄, Disjoint S T → v S + v T ≤ v (S ∪ T)

private theorem sum_le_of_isSuperadditive [DecidableEq M] {ι : Type*}
    {v : Finset M → ℝ} (hv0 : v ∅ = 0) (hsup : IsSuperadditive v)
    (W : Finset ι) {f : ι → Finset M} (hdisj : (W : Set ι).PairwiseDisjoint f) :
    ∑ i ∈ W, v (f i) ≤ v (W.biUnion f) := by
  classical
  induction W using Finset.induction with
  | empty => simp [hv0]
  | insert i W hiW ih =>
    have hW_disj : (W : Set ι).PairwiseDisjoint f :=
      hdisj.subset (Finset.coe_subset.mpr (subset_insert i W))
    have hi_disj : Disjoint (f i) (W.biUnion f) := by
      rw [Finset.disjoint_left]
      intro x hxi hxW
      obtain ⟨j, hjW, hxj⟩ := mem_biUnion.mp hxW
      exact Finset.disjoint_left.mp
        (hdisj (mem_insert_self i W) (mem_insert_of_mem hjW) (fun h => hiW (h ▸ hjW))) hxi hxj
    rw [sum_insert hiW, biUnion_insert]
    exact (add_le_add le_rfl (ih hW_disj)).trans (hsup hi_disj)

/-- Evaluation of an `XOR` bid `(S₁, p₁) XOR ⋯ XOR (Sₖ, pₖ)` at bundle `S`: the maximum of `0`
and all atomic bid valuations `b.eval S` for `b ∈ bids` ([BlumrosenNisan2007], §11.4.1, p. 280).
For nonnegative atomic bids, this equals `max_{i | Sᵢ ⊆ S} pᵢ` (and `0` if no `Sᵢ ⊆ S`). -/
@[expose] def xorBidEval [DecidableEq M] (bids : List (SingleMindedBid M)) (S : Finset M) : ℝ :=
  bids.foldr (fun bid acc => max (bid.eval S) acc) 0

@[simp] theorem xorBidEval_nil [DecidableEq M] (S : Finset M) :
    xorBidEval ([] : List (SingleMindedBid M)) S = 0 := rfl

@[simp] theorem xorBidEval_cons [DecidableEq M] (bid : SingleMindedBid M)
    (bids : List (SingleMindedBid M)) (S : Finset M) :
    xorBidEval (bid :: bids) S = max (bid.eval S) (xorBidEval bids S) := rfl

/-- Every `XOR` bid evaluation is nonnegative. -/
theorem xorBidEval_nonneg [DecidableEq M] (bids : List (SingleMindedBid M)) (S : Finset M) :
    0 ≤ xorBidEval bids S := by
  induction bids with
  | nil => exact le_rfl
  | cons b bs ih => exact ih.trans (le_max_right _ _)

/-- Every atomic bid in `bids` lower-bounds `xorBidEval bids S`. -/
theorem le_xorBidEval_of_mem [DecidableEq M] {bids : List (SingleMindedBid M)}
    {b : SingleMindedBid M} (hb : b ∈ bids) (S : Finset M) :
    b.eval S ≤ xorBidEval bids S := by
  induction bids with
  | nil => exact (List.not_mem_nil hb).elim
  | cons a bs ih =>
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact le_max_left _ _
    · exact (ih hb').trans (le_max_right _ _)

/-- Characterization of upper bounds on `xorBidEval bids S`. -/
theorem xorBidEval_le_iff [DecidableEq M] {bids : List (SingleMindedBid M)} {S : Finset M}
    {c : ℝ} :
    xorBidEval bids S ≤ c ↔ 0 ≤ c ∧ ∀ b ∈ bids, b.eval S ≤ c := by
  induction bids with
  | nil => simp
  | cons a bs ih =>
    simp only [xorBidEval_cons, max_le_iff, ih, List.mem_cons, forall_eq_or_imp]
    tauto

/-- If `xorBidEval bids S > 0`, some atomic bid in `bids` attains it. -/
private theorem exists_mem_xorBidEval_eq_of_pos [DecidableEq M] {bids : List (SingleMindedBid M)}
    {S : Finset M} (hpos : 0 < xorBidEval bids S) :
    ∃ b ∈ bids, b.eval S = xorBidEval bids S := by
  induction bids with
  | nil => simp at hpos
  | cons a bs ih =>
    rw [xorBidEval_cons] at hpos ⊢
    rcases max_choice (a.eval S) (xorBidEval bs S) with h | h
    · exact ⟨a, List.mem_cons_self .., h.symm⟩
    · rw [h] at hpos ⊢
      obtain ⟨b, hb, hbeq⟩ := ih hpos
      exact ⟨b, List.mem_cons_of_mem a hb, hbeq⟩

/-- Every `XOR` bid defines a monotone valuation ("free disposal"). -/
theorem xorBidEval_monotone [DecidableEq M] (bids : List (SingleMindedBid M)) :
    Monotone (xorBidEval bids) := by
  intro S T hST
  rw [xorBidEval_le_iff]
  refine ⟨xorBidEval_nonneg bids T, fun b hb => ?_⟩
  by_cases hsub : b.bundle ⊆ S
  · have hT : b.bundle ⊆ T := hsub.trans hST
    have heq : b.eval S = b.eval T := by simp [SingleMindedBid.eval, hsub, hT]
    rw [heq]
    exact le_xorBidEval_of_mem hb T
  · simp only [SingleMindedBid.eval, hsub, ↓reduceIte]
    exact xorBidEval_nonneg bids T

/-- If every atomic bid has a nonempty bundle, `xorBidEval bids` is normalized (`v ∅ = 0`). -/
theorem xorBidEval_empty_of_nonempty [DecidableEq M] {bids : List (SingleMindedBid M)}
    (hne : ∀ b ∈ bids, b.bundle.Nonempty) : xorBidEval bids ∅ = 0 := by
  refine le_antisymm ?_ (xorBidEval_nonneg bids ∅)
  rw [xorBidEval_le_iff]
  exact ⟨le_rfl, fun b hb => (SingleMindedBid.eval_empty_of_nonempty (hne b hb)).le⟩

/-- A subset `W : Finset (Fin bids.length)` of atomic-bid indices is a *valid collection* for
bundle `S` in an `OR` bid if the selected atomic bids have pairwise disjoint bundles and each
selected bundle is contained in `S` ([BlumrosenNisan2007], §11.4.1, p. 280). -/
@[expose] def IsValidORCollection (bids : List (SingleMindedBid M))
    (S : Finset M) (W : Finset (Fin bids.length)) : Prop :=
  IsCompatible (fun i : Fin bids.length => bids[i]) W ∧
    ∀ i ∈ W, (bids[i]).bundle ⊆ S

private theorem isValidORCollection_empty (bids : List (SingleMindedBid M))
    (S : Finset M) : IsValidORCollection bids S ∅ :=
  ⟨by simp [IsCompatible], fun _ h => (notMem_empty _ h).elim⟩

private theorem validORCollections_nonempty
    (bids : List (SingleMindedBid M)) (S : Finset M) [DecidablePred (IsValidORCollection bids S)] :
    ((Finset.univ : Finset (Finset (Fin bids.length))).filter
      (IsValidORCollection bids S)).Nonempty :=
  ⟨∅, mem_filter.mpr ⟨mem_univ ∅, isValidORCollection_empty bids S⟩⟩

/-- Evaluation of an `OR` bid `(S₁, p₁) OR ⋯ OR (Sₖ, pₖ)` at bundle `S`: the maximum of
`∑ i ∈ W, pᵢ` over all valid (pairwise disjoint, contained in `S`) collections `W` of atomic bids
([BlumrosenNisan2007], §11.4.1, p. 280). -/
noncomputable def orBidEval (bids : List (SingleMindedBid M))
    (S : Finset M) : ℝ :=
  open Classical in
  ((Finset.univ : Finset (Finset (Fin bids.length))).filter
    (IsValidORCollection bids S)).sup'
    (validORCollections_nonempty bids S)
    (fun W => ∑ i ∈ W, (bids[i]).value)

/-- Every valid collection `W` for `S` lower-bounds `orBidEval bids S`. -/
theorem le_orBidEval {bids : List (SingleMindedBid M)} {S : Finset M}
    {W : Finset (Fin bids.length)} (hW : IsValidORCollection bids S W) :
    ∑ i ∈ W, (bids[i]).value ≤ orBidEval bids S := by
  classical
  exact le_sup' (fun W => ∑ i ∈ W, (bids[i]).value) (mem_filter.mpr ⟨mem_univ W, hW⟩)

/-- Characterization of upper bounds on `orBidEval bids S`. -/
theorem orBidEval_le_iff {bids : List (SingleMindedBid M)} {S : Finset M}
    {c : ℝ} :
    orBidEval bids S ≤ c ↔
      ∀ W : Finset (Fin bids.length), IsValidORCollection bids S W →
        ∑ i ∈ W, (bids[i]).value ≤ c := by
  classical
  unfold orBidEval
  rw [sup'_le_iff]
  exact ⟨fun h W hW => h W (mem_filter.mpr ⟨mem_univ W, hW⟩),
    fun h W hW => h W (mem_filter.mp hW).2⟩

/-- `orBidEval bids S` is attained by some valid collection `W`. -/
theorem exists_isValidORCollection_eq (bids : List (SingleMindedBid M))
    (S : Finset M) :
    ∃ W : Finset (Fin bids.length),
      IsValidORCollection bids S W ∧ orBidEval bids S = ∑ i ∈ W, (bids[i]).value := by
  classical
  obtain ⟨W, hWmem, hWeq⟩ :=
    exists_mem_eq_sup' (validORCollections_nonempty bids S) (fun W => ∑ i ∈ W, (bids[i]).value)
  exact ⟨W, (mem_filter.mp hWmem).2, hWeq⟩

@[simp] theorem orBidEval_nil (S : Finset M) :
    orBidEval ([] : List (SingleMindedBid M)) S = 0 := by
  refine le_antisymm ?_ ?_
  · rw [orBidEval_le_iff]
    intro W _
    have hW : W = ∅ := eq_empty_of_forall_notMem fun i => Fin.elim0 i
    simp [hW]
  · simpa using le_orBidEval (isValidORCollection_empty ([] : List (SingleMindedBid M)) S)

/-- Every `OR` bid evaluation is nonnegative (witnessed by the empty collection `W = ∅`). -/
theorem orBidEval_nonneg (bids : List (SingleMindedBid M)) (S : Finset M) :
    0 ≤ orBidEval bids S := by
  simpa using le_orBidEval (isValidORCollection_empty bids S)

/-- Every `OR` bid defines a monotone valuation ("free disposal"). -/
theorem orBidEval_monotone (bids : List (SingleMindedBid M)) :
    Monotone (orBidEval bids) := by
  intro S T hST
  rw [orBidEval_le_iff]
  intro W hW
  exact le_orBidEval ⟨hW.1, fun i hi => (hW.2 i hi).trans hST⟩

/-- If every atomic bid has a nonempty bundle, `orBidEval bids` is normalized (`v ∅ = 0`). -/
theorem orBidEval_empty_of_nonempty {bids : List (SingleMindedBid M)}
    (hne : ∀ b ∈ bids, b.bundle.Nonempty) : orBidEval bids ∅ = 0 := by
  refine le_antisymm ?_ (orBidEval_nonneg bids ∅)
  rw [orBidEval_le_iff]
  intro W hW
  have hWe : W = ∅ := eq_empty_of_forall_notMem fun i hi =>
    (hne _ (List.getElem_mem i.isLt)).ne_empty (subset_empty.mp (hW.2 i hi))
  simp [hWe]

/-- Every normalized `OR` bid valuation (`orBidEval bids ∅ = 0`, in particular every `OR` bid with
nonempty atomic bundles) is superadditive ([BlumrosenNisan2007], §11.4.1, p. 280). No nonnegativity
hypothesis on atomic prices is needed: any empty-bundle atom must have nonpositive price by
`h0`, so dropping empty-bundle atoms from maximizing collections on disjoint bundles `S, T`
yields disjoint collections whose union is valid on `S ∪ T`. -/
theorem orBidEval_isSuperadditive [DecidableEq M] {bids : List (SingleMindedBid M)}
    (h0 : orBidEval bids ∅ = 0) : IsSuperadditive (orBidEval bids) := by
  intro S T hST
  have hempty_nonpos : ∀ i : Fin bids.length, (bids[i]).bundle = ∅ → (bids[i]).value ≤ 0 := by
    intro i hi
    have hval : IsValidORCollection bids ∅ {i} :=
      ⟨by simp [IsCompatible], fun j hj => by rw [mem_singleton.mp hj, hi]⟩
    have hle := le_orBidEval hval
    simp only [sum_singleton, h0] at hle
    exact hle
  obtain ⟨W₁, hW₁, hEq₁⟩ := exists_isValidORCollection_eq bids S
  obtain ⟨W₂, hW₂, hEq₂⟩ := exists_isValidORCollection_eq bids T
  let W₁' := W₁.filter fun i => (bids[i]).bundle.Nonempty
  let W₂' := W₂.filter fun i => (bids[i]).bundle.Nonempty
  have hsum_drop : ∀ W : Finset (Fin bids.length),
      ∑ i ∈ W, (bids[i]).value ≤
        ∑ i ∈ W.filter (fun i => (bids[i]).bundle.Nonempty), (bids[i]).value := by
    intro W
    have hsplit := sum_filter_add_sum_filter_not W (fun i => (bids[i]).bundle.Nonempty)
      (fun i => (bids[i]).value)
    have hrest : ∑ i ∈ W.filter (fun i => ¬ (bids[i]).bundle.Nonempty), (bids[i]).value ≤ 0 :=
      sum_nonpos fun i hi => hempty_nonpos i (not_nonempty_iff_eq_empty.mp (mem_filter.mp hi).2)
    linarith
  have hdisjW : Disjoint W₁' W₂' := by
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    obtain ⟨x, hx⟩ := (mem_filter.mp hi₁).2
    exact Finset.disjoint_left.mp hST
      (hW₁.2 i (mem_filter.mp hi₁).1 hx) (hW₂.2 i (mem_filter.mp hi₂).1 hx)
  have hvalidU : IsValidORCollection bids (S ∪ T) (W₁' ∪ W₂') := by
    refine ⟨?_, fun i hi => ?_⟩
    · intro i hi j hj hij
      rcases mem_union.mp hi with hi₁ | hi₂ <;> rcases mem_union.mp hj with hj₁ | hj₂
      · exact hW₁.1 (mem_filter.mp hi₁).1 (mem_filter.mp hj₁).1 hij
      · exact hST.mono (hW₁.2 i (mem_filter.mp hi₁).1) (hW₂.2 j (mem_filter.mp hj₂).1)
      · exact hST.symm.mono (hW₂.2 i (mem_filter.mp hi₂).1) (hW₁.2 j (mem_filter.mp hj₁).1)
      · exact hW₂.1 (mem_filter.mp hi₂).1 (mem_filter.mp hj₂).1 hij
    · rcases mem_union.mp hi with hi₁ | hi₂
      · exact (hW₁.2 i (mem_filter.mp hi₁).1).trans subset_union_left
      · exact (hW₂.2 i (mem_filter.mp hi₂).1).trans subset_union_right
  calc
    orBidEval bids S + orBidEval bids T
        = ∑ i ∈ W₁, (bids[i]).value + ∑ i ∈ W₂, (bids[i]).value := by rw [hEq₁, hEq₂]
    _ ≤ ∑ i ∈ W₁', (bids[i]).value + ∑ i ∈ W₂', (bids[i]).value :=
          add_le_add (hsum_drop W₁) (hsum_drop W₂)
    _ = ∑ i ∈ W₁' ∪ W₂', (bids[i]).value := (sum_union hdisjW).symm
    _ ≤ orBidEval bids (S ∪ T) := le_orBidEval hvalidU

private lemma card_nonempty_finsets [Fintype M] :
    ((Finset.univ : Finset (Finset M)).filter Finset.Nonempty).card = 2 ^ Fintype.card M - 1 := by
  classical
  have hfilter : (Finset.univ : Finset (Finset M)).filter Finset.Nonempty =
      (Finset.univ : Finset (Finset M)).erase ∅ := by
    ext S
    simp [nonempty_iff_ne_empty]
  rw [hfilter, card_erase_of_mem (mem_univ ∅), card_univ, Fintype.card_finset]

/-- **`XOR` universality** ([BlumrosenNisan2007], §11.4.1, p. 280): every normalized (`v ∅ = 0`),
monotone valuation on a finite item set `M` is represented by an `XOR` bid of size
`2 ^ |M| - 1` whose atomic bids are all nonempty bundles `(S, v S)` (with nonnegative values). -/
theorem exists_xorBid_of_monotone [Fintype M] [DecidableEq M] {v : Finset M → ℝ}
    (hv0 : v ∅ = 0) (hmono : Monotone v) :
    ∃ bids : List (SingleMindedBid M),
      bids.length = 2 ^ Fintype.card M - 1 ∧
      (∀ b ∈ bids, b.bundle.Nonempty ∧ 0 ≤ b.value) ∧
      xorBidEval bids = v := by
  let nonemptyBundles : Finset (Finset M) :=
    (Finset.univ : Finset (Finset M)).filter Finset.Nonempty
  let bids : List (SingleMindedBid M) := nonemptyBundles.toList.map fun T => ⟨T, v T⟩
  refine ⟨bids, ?_, ?_, ?_⟩
  · simp [bids, nonemptyBundles, card_nonempty_finsets]
  · intro b hb
    rcases List.mem_map.mp hb with ⟨T, hT, rfl⟩
    have hTne : T.Nonempty := (mem_filter.mp (mem_toList.mp hT)).2
    exact ⟨hTne, hv0.symm.trans_le (hmono (empty_subset T))⟩
  · funext S
    refine le_antisymm ?_ ?_
    · rw [xorBidEval_le_iff]
      refine ⟨hv0.symm.trans_le (hmono (empty_subset S)), fun b hb => ?_⟩
      rcases List.mem_map.mp hb with ⟨T, _, rfl⟩
      by_cases hTS : T ⊆ S
      · simp only [SingleMindedBid.eval, hTS, ↓reduceIte]
        exact hmono hTS
      · simp only [SingleMindedBid.eval, hTS, ↓reduceIte]
        exact hv0.symm.trans_le (hmono (empty_subset S))
    · rcases S.eq_empty_or_nonempty with rfl | hSne
      · rw [hv0]
        exact xorBidEval_nonneg bids ∅
      · have hmem : ⟨S, v S⟩ ∈ bids :=
          List.mem_map.mpr ⟨S, mem_toList.mpr (mem_filter.mpr ⟨mem_univ S, hSne⟩), rfl⟩
        have hle := le_xorBidEval_of_mem hmem S
        simpa only [SingleMindedBid.eval, Subset.rfl, ↓reduceIte] using hle

/-- **`OR` representability of superadditive valuations** ([BlumrosenNisan2007], §11.4.1, p. 280):
every normalized (`v ∅ = 0`), monotone, superadditive valuation on a finite item set `M` is
represented by an `OR` bid of size `2 ^ |M| - 1` using all nonempty bundles `(S, v S)`. -/
theorem exists_orBid_of_isSuperadditive [Fintype M] [DecidableEq M] {v : Finset M → ℝ}
    (hv0 : v ∅ = 0) (hmono : Monotone v) (hsup : IsSuperadditive v) :
    ∃ bids : List (SingleMindedBid M),
      bids.length = 2 ^ Fintype.card M - 1 ∧
      (∀ b ∈ bids, b.bundle.Nonempty ∧ 0 ≤ b.value) ∧
      orBidEval bids = v := by
  let nonemptyBundles : Finset (Finset M) :=
    (Finset.univ : Finset (Finset M)).filter Finset.Nonempty
  let bids : List (SingleMindedBid M) := nonemptyBundles.toList.map fun T => ⟨T, v T⟩
  have hval_eq : ∀ b ∈ bids, b.value = v b.bundle := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨T, _, rfl⟩
    rfl
  refine ⟨bids, ?_, ?_, ?_⟩
  · simp [bids, nonemptyBundles, card_nonempty_finsets]
  · intro b hb
    rcases List.mem_map.mp hb with ⟨T, hT, rfl⟩
    have hTne : T.Nonempty := (mem_filter.mp (mem_toList.mp hT)).2
    exact ⟨hTne, hv0.symm.trans_le (hmono (empty_subset T))⟩
  · funext S
    refine le_antisymm ?_ ?_
    · rw [orBidEval_le_iff]
      intro W hW
      have hrewrite : ∑ i ∈ W, (bids[i]).value = ∑ i ∈ W, v (bids[i]).bundle :=
        sum_congr rfl fun i _ => hval_eq _ (List.getElem_mem i.isLt)
      rw [hrewrite]
      exact (sum_le_of_isSuperadditive hv0 hsup W hW.1).trans
        (hmono (biUnion_subset.mpr hW.2))
    · rcases S.eq_empty_or_nonempty with rfl | hSne
      · rw [hv0]
        exact orBidEval_nonneg bids ∅
      · have hmem : ⟨S, v S⟩ ∈ bids :=
          List.mem_map.mpr ⟨S, mem_toList.mpr (mem_filter.mpr ⟨mem_univ S, hSne⟩), rfl⟩
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
        have hvalid : IsValidORCollection bids S {i} :=
          ⟨by simp [IsCompatible], fun j hj => by
            rw [mem_singleton.mp hj]
            change (bids.get i).bundle ⊆ S
            rw [hi]⟩
        have hle := le_orBidEval hvalid
        simp only [sum_singleton] at hle
        change (bids.get i).value ≤ orBidEval bids S at hle
        rwa [hi] at hle

/-- **Characterization of `OR`-representable valuations** ([BlumrosenNisan2007], §11.4.1, p. 280):
a normalized valuation (`v ∅ = 0`) on a finite item set `M` is representable by an `OR` bid if and
only if it is monotone and superadditive. -/
theorem exists_orBid_iff_monotone_and_isSuperadditive [Finite M] [DecidableEq M]
    {v : Finset M → ℝ} (hv0 : v ∅ = 0) :
    (∃ bids : List (SingleMindedBid M), orBidEval bids = v) ↔
      Monotone v ∧ IsSuperadditive v := by
  have := Fintype.ofFinite M
  exact ⟨fun ⟨bids, h⟩ => ⟨h ▸ orBidEval_monotone bids,
      h ▸ orBidEval_isSuperadditive (by rw [h, hv0])⟩,
   fun ⟨hmono, hsup⟩ =>
      let ⟨bids, _, _, h⟩ := exists_orBid_of_isSuperadditive hv0 hmono hsup
      ⟨bids, h⟩⟩

/-- **Necessary atomic-bid criterion for `XOR` bids** ([BlumrosenNisan2007], §11.4.1, p. 281):
if `xorBidEval bids = v` and bundle `S` has positive value strictly exceeding every strict subset
`T ⊂ S`, then `⟨S, v S⟩` must appear explicitly in `bids`. -/
theorem mem_xorBid_of_strict_subset_lt [DecidableEq M] {bids : List (SingleMindedBid M)}
    {v : Finset M → ℝ} (heq : xorBidEval bids = v) {S : Finset M}
    (hpos : 0 < v S) (hstrict : ∀ T : Finset M, T ⊂ S → v T < v S) :
    ⟨S, v S⟩ ∈ bids := by
  have hpos' : 0 < xorBidEval bids S := by rwa [heq]
  obtain ⟨b, hb, hbeq⟩ := exists_mem_xorBidEval_eq_of_pos hpos'
  rw [heq] at hbeq
  have hsub : b.bundle ⊆ S := by
    by_contra hnot
    simp only [SingleMindedBid.eval, hnot, ↓reduceIte] at hbeq
    linarith
  have hval : b.value = v S := by
    simpa only [SingleMindedBid.eval, hsub, ↓reduceIte] using hbeq
  have hbun : b.bundle = S := by
    by_contra hne
    have hss : b.bundle ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    have hle : b.value ≤ v b.bundle := by
      have h1 := le_xorBidEval_of_mem hb b.bundle
      rw [SingleMindedBid.eval_self, heq] at h1
      exact h1
    linarith [hstrict b.bundle hss]
  have hb_eq : b = ⟨S, v S⟩ := SingleMindedBid.ext hbun hval
  exact hb_eq ▸ hb

/-- Any `XOR` bid representing a strictly monotone valuation with `0 ≤ v ∅` on finite `M` has
size at least `2 ^ |M| - 1` ([BlumrosenNisan2007], §11.4.1, p. 281). -/
theorem xorBid_length_ge_of_strictMono [Fintype M] [DecidableEq M]
    {bids : List (SingleMindedBid M)} {v : Finset M → ℝ}
    (heq : xorBidEval bids = v) (hv0 : 0 ≤ v ∅) (hstrict : StrictMono v) :
    2 ^ Fintype.card M - 1 ≤ bids.length := by
  let nonemptyBundles : Finset (Finset M) :=
    (Finset.univ : Finset (Finset M)).filter Finset.Nonempty
  have hsub : nonemptyBundles ⊆ (bids.map SingleMindedBid.bundle).toFinset := by
    intro S hS
    have hSne : S.Nonempty := (mem_filter.mp hS).2
    have hpos : 0 < v S := lt_of_le_of_lt hv0 (hstrict (empty_ssubset.mpr hSne))
    have hmem := mem_xorBid_of_strict_subset_lt heq hpos fun T hTS => hstrict hTS
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨⟨S, v S⟩, hmem, rfl⟩)
  calc
    2 ^ Fintype.card M - 1 = nonemptyBundles.card := card_nonempty_finsets.symm
    _ ≤ (bids.map SingleMindedBid.bundle).toFinset.card := card_le_card hsub
    _ ≤ (bids.map SingleMindedBid.bundle).length := List.toFinset_card_le _
    _ = bids.length := List.length_map _

/-! ### Additive and unit-demand separations (Definition 11.17, pp. 280–281) -/

/-- Every nonnegative additive valuation (`additiveValuation w`) is represented by an `OR` bid of
size `|M|` consisting of the single-item atomic bids `({j}, w j)` ([BlumrosenNisan2007], §11.4.1,
Definition 11.17, p. 280). -/
theorem exists_orBid_additiveValuation [Fintype M] {w : M → ℝ}
    (hw : ∀ j, 0 ≤ w j) :
    ∃ bids : List (SingleMindedBid M),
      bids.length = Fintype.card M ∧
      (∀ b ∈ bids, b.bundle.Nonempty ∧ 0 ≤ b.value) ∧
      orBidEval bids = additiveValuation w := by
  classical
  let items : List M := (Finset.univ : Finset M).toList
  have hnd : items.Nodup := nodup_toList _
  let bids : List (SingleMindedBid M) := items.map fun j => ⟨{j}, w j⟩
  refine ⟨bids, ?_, ?_, ?_⟩
  · simp [bids, items]
  · intro b hb
    rcases List.mem_map.mp hb with ⟨j, _, rfl⟩
    exact ⟨singleton_nonempty j, hw j⟩
  · funext S
    have hitem_eq : ∀ i : Fin bids.length,
        bids[i] = ⟨{items[i.val]'(by simpa [bids] using i.isLt)},
          w (items[i.val]'(by simpa [bids] using i.isLt))⟩ := by
      intro i
      simp [bids]
    let f : Fin bids.length → M := fun i => items[i.val]'(by simpa [bids] using i.isLt)
    have hf_inj : Function.Injective f := by
      intro i j hij
      have hget : items.get ⟨i.val, by simpa [bids] using i.isLt⟩ =
          items.get ⟨j.val, by simpa [bids] using j.isLt⟩ := hij
      exact Fin.ext (Fin.mk.inj (List.nodup_iff_injective_get.mp hnd hget))
    have hf_surj : Function.Surjective f := by
      intro x
      have hx : x ∈ items := mem_toList.mpr (mem_univ x)
      obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hx
      exact ⟨⟨k, by simpa [bids] using hk⟩, hkx⟩
    refine le_antisymm ?_ ?_
    · rw [orBidEval_le_iff]
      intro W hW
      have hWsum : ∑ i ∈ W, (bids[i]).value = ∑ x ∈ W.image f, w x := by
        rw [sum_image fun a _ b _ h => hf_inj h]
        refine sum_congr rfl fun i _ => ?_
        rw [hitem_eq i]
      rw [hWsum]
      refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun j _ _ => hw j)
      rcases mem_image.mp hx with ⟨i, hiW, rfl⟩
      have hsub := hW.2 i hiW
      rw [hitem_eq i] at hsub
      exact singleton_subset_iff.mp hsub
    · let W : Finset (Fin bids.length) := Finset.univ.filter fun i => f i ∈ S
      have hvalid : IsValidORCollection bids S W := by
        refine ⟨fun i _ j _ hij => ?_, fun i hi => ?_⟩
        · dsimp only [Function.onFun]
          rw [hitem_eq i, hitem_eq j]
          exact disjoint_singleton.mpr fun h => hij (hf_inj h)
        · rw [hitem_eq i]
          exact singleton_subset_iff.mpr (mem_filter.mp hi).2
      have hW_img : W.image f = S := by
        ext x
        simp only [mem_image, W, mem_filter, mem_univ, true_and]
        exact ⟨fun ⟨_, hi, hfx⟩ => hfx ▸ hi,
          fun hx => let ⟨i, hi⟩ := hf_surj x; ⟨i, hi.symm ▸ hx, hi⟩⟩
      have hWsum : ∑ i ∈ W, (bids[i]).value = additiveValuation w S := by
        calc
          ∑ i ∈ W, (bids[i]).value = ∑ i ∈ W, w (f i) :=
            sum_congr rfl fun i _ => by rw [hitem_eq i]
          _ = ∑ x ∈ W.image f, w x := (sum_image fun a _ b _ h => hf_inj h).symm
          _ = additiveValuation w S := by rw [hW_img]; rfl
      exact hWsum.symm.trans_le (le_orBidEval hvalid)

/-- Every `XOR` bid representing a strictly positive additive valuation (`∀ j, 0 < w j`) on a
finite item set `M` requires at least `2 ^ |M| - 1` atomic bids ([BlumrosenNisan2007], §11.4.1,
p. 281). -/
theorem xorBid_length_ge_additiveValuation [Fintype M] [DecidableEq M]
    {w : M → ℝ} (hw : ∀ j, 0 < w j) {bids : List (SingleMindedBid M)}
    (heq : xorBidEval bids = additiveValuation w) :
    2 ^ Fintype.card M - 1 ≤ bids.length := by
  refine xorBid_length_ge_of_strictMono heq (by simp [additiveValuation]) ?_
  intro S T hST
  obtain ⟨j, hjT, hjS⟩ := exists_of_ssubset hST
  exact sum_lt_sum_of_subset hST.subset hjT hjS (hw j) (fun x _ _ => (hw x).le)

/-- Every nonnegative unit-demand valuation (`unitDemandValuation w`) is represented by an `XOR`
bid of size `|M|` consisting of the single-item atomic bids `({j}, w j)` ([BlumrosenNisan2007],
§11.4.1, Definition 11.17, pp. 280–281). -/
theorem exists_xorBid_unitDemandValuation [Fintype M] [DecidableEq M] {w : M → ℝ}
    (hw : ∀ j, 0 ≤ w j) :
    ∃ bids : List (SingleMindedBid M),
      bids.length = Fintype.card M ∧
      (∀ b ∈ bids, b.bundle.Nonempty ∧ 0 ≤ b.value) ∧
      xorBidEval bids = unitDemandValuation w := by
  let bids : List (SingleMindedBid M) := (Finset.univ : Finset M).toList.map fun j => ⟨{j}, w j⟩
  refine ⟨bids, ?_, ?_, ?_⟩
  · simp [bids]
  · intro b hb
    rcases List.mem_map.mp hb with ⟨j, _, rfl⟩
    exact ⟨singleton_nonempty j, hw j⟩
  · funext S
    refine le_antisymm ?_ ?_
    · rw [xorBidEval_le_iff]
      refine ⟨unitDemandValuation_nonneg w S, fun b hb => ?_⟩
      rcases List.mem_map.mp hb with ⟨j, _, rfl⟩
      by_cases hj : j ∈ S
      · simp only [SingleMindedBid.eval, singleton_subset_iff, hj, ↓reduceIte]
        exact le_unitDemandValuation w hj
      · simp only [SingleMindedBid.eval, singleton_subset_iff, hj, ↓reduceIte]
        exact unitDemandValuation_nonneg w S
    · rcases S.eq_empty_or_nonempty with rfl | hSne
      · simp only [unitDemandValuation_empty]
        exact xorBidEval_nonneg bids ∅
      · obtain ⟨j, hjS, hjeq⟩ := exists_mem_unitDemandValuation_eq hw hSne
        rw [hjeq]
        have hmem : ⟨{j}, w j⟩ ∈ bids :=
          List.mem_map.mpr ⟨j, mem_toList.mpr (mem_univ j), rfl⟩
        have hle := le_xorBidEval_of_mem hmem S
        simpa only [SingleMindedBid.eval, singleton_subset_iff, hjS, ↓reduceIte] using hle

/-- A nontrivial unit-demand valuation (having two distinct items `a ≠ b` with positive values) is
not superadditive ([BlumrosenNisan2007], §11.4.1, p. 281). -/
theorem not_isSuperadditive_unitDemandValuation [DecidableEq M] {w : M → ℝ}
    {a b : M} (hab : a ≠ b) (ha : 0 < w a) (hb : 0 < w b) :
    ¬ IsSuperadditive (unitDemandValuation w) := by
  intro hsup
  have h := hsup (disjoint_singleton.mpr hab)
  have hua : unitDemandValuation w {a} = w a := by
    rw [unitDemandValuation_singleton, max_eq_left ha.le]
  have hub : unitDemandValuation w {b} = w b := by
    rw [unitDemandValuation_singleton, max_eq_left hb.le]
  have huab : unitDemandValuation w ({a} ∪ {b}) = max (w a) (w b) := by
    rw [singleton_union, unitDemandValuation_insert, hub]
  rw [hua, hub, huab] at h
  rcases max_choice (w a) (w b) with hmax | hmax <;> linarith

/-- No `OR` bid can represent a nontrivial unit-demand valuation ([BlumrosenNisan2007], §11.4.1,
p. 281). -/
theorem not_exists_orBid_unitDemandValuation {w : M → ℝ}
    {a b : M} (hab : a ≠ b) (ha : 0 < w a) (hb : 0 < w b) :
    ¬ ∃ bids : List (SingleMindedBid M), orBidEval bids = unitDemandValuation w := by
  classical
  rintro ⟨bids, heq⟩
  exact not_isSuperadditive_unitDemandValuation hab ha hb
    (heq ▸ orBidEval_isSuperadditive (by rw [heq, unitDemandValuation_empty]))

end OrXorBids

/-! ### General `OR`/`XOR` formulae and `OR`-of-`XOR`s (§11.4.2) -/

section Formulae

variable {M : Type*}

/-- Binary `XOR` combination of two valuations: `(v XOR u)(S) = max (v S) (u S)`
([BlumrosenNisan2007], Definition 11.18, p. 281). -/
@[expose] def xorVal (v u : Finset M → ℝ) (S : Finset M) : ℝ :=
  max (v S) (u S)

@[simp] theorem xorVal_empty (v u : Finset M → ℝ) :
    xorVal v u ∅ = max (v ∅) (u ∅) := rfl

theorem xorVal_comm (v u : Finset M → ℝ) : xorVal v u = xorVal u v := by
  funext S
  exact max_comm _ _

theorem xorVal_assoc (v u w : Finset M → ℝ) :
    xorVal (xorVal v u) w = xorVal v (xorVal u w) := by
  funext S
  exact max_assoc _ _ _

theorem xorVal_monotone {v u : Finset M → ℝ} (hv : Monotone v) (hu : Monotone u) :
    Monotone (xorVal v u) :=
  fun _ _ hST => max_le_max (hv hST) (hu hST)

private theorem disjointPairs_nonempty [DecidableEq M] (S : Finset M) :
    ((S.powerset ×ˢ S.powerset).filter fun p : Finset M × Finset M => Disjoint p.1 p.2).Nonempty :=
  ⟨(∅, ∅), mem_filter.mpr ⟨mem_product.mpr ⟨empty_mem_powerset S, empty_mem_powerset S⟩,
    disjoint_empty_left ∅⟩⟩

/-- Binary `OR` combination of two valuations:
`(v OR u)(S) = max_{R, T ⊆ S, R ∩ T = ∅} (v R + u T)`
([BlumrosenNisan2007], Definition 11.18, p. 281). -/
noncomputable def orVal [DecidableEq M] (v u : Finset M → ℝ) (S : Finset M) : ℝ :=
  ((S.powerset ×ˢ S.powerset).filter fun p : Finset M × Finset M => Disjoint p.1 p.2).sup'
    (disjointPairs_nonempty S)
    (fun p => v p.1 + u p.2)

/-- Every disjoint pair `R, T ⊆ S` lower-bounds `orVal v u S`. -/
theorem le_orVal [DecidableEq M] {v u : Finset M → ℝ} {S R T : Finset M}
    (hR : R ⊆ S) (hT : T ⊆ S) (hRT : Disjoint R T) :
    v R + u T ≤ orVal v u S :=
  le_sup' (b := (R, T)) (fun p : Finset M × Finset M => v p.1 + u p.2)
    (mem_filter.mpr ⟨mem_product.mpr ⟨mem_powerset.mpr hR, mem_powerset.mpr hT⟩, hRT⟩)

/-- Characterization of upper bounds on `orVal v u S`. -/
theorem orVal_le_iff [DecidableEq M] {v u : Finset M → ℝ} {S : Finset M} {c : ℝ} :
    orVal v u S ≤ c ↔
      ∀ R ⊆ S, ∀ T ⊆ S, Disjoint R T → v R + u T ≤ c := by
  unfold orVal
  rw [sup'_le_iff]
  constructor
  · intro h R hR T hT hRT
    exact h (R, T)
      (mem_filter.mpr ⟨mem_product.mpr ⟨mem_powerset.mpr hR, mem_powerset.mpr hT⟩, hRT⟩)
  · intro h p hp
    rcases mem_filter.mp hp with ⟨hprod, hdisj⟩
    rcases mem_product.mp hprod with ⟨hR, hT⟩
    exact h p.1 (mem_powerset.mp hR) p.2 (mem_powerset.mp hT) hdisj

/-- `orVal v u S` is attained by some disjoint pair `R, T ⊆ S`. -/
theorem exists_orVal_eq [DecidableEq M] (v u : Finset M → ℝ) (S : Finset M) :
    ∃ R ⊆ S, ∃ T ⊆ S, Disjoint R T ∧ orVal v u S = v R + u T := by
  obtain ⟨p, hp, hpeq⟩ :=
    exists_mem_eq_sup' (disjointPairs_nonempty S) (fun p : Finset M × Finset M => v p.1 + u p.2)
  rcases mem_filter.mp hp with ⟨hprod, hdisj⟩
  rcases mem_product.mp hprod with ⟨hR, hT⟩
  exact ⟨p.1, mem_powerset.mp hR, p.2, mem_powerset.mp hT, hdisj, hpeq⟩

@[simp] theorem orVal_empty [DecidableEq M] (v u : Finset M → ℝ) :
    orVal v u ∅ = v ∅ + u ∅ := by
  refine le_antisymm ?_ (le_orVal (Subset.refl ∅) (Subset.refl ∅) (disjoint_empty_left ∅))
  rw [orVal_le_iff]
  intro R hR T hT _
  rw [subset_empty.mp hR, subset_empty.mp hT]

/-- `orVal v u` is always monotone in the bundle `S`. -/
theorem orVal_monotone [DecidableEq M] (v u : Finset M → ℝ) : Monotone (orVal v u) := by
  intro S T hST
  rw [orVal_le_iff]
  intro A hA B hB hAB
  exact le_orVal (hA.trans hST) (hB.trans hST) hAB

theorem orVal_comm [DecidableEq M] (v u : Finset M → ℝ) : orVal v u = orVal u v := by
  funext S
  refine le_antisymm ?_ ?_ <;>
  · rw [orVal_le_iff]
    intro R hR T hT hRT
    rw [add_comm]
    exact le_orVal hT hR hRT.symm

theorem orVal_assoc [DecidableEq M] (v u w : Finset M → ℝ) :
    orVal (orVal v u) w = orVal v (orVal u w) := by
  funext S
  refine le_antisymm ?_ ?_
  · rw [orVal_le_iff]
    intro A hA C hC hAC
    obtain ⟨R, hRA, T, hTA, hRT, hAeq⟩ := exists_orVal_eq v u A
    rw [hAeq, add_assoc]
    have hTC : Disjoint T C := hAC.mono_left hTA
    have hRTC : Disjoint R (T ∪ C) :=
      Finset.disjoint_union_right.mpr ⟨hRT, hAC.mono_left hRA⟩
    have hle : u T + w C ≤ orVal u w (T ∪ C) :=
      le_orVal subset_union_left subset_union_right hTC
    exact (add_le_add le_rfl hle).trans
      (le_orVal (hRA.trans hA) (union_subset (hTA.trans hA) hC) hRTC)
  · rw [orVal_le_iff]
    intro R hR B hB hRB
    obtain ⟨T, hTB, C, hCB, hTC, hBeq⟩ := exists_orVal_eq u w B
    rw [hBeq, ← add_assoc]
    have hRT : Disjoint R T := hRB.mono_right hTB
    have hRTC : Disjoint (R ∪ T) C :=
      Finset.disjoint_union_left.mpr ⟨hRB.mono_right hCB, hTC⟩
    have hle : v R + u T ≤ orVal v u (R ∪ T) :=
      le_orVal subset_union_left subset_union_right hRT
    exact (add_le_add hle le_rfl).trans
      (le_orVal (union_subset hR (hTB.trans hB)) (hCB.trans hB) hRTC)

private theorem orVal_zero_right [DecidableEq M] {v : Finset M → ℝ} (hv : Monotone v) :
    orVal v (fun _ => 0) = v := by
  funext S
  refine le_antisymm ?_ ?_
  · rw [orVal_le_iff]
    intro R hR _ _ _
    simpa only [add_zero] using hv hR
  · simpa only [add_zero] using le_orVal (v := v) (u := fun _ => 0) Subset.rfl (empty_subset S)
      (disjoint_empty_right S)

/-- An `OR`/`XOR` bidding formula over single-minded atomic bids on item type `M`
([BlumrosenNisan2007], §11.4.2, p. 281), together with the empty `zero` formula of size `0`. -/
inductive BidFormula (M : Type*) where
  /-- The empty formula (size `0`), evaluating to `0` on every bundle. -/
  | zero
  /-- An atomic single-minded bid `(S, p)` (size `1`). -/
  | atom (bid : SingleMindedBid M)
  /-- The `OR` combination `left OR right`. -/
  | or (left right : BidFormula M)
  /-- The `XOR` combination `left XOR right`. -/
  | xor (left right : BidFormula M)

namespace BidFormula

/-- Number of atomic bids in an `OR`/`XOR` formula ([BlumrosenNisan2007], §11.4.1–11.4.2,
pp. 280–281). -/
@[expose] def size : BidFormula M → ℕ
  | .zero => 0
  | .atom _ => 1
  | .or f g => f.size + g.size
  | .xor f g => f.size + g.size

/-- Flat list of atomic bids appearing in a formula, in left-to-right order. -/
@[expose] def atoms : BidFormula M → List (SingleMindedBid M)
  | .zero => []
  | .atom b => [b]
  | .or f g => f.atoms ++ g.atoms
  | .xor f g => f.atoms ++ g.atoms

@[simp] theorem length_atoms (f : BidFormula M) : f.atoms.length = f.size := by
  induction f with
  | zero => rfl
  | atom _ => rfl
  | or f g ihf ihg => simp [atoms, size, ihf, ihg]
  | xor f g ihf ihg => simp [atoms, size, ihf, ihg]

/-- Valuation represented by an `OR`/`XOR` formula ([BlumrosenNisan2007], §11.4.2,
Definition 11.18, p. 281). -/
@[expose] noncomputable def eval [DecidableEq M] : BidFormula M → Finset M → ℝ
  | .zero => fun _ => 0
  | .atom b => b.eval
  | .or f g => orVal f.eval g.eval
  | .xor f g => xorVal f.eval g.eval

/-- If all atomic bids in `f` have nonnegative prices, `f.eval S ≥ 0` for every `S`. -/
theorem eval_nonneg [DecidableEq M] {f : BidFormula M} (hnn : ∀ b ∈ f.atoms, 0 ≤ b.value)
    (S : Finset M) : 0 ≤ f.eval S := by
  induction f generalizing S with
  | zero => exact le_rfl
  | atom b =>
    have hb : 0 ≤ b.value := hnn b (by simp [atoms])
    unfold eval SingleMindedBid.eval
    split_ifs
    · exact hb
    · exact le_rfl
  | or f g ihf ihg =>
    have hnnf : ∀ b ∈ f.atoms, 0 ≤ b.value := fun b hb =>
      hnn b (by simp [atoms, hb])
    have hnng : ∀ b ∈ g.atoms, 0 ≤ b.value := fun b hb =>
      hnn b (by simp [atoms, hb])
    calc
      (0 : ℝ) = 0 + 0 := by ring
      _ ≤ f.eval ∅ + g.eval ∅ := add_le_add (ihf hnnf ∅) (ihg hnng ∅)
      _ ≤ orVal f.eval g.eval S :=
            le_orVal (empty_subset S) (empty_subset S) (disjoint_empty_left ∅)
  | xor f g ihf _ =>
    have hnnf : ∀ b ∈ f.atoms, 0 ≤ b.value := fun b hb =>
      hnn b (by simp [atoms, hb])
    exact (ihf hnnf S).trans (le_max_left _ _)

/-- If all atomic bids in `f` have nonnegative prices, `f.eval` is monotone. -/
theorem eval_monotone [DecidableEq M] {f : BidFormula M} (hnn : ∀ b ∈ f.atoms, 0 ≤ b.value) :
    Monotone f.eval := by
  induction f with
  | zero => exact fun _ _ _ => le_rfl
  | atom b =>
    exact fun _ _ hST => SingleMindedBid.eval_mono (hnn b (by simp [atoms])) hST
  | or f g _ _ => exact orVal_monotone f.eval g.eval
  | xor f g ihf ihg =>
    exact xorVal_monotone
      (ihf fun b hb => hnn b (by simp [atoms, hb]))
      (ihg fun b hb => hnn b (by simp [atoms, hb]))

/-- If all atomic bids in `f` have nonempty bundles, `f.eval ∅ = 0`. -/
theorem eval_empty_of_nonempty [DecidableEq M] {f : BidFormula M}
    (hne : ∀ b ∈ f.atoms, b.bundle.Nonempty) : f.eval ∅ = 0 := by
  induction f with
  | zero => rfl
  | atom b => exact SingleMindedBid.eval_empty_of_nonempty (hne b (by simp [atoms]))
  | or f g ihf ihg =>
    simp only [eval, orVal_empty,
      ihf fun b hb => hne b (by simp [atoms, hb]),
      ihg fun b hb => hne b (by simp [atoms, hb]), add_zero]
  | xor f g ihf ihg =>
    simp only [eval, xorVal_empty,
      ihf fun b hb => hne b (by simp [atoms, hb]),
      ihg fun b hb => hne b (by simp [atoms, hb]), max_self]

/-- Predicate characterizing pure `XOR` formulae (built without `OR`). -/
@[expose] def IsXorFormula : BidFormula M → Prop
  | .zero => True
  | .atom _ => True
  | .or _ _ => False
  | .xor f g => f.IsXorFormula ∧ g.IsXorFormula

/-- Predicate characterizing `OR`-of-`XOR`s formulae: `OR` combinations of pure `XOR` clauses
([BlumrosenNisan2007], §11.4.2, Lemma 11.20, p. 281). -/
@[expose] def IsOrOfXor : BidFormula M → Prop
  | .zero => True
  | .atom _ => True
  | .xor f g => f.IsXorFormula ∧ g.IsXorFormula
  | .or f g => f.IsOrOfXor ∧ g.IsOrOfXor

/-- Build a pure `XOR` formula from a list of atomic bids (returning `zero` on `[]`). -/
@[expose] def ofXorList : List (SingleMindedBid M) → BidFormula M
  | [] => .zero
  | [b] => .atom b
  | b :: c :: bs => .xor (.atom b) (ofXorList (c :: bs))

/-- Build a pure `OR` formula from a list of atomic bids (returning `zero` on `[]`). -/
@[expose] def ofOrList : List (SingleMindedBid M) → BidFormula M
  | [] => .zero
  | [b] => .atom b
  | b :: c :: bs => .or (.atom b) (ofOrList (c :: bs))

/-- Combine a list of subformulae using `OR` (returning `zero` on `[]`). -/
@[expose] def ofOrFormulaList : List (BidFormula M) → BidFormula M
  | [] => .zero
  | [f] => f
  | f :: g :: fs => .or f (ofOrFormulaList (g :: fs))

@[simp] theorem atoms_ofXorList (bids : List (SingleMindedBid M)) :
    (ofXorList bids).atoms = bids := by
  match bids with
  | [] => rfl
  | [_] => rfl
  | b :: c :: bs => simp [ofXorList, atoms, atoms_ofXorList (c :: bs)]

@[simp] theorem size_ofXorList (bids : List (SingleMindedBid M)) :
    (ofXorList bids).size = bids.length := by
  rw [← length_atoms, atoms_ofXorList]

@[simp] theorem atoms_ofOrList (bids : List (SingleMindedBid M)) :
    (ofOrList bids).atoms = bids := by
  match bids with
  | [] => rfl
  | [_] => rfl
  | b :: c :: bs => simp [ofOrList, atoms, atoms_ofOrList (c :: bs)]

@[simp] theorem size_ofOrList (bids : List (SingleMindedBid M)) :
    (ofOrList bids).size = bids.length := by
  rw [← length_atoms, atoms_ofOrList]

@[simp] theorem size_ofOrFormulaList (fs : List (BidFormula M)) :
    (ofOrFormulaList fs).size = (fs.map BidFormula.size).sum := by
  match fs with
  | [] => rfl
  | [f] => simp [ofOrFormulaList]
  | f :: g :: fs => simp [ofOrFormulaList, size, size_ofOrFormulaList (g :: fs)]

theorem mem_atoms_ofOrFormulaList {fs : List (BidFormula M)} {b : SingleMindedBid M} :
    b ∈ (ofOrFormulaList fs).atoms ↔ ∃ f ∈ fs, b ∈ f.atoms := by
  match fs with
  | [] => simp [ofOrFormulaList, atoms]
  | [f] => simp [ofOrFormulaList]
  | f :: g :: fs =>
    simp only [ofOrFormulaList, atoms, List.mem_append, mem_atoms_ofOrFormulaList (fs := g :: fs),
      List.mem_cons, exists_eq_or_imp]

theorem isXorFormula_ofXorList (bids : List (SingleMindedBid M)) :
    (ofXorList bids).IsXorFormula := by
  match bids with
  | [] => trivial
  | [_] => trivial
  | _ :: c :: bs => exact ⟨trivial, isXorFormula_ofXorList (c :: bs)⟩

theorem isOrOfXor_of_isXorFormula {f : BidFormula M} (hf : f.IsXorFormula) : f.IsOrOfXor := by
  cases f with
  | zero => trivial
  | atom _ => trivial
  | or _ _ => exact hf.elim
  | xor _ _ => exact hf

theorem isOrOfXor_ofOrFormulaList {fs : List (BidFormula M)}
    (hfs : ∀ f ∈ fs, f.IsXorFormula) : (ofOrFormulaList fs).IsOrOfXor := by
  match fs with
  | [] => trivial
  | [f] => exact isOrOfXor_of_isXorFormula (hfs f (List.mem_cons_self ..))
  | f :: g :: fs =>
    exact ⟨isOrOfXor_of_isXorFormula (hfs f (List.mem_cons_self ..)),
      isOrOfXor_ofOrFormulaList fun h hh => hfs h (List.mem_cons_of_mem f hh)⟩

/-- On any list of nonnegative atomic bids, `BidFormula.ofXorList` evaluates identically to
`xorBidEval`. -/
theorem eval_ofXorList [DecidableEq M] {bids : List (SingleMindedBid M)}
    (hnn : ∀ b ∈ bids, 0 ≤ b.value) :
    (ofXorList bids).eval = xorBidEval bids := by
  funext S
  match bids with
  | [] => rfl
  | [b] =>
    have hb : 0 ≤ b.eval S := by
      unfold SingleMindedBid.eval
      split_ifs
      · exact hnn b (List.mem_cons_self ..)
      · exact le_rfl
    simp [ofXorList, eval, max_eq_left hb]
  | b :: c :: bs =>
    have ih := congrFun (eval_ofXorList (bids := c :: bs)
      fun x hx => hnn x (List.mem_cons_of_mem b hx)) S
    simp [ofXorList, eval, xorVal, ih]

private theorem orVal_atom_orBidEval [DecidableEq M] {b : SingleMindedBid M}
    (hb : 0 ≤ b.value) (bs : List (SingleMindedBid M)) :
    orVal b.eval (orBidEval bs) = orBidEval (b :: bs) := by
  funext S
  have hb_eval_nn : ∀ R : Finset M, 0 ≤ b.eval R := fun R => by
    unfold SingleMindedBid.eval
    split_ifs
    · exact hb
    · exact le_rfl
  refine le_antisymm ?_ ?_
  · rw [orVal_le_iff]
    intro R hR T hT hRT
    obtain ⟨W, hW, hWeq⟩ := exists_isValidORCollection_eq bs T
    rw [hWeq]
    let Wshift : Finset (Fin (b :: bs).length) :=
      W.map ⟨Fin.succ, Fin.succ_injective _⟩
    have hshift_sum : ∑ i ∈ Wshift, ((b :: bs)[i]).value = ∑ i ∈ W, (bs[i]).value := by
      rw [sum_map]
      rfl
    by_cases hsub : b.bundle ⊆ R
    · have h0not : (0 : Fin (b :: bs).length) ∉ Wshift := by
        simp [Wshift]
      have hvalid : IsValidORCollection (b :: bs) S (insert 0 Wshift) := by
        refine ⟨?_, ?_⟩
        · intro i hi j hj hij
          rcases mem_insert.mp hi with rfl | hi' <;> rcases mem_insert.mp hj with rfl | hj'
          · exact (hij rfl).elim
          · rcases mem_map.mp hj' with ⟨j', hj'W, rfl⟩
            exact hRT.mono hsub (hW.2 j' hj'W)
          · rcases mem_map.mp hi' with ⟨i', hi'W, rfl⟩
            exact hRT.symm.mono (hW.2 i' hi'W) hsub
          · rcases mem_map.mp hi' with ⟨i', hi'W, rfl⟩
            rcases mem_map.mp hj' with ⟨j', hj'W, rfl⟩
            exact hW.1 hi'W hj'W (fun h => hij (congrArg Fin.succ h))
        · intro i hi
          rcases mem_insert.mp hi with rfl | hi'
          · exact hsub.trans hR
          · rcases mem_map.mp hi' with ⟨i', hi'W, rfl⟩
            exact (hW.2 i' hi'W).trans hT
      have hle := le_orBidEval hvalid
      rw [sum_insert h0not, hshift_sum] at hle
      change b.value + ∑ i ∈ W, (bs[i]).value ≤ orBidEval (b :: bs) S at hle
      simpa only [SingleMindedBid.eval, hsub, ↓reduceIte] using hle
    · have hvalid : IsValidORCollection (b :: bs) S Wshift := by
        refine ⟨?_, ?_⟩
        · intro i hi j hj hij
          rcases mem_map.mp hi with ⟨i', hi'W, rfl⟩
          rcases mem_map.mp hj with ⟨j', hj'W, rfl⟩
          exact hW.1 hi'W hj'W (fun h => hij (congrArg Fin.succ h))
        · intro i hi
          rcases mem_map.mp hi with ⟨i', hi'W, rfl⟩
          exact (hW.2 i' hi'W).trans hT
      have hle := le_orBidEval hvalid
      rw [hshift_sum] at hle
      simpa only [SingleMindedBid.eval, hsub, ↓reduceIte, zero_add] using hle
  · rw [orBidEval_le_iff]
    intro W hW
    let Wtail : Finset (Fin bs.length) := Finset.univ.filter fun j => j.succ ∈ W
    have htail_valid : ∀ T : Finset M, (∀ j ∈ Wtail, (bs[j]).bundle ⊆ T) →
        IsValidORCollection bs T Wtail := by
      intro T hT
      refine ⟨fun i hi j hj hij => ?_, hT⟩
      exact hW.1 (mem_filter.mp hi).2 (mem_filter.mp hj).2 (fun h => hij (Fin.succ_injective _ h))
    have htail_eq_erase : W.erase 0 = Wtail.map ⟨Fin.succ, Fin.succ_injective _⟩ := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Wtail]
      · simp [Wtail]
    have hsum_tail : ∑ i ∈ W.erase 0, ((b :: bs)[i]).value = ∑ j ∈ Wtail, (bs[j]).value := by
      rw [htail_eq_erase, sum_map]
      rfl
    by_cases h0 : (0 : Fin (b :: bs).length) ∈ W
    · have hbS : b.bundle ⊆ S := hW.2 0 h0
      have hdisj : Disjoint b.bundle (S \ b.bundle) := disjoint_sdiff
      have htail_sdiff : ∀ j ∈ Wtail, (bs[j]).bundle ⊆ S \ b.bundle := by
        intro j hj
        have hjW : j.succ ∈ W := (mem_filter.mp hj).2
        have hdj : Disjoint b.bundle (bs[j]).bundle := hW.1 h0 hjW (Fin.succ_ne_zero j).symm
        exact subset_sdiff.mpr ⟨hW.2 j.succ hjW, hdj.symm⟩
      calc
        ∑ i ∈ W, ((b :: bs)[i]).value
            = b.value + ∑ i ∈ W.erase 0, ((b :: bs)[i]).value := (add_sum_erase W _ h0).symm
        _ = b.eval b.bundle + ∑ j ∈ Wtail, (bs[j]).value := by
              rw [SingleMindedBid.eval_self, hsum_tail]
        _ ≤ b.eval b.bundle + orBidEval bs (S \ b.bundle) :=
              add_le_add le_rfl (le_orBidEval (htail_valid (S \ b.bundle) htail_sdiff))
        _ ≤ orVal b.eval (orBidEval bs) S := le_orVal hbS sdiff_subset hdisj
    · have htail_S : ∀ j ∈ Wtail, (bs[j]).bundle ⊆ S :=
        fun j hj => hW.2 j.succ (mem_filter.mp hj).2
      calc
        ∑ i ∈ W, ((b :: bs)[i]).value
            = ∑ i ∈ W.erase 0, ((b :: bs)[i]).value := by rw [erase_eq_of_notMem h0]
        _ = ∑ j ∈ Wtail, (bs[j]).value := hsum_tail
        _ ≤ 0 + orBidEval bs S := by
              rw [zero_add]
              exact le_orBidEval (htail_valid S htail_S)
        _ ≤ b.eval ∅ + orBidEval bs S := add_le_add (hb_eval_nn ∅) le_rfl
        _ ≤ orVal b.eval (orBidEval bs) S :=
              le_orVal (empty_subset S) Subset.rfl (disjoint_empty_left S)

/-- On any list of nonnegative atomic bids, `BidFormula.ofOrList` evaluates identically to
`orBidEval`. -/
theorem eval_ofOrList [DecidableEq M] {bids : List (SingleMindedBid M)}
    (hnn : ∀ b ∈ bids, 0 ≤ b.value) :
    (ofOrList bids).eval = orBidEval bids := by
  match bids with
  | [] =>
    funext S
    simp [ofOrList, eval]
  | [b] =>
    have hb : 0 ≤ b.value := hnn b (List.mem_cons_self ..)
    have h1 := orVal_atom_orBidEval hb []
    have h2 : orBidEval ([] : List (SingleMindedBid M)) = fun _ => 0 := funext orBidEval_nil
    rw [h2, orVal_zero_right (fun _ _ hST => SingleMindedBid.eval_mono hb hST)] at h1
    exact h1
  | b :: c :: bs =>
    have hb : 0 ≤ b.value := hnn b (List.mem_cons_self ..)
    have ih := eval_ofOrList (bids := c :: bs) fun x hx => hnn x (List.mem_cons_of_mem b hx)
    change orVal b.eval (ofOrList (c :: bs)).eval = orBidEval (b :: c :: bs)
    rw [ih, orVal_atom_orBidEval hb (c :: bs)]

private theorem eval_ofOrFormulaList_append_singleton [DecidableEq M]
    (fs : List (BidFormula M)) (g : BidFormula M)
    (hg_mono : Monotone g.eval) :
    (ofOrFormulaList (fs ++ [g])).eval = orVal (ofOrFormulaList fs).eval g.eval := by
  match fs with
  | [] =>
    simp only [List.nil_append, ofOrFormulaList, eval]
    rw [orVal_comm, orVal_zero_right hg_mono]
  | [f] => rfl
  | f₁ :: f₂ :: rest =>
    have ih := eval_ofOrFormulaList_append_singleton (f₂ :: rest) g hg_mono
    change orVal f₁.eval (ofOrFormulaList ((f₂ :: rest) ++ [g])).eval =
      orVal (orVal f₁.eval (ofOrFormulaList (f₂ :: rest)).eval) g.eval
    rw [ih, orVal_assoc]

end BidFormula

/-! ### Downward-sloping symmetric valuations (Definition 11.19 and Lemma 11.20, p. 281) -/

/-- Every `XOR` bid representing a downward-sloping symmetric valuation with strictly positive
marginals (`∀ k < |M|, 0 < w k`) requires size at least `2 ^ |M| - 1` ([BlumrosenNisan2007],
§11.4.2, p. 281). -/
theorem xorBid_length_ge_downwardSlopingValuation [Fintype M] [DecidableEq M]
    {w : ℕ → ℝ} (hpos : ∀ k < Fintype.card M, 0 < w k) {bids : List (SingleMindedBid M)}
    (heq : xorBidEval bids = downwardSlopingValuation w) :
    2 ^ Fintype.card M - 1 ≤ bids.length := by
  refine xorBid_length_ge_of_strictMono heq (by simp) ?_
  intro S T hST
  have hcard : S.card < T.card := card_lt_card hST
  have hTle : T.card ≤ Fintype.card M := card_le_univ T
  unfold downwardSlopingValuation
  exact sum_lt_sum_of_subset (range_mono hcard.le) (mem_range.mpr hcard) (by simp)
    (hpos S.card (lt_of_lt_of_le hcard hTle))
    (fun k hk _ => (hpos k (lt_of_lt_of_le (mem_range.mp hk) hTle)).le)

/-- A downward-sloping symmetric valuation with strictly decreasing first marginal (`w 1 < w 0`)
on at least two items (`2 ≤ |M|`) is not superadditive ([BlumrosenNisan2007], §11.4.2, p. 281). -/
theorem not_isSuperadditive_downwardSlopingValuation [Fintype M] [DecidableEq M]
    {w : ℕ → ℝ} (hm : 2 ≤ Fintype.card M) (hdec : w 1 < w 0) :
    ¬ IsSuperadditive (downwardSlopingValuation (M := M) w) := by
  intro hsup
  have hcard : 1 < (Finset.univ : Finset M).card := by
    rw [card_univ]
    omega
  obtain ⟨a, _, b, _, hab⟩ := Finset.one_lt_card.mp hcard
  have h := hsup (disjoint_singleton.mpr hab)
  have hcard_ab : ({a} ∪ {b} : Finset M).card = 2 := by
    rw [singleton_union, card_pair hab]
  simp only [downwardSlopingValuation, card_singleton, hcard_ab, sum_range_succ,
    sum_range_zero, zero_add] at h
  linarith

/-- No `OR` bid can represent a downward-sloping symmetric valuation with `w 1 < w 0` on at least
two items ([BlumrosenNisan2007], §11.4.2, p. 281). -/
theorem not_exists_orBid_downwardSlopingValuation [Fintype M]
    {w : ℕ → ℝ} (hm : 2 ≤ Fintype.card M) (hdec : w 1 < w 0) :
    ¬ ∃ bids : List (SingleMindedBid M), orBidEval bids = downwardSlopingValuation (M := M) w := by
  classical
  rintro ⟨bids, heq⟩
  exact not_isSuperadditive_downwardSlopingValuation hm hdec
    (heq ▸ orBidEval_isSuperadditive (by rw [heq, downwardSlopingValuation_empty]))

/-- **Lemma 11.20** ([BlumrosenNisan2007], §11.4.2, p. 281): every downward-sloping symmetric
valuation on `m = |M|` items (with `w 0 ≥ w 1 ≥ ⋯ ≥ w (m - 1) ≥ 0`) is represented by an
`OR`-of-`XOR`s formula of size `m ^ 2`, consisting of `m` `XOR` clauses each offering `w k` for
any single item. -/
theorem exists_orOfXor_downwardSlopingValuation [Fintype M] [DecidableEq M]
    {w : ℕ → ℝ} (hanti : AntitoneOn w (Set.Iio (Fintype.card M)))
    (hnn : ∀ k < Fintype.card M, 0 ≤ w k) :
    ∃ f : BidFormula M,
      f.IsOrOfXor ∧
      f.size = Fintype.card M ^ 2 ∧
      (∀ b ∈ f.atoms, b.bundle.Nonempty ∧ 0 ≤ b.value) ∧
      f.eval = downwardSlopingValuation w := by
  let clause : ℕ → BidFormula M := fun k =>
    BidFormula.ofXorList ((Finset.univ : Finset M).toList.map fun j => ⟨{j}, w k⟩)
  have hclause_eval : ∀ k < Fintype.card M, ∀ S : Finset M,
      (clause k).eval S = if S.Nonempty then w k else 0 := by
    intro k hk S
    have hnn_k : ∀ b ∈ ((Finset.univ : Finset M).toList.map fun j =>
        (⟨{j}, w k⟩ : SingleMindedBid M)), 0 ≤ b.value := by
      intro b hb
      rcases List.mem_map.mp hb with ⟨_, _, rfl⟩
      exact hnn k hk
    rw [congrFun (BidFormula.eval_ofXorList hnn_k) S]
    refine le_antisymm ?_ ?_
    · rw [xorBidEval_le_iff]
      refine ⟨by split_ifs <;> [exact hnn k hk; exact le_rfl], fun b hb => ?_⟩
      rcases List.mem_map.mp hb with ⟨j, _, rfl⟩
      by_cases hj : j ∈ S
      · have hSne : S.Nonempty := ⟨j, hj⟩
        simp [SingleMindedBid.eval, hj, hSne]
      · simp only [SingleMindedBid.eval, singleton_subset_iff, hj, ↓reduceIte]
        split_ifs
        · exact hnn k hk
        · exact le_rfl
    · split_ifs with hS
      · obtain ⟨j, hj⟩ := hS
        have hmem : (⟨{j}, w k⟩ : SingleMindedBid M) ∈
            (Finset.univ : Finset M).toList.map fun j => ⟨{j}, w k⟩ :=
          List.mem_map.mpr ⟨j, mem_toList.mpr (mem_univ j), rfl⟩
        simpa only [SingleMindedBid.eval, singleton_subset_iff, hj, ↓reduceIte] using
          le_xorBidEval_of_mem hmem S
      · exact xorBidEval_nonneg _ S
  have hprefix : ∀ n ≤ Fintype.card M, ∀ S : Finset M,
      (BidFormula.ofOrFormulaList ((List.range n).map clause)).eval S =
        ∑ k ∈ range (min S.card n), w k := by
    intro n
    induction n with
    | zero =>
      intro _ S
      simp [BidFormula.ofOrFormulaList, BidFormula.eval]
    | succ n ih =>
      intro hn S
      have hn_lt : n < Fintype.card M := Nat.lt_of_succ_le hn
      have hmono_n : Monotone (clause n).eval :=
        BidFormula.eval_monotone fun b hb => by
          rw [BidFormula.atoms_ofXorList] at hb
          rcases List.mem_map.mp hb with ⟨_, _, rfl⟩
          exact hnn n hn_lt
      rw [List.range_succ, List.map_append, List.map_singleton,
        congrFun (BidFormula.eval_ofOrFormulaList_append_singleton _ _ hmono_n) S]
      refine le_antisymm ?_ ?_
      · rw [orVal_le_iff]
        intro R hR T hT hRT
        rw [ih (Nat.le_of_succ_le hn) R, hclause_eval n hn_lt T]
        split_ifs with hTne
        · have hRcard : R.card + 1 ≤ S.card := by
            have h1 : 1 ≤ T.card := card_pos.mpr hTne
            have h2 : R.card + T.card ≤ S.card := by
              rw [← card_union_of_disjoint hRT]
              exact card_le_card (union_subset hR hT)
            omega
          have hmin_le : min R.card n + 1 ≤ min S.card (n + 1) := by omega
          have hw_le : w n ≤ w (min R.card n) :=
            hanti (Set.mem_Iio.mpr (by omega)) (Set.mem_Iio.mpr hn_lt) (Nat.min_le_right _ _)
          calc
            (∑ k ∈ range (min R.card n), w k) + w n
                ≤ (∑ k ∈ range (min R.card n), w k) + w (min R.card n) :=
                  add_le_add le_rfl hw_le
            _ = ∑ k ∈ range (min R.card n + 1), w k := (sum_range_succ w _).symm
            _ ≤ ∑ k ∈ range (min S.card (n + 1)), w k :=
                  sum_le_sum_of_subset_of_nonneg (range_mono hmin_le) fun k hk _ =>
                    hnn k (lt_of_lt_of_le (mem_range.mp hk) (by omega))
        · rw [add_zero]
          have hmin_le : min R.card n ≤ min S.card (n + 1) := by
            have := card_le_card hR
            omega
          exact sum_le_sum_of_subset_of_nonneg (range_mono hmin_le) fun k hk _ =>
            hnn k (lt_of_lt_of_le (mem_range.mp hk) (by omega))
      · by_cases hSn : S.card ≤ n
        · have hmin : min S.card (n + 1) = min S.card n := by omega
          rw [hmin]
          have h0 : (clause n).eval ∅ = 0 := by simp [hclause_eval n hn_lt]
          have hle := le_orVal (v := (BidFormula.ofOrFormulaList ((List.range n).map clause)).eval)
            (u := (clause n).eval) Subset.rfl (empty_subset S) (disjoint_empty_right S)
          rw [ih (Nat.le_of_succ_le hn) S, h0, add_zero] at hle
          exact hle
        · have hSne : S.Nonempty := card_pos.mp (by omega)
          obtain ⟨x, hxS⟩ := hSne
          have hRcard : (S.erase x).card = S.card - 1 := card_erase_of_mem hxS
          have hmin_R : min (S.erase x).card n = n := by omega
          have hmin_S : min S.card (n + 1) = n + 1 := by omega
          have hle := le_orVal (v := (BidFormula.ofOrFormulaList ((List.range n).map clause)).eval)
            (u := (clause n).eval) (erase_subset x S) (singleton_subset_iff.mpr hxS)
            (disjoint_singleton_right.mpr (notMem_erase x S))
          have hcx : (clause n).eval {x} = w n := by
            simp [hclause_eval n hn_lt, singleton_nonempty]
          rw [ih (Nat.le_of_succ_le hn) (S.erase x), hmin_R, hcx, ← sum_range_succ, ← hmin_S] at hle
          exact hle
  let f : BidFormula M := BidFormula.ofOrFormulaList ((List.range (Fintype.card M)).map clause)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · refine BidFormula.isOrOfXor_ofOrFormulaList fun g hg => ?_
    rcases List.mem_map.mp hg with ⟨k, _, rfl⟩
    exact BidFormula.isXorFormula_ofXorList _
  · simp only [f, BidFormula.size_ofOrFormulaList, List.map_map]
    have hconst : ((List.range (Fintype.card M)).map (BidFormula.size ∘ clause)) =
        List.replicate (Fintype.card M) (Fintype.card M) := by
      refine List.ext_getElem (by simp) fun i hi _ => ?_
      simp [clause]
    rw [hconst, List.sum_replicate, smul_eq_mul, sq]
  · intro b hb
    obtain ⟨g, hg, hbg⟩ := BidFormula.mem_atoms_ofOrFormulaList.mp hb
    rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
    rw [BidFormula.atoms_ofXorList] at hbg
    rcases List.mem_map.mp hbg with ⟨j, _, rfl⟩
    exact ⟨singleton_nonempty j, hnn k (List.mem_range.mp hk)⟩
  · funext S
    rw [hprefix (Fintype.card M) le_rfl S, Nat.min_eq_left (card_le_univ S)]
    rfl

end Formulae

/-! ### Dummy items and `OR*` simulation (§11.4.3, Theorem 11.21) -/

section ORStar

variable {M : Type*}

/-- An `OR*` bid on real item type `M` with dummy item type `D` ([BlumrosenNisan2007], §11.4.3,
p. 282): an `OR` bid over `M ⊕ D`, evaluated at a real-item bundle `S : Finset M` by offering `S`
together with all dummy items `Finset.univ : Finset D`. -/
structure ORStarBid (M D : Type*) where
  /-- The atomic single-minded bids on the augmented item set `M ⊕ D`. -/
  bids : List (SingleMindedBid (M ⊕ D))

namespace ORStarBid

/-- The size of an `OR*` bid is the number of atomic bids it contains. -/
@[expose] def size {D : Type*} (b : ORStarBid M D) : ℕ :=
  b.bids.length

/-- Valuation represented by an `OR*` bid: `b.eval S = orBidEval b.bids (S ∪ D)`
([BlumrosenNisan2007], §11.4.3, p. 282). -/
@[expose] noncomputable def eval {D : Type*} [Fintype D]
    (b : ORStarBid M D) (S : Finset M) : ℝ :=
  orBidEval b.bids (S.disjSum (Finset.univ : Finset D))

end ORStarBid

private lemma disjoint_disjSum_iff {α β : Type*}
    {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} :
    Disjoint (s₁.disjSum t₁) (s₂.disjSum t₂) ↔ Disjoint s₁ s₂ ∧ Disjoint t₁ t₂ := by
  simp only [Finset.disjoint_left, Finset.mem_disjSum]
  constructor
  · intro h
    refine ⟨fun a ha₁ ha₂ => h (Or.inl ⟨a, ha₁, rfl⟩) (Or.inl ⟨a, ha₂, rfl⟩),
      fun b hb₁ hb₂ => h (Or.inr ⟨b, hb₁, rfl⟩) (Or.inr ⟨b, hb₂, rfl⟩)⟩
  · rintro ⟨hs, ht⟩ x (⟨a, ha₁, rfl⟩ | ⟨b, hb₁, rfl⟩) (⟨a', ha₂, h'⟩ | ⟨b', hb₂, h'⟩)
    · exact hs ha₁ (Sum.inl.inj h' ▸ ha₂)
    · cases h'
    · cases h'
    · exact ht hb₁ (Sum.inr.inj h' ▸ hb₂)

/-- Pairwise `XOR`-conflict relation between atomic-bid positions in a `BidFormula`: two atom
positions conflict iff their lowest common ancestor in the formula tree is an `XOR` node. -/
private def BidFormula.xorConflict : BidFormula M → ℕ → ℕ → Prop
  | .zero, _, _ => False
  | .atom _, _, _ => False
  | .or f g, i, j =>
      (i < f.size ∧ j < f.size ∧ f.xorConflict i j) ∨
      (f.size ≤ i ∧ f.size ≤ j ∧ g.xorConflict (i - f.size) (j - f.size))
  | .xor f g, i, j =>
      (i < f.size ∧ j < f.size ∧ f.xorConflict i j) ∨
      (f.size ≤ i ∧ f.size ≤ j ∧ g.xorConflict (i - f.size) (j - f.size)) ∨
      (i < f.size ∧ f.size ≤ j) ∨
      (f.size ≤ i ∧ j < f.size)

private theorem BidFormula.xorConflict_symm (f : BidFormula M) {i j : ℕ} :
    f.xorConflict i j → f.xorConflict j i := by
  induction f generalizing i j with
  | zero => exact id
  | atom _ => exact id
  | or f g ihf ihg =>
    rintro (⟨hi, hj, h⟩ | ⟨hi, hj, h⟩)
    · exact Or.inl ⟨hj, hi, ihf h⟩
    · exact Or.inr ⟨hj, hi, ihg h⟩
  | xor f g ihf ihg =>
    rintro (⟨hi, hj, h⟩ | ⟨hi, hj, h⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩)
    · exact Or.inl ⟨hj, hi, ihf h⟩
    · exact Or.inr (Or.inl ⟨hj, hi, ihg h⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hj, hi⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hj, hi⟩))

private theorem BidFormula.xorConflict_irrefl (f : BidFormula M) (i : ℕ) :
    ¬ f.xorConflict i i := by
  induction f generalizing i with
  | zero => exact id
  | atom _ => exact id
  | or f g ihf ihg =>
    rintro (⟨_, _, h⟩ | ⟨_, _, h⟩)
    · exact ihf i h
    · exact ihg (i - f.size) h
  | xor f g ihf ihg =>
    rintro (⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩)
    · exact ihf i h
    · exact ihg (i - f.size) h
    · omega
    · omega

/-- A valid atom selection for `f` on bundle `S`: pairwise disjoint real bundles contained in `S`
forming an independent set in `f.xorConflict`. -/
private def IsValidFormulaSelection (f : BidFormula M) (S : Finset M)
    (W : Finset (Fin f.atoms.length)) : Prop :=
  IsValidORCollection f.atoms S W ∧
    ∀ i ∈ W, ∀ j ∈ W, ¬ f.xorConflict i.val j.val

private theorem isValidFormulaSelection_empty (f : BidFormula M) (S : Finset M) :
    IsValidFormulaSelection f S ∅ :=
  ⟨isValidORCollection_empty f.atoms S, fun _ h => (notMem_empty _ h).elim⟩

private def appendIdxEquiv {α : Type*} (l₁ l₂ : List α) :
    Fin l₁.length ⊕ Fin l₂.length ≃ Fin (l₁ ++ l₂).length :=
  finSumFinEquiv.trans (finCongr List.length_append.symm)

private lemma getElem_appendIdxEquiv_inl {α : Type*} (l₁ l₂ : List α) (i : Fin l₁.length) :
    (l₁ ++ l₂)[appendIdxEquiv l₁ l₂ (.inl i)] = l₁[i] := by
  simp [appendIdxEquiv]

private lemma getElem_appendIdxEquiv_inr {α : Type*} (l₁ l₂ : List α) (j : Fin l₂.length) :
    (l₁ ++ l₂)[appendIdxEquiv l₁ l₂ (.inr j)] = l₂[j] := by
  simp [appendIdxEquiv]

/-- Split a valid `OR` collection on `l₁ ++ l₂` into its left (`l₁`) and right (`l₂`) parts,
preserving compatibility, bundle inclusion, cross-disjointness, and weight sums. -/
private theorem split_append_orCollection {l₁ l₂ : List (SingleMindedBid M)}
    {S : Finset M} {W : Finset (Fin (l₁ ++ l₂).length)}
    (hW : IsValidORCollection (l₁ ++ l₂) S W) :
    let e := appendIdxEquiv l₁ l₂
    let W₁ : Finset (Fin l₁.length) := (W.map e.symm.toEmbedding).toLeft
    let W₂ : Finset (Fin l₂.length) := (W.map e.symm.toEmbedding).toRight
    (∀ i ∈ W₁, e (.inl i) ∈ W) ∧
    (∀ j ∈ W₂, e (.inr j) ∈ W) ∧
    IsValidORCollection l₁ S W₁ ∧
    IsValidORCollection l₂ S W₂ ∧
    (∀ i ∈ W₁, ∀ j ∈ W₂, Disjoint (l₁[i]).bundle (l₂[j]).bundle) ∧
    ∑ k ∈ W, ((l₁ ++ l₂)[k]).value =
      ∑ i ∈ W₁, (l₁[i]).value + ∑ j ∈ W₂, (l₂[j]).value := by
  intro e W₁ W₂
  have hW₁_mem : ∀ i ∈ W₁, e (.inl i) ∈ W := by
    intro i hi
    rcases mem_map.mp (Finset.mem_toLeft.mp hi) with ⟨k, hkW, hkeq⟩
    have : e (.inl i) = k := by simpa using congrArg e hkeq.symm
    exact this ▸ hkW
  have hW₂_mem : ∀ j ∈ W₂, e (.inr j) ∈ W := by
    intro j hj
    rcases mem_map.mp (Finset.mem_toRight.mp hj) with ⟨k, hkW, hkeq⟩
    have : e (.inr j) = k := by simpa using congrArg e hkeq.symm
    exact this ▸ hkW
  refine ⟨hW₁_mem, hW₂_mem, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i₁ hi₁ i₂ hi₂ hne
    have hdj := hW.1 (hW₁_mem i₁ hi₁) (hW₁_mem i₂ hi₂)
      (fun h => hne (Sum.inl.inj (e.injective h)))
    dsimp only [Function.onFun] at hdj ⊢
    rwa [getElem_appendIdxEquiv_inl, getElem_appendIdxEquiv_inl] at hdj
  · intro i hi
    have h := hW.2 (e (.inl i)) (hW₁_mem i hi)
    rwa [getElem_appendIdxEquiv_inl] at h
  · intro j₁ hj₁ j₂ hj₂ hne
    have hdj := hW.1 (hW₂_mem j₁ hj₁) (hW₂_mem j₂ hj₂)
      (fun h => hne (Sum.inr.inj (e.injective h)))
    dsimp only [Function.onFun] at hdj ⊢
    rwa [getElem_appendIdxEquiv_inr, getElem_appendIdxEquiv_inr] at hdj
  · intro j hj
    have h := hW.2 (e (.inr j)) (hW₂_mem j hj)
    rwa [getElem_appendIdxEquiv_inr] at h
  · intro i hi j hj
    have hne : e (.inl i) ≠ e (.inr j) := fun h => by cases e.injective h
    have hdj := hW.1 (hW₁_mem i hi) (hW₂_mem j hj) hne
    dsimp only [Function.onFun] at hdj
    rwa [getElem_appendIdxEquiv_inl, getElem_appendIdxEquiv_inr] at hdj
  · have hW_eq : W = (W₁.disjSum W₂).map e.toEmbedding := by
      dsimp only [W₁, W₂]
      rw [Finset.toLeft_disjSum_toRight]
      ext k
      simp
    rw [hW_eq, sum_map, ← Finset.map_inl_disjUnion_map_inr, sum_disjUnion, sum_map, sum_map]
    congr 1
    · refine sum_congr rfl fun i _ => ?_
      change ((l₁ ++ l₂)[e (.inl i)]).value = (l₁[i]).value
      rw [getElem_appendIdxEquiv_inl]
    · refine sum_congr rfl fun j _ => ?_
      change ((l₁ ++ l₂)[e (.inr j)]).value = (l₂[j]).value
      rw [getElem_appendIdxEquiv_inr]

/-- Combine two valid `OR` collections on disjoint subbundles `R, T ⊆ S` into a valid collection
on `l₁ ++ l₂`. -/
private theorem disjSum_append_orCollection {l₁ l₂ : List (SingleMindedBid M)}
    {S R T : Finset M} (hRS : R ⊆ S) (hTS : T ⊆ S) (hRT : Disjoint R T)
    {W₁ : Finset (Fin l₁.length)} {W₂ : Finset (Fin l₂.length)}
    (hW₁ : IsValidORCollection l₁ R W₁) (hW₂ : IsValidORCollection l₂ T W₂) :
    let W := (W₁.disjSum W₂).map (appendIdxEquiv l₁ l₂).toEmbedding
    IsValidORCollection (l₁ ++ l₂) S W ∧
    ∑ k ∈ W, ((l₁ ++ l₂)[k]).value =
      ∑ i ∈ W₁, (l₁[i]).value + ∑ j ∈ W₂, (l₂[j]).value := by
  intro W
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    rcases mem_map.mp hx with ⟨a, ha, rfl⟩
    rcases mem_map.mp hy with ⟨b, hb, rfl⟩
    have hab : a ≠ b := fun h => hxy (congrArg (appendIdxEquiv l₁ l₂).toEmbedding h)
    dsimp only [Function.onFun, Equiv.coe_toEmbedding]
    cases a with
    | inl i₁ =>
      cases b with
      | inl i₂ =>
        rw [getElem_appendIdxEquiv_inl, getElem_appendIdxEquiv_inl]
        exact hW₁.1 (Finset.inl_mem_disjSum.mp ha) (Finset.inl_mem_disjSum.mp hb)
          (fun h => hab (congrArg Sum.inl h))
      | inr j₂ =>
        rw [getElem_appendIdxEquiv_inl, getElem_appendIdxEquiv_inr]
        exact hRT.mono (hW₁.2 i₁ (Finset.inl_mem_disjSum.mp ha))
          (hW₂.2 j₂ (Finset.inr_mem_disjSum.mp hb))
    | inr j₁ =>
      cases b with
      | inl i₂ =>
        rw [getElem_appendIdxEquiv_inr, getElem_appendIdxEquiv_inl]
        exact hRT.symm.mono (hW₂.2 j₁ (Finset.inr_mem_disjSum.mp ha))
          (hW₁.2 i₂ (Finset.inl_mem_disjSum.mp hb))
      | inr j₂ =>
        rw [getElem_appendIdxEquiv_inr, getElem_appendIdxEquiv_inr]
        exact hW₂.1 (Finset.inr_mem_disjSum.mp ha) (Finset.inr_mem_disjSum.mp hb)
          (fun h => hab (congrArg Sum.inr h))
  · intro x hx
    rcases mem_map.mp hx with ⟨a, ha, rfl⟩
    dsimp only [Equiv.coe_toEmbedding]
    cases a with
    | inl i =>
      rw [getElem_appendIdxEquiv_inl]
      exact (hW₁.2 i (Finset.inl_mem_disjSum.mp ha)).trans hRS
    | inr j =>
      rw [getElem_appendIdxEquiv_inr]
      exact (hW₂.2 j (Finset.inr_mem_disjSum.mp ha)).trans hTS
  · dsimp only [W]
    rw [sum_map, ← Finset.map_inl_disjUnion_map_inr, sum_disjUnion, sum_map, sum_map]
    congr 1
    · refine sum_congr rfl fun i _ => ?_
      change ((l₁ ++ l₂)[appendIdxEquiv l₁ l₂ (.inl i)]).value = (l₁[i]).value
      rw [getElem_appendIdxEquiv_inl]
    · refine sum_congr rfl fun j _ => ?_
      change ((l₁ ++ l₂)[appendIdxEquiv l₁ l₂ (.inr j)]).value = (l₂[j]).value
      rw [getElem_appendIdxEquiv_inr]

private lemma appendIdxEquiv_inl_lt (f g : BidFormula M) (i : Fin f.atoms.length) :
    (appendIdxEquiv f.atoms g.atoms (.inl i)).val < f.size := by
  rw [← f.length_atoms]
  exact i.isLt

private lemma appendIdxEquiv_inr_val (f g : BidFormula M) (j : Fin g.atoms.length) :
    (appendIdxEquiv f.atoms g.atoms (.inr j)).val = f.size + j.val := by
  rw [← f.length_atoms]
  rfl

/-- Fundamental correspondence between `BidFormula.eval` and maximum-weight independent compatible
atom selections in `f.xorConflict`. -/
private theorem bidFormula_eval_eq_max_selection [DecidableEq M] (f : BidFormula M)
    (hnn : ∀ b ∈ f.atoms, 0 ≤ b.value) (S : Finset M) :
    (∀ W : Finset (Fin f.atoms.length), IsValidFormulaSelection f S W →
        ∑ i ∈ W, (f.atoms[i]).value ≤ f.eval S) ∧
    (∃ W : Finset (Fin f.atoms.length), IsValidFormulaSelection f S W ∧
        f.eval S = ∑ i ∈ W, (f.atoms[i]).value) := by
  induction f generalizing S with
  | zero =>
    refine ⟨fun W _ => ?_, ⟨∅, isValidFormulaSelection_empty .zero S, by simp [BidFormula.eval]⟩⟩
    have hW : W = ∅ := eq_empty_of_forall_notMem fun i => Fin.elim0 i
    simp [hW, BidFormula.eval]
  | atom b =>
    have hb : 0 ≤ b.value := hnn b (by simp [BidFormula.atoms])
    let z0 : Fin (BidFormula.atom b).atoms.length := ⟨0, by simp [BidFormula.atoms]⟩
    have hz_uniq : ∀ i : Fin (BidFormula.atom b).atoms.length, i = z0 := fun i => by
      have hi : i.val < 1 := by simpa [BidFormula.atoms] using i.isLt
      exact Fin.ext (show i.val = 0 by omega)
    constructor
    · intro W hW
      by_cases h0 : z0 ∈ W
      · have hW_eq : W = {z0} := by
          ext i
          simp [hz_uniq i, h0]
        have hsub : b.bundle ⊆ S := by
          simpa [BidFormula.atoms, z0] using hW.1.2 z0 h0
        rw [hW_eq, sum_singleton]
        change b.value ≤ b.eval S
        simp [SingleMindedBid.eval, hsub]
      · have hW_eq : W = ∅ := eq_empty_of_forall_notMem fun i hi => h0 (hz_uniq i ▸ hi)
        simp only [hW_eq, sum_empty, BidFormula.eval, SingleMindedBid.eval]
        split_ifs
        · exact hb
        · exact le_rfl
    · by_cases hsub : b.bundle ⊆ S
      · refine ⟨{z0}, ⟨⟨by simp [IsCompatible], ?_⟩, ?_⟩, ?_⟩
        · intro i hi
          rw [mem_singleton.mp hi]
          exact hsub
        · intro _ _ _ _
          exact id
        · rw [sum_singleton]
          change b.eval S = b.value
          simp [SingleMindedBid.eval, hsub]
      · refine ⟨∅, isValidFormulaSelection_empty (.atom b) S, ?_⟩
        simp [BidFormula.eval, SingleMindedBid.eval, hsub]
  | or f g ihf ihg =>
    have hnnf : ∀ b ∈ f.atoms, 0 ≤ b.value := fun b hb => hnn b (by simp [BidFormula.atoms, hb])
    have hnng : ∀ b ∈ g.atoms, 0 ≤ b.value := fun b hb => hnn b (by simp [BidFormula.atoms, hb])
    constructor
    · intro W hW
      obtain ⟨hW₁_mem, hW₂_mem, hW₁_or, hW₂_or, hcross, hsum_split⟩ :=
        split_append_orCollection (l₁ := f.atoms) (l₂ := g.atoms) hW.1
      set e := appendIdxEquiv f.atoms g.atoms
      set W₁ := (W.map e.symm.toEmbedding).toLeft
      set W₂ := (W.map e.symm.toEmbedding).toRight
      let R : Finset M := W₁.biUnion fun i => (f.atoms[i]).bundle
      let T : Finset M := W₂.biUnion fun j => (g.atoms[j]).bundle
      have hRT : Disjoint R T := by
        rw [Finset.disjoint_left]
        intro x hxR hxT
        obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hxR
        obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hxT
        exact Finset.disjoint_left.mp (hcross i hi j hj) hxi hxj
      have hW₁_valid : IsValidFormulaSelection f R W₁ :=
        ⟨⟨hW₁_or.1, fun i hi => subset_biUnion_of_mem
            (fun k : Fin f.atoms.length => (f.atoms[k]).bundle) hi⟩,
          fun i₁ hi₁ i₂ hi₂ hconf => hW.2 (e (.inl i₁)) (hW₁_mem i₁ hi₁)
            (e (.inl i₂)) (hW₁_mem i₂ hi₂)
            (Or.inl ⟨appendIdxEquiv_inl_lt f g i₁, appendIdxEquiv_inl_lt f g i₂, hconf⟩)⟩
      have hW₂_valid : IsValidFormulaSelection g T W₂ :=
        ⟨⟨hW₂_or.1, fun j hj => subset_biUnion_of_mem
            (fun k : Fin g.atoms.length => (g.atoms[k]).bundle) hj⟩,
          fun j₁ hj₁ j₂ hj₂ hconf => hW.2 (e (.inr j₁)) (hW₂_mem j₁ hj₁)
            (e (.inr j₂)) (hW₂_mem j₂ hj₂)
            (Or.inr ⟨by rw [appendIdxEquiv_inr_val f g]; exact Nat.le_add_right _ _,
              by rw [appendIdxEquiv_inr_val f g]; exact Nat.le_add_right _ _,
              by simpa only [e, appendIdxEquiv_inr_val f g, Nat.add_sub_cancel_left] using hconf⟩)⟩
      exact hsum_split.trans_le
        ((add_le_add ((ihf hnnf R).1 W₁ hW₁_valid) ((ihg hnng T).1 W₂ hW₂_valid)).trans
          (le_orVal (biUnion_subset.mpr hW₁_or.2) (biUnion_subset.mpr hW₂_or.2) hRT))
    · obtain ⟨R, hRS, T, hTS, hRT, hEq⟩ := exists_orVal_eq f.eval g.eval S
      obtain ⟨W₁, hW₁, hEq₁⟩ := (ihf hnnf R).2
      obtain ⟨W₂, hW₂, hEq₂⟩ := (ihg hnng T).2
      obtain ⟨hvalid, hsum⟩ := disjSum_append_orCollection hRS hTS hRT hW₁.1 hW₂.1
      refine ⟨(W₁.disjSum W₂).map (appendIdxEquiv f.atoms g.atoms).toEmbedding, ⟨hvalid, ?_⟩, ?_⟩
      · intro x hx y hy hconf
        rcases mem_map.mp hx with ⟨a, ha, rfl⟩
        rcases mem_map.mp hy with ⟨b, hb, rfl⟩
        change (f.or g).xorConflict (appendIdxEquiv f.atoms g.atoms a).val
          (appendIdxEquiv f.atoms g.atoms b).val at hconf
        cases a with
        | inl i₁ =>
          have hi₁ := appendIdxEquiv_inl_lt f g i₁
          cases b with
          | inl i₂ =>
            rcases hconf with ⟨_, _, hc⟩ | ⟨hge, _, _⟩
            · exact hW₁.2 i₁ (Finset.inl_mem_disjSum.mp ha) i₂ (Finset.inl_mem_disjSum.mp hb) hc
            · omega
          | inr j₂ =>
            have hj₂ := appendIdxEquiv_inr_val f g j₂
            rcases hconf with ⟨_, hlt, _⟩ | ⟨hge, _, _⟩ <;> omega
        | inr j₁ =>
          have hj₁ := appendIdxEquiv_inr_val f g j₁
          cases b with
          | inl i₂ =>
            have hi₂ := appendIdxEquiv_inl_lt f g i₂
            rcases hconf with ⟨hlt, _, _⟩ | ⟨_, hge, _⟩ <;> omega
          | inr j₂ =>
            rcases hconf with ⟨hlt, _, _⟩ | ⟨_, _, hc⟩
            · omega
            · exact hW₂.2 j₁ (Finset.inr_mem_disjSum.mp ha) j₂ (Finset.inr_mem_disjSum.mp hb)
                (by simpa only [appendIdxEquiv_inr_val f g, Nat.add_sub_cancel_left] using hc)
      · rw [BidFormula.eval, hEq, hEq₁, hEq₂]
        exact hsum.symm
  | xor f g ihf ihg =>
    have hnnf : ∀ b ∈ f.atoms, 0 ≤ b.value := fun b hb => hnn b (by simp [BidFormula.atoms, hb])
    have hnng : ∀ b ∈ g.atoms, 0 ≤ b.value := fun b hb => hnn b (by simp [BidFormula.atoms, hb])
    constructor
    · intro W hW
      obtain ⟨hW₁_mem, hW₂_mem, hW₁_or, hW₂_or, _, hsum_split⟩ :=
        split_append_orCollection (l₁ := f.atoms) (l₂ := g.atoms) hW.1
      have hnot_both : (W.map (appendIdxEquiv f.atoms g.atoms).symm.toEmbedding).toLeft = ∅ ∨
          (W.map (appendIdxEquiv f.atoms g.atoms).symm.toEmbedding).toRight = ∅ := by
        by_contra hboth
        push Not at hboth
        obtain ⟨i, hi⟩ := hboth.1
        obtain ⟨j, hj⟩ := hboth.2
        exact hW.2 (appendIdxEquiv f.atoms g.atoms (.inl i)) (hW₁_mem i hi)
          (appendIdxEquiv f.atoms g.atoms (.inr j)) (hW₂_mem j hj)
          (Or.inr (Or.inr (Or.inl ⟨appendIdxEquiv_inl_lt f g i,
            by rw [appendIdxEquiv_inr_val f g]; exact Nat.le_add_right _ _⟩)))
      refine hsum_split.trans_le ?_
      rcases hnot_both with h1 | h2
      · rw [h1, sum_empty, zero_add]
        refine ((ihg hnng S).1 _ ⟨hW₂_or, fun j₁ hj₁ j₂ hj₂ hconf => ?_⟩).trans (le_max_right _ _)
        exact hW.2 _ (hW₂_mem j₁ hj₁) _ (hW₂_mem j₂ hj₂)
          (Or.inr (Or.inl ⟨by rw [appendIdxEquiv_inr_val f g]; exact Nat.le_add_right _ _,
            by rw [appendIdxEquiv_inr_val f g]; exact Nat.le_add_right _ _,
            by simpa only [appendIdxEquiv_inr_val f g, Nat.add_sub_cancel_left] using hconf⟩))
      · rw [h2, sum_empty, add_zero]
        refine ((ihf hnnf S).1 _ ⟨hW₁_or, fun i₁ hi₁ i₂ hi₂ hconf => ?_⟩).trans (le_max_left _ _)
        exact hW.2 _ (hW₁_mem i₁ hi₁) _ (hW₁_mem i₂ hi₂)
          (Or.inl ⟨appendIdxEquiv_inl_lt f g i₁, appendIdxEquiv_inl_lt f g i₂, hconf⟩)
    · rcases max_choice (f.eval S) (g.eval S) with hmax | hmax
      · obtain ⟨W₁, hW₁, hEq₁⟩ := (ihf hnnf S).2
        obtain ⟨hvalid, hsum⟩ := disjSum_append_orCollection (l₁ := f.atoms) (l₂ := g.atoms)
          Subset.rfl (empty_subset S) (disjoint_empty_right S) hW₁.1
          (isValidORCollection_empty g.atoms ∅)
        refine ⟨(W₁.disjSum ∅).map (appendIdxEquiv f.atoms g.atoms).toEmbedding, ⟨hvalid, ?_⟩, ?_⟩
        · intro x hx y hy hconf
          rcases mem_map.mp hx with ⟨a, ha, rfl⟩
          rcases mem_map.mp hy with ⟨b, hb, rfl⟩
          change (f.xor g).xorConflict (appendIdxEquiv f.atoms g.atoms a).val
            (appendIdxEquiv f.atoms g.atoms b).val at hconf
          cases a with
          | inr j => exact (notMem_empty j (Finset.inr_mem_disjSum.mp ha)).elim
          | inl i₁ =>
            cases b with
            | inr j => exact (notMem_empty j (Finset.inr_mem_disjSum.mp hb)).elim
            | inl i₂ =>
              have hlt₁ := appendIdxEquiv_inl_lt f g i₁
              have hlt₂ := appendIdxEquiv_inl_lt f g i₂
              rcases hconf with ⟨_, _, hc⟩ | ⟨hge, _, _⟩ | ⟨_, hge⟩ | ⟨hge, _⟩
              · exact hW₁.2 i₁ (Finset.inl_mem_disjSum.mp ha) i₂ (Finset.inl_mem_disjSum.mp hb) hc
              · omega
              · omega
              · omega
        · rw [BidFormula.eval, xorVal, hmax, hEq₁]
          exact (by simp : ∑ i ∈ W₁, (f.atoms[i]).value =
            ∑ i ∈ W₁, (f.atoms[i]).value + ∑ j ∈ (∅ : Finset (Fin g.atoms.length)),
              (g.atoms[j]).value).trans hsum.symm
      · obtain ⟨W₂, hW₂, hEq₂⟩ := (ihg hnng S).2
        obtain ⟨hvalid, hsum⟩ := disjSum_append_orCollection (l₁ := f.atoms) (l₂ := g.atoms)
          (empty_subset S) Subset.rfl (disjoint_empty_left S)
          (isValidORCollection_empty f.atoms ∅) hW₂.1
        refine ⟨((∅ : Finset (Fin f.atoms.length)).disjSum W₂).map
          (appendIdxEquiv f.atoms g.atoms).toEmbedding, ⟨hvalid, ?_⟩, ?_⟩
        · intro x hx y hy hconf
          rcases mem_map.mp hx with ⟨a, ha, rfl⟩
          rcases mem_map.mp hy with ⟨b, hb, rfl⟩
          change (f.xor g).xorConflict (appendIdxEquiv f.atoms g.atoms a).val
            (appendIdxEquiv f.atoms g.atoms b).val at hconf
          cases a with
          | inl i => exact (notMem_empty i (Finset.inl_mem_disjSum.mp ha)).elim
          | inr j₁ =>
            cases b with
            | inl i => exact (notMem_empty i (Finset.inl_mem_disjSum.mp hb)).elim
            | inr j₂ =>
              have hge₁ := appendIdxEquiv_inr_val f g j₁
              have hge₂ := appendIdxEquiv_inr_val f g j₂
              rcases hconf with ⟨hlt, _, _⟩ | ⟨_, _, hc⟩ | ⟨hlt, _⟩ | ⟨_, hlt⟩
              · omega
              · exact hW₂.2 j₁ (Finset.inr_mem_disjSum.mp ha) j₂ (Finset.inr_mem_disjSum.mp hb)
                  (by simpa only [appendIdxEquiv_inr_val f g, Nat.add_sub_cancel_left] using hc)
              · omega
              · omega
        · rw [BidFormula.eval, xorVal, hmax, hEq₂]
          exact (by simp : ∑ j ∈ W₂, (g.atoms[j]).value =
            ∑ i ∈ (∅ : Finset (Fin f.atoms.length)), (f.atoms[i]).value +
              ∑ j ∈ W₂, (g.atoms[j]).value).trans hsum.symm

/-- **Theorem 11.21** ([BlumrosenNisan2007], §11.4.3, pp. 282–283): any valuation represented by
an `OR`/`XOR` formula `f` of size `s` with nonnegative atomic prices can be represented by an `OR*`
bid of size `s` using at most `s.choose 2` (hence at most `s ^ 2`) dummy items, one dummy item per
`XOR`-conflicting pair of atomic bids. -/
theorem exists_orStarBid_of_bidFormula [DecidableEq M] (f : BidFormula M)
    (hnn : ∀ b ∈ f.atoms, 0 ≤ b.value) :
    ∃ (d : ℕ) (b : ORStarBid M (Fin d)),
      b.size = f.size ∧
      d ≤ f.size.choose 2 ∧
      (∀ a ∈ b.bids, 0 ≤ a.value) ∧
      b.eval = f.eval := by
  classical
  let E : Finset (Finset (Fin f.atoms.length)) :=
    ((Finset.univ : Finset (Fin f.atoms.length)).powersetCard 2).filter fun pair =>
      ∃ i ∈ pair, ∃ j ∈ pair, f.xorConflict i.val j.val
  let d : ℕ := E.card
  have hd_le : d ≤ f.size.choose 2 := by
    calc
      d ≤ ((Finset.univ : Finset (Fin f.atoms.length)).powersetCard 2).card :=
        card_le_card (filter_subset _ _)
      _ = f.atoms.length.choose 2 := by rw [card_powersetCard, card_univ, Fintype.card_fin]
      _ = f.size.choose 2 := by rw [f.length_atoms]
  let equivD : {pair // pair ∈ E} ≃ Fin d := Fintype.equivFinOfCardEq (Fintype.card_coe E)
  let dummySet : Fin f.atoms.length → Finset (Fin d) := fun i =>
    Finset.univ.filter fun k : Fin d => i ∈ (equivD.symm k).val
  let augBid : Fin f.atoms.length → SingleMindedBid (M ⊕ Fin d) := fun i =>
    ⟨(f.atoms[i]).bundle.disjSum (dummySet i), (f.atoms[i]).value⟩
  let b : ORStarBid M (Fin d) := ⟨List.ofFn augBid⟩
  have hlen : b.bids.length = f.atoms.length := List.length_ofFn
  have hdisj_dummy : ∀ i j : Fin f.atoms.length, i ≠ j →
      (Disjoint (dummySet i) (dummySet j) ↔ ¬ f.xorConflict i.val j.val) := by
    intro i j hij
    constructor
    · intro hdisj hconf
      have hpairE : ({i, j} : Finset (Fin f.atoms.length)) ∈ E := by
        refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, card_pair hij⟩,
          ⟨i, mem_insert_self i {j}, j, mem_insert_of_mem (mem_singleton_self j), hconf⟩⟩
      let k : Fin d := equivD ⟨{i, j}, hpairE⟩
      have hki : k ∈ dummySet i := by
        simp [dummySet, k]
      have hkj : k ∈ dummySet j := by
        simp [dummySet, k]
      exact Finset.disjoint_left.mp hdisj hki hkj
    · intro hnot
      rw [Finset.disjoint_left]
      intro k hki hkj
      have hi : i ∈ (equivD.symm k).val := (mem_filter.mp hki).2
      have hj : j ∈ (equivD.symm k).val := (mem_filter.mp hkj).2
      have hmemE : (equivD.symm k).val ∈ E := (equivD.symm k).property
      have hcard2 : (equivD.symm k).val.card = 2 :=
        (mem_powersetCard.mp (mem_filter.mp hmemE).1).2
      have hpair_eq : ({i, j} : Finset (Fin f.atoms.length)) = (equivD.symm k).val :=
        eq_of_subset_of_card_le (insert_subset hi (singleton_subset_iff.mpr hj))
          (by rw [card_pair hij, hcard2])
      obtain ⟨u, hu, v, hv, huv⟩ := (mem_filter.mp hmemE).2
      rw [← hpair_eq] at hu hv
      rcases mem_insert.mp hu with hiu | hu' <;> rcases mem_insert.mp hv with hiv | hv'
      · rw [hiu, hiv] at huv
        exact f.xorConflict_irrefl i.val huv
      · rw [hiu, mem_singleton.mp hv'] at huv
        exact hnot huv
      · rw [mem_singleton.mp hu', hiv] at huv
        exact hnot (f.xorConflict_symm huv)
      · rw [mem_singleton.mp hu', mem_singleton.mp hv'] at huv
        exact f.xorConflict_irrefl j.val huv
  refine ⟨d, b, ?_, hd_le, ?_, ?_⟩
  · simp [ORStarBid.size, b, f.length_atoms]
  · intro a ha
    rcases List.mem_ofFn.mp ha with ⟨i, rfl⟩
    exact hnn (f.atoms[i]) (List.getElem_mem i.isLt)
  · funext S
    let idxEquiv : Fin b.bids.length ≃ Fin f.atoms.length := finCongr hlen
    have hget : ∀ k : Fin b.bids.length, b.bids[k] = augBid (idxEquiv k) := fun k => by
      change (List.ofFn augBid)[k.val]'(by simpa [b] using k.isLt) = augBid (idxEquiv k)
      rw [List.getElem_ofFn]
      rfl
    have hvalid_iff : ∀ W : Finset (Fin b.bids.length),
        IsValidORCollection b.bids (S.disjSum Finset.univ) W ↔
          IsValidFormulaSelection f S (W.map idxEquiv.toEmbedding) := by
      intro W
      constructor
      · intro hW
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro i₁ hi₁ i₂ hi₂ hne
          rcases mem_map.mp hi₁ with ⟨k₁, hk₁, rfl⟩
          rcases mem_map.mp hi₂ with ⟨k₂, hk₂, rfl⟩
          have hk : k₁ ≠ k₂ := fun h => hne (congrArg idxEquiv.toEmbedding h)
          have hdj := hW.1 hk₁ hk₂ hk
          dsimp only [Function.onFun, Equiv.coe_toEmbedding] at hdj ⊢
          rw [hget k₁, hget k₂] at hdj
          exact (disjoint_disjSum_iff.mp hdj).1
        · intro i hi
          rcases mem_map.mp hi with ⟨k, hk, rfl⟩
          have hsub := hW.2 k hk
          dsimp only [Equiv.coe_toEmbedding]
          rw [hget k] at hsub
          simpa only [augBid, Finset.toLeft_disjSum] using (Finset.subset_disjSum.mp hsub).1
        · intro i₁ hi₁ i₂ hi₂
          rcases mem_map.mp hi₁ with ⟨k₁, hk₁, rfl⟩
          rcases mem_map.mp hi₂ with ⟨k₂, hk₂, rfl⟩
          dsimp only [Equiv.coe_toEmbedding]
          by_cases hk : k₁ = k₂
          · subst hk
            exact f.xorConflict_irrefl _
          · have hdj := hW.1 hk₁ hk₂ hk
            dsimp only [Function.onFun] at hdj
            rw [hget k₁, hget k₂] at hdj
            exact (hdisj_dummy (idxEquiv k₁) (idxEquiv k₂)
              (fun h => hk (idxEquiv.injective h))).mp (disjoint_disjSum_iff.mp hdj).2
      · intro hW
        refine ⟨fun k₁ hk₁ k₂ hk₂ hk => ?_, fun k hk => ?_⟩
        · dsimp only [Function.onFun]
          rw [hget k₁, hget k₂]
          have hi₁ : idxEquiv k₁ ∈ W.map idxEquiv.toEmbedding := mem_map_of_mem _ hk₁
          have hi₂ : idxEquiv k₂ ∈ W.map idxEquiv.toEmbedding := mem_map_of_mem _ hk₂
          have hne : idxEquiv k₁ ≠ idxEquiv k₂ := fun h => hk (idxEquiv.injective h)
          exact disjoint_disjSum_iff.mpr
            ⟨hW.1.1 hi₁ hi₂ hne, (hdisj_dummy _ _ hne).mpr (hW.2 _ hi₁ _ hi₂)⟩
        · rw [hget k]
          refine Finset.subset_disjSum.mpr ⟨?_, subset_univ _⟩
          simpa only [augBid, Finset.toLeft_disjSum] using
            hW.1.2 (idxEquiv k) (mem_map_of_mem _ hk)
    have hsum_eq : ∀ W : Finset (Fin b.bids.length),
        ∑ k ∈ W, (b.bids[k]).value =
          ∑ i ∈ W.map idxEquiv.toEmbedding, (f.atoms[i]).value := fun W => by
      rw [sum_map]
      refine sum_congr rfl fun k _ => ?_
      rw [hget k]
      rfl
    obtain ⟨hmax_le, Wopt, hWopt, hWopt_eq⟩ := bidFormula_eval_eq_max_selection f hnn S
    refine le_antisymm ?_ ?_
    · unfold ORStarBid.eval
      rw [orBidEval_le_iff]
      intro W hW
      rw [hsum_eq W]
      exact hmax_le (W.map idxEquiv.toEmbedding) ((hvalid_iff W).mp hW)
    · let Wb : Finset (Fin b.bids.length) := Wopt.map idxEquiv.symm.toEmbedding
      have hWb_map : Wb.map idxEquiv.toEmbedding = Wopt := by
        ext i
        simp [Wb]
      have hWb_valid : IsValidORCollection b.bids (S.disjSum Finset.univ) Wb :=
        (hvalid_iff Wb).mpr (hWb_map ▸ hWopt)
      calc
        f.eval S = ∑ i ∈ Wopt, (f.atoms[i]).value := hWopt_eq
        _ = ∑ k ∈ Wb, (b.bids[k]).value := by rw [hsum_eq Wb, hWb_map]
        _ ≤ b.eval S := le_orBidEval hWb_valid

end ORStar

/-! ### Threshold and majority valuation `OR*` lower bound (Exercise 11.5, p. 299) -/

section MajorityLowerBound

variable {M : Type*}

/-- The `k`-threshold valuation on item type `M`: assigns `1` to every bundle of at least `k`
items and `0` to every bundle of fewer than `k` items. -/
@[expose] def thresholdValuation (k : ℕ) (S : Finset M) : ℝ :=
  if k ≤ S.card then 1 else 0

/-- The **majority valuation** on a finite item set `M` ([BlumrosenNisan2007], Exercise 11.5,
p. 299): assigns `1` to every bundle of at least `m / 2` items (i.e., `(m + 1) / 2 ≤ S.card`)
and `0` to all smaller bundles. -/
@[expose] def majorityValuation (M : Type*) [Fintype M] (S : Finset M) : ℝ :=
  thresholdValuation ((Fintype.card M + 1) / 2) S

/-- `majorityValuation M S = 1` if and only if `S` has at least `(|M| : ℝ) / 2` items. -/
theorem majorityValuation_eq_one_iff [Fintype M] (S : Finset M) :
    majorityValuation M S = 1 ↔ (Fintype.card M : ℝ) / 2 ≤ (S.card : ℝ) := by
  unfold majorityValuation thresholdValuation
  have hnat : (Fintype.card M + 1) / 2 ≤ S.card ↔ (Fintype.card M : ℝ) / 2 ≤ (S.card : ℝ) := by
    constructor
    · intro h
      have h2 : Fintype.card M ≤ 2 * S.card := by omega
      have h2r : (Fintype.card M : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast h2
      linarith
    · intro h
      have h2r : (Fintype.card M : ℝ) ≤ 2 * (S.card : ℝ) := by linarith
      have h2 : Fintype.card M ≤ 2 * S.card := by exact_mod_cast h2r
      omega
  rw [← hnat]
  split_ifs with h <;> simp [h]

/-- On any nonempty item set `M`, the majority valuation is normalized (`v ∅ = 0`). -/
@[simp] theorem majorityValuation_empty [Fintype M] [Nonempty M] :
    majorityValuation M ∅ = 0 := by
  have hpos : 0 < Fintype.card M := Fintype.card_pos
  have hlt : ¬ (Fintype.card M + 1) / 2 ≤ 0 := by omega
  simp [majorityValuation, thresholdValuation, hlt]

/-- Every `OR*` bid representing the `k`-threshold valuation on finite `M` requires at least
`(|M|).choose k` atomic bids (one atom whose real-item projection equals `S` for each `k`-element
bundle `S`, with no nonnegativity assumption needed on atomic prices). -/
theorem thresholdValuation_orStarBid_size_ge [Fintype M]
    {D : Type*} [Fintype D] {k : ℕ} {b : ORStarBid M D}
    (heq : b.eval = thresholdValuation k) :
    (Fintype.card M).choose k ≤ b.size := by
  classical
  have hsub : (Finset.univ : Finset M).powersetCard k ⊆
      (b.bids.map fun a => a.bundle.toLeft).toFinset := by
    intro S hS
    have hScard : S.card = k := (mem_powersetCard.mp hS).2
    have hval : b.eval S = 1 := by
      rw [heq]
      simp [thresholdValuation, hScard]
    obtain ⟨W, hW, hWeq⟩ := exists_isValidORCollection_eq b.bids (S.disjSum Finset.univ)
    change b.eval S = ∑ i ∈ W, (b.bids[i]).value at hWeq
    have hpos_sum : (0 : ℝ) < ∑ i ∈ W, (b.bids[i]).value := by linarith
    have hex_pos : ∃ i ∈ W, (0 : ℝ) < (b.bids[i]).value := by
      by_contra hnot
      push Not at hnot
      have hle0 : ∑ i ∈ W, (b.bids[i]).value ≤ 0 := sum_nonpos hnot
      linarith
    obtain ⟨i, hiW, hipos⟩ := hex_pos
    let R : Finset M := (b.bids[i]).bundle.toLeft
    have hRS : R ⊆ S := (Finset.subset_disjSum.mp (hW.2 i hiW)).1
    have hvalid_R : IsValidORCollection b.bids (R.disjSum Finset.univ) {i} :=
      ⟨by simp [IsCompatible], fun j hj => by
        rw [mem_singleton.mp hj]
        exact Finset.subset_disjSum.mpr ⟨Subset.rfl, subset_univ _⟩⟩
    have hle_R : (b.bids[i]).value ≤ b.eval R := by
      unfold ORStarBid.eval
      simpa only [sum_singleton] using le_orBidEval hvalid_R
    have hRpos : 0 < thresholdValuation k R := by
      rw [← heq]
      exact lt_of_lt_of_le hipos hle_R
    have hkR : k ≤ R.card := by
      unfold thresholdValuation at hRpos
      split_ifs at hRpos with hk
      · exact hk
      · linarith
    have hReq : R = S := eq_of_subset_of_card_le hRS (hScard.symm ▸ hkR)
    exact List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨b.bids[i], List.getElem_mem i.isLt, hReq⟩)
  calc
    (Fintype.card M).choose k = ((Finset.univ : Finset M).powersetCard k).card := by
      rw [card_powersetCard, card_univ]
    _ ≤ (b.bids.map fun a => a.bundle.toLeft).toFinset.card := card_le_card hsub
    _ ≤ (b.bids.map fun a => a.bundle.toLeft).length := List.toFinset_card_le _
    _ = b.size := List.length_map _

/-- **Exercise 11.5** ([BlumrosenNisan2007], p. 299): representing the majority valuation on
`m = |M|` items using an `OR*` bid requires size at least `m.choose (m / 2)`. -/
theorem majorityValuation_orStarBid_size_ge [Fintype M]
    {D : Type*} [Fintype D] {b : ORStarBid M D}
    (heq : b.eval = majorityValuation M) :
    (Fintype.card M).choose (Fintype.card M / 2) ≤ b.size := by
  have hchoose : (Fintype.card M).choose (Fintype.card M / 2) =
      (Fintype.card M).choose ((Fintype.card M + 1) / 2) := by
    rcases Nat.even_or_odd (Fintype.card M) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have h1 : (k + k) / 2 = k := by omega
      have h2 : (k + k + 1) / 2 = k := by omega
      rw [hk, h1, h2]
    · have h1 : (2 * k + 1) / 2 = k := by omega
      have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      rw [hk, h1, h2, ← Nat.choose_symm (by omega : k ≤ 2 * k + 1)]
      congr 1
      omega
  rw [hchoose]
  exact thresholdValuation_orStarBid_size_ge heq

end MajorityLowerBound

end Cslib.GameTheory.CombinatorialAuction
