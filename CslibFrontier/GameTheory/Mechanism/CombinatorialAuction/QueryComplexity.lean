/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Query.Submodular.ValueQuery
public import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.Walrasian
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Combinatorial auctions: value queries vs. demand queries

In iterative combinatorial auctions, the auctioneer interacts with bidders as black-box oracles
([BlumrosenNisan2007], §11.5, pp. 283–285). Reusing `Cslib.Query.ValueQuery` for value oracles
(`S ↦ v S`) and `Cslib.FreeM` for query-counting programs, this module formalizes item-price demand
oracles and the query-complexity separation of §11.5.1 and Exercise 11.3, together with the
demand-query separation-oracle step of §11.5.2:

1. **Item-price demand oracle (`DemandQuery`, `DemandQuery.IsValidOracle`, §11.5.1, p. 284):**
   a query `.demand p` presents item prices `p : M → ℝ` and receives a bundle `T : Finset M`
   maximizing quasilinear utility `v S - ∑ j ∈ S, p j` (`IsDemand v p T`). Every valuation on a
   finite item set admits a valid demand oracle (`DemandQuery.exists_isValidOracle`).
2. **Simulating a value query with `m * t` demand queries (`valueQueryProg`,
   `eval_valueQueryProg`, `countQueries_valueQueryProg_le`; Lemma 11.22, p. 284):**
   for a normalized (`v ∅ = 0`) monotone valuation whose bundle values are `t`-bit integers in
   `{0, 1, ..., 2 ^ t - 1}` (fixed-point valuations with `t` bits of precision and known quantum
   `δ > 0` reduce by scaling prices by `δ`), `marginalValueProg` computes `v (insert j S) - v S`
   for `j ∉ S` in exactly `t` demand queries by binary search over half-integer test prices
   `thresh - 1 / 2` (with price `0` on `S` and `2 ^ t` outside `insert j S`, avoiding any demand
   tie-breaking ambiguity across arbitrary valid oracles). Telescoping over `S` yields
   `valueQueryProg`, which recovers `v S` in exactly `S.card * t ≤ Fintype.card M * t` demand
   queries.
3. **Exponential value-query lower bound for simulating a demand query and finding an optimal
   allocation (`choose_half_le_countQueries_demandSim`, `oneDemandQueryOptimalAlloc`,
   `eval_oneDemandQueryOptimalAlloc_optimal`, `choose_half_sub_one_le_countQueries_optimalAlloc`;
   Lemma 11.23, p. 284, and Exercise 11.3, p. 298):**
   for `2 ≤ Fintype.card M`, let `k = Fintype.card M / 2`. Every valuation in `IsSeparatorClassVal`
   — the base threshold valuation `thresholdBaseVal M` (`2` if `k < |S|`, else `0`) and each
   single-bundle bump `hiddenBundleVal M T` (`|T| = k`) — is normalized and monotone. At uniform
   item price `separatorPrice M = 4 / (2 * k + 1)`, the unique demand bundle of `thresholdBaseVal M`
   is `∅`, while the unique demand bundle of `hiddenBundleVal M T` is `T`. Consequently:
   * every deterministic `ValueQuery` program simulating a demand query at `separatorPrice M` on
     `IsSeparatorClassVal M` makes at least `(Fintype.card M).choose (Fintype.card M / 2)` value
     queries on `thresholdBaseVal M` (Lemma 11.23);
   * paired with the fixed normalized monotone valuation `complementThresholdVal M` for bidder `1`,
     a single demand query (`oneDemandQueryOptimalAlloc`) determines an optimal two-bidder
     allocation on every `IsSeparatorClassVal M` valuation, whereas every deterministic `ValueQuery`
     program finding an optimal allocation (even with full knowledge of bidder `1`) makes at least
     `(Fintype.card M).choose (Fintype.card M / 2) - 1` value queries on `thresholdBaseVal M`
     (Exercise 11.3; this bound is tight because an algorithm may guess one unqueried `k`-set).
   Notice `(Fintype.card M).choose (Fintype.card M / 2) ≥ 2 ^ (Fintype.card M / 2)` is exponential
   in `Fintype.card M` (see also `Nat.four_pow_le_two_mul_add_one_mul_centralBinom`).
4. **DLPR demand-query separation-oracle step (`isDLPRFeasible_iff_of_isValidOracle`,
   `dlprBidderCheckProg`, `isDLPRFeasible_iff_dlprBidderCheckProg`; step of §11.5.2, p. 285):**
   given nonnegative `(u, p)`, querying each bidder `i` once at prices `p` checks feasibility of
   the dual LP relaxation DLPR (`IsDLPRFeasible`) or exhibits a violated constraint (11.8), and
   `dlprBidderCheckProg` performs each bidder's check using only demand queries in at most
   `1 + Fintype.card M * t` queries. This is an intermediate step of [BlumrosenNisan2007], §11.5.2,
   and **not** the full polynomial-time Ellipsoid result (Theorem 11.24, p. 285), which remains open
   under issue `#7789`.

No running-time claims are made in this module: all bounds are exact oracle query counts in
`Cslib.FreeM`.

## Main definitions

* `Cslib.GameTheory.CombinatorialAuction.DemandQuery`, `DemandQuery.ask`,
  `DemandQuery.IsValidOracle`: item-price demand query signature and valid-oracle predicate
  ([BlumrosenNisan2007], §11.5.1, p. 284).
* `Cslib.GameTheory.CombinatorialAuction.marginalValueProg`,
  `Cslib.GameTheory.CombinatorialAuction.valueQueryProg`: demand-query programs simulating marginal
  and full value queries (Lemma 11.22, p. 284).
* `Cslib.GameTheory.CombinatorialAuction.thresholdBaseVal`,
  `Cslib.GameTheory.CombinatorialAuction.hiddenBundleVal`,
  `Cslib.GameTheory.CombinatorialAuction.IsSeparatorClassVal`,
  `Cslib.GameTheory.CombinatorialAuction.complementThresholdVal`,
  `Cslib.GameTheory.CombinatorialAuction.separatorPrice`,
  `Cslib.GameTheory.CombinatorialAuction.oneDemandQueryOptimalAlloc`: adversarial valuation class,
  separating price vector, and 1-demand-query optimal allocation program (Lemma 11.23 and
  Exercise 11.3, pp. 284 and 298).
* `Cslib.GameTheory.CombinatorialAuction.dlprBidderCheckProg`: demand-query separation-oracle
  subroutine for one bidder's DLPR constraints (step of §11.5.2, p. 285).

## Main results

* `DemandQuery.exists_isValidOracle`: every valuation on a finite item set admits a valid demand
  oracle.
* `eval_marginalValueProg`, `countQueries_marginalValueProg`: exact marginal-value recovery in `t`
  demand queries.
* `eval_valueQueryProg`, `countQueries_valueQueryProg`, `countQueries_valueQueryProg_le`:
  **Lemma 11.22** ([BlumrosenNisan2007], p. 284): simulating a value query in
  `S.card * t ≤ Fintype.card M * t` demand queries.
* `choose_half_le_countQueries_demandSim`: **Lemma 11.23** ([BlumrosenNisan2007], p. 284):
  `m.choose (m / 2)` value-query lower bound for simulating a single demand query.
* `countQueries_oneDemandQueryOptimalAlloc`, `eval_oneDemandQueryOptimalAlloc_optimal`,
  `choose_half_sub_one_le_countQueries_optimalAlloc`: **Exercise 11.3** ([BlumrosenNisan2007],
  p. 298): `1` demand query suffices for optimal allocation on `IsSeparatorClassVal`, whereas value
  queries require at least `m.choose (m / 2) - 1`.
* `isDLPRFeasible_iff_of_isValidOracle`, `countQueries_dlprBidderCheckProg_le`,
  `dlprBidderCheckProg_eq_none_iff`, `dlprBidderCheckProg_eq_some_violated`,
  `isDLPRFeasible_iff_dlprBidderCheckProg`: demand-query separation-oracle characterization for DLPR
  (step of [BlumrosenNisan2007], §11.5.2, p. 285; not Theorem 11.24).

## References

* [L. Blumrosen and N. Nisan, *Combinatorial Auctions*][BlumrosenNisan2007], Chapter 11,
  §§11.5.1–11.5.2 and Exercise 11.3, pp. 283–285 and 298.
-/

public section

namespace Cslib.GameTheory.CombinatorialAuction

open Finset Cslib.Query

/-! ### Item-price demand query oracle (§11.5.1, p. 284) -/

/-- Demand-oracle query signature with item prices for a combinatorial auction over item set `M`:
`.demand p` presents an item price vector `p : M → ℝ` and receives a bundle `T : Finset M`
([BlumrosenNisan2007], §11.5.1, p. 284). -/
inductive DemandQuery (M : Type) : Type → Type where
  | demand (p : M → ℝ) : DemandQuery M (Finset M)

/-- Issue a demand query at item prices `p` in `FreeM (DemandQuery M) (Finset M)`. -/
abbrev DemandQuery.ask {M : Type} (p : M → ℝ) : FreeM (DemandQuery M) (Finset M) :=
  FreeM.lift (.demand p)

@[simp] theorem DemandQuery.eval_ask {M : Type}
    (oracle : {ι : Type} → DemandQuery M ι → ι) (p : M → ℝ) :
    (DemandQuery.ask p).eval oracle = oracle (.demand p) := rfl

theorem DemandQuery.countQueries_ask {M : Type}
    (oracle : {ι : Type} → DemandQuery M ι → ι) (p : M → ℝ) :
    (DemandQuery.ask p).countQueries oracle = 1 :=
  FreeM.countQueries_lift oracle (.demand p)

/-- A `DemandQuery M` oracle is *valid* for valuation `v : Finset M → ℝ` if, at every item price
vector `p`, it returns a demand bundle maximizing `v S - ∑ j ∈ S, p j`
([BlumrosenNisan2007], Definition 11.11 and §11.5.1, pp. 277 and 284). -/
@[expose] def DemandQuery.IsValidOracle {M : Type} (v : Finset M → ℝ)
    (oracle : {ι : Type} → DemandQuery M ι → ι) : Prop :=
  ∀ p : M → ℝ, IsDemand v p (oracle (.demand p))

/-- Every valuation on a finite item set admits a valid demand oracle. -/
theorem DemandQuery.exists_isValidOracle {M : Type} [Finite M] (v : Finset M → ℝ) :
    ∃ oracle : {ι : Type} → DemandQuery M ι → ι, DemandQuery.IsValidOracle v oracle := by
  classical
  refine ⟨fun {ι} q => match q with
    | .demand p => (exists_isDemand v p).choose, fun p => (exists_isDemand v p).choose_spec⟩

/-! ### Lemma 11.22: simulating value queries with `m * t` demand queries (§11.5.1, p. 284) -/

section ValueSimulation

variable {M : Type} [DecidableEq M]

/-- Price vector testing whether the marginal value of `j` relative to `S` is at least `thresh`:
items in `S` cost `0`, item `j` costs `thresh - 1 / 2`, and items outside `insert j S` cost
`2 ^ t` (acting as `∞` for valuations bounded strictly below `2 ^ t`). Using a half-integer price
for `j` eliminates demand ties for all integer-valued valuations. -/
private noncomputable def marginalPrice (t : ℕ) (S : Finset M) (j : M) (thresh : ℕ) : M → ℝ :=
  fun i => if i ∈ S then 0 else if i = j then (thresh : ℝ) - 1 / 2 else (2 : ℝ) ^ t

/-- `k`-step binary search over `[lo, lo + 2 ^ k)` for the marginal value of `j` relative to `S`. -/
private noncomputable def marginalSearchAux (t : ℕ) (S : Finset M) (j : M) :
    ℕ → ℕ → FreeM (DemandQuery M) ℕ
  | 0, lo => pure lo
  | k + 1, lo => do
    let D ← DemandQuery.ask (marginalPrice t S j (lo + 2 ^ k))
    if j ∈ D then
      marginalSearchAux t S j k (lo + 2 ^ k)
    else
      marginalSearchAux t S j k lo

/-- Demand-query program computing the marginal value `v (insert j S) - v S` for `j ∉ S` and a
monotone `t`-bit integer-valued valuation `v` in `t` demand queries
([BlumrosenNisan2007], proof of Lemma 11.22, p. 284). -/
noncomputable def marginalValueProg (t : ℕ) (S : Finset M) (j : M) : FreeM (DemandQuery M) ℕ :=
  marginalSearchAux t S j t 0

/-- Telescoping demand-query program accumulating marginal values over a list of items, starting
from `acc` and skipping items already in `acc`. -/
private noncomputable def valueQueryListAux (t : ℕ) :
    Finset M → List M → FreeM (DemandQuery M) ℕ
  | _, [] => pure 0
  | acc, j :: rest =>
    if j ∈ acc then
      valueQueryListAux t acc rest
    else do
      let mv ← marginalValueProg t acc j
      let tail ← valueQueryListAux t (insert j acc) rest
      pure (mv + tail)

/-- Demand-query program simulating a value query `v S` for a normalized monotone `t`-bit
integer-valued valuation `v` by telescoping `marginalValueProg` over the elements of `S`
([BlumrosenNisan2007], Lemma 11.22, p. 284). -/
noncomputable def valueQueryProg (t : ℕ) (S : Finset M) : FreeM (DemandQuery M) ℕ :=
  valueQueryListAux t ∅ S.toList

private theorem marginalPrice_nonneg {t : ℕ} {S : Finset M} {j : M} {thresh : ℕ}
    (hthresh : 1 ≤ thresh) (i : M) :
    0 ≤ marginalPrice t S j thresh i := by
  unfold marginalPrice
  split_ifs
  · exact le_rfl
  · have h1 : (1 : ℝ) ≤ (thresh : ℝ) := by exact_mod_cast hthresh
    linarith
  · positivity

private theorem sum_marginalPrice_of_subset {t : ℕ} {S T : Finset M} {j : M} {thresh : ℕ}
    (hTS : T ⊆ S) :
    ∑ i ∈ T, marginalPrice t S j thresh i = 0 :=
  Finset.sum_eq_zero fun i hi => by simp [marginalPrice, hTS hi]

private theorem sum_marginalPrice_of_mem_insert {t : ℕ} {S T : Finset M} {j : M} {thresh : ℕ}
    (hjS : j ∉ S) (hT : T ⊆ insert j S) (hjT : j ∈ T) :
    ∑ i ∈ T, marginalPrice t S j thresh i = (thresh : ℝ) - 1 / 2 := by
  rw [← Finset.insert_erase hjT, Finset.sum_insert (Finset.notMem_erase j T)]
  have herase : T.erase j ⊆ S := by
    intro i hi
    rcases Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hi)) with rfl | hiS
    · exact absurd hi (Finset.notMem_erase _ _)
    · exact hiS
  rw [sum_marginalPrice_of_subset herase, add_zero]
  simp [marginalPrice, hjS]

private theorem mem_demand_marginalPrice_iff {v : Finset M → ℝ} {f : Finset M → ℕ} {t : ℕ}
    (hmono : Monotone v) (hval : ∀ R, v R = (f R : ℝ)) (hbound : ∀ R, f R < 2 ^ t)
    {S D : Finset M} {j : M} {thresh : ℕ} (hjS : j ∉ S) (hthresh : 1 ≤ thresh)
    (hD : IsDemand v (marginalPrice t S j thresh) D) :
    j ∈ D ↔ thresh ≤ f (insert j S) - f S := by
  have hS_util : v S - ∑ i ∈ S, marginalPrice t S j thresh i = (f S : ℝ) := by
    rw [sum_marginalPrice_of_subset (Finset.Subset.refl S), sub_zero, hval S]
  have hD_sub : D ⊆ insert j S := by
    intro x hxD
    by_contra hx
    have hxS : x ∉ S := fun h => hx (Finset.mem_insert_of_mem h)
    have hxj : x ≠ j := fun h => hx (h ▸ Finset.mem_insert_self j S)
    have hpx : marginalPrice t S j thresh x = (2 : ℝ) ^ t := by simp [marginalPrice, hxS, hxj]
    have hsum : (2 : ℝ) ^ t ≤ ∑ i ∈ D, marginalPrice t S j thresh i := by
      rw [← hpx]
      exact Finset.single_le_sum (fun i _ => marginalPrice_nonneg hthresh i) hxD
    have hfD : (f D : ℝ) < (2 : ℝ) ^ t := by exact_mod_cast hbound D
    have hD_lt : v D - ∑ i ∈ D, marginalPrice t S j thresh i < 0 := by
      rw [hval D]; linarith
    have hge := hD S
    have hfS : (0 : ℝ) ≤ (f S : ℝ) := Nat.cast_nonneg _
    linarith
  have hf_le : f S ≤ f (insert j S) := by
    have h := hmono (Finset.subset_insert j S)
    rw [hval S, hval (insert j S)] at h
    exact_mod_cast h
  have hdiff_cast : ((f (insert j S) - f S : ℕ) : ℝ) = (f (insert j S) : ℝ) - (f S : ℝ) :=
    Nat.cast_sub hf_le
  have hjS_util : v (insert j S) - ∑ i ∈ insert j S, marginalPrice t S j thresh i =
      (f (insert j S) : ℝ) - ((thresh : ℝ) - 1 / 2) := by
    rw [sum_marginalPrice_of_mem_insert hjS (Finset.Subset.refl _) (Finset.mem_insert_self j S),
      hval (insert j S)]
  constructor
  · intro hjD
    by_contra hlt
    push Not at hlt
    have hle : (f (insert j S) - f S : ℕ) + 1 ≤ thresh := hlt
    have hle_r : ((f (insert j S) - f S : ℕ) : ℝ) + 1 ≤ (thresh : ℝ) := by exact_mod_cast hle
    have hD_le : v D ≤ v (insert j S) := hmono hD_sub
    have hD_price := sum_marginalPrice_of_mem_insert (t := t) (thresh := thresh) hjS hD_sub hjD
    have hge := hD S
    rw [hD_price, hS_util] at hge
    rw [hval (insert j S)] at hD_le
    linarith
  · intro hge_thresh
    by_contra hjD
    have hDS : D ⊆ S := by
      intro x hxD
      rcases Finset.mem_insert.mp (hD_sub hxD) with rfl | hxS
      · exact absurd hxD hjD
      · exact hxS
    have hD_le : v D ≤ v S := hmono hDS
    have hD_price := sum_marginalPrice_of_subset (t := t) (j := j) (thresh := thresh) hDS
    have hge := hD (insert j S)
    have hge_r : (thresh : ℝ) ≤ ((f (insert j S) - f S : ℕ) : ℝ) := by exact_mod_cast hge_thresh
    rw [hD_price, sub_zero, hjS_util] at hge
    rw [hval S] at hD_le
    linarith

private theorem eval_marginalSearchAux {v : Finset M → ℝ} {f : Finset M → ℕ} {t : ℕ}
    (hmono : Monotone v) (hval : ∀ R, v R = (f R : ℝ)) (hbound : ∀ R, f R < 2 ^ t)
    {oracle : {ι : Type} → DemandQuery M ι → ι}
    (horacle : DemandQuery.IsValidOracle v oracle)
    {S : Finset M} {j : M} (hjS : j ∉ S) :
    ∀ (k lo : ℕ), lo ≤ f (insert j S) - f S → f (insert j S) - f S < lo + 2 ^ k →
      (marginalSearchAux t S j k lo).eval oracle = f (insert j S) - f S
  | 0, lo, hlo, hhi => by
    simp only [marginalSearchAux, FreeM.eval_pure]
    omega
  | k + 1, lo, hlo, hhi => by
    simp only [marginalSearchAux, DemandQuery.ask, FreeM.eval_liftBind]
    have hthresh : 1 ≤ lo + 2 ^ k := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    have hiff := mem_demand_marginalPrice_iff hmono hval hbound hjS hthresh
      (horacle (marginalPrice t S j (lo + 2 ^ k)))
    split_ifs with hjD
    · have hge := hiff.mp hjD
      exact eval_marginalSearchAux hmono hval hbound horacle hjS k (lo + 2 ^ k) hge
        (by rw [pow_succ] at hhi; omega)
    · have hlt : f (insert j S) - f S < lo + 2 ^ k := Nat.lt_of_not_ge (mt hiff.mpr hjD)
      exact eval_marginalSearchAux hmono hval hbound horacle hjS k lo hlo hlt

private theorem countQueries_marginalSearchAux (t : ℕ) (S : Finset M) (j : M)
    (oracle : {ι : Type} → DemandQuery M ι → ι) :
    ∀ (k lo : ℕ), (marginalSearchAux t S j k lo).countQueries oracle = k
  | 0, _ => rfl
  | k + 1, lo => by
    simp only [marginalSearchAux, DemandQuery.ask, FreeM.countQueries_liftBind]
    split_ifs <;> rw [countQueries_marginalSearchAux] <;> omega

/-- `marginalValueProg t S j` recovers the exact marginal value `v (insert j S) - v S` for every
monotone `t`-bit integer-valued valuation `v`, every `j ∉ S`, and every valid demand oracle
([BlumrosenNisan2007], proof of Lemma 11.22, p. 284). -/
theorem eval_marginalValueProg {v : Finset M → ℝ} {t : ℕ}
    (hmono : Monotone v)
    (hbit : ∃ f : Finset M → ℕ, (∀ R, v R = (f R : ℝ)) ∧ ∀ R, f R < 2 ^ t)
    {oracle : {ι : Type} → DemandQuery M ι → ι}
    (horacle : DemandQuery.IsValidOracle v oracle)
    {S : Finset M} {j : M} (hjS : j ∉ S) :
    (((marginalValueProg t S j).eval oracle : ℕ) : ℝ) = v (insert j S) - v S := by
  obtain ⟨f, hval, hbound⟩ := hbit
  have heq : (marginalValueProg t S j).eval oracle = f (insert j S) - f S :=
    eval_marginalSearchAux hmono hval hbound horacle hjS t 0 (Nat.zero_le _)
      (by have := hbound (insert j S); omega)
  have hf_le : f S ≤ f (insert j S) := by
    have h := hmono (Finset.subset_insert j S)
    rw [hval S, hval (insert j S)] at h
    exact_mod_cast h
  rw [heq, Nat.cast_sub hf_le, hval (insert j S), hval S]

/-- `marginalValueProg t S j` always issues exactly `t` demand queries (for any oracle). -/
theorem countQueries_marginalValueProg (t : ℕ) (S : Finset M) (j : M)
    (oracle : {ι : Type} → DemandQuery M ι → ι) :
    (marginalValueProg t S j).countQueries oracle = t :=
  countQueries_marginalSearchAux t S j oracle t 0

private theorem eval_valueQueryListAux {v : Finset M → ℝ} {t : ℕ}
    (hmono : Monotone v)
    (hbit : ∃ f : Finset M → ℕ, (∀ R, v R = (f R : ℝ)) ∧ ∀ R, f R < 2 ^ t)
    {oracle : {ι : Type} → DemandQuery M ι → ι}
    (horacle : DemandQuery.IsValidOracle v oracle) :
    ∀ (acc : Finset M) (xs : List M),
      (((valueQueryListAux t acc xs).eval oracle : ℕ) : ℝ) = v (acc ∪ xs.toFinset) - v acc
  | acc, [] => by simp [valueQueryListAux]
  | acc, j :: rest => by
    simp only [valueQueryListAux]
    split_ifs with hj
    · rw [eval_valueQueryListAux hmono hbit horacle acc rest]
      congr 2
      ext x
      simp only [Finset.mem_union, List.toFinset_cons, Finset.mem_insert]
      exact ⟨fun h => h.imp_right Or.inr,
        fun h => h.elim Or.inl fun h' => h'.elim (fun hx => Or.inl (hx ▸ hj)) Or.inr⟩
    · simp only [FreeM.eval_bind, FreeM.eval_pure, Nat.cast_add]
      rw [eval_marginalValueProg hmono hbit horacle hj,
        eval_valueQueryListAux hmono hbit horacle (insert j acc) rest]
      have hunion : insert j acc ∪ rest.toFinset = acc ∪ (j :: rest).toFinset := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
        constructor
        · rintro ((rfl | ha) | hr)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl ha
          · exact Or.inr (Or.inr hr)
        · rintro (ha | rfl | hr)
          · exact Or.inl (Or.inr ha)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr hr
      rw [hunion]
      linarith

private theorem countQueries_valueQueryListAux (t : ℕ)
    (oracle : {ι : Type} → DemandQuery M ι → ι) :
    ∀ (acc : Finset M) (xs : List M),
      (valueQueryListAux t acc xs).countQueries oracle = (xs.toFinset \ acc).card * t
  | acc, [] => by simp [valueQueryListAux]
  | acc, j :: rest => by
    simp only [valueQueryListAux]
    split_ifs with hj
    · rw [countQueries_valueQueryListAux t oracle acc rest]
      congr 2
      ext x
      simp only [Finset.mem_sdiff, List.toFinset_cons, Finset.mem_insert]
      exact ⟨fun ⟨hx, hna⟩ => ⟨Or.inr hx, hna⟩,
        fun ⟨hx, hna⟩ => ⟨hx.elim (fun h => absurd (h ▸ hj) hna) id, hna⟩⟩
    · simp only [FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero,
        countQueries_marginalValueProg, countQueries_valueQueryListAux]
      have hdiff : (j :: rest).toFinset \ acc = insert j (rest.toFinset \ insert j acc) := by
        ext x
        simp only [Finset.mem_sdiff, List.toFinset_cons, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hrest, hna⟩
          · exact Or.inl rfl
          · by_cases hxj : x = j
            · exact Or.inl hxj
            · exact Or.inr ⟨hrest, fun h => h.elim hxj hna⟩
        · rintro (rfl | ⟨hrest, hna⟩)
          · exact ⟨Or.inl rfl, hj⟩
          · exact ⟨Or.inr hrest, fun h => hna (Or.inr h)⟩
      have hj_not : j ∉ rest.toFinset \ insert j acc := by simp
      rw [hdiff, Finset.card_insert_of_notMem hj_not, Nat.add_mul, one_mul, Nat.add_comm]

/-- **Lemma 11.22 (correctness)** ([BlumrosenNisan2007], §11.5.1, p. 284): for every normalized
(`v ∅ = 0`) monotone valuation `v : Finset M → ℝ` whose bundle values are `t`-bit integers in
`{0, 1, ..., 2 ^ t - 1}` and every valid demand oracle `oracle` for `v`, `valueQueryProg t S`
returns `v S`. -/
theorem eval_valueQueryProg {v : Finset M → ℝ} {t : ℕ}
    (h0 : v ∅ = 0) (hmono : Monotone v)
    (hbit : ∃ f : Finset M → ℕ, (∀ R, v R = (f R : ℝ)) ∧ ∀ R, f R < 2 ^ t)
    {oracle : {ι : Type} → DemandQuery M ι → ι}
    (horacle : DemandQuery.IsValidOracle v oracle) (S : Finset M) :
    (((valueQueryProg t S).eval oracle : ℕ) : ℝ) = v S := by
  unfold valueQueryProg
  rw [eval_valueQueryListAux hmono hbit horacle ∅ S.toList, Finset.empty_union,
    Finset.toList_toFinset, h0, sub_zero]

/-- `valueQueryProg t S` makes exactly `S.card * t` demand queries against any oracle. -/
theorem countQueries_valueQueryProg (t : ℕ) (S : Finset M)
    (oracle : {ι : Type} → DemandQuery M ι → ι) :
    (valueQueryProg t S).countQueries oracle = S.card * t := by
  unfold valueQueryProg
  rw [countQueries_valueQueryListAux, Finset.toList_toFinset, Finset.sdiff_empty]

/-- **Lemma 11.22 (query bound)** ([BlumrosenNisan2007], §11.5.1, p. 284): on a finite item set `M`
of cardinality `m = Fintype.card M`, `valueQueryProg t S` makes at most `m * t` demand queries. -/
theorem countQueries_valueQueryProg_le [Fintype M] (t : ℕ) (S : Finset M)
    (oracle : {ι : Type} → DemandQuery M ι → ι) :
    (valueQueryProg t S).countQueries oracle ≤ Fintype.card M * t := by
  rw [countQueries_valueQueryProg]
  exact Nat.mul_le_mul_right t (Finset.card_le_univ S)

end ValueSimulation

/-! ### Lemma 11.23 & Exercise 11.3: exponential value-query lower bound (§11.5.1, pp. 284, 298) -/

private theorem welfare_two {M : Type} (v₁ v₂ : Finset M → ℝ) (a : Allocation (Fin 2) M) :
    welfare ![v₁, v₂] a = v₁ (a.bundle 0) + v₂ (a.bundle 1) := by
  simp [welfare, Fin.sum_univ_two]

section DemandSeparation

variable {M : Type} [Fintype M]

/-- Base threshold valuation for the value-vs.-demand separation: assigns `2` to bundles of size
strictly greater than `Fintype.card M / 2` and `0` to all smaller bundles
([BlumrosenNisan2007], Lemma 11.23 and Exercise 11.3, pp. 284 and 298). -/
@[expose] def thresholdBaseVal (M : Type) [Fintype M] (S : Finset M) : ℝ :=
  if Fintype.card M / 2 < S.card then 2 else 0

open scoped Classical in
/-- Hidden-bundle valuation for a target bundle `T` of size `Fintype.card M / 2`: assigns `2` to
supersets of `T` and to all bundles of size strictly greater than `Fintype.card M / 2`, and `0`
otherwise. It agrees with `thresholdBaseVal M` on every bundle except `T`. -/
@[expose] noncomputable def hiddenBundleVal (M : Type) [Fintype M] (T S : Finset M) : ℝ :=
  if T ⊆ S ∨ Fintype.card M / 2 < S.card then 2 else 0

/-- Adversarial class of bidder-0 valuations witnessing Lemma 11.23 and Exercise 11.3
([BlumrosenNisan2007], pp. 284 and 298): `thresholdBaseVal M` together with `hiddenBundleVal M T`
for every bundle `T` of size `Fintype.card M / 2`. -/
@[expose] def IsSeparatorClassVal (M : Type) [Fintype M] (v : Finset M → ℝ) : Prop :=
  v = thresholdBaseVal M ∨ ∃ T : Finset M, T.card = Fintype.card M / 2 ∧
    v = hiddenBundleVal M T

/-- Fixed bidder-1 valuation paired with `IsSeparatorClassVal M` in Exercise 11.3: assigns `2` to
every bundle of size at least `Fintype.card M - Fintype.card M / 2` and `0` otherwise. -/
@[expose] def complementThresholdVal (M : Type) [Fintype M] (S : Finset M) : ℝ :=
  if Fintype.card M - Fintype.card M / 2 ≤ S.card then 2 else 0

/-- Uniform item price vector `4 / (2 * (m / 2) + 1)` separating `thresholdBaseVal M` (unique
demand `∅`) from every `hiddenBundleVal M T` with `|T| = m / 2` (unique demand `T`). -/
@[expose] noncomputable def separatorPrice (M : Type) [Fintype M] : M → ℝ :=
  fun _ => 4 / (2 * (Fintype.card M / 2 : ℕ) + 1)

/-- Every valuation in `IsSeparatorClassVal M` is normalized (`v ∅ = 0`) and monotone when
`2 ≤ Fintype.card M`. -/
theorem IsSeparatorClassVal.empty_and_monotone (hm : 2 ≤ Fintype.card M)
    {v : Finset M → ℝ} (hv : IsSeparatorClassVal M v) :
    v ∅ = 0 ∧ Monotone v := by
  rcases hv with rfl | ⟨T, hT, rfl⟩
  · refine ⟨by simp [thresholdBaseVal], fun S₁ S₂ hsub => ?_⟩
    unfold thresholdBaseVal
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (lt_of_lt_of_le h1 (Finset.card_le_card hsub)) h2
    · norm_num
    · exact le_rfl
  · refine ⟨?_, fun S₁ S₂ hsub => ?_⟩
    · have hne : ¬ T ⊆ ∅ := by
        intro h
        have hc := Finset.card_le_card h
        simp only [Finset.card_empty] at hc
        omega
      simp [hiddenBundleVal, hne]
    · unfold hiddenBundleVal
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso; apply h2
        exact h1.imp (fun h => h.trans hsub) (fun h => lt_of_lt_of_le h (Finset.card_le_card hsub))
      · norm_num
      · exact le_rfl

/-- `complementThresholdVal M` is normalized (`v ∅ = 0`) and monotone when `2 ≤ Fintype.card M`. -/
theorem complementThresholdVal_empty_and_monotone (hm : 2 ≤ Fintype.card M) :
    complementThresholdVal M ∅ = 0 ∧ Monotone (complementThresholdVal M) := by
  refine ⟨?_, fun S₁ S₂ hsub => ?_⟩
  · have hpos : ¬ Fintype.card M - Fintype.card M / 2 ≤ 0 := by omega
    simp [complementThresholdVal, hpos]
  · unfold complementThresholdVal
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans (Finset.card_le_card hsub)) h2
    · norm_num
    · exact le_rfl

private theorem hiddenBundleVal_eq_thresholdBaseVal_of_ne {T S : Finset M}
    (hT : T.card = Fintype.card M / 2) (hne : S ≠ T) :
    hiddenBundleVal M T S = thresholdBaseVal M S := by
  unfold hiddenBundleVal thresholdBaseVal
  by_cases hcard : Fintype.card M / 2 < S.card
  · simp [hcard]
  · have hnot : ¬ T ⊆ S := by
      intro hsub
      exact hne ((Finset.eq_of_subset_of_card_le hsub (by omega)).symm)
    simp [hcard, hnot]

private theorem thresholdBaseVal_util_lt_zero {S : Finset M} (hS : S ≠ ∅) :
    thresholdBaseVal M S - ∑ j ∈ S, separatorPrice M j < 0 := by
  set k : ℕ := Fintype.card M / 2
  have hden : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  unfold thresholdBaseVal separatorPrice
  rw [Finset.sum_const, nsmul_eq_mul]
  split_ifs with hgt
  · have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hgt
    have hdiv : 2 < (S.card : ℝ) * (4 / (2 * (k : ℝ) + 1)) := by
      rw [mul_div_assoc', lt_div_iff₀ hden]
      push_cast at hk1
      linarith
    linarith
  · have hpos : (0 : ℝ) < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (nonempty_iff_ne_empty.mpr hS)
    have hp : (0 : ℝ) < 4 / (2 * (k : ℝ) + 1) := by positivity
    nlinarith

private theorem isDemand_thresholdBaseVal_iff (D : Finset M) :
    IsDemand (thresholdBaseVal M) (separatorPrice M) D ↔ D = ∅ := by
  constructor
  · intro hD
    by_contra hne
    have hlt := thresholdBaseVal_util_lt_zero hne
    have h0 := hD ∅
    have hempty : thresholdBaseVal M ∅ - ∑ j ∈ (∅ : Finset M), separatorPrice M j = 0 := by
      simp [thresholdBaseVal]
    linarith
  · rintro rfl S
    have hempty : thresholdBaseVal M ∅ - ∑ j ∈ (∅ : Finset M), separatorPrice M j = 0 := by
      simp [thresholdBaseVal]
    rw [hempty]
    by_cases hS : S = ∅
    · subst hS; exact hempty.le
    · exact (thresholdBaseVal_util_lt_zero hS).le

private theorem hiddenBundleVal_util_pos {T : Finset M} (hT : T.card = Fintype.card M / 2) :
    0 < hiddenBundleVal M T T - ∑ j ∈ T, separatorPrice M j := by
  set k : ℕ := Fintype.card M / 2
  have hden : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  unfold hiddenBundleVal separatorPrice
  rw [Finset.sum_const, nsmul_eq_mul, hT]
  simp only [Finset.Subset.refl, true_or, ↓reduceIte]
  have : (k : ℝ) * (4 / (2 * (k : ℝ) + 1)) < 2 := by
    rw [mul_div_assoc', div_lt_iff₀ hden]; linarith
  linarith

private theorem isDemand_hiddenBundleVal_iff {T : Finset M} (hT : T.card = Fintype.card M / 2)
    (D : Finset M) :
    IsDemand (hiddenBundleVal M T) (separatorPrice M) D ↔ D = T := by
  have hpos := hiddenBundleVal_util_pos hT
  have hnonpos : ∀ S, S ≠ T → hiddenBundleVal M T S - ∑ j ∈ S, separatorPrice M j ≤ 0 := by
    intro S hne
    rw [hiddenBundleVal_eq_thresholdBaseVal_of_ne hT hne]
    by_cases hS : S = ∅
    · subst hS; simp [thresholdBaseVal]
    · exact (thresholdBaseVal_util_lt_zero hS).le
  constructor
  · intro hD
    by_contra hne
    linarith [hD T, hnonpos D hne]
  · intro hEq S
    subst hEq
    by_cases hSD : S = D
    · rw [hSD]
    · exact (hnonpos S hSD).trans hpos.le

/-- **Lemma 11.23** ([BlumrosenNisan2007], §11.5.1, p. 284): for any finite item set `M` with
`2 ≤ Fintype.card M`, every deterministic `ValueQuery` program that simulates a single demand query
at `separatorPrice M` across the normalized monotone valuations in `IsSeparatorClassVal M` (and in
particular across all normalized monotone valuations) makes at least
`(Fintype.card M).choose (Fintype.card M / 2)` value queries on `thresholdBaseVal M`. -/
theorem choose_half_le_countQueries_demandSim (hm : 2 ≤ Fintype.card M)
    (prog : FreeM (ValueQuery M ℝ) (Finset M))
    (hsim : ∀ v : Finset M → ℝ, IsSeparatorClassVal M v →
      IsDemand v (separatorPrice M) (prog.eval (ValueQuery.oracleOf v))) :
    (Fintype.card M).choose (Fintype.card M / 2) ≤
      prog.countQueries (ValueQuery.oracleOf (thresholdBaseVal M)) := by
  classical
  set k := Fintype.card M / 2
  set v₀ := thresholdBaseVal M
  have heval₀ : prog.eval (ValueQuery.oracleOf v₀) = ∅ :=
    (isDemand_thresholdBaseVal_iff _).mp (hsim v₀ (Or.inl rfl))
  have hsub : Finset.powersetCard k (Finset.univ : Finset M) ⊆
      ValueQuery.queriedSets (ValueQuery.oracleOf v₀) prog := by
    intro T hT
    have hTcard : T.card = k := (Finset.mem_powersetCard.mp hT).2
    by_contra hnot
    have hagree : ∀ S ∈ ValueQuery.queriedSets (ValueQuery.oracleOf v₀) prog,
        ValueQuery.oracleOf v₀ (.value S) =
          ValueQuery.oracleOf (hiddenBundleVal M T) (.value S) := by
      intro S hS
      have hne : S ≠ T := fun h => hnot (h ▸ hS)
      exact (hiddenBundleVal_eq_thresholdBaseVal_of_ne hTcard hne).symm
    have heq := ValueQuery.eval_eq_of_agree_on_queriedSets prog hagree
    have hdemT : IsDemand (hiddenBundleVal M T) (separatorPrice M) ∅ := by
      rw [← heval₀, heq]
      exact hsim _ (Or.inr ⟨T, hTcard, rfl⟩)
    have hTempty : ∅ = T := (isDemand_hiddenBundleVal_iff hTcard ∅).mp hdemT
    rw [← hTempty, Finset.card_empty] at hTcard
    omega
  calc (Fintype.card M).choose k
      = (Finset.powersetCard k (Finset.univ : Finset M)).card := by
          rw [Finset.card_powersetCard, Finset.card_univ]
    _ ≤ (ValueQuery.queriedSets (ValueQuery.oracleOf v₀) prog).card := Finset.card_le_card hsub
    _ ≤ prog.countQueries (ValueQuery.oracleOf v₀) :=
          ValueQuery.card_queriedSets_le_countQueries _ _

/-- Two-bidder partition allocation assigning `D` to bidder `0` and its complement `Dᶜ` to
bidder `1`. -/
private def partitionAlloc [DecidableEq M] (D : Finset M) : Allocation (Fin 2) M where
  bundle := ![D, Dᶜ]
  disjoint i₁ i₂ hne := by
    fin_cases i₁ <;> fin_cases i₂
    · exact absurd rfl hne
    · exact disjoint_compl_right
    · exact disjoint_compl_left
    · exact absurd rfl hne

/-- Single-demand-query program for Exercise 11.3 ([BlumrosenNisan2007], p. 298): queries bidder `0`
once at `separatorPrice M` and allocates the returned demand bundle `D` to bidder `0` and `Dᶜ` to
bidder `1`. -/
noncomputable def oneDemandQueryOptimalAlloc (M : Type) [Fintype M] [DecidableEq M] :
    FreeM (DemandQuery M) (Allocation (Fin 2) M) := do
  let D ← DemandQuery.ask (separatorPrice M)
  pure (partitionAlloc D)

/-- `oneDemandQueryOptimalAlloc M` makes exactly `1` demand query against any oracle. -/
theorem countQueries_oneDemandQueryOptimalAlloc [DecidableEq M]
    (oracle : {ι : Type} → DemandQuery M ι → ι) :
    (oneDemandQueryOptimalAlloc M).countQueries oracle = 1 := by
  simp [oneDemandQueryOptimalAlloc]

private theorem card_add_card_le_of_alloc (a : Allocation (Fin 2) M) :
    (a.bundle 0).card + (a.bundle 1).card ≤ Fintype.card M := by
  classical
  have hdisj : Disjoint (a.bundle 0) (a.bundle 1) := a.disjoint (by decide : (0 : Fin 2) ≠ 1)
  rw [← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_univ _

private theorem welfare_thresholdBaseVal_le (b : Allocation (Fin 2) M) :
    welfare ![thresholdBaseVal M, complementThresholdVal M] b ≤ 2 := by
  rw [welfare_two]
  have hcard := card_add_card_le_of_alloc b
  unfold thresholdBaseVal complementThresholdVal
  split_ifs with h1 h2
  · omega
  · norm_num
  · norm_num
  · norm_num

private theorem welfare_hiddenBundleVal_le {T : Finset M} (b : Allocation (Fin 2) M) :
    welfare ![hiddenBundleVal M T, complementThresholdVal M] b ≤ 4 := by
  rw [welfare_two]
  unfold hiddenBundleVal complementThresholdVal
  split_ifs <;> norm_num

private theorem welfare_hiddenBundleVal_partitionAlloc [DecidableEq M] {T : Finset M}
    (hT : T.card = Fintype.card M / 2) :
    welfare ![hiddenBundleVal M T, complementThresholdVal M] (partitionAlloc T) = 4 := by
  rw [welfare_two]
  have h0 : (partitionAlloc T).bundle 0 = T := rfl
  have h1 : (partitionAlloc T).bundle 1 = Tᶜ := rfl
  have hTc : (Tᶜ).card = Fintype.card M - Fintype.card M / 2 := by
    rw [Finset.card_compl, hT]
  rw [h0, h1]
  simp only [hiddenBundleVal, complementThresholdVal, true_or, ↓reduceIte, hTc, le_refl]
  norm_num

/-- **Exercise 11.3 (1-demand-query upper bound)** ([BlumrosenNisan2007], p. 298): for every
`v₁` in `IsSeparatorClassVal M` paired with bidder `1`'s valuation `complementThresholdVal M`,
`oneDemandQueryOptimalAlloc M` finds a welfare-maximizing allocation using `1` demand query to any
valid demand oracle for `v₁`. -/
theorem eval_oneDemandQueryOptimalAlloc_optimal [DecidableEq M]
    {v₁ : Finset M → ℝ} (hv₁ : IsSeparatorClassVal M v₁)
    {oracle : {ι : Type} → DemandQuery M ι → ι}
    (horacle : DemandQuery.IsValidOracle v₁ oracle) (b : Allocation (Fin 2) M) :
    welfare ![v₁, complementThresholdVal M] b ≤
      welfare ![v₁, complementThresholdVal M] ((oneDemandQueryOptimalAlloc M).eval oracle) := by
  simp only [oneDemandQueryOptimalAlloc, DemandQuery.ask, FreeM.eval_liftBind, FreeM.eval_pure]
  rcases hv₁ with rfl | ⟨T, hT, rfl⟩
  · have hD : oracle (.demand (separatorPrice M)) = ∅ :=
      (isDemand_thresholdBaseVal_iff _).mp (horacle (separatorPrice M))
    rw [hD]
    have hval : welfare ![thresholdBaseVal M, complementThresholdVal M]
        (partitionAlloc (∅ : Finset M)) = 2 := by
      rw [welfare_two]
      have h0 : (partitionAlloc (∅ : Finset M)).bundle 0 = ∅ := rfl
      have h1 : (partitionAlloc (∅ : Finset M)).bundle 1 = Finset.univ := by
        simp [partitionAlloc]
      rw [h0, h1]
      simp only [thresholdBaseVal, complementThresholdVal, Finset.card_empty, Nat.not_lt_zero,
        ↓reduceIte, Finset.card_univ, zero_add]
      have hle : Fintype.card M - Fintype.card M / 2 ≤ Fintype.card M := Nat.sub_le _ _
      simp [hle]
    rw [hval]
    exact welfare_thresholdBaseVal_le b
  · have hD : oracle (.demand (separatorPrice M)) = T :=
      (isDemand_hiddenBundleVal_iff hT _).mp (horacle (separatorPrice M))
    rw [hD, welfare_hiddenBundleVal_partitionAlloc hT]
    exact welfare_hiddenBundleVal_le b

/-- **Exercise 11.3 (exponential value-query lower bound)** ([BlumrosenNisan2007], p. 298): for
any finite item set `M`, every deterministic `ValueQuery` program that finds a welfare-maximizing
allocation for `![v₁, complementThresholdVal M]` across all `v₁` in `IsSeparatorClassVal M` (even
with full free knowledge of bidder `1`'s valuation) makes at least
`(Fintype.card M).choose (Fintype.card M / 2) - 1` value queries on `thresholdBaseVal M`. -/
theorem choose_half_sub_one_le_countQueries_optimalAlloc
    (prog : FreeM (ValueQuery M ℝ) (Allocation (Fin 2) M))
    (hopt : ∀ v₁ : Finset M → ℝ, IsSeparatorClassVal M v₁ →
      ∀ b : Allocation (Fin 2) M,
        welfare ![v₁, complementThresholdVal M] b ≤
          welfare ![v₁, complementThresholdVal M] (prog.eval (ValueQuery.oracleOf v₁))) :
    (Fintype.card M).choose (Fintype.card M / 2) - 1 ≤
      prog.countQueries (ValueQuery.oracleOf (thresholdBaseVal M)) := by
  classical
  set k := Fintype.card M / 2
  set v₀ := thresholdBaseVal M
  set a₀ := prog.eval (ValueQuery.oracleOf v₀)
  have hsub : (Finset.powersetCard k (Finset.univ : Finset M)).erase (a₀.bundle 0) ⊆
      ValueQuery.queriedSets (ValueQuery.oracleOf v₀) prog := by
    intro T hT
    rcases Finset.mem_erase.mp hT with ⟨hTne, hTmem⟩
    have hTcard : T.card = k := (Finset.mem_powersetCard.mp hTmem).2
    by_contra hnot
    have hagree : ∀ S ∈ ValueQuery.queriedSets (ValueQuery.oracleOf v₀) prog,
        ValueQuery.oracleOf v₀ (.value S) =
          ValueQuery.oracleOf (hiddenBundleVal M T) (.value S) := by
      intro S hS
      have hne : S ≠ T := fun h => hnot (h ▸ hS)
      exact (hiddenBundleVal_eq_thresholdBaseVal_of_ne hTcard hne).symm
    have heq := ValueQuery.eval_eq_of_agree_on_queriedSets prog hagree
    have hge := hopt (hiddenBundleVal M T) (Or.inr ⟨T, hTcard, rfl⟩) (partitionAlloc T)
    rw [← heq] at hge
    change welfare ![hiddenBundleVal M T, complementThresholdVal M] (partitionAlloc T) ≤
      welfare ![hiddenBundleVal M T, complementThresholdVal M] a₀ at hge
    rw [welfare_hiddenBundleVal_partitionAlloc hTcard, welfare_two] at hge
    have hcard_sum := card_add_card_le_of_alloc a₀
    unfold hiddenBundleVal complementThresholdVal at hge
    split_ifs at hge with h1 h2
    · have hle0 : (a₀.bundle 0).card ≤ k := by omega
      have hTsub : T ⊆ a₀.bundle 0 := h1.resolve_right (by omega)
      exact hTne (Finset.eq_of_subset_of_card_le hTsub (by omega))
    · norm_num at hge
    · norm_num at hge
    · norm_num at hge
  calc (Fintype.card M).choose k - 1
      = (Finset.powersetCard k (Finset.univ : Finset M)).card - 1 := by
          rw [Finset.card_powersetCard, Finset.card_univ]
    _ ≤ ((Finset.powersetCard k (Finset.univ : Finset M)).erase (a₀.bundle 0)).card :=
          Finset.pred_card_le_card_erase
    _ ≤ (ValueQuery.queriedSets (ValueQuery.oracleOf v₀) prog).card := Finset.card_le_card hsub
    _ ≤ prog.countQueries (ValueQuery.oracleOf v₀) :=
          ValueQuery.card_queriedSets_le_countQueries _ _

end DemandSeparation

/-! ### Step of §11.5.2 (p. 285): DLPR demand-query separation oracle -/

section DLPRSeparation

/-- **Step of [BlumrosenNisan2007], §11.5.2 (p. 285)** (not Theorem 11.24, whose polynomial-time
Ellipsoid bound remains open under issue `#7789`): for arbitrary real valuations
`v : N → Finset M → ℝ`, valid demand oracles `oracles`, and nonnegative `(u, p)`, feasibility in
the dual LP relaxation DLPR (`IsDLPRFeasible`) holds if and only if each bidder `i`'s demand bundle
`D_i = oracles i (.demand p)` satisfies constraint (11.8): `v i D_i - ∑ j ∈ D_i, p j ≤ u i`. -/
theorem isDLPRFeasible_iff_of_isValidOracle {N M : Type}
    {v : N → Finset M → ℝ}
    {oracles : N → ({ι : Type} → DemandQuery M ι → ι)}
    (horacles : ∀ i, DemandQuery.IsValidOracle (v i) (oracles i))
    {u : N → ℝ} {p : M → ℝ} (hu : ∀ i, 0 ≤ u i) (hp : ∀ j, 0 ≤ p j) :
    IsDLPRFeasible v u p ↔
      ∀ i : N, v i (oracles i (.demand p)) - ∑ j ∈ oracles i (.demand p), p j ≤ u i := by
  constructor
  · intro hfeas i
    linarith [hfeas.cover i (oracles i (.demand p))]
  · intro hcheck
    refine ⟨fun i S => ?_, hu, hp⟩
    linarith [horacles i p S, hcheck i]

/-- **Step of [BlumrosenNisan2007], §11.5.2 (p. 285)** (not Theorem 11.24, which remains open under
issue `#7789`): pure demand-query separation subroutine for a single bidder's DLPR constraints
(11.8). Given precision `t`, candidate dual utility `u_i`, and item prices `p`, it queries the
bidder's demand bundle `D` at `p`, simulates `v_i(D)` via `valueQueryProg t D`, and returns `none`
when `v_i(D) - ∑ j ∈ D, p j ≤ u_i` or `some D` as an explicit violated constraint otherwise. -/
noncomputable def dlprBidderCheckProg {M : Type} [DecidableEq M]
    (t : ℕ) (u_i : ℝ) (p : M → ℝ) : FreeM (DemandQuery M) (Option (Finset M)) := do
  let D ← DemandQuery.ask p
  let val ← valueQueryProg t D
  pure (if (val : ℝ) - ∑ j ∈ D, p j ≤ u_i then none else some D)

/-- `dlprBidderCheckProg t u_i p` makes at most `1 + Fintype.card M * t` demand queries against any
oracle. -/
theorem countQueries_dlprBidderCheckProg_le {M : Type} [Fintype M] [DecidableEq M]
    (t : ℕ) (u_i : ℝ) (p : M → ℝ) (oracle : {ι : Type} → DemandQuery M ι → ι) :
    (dlprBidderCheckProg t u_i p).countQueries oracle ≤ 1 + Fintype.card M * t := by
  simp only [dlprBidderCheckProg, FreeM.countQueries_bind, DemandQuery.countQueries_ask,
    DemandQuery.eval_ask, FreeM.countQueries_pure, add_zero]
  have h1 := countQueries_valueQueryProg_le t (oracle (.demand p)) oracle
  omega

private theorem eval_dlprBidderCheckProg {M : Type} [DecidableEq M]
    (t : ℕ) (u_i : ℝ) (p : M → ℝ) (oracle : {ι : Type} → DemandQuery M ι → ι) :
    (dlprBidderCheckProg t u_i p).eval oracle =
      if (((valueQueryProg t (oracle (.demand p))).eval oracle : ℕ) : ℝ) -
          ∑ j ∈ oracle (.demand p), p j ≤ u_i then
        none
      else
        some (oracle (.demand p)) := by
  unfold dlprBidderCheckProg DemandQuery.ask
  rw [FreeM.eval_liftBind, FreeM.eval_bind, FreeM.eval_pure]

/-- **Step of [BlumrosenNisan2007], §11.5.2 (p. 285)** (not Theorem 11.24, which remains open under
issue `#7789`): for a normalized monotone `t`-bit integer-valued valuation `v_i` and valid demand
oracle `oracle`, `dlprBidderCheckProg t u_i p` returns `none` iff every bundle `S` satisfies DLPR
constraint (11.8) `v_i S ≤ u_i + ∑ j ∈ S, p j`. -/
theorem dlprBidderCheckProg_eq_none_iff {M : Type} [DecidableEq M]
    {v_i : Finset M → ℝ} {t : ℕ}
    (h0 : v_i ∅ = 0) (hmono : Monotone v_i)
    (hbit : ∃ f : Finset M → ℕ, (∀ R, v_i R = (f R : ℝ)) ∧ ∀ R, f R < 2 ^ t)
    {oracle : {ι : Type} → DemandQuery M ι → ι}
    (horacle : DemandQuery.IsValidOracle v_i oracle) (u_i : ℝ) (p : M → ℝ) :
    (dlprBidderCheckProg t u_i p).eval oracle = none ↔
      ∀ S : Finset M, v_i S ≤ u_i + ∑ j ∈ S, p j := by
  rw [eval_dlprBidderCheckProg]
  have hval := eval_valueQueryProg h0 hmono hbit horacle (oracle (.demand p))
  split_ifs with hle
  · rw [hval] at hle
    simp only [true_iff]
    intro S
    linarith [horacle p S]
  · rw [hval] at hle
    simp only [false_iff, not_forall, not_le]
    exact ⟨oracle (.demand p), by linarith⟩

/-- **Step of [BlumrosenNisan2007], §11.5.2 (p. 285)** (not Theorem 11.24, which remains open under
issue `#7789`): whenever `dlprBidderCheckProg t u_i p` returns `some D`, the bundle `D` strictly
violates DLPR constraint (11.8): `u_i + ∑ j ∈ D, p j < v_i D`. -/
theorem dlprBidderCheckProg_eq_some_violated {M : Type} [DecidableEq M]
    {v_i : Finset M → ℝ} {t : ℕ}
    (h0 : v_i ∅ = 0) (hmono : Monotone v_i)
    (hbit : ∃ f : Finset M → ℕ, (∀ R, v_i R = (f R : ℝ)) ∧ ∀ R, f R < 2 ^ t)
    {oracle : {ι : Type} → DemandQuery M ι → ι}
    (horacle : DemandQuery.IsValidOracle v_i oracle) {u_i : ℝ} {p : M → ℝ} {D : Finset M}
    (hsome : (dlprBidderCheckProg t u_i p).eval oracle = some D) :
    u_i + ∑ j ∈ D, p j < v_i D := by
  rw [eval_dlprBidderCheckProg] at hsome
  have hval := eval_valueQueryProg h0 hmono hbit horacle (oracle (.demand p))
  split_ifs at hsome with hle
  rw [hval] at hle
  simp only [Option.some.injEq] at hsome
  subst hsome
  linarith

/-- **Step of [BlumrosenNisan2007], §11.5.2 (p. 285)** (not Theorem 11.24, which remains open under
issue `#7789`): running `dlprBidderCheckProg` on every bidder `i : N` checks `IsDLPRFeasible v u p`
for nonnegative `(u, p)` using at most `Fintype.card N * (1 + Fintype.card M * t)` total demand
queries. -/
theorem isDLPRFeasible_iff_dlprBidderCheckProg {N M : Type} [Fintype N] [Fintype M] [DecidableEq M]
    {v : N → Finset M → ℝ} {t : ℕ}
    (h0 : ∀ i, v i ∅ = 0) (hmono : ∀ i, Monotone (v i))
    (hbit : ∀ i, ∃ f : Finset M → ℕ, (∀ R, v i R = (f R : ℝ)) ∧ ∀ R, f R < 2 ^ t)
    {oracles : N → ({ι : Type} → DemandQuery M ι → ι)}
    (horacles : ∀ i, DemandQuery.IsValidOracle (v i) (oracles i))
    {u : N → ℝ} {p : M → ℝ} (hu : ∀ i, 0 ≤ u i) (hp : ∀ j, 0 ≤ p j) :
    (IsDLPRFeasible v u p ↔
        ∀ i : N, (dlprBidderCheckProg t (u i) p).eval (oracles i) = none) ∧
      ∑ i : N, (dlprBidderCheckProg t (u i) p).countQueries (oracles i) ≤
        Fintype.card N * (1 + Fintype.card M * t) := by
  refine ⟨⟨fun hfeas i => (dlprBidderCheckProg_eq_none_iff (h0 i) (hmono i) (hbit i)
      (horacles i) (u i) p).mpr (hfeas.cover i),
    fun hall => ⟨fun i => (dlprBidderCheckProg_eq_none_iff (h0 i) (hmono i) (hbit i)
      (horacles i) (u i) p).mp (hall i), hu, hp⟩⟩, ?_⟩
  calc ∑ i : N, (dlprBidderCheckProg t (u i) p).countQueries (oracles i)
      ≤ ∑ _i : N, (1 + Fintype.card M * t) :=
          Finset.sum_le_sum fun i _ => countQueries_dlprBidderCheckProg_le t (u i) p (oracles i)
    _ = Fintype.card N * (1 + Fintype.card M * t) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end DLPRSeparation

end Cslib.GameTheory.CombinatorialAuction
