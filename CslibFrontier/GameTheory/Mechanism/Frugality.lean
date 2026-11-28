/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MinimumSpanningTree
public import CslibFrontier.GameTheory.Mechanism.VCG
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.Matroid.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Antichain
import CslibFrontier.Foundations.Data.Finset.ApplyUpdate
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Frugality in Set-System, Path, and Spanning-Tree Procurement Auctions

In a *procurement* ("hiring-a-team") auction ([HartlineKarlin2007], §13.5, pp. 350–354), a finite
set of agents `E` each has a private nonnegative cost `c e ≥ 0` (equivalently valuation `-c e`),
and the auctioneer must purchase a feasible subset `S ∈ F` from a nonempty, monopoly-free family
`F : Finset (Finset E)` while minimizing total payments.

This module formalizes the competitive frugality framework and main bounds of
[HartlineKarlin2007], §13.5 (pp. 350–354) and Exercise 13.12 (p. 361):

* **Procurement mechanisms and VCG (§13.5, pp. 350–352):** `ProcurementMechanism E F`,
  incentive predicates `IsDSIC`, `IsIR`, `LosersPaidZero`, antitonicity and winner-payment
  bid-independence (`ProcurementMechanism.IsDSIC.antitone_alloc`, `pay_eq_of_mem_alloc`), and the
  Clarke-pivot VCG procurement mechanism `vcgMechanism` (bridged to
  `Cslib.GameTheory.Mechanism.groves` on negative cost valuations with the outside-option pivot
  `max_{T ∈ F, e ∉ T} (-c(T))`).
* **Pay-your-bid Nash benchmark `N(c)` and frugality ratio (§13.5.1, Definition 13.52 and
  Footnote 3, p. 352):** `IsPayYourBidNash` characterizes pure Nash equilibria of the pay-your-bid
  mechanism `N` in which non-winners bid truthfully and ties are broken in favor of efficiency
  (`isPayYourBidNash_iff_pureNash`), proved nonempty for every monopoly-free family
  (`exists_isPayYourBidNash`), with `cheapestNash` as the infimum benchmark `N(c)` and
  `HasFrugalityRatioLe` as the multiplicative form of Definition 13.52 (avoiding `0 / 0`).
* **Theorem 13.53 (§13.5.1.1, p. 353):** on any nonempty, monopoly-free antichain `(E, F)`, VCG
  has frugality ratio `1` (`HasFrugalityRatioLe F (vcgMechanism F hF hmono) 1`) **if and only if**
  `F` is the family of bases of a matroid (`IsMatroidBaseFamily`, bridged to Mathlib's `Matroid`
  in `isMatroidBaseFamily_iff_exists_matroid`). The forward direction uses Brualdi's basis-exchange
  bijection (via Hall's marriage theorem) to show that every restricted pay-your-bid Nash
  equilibrium pays exactly `(vcgMechanism F hF hmono).totalPay c`; the converse constructs explicit
  nonnegative cost profiles when equicardinality or basis exchange fails. Note that the antichain
  assumption (minimal feasible sets, as in the source literature) is necessary for the converse:
  adding a strict superset `{0, 2}` to `{{0}, {1}}` leaves VCG at frugality ratio `1` on
  nonnegative costs without being a matroid base family.
* **Exercise 13.12 (p. 361; Example 13.51, p. 351):** for any finite connected bridgeless simple
  graph `G`, the spanning-tree family `spanningTreeFamily G` is a monopoly-free matroid base
  family, so VCG has frugality ratio `1` for spanning-tree auctions
  (`vcg_spanningTree_hasFrugalityRatioLe_one`).
* **Theorem 13.54 and weighted path auction (§13.5, p. 351; §13.5.1.1, pp. 353–354):** on two
  vertex-disjoint paths `twoDisjointPaths n n'` of lengths `n, n' ≥ 1`, VCG pays `n * n'` on the
  `0`/`1` profile (`vcgTotalPay_twoDisjointPaths_zero_one`), every deterministic DSIC, IR,
  losers-paid-zero procurement mechanism has frugality ratio at least `(1 / 2) * √(n * n')`
  (`twoDisjointPaths_frugality_lower_bound`, `le_of_hasFrugalityRatioLe_twoDisjointPaths`), and
  the `√|P| · c(P)` weighted threshold mechanism `sqrtWeightedPathMechanism` is DSIC, IR, pays
  losers zero, and achieves frugality ratio at most `√(n * n')`
  (`sqrtWeightedPathMechanism_hasFrugalityRatioLe`).

No running-time claim is made in this module.

## Main definitions

* `IsMonopolyFree`: no agent belongs to every feasible set.
* `ProcurementMechanism`: feasible-set allocation rule and payment rule for `(E, F)`.
* `ProcurementMechanism.utility`, `totalPay`, `IsDSIC`, `IsIR`, `LosersPaidZero`.
* `IsMinCostSet`, `vcgAlloc`, `vcgPayOfSet`, `vcgMechanism`: VCG procurement mechanism.
* `IsPayYourBidNash`, `cheapestNash`, `HasFrugalityRatioLe`: pay-your-bid Nash benchmark `N(c)`
  and multiplicative frugality ratio ([HartlineKarlin2007], Definition 13.52, p. 352).
* `IsMatroidBaseFamily`: finite matroid base family via basis exchange.
* `spanningTreeFamily`: edge-set family of spanning trees of a finite simple graph
  ([HartlineKarlin2007], Example 13.51, p. 351).
* `twoDisjointPaths`, `sqrtWeightedPathMechanism`: two vertex-disjoint paths and the
  `√|P| · c(P)` weighted procurement auction ([HartlineKarlin2007], §13.5, p. 351; §13.5.1.1,
  pp. 353–354).

## Main results

* `ProcurementMechanism.IsDSIC.antitone_alloc`, `ProcurementMechanism.IsDSIC.pay_eq_of_mem_alloc`,
  `ProcurementMechanism.IsDSIC.le_pay_of_mem_alloc_update`: monotonicity and payment-threshold
  properties of DSIC procurement mechanisms.
* `vcgMechanism_isDSIC`, `vcgMechanism_isIR`, `vcgMechanism_losersPaidZero`: VCG properties and
  bridge to `Cslib.GameTheory.Mechanism.groves`.
* `isPayYourBidNash_iff_pureNash`, `exists_isPayYourBidNash`, `cheapestNash_le_vcgTotalPay`:
  game-theoretic equivalence, existence, and upper bound for the Nash benchmark `N(c)`.
* `cheapestNash_of_pairwiseDisjoint`, `cheapestNash_twoDisjointPaths`: `N(c)` equals the
  second-cheapest path cost on pairwise-disjoint paths ([HartlineKarlin2007], p. 352).
* `isMatroidBaseFamily_iff_exists_matroid`, `IsMatroidBaseFamily.exists_exchange_bijection`:
  equivalence with Mathlib `Matroid` and Brualdi's strong exchange bijection.
* `vcgTotalPay_eq_cheapestNash_of_isMatroidBaseFamily`,
  `vcg_hasFrugalityRatioLe_one_iff_isMatroidBaseFamily`: **Theorem 13.53**
  ([HartlineKarlin2007], §13.5.1.1, p. 353).
* `spanningTreeFamily_isMatroidBaseFamily`, `vcg_spanningTree_hasFrugalityRatioLe_one`:
  **Exercise 13.12** ([HartlineKarlin2007], p. 361).
* `twoDisjointPaths_frugality_lower_bound`, `le_of_hasFrugalityRatioLe_twoDisjointPaths`:
  **Theorem 13.54** ([HartlineKarlin2007], §13.5.1.1, p. 353).
* `sqrtWeightedPathMechanism_isDSIC`, `sqrtWeightedPathMechanism_isIR`,
  `sqrtWeightedPathMechanism_hasFrugalityRatioLe`: near-optimal `√(|P||P'|)`-frugal mechanism
  ([HartlineKarlin2007], §13.5.1.1, p. 354).

## References

* [J. D. Hartline and A. R. Karlin, *Profit Maximization in Mechanism Design*, Chapter 13 of
  *Algorithmic Game Theory*][HartlineKarlin2007], §13.5 (pp. 350–354) and Exercise 13.12 (p. 361).
-/

open Finset
open scoped BigOperators

public section

namespace Cslib.GameTheory.Mechanism.Frugality

/-- Updating agent `e`'s bid from `b e` to `z` shifts the sum over `A` by `z - b e` when
`e ∈ A` and leaves it unchanged otherwise. -/
private theorem sum_update_eq_add_ite {E : Type*} [DecidableEq E] (A : Finset E) (b : E → ℝ)
    (e : E) (z : ℝ) :
    ∑ x ∈ A, Function.update b e z x = (∑ x ∈ A, b x) + if e ∈ A then z - b e else 0 := by
  by_cases heA : e ∈ A
  · simp only [heA, ↓reduceIte]
    rw [Finset.sum_apply_update_of_mem heA (fun _ v => v) b z, Finset.sum_erase_eq_sub heA]
    ring
  · simp only [heA, ↓reduceIte, add_zero]
    exact Finset.sum_congr rfl fun x hx =>
      Function.update_of_ne (fun (h : x = e) => heA (h ▸ hx)) _ _

/-! ### Set-system procurement environments and mechanisms -/

section Procurement

variable {E : Type*} {F : Finset (Finset E)}

/-- A feasible family `F` is *monopoly-free* if no agent belongs to every feasible set: for every
agent `e`, some feasible set avoids `e`. Without this condition, a monopoly agent can demand
arbitrarily large payments in VCG and no pure Nash equilibrium exists in pay-your-bid auctions. -/
@[expose] def IsMonopolyFree (F : Finset (Finset E)) : Prop :=
  ∀ e : E, ∃ S ∈ F, e ∉ S

/-- A deterministic sealed-bid *procurement mechanism* for the set system `(E, F)`
([HartlineKarlin2007], §13.5, p. 351): on a reported cost profile `b : E → ℝ`, it selects a
feasible set `alloc b ∈ F` and pays each agent `e` the amount `pay b e`. -/
structure ProcurementMechanism (E : Type*) (F : Finset (Finset E)) where
  /-- The feasible-set allocation rule. -/
  alloc : (E → ℝ) → Finset E
  /-- Feasibility: the chosen set belongs to `F` on every bid profile. -/
  alloc_mem : ∀ b, alloc b ∈ F
  /-- The payment rule: `pay b e` is the transfer from the auctioneer to agent `e`. -/
  pay : (E → ℝ) → E → ℝ

namespace ProcurementMechanism

/-- Quasilinear utility of agent `e` with true cost `cₑ` on bid profile `b`:
`pay b e - cₑ` if `e ∈ alloc b`, and `pay b e` otherwise (corresponding to valuation `-cₑ` and
transfer `-pay b e` in [HartlineKarlin2007], p. 351). -/
@[expose] def utility [DecidableEq E] (M : ProcurementMechanism E F) (e : E) (cₑ : ℝ)
    (b : E → ℝ) : ℝ :=
  M.pay b e - if e ∈ M.alloc b then cₑ else 0

/-- Total payment made by the auctioneer on bid profile `b`. -/
@[expose] def totalPay [Fintype E] (M : ProcurementMechanism E F) (b : E → ℝ) : ℝ :=
  ∑ e : E, M.pay b e

/-- Dominant-strategy incentive compatibility on nonnegative cost profiles: for every agent `e`,
nonnegative bid profile `b`, and true cost `cₑ ≥ 0`, reporting `cₑ` maximizes `e`'s utility. -/
@[expose] def IsDSIC [DecidableEq E] (M : ProcurementMechanism E F) : Prop :=
  ∀ (e : E) (b : E → ℝ) (cₑ : ℝ), 0 ≤ b → 0 ≤ cₑ →
    M.utility e cₑ b ≤ M.utility e cₑ (Function.update b e cₑ)

/-- Individual rationality on nonnegative cost profiles: a truthful agent gets nonnegative
utility. -/
@[expose] def IsIR [DecidableEq E] (M : ProcurementMechanism E F) : Prop :=
  ∀ (e : E) (b : E → ℝ), 0 ≤ b → 0 ≤ M.utility e (b e) b

/-- Normalization for procurement auctions: losing agents (`e ∉ alloc b`) receive zero payment on
every nonnegative bid profile. -/
@[expose] def LosersPaidZero (M : ProcurementMechanism E F) : Prop :=
  ∀ (b : E → ℝ), 0 ≤ b → ∀ e, e ∉ M.alloc b → M.pay b e = 0

/-- When losers are paid zero, `totalPay` equals the sum of payments over winning agents. -/
theorem totalPay_eq_sum_alloc [Fintype E] {M : ProcurementMechanism E F} (hZ : M.LosersPaidZero)
    {b : E → ℝ} (hb : 0 ≤ b) :
    M.totalPay b = ∑ e ∈ M.alloc b, M.pay b e := by
  unfold totalPay
  symm
  exact Finset.sum_subset (Finset.subset_univ _) fun e _ he => hZ b hb e he

/-- Under `IsIR` and `LosersPaidZero`, every agent receives a nonnegative payment on nonnegative
cost profiles. -/
theorem pay_nonneg [DecidableEq E] {M : ProcurementMechanism E F} (hIR : M.IsIR)
    (hZ : M.LosersPaidZero) {b : E → ℝ} (hb : 0 ≤ b) (e : E) :
    0 ≤ M.pay b e := by
  by_cases he : e ∈ M.alloc b
  · have h := hIR e b hb
    simp only [utility, he, ↓reduceIte] at h
    have hbe : 0 ≤ b e := hb e
    linarith
  · rw [hZ b hb e he]

/-- Under `IsDSIC`, the allocation rule is *monotone* (antitone in own cost): lowering agent `e`'s
nonnegative bid preserves winning ([HartlineKarlin2007], §13.5.1.1, p. 353). -/
theorem IsDSIC.antitone_alloc [DecidableEq E] {M : ProcurementMechanism E F} (hM : M.IsDSIC)
    {b : E → ℝ} (hb : 0 ≤ b) {e : E} {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy_win : e ∈ M.alloc (Function.update b e y)) :
    e ∈ M.alloc (Function.update b e x) := by
  rcases hxy.lt_or_eq with hlt | rfl
  · by_contra hx_lose
    have h1 := hM e (Function.update b e y) x
      (le_update_iff.2 ⟨hx.trans hlt.le, fun j _ => hb j⟩) hx
    have h2 := hM e (Function.update b e x) y
      (le_update_iff.2 ⟨hx, fun j _ => hb j⟩) (hx.trans hlt.le)
    simp only [utility, Function.update_idem, hy_win, hx_lose, ↓reduceIte] at h1 h2
    linarith
  · exact hy_win

/-- Under `IsDSIC`, a winning agent's payment does not depend on its own bid as long as it
continues to win. -/
theorem IsDSIC.pay_eq_of_mem_alloc [DecidableEq E] {M : ProcurementMechanism E F} (hM : M.IsDSIC)
    {b : E → ℝ} (hb : 0 ≤ b) {e : E} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hx_win : e ∈ M.alloc (Function.update b e x))
    (hy_win : e ∈ M.alloc (Function.update b e y)) :
    M.pay (Function.update b e x) e = M.pay (Function.update b e y) e := by
  have h1 := hM e (Function.update b e y) x (le_update_iff.2 ⟨hy, fun j _ => hb j⟩) hx
  have h2 := hM e (Function.update b e x) y (le_update_iff.2 ⟨hx, fun j _ => hb j⟩) hy
  simp only [utility, Function.update_idem, hx_win, hy_win, ↓reduceIte] at h1 h2
  linarith

/-- Under `IsDSIC` and `IsIR`, if agent `e` wins at both nonnegative bids `x` and `y`, then its
payment at `x` is at least `y`. -/
theorem IsDSIC.le_pay_of_mem_alloc_update [DecidableEq E] {M : ProcurementMechanism E F}
    (hM : M.IsDSIC) (hIR : M.IsIR) {b : E → ℝ} (hb : 0 ≤ b) {e : E} {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hx_win : e ∈ M.alloc (Function.update b e x))
    (hy_win : e ∈ M.alloc (Function.update b e y)) :
    y ≤ M.pay (Function.update b e x) e := by
  rw [hM.pay_eq_of_mem_alloc hb hx hy hx_win hy_win]
  have h := hIR e (Function.update b e y) (le_update_iff.2 ⟨hy, fun j _ => hb j⟩)
  simp only [utility, Function.update_self, hy_win, ↓reduceIte] at h
  linarith

end ProcurementMechanism

end Procurement

/-! ### The VCG procurement mechanism -/

section VCG

variable {E : Type*}

/-- `S` is a *minimum-cost feasible set* in `F` for cost profile `c` if `S ∈ F` and no feasible
set has strictly smaller total cost. -/
@[expose] def IsMinCostSet (F : Finset (Finset E)) (c : E → ℝ) (S : Finset E) : Prop :=
  S ∈ F ∧ ∀ T ∈ F, ∑ e ∈ S, c e ≤ ∑ e ∈ T, c e

/-- Every nonempty feasible family admits a minimum-cost feasible set. -/
theorem exists_isMinCostSet {F : Finset (Finset E)} (hF : F.Nonempty) (c : E → ℝ) :
    ∃ S, IsMinCostSet F c S :=
  Finset.exists_min_image F (fun S => ∑ e ∈ S, c e) hF

/-- Canonical VCG procurement allocation rule: picks a minimum-cost feasible set in `F`. -/
noncomputable def vcgAlloc (F : Finset (Finset E)) (hF : F.Nonempty) (c : E → ℝ) : Finset E :=
  (exists_isMinCostSet hF c).choose

theorem vcgAlloc_isMinCostSet (F : Finset (Finset E)) (hF : F.Nonempty) (c : E → ℝ) :
    IsMinCostSet F c (vcgAlloc F hF c) :=
  (exists_isMinCostSet hF c).choose_spec

/-- The nonempty subcollection of feasible sets avoiding agent `e`, guaranteed by
`IsMonopolyFree F`. -/
theorem IsMonopolyFree.filter_notMem_nonempty [DecidableEq E] {F : Finset (Finset E)}
    (hmono : IsMonopolyFree F) (e : E) : (F.filter fun T => e ∉ T).Nonempty := by
  obtain ⟨T, hTF, heT⟩ := hmono e
  exact ⟨T, Finset.mem_filter.2 ⟨hTF, heT⟩⟩

/-- The Clarke-pivot VCG payment to agent `e` when feasible set `S` is selected on cost profile
`c`: `min_{T ∈ F, e ∉ T} c(T) - c(S \ {e})`. When `S` is a minimum-cost set, this equals
`min_{T ∈ F, e ∉ T} c(T) - (c(S) - c(e))` for `e ∈ S` and `0` for `e ∉ S`
([HartlineKarlin2007], §13.5, p. 351). -/
@[expose] noncomputable def vcgPayOfSet [DecidableEq E] (F : Finset (Finset E))
    (hmono : IsMonopolyFree F) (c : E → ℝ) (S : Finset E) (e : E) : ℝ :=
  (F.filter fun T => e ∉ T).inf' (hmono.filter_notMem_nonempty e) (fun T => ∑ x ∈ T, c x) -
    ∑ x ∈ S.erase e, c x

/-- For a winning agent `e ∈ S`, `vcgPayOfSet` equals `min_{T ∈ F, e ∉ T} c(T) - (c(S) - c(e))`. -/
theorem vcgPayOfSet_of_mem [DecidableEq E] {F : Finset (Finset E)} (hmono : IsMonopolyFree F)
    (c : E → ℝ) {S : Finset E} {e : E} (he : e ∈ S) :
    vcgPayOfSet F hmono c S e =
      (F.filter fun T => e ∉ T).inf' (hmono.filter_notMem_nonempty e) (fun T => ∑ x ∈ T, c x) -
        ((∑ x ∈ S, c x) - c e) := by
  unfold vcgPayOfSet
  rw [Finset.sum_erase_eq_sub he]

/-- For a losing agent `e ∉ S` of a minimum-cost feasible set `S`, `vcgPayOfSet` is `0`. -/
theorem vcgPayOfSet_of_notMem [DecidableEq E] {F : Finset (Finset E)} (hmono : IsMonopolyFree F)
    {c : E → ℝ} {S : Finset E} (hS : IsMinCostSet F c S) {e : E} (he : e ∉ S) :
    vcgPayOfSet F hmono c S e = 0 := by
  unfold vcgPayOfSet
  rw [Finset.erase_eq_of_notMem he, sub_eq_zero]
  refine le_antisymm ?_ ?_
  · exact Finset.inf'_le (fun T => ∑ x ∈ T, c x) (Finset.mem_filter.2 ⟨hS.1, he⟩)
  · exact Finset.le_inf' _ _ fun T hT => hS.2 T (Finset.mem_filter.1 hT).1

/-- For a winning agent `e ∈ S` of a minimum-cost feasible set `S`, its VCG payment covers its
cost. -/
theorem cost_le_vcgPayOfSet [DecidableEq E] {F : Finset (Finset E)} (hmono : IsMonopolyFree F)
    {c : E → ℝ} {S : Finset E} (hS : IsMinCostSet F c S) {e : E} (he : e ∈ S) :
    c e ≤ vcgPayOfSet F hmono c S e := by
  rw [vcgPayOfSet_of_mem hmono c he]
  have hle : ∑ x ∈ S, c x ≤
      (F.filter fun T => e ∉ T).inf' (hmono.filter_notMem_nonempty e) (fun T => ∑ x ∈ T, c x) :=
    Finset.le_inf' _ _ fun T hT => hS.2 T (Finset.mem_filter.1 hT).1
  linarith

/-- Upper bound on `vcgPayOfSet`: every feasible set `T` avoiding `e` bounds `vcgPayOfSet` from
above by `c(T) - c(S \ {e})`. -/
theorem vcgPayOfSet_le [DecidableEq E] {F : Finset (Finset E)} (hmono : IsMonopolyFree F)
    (c : E → ℝ) (S : Finset E) {e : E} {T : Finset E} (hTF : T ∈ F) (heT : e ∉ T) :
    vcgPayOfSet F hmono c S e ≤ (∑ x ∈ T, c x) - ∑ x ∈ S.erase e, c x := by
  unfold vcgPayOfSet
  gcongr
  exact Finset.inf'_le (fun R => ∑ x ∈ R, c x) (Finset.mem_filter.2 ⟨hTF, heT⟩)

/-- Lower bound on `vcgPayOfSet`: if every `T ∈ F` avoiding `e` satisfies `r ≤ c(T) - c(S \ {e})`,
then `r ≤ vcgPayOfSet F hmono c S e`. -/
theorem le_vcgPayOfSet [DecidableEq E] {F : Finset (Finset E)} (hmono : IsMonopolyFree F)
    (c : E → ℝ) (S : Finset E) {e : E} {r : ℝ}
    (h : ∀ T ∈ F, e ∉ T → r ≤ (∑ x ∈ T, c x) - ∑ x ∈ S.erase e, c x) :
    r ≤ vcgPayOfSet F hmono c S e := by
  unfold vcgPayOfSet
  have h' : r + ∑ x ∈ S.erase e, c x ≤
      (F.filter fun T => e ∉ T).inf' (hmono.filter_notMem_nonempty e) (fun T => ∑ x ∈ T, c x) :=
    Finset.le_inf' _ _ fun T hT => by
      obtain ⟨hTF, heT⟩ := Finset.mem_filter.1 hT
      linarith [h T hTF heT]
  linarith

/-- The VCG procurement mechanism on a nonempty, monopoly-free feasible family `(E, F)`
([HartlineKarlin2007], §13.5, p. 351). -/
@[expose] noncomputable def vcgMechanism [DecidableEq E] (F : Finset (Finset E))
    (hF : F.Nonempty) (hmono : IsMonopolyFree F) : ProcurementMechanism E F where
  alloc := vcgAlloc F hF
  alloc_mem c := (vcgAlloc_isMinCostSet F hF c).1
  pay c e := vcgPayOfSet F hmono c (vcgAlloc F hF c) e

/-- Negative-cost valuation induced by cost profile `c` on feasible outcomes `{S // S ∈ F}`:
agent `e` values outcome `S` at `-c e` if `e ∈ S` and `0` otherwise ([HartlineKarlin2007],
p. 351). -/
@[expose] def negCostValuation [DecidableEq E] (F : Finset (Finset E)) (c : E → ℝ) (e : E)
    (S : {S // S ∈ F}) : ℝ :=
  if e ∈ S.1 then -c e else 0

/-- The outside-option Groves pivot for procurement: `max_{T ∈ F, e ∉ T} ∑_{j ≠ e} v_j(T)`,
which restricts the economy to feasible sets not requiring agent `e`. -/
@[expose] noncomputable def procurementGrovesPivot [Fintype E] [DecidableEq E]
    (F : Finset (Finset E)) (hmono : IsMonopolyFree F) (e : E)
    (v : E → {S // S ∈ F} → ℝ) : ℝ :=
  (F.filter fun T => e ∉ T).attach.sup'
    ((hmono.filter_notMem_nonempty e).attach)
    fun T => ∑ j ∈ Finset.univ.erase e, v j ⟨T.1, (Finset.mem_filter.1 T.2).1⟩

/-- Bridge to `Cslib.GameTheory.Mechanism.groves` (`VCG.lean`): on negative-cost valuations,
`vcgMechanism` pays each agent the negation of the Groves payment with the outside-option pivot
`procurementGrovesPivot`. -/
theorem vcgMechanism_pay_eq_neg_groves [Fintype E] [DecidableEq E] (F : Finset (Finset E))
    (hF : F.Nonempty) (hmono : IsMonopolyFree F)
    (f : (E → {S // S ∈ F} → ℝ) → {S // S ∈ F})
    (c : E → ℝ) (hf : (f (negCostValuation F c)).1 = vcgAlloc F hF c) (e : E) :
    (vcgMechanism F hF hmono).pay c e =
      -(Cslib.GameTheory.Mechanism.groves f (procurementGrovesPivot F hmono)).payment
        (negCostValuation F c) e := by
  have hsum : ∀ (T : Finset E) (hTF : T ∈ F),
      ∑ j ∈ Finset.univ.erase e, negCostValuation F c j ⟨T, hTF⟩ = -(∑ x ∈ T.erase e, c x) := by
    intro T hTF
    rw [← Finset.sum_neg_distrib]
    have hsub : T.erase e ⊆ Finset.univ.erase e := fun x hx =>
      Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hx).1, Finset.mem_univ x⟩
    rw [← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun x hx => by
        simp only [negCostValuation, Finset.mem_of_mem_erase hx, ↓reduceIte]
    · intro x hx hxe
      have hxT : x ∉ T := fun h => hxe (Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hx).1, h⟩)
      simp only [negCostValuation, hxT, ↓reduceIte]
  simp only [Cslib.GameTheory.Mechanism.groves, vcgMechanism, vcgPayOfSet,
    procurementGrovesPivot, neg_sub]
  have h1 : ∑ j ∈ Finset.univ.erase e, negCostValuation F c j (f (negCostValuation F c)) =
      -(∑ x ∈ (vcgAlloc F hF c).erase e, c x) := by
    have hf_eq : f (negCostValuation F c) =
        ⟨vcgAlloc F hF c, (vcgAlloc_isMinCostSet F hF c).1⟩ := Subtype.ext hf
    rw [hf_eq]
    exact hsum (vcgAlloc F hF c) (vcgAlloc_isMinCostSet F hF c).1
  rw [h1]
  have hsup :
      (F.filter fun T => e ∉ T).attach.sup' ((hmono.filter_notMem_nonempty e).attach)
        (fun T => ∑ j ∈ Finset.univ.erase e, negCostValuation F c j
          ⟨T.1, (Finset.mem_filter.1 T.2).1⟩) =
      -((F.filter fun T => e ∉ T).inf' (hmono.filter_notMem_nonempty e)
        (fun T => ∑ x ∈ T, c x)) := by
    refine le_antisymm ?_ ?_
    · refine Finset.sup'_le _ _ fun T _ => ?_
      rw [hsum T.1 (Finset.mem_filter.1 T.2).1,
        Finset.erase_eq_of_notMem (Finset.mem_filter.1 T.2).2, neg_le_neg_iff]
      exact Finset.inf'_le (fun R => ∑ x ∈ R, c x) T.2
    · rw [neg_le]
      refine Finset.le_inf' _ _ fun T hT => ?_
      rw [neg_le]
      have hle := Finset.le_sup'
        (f := fun T : {T // T ∈ F.filter fun T => e ∉ T} =>
          ∑ j ∈ Finset.univ.erase e, negCostValuation F c j ⟨T.1, (Finset.mem_filter.1 T.2).1⟩)
        (Finset.mem_attach _ ⟨T, hT⟩)
      rwa [hsum T (Finset.mem_filter.1 hT).1,
        Finset.erase_eq_of_notMem (Finset.mem_filter.1 hT).2] at hle
  rw [hsup]
  ring

/-- The VCG procurement mechanism is DSIC (even without restricting to nonnegative costs). -/
theorem vcgMechanism_isDSIC [DecidableEq E] (F : Finset (Finset E)) (hF : F.Nonempty)
    (hmono : IsMonopolyFree F) : (vcgMechanism F hF hmono).IsDSIC := by
  intro e b cₑ _ _
  simp only [ProcurementMechanism.utility, vcgMechanism, vcgPayOfSet]
  let S := vcgAlloc F hF b
  let S' := vcgAlloc F hF (Function.update b e cₑ)
  have hS' : IsMinCostSet F (Function.update b e cₑ) S' := vcgAlloc_isMinCostSet F hF _
  have hpivot :
      (F.filter fun T => e ∉ T).inf' (hmono.filter_notMem_nonempty e)
        (fun T => ∑ x ∈ T, Function.update b e cₑ x) =
      (F.filter fun T => e ∉ T).inf' (hmono.filter_notMem_nonempty e) (fun T => ∑ x ∈ T, b x) :=
    Finset.inf'_congr _ rfl fun T hT => Finset.sum_congr rfl fun x hx =>
      Function.update_of_ne (fun (hxe : x = e) => (Finset.mem_filter.1 hT).2 (hxe ▸ hx)) _ _
  have hmin : ∑ x ∈ S', Function.update b e cₑ x ≤ ∑ x ∈ S, Function.update b e cₑ x :=
    hS'.2 S (vcgAlloc_isMinCostSet F hF b).1
  have hsumS' : ∑ x ∈ S'.erase e, Function.update b e cₑ x = ∑ x ∈ S'.erase e, b x :=
    Finset.sum_congr rfl fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _
  rw [hpivot, hsumS']
  rw [sum_update_eq_add_ite S' b e cₑ, sum_update_eq_add_ite S b e cₑ] at hmin
  dsimp only [S, S'] at hmin ⊢
  by_cases h1 : e ∈ vcgAlloc F hF (Function.update b e cₑ) <;>
    by_cases h2 : e ∈ vcgAlloc F hF b <;>
    simp only [h1, h2, ↓reduceIte] at hmin ⊢
  · rw [Finset.sum_erase_eq_sub h1, Finset.sum_erase_eq_sub h2]; linarith
  · rw [Finset.sum_erase_eq_sub h1, Finset.erase_eq_of_notMem h2]; linarith
  · rw [Finset.erase_eq_of_notMem h1, Finset.sum_erase_eq_sub h2]; linarith
  · rw [Finset.erase_eq_of_notMem h1, Finset.erase_eq_of_notMem h2]; linarith

/-- The VCG procurement mechanism is individually rational. -/
theorem vcgMechanism_isIR [DecidableEq E] (F : Finset (Finset E)) (hF : F.Nonempty)
    (hmono : IsMonopolyFree F) : (vcgMechanism F hF hmono).IsIR := by
  intro e b _
  simp only [ProcurementMechanism.utility, vcgMechanism]
  by_cases he : e ∈ vcgAlloc F hF b
  · simp only [he, ↓reduceIte, sub_nonneg]
    exact cost_le_vcgPayOfSet hmono (vcgAlloc_isMinCostSet F hF b) he
  · simp only [he, ↓reduceIte, sub_zero,
      vcgPayOfSet_of_notMem hmono (vcgAlloc_isMinCostSet F hF b) he, le_rfl]

/-- The VCG procurement mechanism pays losers zero. -/
theorem vcgMechanism_losersPaidZero [DecidableEq E] (F : Finset (Finset E)) (hF : F.Nonempty)
    (hmono : IsMonopolyFree F) : (vcgMechanism F hF hmono).LosersPaidZero :=
  fun b _ _ he => vcgPayOfSet_of_notMem hmono (vcgAlloc_isMinCostSet F hF b) he

end VCG

/-! ### Pay-your-bid Nash benchmark `N(c)` and frugality ratio -/

section NashBenchmark

variable {E : Type*}

/-- A restricted pure Nash equilibrium `(b, S)` of the pay-your-bid mechanism `N` for cost profile
`c` ([HartlineKarlin2007], §13.5.1 and Footnote 3, p. 352): `S ∈ F` is a cheapest feasible set
under `b`, winners bid at least their true costs, non-winners bid truthfully, and every winner is
tightly constrained by some tied feasible set excluding it.

`isPayYourBidNash_iff_pureNash` establishes the exact equivalence with unilateral-deviation pure
Nash equilibria of the pay-your-bid mechanism `N` (with non-winners bidding truthfully) on every
monopoly-free family, and `IsPayYourBidNash.isMinCostSet` proves that `S` is automatically
efficient (minimum true cost). -/
structure IsPayYourBidNash (F : Finset (Finset E)) (c b : E → ℝ) (S : Finset E) : Prop where
  /-- The winning set `S` is feasible. -/
  mem : S ∈ F
  /-- `S` minimizes total bid among all feasible sets. -/
  min_bid : ∀ T ∈ F, ∑ e ∈ S, b e ≤ ∑ e ∈ T, b e
  /-- Every winner covers its true cost. -/
  winner_ge : ∀ e ∈ S, c e ≤ b e
  /-- Non-winners bid their true cost (Footnote 3, p. 352). -/
  loser_truthful : ∀ e, e ∉ S → b e = c e
  /-- No winner can raise its bid without creating a strictly cheaper feasible set avoiding it. -/
  winner_tight : ∀ e ∈ S, ∃ T ∈ F, e ∉ T ∧ ∑ x ∈ S, b x = ∑ x ∈ T, b x

/-- Utility of agent `e` with true cost `cₑ` in the pay-your-bid auction when feasible set `S`
wins under bid profile `b`. -/
@[expose] def payYourBidUtility [DecidableEq E] (e : E) (cₑ : ℝ) (b : E → ℝ) (S : Finset E) : ℝ :=
  if e ∈ S then b e - cₑ else 0

/-- Every restricted pay-your-bid Nash equilibrium automatically selects a minimum true-cost
(efficient) feasible set `S`. -/
theorem IsPayYourBidNash.isMinCostSet {F : Finset (Finset E)} {c b : E → ℝ}
    {S : Finset E} (h : IsPayYourBidNash F c b S) : IsMinCostSet F c S := by
  classical
  refine ⟨h.mem, fun T hTF => ?_⟩
  have hbid := h.min_bid T hTF
  have hSsplit : ∑ x ∈ S, b x = (∑ x ∈ S ∩ T, b x) + ∑ x ∈ S \ T, b x :=
    (sum_inter_add_sum_sdiff S T b).symm
  have hTsplit : ∑ x ∈ T, b x = (∑ x ∈ S ∩ T, b x) + ∑ x ∈ T \ S, b x := by
    rw [Finset.inter_comm, sum_inter_add_sum_sdiff T S b]
  have hdiff_b : ∑ x ∈ S \ T, b x ≤ ∑ x ∈ T \ S, b x := by linarith
  have hle_ST : ∑ x ∈ S \ T, c x ≤ ∑ x ∈ S \ T, b x :=
    Finset.sum_le_sum fun x hx => h.winner_ge x (Finset.mem_sdiff.1 hx).1
  have heq_TS : ∑ x ∈ T \ S, b x = ∑ x ∈ T \ S, c x :=
    Finset.sum_congr rfl fun x hx => h.loser_truthful x (Finset.mem_sdiff.1 hx).2
  have hSc : ∑ x ∈ S, c x = (∑ x ∈ S ∩ T, c x) + ∑ x ∈ S \ T, c x :=
    (sum_inter_add_sum_sdiff S T c).symm
  have hTc : ∑ x ∈ T, c x = (∑ x ∈ S ∩ T, c x) + ∑ x ∈ T \ S, c x := by
    rw [Finset.inter_comm, sum_inter_add_sum_sdiff T S c]
  linarith

/-- In any restricted pay-your-bid Nash equilibrium `(b, S)`, every winner's bid is bounded above
by its VCG payment `vcgPayOfSet F hmono c S e`. -/
theorem IsPayYourBidNash.bid_le_vcgPayOfSet [DecidableEq E] {F : Finset (Finset E)}
    (hmono : IsMonopolyFree F) {c b : E → ℝ} {S : Finset E}
    (h : IsPayYourBidNash F c b S) {e : E} (he : e ∈ S) :
    b e ≤ vcgPayOfSet F hmono c S e := by
  refine le_vcgPayOfSet hmono c S fun T hTF heT => ?_
  have hbid := h.min_bid T hTF
  have hSsplit : ∑ x ∈ S, b x = (∑ x ∈ S ∩ T, b x) + ∑ x ∈ S \ T, b x :=
    (sum_inter_add_sum_sdiff S T b).symm
  have hTsplit : ∑ x ∈ T, b x = (∑ x ∈ S ∩ T, b x) + ∑ x ∈ T \ S, b x := by
    rw [Finset.inter_comm, sum_inter_add_sum_sdiff T S b]
  have hdiff_b : ∑ x ∈ S \ T, b x ≤ ∑ x ∈ T \ S, b x := by linarith
  have heST : e ∈ S \ T := Finset.mem_sdiff.2 ⟨he, heT⟩
  have hST_erase : ∑ x ∈ S \ T, b x = b e + ∑ x ∈ (S \ T).erase e, b x :=
    (Finset.add_sum_erase (S \ T) b heST).symm
  have hle_er : ∑ x ∈ (S \ T).erase e, c x ≤ ∑ x ∈ (S \ T).erase e, b x :=
    Finset.sum_le_sum fun x hx => h.winner_ge x (Finset.mem_sdiff.1 (Finset.mem_of_mem_erase hx)).1
  have heq_TS : ∑ x ∈ T \ S, b x = ∑ x ∈ T \ S, c x :=
    Finset.sum_congr rfl fun x hx => h.loser_truthful x (Finset.mem_sdiff.1 hx).2
  have hSer : ∑ x ∈ S.erase e, c x = (∑ x ∈ S ∩ T, c x) + ∑ x ∈ (S \ T).erase e, c x := by
    have hSc := (sum_inter_add_sum_sdiff S T c).symm
    rw [Finset.sum_erase_eq_sub he, Finset.sum_erase_eq_sub heST]
    linarith
  have hTc : ∑ x ∈ T, c x = (∑ x ∈ S ∩ T, c x) + ∑ x ∈ T \ S, c x := by
    rw [Finset.inter_comm, sum_inter_add_sum_sdiff T S c]
  linarith

/-- **Game-theoretic equivalence ([HartlineKarlin2007], §13.5.1 and Footnote 3, p. 352):**
given any pay-your-bid allocation rule `alloc` that selects a minimum-bid feasible set on every
bid profile and picks `S` at `b` on a monopoly-free family `F`, `(b, S)` satisfies
`IsPayYourBidNash F c b S` if and only if non-winners bid truthfully and no agent can strictly
increase its pay-your-bid utility by a unilateral deviation. -/
theorem isPayYourBidNash_iff_pureNash [DecidableEq E] {F : Finset (Finset E)}
    (hmono : IsMonopolyFree F) {alloc : (E → ℝ) → Finset E}
    (halloc : ∀ b', IsMinCostSet F b' (alloc b')) {c b : E → ℝ} {S : Finset E}
    (hS : alloc b = S) :
    IsPayYourBidNash F c b S ↔
      (∀ e, e ∉ S → b e = c e) ∧
      ∀ (e : E) (z : ℝ),
        payYourBidUtility e (c e) (Function.update b e z) (alloc (Function.update b e z)) ≤
          payYourBidUtility e (c e) b S := by
  constructor
  · intro h
    refine ⟨h.loser_truthful, fun e z => ?_⟩
    let b' := Function.update b e z
    let S' := alloc b'
    have hS' : IsMinCostSet F b' S' := halloc b'
    change payYourBidUtility e (c e) b' S' ≤ payYourBidUtility e (c e) b S
    by_cases heS : e ∈ S
    · simp only [payYourBidUtility, heS, ↓reduceIte]
      by_cases heS' : e ∈ S'
      · simp only [heS', ↓reduceIte, b', Function.update_self]
        by_cases hzb : z ≤ b e
        · linarith
        · push Not at hzb
          obtain ⟨T, hTF, heT, hTeq⟩ := h.winner_tight e heS
          have hle := hS'.2 T hTF
          rw [sum_update_eq_add_ite S' b e z, sum_update_eq_add_ite T b e z] at hle
          simp only [heS', heT, ↓reduceIte, add_zero] at hle
          linarith [h.min_bid S' hS'.1]
      · simp only [heS', ↓reduceIte]
        linarith [h.winner_ge e heS]
    · simp only [payYourBidUtility, heS, ↓reduceIte]
      by_cases heS' : e ∈ S'
      · simp only [heS', ↓reduceIte, b', Function.update_self]
        have hle := hS'.2 S h.mem
        rw [sum_update_eq_add_ite S' b e z, sum_update_eq_add_ite S b e z] at hle
        simp only [heS', heS, ↓reduceIte, add_zero] at hle
        have hbc : b e = c e := h.loser_truthful e heS
        linarith [h.min_bid S' hS'.1]
      · simp only [heS', ↓reduceIte, le_rfl]
  · rintro ⟨hloser, hne⟩
    have hSb : IsMinCostSet F b S := hS ▸ halloc b
    refine ⟨hSb.1, hSb.2, ?_, hloser, ?_⟩
    · intro e heS
      by_contra hlt
      push Not at hlt
      obtain ⟨T, hTF, heT⟩ := hmono e
      let z := b e + ((∑ x ∈ T, b x) - ∑ x ∈ S, b x) + 1
      let b' := Function.update b e z
      have he_not : e ∉ alloc b' := by
        intro he'
        have hle := (halloc b').2 T hTF
        rw [sum_update_eq_add_ite (alloc b') b e z, sum_update_eq_add_ite T b e z] at hle
        simp only [he', heT, ↓reduceIte, add_zero] at hle
        have hS_le := hSb.2 (alloc b') (halloc b').1
        dsimp only [z] at hle
        linarith
      have hdev := hne e z
      simp only [payYourBidUtility, heS, ↓reduceIte] at hdev
      change (if e ∈ alloc b' then _ else 0) ≤ _ at hdev
      simp only [he_not, ↓reduceIte] at hdev
      linarith
    · intro e heS
      by_contra hno
      push Not at hno
      have hstrict : ∀ T ∈ F.filter (fun T => e ∉ T), 0 < (∑ x ∈ T, b x) - ∑ x ∈ S, b x := by
        intro T hT
        obtain ⟨hTF, heT⟩ := Finset.mem_filter.1 hT
        exact sub_pos.2 (lt_of_le_of_ne (hSb.2 T hTF) (hno T hTF heT))
      let δ := (F.filter fun T => e ∉ T).inf' (hmono.filter_notMem_nonempty e)
        (fun T => (∑ x ∈ T, b x) - ∑ x ∈ S, b x)
      have hδpos : 0 < δ := (Finset.lt_inf'_iff _).2 hstrict
      let z := b e + δ / 2
      let b' := Function.update b e z
      have he_in : e ∈ alloc b' := by
        by_contra he_not
        have hle := (halloc b').2 S hSb.1
        rw [sum_update_eq_add_ite (alloc b') b e z, sum_update_eq_add_ite S b e z] at hle
        simp only [he_not, heS, ↓reduceIte, add_zero] at hle
        have hδle : δ ≤ (∑ x ∈ alloc b', b x) - ∑ x ∈ S, b x :=
          Finset.inf'_le (fun T => (∑ x ∈ T, b x) - ∑ x ∈ S, b x)
            (Finset.mem_filter.2 ⟨(halloc b').1, he_not⟩)
        dsimp only [z] at hle
        linarith
      have hdev := hne e z
      simp only [payYourBidUtility, heS, ↓reduceIte, Function.update_self] at hdev
      change (if e ∈ alloc b' then z - c e else 0) ≤ _ at hdev
      simp only [he_in, ↓reduceIte] at hdev
      dsimp only [z] at hdev
      linarith

/-- Greedy bid-raising construction: for every monopoly-free family `F` and every minimum-cost
feasible set `S`, raising the bids of elements of `S` one by one up to their tightest blocking
alternative yields a restricted pay-your-bid Nash equilibrium `(b, S)`. -/
theorem exists_isPayYourBidNash_of_isMinCostSet {F : Finset (Finset E)}
    (hmono : IsMonopolyFree F) {c : E → ℝ} {S : Finset E} (hS : IsMinCostSet F c S) :
    ∃ b : E → ℝ, IsPayYourBidNash F c b S := by
  classical
  suffices h : ∀ D : Finset E, D ⊆ S →
      ∃ b : E → ℝ,
        (∀ T ∈ F, ∑ x ∈ S, b x ≤ ∑ x ∈ T, b x) ∧
        (∀ e ∈ S, c e ≤ b e) ∧
        (∀ e, e ∉ S → b e = c e) ∧
        (∀ e ∈ D, ∃ T ∈ F, e ∉ T ∧ ∑ x ∈ S, b x = ∑ x ∈ T, b x) by
    obtain ⟨b, hmin, hge, hloser, htight⟩ := h S Subset.rfl
    exact ⟨b, hS.1, hmin, hge, hloser, htight⟩
  intro D
  induction D using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨c, hS.2, fun _ _ => le_rfl, fun _ _ => rfl, fun _ h => (Finset.notMem_empty _ h).elim⟩
  | @insert e D heD ih =>
    intro hsub
    obtain ⟨b, hmin, hge, hloser, htight⟩ := ih ((Finset.subset_insert e D).trans hsub)
    have heS : e ∈ S := hsub (Finset.mem_insert_self e D)
    set Fe := F.filter fun T => e ∉ T
    have hFe : Fe.Nonempty := hmono.filter_notMem_nonempty e
    obtain ⟨Tstar, hTstar_mem, hTstar_min⟩ :=
      Finset.exists_min_image Fe (fun T => (∑ x ∈ T, b x) - ∑ x ∈ S, b x) hFe
    set δ := (∑ x ∈ Tstar, b x) - ∑ x ∈ S, b x
    have hδ0 : 0 ≤ δ := sub_nonneg.2 (hmin Tstar (Finset.mem_filter.1 hTstar_mem).1)
    set b' := Function.update b e (b e + δ)
    have hsum_b' : ∀ A : Finset E,
        ∑ x ∈ A, b' x = (∑ x ∈ A, b x) + if e ∈ A then δ else 0 := fun A => by
      rw [sum_update_eq_add_ite A b e (b e + δ)]
      simp only [add_sub_cancel_left]
    refine ⟨b', ?_, ?_, ?_, ?_⟩
    · intro T hTF
      rw [hsum_b' S, hsum_b' T]
      simp only [heS, ↓reduceIte]
      by_cases heT : e ∈ T
      · simp only [heT, ↓reduceIte]
        linarith [hmin T hTF]
      · simp only [heT, ↓reduceIte, add_zero]
        have hle := hTstar_min T (Finset.mem_filter.2 ⟨hTF, heT⟩)
        linarith
    · intro x hxS
      by_cases hxe : x = e
      · subst hxe
        simp only [b', Function.update_self]
        linarith [hge x hxS]
      · simp only [b', Function.update_of_ne hxe]
        exact hge x hxS
    · intro x hxS
      have hxe : x ≠ e := fun h => hxS (h ▸ heS)
      simp only [b', Function.update_of_ne hxe]
      exact hloser x hxS
    · intro d hd
      rcases Finset.mem_insert.1 hd with rfl | hdD
      · refine ⟨Tstar, (Finset.mem_filter.1 hTstar_mem).1, (Finset.mem_filter.1 hTstar_mem).2, ?_⟩
        rw [hsum_b' S, hsum_b' Tstar]
        simp only [heS, (Finset.mem_filter.1 hTstar_mem).2, ↓reduceIte, add_zero]
        ring
      · obtain ⟨T, hTF, hdT, hTeq⟩ := htight d hdD
        refine ⟨T, hTF, hdT, ?_⟩
        rw [hsum_b' S, hsum_b' T]
        simp only [heS, ↓reduceIte]
        by_cases heT : e ∈ T
        · simp only [heT, ↓reduceIte, hTeq]
        · simp only [heT, ↓reduceIte, add_zero]
          have hle := hTstar_min T (Finset.mem_filter.2 ⟨hTF, heT⟩)
          have hδ_zero : δ = 0 := by linarith
          linarith

/-- Every nonempty, monopoly-free set system has at least one restricted pay-your-bid Nash
equilibrium ([HartlineKarlin2007], §13.5.1, p. 352). -/
theorem exists_isPayYourBidNash {F : Finset (Finset E)} (hF : F.Nonempty)
    (hmono : IsMonopolyFree F) (c : E → ℝ) :
    ∃ b S, IsPayYourBidNash F c b S := by
  obtain ⟨S, hS⟩ := exists_isMinCostSet hF c
  obtain ⟨b, hb⟩ := exists_isPayYourBidNash_of_isMinCostSet hmono hS
  exact ⟨b, S, hb⟩

/-- The *cheapest Nash benchmark* `N(c)` ([HartlineKarlin2007], §13.5.1, p. 352): the infimum of
total pay-your-bid payments `∑ e ∈ S, b e` over all restricted pure Nash equilibria `(b, S)` for
true cost profile `c`. -/
@[expose] noncomputable def cheapestNash (F : Finset (Finset E)) (c : E → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ b S, IsPayYourBidNash F c b S ∧ r = ∑ e ∈ S, b e}

private theorem bddBelow_payYourBidNash_set {F : Finset (Finset E)} (hF : F.Nonempty)
    (c : E → ℝ) :
    BddBelow {r : ℝ | ∃ b S, IsPayYourBidNash F c b S ∧ r = ∑ e ∈ S, b e} := by
  refine ⟨F.inf' hF (fun S => ∑ e ∈ S, c e), ?_⟩
  rintro r ⟨b, S, h, rfl⟩
  exact (Finset.inf'_le (fun T => ∑ e ∈ T, c e) h.mem).trans
    (Finset.sum_le_sum fun e he => h.winner_ge e he)

theorem cheapestNash_le_of_isPayYourBidNash {F : Finset (Finset E)} (hF : F.Nonempty)
    {c b : E → ℝ} {S : Finset E} (h : IsPayYourBidNash F c b S) :
    cheapestNash F c ≤ ∑ e ∈ S, b e :=
  csInf_le (bddBelow_payYourBidNash_set hF c) ⟨b, S, h, rfl⟩

theorem le_cheapestNash {F : Finset (Finset E)} (hF : F.Nonempty)
    (hmono : IsMonopolyFree F) {c : E → ℝ} {r : ℝ}
    (h : ∀ b S, IsPayYourBidNash F c b S → r ≤ ∑ e ∈ S, b e) :
    r ≤ cheapestNash F c := by
  obtain ⟨b₀, S₀, h₀⟩ := exists_isPayYourBidNash hF hmono c
  exact le_csInf ⟨∑ e ∈ S₀, b₀ e, b₀, S₀, h₀, rfl⟩ fun _ ⟨b, S, hne, hr⟩ => hr ▸ h b S hne

theorem cheapestNash_nonneg {F : Finset (Finset E)} (hF : F.Nonempty)
    (hmono : IsMonopolyFree F) {c : E → ℝ} (hc : 0 ≤ c) :
    0 ≤ cheapestNash F c :=
  le_cheapestNash hF hmono fun _ _ h =>
    Finset.sum_nonneg fun e he => (hc e).trans (h.winner_ge e he)

/-- On every nonempty, monopoly-free set system, the cheapest Nash benchmark `N(c)` never exceeds
the VCG total payment (for any cost profile `c`). -/
theorem cheapestNash_le_vcgTotalPay [Fintype E] [DecidableEq E] {F : Finset (Finset E)}
    (hF : F.Nonempty) (hmono : IsMonopolyFree F) (c : E → ℝ) :
    cheapestNash F c ≤ (vcgMechanism F hF hmono).totalPay c := by
  set S := vcgAlloc F hF c
  have hS : IsMinCostSet F c S := vcgAlloc_isMinCostSet F hF c
  obtain ⟨b, hb⟩ := exists_isPayYourBidNash_of_isMinCostSet hmono hS
  have hle : ∑ e ∈ S, b e ≤ ∑ e ∈ S, vcgPayOfSet F hmono c S e :=
    Finset.sum_le_sum fun e he => hb.bid_le_vcgPayOfSet hmono he
  have htot : (vcgMechanism F hF hmono).totalPay c = ∑ e ∈ S, vcgPayOfSet F hmono c S e := by
    unfold ProcurementMechanism.totalPay vcgMechanism
    symm
    exact Finset.sum_subset (Finset.subset_univ _) fun e _ he => vcgPayOfSet_of_notMem hmono hS he
  rw [htot]
  exact (cheapestNash_le_of_isPayYourBidNash hF hb).trans hle

/-- **Frugality ratio upper bound ([HartlineKarlin2007], Definition 13.52, p. 352):**
`HasFrugalityRatioLe F M ρ` states that `0 ≤ ρ` and for every nonnegative cost profile `c`,
`M.totalPay c ≤ ρ * cheapestNash F c` (multiplicative form avoiding `0 / 0`). -/
@[expose] def HasFrugalityRatioLe [Fintype E] (F : Finset (Finset E))
    (M : ProcurementMechanism E F) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ ∀ c : E → ℝ, 0 ≤ c → M.totalPay c ≤ ρ * cheapestNash F c

/-- On a family `F` of at least two pairwise-disjoint nonempty feasible sets (such as `k ≥ 2`
parallel vertex-disjoint `s`-`t` paths), `cheapestNash F c` equals the cost of the second-cheapest
feasible set ([HartlineKarlin2007], §13.5.1, p. 352). -/
theorem cheapestNash_of_pairwiseDisjoint [DecidableEq E] {F : Finset (Finset E)}
    (hdisj : (F : Set (Finset E)).PairwiseDisjoint id) (hne_sets : ∀ S ∈ F, S.Nonempty)
    (hcard : 2 ≤ F.card) (c : E → ℝ) {S : Finset E} (hS : IsMinCostSet F c S) :
    cheapestNash F c =
      (F.erase S).inf' (Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hS.1]; omega))
        (fun T => ∑ e ∈ T, c e) := by
  have hF : F.Nonempty := ⟨S, hS.1⟩
  have her_ne : (F.erase S).Nonempty :=
    Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hS.1]; omega)
  have hmono : IsMonopolyFree F := by
    intro e
    by_cases heS : e ∈ S
    · obtain ⟨T, hT⟩ := her_ne
      obtain ⟨hTS, hTF⟩ := Finset.mem_erase.1 hT
      exact ⟨T, hTF, Finset.disjoint_left.1 (hdisj hS.1 hTF hTS.symm) heS⟩
    · exact ⟨S, hS.1, heS⟩
  have hsecond_eq : ∀ b S', IsPayYourBidNash F c b S' →
      ∑ e ∈ S', b e = (F.erase S).inf' her_ne (fun T => ∑ e ∈ T, c e) := by
    intro b S' h
    obtain ⟨e₀, he₀⟩ := hne_sets S' h.mem
    obtain ⟨T₀, hT₀F, he₀T₀, hT₀eq⟩ := h.winner_tight e₀ he₀
    have hT₀ne : T₀ ≠ S' := fun hEq => he₀T₀ (hEq ▸ he₀)
    have hT₀c : ∑ e ∈ T₀, b e = ∑ e ∈ T₀, c e :=
      Finset.sum_congr rfl fun e he =>
        h.loser_truthful e (Finset.disjoint_left.1 (hdisj hT₀F h.mem hT₀ne) he)
    have hS'_min : IsMinCostSet F c S' := h.isMinCostSet
    have hS'_c : ∑ e ∈ S', c e = ∑ e ∈ S, c e :=
      le_antisymm (hS'_min.2 S hS.1) (hS.2 S' hS'_min.1)
    have hother_le : ∀ T ∈ F, T ≠ S' → ∑ e ∈ S', b e ≤ ∑ e ∈ T, c e := by
      intro T hTF hTne
      have hTc : ∑ e ∈ T, b e = ∑ e ∈ T, c e :=
        Finset.sum_congr rfl fun e he =>
          h.loser_truthful e (Finset.disjoint_left.1 (hdisj hTF h.mem hTne) he)
      linarith [h.min_bid T hTF]
    refine le_antisymm ?_ ?_
    · refine Finset.le_inf' _ _ fun T hT => ?_
      obtain ⟨hTS, hTF⟩ := Finset.mem_erase.1 hT
      by_cases hTS' : T = S'
      · rw [hTS', hS'_c]
        have hS_ne : S ≠ S' := hTS' ▸ hTS.symm
        exact hother_le S hS.1 hS_ne
      · exact hother_le T hTF hTS'
    · rw [hT₀eq, hT₀c]
      by_cases hT₀S : T₀ = S
      · rw [hT₀S, ← hS'_c]
        have hS'ne : S' ≠ S := hT₀S ▸ hT₀ne.symm
        exact Finset.inf'_le (fun T => ∑ e ∈ T, c e) (Finset.mem_erase.2 ⟨hS'ne, h.mem⟩)
      · exact Finset.inf'_le (fun T => ∑ e ∈ T, c e) (Finset.mem_erase.2 ⟨hT₀S, hT₀F⟩)
  refine le_antisymm ?_ (le_cheapestNash hF hmono fun b S' h => (hsecond_eq b S' h).ge)
  obtain ⟨b, S', h⟩ := exists_isPayYourBidNash hF hmono c
  exact (cheapestNash_le_of_isPayYourBidNash hF h).trans_eq (hsecond_eq b S' h)

end NashBenchmark

/-! ### Theorem 13.53: Matroid characterization of VCG frugality ratio `1` -/

section MatroidCharacterization

variable {E : Type*}

/-- A finite family `F : Finset (Finset E)` is a *matroid base family* if it is nonempty and
satisfies the basis exchange axiom: for any `S, T ∈ F` and `e ∈ S \ T`, there exists `f ∈ T \ S`
such that `insert f (S.erase e) ∈ F`. -/
structure IsMatroidBaseFamily [DecidableEq E] (F : Finset (Finset E)) : Prop where
  /-- There is at least one base. -/
  nonempty : F.Nonempty
  /-- Basis exchange axiom. -/
  exchange : ∀ S ∈ F, ∀ T ∈ F, ∀ e ∈ S \ T, ∃ f ∈ T \ S, insert f (S.erase e) ∈ F

/-- Every matroid base family is an antichain under inclusion. -/
theorem IsMatroidBaseFamily.isAntichain [DecidableEq E] {F : Finset (Finset E)}
    (h : IsMatroidBaseFamily F) : IsAntichain (· ⊆ ·) (F : Set (Finset E)) := by
  intro S hS T hT hne hsub
  obtain ⟨e, heT, heS⟩ := Finset.not_subset.1 fun hTS => hne (Finset.Subset.antisymm hsub hTS)
  obtain ⟨f, hf, _⟩ := h.exchange T hT S hS e (Finset.mem_sdiff.2 ⟨heT, heS⟩)
  exact (Finset.mem_sdiff.1 hf).2 (hsub (Finset.mem_sdiff.1 hf).1)

/-- Bridge to Mathlib's `Matroid`: on a finite ground type `E`, `IsMatroidBaseFamily F` holds if
and only if `F` is the family of bases of a `Matroid E` with ground set `Set.univ`. -/
theorem isMatroidBaseFamily_iff_exists_matroid [Finite E] [DecidableEq E]
    (F : Finset (Finset E)) :
    IsMatroidBaseFamily F ↔
      ∃ M : Matroid E, M.E = Set.univ ∧ ∀ S : Finset E, S ∈ F ↔ M.IsBase (S : Set E) := by
  constructor
  · intro h
    let isBaseSet : Set E → Prop := fun B => ∃ S ∈ F, (S : Set E) = B
    let indepSet : Set E → Prop := fun I => ∃ S ∈ F, I ⊆ (S : Set E)
    have hexch : Matroid.ExchangeProperty isBaseSet := by
      rintro X Y ⟨S, hSF, rfl⟩ ⟨T, hTF, rfl⟩ e ⟨heS, heT⟩
      obtain ⟨f, hf, hmem⟩ := h.exchange S hSF T hTF e (Finset.mem_sdiff.2 ⟨heS, heT⟩)
      refine ⟨f, ⟨(Finset.mem_sdiff.1 hf).1, (Finset.mem_sdiff.1 hf).2⟩,
        insert f (S.erase e), hmem, ?_⟩
      simp only [Finset.coe_insert, Finset.coe_erase]
    have hmax : ∀ X : Set E, X ⊆ Set.univ → Matroid.ExistsMaximalSubsetProperty indepSet X := by
      intro X _ I hI hIX
      exact Set.Finite.exists_le_maximal (Set.toFinite _)
        (show I ∈ {K | indepSet K ∧ K ⊆ X} from ⟨hI, hIX⟩)
    refine ⟨{
      E := Set.univ
      IsBase := isBaseSet
      Indep := indepSet
      indep_iff' := fun I => ⟨fun ⟨S, hSF, hIS⟩ => ⟨(S : Set E), ⟨S, hSF, rfl⟩, hIS⟩,
        fun ⟨_, ⟨S, hSF, rfl⟩, hIS⟩ => ⟨S, hSF, hIS⟩⟩
      exists_isBase := let ⟨S, hSF⟩ := h.nonempty; ⟨(S : Set E), S, hSF, rfl⟩
      isBase_exchange := hexch
      maximality := hmax
      subset_ground := fun _ _ => Set.subset_univ _
    }, rfl, fun S => ⟨fun hSF => ⟨S, hSF, rfl⟩, fun ⟨T, hTF, hTS⟩ => by
      rwa [← Finset.coe_inj.1 hTS]⟩⟩
  · rintro ⟨M, _, hM⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨B, hB⟩ := M.exists_isBase
      have hfin : B.Finite := Set.toFinite B
      refine ⟨hfin.toFinset, (hM _).2 ?_⟩
      simpa only [Set.Finite.coe_toFinset] using hB
    · intro S hS T hT e he
      obtain ⟨heS, heT⟩ := Finset.mem_sdiff.1 he
      obtain ⟨f, ⟨hfT, hfS⟩, hB⟩ :=
        ((hM S).1 hS).exchange ((hM T).1 hT) ⟨heS, heT⟩
      refine ⟨f, Finset.mem_sdiff.2 ⟨hfT, hfS⟩, (hM _).2 ?_⟩
      simpa only [Finset.coe_insert, Finset.coe_erase] using hB

/-- All bases in a matroid base family have equal cardinality. -/
theorem IsMatroidBaseFamily.card_eq [Finite E] [DecidableEq E] {F : Finset (Finset E)}
    (h : IsMatroidBaseFamily F) {S T : Finset E} (hS : S ∈ F) (hT : T ∈ F) :
    S.card = T.card := by
  obtain ⟨M, _, hM⟩ := (isMatroidBaseFamily_iff_exists_matroid F).1 h
  have h1 := ((hM S).1 hS).encard_eq_encard_of_isBase ((hM T).1 hT)
  simpa only [Set.encard_coe_eq_coe_finsetCard, Nat.cast_inj] using h1

/-- **Brualdi's basis-exchange bijection:** for any two bases `S, T` of a finite matroid base
family `F`, there is a bijection `φ : S \ T → T \ S` such that `insert (φ x) (S.erase x) ∈ F`
for every `x ∈ S \ T`. Proved via Hall's marriage theorem and fundamental circuits. -/
theorem IsMatroidBaseFamily.exists_exchange_bijection [Finite E] [DecidableEq E]
    {F : Finset (Finset E)} (h : IsMatroidBaseFamily F) {S T : Finset E}
    (hS : S ∈ F) (hT : T ∈ F) :
    ∃ φ : {x // x ∈ S \ T} → {y // y ∈ T \ S},
      Function.Bijective φ ∧ ∀ x : {x // x ∈ S \ T}, insert (φ x).1 (S.erase x.1) ∈ F := by
  have := Fintype.ofFinite E
  obtain ⟨M, hME, hM⟩ := (isMatroidBaseFamily_iff_exists_matroid F).1 h
  have hSB : M.IsBase (S : Set E) := (hM S).1 hS
  have hTB : M.IsBase (T : Set E) := (hM T).1 hT
  let N : {x // x ∈ S \ T} → Finset E := fun x =>
    (T \ S).filter fun y => insert y (S.erase x.1) ∈ F
  have hhall : ∀ A : Finset {x // x ∈ S \ T}, A.card ≤ (A.biUnion N).card := by
    intro A
    let A' : Finset E := A.map ⟨Subtype.val, Subtype.val_injective⟩
    have hA'_sub_sdiff : A' ⊆ S \ T := by
      intro x hx
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hx
      exact a.2
    have hA'_sub_S : A' ⊆ S := hA'_sub_sdiff.trans Finset.sdiff_subset
    have hI_ind : M.Indep ((S \ A' : Finset E) : Set E) :=
      hSB.indep.subset (Finset.coe_subset.2 Finset.sdiff_subset)
    obtain ⟨B', hB'base, hSA_sub, hB'_sub⟩ := hI_ind.exists_isBase_subset_union_isBase hTB
    have hB'fin : B'.Finite := Set.toFinite B'
    set B : Finset E := hB'fin.toFinset
    have hBF : B ∈ F := (hM B).2 (by simpa only [B, Set.Finite.coe_toFinset] using hB'base)
    have hSA_B : S \ A' ⊆ B := fun x hx =>
      hB'fin.mem_toFinset.2 (hSA_sub (Finset.mem_coe.2 hx))
    have hC_sub : B \ (S \ A') ⊆ A.biUnion N := by
      intro y hy
      obtain ⟨hyB, hySA⟩ := Finset.mem_sdiff.1 hy
      have hyB' : y ∈ B' := hB'fin.mem_toFinset.1 hyB
      have hyU : y ∈ ((S \ A' : Finset E) : Set E) ∪ (T : Set E) := hB'_sub hyB'
      have hyT : y ∈ T := by
        rcases hyU with h1 | h2
        · exact absurd (Finset.mem_coe.1 h1) hySA
        · exact Finset.mem_coe.1 h2
      have hy_not_S : y ∉ S := by
        intro hyS
        have hyA' : y ∈ A' := by
          by_contra hyA'
          exact hySA (Finset.mem_sdiff.2 ⟨hyS, hyA'⟩)
        exact (Finset.mem_sdiff.1 (hA'_sub_sdiff hyA')).2 hyT
      have hcirc : M.IsCircuit (M.fundCircuit y (S : Set E)) :=
        hSB.fundCircuit_isCircuit (by rw [hME]; trivial) (by simpa using hy_not_S)
      have hnot_sub : ¬ M.fundCircuit y (S : Set E) ⊆ insert y ((S \ A' : Finset E) : Set E) := by
        intro hsub
        have hsubB' : M.fundCircuit y (S : Set E) ⊆ B' :=
          hsub.trans (Set.insert_subset hyB' hSA_sub)
        exact hcirc.dep.not_indep (hB'base.indep.subset hsubB')
      obtain ⟨x, hxC, hx_not⟩ := Set.not_subset.1 hnot_sub
      have hx_ins : x ∈ insert y (S : Set E) := M.fundCircuit_subset_insert y (S : Set E) hxC
      have hxy : x ≠ y := fun hEq => hx_not (hEq ▸ Set.mem_insert _ _)
      have hxS : x ∈ S := by
        rcases Set.mem_insert_iff.1 hx_ins with rfl | hxS
        · exact absurd rfl hxy
        · exact Finset.mem_coe.1 hxS
      have hxA' : x ∈ A' := by
        by_contra hxA'
        exact hx_not (Set.mem_insert_of_mem y (Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hxS, hxA'⟩)))
      obtain ⟨a, haA, rfl⟩ := Finset.mem_map.1 hxA'
      have hind_swap : M.Indep (insert y (S : Set E) \ {a.1}) :=
        (hSB.indep.mem_fundCircuit_iff (by rw [hSB.closure_eq, hME]; trivial)
          (by simpa using hy_not_S)).1 hxC
      have hbase_swap' : M.IsBase (insert y (S : Set E) \ {a.1}) :=
        hSB.exchange_isBase_of_indep' (Finset.mem_coe.2 hxS)
          (by simpa using hy_not_S) hind_swap
      have hay : a.1 ≠ y := hxy
      have hbase_swap : M.IsBase (insert y ((S : Set E) \ {a.1})) := by
        rwa [← Set.insert_sdiff_singleton_comm hay.symm] at hbase_swap'
      have hmem_swap : insert y (S.erase a.1) ∈ F := (hM _).2 (by
        simpa only [Finset.coe_insert, Finset.coe_erase] using hbase_swap)
      exact Finset.mem_biUnion.2 ⟨a, haA, Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hyT, hy_not_S⟩,
        hmem_swap⟩⟩
    have hcard_eq : (B \ (S \ A')).card = A.card := by
      have hBS : B.card = S.card := h.card_eq hBF hS
      have hA'card : A'.card = A.card := Finset.card_map _
      have h1 : (B \ (S \ A')).card = B.card - (S \ A').card := Finset.card_sdiff_of_subset hSA_B
      have h2 : (S \ A').card = S.card - A'.card := Finset.card_sdiff_of_subset hA'_sub_S
      have h3 : A'.card ≤ S.card := Finset.card_le_card hA'_sub_S
      omega
    exact hcard_eq ▸ Finset.card_le_card hC_sub
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective N).1 hhall
  let φ : {x // x ∈ S \ T} → {y // y ∈ T \ S} := fun x =>
    ⟨f x, (Finset.mem_filter.1 (hfmem x)).1⟩
  have hφ_inj : Function.Injective φ := fun x₁ x₂ hEq =>
    hfinj (congrArg Subtype.val hEq)
  have hcard_sdiff : Fintype.card {x // x ∈ S \ T} = Fintype.card {y // y ∈ T \ S} := by
    simp only [Fintype.card_coe]
    have h1 := Finset.card_inter_add_card_sdiff S T
    have h2 := Finset.card_inter_add_card_sdiff T S
    rw [Finset.inter_comm] at h2
    have hST := h.card_eq hS hT
    omega
  refine ⟨φ, (Fintype.bijective_iff_injective_and_card φ).2 ⟨hφ_inj, hcard_sdiff⟩, fun x =>
    (Finset.mem_filter.1 (hfmem x)).2⟩

private theorem sum_sdiff_eq_sum_bijective {α : Type*} [DecidableEq α] {S T : Finset α}
    {φ : {x // x ∈ S \ T} → {y // y ∈ T \ S}} (hφ : Function.Bijective φ) (f : α → ℝ) :
    ∑ y ∈ T \ S, f y = ∑ x : {x // x ∈ S \ T}, f (φ x).1 := by
  rw [← Finset.sum_coe_sort (T \ S) f]
  exact (Fintype.sum_bijective φ hφ _ _ fun _ => rfl).symm

/-- On a matroid base family, for any minimum-cost base `S` and `e ∈ S`, the VCG payment
`vcgPayOfSet F hmono c S e` equals the minimum cost of an element `f ∉ S` that can replace `e` in
`S`. -/
private theorem vcgPayOfSet_eq_inf_exchange [Finite E] [DecidableEq E] {F : Finset (Finset E)}
    (hmat : IsMatroidBaseFamily F) (hmono : IsMonopolyFree F) {c : E → ℝ} {S : Finset E}
    (hS : IsMinCostSet F c S) {e : E} (he : e ∈ S) :
    ∃ f, f ∉ S ∧ insert f (S.erase e) ∈ F ∧ vcgPayOfSet F hmono c S e = c f ∧
      ∀ g, g ∉ S → insert g (S.erase e) ∈ F → vcgPayOfSet F hmono c S e ≤ c g := by
  have := Fintype.ofFinite E
  have hex_ne : (Finset.univ.filter fun f : E => f ∉ S ∧ insert f (S.erase e) ∈ F).Nonempty := by
    obtain ⟨T, hTF, heT⟩ := hmono e
    obtain ⟨f, hf, hmem⟩ := hmat.exchange S hS.1 T hTF e (Finset.mem_sdiff.2 ⟨he, heT⟩)
    exact ⟨f, Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_sdiff.1 hf).2, hmem⟩⟩
  obtain ⟨f₀, hf₀_mem, hf₀_min⟩ := Finset.exists_min_image _ c hex_ne
  obtain ⟨_, hf₀S, hf₀F⟩ := Finset.mem_filter.1 hf₀_mem
  have hle : vcgPayOfSet F hmono c S e ≤ c f₀ := by
    have he_not : e ∉ insert f₀ (S.erase e) := by
      simp only [Finset.mem_insert, Finset.mem_erase, not_or, not_and]
      exact ⟨fun h => hf₀S (h ▸ he), fun h _ => h rfl⟩
    have h1 := vcgPayOfSet_le hmono c S hf₀F he_not
    have hf₀_not_er : f₀ ∉ S.erase e := fun h => hf₀S (Finset.mem_of_mem_erase h)
    rw [Finset.sum_insert hf₀_not_er] at h1
    linarith
  have hge : c f₀ ≤ vcgPayOfSet F hmono c S e := by
    refine le_vcgPayOfSet hmono c S fun T hTF heT => ?_
    obtain ⟨φ, hφbij, hφmem⟩ := hmat.exists_exchange_bijection hS.1 hTF
    have hterm : ∀ x : {x // x ∈ S \ T}, c x.1 ≤ c (φ x).1 := by
      intro x
      have hxS : x.1 ∈ S := (Finset.mem_sdiff.1 x.2).1
      have hφ_notS : (φ x).1 ∉ S := (Finset.mem_sdiff.1 (φ x).2).2
      have hle' := hS.2 _ (hφmem x)
      have hφ_not_er : (φ x).1 ∉ S.erase x.1 := fun h => hφ_notS (Finset.mem_of_mem_erase h)
      rw [Finset.sum_insert hφ_not_er, Finset.sum_erase_eq_sub hxS] at hle'
      linarith
    have heST : e ∈ S \ T := Finset.mem_sdiff.2 ⟨he, heT⟩
    let e' : {x // x ∈ S \ T} := ⟨e, heST⟩
    have hcf₀ : c f₀ ≤ c (φ e').1 := hf₀_min (φ e').1
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_sdiff.1 (φ e').2).2, hφmem e'⟩)
    have hsum_diff :
        (∑ y ∈ T \ S, c y) - (∑ x ∈ S \ T, c x) =
          ∑ x : {x // x ∈ S \ T}, (c (φ x).1 - c x.1) := by
      rw [sum_sdiff_eq_sum_bijective hφbij c, ← Finset.sum_coe_sort (S \ T) c,
        Finset.sum_sub_distrib]
    have hsum_ge : c (φ e').1 - c e ≤ ∑ x : {x // x ∈ S \ T}, (c (φ x).1 - c x.1) :=
      Finset.single_le_sum (f := fun x : {x // x ∈ S \ T} => c (φ x).1 - c x.1)
        (fun x _ => sub_nonneg.2 (hterm x)) (Finset.mem_univ e')
    have hSc : ∑ x ∈ S, c x = (∑ x ∈ S ∩ T, c x) + ∑ x ∈ S \ T, c x :=
      (sum_inter_add_sum_sdiff S T c).symm
    have hTc : ∑ x ∈ T, c x = (∑ x ∈ S ∩ T, c x) + ∑ x ∈ T \ S, c x := by
      rw [Finset.inter_comm, sum_inter_add_sum_sdiff T S c]
    rw [Finset.sum_erase_eq_sub he]
    linarith
  have heq : vcgPayOfSet F hmono c S e = c f₀ := le_antisymm hle hge
  refine ⟨f₀, hf₀S, hf₀F, heq, fun g hgS hgF => ?_⟩
  rw [heq]
  exact hf₀_min g (Finset.mem_filter.2 ⟨Finset.mem_univ _, hgS, hgF⟩)

/-- On a matroid base family, setting winner bids to their VCG payments and loser bids to their
true costs yields a restricted pay-your-bid Nash equilibrium. -/
theorem isPayYourBidNash_vcg [Finite E] [DecidableEq E] {F : Finset (Finset E)}
    (hmat : IsMatroidBaseFamily F) (hmono : IsMonopolyFree F) {c : E → ℝ} {S : Finset E}
    (hS : IsMinCostSet F c S) :
    IsPayYourBidNash F c (fun e => if e ∈ S then vcgPayOfSet F hmono c S e else c e) S := by
  let b : E → ℝ := fun e => if e ∈ S then vcgPayOfSet F hmono c S e else c e
  refine ⟨hS.1, ?_,
    fun e he => by simp only [he, ↓reduceIte]; exact cost_le_vcgPayOfSet hmono hS he,
    fun e he => by simp only [he, ↓reduceIte], ?_⟩
  · intro T hTF
    obtain ⟨φ, hφbij, hφmem⟩ := hmat.exists_exchange_bijection hS.1 hTF
    have hle_sum : ∑ x ∈ S \ T, b x ≤ ∑ y ∈ T \ S, b y := by
      rw [← Finset.sum_coe_sort (S \ T) b, sum_sdiff_eq_sum_bijective hφbij b]
      refine Finset.sum_le_sum fun x _ => ?_
      have hxS : x.1 ∈ S := (Finset.mem_sdiff.1 x.2).1
      have hφS : (φ x).1 ∉ S := (Finset.mem_sdiff.1 (φ x).2).2
      simp only [b, hxS, hφS, ↓reduceIte]
      obtain ⟨_, _, _, _, hmin⟩ := vcgPayOfSet_eq_inf_exchange hmat hmono hS hxS
      exact hmin (φ x).1 hφS (hφmem x)
    have hSb : ∑ x ∈ S, b x = (∑ x ∈ S ∩ T, b x) + ∑ x ∈ S \ T, b x :=
      (sum_inter_add_sum_sdiff S T b).symm
    have hTb : ∑ x ∈ T, b x = (∑ x ∈ S ∩ T, b x) + ∑ x ∈ T \ S, b x := by
      rw [Finset.inter_comm, sum_inter_add_sum_sdiff T S b]
    linarith
  · intro e he
    obtain ⟨f, hfS, hfF, hfeq, _⟩ := vcgPayOfSet_eq_inf_exchange hmat hmono hS he
    have he_not : e ∉ insert f (S.erase e) := by
      simp only [Finset.mem_insert, Finset.mem_erase, not_or, not_and]
      exact ⟨fun h => hfS (h ▸ he), fun h _ => h rfl⟩
    have hf_not_er : f ∉ S.erase e := fun h => hfS (Finset.mem_of_mem_erase h)
    refine ⟨insert f (S.erase e), hfF, he_not, ?_⟩
    rw [Finset.sum_insert hf_not_er, Finset.sum_erase_eq_sub he]
    simp only [he, hfS, ↓reduceIte, hfeq]
    ring

/-- On a matroid base family, every restricted pay-your-bid Nash equilibrium `(b, S')` pays every
winner its VCG payment `vcgPayOfSet F hmono c S' e`, and achieves the exact same total payment as
`vcgMechanism` (regardless of tie-breaking among minimum-cost bases). -/
theorem sum_eq_vcgTotalPay_of_isPayYourBidNash [Fintype E] [DecidableEq E]
    {F : Finset (Finset E)} (hmat : IsMatroidBaseFamily F) (hmono : IsMonopolyFree F)
    {c b : E → ℝ} {S' : Finset E} (h : IsPayYourBidNash F c b S') :
    ∑ e ∈ S', b e = (vcgMechanism F hmat.nonempty hmono).totalPay c := by
  have hS'_min : IsMinCostSet F c S' := h.isMinCostSet
  have hb_eq_vcg : ∀ e ∈ S', b e = vcgPayOfSet F hmono c S' e := by
    intro e he
    refine le_antisymm (h.bid_le_vcgPayOfSet hmono he) ?_
    obtain ⟨T, hTF, heT, hTeq⟩ := h.winner_tight e he
    obtain ⟨φ, hφbij, hφmem⟩ := hmat.exists_exchange_bijection hS'_min.1 hTF
    have hterm_le : ∀ x : {x // x ∈ S' \ T}, b x.1 ≤ b (φ x).1 := by
      intro x
      have hxS' : x.1 ∈ S' := (Finset.mem_sdiff.1 x.2).1
      have hφS' : (φ x).1 ∉ S' := (Finset.mem_sdiff.1 (φ x).2).2
      rw [h.loser_truthful _ hφS']
      obtain ⟨_, _, _, _, hmin⟩ := vcgPayOfSet_eq_inf_exchange hmat hmono hS'_min hxS'
      exact (h.bid_le_vcgPayOfSet hmono hxS').trans (hmin (φ x).1 hφS' (hφmem x))
    have hsum_eq : ∑ x : {x // x ∈ S' \ T}, b x.1 = ∑ x : {x // x ∈ S' \ T}, b (φ x).1 := by
      have hS'b : ∑ x ∈ S', b x = (∑ x ∈ S' ∩ T, b x) + ∑ x ∈ S' \ T, b x :=
        (sum_inter_add_sum_sdiff S' T b).symm
      have hTb : ∑ x ∈ T, b x = (∑ x ∈ S' ∩ T, b x) + ∑ x ∈ T \ S', b x := by
        rw [Finset.inter_comm, sum_inter_add_sum_sdiff T S' b]
      have hdiff : ∑ x ∈ S' \ T, b x = ∑ x ∈ T \ S', b x := by linarith
      rw [Finset.sum_coe_sort (S' \ T) b, hdiff, sum_sdiff_eq_sum_bijective hφbij b]
    have hall_eq : ∀ x : {x // x ∈ S' \ T}, b x.1 = b (φ x).1 := fun x =>
      (Finset.sum_eq_sum_iff_of_le (fun y _ => hterm_le y)).1 hsum_eq x (Finset.mem_univ x)
    let e' : {x // x ∈ S' \ T} := ⟨e, Finset.mem_sdiff.2 ⟨he, heT⟩⟩
    have hφeS' : (φ e').1 ∉ S' := (Finset.mem_sdiff.1 (φ e').2).2
    have hbe_eq : b e = c (φ e').1 := by
      rw [← h.loser_truthful _ hφeS']
      exact hall_eq e'
    obtain ⟨_, _, _, _, hmin⟩ := vcgPayOfSet_eq_inf_exchange hmat hmono hS'_min he
    rw [hbe_eq]
    exact hmin (φ e').1 hφeS' (hφmem e')
  set S := vcgAlloc F hmat.nonempty c
  have hS_min : IsMinCostSet F c S := vcgAlloc_isMinCostSet F hmat.nonempty c
  have hc_eq : ∑ x ∈ S', c x = ∑ x ∈ S, c x :=
    le_antisymm (hS'_min.2 S hS_min.1) (hS_min.2 S' hS'_min.1)
  have hdiff_vcg : ∀ A B : Finset E, IsMinCostSet F c A → IsMinCostSet F c B →
      ∑ x ∈ A \ B, vcgPayOfSet F hmono c A x = ∑ x ∈ A \ B, c x := by
    intro A B hA hB
    have hAB_c : ∑ x ∈ A, c x = ∑ x ∈ B, c x := le_antisymm (hA.2 B hB.1) (hB.2 A hA.1)
    have h1 : ∑ x ∈ A \ B, c x ≤ ∑ x ∈ A \ B, vcgPayOfSet F hmono c A x :=
      Finset.sum_le_sum fun x hx => cost_le_vcgPayOfSet hmono hA (Finset.mem_sdiff.1 hx).1
    have h2 : ∑ x ∈ A \ B, vcgPayOfSet F hmono c A x ≤ ∑ x ∈ B \ A, c x := by
      have hne := isPayYourBidNash_vcg hmat hmono hA
      have hle := hne.min_bid B hB.1
      have hA_eq : ∑ x ∈ A, (if x ∈ A then vcgPayOfSet F hmono c A x else c x) =
          (∑ x ∈ A ∩ B, vcgPayOfSet F hmono c A x) +
            ∑ x ∈ A \ B, vcgPayOfSet F hmono c A x := by
        rw [← sum_inter_add_sum_sdiff A B]
        congr 1
        · exact Finset.sum_congr rfl fun x hx => by
            simp only [(Finset.mem_inter.1 hx).1, ↓reduceIte]
        · exact Finset.sum_congr rfl fun x hx => by
            simp only [(Finset.mem_sdiff.1 hx).1, ↓reduceIte]
      have hB_eq : ∑ x ∈ B, (if x ∈ A then vcgPayOfSet F hmono c A x else c x) =
          (∑ x ∈ A ∩ B, vcgPayOfSet F hmono c A x) + ∑ x ∈ B \ A, c x := by
        rw [← sum_inter_add_sum_sdiff B A, Finset.inter_comm]
        congr 1
        · exact Finset.sum_congr rfl fun x hx => by
            simp only [(Finset.mem_inter.1 hx).1, ↓reduceIte]
        · exact Finset.sum_congr rfl fun x hx => by
            simp only [(Finset.mem_sdiff.1 hx).2, ↓reduceIte]
      linarith
    have h3 : ∑ x ∈ B \ A, c x = ∑ x ∈ A \ B, c x := by
      have hBc := (sum_inter_add_sum_sdiff B A c).symm
      have hAc := (sum_inter_add_sum_sdiff A B c).symm
      rw [Finset.inter_comm] at hBc
      linarith
    linarith
  have hS'_diff := hdiff_vcg S' S hS'_min hS_min
  have hS_diff := hdiff_vcg S S' hS_min hS'_min
  have hinter_eq : ∑ x ∈ S' ∩ S, vcgPayOfSet F hmono c S' x =
      ∑ x ∈ S' ∩ S, vcgPayOfSet F hmono c S x :=
    Finset.sum_congr rfl fun x hx => by
      obtain ⟨hxS', hxS⟩ := Finset.mem_inter.1 hx
      rw [vcgPayOfSet_of_mem hmono c hxS', vcgPayOfSet_of_mem hmono c hxS, hc_eq]
  have hcdiff : ∑ x ∈ S' \ S, c x = ∑ x ∈ S \ S', c x := by
    have hSc := (sum_inter_add_sum_sdiff S S' c).symm
    have hS'c := (sum_inter_add_sum_sdiff S' S c).symm
    rw [Finset.inter_comm] at hSc
    linarith
  have htot : (vcgMechanism F hmat.nonempty hmono).totalPay c =
      ∑ x ∈ S, vcgPayOfSet F hmono c S x := by
    unfold ProcurementMechanism.totalPay vcgMechanism
    symm
    exact Finset.sum_subset (Finset.subset_univ _) fun e _ he =>
      vcgPayOfSet_of_notMem hmono hS_min he
  rw [htot, Finset.sum_congr rfl hb_eq_vcg,
    ← sum_inter_add_sum_sdiff S' S, ← sum_inter_add_sum_sdiff S S',
    Finset.inter_comm S S', hinter_eq, hS'_diff, hS_diff, hcdiff]

/-- **Theorem 13.53 (forward direction, exact equality):** on any monopoly-free matroid base
family, VCG's total payment equals the cheapest Nash benchmark `N(c)` for every cost profile `c`
([HartlineKarlin2007], §13.5.1.1, p. 353). -/
theorem vcgTotalPay_eq_cheapestNash_of_isMatroidBaseFamily [Fintype E] [DecidableEq E]
    {F : Finset (Finset E)} (hmat : IsMatroidBaseFamily F) (hmono : IsMonopolyFree F)
    (c : E → ℝ) :
    (vcgMechanism F hmat.nonempty hmono).totalPay c = cheapestNash F c :=
  le_antisymm
    (le_cheapestNash hmat.nonempty hmono fun _ _ h =>
      (sum_eq_vcgTotalPay_of_isPayYourBidNash hmat hmono h).ge)
    (cheapestNash_le_vcgTotalPay hmat.nonempty hmono c)

/-- On any monopoly-free matroid base family, VCG has frugality ratio at most `1` (hence exact
frugality ratio `1`, by `cheapestNash_le_vcgTotalPay`). -/
theorem vcg_hasFrugalityRatioLe_one_of_isMatroidBaseFamily [Fintype E] [DecidableEq E]
    {F : Finset (Finset E)} (hmat : IsMatroidBaseFamily F) (hmono : IsMonopolyFree F) :
    HasFrugalityRatioLe F (vcgMechanism F hmat.nonempty hmono) 1 :=
  ⟨zero_le_one, fun c _ => by
    rw [one_mul, vcgTotalPay_eq_cheapestNash_of_isMatroidBaseFamily hmat hmono c]⟩

/-- Helper for the converse of Theorem 13.53: for any `S, T ∈ F` in an antichain, assigning cost
`0` on `S`, `1` on `T \ S`, and `2` outside `S ∪ T` makes `S` the unique minimum-cost feasible set
and bounds the Nash total payment on `S \ T` by `(T \ S).card`, while every `x ∈ S \ T` has VCG
payment at least `1`. -/
private theorem converse_cost_profile_bounds [DecidableEq E] {F : Finset (Finset E)}
    (hF : F.Nonempty) (hmono : IsMonopolyFree F)
    (hanti : IsAntichain (· ⊆ ·) (F : Set (Finset E))) {S T : Finset E} (hSF : S ∈ F)
    (hTF : T ∈ F) :
    let c : E → ℝ := fun x => if x ∈ S then 0 else if x ∈ T then 1 else 2
    0 ≤ c ∧
    vcgAlloc F hF c = S ∧
    (∀ x ∈ S \ T, 1 ≤ vcgPayOfSet F hmono c S x) ∧
    ∃ b : E → ℝ, IsPayYourBidNash F c b S ∧
      ∑ x ∈ S, b x ≤ (∑ x ∈ S ∩ T, vcgPayOfSet F hmono c S x) + ((T \ S).card : ℝ) := by
  intro c
  have hc0 : 0 ≤ c := fun x => by
    dsimp only [c]
    split_ifs <;> norm_num
  have hcS : ∑ x ∈ S, c x = 0 := Finset.sum_eq_zero fun x hx => by simp only [c, hx, ↓reduceIte]
  have hSmin : IsMinCostSet F c S := ⟨hSF, fun R _ => by
    rw [hcS]
    exact Finset.sum_nonneg fun x _ => hc0 x⟩
  have huniq : vcgAlloc F hF c = S := by
    set A := vcgAlloc F hF c
    have hA := vcgAlloc_isMinCostSet F hF c
    have hA0 : ∑ x ∈ A, c x = 0 := le_antisymm (hcS ▸ hA.2 S hSF)
      (Finset.sum_nonneg fun x _ => hc0 x)
    have hAS : A ⊆ S := by
      intro x hxA
      by_contra hxS
      have hxpos : 0 < c x := by
        dsimp only [c]
        simp only [hxS, ↓reduceIte]
        split_ifs <;> norm_num
      have hle := Finset.single_le_sum (f := c) (fun y _ => hc0 y) hxA
      linarith
    exact hanti.eq hA.1 hSF hAS
  have hvcg_ge_one : ∀ x ∈ S \ T, 1 ≤ vcgPayOfSet F hmono c S x := by
    intro x hx
    have hxS : x ∈ S := (Finset.mem_sdiff.1 hx).1
    refine le_vcgPayOfSet hmono c S fun R hRF hxR => ?_
    have hnot_sub : ¬ R ⊆ S := fun hRS => hxR (hanti.eq hRF hSF hRS ▸ hxS)
    obtain ⟨y, hyR, hyS⟩ := Finset.not_subset.1 hnot_sub
    have hy_ge : 1 ≤ c y := by
      dsimp only [c]
      simp only [hyS, ↓reduceIte]
      split_ifs <;> norm_num
    have hR_ge : 1 ≤ ∑ z ∈ R, c z := hy_ge.trans (Finset.single_le_sum (fun z _ => hc0 z) hyR)
    have hSer : ∑ z ∈ S.erase x, c z = 0 :=
      Finset.sum_eq_zero fun z hz => by simp only [c, Finset.mem_of_mem_erase hz, ↓reduceIte]
    linarith
  obtain ⟨b, hb⟩ := exists_isPayYourBidNash_of_isMinCostSet hmono hSmin
  refine ⟨hc0, huniq, hvcg_ge_one, b, hb, ?_⟩
  have hSb : ∑ x ∈ S, b x = (∑ x ∈ S ∩ T, b x) + ∑ x ∈ S \ T, b x :=
    (sum_inter_add_sum_sdiff S T b).symm
  have hTb : ∑ x ∈ T, b x = (∑ x ∈ S ∩ T, b x) + ∑ x ∈ T \ S, b x := by
    rw [Finset.inter_comm, sum_inter_add_sum_sdiff T S b]
  have hdiff_le : ∑ x ∈ S \ T, b x ≤ ∑ x ∈ T \ S, b x := by linarith [hb.min_bid T hTF]
  have hTS_eq : ∑ x ∈ T \ S, b x = ((T \ S).card : ℝ) := by
    calc ∑ x ∈ T \ S, b x = ∑ x ∈ T \ S, c x :=
          Finset.sum_congr rfl fun x hx => hb.loser_truthful x (Finset.mem_sdiff.1 hx).2
      _ = ∑ _x ∈ T \ S, (1 : ℝ) :=
          Finset.sum_congr rfl fun x hx => by
            obtain ⟨hxT, hxS⟩ := Finset.mem_sdiff.1 hx
            simp only [c, hxS, hxT, ↓reduceIte]
      _ = ((T \ S).card : ℝ) := by simp
  have hinter_le : ∑ x ∈ S ∩ T, b x ≤ ∑ x ∈ S ∩ T, vcgPayOfSet F hmono c S x :=
    Finset.sum_le_sum fun x hx => hb.bid_le_vcgPayOfSet hmono (Finset.mem_inter.1 hx).1
  linarith

/-- **Theorem 13.53 (converse direction):** on any nonempty, monopoly-free antichain `(E, F)`, if
VCG has frugality ratio `1`, then `F` is a matroid base family ([HartlineKarlin2007], §13.5.1.1,
p. 353). -/
private theorem isMatroidBaseFamily_of_vcg_hasFrugalityRatioLe_one [Fintype E] [DecidableEq E]
    {F : Finset (Finset E)} (hF : F.Nonempty) (hmono : IsMonopolyFree F)
    (hanti : IsAntichain (· ⊆ ·) (F : Set (Finset E)))
    (h1 : HasFrugalityRatioLe F (vcgMechanism F hF hmono) 1) :
    IsMatroidBaseFamily F := by
  have hequicard : ∀ S ∈ F, ∀ T ∈ F, S.card = T.card := by
    intro S hSF T hTF
    suffices hle : ∀ A ∈ F, ∀ B ∈ F, A.card ≤ B.card from
      le_antisymm (hle S hSF T hTF) (hle T hTF S hSF)
    intro A hAF B hBF
    by_contra hlt
    push Not at hlt
    obtain ⟨hc0, huniq, hvcg_ge, b, hb, hb_le⟩ :=
      converse_cost_profile_bounds hF hmono hanti hAF hBF
    set c : E → ℝ := fun x => if x ∈ A then 0 else if x ∈ B then 1 else 2
    have htot : (vcgMechanism F hF hmono).totalPay c =
        (∑ x ∈ A ∩ B, vcgPayOfSet F hmono c A x) + ∑ x ∈ A \ B, vcgPayOfSet F hmono c A x := by
      rw [(vcgMechanism F hF hmono).totalPay_eq_sum_alloc (vcgMechanism_losersPaidZero F hF hmono)
        hc0]
      simp only [vcgMechanism, huniq]
      exact (sum_inter_add_sum_sdiff A B _).symm
    have hdiff_ge : ((A \ B).card : ℝ) ≤ ∑ x ∈ A \ B, vcgPayOfSet F hmono c A x := by
      calc ((A \ B).card : ℝ) = ∑ _x ∈ A \ B, (1 : ℝ) := by simp
        _ ≤ ∑ x ∈ A \ B, vcgPayOfSet F hmono c A x := Finset.sum_le_sum hvcg_ge
    have hcard_lt : (B \ A).card < (A \ B).card := by
      have h1 := Finset.card_inter_add_card_sdiff A B
      have h2 := Finset.card_inter_add_card_sdiff B A
      rw [Finset.inter_comm] at h2
      omega
    have hcard_lt_R : ((B \ A).card : ℝ) < ((A \ B).card : ℝ) := Nat.cast_lt.2 hcard_lt
    have hratio := h1.2 c hc0
    rw [one_mul] at hratio
    have hcn := cheapestNash_le_of_isPayYourBidNash hF hb
    linarith
  refine ⟨hF, fun S hSF T hTF e he => ?_⟩
  by_contra hno
  push Not at hno
  obtain ⟨hc0, huniq, hvcg_ge, b, hb, hb_le⟩ :=
    converse_cost_profile_bounds hF hmono hanti hSF hTF
  set c : E → ℝ := fun x => if x ∈ S then 0 else if x ∈ T then 1 else 2
  have heS : e ∈ S := (Finset.mem_sdiff.1 he).1
  have hvcg_e_ge2 : 2 ≤ vcgPayOfSet F hmono c S e := by
    refine le_vcgPayOfSet hmono c S fun R hRF heR => ?_
    have hSer : ∑ z ∈ S.erase e, c z = 0 :=
      Finset.sum_eq_zero fun z hz => by simp only [c, Finset.mem_of_mem_erase hz, ↓reduceIte]
    rw [hSer, sub_zero]
    by_cases hRsub : R ⊆ S ∪ T
    · have hRS_ne : (R \ S).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hempty
        exact heR (hanti.eq hRF hSF hempty ▸ heS)
      have hRS_ge2 : 2 ≤ (R \ S).card := by
        by_contra hlt2
        have hcard1 : (R \ S).card = 1 := by
          have hpos := Finset.card_pos.2 hRS_ne
          omega
        obtain ⟨f, hf_eq⟩ := Finset.card_eq_one.1 hcard1
        have hfRS : f ∈ R \ S := hf_eq ▸ Finset.mem_singleton_self f
        have hfT : f ∈ T := by
          rcases Finset.mem_union.1 (hRsub (Finset.mem_sdiff.1 hfRS).1) with hfS | hfT
          · exact absurd hfS (Finset.mem_sdiff.1 hfRS).2
          · exact hfT
        have hfS : f ∉ S := (Finset.mem_sdiff.1 hfRS).2
        have hRsub' : R ⊆ insert f (S.erase e) := by
          intro x hxR
          by_cases hxS : x ∈ S
          · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h => heR (h ▸ hxR), hxS⟩)
          · have hx_in : x ∈ ({f} : Finset E) := hf_eq ▸ Finset.mem_sdiff.2 ⟨hxR, hxS⟩
            rw [Finset.mem_singleton.1 hx_in]
            exact Finset.mem_insert_self f _
        have hcard_eq' : R.card = (insert f (S.erase e)).card := by
          have hf_not_er : f ∉ S.erase e := fun h => hfS (Finset.mem_of_mem_erase h)
          rw [Finset.card_insert_of_notMem hf_not_er, Finset.card_erase_of_mem heS,
            hequicard R hRF S hSF]
          have hSpos : 1 ≤ S.card := Finset.card_pos.2 ⟨e, heS⟩
          omega
        have hReq : R = insert f (S.erase e) := Finset.eq_of_subset_of_card_le hRsub' hcard_eq'.ge
        exact hno f (Finset.mem_sdiff.2 ⟨hfT, hfS⟩) (hReq ▸ hRF)
      calc (2 : ℝ) ≤ ((R \ S).card : ℝ) := by exact_mod_cast hRS_ge2
        _ = ∑ _x ∈ R \ S, (1 : ℝ) := by simp
        _ = ∑ x ∈ R \ S, c x := Finset.sum_congr rfl fun x hx => by
            obtain ⟨hxR, hxS⟩ := Finset.mem_sdiff.1 hx
            have hxT : x ∈ T := (Finset.mem_union.1 (hRsub hxR)).resolve_left hxS
            simp only [c, hxS, hxT, ↓reduceIte]
        _ ≤ ∑ x ∈ R, c x := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
            fun x _ _ => hc0 x
    · obtain ⟨z, hzR, hzST⟩ := Finset.not_subset.1 hRsub
      have hzS : z ∉ S := fun h => hzST (Finset.mem_union_left T h)
      have hzT : z ∉ T := fun h => hzST (Finset.mem_union_right S h)
      have hcz : c z = 2 := by simp only [c, hzS, hzT, ↓reduceIte]
      exact hcz ▸ Finset.single_le_sum (fun x _ => hc0 x) hzR
  have hdiff_ge : ((S \ T).card : ℝ) + 1 ≤ ∑ x ∈ S \ T, vcgPayOfSet F hmono c S x := by
    rw [← Finset.add_sum_erase (S \ T) _ he]
    have her_ge : (((S \ T).erase e).card : ℝ) ≤
        ∑ x ∈ (S \ T).erase e, vcgPayOfSet F hmono c S x := by
      calc (((S \ T).erase e).card : ℝ) = ∑ _x ∈ (S \ T).erase e, (1 : ℝ) := by simp
        _ ≤ ∑ x ∈ (S \ T).erase e, vcgPayOfSet F hmono c S x :=
          Finset.sum_le_sum fun x hx => hvcg_ge x (Finset.mem_of_mem_erase hx)
    have hcard_er : (((S \ T).erase e).card : ℝ) + 1 = ((S \ T).card : ℝ) := by
      rw [Finset.card_erase_of_mem he]
      have hpos : 1 ≤ (S \ T).card := Finset.card_pos.2 ⟨e, he⟩
      exact_mod_cast Nat.sub_add_cancel hpos
    linarith
  have hcard_eq_sdiff : ((T \ S).card : ℝ) = ((S \ T).card : ℝ) := by
    have h1 := Finset.card_inter_add_card_sdiff S T
    have h2 := Finset.card_inter_add_card_sdiff T S
    rw [Finset.inter_comm] at h2
    have hST := hequicard S hSF T hTF
    exact_mod_cast (by omega : (T \ S).card = (S \ T).card)
  have htot : (vcgMechanism F hF hmono).totalPay c =
      (∑ x ∈ S ∩ T, vcgPayOfSet F hmono c S x) + ∑ x ∈ S \ T, vcgPayOfSet F hmono c S x := by
    rw [(vcgMechanism F hF hmono).totalPay_eq_sum_alloc (vcgMechanism_losersPaidZero F hF hmono)
      hc0]
    simp only [vcgMechanism, huniq]
    exact (sum_inter_add_sum_sdiff S T _).symm
  have hratio := h1.2 c hc0
  rw [one_mul] at hratio
  have hcn := cheapestNash_le_of_isPayYourBidNash hF hb
  linarith

/-- **Theorem 13.53 ([HartlineKarlin2007], §13.5.1.1, p. 353):**
for any nonempty, monopoly-free antichain `(E, F)` of feasible sets, the VCG procurement mechanism
has frugality ratio `1` if and only if `F` is the set of bases of a matroid. -/
theorem vcg_hasFrugalityRatioLe_one_iff_isMatroidBaseFamily [Fintype E] [DecidableEq E]
    {F : Finset (Finset E)} (hF : F.Nonempty) (hmono : IsMonopolyFree F)
    (hanti : IsAntichain (· ⊆ ·) (F : Set (Finset E))) :
    HasFrugalityRatioLe F (vcgMechanism F hF hmono) 1 ↔ IsMatroidBaseFamily F :=
  ⟨isMatroidBaseFamily_of_vcg_hasFrugalityRatioLe_one hF hmono hanti,
    fun hmat => vcg_hasFrugalityRatioLe_one_of_isMatroidBaseFamily hmat hmono⟩

end MatroidCharacterization

/-! ### Exercise 13.12: Spanning-tree auctions -/

section SpanningTree

variable {V : Type*}

/-- The spanning subgraph of `G` formed by a subset `S` of edges of `G`. -/
@[expose] def spanningTreeSubgraph {G : SimpleGraph V} (S : Finset G.edgeSet) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Subtype.val '' (S : Set G.edgeSet))

private theorem spanningTreeSubgraph_le {G : SimpleGraph V} (S : Finset G.edgeSet) :
    spanningTreeSubgraph S ≤ G := by
  intro u v huv
  rw [spanningTreeSubgraph, SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨⟨e, heG⟩, _, heq⟩, _⟩ := huv
  exact G.mem_edgeSet.1 (heq ▸ heG)

private theorem spanningTreeSubgraph_edgeSet {G : SimpleGraph V} (S : Finset G.edgeSet) :
    (spanningTreeSubgraph S).edgeSet = Subtype.val '' (S : Set G.edgeSet) := by
  unfold spanningTreeSubgraph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, Set.mem_image, Finset.mem_coe, and_iff_left_iff_imp]
  rintro ⟨⟨e', heG⟩, _, rfl⟩
  exact G.not_isDiag_of_mem_edgeSet heG

/-- The feasible family of spanning trees of a finite simple graph `G`, represented as subsets of
its edge set `G.edgeSet` ([HartlineKarlin2007], Example 13.51, p. 351; Exercise 13.12, p. 361). -/
@[expose] noncomputable def spanningTreeFamily (G : SimpleGraph V) [Fintype G.edgeSet] :
    Finset (Finset G.edgeSet) := by
  classical
  exact Finset.univ.filter fun S => (spanningTreeSubgraph S).IsTree

theorem mem_spanningTreeFamily_iff {G : SimpleGraph V} [Fintype G.edgeSet]
    (S : Finset G.edgeSet) :
    S ∈ spanningTreeFamily G ↔ SimpleGraph.IsSpanningTree G (spanningTreeSubgraph S) := by
  classical
  simp only [spanningTreeFamily, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.IsSpanningTree, spanningTreeSubgraph_le, true_and]

private noncomputable def edgeFinsetOfSubgraph {G H : SimpleGraph V} [Fintype G.edgeSet] :
    Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun e : G.edgeSet => e.1 ∈ H.edgeSet

private theorem spanningTreeSubgraph_edgeFinsetOfSubgraph {G H : SimpleGraph V} (hHG : H ≤ G)
    [Fintype G.edgeSet] :
    spanningTreeSubgraph (edgeFinsetOfSubgraph (G := G) (H := H)) = H := by
  classical
  apply SimpleGraph.edgeSet_inj.1
  rw [spanningTreeSubgraph_edgeSet]
  ext e
  simp only [Set.mem_image, Finset.mem_coe, edgeFinsetOfSubgraph, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨e', _⟩, he'H, rfl⟩
    exact he'H
  · intro heH
    exact ⟨⟨e, SimpleGraph.edgeSet_mono hHG heH⟩, heH, rfl⟩

/-- Every finite connected simple graph has a nonempty spanning-tree family. -/
theorem spanningTreeFamily_nonempty {G : SimpleGraph V} [Fintype G.edgeSet] (hconn : G.Connected) :
    (spanningTreeFamily G).Nonempty := by
  obtain ⟨T, hTG, hT⟩ := hconn.exists_isTree_le
  refine ⟨edgeFinsetOfSubgraph (G := G) (H := T), (mem_spanningTreeFamily_iff _).2 ?_⟩
  rw [spanningTreeSubgraph_edgeFinsetOfSubgraph hTG]
  exact ⟨hTG, hT⟩

/-- A connected graph's spanning-tree family is monopoly-free if and only if `G` is bridgeless
(equivalently `G.IsEdgeConnected 2`). -/
theorem isMonopolyFree_spanningTreeFamily_iff {G : SimpleGraph V} [Fintype G.edgeSet]
    (hconn : G.Connected) :
    IsMonopolyFree (spanningTreeFamily G) ↔ ∀ e, ¬ G.IsBridge e := by
  classical
  constructor
  · intro hmono e hbr
    induction e using Sym2.ind with
    | _ u v =>
      have heG : s(u, v) ∈ G.edgeSet := G.mem_edgeSet.2 (hbr.reachable_iff_adj.1 (hconn u v))
      obtain ⟨S, hSF, heS⟩ := hmono ⟨s(u, v), heG⟩
      have hST := (mem_spanningTreeFamily_iff S).1 hSF
      have hsub : spanningTreeSubgraph S ≤ G.deleteEdges {s(u, v)} := by
        intro x y hxy
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hST.1 hxy, fun heq => heS ?_⟩
        have hmem : s(x, y) ∈ (spanningTreeSubgraph S).edgeSet :=
          (spanningTreeSubgraph S).mem_edgeSet.2 hxy
        rw [spanningTreeSubgraph_edgeSet] at hmem
        obtain ⟨e', he'S, he'eq⟩ := hmem
        have : e' = ⟨s(u, v), heG⟩ := Subtype.ext (he'eq.trans heq)
        exact this ▸ he'S
      exact (SimpleGraph.isBridge_iff.1 hbr) ((hST.2.connected u v).mono hsub)
  · intro hnobridge e
    have hconn' : (G.deleteEdges {e.1}).Connected :=
      hconn.preconnected.connected_deleteEdges_of_not_isBridge (hnobridge e.1)
    obtain ⟨T, hTle, hTree⟩ := hconn'.exists_isTree_le
    have hTG : T ≤ G := hTle.trans (SimpleGraph.deleteEdges_le _)
    refine ⟨edgeFinsetOfSubgraph (G := G) (H := T), (mem_spanningTreeFamily_iff _).2 ?_, ?_⟩
    · rw [spanningTreeSubgraph_edgeFinsetOfSubgraph hTG]
      exact ⟨hTG, hTree⟩
    · simp only [edgeFinsetOfSubgraph, Finset.mem_filter, Finset.mem_univ, true_and]
      intro heT
      have hmem := SimpleGraph.edgeSet_mono hTle heT
      rw [SimpleGraph.edgeSet_deleteEdges] at hmem
      exact hmem.2 rfl

/-- **Graphic matroid base property:** for any finite connected simple graph `G`, the spanning
trees of `G` form a matroid base family. -/
theorem spanningTreeFamily_isMatroidBaseFamily [Finite V] {G : SimpleGraph V} [Fintype G.edgeSet]
    [DecidableEq G.edgeSet] (hconn : G.Connected) :
    IsMatroidBaseFamily (spanningTreeFamily G) := by
  have := Fintype.ofFinite V
  classical
  refine ⟨spanningTreeFamily_nonempty hconn, fun S₁ hS₁ S₂ hS₂ e he => ?_⟩
  obtain ⟨he₁, he₂⟩ := Finset.mem_sdiff.1 he
  set T₁ := spanningTreeSubgraph S₁
  set T₂ := spanningTreeSubgraph S₂
  have hT₁ : SimpleGraph.IsSpanningTree G T₁ := (mem_spanningTreeFamily_iff S₁).1 hS₁
  have hT₂ : SimpleGraph.IsSpanningTree G T₂ := (mem_spanningTreeFamily_iff S₂).1 hS₂
  have heT₁ : e.1 ∈ T₁.edgeSet := by
    rw [spanningTreeSubgraph_edgeSet]; exact ⟨e, he₁, rfl⟩
  have heT₂ : e.1 ∉ T₂.edgeSet := by
    rw [spanningTreeSubgraph_edgeSet]
    rintro ⟨e', he'S₂, he'eq⟩
    have : e' = e := Subtype.ext he'eq
    exact he₂ (this ▸ he'S₂)
  rcases e with ⟨e₀, he₀G⟩
  induction e₀ using Sym2.ind with
  | _ u v =>
    set T₁' := T₁.deleteEdges {s(u, v)}
    have hbridge : T₁.IsBridge s(u, v) :=
      SimpleGraph.isAcyclic_iff_forall_isBridge.1 hT₁.2.isAcyclic heT₁
    have hnotReach : ¬ T₁'.Reachable u v := SimpleGraph.isBridge_iff.1 hbridge
    let C : Finset V := Finset.univ.filter fun w => T₁'.Reachable u w
    have huC : u ∈ C := Finset.mem_filter.2 ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl u⟩
    have hvC : v ∉ C := fun hv => hnotReach (Finset.mem_filter.1 hv).2
    have hCproper : C ≠ Finset.univ := fun hEq => hvC (hEq ▸ Finset.mem_univ v)
    obtain ⟨f₀, hf₀T₂, a, haC, b, hbC, rfl⟩ :=
      SimpleGraph.exists_isOutgoingEdge hT₂.2.connected ⟨u, huC⟩ hCproper
    have hf₀G : s(a, b) ∈ G.edgeSet := SimpleGraph.edgeSet_mono hT₂.1 hf₀T₂
    let f : G.edgeSet := ⟨s(a, b), hf₀G⟩
    have hfS₂ : f ∈ S₂ := by
      have hf₀T₂' : s(a, b) ∈ T₂.edgeSet := hf₀T₂
      rw [spanningTreeSubgraph_edgeSet] at hf₀T₂'
      obtain ⟨f', hf'S₂, hf'eq⟩ := hf₀T₂'
      have hEq : f' = f := Subtype.ext hf'eq
      exact hEq ▸ hf'S₂
    have hf_not_T₁ : s(a, b) ∉ T₁.edgeSet := by
      intro hfT₁
      have hne_ef : s(a, b) ≠ s(u, v) := fun hEq =>
        heT₂ (show s(u, v) ∈ T₂.edgeSet from hEq ▸ hf₀T₂)
      have hadj' : T₁'.Adj a b := (SimpleGraph.deleteEdges_adj).2 ⟨T₁.mem_edgeSet.1 hfT₁, hne_ef⟩
      exact hbC (Finset.mem_filter.2 ⟨Finset.mem_univ _,
        (Finset.mem_filter.1 haC).2.trans hadj'.reachable⟩)
    have hfS₁ : f ∉ S₁ := fun hf₁ => hf_not_T₁ (by
      rw [spanningTreeSubgraph_edgeSet]; exact ⟨f, hf₁, rfl⟩)
    refine ⟨f, Finset.mem_sdiff.2 ⟨hfS₂, hfS₁⟩, (mem_spanningTreeFamily_iff _).2 ?_⟩
    set S₃ := insert f (S₁.erase ⟨s(u, v), he₀G⟩)
    set T₃ := spanningTreeSubgraph S₃
    have hT₃_eq : T₃ = T₁' ⊔ SimpleGraph.edge a b := by
      apply SimpleGraph.edgeSet_inj.1
      have hab : a ≠ b := (T₂.mem_edgeSet.1 hf₀T₂).ne
      rw [spanningTreeSubgraph_edgeSet, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges,
        SimpleGraph.edgeSet_edge, spanningTreeSubgraph_edgeSet]
      ext z
      simp only [S₃, Finset.coe_insert, Finset.coe_erase, Set.image_insert_eq, Set.mem_insert_iff,
        Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_union]
      constructor
      · rintro (rfl | ⟨x, ⟨hx₁, hxne⟩, rfl⟩)
        · exact Or.inr ⟨rfl, by simpa [f] using hab⟩
        · exact Or.inl ⟨⟨x, hx₁, rfl⟩, fun hEq => hxne (Subtype.ext hEq)⟩
      · rintro (⟨⟨x, hx₁, rfl⟩, hne⟩ | ⟨rfl, _⟩)
        · exact Or.inr ⟨x, ⟨hx₁, fun hEq => hne (congrArg Subtype.val hEq)⟩, rfl⟩
        · exact Or.inl rfl
    have hreach_uv : ∀ w : V, T₁'.Reachable u w ∨ T₁'.Reachable v w := by
      intro w
      obtain ⟨p⟩ := hT₁.2.connected u w
      have haux : ∀ {x y : V} (q : T₁.Walk x y),
          (T₁'.Reachable u x ∨ T₁'.Reachable v x) →
          (T₁'.Reachable u y ∨ T₁'.Reachable v y) := by
        intro x y q
        induction q with
        | nil => exact id
        | @cons x₁ x₂ x₃ hstep q ih =>
          intro hstart
          apply ih
          by_cases hEq : s(x₁, x₂) = s(u, v)
          · rcases Sym2.eq_iff.1 hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr (SimpleGraph.Reachable.refl _)
            · exact Or.inl (SimpleGraph.Reachable.refl _)
          · have hadj' : T₁'.Adj x₁ x₂ := (SimpleGraph.deleteEdges_adj).2 ⟨hstep, hEq⟩
            exact hstart.imp (fun h => h.trans hadj'.reachable) (fun h => h.trans hadj'.reachable)
      exact haux p (Or.inl (SimpleGraph.Reachable.refl u))
    have hT₃_conn : T₃.Connected := by
      have : Nonempty V := hconn.nonempty
      rw [hT₃_eq]
      have hvb : T₁'.Reachable v b := (hreach_uv b).resolve_left fun hub =>
        hbC (Finset.mem_filter.2 ⟨Finset.mem_univ _, hub⟩)
      have hab_adj : (T₁' ⊔ SimpleGraph.edge a b).Adj a b :=
        Or.inr ((SimpleGraph.edge_adj a b a b).2
          ⟨Or.inl ⟨rfl, rfl⟩, (T₂.mem_edgeSet.1 hf₀T₂).ne⟩)
      have huv_T₃ : (T₁' ⊔ SimpleGraph.edge a b).Reachable u v :=
        ((Finset.mem_filter.1 haC).2.mono le_sup_left).trans
          (hab_adj.reachable.trans (hvb.symm.mono le_sup_left))
      have hall : ∀ w : V, (T₁' ⊔ SimpleGraph.edge a b).Reachable u w := fun w =>
        (hreach_uv w).elim (fun h => h.mono le_sup_left)
          (fun h => huv_T₃.trans (h.mono le_sup_left))
      exact ⟨fun x y => (hall x).symm.trans (hall y)⟩
    have hT₃_card : T₃.edgeFinset.card + 1 = Fintype.card V := by
      have hcard_fn : ∀ S : Finset G.edgeSet,
          (spanningTreeSubgraph S).edgeFinset.card = S.card := by
        intro S
        have hEq : (spanningTreeSubgraph S).edgeFinset = S.image Subtype.val := by
          ext z
          simp only [SimpleGraph.mem_edgeFinset, spanningTreeSubgraph_edgeSet, Finset.mem_image,
            Set.mem_image, Finset.mem_coe]
        rw [hEq, Finset.card_image_of_injective _ Subtype.val_injective]
      rw [hcard_fn S₃]
      have hf_not_er : f ∉ S₁.erase ⟨s(u, v), he₀G⟩ := fun h => hfS₁ (Finset.mem_of_mem_erase h)
      have hS₃card : S₃.card = S₁.card := by
        rw [Finset.card_insert_of_notMem hf_not_er, Finset.card_erase_of_mem he₁,
          Nat.sub_add_cancel (Finset.card_pos.2 ⟨_, he₁⟩)]
      rw [hS₃card, ← hcard_fn S₁, hT₁.2.card_edgeFinset]
    refine ⟨spanningTreeSubgraph_le S₃, ?_⟩
    rw [SimpleGraph.isTree_iff_connected_and_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    exact ⟨hT₃_conn, hT₃_card⟩

/-- **Exercise 13.12 ([HartlineKarlin2007], p. 361; Example 13.51, p. 351):**
for any finite connected bridgeless simple graph `G`, the VCG spanning-tree auction has total
payment equal to `cheapestNash` on every cost profile `c` and hence achieves frugality ratio `1`. -/
theorem vcg_spanningTree_totalPay_eq_cheapestNash [Finite V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq G.edgeSet] (hconn : G.Connected)
    (hnobridge : ∀ e, ¬ G.IsBridge e) (c : G.edgeSet → ℝ) :
    (vcgMechanism (spanningTreeFamily G) (spanningTreeFamily_nonempty hconn)
      ((isMonopolyFree_spanningTreeFamily_iff hconn).2 hnobridge)).totalPay c =
      cheapestNash (spanningTreeFamily G) c :=
  vcgTotalPay_eq_cheapestNash_of_isMatroidBaseFamily
    (spanningTreeFamily_isMatroidBaseFamily hconn)
    ((isMonopolyFree_spanningTreeFamily_iff hconn).2 hnobridge) c

/-- **Exercise 13.12 ([HartlineKarlin2007], p. 361):** VCG has frugality ratio `1` for
spanning-tree auctions on every finite connected bridgeless (equivalently `2`-edge-connected)
simple graph. -/
theorem vcg_spanningTree_hasFrugalityRatioLe_one [Finite V] {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq G.edgeSet] (hconn : G.Connected)
    (hnobridge : ∀ e, ¬ G.IsBridge e) :
    HasFrugalityRatioLe (spanningTreeFamily G)
      (vcgMechanism (spanningTreeFamily G) (spanningTreeFamily_nonempty hconn)
        ((isMonopolyFree_spanningTreeFamily_iff hconn).2 hnobridge)) 1 :=
  vcg_hasFrugalityRatioLe_one_of_isMatroidBaseFamily
    (spanningTreeFamily_isMatroidBaseFamily hconn)
    ((isMonopolyFree_spanningTreeFamily_iff hconn).2 hnobridge)

end SpanningTree

/-! ### Theorem 13.54 and the `√(|P||P'|)`-frugal weighted path mechanism -/

section TwoDisjointPaths

/-- The first (`n`-edge) path in the two-disjoint-paths set system on `Fin n ⊕ Fin n'`. -/
@[expose] def leftPath (n n' : ℕ) : Finset (Fin n ⊕ Fin n') :=
  Finset.univ.map Function.Embedding.inl

/-- The second (`n'`-edge) path in the two-disjoint-paths set system on `Fin n ⊕ Fin n'`. -/
@[expose] def rightPath (n n' : ℕ) : Finset (Fin n ⊕ Fin n') :=
  Finset.univ.map Function.Embedding.inr

/-- Set system of two vertex-disjoint `s`-`t` paths `P` (`|P| = n`) and `P'` (`|P'| = n'`)
([HartlineKarlin2007], §13.5, pp. 351, 353–354). -/
@[expose] def twoDisjointPaths (n n' : ℕ) : Finset (Finset (Fin n ⊕ Fin n')) :=
  {leftPath n n', rightPath n n'}

@[simp]
theorem mem_leftPath_inl (n n' : ℕ) (i : Fin n) : Sum.inl i ∈ leftPath n n' := by
  simp [leftPath]

@[simp]
theorem notMem_leftPath_inr (n n' : ℕ) (j : Fin n') : Sum.inr j ∉ leftPath n n' := by
  simp [leftPath]

@[simp]
theorem mem_rightPath_inr (n n' : ℕ) (j : Fin n') : Sum.inr j ∈ rightPath n n' := by
  simp [rightPath]

@[simp]
theorem notMem_rightPath_inl (n n' : ℕ) (i : Fin n) : Sum.inl i ∉ rightPath n n' := by
  simp [rightPath]

theorem sum_leftPath (n n' : ℕ) (c : Fin n ⊕ Fin n' → ℝ) :
    ∑ e ∈ leftPath n n', c e = ∑ i : Fin n, c (Sum.inl i) := by
  simp [leftPath]

theorem sum_rightPath (n n' : ℕ) (c : Fin n ⊕ Fin n' → ℝ) :
    ∑ e ∈ rightPath n n', c e = ∑ j : Fin n', c (Sum.inr j) := by
  simp [rightPath]

private theorem leftPath_ne_rightPath {n n' : ℕ} (hn : 0 < n) :
    leftPath n n' ≠ rightPath n n' := fun h =>
  notMem_rightPath_inl n n' ⟨0, hn⟩ (h ▸ mem_leftPath_inl n n' ⟨0, hn⟩)

theorem twoDisjointPaths_nonempty (n n' : ℕ) : (twoDisjointPaths n n').Nonempty :=
  ⟨leftPath n n', by simp [twoDisjointPaths]⟩

theorem twoDisjointPaths_isMonopolyFree (n n' : ℕ) :
    IsMonopolyFree (twoDisjointPaths n n') := by
  rintro (i | j)
  · exact ⟨rightPath n n', by simp [twoDisjointPaths], notMem_rightPath_inl n n' i⟩
  · exact ⟨leftPath n n', by simp [twoDisjointPaths], notMem_leftPath_inr n n' j⟩

theorem twoDisjointPaths_isAntichain {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n') :
    IsAntichain (· ⊆ ·) (twoDisjointPaths n n' : Set (Finset (Fin n ⊕ Fin n'))) := by
  intro S hS T hT hne hsub
  simp only [Finset.mem_coe, twoDisjointPaths, Finset.mem_insert, Finset.mem_singleton] at hS hT
  rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
  · exact hne rfl
  · exact notMem_rightPath_inl n n' ⟨0, hn⟩ (hsub (mem_leftPath_inl n n' ⟨0, hn⟩))
  · exact notMem_leftPath_inr n n' ⟨0, hn'⟩ (hsub (mem_rightPath_inr n n' ⟨0, hn'⟩))
  · exact hne rfl

/-- On two vertex-disjoint nonempty paths, the cheapest Nash benchmark `N(c)` equals the larger of
the two path costs (the second-cheapest path cost, [HartlineKarlin2007], §13.5.1, p. 352). -/
theorem cheapestNash_twoDisjointPaths {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n')
    (c : Fin n ⊕ Fin n' → ℝ) :
    cheapestNash (twoDisjointPaths n n') c =
      max (∑ i : Fin n, c (Sum.inl i)) (∑ j : Fin n', c (Sum.inr j)) := by
  have hne_lr : leftPath n n' ≠ rightPath n n' := leftPath_ne_rightPath hn
  have hdisj : (twoDisjointPaths n n' : Set (Finset (Fin n ⊕ Fin n'))).PairwiseDisjoint id := by
    intro S hS T hT hne
    simp only [Finset.mem_coe, twoDisjointPaths, Finset.mem_insert, Finset.mem_singleton] at hS hT
    rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
    · exact absurd rfl hne
    · exact Finset.disjoint_left.2 fun x hx => by
        rcases x with i | j
        · exact notMem_rightPath_inl n n' i
        · exact absurd hx (notMem_leftPath_inr n n' j)
    · exact Finset.disjoint_left.2 fun x hx => by
        rcases x with i | j
        · exact absurd hx (notMem_rightPath_inl n n' i)
        · exact notMem_leftPath_inr n n' j
    · exact absurd rfl hne
  have hne_sets : ∀ S ∈ twoDisjointPaths n n', S.Nonempty := by
    intro S hS
    simp only [twoDisjointPaths, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · exact ⟨Sum.inl ⟨0, hn⟩, mem_leftPath_inl n n' _⟩
    · exact ⟨Sum.inr ⟨0, hn'⟩, mem_rightPath_inr n n' _⟩
  have hcard : 2 ≤ (twoDisjointPaths n n').card := by
    rw [twoDisjointPaths, Finset.card_pair hne_lr]
  by_cases hle : ∑ i : Fin n, c (Sum.inl i) ≤ ∑ j : Fin n', c (Sum.inr j)
  · have hmin : IsMinCostSet (twoDisjointPaths n n') c (leftPath n n') := by
      refine ⟨by simp [twoDisjointPaths], fun T hT => ?_⟩
      simp only [twoDisjointPaths, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · exact le_rfl
      · simpa only [sum_leftPath, sum_rightPath] using hle
    rw [cheapestNash_of_pairwiseDisjoint hdisj hne_sets hcard c hmin, max_eq_right hle]
    have her : (twoDisjointPaths n n').erase (leftPath n n') = {rightPath n n'} := by
      ext T
      simp only [twoDisjointPaths, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨h1, h2⟩ => h2.resolve_left h1, fun h => ⟨h ▸ hne_lr.symm, Or.inr h⟩⟩
    simp only [her, Finset.inf'_singleton, sum_rightPath]
  · push Not at hle
    have hmin : IsMinCostSet (twoDisjointPaths n n') c (rightPath n n') := by
      refine ⟨by simp [twoDisjointPaths], fun T hT => ?_⟩
      simp only [twoDisjointPaths, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · simpa only [sum_leftPath, sum_rightPath] using hle.le
      · exact le_rfl
    rw [cheapestNash_of_pairwiseDisjoint hdisj hne_sets hcard c hmin, max_eq_left hle.le]
    have her : (twoDisjointPaths n n').erase (rightPath n n') = {leftPath n n'} := by
      ext T
      simp only [twoDisjointPaths, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨h1, h2⟩ => h2.resolve_right h1, fun h => ⟨h ▸ hne_lr, Or.inl h⟩⟩
    simp only [her, Finset.inf'_singleton, sum_leftPath]

/-- **VCG overpayment on two vertex-disjoint paths ([HartlineKarlin2007], §13.5, p. 351):**
when every edge on `P` (`|P| = n`) has cost `0` and every edge on `P'` (`|P'| = n' ≥ 1`) has cost
`1`, VCG purchases `P` and pays each of its `n` edges `n'`, for a total payment of `n * n'`,
whereas `cheapestNash = n'`. When `n = n'`, VCG pays `n^2` against benchmark `n`. -/
theorem vcgTotalPay_twoDisjointPaths_zero_one {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n') :
    let c : Fin n ⊕ Fin n' → ℝ := Sum.elim (fun _ => 0) (fun _ => 1)
    (vcgMechanism (twoDisjointPaths n n') (twoDisjointPaths_nonempty n n')
        (twoDisjointPaths_isMonopolyFree n n')).totalPay c = (n : ℝ) * (n' : ℝ) ∧
      cheapestNash (twoDisjointPaths n n') c = (n' : ℝ) := by
  intro c
  have hc0 : 0 ≤ c := fun x => by cases x <;> norm_num [c]
  have hcL : ∑ e ∈ leftPath n n', c e = 0 := by simp [sum_leftPath, c]
  have hcR : ∑ e ∈ rightPath n n', c e = (n' : ℝ) := by simp [sum_rightPath, c]
  have halloc : vcgAlloc (twoDisjointPaths n n') (twoDisjointPaths_nonempty n n') c =
      leftPath n n' := by
    set A := vcgAlloc (twoDisjointPaths n n') (twoDisjointPaths_nonempty n n') c
    have hA : IsMinCostSet (twoDisjointPaths n n') c A :=
      vcgAlloc_isMinCostSet (twoDisjointPaths n n') (twoDisjointPaths_nonempty n n') c
    have hmem := hA.1
    simp only [twoDisjointPaths, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact h
    · exfalso
      have hle := hA.2 (leftPath n n') (by simp [twoDisjointPaths])
      rw [h, hcR, hcL] at hle
      have : (0 : ℝ) < (n' : ℝ) := Nat.cast_pos.2 hn'
      linarith
  constructor
  · rw [(vcgMechanism _ _ _).totalPay_eq_sum_alloc (vcgMechanism_losersPaidZero _ _ _) hc0]
    simp only [vcgMechanism, halloc, sum_leftPath]
    have hpay : ∀ i : Fin n,
        vcgPayOfSet (twoDisjointPaths n n') (twoDisjointPaths_isMonopolyFree n n') c
          (leftPath n n') (Sum.inl i) = (n' : ℝ) := by
      intro i
      unfold vcgPayOfSet
      have hfilt : (twoDisjointPaths n n').filter (fun T => Sum.inl i ∉ T) = {rightPath n n'} := by
        ext T
        simp only [twoDisjointPaths, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hnot⟩
          · exact absurd (mem_leftPath_inl n n' i) hnot
          · rfl
        · rintro rfl
          exact ⟨Or.inr rfl, notMem_rightPath_inl n n' i⟩
      have her0 : ∑ x ∈ (leftPath n n').erase (Sum.inl i), c x = 0 :=
        Finset.sum_eq_zero fun x hx => by
          have hxL := Finset.mem_of_mem_erase hx
          rcases x with i' | j'
          · rfl
          · exact absurd hxL (notMem_leftPath_inr n n' j')
      rw [Finset.inf'_congr _ hfilt (fun _ _ => rfl), Finset.inf'_singleton, hcR, her0, sub_zero]
    simp only [hpay, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · rw [cheapestNash_twoDisjointPaths hn hn' c]
    simp only [c, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact max_eq_right (Nat.cast_nonneg n')

/-- **Theorem 13.54 ([HartlineKarlin2007], §13.5.1.1, p. 353):**
for two vertex-disjoint paths of lengths `n ≥ 1` and `n' ≥ 1`, every deterministic DSIC,
individually rational, losers-paid-zero procurement mechanism `M` admits a nonnegative cost profile
`c` with `0 < cheapestNash (twoDisjointPaths n n') c` on which
`M.totalPay c ≥ (1 / 2) * √(n * n') * cheapestNash (twoDisjointPaths n n') c`. -/
theorem twoDisjointPaths_frugality_lower_bound {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n')
    (M : ProcurementMechanism (Fin n ⊕ Fin n') (twoDisjointPaths n n'))
    (hDSIC : M.IsDSIC) (hIR : M.IsIR) (hZ : M.LosersPaidZero) :
    ∃ c : Fin n ⊕ Fin n' → ℝ, 0 ≤ c ∧
      0 < cheapestNash (twoDisjointPaths n n') c ∧
      (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * (n' : ℝ)) * cheapestNash (twoDisjointPaths n n') c ≤
        M.totalPay c := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hn'R : (0 : ℝ) < (n' : ℝ) := Nat.cast_pos.2 hn'
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsn' : (0 : ℝ) < Real.sqrt (n' : ℝ) := Real.sqrt_pos.2 hn'R
  let prof : Fin n → Fin n' → (Fin n ⊕ Fin n' → ℝ) := fun i j =>
    Sum.elim (fun i' => if i' = i then 1 / Real.sqrt (n : ℝ) else 0)
      (fun j' => if j' = j then 1 / Real.sqrt (n' : ℝ) else 0)
  let outL : Fin n → Finset (Fin n') := fun i =>
    Finset.univ.filter fun j => M.alloc (prof i j) = rightPath n n'
  let outR : Fin n' → Finset (Fin n) := fun j =>
    Finset.univ.filter fun i => M.alloc (prof i j) = leftPath n n'
  have hcount :
      (∑ i : Fin n, ((outL i).card : ℝ)) + ∑ j : Fin n', ((outR j).card : ℝ) ≥
        (n : ℝ) * (n' : ℝ) := by
    have h1 : ∑ i : Fin n, ((outL i).card : ℝ) =
        ∑ i : Fin n, ∑ j : Fin n', if M.alloc (prof i j) = rightPath n n' then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl fun i _ => by simp [outL]
    have h2 : ∑ j : Fin n', ((outR j).card : ℝ) =
        ∑ i : Fin n, ∑ j : Fin n', if M.alloc (prof i j) = leftPath n n' then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by simp [outR]
    rw [h1, h2, ← Finset.sum_add_distrib]
    calc (n : ℝ) * (n' : ℝ) = ∑ _i : Fin n, ∑ _j : Fin n', (1 : ℝ) := by simp
      _ ≤ ∑ i : Fin n,
          ((∑ j : Fin n', if M.alloc (prof i j) = rightPath n n' then (1 : ℝ) else 0) +
            ∑ j : Fin n', if M.alloc (prof i j) = leftPath n n' then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ => ?_
        have hmem := M.alloc_mem (prof i j)
        simp only [twoDisjointPaths, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with hL | hR
        · simp only [hL, ↓reduceIte]
          split_ifs <;> norm_num
        · simp only [hR, ↓reduceIte]
          split_ifs <;> norm_num
  have hsplit : (n : ℝ) * (n' : ℝ) / 2 ≤ ∑ i : Fin n, ((outL i).card : ℝ) ∨
      (n : ℝ) * (n' : ℝ) / 2 ≤ ∑ j : Fin n', ((outR j).card : ℝ) := by
    by_contra h
    push Not at h
    linarith
  rcases hsplit with hLcase | hRcase
  · obtain ⟨i, _, hi_deg⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin n)))
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (f := fun _ => (n' : ℝ) / 2)
      (g := fun i => ((outL i).card : ℝ)) (by simp; linarith)
    let c : Fin n ⊕ Fin n' → ℝ :=
      Sum.elim (fun i' => if i' = i then 1 / Real.sqrt (n : ℝ) else 0) (fun _ => 0)
    have hc0 : 0 ≤ c := fun x => by
      cases x with
      | inl i' => simp only [Pi.zero_apply, c, Sum.elim_inl]; split_ifs <;> positivity
      | inr j' => simp [c]
    have hcn : cheapestNash (twoDisjointPaths n n') c = 1 / Real.sqrt (n : ℝ) := by
      rw [cheapestNash_twoDisjointPaths hn hn' c]
      simp only [c, Sum.elim_inl, Sum.elim_inr, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        Finset.sum_const_zero]
      exact max_eq_left (by positivity)
    refine ⟨c, hc0, hcn ▸ by positivity, ?_⟩
    have hupd : ∀ j : Fin n',
        Function.update c (Sum.inr j) (1 / Real.sqrt (n' : ℝ)) = prof i j := by
      intro j
      ext x
      cases x with
      | inl i' => simp [c, prof]
      | inr j' =>
        by_cases hjj : j' = j
        · subst hjj; simp [prof]
        · simp [c, prof, hjj]
    have hpay_ge : ∀ j ∈ outL i, 1 / Real.sqrt (n' : ℝ) ≤ M.pay c (Sum.inr j) := by
      intro j hj
      have hwin_j :
          Sum.inr j ∈ M.alloc (Function.update c (Sum.inr j) (1 / Real.sqrt (n' : ℝ))) := by
        rw [hupd j, (Finset.mem_filter.1 hj).2]
        exact mem_rightPath_inr n n' j
      have hwin_0 : Sum.inr j ∈ M.alloc (Function.update c (Sum.inr j) 0) :=
        hDSIC.antitone_alloc hc0 le_rfl (by positivity) hwin_j
      have hle := hDSIC.le_pay_of_mem_alloc_update hIR hc0 le_rfl (by positivity) hwin_0 hwin_j
      have hceq : Function.update c (Sum.inr j) 0 = c := by
        simpa only [c, Sum.elim_inr] using Function.update_eq_self (Sum.inr j) c
      rwa [hceq] at hle
    have htot_ge : ((outL i).card : ℝ) * (1 / Real.sqrt (n' : ℝ)) ≤ M.totalPay c := by
      unfold ProcurementMechanism.totalPay
      calc ((outL i).card : ℝ) * (1 / Real.sqrt (n' : ℝ))
          = ∑ _j ∈ outL i, (1 / Real.sqrt (n' : ℝ)) := by simp
        _ ≤ ∑ j ∈ outL i, M.pay c (Sum.inr j) := Finset.sum_le_sum hpay_ge
        _ = ∑ e ∈ (outL i).map Function.Embedding.inr, M.pay c e := by simp
        _ ≤ ∑ e : Fin n ⊕ Fin n', M.pay c e :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun e _ _ =>
              M.pay_nonneg hIR hZ hc0 e
    have hmul : (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * (n' : ℝ)) * (1 / Real.sqrt (n : ℝ)) =
        ((n' : ℝ) / 2) * (1 / Real.sqrt (n' : ℝ)) := by
      rw [Real.sqrt_mul hnR.le]
      have hsq : Real.sqrt (n' : ℝ) * Real.sqrt (n' : ℝ) = (n' : ℝ) := Real.mul_self_sqrt hn'R.le
      field_simp [hsn.ne', hsn'.ne']
      linarith
    rw [hcn, hmul]
    exact (mul_le_mul_of_nonneg_right hi_deg (by positivity)).trans htot_ge
  · obtain ⟨j, _, hj_deg⟩ := Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Fin n')))
      ⟨⟨0, hn'⟩, Finset.mem_univ _⟩ (f := fun _ => (n : ℝ) / 2)
      (g := fun j => ((outR j).card : ℝ)) (by simp; linarith)
    let c : Fin n ⊕ Fin n' → ℝ :=
      Sum.elim (fun _ => 0) (fun j' => if j' = j then 1 / Real.sqrt (n' : ℝ) else 0)
    have hc0 : 0 ≤ c := fun x => by
      cases x with
      | inl i' => simp [c]
      | inr j' => simp only [Pi.zero_apply, c, Sum.elim_inr]; split_ifs <;> positivity
    have hcn : cheapestNash (twoDisjointPaths n n') c = 1 / Real.sqrt (n' : ℝ) := by
      rw [cheapestNash_twoDisjointPaths hn hn' c]
      simp only [c, Sum.elim_inl, Sum.elim_inr, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        Finset.sum_const_zero]
      exact max_eq_right (by positivity)
    refine ⟨c, hc0, hcn ▸ by positivity, ?_⟩
    have hupd : ∀ i : Fin n, Function.update c (Sum.inl i) (1 / Real.sqrt (n : ℝ)) = prof i j := by
      intro i
      ext x
      cases x with
      | inl i' =>
        by_cases hii : i' = i
        · subst hii; simp [prof]
        · simp [c, prof, hii]
      | inr j' => simp [c, prof]
    have hpay_ge : ∀ i ∈ outR j, 1 / Real.sqrt (n : ℝ) ≤ M.pay c (Sum.inl i) := by
      intro i hi
      have hwin_i :
          Sum.inl i ∈ M.alloc (Function.update c (Sum.inl i) (1 / Real.sqrt (n : ℝ))) := by
        rw [hupd i, (Finset.mem_filter.1 hi).2]
        exact mem_leftPath_inl n n' i
      have hwin_0 : Sum.inl i ∈ M.alloc (Function.update c (Sum.inl i) 0) :=
        hDSIC.antitone_alloc hc0 le_rfl (by positivity) hwin_i
      have hle := hDSIC.le_pay_of_mem_alloc_update hIR hc0 le_rfl (by positivity) hwin_0 hwin_i
      have hceq : Function.update c (Sum.inl i) 0 = c := by
        simpa only [c, Sum.elim_inl] using Function.update_eq_self (Sum.inl i) c
      rwa [hceq] at hle
    have htot_ge : ((outR j).card : ℝ) * (1 / Real.sqrt (n : ℝ)) ≤ M.totalPay c := by
      unfold ProcurementMechanism.totalPay
      calc ((outR j).card : ℝ) * (1 / Real.sqrt (n : ℝ))
          = ∑ _i ∈ outR j, (1 / Real.sqrt (n : ℝ)) := by simp
        _ ≤ ∑ i ∈ outR j, M.pay c (Sum.inl i) := Finset.sum_le_sum hpay_ge
        _ = ∑ e ∈ (outR j).map Function.Embedding.inl, M.pay c e := by simp
        _ ≤ ∑ e : Fin n ⊕ Fin n', M.pay c e :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun e _ _ =>
              M.pay_nonneg hIR hZ hc0 e
    have hmul : (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * (n' : ℝ)) * (1 / Real.sqrt (n' : ℝ)) =
        ((n : ℝ) / 2) * (1 / Real.sqrt (n : ℝ)) := by
      rw [Real.sqrt_mul hnR.le]
      have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hnR.le
      field_simp [hsn.ne', hsn'.ne']
      linarith
    rw [hcn, hmul]
    exact (mul_le_mul_of_nonneg_right hj_deg (by positivity)).trans htot_ge

/-- Corollary of Theorem 13.54: any frugality ratio upper bound `ρ` for a deterministic DSIC, IR,
losers-paid-zero procurement mechanism on `twoDisjointPaths n n'` satisfies
`(1 / 2) * √(n * n') ≤ ρ`. -/
theorem le_of_hasFrugalityRatioLe_twoDisjointPaths {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n')
    {M : ProcurementMechanism (Fin n ⊕ Fin n') (twoDisjointPaths n n')}
    (hDSIC : M.IsDSIC) (hIR : M.IsIR) (hZ : M.LosersPaidZero) {ρ : ℝ}
    (hρ : HasFrugalityRatioLe (twoDisjointPaths n n') M ρ) :
    (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * (n' : ℝ)) ≤ ρ := by
  obtain ⟨c, hc0, hpos, hge⟩ := twoDisjointPaths_frugality_lower_bound hn hn' M hDSIC hIR hZ
  have hle := hρ.2 c hc0
  exact le_of_mul_le_mul_right (hge.trans hle) hpos

/-- **Near-optimal `√(|P||P'|)`-frugal weighted path mechanism ([HartlineKarlin2007], §13.5.1.1,
p. 354):** selects `leftPath n n'` when `√n · c(P) ≤ √n' · c(P')` and `rightPath n n'` otherwise,
paying each winning edge its critical threshold bid. -/
@[expose] noncomputable def sqrtWeightedPathMechanism (n n' : ℕ) :
    ProcurementMechanism (Fin n ⊕ Fin n') (twoDisjointPaths n n') where
  alloc b :=
    if Real.sqrt (n : ℝ) * (∑ i : Fin n, b (Sum.inl i)) ≤
        Real.sqrt (n' : ℝ) * (∑ j : Fin n', b (Sum.inr j)) then
      leftPath n n'
    else
      rightPath n n'
  alloc_mem b := by
    split_ifs <;> simp [twoDisjointPaths]
  pay b e :=
    if Real.sqrt (n : ℝ) * (∑ i : Fin n, b (Sum.inl i)) ≤
        Real.sqrt (n' : ℝ) * (∑ j : Fin n', b (Sum.inr j)) then
      match e with
      | Sum.inl i =>
          (Real.sqrt (n' : ℝ) / Real.sqrt (n : ℝ)) * (∑ j : Fin n', b (Sum.inr j)) -
            ∑ i' ∈ Finset.univ.erase i, b (Sum.inl i')
      | Sum.inr _ => 0
    else
      match e with
      | Sum.inl _ => 0
      | Sum.inr j =>
          (Real.sqrt (n : ℝ) / Real.sqrt (n' : ℝ)) * (∑ i : Fin n, b (Sum.inl i)) -
            ∑ j' ∈ Finset.univ.erase j, b (Sum.inr j')

theorem sqrtWeightedPathMechanism_losersPaidZero (n n' : ℕ) :
    (sqrtWeightedPathMechanism n n').LosersPaidZero := by
  intro b _ e he
  simp only [sqrtWeightedPathMechanism] at he ⊢
  split_ifs at he ⊢
  · cases e with
    | inl i => exact absurd (mem_leftPath_inl n n' i) he
    | inr j => rfl
  · cases e with
    | inl i => rfl
    | inr j => exact absurd (mem_rightPath_inr n n' j) he

theorem sqrtWeightedPathMechanism_isIR {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n') :
    (sqrtWeightedPathMechanism n n').IsIR := by
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have hsn' : (0 : ℝ) < Real.sqrt (n' : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn')
  intro e b _
  by_cases hle : Real.sqrt (n : ℝ) * (∑ i : Fin n, b (Sum.inl i)) ≤
      Real.sqrt (n' : ℝ) * (∑ j : Fin n', b (Sum.inr j))
  · simp only [ProcurementMechanism.utility, sqrtWeightedPathMechanism, hle, ↓reduceIte]
    cases e with
    | inl i =>
      simp only [mem_leftPath_inl, ↓reduceIte]
      have hdiv : ∑ k : Fin n, b (Sum.inl k) ≤
          (Real.sqrt (n' : ℝ) / Real.sqrt (n : ℝ)) * ∑ j : Fin n', b (Sum.inr j) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hsn]
        linarith
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      linarith
    | inr j =>
      simp only [notMem_leftPath_inr, ↓reduceIte, sub_zero, le_rfl]
  · simp only [ProcurementMechanism.utility, sqrtWeightedPathMechanism, hle, ↓reduceIte]
    push Not at hle
    cases e with
    | inl i =>
      simp only [notMem_rightPath_inl, ↓reduceIte, sub_zero, le_rfl]
    | inr j =>
      simp only [mem_rightPath_inr, ↓reduceIte]
      have hdiv : ∑ k : Fin n', b (Sum.inr k) ≤
          (Real.sqrt (n : ℝ) / Real.sqrt (n' : ℝ)) * ∑ i : Fin n, b (Sum.inl i) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hsn']
        linarith
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
      linarith

theorem sqrtWeightedPathMechanism_isDSIC {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n') :
    (sqrtWeightedPathMechanism n n').IsDSIC := by
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have hsn' : (0 : ℝ) < Real.sqrt (n' : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn')
  intro e b cₑ _ _
  cases e with
  | inl i =>
    have hR : ∑ j : Fin n', Function.update b (Sum.inl i) cₑ (Sum.inr j) =
        ∑ j : Fin n', b (Sum.inr j) :=
      Finset.sum_congr rfl fun j _ => Function.update_of_ne (by simp) _ _
    have hL_er : ∑ i' ∈ Finset.univ.erase i, Function.update b (Sum.inl i) cₑ (Sum.inl i') =
        ∑ i' ∈ Finset.univ.erase i, b (Sum.inl i') :=
      Finset.sum_congr rfl fun i' hi' =>
        Function.update_of_ne (fun h => Finset.ne_of_mem_erase hi' (Sum.inl.inj h)) _ _
    have hL_upd : ∑ i' : Fin n, Function.update b (Sum.inl i) cₑ (Sum.inl i') =
        cₑ + ∑ i' ∈ Finset.univ.erase i, b (Sum.inl i') := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self, hL_er]
    by_cases h1 : Real.sqrt (n : ℝ) * (∑ k : Fin n, b (Sum.inl k)) ≤
        Real.sqrt (n' : ℝ) * (∑ j : Fin n', b (Sum.inr j)) <;>
      by_cases h2 : Real.sqrt (n : ℝ) *
          (∑ k : Fin n, Function.update b (Sum.inl i) cₑ (Sum.inl k)) ≤
          Real.sqrt (n' : ℝ) * (∑ j : Fin n', Function.update b (Sum.inl i) cₑ (Sum.inr j))
    · simp only [ProcurementMechanism.utility, sqrtWeightedPathMechanism, h1, h2, ↓reduceIte,
        mem_leftPath_inl]
      rw [hR, hL_er]
    · simp only [ProcurementMechanism.utility, sqrtWeightedPathMechanism, h1, h2, ↓reduceIte,
        mem_leftPath_inl, notMem_rightPath_inl, sub_zero]
      rw [hL_upd, hR] at h2
      push Not at h2
      have hlt : (Real.sqrt (n' : ℝ) / Real.sqrt (n : ℝ)) * ∑ j : Fin n', b (Sum.inr j) <
          cₑ + ∑ i' ∈ Finset.univ.erase i, b (Sum.inl i') := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hsn]
        linarith
      linarith
    · simp only [ProcurementMechanism.utility, sqrtWeightedPathMechanism, h1, h2, ↓reduceIte,
        mem_leftPath_inl, notMem_rightPath_inl, sub_zero]
      rw [hR, hL_er]
      rw [hL_upd, hR] at h2
      have hle : cₑ + ∑ i' ∈ Finset.univ.erase i, b (Sum.inl i') ≤
          (Real.sqrt (n' : ℝ) / Real.sqrt (n : ℝ)) * ∑ j : Fin n', b (Sum.inr j) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hsn]
        linarith
      linarith
    · simp only [ProcurementMechanism.utility, sqrtWeightedPathMechanism, h1, h2, ↓reduceIte,
        notMem_rightPath_inl, le_rfl]
  | inr j =>
    have hL : ∑ i : Fin n, Function.update b (Sum.inr j) cₑ (Sum.inl i) =
        ∑ i : Fin n, b (Sum.inl i) :=
      Finset.sum_congr rfl fun i _ => Function.update_of_ne (by simp) _ _
    have hR_er : ∑ j' ∈ Finset.univ.erase j, Function.update b (Sum.inr j) cₑ (Sum.inr j') =
        ∑ j' ∈ Finset.univ.erase j, b (Sum.inr j') :=
      Finset.sum_congr rfl fun j' hj' =>
        Function.update_of_ne (fun h => Finset.ne_of_mem_erase hj' (Sum.inr.inj h)) _ _
    have hR_upd : ∑ j' : Fin n', Function.update b (Sum.inr j) cₑ (Sum.inr j') =
        cₑ + ∑ j' ∈ Finset.univ.erase j, b (Sum.inr j') := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self, hR_er]
    by_cases h1 : Real.sqrt (n : ℝ) * (∑ i : Fin n, b (Sum.inl i)) ≤
        Real.sqrt (n' : ℝ) * (∑ k : Fin n', b (Sum.inr k)) <;>
      by_cases h2 : Real.sqrt (n : ℝ) *
          (∑ i : Fin n, Function.update b (Sum.inr j) cₑ (Sum.inl i)) ≤
          Real.sqrt (n' : ℝ) * (∑ k : Fin n', Function.update b (Sum.inr j) cₑ (Sum.inr k))
    · simp only [ProcurementMechanism.utility, sqrtWeightedPathMechanism, h1, h2, ↓reduceIte,
        notMem_leftPath_inr, le_rfl]
    · simp only [ProcurementMechanism.utility, sqrtWeightedPathMechanism, h1, h2, ↓reduceIte,
        notMem_leftPath_inr, mem_rightPath_inr, sub_zero]
      rw [hL, hR_er]
      rw [hL, hR_upd] at h2
      push Not at h2
      have hlt : cₑ + ∑ j' ∈ Finset.univ.erase j, b (Sum.inr j') <
          (Real.sqrt (n : ℝ) / Real.sqrt (n' : ℝ)) * ∑ i : Fin n, b (Sum.inl i) := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ hsn']
        linarith
      linarith
    · simp only [ProcurementMechanism.utility, sqrtWeightedPathMechanism, h1, h2, ↓reduceIte,
        notMem_leftPath_inr, mem_rightPath_inr, sub_zero]
      rw [hL, hR_upd] at h2
      have hle : (Real.sqrt (n : ℝ) / Real.sqrt (n' : ℝ)) * ∑ i : Fin n, b (Sum.inl i) ≤
          cₑ + ∑ j' ∈ Finset.univ.erase j, b (Sum.inr j') := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hsn']
        linarith
      linarith
    · simp only [ProcurementMechanism.utility, sqrtWeightedPathMechanism, h1, h2, ↓reduceIte,
        mem_rightPath_inr]
      rw [hL, hR_er]

/-- **Upper bound for the weighted path auction ([HartlineKarlin2007], §13.5.1.1, p. 354):**
`sqrtWeightedPathMechanism n n'` achieves frugality ratio at most `√(n * n')`, matching Theorem
13.54 within a factor of `2`. -/
theorem sqrtWeightedPathMechanism_hasFrugalityRatioLe {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n') :
    HasFrugalityRatioLe (twoDisjointPaths n n') (sqrtWeightedPathMechanism n n')
      (Real.sqrt ((n : ℝ) * (n' : ℝ))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hn'R : (0 : ℝ) < (n' : ℝ) := Nat.cast_pos.2 hn'
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsn' : (0 : ℝ) < Real.sqrt (n' : ℝ) := Real.sqrt_pos.2 hn'R
  refine ⟨Real.sqrt_nonneg _, fun c hc0 => ?_⟩
  rw [(sqrtWeightedPathMechanism n n').totalPay_eq_sum_alloc
    (sqrtWeightedPathMechanism_losersPaidZero n n') hc0,
    cheapestNash_twoDisjointPaths hn hn' c]
  simp only [sqrtWeightedPathMechanism]
  split_ifs with hle
  · rw [sum_leftPath]
    calc ∑ i : Fin n,
          ((Real.sqrt (n' : ℝ) / Real.sqrt (n : ℝ)) * (∑ j : Fin n', c (Sum.inr j)) -
            ∑ i' ∈ Finset.univ.erase i, c (Sum.inl i'))
        ≤ ∑ _i : Fin n,
            ((Real.sqrt (n' : ℝ) / Real.sqrt (n : ℝ)) * ∑ j : Fin n', c (Sum.inr j)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hnn : 0 ≤ ∑ i' ∈ Finset.univ.erase i, c (Sum.inl i') :=
            Finset.sum_nonneg fun i' _ => hc0 (Sum.inl i')
          linarith
      _ = (n : ℝ) * ((Real.sqrt (n' : ℝ) / Real.sqrt (n : ℝ)) * ∑ j : Fin n', c (Sum.inr j)) := by
          simp
      _ = Real.sqrt ((n : ℝ) * (n' : ℝ)) * ∑ j : Fin n', c (Sum.inr j) := by
          rw [Real.sqrt_mul hnR.le]
          field_simp [hsn.ne']
          rw [Real.sq_sqrt hnR.le]
      _ ≤ Real.sqrt ((n : ℝ) * (n' : ℝ)) *
            max (∑ i : Fin n, c (Sum.inl i)) (∑ j : Fin n', c (Sum.inr j)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _)
  · rw [sum_rightPath]
    calc ∑ j : Fin n',
          ((Real.sqrt (n : ℝ) / Real.sqrt (n' : ℝ)) * (∑ i : Fin n, c (Sum.inl i)) -
            ∑ j' ∈ Finset.univ.erase j, c (Sum.inr j'))
        ≤ ∑ _j : Fin n',
            ((Real.sqrt (n : ℝ) / Real.sqrt (n' : ℝ)) * ∑ i : Fin n, c (Sum.inl i)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hnn : 0 ≤ ∑ j' ∈ Finset.univ.erase j, c (Sum.inr j') :=
            Finset.sum_nonneg fun j' _ => hc0 (Sum.inr j')
          linarith
      _ = (n' : ℝ) * ((Real.sqrt (n : ℝ) / Real.sqrt (n' : ℝ)) * ∑ i : Fin n, c (Sum.inl i)) := by
          simp
      _ = Real.sqrt ((n : ℝ) * (n' : ℝ)) * ∑ i : Fin n, c (Sum.inl i) := by
          rw [Real.sqrt_mul hnR.le]
          field_simp [hsn'.ne']
          rw [Real.sq_sqrt hn'R.le]
      _ ≤ Real.sqrt ((n : ℝ) * (n' : ℝ)) *
            max (∑ i : Fin n, c (Sum.inl i)) (∑ j : Fin n', c (Sum.inr j)) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg _)

end TwoDisjointPaths

end Cslib.GameTheory.Mechanism.Frugality
