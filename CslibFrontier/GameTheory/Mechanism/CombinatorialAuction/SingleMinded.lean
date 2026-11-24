/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Single-minded combinatorial auctions and the LOS greedy mechanism

A *single-minded bidder* desires a single bundle of items `S* : Finset M` and obtains a nonnegative
value `v* : ℝ` from any allocation containing `S*`, and `0` otherwise ([BlumrosenNisan2007],
§11.2, Definition 11.3, p. 270). This module formalizes §11.2 of [BlumrosenNisan2007] (pp.
270–275): winner determination via compatible winner sets `W : Finset N` (Definition 11.4,
p. 271), direct mechanisms for single-minded bidders and dominant-strategy incentive compatibility
(Definition 11.7, p. 273), the characterization of DSIC mechanisms via monotonicity and critical
payments (Lemma 11.9, pp. 274–275), the greedy mechanism of Lehmann–O'Callaghan–Shoham
(Figure 11.1, p. 274), and its `√m`-approximation ratio (Lemma 11.10, p. 275).

No computational complexity or running-time claim is formalized here: the NP-completeness results
(Propositions 11.5–11.6, pp. 271–272) and the polynomial-time clause of Theorem 11.8 (p. 273)
remain open under issue #7789.

Single-minded bids have both a private scalar value and a private desired bundle, so the DSIC
characterization is distinct from the single-parameter model in
`CslibFrontier.GameTheory.Mechanism.SingleParameter` (and `VCG.lean` for general valuations).

## Precision notes on the printed source

1. **Lemma 11.9 (pp. 274–275):** In the exact equivalence
   `Mechanism.isDSIC_and_isIR_and_hasNonnegPayment_iff` for mechanisms in which losers pay `0`,
   monotonicity takes the strict-value form `IsWeakMonotone`
   (`S' ⊆ S → v < v' → i ∈ w (update b i ⟨S', v'⟩)`), which agrees with the book's
   `v_i' > v_i*` clause while also holding on equal bundles `S' = S`. Stronger non-strict
   monotonicity (`v ≤ v'`) is **not** necessary at the critical threshold tie `v = criticalValue`.
   The converse (`HasCriticalPayments`) additionally requires individual rationality (`IsIR`) and
   nonnegative payments (`HasNonnegPayment`), ruling out degenerate constant-winning mechanisms
   with shifted fixed payments. Each side condition is shown tight by a counterexample in
   `CslibFrontierTests.GameTheory.SingleMinded`.
2. **Figure 11.1 payment condition (p. 274):** The displayed box defines `j` as the earliest index
   with `S_i* ∩ S_j* ≠ ∅` and "for all `k < j, k ≠ i`, `S_k* ∩ S_j* = ∅`", omitting `k ∈ W`.
   Dropping `k ∈ W` allows a losing earlier bidder `k` to mask `j`, breaking truthfulness.
   With `k ∈ W` restored, the first such `j` equals the earliest bidder intersecting `S_i*` that
   wins in the greedy run without `i` (`losPayment_eq_first_blocked`).
3. **Empty desired bundles (`S* = ∅`) and empty item sets (`m = 0`):** Under Definition 11.3,
   a bid `(∅, v*)` with `v* > 0` gives `eval ∅ = v* ≠ 0` (not normalized per Definition 11.1,
   p. 268). In `losScore`, division by `√0 = 0` produces `0`, yet empty-bundle bidders never
   conflict with any other bid, so they always win in `losWinners` and pay `0` (matching their
   critical value). Lemma 11.10 assumes `[Nonempty M]` (`m ≥ 1`, so `1 ≤ √m`), which ensures that
   empty-bundle winners in `OPT` are bounded by `√m` times their own value; when `M` is empty,
   `√0 = 0` fails the literal bound on a positive bid for `∅`.

## Main definitions

* `SingleMindedBid`, `SingleMindedBid.eval`: single-minded bid `(S*, v*)` and induced valuation
  ([BlumrosenNisan2007], Definition 11.3, p. 270).
* `IsCompatible`: pairwise-disjoint desired bundles for a winner set `W : Finset N`
  (Definition 11.4, p. 271).
* `Mechanism`, `Mechanism.utility`, `Mechanism.IsFeasible`, `Mechanism.IsDSIC`, `Mechanism.IsIR`,
  `Mechanism.LosersPayZero`, `Mechanism.HasNonnegPayment`: winner-set single-minded mechanism model
  (Definition 11.7, p. 273).
* `IsWeakMonotone`, `IsMonotone`, `criticalValue`, `Mechanism.HasCriticalPayments`: the two
  characterization predicates of Lemma 11.9 (p. 274).
* `losScore`, `losLt`, `greedyStep`, `greedySelect`, `losWinners`, `losWinnersWithout`,
  `losPayment`, `losMechanism`: the LOS greedy mechanism (Figure 11.1, p. 274).

## Main results

* `Mechanism.isWeakMonotone_of_isDSIC`, `Mechanism.hasCriticalPayments_of_isDSIC`,
  `Mechanism.isDSIC_of_isWeakMonotone`, `Mechanism.isDSIC_and_isIR_and_hasNonnegPayment_iff`:
  the two-way characterization of truthful single-minded mechanisms
  ([BlumrosenNisan2007], Lemma 11.9, pp. 274–275).
* `losWinners_isCompatible`, `losWinners_isMonotone`: feasibility and strong monotonicity of the
  greedy allocation rule.
* `losPayment_eq_criticalValue`, `losPayment_eq_first_blocked`: exact critical-value and
  earliest-blocked-bidder payment characterization for winners in `losMechanism`.
* `losWinners_approx`: the `√m`-approximation guarantee ([BlumrosenNisan2007], Lemma 11.10,
  p. 275).
* `losMechanism_isFeasible`, `losMechanism_losersPayZero`, `losMechanism_isDSIC`,
  `losMechanism_isIR`, `losMechanism_hasNonnegPayment`: feasibility, normalization, truthfulness,
  individual rationality, and nonnegative payments for `losMechanism` (without requiring
  `[Fintype M]` or `[Nonempty M]`; no running-time claim is made).

## References

* [L. Blumrosen and N. Nisan, *Combinatorial Auctions*][BlumrosenNisan2007]
-/

public section

namespace Cslib.GameTheory.CombinatorialAuction.SingleMinded

/-! ### Single-minded bids and winner-set compatibility -/

/-- A single-minded bid `(S*, v*)` on item type `M` ([BlumrosenNisan2007], Definition 11.3,
p. 270). The bidder desires `bundle` (`S*`) and values any superset of `bundle` at `value` (`v*`),
and all other bundles at `0`. Nonnegativity (`0 ≤ bid.value`) is passed as a hypothesis on
profiles. -/
@[ext]
structure SingleMindedBid (M : Type*) where
  /-- The desired bundle of items `S*`. -/
  bundle : Finset M
  /-- The bidder's scalar value `v*` for receiving a superset of `bundle`. -/
  value : ℝ

namespace SingleMindedBid

variable {M : Type*}

/-- Valuation `v(S)` induced by a single-minded bid: `bid.value` if `bid.bundle ⊆ S`, and `0`
otherwise ([BlumrosenNisan2007], Definition 11.3, p. 270). -/
@[expose] def eval [DecidableEq M] (bid : SingleMindedBid M) (S : Finset M) : ℝ :=
  if bid.bundle ⊆ S then bid.value else 0

/-- A single-minded bid evaluated on its own desired bundle returns its value. -/
@[simp]
theorem eval_self [DecidableEq M] (bid : SingleMindedBid M) :
    bid.eval bid.bundle = bid.value := by
  simp [eval]

/-- Monotonicity ("free disposal", [BlumrosenNisan2007], Definition 11.1, p. 268) of a nonnegative
single-minded valuation. -/
theorem eval_mono [DecidableEq M] {bid : SingleMindedBid M} (hv : 0 ≤ bid.value)
    {S T : Finset M} (hST : S ⊆ T) : bid.eval S ≤ bid.eval T := by
  by_cases hS : bid.bundle ⊆ S
  · simp [eval, hS, hS.trans hST]
  · simp only [eval, hS, ↓reduceIte]
    split_ifs <;> linarith

/-- Normalization (`v(∅) = 0`, [BlumrosenNisan2007], Definition 11.1, p. 268) holds for every
single-minded bid with a nonempty desired bundle. -/
theorem eval_empty_of_nonempty [DecidableEq M] {bid : SingleMindedBid M}
    (h : bid.bundle.Nonempty) : bid.eval ∅ = 0 := by
  have hnot : ¬ bid.bundle ⊆ ∅ := fun hsub => h.ne_empty (Finset.subset_empty.mp hsub)
  simp [eval, hnot]

end SingleMindedBid

/-- A winner set `W` is *compatible* (feasible) for single-minded bid profile `b` if distinct
winners have pairwise disjoint desired bundles ([BlumrosenNisan2007], Definition 11.4, p. 271). -/
@[expose] def IsCompatible {N M : Type*} (b : N → SingleMindedBid M) (W : Finset N) : Prop :=
  (W : Set N).PairwiseDisjoint fun i => (b i).bundle

/-- The total cardinality of bundles in a compatible winner set is at most the number of items
`Fintype.card M`. -/
theorem IsCompatible.sum_card_le {N M : Type*} [Fintype M]
    {b : N → SingleMindedBid M} {W : Finset N} (hW : IsCompatible b W) :
    ∑ i ∈ W, (b i).bundle.card ≤ Fintype.card M := by
  classical
  rw [← Finset.card_biUnion hW]
  exact Finset.card_le_univ _

private theorem update_value_nonneg {N M : Type*} [DecidableEq N] {b : N → SingleMindedBid M}
    (hb : ∀ j, 0 ≤ (b j).value) (i : N) {bid : SingleMindedBid M} (hbid : 0 ≤ bid.value) :
    ∀ j, 0 ≤ (Function.update b i bid j).value := fun j => by
  by_cases hj : j = i
  · subst hj; simpa only [Function.update_self] using hbid
  · simpa only [Function.update_of_ne hj] using hb j

/-! ### Direct mechanisms and Lemma 11.9 characterization -/

/-- A direct-revelation mechanism for single-minded bidders in the winner-set representation
([BlumrosenNisan2007], Definition 11.4, p. 271 and Definition 11.7, p. 273). On a profile
`b : N → SingleMindedBid M`, each winner `i ∈ winners b` receives its exact declared bundle
`(b i).bundle`, each loser receives nothing, and `payment b i` is charged to bidder `i`. -/
structure Mechanism (N M : Type*) where
  /-- The set of winning bidders for a reported bid profile. -/
  winners : (N → SingleMindedBid M) → Finset N
  /-- The payment charged to each bidder for a reported bid profile. -/
  payment : (N → SingleMindedBid M) → N → ℝ

namespace Mechanism

variable {N M : Type*}

/-- Feasibility: on every nonnegative bid profile, winners have pairwise disjoint desired bundles.
-/
@[expose] def IsFeasible (m : Mechanism N M) : Prop :=
  ∀ b : N → SingleMindedBid M, (∀ i, 0 ≤ (b i).value) → IsCompatible b (m.winners b)

/-- Quasilinear utility of bidder `i` with true bid `trueBid` under reported profile `b`:
`trueBid.value` if `i ∈ m.winners b` and `trueBid.bundle ⊆ (b i).bundle`, `0` otherwise, minus
`m.payment b i` ([BlumrosenNisan2007], Definition 11.7, p. 273). For nonempty `trueBid.bundle`
this agrees with evaluating `trueBid` at the allocated bundle (`(b i).bundle` or `∅`). -/
@[expose] def utility [DecidableEq N] [DecidableEq M] (m : Mechanism N M) (i : N)
    (trueBid : SingleMindedBid M) (b : N → SingleMindedBid M) : ℝ :=
  (if i ∈ m.winners b then trueBid.eval (b i).bundle else 0) - m.payment b i

/-- For nonempty desired bundle `trueBid.bundle`, `utility` agrees with evaluating `trueBid` on
the allocated bundle (`(b i).bundle` for winners, `∅` for losers). -/
theorem utility_eq_eval_allocated [DecidableEq N] [DecidableEq M] (m : Mechanism N M) (i : N)
    {trueBid : SingleMindedBid M} (hne : trueBid.bundle.Nonempty)
    (b : N → SingleMindedBid M) :
    m.utility i trueBid b =
      trueBid.eval (if i ∈ m.winners b then (b i).bundle else ∅) - m.payment b i := by
  by_cases hi : i ∈ m.winners b
  · simp [utility, hi]
  · simp [utility, hi, trueBid.eval_empty_of_nonempty hne]

/-- Dominant-strategy incentive compatibility (DSIC) on nonnegative single-minded bids
([BlumrosenNisan2007], Definition 11.7, p. 273): for every bidder `i`, nonnegative reported
profile `b` (holding both the others' bids `b₋ᵢ` and an arbitrary deviation `b i`), and true
nonnegative bid `trueBid`, reporting truthfully does not decrease `i`'s utility. -/
@[expose] def IsDSIC [DecidableEq N] [DecidableEq M] (m : Mechanism N M) : Prop :=
  ∀ (i : N) (b : N → SingleMindedBid M) (trueBid : SingleMindedBid M),
    (∀ j, 0 ≤ (b j).value) → 0 ≤ trueBid.value →
    m.utility i trueBid b ≤ m.utility i trueBid (Function.update b i trueBid)

/-- Individual rationality (voluntary participation): a truthful bidder with a nonnegative bid
receives nonnegative utility. -/
@[expose] def IsIR [DecidableEq N] [DecidableEq M] (m : Mechanism N M) : Prop :=
  ∀ (i : N) (b : N → SingleMindedBid M), (∀ j, 0 ≤ (b j).value) →
    0 ≤ m.utility i (b i) b

/-- Normalization for losers: on every nonnegative bid profile, losing bidders pay `0`
([BlumrosenNisan2007], Lemma 11.9, p. 274). -/
@[expose] def LosersPayZero (m : Mechanism N M) : Prop :=
  ∀ (b : N → SingleMindedBid M), (∀ j, 0 ≤ (b j).value) →
    ∀ i, i ∉ m.winners b → m.payment b i = 0

/-- No positive transfers: on every nonnegative bid profile, every bidder's payment is
nonnegative. -/
@[expose] def HasNonnegPayment (m : Mechanism N M) : Prop :=
  ∀ (b : N → SingleMindedBid M), (∀ j, 0 ≤ (b j).value) →
    ∀ i, 0 ≤ m.payment b i

end Mechanism

/-- Weak (strict-value) monotonicity of a single-minded allocation rule `w`
([BlumrosenNisan2007], Lemma 11.9(i), p. 274): a bidder who wins with bid `(S*, v*)` continues to
win for every `S' ⊆ S*` and **strictly greater** `v' > v*`. This is the exact monotonicity
condition needed and implied by DSIC + `LosersPayZero` (strong `v ≤ v'` fails at critical-value
ties). -/
@[expose] def IsWeakMonotone {N M : Type*} [DecidableEq N]
    (w : (N → SingleMindedBid M) → Finset N) : Prop :=
  ∀ (i : N) (b : N → SingleMindedBid M) (S' : Finset M) (v' : ℝ),
    (∀ j, 0 ≤ (b j).value) → i ∈ w b → S' ⊆ (b i).bundle → (b i).value < v' →
    i ∈ w (Function.update b i ⟨S', v'⟩)

/-- Strong (non-strict-value) monotonicity of a single-minded allocation rule `w`: a bidder who
wins with `(S*, v*)` keeps winning for every `S' ⊆ S*` and `v' ≥ v*`. -/
@[expose] def IsMonotone {N M : Type*} [DecidableEq N]
    (w : (N → SingleMindedBid M) → Finset N) : Prop :=
  ∀ (i : N) (b : N → SingleMindedBid M) (S' : Finset M) (v' : ℝ),
    (∀ j, 0 ≤ (b j).value) → i ∈ w b → S' ⊆ (b i).bundle → (b i).value ≤ v' →
    i ∈ w (Function.update b i ⟨S', v'⟩)

/-- Strong monotonicity implies weak monotonicity. -/
theorem IsMonotone.isWeakMonotone {N M : Type*} [DecidableEq N]
    {w : (N → SingleMindedBid M) → Finset N} (hw : IsMonotone w) :
    IsWeakMonotone w :=
  fun i b S' v' hb hi hS hlt => hw i b S' v' hb hi hS hlt.le

/-- The critical value of bidder `i` for its declared bundle `(b i).bundle` against the other
bids `b₋ᵢ` ([BlumrosenNisan2007], Lemma 11.9(ii), p. 274): the infimum of all nonnegative values
`z` at which `i` wins when bidding `((b i).bundle, z)`. Defaults to `0` if the set is empty. -/
@[expose] noncomputable def criticalValue {N M : Type*} [DecidableEq N]
    (w : (N → SingleMindedBid M) → Finset N) (b : N → SingleMindedBid M) (i : N) : ℝ :=
  sInf {z : ℝ | 0 ≤ z ∧ i ∈ w (Function.update b i ⟨(b i).bundle, z⟩)}

/-- Changing bidder `i`'s declared value does not change its critical value for the same bundle. -/
@[simp]
theorem criticalValue_update_value {N M : Type*} [DecidableEq N]
    (w : (N → SingleMindedBid M) → Finset N) (b : N → SingleMindedBid M) (i : N) (v : ℝ) :
    criticalValue w (Function.update b i ⟨(b i).bundle, v⟩) i = criticalValue w b i := by
  simp only [criticalValue, Function.update_self, Function.update_idem]

/-- Every critical value is nonnegative. -/
theorem criticalValue_nonneg {N M : Type*} [DecidableEq N]
    (w : (N → SingleMindedBid M) → Finset N) (b : N → SingleMindedBid M) (i : N) :
    0 ≤ criticalValue w b i :=
  Real.sInf_nonneg fun _ hz => hz.1

/-- Any nonnegative winning value for bundle `(b i).bundle` upper-bounds the critical value. -/
theorem criticalValue_le_of_mem {N M : Type*} [DecidableEq N]
    {w : (N → SingleMindedBid M) → Finset N} {b : N → SingleMindedBid M} {i : N}
    {z : ℝ} (hz : 0 ≤ z) (hwin : i ∈ w (Function.update b i ⟨(b i).bundle, z⟩)) :
    criticalValue w b i ≤ z :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hz, hwin⟩

private theorem criticalValue_eq_of_threshold {N M : Type*} [DecidableEq N]
    {w : (N → SingleMindedBid M) → Finset N} {b : N → SingleMindedBid M} {i : N} {t : ℝ}
    (ht : 0 ≤ t)
    (hlt : ∀ z, t < z → i ∈ w (Function.update b i ⟨(b i).bundle, z⟩))
    (hle : ∀ z, 0 ≤ z → i ∈ w (Function.update b i ⟨(b i).bundle, z⟩) → t ≤ z) :
    criticalValue w b i = t := by
  apply le_antisymm
  · rw [← csInf_Ioi (a := t)]
    exact csInf_le_csInf ⟨0, fun _ h => h.1⟩ Set.nonempty_Ioi
      fun z hz => ⟨ht.trans (le_of_lt hz), hlt z hz⟩
  · exact le_csInf ⟨t + 1, by linarith, hlt _ (by linarith)⟩ fun z hz => hle z hz.1 hz.2

/-- A winning bidder's payment equals its critical value for every nonnegative bid profile
([BlumrosenNisan2007], Lemma 11.9(ii), p. 274). -/
@[expose] def Mechanism.HasCriticalPayments {N M : Type*} [DecidableEq N]
    (m : Mechanism N M) : Prop :=
  ∀ (b : N → SingleMindedBid M), (∀ j, 0 ≤ (b j).value) →
    ∀ i ∈ m.winners b, m.payment b i = criticalValue m.winners b i

private theorem criticalValue_mono_bundle {N M : Type*} [DecidableEq N]
    {w : (N → SingleMindedBid M) → Finset N} (hw : IsWeakMonotone w)
    {b : N → SingleMindedBid M} (hb : ∀ j, 0 ≤ (b j).value) {i : N}
    {S S' : Finset M} (hSS' : S ⊆ S') {v' : ℝ} (hv' : 0 ≤ v')
    (hwin : i ∈ w (Function.update b i ⟨S', v'⟩)) (v : ℝ) :
    criticalValue w (Function.update b i ⟨S, v⟩) i ≤
      criticalValue w (Function.update b i ⟨S', v'⟩) i := by
  have hne : {z : ℝ | 0 ≤ z ∧ i ∈ w (Function.update b i ⟨S', z⟩)}.Nonempty :=
    ⟨v', hv', hwin⟩
  have hrew : criticalValue w (Function.update b i ⟨S', v'⟩) i =
      sInf {z : ℝ | 0 ≤ z ∧ i ∈ w (Function.update b i ⟨S', z⟩)} := by
    simp only [criticalValue, Function.update_self, Function.update_idem]
  rw [hrew]
  refine le_csInf hne fun z ⟨hz0, hzw⟩ => ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hz_step : i ∈ w (Function.update b i ⟨S, z + ε⟩) := by
    have hmono := hw i (Function.update b i ⟨S', z⟩) S (z + ε)
      (update_value_nonneg hb i hz0) hzw
      (by simpa only [Function.update_self] using hSS')
      (by simpa only [Function.update_self] using lt_add_of_pos_right z hε)
    simpa only [Function.update_idem] using hmono
  exact criticalValue_le_of_mem (w := w)
    (b := Function.update b i ⟨S, v⟩) (i := i) (z := z + ε) (by linarith)
    (by simpa only [Function.update_self, Function.update_idem] using hz_step)

namespace Mechanism

variable {N M : Type*}

/-- Every normalized mechanism charging winners their critical values has nonnegative payments. -/
theorem hasNonnegPayment_of_hasCriticalPayments [DecidableEq N] {m : Mechanism N M}
    (h0 : m.LosersPayZero) (hcrit : m.HasCriticalPayments) : m.HasNonnegPayment := by
  intro b hb i
  by_cases hi : i ∈ m.winners b
  · rw [hcrit b hb i hi]
    exact criticalValue_nonneg m.winners b i
  · rw [h0 b hb i hi]

/-- Every normalized mechanism charging winners their critical values is individually rational. -/
theorem isIR_of_hasCriticalPayments [DecidableEq N] [DecidableEq M] {m : Mechanism N M}
    (h0 : m.LosersPayZero) (hcrit : m.HasCriticalPayments) : m.IsIR := by
  intro i b hb
  simp only [utility]
  by_cases hi : i ∈ m.winners b
  · simp only [hi, ↓reduceIte, SingleMindedBid.eval_self, hcrit b hb i hi]
    have hle : criticalValue m.winners b i ≤ (b i).value :=
      criticalValue_le_of_mem (hb i) (by rwa [Function.update_eq_self])
    linarith
  · simp only [hi, ↓reduceIte, h0 b hb i hi, sub_zero, le_refl]

/-- Sufficiency of [BlumrosenNisan2007], Lemma 11.9 (pp. 274–275): if losers pay `0`, the
allocation rule is weakly monotone, and winners pay their critical values, then the mechanism is
DSIC. No boundary assumption is required at the tie `v = criticalValue`. -/
theorem isDSIC_of_isWeakMonotone [DecidableEq N] [DecidableEq M] {m : Mechanism N M}
    (h0 : m.LosersPayZero) (hmono : IsWeakMonotone m.winners) (hcrit : m.HasCriticalPayments) :
    m.IsDSIC := by
  intro i b trueBid hb ht
  have hir : 0 ≤ m.utility i trueBid (Function.update b i trueBid) := by
    have h := isIR_of_hasCriticalPayments h0 hcrit i (Function.update b i trueBid)
      (update_value_nonneg hb i ht)
    simpa only [Function.update_self] using h
  by_cases hwin : i ∈ m.winners b
  · by_cases hsub : trueBid.bundle ⊆ (b i).bundle
    · have hpay : m.payment b i = criticalValue m.winners b i := hcrit b hb i hwin
      have hcv_le : criticalValue m.winners (Function.update b i trueBid) i ≤
          criticalValue m.winners b i := by
        have hwin' : i ∈ m.winners (Function.update b i ⟨(b i).bundle, (b i).value⟩) := by
          change i ∈ m.winners (Function.update b i (b i))
          rwa [Function.update_eq_self]
        have h := criticalValue_mono_bundle hmono hb hsub (hb i) hwin' trueBid.value
        have hbi : Function.update b i ⟨(b i).bundle, (b i).value⟩ = b :=
          Function.update_eq_self i b
        simpa only [hbi] using h
      have hutil_dev : m.utility i trueBid b = trueBid.value - criticalValue m.winners b i := by
        simp [utility, hwin, SingleMindedBid.eval, hsub, hpay]
      rw [hutil_dev]
      by_cases htwin : i ∈ m.winners (Function.update b i trueBid)
      · have hpay_t : m.payment (Function.update b i trueBid) i =
            criticalValue m.winners (Function.update b i trueBid) i :=
          hcrit _ (update_value_nonneg hb i ht) i htwin
        have hutil_t : m.utility i trueBid (Function.update b i trueBid) =
            trueBid.value - criticalValue m.winners (Function.update b i trueBid) i := by
          simp [utility, htwin, Function.update_self, hpay_t]
        linarith
      · have hle_cv : trueBid.value ≤
            criticalValue m.winners (Function.update b i trueBid) i := by
          by_contra hlt
          push Not at hlt
          have hlt' : sInf {z : ℝ | 0 ≤ z ∧
              i ∈ m.winners (Function.update b i ⟨trueBid.bundle, z⟩)} < trueBid.value := by
            simpa only [criticalValue, Function.update_self, Function.update_idem] using hlt
          have hne : {z : ℝ | 0 ≤ z ∧
              i ∈ m.winners (Function.update b i ⟨trueBid.bundle, z⟩)}.Nonempty :=
            ⟨(b i).value + 1, by linarith [hb i],
              hmono i b trueBid.bundle ((b i).value + 1) hb hwin hsub (by linarith)⟩
          obtain ⟨z, ⟨hz0, hzw⟩, hzt⟩ := exists_lt_of_csInf_lt hne hlt'
          have hstep := hmono i (Function.update b i ⟨trueBid.bundle, z⟩)
            trueBid.bundle trueBid.value (update_value_nonneg hb i hz0) hzw
            (by simp) (by simpa only [Function.update_self] using hzt)
          simp only [Function.update_idem] at hstep
          exact htwin hstep
        have hutil_t : m.utility i trueBid (Function.update b i trueBid) = 0 := by
          have hp := h0 _ (update_value_nonneg hb i ht) i htwin
          simp [utility, htwin, hp]
        linarith
    · have hnp : 0 ≤ m.payment b i := hasNonnegPayment_of_hasCriticalPayments h0 hcrit b hb i
      have hutil_dev : m.utility i trueBid b = -m.payment b i := by
        simp [utility, hwin, SingleMindedBid.eval, hsub]
      linarith
  · have hp : m.payment b i = 0 := h0 b hb i hwin
    have hutil_dev : m.utility i trueBid b = 0 := by simp [utility, hwin, hp]
    linarith

/-- Necessity of weak monotonicity in [BlumrosenNisan2007], Lemma 11.9 (p. 274): every DSIC
mechanism in which losers pay `0` has a weakly monotone allocation rule. Neither `IsIR` nor
`HasNonnegPayment` is needed for this implication. -/
theorem isWeakMonotone_of_isDSIC [DecidableEq N] [DecidableEq M] {m : Mechanism N M}
    (h0 : m.LosersPayZero) (hdsic : m.IsDSIC) : IsWeakMonotone m.winners := by
  intro i b S' v' hb hwin hsub hlt
  have hv' : 0 ≤ v' := le_trans (hb i) hlt.le
  set b' := Function.update b i ⟨S', v'⟩
  have hb' : ∀ j, 0 ≤ (b' j).value := update_value_nonneg hb i hv'
  by_contra hlose
  have h1 := hdsic i b' (b i) hb' (hb i)
  have h1' : Function.update b' i (b i) = b := by
    simp [b', Function.update_idem, Function.update_eq_self]
  rw [h1'] at h1
  have hp' : m.payment b' i = 0 := h0 b' hb' i hlose
  have hpay_le : m.payment b i ≤ (b i).value := by
    have hu_b' : m.utility i (b i) b' = 0 := by simp [utility, hlose, hp']
    have hu_b : m.utility i (b i) b = (b i).value - m.payment b i := by
      simp [utility, hwin]
    linarith
  have h2 := hdsic i b ⟨S', v'⟩ hb hv'
  have hu_dev : m.utility i ⟨S', v'⟩ b = v' - m.payment b i := by
    simp [utility, hwin, SingleMindedBid.eval, hsub]
  have hu_t : m.utility i ⟨S', v'⟩ b' = 0 := by simp [utility, hlose, hp']
  linarith

/-- Necessity of critical payments in [BlumrosenNisan2007], Lemma 11.9 (p. 274): in a DSIC,
individually rational mechanism where losers pay `0` and payments are nonnegative, every winner
pays its critical value. Both `IsIR` and `HasNonnegPayment` are tight on degenerate profiles where
a bidder has no losing bid. -/
theorem hasCriticalPayments_of_isDSIC [DecidableEq N] [DecidableEq M] {m : Mechanism N M}
    (h0 : m.LosersPayZero) (hdsic : m.IsDSIC) (hir : m.IsIR) (hnn : m.HasNonnegPayment) :
    m.HasCriticalPayments := by
  intro b hb i hwin
  apply le_antisymm
  · refine le_csInf ⟨(b i).value, hb i, by rwa [Function.update_eq_self]⟩ ?_
    rintro x ⟨hx0, hxwin⟩
    set bx := Function.update b i ⟨(b i).bundle, x⟩
    have hbx : ∀ j, 0 ≤ (bx j).value := update_value_nonneg hb i hx0
    have h_eq : m.payment b i = m.payment bx i := by
      have h1 := hdsic i b ⟨(b i).bundle, x⟩ hb hx0
      have h2 := hdsic i bx (b i) hbx (hb i)
      have hupd : Function.update bx i (b i) = b := by
        simp [bx, Function.update_idem, Function.update_eq_self]
      rw [hupd] at h2
      have h1' : x - m.payment b i ≤ x - m.payment bx i := by
        simpa [utility, hwin, hxwin, bx, SingleMindedBid.eval] using h1
      have h2' : (b i).value - m.payment bx i ≤ (b i).value - m.payment b i := by
        simpa [utility, hwin, hxwin, bx, SingleMindedBid.eval] using h2
      linarith
    have hir_x := hir i bx hbx
    have hir_x' : 0 ≤ x - m.payment bx i := by
      simpa [utility, hxwin, bx, SingleMindedBid.eval] using hir_x
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    set p := m.payment b i
    have hp0 : 0 ≤ p := hnn b hb i
    have hpe : 0 ≤ p + ε := by linarith
    have hwin_pe : i ∈ m.winners (Function.update b i ⟨(b i).bundle, p + ε⟩) := by
      by_contra hlose
      set b' := Function.update b i ⟨(b i).bundle, p + ε⟩
      have hb' : ∀ j, 0 ≤ (b' j).value := update_value_nonneg hb i hpe
      have hds := hdsic i b ⟨(b i).bundle, p + ε⟩ hb hpe
      have hpay' : m.payment b' i = 0 := h0 b' hb' i hlose
      have hu_b : m.utility i ⟨(b i).bundle, p + ε⟩ b = p + ε - p := by
        simp [utility, hwin, SingleMindedBid.eval, p]
      have hu_b' : m.utility i ⟨(b i).bundle, p + ε⟩ b' = 0 := by
        simp [utility, hlose, hpay']
      linarith
    exact criticalValue_le_of_mem hpe hwin_pe

/-- **Characterization of truthful single-minded mechanisms** ([BlumrosenNisan2007], Lemma 11.9,
pp. 274–275): a mechanism in which losers pay `0` is DSIC, individually rational, and has
nonnegative payments if and only if its allocation rule is weakly monotone (`IsWeakMonotone`) and
every winner pays its critical value (`HasCriticalPayments`). -/
theorem isDSIC_and_isIR_and_hasNonnegPayment_iff [DecidableEq N] [DecidableEq M]
    {m : Mechanism N M} (h0 : m.LosersPayZero) :
    (m.IsDSIC ∧ m.IsIR ∧ m.HasNonnegPayment) ↔
      (IsWeakMonotone m.winners ∧ m.HasCriticalPayments) :=
  ⟨fun ⟨hdsic, hir, hnn⟩ =>
    ⟨isWeakMonotone_of_isDSIC h0 hdsic, hasCriticalPayments_of_isDSIC h0 hdsic hir hnn⟩,
   fun ⟨hmono, hcrit⟩ =>
    ⟨isDSIC_of_isWeakMonotone h0 hmono hcrit,
      isIR_of_hasCriticalPayments h0 hcrit,
      hasNonnegPayment_of_hasCriticalPayments h0 hcrit⟩⟩

end Mechanism

/-! ### The LOS greedy mechanism (Figure 11.1, p. 274) -/

/-- Priority score `v* / √|S*|` of a single-minded bid ([BlumrosenNisan2007], Figure 11.1,
p. 274). When `bid.bundle = ∅`, Lean's division convention sets `losScore = 0`; empty-bundle
bidders conflict with no other bidder, so they still always enter the greedy winner set `losWinners`
and pay `0`. -/
@[expose] noncomputable def losScore {M : Type*} (bid : SingleMindedBid M) : ℝ :=
  bid.value / Real.sqrt bid.bundle.card

/-- Strict priority order of bidders in the LOS greedy mechanism ([BlumrosenNisan2007],
Figure 11.1, p. 274): higher `losScore` comes first, breaking ties deterministically by `i < j`. -/
@[expose] noncomputable def losLt {N M : Type*} [LT N]
    (b : N → SingleMindedBid M) (i j : N) : Prop :=
  losScore (b j) < losScore (b i) ∨ (losScore (b j) = losScore (b i) ∧ i < j)

private noncomputable def losLe {N M : Type*} [LE N]
    (b : N → SingleMindedBid M) (i j : N) : Prop :=
  losScore (b j) < losScore (b i) ∨ (losScore (b j) = losScore (b i) ∧ i ≤ j)

private theorem losLt_irrefl {N M : Type*} [Preorder N] (b : N → SingleMindedBid M) (i : N) :
    ¬ losLt b i i := by
  rintro (h | ⟨_, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

private theorem losLt_trans {N M : Type*} [Preorder N] (b : N → SingleMindedBid M)
    {i j k : N} (hij : losLt b i j) (hjk : losLt b j k) : losLt b i k := by
  rcases hij with h1 | ⟨e1, h1⟩ <;> rcases hjk with h2 | ⟨e2, h2⟩
  · exact Or.inl (lt_trans h2 h1)
  · exact Or.inl (lt_of_eq_of_lt e2 h1)
  · exact Or.inl (lt_of_lt_of_eq h2 e1)
  · exact Or.inr ⟨e2.trans e1, lt_trans h1 h2⟩

private theorem losLt_asymm {N M : Type*} [Preorder N] (b : N → SingleMindedBid M)
    {i j : N} (hij : losLt b i j) : ¬ losLt b j i :=
  fun hji => losLt_irrefl b i (losLt_trans b hij hji)

private theorem losLt_total {N M : Type*} [LinearOrder N] (b : N → SingleMindedBid M)
    {i j : N} (hne : i ≠ j) : losLt b i j ∨ losLt b j i := by
  rcases lt_trichotomy (losScore (b j)) (losScore (b i)) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (Or.inr ⟨h, hlt⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hgt⟩)
  · exact Or.inr (Or.inl h)

private theorem losScore_le_of_losLt {N M : Type*} [LT N] {b : N → SingleMindedBid M}
    {i j : N} (h : losLt b i j) : losScore (b j) ≤ losScore (b i) := by
  rcases h with h | ⟨e, _⟩
  · exact h.le
  · exact e.le

private theorem losLe_iff_eq_or_losLt {N M : Type*} [LinearOrder N] (b : N → SingleMindedBid M)
    (i j : N) : losLe b i j ↔ i = j ∨ losLt b i j := by
  constructor
  · rintro (h | ⟨e, hle⟩)
    · exact Or.inr (Or.inl h)
    · rcases eq_or_lt_of_le hle with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨e, hlt⟩)
  · rintro (rfl | h | ⟨e, hlt⟩)
    · exact Or.inr ⟨rfl, le_rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, hlt.le⟩

private theorem losLe_total {N M : Type*} [LinearOrder N] (b : N → SingleMindedBid M) :
    Std.Total (losLe b) :=
  ⟨fun i j => by
    by_cases h : i = j
    · subst h; exact Or.inl (Or.inr ⟨rfl, le_rfl⟩)
    · rcases losLt_total b h with h1 | h2
      · exact Or.inl ((losLe_iff_eq_or_losLt b i j).2 (Or.inr h1))
      · exact Or.inr ((losLe_iff_eq_or_losLt b j i).2 (Or.inr h2))⟩

private theorem losLe_trans {N M : Type*} [LinearOrder N] (b : N → SingleMindedBid M) :
    IsTrans N (losLe b) :=
  ⟨fun i j k hij hjk => by
    rw [losLe_iff_eq_or_losLt] at hij hjk ⊢
    rcases hij with rfl | h1
    · exact hjk
    · rcases hjk with rfl | h2
      · exact Or.inr h1
      · exact Or.inr (losLt_trans b h1 h2)⟩

private theorem losLe_antisymm {N M : Type*} [LinearOrder N] (b : N → SingleMindedBid M) :
    Std.Antisymm (losLe b) :=
  ⟨fun i j hij hji => by
    rw [losLe_iff_eq_or_losLt] at hij hji
    rcases hij with rfl | h1
    · rfl
    · rcases hji with rfl | h2
      · rfl
      · exact (losLt_asymm b h1 h2).elim⟩

private theorem list_eq_of_perm_of_pairwise_losLt {N M : Type*} [LinearOrder N]
    {b : N → SingleMindedBid M} {l₁ l₂ : List N}
    (hp : l₁.Perm l₂) (h₁ : l₁.Pairwise (losLt b)) (h₂ : l₂.Pairwise (losLt b)) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact hp.nil_eq
  | cons a t₁ ih =>
    cases l₂ with
    | nil => exact (hp.symm.nil_eq ▸ rfl)
    | cons c t₂ =>
      rcases List.pairwise_cons.1 h₁ with ⟨ha, ht₁⟩
      rcases List.pairwise_cons.1 h₂ with ⟨hc, ht₂⟩
      have heq : a = c := by
        by_contra hne
        have hac : a ∈ t₂ := by
          have hm : a ∈ c :: t₂ := hp.subset (List.mem_cons_self ..)
          exact (List.mem_cons.1 hm).resolve_left hne
        have hca : c ∈ t₁ := by
          have hm : c ∈ a :: t₁ := hp.symm.subset (List.mem_cons_self ..)
          exact (List.mem_cons.1 hm).resolve_left (Ne.symm hne)
        exact losLt_asymm b (ha c hca) (hc a hac)
      subst heq
      rw [ih (hp.cons_inv) ht₁ ht₂]

/-- Single step of the greedy loop: add `i` to `W` if its bundle is disjoint from all bundles
already in `W`. -/
@[expose] def greedyStep {N M : Type*} [DecidableEq N] [DecidableEq M]
    (b : N → SingleMindedBid M) (W : Finset N) (i : N) : Finset N :=
  if ∀ j ∈ W, Disjoint (b i).bundle (b j).bundle then insert i W else W

/-- Greedy pass scanning a list `l` of bidders in order and accepting each bidder whose bundle is
disjoint from all previously accepted bidders' bundles ([BlumrosenNisan2007], Figure 11.1,
p. 274). -/
@[expose] def greedySelect {N M : Type*} [DecidableEq N] [DecidableEq M]
    (b : N → SingleMindedBid M) (l : List N) : Finset N :=
  l.foldl (greedyStep b) ∅

private theorem subset_foldl_greedyStep {N M : Type*} [DecidableEq N] [DecidableEq M]
    (b : N → SingleMindedBid M) (l : List N) (W : Finset N) :
    W ⊆ l.foldl (greedyStep b) W := by
  induction l generalizing W with
  | nil => exact Finset.Subset.rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    refine Finset.Subset.trans ?_ (ih _)
    unfold greedyStep
    split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.rfl

private theorem foldl_greedyStep_subset_union {N M : Type*} [DecidableEq N] [DecidableEq M]
    (b : N → SingleMindedBid M) (l : List N) (W : Finset N) {x : N}
    (hx : x ∈ l.foldl (greedyStep b) W) : x ∈ W ∨ x ∈ l := by
  induction l generalizing W with
  | nil => exact Or.inl hx
  | cons a t ih =>
    simp only [List.foldl_cons] at hx
    rcases ih _ hx with h | h
    · unfold greedyStep at h
      split_ifs at h
      · rcases Finset.mem_insert.mp h with rfl | hW
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl hW
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem a h)

private theorem mem_foldl_greedyStep_of_not_mem {N M : Type*} [DecidableEq N] [DecidableEq M]
    (b : N → SingleMindedBid M) (l : List N) (W : Finset N) {x : N} (hxl : x ∉ l) :
    x ∈ l.foldl (greedyStep b) W ↔ x ∈ W := by
  constructor
  · intro hx
    rcases foldl_greedyStep_subset_union b l W hx with h | h
    · exact h
    · exact (hxl h).elim
  · exact fun hx => subset_foldl_greedyStep b l W hx

private theorem isCompatible_foldl_greedyStep {N M : Type*} [DecidableEq N] [DecidableEq M]
    (b : N → SingleMindedBid M) (l : List N) {W : Finset N} (hW : IsCompatible b W) :
    IsCompatible b (l.foldl (greedyStep b) W) := by
  induction l generalizing W with
  | nil => exact hW
  | cons a t ih =>
    simp only [List.foldl_cons]
    refine ih ?_
    unfold greedyStep
    split_ifs with hdisj
    · intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hxW <;>
        rcases Finset.mem_insert.mp hy with rfl | hyW
      · exact (hxy rfl).elim
      · exact hdisj y hyW
      · exact (hdisj x hxW).symm
      · exact hW hxW hyW hxy
    · exact hW

private theorem greedySelect_congr {N M : Type*} [DecidableEq N] [DecidableEq M]
    {b b' : N → SingleMindedBid M} {l : List N} (h : ∀ k ∈ l, b k = b' k) :
    ∀ W : Finset N, (∀ k ∈ W, b k = b' k) →
      l.foldl (greedyStep b) W = l.foldl (greedyStep b') W := by
  induction l with
  | nil => intro W _; rfl
  | cons a t ih =>
    intro W hW
    simp only [List.foldl_cons]
    have ha : b a = b' a := h a (List.mem_cons_self ..)
    have hstep : greedyStep b W a = greedyStep b' W a := by
      unfold greedyStep
      have heq : (∀ j ∈ W, Disjoint (b a).bundle (b j).bundle) ↔
          (∀ j ∈ W, Disjoint (b' a).bundle (b' j).bundle) := by
        constructor <;> intro hd j hj
        · rw [← ha, ← hW j hj]; exact hd j hj
        · rw [ha, hW j hj]; exact hd j hj
      simp only [heq]
    rw [hstep]
    refine ih (fun k hk => h k (List.mem_cons_of_mem a hk)) _ fun k hk => ?_
    unfold greedyStep at hk
    split_ifs at hk
    · rcases Finset.mem_insert.mp hk with rfl | hkW
      · exact ha
      · exact hW k hkW
    · exact hW k hk

private theorem mem_greedySelect_append_cons {N M : Type*} [DecidableEq N] [DecidableEq M]
    (b : N → SingleMindedBid M) {l₁ l₂ : List N} {i : N} (h1 : i ∉ l₁) (h2 : i ∉ l₂) :
    i ∈ greedySelect b (l₁ ++ i :: l₂) ↔
      ∀ j ∈ greedySelect b l₁, Disjoint (b i).bundle (b j).bundle := by
  simp only [greedySelect, List.foldl_append, List.foldl_cons]
  rw [mem_foldl_greedyStep_of_not_mem b l₂ _ h2]
  set W₁ := l₁.foldl (greedyStep b) ∅
  have hi_not : i ∉ W₁ := fun hi => by
    rcases foldl_greedyStep_subset_union b l₁ ∅ hi with h | h
    · exact (Finset.notMem_empty _ h)
    · exact h1 h
  change i ∈ greedyStep b W₁ i ↔ ∀ j ∈ W₁, Disjoint (b i).bundle (b j).bundle
  unfold greedyStep
  split_ifs with hdisj
  · exact iff_of_true (Finset.mem_insert_self i W₁) hdisj
  · exact iff_of_false hi_not hdisj

section LosSort

private noncomputable def losSort {N M : Type*} [LinearOrder N]
    (b : N → SingleMindedBid M) (s : Finset N) : List N :=
  @Finset.sort N s (losLe b) (Classical.decRel _) (losLe_trans b)
    (losLe_antisymm b) (losLe_total b)

private theorem mem_losSort {N M : Type*} [LinearOrder N]
    (b : N → SingleMindedBid M) (s : Finset N) (i : N) :
    i ∈ losSort b s ↔ i ∈ s :=
  @Finset.mem_sort N s (losLe b) (Classical.decRel _) (losLe_trans b)
    (losLe_antisymm b) (losLe_total b) i

private theorem losSort_nodup {N M : Type*} [LinearOrder N]
    (b : N → SingleMindedBid M) (s : Finset N) :
    (losSort b s).Nodup :=
  @Finset.sort_nodup N s (losLe b) (Classical.decRel _) (losLe_trans b)
    (losLe_antisymm b) (losLe_total b)

private theorem losSort_pairwise_losLt {N M : Type*} [LinearOrder N]
    (b : N → SingleMindedBid M) (s : Finset N) :
    (losSort b s).Pairwise (losLt b) := by
  have hle : (losSort b s).Pairwise (losLe b) :=
    @Finset.pairwise_sort N s (losLe b) (Classical.decRel _) (losLe_trans b)
      (losLe_antisymm b) (losLe_total b)
  refine ((losSort_nodup b s).and hle).imp fun {a c} ⟨hne, h⟩ => ?_
  rcases (losLe_iff_eq_or_losLt b a c).mp h with rfl | hlt
  · exact (hne rfl).elim
  · exact hlt

end LosSort

private theorem losSort_eq_of_pairwise {N M : Type*} [LinearOrder N]
    {b : N → SingleMindedBid M} {s : Finset N} {l : List N}
    (hnd : l.Nodup) (hmem : ∀ i, i ∈ l ↔ i ∈ s) (hsort : l.Pairwise (losLt b)) :
    losSort b s = l := by
  refine list_eq_of_perm_of_pairwise_losLt ?_ (losSort_pairwise_losLt b s) hsort
  exact (List.perm_ext_iff_of_nodup (losSort_nodup b s) hnd).2 fun i =>
    (mem_losSort b s i).trans (hmem i).symm

private theorem losSort_erase_update {N M : Type*} [LinearOrder N]
    (b : N → SingleMindedBid M) (s : Finset N) (i : N) (bid : SingleMindedBid M) :
    losSort (Function.update b i bid) (s.erase i) = losSort b (s.erase i) := by
  refine losSort_eq_of_pairwise (losSort_nodup b (s.erase i))
    (fun j => mem_losSort b (s.erase i) j) ?_
  have hmem := losSort_pairwise_losLt b (s.erase i)
  refine List.pairwise_iff_getElem.2 fun a b' ha hb' hab => ?_
  have ha' : (losSort b (s.erase i))[a] ≠ i :=
    (Finset.mem_erase.mp ((mem_losSort b (s.erase i) _).1 (List.getElem_mem ha))).1
  have hb'' : (losSort b (s.erase i))[b'] ≠ i :=
    (Finset.mem_erase.mp ((mem_losSort b (s.erase i) _).1 (List.getElem_mem hb'))).1
  have hlt := List.pairwise_iff_getElem.1 hmem a b' ha hb' hab
  simpa only [losLt, Function.update_of_ne ha', Function.update_of_ne hb''] using hlt

/-- The winning bidder set produced by the LOS greedy mechanism ([BlumrosenNisan2007], Figure 11.1,
p. 274): sorts all bidders by decreasing `losScore` (ties broken by smaller index `i < j`) and
greedily accepts every bidder whose desired bundle is disjoint from the previously accepted ones.
-/
noncomputable def losWinners {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M]
    (b : N → SingleMindedBid M) : Finset N :=
  greedySelect b (losSort b Finset.univ)

/-- The winning bidder set of the greedy pass with bidder `i` removed (`N \ {i}`). Depends only on
the other bidders' bids `b₋ᵢ` (`losWinnersWithout_update`). -/
noncomputable def losWinnersWithout {N M : Type*} [Fintype N] [LinearOrder N]
    [DecidableEq M] (b : N → SingleMindedBid M) (i : N) : Finset N :=
  greedySelect b (losSort b (Finset.univ.erase i))

/-- Characterizing `losWinners` using an explicit sorted list of bidders (useful for evaluating
concrete examples). -/
theorem losWinners_eq_greedySelect {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M]
    {b : N → SingleMindedBid M} {l : List N}
    (hnd : l.Nodup) (hmem : ∀ i, i ∈ l) (hsort : l.Pairwise (losLt b)) :
    losWinners b = greedySelect b l := by
  unfold losWinners
  rw [losSort_eq_of_pairwise hnd (fun i => by simp [hmem i]) hsort]

/-- Characterizing `losWinnersWithout` using an explicit sorted list of `N \ {i}`. -/
theorem losWinnersWithout_eq_greedySelect {N M : Type*} [Fintype N] [LinearOrder N]
    [DecidableEq M] {b : N → SingleMindedBid M} {i : N} {l : List N}
    (hnd : l.Nodup) (hmem : ∀ j, j ∈ l ↔ j ≠ i) (hsort : l.Pairwise (losLt b)) :
    losWinnersWithout b i = greedySelect b l := by
  unfold losWinnersWithout
  rw [losSort_eq_of_pairwise hnd (fun j => by simp [hmem j]) hsort]

/-- `losWinnersWithout b i` is independent of bidder `i`'s own bid. -/
@[simp]
theorem losWinnersWithout_update {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M]
    (b : N → SingleMindedBid M) (i : N) (bid : SingleMindedBid M) :
    losWinnersWithout (Function.update b i bid) i = losWinnersWithout b i := by
  unfold losWinnersWithout
  rw [losSort_erase_update]
  refine greedySelect_congr (fun k hk => ?_) ∅ (fun _ h => (Finset.notMem_empty _ h).elim)
  have hne : k ≠ i := (Finset.mem_erase.mp ((mem_losSort b _ k).1 hk)).1
  exact Function.update_of_ne hne bid b

/-- The greedy winner set `losWinners b` is always feasible (pairwise disjoint desired bundles). -/
theorem losWinners_isCompatible {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M]
    (b : N → SingleMindedBid M) : IsCompatible b (losWinners b) :=
  isCompatible_foldl_greedyStep b _ (by simp [IsCompatible])

private theorem losSort_split {N M : Type*} [Fintype N] [LinearOrder N]
    (b : N → SingleMindedBid M) (i : N) :
    ∃ l₁ l₂ : List N,
      losSort b Finset.univ = l₁ ++ i :: l₂ ∧
      losSort b (Finset.univ.erase i) = l₁ ++ l₂ ∧
      i ∉ l₁ ∧ i ∉ l₂ ∧
      (∀ k ∈ l₁, losLt b k i) ∧ (∀ k ∈ l₂, losLt b i k) := by
  have hi : i ∈ losSort b Finset.univ := (mem_losSort b _ i).2 (Finset.mem_univ i)
  obtain ⟨l₁, l₂, heq⟩ := List.append_of_mem hi
  have hnd : (l₁ ++ i :: l₂).Nodup := heq ▸ losSort_nodup b Finset.univ
  have hp : (l₁ ++ i :: l₂).Pairwise (losLt b) := heq ▸ losSort_pairwise_losLt b Finset.univ
  have hnd_mid : i ∉ l₁ ∧ i ∉ l₂ ∧ (l₁ ++ l₂).Nodup := by
    rw [List.nodup_append] at hnd
    rcases hnd with ⟨hnd1, hnd2, hdisj⟩
    have hcons := List.nodup_cons.1 hnd2
    refine ⟨fun h => hdisj i h i (List.mem_cons_self ..) rfl, hcons.1, ?_⟩
    exact List.nodup_append.2 ⟨hnd1, hcons.2,
      fun a ha b hb => hdisj a ha b (List.mem_cons_of_mem i hb)⟩
  have hp_sub : (l₁ ++ l₂).Pairwise (losLt b) :=
    hp.sublist (by simp)
  have hbefore : ∀ k ∈ l₁, losLt b k i := by
    intro k hk
    exact (List.pairwise_append.1 hp).2.2 k hk i (List.mem_cons_self ..)
  have hafter : ∀ k ∈ l₂, losLt b i k := by
    intro k hk
    exact (List.pairwise_cons.1 (List.pairwise_append.1 hp).2.1).1 k hk
  have hmem : ∀ k, k ∈ l₁ ++ l₂ ↔ k ∈ Finset.univ.erase i := by
    intro k
    constructor
    · intro hk
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ k⟩
      rintro rfl
      rcases List.mem_append.1 hk with h | h
      · exact hnd_mid.1 h
      · exact hnd_mid.2.1 h
    · intro hk
      have hne : k ≠ i := (Finset.mem_erase.1 hk).1
      have hmem_all : k ∈ l₁ ++ i :: l₂ := heq ▸ (mem_losSort b Finset.univ k).2 (Finset.mem_univ k)
      rcases List.mem_append.1 hmem_all with h | h
      · exact List.mem_append_left _ h
      · rcases List.mem_cons.1 h with rfl | h'
        · exact (hne rfl).elim
        · exact List.mem_append_right _ h'
  exact ⟨l₁, l₂, heq, losSort_eq_of_pairwise hnd_mid.2.2 hmem hp_sub,
    hnd_mid.1, hnd_mid.2.1, hbefore, hafter⟩

/-- Key characterization of `losWinners`: bidder `i` wins if and only if its bundle is disjoint
from every bidder in `losWinnersWithout b i` that precedes `i` in `losLt b`. -/
theorem mem_losWinners_iff {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M]
    (b : N → SingleMindedBid M) (i : N) :
    i ∈ losWinners b ↔
      ∀ j ∈ losWinnersWithout b i, losLt b j i → Disjoint (b i).bundle (b j).bundle := by
  obtain ⟨l₁, l₂, h1, h2, hni1, hni2, hbef, haft⟩ := losSort_split b i
  unfold losWinners losWinnersWithout
  rw [h1, h2, mem_greedySelect_append_cons b hni1 hni2]
  have hnd : (l₁ ++ l₂).Nodup := h2 ▸ losSort_nodup b (Finset.univ.erase i)
  have hdisj : ∀ j ∈ l₁, j ∉ l₂ := fun j hj1 hj2 =>
    (List.nodup_append.1 hnd).2.2 j hj1 j hj2 rfl
  constructor
  · intro h j hj hlt
    have hj_in_l1 : j ∈ l₁ := by
      rcases foldl_greedyStep_subset_union b (l₁ ++ l₂) ∅ hj with he | hmem
      · exact (Finset.notMem_empty _ he).elim
      · rcases List.mem_append.1 hmem with h' | h'
        · exact h'
        · exact (losLt_asymm b (haft j h') hlt).elim
    have hjn2 : j ∉ l₂ := hdisj j hj_in_l1
    have hj1 : j ∈ greedySelect b l₁ := by
      unfold greedySelect at hj ⊢
      rw [List.foldl_append] at hj
      exact (mem_foldl_greedyStep_of_not_mem b l₂ _ hjn2).1 hj
    exact h j hj1
  · intro h j hj
    have hj1_mem : j ∈ l₁ := by
      rcases foldl_greedyStep_subset_union b l₁ ∅ hj with he | hm
      · exact (Finset.notMem_empty _ he).elim
      · exact hm
    have hj_w : j ∈ greedySelect b (l₁ ++ l₂) := by
      unfold greedySelect at hj ⊢
      rw [List.foldl_append]
      exact subset_foldl_greedyStep b l₂ _ hj
    exact h j hj_w (hbef j hj1_mem)

private theorem mem_greedySelect_losSort_iff {N M : Type*} [LinearOrder N] [DecidableEq M]
    (b : N → SingleMindedBid M) {s : Finset N} {k : N} (hk : k ∈ s) :
    k ∈ greedySelect b (losSort b s) ↔
      ∀ j ∈ greedySelect b (losSort b s), losLt b j k → Disjoint (b k).bundle (b j).bundle := by
  have hk_mem : k ∈ losSort b s := (mem_losSort b s k).2 hk
  obtain ⟨l₁, l₂, heq⟩ := List.append_of_mem hk_mem
  have hnd : (l₁ ++ k :: l₂).Nodup := heq ▸ losSort_nodup b s
  have hp : (l₁ ++ k :: l₂).Pairwise (losLt b) := heq ▸ losSort_pairwise_losLt b s
  have hnk1 : k ∉ l₁ := fun h =>
    (List.nodup_append.1 hnd).2.2 k h k (List.mem_cons_self ..) rfl
  have hnk2 : k ∉ l₂ := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  have hbef : ∀ j ∈ l₁, losLt b j k :=
    fun j hj => (List.pairwise_append.1 hp).2.2 j hj k (List.mem_cons_self ..)
  have haft : ∀ j ∈ l₂, losLt b k j :=
    fun j hj => (List.pairwise_cons.1 (List.pairwise_append.1 hp).2.1).1 j hj
  have hdisj : ∀ j ∈ l₁, j ∉ k :: l₂ := fun j hj1 hj2 =>
    (List.nodup_append.1 hnd).2.2 j hj1 j hj2 rfl
  rw [heq, mem_greedySelect_append_cons b hnk1 hnk2]
  constructor
  · intro h j hj hlt
    have hj_l1 : j ∈ l₁ := by
      rcases foldl_greedyStep_subset_union b (l₁ ++ k :: l₂) ∅ hj with he | hm
      · exact (Finset.notMem_empty _ he).elim
      · rcases List.mem_append.1 hm with h' | h'
        · exact h'
        · rcases List.mem_cons.1 h' with rfl | h''
          · exact (losLt_irrefl b _ hlt).elim
          · exact (losLt_asymm b (haft j h'') hlt).elim
    have hj' : j ∈ (l₁ ++ k :: l₂).foldl (greedyStep b) ∅ := hj
    rw [List.foldl_append] at hj'
    exact h j ((mem_foldl_greedyStep_of_not_mem b (k :: l₂) _ (hdisj j hj_l1)).1 hj')
  · intro h j hj
    have hj_l1 : j ∈ l₁ := by
      rcases foldl_greedyStep_subset_union b l₁ ∅ hj with he | hm
      · exact (Finset.notMem_empty _ he).elim
      · exact hm
    have hj_all : j ∈ greedySelect b (l₁ ++ k :: l₂) := by
      unfold greedySelect at hj ⊢
      rw [List.foldl_append]
      exact subset_foldl_greedyStep b (k :: l₂) _ hj
    exact h j hj_all (hbef j hj_l1)

private theorem mem_losWinners_iff_earlier_winners {N M : Type*} [Fintype N] [LinearOrder N]
    [DecidableEq M] (b : N → SingleMindedBid M) (i : N) :
    i ∈ losWinners b ↔
      ∀ j ∈ losWinners b, losLt b j i → Disjoint (b i).bundle (b j).bundle :=
  mem_greedySelect_losSort_iff b (Finset.mem_univ i)

private theorem mem_losWinnersWithout_iff_earlier {N M : Type*} [Fintype N] [LinearOrder N]
    [DecidableEq M] (b : N → SingleMindedBid M) {i k : N} (hki : k ≠ i) :
    k ∈ losWinnersWithout b i ↔
      ∀ j ∈ losWinnersWithout b i, losLt b j k → Disjoint (b k).bundle (b j).bundle :=
  mem_greedySelect_losSort_iff b (Finset.mem_erase.2 ⟨hki, Finset.mem_univ k⟩)

private theorem losWinnersWithout_subset_ne {N M : Type*} [Fintype N] [LinearOrder N]
    [DecidableEq M] (b : N → SingleMindedBid M) {i j : N}
    (hj : j ∈ losWinnersWithout b i) : j ≠ i := by
  unfold losWinnersWithout greedySelect at hj
  rcases foldl_greedyStep_subset_union b (losSort b (Finset.univ.erase i)) ∅ hj with he | hm
  · exact (Finset.notMem_empty _ he).elim
  · exact (Finset.mem_erase.1 ((mem_losSort b (Finset.univ.erase i) j).1 hm)).1

/-- An empty-bundle bidder never conflicts with any winner and hence always wins in `losWinners`. -/
theorem mem_losWinners_of_bundle_empty {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M]
    (b : N → SingleMindedBid M) {i : N} (he : (b i).bundle = ∅) : i ∈ losWinners b :=
  (mem_losWinners_iff b i).2 fun _ _ _ => by rw [he]; exact Finset.disjoint_empty_left _

private theorem losScore_mono {M : Type*} {S S' : Finset M} {v v' : ℝ}
    (hv : 0 ≤ v) (hvv' : v ≤ v') (hSS' : S' ⊆ S) (hne : S'.Nonempty) :
    losScore ⟨S, v⟩ ≤ losScore ⟨S', v'⟩ := by
  have hc_pos : (0 : ℝ) < S'.card := Nat.cast_pos.2 hne.card_pos
  have hc_le : (S'.card : ℝ) ≤ S.card := Nat.cast_le.2 (Finset.card_le_card hSS')
  have hsq_pos : 0 < Real.sqrt S'.card := Real.sqrt_pos.2 hc_pos
  have hsq_le : Real.sqrt S'.card ≤ Real.sqrt S.card := Real.sqrt_le_sqrt hc_le
  unfold losScore
  calc v / Real.sqrt S.card ≤ v' / Real.sqrt S.card :=
        div_le_div_of_nonneg_right hvv' (Real.sqrt_nonneg _)
    _ ≤ v' / Real.sqrt S'.card :=
        div_le_div_of_nonneg_left (hv.trans hvv') hsq_pos hsq_le

/-- The LOS greedy allocation rule is strongly monotone: lowering a winner's desired bundle to
`S' ⊆ S` and raising its bid to `v' ≥ v` preserves winning. -/
theorem losWinners_isMonotone {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M] :
    IsMonotone (losWinners (N := N) (M := M)) := by
  intro i b S' v' hb hwin hsub hle
  by_cases hS' : S' = ∅
  · refine mem_losWinners_of_bundle_empty _ ?_
    simp [Function.update_self, hS']
  · have hne : S'.Nonempty := Finset.nonempty_iff_ne_empty.2 hS'
    have hscore : losScore (b i) ≤ losScore ⟨S', v'⟩ :=
      losScore_mono (hb i) hle hsub hne
    rw [mem_losWinners_iff, losWinnersWithout_update]
    intro j hj hlt
    have hjne : j ≠ i := losWinnersWithout_subset_ne b hj
    simp only [Function.update_self, Function.update_of_ne hjne]
    have hlt_orig : losLt b j i := by
      rcases hlt with hs | ⟨es, hij⟩
      · simp only [Function.update_self, Function.update_of_ne hjne] at hs
        exact Or.inl (lt_of_le_of_lt hscore hs)
      · simp only [Function.update_self, Function.update_of_ne hjne] at es
        rcases lt_or_eq_of_le hscore with hs | hs
        · exact Or.inl (lt_of_lt_of_eq hs es)
        · exact Or.inr ⟨hs.trans es, hij⟩
    have hdisj := (mem_losWinners_iff b i).1 hwin j hj hlt_orig
    exact hdisj.mono_left hsub

private noncomputable def losBlockers {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M]
    (b : N → SingleMindedBid M) (i : N) : Finset N :=
  open scoped Classical in
  (losWinnersWithout b i).filter fun j => ¬ Disjoint (b i).bundle (b j).bundle

/-- Payment rule of the LOS greedy mechanism ([BlumrosenNisan2007], Figure 11.1, p. 274):
losers pay `0`; a winner `i` pays `0` if its bundle conflicts with no winner in
`losWinnersWithout b i`, and otherwise pays `max_{j ∈ blockers} losScore (b j) * √|S_i*|`.
Theorem `losPayment_eq_first_blocked` proves this equals `v_j* / √(|S_j*| / |S_i*|)` for the
earliest-ranked bidder `j` blocked solely by `i`. -/
noncomputable def losPayment {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M]
    (b : N → SingleMindedBid M) (i : N) : ℝ :=
  if i ∈ losWinners b then
    if h : (losBlockers b i).Nonempty then
      ((losBlockers b i).image fun j => losScore (b j)).max' (h.image _) *
        Real.sqrt (b i).bundle.card
    else 0
  else 0

/-- The LOS greedy mechanism for single-minded bidders ([BlumrosenNisan2007], Figure 11.1,
p. 274). -/
@[expose] noncomputable def losMechanism {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M] :
    Mechanism N M where
  winners := losWinners
  payment := losPayment

/-- The LOS greedy mechanism always outputs a compatible (feasible) winner set. -/
theorem losMechanism_isFeasible {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M] :
    (losMechanism (N := N) (M := M)).IsFeasible :=
  fun b _ => losWinners_isCompatible b

/-- Losing bidders pay `0` in the LOS greedy mechanism. -/
theorem losMechanism_losersPayZero {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M] :
    (losMechanism (N := N) (M := M)).LosersPayZero := by
  intro b _ i hni
  have hni' : i ∉ losWinners b := hni
  change losPayment b i = 0
  simp only [losPayment, hni', ↓reduceIte]

/-- An empty-bundle bidder has zero payment in `losMechanism`. -/
theorem losPayment_eq_zero_of_bundle_empty {N M : Type*} [Fintype N] [LinearOrder N]
    [DecidableEq M] (b : N → SingleMindedBid M) {i : N} (he : (b i).bundle = ∅) :
    losPayment b i = 0 := by
  unfold losPayment
  split_ifs
  · simp [he]
  · rfl
  · rfl

/-- Every winning bidder's LOS payment equals its critical value ([BlumrosenNisan2007], p. 274). -/
theorem losPayment_eq_criticalValue {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M]
    (b : N → SingleMindedBid M) (hb : ∀ j, 0 ≤ (b j).value) {i : N} (hwin : i ∈ losWinners b) :
    losPayment b i = criticalValue losWinners b i := by
  simp only [losPayment, hwin, ↓reduceIte]
  split_ifs with hne
  · set sMax := ((losBlockers b i).image fun j => losScore (b j)).max' (hne.image _)
    have ⟨jStar, hjStar_mem, hjStar_eq⟩ : ∃ j ∈ losBlockers b i, losScore (b j) = sMax := by
      have hm := Finset.max'_mem ((losBlockers b i).image fun j => losScore (b j)) (hne.image _)
      simpa only [Finset.mem_image] using hm
    have hnd_ij : ¬ Disjoint (b i).bundle (b jStar).bundle :=
      (Finset.mem_filter.1 hjStar_mem).2
    have hi_ne : (b i).bundle.Nonempty := by
      rw [Finset.not_disjoint_iff] at hnd_ij
      exact ⟨hnd_ij.choose, hnd_ij.choose_spec.1⟩
    have hsq_pos : 0 < Real.sqrt (b i).bundle.card :=
      Real.sqrt_pos.2 (Nat.cast_pos.2 hi_ne.card_pos)
    have hsMax_nn : 0 ≤ sMax := by
      rw [← hjStar_eq]
      exact div_nonneg (hb jStar) (Real.sqrt_nonneg _)
    have ht_nn : 0 ≤ sMax * Real.sqrt (b i).bundle.card :=
      mul_nonneg hsMax_nn hsq_pos.le
    symm
    refine criticalValue_eq_of_threshold ht_nn ?_ ?_
    · intro z hz
      rw [mem_losWinners_iff, losWinnersWithout_update]
      intro j hj hlt
      by_contra hnd
      have hjb : j ∈ losBlockers b i := by
        refine Finset.mem_filter.2 ⟨hj, ?_⟩
        simpa only [Function.update_self,
          Function.update_of_ne (losWinnersWithout_subset_ne b hj)] using hnd
      have hsc_le : losScore (b j) ≤ sMax :=
        Finset.le_max' ((losBlockers b i).image fun k => losScore (b k)) (losScore (b j))
          (Finset.mem_image_of_mem (fun k => losScore (b k)) hjb)
      have hsc_lt : losScore (b j) < z / Real.sqrt (b i).bundle.card := by
        have hlt' : sMax < z / Real.sqrt (b i).bundle.card := (lt_div_iff₀ hsq_pos).2 hz
        exact lt_of_le_of_lt hsc_le hlt'
      have hj_le := losScore_le_of_losLt hlt
      simp only [Function.update_self,
        Function.update_of_ne (losWinnersWithout_subset_ne b hj)] at hj_le
      change z / Real.sqrt (b i).bundle.card ≤ losScore (b j) at hj_le
      linarith
    · intro z _ hwin_z
      by_contra hlt
      push Not at hlt
      have hjStar_w : jStar ∈ losWinnersWithout b i := (Finset.mem_filter.1 hjStar_mem).1
      have hjStar_ne : jStar ≠ i := losWinnersWithout_subset_ne b hjStar_w
      have hscore_lt : z / Real.sqrt (b i).bundle.card < losScore (b jStar) := by
        rw [hjStar_eq]
        exact (div_lt_iff₀ hsq_pos).2 hlt
      have hlt_ji : losLt (Function.update b i ⟨(b i).bundle, z⟩) jStar i := by
        left
        simpa only [Function.update_self, Function.update_of_ne hjStar_ne, losScore] using hscore_lt
      have hdisj := (mem_losWinners_iff _ i).1 hwin_z jStar
        (by rwa [losWinnersWithout_update]) hlt_ji
      simp only [Function.update_self, Function.update_of_ne hjStar_ne] at hdisj
      exact hnd_ij hdisj
  · symm
    refine criticalValue_eq_of_threshold le_rfl ?_ (fun z hz _ => hz)
    intro z _
    rw [mem_losWinners_iff, losWinnersWithout_update]
    intro j hj _
    have hjne : j ≠ i := losWinnersWithout_subset_ne b hj
    simp only [Function.update_self, Function.update_of_ne hjne]
    by_contra hnd
    exact hne ⟨j, Finset.mem_filter.2 ⟨hj, hnd⟩⟩

private theorem losLt_wf {N M : Type*} [Finite N] [Preorder N] (b : N → SingleMindedBid M) :
    WellFounded (losLt b) := by
  have : IsTrans N (losLt b) := ⟨fun _ _ _ => losLt_trans b⟩
  have : Std.Irrefl (losLt b) := ⟨losLt_irrefl b⟩
  exact Finite.wellFounded_of_trans_of_irrefl (losLt b)

private theorem winners_agree_before_blocker {N M : Type*} [Fintype N] [LinearOrder N]
    [DecidableEq M] (b : N → SingleMindedBid M) {i : N} :
    ∀ k : N, k ≠ i → (∀ x ∈ losBlockers b i, ¬ losLt b x k) →
      (k ∈ losWinnersWithout b i ↔
        ∀ r ∈ losWinners b, r ≠ i → losLt b r k → Disjoint (b k).bundle (b r).bundle) := by
  classical
  have hwf : WellFounded (losLt b) := losLt_wf b
  intro k
  induction k using hwf.induction with
  | h k ih =>
    intro hki hno
    have h_agree : ∀ r : N, r ≠ i → losLt b r k →
        (r ∈ losWinnersWithout b i ↔ r ∈ losWinners b) := by
      intro r hri hlt
      have hno_r : ∀ x ∈ losBlockers b i, ¬ losLt b x r :=
        fun x hx hxr => hno x hx (losLt_trans b hxr hlt)
      have heq := ih r hlt hri hno_r
      constructor
      · intro hrw
        have hdisj_i : Disjoint (b i).bundle (b r).bundle := by
          by_contra hnd
          exact hno r (Finset.mem_filter.2 ⟨hrw, hnd⟩) hlt
        refine (mem_losWinners_iff_earlier_winners b r).2 fun t ht htr => ?_
        by_cases hti : t = i
        · subst hti; exact hdisj_i.symm
        · exact heq.1 hrw t ht hti htr
      · intro hr
        refine heq.2 fun t ht hti htr => ?_
        exact (mem_losWinners_iff_earlier_winners b r).1 hr t ht htr
    rw [mem_losWinnersWithout_iff_earlier b hki]
    constructor
    · intro h r hr hri hlt
      exact h r ((h_agree r hri hlt).2 hr) hlt
    · intro h r hr hlt
      have hri : r ≠ i := losWinnersWithout_subset_ne b hr
      exact h r ((h_agree r hri hlt).1 hr) hri hlt

private theorem eq_div_sqrt_div {x a c : ℝ} (hc : 0 ≤ c) :
    (x / Real.sqrt c) * Real.sqrt a = x / Real.sqrt (c / a) := by
  rw [Real.sqrt_div hc, div_div_eq_mul_div, div_mul_eq_mul_div]

/-- Equivalence with the (corrected) displayed payment formula of [BlumrosenNisan2007],
Figure 11.1 (p. 274). A bidder `j ≠ i` is blocked solely by `i` when `S_i* ∩ S_j* ≠ ∅` and
`S_k* ∩ S_j* = ∅` for every **winner** `k ∈ losWinners b` with `k ≠ i` preceding `j`
(correcting the printed box's omission of `k ∈ W`). For `i ∈ losWinners b`, either such a `j`
exists and the earliest (`losLt b`-minimal) one satisfies
`losPayment b i = v_j* / √(|S_j*| / |S_i*|)`, or no such `j` exists and `losPayment b i = 0`. -/
theorem losPayment_eq_first_blocked {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M]
    (b : N → SingleMindedBid M) {i : N} (hwin : i ∈ losWinners b) :
    (∃ j : N, j ≠ i ∧ ¬ Disjoint (b i).bundle (b j).bundle ∧
        (∀ k ∈ losWinners b, k ≠ i → losLt b k j → Disjoint (b k).bundle (b j).bundle) ∧
        (∀ j', j' ≠ i → ¬ Disjoint (b i).bundle (b j').bundle →
          (∀ k ∈ losWinners b, k ≠ i → losLt b k j' → Disjoint (b k).bundle (b j').bundle) →
          j = j' ∨ losLt b j j') ∧
        losLt b i j ∧
        losPayment b i =
          (b j).value / Real.sqrt (((b j).bundle.card : ℝ) / ((b i).bundle.card : ℝ))) ∨
      ((∀ j : N, j ≠ i → ¬ Disjoint (b i).bundle (b j).bundle →
        ∃ k ∈ losWinners b, k ≠ i ∧ losLt b k j ∧ ¬ Disjoint (b k).bundle (b j).bundle) ∧
        losPayment b i = 0) := by
  classical
  have hwf : WellFounded (losLt b) := losLt_wf b
  by_cases hne : (losBlockers b i).Nonempty
  · left
    obtain ⟨j, hj_mem, hj_min⟩ := hwf.has_min (losBlockers b i : Set N) hne
    change j ∈ losBlockers b i at hj_mem
    have hj_w : j ∈ losWinnersWithout b i := (Finset.mem_filter.1 hj_mem).1
    have hnd_ij : ¬ Disjoint (b i).bundle (b j).bundle := (Finset.mem_filter.1 hj_mem).2
    have hji : j ≠ i := losWinnersWithout_subset_ne b hj_w
    have hno_j : ∀ x ∈ losBlockers b i, ¬ losLt b x j := fun x hx hlt => hj_min x hx hlt
    have hcond_j : ∀ k ∈ losWinners b, k ≠ i → losLt b k j →
        Disjoint (b k).bundle (b j).bundle := fun k hk hki hlt =>
      ((winners_agree_before_blocker b j hji hno_j).1 hj_w k hk hki hlt).symm
    have hmin_j : ∀ j', j' ≠ i → ¬ Disjoint (b i).bundle (b j').bundle →
        (∀ k ∈ losWinners b, k ≠ i → losLt b k j' → Disjoint (b k).bundle (b j').bundle) →
        j = j' ∨ losLt b j j' := by
      intro j' hj'i hnd' hcond'
      by_cases heq : j = j'
      · exact Or.inl heq
      · rcases losLt_total b heq with h | h
        · exact Or.inr h
        · exfalso
          have hno' : ∀ x ∈ losBlockers b i, ¬ losLt b x j' :=
            fun x hx hxj' => hj_min x hx (losLt_trans b hxj' h)
          have hj'w : j' ∈ losWinnersWithout b i :=
            (winners_agree_before_blocker b j' hj'i hno').2
              (fun k hk hki hlt => (hcond' k hk hki hlt).symm)
          exact hj_min j' (Finset.mem_filter.2 ⟨hj'w, hnd'⟩) h
    have hij_lt : losLt b i j := by
      rcases losLt_total b hji.symm with h | h
      · exact h
      · exfalso
        exact hnd_ij ((mem_losWinners_iff b i).1 hwin j hj_w h)
    have hmax_eq : ((losBlockers b i).image fun x => losScore (b x)).max' (hne.image _) =
        losScore (b j) := by
      refine le_antisymm ?_
        (Finset.le_max' ((losBlockers b i).image fun x => losScore (b x)) (losScore (b j))
          (Finset.mem_image_of_mem (fun x => losScore (b x)) hj_mem))
      refine Finset.max'_le _ _ _ fun r hr => ?_
      rcases Finset.mem_image.1 hr with ⟨x, hx, rfl⟩
      by_cases hxj : x = j
      · subst hxj; exact le_rfl
      · rcases losLt_total b hxj with hlt | hlt
        · exact (hj_min x hx hlt).elim
        · exact losScore_le_of_losLt hlt
    have hpay : losPayment b i =
        (b j).value / Real.sqrt (((b j).bundle.card : ℝ) / ((b i).bundle.card : ℝ)) := by
      simp only [losPayment, hwin, ↓reduceIte, hne, ↓reduceDIte, hmax_eq]
      exact eq_div_sqrt_div (Nat.cast_nonneg _)
    exact ⟨j, hji, hnd_ij, hcond_j, hmin_j, hij_lt, hpay⟩
  · right
    refine ⟨?_, ?_⟩
    · intro j hji hnd
      by_contra hall
      push Not at hall
      have hno : ∀ x ∈ losBlockers b i, ¬ losLt b x j :=
        fun x hx => (hne ⟨x, hx⟩).elim
      have hjw : j ∈ losWinnersWithout b i :=
        (winners_agree_before_blocker b j hji hno).2
          (fun k hk hki hlt => (hall k hk hki hlt).symm)
      exact hne ⟨j, Finset.mem_filter.2 ⟨hjw, hnd⟩⟩
    · simp only [losPayment, hwin, ↓reduceIte, hne, ↓reduceDIte]

/-- The LOS greedy mechanism is dominant-strategy incentive compatible ([BlumrosenNisan2007],
Theorem 11.8 / Lemma 11.9, pp. 273–275). -/
theorem losMechanism_isDSIC {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M] :
    (losMechanism (N := N) (M := M)).IsDSIC :=
  Mechanism.isDSIC_of_isWeakMonotone losMechanism_losersPayZero
    losWinners_isMonotone.isWeakMonotone
    (fun b hb _ hi => losPayment_eq_criticalValue b hb hi)

/-- The LOS greedy mechanism is individually rational. -/
theorem losMechanism_isIR {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M] :
    (losMechanism (N := N) (M := M)).IsIR :=
  Mechanism.isIR_of_hasCriticalPayments losMechanism_losersPayZero
    (fun b hb _ hi => losPayment_eq_criticalValue b hb hi)

/-- All payments in the LOS greedy mechanism are nonnegative on nonnegative bid profiles. -/
theorem losMechanism_hasNonnegPayment {N M : Type*} [Fintype N] [LinearOrder N] [DecidableEq M] :
    (losMechanism (N := N) (M := M)).HasNonnegPayment :=
  Mechanism.hasNonnegPayment_of_hasCriticalPayments losMechanism_losersPayZero
    (fun b hb _ hi => losPayment_eq_criticalValue b hb hi)

/-! ### The `√m`-approximation guarantee (Lemma 11.10, p. 275) -/

private theorem card_optBlocked_le {N M : Type*}
    {b : N → SingleMindedBid M} {opt : Finset N} (hopt : IsCompatible b opt) (i : N)
    {s : Finset N} (hs_sub : s ⊆ opt) (hs_hit : ∀ j ∈ s, ¬ Disjoint (b i).bundle (b j).bundle) :
    s.card ≤ (b i).bundle.card := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · simp
  · have hpick : ∀ j ∈ s, ∃ a ∈ (b i).bundle, a ∈ (b j).bundle := fun j hj =>
      Finset.not_disjoint_iff.1 (hs_hit j hj)
    choose f hf using fun j : {j // j ∈ s} => hpick j.1 j.2
    refine Finset.card_le_card_of_injOn
      (fun j => if hj : j ∈ s then f ⟨j, hj⟩ else f ⟨j₀, hj₀⟩) ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe] at hj ⊢
      simp only [hj, ↓reduceDIte]
      exact (hf ⟨j, hj⟩).1
    · intro j₁ hj₁ j₂ hj₂ heq
      simp only [Finset.mem_coe] at hj₁ hj₂
      simp only [hj₁, hj₂, ↓reduceDIte] at heq
      by_contra hne
      have hdisj : Disjoint (b j₁).bundle (b j₂).bundle :=
        hopt (hs_sub hj₁) (hs_sub hj₂) hne
      have hm1 := (hf ⟨j₁, hj₁⟩).2
      have hm2 := (hf ⟨j₂, hj₂⟩).2
      rw [heq] at hm1
      exact Finset.disjoint_left.1 hdisj hm1 hm2

private theorem sum_optBlocked_le {N M : Type*} [LinearOrder N] [Fintype M]
    (b : N → SingleMindedBid M) (hb : ∀ j, 0 ≤ (b j).value)
    {opt : Finset N} (hopt : IsCompatible b opt) {i : N} (hi_ne : (b i).bundle.Nonempty)
    {optI : Finset N} (hsub : optI ⊆ opt)
    (hspec : ∀ j ∈ optI, (i = j ∨ losLt b i j) ∧ ¬ Disjoint (b i).bundle (b j).bundle) :
    ∑ j ∈ optI, (b j).value ≤ Real.sqrt (Fintype.card M) * (b i).value := by
  have hsi_pos : 0 < Real.sqrt (b i).bundle.card :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 hi_ne.card_pos)
  -- Display (11.1) in [BlumrosenNisan2007], p. 275.
  have h11_1 : ∑ j ∈ optI, (b j).value ≤
      losScore (b i) * ∑ j ∈ optI, Real.sqrt (b j).bundle.card := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rcases hspec j hj with ⟨hle, hnd⟩
    have hj_ne : (b j).bundle.Nonempty := by
      rw [Finset.not_disjoint_iff] at hnd
      exact ⟨hnd.choose, hnd.choose_spec.2⟩
    have hsc_j_le : losScore (b j) ≤ losScore (b i) := by
      rcases hle with rfl | hlt
      · exact le_rfl
      · exact losScore_le_of_losLt hlt
    have hsj_pos : 0 < Real.sqrt (b j).bundle.card :=
      Real.sqrt_pos.2 (Nat.cast_pos.2 hj_ne.card_pos)
    calc (b j).value
        = losScore (b j) * Real.sqrt (b j).bundle.card := by
          unfold losScore; field_simp
      _ ≤ losScore (b i) * Real.sqrt (b j).bundle.card :=
          mul_le_mul_of_nonneg_right hsc_j_le hsj_pos.le
  -- Display (11.2) via Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`).
  have hcs_sq : (∑ j ∈ optI, Real.sqrt (b j).bundle.card) ^ 2 ≤
      (optI.card : ℝ) * ∑ j ∈ optI, ((b j).bundle.card : ℝ) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq optI
      (fun _ => (1 : ℝ)) (fun j => Real.sqrt (b j).bundle.card)
    simpa [Real.sq_sqrt (Nat.cast_nonneg _)] using hcs
  have hcard_optI : (optI.card : ℝ) ≤ (b i).bundle.card := by
    exact_mod_cast card_optBlocked_le hopt i hsub fun j hj => (hspec j hj).2
  have hcompatI : IsCompatible b optI := hopt.subset (Finset.coe_subset.2 hsub)
  have hsum_card : ∑ j ∈ optI, ((b j).bundle.card : ℝ) ≤ Fintype.card M := by
    exact_mod_cast hcompatI.sum_card_le
  have hcs_bound : ∑ j ∈ optI, Real.sqrt (b j).bundle.card ≤
      Real.sqrt (b i).bundle.card * Real.sqrt (Fintype.card M) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    refine Real.le_sqrt_of_sq_le ?_
    exact hcs_sq.trans (mul_le_mul hcard_optI hsum_card
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc ∑ j ∈ optI, (b j).value
      ≤ losScore (b i) * ∑ j ∈ optI, Real.sqrt (b j).bundle.card := h11_1
    _ ≤ losScore (b i) * (Real.sqrt (b i).bundle.card * Real.sqrt (Fintype.card M)) :=
        mul_le_mul_of_nonneg_left hcs_bound (div_nonneg (hb i) hsi_pos.le)
    _ = Real.sqrt (Fintype.card M) * (b i).value := by
        unfold losScore
        field_simp

/-- **Approximation ratio of the LOS greedy mechanism** ([BlumrosenNisan2007], Lemma 11.10, p. 275):
assuming at least one item (`[Nonempty M]`), the social welfare of *every* compatible winner set
`opt` is at most `√m` times the welfare of the greedy winner set `losWinners b`, where
`m = Fintype.card M`.

Empty desired bundles `S* = ∅` are handled seamlessly via `[Nonempty M]`: every empty-bundle bidder
enters `losWinners b` directly, contributing `v_i ≤ 1 * v_i ≤ √m * v_i`. When `M` is empty
(`m = 0`), a single positive bid for `∅` makes the literal inequality `v ≤ 0 * v` false (a witness
is checked in `CslibFrontierTests.GameTheory.SingleMinded`). -/
theorem losWinners_approx {N M : Type*} [Fintype N] [LinearOrder N] [Fintype M] [DecidableEq M]
    [Nonempty M] (b : N → SingleMindedBid M) (hb : ∀ i, 0 ≤ (b i).value)
    (opt : Finset N) (hopt : IsCompatible b opt) :
    ∑ i ∈ opt, (b i).value ≤ Real.sqrt (Fintype.card M) * ∑ i ∈ losWinners b, (b i).value := by
  classical
  set W := losWinners b
  set optEmpty := opt.filter fun j => (b j).bundle = ∅
  set optPos := opt.filter fun j => (b j).bundle.Nonempty
  set wEmpty := W.filter fun i => (b i).bundle = ∅
  set wPos := W.filter fun i => (b i).bundle.Nonempty
  have hsplit : ∀ s : Finset N, ∑ j ∈ s, (b j).value =
      ∑ j ∈ s.filter (fun j => (b j).bundle = ∅), (b j).value +
      ∑ j ∈ s.filter (fun j => (b j).bundle.Nonempty), (b j).value := fun s => by
    have hdisj : Disjoint (s.filter fun j => (b j).bundle = ∅)
        (s.filter fun j => (b j).bundle.Nonempty) :=
      Finset.disjoint_filter.2 fun _ _ he hne => hne.ne_empty he
    have hunion : s.filter (fun j => (b j).bundle = ∅) ∪
        s.filter (fun j => (b j).bundle.Nonempty) = s := by
      ext j
      simp only [Finset.mem_union, Finset.mem_filter, Finset.nonempty_iff_ne_empty]
      tauto
    rw [← Finset.sum_union hdisj, hunion]
  have hopt_part := hsplit opt
  have hW_part := hsplit W
  have hsubEmpty : optEmpty ⊆ wEmpty := fun j hj => by
    rcases Finset.mem_filter.1 hj with ⟨_, he⟩
    exact Finset.mem_filter.2 ⟨mem_losWinners_of_bundle_empty b he, he⟩
  have hsumEmpty : ∑ j ∈ optEmpty, (b j).value ≤ ∑ i ∈ wEmpty, (b i).value :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubEmpty fun i _ _ => hb i
  have hblock_exists : ∀ j ∈ optPos, ∃ i ∈ wPos,
      (i = j ∨ losLt b i j) ∧ ¬ Disjoint (b i).bundle (b j).bundle := by
    intro j hj
    rcases Finset.mem_filter.1 hj with ⟨_, hjne⟩
    by_cases hjW : j ∈ W
    · refine ⟨j, Finset.mem_filter.2 ⟨hjW, hjne⟩, Or.inl rfl, ?_⟩
      exact Finset.not_disjoint_iff.2 ⟨hjne.choose, hjne.choose_spec, hjne.choose_spec⟩
    · have hblock : ∃ i ∈ W, losLt b i j ∧ ¬ Disjoint (b j).bundle (b i).bundle := by
        by_contra hnone
        push Not at hnone
        exact hjW ((mem_losWinners_iff_earlier_winners b j).2 hnone)
      obtain ⟨i, hiW, hilt, hnd⟩ := hblock
      have hnd' : ¬ Disjoint (b i).bundle (b j).bundle := fun h => hnd h.symm
      have hine : (b i).bundle.Nonempty := by
        rw [Finset.not_disjoint_iff] at hnd'
        exact ⟨hnd'.choose, hnd'.choose_spec.1⟩
      exact ⟨i, Finset.mem_filter.2 ⟨hiW, hine⟩, Or.inr hilt, hnd'⟩
  let owner : N → N := fun j => if hj : j ∈ optPos then (hblock_exists j hj).choose else j
  have hmaps : ∀ j ∈ optPos, owner j ∈ wPos := fun j hj => by
    simp only [owner, hj, ↓reduceDIte]
    exact (hblock_exists j hj).choose_spec.1
  have hsumPos : ∑ j ∈ optPos, (b j).value ≤
      Real.sqrt (Fintype.card M) * ∑ i ∈ wPos, (b i).value := by
    calc ∑ j ∈ optPos, (b j).value
        = ∑ i ∈ wPos, ∑ j ∈ optPos with owner j = i, (b j).value :=
          (Finset.sum_fiberwise_of_maps_to hmaps fun j => (b j).value).symm
      _ ≤ ∑ i ∈ wPos, (Real.sqrt (Fintype.card M) * (b i).value) := by
          refine Finset.sum_le_sum fun i hi => sum_optBlocked_le b hb hopt
            (Finset.mem_filter.1 hi).2
            ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)) fun j hj => ?_
          rcases Finset.mem_filter.1 hj with ⟨hjPos, hown⟩
          simp only [owner, hjPos, ↓reduceDIte] at hown
          rw [← hown]
          exact (hblock_exists j hjPos).choose_spec.2
      _ = Real.sqrt (Fintype.card M) * ∑ i ∈ wPos, (b i).value :=
          (Finset.mul_sum _ _ _).symm
  have h1_le_sqrt : (1 : ℝ) ≤ Real.sqrt (Fintype.card M) := by
    have hm : (1 : ℝ) ≤ Fintype.card M := by exact_mod_cast Fintype.card_pos (α := M)
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hm
  have hwEmpty_nn : 0 ≤ ∑ i ∈ wEmpty, (b i).value := Finset.sum_nonneg fun i _ => hb i
  calc ∑ j ∈ opt, (b j).value
      = ∑ j ∈ optEmpty, (b j).value + ∑ j ∈ optPos, (b j).value := hopt_part
    _ ≤ ∑ i ∈ wEmpty, (b i).value + Real.sqrt (Fintype.card M) * ∑ i ∈ wPos, (b i).value :=
        add_le_add hsumEmpty hsumPos
    _ ≤ Real.sqrt (Fintype.card M) * ∑ i ∈ wEmpty, (b i).value +
        Real.sqrt (Fintype.card M) * ∑ i ∈ wPos, (b i).value := by
        nlinarith
    _ = Real.sqrt (Fintype.card M) * ∑ i ∈ W, (b i).value := by
        rw [← mul_add, ← hW_part]

end Cslib.GameTheory.CombinatorialAuction.SingleMinded
