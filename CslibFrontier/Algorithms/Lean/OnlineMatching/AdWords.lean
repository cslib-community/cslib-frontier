/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.MinMax
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic

/-!
# Online budgeted ad allocation (AdWords): Greedy and MSVV

This module formalizes the online budgeted ad allocation (AdWords) problem from
[Lahaie, Pennock, Saberi, and Vohra, *Sponsored Search Auctions*,
§28.4.1][LahaiePennockSaberiVohra2007] (pp. 707–711 and Exercise 28.6, p. 716):

* the offline fractional linear program relaxation (28.11) and its dual, weak duality,
  complementary slackness, and the equivalence between the keyword-multiplicity form (demands `r_i`)
  and the unit-demand arrival-sequence form (`r_t = 1`);
* the **Greedy** online algorithm in both truncated-spend (`greedyTruncRule`, capped bid
  `min (q j) (B j - s j)`, exact `1 / 2`-competitive whenever `b t j ≤ B j` with no small-bid
  assumption) and all-or-nothing (`greedyAllOrNothingRule`, reject if `s j + q j > B j`, exact
  `(1 - R) / (2 - R)`-competitive whenever `b t j ≤ R * B j` and `0 ≤ R ≤ 1`) models, plus the
  tight two-bidder worst-case family from p. 709;
* **Algorithm 1 (MSVV)** scaling bids by `φ(x) = 1 - exp (x - 1)` in both truncated-spend
  (`msvvTruncRule`, `(1 - exp (-1)) * exp (-R)`-competitive for all `R ≥ 0`) and all-or-nothing
  (`msvvAllOrNothingRule`, `(1 - exp (-1)) * (1 - R) * exp (-R)`-competitive for `0 ≤ R ≤ 1`)
  models, proved against arbitrary fractional LP solutions **without** assuming that `OPT` exhausts
  budgets (Exercise 28.6, p. 716), together with the `Filter.Tendsto` limits `→ 1 - exp (-1)` as
  `R → 0`;
* the continuous trade-off inequality (`msvvTrunc_tradeoff`, the continuous analogue of Lemma 28.4,
  display (28.13), p. 710) and the discrete `k`-bucket geometric-series step (`discretePhi_tradeoff`
  and `tendsto_discretePhi_zero`, displays (28.12)–(28.13), pp. 710–711).

## Model

An advertiser set `ι` (`[Fintype ι] [LinearOrder ι]`) has budgets `budget : ι → ℝ` (assumed
strictly positive in the competitive-ratio theorems). A keyword LP `LP κ ι` records bids
`bid : κ → ι → ℝ`, budgets `budget : ι → ℝ`, and keyword demands `demand : κ → ℝ`. Given a finite
query arrival sequence `b : Fin T → ι → ℝ`, the deterministic online algorithms maintain cumulative
spending `spent : ι → ℝ` via a shared step-runner (`spentAt`) and tie-break maximal scores toward
the smallest advertiser in `ι` using `argmaxOver`.

Because the online problem here deals with real-valued revenue maximization against a fractional LP
relaxation weighted by `Real.exp`, it is kept separate from `Cslib.DataStructure.Online.Problem`,
which models integer (`ℕ`-valued) step-cost minimization.

## Source mapping and discrepancies verified on the page images

Every locator below was verified on rendered page images of [LahaiePennockSaberiVohra2007]:

* **LP (28.11) and dual** (§28.4.1, p. 708): `LP`, `LP.IsPrimalFeasible`, `LP.IsDualFeasible`,
  `LP.primalObj_le_dualObj`, and `LP.complementarySlackness`.
* **Greedy `1/2` ratio** (§28.4.1, p. 709): without bounding `b t j ≤ B j`, the fractional LP
  (28.11) has integrality gap `n` (a single query where `n` unit-budget bidders each bid `n` has LP
  value `n` via `x t j = 1 / n`, while any online allocation collects at most `1`). With
  `b t j ≤ B j`, capped-bid truncated greedy achieves exact `1 / 2` (`greedyTrunc_competitive`).
  All-or-nothing greedy achieves the sharper bound `(1 - R) / (2 - R) ≥ (1 - R) / 2` under
  `b t j ≤ R * B j` and `0 ≤ R ≤ 1` (`greedyAllOrNothing_competitive`).
* **Two-bidder greedy example** (§28.4.1, p. 709): with `B₁ = B₂ = 2`, `b₁₁ = 2`, `b₁₂ = 2 - ε`,
  `b₂₁ = 2`, `b₂₂ = ε` (`0 < ε < 2`), the book states greedy earns `2 + ε` and that assigning
  query 2 to bidder 1 and query 1 to bidder 2 yields `4`. The true sum is `2 + (2 - ε) = 4 - ε`
  (certified optimal by a dual witness for `0 < ε ≤ 1`; for `1 < ε < 2`, `2 + ε > 4 - ε`). The
  ratio `(2 + ε) / (4 - ε)` still converges to `1 / 2` as `ε → 0`.
* **Algorithm 1 & Theorem 28.3 (upper bound half)** (§28.4.1, pp. 709–711) and **Exercise 28.6**
  (p. 716): the proof sketch in the book introduces discrete `k`-buckets `Φ(s)` (28.12) and assumes
  that the optimal solution exhausts all budgets; in addition, the second line of the aligned sum
  display on p. 710 prints `∑_{j=0}^i Φ(i)` where `∑_{j=0}^i Φ(j)` is intended. Here
  `msvvTrunc_competitive` and `msvvAllOrNothing_competitive` give exact, non-asymptotic finite-bid
  proofs via the continuous exponential primal-dual potential `β_j(f) = (exp f - 1) / (exp 1 - 1)`
  (without assuming budget exhaustion or `k`-discretization rounding).

## Open work and limitations

* **No optimality lower bound:** the remark preceding Theorem 28.3 on p. 709 ("no deterministic or
  randomized algorithm can achieve a better competitive ratio") is **not** formalized here; only
  the competitive-ratio guarantee (revenue lower bound) for Algorithm 1 is proved. The matching
  lower bound stays open under issue `#7789`.
* **No running-time claim:** the algorithms are pure noncomputable functions over `ℝ` using
  `Real.exp`; no Word-RAM or Turing-machine time bound is asserted.

## Main definitions

* `Cslib.Algorithms.Lean.OnlineMatching.AdWords.LP`: the offline LP relaxation (28.11), with
  `LP.IsPrimalFeasible`, `LP.IsDualFeasible`, `LP.primalObj`, `LP.dualObj`, `LP.unit`, and
  `LP.countLP`.
* `Cslib.Algorithms.Lean.OnlineMatching.AdWords.StepResult`, `argmaxOver`, `spentAt`, `finalSpent`,
  `revenue`, `choiceAt`, `paymentAt`: shared deterministic sequential allocation runner.
* `Cslib.Algorithms.Lean.OnlineMatching.AdWords.msvvWeight`: the discount function
  `φ(x) = 1 - Real.exp (x - 1)`.
* `Cslib.Algorithms.Lean.OnlineMatching.AdWords.greedyTruncRule`, `greedyAllOrNothingRule`,
  `msvvTruncRule`, `msvvAllOrNothingRule`: the four online allocation rules.
* `Cslib.Algorithms.Lean.OnlineMatching.AdWords.discretePhi`: the discrete tradeoff function
  `Φ(s) = 1 - (1 - 1 / k) ^ (k - s)` (display (28.12), p. 710).

## Main results

* `LP.primalObj_le_dualObj`: weak duality for Eq. (28.11).
* `LP.complementarySlackness`: complementary slackness at primal–dual optimality (p. 708).
* `LP.exists_unitPrimal_of_countLP`: correspondence between the keyword-frequency LP and the
  unit-demand arrival-sequence LP.
* `greedyTrunc_competitive`, `greedyAllOrNothing_competitive`: competitive ratios for Greedy
  (`1 / 2` exact; `(1 - R) / (2 - R)` all-or-nothing).
* `greedy_two_bidder_example`, `tendsto_two_bidder_ratio`: tight two-bidder instance (p. 709).
* `msvvTrunc_tradeoff`: continuous trade-off inequality (analogue of Lemma 28.4, display (28.13)).
* `msvvTrunc_competitive`, `msvvTrunc_competitive_countLP`: exact `(1 - exp (-1)) * exp (-R)`
  revenue guarantee for MSVV Algorithm 1 (truncated spend), including Exercise 28.6.
* `msvvAllOrNothing_competitive`, `msvvAllOrNothing_competitive_countLP`: exact
  `(1 - exp (-1)) * (1 - R) * exp (-R)` revenue guarantee for MSVV Algorithm 1 (all-or-nothing),
  including Exercise 28.6.
* `tendsto_greedyAllOrNothing_factor`, `tendsto_msvvTrunc_factor`,
  `tendsto_msvvAllOrNothing_factor`: small-bid asymptotic limits as `R → 0`.
* `discretePhi_tradeoff`, `discretePhi_tradeoff_zero`, `tendsto_discretePhi_zero`: the discrete
  geometric-series step of NRTV pp. 710–711 and its limit `1 - exp (-1)`.

## References

* [S. Lahaie, D. M. Pennock, A. Saberi, and R. V. Vohra, *Sponsored Search Auctions*, Ch. 28 in
  *Algorithmic Game Theory*][LahaiePennockSaberiVohra2007]
-/

public section

namespace Cslib.Algorithms.Lean.OnlineMatching.AdWords

open Finset

/-! ### Offline fractional LP relaxation (NRTV Eq. 28.11) -/

/-- The offline fractional linear program for the online budgeted ad allocation problem
([LahaiePennockSaberiVohra2007], §28.4.1, Eq. (28.11), p. 708): keywords `κ` with arrival
frequencies `demand`, advertisers `ι` with budgets `budget`, and bid matrix `bid`. -/
structure LP (κ ι : Type*) where
  /-- Advertiser bids: `bid i j` is advertiser `j`'s bid for one query of keyword `i`. -/
  bid : κ → ι → ℝ
  /-- Advertiser budgets `B_j`. -/
  budget : ι → ℝ
  /-- Keyword frequencies (number of queries) `r_i`. -/
  demand : κ → ℝ

namespace LP

section Core

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- Primal feasibility for the fractional allocation `x : κ → ι → ℝ` in
[LahaiePennockSaberiVohra2007], Eq. (28.11), p. 708. -/
structure IsPrimalFeasible (lp : LP κ ι) (x : κ → ι → ℝ) : Prop where
  /-- Nonnegativity: `x i j ≥ 0`. -/
  nonneg : ∀ i j, 0 ≤ x i j
  /-- Demand cap: total allocation of keyword `i` is at most `demand i`. -/
  demand_le : ∀ i, ∑ j, x i j ≤ lp.demand i
  /-- Budget cap: total charge to advertiser `j` is at most `budget j`. -/
  budget_le : ∀ j, ∑ i, lp.bid i j * x i j ≤ lp.budget j

/-- Dual feasibility for `(α, β)` in the dual of [LahaiePennockSaberiVohra2007], Eq. (28.11),
p. 708. -/
structure IsDualFeasible (lp : LP κ ι) (α : κ → ℝ) (β : ι → ℝ) : Prop where
  /-- Nonnegativity of keyword shadow prices `α i ≥ 0`. -/
  alpha_nonneg : ∀ i, 0 ≤ α i
  /-- Nonnegativity of budget shadow prices `β j ≥ 0`. -/
  beta_nonneg : ∀ j, 0 ≤ β j
  /-- Dual covering constraint: `α i + bid i j * β j ≥ bid i j`. -/
  bid_le : ∀ i j, lp.bid i j ≤ α i + lp.bid i j * β j

/-- Primal objective `∑ i, ∑ j, bid i j * x i j` of Eq. (28.11). -/
@[expose] def primalObj (lp : LP κ ι) (x : κ → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, lp.bid i j * x i j

/-- Dual objective `∑ j, budget j * β j + ∑ i, demand i * α i` of the dual of Eq. (28.11). -/
@[expose] def dualObj (lp : LP κ ι) (α : κ → ℝ) (β : ι → ℝ) : ℝ :=
  ∑ j, lp.budget j * β j + ∑ i, lp.demand i * α i

private theorem dual_sum_split {lp : LP κ ι} (x : κ → ι → ℝ) (α : κ → ℝ) (β : ι → ℝ) :
    ∑ i, ∑ j, (α i + lp.bid i j * β j) * x i j =
      (∑ j, (∑ i, lp.bid i j * x i j) * β j) + ∑ i, (∑ j, x i j) * α i := by
  calc
    ∑ i, ∑ j, (α i + lp.bid i j * β j) * x i j
        = (∑ i, ∑ j, α i * x i j) + ∑ i, ∑ j, lp.bid i j * β j * x i j := by
          simp_rw [add_mul, Finset.sum_add_distrib]
    _ = (∑ j, (∑ i, lp.bid i j * x i j) * β j) + ∑ i, (∑ j, x i j) * α i := by
          rw [add_comm, Finset.sum_comm]
          refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => ?_)
            (Finset.sum_congr rfl fun i _ => ?_)
          · rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
          · rw [← Finset.mul_sum, mul_comm]

/-- **Weak duality** for the AdWords LP relaxation Eq. (28.11)
([LahaiePennockSaberiVohra2007], §28.4.1, p. 708). -/
theorem primalObj_le_dualObj {lp : LP κ ι} {x : κ → ι → ℝ} {α : κ → ℝ} {β : ι → ℝ}
    (hx : lp.IsPrimalFeasible x) (hd : lp.IsDualFeasible α β) :
    lp.primalObj x ≤ lp.dualObj α β :=
  calc lp.primalObj x
      ≤ ∑ i, ∑ j, (α i + lp.bid i j * β j) * x i j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hd.bid_le i j) (hx.nonneg i j)
    _ = (∑ j, (∑ i, lp.bid i j * x i j) * β j) + ∑ i, (∑ j, x i j) * α i := dual_sum_split x α β
    _ ≤ lp.dualObj α β := add_le_add
        (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hx.budget_le j) (hd.beta_nonneg j))
        (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hx.demand_le i) (hd.alpha_nonneg i))

/-- **Complementary slackness** for Eq. (28.11) ([LahaiePennockSaberiVohra2007], §28.4.1, p. 708):
at primal–dual equality `primalObj x = dualObj α β`, every pair `(i, j)` with `x i j > 0`
satisfies `(1 - β j) * bid i j = α i` and maximizes `(1 - β k) * bid i k` over all advertisers
`k`. -/
theorem complementarySlackness {lp : LP κ ι} {x : κ → ι → ℝ} {α : κ → ℝ} {β : ι → ℝ}
    (hx : lp.IsPrimalFeasible x) (hd : lp.IsDualFeasible α β)
    (heq : lp.primalObj x = lp.dualObj α β) {i : κ} {j : ι} (hxpos : 0 < x i j) :
    (1 - β j) * lp.bid i j = α i ∧ ∀ k, (1 - β k) * lp.bid i k ≤ (1 - β j) * lp.bid i j := by
  have hslack (i' : κ) (j' : ι) : 0 ≤ (α i' + lp.bid i' j' * β j' - lp.bid i' j') * x i' j' :=
    mul_nonneg (sub_nonneg.mpr (hd.bid_le i' j')) (hx.nonneg i' j')
  have h2 : ∑ i', ∑ j', (α i' + lp.bid i' j' * β j') * x i' j' ≤ lp.dualObj α β := by
    rw [dual_sum_split]
    exact add_le_add
      (Finset.sum_le_sum fun j' _ =>
        mul_le_mul_of_nonneg_right (hx.budget_le j') (hd.beta_nonneg j'))
      (Finset.sum_le_sum fun i' _ =>
        mul_le_mul_of_nonneg_right (hx.demand_le i') (hd.alpha_nonneg i'))
  have hsum_zero : ∑ i', ∑ j', (α i' + lp.bid i' j' * β j' - lp.bid i' j') * x i' j' = 0 := by
    have hsub : ∑ i', ∑ j', (α i' + lp.bid i' j' * β j' - lp.bid i' j') * x i' j' =
        (∑ i', ∑ j', (α i' + lp.bid i' j' * β j') * x i' j') - lp.primalObj x := by
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      rfl
    exact le_antisymm (by linarith)
      (Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ => hslack i' j')
  have hi_zero := (Finset.sum_eq_zero_iff_of_nonneg fun i' _ =>
    Finset.sum_nonneg fun j' _ => hslack i' j').mp hsum_zero i (mem_univ i)
  have htight := (mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun j' _ =>
    hslack i j').mp hi_zero j (mem_univ j))).resolve_right hxpos.ne'
  refine ⟨by linarith, fun k => ?_⟩
  linarith [hd.bid_le i k]

end Core

/-- The unit-demand LP instance for a stream of `T` arriving queries with per-query bids
`bid : Fin T → ι → ℝ` (`demand t = 1` for every `t : Fin T`). -/
@[expose] def unit {T : ℕ} {ι : Type*} (bid : Fin T → ι → ℝ) (budget : ι → ℝ) :
    LP (Fin T) ι where
  bid := bid
  budget := budget
  demand := fun _ => 1

/-- The keyword-frequency LP relaxation Eq. (28.11) induced by a sequence `queries : Fin T → κ`
of arriving keywords: `demand i` is the number of arrivals `t : Fin T` with `queries t = i`. -/
@[expose] def countLP {T : ℕ} {κ ι : Type*} [DecidableEq κ] (bid : κ → ι → ℝ)
    (budget : ι → ℝ) (queries : Fin T → κ) : LP κ ι where
  bid := bid
  budget := budget
  demand i := ((univ.filter fun t : Fin T => queries t = i).card : ℝ)

/-- Every feasible fractional solution `x` to the keyword-frequency LP `countLP` spreads evenly
across matching arrival steps into a feasible solution `y` of the unit-demand LP `unit` with the
exact same primal objective value ([LahaiePennockSaberiVohra2007], §28.4.1, p. 708). -/
theorem exists_unitPrimal_of_countLP {T : ℕ} {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] {bid : κ → ι → ℝ} {budget : ι → ℝ} (queries : Fin T → κ) {x : κ → ι → ℝ}
    (hx : (countLP bid budget queries).IsPrimalFeasible x) :
    ∃ y : Fin T → ι → ℝ,
      (unit (fun t j => bid (queries t) j) budget).IsPrimalFeasible y ∧
        (unit (fun t j => bid (queries t) j) budget).primalObj y =
          (countLP bid budget queries).primalObj x := by
  let cnt : κ → ℕ := fun i => (univ.filter fun t : Fin T => queries t = i).card
  let y : Fin T → ι → ℝ := fun t j => x (queries t) j / (cnt (queries t) : ℝ)
  have hcnt_pos (t : Fin T) : 0 < cnt (queries t) :=
    Finset.card_pos.mpr ⟨t, mem_filter.mpr ⟨mem_univ t, rfl⟩⟩
  have hx_zero (i : κ) (hci : cnt i = 0) (j : ι) : x i j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j' _ => hx.nonneg i j').mp
      (le_antisymm (by simpa [countLP, cnt, hci] using hx.demand_le i)
        (Finset.sum_nonneg fun j' _ => hx.nonneg i j')) j (mem_univ j)
  have hsum_j (j : ι) : ∑ t : Fin T, bid (queries t) j * y t j = ∑ i : κ, bid i j * x i j := by
    calc ∑ t : Fin T, bid (queries t) j * y t j
        = ∑ i : κ, ∑ t ∈ univ.filter (fun t : Fin T => queries t = i),
            bid (queries t) j * y t j := by
          rw [← Finset.sum_fiberwise_of_maps_to (g := queries) (t := univ) (fun _ _ => mem_univ _)]
      _ = ∑ i : κ, bid i j * x i j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hconst : ∑ t ∈ univ.filter (fun t : Fin T => queries t = i),
              bid (queries t) j * y t j =
              (cnt i : ℝ) * (bid i j * (x i j / (cnt i : ℝ))) := by
            calc ∑ t ∈ univ.filter (fun t : Fin T => queries t = i), bid (queries t) j * y t j
                = ∑ _t ∈ univ.filter (fun t : Fin T => queries t = i),
                    bid i j * (x i j / (cnt i : ℝ)) :=
                  Finset.sum_congr rfl fun t ht => by
                    have hqt := (mem_filter.mp ht).2
                    simp only [y, hqt]
              _ = (cnt i : ℝ) * (bid i j * (x i j / (cnt i : ℝ))) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
          rw [hconst]
          rcases Nat.eq_zero_or_pos (cnt i) with h0 | hpos
          · simp [hx_zero i h0 j, h0]
          · have hne : (cnt i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
            field_simp [hne]
  refine ⟨y, ⟨fun _ _ => div_nonneg (hx.nonneg _ _) (Nat.cast_nonneg _), fun t => ?_,
    fun j => ?_⟩, ?_⟩
  · have hpos : (0 : ℝ) < cnt (queries t) := Nat.cast_pos.mpr (hcnt_pos t)
    calc ∑ j, y t j
        = (∑ j, x (queries t) j) / (cnt (queries t) : ℝ) := by simp only [y, Finset.sum_div]
      _ ≤ (cnt (queries t) : ℝ) / (cnt (queries t) : ℝ) :=
        div_le_div_of_nonneg_right (hx.demand_le (queries t)) hpos.le
      _ = 1 := div_self hpos.ne'
  · change ∑ t : Fin T, bid (queries t) j * y t j ≤ budget j
    rw [hsum_j j]
    exact hx.budget_le j
  · change ∑ t : Fin T, ∑ j, bid (queries t) j * y t j = ∑ i : κ, ∑ j, bid i j * x i j
    rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => bid i j * x i j)]
    exact Finset.sum_congr rfl fun j _ => hsum_j j

end LP

/-! ### Shared deterministic online allocation runner -/

/-- The deterministic `argmax` of `score : ι → ℝ` over a finite set `S : Finset ι`, breaking ties
toward the smallest advertiser in `[LinearOrder ι]`, or `none` if `S` is empty. -/
@[expose] noncomputable def argmaxOver {ι : Type*} [LinearOrder ι] (S : Finset ι)
    (score : ι → ℝ) : Option ι :=
  letI := Classical.decRel (fun a b : ℝ => a < b)
  (S.sort (· ≤ ·)).argmax score

private theorem argmaxOver_eq_none_iff {ι : Type*} [LinearOrder ι] (S : Finset ι)
    (score : ι → ℝ) : argmaxOver S score = none ↔ S = ∅ := by
  classical
  simp only [argmaxOver, List.argmax_eq_none, List.eq_nil_iff_forall_not_mem,
    Finset.mem_sort, Finset.eq_empty_iff_forall_notMem]

private theorem argmaxOver_mem {ι : Type*} [LinearOrder ι] {S : Finset ι} {score : ι → ℝ}
    {j : ι} (h : argmaxOver S score = some j) : j ∈ S := by
  classical
  exact (Finset.mem_sort (· ≤ ·)).mp
    (List.argmax_mem (l := S.sort (· ≤ ·)) (by simpa [argmaxOver] using h))

private theorem le_of_argmaxOver_eq_some {ι : Type*} [LinearOrder ι] {S : Finset ι}
    {score : ι → ℝ} {j k : ι} (h : argmaxOver S score = some j) (hk : k ∈ S) :
    score k ≤ score j := by
  classical
  exact List.le_of_mem_argmax ((Finset.mem_sort (· ≤ ·)).mpr hk)
    (by simpa [argmaxOver] using h)

private theorem exists_argmaxOver_of_mem {ι : Type*} [LinearOrder ι] {S : Finset ι}
    {score : ι → ℝ} {k : ι} (hk : k ∈ S) :
    ∃ j, argmaxOver S score = some j ∧ score k ≤ score j := by
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp
    (mt (argmaxOver_eq_none_iff S score).mp (Finset.Nonempty.ne_empty ⟨k, hk⟩))
  exact ⟨j, hj, le_of_argmaxOver_eq_some hj hk⟩

/-- Specification characterizing the exact tie-breaking choice `argmaxOver S score = some j`:
`j ∈ S`, `score j` maximizes `score` on `S`, and every strictly smaller `k ∈ S` has strictly
smaller score. -/
theorem argmaxOver_eq_some_iff {ι : Type*} [LinearOrder ι] {S : Finset ι} {score : ι → ℝ}
    {j : ι} :
    argmaxOver S score = some j ↔
      j ∈ S ∧ (∀ k ∈ S, score k ≤ score j) ∧ (∀ k ∈ S, k < j → score k < score j) := by
  classical
  set l := S.sort (· ≤ ·)
  have hsorted : l.Pairwise (· < ·) :=
    ((S.pairwise_sort (· ≤ ·)).and (S.sort_nodup (· ≤ ·))).imp fun h => lt_of_le_of_ne h.1 h.2
  have hlt_of_idx {a b : ι} (ha : a ∈ S) (hb : b ∈ S) (hlt : l.idxOf a < l.idxOf b) : a < b := by
    have ha' := List.idxOf_lt_length_of_mem ((Finset.mem_sort (· ≤ ·)).mpr ha)
    have hb' := List.idxOf_lt_length_of_mem ((Finset.mem_sort (· ≤ ·)).mpr hb)
    have hp := List.pairwise_iff_getElem.mp hsorted _ _ ha' hb' hlt
    rwa [List.getElem_idxOf ha', List.getElem_idxOf hb'] at hp
  have heq_of_idx {a b : ι} (ha : a ∈ S) (hb : b ∈ S) (heq : l.idxOf a = l.idxOf b) : a = b := by
    have ha' := List.idxOf_lt_length_of_mem ((Finset.mem_sort (· ≤ ·)).mpr ha)
    have hb' := List.idxOf_lt_length_of_mem ((Finset.mem_sort (· ≤ ·)).mpr hb)
    rw [← List.getElem_idxOf ha', ← List.getElem_idxOf hb']
    congr 1
  refine ⟨fun h => ⟨argmaxOver_mem h, fun _ hk => le_of_argmaxOver_eq_some h hk,
    fun k hk hkj => ?_⟩, fun ⟨hj, hmax, htie⟩ => ?_⟩
  · by_contra hnot
    have hidx := List.index_of_argmax (by simpa [argmaxOver, l] using h) (le_of_not_gt hnot)
    exact hidx.lt_or_eq.elim (fun hlt => (hlt_of_idx (argmaxOver_mem h) hk hlt).not_gt hkj)
      fun heq => hkj.ne' (heq_of_idx (argmaxOver_mem h) hk heq)
  · obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp
      (mt (argmaxOver_eq_none_iff S score).mp (Finset.Nonempty.ne_empty ⟨j, hj⟩))
    have hmS := argmaxOver_mem hm
    have hidx := List.index_of_argmax (by simpa [argmaxOver, l] using hm) (hmax m hmS)
    exact hidx.lt_or_eq.elim
      (fun hlt => absurd (htie m hmS (hlt_of_idx hmS hj hlt)) (not_lt_of_ge
        (le_of_argmaxOver_eq_some hm hj)))
      fun heq => heq_of_idx hmS hj heq ▸ hm

/-- One-step outcome produced by an online allocation rule on a single arriving query. -/
structure StepResult (ι : Type*) where
  /-- Advertiser selected to receive the query, or `none` if the query is left unallocated. -/
  choice : Option ι
  /-- Payment charged to `choice` (`0` when `choice = none`). -/
  payment : ℝ

/-- Update the cumulative spend vector `spent` with a single `StepResult`. -/
@[expose] def applyStep {ι : Type*} [DecidableEq ι] (spent : ι → ℝ) (res : StepResult ι) :
    ι → ℝ :=
  match res.choice with
  | none => spent
  | some j => Function.update spent j (spent j + res.payment)

/-- Type alias for a deterministic online allocation rule: given current cumulative spending
`spent : ι → ℝ` and the arriving query's bid vector `q : ι → ℝ`, return a `StepResult ι`. -/
abbrev AllocationRule (ι : Type*) := (ι → ℝ) → (ι → ℝ) → StepResult ι

private def spentAux {T : ℕ} {ι : Type*} [DecidableEq ι] (rule : AllocationRule ι)
    (b : Fin T → ι → ℝ) : (n : ℕ) → n ≤ T → ι → ℝ
  | 0, _ => 0
  | n + 1, hn =>
      let prev := spentAux rule b n (Nat.le_of_succ_le hn)
      applyStep prev (rule prev (b ⟨n, hn⟩))

/-- Cumulative spending vector after processing the first `t.val` queries (`t : Fin (T + 1)`). -/
def spentAt {T : ℕ} {ι : Type*} [DecidableEq ι] (rule : AllocationRule ι)
    (b : Fin T → ι → ℝ) (t : Fin (T + 1)) : ι → ℝ :=
  spentAux rule b t.val (Nat.le_of_lt_succ t.isLt)

/-- Cumulative spending vector after processing all `T` queries. -/
@[expose] def finalSpent {T : ℕ} {ι : Type*} [DecidableEq ι] (rule : AllocationRule ι)
    (b : Fin T → ι → ℝ) : ι → ℝ :=
  spentAt rule b (Fin.last T)

/-- Total online revenue collected after processing all `T` queries: `∑ j, finalSpent rule b j`. -/
@[expose] def revenue {T : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (rule : AllocationRule ι)
    (b : Fin T → ι → ℝ) : ℝ :=
  ∑ j, finalSpent rule b j

/-- Chosen advertiser at query arrival step `t : Fin T`. -/
@[expose] def choiceAt {T : ℕ} {ι : Type*} [DecidableEq ι] (rule : AllocationRule ι)
    (b : Fin T → ι → ℝ) (t : Fin T) : Option ι :=
  (rule (spentAt rule b t.castSucc) (b t)).choice

/-- Payment collected at query arrival step `t : Fin T`. -/
@[expose] def paymentAt {T : ℕ} {ι : Type*} [DecidableEq ι] (rule : AllocationRule ι)
    (b : Fin T → ι → ℝ) (t : Fin T) : ℝ :=
  (rule (spentAt rule b t.castSucc) (b t)).payment

/-- Initial spending vector before any queries arrive is identically zero. -/
@[simp] theorem spentAt_zero {T : ℕ} {ι : Type*} [DecidableEq ι] (rule : AllocationRule ι)
    (b : Fin T → ι → ℝ) : spentAt rule b 0 = 0 := by
  simp only [spentAt, Fin.val_zero, spentAux]

/-- One-step recurrence updating cumulative spending after processing query `t`. -/
@[simp] theorem spentAt_succ {T : ℕ} {ι : Type*} [DecidableEq ι] (rule : AllocationRule ι)
    (b : Fin T → ι → ℝ) (t : Fin T) :
    spentAt rule b t.succ =
      applyStep (spentAt rule b t.castSucc) (rule (spentAt rule b t.castSucc) (b t)) := by
  simp only [spentAt, Fin.val_succ, spentAux, Fin.val_castSucc, Fin.eta]

private theorem spentAt_mono {T : ℕ} {ι : Type*} [DecidableEq ι] {rule : AllocationRule ι}
    {b : Fin T → ι → ℝ} (hnonneg : ∀ t : Fin T, 0 ≤ paymentAt rule b t)
    {t₁ t₂ : Fin (T + 1)} (ht : t₁ ≤ t₂) (j : ι) :
    spentAt rule b t₁ j ≤ spentAt rule b t₂ j := by
  have aux (n : ℕ) (hn : n ≤ T) : ∀ m (hm : m ≤ n),
      spentAux rule b m (hm.trans hn) j ≤ spentAux rule b n hn j := by
    induction n with
    | zero =>
      rintro m hm
      obtain rfl := Nat.le_zero.mp hm
      exact le_rfl
    | succ k ih =>
      intro m hm
      rcases eq_or_lt_of_le hm with rfl | hlt
      · exact le_rfl
      · have hkT : k ≤ T := Nat.le_of_succ_le hn
        have hmk : m ≤ k := Nat.lt_succ_iff.mp hlt
        refine (ih hkT m hmk).trans ?_
        have hp : 0 ≤ (rule (spentAux rule b k hkT) (b ⟨k, hn⟩)).payment := hnonneg ⟨k, hn⟩
        change spentAux rule b k hkT j ≤ applyStep (spentAux rule b k hkT) (rule _ (b ⟨k, hn⟩)) j
        cases hch : (rule (spentAux rule b k hkT) (b ⟨k, hn⟩)).choice with
        | none => simp [applyStep, hch]
        | some j₀ =>
          by_cases hj : j = j₀
          · subst hj
            simp only [applyStep, hch, Function.update_self]; linarith
          · simp [applyStep, hch, hj]
  exact aux t₂.val (Nat.le_of_lt_succ t₂.isLt) t₁.val ht

private theorem spentAt_telescope {T : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rule : AllocationRule ι) (b : Fin T → ι → ℝ) (f : ι → ℝ → ℝ) :
    ∑ j, f j (finalSpent rule b j) - ∑ j, f j 0 =
      ∑ t : Fin T,
        match choiceAt rule b t with
        | none => 0
        | some j => f j (spentAt rule b t.succ j) - f j (spentAt rule b t.castSucc j) := by
  have step_diff (t : Fin T) :
      ∑ j, f j (spentAt rule b t.succ j) - ∑ j, f j (spentAt rule b t.castSucc j) =
        match choiceAt rule b t with
        | none => 0
        | some j => f j (spentAt rule b t.succ j) - f j (spentAt rule b t.castSucc j) := by
    rw [← Finset.sum_sub_distrib]
    cases hch : choiceAt rule b t with
    | none =>
      have hch' : (rule (spentAt rule b t.castSucc) (b t)).choice = none := hch
      exact Finset.sum_eq_zero fun j _ => by simp [spentAt_succ, applyStep, hch']
    | some j₀ =>
      have hch' : (rule (spentAt rule b t.castSucc) (b t)).choice = some j₀ := hch
      exact Finset.sum_eq_single j₀
        (fun j _ hj => by simp [spentAt_succ, applyStep, hch', hj])
        fun hmem => absurd (mem_univ j₀) hmem
  have htele (n : ℕ) (hn : n ≤ T) :
      ∑ j, f j (spentAux rule b n hn j) - ∑ j, f j 0 =
        ∑ k : Fin n, (∑ j, f j (spentAt rule b ⟨k.val + 1, by omega⟩ j) -
          ∑ j, f j (spentAt rule b ⟨k.val, by omega⟩ j)) := by
    induction n with
    | zero => simp [spentAux]
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      have hm : m ≤ T := Nat.le_of_succ_le hn
      have hcast (k : Fin m) : (k.castSucc : Fin (m + 1)).val = k.val := rfl
      have hml : ∑ j, f j (spentAux rule b m hm j) =
          ∑ j, f j (spentAt rule b ⟨m, Nat.lt_succ_of_le hm⟩ j) := rfl
      change (∑ j, f j (spentAt rule b ⟨m + 1, by omega⟩ j) - ∑ j, f j 0) =
        (∑ k : Fin m, _) +
          (∑ j, f j (spentAt rule b ⟨m + 1, by omega⟩ j) -
            ∑ j, f j (spentAt rule b ⟨m, by omega⟩ j))
      rw [← hml]
      simp_rw [hcast]
      linarith [ih hm]
  calc ∑ j, f j (finalSpent rule b j) - ∑ j, f j 0
      = ∑ k : Fin T, (∑ j, f j (spentAt rule b k.succ j) -
          ∑ j, f j (spentAt rule b k.castSucc j)) := htele T le_rfl
    _ = _ := Finset.sum_congr rfl fun t _ => step_diff t

/-- When an unallocated query always charges `0`, `revenue` equals the sum of per-step payments. -/
theorem revenue_eq_sum_paymentAt {T : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {rule : AllocationRule ι} {b : Fin T → ι → ℝ}
    (hnone : ∀ t : Fin T, choiceAt rule b t = none → paymentAt rule b t = 0) :
    revenue rule b = ∑ t : Fin T, paymentAt rule b t := by
  have ht := spentAt_telescope rule b (fun _ x => x)
  simp only [Finset.sum_const_zero, sub_zero] at ht
  refine ht.trans (Finset.sum_congr rfl fun t _ => ?_)
  cases hch : choiceAt rule b t with
  | none => exact (hnone t hch).symm
  | some j =>
    simp only [spentAt_succ, applyStep, choiceAt, paymentAt] at hch ⊢
    simp [hch]

/-! ### The four online allocation rules -/

/-- The MSVV trade-off function `φ(x) = 1 - exp (x - 1)`
([LahaiePennockSaberiVohra2007], §28.4.1, p. 709). -/
@[expose] noncomputable def msvvWeight (x : ℝ) : ℝ :=
  1 - Real.exp (x - 1)

/-- The MSVV trade-off weight `φ(x) = 1 - exp (x - 1)` is nonnegative for `x ≤ 1`. -/
theorem msvvWeight_nonneg {x : ℝ} (hx : x ≤ 1) : 0 ≤ msvvWeight x := by
  rw [msvvWeight, sub_nonneg, Real.exp_le_one_iff]
  linarith

/-- The MSVV trade-off weight `φ(x) = 1 - exp (x - 1)` is antitone (nonincreasing). -/
theorem msvvWeight_antitone : Antitone msvvWeight := by
  intro x y hxy
  rw [msvvWeight, msvvWeight]
  exact sub_le_sub_left (Real.exp_le_exp.mpr (sub_le_sub_right hxy 1)) 1

/-- Capped-bid truncated **Greedy** allocation rule: among advertisers with unexhausted budget
`s j < B j`, pick the one maximizing the effective payment `min (q j) (B j - s j)` (ties broken
toward the smallest advertiser), and charge that amount. Coincides with raw-bid Greedy whenever
the winning bid fits in remaining budget. -/
@[expose] noncomputable def greedyTruncRule {ι : Type*} [Fintype ι] [LinearOrder ι]
    (budget : ι → ℝ) : AllocationRule ι :=
  fun s q =>
    letI := Classical.decPred fun j : ι => s j < budget j
    match argmaxOver (univ.filter fun j => s j < budget j) (fun j => min (q j) (budget j - s j))
    with
    | none => ⟨none, 0⟩
    | some j => ⟨some j, min (q j) (budget j - s j)⟩

/-- All-or-nothing **Greedy** allocation rule: among advertisers whose remaining budget fits the
full bid (`s j + q j ≤ B j`), pick the one maximizing `q j` (ties broken toward the smallest
advertiser), and charge `q j`. -/
@[expose] noncomputable def greedyAllOrNothingRule {ι : Type*} [Fintype ι] [LinearOrder ι]
    (budget : ι → ℝ) : AllocationRule ι :=
  fun s q =>
    letI := Classical.decPred fun j : ι => s j + q j ≤ budget j
    match argmaxOver (univ.filter fun j => s j + q j ≤ budget j) q with
    | none => ⟨none, 0⟩
    | some j => ⟨some j, q j⟩

/-- **MSVV Algorithm 1** ([LahaiePennockSaberiVohra2007], §28.4.1, p. 709) with truncated spend:
among advertisers with unexhausted budget `s j < B j`, pick the one maximizing
`q j * msvvWeight (s j / B j)` (ties broken toward the smallest advertiser), and charge
`min (q j) (B j - s j)`. -/
@[expose] noncomputable def msvvTruncRule {ι : Type*} [Fintype ι] [LinearOrder ι]
    (budget : ι → ℝ) : AllocationRule ι :=
  fun s q =>
    letI := Classical.decPred fun j : ι => s j < budget j
    match argmaxOver (univ.filter fun j => s j < budget j)
        (fun j => q j * msvvWeight (s j / budget j)) with
    | none => ⟨none, 0⟩
    | some j => ⟨some j, min (q j) (budget j - s j)⟩

/-- **MSVV Algorithm 1** ([LahaiePennockSaberiVohra2007], §28.4.1, p. 709) with all-or-nothing
spend: among advertisers with remaining budget `s j + q j ≤ B j`, pick the one maximizing
`q j * msvvWeight (s j / B j)` (ties broken toward the smallest advertiser), and charge `q j`. -/
@[expose] noncomputable def msvvAllOrNothingRule {ι : Type*} [Fintype ι] [LinearOrder ι]
    (budget : ι → ℝ) : AllocationRule ι :=
  fun s q =>
    letI := Classical.decPred fun j : ι => s j + q j ≤ budget j
    match argmaxOver (univ.filter fun j => s j + q j ≤ budget j)
        (fun j => q j * msvvWeight (s j / budget j)) with
    | none => ⟨none, 0⟩
    | some j => ⟨some j, q j⟩

/-! ### Budget-safety invariants -/

private theorem trunc_invariant {T : ℕ} {ι : Type*} [DecidableEq ι]
    (budget : ι → ℝ) (hB : ∀ j, 0 ≤ budget j) (b : Fin T → ι → ℝ)
    (hb : ∀ t j, 0 ≤ b t j) (rule : AllocationRule ι)
    (hstep : ∀ s q,
      (∀ j, 0 ≤ s j ∧ s j ≤ budget j) → (∀ j, 0 ≤ q j) →
      match (rule s q).choice with
      | none => (rule s q).payment = 0
      | some j => 0 ≤ (rule s q).payment ∧ s j + (rule s q).payment ≤ budget j)
    (t : Fin (T + 1)) (j : ι) :
    0 ≤ spentAt rule b t j ∧ spentAt rule b t j ≤ budget j := by
  have aux (n : ℕ) (hn : n ≤ T) : ∀ j,
      0 ≤ spentAux rule b n hn j ∧ spentAux rule b n hn j ≤ budget j := by
    induction n with
    | zero => exact fun j => ⟨le_rfl, hB j⟩
    | succ m ih =>
      have hmT : m ≤ T := Nat.le_of_succ_le hn
      have hprev := ih hmT
      have hs := hstep (spentAux rule b m hmT) (b ⟨m, hn⟩) hprev (hb ⟨m, hn⟩)
      intro j
      change 0 ≤ applyStep (spentAux rule b m hmT) _ j ∧
        applyStep (spentAux rule b m hmT) _ j ≤ budget j
      cases hch : (rule (spentAux rule b m hmT) (b ⟨m, hn⟩)).choice with
      | none => simpa [applyStep, hch] using hprev j
      | some j₀ =>
        simp only [hch] at hs
        by_cases hj : j = j₀
        · subst hj
          simp only [applyStep, hch, Function.update_self]
          exact ⟨add_nonneg (hprev j).1 hs.1, hs.2⟩
        · simpa [applyStep, hch, hj] using hprev j
  exact aux t.val (Nat.le_of_lt_succ t.isLt) j

private theorem truncRule_bounds {ι : Type*} [Fintype ι] [LinearOrder ι] {budget : ι → ℝ}
    (score : (ι → ℝ) → (ι → ℝ) → ι → ℝ) {s q : ι → ℝ}
    (hs : ∀ j, 0 ≤ s j ∧ s j ≤ budget j) (hq : ∀ j, 0 ≤ q j) :
    letI := Classical.decPred fun j : ι => s j < budget j
    let res : StepResult ι :=
      match argmaxOver (univ.filter fun j => s j < budget j) (score s q) with
      | none => ⟨none, 0⟩
      | some j => ⟨some j, min (q j) (budget j - s j)⟩
    match res.choice with
    | none => res.payment = 0
    | some j => 0 ≤ res.payment ∧ s j + res.payment ≤ budget j := by
  classical
  cases h : argmaxOver (univ.filter fun j => s j < budget j) (score s q) with
  | none => rfl
  | some j =>
      refine ⟨le_min (hq j) (sub_nonneg.mpr (hs j).2), ?_⟩
      linarith [min_le_right (q j) (budget j - s j)]

private theorem aonRule_bounds {ι : Type*} [Fintype ι] [LinearOrder ι] {budget : ι → ℝ}
    (score : (ι → ℝ) → (ι → ℝ) → ι → ℝ) {s q : ι → ℝ} (hq : ∀ j, 0 ≤ q j) :
    letI := Classical.decPred fun j : ι => s j + q j ≤ budget j
    let res : StepResult ι :=
      match argmaxOver (univ.filter fun j => s j + q j ≤ budget j) (score s q) with
      | none => ⟨none, 0⟩
      | some j => ⟨some j, q j⟩
    match res.choice with
    | none => res.payment = 0
    | some j => 0 ≤ res.payment ∧ s j + res.payment ≤ budget j := by
  classical
  cases h : argmaxOver (univ.filter fun j => s j + q j ≤ budget j) (score s q) with
  | none => rfl
  | some j =>
      have hmem := (mem_filter.mp (argmaxOver_mem h)).2
      exact ⟨hq j, hmem⟩

private theorem paymentAt_nonneg_of_step {T : ℕ} {ι : Type*} [DecidableEq ι]
    {rule : AllocationRule ι} {budget : ι → ℝ} {b : Fin T → ι → ℝ}
    (hinv : ∀ t j, 0 ≤ spentAt rule b t j ∧ spentAt rule b t j ≤ budget j)
    (hb : ∀ t j, 0 ≤ b t j)
    (hstep : ∀ s q, (∀ j, 0 ≤ s j ∧ s j ≤ budget j) → (∀ j, 0 ≤ q j) →
      match (rule s q).choice with
      | none => (rule s q).payment = 0
      | some j => 0 ≤ (rule s q).payment ∧ s j + (rule s q).payment ≤ budget j)
    (t : Fin T) : 0 ≤ paymentAt rule b t := by
  have hs := hstep (spentAt rule b t.castSucc) (b t) (hinv t.castSucc) (hb t)
  change 0 ≤ (rule (spentAt rule b t.castSucc) (b t)).payment
  cases hch : (rule (spentAt rule b t.castSucc) (b t)).choice with
  | none => simp only [hch] at hs; linarith
  | some j => simp only [hch] at hs; exact hs.1

/-- `greedyTruncRule` keeps every advertiser's cumulative spending inside `[0, budget j]`. -/
theorem greedyTrunc_spent_mem {T : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Fin T → ι → ℝ} {budget : ι → ℝ} (hB : ∀ j, 0 ≤ budget j) (hb : ∀ t j, 0 ≤ b t j)
    (t : Fin (T + 1)) (j : ι) :
    0 ≤ spentAt (greedyTruncRule budget) b t j ∧
      spentAt (greedyTruncRule budget) b t j ≤ budget j :=
  trunc_invariant budget hB b hb _ (fun _ _ hs hq =>
    truncRule_bounds (budget := budget) (fun s q j => min (q j) (budget j - s j)) hs hq) t j

/-- `greedyAllOrNothingRule` keeps every advertiser's cumulative spending inside `[0, budget j]`. -/
theorem greedyAllOrNothing_spent_mem {T : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Fin T → ι → ℝ} {budget : ι → ℝ} (hB : ∀ j, 0 ≤ budget j) (hb : ∀ t j, 0 ≤ b t j)
    (t : Fin (T + 1)) (j : ι) :
    0 ≤ spentAt (greedyAllOrNothingRule budget) b t j ∧
      spentAt (greedyAllOrNothingRule budget) b t j ≤ budget j :=
  trunc_invariant budget hB b hb _ (fun _ _ _ hq =>
    aonRule_bounds (budget := budget) (fun _ q j => q j) hq) t j

/-- `msvvTruncRule` keeps every advertiser's cumulative spending inside `[0, budget j]`. -/
theorem msvvTrunc_spent_mem {T : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Fin T → ι → ℝ} {budget : ι → ℝ} (hB : ∀ j, 0 ≤ budget j) (hb : ∀ t j, 0 ≤ b t j)
    (t : Fin (T + 1)) (j : ι) :
    0 ≤ spentAt (msvvTruncRule budget) b t j ∧
      spentAt (msvvTruncRule budget) b t j ≤ budget j :=
  trunc_invariant budget hB b hb _ (fun _ _ hs hq =>
    truncRule_bounds (budget := budget)
      (fun s q j => q j * msvvWeight (s j / budget j)) hs hq) t j

/-- `msvvAllOrNothingRule` keeps every advertiser's cumulative spending inside `[0, budget j]`. -/
theorem msvvAllOrNothing_spent_mem {T : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Fin T → ι → ℝ} {budget : ι → ℝ} (hB : ∀ j, 0 ≤ budget j) (hb : ∀ t j, 0 ≤ b t j)
    (t : Fin (T + 1)) (j : ι) :
    0 ≤ spentAt (msvvAllOrNothingRule budget) b t j ∧
      spentAt (msvvAllOrNothingRule budget) b t j ≤ budget j :=
  trunc_invariant budget hB b hb _ (fun _ _ _ hq =>
    aonRule_bounds (budget := budget)
      (fun s q j => q j * msvvWeight (s j / budget j)) hq) t j

private theorem trunc_payment_eq_zero_of_none {ι : Type*} [Fintype ι] [LinearOrder ι]
    {budget : ι → ℝ} (score : (ι → ℝ) → (ι → ℝ) → ι → ℝ) {s q : ι → ℝ}
    (hnone :
      (letI := Classical.decPred fun j : ι => s j < budget j
       match argmaxOver (univ.filter fun j => s j < budget j) (score s q) with
       | none => (⟨none, 0⟩ : StepResult ι)
       | some j => ⟨some j, min (q j) (budget j - s j)⟩).choice = none) :
    (letI := Classical.decPred fun j : ι => s j < budget j
     match argmaxOver (univ.filter fun j => s j < budget j) (score s q) with
     | none => (⟨none, 0⟩ : StepResult ι)
     | some j => ⟨some j, min (q j) (budget j - s j)⟩).payment = 0 := by
  classical
  cases h : argmaxOver (univ.filter fun j => s j < budget j) (score s q) <;>
    simp_all

private theorem aon_payment_eq_zero_of_none {ι : Type*} [Fintype ι] [LinearOrder ι]
    {budget : ι → ℝ} (score : (ι → ℝ) → (ι → ℝ) → ι → ℝ) {s q : ι → ℝ}
    (hnone :
      (letI := Classical.decPred fun j : ι => s j + q j ≤ budget j
       match argmaxOver (univ.filter fun j => s j + q j ≤ budget j) (score s q) with
       | none => (⟨none, 0⟩ : StepResult ι)
       | some j => ⟨some j, q j⟩).choice = none) :
    (letI := Classical.decPred fun j : ι => s j + q j ≤ budget j
     match argmaxOver (univ.filter fun j => s j + q j ≤ budget j) (score s q) with
     | none => (⟨none, 0⟩ : StepResult ι)
     | some j => ⟨some j, q j⟩).payment = 0 := by
  classical
  cases h : argmaxOver (univ.filter fun j => s j + q j ≤ budget j) (score s q) <;>
    simp_all

/-! ### Greedy competitive ratios (NRTV §28.4.1, p. 709) -/

/-- Exact **`1 / 2`-competitive ratio** for capped-bid truncated **Greedy** against the offline
fractional LP relaxation (28.11) ([LahaiePennockSaberiVohra2007], §28.4.1, p. 709). Requires only
`0 ≤ b t j ≤ budget j` (no small-bid assumption and no assumption that `OPT` exhausts budgets). -/
theorem greedyTrunc_competitive {T : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Fin T → ι → ℝ} {budget : ι → ℝ} {x : Fin T → ι → ℝ}
    (hB : ∀ j, 0 < budget j) (hb0 : ∀ t j, 0 ≤ b t j) (hbB : ∀ t j, b t j ≤ budget j)
    (hx : (LP.unit b budget).IsPrimalFeasible x) :
    (LP.unit b budget).primalObj x ≤ 2 * revenue (greedyTruncRule budget) b := by
  classical
  set rule := greedyTruncRule budget
  have hinv : ∀ t j, 0 ≤ spentAt rule b t j ∧ spentAt rule b t j ≤ budget j :=
    greedyTrunc_spent_mem (fun j => (hB j).le) hb0
  have hpay_nonneg : ∀ t : Fin T, 0 ≤ paymentAt rule b t :=
    paymentAt_nonneg_of_step hinv hb0 fun _ _ hs hq =>
      truncRule_bounds (budget := budget) (fun s q j => min (q j) (budget j - s j)) hs hq
  let α : Fin T → ℝ := paymentAt rule b
  let β : ι → ℝ := fun j => finalSpent rule b j / budget j
  have hmono (t : Fin T) (j : ι) : spentAt rule b t.castSucc j ≤ finalSpent rule b j :=
    spentAt_mono hpay_nonneg (Fin.le_last t.castSucc) j
  have hdual : (LP.unit b budget).IsDualFeasible α β := by
    refine ⟨hpay_nonneg, fun j => div_nonneg (hinv _ j).1 (hB j).le, fun t j => ?_⟩
    have hrem : min (b t j) (budget j - finalSpent rule b j) ≤ α t := by
      rcases lt_or_ge (spentAt rule b t.castSucc j) (budget j) with hlt | hge
      · have hmem : j ∈ univ.filter fun k => spentAt rule b t.castSucc k < budget k :=
          mem_filter.mpr ⟨mem_univ j, hlt⟩
        obtain ⟨jstar, hjstar, hle⟩ := exists_argmaxOver_of_mem hmem
          (score := fun k => min (b t k) (budget k - spentAt rule b t.castSucc k))
        have hαeq : α t = min (b t jstar) (budget jstar - spentAt rule b t.castSucc jstar) := by
          change (greedyTruncRule budget (spentAt rule b t.castSucc) (b t)).payment = _
          simp only [greedyTruncRule, hjstar]
        exact hαeq ▸ (min_le_min_left (b t j) (sub_le_sub_left (hmono t j) _)).trans hle
      · have hfeq : finalSpent rule b j = budget j :=
          le_antisymm (hinv (Fin.last T) j).2 (hge.trans (hmono t j))
        rw [hfeq, sub_self]
        exact (min_le_right _ _).trans (hpay_nonneg t)
    have hprod_le : b t j * (1 - β j) ≤ min (b t j) (budget j - finalSpent rule b j) := by
      refine le_min ?_ ?_
      · have hβ0 : 0 ≤ β j := div_nonneg (hinv _ j).1 (hB j).le
        nlinarith [hb0 t j]
      · have hprod_eq : b t j * (1 - β j) =
            (b t j / budget j) * (budget j - finalSpent rule b j) := by
          simp only [β]
          field_simp [(hB j).ne']
        rw [hprod_eq]
        have hrem_nn : 0 ≤ budget j - finalSpent rule b j := sub_nonneg.mpr (hinv (Fin.last T) j).2
        nlinarith [(div_le_one (hB j)).mpr (hbB t j)]
    change b t j ≤ α t + b t j * β j
    linarith
  have hsumβ : ∑ j, budget j * β j = revenue rule b :=
    Finset.sum_congr rfl fun j _ => mul_div_cancel₀ _ (hB j).ne'
  have hsumα : ∑ t : Fin T, α t = revenue rule b := by
    refine (revenue_eq_sum_paymentAt fun t ht => ?_).symm
    exact trunc_payment_eq_zero_of_none (budget := budget)
      (fun s q j => min (q j) (budget j - s j))
      (by simpa [rule, choiceAt, greedyTruncRule] using ht)
  have hdobj : (LP.unit b budget).dualObj α β = 2 * revenue rule b := by
    change ∑ j, budget j * β j + ∑ t : Fin T, 1 * α t = _
    simp_rw [one_mul]
    linarith
  exact (LP.primalObj_le_dualObj hx hdual).trans_eq hdobj

/-- Exact **`(1 - R) / (2 - R)`-competitive ratio** for all-or-nothing **Greedy** against the
offline fractional LP relaxation (28.11) ([LahaiePennockSaberiVohra2007], §28.4.1, p. 709) when all
bids satisfy `b t j ≤ R * budget j` (`0 ≤ R ≤ 1`). Because `2 - R ≤ 2`, this is strictly tighter
than the standard `(1 - R) / 2` bound for non-zero `R`, and its factor tends to `1 / 2` as
`R → 0` (`tendsto_greedyAllOrNothing_factor`). -/
theorem greedyAllOrNothing_competitive {T : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Fin T → ι → ℝ} {budget : ι → ℝ} {x : Fin T → ι → ℝ} {R : ℝ}
    (hB : ∀ j, 0 < budget j) (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hb0 : ∀ t j, 0 ≤ b t j) (hbR : ∀ t j, b t j ≤ R * budget j)
    (hx : (LP.unit b budget).IsPrimalFeasible x) :
    (1 - R) * (LP.unit b budget).primalObj x ≤
      (2 - R) * revenue (greedyAllOrNothingRule budget) b := by
  classical
  set rule := greedyAllOrNothingRule budget
  have hinv : ∀ t j, 0 ≤ spentAt rule b t j ∧ spentAt rule b t j ≤ budget j :=
    greedyAllOrNothing_spent_mem (fun j => (hB j).le) hb0
  have hpay_nonneg : ∀ t : Fin T, 0 ≤ paymentAt rule b t :=
    paymentAt_nonneg_of_step hinv hb0 fun _ _ _ hq =>
      aonRule_bounds (budget := budget) (fun _ q j => q j) hq
  let α : Fin T → ℝ := paymentAt rule b
  let β : ι → ℝ := fun j => if (1 - R) * budget j < finalSpent rule b j then 1 else 0
  have hmono (t : Fin T) (j : ι) : spentAt rule b t.castSucc j ≤ finalSpent rule b j :=
    spentAt_mono hpay_nonneg (Fin.le_last t.castSucc) j
  have hdual : (LP.unit b budget).IsDualFeasible α β := by
    refine ⟨hpay_nonneg, fun j => by dsimp only [β]; split_ifs <;> norm_num, fun t j => ?_⟩
    by_cases hhigh : (1 - R) * budget j < finalSpent rule b j
    · change b t j ≤ α t + b t j * β j
      simp only [β, hhigh, ↓reduceIte, mul_one]; linarith [hpay_nonneg t]
    · have hmem : j ∈ univ.filter fun k => spentAt rule b t.castSucc k + b t k ≤ budget k :=
        mem_filter.mpr ⟨mem_univ j, by linarith [hmono t j, hbR t j]⟩
      obtain ⟨jstar, hjstar, hle⟩ := exists_argmaxOver_of_mem hmem (score := b t)
      have hαeq : α t = b t jstar := by
        change (greedyAllOrNothingRule budget (spentAt rule b t.castSucc) (b t)).payment = _
        simp only [greedyAllOrNothingRule, hjstar]
      change b t j ≤ α t + b t j * β j
      simpa [β, hhigh, hαeq] using hle
  have hsumβ : (1 - R) * ∑ j, budget j * β j ≤ revenue rule b := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    dsimp only [β]
    split_ifs with hhigh
    · linarith
    · simp only [mul_zero]
      exact (hinv (Fin.last T) j).1
  have hsumα : ∑ t : Fin T, α t = revenue rule b := by
    refine (revenue_eq_sum_paymentAt fun t ht => ?_).symm
    exact aon_payment_eq_zero_of_none (budget := budget) (fun _ q j => q j)
      (by simpa [rule, choiceAt, greedyAllOrNothingRule] using ht)
  have hdual_eq : (LP.unit b budget).dualObj α β = ∑ j, budget j * β j + revenue rule b := by
    change ∑ j, budget j * β j + ∑ t : Fin T, 1 * α t = _
    simp_rw [one_mul]
    rw [hsumα]
  have hrev_nn : 0 ≤ revenue rule b := Finset.sum_nonneg fun j _ => (hinv (Fin.last T) j).1
  nlinarith [mul_le_mul_of_nonneg_left (LP.primalObj_le_dualObj hx hdual) (sub_nonneg.mpr hR1)]

/-- As the bid-to-budget ratio `R → 0`, the all-or-nothing Greedy factor `(1 - R) / (2 - R)`
converges to `1 / 2`. -/
theorem tendsto_greedyAllOrNothing_factor :
    Filter.Tendsto (fun R : ℝ => (1 - R) / (2 - R)) (nhds 0) (nhds (1 / 2)) := by
  have hdiv : Filter.Tendsto (fun R : ℝ => (1 - R) / (2 - R)) (nhds 0)
      (nhds ((1 - 0) / (2 - 0))) :=
    (tendsto_const_nhds.sub Filter.tendsto_id).div
      (tendsto_const_nhds.sub Filter.tendsto_id) (by norm_num)
  norm_num at hdiv
  exact hdiv

/-! ### Tight two-bidder worst-case example for Greedy (NRTV p. 709) -/

/-- The bid matrix for the two-bidder Greedy lower-bound example
([LahaiePennockSaberiVohra2007], §28.4.1, p. 709): `b 0 = ![2, 2 - ε]`, `b 1 = ![2, ε]`. -/
@[expose] def twoBidderBids (ε : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![2, 2 - ε], ![2, ε]]

/-- Equal advertiser budgets `B = ![2, 2]` for the two-bidder example. -/
@[expose] def twoBidderBudget : Fin 2 → ℝ := ![2, 2]

/-- The off-diagonal integral allocation `x 0 = ![0, 1]`, `x 1 = ![1, 0]` assigning query 1 to
bidder 2 and query 2 to bidder 1. -/
@[expose] def twoBidderOptAlloc : Fin 2 → Fin 2 → ℝ :=
  ![![0, 1], ![1, 0]]

/-- **Tightness of the `1/2` ratio for Greedy** ([LahaiePennockSaberiVohra2007], §28.4.1, p. 709):
for `0 < ε < 2` with `B = ![2, 2]`, `b₁₁ = 2`, `b₁₂ = 2 - ε`, `b₂₁ = 2`, `b₂₂ = ε`:
1. Both `greedyTruncRule` and `greedyAllOrNothingRule` earn `2 + ε`.
2. `twoBidderOptAlloc` is LP-feasible and attains revenue **`4 - ε`** (correcting the printed `4`
   on NRTV p. 709).
3. For `0 < ε ≤ 1`, `4 - ε` is **exact LP-optimal** (every feasible fractional LP solution `x`
   has `primalObj x ≤ 4 - ε`, certified by the dual witness `α = ![2 - ε, ε]`,
   `β = ![1 - ε / 2, 0]`). -/
theorem greedy_two_bidder_example {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε < 2) :
    revenue (greedyTruncRule twoBidderBudget) (twoBidderBids ε) = 2 + ε ∧
      revenue (greedyAllOrNothingRule twoBidderBudget) (twoBidderBids ε) = 2 + ε ∧
      (LP.unit (twoBidderBids ε) twoBidderBudget).IsPrimalFeasible twoBidderOptAlloc ∧
      (LP.unit (twoBidderBids ε) twoBidderBudget).primalObj twoBidderOptAlloc = 4 - ε ∧
      (ε ≤ 1 → ∀ x, (LP.unit (twoBidderBids ε) twoBidderBudget).IsPrimalFeasible x →
        (LP.unit (twoBidderBids ε) twoBidderBudget).primalObj x ≤ 4 - ε) := by
  classical
  have htrunc0 : greedyTruncRule twoBidderBudget 0 (twoBidderBids ε 0) = ⟨some 0, 2⟩ := by
    have harg : argmaxOver (univ.filter fun j : Fin 2 => (0 : Fin 2 → ℝ) j < twoBidderBudget j)
        (fun j => min (twoBidderBids ε 0 j) (twoBidderBudget j - (0 : Fin 2 → ℝ) j)) = some 0 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num [twoBidderBudget]⟩,
        fun k _ => ?_, fun k _ hlt => absurd hlt (Fin.not_lt_zero k)⟩
      fin_cases k
      · exact le_rfl
      · change min (2 - ε) (2 - 0) ≤ min (2 : ℝ) (2 - 0)
        simp only [sub_zero, min_self]
        exact min_le_of_left_le (by linarith)
    simp only [greedyTruncRule, harg]
    change (⟨some 0, min (2 : ℝ) (2 - 0)⟩ : StepResult (Fin 2)) = ⟨some 0, 2⟩
    simp only [sub_zero, min_self]
  have hs1_t : spentAt (greedyTruncRule twoBidderBudget) (twoBidderBids ε) 1 = ![2, 0] := by
    funext j
    change spentAt _ _ (Fin.succ 0) j = _
    rw [spentAt_succ]
    fin_cases j <;> simp [Fin.castSucc_zero, spentAt_zero, htrunc0, applyStep, Function.update]
  have htrunc1 : greedyTruncRule twoBidderBudget ![2, 0] (twoBidderBids ε 1) = ⟨some 1, ε⟩ := by
    have harg : argmaxOver
        (univ.filter fun j : Fin 2 => (![2, 0] : Fin 2 → ℝ) j < twoBidderBudget j)
        (fun j => min (twoBidderBids ε 1 j) (twoBidderBudget j - (![2, 0] : Fin 2 → ℝ) j)) =
        some 1 := by
      rw [argmaxOver_eq_some_iff]
      have h1only (k : Fin 2) (hk : k ∈ univ.filter fun j : Fin 2 =>
          (![2, 0] : Fin 2 → ℝ) j < twoBidderBudget j) : k = 1 := by
        have hk' := (mem_filter.mp hk).2
        fin_cases k
        · norm_num [twoBidderBudget] at hk'
        · rfl
      exact ⟨mem_filter.mpr ⟨mem_univ 1, by norm_num [twoBidderBudget]⟩,
        fun k hk => by rw [h1only k hk], fun k hk hlt => absurd (h1only k hk ▸ hlt) (lt_irrefl 1)⟩
    simp only [greedyTruncRule, harg]
    change (⟨some 1, min ε (2 - 0)⟩ : StepResult (Fin 2)) = ⟨some 1, ε⟩
    simp only [sub_zero, min_eq_left hε2.le]
  have hrev_t : revenue (greedyTruncRule twoBidderBudget) (twoBidderBids ε) = 2 + ε := by
    have hfin : finalSpent (greedyTruncRule twoBidderBudget) (twoBidderBids ε) = ![2, ε] := by
      funext j
      change spentAt _ _ (Fin.succ 1) j = _
      have hcs : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
      rw [spentAt_succ, hcs, hs1_t, htrunc1]
      fin_cases j <;> simp [applyStep, Function.update]
    simp only [revenue, hfin, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have haon0 : greedyAllOrNothingRule twoBidderBudget 0 (twoBidderBids ε 0) = ⟨some 0, 2⟩ := by
    have harg : argmaxOver (univ.filter fun j : Fin 2 =>
        (0 : Fin 2 → ℝ) j + twoBidderBids ε 0 j ≤ twoBidderBudget j) (twoBidderBids ε 0) =
        some 0 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num [twoBidderBids, twoBidderBudget]⟩,
        fun k _ => ?_, fun k _ hlt => absurd hlt (Fin.not_lt_zero k)⟩
      fin_cases k
      · exact le_rfl
      · change (2 - ε : ℝ) ≤ 2
        linarith
    simp only [greedyAllOrNothingRule, harg]
    rfl
  have hs1_a : spentAt (greedyAllOrNothingRule twoBidderBudget) (twoBidderBids ε) 1 = ![2, 0] := by
    funext j
    change spentAt _ _ (Fin.succ 0) j = _
    rw [spentAt_succ]
    fin_cases j <;> simp [Fin.castSucc_zero, spentAt_zero, haon0, applyStep, Function.update]
  have haon1 : greedyAllOrNothingRule twoBidderBudget ![2, 0] (twoBidderBids ε 1) =
      ⟨some 1, ε⟩ := by
    have harg : argmaxOver (univ.filter fun j : Fin 2 =>
        (![2, 0] : Fin 2 → ℝ) j + twoBidderBids ε 1 j ≤ twoBidderBudget j) (twoBidderBids ε 1) =
        some 1 := by
      rw [argmaxOver_eq_some_iff]
      have h1only (k : Fin 2) (hk : k ∈ univ.filter fun j : Fin 2 =>
          (![2, 0] : Fin 2 → ℝ) j + twoBidderBids ε 1 j ≤ twoBidderBudget j) : k = 1 := by
        have hk' := (mem_filter.mp hk).2
        fin_cases k
        · norm_num [twoBidderBids, twoBidderBudget] at hk'
        · rfl
      refine ⟨mem_filter.mpr ⟨mem_univ 1, ?_⟩,
        fun k hk => by rw [h1only k hk], fun k hk hlt => absurd (h1only k hk ▸ hlt) (lt_irrefl 1)⟩
      change (0 + ε : ℝ) ≤ 2
      linarith
    simp only [greedyAllOrNothingRule, harg]
    rfl
  have hrev_a : revenue (greedyAllOrNothingRule twoBidderBudget) (twoBidderBids ε) = 2 + ε := by
    have hfin : finalSpent (greedyAllOrNothingRule twoBidderBudget) (twoBidderBids ε) =
        ![2, ε] := by
      funext j
      change spentAt _ _ (Fin.succ 1) j = _
      have hcs : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
      rw [spentAt_succ, hcs, hs1_a, haon1]
      fin_cases j <;> simp [applyStep, Function.update]
    simp only [revenue, hfin, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hfeas : (LP.unit (twoBidderBids ε) twoBidderBudget).IsPrimalFeasible twoBidderOptAlloc := by
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · fin_cases i <;> fin_cases j <;> norm_num [twoBidderOptAlloc]
    · fin_cases i <;> norm_num [LP.unit, twoBidderOptAlloc, Fin.sum_univ_two]
    · fin_cases j
      · norm_num [LP.unit, twoBidderBids, twoBidderBudget, twoBidderOptAlloc, Fin.sum_univ_two]
      · rw [Fin.sum_univ_two]
        change (2 - ε) * 1 + ε * 0 ≤ 2
        linarith
  have hval : (LP.unit (twoBidderBids ε) twoBidderBudget).primalObj twoBidderOptAlloc = 4 - ε := by
    simp only [LP.primalObj, Fin.sum_univ_two]
    change (2 * 0 + (2 - ε) * 1) + (2 * 1 + ε * 0) = 4 - ε
    ring
  refine ⟨hrev_t, hrev_a, hfeas, hval, fun hε1 x hx => ?_⟩
  let α : Fin 2 → ℝ := ![2 - ε, ε]
  let β : Fin 2 → ℝ := ![1 - ε / 2, 0]
  have hd : (LP.unit (twoBidderBids ε) twoBidderBudget).IsDualFeasible α β := by
    refine ⟨fun i => ?_, fun j => ?_, fun i j => ?_⟩
    · fin_cases i
      · change (0 : ℝ) ≤ 2 - ε; linarith
      · change (0 : ℝ) ≤ ε; linarith
    · fin_cases j
      · change (0 : ℝ) ≤ 1 - ε / 2; linarith
      · exact le_rfl
    · fin_cases i <;> fin_cases j
      · change (2 : ℝ) ≤ (2 - ε) + 2 * (1 - ε / 2); linarith
      · change (2 - ε : ℝ) ≤ (2 - ε) + (2 - ε) * 0; linarith
      · change (2 : ℝ) ≤ ε + 2 * (1 - ε / 2); linarith
      · change (ε : ℝ) ≤ ε + ε * 0; linarith
  have hdobj : (LP.unit (twoBidderBids ε) twoBidderBudget).dualObj α β = 4 - ε := by
    simp only [LP.dualObj, Fin.sum_univ_two]
    change (2 * (1 - ε / 2) + 2 * 0) + (1 * (2 - ε) + 1 * ε) = 4 - ε
    ring
  exact (LP.primalObj_le_dualObj hx hd).trans_eq hdobj

/-- The ratio `(2 + ε) / (4 - ε)` of the two-bidder greedy revenue to its true optimum `4 - ε`
converges to `1 / 2` as `ε → 0`. -/
theorem tendsto_two_bidder_ratio :
    Filter.Tendsto (fun ε : ℝ => (2 + ε) / (4 - ε)) (nhds 0) (nhds (1 / 2)) := by
  have hdiv : Filter.Tendsto (fun ε : ℝ => (2 + ε) / (4 - ε)) (nhds 0)
      (nhds ((2 + 0) / (4 - 0))) :=
    (tendsto_const_nhds.add Filter.tendsto_id).div
      (tendsto_const_nhds.sub Filter.tendsto_id) (by norm_num)
  norm_num at hdiv
  exact hdiv

/-! ### Exponential inequalities for the primal-dual MSVV proof -/

private theorem exp_sub_one_le_mul_exp (u : ℝ) : Real.exp u - 1 ≤ u * Real.exp u := by
  have hmul := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u)) (Real.exp_pos u).le
  rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos u).ne'] at hmul
  linarith

private theorem one_sub_exp_neg_le (u : ℝ) : 1 - Real.exp (-u) ≤ u := by
  linarith [Real.add_one_le_exp (-u)]

private theorem exp_one_sub_one_pos : 0 < Real.exp 1 - 1 :=
  sub_pos.mpr (Real.one_lt_exp_iff.mpr one_pos)

private theorem one_sub_exp_neg_one_pos : 0 < 1 - Real.exp (-1) :=
  sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))

private theorem msvv_rescale_le {a r R : ℝ}
    (h : a ≤ r * (Real.exp 1 / (Real.exp 1 - 1)) * Real.exp R) :
    (1 - Real.exp (-1)) * Real.exp (-R) * a ≤ r := by
  have hc_pos : 0 < 1 - Real.exp (-1) := one_sub_exp_neg_one_pos
  have hden_pos : 0 < Real.exp 1 - 1 := exp_one_sub_one_pos
  have hfactor : Real.exp 1 / (Real.exp 1 - 1) = (1 - Real.exp (-1))⁻¹ := by
    have hex : Real.exp 1 * Real.exp (-1) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [eq_comm, inv_eq_iff_eq_inv, inv_div]
    field_simp [hden_pos.ne', (Real.exp_pos 1).ne']
    linarith
  have hmul := mul_le_mul_of_nonneg_left h (mul_pos hc_pos (Real.exp_pos (-R))).le
  have hRcan : Real.exp (-R) * Real.exp R = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hcancel : (1 - Real.exp (-1)) * Real.exp (-R) *
      (r * (Real.exp 1 / (Real.exp 1 - 1)) * Real.exp R) = r := by
    rw [hfactor]
    calc
      (1 - Real.exp (-1)) * Real.exp (-R) * (r * (1 - Real.exp (-1))⁻¹ * Real.exp R)
          = r * ((1 - Real.exp (-1)) * (1 - Real.exp (-1))⁻¹) *
              (Real.exp (-R) * Real.exp R) := by ring
      _ = r := by rw [mul_inv_cancel₀ hc_pos.ne', hRcan, mul_one, mul_one]
  linarith [hmul, hcancel]

private theorem msvvWeight_eq_dual_factor (x : ℝ) :
    msvvWeight x / (1 - Real.exp (-1)) = (Real.exp 1 - Real.exp x) / (Real.exp 1 - 1) := by
  rw [msvvWeight, div_eq_div_iff one_sub_exp_neg_one_pos.ne' exp_one_sub_one_pos.ne']
  have hex1 : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hex2 : Real.exp 1 * Real.exp (x - 1) = Real.exp x := by
    rw [← Real.exp_add, add_sub_cancel]
  have hex3 : Real.exp x * Real.exp (-1) = Real.exp (x - 1) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  linear_combination hex1 - hex2 - hex3

/-- One-step numerator bound for the exponential primal-dual potential `β(f) = (e^f - 1)/(e - 1)`:
both non-truncating (`pay = bid ≤ B - s`) and truncating (`pay = B - s < bid`) steps satisfy the
same inequality with constant `exp 1 * exp R`. -/
private theorem msvv_step_numerator_le {B s bid R : ℝ} (hB : 0 < B) (hsB : s ≤ B)
    (hbid0 : 0 ≤ bid) (hbidR : bid ≤ R * B) :
    let pay := min bid (B - s)
    let f := s / B
    let f' := (s + pay) / B
    bid * (Real.exp 1 - Real.exp f) + B * (Real.exp f' - Real.exp f) ≤
      pay * Real.exp 1 * Real.exp R := by
  intro pay f f'
  have hf_le : f ≤ 1 := (div_le_one hB).mpr hsB
  by_cases hfit : bid ≤ B - s
  · have hpay : pay = bid := min_eq_left hfit
    set u := bid / B
    have hu0 : 0 ≤ u := div_nonneg hbid0 hB.le
    have huR : u ≤ R := (div_le_iff₀ hB).mpr hbidR
    have hf' : f' = f + u := by
      simp only [f', f, hpay, u, add_div]
    have hstep_exp : Real.exp f' - Real.exp f = Real.exp f * (Real.exp u - 1) := by
      rw [hf', Real.exp_add]
      ring
    have hsub1 : B * (Real.exp f' - Real.exp f) ≤ bid * Real.exp f * Real.exp u := by
      rw [hstep_exp]
      have heq : B * (Real.exp f * (u * Real.exp u)) = bid * Real.exp f * Real.exp u := by
        simp only [u]
        field_simp [hB.ne']
      linarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp u) (Real.exp_pos f).le) hB.le]
    have hbound2 : Real.exp 1 + Real.exp f * (Real.exp u - 1) ≤ Real.exp 1 * Real.exp u := by
      have := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hf_le)
        (sub_nonneg.mpr (Real.one_le_exp hu0))
      linarith
    calc
      bid * (Real.exp 1 - Real.exp f) + B * (Real.exp f' - Real.exp f)
          ≤ bid * (Real.exp 1 - Real.exp f) + bid * Real.exp f * Real.exp u := by linarith
      _ = bid * (Real.exp 1 + Real.exp f * (Real.exp u - 1)) := by ring
      _ ≤ bid * (Real.exp 1 * Real.exp u) := mul_le_mul_of_nonneg_left hbound2 hbid0
      _ ≤ bid * (Real.exp 1 * Real.exp R) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr huR) (Real.exp_pos 1).le) hbid0
      _ = pay * Real.exp 1 * Real.exp R := by rw [hpay]; ring
  · have hpay : pay = B - s := min_eq_right (le_of_not_ge hfit)
    have hpay0 : 0 ≤ pay := by rw [hpay]; linarith
    have hf' : f' = 1 := by
      simp only [f', hpay]
      rw [add_sub_cancel, div_self hB.ne']
    have hrem : 1 - f = pay / B := by
      simp only [f, hpay]
      field_simp [hB.ne']
    have hdiff_exp : Real.exp 1 - Real.exp f ≤ Real.exp 1 * (1 - f) := by
      have hexp : Real.exp f = Real.exp 1 * Real.exp (-(1 - f)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      nlinarith [one_sub_exp_neg_le (1 - f), (Real.exp_pos 1).le]
    have hdiff_pay : B * (Real.exp 1 - Real.exp f) ≤ pay * Real.exp 1 := by
      have h1 := mul_le_mul_of_nonneg_left hdiff_exp hB.le
      rw [hrem] at h1
      have h2 : B * (Real.exp 1 * (pay / B)) = pay * Real.exp 1 := by
        field_simp [hB.ne']
      linarith
    have hbid_term : bid * (Real.exp 1 - Real.exp f) ≤ R * pay * Real.exp 1 := by
      have h1 := mul_le_mul_of_nonneg_right hbidR (sub_nonneg.mpr (Real.exp_le_exp.mpr hf_le))
      have hR0 : 0 ≤ R := by nlinarith
      linarith [mul_le_mul_of_nonneg_left hdiff_pay hR0]
    rw [hf']
    calc
      bid * (Real.exp 1 - Real.exp f) + B * (Real.exp 1 - Real.exp f)
          ≤ R * pay * Real.exp 1 + pay * Real.exp 1 := by linarith
      _ = (R + 1) * (pay * Real.exp 1) := by ring
      _ ≤ Real.exp R * (pay * Real.exp 1) :=
          mul_le_mul_of_nonneg_right (Real.add_one_le_exp R)
            (mul_nonneg hpay0 (Real.exp_pos 1).le)
      _ = pay * Real.exp 1 * Real.exp R := by ring

/-! ### Continuous trade-off inequality (analogue of NRTV Lemma 28.4) and Theorem 28.3 -/

private noncomputable def msvvDualBeta {ι : Type*} (budget : ι → ℝ) (spent : ι → ℝ) (j : ι) : ℝ :=
  (Real.exp (spent j / budget j) - 1) / (Real.exp 1 - 1)

private noncomputable def msvvDualAlpha {T : ℕ} {ι : Type*} [DecidableEq ι]
    (rule : AllocationRule ι) (b : Fin T → ι → ℝ) (budget : ι → ℝ) (t : Fin T) : ℝ :=
  match choiceAt rule b t with
  | none => 0
  | some j =>
      b t j * (msvvWeight (spentAt rule b t.castSucc j / budget j) / (1 - Real.exp (-1)))

private theorem one_sub_msvvDualBeta {ι : Type*} (budget spent : ι → ℝ) (j : ι) :
    1 - msvvDualBeta budget spent j =
      msvvWeight (spent j / budget j) / (1 - Real.exp (-1)) := by
  have hden_pos : 0 < Real.exp 1 - 1 := exp_one_sub_one_pos
  rw [msvvWeight_eq_dual_factor]
  simp only [msvvDualBeta]
  field_simp [hden_pos.ne']
  ring

private theorem msvvDualAlpha_nonneg {T : ℕ} {ι : Type*} [DecidableEq ι]
    {rule : AllocationRule ι} {b : Fin T → ι → ℝ} {budget : ι → ℝ}
    (hB : ∀ j, 0 < budget j) (hb0 : ∀ t j, 0 ≤ b t j)
    (hinv : ∀ t j, spentAt rule b t j ≤ budget j) (t : Fin T) :
    0 ≤ msvvDualAlpha rule b budget t := by
  simp only [msvvDualAlpha]
  cases hch : choiceAt rule b t with
  | none => exact le_rfl
  | some j =>
      exact mul_nonneg (hb0 t j)
        (div_nonneg (msvvWeight_nonneg ((div_le_one (hB j)).mpr (hinv t.castSucc j)))
          one_sub_exp_neg_one_pos.le)

private theorem msvvDualBeta_nonneg {ι : Type*} {budget spent : ι → ℝ}
    (hB : ∀ j, 0 < budget j) (hs : ∀ j, 0 ≤ spent j) (j : ι) :
    0 ≤ msvvDualBeta budget spent j :=
  div_nonneg (sub_nonneg.mpr (Real.one_le_exp (div_nonneg (hs j) (hB j).le)))
    exp_one_sub_one_pos.le

private theorem msvv_dual_sum_le {T : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {rule : AllocationRule ι} {b : Fin T → ι → ℝ} {budget : ι → ℝ} {R : ℝ}
    (hB : ∀ j, 0 < budget j) (hb0 : ∀ t j, 0 ≤ b t j)
    (hbR : ∀ t j, b t j ≤ R * budget j)
    (hinv : ∀ t j, spentAt rule b t j ≤ budget j)
    (hnone : ∀ t, choiceAt rule b t = none → paymentAt rule b t = 0)
    (hsome : ∀ t j, choiceAt rule b t = some j →
      paymentAt rule b t = min (b t j) (budget j - spentAt rule b t.castSucc j)) :
    ∑ j, budget j * msvvDualBeta budget (finalSpent rule b) j +
        ∑ t : Fin T, msvvDualAlpha rule b budget t ≤
      revenue rule b * (Real.exp 1 / (Real.exp 1 - 1)) * Real.exp R := by
  have hden_pos : 0 < Real.exp 1 - 1 := exp_one_sub_one_pos
  let dualPot : ι → ℝ → ℝ := fun j s =>
    budget j * ((Real.exp (s / budget j) - 1) / (Real.exp 1 - 1))
  have htele := spentAt_telescope rule b dualPot
  have hzero : ∑ j, dualPot j 0 = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [dualPot, zero_div, Real.exp_zero, sub_self, zero_div, mul_zero]
  rw [hzero, sub_zero] at htele
  have hrev_eq : revenue rule b = ∑ t : Fin T, paymentAt rule b t :=
    revenue_eq_sum_paymentAt hnone
  have hsum_b : ∑ j, budget j * msvvDualBeta budget (finalSpent rule b) j =
      ∑ j, dualPot j (finalSpent rule b j) := rfl
  rw [hsum_b, htele, add_comm, ← Finset.sum_add_distrib, hrev_eq,
    Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun t _ => ?_
  cases hch : choiceAt rule b t with
  | none =>
      have hp0 := hnone t hch
      simp only [msvvDualAlpha, hch, add_zero, hp0, zero_mul, le_refl]
  | some j =>
      have hpay_eq := hsome t j hch
      have hsucc_eq : spentAt rule b t.succ j =
          spentAt rule b t.castSucc j + paymentAt rule b t := by
        have : (rule (spentAt rule b t.castSucc) (b t)).choice = some j := hch
        simp only [spentAt_succ, applyStep, this, Function.update_self, paymentAt]
      have hnum := msvv_step_numerator_le (hB j) (hinv t.castSucc j) (hb0 t j) (hbR t j)
      have hαeq : msvvDualAlpha rule b budget t = b t j * (Real.exp 1 -
          Real.exp (spentAt rule b t.castSucc j / budget j)) / (Real.exp 1 - 1) := by
        simp only [msvvDualAlpha, hch, msvvWeight_eq_dual_factor, mul_div_assoc]
      have hpot_eq :
          dualPot j (spentAt rule b t.succ j) - dualPot j (spentAt rule b t.castSucc j) =
            budget j * (Real.exp ((spentAt rule b t.castSucc j +
              min (b t j) (budget j - spentAt rule b t.castSucc j)) / budget j) -
              Real.exp (spentAt rule b t.castSucc j / budget j)) / (Real.exp 1 - 1) := by
        simp only [dualPot, hsucc_eq, hpay_eq]
        ring
      dsimp only
      rw [hαeq, hpot_eq, ← add_div, hpay_eq]
      rw [show min (b t j) (budget j - spentAt rule b t.castSucc j) *
            (Real.exp 1 / (Real.exp 1 - 1)) * Real.exp R =
          (min (b t j) (budget j - spentAt rule b t.castSucc j) * Real.exp 1 * Real.exp R) /
            (Real.exp 1 - 1) by ring]
      exact div_le_div_of_nonneg_right hnum hden_pos.le

private theorem msvvTrunc_pointwise_le {T : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Fin T → ι → ℝ} {budget : ι → ℝ}
    (hB : ∀ j, 0 < budget j) (hb0 : ∀ t j, 0 ≤ b t j) (t : Fin T) (j : ι) :
    msvvWeight (finalSpent (msvvTruncRule budget) b j / budget j) * b t j ≤
      match choiceAt (msvvTruncRule budget) b t with
      | none => 0
      | some k =>
          msvvWeight (spentAt (msvvTruncRule budget) b t.castSucc k / budget k) * b t k := by
  classical
  set rule := msvvTruncRule budget
  have hinv := msvvTrunc_spent_mem (fun k => (hB k).le) hb0
  have hpay_nonneg : ∀ t' : Fin T, 0 ≤ paymentAt rule b t' :=
    paymentAt_nonneg_of_step hinv hb0 (fun _ _ hs hq =>
      truncRule_bounds (budget := budget)
        (fun s q k => q k * msvvWeight (s k / budget k)) hs hq)
  have hmono : spentAt rule b t.castSucc j ≤ finalSpent rule b j :=
    spentAt_mono hpay_nonneg (Fin.le_last t.castSucc) j
  rcases lt_or_ge (spentAt rule b t.castSucc j) (budget j) with hlt | hge
  · have hmem : j ∈ univ.filter (fun k => spentAt rule b t.castSucc k < budget k) :=
      mem_filter.mpr ⟨mem_univ j, hlt⟩
    obtain ⟨jstar, hjstar, hmax⟩ := exists_argmaxOver_of_mem hmem
      (score := fun k => b t k * msvvWeight (spentAt rule b t.castSucc k / budget k))
    have hch : choiceAt rule b t = some jstar := by
      change (msvvTruncRule budget (spentAt rule b t.castSucc) (b t)).choice = _
      simp only [msvvTruncRule, hjstar]
    rw [hch]
    have hanti : msvvWeight (finalSpent rule b j / budget j) ≤
        msvvWeight (spentAt rule b t.castSucc j / budget j) :=
      msvvWeight_antitone (div_le_div_of_nonneg_right hmono (hB j).le)
    have h1 := mul_le_mul_of_nonneg_right hanti (hb0 t j)
    linarith [h1, hmax]
  · have hfinal_eq : finalSpent rule b j = budget j :=
      le_antisymm (hinv (Fin.last T) j).2 (hge.trans hmono)
    rw [hfinal_eq, div_self (hB j).ne', msvvWeight, sub_self, Real.exp_zero, sub_self, zero_mul]
    cases hch : choiceAt rule b t with
    | none => exact le_rfl
    | some k =>
        exact mul_nonneg
          (msvvWeight_nonneg ((div_le_one (hB k)).mpr (hinv t.castSucc k).2)) (hb0 t k)

/-- **Continuous trade-off inequality** for **MSVV Algorithm 1** (truncated spend), the continuous
analogue of [LahaiePennockSaberiVohra2007], Lemma 28.4, Eq. (28.13), p. 710. Holds against every
LP-feasible fractional solution `x` without assuming that `OPT` exhausts every budget. -/
theorem msvvTrunc_tradeoff {T : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Fin T → ι → ℝ} {budget : ι → ℝ} {x : Fin T → ι → ℝ}
    (hB : ∀ j, 0 < budget j) (hb0 : ∀ t j, 0 ≤ b t j)
    (hx : (LP.unit b budget).IsPrimalFeasible x) :
    ∑ j, msvvWeight (finalSpent (msvvTruncRule budget) b j / budget j) *
        (∑ t : Fin T, b t j * x t j) ≤
      ∑ t : Fin T,
        match choiceAt (msvvTruncRule budget) b t with
        | none => 0
        | some j =>
            msvvWeight (spentAt (msvvTruncRule budget) b t.castSucc j / budget j) * b t j := by
  let score : Fin T → ℝ := fun t =>
    match choiceAt (msvvTruncRule budget) b t with
    | none => 0
    | some j => msvvWeight (spentAt (msvvTruncRule budget) b t.castSucc j / budget j) * b t j
  have hinv := msvvTrunc_spent_mem (b := b) (fun k => (hB k).le) hb0
  have hscore_nn : ∀ t, 0 ≤ score t := fun t => by
    dsimp only [score]
    cases hch : choiceAt (msvvTruncRule budget) b t with
    | none => exact le_rfl
    | some k =>
        exact mul_nonneg
          (msvvWeight_nonneg ((div_le_one (hB k)).mpr (hinv t.castSucc k).2)) (hb0 t k)
  calc
    ∑ j, msvvWeight (finalSpent (msvvTruncRule budget) b j / budget j) *
          (∑ t : Fin T, b t j * x t j)
        = ∑ t : Fin T, ∑ j,
            (msvvWeight (finalSpent (msvvTruncRule budget) b j / budget j) * b t j) * x t j := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ t : Fin T, ∑ j, score t * x t j :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (msvvTrunc_pointwise_le hB hb0 t j) (hx.nonneg t j)
    _ = ∑ t : Fin T, score t * ∑ j, x t j := by
        refine Finset.sum_congr rfl fun t _ => (Finset.mul_sum ..).symm
    _ ≤ ∑ t : Fin T, score t * 1 :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hx.demand_le t) (hscore_nn t)
    _ = ∑ t : Fin T, score t := by simp only [mul_one]

/-- **MSVV Algorithm 1 competitive-ratio upper bound (truncated spend)** — the revenue lower bound
half of [LahaiePennockSaberiVohra2007], Theorem 28.3 (pp. 709–711) and Exercise 28.6 (p. 716).

For every finite bid ratio `R ≥ 0` with `b t j ≤ R * budget j`, every positive budget profile
`budget`, and **every** feasible fractional LP solution `x` to Eq. (28.11) (**without** assuming
`OPT` exhausts budgets):
`(1 - exp (-1)) * exp (-R) * primalObj x ≤ revenue (msvvTruncRule budget) b`.

The companion optimality lower bound ("no deterministic or randomized online algorithm beats
`1 - 1/e`") is **not** proved here and stays open under issue `#7789`. No running-time claim is
made. -/
theorem msvvTrunc_competitive {T : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Fin T → ι → ℝ} {budget : ι → ℝ} {x : Fin T → ι → ℝ} {R : ℝ}
    (hB : ∀ j, 0 < budget j) (hb0 : ∀ t j, 0 ≤ b t j)
    (hbR : ∀ t j, b t j ≤ R * budget j)
    (hx : (LP.unit b budget).IsPrimalFeasible x) :
    (1 - Real.exp (-1)) * Real.exp (-R) * (LP.unit b budget).primalObj x ≤
      revenue (msvvTruncRule budget) b := by
  classical
  set rule := msvvTruncRule budget
  have hinv := msvvTrunc_spent_mem (b := b) (fun j => (hB j).le) hb0
  let α : Fin T → ℝ := msvvDualAlpha rule b budget
  let β : ι → ℝ := msvvDualBeta budget (finalSpent rule b)
  have hdual : (LP.unit b budget).IsDualFeasible α β := by
    refine ⟨msvvDualAlpha_nonneg hB hb0 fun t j => (hinv t j).2,
      msvvDualBeta_nonneg hB fun j => (hinv (Fin.last T) j).1, fun t j => ?_⟩
    have hpt := msvvTrunc_pointwise_le hB hb0 t j
    have hwant : b t j * (1 - β j) ≤ α t := by
      rw [one_sub_msvvDualBeta]
      have hα_eq : α t = (match choiceAt rule b t with
          | none => 0
          | some k => msvvWeight (spentAt rule b t.castSucc k / budget k) * b t k) /
            (1 - Real.exp (-1)) := by
        simp only [α, msvvDualAlpha]
        cases choiceAt rule b t with
        | none => simp only [zero_div]
        | some k => ring
      rw [hα_eq, ← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ one_sub_exp_neg_one_pos.le
      linarith [hpt]
    change b t j ≤ α t + b t j * β j
    linarith
  have hdual_le : (LP.unit b budget).dualObj α β ≤
      revenue rule b * (Real.exp 1 / (Real.exp 1 - 1)) * Real.exp R := by
    change ∑ j, budget j * β j + ∑ t : Fin T, 1 * α t ≤ _
    simp_rw [one_mul]
    refine msvv_dual_sum_le hB hb0 hbR (fun t j => (hinv t j).2)
      (fun t ht => trunc_payment_eq_zero_of_none (budget := budget)
        (fun s q k => q k * msvvWeight (s k / budget k))
        (by simpa [rule, choiceAt, msvvTruncRule] using ht))
      (fun t j hch => ?_)
    change (msvvTruncRule budget (spentAt rule b t.castSucc) (b t)).payment = _
    have hch' : (msvvTruncRule budget (spentAt rule b t.castSucc) (b t)).choice = some j := hch
    simp only [msvvTruncRule] at hch' ⊢
    cases harg : argmaxOver (univ.filter fun k => spentAt rule b t.castSucc k < budget k)
        (fun k => b t k * msvvWeight (spentAt rule b t.castSucc k / budget k)) with
    | none => simp only [harg] at hch'; cases hch'
    | some j₀ => simp only [harg] at hch' ⊢; cases hch'; rfl
  exact msvv_rescale_le ((LP.primalObj_le_dualObj hx hdual).trans hdual_le)

/-- **MSVV Algorithm 1 competitive-ratio upper bound (truncated spend)** lifted directly to the
keyword-frequency LP relaxation (28.11) `countLP` (`demand i = #{t | queries t = i}`). -/
theorem msvvTrunc_competitive_countLP {T : ℕ} {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [LinearOrder ι] {bid : κ → ι → ℝ} {budget : ι → ℝ}
    (queries : Fin T → κ) {x : κ → ι → ℝ} {R : ℝ}
    (hB : ∀ j, 0 < budget j) (hb0 : ∀ i j, 0 ≤ bid i j)
    (hbR : ∀ i j, bid i j ≤ R * budget j)
    (hx : (LP.countLP bid budget queries).IsPrimalFeasible x) :
    (1 - Real.exp (-1)) * Real.exp (-R) *
        (LP.countLP bid budget queries).primalObj x ≤
      revenue (msvvTruncRule budget) (fun t j => bid (queries t) j) := by
  obtain ⟨y, hy, hobj⟩ := LP.exists_unitPrimal_of_countLP queries hx
  rw [← hobj]
  exact msvvTrunc_competitive hB (fun t j => hb0 (queries t) j) (fun t j => hbR (queries t) j) hy

/-- **MSVV Algorithm 1 competitive-ratio upper bound (all-or-nothing spend)** — the revenue lower
bound half of [LahaiePennockSaberiVohra2007], Theorem 28.3 (pp. 709–711) and Exercise 28.6
(p. 716), when a query is assigned to `j` only if `s j + b t j ≤ budget j`.

For every `0 ≤ R ≤ 1` with `b t j ≤ R * budget j` and **every** feasible fractional LP solution `x`
to Eq. (28.11) (**without** assuming `OPT` exhausts budgets):
`(1 - exp (-1)) * (1 - R) * exp (-R) * primalObj x ≤ revenue (msvvAllOrNothingRule budget) b`.

The matching optimality lower bound stays open under issue `#7789`. No running-time claim is made.
-/
theorem msvvAllOrNothing_competitive {T : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Fin T → ι → ℝ} {budget : ι → ℝ} {x : Fin T → ι → ℝ} {R : ℝ}
    (hB : ∀ j, 0 < budget j) (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hb0 : ∀ t j, 0 ≤ b t j) (hbR : ∀ t j, b t j ≤ R * budget j)
    (hx : (LP.unit b budget).IsPrimalFeasible x) :
    (1 - Real.exp (-1)) * (1 - R) * Real.exp (-R) * (LP.unit b budget).primalObj x ≤
      revenue (msvvAllOrNothingRule budget) b := by
  classical
  set rule := msvvAllOrNothingRule budget
  have hinv := msvvAllOrNothing_spent_mem (b := b) (fun j => (hB j).le) hb0
  have hpay_nonneg : ∀ t : Fin T, 0 ≤ paymentAt rule b t :=
    paymentAt_nonneg_of_step hinv hb0 (fun _ _ _ hq =>
      aonRule_bounds (budget := budget)
        (fun s q j => q j * msvvWeight (s j / budget j)) hq)
  have hmono : ∀ (t : Fin T) (j : ι), spentAt rule b t.castSucc j ≤ finalSpent rule b j :=
    fun t j => spentAt_mono hpay_nonneg (Fin.le_last t.castSucc) j
  have hden_pos : 0 < Real.exp 1 - 1 := exp_one_sub_one_pos
  have hc_pos : 0 < 1 - Real.exp (-1) := one_sub_exp_neg_one_pos
  let α : Fin T → ℝ := msvvDualAlpha rule b budget
  let βT : ι → ℝ := msvvDualBeta budget (finalSpent rule b)
  let β : ι → ℝ := fun j =>
    if (1 - R) * budget j < finalSpent rule b j then 1 else βT j
  have hα_nn : ∀ t, 0 ≤ α t := msvvDualAlpha_nonneg hB hb0 fun t j => (hinv t j).2
  have hβT_nn : ∀ j, 0 ≤ βT j := msvvDualBeta_nonneg hB fun j => (hinv (Fin.last T) j).1
  have hdual : (LP.unit b budget).IsDualFeasible α β := by
    refine ⟨hα_nn, fun j => ?_, fun t j => ?_⟩
    · dsimp only [β]
      split_ifs
      · exact zero_le_one
      · exact hβT_nn j
    · by_cases hhigh : (1 - R) * budget j < finalSpent rule b j
      · have hβ : β j = 1 := ite_eq_left_iff.mpr fun h => absurd hhigh h
        change b t j ≤ α t + b t j * β j
        rw [hβ, mul_one]
        linarith [hα_nn t]
      · have hlow : finalSpent rule b j ≤ (1 - R) * budget j := le_of_not_gt hhigh
        have hfit : spentAt rule b t.castSucc j + b t j ≤ budget j := by
          linarith [hmono t j, hbR t j]
        have hmem : j ∈ univ.filter (fun k => spentAt rule b t.castSucc k + b t k ≤ budget k) :=
          mem_filter.mpr ⟨mem_univ j, hfit⟩
        obtain ⟨jstar, hjstar, hmax⟩ := exists_argmaxOver_of_mem hmem
          (score := fun k => b t k * msvvWeight (spentAt rule b t.castSucc k / budget k))
        have hch : choiceAt rule b t = some jstar := by
          change (msvvAllOrNothingRule budget (spentAt rule b t.castSucc) (b t)).choice = _
          simp only [msvvAllOrNothingRule, hjstar]
        have hβ : β j = βT j := ite_eq_right_iff.mpr fun h => absurd h hhigh
        have hanti : msvvWeight (finalSpent rule b j / budget j) ≤
            msvvWeight (spentAt rule b t.castSucc j / budget j) :=
          msvvWeight_antitone (div_le_div_of_nonneg_right (hmono t j) (hB j).le)
        have hαeq : α t = b t jstar *
            msvvWeight (spentAt rule b t.castSucc jstar / budget jstar) / (1 - Real.exp (-1)) := by
          simp only [α, msvvDualAlpha, hch, mul_div_assoc]
        have hle : b t j * (1 - βT j) ≤ α t := by
          rw [show βT j = msvvDualBeta budget (finalSpent rule b) j from rfl,
            one_sub_msvvDualBeta, ← mul_div_assoc, hαeq]
          exact div_le_div_of_nonneg_right
            ((mul_le_mul_of_nonneg_left hanti (hb0 t j)).trans hmax) hc_pos.le
        change b t j ≤ α t + b t j * β j
        rw [hβ]
        linarith
  have hbase : ∑ j, budget j * βT j + ∑ t : Fin T, α t ≤
      revenue rule b * (Real.exp 1 / (Real.exp 1 - 1)) * Real.exp R := by
    refine msvv_dual_sum_le hB hb0 hbR (fun t j => (hinv t j).2)
      (fun t ht => aon_payment_eq_zero_of_none (budget := budget)
        (fun s q k => q k * msvvWeight (s k / budget k))
        (by simpa [rule, choiceAt, msvvAllOrNothingRule] using ht))
      (fun t j hch => ?_)
    have hch' : (msvvAllOrNothingRule budget (spentAt rule b t.castSucc) (b t)).choice =
        some j := hch
    have harg_eq : argmaxOver
        (univ.filter fun k => spentAt rule b t.castSucc k + b t k ≤ budget k)
        (fun k => b t k * msvvWeight (spentAt rule b t.castSucc k / budget k)) = some j := by
      simp only [msvvAllOrNothingRule] at hch'
      cases harg : argmaxOver
          (univ.filter fun k => spentAt rule b t.castSucc k + b t k ≤ budget k)
          (fun k => b t k * msvvWeight (spentAt rule b t.castSucc k / budget k)) with
      | none => simp only [harg] at hch'; cases hch'
      | some j₀ => simp only [harg] at hch'; cases hch'; rfl
    have hfit : spentAt rule b t.castSucc j + b t j ≤ budget j :=
      (mem_filter.mp (argmaxOver_mem harg_eq)).2
    have hpay : paymentAt rule b t = b t j := by
      change (msvvAllOrNothingRule budget (spentAt rule b t.castSucc) (b t)).payment = _
      simp only [msvvAllOrNothingRule, harg_eq]
    rw [hpay, min_eq_left (by linarith)]
  have hboost : (1 - R) * ∑ j, budget j * (β j - βT j) ≤
      R * (Real.exp 1 / (Real.exp 1 - 1)) * revenue rule b := by
    rw [Finset.mul_sum]
    calc
      ∑ j, (1 - R) * (budget j * (β j - βT j))
          ≤ ∑ j, R * (Real.exp 1 / (Real.exp 1 - 1)) * finalSpent rule b j := by
            refine Finset.sum_le_sum fun j _ => ?_
            by_cases hhigh : (1 - R) * budget j < finalSpent rule b j
            · have hβ : β j = 1 := ite_eq_left_iff.mpr fun h => absurd hhigh h
              rw [hβ]
              have hf : 1 - R ≤ finalSpent rule b j / budget j :=
                (le_div_iff₀ (hB j)).mpr hhigh.le
              have hex_le : Real.exp (1 - R) ≤ Real.exp (finalSpent rule b j / budget j) :=
                Real.exp_le_exp.mpr hf
              have hgap : Real.exp 1 - Real.exp (finalSpent rule b j / budget j) ≤
                  Real.exp 1 * R := by
                have hex : Real.exp (1 - R) = Real.exp 1 * Real.exp (-R) := by
                  rw [← Real.exp_add, sub_eq_add_neg]
                have h1 := one_sub_exp_neg_le R
                have hepos : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
                nlinarith
              have h1sub : 1 - βT j ≤ R * (Real.exp 1 / (Real.exp 1 - 1)) := by
                have heq : 1 - βT j = (Real.exp 1 -
                    Real.exp (finalSpent rule b j / budget j)) / (Real.exp 1 - 1) := by
                  simp only [βT, msvvDualBeta]
                  field_simp [hden_pos.ne']
                  ring
                rw [heq, show R * (Real.exp 1 / (Real.exp 1 - 1)) =
                    (Real.exp 1 * R) / (Real.exp 1 - 1) by ring]
                exact div_le_div_of_nonneg_right hgap hden_pos.le
              have h1sub_nn : 0 ≤ 1 - βT j := by
                have : Real.exp (finalSpent rule b j / budget j) ≤ Real.exp 1 :=
                  Real.exp_le_exp.mpr ((div_le_one (hB j)).mpr (hinv (Fin.last T) j).2)
                simp only [βT, msvvDualBeta, sub_nonneg, div_le_one hden_pos]
                linarith
              have hfac_nn : 0 ≤ (1 - R) * budget j := mul_nonneg (by linarith) (hB j).le
              calc
                (1 - R) * (budget j * (1 - βT j))
                    = ((1 - R) * budget j) * (1 - βT j) := by ring
                _ ≤ finalSpent rule b j * (1 - βT j) :=
                    mul_le_mul_of_nonneg_right hhigh.le h1sub_nn
                _ ≤ finalSpent rule b j * (R * (Real.exp 1 / (Real.exp 1 - 1))) :=
                    mul_le_mul_of_nonneg_left h1sub (hinv (Fin.last T) j).1
                _ = R * (Real.exp 1 / (Real.exp 1 - 1)) * finalSpent rule b j := by ring
            · have hβ : β j = βT j := ite_eq_right_iff.mpr fun h => absurd h hhigh
              rw [hβ, sub_self, mul_zero, mul_zero]
              exact mul_nonneg
                (mul_nonneg hR0 (div_nonneg (Real.exp_pos 1).le hden_pos.le))
                (hinv (Fin.last T) j).1
      _ = R * (Real.exp 1 / (Real.exp 1 - 1)) * revenue rule b :=
          (Finset.mul_sum ..).symm
  have hdual_split : (LP.unit b budget).dualObj α β =
      (∑ j, budget j * βT j + ∑ t : Fin T, α t) + ∑ j, budget j * (β j - βT j) := by
    change ∑ j, budget j * β j + ∑ t : Fin T, 1 * α t = _
    simp_rw [one_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have h1R : 0 ≤ 1 - R := sub_nonneg.mpr hR1
  have hrev_nn : 0 ≤ revenue rule b :=
    Finset.sum_nonneg fun j _ => (hinv (Fin.last T) j).1
  have hcoef : (1 - R) * Real.exp R + R ≤ Real.exp R := by
    have heR : 1 ≤ Real.exp R := Real.one_le_exp hR0
    nlinarith
  have hweak := LP.primalObj_le_dualObj hx hdual
  have hscaled : (1 - R) * (LP.unit b budget).primalObj x ≤
      revenue rule b * (Real.exp 1 / (Real.exp 1 - 1)) * Real.exp R := by
    calc
      (1 - R) * (LP.unit b budget).primalObj x
          ≤ (1 - R) * (LP.unit b budget).dualObj α β := mul_le_mul_of_nonneg_left hweak h1R
      _ = (1 - R) * (∑ j, budget j * βT j + ∑ t : Fin T, α t) +
            (1 - R) * ∑ j, budget j * (β j - βT j) := by rw [hdual_split, mul_add]
      _ ≤ (1 - R) * (revenue rule b * (Real.exp 1 / (Real.exp 1 - 1)) * Real.exp R) +
            R * (Real.exp 1 / (Real.exp 1 - 1)) * revenue rule b :=
          add_le_add (mul_le_mul_of_nonneg_left hbase h1R) hboost
      _ = revenue rule b * (Real.exp 1 / (Real.exp 1 - 1)) * ((1 - R) * Real.exp R + R) := by
          ring
      _ ≤ revenue rule b * (Real.exp 1 / (Real.exp 1 - 1)) * Real.exp R :=
          mul_le_mul_of_nonneg_left hcoef
            (mul_nonneg hrev_nn (div_nonneg (Real.exp_pos 1).le hden_pos.le))
  have hres := msvv_rescale_le hscaled
  linarith [show (1 - Real.exp (-1)) * Real.exp (-R) * ((1 - R) * (LP.unit b budget).primalObj x) =
    (1 - Real.exp (-1)) * (1 - R) * Real.exp (-R) * (LP.unit b budget).primalObj x by ring]

/-- **MSVV Algorithm 1 competitive-ratio upper bound (all-or-nothing spend)** lifted directly to the
keyword-frequency LP relaxation (28.11) `countLP` (`demand i = #{t | queries t = i}`). -/
theorem msvvAllOrNothing_competitive_countLP {T : ℕ} {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [LinearOrder ι] {bid : κ → ι → ℝ} {budget : ι → ℝ}
    (queries : Fin T → κ) {x : κ → ι → ℝ} {R : ℝ}
    (hB : ∀ j, 0 < budget j) (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hb0 : ∀ i j, 0 ≤ bid i j) (hbR : ∀ i j, bid i j ≤ R * budget j)
    (hx : (LP.countLP bid budget queries).IsPrimalFeasible x) :
    (1 - Real.exp (-1)) * (1 - R) * Real.exp (-R) *
        (LP.countLP bid budget queries).primalObj x ≤
      revenue (msvvAllOrNothingRule budget) (fun t j => bid (queries t) j) := by
  obtain ⟨y, hy, hobj⟩ := LP.exists_unitPrimal_of_countLP queries hx
  rw [← hobj]
  exact msvvAllOrNothing_competitive hB hR0 hR1
    (fun t j => hb0 (queries t) j) (fun t j => hbR (queries t) j) hy

/-- As the bid-to-budget ratio `R → 0`, the truncated-spend MSVV competitive factor converges to
`1 - exp (-1)` (`1 - 1 / e`). -/
theorem tendsto_msvvTrunc_factor :
    Filter.Tendsto (fun R : ℝ => (1 - Real.exp (-1)) * Real.exp (-R))
      (nhds 0) (nhds (1 - Real.exp (-1))) := by
  have h : Filter.Tendsto (fun R : ℝ => Real.exp (-R)) (nhds 0) (nhds (Real.exp (-0))) :=
    (Real.continuous_exp.comp continuous_neg).tendsto 0
  simpa using (tendsto_const_nhds (x := 1 - Real.exp (-1))).mul h

/-- As the bid-to-budget ratio `R → 0`, the all-or-nothing MSVV competitive factor converges to
`1 - exp (-1)` (`1 - 1 / e`). -/
theorem tendsto_msvvAllOrNothing_factor :
    Filter.Tendsto (fun R : ℝ => (1 - Real.exp (-1)) * (1 - R) * Real.exp (-R))
      (nhds 0) (nhds (1 - Real.exp (-1))) := by
  have h1 : Filter.Tendsto (fun R : ℝ => 1 - R) (nhds 0) (nhds (1 - 0)) :=
    tendsto_const_nhds.sub Filter.tendsto_id
  have h2 : Filter.Tendsto (fun R : ℝ => Real.exp (-R)) (nhds 0) (nhds (Real.exp (-0))) :=
    (Real.continuous_exp.comp continuous_neg).tendsto 0
  simpa using ((tendsto_const_nhds (x := 1 - Real.exp (-1))).mul h1).mul h2

/-! ### Discrete `k`-bucket geometric series (NRTV displays 28.12–28.13, pp. 710–711) -/

/-- Discrete trade-off function `Φ(s) = 1 - (1 - 1 / k) ^ (k - s)`
([LahaiePennockSaberiVohra2007], §28.4.1, display (28.12), p. 710). -/
@[expose] noncomputable def discretePhi (k s : ℕ) : ℝ :=
  1 - (1 - 1 / (k : ℝ)) ^ (k - s)

private theorem discretePhi_nonneg {k : ℕ} (hk : 0 < k) (s : ℕ) : 0 ≤ discretePhi k s := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [discretePhi, sub_nonneg]
  exact pow_le_one₀ (sub_nonneg.mpr ((div_le_one hkpos).mpr (by exact_mod_cast hk)))
    (sub_le_self _ (by positivity))

private theorem sum_discretePhi_eq (k : ℕ) (hk : 0 < k) (j : ℕ) (hj : j ≤ k) :
    (1 / (k : ℝ)) * ∑ i ∈ Finset.range (j + 1), discretePhi k i =
      (j : ℝ) / k + discretePhi k j - discretePhi k 0 + discretePhi k 0 / k := by
  have hkne : (k : ℝ) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
  induction j with
  | zero =>
      simp only [Nat.cast_zero, zero_div, zero_add, Finset.range_one, Finset.sum_singleton,
        sub_self]
      ring
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih (Nat.le_of_succ_le hj)]
      have hpow : (1 - 1 / (k : ℝ)) ^ (k - m) =
          (1 - 1 / (k : ℝ)) * (1 - 1 / (k : ℝ)) ^ (k - (m + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      simp only [discretePhi, Nat.cast_add, Nat.cast_one, hpow]
      field_simp [hkne]
      ring

private theorem sum_discretePhi_Icc_eq (k : ℕ) (hk : 0 < k) (j : ℕ) (hj : j ≤ k) :
    (1 / (k : ℝ)) * ∑ i ∈ Finset.Icc 1 j, discretePhi k i =
      (j : ℝ) / k + discretePhi k j - discretePhi k 0 := by
  have hsum := sum_discretePhi_eq k hk j hj
  have hunion : Finset.range (j + 1) = insert 0 (Finset.Icc 1 j) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hunion, Finset.sum_insert (by simp), mul_add] at hsum
  linarith [show (1 / (k : ℝ)) * discretePhi k 0 = discretePhi k 0 / k by ring]

/-- The exact discrete geometric-series step proving NRTV p. 710–711 from display (28.13)
(correcting the printed inner index typo `∑_{j=0}^i Φ(i)` → `∑_{j=0}^i Φ(j)` on p. 710).
Given `∑ i, Φ(i) s_i ≤ ∑ i, Φ(i) w_i` and `w_i ≤ (∑_{j ≥ i} s_j) / k`, yields
`(1 - 1 / k) * Φ(0) * ∑ s_i ≤ ∑ (i / k) * s_i`. -/
theorem discretePhi_tradeoff {k : ℕ} (hk : 0 < k) {s w : Fin (k + 1) → ℝ}
    (htrade : ∑ i, discretePhi k i.val * s i ≤ ∑ i, discretePhi k i.val * w i)
    (hw : ∀ i : Fin (k + 1), w i ≤ (∑ j : Fin (k + 1) with i ≤ j, s j) / k) :
    (1 - 1 / (k : ℝ)) * discretePhi k 0 * (∑ i, s i) ≤
      ∑ i, (i.val : ℝ) / k * s i := by
  have h1 : ∑ i : Fin (k + 1), discretePhi k i.val * w i ≤
      (1 / (k : ℝ)) * ∑ i : Fin (k + 1),
        discretePhi k i.val * ∑ j : Fin (k + 1) with i ≤ j, s j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (hw i) (discretePhi_nonneg hk i.val)
    have hmul : discretePhi k i.val * ((∑ j with i ≤ j, s j) / k) =
        1 / (k : ℝ) * (discretePhi k i.val * ∑ j with i ≤ j, s j) := by ring
    linarith
  have hswap : ∑ i : Fin (k + 1), discretePhi k i.val * ∑ j : Fin (k + 1) with i ≤ j, s j =
      ∑ j : Fin (k + 1), (∑ i ∈ Finset.range (j.val + 1), discretePhi k i) * s j := by
    rw [Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum, Finset.sum_filter],
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    congr 1
    rw [Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, Finset.sum_map,
      ← Finset.filter_ge_eq_Iic]
    rfl
  have hcalc : (1 / (k : ℝ)) * ∑ j : Fin (k + 1),
        (∑ i ∈ Finset.range (j.val + 1), discretePhi k i) * s j =
      ∑ j : Fin (k + 1), ((j.val : ℝ) / k + discretePhi k j.val -
        (1 - 1 / (k : ℝ)) * discretePhi k 0) * s j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := sum_discretePhi_eq k hk j.val (Nat.le_of_lt_succ j.isLt)
    have hmul : 1 / (k : ℝ) * ((∑ i ∈ Finset.range (j.val + 1), discretePhi k i) * s j) =
        (1 / (k : ℝ) * ∑ i ∈ Finset.range (j.val + 1), discretePhi k i) * s j := by ring
    rw [hmul, hj]
    ring
  have hle : ∑ i, discretePhi k i.val * s i ≤
      ∑ j : Fin (k + 1), ((j.val : ℝ) / k + discretePhi k j.val -
        (1 - 1 / (k : ℝ)) * discretePhi k 0) * s j := by
    calc
      ∑ i, discretePhi k i.val * s i ≤ ∑ i, discretePhi k i.val * w i := htrade
      _ ≤ (1 / (k : ℝ)) * ∑ i, discretePhi k i.val * ∑ j with i ≤ j, s j := h1
      _ = _ := by rw [hswap, hcalc]
  have hre : ∑ j : Fin (k + 1), ((j.val : ℝ) / k + discretePhi k j.val -
        (1 - 1 / (k : ℝ)) * discretePhi k 0) * s j =
      (∑ j, (j.val : ℝ) / k * s j) + (∑ j, discretePhi k j.val * s j) -
        (1 - 1 / (k : ℝ)) * discretePhi k 0 * (∑ j, s j) := by
    simp_rw [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [hle, hre]

/-- Exact error-free version of `discretePhi_tradeoff` when no budget is spent inside the empty
zero-interval `(-1/k, 0]` (`w 0 = 0`): `Φ(0) * ∑ s_i ≤ ∑ (i / k) * s_i`. -/
theorem discretePhi_tradeoff_zero {k : ℕ} (hk : 0 < k) {s w : Fin (k + 1) → ℝ}
    (htrade : ∑ i, discretePhi k i.val * s i ≤ ∑ i, discretePhi k i.val * w i)
    (hw0 : w 0 = 0)
    (hw : ∀ i : Fin (k + 1), 0 < i.val → w i ≤ (∑ j : Fin (k + 1) with i ≤ j, s j) / k) :
    discretePhi k 0 * (∑ i, s i) ≤ ∑ i, (i.val : ℝ) / k * s i := by
  have h1 : ∑ i : Fin (k + 1), discretePhi k i.val * w i ≤
      (1 / (k : ℝ)) * ∑ i : Fin (k + 1) with 0 < i.val,
        discretePhi k i.val * ∑ j : Fin (k + 1) with i ≤ j, s j := by
    rw [Finset.mul_sum]
    have huniv : (univ : Finset (Fin (k + 1))) =
        insert 0 (univ.filter fun i : Fin (k + 1) => 0 < i.val) := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, true_iff,
        Fin.ext_iff, Fin.val_zero]
      omega
    conv_lhs => rw [huniv]
    rw [Finset.sum_insert (by simp), Fin.val_zero, hw0, mul_zero, zero_add]
    refine Finset.sum_le_sum fun i hi => ?_
    have := mul_le_mul_of_nonneg_left (hw i (mem_filter.mp hi).2) (discretePhi_nonneg hk i.val)
    have hmul : discretePhi k i.val * ((∑ j with i ≤ j, s j) / k) =
        1 / (k : ℝ) * (discretePhi k i.val * ∑ j with i ≤ j, s j) := by ring
    linarith
  have hswap : ∑ i : Fin (k + 1) with 0 < i.val,
        discretePhi k i.val * ∑ j : Fin (k + 1) with i ≤ j, s j =
      ∑ j : Fin (k + 1), (∑ i ∈ Finset.Icc 1 j.val, discretePhi k i) * s j := by
    rw [Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum, Finset.sum_filter],
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, Finset.filter_filter, ← Finset.sum_mul]
    congr 1
    let one : Fin (k + 1) := ⟨1, by omega⟩
    change _ = ∑ i ∈ Finset.Icc one.val j.val, discretePhi k i
    rw [← Fin.map_valEmbedding_Icc, Finset.sum_map]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc, Fin.le_def, one]
    omega
  have hcalc : (1 / (k : ℝ)) * ∑ j : Fin (k + 1),
        (∑ i ∈ Finset.Icc 1 j.val, discretePhi k i) * s j =
      ∑ j : Fin (k + 1),
        ((j.val : ℝ) / k + discretePhi k j.val - discretePhi k 0) * s j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := sum_discretePhi_Icc_eq k hk j.val (Nat.le_of_lt_succ j.isLt)
    have hmul : 1 / (k : ℝ) * ((∑ i ∈ Finset.Icc 1 j.val, discretePhi k i) * s j) =
        (1 / (k : ℝ) * ∑ i ∈ Finset.Icc 1 j.val, discretePhi k i) * s j := by ring
    rw [hmul, hj]
  have hle : ∑ i, discretePhi k i.val * s i ≤
      ∑ j : Fin (k + 1), ((j.val : ℝ) / k + discretePhi k j.val - discretePhi k 0) * s j := by
    calc
      ∑ i, discretePhi k i.val * s i ≤ ∑ i, discretePhi k i.val * w i := htrade
      _ ≤ (1 / (k : ℝ)) * ∑ i with 0 < i.val,
            discretePhi k i.val * ∑ j with i ≤ j, s j := h1
      _ = _ := by rw [hswap, hcalc]
  have hre : ∑ j : Fin (k + 1),
        ((j.val : ℝ) / k + discretePhi k j.val - discretePhi k 0) * s j =
      (∑ j, (j.val : ℝ) / k * s j) + (∑ j, discretePhi k j.val * s j) -
        discretePhi k 0 * (∑ j, s j) := by
    simp_rw [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [hle, hre]

/-- As the discretization `k → ∞`, `discretePhi k 0 = 1 - (1 - 1 / k) ^ k` converges to
`1 - exp (-1)` ([LahaiePennockSaberiVohra2007], §28.4.1, p. 711). -/
theorem tendsto_discretePhi_zero :
    Filter.Tendsto (fun k : ℕ => discretePhi k 0) Filter.atTop (nhds (1 - Real.exp (-1))) := by
  have hexp : Filter.Tendsto (fun k : ℕ => (1 + (-1 : ℝ) / k) ^ k) Filter.atTop
      (nhds (Real.exp (-1))) :=
    Real.tendsto_one_add_div_pow_exp (-1)
  have hsub : Filter.Tendsto (fun k : ℕ => 1 - (1 + (-1 : ℝ) / k) ^ k) Filter.atTop
      (nhds (1 - Real.exp (-1))) :=
    tendsto_const_nhds.sub hexp
  refine hsub.congr fun k => ?_
  simp only [discretePhi, Nat.sub_zero, sub_eq_add_neg, neg_div]

end Cslib.Algorithms.Lean.OnlineMatching.AdWords
