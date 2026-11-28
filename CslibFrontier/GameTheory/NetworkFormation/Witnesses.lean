/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.NetworkFormation.FairConnection
import CslibFrontier.Foundations.NumberTheory.Harmonic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tightness and separation witnesses for fair connection games

Concrete finite network families accompanying
`CslibFrontier.GameTheory.NetworkFormation.FairConnection`:

1. **Directed single-sink broadcast network (`broadcastNetwork k ε`)** ([AnshelevichDKTWR2008];
   [RoughgardenTardos2007], Example 17.3; [TardosWexler2007], Section 19.3.1): `(k + 2)` vertices
   (`k` sources `source i`, an intermediate meeting vertex `hub`, and a common `sink`), with
   zero-cost feeder arcs `source i → hub`, a shared `trunk` arc `hub → sink` of cost `1 + ε`, and
   direct bypass arcs `source i → sink` of cost `1 / (i + 1)`.
   * Unlike the abstract resource game `CongestionGame.optOut`, this is an explicit graph
     `FairConnectionGame` retaining the zero-cost feeder arcs `source i → hub`, and every simple
     `source i`–`sink` dipath is proved to be either `[direct i]` or `[toHub i, trunk]`.
   * For `ε > 0`, the unique pure Nash equilibrium is the all-direct profile of social cost `H k`,
     whereas the all-shared profile forms a Steiner arborescence of social cost `1 + ε`, showing
     **Anshelevich et al.'s `H_k` price-of-stability bound is tight** even on single-sink directed
     networks (`exists_forall_isPureNash_broadcastNetwork_mul_lt`).
   * At `ε = 0`, both the all-shared profile (optimal cost `1`) and the all-direct profile (cost
     `H k`) are pure Nash equilibria.

2. **Undirected single-sink counterpart (`undirectedBroadcastNetwork k ε`)**
   ([RoughgardenTardos2007]): replacing the directed arcs of `broadcastNetwork k ε` with unordered
   edges on the same vertices and costs collapses the price of stability from `H k` to **`1`**.
   Player `k - 1` traverses its cost-`1 / k` direct edge `{source (k - 1), sink}` while every
   other player `i` routes along the three-edge simple path
   `source i — hub — source (k - 1) — sink`,
   sharing `{source (k - 1), sink}` and zero-cost hub edges for a pure Nash equilibrium that
   globally minimizes social cost (`1 / k`).

3. **Two-node parallel-link network (`parallelNetwork k ε`)** ([RoughgardenTardos2007];
   [TardosWexler2007]): `k ≥ 1` players connect `false` to `true` across two parallel directed arcs
   of costs `1 + ε` and `k`. At `ε = 0`, all players sharing the cost-`k` arc is a pure Nash
   equilibrium of cost `k` against optimal cost `1` (**exact `PoA = k`**); for `ε > 0`, it is a
   **strict** pure Nash equilibrium of cost ratio `k / (1 + ε) → k`.

4. **Best pure Nash equilibrium need not minimize Rosenthal's potential (`potentialGapNetwork`)**
   ([TardosWexler2007]): a three-player single-sink network (`trunk` cost `2`, private bypass cost
   `6 / 5`) whose socially optimal profile (`socialCost = 2`, `Φ = 11 / 3`) is a pure Nash
   equilibrium, while the all-direct pure Nash equilibrium (`socialCost = 18 / 5`) strictly
   minimizes Rosenthal's potential (`Φ = 18 / 5`).

## Main definitions

* `Cslib.GameTheory.BroadcastVertex`, `Cslib.GameTheory.BroadcastArc`: vertices and arcs of the
  `(k + 2)`-node single-sink broadcast network.
* `Cslib.GameTheory.generalBroadcastNetwork`, `Cslib.GameTheory.broadcastNetwork`: parametric and
  harmonic-bypass directed single-sink fair connection games.
* `Cslib.GameTheory.undirectedBroadcastGraph`, `Cslib.GameTheory.undirectedBroadcastNetwork`:
  undirected simple-graph counterpart of `broadcastNetwork`.
* `Cslib.GameTheory.parallelNetwork`: two-vertex parallel-arc `PoA = k` witness family.
* `Cslib.GameTheory.potentialGapNetwork`: three-player network separating socially optimal pure
  Nash equilibria from potential minimizers.

## Main results

* `Cslib.GameTheory.generalBroadcastNetwork_path_eq_or`: every simple `source i`–`sink` dipath in
  the broadcast digraph is either `broadcastDirectPath` or `broadcastSharedPath`.
* `Cslib.GameTheory.broadcastNetwork_cost_eq_optOut`,
  `Cslib.GameTheory.isPureNash_broadcastNetwork_iff`: cost isomorphism with `CongestionGame.optOut`
  and uniqueness of the all-direct pure Nash equilibrium for `ε > 0`.
* `Cslib.GameTheory.exists_forall_isPureNash_broadcastNetwork_mul_lt`: **tightness of the `H_k`
  price-of-stability bound** on directed single-sink fair connection games.
* `Cslib.GameTheory.isPureNash_broadcastDirect_zero`,
  `Cslib.GameTheory.isPureNash_broadcastShared_zero`: at `ε = 0`, both the optimal `1`-cost network
  and the `H_k`-cost direct network are pure Nash equilibria.
* `Cslib.GameTheory.isPureNash_undirectedViaLastProfile`,
  `Cslib.GameTheory.socialCost_undirectedViaLastProfile_le`: **in the undirected `H_k` network,
  `PoS = 1`** ([RoughgardenTardos2007]).
* `Cslib.GameTheory.isPureNash_parallelExpensiveProfile`,
  `Cslib.GameTheory.socialCost_parallelExpensive_eq_mul_cheap`,
  `Cslib.GameTheory.exists_strictPureNash_parallelNetwork_mul_lt`: **tightness of `PoA = k`** (both
  exact at `ε = 0` and via strict pure Nash equilibria for `ε > 0`).
* `Cslib.GameTheory.potentialGapNetwork_best_nash_not_min_potential`: socially optimal pure Nash
  equilibrium with strictly larger Rosenthal potential than the global potential minimizer
  ([TardosWexler2007]).

## References

* [AnshelevichDKTWR2008]
* [Roughgarden2013CS364A]
* [RoughgardenTardos2007]
* [TardosWexler2007]
-/

public section

namespace Cslib.GameTheory

/-! ### 1. Parametric and `H_k` directed single-sink broadcast networks -/

/-- Vertices of the `(k + 2)`-node single-sink broadcast network: `k` player sources `source i`,
an intermediate meeting vertex `hub`, and the common `sink`. -/
inductive BroadcastVertex (k : ℕ) where
  | source (i : Fin k)
  | hub
  | sink
  deriving DecidableEq

/-- Equivalence between `BroadcastVertex k` and `Fin k ⊕ Bool`. -/
@[expose] def broadcastVertexEquiv (k : ℕ) : BroadcastVertex k ≃ Fin k ⊕ Bool where
  toFun
    | .source i => .inl i
    | .hub => .inr false
    | .sink => .inr true
  invFun
    | .inl i => .source i
    | .inr false => .hub
    | .inr true => .sink
  left_inv v := by cases v <;> rfl
  right_inv x := by rcases x with i | (_ | _) <;> rfl

instance instFintypeBroadcastVertex (k : ℕ) : Fintype (BroadcastVertex k) :=
  Fintype.ofEquiv (Fin k ⊕ Bool) (broadcastVertexEquiv k).symm

/-- Directed arcs of the single-sink broadcast network: zero-cost feeder arcs `toHub i`
(`source i → hub`), the shared `trunk` (`hub → sink`), and private bypass arcs `direct i`
(`source i → sink`). -/
inductive BroadcastArc (k : ℕ) where
  | toHub (i : Fin k)
  | trunk
  | direct (i : Fin k)
  deriving DecidableEq

/-- Equivalence between `BroadcastArc k` and `Fin k ⊕ Option (Fin k)`. -/
@[expose] def broadcastArcEquiv (k : ℕ) : BroadcastArc k ≃ Fin k ⊕ Option (Fin k) where
  toFun
    | .toHub i => .inl i
    | .trunk => .inr none
    | .direct i => .inr (some i)
  invFun
    | .inl i => .toHub i
    | .inr none => .trunk
    | .inr (some i) => .direct i
  left_inv e := by cases e <;> rfl
  right_inv x := by rcases x with i | (_ | j) <;> rfl

instance instFintypeBroadcastArc (k : ℕ) : Fintype (BroadcastArc k) :=
  Fintype.ofEquiv (Fin k ⊕ Option (Fin k)) (broadcastArcEquiv k).symm

/-- Source endpoint of a `BroadcastArc`. -/
@[expose] def BroadcastArc.src {k : ℕ} : BroadcastArc k → BroadcastVertex k
  | .toHub i => .source i
  | .trunk => .hub
  | .direct i => .source i

/-- Target endpoint of a `BroadcastArc`. -/
@[expose] def BroadcastArc.tgt {k : ℕ} : BroadcastArc k → BroadcastVertex k
  | .toHub _ => .hub
  | .trunk => .sink
  | .direct _ => .sink

/-- Parametric cost function on `BroadcastArc k`: `0` on feeder arcs `toHub i`, `trunkCost` on
`trunk`, and `directCost i` on `direct i`. -/
@[expose] def generalBroadcastArcCost {k : ℕ} (trunkCost : ℝ) (directCost : Fin k → ℝ) :
    BroadcastArc k → ℝ
  | .toHub _ => 0
  | .trunk => trunkCost
  | .direct i => directCost i

/-- Single-sink directed `FairConnectionGame` on `(BroadcastVertex k, BroadcastArc k)` with shared
trunk cost `trunkCost` and private bypass costs `directCost`. -/
@[expose] def generalBroadcastNetwork (k : ℕ) (trunkCost : ℝ) (directCost : Fin k → ℝ) :
    FairConnectionGame (Fin k) (BroadcastVertex k) (BroadcastArc k) where
  src := BroadcastArc.src
  tgt := BroadcastArc.tgt
  edgeCost := generalBroadcastArcCost trunkCost directCost
  source := BroadcastVertex.source
  sink _ := BroadcastVertex.sink

section GeneralBroadcast

variable {k : ℕ} {trunkCost : ℝ} {directCost : Fin k → ℝ}

/-- Player `i`'s 1-arc private bypass path `[direct i]`. -/
@[expose] def broadcastDirectPath (trunkCost : ℝ) (directCost : Fin k → ℝ) (i : Fin k) :
    (generalBroadcastNetwork k trunkCost directCost).Path i :=
  ⟨[.direct i], List.isChain_singleton _,
    by simp [generalBroadcastNetwork, BroadcastArc.tgt],
    fun _ he => by cases he; rfl, by simp, fun _ he => by cases he; rfl⟩

/-- Player `i`'s 2-arc shared path `[toHub i, trunk]`. -/
@[expose] def broadcastSharedPath (trunkCost : ℝ) (directCost : Fin k → ℝ) (i : Fin k) :
    (generalBroadcastNetwork k trunkCost directCost).Path i :=
  ⟨[.toHub i, .trunk], List.isChain_cons_cons.mpr ⟨rfl, List.isChain_singleton _⟩,
    by simp [generalBroadcastNetwork, BroadcastArc.tgt],
    fun _ he => by cases he; rfl, by simp,
    fun e he => by
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
        Option.some.injEq] at he
      subst he
      rfl⟩

theorem broadcastDirectPath_ne_sharedPath (i : Fin k) :
    broadcastDirectPath trunkCost directCost i ≠ broadcastSharedPath trunkCost directCost i := by
  intro h
  have := congrArg (fun p : (generalBroadcastNetwork k trunkCost directCost).Path i =>
    p.arcs.length) h
  norm_num [FairConnectionGame.Path.arcs, broadcastDirectPath, broadcastSharedPath] at this

private theorem no_arc_from_sink {e : BroadcastArc k} : BroadcastArc.src e ≠ .sink := by
  cases e <;> simp [BroadcastArc.src]

/-- **Complete classification of simple paths in the broadcast digraph**: every simple directed path
from `source i` to `sink` is either `[direct i]` or `[toHub i, trunk]`. -/
theorem generalBroadcastNetwork_path_eq_or {i : Fin k}
    (p : (generalBroadcastNetwork k trunkCost directCost).Path i) :
    p = broadcastDirectPath trunkCost directCost i ∨
      p = broadcastSharedPath trunkCost directCost i := by
  obtain ⟨q, hchain, _, hhd, hnil, hlast⟩ := p
  rcases q with _ | ⟨e₁, qs⟩
  · exact absurd (hnil rfl) (by rintro ⟨⟩)
  cases e₁ with
  | trunk => exact absurd (hhd .trunk rfl) (by rintro ⟨⟩)
  | direct j =>
    cases hhd (.direct j) rfl
    rcases qs with _ | ⟨_, _⟩
    · exact Or.inl rfl
    · exact absurd (List.isChain_cons_cons.mp hchain).1.symm no_arc_from_sink
  | toHub j =>
    cases hhd (.toHub j) rfl
    rcases qs with _ | ⟨e₂, rest⟩
    · exact absurd (hlast (.toHub i) rfl) (by rintro ⟨⟩)
    cases e₂ with
    | toHub _ | direct _ =>
      exact absurd (List.isChain_cons_cons.mp hchain).1.symm (by rintro ⟨⟩)
    | trunk =>
      rcases rest with _ | ⟨_, _⟩
      · exact Or.inr rfl
      · exact absurd (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchain).2).1.symm
          no_arc_from_sink

/-- Boolean indicator of whether `p` is the private bypass path `broadcastDirectPath`. -/
@[expose] def broadcastIsDirect {i : Fin k}
    (p : (generalBroadcastNetwork k trunkCost directCost).Path i) : Bool :=
  decide (p = broadcastDirectPath trunkCost directCost i)

@[simp]
theorem broadcastIsDirect_direct (i : Fin k) :
    broadcastIsDirect (broadcastDirectPath trunkCost directCost i) = true :=
  decide_eq_true rfl

@[simp]
theorem broadcastIsDirect_shared (i : Fin k) :
    broadcastIsDirect (broadcastSharedPath trunkCost directCost i) = false :=
  decide_eq_false (broadcastDirectPath_ne_sharedPath i).symm

theorem broadcastPath_eq_ite {i : Fin k}
    (p : (generalBroadcastNetwork k trunkCost directCost).Path i) :
    p = if broadcastIsDirect p then broadcastDirectPath trunkCost directCost i
      else broadcastSharedPath trunkCost directCost i := by
  rcases generalBroadcastNetwork_path_eq_or p with rfl | rfl <;> simp

private theorem mem_pathEdges_direct_iff {j i : Fin k}
    (p : (generalBroadcastNetwork k trunkCost directCost).Path j) :
    BroadcastArc.direct i ∈ (generalBroadcastNetwork k trunkCost directCost).pathEdges p ↔
      j = i ∧ broadcastIsDirect p = true := by
  rcases generalBroadcastNetwork_path_eq_or p with rfl | rfl
  · rw [broadcastIsDirect_direct]
    simp [FairConnectionGame.pathEdges, FairConnectionGame.Path.arcs, broadcastDirectPath, eq_comm]
  · rw [broadcastIsDirect_shared]
    simp [FairConnectionGame.pathEdges, FairConnectionGame.Path.arcs, broadcastSharedPath]

private theorem mem_pathEdges_trunk_iff {j : Fin k}
    (p : (generalBroadcastNetwork k trunkCost directCost).Path j) :
    BroadcastArc.trunk ∈ (generalBroadcastNetwork k trunkCost directCost).pathEdges p ↔
      broadcastIsDirect p = false := by
  rcases generalBroadcastNetwork_path_eq_or p with rfl | rfl
  · rw [broadcastIsDirect_direct]
    simp [FairConnectionGame.pathEdges, FairConnectionGame.Path.arcs, broadcastDirectPath]
  · rw [broadcastIsDirect_shared]
    simp [FairConnectionGame.pathEdges, FairConnectionGame.Path.arcs, broadcastSharedPath]

/-- Closed-form player cost in `generalBroadcastNetwork`: `directCost i` on the private bypass, and
`trunkCost / m` when `m` players share the trunk (the zero-cost feeder arc `toHub i` adds `0`). -/
theorem generalBroadcastNetwork_cost
    (s : ∀ i, (generalBroadcastNetwork k trunkCost directCost).Path i) (i : Fin k) :
    (generalBroadcastNetwork k trunkCost directCost).toCostGame.cost i s =
      if broadcastIsDirect (s i) then directCost i
      else trunkCost / (Finset.univ.filter fun j => broadcastIsDirect (s j) = false).card := by
  rw [FairConnectionGame.toCostGame_cost]
  rcases generalBroadcastNetwork_path_eq_or (s i) with hi | hi
  · rw [hi, broadcastIsDirect_direct]
    simp only [↓reduceIte]
    have hload : (generalBroadcastNetwork k trunkCost directCost).edgeLoad s (.direct i) = 1 :=
      Finset.card_eq_one.mpr ⟨i, Finset.ext fun j => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          mem_pathEdges_direct_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, by rw [h, hi, broadcastIsDirect_direct]⟩⟩⟩
    change ∑ e ∈ ({BroadcastArc.direct i} : Finset (BroadcastArc k)), _ = _
    rw [Finset.sum_singleton, hload, Nat.cast_one, div_one]
    rfl
  · rw [hi, broadcastIsDirect_shared]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hload : (generalBroadcastNetwork k trunkCost directCost).edgeLoad s .trunk =
        (Finset.univ.filter fun j => broadcastIsDirect (s j) = false).card :=
      congrArg Finset.card (Finset.filter_congr fun j _ => mem_pathEdges_trunk_iff (s j))
    change ∑ e ∈ ({BroadcastArc.toHub i, .trunk} : Finset (BroadcastArc k)), _ = _
    rw [Finset.sum_pair (by rintro ⟨⟩), hload]
    change 0 / _ + trunkCost / _ = _
    rw [zero_div, zero_add]

theorem generalBroadcastNetwork_terminalsConnected :
    (generalBroadcastNetwork k trunkCost directCost).TerminalsConnected :=
  fun i => ⟨_, (broadcastDirectPath trunkCost directCost i).isDipath⟩

end GeneralBroadcast

/-- **Anshelevich et al. directed single-sink `H_k` network** ([AnshelevichDKTWR2008];
[RoughgardenTardos2007], Example 17.3; [TardosWexler2007], Section 19.3.1): `k` sources connect to a
common sink using zero-cost feeder arcs `source i → hub`, a shared `trunk` (`hub → sink`) of cost
`1 + ε`, and private bypasses `source i → sink` of cost `1 / (i + 1)`. -/
noncomputable abbrev broadcastNetwork (k : ℕ) (ε : ℝ) :
    FairConnectionGame (Fin k) (BroadcastVertex k) (BroadcastArc k) :=
  generalBroadcastNetwork k (1 + ε) fun i => 1 / ((i : ℕ) + 1)

/-- Profile on `broadcastNetwork k ε` in which every player uses its private bypass `direct i`. -/
noncomputable abbrev broadcastDirectProfile (k : ℕ) (ε : ℝ) :
    ∀ i, (broadcastNetwork k ε).Path i :=
  fun i => broadcastDirectPath (1 + ε) (fun j => 1 / ((j : ℕ) + 1)) i

/-- Profile on `broadcastNetwork k ε` in which every player routes through `hub` and shares `trunk`.
-/
noncomputable abbrev broadcastSharedProfile (k : ℕ) (ε : ℝ) :
    ∀ i, (broadcastNetwork k ε).Path i :=
  fun i => broadcastSharedPath (1 + ε) (fun j => 1 / ((j : ℕ) + 1)) i

theorem broadcastNetwork_edgeCost_nonneg {k : ℕ} {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ e, 0 ≤ (broadcastNetwork k ε).edgeCost e
  | .toHub _ => le_rfl
  | .trunk => by change 0 ≤ 1 + ε; linarith
  | .direct _ => by change 0 ≤ 1 / (_ + 1 : ℝ); positivity

/-- **Exact cost isomorphism between `broadcastNetwork k ε` and `CongestionGame.optOut k ε`**:
retaining the zero-cost feeder arcs `source i → hub` preserves every player's cost under
`broadcastIsDirect`. -/
theorem broadcastNetwork_cost_eq_optOut {k : ℕ} {ε : ℝ}
    (s : ∀ i, (broadcastNetwork k ε).Path i) (i : Fin k) :
    (broadcastNetwork k ε).toCostGame.cost i s =
      (CongestionGame.optOut k ε).toCostGame.cost i (fun j => broadcastIsDirect (s j)) := by
  rw [generalBroadcastNetwork_cost, CongestionGame.optOut_cost]

theorem broadcastNetwork_socialCost_eq_optOut {k : ℕ} {ε : ℝ}
    (s : ∀ i, (broadcastNetwork k ε).Path i) :
    (broadcastNetwork k ε).toCostGame.socialCost s =
      (CongestionGame.optOut k ε).toCostGame.socialCost (fun j => broadcastIsDirect (s j)) := by
  simp only [CostGame.socialCost, broadcastNetwork_cost_eq_optOut]

theorem socialCost_broadcastDirectProfile (k : ℕ) (ε : ℝ) :
    (broadcastNetwork k ε).toCostGame.socialCost (broadcastDirectProfile k ε) = harmonic k := by
  have htrue : (fun j => broadcastIsDirect (broadcastDirectProfile k ε j)) = fun _ => true :=
    funext broadcastIsDirect_direct
  rw [broadcastNetwork_socialCost_eq_optOut, htrue, CongestionGame.socialCost_optOut_true]

theorem socialCost_broadcastSharedProfile {k : ℕ} (hk : k ≠ 0) (ε : ℝ) :
    (broadcastNetwork k ε).toCostGame.socialCost (broadcastSharedProfile k ε) = 1 + ε := by
  have hfalse : (fun j => broadcastIsDirect (broadcastSharedProfile k ε j)) = fun _ => false :=
    funext broadcastIsDirect_shared
  rw [broadcastNetwork_socialCost_eq_optOut, hfalse, CongestionGame.socialCost_optOut_false hk]

private theorem broadcastIsDirect_update {k : ℕ} {ε : ℝ}
    (s : ∀ i, (broadcastNetwork k ε).Path i) (i : Fin k) (b : Bool) :
    (fun j => broadcastIsDirect (Function.update s i
      (if b then broadcastDirectProfile k ε i else broadcastSharedProfile k ε i) j)) =
      Function.update (fun j => broadcastIsDirect (s j)) i b := by
  funext j
  by_cases hji : j = i
  · subst hji
    cases b <;> simp [broadcastDirectProfile, broadcastSharedProfile]
  · simp [hji]

theorem isPureNash_broadcastNetwork_iff_optOut {k : ℕ} {ε : ℝ}
    (s : ∀ i, (broadcastNetwork k ε).Path i) :
    (broadcastNetwork k ε).toCostGame.IsPureNash s ↔
      (CongestionGame.optOut k ε).toCostGame.IsPureNash (fun j => broadcastIsDirect (s j)) := by
  refine ⟨fun hs i b => ?_, fun hs i a => ?_⟩
  · simpa only [broadcastNetwork_cost_eq_optOut, broadcastIsDirect_update] using
      hs i (if b then broadcastDirectProfile k ε i else broadcastSharedProfile k ε i)
  · have h := hs i (broadcastIsDirect a)
    rwa [← broadcastNetwork_cost_eq_optOut, ← broadcastIsDirect_update,
      ← broadcastNetwork_cost_eq_optOut, ← broadcastPath_eq_ite a] at h

/-- **For `ε > 0`, the unique pure Nash equilibrium of `broadcastNetwork k ε` is the all-direct
profile** ([RoughgardenTardos2007], Example 17.3; [TardosWexler2007], Section 19.3.1). -/
theorem isPureNash_broadcastNetwork_iff {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (s : ∀ i, (broadcastNetwork k ε).Path i) :
    (broadcastNetwork k ε).toCostGame.IsPureNash s ↔ s = broadcastDirectProfile k ε := by
  rw [isPureNash_broadcastNetwork_iff_optOut, CongestionGame.isPureNash_optOut_iff hε]
  refine ⟨fun h => funext fun i => ?_, ?_⟩
  · have hp := broadcastPath_eq_ite (s i)
    simpa [congrFun h i, broadcastDirectProfile] using hp
  · rintro rfl
    exact funext broadcastIsDirect_direct

/-- **Tightness of Anshelevich et al.'s `H_k` price-of-stability bound on single-sink directed
networks** ([AnshelevichDKTWR2008]; [TardosWexler2007], Section 19.3.1): for `k ≥ 1` players and
every `r < H k`, there is `ε > 0` such that `broadcastNetwork k ε` has nonnegative edge costs,
connected terminals, and **every** pure Nash equilibrium `s` has social cost strictly exceeding
`r` times the shared-arborescence cost `1 + ε`. -/
theorem exists_forall_isPureNash_broadcastNetwork_mul_lt {k : ℕ} (hk : k ≠ 0) {r : ℝ}
    (hr : r < harmonic k) :
    ∃ ε > 0, (∀ e, 0 ≤ (broadcastNetwork k ε).edgeCost e) ∧
      (broadcastNetwork k ε).TerminalsConnected ∧
      ∀ s, (broadcastNetwork k ε).toCostGame.IsPureNash s →
        r * (broadcastNetwork k ε).toCostGame.socialCost (broadcastSharedProfile k ε)
          < (broadcastNetwork k ε).toCostGame.socialCost s := by
  obtain ⟨ε, hε, hlt⟩ := CongestionGame.exists_forall_isPureNash_optOut_mul_lt hk hr
  refine ⟨ε, hε, broadcastNetwork_edgeCost_nonneg hε.le, generalBroadcastNetwork_terminalsConnected,
    fun s hs => ?_⟩
  have h := hlt _ ((isPureNash_broadcastNetwork_iff_optOut s).1 hs)
  rw [CongestionGame.socialCost_optOut_false hk, ← broadcastNetwork_socialCost_eq_optOut] at h
  rwa [socialCost_broadcastSharedProfile hk]

/-- At `ε = 0`, the all-direct profile (of social cost `H k`) is still a pure Nash equilibrium of
`broadcastNetwork k 0`. -/
theorem isPureNash_broadcastDirect_zero (k : ℕ) :
    (broadcastNetwork k 0).toCostGame.IsPureNash (broadcastDirectProfile k 0) := by
  have htrue : (fun j => broadcastIsDirect (broadcastDirectProfile k 0 j)) = fun _ => true :=
    funext broadcastIsDirect_direct
  rw [isPureNash_broadcastNetwork_iff_optOut, htrue]
  intro i b
  cases b
  · simp only [CongestionGame.optOut_cost, Function.update_self, Bool.false_eq_true, ↓reduceIte]
    rw [Finset.card_eq_one.mpr ⟨i, Finset.ext fun j => by
      by_cases h : j = i <;> simp [h]⟩]
    simp only [Nat.cast_one, add_zero, div_one]
    exact div_le_self zero_le_one (by norm_cast; omega)
  · rw [Function.update_eq_self]

/-- At `ε = 0`, the socially optimal all-shared profile (of social cost `1` for `k ≥ 1`) is also a
pure Nash equilibrium of `broadcastNetwork k 0`: each player pays `1 / k ≤ 1 / (i + 1)`. -/
theorem isPureNash_broadcastShared_zero (k : ℕ) :
    (broadcastNetwork k 0).toCostGame.IsPureNash (broadcastSharedProfile k 0) := by
  have hfalse : (fun j => broadcastIsDirect (broadcastSharedProfile k 0 j)) = fun _ => false :=
    funext broadcastIsDirect_shared
  rw [isPureNash_broadcastNetwork_iff_optOut, hfalse]
  intro i b
  cases b
  · rw [Function.update_eq_self]
  · rw [CongestionGame.optOut_cost, CongestionGame.optOut_cost, Function.update_self,
      Finset.filter_true_of_mem fun _ _ => rfl]
    simp only [Finset.card_univ, Fintype.card_fin, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_of_lt i.isLt)

/-! ### 2. Undirected single-sink counterpart (`PoS = 1`) -/

private def broadcastRel (k : ℕ) : BroadcastVertex k → BroadcastVertex k → Prop
  | .source _, .hub => True
  | .source _, .sink => True
  | .hub, .sink => True
  | _, _ => False

/-- Underlying simple graph of the undirected single-sink `H_k` example ([RoughgardenTardos2007]):
unordered edges `{source i, hub}`, `{hub, sink}`, and `{source i, sink}`. -/
def undirectedBroadcastGraph (k : ℕ) : SimpleGraph (BroadcastVertex k) :=
  SimpleGraph.fromRel (broadcastRel k)

private noncomputable def broadcastPairCost (k : ℕ) (ε : ℝ) :
    BroadcastVertex k → BroadcastVertex k → ℝ
  | .source i, .sink | .sink, .source i => 1 / ((i : ℕ) + 1)
  | .hub, .sink | .sink, .hub => 1 + ε
  | _, _ => 0

private theorem broadcastPairCost_symm (k : ℕ) (ε : ℝ) (u v : BroadcastVertex k) :
    broadcastPairCost k ε u v = broadcastPairCost k ε v u := by
  cases u <;> cases v <;> rfl

/-- Edge costs on `Sym2 (BroadcastVertex k)`: `0` on `{source i, hub}`, `1 + ε` on `{hub, sink}`,
and `1 / (i + 1)` on `{source i, sink}`. -/
noncomputable def undirectedBroadcastEdgeCost (k : ℕ) (ε : ℝ) :
    Sym2 (BroadcastVertex k) → ℝ :=
  Sym2.lift ⟨broadcastPairCost k ε, broadcastPairCost_symm k ε⟩

/-- **Undirected single-sink `H_k` fair connection game** ([RoughgardenTardos2007]). -/
noncomputable abbrev undirectedBroadcastNetwork (k : ℕ) (ε : ℝ) :
    UndirectedFairConnectionGame (Fin k) (BroadcastVertex k) where
  graph := undirectedBroadcastGraph k
  edgeCost := undirectedBroadcastEdgeCost k ε
  source := BroadcastVertex.source
  sink _ := BroadcastVertex.sink

theorem undirectedBroadcastEdgeCost_nonneg {k : ℕ} {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ e, 0 ≤ undirectedBroadcastEdgeCost k ε e := by
  refine Sym2.ind fun u v => ?_
  cases u <;> cases v <;> simp only [undirectedBroadcastEdgeCost, Sym2.lift_mk]
  all_goals dsimp only [broadcastPairCost]
  all_goals first | exact le_rfl | positivity

private theorem undirectedAdj_source_hub {k : ℕ} (i : Fin k) :
    (undirectedBroadcastGraph k).Adj (.source i) .hub :=
  ⟨by rintro ⟨⟩, Or.inl trivial⟩

private theorem undirectedAdj_source_sink {k : ℕ} (i : Fin k) :
    (undirectedBroadcastGraph k).Adj (.source i) .sink :=
  ⟨by rintro ⟨⟩, Or.inl trivial⟩

private def broadcastLast {k : ℕ} (hk : 0 < k) : Fin k :=
  ⟨k - 1, Nat.sub_lt hk zero_lt_one⟩

/-- Strategy profile in `undirectedBroadcastNetwork k ε` (`k > 0`) routing every player through
player `k - 1`'s cost-`1 / k` edge `{source (k - 1), sink}` via the zero-cost hub edges: player
`last = k - 1` takes `source last — sink` and every `i ≠ last` takes
`source i — hub — source last — sink`. -/
noncomputable def undirectedViaLastProfile {k : ℕ} (hk : 0 < k) (ε : ℝ) :
    ∀ i, (undirectedBroadcastNetwork k ε).Path i := fun i =>
  if hi : i = broadcastLast hk then
    SimpleGraph.Path.singleton (undirectedAdj_source_sink i)
  else
    ⟨SimpleGraph.Walk.cons (undirectedAdj_source_hub i)
        (SimpleGraph.Walk.cons (undirectedAdj_source_hub (broadcastLast hk)).symm
          (SimpleGraph.Walk.cons (undirectedAdj_source_sink (broadcastLast hk))
            SimpleGraph.Walk.nil)),
      (SimpleGraph.Walk.isPath_def _).mpr (by simp [hi])⟩

private theorem last_edge_mem_undirectedViaLastProfile {k : ℕ} (hk : 0 < k) (ε : ℝ) (i : Fin k) :
    s(BroadcastVertex.source (broadcastLast hk), BroadcastVertex.sink) ∈
      (undirectedBroadcastNetwork k ε).pathEdges (undirectedViaLastProfile hk ε i) := by
  unfold undirectedViaLastProfile
  split_ifs with hi
  · rw [hi]
    simp [UndirectedFairConnectionGame.pathEdges, SimpleGraph.Path.singleton]
  · simp [UndirectedFairConnectionGame.pathEdges]

theorem cost_undirectedViaLastProfile {k : ℕ} (hk : 0 < k) (ε : ℝ) (i : Fin k) :
    (undirectedBroadcastNetwork k ε).toCostGame.cost i (undirectedViaLastProfile hk ε) =
      (1 / (k : ℝ)) / k := by
  have hlast_val : (((broadcastLast hk : Fin k) : ℕ) : ℝ) + 1 = k := by
    exact_mod_cast Nat.sub_add_cancel hk
  have hload : (undirectedBroadcastNetwork k ε).edgeLoad (undirectedViaLastProfile hk ε)
      s(.source (broadcastLast hk), .sink) = k := by
    rw [UndirectedFairConnectionGame.edgeLoad, Finset.filter_true_of_mem fun j _ =>
      last_edge_mem_undirectedViaLastProfile hk ε j, Finset.card_univ, Fintype.card_fin]
  have hzero (e) (he : e ∈ (undirectedBroadcastNetwork k ε).pathEdges
      (undirectedViaLastProfile hk ε i))
      (hne : e ≠ s(.source (broadcastLast hk), .sink)) :
      (undirectedBroadcastNetwork k ε).edgeCost e /
        (undirectedBroadcastNetwork k ε).edgeLoad (undirectedViaLastProfile hk ε) e = 0 := by
    unfold undirectedViaLastProfile at he
    split_ifs at he with hi
    · rw [hi] at he
      simp only [UndirectedFairConnectionGame.pathEdges, SimpleGraph.Path.singleton,
        SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_toFinset,
        List.mem_singleton] at he
      exact absurd he hne
    · simp only [UndirectedFairConnectionGame.pathEdges, List.mem_toFinset,
        SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · simp [undirectedBroadcastEdgeCost, broadcastPairCost]
      · simp [undirectedBroadcastEdgeCost, broadcastPairCost]
      · exact absurd rfl hne
  rw [UndirectedFairConnectionGame.toCostGame_cost,
    Finset.sum_eq_single_of_mem _ (last_edge_mem_undirectedViaLastProfile hk ε i) hzero, hload]
  change (1 / ((((broadcastLast hk : Fin k) : ℕ) : ℝ) + 1)) / k = _
  rw [hlast_val]

theorem socialCost_undirectedViaLastProfile {k : ℕ} (hk : 0 < k) (ε : ℝ) :
    (undirectedBroadcastNetwork k ε).toCostGame.socialCost (undirectedViaLastProfile hk ε) =
      1 / k := by
  rw [CostGame.socialCost, Finset.sum_congr rfl fun i _ => cost_undirectedViaLastProfile hk ε i,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  exact mul_div_cancel₀ _ hkR

private theorem exists_adj_mem_edges_of_ne {V : Type*} {G : SimpleGraph V} {u v : V}
    (w : G.Walk u v) (huv : u ≠ v) : ∃ x, G.Adj u x ∧ s(u, x) ∈ w.edges := by
  cases w with
  | nil => exact absurd rfl huv
  | cons hadj _ => exact ⟨_, hadj, by simp⟩

/-- Every `source j`–`sink` path in `undirectedBroadcastNetwork k ε` (`k > 0`, `ε ≥ 0`) traverses an
edge incident to `sink`, whose cost is at least `1 / k`. -/
private theorem one_div_le_sum_pathEdges_undirectedBroadcast {k : ℕ} (hk : 0 < k) {ε : ℝ}
    (hε : 0 ≤ ε) {j : Fin k} (p : (undirectedBroadcastNetwork k ε).Path j) :
    1 / (k : ℝ) ≤ ∑ e ∈ (undirectedBroadcastNetwork k ε).pathEdges p,
      undirectedBroadcastEdgeCost k ε e := by
  obtain ⟨x, hadj, hmem_rev⟩ :=
    exists_adj_mem_edges_of_ne p.val.reverse (by rintro ⟨⟩)
  rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hmem_rev
  have hmem : s(.sink, x) ∈ (undirectedBroadcastNetwork k ε).pathEdges p :=
    List.mem_toFinset.2 hmem_rev
  have hge : 1 / (k : ℝ) ≤ undirectedBroadcastEdgeCost k ε s(.sink, x) := by
    cases x with
    | sink => exact absurd rfl hadj.ne
    | hub =>
      change 1 / (k : ℝ) ≤ 1 + ε
      have h1 : 1 / (k : ℝ) ≤ 1 := div_le_self zero_le_one (by exact_mod_cast hk)
      linarith
    | source m =>
      change 1 / (k : ℝ) ≤ 1 / ((m : ℕ) + 1 : ℝ)
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_of_lt m.isLt)
  exact hge.trans (Finset.single_le_sum
    (fun e _ => undirectedBroadcastEdgeCost_nonneg hε e) hmem)

/-- **`undirectedViaLastProfile` globally minimizes social cost** in
`undirectedBroadcastNetwork k ε` for `k > 0` and `ε ≥ 0`: every profile costs at least `1 / k`. -/
theorem socialCost_undirectedViaLastProfile_le {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 ≤ ε)
    (s' : ∀ i, (undirectedBroadcastNetwork k ε).Path i) :
    (undirectedBroadcastNetwork k ε).toCostGame.socialCost (undirectedViaLastProfile hk ε)
      ≤ (undirectedBroadcastNetwork k ε).toCostGame.socialCost s' := by
  rw [socialCost_undirectedViaLastProfile hk ε]
  exact (one_div_le_sum_pathEdges_undirectedBroadcast hk hε (s' ⟨0, hk⟩)).trans
    (CongestionGame.sum_le_socialCost_fairCostSharing _ _
      (undirectedBroadcastEdgeCost_nonneg hε) s' ⟨0, hk⟩)

/-- **In the undirected `H_k` network, `undirectedViaLastProfile` is a pure Nash equilibrium** (so
**`PoS = 1`**, [RoughgardenTardos2007]): in every profile every player pays at least
`(1 / k) / k`, which `undirectedViaLastProfile` already achieves. -/
theorem isPureNash_undirectedViaLastProfile {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 ≤ ε) :
    (undirectedBroadcastNetwork k ε).toCostGame.IsPureNash (undirectedViaLastProfile hk ε) := by
  intro i a
  rw [cost_undirectedViaLastProfile hk ε i]
  have h1 : (1 / (k : ℝ)) / k ≤
      (∑ e ∈ (undirectedBroadcastNetwork k ε).pathEdges a,
        undirectedBroadcastEdgeCost k ε e) / Fintype.card (Fin k) := by
    rw [Fintype.card_fin]
    exact div_le_div_of_nonneg_right (one_div_le_sum_pathEdges_undirectedBroadcast hk hε a)
      (Nat.cast_nonneg _)
  have h2 := CongestionGame.sum_div_card_le_cost_fairCostSharing
    (fun _ p => (undirectedBroadcastNetwork k ε).pathEdges p) (undirectedBroadcastEdgeCost k ε)
    (undirectedBroadcastEdgeCost_nonneg hε) (Function.update (undirectedViaLastProfile hk ε) i a) i
  rw [Function.update_self] at h2
  exact h1.trans h2

/-! ### 3. Two-node parallel-link `PoA = k` witness (`parallelNetwork k ε`) -/

/-- **Two-node parallel-arc Shapley network design game** ([RoughgardenTardos2007];
[TardosWexler2007]): `k` players connect `false` to `true` across two parallel directed arcs
(`true` of cost `1 + ε` and `false` of cost `k`). -/
@[expose] noncomputable def parallelNetwork (k : ℕ) (ε : ℝ) :
    FairConnectionGame (Fin k) Bool Bool where
  src _ := false
  tgt _ := true
  edgeCost b := if b then 1 + ε else k
  source _ := false
  sink _ := true

/-- Player `i` takes the cheap arc `true` (cost `1 + ε`). -/
@[expose] def parallelCheapPath (k : ℕ) (ε : ℝ) (i : Fin k) : (parallelNetwork k ε).Path i :=
  ⟨[true], List.isChain_singleton _, by simp [parallelNetwork],
    fun _ h => by cases h; rfl, by simp, fun _ h => by cases h; rfl⟩

/-- Player `i` takes the expensive arc `false` (cost `k`). -/
@[expose] def parallelExpensivePath (k : ℕ) (ε : ℝ) (i : Fin k) : (parallelNetwork k ε).Path i :=
  ⟨[false], List.isChain_singleton _, by simp [parallelNetwork],
    fun _ h => by cases h; rfl, by simp, fun _ h => by cases h; rfl⟩

/-- Profile on `parallelNetwork k ε` in which all `k` players share the cheap arc `true`. -/
@[expose] def parallelCheapProfile (k : ℕ) (ε : ℝ) : ∀ i, (parallelNetwork k ε).Path i :=
  parallelCheapPath k ε

/-- Profile on `parallelNetwork k ε` in which all `k` players share the expensive arc `false`. -/
@[expose] def parallelExpensiveProfile (k : ℕ) (ε : ℝ) : ∀ i, (parallelNetwork k ε).Path i :=
  parallelExpensivePath k ε

/-- Every simple dipath in `parallelNetwork k ε` is `[true]` or `[false]`. -/
theorem parallelNetwork_path_eq_or {k : ℕ} {ε : ℝ} {i : Fin k}
    (p : (parallelNetwork k ε).Path i) :
    p = parallelCheapPath k ε i ∨ p = parallelExpensivePath k ε i := by
  obtain ⟨q, hchain, _, _, hnil, _⟩ := p
  rcases q with _ | ⟨b, qs⟩
  · exact absurd (hnil rfl) Bool.false_ne_true
  · rcases qs with _ | ⟨_, _⟩
    · cases b
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact absurd (List.isChain_cons_cons.mp hchain).1 Bool.noConfusion

theorem parallelNetwork_edgeCost_nonneg {k : ℕ} {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ b, 0 ≤ (parallelNetwork k ε).edgeCost b
  | true => by change 0 ≤ 1 + ε; linarith
  | false => Nat.cast_nonneg k

private theorem formedEdges_parallel_singleton {k : ℕ} (hk : k ≠ 0) {ε : ℝ} {b : Bool}
    {s : ∀ i, (parallelNetwork k ε).Path i} (hs : ∀ i, (s i).arcs = [b]) :
    (parallelNetwork k ε).formedEdges s = {b} := by
  ext e
  simp only [FairConnectionGame.formedEdges, Finset.mem_biUnion, Finset.mem_univ, true_and,
    FairConnectionGame.pathEdges, hs, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
    Finset.mem_singleton]
  exact ⟨fun ⟨_, he⟩ => he, fun he => ⟨⟨0, Nat.pos_of_ne_zero hk⟩, he⟩⟩

theorem socialCost_parallelCheapProfile {k : ℕ} (hk : k ≠ 0) (ε : ℝ) :
    (parallelNetwork k ε).toCostGame.socialCost (parallelCheapProfile k ε) = 1 + ε := by
  rw [FairConnectionGame.socialCost_eq_sum_formedEdges,
    formedEdges_parallel_singleton hk fun _ => rfl, Finset.sum_singleton]
  rfl

theorem socialCost_parallelExpensiveProfile {k : ℕ} (hk : k ≠ 0) (ε : ℝ) :
    (parallelNetwork k ε).toCostGame.socialCost (parallelExpensiveProfile k ε) = k := by
  rw [FairConnectionGame.socialCost_eq_sum_formedEdges,
    formedEdges_parallel_singleton hk fun _ => rfl, Finset.sum_singleton]
  rfl

/-- At `parallelExpensiveProfile k ε`, each player pays `1` (`= k / k`). -/
theorem cost_parallelExpensiveProfile {k : ℕ} (hk : k ≠ 0) (ε : ℝ) (i : Fin k) :
    (parallelNetwork k ε).toCostGame.cost i (parallelExpensiveProfile k ε) = 1 := by
  rw [FairConnectionGame.toCostGame_cost]
  have hload : (parallelNetwork k ε).edgeLoad (parallelExpensiveProfile k ε) false = k := by
    rw [FairConnectionGame.edgeLoad,
      Finset.filter_true_of_mem fun _ _ => by
        simp [FairConnectionGame.pathEdges, FairConnectionGame.Path.arcs, parallelExpensiveProfile,
          parallelExpensivePath],
      Finset.card_univ, Fintype.card_fin]
  change ∑ b ∈ ({false} : Finset Bool), _ = 1
  rw [Finset.sum_singleton, hload]
  exact div_self (Nat.cast_ne_zero.mpr hk)

private theorem cost_update_parallelExpensive_cheap {k : ℕ} (ε : ℝ) (i : Fin k) :
    (parallelNetwork k ε).toCostGame.cost i
      (Function.update (parallelExpensiveProfile k ε) i (parallelCheapPath k ε i)) = 1 + ε := by
  rw [FairConnectionGame.toCostGame_cost, Function.update_self]
  have hload : (parallelNetwork k ε).edgeLoad
      (Function.update (parallelExpensiveProfile k ε) i (parallelCheapPath k ε i)) true = 1 :=
    Finset.card_eq_one.mpr ⟨i, Finset.ext fun j => by
      by_cases hji : j = i <;>
        simp [hji, FairConnectionGame.pathEdges, FairConnectionGame.Path.arcs, parallelCheapPath,
          parallelExpensiveProfile, parallelExpensivePath]⟩
  change ∑ b ∈ ({true} : Finset Bool), _ = 1 + ε
  rw [Finset.sum_singleton, hload, Nat.cast_one, div_one]
  rfl

/-- **All players sharing the cost-`k` arc is a pure Nash equilibrium** for `k ≥ 1` and `ε ≥ 0`:
each player pays `k / k = 1`, while deviating alone to the cheap arc costs `1 + ε ≥ 1`. -/
theorem isPureNash_parallelExpensiveProfile {k : ℕ} (hk : k ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    (parallelNetwork k ε).toCostGame.IsPureNash (parallelExpensiveProfile k ε) := by
  intro i a
  rcases parallelNetwork_path_eq_or a with rfl | rfl
  · rw [cost_parallelExpensiveProfile hk ε i, cost_update_parallelExpensive_cheap]
    linarith
  · have hsame : Function.update (parallelExpensiveProfile k ε) i (parallelExpensivePath k ε i) =
        parallelExpensiveProfile k ε := Function.update_eq_self i _
    rw [hsame]

/-- **Exact `PoA = k` witness** ([RoughgardenTardos2007]; [TardosWexler2007]): for `k ≥ 1` at
`ε = 0`, `parallelExpensiveProfile k 0` is a pure Nash equilibrium of social cost `k * OPT`, and
`parallelCheapProfile k 0` achieves the minimum social cost `1` across all profiles. -/
theorem socialCost_parallelExpensive_eq_mul_cheap {k : ℕ} (hk : k ≠ 0) :
    (parallelNetwork k 0).toCostGame.IsPureNash (parallelExpensiveProfile k 0) ∧
      (∀ s', (parallelNetwork k 0).toCostGame.socialCost (parallelCheapProfile k 0)
        ≤ (parallelNetwork k 0).toCostGame.socialCost s') ∧
      (parallelNetwork k 0).toCostGame.socialCost (parallelExpensiveProfile k 0) =
        Fintype.card (Fin k) *
          (parallelNetwork k 0).toCostGame.socialCost (parallelCheapProfile k 0) := by
  refine ⟨isPureNash_parallelExpensiveProfile hk le_rfl, fun s' => ?_, ?_⟩
  · rw [socialCost_parallelCheapProfile hk 0, add_zero]
    have i₀ : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
    have h1 : (1 : ℝ) ≤ ∑ b ∈ (parallelNetwork k 0).pathEdges (s' i₀),
        (parallelNetwork k 0).edgeCost b := by
      rcases parallelNetwork_path_eq_or (s' i₀) with h | h <;> rw [h]
      · simp [FairConnectionGame.pathEdges, FairConnectionGame.Path.arcs, parallelCheapPath,
          parallelNetwork]
      · simp only [FairConnectionGame.pathEdges, FairConnectionGame.Path.arcs,
          parallelExpensivePath, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
          Finset.sum_singleton, parallelNetwork, Bool.false_eq_true, ↓reduceIte]
        exact_mod_cast Nat.pos_of_ne_zero hk
    exact h1.trans (CongestionGame.sum_le_socialCost_fairCostSharing _ _
      (parallelNetwork_edgeCost_nonneg le_rfl) s' i₀)
  · rw [socialCost_parallelExpensiveProfile hk 0, socialCost_parallelCheapProfile hk 0,
      Fintype.card_fin, add_zero, mul_one]

/-- **Strict pure Nash equilibrium `PoA → k` witness** ([RoughgardenTardos2007]):
for `k ≥ 1` and every `r < k`, there exists `ε > 0` such that `parallelExpensiveProfile k ε` is a
strict pure Nash equilibrium (every unilateral deviation to a distinct path strictly increases the
deviator's cost) whose social cost exceeds `r` times `socialCost (parallelCheapProfile k ε)`. -/
theorem exists_strictPureNash_parallelNetwork_mul_lt {k : ℕ} (hk : k ≠ 0) {r : ℝ}
    (hr : r < k) :
    ∃ ε > 0, (∀ i (a : (parallelNetwork k ε).Path i), a ≠ parallelExpensiveProfile k ε i →
        (parallelNetwork k ε).toCostGame.cost i (parallelExpensiveProfile k ε) <
          (parallelNetwork k ε).toCostGame.cost i
            (Function.update (parallelExpensiveProfile k ε) i a)) ∧
      r * (parallelNetwork k ε).toCostGame.socialCost (parallelCheapProfile k ε) <
        (parallelNetwork k ε).toCostGame.socialCost (parallelExpensiveProfile k ε) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  obtain ⟨ε, hε, hlt⟩ : ∃ ε > 0, r * (1 + ε) < k := by
    rcases le_or_gt r 0 with hr0 | hr0
    · exact ⟨1, one_pos, by nlinarith⟩
    · refine ⟨(k - r) / (2 * r), div_pos (by linarith) (by linarith), ?_⟩
      have : r * (1 + (k - r) / (2 * r)) = (r + k) / 2 := by field_simp; ring
      rw [this]
      linarith
  refine ⟨ε, hε, fun i a hne => ?_, ?_⟩
  · rcases parallelNetwork_path_eq_or a with rfl | rfl
    · rw [cost_parallelExpensiveProfile hk ε i, cost_update_parallelExpensive_cheap]
      linarith
    · exact absurd rfl hne
  · rw [socialCost_parallelCheapProfile hk ε, socialCost_parallelExpensiveProfile hk ε]
    exact hlt

/-! ### 4. Socially best pure Nash need not minimize Rosenthal's potential -/

/-- Three-player single-sink fair connection game separating socially optimal pure Nash equilibria
from global minimizers of Rosenthal's potential ([TardosWexler2007]): `trunk` costs `2`, feeder
arcs `toHub i` cost `0`, and each player's private bypass `direct i` costs `6 / 5`. -/
noncomputable abbrev potentialGapNetwork :
    FairConnectionGame (Fin 3) (BroadcastVertex 3) (BroadcastArc 3) :=
  generalBroadcastNetwork 3 2 fun _ => 6 / 5

/-- All three players share `trunk` (`socialCost = 2`, `potential = 11 / 3`). -/
noncomputable abbrev potentialGapShared : ∀ i, potentialGapNetwork.Path i :=
  broadcastSharedPath 2 fun _ => 6 / 5

/-- All three players use private bypasses `direct i` (`socialCost = 18 / 5`, `potential = 18 / 5`).
-/
noncomputable abbrev potentialGapDirect : ∀ i, potentialGapNetwork.Path i :=
  broadcastDirectPath 2 fun _ => 6 / 5

/-- **Potential-minimizer separation witness** ([TardosWexler2007]): in `potentialGapNetwork`,
1. `potentialGapShared` is a pure Nash equilibrium that globally minimizes `socialCost` (`2`),
2. `potentialGapDirect` is a pure Nash equilibrium that globally minimizes `potential` (`18 / 5`),
3. `potential potentialGapDirect < potential potentialGapShared` (`18 / 5 < 11 / 3`) and
   `socialCost potentialGapShared < socialCost potentialGapDirect` (`2 < 18 / 5`),
so **no global minimizer of Rosenthal's potential achieves the optimal pure-Nash social cost**. -/
theorem potentialGapNetwork_best_nash_not_min_potential :
    potentialGapNetwork.toCostGame.IsPureNash potentialGapShared ∧
      (∀ s, potentialGapNetwork.toCostGame.socialCost potentialGapShared ≤
        potentialGapNetwork.toCostGame.socialCost s) ∧
      potentialGapNetwork.toCostGame.IsPureNash potentialGapDirect ∧
      (∀ s, potentialGapNetwork.potential potentialGapDirect ≤
        potentialGapNetwork.potential s) ∧
      potentialGapNetwork.toCostGame.socialCost potentialGapShared <
        potentialGapNetwork.toCostGame.socialCost potentialGapDirect ∧
      potentialGapNetwork.potential potentialGapDirect <
        potentialGapNetwork.potential potentialGapShared := by
  have hcost_shared : ∀ i : Fin 3,
      potentialGapNetwork.toCostGame.cost i potentialGapShared = 2 / 3 := fun i => by
    rw [generalBroadcastNetwork_cost]
    simp [potentialGapShared]
  have hcost_direct : ∀ i : Fin 3,
      potentialGapNetwork.toCostGame.cost i potentialGapDirect = 6 / 5 := fun i => by
    rw [generalBroadcastNetwork_cost]
    simp [potentialGapDirect]
  have hsc_shared : potentialGapNetwork.toCostGame.socialCost potentialGapShared = 2 := by
    rw [CostGame.socialCost, Fin.sum_univ_three, hcost_shared, hcost_shared, hcost_shared]
    norm_num
  have hsc_direct : potentialGapNetwork.toCostGame.socialCost potentialGapDirect = 18 / 5 := by
    rw [CostGame.socialCost, Fin.sum_univ_three, hcost_direct, hcost_direct, hcost_direct]
    norm_num
  have hpot_formula : ∀ s : ∀ i, potentialGapNetwork.Path i,
      potentialGapNetwork.potential s =
        2 * harmonic (Finset.univ.filter fun j : Fin 3 =>
            broadcastIsDirect (s j) = false).card +
          (6 / 5 : ℝ) * (Finset.univ.filter fun j : Fin 3 =>
            broadcastIsDirect (s j) = true).card := by
    intro s
    rw [FairConnectionGame.potential_eq]
    have hsum : (∑ e : BroadcastArc 3,
          potentialGapNetwork.edgeCost e * harmonic (potentialGapNetwork.edgeLoad s e)) =
        (∑ i : Fin 3, 0 * (harmonic (potentialGapNetwork.edgeLoad s (.toHub i)) : ℝ)) +
          (2 * (harmonic (potentialGapNetwork.edgeLoad s .trunk) : ℝ) +
            ∑ i : Fin 3, (6 / 5 : ℝ) * harmonic (potentialGapNetwork.edgeLoad s (.direct i))) := by
      rw [← (broadcastArcEquiv 3).symm.sum_comp]
      simp only [Fintype.sum_sum_type, Fintype.sum_option, broadcastArcEquiv, Equiv.coe_fn_symm_mk]
      rfl
    rw [hsum]
    simp only [zero_mul, Finset.sum_const_zero, zero_add]
    have htrunk : potentialGapNetwork.edgeLoad s .trunk =
        (Finset.univ.filter fun j : Fin 3 => broadcastIsDirect (s j) = false).card :=
      congrArg Finset.card (Finset.filter_congr fun j _ => mem_pathEdges_trunk_iff (s j))
    have hdir (i : Fin 3) : (harmonic (potentialGapNetwork.edgeLoad s (.direct i)) : ℝ) =
        if broadcastIsDirect (s i) = true then 1 else 0 := by
      by_cases hi : broadcastIsDirect (s i) = true
      · have hl : potentialGapNetwork.edgeLoad s (.direct i) = 1 :=
          Finset.card_eq_one.mpr ⟨i, Finset.ext fun j => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
              mem_pathEdges_direct_iff]
            exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hi⟩⟩⟩
        rw [hl, harmonic_succ, harmonic_zero]
        simp [hi]
      · have hl : potentialGapNetwork.edgeLoad s (.direct i) = 0 :=
          Finset.card_eq_zero.mpr <| Finset.filter_eq_empty_iff.mpr fun j _ hmem =>
            let ⟨hji, hd⟩ := (mem_pathEdges_direct_iff (s j)).1 hmem
            hi (hji ▸ hd)
        simp [hl, hi, harmonic_zero]
    rw [htrunk, Finset.sum_congr rfl fun i _ => by rw [hdir i], ← Finset.mul_sum]
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hpot_direct : potentialGapNetwork.potential potentialGapDirect = 18 / 5 := by
    rw [hpot_formula,
      Finset.filter_true_of_mem fun j _ => broadcastIsDirect_direct (trunkCost := 2)
        (directCost := fun _ => 6 / 5) j]
    simp only [potentialGapDirect, broadcastIsDirect_direct, Bool.true_eq_false,
      Finset.filter_false, Finset.card_empty, harmonic_zero, Rat.cast_zero, mul_zero, zero_add,
      Finset.card_univ, Fintype.card_fin]
    norm_num
  have hpot_shared : potentialGapNetwork.potential potentialGapShared = 11 / 3 := by
    rw [hpot_formula,
      Finset.filter_true_of_mem fun j _ => broadcastIsDirect_shared (trunkCost := 2)
        (directCost := fun _ => 6 / 5) j]
    simp only [potentialGapShared, broadcastIsDirect_shared, Finset.card_univ, Fintype.card_fin,
      Bool.false_eq_true, Finset.filter_false, Finset.card_empty, Nat.cast_zero, mul_zero,
      add_zero, harmonic_succ, harmonic_zero]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, by linarith, by linarith⟩
  · intro i a
    rw [hcost_shared i, generalBroadcastNetwork_cost]
    rcases generalBroadcastNetwork_path_eq_or a with rfl | rfl
    · rw [Function.update_self, broadcastIsDirect_direct]
      norm_num
    · rw [Function.update_eq_self i potentialGapShared]
      simp [potentialGapShared]
  · intro s
    rw [hsc_shared]
    by_cases hall : ∀ j : Fin 3, broadcastIsDirect (s j) = true
    · have hs_eq : s = potentialGapDirect := funext fun j => by
        simpa [hall j] using broadcastPath_eq_ite (s j)
      rw [hs_eq, hsc_direct]
      norm_num
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      rw [FairConnectionGame.socialCost_eq_sum_formedEdges]
      have hmem : BroadcastArc.trunk ∈ potentialGapNetwork.formedEdges s :=
        Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j,
          (mem_pathEdges_trunk_iff (s j)).2 (Bool.eq_false_iff.2 hj)⟩
      exact (show (2 : ℝ) = potentialGapNetwork.edgeCost .trunk from rfl).trans_le
        (Finset.single_le_sum (fun e _ => by
          cases e <;> norm_num [potentialGapNetwork, generalBroadcastNetwork,
            generalBroadcastArcCost]) hmem)
  · intro i a
    rw [hcost_direct i, generalBroadcastNetwork_cost]
    rcases generalBroadcastNetwork_path_eq_or a with rfl | rfl
    · rw [Function.update_eq_self i potentialGapDirect]
      simp [potentialGapDirect]
    · rw [Function.update_self, broadcastIsDirect_shared,
        Finset.card_eq_one.mpr ⟨i, Finset.ext fun j => by
          by_cases h : j = i <;> simp [h, potentialGapDirect]⟩]
      norm_num
  · intro s
    rw [hpot_direct, hpot_formula]
    set m := (Finset.univ.filter fun j : Fin 3 => broadcastIsDirect (s j) = false).card
    have hcomp : (Finset.univ.filter fun j : Fin 3 => broadcastIsDirect (s j) = true).card =
        3 - m := by
      have hadd := Finset.card_filter_add_card_filter_not
        (fun j : Fin 3 => broadcastIsDirect (s j) = false) (s := Finset.univ)
      simp only [Bool.not_eq_false, Finset.card_univ, Fintype.card_fin] at hadd
      omega
    have hm_le : m ≤ 3 := (Finset.card_filter_le _ _).trans_eq (by simp)
    rw [hcomp]
    rcases m with _ | _ | _ | _ | m
    · simp only [harmonic_zero, Rat.cast_zero, mul_zero, zero_add, Nat.sub_zero, Nat.cast_ofNat]
      norm_num
    · rw [harmonic_succ, harmonic_zero]; norm_num
    · rw [harmonic_succ, harmonic_succ, harmonic_zero]; norm_num
    · rw [harmonic_succ, harmonic_succ, harmonic_succ, harmonic_zero]; norm_num
    · omega

end Cslib.GameTheory
