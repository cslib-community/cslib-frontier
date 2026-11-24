/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.NetworkFormation.Witnesses
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checked tests for NRTV Ch. 19 fair connection games

Kernel-checked examples (using ordinary `module` imports and zero `native_decide`) exercising
`CslibFrontier.GameTheory.NetworkFormation.FairConnection` and
`CslibFrontier.GameTheory.NetworkFormation.Witnesses`:

1. **Multi-commodity bow-tie network** (`source 0 ≠ source 1` and `sink 0 ≠ sink 1`) on `Fin 6`
   with a shared bridge `2 → 3` (cost `2`), feeder arcs `0 → 2`, `1 → 2`, `3 → 4`, `3 → 5`
   (cost `1 / 2` each), private bypasses `0 → 4`, `1 → 5` (cost `5 / 2` each), and an unused cross
   arc `4 → 5` (cost `1`):
   * exact Rosenthal potential step `Φ(update) - Φ(s) = cost_i(update) - cost_i(s) = 1 / 2`,
   * `socialCost = 4 < 5 = Φ` on the bridge-sharing pure Nash equilibrium,
   * centralized `IsSteinerSubgraph` comparison on a non-minimal Steiner subgraph containing the
     unused arc `4 → 5`,
   * Anshelevich et al. `H_2 = 3 / 2` Steiner-subgraph bound and `PoA ≤ 2` bound.
2. **Disconnected-terminal boundary**: a 2-vertex `FairConnectionGame` with a reverse arc `1 → 0`
   fails `TerminalsConnected` for terminal pair `(0, 1)` and has an empty path strategy space.
3. **Four-player directed vs. undirected `H_4 = 25 / 12` broadcast network (`ε = 1 / 20` and `0`)**:
   * in the directed network at `ε = 1 / 20`, the unique pure Nash equilibrium costs `25 / 12`
     against shared cost `21 / 20` (`PoS = 125 / 63 > 19 / 10 > H_3`), while at `ε = 0` both the
     cost-`1` shared profile and cost-`25 / 12` direct profile are pure Nash equilibria;
   * in the undirected network at `ε = 1 / 20`, `undirectedViaLastProfile` is a pure Nash
     equilibrium of globally minimal social cost `1 / 4` (`PoS = 1`, each player paying `1 / 16`).
4. **Four-player parallel-link `PoA = 4` network**: exact `socialCost = 4 = 4 * OPT` at `ε = 0`,
   strict pure Nash equilibrium at `ε = 1 / 10`, and matching general `PoA ≤ 4` upper bound.
5. **Three-player `potentialGapNetwork` ([TardosWexler2007])**: socially optimal pure Nash
   equilibrium (`socialCost = 2`, `Φ = 11 / 3`) strictly exceeds the global minimum of Rosenthal's
   potential (`Φ = 18 / 5` at the cost-`18 / 5` direct pure Nash equilibrium).
-/

public section

namespace CslibFrontierTests.NetworkFormationNRTV

open Cslib.GameTheory Cslib.Multidigraph

/-! ### 1. Multi-commodity bow-tie network with distinct sources and sinks -/

/-- Arcs of the 6-vertex multi-commodity bow-tie network (`0 → 4` for player `0`, `1 → 5` for
player `1`). -/
inductive BowTieArc where
  | in0
  | in1
  | bridge
  | out0
  | out1
  | bypass0
  | bypass1
  | extraChord
  deriving DecidableEq

instance : Fintype BowTieArc where
  elems := {.in0, .in1, .bridge, .out0, .out1, .bypass0, .bypass1, .extraChord}
  complete e := by cases e <;> decide

def BowTieArc.src : BowTieArc → Fin 6
  | .in0 => 0
  | .in1 => 1
  | .bridge => 2
  | .out0 => 3
  | .out1 => 3
  | .bypass0 => 0
  | .bypass1 => 1
  | .extraChord => 4

def BowTieArc.tgt : BowTieArc → Fin 6
  | .in0 => 2
  | .in1 => 2
  | .bridge => 3
  | .out0 => 4
  | .out1 => 5
  | .bypass0 => 4
  | .bypass1 => 5
  | .extraChord => 5

noncomputable def bowTieCost : BowTieArc → ℝ
  | .in0 | .in1 | .out0 | .out1 => 1 / 2
  | .bridge => 2
  | .bypass0 | .bypass1 => 5 / 2
  | .extraChord => 1

/-- Multi-commodity 2-player `FairConnectionGame`: player `0` connects `0 → 4` and player `1`
connects `1 → 5`. -/
noncomputable def bowTieGame : FairConnectionGame (Fin 2) (Fin 6) BowTieArc where
  src := BowTieArc.src
  tgt := BowTieArc.tgt
  edgeCost := bowTieCost
  source i := if i = 0 then 0 else 1
  sink i := if i = 0 then 4 else 5

theorem bowTieGame_source_ne : bowTieGame.source 0 ≠ bowTieGame.source 1 := by decide
theorem bowTieGame_sink_ne : bowTieGame.sink 0 ≠ bowTieGame.sink 1 := by decide

theorem bowTieCost_nonneg : ∀ e, 0 ≤ bowTieGame.edgeCost e := by
  intro e
  cases e <;> norm_num [bowTieGame, bowTieCost]

/-- Bridge-sharing profile: player `0` takes `0 → 2 → 3 → 4` and player `1` takes `1 → 2 → 3 → 5`.
-/
def bowTieBridgeProfile : ∀ i, bowTieGame.Path i
  | 0 => ⟨[.in0, .bridge, .out0], by decide⟩
  | 1 => ⟨[.in1, .bridge, .out1], by decide⟩

/-- Private bypass profile: player `0` takes `0 → 4` and player `1` takes `1 → 5`. -/
def bowTieBypassProfile : ∀ i, bowTieGame.Path i
  | 0 => ⟨[.bypass0], by decide⟩
  | 1 => ⟨[.bypass1], by decide⟩

/-- Bridge-sharing social cost is `4` (`4 * (1/2) + 2`), while bypass social cost is `5`. -/
example : bowTieGame.toCostGame.socialCost bowTieBridgeProfile = 4 ∧
    bowTieGame.toCostGame.socialCost bowTieBypassProfile = 5 := by
  rw [bowTieGame.socialCost_eq_sum_formedEdges, bowTieGame.socialCost_eq_sum_formedEdges]
  have hf1 : bowTieGame.formedEdges bowTieBridgeProfile = {.in0, .in1, .bridge, .out0, .out1} := by
    decide
  have hf2 : bowTieGame.formedEdges bowTieBypassProfile = {.bypass0, .bypass1} := by decide
  rw [hf1, hf2]
  norm_num [bowTieGame, bowTieCost]

/-- Exact Rosenthal potential step on a unilateral deviation from `bowTieBypassProfile`: when
player `0` switches alone from `[bypass0]` (cost `5 / 2`) to `[in0, bridge, out0]` (standalone cost
`1/2 + 2 + 1/2 = 3`), both player `0`'s cost and `bowTieGame.potential` increase by `1 / 2`. -/
example :
    let s' := Function.update bowTieBypassProfile 0 (bowTieBridgeProfile 0)
    bowTieGame.toCostGame.cost 0 s' - bowTieGame.toCostGame.cost 0 bowTieBypassProfile = 1 / 2 ∧
      bowTieGame.potential s' - bowTieGame.potential bowTieBypassProfile = 1 / 2 := by
  intro s'
  have hpot := bowTieGame.isExactPotential_potential bowTieBypassProfile 0 (bowTieBridgeProfile 0)
  have hc0 : bowTieGame.toCostGame.cost 0 bowTieBypassProfile = 5 / 2 := by
    rw [bowTieGame.toCostGame_cost]
    have he : bowTieGame.pathEdges (bowTieBypassProfile 0) = {.bypass0} := by decide
    have hl : bowTieGame.edgeLoad bowTieBypassProfile .bypass0 = 1 := by decide
    rw [he, Finset.sum_singleton, hl]
    norm_num [bowTieGame, bowTieCost]
  have hc1 : bowTieGame.toCostGame.cost 0 s' = 3 := by
    rw [bowTieGame.toCostGame_cost]
    have he : bowTieGame.pathEdges (s' 0) = {.in0, .bridge, .out0} := by decide
    have hl1 : bowTieGame.edgeLoad s' .in0 = 1 := by decide
    have hl2 : bowTieGame.edgeLoad s' .bridge = 1 := by decide
    have hl3 : bowTieGame.edgeLoad s' .out0 = 1 := by decide
    rw [he]
    simp only [Finset.sum_insert (by decide : BowTieArc.in0 ∉ ({.bridge, .out0} : Finset _)),
      Finset.sum_pair (by decide : BowTieArc.bridge ≠ .out0), hl1, hl2, hl3]
    norm_num [bowTieGame, bowTieCost]
  constructor
  · linarith
  · linarith

/-- Non-minimal centralized Steiner subgraph including the unused chord `extraChord` (`4 → 5`,
cost `1`) has edge-set cost `5`, while Anshelevich et al.'s Steiner bound guarantees a pure Nash
equilibrium of cost at most `H_2 * 4 = 6` (and at most `H_2 * 5 = 15 / 2` against the redundant
subgraph). -/
example :
    let F_redundant : Finset BowTieArc := {.in0, .in1, .bridge, .out0, .out1, .extraChord}
    bowTieGame.IsSteinerSubgraph F_redundant ∧
      ∑ e ∈ F_redundant, bowTieGame.edgeCost e = 5 ∧
      ∃ s, bowTieGame.toCostGame.IsPureNash s ∧
        bowTieGame.toCostGame.socialCost s ≤ 6 := by
  intro F_redundant
  have hF_min : bowTieGame.IsSteinerSubgraph (bowTieGame.formedEdges bowTieBridgeProfile) :=
    bowTieGame.isSteinerSubgraph_formedEdges bowTieBridgeProfile
  have hF_red : bowTieGame.IsSteinerSubgraph F_redundant := fun i => by
    obtain ⟨q, hq, hsub⟩ := hF_min i
    refine ⟨q, hq, fun e he => ?_⟩
    have hmem := hsub e he
    have hf : bowTieGame.formedEdges bowTieBridgeProfile ⊆ F_redundant := by decide
    exact hf hmem
  have hcost_red : ∑ e ∈ F_redundant, bowTieGame.edgeCost e = 5 := by
    norm_num [F_redundant, bowTieGame, bowTieCost]
  obtain ⟨s, hs, hle⟩ := bowTieGame.exists_isPureNash_socialCost_le_harmonic_mul_steinerCost
    hF_min.terminalsConnected bowTieCost_nonneg
  have hmin_cost : ∑ e ∈ bowTieGame.formedEdges bowTieBridgeProfile, bowTieGame.edgeCost e = 4 := by
    have hf : bowTieGame.formedEdges bowTieBridgeProfile = {.in0, .in1, .bridge, .out0, .out1} := by
      decide
    rw [hf]
    norm_num [bowTieGame, bowTieCost]
  have hH2 : ((harmonic (Fintype.card (Fin 2)) : ℚ) : ℝ) = 3 / 2 := by
    rw [Fintype.card_fin, harmonic_succ, harmonic_succ, harmonic_zero]
    norm_num
  refine ⟨hF_red, hcost_red, s, hs, ?_⟩
  have hbound := hle _ hF_min
  rw [hH2, hmin_cost] at hbound
  linarith

/-! ### 2. Boundary check: disconnected terminals have empty strategy space -/

/-- Single reverse arc `true → false` leaves terminal pair `(false, true)` disconnected. -/
def reverseArcGame : FairConnectionGame Unit Bool Unit where
  src _ := true
  tgt _ := false
  edgeCost _ := 1
  source _ := false
  sink _ := true

example : ¬ reverseArcGame.TerminalsConnected ∧ IsEmpty (reverseArcGame.Path ()) := by
  refine ⟨fun h => ?_, ⟨fun ⟨q, hq⟩ => ?_⟩⟩
  · obtain ⟨q, hq⟩ := h ()
    rcases q with _ | ⟨⟨⟩, _⟩
    · exact Bool.false_ne_true (hq.2.2.2.1 rfl)
    · exact Bool.noConfusion (hq.2.2.1 () rfl)
  · rcases q with _ | ⟨⟨⟩, _⟩
    · exact Bool.false_ne_true (hq.2.2.2.1 rfl)
    · exact Bool.noConfusion (hq.2.2.1 () rfl)

/-! ### 3. Directed vs. undirected 4-player `H_4 = 25 / 12` broadcast network -/

theorem harmonic_four : ((harmonic 4 : ℚ) : ℝ) = 25 / 12 := by
  rw [harmonic_succ, harmonic_succ, harmonic_succ, harmonic_succ, harmonic_zero]
  norm_num

/-- In the 4-player directed `broadcastNetwork 4 (1 / 20)`, every pure Nash equilibrium costs
`25 / 12`, strictly more than `19 / 10` times the shared-trunk cost `21 / 20` (`125 / 63 > 1.9`). -/
example :
    (∀ s, (broadcastNetwork 4 (1 / 20)).toCostGame.IsPureNash s ↔
      s = broadcastDirectProfile 4 (1 / 20)) ∧
    (broadcastNetwork 4 (1 / 20)).toCostGame.socialCost (broadcastDirectProfile 4 (1 / 20)) =
      25 / 12 ∧
    19 / 10 *
        (broadcastNetwork 4 (1 / 20)).toCostGame.socialCost (broadcastSharedProfile 4 (1 / 20)) <
      (broadcastNetwork 4 (1 / 20)).toCostGame.socialCost (broadcastDirectProfile 4 (1 / 20)) := by
  refine ⟨isPureNash_broadcastNetwork_iff (by norm_num), ?_, ?_⟩
  · rw [socialCost_broadcastDirectProfile, harmonic_four]
  · rw [socialCost_broadcastSharedProfile (by decide), socialCost_broadcastDirectProfile,
      harmonic_four]
    norm_num

/-- At `ε = 0`, both the cost-`1` shared profile and the cost-`25 / 12` direct profile are pure
Nash equilibria of `broadcastNetwork 4 0`. -/
example :
    (broadcastNetwork 4 0).toCostGame.IsPureNash (broadcastSharedProfile 4 0) ∧
    (broadcastNetwork 4 0).toCostGame.IsPureNash (broadcastDirectProfile 4 0) ∧
    (broadcastNetwork 4 0).toCostGame.socialCost (broadcastSharedProfile 4 0) = 1 ∧
    (broadcastNetwork 4 0).toCostGame.socialCost (broadcastDirectProfile 4 0) = 25 / 12 :=
  ⟨isPureNash_broadcastShared_zero 4, isPureNash_broadcastDirect_zero 4,
    by rw [socialCost_broadcastSharedProfile (by decide)]; norm_num,
    by rw [socialCost_broadcastDirectProfile, harmonic_four]⟩

/-- In the undirected 4-player `undirectedBroadcastNetwork 4 (1 / 20)` with the exact same
parameters, `undirectedViaLastProfile` is a pure Nash equilibrium of globally optimal social cost
`1 / 4`, with every player paying `1 / 16`. -/
example :
    let s := undirectedViaLastProfile (show 0 < 4 by decide) (1 / 20)
    (undirectedBroadcastNetwork 4 (1 / 20)).toCostGame.IsPureNash s ∧
    (undirectedBroadcastNetwork 4 (1 / 20)).toCostGame.socialCost s = 1 / 4 ∧
    (∀ i, (undirectedBroadcastNetwork 4 (1 / 20)).toCostGame.cost i s = 1 / 16) ∧
    ∀ s', (undirectedBroadcastNetwork 4 (1 / 20)).toCostGame.socialCost s ≤
      (undirectedBroadcastNetwork 4 (1 / 20)).toCostGame.socialCost s' := by
  intro s
  refine ⟨isPureNash_undirectedViaLastProfile (by decide) (by norm_num),
    by rw [socialCost_undirectedViaLastProfile]; norm_num,
    fun i => by rw [cost_undirectedViaLastProfile]; norm_num,
    socialCost_undirectedViaLastProfile_le (by decide) (by norm_num)⟩

/-! ### 4. Four-player parallel-link `PoA = 4` network and matching upper bound -/

example :
    (parallelNetwork 4 0).toCostGame.IsPureNash (parallelExpensiveProfile 4 0) ∧
    (parallelNetwork 4 0).toCostGame.socialCost (parallelExpensiveProfile 4 0) = 4 ∧
    (parallelNetwork 4 0).toCostGame.socialCost (parallelCheapProfile 4 0) = 1 ∧
    ∀ s, (parallelNetwork 4 0).toCostGame.IsPureNash s →
      (parallelNetwork 4 0).toCostGame.socialCost s ≤
        4 * (parallelNetwork 4 0).toCostGame.socialCost (parallelCheapProfile 4 0) := by
  obtain ⟨hnash, _, _⟩ := socialCost_parallelExpensive_eq_mul_cheap (k := 4) (by decide)
  refine ⟨hnash, ?_, ?_, fun s hs => ?_⟩
  · rw [socialCost_parallelExpensiveProfile (by decide)]; norm_num
  · rw [socialCost_parallelCheapProfile (by decide)]; norm_num
  · have h := (parallelNetwork 4 0).socialCost_le_card_mul_of_isPureNash
      (parallelNetwork_edgeCost_nonneg le_rfl) hs (parallelCheapProfile 4 0)
    simpa [Fintype.card_fin] using h

/-! ### 5. Socially optimal pure NE vs. potential minimizer (`potentialGapNetwork`) -/

example :
    potentialGapNetwork.toCostGame.IsPureNash potentialGapShared ∧
    potentialGapNetwork.toCostGame.IsPureNash potentialGapDirect ∧
    potentialGapNetwork.toCostGame.socialCost potentialGapShared <
      potentialGapNetwork.toCostGame.socialCost potentialGapDirect ∧
    potentialGapNetwork.potential potentialGapDirect <
      potentialGapNetwork.potential potentialGapShared ∧
    ∀ s, potentialGapNetwork.potential potentialGapDirect ≤ potentialGapNetwork.potential s := by
  obtain ⟨hns, _, hnd, hpot_min, hsc_lt, hpot_lt⟩ :=
    potentialGapNetwork_best_nash_not_min_potential
  exact ⟨hns, hnd, hsc_lt, hpot_lt, hpot_min⟩

end CslibFrontierTests.NetworkFormationNRTV
