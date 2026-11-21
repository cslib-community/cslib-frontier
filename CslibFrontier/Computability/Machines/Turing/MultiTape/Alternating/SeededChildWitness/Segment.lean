/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Segment
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TailCallGround
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness.Dispatch

/-!
# The actual witness prefix of a descendant endpoint segment

The controller's recursive branch plays all nine existential fields, the universal selector and
the selected bit index, on the physical work tape. At the right end its terminal sees the exact
chosen word. Establishing its one dispatched local, parent or count-bit task at that configuration
suffices for the enclosing finite controller's segment to verify the real child endpoints.
-/

public section

namespace Turing.MultiTapeATM.SeededChildCounts

open Cslib BalancedSchedules Circuits.Frontier.NativeChild EndpointQuery
open SeededChildWitness Dispatch QuantifiedWord
open WordGameLeaf (config)

/-- Only states of the routed terminal may recur. The existential and universal choices all
complete before any such handover. -/
def terminalMark {S : Type} (mark : S → Bool) : QuantifiedWord.State S → Bool
  | .leaf s => mark s
  | _ => false

/-- One nonempty endpoint segment from its physical dispatch. The flag tape contains the
prepared choices at its origin. A second work symbol selects recursion over the existing ground
branch. Each terminal receives the completed word exactly once on its branch. -/
theorem child_segment {k : ℕ} {S G : Type} (tape flag : Fin k) (leaf : MultiTapeATM k Bool S)
    (ground : MultiTapeATM k Bool G) (mark : S → Bool)
    {input : List Bool} (storage : Cfg k Bool Unit input)
    (ready meaning : Cfg k Bool (TailCallGround.State (QuantifiedWord.State S) G) input → Prop)
    {U a : ℕ} (seed : SeededLabels.Seed U (6 * a)) (i : Fin a) (group : ℕ)
    {q : EndpointQuery} {es} (hq : q.Represents es)
    (hkeys : ∀ e p, q.accepts e p → p.1 < U ∧ p.2 < U) (j : ℕ) (answer : ℕ × ℕ) (t : ℕ) :
    let l := Labels.ofSeed U a seed i group
    let b : Public := ⟨q.size, U, j⟩
    let localTest (p : Proposal) := SeededChildWitness.run
      ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, p.edge, 0⟩, i.val, group, j,
        p.ends, answer, p.counts⟩ = true
    let flags := witnessFlags (width b)
    let node := QuantifiedWord.machine leaf tape
    let host := TailCallGround.body flag node ground
    let again := TailCallGround.again (G := G) (terminalMark mark)
    let start := config tape (none : Option Unit) flags 0 storage
    start.workTapeSymbols flag ≠ some true →
    (∀ xs : List Bool, xs.length = flags.length →
      TailCall.Segment host again ready meaning t (config tape
        (some (.node (.leaf leaf.toPTM.initial))) xs xs.length storage)
        (routedValue q l b localTest xs)) →
    TailCall.Segment host again ready meaning (t + 2 * flags.length + 1 + 1)
      (start.withState (some .entry)) ((q.child (l.split q)).accepts j answer) := by
  intro l b localTest flags node host again start hf hr
  let sim := TailCallGround.nodeSimulation flag node ground
  have hm (s : QuantifiedWord.State S) : sim.stateMap s = .node s := by
    simp [sim]
  have hg := QuantifiedWord.segment leaf tape sim again ready meaning t storage
    (routedValue q l b localTest) [] flags
    (by rw [hm]; rfl) (fun p => by rw [hm]; rfl)
    (fun xs hx => by
      simpa only [List.nil_append, TailCallGround.nodeSimulation_stateMap, sim,
        Cfg.mapState, config, Option.map_some, host] using hr xs hx)
  apply TailCallGround.node_segment flag node ground (terminalMark mark) start hf
  have hh := hg.iff (child_iff_plays_dispatch seed i group hq hkeys j answer).symm
  simpa only [start, node, again, List.nil_append, List.length_nil, Cfg.mapState, config,
    sim, TailCallGround.nodeSimulation_stateMap, Option.map_some, Cfg.withState, machine_initial]
    using hh

end Turing.MultiTapeATM.SeededChildCounts
