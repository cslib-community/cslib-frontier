/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceContext
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Dispatch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.DeterministicCall
import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenWeightedSubdivision.Replay

/-!
# Tagged callback for a Justesen source round

A source round requests either adjacency between two vertices or membership of one candidate.
The request selects the entry tag. Both alternatives use the supplied initialized subdivision
context and read the original input.

## Main definitions

* `Cslib.Complexity.STCON.justesenRoundCallback`: dispatch to the edge or membership machine.
* `Cslib.Complexity.STCON.justesenRoundCallbackStart`: initialize the requested alternative.
* `Cslib.Complexity.STCON.justesenRoundCallbackReply`: decode the optional Boolean reply.

## Main results

* `Cslib.Complexity.STCON.justesenRoundCallback_readReply`: the selected callback consumes
  exactly its own selectors, preserves its verdict, and returns the same suffix.
* `Cslib.Complexity.STCON.configurationJustesenRoundCallback_existsUnique_firstHalting`:
  each request at exact tally totals has one first-halting trace returning a Boolean
  if the membership transcript is unique.
* `Cslib.Complexity.STCON.configurationJustesenRoundCallback_readReply_correct`:
  at exact totals, parsed edge and membership replies agree with adjacency and reachability.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.DoubleCounting _root_.Turing.QueryMachine.Subdivision
open _root_.Turing.NondeterministicQueryMachine

variable {k : ℕ} {State : Type} [Fintype State]

/-- The tagged callback state keeps rejection distinct from either Boolean verdict. -/
abbrev JustesenRoundCallbackState :=
  Option JustesenSubdivisionState ⊕
    MembershipTally.RetainedState JustesenSubdivisionContext JustesenSubdivisionState

/-- Run the requested adjacency or membership callback on the original input. -/
@[expose] noncomputable def justesenRoundCallback (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    NondeterministicQueryMachine JustesenRoundCallbackState :=
  (justesenWeightedSubdivisionCallback ntm).withRejectingChoice.dispatch
    (justesenSourceMembershipMachine ntm c)

/-- The round request determines the callback tag and the queried vertex IDs. -/
@[expose] def justesenRoundCallbackStart (adjacency : JustesenSubdivisionContext)
    (ctx : SourceRound.Context) : SourceRound.Request → JustesenRoundCallbackState
  | .edge u v => .inl (some (justesenSubdivisionEdgeStart (adjacency, u, v)))
  | .member v => .inr (justesenRoundMembershipStart adjacency ctx v)

/-- Read the optional Boolean reply from the selected callback. -/
@[expose] def justesenRoundCallbackReply : JustesenRoundCallbackState → Option Bool :=
  Sum.elim (Option.map callbackVerdict) MembershipTally.retainedReply

/-- A request's tagged reply parser agrees with the corresponding direct parser. -/
theorem justesenRoundCallback_readReply
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (adjacency : JustesenSubdivisionContext)
    (ctx : SourceRound.Context) (request : SourceRound.Request) (input bits : List Bool) :
    (justesenRoundCallback ntm c).readReply justesenRoundCallbackReply input
      (justesenRoundCallbackStart adjacency ctx request) bits =
      match request with
      | .edge u v => (justesenWeightedSubdivisionCallback ntm).withRejectingChoice.readReply
          (Option.map callbackVerdict) input
          (some (justesenSubdivisionEdgeStart (adjacency, u, v))) bits
      | .member v => (justesenSourceMembershipMachine ntm c).readReply
          MembershipTally.retainedReply input
          (justesenRoundMembershipStart adjacency ctx v) bits := by
  cases request <;> apply Option.ext <;> rintro ⟨hit, suffix⟩ <;>
    simp only [justesenRoundCallbackStart, justesenRoundCallback, readReply_iff,
      firstHalting_dispatch_inl, firstHalting_dispatch_inr, replay_dispatch,
      Sum.map_inl, Sum.map_inr, justesenRoundCallbackReply, Sum.elim_inl, Sum.elim_inr]

open Cslib.Code.JustesenFamily Cslib.DoubleCounting

/-- At exact round totals, each in-range request has one first-halting selector list returning
a Boolean, provided the membership transcript is unique at that radius. -/
theorem configurationJustesenRoundCallback_existsUnique_firstHalting
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source : Fin n) (radius : ℕ),
      let adjacent := configurationJustesenSubdivisionAdjacent ntm c w seed
      let edge := fun u v => adjacent u v = true
      (∃! transcript, Passes edge source radius transcript) →
      let adjacency := configurationJustesenSubdivisionContext ntm c w seed.val
      let ctx : SourceRound.Context := ⟨n, source.val, radius, expected edge source radius⟩
      let M := justesenRoundCallback ntm c
      ∀ req : SourceRound.Request, req.InRange n →
        let entry := justesenRoundCallbackStart adjacency ctx req
        ∃! bits, M.FirstHalting w bits entry ∧
          (justesenRoundCallbackReply (M.replay w bits entry)).isSome := by
  intro I n seed source radius adjacent edge hpass adjacency ctx M req hr entry
  cases req with
  | edge u v =>
    obtain ⟨hu, hv⟩ := hr
    simp only [M, entry, justesenRoundCallback, justesenRoundCallbackStart,
      firstHalting_dispatch_inl, replay_dispatch, Sum.map_inl, justesenRoundCallbackReply,
      Sum.elim_inl, Option.isSome_map]
    have hspec := configurationJustesenSubdivisionEdge_firstHalting_iff ntm c w
      seed ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨[false, false, false], (hspec _).mpr rfl, fun bits h => (hspec bits).mp h⟩
  | member v =>
    simp only [M, entry, justesenRoundCallback, justesenRoundCallbackStart,
      firstHalting_dispatch_inr, replay_dispatch, Sum.map_inr, justesenRoundCallbackReply,
      Sum.elim_inr]
    let entered := (justesenSourceMembershipMachine ntm c).withInit
      (justesenRoundMembershipStart adjacency ctx v)
    change ∃! bits, entered.FirstHalting w bits entered.init ∧
      (MembershipTally.retainedReply (entered.run w bits)).isSome
    dsimp only [entered, adjacency]
    rw [justesenRoundMembershipMachine_withInit]
    exact configurationJustesenMembershipTally_existsUnique_firstHalting ntm c w
      seed source ⟨v, hr⟩ radius hpass

/-- A successful tagged reply agrees with subdivision adjacency or bounded reachability,
according to the request. The membership call uses the exact round totals. -/
theorem configurationJustesenRoundCallback_readReply_correct
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (source : Fin n) (radius : ℕ),
      let adjacent := configurationJustesenSubdivisionAdjacent ntm c w seed
      let edge := fun u v => adjacent u v = true
      let adjacency := configurationJustesenSubdivisionContext ntm c w seed.val
      let ctx : SourceRound.Context := ⟨n, source.val, radius, expected edge source radius⟩
      ∀ (req : SourceRound.Request) (hr : req.InRange n) (bits : List Bool)
        (hit : Bool) (suffix : List Bool),
        (justesenRoundCallback ntm c).readReply justesenRoundCallbackReply w
          (justesenRoundCallbackStart adjacency ctx req) bits = some (hit, suffix) →
        match req, hr with
        | .edge u v, ⟨hu, hv⟩ => hit = adjacent ⟨u, hu⟩ ⟨v, hv⟩
        | .member v, hv =>
          hit ↔ (⟨v, hv⟩ : Fin n) ∈ Relation.reachableWithin edge source radius := by
  intro I n seed source radius adjacent edge adjacency ctx req hr bits hit suffix hreply
  rw [justesenRoundCallback_readReply] at hreply
  cases req with
  | edge u v =>
    rcases hr with ⟨hu, hv⟩
    have h := (configurationJustesenSubdivisionEdge_readReply_iff ntm c w
      seed ⟨u, hu⟩ ⟨v, hv⟩ bits suffix hit).mp hreply
    apply Bool.eq_iff_iff.mpr
    simpa only [adjacent, configurationJustesenSubdivisionAdjacent, decide_eq_true_eq] using h.2
  | member v =>
    exact justesenRoundMembership_readReply_correct ntm c w seed source ⟨v, hr⟩
      radius bits hit suffix hreply

end Cslib.Complexity.STCON
