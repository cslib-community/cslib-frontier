/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenMembershipTally
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.SourceRoundLoop

/-!
# Retained context for a Justesen source scan

The source loop retains the initialized weighted adjacency context and the two query endpoints.
On stabilization, the membership entry takes the current radius and tally from the loop
registers. The dimension comes from the retained subdivision, so the entry uses the same
carrier as the adjacency callback.

## Main definitions

* `Cslib.Complexity.STCON.JustesenSourceContext`: the data retained across source rounds.
* `Cslib.Complexity.STCON.justesenSourceMembershipStart`: the final membership entry.

## Main results

* `Cslib.Complexity.STCON.justesenSourceMembershipStart_inSpace`: construct the final
  membership entry in linear workspace in the encoded loop registers.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Reachability.Hoza
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open _root_.Turing.DoubleCounting _root_.Turing.QueryMachine.Subdivision

/-- The data retained across all rounds for one source query. -/
structure JustesenSourceContext where
  /-- The initialized subdivision context shared by adjacency and membership calls. -/
  adjacency : JustesenSubdivisionContext
  /-- The subdivision ID of the current source. -/
  sourceID : ℕ
  /-- The subdivision ID of the designated membership target. -/
  targetID : ℕ

/-- Frame the adjacency context and the two binary endpoint IDs. -/
enc_structure encJustesenSourceContext : JustesenSourceContext where
  adjacency : encJustesenSubdivisionContext, sourceID : encNat, targetID : encNat

/-- Number of vertices in the retained subdivision. -/
@[expose] def JustesenSourceContext.size (ctx : JustesenSourceContext) : ℕ :=
  ctx.adjacency.parameters.search.subdivision.vertexCount

/-- Read the subdivision size from the existing adjacency context encoding. -/
theorem encJustesenSourceContext_size_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {ctx : α → JustesenSourceContext}
    (hctx : ComputableInSpace ctx enc encJustesenSourceContext S) :
    ComputableInSpace (fun a => (ctx a).size) enc encNat S :=
  encSubdivisionSize_vertexCount_budget
    (encJustesenSubdivisionContext_subdivision_budget
      (encJustesenSourceContext_adjacency_budget hctx))

/-- Enter final membership at the loop's current radius and verified tally. -/
@[expose] def justesenSourceMembershipStart (r : SourceRoundLoop.Registers JustesenSourceContext) :
    MembershipTally.RetainedState JustesenSubdivisionContext JustesenSubdivisionState :=
  MembershipTally.retainedInitial r.context.adjacency
    ⟨r.context.size, r.context.sourceID, r.context.targetID, r.radius, r.tally⟩

/-- Final membership entry uses linear workspace in the encoded source-loop registers. -/
theorem justesenSourceMembershipStart_inSpace :
    let E := SourceRoundLoop.encRegisters encJustesenSourceContext
    ComputableInSpace justesenSourceMembershipStart E
      (MembershipTally.encRetainedState encJustesenSubdivisionContext encJustesenSubdivisionState)
      (fun r => (E r).length) := by
  intro E
  have hr := budget_id (enc := E) (.refl _)
  have hctx := SourceRoundLoop.encRegisters_context_budget encJustesenSourceContext hr
  have hparams := MembershipTally.encContext_mk_budget
    (encJustesenSourceContext_size_budget hctx)
    (encJustesenSourceContext_sourceID_budget hctx) (encJustesenSourceContext_targetID_budget hctx)
    (SourceRoundLoop.encRegisters_radius_budget encJustesenSourceContext hr)
    (SourceRoundLoop.encRegisters_tally_budget encJustesenSourceContext hr)
  exact MembershipTally.retainedInitial_budget encJustesenSubdivisionContext
    encJustesenSubdivisionState (encJustesenSourceContext_adjacency_budget hctx) hparams

end Cslib.Complexity.STCON
