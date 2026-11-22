/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceContext
public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler

/-!
# Source loop entry from a scheduler request

The scheduler provides the initialized subdivision parameters, a binary seed rank, and a
source ID. The source scanner combines those with the prepared field context and retains the
designated target from the setup. This works for both the designated call and each indexed
original-source call.

## Main definitions

* `Cslib.Complexity.STCON.justesenSourceContextOfRequest`: build the retained source context.
* `Cslib.Complexity.STCON.justesenSourceRegistersOfRequest`: initialize the loop at full fuel.

## Main results

* `Cslib.Complexity.STCON.justesenSourceContextOfRequest_budget`: build the context under the
  common budget of the two producers.
* `Cslib.Complexity.STCON.justesenSourceContextOfRequest_adjacency_eq`: the retained adjacency
  agrees with the initializer on the original word.
* `Cslib.Complexity.STCON.justesenSourceRegistersOfRequest_budget`: full-fuel registers
  use the same shared budget.
* `Cslib.Complexity.STCON.justesenSourceRegistersOfRequest_eq`: the scheduler and
  the original-word initializer give the same initial registers.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily
open _root_.Turing _root_.Turing.DoubleCounting
open _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace

/-- Use the requested source, the designated target, and the supplied field context. -/
@[expose] def justesenSourceContextOfRequest (r : SeedScanRequest) (field : FieldContext) :
    JustesenSourceContext :=
  ⟨⟨r.setup.parameters, field, r.seed⟩, r.sourceID, r.setup.targetID⟩

/-- The source context uses the common workspace budget of the request and field producers. -/
theorem justesenSourceContextOfRequest_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {request : α → SeedScanRequest} {field : α → FieldContext}
    (hrequest : ComputableInSpace request enc encSeedScanRequest S)
    (hfield : ComputableInSpace field enc encFieldContext S) :
    ComputableInSpace (fun a => justesenSourceContextOfRequest (request a) (field a))
      enc encJustesenSourceContext S := by
  have hsetup := encSeedScanRequest_setup_budget hrequest
  have hadj := encJustesenSubdivisionContext_mk_budget
    (encSeedSearchSetup_parameters_budget hsetup) hfield (encSeedScanRequest_seed_budget hrequest)
  exact encJustesenSourceContext_mk_budget hadj (encSeedScanRequest_sourceID_budget hrequest)
    (encSeedSearchSetup_targetID_budget hsetup)

/-- A request from the initialized setup uses exactly the original word's adjacency context,
independently of which source was requested. -/
theorem justesenSourceContextOfRequest_adjacency_eq {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) (rank source : ℕ) :
    (justesenSourceContextOfRequest ⟨configurationSeedSearchSetup ntm c w, rank, source⟩
      (configurationFieldContext ntm c w)).adjacency =
        configurationJustesenSubdivisionContext ntm c w rank := by
  simp only [justesenSourceContextOfRequest, configurationJustesenSubdivisionContext,
    (configurationSeedSearchSetup_endpoints ntm c w).1]

/-- Use the prepared request and field to start the loop with one round of fuel per vertex. -/
@[expose] def justesenSourceRegistersOfRequest (request : SeedScanRequest) (field : FieldContext) :
    SourceRoundLoop.Registers JustesenSourceContext :=
  let context := justesenSourceContextOfRequest request field
  SourceRoundLoop.start context context.size

/-- Form full-fuel registers within the shared budget of the request and field producers. -/
theorem justesenSourceRegistersOfRequest_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {request : α → SeedScanRequest} {field : α → FieldContext}
    (hrequest : ComputableInSpace request enc encSeedScanRequest S)
    (hfield : ComputableInSpace field enc encFieldContext S) :
    ComputableInSpace (fun a => justesenSourceRegistersOfRequest (request a) (field a))
      enc (SourceRoundLoop.encRegisters encJustesenSourceContext) S := by
  have hcontext := justesenSourceContextOfRequest_budget hrequest hfield
  exact SourceRoundLoop.start_budget encJustesenSourceContext hcontext
    (encJustesenSourceContext_size_budget hcontext)

/-- At the initialized setup and field, the request gives the original word's full-fuel entry. -/
theorem justesenSourceRegistersOfRequest_eq {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) (rank source : ℕ) :
    let setup := configurationSeedSearchSetup ntm c w
    justesenSourceRegistersOfRequest ⟨setup, rank, source⟩ (configurationFieldContext ntm c w) =
      SourceRoundLoop.start
        ⟨configurationJustesenSubdivisionContext ntm c w rank, source, setup.targetID⟩
        setup.parameters.search.subdivision.vertexCount := by
  intro setup
  have hctx :
      justesenSourceContextOfRequest ⟨setup, rank, source⟩ (configurationFieldContext ntm c w) =
        ⟨configurationJustesenSubdivisionContext ntm c w rank, source, setup.targetID⟩ := by
    have h := justesenSourceContextOfRequest_adjacency_eq ntm c w rank source
    change (⟨(justesenSourceContextOfRequest ⟨setup, rank, source⟩
      (configurationFieldContext ntm c w)).adjacency, source, setup.targetID⟩ :
        JustesenSourceContext) = _
    rw [h]
  rw [justesenSourceRegistersOfRequest, hctx, configurationJustesenSourceContext_size]

end Cslib.Complexity.STCON
