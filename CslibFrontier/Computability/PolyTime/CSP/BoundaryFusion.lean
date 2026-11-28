/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryFusion
import CslibFrontier.Computability.PolyTime.CSP.Boundary
import CslibFrontier.Computability.PolyTime.Graph.RotationSystem.Reindex
import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Tactic.PolyTime
import Mathlib.Logic.Function.Basic

/-!
# Native polynomial time for raw head-wire fusion

The existing `CrossInsertion.fuseHead` is certified on every raw state, with the unchanged
`CrossInsertion.encState` layout: the binary-named body, then the binary boundary word, then
the binary successor table. The first two fields are framed. The relation alphabet is arbitrary.

The residual boundary count is computed in unary from the actual twice-tailed port list.
Body occurrence counts and table-walk clocks also come from actual lists. Binary variable
names, queried corners and malformed successor entries are compared or read with the existing
saturating lookup program; their numerical values never fund a loop. No checker invariant,
distinctness, arity bound or bound on table entries is used.

This is the runtime certificate for one original head-identification operation. Sequential
CROSS transposition and its accumulated iteration bound remain objectives of
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main results

* `CrossInsertion.computableInPolyTime_fuseHead`: native polynomial time on all raw states.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph Turing.MultiTapeTM

variable {Rel : Type}

attribute [local fun_prop] OrderedBoundary.computableInPolyTime_restrictPrefix
  RotationCertificate.computableInPolyTime_swapSuccessors

/-- Fuse the first two boundary wires in native polynomial time on every raw state.
Names and table entries are binary; all counts are computed in unary from actual lists.
The residual boundary length varies with the input, with no acceptance or arity premise. -/
theorem computableInPolyTime_fuseHead (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fuseHead (Rel := Rel)) (encState encRel) (encState encRel) := by
  open scoped State in
  let input := encState encRel
  let update (I : State Rel) := Function.update id (I.ports.tail.headD 0) (I.ports.headD 0)
  have hupdate : ComputableInPolyTime (fun p : State Rel × ℕ => update p.1 p.2)
      (encPair input encNat) encNat := by
    dsimp only [update]
    simp only [Function.update_apply, id_eq]
    polytime
  have hrenamed : ComputableInPolyTime (fun I : State Rel => I.body.relabel (update I))
      input (encCSP encRel encNat) := by
    unfold CSP.relabel Constraint.relabel
    polytime
  have hcertificate : ComputableInPolyTime (fun I : State Rel =>
      equalDropCertificate I.body I.ports.tail.tail.length I.rotation)
      input encRotationCertificate := by
    simp only [equalDropCertificate, ← CSP.vars_length_eq_occurrences]
    polytime
  have hbranch : ComputableInPolyTime
      (fun I : State Rel => if I.ports.length < 2 then I else
        ⟨I.body.relabel (update I), I.ports.tail.map (update I),
          equalDropCertificate I.body I.ports.tail.tail.length I.rotation⟩)
      input input := by polytime
  refine hbranch.of_enc_eq fun I => congrArg (encState encRel) ?_
  rcases I with ⟨F, _ | ⟨x, _ | ⟨y, ps⟩⟩, c⟩ <;> simp [fuseHead, update]

end Cslib.Complexity.CSP.CrossInsertion
