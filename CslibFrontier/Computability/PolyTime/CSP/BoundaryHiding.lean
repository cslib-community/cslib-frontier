/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryHiding
import CslibFrontier.Computability.PolyTime.CSP.Boundary
import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Native polynomial time for raw head-marker hiding

The existing state encoding is unchanged: the binary-named body and binary port word
are framed, followed by the binary successor table. The retained count is computed in
unary from actual body occurrences and the boundary tail. Only this count and the actual
table length fund loops; malformed binary entries remain data. Empty boundaries return
their exact input. The relation alphabet may be any type with the supplied encoding.

## Main results

* `CrossInsertion.computableInPolyTime_hideHead`: plain native polynomial time on every raw
  state, without a checker, distinctness, arity, size or entry-bound premise.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph Turing.MultiTapeTM

variable {Rel : Type}

/-- Hiding one marker is native polynomial time on every raw encoded state. Names and
entries remain binary; unary clocks come only from actual lists. No runtime provider or
source validity invariant is supplied. -/
theorem computableInPolyTime_hideHead (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (hideHead (Rel := Rel)) (encState encRel) (encState encRel) := by
  let input := encState encRel
  have hbody := encState_body_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have hports := encState_ports_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have hrot := encState_rotation_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have htail := (ComputableInPolyTime.tail (encA := encNat)).comp hports
  have hm : ComputableInPolyTime (fun I : State Rel => I.body.occurrences.length)
      input encUnary := by
    have h := (computableInPolyTime_length_vars encRel encNat).comp hbody
    simpa only [Function.comp_def, CSP.vars_length_eq_occurrences] using h
  have hn := (ComputableInPolyTime.length_list encNat).comp htail
  have hcount : ComputableInPolyTime (fun I : State Rel =>
      2 * (I.body.occurrences.length + I.ports.tail.length)) input encUnary := by fun_prop
  have htable := OrderedBoundary.computableInPolyTime_restrictPrefix hrot hcount
  have houtput := encState_mk_polyTime encRel hbody htail htable
  have hempty := (ComputableInPolyTime.listIsEmpty (encA := encNat)).comp hports
  have hbranch := hempty.ite (ComputableInPolyTime.id' (encIn := input)) houtput
  apply hbranch.of_enc_eq
  intro I
  apply congrArg (encState encRel)
  rcases I with ⟨F, ports, c⟩
  cases ports <;> rfl

end Cslib.Complexity.CSP.CrossInsertion
