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
import CslibFrontier.Tactic.PolyTime

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

attribute [local fun_prop] OrderedBoundary.computableInPolyTime_restrictPrefix

/-- Hiding one marker is native polynomial time on every raw encoded state. Names and
entries remain binary; unary clocks come only from actual lists. No runtime provider or
source validity invariant is supplied. -/
theorem computableInPolyTime_hideHead (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (hideHead (Rel := Rel)) (encState encRel) (encState encRel) := by
  open scoped State in
  have hbranch : ComputableInPolyTime
      (fun I : State Rel => if I.ports.isEmpty then I else
        ⟨I.body, I.ports.tail,
          restrictPrefix (2 * (I.body.vars.length + I.ports.tail.length)) I.rotation⟩)
      (encState encRel) (encState encRel) := by polytime
  apply hbranch.of_enc_eq
  intro I
  apply congrArg (encState encRel)
  rcases I with ⟨F, ports, c⟩
  cases ports <;> simp [hideHead, CSP.vars_length_eq_occurrences]

end Cslib.Complexity.CSP.CrossInsertion
