/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CrossInsertion
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryDeletion
import Mathlib.Data.List.Rotate

/-!
# One executed forward rotation of an ordered boundary

`CrossInsertion.rotateLeft` moves the first port to the end and transports the actual
successor table with `OrderedBoundary.rotateBoundaryCertificate`. The full input is retained
at boundary length zero or one, including malformed or surplus table entries. The body and
its global assignments are unchanged; the directed boundary values rotate to the left.

The existing static `Witness.rotateCons` and its complete certificate equation internally
prove acceptance of the computed table. Semantic transport applies to all raw states, even
with repeated or unused names. This original single step is a prerequisite for the CROSS
compiler in [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091); positioned
operations, transposition, iteration bounds and the full compiler remain open there.

## Main definitions

* `CrossInsertion.rotateLeft`: one forward rotation on raw states.

## Main results

* `CrossInsertion.accepted_rotateLeft`: complete checker preservation for the emitted table.
* `CrossInsertion.boundary_rotateLeft_iff`: exact ordered assignment-value transport.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary

variable {Rel : Type}

/-- Move the first port to the end using the literal forward table transport, with the
actual occurrence and port counts. Empty and singleton boundaries retain the entire state. -/
@[expose] def rotateLeft (I : State Rel) : State Rel :=
  match I.ports with
  | x :: y :: ps =>
    ⟨I.body, (y :: ps) ++ [x],
      rotateBoundaryCertificate I.body.occurrences.length I.ports.length I.rotation⟩
  | _ => I

private theorem rotateLeft_body (I : State Rel) : (rotateLeft I).body = I.body := by
  rcases I with ⟨F, ports, c⟩
  cases ports with
  | nil => rfl
  | cons x ps => cases ps <;> rfl

private theorem rotateLeft_ports (I : State Rel) :
    (rotateLeft I).ports = I.ports.rotate 1 := by
  rcases I with ⟨F, ports, c⟩
  cases ports with
  | nil => rfl
  | cons x ps =>
    cases ps <;> simp [rotateLeft, List.rotate_cons_succ]

/-- The source witness and the static constructor's full table equation supply both full
checks internally. The computed output requires no target rotation or genus provider. -/
theorem accepted_rotateLeft (I : State Rel) (hI : I.Accepted) :
    (rotateLeft I).Accepted := by
  rcases I with ⟨F, ports, c⟩
  cases ports with
  | nil => exact hI
  | cons x ps =>
    cases ps with
    | nil => exact hI
    | cons y ps =>
      let w : Witness F (x :: y :: ps) := ⟨c, hI.2⟩
      have h := (w.rotateCons hI.1).accepted
      rw [Witness.rotateCons_certificate] at h
      refine ⟨?_, h⟩
      exact hI.1.perm (List.perm_append_comm (l₁ := [x]) (l₂ := y :: ps))

/-- Forward boundary rotation preserves evaluation under every global assignment. -/
theorem eval_rotateLeft (sem : Rel → List Bool → Bool) (I : State Rel) (σ : ℕ → Bool) :
    (rotateLeft I).body.eval sem σ = I.body.eval sem σ := by
  rw [rotateLeft_body]

/-- The complete ordered value word is rotated once, including repeated raw port names. -/
theorem map_ports_rotateLeft (I : State Rel) (σ : ℕ → Bool) :
    (rotateLeft I).ports.map σ = (I.ports.map σ).rotate 1 := by
  rw [rotateLeft_ports, List.map_rotate]

/-- A satisfying source assignment with the given word is exactly a satisfying output
assignment with that word rotated left. No checker, distinctness, arity or word-length
premise is needed; mismatched lengths and repeated names retain their exact meaning. -/
theorem boundary_rotateLeft_iff (sem : Rel → List Bool → Bool) (I : State Rel)
    (values : List Bool) :
    (∃ σ : ℕ → Bool, (rotateLeft I).body.eval sem σ = true ∧
      (rotateLeft I).ports.map σ = values.rotate 1) ↔
      ∃ σ : ℕ → Bool, I.body.eval sem σ = true ∧ I.ports.map σ = values := by
  simp only [eval_rotateLeft, map_ports_rotateLeft, List.rotate_eq_rotate]

end Cslib.Complexity.CSP.CrossInsertion
