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
# Executed one-step rotations of an ordered boundary

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
* `CrossInsertion.rotateRight`: one backward word rotation with the executed RIGHT table.

## Main results

* `CrossInsertion.accepted_rotateLeft`: complete checker preservation for the emitted table.
* `CrossInsertion.boundary_rotateLeft_iff`: exact ordered assignment-value transport.
* `CrossInsertion.accepted_rotateRight`: full checker preservation for RIGHT transport.
* `CrossInsertion.boundary_rotateRight_iff`: exact rightward assignment-value transport.
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

/-- LEFT boundary movement retains the entire actual body. -/
theorem rotateLeft_body (I : State Rel) : (rotateLeft I).body = I.body := by
  rcases I with ⟨F, ports, c⟩
  cases ports with
  | nil => rfl
  | cons x ps => cases ps <;> rfl

/-- LEFT boundary movement rotates the ordered raw port word by one position. -/
theorem rotateLeft_ports (I : State Rel) :
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

/-- Move the last port to the front with the literal RIGHT table transport. Empty and
singleton raw boundaries retain the entire original state, including malformed entries. -/
@[expose] def rotateRight (I : State Rel) : State Rel :=
  match I.ports with
  | _ :: _ :: _ =>
    ⟨I.body, (I.ports.reverse.tail ++ [I.ports.reverse.headD 0]).reverse,
      rotateBoundaryCertificateRight I.body.occurrences.length I.ports.length I.rotation⟩
  | _ => I

/-- Moving the last raw port to the front emits the literal RIGHT table on all inputs. -/
theorem rotateRight_snoc (F : CSP Rel ℕ) (ps : List ℕ) (p : ℕ)
    (c : Graph.RotationCertificate) :
    rotateRight (⟨F, ps ++ [p], c⟩ : State Rel) =
      ⟨F, p :: ps, rotateBoundaryCertificateRight F.occurrences.length (ps.length + 1) c⟩ := by
  cases ps with
  | nil => simp [rotateRight, rotateBoundaryCertificateRight]
  | cons x xs =>
    cases xs <;> simp [rotateRight, List.reverse_append, List.reverse_cons]

/-- RIGHT boundary movement retains the entire actual body. -/
theorem rotateRight_body (I : State Rel) : (rotateRight I).body = I.body := by
  rcases I with ⟨F, ports, c⟩
  induction ports using List.reverseRecOn with
  | nil => rfl
  | append_singleton ps p _ih => rw [rotateRight_snoc]

/-- RIGHT boundary movement rotates the ordered raw port word by one position. -/
theorem rotateRight_ports (I : State Rel) :
    (rotateRight I).ports = (I.ports.reverse.rotate 1).reverse := by
  rcases I with ⟨F, ports, c⟩
  induction ports using List.reverseRecOn with
  | nil => simp [rotateRight]
  | append_singleton ps p _ih =>
    rw [rotateRight_snoc]
    simp [List.reverse_append, List.rotate_cons_succ]

/-- The actual last-to-first static constructor supplies full acceptance of the computed
RIGHT table. No target rotation, genus, order agreement or recognition provider is input. -/
theorem accepted_rotateRight (I : State Rel) (hI : I.Accepted) :
    (rotateRight I).Accepted := by
  rcases I with ⟨F, ports, c⟩
  induction ports using List.reverseRecOn with
  | nil => exact hI
  | append_singleton ps p _ih =>
    rw [rotateRight_snoc]
    let w : Witness F (ps ++ [p]) := ⟨c, hI.2⟩
    have h := (w.unrotateSnoc hI.1).accepted
    rw [Witness.unrotateSnoc_certificate] at h
    exact ⟨hI.1.perm (List.perm_append_comm (l₁ := ps) (l₂ := [p])), h⟩

/-- RIGHT boundary movement leaves every body evaluation unchanged under every assignment. -/
theorem eval_rotateRight (sem : Rel → List Bool → Bool) (I : State Rel) (σ : ℕ → Bool) :
    (rotateRight I).body.eval sem σ = I.body.eval sem σ := by
  rw [rotateRight_body]

/-- The complete mapped word moves right, including repeated and unused raw port names.
The two word reversals do not reflect a constraint scope or its rotation. -/
theorem map_ports_rotateRight (I : State Rel) (σ : ℕ → Bool) :
    (rotateRight I).ports.map σ = ((I.ports.map σ).reverse.rotate 1).reverse := by
  rw [rotateRight_ports, List.map_reverse, List.map_rotate, List.map_reverse]

/-- Exact rightward ordered-value transport for arbitrary raw states and value words.
The same body assignments work on both sides; no checker, distinctness, arity or word-length
premise is required. This makes no raw full-cycle cancellation assertion. -/
theorem boundary_rotateRight_iff (sem : Rel → List Bool → Bool) (I : State Rel)
    (values : List Bool) :
    (∃ σ : ℕ → Bool, (rotateRight I).body.eval sem σ = true ∧
      (rotateRight I).ports.map σ = (values.reverse.rotate 1).reverse) ↔
      ∃ σ : ℕ → Bool, I.body.eval sem σ = true ∧ I.ports.map σ = values := by
  simp only [eval_rotateRight, map_ports_rotateRight, List.reverse_inj, List.rotate_eq_rotate]

end Cslib.Complexity.CSP.CrossInsertion
