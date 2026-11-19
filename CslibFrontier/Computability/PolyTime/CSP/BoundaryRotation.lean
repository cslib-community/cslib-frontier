/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryRotation
import CslibFrontier.Computability.PolyTime.Graph.RotationSystem.Reindex
import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Plain polynomial time for raw boundary rotations

The existing state encoding is unchanged: the binary-named body and binary port word
are framed, followed by the binary successor table. Actual body occurrences and boundary
length are computed in unary and fund the output range. Binary division, remainder,
comparison and arithmetic transport the indices and arbitrary malformed entries. Saturating
lookup is the existing captured reindex program; entry values never fund a loop.

The relation alphabet is arbitrary. No checker, distinctness, arity, size, entry-bound or
runtime premise is required. This is not a polynomial-time assertion for freely supplied
binary counts: the counts here are computed from actual encoded lists. It certifies only
one step; accumulated iteration and the CROSS compiler remain open in
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main results

* `CrossInsertion.computableInPolyTime_rotateLeft`: all-raw plain polynomial time with the
  unchanged state encoding.
* `CrossInsertion.computableInPolyTime_rotateRight`: all-raw RIGHT transport using the same
  private arithmetic pair in the opposite order.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph Turing.MultiTapeTM

variable {Rel : Type}

private theorem boundary_index_maps_polyTime {α : Type} {input : α ↪ List Bool}
    {m n : α → ℕ} (hm : ComputableInPolyTime m input encNat)
    (hn : ComputableInPolyTime n input encNat) :
    ComputableInPolyTime (fun p : α × ℕ =>
      boundaryIndexMap (m p.1) (n p.1) (fun j => (j + 1) % n p.1) p.2)
      (encPair input encNat) encNat ∧
    ComputableInPolyTime (fun p : α × ℕ =>
      boundaryIndexMap (m p.1) (n p.1) (fun j => (j + n p.1 - 1) % n p.1) p.2)
      (encPair input encNat) encNat := by
  have hx := ComputableInPolyTime.fst input encNat
  have hi := ComputableInPolyTime.snd input encNat
  have hM : ComputableInPolyTime (fun p : α × ℕ => m p.1)
      (encPair input encNat) encNat := hm.comp hx
  have hN : ComputableInPolyTime (fun p : α × ℕ => n p.1)
      (encPair input encNat) encNat := hn.comp hx
  have hlow : ComputableInPolyTime (fun p : α × ℕ => 2 * m p.1)
      (encPair input encNat) encNat :=
    ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2) hM
  have hhigh : ComputableInPolyTime (fun p : α × ℕ => 2 * (m p.1 + n p.1))
      (encPair input encNat) encNat :=
    ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
      (ComputableInPolyTime.binary_add' hM hN)
  have hwindow : ComputableInPolyTime (fun p : α × ℕ =>
      decide (2 * m p.1 ≤ p.2 ∧ p.2 < 2 * (m p.1 + n p.1)))
      (encPair input encNat) encBool := ComputableInPolyTime.decide_and
    (ComputableInPolyTime.binary_le.comp (hlow.prod hi))
    (ComputableInPolyTime.binary_lt' hi hhigh)
  have hquot : ComputableInPolyTime (fun p : α × ℕ => p.2 / 2)
      (encPair input encNat) encNat :=
    ComputableInPolyTime.binary_div.comp (hi.prod (ComputableInPolyTime.const 2))
  have hslot : ComputableInPolyTime (fun p : α × ℕ => p.2 / 2 - m p.1)
      (encPair input encNat) encNat := ComputableInPolyTime.binary_sub' hquot hM
  have hnext : ComputableInPolyTime (fun p : α × ℕ => (p.2 / 2 - m p.1 + 1) % n p.1)
      (encPair input encNat) encNat := ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.binary_add' hslot (ComputableInPolyTime.const 1)) hN
  have hprevious : ComputableInPolyTime (fun p : α × ℕ =>
      (p.2 / 2 - m p.1 + n p.1 - 1) % n p.1)
      (encPair input encNat) encNat := ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.binary_sub' (ComputableInPolyTime.binary_add' hslot hN)
      (ComputableInPolyTime.const 1)) hN
  have hside : ComputableInPolyTime (fun p : α × ℕ => p.2 % 2)
      (encPair input encNat) encNat :=
    ComputableInPolyTime.binary_mod' hi (ComputableInPolyTime.const 2)
  have hforwardValue : ComputableInPolyTime (fun p : α × ℕ =>
      2 * (m p.1 + ((p.2 / 2 - m p.1 + 1) % n p.1)) + p.2 % 2)
      (encPair input encNat) encNat := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
      (ComputableInPolyTime.binary_add' hM hnext)) hside
  have hbackValue : ComputableInPolyTime (fun p : α × ℕ =>
      2 * (m p.1 + ((p.2 / 2 - m p.1 + n p.1 - 1) % n p.1)) + p.2 % 2)
      (encPair input encNat) encNat := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
      (ComputableInPolyTime.binary_add' hM hprevious)) hside
  have hforward : ComputableInPolyTime (fun p : α × ℕ =>
      boundaryIndexMap (m p.1) (n p.1) (fun j => (j + 1) % n p.1) p.2)
      (encPair input encNat) encNat :=
    by simpa only [boundaryIndexMap] using
      ComputableInPolyTime.ite_decide hwindow hforwardValue hi
  have hback : ComputableInPolyTime (fun p : α × ℕ =>
      boundaryIndexMap (m p.1) (n p.1) (fun j => (j + n p.1 - 1) % n p.1) p.2)
      (encPair input encNat) encNat :=
    by simpa only [boundaryIndexMap] using
      ComputableInPolyTime.ite_decide hwindow hbackValue hi
  exact ⟨hforward, hback⟩

private theorem state_tables_polyTime (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun I : State Rel => rotateBoundaryCertificate
      I.body.occurrences.length I.ports.length I.rotation)
      (encState encRel) encRotationCertificate ∧
    ComputableInPolyTime (fun I : State Rel => rotateBoundaryCertificateRight
      I.body.occurrences.length I.ports.length I.rotation)
      (encState encRel) encRotationCertificate := by
  let input := encState encRel
  have hbody := encState_body_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have hports := encState_ports_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have hrot := encState_rotation_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  let m (I : State Rel) := I.body.occurrences.length
  let n (I : State Rel) := I.ports.length
  have hm : ComputableInPolyTime m input encUnary := by
    have h := (computableInPolyTime_length_vars encRel encNat).comp hbody
    simpa only [m, Function.comp_def, CSP.vars_length_eq_occurrences] using h
  have hn : ComputableInPolyTime n input encUnary :=
    (ComputableInPolyTime.length_list encNat).comp hports
  have hcount : ComputableInPolyTime (fun I => 2 * (m I + n I)) input encUnary := by
    fun_prop
  have hmBinary : ComputableInPolyTime m input encNat :=
    ComputableInPolyTime.unary_to_binary.comp hm
  have hnBinary : ComputableInPolyTime n input encNat :=
    ComputableInPolyTime.unary_to_binary.comp hn
  have hmaps := boundary_index_maps_polyTime hmBinary hnBinary
  have hreindex := RotationCertificate.computableInPolyTime_reindex
    (forward := fun I => boundaryIndexMap (m I) (n I) (fun j => (j + 1) % n I))
    (back := fun I => boundaryIndexMap (m I) (n I) (fun j => (j + n I - 1) % n I))
    hrot hcount hmaps.1 hmaps.2
  have hshort := ComputableInPolyTime.unary_le' hn (ComputableInPolyTime.const 1)
  have hleft : ComputableInPolyTime (fun I : State Rel =>
      rotateBoundaryCertificate (m I) (n I) I.rotation) input encRotationCertificate := by
    simpa only [rotateBoundaryCertificate] using
      ComputableInPolyTime.ite_decide hshort hrot hreindex
  have hreindexRight := RotationCertificate.computableInPolyTime_reindex
    (forward := fun I => boundaryIndexMap (m I) (n I) (fun j => (j + n I - 1) % n I))
    (back := fun I => boundaryIndexMap (m I) (n I) (fun j => (j + 1) % n I))
    hrot hcount hmaps.2 hmaps.1
  have hright : ComputableInPolyTime (fun I : State Rel =>
      rotateBoundaryCertificateRight (m I) (n I) I.rotation) input encRotationCertificate := by
    simpa only [rotateBoundaryCertificateRight_eq_reindex_mod] using
      ComputableInPolyTime.ite_decide hshort hrot hreindexRight
  exact ⟨hleft, hright⟩

/-- Execute one forward boundary rotation on every raw encoded state in plain polynomial
time. Unary counts come from the actual lists; arbitrary binary names and table entries
remain data. Empty and singleton states retain their entire original encoding. -/
theorem computableInPolyTime_rotateLeft (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (rotateLeft (Rel := Rel)) (encState encRel) (encState encRel) := by
  let input := encState encRel
  have hbody := encState_body_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have hports := encState_ports_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have htable := (state_tables_polyTime encRel).1
  have hshort := ComputableInPolyTime.unary_le'
    ((ComputableInPolyTime.length_list encNat).comp hports) (ComputableInPolyTime.const 1)
  have htail := (ComputableInPolyTime.tail (encA := encNat)).comp hports
  have hhead := (ComputableInPolyTime.headD (encA := encNat) 0).comp hports
  have hword := ComputableInPolyTime.listAppend' htail
    (ComputableInPolyTime.cons' hhead (ComputableInPolyTime.const []))
  have houtput := encState_mk_polyTime encRel hbody hword htable
  have hbranch := ComputableInPolyTime.ite_decide hshort
    (ComputableInPolyTime.id' (encIn := input)) houtput
  apply hbranch.of_enc_eq
  intro I
  apply congrArg (encState encRel)
  rcases I with ⟨F, ports, c⟩
  cases ports with
  | nil => rfl
  | cons x ps => cases ps <;> simp [rotateLeft]

/-- One RIGHT rotation is plain polynomial time on EVERY raw state with the unchanged
encoding. Unary clocks use actual lists; binary names/entries have no magnitude bound.
This is one step and does not cancel arbitrary raw full cycles. -/
theorem computableInPolyTime_rotateRight (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (rotateRight (Rel := Rel)) (encState encRel) (encState encRel) := by
  let input := encState encRel
  have hbody := encState_body_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have hports := encState_ports_polyTime encRel (ComputableInPolyTime.id' (encIn := input))
  have htable := (state_tables_polyTime encRel).2
  have hshort := ComputableInPolyTime.unary_le'
    ((ComputableInPolyTime.length_list encNat).comp hports) (ComputableInPolyTime.const 1)
  have hrev := ComputableInPolyTime.listReverseWithInput hports
  have htail := (ComputableInPolyTime.tail (encA := encNat)).comp hrev
  have hhead := (ComputableInPolyTime.headD (encA := encNat) 0).comp hrev
  have hword := ComputableInPolyTime.listReverseWithInput
    (ComputableInPolyTime.listAppend' htail
      (ComputableInPolyTime.cons' hhead (ComputableInPolyTime.const [])))
  have houtput := encState_mk_polyTime encRel hbody hword htable
  have hbranch := ComputableInPolyTime.ite_decide hshort
    (ComputableInPolyTime.id' (encIn := input)) houtput
  apply hbranch.of_enc_eq
  intro I
  apply congrArg (encState encRel)
  rcases I with ⟨F, ports, c⟩
  cases ports with
  | nil => rfl
  | cons x ps => cases ps <;> simp [rotateRight]

end Cslib.Complexity.CSP.CrossInsertion
