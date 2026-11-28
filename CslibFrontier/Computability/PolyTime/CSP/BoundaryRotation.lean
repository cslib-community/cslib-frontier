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
import CslibFrontier.Tactic.PolyTime

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

open scoped State

private theorem boundary_index_maps_polyTime {α : Type} {input : α ↪ List Bool}
    {m n : α → ℕ} (hm : ComputableInPolyTime m input encNat)
    (hn : ComputableInPolyTime n input encNat) :
    ComputableInPolyTime (fun p : α × ℕ =>
      boundaryIndexMap (m p.1) (n p.1) (fun j => (j + 1) % n p.1) p.2)
      (encPair input encNat) encNat ∧
    ComputableInPolyTime (fun p : α × ℕ =>
      boundaryIndexMap (m p.1) (n p.1) (fun j => (j + n p.1 - 1) % n p.1) p.2)
      (encPair input encNat) encNat := by
  have hM : ComputableInPolyTime (fun p : α × ℕ => m p.1) (encPair input encNat) encNat :=
    hm.comp (.fst input encNat)
  have hN : ComputableInPolyTime (fun p : α × ℕ => n p.1) (encPair input encNat) encNat :=
    hn.comp (.fst input encNat)
  have hi := ComputableInPolyTime.snd input encNat
  have htwo := ComputableInPolyTime.const (encIn := encPair input encNat) (encOut := encNat) 2
  have hone := ComputableInPolyTime.const (encIn := encPair input encNat) (encOut := encNat) 1
  have hwin := ((htwo.binary_mul' hM).binary_le' hi).decide_and
    (hi.binary_lt' (htwo.binary_mul' (hM.binary_add' hN)))
  have hslot := (hi.binary_div' htwo).binary_sub' hM
  have hside := hi.binary_mod' htwo
  simp only [boundaryIndexMap]
  exact ⟨hwin.ite_decide
      ((htwo.binary_mul' (hM.binary_add' ((hslot.binary_add' hone).binary_mod' hN))).binary_add'
        hside) hi,
    hwin.ite_decide
      ((htwo.binary_mul' (hM.binary_add' (((hslot.binary_add' hN).binary_sub' hone).binary_mod'
        hN))).binary_add' hside) hi⟩

private theorem state_tables_polyTime (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun I : State Rel => rotateBoundaryCertificate
      I.body.occurrences.length I.ports.length I.rotation)
      (encState encRel) encRotationCertificate ∧
    ComputableInPolyTime (fun I : State Rel => rotateBoundaryCertificateRight
      I.body.occurrences.length I.ports.length I.rotation)
      (encState encRel) encRotationCertificate := by
  simp only [← CSP.vars_length_eq_occurrences]
  have hmaps := boundary_index_maps_polyTime (input := encState encRel)
    (m := fun I : State Rel => I.body.vars.length)
    (n := fun I : State Rel => I.ports.length)
    (by polytime) (by polytime)
  have hreindex := RotationCertificate.computableInPolyTime_reindex
    (table := State.rotation) (count := fun I => 2 * (I.body.vars.length + I.ports.length))
    (forward := fun I : State Rel =>
      boundaryIndexMap I.body.vars.length I.ports.length (fun j => (j + 1) % I.ports.length))
    (back := fun I : State Rel => boundaryIndexMap I.body.vars.length I.ports.length
      (fun j => (j + I.ports.length - 1) % I.ports.length))
    (by fun_prop) (by fun_prop) hmaps.1 hmaps.2
  have hreindexRight := RotationCertificate.computableInPolyTime_reindex
    (table := State.rotation) (count := fun I => 2 * (I.body.vars.length + I.ports.length))
    (forward := fun I : State Rel => boundaryIndexMap I.body.vars.length I.ports.length
      (fun j => (j + I.ports.length - 1) % I.ports.length))
    (back := fun I : State Rel =>
      boundaryIndexMap I.body.vars.length I.ports.length (fun j => (j + 1) % I.ports.length))
    (by fun_prop) (by fun_prop) hmaps.2 hmaps.1
  refine ⟨by polytime [rotateBoundaryCertificate], ?_⟩
  simp only [rotateBoundaryCertificateRight_eq_reindex_mod]
  polytime

/-- Execute one forward boundary rotation on every raw encoded state in plain polynomial
time. Unary counts come from the actual lists; arbitrary binary names and table entries
remain data. Empty and singleton states retain their entire original encoding. -/
theorem computableInPolyTime_rotateLeft (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (rotateLeft (Rel := Rel)) (encState encRel) (encState encRel) := by
  have htable := (state_tables_polyTime encRel).1
  have hbranch : ComputableInPolyTime
      (fun I : State Rel => if I.ports.length ≤ 1 then I else
        ⟨I.body, I.ports.tail ++ [I.ports.headD 0],
          rotateBoundaryCertificate I.body.occurrences.length I.ports.length I.rotation⟩)
      (encState encRel) (encState encRel) := by polytime
  refine hbranch.of_enc_eq fun ⟨F, ports, c⟩ => congrArg (encState encRel) ?_
  rcases ports with _ | ⟨x, _ | _⟩ <;> simp [rotateLeft]

/-- One RIGHT rotation is plain polynomial time on EVERY raw state with the unchanged
encoding. Unary clocks use actual lists; binary names/entries have no magnitude bound.
This is one step and does not cancel arbitrary raw full cycles. -/
theorem computableInPolyTime_rotateRight (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (rotateRight (Rel := Rel)) (encState encRel) (encState encRel) := by
  have htable := (state_tables_polyTime encRel).2
  have hrev := ComputableInPolyTime.listReverseWithInput (list := State.ports (Rel := Rel))
    (encA := encNat) (encIn := encState encRel) (by fun_prop)
  have hword := ComputableInPolyTime.listReverseWithInput
    (list := fun I : State Rel => I.ports.reverse.tail ++ [I.ports.reverse.headD 0])
    (encA := encNat) (encIn := encState encRel) (by fun_prop)
  have hbranch : ComputableInPolyTime
      (fun I : State Rel => if I.ports.length ≤ 1 then I else
        ⟨I.body, (I.ports.reverse.tail ++ [I.ports.reverse.headD 0]).reverse,
          rotateBoundaryCertificateRight I.body.occurrences.length I.ports.length I.rotation⟩)
      (encState encRel) (encState encRel) :=
    ComputableInPolyTime.ite_decide (by fun_prop) (by fun_prop) (by fun_prop)
  refine hbranch.of_enc_eq fun ⟨F, ports, c⟩ => congrArg (encState encRel) ?_
  rcases ports with _ | ⟨x, _ | _⟩ <;> simp [rotateRight]

end Cslib.Complexity.CSP.CrossInsertion
