/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.GadgetCyclic

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryDeletion
public import CslibFrontier.Computability.PolyTime.CSP.BoundaryRotation
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary
import Mathlib.Data.List.Rotate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-!
# Directed boundary-table clients

The production atom table and an unused-port star with a closed nullary component
exercise the static constructor and its literal table equation. Malformed tables expose
transformed-zero fallback and preserve exact certificate identity at boundary length zero
or one. These tests concern individual directed steps and raw cycle noncancellation,
not positioned operations or a compiler.
-/

public section

namespace CslibFrontierTests.CSPBoundaryRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity Cslib.Complexity.CSP
open OrderedBoundary

example (c : Graph.RotationCertificate) (M : ℕ) :
    rotateBoundaryCertificate M 0 c = c ∧ rotateBoundaryCertificate M 1 c = c := by
  simp [rotateBoundaryCertificate]

example : rotateBoundaryCertificate 20 0 ⟨[2 ^ 300, 7, 9]⟩ = ⟨[2 ^ 300, 7, 9]⟩ ∧
    rotateBoundaryCertificate 20 1 ⟨[2 ^ 300, 7, 9]⟩ = ⟨[2 ^ 300, 7, 9]⟩ :=
  ⟨rfl, rfl⟩

example : (rotateBoundaryCertificate 0 2 ⟨[]⟩).successor = [2, 2, 2, 2] := by
  decide +kernel

example : (rotateBoundaryCertificate 0 3 ⟨[]⟩).successor = [2, 2, 2, 2, 2, 2] ∧
    (rotateBoundaryCertificate 0 3 ⟨[]⟩).successor ≠ [4, 4, 4, 4, 4, 4] := by
  decide +kernel

-- The opposite probe-only arithmetic would send the missing-entry zero to four.
example : (Graph.RotationCertificate.reindex ⟨[]⟩ 6
    (fun i => 2 * ((i / 2 + 3 - 1) % 3) + i % 2)
    (fun i => 2 * ((i / 2 + 1) % 3) + i % 2)).successor = [4, 4, 4, 4, 4, 4] := by
  decide +kernel

example : (rotateBoundaryCertificate 1 2 ⟨[]⟩).successor = [0, 0, 0, 0, 0, 0] := by
  decide +kernel

-- Raw counts retain repeated body occurrences and repeated sparse port names.
example : (rotateBoundaryCertificate
      (CSP.occurrences ([⟨(), [2 ^ 250, 2 ^ 250]⟩] : CSP Unit ℕ)).length
      ([2 ^ 250, 7, 2 ^ 250] : List ℕ).length ⟨[2 ^ 300]⟩).successor =
      [2 ^ 300, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- The existing production atom certificate on three distinct actual names. -/
def atomSource : Witness ([⟨(), [0, 1, 2]⟩] : CSP Unit ℕ) [0, 1, 2] :=
  ⟨atomBoundaryCertificate 3, by decide +kernel⟩

example : (atomSource.rotateCons (by decide)).certificate.successor =
    [6, 3, 10, 5, 8, 1, 0, 9, 4, 11, 2, 7] := by
  rw [Witness.rotateCons_certificate]
  decide +kernel

-- The old generic constructor is inspected through its new public equation as well.
example (v : Fin 3 → ℕ) (w : Witness ([⟨(), []⟩] : CSP Unit ℕ) (List.ofFn v))
    (hn : (List.ofFn v).Nodup) :
    (w.rotateOfFn hn).certificate.successor =
      (rotateBoundaryCertificate 0 3 w.certificate).successor := by
  rw [Witness.rotateOfFn_certificate]
  rfl

/-- Three unused boundary names and a separate closed nullary body component. -/
def closedStar : Witness ([⟨(), []⟩] : CSP Unit ℕ) [10, 20, 30] :=
  ⟨⟨[0, 3, 2, 5, 4, 1]⟩, by decide +kernel⟩

example : (closedStar.rotateCons (by decide)).certificate.successor = [0, 3, 2, 5, 4, 1] := by
  rw [Witness.rotateCons_certificate]
  decide +kernel

-- State-level clients retain the earlier static and numeric tests above unchanged.
open CrossInsertion Turing.MultiTapeTM

private def atomState : State Unit :=
  ⟨[⟨(), [0, 1, 2]⟩], [0, 1, 2], atomSource.certificate⟩

example : (rotateLeft atomState).Accepted :=
  accepted_rotateLeft atomState ⟨by decide, atomSource.accepted⟩

example : (rotateLeft atomState).ports = [1, 2, 0] ∧
    (rotateLeft atomState).body = atomState.body ∧
    (rotateLeft atomState).rotation.successor = [6, 3, 10, 5, 8, 1, 0, 9, 4, 11, 2, 7] := by
  decide +kernel

private def closedState : State Unit :=
  ⟨[⟨(), []⟩], [10, 20, 30], closedStar.certificate⟩

example : (rotateLeft closedState).Accepted :=
  accepted_rotateLeft closedState ⟨by decide, closedStar.accepted⟩

example : (rotateLeft closedState).ports = [20, 30, 10] ∧
    (rotateLeft closedState).ports ≠ [30, 10, 20] ∧
    (rotateLeft closedState).rotation.successor = [0, 3, 2, 5, 4, 1] := by
  decide +kernel

example (σ : ℕ → Bool) :
    (rotateLeft closedState).body.eval (fun _ _ => false) σ = false := by
  rw [eval_rotateLeft]
  rfl

-- Short raw states preserve the complete malformed/surplus input, not just its fields' sizes.
example : rotateLeft (⟨[⟨(), []⟩], [], ⟨[2 ^ 300, 7, 9]⟩⟩ : State Unit) =
    ⟨[⟨(), []⟩], [], ⟨[2 ^ 300, 7, 9]⟩⟩ := rfl

example : rotateLeft (⟨[⟨(), []⟩], [2 ^ 250], ⟨[2 ^ 300, 7, 9]⟩⟩ : State Unit) =
    ⟨[⟨(), []⟩], [2 ^ 250], ⟨[2 ^ 300, 7, 9]⟩⟩ := rfl

example : (rotateLeft (⟨[], [17, 5], ⟨[]⟩⟩ : State Unit)).rotation.successor =
    [2, 2, 2, 2] := by decide +kernel

example : (rotateLeft (⟨[], [17, 5, 7], ⟨[]⟩⟩ : State Unit)).rotation.successor =
    [2, 2, 2, 2, 2, 2] ∧
    (rotateLeft (⟨[], [17, 5, 7], ⟨[]⟩⟩ : State Unit)).rotation.successor ≠
      [4, 4, 4, 4, 4, 4] := by decide +kernel

example : (rotateLeft (⟨[⟨(), [17]⟩], [17, 5], ⟨[]⟩⟩ : State Unit)).rotation.successor =
    [0, 0, 0, 0, 0, 0] := by decide +kernel

private def malformedState : State Unit :=
  ⟨[⟨(), [2 ^ 250, 2 ^ 250]⟩, ⟨(), []⟩], [2 ^ 250, 7, 2 ^ 250], ⟨[2 ^ 300]⟩⟩

example : ¬malformedState.Accepted := by decide +kernel

example : (rotateLeft malformedState).body = malformedState.body ∧
    (rotateLeft malformedState).ports = [7, 2 ^ 250, 2 ^ 250] ∧
    (rotateLeft malformedState).rotation.successor =
      [2 ^ 300, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel

-- Existential transport is nonvacuous even with repeated raw names and a rejected table.
example : ∃ σ : ℕ → Bool,
    (rotateLeft (⟨[], [5, 5, 9], ⟨[2 ^ 300]⟩⟩ : State Unit)).body.eval
      (fun _ _ => true) σ = true ∧
    (rotateLeft (⟨[], [5, 5, 9], ⟨[2 ^ 300]⟩⟩ : State Unit)).ports.map σ =
      [true, false, true] := by
  have h := (boundary_rotateLeft_iff (fun _ _ => true)
    (⟨[], [5, 5, 9], ⟨[2 ^ 300]⟩⟩ : State Unit) [true, true, false]).mpr
    ⟨fun z => decide (z = 5), rfl, by decide +kernel⟩
  simpa only [List.rotate_cons_succ, List.rotate_zero, List.cons_append, List.nil_append]
    using h

example : ¬∃ σ : ℕ → Bool,
    (rotateLeft (⟨[], [5, 5, 9], ⟨[]⟩⟩ : State Unit)).ports.map σ =
      [false, false, true] := by
  rintro ⟨σ, h⟩
  change [σ 5, σ 9, σ 5] = [false, false, true] at h
  have hfirst := (List.cons.inj h).1
  have hlast := (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).1
  cases hfirst.symm.trans hlast

-- Plain all-raw certificates compose through generated field projections, with no Finite Rel.
example {Rel : Type} (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun I : State Rel => (rotateLeft I).rotation.successor)
      (encState encRel) (encList encNat) :=
  Graph.RotationCertificate.computableInPolyTime_successor.comp
    (encState_rotation_polyTime encRel (computableInPolyTime_rotateLeft encRel))

-- Varying raw boundary lengths fund the clock, even with a fixed huge malformed table.
example : ComputableInPolyTime (fun ports : List ℕ =>
      rotateLeft (⟨[⟨(), []⟩], ports, ⟨[2 ^ 300]⟩⟩ : State Unit))
      (encList encNat) (encState encUnit) :=
  (computableInPolyTime_rotateLeft encUnit).comp
    (encState_mk_polyTime encUnit (ComputableInPolyTime.const ([⟨(), []⟩] : CSP Unit ℕ))
      ComputableInPolyTime.id'
      (ComputableInPolyTime.const (⟨[2 ^ 300]⟩ : Graph.RotationCertificate)))

-- The existing domain encoding and its generated projections remain directly usable.
example {Rel : Type} (encRel : Rel ↪ List Bool) (I : State Rel) :
    encState encRel (rotateLeft I) =
      encPair (encCSP encRel encNat)
        (encPair (encList encNat) Graph.encRotationCertificate)
        ((rotateLeft I).body, (rotateLeft I).ports, (rotateLeft I).rotation) := rfl

-- RIGHT clients use the same production atom and closed-star fixtures as LEFT.
example : (rotateRight atomState).Accepted :=
  accepted_rotateRight atomState ⟨by decide, atomSource.accepted⟩

example : (rotateRight atomState).ports = [2, 0, 1] ∧
    (rotateRight atomState).body = atomState.body ∧
    (rotateRight atomState).rotation.successor = [8, 3, 6, 5, 10, 1, 2, 9, 0, 11, 4, 7] := by
  decide +kernel

example : (rotateRight closedState).Accepted :=
  accepted_rotateRight closedState ⟨by decide, closedStar.accepted⟩

example : (rotateRight closedState).ports = [30, 10, 20] ∧
    (rotateRight closedState).ports ≠ [20, 30, 10] ∧
    (rotateRight closedState).rotation.successor = [0, 3, 2, 5, 4, 1] := by
  decide +kernel

example : rotateRight (⟨[⟨(), []⟩], [], ⟨[2 ^ 300, 7, 9]⟩⟩ : State Unit) =
    ⟨[⟨(), []⟩], [], ⟨[2 ^ 300, 7, 9]⟩⟩ := rfl

example : rotateRight (⟨[⟨(), []⟩], [2 ^ 250], ⟨[2 ^ 300, 7, 9]⟩⟩ : State Unit) =
    ⟨[⟨(), []⟩], [2 ^ 250], ⟨[2 ^ 300, 7, 9]⟩⟩ := rfl

example : (rotateRight (⟨[], [17, 5, 7], ⟨[]⟩⟩ : State Unit)).rotation.successor =
    [4, 4, 4, 4, 4, 4] ∧
    (rotateRight (⟨[], [17, 5, 7], ⟨[]⟩⟩ : State Unit)).rotation.successor ≠
      [2, 2, 2, 2, 2, 2] := by decide +kernel

example : (rotateRight (⟨[], [17, 5], ⟨[]⟩⟩ : State Unit)).rotation.successor =
    [2, 2, 2, 2] := by decide +kernel

example : (rotateRight (⟨[⟨(), [17]⟩], [17, 5], ⟨[]⟩⟩ : State Unit)).rotation.successor =
    [0, 0, 0, 0, 0, 0] := by decide +kernel

example : (rotateRight malformedState).body = malformedState.body ∧
    (rotateRight malformedState).ports = [2 ^ 250, 2 ^ 250, 7] ∧
    (rotateRight malformedState).rotation.successor =
      [2 ^ 300, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel

-- One full raw cycle preserves the word but need not recover an empty malformed table.
example : (rotateRight (rotateRight (⟨[], [5, 7], ⟨[]⟩⟩ : State Unit))).ports = [5, 7] ∧
    (rotateRight (rotateRight (⟨[], [5, 7], ⟨[]⟩⟩ : State Unit))).rotation.successor =
      [0, 0, 0, 0] := by decide +kernel

example : ∃ σ : ℕ → Bool,
    (rotateRight (⟨[], [5, 5, 9], ⟨[2 ^ 300]⟩⟩ : State Unit)).body.eval
      (fun _ _ => true) σ = true ∧
    (rotateRight (⟨[], [5, 5, 9], ⟨[2 ^ 300]⟩⟩ : State Unit)).ports.map σ =
      [false, true, true] := by
  have h := (boundary_rotateRight_iff (fun _ _ => true)
    (⟨[], [5, 5, 9], ⟨[2 ^ 300]⟩⟩ : State Unit) [true, true, false]).mpr
    ⟨fun z => decide (z = 5), rfl, by decide +kernel⟩
  simpa only [List.reverse_cons, List.reverse_nil, List.rotate_cons_succ,
    List.rotate_zero, List.cons_append, List.nil_append] using h

example {Rel : Type} (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun I : State Rel => (rotateRight I).rotation.successor)
      (encState encRel) (encList encNat) :=
  Graph.RotationCertificate.computableInPolyTime_successor.comp
    (encState_rotation_polyTime encRel (computableInPolyTime_rotateRight encRel))

example : ComputableInPolyTime (fun ports : List ℕ =>
      rotateRight (⟨[⟨(), []⟩], ports, ⟨[2 ^ 300]⟩⟩ : State Unit))
      (encList encNat) (encState encUnit) :=
  (computableInPolyTime_rotateRight encUnit).comp
    (encState_mk_polyTime encUnit (ComputableInPolyTime.const ([⟨(), []⟩] : CSP Unit ℕ))
      ComputableInPolyTime.id'
      (ComputableInPolyTime.const (⟨[2 ^ 300]⟩ : Graph.RotationCertificate)))

-- The actual old opposite-direction gadget constructor, not a copied table surgery.
example : ((Witness.atom (fun _ : Unit => 3) (fun _ _ => true) ()).rotate).certificate.successor =
    [8, 3, 6, 5, 10, 1, 2, 9, 0, 11, 4, 7] := by
  rw [GadgetWitness.rotate_certificate]
  decide +kernel

end CslibFrontierTests.CSPBoundaryRotation
