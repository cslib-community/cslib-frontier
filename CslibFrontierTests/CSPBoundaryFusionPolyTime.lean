/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.BoundaryFusion
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-! Ordinary clients of the all-raw head-fusion certificate. The input boundary can have
arbitrary length, repetitions and sparse binary names; no accepted-source premise is available.
The literal malformed example retains a closed nullary row and oversized binary table data. -/

public section

namespace CslibFrontierTests.CSPBoundaryFusionPolyTime

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP
open Cslib.Complexity.CSP.CrossInsertion Turing.MultiTapeTM

-- The generated state projection composes directly with the plain all-input certificate.
example {Rel : Type} (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun I : State Rel => (fuseHead I).rotation.successor)
      (encState encRel) (encList encNat) :=
  Graph.RotationCertificate.computableInPolyTime_successor.comp
    (encState_rotation_polyTime encRel (computableInPolyTime_fuseHead encRel))

-- This client has a varying boundary, a malformed fixed table and a closed component.
example : ComputableInPolyTime (fun ports : List ℕ =>
      fuseHead (⟨[⟨(), []⟩], ports, ⟨[2 ^ 300]⟩⟩ : State Unit))
      (encList encNat) (encState encUnit) :=
  (computableInPolyTime_fuseHead encUnit).comp
    (encState_mk_polyTime encUnit (ComputableInPolyTime.const ([⟨(), []⟩] : CSP Unit ℕ))
      ComputableInPolyTime.id'
      (ComputableInPolyTime.const (⟨[2 ^ 300]⟩ : Graph.RotationCertificate)))

/-- A rejected raw fixture whose binary labels exceed every actual loop clock. -/
def malformed : State Unit :=
  ⟨[⟨(), [2 ^ 250, 17, 2 ^ 250]⟩, ⟨(), []⟩], [2 ^ 250, 17, 17, 5, 17],
    ⟨[2 ^ 300]⟩⟩

example : ¬malformed.Accepted := by decide +kernel

example : (fuseHead malformed).body =
      [⟨(), [2 ^ 250, 2 ^ 250, 2 ^ 250]⟩, ⟨(), []⟩] ∧
    (fuseHead malformed).ports = [2 ^ 250, 2 ^ 250, 5, 2 ^ 250] ∧
    (fuseHead malformed).rotation.successor = List.replicate 14 0 := by
  decide +kernel

example : fuseHead (⟨[⟨(), []⟩], [], ⟨[2 ^ 300]⟩⟩ : State Unit) =
    ⟨[⟨(), []⟩], [], ⟨[2 ^ 300]⟩⟩ := rfl

example : fuseHead (⟨[⟨(), []⟩], [17], ⟨[2 ^ 300]⟩⟩ : State Unit) =
    ⟨[⟨(), []⟩], [17], ⟨[2 ^ 300]⟩⟩ := rfl

end CslibFrontierTests.CSPBoundaryFusionPolyTime
