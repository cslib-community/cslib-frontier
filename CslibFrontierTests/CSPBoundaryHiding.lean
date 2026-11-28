/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.BoundaryHiding
import CslibFrontier.Computability.PolyTime.CSP.BoundaryFusion
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary

/-! Ordinary clients of head-marker hiding and its shared plain restriction certificate.
The production atom table is reused; no CROSS fixture is duplicated. Closed false nullaries,
hidden unused ports, repeated raw ports and oversized binary entries remain explicit. -/

public section

namespace CslibFrontierTests.CSPBoundaryHiding

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP
open OrderedBoundary CrossInsertion Turing.MultiTapeTM

/-- A sparse binary atom and a separate false nullary symbol, using the production table. -/
def atomWithNullary : State Bool :=
  ⟨[⟨true, [2 ^ 250, 17]⟩, ⟨false, []⟩], [2 ^ 250, 17], atomBoundaryCertificate 2⟩

example : CSP.validArity (fun r : Bool => if r then 2 else 0) atomWithNullary.body = true := by
  decide +kernel

example : atomWithNullary.Accepted := by decide +kernel

example : (hideHead atomWithNullary).Accepted :=
  accepted_hideHead atomWithNullary (by decide +kernel)

example : (hideHead atomWithNullary).body = atomWithNullary.body ∧
    (hideHead atomWithNullary).ports = [17] ∧
    (hideHead atomWithNullary).rotation.successor = [0, 3, 4, 1, 2, 5] := by
  decide +kernel

example (σ : ℕ → Bool) :
    (hideHead atomWithNullary).body.eval (fun r xs => r && decide (xs ≠ [])) σ = false := by
  simp [hideHead, atomWithNullary, CSP.eval, Constraint.eval]

private def unused : State Unit := ⟨[⟨(), []⟩], [2 ^ 250], ⟨[0, 1]⟩⟩

example : unused.Accepted ∧ (hideHead unused).Accepted :=
  ⟨by decide +kernel, accepted_hideHead unused (by decide +kernel)⟩

example : hideHead unused = (⟨[⟨(), []⟩], [], ⟨[]⟩⟩ : State Unit) := rfl

example : hideHead (⟨[⟨(), []⟩], [], ⟨[2 ^ 300]⟩⟩ : State Unit) =
    ⟨[⟨(), []⟩], [], ⟨[2 ^ 300]⟩⟩ := rfl

example : (hideHead (⟨[⟨(), []⟩], [3, 3], ⟨[2 ^ 300]⟩⟩ : State Unit)).ports = [3] ∧
    (hideHead (⟨[⟨(), []⟩], [3, 3], ⟨[2 ^ 300]⟩⟩ : State Unit)).rotation.successor = [0, 0] := by
  decide +kernel

example (sem : Unit → List Bool → Bool) (F : CSP Unit ℕ) (p : ℕ)
    (ps : List ℕ) (c : Graph.RotationCertificate) (values : List Bool)
    (h : ∃ σ : ℕ → Bool, F.eval sem σ = true ∧ (p :: ps).map σ = true :: values) :
    ∃ σ : ℕ → Bool, (hideHead (⟨F, p :: ps, c⟩ : State Unit)).body.eval sem σ = true ∧
      (hideHead (⟨F, p :: ps, c⟩ : State Unit)).ports.map σ = values :=
  (boundary_hideHead_iff sem F p ps c values).mpr ⟨true, h⟩

-- A raw composition certificate needs no acceptance premise or finite target alphabet.
example {Rel : Type} (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun I : State Rel => hideHead (fuseHead I))
      (encState encRel) (encState encRel) :=
  (computableInPolyTime_hideHead encRel).comp (computableInPolyTime_fuseHead encRel)

example {Rel : Type} (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun I : State Rel => (hideHead I).rotation.successor)
      (encState encRel) (encList encNat) :=
  Graph.RotationCertificate.computableInPolyTime_successor.comp
    (encState_rotation_polyTime encRel (computableInPolyTime_hideHead encRel))

end CslibFrontierTests.CSPBoundaryHiding
