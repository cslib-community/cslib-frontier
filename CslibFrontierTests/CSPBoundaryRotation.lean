/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryDeletion
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary

/-!
# Forward boundary-table clients

The production atom table and an unused-port star with a closed nullary component
exercise the static constructor and its literal table equation. Malformed tables expose
transformed-zero fallback and preserve exact certificate identity at boundary length zero
or one. These tests concern one forward step, not inverse or positioned constructors.
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

end CslibFrontierTests.CSPBoundaryRotation
