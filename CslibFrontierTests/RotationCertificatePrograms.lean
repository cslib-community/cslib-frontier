/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.BoundaryAppend
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Boundary

/-! Raw reindexing retains its transformed fallback. Probe append keeps literal positive
argument order and retains a closed body when its boundary is empty. -/

public section

namespace CslibFrontierTests.RotationCertificatePrograms

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP Cslib.Complexity.Graph
open OrderedBoundary

/-- One unary atom and its single-port structural probe. -/
def singlePort : RotationCertificate := ⟨[2, 1, 0, 3]⟩

/-- Two separate original unary atoms, each keeping its own variable. -/
def body : CSP Unit ℕ := [⟨(), [0]⟩, ⟨(), [1]⟩]

example : (RotationCertificate.reindex ⟨[]⟩ 2 (· + 7) (fun _ => 2 ^ 250)).successor =
    [7, 7] := by decide +kernel

example : (List.range 9).map (Nat.blockMove 2 3 4) = [0, 1, 6, 7, 8, 2, 3, 4, 5] := by
  decide +kernel

example : (RotationCertificate.reindex ⟨List.range 9⟩ 9
    (Nat.blockMove 2 3 4) (Nat.blockMove 2 4 3)).successor = List.range 9 := by
  decide +kernel

example : (appendRawCertificate 1 1 1 1 singlePort singlePort).successor =
    [6, 1, 4, 3, 2, 7, 0, 5] := by decide +kernel

example : verify body [0, 1] (appendRawCertificate 1 1 1 1 singlePort singlePort) = true := by
  decide +kernel

-- The right body is closed, with an empty probe. Its actual edge component survives.
example : (appendRawCertificate 1 1 1 0 singlePort ⟨[0, 1]⟩).successor =
    [4, 1, 2, 3, 0, 5] := by decide +kernel

example : verify body [0] (appendRawCertificate 1 1 1 0 singlePort ⟨[0, 1]⟩) = true := by
  decide +kernel

example : appendRawCertificate 0 0 0 0 ⟨[]⟩ ⟨[]⟩ = ⟨[]⟩ := rfl

end CslibFrontierTests.RotationCertificatePrograms
