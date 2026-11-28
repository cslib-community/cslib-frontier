/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.Selection
meta import CslibFrontier.Algorithms.PlantedClique.Selection
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List.Sort
import CslibFrontier.Tactic.PolyTime

/-! Executable checks for stable coordinate selection and dense degree cleanup. -/

set_option linter.privateModule false
-- These checks execute the compiled stable sorting implementation.
set_option linter.hashCommand false

open Cslib.Algorithms.PlantedClique Turing.MultiTapeTM

-- Equal absolute scores retain their original index order.
#guard largestIndices 2 [-4, 4, 1, -5] == [3, 0]

-- A requested size beyond the available coordinates keeps each index once.
#guard largestIndices 9 [-4, 4, 1, -5] == [3, 0, 1, 2]

-- The lower triangular word entries are ignored by the symmetric graph decoder.
example : (RecoveryInput.mk 3 2 [false, true]).adjacent 1 0 = true := by decide

-- This path has both selected vertices adjacent only to its middle vertex.
example : (RecoveryInput.mk 3 2 [false, true, false, false, false, true]).cleanup [0, 2] =
    [1] := by decide

-- The missing second edge is padded by false, so the degree threshold fails everywhere.
example : (RecoveryInput.mk 3 2 [false, true]).cleanup [0, 2] = [] := by decide

-- The loopless convention counts three neighbors inside a complete four-vertex graph.
example : (RecoveryInput.mk 4 4 (List.replicate 16 true)).cleanup [0, 1, 2, 3] =
    [0, 1, 2, 3] := by decide

example : ComputableInPolyTime (fun p : ℕ × List ℤ => largestIndices p.1 p.2)
    (encPair encUnary (encList encIntBin)) (encList encUnary) := by
  fun_prop

example : ComputableInPolyTime (fun p : RecoveryInput × List ℕ => p.1.cleanup p.2)
    (encPair encRecoveryInput (encList encUnary)) (encList encUnary) := by
  fun_prop

-- A separate binary-natural client does not capture the input in its comparison.
example : ComputableInPolyTime
    (fun xs : List ℕ => xs.mergeSort fun a b => decide (a ≤ b))
    (encList encNat) (encList encNat) := by
  have hrel : ComputableInPolyTime
      (fun p : (List ℕ × ℕ) × ℕ => decide (p.1.2 ≤ p.2))
      (encPair (encPair (encList encNat) encNat) encNat) encBool :=
    ComputableInPolyTime.binary_le.comp
      (g := fun p : (List ℕ × ℕ) × ℕ => (p.1.2, p.2)) (by fun_prop)
  exact ComputableInPolyTime.mergeSortWithInput
    (r := fun (_ : List ℕ) a b => a ≤ b) ComputableInPolyTime.id' hrel
    (fun _ _ _ _ => le_trans) (fun _ => le_total)
