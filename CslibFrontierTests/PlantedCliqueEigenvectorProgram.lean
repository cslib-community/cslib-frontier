/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.EigenvectorProgram
meta import CslibFrontier.Algorithms.PlantedClique.EigenvectorProgram

/-!
# Integer spectral-filter clients

The two-vertex check identifies the filter of the ordinary adjacency matrix. The three-vertex
star makes the maximizing column differ from the first column and exercises signed entries and
stable selection among tied maximizing columns. Missing edges, ignored diagonal bits and the
empty-dimensional fallback have explicit computational checks.

The native certificate client varies the dense input and unary iteration count together.
-/

set_option linter.privateModule false

open Cslib.Algorithms.PlantedClique Turing.MultiTapeTM

example : ComputableInPolyTime
    (fun p : RecoveryInput × ℕ => eigenvectorPowerColumn p.1 p.2)
    (encPair encRecoveryInput encUnary) (encList encIntBin) := by
  fun_prop

example : ComputableInPolyTime
    (fun p : RecoveryInput × ℕ => recoverEigenvectorPowerInput p.1 p.2)
    (encPair encRecoveryInput encUnary) (encList encUnary) := by
  fun_prop

example (x : RecoveryInput) (steps : ℕ) :
    (eigenvectorPowerColumn x steps).length = x.vertexCount :=
  length_eigenvectorPowerColumn x steps

set_option linter.hashCommand false

#guard (RecoveryInput.mk 2 1 [true, true, false, true]).eigenvectorFilterRows ==
  [[251, 4], [4, 251]]

#guard eigenvectorPowerColumn (RecoveryInput.mk 2 1 [true, true, false, true]) 2 ==
  [63017, 2008]

#guard eigenvectorPowerColumn
  (RecoveryInput.mk 3 1 [true, true, true, false, true, false, false, false, true]) 1 ==
    [4, 395, -4]

#guard eigenvectorPowerColumn (RecoveryInput.mk 3 1 [true]) 1 == [399, 0, 0]

#guard eigenvectorPowerColumn (RecoveryInput.mk 3 1 []) 0 == [1, 0, 0]

#guard eigenvectorPowerColumn (RecoveryInput.mk 0 6 [true, false, true]) 20 == []
