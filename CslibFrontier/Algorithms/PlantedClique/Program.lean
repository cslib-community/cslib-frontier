/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Selection
public import CslibFrontier.Algorithms.IntegerPower.Program
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# A uniform program for spectral planted-clique recovery

This module realizes the complete recovery algorithm on the dense inputs of `RecoveryInput`.
The vertex count, target clique size, and adjacency word all vary at runtime. Search counters
use unary encodings; matrix and vector entries and squared norms use signed binary encodings.

The program enumerates the same candidate columns in the same order as `growingColumn?`, with
the same exact integer growth test. Its zero fallback, selection among tied coordinates, and
degree-cleanup threshold are also identical. `toFinset_recoverInput` identifies the complete
list of output identifiers with `recover` on the decoded graph. This agreement holds for every
dense input, including empty graphs and malformed adjacency words.

`computableInPolyTime_recoverInput` gives one native multitape polynomial-time certificate for
all dense inputs. It charges building the signed matrix, enumerating and testing candidate
columns, sorting their coordinates, and degree cleanup. The power-column kernel bounds all
intermediate signed-binary encodings. The certificate has no planted-clique or spectral premise;
the probabilistic correctness theorem is connected separately in `PolyTime`.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Turing.MultiTapeTM Matrix IntegerPower

/-- Recover a list of vertex identifiers from a dense input by exact integer powers, stable
coordinate selection, and degree cleanup. -/
@[expose] def recoverInput (x : RecoveryInput) : List ℕ :=
  x.cleanup (largestIndices x.cliqueSize (recoveredIntegerVector x.signedRows x.cliqueSize))

/-- The complete list program computes precisely the mathematical recovery set, including on
inputs outside the probabilistic recovery regime. -/
theorem toFinset_recoverInput (x : RecoveryInput) :
    (recoverInput x).toFinset = (recover x.graph x.cliqueSize).image Fin.val := by
  unfold recoverInput recover
  apply x.toFinset_cleanup _ _ _ (nodup_largestIndices _ _)
  rw [x.signedRows_eq_ofFn,
    recoveredIntegerVector_ofFn (signedAdjacency x.graph) x.cliqueSize]
  exact toFinset_largestIndices_ofFn x.cliqueSize
    (recoveredVector (signedAdjacency x.graph) x.cliqueSize)

/-- A single native multitape machine computes the complete recovery output in polynomial time
on every dense input. Both dimensions are supplied at runtime, and the output identifiers are
framed unary naturals. -/
@[fun_prop] theorem computableInPolyTime_recoverInput :
    ComputableInPolyTime recoverInput encRecoveryInput (encList encUnary) := by
  unfold recoverInput
  exact RecoveryInput.computableInPolyTime_cleanup ComputableInPolyTime.id'
    (computableInPolyTime_largestIndices (by fun_prop)
      (computableInPolyTime_recoveredIntegerVector
        RecoveryInput.computableInPolyTime_signedRows (by fun_prop)))

end Cslib.Algorithms.PlantedClique
