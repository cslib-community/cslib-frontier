/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.Algorithm
import CslibFrontier.Probability.PlantedClique.Model
meta import CslibFrontier.Algorithms.PlantedClique.Algorithm
meta import CslibFrontier.Probability.PlantedClique.Model

/-!
# Concrete runs of planted-clique recovery

These examples execute the integer power search, coordinate selection, and degree cleanup on
small graphs. A six-clique with two isolated outside vertices is recovered both when its
vertices are consecutive and when they are interspersed with outside vertices. The examples do
not meet the asymptotic theorem's conservative size hypothesis; they are direct execution
checks, not applications of that theorem.

The small graph with vertex zero outside the clique records the behavior outside the theorem's
promise: the first growing orbit need not approximate the planted set there. Empty inputs and
a search with no growing vector also have well-defined results.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PlantedClique

open Cslib.Algorithms.PlantedClique Cslib.Probability.PlantedClique

-- The three full runs are executable regression checks.
set_option linter.hashCommand false

private def consecutiveClique : Finset (Fin 8) := {0, 1, 2, 3, 4, 5}

private def interspersedClique : Finset (Fin 8) := {0, 1, 3, 4, 6, 7}

private def outsiderFirstClique : Finset (Fin 8) := {1, 2, 3, 4, 6, 7}

/-- Three stored matrix-vector multiplications preserve both magnitude and sign. -/
example : powerColumnVector (fun i j : Fin 2 => if i = j then 1 else -1) 3 0 =
    #v[(4 : ℤ), -4] := by
  decide +kernel

-- Consecutive planted vertices, with no edges touching either outside vertex.
#guard recover (sample consecutiveClique (fun _ => false)) 6 == consecutiveClique

-- Recovery depends on the scores and graph, rather than selecting the first six labels.
#guard recover (sample interspersedClique (fun _ => false)) 6 == interspersedClique

-- Below the theorem's size promise, a growing orbit can point away from the clique.
#guard recover (sample outsiderFirstClique (fun _ => false)) 6 == ∅

/-- The empty input is total even when the requested size exceeds its number of vertices. -/
example : recover (sample (∅ : Finset (Fin 0)) (fun _ => false)) 6 = ∅ := by
  decide +kernel

/-- A zero matrix has no nonzero growing vector, so the search follows its default branch. -/
example : growingColumn? (signedAdjacency (sample (∅ : Finset (Fin 1)) (fun _ => false))) 1 =
    none := by
  decide +kernel

/-- The default branch and cleanup also give a total answer on a single isolated vertex. -/
example : recover (sample (∅ : Finset (Fin 1)) (fun _ => false)) 1 = ∅ := by
  simp [recover, SimpleGraph.recoverCliqueByDegree, sample]

end CslibFrontierTests.PlantedClique
