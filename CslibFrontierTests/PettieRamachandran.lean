/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.Restrict
meta import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.Restrict

/-!
# Small instances of optimal comparison-tree synthesis

A triangle needs two comparisons to find its heaviest edge. A forest needs none.
A pair of parallel edges needs one comparison, even with sparse original labels.
-/

open Cslib Cslib.Multigraph Cslib.Query
open scoped Sym2

private def triangle (e : Fin 3) : Sym2 (Fin 3) :=
  if e = 0 then s(0, 1) else if e = 1 then s(0, 2) else s(1, 2)

#guard optimalMSFComparisons triangle == 2
#guard (optimalMSFProgram triangle).eval (LEQuery.keyOracle Fin.val) == {0, 1}

private def path (e : Fin 2) : Sym2 (Fin 3) := if e = 0 then s(0, 1) else s(1, 2)

#guard optimalMSFComparisons path == 0
#guard optimalMSFComparisons (fun _ : Fin 2 => (s(0, 0) : Sym2 (Fin 1))) == 0

private def parallel (_ : ℕ) : Sym2 ℕ := s(100, 900)

#guard (optimalMSFOn parallel {9, 71}).eval (LEQuery.keyOracle (fun n : ℕ => -(n : ℤ))) == {71}
#guard (optimalMSFOn parallel {9, 71}).countQueries (LEQuery.keyOracle id) == 1
