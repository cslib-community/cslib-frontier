/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPortRank

open Turing Turing.MultiTapePTM Turing.MultiTapeTM Turing.MultiTapeATM.RootPortRank
open Cslib Cslib.Circuits.Frontier
open RootPredecessorGraph (edgeCount vertexCount)

-- At the complete prefix, the same fixed context counts every row or column port of the group.
example {k q copies a : ℕ} {State : Type} (M : MultiTapePTM k Bool State)
    (input : List Bool) (b σ : ℕ) (code : BlockLetter k State b → Fin copies → Bool)
    (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a)) (i : Fin a)
    (column : Bool) (g : ℕ) :
    (∑ j ∈ Finset.range (edgeCount k q copies), (RootPortContext.predicate k
      (RootPortContext.word (graphInput k q copies σ a seed i column g (edgeCount k q copies)), j)
      ).toNat) =
      (NativeChild.portEdges (RootPortGraph.groups seed i) g (RootPortGraph.ends (q := q) M
        input b σ code) (RootPortGraph.side column)).length := by
  rw [sum_eq_portRank M input b σ code seed i column g le_rfl,
    NativeChild.length_portEdges_eq_portRank]
  simp only [RootPortGraph.ends, List.length_ofFn]
