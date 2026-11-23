/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.WordRAM.TwoSAT

register_result "twosat-linear-wordram" where
  title := "Aspvall–Plass–Tarjan linear-time 2-SAT decision and witness construction on the \
    word RAM"
  topic := "algorithms"
  sources := [
    { paper := AspvallPlassTarjan1979, theorem := "Theorem 1 and \"Two-satisfiability algorithm\"",
      locator := "1979 journal scan, printed p. 121 steps 1(i)–(ii) and p. 122" }
  ]
  theorems := [
    Cslib.Algorithms.WordRAM.TwoSAT.Instance.inputFits_encode,
    Cslib.Algorithms.WordRAM.TwoSAT.decodeAnswer_answerWords,
    Cslib.Algorithms.WordRAM.TwoSAT.answerWords_eq_nil_iff,
    Cslib.Algorithms.WordRAM.TwoSAT.eval_of_decodeAnswer_eq_some,
    Cslib.Algorithms.WordRAM.TwoSAT.program_spec,
    Cslib.Algorithms.WordRAM.TwoSAT.computesListInTime_program
  ]
  scope := "Standard-basis Word-RAM realization (Cslib.WordRAM.Basis.standard) of the \
    Aspvall–Plass–Tarjan 2-SAT algorithm on formulas φ : CNF (Fin n) encoded as \
    Instance.encode ([n, |φ|] ++ φ.flatMap (encodeClauseBy Fin.val)). At every word width w \
    satisfying Fits w G.wordBound (32 * (n + |φ| + totalLits + 1)), program halts within \
    512 * (n + |φ| + 1) instructions (ExecutesList / Program.ComputesListInTime) using CSR \
    implication and transpose graphs and an explicit iterative DFS stack in linear memory, \
    outputting [] iff φ violates width ≤ 2 or is unsatisfiable and \
    1 :: [(σ 0).toNat, …, (σ (n - 1)).toNat] for a satisfying assignment σ otherwise. Lean's \
    Kosaraju SCC pass and this certified Word-RAM implementation and instruction bound are this \
    formalization's own refinement; the paper uses Tarjan's SCC algorithm and also studies \
    quantified 2-CNF."
