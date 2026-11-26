/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.WidthThree

open Cslib.Complexity Cslib.Complexity.QuantifiedSAT.WidthThree
open Cslib.Logic.PL

example : SigmaPComplete 1 encoding (SigmaWidthThree 1) := sigmaWidthThree_complete (by decide)
example : SigmaPComplete 2 encoding (SigmaWidthThree 2) := sigmaWidthThree_complete (by decide)
example : SigmaPComplete 3 encoding (SigmaWidthThree 3) := sigmaWidthThree_complete (by decide)
example : PiPComplete 3 encoding (PiWidthThree 3) := piWidthThree_complete (by decide)
example : PiPComplete 4 encoding (PiWidthThree 4) := piWidthThree_complete (by decide)

-- An empty term is true even with no bound variables.
example : ([[], []], [[]]) ∈ SigmaWidthThree 2 := by
  simp [SigmaWidthThree, prenexAt, PrenexQBF.SigmaSAT, PrenexQBF.WellFormed, matrix,
    PrenexQBF.formula, QBF.blocks, QBF.ofCNF, QBF.ofClause, DNF.negate, Term.negate, QBF.eval,
    QBF.exs, QBF.alls, QBF.freeVars, QBF.quantifierFree_bot]

#print axioms sigmaWidthThree_complete
#print axioms piWidthThree_complete
#print axioms exists_normalFormReduction
#print axioms iterate_not_true_eq
#print axioms widthThree_blocks_eval
#print axioms widthThreeCNF_blocks_eval
