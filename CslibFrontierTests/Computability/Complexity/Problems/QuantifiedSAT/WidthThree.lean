/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.WidthThree

open Cslib.Complexity Cslib.Complexity.QuantifiedSAT.WidthThree
open Cslib.Logic.PL

example : SigmaPComplete 2 encoding DNF3Two := dnf3Two_complete

-- An empty term is true even with no bound variables.
example : ([[], []], [[]]) ∈ DNF3Two := by
  simp [DNF3Two, DNF2, PrenexQBF.SigmaSAT, PrenexQBF.WellFormed, prenex, matrix,
    PrenexQBF.formula, QBF.blocks, QBF.ofCNF, QBF.ofClause, DNF.negate, Term.negate, QBF.eval,
    QBF.exs, QBF.alls, QBF.freeVars, QBF.quantifierFree_bot]

#print axioms dnf3Two_complete
#print axioms compile3DNF_correct
#print axioms polytime_compile3DNF
#print axioms widthThree_blocks_eval
#print axioms widthThreeCNF_blocks_eval
