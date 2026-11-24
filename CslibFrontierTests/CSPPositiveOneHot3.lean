/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.Problems.CSP.OneHot3

/-!
The adapter keeps indexed repeated clauses and repeated variable occurrences. Exactly one
true occurrence is different from exactly one true distinct variable: the repeated scope
below rejects an assignment making its repeated variable true.
-/

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP

public section

namespace CslibFrontierTests.CSPPositiveOneHot3

/-- Two equal positive clauses, each retaining a repeated literal occurrence. -/
def positive : CNF ℕ :=
  [[(91, true), (91, true), (4, true)], [(91, true), (91, true), (4, true)]]

example : OneHot3.ofCNF positive =
    [⟨(), [91, 91, 4]⟩, ⟨(), [91, 91, 4]⟩] := rfl

example : incidenceGraph (OneHot3.ofCNF positive) = SAT.incidenceGraph positive := by
  apply OneHot3.incidenceGraph_ofCNF
  decide

example : (OneHot3.ofCNF positive).eval OneHot3.sem (fun v => v == 91) = false := by decide

example : (OneHot3.ofCNF positive).eval OneHot3.sem (fun v => v == 4) = true := by decide

example : OneHot3.sem () [true, false, false] = OneHot3.sem () [false, true, false] := by decide

example : (OneHot3.ofCNF [[]]).eval OneHot3.sem (fun _ => false) = false := by decide

example : (OneHot3.ofCNF []).eval OneHot3.sem (fun _ => false) = true := by decide

end CslibFrontierTests.CSPPositiveOneHot3
