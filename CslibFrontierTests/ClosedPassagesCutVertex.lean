/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (closed passages through prescribed darts)

import CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.CutVertex

/-! A positive-length path and an empty path both close through their specified indexed darts. -/
set_option linter.privateModule false

namespace CslibFrontierTests.ClosedPassagesCutVertex

open Cslib.Complexity Cslib.Complexity.Graph

private abbrev triangle : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 0)]⟩

private abbrev a : Dart triangle := (0, false)
private abbrev b : Dart triangle := (2, true)

private theorem a_other : a.reverse.vertex ≠ 0 := by decide
private theorem b_other : b.reverse.vertex ≠ 0 := by decide

private theorem bridge : (triangle.toSimpleGraph.induce {w | w ≠ 0}).Reachable
    ⟨a.reverse.vertex, a_other⟩ ⟨b.reverse.vertex, b_other⟩ :=
  SimpleGraph.Adj.reachable (Graph.toSimpleGraph_adj.mpr (by decide))

example : ∃ (x : Fin 3 → Bool) (P : ClosedPassages triangle x) (i : Fin P.count),
    P.dart i false = a ∧ P.dart i true = b ∧ x 0 = true ∧ x 2 = true ∧
      (∀ j, (P.dart j false).vertex = 0 → j = i) ∧
      (triangle.toSimpleGraph.induce {w | w ≠ 0}).Reachable
        ⟨a.reverse.vertex, a_other⟩ ⟨b.reverse.vertex, b_other⟩ := by
  obtain ⟨x, P, i, ha, hb, hunique, hreach⟩ :=
    ClosedPassages.exists_through_darts_of_reachable a b rfl rfl (by decide) a_other b_other bridge
  have hx₀ : x 0 = true := by simpa only [ha] using P.supported i false
  have hx₂ : x 2 = true := by simpa only [hb] using P.supported i true
  exact ⟨x, P, i, ha, hb, hx₀, hx₂, hunique, hreach b.reverse hx₂ b_other⟩

private abbrev parallel : Graph := ⟨[0, 1], [(0, 1), (0, 1)]⟩

private abbrev c : Dart parallel := (0, false)
private abbrev d : Dart parallel := (1, false)

private theorem c_other : c.reverse.vertex ≠ 0 := by decide
private theorem d_other : d.reverse.vertex ≠ 0 := by decide

example : ∃ (x : Fin 2 → Bool) (P : ClosedPassages parallel x) (i : Fin P.count),
    P.dart i false = c ∧ P.dart i true = d := by
  have here : (parallel.toSimpleGraph.induce {w | w ≠ 0}).Reachable
      ⟨c.reverse.vertex, c_other⟩ ⟨d.reverse.vertex, d_other⟩ := .rfl
  obtain ⟨x, P, i, hc, hd, _, _⟩ :=
    ClosedPassages.exists_through_darts_of_reachable c d rfl rfl (by decide) c_other d_other here
  exact ⟨x, P, i, hc, hd⟩

end CslibFrontierTests.ClosedPassagesCutVertex
