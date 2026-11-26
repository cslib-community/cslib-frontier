/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.AndOr
import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Numbering.Rows
import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Template

/-! A legal one-letter symbol change lifts through the actual standard AND/OR implementation. -/

open Cslib.Complexity.NCL

private def compatibility : Digraph (Fin 2) := ⟨fun _ _ => True⟩

private instance : DecidableRel compatibility.Adj := fun _ _ => isTrue trivial

example : (HWord.AndOr.graph (n := 0) compatibility (by decide)).WellFormed :=
  HWord.AndOr.wellFormed compatibility (by decide)

example :
    (HWord.AndOr.graph (n := 1) compatibility (by decide)).Reachable
      (HWord.AndOr.orientation compatibility (by decide) (fun _ => 0))
      (HWord.AndOr.orientation compatibility (by decide) (fun _ => 1)) := by
  apply (HWord.AndOr.reachable_orientation_iff compatibility (by decide) _ _).mpr
  exact HWord.reachable_of_eq_off (fun _ _ _ => trivial) (fun _ _ _ => trivial) 0
    (fun j hj => False.elim (hj (Fin.eq_zero j)))
