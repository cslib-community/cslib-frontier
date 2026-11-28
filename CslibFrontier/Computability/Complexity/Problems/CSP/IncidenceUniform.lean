/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.IncidencePrefix
import CslibFrontier.Foundations.Data.List.Counting

/-!
# Exact incidence indices for uniform-width constraint bodies

When every scope has the same width, the original occurrence index is the row width times
the constraint position plus its argument position. This specializes the existing prefix
formula without identifying repeated variables or repeated constraints. The uniform-width
hypothesis describes a source template; it places no bound on a target constraint language.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- Equal scope widths give their literal row-major incidence positions. Parallel
occurrences retain separate positions, including when their variable names coincide. -/
theorem incidenceEdgeIndex_eq_mul_add (k : ℕ)
    (hw : ∀ row ∈ F, row.scope.length = k) (o : F.Occurrence) :
    incidenceEdgeIndex o = k * o.1.val + o.2.val := by
  rw [incidenceEdgeIndex_eq_prefix, Cslib.Logic.PL.CSP.vars,
    List.length_flatMap_of_forall_length_eq (fun row hrow =>
      hw row (List.mem_of_mem_take hrow)), List.length_take,
    Nat.min_eq_left o.1.isLt.le, Nat.mul_comm]

/-- The actual listed edge count is the width times the actual row count. No variable
label or maximum variable index occurs in this bound. -/
theorem length_edges_incidenceGraph_eq_mul (k : ℕ)
    (hw : ∀ row ∈ F, row.scope.length = k) :
    (incidenceGraph F).edges.length = k * F.length := by
  rw [length_edges_incidenceGraph]
  calc
    _ = (F.map (fun _ => k)).sum := by
      apply congrArg List.sum
      exact List.map_congr_left hw
    _ = k * F.length := by simp [List.map_const', List.sum_replicate, Nat.mul_comm]

end Cslib.Complexity.CSP
