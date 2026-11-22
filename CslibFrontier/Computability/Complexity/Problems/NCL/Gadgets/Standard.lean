/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Prim
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CheckGens
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Incidence

/-!
# Standard primitive cells

## Main definitions

* `Cslib.Complexity.NCL.Prim.checkStandard`: AND/OR vertices with distinct port edges and
  consistent colored boundary incidences.

## Main results

* `Cslib.Complexity.NCL.Diagram.checkGens_checkStandard_iff`: recover the three component checks.
-/

public section

namespace Cslib.Complexity.NCL

/-- Check AND/OR shape, distinct port edges, and consistent colored boundary incidences. -/
@[expose] def Prim.checkStandard {a b : List Color} (g : Prim a b) : Bool :=
  g.all Vertex.checkAndOr && (g.all Vertex.checkLoopFree && Prim.interp.checkPorts g)

/-- A standard-cell check is the conjunction of its three structural checks. -/
theorem Diagram.checkGens_checkStandard_iff {a b : List Color} (D : Diagram Prim a b) :
    D.checkGens Prim.checkStandard = true ↔
      D.checkGens (fun g => g.all Vertex.checkAndOr) = true ∧
      D.checkGens (fun g => g.all Vertex.checkLoopFree) = true ∧
      D.checkGens Prim.interp.checkPorts = true := by
  change D.checkGens (fun g => g.all Vertex.checkAndOr &&
    (g.all Vertex.checkLoopFree && Prim.interp.checkPorts g)) = true ↔ _
  rw [Diagram.checkGens_and, Diagram.checkGens_and]
  simp only [Bool.and_eq_true]

end Cslib.Complexity.NCL
