/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Replacement.Basic
import Mathlib.Data.List.NodupEquivFin

/-!
# Explicit enumeration of private implementation wires

Scan wires in creation order and retain those outside the boundary. This enumeration is
computable and gives exact finite numbering without choosing a finite-type equivalence.

## Main definitions

* `Diagram.Replacement.innerList`: the private wires in creation order.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner

namespace Cslib.Complexity.NCL.Diagram.Replacement

variable {a b : List Color} {g : Prim a b} {H : Diagram Prim a b}
variable (S : OpenSim Prim.interp Prim.interp (gen g) H)

/-- Private wires in creation order, found by a finite boundary-membership test. -/
@[expose] def innerList : List (Inner S) :=
  ((List.finRange (a.length + H.innerCount)).map H.numEquiv.symm).filterMap fun e =>
    if h : e ∉ Set.range S.ι then some ⟨e, h⟩ else none

/-- Every private wire appears in the scan. -/
theorem mem_innerList (e : Inner S) : e ∈ innerList S := by
  apply List.mem_filterMap.mpr
  refine ⟨e.val, List.mem_map.mpr
    ⟨H.numEquiv e, List.mem_finRange _, H.numEquiv.symm_apply_apply e⟩,
    ?_⟩
  simp [e.property]

/-- Creation order lists every private wire at most once. -/
theorem innerList_nodup : (innerList S).Nodup := by
  apply List.Nodup.filterMap
  · intro e f w he hf
    split_ifs at he hf <;>
      simp only [Option.mem_def, Option.some.injEq, reduceCtorEq] at he hf
    exact (congrArg Subtype.val he).trans (congrArg Subtype.val hf).symm
  · exact (List.nodup_finRange _).map H.numEquiv.symm.injective

end Cslib.Complexity.NCL.Diagram.Replacement
