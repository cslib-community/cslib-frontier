/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Closure
import CslibFrontier.Computability.Complexity.Problems.STCON.Completeness

/-! Tests for the closure of `NL` under logspace reductions, union and intersection, on `STCON`
and its complement. With the reduction of every problem in `NL` to `STCON`, closure under
reductions characterizes `NL` as the problems that reduce to `STCON`, for every encoding. -/

namespace CslibFrontierTests.NLClosure

open Cslib.Complexity

/-- `NL` is exactly the class of problems that reduce to `STCON` in logarithmic space. -/
example {α : Type} {enc : α ↪ List Bool} (A : Set α) :
    A ∈ NL enc ↔ LogSpaceReducible enc encSTCON A STCON :=
  ⟨STCON.logSpaceReducible_of_mem_NL, fun h => h.mem_NL STCON.mem_NL⟩

/-- A union and an intersection of `NL` problems with different witnessing machines. -/
example : STCON ∪ STCONᶜ ∈ NL encSTCON := union_mem_NL STCON.mem_NL STCON.compl_mem_NL

example : STCON ∩ STCONᶜ ∈ NL encSTCON := inter_mem_NL STCON.mem_NL STCON.compl_mem_NL

/-- Hardness for `NL` and membership place `NL` in itself, through `STCON`. -/
example {α : Type} (enc : α ↪ List Bool) : NL enc ⊆ NL enc :=
  STCON.logSpaceHard.subset_NL STCON.mem_NL enc

end CslibFrontierTests.NLClosure
