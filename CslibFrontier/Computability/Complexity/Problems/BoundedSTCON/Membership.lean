/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.BoundedSTCON.LogSpace
public import CslibFrontier.Computability.Complexity.Problems.STCON.Completeness
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Closure

/-!
# Length-bounded directed connectivity is in NL

Exercise 5.19 of the January 2007 draft of [Goldreich2008] (printed p. 197, PDF p. 81)
asks whether a directed graph has a path of at most a given length between two designated
vertices. `BoundedSTCON.mem_NL` proves membership in `NL` for every adjacency-matrix instance
and every natural bound in binary (`encBoundedSTCON`). A negative integer bound, if admitted,
is always a no-instance; here the length parameter is a natural number. Zero-length paths
are allowed, exactly when the terminals coincide.

The reduction caps the bound at the vertex count, adds one layer for each allowed transition,
and pads a shorter path with stationary steps. It writes the existing `encSTCON` format using
polynomially bounded counters. Thus `logSpaceReducible_STCON` and `STCON.mem_NL` imply
membership by closure of `NL` under logarithmic-space reductions. Space counts visited work
cells, with read-only input and write-only output; the native machine may have any fixed finite
number of work tapes.
-/

public section
namespace Cslib.Complexity.BoundedSTCON

/-- Length-bounded connectivity reduces to directed connectivity through the capped layered
adjacency matrix. -/
theorem logSpaceReducible_STCON :
    LogSpaceReducible encBoundedSTCON encSTCON BoundedSTCON STCON :=
  ⟨BoundedSTCONInstance.layered, BoundedSTCONInstance.computableInLogSpace_layered,
    fun I => I.layered_mem_iff.symm⟩

/-- Bounded-length directed connectivity is in `NL`, for adjacency-matrix graphs and binary
natural length bounds (Goldreich's January 2007 draft, Exercise 5.19). -/
theorem mem_NL : BoundedSTCON ∈ NL encBoundedSTCON :=
  logSpaceReducible_STCON.mem_NL STCON.mem_NL

end Cslib.Complexity.BoundedSTCON
