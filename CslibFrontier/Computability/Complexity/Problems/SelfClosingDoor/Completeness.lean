/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.PSPACE
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.NCLProgram
import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.RegisterCompiler
import CslibFrontier.Computability.Complexity.Problems.NCL.Hardness

/-!
# Directed symmetric self-closing door reachability is PSPACE-complete

AND/OR constraint logic compiles to a guarded Boolean register program. Each completed
verification cycle reverses one legal source edge, and the accepting branch reads the entire
target configuration. Register doors and private return markers implement these instructions;
diode doors implement their directed wiring. Both concrete compilers are polynomial-time.

This original reduction proves the directed symmetric case of
[AniBosboomDemaineEtAl2021, Corollary 2.4]. The instance is an arbitrary finite door list with
binary location labels, prescribed initial door bits and a target player location. Final door
bits are unrestricted. The finite-configuration space search supplies the matching upper bound.

## Main results

* `polyTimeReducible_AndOrNCL`: the concrete polynomial-time reduction from AND/OR NCL.
* `Reachability_pspaceHard`, `Reachability_pspaceComplete`: hardness and completeness.

## References

* [Ani et al.][AniBosboomDemaineEtAl2021, Corollary 2.4, p. 3:5]
* [Hearn and Demaine][HearnDemaine2005, Theorem 5]
-/

public section

namespace Cslib.Complexity.SelfClosingDoor

/-- AND/OR NCL configuration reachability reduces to directed symmetric door reachability
by the explicit register-program and door-network compilers. -/
theorem polyTimeReducible_AndOrNCL :
    PolyTimeReducible NCL.encAndOrNCL encInstance NCL.AndOrNCL Reachability :=
  ⟨fun x => RegisterProgram.compile (RegisterProgram.NCLCompiler.compile x),
    RegisterProgram.computableInPolyTime_compile.comp
      RegisterProgram.NCLCompiler.computableInPolyTime_compile,
    fun x => ((RegisterProgram.compile_reachability_iff _).trans
      (RegisterProgram.NCLCompiler.compile_accepts_iff x)).symm⟩

/-- Single-player target reachability in an arbitrary network of directed symmetric
self-closing doors is PSPACE-hard under polynomial-time many-one reductions. -/
theorem Reachability_pspaceHard : PSPACEHard encInstance Reachability :=
  NCL.AndOrNCL_pspaceHard.trans polyTimeReducible_AndOrNCL

/-- Single-player target reachability in directed symmetric self-closing door networks is
PSPACE-complete for the explicit door-list encoding with binary location labels. -/
theorem Reachability_pspaceComplete : PSPACEComplete encInstance Reachability :=
  ⟨Reachability_mem_PSPACE, Reachability_pspaceHard⟩

end Cslib.Complexity.SelfClosingDoor
