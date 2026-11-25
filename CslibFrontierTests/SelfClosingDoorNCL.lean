/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.NCLProgram
import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Step
import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Incidence

/-! A loop reversal and malformed-target rejection through the NCL register compiler. -/

open Cslib.Complexity Cslib.Complexity.NCL
open Cslib.Complexity.SelfClosingDoor.RegisterProgram

set_option linter.privateModule false

namespace CslibFrontierTests.SelfClosingDoorNCL

private def loopGraph : AndOrGraph :=
  ⟨[.or ⟨0, false⟩ ⟨0, true⟩ ⟨1, false⟩,
    .or ⟨2, false⟩ ⟨2, true⟩ ⟨1, true⟩], 3⟩

private theorem valid : loopGraph.Valid :=
  (AndOrGraph.checkValid_eq_true_iff _).1 (by decide +kernel)

private def source : AndOrNCL.Instance := ⟨loopGraph, [false, false, false], [true, false, false]⟩

-- Reversing the loop changes which of its two incidences supplies the first vertex.
private theorem loop_step : loopGraph.graph.Step
    (loopGraph.config source.initial) (loopGraph.config source.target) :=
  ((AndOrGraph.checkStep_eq_true_iff _ valid.1 _ _).1 (by decide +kernel)).2.2

example : (NCLCompiler.compile source).Accepts :=
  (NCLCompiler.compile_accepts_iff source).2
    ⟨valid, rfl, rfl, loop_step.legal_left, .single loop_step⟩

example : ¬ (NCLCompiler.compile {source with target := [false, false]}).Accepts := by
  rw [NCLCompiler.compile_accepts_iff]
  rintro ⟨_, _, hlen, _⟩
  change 2 = 3 at hlen
  omega

end CslibFrontierTests.SelfClosingDoorNCL
