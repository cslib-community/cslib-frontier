/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.ACC0.CodeLength

/-!
# Tests for the fan-in normalization of `AC⁰[q]` circuits

Concrete checks for `CslibFrontier.Computability.Circuit.Boolean.ACC0.CodeLength`: a `MOD_2` gate
reading a wire four times reads it no times after normalization, and five times becomes once.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Boolean.ACC0.CodeLength

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

example : (Unbounded.modWires 2 ![4] ![(Wire.input 0 : Wire 1 0)]).length = 0 := by
  simp [Unbounded.modWires]
example : (Unbounded.modWires 2 ![5] ![(Wire.input 0 : Wire 1 0)]).length = 1 := by
  simp [Unbounded.modWires]

end CslibFrontierTests.Computability.Circuit.Boolean.ACC0.CodeLength
