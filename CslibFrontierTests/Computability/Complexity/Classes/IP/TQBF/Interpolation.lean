/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.IP.TQBF.Interpolation

/-!
# Tests for interpolation modulo a prime

Concrete checks for `Cslib.Complexity.QBFProtocol.interpMod` and its building blocks:

* `invMod` is the inverse modulo `5` and `7` of each nonzero residue;
* `interpMod 5 2 [1, 2, 0] = [1, 0, 1]`, the polynomial `1 + X ^ 2`, and the output has `D + 1`
  entries below the modulus;
* missing values read as `0`, and the interpolant of a constant is that constant.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Complexity.Classes.IP.TQBF.Interpolation

open Cslib.Complexity.QBFProtocol

/-- `invMod 5` inverts each nonzero residue. -/
example : (List.range 4).map (fun a => a + 1) = [1, 2, 3, 4] ∧
    ((List.range 4).map fun a => (a + 1) * invMod 5 (a + 1) % 5) = [1, 1, 1, 1] := by decide

/-- `invMod 7 3 = 5`, as `3 * 5 = 15 = 1 (mod 7)`. -/
example : invMod 7 3 = 5 := by decide

/-- The values `1, 2, 0` at `0, 1, 2` modulo `5` interpolate to `1 + X ^ 2`. -/
example : interpMod 5 2 [1, 2, 0] = [1, 0, 1] := by decide

/-- The result has `D + 1` entries below the modulus. -/
example : (interpMod 5 2 [1, 2, 0]).length = 3 ∧ ∀ a ∈ interpMod 5 2 [1, 2, 0], a < 5 := by
  decide

/-- A value list is interpolated at its length: `[0, 1, 4]` is `X ^ 2` modulo `7`. -/
example : interpMod 7 2 [0, 1, 4] = [0, 0, 1] := by decide

/-- Missing values read as `0`: the interpolant of `[1]` at `D = 2` is `(X - 1) (X - 2) / 2`. -/
example : interpMod 5 2 [1] = [1, 1, 3] := by decide

/-- The interpolant of constant values is the constant polynomial. -/
example : interpMod 7 3 [4, 4, 4, 4] = [4, 0, 0, 0] := by decide

end CslibFrontierTests.Computability.Complexity.Classes.IP.TQBF.Interpolation
