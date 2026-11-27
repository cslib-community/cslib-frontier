/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.Lean.CDCL.Luby

/-!
# The Luby sequence

The kernel checks the first 63 terms of the Luby sequence with base 2 against its recursive
description, and the first terms with base 3.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.Lean.CDCL.Luby

open Cslib.Algorithms.Lean.CDCL

/-- The first terms, with base 2. -/
example : (List.range 15).map (luby 2) = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8] := by
  decide

/-- The recursive description: the complete subsequence of length `2 ^ (k + 1) - 1` is two copies
of the one of length `2 ^ k - 1`, then `2 ^ k`; checked up to length 63. -/
def lubyRef : ℕ → List ℕ
  | 0 => []
  | k + 1 => lubyRef k ++ lubyRef k ++ [2 ^ k]

example : (List.range 63).map (luby 2) = lubyRef 6 := by decide

/-- With base 3. -/
example : (List.range 7).map (luby 3) = [1, 1, 3, 1, 1, 3, 9] := by decide

end CslibFrontierTests.Algorithms.Lean.CDCL.Luby
