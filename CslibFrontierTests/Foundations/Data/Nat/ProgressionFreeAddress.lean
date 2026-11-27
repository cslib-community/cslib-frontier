/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.Data.Nat.ProgressionFreeAddress

set_option linter.privateModule false

open Cslib.ProgressionFreeAddress

example : encode 2 ![1, 0] = 17 := by decide
example : encode 2 ![0, 1] = 20 := by decide
example : encodeBlocks (m := 2) (w := 2) 2 ![0, 1, 1, 0] 1 = 17 := by decide
