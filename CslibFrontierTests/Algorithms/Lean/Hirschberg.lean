/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.EditDistance.Hirschberg

/-!
# Hirschberg reconstruction on directed costs and tied longest common subsequences
-/

namespace CslibFrontierTests.Hirschberg

open Cslib.Algorithms.Lean.EditDistance

private def directed : Costs Nat where
  del a := a + 5
  ins b := b + 1
  sub a b := if a = b then 0 else 20

-- Transposing the short and long inputs must also transpose prices and emitted operations.
#guard (hirschbergAlign directed [1] [0, 2, 0]).cost directed == 11
#guard (hirschbergAlign directed [0, 2, 0] [1]).cost directed == 19
#guard (hirschbergAlign directed [] [1, 2]).tgt == [1, 2]

-- Either tied solution is acceptable. A repeated match must still be used at most once.
example : (hirschbergLCS [0, 1, 0] [1, 0, 1]).length = 2 := by
  rw [(hirschbergLCS_spec _ _).2.2]
  decide

end CslibFrontierTests.Hirschberg
