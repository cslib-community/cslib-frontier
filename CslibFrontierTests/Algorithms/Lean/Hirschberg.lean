/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.EditDistance.Hirschberg
meta import CslibFrontier.Algorithms.Lean.EditDistance.Hirschberg

/-!
# Hirschberg reconstruction on directed costs and tied longest common subsequences
-/

-- Evaluate the compiled reconstruction on concrete input words.
set_option linter.hashCommand false

-- This test module exports no library declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Hirschberg

open Cslib.Algorithms.Lean.EditDistance

private def directionalCosts : Costs Bool where
  del _ := 4
  ins _ := 1
  sub a b := if a == b || !a then 0 else 8

-- Swapping the two words changes the true optimum. The first case transposes the DP orientation.
#guard
  let s := hirschbergAlign directionalCosts [false] [true, true, true]
  s.src == [false] && s.tgt == [true, true, true] && s.cost directionalCosts == 2

#guard
  let s := hirschbergAlign directionalCosts [true, true, true] [false]
  s.src == [true, true, true] && s.tgt == [false] && s.cost directionalCosts == 13

-- Width zero and a long single-column alignment exercise the degenerate subproblems.
#guard hirschbergAlign directionalCosts [] [true, false] == [.ins true, .ins false]
#guard
  let s := hirschbergAlign directionalCosts (List.replicate 32 false) [true]
  s.src.length == 32 && s.tgt == [true] && s.cost directionalCosts == 124

-- Either tied solution is acceptable. A repeated match must still be used at most once.
example : (hirschbergLCS [0, 1, 0] [1, 0, 1]).length = 2 := by
  rw [(hirschbergLCS_spec _ _).2.2]
  decide

end CslibFrontierTests.Hirschberg
