/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.SAT.SingleTape

set_option linter.privateModule false

open Cslib.Complexity Cslib.Turing

example {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}
    {ι : Bool → Symbol} {yes : Symbol}
    (h : tm.DecidesByHeadInTime ι (encCNF '' SAT) yes (fun n => n + 1)) : False :=
  singleTape_sat_no_linear (C := 1) (by simpa using h)
