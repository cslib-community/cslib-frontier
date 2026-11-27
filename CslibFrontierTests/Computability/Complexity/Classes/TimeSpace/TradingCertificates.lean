/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.TimeSpace.TradingCertificates

set_option linter.privateModule false

open Cslib.Complexity

private def profiles : List TradingProfile := [.spaceTwelve, .two 8, .nt 11]

example : searchTradingChain 11 8 3 profiles (.nt 12) (.nt 11) =
    some [.spaceTwelve, .two 8, .nt 11] := by
  simp [searchTradingChain, profiles, tradingCandidates, checkTradingChain, tradingEdge,
    List.flatMap, List.find?]

example : searchTradingChain 7 5 3 profiles (.nt 12) (.nt 11) = none := by
  simp [searchTradingChain, profiles, tradingCandidates, checkTradingChain, tradingEdge,
    List.flatMap, List.find?]

example : searchTradingChain 11 8 2 profiles (.nt 12) (.nt 11) = none := by
  simp [searchTradingChain, profiles, tradingCandidates, checkTradingChain, tradingEdge,
    List.flatMap, List.find?]

example : tradingEdge 11 0 (.two 8) (.nt 11) = false := by decide
