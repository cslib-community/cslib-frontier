/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PolyTime.Plurality

/-! Binary natural outputs use the plurality certificate, including ties and empty lists. -/

set_option linter.privateModule false

open Cslib Turing.MultiTapeTM

example : ComputableInPolyTime (ProbComp.plurality (0 : ℕ)) (encList encNat) encNat :=
  ComputableInPolyTime.plurality encNat 0

example : ProbComp.plurality (0 : ℕ) [11, 40, 40, 11] = 11 := by decide

example : ProbComp.plurality (40 : ℕ) [] = 40 := by decide
