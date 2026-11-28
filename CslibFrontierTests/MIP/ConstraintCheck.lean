/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.MIP.ConstraintCheck

/-! Modular final claims and explicitly rejected correction replies. -/

open Cslib.Complexity.MIP

-- No gates with equal zero input and challenge make the first two factors one. With three
-- zero sign bits and corrected one values, the literal factor also equals one modulo three.
example : checkConstraintClaim 3 1 [] [0] [0] [0, 0, 0] 4 ![some 1, some 1, some 1] = true ∧
    checkConstraintClaim 3 1 [] [0] [0] [0, 0, 0] 4 ![some 1, none, some 1] = false ∧
    checkConstraintClaim 3 1 [] [0] [0] [0, 0, 0] 0 ![some 1, some 1, some 1] = false := by
  decide
