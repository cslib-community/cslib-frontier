/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.Permanent.Nonnegative
import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT

/-! Checked clients of the support table and of Goldreich Exercise 6.25. -/

set_option linter.privateModule false

namespace Cslib.Complexity

open Cslib.Logic.PL

-- The support marks the non-zero entries, keeping ragged rows.
example : supportTable [[0, 2], [-1]] = [[false, true], [true]] := by decide

-- Non-negative tables: the anti-diagonal table has a non-zero permanent and so has its support.
example :
    IntPermanent [[0, 2], [3, 0]] ≠ 0 ↔ ZeroOnePermanent (supportTable [[0, 2], [3, 0]]) ≠ 0 :=
  intPermanent_ne_zero_iff_zeroOnePermanent_supportTable (by decide)

-- Without non-negativity the support can have a matching while the permanent cancels:
-- `perm [[1, 1], [1, -1]] = 1 * (-1) + 1 * 1 = 0`, while its support is the all-ones table.
example :
    IntPermanent [[1, 1], [1, -1]] = 0 ∧ ZeroOnePermanent (supportTable [[1, 1], [1, -1]]) = 2 := by
  decide

/-- Exercise 6.25 applied to the library's Proposition 6.21: unless `P = NP`, Goldreich's matrices
(`c = 12`) have a negative entry on some 3CNF formula. -/
example (h : P encCNF ≠ NP encCNF) :
    ∃ φ : CNF ℕ, (∀ C ∈ φ, C.length ≤ 3) ∧ ∃ row ∈ cnfToPermanentTable φ, ∃ x ∈ row, x < 0 := by
  by_contra hneg
  push Not at hneg
  refine exercise_6_25 h ⟨12, by norm_num, {x | 0 ≤ x}, fun _ hx => hx, cnfToPermanentTable,
    computableInPolyTime_cnfToPermanentTable, fun φ hφ => ⟨hneg φ hφ, ?_⟩⟩
  rw [intPermanent_cnfToPermanentTable]

end Cslib.Complexity
