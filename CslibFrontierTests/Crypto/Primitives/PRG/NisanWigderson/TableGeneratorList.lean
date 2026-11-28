/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.TableGeneratorList

/-!
# Tests for the Nisan–Wigderson generator of a truth table on bit lists

Only cheap facts about `Cslib.Crypto.PRG.NisanWigderson.tableGeneratorList`, since evaluating an
output bit takes arithmetic in a field of degree at least `8192`:

* the output has exactly `m` bits, for concrete and for arbitrary parameters;
* with `m = 0` the output is empty, whatever the table and the seed;
* `tableGeneratorList_take` makes two seeds that agree on the first `tableSeedLength` bits give
  the same output, and shows that an output is determined by a prefix of the seed.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.Primitives.PRG.NisanWigderson.TableGeneratorList

open Cslib.Crypto.PRG.NisanWigderson

/-- The output has `m` bits: `3` bits on a concrete table and seed. -/
example : (tableGeneratorList 5 3 [true, false, false, true] [true, false]).length = 3 := by
  simp [tableGeneratorList]

/-- The output has `m` bits, for every table, seed and size. -/
example (S m : ℕ) (T z : List Bool) : (tableGeneratorList S m T z).length = m := by
  simp [tableGeneratorList]

/-- With no output bits the output is empty. -/
example (S : ℕ) (T z : List Bool) : tableGeneratorList S 0 T z = [] := by
  simp [tableGeneratorList]

/-- Seeds that agree on the first `tableSeedLength` bits give equal outputs. -/
example (S m : ℕ) (T σ₁ σ₂ : List Bool)
    (h : σ₁.take (tableSeedLength (Nat.log 2 T.length) S m) =
      σ₂.take (tableSeedLength (Nat.log 2 T.length) S m)) :
    tableGeneratorList S m T σ₁ = tableGeneratorList S m T σ₂ := by
  rw [← tableGeneratorList_take S m T σ₁, ← tableGeneratorList_take S m T σ₂, h]

end CslibFrontierTests.Crypto.Primitives.PRG.NisanWigderson.TableGeneratorList
