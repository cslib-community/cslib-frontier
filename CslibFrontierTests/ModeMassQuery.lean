/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.ModeMassQuery

open Cslib.SparseModeTuple Cslib.Circuits.Frontier.ModeMassQuery Cslib.BitString

private def rows : List Row := [⟨7, ⟨4, 1⟩, [⟨0, 99⟩]⟩]

-- The three forward pairs contribute 6, 9 and 3 after clipping. The fourth is reversed.
example : (equivFin _ (result 3 2 rows) : ℕ) = 18 := by
  rw [val_result]
  decide

-- Equality fails the strict test, and the next budget succeeds on exactly the same table.
example : ¬(equivFin _ (result 610 (encode rows).length rows) : ℕ) < 610 ∧
    (equivFin _ (result 611 (encode rows).length rows) : ℕ) < 611 := by
  rw [val_result_lt_iff, val_result_lt_iff]
  decide

example : (equivFin _ (result 0 0 []) : ℕ) = 0 := by
  rw [val_result]
  decide
