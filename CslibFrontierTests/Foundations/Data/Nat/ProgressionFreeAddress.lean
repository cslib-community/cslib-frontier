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

example : encode 2 ![1, 0] < 48 := by
  exact encode_bound _ (by decide)

example (x y : Fin 2 → ℕ) (hx : ∀ i, x i < 2) (hy : ∀ i, y i < 2)
    (h : encode 2 x + encode 2 y = 34) : x 0 = 1 ∧ y 1 = 0 := by
  have hmid : encode 2 x + encode 2 y = encode 2 ![1, 0] + encode 2 ![1, 0] := h
  obtain ⟨rfl, rfl⟩ := encode_midpoint hx hy (by decide) hmid
  decide

example (x : Fin (2 * 2) → ℕ) (hx : ∀ i, x i < 2)
    (h : encodeBlocks (m := 2) (w := 2) 2 x = ![20, 17]) : x 2 = 1 := by
  have heq : encodeBlocks (m := 2) (w := 2) 2 x =
      encodeBlocks (m := 2) (w := 2) 2 ![0, 1, 1, 0] :=
    h.trans (by decide)
  exact (congrFun (encodeBlocks_injOn hx (by decide) heq) 2).trans (by decide)

example : encode 0 (![] : Fin 0 → ℕ) = 0 := by decide
example : encode 1 ![0] = 0 := by decide
example : encode 1 ![2] % 2 ≠ Behrend.map 2 ![2] := by decide
