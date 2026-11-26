/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: local-only (tests of CslibFrontier.Foundations.Data.BitString.Pad10Star)

public import CslibFrontier.Foundations.Data.BitString.Pad10Star

/-! # Tests for `Cslib.BitString.pad10star` and `Cslib.BitString.toBlocks` -/

namespace CslibFrontierTests.BitString.Pad10Star

open Cslib Cslib.BitString

-- 1. Padding: a `1`, then zeros up to the next multiple of the block length; a list of whole
-- blocks gets one more block.
example : pad10star 3 [true] = [true, true, false] := rfl

example : pad10star 2 [false, true] = [false, true, true, false] := rfl

example : (pad10star 3 [false, true, true, false]).length = 6 := length_pad10star (by decide) _

-- 2. Cutting drops an incomplete last block, and there are no blocks of width `0`.
example : toBlocks 2 [true, false, false, true, true] = [![true, false], ![false, true]] := by
  decide

example (l : List Bool) : toBlocks 0 l = [] := List.eq_nil_of_length_eq_zero (by simp)

-- 3. Block `k` of the padded list, read from the list itself: there are `L.length / r + 1`
-- blocks, and the zeros of the padding are the default of `getD`.
example {r : ℕ} (hr : 0 < r) (L : List Bool) (k : ℕ) :
    (toBlocks r (pad10star r L))[k]? =
      if k < L.length / r + 1 then some fun i : Fin r => (L ++ [true]).getD (k * r + i) false
      else none := by
  simp only [getElem?_toBlocks, length_pad10star_div hr, getD_pad10star]

-- 4. The padded list is the concatenation of its blocks, and it determines the list.
example {r : ℕ} (hr : 0 < r) (L : List Bool) :
    (toBlocks r (pad10star r L)).flatMap List.ofFn = pad10star r L :=
  flatMap_ofFn_toBlocks (dvd_length_pad10star hr L)

example : toBlocks 2 (pad10star 2 [true]) ≠ toBlocks 2 (pad10star 2 [true, true]) :=
  fun h => by simpa using toBlocks_pad10star_injective (by decide) h

end CslibFrontierTests.BitString.Pad10Star
