/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.ByteString
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Fixed byte pairs

This module supplies the two-block convenience wrapper used by hash functions with a `2n`-byte
input. General indexed block concatenation is already provided, for every carrier, by
`Cslib.BitString.blocksEquiv.symm`.

## Main definitions

* `Cslib.Crypto.FixedBytes.pairBlocks`: concatenate two blocks of the same width.

## Main results

* `Cslib.Crypto.FixedBytes.pairBlocks_left`, `pairBlocks_right`: the two-block specialization
  agrees with its left and right inputs.

## References

This is general byte-string infrastructure rather than a formalization of an external result.
-/

public section

namespace Cslib.Crypto.FixedBytes

/-- Concatenate two equal-width byte strings as consecutive blocks, using `FixedBytes.append`. -/
def pairBlocks {width : ℕ} (left right : FixedBytes width) : FixedBytes (2 * width) :=
  fun i => FixedBytes.append left right ⟨i.val, by omega⟩

/-- The first block of a two-block concatenation is its left input. -/
@[simp] theorem pairBlocks_left {width : ℕ} (left right : FixedBytes width)
    (offset : Fin width) :
    pairBlocks left right (finProdFinEquiv (0, offset)) = left offset := by
  change FixedBytes.append left right (Fin.castAdd width offset) = left offset
  exact FixedBytes.append_left left right offset

/-- The second block of a two-block concatenation is its right input. -/
@[simp] theorem pairBlocks_right {width : ℕ} (left right : FixedBytes width)
    (offset : Fin width) :
    pairBlocks left right (finProdFinEquiv (1, offset)) = right offset := by
  change FixedBytes.append left right (Fin.natAdd width offset) = right offset
  exact FixedBytes.append_right left right offset

end Cslib.Crypto.FixedBytes
