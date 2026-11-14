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
# Fixed byte blocks

This module supplies the typed bridge from an indexed family of equal-width byte blocks to their
row-major concatenation. It lets cryptographic clients retain their block structure while passing
an exact-length byte string to a primitive.

## Main definitions

* `Cslib.Crypto.FixedBytes.flattenBlocks`: concatenate indexed fixed-width blocks.
* `Cslib.Crypto.FixedBytes.pairBlocks`: concatenate two blocks of the same width.

## Main results

* `Cslib.Crypto.FixedBytes.flattenBlocks_apply`: concatenation reads each source block at its
  corresponding row-major coordinate.
* `Cslib.Crypto.FixedBytes.pairBlocks_left`, `pairBlocks_right`: the two-block specialization
  agrees with its left and right inputs.

## References

This is general byte-string infrastructure rather than a formalization of an external result.
-/

public section

namespace Cslib.Crypto.FixedBytes

/-- Concatenate `blocks` fixed byte strings of width `width` in increasing block order. -/
def flattenBlocks {blocks width : ℕ} (X : Fin blocks → FixedBytes width) :
    FixedBytes (blocks * width) := fun index =>
  let coordinate := finProdFinEquiv.symm index
  X coordinate.1 coordinate.2

/-- Reading the row-major coordinate of a block and offset returns that source byte. -/
@[simp] theorem flattenBlocks_apply {blocks width : ℕ} (X : Fin blocks → FixedBytes width)
    (block : Fin blocks) (offset : Fin width) :
    flattenBlocks X (finProdFinEquiv (block, offset)) = X block offset := by
  simp [flattenBlocks]

/-- Concatenate two equal-width byte strings as consecutive blocks. -/
def pairBlocks {width : ℕ} (left right : FixedBytes width) : FixedBytes (2 * width) :=
  flattenBlocks (blocks := 2) fun block => if block.val = 0 then left else right

/-- The first block of a two-block concatenation is its left input. -/
@[simp] theorem pairBlocks_left {width : ℕ} (left right : FixedBytes width)
    (offset : Fin width) :
    pairBlocks left right (finProdFinEquiv (0, offset)) = left offset := by
  simp [pairBlocks]

/-- The second block of a two-block concatenation is its right input. -/
@[simp] theorem pairBlocks_right {width : ℕ} (left right : FixedBytes width)
    (offset : Fin width) :
    pairBlocks left right (finProdFinEquiv (1, offset)) = right offset := by
  simp [pairBlocks]

end Cslib.Crypto.FixedBytes
