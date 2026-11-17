/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.MerkleDamgard
import CslibFrontier.Crypto.Computational.MerkleDamgard.LengthPadding

/-!
# Tests for length-strengthened Merkle–Damgård padding
-/

namespace CslibFrontierTests.Crypto.MerkleDamgardLengthPadding

open Cslib.Crypto

/-- Partition example ([BonehShoup2023], §8.4, pp. 296–297): at `n = 4` (with `2`-bit length field),
`msg = [true]` leaves room for `PB = 1 ‖ 01` in the single block (`s = 1`). -/
example : mdLengthBlocks 4 [true] = [[true, true, false, true]] := by
  decide

/-- Additional padding block ([BonehShoup2023], §8.4, p. 297: "If the message length is such that
there is no space for `PB` in the last block ..., then an additional block is added just for the
padding block"): at `n = 4`, `msg = [true, false]` leaves no room for `PB`, so `1 ‖ 0` finishes the
first block and the `2`-bit count `⟨2⟩` goes in an additional block. -/
example :
    mdLengthBlocks 4 [true, false] =
      [[true, false, true, false], [false, false, true, false]] := by
  decide

/-- The bound `hs₂` in `mdLengthBlocks_suffix_iff` cannot be weakened to `≤`: at `n = 4`,
`m₂ = List.replicate 13 false` has `mdLengthBlockCount 4 m₂ = 4 = 2 ^ (4 / 2)`, the first count
that does not fit in two bits, and the blocks of the different message `List.replicate 5 false` are
a suffix of its blocks. -/
example :
    mdLengthBlockCount 4 (List.replicate 13 false) = 2 ^ (4 / 2) ∧
      mdLengthBlocks 4 (List.replicate 5 false) <:+ mdLengthBlocks 4 (List.replicate 13 false) := by
  decide

/-- Boundary counterexample for `length_mdLengthPad` and `flatten_mdLengthBlocks` at `n = 4`:
a ten-zero-bit message has block count `4 = 2 ^ (4 / 2)`, so replacing `<` with `≤` fails. -/
example :
    mdLengthBlockCount 4 (List.replicate 10 false) = 2 ^ (4 / 2) ∧
      (mdLengthPad 4 (List.replicate 10 false)).length ≠
        mdLengthBlockCount 4 (List.replicate 10 false) * 4 ∧
      (mdLengthBlocks 4 (List.replicate 10 false)).flatten ≠
        mdLengthPad 4 (List.replicate 10 false) := by
  decide

/-- Collision resistance on messages whose padded block count fits in the `(n / 2)`-bit field,
obtained directly from `CompressionFamily.collisionResistantOn_merkleDamgardChain` and
`mdLengthBlocks_suffix_iff` ([BonehShoup2023], §8.4, Theorem 8.3, p. 297). -/
example {h : List Bool → List Bool → List Bool} (hh : CompressionFamily h) :
    CollisionResistantOn
      (fun k msg =>
        merkleDamgardChain h k (List.replicate k.length false) (mdLengthBlocks k.length msg))
      (fun n m => decide (mdLengthBlockCount n m < 2 ^ (n / 2))) := by
  refine hh.collisionResistantOn_merkleDamgardChain mdLengthBlocks _
    computableInPolyTime_mdLengthBlocks ?_ ?_
  · exact Filter.Eventually.of_forall fun _ _ _ _ hb => length_of_mem_mdLengthBlocks hb
  · exact Filter.Eventually.of_forall fun n m₁ m₂ _ h₂ hne hsuf =>
      hne ((mdLengthBlocks_suffix_iff (of_decide_eq_true h₂)).mp hsuf)

end CslibFrontierTests.Crypto.MerkleDamgardLengthPadding
