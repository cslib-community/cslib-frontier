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

/-- Necessity of the non-overflow hypothesis `hs₂` in `mdLengthBlocks_suffix_iff`: at `n = 4`
(`2 ^ (n / 2) = 4`), `m₂ = List.replicate 26 false` has `mdLengthBlockCount 4 m₂ = 8 ≥ 4`,
truncating its final block to `[false, false, true, false]` and making
`mdLengthBlocks 4 [false, false]` a suffix of `mdLengthBlocks 4 m₂`. -/
example :
    mdLengthBlocks 4 [false, false] <:+ mdLengthBlocks 4 (List.replicate 26 false) := by
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
