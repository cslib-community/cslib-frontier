/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.NisanSpace
import CslibFrontier.Computability.Complexity.Classes.LogSpace.USTCON

/-! Nisan's generator on seeds packed into naturals: the Toeplitz hash on packed blocks follows the
orientation of `Matrix.toeplitz`, the on-demand generator bits stream exactly the output of
`Cslib.Crypto.PRG.Nisan.bitGenerator`, and `BPL ⊆ DSPACE(log² n)` applies to a concrete language. -/

namespace CslibFrontierTests.NisanGeneratorSpace

open Cslib.Probability Cslib.Crypto.PRG.Nisan Cslib.Complexity

-- Orientation of the Toeplitz matrix, with blocks of `n = 2` bits: the diagonals are bits `0, 1, 2`
-- of the seed and the offset bits `3, 4`, and `toeplitz a i j = a (i + 1 - j)`. With only diagonal
-- `2` set (`z = 4`), the block `x = 1` (only `x₀`) hashes to `(a 1, a 2) = (0, 1)`, that is `2`,
-- while `x = 2` (only `x₁`) hashes to `(a 0, a 1) = (0, 0)`. A transposed matrix would swap them.
example : toeplitzHashNat 2 4 0 1 = 2 := by decide
example : toeplitzHashNat 2 4 0 2 = 0 := by decide
-- The offset is added: setting offset bit `0` (seed bit `3`) flips output bit `0`.
example : toeplitzHashNat 2 (4 + 8) 0 1 = 3 := by decide
-- The seed is read from the offset `o`: shifting the seed by one bit and reading from `1` agrees.
example : toeplitzHashNat 2 8 1 1 = 2 := by decide

-- The packed bits agree with `Cslib.Probability.toeplitzHash` on every block of two bits for a seed
-- with every diagonal and offset bit set.
example : ∀ x : Fin 4, ∀ i : Fin 2, (toeplitzHashNat 2 31 0 x).testBit i =
    toeplitzHash (hashSeedOfNat 2 31 0) (fun j : Fin 2 => (x : ℕ).testBit j) i := by
  decide

-- The on-demand bits of the generator with blocks of `2` bits and one hash seed (`2 ^ 1 * 2 = 4`
-- output bits, seeds of `2 + 1 * 5 = 7` bits) stream the output of `bitGenerator`, for every seed.
example : ∀ z : Fin (2 ^ 7), (List.ofFn fun j : Fin (2 ^ 1 * 2) => bitGeneratorNat 2 1 z j) =
    List.ofFn (bitGenerator 2 1 (seedOfNat 2 1 z)) := by
  decide

-- With two hash seeds the last block applies both hashes, in order: the block index `3 = 0b11`
-- selects both levels, on seeds of `2 + 2 * 5 = 12` bits.
example : ∀ j : Fin (2 ^ 2 * 2),
    bitGeneratorNat 2 2 2741 j = bitGenerator 2 2 (seedOfNat 2 2 2741) j := by
  decide
example : ∀ j : Fin (2 ^ 2 * 2),
    bitGeneratorNat 2 2 1234 j = bitGenerator 2 2 (seedOfNat 2 2 1234) j := by
  decide

-- Boundary `k = 0`: the generator outputs its seed block.
example (z : ℕ) : bitGeneratorNat 3 0 z 1 = z.testBit 1 := by
  simp [bitGeneratorNat, blockNat]

-- `BPL ⊆ DSPACE(log² n)` has only class membership as hypothesis, and it is met: undirected
-- connectivity is in `L ⊆ BPL`, so it is decided within `O(log² n)` work cells.
example : USTCON ∈ DSPACE encUSTCON fun n => Nat.log2 n ^ 2 :=
  BPL_subset_DSPACE_log2_sq (L_subset_BPL USTCON_mem_L)

end CslibFrontierTests.NisanGeneratorSpace
