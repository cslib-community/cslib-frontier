/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import Mathlib.Data.Nat.Notation

/-! # The Luby sequence

The restart schedule of MiniSat (`luby_restart`). The Luby sequence `1, 1, 2, 1, 1, 2, 4, 1, 1, 2,
1, 1, 2, 4, 8, …` of Luby, Sinclair and Zuckerman repeats each prefix before doubling; `luby y x`
is its `x`-th term with base `y` in place of `2`, as MiniSat's `luby` computes it: find the
smallest complete subsequence (of length `2 ^ (k + 1) - 1`) containing `x`, then descend into it.

Both loops are bounded by fuel, so the kernel can evaluate the sequence; the fuel suffices, as the
tests check on its prefix.

## Main definitions

* `luby`: the `x`-th term of the Luby sequence with base `y`.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

/-- The smallest complete subsequence containing position `x`: its size `2 ^ (seq + 1) - 1` and
`seq`, by doubling from `size` and `seq`. -/
def lubyFind (x : ℕ) : (fuel size seq : ℕ) → ℕ × ℕ
  | 0, size, seq => (size, seq)
  | fuel + 1, size, seq =>
    if size < x + 1 then lubyFind x fuel (2 * size + 1) (seq + 1) else (size, seq)

/-- The exponent of the term at position `x` of a complete subsequence of size `size` and exponent
`seq`: the last position has the exponent `seq`; otherwise descend into the half containing
`x`. -/
def lubyDown : (fuel size seq x : ℕ) → ℕ
  | 0, _, seq, _ => seq
  | fuel + 1, size, seq, x =>
    if size - 1 = x then seq
    else lubyDown fuel ((size - 1) / 2) (seq - 1) (x % ((size - 1) / 2))

/-- **The Luby sequence**: its term at position `x`, with base `y`. -/
def luby (y x : ℕ) : ℕ :=
  let p := lubyFind x (x + 1) 1 0
  y ^ lubyDown (p.2 + 1) p.1 p.2 x

end Cslib.Algorithms.Lean.CDCL
