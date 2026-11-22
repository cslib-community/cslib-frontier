/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
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

## Main results

* `Cslib.Algorithms.Lean.CDCL.luby_pow`: for every base `y`, the term at the end of each complete
  subsequence, at position `2 ^ (m + 1) - 2`, is `y ^ m`. So the sequence is unbounded for
  `y ≥ 2` (for `y = 1` every term is `1`); the solver's termination with restarts rests on it.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

/-- The smallest complete subsequence containing position `x`: its size `2 ^ (seq + 1) - 1` and
`seq`, by doubling from `size` and `seq`. A loop of `luby`, which supplies enough fuel. -/
def luby.find (x : ℕ) : (fuel size seq : ℕ) → ℕ × ℕ
  | 0, size, seq => (size, seq)
  | fuel + 1, size, seq =>
    if size < x + 1 then luby.find x fuel (2 * size + 1) (seq + 1) else (size, seq)

/-- The exponent of the term at position `x` of a complete subsequence of size `size` and exponent
`seq`: the last position has the exponent `seq`; otherwise descend into the half containing
`x`. A loop of `luby`, which supplies enough fuel. -/
def luby.down : (fuel size seq x : ℕ) → ℕ
  | 0, _, seq, _ => seq
  | fuel + 1, size, seq, x =>
    if size - 1 = x then seq
    else luby.down fuel ((size - 1) / 2) (seq - 1) (x % ((size - 1) / 2))

/-- **The Luby sequence**: its term at position `x`, with base `y`. -/
def luby (y x : ℕ) : ℕ :=
  let p := luby.find x (x + 1) 1 0
  y ^ luby.down (p.2 + 1) p.1 p.2 x

/-- From a complete subsequence of exponent `s`, the search for the position `2 ^ (m + 1) - 2`
reaches the complete subsequence of exponent `m`, given `m - s` fuel. -/
private theorem lubyFind_pow (m : ℕ) : ∀ (d s size fuel : ℕ), s + d = m → size = 2 ^ (s + 1) - 1 →
    d ≤ fuel → luby.find (2 ^ (m + 1) - 2) fuel size s = (2 ^ (m + 1) - 1, m)
  | 0, s, size, fuel, h, hsize, _ => by
    have hm : s = m := by omega
    subst hm hsize
    have : 2 ≤ 2 ^ (s + 1) := by
      rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := s); omega
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [luby.find, ite_eq_right (by omega)]
  | d + 1, s, size, fuel, h, hsize, hfuel => by
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hlt : 2 ^ (s + 1) < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    have h2 : 2 ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by rw [Nat.pow_succ]; omega
    have h1 := Nat.one_le_two_pow (n := s + 1)
    rw [luby.find, ite_eq_left (by omega)]
    exact lubyFind_pow m d (s + 1) _ fuel (by omega) (by omega) (by omega)

/-- **The peaks of the Luby sequence**: for every base `y`, its term at position
`2 ^ (m + 1) - 2`, the end of a complete subsequence, is `y ^ m`. So the sequence is unbounded for
`y ≥ 2`; for `y = 1` its peaks, like all its terms, are `1`. -/
theorem luby_pow (y m : ℕ) : luby y (2 ^ (m + 1) - 2) = y ^ m := by
  have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
  have hm : m < 2 ^ m := Nat.lt_two_pow_self
  have hfind := lubyFind_pow m m 0 1 (2 ^ (m + 1) - 2 + 1) (by omega) (by simp) (by omega)
  unfold luby
  simp only [hfind]
  rw [luby.down, ite_eq_left (by omega)]

end Cslib.Algorithms.Lean.CDCL
