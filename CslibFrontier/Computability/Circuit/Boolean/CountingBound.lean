/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (next to `Cslib/Computability/Circuit/Boolean/Counting.lean`)

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Counting
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Factorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A power-of-two bound on the number of small De Morgan circuits

At most `2 ^ M` functions on `n` inputs have De Morgan circuit complexity at most `s`, where
`M = computableFunctionsLogBound n s = (s + 1) (2 ⌈log₂ (n + s + 1)⌉ + 3)`. This is the factorial
bound `Cslib.Circuits.Boolean.card_computableFunctions_mul_factorial_le` with the factorial dropped
and every factor rounded up to a power of two. The resulting exponent is `O(s log (n + s))`, which
union bounds over small circuits need.

## Main definitions

* `Cslib.Circuits.Boolean.computableFunctionsLogBound`: the exponent
  `(s + 1) * (2 * Nat.clog 2 (n + s + 1) + 3)`.

## Main results

* `Cslib.Circuits.Boolean.card_computableFunctions_le_two_pow`:
  `(computableFunctions n s).card ≤ 2 ^ computableFunctionsLogBound n s`.
* `Cslib.Circuits.Boolean.computableFunctionsLogBound_le_poly`: the exponent is at most
  `(s + 1) (2 (n + s + 1) + 3)`.
* `Cslib.Circuits.Boolean.card_computableFunctions_two_pow_div_five_mul_le`: for `n ≥ 16`, at most
  `2 ^ (2 ^ n / 4)` functions have at most `2 ^ n / (5 n)` gates [AroraBarak07, Theorem 6.15].

## References

* [C. E. Shannon, *The synthesis of two-terminal switching circuits*][Shannon1949]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07]
-/

public section

namespace Cslib.Circuits.Boolean

/-- An explicit `s log(n + s)` upper bound on `log₂ (computableFunctions n s).card`, derived from
`card_computableFunctions_mul_factorial_le`. -/
@[expose] def computableFunctionsLogBound (n s : ℕ) : ℕ :=
  (s + 1) * (2 * Nat.clog 2 (n + s + 1) + 3)

/-- The number of `n`-input Boolean functions of De Morgan circuit complexity at most `s` is at most
`2 ^ computableFunctionsLogBound n s`. -/
theorem card_computableFunctions_le_two_pow (n s : ℕ) :
    (computableFunctions n s).card ≤ 2 ^ computableFunctionsLogBound n s := by
  set L := Nat.clog 2 (n + s + 1)
  have hns : n + s + 1 ≤ 2 ^ L := Nat.le_pow_clog (by decide) (n + s + 1)
  have hs1 : s + 1 ≤ 2 ^ L := (by omega : s + 1 ≤ n + s + 1).trans hns
  have hns0 : n + s ≤ 2 ^ L := (by omega : n + s ≤ n + s + 1).trans hns
  have hbase : 5 * (n + s + 1) ^ 2 ≤ 2 ^ (2 * L + 3) := by
    calc 5 * (n + s + 1) ^ 2
        ≤ 8 * (2 ^ L) ^ 2 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hns 2)
      _ = 2 ^ (2 * L + 3) := by
        rw [← pow_mul, pow_add]
        ring
  have hpow : (5 * (n + s + 1) ^ 2) ^ s ≤ 2 ^ (s * (2 * L + 3)) := by
    calc (5 * (n + s + 1) ^ 2) ^ s
        ≤ (2 ^ (2 * L + 3)) ^ s := Nat.pow_le_pow_left hbase s
      _ = 2 ^ (s * (2 * L + 3)) := by rw [← pow_mul, mul_comm]
  have hends : (s + 1) * (n + s) ≤ 2 ^ (2 * L + 3) := by
    calc (s + 1) * (n + s)
        ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul hs1 hns0
      _ = 2 ^ (2 * L) := by rw [← pow_add, two_mul]
      _ ≤ 2 ^ (2 * L + 3) := Nat.pow_le_pow_right (by decide) (by omega)
  calc (computableFunctions n s).card
      ≤ (computableFunctions n s).card * s.factorial :=
        Nat.le_mul_of_pos_right _ (Nat.factorial_pos s)
    _ ≤ (s + 1) * (5 * (n + s + 1) ^ 2) ^ s * (n + s) :=
        card_computableFunctions_mul_factorial_le n s
    _ = ((s + 1) * (n + s)) * (5 * (n + s + 1) ^ 2) ^ s := by ring
    _ ≤ 2 ^ (2 * L + 3) * 2 ^ (s * (2 * L + 3)) := Nat.mul_le_mul hends hpow
    _ = 2 ^ computableFunctionsLogBound n s := by
        rw [← pow_add, computableFunctionsLogBound]
        congr 1
        ring

/-- Elementary polynomial upper bound on `computableFunctionsLogBound n s`: since
`Nat.clog 2 (n + s + 1) ≤ n + s + 1`, we have
`computableFunctionsLogBound n s ≤ (s + 1) * (2 * (n + s + 1) + 3)`. -/
theorem computableFunctionsLogBound_le_poly (n s : ℕ) :
    computableFunctionsLogBound n s ≤ (s + 1) * (2 * (n + s + 1) + 3) := by
  have hclog : Nat.clog 2 (n + s + 1) ≤ n + s + 1 :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.lt_two_pow_self).le
  dsimp only [computableFunctionsLogBound]
  gcongr

private theorem mul_sq_le_two_pow {n : ℕ} (hn : 16 ≤ n) : 64 * n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc 64 * (n + 1) ^ 2 ≤ 2 * (64 * n ^ 2) := by nlinarith
      _ ≤ 2 ^ (n + 1) := by rw [pow_succ 2 n]; omega

/-- **Almost all functions need about `2 ^ n / n` gates** [AroraBarak07, Theorem 6.15],
[Shannon1949]. For `n ≥ 16`, at most `2 ^ (2 ^ n / 4)` of the `2 ^ 2 ^ n` Boolean functions on `n`
inputs have a circuit with at most `2 ^ n / (5 n)` gates, so all but a `2 ^ (-3 · 2 ^ n / 4)`
fraction need more.

This is stronger than the draft's Theorem 6.15 ("for `n ≥ 100`, almost all Boolean functions on
`n` variables require circuits of size at least `2 ^ n / (10 n)`"). The draft counts all vertices
of a circuit, its `n` inputs included, and has no constant gates, so a draft circuit with fewer
than `2 ^ n / (10 n)` vertices is a De Morgan circuit with fewer than `2 ^ n / (5 n)` gates.
The draft's proof claims `s ^ (3 s) ≤ 2 ^ (2 ^ n / 10)` at `s = 2 ^ n / (10 n)`. That inequality
fails (at `n = 100`, `3 s log₂ s ≈ 0.27 · 2 ^ n`), but any bound `2 ^ (c · 2 ^ n)` with `c < 1`
proves the theorem. Here the factorial count `card_computableFunctions_mul_factorial_le` gives
`c = 1 / 4`. -/
theorem card_computableFunctions_two_pow_div_five_mul_le {n : ℕ} (hn : 16 ≤ n) :
    (computableFunctions n (2 ^ n / (5 * n))).card ≤ 2 ^ (2 ^ n / 4) := by
  set s := 2 ^ n / (5 * n)
  set c := (computableFunctions n s).card
  have h64 := mul_sq_le_two_pow hn
  have hsn : 5 * n * s ≤ 2 ^ n := Nat.mul_div_le _ _
  have hs : n + 1 ≤ s := (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
  have hs64 : 64 * s ≤ 2 ^ n := le_trans (Nat.mul_le_mul_right s (by omega : 64 ≤ 5 * n)) hsn
  -- Shannon's count, simplified with `n + 1 ≤ s` and `s ^ s ≤ 3 ^ s s!`.
  have hcount : c * s.factorial ≤ 4 * s ^ 2 * (20 * s ^ 2) ^ s := by
    refine (card_computableFunctions_mul_factorial_le n s).trans ?_
    calc (s + 1) * (5 * (n + s + 1) ^ 2) ^ s * (n + s)
        ≤ (2 * s) * (5 * (2 * s) ^ 2) ^ s * (2 * s) := by gcongr <;> omega
      _ = 4 * s ^ 2 * (20 * s ^ 2) ^ s := by ring
  have hc : c * s ^ s ≤ 4 * s ^ 2 * (60 * s) ^ s * s ^ s := by
    calc c * s ^ s ≤ c * (3 ^ s * s.factorial) :=
          Nat.mul_le_mul_left _ (Nat.pow_self_le_three_pow_mul_factorial s)
      _ = 3 ^ s * (c * s.factorial) := by ring
      _ ≤ 3 ^ s * (4 * s ^ 2 * (20 * s ^ 2) ^ s) := Nat.mul_le_mul_left _ hcount
      _ = 4 * s ^ 2 * (60 * s) ^ s * s ^ s := by
        rw [mul_pow, mul_pow, show (60 : ℕ) ^ s = 3 ^ s * 20 ^ s by rw [← mul_pow]; norm_num]; ring
  have hc' : c ≤ 4 * s ^ 2 * (60 * s) ^ s :=
    Nat.le_of_mul_le_mul_right hc (pow_pos (by omega) s)
  have hexp : n * (s + 2) ≤ 2 ^ n / 4 := by
    apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
    nlinarith
  calc c ≤ 4 * s ^ 2 * (60 * s) ^ s := hc'
    _ ≤ (2 ^ n) ^ 2 * (2 ^ n) ^ s := by
        gcongr
        · nlinarith
        · omega
    _ = 2 ^ (n * (s + 2)) := by rw [← pow_add, ← pow_mul]; ring_nf
    _ ≤ 2 ^ (2 ^ n / 4) := Nat.pow_le_pow_right two_pos hexp

end Cslib.Circuits.Boolean
