/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Common binary prefixes through exclusive or

Two naturals `A < B` agree above bit `s = (A ^^^ B).size`, i.e. on the common prefix of their
binary expansions, and the dyadic point `(2 (A / 2^s) + 1) 2^(s-1)`, the common prefix followed by
a `1`, separates them. This is the arithmetic content of the compression code in the completeness
proof of [Bogdanov and Trevisan, Claim 20][BogdanovTrevisan2006].

## Main results

* `Nat.div_two_pow_eq_iff_xor_lt`: two naturals have the same quotient by `2 ^ k` exactly when
  their exclusive or is below `2 ^ k`.
* `Nat.lt_commonPrefix_mid_le`: the split of `A < B` at their highest differing bit.

## References

* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
-/

public section

namespace Nat

/-- Two naturals have the same quotient by `2 ^ k` exactly when their exclusive or is below
`2 ^ k`. -/
theorem div_two_pow_eq_iff_xor_lt (A B k : ℕ) : A / 2 ^ k = B / 2 ^ k ↔ A ^^^ B < 2 ^ k := by
  refine ⟨fun h => Nat.lt_pow_two_of_testBit _ fun i hi => ?_,
    fun h => Nat.eq_of_testBit_eq fun i => ?_⟩
  · have h1 := (Nat.testBit_div_two_pow (n := k) A (i - k)).symm.trans
      (h ▸ Nat.testBit_div_two_pow (n := k) B (i - k))
    rw [show i - k + k = i by omega] at h1
    simp [Nat.testBit_xor, h1]
  · have := Nat.testBit_lt_two_pow (x := A ^^^ B) (i := i + k)
      (h.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    rw [Nat.testBit_xor] at this
    revert this
    cases A.testBit (i + k) <;> cases B.testBit (i + k) <;> simp

/-- **Splitting at the highest differing bit.** For `A < B` and `s = (A ^^^ B).size`, the two
numbers have the same quotient `Z` by `2 ^ s`, and the dyadic point `(2 Z + 1) 2^(s-1)` lies
strictly above `A` and at most `B`. -/
theorem lt_commonPrefix_mid_le {A B : ℕ} (hAB : A < B) :
    1 ≤ (A ^^^ B).size ∧ A / 2 ^ (A ^^^ B).size = B / 2 ^ (A ^^^ B).size ∧
      A < (2 * (A / 2 ^ (A ^^^ B).size) + 1) * 2 ^ ((A ^^^ B).size - 1) ∧
      (2 * (A / 2 ^ (A ^^^ B).size) + 1) * 2 ^ ((A ^^^ B).size - 1) ≤ B := by
  set s := (A ^^^ B).size
  have hs1 : 1 ≤ s := Nat.size_pos.mpr <| Nat.pos_of_ne_zero fun h0 => hAB.ne <| by
    simpa using (div_two_pow_eq_iff_xor_lt A B 0).mpr (by simp [h0])
  have heq : A / 2 ^ s = B / 2 ^ s := (div_two_pow_eq_iff_xor_lt A B s).mpr (Nat.lt_size_self _)
  have hne' : A / 2 ^ (s - 1) ≠ B / 2 ^ (s - 1) := fun h => by
    have := (div_two_pow_eq_iff_xor_lt A B (s - 1)).mp h
    have := Nat.lt_size.mp (show s - 1 < s by omega)
    omega
  have hpow : 2 ^ s = 2 ^ (s - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hs1]
  have hle := Nat.div_le_div_right (c := 2 ^ (s - 1)) hAB.le
  have hA2 : A / 2 ^ s = A / 2 ^ (s - 1) / 2 := by rw [hpow, Nat.div_div_eq_div_mul]
  have hB2 : B / 2 ^ s = B / 2 ^ (s - 1) / 2 := by rw [hpow, Nat.div_div_eq_div_mul]
  refine ⟨hs1, heq, ?_, ?_⟩
  · simpa only [show A / 2 ^ (s - 1) = 2 * (A / 2 ^ s) by omega, mul_comm (2 ^ (s - 1))] using
      Nat.lt_mul_div_succ A (by positivity : 0 < 2 ^ (s - 1))
  · simpa only [show B / 2 ^ (s - 1) = 2 * (A / 2 ^ s) + 1 by omega] using
      Nat.div_mul_le_self B (2 ^ (s - 1))

end Nat
