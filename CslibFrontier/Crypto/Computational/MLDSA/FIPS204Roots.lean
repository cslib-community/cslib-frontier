/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The roots used by the FIPS 204 number-theoretic transform

[FIPS 204][NISTFIPS204], §§2.5 and 7.5, specifies 1753 as a primitive 512th root modulo
8380417. Its odd powers are 256 distinct roots of `X^256 + 1`. The index here is the odd
exponent's position before the standard's eight-bit reversal.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

/-- The specified generator has multiplicative order 512 in the FIPS field. -/
theorem orderOf_zeta : orderOf (1753 : ZMod 8380417) = 512 :=
  orderOf_eq_prime_pow (p := 2) (n := 8) (by decide +kernel) (by decide +kernel)

/-- The odd roots of `X^256 + 1` in exponent order, before the bit reversal in equation (2.1). -/
def nttNode (i : Fin 256) : ZMod 8380417 := 1753 ^ (2 * i.val + 1)

theorem nttNode_pow (i : Fin 256) : nttNode i ^ 256 = -1 := by
  have h : (1753 : ZMod 8380417) ^ 256 = -1 := by decide +kernel
  rw [nttNode, ← pow_mul, Nat.mul_comm, pow_mul, h, pow_add, pow_mul]
  norm_num

theorem nttNode_injective : Function.Injective nttNode := by
  intro i j hij
  have h := pow_injOn_Iio_orderOf (x := (1753 : ZMod 8380417))
    (show 2 * i.val + 1 < orderOf (1753 : ZMod 8380417) by rw [orderOf_zeta]; lia)
    (show 2 * j.val + 1 < orderOf (1753 : ZMod 8380417) by rw [orderOf_zeta]; lia) hij
  apply Fin.ext
  lia

end Cslib.Crypto.MLDSA.FIPS204
