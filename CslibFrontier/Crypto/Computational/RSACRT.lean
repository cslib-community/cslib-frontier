/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.RSATrapdoor
public import CslibFrontier.Foundations.Data.Nat.ChineseRemainder
import Mathlib.FieldTheory.Finite.Basic

/-!
# RSA-CRT inversion and the gcd identity behind its fault attack

RSA-CRT computes the RSA inverse `y ^ d mod n` from the private key `(p, q, d_p, d_q, q_inv)`:
it computes `x_p = y ^ d_p mod p` and `x_q = y ^ d_q mod q` and recombines them by the Chinese
Remainder Theorem as `x_q + (q_inv · (x_p − x_q) mod p) · q`. If `x_q` is correct and `x_p` is
not, the recombined output `σ` satisfies `gcd(σ ^ e − h, n) = q`, where `h` is the input and
`σ ^ e − h` is computed in `ℤ_n` and read in `[0, n)` ([BonehShoup2023], §16.4.3, pp. 701–702).

## Main definitions

* `Cslib.Crypto.RSACRTKey`: the RSA-CRT private key `(p, q, d_p, d_q, q_inv)`.
* `Cslib.Crypto.RSACRTKey.powP`, `Cslib.Crypto.RSACRTKey.powQ`, `Cslib.Crypto.RSACRTKey.combine`,
  `Cslib.Crypto.RSACRTKey.invert`: the three steps of RSA-CRT inversion and their composite.
* `Cslib.Crypto.RSADesc.crtKeyWith`: the key derived from an `RSADesc`, with
  `d_p = d mod (p - 1)`, `d_q = d mod (q - 1)` and a given `q_inv`.
* `Cslib.Crypto.RSADesc.crtQInv`, `Cslib.Crypto.RSADesc.crtKey`: the inverse of `q` modulo `p`
  taken from `ZMod p`, and the key that uses it.

## Main results

* `Cslib.Crypto.RSADesc.crtQInv_mul_modEq_one`: `crtQInv` is an inverse of `q` modulo `p`.
* `Cslib.Crypto.RSACRTKey.combine_mod_mod`, `Cslib.Crypto.RSACRTKey.combine_modEq_p`,
  `Cslib.Crypto.RSACRTKey.combine_modEq_q`: recombination returns `x < p * q` from its residues,
  and its output is congruent to `x_p` modulo `p` and to `x_q` modulo `q`.
* `Cslib.Crypto.RSADesc.powP_crtKeyWith`, `Cslib.Crypto.RSADesc.powQ_crtKeyWith`: for odd `p`
  (respectively `q`), the first two steps compute `y ^ d mod p` and `y ^ d mod q`.
* `Cslib.Crypto.RSADesc.invert_crtKeyWith`, `Cslib.Crypto.RSADesc.invert_crtKey`: for odd `p` and
  `q`, RSA-CRT inversion equals `rsaInvert n d` on every input.
* `Cslib.Crypto.RSADesc.gcd_val_pow_sub_eq_q`: an output `σ` that agrees with `h ^ d` modulo `q`
  but not modulo `p` gives `gcd(σ ^ e − h, n) = q`.
* `Cslib.Crypto.RSADesc.gcd_val_pow_sub_combine_eq_q`: the gcd identity behind the fault attack:
  recombining a correct `x_q` with an `x_p'` that is not congruent to `h ^ d` modulo `p` gives an
  output `σ` with `gcd(σ ^ e − h, n) = q`.

## Implementation notes

Residues are natural numbers. The book's `σ̂ ^ e − H(m) ∈ ℤ_n`, read as an integer in `[0, n)`, is
`((σ : ZMod n) ^ e - h).val`, and an arbitrary natural number `h` takes the place of the hash
value `H(m)`. The theorems hold for every `q_inv` with `q_inv * q ≡ 1 [MOD p]`;
`RSADesc.crtKey` uses the inverse in `ZMod p`. The book also assumes `p > q`; no result here needs
it.

Recombination is `crtCombine q p x_q x_p q_inv` from
`CslibFrontier/Foundations/Data/Nat/ChineseRemainder.lean`; its congruences and correctness come
from `crtCombine_modEq_left`, `crtCombine_modEq_right` and `crtCombine_eq`.

Correctness of RSA-CRT needs `p` and `q` odd: `RSADesc` admits `p = 2`, where
`d_p = d mod 1 = 0`, so step 1 returns `1` for every `y`, which is wrong for even `y`. The tests
check the counterexample `p = 2`, `q = 5`, `e = d = 3`, `y = 2`, where RSA-CRT returns `3` and
`y ^ d mod n = 8`. The fault-attack identity does not need oddness: its hypothesis is that `x_q`
is congruent to the correct value `h ^ d` modulo `q`.

Not formalized: the book's estimate that RSA-CRT is about four times faster, and FDH-RSA signing;
nothing is proved about an attacker or its running time.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  §16.4.3, pp. 701–702.
-/

public section

namespace Cslib.Crypto

/-- An RSA-CRT private key `(p, q, d_p, d_q, q_inv)` ([BonehShoup2023], §16.4.3, p. 701). The
structure carries no conditions: `RSADesc.crtKeyWith` derives the key of an RSA key, and each
theorem states the hypotheses it uses. -/
structure RSACRTKey where
  /-- The first prime factor of the modulus. -/
  p : ℕ
  /-- The second prime factor of the modulus. -/
  q : ℕ
  /-- The exponent used modulo `p`, `d mod (p - 1)` for a key derived from `d`. -/
  dp : ℕ
  /-- The exponent used modulo `q`, `d mod (q - 1)` for a key derived from `d`. -/
  dq : ℕ
  /-- An inverse of `q` modulo `p`. -/
  qInv : ℕ

namespace RSACRTKey

/-- Step 1 of RSA-CRT inversion: `x_p = y ^ d_p mod p`. -/
@[expose] def powP (key : RSACRTKey) (y : ℕ) : ℕ :=
  y ^ key.dp % key.p

/-- Step 2 of RSA-CRT inversion: `x_q = y ^ d_q mod q`. -/
@[expose] def powQ (key : RSACRTKey) (y : ℕ) : ℕ :=
  y ^ key.dq % key.q

/-- Step 3 of RSA-CRT inversion: recombine `x_p` and `x_q` as
`x_q + (q_inv · (x_p − x_q) mod p) · q`, with `x_p − x_q` taken in `ℤ`, which is
`crtCombine q p x_q x_p q_inv` (it computes `x_p − x_q` as `x_p + (p − x_q mod p)`). -/
@[expose] def combine (key : RSACRTKey) (xp xq : ℕ) : ℕ :=
  crtCombine key.q key.p xq xp key.qInv

/-- RSA-CRT inversion ([BonehShoup2023], §16.4.3, p. 701): recombine `y ^ d_p mod p` and
`y ^ d_q mod q`. -/
@[expose] def invert (key : RSACRTKey) (y : ℕ) : ℕ :=
  key.combine (key.powP y) (key.powQ y)

/-- The hypothesis `q_inv * q ≡ 1 [MOD p]`, read in `ZMod p`. -/
private theorem natCast_qInv_mul_q {key : RSACRTKey} (hinv : key.qInv * key.q ≡ 1 [MOD key.p]) :
    (key.qInv : ZMod key.p) * key.q = 1 := by
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).2 hinv
  push_cast at h
  exact h

/-- **CRT recombination** ([BonehShoup2023], §16.4.3, p. 701): for an inverse `q_inv` of `q`
modulo `p` and `x < p * q`, recombining `x mod p` and `x mod q` returns `x`. Positivity of `p`
and `q` follows from `x < p * q`, and their coprimality from the inverse. -/
theorem combine_mod_mod (key : RSACRTKey) (hinv : key.qInv * key.q ≡ 1 [MOD key.p]) {x : ℕ}
    (hx : x < key.p * key.q) : key.combine (x % key.p) (x % key.q) = x :=
  crtCombine_eq (Nat.pos_of_ne_zero fun h => by simp [h] at hx)
    (Nat.pos_of_ne_zero fun h => by simp [h] at hx)
    (Nat.coprime_of_mul_modEq_one key.qInv (by rwa [mul_comm])) (by rwa [mul_comm]) rfl rfl
    key.qInv (natCast_qInv_mul_q hinv)

/-- The recombined value is congruent to `x_q` modulo `q`, for all `x_p` and `x_q`. -/
theorem combine_modEq_q (key : RSACRTKey) (xp xq : ℕ) : key.combine xp xq ≡ xq [MOD key.q] :=
  crtCombine_modEq_left key.q key.p xq xp key.qInv

/-- The recombined value is congruent to `x_p` modulo `p` ([BonehShoup2023], §16.4.3, p. 701:
"The reader can verify that indeed x ≡ x_p mod p"), for every `x_p` and `x_q`. -/
theorem combine_modEq_p (key : RSACRTKey) (hp : 0 < key.p)
    (hinv : key.qInv * key.q ≡ 1 [MOD key.p]) (xp xq : ℕ) : key.combine xp xq ≡ xp [MOD key.p] :=
  crtCombine_modEq_right hp (natCast_qInv_mul_q hinv) xq xp

end RSACRTKey

namespace RSADesc

/-- The RSA-CRT key of `desc` with a given `q_inv` ([BonehShoup2023], §16.4.3, p. 701):
`d_p = d mod (p - 1)` and `d_q = d mod (q - 1)`. The results about it assume
`qInv * q ≡ 1 [MOD p]`. -/
@[expose] def crtKeyWith (desc : RSADesc) (qInv : ℕ) : RSACRTKey where
  p := desc.p
  q := desc.q
  dp := desc.d % (desc.p - 1)
  dq := desc.d % (desc.q - 1)
  qInv := qInv

/-- The inverse of `q` modulo `p`, as the value of `q⁻¹` in `ZMod p`. -/
@[expose] def crtQInv (desc : RSADesc) : ℕ :=
  ((desc.q : ZMod desc.p)⁻¹).val

/-- `crtQInv` is an inverse of `q` modulo `p`. -/
theorem crtQInv_mul_modEq_one (desc : RSADesc) : desc.crtQInv * desc.q ≡ 1 [MOD desc.p] := by
  have : NeZero desc.p := ⟨desc.hp.ne_zero⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [crtQInv, ZMod.natCast_zmod_val, mul_comm]
  exact ZMod.coe_mul_inv_eq_one _ ((Nat.coprime_primes desc.hq desc.hp).2 desc.hpq.symm)

/-- The RSA-CRT key of `desc` ([BonehShoup2023], §16.4.3, p. 701), with `q_inv = crtQInv`. -/
def crtKey (desc : RSADesc) : RSACRTKey :=
  desc.crtKeyWith desc.crtQInv

/-- `x ^ (a mod (p - 1)) ≡ x ^ a [MOD p]` for a prime `p` when `a mod (p - 1)` is positive. -/
private theorem pow_mod_sub_one_modEq {p a : ℕ} (hp : p.Prime) (ha : 0 < a % (p - 1)) (x : ℕ) :
    x ^ (a % (p - 1)) ≡ x ^ a [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  by_cases hx : (x : ZMod p) = 0
  · rw [hx, zero_pow ha.ne', zero_pow (by rintro rfl; simp at ha)]
  · exact (pow_eq_pow_mod a (ZMod.pow_card_sub_one_eq_one hx)).symm

/-- If `e * d ≡ 1 [MOD m]` and `m ≠ 1`, then `m` does not divide `d`. -/
private theorem pos_mod_of_mul_modEq_one {e d m : ℕ} (hm : m ≠ 1) (h : e * d ≡ 1 [MOD m]) :
    0 < d % m :=
  Nat.pos_of_ne_zero fun h0 => hm <|
    (Nat.coprime_of_mul_modEq_one e (by rwa [mul_comm])).symm.eq_one_of_dvd
      (Nat.dvd_of_mod_eq_zero h0)

/-- Step 1 of RSA-CRT inversion computes `y ^ d mod p` ([BonehShoup2023], §16.4.3, p. 701, "by
definition of d_p"). The hypothesis `p ≠ 2` is not in the book; it is needed because
`d_p = d mod 1 = 0` when `p = 2`. -/
theorem powP_crtKeyWith (desc : RSADesc) (hp2 : desc.p ≠ 2) (qInv y : ℕ) :
    (desc.crtKeyWith qInv).powP y = y ^ desc.d % desc.p :=
  pow_mod_sub_one_modEq desc.hp
    (pos_mod_of_mul_modEq_one (by have := desc.hp.two_le; omega)
      (desc.hed.of_dvd (dvd_mul_right _ _))) y

/-- Step 2 of RSA-CRT inversion computes `y ^ d mod q` ([BonehShoup2023], §16.4.3, p. 701, "by
definition of d_q"). The hypothesis `q ≠ 2` is not in the book; it is needed because
`d_q = d mod 1 = 0` when `q = 2`. -/
theorem powQ_crtKeyWith (desc : RSADesc) (hq2 : desc.q ≠ 2) (qInv y : ℕ) :
    (desc.crtKeyWith qInv).powQ y = y ^ desc.d % desc.q :=
  pow_mod_sub_one_modEq desc.hq
    (pos_mod_of_mul_modEq_one (by have := desc.hq.two_le; omega)
      (desc.hed.of_dvd (dvd_mul_left _ _))) y

/-- **Correctness of RSA-CRT inversion** ([BonehShoup2023], §16.4.3, p. 701): for odd primes `p`
and `q` and any inverse `q_inv` of `q` modulo `p`, RSA-CRT inversion equals `y ^ d mod n` for
every `y`. The book does not state that `p` and `q` are odd; without it the statement fails (see
the module documentation). -/
theorem invert_crtKeyWith (desc : RSADesc) (hp2 : desc.p ≠ 2) (hq2 : desc.q ≠ 2) {qInv : ℕ}
    (hinv : qInv * desc.q ≡ 1 [MOD desc.p]) (y : ℕ) :
    (desc.crtKeyWith qInv).invert y = rsaInvert desc.modulus desc.d y := by
  have hP : (desc.crtKeyWith qInv).powP y = rsaInvert desc.modulus desc.d y % desc.p := by
    rw [desc.powP_crtKeyWith hp2, rsaInvert, RSADesc.modulus, Nat.mod_mul_right_mod]
  have hQ : (desc.crtKeyWith qInv).powQ y = rsaInvert desc.modulus desc.d y % desc.q := by
    rw [desc.powQ_crtKeyWith hq2, rsaInvert, RSADesc.modulus, Nat.mod_mul_left_mod]
  rw [RSACRTKey.invert, hP, hQ]
  exact RSACRTKey.combine_mod_mod _ hinv (Nat.mod_lt _ desc.modulus_pos)

/-- **Correctness of RSA-CRT inversion** with the key `crtKey`: for odd `p` and `q`, it equals
`y ^ d mod n` for every `y`. -/
theorem invert_crtKey (desc : RSADesc) (hp2 : desc.p ≠ 2) (hq2 : desc.q ≠ 2) (y : ℕ) :
    desc.crtKey.invert y = rsaInvert desc.modulus desc.d y :=
  desc.invert_crtKeyWith hp2 hq2 desc.crtQInv_mul_modEq_one y

/-- **The gcd step of the fault attack** ([BonehShoup2023], §16.4.3, p. 702): if `σ` agrees with
`h ^ d` modulo `q` but not modulo `p`, then `q` is the gcd of `n` and the representative in
`[0, n)` of `σ ^ e − h ∈ ℤ_n`. Any natural number `h` stands in for the hash value `H(m)`. -/
theorem gcd_val_pow_sub_eq_q (desc : RSADesc) {σ h : ℕ} (hσq : σ ≡ h ^ desc.d [MOD desc.q])
    (hσp : ¬ σ ≡ h ^ desc.d [MOD desc.p]) :
    Nat.gcd ((σ : ZMod desc.modulus) ^ desc.e - h).val desc.modulus = desc.q := by
  set v := ((σ : ZMod desc.modulus) ^ desc.e - h).val with hv_def
  have hv : v + h ≡ σ ^ desc.e [MOD desc.modulus] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hv_def, ZMod.natCast_zmod_val, sub_add_cancel]
  have hvq : desc.q ∣ v := by
    have h1 : σ ^ desc.e ≡ h [MOD desc.q] :=
      calc σ ^ desc.e ≡ (h ^ desc.d) ^ desc.e [MOD desc.q] := hσq.pow _
        _ = h ^ (desc.e * desc.d) := by rw [← pow_mul, mul_comm]
        _ ≡ h [MOD desc.q] := (rsa_pow_mul_modEq desc h).of_dvd (dvd_mul_left _ _)
    have h2 : v + h ≡ 0 + h [MOD desc.q] := by
      rw [zero_add]
      exact (hv.of_dvd (dvd_mul_left _ _)).trans h1
    exact Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_right_cancel' h h2)
  have hvp : ¬ desc.p ∣ v := by
    intro hdvd
    apply hσp
    have h1 : σ ^ desc.e ≡ h [MOD desc.p] := by
      have h2 : v + h ≡ 0 + h [MOD desc.p] := (Nat.modEq_zero_iff_dvd.2 hdvd).add_right h
      rw [zero_add] at h2
      exact (hv.of_dvd (dvd_mul_right _ _)).symm.trans h2
    calc σ ≡ σ ^ (desc.e * desc.d) [MOD desc.p] :=
          ((rsa_pow_mul_modEq desc σ).of_dvd (dvd_mul_right _ _)).symm
      _ = (σ ^ desc.e) ^ desc.d := pow_mul _ _ _
      _ ≡ h ^ desc.d [MOD desc.p] := h1.pow _
  change Nat.gcd v (desc.p * desc.q) = desc.q
  rw [Nat.Coprime.gcd_mul v ((Nat.coprime_primes desc.hp desc.hq).2 desc.hpq),
    Nat.gcd_eq_right hvq,
    Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd desc.hp).2 hvp)),
    one_mul]

/-- **The gcd identity behind the fault attack on RSA-CRT** ([BonehShoup2023], §16.4.3,
pp. 701–702): recombine any `x_q ≡ h ^ d (mod q)`, such as the correct `x_q = h ^ d mod q`, with
any `x_p'` that is not congruent to `h ^ d` modulo `p` (a faulty step 1). The output `σ`
satisfies `gcd(σ ^ e − h, n) = q`, with `σ ^ e − h ∈ ℤ_n` read in `[0, n)`. Any natural number
`h` stands in for the hash value `H(m)`, and `q_inv` is any inverse of `q` modulo `p`. For a
residue `x_p' < p` the hypothesis says `x_p' ≠ h ^ d mod p`, as in the book;
`RSADesc.powQ_crtKeyWith` shows that step 2 computes `x_q = h ^ d mod q` when `q` is odd. -/
theorem gcd_val_pow_sub_combine_eq_q (desc : RSADesc) {qInv : ℕ}
    (hinv : qInv * desc.q ≡ 1 [MOD desc.p]) {h xp xq : ℕ} (hxq : xq ≡ h ^ desc.d [MOD desc.q])
    (hxp : ¬ xp ≡ h ^ desc.d [MOD desc.p]) :
    Nat.gcd ((((desc.crtKeyWith qInv).combine xp xq : ℕ) : ZMod desc.modulus) ^ desc.e - h).val
      desc.modulus = desc.q :=
  desc.gcd_val_pow_sub_eq_q (((desc.crtKeyWith qInv).combine_modEq_q _ _).trans hxq)
    fun h' => hxp (((desc.crtKeyWith qInv).combine_modEq_p desc.hp.pos hinv xp xq).symm.trans h')

end RSADesc

end Cslib.Crypto
