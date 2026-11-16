/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Factoring.WeakModuli
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd

/-!
# Linear-relation Fermat factoring

Formalizes Fermat factoring under a known integer linear relation `|a * p - b * q| < n ^ (1 / 4)`
(Boneh–Shoup Section 16.4.2.1, p. 699, and Exercise 16.14, p. 710). The book writes
`|a * p + b * q| < n ^ (1 / 4)` with real parameters `a` and `b`; here `a` and `b` are natural
numbers with the book's `b` negated, and non-integer real parameters `(a, b)` are out of scope.

Multiplying `n = p * q` by `4 * a * b` pairs `2 * a * p` and `2 * b * q`, whose sum is always
even, so `fermatFactor (4 * a * b * n)` recovers `(2 * a * p, 2 * b * q)` up to order without any
parity side condition on `a * p + b * q` (by contrast, `a = 3`, `b = 2` on odd `p` gives odd
`3 * p + 2 * q`, so `⌈√(6 * n)⌉ ≠ (3 * p + 2 * q) / 2`). Taking gcds with `n` then recovers
`(p, q)` or `(q, p)` provided `Nat.Coprime (2 * a) q` and `Nat.Coprime (2 * b) p` (equivalently
`¬ q ∣ 2 * a` and `¬ p ∣ 2 * b` for primes `p, q`). Because `fermatFactor` computes a single
closed-form integer square root with no gap search loop, complexity is certified directly as
`ComputableInPolyTime` rather than as a step bound in terms of `|a * p - b * q|`.

## Main definitions

- `fermatFactorLinear`: feeds `4 * a * b * n` to `fermatFactor` and takes gcds with `n`.

## Main results

- `fermatFactor_four_mul_eq`: closed-form Fermat factorization of `4 * a * b * (p * q)`.
- `fermatFactorLinear_mul_eq`, `fermatFactorLinear_mul_eq_of_lt_rpow`: factor recovery under
  `|a * p - b * q| < (4 * a * b * p * q) ^ (1 / 4)` and under the book's bound `n ^ (1 / 4)`
  for positive `a`, `b`.
- `RSADesc.fermatFactorLinear_eq_of_lt_rpow`: RSA modulus wrapper using `¬ desc.q ∣ 2 * a` and
  `¬ desc.p ∣ 2 * b`.
- `computableInPolyTime_fermatFactorLinear`, `computableInPolyTime_fermatFactorLinear_prod`:
  polynomial-time computability certificates.

## References

- [BonehShoup2023], Section 16.4.2.1 (p. 699) and Exercise 16.14 (p. 710).
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- Factors `n = p * q` when `a * p` and `b * q` are close, by applying `fermatFactor` to
`4 * a * b * n = (2 * a * p) * (2 * b * q)` and taking gcds with `n`. -/
@[expose] def fermatFactorLinear (a b n : ℕ) : ℕ × ℕ :=
  let (u, v) := fermatFactor (4 * a * b * n)
  (Nat.gcd u n, Nat.gcd v n)

private theorem close_double_of_abs_mul_sub_mul_lt {a b p q : ℕ}
    (hclose : |(a : ℝ) * p - b * q| < (4 * (a : ℝ) * b * p * q) ^ (1 / 4 : ℝ)) :
    |((2 * a * p : ℕ) : ℝ) - (2 * b * q : ℕ)| <
      2 * (((2 * a * p : ℕ) : ℝ) * (2 * b * q : ℕ)) ^ (1 / 4 : ℝ) := by
  have h1 : |((2 * a * p : ℕ) : ℝ) - (2 * b * q : ℕ)| = 2 * |(a : ℝ) * p - b * q| := by
    push_cast
    rw [show 2 * (a : ℝ) * p - 2 * b * q = 2 * ((a : ℝ) * p - b * q) by ring, abs_mul,
      abs_of_pos two_pos]
  have h2 : (((2 * a * p : ℕ) : ℝ) * (2 * b * q : ℕ)) = 4 * (a : ℝ) * b * p * q := by
    push_cast
    ring
  rw [h1, h2]
  linarith

/-- Under `|(a : ℝ) * p - b * q| < (4 * a * b * p * q) ^ (1 / 4)`, `fermatFactor` on
`4 * a * b * (p * q)` returns `(2 * a * p, 2 * b * q)` when `b * q ≤ a * p` and the swapped
pair otherwise. -/
theorem fermatFactor_four_mul_eq {a b p q : ℕ}
    (hclose : |(a : ℝ) * p - b * q| < (4 * (a : ℝ) * b * p * q) ^ (1 / 4 : ℝ)) :
    fermatFactor (4 * a * b * (p * q)) =
      if b * q ≤ a * p then (2 * a * p, 2 * b * q) else (2 * b * q, 2 * a * p) := by
  have hev : Even (2 * a * p + 2 * b * q) := ⟨a * p + b * q, by ring⟩
  have hprod : 4 * a * b * (p * q) = (2 * a * p) * (2 * b * q) := by ring
  have hcd := close_double_of_abs_mul_sub_mul_lt hclose
  rw [hprod]
  split_ifs with hle
  · exact fermatFactor_mul_eq (by simpa only [mul_assoc] using Nat.mul_le_mul_left 2 hle) hev hcd
  · rw [mul_comm (2 * a * p)]
    rw [abs_sub_comm, mul_comm ((2 * a * p : ℕ) : ℝ)] at hcd
    exact fermatFactor_mul_eq
      (by simpa only [mul_assoc] using Nat.mul_le_mul_left 2 (le_of_not_ge hle))
      (add_comm (2 * a * p) (2 * b * q) ▸ hev) hcd

/-- `fermatFactorLinear a b (p * q)` recovers `(p, q)` when `b * q ≤ a * p` and `(q, p)`
otherwise, under `Nat.Coprime (2 * a) q`, `Nat.Coprime (2 * b) p`, and
`|(a : ℝ) * p - b * q| < (4 * a * b * p * q) ^ (1 / 4)`. -/
theorem fermatFactorLinear_mul_eq {a b p q : ℕ}
    (hcop_a : Nat.Coprime (2 * a) q) (hcop_b : Nat.Coprime (2 * b) p)
    (hclose : |(a : ℝ) * p - b * q| < (4 * (a : ℝ) * b * p * q) ^ (1 / 4 : ℝ)) :
    fermatFactorLinear a b (p * q) = if b * q ≤ a * p then (p, q) else (q, p) := by
  have hg₁ : Nat.gcd (2 * a * p) (p * q) = p := by
    rw [show 2 * a * p = p * (2 * a) by ring, Nat.gcd_mul_left, hcop_a, mul_one]
  have hg₂ : Nat.gcd (2 * b * q) (p * q) = q := by
    rw [show 2 * b * q = q * (2 * b) by ring, mul_comm p q, Nat.gcd_mul_left, hcop_b, mul_one]
  rw [fermatFactorLinear, fermatFactor_four_mul_eq hclose]
  split_ifs <;> simp [hg₁, hg₂]

/-- Corollary of `fermatFactorLinear_mul_eq` under the textbook bound
`|(a : ℝ) * p - b * q| < ((p : ℝ) * q) ^ (1 / 4 : ℝ)` for positive integers `a` and `b`. -/
theorem fermatFactorLinear_mul_eq_of_lt_rpow {a b p q : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (hcop_a : Nat.Coprime (2 * a) q) (hcop_b : Nat.Coprime (2 * b) p)
    (hclose : |(a : ℝ) * p - b * q| < ((p : ℝ) * q) ^ (1 / 4 : ℝ)) :
    fermatFactorLinear a b (p * q) = if b * q ≤ a * p then (p, q) else (q, p) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hab : (1 : ℝ) ≤ 4 * a * b := by nlinarith
  have hle : (p : ℝ) * q ≤ 4 * (a : ℝ) * b * p * q := by
    have hpq : 0 ≤ (p : ℝ) * q := by positivity
    calc (p : ℝ) * q = 1 * (p * q) := (one_mul _).symm
      _ ≤ 4 * a * b * (p * q) := mul_le_mul_of_nonneg_right hab hpq
      _ = 4 * a * b * p * q := by ring
  have hrpow : ((p : ℝ) * q) ^ (1 / 4 : ℝ) ≤ (4 * (a : ℝ) * b * p * q) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hle (by positivity)
  exact fermatFactorLinear_mul_eq hcop_a hcop_b (hclose.trans_le hrpow)

/-- Textbook-bound `RSADesc` wrapper: if `¬ desc.q ∣ 2 * a`, `¬ desc.p ∣ 2 * b`, and
`|a * desc.p - b * desc.q| < desc.modulus ^ (1 / 4)`, then `fermatFactorLinear a b desc.modulus`
recovers `(desc.p, desc.q)` up to order. -/
theorem RSADesc.fermatFactorLinear_eq_of_lt_rpow (desc : RSADesc) {a b : ℕ}
    (ha : ¬ desc.q ∣ 2 * a) (hb : ¬ desc.p ∣ 2 * b)
    (hclose : |(a : ℝ) * desc.p - b * desc.q| < (desc.modulus : ℝ) ^ (1 / 4 : ℝ)) :
    fermatFactorLinear a b desc.modulus =
      if b * desc.q ≤ a * desc.p then (desc.p, desc.q) else (desc.q, desc.p) := by
  have ha0 : 0 < a := Nat.pos_of_ne_zero fun h => ha (by simp [h])
  have hb0 : 0 < b := Nat.pos_of_ne_zero fun h => hb (by simp [h])
  have hcop_a : Nat.Coprime (2 * a) desc.q := (desc.hq.coprime_iff_not_dvd.2 ha).symm
  have hcop_b : Nat.Coprime (2 * b) desc.p := (desc.hp.coprime_iff_not_dvd.2 hb).symm
  exact fermatFactorLinear_mul_eq_of_lt_rpow ha0 hb0 hcop_a hcop_b
    (by simpa [RSADesc.modulus] using hclose)

/-- `fermatFactorLinear` is computable in polynomial time (compositionally). -/
@[fun_prop]
theorem computableInPolyTime_fermatFactorLinear {α : Type} {enc : α ↪ List Bool}
    {a b n : α → ℕ}
    (ha : ComputableInPolyTime a enc encNat)
    (hb : ComputableInPolyTime b enc encNat)
    (hn : ComputableInPolyTime n enc encNat) :
    ComputableInPolyTime (fun x => fermatFactorLinear (a x) (b x) (n x))
      enc (encPair encNat encNat) := by
  unfold fermatFactorLinear
  have harg : ComputableInPolyTime (fun x => 4 * a x * b x * n x) enc encNat := by fun_prop
  have huv : ComputableInPolyTime (fun x => fermatFactor (4 * a x * b x * n x))
      enc (encPair encNat encNat) :=
    computableInPolyTime_fermatFactor.comp harg
  exact (ComputableInPolyTime.binary_gcd' huv.fst' hn).prod
    (ComputableInPolyTime.binary_gcd' huv.snd' hn)

/-- `fermatFactorLinear` is computable in polynomial time on `((a, b), n)`. -/
theorem computableInPolyTime_fermatFactorLinear_prod :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => fermatFactorLinear p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) encNat) (encPair encNat encNat) :=
  computableInPolyTime_fermatFactorLinear (by fun_prop) (by fun_prop) (by fun_prop)

end Cslib.Crypto
