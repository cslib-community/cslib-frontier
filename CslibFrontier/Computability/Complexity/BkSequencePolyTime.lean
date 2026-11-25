/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.Additive.BkSequence
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime

/-!
# Polynomial-time constructibility of Sergeev's explicit `B_k`-sequence

Sergeev ([Sergeev2023BkSequence], Abstract and pp. 2–3) shows that the size-`n` `B_k`-sequence
`H[n, k]` (`Cslib.sergeevBkSequence n k`) is computable in time `(n + k) ^ O(1)` with output
elements represented in binary:

1. The first `n` odd primes (`Cslib.firstOddPrimes n`) lie below
   `Cslib.primeSearchBound n = (n + 2) * (2 * ⌊log₂(n + 2)⌋ + 4)` and are found in unary
   polynomial time by trial division (`Cslib.Complexity.computableInPolyTime_firstOddPrimes`).
2. Given modulus exponent `r` in unary and odd input `x` in binary, the base-`5` discrete logarithm
   `Cslib.dlogFiveModTwoPow r x` extracts `r - 2` binary digits sequentially via modular
   exponentiation modulo `2 ^ r`, maintaining an accumulator strictly below `2 ^ r`
   (`Cslib.Complexity.computableInPolyTime_dlogFiveModTwoPow`).
3. Combining the unary modulus exponent `Cslib.sergeevModulusExp n k = O(k log(n + 2))` with
   `dlogFiveModTwoPow` over `firstOddPrimes n` certifies `Cslib.sergeevBkSequence` from unary
   `(n, k)` (`encPair encUnary encUnary`) to a framed list of binary naturals (`encList encNat`)
   (`Cslib.Complexity.computableInPolyTime_sergeevBkSequence`).

## Main results

* `Cslib.Complexity.computableInPolyTime_firstOddPrimes`: `firstOddPrimes` is computable in
  polynomial time from unary `n` to unary prime entries.
* `Cslib.Complexity.computableInPolyTime_dlogFiveModTwoPow`: `dlogFiveModTwoPow` is computable in
  polynomial time from `(r, x)` under `encPair encUnary encNat` to `encNat`.
* `Cslib.Complexity.computableInPolyTime_sergeevModulusExp`: `sergeevModulusExp` is computable in
  polynomial time from unary `(n, k)` (`encPair encUnary encUnary`) to `encUnary`.
* `Cslib.Complexity.computableInPolyTime_sergeevBkSequence`: `sergeevBkSequence` is computable in
  polynomial time from unary `(n, k)` (`encPair encUnary encUnary`) to binary entries
  (`encList encNat`).

## References

* [I. S. Sergeev, *An Explicit Finite $B_k$-Sequence*][Sergeev2023BkSequence], arXiv:2304.03988v1,
  pp. 1–3.
-/

public section

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

namespace Cslib.Complexity

/-- Computing the first `n` odd primes from unary `n` (`encUnary`) produces a framed list of unary
primes (`encList encUnary`) in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_firstOddPrimes :
    ComputableInPolyTime firstOddPrimes encUnary (encList encUnary) := by
  unfold firstOddPrimes primeSearchBound; fun_prop

/-- Computing Sergeev's base-`5` discrete logarithm `dlogFiveModTwoPow r x` from unary modulus
exponent `r` and binary integer `x` (`encPair encUnary encNat`) produces a binary natural
(`encNat`) in polynomial time ([Sergeev2023BkSequence], pp. 2–3). -/
@[fun_prop]
theorem computableInPolyTime_dlogFiveModTwoPow :
    ComputableInPolyTime (fun p : ℕ × ℕ => dlogFiveModTwoPow p.1 p.2)
      (encPair encUnary encNat) encNat := by
  let normX : ℕ × ℕ → ℕ := fun p =>
    if p.2 % 4 = 1 then p.2 % 2 ^ p.1 else (2 ^ p.1 - p.2 % 2 ^ p.1) % 2 ^ p.1
  have hnormX : ComputableInPolyTime normX (encPair encUnary encNat) encNat := by
    have h2r : ComputableInPolyTime (fun p : ℕ × ℕ => 2 ^ p.1) _ _ :=
      binary_two_pow.comp (fst encUnary encNat)
    have hx := snd encUnary encNat
    have hxmod2r := binary_mod' hx h2r
    exact (decide_eq' (binary_mod' hx (.const 4)) (.const 1)).ite_decide hxmod2r
      (binary_mod' (binary_sub' h2r hxmod2r) h2r)
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × ℕ) × ℕ => dlogFiveStep q.1.1.1 q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair encUnary encNat) encNat) encUnary) encNat := by
    have hstate := fst (encPair (encPair encUnary encNat) encNat) encUnary
    have hi := snd (encPair (encPair encUnary encNat) encNat) encUnary
    have hr := hstate.fst'.fst'
    have ha := hstate.snd'
    have h2r : ComputableInPolyTime (fun q : ((ℕ × ℕ) × ℕ) × ℕ => 2 ^ q.1.1.1) _ _ :=
      binary_two_pow.comp hr
    have hsub (c : ℕ) : ComputableInPolyTime (fun q : ((ℕ × ℕ) × ℕ) × ℕ => q.1.1.1 - c) _ _ :=
      unary_sub.comp (hr.prod (.const c))
    have hinv5a := binary_powMod (.const 5) (binary_sub' (binary_two_pow.comp (hsub 2)) ha) h2r
      fun _ => Nat.two_pow_pos _
    have hprod := binary_mod' (binary_mul' hinv5a hstate.fst'.snd') h2r
    have hu := binary_powMod hprod (binary_two_pow.comp (unary_sub.comp ((hsub 3).prod hi))) h2r
      fun _ => Nat.two_pow_pos _
    have htarget := binary_add' (binary_two_pow.comp (hsub 1)) (.const 1)
    refine ((decide_eq' hu htarget).ite_decide (binary_add' ha (binary_two_pow.comp hi))
      ha).of_enc_eq fun q => ?_
    simp only [dlogFiveStep, Nat.powMod_def, Function.comp_apply]
  exact foldlWith (encP := encPair encUnary encNat) (encA := encUnary)
    (encL := encList encUnary) (encB := encNat)
    (step := fun (rx : ℕ × ℕ) (a i : ℕ) => dlogFiveStep rx.1 rx.2 a i)
    ((fst encUnary encNat).prod hnormX)
    (show ComputableInPolyTime (fun p : ℕ × ℕ => List.range (p.1 - 2)) _ _ by fun_prop)
    (.const 0) hstep (B := fun p => (encPair encUnary encNat p).length) PolyBounded.self
    fun p j hj => by
      rw [List.length_range] at hj
      have hlt : ((List.range (p.1 - 2)).take j).foldl (dlogFiveStep p.1 (normX p)) 0 < 2 ^ p.1 :=
        (foldl_dlogFiveStep_take_lt p.1 (normX p) (p.1 - 2) j hj).trans_le
          (Nat.pow_le_pow_right (by decide) (by omega))
      rw [encNat_apply, Nat.size_eq_bits_len]
      refine (Nat.size_le.mpr hlt).trans ?_
      simpa only [encUnary_apply, List.length_replicate] using
        length_le_encPair_left encUnary encNat p

/-- Computing Sergeev's modulus exponent `sergeevModulusExp n k` from unary `(n, k)`
(`encPair encUnary encUnary`) produces a unary exponent (`encUnary`) in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_sergeevModulusExp :
    ComputableInPolyTime (fun p : ℕ × ℕ => sergeevModulusExp p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  have hn := fst encUnary encUnary
  have hlast := listGetDWithInput (computableInPolyTime_firstOddPrimes.comp hn)
    (unary_sub.comp (hn.prod (.const 1))) 3
  have hclog := binary_clog_two.comp
    (binary_pow' (unary_to_binary.comp hlast) (snd encUnary encUnary))
  exact unary_max.comp ((const 3).prod (unary_add.comp ((const 1).prod hclog)))

/-- **Explicitness of Sergeev's `B_k`-sequence** ([Sergeev2023BkSequence], Abstract and pp. 2–3):
given `(n, k)` in unary (`encPair encUnary encUnary`), `sergeevBkSequence n k` is computable in
polynomial time (`(n + k) ^ O(1)` steps) as a framed list of binary naturals (`encList encNat`). -/
@[fun_prop]
theorem computableInPolyTime_sergeevBkSequence :
    ComputableInPolyTime (fun p : ℕ × ℕ => sergeevBkSequence p.1 p.2)
      (encPair encUnary encUnary) (encList encNat) :=
  mapWith (computableInPolyTime_dlogFiveModTwoPow.comp
      ((fst encUnary encUnary).prod (unary_to_binary.comp (snd encUnary encUnary))))
    computableInPolyTime_sergeevModulusExp
    (computableInPolyTime_firstOddPrimes.comp (fst encUnary encUnary))

end Cslib.Complexity

end
