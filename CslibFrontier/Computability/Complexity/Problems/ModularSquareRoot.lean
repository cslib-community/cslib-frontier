/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.PolyTime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Square roots modulo a prime (Goldreich, Exercise 6.16, items 1–3)

[Goldreich, Exercise 6.16][Goldreich2007Draft] (February 2007 `r3.pdf`, PDF p. 55 / printed
p. 257) builds a probabilistic polynomial-time algorithm that, given a prime `P` and a quadratic
residue `s` modulo `P`, finds a square root of `s` modulo `P`. Its first three items are the
deterministic part:

1. if `P ≡ 3 (mod 4)`, then `s ^ ((P + 1) / 4)` is a square root of `s`
   (`ModularSquareRoot.pow_add_one_div_four_sq_modEq`);
2. if `s ^ e * t ^ e' ≡ 1` for an odd `e` and an even `e'`, then
   `s ^ ((e + 1) / 2) * t ^ (e' / 2)` is a square root of `s`
   (`ModularSquareRoot.sq_eq_of_pow_mul_pow_eq_one`);
3. given a quadratic non-residue `t`, such `e` and `e'` are found deterministically in polynomial
   time (`ModularSquareRoot.descentExponents_spec`,
   `ModularSquareRoot.computableInPolyTime_descentExponents`).

Item 3 is the descent of the source's footnote 23. Start from `e = P / 2` and `e' = 0`, so that
`s ^ e * t ^ e' = 1` by Euler's criterion. While `e` is even, `x = s ^ (e / 2) * t ^ (e' / 2)`
squares to `1`, so `x = ±1`; halve both exponents, and if `x = -1` also add `P / 2` to `e'`,
using `t ^ (P / 2) = -1`. Throughout, `2 * e` divides `e'`, so `e'` is even once `e` is odd.
`e` reaches its odd part after at most `log₂ P` halvings; the loop runs `Nat.size P` rounds. When
`P ≡ 3 (mod 4)`, `P / 2` is already odd and the loop does nothing, so the same algorithm returns
the root of item 1 and needs no non-residue.

`ModularSquareRoot.sqrtMod` combines items 2 and 3 into a native polynomial-time algorithm
(`ModularSquareRoot.computableInPolyTime_sqrtMod`, `ModularSquareRoot.sqrtMod_sq`). Item 4 and the
randomized search for a non-residue are not formalized here: the source's item 4 needs the
correction recorded in the exercise inventory (row 6.16(4)).

## Main definitions

* `Cslib.Complexity.ModularSquareRoot.descentStep`, `descentExponents`: footnote 23's descent.
* `Cslib.Complexity.ModularSquareRoot.sqrtMod`: the square root it produces.

## Main results

* `Cslib.Complexity.ModularSquareRoot.pow_add_one_div_four_sq_modEq`: item 1.
* `Cslib.Complexity.ModularSquareRoot.sq_eq_of_pow_mul_pow_eq_one`: item 2.
* `Cslib.Complexity.ModularSquareRoot.descentExponents_spec`,
  `Cslib.Complexity.ModularSquareRoot.computableInPolyTime_descentExponents`: item 3.
* `Cslib.Complexity.ModularSquareRoot.sqrtMod_sq`,
  `Cslib.Complexity.ModularSquareRoot.computableInPolyTime_sqrtMod`: the deterministic square-root
  algorithm given a non-residue.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

public section

namespace Cslib.Complexity.ModularSquareRoot

open Turing.MultiTapeTM

/-- **Goldreich, Exercise 6.16, item 1.** For a prime `p ≡ 3 (mod 4)` and a quadratic residue `y`
modulo `p`, `y ^ ((p + 1) / 4) mod p` is a square root of `y` modulo `p`. -/
theorem pow_add_one_div_four_sq_modEq {p y : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    (hsq : ∃ x : ℕ, x ^ 2 ≡ y [MOD p]) :
    (y ^ ((p + 1) / 4) % p) ^ 2 ≡ y [MOD p] := by
  rcases hsq with ⟨x, hx⟩
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_natCast_iff] at hx ⊢
  push_cast at hx ⊢
  rw [ZMod.natCast_mod, Nat.cast_pow, ← hx]
  by_cases hx0 : (x : ZMod p) = 0
  · have hpos : 0 < (p + 1) / 4 := by omega
    rw [hx0, zero_pow (by norm_num), zero_pow (Nat.ne_of_gt hpos), zero_pow (by norm_num)]
  · have h4 : 4 * ((p + 1) / 4) = p + 1 := by omega
    calc
      (((x : ZMod p) ^ 2) ^ ((p + 1) / 4)) ^ 2
          = (x : ZMod p) ^ (4 * ((p + 1) / 4)) := by ring
      _ = (x : ZMod p) ^ (p + 1) := by rw [h4]
      _ = (x : ZMod p) ^ (p - 1) * (x : ZMod p) ^ 2 := by
        have hp1 : 1 ≤ p := hp.one_lt.le
        rw [← pow_add, show p - 1 + 2 = p + 1 by omega]
      _ = 1 * (x : ZMod p) ^ 2 := by rw [ZMod.pow_card_sub_one_eq_one hx0]
      _ = (x : ZMod p) ^ 2 := one_mul _

/-- **Goldreich, Exercise 6.16, item 2.** If `s ^ e * t ^ e' = 1` with `e` odd and `e'` even, then
`s ^ ((e + 1) / 2) * t ^ (e' / 2)` is a square root of `s`. -/
theorem sq_eq_of_pow_mul_pow_eq_one {M : Type*} [CommMonoid M] {s t : M} {e e' : ℕ} (he : Odd e)
    (he' : Even e') (h : s ^ e * t ^ e' = 1) : (s ^ ((e + 1) / 2) * t ^ (e' / 2)) ^ 2 = s := by
  obtain ⟨k, rfl⟩ := he
  obtain ⟨k', rfl⟩ := he'
  have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h2 : (k' + k') / 2 = k' := by omega
  rw [h1, h2, mul_pow, ← pow_mul, ← pow_mul, show (k + 1) * 2 = (2 * k + 1) + 1 by ring,
    show k' * 2 = k' + k' by ring, pow_succ, mul_right_comm, h, one_mul]

/-- One round of the descent of footnote 23 on the exponent pair `(e, e')`: if `e` is even, halve
both exponents and, when `s ^ (e / 2) * t ^ (e' / 2)` is not `1` modulo `P`, add `P / 2` to the
second; if `e` is odd, stop. -/
@[expose] def descentStep (P s t : ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  if st.1 % 2 = 0 then
    if powMod P s (st.1 / 2) * powMod P t (st.2 / 2) % P = 1 then (st.1 / 2, st.2 / 2)
    else (st.1 / 2, st.2 / 2 + P / 2)
  else st

/-- **The exponents of footnote 23**: `Nat.size P` descent rounds from `(P / 2, 0)`. -/
@[expose] def descentExponents (P s t : ℕ) : ℕ × ℕ :=
  (descentStep P s t)^[P.size] (P / 2, 0)

/-- The square root of `s` modulo `P` found with the non-residue `t`:
`s ^ ((e + 1) / 2) * t ^ (e' / 2) mod P` for the descent exponents `(e, e')`. -/
@[expose] def sqrtMod (P s t : ℕ) : ℕ :=
  let exps := descentExponents P s t
  powMod P s ((exps.1 + 1) / 2) * powMod P t (exps.2 / 2) % P

/-! ### Correctness -/

section Correctness

variable {P s t : ℕ}

/-- The descent invariant after `i` rounds: `e` divides `P / 2` and is odd or equal to
`(P / 2) / 2 ^ i`, `2 * e` divides `e'`, and `s ^ e * t ^ e' = 1` modulo `P`. -/
private def Inv (P s t : ℕ) (i : ℕ) (st : ℕ × ℕ) : Prop :=
  st.1 ∣ P / 2 ∧ (st.1 % 2 = 1 ∨ st.1 * 2 ^ i = P / 2) ∧ 2 * st.1 ∣ st.2 ∧
    (s : ZMod P) ^ st.1 * (t : ZMod P) ^ st.2 = 1

/-- The test of a descent round computes, modulo `P`, whether `s ^ a * t ^ b = 1`. -/
private theorem test_iff (hP : 1 < P) (a b : ℕ) :
    powMod P s a * powMod P t b % P = 1 ↔ (s : ZMod P) ^ a * (t : ZMod P) ^ b = 1 := by
  rw [powMod_of_ne_zero (by omega), powMod_of_ne_zero (by omega)]
  have hcast : (((s ^ a % P) * (t ^ b % P) % P : ℕ) : ZMod P) =
      (s : ZMod P) ^ a * (t : ZMod P) ^ b := by
    push_cast [ZMod.natCast_mod]
    rfl
  rw [← hcast, show (1 : ZMod P) = ((1 : ℕ) : ZMod P) from Nat.cast_one.symm,
    ZMod.natCast_eq_natCast_iff', Nat.mod_mod, Nat.one_mod_eq_one.mpr (by omega)]

private theorem inv_descentStep [Fact P.Prime] (ht : P % 4 = 3 ∨ (t : ZMod P) ^ (P / 2) = -1)
    {i : ℕ} {st : ℕ × ℕ} (h : Inv P s t i st) : Inv P s t (i + 1) (descentStep P s t st) := by
  obtain ⟨e, e'⟩ := st
  obtain ⟨hdvd, hodd, hdvd', hone⟩ := h
  dsimp only at hdvd hodd hdvd' hone
  have hP : 1 < P := (Fact.out : P.Prime).one_lt
  unfold descentStep
  dsimp only
  by_cases he : e % 2 = 0
  swap
  · rw [ite_eq_right he]
    exact ⟨hdvd, by omega, hdvd', hone⟩
  rw [ite_eq_left he]
  obtain ⟨k, rfl⟩ : 2 ∣ e := Nat.dvd_of_mod_eq_zero he
  obtain ⟨m, rfl⟩ := hdvd'
  have h2 : 2 * (2 * k) * m / 2 = 2 * k * m := by
    rw [show 2 * (2 * k) * m = 2 * (2 * k * m) by ring, Nat.mul_div_cancel_left _ two_pos]
  have hodd' : k * 2 ^ (i + 1) = P / 2 := by
    rcases hodd with h | h
    · omega
    · rw [pow_succ, ← h]
      ring
  have hk : k ∣ P / 2 := Nat.dvd_trans (Dvd.intro_left 2 rfl) hdvd
  simp only [Nat.mul_div_cancel_left k two_pos, h2]
  split_ifs with hx <;> rw [test_iff hP] at hx
  · -- `x = 1`: halve both exponents.
    exact ⟨hk, Or.inr hodd', ⟨m, by ring⟩, hx⟩
  · -- `x = -1`: also multiply by `t ^ (P / 2) = -1`.
    have htm : (t : ZMod P) ^ (P / 2) = -1 := by
      rcases ht with h3 | h
      · exfalso
        have : 2 ∣ P / 2 := ⟨k * 2 ^ i, by rw [← hodd', pow_succ]; ring⟩
        omega
      · exact h
    have hsq : ((s : ZMod P) ^ k * (t : ZMod P) ^ (2 * k * m)) *
        ((s : ZMod P) ^ k * (t : ZMod P) ^ (2 * k * m)) = 1 := by
      rw [← hone]
      ring
    have hneg := (mul_self_eq_one_iff.mp hsq).resolve_left hx
    refine ⟨hk, Or.inr hodd', Nat.dvd_add ⟨m, by ring⟩ hdvd, ?_⟩
    rw [pow_add, ← mul_assoc, hneg, htm]
    norm_num

private theorem inv_iterate [Fact P.Prime] (hs : (s : ZMod P) ^ (P / 2) = 1)
    (ht : P % 4 = 3 ∨ (t : ZMod P) ^ (P / 2) = -1) (i : ℕ) :
    Inv P s t i ((descentStep P s t)^[i] (P / 2, 0)) := by
  induction i with
  | zero => exact ⟨dvd_rfl, Or.inr (by simp), dvd_zero _, by simpa using hs⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact inv_descentStep ht ih

/-- **Goldreich, Exercise 6.16, item 3.** For a prime `P`, a non-zero quadratic residue `s`
and a quadratic non-residue `t` (`t ^ (P / 2) = -1`, Euler's criterion), the descent finds an odd
`e` and an even `e'` with `s ^ e * t ^ e' = 1` modulo `P`. When `P ≡ 3 (mod 4)` no non-residue is
needed. -/
theorem descentExponents_spec (hP : P.Prime) (hs0 : (s : ZMod P) ≠ 0)
    (hs : IsSquare (s : ZMod P)) (ht : P % 4 = 3 ∨ (t : ZMod P) ^ (P / 2) = -1) :
    Odd (descentExponents P s t).1 ∧ Even (descentExponents P s t).2 ∧
      (s : ZMod P) ^ (descentExponents P s t).1 * (t : ZMod P) ^ (descentExponents P s t).2 =
        1 := by
  have : Fact P.Prime := ⟨hP⟩
  unfold descentExponents
  obtain ⟨hdvd, hodd, hdvd', hone⟩ :=
    inv_iterate ((ZMod.euler_criterion P hs0).mp hs) ht P.size
  set e := ((descentStep P s t)^[P.size] (P / 2, 0)).1
  have hpos : 0 < P / 2 := by have := hP.two_le; omega
  have he : e % 2 = 1 := by
    rcases hodd with h | h
    · exact h
    · exfalso
      have hlt : P / 2 < 2 ^ P.size := (Nat.div_le_self _ _).trans_lt (Nat.lt_size_self P)
      have he0 : e ≠ 0 := fun h0 => by rw [h0, zero_dvd_iff] at hdvd; omega
      have hle : 2 ^ P.size ≤ e * 2 ^ P.size := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero he0)
      omega
  exact ⟨Nat.odd_iff.mpr he, even_iff_two_dvd.mpr ((Dvd.intro e rfl).trans hdvd'), hone⟩

/-- The first descent exponent stays positive: it starts at `P / 2 ≥ 1` and only an even one is
halved. -/
private theorem one_le_iterate_fst (hP : 2 ≤ P) (i : ℕ) :
    1 ≤ ((descentStep P s t)^[i] (P / 2, 0)).1 := by
  induction i with
  | zero => exact Nat.div_pos hP two_pos
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    generalize (descentStep P s t)^[i] (P / 2, 0) = st at ih ⊢
    obtain ⟨e, e'⟩ := st
    dsimp only at ih
    unfold descentStep
    dsimp only
    split_ifs <;> dsimp only <;> omega

/-- **A square root modulo a prime from a non-residue.** For a prime `P`, a quadratic residue `s`
modulo `P` (zero included) and a quadratic non-residue `t`, `sqrtMod P s t` is a square root of
`s` modulo `P` (Goldreich, Exercise 6.16, items 2 and 3). When `P ≡ 3 (mod 4)` no non-residue is
needed, and the result is `s ^ ((P + 1) / 4) mod P` of item 1. -/
theorem sqrtMod_sq (hP : P.Prime) (hs : IsSquare (s : ZMod P))
    (ht : P % 4 = 3 ∨ (t : ZMod P) ^ (P / 2) = -1) : (sqrtMod P s t : ZMod P) ^ 2 = s := by
  have hcast : (sqrtMod P s t : ZMod P) = (s : ZMod P) ^ (((descentExponents P s t).1 + 1) / 2) *
      (t : ZMod P) ^ ((descentExponents P s t).2 / 2) := by
    rw [sqrtMod, powMod_of_ne_zero hP.ne_zero, powMod_of_ne_zero hP.ne_zero]
    push_cast [ZMod.natCast_mod]
    rfl
  rw [hcast]
  by_cases hs0 : (s : ZMod P) = 0
  · have h1 := one_le_iterate_fst (s := s) (t := t) hP.two_le P.size
    rw [hs0, zero_pow (by unfold descentExponents; omega), zero_mul,
      zero_pow two_ne_zero]
  · obtain ⟨he, he', hone⟩ := descentExponents_spec hP hs0 hs ht
    exact sq_eq_of_pow_mul_pow_eq_one he he' hone

end Correctness

/-! ### Running time -/

section RunningTime

private theorem computableInPolyTime_descentStep :
    ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) => descentStep p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair encNat (encPair encNat encNat)) (encPair encNat encNat))
      (encPair encNat encNat) := by
  let enc := encPair (encPair encNat (encPair encNat encNat)) (encPair encNat encNat)
  have two : ComputableInPolyTime (fun _ : (ℕ × ℕ × ℕ) × (ℕ × ℕ) => (2 : ℕ)) enc encNat :=
    ComputableInPolyTime.const 2
  have hP : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) => p.1.1) enc encNat := by
    fun_prop
  have he : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) => p.2.1 / 2) enc encNat :=
    ComputableInPolyTime.binary_div' (by fun_prop) two
  have he' : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) => p.2.2 / 2) enc encNat :=
    ComputableInPolyTime.binary_div' (by fun_prop) two
  have hhalf : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) => p.1.1 / 2) enc encNat :=
    ComputableInPolyTime.binary_div' hP two
  have hpar : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) => decide (p.2.1 % 2 = 0))
      enc encBool :=
    ComputableInPolyTime.decide_eq' (ComputableInPolyTime.binary_mod' (by fun_prop) two)
      (ComputableInPolyTime.const 0)
  have hs := computableInPolyTime_powMod hP (x := fun p => p.1.2.1) (by fun_prop) he
  have ht := computableInPolyTime_powMod hP (x := fun p => p.1.2.2) (by fun_prop) he'
  have htest : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) =>
      decide (powMod p.1.1 p.1.2.1 (p.2.1 / 2) * powMod p.1.1 p.1.2.2 (p.2.2 / 2) % p.1.1 = 1))
      enc encBool :=
    ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.binary_mod' (ComputableInPolyTime.binary_mul' hs ht) hP)
      (ComputableInPolyTime.const 1)
  have hkeep : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) => (p.2.1 / 2, p.2.2 / 2))
      enc (encPair encNat encNat) := he.prod he'
  have hadd : ComputableInPolyTime
      (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ) => (p.2.1 / 2, p.2.2 / 2 + p.1.1 / 2))
      enc (encPair encNat encNat) := he.prod (ComputableInPolyTime.binary_add' he' hhalf)
  exact ComputableInPolyTime.ite_decide hpar (ComputableInPolyTime.ite_decide htest hkeep hadd)
    (by fun_prop)

/-- The descent keeps both exponents at most `P`. -/
private theorem descentStep_le {P s t : ℕ} {st : ℕ × ℕ} (h : st.1 ≤ P ∧ st.2 ≤ P) :
    (descentStep P s t st).1 ≤ P ∧ (descentStep P s t st).2 ≤ P := by
  obtain ⟨e, e'⟩ := st
  dsimp only at h
  unfold descentStep
  dsimp only
  split_ifs <;> dsimp only <;> omega

private theorem computableInPolyTime_descentExponents_triple :
    ComputableInPolyTime (fun x : ℕ × ℕ × ℕ => descentExponents x.1 x.2.1 x.2.2)
      (encPair encNat (encPair encNat encNat)) (encPair encNat encNat) := by
  refine (ComputableInPolyTime.iterateWith_spec (par := fun x : ℕ × ℕ × ℕ => x)
    (count := fun x => x.1.size) (init := fun x => (x.1 / 2, 0))
    (step := fun x st => descentStep x.1 x.2.1 x.2.2 st)
    ComputableInPolyTime.id' (by fun_prop) (by fun_prop) computableInPolyTime_descentStep
    (fun x _ st => st.1 ≤ x.1 ∧ st.2 ≤ x.1)
    (fun x => ⟨Nat.div_le_self _ _, Nat.zero_le _⟩)
    (fun _ _ _ _ h => descentStep_le h)
    (size := fun x => 2 * (encPair encNat (encPair encNat encNat) x).length + 2) ?_ ?_).1
  · exact PolyBounded.of_forall_le 2 1 fun x => by simp only [pow_one]; omega
  · rintro ⟨P, s, t⟩ _ ⟨e, e'⟩ _ ⟨he, he'⟩
    have h1 := length_encNat_mono he
    have h2 := length_encNat_mono he'
    dsimp only at h1 h2 ⊢
    enc_len

/-- **Item 3 runs in polynomial time**: the descent exponents are computable in polynomial time,
from binary naturals to a pair of binary naturals. -/
theorem computableInPolyTime_descentExponents {α : Type} {input : α ↪ List Bool}
    {P s t : α → ℕ} (hP : ComputableInPolyTime P input encNat)
    (hs : ComputableInPolyTime s input encNat) (ht : ComputableInPolyTime t input encNat) :
    ComputableInPolyTime (fun a => descentExponents (P a) (s a) (t a)) input
      (encPair encNat encNat) := by
  have h := computableInPolyTime_descentExponents_triple.comp (hP.prod (hs.prod ht))
  simp only [Function.comp_def] at h
  exact h

/-- **The square-root algorithm runs in polynomial time**, on binary naturals. -/
theorem computableInPolyTime_sqrtMod {α : Type} {input : α ↪ List Bool} {P s t : α → ℕ}
    (hP : ComputableInPolyTime P input encNat) (hs : ComputableInPolyTime s input encNat)
    (ht : ComputableInPolyTime t input encNat) :
    ComputableInPolyTime (fun a => sqrtMod (P a) (s a) (t a)) input encNat := by
  have hd := computableInPolyTime_descentExponents hP hs ht
  have h1 := computableInPolyTime_powMod hP hs
    (e := fun a => ((descentExponents (P a) (s a) (t a)).1 + 1) / 2) (by fun_prop)
  have h2 := computableInPolyTime_powMod hP ht
    (e := fun a => (descentExponents (P a) (s a) (t a)).2 / 2) (by fun_prop)
  simp only [sqrtMod]
  exact ComputableInPolyTime.binary_mod' (ComputableInPolyTime.binary_mul' h1 h2) hP

end RunningTime

end Cslib.Complexity.ModularSquareRoot
