/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Tactic.PolyTime.Init
import Mathlib.Data.ZMod.Basic

/-!
# Polynomial-time modular exponentiation

Square-and-multiply computes `a ^ e % m` on binary naturals with a positive modulus. It folds over
the exponent's binary digits from the most significant one, squaring the accumulator and
multiplying by `a` at each `1` digit, reducing modulo `m` after every product. Every intermediate
value is below `m`, so the work is polynomial in the lengths of `a`, `e` and `m`.

Without a modulus, `a ^ e` has about `e` times as many digits as `a`, exponentially many in the
length of `e`; the statement therefore requires a positive modulus. The total function `powMod`
returns `1` at the modulus `0` instead, so it is polynomial-time on every input. This is where it
differs from core's `Nat.powMod`, which returns the unreduced power at the modulus `0`. Powers
compose (`Turing.MultiTapeTM.powMod_powMod`), and powers of a unit are units
(`Turing.MultiTapeTM.coprime_powMod`).

## Main definitions

* `Turing.MultiTapeTM.powMod`: modular exponentiation, returning `1` at the modulus `0`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_powMod`: modular exponentiation of computed
  binary values with a positive modulus.
* `Turing.MultiTapeTM.computableInPolyTime_powMod`: `powMod` of computed binary values, with no
  condition on the modulus.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Turing.MultiTapeTM

namespace BinaryPowMod

/-- One square-and-multiply step modulo `m` for the base `a`: square the accumulator, and
multiply by `a` when the next exponent digit, most significant first, is `1`. -/
private def step (par : ℕ × ℕ) (acc : ℕ) (bit : Bool) : ℕ :=
  acc * acc % par.2 * (if bit then par.1 else 1) % par.2

/-- Folding `step` over a most-significant-first word computes the power of its value. -/
private theorem foldl_step (a m : ℕ) (word : List Bool) :
    word.foldl (step (a, m)) (1 % m) = a ^ Cslib.BitString.binaryValue word % m := by
  induction word using List.reverseRecOn with
  | nil => simp [Cslib.BitString.binaryValue]
  | append_singleton word bit ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Cslib.BitString.binaryValue_snoc, step, ← ZMod.natCast_eq_natCast_iff']
    cases bit <;> simp only [Nat.cast_mul, ZMod.natCast_mod, Nat.cast_pow, Bool.toNat_false,
      Bool.toNat_true, Bool.false_eq_true, ite_false, ite_true, pow_add, pow_mul, add_zero, pow_one,
      mul_one] <;> ring

/-- The exponent's digits, most significant first, give `a ^ e % m`. -/
private theorem powMod_eq (a e m : ℕ) :
    e.bits.reverse.foldl (step (a, m)) (1 % m) = a ^ e % m := by
  rw [foldl_step, Cslib.BitString.binaryValue_reverse_bits]

/-- Modular exponentiation with the modulus `m + 1`, which is positive. -/
private theorem computableInPolyTime_powMod_succ :
    ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => p.1 ^ p.2.1 % (p.2.2 + 1))
      (encPair encNat (encPair encNat encNat)) encNat := by
  have hpar : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => (p.1, p.2.2 + 1))
      (encPair encNat (encPair encNat encNat)) (encPair encNat encNat) := by fun_prop
  have hlist : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => p.2.1.bits.reverse)
      (encPair encNat (encPair encNat encNat)) encBits := by fun_prop
  have hinit : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ => 1 % (p.2.2 + 1))
      (encPair encNat (encPair encNat encNat)) encNat :=
    ComputableInPolyTime.binary_mod' (.const 1)
      (.binary_add' (ComputableInPolyTime.snd encNat (encPair encNat encNat)).snd' (.const 1))
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × ℕ) × Bool => step q.1.1 q.1.2 q.2)
      (encPair (encPair (encPair encNat encNat) encNat) encBool) encNat := by
    unfold step
    have hstate := ComputableInPolyTime.fst (encPair (encPair encNat encNat) encNat) encBool
    have hbit := ComputableInPolyTime.snd (encPair (encPair encNat encNat) encNat) encBool
    exact ComputableInPolyTime.binary_mod'
      (.binary_mul' (.binary_mod' (.binary_mul' hstate.snd' hstate.snd') hstate.fst'.snd')
        (hbit.ite' hstate.fst'.fst' (.const 1))) hstate.fst'.snd'
  simpa only [powMod_eq] using ComputableInPolyTime.foldlWith (encP := encPair encNat encNat)
    (encA := encBool) (encL := encBits) (encB := encNat) hpar hlist hinit hstep
    (B := fun p => (encPair encNat (encPair encNat encNat) p).length) PolyBounded.self
    (fun p i _ => by
      rw [foldl_step]
      have hle : p.1 ^ Cslib.BitString.binaryValue (p.2.1.bits.reverse.take i) % (p.2.2 + 1) ≤
          p.2.2 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos _))
      calc (encNat _).length ≤ (encNat p.2.2).length := by
            simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hle
        _ ≤ (encPair encNat encNat p.2).length := length_le_encPair_right encNat encNat p.2
        _ ≤ (encPair encNat (encPair encNat encNat) p).length :=
          length_le_encPair_right encNat (encPair encNat encNat) p)

end BinaryPowMod

/-- **Modular exponentiation** of computed binary values with a positive modulus, by
square-and-multiply. -/
theorem ComputableInPolyTime.binary_powMod {α : Type} {input : α ↪ List Bool}
    {base exponent modulus : α → ℕ} (hbase : ComputableInPolyTime base input encNat)
    (hexponent : ComputableInPolyTime exponent input encNat)
    (hmodulus : ComputableInPolyTime modulus input encNat) (hpos : ∀ a, 0 < modulus a) :
    ComputableInPolyTime (fun a => base a ^ exponent a % modulus a) input encNat := by
  simpa only [Function.comp_def, Nat.sub_add_cancel (hpos _)] using
    BinaryPowMod.computableInPolyTime_powMod_succ.comp
      (hbase.prod (hexponent.prod (ComputableInPolyTime.binary_sub' hmodulus (.const 1))))

/-! ### Total modular exponentiation -/

/-- Modular exponentiation `x ^ e mod M`. For the degenerate modulus `M = 0` it returns `1`
instead of the unreduced power, so that it is computable in polynomial time on every input. -/
@[expose] def powMod (M x e : ℕ) : ℕ := if M = 0 then 1 else x ^ e % M

theorem powMod_of_ne_zero {M : ℕ} (hM : M ≠ 0) (x e : ℕ) : powMod M x e = x ^ e % M := by
  simp [powMod, hM]

/-- Raising `powMod N g a` to the power `b` modulo `N` is `powMod N g (a * b)`. -/
theorem powMod_powMod (N g a b : ℕ) : powMod N (powMod N g a) b = powMod N g (a * b) := by
  by_cases hN : N = 0 <;> simp [powMod, hN, Nat.pow_mod, pow_mul]

/-- A power of a unit modulo `N` is a unit modulo `N`. -/
theorem coprime_powMod {N g : ℕ} (hg : Nat.Coprime g N) (e : ℕ) :
    Nat.Coprime (powMod N g e) N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [powMod]
  · rw [powMod_of_ne_zero hN.ne', Nat.Coprime, (Nat.mod_modEq (g ^ e) N).gcd_eq]
    exact hg.pow_left e

/-- `powMod` is computable in polynomial time. -/
theorem computableInPolyTime_powMod {α : Type} {input : α ↪ List Bool} {M x e : α → ℕ}
    (hM : ComputableInPolyTime M input encNat) (hx : ComputableInPolyTime x input encNat)
    (he : ComputableInPolyTime e input encNat) :
    ComputableInPolyTime (fun a => powMod (M a) (x a) (e a)) input encNat := by
  have heq : (fun a => powMod (M a) (x a) (e a)) =
      fun a => if M a = 0 then 1 else x a ^ e a % (M a - 1 + 1) := funext fun a => by
    unfold powMod
    split_ifs with h0
    · rfl
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]
  rw [heq]
  exact ComputableInPolyTime.ite_decide (condition := fun a => M a = 0)
    (.decide_eq' hM (.const 0)) (.const 1) <|
    ComputableInPolyTime.binary_powMod hx he
      (.binary_add' (.binary_sub' hM (.const 1)) (.const 1)) fun _ => Nat.succ_pos _

end Turing.MultiTapeTM

end
