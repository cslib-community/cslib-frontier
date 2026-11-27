/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Polynomial.CoeffList
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Modular Horner evaluation on binary and unary inputs

Reducing each intermediate value modulo the input modulus bounds the accumulator throughout the
fold. The binary machine certificate also handles unary input and output by changing encodings
and using the unary modulus as a bound for the returned value.

## Main definitions

* `Polynomial.evalCoeffListMod` evaluates a list of natural coefficients modulo a given modulus.

## Main results

* `Polynomial.natCast_evalCoeffListMod` interprets the returned residue as a polynomial value.
* `Turing.MultiTapeTM.ComputableInPolyTime.evalCoeffListMod` and
  `Turing.MultiTapeTM.ComputableInPolyTime.evalCoeffListMod_unary` give the machine certificates.
-/

public section

namespace Polynomial

/-- Evaluate a polynomial modulo `p` by Horner's rule, taking the constant coefficient first.
For `p = 0` return zero. -/
@[expose] def evalCoeffListMod (p z : ℕ) (l : List ℕ) : ℕ :=
  l.foldr (fun a acc => (a + z * acc) % max p 1) 0

/-- Every Horner accumulator is a residue, including the zero-modulus convention. -/
theorem evalCoeffListMod_lt (p z : ℕ) (l : List ℕ) : evalCoeffListMod p z l < max p 1 := by
  cases l with
  | nil =>
    change 0 < max p 1
    omega
  | cons a l => exact Nat.mod_lt _ (by omega)

/-- With a positive modulus, the returned representative is strictly below the modulus. -/
theorem evalCoeffListMod_lt_modulus {p : ℕ} [NeZero p] (z : ℕ) (l : List ℕ) :
    evalCoeffListMod p z l < p := by
  simpa only [max_eq_left (NeZero.one_le (n := p))] using evalCoeffListMod_lt p z l

/-- Modular Horner evaluation agrees with evaluation of the coefficient polynomial in `ZMod p`. -/
theorem natCast_evalCoeffListMod {p : ℕ} [NeZero p] (z : ℕ) (l : List ℕ) :
    (evalCoeffListMod p z l : ZMod p) = (ofCoeffList (l.map Nat.cast)).eval (z : ZMod p) := by
  rw [eval_ofCoeffList]
  induction l with
  | nil => simp [evalCoeffListMod]
  | cons a l ih =>
    change (((a + z * evalCoeffListMod p z l) % max p 1 : ℕ) : ZMod p) = _
    rw [Nat.max_eq_left (NeZero.one_le), ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ih]
    simp

end Polynomial

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Evaluate a polynomial given its binary natural coefficients, point and modulus. -/
@[fun_prop] theorem evalCoeffListMod {α : Type} {enc : α ↪ List Bool} {p z : α → ℕ}
    {l : α → List ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hz : ComputableInPolyTime z enc encNat) (hl : ComputableInPolyTime l enc (encList encNat)) :
    ComputableInPolyTime (fun x => Polynomial.evalCoeffListMod (p x) (z x) (l x)) enc encNat := by
  have hmod := binary_max' hp (const 1)
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × ℕ) × ℕ => (q.2 + q.1.1.2 * q.1.2) % q.1.1.1)
      (encPair (encPair (encPair encNat encNat) encNat) encNat) encNat := by
    exact binary_mod' (binary_add' (snd _ _) (binary_mul' (by fun_prop) (by fun_prop)))
      (by fun_prop)
  have hfold := foldlWith (encA := encNat) (encB := encNat) (encL := encList encNat)
    (encP := encPair encNat encNat)
    (par := fun x => (max (p x) 1, z x)) (list := fun x => (l x).reverse) (init := fun _ => 0)
    (step := fun par acc a => (a + par.2 * acc) % par.1)
    (hmod.prod hz) (listReverseWithInput hl) (const 0) hstep
    (B := fun x => (encNat (max (p x) 1)).length) hmod.polyBounded_length
    (fun x i _ => by
      have hlt := Polynomial.evalCoeffListMod_lt (p x) (z x) ((List.take i (l x).reverse).reverse)
      rw [Polynomial.evalCoeffListMod, ← List.foldl_reverse, List.reverse_reverse] at hlt
      simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hlt.le)
  simpa only [Polynomial.evalCoeffListMod, List.foldl_reverse] using hfold

/-- Modular evaluation of unary coefficients, point and modulus, returning the residue in
unary. The modulus bounds the conversion of the binary result back to unary. -/
@[fun_prop] theorem evalCoeffListMod_unary {α : Type} {enc : α ↪ List Bool} {p z : α → ℕ}
    {l : α → List ℕ} (hp : ComputableInPolyTime p enc encUnary)
    (hz : ComputableInPolyTime z enc encUnary) (hl : ComputableInPolyTime l enc (encList encUnary)) :
    ComputableInPolyTime (fun x => Polynomial.evalCoeffListMod (p x) (z x) (l x)) enc encUnary := by
  have hcoeff : ComputableInPolyTime l enc (encList encNat) := by
    simpa using (map unary_to_binary).comp hl
  apply binary_to_unary_bounded (evalCoeffListMod (unary_to_binary.comp hp)
    (unary_to_binary.comp hz) hcoeff) hp
  intro x
  change Polynomial.evalCoeffListMod (p x) (z x) (l x) ≤ p x
  have := Polynomial.evalCoeffListMod_lt (p x) (z x) (l x)
  omega

end Turing.MultiTapeTM.ComputableInPolyTime
