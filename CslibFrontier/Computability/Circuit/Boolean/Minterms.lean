/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Circuit.Evaluation
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Computability.Circuit.Boolean.Simps

/-!
# Shared Boolean minterms

The circuit computes the indicator of every assignment to its input bits. Each stage retains
the preceding minterms and extends them by one new bit. Sharing the preceding table gives a
linear bound in the number of assignments, including all constants and negations.

## Main definitions

* `Cslib.Circuits.Boolean.mintermExtension`: one-step formula extending a tail minterm by testing
  the head bit.
* `Cslib.Circuits.Boolean.mintermCircuit`: all assignment indicators in `BitString.equivFin` order.

## Main results

* `Cslib.Circuits.Boolean.eval_mintermCircuit`: the output is the indicator of the input's index.
* `Cslib.Circuits.Boolean.size_mintermCircuit_add_three_le`: at most `4 * 2 ^ n - 3` gates.

## References

* Adapted from MassProduction/ShannonCircuit.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- One extension reads a preceding minterm and tests the new head bit. -/
def mintermExtension (n : ℕ) (a : Fin (2 ^ (n + 1))) : Formula signature (2 ^ n + 1) :=
  (Formula.input
    (Fin.castAdd 1 (BitString.equivFin n (Fin.tail ((BitString.equivFin _).symm a))))).and
    (if (BitString.equivFin _).symm a 0 then Formula.input (Fin.last (2 ^ n))
     else (Formula.input (Fin.last (2 ^ n))).not)

private theorem size_mintermExtension_le (n : ℕ) (a : Fin (2 ^ (n + 1))) :
    (mintermExtension n a).size ≤ 2 := by
  unfold mintermExtension
  cases (BitString.equivFin (n + 1)).symm a 0 <;> simp

/-- Shared indicators of all `n`-bit assignments, indexed least significant bit first. -/
def mintermCircuit : (n : ℕ) → Circuit signature n (2 ^ n)
  | 0 => (Formula.const true).toCircuit
  | n + 1 =>
    (Circuit.pi fun a => (mintermExtension n a).toCircuit).comp
      (((mintermCircuit n).comp (Circuit.wiring signature Fin.succ)).append
        (Circuit.wiring signature fun _ : Fin 1 => (0 : Fin (n + 1))))

/-- A complete assignment is determined by its head and tail. -/
private theorem assignment_eq_iff {n : ℕ} (x : BitString (n + 1))
    (a : Fin (2 ^ (n + 1))) :
    BitString.equivFin (n + 1) x = a ↔
      BitString.equivFin n (Fin.tail x) =
        BitString.equivFin n (Fin.tail ((BitString.equivFin _).symm a)) ∧
      x 0 = (BitString.equivFin _).symm a 0 := by
  rw [← Equiv.eq_symm_apply, Equiv.apply_eq_iff_eq]
  constructor
  · intro h
    subst x
    exact ⟨rfl, rfl⟩
  · rintro ⟨ht, hh⟩
    rw [← Fin.cons_self_tail x, ht, hh, Fin.cons_self_tail]

/-- Each output is true precisely for the assignment bearing that index. -/
@[simp] theorem eval_mintermCircuit (n : ℕ) (x : BitString n) (a : Fin (2 ^ n)) :
    (mintermCircuit n).eval interpretation x a = decide (BitString.equivFin n x = a) := by
  induction n with
  | zero =>
    have h : BitString.equivFin 0 x = a := Subsingleton.elim (α := Fin 1) _ _
    simp [mintermCircuit, h]
  | succ n ih =>
    simp only [circuit_simps, mintermCircuit]
    simp only [circuit_simps, mintermExtension, ih]
    have hlast : Fin.last (2 ^ n) = Fin.natAdd (2 ^ n) (0 : Fin 1) := rfl
    cases hb : (BitString.equivFin (n + 1)).symm a 0 <;>
      simp [circuit_simps, hb, hlast, assignment_eq_iff, Fin.tail_def, Function.comp_def]

/-- All minterms together use at most `4 * 2 ^ n - 3` gates, counting constants too. -/
theorem size_mintermCircuit_add_three_le (n : ℕ) :
    (mintermCircuit n).size + 3 ≤ 4 * 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have := size_mintermExtension_le n
    circuit_bound [mintermCircuit, pow_succ]

end Cslib.Circuits.Boolean
