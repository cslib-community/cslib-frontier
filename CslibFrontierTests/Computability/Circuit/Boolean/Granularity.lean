/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

import CslibFrontier.Computability.Circuit.Boolean.MajorityNonlinear
import CslibFrontier.Computability.Circuit.Pi
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Tactic.NormNum

/-!
# Circuit Fourier-denominator regression tests

One AND gate supplies three different outputs through free XOR gates. Every output has
half-integral coefficients, and a parity of two outputs cancels the shared AND result.
The tests also cover a nullary constant, a nonconstant zero-cost affine circuit, and the
majority lower bound at odd and even arities. A one-AND majority circuit makes the lower
bound sharp at three inputs.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Boolean.Granularity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.BitString Finset

private theorem full_arity (op : (fullSignature 2 Bool).Op) :
    (fullSignature 2 Bool).Arity op ≤ 2 := by
  cases op <;> simp [fullSignature]

private def sharedProgram : Program (fullSignature 2 Bool) 2 3 :=
  let p0 : Program (fullSignature 2 Bool) 2 0 := .empty
  let p := p0.gate ⟨.fn (fun x => x 0 * x 1), ![.input 0, .input 1]⟩
  let q := p.gate ⟨.fn (fun x => x 0 + x 1), ![.gate 0, .input 0]⟩
  q.gate ⟨.fn (fun x => x 0 + x 1), ![.gate 0, .input 1]⟩

private def sharedCircuit : Circuit (fullSignature 2 Bool) 2 3 :=
  ⟨sharedProgram, Wire.gate⟩

private theorem shared_cost :
    sharedCircuit.program.cost (nonlinearCost fullInterpretation) = 1 := by
  decide +kernel

private theorem shared_eval (x : Fin 2 → Bool) :
    sharedCircuit.eval fullInterpretation x =
      ![x 0 * x 1, x 0 * x 1 + x 0, x 0 * x 1 + x 1] := by
  revert x
  decide +kernel

-- The denominator is two despite three outputs and repeated uses of the nonlinear wire.
example (j : Fin 3) (S : Finset (Fin 2)) :
    ∃ z : ℤ, fourierCoeff (fun x => signVal (sharedCircuit.eval fullInterpretation x j)) S =
      z / 2 := by
  simpa only [shared_cost, pow_one] using
    sharedCircuit.exists_fourierCoeff_signVal_eval_eq_intCast_div_two_pow_nonlinearCost
      fullInterpretation full_arity j S

-- This denominator is attained: all three outputs have bias 1/2.
example (j : Fin 3) :
    fourierCoeff (fun x => signVal (sharedCircuit.eval fullInterpretation x j)) ∅ = 1 / 2 := by
  fin_cases j <;>
    simp only [shared_eval, fourierCoeff, Fin.expect_univ_cons,
      Fintype.expect_bool, Fintype.expect_unique] <;>
    norm_num [chi, signVal, Bool.mul_eq_and, Bool.add_eq_xor]

-- The shared AND value cancels in a joint workspace character.
example :
    fourierCoeff (fun x => chi ℝ ({.gate 0, .gate 1} : Finset (Wire 2 3))
      (sharedProgram.trace fullInterpretation x)) {0} = 1 := by
  have h : (fun x => chi ℝ ({.gate 0, .gate 1} : Finset (Wire 2 3))
      (sharedProgram.trace fullInterpretation x)) = chi ℝ ({0} : Finset (Fin 2)) := by
    funext x
    simp only [chi,
      prod_insert (show (Wire.gate 0 : Wire 2 3) ∉ {Wire.gate 1} by decide), prod_singleton]
    change (-1 : ℝ) ^ (x 0 * x 1).toNat * (-1) ^ (x 0 * x 1 + x 0).toNat =
      (-1) ^ (x 0).toNat
    cases x 0 <;> cases x 1 <;> norm_num [Bool.mul_eq_and, Bool.add_eq_xor]
  rw [h, fourierCoeff_chi]
  simp

private def zeroInputConstant : Circuit (fullSignature 2 Bool) 0 1 :=
  Circuit.oneGate (.con true) Fin.elim0

-- Empty input type and nullary gates are included; true has coefficient -1.
example :
    zeroInputConstant.program.cost (nonlinearCost fullInterpretation) = 0 ∧
      fourierCoeff (fun x => signVal (zeroInputConstant.eval fullInterpretation x 0)) ∅ = -1 := by
  constructor
  · decide +kernel
  · change fourierCoeff (fun _ : Fin 0 → Bool => signVal true) ∅ = -1
    simp

private def xorOnly : Circuit (fullSignature 2 Bool) 2 1 :=
  Circuit.oneGate (.fn fun x => x 0 + x 1) id

-- Arbitrary Fourier masks of a nonconstant zero-cost affine output have integral coefficients.
example (S : Finset (Fin 2)) :
    ∃ z : ℤ, fourierCoeff (fun x => signVal (xorOnly.eval fullInterpretation x 0)) S = z := by
  have hcost : xorOnly.program.cost (nonlinearCost fullInterpretation) = 0 := by decide +kernel
  simpa only [hcost, pow_zero, div_one] using
    xorOnly.exists_fourierCoeff_signVal_eval_eq_intCast_div_two_pow_nonlinearCost
      fullInterpretation full_arity 0 S

-- Odd arity with several nonzero binary digits: 31 - B(31) = 26.
example : 26 ≤ Zhegalkin.multiplicativeComplexity (single (majority 31)) := by
  have h : 31 - (Nat.digits 2 31).sum = 26 := by decide +kernel
  simpa only [h] using Zhegalkin.sub_sum_digits_le_multiplicativeComplexity_majority 31

-- Even arity uses the constant coefficient and the tie-accepting convention.
example : majority 2 ![true, false] = true := by decide +kernel

example : 7 ≤ Zhegalkin.multiplicativeComplexity (single (majority 8)) := by
  have h : 8 - (Nat.digits 2 8).sum = 7 := by decide +kernel
  simpa only [h] using Zhegalkin.sub_sum_digits_le_multiplicativeComplexity_majority 8

private def majorityThree : Circuit Zhegalkin.signature 3 1 :=
  let p0 : Program Zhegalkin.signature 3 0 := .empty
  let p1 := p0.gate ⟨.xor, ![.input 0, .input 1]⟩
  let p2 := p1.gate ⟨.xor, ![.input 0, .input 2]⟩
  let p3 := p2.gate ⟨.and, ![.gate 0, .gate 1]⟩
  let p4 := p3.gate ⟨.xor, ![.input 0, .gate 2]⟩
  ⟨p4, fun _ => .gate 3⟩

-- The lower-bound theorem and an explicit matching circuit meet in the canonical infimum.
example : Zhegalkin.multiplicativeComplexity (single (majority 3)) = 1 := by
  apply le_antisymm
  · have hc : majorityThree.Computes Zhegalkin.interpretation (single (majority 3)) := by
      intro x
      funext i
      fin_cases i
      revert x
      decide +kernel
    exact (Zhegalkin.multiplicativeComplexity_le_of_computes majorityThree hc).trans_eq rfl
  · have h : 3 - (Nat.digits 2 3).sum = 1 := by decide +kernel
    simpa only [h] using Zhegalkin.sub_sum_digits_le_multiplicativeComplexity_majority 3

-- The all-n endpoint includes the zero-input tie, computed by a free constant gate.
example : Zhegalkin.multiplicativeComplexity (single (majority 0)) = 0 := by
  let c : Circuit Zhegalkin.signature 0 1 := Circuit.oneGate .one Fin.elim0
  have hc : c.Computes Zhegalkin.interpretation (single (majority 0)) := by
    intro x
    funext i
    fin_cases i
    rfl
  exact Nat.eq_zero_of_le_zero
    ((Zhegalkin.multiplicativeComplexity_le_of_computes c hc).trans_eq rfl)

end CslibFrontierTests.Computability.Circuit.Boolean.Granularity
