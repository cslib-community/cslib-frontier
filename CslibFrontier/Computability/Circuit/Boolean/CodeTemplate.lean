/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
public import CslibFrontier.Computability.Circuit.Boolean.Formula
import Mathlib.Tactic.FinCases

/-!
# Uniform instantiation of fixed De Morgan formula templates

Specializes `Cslib.Circuits.Circuit.formulaCode` and the typed formula `(·.toCircuit.code)` rules
from `CslibFrontier.Computability.Circuit.Encoding.Combinators` to De Morgan formulas.

## Main definitions

* `Cslib.Circuits.Boolean.formulaCode`: the actual code of a fixed De Morgan formula at selected
  wires.

## Main results

* `Cslib.Circuits.Boolean.formulaCode_eq_code`: exact agreement with typed instantiation.
* `Cslib.Circuits.Boolean.computableInPolyTime_formulaCode`: instantiate a fixed formula
  at efficiently computed input wires.
* `Cslib.Circuits.Boolean.computableInPolyTime_code_input_toCircuit`,
  `computableInPolyTime_code_const_toCircuit`, `computableInPolyTime_code_not_toCircuit`,
  `computableInPolyTime_code_and_toCircuit`, `computableInPolyTime_code_or_toCircuit`,
  `computableInPolyTime_code_ite_toCircuit`: typed polynomial-time code rules for De Morgan
  formulas.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-- Instantiate a De Morgan formula at raw wire numbers. -/
abbrev formulaCode {m : ℕ} (n : ℕ) (F : Formula signature m) (wires : Fin m → ℕ) :
    List (Op × List ℕ) × List ℕ :=
  Circuit.formulaCode n F wires

/-- Instantiating valid input wires constructs the renamed formula's circuit code. -/
theorem formulaCode_eq_code {n m : ℕ} (F : Formula signature m) (wires : Fin m → Fin n) :
    formulaCode n F (fun i => (wires i).val) = (F.rename wires).toCircuit.code :=
  Circuit.formulaCode_eq_code F wires

/-- A fixed formula's instantiated code is polynomial-time in the target input count and
selected binary wire numbers. -/
theorem computableInPolyTime_formulaCode {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {m : ℕ} (F : Formula signature m) {wires : α → Fin m → ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hwires : ∀ i, ComputableInPolyTime (fun a => wires a i) enc encNat) :
    ComputableInPolyTime (fun a => formulaCode (n a) F (wires a)) enc encCode :=
  Circuit.computableInPolyTime_formulaCode F hn hwires

/-- Emit the circuit code of a De Morgan input leaf `(Formula.input (w a)).toCircuit`. -/
theorem computableInPolyTime_code_input_toCircuit {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {w : (a : α) → Fin (n a)}
    (hw : ComputableInPolyTime (fun a => (w a).val) enc encNat) :
    ComputableInPolyTime (fun a => (Formula.input (σ := signature) (w a)).toCircuit.code)
      enc encCode :=
  Formula.computableInPolyTime_code_input_toCircuit (σ := signature) (encOp := encOp) hw

/-- Emit the circuit code of a De Morgan constant leaf `(Formula.const b).toCircuit`. -/
theorem computableInPolyTime_code_const_toCircuit {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} (b : Bool) (hn : ComputableInPolyTime n enc encNat) :
    ComputableInPolyTime (fun a => (Formula.const (n := n a) b).toCircuit.code) enc encCode :=
  Formula.computableInPolyTime_code_gate_toCircuit (σ := signature) (encOp := encOp)
    (.const b) hn fun j => Fin.elim0 j

/-- Emit the circuit code of a negated De Morgan formula `(F a).not.toCircuit`. -/
theorem computableInPolyTime_code_not_toCircuit {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {F : (a : α) → Formula signature (n a)}
    (hn : ComputableInPolyTime n enc encNat)
    (hF : ComputableInPolyTime (fun a => (F a).toCircuit.code) enc encCode) :
    ComputableInPolyTime (fun a => (F a).not.toCircuit.code) enc encCode :=
  Formula.computableInPolyTime_code_gate_toCircuit (σ := signature) (encOp := encOp)
    .not hn fun j => by
      fin_cases j
      exact hF

/-- Emit the circuit code of a conjunction `((F a).and (G a)).toCircuit`. -/
theorem computableInPolyTime_code_and_toCircuit {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {F G : (a : α) → Formula signature (n a)}
    (hn : ComputableInPolyTime n enc encNat)
    (hF : ComputableInPolyTime (fun a => (F a).toCircuit.code) enc encCode)
    (hG : ComputableInPolyTime (fun a => (G a).toCircuit.code) enc encCode) :
    ComputableInPolyTime (fun a => ((F a).and (G a)).toCircuit.code) enc encCode :=
  Formula.computableInPolyTime_code_gate_toCircuit (σ := signature) (encOp := encOp)
    .and hn fun j => by
      fin_cases j
      · exact hF
      · exact hG

/-- Emit the circuit code of a disjunction `((F a).or (G a)).toCircuit`. -/
theorem computableInPolyTime_code_or_toCircuit {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {F G : (a : α) → Formula signature (n a)}
    (hn : ComputableInPolyTime n enc encNat)
    (hF : ComputableInPolyTime (fun a => (F a).toCircuit.code) enc encCode)
    (hG : ComputableInPolyTime (fun a => (G a).toCircuit.code) enc encCode) :
    ComputableInPolyTime (fun a => ((F a).or (G a)).toCircuit.code) enc encCode :=
  Formula.computableInPolyTime_code_gate_toCircuit (σ := signature) (encOp := encOp)
    .or hn fun j => by
      fin_cases j
      · exact hF
      · exact hG

/-- Emit the circuit code of a conditional choice of De Morgan formulas. -/
theorem computableInPolyTime_code_ite_toCircuit {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {p : α → Prop} [∀ a, Decidable (p a)]
    {t e : (a : α) → Formula signature (n a)}
    (hp : ComputableInPolyTime (fun a => decide (p a)) enc encBool)
    (ht : ComputableInPolyTime (fun a => (t a).toCircuit.code) enc encCode)
    (he : ComputableInPolyTime (fun a => (e a).toCircuit.code) enc encCode) :
    ComputableInPolyTime (fun a => (if p a then t a else e a).toCircuit.code) enc encCode :=
  Formula.computableInPolyTime_code_ite_toCircuit (σ := signature) (encOp := encOp) hp ht he

end Cslib.Circuits.Boolean
