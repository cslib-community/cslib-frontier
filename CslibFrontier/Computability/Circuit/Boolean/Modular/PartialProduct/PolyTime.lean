/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Modular.PartialProduct
public import CslibFrontier.Computability.Circuit.Boolean.CodeTemplate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native partial-product generation

Certifies polynomial-time generation of `(partialProduct w i).code` directly from the typed circuit
definition via typed `@[fun_prop]` `(·.code)` rules. The word width is given in unary and bit
indices in binary; every emitted gate and wire reference is charged.

## Main results

* `Cslib.Circuits.Boolean.Modular.computableInPolyTime_partialProductBit`: polynomial-time code
  generation for a single product-bit formula.
* `Cslib.Circuits.Boolean.Modular.computableInPolyTime_partialProduct`,
  `Cslib.Circuits.Boolean.Modular.computableCircuitCode_partialProduct`: typed `@[fun_prop]`
  generation of `(partialProduct (w a) (i a)).code`.
-/

public section

namespace Cslib.Circuits.Boolean.Modular

open Turing.MultiTapeTM ComputableInPolyTime

/-- Emit the circuit code of a single retained product bit
`(partialProductBit (w a) (i a) (j a)).toCircuit` from binary width and binary bit indices. -/
theorem computableInPolyTime_partialProductBit {α : Type} {enc : α ↪ List Bool}
    {w : α → ℕ} {i j : (a : α) → Fin (w a)}
    (hw : ComputableInPolyTime w enc encNat)
    (hi : ComputableInPolyTime (fun a => (i a).val) enc encNat)
    (hj : ComputableInPolyTime (fun a => (j a).val) enc encNat) :
    ComputableInPolyTime (fun a => (partialProductBit (w a) (i a) (j a)).toCircuit.code)
      enc encCode := by
  have hn : ComputableInPolyTime (fun a => w a + w a) enc encNat := by fun_prop
  unfold partialProductBit
  apply computableInPolyTime_code_ite_toCircuit
  · fun_prop
  · apply computableInPolyTime_code_and_toCircuit hn
    · apply computableInPolyTime_code_input_toCircuit
      simp only [Fin.val_castAdd]
      fun_prop
    · apply computableInPolyTime_code_input_toCircuit
      simp only [Fin.val_natAdd]
      fun_prop
  · exact computableInPolyTime_code_const_toCircuit false hn

/-- Emit the circuit code of a shifted partial product `(partialProduct (w a) (i a)).code`
uniformly from unary width and binary shift index. -/
theorem computableInPolyTime_partialProduct {α : Type} {enc : α ↪ List Bool}
    {w : α → ℕ} {i : (a : α) → Fin (w a)}
    (hw : ComputableInPolyTime w enc encUnary)
    (hi : ComputableInPolyTime (fun a => (i a).val) enc encNat) :
    ComputableInPolyTime (fun a => (partialProduct (w a) (i a)).code) enc encCode := by
  have hwb : ComputableInPolyTime w enc encNat := unary_to_binary.comp hw
  unfold partialProduct
  apply Circuit.computableInPolyTime_code_pi (σ := signature) (encOp := encOp)
  · fun_prop
  · exact hw
  · let encQ := Circuit.encWithFinUnary enc w
    exact computableInPolyTime_partialProductBit
      (hwb.comp (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ))))
      (hi.comp (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ))))
      (Circuit.computableInPolyTime_withFinUnary_val_binary (id' (encIn := encQ)))

/-- `@[fun_prop]` rule for `partialProduct` in typed circuit compositions. -/
@[fun_prop] theorem computableCircuitCode_partialProduct {α : Type} {enc : α ↪ List Bool}
    {w : α → ℕ} {i : (a : α) → Fin (w a)}
    (hw : ComputableInPolyTime w enc encUnary)
    (hi : ComputableInPolyTime (fun a => (i a).val) enc encNat) :
    Circuit.ComputableCircuitCode (fun a => partialProduct (w a) (i a)) enc encOp :=
  Circuit.computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_partialProduct hw hi)

end Cslib.Circuits.Boolean.Modular
