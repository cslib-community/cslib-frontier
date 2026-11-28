/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Modular.InnerProduct
public import CslibFrontier.Computability.Circuit.Boolean.Modular.Multiply.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native modular inner-product generation

Certifies polynomial-time generation of `(innerProduct k w).code` directly from its typed
block-selection and carry-save definition via typed `@[fun_prop]` `(·.code)` rules. Unary array
count and word width generate all block selectors, complete product circuits, and the balanced
carry-save sum.

## Main results

* `Cslib.Circuits.Boolean.Modular.computableInPolyTime_innerProductInputs`: polynomial-time
  generation of `(Circuit.wiring signature (innerProductInputs (k a) (w a) (j a))).code`.
* `Cslib.Circuits.Boolean.Modular.computableInPolyTime_innerProductTerm`,
  `Cslib.Circuits.Boolean.Modular.computableCircuitCode_innerProductTerm`: typed `@[fun_prop]`
  generation of `(innerProductTerm (k a) (w a) (j a)).code`.
* `Cslib.Circuits.Boolean.Modular.computableInPolyTime_innerProduct`,
  `Cslib.Circuits.Boolean.Modular.computableCircuitCode_innerProduct`: typed `@[fun_prop]`
  generation of `(innerProduct p.1 p.2).code`.
-/

public section

namespace Cslib.Circuits.Boolean.Modular

open Turing.MultiTapeTM ComputableInPolyTime

private theorem val_innerProductInputs {k w : ℕ} (j : Fin k) (i : Fin (w + w)) :
    (innerProductInputs k w j i).val =
      if i.val < w then j.val * w + i.val else k * w + (j.val * w + (i.val - w)) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [innerProductInputs, finProdFinEquiv, i.isLt, Nat.add_comm, Nat.mul_comm]
  · simp only [innerProductInputs, Fin.addCases_right, Fin.val_natAdd]
    rw [ite_eq_right (by omega)]
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

/-- Emit the block-selector wiring code `(Circuit.wiring signature (innerProductInputs ...)).code`
uniformly from binary array count, unary word width, and binary block index. -/
theorem computableInPolyTime_innerProductInputs {α : Type} {enc : α ↪ List Bool}
    {k w : α → ℕ} {j : (a : α) → Fin (k a)}
    (hk : ComputableInPolyTime k enc encNat)
    (hw : ComputableInPolyTime w enc encUnary)
    (hj : ComputableInPolyTime (fun a => (j a).val) enc encNat) :
    ComputableInPolyTime
      (fun a => (Circuit.wiring signature (innerProductInputs (k a) (w a) (j a))).code)
      enc encCode := by
  have hwb : ComputableInPolyTime w enc encNat := unary_to_binary.comp hw
  refine Circuit.computableInPolyTime_code_wiring (σ := signature) (encOp := encOp)
    (by fun_prop) ?_
  let encQ := Circuit.encWithFinUnary enc (fun a => w a + w a)
  have hk' := hk.comp (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ)))
  have hw' := hwb.comp (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ)))
  have hj' := hj.comp (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ)))
  have hi' := Circuit.computableInPolyTime_withFinUnary_val_binary (id' (encIn := encQ))
  simp only [val_innerProductInputs]; fun_prop

/-- Emit the code of one blockwise product `(innerProductTerm (k a) (w a) (j a)).code` uniformly
from binary array count, unary word width, and binary block index. -/
theorem computableInPolyTime_innerProductTerm {α : Type} {enc : α ↪ List Bool}
    {k w : α → ℕ} {j : (a : α) → Fin (k a)}
    (hk : ComputableInPolyTime k enc encNat)
    (hw : ComputableInPolyTime w enc encUnary)
    (hj : ComputableInPolyTime (fun a => (j a).val) enc encNat) :
    ComputableInPolyTime (fun a => (innerProductTerm (k a) (w a) (j a)).code) enc encCode := by
  unfold innerProductTerm
  have hwb : ComputableInPolyTime w enc encNat := unary_to_binary.comp hw
  have hin : Circuit.ComputableCircuitCode
      (fun a => Circuit.wiring signature (innerProductInputs (k a) (w a) (j a))) enc encOp :=
    Circuit.computableCircuitCode_of_computableInPolyTime
      (computableInPolyTime_innerProductInputs hk hw hj)
  fun_prop

/-- `@[fun_prop]` rule for `innerProductTerm` in typed circuit compositions. -/
@[fun_prop] theorem computableCircuitCode_innerProductTerm {α : Type} {enc : α ↪ List Bool}
    {k w : α → ℕ} {j : (a : α) → Fin (k a)}
    (hk : ComputableInPolyTime k enc encNat)
    (hw : ComputableInPolyTime w enc encUnary)
    (hj : ComputableInPolyTime (fun a => (j a).val) enc encNat) :
    Circuit.ComputableCircuitCode (fun a => innerProductTerm (k a) (w a) (j a)) enc encOp :=
  Circuit.computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_innerProductTerm hk hw hj)

/-- The full constructor is uniform in unary count and width. -/
theorem computableInPolyTime_innerProduct :
    ComputableInPolyTime (fun p : ℕ × ℕ => (innerProduct p.1 p.2).code)
      (encPair encUnary encUnary) encCode := by
  unfold innerProduct
  have hk : ComputableInPolyTime (fun p : ℕ × ℕ => p.1) (encPair encUnary encUnary) encNat :=
    unary_to_binary.comp (fst encUnary encUnary)
  have hw : ComputableInPolyTime (fun p : ℕ × ℕ => p.2) (encPair encUnary encUnary) encNat :=
    unary_to_binary.comp (snd encUnary encUnary)
  refine computableInPolyTime_sumPairs (by fun_prop) (snd encUnary encUnary) ?_
  let encQ := Circuit.encWithFinUnary (encPair encUnary encUnary) Prod.fst
  have hqk := hk.comp (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ)))
  have hqw := (snd encUnary encUnary).comp
    (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ)))
  have hqwb := unary_to_binary.comp hqw
  simpa only [List.map_ofFn, Function.comp_def] using
    Circuit.computableInPolyTime_ofFn_unary (k := Prod.fst) (fst encUnary encUnary) (by fun_prop)

/-- `@[fun_prop]` rule for `innerProduct` in typed circuit compositions. -/
@[fun_prop] theorem computableCircuitCode_innerProduct {α : Type} {enc : α ↪ List Bool}
    {k w : α → ℕ} (hk : ComputableInPolyTime k enc encUnary)
    (hw : ComputableInPolyTime w enc encUnary) :
    Circuit.ComputableCircuitCode (fun a => innerProduct (k a) (w a)) enc encOp := by
  refine Circuit.computableCircuitCode_of_computableInPolyTime (σ := signature) (encOp := encOp) ?_
  simpa only [Function.comp_def] using computableInPolyTime_innerProduct.comp (hk.prod hw)

end Cslib.Circuits.Boolean.Modular
