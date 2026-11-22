/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Modular.Subtract
public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native modular subtraction generation

Certifies polynomial-time generation of `(subtract w).code` directly from its typed
complement-plus-carry definition via typed `@[fun_prop]` `(·.code)` rules. All circuit gates, wire
references, and output selectors are charged from unary width.

## Main results

* `Cslib.Circuits.Boolean.Modular.computableInPolyTime_subtractInputs`,
  `Cslib.Circuits.Boolean.Modular.computableCircuitCode_subtractInputs`: typed `@[fun_prop]`
  generation of `(subtractInputs w).code`.
* `Cslib.Circuits.Boolean.Modular.computableInPolyTime_subtract`,
  `Cslib.Circuits.Boolean.Modular.computableCircuitCode_subtract`: typed `@[fun_prop]` generation of
  `(subtract w).code`.
-/

public section

namespace Cslib.Circuits.Boolean.Modular

open Turing.MultiTapeTM ComputableInPolyTime

/-- Emit the code of the complemented-input and incoming-carry stage `subtractInputs w` from unary
width. -/
theorem computableInPolyTime_subtractInputs :
    ComputableInPolyTime (fun w => (subtractInputs w).code) encUnary encCode := by
  unfold subtractInputs
  have hwb : ComputableInPolyTime (fun w : ℕ => w) encUnary encNat := unary_to_binary
  have hn : ComputableInPolyTime (fun w : ℕ => w + w) encUnary encNat := by fun_prop
  have hwiring : Circuit.ComputableCircuitCode
      (fun w => Circuit.wiring signature (Fin.castAdd w : Fin w → Fin (w + w)))
      encUnary encOp := by
    apply Circuit.computableCircuitCode_wiring
    · exact id'
    · simp only [Fin.val_castAdd]
      fun_prop
  have hnot : Circuit.ComputableCircuitCode
      (fun w => Circuit.pi fun i : Fin w => (Formula.input (Fin.natAdd w i)).not.toCircuit)
      encUnary encOp := by
    apply Circuit.computableCircuitCode_pi hn id'
    apply Circuit.computableCircuitCode_of_computableInPolyTime
    let encQ := Circuit.encWithFinUnary encUnary id
    have hq : ComputableInPolyTime (fun q : Σ w : ℕ, Fin w => q.1) encQ encNat :=
      unary_to_binary.comp (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ)))
    apply computableInPolyTime_code_not_toCircuit (by fun_prop)
    apply computableInPolyTime_code_input_toCircuit
    simp only [Fin.val_natAdd]
    fun_prop
  have htrue : Circuit.ComputableCircuitCode
      (fun w => Circuit.oneGate (σ := signature) (n := w + w) (.const true) Fin.elim0)
      encUnary encOp :=
    Circuit.computableCircuitCode_of_computableInPolyTime
      (Circuit.computableInPolyTime_code_oneGate (σ := signature) (encOp := encOp)
        (.const true) hn fun j => Fin.elim0 j)
  fun_prop

/-- `@[fun_prop]` rule for `subtractInputs` in typed circuit compositions. -/
@[fun_prop] theorem computableCircuitCode_subtractInputs {α : Type} {enc : α ↪ List Bool}
    {w : α → ℕ} (hw : ComputableInPolyTime w enc encUnary) :
    Circuit.ComputableCircuitCode (fun a => subtractInputs (w a)) enc encOp :=
  Circuit.computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_subtractInputs.comp hw)

/-- Full generation is polynomial-time in unary width, including binary gate and output indices. -/
theorem computableInPolyTime_subtract :
    ComputableInPolyTime (fun w => (subtract w).code) encUnary encCode := by
  unfold subtract
  have hwb : ComputableInPolyTime (fun w : ℕ => w) encUnary encNat := unary_to_binary
  have hout : Circuit.ComputableCircuitCode
      (fun w => Circuit.wiring signature (fun i : Fin w => i.castSucc)) encUnary encOp := by
    apply Circuit.computableCircuitCode_wiring
    · exact id'
    · simp only [Fin.val_castSucc]
      fun_prop
  fun_prop

/-- `@[fun_prop]` rule for `subtract` in typed circuit compositions. -/
@[fun_prop] theorem computableCircuitCode_subtract {α : Type} {enc : α ↪ List Bool}
    {w : α → ℕ} (hw : ComputableInPolyTime w enc encUnary) :
    Circuit.ComputableCircuitCode (fun a => subtract (w a)) enc encOp :=
  Circuit.computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_subtract.comp hw)

end Cslib.Circuits.Boolean.Modular
