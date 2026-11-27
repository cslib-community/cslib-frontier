/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Comparison
public import CslibFrontier.Computability.Circuit.Boolean.Comparison.OrderPolyTime
public import CslibFrontier.Computability.Circuit.Boolean.CodeTemplate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native generation of multiplexers and minimum selectors

Certifies polynomial-time generation of `(muxCircuit w).code`, `(minCircuit w).code`, and
`(keyedMinCircuit k p).code` directly from their typed circuit definitions via typed `@[fun_prop]`
`(·.code)` rules. Widths are given in unary and all emitted wire references are binary.

## Main results

* `Cslib.Circuits.Boolean.computableInPolyTime_muxBit`: polynomial-time code generation for one
  multiplexer-bit formula.
* `Cslib.Circuits.Boolean.computableInPolyTime_muxCircuit`,
  `Cslib.Circuits.Boolean.computableCircuitCode_muxCircuit`: typed `@[fun_prop]` generation of
  `(muxCircuit w).code`.
* `Cslib.Circuits.Boolean.computableInPolyTime_minCircuit`,
  `Cslib.Circuits.Boolean.computableCircuitCode_minCircuit`: typed `@[fun_prop]` generation of
  `(minCircuit w).code`.
* `Cslib.Circuits.Boolean.computableInPolyTime_keyedMinCircuit`,
  `Cslib.Circuits.Boolean.computableCircuitCode_keyedMinCircuit`: typed `@[fun_prop]` generation of
  `(keyedMinCircuit p.1 p.2).code`.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

/-- Emit the circuit code of bit `i` of the multiplexer `(muxBit (i a)).toCircuit` from binary word
width and binary bit index. -/
theorem computableInPolyTime_muxBit {α : Type} {enc : α ↪ List Bool}
    {w : α → ℕ} {i : (a : α) → Fin (w a)}
    (hw : ComputableInPolyTime w enc encNat)
    (hi : ComputableInPolyTime (fun a => (i a).val) enc encNat) :
    ComputableInPolyTime (fun a => (muxBit (i a)).toCircuit.code) enc encCode := by
  have hn : ComputableInPolyTime (fun a => 1 + (w a + w a) + 1) enc encNat := by fun_prop
  unfold muxBit
  apply computableInPolyTime_code_or_toCircuit hn
  · apply computableInPolyTime_code_and_toCircuit hn
    · exact computableInPolyTime_code_input_toCircuit (const 0)
    · apply computableInPolyTime_code_input_toCircuit
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      fun_prop
  · apply computableInPolyTime_code_and_toCircuit hn
    · apply computableInPolyTime_code_input_toCircuit
      simp only [Fin.val_natAdd, Fin.val_zero, Nat.add_zero]
      fun_prop
    · apply computableInPolyTime_code_input_toCircuit
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      fun_prop

/-- The multiplexer on words of `w` bits has a polynomial-time code generator in unary `w`. -/
theorem computableInPolyTime_muxCircuit :
    ComputableInPolyTime (fun w => (muxCircuit w).code) encUnary encCode := by
  unfold muxCircuit
  have hwb : ComputableInPolyTime (fun w : ℕ => w) encUnary encNat := unary_to_binary
  have hn : ComputableInPolyTime (fun w : ℕ => 1 + (w + w)) encUnary encNat := by fun_prop
  have hn1 : ComputableInPolyTime (fun w : ℕ => 1 + (w + w) + 1) encUnary encNat := by fun_prop
  have hbits : Circuit.ComputableCircuitCode
      (fun w => Circuit.pi fun i : Fin w => (muxBit i).toCircuit) encUnary encOp := by
    apply Circuit.computableCircuitCode_pi hn1 id'
    apply Circuit.computableCircuitCode_of_computableInPolyTime
    let encQ := Circuit.encWithFinUnary encUnary id
    exact computableInPolyTime_muxBit
      (unary_to_binary.comp (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ))))
      (Circuit.computableInPolyTime_withFinUnary_val_binary (id' (encIn := encQ)))
  have hnot : Circuit.ComputableCircuitCode
      (fun w => Circuit.oneGate (σ := signature) Op.not
        fun _ => Fin.castAdd (w + w) (0 : Fin 1)) encUnary encOp :=
    Circuit.computableCircuitCode_of_computableInPolyTime
      (Circuit.computableInPolyTime_code_oneGate (σ := signature) (encOp := encOp)
        Op.not hn fun _ => const 0)
  fun_prop

/-- `@[fun_prop]` rule for `muxCircuit` in typed circuit compositions. -/
@[fun_prop] theorem computableCircuitCode_muxCircuit {α : Type} {enc : α ↪ List Bool}
    {w : α → ℕ} (hw : ComputableInPolyTime w enc encUnary) :
    Circuit.ComputableCircuitCode (fun a => muxCircuit (w a)) enc encOp :=
  Circuit.computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_muxCircuit.comp hw)

/-- The minimum selector `minCircuit w` has a polynomial-time code generator in unary `w`. -/
theorem computableInPolyTime_minCircuit :
    ComputableInPolyTime (fun w => (minCircuit w).code) encUnary encCode := by
  unfold minCircuit
  have hwb : ComputableInPolyTime (fun w : ℕ => w) encUnary encNat := unary_to_binary
  fun_prop

/-- `@[fun_prop]` rule for `minCircuit` in typed circuit compositions. -/
@[fun_prop] theorem computableCircuitCode_minCircuit {α : Type} {enc : α ↪ List Bool}
    {w : α → ℕ} (hw : ComputableInPolyTime w enc encUnary) :
    Circuit.ComputableCircuitCode (fun a => minCircuit (w a)) enc encOp :=
  Circuit.computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_minCircuit.comp hw)

private theorem val_keyBits (k p : ℕ) (i : Fin (k + k)) :
    (keyBits k p i).val = if i.val < k then i.val else (k + p) + (i.val - k) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [keyBits, j.isLt]
  · simp only [keyBits, Fin.append_right, Fin.val_natAdd, Fin.val_castAdd]
    rw [ite_eq_right (by omega)]
    omega

/-- The keyed minimum selector `keyedMinCircuit k p` has a polynomial-time code generator in unary
key width `k` and payload width `p`. -/
theorem computableInPolyTime_keyedMinCircuit :
    ComputableInPolyTime (fun q : ℕ × ℕ => (keyedMinCircuit q.1 q.2).code)
      (encPair encUnary encUnary) encCode := by
  unfold keyedMinCircuit
  have hk : ComputableInPolyTime (fun q : ℕ × ℕ => q.1) (encPair encUnary encUnary) encNat :=
    unary_to_binary.comp (fst encUnary encUnary)
  have hp : ComputableInPolyTime (fun q : ℕ × ℕ => q.2) (encPair encUnary encUnary) encNat :=
    unary_to_binary.comp (snd encUnary encUnary)
  have hkey : Circuit.ComputableCircuitCode
      (fun q : ℕ × ℕ => Circuit.wiring signature (keyBits q.1 q.2))
      (encPair encUnary encUnary) encOp := by
    apply Circuit.computableCircuitCode_wiring
    · fun_prop
    · let encQ := Circuit.encWithFinUnary (encPair encUnary encUnary) fun q => q.1 + q.1
      have hk' := hk.comp (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ)))
      have hp' := hp.comp (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ)))
      have hi' := Circuit.computableInPolyTime_withFinUnary_val_binary (id' (encIn := encQ))
      simp only [val_keyBits]
      fun_prop
  fun_prop

/-- `@[fun_prop]` rule for `keyedMinCircuit` in typed circuit compositions. -/
@[fun_prop] theorem computableCircuitCode_keyedMinCircuit {α : Type} {enc : α ↪ List Bool}
    {k p : α → ℕ} (hk : ComputableInPolyTime k enc encUnary)
    (hp : ComputableInPolyTime p enc encUnary) :
    Circuit.ComputableCircuitCode (fun a => keyedMinCircuit (k a) (p a)) enc encOp := by
  refine Circuit.computableCircuitCode_of_computableInPolyTime (σ := signature) (encOp := encOp) ?_
  simpa only [Function.comp_def] using computableInPolyTime_keyedMinCircuit.comp (hk.prod hp)

end Cslib.Circuits.Boolean
