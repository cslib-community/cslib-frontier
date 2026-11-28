/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.Computability.Circuit.Arithmetic.EvaluationTime
import CslibFrontier.Computability.Circuit.Boolean.Comparison.PolyTime
import CslibFrontier.Computability.Circuit.Boolean.Modular.InnerProduct.PolyTime
import CslibFrontier.Computability.Circuit.Boolean.Modular.Subtract.PolyTime
import CslibFrontier.Computability.Circuit.Encoding.Combinators
import CslibFrontier.Computability.Circuit.Encoding.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.ZMod.Basic

/-!
# Signature-generic circuit codes and shadow-free typed `@[fun_prop]` rules

Checked tests for:
1. Signature-generic `Circuit.code`, `Circuit.ofCode`, `Circuit.compCode`, `Circuit.replicateCode`,
   and `Circuit.balancedCode` on non-Boolean signatures (`arithSignature (ZMod 5)`,
   `arithSignature ℚ` with infinite operation carrier `ArithOp ℚ`, and a ternary threshold gate
   signature).
2. Typed `@[fun_prop]` `ComputableInPolyTime` rules on inline composed circuits over arbitrary
   signatures, `arithSignature ℚ`, and `Boolean.signature` without untyped shadow `*Code` mirrors.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CircuitGenericCodes

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Gate replacement with an unused zero-gate implementation -/

private abbrev unarySignature : Signature where
  Op := Bool
  Arity _ := 1

private def unaryGate : Circuit unarySignature 1 1 := Circuit.oneGate true id

private def replaceUnary : Bool → Circuit unarySignature 1 1
  | true => unaryGate.comp unaryGate
  | false => Circuit.wiring unarySignature id

-- Two source gates expand to four. The second block starts by reading the first block's output.
example : ((unaryGate.comp unaryGate).simulate replaceUnary).code =
    ([(true, [0]), (true, [1]), (true, [2]), (true, [3])], [4]) := by
  rw [Circuit.code_simulate_uniform (unaryGate.comp unaryGate) (τ := unarySignature)
    replaceUnary (B := 2) (by decide) (by decide)]
  decide

/-! ### 1. Arithmetic circuits over `ZMod 5`: `code`, `ofCode`, `compCode`, `evalOutputs` -/

/-- `x₀ + 2` and `x₀ * x₁` in parallel over `ZMod 5`: `(x₀, x₁) ↦ (x₀ + 2, x₀ * x₁)`. -/
private def zmodPairCircuit : Circuit (arithSignature (ZMod 5)) 2 2 :=
  let c2 : Circuit (arithSignature (ZMod 5)) 2 1 :=
    Circuit.oneGate (ArithOp.const 2) Fin.elim0
  let sum : Circuit (arithSignature (ZMod 5)) 2 1 :=
    (Circuit.oneGate ArithOp.add id).comp
      ((Circuit.wiring (arithSignature (ZMod 5)) fun _ => 0).append c2)
  let prod : Circuit (arithSignature (ZMod 5)) 2 1 :=
    Circuit.oneGate ArithOp.mul ![0, 1]
  sum.append prod

/-- Add two inputs `(y₀, y₁) ↦ y₀ + y₁` over `ZMod 5`. -/
private def zmodAddCircuit : Circuit (arithSignature (ZMod 5)) 2 1 :=
  Circuit.oneGate ArithOp.add ![0, 1]

/-- Decoding inverts coding on `arithSignature (ZMod 5)`. -/
example :
    Circuit.ofCode (σ := arithSignature (ZMod 5)) 2 2 zmodPairCircuit.code =
      some zmodPairCircuit :=
  Circuit.ofCode_code zmodPairCircuit

/-- Raw `Circuit.compCode` agrees with typed `Circuit.comp` on `arithSignature (ZMod 5)`. -/
example :
    Circuit.compCode 2 zmodAddCircuit.code zmodPairCircuit.code =
      (zmodAddCircuit.comp zmodPairCircuit).code :=
  (Circuit.code_comp zmodAddCircuit zmodPairCircuit).symm

/-- `evalOutputs` on `arithSignature (ZMod 5)` evaluates `(3 + 2) + (3 * 4) = 0 + 2 = 2 (mod 5)`. -/
example :
    let composed := zmodAddCircuit.comp zmodPairCircuit
    evalOutputs (arithInterpretation (ZMod 5)) 0 composed.code [3, 4] = [2] := by
  decide

/-! ### 2. Infinite operation signature `arithSignature ℚ`: `balancedCode` & typed `@[fun_prop]` -/

/-- Binary encoding of `ArithOp ℚ` via `encRat`. -/
private abbrev encRatOp : ArithOp ℚ ↪ List Bool :=
  ArithOp.encoding encRat

/-- Single rational addition gate `(x, y) ↦ x + y`. -/
private def ratAddGate : Circuit (arithSignature ℚ) 2 1 :=
  Circuit.oneGate ArithOp.add ![0, 1]

/-- Single rational multiplication gate `(x, y) ↦ x * y`. -/
private def ratMulGate : Circuit (arithSignature ℚ) 2 1 :=
  Circuit.oneGate ArithOp.mul ![0, 1]

/-- Constant rational circuit on `n` inputs emitting `q : ℚ`. -/
private def ratConst (n : ℕ) (q : ℚ) : Circuit (arithSignature ℚ) n 1 :=
  Circuit.oneGate (ArithOp.const q) Fin.elim0

/-- `Circuit.balancedCode` is polynomial-time even over the infinite operation type `ArithOp ℚ`
(no `[Finite σ.Op]` assumption). -/
example :
    ComputableInPolyTime
      (fun p : ℕ × List (List (ArithOp ℚ × List ℕ) × List ℕ) =>
        Circuit.balancedCode p.1 ratAddGate.code (ratConst p.1 0).code p.2)
      (encPair encNat (encList (Circuit.encCode encRatOp)))
      (Circuit.encCode encRatOp) := by
  have hn : ComputableInPolyTime
      (fun p : ℕ × List (List (ArithOp ℚ × List ℕ) × List ℕ) => p.1)
      (encPair encNat (encList (Circuit.encCode encRatOp))) encNat :=
    fst encNat _
  have hzero : ComputableInPolyTime
      (fun p : ℕ × List (List (ArithOp ℚ × List ℕ) × List ℕ) => (ratConst p.1 0).code)
      (encPair encNat (encList (Circuit.encCode encRatOp))) (Circuit.encCode encRatOp) := by
    unfold ratConst
    exact Circuit.computableInPolyTime_code_oneGate (σ := arithSignature ℚ) (encOp := encRatOp)
      (ArithOp.const 0) hn fun j => Fin.elim0 j
  exact Circuit.computableInPolyTime_balancedCode hn (const ratAddGate.code) hzero (snd encNat _)

/-- Typed `@[fun_prop]` proves polynomial-time code generation for a composed family of rational
arithmetic circuits directly from `(·.code)`, with no shadow `*Code` definitions. -/
private theorem computableInPolyTime_ratAffineProd :
    ComputableInPolyTime
      (fun n : ℕ =>
        (ratMulGate.comp
          ((Circuit.wiring (arithSignature ℚ) fun _ : Fin 1 => (0 : Fin (n + 1))).append
            (ratConst (n + 1) 1))).code)
      encUnary (Circuit.encCode encRatOp) := by
  have hnb : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat := unary_to_binary
  have hn1 : ComputableInPolyTime (fun n : ℕ => n + 1) encUnary encNat := by fun_prop
  have hw0 : Circuit.ComputableCircuitCode
      (fun n => Circuit.wiring (arithSignature ℚ) fun _ : Fin 1 => (0 : Fin (n + 1)))
      encUnary encRatOp :=
    Circuit.computableCircuitCode_wiring (const 1) (const 0)
  have hc1 : Circuit.ComputableCircuitCode
      (fun n => ratConst (n + 1) 1) encUnary encRatOp :=
    Circuit.computableCircuitCode_of_computableInPolyTime
      (Circuit.computableInPolyTime_code_oneGate (σ := arithSignature ℚ) (encOp := encRatOp)
        (ArithOp.const 1) hn1 fun j => Fin.elim0 j)
  fun_prop

/-! ### 3. Non-Boolean ternary threshold gate: generic `computableInPolyTime_evalOutputs` -/

/-- A single ternary majority gate signature (fan-in 3, neither De Morgan nor binary arithmetic). -/
private abbrev maj3Signature : Signature where
  Op := Unit
  Arity _ := 3

private def maj3Interp : Interpretation maj3Signature Bool :=
  fun _ args =>
    (args 0 && args 1) || (args 0 && args 2) || (args 1 && args 2)

private def encUnit : Unit ↪ List Bool :=
  ⟨fun _ => [], fun _ _ _ => rfl⟩

/-- Generic `computableInPolyTime_evalOutputs` certifies polynomial-time evaluation of runtime
ternary-majority codes without any signature-specific casework. -/
example :
    ComputableInPolyTime
      (fun p : (List (Unit × List ℕ) × List ℕ) × List Bool =>
        evalOutputs maj3Interp false p.1 p.2)
      (encPair (Circuit.encCode encUnit) (encList encBool))
      (encList encBool) := by
  have hc := fst (Circuit.encCode encUnit) (encList encBool)
  have hx := snd (Circuit.encCode encUnit) (encList encBool)
  exact Circuits.computableInPolyTime_evalOutputs maj3Interp false hc hx

/-! ### 4. Signature-polymorphic & Boolean shadow-free typed `@[fun_prop]` compositions -/

/-- Over any `Signature` and explicit `encOp`, `fun_prop` certifies
`((d x).comp ((c x).append (Circuit.id σ (n x)))).code` directly from plain
`ComputableInPolyTime` hypotheses on `(d x).code` and `(c x).code`. -/
private theorem computableInPolyTime_genericComp {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m p : α → ℕ}
    {d : (a : α) → Circuit σ (m a + n a) (p a)} {c : (a : α) → Circuit σ (n a) (m a)}
    (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime (fun a => (d a).code) enc (Circuit.encCode encOp))
    (hc : ComputableInPolyTime (fun a => (c a).code) enc (Circuit.encCode encOp)) :
    ComputableInPolyTime
      (fun a => ((d a).comp ((c a).append (Circuit.id σ (n a)))).code)
      enc (Circuit.encCode encOp) := by
  have hnb : ComputableInPolyTime n enc encNat := unary_to_binary.comp hn
  fun_prop

/-- Inline composition of `Modular.subtract`, `Modular.multiply`, and `minCircuit` certified
directly by `fun_prop` without any shadow `*Code` definitions. -/
private theorem computableInPolyTime_subtract_multiply_min :
    ComputableInPolyTime
      (fun w : ℕ =>
        ((Modular.subtract w).comp ((Modular.multiply w).append (minCircuit w))).code)
      encUnary Boolean.encCode := by
  have hwb : ComputableInPolyTime (fun w : ℕ => w) encUnary encNat := unary_to_binary
  fun_prop

/-- Inline composition of `Modular.subtract` over `Modular.innerProduct`, `replicate`, and
`keyedMinCircuit` certified directly by `fun_prop` without shadow `*Code` definitions. -/
private theorem computableInPolyTime_composedInnerProduct :
    ComputableInPolyTime
      (fun p : ℕ × ℕ =>
        (((Modular.subtract p.2).comp
          ((Modular.innerProduct p.1 p.2).append (Modular.innerProduct p.1 p.2))).replicate
            p.1).code)
      (encPair encUnary encUnary) Boolean.encCode := by
  have hk : ComputableInPolyTime (fun p : ℕ × ℕ => p.1) (encPair encUnary encUnary) encNat :=
    unary_to_binary.comp (fst encUnary encUnary)
  have hw : ComputableInPolyTime (fun p : ℕ × ℕ => p.2) (encPair encUnary encUnary) encNat :=
    unary_to_binary.comp (snd encUnary encUnary)
  fun_prop

example :
    ComputableInPolyTime
      (fun p : ℕ × ℕ => (keyedMinCircuit p.1 p.2).code)
      (encPair encUnary encUnary) Boolean.encCode := by
  fun_prop

/--
info: 'Cslib.Circuits.Boolean.Modular.computableInPolyTime_innerProduct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Circuits.Boolean.Modular.computableInPolyTime_innerProduct

end CslibFrontierTests.CircuitGenericCodes
