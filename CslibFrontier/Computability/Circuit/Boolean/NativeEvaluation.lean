/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
public import CslibFrontier.Computability.Circuit.Boolean.OpValue
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Equality
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Retained native evaluation of Boolean circuits

This module keeps the concrete multitape programs used to evaluate De Morgan gate lists and fixed
typed circuits. The raw evaluator scans the encoded gate list once and retains exact native time,
workspace, input, output, and static-description coordinates. The fixed evaluator hardwires one
`installedCode := const (encBitString n) encCode c.code` subcompiler, so callers add no separate
external `c.code` charge. `NativeCompiler.staticBits` charges the complete generated
transition-table description, including all composed evaluator and controller code.

## Main definitions

* `Cslib.Circuits.Boolean.evalCodeStepCompiler`: retained evaluation of one encoded gate.
* `Cslib.Circuits.Boolean.evalCodeCompiler`: retained evaluation of a runtime-supplied gate list.
* `Cslib.Circuits.Boolean.evalCircuitCompiler`: retained evaluation of one fixed typed circuit.

## Main results

* `Cslib.Circuits.Boolean.computableInPolyTime_evalFixedCircuit`: the fixed evaluator's ordinary
  polynomial-time abstraction.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing MultiTapeTM MultiTapeTM.Internal
open MultiTapeTM.Internal.NativeCompiler

/-- Retained evaluation of one De Morgan gate. Missing arguments and out-of-range wires read
`false`, exactly as in `evalCodeStep interpretation false`. -/
@[expose] noncomputable def evalCodeStepCompiler :
    NativeCompiler (evalCodeStep interpretation false)
      (encPair encBits encGate) encBits := by
  let encInput := encPair encBits encGate
  let values := first encBits encGate
  let gate := second encBits encGate
  let op := (first encOp (encList encNat)).comp gate
  let args := (second encOp (encList encNat)).comp gate
  let argument (i : ℕ) : NativeCompiler
      (fun input : List Bool × (Op × List ℕ) =>
        input.2.2[i]?.elim false (input.1.getD · false)) encInput encBool := by
    let indexed := args.pair (const encInput encNat i)
    let wire? := (listGet?NatCompiler encNat).comp indexed
    let present := (optionIsSomeTest encNat).comp wire?
    let wire := (optionGetD 0 encNat).comp wire?
    let read := (bitsGetDNatCompiler false).comp (values.pair wire)
    exact (ite present read (const encInput encBool false)).ofOutputEq fun input => by
      cases h : input.2.2[i]? <;> simp [h]
  let firstArg := argument 0
  let secondArg := argument 1
  let falseCompiler := const encInput encBool false
  let trueCompiler := const encInput encBool true
  let notCompiler := ite (boolToTest.comp firstArg) falseCompiler trueCompiler
  let andCompiler := ite (boolToTest.comp firstArg) secondArg falseCompiler
  let orCompiler := ite (boolToTest.comp firstArg) trueCompiler secondArg
  let isOp (target : Op) :=
    (wordEqTest encOp).comp (op.pair (const encInput encOp target))
  let value :=
    ite (isOp (.const false)) falseCompiler
      (ite (isOp (.const true)) trueCompiler
        (ite (isOp .not) notCompiler (ite (isOp .and) andCompiler orCompiler)))
  let gateValue : NativeCompiler
      (fun input : List Bool × (Op × List ℕ) =>
        input.2.1.value
          (input.2.2[0]?.elim false (input.1.getD · false))
          (input.2.2[1]?.elim false (input.1.getD · false)))
      encInput encBool :=
    value.ofOutputEq fun input => by
      rcases input with ⟨values, op, args⟩
      cases op with
      | const bit => cases bit <;> simp [Op.value]
      | not => simp [Op.value]
      | and => simp [Op.value]
      | or => simp [Op.value]
  let singleton : NativeCompiler
      (fun input : List Bool × (Op × List ℕ) =>
        [input.2.1.value
          (input.2.2[0]?.elim false (input.1.getD · false))
          (input.2.2[1]?.elim false (input.1.getD · false))])
      encInput encBits :=
    gateValue.ofOutputEq fun _ => rfl
  exact (values.append singleton).ofOutputEq fun input => by
    rcases input with ⟨values, op, args⟩
    cases op with
    | const bit => cases bit <;> rfl
    | not => rfl
    | and => rfl
    | or => rfl

/-- Peak lifted-callback workspace over the actual runtime gate-list scan. -/
@[expose] noncomputable def evalCodeSMax
    (input : List Bool × List (Op × List ℕ)) : ℕ :=
  let nextCompiler := evalCodeStepCompiler
  let emitCompiler := const (encPair encBits encGate) encUnit ()
  let finishCompiler := identity encBits
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  (Finset.range input.2.length).sup fun j =>
    if hj : j < input.2.length then
      let pair := (streamState input.1 (evalCodeStep interpretation false) input.2 j,
        input.2[j])
      inputFromWordWorkspace K emitCompiler pair +
        onWordsWorkspace K (streamFramedNext nextCompiler) pair
    else 0

/-- Peak encoded trace/gate length over the actual runtime gate-list scan. -/
@[expose] def evalCodeLMax (input : List Bool × List (Op × List ℕ)) : ℕ :=
  max
    ((Finset.range (input.2.length + 1)).sup fun j =>
      if hj : j ≤ input.2.length then
        (encBits (streamState input.1 (evalCodeStep interpretation false) input.2 j)).length
      else 0)
    ((Finset.range input.2.length).sup fun j =>
      if hj : j < input.2.length then (encGate input.2[j]).length else 0)

/-- Retained evaluation of a runtime-supplied De Morgan gate list. The gate list is input data,
not installed code; every framed gate is scanned by the concrete stream machine. -/
@[expose] noncomputable def evalCodeCompiler :
    NativeCompiler
      (fun input : List Bool × List (Op × List ℕ) =>
        evalCode interpretation false input.1 input.2)
      (encPair encBits (encList encGate)) encBits := by
  let nextCompiler := evalCodeStepCompiler
  let emitCompiler := const (encPair encBits encGate) encUnit ()
  let finishCompiler := identity encBits
  apply streamFoldPair nextCompiler emitCompiler finishCompiler
    (sMax := evalCodeSMax) (lMax := evalCodeLMax)
  · rintro ⟨values, gates⟩
    simp only [encUnit_apply, streamEmit_const_nil, List.nil_append, id_eq]
    congr 1
    simp [streamState, evalCode]
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        let pair := (streamState input.1 (evalCodeStep interpretation false) input.2 j,
          input.2[j])
        inputFromWordWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            emitCompiler pair +
          onWordsWorkspace
            (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
            (streamFramedNext nextCompiler) pair
        else 0)
      (Finset.mem_range.mpr hj)
    simpa only [evalCodeSMax, nextCompiler, emitCompiler, finishCompiler, hj, dite_true]
      using hsup
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range (input.2.length + 1))
      (f := fun j => if hj : j ≤ input.2.length then
        (encBits (streamState input.1 (evalCodeStep interpretation false) input.2 j)).length
        else 0)
      (Finset.mem_range.mpr (by omega : j < input.2.length + 1))
    have hbound :
        (encBits (streamState input.1 (evalCodeStep interpretation false) input.2 j)).length ≤
          (Finset.range (input.2.length + 1)).sup fun j =>
            if hj : j ≤ input.2.length then
              (encBits
                (streamState input.1 (evalCodeStep interpretation false) input.2 j)).length
            else 0 := by
      simpa only [hj, dite_true] using hsup
    exact hbound.trans (Nat.le_max_left _ _)
  · intro input j hj
    have hsup := Finset.le_sup
      (s := Finset.range input.2.length)
      (f := fun j => if hj : j < input.2.length then
        (encGate input.2[j]).length else 0)
      (Finset.mem_range.mpr hj)
    have hbound : (encGate input.2[j]).length ≤
        (Finset.range input.2.length).sup fun j =>
          if hj : j < input.2.length then (encGate input.2[j]).length else 0 := by
      simpa only [hj, dite_true] using hsup
    exact hbound.trans (Nat.le_max_right _ _)

/-- The raw evaluator emits the initial bits followed by exactly one bit per gate. -/
@[simp] theorem outputBits_evalCodeCompiler
    (input : List Bool × List (Op × List ℕ)) :
    evalCodeCompiler.outputBits input = input.1.length + input.2.length := by
  simp [NativeCompiler.outputBits]

/-- Retained evaluation of one fixed typed De Morgan circuit. The construction contains exactly
one `installedCode := const (encBitString n) encCode c.code` subcompiler, so callers add no second
external `encCode c.code` charge. Runtime charges include emitting and marshalling that code on
each invocation. `staticBits` charges the complete generated transition-table description,
including the inlined lookup, evaluator and controller code; it is not a count of literal encoded
code occurrences in that table. -/
@[expose] noncomputable def evalCircuitCompiler {n m : ℕ}
    (c : Circuit signature n m) :
    NativeCompiler (c.eval interpretation) (encBitString n) (encBitString m) := by
  let nextCompiler := first encBits encNat
  let emitCompiler := bitsGetDNatCompiler false
  let finishCompiler := const encBits encBits []
  let outputSMax (input : List Bool × List ℕ) :=
    let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
    (Finset.range input.2.length).sup fun j =>
      if hj : j < input.2.length then
        let pair := (streamState input.1 Prod.fst input.2 j, input.2[j])
        inputFromWordWorkspace K emitCompiler pair +
          onWordsWorkspace K (streamFramedNext nextCompiler) pair
      else 0
  let outputLMax (input : List Bool × List ℕ) :=
    max
      ((Finset.range (input.2.length + 1)).sup fun j =>
        if hj : j ≤ input.2.length then
          (encBits (streamState input.1 Prod.fst input.2 j)).length
        else 0)
      ((Finset.range input.2.length).sup fun j =>
        if hj : j < input.2.length then (encNat input.2[j]).length else 0)
  let outputsCompiler : NativeCompiler
      (fun input : List Bool × List ℕ => input.2.map (input.1.getD · false))
      (encPair encBits (encList encNat)) encBits := by
    apply streamFoldPair nextCompiler emitCompiler finishCompiler
      (sMax := outputSMax) (lMax := outputLMax)
    · rintro ⟨values, outputs⟩
      simp only [Function.const_apply, encBits_apply, List.append_nil]
      induction outputs generalizing values with
      | nil => rfl
      | cons output outputs ih =>
        simp only [List.map_cons, streamEmit, encBool_apply, List.singleton_append]
        congr 1
        simpa only [encBool_apply] using ih values
    · intro input j hj
      have hsup := Finset.le_sup
        (s := Finset.range input.2.length)
        (f := fun j => if hj : j < input.2.length then
          let pair := (streamState input.1 Prod.fst input.2 j, input.2[j])
          inputFromWordWorkspace
              (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
              emitCompiler pair +
            onWordsWorkspace
              (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
              (streamFramedNext nextCompiler) pair
          else 0)
        (Finset.mem_range.mpr hj)
      simpa only [outputSMax, hj, dite_true] using hsup
    · intro input j hj
      have hsup := Finset.le_sup
        (s := Finset.range (input.2.length + 1))
        (f := fun j => if hj : j ≤ input.2.length then
          (encBits (streamState input.1 Prod.fst input.2 j)).length else 0)
        (Finset.mem_range.mpr (by omega : j < input.2.length + 1))
      have hbound : (encBits (streamState input.1 Prod.fst input.2 j)).length ≤
          (Finset.range (input.2.length + 1)).sup fun j =>
            if hj : j ≤ input.2.length then
              (encBits (streamState input.1 Prod.fst input.2 j)).length else 0 := by
        simpa only [hj, dite_true] using hsup
      exact hbound.trans (Nat.le_max_left _ _)
    · intro input j hj
      have hsup := Finset.le_sup
        (s := Finset.range input.2.length)
        (f := fun j => if hj : j < input.2.length then
          (encNat input.2[j]).length else 0)
        (Finset.mem_range.mpr hj)
      have hbound : (encNat input.2[j]).length ≤
          (Finset.range input.2.length).sup fun j =>
            if hj : j < input.2.length then (encNat input.2[j]).length else 0 := by
        simpa only [hj, dite_true] using hsup
      exact hbound.trans (Nat.le_max_right _ _)
  let encRuntime := encPair encBits encCode
  let values := first encBits encCode
  let code := second encBits encCode
  let gates := (first (encList encGate) (encList encNat)).comp code
  let outputs := (second (encList encGate) (encList encNat)).comp code
  let trace := evalCodeCompiler.comp (values.pair gates)
  let runtime : NativeCompiler
      (fun input : List Bool × Cslib.Complexity.CircuitCode =>
        Cslib.Complexity.evalCircuitOutputs input.2 input.1)
      encRuntime encBits :=
    outputsCompiler.comp (trace.pair outputs)
  let rawInput : NativeCompiler (fun x : Cslib.BitString n => List.ofFn x)
      (encBitString n) encBits :=
    (identity (encBitString n)).ofOutputEq fun x => by
      simp only [encBitString_apply, encBits_apply, id_eq]
  let installedCode := const (encBitString n) encCode c.code
  let fixed := runtime.comp (rawInput.pair installedCode)
  exact fixed.ofOutputEq fun x => by
    simpa only [encBitString_apply, encBits_apply, Function.const_apply] using congrArg encBits
      (Cslib.Complexity.evalCircuitOutputs_code c x).symm

/-- A fixed `n`-by-`m` circuit evaluator emits exactly `m` raw output bits. -/
@[simp] theorem outputBits_evalCircuitCompiler {n m : ℕ}
    (c : Circuit signature n m) (input : Cslib.BitString n) :
    (evalCircuitCompiler c).outputBits input = m := by
  simp [NativeCompiler.outputBits, encBitString_apply]

/-- Forget the fixed evaluator's concrete program and resource coordinates to the ordinary
polynomial-time interface. The proof packages the retained machine itself, bounded by the maxima
of its exact time and workspace maps over the fixed-width input type. -/
@[fun_prop] theorem computableInPolyTime_evalFixedCircuit {n m : ℕ}
    (c : Circuit signature n m) :
    ComputableInPolyTime (c.eval interpretation) (encBitString n) (encBitString m) := by
  let compiler := evalCircuitCompiler c
  let tMax := Finset.univ.sup compiler.time
  let sMax := Finset.univ.sup compiler.workspace
  refine ⟨fun _ => tMax, fun _ => sMax,
    polynomiallyBounded_iff_le.mpr ⟨tMax, 0, fun _ => by simp⟩,
    polynomiallyBounded_iff_le.mpr ⟨sMax, 0, fun _ => by simp⟩, ?_⟩
  exact compiler.computableInTimeAndSpace.mono
    (fun input => Finset.le_sup (f := compiler.time) (Finset.mem_univ input))
    (fun input => Finset.le_sup (f := compiler.workspace) (Finset.mem_univ input))

end Cslib.Circuits.Boolean
