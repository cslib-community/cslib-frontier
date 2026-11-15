/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
public import CslibFrontier.Computability.Circuit.Parallel
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native code for two circuits on disjoint inputs

`parallelCode` applies the existing sequential and shared-input code constructors to two raw
circuit codes.  The first code reads the first input block and the second reads the following
block.  This retains each component's internal sharing; it is not a truth-table compiler.

## Main definitions

* `Cslib.Circuits.Boolean.parallelCode`: raw code for two disjoint-input circuits.

## Main results

* `Cslib.Circuits.Boolean.parallelCode_code`: exact agreement with `Circuit.parallel`.
* `Cslib.Circuits.Boolean.computableInPolyTime_parallelCode`: native polynomial-time generation.

These code-composition results are original infrastructure.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

/-- Run raw code `left` on the first `leftInputs` inputs and `right` on the following
`rightInputs` inputs, concatenating their outputs. -/
@[expose] def parallelCode (leftInputs rightInputs : ℕ)
    (left right : List (Op × List ℕ) × List ℕ) : List (Op × List ℕ) × List ℕ :=
  appendCode (leftInputs + rightInputs)
    (compCode (leftInputs + rightInputs) left ([], List.range leftInputs))
    (compCode (leftInputs + rightInputs) right
      ([], (List.range rightInputs).map (leftInputs + ·)))

/-- The raw disjoint-input constructor is exactly the code of typed parallel composition. -/
theorem parallelCode_code {n m p q : ℕ}
    (left : Circuit signature n m) (right : Circuit signature p q) :
    parallelCode n p left.code right.code = (left.parallel right).code := by
  rw [parallelCode, Circuit.parallel]
  rw [show ([], List.range n) = (Circuit.wiring signature (Fin.castAdd p)).code by
    symm
    simpa using Circuit.code_wiring_eq_map
      (σ := signature) (f := Fin.castAdd p) (g := id) (fun _ => rfl)]
  rw [show ([], (List.range p).map (n + ·)) =
      (Circuit.wiring signature (Fin.natAdd n)).code by
    symm
    simpa using Circuit.code_wiring_eq_map
      (σ := signature) (f := Fin.natAdd n) (g := (n + ·)) (fun _ => rfl)]
  rw [compCode_code, compCode_code, appendCode_code]

/-- Parallel composition is generated in polynomial time from unary input-block sizes and the
complete binary-wire encodings of both component codes. -/
@[fun_prop] theorem computableInPolyTime_parallelCode {α : Type} {enc : α ↪ List Bool}
    {n p : α → ℕ} {left right : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encUnary)
    (hleft : ComputableInPolyTime left enc encCode)
    (hright : ComputableInPolyTime right enc encCode) :
    ComputableInPolyTime
      (fun a => parallelCode (n a) (p a) (left a) (right a)) enc encCode := by
  have hn' := unary_to_binary.comp hn
  have hp' := unary_to_binary.comp hp
  have htotal := binary_add' hn' hp'
  have hleftWires : ComputableInPolyTime
      (fun a => List.range (n a)) enc (encList encNat) := by
    have h := unary_to_binary.map.comp (range.comp hn)
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using h
  have hleftInput : ComputableInPolyTime
      (fun a => ([], List.range (n a))) enc encCode :=
    (const (encOut := encList encGate) []).prod hleftWires
  have hrightWires : ComputableInPolyTime
      (fun a => (List.range (p a)).map (n a + ·)) enc (encList encNat) := by
    have hwire : ComputableInPolyTime (fun q : α × ℕ => n q.1 + q.2)
        (encPair enc encUnary) encNat :=
      binary_add' (hn'.comp (fst _ _)) (unary_to_binary.comp (snd _ _))
    exact mapWithInput (range.comp hp) hwire
  have hrightInput : ComputableInPolyTime
      (fun a => ([], (List.range (p a)).map (n a + ·))) enc encCode :=
    (const (encOut := encList encGate) []).prod hrightWires
  exact computableInPolyTime_appendCode htotal
    (computableInPolyTime_compCode htotal hleft hleftInput)
    (computableInPolyTime_compCode htotal hright hrightInput)

end Cslib.Circuits.Boolean
