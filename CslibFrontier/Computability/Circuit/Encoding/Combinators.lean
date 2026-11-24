/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Balanced
public import CslibFrontier.Computability.Circuit.Encoding.Basic
public import CslibFrontier.Computability.Circuit.Formula
public import CslibFrontier.Computability.Circuit.Replication
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Data.List.TakeDrop

/-!
# Signature-generic circuit code combinators and typed `fun_prop` bridges

Wire-relocating transformations on raw circuit codes (`List (Op × List ℕ) × List ℕ`) depend only
on wire numbers, never on the operation type `Op`:

* `Circuit.appendCode`, `Circuit.appendCodes`, `Circuit.bundleCode`: combine raw circuit codes on
  shared inputs, matching `Circuit.append` and `Circuit.pi`.
* `Circuit.compCode`: sequential composition feeding the outputs of one raw code into the inputs of
  another, matching `Circuit.comp`.
* `Circuit.replicateCode`: disjoint-input copies of a raw code, matching `Circuit.replicate`.
* `Circuit.formulaCode`: instantiate a fixed `Formula σ m` at raw wire numbers, matching
  `Formula.rename` followed by `Formula.toCircuit`.
* `Circuit.balancedCode`: combine raw leaf codes along the exact half-split tree of
  `Circuit.balanced` without arity-sized loops.

Each raw combinator is polynomial-time under `Circuit.encCode encOp` for any explicit operation
encoding `encOp : Op ↪ List Bool` (with no finiteness assumption on `Op`), and each has a typed
`Circuit.code_*` bridge equation. Layering `of_enc_eq` on those bridges gives direct `@[fun_prop]`
rules for `(fun a => (C a).code)` across `Circuit.wiring`, `Circuit.oneGate`, `Circuit.append`,
`Circuit.pi`, `Circuit.comp`, `Circuit.replicate`, `Circuit.balanced`, and `Formula.toCircuit`, so
uniform circuit-family proofs compose directly over typed `Circuit` definitions.

## Main definitions

* `Cslib.Circuits.Program.appendWireCode`: wire-number map under program continuation.
* `Cslib.Circuits.Circuit.shiftCodeWire`, `Cslib.Circuits.Circuit.shiftCode`,
  `Cslib.Circuits.Circuit.appendCode`, `Cslib.Circuits.Circuit.appendCodes`,
  `Cslib.Circuits.Circuit.bundleCode`: shared-input raw code combinators.
* `Cslib.Circuits.Circuit.compCodeWire`, `Cslib.Circuits.Circuit.compCode`: sequential raw code
  composition.
* `Cslib.Circuits.Circuit.replicateWire`, `Cslib.Circuits.Circuit.replicateCode`: disjoint-input
  raw code replication.
* `Cslib.Circuits.Circuit.formulaCode`: raw wire instantiation of a fixed `Formula`.
* `Cslib.Circuits.Circuit.balancedCode`: half-split balanced raw code fold.
* `Cslib.Circuits.Circuit.encWithFinUnary`: explicit encoding of `(Σ a : α, Fin (k a))` pairing an
  encoded input with a unary `Fin` index.
* `Cslib.Circuits.Circuit.ComputableCircuitCode`: `@[fun_prop]` predicate indexing uniform
  polynomial-time `(·.code)` generation by the outer `Circuit` constructor rather than colliding on
  `Circuit.code`.

## Main results

* `Cslib.Circuits.Program.code_append`: code of program continuation.
* `Cslib.Circuits.Circuit.code_oneGate`, `Cslib.Circuits.Circuit.code_append`,
  `Cslib.Circuits.Circuit.code_pi`, `Cslib.Circuits.Circuit.code_pi_bundle`,
  `Cslib.Circuits.Circuit.code_comp`, `Cslib.Circuits.Circuit.code_replicate`,
  `Cslib.Circuits.Circuit.code_balanced`, `Cslib.Circuits.Circuit.formulaCode_eq_code`: typed
  `Circuit.code` bridge equations over an arbitrary `Signature`.
* `Cslib.Circuits.Circuit.computableInPolyTime_appendCode`,
  `Cslib.Circuits.Circuit.computableInPolyTime_appendCodes`,
  `Cslib.Circuits.Circuit.computableInPolyTime_bundleCode`,
  `Cslib.Circuits.Circuit.computableInPolyTime_compCode`,
  `Cslib.Circuits.Circuit.computableInPolyTime_replicateCode`,
  `Cslib.Circuits.Circuit.computableInPolyTime_formulaCode`,
  `Cslib.Circuits.Circuit.computableInPolyTime_balancedCode`: polynomial-time raw code
  combinators.
* `Cslib.Circuits.Circuit.computableInPolyTime_code`,
  `Cslib.Circuits.Circuit.computableCircuitCode_id`,
  `Cslib.Circuits.Circuit.computableCircuitCode_wiring`,
  `Cslib.Circuits.Circuit.computableCircuitCode_append`,
  `Cslib.Circuits.Circuit.computableCircuitCode_pi`,
  `Cslib.Circuits.Circuit.computableCircuitCode_comp`,
  `Cslib.Circuits.Circuit.computableCircuitCode_replicate`,
  `Cslib.Circuits.Circuit.computableCircuitCode_balanced`,
  `Cslib.Circuits.Circuit.computableCircuitCode_ite`: constructor-indexed `@[fun_prop]` rules for
  `(fun a => (c a).code)`.
* `Cslib.Circuits.Circuit.computableInPolyTime_code_id`,
  `Cslib.Circuits.Circuit.computableInPolyTime_code_wiring`,
  `Cslib.Circuits.Circuit.computableInPolyTime_code_oneGate`,
  `Cslib.Circuits.Circuit.computableInPolyTime_code_append`,
  `Cslib.Circuits.Circuit.computableInPolyTime_code_pi`,
  `Cslib.Circuits.Circuit.computableInPolyTime_code_comp`,
  `Cslib.Circuits.Circuit.computableInPolyTime_code_replicate`,
  `Cslib.Circuits.Circuit.computableInPolyTime_code_balanced`,
  `Cslib.Circuits.Formula.computableInPolyTime_code_gate_toCircuit`: direct typed
  `ComputableInPolyTime` code-generation theorems.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

public section

namespace Cslib.Circuits

namespace Program

universe v

variable {σ : Signature.{v}} {n m s t : ℕ}

private theorem code_mapWires (line : Line σ m t) (f : Wire m t → Wire n s)
    (ren : ℕ → ℕ) (h : ∀ w, (f w).toNat = ren w.toNat) :
    (line.mapWires f).code = (line.code.1, line.code.2.map ren) := by
  simp only [Line.code, Line.mapWires, List.map_ofFn]
  congr 2 with i : 1
  exact h (line.wires i)

/-- The wire-number map when continuing a program with another program. -/
@[expose] def appendWireCode (n m s : ℕ) (feed : Fin m → Wire n s) (i : ℕ) : ℕ :=
  if h : i < m then (feed ⟨i, h⟩).toNat else n + s + (i - m)

/-- Numbering a continued wire agrees with the raw wire-number map. -/
theorem appendedWire_toNat (feed : Fin m → Wire n s) (w : Wire m t) :
    (appendedWire feed w).toNat = appendWireCode n m s feed w.toNat := by
  cases w with
  | input i =>
      cases h : feed i <;> simp [appendWireCode, h, Wire.toNat]
  | gate j => simp [appendWireCode, Wire.toNat, Nat.add_assoc]

/-- Program continuation acts on codes by appending the rewired gate list. -/
theorem code_append (p : Program σ n s) (feed : Fin m → Wire n s) (q : Program σ m t) :
    (p.append feed q).code = p.code ++
      q.code.map (fun g => (g.1, g.2.map (appendWireCode n m s feed))) := by
  induction q with
  | empty => simp [append]
  | gate q line ih =>
    simp only [append, code_gate, ih, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, code_mapWires line (appendedWire feed) _ (appendedWire_toNat feed)]

end Program

namespace Circuit

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Shared-input append and bundling -/

section RawCombinators

universe v

/-- Retain an input wire, or shift a gate wire past `offset` preceding gates. -/
@[expose] def shiftCodeWire (n offset i : ℕ) : ℕ := if i < n then i else i + offset

/-- Shift the gate references and output references of a raw code. Input wires are preserved. -/
@[expose] def shiftCode {Op : Type*} (n offset : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  (code.1.map (fun g => (g.1, g.2.map (shiftCodeWire n offset))),
    code.2.map (shiftCodeWire n offset))

/-- Run two raw codes on shared inputs, listing the first code's outputs before the second's.
Malformed codes are transformed as data; semantic correctness is asserted on typed circuits. -/
@[expose] def appendCode {Op : Type*} (n : ℕ) (c d : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  (c.1 ++ d.1.map (fun g => (g.1, g.2.map (shiftCodeWire n c.1.length))),
    c.2 ++ d.2.map (shiftCodeWire n c.1.length))

/-- Appending two raw codes sums their gate counts. -/
@[simp] theorem length_appendCode {Op : Type*} (n : ℕ) (c d : List (Op × List ℕ) × List ℕ) :
    (appendCode n c d).1.length = c.1.length + d.1.length := by
  simp [appendCode]

/-- Appending two raw codes sums their output counts. -/
@[simp] theorem length_appendCode_outputs {Op : Type*} (n : ℕ)
    (c d : List (Op × List ℕ) × List ℕ) :
    (appendCode n c d).2.length = c.2.length + d.2.length := by
  simp [appendCode]

private theorem appendWireCode_input (n offset : ℕ) :
    Program.appendWireCode n n offset Wire.input = shiftCodeWire n offset := by
  funext i
  by_cases hi : i < n
  · simp [Program.appendWireCode, shiftCodeWire, hi]
  · simp only [Program.appendWireCode, shiftCodeWire, dite_eq_right hi, ite_eq_right hi]
    omega

private theorem toNat_castAdd {n k : ℕ} (w : Wire n k) (extra : ℕ) :
    (w.castAdd extra).toNat = w.toNat := by
  cases w <;> rfl

/-- The serialized code of `c.append d` is `appendCode n c.code d.code`. -/
theorem code_append {σ : Signature.{v}} {n m p : ℕ} (c : Circuit σ n m) (d : Circuit σ n p) :
    (c.append d).code = appendCode n c.code d.code := by
  symm
  simp only [appendCode, Circuit.code, Circuit.append, Program.code_append,
    appendWireCode_input]
  apply Prod.ext
  · rw [Program.length_code]
  rw [show (fun j => (Fin.append (Wire.castAdd d.size ∘ c.outputs)
    (Program.appendedWire Wire.input ∘ d.outputs) j).toNat) =
      Fin.append (fun j => (c.outputs j).toNat)
        (fun j => shiftCodeWire n c.size (d.outputs j).toNat) from ?_]
  · simp only [List.ofFn_fin_append, List.map_ofFn]
    rw [Program.length_code]
    rfl
  · funext j
    induction j using Fin.addCases with
    | left i => simp [toNat_castAdd]
    | right i =>
      simp only [Fin.append_right, Function.comp_apply, Program.appendedWire_toNat,
        appendWireCode_input]

/-- Combine a list of raw codes on shared inputs, preserving block and output order.
Blocks may have different gate counts and any number of outputs. -/
@[expose] def appendCodes {Op : Type*} (n : ℕ) (codes : List (List (Op × List ℕ) × List ℕ)) :
    List (Op × List ℕ) × List ℕ :=
  codes.foldl (appendCode n) ([], [])

/-- Combining an empty list of raw codes yields the empty code. -/
@[simp] theorem appendCodes_nil {Op : Type*} (n : ℕ) :
    appendCodes n ([] : List (List (Op × List ℕ) × List ℕ)) = ([], []) := rfl

/-- Adding a final block is ordinary shared-input append. -/
theorem appendCodes_append_singleton {Op : Type*} (n : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) (code : List (Op × List ℕ) × List ℕ) :
    appendCodes n (codes ++ [code]) = appendCode n (appendCodes n codes) code := by
  simp [appendCodes]

/-- The combined code retains every gate, without padding the individual blocks. -/
@[simp] theorem length_appendCodes {Op : Type*} (n : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) :
    (appendCodes n codes).1.length = (codes.flatMap Prod.fst).length := by
  induction codes using List.reverseRecOn with
  | nil => rfl
  | append_singleton codes code ih =>
    simp [appendCodes_append_singleton, ih]

/-- The combined code retains all outputs, including repeated outputs and zero-gate blocks. -/
@[simp] theorem length_appendCodes_outputs {Op : Type*} (n : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) :
    (appendCodes n codes).2.length = (codes.flatMap Prod.snd).length := by
  induction codes using List.reverseRecOn with
  | nil => rfl
  | append_singleton codes code ih =>
    simp [appendCodes_append_singleton, ih]

private def appendCodesDirect {Op : Type*} (n : ℕ) (codes : List (List (Op × List ℕ) × List ℕ)) :
    List (Op × List ℕ) × List ℕ :=
  (codes.zipIdx.flatMap fun q =>
      (shiftCode n ((codes.take q.2).flatMap Prod.fst).length q.1).1,
    codes.zipIdx.flatMap fun q =>
      (shiftCode n ((codes.take q.2).flatMap Prod.fst).length q.1).2)

private theorem appendCodesDirect_snoc {Op : Type*} (n : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) (code : List (Op × List ℕ) × List ℕ) :
    appendCodesDirect n (codes ++ [code]) =
      ((appendCodesDirect n codes).1 ++
          (shiftCode n (codes.flatMap Prod.fst).length code).1,
        (appendCodesDirect n codes).2 ++
          (shiftCode n (codes.flatMap Prod.fst).length code).2) := by
  have hprefix (q : (List (Op × List ℕ) × List ℕ) × ℕ) (hq : q ∈ codes.zipIdx) :
      (codes ++ [code]).take q.2 = codes.take q.2 :=
    List.take_append_of_le_length (by have := List.snd_lt_of_mem_zipIdx hq; omega)
  simp only [appendCodesDirect, List.zipIdx_append, List.flatMap_append, List.zipIdx_cons,
    List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, Nat.zero_add,
    List.take_left, List.append_nil]
  apply Prod.ext <;> dsimp only <;> congr 1 <;>
    apply List.flatMap_congr <;> intro q hq <;> rw [hprefix q hq]

private theorem appendCodesDirect_eq_appendCodes {Op : Type*} (n : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) :
    appendCodesDirect n codes = appendCodes n codes := by
  induction codes using List.reverseRecOn with
  | nil => rfl
  | append_singleton codes code ih =>
    rw [appendCodesDirect_snoc, appendCodes_append_singleton, ih]
    simp only [appendCode, length_appendCodes, shiftCode]

/-- The serialized code of `Circuit.pi cs` is `appendCodes n` of the component codes. -/
theorem code_pi {σ : Signature.{v}} {k n : ℕ} (cs : Fin k → Circuit σ n 1) :
    (Circuit.pi cs).code = appendCodes n (List.ofFn (fun j => (cs j).code)) := by
  symm
  induction k with
  | zero => simp [Circuit.pi, Circuit.code, Circuit.wiring]
  | succ k ih =>
    rw [List.ofFn_succ_last, appendCodes_append_singleton,
      ih (fun j => cs j.castSucc), ← code_append]
    rfl

/-- Combine equal-sized gate blocks on shared inputs. Block `j` is relocated by `j * blockSize`.
The construction is total on raw data; its append semantics requires the stated block sizes. -/
@[expose] def bundleCode {Op : Type*} (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) : List (Op × List ℕ) × List ℕ :=
  (codes.zipIdx.flatMap fun q => (shiftCode n (q.2 * blockSize) q.1).1,
    codes.zipIdx.flatMap fun q => (shiftCode n (q.2 * blockSize) q.1).2)

private theorem bundleCode_snoc {Op : Type*} (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) (code : List (Op × List ℕ) × List ℕ) :
    bundleCode n blockSize (codes ++ [code]) =
      ((bundleCode n blockSize codes).1 ++ (shiftCode n (codes.length * blockSize) code).1,
        (bundleCode n blockSize codes).2 ++ (shiftCode n (codes.length * blockSize) code).2) := by
  simp [bundleCode, List.zipIdx_append]

/-- Equal-sized blocks occupy exactly their number times their common gate count. -/
theorem length_bundleCode {Op : Type*} (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ))
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    (bundleCode n blockSize codes).1.length = codes.length * blockSize := by
  induction codes using List.reverseRecOn with
  | nil => simp [bundleCode]
  | append_singleton codes code ih =>
    rw [bundleCode_snoc]
    simp only [List.length_append, shiftCode, List.length_map, List.length_singleton,
      Nat.add_mul, Nat.one_mul]
    rw [ih (fun c hc => hlen c (List.mem_append_left _ hc)), hlen code (by simp)]

/-- Adding the next equal-sized block is shared-input append. -/
theorem bundleCode_append_singleton {Op : Type*} (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) (code : List (Op × List ℕ) × List ℕ)
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    bundleCode n blockSize (codes ++ [code]) =
      appendCode n (bundleCode n blockSize codes) code := by
  rw [bundleCode_snoc]
  simp only [appendCode, length_bundleCode n blockSize codes hlen, shiftCode]

/-- For equal-sized blocks, direct relocation agrees with repeated shared-input append. -/
theorem bundleCode_eq_foldl_appendCode {Op : Type*} (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ))
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    bundleCode n blockSize codes = codes.foldl (appendCode n) ([], []) := by
  induction codes using List.reverseRecOn with
  | nil => rfl
  | append_singleton codes code ih =>
    have hprefix : ∀ c ∈ codes, c.1.length = blockSize :=
      fun c hc => hlen c (List.mem_append_left _ hc)
    rw [bundleCode_snoc, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih hprefix]
    simp only [appendCode, length_bundleCode n blockSize codes hprefix, shiftCode]

/-- Fixed-size bundling is a specialization of the varying-size constructor. -/
theorem bundleCode_eq_appendCodes {Op : Type*} (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ))
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    bundleCode n blockSize codes = appendCodes n codes :=
  bundleCode_eq_foldl_appendCode n blockSize codes hlen

/-- When every component has size `blockSize`, `bundleCode` computes `(Circuit.pi cs).code`. -/
theorem code_pi_bundle {σ : Signature.{v}} {k n : ℕ} (cs : Fin k → Circuit σ n 1) (blockSize : ℕ)
    (hs : ∀ j, (cs j).size = blockSize) :
    (Circuit.pi cs).code = bundleCode n blockSize (List.ofFn (fun j => (cs j).code)) := by
  rw [code_pi, bundleCode_eq_appendCodes]
  intro c hc
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
  exact (length_code_fst _).trans (hs j)

/-! ### Sequential composition -/

/-- Route a later circuit's inputs through `c`'s outputs and shift its gates past `c`'s gates. -/
@[expose] def compCodeWire {Op : Type*} (n : ℕ) (c : List (Op × List ℕ) × List ℕ) (i : ℕ) : ℕ :=
  if i < c.2.length then c.2.getD i 0 else n + c.1.length + (i - c.2.length)

/-- Feed the outputs of `c` to the inputs of `d`, matching the argument order of `Circuit.comp`.
The constructor is total on raw data, including malformed circuit codes. -/
@[expose] def compCode {Op : Type*} (n : ℕ) (d c : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  (c.1 ++ d.1.map (fun g => (g.1, g.2.map (compCodeWire n c))),
    d.2.map (compCodeWire n c))

private theorem compCodeWire_code {σ : Signature.{v}} {n m : ℕ} (c : Circuit σ n m) (i : ℕ) :
    compCodeWire n c.code i = Program.appendWireCode n m c.size c.outputs i := by
  have hlength := Program.length_code c.program
  by_cases hi : i < m <;>
    simp [compCodeWire, Circuit.code, Program.appendWireCode, hi,
      List.getD_eq_getElem?_getD, hlength]

/-- The serialized code of `d.comp c` is `compCode n d.code c.code`. -/
theorem code_comp {σ : Signature.{v}} {n m p : ℕ} (d : Circuit σ m p) (c : Circuit σ n m) :
    (d.comp c).code = compCode n d.code c.code := by
  symm
  have hwire : compCodeWire n c.code =
      Program.appendWireCode n m c.size c.outputs := funext (compCodeWire_code c)
  apply Prod.ext
  · simp only [compCode, Circuit.code, Circuit.comp, Program.code_append]
    change c.program.code ++ d.program.code.map (fun g => (g.1, g.2.map
      (compCodeWire n c.code))) = _
    rw [hwire]
  · simp only [compCode, Circuit.code, Circuit.comp, List.map_ofFn, Function.comp_apply]
    congr 1 with i : 1
    rw [Program.appendedWire_toNat]
    exact compCodeWire_code c _

/-- Sequential composition retains both gate lists. -/
@[simp] theorem length_compCode {Op : Type*} (n : ℕ) (d c : List (Op × List ℕ) × List ℕ) :
    (compCode n d c).1.length = c.1.length + d.1.length := by
  simp [compCode]

/-- Sequential composition retains the later circuit's number of outputs. -/
@[simp] theorem length_compCode_outputs {Op : Type*} (n : ℕ) (d c : List (Op × List ℕ) × List ℕ) :
    (compCode n d c).2.length = d.2.length := by
  simp [compCode]

/-! ### Disjoint-input replication -/

/-- The number of wire `i` of a circuit with `n` inputs and `s` gates in copy `t` of `k`
disjoint copies: input `i < n` is input `t * n + i` of the replicated circuit, and gate wire
`n + g` is gate `t * s + g` of the replicated circuit. -/
@[expose] def replicateWire (n s k t i : ℕ) : ℕ :=
  if i < n then t * n + i else k * n + t * s + (i - n)

/-- The code of `k` disjoint copies of the circuit with code `code` on `n` inputs. -/
@[expose] def replicateCode {Op : Type*} (n k : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  ((List.range k).flatMap fun t =>
      code.1.map fun g => (g.1, g.2.map (replicateWire n code.1.length k t)),
    (List.range k).flatMap fun t => code.2.map (replicateWire n code.1.length k t))

private theorem code_wiring_cast {σ : Signature.{v}} {a b : ℕ} (h : a = b) :
    (wiring σ (Fin.cast h)).code = ([], List.range a) := by
  simpa using code_wiring_eq_map (σ := σ) (f := Fin.cast h) (g := _root_.id) fun _ => rfl

private theorem compCode_range_left {Op : Type*} (n L : ℕ) (X : List (Op × List ℕ) × List ℕ)
    (h : X.2.length = L) : compCode n ([], List.range L) X = X := by
  subst h
  obtain ⟨gs, outs⟩ := X
  simp only [compCode, List.map_nil, List.append_nil, Prod.mk.injEq, true_and]
  apply List.ext_getElem (by simp)
  intro i hi _
  simp only [List.length_map, List.length_range] at hi
  simp [compCodeWire, hi, List.getD_eq_getElem?_getD]

private theorem compCode_range_right {Op : Type*} (n L : ℕ) (X : List (Op × List ℕ) × List ℕ)
    (h : L = n) : compCode n X ([], List.range L) = X := by
  rw [h]
  obtain ⟨gs, outs⟩ := X
  have hw : compCodeWire (Op := Op) n ([], List.range n) = _root_.id := by
    funext i
    by_cases hi : i < n <;> simp [compCodeWire, hi, List.getD_eq_getElem?_getD]
    omega
  simp [compCode, hw]

private theorem compCodeWire_range_map {Op : Type*} (N L : ℕ) (g : ℕ → ℕ) (i : ℕ) :
    compCodeWire (Op := Op) N ([], (List.range L).map g) i =
      if i < L then g i else N + (i - L) := by
  by_cases hi : i < L <;>
    simp [compCodeWire, hi, List.getD_eq_getElem?_getD]

/-- Replicating a raw code multiplies its gate count by `k`. -/
@[simp] theorem length_replicateCode {Op : Type*} (n k : ℕ)
    (code : List (Op × List ℕ) × List ℕ) :
    (replicateCode n k code).1.length = k * code.1.length := by
  simp [replicateCode, List.length_flatMap, List.sum_replicate]

/-- The serialized code of `c.replicate k` is `replicateCode n k c.code`. -/
theorem code_replicate {σ : Signature.{v}} {n m : ℕ} (c : Circuit σ n m) (k : ℕ) :
    (c.replicate k).code = replicateCode n k c.code := by
  symm
  induction k with
  | zero => simp [replicateCode, Circuit.replicate, Circuit.parallelFamily, code_wiring]
  | succ k ih =>
    rw [show c.replicate (k + 1) = (wiring σ (Fin.cast (Nat.succ_mul k m))).comp
        (((c.replicate k).parallel c).comp
          (wiring σ (Fin.cast (Nat.succ_mul k n).symm))) from rfl,
      code_comp, code_comp, code_wiring_cast, code_wiring_cast,
      compCode_range_right _ _ _ (Nat.succ_mul k n).symm,
      compCode_range_left _ _ _ (by simp [Circuit.code, Nat.succ_mul]),
      Circuit.parallel, code_append, code_comp, code_comp,
      code_wiring_eq_map (σ := σ) (f := Fin.castAdd n) (g := _root_.id) (fun _ => rfl),
      code_wiring_eq_map (σ := σ) (f := Fin.natAdd (k * n)) (g := (k * n + ·)) (fun _ => rfl),
      ← ih]
    have hA : ∀ t ∈ List.range k,
        compCodeWire (Op := σ.Op) (k * n + n) ([], (List.range (k * n)).map _root_.id) ∘
          replicateWire n c.code.1.length k t = replicateWire n c.code.1.length (k + 1) t := by
      intro t ht
      have ht := List.mem_range.1 ht
      funext i
      simp only [Function.comp_apply, compCodeWire_range_map, replicateWire, Nat.succ_mul, id_eq]
      have : t * n + n ≤ k * n := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right n ht
      split_ifs <;> omega
    have hB : shiftCodeWire (k * n + n) (k * c.code.1.length) ∘
        compCodeWire (Op := σ.Op) (k * n + n) ([], (List.range n).map (k * n + ·)) =
          replicateWire n c.code.1.length (k + 1) k := by
      funext i
      simp only [Function.comp_apply, compCodeWire_range_map, replicateWire, shiftCodeWire,
        Nat.succ_mul]
      split_ifs <;> omega
    simp only [replicateCode, appendCode, compCode, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.map_flatMap, List.map_map, List.nil_append, Prod.mk.injEq,
      List.length_flatMap, List.length_map, List.map_const', List.sum_replicate,
      List.length_range, smul_eq_mul]
    refine ⟨?_, ?_⟩
    · congr 1
      · apply List.flatMap_congr
        intro t ht
        apply List.map_congr_left
        intro g _
        simp only [Function.comp_apply, List.map_map, hA t ht]
      · apply List.map_congr_left
        intro g _
        simp only [Function.comp_apply, List.map_map, hB]
    · congr 1
      · apply List.flatMap_congr
        intro t ht
        rw [hA t ht]
      · rw [hB]

/-! ### Single-gate and formula-template serialization -/

/-- The serialized code of `Circuit.oneGate op args` on `n` inputs has one gate reading the wire
indices `(args a).val` and designated output wire `n`. -/
theorem code_oneGate {σ : Signature.{v}} {n : ℕ} (op : σ.Op) (args : Fin (σ.Arity op) → Fin n) :
    (oneGate op args).code = ([(op, List.ofFn fun a => (args a).val)], [n]) := by
  simp [oneGate, Circuit.code, Line.code]

/-- Instantiate a formula `F` over `σ` at raw wire numbers. Total even when a selected wire is
outside the declared input count; typed correctness holds on `Fin n`-valued wires. -/
@[expose] def formulaCode {σ : Signature.{v}} {m : ℕ} (n : ℕ) (F : Formula σ m)
    (wires : Fin m → ℕ) : List (σ.Op × List ℕ) × List ℕ :=
  match F with
  | .input i => ([], [wires i])
  | .gate op args => compCode n (oneGate (σ := σ) op _root_.id).code
      (appendCodes n (List.ofFn fun i => formulaCode n (args i) wires))

/-- Instantiating valid input wires constructs the exact circuit code of
`(F.rename wires).toCircuit`. -/
theorem formulaCode_eq_code {σ : Signature.{v}} {n m : ℕ} (F : Formula σ m)
    (wires : Fin m → Fin n) :
    formulaCode n F (fun i => (wires i).val) = (F.rename wires).toCircuit.code := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    simp only [formulaCode, ih, ← code_pi, ← code_comp,
      Formula.rename, Formula.gate_bind, Formula.toCircuit]

end RawCombinators

/-! ### Polynomial-time certificates for raw combinators -/

section PolyTimeRaw

variable {Op α : Type} {encOp : Op ↪ List Bool} {enc : α ↪ List Bool}

/-- Shifting wire numbers is polynomial-time with all quantities encoded in binary. -/
@[fun_prop]
theorem computableInPolyTime_shiftCodeWire {n offset i : α → ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hoffset : ComputableInPolyTime offset enc encNat)
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun a => shiftCodeWire (n a) (offset a) (i a)) enc encNat := by
  unfold shiftCodeWire
  fun_prop

/-- Relocating a circuit-code block is polynomial-time with binary offsets. -/
@[fun_prop]
theorem computableInPolyTime_shiftCode {n offset : α → ℕ}
    {code : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hoffset : ComputableInPolyTime offset enc encNat)
    (hcode : ComputableInPolyTime code enc (encCode encOp)) :
    ComputableInPolyTime (fun a => shiftCode (n a) (offset a) (code a)) enc (encCode encOp) := by
  fun_prop [shiftCode]

/-- Combining circuit codes is polynomial-time, including binary input and wire counts. -/
@[fun_prop]
theorem computableInPolyTime_appendCode {n : α → ℕ}
    {c d : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hc : ComputableInPolyTime c enc (encCode encOp))
    (hd : ComputableInPolyTime d enc (encCode encOp)) :
    ComputableInPolyTime (fun a => appendCode (n a) (c a) (d a)) enc (encCode encOp) := by
  have hlen : ComputableInPolyTime (fun a => (c a).1.length) enc encNat :=
    (length_list_binary (encGate encOp)).comp hc.fst'
  have hshift := computableInPolyTime_shiftCode hn hlen hd
  exact (listAppend' hc.fst' hshift.fst').prod (listAppend' hc.snd' hshift.snd')

/-- Combining arbitrary raw blocks is polynomial-time in their complete encodings.
Input and wire numbers are binary; no uniform block-size or well-formedness premise is needed. -/
@[fun_prop]
theorem computableInPolyTime_appendCodes {n : α → ℕ}
    {codes : α → List (List (Op × List ℕ) × List ℕ)}
    (hn : ComputableInPolyTime n enc encNat)
    (hcodes : ComputableInPolyTime codes enc (encList (encCode encOp))) :
    ComputableInPolyTime (fun a => appendCodes (n a) (codes a)) enc (encCode encOp) := by
  let encBlock := encPair (encCode encOp) encUnary
  have hblocks : ComputableInPolyTime (fun a => (codes a).zipIdx) enc (encList encBlock) := by
    fun_prop
  have hpar := fst enc encBlock
  have hentry := snd enc encBlock
  have hprefix : ComputableInPolyTime
      (fun q : α × ((List (Op × List ℕ) × List ℕ) × ℕ) => (codes q.1).take q.2.2)
      (encPair enc encBlock) (encList (encCode encOp)) := by
    fun_prop
  have hprefixGates := flatMapWithInput (encB := encGate encOp)
    (f := fun (_ : α × ((List (Op × List ℕ) × List ℕ) × ℕ)) c => c.1)
    hprefix ((snd _ (encCode encOp)).fst')
  have hoffset := (length_list_binary (encGate encOp)).comp hprefixGates
  have hshift := computableInPolyTime_shiftCode (hn.comp hpar) hoffset hentry.fst'
  have hgates := flatMapWithInput (encB := encGate encOp)
    (f := fun a (q : (List (Op × List ℕ) × List ℕ) × ℕ) =>
      (shiftCode (n a) (((codes a).take q.2).flatMap Prod.fst).length q.1).1)
    hblocks hshift.fst'
  have houtputs := flatMapWithInput (encB := encNat)
    (f := fun a (q : (List (Op × List ℕ) × List ℕ) × ℕ) =>
      (shiftCode (n a) (((codes a).take q.2).flatMap Prod.fst).length q.1).2)
    hblocks hshift.snd'
  have h := hgates.prod houtputs
  change ComputableInPolyTime (fun a => appendCodesDirect (n a) (codes a)) enc (encCode encOp) at h
  simpa only [appendCodesDirect_eq_appendCodes] using h

/-- Bundling raw blocks is polynomial-time in their encodings and binary layout parameters. -/
@[fun_prop]
theorem computableInPolyTime_bundleCode {n blockSize : α → ℕ}
    {codes : α → List (List (Op × List ℕ) × List ℕ)}
    (hn : ComputableInPolyTime n enc encNat)
    (hblock : ComputableInPolyTime blockSize enc encNat)
    (hcodes : ComputableInPolyTime codes enc (encList (encCode encOp))) :
    ComputableInPolyTime (fun a => bundleCode (n a) (blockSize a) (codes a))
      enc (encCode encOp) := by
  fun_prop [bundleCode]

/-- Resolve a composed wire in polynomial time, including binary output lookup and offsets. -/
@[fun_prop]
theorem computableInPolyTime_compCodeWire {n i : α → ℕ}
    {c : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hc : ComputableInPolyTime c enc (encCode encOp))
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun a => compCodeWire (n a) (c a) (i a)) enc encNat := by
  have houtputs : ComputableInPolyTime (fun a => (c a).2.length) enc encNat :=
    (length_list_binary encNat).comp hc.snd'
  have hgates : ComputableInPolyTime (fun a => (c a).1.length) enc encNat :=
    (length_list_binary (encGate encOp)).comp hc.fst'
  have hlookup : ComputableInPolyTime (fun a => (c a).2.getD (i a) 0) enc encNat :=
    listGetD_binary 0 hc.snd' hi
  unfold compCodeWire
  fun_prop

/-- Construct sequential circuit codes in polynomial time. All wire indices and input counts
are binary; list lengths, input lookup, gate relocation and the whole output code are charged. -/
@[fun_prop]
theorem computableInPolyTime_compCode {n : α → ℕ}
    {d c : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hd : ComputableInPolyTime d enc (encCode encOp))
    (hc : ComputableInPolyTime c enc (encCode encOp)) :
    ComputableInPolyTime (fun a => compCode (n a) (d a) (c a)) enc (encCode encOp) := by
  fun_prop [compCode]

/-- Numbering a replicated wire is polynomial-time with all quantities in binary. -/
@[fun_prop]
theorem computableInPolyTime_replicateWire {n s k t i : α → ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hs : ComputableInPolyTime s enc encNat)
    (hk : ComputableInPolyTime k enc encNat)
    (ht : ComputableInPolyTime t enc encNat)
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun a => replicateWire (n a) (s a) (k a) (t a) (i a)) enc encNat := by
  unfold replicateWire
  fun_prop

/-- Replicating a raw code is polynomial-time, with a binary input count and a unary number of
copies. -/
@[fun_prop]
theorem computableInPolyTime_replicateCode {n k : α → ℕ}
    {code : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hk : ComputableInPolyTime k enc encUnary)
    (hcode : ComputableInPolyTime code enc (encCode encOp)) :
    ComputableInPolyTime (fun a => replicateCode (n a) (k a) (code a)) enc (encCode encOp) := by
  fun_prop [replicateCode]

/-- A fixed formula's instantiated code is polynomial-time in the target input count and
selected binary wire numbers, over any signature `σ`. -/
theorem computableInPolyTime_formulaCode {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {n : α → ℕ} {m : ℕ} (F : Formula σ m) {wires : α → Fin m → ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hwires : ∀ i, ComputableInPolyTime (fun a => wires a i) enc encNat) :
    ComputableInPolyTime (fun a => formulaCode (n a) F (wires a)) enc (encCode encOp) := by
  induction F with
  | input i => exact (const []).prod ((hwires i).cons' (const []))
  | gate op args ih =>
    exact computableInPolyTime_compCode hn
      (const (oneGate (σ := σ) op _root_.id).code)
      (computableInPolyTime_appendCodes hn (ofFn (fun i => ih i)))

end PolyTimeRaw

/-! ### Balanced raw code tree -/

section Balanced

private def intervalRow {Op : Type*} (n : ℕ) (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ))
    (rows : List (List (List (Op × List ℕ) × List ℕ))) :
    List (List (Op × List ℕ) × List ℕ) :=
  (List.range (leaves.length + 1)).map fun start =>
    if rows.length = 1 then leaves.getD start unit
    else if start + rows.length ≤ leaves.length then
      compCode n op (appendCode n
        ((rows.getD (rows.length / 2) []).getD start unit)
        ((rows.getD (rows.length - rows.length / 2) []).getD
          (start + rows.length / 2) unit))
    else unit

private def intervalTables {Op : Type*} (n : ℕ) (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) (count : ℕ) :
    List (List (List (Op × List ℕ) × List ℕ)) :=
  (fun rows => rows ++ [intervalRow n op unit leaves rows])^[count]
    [List.replicate (leaves.length + 1) unit]

/-- Generate the exact half-split code on shared inputs. The supplied fallback is returned only
for an empty leaf list. Malformed codes are transformed as data, without arity-sized loops. -/
@[expose] def balancedCode {Op : Type*} (n : ℕ) (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) : List (Op × List ℕ) × List ℕ :=
  private_decl% ((intervalTables n op unit leaves leaves.length).getD leaves.length []).getD 0 unit

private theorem length_intervalTables {Op : Type*} (n : ℕ)
    (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) (count : ℕ) :
    (intervalTables n op unit leaves count).length = count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [intervalTables, Function.iterate_succ_apply', List.length_append,
      List.length_cons, List.length_nil]
    simpa only [intervalTables] using congrArg (· + 1) ih

private def referenceCode {Op : Type*} (n : ℕ) (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) : List (Op × List ℕ) × List ℕ :=
  leaves.balancedFold (fun c d => compCode n op (appendCode n c d)) unit _root_.id

private def codeMass {Op : Type*} (c : List (Op × List ℕ) × List ℕ) : ℕ :=
  (c.1.map fun gate => gate.2.length + 1).sum + c.2.length

private def OpBitsLe {Op : Type} (encOp : Op ↪ List Bool)
    (c : List (Op × List ℕ) × List ℕ) (bound : ℕ) : Prop :=
  ∀ gate ∈ c.1, (encOp gate.1).length ≤ bound

private def WireBitsLe {Op : Type*} (c : List (Op × List ℕ) × List ℕ) (bound : ℕ) : Prop :=
  (∀ gate ∈ c.1, ∀ wire ∈ gate.2, (encNat wire).length ≤ bound) ∧
    ∀ wire ∈ c.2, (encNat wire).length ≤ bound

private theorem codeMass_le_encoding {Op : Type} (encOp : Op ↪ List Bool)
    (c : List (Op × List ℕ) × List ℕ) : codeMass c ≤ (encCode encOp c).length := by
  have hg : (c.1.map fun gate => gate.2.length + 1).sum ≤
      (encList (encGate encOp) c.1).length := by
    rw [length_encList]
    apply List.sum_le_sum
    intro gate _
    have := length_le_length_encList encNat gate.2
    enc_len [encGate]
  have ho := length_le_length_encList encNat c.2
  enc_len [codeMass, encCode, encGate] at hg ⊢

private theorem opBitsLe_encoding {Op : Type} (encOp : Op ↪ List Bool)
    (c : List (Op × List ℕ) × List ℕ) : OpBitsLe encOp c (encCode encOp c).length := by
  intro gate hg
  have hb := length_le_encList_of_mem (encGate encOp) hg
  rw [show (encGate encOp gate).length =
    2 * (encOp gate.1).length + 1 + (encList encNat gate.2).length from length_encPair gate] at hb
  rw [show (encCode encOp c).length =
    2 * (encList (encGate encOp) c.1).length + 1 + (encList encNat c.2).length
      from length_encPair c]
  omega

private theorem wireBitsLe_encoding {Op : Type} (encOp : Op ↪ List Bool)
    (c : List (Op × List ℕ) × List ℕ) : WireBitsLe c (encCode encOp c).length := by
  constructor
  · intro gate hg wire hw
    have ha := length_le_encList_of_mem encNat hw
    have hb := length_le_encList_of_mem (encGate encOp) hg
    rw [show (encGate encOp gate).length =
      2 * (encOp gate.1).length + 1 + (encList encNat gate.2).length from length_encPair gate] at hb
    rw [show (encCode encOp c).length =
      2 * (encList (encGate encOp) c.1).length + 1 + (encList encNat c.2).length
        from length_encPair c]
    omega
  · intro wire hw
    have := length_le_encList_of_mem encNat hw
    enc_len [encCode]

private theorem codeMass_append {Op : Type*} (n : ℕ) (c d : List (Op × List ℕ) × List ℕ) :
    codeMass (appendCode n c d) = codeMass c + codeMass d := by
  simp [codeMass, appendCode, List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm]

private theorem codeMass_comp_le {Op : Type*} (n : ℕ) (d c : List (Op × List ℕ) × List ℕ) :
    codeMass (compCode n d c) ≤ codeMass c + codeMass d := by
  simp only [codeMass, compCode, List.map_append, List.map_map, Function.comp_def,
    List.length_map, List.sum_append]
  omega

private theorem gates_le_codeMass {Op : Type*} (c : List (Op × List ℕ) × List ℕ) :
    c.1.length ≤ codeMass c := by
  have h : c.1.length ≤ (c.1.map fun gate => gate.2.length + 1).sum := by
    induction c.1 with
    | nil => simp
    | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  exact h.trans (Nat.le_add_right _ _)

private theorem opBitsLe_mono {Op : Type} {encOp : Op ↪ List Bool}
    {c : List (Op × List ℕ) × List ℕ} {a b : ℕ} (h : OpBitsLe encOp c a) (hab : a ≤ b) :
    OpBitsLe encOp c b :=
  fun g hg => (h g hg).trans hab

private theorem opBitsLe_append {Op : Type} {encOp : Op ↪ List Bool} (n : ℕ)
    {c d : List (Op × List ℕ) × List ℕ} {B : ℕ}
    (hc : OpBitsLe encOp c B) (hd : OpBitsLe encOp d B) :
    OpBitsLe encOp (appendCode n c d) B := by
  intro gate hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hc gate hg
  · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
    exact hd g hmem

private theorem opBitsLe_comp {Op : Type} {encOp : Op ↪ List Bool} (n : ℕ)
    {d c : List (Op × List ℕ) × List ℕ} {B : ℕ}
    (hc : OpBitsLe encOp c B) (hd : OpBitsLe encOp d B) :
    OpBitsLe encOp (compCode n d c) B := by
  intro gate hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hc gate hg
  · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
    exact hd g hmem

private theorem wireBitsLe_mono {Op : Type*} {c : List (Op × List ℕ) × List ℕ} {a b : ℕ}
    (h : WireBitsLe c a) (hab : a ≤ b) : WireBitsLe c b :=
  ⟨fun g hg i hi => (h.1 g hg i hi).trans hab, fun i hi => (h.2 i hi).trans hab⟩

private theorem shiftCodeWire_bits (n offset wire bound : ℕ)
    (h : (encNat wire).length ≤ bound) :
    (encNat (shiftCodeWire n offset wire)).length ≤ bound + offset := by
  unfold shiftCodeWire
  split
  · omega
  · induction offset with
    | zero => simpa using h
    | succ k ih =>
      have hsize : (wire + k + 1).size ≤ (wire + k).size + 1 := by
        refine Nat.size_le.mpr ?_
        rw [pow_succ]
        have := Nat.lt_size_self (wire + k)
        have := Nat.one_le_two_pow (n := (wire + k).size)
        omega
      rw [← Nat.add_assoc, length_encNat_eq_size]
      rw [length_encNat_eq_size] at ih
      omega

private theorem wireBitsLe_append {Op : Type*} (n : ℕ)
    {c d : List (Op × List ℕ) × List ℕ} {a b : ℕ}
    (hc : WireBitsLe c a) (hd : WireBitsLe d b) :
    WireBitsLe (appendCode n c d) (a + b + codeMass c) := by
  constructor
  · intro gate hg wire hw
    rcases List.mem_append.mp hg with hg | hg
    · exact (hc.1 gate hg wire hw).trans (by omega)
    · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact (shiftCodeWire_bits n _ i b (hd.1 g hmem i hi)).trans
        (by have := gates_le_codeMass c; omega)
  · intro wire hw
    rcases List.mem_append.mp hw with hw | hw
    · exact (hc.2 wire hw).trans (by omega)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact (shiftCodeWire_bits n _ i b (hd.2 i hi)).trans
        (by have := gates_le_codeMass c; omega)

private theorem compCodeWire_bits {Op : Type*} (n : ℕ)
    {c : List (Op × List ℕ) × List ℕ} {wire a b : ℕ}
    (hc : WireBitsLe c a) (hi : (encNat wire).length ≤ b) :
    (encNat (compCodeWire n c wire)).length ≤
      a + b + (encNat n).length + codeMass c + 2 := by
  unfold compCodeWire
  split
  · rename_i h
    rw [List.getD_eq_getElem _ _ h]
    exact (hc.2 _ (List.getElem_mem h)).trans (by omega)
  · have hsub : (encNat (wire - c.2.length)).length ≤ b := by
      refine (?_ : (encNat (wire - c.2.length)).length ≤ (encNat wire).length).trans hi
      simpa only [length_encNat_eq_size] using Nat.size_le_size (Nat.sub_le wire c.2.length)
    have hgate := (length_encNat_le_self c.1.length).trans (gates_le_codeMass c)
    have hsum := length_encNat_add_le_add n c.1.length
    have htotal := length_encNat_add_le_add (n + c.1.length) (wire - c.2.length)
    omega

private theorem wireBitsLe_comp {Op : Type*} (n : ℕ)
    {d c : List (Op × List ℕ) × List ℕ} {a b : ℕ}
    (hc : WireBitsLe c a) (hd : WireBitsLe d b) :
    WireBitsLe (compCode n d c) (a + b + (encNat n).length + codeMass c + 2) := by
  constructor
  · intro gate hg wire hw
    rcases List.mem_append.mp hg with hg | hg
    · exact (hc.1 gate hg wire hw).trans (by omega)
    · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact compCodeWire_bits n hc (hd.1 g hmem i hi)
  · intro wire hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact compCodeWire_bits n hc (hd.2 i hi)

private theorem referenceCode_bounds {Op : Type} {encOp : Op ↪ List Bool}
    (n : ℕ) (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) (k B : ℕ)
    (hopTag : OpBitsLe encOp op B) (hop : codeMass op ≤ B) (hopBits : WireBitsLe op B)
    (hk : leaves.length ≤ k)
    (hcodes : ∀ c ∈ leaves, OpBitsLe encOp c B ∧ codeMass c ≤ B ∧ WireBitsLe c B)
    (hne : leaves ≠ []) :
    OpBitsLe encOp (referenceCode n op unit leaves) B ∧
      codeMass (referenceCode n op unit leaves) ≤ (2 * leaves.length - 1) * B ∧
      WireBitsLe (referenceCode n op unit leaves)
        ((2 * leaves.length - 1) * (B + (encNat n).length + 3 * ((2 * k + 1) * B) + 2)) := by
  let M := (2 * k + 1) * B
  let D := B + (encNat n).length + 3 * M + 2
  change OpBitsLe encOp (leaves.balancedFold _ unit _root_.id) B ∧
    codeMass (leaves.balancedFold _ unit _root_.id) ≤ _ ∧
    WireBitsLe (leaves.balancedFold _ unit _root_.id) ((2 * leaves.length - 1) * D)
  refine List.balancedFold_induction
    (p := fun l c => l.length ≤ k →
      (∀ a ∈ l, OpBitsLe encOp a B ∧ codeMass a ≤ B ∧ WireBitsLe a B) → l ≠ [] →
      OpBitsLe encOp c B ∧ codeMass c ≤ (2 * l.length - 1) * B ∧
        WireBitsLe c ((2 * l.length - 1) * D))
    (fun _ _ h => (h rfl).elim) ?_ ?_ leaves hk hcodes hne
  · intro c _ hc _
    obtain ⟨ht, hm, hw⟩ := hc c (by simp)
    simpa only [List.length_singleton, Nat.reduceMul, Nat.reduceSub, one_mul] using
      ⟨ht, hm, wireBitsLe_mono hw (by dsimp [D]; omega)⟩
  · intro left right c d hleft hright ihleft ihright hlength hc _
    have hlpos := List.length_pos_iff.mpr hleft
    have hrpos := List.length_pos_iff.mpr hright
    have hll : left.length ≤ k := by simp only [List.length_append] at hlength; omega
    have hrl : right.length ≤ k := by simp only [List.length_append] at hlength; omega
    obtain ⟨htl, hml, hwl⟩ := ihleft hll (fun a ha => hc a (List.mem_append_left _ ha)) hleft
    obtain ⟨htr, hmr, hwr⟩ := ihright hrl (fun a ha => hc a (List.mem_append_right _ ha)) hright
    have hcm : codeMass c ≤ M := hml.trans (Nat.mul_le_mul_right B (by omega))
    have hdm : codeMass d ≤ M := hmr.trans (Nat.mul_le_mul_right B (by omega))
    have hcoeff : 2 * (left ++ right).length - 1 =
        (2 * left.length - 1) + (2 * right.length - 1) + 1 := by
      simp only [List.length_append]
      omega
    refine ⟨opBitsLe_comp n (opBitsLe_append n htl htr) hopTag, ?_, ?_⟩
    · have h := codeMass_comp_le n op (appendCode n c d)
      rw [codeMass_append] at h
      rw [hcoeff]
      nlinarith [hml, hmr]
    · apply wireBitsLe_mono (wireBitsLe_comp n (wireBitsLe_append n hwl hwr) hopBits)
      rw [codeMass_append, hcoeff]
      dsimp only [D]
      nlinarith

private theorem le_sum_map_of_mem {α : Type*} (f : α → ℕ) {a : α} {l : List α}
    (ha : a ∈ l) : f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | h
    · omega
    · have := ih h; omega

private theorem length_encoding_of_bounds {Op : Type} {encOp : Op ↪ List Bool}
    {c : List (Op × List ℕ) × List ℕ} {B M W : ℕ}
    (ht : OpBitsLe encOp c B) (hm : codeMass c ≤ M) (hw : WireBitsLe c W) :
    (encCode encOp c).length ≤
      2 * M * (4 * B + 3 + 2 * M * (2 * W + 1)) + 1 + M * (2 * W + 1) := by
  have hgate (g : Op × List ℕ) (hg : g ∈ c.1) :
      (encGate encOp g).length ≤ 2 * B + 1 + M * (2 * W + 1) := by
    have htag := ht g hg
    have hargs : g.2.length ≤ M := by
      have h := le_sum_map_of_mem (fun g : Op × List ℕ => g.2.length + 1) hg
      dsimp only [codeMass] at hm
      omega
    have hwords := length_encList_le encNat g.2 (hw.1 g hg)
    have hb := hwords.trans (Nat.mul_le_mul_right (2 * W + 1) hargs)
    rw [show (encGate encOp g).length =
      2 * (encOp g.1).length + 1 + (encList encNat g.2).length from length_encPair g]
    omega
  have hgates := length_encList_le (encGate encOp) c.1 hgate
  have hgc := (gates_le_codeMass c).trans hm
  have hgates' := hgates.trans
    (Nat.mul_le_mul_right (2 * (2 * B + 1 + M * (2 * W + 1)) + 1) hgc)
  have hout := length_encList_le encNat c.2 hw.2
  have hoc : c.2.length ≤ M := by dsimp only [codeMass] at hm; omega
  have hout' := hout.trans (Nat.mul_le_mul_right (2 * W + 1) hoc)
  rw [show (encCode encOp c).length =
    2 * (encList (encGate encOp) c.1).length + 1 + (encList encNat c.2).length
      from length_encPair c]
  nlinarith

private theorem computedGetD {α β : Type} {encIn : α ↪ List Bool} {enc : β ↪ List Bool}
    {values : α → List β} {index : α → ℕ} {fallback : α → β}
    (hv : ComputableInPolyTime values encIn (encList enc))
    (hi : ComputableInPolyTime index encIn encUnary)
    (hf : ComputableInPolyTime fallback encIn enc) :
    ComputableInPolyTime (fun a => (values a).getD (index a) (fallback a)) encIn enc := by
  have hhead := (head? enc).comp ((dropUnary (encA := enc)).comp (hv.prod hi))
  simpa only [Function.comp_def, List.head?_drop, List.getD_eq_getElem?_getD] using
    optionGetDWithInput hhead hf

private theorem computable_intervalRow {Op α : Type} {encOp : Op ↪ List Bool}
    {enc : α ↪ List Bool} {n : α → ℕ}
    {op unit : α → List (Op × List ℕ) × List ℕ}
    {leaves : α → List (List (Op × List ℕ) × List ℕ)}
    {rows : α → List (List (List (Op × List ℕ) × List ℕ))}
    (hn : ComputableInPolyTime n enc encNat)
    (hop : ComputableInPolyTime op enc (encCode encOp))
    (hu : ComputableInPolyTime unit enc (encCode encOp))
    (hl : ComputableInPolyTime leaves enc (encList (encCode encOp)))
    (hr : ComputableInPolyTime rows enc (encList (encList (encCode encOp)))) :
    ComputableInPolyTime (fun a => intervalRow (n a) (op a) (unit a) (leaves a) (rows a))
      enc (encList (encCode encOp)) := by
  have hlen := (length_list (encList (encCode encOp))).comp hr
  have hhalf := (unary_div_const 2).comp hlen
  have hrest : ComputableInPolyTime (fun a => (rows a).length - (rows a).length / 2)
      enc encUnary := by fun_prop
  have hleft := (listGetD (encA := encList (encCode encOp)) []).comp (hr.prod hhalf)
  have hright := (listGetD (encA := encList (encCode encOp)) []).comp (hr.prod hrest)
  have hbody : ComputableInPolyTime
      (fun p : α × ℕ =>
        if (rows p.1).length = 1 then (leaves p.1).getD p.2 (unit p.1)
        else if p.2 + (rows p.1).length ≤ (leaves p.1).length then
          compCode (n p.1) (op p.1) (appendCode (n p.1)
            (((rows p.1).getD ((rows p.1).length / 2) []).getD p.2 (unit p.1))
            (((rows p.1).getD ((rows p.1).length - (rows p.1).length / 2) []).getD
              (p.2 + (rows p.1).length / 2) (unit p.1)))
        else unit p.1) (encPair enc encUnary) (encCode encOp) := by
    have hfst := fst enc encUnary
    have hs := snd enc encUnary
    have hleaf := computedGetD (hl.comp hfst) hs (hu.comp hfst)
    have hlc := computedGetD (hleft.comp hfst) hs (hu.comp hfst)
    have hrc := computedGetD (hright.comp hfst)
      (show ComputableInPolyTime
        (fun p : α × ℕ => p.2 + (rows p.1).length / 2) (encPair enc encUnary) encUnary from
          by fun_prop) (hu.comp hfst)
    fun_prop
  have hrange : ComputableInPolyTime (fun a => List.range ((leaves a).length + 1))
      enc (encList encUnary) := by fun_prop
  exact mapWithInput hrange hbody

private theorem intervalRow_getD {Op : Type*} (n : ℕ)
    (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ))
    (rows : List (List (List (Op × List ℕ) × List ℕ))) (start : ℕ)
    (hs : start ≤ leaves.length) :
    (intervalRow n op unit leaves rows).getD start unit =
      if rows.length = 1 then leaves.getD start unit
      else if start + rows.length ≤ leaves.length then
        compCode n op (appendCode n
          ((rows.getD (rows.length / 2) []).getD start unit)
          ((rows.getD (rows.length - rows.length / 2) []).getD
            (start + rows.length / 2) unit))
      else unit := by
  rw [List.getD_eq_getElem _ _ (by simp [intervalRow]; omega)]
  simp [intervalRow]

private theorem intervalTables_getD {Op : Type*} (n : ℕ)
    (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ))
    (count len start : ℕ) (hl : len ≤ count) (hs : start + len ≤ leaves.length) :
    ((intervalTables n op unit leaves count).getD len []).getD start unit =
      referenceCode n op unit ((leaves.drop start).take len) := by
  induction count generalizing len start with
  | zero =>
    have : len = 0 := by omega
    subst len
    simp [intervalTables, referenceCode]
  | succ count ih =>
    rw [intervalTables, Function.iterate_succ_apply']
    change (((intervalTables n op unit leaves count) ++
      [intervalRow n op unit leaves (intervalTables n op unit leaves count)]).getD len []).getD
        start unit = _
    by_cases hlt : len ≤ count
    · rw [List.getD_append _ _ _ _ (by rw [length_intervalTables]; omega)]
      exact ih _ _ hlt hs
    · have heq : len = count + 1 := by omega
      subst len
      rw [← length_intervalTables n op unit leaves count, List.getD_append_cons_length,
        intervalRow_getD n op unit leaves _ start (by omega), length_intervalTables]
      by_cases hc : count = 0
      · subst count
        rw [ite_eq_left rfl]
        rw [List.take_one_drop_eq_of_lt_length (by omega)]
        rw [List.getD_eq_getElem _ _ (by omega : start < leaves.length)]
        simp [referenceCode]
      · rw [ite_eq_right (by omega), ite_eq_left hs]
        have hh : (count + 1) / 2 ≤ count := by omega
        have hr : count + 1 - (count + 1) / 2 ≤ count := by omega
        rw [ih _ _ hh (by omega), ih _ _ hr (by omega)]
        have hlength : ((leaves.drop start).take (count + 1)).length = count + 1 := by
          simp only [List.length_take, List.length_drop]
          omega
        conv_rhs =>
          unfold referenceCode
          rw [List.balancedFold_of_two_le (by rw [hlength]; omega), hlength]
        simp only [List.take_take, List.drop_take, List.drop_drop, referenceCode,
          Nat.min_eq_left (by omega : (count + 1) / 2 ≤ count + 1)]

private theorem intervalTables_getD_invalid {Op : Type*} (n : ℕ)
    (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ))
    (count len start : ℕ) (hl : len ≤ count) (hs : start ≤ leaves.length)
    (hinvalid : leaves.length < start + len) :
    ((intervalTables n op unit leaves count).getD len []).getD start unit = unit := by
  induction count generalizing len start with
  | zero => omega
  | succ count ih =>
    rw [intervalTables, Function.iterate_succ_apply']
    change (((intervalTables n op unit leaves count) ++
      [intervalRow n op unit leaves (intervalTables n op unit leaves count)]).getD len []).getD
        start unit = _
    by_cases hlt : len ≤ count
    · rw [List.getD_append _ _ _ _ (by rw [length_intervalTables]; omega)]
      exact ih _ _ hlt hs hinvalid
    · have heq : len = count + 1 := by omega
      subst len
      rw [← length_intervalTables n op unit leaves count, List.getD_append_cons_length,
        intervalRow_getD n op unit leaves _ start hs, length_intervalTables]
      split
      · exact List.getD_eq_default _ _ (by omega)
      · rw [ite_eq_right (by omega)]

private theorem intervalTables_row_length {Op : Type*} (n : ℕ)
    (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) (count : ℕ)
    (row : List (List (Op × List ℕ) × List ℕ))
    (hr : row ∈ intervalTables n op unit leaves count) :
    row.length = leaves.length + 1 := by
  induction count with
  | zero =>
    have heq : row = List.replicate (leaves.length + 1) unit := by
      simpa [intervalTables] using hr
    simp [heq]
  | succ count ih =>
    change row ∈ (fun rows => rows ++ [intervalRow n op unit leaves rows])^[count + 1]
      [List.replicate (leaves.length + 1) unit] at hr
    rw [Function.iterate_succ_apply'] at hr
    rcases List.mem_append.mp hr with h | h
    · exact ih h
    · have heq : row = intervalRow n op unit leaves (intervalTables n op unit leaves count) :=
        List.mem_singleton.mp h
      rw [heq]
      simp [intervalRow]

private def inputBudget {Op : Type} (encOp : Op ↪ List Bool)
    (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) : ℕ :=
  (encCode encOp op).length + (encCode encOp unit).length +
    (encList (encCode encOp) leaves).length + 1

private def entryBound {Op : Type} (encOp : Op ↪ List Bool) (n : ℕ)
    (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) : ℕ :=
  let B := inputBudget encOp op unit leaves
  let M := (2 * leaves.length + 1) * B
  let W := (2 * leaves.length + 1) * (B + (encNat n).length + 3 * M + 2)
  2 * M * (4 * B + 3 + 2 * M * (2 * W + 1)) + 1 + M * (2 * W + 1)

private def tableBound {Op : Type} (encOp : Op ↪ List Bool) (n : ℕ)
    (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) : ℕ :=
  (leaves.length + 1) *
    (2 * ((leaves.length + 1) * (2 * entryBound encOp n op unit leaves + 1)) + 1)

private theorem intervalTables_entry_bound {Op : Type} (encOp : Op ↪ List Bool) (n : ℕ)
    (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) (count : ℕ)
    {row : List (List (Op × List ℕ) × List ℕ)} {code : List (Op × List ℕ) × List ℕ}
    (hr : row ∈ intervalTables n op unit leaves count) (hc : code ∈ row) :
    (encCode encOp code).length ≤ entryBound encOp n op unit leaves := by
  let B := inputBudget encOp op unit leaves
  let M := (2 * leaves.length + 1) * B
  let D := B + (encNat n).length + 3 * M + 2
  have hunit : OpBitsLe encOp unit B ∧ codeMass unit ≤ B ∧ WireBitsLe unit B :=
    ⟨opBitsLe_mono (opBitsLe_encoding encOp unit) (by dsimp [B, inputBudget]; omega),
      (codeMass_le_encoding encOp unit).trans (by dsimp [B, inputBudget]; omega),
      wireBitsLe_mono (wireBitsLe_encoding encOp unit) (by dsimp [B, inputBudget]; omega)⟩
  have hop : OpBitsLe encOp op B ∧ codeMass op ≤ B ∧ WireBitsLe op B :=
    ⟨opBitsLe_mono (opBitsLe_encoding encOp op) (by dsimp [B, inputBudget]; omega),
      (codeMass_le_encoding encOp op).trans (by dsimp [B, inputBudget]; omega),
      wireBitsLe_mono (wireBitsLe_encoding encOp op) (by dsimp [B, inputBudget]; omega)⟩
  have hleaves : ∀ c ∈ leaves, OpBitsLe encOp c B ∧ codeMass c ≤ B ∧ WireBitsLe c B := by
    intro c h
    have hc := length_le_encList_of_mem (encCode encOp) h
    have hB : (encCode encOp c).length ≤ B := by dsimp only [B, inputBudget]; omega
    exact ⟨opBitsLe_mono (opBitsLe_encoding encOp c) hB,
      (codeMass_le_encoding encOp c).trans hB,
      wireBitsLe_mono (wireBitsLe_encoding encOp c) hB⟩
  have hBM : B ≤ M := by dsimp [M]; nlinarith
  have hBW : B ≤ (2 * leaves.length + 1) * D := by dsimp [D]; nlinarith
  suffices OpBitsLe encOp code B ∧ codeMass code ≤ M ∧
      WireBitsLe code ((2 * leaves.length + 1) * D) by
    exact length_encoding_of_bounds this.1 this.2.1 this.2.2
  obtain ⟨len, hlen, rfl⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨start, hstart, rfl⟩ := List.mem_iff_getElem.mp hc
  have hlen' : len ≤ count := by rw [length_intervalTables] at hlen; omega
  have hrowlen := intervalTables_row_length n op unit leaves count _
    (List.getElem_mem hlen)
  have hstart' : start ≤ leaves.length := by omega
  rw [← List.getD_eq_getElem _ unit hstart, ← List.getD_eq_getElem _ [] hlen]
  by_cases hvalid : start + len ≤ leaves.length
  · rw [intervalTables_getD _ _ _ _ _ _ _ hlen' hvalid]
    by_cases he : (leaves.drop start).take len = []
    · rw [he]
      simpa only [referenceCode, List.balancedFold_nil] using
        ⟨hunit.1, hunit.2.1.trans hBM, wireBitsLe_mono hunit.2.2 hBW⟩
    · have hlength : ((leaves.drop start).take len).length ≤ leaves.length := by grind
      obtain ⟨hbt, hbm, hbw⟩ := referenceCode_bounds n op unit _ leaves.length B
        hop.1 hop.2.1 hop.2.2 hlength
        (fun c hc => hleaves c (List.mem_of_mem_drop (List.mem_of_mem_take hc))) he
      exact ⟨hbt, hbm.trans (Nat.mul_le_mul_right B (by omega)),
        wireBitsLe_mono hbw (Nat.mul_le_mul_right D (by omega))⟩
  · rw [intervalTables_getD_invalid _ _ _ _ _ _ _ hlen' hstart' (by omega)]
    exact ⟨hunit.1, hunit.2.1.trans hBM, wireBitsLe_mono hunit.2.2 hBW⟩

private theorem intervalTables_bound {Op : Type} (encOp : Op ↪ List Bool) (n : ℕ)
    (op unit : List (Op × List ℕ) × List ℕ)
    (leaves : List (List (Op × List ℕ) × List ℕ)) (count : ℕ)
    (hcount : count ≤ leaves.length) :
    (encList (encList (encCode encOp)) (intervalTables n op unit leaves count)).length ≤
      tableBound encOp n op unit leaves := by
  have hrows (row : List (List (Op × List ℕ) × List ℕ))
      (hr : row ∈ intervalTables n op unit leaves count) :
      (encList (encCode encOp) row).length ≤
        (leaves.length + 1) * (2 * entryBound encOp n op unit leaves + 1) := by
    have h := length_encList_le (encCode encOp) row
      (fun c hc => intervalTables_entry_bound encOp n op unit leaves count hr hc)
    rwa [intervalTables_row_length n op unit leaves count row hr] at h
  have h := length_encList_le (encList (encCode encOp)) _ hrows
  rw [length_intervalTables] at h
  exact h.trans (Nat.mul_le_mul_right _ (by omega))

private theorem referenceCode_map {σ : Signature} {n r : ℕ} (op : Circuit σ (r + r) r)
    (unit : Circuit σ n r) (leaves : List (Circuit σ n r)) :
    referenceCode n op.code unit.code (leaves.map Circuit.code) =
      (Circuit.balanced op unit leaves).code := by
  induction leaves using List.balancedFold.induct with
  | case1 => simp [referenceCode, Circuit.balanced]
  | case2 c => simp [referenceCode, Circuit.balanced]
  | case3 a b leaves ih₁ ih₂ =>
    have hm : 2 ≤ ((a :: b :: leaves).map Circuit.code).length := by simp
    rw [referenceCode, List.balancedFold_of_two_le hm, List.length_map,
      ← List.map_take, ← List.map_drop]
    change compCode n op.code (appendCode n
      (referenceCode n op.code unit.code _)
      (referenceCode n op.code unit.code _)) = _
    rw [ih₁, ih₂, ← code_append, ← code_comp]
    congr 1
    simp only [Circuit.balanced]
    exact (List.balancedFold_of_two_le
      (op := fun C D : Circuit σ n r => op.comp (C.append D))
      (e := unit) (f := _root_.id) (by simp : 2 ≤ (a :: b :: leaves).length)).symm

/-- The serialized code of `Circuit.balanced op unit leaves` is `balancedCode` of their codes,
including empty fallback programs, unused operators, dead gates and intermediate gate order. -/
theorem code_balanced {σ : Signature} {n r : ℕ} (op : Circuit σ (r + r) r)
    (unit : Circuit σ n r) (leaves : List (Circuit σ n r)) :
    (Circuit.balanced op unit leaves).code =
      balancedCode n op.code unit.code (leaves.map Circuit.code) := by
  symm
  change ((intervalTables n op.code unit.code (leaves.map Circuit.code)
    (leaves.map Circuit.code).length).getD (leaves.map Circuit.code).length []).getD 0 unit.code = _
  rw [intervalTables_getD _ _ _ _ _ _ _ le_rfl (by omega)]
  simp only [List.drop_zero, List.take_length]
  exact referenceCode_map op unit leaves

/-- Uniform native generation from the binary shared-input count and the complete operator,
fallback and leaf codes, over any operation encoding `encOp : Op ↪ List Bool`. -/
@[fun_prop]
theorem computableInPolyTime_balancedCode {Op α : Type} {encOp : Op ↪ List Bool}
    {enc : α ↪ List Bool} {n : α → ℕ}
    {op unit : α → List (Op × List ℕ) × List ℕ}
    {leaves : α → List (List (Op × List ℕ) × List ℕ)}
    (hn : ComputableInPolyTime n enc encNat)
    (hop : ComputableInPolyTime op enc (encCode encOp))
    (hu : ComputableInPolyTime unit enc (encCode encOp))
    (hl : ComputableInPolyTime leaves enc (encList (encCode encOp))) :
    ComputableInPolyTime (fun a => balancedCode (n a) (op a) (unit a) (leaves a))
      enc (encCode encOp) := by
  let rowsEnc := encList (encList (encCode encOp))
  let init (a : α) := [List.replicate ((leaves a).length + 1) (unit a)]
  let step (a : α) (rows : List (List (List (Op × List ℕ) × List ℕ))) :=
    rows ++ [intervalRow (n a) (op a) (unit a) (leaves a) rows]
  have hcount := (length_list (encCode encOp)).comp hl
  have hi : ComputableInPolyTime init enc rowsEnc := by
    dsimp only [init, rowsEnc]
    fun_prop
  have hs : ComputableInPolyTime
      (fun p : α × List (List (List (Op × List ℕ) × List ℕ)) => step p.1 p.2)
      (encPair enc rowsEnc) rowsEnc := by
    have hf := fst enc rowsEnc
    have hr := snd enc rowsEnc
    have hrow := computable_intervalRow (hn.comp hf) (hop.comp hf) (hu.comp hf) (hl.comp hf) hr
    dsimp only [step, rowsEnc]
    fun_prop
  have hb : PolyBounded (fun a => (enc a).length)
      (fun a => tableBound encOp (n a) (op a) (unit a) (leaves a)) := by
    growth_poly
  have ht := iterateWith (par := _root_.id) (count := fun a => (leaves a).length)
    (init := init) (step := step) id' hcount hi hs hb (fun a count hcount =>
      intervalTables_bound encOp (n a) (op a) (unit a) (leaves a) count hcount)
  have hrow := (listGetD (encA := encList (encCode encOp)) []).comp (ht.prod hcount)
  change ComputableInPolyTime (fun a =>
    ((intervalTables (n a) (op a) (unit a) (leaves a) (leaves a).length).getD
      (leaves a).length []).getD 0 (unit a)) enc (encCode encOp)
  exact computedGetD hrow (const 0) hu

end Balanced

/-! ### Typed `@[fun_prop]` `(·.code)` rules -/

section TypedFunProp

/-- An input `a : α` paired with a bounded index `i : Fin (k a)`: `a` is framed under `enc`
followed by `i.val` in unary (`encUnary`). -/
@[expose] def encWithFinUnary {α : Type} (enc : α ↪ List Bool) (k : α → ℕ) :
    (Σ a : α, Fin (k a)) ↪ List Bool :=
  ⟨fun q => encPair enc encUnary (q.1, q.2.val), by
    rintro ⟨a, i⟩ ⟨a', i'⟩ h
    obtain ⟨ha, hi⟩ := Prod.ext_iff.1 ((encPair enc encUnary).injective h)
    dsimp only at ha hi
    subst ha
    exact congrArg (Sigma.mk a) (Fin.ext hi)⟩

/-- `encWithFinUnary` encodes `⟨a, i⟩` as the framed pair `(a, i.val)` with `i.val` in unary. -/
@[simp] theorem encWithFinUnary_apply {α : Type} (enc : α ↪ List Bool) (k : α → ℕ)
    (q : Σ a : α, Fin (k a)) :
    encWithFinUnary enc k q = encPair enc encUnary (q.1, q.2.val) := rfl

/-- Project the outer input from an `encWithFinUnary`-encoded dependent pair. -/
@[fun_prop]
theorem computableInPolyTime_withFinUnary_fst {α β : Type}
    {encIn : β ↪ List Bool} {enc : α ↪ List Bool} {k : α → ℕ}
    {f : β → Σ a : α, Fin (k a)}
    (hf : ComputableInPolyTime f encIn (encWithFinUnary enc k)) :
    ComputableInPolyTime (fun b => (f b).1) encIn enc :=
  (fst enc encUnary).comp ((ComputableInPolyTime.of_eq (encIn := encWithFinUnary enc k)
    (encOut := encPair enc encUnary) fun _ => rfl).comp hf)

/-- Project the `Fin` index as a unary natural from an `encWithFinUnary`-encoded dependent pair. -/
@[fun_prop]
theorem computableInPolyTime_withFinUnary_val {α β : Type}
    {encIn : β ↪ List Bool} {enc : α ↪ List Bool} {k : α → ℕ}
    {f : β → Σ a : α, Fin (k a)}
    (hf : ComputableInPolyTime f encIn (encWithFinUnary enc k)) :
    ComputableInPolyTime (fun b => ((f b).2 : ℕ)) encIn encUnary :=
  (snd enc encUnary).comp ((ComputableInPolyTime.of_eq (encIn := encWithFinUnary enc k)
    (encOut := encPair enc encUnary) fun _ => rfl).comp hf)

/-- Project the `Fin` index as a binary natural from an `encWithFinUnary`-encoded dependent pair. -/
@[fun_prop]
theorem computableInPolyTime_withFinUnary_val_binary {α β : Type}
    {encIn : β ↪ List Bool} {enc : α ↪ List Bool} {k : α → ℕ}
    {f : β → Σ a : α, Fin (k a)}
    (hf : ComputableInPolyTime f encIn (encWithFinUnary enc k)) :
    ComputableInPolyTime (fun b => ((f b).2 : ℕ)) encIn encNat :=
  unary_to_binary.comp (computableInPolyTime_withFinUnary_val hf)

/-- Tabulate a runtime-indexed `Fin (k a) → β` family in polynomial time when `k` is computed in
unary and the indexed body is polynomial-time on `encWithFinUnary enc k`. -/
theorem computableInPolyTime_ofFn_unary {α β : Type}
    {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {k : α → ℕ} {f : (a : α) → Fin (k a) → β}
    (hk : ComputableInPolyTime k enc encUnary)
    (hf : ComputableInPolyTime (fun q : Σ a, Fin (k a) => f q.1 q.2)
      (encWithFinUnary enc k) encB) :
    ComputableInPolyTime (fun a => List.ofFn (f a)) enc (encList encB) := by
  have hlist : ComputableInPolyTime (fun a : α => (List.range (k a)).map fun j => (a, j))
      enc (encList (encPair enc encUnary)) :=
    mapWithInput (range.comp hk) id'
  have hfin : ComputableInPolyTime
      (fun a : α => (List.finRange (k a)).map fun i => (⟨a, i⟩ : Σ a', Fin (k a')))
      enc (encList (encWithFinUnary enc k)) :=
    hlist.of_enc_eq fun a => by
      have hm : ((List.finRange (k a)).map fun i => encWithFinUnary enc k ⟨a, i⟩) =
          ((List.range (k a)).map fun j => encPair enc encUnary (a, j)) :=
        List.ext_getElem (by simp) fun j hj₁ hj₂ => by simp [encWithFinUnary]
      simpa only [encList, Function.Embedding.coeFn_mk, List.flatMap_map, Function.comp_def]
        using congrArg (List.flatMap frame) hm
  simpa only [Function.comp_def, List.map_map, List.ofFn_eq_map] using hf.map.comp hfin

/-- Emit the code of a typed `Circuit.wiring` from unary output arity and binary wire indices. -/
theorem computableInPolyTime_code_wiring {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m : α → ℕ}
    {sel : (a : α) → Fin (m a) → Fin (n a)}
    (hm : ComputableInPolyTime m enc encUnary)
    (hsel : ComputableInPolyTime (fun q : Σ a, Fin (m a) => (sel q.1 q.2).val)
      (encWithFinUnary enc m) encNat) :
    ComputableInPolyTime (fun a => (wiring σ (sel a)).code) enc (encCode encOp) := by
  simpa only [code_wiring] using
    (const (encOut := encList (encGate encOp)) []).prod
      (computableInPolyTime_ofFn_unary hm hsel)

/-- Emit the code of a typed identity circuit `Circuit.id σ (n a)` from unary arity. -/
theorem computableInPolyTime_code_id {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun a => (Circuit.id σ (n a)).code) enc (encCode encOp) :=
  computableInPolyTime_code_wiring hn
    (computableInPolyTime_withFinUnary_val_binary (id' (encIn := encWithFinUnary enc n)))

/-- Emit the code of a typed `Circuit.oneGate` from binary input arity and binary wire indices. -/
theorem computableInPolyTime_code_oneGate {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (op : σ.Op) {args : (a : α) → Fin (σ.Arity op) → Fin (n a)}
    (hn : ComputableInPolyTime n enc encNat)
    (hargs : ∀ j, ComputableInPolyTime (fun a => (args a j).val) enc encNat) :
    ComputableInPolyTime (fun a => (oneGate (σ := σ) op (args a)).code)
      enc (encCode encOp) := by
  simpa only [code_oneGate] using
    (((const (encOut := encOp) op).prod (ofFn hargs)).cons' (const [])).prod
      (hn.cons' (const []))

/-- Emit the code of a typed `Circuit.append` from binary input arity and the two subcircuit
codes. -/
theorem computableInPolyTime_code_append {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m p : α → ℕ}
    {c : (a : α) → Circuit σ (n a) (m a)} {d : (a : α) → Circuit σ (n a) (p a)}
    (hn : ComputableInPolyTime n enc encNat)
    (hc : ComputableInPolyTime (fun a => (c a).code) enc (encCode encOp))
    (hd : ComputableInPolyTime (fun a => (d a).code) enc (encCode encOp)) :
    ComputableInPolyTime (fun a => ((c a).append (d a)).code) enc (encCode encOp) := by
  simpa only [code_append] using computableInPolyTime_appendCode hn hc hd

/-- Emit the code of a typed `Circuit.pi` family from binary input arity, unary output count, and
uniformly generated component codes. -/
theorem computableInPolyTime_code_pi {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n k : α → ℕ}
    {cs : (a : α) → Fin (k a) → Circuit σ (n a) 1}
    (hn : ComputableInPolyTime n enc encNat)
    (hk : ComputableInPolyTime k enc encUnary)
    (hcs : ComputableInPolyTime (fun q : Σ a, Fin (k a) => (cs q.1 q.2).code)
      (encWithFinUnary enc k) (encCode encOp)) :
    ComputableInPolyTime (fun a => (pi (cs a)).code) enc (encCode encOp) := by
  simpa only [code_pi] using
    computableInPolyTime_appendCodes hn (computableInPolyTime_ofFn_unary hk hcs)

/-- Emit the code of a typed sequential composition `d.comp c` from binary input arity and the two
subcircuit codes. -/
theorem computableInPolyTime_code_comp {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m p : α → ℕ}
    {d : (a : α) → Circuit σ (m a) (p a)} {c : (a : α) → Circuit σ (n a) (m a)}
    (hn : ComputableInPolyTime n enc encNat)
    (hd : ComputableInPolyTime (fun a => (d a).code) enc (encCode encOp))
    (hc : ComputableInPolyTime (fun a => (c a).code) enc (encCode encOp)) :
    ComputableInPolyTime (fun a => ((d a).comp (c a)).code) enc (encCode encOp) := by
  simpa only [code_comp] using computableInPolyTime_compCode hn hd hc

/-- Emit the code of a typed `Circuit.replicate` from binary input arity, unary copy count, and
the base circuit code. -/
theorem computableInPolyTime_code_replicate {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m k : α → ℕ}
    {c : (a : α) → Circuit σ (n a) (m a)}
    (hn : ComputableInPolyTime n enc encNat)
    (hk : ComputableInPolyTime k enc encUnary)
    (hc : ComputableInPolyTime (fun a => (c a).code) enc (encCode encOp)) :
    ComputableInPolyTime (fun a => ((c a).replicate (k a)).code) enc (encCode encOp) := by
  simpa only [code_replicate] using computableInPolyTime_replicateCode hn hk hc

/-- Emit the code of a typed `Circuit.balanced` tree from binary input arity and the operator,
fallback, and leaf circuit codes. -/
theorem computableInPolyTime_code_balanced {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n r : α → ℕ}
    {op : (a : α) → Circuit σ (r a + r a) (r a)}
    {unit : (a : α) → Circuit σ (n a) (r a)}
    {leaves : (a : α) → List (Circuit σ (n a) (r a))}
    (hn : ComputableInPolyTime n enc encNat)
    (hop : ComputableInPolyTime (fun a => (op a).code) enc (encCode encOp))
    (hunit : ComputableInPolyTime (fun a => (unit a).code) enc (encCode encOp))
    (hleaves : ComputableInPolyTime (fun a => (leaves a).map code)
      enc (encList (encCode encOp))) :
    ComputableInPolyTime (fun a => (balanced (op a) (unit a) (leaves a)).code)
      enc (encCode encOp) := by
  simpa only [code_balanced] using computableInPolyTime_balancedCode hn hop hunit hleaves

/-- Emit the code of a conditional choice of typed circuits. -/
theorem computableInPolyTime_code_ite {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m : α → ℕ}
    {p : α → Prop} [∀ a, Decidable (p a)]
    {t e : (a : α) → Circuit σ (n a) (m a)}
    (hp : ComputableInPolyTime (fun a => decide (p a)) enc encBool)
    (ht : ComputableInPolyTime (fun a => (t a).code) enc (encCode encOp))
    (he : ComputableInPolyTime (fun a => (e a).code) enc (encCode encOp)) :
    ComputableInPolyTime (fun a => (if p a then t a else e a).code)
      enc (encCode encOp) :=
  (hp.ite ht he).of_enc_eq fun a => by
    simp only [decide_eq_true_eq]
    split_ifs <;> rfl

/-- Uniform polynomial-time generation of the serialized code `(c a).code` of a typed circuit
family `c : (a : α) → Circuit σ (n a) (m a)` under explicit input encoding `enc` and operation
encoding `encOp`. Indexing `@[fun_prop]` rules on `ComputableCircuitCode` keys each rule by its
outer `Circuit` constructor (`comp`, `append`, `replicate`, `wiring`, `pi`, `balanced`, `ite`)
instead of colliding on `Circuit.code`. -/
@[irreducible, fun_prop]
def ComputableCircuitCode {σ : Signature} {α : Type} {n m : α → ℕ}
    (c : (a : α) → Circuit σ (n a) (m a)) (enc : α ↪ List Bool)
    (encOp : σ.Op ↪ List Bool) : Prop :=
  ComputableInPolyTime (fun a => (c a).code) enc (encCode encOp)

/-- Bridge `ComputableInPolyTime (fun a => (c a).code)` to constructor-indexed
`ComputableCircuitCode`. -/
@[fun_prop]
theorem computableInPolyTime_code {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m : α → ℕ}
    {c : (a : α) → Circuit σ (n a) (m a)}
    (hc : ComputableCircuitCode c enc encOp) :
    ComputableInPolyTime (fun a => (c a).code) enc (encCode encOp) := by
  unfold ComputableCircuitCode at hc
  exact hc

/-- Bridge a plain `ComputableInPolyTime (fun a => (c a).code)` hypothesis (such as a free
circuit-family parameter) into `ComputableCircuitCode`. -/
@[fun_prop]
theorem computableCircuitCode_of_computableInPolyTime {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m : α → ℕ}
    {c : (a : α) → Circuit σ (n a) (m a)}
    (hc : ComputableInPolyTime (fun a => (c a).code) enc (encCode encOp)) :
    ComputableCircuitCode c enc encOp := by
  unfold ComputableCircuitCode
  exact hc

/-- Extract the underlying `ComputableInPolyTime` certificate from `ComputableCircuitCode`. -/
theorem ComputableCircuitCode.computableInPolyTime {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m : α → ℕ}
    {c : (a : α) → Circuit σ (n a) (m a)}
    (hc : ComputableCircuitCode c enc encOp) :
    ComputableInPolyTime (fun a => (c a).code) enc (encCode encOp) :=
  computableInPolyTime_code hc

/-- A fixed typed circuit has constant code in polynomial time. -/
@[fun_prop]
theorem computableCircuitCode_const {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m : ℕ} (c : Circuit σ n m) :
    ComputableCircuitCode (fun _ : α => c) enc encOp := by
  unfold ComputableCircuitCode
  exact const c.code

/-- `@[fun_prop]` rule for `Circuit.id`. -/
@[fun_prop]
theorem computableCircuitCode_id {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) :
    ComputableCircuitCode (fun a => Circuit.id σ (n a)) enc encOp :=
  computableCircuitCode_of_computableInPolyTime (computableInPolyTime_code_id hn)

/-- `@[fun_prop]` rule for `Circuit.wiring`. -/
@[fun_prop]
theorem computableCircuitCode_wiring {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m : α → ℕ}
    {sel : (a : α) → Fin (m a) → Fin (n a)}
    (hm : ComputableInPolyTime m enc encUnary)
    (hsel : ComputableInPolyTime (fun q : Σ a, Fin (m a) => (sel q.1 q.2).val)
      (encWithFinUnary enc m) encNat) :
    ComputableCircuitCode (fun a => wiring σ (sel a)) enc encOp :=
  computableCircuitCode_of_computableInPolyTime (computableInPolyTime_code_wiring hm hsel)

/-- `@[fun_prop]` rule for `Circuit.append`. -/
@[fun_prop]
theorem computableCircuitCode_append {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m p : α → ℕ}
    {c : (a : α) → Circuit σ (n a) (m a)} {d : (a : α) → Circuit σ (n a) (p a)}
    (hn : ComputableInPolyTime n enc encNat)
    (hc : ComputableCircuitCode c enc encOp)
    (hd : ComputableCircuitCode d enc encOp) :
    ComputableCircuitCode (fun a => (c a).append (d a)) enc encOp :=
  computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_code_append hn hc.computableInPolyTime hd.computableInPolyTime)

/-- `@[fun_prop]` rule for `Circuit.pi`. -/
@[fun_prop]
theorem computableCircuitCode_pi {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n k : α → ℕ}
    {cs : (a : α) → Fin (k a) → Circuit σ (n a) 1}
    (hn : ComputableInPolyTime n enc encNat)
    (hk : ComputableInPolyTime k enc encUnary)
    (hcs : ComputableCircuitCode (fun q : Σ a, Fin (k a) => cs q.1 q.2)
      (encWithFinUnary enc k) encOp) :
    ComputableCircuitCode (fun a => pi (cs a)) enc encOp :=
  computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_code_pi hn hk hcs.computableInPolyTime)

/-- `@[fun_prop]` rule for `Circuit.comp`. -/
@[fun_prop]
theorem computableCircuitCode_comp {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m p : α → ℕ}
    {d : (a : α) → Circuit σ (m a) (p a)} {c : (a : α) → Circuit σ (n a) (m a)}
    (hn : ComputableInPolyTime n enc encNat)
    (hd : ComputableCircuitCode d enc encOp)
    (hc : ComputableCircuitCode c enc encOp) :
    ComputableCircuitCode (fun a => (d a).comp (c a)) enc encOp :=
  computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_code_comp hn hd.computableInPolyTime hc.computableInPolyTime)

/-- `@[fun_prop]` rule for `Circuit.replicate`. -/
@[fun_prop]
theorem computableCircuitCode_replicate {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m k : α → ℕ}
    {c : (a : α) → Circuit σ (n a) (m a)}
    (hn : ComputableInPolyTime n enc encNat)
    (hk : ComputableInPolyTime k enc encUnary)
    (hc : ComputableCircuitCode c enc encOp) :
    ComputableCircuitCode (fun a => (c a).replicate (k a)) enc encOp :=
  computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_code_replicate hn hk hc.computableInPolyTime)

/-- `@[fun_prop]` rule for `Circuit.balanced`. -/
@[fun_prop]
theorem computableCircuitCode_balanced {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n r : α → ℕ}
    {op : (a : α) → Circuit σ (r a + r a) (r a)}
    {unit : (a : α) → Circuit σ (n a) (r a)}
    {leaves : (a : α) → List (Circuit σ (n a) (r a))}
    (hn : ComputableInPolyTime n enc encNat)
    (hop : ComputableCircuitCode op enc encOp)
    (hunit : ComputableCircuitCode unit enc encOp)
    (hleaves : ComputableInPolyTime (fun a => (leaves a).map code)
      enc (encList (encCode encOp))) :
    ComputableCircuitCode (fun a => balanced (op a) (unit a) (leaves a)) enc encOp :=
  computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_code_balanced hn hop.computableInPolyTime
      hunit.computableInPolyTime hleaves)

/-- `@[fun_prop]` rule for conditional choice of typed circuits. -/
@[fun_prop]
theorem computableCircuitCode_ite {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n m : α → ℕ}
    {p : α → Prop} [∀ a, Decidable (p a)]
    {t e : (a : α) → Circuit σ (n a) (m a)}
    (hp : ComputableInPolyTime (fun a => decide (p a)) enc encBool)
    (ht : ComputableCircuitCode t enc encOp)
    (he : ComputableCircuitCode e enc encOp) :
    ComputableCircuitCode (fun a => if p a then t a else e a) enc encOp :=
  computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_code_ite hp ht.computableInPolyTime he.computableInPolyTime)

/-- Emit the circuit code of an input formula `(Formula.input (w a)).toCircuit`. -/
theorem _root_.Cslib.Circuits.Formula.computableInPolyTime_code_input_toCircuit
    {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    {w : (a : α) → Fin (n a)}
    (hw : ComputableInPolyTime (fun a => (w a).val) enc encNat) :
    ComputableInPolyTime (fun a => (Formula.input (σ := σ) (w a)).toCircuit.code)
      enc (encCode encOp) :=
  (const (encOut := encList (encGate encOp)) []).prod (hw.cons' (const []))

/-- Emit the circuit code of a fixed-operation formula node `(Formula.gate op (args a)).toCircuit`
from binary input arity and the subformula circuit codes. -/
theorem _root_.Cslib.Circuits.Formula.computableInPolyTime_code_gate_toCircuit
    {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (op : σ.Op) {args : (a : α) → Fin (σ.Arity op) → Formula σ (n a)}
    (hn : ComputableInPolyTime n enc encNat)
    (hargs : ∀ j, ComputableInPolyTime (fun a => (args a j).toCircuit.code) enc (encCode encOp)) :
    ComputableInPolyTime (fun a => (Formula.gate op (args a)).toCircuit.code)
      enc (encCode encOp) := by
  simpa only [Formula.toCircuit, code_comp, code_pi] using
    computableInPolyTime_compCode hn (const (oneGate (σ := σ) op _root_.id).code)
      (computableInPolyTime_appendCodes hn (ofFn hargs))

/-- Emit the circuit code of a conditional choice of formulas
`(if p a then t a else e a).toCircuit`. -/
theorem _root_.Cslib.Circuits.Formula.computableInPolyTime_code_ite_toCircuit
    {σ : Signature} {encOp : σ.Op ↪ List Bool}
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    {p : α → Prop} [∀ a, Decidable (p a)]
    {t e : (a : α) → Formula σ (n a)}
    (hp : ComputableInPolyTime (fun a => decide (p a)) enc encBool)
    (ht : ComputableInPolyTime (fun a => (t a).toCircuit.code) enc (encCode encOp))
    (he : ComputableInPolyTime (fun a => (e a).toCircuit.code) enc (encCode encOp)) :
    ComputableInPolyTime (fun a => (if p a then t a else e a).toCircuit.code)
      enc (encCode encOp) :=
  (hp.ite ht he).of_enc_eq fun a => by
    simp only [decide_eq_true_eq]
    split_ifs <;> rfl

end TypedFunProp

end Circuit

end Cslib.Circuits
