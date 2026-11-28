/-
Copyright (c) 2026 Christian Reitwiessner, Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedState
public import CslibFrontier.Computability.Circuit.Encoding.Basic
public import CslibFrontier.Computability.WordRAM.Realization.RecordOps
public import CslibFrontier.Computability.WordRAM.Structured
import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.OfCircuit
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Word layout of the input circuit of the `4n - 9d` refuter, and its charged decoding

The input layout of the Word-RAM refuter of issue `#4322` (Milestone 4), and a fixed
standard-basis program `initCode` that decodes it and builds the packed initial state
`initialPacked C` of `Cslib.Algorithms.WordRAM.Refuter4n.PackedState` in memory, with an
`ExecWithin` certificate and an explicit instruction bound in the library's Word-RAM cost model.
No running time is claimed here for the refuter as a whole.

**Input layout** (`encode`). A circuit `C : Circuit (fullSignature 2 Bool) n 1` with `s = C.size`
program lines is the word list `[n, s]`, then the three words `LineWords` (tag, left, right) of
each line in program order, then the number of the output wire. The line words are read off the
existing circuit code `Circuit.code` (`codeWords`), so wires are their numbers
`Wire.toNat` (`input i ↦ i`, `gate k ↦ n + k`). A line `.fn op` has the 4-bit truth table `ttOf` of
`op` as tag (below `16`) and the numbers of its two wires; a constant line `.con c` has tag
`16 + c` and operand words `0`. This is a word list for `Cslib.WordRAM.Data.init`, one field per
word, so the program reads each field with one load. It is separate from the bit-string code
`Cslib.Circuits.Circuit.encCircuit`, whose decoding on the Word-RAM would need bit parsing.
The words determine the circuit (`encode_injective`).
`LineWords` has the shape of the gate row `GateRow` of the packed state but other contents (wire
numbers and the constant tags `16 + c`, not argument codes), so it is a separate record. At an
admitted width every input word fits (`inputFits_encode`).

**Decoding.** `initCode` decodes the lines in one pass in program order, as the one-pass
gate-table builder of `SemiCircuit.ofCircuitBinary`: line `j` reads the literal codes
(`litCode`) of the earlier lines, absorbs the negations of its operands into its
truth table, and is either a function of one operand (`unaryLit`) or the binary gate `n + j` with
gate row `⟨tt, left, right⟩`. The arithmetic decoder that the program computes is private and is
proved equal to the builder line by line (literal codes and gate rows) through the public interface
of `SemiCircuit.OfCircuit`: the per-line literal and gate `lineBinaryLit`, `lineBinaryGate`, the
wire literals (`programWireLit_input`, `programWireLit_gate`), the prefix and last-line lemmas
(`programGateLit_gate_castSucc`, `programGateLit_gate_last`, `mem_programBinaryGates_gate_of_ne`,
`mem_programBinaryGates_gate_last`, `programBinaryGate_gate_of_ne`, `programBinaryGate_gate_last`)
and `ofCircuitBinary_gates`, `ofCircuitBinary_gate`, `ofCircuitBinary_out`. So the public
statement is about `initialPacked C` itself.

**Memory image** (`Layout`, `Stored`). From a base address, the parameter mask, auxiliary mask,
gate mask, output literal and number of pairs, then `N` gate rows of three words, `E` equation
words, `n` rows of the parameter map and room for `N` two-word pair records. `layout C` places it
just past the input (base `4 + 3 s`) with `N = nameBound C` and `E = eqnBound C`; the program keeps
one scratch word per line after it, in `[(layout C).top, workEnd C)`, and states nothing about
their final values. `Stored L P` does not relate the sizes in `L` to the table lengths of `P`; a
client uses it with `layout C` and the length facts of `Rep`. Its tables are fixed-stride record
arrays `Cslib.WordRAM.Realization.HoldsRecords` (gate rows of three words, equation and parameter
words of one, pair records of two), so the framing and slicing lemmas of that predicate apply.

**Width condition** (`FitsWidth`). `w ≥ n + C.size + 2` (the basis of `Rep.fits`) and `w ≥ 7`
(the tags `16, 17`, and the workspace when `n + C.size < 5`). At these widths the input words fit
(`inputFits_encode`) and every address of the workspace fits (`fits_workEnd`). Memory past the
input starts at zero, so the zero words of the state (unused gate rows, the equation table, the
auxiliary mask, the empty pair list) need no stores.

**Bound.** `exec_initCode`: from `encode C`, at every admitted width, `initCode` stores
`initialPacked C` at `layout C` in at most `initTime C = 6 n + 73 s + 50` instructions in the
library's Word-RAM cost model, counting every load, store, arithmetic and bitwise operation,
comparison, branch and loop test, and every cell outside `[base, workEnd C)` ends as it started.
The workspace bound (`workEnd C`, linear in `n + s`) and the instruction bound are separate
statements.

## Main definitions

* `Cslib.Algorithms.WordRAM.Refuter4n.LineWords`, `codeWords`, `encode`: the input layout.
* `Cslib.Algorithms.WordRAM.Refuter4n.Layout` (`rowAddr`, `eqnAddr`, `phiAddr`, `pairAddr`,
  `top`), `Stored`, `layout`, `workEnd`: the memory image of a packed state.
* `Cslib.Algorithms.WordRAM.Refuter4n.FitsWidth`: the admitted widths.
* `Cslib.Algorithms.WordRAM.Refuter4n.initCode`, `initTime`: the program and its bound.

## Main results

* `Cslib.Algorithms.WordRAM.Refuter4n.encode_injective`: the input words determine the circuit.
* `Cslib.Algorithms.WordRAM.Refuter4n.inputFits_encode`, `fits_workEnd`: fields and addresses
  fit at the admitted widths.
* `Cslib.Algorithms.WordRAM.Refuter4n.exec_initCode`: charged decoding and initial-state
  construction.
-/

public section

namespace Cslib.Algorithms.WordRAM.Refuter4n

open Cslib.Circuits Cslib.Circuits.Boolean.AffineDisperser4n Cslib.Circuits.Boolean.SemiCircuit

variable {n : ℕ}

/-! ### The input layout -/

/-- The three input words of a program line, stored in this order. -/
structure LineWords where
  /-- The truth table `ttOf` (below `16`) of a `.fn` line, or `16 + c` for a constant `.con c`. -/
  tag : ℕ
  /-- The wire number of the first operand (`0` for a constant line). -/
  left : ℕ
  /-- The wire number of the second operand (`0` for a constant line). -/
  right : ℕ

/-- The words of a line code (`Line.code`: the operation and the numbers `Wire.toNat` of the wires
it reads): `.fn op` has the truth table `ttOf` of `op` as tag (below `16`) and the numbers of its
two wires; `.con c` has tag `16 + c` and operand words `0`. -/
@[expose] def codeWords : (fullSignature 2 Bool).Op × List ℕ → LineWords
  | (.fn op, ws) => ⟨ttOf fun a b => op ![a, b], ws.getD 0 0, ws.getD 1 0⟩
  | (.con c, _) => ⟨16 + c.toNat, 0, 0⟩

/-- The Word-RAM input of a circuit, read off its code `Circuit.code` (line codes and output wire
numbers): `[n, s]`, the three words `codeWords` of each line, the number of the output wire. -/
@[expose] def encode (C : Circuit (fullSignature 2 Bool) n 1) : List ℕ :=
  n :: C.size :: (C.code.1.map codeWords).flatMap (fun t => [t.tag, t.left, t.right]) ++ C.code.2

/-- The line words of a program in program order. -/
private def progWords {g : ℕ} (p : Program (fullSignature 2 Bool) n g) : List LineWords :=
  p.code.map codeWords

private theorem encode_eq (C : Circuit (fullSignature 2 Bool) n 1) :
    encode C = n :: C.size :: (progWords C.program).flatMap (fun t => [t.tag, t.left, t.right]) ++
      [(C.outputs 0).toNat] := rfl

/-- The words of one line. -/
private def lineWords {g : ℕ} (line : Line (fullSignature 2 Bool) n g) : LineWords :=
  codeWords line.code

private theorem lineWords_fn {g : ℕ} (op : (Fin 2 → Bool) → Bool)
    (w : Fin ((fullSignature 2 Bool).Arity (.fn op)) → Wire n g) :
    lineWords (⟨.fn op, w⟩ : Line (fullSignature 2 Bool) n g) =
      ⟨ttOf fun a b => op ![a, b], (w ⟨0, by simp [fullSignature]⟩).toNat,
        (w ⟨1, by simp [fullSignature]⟩).toNat⟩ := rfl

private theorem lineWords_con {g : ℕ} (c : Bool)
    (w : Fin ((fullSignature 2 Bool).Arity (.con c)) → Wire n g) :
    lineWords (⟨.con c, w⟩ : Line (fullSignature 2 Bool) n g) = ⟨16 + c.toNat, 0, 0⟩ := rfl

private theorem progWords_gate {g : ℕ} (p : Program (fullSignature 2 Bool) n g)
    (line : Line (fullSignature 2 Bool) n g) :
    progWords (p.gate line) = progWords p ++ [lineWords line] := by
  simp [progWords, lineWords]

/-! ### The decoder -/

/-- A decoded line: its literal code and, for a genuinely binary line, its gate row. -/
private structure DecodedLine where
  lit : ℕ
  row : Option GateRow

/-- The literal code of a wire word, given the literal codes `L` of the earlier lines: input
`i ↦ litCode (node i false) = 2 i + 4`, gate `k ↦ L[k]`. -/
private def wireLit (n : ℕ) (L : List ℕ) (x : ℕ) : ℕ :=
  if x < n then x + x + 4 else L.getD (x - n) 0

/-- Swap the truth-table bits `0 ↔ 1` and `2 ↔ 3` (negate the second input). -/
private def swapLo (t : ℕ) : ℕ := ((t &&& 5) <<< 1) ||| ((t >>> 1) &&& 5)

/-- Swap the truth-table bits `0 ↔ 2` and `1 ↔ 3` (negate the first input). -/
private def swapHi (t : ℕ) : ℕ := ((t &&& 3) <<< 2) ||| ((t >>> 2) &&& 3)

/-- Absorb the negations of the operand literals `x₀, x₁` into the truth table `t`. -/
private def absorb (t x₀ x₁ : ℕ) : ℕ :=
  let t := if x₁ &&& 1 = 1 then swapLo t else t
  if x₀ &&& 1 = 1 then swapHi t else t

/-- Classify line `j` with absorbed truth table `u` and operand literal codes `x₀, x₁`: a
function of one operand (`unaryLit`) or a binary gate `n + j`. Returns the literal code of the
line and the gate row, if any. -/
private def classify (n j u x₀ x₁ : ℕ) : DecodedLine :=
  if (u ^^^ (u >>> 1)) &&& 5 = 0 then
    ⟨if u &&& 1 = (u >>> 2) &&& 1 then (u &&& 1) + (u &&& 1)
      else x₀ - (x₀ &&& 1) + (u &&& 1), none⟩
  else if (u ^^^ (u >>> 2)) &&& 3 = 0 then
    ⟨if u &&& 1 = (u >>> 1) &&& 1 then (u &&& 1) + (u &&& 1)
      else x₁ - (x₁ &&& 1) + (u &&& 1), none⟩
  else ⟨(n + j) + (n + j) + 4, some ⟨u, x₀ >>> 1, x₁ >>> 1⟩⟩

/-- Decode line `j` given the literal codes `L` of the earlier lines: its literal code and, for a
genuinely binary line, the gate row of gate `n + j`. -/
private def lineOut (n j : ℕ) (L : List ℕ) (tr : LineWords) : DecodedLine :=
  if tr.tag < 16 then
    classify n j (absorb tr.tag (wireLit n L tr.left) (wireLit n L tr.right))
      (wireLit n L tr.left) (wireLit n L tr.right)
  else ⟨(tr.tag - 16) + (tr.tag - 16), none⟩

/-- Decode the lines in order, each reading the literal codes of the earlier ones. -/
private def decodeLines (n : ℕ) (trs : List LineWords) : List DecodedLine :=
  trs.foldl (fun acc tr => acc ++ [lineOut n acc.length (acc.map DecodedLine.lit) tr]) []

private theorem decodeLines_append_singleton (l : List LineWords) (tr : LineWords) :
    decodeLines n (l ++ [tr]) = decodeLines n l ++
      [lineOut n (decodeLines n l).length ((decodeLines n l).map DecodedLine.lit) tr] := by
  simp [decodeLines, List.foldl_append]

private theorem length_decodeLines (l : List LineWords) :
    (decodeLines n l).length = l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l tr ih => simp [decodeLines_append_singleton, ih]

/-! ### Literal codes -/

private theorem litCode_and_one (ℓ : Lit) : litCode ℓ &&& 1 = ℓ.neg.toNat := by
  rw [Nat.and_one_is_mod, litCode]; cases ℓ.neg <;> simp

private theorem litCode_shiftRight (ℓ : Lit) : litCode ℓ >>> 1 = argCode ℓ.arg := by
  rw [Nat.shiftRight_eq_div_pow, litCode, pow_one]
  have := Bool.toNat_le ℓ.neg
  omega

private theorem wireLit_toNat {g : ℕ} (wLit : Wire n g → Lit) (L : List ℕ)
    (hin : ∀ i : Fin n, wLit (.input i) = Lit.node i false)
    (hL : ∀ k : Fin g, L.getD k 0 = litCode (wLit (.gate k))) (w : Wire n g) :
    wireLit n L w.toNat = litCode (wLit w) := by
  cases w with
  | input i =>
    simp only [hin, wireLit, Wire.toNat_input, i.isLt, ↓reduceIte, litCode, Lit.node, argCode,
      Bool.toNat_false]
    omega
  | gate k =>
    simp [wireLit, Wire.toNat_gate, ← hL]

/-- **One line.** On the literal codes of the earlier lines, `lineOut` is the literal code and the
gate row that the one-pass builder of `ofCircuitBinary` assigns to the line. -/
private theorem lineOut_lineWords {g : ℕ} (wLit : Wire n g → Lit) (L : List ℕ)
    (hin : ∀ i : Fin n, wLit (.input i) = Lit.node i false)
    (hL : ∀ k : Fin g, L.getD k 0 = litCode (wLit (.gate k)))
    (line : Line (fullSignature 2 Bool) n g) :
    lineOut n g L (lineWords line) = ⟨litCode (lineBinaryLit wLit line),
      if binaryB2Cost line.op = 1 then some (rowOf (lineBinaryGate wLit line)) else none⟩ := by
  rcases line with ⟨op | c, w⟩
  · have h0 := wireLit_toNat wLit L hin hL (w ⟨0, by simp [fullSignature]⟩)
    have h1 := wireLit_toNat wLit L hin hL (w ⟨1, by simp [fullSignature]⟩)
    simp only [lineWords_fn, lineOut, classify, h0, h1, lineBinaryLit, lineBinaryGate, binaryB2Cost]
    generalize wLit (w ⟨0, by simp [fullSignature]⟩) = l₀
    generalize wLit (w ⟨1, by simp [fullSignature]⟩) = l₁
    have ht := ttOf_lt fun a b => op ![a, b]
    simp only [ht, ↓reduceIte, litCode_shiftRight, absorb, litCode_and_one]
    rcases l₀ with ⟨a₀, n₀⟩
    rcases l₁ with ⟨a₁, n₁⟩
    simp only [unaryLit, rowOf, ttOf, litCode, Lit.const, argCode]
    obtain ⟨b₀₀, h₀₀⟩ : ∃ b, op ![false, false] = b := ⟨_, rfl⟩
    obtain ⟨b₀₁, h₀₁⟩ : ∃ b, op ![false, true] = b := ⟨_, rfl⟩
    obtain ⟨b₁₀, h₁₀⟩ : ∃ b, op ![true, false] = b := ⟨_, rfl⟩
    obtain ⟨b₁₁, h₁₁⟩ : ∃ b, op ![true, true] = b := ⟨_, rfl⟩
    cases n₀ <;> cases n₁ <;>
      simp only [Bool.xor_true, Bool.xor_false, Bool.not_false, Bool.not_true, h₀₀, h₀₁, h₁₀,
        h₁₁] <;>
      cases b₀₀ <;> cases b₀₁ <;> cases b₁₀ <;> cases b₁₁ <;>
      simp [swapLo, swapHi, Lit.node, show ∀ x : ℕ, 2 * (x + 2) = x + x + 4 from fun x => by omega]
  · cases c <;>
      simp [lineWords_con, lineOut, lineBinaryLit, binaryB2Cost, litCode, Lit.const, argCode]

/-- **Program.** Decoding the line words of a program gives, line by line, the folded literal
code of the one-pass builder (`programGateLit`) and the gate row of the binary gate `n + j`, if
any. -/
private theorem decodeLines_progWords : ∀ {g : ℕ} (p : Program (fullSignature 2 Bool) n g),
    decodeLines n (progWords p) = List.ofFn fun j : Fin g =>
      ⟨litCode (programGateLit p j),
        if n + (j : ℕ) ∈ programBinaryGates p then some (rowOf (programBinaryGate p (n + j)))
        else none⟩
  | _, .empty => rfl
  | _, @Program.gate _ _ g p line => by
    have ih := decodeLines_progWords p
    have hlen : (decodeLines n (progWords p)).length = g := by rw [ih, List.length_ofFn]
    rw [progWords_gate, decodeLines_append_singleton, hlen, List.ofFn_succ_last, ih]
    have hne : ∀ j : Fin g, n + (j : ℕ) ≠ n + g := fun j => by have := j.isLt; omega
    congr 1
    · refine List.ofFn_inj.2 (funext fun j => ?_)
      rw [Fin.val_castSucc]
      simp only [programGateLit_gate_castSucc, mem_programBinaryGates_gate_of_ne p line (hne j),
        programBinaryGate_gate_of_ne p line (hne j)]
    · rw [lineOut_lineWords (programWireLit p) _ (programWireLit_input p) (fun k => by
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_ofFn,
            programWireLit_gate])]
      simp only [Fin.val_last, programGateLit_gate_last, mem_programBinaryGates_gate_last,
        programBinaryGate_gate_last]

/-! ### Validity of the encoding -/

/-- The words of line `j` are valid: the tag is below `18`, a `.fn` line reads only inputs and
earlier lines, and a constant line has operand words `0`. -/
private def WordsOK (n j : ℕ) (tr : LineWords) : Prop :=
  tr.tag < 18 ∧ (tr.tag < 16 → tr.left < n + j ∧ tr.right < n + j) ∧
    (16 ≤ tr.tag → tr.left = 0 ∧ tr.right = 0)

private theorem wordsOK_lineWords {g : ℕ} (line : Line (fullSignature 2 Bool) n g) :
    WordsOK n g (lineWords line) := by
  rcases line with ⟨op | c, w⟩
  · have := ttOf_lt fun a b => op ![a, b]
    refine ⟨by simp only [lineWords_fn]; omega, fun _ => ⟨Wire.toNat_lt _, Wire.toNat_lt _⟩,
      fun h => ?_⟩
    simp only [lineWords_fn] at h
    omega
  · have := Bool.toNat_le c
    refine ⟨by simp only [lineWords_con]; omega, fun h => ?_, fun _ => ⟨rfl, rfl⟩⟩
    simp only [lineWords_con] at h
    omega

private theorem progWords_ok : ∀ {g : ℕ} (p : Program (fullSignature 2 Bool) n g),
    (progWords p).length = g ∧ ∀ j < g, WordsOK n j ((progWords p).getD j ⟨0, 0, 0⟩)
  | _, .empty => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | _, @Program.gate _ _ g p line => by
    obtain ⟨hl, hok⟩ := progWords_ok p
    refine ⟨by simp [progWords_gate, hl], fun j hj => ?_⟩
    simp only [progWords_gate]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact hok j hj
    · rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
      exact wordsOK_lineWords line

/-- The `c`-th word of a triple. -/
private def lineWord (tr : LineWords) : ℕ → ℕ
  | 0 => tr.tag
  | 1 => tr.left
  | _ => tr.right

private theorem getD_flatMap_triple : ∀ (l : List LineWords) (j c : ℕ), j < l.length →
    c < 3 → (l.flatMap fun t => [t.tag, t.left, t.right]).getD (3 * j + c) 0 =
      lineWord (l.getD j ⟨0, 0, 0⟩) c
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | t :: l, 0, c, _, hc => by
    interval_cases c <;> rfl
  | t :: l, j + 1, c, hj, hc => by
    rw [List.flatMap_cons, show 3 * (j + 1) + c = 3 * j + c + 3 by omega,
      List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel, List.getD_cons_succ]
    exact getD_flatMap_triple l j c (by simpa using hj) hc

private theorem length_flatMap_triple (l : List LineWords) :
    (l.flatMap fun t => [t.tag, t.left, t.right]).length = 3 * l.length := by
  simp [List.length_flatMap, Nat.mul_comm]

/-- Reads of the input memory. -/
private theorem init_encode (C : Circuit (fullSignature 2 Bool) n 1) :
    (Cslib.WordRAM.Data.init (encode C) : Cslib.WordRAM.Data 24).mem 1 = n ∧
    (Cslib.WordRAM.Data.init (encode C) : Cslib.WordRAM.Data 24).mem 2 = C.size ∧
    (∀ j < C.size, ∀ c < 3,
      (Cslib.WordRAM.Data.init (encode C) : Cslib.WordRAM.Data 24).mem (3 + 3 * j + c) =
        lineWord ((progWords C.program).getD j ⟨0, 0, 0⟩) c) ∧
    (Cslib.WordRAM.Data.init (encode C) : Cslib.WordRAM.Data 24).mem (3 + 3 * C.size) =
      (C.outputs 0).toNat ∧
    ∀ a, 4 + 3 * C.size ≤ a →
      (Cslib.WordRAM.Data.init (encode C) : Cslib.WordRAM.Data 24).mem a = 0 := by
  have hl := (progWords_ok C.program).1
  have hf := length_flatMap_triple (progWords C.program)
  rw [hl] at hf
  refine ⟨rfl, rfl, fun j hj c hc => ?_, ?_, fun a ha => ?_⟩
  · rw [show 3 + 3 * j + c = (3 * j + c + 1 + 1) + 1 by omega, Cslib.WordRAM.Data.init_mem_succ]
    simp only [encode_eq]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_cons, hf]; omega),
      List.getD_cons_succ, List.getD_cons_succ]
    exact getD_flatMap_triple _ j c (by rw [hl]; exact hj) hc
  · rw [show 3 + 3 * C.size = (3 * C.size + 2) + 1 by omega, Cslib.WordRAM.Data.init_mem_succ]
    simp only [encode_eq]
    rw [List.getD_append_right _ _ _ _ (by simp [hf])]
    simp [hf]
  · rw [show a = (a - 1) + 1 by omega, Cslib.WordRAM.Data.init_mem_succ, List.getD_eq_default]
    simp only [encode_eq, List.length_cons, List.length_append, hf, List.length_nil]
    omega

/-! ### Decoding prefixes -/

private theorem getD_decodeLines (l : List LineWords) {k : ℕ} (hk : k < l.length) :
    (decodeLines n l).getD k ⟨0, none⟩ =
      lineOut n k (((decodeLines n l).take k).map DecodedLine.lit)
        (l.getD k ⟨0, 0, 0⟩) := by
  induction l using List.reverseRecOn with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | append_singleton l tr ih =>
    have hD := length_decodeLines (n := n) l
    rw [decodeLines_append_singleton]
    rcases Nat.lt_or_ge k l.length with hkl | hkl
    · rw [List.getD_append _ _ _ _ (by omega), List.take_append_of_le_length (by omega),
        List.getD_append _ _ _ _ hkl]
      exact ih hkl
    · have hk' : k = l.length := by
        rw [List.length_append, List.length_singleton] at hk; omega
      subst hk'
      rw [List.getD_append_right _ _ _ _ (by omega), List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega), List.getD_append_right _ _ _ _ le_rfl, hD]
      simp

/-! ### The decoded circuit -/

/-- The decoded lines of `C`. -/
private abbrev outs (C : Circuit (fullSignature 2 Bool) n 1) : List DecodedLine :=
  decodeLines n (progWords C.program)

private theorem getD_outs (C : Circuit (fullSignature 2 Bool) n 1) {j : ℕ} (hj : j < C.size) :
    (outs C).getD j ⟨0, none⟩ = ⟨litCode (programGateLit C.program ⟨j, hj⟩),
      if n + j ∈ (initialState C).gates then
        some (rowOf ((initialState C).gate (n + j))) else none⟩ := by
  rw [outs, decodeLines_progWords, List.getD_eq_getElem _ _ (by simpa using hj),
    List.getElem_ofFn]
  change _ = DecodedLine.mk _ (if n + j ∈ (ofCircuitBinary C).gates then
    some (rowOf ((ofCircuitBinary C).gate (n + j))) else none)
  rw [ofCircuitBinary_gates, ofCircuitBinary_gate]

private theorem length_outs (C : Circuit (fullSignature 2 Bool) n 1) :
    (outs C).length = C.size := by
  rw [outs, length_decodeLines, (progWords_ok C.program).1]

private theorem code_lt (C : Circuit (fullSignature 2 Bool) n 1) {j : ℕ} (hj : j < C.size) :
    ((outs C).getD j ⟨0, none⟩).lit < 2 * nameBound C + 4 := by
  rw [getD_outs C hj, ← programWireLit_gate]
  exact litCode_lt fun t ht => (reads_programWireLit C.program (.gate ⟨j, hj⟩) ht).2

private theorem out_eq (C : Circuit (fullSignature 2 Bool) n 1) :
    litCode (initialState C).out =
      wireLit n ((outs C).map DecodedLine.lit) ((C.outputs 0).toNat) := by
  change litCode (ofCircuitBinary C).out = _
  rw [ofCircuitBinary_out]
  refine (wireLit_toNat (programWireLit C.program) _ (programWireLit_input _)
    (fun k => ?_) _).symm
  rw [List.getD_eq_getElem _ _ (by simp [length_outs]), List.getElem_map]
  have := getD_outs C k.isLt
  rw [List.getD_eq_getElem _ _ (by simp [length_outs])] at this
  rw [this, programWireLit_gate]

private theorem maskOf_gates (C : Circuit (fullSignature 2 Bool) n 1) :
    maskOf (initialState C).gates = ∑ j ∈ Finset.range C.size,
      if ((outs C).getD j ⟨0, none⟩).row.isSome then 2 ^ (n + j) else 0 := by
  have hG : (initialState C).gates =
      ((Finset.range C.size).filter fun j => n + j ∈ (initialState C).gates).map
        (addLeftEmbedding n) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_range, addLeftEmbedding_apply]
    constructor
    · intro hi
      have := mem_gates_ofCircuitBinary hi
      exact ⟨i - n, ⟨by omega, by rwa [Nat.add_sub_cancel' this.1]⟩, by omega⟩
    · rintro ⟨j, ⟨-, hj⟩, rfl⟩
      exact hj
  rw [maskOf, hG, Finset.sum_map, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [getD_outs C (Finset.mem_range.1 hj)]
  by_cases h : n + j ∈ (initialState C).gates <;> simp [h]

private theorem maskOf_range (k : ℕ) : maskOf (Finset.range k) = 2 ^ k - 1 := by
  rw [maskOf, Nat.geomSum_eq le_rfl, Nat.add_one_sub_one, Nat.div_one]

private theorem mem_progWords {g : ℕ} (p : Program (fullSignature 2 Bool) n g) (t : LineWords)
    (ht : t ∈ progWords p) : t.tag < 18 ∧ t.left ≤ n + g ∧ t.right ≤ n + g := by
  obtain ⟨hl, hok⟩ := progWords_ok p
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
  have hjg : j < g := hl ▸ hj
  obtain ⟨h1, h2, h3⟩ := List.getD_eq_getElem (progWords p) ⟨0, 0, 0⟩ hj ▸ hok j hjg
  by_cases h16 : (progWords p)[j].tag < 16
  · have := h2 h16
    exact ⟨h1, by omega, by omega⟩
  · have := h3 (by omega)
    exact ⟨h1, by omega, by omega⟩

/-! ### Faithfulness of the input layout -/

/-- Read a line code back from its words. -/
private def wordsCode (t : LineWords) : (fullSignature 2 Bool).Op × List ℕ :=
  if t.tag < 16 then (FullOp.fn fun x => t.tag.testBit (idx (x 0) (x 1)), [t.left, t.right])
  else (FullOp.con (decide (t.tag = 17)), [])

private theorem wordsCode_codeWords (g : (fullSignature 2 Bool).Op × List ℕ)
    (hg : g.2.length = (fullSignature 2 Bool).Arity g.1) : wordsCode (codeWords g) = g := by
  obtain ⟨op | c, ws⟩ := g
  · obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 (hg : ws.length = 2)
    simp only [codeWords, wordsCode, ttOf_lt, ↓reduceIte, List.getD_cons_zero,
      List.getD_cons_succ]
    refine Prod.ext (congrArg FullOp.fn (funext fun x => ?_)) rfl
    rw [testBit_ttOf]
    congr 1
    ext i
    fin_cases i <;> rfl
  · obtain rfl : ws = [] := List.length_eq_zero_iff.1 hg
    cases c <;> simp [codeWords, wordsCode]

private theorem length_of_mem_code {g : ℕ} (p : Program (fullSignature 2 Bool) n g) :
    ∀ x ∈ p.code, x.2.length = (fullSignature 2 Bool).Arity x.1 := by
  induction p with
  | empty => simp
  | gate p line ih =>
    intro x hx
    rw [Program.code_gate, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih x hx
    · exact Line.length_code_snd line

private theorem map_wordsCode_progWords {g : ℕ} (p : Program (fullSignature 2 Bool) n g) :
    (progWords p).map wordsCode = p.code := by
  rw [progWords, List.map_map]
  exact (List.map_congr_left fun x hx => wordsCode_codeWords x (length_of_mem_code p x hx)).trans
    (List.map_id _)

private theorem flatMap_triple_injective : ∀ {l₁ l₂ : List LineWords},
    l₁.flatMap (fun t => [t.tag, t.left, t.right]) =
      l₂.flatMap (fun t => [t.tag, t.left, t.right]) → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | ⟨_, _, _⟩ :: _, ⟨_, _, _⟩ :: _, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl, rfl, h⟩ := h
    rw [flatMap_triple_injective h]

/-- **Faithful layout.** The input words determine the circuit. -/
theorem encode_injective :
    Function.Injective (encode : Circuit (fullSignature 2 Bool) n 1 → List ℕ) := by
  intro C₁ C₂ h
  rw [encode_eq, encode_eq] at h
  simp only [List.cons_append, List.cons.injEq] at h
  obtain ⟨-, hs, h⟩ := h
  have hl : ((progWords C₁.program).flatMap fun t => [t.tag, t.left, t.right]).length =
      ((progWords C₂.program).flatMap fun t => [t.tag, t.left, t.right]).length := by
    rw [length_flatMap_triple, length_flatMap_triple, (progWords_ok C₁.program).1,
      (progWords_ok C₂.program).1, hs]
  obtain ⟨hw, ho⟩ := List.append_inj h hl
  have hp := congrArg (List.map wordsCode) (flatMap_triple_injective hw)
  rw [map_wordsCode_progWords, map_wordsCode_progWords] at hp
  refine Circuit.code_injective (Prod.ext hp ?_)
  simpa [Circuit.code] using ho

/-! ### The memory image of a packed state -/

/-- Addresses of a packed state in memory, from the base address `base`, with `N` gate rows,
`E` equation words and `n` rows of the parameter map. -/
structure Layout where
  /-- Address of the parameter mask; then the auxiliary mask, gate mask, output literal and
  number of pairs. -/
  base : ℕ
  /-- Number of gate rows. -/
  N : ℕ
  /-- Number of equation words. -/
  E : ℕ
  /-- Number of rows of the parameter map. -/
  n : ℕ

namespace Layout

/-- Word `c < 3` of gate row `J`. -/
@[expose] def rowAddr (L : Layout) (J c : ℕ) : ℕ := L.base + 5 + 3 * J + c

/-- Equation word `e`. -/
@[expose] def eqnAddr (L : Layout) (e : ℕ) : ℕ := L.base + 5 + 3 * L.N + e

/-- Row `i` of the parameter map. -/
@[expose] def phiAddr (L : Layout) (i : ℕ) : ℕ := L.base + 5 + 3 * L.N + L.E + i

/-- Word `c < 2` of pair record `k` (room for `N` records, `Rep.length_pairs_le`). -/
@[expose] def pairAddr (L : Layout) (k c : ℕ) : ℕ := L.base + 5 + 3 * L.N + L.E + L.n + 2 * k + c

/-- The first address past the packed state. -/
@[expose] def top (L : Layout) : ℕ := L.base + 5 + 5 * L.N + L.E + L.n

end Layout

/-- The memory `mem` holds the words of the packed state `P` at the addresses of `L`. It does not
relate the sizes `L.N`, `L.E`, `L.n` to the table lengths of `P`, so the regions are disjoint only
when those lengths are at most the sizes (as for `layout C` and a state represented by `Rep`). -/
structure Stored (L : Layout) (P : PackedState) (mem : ℕ → ℕ) : Prop where
  /-- The parameter mask. -/
  params : mem L.base = P.params
  /-- The auxiliary mask. -/
  aux : mem (L.base + 1) = P.aux
  /-- The gate mask. -/
  gates : mem (L.base + 2) = P.gates
  /-- The output literal. -/
  out : mem (L.base + 3) = P.out
  /-- The number of pair records. -/
  pairCount : mem (L.base + 4) = P.pairs.length
  /-- The gate rows `⟨tt, left, right⟩`, three words each from `L.rowAddr 0 0`. -/
  gateRows : Cslib.WordRAM.Realization.HoldsRecords 3 (L.rowAddr 0 0)
    (P.gateRows.map fun r => ![r.tt, r.left, r.right]) mem
  /-- The equation words, one each from `L.eqnAddr 0`. -/
  eqnRows : Cslib.WordRAM.Realization.HoldsRecords 1 (L.eqnAddr 0) (P.eqnRows.map fun e => ![e]) mem
  /-- The rows of the parameter map, one word each from `L.phiAddr 0`. -/
  phiRows : Cslib.WordRAM.Realization.HoldsRecords 1 (L.phiAddr 0) (P.phiRows.map fun r => ![r]) mem
  /-- The pair records, two words each from `L.pairAddr 0 0`. -/
  pairs : Cslib.WordRAM.Realization.HoldsRecords 2 (L.pairAddr 0 0)
    (P.pairs.map fun pr => ![pr.1, pr.2]) mem

/-- `Stored` from its words, row by row. -/
private theorem stored_of_words {L : Layout} {P : PackedState} {mem : ℕ → ℕ}
    (h₀ : mem L.base = P.params) (h₁ : mem (L.base + 1) = P.aux)
    (h₂ : mem (L.base + 2) = P.gates) (h₃ : mem (L.base + 3) = P.out)
    (h₄ : mem (L.base + 4) = P.pairs.length)
    (hg : ∀ J < P.gateRows.length, mem (L.rowAddr J 0) = (P.gateRows.getD J ⟨0, 0, 0⟩).tt ∧
      mem (L.rowAddr J 1) = (P.gateRows.getD J ⟨0, 0, 0⟩).left ∧
      mem (L.rowAddr J 2) = (P.gateRows.getD J ⟨0, 0, 0⟩).right)
    (he : ∀ e < P.eqnRows.length, mem (L.eqnAddr e) = P.eqnRows.getD e 0)
    (hp : ∀ i < P.phiRows.length, mem (L.phiAddr i) = P.phiRows.getD i 0)
    (hq : ∀ k < P.pairs.length, mem (L.pairAddr k 0) = (P.pairs.getD k (0, 0)).1 ∧
      mem (L.pairAddr k 1) = (P.pairs.getD k (0, 0)).2) :
    Stored L P mem := by
  refine ⟨h₀, h₁, h₂, h₃, h₄, fun J hJ c => ?_, fun e hE c => ?_, fun i hi c => ?_,
    fun k hk c => ?_⟩
  · rw [List.length_map] at hJ
    obtain ⟨a, b, d⟩ := hg J hJ
    rw [List.getD_eq_getElem _ _ hJ] at a b d
    have hA : ∀ c' : ℕ, L.rowAddr 0 0 + 3 * J + c' = L.rowAddr J c' := fun c' => by
      unfold Layout.rowAddr; omega
    rw [hA, List.getElem_map]
    fin_cases c
    exacts [a, b, d]
  · rw [List.length_map] at hE
    have hA : L.eqnAddr 0 + 1 * e + (c : ℕ) = L.eqnAddr e := by
      rw [Fin.fin_one_eq_zero c, Fin.val_zero]; unfold Layout.eqnAddr; omega
    rw [hA, List.getElem_map, Fin.fin_one_eq_zero c, he e hE, List.getD_eq_getElem _ _ hE]
    rfl
  · rw [List.length_map] at hi
    have hA : L.phiAddr 0 + 1 * i + (c : ℕ) = L.phiAddr i := by
      rw [Fin.fin_one_eq_zero c, Fin.val_zero]; unfold Layout.phiAddr; omega
    rw [hA, List.getElem_map, Fin.fin_one_eq_zero c, hp i hi, List.getD_eq_getElem _ _ hi]
    rfl
  · rw [List.length_map] at hk
    obtain ⟨a, b⟩ := hq k hk
    rw [List.getD_eq_getElem _ _ hk] at a b
    have hA : ∀ c' : ℕ, L.pairAddr 0 0 + 2 * k + c' = L.pairAddr k c' := fun c' => by
      unfold Layout.pairAddr; omega
    rw [hA, List.getElem_map]
    fin_cases c
    exacts [a, b]

/-- The layout of the initial state of `C`, just past the input: base `4 + 3 C.size`,
`nameBound C` gate rows, `eqnBound C` equation words and `n` rows of the parameter map. The
program keeps one scratch word per line at `top + j`. -/
@[expose] def layout (C : Circuit (fullSignature 2 Bool) n 1) : Layout :=
  ⟨4 + 3 * C.size, nameBound C, eqnBound C, n⟩

/-- The end of the workspace of the program: the packed state and one scratch word per line. -/
@[expose] def workEnd (C : Circuit (fullSignature 2 Bool) n 1) : ℕ := (layout C).top + C.size

private theorem workEnd_eq (C : Circuit (fullSignature 2 Bool) n 1) :
    workEnd C = 9 + 16 * C.size + 11 * n := by
  simp only [workEnd, layout, Layout.top, nameBound, eqnBound]; omega

/-- Admitted word widths: `w ≥ n + C.size + 2` (the width basis of `Rep.fits`) and `w ≥ 7` (the
tags `16, 17` of constant lines, and the workspace of small circuits). -/
@[expose] def FitsWidth (C : Circuit (fullSignature 2 Bool) n 1) (w : ℕ) : Prop :=
  nameBound C + 2 ≤ w ∧ 7 ≤ w

private theorem lt_two_pow_add_two {N : ℕ} (h : 5 ≤ N) : 16 * N + 9 < 4 * 2 ^ N := by
  induction N, h using Nat.le_induction with
  | base => decide
  | succ N _ ih => rw [pow_succ]; omega

/-- **Fit of the workspace.** At an admitted width every address of the program, up to
`workEnd C = 9 + 16 C.size + 11 n`, fits in a word. -/
theorem fits_workEnd (C : Circuit (fullSignature 2 Bool) n 1) {w : ℕ} (hw : FitsWidth C w) :
    Cslib.WordRAM.Fits w (workEnd C) := by
  obtain ⟨hwN, hw7⟩ := hw
  have hE := workEnd_eq C
  have h1 := Nat.pow_le_pow_right (n := 2) two_pos hwN
  have h2 := Nat.pow_le_pow_right (n := 2) two_pos hw7
  rw [pow_add] at h1
  change workEnd C < 2 ^ w
  simp only [nameBound] at h1
  rcases Nat.lt_or_ge (n + C.size) 5 with h | h
  · have : (2 : ℕ) ^ 7 = 128 := rfl
    omega
  · have := lt_two_pow_add_two h
    have : (2 : ℕ) ^ 2 = 4 := rfl
    omega

/-- **Fit of the input.** At an admitted width, the input length and every input word (`n`, the
line count, tags below `18`, wire words below `n + C.size`) fit in a word. -/
theorem inputFits_encode (C : Circuit (fullSignature 2 Bool) n 1) {w : ℕ} (hw : FitsWidth C w) :
    Cslib.WordRAM.InputFits w (encode C) := by
  have hWE := fits_workEnd C hw
  obtain ⟨hwN, hw7⟩ := hw
  have hw5 : 5 ≤ w := by omega
  have hE := workEnd_eq C
  have h32 := Nat.pow_le_pow_right (n := 2) two_pos hw5
  change workEnd C < 2 ^ w at hWE
  have hl := (progWords_ok C.program).1
  refine ⟨?_, fun v hv => ?_⟩
  · change (encode C).length < 2 ^ w
    simp only [encode_eq, List.length_append, List.length_cons, length_flatMap_triple, hl,
      List.length_nil]
    omega
  · change v < 2 ^ w
    simp only [encode_eq, List.mem_append, List.mem_cons, List.mem_flatMap,
      List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl | ⟨t, ht, hv⟩) | rfl
    · omega
    · omega
    · obtain ⟨h1, h2, h3⟩ := mem_progWords C.program t ht
      have : (2 : ℕ) ^ 5 = 32 := rfl
      rcases hv with rfl | rfl | rfl <;> omega
    · have := Wire.toNat_lt (C.outputs 0)
      omega

/-! ### The Word-RAM program -/

/-- A register below `k` is not a register at index `k` or above. -/
private theorem ne_of_lt_val {k : ℕ} {i r : Fin 24} (hi : i.val < k) (hr : k ≤ r.val := by decide) :
    i ≠ r := fun h => by subst h; omega

section Program

open Cslib.WordRAM

/-- `n`. -/
private abbrev rN : Fin 24 := 0
/-- `s`, the number of lines. -/
private abbrev rS : Fin 24 := 1
/-- Constant `1`. -/
private abbrev rOne : Fin 24 := 2
/-- Constant `0`. -/
private abbrev rZero : Fin 24 := 3
/-- Constant `2`. -/
private abbrev rTwo : Fin 24 := 4
/-- Constant `3`. -/
private abbrev rThree : Fin 24 := 5
/-- Constant `4`. -/
private abbrev rFour : Fin 24 := 6
/-- Constant `5`. -/
private abbrev rFive : Fin 24 := 7
/-- Constant `16`. -/
private abbrev r16 : Fin 24 := 8
/-- Address of the first gate row. -/
private abbrev rRow : Fin 24 := 9
/-- Address of the literal scratch table. -/
private abbrev rLit : Fin 24 := 10
/-- Address of the first `phi` row. -/
private abbrev rPhi : Fin 24 := 11
/-- Base address of the packed state. -/
private abbrev rBase : Fin 24 := 12
/-- Loop counter. -/
private abbrev rI : Fin 24 := 13
/-- Input address. -/
private abbrev rA : Fin 24 := 14
/-- Power of two `2 ^ (n + j)`. -/
private abbrev rP : Fin 24 := 15
/-- Gate mask. -/
private abbrev rG : Fin 24 := 16
/-- Truth table. -/
private abbrev rT : Fin 24 := 17
/-- First operand. -/
private abbrev rX0 : Fin 24 := 18
/-- Second operand. -/
private abbrev rX1 : Fin 24 := 19
/-- Literal code of the line. -/
private abbrev rC : Fin 24 := 20
/-- Scratch. -/
private abbrev rU : Fin 24 := 21
/-- Scratch. -/
private abbrev rV : Fin 24 := 22
/-- Scratch. -/
private abbrev rW : Fin 24 := 23

/-- The literal code of the wire word in `rX0`. -/
private def litX0 : Code .standard 24 := ram[
  if rX0 < rN then [ rX0 ← rX0 + rX0; rX0 ← rX0 + rFour ]
    else [ rX0 ← rX0 - rN; rX0 ← rX0 + rLit; rX0 ← *rX0 ] ]

private theorem exec_litX0 {w W : ℕ} (y : Data 24) (L : List ℕ) (hW : Fits w W)
    (hfour : y.regs rFour = 4) (hx : y.regs rX0 + y.regs rX0 + 4 ≤ W)
    (hl : y.regs rX0 - y.regs rN + y.regs rLit ≤ W)
    (hm : y.regs rN ≤ y.regs rX0 →
      y.mem (y.regs rX0 - y.regs rN + y.regs rLit) = L.getD (y.regs rX0 - y.regs rN) 0) :
    ∃ z, ExecWithin w litX0 y z 6 ∧ z.mem = y.mem ∧
      (∀ i : Fin 24, i ≠ rX0 → z.regs i = y.regs i) ∧
      z.regs rX0 = wireLit (y.regs rN) L (y.regs rX0) := by
  refine WP.exists_execWithin ?_
  unfold litX0
  wram_exec [hfour]
  · exact ⟨rfl, fun i hi => by wram_simp, by wram_simp; simp [wireLit, hc]⟩
  · exact ⟨rfl, fun i hi => by wram_simp, by wram_simp; simp [wireLit, hc, hm (by omega)]⟩

/-- The literal code of the wire word in `rX1`: `litX0` with the registers `rX0, rX1` swapped. -/
private def litX1 : Code .standard 24 := litX0.rename (Equiv.swap rX0 rX1)

private theorem exec_litX1 {w W : ℕ} (y : Data 24) (L : List ℕ) (hW : Fits w W)
    (hfour : y.regs rFour = 4) (hx : y.regs rX1 + y.regs rX1 + 4 ≤ W)
    (hl : y.regs rX1 - y.regs rN + y.regs rLit ≤ W)
    (hm : y.regs rN ≤ y.regs rX1 →
      y.mem (y.regs rX1 - y.regs rN + y.regs rLit) = L.getD (y.regs rX1 - y.regs rN) 0) :
    ∃ z, ExecWithin w litX1 y z 6 ∧ z.mem = y.mem ∧
      (∀ i : Fin 24, i ≠ rX1 → z.regs i = y.regs i) ∧
      z.regs rX1 = wireLit (y.regs rN) L (y.regs rX1) := by
  have hc : ∀ (x : Data 24) i, (x.comap (Equiv.swap rX0 rX1)).regs i =
      x.regs (Equiv.swap rX0 rX1 i) := fun _ _ => rfl
  have hcm : ∀ x : Data 24, (x.comap (Equiv.swap rX0 rX1)).mem = x.mem := fun _ => rfl
  have h0 : Equiv.swap rX0 rX1 rX0 = rX1 := Equiv.swap_apply_left _ _
  have hN : Equiv.swap rX0 rX1 rN = rN := by decide
  have h4 : Equiv.swap rX0 rX1 rFour = rFour := by decide
  have hL : Equiv.swap rX0 rX1 rLit = rLit := by decide
  obtain ⟨z, hz, ⟨hzm, hzr, hzv⟩, -⟩ := ExecWithin.rename_post (Equiv.swap rX0 rX1).injective
    (exec_litX0 (y.comap (Equiv.swap rX0 rX1)) L hW (by simpa only [hc, h4] using hfour)
      (by simpa only [hc, h0] using hx) (by simpa only [hc, h0, hN, hL] using hl)
      (by simpa only [hc, hcm, h0, hN, hL] using hm))
  refine ⟨z, hz, by simpa only [hcm] using hzm, fun i hi => ?_, ?_⟩
  · have hi' : Equiv.swap rX0 rX1 i ≠ rX0 := by
      rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]; exact hi
    simpa only [hc, Equiv.swap_apply_self] using hzr _ hi'
  · simpa only [hc, h0, hN, hL] using hzv

private theorem swapLo_lt : ∀ t < 16, swapLo t < 16 := by decide
private theorem swapHi_lt : ∀ t < 16, swapHi t < 16 := by decide

/-- Absorb the operand negations into the truth table in `rT`. -/
private def absorbBlk : Code .standard 24 := ram[
  rU ← rX1 &&& rOne;
  if rU = rOne then [ rU ← rT &&& rFive; rU ← rU <<< rOne; rV ← rT >>> rOne; rV ← rV &&& rFive;
    rT ← rU ||| rV ] else [ rU ← rU ];
  rU ← rX0 &&& rOne;
  if rU = rOne then [ rU ← rT &&& rThree; rU ← rU <<< rTwo; rV ← rT >>> rTwo;
    rV ← rV &&& rThree; rT ← rU ||| rV ] else [ rU ← rU ] ]

private theorem exec_absorbBlk {w : ℕ} (y : Data 24) (hw : 5 ≤ w)
    (hone : y.regs rOne = 1) (htwo : y.regs rTwo = 2) (hthree : y.regs rThree = 3)
    (hfive : y.regs rFive = 5) (ht : y.regs rT < 16) :
    ∃ z, ExecWithin w absorbBlk y z 16 ∧ z.mem = y.mem ∧
      (∀ i : Fin 24, i ≠ rT → i ≠ rU → i ≠ rV → z.regs i = y.regs i) ∧
      z.regs rT = absorb (y.regs rT) (y.regs rX0) (y.regs rX1) := by
  have h16 : Fits w 16 := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right two_pos hw)
  have hlo := swapLo_lt _ ht
  refine WP.exists_execWithin ?_
  unfold absorbBlk
  wram_exec [hone, htwo, hthree, hfive]
  all_goals exact ⟨rfl, fun i h1 h2 h3 => by wram_simp, by
    wram_simp
    simp only [absorb, swapLo, swapHi, *, ↓reduceIte]⟩

/-- Row field `c` of an optional gate row (`0` for no row). -/
private def rowField : Option GateRow → ℕ → ℕ
  | none, _ => 0
  | some r, 0 => r.tt
  | some r, 1 => r.left
  | some r, _ => r.right

/-- Classify the line from the absorbed truth table in `rT`; for a binary line, store its gate
row and add `rP` to the gate mask. -/
private def classBlk : Code .standard 24 := ram[
  rW ← rT &&& rOne; rU ← rT >>> rOne; rU ← rT ^^^ rU; rU ← rU &&& rFive;
  if rU = rZero then [ rV ← rT >>> rTwo; rV ← rV &&& rOne;
    if rW = rV then [ rC ← rW + rW ] else [ rC ← rX0 &&& rOne; rC ← rX0 - rC; rC ← rC + rW ] ]
  else [ rU ← rT >>> rTwo; rU ← rT ^^^ rU; rU ← rU &&& rThree;
    if rU = rZero then [ rV ← rT >>> rOne; rV ← rV &&& rOne;
      if rW = rV then [ rC ← rW + rW ] else [ rC ← rX1 &&& rOne; rC ← rX1 - rC; rC ← rC + rW ] ]
    else [ rC ← rN + rI; rV ← rC * rThree; rV ← rV + rRow;
      *rV ← rT; rV ← rV + rOne; rU ← rX0 >>> rOne; *rV ← rU; rV ← rV + rOne;
      rU ← rX1 >>> rOne; *rV ← rU;
      rG ← rG + rP; rC ← rC + rC; rC ← rC + rFour ] ] ]

private theorem exec_classBlk {w W : ℕ} (y : Data 24) (hW : Fits w W) (hw : 5 ≤ w)
    (hone : y.regs rOne = 1) (hzero : y.regs rZero = 0) (htwo : y.regs rTwo = 2)
    (hthree : y.regs rThree = 3) (hfour : y.regs rFour = 4) (hfive : y.regs rFive = 5)
    (ht : y.regs rT < 16) (hx₀ : y.regs rX0 + 1 ≤ W) (hx₁ : y.regs rX1 + 1 ≤ W)
    (hrow : y.regs rRow + 3 * (y.regs rN + y.regs rI) + 2 ≤ W)
    (hg : y.regs rG + y.regs rP ≤ W)
    (hz : ∀ c < 3, y.mem (y.regs rRow + 3 * (y.regs rN + y.regs rI) + c) = 0) :
    ∃ z, ExecWithin w classBlk y z 30 ∧
      (∀ i : Fin 24, i ≠ rC → i ≠ rU → i ≠ rV → i ≠ rW → i ≠ rG → z.regs i = y.regs i) ∧
      z.regs rC = (classify (y.regs rN) (y.regs rI) (y.regs rT) (y.regs rX0) (y.regs rX1)).lit ∧
      z.regs rG = y.regs rG + (if (classify (y.regs rN) (y.regs rI) (y.regs rT) (y.regs rX0)
        (y.regs rX1)).row.isSome then y.regs rP else 0) ∧
      (∀ c < 3, z.mem (y.regs rRow + 3 * (y.regs rN + y.regs rI) + c) = rowField
        (classify (y.regs rN) (y.regs rI) (y.regs rT) (y.regs rX0) (y.regs rX1)).row c) ∧
      ∀ a, (a < y.regs rRow + 3 * (y.regs rN + y.regs rI) ∨
        y.regs rRow + 3 * (y.regs rN + y.regs rI) + 3 ≤ a) → z.mem a = y.mem a := by
  have h16 : Fits w 16 := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right two_pos hw)
  refine WP.exists_execWithin ?_
  unfold classBlk
  wram_exec [hone, hzero, htwo, hthree, hfour, hfive]
  all_goals
    refine ⟨fun i h1 h2 h3 h4 h5 => by wram_simp, ?_, ?_, fun c hc3 => ?_, fun a ha => ?_⟩
  all_goals wram_simp
  all_goals simp only [classify, *, ↓reduceIte, Option.isSome_none, Option.isSome_some,
    Bool.false_eq_true, rowField, add_zero]
  interval_cases c <;> simp only [Data.write, Data.set_mem, Function.update_apply] <;>
    split_ifs <;> first | rfl | omega

private theorem absorb_lt {t : ℕ} (ht : t < 16) (x₀ x₁ : ℕ) : absorb t x₀ x₁ < 16 := by
  have h1 : (if x₁ &&& 1 = 1 then swapLo t else t) < 16 := by
    split_ifs
    exacts [swapLo_lt t ht, ht]
  simp only [absorb]
  split_ifs at h1 ⊢ <;> first | exact swapHi_lt _ h1 | exact h1

/-- Read the three words of a line. -/
private def readBlk : Code .standard 24 := ram[
  rT ← *rA; rA ← rA + rOne; rX0 ← *rA; rA ← rA + rOne; rX1 ← *rA; rA ← rA + rOne ]

/-- The literal code `2 c` of a constant line with tag `16 + c`. -/
private def conBlk : Code .standard 24 := ram[ rC ← rT - r16; rC ← rC + rC ]

/-- Store the literal code of the line and advance to the next line. -/
private def storeBlk : Code .standard 24 := ram[
  rV ← rLit + rI; *rV ← rC; rP ← rP + rP; rI ← rI + rOne ]

/-- A `.fn` line: operand literals, absorption, classification. -/
private def fnBlk : Code .standard 24 := .seq litX0 (.seq litX1 (.seq absorbBlk classBlk))

/-- One line of the decoder. -/
private def lineBody : Code .standard 24 :=
  .seq readBlk (.seq (.branch (.lt rT r16) fnBlk conBlk) storeBlk)

private theorem exec_lineBody {w W : ℕ} (y : Data 24) (L : List ℕ) (tr : LineWords)
    (hW : Fits w W) (hw : 5 ≤ w)
    (hone : y.regs rOne = 1) (hzero : y.regs rZero = 0) (htwo : y.regs rTwo = 2)
    (hthree : y.regs rThree = 3) (hfour : y.regs rFour = 4) (hfive : y.regs rFive = 5)
    (h16 : y.regs r16 = 16)
    (htr₀ : y.mem (y.regs rA) = tr.tag) (htr₁ : y.mem (y.regs rA + 1) = tr.left)
    (htr₂ : y.mem (y.regs rA + 1 + 1) = tr.right) (hok : WordsOK (y.regs rN) (y.regs rI) tr)
    (hL : ∀ k < y.regs rI, y.mem (k + y.regs rLit) = L.getD k 0)
    (hLb : ∀ k < y.regs rI, L.getD k 0 + 1 ≤ W)
    (hn : 2 * (y.regs rN + y.regs rI) + 4 ≤ W) (hA : y.regs rA + 3 ≤ W)
    (hlit : y.regs rLit + y.regs rI + 1 ≤ W)
    (hrow : y.regs rRow + 3 * (y.regs rN + y.regs rI) + 3 ≤ y.regs rLit)
    (hg : y.regs rG + y.regs rP ≤ W) (hP : y.regs rP + y.regs rP ≤ W)
    (hz : ∀ c < 3, y.mem (y.regs rRow + 3 * (y.regs rN + y.regs rI) + c) = 0) :
    ∃ z, ExecWithin w lineBody y z 71 ∧
      (∀ i : Fin 24, i.val < 13 → z.regs i = y.regs i) ∧
      z.regs rA = y.regs rA + 3 ∧ z.regs rI = y.regs rI + 1 ∧
      z.regs rP = y.regs rP + y.regs rP ∧
      z.regs rG = y.regs rG +
        (if (lineOut (y.regs rN) (y.regs rI) L tr).row.isSome then y.regs rP else 0) ∧
      z.mem (y.regs rLit + y.regs rI) = (lineOut (y.regs rN) (y.regs rI) L tr).lit ∧
      (∀ c < 3, z.mem (y.regs rRow + 3 * (y.regs rN + y.regs rI) + c) =
        rowField (lineOut (y.regs rN) (y.regs rI) L tr).row c) ∧
      ∀ a, a ≠ y.regs rLit + y.regs rI → (a < y.regs rRow + 3 * (y.regs rN + y.regs rI) ∨
        y.regs rRow + 3 * (y.regs rN + y.regs rI) + 3 ≤ a) → z.mem a = y.mem a := by
  obtain ⟨y₁, he₁, hm₁, hr₁, hT₁, hX0₁, hX1₁, hA₁⟩ : ∃ y₁, ExecWithin w readBlk y y₁ 6 ∧
      y₁.mem = y.mem ∧
      (∀ i : Fin 24, i ≠ rT → i ≠ rX0 → i ≠ rX1 → i ≠ rA → y₁.regs i = y.regs i) ∧
      y₁.regs rT = tr.tag ∧ y₁.regs rX0 = tr.left ∧ y₁.regs rX1 = tr.right ∧
      y₁.regs rA = y.regs rA + 3 := by
    refine WP.exists_execWithin ?_
    unfold readBlk
    wram_exec [hone, htr₀, htr₁, htr₂]
    exact ⟨rfl, fun i h1 h2 h3 h4 => by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp⟩
  have r₁ : ∀ i : Fin 24, i.val < 17 → i ≠ rA → y₁.regs i = y.regs i := fun i hi hiA =>
    hr₁ i (ne_of_lt_val hi) (ne_of_lt_val hi)
      (ne_of_lt_val hi) hiA
  set n := y.regs rN with hn_def
  set j := y.regs rI with hj_def
  set R := y.regs rRow + 3 * (n + j) with hR_def
  set o := lineOut n j L tr with ho_def
  have hbr : ∃ y₂, ExecWithin w (.branch (.lt rT r16) fnBlk conBlk) y₁ y₂ 61 ∧
      (∀ i : Fin 24, i.val < 16 → y₂.regs i = y₁.regs i) ∧
      y₂.regs rC = o.lit ∧ y₂.regs rG = y.regs rG + (if o.row.isSome then y.regs rP else 0) ∧
      (∀ c < 3, y₂.mem (R + c) = rowField o.row c) ∧
      ∀ a, (a < R ∨ R + 3 ≤ a) → y₂.mem a = y.mem a := by
    have hc16 : y₁.regs r16 = 16 := (r₁ r16 (by decide) (by decide)).trans h16
    by_cases ht : tr.tag < 16
    · obtain ⟨ha₀, ha₁⟩ := hok.2.1 ht
      have eN₁ : y₁.regs rN = n := r₁ rN (by decide) (by decide)
      have eLit₁ : y₁.regs rLit = y.regs rLit := r₁ rLit (by decide) (by decide)
      obtain ⟨z₁, e₁, m₁, f₁, v₁⟩ := exec_litX0 y₁ L hW
        ((r₁ rFour (by decide) (by decide)).trans hfour) (by rw [hX0₁]; omega)
        (by rw [hX0₁, eN₁, eLit₁]; omega)
        (fun hge => by rw [hm₁, hX0₁, eN₁, eLit₁]; exact hL _ (by rw [hX0₁, eN₁] at hge; omega))
      have eX1₁ : z₁.regs rX1 = tr.right := (f₁ rX1 (by decide)).trans hX1₁
      have eN₂ : z₁.regs rN = n := (f₁ rN (by decide)).trans eN₁
      have eLit₂ : z₁.regs rLit = y.regs rLit := (f₁ rLit (by decide)).trans eLit₁
      obtain ⟨z₂, e₂, m₂, f₂, v₂⟩ := exec_litX1 z₁ L hW
        ((f₁ rFour (by decide)).trans ((r₁ rFour (by decide) (by decide)).trans hfour))
        (by rw [eX1₁]; omega) (by rw [eX1₁, eN₂, eLit₂]; omega)
        (fun hge => by
          rw [m₁, hm₁, eX1₁, eN₂, eLit₂]; exact hL _ (by rw [eX1₁, eN₂] at hge; omega))
      have ec : ∀ i : Fin 24, i.val < 17 → i ≠ rA → z₂.regs i = y.regs i := fun i hi hiA =>
        (f₂ i (ne_of_lt_val hi)).trans
          ((f₁ i (ne_of_lt_val hi)).trans (r₁ i hi hiA))
      have eT₂ : z₂.regs rT = tr.tag :=
        (f₂ rT (by decide)).trans ((f₁ rT (by decide)).trans hT₁)
      have eX0₂ : z₂.regs rX0 = wireLit n L tr.left := by
        rw [f₂ rX0 (by decide), v₁, eN₁, hX0₁]
      have eX1₂ : z₂.regs rX1 = wireLit n L tr.right := by rw [v₂, eN₂, eX1₁]
      obtain ⟨z₃, e₃, m₃, f₃, v₃⟩ := exec_absorbBlk z₂ hw
        ((ec rOne (by decide) (by decide)).trans hone)
        ((ec rTwo (by decide) (by decide)).trans htwo)
        ((ec rThree (by decide) (by decide)).trans hthree)
        ((ec rFive (by decide) (by decide)).trans hfive) (by rw [eT₂]; exact ht)
      have ec₃ : ∀ i : Fin 24, i.val < 17 → i ≠ rA → i ≠ rU → i ≠ rV → z₃.regs i = y.regs i :=
        fun i hi hiA hU hV => (f₃ i (ne_of_lt_val hi) hU hV).trans
          (ec i hi hiA)
      have eX0₃ : z₃.regs rX0 = wireLit n L tr.left :=
        (f₃ rX0 (by decide) (by decide) (by decide)).trans eX0₂
      have eX1₃ : z₃.regs rX1 = wireLit n L tr.right :=
        (f₃ rX1 (by decide) (by decide) (by decide)).trans eX1₂
      have eT₃ : z₃.regs rT = absorb tr.tag (wireLit n L tr.left) (wireLit n L tr.right) := by
        rw [v₃, eT₂, eX0₂, eX1₂]
      have hwl : ∀ x, x < n + j → wireLit n L x + 1 ≤ W := fun x hx => by
        unfold wireLit
        split_ifs with h
        · omega
        · exact hLb _ (by omega)
      have g := fun (i : Fin 24) (hi : i.val < 13) =>
        ec₃ i (by omega) (ne_of_lt_val hi)
          (ne_of_lt_val hi) (ne_of_lt_val hi)
      have eI₃ : z₃.regs rI = j := ec₃ rI (by decide) (by decide) (by decide) (by decide)
      have eG₃ : z₃.regs rG = y.regs rG := ec₃ rG (by decide) (by decide) (by decide) (by decide)
      have eP₃ : z₃.regs rP = y.regs rP := ec₃ rP (by decide) (by decide) (by decide) (by decide)
      have eN₃ : z₃.regs rN = n := g rN (by decide)
      have eRow₃ : z₃.regs rRow = y.regs rRow := g rRow (by decide)
      have hmem₃ : z₃.mem = y.mem := m₃.trans (m₂.trans (m₁.trans hm₁))
      obtain ⟨z₄, e₄, f₄, v₄, vG₄, vR₄, vF₄⟩ := exec_classBlk z₃ hW hw
        ((g rOne (by decide)).trans hone) ((g rZero (by decide)).trans hzero)
        ((g rTwo (by decide)).trans htwo) ((g rThree (by decide)).trans hthree)
        ((g rFour (by decide)).trans hfour) ((g rFive (by decide)).trans hfive)
        (by rw [eT₃]; exact absorb_lt ht _ _) (by rw [eX0₃]; exact hwl _ ha₀)
        (by rw [eX1₃]; exact hwl _ ha₁) (by rw [eRow₃, eN₃, eI₃]; omega)
        (by rw [eG₃, eP₃]; exact hg)
        (fun c hc => by rw [hmem₃, eRow₃, eN₃, eI₃]; exact hz c hc)
      have hcl : classify (z₃.regs rN) (z₃.regs rI) (z₃.regs rT) (z₃.regs rX0) (z₃.regs rX1) =
          o := by
        rw [eN₃, eI₃, eT₃, eX0₃, eX1₃, ho_def, lineOut]
        simp only [ht, ↓reduceIte]
      rw [hcl] at v₄
      rw [hcl, eG₃, eP₃] at vG₄
      rw [hcl, eRow₃, eN₃, eI₃] at vR₄
      rw [eRow₃, eN₃, eI₃] at vF₄
      refine ⟨z₄, (ExecWithin.branch_pos (by rw [Cond.holds_lt, hT₁, hc16]; exact ht)
        (e₁.seq (e₂.seq (e₃.seq e₄)))).mono (by omega), fun i hi => ?_, v₄, vG₄, vR₄,
        fun a ha => (vF₄ a ha).trans (by rw [hmem₃])⟩
      rw [f₄ i (ne_of_lt_val hi) (ne_of_lt_val hi)
        (ne_of_lt_val hi) (ne_of_lt_val hi)
        (ne_of_lt_val hi),
        f₃ i (ne_of_lt_val hi) (ne_of_lt_val hi)
          (ne_of_lt_val hi),
        f₂ i (ne_of_lt_val hi), f₁ i (ne_of_lt_val hi)]
    · have ho : o = ⟨(tr.tag - 16) + (tr.tag - 16), none⟩ := by
        rw [ho_def, lineOut]; simp only [ht, ↓reduceIte]
      obtain ⟨z, e, mz, fz, vz⟩ : ∃ z, ExecWithin w conBlk y₁ z 2 ∧ z.mem = y₁.mem ∧
          (∀ i : Fin 24, i ≠ rC → z.regs i = y₁.regs i) ∧
          z.regs rC = (tr.tag - 16) + (tr.tag - 16) := by
        have := hok.1
        refine WP.exists_execWithin ?_
        unfold conBlk
        wram_exec [hc16, hT₁]
        exact ⟨rfl, fun i h1 => by wram_simp, by wram_simp⟩
      refine ⟨z, (ExecWithin.branch_neg (by rw [Cond.holds_lt, hT₁, hc16]; exact ht) e).mono
        (by omega), fun i hi => fz i (ne_of_lt_val hi), by rw [vz, ho],
        ?_, fun c hc => ?_, fun a _ => by rw [mz, hm₁]⟩
      · rw [fz rG (by decide), r₁ rG (by decide) (by decide), ho]; simp
      · rw [mz, hm₁, ho, hz c hc]; rfl
  obtain ⟨y₂, he₂, f₂, vC₂, vG₂, vR₂, vF₂⟩ := hbr
  have e₂ : ∀ i : Fin 24, i.val < 16 → i ≠ rA → y₂.regs i = y.regs i := fun i hi hiA =>
    (f₂ i hi).trans (r₁ i (by omega) hiA)
  have eLit₂ : y₂.regs rLit = y.regs rLit := e₂ rLit (by decide) (by decide)
  have eI₂ : y₂.regs rI = j := e₂ rI (by decide) (by decide)
  have eP₂ : y₂.regs rP = y.regs rP := e₂ rP (by decide) (by decide)
  have eOne₂ : y₂.regs rOne = 1 := (e₂ rOne (by decide) (by decide)).trans hone
  obtain ⟨z, he₃, mz, fz, vI, vP⟩ : ∃ z, ExecWithin w storeBlk y₂ z 4 ∧
      z.mem = Function.update y₂.mem (y.regs rLit + j) o.lit ∧
      (∀ i : Fin 24, i ≠ rV → i ≠ rP → i ≠ rI → z.regs i = y₂.regs i) ∧
      z.regs rI = j + 1 ∧ z.regs rP = y.regs rP + y.regs rP := by
    refine WP.exists_execWithin ?_
    unfold storeBlk
    wram_exec [eLit₂, eI₂, eP₂, eOne₂, vC₂]
    exact ⟨by wram_simp, fun i h1 h2 h3 => by wram_simp, by wram_simp, by wram_simp⟩
  have hA₂ : y₂.regs rA = y.regs rA + 3 := (f₂ rA (by decide)).trans hA₁
  refine ⟨z, (he₁.seq (he₂.seq he₃)).mono (by omega), fun i hi => ?_,
    by rw [fz rA (by decide) (by decide) (by decide), hA₂], vI, vP, ?_, ?_, fun c hc => ?_,
    fun a ha hR => ?_⟩
  · rw [fz i (ne_of_lt_val hi) (ne_of_lt_val hi)
      (ne_of_lt_val hi)]
    exact e₂ i (by omega) (ne_of_lt_val hi)
  · rw [fz rG (by decide) (by decide) (by decide), vG₂]
  · rw [mz, Function.update_self]
  · rw [mz, Function.update_of_ne (by omega)]
    exact vR₂ c hc
  · rw [mz, Function.update_of_ne ha]
    exact vF₂ a hR

/-- One `phi` row `2 ^ i` per parameter. -/
private def phiBody : Code .standard 24 := ram[
  rA ← rPhi + rI; *rA ← rP; rP ← rP + rP; rI ← rI + rOne ]

/-- Read `n` and `s`, set the constants and the base addresses of the layout. -/
private def setup : Code .standard 24 := ram[
  rT ← #1; rN ← *rT; rT ← #2; rS ← *rT;
  rOne ← #1; rZero ← #0; rTwo ← #2; rThree ← #3; rFour ← #4; rFive ← #5; r16 ← #16;
  rBase ← rS * rThree; rBase ← rBase + rFour; rRow ← rBase + rFive;
  rU ← rN + rS; rV ← rU * rThree; rPhi ← rRow + rV;
  rV ← rN * rFive; rPhi ← rPhi + rV; rW ← #7; rV ← rS * rW; rPhi ← rPhi + rV;
  rLit ← rPhi + rN; rLit ← rLit + rU; rLit ← rLit + rU;
  rP ← #1; rG ← #0; rI ← #0 ]

/-- Store the parameter mask `2 ^ n - 1` and start the line loop. -/
private def mid : Code .standard 24 := ram[
  rV ← rP - rOne; *rBase ← rV; rI ← #0; rA ← #3 ]

/-- Read the output wire. -/
private def final₁ : Code .standard 24 := ram[ rX0 ← *rA ]

/-- Store the output literal and the gate mask. -/
private def final₂ : Code .standard 24 := ram[
  rV ← rBase + rThree; *rV ← rX0; rV ← rBase + rTwo; *rV ← rG ]

end Program

open Cslib.WordRAM

/-- The fixed standard-basis program that decodes the input circuit and builds the packed initial
state `initialPacked C` at the addresses of `layout C`. -/
def initCode : Code .standard 24 :=
  .seq setup (.seq (.loop (.lt rI rN) phiBody) (.seq mid (.seq (.loop (.lt rI rS) lineBody)
    (.seq final₁ (.seq litX0 final₂)))))

/-- The instruction bound of `initCode`: `6 n + 73 s + 50` for `s = C.size` lines. -/
@[expose] def initTime (C : Circuit (fullSignature 2 Bool) n 1) : ℕ :=
  6 * n + 73 * C.size + 50

/-- The gate mask after `k` lines. -/
private def gmask (C : Circuit (fullSignature 2 Bool) n 1) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, if ((outs C).getD j ⟨0, none⟩).row.isSome then 2 ^ (n + j) else 0

private theorem gmask_add (C : Circuit (fullSignature 2 Bool) n 1) (k : ℕ) :
    gmask C k + 2 ^ n ≤ 2 ^ (n + k) := by
  induction k with
  | zero => simp [gmask]
  | succ k ih =>
    rw [gmask, Finset.sum_range_succ, ← gmask, ← Nat.add_assoc, pow_succ]
    split_ifs <;> omega

private theorem getD_take_outs (C : Circuit (fullSignature 2 Bool) n 1) {k j : ℕ} (hj : j < k) :
    (((outs C).take k).map DecodedLine.lit).getD j 0 = ((outs C).getD j ⟨0, none⟩).lit := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_take_of_lt hj]
  cases (outs C)[j]? <;> rfl

private theorem rowField_getD (o : Option GateRow) :
    rowField o 0 = (o.getD ⟨0, 0, 0⟩).tt ∧ rowField o 1 = (o.getD ⟨0, 0, 0⟩).left ∧
      rowField o 2 = (o.getD ⟨0, 0, 0⟩).right := by
  cases o <;> exact ⟨rfl, rfl, rfl⟩

/-- **Charged decoding and initial state.** At every admitted width, `initCode` runs from the
input `encode C` in at most `initTime C = 6 n + 73 C.size + 50` instructions (in the library's
Word-RAM cost model, every load, store, arithmetic and bitwise operation, branch and loop test
counted) and leaves the packed initial state `initialPacked C` at the addresses of `layout C`.
Every cell outside the workspace `[(layout C).base, workEnd C)`, the input included, ends with its
initial value. -/
theorem exec_initCode (C : Circuit (fullSignature 2 Bool) n 1) {w : ℕ} (hw : FitsWidth C w) :
    ∃ y, ExecWithin w initCode (.init (encode C)) y (initTime C) ∧
      Stored (layout C) (initialPacked C) y.mem ∧
      ∀ a, (a < (layout C).base ∨ workEnd C ≤ a) →
        y.mem a = (Data.init (encode C) : Data 24).mem a := by
  have hWE := fits_workEnd C hw
  obtain ⟨hwN, hw7⟩ := hw
  have hw5 : 5 ≤ w := by omega
  obtain ⟨m₀, hm₀def⟩ : ∃ m, m = (Data.init (encode C) : Data 24).mem := ⟨_, rfl⟩
  obtain ⟨hi1, hi2, hitr, hiout, hi0⟩ := init_encode C
  rw [← hm₀def] at hi1 hi2 hitr hiout hi0
  rw [← hm₀def]
  obtain ⟨htl, hok⟩ := progWords_ok C.program
  have hNB : nameBound C = n + C.size := rfl
  rw [hNB] at hwN
  set s := C.size with hs
  set base := 4 + 3 * s with hbase
  set row := base + 5 with hrow
  set phi := row + 3 * (n + s) + (5 * n + 7 * s) with hphi
  set top := phi + n + 2 * (n + s) with htop
  have hWE' : top + s < 2 ^ w := by
    have : workEnd C < 2 ^ w := hWE
    simp only [workEnd, layout, Layout.top, nameBound, eqnBound] at this
    omega
  obtain ⟨W, hWdef⟩ : ∃ W, W = 2 ^ w - 1 := ⟨_, rfl⟩
  have hW : Fits w W := by
    rw [hWdef]; change 2 ^ w - 1 < 2 ^ w; have := Nat.two_pow_pos w; omega
  have hWt : top + s ≤ W := by omega
  have hpN : 2 ^ (n + s) + 2 ^ (n + s) ≤ W := by
    have := Nat.pow_le_pow_right (n := 2) two_pos (show n + s + 2 ≤ w by omega)
    rw [pow_succ, pow_succ] at this; omega
  have hpw : ∀ k ≤ n + s, 2 ^ k + 2 ^ k ≤ W := fun k hk => by
    have := Nat.pow_le_pow_right (n := 2) two_pos hk; omega
  have h16w : 16 ≤ W := by
    have := Nat.pow_le_pow_right (n := 2) two_pos hw5; omega
  -- setup
  obtain ⟨y₀, he₀, hm₀, eN, eS, eOne, eZero, eTwo, eThree, eFour, eFive, e16, eRow, eLit, ePhi,
      eBase, eP₀, eG₀, eI₀⟩ : ∃ y₀, ExecWithin w setup (.init (encode C)) y₀ 28 ∧ y₀.mem = m₀ ∧
      y₀.regs rN = n ∧ y₀.regs rS = s ∧ y₀.regs rOne = 1 ∧ y₀.regs rZero = 0 ∧
      y₀.regs rTwo = 2 ∧ y₀.regs rThree = 3 ∧ y₀.regs rFour = 4 ∧ y₀.regs rFive = 5 ∧
      y₀.regs r16 = 16 ∧ y₀.regs rRow = row ∧ y₀.regs rLit = top ∧ y₀.regs rPhi = phi ∧
      y₀.regs rBase = base ∧ y₀.regs rP = 1 ∧ y₀.regs rG = 0 ∧ y₀.regs rI = 0 := by
    refine WP.exists_execWithin ?_
    unfold setup
    have hj1 : (Data.init (encode C) : Data 24).mem 1 = n := by rw [← hm₀def]; exact hi1
    have hj2 : (Data.init (encode C) : Data 24).mem 2 = s := by rw [← hm₀def]; exact hi2
    wram_exec [hj1, hj2]
    refine ⟨hm₀def.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      wram_simp <;> omega
  -- the `phi` rows
  let P₁ (i : ℕ) (y : Data 24) : Prop :=
    (∀ r : Fin 24, r.val < 13 → y.regs r = y₀.regs r) ∧ y.regs rP = 2 ^ i ∧ y.regs rG = 0 ∧
      (∀ k < i, y.mem (phi + k) = 2 ^ k) ∧ ∀ a, ¬(phi ≤ a ∧ a < phi + i) → y.mem a = m₀ a
  obtain ⟨y₁, he₁, ⟨hr₁, hP₁, hG₁, hphi₁, hf₁⟩, hI₁⟩ := ExecWithin.loop_count
    (body := phiBody) (index := rI) (limit := rN) (N := n) (T := 4) (w := w) P₁
    (fun y hy => (hy.1 rN (by decide)).trans eN)
    (fun y hy hlt => by
      obtain ⟨hr, hp, hg, hm, hf⟩ := hy
      have ePh : y.regs rPhi = phi := (hr rPhi (by decide)).trans ePhi
      have eO : y.regs rOne = 1 := (hr rOne (by decide)).trans eOne
      have hlt' : y.regs rI < n := hlt
      have := hpw (y.regs rI) (by omega)
      obtain ⟨z, he, mz, rz, Pz, Iz, Gz⟩ : ∃ z, ExecWithin w phiBody y z 4 ∧
          z.mem = Function.update y.mem (phi + y.regs rI) (2 ^ y.regs rI) ∧
          (∀ r : Fin 24, r.val < 13 → z.regs r = y.regs r) ∧
          z.regs rP = 2 ^ y.regs rI + 2 ^ y.regs rI ∧ z.regs rI = y.regs rI + 1 ∧
          z.regs rG = y.regs rG := by
        refine WP.exists_execWithin ?_
        unfold phiBody
        wram_exec [ePh, eO, hp]
        exact ⟨by wram_simp, fun r hr => by
          fin_cases r <;> first | exact absurd hr (by decide) | wram_simp,
          by wram_simp, by wram_simp, by wram_simp⟩
      obtain ⟨hm', hf'⟩ := prefix_write_step (e := fun k => 2 ^ k) hm hf mz
      exact ⟨z, he, ⟨fun r hr' => (rz r hr').trans (hr r hr'), by rw [Pz, pow_succ]; ring,
        by rw [Gz, hg], hm', hf'⟩, Iz⟩)
    (by rw [eI₀]; omega)
    (by rw [eI₀]; exact ⟨fun _ _ => rfl, eP₀, eG₀, fun k hk => absurd hk (Nat.not_lt_zero _),
      fun a _ => by rw [hm₀]⟩)
  -- the parameter mask, start of the line loop
  have eO₁ : y₁.regs rOne = 1 := (hr₁ rOne (by decide)).trans eOne
  have eB₁ : y₁.regs rBase = base := (hr₁ rBase (by decide)).trans eBase
  have := hpw n (by omega)
  obtain ⟨y₂, he₂, hm₂, hr₂, hP₂, hG₂, hI₂, hA₂⟩ : ∃ y₂, ExecWithin w mid y₁ y₂ 4 ∧
      y₂.mem = Function.update y₁.mem base (2 ^ n - 1) ∧
      (∀ r : Fin 24, r.val < 13 → y₂.regs r = y₁.regs r) ∧ y₂.regs rP = 2 ^ n ∧
      y₂.regs rG = 0 ∧ y₂.regs rI = 0 ∧ y₂.regs rA = 3 := by
    refine WP.exists_execWithin ?_
    unfold mid
    wram_exec [eO₁, eB₁, hP₁]
    exact ⟨by wram_simp, fun r hr => by
      fin_cases r <;> first | exact absurd hr (by decide) | wram_simp,
      by wram_simp; exact hP₁, by wram_simp; exact hG₁, by wram_simp, by wram_simp⟩
  obtain ⟨m₁, hm₁def⟩ : ∃ m, m = y₂.mem := ⟨_, rfl⟩
  -- memory before the line loop
  have hm₁in : ∀ a, a < base → m₁ a = m₀ a := fun a ha => by
    rw [hm₁def, hm₂, Function.update_of_ne (by omega), hf₁ a (by omega)]
  have hm₁z : ∀ a, base < a → a < phi → m₁ a = 0 := fun a h1 h2 => by
    rw [hm₁def, hm₂, Function.update_of_ne (by omega), hf₁ a (by omega), hi0 a (by omega)]
  -- the line loop
  let Q (k : ℕ) (y : Data 24) : Prop :=
    (∀ r : Fin 24, r.val < 13 → y.regs r = y₀.regs r) ∧ y.regs rA = 3 + 3 * k ∧
      y.regs rP = 2 ^ (n + k) ∧ y.regs rG = gmask C k ∧
      (∀ j < k, y.mem (top + j) = ((outs C).getD j ⟨0, none⟩).lit) ∧
      (∀ j < k, ∀ c < 3, y.mem (row + 3 * (n + j) + c) =
        rowField ((outs C).getD j ⟨0, none⟩).row c) ∧
      ∀ a, ¬(top ≤ a ∧ a < top + k) → ¬(row + 3 * n ≤ a ∧ a < row + 3 * (n + k)) →
        y.mem a = m₁ a
  obtain ⟨y₃, he₃, ⟨hr₃, hA₃, hP₃, hG₃, hlit₃, hrow₃, hf₃⟩, hI₃⟩ := ExecWithin.loop_count
    (body := lineBody) (index := rI) (limit := rS) (N := s) (T := 71) (w := w) Q
    (fun y hy => (hy.1 rS (by decide)).trans eS)
    (fun y hy hlt => by
      obtain ⟨hr, hA, hp, hg, hlit, hrw, hf⟩ := hy
      set k := y.regs rI with hk
      have hks : k < s := hlt
      have hin : ∀ a, a < base → y.mem a = m₀ a := fun a ha => by
        rw [hf a (by omega) (by omega), hm₁in a ha]
      have g := fun (r : Fin 24) (h : r.val < 13) => hr r h
      have hgm := gmask_add C k
      have hpk := hpw (n + k) (by omega)
      have hpk1 := hpw (n + k + 1) (by omega)
      obtain ⟨z, he, rz, Az, Iz, Pz, Gz, litz, rowz, fz⟩ := exec_lineBody y
        (((outs C).take k).map DecodedLine.lit) ((progWords C.program).getD k ⟨0, 0, 0⟩) hW hw5
        ((g rOne (by decide)).trans eOne) ((g rZero (by decide)).trans eZero)
        ((g rTwo (by decide)).trans eTwo) ((g rThree (by decide)).trans eThree)
        ((g rFour (by decide)).trans eFour) ((g rFive (by decide)).trans eFive)
        ((g r16 (by decide)).trans e16)
        (by rw [hA, hin _ (by omega)]; exact hitr k hks 0 (by decide))
        (by rw [hA, hin _ (by omega)]; exact hitr k hks 1 (by decide))
        (by rw [hA, hin _ (by omega), show 3 + 3 * k + 1 + 1 = 3 + 3 * k + 2 by omega]
            exact hitr k hks 2 (by decide))
        (by rw [g rN (by decide), eN]; exact hok k hks)
        (fun j hj => by
          rw [g rLit (by decide), eLit, Nat.add_comm, hlit j hj, getD_take_outs C hj])
        (fun j hj => by
          rw [getD_take_outs C hj]
          have := code_lt C (show j < C.size by omega)
          rw [hNB] at this; omega)
        (by rw [g rN (by decide), eN]; omega) (by rw [hA]; omega)
        (by rw [g rLit (by decide), eLit]; omega)
        (by rw [g rRow (by decide), eRow, g rLit (by decide), eLit, g rN (by decide), eN]; omega)
        (by rw [hg, hp]; omega) (by rw [hp]; omega)
        (fun c hc => by
          rw [g rRow (by decide), eRow, g rN (by decide), eN,
            hf _ (by omega) (by omega), hm₁z _ (by omega) (by omega)])
      have hlo : lineOut n k (((outs C).take k).map DecodedLine.lit)
          ((progWords C.program).getD k ⟨0, 0, 0⟩) = (outs C).getD k ⟨0, none⟩ :=
        (getD_decodeLines _ (by rw [htl]; exact hks)).symm
      rw [g rN (by decide), eN, hlo] at Gz litz rowz
      rw [g rN (by decide), eN] at fz
      rw [g rLit (by decide), eLit] at litz fz
      rw [g rRow (by decide), eRow] at rowz fz
      refine ⟨z, he, ⟨fun r hr' => (rz r hr').trans (hr r hr'), by rw [Az, hA]; ring,
        by rw [Pz, hp, ← Nat.add_assoc, pow_succ]; ring,
        by rw [Gz, hg, hp, gmask, gmask, Finset.sum_range_succ], fun j hj => ?_,
        fun j hj c hc => ?_, fun a ha1 ha2 => ?_⟩, Iz⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [fz _ (by omega) (by omega)]; exact hlit j hj
        · exact litz
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [fz _ (by omega) (by omega)]; exact hrw j hj c hc
        · exact rowz c hc
      · rw [fz a (by omega) (by omega)]
        exact hf a (by omega) (by omega))
    (by rw [hI₂]; omega)
    (by
      rw [hI₂]
      refine ⟨fun r hr => (hr₂ r hr).trans (hr₁ r hr), by rw [hA₂], by rw [hP₂, Nat.add_zero], by
        rw [hG₂]; rfl, fun j hj => absurd hj (Nat.not_lt_zero _),
        fun j hj => absurd hj (Nat.not_lt_zero _), fun a _ _ => by rw [hm₁def]⟩)
  -- the output literal and the gate mask
  have hin₃ : ∀ a, a < base → y₃.mem a = m₀ a := fun a ha => by
    rw [hf₃ a (by omega) (by omega), hm₁in a ha]
  obtain ⟨y₄, he₄, hm₄, hr₄, hX₄⟩ : ∃ y₄, ExecWithin w final₁ y₃ y₄ 1 ∧ y₄.mem = y₃.mem ∧
      (∀ r : Fin 24, r ≠ rX0 → y₄.regs r = y₃.regs r) ∧
      y₄.regs rX0 = (C.outputs 0).toNat := by
    refine WP.exists_execWithin ?_
    unfold final₁
    wram_exec [hA₃, hin₃ _ (show 3 + 3 * s < base by omega), hiout]
    exact ⟨rfl, fun r hr => by wram_simp, by wram_simp; exact hiout⟩
  have g₄ : ∀ r : Fin 24, r.val < 13 → y₄.regs r = y₀.regs r := fun r hr =>
    (hr₄ r (ne_of_lt_val hr)).trans (hr₃ r hr)
  have hwo := Wire.toNat_lt (C.outputs 0)
  obtain ⟨y₅, he₅, hm₅, hr₅, hX₅⟩ := exec_litX0 y₄ ((outs C).map DecodedLine.lit) hW
    ((g₄ rFour (by decide)).trans eFour) (by rw [hX₄]; omega)
    (by rw [hX₄, g₄ rN (by decide), eN, g₄ rLit (by decide), eLit]; omega)
    (fun hge => by
      rw [hX₄, g₄ rN (by decide), eN] at hge ⊢
      rw [hm₄, g₄ rLit (by decide), eLit, Nat.add_comm, hlit₃ _ (by omega)]
      rw [← getD_take_outs C (k := s) (by omega), List.take_of_length_le (by rw [length_outs])])
  have hout : y₅.regs rX0 = litCode (initialState C).out := by
    rw [hX₅, g₄ rN (by decide), eN, hX₄, out_eq]
  have g₅ : ∀ r : Fin 24, r.val < 13 → y₅.regs r = y₀.regs r := fun r hr =>
    (hr₅ r (ne_of_lt_val hr)).trans (g₄ r hr)
  have eG₅ : y₅.regs rG = gmask C s :=
    (hr₅ rG (by decide)).trans ((hr₄ rG (by decide)).trans hG₃)
  obtain ⟨y₆, he₆, hm₆⟩ : ∃ y₆, ExecWithin w final₂ y₅ y₆ 4 ∧
      y₆.mem = Function.update (Function.update y₅.mem (base + 3) (litCode (initialState C).out))
        (base + 2) (gmask C s) := by
    refine WP.exists_execWithin ?_
    unfold final₂
    wram_exec [g₅ rBase (by decide), eBase, g₅ rThree (by decide), eThree,
      g₅ rTwo (by decide), eTwo, hout, eG₅]
    exact by wram_simp
  -- assembling the bound and the stored state
  have hmem₂ : y₆.mem (base + 2) = gmask C s := by rw [hm₆, Function.update_self]
  have hmem₃ : y₆.mem (base + 3) = litCode (initialState C).out := by
    rw [hm₆, Function.update_of_ne (by omega), Function.update_self]
  have hmemo : ∀ a, a ≠ base + 2 → a ≠ base + 3 → y₆.mem a = y₃.mem a := fun a h2 h3 => by
    rw [hm₆, Function.update_of_ne h2, Function.update_of_ne h3, hm₅, hm₄]
  have hrest₀ : y₃.mem base = 2 ^ n - 1 := by
    rw [hf₃ base (by omega) (by omega), hm₁def, hm₂, Function.update_self]
  have hrestz : ∀ a, base < a → a < phi → ¬(row + 3 * n ≤ a ∧ a < row + 3 * (n + s)) →
      y₃.mem a = 0 := fun a h1 h2 h3 => by
    rw [hf₃ a (by omega) h3, hm₁def, hm₂, Function.update_of_ne (by omega), hf₁ a (by omega),
      hi0 a (by omega)]
  refine ⟨y₆, (he₀.seq (he₁.seq (he₂.seq (he₃.seq (he₄.seq (he₅.seq he₆)))))).mono ?_, ?_,
    fun a ha => ?_⟩
  · rw [eI₀, hI₂]; simp only [initTime, Nat.sub_zero]; omega
  · refine stored_of_words ?_ ?_ ?_ ?_ ?_ (fun J hJ => ?_) (fun e he => ?_) (fun i hi => ?_)
      (fun k hk => absurd hk (by simp [initialPacked]))
    · change y₆.mem base = maskOf (Finset.range n)
      rw [hmemo base (by omega) (by omega), hrest₀, maskOf_range]
    · change y₆.mem (base + 1) = 0
      rw [hmemo (base + 1) (by omega) (by omega), hrestz _ (by omega) (by omega) (by omega)]
    · change y₆.mem (base + 2) = maskOf (initialState C).gates
      rw [hmem₂, maskOf_gates]; rfl
    · exact hmem₃
    · change y₆.mem (base + 4) = 0
      rw [hmemo (base + 4) (by omega) (by omega), hrestz _ (by omega) (by omega) (by omega)]
    · have hJN : J < n + s := by simpa [initialPacked, nameBound] using hJ
      have hrowJ : (initialPacked C).gateRows.getD J ⟨0, 0, 0⟩ =
          if J ∈ (initialState C).gates then rowOf ((initialState C).gate J) else ⟨0, 0, 0⟩ := by
        rw [List.getD_eq_getElem _ _ hJ]; simp [initialPacked]
      have hadd : ∀ c, (layout C).rowAddr J c = row + 3 * J + c := fun c => by
        simp only [Layout.rowAddr, layout]; omega
      rw [hadd 0, hadd 1, hadd 2, hrowJ, hmemo (row + 3 * J + 0) (by omega) (by omega),
        hmemo (row + 3 * J + 1) (by omega) (by omega), hmemo (row + 3 * J + 2) (by omega)
        (by omega)]
      rcases Nat.lt_or_ge J n with hJn | hJn
      · have hJg : J ∉ (initialState C).gates := fun h => by
          have := mem_gates_ofCircuitBinary h; omega
        simp only [hJg, ↓reduceIte]
        exact ⟨hrestz _ (by omega) (by omega) (by omega), hrestz _ (by omega) (by omega)
          (by omega), hrestz _ (by omega) (by omega) (by omega)⟩
      · obtain ⟨j, rfl⟩ : ∃ j, J = n + j := ⟨J - n, by omega⟩
        have hj : j < s := by omega
        have hro : ((outs C).getD j ⟨0, none⟩).row = if n + j ∈ (initialState C).gates then
            some (rowOf ((initialState C).gate (n + j))) else none := by
          rw [getD_outs C hj]
        obtain ⟨h0, h1, h2⟩ := rowField_getD ((outs C).getD j ⟨0, none⟩).row
        rw [hrow₃ j hj 0 (by decide), hrow₃ j hj 1 (by decide), hrow₃ j hj 2 (by decide), h0, h1,
          h2, hro]
        split_ifs <;> exact ⟨rfl, rfl, rfl⟩
    · have heE : e < 5 * n + 7 * s := by simpa [initialPacked, eqnBound] using he
      have : (layout C).eqnAddr e = row + 3 * (n + s) + e := by
        simp only [Layout.eqnAddr, layout, nameBound]; omega
      rw [this, hmemo _ (by omega) (by omega), hrestz _ (by omega) (by omega) (by omega)]
      simp [initialPacked]
    · have hin : i < n := by simpa [initialPacked] using hi
      have : (layout C).phiAddr i = phi + i := by
        simp only [Layout.phiAddr, layout, nameBound, eqnBound]; omega
      rw [this, hmemo _ (by omega) (by omega), hf₃ _ (by omega) (by omega), hm₁def, hm₂,
        Function.update_of_ne (by omega), hphi₁ i hin, List.getD_eq_getElem _ _ hi]
      simp [initialPacked]
  · have hb : (layout C).base = base := rfl
    have he : workEnd C = top + s := by rw [workEnd_eq]; omega
    rw [hb, he] at ha
    rw [hmemo a (by omega) (by omega), hf₃ a (by omega) (by omega), hm₁def, hm₂,
      Function.update_of_ne (by omega), hf₁ a (by omega)]

end Cslib.Algorithms.WordRAM.Refuter4n
