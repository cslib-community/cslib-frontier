/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedState
import all CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.OfCircuit
import Mathlib.Data.List.GetD

/-!
# Word layout of the input circuit of the `4n - 9d` refuter

PART 1 (pure layer, under construction).
-/

public section

namespace Cslib.Algorithms.WordRAM.Refuter4n

open Cslib.Circuits Cslib.Circuits.Boolean.AffineDisperser4n Cslib.Circuits.Boolean.SemiCircuit

variable {n : ℕ}

/-! ### The input layout -/

/-- The word of a wire: input `i ↦ i`, gate `k ↦ n + k`. -/
@[expose] def wireCode {g : ℕ} : Wire n g → ℕ
  | .input i => i
  | .gate k => n + k

/-- The three words `(tag, a, b)` of a program line: `.fn op` has the truth table `ttOf` of `op`
as tag (below `16`) and the words of its two wires; `.con c` has tag `16 + c` and `a = b = 0`. -/
@[expose] def lineTriple {g : ℕ} : Line (fullSignature 2 Bool) n g → ℕ × ℕ × ℕ
  | ⟨.fn op, w⟩ => (ttOf fun a b => op ![a, b], wireCode (w ⟨0, by simp [fullSignature]⟩),
      wireCode (w ⟨1, by simp [fullSignature]⟩))
  | ⟨.con c, _⟩ => (16 + c.toNat, 0, 0)

/-- The line triples of a program, in program order. -/
@[expose] def progTriples : {g : ℕ} → Program (fullSignature 2 Bool) n g → List (ℕ × ℕ × ℕ)
  | _, .empty => []
  | _, .gate p line => progTriples p ++ [lineTriple line]

/-- The Word-RAM input of a circuit: `[n, s]`, three words per line, the word of the output
wire. -/
@[expose] def encode (C : Circuit (fullSignature 2 Bool) n 1) : List ℕ :=
  n :: C.size :: (progTriples C.program).flatMap (fun t => [t.1, t.2.1, t.2.2]) ++
    [wireCode (C.outputs 0)]

/-! ### The decoder -/

/-- The literal code of a wire word, given the literal codes `L` of the earlier lines: input
`i ↦ litCode (node i false) = 2 i + 4`, gate `k ↦ L[k]`. -/
@[expose] def wireLit (n : ℕ) (L : List ℕ) (x : ℕ) : ℕ :=
  if x < n then x + x + 4 else L.getD (x - n) 0

/-- Swap the truth-table bits `0 ↔ 1` and `2 ↔ 3` (negate the second input). -/
@[expose] def swapLo (t : ℕ) : ℕ := ((t &&& 5) <<< 1) ||| ((t >>> 1) &&& 5)

/-- Swap the truth-table bits `0 ↔ 2` and `1 ↔ 3` (negate the first input). -/
@[expose] def swapHi (t : ℕ) : ℕ := ((t &&& 3) <<< 2) ||| ((t >>> 2) &&& 3)

/-- Absorb the negations of the operand literals `x₀, x₁` into the truth table `t`. -/
@[expose] def absorb (t x₀ x₁ : ℕ) : ℕ :=
  let t := if x₁ &&& 1 = 1 then swapLo t else t
  if x₀ &&& 1 = 1 then swapHi t else t

/-- Decode line `j` (tag `t`, wire words `a, b`) given the literal codes `L` of the earlier lines:
its literal code and, for a genuinely binary line, the gate row of gate `n + j`. -/
@[expose] def lineOut (n j : ℕ) (L : List ℕ) (tr : ℕ × ℕ × ℕ) : ℕ × Option GateRow :=
  if tr.1 < 16 then
    let x₀ := wireLit n L tr.2.1
    let x₁ := wireLit n L tr.2.2
    let u := absorb tr.1 x₀ x₁
    let u₀ := u &&& 1
    if (u ^^^ (u >>> 1)) &&& 5 = 0 then
      (if u₀ = (u >>> 2) &&& 1 then u₀ + u₀ else x₀ - (x₀ &&& 1) + u₀, none)
    else if (u ^^^ (u >>> 2)) &&& 3 = 0 then
      (if u₀ = (u >>> 1) &&& 1 then u₀ + u₀ else x₁ - (x₁ &&& 1) + u₀, none)
    else ((n + j) + (n + j) + 4, some ⟨u, x₀ >>> 1, x₁ >>> 1⟩)
  else ((tr.1 - 16) + (tr.1 - 16), none)

/-- Decode the lines in order, each reading the literal codes of the earlier ones. -/
@[expose] def decodeLines (n : ℕ) (trs : List (ℕ × ℕ × ℕ)) : List (ℕ × Option GateRow) :=
  trs.foldl (fun acc tr => acc ++ [lineOut n acc.length (acc.map Prod.fst) tr]) []

theorem decodeLines_append_singleton (l : List (ℕ × ℕ × ℕ)) (tr : ℕ × ℕ × ℕ) :
    decodeLines n (l ++ [tr]) = decodeLines n l ++
      [lineOut n (decodeLines n l).length ((decodeLines n l).map Prod.fst) tr] := by
  simp [decodeLines, List.foldl_append]

theorem length_decodeLines (l : List (ℕ × ℕ × ℕ)) : (decodeLines n l).length = l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l tr ih => simp [decodeLines_append_singleton, ih]

/-! ### Literal codes -/

private theorem litCode_and_one (ℓ : Lit) : litCode ℓ &&& 1 = ℓ.neg.toNat := by
  rw [Nat.and_one_is_mod, litCode]; cases ℓ.neg <;> simp

private theorem litCode_shiftRight (ℓ : Lit) : litCode ℓ >>> 1 = argCode ℓ.arg := by
  rw [Nat.shiftRight_eq_div_pow, litCode]; cases ℓ.neg <;> simp; omega

private theorem wireLit_wireCode {g : ℕ} (wLit : Wire n g → Lit) (L : List ℕ)
    (hin : ∀ i : Fin n, wLit (.input i) = Lit.node i false)
    (hL : ∀ k : Fin g, L.getD k 0 = litCode (wLit (.gate k))) (w : Wire n g) :
    wireLit n L (wireCode w) = litCode (wLit w) := by
  cases w with
  | input i =>
    simp only [hin, wireLit, wireCode, i.isLt, ↓reduceIte, litCode, Lit.node, argCode,
      Bool.toNat_false]
    omega
  | gate k =>
    simp [wireLit, wireCode, ← hL]

/-- **One line.** On the literal codes of the earlier lines, `lineOut` is the literal code and the
gate row that the one-pass builder of `ofCircuitBinary` assigns to the line. -/
private theorem lineOut_lineTriple {g : ℕ} (wLit : Wire n g → Lit) (L : List ℕ)
    (hin : ∀ i : Fin n, wLit (.input i) = Lit.node i false)
    (hL : ∀ k : Fin g, L.getD k 0 = litCode (wLit (.gate k)))
    (line : Line (fullSignature 2 Bool) n g) :
    lineOut n g L (lineTriple line) = (litCode (lineBinaryLit wLit line),
      if binaryB2Cost line.op = 1 then some (rowOf (lineBinaryGate wLit line)) else none) := by
  rcases line with ⟨op | c, w⟩
  · have h0 := wireLit_wireCode wLit L hin hL (w ⟨0, by simp [fullSignature]⟩)
    have h1 := wireLit_wireCode wLit L hin hL (w ⟨1, by simp [fullSignature]⟩)
    simp only [lineTriple, lineOut, h0, h1, lineBinaryLit, lineBinaryGate, binaryB2Cost]
    generalize wLit (w ⟨0, by simp [fullSignature]⟩) = l₀
    generalize wLit (w ⟨1, by simp [fullSignature]⟩) = l₁
    have ht : ttOf (fun a b => op ![a, b]) < 16 := by
      simp only [ttOf]
      have := Bool.toNat_le (op ![false, false]); have := Bool.toNat_le (op ![false, true])
      have := Bool.toNat_le (op ![true, false]); have := Bool.toNat_le (op ![true, true])
      omega
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
      simp [swapLo, swapHi, Lit.node] <;> omega
  · cases c <;> simp [lineTriple, lineOut, lineBinaryLit, binaryB2Cost, litCode, Lit.const, argCode]

/-- **Program.** Decoding the line triples of a program gives, line by line, the folded literal
code of `programGateLitVector` and the gate row of the binary gate `n + j`, if any. -/
private theorem decodeLines_progTriples : ∀ {g : ℕ} (p : Program (fullSignature 2 Bool) n g),
    decodeLines n (progTriples p) = List.ofFn fun j : Fin g =>
      (litCode (programGateLit p j),
        if n + (j : ℕ) ∈ programBinaryGates p then some (rowOf (programBinaryGate p (n + j)))
        else none)
  | _, .empty => rfl
  | _, @Program.gate _ _ g p line => by
    have ih := decodeLines_progTriples p
    have hlen : (decodeLines n (progTriples p)).length = g := by rw [ih, List.length_ofFn]
    rw [progTriples, decodeLines_append_singleton, hlen, List.ofFn_succ_last, ih]
    have hne : ∀ j : Fin g, n + (j : ℕ) ≠ n + g := fun j => by have := j.isLt; omega
    have hmem : ∀ j : Fin g, n + (j : ℕ) ∈ programBinaryGates (p.gate line) ↔
        n + (j : ℕ) ∈ programBinaryGates p := fun j => by
      simp only [programBinaryGates]
      have : (j : ℕ) ≠ g := by have := j.isLt; omega
      split_ifs <;> simp [this]
    have hlast : n + g ∈ programBinaryGates (p.gate line) ↔ binaryB2Cost line.op = 1 := by
      simp only [programBinaryGates]
      split_ifs with h
      · simp [h]
      · exact ⟨fun h' => absurd (mem_programBinaryGates_bounds h').2 (by omega),
          fun h' => absurd h' h⟩
    congr 1
    · refine List.ofFn_inj.2 (funext fun j => ?_)
      rw [Fin.val_castSucc]
      have hgl : programGateLit (p.gate line) j.castSucc = programGateLit p j :=
        Vector.getElem_push_lt j.isLt
      simp only [hgl, hmem j, programBinaryGate, hne j, ↓reduceIte]
    · rw [lineOut_lineTriple (programWireLit p) _ (fun _ => rfl) (fun k => by
          rw [List.getD_eq_getElem _ _ (by simp)]
          simp [programWireLit])]
      have hgl : programGateLit (p.gate line) (Fin.last g) =
          lineBinaryLit (programWireLit p) line :=
        programWireLit_gate_last p line
      simp only [Fin.val_last, hgl, hlast, programBinaryGate, ↓reduceIte]

end Cslib.Algorithms.WordRAM.Refuter4n
