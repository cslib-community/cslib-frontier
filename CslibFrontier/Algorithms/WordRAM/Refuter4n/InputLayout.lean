/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedState
public import CslibFrontier.Computability.WordRAM.Structured
import all CslibFrontier.Computability.Circuit.Boolean.SemiCircuit.OfCircuit
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

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

/-- Classify line `j` with absorbed truth table `u` and operand literal codes `x₀, x₁`: a
function of one operand (`unaryLit`) or a binary gate `n + j`. Returns the literal code of the
line and the gate row, if any. -/
@[expose] def classify (n j u x₀ x₁ : ℕ) : ℕ × Option GateRow :=
  if (u ^^^ (u >>> 1)) &&& 5 = 0 then
    (if u &&& 1 = (u >>> 2) &&& 1 then (u &&& 1) + (u &&& 1)
      else x₀ - (x₀ &&& 1) + (u &&& 1), none)
  else if (u ^^^ (u >>> 2)) &&& 3 = 0 then
    (if u &&& 1 = (u >>> 1) &&& 1 then (u &&& 1) + (u &&& 1)
      else x₁ - (x₁ &&& 1) + (u &&& 1), none)
  else ((n + j) + (n + j) + 4, some ⟨u, x₀ >>> 1, x₁ >>> 1⟩)

/-- Decode line `j` (tag `t`, wire words `a, b`) given the literal codes `L` of the earlier lines:
its literal code and, for a genuinely binary line, the gate row of gate `n + j`. -/
@[expose] def lineOut (n j : ℕ) (L : List ℕ) (tr : ℕ × ℕ × ℕ) : ℕ × Option GateRow :=
  if tr.1 < 16 then
    classify n j (absorb tr.1 (wireLit n L tr.2.1) (wireLit n L tr.2.2)) (wireLit n L tr.2.1)
      (wireLit n L tr.2.2)
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
    simp only [lineTriple, lineOut, classify, h0, h1, lineBinaryLit, lineBinaryGate, binaryB2Cost]
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

/-! ### Validity of the encoding -/

private theorem ttOf_lt' (op : Bool → Bool → Bool) : ttOf op < 16 := by
  unfold ttOf
  have := Bool.toNat_le (op false false); have := Bool.toNat_le (op false true)
  have := Bool.toNat_le (op true false); have := Bool.toNat_le (op true true)
  omega

private theorem wireCode_lt {g : ℕ} (w : Wire n g) : wireCode w < n + g := by
  cases w with
  | input i => have := i.isLt; simp only [wireCode]; omega
  | gate k => have := k.isLt; simp only [wireCode]; omega

/-- A triple is valid at line `j`: its tag is below `18`, and a `.fn` line reads only inputs and
earlier lines. -/
private def TripleOK (n j : ℕ) (tr : ℕ × ℕ × ℕ) : Prop :=
  tr.1 < 18 ∧ (tr.1 < 16 → tr.2.1 < n + j ∧ tr.2.2 < n + j)

private theorem tripleOK_lineTriple {g : ℕ} (line : Line (fullSignature 2 Bool) n g) :
    TripleOK n g (lineTriple line) := by
  rcases line with ⟨op | c, w⟩
  · have := ttOf_lt' fun a b => op ![a, b]
    exact ⟨by simp only [lineTriple]; omega, fun _ => ⟨wireCode_lt _, wireCode_lt _⟩⟩
  · have := Bool.toNat_le c
    refine ⟨by simp only [lineTriple]; omega, fun h => ?_⟩
    simp only [lineTriple] at h
    omega

private theorem progTriples_ok : ∀ {g : ℕ} (p : Program (fullSignature 2 Bool) n g),
    (progTriples p).length = g ∧ ∀ j < g, TripleOK n j ((progTriples p).getD j (0, 0, 0))
  | _, .empty => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | _, @Program.gate _ _ g p line => by
    obtain ⟨hl, hok⟩ := progTriples_ok p
    refine ⟨by simp [progTriples, hl], fun j hj => ?_⟩
    simp only [progTriples]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact hok j hj
    · rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
      exact tripleOK_lineTriple line

/-- The `c`-th word of a triple. -/
private def tripleWord (tr : ℕ × ℕ × ℕ) : ℕ → ℕ
  | 0 => tr.1
  | 1 => tr.2.1
  | _ => tr.2.2

private theorem getD_flatMap_triple : ∀ (l : List (ℕ × ℕ × ℕ)) (j c : ℕ), j < l.length →
    c < 3 → (l.flatMap fun t => [t.1, t.2.1, t.2.2]).getD (3 * j + c) 0 =
      tripleWord (l.getD j (0, 0, 0)) c
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | t :: l, 0, c, _, hc => by
    interval_cases c <;> rfl
  | t :: l, j + 1, c, hj, hc => by
    rw [List.flatMap_cons, show 3 * (j + 1) + c = 3 * j + c + 3 by omega,
      List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel, List.getD_cons_succ]
    exact getD_flatMap_triple l j c (by simpa using hj) hc

private theorem length_flatMap_triple (l : List (ℕ × ℕ × ℕ)) :
    (l.flatMap fun t => [t.1, t.2.1, t.2.2]).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [List.flatMap_cons, ih]; omega

/-- Reads of the input memory. -/
private theorem init_encode (C : Circuit (fullSignature 2 Bool) n 1) :
    (Cslib.WordRAM.Data.init (encode C) : Cslib.WordRAM.Data 24).mem 1 = n ∧
    (Cslib.WordRAM.Data.init (encode C) : Cslib.WordRAM.Data 24).mem 2 = C.size ∧
    (∀ j < C.size, ∀ c < 3,
      (Cslib.WordRAM.Data.init (encode C) : Cslib.WordRAM.Data 24).mem (3 + 3 * j + c) =
        tripleWord ((progTriples C.program).getD j (0, 0, 0)) c) ∧
    (Cslib.WordRAM.Data.init (encode C) : Cslib.WordRAM.Data 24).mem (3 + 3 * C.size) =
      wireCode (C.outputs 0) ∧
    ∀ a, 4 + 3 * C.size ≤ a →
      (Cslib.WordRAM.Data.init (encode C) : Cslib.WordRAM.Data 24).mem a = 0 := by
  have hl := (progTriples_ok C.program).1
  have hf := length_flatMap_triple (progTriples C.program)
  rw [hl] at hf
  refine ⟨rfl, rfl, fun j hj c hc => ?_, ?_, fun a ha => ?_⟩
  · rw [show 3 + 3 * j + c = (3 * j + c + 1 + 1) + 1 by omega, Cslib.WordRAM.Data.init_mem_succ]
    simp only [encode]
    rw [List.getD_append _ _ _ _ (by simp [hf]; omega), List.getD_cons_succ, List.getD_cons_succ]
    exact getD_flatMap_triple _ j c (by rw [hl]; exact hj) hc
  · rw [show 3 + 3 * C.size = (3 * C.size + 2) + 1 by omega, Cslib.WordRAM.Data.init_mem_succ]
    simp only [encode]
    rw [List.getD_append_right _ _ _ _ (by simp [hf])]
    simp [hf]
  · rw [show a = (a - 1) + 1 by omega, Cslib.WordRAM.Data.init_mem_succ, List.getD_eq_default]
    simp only [encode, List.length_cons, List.length_append, hf, List.length_nil]
    omega

/-! ### Decoding prefixes -/

theorem decodeLines_take (l : List (ℕ × ℕ × ℕ)) (k : ℕ) :
    decodeLines n (l.take k) = (decodeLines n l).take k := by
  induction l using List.reverseRecOn generalizing k with
  | nil => cases k <;> rfl
  | append_singleton l tr ih =>
    rw [decodeLines_append_singleton]
    by_cases hk : k ≤ l.length
    · rw [List.take_append_of_le_length hk, List.take_append_of_le_length
        (by rw [length_decodeLines]; exact hk), ih]
    · rw [List.take_of_length_le (by simp; omega), List.take_of_length_le
        (by simp [length_decodeLines]; omega), decodeLines_append_singleton]

private theorem getD_decodeLines (l : List (ℕ × ℕ × ℕ)) {k : ℕ} (hk : k < l.length) :
    (decodeLines n l).getD k (0, none) = lineOut n k (((decodeLines n l).take k).map Prod.fst)
      (l.getD k (0, 0, 0)) := by
  induction l using List.reverseRecOn with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | append_singleton l tr ih =>
    have hD := length_decodeLines (n := n) l
    rw [decodeLines_append_singleton]
    rcases Nat.lt_or_ge k l.length with hkl | hkl
    · rw [List.getD_append _ _ _ _ (by omega), List.take_append_of_le_length (by omega),
        List.getD_append _ _ _ _ hkl]
      exact ih hkl
    · have hk' : k = l.length := by simp at hk; omega
      subst hk'
      rw [List.getD_append_right _ _ _ _ (by omega), List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega), List.getD_append_right _ _ _ _ le_rfl, hD]
      simp

/-! ### The decoded circuit -/

private theorem litCode_lt {ℓ : Lit} {N : ℕ} (h : ∀ t, ℓ.Reads t → t < N) :
    litCode ℓ < 2 * N + 4 := by
  obtain ⟨a, neg⟩ := ℓ
  have := Bool.toNat_le neg
  cases a with
  | const b => have := Bool.toNat_le b; simp only [litCode, argCode]; omega
  | node t => have := h t rfl; simp only [litCode, argCode]; omega

/-- The decoded lines of `C`. -/
private abbrev outs (C : Circuit (fullSignature 2 Bool) n 1) : List (ℕ × Option GateRow) :=
  decodeLines n (progTriples C.program)

private theorem getD_outs (C : Circuit (fullSignature 2 Bool) n 1) {j : ℕ} (hj : j < C.size) :
    (outs C).getD j (0, none) = (litCode (programGateLit C.program ⟨j, hj⟩),
      if n + j ∈ (initialState C).gates then
        some (rowOf ((initialState C).gate (n + j))) else none) := by
  rw [outs, decodeLines_progTriples, List.getD_eq_getElem _ _ (by simpa using hj),
    List.getElem_ofFn]
  rfl

private theorem length_outs (C : Circuit (fullSignature 2 Bool) n 1) :
    (outs C).length = C.size := by
  rw [outs, length_decodeLines, (progTriples_ok C.program).1]

private theorem code_lt (C : Circuit (fullSignature 2 Bool) n 1) {j : ℕ} (hj : j < C.size) :
    ((outs C).getD j (0, none)).1 < 2 * nameBound C + 4 := by
  rw [getD_outs C hj]
  exact litCode_lt fun t ht => (reads_programWireLit C.program (.gate ⟨j, hj⟩) ht).2

private theorem out_eq (C : Circuit (fullSignature 2 Bool) n 1) :
    litCode (initialState C).out =
      wireLit n ((outs C).map Prod.fst) (wireCode (C.outputs 0)) := by
  refine (wireLit_wireCode (programWireLit C.program) _ (fun _ => rfl) (fun k => ?_) _).symm
  rw [List.getD_eq_getElem _ _ (by simp [length_outs]), List.getElem_map]
  have := getD_outs C k.isLt
  rw [List.getD_eq_getElem _ _ (by simp [length_outs])] at this
  rw [this]
  rfl

private theorem maskOf_gates (C : Circuit (fullSignature 2 Bool) n 1) :
    maskOf (initialState C).gates = ∑ j ∈ Finset.range C.size,
      if ((outs C).getD j (0, none)).2.isSome then 2 ^ (n + j) else 0 := by
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
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [maskOf] at ih ⊢
    rw [Finset.sum_range_succ, ih, pow_succ]
    have := Nat.one_le_two_pow (n := k)
    omega

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

/-- The memory `mem` holds the packed state `P` at the addresses of `L`. -/
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
  /-- The gate rows. -/
  gateRow : ∀ J < P.gateRows.length, mem (L.rowAddr J 0) = (P.gateRows.getD J ⟨0, 0, 0⟩).tt ∧
    mem (L.rowAddr J 1) = (P.gateRows.getD J ⟨0, 0, 0⟩).left ∧
    mem (L.rowAddr J 2) = (P.gateRows.getD J ⟨0, 0, 0⟩).right
  /-- The equation words. -/
  eqnRow : ∀ e < P.eqnRows.length, mem (L.eqnAddr e) = P.eqnRows.getD e 0
  /-- The rows of the parameter map. -/
  phiRow : ∀ i < P.phiRows.length, mem (L.phiAddr i) = P.phiRows.getD i 0
  /-- The pair records. -/
  pair : ∀ k < P.pairs.length, mem (L.pairAddr k 0) = (P.pairs.getD k (0, 0)).1 ∧
    mem (L.pairAddr k 1) = (P.pairs.getD k (0, 0)).2

/-- The layout of the initial state of `C`, just past the input: base `4 + 3 C.size`,
`nameBound C` gate rows, `eqnBound C` equation words and `n` rows of the parameter map. The
program keeps one scratch word per line at `top + j`. -/
@[expose] def layout (C : Circuit (fullSignature 2 Bool) n 1) : Layout :=
  ⟨4 + 3 * C.size, nameBound C, eqnBound C, n⟩

/-- The end of the workspace of the program: the packed state and one scratch word per line. -/
@[expose] def workEnd (C : Circuit (fullSignature 2 Bool) n 1) : ℕ := (layout C).top + C.size

/-- Admitted word widths: `w ≥ n + C.size + 2` (block 1's basis, `Rep.fits`), `w ≥ 5` (the tags
`16, 17` of constant lines), and the workspace addresses fit. -/
@[expose] def FitsWidth (C : Circuit (fullSignature 2 Bool) n 1) (w : ℕ) : Prop :=
  nameBound C + 2 ≤ w ∧ 5 ≤ w ∧ Cslib.WordRAM.Fits w (workEnd C)

/-- Every width `w ≥ n + C.size + 5` is admitted. -/
theorem fitsWidth_of_le (C : Circuit (fullSignature 2 Bool) n 1) {w : ℕ}
    (hw : nameBound C + 5 ≤ w) : FitsWidth C w := by
  refine ⟨by omega, by omega, ?_⟩
  have h1 : 32 * (nameBound C + 1) ≤ 2 ^ (nameBound C + 5) := by
    rw [pow_add]; have := Nat.lt_two_pow_self (n := nameBound C); norm_num; omega
  have h2 := Nat.pow_le_pow_right (n := 2) two_pos hw
  change workEnd C < 2 ^ w
  simp only [workEnd, layout, Layout.top, nameBound, eqnBound] at h1 h2 ⊢
  omega

/-! ### The Word-RAM program -/

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

/-- The literal code of the wire word in `rX1`. -/
private def litX1 : Code .standard 24 := ram[
  if rX1 < rN then [ rX1 ← rX1 + rX1; rX1 ← rX1 + rFour ]
    else [ rX1 ← rX1 - rN; rX1 ← rX1 + rLit; rX1 ← *rX1 ] ]

private theorem exec_litX1 {w W : ℕ} (y : Data 24) (L : List ℕ) (hW : Fits w W)
    (hfour : y.regs rFour = 4) (hx : y.regs rX1 + y.regs rX1 + 4 ≤ W)
    (hl : y.regs rX1 - y.regs rN + y.regs rLit ≤ W)
    (hm : y.regs rN ≤ y.regs rX1 →
      y.mem (y.regs rX1 - y.regs rN + y.regs rLit) = L.getD (y.regs rX1 - y.regs rN) 0) :
    ∃ z, ExecWithin w litX1 y z 6 ∧ z.mem = y.mem ∧
      (∀ i : Fin 24, i ≠ rX1 → z.regs i = y.regs i) ∧
      z.regs rX1 = wireLit (y.regs rN) L (y.regs rX1) := by
  refine WP.exists_execWithin ?_
  unfold litX1
  wram_exec [hfour]
  · exact ⟨rfl, fun i hi => by wram_simp, by wram_simp; simp [wireLit, hc]⟩
  · exact ⟨rfl, fun i hi => by wram_simp, by wram_simp; simp [wireLit, hc, hm (by omega)]⟩

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
    (hcode : (y.regs rN + y.regs rI) + (y.regs rN + y.regs rI) + 4 ≤ W)
    (hg : y.regs rG + y.regs rP ≤ W)
    (hz : ∀ c < 3, y.mem (y.regs rRow + 3 * (y.regs rN + y.regs rI) + c) = 0) :
    ∃ z, ExecWithin w classBlk y z 30 ∧
      (∀ i : Fin 24, i ≠ rC → i ≠ rU → i ≠ rV → i ≠ rW → i ≠ rG → z.regs i = y.regs i) ∧
      z.regs rC = (classify (y.regs rN) (y.regs rI) (y.regs rT) (y.regs rX0) (y.regs rX1)).1 ∧
      z.regs rG = y.regs rG + (if (classify (y.regs rN) (y.regs rI) (y.regs rT) (y.regs rX0)
        (y.regs rX1)).2.isSome then y.regs rP else 0) ∧
      (∀ c < 3, z.mem (y.regs rRow + 3 * (y.regs rN + y.regs rI) + c) = rowField
        (classify (y.regs rN) (y.regs rI) (y.regs rT) (y.regs rX0) (y.regs rX1)).2 c) ∧
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

end Program

end Cslib.Algorithms.WordRAM.Refuter4n
