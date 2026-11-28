/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CYK.Basic
public import CslibFrontier.Computability.WordRAM.Function
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Word-RAM Cocke–Younger–Kasami parsing

Checked Word-RAM implementation and `O((|R| + 1)(|w| + 1)³)` running-time bound (with constant
`21`-instruction handling of the empty word) for the Cocke–Younger–Kasami membership algorithm of
`CslibFrontier.Algorithms.Lean.CYK.Basic` on grammars in Chomsky normal form.

An encoded instance (`CYKInstance`) presents a Chomsky normal form grammar over nonterminals
`Fin numNTs` and natural-number terminals `ℕ`, together with an input word `word : List ℕ`. In
`State.init I.encode`, the header `[numNTs, initial, nilRule, |R|, |w|]` is followed by `4 |R|`
words encoding the rules (`[0, A, a, 0]` for `leaf A a` and `[1, A, B, C]` for `node A B C`) and
`|w|` terminal words. Above the input (`dpBase = I.encode.length + 1`), all memory cells are `0` in
`State.init`; the program maintains an `n × n × numNTs` Boolean membership table at
`dpBase + ((l - 1) * n + i) * numNTs + A`, scanning all `|R|` rules for each of the `n` length-one
subwords and each of the `C(n + 1, 3)` pairs `(i, l, k)` of a longer subword and split point.

## Main definitions

* `Cslib.Algorithms.WordRAM.CYK.encodeRule`: four-word encoding of a Chomsky normal form rule.
* `Cslib.Algorithms.WordRAM.CYK.CYKInstance`: a Chomsky normal form grammar over `Fin numNTs` and
  `ℕ` paired with an input word, its word layout `CYKInstance.encode`, its time bound
  `CYKInstance.timeBound`, and its word-width condition `CYKInstance.FitsWidth`.
* `Cslib.Algorithms.WordRAM.CYK.cykProgram`: fixed `Program .standard 24` deciding membership in
  `I.grammar.toCFG.language`.

## Main results

* `Cslib.Algorithms.WordRAM.CYK.computesInTime_cyk`: `cykProgram` computes
  `(cyk I.grammar I.word).toNat` within `I.timeBound` instructions (`21` on `[]`, and
  `42 (|R| + 1) |w|³` on nonempty words) at every fitting width.
* `Cslib.Algorithms.WordRAM.CYK.decidesInTime_cyk`: `cykProgram` decides
  `{I | I.word ∈ I.grammar.toCFG.language}` within `I.timeBound` instructions at every fitting
  width.
* `Cslib.Algorithms.WordRAM.CYK.uniformDecidableInTime_cyk`: uniform Word-RAM decidability of
  `{I | I.word ∈ I.grammar.toCFG.language}` in `42 (|R| + 1) (|w| + 1)³` instructions, bundling
  width admissibility (`CYKInstance.inputAdmissible`).

## References

* [T. Kasami, *An efficient recognition and syntax-analysis algorithm for context-free
  languages*][Kasami1965]
* [D. H. Younger, *Recognition and parsing of context-free languages in time n³*][Younger1967]
* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages,
  and Computation*][Hopcroft2006]
-/

public section

namespace Cslib.Algorithms.WordRAM.CYK

open Cslib.Algorithms.Lean.CYK
open Cslib.WordRAM
open Cslib.ChomskyNormalFormGrammar Cslib.ChomskyNormalFormRule

/-! ## Problem instances and flat word encoding -/

/-- Four-word encoding of a Chomsky normal form rule over terminals `ℕ` and nonterminals `Fin V`:
`[0, A, a, 0]` for `leaf A a` and `[1, A, B, C]` for `node A B C`. -/
@[expose] def encodeRule {V : ℕ} : ChomskyNormalFormRule ℕ (Fin V) → List ℕ
  | .leaf A a => [0, A.val, a, 0]
  | .node A B C => [1, A.val, B.val, C.val]

@[simp]
private theorem length_encodeRule {V : ℕ} (r : ChomskyNormalFormRule ℕ (Fin V)) :
    (encodeRule r).length = 4 := by
  cases r <;> rfl

private theorem flatMap_encodeRule_length {V : ℕ}
    (rs : List (ChomskyNormalFormRule ℕ (Fin V))) :
    (rs.flatMap encodeRule).length = 4 * rs.length := by
  simp only [List.length_flatMap, length_encodeRule, List.map_const', List.sum_replicate,
    Nat.nsmul_eq_mul]
  omega

/-- An encoded Chomsky normal form membership instance for the Word-RAM: nonterminals
`Fin numNTs`, natural-number terminal words, a rule list satisfying the standard `nilRule`
invariant, and an input word `word : List ℕ`. -/
structure CYKInstance where
  /-- Number of nonterminals `|V|`. -/
  numNTs : ℕ
  /-- Start symbol `S ∈ Fin numNTs`. -/
  initial : Fin numNTs
  /-- Rules `A → a` (`leaf A a`) and `A → B C` (`node A B C`). -/
  rules : List (ChomskyNormalFormRule ℕ (Fin numNTs))
  /-- Whether the grammar includes `initial → ε`. -/
  nilRule : Bool
  /-- When `nilRule = true`, `initial` occurs on no right-hand side. -/
  initial_notMem_output :
    nilRule = true → ∀ r ∈ rules, Symbol.nonterminal initial ∉ r.output
  /-- Input word over `ℕ`. -/
  word : List ℕ

namespace CYKInstance

/-- View `I` as a `ChomskyNormalFormGrammar ℕ`. -/
abbrev grammar (I : CYKInstance) : ChomskyNormalFormGrammar ℕ where
  NT := Fin I.numNTs
  initial := I.initial
  rules := I.rules
  nilRule := I.nilRule
  initial_notMem_output := I.initial_notMem_output

/-- Concatenated 4-word encodings of `I.rules`. -/
@[expose] def encodeRules (I : CYKInstance) : List ℕ :=
  I.rules.flatMap encodeRule

/-- Word-RAM input layout `[numNTs, initial, nilRule, |rules|, |word|] ++ encodeRules ++ word`. -/
@[expose] def encode (I : CYKInstance) : List ℕ :=
  [I.numNTs, I.initial.val, I.nilRule.toNat, I.rules.length, I.word.length] ++
    I.encodeRules ++ I.word

@[simp]
theorem length_encodeRules (I : CYKInstance) : I.encodeRules.length = 4 * I.rules.length :=
  flatMap_encodeRule_length I.rules

@[simp]
theorem length_encode (I : CYKInstance) :
    I.encode.length = 5 + 4 * I.rules.length + I.word.length := by
  simp [encode]
  omega

/-- Word-width condition for `CYKInstance`: input addresses and the `|w| × |w| × numNTs` Boolean
CYK table fit in `w` bits. -/
abbrev FitsWidth (I : CYKInstance) (w : ℕ) : Prop :=
  Fits w (I.encode.length + I.word.length * I.word.length * I.numNTs + 6)

/-- Every `CYKInstance` admits a fitting word width. -/
theorem inputAdmissible : InputAdmissible (fun _ => encode) FitsWidth := by
  intro I
  obtain ⟨w, hw, hfit⟩ := InputFits.exists_width I.encode
    (I.encode.length + I.word.length * I.word.length * I.numNTs + 6)
  exact ⟨w, (fits_self _).mono hw, hfit⟩

/-- Step budget of `cykProgram` on `I`: `21` instructions on the empty word and
`42 (|R| + 1) |w|³` instructions on nonempty words. -/
@[expose] def timeBound (I : CYKInstance) : ℕ :=
  if I.word = [] then 21 else 42 * (I.rules.length + 1) * I.word.length ^ 3

/-- Uniform cubic upper bound across both empty and nonempty words. -/
theorem timeBound_le (I : CYKInstance) :
    I.timeBound ≤ 42 * (I.rules.length + 1) * (I.word.length + 1) ^ 3 := by
  unfold timeBound
  split_ifs with hw
  · rw [hw]
    simp only [List.length_nil, zero_add, one_pow, mul_one]
    omega
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) 3)

end CYKInstance

/-! ## Register layout and structured CYK program -/

-- Read-only registers initialized by `cykSetup`: 0..9
private abbrev regV : Fin 24 := 0
private abbrev regInit : Fin 24 := 1
private abbrev regNil : Fin 24 := 2
private abbrev regR : Fin 24 := 3
private abbrev regN : Fin 24 := 4
private abbrev regRulesBase : Fin 24 := 5
private abbrev regWordBase : Fin 24 := 6
private abbrev regDPBase : Fin 24 := 7
private abbrev regOne : Fin 24 := 8
private abbrev regFour : Fin 24 := 9
-- Loop counters and cell pointers: 10..18
private abbrev regD : Fin 24 := 10
private abbrev regILim : Fin 24 := 11
private abbrev regI : Fin 24 := 12
private abbrev regCurBase : Fin 24 := 13
private abbrev regWi : Fin 24 := 14
private abbrev regK : Fin 24 := 15
private abbrev regLeftBase : Fin 24 := 16
private abbrev regRightBase : Fin 24 := 17
private abbrev regRIdx : Fin 24 := 18
-- Rule fields, answer register (`regTag`), and scratch registers: 19..23
private abbrev regRPtr : Fin 24 := 19
private abbrev regTag : Fin 24 := 20
private abbrev regLHS : Fin 24 := 21
private abbrev regArg1 : Fin 24 := 22
private abbrev regArg2 : Fin 24 := 23

private def cykSetup : Code .standard 24 :=
  ram[
    regOne ← #1;
    regFour ← #4;
    regArg2 ← #1; regV ← *regArg2;
    regArg2 ← #2; regInit ← *regArg2;
    regArg2 ← #3; regNil ← *regArg2;
    regArg2 ← #4; regR ← *regArg2;
    regArg2 ← #5; regN ← *regArg2;
    regRulesBase ← #6;
    regArg2 ← regFour * regR;
    regWordBase ← regRulesBase + regArg2;
    regDPBase ← regWordBase + regN;
    regTag ← #0 ]

private def leafPre : Code .standard 24 :=
  ram[
    regArg2 ← regWordBase + regI;
    regWi ← *regArg2;
    regArg2 ← regI * regV;
    regCurBase ← regDPBase + regArg2;
    regRIdx ← #0 ]

private def leafRuleLoad : Code .standard 24 :=
  ram[
    regRPtr ← regFour * regRIdx;
    regRPtr ← regRulesBase + regRPtr;
    regTag ← *regRPtr;
    regRPtr ← regRPtr + regOne;
    regLHS ← *regRPtr;
    regRPtr ← regRPtr + regOne;
    regArg1 ← *regRPtr;
    regArg2 ← #0 ]

private def leafRuleBody : Code .standard 24 :=
  .seq leafRuleLoad
    (.seq
      (.branch (.eq regTag regArg2)
        (.branch (.eq regWi regArg1)
          (ram[ regArg2 ← regCurBase + regLHS; *regArg2 ← regOne ])
          (ram[ regArg2 ← regArg2 ]))
        (ram[ regArg2 ← regArg2 ]))
      (ram[ regRIdx ← regRIdx + regOne ]))

private def leafCellBody : Code .standard 24 :=
  .seq leafPre
    (.seq (.loop (.lt regRIdx regR) leafRuleBody)
      (ram[ regI ← regI + regOne ]))

private def nodeCellPre : Code .standard 24 :=
  ram[
    regArg2 ← regD * regN;
    regArg2 ← regArg2 + regI;
    regArg2 ← regArg2 * regV;
    regCurBase ← regDPBase + regArg2;
    regK ← #0 ]

private def nodeSplitPre : Code .standard 24 :=
  ram[
    regArg2 ← regK * regN;
    regArg2 ← regArg2 + regI;
    regArg2 ← regArg2 * regV;
    regLeftBase ← regDPBase + regArg2;
    regArg1 ← regD - regOne;
    regArg1 ← regArg1 - regK;
    regArg1 ← regArg1 * regN;
    regArg2 ← regI + regK;
    regArg2 ← regArg2 + regOne;
    regArg1 ← regArg1 + regArg2;
    regArg1 ← regArg1 * regV;
    regRightBase ← regDPBase + regArg1;
    regRIdx ← #0 ]

private def nodeRuleLoad : Code .standard 24 :=
  ram[
    regRPtr ← regFour * regRIdx;
    regRPtr ← regRulesBase + regRPtr;
    regTag ← *regRPtr;
    regRPtr ← regRPtr + regOne;
    regLHS ← *regRPtr;
    regRPtr ← regRPtr + regOne;
    regArg1 ← *regRPtr;
    regRPtr ← regRPtr + regOne;
    regArg2 ← *regRPtr ]

private def nodeSubcellLoads : Code .standard 24 :=
  ram[
    regArg1 ← regLeftBase + regArg1;
    regArg1 ← *regArg1;
    regArg2 ← regRightBase + regArg2;
    regArg2 ← *regArg2 ]

private def nodeRuleBody : Code .standard 24 :=
  .seq nodeRuleLoad
    (.seq
      (.branch (.eq regTag regOne)
        (.seq nodeSubcellLoads
          (.branch (.eq regArg1 regOne)
            (.branch (.eq regArg2 regOne)
              (ram[ regArg2 ← regCurBase + regLHS; *regArg2 ← regOne ])
              (ram[ regArg2 ← regArg2 ]))
            (ram[ regArg2 ← regArg2 ])))
        (ram[ regArg2 ← regArg2 ]))
      (ram[ regRIdx ← regRIdx + regOne ]))

private def nodeSplitBody : Code .standard 24 :=
  .seq nodeSplitPre
    (.seq (.loop (.lt regRIdx regR) nodeRuleBody)
      (ram[ regK ← regK + regOne ]))

private def nodeCellBody : Code .standard 24 :=
  .seq nodeCellPre
    (.seq (.loop (.lt regK regD) nodeSplitBody)
      (ram[ regI ← regI + regOne ]))

private def nodeLevelBody : Code .standard 24 :=
  .seq (ram[ regILim ← regN - regD; regI ← #0 ])
    (.seq (.loop (.lt regI regILim) nodeCellBody)
      (ram[ regD ← regD + regOne ]))

private def cykFinalRead : Code .standard 24 :=
  ram[
    regArg2 ← regN - regOne;
    regArg2 ← regArg2 * regN;
    regArg2 ← regArg2 * regV;
    regArg2 ← regDPBase + regArg2;
    regArg2 ← regArg2 + regInit;
    regTag ← *regArg2 ]

private def cykNonempty : Code .standard 24 :=
  .seq (.seq (ram[ regI ← #0 ]) (.loop (.lt regI regN) leafCellBody))
    (.seq (.seq (ram[ regD ← #1 ]) (.loop (.lt regD regN) nodeLevelBody))
      cykFinalRead)

private def cykCode : Code .standard 24 :=
  .seq cykSetup
    (.branch (.lt regTag regN)
      cykNonempty
      (ram[ regTag ← regNil ]))

/-- Fixed standard-basis Word-RAM program computing `(cyk I.grammar I.word).toNat` and deciding
`I.word ∈ I.grammar.toCFG.language`. -/
def cykProgram : Program .standard 24 :=
  cykCode.program regTag

/-! ## Input-slice and table-address helpers -/

private theorem init_mem_above (input : List ℕ) {addr : ℕ} (h : input.length + 1 ≤ addr) :
    (Data.init input : Data 24).mem addr = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, addr = k + 1 := ⟨addr - 1, by omega⟩
  rw [Data.init_mem_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

private theorem flatMap_encodeRule_getElem {V : ℕ} (rs : List (ChomskyNormalFormRule ℕ (Fin V)))
    {idx off : ℕ} (hidx : idx < rs.length) (hoff : off < 4) :
    (rs.flatMap encodeRule)[4 * idx + off]'(by rw [flatMap_encodeRule_length]; omega) =
      (encodeRule rs[idx])[off]'(by simp [hoff]) := by
  have h := List.getElem?_flatMap_mul_add rs encodeRule 4
    (fun r _ => length_encodeRule r) hidx hoff
  rw [Nat.mul_comm idx 4, List.getElem?_eq_getElem (by rw [flatMap_encodeRule_length]; omega),
    List.getElem?_eq_getElem (by simpa using hoff)] at h
  exact Option.some.inj h

private theorem cyk_read_rule (I : CYKInstance) {idx off : ℕ} (hidx : idx < I.rules.length)
    (hoff : off < 4) :
    (Data.init I.encode : Data 24).mem (6 + 4 * idx + off) =
      (encodeRule I.rules[idx])[off]'(by cases I.rules[idx] <;> simp [encodeRule] <;> omega) := by
  have hlt : 4 * idx + off < I.encodeRules.length := by rw [I.length_encodeRules]; omega
  have h := Data.init_realizes_append (r := 24)
    [I.numNTs, I.initial.val, I.nilRule.toNat, I.rules.length, I.word.length]
    I.encodeRules I.word ⟨4 * idx + off, hlt⟩
  change (Data.init ([I.numNTs, I.initial.val, I.nilRule.toNat, I.rules.length, I.word.length] ++
      (I.encodeRules ++ I.word)) : Data 24).mem (5 + 1 + (4 * idx + off)) =
    I.encodeRules[4 * idx + off] at h
  rw [← List.append_assoc, show 5 + 1 + (4 * idx + off) = 6 + 4 * idx + off by omega] at h
  exact h.trans (flatMap_encodeRule_getElem I.rules hidx hoff)

private theorem cyk_read_word (I : CYKInstance) {i : ℕ} (hi : i < I.word.length) :
    (Data.init I.encode : Data 24).mem (6 + 4 * I.rules.length + i) = I.word[i] := by
  have h := Data.init_realizes_append (r := 24)
    ([I.numNTs, I.initial.val, I.nilRule.toNat, I.rules.length, I.word.length] ++ I.encodeRules)
    I.word [] ⟨i, hi⟩
  change (Data.init (([I.numNTs, I.initial.val, I.nilRule.toNat, I.rules.length, I.word.length] ++
      I.encodeRules) ++ (I.word ++ [])) : Data 24).mem
    (([I.numNTs, I.initial.val, I.nilRule.toNat, I.rules.length, I.word.length] ++
      I.encodeRules).length + 1 + i) = I.word[i] at h
  have haddr : ([I.numNTs, I.initial.val, I.nilRule.toNat, I.rules.length, I.word.length] ++
      I.encodeRules).length + 1 + i = 6 + 4 * I.rules.length + i := by simp; omega
  rw [List.append_nil, haddr] at h
  exact h

/-- Base address of cell `(i, d + 1)` (`0 ≤ d < |w|`, `0 ≤ i < |w| - d`) in the Boolean DP
table. -/
private def cellBase (I : CYKInstance) (d i : ℕ) : ℕ :=
  I.encode.length + 1 + (d * I.word.length + i) * I.numNTs

private theorem cellAddr_lt_next (I : CYKInstance) (d i : ℕ) (A : Fin I.numNTs) :
    cellBase I d i + A.val <
      I.encode.length + 1 + (d * I.word.length + i + 1) * I.numNTs := by
  have hA : A.val < I.numNTs := A.isLt
  dsimp only [cellBase]
  nlinarith

private theorem dpBase_lt_cellAddr (I : CYKInstance) (d i : ℕ) (A : Fin I.numNTs)
    {addr : ℕ} (h : addr < I.encode.length + 1) : addr < cellBase I d i + A.val := by
  dsimp only [cellBase]
  omega

private theorem next_le_cellBase_of_lt (I : CYKInstance) {d' i' d i : ℕ}
    (hi' : i' < I.word.length) (hlt : d' < d ∨ (d' = d ∧ i' < i)) :
    I.encode.length + 1 + (d' * I.word.length + i' + 1) * I.numNTs ≤ cellBase I d i := by
  dsimp only [cellBase]
  have hidx : d' * I.word.length + i' + 1 ≤ d * I.word.length + i := by
    rcases hlt with hd | ⟨rfl, hi⟩
    · have hd1 : d' + 1 ≤ d := hd
      nlinarith
    · omega
  have hmul := Nat.mul_le_mul_right I.numNTs hidx
  omega

private theorem cellAddr_ne_of_lt (I : CYKInstance) {d' i' d i : ℕ}
    (hi' : i' < I.word.length) (hlt : d' < d ∨ (d' = d ∧ i' < i))
    (A' A : Fin I.numNTs) : cellBase I d' i' + A'.val ≠ cellBase I d i + A.val := by
  have h1 := cellAddr_lt_next I d' i' A'
  have h2 := next_le_cellBase_of_lt I hi' hlt
  omega

private theorem le_tableBound_of_lt (I : CYKInstance) (d i : ℕ)
    (hd : d < I.word.length) (hi : i < I.word.length) :
    d * I.word.length ≤ I.word.length * I.word.length * I.numNTs ∧
    d * I.word.length + i ≤ I.word.length * I.word.length * I.numNTs ∧
    (d * I.word.length + i) * I.numNTs + I.numNTs ≤
      I.word.length * I.word.length * I.numNTs := by
  have hV : 1 ≤ I.numNTs := Nat.pos_of_ne_zero fun h => Fin.elim0 (h ▸ I.initial)
  have hmul : (d * I.word.length + i + 1) * I.numNTs ≤
      I.word.length * I.word.length * I.numNTs :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have h1 : d * I.word.length + i ≤ (d * I.word.length + i) * I.numNTs :=
    Nat.le_mul_of_pos_right _ hV
  rw [Nat.add_one_mul] at hmul
  exact ⟨by omega, by omega, by omega⟩

private theorem cellBase_add_le_tableEnd (I : CYKInstance) (d i : ℕ)
    (hd : d < I.word.length) (hi : i < I.word.length) :
    cellBase I d i + I.numNTs ≤
      I.encode.length + 1 + I.word.length * I.word.length * I.numNTs := by
  have ⟨_, _, h3⟩ := le_tableBound_of_lt I d i hd hi
  dsimp only [cellBase]
  omega

/-! ## Setup and invariant predicates -/

private structure FixedRegs (I : CYKInstance) (st : Data 24) : Prop where
  v : st.regs regV = I.numNTs
  init : st.regs regInit = I.initial.val
  nil : st.regs regNil = I.nilRule.toNat
  r : st.regs regR = I.rules.length
  n : st.regs regN = I.word.length
  rulesBase : st.regs regRulesBase = 6
  wordBase : st.regs regWordBase = 6 + 4 * I.rules.length
  dpBase : st.regs regDPBase = I.encode.length + 1
  one : st.regs regOne = 1
  four : st.regs regFour = 4

private theorem exec_cykSetup {w : ℕ} (I : CYKInstance) (hw : I.FitsWidth w) :
    ∃ x₀, ExecWithin w cykSetup (.init I.encode) x₀ 17 ∧
      x₀.mem = (Data.init I.encode : Data 24).mem ∧
      FixedRegs I x₀ ∧
      x₀.regs regTag = 0 := by
  have hlen := I.length_encode
  have hm1 : (Data.init I.encode : Data 24).mem 1 = I.numNTs := by simp [CYKInstance.encode]
  have hm2 : (Data.init I.encode : Data 24).mem 2 = I.initial.val := by simp [CYKInstance.encode]
  have hm3 : (Data.init I.encode : Data 24).mem 3 = I.nilRule.toNat := by simp [CYKInstance.encode]
  have hm4 : (Data.init I.encode : Data 24).mem 4 = I.rules.length := by simp [CYKInstance.encode]
  have hm5 : (Data.init I.encode : Data 24).mem 5 = I.word.length := by simp [CYKInstance.encode]
  wram_exec * [cykSetup]
  · refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals wram_simp *
    omega
  all_goals exact hw.of_le (by omega)

/-- Memory invariant at the boundary before filling cell `(d, i)` (`0 ≤ d ≤ |w|`,
`0 ≤ i ≤ |w| - d`): input memory is intact, all earlier cells `(d', i')` hold exact `0/1`
membership for `table I.grammar I.word (d' + 1) i' (d' + 1)`, and all addresses from
`cellBase I d i` upward are `0`. -/
private def CellBoundaryMem (I : CYKInstance) (d i : ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ addr < I.encode.length + 1, mem addr = (Data.init I.encode : Data 24).mem addr) ∧
  (∀ d' < d, ∀ i' < I.word.length - d', ∀ A : Fin I.numNTs,
    mem (cellBase I d' i' + A.val) =
      (decide (A ∈ table I.grammar I.word (d' + 1) i' (d' + 1))).toNat) ∧
  (∀ i' < i, ∀ A : Fin I.numNTs,
    mem (cellBase I d i' + A.val) =
      (decide (A ∈ table I.grammar I.word (d + 1) i' (d + 1))).toNat) ∧
  (∀ addr, cellBase I d i ≤ addr → mem addr = 0)

/-- Memory invariant while filling cell `(d, i)` with current predicate `P : Fin I.numNTs → Prop`
on its `numNTs` slots. -/
private def ActiveCellMem (I : CYKInstance) (d i : ℕ) (P : Fin I.numNTs → Prop)
    [DecidablePred P] (mem : ℕ → ℕ) : Prop :=
  (∀ addr < I.encode.length + 1, mem addr = (Data.init I.encode : Data 24).mem addr) ∧
  (∀ d' < d, ∀ i' < I.word.length - d', ∀ A : Fin I.numNTs,
    mem (cellBase I d' i' + A.val) =
      (decide (A ∈ table I.grammar I.word (d' + 1) i' (d' + 1))).toNat) ∧
  (∀ i' < i, ∀ A : Fin I.numNTs,
    mem (cellBase I d i' + A.val) =
      (decide (A ∈ table I.grammar I.word (d + 1) i' (d + 1))).toNat) ∧
  (∀ A : Fin I.numNTs, mem (cellBase I d i + A.val) = (decide (P A)).toNat) ∧
  (∀ addr, I.encode.length + 1 + (d * I.word.length + i + 1) * I.numNTs ≤ addr → mem addr = 0)

private theorem activeCellMem_start (I : CYKInstance) (d i : ℕ) {mem : ℕ → ℕ}
    (hb : CellBoundaryMem I d i mem) :
    ActiveCellMem I d i (fun _ => False) mem := by
  refine ⟨hb.1, hb.2.1, hb.2.2.1, fun A => ?_, fun addr haddr => ?_⟩
  · simp only [decide_false, Bool.toNat_false]
    exact hb.2.2.2 _ (by dsimp only [cellBase]; omega)
  · exact hb.2.2.2 _ (by dsimp only [cellBase]; nlinarith)

private theorem activeCellMem_read_rule (I : CYKInstance) {d i rIdx : ℕ}
    {P : Fin I.numNTs → Prop} [DecidablePred P] {mem : ℕ → ℕ}
    (hmem : ActiveCellMem I d i P mem) (hrIdx : rIdx < I.rules.length) :
    mem (6 + 4 * rIdx) = (encodeRule I.rules[rIdx])[0]'(by simp) ∧
      mem (6 + 4 * rIdx + 1) = (encodeRule I.rules[rIdx])[1]'(by simp) ∧
      mem (6 + 4 * rIdx + 1 + 1) = (encodeRule I.rules[rIdx])[2]'(by simp) ∧
      mem (6 + 4 * rIdx + 1 + 1 + 1) = (encodeRule I.rules[rIdx])[3]'(by simp) := by
  have hlen := I.length_encode
  have h (off : ℕ) (hoff : off < 4) :
      mem (6 + 4 * rIdx + off) = (encodeRule I.rules[rIdx])[off]'(by simp [hoff]) :=
    (hmem.1 (6 + 4 * rIdx + off) (by omega)).trans (cyk_read_rule I hrIdx hoff)
  refine ⟨by simpa only [Nat.add_zero] using h 0 (by decide), h 1 (by decide), ?_, ?_⟩
  · rw [show 6 + 4 * rIdx + 1 + 1 = 6 + 4 * rIdx + 2 by omega]; exact h 2 (by decide)
  · rw [show 6 + 4 * rIdx + 1 + 1 + 1 = 6 + 4 * rIdx + 3 by omega]; exact h 3 (by decide)

private theorem activeCellMem_write_one (I : CYKInstance) {d i : ℕ} (hi : i < I.word.length)
    (P Q : Fin I.numNTs → Prop) [DecidablePred P] [DecidablePred Q]
    (A₀ : Fin I.numNTs) (hQ : ∀ A, Q A ↔ P A ∨ A = A₀) {mem : ℕ → ℕ}
    (hm : ActiveCellMem I d i P mem) :
    ActiveCellMem I d i Q (Function.update mem (cellBase I d i + A₀.val) 1) := by
  refine ⟨fun addr hlt => ?_, fun d' hd' i' hi' A => ?_, fun i' hi' A => ?_, fun A => ?_,
    fun addr hge => ?_⟩
  · rw [Function.update_of_ne (Nat.ne_of_lt (dpBase_lt_cellAddr I d i A₀ hlt))]
    exact hm.1 addr hlt
  · rw [Function.update_of_ne
      (cellAddr_ne_of_lt I (by omega) (Or.inl hd') A A₀)]
    exact hm.2.1 d' hd' i' hi' A
  · rw [Function.update_of_ne
      (cellAddr_ne_of_lt I (by omega) (Or.inr ⟨rfl, hi'⟩) A A₀)]
    exact hm.2.2.1 i' hi' A
  · rcases eq_or_ne A A₀ with rfl | hne
    · have hQA : Q A := (hQ A).2 (Or.inr rfl)
      rw [Function.update_self, decide_eq_true hQA, Bool.toNat_true]
    · have hne_addr : cellBase I d i + A.val ≠ cellBase I d i + A₀.val := by
        intro heq
        exact hne (Fin.ext (by omega))
      have hQP : Q A ↔ P A := (hQ A).trans (or_iff_left hne)
      rw [Function.update_of_ne hne_addr, hm.2.2.2.1 A, decide_eq_decide.2 hQP]
  · have hlt := cellAddr_lt_next I d i A₀
    rw [Function.update_of_ne (by omega)]
    exact hm.2.2.2.2 addr hge

private theorem activeCellMem_congr (I : CYKInstance) (d i : ℕ)
    (P Q : Fin I.numNTs → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ A, P A ↔ Q A) {mem : ℕ → ℕ} (hm : ActiveCellMem I d i P mem) :
    ActiveCellMem I d i Q mem :=
  ⟨hm.1, hm.2.1, hm.2.2.1,
    fun A => (hm.2.2.2.1 A).trans (by rw [decide_eq_decide.2 (hPQ A)]), hm.2.2.2.2⟩

private theorem cellBoundaryMem_finish_cell (I : CYKInstance) {d i : ℕ}
    (P : Fin I.numNTs → Prop) [DecidablePred P]
    (hP : ∀ A, P A ↔ A ∈ table I.grammar I.word (d + 1) i (d + 1))
    {mem : ℕ → ℕ} (hm : ActiveCellMem I d i P mem) :
    CellBoundaryMem I d (i + 1) mem := by
  refine ⟨hm.1, hm.2.1, fun i' hi' A => ?_, fun addr haddr => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
    · exact hm.2.2.1 i' hlt A
    · exact (hm.2.2.2.1 A).trans (by rw [decide_eq_decide.2 (hP A)])
  · exact hm.2.2.2.2 addr (by dsimp only [cellBase] at haddr; omega)

private theorem cellBoundaryMem_next_level (I : CYKInstance) (d : ℕ) {mem : ℕ → ℕ}
    (hb : CellBoundaryMem I d (I.word.length - d) mem) :
    CellBoundaryMem I (d + 1) 0 mem := by
  refine ⟨hb.1, fun d' hd' i' hi' A => ?_, fun _ hi' => absurd hi' (Nat.not_lt_zero _),
    fun addr haddr => hb.2.2.2 addr ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hd' with hlt | rfl
    · exact hb.2.1 d' hlt i' hi' A
    · exact hb.2.2.1 i' hi' A
  · dsimp only [cellBase] at haddr ⊢
    have hidx : d * I.word.length + (I.word.length - d) ≤ (d + 1) * I.word.length + 0 := by
      have : I.word.length - d ≤ I.word.length := Nat.sub_le _ _
      nlinarith
    have hmul := Nat.mul_le_mul_right I.numNTs hidx
    omega

/-! ## Execution of a counted loop followed by a counter increment -/

/-- Execute `.loop (.lt rInner rInnerLim) body` from counter `0` to `lim`, followed by
incrementing an outer register `rOuter` holding `outerVal` via `regOne`. -/
private theorem exec_loopZero_then_inc {w : ℕ} {rInner rInnerLim rOuter : Fin 24}
    {body : Code .standard 24} {tb lim outerVal : ℕ}
    (P : ℕ → Data 24 → Prop) {p1 : Data 24}
    (hlim : ∀ q, P (q.regs rInner) q → q.regs rInnerLim = lim)
    (hbody : ∀ q, P (q.regs rInner) q → q.regs rInner < lim →
      ∃ q', ExecWithin w body q q' tb ∧ P (q.regs rInner + 1) q' ∧
        q'.regs rInner = q.regs rInner + 1)
    (hp1_zero : p1.regs rInner = 0)
    (hp1 : P 0 p1)
    (houter : ∀ q, P lim q → q.regs rOuter = outerVal ∧ q.regs regOne = 1)
    (hf_inc : Fits w (outerVal + 1)) :
    ∃ p3, ExecWithin w (.seq (.loop (.lt rInner rInnerLim) body)
        (ram[ rOuter ← rOuter + regOne ])) p1 p3 (lim * (tb + 2) + 3) ∧
      (∃ p2, P lim p2 ∧ p3 = p2.set rOuter (outerVal + 1)) := by
  have hp1' : P (p1.regs rInner) p1 := hp1_zero.symm ▸ hp1
  have hle0 : p1.regs rInner ≤ lim := hp1_zero.symm ▸ Nat.zero_le lim
  obtain ⟨p2, hloop, hp2, _⟩ := ExecWithin.loop_count P hlim hbody hle0 hp1'
  rw [hp1_zero, Nat.sub_zero] at hloop
  obtain ⟨hp2_out, hp2_one⟩ := houter p2 hp2
  have hinc : ExecWithin w (ram[ rOuter ← rOuter + regOne ]) p2 (p2.set rOuter (outerVal + 1)) 1 :=
    by wram_exec [hp2_out, hp2_one, hf_inc]
  exact ⟨p2.set rOuter (outerVal + 1), (hloop.seq hinc).mono (by omega), p2, hp2, rfl⟩

/-! ## Execution of the leaf level (`d = 0`) -/

private def LeafAccProp (I : CYKInstance) (wi rIdx : ℕ) (A : Fin I.numNTs) : Prop :=
  ∃ idx < rIdx, ∃ h : idx < I.rules.length, I.rules[idx] = .leaf A wi

private instance (I : CYKInstance) (wi rIdx : ℕ) : DecidablePred (LeafAccProp I wi rIdx) := by
  unfold LeafAccProp
  infer_instance

private theorem leafAccProp_step_none (I : CYKInstance) {wi rIdx : ℕ}
    (hrIdx : rIdx < I.rules.length) (hnone : ∀ A, I.rules[rIdx] ≠ .leaf A wi) (A : Fin I.numNTs) :
    LeafAccProp I wi rIdx A ↔ LeafAccProp I wi (rIdx + 1) A :=
  ⟨fun ⟨idx, hlt, hidx, heq⟩ => ⟨idx, Nat.lt_succ_of_lt hlt, hidx, heq⟩,
   fun ⟨idx, hlt, hidx, heq⟩ => by
     rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | rfl
     · exact ⟨idx, hlt', hidx, heq⟩
     · exact absurd heq (hnone A)⟩

private theorem exec_leafRuleStep {w : ℕ} (I : CYKInstance) (hw : I.FitsWidth w)
    {i rIdx : ℕ} (hi : i < I.word.length) (hrIdx : rIdx < I.rules.length)
    (st : Data 24) (hfix : FixedRegs I st)
    (hcb : st.regs regCurBase = cellBase I 0 i)
    (hwi : st.regs regWi = I.word[i])
    (hr : st.regs regRIdx = rIdx)
    (hmem : ActiveCellMem I 0 i (LeafAccProp I I.word[i] rIdx) st.mem) :
    ∃ st', ExecWithin w leafRuleBody st st' 13 ∧
      st'.regs regRIdx = rIdx + 1 ∧
      ActiveCellMem I 0 i (LeafAccProp I I.word[i] (rIdx + 1)) st'.mem := by
  have hlen := I.length_encode
  have hle_tbl := cellBase_add_le_tableEnd I 0 i (Nat.zero_lt_of_lt hi) hi
  obtain ⟨hm0, hm1, hm2, _⟩ := activeCellMem_read_rule I hmem hrIdx
  unfold leafRuleBody leafRuleLoad
  cases hr_eq : I.rules[rIdx] with
  | leaf A₀ a₀ =>
    have hA : A₀.val < I.numNTs := A₀.isLt
    simp only [hr_eq, encodeRule, List.getElem_cons_zero, List.getElem_cons_succ] at hm0 hm1 hm2
    by_cases hmatch : I.word[i] = a₀
    · wram_exec * [hmatch]
      · refine ⟨by wram_simp *, ?_⟩
        rw [Data.set_mem, Data.write_mem]
        refine activeCellMem_write_one I hi _ _ A₀ (fun A => ?_) hmem
        constructor
        · rintro ⟨idx, hlt, hidx, heq⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | rfl
          · exact Or.inl ⟨idx, hlt', hidx, heq⟩
          · rw [hr_eq] at heq; injection heq with hA' _; exact Or.inr hA'.symm
        · rintro (⟨idx, hlt, hidx, heq⟩ | rfl)
          · exact ⟨idx, Nat.lt_succ_of_lt hlt, hidx, heq⟩
          · exact ⟨rIdx, Nat.lt_succ_self _, hrIdx, by rw [hr_eq, hmatch]⟩
      all_goals exact hw.of_le (by omega)
    · wram_exec *
      · refine ⟨by wram_simp *, activeCellMem_congr I 0 i _ _
          (leafAccProp_step_none I hrIdx fun A hc => ?_) hmem⟩
        rw [hr_eq] at hc; injection hc with _ ha; exact hmatch ha.symm
      all_goals exact hw.of_le (by omega)
  | node A₀ B₀ C₀ =>
    simp only [hr_eq, encodeRule, List.getElem_cons_zero, List.getElem_cons_succ] at hm0 hm1 hm2
    wram_exec *
    · exact ⟨by wram_simp *, activeCellMem_congr I 0 i _ _
        (leafAccProp_step_none I hrIdx fun A hc => by rw [hr_eq] at hc; cases hc) hmem⟩
    all_goals exact hw.of_le (by omega)

private theorem exec_leafLevel {w : ℕ} (I : CYKInstance) (hw : I.FitsWidth w)
    (x₀ : Data 24) (hfix₀ : FixedRegs I x₀) (hmem₀ : CellBoundaryMem I 0 0 x₀.mem) :
    ∃ x₁, ExecWithin w (.seq (ram[ regI ← #0 ]) (.loop (.lt regI regN) leafCellBody)) x₀ x₁
        (I.word.length * (15 * I.rules.length + 10) + 3) ∧
      FixedRegs I x₁ ∧
      CellBoundaryMem I 1 0 x₁.mem := by
  let s0 := x₀.set regI 0
  have hsetI : ExecWithin w (ram[ regI ← #0 ] : Code .standard 24) x₀ s0 1 := by wram_exec
  let Pleaf (i : ℕ) (st : Data 24) : Prop :=
    FixedRegs I st ∧ CellBoundaryMem I 0 i st.mem
  have hbody : ∀ st, Pleaf (st.regs regI) st → st.regs regI < I.word.length →
      ∃ st', ExecWithin w leafCellBody st st' (15 * I.rules.length + 8) ∧
        Pleaf (st.regs regI + 1) st' ∧ st'.regs regI = st.regs regI + 1 := by
    intro st ⟨hfix, hb⟩ hi
    set i := st.regs regI with hi_def
    have hi_reg : st.regs regI = i := hi_def.symm
    have hlen := I.length_encode
    have ⟨_, _, hle_tbl⟩ := le_tableBound_of_lt I 0 i (Nat.zero_lt_of_lt hi) hi
    simp only [Nat.zero_mul, Nat.zero_add] at hle_tbl
    have hread_wi : st.mem (6 + 4 * I.rules.length + i) = I.word[i] :=
      (hb.1 (6 + 4 * I.rules.length + i) (by omega)).trans (cyk_read_word I hi)
    let Prule (rIdx : ℕ) (q : Data 24) : Prop :=
      FixedRegs I q ∧ q.regs regI = i ∧ q.regs regCurBase = cellBase I 0 i ∧
        q.regs regWi = I.word[i] ∧ ActiveCellMem I 0 i (LeafAccProp I I.word[i] rIdx) q.mem
    have hpre : ∃ p1, ExecWithin w leafPre st p1 5 ∧
        p1.regs regRIdx = 0 ∧ Prule 0 p1 := by
      wram_exec * [leafPre]
      · refine ⟨by wram_simp *, by regs_frame, by wram_simp *, ?_, by wram_simp *, ?_⟩
        · wram_simp *; simp [cellBase]
        · exact activeCellMem_congr I 0 i (fun _ => False) _ (by simp [LeafAccProp])
            (activeCellMem_start I 0 i hb)
      all_goals exact hw.of_le (by omega)
    obtain ⟨p1, hpre_ex, hp1_z, hp1_P⟩ := hpre
    obtain ⟨p3, htail, p2, ⟨hp2_fix, hp2_i, _, _, hp2_mem⟩, rfl⟩ :=
      exec_loopZero_then_inc Prule (fun _ h => h.1.r)
        (fun q ⟨hq_fix, hq_i, hq_cb, hq_wi, hq_mem⟩ hrlt => by
          obtain ⟨q', hstep, hq'_ridx, hq'_mem⟩ :=
            exec_leafRuleStep I hw hi hrlt q hq_fix hq_cb hq_wi rfl hq_mem
          exact ⟨q', hstep, ⟨by regs_frame, by regs_frame, by regs_frame, by regs_frame,
            hq'_mem⟩, hq'_ridx⟩)
        hp1_z hp1_P (fun _ h => ⟨h.2.1, h.1.one⟩) (hw.of_le (by omega))
    refine ⟨p2.set regI (i + 1), (hpre_ex.seq htail).mono (le_of_eq (by ring)),
      ⟨by regs_frame, cellBoundaryMem_finish_cell I _ (fun A => ?_) hp2_mem⟩,
      Data.set_regs_self p2 regI (i + 1)⟩
    rw [table, level_apply (G := I.grammar), ite_eq_left ⟨rfl, by omega⟩, cell, ite_eq_left rfl,
      mem_leafCell (G := I.grammar), List.getElem?_eq_getElem hi]
    exact ⟨fun ⟨idx, _, hidx, heq⟩ => ⟨I.word[i], rfl, heq ▸ List.getElem_mem hidx⟩,
      fun ⟨a, ha, hmem_r⟩ => by
        injection ha with ha'; subst ha'
        obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.1 hmem_r
        exact ⟨idx, hidx, hidx, heq⟩⟩
  have hs0_leaf : Pleaf (s0.regs regI) s0 := ⟨by regs_frame, hmem₀⟩
  obtain ⟨x₁, hloopI, ⟨hx₁_fix, hx₁_mem⟩, _⟩ :=
    ExecWithin.loop_count Pleaf (fun _ h => h.1.n) hbody (Nat.zero_le _) hs0_leaf
  have hs0_i : s0.regs regI = 0 := rfl
  rw [hs0_i, Nat.sub_zero] at hloopI
  have hx₁_mem' : CellBoundaryMem I 0 (I.word.length - 0) x₁.mem := by
    simpa only [Nat.sub_zero] using hx₁_mem
  exact ⟨x₁, (hsetI.seq hloopI).mono (le_of_eq (by ring)), hx₁_fix,
    cellBoundaryMem_next_level I 0 hx₁_mem'⟩

/-! ## Execution of the node levels (`1 ≤ d < |w|`) -/

private def SplitMatch (I : CYKInstance) (d i k' : ℕ)
    (r : ChomskyNormalFormRule ℕ (Fin I.numNTs)) (A : Fin I.numNTs) : Prop :=
  ∃ B C, r = .node A B C ∧
    B ∈ table I.grammar I.word (k' + 1) i (k' + 1) ∧
    C ∈ table I.grammar I.word (d - k') (i + k' + 1) (d - k')

private instance (I : CYKInstance) (d i k' : ℕ) (r : ChomskyNormalFormRule ℕ (Fin I.numNTs)) :
    DecidablePred (SplitMatch I d i k' r) := fun A => by
  unfold SplitMatch
  cases r with
  | leaf A₀ a₀ =>
    exact isFalse fun ⟨B, C, h, _⟩ => by cases h
  | node A₀ B₀ C₀ =>
    exact decidable_of_iff
      (A₀ = A ∧ B₀ ∈ table I.grammar I.word (k' + 1) i (k' + 1) ∧
        C₀ ∈ table I.grammar I.word (d - k') (i + k' + 1) (d - k'))
      ⟨fun ⟨hA, hB, hC⟩ => ⟨B₀, C₀, by rw [hA], hB, hC⟩,
       fun ⟨B, C, h, hB, hC⟩ => by
         injection h with hA hB' hC'
         subst hA; subst hB'; subst hC'
         exact ⟨rfl, hB, hC⟩⟩

private def NodeAccProp (I : CYKInstance) (d i k rIdx : ℕ) (A : Fin I.numNTs) : Prop :=
  (∃ k' < k, ∃ r ∈ I.rules, SplitMatch I d i k' r A) ∨
  (∃ idx < rIdx, ∃ h : idx < I.rules.length, SplitMatch I d i k I.rules[idx] A)

private instance (I : CYKInstance) (d i k rIdx : ℕ) :
    DecidablePred (NodeAccProp I d i k rIdx) := by
  unfold NodeAccProp
  infer_instance

private theorem nodeAccProp_step_none (I : CYKInstance) {d i k rIdx : ℕ}
    (hrIdx : rIdx < I.rules.length)
    (hnone : ∀ A, ¬SplitMatch I d i k I.rules[rIdx] A) (A : Fin I.numNTs) :
    NodeAccProp I d i k rIdx A ↔ NodeAccProp I d i k (rIdx + 1) A :=
  ⟨fun h => h.imp id fun ⟨idx, hlt, hidx, hsm⟩ => ⟨idx, Nat.lt_succ_of_lt hlt, hidx, hsm⟩,
   fun h => h.imp id fun ⟨idx, hlt, hidx, hsm⟩ => by
     rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | rfl
     · exact ⟨idx, hlt', hidx, hsm⟩
     · exact absurd hsm (hnone A)⟩

private theorem exec_nodeRuleStep {w : ℕ} (I : CYKInstance) (hw : I.FitsWidth w)
    {d i k rIdx : ℕ} (hd1 : 1 ≤ d) (hd : d < I.word.length) (hi : i < I.word.length - d)
    (hk : k < d) (hrIdx : rIdx < I.rules.length)
    (st : Data 24) (hfix : FixedRegs I st)
    (hcb : st.regs regCurBase = cellBase I d i)
    (hlb : st.regs regLeftBase = cellBase I k i)
    (hrb_sub : st.regs regRightBase = cellBase I (d - 1 - k) (i + k + 1))
    (hr : st.regs regRIdx = rIdx)
    (hmem : ActiveCellMem I d i (NodeAccProp I d i k rIdx) st.mem) :
    ∃ st', ExecWithin w nodeRuleBody st st' 19 ∧
      st'.regs regRIdx = rIdx + 1 ∧
      ActiveCellMem I d i (NodeAccProp I d i k (rIdx + 1)) st'.mem := by
  have hlen := I.length_encode
  obtain ⟨hm0, hm1, hm2, hm3⟩ := activeCellMem_read_rule I hmem hrIdx
  unfold nodeRuleBody nodeRuleLoad nodeSubcellLoads
  cases hr_eq : I.rules[rIdx] with
  | leaf A₀ a₀ =>
    simp only [hr_eq, encodeRule, List.getElem_cons_zero, List.getElem_cons_succ]
      at hm0 hm1 hm2 hm3
    wram_exec *
    · exact ⟨by wram_simp *, activeCellMem_congr I d i _ _
        (nodeAccProp_step_none I hrIdx fun A ⟨_, _, hc, _⟩ => by rw [hr_eq] at hc; cases hc) hmem⟩
    all_goals exact hw.of_le (by omega)
  | node A₀ B₀ C₀ =>
    simp only [hr_eq, encodeRule, List.getElem_cons_zero, List.getElem_cons_succ]
      at hm0 hm1 hm2 hm3
    have hle_left := cellBase_add_le_tableEnd I k i (by omega) (by omega)
    have hle_right := cellBase_add_le_tableEnd I (d - 1 - k) (i + k + 1) (by omega) (by omega)
    have hle_cur := cellBase_add_le_tableEnd I d i hd (by omega)
    have hA_lt : A₀.val < I.numNTs := A₀.isLt
    have hB_lt : B₀.val < I.numNTs := B₀.isLt
    have hC_lt : C₀.val < I.numNTs := C₀.isLt
    have hread_B : st.mem (cellBase I k i + B₀.val) =
        (decide (B₀ ∈ table I.grammar I.word (k + 1) i (k + 1))).toNat :=
      hmem.2.1 k hk i (by omega) B₀
    have hread_C : st.mem (cellBase I (d - 1 - k) (i + k + 1) + C₀.val) =
        (decide (C₀ ∈ table I.grammar I.word (d - k) (i + k + 1) (d - k))).toNat := by
      have hraw := hmem.2.1 (d - 1 - k) (by omega) (i + k + 1) (by omega) C₀
      rwa [show d - 1 - k + 1 = d - k by omega] at hraw
    by_cases hB : B₀ ∈ table I.grammar I.word (k + 1) i (k + 1)
    · simp only [hB, decide_true, Bool.toNat_true] at hread_B
      by_cases hC : C₀ ∈ table I.grammar I.word (d - k) (i + k + 1) (d - k)
      · simp only [hC, decide_true, Bool.toNat_true] at hread_C
        wram_exec *
        · refine ⟨by wram_simp *, ?_⟩
          rw [Data.set_mem, Data.write_mem]
          refine activeCellMem_write_one I (by omega) _ _ A₀ (fun A => ?_) hmem
          constructor
          · rintro (hprev | ⟨idx, hlt, hidx, hsm⟩)
            · exact Or.inl (Or.inl hprev)
            · rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | rfl
              · exact Or.inl (Or.inr ⟨idx, hlt', hidx, hsm⟩)
              · obtain ⟨_, _, hc, _⟩ := hsm
                rw [hr_eq] at hc; injection hc with hA' _ _; exact Or.inr hA'.symm
          · rintro ((hprev | ⟨idx, hlt, hidx, hsm⟩) | rfl)
            · exact Or.inl hprev
            · exact Or.inr ⟨idx, Nat.lt_succ_of_lt hlt, hidx, hsm⟩
            · exact Or.inr ⟨rIdx, Nat.lt_succ_self _, hrIdx, B₀, C₀, hr_eq, hB, hC⟩
        all_goals exact hw.of_le (by omega)
      · simp only [hC, decide_false, Bool.toNat_false] at hread_C
        wram_exec *
        · exact ⟨by wram_simp *, activeCellMem_congr I d i _ _
            (nodeAccProp_step_none I hrIdx fun A ⟨_, _, hc, _, hC'⟩ => by
              rw [hr_eq] at hc; injection hc with _ _ hCeq; subst hCeq; exact hC hC') hmem⟩
        all_goals exact hw.of_le (by omega)
    · simp only [hB, decide_false, Bool.toNat_false] at hread_B
      wram_exec *
      · exact ⟨by wram_simp *, activeCellMem_congr I d i _ _
          (nodeAccProp_step_none I hrIdx fun A ⟨_, _, hc, hB', _⟩ => by
            rw [hr_eq] at hc; injection hc with _ hBeq _; subst hBeq; exact hB hB') hmem⟩
      all_goals exact hw.of_le (by omega)

private theorem exec_nodeSplitStep {w : ℕ} (I : CYKInstance) (hw : I.FitsWidth w)
    {d i k : ℕ} (hd1 : 1 ≤ d) (hd : d < I.word.length) (hi : i < I.word.length - d) (hk : k < d)
    (st : Data 24) (hfix : FixedRegs I st)
    (hd_reg : st.regs regD = d)
    (hilim : st.regs regILim = I.word.length - d)
    (hi_reg : st.regs regI = i)
    (hcb : st.regs regCurBase = cellBase I d i)
    (hk_reg : st.regs regK = k)
    (hmem : ActiveCellMem I d i (NodeAccProp I d i k 0) st.mem) :
    ∃ st', ExecWithin w nodeSplitBody st st' (21 * I.rules.length + 16) ∧
      FixedRegs I st' ∧
      st'.regs regD = d ∧
      st'.regs regILim = I.word.length - d ∧
      st'.regs regI = i ∧
      st'.regs regCurBase = cellBase I d i ∧
      st'.regs regK = k + 1 ∧
      ActiveCellMem I d i (NodeAccProp I d i (k + 1) 0) st'.mem := by
  have hlen := I.length_encode
  have ⟨hl1, hl2, hl3⟩ := le_tableBound_of_lt I k i (by omega) (by omega)
  have ⟨hr1, hr2, hr3⟩ := le_tableBound_of_lt I (d - 1 - k) (i + k + 1) (by omega) (by omega)
  let Prule (rIdx : ℕ) (q : Data 24) : Prop :=
    FixedRegs I q ∧ q.regs regD = d ∧ q.regs regILim = I.word.length - d ∧
      q.regs regI = i ∧ q.regs regCurBase = cellBase I d i ∧ q.regs regK = k ∧
      q.regs regLeftBase = cellBase I k i ∧
      q.regs regRightBase = cellBase I (d - 1 - k) (i + k + 1) ∧
      ActiveCellMem I d i (NodeAccProp I d i k rIdx) q.mem
  have hpre : ∃ p1, ExecWithin w nodeSplitPre st p1 13 ∧ p1.regs regRIdx = 0 ∧ Prule 0 p1 := by
    wram_exec * [nodeSplitPre]
    · refine ⟨by wram_simp *, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
        by regs_frame, by regs_frame, ?_, ?_, hmem⟩ <;> (wram_simp *; rfl)
    all_goals exact hw.of_le (by omega)
  obtain ⟨p1, hpre_ex, hp1_z, hp1_P⟩ := hpre
  obtain ⟨p3, htail, p2, ⟨hp2_fix, hp2_d, hp2_ilim, hp2_i, hp2_cb, hp2_k, _, _, hp2_mem⟩, rfl⟩ :=
    exec_loopZero_then_inc Prule (fun _ h => h.1.r)
      (fun q ⟨hq_fix, hq_d, hq_ilim, hq_i, hq_cb, hq_k, hq_lb, hq_rb, hq_mem⟩ hrlt => by
        obtain ⟨q', hstep, hq'_ridx, hq'_mem⟩ :=
          exec_nodeRuleStep I hw hd1 hd hi hk hrlt q hq_fix hq_cb hq_lb hq_rb rfl hq_mem
        exact ⟨q', hstep, ⟨by regs_frame, by regs_frame, by regs_frame, by regs_frame,
          by regs_frame, by regs_frame, by regs_frame, by regs_frame, hq'_mem⟩, hq'_ridx⟩)
      hp1_z hp1_P (fun _ h => ⟨h.2.2.2.2.2.1, h.1.one⟩) (hw.of_le (by omega))
  refine ⟨p2.set regK (k + 1), (hpre_ex.seq htail).mono (le_of_eq (by ring)),
    by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    Data.set_regs_self p2 regK (k + 1),
    activeCellMem_congr I d i _ _ (fun A => ?_) hp2_mem⟩
  unfold NodeAccProp
  constructor
  · rintro (⟨k', hk', r, hr_mem, hsm⟩ | ⟨idx, _, hidx, hsm⟩)
    · exact Or.inl ⟨k', Nat.lt_succ_of_lt hk', r, hr_mem, hsm⟩
    · exact Or.inl ⟨k, Nat.lt_succ_self _, I.rules[idx], List.getElem_mem hidx, hsm⟩
  · rintro (⟨k', hk', r, hr_mem, hsm⟩ | ⟨_, hlt, _⟩)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt' | rfl
      · exact Or.inl ⟨k', hlt', r, hr_mem, hsm⟩
      · obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 hr_mem
        exact Or.inr ⟨idx, hidx, hidx, hsm⟩
    · cases hlt

private theorem exec_nodeCellStep {w : ℕ} (I : CYKInstance) (hw : I.FitsWidth w)
    {d i : ℕ} (hd1 : 1 ≤ d) (hd : d < I.word.length) (hi : i < I.word.length - d)
    (st : Data 24) (hfix : FixedRegs I st)
    (hd_reg : st.regs regD = d)
    (hilim : st.regs regILim = I.word.length - d)
    (hi_reg : st.regs regI = i)
    (hb : CellBoundaryMem I d i st.mem) :
    ∃ st', ExecWithin w nodeCellBody st st'
        ((I.word.length - 1) * (21 * I.rules.length + 18) + 8) ∧
      FixedRegs I st' ∧
      st'.regs regD = d ∧
      st'.regs regILim = I.word.length - d ∧
      st'.regs regI = i + 1 ∧
      CellBoundaryMem I d (i + 1) st'.mem := by
  have hlen := I.length_encode
  have ⟨hc1, hc2, hc3⟩ := le_tableBound_of_lt I d i hd (by omega)
  let Psplit (k : ℕ) (q : Data 24) : Prop :=
    FixedRegs I q ∧ q.regs regD = d ∧ q.regs regILim = I.word.length - d ∧
      q.regs regI = i ∧ q.regs regCurBase = cellBase I d i ∧
      ActiveCellMem I d i (NodeAccProp I d i k 0) q.mem
  have hpre : ∃ p1, ExecWithin w nodeCellPre st p1 5 ∧ p1.regs regK = 0 ∧ Psplit 0 p1 := by
    wram_exec * [nodeCellPre]
    · refine ⟨by wram_simp *, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
        by wram_simp *; rfl,
        activeCellMem_congr I d i (fun _ => False) _ (by simp [NodeAccProp])
          (activeCellMem_start I d i hb)⟩
    all_goals exact hw.of_le (by omega)
  obtain ⟨p1, hpre_ex, hp1_z, hp1_P⟩ := hpre
  obtain ⟨p3, htail, p2, ⟨hp2_fix, hp2_d, hp2_ilim, hp2_i, _, hp2_mem⟩, rfl⟩ :=
    exec_loopZero_then_inc Psplit (fun _ h => h.2.1)
      (fun q ⟨hq_fix, hq_d, hq_ilim, hq_i, hq_cb, hq_mem⟩ hklt => by
        obtain ⟨q', hstep, hq'_fix, hq'_d, hq'_ilim, hq'_i, hq'_cb, hq'_k, hq'_mem⟩ :=
          exec_nodeSplitStep I hw hd1 hd hi hklt q hq_fix hq_d hq_ilim hq_i hq_cb rfl hq_mem
        exact ⟨q', hstep, ⟨hq'_fix, hq'_d, hq'_ilim, hq'_i, hq'_cb, hq'_mem⟩, hq'_k⟩)
      hp1_z hp1_P (fun _ h => ⟨h.2.2.2.1, h.1.one⟩) (hw.of_le (by omega))
  have hmono_bound : 5 + (d * (21 * I.rules.length + 16 + 2) + 3) ≤
      (I.word.length - 1) * (21 * I.rules.length + 18) + 8 := by
    change 5 + (d * (21 * I.rules.length + 18) + 3) ≤ _
    have := Nat.mul_le_mul_right (21 * I.rules.length + 18)
      (show d ≤ I.word.length - 1 by omega)
    omega
  refine ⟨p2.set regI (i + 1), (hpre_ex.seq htail).mono hmono_bound,
    by regs_frame, by regs_frame, by regs_frame, Data.set_regs_self p2 regI (i + 1),
    cellBoundaryMem_finish_cell I _ (fun A => ?_) hp2_mem⟩
  rw [table, level_apply (G := I.grammar), ite_eq_left ⟨rfl, by omega⟩, cell,
    ite_eq_right (by omega), mem_nodeCell (G := I.grammar), Nat.add_sub_cancel]
  simp only [NodeAccProp, SplitMatch, Nat.not_lt_zero, false_and, exists_false, or_false]
  constructor
  · rintro ⟨k', hk', _, hr_mem, B, C, rfl, hB, hC⟩
    have hk_sub : d + 1 - k' - 1 = d - k' := by omega
    refine ⟨k', hk', B, C, hr_mem, ?_, ?_⟩
    · rwa [table_eq_of_le (G := I.grammar) (by omega) i]
    · rwa [hk_sub, table_eq_of_le (G := I.grammar) (by omega) (i + k' + 1)]
  · rintro ⟨k', hk', B, C, hr_mem, hB, hC⟩
    have hk_sub : d + 1 - k' - 1 = d - k' := by omega
    refine ⟨k', hk', .node A B C, hr_mem, B, C, rfl, ?_, ?_⟩
    · rwa [table_eq_of_le (G := I.grammar) (by omega) i] at hB
    · rwa [hk_sub, table_eq_of_le (G := I.grammar) (by omega) (i + k' + 1)] at hC

private theorem exec_nodeLevels {w : ℕ} (I : CYKInstance) (hw : I.FitsWidth w)
    (hn_pos : 0 < I.word.length) (x₁ : Data 24)
    (hfix₁ : FixedRegs I x₁) (hmem₁ : CellBoundaryMem I 1 0 x₁.mem) :
    ∃ x₂, ExecWithin w (.seq (ram[ regD ← #1 ]) (.loop (.lt regD regN) nodeLevelBody)) x₁ x₂
        ((I.word.length - 1) *
          ((I.word.length - 1) *
            ((I.word.length - 1) * (21 * I.rules.length + 18) + 10) + 7) + 3) ∧
      FixedRegs I x₂ ∧
      CellBoundaryMem I I.word.length 0 x₂.mem := by
  let s0 := x₁.set regD 1
  have hsetD : ExecWithin w (ram[ regD ← #1 ] : Code .standard 24) x₁ s0 1 := by
    wram_exec; exact hw.of_le (by omega)
  let Plevel (d : ℕ) (st : Data 24) : Prop :=
    1 ≤ d ∧ FixedRegs I st ∧ CellBoundaryMem I d 0 st.mem
  have hlevelBody : ∀ st, Plevel (st.regs regD) st → st.regs regD < I.word.length →
      ∃ st', ExecWithin w nodeLevelBody st st'
          ((I.word.length - 1) *
            ((I.word.length - 1) * (21 * I.rules.length + 18) + 10) + 5) ∧
        Plevel (st.regs regD + 1) st' ∧ st'.regs regD = st.regs regD + 1 := by
    intro st ⟨hd1, hfix, hb⟩ hd
    set d := st.regs regD with hd_def
    have hd_reg : st.regs regD = d := hd_def.symm
    have hlen := I.length_encode
    let Pcell (i : ℕ) (q : Data 24) : Prop :=
      FixedRegs I q ∧ q.regs regD = d ∧ q.regs regILim = I.word.length - d ∧
        CellBoundaryMem I d i q.mem
    have hpre : ∃ p1, ExecWithin w (ram[ regILim ← regN - regD; regI ← #0 ]) st p1 2 ∧
        p1.regs regI = 0 ∧ Pcell 0 p1 := by
      wram_exec *
      · exact ⟨by wram_simp *, by regs_frame, by regs_frame, by wram_simp *, hb⟩
      · exact hw.of_le (by omega)
    obtain ⟨p1, hpre_ex, hp1_z, hp1_P⟩ := hpre
    obtain ⟨p3, htail, p2, ⟨hp2_fix, hp2_d, _, hp2_mem⟩, rfl⟩ :=
      exec_loopZero_then_inc Pcell (fun _ h => h.2.2.1)
        (fun q ⟨hq_fix, hq_d, hq_ilim, hq_mem⟩ hilt => by
          obtain ⟨q', hstep, hq'_fix, hq'_d, hq'_ilim, hq'_i, hq'_mem⟩ :=
            exec_nodeCellStep I hw hd1 hd hilt q hq_fix hq_d hq_ilim rfl hq_mem
          exact ⟨q', hstep, ⟨hq'_fix, hq'_d, hq'_ilim, hq'_mem⟩, hq'_i⟩)
        hp1_z hp1_P (fun _ h => ⟨h.2.1, h.1.one⟩) (hw.of_le (by omega))
    have hmono :
        2 + ((I.word.length - d) *
          ((I.word.length - 1) * (21 * I.rules.length + 18) + 8 + 2) + 3) ≤
          (I.word.length - 1) *
            ((I.word.length - 1) * (21 * I.rules.length + 18) + 10) + 5 := by
      change 2 + ((I.word.length - d) *
        ((I.word.length - 1) * (21 * I.rules.length + 18) + 10) + 3) ≤ _
      have := Nat.mul_le_mul_right
        ((I.word.length - 1) * (21 * I.rules.length + 18) + 10)
        (show I.word.length - d ≤ I.word.length - 1 by omega)
      omega
    exact ⟨p2.set regD (d + 1), (hpre_ex.seq htail).mono hmono,
      ⟨by omega, by regs_frame, cellBoundaryMem_next_level I d hp2_mem⟩,
      Data.set_regs_self p2 regD (d + 1)⟩
  have hs0_level : Plevel (s0.regs regD) s0 := ⟨le_rfl, by regs_frame, hmem₁⟩
  have hs0_le : s0.regs regD ≤ I.word.length := hn_pos
  obtain ⟨x₂, hloopD, ⟨_, hx₂_fix, hx₂_mem⟩, _⟩ :=
    ExecWithin.loop_count Plevel (fun _ h => h.2.1.n) hlevelBody hs0_le hs0_level
  have hs0_d : s0.regs regD = 1 := rfl
  rw [hs0_d] at hloopD
  exact ⟨x₂, (hsetD.seq hloopD).mono (le_of_eq (by ring)), hx₂_fix, hx₂_mem⟩

/-! ## Top-level execution and public running-time theorems -/

private theorem poly_bound_nonempty (R m : ℕ) :
    17 + (1 + (((m + 1) * (15 * R + 10) + 3) +
      ((m * (m * (m * (21 * R + 18) + 10) + 7) + 3) + 6))) ≤
      41 * (R + 1) * (m + 1) ^ 3 :=
  Nat.le.intro (k := 20 * R * m ^ 3 + 23 * m ^ 3 + 123 * R * m ^ 2 + 113 * m ^ 2 +
      108 * R * m + 106 * m + 26 * R + 1)
    (by ring)

private theorem exec_cykCode {w : ℕ} (I : CYKInstance) (hw : I.FitsWidth w) :
    ∃ xf, ExecWithin w cykCode (.init I.encode) xf
        (if I.word = [] then 20 else 41 * (I.rules.length + 1) * I.word.length ^ 3) ∧
      xf.regs regTag = (cyk I.grammar I.word).toNat := by
  obtain ⟨x₀, hsetup, hx₀_mem, hfix₀, htag₀⟩ := exec_cykSetup I hw
  by_cases hw_nil : I.word = []
  · have hn0 : x₀.regs regN = 0 := hfix₀.n.trans (by simp [hw_nil])
    have hbr : ∃ xf, ExecWithin w (.branch (.lt regTag regN) cykNonempty (ram[ regTag ← regNil ]))
        x₀ xf 3 ∧ xf.regs regTag = I.nilRule.toNat := by
      wram_exec *
      wram_simp *
    obtain ⟨xf, hbr_ex, hres⟩ := hbr
    refine ⟨xf, (hsetup.seq hbr_ex).mono (by rw [ite_eq_left hw_nil]), ?_⟩
    rw [hres, cyk, ite_eq_left hw_nil]
  · have hn_pos : 0 < I.word.length := List.length_pos_of_ne_nil hw_nil
    have hlt : Cond.Holds (.lt regTag regN) x₀ := by
      simp [Cond.holds_lt, htag₀, hfix₀.n, hn_pos]
    have hmem₀ : CellBoundaryMem I 0 0 x₀.mem := by
      refine ⟨fun addr _ => hx₀_mem ▸ rfl,
        fun _ hd' => absurd hd' (Nat.not_lt_zero _),
        fun _ hi' => absurd hi' (Nat.not_lt_zero _),
        fun addr haddr => ?_⟩
      rw [hx₀_mem]
      exact init_mem_above I.encode (by dsimp only [cellBase] at haddr; omega)
    obtain ⟨x₁, hleaf, hfix₁, hmem₁⟩ := exec_leafLevel I hw x₀ hfix₀ hmem₀
    obtain ⟨x₂, hnodes, hfix₂, hmem₂⟩ := exec_nodeLevels I hw hn_pos x₁ hfix₁ hmem₁
    have hlen := I.length_encode
    have ⟨hf1, _, hf3⟩ := le_tableBound_of_lt I (I.word.length - 1) 0 (by omega) hn_pos
    simp only [Nat.add_zero] at hf3
    have hinit_lt : I.initial.val < I.numNTs := I.initial.isLt
    have hread_init := hmem₂.2.1 (I.word.length - 1) (by omega) 0 (by omega) I.initial
    have haddr_eq :
        I.encode.length + 1 + (I.word.length - 1) * I.word.length * I.numNTs + I.initial.val =
          cellBase I (I.word.length - 1) 0 + I.initial.val := by simp [cellBase]
    have hfin : ∃ xf, ExecWithin w cykFinalRead x₂ xf 6 ∧
        xf.regs regTag = (cyk I.grammar I.word).toNat := by
      wram_exec * [cykFinalRead]
      · wram_simp *
        rw [haddr_eq, hread_init, show I.word.length - 1 + 1 = I.word.length by omega,
          cyk, ite_eq_right hw_nil]
      all_goals exact hw.of_le (by omega)
    obtain ⟨xf, hfin_ex, hres⟩ := hfin
    have hbr := ExecWithin.branch_pos (neg := ram[ regTag ← regNil ]) hlt
      (hleaf.seq (hnodes.seq hfin_ex))
    obtain ⟨m, hm⟩ : ∃ m, I.word.length = m + 1 := ⟨I.word.length - 1, by omega⟩
    refine ⟨xf, (hsetup.seq hbr).mono ?_, hres⟩
    rw [ite_eq_right hw_nil, hm, Nat.add_sub_cancel]
    exact (le_of_eq (by ring)).trans (poly_bound_nonempty I.rules.length m)

/-- **Word-RAM functional running time of CYK.** `cykProgram` computes
`(cyk I.grammar I.word).toNat` in at most `I.timeBound` instructions (`21` on `[]`, and
`42 (|R| + 1) |w|³` on nonempty words) at every fitting word width `w`. -/
theorem computesInTime_cyk :
    cykProgram.ComputesInTime (fun _ => CYKInstance.encode)
      (fun I _ => I.timeBound) CYKInstance.FitsWidth
      (fun I => (cyk I.grammar I.word).toNat) := by
  refine (cykCode.computesInTime_program regTag
    (time := fun I _ =>
      if I.word = [] then 20 else 41 * (I.rules.length + 1) * I.word.length ^ 3) ?_).mono ?_
    (fun _ _ h => h)
  · intro I w hw _
    exact exec_cykCode I hw
  · intro I _
    unfold CYKInstance.timeBound
    split_ifs with hw
    · omega
    · have hpos : 1 ≤ (I.rules.length + 1) * I.word.length ^ 3 :=
        Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (List.length_pos_of_ne_nil hw))
      nlinarith

/-- **Word-RAM decision running time of CYK.** `cykProgram` decides membership in
`I.grammar.toCFG.language` within `I.timeBound` instructions (`21` on `[]`, and
`42 (|R| + 1) |w|³` on nonempty words) at every fitting word width `w`. -/
theorem decidesInTime_cyk :
    cykProgram.DecidesInTime (fun _ => CYKInstance.encode)
      {I : CYKInstance | I.word ∈ I.grammar.toCFG.language}
      (fun I _ => I.timeBound) CYKInstance.FitsWidth := by
  intro I w hw hin
  obtain ⟨n, hexec, hle⟩ := computesInTime_cyk I w hw hin
  refine ⟨(cyk I.grammar I.word).toNat, n, hexec, hle, Bool.toNat_le _, ?_⟩
  rw [Set.mem_ofPred_eq, ← cyk_eq_true_iff (G := I.grammar) (w := I.word)]
  cases cyk I.grammar I.word <;> simp

/-- **Uniform cubic Word-RAM decidability of CYK.** Membership in the language of an encoded
Chomsky normal form grammar is uniformly decidable on a standard-basis Word-RAM in at most
`42 (|R| + 1) (|w| + 1)³` instructions, bundling width admissibility
`CYKInstance.inputAdmissible`. -/
theorem uniformDecidableInTime_cyk :
    UniformDecidableInTime .standard {I : CYKInstance | I.word ∈ I.grammar.toCFG.language}
      (fun _ => CYKInstance.encode)
      (fun I _ => 42 * (I.rules.length + 1) * (I.word.length + 1) ^ 3)
      CYKInstance.FitsWidth :=
  ⟨24, cykProgram, decidesInTime_cyk.mono (fun I _ => I.timeBound_le) (fun _ _ h => h),
    CYKInstance.inputAdmissible⟩

end Cslib.Algorithms.WordRAM.CYK
