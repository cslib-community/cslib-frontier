/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.CYK.Basic
public import CslibFrontier.Algorithms.WordRAM.CYK

/-!
# The Cocke–Younger–Kasami algorithm: worked examples

Kernel-checked examples (no `native_decide`) for two grammars in Chomsky normal form: `{aⁿbⁿ}`
without `ε`, whose start symbol occurs on a right-hand side, and the balanced-parenthesis
language with the rule `S → ε`. Each grammar gets accepted and rejected words, including the
empty word, through `cyk`, through the `Decidable` instance on language membership, and through
the Word-RAM program `cykProgram` and its running-time certificates. The file also checks that the
bundled `nilRule` invariant is not vacuous.
-/

public section

namespace CslibFrontierTests.CYK

open Cslib Cslib.Algorithms.Lean.CYK Cslib.Algorithms.WordRAM.CYK Cslib.WordRAM
open ChomskyNormalFormRule

/-! ### `{aⁿbⁿ | n ≥ 1}` -/

/-- Nonterminals for `{aⁿbⁿ}`. -/
inductive N
  | S | X | A | B
  deriving DecidableEq, Repr

/-- `{aⁿbⁿ | n ≥ 1}`: `S → AB | AX`, `X → SB`, `A → a`, `B → b`. The start symbol `S` occurs on
the right-hand side of `X → SB`, which is allowed since there is no rule `S → ε`. -/
@[expose] def anbn : ChomskyNormalFormGrammar Char where
  NT := N
  initial := .S
  rules := [node .S .A .B, node .S .A .X, node .X .S .B, leaf .A 'a', leaf .B 'b']
  nilRule := false
  initial_notMem_output := by simp

instance : DecidableEq anbn.NT := inferInstanceAs (DecidableEq N)

example : cyk anbn ['a', 'b'] = true := by decide
example : cyk anbn ['a', 'a', 'b', 'b'] = true := by decide
example : cyk anbn ['a', 'a', 'a', 'b', 'b', 'b'] = true := by decide
example : cyk anbn ['a', 'b', 'a', 'b'] = false := by decide
example : cyk anbn ['a', 'a', 'b'] = false := by decide
example : cyk anbn ['b', 'a'] = false := by decide
example : cyk anbn ['a'] = false := by decide
example : cyk anbn [] = false := by decide

example : ['a', 'a', 'b', 'b'] ∈ anbn.toCFG.language := by decide
example : ['a', 'b', 'b'] ∉ anbn.toCFG.language := by decide
example : [] ∉ anbn.toCFG.language := by decide

/-- Reading derivations off the table: `X` derives `abb` (the cell of length `3` at position `1`
of `aabb`), and `S` does not derive `abab`. The nonterminals are given type `anbn.NT`, so that
`decide` finds the `DecidableEq anbn.NT` instance. -/
example : anbn.toCFG.Derives [.nonterminal N.X] ((['a', 'b', 'b'] : List Char).map .terminal) :=
  (mem_table_iff (G := anbn) (w := ['a', 'a', 'b', 'b']) (L := 3) (i := 1) (l := 3) (by decide)
    (by decide) (by decide) (show anbn.NT from N.X)).mp (by decide)

example : ¬ anbn.toCFG.Derives [.nonterminal anbn.initial]
    ((['a', 'b', 'a', 'b'] : List Char).map .terminal) :=
  fun h => absurd ((mem_table_iff (G := anbn) (w := ['a', 'b', 'a', 'b']) (L := 4) (i := 0)
    (l := 4) (by decide) (by decide) (by decide) anbn.initial).mpr h) (by decide)

/-! ### Balanced parentheses, with `ε` -/

/-- Nonterminals for the balanced-parenthesis language. -/
inductive D
  | Z | S | Y | L | R
  deriving DecidableEq, Repr

/-- Balanced parentheses, including `ε`: `Z → ε | LR | LY | SS`, `S → LR | LY | SS`, `Y → SR`,
`L → (`, `R → )`. The start symbol `Z` occurs on no right-hand side, as the rule `Z → ε`
requires. -/
@[expose] def dyck : ChomskyNormalFormGrammar Char where
  NT := D
  initial := .Z
  rules := [node .Z .L .R, node .Z .L .Y, node .Z .S .S,
    node .S .L .R, node .S .L .Y, node .S .S .S, node .Y .S .R, leaf .L '(', leaf .R ')']
  nilRule := true
  initial_notMem_output := by simp [output]

instance : DecidableEq dyck.NT := inferInstanceAs (DecidableEq D)

example : [] ∈ dyck.toCFG.language := by decide
example : ['(', ')'] ∈ dyck.toCFG.language := by decide
example : ['(', '(', ')', ')'] ∈ dyck.toCFG.language := by decide
example : ['(', '(', ')', ')', '(', ')'] ∈ dyck.toCFG.language := by decide
example : ['(', ')', ')', '('] ∉ dyck.toCFG.language := by decide
example : ['('] ∉ dyck.toCFG.language := by decide
example : [')', '('] ∉ dyck.toCFG.language := by decide

/-- Insertion skips repeats: the cell of `()()` holds `S` and `Z` once each, although each is
found at two split points. (`S` is given type `dyck.NT` so that `decide` finds the
`DecidableEq dyck.NT` instance.) -/
example : table dyck ['(', ')', '(', ')'] 4 0 4 = [show dyck.NT from D.S, dyck.initial] := by
  decide

/-! ### Word-RAM execution and running-time certificates -/

/-- Encoded `{aⁿbⁿ | n ≥ 1}` instance on word `w` (`0 = 'a'`, `1 = 'b'`). -/
@[expose] def anbnInst (w : List ℕ) : CYKInstance where
  numNTs := 4
  initial := 0
  rules := [node 0 2 3, node 0 2 1, node 1 0 3, leaf 2 0, leaf 3 1]
  nilRule := false
  initial_notMem_output := by simp
  word := w

/-- Encoded balanced-parenthesis instance with `Z → ε` (`0 = '('`, `1 = ')'`). -/
@[expose] def dyckInst (w : List ℕ) : CYKInstance where
  numNTs := 5
  initial := 0
  rules := [node 0 3 4, node 0 3 2, node 0 1 1,
    node 1 3 4, node 1 3 2, node 1 1 1, node 2 1 4, leaf 3 0, leaf 4 1]
  nilRule := true
  initial_notMem_output := by simp [ChomskyNormalFormRule.output]
  word := w

-- Accepted `aabb` (`[0, 0, 1, 1]`) on `{aⁿbⁿ}`: `timeBound = 42 * 6 * 64 = 16128`
example : ∃ n ≤ 42 * 6 * 64,
    Executes 8 cykProgram (.init (anbnInst [0, 0, 1, 1]).encode) 1 n ∧
      Cslib.WordRAM.run 8 cykProgram (42 * 6 * 64) (.init (anbnInst [0, 0, 1, 1]).encode) =
        some (1, n) := by
  obtain ⟨n, hexec, hle⟩ :=
    computesInTime_cyk (anbnInst [0, 0, 1, 1]) 8 (by decide) (by decide)
  dsimp only at hexec hle
  have hval : (cyk (anbnInst [0, 0, 1, 1]).grammar (anbnInst [0, 0, 1, 1]).word).toNat = 1 := by
    decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

-- Rejected `abab` (`[0, 1, 0, 1]`) on `{aⁿbⁿ}`
example : ∃ n ≤ 42 * 6 * 64,
    Executes 8 cykProgram (.init (anbnInst [0, 1, 0, 1]).encode) 0 n ∧
      Cslib.WordRAM.run 8 cykProgram (42 * 6 * 64) (.init (anbnInst [0, 1, 0, 1]).encode) =
        some (0, n) := by
  obtain ⟨n, hexec, hle⟩ :=
    computesInTime_cyk (anbnInst [0, 1, 0, 1]) 8 (by decide) (by decide)
  dsimp only at hexec hle
  have hval : (cyk (anbnInst [0, 1, 0, 1]).grammar (anbnInst [0, 1, 0, 1]).word).toNat = 0 := by
    decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

-- Asymmetric left/right rejection `bbaa` (`[1, 1, 0, 0]`) on `{aⁿbⁿ}` (`B`/`C` order witness)
example : ∃ n ≤ 42 * 6 * 64,
    Executes 8 cykProgram (.init (anbnInst [1, 1, 0, 0]).encode) 0 n ∧
      Cslib.WordRAM.run 8 cykProgram (42 * 6 * 64) (.init (anbnInst [1, 1, 0, 0]).encode) =
        some (0, n) := by
  obtain ⟨n, hexec, hle⟩ :=
    computesInTime_cyk (anbnInst [1, 1, 0, 0]) 8 (by decide) (by decide)
  dsimp only at hexec hle
  have hval : (cyk (anbnInst [1, 1, 0, 0]).grammar (anbnInst [1, 1, 0, 0]).word).toNat = 0 := by
    decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

-- Single-letter `[0]` (`|w| = 1`, leaf level with zero node-level iterations)
example : ∃ n ≤ 42 * 6 * 1,
    Executes 6 cykProgram (.init (anbnInst [0]).encode) 0 n ∧
      Cslib.WordRAM.run 6 cykProgram (42 * 6 * 1) (.init (anbnInst [0]).encode) = some (0, n) := by
  obtain ⟨n, hexec, hle⟩ := computesInTime_cyk (anbnInst [0]) 6 (by decide) (by decide)
  dsimp only at hexec hle
  have hval : (cyk (anbnInst [0]).grammar (anbnInst [0]).word).toNat = 0 := by decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

-- Empty-word rejection on `{aⁿbⁿ}` (`nilRule = false`) in `≤ 21` instructions
example : ∃ n ≤ 21,
    Executes 6 cykProgram (.init (anbnInst []).encode) 0 n ∧
      Cslib.WordRAM.run 6 cykProgram 21 (.init (anbnInst []).encode) = some (0, n) := by
  obtain ⟨n, hexec, hle⟩ := computesInTime_cyk (anbnInst []) 6 (by decide) (by decide)
  dsimp only at hexec hle
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

-- Empty-word and nonempty `dyck` (`nilRule = true`) through `DecidesInTime` and `ComputesInTime`
example : cykProgram.Answers 6 (dyckInst []).encode
    ([] ∈ (dyckInst []).grammar.toCFG.language) 21 :=
  decidesInTime_cyk (dyckInst []) 6 (by decide) (by decide)

example : ∃ n ≤ 42 * 10 * 64,
    Executes 8 cykProgram (.init (dyckInst [0, 1, 0, 1]).encode) 1 n ∧
      Cslib.WordRAM.run 8 cykProgram (42 * 10 * 64) (.init (dyckInst [0, 1, 0, 1]).encode) =
        some (1, n) := by
  obtain ⟨n, hexec, hle⟩ :=
    computesInTime_cyk (dyckInst [0, 1, 0, 1]) 8 (by decide) (by decide)
  dsimp only at hexec hle
  have hval : (cyk (dyckInst [0, 1, 0, 1]).grammar (dyckInst [0, 1, 0, 1]).word).toNat = 1 := by
    decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

example : ∃ n ≤ 42 * 10 * 8,
    Executes 7 cykProgram (.init (dyckInst [1, 0]).encode) 0 n ∧
      Cslib.WordRAM.run 7 cykProgram (42 * 10 * 8) (.init (dyckInst [1, 0]).encode) =
        some (0, n) := by
  obtain ⟨n, hexec, hle⟩ := computesInTime_cyk (dyckInst [1, 0]) 7 (by decide) (by decide)
  dsimp only at hexec hle
  have hval : (cyk (dyckInst [1, 0]).grammar (dyckInst [1, 0]).word).toNat = 0 := by decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

-- Single-letter accepted witness (`S → 0` on `[0]`, exercising `|w| = 1` with `cykFinalRead = 1`)
def singleLetterInst : CYKInstance where
  numNTs := 1
  initial := 0
  rules := [leaf 0 0]
  nilRule := false
  initial_notMem_output := by intro h; cases h
  word := [0]

example : ∃ n ≤ 42 * 2 * 1,
    Executes 5 cykProgram (.init singleLetterInst.encode) 1 n ∧
      Cslib.WordRAM.run 5 cykProgram (42 * 2 * 1) (.init singleLetterInst.encode) =
        some (1, n) := by
  obtain ⟨n, hexec, hle⟩ := computesInTime_cyk singleLetterInst 5 (by decide) (by decide)
  dsimp only at hexec hle
  have hval : (cyk singleLetterInst.grammar singleLetterInst.word).toNat = 1 := by decide
  rw [hval] at hexec
  exact ⟨n, hle, hexec, run_mono hexec.run_eq hle⟩

/-! ### The invariant is not vacuous -/

/-- With the rule `S → ε`, no rule may use the start symbol on its right-hand side; `dyck` shows
that such grammars exist. -/
example (G : ChomskyNormalFormGrammar Char) (h : G.nilRule = true) :
    node G.initial G.initial G.initial ∉ G.rules :=
  fun hr => G.initial_notMem_output h _ hr (by simp [output])

example : dyck.nilRule = true := rfl

end CslibFrontierTests.CYK
