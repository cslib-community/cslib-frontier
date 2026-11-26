/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Input
public import CslibFrontier.Computability.WordRAM.PreservesMask
public import CslibFrontier.Computability.WordRAM.Structured

/-!
# Word-RAM Memory and Register Layout for Aho–Corasick

Base addresses (`Input.maxS` through `Input.outBase`), register aliases `Reg.*` over `Fin 26`,
and the register-layout invariant `LayoutInv` preserved across all four phases of `searchCode`.

This module stays independent of the pure trie and BFS models (`TrieModel`, `BFSModel`,
`BFSCorrect`) so `Layout` and `Code` build in parallel with the pure proof layers.

## Main definitions

* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.maxS`, `Input.textBase`, `Input.trieBase`,
  `Input.deltaBase`, `Input.failBase`, `Input.depthBase`, `Input.termBase`, `Input.outHeadBase`,
  `Input.outNextBase`, `Input.queueBase`, `Input.outBase`: opaque workspace base addresses.
* `Cslib.Algorithms.WordRAM.AhoCorasick.LayoutInv`: pinned read-only register invariant covering
  registers `0..17`.

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.wordBound_eq_outBase`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.layout_order`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.fits_of_le_outBase`: layout arithmetic identities.
* `Cslib.Algorithms.WordRAM.AhoCorasick.LayoutInv.of_preserves`: preserve `LayoutInv` across any
  code block whose writes start at register `18` or higher.
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.WordRAM
open Cslib.Algorithms.Lean.AhoCorasick

/-! ## Word-RAM register and memory layout (`Fin 26`, `Basis.standard`) -/

/-- Upper bound on the number of trie states (`totalPatternLen inp.patterns + 1`). -/
def Input.maxS (inp : Input) : ℕ := totalPatternLen inp.patterns + 1

/-- Base word address of the input text array inside the serialized Word-RAM memory. -/
def Input.textBase (inp : Input) : ℕ :=
  5 + inp.patterns.length + totalPatternLen inp.patterns

/-- Base address of the flat `maxS × σ` array-trie goto table. -/
def Input.trieBase (inp : Input) : ℕ := inp.textBase + inp.text.length

/-- Base address of the flat `maxS × σ` deterministic next-move (`delta`) table. -/
def Input.deltaBase (inp : Input) : ℕ := inp.trieBase + inp.maxS * inp.alphabetSize

/-- Base address of the `maxS`-word failure-link array. -/
def Input.failBase (inp : Input) : ℕ := inp.deltaBase + inp.maxS * inp.alphabetSize

/-- Base address of the `maxS`-word state-depth array. -/
def Input.depthBase (inp : Input) : ℕ := inp.failBase + inp.maxS

/-- Base address of the `maxS`-word terminal-state indicator array. -/
def Input.termBase (inp : Input) : ℕ := inp.depthBase + inp.maxS

/-- Base address of the `maxS`-word linked output-chain head array. -/
def Input.outHeadBase (inp : Input) : ℕ := inp.termBase + inp.maxS

/-- Base address of the `maxS`-word linked output-chain `next` array. -/
def Input.outNextBase (inp : Input) : ℕ := inp.outHeadBase + inp.maxS

/-- Base address of the `maxS`-word BFS FIFO queue array. -/
def Input.queueBase (inp : Input) : ℕ := inp.outNextBase + inp.maxS

/-- Base address of the length-prefixed output list buffer. -/
def Input.outBase (inp : Input) : ℕ := inp.queueBase + inp.maxS

theorem wordBound_eq_outBase (inp : Input) :
    inp.wordBound = inp.outBase + 2 * (occurrences inp.patterns inp.text).length + 4 := by
  dsimp only [Input.wordBound, Input.outBase, Input.queueBase, Input.outNextBase,
    Input.outHeadBase, Input.termBase, Input.depthBase, Input.failBase, Input.deltaBase,
    Input.trieBase, Input.textBase, Input.maxS]
  rw [Nat.mul_assoc]
  omega

theorem layout_order (inp : Input) :
    inp.maxS = totalPatternLen inp.patterns + 1 ∧
    inp.textBase = 5 + inp.patterns.length + totalPatternLen inp.patterns ∧
    inp.trieBase = inp.textBase + inp.text.length ∧
    inp.deltaBase = inp.trieBase + inp.maxS * inp.alphabetSize ∧
    inp.failBase = inp.deltaBase + inp.maxS * inp.alphabetSize ∧
    inp.depthBase = inp.failBase + inp.maxS ∧
    inp.termBase = inp.depthBase + inp.maxS ∧
    inp.outHeadBase = inp.termBase + inp.maxS ∧
    inp.outNextBase = inp.outHeadBase + inp.maxS ∧
    inp.queueBase = inp.outNextBase + inp.maxS ∧
    inp.outBase = inp.queueBase + inp.maxS :=
  by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fits_of_le_outBase {inp : Input} {w v : ℕ} (hw : Fits w inp.wordBound)
    (hv : v ≤ inp.outBase) : Fits w v :=
  hw.of_le (by have := wordBound_eq_outBase inp; omega)

namespace Reg

/-- Alphabet size register `σ`. -/
abbrev sigma : Fin 26 := 0
/-- Keyword count register `|P|`. -/
abbrev numPat : Fin 26 := 1
/-- Total keyword length register `‖P‖`. -/
abbrev totPat : Fin 26 := 2
/-- Text length register `|t|`. -/
abbrev textLen : Fin 26 := 3
/-- Maximum trie state count register `maxS = ‖P‖ + 1`. -/
abbrev maxS : Fin 26 := 4
/-- Base address register for the serialized keyword array (`5`). -/
abbrev patBase : Fin 26 := 5
/-- Base address register for the text array (`Input.textBase`). -/
abbrev textBase : Fin 26 := 6
/-- Base address register for the goto table (`Input.trieBase`). -/
abbrev trieBase : Fin 26 := 7
/-- Base address register for the next-move table (`Input.deltaBase`). -/
abbrev deltaBase : Fin 26 := 8
/-- Base address register for the failure-link array (`Input.failBase`). -/
abbrev failBase : Fin 26 := 9
/-- Base address register for the state-depth array (`Input.depthBase`). -/
abbrev depthBase : Fin 26 := 10
/-- Base address register for the terminal-state array (`Input.termBase`). -/
abbrev termBase : Fin 26 := 11
/-- Base address register for the output-chain head array (`Input.outHeadBase`). -/
abbrev outHeadBase : Fin 26 := 12
/-- Base address register for the output-chain `next` array (`Input.outNextBase`). -/
abbrev outNextBase : Fin 26 := 13
/-- Base address register for the BFS FIFO queue (`Input.queueBase`). -/
abbrev queueBase : Fin 26 := 15
/-- Constant-zero register (`0`). -/
abbrev zero : Fin 26 := 16
/-- Constant-one register (`1`). -/
abbrev one : Fin 26 := 17
/-- Scratch register holding the current state counter or automaton state. -/
abbrev rState : Fin 26 := 18
/-- Scratch register `r1` (`Fin 26`). -/
abbrev r1 : Fin 26 := 19
/-- Scratch register `r2` (`Fin 26`). -/
abbrev r2 : Fin 26 := 20
/-- Scratch register `r3` (`Fin 26`). -/
abbrev r3 : Fin 26 := 21
/-- Scratch register `r4` (`Fin 26`). -/
abbrev r4 : Fin 26 := 22
/-- Scratch register `r5` (`Fin 26`). -/
abbrev r5 : Fin 26 := 23
/-- Scratch register `r6` (`Fin 26`). -/
abbrev r6 : Fin 26 := 24
/-- Scratch register `r7` (`Fin 26`). -/
abbrev r7 : Fin 26 := 25

end Reg

open Reg

/-- Invariant asserting that the 18 read-only layout registers (`0..17`) hold `inp`'s constants
and workspace base addresses. -/
structure LayoutInv (inp : Input) (x : Data 26) : Prop where
  h_sigma : x.regs sigma = inp.alphabetSize
  h_numPat : x.regs numPat = inp.patterns.length
  h_totPat : x.regs totPat = totalPatternLen inp.patterns
  h_textLen : x.regs textLen = inp.text.length
  h_maxS : x.regs maxS = inp.maxS
  h_patBase : x.regs patBase = 5
  h_textBase : x.regs textBase = inp.textBase
  h_trieBase : x.regs trieBase = inp.trieBase
  h_deltaBase : x.regs deltaBase = inp.deltaBase
  h_failBase : x.regs failBase = inp.failBase
  h_depthBase : x.regs depthBase = inp.depthBase
  h_termBase : x.regs termBase = inp.termBase
  h_outHeadBase : x.regs outHeadBase = inp.outHeadBase
  h_outNextBase : x.regs outNextBase = inp.outNextBase
  h_out : x.regs out = inp.outBase
  h_queueBase : x.regs queueBase = inp.queueBase
  h_zero : x.regs zero = 0
  h_one : x.regs one = 1

theorem LayoutInv.of_preserves {inp : Input} {x y : Data 26} {w t : ℕ}
    {c : Code .standard 26} (hL : LayoutInv inp x) (he : ExecWithin w c x y t)
    (hk : 18 ≤ c.writeStart := by decide) : LayoutInv inp y where
  h_sigma := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_sigma
  h_numPat := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_numPat
  h_totPat := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_totPat
  h_textLen := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_textLen
  h_maxS := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_maxS
  h_patBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_patBase
  h_textBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_textBase
  h_trieBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_trieBase
  h_deltaBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_deltaBase
  h_failBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_failBase
  h_depthBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_depthBase
  h_termBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_termBase
  h_outHeadBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_outHeadBase
  h_outNextBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_outNextBase
  h_out := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_out
  h_queueBase := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_queueBase
  h_zero := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_zero
  h_one := (he.regs_eq (c.preserves_of_writeStart hk (by decide))).trans hL.h_one

end Cslib.Algorithms.WordRAM.AhoCorasick
