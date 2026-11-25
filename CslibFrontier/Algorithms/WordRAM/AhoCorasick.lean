/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.AhoCorasick.Basic
public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Input
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Structured
import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Code
import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Layout
import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Phase1Setup
import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Phase2Trie
import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Phase3Loop
import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Phase4Scan

/-!
# Aho–Corasick Multi-Pattern Matching on the Word-RAM

Linear-time implementation of the Aho–Corasick multi-pattern string matching machine
(`[AhoCorasick1975]`, Algorithms 1, 2, and 3 and Section 6) on the `Basis.standard` Word-RAM over
bounded integer alphabets `[0, σ)`:

1. **Array-trie construction** inserts all keywords `P` (`|P|` keywords of total length
   `‖P‖ = totalPatternLen P`) into a flat `(‖P‖ + 1) × σ` integer-state goto table with root `0`
   in `O((‖P‖ + 1) · σ + |P|)` instructions.
2. **Breadth-first failure, next-move, and output-link construction** populates `fail[s]`,
   `delta[s * σ + a]`, `outHead[s]`, and `outNext[s]` over an explicit FIFO queue in
   `O((‖P‖ + 1) · σ)` instructions, visiting each shared trie state once.
3. **Amortized text scanning** executes Algorithm 1 along `trie` and `fail` using the failure-depth
   potential `depth[u]` (`[AhoCorasick1975]`, Theorem 2) and emits each reported keyword occurrence
   as `[endPos, keywordLen]` via `outHead` / `outNext` in `O(|t| + occ)` instructions (independent
   of `σ` during the scan).

The implementation and proof are organized into focused submodules under
`CslibFrontier.Algorithms.WordRAM.AhoCorasick`:

* `AhoCorasick.Input`: public `Input`, encodings/decoders, `wordBound`, `searchTime`, and `Reg.out`.
* `AhoCorasick.TrieModel`: pure integer-state trie model `PTrie` and `TreeInv`.
* `AhoCorasick.BFSModel`: pure breadth-first state `PBFS`, `followOut`, and root-loop pass.
* `AhoCorasick.BFSCorrect`: pure `BFSInv` / `AutomatonInv` correctness proof for `PBFS.build`.
* `AhoCorasick.Layout`: workspace base addresses, register aliases, and `LayoutInv`.
* `AhoCorasick.Code`: structured `Code .standard 26` blocks for all four phases.
* `AhoCorasick.Phase1Setup`: `TrieMem` and header-decode / zero-fill proof (`setupAndClearCode`).
* `AhoCorasick.Phase2Trie`: flat array-trie construction proof (`buildTrieCode`).
* `AhoCorasick.Phase3Mem`: `BFSMem`, table-update lemmas, and depth-1 root loop proof.
* `AhoCorasick.Phase3Loop`: inner/outer BFS loop proof (`bfsBuildCode`).
* `AhoCorasick.Phase4Step`: amortized failure-link step proof (`stepCode`).
* `AhoCorasick.Phase4Scan`: output-link emission and full text-scan proof (`scanCode`).

## Main definitions

* `Cslib.Algorithms.WordRAM.AhoCorasick.Input`: integer-alphabet multi-pattern matching instance.
* `Cslib.Algorithms.WordRAM.AhoCorasick.totalPatternLen`: total keyword length `‖P‖`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.Valid`: alphabet validity `< σ`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.encodePatterns`, `Input.encode`: flat word-array input
  encoding.
* `Cslib.Algorithms.WordRAM.AhoCorasick.encodeOccurrences`, `decodeOccurrences`: flat `[pos, len]`
  occurrence encoding and lossless decoder.
* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.wordBound`, `searchTime`: word-width threshold and
  instruction bound.
* `Cslib.Algorithms.WordRAM.AhoCorasick.Reg.out`: output header register.
* `Cslib.Algorithms.WordRAM.AhoCorasick.searchCode`, `searchProgram`: structured and flat Word-RAM
  Aho–Corasick multi-pattern matcher.

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.decodeOccurrences_encodeOccurrences`: `decodeOccurrences t`
  recovers `occurrences P t` from `encodeOccurrences (occurrences P t)`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.wordBound_le`: polynomial upper bound on `inp.wordBound`
  independent of `occ`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.Valid.inputFits`: `InputFits w inp.encode` from
  `inp.Valid` and `Fits w inp.wordBound`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.searchCode_exec`, `searchProgram_computesListInTime`,
  `searchProgram_executesList`: linear `O((‖P‖ + 1) · σ + |P| + |t| + occ)` Word-RAM running time.

## References

* [A. V. Aho and M. J. Corasick, *Efficient String Matching: An Aid to Bibliographic
  Search*][AhoCorasick1975]
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.WordRAM
open Cslib.Algorithms.Lean.AhoCorasick
open Reg

/-- Structured Word-RAM implementation of Aho–Corasick multi-pattern string matching:
initializes and clears the scratch tables, builds the array trie, runs breadth-first failure,
next-move, and output-link construction, and scans the text emitting `[endPos, keywordLen]` pairs
at `Reg.out`. -/
def searchCode : Code .standard 26 :=
  .seq setupAndClearCode (.seq buildTrieCode (.seq bfsBuildCode scanCode))

/-- Flat Word-RAM program computing `encodeOccurrences (occurrences inp.patterns inp.text)` from
`inp.encode`. -/
def searchProgram : Program .standard 26 :=
  searchCode.program out

/-! ## Top-level Word-RAM running-time theorems -/

/-- `searchCode` computes `encodeOccurrences (occurrences inp.patterns inp.text)` at `Reg.out`
within `searchTime inp - 1` instructions at any word width `w` with `Fits w inp.wordBound`. -/
theorem searchCode_exec (inp : Input) (w : ℕ)
    (hvalid : inp.Valid) (hw : Fits w inp.wordBound) :
    ∃ y, ExecWithin w searchCode (.init inp.encode) y (searchTime inp - 1) ∧
      outputList y.mem (y.regs out) =
        encodeOccurrences (occurrences inp.patterns inp.text) ∧
      Fits w (y.regs out + (encodeOccurrences (occurrences inp.patterns inp.text)).length) := by
  obtain ⟨x₁, he₁, hL₁, hM₁⟩ := exec_setupAndClear inp w hw
  obtain ⟨x₂, he₂, hL₂, hM₂⟩ := exec_buildTrie inp w hvalid hw x₁ hL₁ hM₁
  obtain ⟨x₃, he₃, hL₃, hM₃⟩ := exec_bfsBuild inp w hvalid hw x₂ hL₂ hM₂
  obtain ⟨y, he₄, hLy, hout⟩ := exec_scanCode inp w hvalid hw x₃ hL₃ hM₃
  have hcost :
      (8 * inp.maxS * inp.alphabetSize + 24 * inp.maxS + 31) +
        ((19 * inp.maxS + 11 * inp.patterns.length + 5) +
          ((52 * inp.maxS * inp.alphabetSize + 10 * inp.maxS + 7) +
            (38 * inp.text.length + 10 * (occurrences inp.patterns inp.text).length + 8))) ≤
      searchTime inp - 1 := by
    have hmaxS := (layout_order inp).1
    dsimp only [searchTime]
    rw [hmaxS]
    simp only [Nat.mul_assoc]
    omega
  refine ⟨y, (he₁.seq (he₂.seq (he₃.seq he₄))).mono hcost, hout, ?_⟩
  rw [hLy.h_out, length_encodeOccurrences]
  exact hw.of_le (by rw [wordBound_eq_outBase]; omega)

/-- `searchProgram` computes `encodeOccurrences (occurrences inp.patterns inp.text)` within
`searchTime inp = O((‖P‖ + 1) · σ + |P| + |t| + occ)` instructions at any fitting width with
`inp.Valid` and `Fits w inp.wordBound`. -/
theorem searchProgram_computesListInTime :
    searchProgram.ComputesListInTime
      (fun _ (inp : Input) => inp.encode)
      (fun inp _ => searchTime inp)
      (fun inp w => inp.Valid ∧ Fits w inp.wordBound)
      (fun inp => encodeOccurrences (occurrences inp.patterns inp.text)) :=
  searchCode.computesListInTime_program out fun inp w ⟨hvalid, hw⟩ _ =>
    searchCode_exec inp w hvalid hw

/-- Direct `ExecutesList` corollary for `searchProgram` discharging `InputFits` automatically from
`inp.Valid` and `Fits w inp.wordBound`. -/
theorem searchProgram_executesList (inp : Input) (w : ℕ)
    (hvalid : inp.Valid) (hw : Fits w inp.wordBound) :
    ∃ t, ExecutesList w searchProgram (.init inp.encode)
        (encodeOccurrences (occurrences inp.patterns inp.text)) t ∧
      t ≤ searchTime inp :=
  searchProgram_computesListInTime inp w ⟨hvalid, hw⟩ (hvalid.inputFits hw)

end Cslib.Algorithms.WordRAM.AhoCorasick
