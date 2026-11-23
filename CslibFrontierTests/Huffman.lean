/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.Huffman.TwoQueue
import CslibFrontier.Algorithms.WordRAM.Huffman
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

meta import CslibFrontier.Algorithms.Lean.Huffman.TwoQueue
meta import CslibFrontier.Algorithms.WordRAM.Huffman
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval

/-!
# Tests for Huffman Coding, Kraft Converse, and Word-RAM Two-Queue Construction
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Huffman

open Cslib.WordRAM
open Cslib.Algorithms.Lean.Huffman
open Cslib.Algorithms.WordRAM.Huffman

/-! ## 1. Classic CLRS Figure 16.5 six-symbol example (`a:45, b:13, c:12, d:16, e:9, f:5`) -/

private meta def clrsSyms : List Char := ['a', 'b', 'c', 'd', 'e', 'f']

private meta def clrsWeight : Char → ℕ
  | 'a' => 45
  | 'b' => 13
  | 'c' => 12
  | 'd' => 16
  | 'e' => 9
  | 'f' => 5
  | _ => 0

-- Exact optimal weighted external path length `224` (vs `300` for a 3-bit fixed-length code).
#guard
  match huffman clrsWeight clrsSyms with
  | some T => T.weightedPathLength clrsWeight == 224 && T.maxDepth == 4
  | none => false

-- Bit-stream round-trip and empirical bit-length identity.
#guard
  match huffman clrsWeight clrsSyms with
  | some T =>
    let msg : List Char := "abacadaeaf".toList
    match T.encode msg with
    | some bits =>
      T.decode bits == some msg &&
        bits.length == T.weightedPathLength (fun c => msg.count c)
    | none => false
  | none => false

-- Degenerate `n = 0` and `n = 1` inputs.
#guard huffman (id : ℕ → ℕ) [] == none
#guard huffman (id : ℕ → ℕ) [42] == some (.leaf 42)

/-! ## 2. Word-RAM `O(n)` pre-sorted and `O(n log n)` unsorted Huffman programs -/

private meta def evalFromSorted (w : ℕ) (ws : List ℕ) : Option (List ℕ × ℕ) :=
  (fromSortedCode.eval w 512 (Data.init ws)).map fun (x, t) =>
    (outputList x.mem (x.regs Reg.out), t + 1)

private meta def evalHuffman (w : ℕ) (ws : List ℕ) : Option (List ℕ × ℕ) :=
  (huffmanCode.eval w 512 (Data.init ws)).map fun (x, t) =>
    (outputList x.mem (x.regs Reg.out), t + 1)

-- Boundary `n = 0`, `n = 1`, `n = 2`, zero weights, and `n = 6` Fibonacci sorted runs
-- within `57 * n + 24` steps.
#guard (evalFromSorted 64 []).map Prod.fst == some []
#guard (evalFromSorted 64 [42]).map Prod.fst == some [0]
#guard (evalFromSorted 64 [0, 0]).map Prod.fst == some [1, 1]
#guard (evalFromSorted 64 [0, 0, 5]).map Prod.fst == some [2, 2, 1]
#guard (evalFromSorted 64 [3, 5]).map Prod.fst == some [1, 1]
#guard
  match evalFromSorted 64 [1, 1, 2, 3, 5, 8] with
  | some (lens, steps) =>
    lens == [5, 5, 4, 3, 2, 1] && steps ≤ 57 * 6 + 24
  | none => false

-- Unsorted Word-RAM runs: `n = 0`, `n = 1`, unsorted `n = 2` (`[8, 3]`), zero weights (`[0, 0]` and
-- `[5, 0, 0, 3]`), equal weights, and CLRS `[45, 13, 12, 16, 9, 5]` at tight word width `w = 7`
-- (`10 * 6 + 3 = 63 < 128` and `ws.sum = 100 < 128`, whereas `6 * 100 = 600` overflows 7 bits).
#guard (evalHuffman 64 []).map Prod.fst == some []
#guard (evalHuffman 64 [42]).map Prod.fst == some [0]
#guard (evalHuffman 8 [8, 3]).map Prod.fst == some [1, 1]
#guard (evalHuffman 8 [0, 0]).map Prod.fst == some [1, 1]
#guard (evalHuffman 8 [5, 0, 0, 3]).map Prod.fst == some [1, 3, 3, 2]
#guard (evalHuffman 64 [5, 5, 5, 5]).map Prod.fst == some [2, 2, 2, 2]
#guard
  match evalHuffman 7 [45, 13, 12, 16, 9, 5] with
  | some (lens, steps) =>
    lens == [1, 3, 3, 3, 4, 4] &&
      (List.zipWith (· * ·) lens [45, 13, 12, 16, 9, 5]).sum == 224 &&
      steps ≤ 52 * 6 * Nat.clog 2 6 + 82 * 6 + 47
  | none => false

-- Checked non-vacuity of `fromSortedCode_exec` / `fromSortedProgram_spec` (including `ws = [0, 0]`)
-- and `huffmanCode_exec` / `huffmanProgram_spec` at tight fitting word width `w = 7`.
example :
    let ws : List ℕ := [1, 1, 2, 3, 5, 8]
    (∃ y lens, ExecWithin 6 fromSortedCode (Data.init ws) y (57 * ws.length + 23) ∧
      Block.HoldsList 1 ws y.mem ∧ outputList y.mem (y.regs Reg.out) = lens ∧
      lens.length = ws.length) ∧
    (∃ lens steps,
      ExecutesList 6 fromSortedProgram (.init [0, 0]) lens steps ∧
      steps ≤ 57 * 2 + 24 ∧ lens.length = 2) := by
  intro ws
  obtain ⟨y, lens, hexC, hhold, _, hout, hlen, _, _⟩ :=
    fromSortedCode_exec (w := 6) ws (by decide) (by decide)
  obtain ⟨lens0, steps0, hex0, hst0, hlen0, _, _⟩ :=
    fromSortedProgram_spec (w := 6) [0, 0] (by decide) (by decide)
  exact ⟨⟨y, lens, hexC, hhold, hout, hlen⟩, ⟨lens0, steps0, hex0, hst0, hlen0⟩⟩

example :
    let ws : List ℕ := [45, 13, 12, 16, 9, 5]
    (∃ y lens,
      ExecWithin 7 huffmanCode (Data.init ws) y
        (52 * ws.length * Nat.clog 2 ws.length + 82 * ws.length + 46) ∧
      Block.HoldsList 1 ws y.mem ∧ outputList y.mem (y.regs Reg.out) = lens) ∧
    (∃ lens steps,
      ExecutesList 7 huffmanProgram (.init ws) lens steps ∧
      steps ≤ 52 * ws.length * Nat.clog 2 ws.length + 82 * ws.length + 47 ∧
      lens.length = ws.length) := by
  intro ws
  have hmem : Fits 7 (10 * ws.length + 3) := by decide
  have hsum : Fits 7 ws.sum := by decide
  obtain ⟨y, lensC, hexC, hhold, _, hout, _, _, _⟩ := huffmanCode_exec ws hmem hsum
  obtain ⟨lens, steps, hex, hst, hlen, _, _⟩ := huffmanProgram_spec ws hmem hsum
  exact ⟨⟨y, lensC, hexC, hhold, hout⟩, ⟨lens, steps, hex, hst, hlen⟩⟩

/-! ## 3. Constructive binary Kraft assignment and unary-trie compaction -/

private meta def kraftDemoLen : Fin 4 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 3

-- Dyadic Kraft construction for `[1, 2, 3, 3]` (`1/2 + 1/4 + 1/8 + 1/8 = 1`) produces
-- `[false], [true, false], [true, true, false], [true, true, true]`.
#guard
  (kraftAssign 3 kraftDemoLen 0 [0, 1, 2, 3]).map Prod.snd ==
    [[false], [true, false], [true, true, false], [true, true, true]]

-- Unary-node compaction: `[(0, [false, false]), (1, [false, true])]` contracts to
-- `.branch (.leaf 0) (.leaf 1)` and strictly lowers weighted path length from `2 * (3 + 5) = 16`
-- to `1 * (3 + 5) = 8`.
#guard
  treeOfCodebook [(0, [false, false]), (1, [false, true])] ==
    some (.branch (.leaf 0) (.leaf 1))

-- Kraft theorem negative direction: lengths `(1, 1, 2)` on `Fin 3` have Kraft sum `5/4 > 1`, so no
-- injective prefix-free binary code exists.
example : ¬ ∃ code : Fin 3 → List Bool,
    Set.InjOn code ↑(Finset.univ : Finset (Fin 3)) ∧
    InformationTheory.IsPrefixFree (code '' ↑(Finset.univ : Finset (Fin 3))) ∧
    ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      (code a).length = match a with | 0 => 1 | 1 => 1 | 2 => 2 := by
  rw [exists_isPrefixFree_iff_kraft_le_one]
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have hsum : (∑ a ∈ (Finset.univ : Finset (Fin 3)),
      (1 / 2 : ℝ) ^ (match a with | 0 => 1 | 1 => 1 | 2 => 2)) = 5 / 4 := by
    rw [huniv]
    norm_num
  linarith

/-! ## 4. Full-tree optimality with negative weights (`ℤ`) -/

-- Witness that `IsHuffmanBuild.weightedPathLength_le` requires neither `0 ≤ w a` nor `Nodup`:
-- merging `(-5)` and `(-2)` first achieves path length `2 * (-5) + 2 * (-2) + 1 * 3 = -11`,
-- beating merging `(-2)` and `3` first (`1 * (-5) + 2 * (-2) + 2 * 3 = -3`).
example :
    let w : Fin 3 → ℤ := ![(-5), (-2), 3]
    let T_huff : CodeTree (Fin 3) := .branch (.branch (.leaf 0) (.leaf 1)) (.leaf 2)
    let T_subopt : CodeTree (Fin 3) := .branch (.leaf 0) (.branch (.leaf 1) (.leaf 2))
    IsHuffmanBuild w ([0, 1, 2].map .leaf) T_huff ∧
      T_huff.weightedPathLength w ≤ T_subopt.weightedPathLength w := by
  intro w T_huff T_subopt
  have hmin1 : IsMinPair w ([0, 1, 2].map .leaf) (.leaf 0) (.leaf 1) [.leaf 2] := by
    refine ⟨List.Perm.refl _, ?_⟩
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    simp [w]
  have hmin2 : IsMinPair w [CodeTree.branch (.leaf 0) (.leaf 1), .leaf 2]
      (.branch (.leaf 0) (.leaf 1)) (.leaf 2) [] :=
    ⟨List.Perm.refl _, fun _ h => False.elim (List.not_mem_nil h)⟩
  have hbuild : IsHuffmanBuild w ([0, 1, 2].map .leaf) T_huff :=
    .step hmin1 (.step hmin2 (.single T_huff))
  exact ⟨hbuild, hbuild.weightedPathLength_le T_subopt (List.Perm.refl _)⟩

/-! ## 5. Optimality against a non-prefix-free uniquely decodable suffix code -/

-- Reversed prefix code `{[false], [false, true], [true, true]}` on `Fin 3`:
-- NOT `IsPrefixFree` (`[false] <+: [false, true]`), yet `IsUniquelyDecodable` because its reversal
-- `{[false], [true, false], [true, true]}` is prefix-free without `[]`!
private def suffixCode : Fin 3 → List Bool
  | 0 => [false]
  | 1 => [false, true]
  | 2 => [true, true]

private def revPrefixCode : Fin 3 → List Bool
  | 0 => [false]
  | 1 => [true, false]
  | 2 => [true, true]

private theorem not_isPrefixFree_suffixCode :
    ¬ InformationTheory.IsPrefixFree
      (suffixCode '' {a : Fin 3 | a ∈ ([0, 1, 2] : List (Fin 3))}) := by
  intro hpf
  have h0 : suffixCode 0 ∈ suffixCode '' {a : Fin 3 | a ∈ ([0, 1, 2] : List (Fin 3))} :=
    ⟨0, by simp, rfl⟩
  have h1 : suffixCode 1 ∈ suffixCode '' {a : Fin 3 | a ∈ ([0, 1, 2] : List (Fin 3))} :=
    ⟨1, by simp, rfl⟩
  have hEq := hpf _ h0 _ h1 ⟨[true], rfl⟩
  simp [suffixCode] at hEq

private theorem flatten_reverse_map_reverse {α : Type*} (L : List (List α)) :
    (L.reverse.map List.reverse).flatten = L.flatten.reverse := by
  induction L with
  | nil => rfl
  | cons w ws ih =>
    rw [List.reverse_cons, List.map_append, List.flatten_append, ih]
    simp

private theorem isUniquelyDecodable_suffixCode :
    InformationTheory.IsUniquelyDecodable
      (suffixCode '' {a : Fin 3 | a ∈ ([0, 1, 2] : List (Fin 3))}) := by
  let S_rev : Set (List Bool) :=
    revPrefixCode '' {a : Fin 3 | a ∈ ([0, 1, 2] : List (Fin 3))}
  have hpf_dec : ∀ i j : Fin 3, revPrefixCode i <+: revPrefixCode j →
      revPrefixCode i = revPrefixCode j := by decide
  have hpf_rev : InformationTheory.IsPrefixFree S_rev := by
    rintro _ ⟨i, _, rfl⟩ _ ⟨j, _, rfl⟩ hpref
    exact hpf_dec i j hpref
  have hnil_dec : ∀ i : Fin 3, revPrefixCode i ≠ [] := by decide
  have hnil_rev : [] ∉ S_rev := by
    rintro ⟨i, _, hi⟩
    exact hnil_dec i hi
  have hud_rev := hpf_rev.isUniquelyDecodable hnil_rev
  intro L₁ L₂ hL₁ hL₂ hflat
  have hrev_eq : ∀ i : Fin 3, (suffixCode i).reverse = revPrefixCode i := by decide
  have hmem_rev : ∀ {L : List (List Bool)},
      (∀ w ∈ L, w ∈ suffixCode '' {a : Fin 3 | a ∈ ([0, 1, 2] : List (Fin 3))}) →
      ∀ u ∈ L.reverse.map List.reverse, u ∈ S_rev := by
    intro L hL u hu
    rcases List.mem_map.mp hu with ⟨w, hw, rfl⟩
    rcases hL w (List.mem_reverse.mp hw) with ⟨i, hi, rfl⟩
    exact ⟨i, hi, (hrev_eq i).symm⟩
  have hflat_rev : (L₁.reverse.map List.reverse).flatten =
      (L₂.reverse.map List.reverse).flatten := by
    rw [flatten_reverse_map_reverse, flatten_reverse_map_reverse, hflat]
  have hEq_rev := hud_rev _ _ (hmem_rev hL₁) (hmem_rev hL₂) hflat_rev
  have hmap_inj : ∀ {A B : List (List Bool)},
      A.map List.reverse = B.map List.reverse → A = B := by
    intro A B hAB
    have := congrArg (List.map List.reverse) hAB
    simpa [List.map_map, Function.comp_def, List.reverse_reverse] using this
  exact List.reverse_injective (hmap_inj hEq_rev)

-- Instantiate `huffman_optimal_isUniquelyDecodable` against the non-prefix-free `suffixCode`!
example :
    let syms : List (Fin 3) := [0, 1, 2]
    let w : Fin 3 → ℕ := ![5, 7, 10]
    ∃ T, huffman w syms = some T ∧
      T.weightedPathLength w ≤ (syms.map fun a => (suffixCode a).length • w a).sum := by
  intro syms w
  have hne : syms ≠ [] := by decide
  have hnodup : syms.Nodup := by decide
  have hw : ∀ a ∈ syms, 0 ≤ w a := fun _ _ => Nat.zero_le _
  have hinj_dec : ∀ i j : Fin 3, suffixCode i = suffixCode j → i = j := by decide
  have hinj : Set.InjOn suffixCode {a | a ∈ syms} := fun i _ j _ hEq => hinj_dec i j hEq
  rcases huffman_spec hne hw with ⟨T, hT, _, _⟩
  exact ⟨T, hT, huffman_optimal_isUniquelyDecodable hne hnodup hw hT hinj
    isUniquelyDecodable_suffixCode⟩

end CslibFrontierTests.Huffman
