/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Internal cell-footprint predicate for flat Word-RAM binary tries

Internal `TrieRep` predicate and helper lemmas shared privately between `Basic` (defining
unexposed `HoldsTrie`), `Trie`, `InputTrie`, `Tabulate`, and `Stages`; never re-exported through
`TrimmedYates` or `TrimmedYates.Basic`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.TrieRep`: cell-footprint representation of a depth-`d`
  binary trie in flat word memory.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.TrieRep.congr_mem`, `TrieRep.zero_root`,
  `TrieRep.fresh_node`: memory framing, empty root, and fresh-node lemmas.
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

/-- `TrieRep mem d node S fn`: `node` is the root of a depth-`d` binary trie in `mem` with owned
cell footprint `S`, representing the function `fn : ℕ → ℕ` on low-`d`-bit keys. `node = 0` is the
empty trie returning `0` everywhere. Every allocated node occupies `{node, node + 1}` with
`0 < node`. -/
@[expose] def TrieRep (mem : ℕ → ℕ) : ℕ → ℕ → Set ℕ → (ℕ → ℕ) → Prop
  | 0, node, S, fn =>
    (node = 0 ∧ S = ∅ ∧ ∀ m, fn m = 0) ∨
    (0 < node ∧ S = {node, node + 1} ∧ ∀ m, fn m = mem node)
  | d + 1, node, S, fn =>
    (node = 0 ∧ S = ∅ ∧ ∀ m, fn m = 0) ∨
    (0 < node ∧ ∃ S₀ S₁ fn₀ fn₁,
      Disjoint ({node, node + 1} : Set ℕ) (S₀ ∪ S₁) ∧
      Disjoint S₀ S₁ ∧
      S = {node, node + 1} ∪ S₀ ∪ S₁ ∧
      TrieRep mem d (mem node) S₀ fn₀ ∧
      TrieRep mem d (mem (node + 1)) S₁ fn₁ ∧
      ∀ m, fn m = if m % 2 = 0 then fn₀ (m / 2) else fn₁ (m / 2))

/-- Memory writes outside `S` preserve `TrieRep`. -/
theorem TrieRep.congr_mem {mem mem' : ℕ → ℕ} {d node : ℕ} {S : Set ℕ} {fn : ℕ → ℕ}
    (h : TrieRep mem d node S fn) (heq : ∀ a ∈ S, mem' a = mem a) :
    TrieRep mem' d node S fn := by
  induction d generalizing node S fn with
  | zero =>
    rcases h with ⟨rfl, rfl, hfn⟩ | ⟨hpos, rfl, hfn⟩
    · exact Or.inl ⟨rfl, rfl, hfn⟩
    · refine Or.inr ⟨hpos, rfl, fun m => ?_⟩
      rw [hfn m, heq node (by simp)]
  | succ d ih =>
    rcases h with ⟨rfl, rfl, hfn⟩ | ⟨hpos, S₀, S₁, fn₀, fn₁, hd₀, hd₁, rfl, ht₀, ht₁, hfn⟩
    · exact Or.inl ⟨rfl, rfl, hfn⟩
    · refine Or.inr ⟨hpos, S₀, S₁, fn₀, fn₁, hd₀, hd₁, rfl, ?_, ?_, hfn⟩
      · rw [heq node (by simp)]
        exact ih ht₀ fun a ha => heq a (by simp [ha])
      · rw [heq (node + 1) (by simp)]
        exact ih ht₁ fun a ha => heq a (by simp [ha])

/-- Address `0` represents the identically zero trie with empty cell footprint. -/
theorem TrieRep.zero_root (mem : ℕ → ℕ) (d : ℕ) :
    TrieRep mem d 0 ∅ (fun _ => 0) := by
  cases d <;> exact Or.inl ⟨rfl, rfl, fun _ => rfl⟩

/-- Fresh zero-initialized two-word node represents the identically zero trie. -/
theorem TrieRep.fresh_node {mem : ℕ → ℕ} (d : ℕ) {node : ℕ} (hpos : 0 < node)
    (h0 : mem node = 0) (h1 : mem (node + 1) = 0) :
    TrieRep mem d node {node, node + 1} (fun _ => 0) := by
  cases d with
  | zero => exact Or.inr ⟨hpos, rfl, fun _ => h0.symm⟩
  | succ d =>
    refine Or.inr ⟨hpos, ∅, ∅, fun _ => 0, fun _ => 0, by simp, by simp, by simp, ?_, ?_,
      fun _ => by split_ifs <;> rfl⟩
    · rw [h0]; exact TrieRep.zero_root mem d
    · rw [h1]; exact TrieRep.zero_root mem d

end Cslib.Algorithms.WordRAM.TrimmedYates
