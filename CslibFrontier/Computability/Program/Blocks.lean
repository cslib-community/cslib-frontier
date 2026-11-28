/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger, Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger, Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Indexed assembly of finite instruction blocks

The assembler is independent of the source and target instruction types. Fixed block lengths
provide exact prefix offsets; forward and reverse machine compilers share this construction.
-/

public section
namespace Cslib.Program
variable {α β : Type*}

/-- Concatenate compiled blocks, numbering source instructions from `start`. -/
@[expose] def compileBlocks (block : ℕ → α → List β) :
    ℕ → List α → List β
  | _, [] => []
  | start, i :: code => block start i ++ compileBlocks block (start + 1) code

/-- Fixed-size blocks give a target program of length `k * code.length`. -/
theorem length_compileBlocks {block : ℕ → α → List β} {k : ℕ} {code : List α}
    (hblock : ∀ pc i, i ∈ code → (block pc i).length = k) (start : ℕ) :
    (compileBlocks block start code).length = k * code.length := by
  induction code generalizing start with
  | nil => simp [compileBlocks]
  | cons i code ih =>
    simp [compileBlocks, hblock start i List.mem_cons_self,
      ih (fun pc j hj => hblock pc j (List.mem_cons_of_mem i hj)) (start + 1), Nat.mul_succ,
      Nat.add_comm]

/-- An indexed block occurs after a prefix of exactly `k * j` target instructions. -/
theorem compileBlocks_decompose {block : ℕ → α → List β} {k start j : ℕ}
    {code : List α} {i : α}
    (hblock : ∀ pc a, a ∈ code → (block pc a).length = k) (hi : code[j]? = some i) :
    ∃ pre post, pre.length = k * j ∧
      compileBlocks block start code = pre ++ (block (start + j) i ++ post) := by
  induction code generalizing start j with
  | nil => simp at hi
  | cons a code ih =>
    cases j with
    | zero =>
      obtain rfl : a = i := by simpa using hi
      exact ⟨[], compileBlocks block (start + 1) code, rfl, rfl⟩
    | succ j =>
      obtain ⟨pre, post, len, eq⟩ := ih
        (fun pc a ha => hblock pc a (List.mem_cons_of_mem _ ha))
        (by simpa using hi) (start := start + 1)
      exact ⟨block start a ++ pre, post,
        by simp [hblock start a List.mem_cons_self, len, Nat.mul_succ, Nat.add_comm],
        by simp [compileBlocks, eq, List.append_assoc, Nat.add_left_comm, Nat.add_comm]⟩

/-- Fetch within a fixed-size compiled block agrees with fetching inside that block. -/
theorem getElem?_compileBlocks {block : ℕ → α → List β} {k start j n : ℕ}
    {code : List α} {i : α} {instruction : β}
    (hblock : ∀ pc a, a ∈ code → (block pc a).length = k) (hi : code[j]? = some i)
    (localGet : (block (start + j) i)[n]? = some instruction) :
    (compileBlocks block start code)[k * j + n]? = some instruction := by
  obtain ⟨pre, post, len, eq⟩ := compileBlocks_decompose hblock hi (start := start)
  rwa [eq, ← len, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (List.getElem?_eq_some_iff.mp localGet).1]

end Cslib.Program
