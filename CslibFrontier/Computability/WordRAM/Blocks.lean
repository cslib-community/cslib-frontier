/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger, Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger, Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Compile

/-!
# Placing fixed-size instruction blocks

`Program.compileBlocks` concatenates target blocks, passing each block its source instruction
index. When every block has length `k`, `Program.Contains.block` locates source instruction `j`
at target offset `k * j`, including inside a larger target program. Compilers supply their own
relocated branches and any padding required to obtain the fixed block length.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ} {α : Type*}

/-- Concatenate compiled blocks, numbering source instructions from `start`. -/
@[expose] def Program.compileBlocks (block : ℕ → α → Program B r) :
    ℕ → List α → Program B r
  | _, [] => []
  | start, i :: code => block start i ++ compileBlocks block (start + 1) code

/-- Fixed-size blocks give a target program of length `k * code.length`. -/
theorem Program.length_compileBlocks {block : ℕ → α → Program B r} {k : ℕ} {code : List α}
    (hblock : ∀ pc i, i ∈ code → (block pc i).length = k) (start : ℕ) :
    (compileBlocks block start code).length = k * code.length := by
  induction code generalizing start with
  | nil => simp [compileBlocks]
  | cons i code ih =>
    have ht := ih (fun pc j hj => hblock pc j (List.mem_cons_of_mem i hj)) (start + 1)
    simp only [compileBlocks, List.length_append, List.length_cons,
      hblock start i (List.mem_cons_self), ht, Nat.mul_succ]
    omega

/-- Locate the compiled block for an indexed source instruction within a containing program. -/
theorem Program.Contains.block {block : ℕ → α → Program B r} {k base start j : ℕ}
    {q : Program B r} {code : List α} {i : α}
    (hq : q.Contains base (Program.compileBlocks block start code))
    (hblock : ∀ pc i, i ∈ code → (block pc i).length = k) (hi : code[j]? = some i) :
    q.Contains (base + k * j) (block (start + j) i) := by
  induction code generalizing start base j with
  | nil => simp at hi
  | cons a code ih =>
    simp only [Program.compileBlocks] at hq
    cases j with
    | zero =>
      have he : a = i := by simpa using hi
      subst i
      simpa only [Nat.mul_zero, Nat.add_zero] using hq.append_left
    | succ j =>
      have ht : q.Contains (base + k) (Program.compileBlocks block (start + 1) code) := by
        simpa only [hblock start a List.mem_cons_self] using hq.append_right
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih ht (fun pc i hi => hblock pc i (List.mem_cons_of_mem a hi)) (by simpa using hi)

end Cslib.WordRAM
