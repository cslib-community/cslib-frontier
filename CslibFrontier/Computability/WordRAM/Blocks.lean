/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger, Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger, Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Computability.Program.Blocks

/-!
# Placing fixed-size instruction blocks

`Cslib.Program.compileBlocks` concatenates target blocks, passing each block its source instruction
index. When every block has length `k`, `Program.Contains.block` locates source instruction `j`
at target offset `k * j`, including inside a larger target program. Compilers supply their own
relocated branches and any padding required to obtain the fixed block length.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ} {α : Type*}

/-- Locate the compiled block for an indexed source instruction within a containing program. -/
theorem Program.Contains.block {block : ℕ → α → Program B r} {k base start j : ℕ}
    {q : Program B r} {code : List α} {i : α}
    (hq : q.Contains base (Cslib.Program.compileBlocks block start code))
    (hblock : ∀ pc i, i ∈ code → (block pc i).length = k) (hi : code[j]? = some i) :
    q.Contains (base + k * j) (block (start + j) i) := by
  obtain ⟨pre, post, len, eq⟩ := Cslib.Program.compileBlocks_decompose hblock hi (start := start)
  rw [eq] at hq
  simpa only [len] using hq.append_right.append_left

end Cslib.WordRAM
