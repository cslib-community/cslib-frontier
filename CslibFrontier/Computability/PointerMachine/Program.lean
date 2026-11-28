/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Blocks
public import CslibFrontier.Computability.Program.Blocks

/-!
# Pointer-machine execution inside compiled programs

A certified halting routine can be embedded into an indexed, fixed-size compiled block.
The theorem charges its final continuation jump and allows unused padding after the routine.
-/

public section
namespace Cslib.PointerMachine
variable {M : Model} {L : Layout} {α : Type*}

/-- A routine placed at the start of a compiled block runs with unchanged cost. Padding is
not executed: the routine's final halt becomes a jump to the absolute continuation label. -/
theorem Executes.inCompiledBlock {block : ℕ → α → List (Instr M L)}
    {k start j next time : ℕ} {source : List α} {i : α}
    {body suffix : List (Instr M L)} {x y : State M L}
    (run : Executes body x y time)
    (size : ∀ pc a, a ∈ source → (block pc a).length = k) (get : source[j]? = some i)
    (placed : block (start + j) i = body.map (Instr.relocate (k * j) next) ++ suffix) :
    Runs (Cslib.Program.compileBlocks block start source)
      { x with pc := k * j + x.pc } { y with pc := next } time := by
  obtain ⟨pre, post, len, eq⟩ := Cslib.Program.compileBlocks_decompose size get (start := start)
  have embedded := run.inBlock pre (suffix ++ post) next
  rw [eq, placed]
  simpa only [len, List.append_assoc] using embedded

end Cslib.PointerMachine
