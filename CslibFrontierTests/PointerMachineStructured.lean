/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.Computability.PointerMachine.Assemble
import CslibFrontier.Computability.PointerMachine.SymbolicExec

/-! Structured pointer-machine programs: the notation, the assembled instructions, evaluation,
the loop rule, symbolic execution and frames read off the program text. -/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Cslib.PointerMachine

private abbrev model : Model where
  Value := ℕ
  undefined := 0
  Op := Unit
  Test := Unit
  evalOp _ a b := a + b
  evalTest _ a b := decide (a < b)

private abbrev L : Layout := ⟨2, 2, 1, 1⟩
private abbrev p : Fin 2 := 0
private abbrev q : Fin 2 := 1
private abbrev s : Fin 2 := 0
private abbrev t : Fin 2 := 1
private abbrev next : Fin 1 := 0
private abbrev val : Fin 1 := 0

/-! Every statement form unfolds to the constructors of `Code`. -/

example : (pm[ p ← null; q ← new; q[next] ← p; p ← q[next]; p ← q ] : Code model L) =
    .seq (.op (.null p)) (.seq (.op (.create q)) (.seq (.op (.storePtr next q p))
      (.seq (.op (.loadPtr p next q)) (.op (.movePtr p q))))) := rfl

example : (pm[ s := t; s := q[val]; q[val] := s; s := () s t ] : Code model L) =
    .seq (.op (.moveData s t)) (.seq (.op (.loadData s val q)) (.seq (.op (.storeData val q s))
      (.op (.op () s s t)))) := rfl

-- A negated test exchanges the alternatives of a conditional and selects the other loop.
example : (pm[ if p ≠ q then [ p ← q ] else [ q ← p ] ] : Code model L) =
    pm[ if p = q then [ q ← p ] else [ p ← q ] ] := rfl

example : (pm[ if ¬(()) s t then [ s := t ] ] : Code model L) =
    .branch (.data () s t) .skip (.op (.moveData s t)) := rfl

example : (pm[ while p ≠ q do [ p ← p[next] ] ] : Code model L) =
    .loopUntil (.ptrEq p q) (.op (.loadPtr p next p)) := rfl

example : (pm[ while ¬(()) s t do [ s := () s s ] ] : Code model L) =
    .loopUntil (.data () s t) (.op (.op () s s s)) := rfl

example : (pm[ while (()) s t do [ ⟪.skip⟫ ] ] : Code model L) =
    .loop (.data () s t) .skip := rfl

/-! Assembly: tests and jumps to absolute labels. -/

example : Code.program (pm[ while p ≠ q do [ p ← p[next] ] ] : Code model L) =
    [.ifPtrEq 0 1 3, .loadPtr 0 0 0, .goto 0, .halt] := rfl

example : Code.program (pm[ if p = q then [ s := t ] else [ t := s ]; p ← null ] : Code model L) =
    [.ifPtrEq 0 1 3, .moveData 1 0, .goto 4, .moveData 0 1, .null 0, .halt] := rfl

example (c : Code model L) : c.program.length = c.size + 1 := by simp [Code.program]

/-! Loops are evaluated with a budget of iterations; without it the interpreter gives up. -/

private def chain : State model L := ⟨0, fun i => if i = p then some 0 else none, fun _ => 0,
  [⟨fun _ => some 1, fun _ => 7⟩, ⟨fun _ => none, fun _ => 8⟩]⟩

example : (Code.eval (pm[ while p ≠ q do [ p ← p[next] ] ] : Code model L) 2 chain).map (·.2) =
    some 7 := by decide
example : (Code.eval (pm[ while p ≠ q do [ p ← p[next] ] ] : Code model L) 1 chain).map (·.2) =
    none := by decide

/-! Loop-free code is evaluated by `simp`, with the instruction count of each path. -/

example (x : State model L) (h : x.data s < x.data t) :
    ExecWithin pm[ if (()) s t then [ s := t ] else [ t := s ] ] x (x.setData s (x.data t)) 2 :=
  .of_eval (fuel := 0)
    (by simp [Cslib.Program.Code.eval, Test.Holds, Op.effect, Op.instr, Instr.effect, h])
    le_rfl

-- A list walk: the loop rule with an invariant and a measure, here the distance to null.
example (x : State model L) (k : ℕ) (hq : x.ptr q = none)
    (dist : State model L → ℕ)
    (step : ∀ y, y.ptr q = none → y.ptr p ≠ none →
      ((Op.loadPtr p next p).effect y).ptr q = none ∧
        dist ((Op.loadPtr p next p).effect y) < dist y)
    (hk : dist x = k) :
    ∃ y, ExecWithin pm[ while p ≠ q do [ p ← p[next] ] ] x y (k * 3 + 1) ∧ y.ptr p = none := by
  obtain ⟨y, run, inv, done⟩ := Cslib.Program.ExecWithin.loopUntil_invariant
    (I := instructionSet model L) (t := .ptrEq p q)
    (body := .op (.loadPtr p next p)) (fun y => y.ptr q = none) dist (T := 1)
    (fun y hy ht => ⟨_, ExecWithin.op, step y hy (by simpa [Test.Holds, hy] using ht)⟩) hq
  exact ⟨y, hk ▸ run, by simpa [Test.Holds, inv] using done⟩

/-! Symbolic execution: `pm_exec` runs the data instructions and takes the alternative that the
hypothesis decides, leaving the postcondition about a state in assignment form. -/

private abbrev swapMax : Code model L :=
  pm[ if (()) s t then [ s := t ]; p ← null ]

example (x : State model L) (h : x.data s < x.data t) :
    ∃ y, ExecWithin swapMax x y 3 ∧ y.data s = x.data t ∧ y.ptr p = none := by
  apply WP.exists_execWithin
  pm_exec [swapMax, h]
  simp

/-! Frames are read off the program text: what the program does not assign is unchanged. -/

example (x y : State model L) (run : ExecWithin swapMax x y 3) :
    y.heap = x.heap ∧ y.ptr q = x.ptr q ∧ y.data t = x.data t :=
  ⟨run.heap_eq (by pm_frame), run.ptr_keep [p] (by pm_frame) (by simp),
    run.data_keep [s] (by pm_frame) (by simp)⟩
