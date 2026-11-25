/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.TM0Encoding

/-! A two-cell computation, its symmetric rewriting path, and an incorrect write target. -/

namespace CslibFrontierTests.HWordMachine

open Turing.TM0Window Cslib.Complexity.NCL.TM0Window StateTransition

private def machine : Turing.TM0.Machine Bool (Fin 3) := fun q _ =>
  if q = 0 then some (1, .move .right)
  else if q = 1 then some (2, .write true) else none

private def initial : Cfg Bool (Fin 3) := ⟨0, false, [], [false]⟩
private def moved : Cfg Bool (Fin 3) := ⟨1, false, [false], []⟩
private def final : Cfg Bool (Fin 3) := ⟨2, true, [false], []⟩

private def moveLeft : Turing.TM0.Machine Bool (Fin 1) :=
  fun _ _ => some (0, .move .left)

-- The finite window stops at its boundary even when the native instruction requests a move.
example : step moveLeft (⟨0, false, [], []⟩ : Cfg Bool (Fin 1)) = none := rfl

example : moveLeft 0 false = some (0, .move .left) := rfl

example : Reaches (step machine) initial final := by
  have h : Reaches (step machine) initial moved := .single (by rfl)
  exact h.tail (by rfl)

example : Relation.ReflTransGen (Cslib.PostCorrespondence.Rewrites (Rules.SymmetricRule machine))
    (Rules.word (.stable initial)) (Rules.word (.stable final)) := by
  apply (Rules.symmetric_reaches_halted_iff machine initial final (by decide +kernel)).mpr
  have h : Reaches (step machine) initial moved := .single (by rfl)
  exact h.tail (by rfl)

example : ¬Cslib.PostCorrespondence.Rewrites (Rules.Rule machine) (Rules.word (.stable moved))
    (Rules.word (.stable (⟨2, false, [false], []⟩ : Cfg Bool (Fin 3)))) := by
  rw [Rules.rewrites_word_iff]
  simp [Phases.step, step, machine, moved, Rules.word, Rules.frame]

end CslibFrontierTests.HWordMachine
