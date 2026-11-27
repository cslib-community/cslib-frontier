/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.QueryCompiler
import Mathlib.Tactic.FinCases

/-! # Native unambiguous logarithmic space

Check UL membership for a machine that accepts according to the encoded input bit, and
apply the forgetful inclusion to obtain NL membership.
Also compile an abstract query machine that accepts or rejects from its initial state.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LogSpace.Counting

open Turing MultiTapeCTM
open Cslib.Complexity Turing.MultiTapeTM

private def readBit : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ bit _ _ := [
    .step { inputTape := 0, workTapes := Fin.elim0, output := some (bit.getD false), state := none }
      Empty.elim Empty.elim]

/-- A one-step native witness yields both UL and NL membership, with acceptance determined by
the actual encoded input bit. -/
example : ({true} : Set Bool) ∈ UL encBool ∧ ({true} : Set Bool) ∈ NL encBool := by
  have hUL : ({true} : Set Bool) ∈ UL encBool := by
    let f (b : Bool) : ℕ := if b then 1 else 0
    refine ⟨f, ⟨0, Unit, inferInstance, readBit, 0, ?_⟩, ?_, ?_⟩
    · intro a
      refine ⟨?_, 1, ?_, ?_⟩
      · intro p
        simp [MultiTapeNTM.ComputationPath.space, MultiTapeNTM.RunPath.space]
      · apply HaltsWithin.step (by cases a <;> decide)
        intro index
        apply HaltsWithin.halt
        cases a <;> fin_cases index <;> rfl
      · cases a <;> decide
    · intro a
      cases a <;> decide
    · intro a
      cases a <;> decide
  exact ⟨hUL, UL_subset_NL hUL⟩

private def haltedInput : NondeterministicQueryMachine Bool where
  init := false
  query _ := 0
  next s := s.1
  halted _ := true
  accept := not

/-- The two input bits start halted, and only the false input accepts. -/
example : ({false} : Set Bool) ∈ UL encBool := by
  have hnil (b : Bool) (bits : List Bool) (h : haltedInput.FirstHalting (encBool b) bits b) :
      bits = [] := by
    cases bits with
    | nil => rfl
    | cons c cs =>
      exact Bool.noConfusion ((haltedInput.firstHalting_cons_iff (encBool b) c cs b).mp h).1
  refine haltedInput.mem_UL_of_firstHalting (encS := encBool)
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _) id ?_ ?_ ?_ ?_ ?_
  · exact (ComputableInSpace.of_finite id).weaken (.of_le fun b => by simp [encBool_apply])
  · exact ⟨1, fun b bits => by simp [encBool_apply]⟩
  · exact fun _ => ⟨0, fun _ _ => rfl⟩
  · intro b bits hbits other hother
    exact (hnil b bits hbits.1).trans (hnil b other hother.1).symm
  · intro b
    simp only [Set.mem_singleton_iff, NondeterministicQueryMachine.accepts_iff_exists_firstHalting]
    constructor
    · rintro rfl
      exact ⟨[], ⟨rfl, fun n h => by simp at h⟩, rfl⟩
    · rintro ⟨bits, hfirst, haccept⟩
      rw [hnil b bits hfirst] at haccept
      cases b
      · rfl
      · exact Bool.noConfusion haccept

end CslibFrontierTests.LogSpace.Counting
