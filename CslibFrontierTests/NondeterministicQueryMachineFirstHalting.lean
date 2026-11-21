/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine

/-! # First-halting choice prefixes

An abstract query machine records the first choice as its verdict and halts. The examples
check that subsequent padding leaves that verdict intact and that an initially halted
state needs no choices.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.NondeterministicQueryMachineFirstHalting

open Turing

private def chooseVerdict : NondeterministicQueryMachine (Option Bool) where
  init := none
  query _ := 0
  next := fun ⟨_, _, choice⟩ => some choice
  halted := Option.isSome
  accept := (·.getD false)

/-- The unique first-halting prefix retains the true selector and removes the false padding. -/
example : ∃ first : List Bool, first = [true] ∧ chooseVerdict.replay [] first none = some true := by
  obtain ⟨first, ⟨_, _, hstate⟩, huniq⟩ :=
    chooseVerdict.existsUnique_firstHalting_prefix [] (s := none) (choices := [true, false])
      (by rfl)
  have hone : [true] <+: [true, false] ∧
      chooseVerdict.FirstHalting [] [true] none ∧
      chooseVerdict.replay [] [true] none = chooseVerdict.replay [] [true, false] none := by
    refine ⟨⟨[false], rfl⟩, ⟨rfl, ?_⟩, rfl⟩
    intro n hn
    obtain rfl : n = 0 := Nat.lt_one_iff.mp hn
    rfl
  exact ⟨first, (huniq _ hone).symm, hstate⟩

/-- An accepting state supplied at initialization has an empty first-halting trace. -/
example : ∃ choices : List Bool, choices = [] ∧
    (chooseVerdict.withInit (some true)).accept
      ((chooseVerdict.withInit (some true)).run [] choices) = true := by
  have haccept : (chooseVerdict.withInit (some true)).Accepts [] := ⟨[false], rfl, rfl⟩
  obtain ⟨choices, hfirst, hv⟩ :=
    ((chooseVerdict.withInit (some true)).accepts_iff_exists_firstHalting []).mp haccept
  refine ⟨choices, ?_, hv⟩
  by_contra hne
  exact Bool.noConfusion (hfirst.2 0 (List.length_pos_iff.mpr hne))

end CslibFrontierTests.NondeterministicQueryMachineFirstHalting
