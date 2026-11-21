/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.VertexParameters

/-!
# Ordinary-import clients of uniform reader parameter processing

These cases check runtime width measurement/validation and native preparation. The ID source
is still a separate read-only word; uniform combined-input dispatch is not asserted here.
-/

-- This module contains only checked clients.
set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingVertexParameters

open Turing Turing.MultiTapeTM Turing.DoubleCounting
open VertexReader VertexParameters

-- Binary sizes at zero, one, and powers of two match the existing canonical codec.
example : (prepare ⟨0, 0⟩).map State.width = some 0 := by decide +kernel
example : (prepare ⟨1, 1⟩).map State.width = some 1 := by decide +kernel
example : (prepare ⟨2, 2⟩).map State.width = some 2 := by decide +kernel
example : (prepare ⟨4, 3⟩).map State.width = some 3 := by decide +kernel
example : (prepare ⟨8, 4⟩).map State.width = some 4 := by decide +kernel

-- One fewer bit at a power of two is invalid, even if some small IDs would fit.
example : prepare ⟨4, 2⟩ = none := by decide +kernel
example : prepare ⟨4, 4⟩ = none := by decide +kernel
example : prepare ⟨0, 1⟩ = none := by decide +kernel
example : prepare ⟨1, 0⟩ = none := by decide +kernel
example : prepare ⟨3, 1000000⟩ = none := by decide +kernel

private def initializedFour : State := ⟨4, 3, 0, 0, false⟩

private theorem prepare_four : prepare ⟨4, 3⟩ = some initializedFour := rfl

-- Initialization resets the actual cursor, accumulator and missing-bit flag.
example : (prepare ⟨4, 3⟩).map State.cursor = some 0 := by decide +kernel
example : (prepare ⟨4, 3⟩).map State.value = some 0 := by decide +kernel
example : (prepare ⟨4, 3⟩).map State.truncated = some false := by decide +kernel

-- A dispatch caller can recover both validation and the state-loading equation.
example (p : Parameters) (s : State) (h : prepare p = some s) :
    p.width = p.dimension.size ∧ s.cursor = 0 ∧ s.value = 0 ∧ s.truncated = false := by
  obtain ⟨hw, rfl⟩ := (prepare_eq_some_iff p s).mp h
  exact ⟨hw, rfl, rfl, rfl⟩

-- The same dimension-independent reader handles the successfully loaded state.
example : result ((machine 0).runFrom [false, true, true] initializedFour 3) = some 3 := by
  rw [result_prepare ⟨4, 3⟩ initializedFour prepare_four]
  decide +kernel

example : result ((machine 0).runFrom [true, false, false] initializedFour 3) = none := by
  rw [result_prepare ⟨4, 3⟩ initializedFour prepare_four]
  decide +kernel

example : result ((machine 0).runFrom [false, true] initializedFour 3) = none := by
  rw [result_prepare ⟨4, 3⟩ initializedFour prepare_four]
  decide +kernel

-- Agreement and bounds are uniform in the dimension, for all clocks and read-only choice words.
example (p : Parameters) (s : State) (h : prepare p = some s) (w : List Bool) (t : ℕ) :
    (machine 0).runFrom w s t = (machine p.dimension).run w t :=
  runFrom_prepare p s h w t

example (w : List Bool) (t : ℕ) :
    (encState ((machine 0).runFrom w initializedFour t)).length ≤ 33 := by
  have h := runFrom_length_le ⟨4, 3⟩ initializedFour prepare_four w t
  convert h using 1
  decide +kernel

-- Actual native initialization can be followed by the existing native range/result check.
example : ComputableInSpace
    (fun p : Parameters => result ((prepare p).getD ⟨0, 0, 0, 0, false⟩))
    encParameters (encOption encNat) (fun p => (encParameters p).length) := by
  have hs : ComputableInSpace
      (fun p : Parameters => (prepare p).getD ⟨0, 0, 0, 0, false⟩)
      encParameters encState (fun p => (encParameters p).length) :=
    ComputableInSpace.budget_optionGetD (encB := encState) ⟨0, 0, 0, 0, false⟩ prepare_inSpace
  exact ComputableInSpace.budget_comp_linear result_inSpace hs

end CslibFrontierTests.DoubleCountingVertexParameters
