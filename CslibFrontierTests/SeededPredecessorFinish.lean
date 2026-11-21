/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.PolyTime.SeededPredecessorFinish

open Cslib Turing.MultiTapeTM

-- A padded edge or padded candidate rejects, including when the other lookup returns key zero.
example (c : SeededPredecessor.Context) :
    SeededPredecessorFinish.run ⟨c, none, some (0, 0)⟩ = false ∧
    SeededPredecessorFinish.run ⟨c, some (0, 0), none⟩ = false := by simp

-- Parallel edges count in increasing index order for every seed and every label length.
example (c : SeededPredecessor.Context) (p : ℕ × ℕ) (i : ℕ) :
    SeededPredecessorFinish.run ⟨{ c with candidate := i, edge := i + 1 }, some p, some p⟩ =
      true ∧
    SeededPredecessorFinish.run ⟨{ c with candidate := i, edge := i }, some p, some p⟩ =
      false := by
  simp [SeededPredecessor.test, SeededPredecessor.Context.withEndpoints]

example : ComputableInPolyTime SeededPredecessorFinish.run SeededPredecessorFinish.encInput
    encBool := SeededPredecessorFinish.computableInPolyTime_run
