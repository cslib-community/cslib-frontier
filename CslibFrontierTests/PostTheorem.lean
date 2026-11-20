/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Foundations.Computability.PostTheorem

open Cslib.Computability
open Nat.RecursiveIn.KleenePost (halting)

example : halting ∈ ArithmeticDelta 2 :=
  mem_arithmeticDelta_succ_iff.mpr decidableIn_halting_firstJump

example : EnumerableIn (iteratedJump 2) halting :=
  mem_arithmeticSigma_two_iff.mp (iteratedJump_succ_mem_arithmeticSigma 1)

example : iteratedJump 2 ∈ ArithmeticSigma 3 := by
  apply mem_arithmeticSigma_succ_iff.mpr
  apply DecidableIn.enumerableIn
  exact decidableIn_iff_exists_code.mpr ⟨Nat.RecursiveIn.Code.oracle, rfl⟩

example {A : Set ℕ} (h : EnumerableIn A halting) : A ∈ ArithmeticSigma 2 :=
  mem_arithmeticSigma_two_iff.mpr h

example {A : Set ℕ} (h : A ∈ ArithmeticDelta 1) : ComputablePred (· ∈ A) :=
  mem_arithmeticDelta_one_iff.mp h
