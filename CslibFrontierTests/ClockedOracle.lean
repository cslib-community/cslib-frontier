/-
Copyright (c) 2026 Christian Reitwiessner, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Matthew Doty
-/

module

import CslibFrontier.Foundations.Computability.RecursiveInClocked

/-! # Unbounded search in clocked oracle programs halts or diverges with the oracle -/

set_option linter.privateModule false

namespace CslibFrontierTests.ClockedOracle

open Cslib

/-- Search for the least position at which the oracle answers `0`. -/
def firstZero : ClockedComp natOracleSpec ℕ :=
  ClockedComp.rfind fun i => (fun r => decide (r = 0)) <$> ClockedComp.query i

theorem eval_firstZero (g : ℕ →. ℕ) :
    ClockedComp.eval g firstZero = Nat.rfind fun i => (g i).map fun r => decide (r = 0) := by
  rw [firstZero, ClockedComp.eval_rfind g fun i => (ClockedComp.Stable.query i).map _]
  congr 1
  funext i
  rw [ClockedComp.eval_map g (.query i)]
  exact congrArg _ (ClockedComp.eval_query g i)

/-- Against an oracle that never answers `0`, the search diverges. -/
example : ClockedComp.eval (fun _ => Part.some 1 : ℕ →. ℕ) firstZero = Part.none := by
  refine (eval_firstZero _).trans (Part.eq_none_iff.2 fun n hn => ?_)
  simpa using Nat.rfind_spec hn

/-- Against an oracle answering `0` first at position `3`, the search returns `3`. -/
example :
    ClockedComp.eval (fun i => Part.some (if i = 3 then 0 else 1) : ℕ →. ℕ) firstZero =
      Part.some 3 := by
  refine (eval_firstZero _).trans
    (Part.eq_some_iff.2 (Nat.mem_rfind.2 ⟨by simp, fun {m} hm => ?_⟩))
  interval_cases m <;> simp

/-- If the oracle is undefined at position `1`, the search diverges even though the oracle
answers `0` at position `3`: earlier trials must return. -/
example :
    ClockedComp.eval
      (fun i => if i = 1 then Part.none else Part.some (if i = 3 then 0 else 1) : ℕ →. ℕ)
      firstZero = Part.none := by
  refine (eval_firstZero _).trans (Part.eq_none_iff.2 fun n hn => ?_)
  rcases Nat.lt_or_ge 1 n with h | h
  · obtain ⟨_, h1⟩ := (Part.mem_map_iff _).1 (Nat.rfind_min hn h)
    simp at h1
  · interval_cases n
    · simpa using Nat.rfind_spec hn
    · obtain ⟨_, h1⟩ := (Part.mem_map_iff _).1 (Nat.rfind_spec hn)
      simp at h1

/-- The compiled program of a code agrees with the code, here unbounded search for a zero of
the oracle. -/
example (g : ℕ →. ℕ) (n : ℕ) :
    ClockedComp.eval g ((Nat.RecursiveIn.Code.rfind .oracle).toClocked n) =
      Nat.rfind fun i => (fun m => decide (m = 0)) <$> g (Nat.pair n i) := by
  rw [Nat.RecursiveIn.Code.eval_toClocked, Nat.RecursiveIn.Code.eval_rfind]
  rfl

/-- Compiled programs have computable dialogues, so the hypothesis of the program-to-code
direction is satisfiable. -/
example (c : Nat.RecursiveIn.Code) :
    Computable (ClockedComp.dialogue c.toClocked) :=
  Nat.RecursiveIn.Code.computable_dialogue_toClocked c

/-- A partial oracle, undefined at `0`. -/
def holey : ℕ →. ℕ := fun n => if n = 0 then Part.none else Part.some n

/-- The characterization applies to the partial oracle `holey`: the oracle itself is computed by
a family of clocked programs with computable dialogue. -/
example : ∃ P : ℕ → ClockedComp natOracleSpec ℕ, Computable (ClockedComp.dialogue P) ∧
    ∀ n, ClockedComp.eval holey (P n) = holey n :=
  Nat.RecursiveIn.Code.recursiveIn_iff_exists_clockedComp.1 (Nat.RecursiveIn.oracle _ rfl)

/-- The compiled program diverges where the oracle is undefined. -/
example : ClockedComp.eval holey (Nat.RecursiveIn.Code.oracle.toClocked 0) = Part.none := by
  rw [Nat.RecursiveIn.Code.eval_toClocked]
  rfl

end CslibFrontierTests.ClockedOracle
