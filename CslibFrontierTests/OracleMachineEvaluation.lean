/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.OraclePrograms

/-! # Oracle answers control halting and output -/

set_option linter.privateModule false

namespace CslibFrontierTests.OracleMachineEvaluation

open Turing.MultiTapeTM.Universal

/-- On empty input, write one tally, submit it, and emit 7 if the answer is yes. -/
private def queryOne : OracleDesc where
  tapes := 0
  initial := 0
  table :=
    [(⟨0, none, []⟩, .step ⟨.zero, [], none, some 1⟩ true),
     (⟨1, none, []⟩, .query 2 3),
     (⟨2, none, []⟩, .step ⟨.zero, [], some 7, none⟩ false),
     (⟨3, none, []⟩, .step ⟨.zero, [], none, some 3⟩ false)]

example : [7] ∈ queryOne.eval (· == 1) [] := by
  apply (queryOne.mem_eval_iff (· == 1) [] [7]).mpr
  exact ⟨3, rfl, rfl⟩

example : ¬ (queryOne.eval (· == 0) []).Dom := by
  intro h
  obtain ⟨out, hout⟩ := Part.dom_iff_mem.mp h
  obtain ⟨t, ht, _⟩ := (queryOne.mem_eval_iff (· == 0) [] out).mp hout
  have fixed : queryOne.step (· == 0) [] (queryOne.runFor (· == 0) [] 2) =
      queryOne.runFor (· == 0) [] 2 := rfl
  match t with
  | 0 => exact (by decide : ¬ (queryOne.runFor (· == 0) [] 0).ordinary.state = none) ht
  | 1 => exact (by decide : ¬ (queryOne.runFor (· == 0) [] 1).ordinary.state = none) ht
  | t + 2 =>
    rw [OracleDesc.runFor, Function.iterate_add_apply, ← OracleDesc.runFor,
      Function.iterate_fixed fixed] at ht
    exact (by decide : ¬ (queryOne.runFor (· == 0) [] 2).ordinary.state = none) ht

example : ∃ c : Nat.RecursiveIn.Code, ∀ (oracle : ℕ → Bool),
    c.eval (fun n => Part.some (oracle n).toNat) (Encodable.encode ([] : List ℕ)) =
      (queryOne.eval oracle []).map Encodable.encode := by
  obtain ⟨c, hc⟩ := queryOne.exists_code_eval
  exact ⟨c, fun oracle => hc oracle []⟩

example : OracleDesc.unaryQuery.evalUnary (· == 5) 5 = Part.some 1 := by
  rw [OracleDesc.evalUnary_unaryQuery]
  rfl

example : OracleDesc.unaryQuery.eval (· == 4) [1, 1, 1, 1, 1] = Part.some [] := by
  change OracleDesc.unaryQuery.eval (· == 4) (List.replicate 5 1) = Part.some []
  rw [OracleDesc.eval_unaryQuery]
  rfl

end CslibFrontierTests.OracleMachineEvaluation
