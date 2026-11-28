/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.CookLevin.Correctness

/-!
# The run tableau versus the full tableau

A concrete zero-work-tape machine halts after one step with output `[false]`. The assignment read
off its run satisfies `runTableau`, which only describes runs, but not `tableau`, whose
acceptance clauses ask for output `[true]`. The same machine with output `[true]` satisfies both.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Complexity.CookLevin.RunTableau

open Turing.MultiTapeTM Cslib.Complexity.CookLevin

/-- Halts on the first step, having output the bit `b`. -/
private def emit (b : Bool) : Turing.MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, Fin.elim0, some b, none⟩

/-- The run of `emit b` on the empty input has halted after one step, with output `[b]`. -/
private theorem run_emit (b : Bool) :
    ((emit b).runFrom ((emit b).initCfg ([] ++ [])) 1).state = none ∧
      ((emit b).runFrom ((emit b).initCfg ([] ++ [])) 1).output = [b] := by
  have h : ((emit b).initCfg ([] ++ [])).state = some () := rfl
  change ((emit b).step ((emit b).initCfg ([] ++ []))).state = none ∧
    ((emit b).step ((emit b).initCfg ([] ++ []))).output = [b]
  rw [step_of_state h]
  simp [Turing.Action.apply, emit]

-- The rejecting run (output `[false]`) satisfies the run tableau: it has no acceptance clauses ...
example : (runTableau (emit false) [] 0 1).eval (runAssignment (emit false) [] []) = true :=
  eval_runTableau_runAssignment rfl

-- ... but its assignment fails the full tableau, because its output is not `[true]`.
example : (tableau (emit false) [] 0 1).eval (runAssignment (emit false) [] []) = false := by
  refine Bool.eq_false_iff.2 fun h => ?_
  have h' := (exists_eval_tableau_iff (tm := emit false) (u := []) (T := 1) (z := [])).1
    ⟨_, rfl, h⟩
  rw [(run_emit false).2] at h'
  exact absurd h'.2 (by decide)

-- No assignment at all satisfies the full tableau of the rejecting machine.
example : ¬ (tableau (emit false) [] 0 1).Satisfiable := by
  rw [tableau_satisfiable_iff]
  rintro ⟨w, hw, -, hout⟩
  obtain rfl : w = [] := List.length_eq_zero_iff.1 hw
  rw [(run_emit false).2] at hout
  exact absurd hout (by decide)

-- The accepting machine's run satisfies both.
example : (runTableau (emit true) [] 0 1).eval (runAssignment (emit true) [] []) = true ∧
    (tableau (emit true) [] 0 1).eval (runAssignment (emit true) [] []) = true :=
  ⟨eval_runTableau_runAssignment rfl,
    eval_tableau_runAssignment rfl (run_emit true).1 (run_emit true).2⟩

end CslibFrontierTests.Computability.Complexity.CookLevin.RunTableau
