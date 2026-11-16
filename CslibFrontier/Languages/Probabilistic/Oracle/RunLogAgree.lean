/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag

/-!
# Run-log agreement until a marked query

Two stateless probabilistic oracles that have the same output distribution away from a predicate
`bad` induce logging oracles satisfying `ProbOracleComp.IdenticalUntilBad` (until the log names a
`bad` query), so they assign the same probability to every outcome of `ProbOracleComp.runLog` whose
log mentions no query satisfying `bad`.

## Main results

* `Cslib.ProbOracleComp.eval_runLog_apply_eq_of_agree`: equal probabilities for outcomes without a
  `bad` query in the log.
* `Cslib.ProbOracleComp.map_fst_eval_runLog`: forgetting the log of `runLog` gives `run`.
-/

public section

namespace Cslib.ProbOracleComp

variable {Q R α : Type}

/-- The evaluated logging oracle of `runLog`. -/
private noncomputable abbrev logStep (O : Q → ProbComp R) (q : Q) :
    StateT (List (Q × R)) PMF R :=
  fun log => ProbComp.eval ((fun r => (r, log ++ [(q, r)])) <$> O q)

/-- The logging oracles of two oracles that agree away from `bad` are identical until the log
names a `bad` query. -/
private theorem identicalUntilBad_logStep {O O' : Q → ProbComp R} {bad : Q → Prop}
    (h : ∀ q, ¬ bad q → ProbComp.eval (O q) = ProbComp.eval (O' q)) :
    ProbOracleComp.IdenticalUntilBad (logStep O) (logStep O') fun log => ∃ p ∈ log, bad p.1 := by
  have habsorb : ∀ (O'' : Q → ProbComp R) (q : Q) (s : List (Q × R)), (∃ p ∈ s, bad p.1) →
      ∀ x ∈ (logStep O'' q s).support, ∃ p ∈ x.2, bad p.1 := by
    intro O'' q s ⟨p, hp, hb⟩ x hx
    simp only [logStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hx
    obtain ⟨r, -, rfl⟩ := hx
    exact ⟨p, List.mem_append_left _ hp, hb⟩
  refine OracleComp.IdenticalUntilBad.probOracleComp
    ⟨fun q s _ a s' hs' => ?_, habsorb O, habsorb O'⟩
  by_cases hq : bad q
  · -- A marked query is logged, so neither oracle reaches the good log `s'`.
    have hzero : ∀ O'' : Q → ProbComp R, logStep O'' q s (a, s') = 0 := by
      intro O''
      rw [PMF.apply_eq_zero_iff]
      intro hmem
      simp only [logStep, ProbComp.eval_map, PMF.mem_support_map_iff, Prod.mk.injEq] at hmem
      obtain ⟨r, -, -, rfl⟩ := hmem
      exact hs' ⟨(q, r), by simp, hq⟩
    rw [hzero, hzero]
  · simp only [logStep, ProbComp.eval_map, h q hq]

/-- Two oracles that agree away from `bad` give the same probability to every outcome whose log
names no `bad` query. -/
theorem eval_runLog_apply_eq_of_agree {O O' : Q → ProbComp R} {bad : Q → Prop}
    (h : ∀ q, ¬ bad q → ProbComp.eval (O q) = ProbComp.eval (O' q))
    (A : ProbOracleComp (fun _ : Q => R) α) {z : α × List (Q × R)}
    (hz : ∀ p ∈ z.2, ¬ bad p.1) :
    ProbComp.eval (A.runLog O) z = ProbComp.eval (A.runLog O') z := by
  rw [runLog, runLog, eval_runState, eval_runState]
  exact (identicalUntilBad_logStep h).run_apply A [] z.1 z.2 (by simpa using hz)

/-- Forgetting the log of `runLog` gives `run`. -/
theorem map_fst_eval_runLog (A : ProbOracleComp (fun _ : Q => R) α) (O : Q → ProbComp R) :
    (ProbComp.eval (A.runLog O)).map Prod.fst = ProbComp.eval (A.run O) := by
  rw [runLog, eval_runState, eval_run]
  have h := runWith_map_state (logStep O) (fun q => StateT.lift (ProbComp.eval (O q)))
    (fun _ => ()) (fun q s => by
      simp only [logStep, ProbComp.eval_map, PMF.map_comp]
      rfl) A []
  rw [runWith_lift] at h
  have h' := congrArg (PMF.map Prod.fst) h
  rw [PMF.map_comp, PMF.map_comp] at h'
  exact h'.trans ((PMF.map_id _).trans (OracleComp.evalWith_eq_interpret _ _))

end Cslib.ProbOracleComp
