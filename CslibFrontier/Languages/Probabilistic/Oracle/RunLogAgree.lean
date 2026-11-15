/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# Run-log agreement until a marked query

Two stateless probabilistic oracles that have the same output distribution away from a predicate
`bad` assign the same probability to every outcome of `ProbOracleComp.runLog` whose log mentions
no query satisfying `bad`. This is the game-hopping step ("identical until bad") in its exact
logged form.

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

/-- Every supported run of the logging oracle from the log `s` ends in a log that extends `s`. -/
private theorem prefix_of_mem_support_runWith_logStep (O : Q → ProbComp R)
    (A : ProbOracleComp (fun _ : Q => R) α) (s : List (Q × R)) {z : α × List (Q × R)}
    (hz : z ∈ (runWith (logStep O) A s).support) : s <+: z.2 := by
  induction A using ProbOracleComp.induction generalizing s with
  | pure a =>
    rw [runWith_pure, PMF.mem_support_pure_iff] at hz
    subst hz
    exact List.prefix_refl s
  | sample_bind n cont ih =>
    rw [runWith_sample_bind, PMF.mem_support_bind_iff] at hz
    obtain ⟨i, -, hi⟩ := hz
    exact ih i s hi
  | query_bind q cont ih =>
    rw [runWith_bind, runWith_query, PMF.mem_support_bind_iff] at hz
    obtain ⟨x, hx, hcont⟩ := hz
    simp only [logStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hx
    obtain ⟨r, -, rfl⟩ := hx
    exact (List.prefix_append s _).trans (ih r _ hcont)

/-- `eval_runLog_apply_eq_of_agree` from an arbitrary starting log. -/
private theorem runWith_logStep_apply_eq_of_agree {O O' : Q → ProbComp R} {bad : Q → Prop}
    (h : ∀ q, ¬ bad q → ProbComp.eval (O q) = ProbComp.eval (O' q))
    (A : ProbOracleComp (fun _ : Q => R) α) (s : List (Q × R)) {z : α × List (Q × R)}
    (hz : ∀ p ∈ z.2, ¬ bad p.1) :
    runWith (logStep O) A s z = runWith (logStep O') A s z := by
  induction A using ProbOracleComp.induction generalizing s with
  | pure a => rw [runWith_pure, runWith_pure]
  | sample_bind n cont ih =>
    rw [runWith_sample_bind, runWith_sample_bind, PMF.bind_apply, PMF.bind_apply]
    exact tsum_congr fun i => by rw [ih i s]
  | query_bind q cont ih =>
    rw [runWith_bind, runWith_bind, runWith_query, runWith_query, PMF.bind_apply, PMF.bind_apply]
    by_cases hq : bad q
    · -- A marked query is logged, so no run through it ends in `z`.
      have hzero : ∀ (O'' : Q → ProbComp R) (x : R × List (Q × R)),
          logStep O'' q s x * runWith (logStep O'') (cont x.1) x.2 z = 0 := by
        intro O'' x
        by_contra hne
        obtain ⟨hx, hcont⟩ := mul_ne_zero_iff.mp hne
        rw [← PMF.mem_support_iff] at hx hcont
        simp only [logStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hx
        obtain ⟨r, -, rfl⟩ := hx
        have hpre := prefix_of_mem_support_runWith_logStep O'' (cont r) _ hcont
        exact hz (q, r) (hpre.subset (by simp)) hq
      simp only [hzero]
    · have hstep : logStep O q s = logStep O' q s := by
        simp only [logStep, ProbComp.eval_map, h q hq]
      rw [hstep]
      exact tsum_congr fun x => by rw [ih x.1 x.2]

/-- Two oracles that agree away from `bad` give the same probability to every outcome whose log
names no `bad` query. -/
theorem eval_runLog_apply_eq_of_agree {O O' : Q → ProbComp R} {bad : Q → Prop}
    (h : ∀ q, ¬ bad q → ProbComp.eval (O q) = ProbComp.eval (O' q))
    (A : ProbOracleComp (fun _ : Q => R) α) {z : α × List (Q × R)}
    (hz : ∀ p ∈ z.2, ¬ bad p.1) :
    ProbComp.eval (A.runLog O) z = ProbComp.eval (A.runLog O') z := by
  rw [runLog, runLog, eval_runState, eval_runState]
  exact runWith_logStep_apply_eq_of_agree h A [] hz

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
  exact h'.trans (PMF.map_id _)

/-- The hypothesis on the log is needed: one query, two different constant oracles. -/
example : ProbComp.eval ((ProbOracleComp.query (spec := fun _ : Unit => Bool) ()).runLog
      fun _ => pure true) (true, [((), true)]) ≠
    ProbComp.eval ((ProbOracleComp.query (spec := fun _ : Unit => Bool) ()).runLog
      fun _ => pure false) (true, [((), true)]) := by
  simp [runLog, StateT.run]

end Cslib.ProbOracleComp
