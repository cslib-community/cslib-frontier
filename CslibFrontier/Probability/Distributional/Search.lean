/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind

/-!
# Distributional search with partially observed state

A `DistributionalSearchProblem` specifies a distribution on states, the observation given to a
solver, and the relation used to judge its answer. Separating the state from its observation
allows both ordinary relation search and recovery of a hidden planted object. The solver receives
only the observation; the success test may also use the hidden state.

These are semantic definitions, independent of an encoding or model of computation. The
Boolean `experiment` uses classical decidability only to score the answer, and does not assert
that the success relation can be decided by the solver. `ofRelation` specializes to the ordinary
setting where the entire state is observed and answers satisfy a relation on inputs and outputs.
Solvers have total output laws; an explicit error or `Option` output can represent failure.

For a family of problems, `HasSolver` asks for one admitted program whose failure probability
meets a bound at every parameter. An evaluator and a predicate on whole programs specify the
model. In particular, admitting a single machine differs from admitting arbitrary families of
circuits or arbitrary statistical rules; the definition does not identify these choices.

## Main definitions

* `Cslib.Probability.DistributionalSearchProblem`: a law, an observation and a success relation.
* `Cslib.Probability.DistributionalSearchProblem.experiment`: the Boolean success experiment.
* `Cslib.Probability.DistributionalSearchProblem.ofRelation`: fully observed relation search.
* `Cslib.Probability.DistributionalSearchProblem.HasSolver`: one admitted solver for a family.
-/

public section

namespace Cslib.Probability

open scoped ENNReal

/-- A distributional search problem, allowing the success test to depend on hidden state. -/
structure DistributionalSearchProblem (State Input Output : Type*) where
  /-- The law of the complete state, including any hidden information. -/
  distribution : PMF State
  /-- The information revealed to the solver. -/
  observe : State → Input
  /-- When an output counts as a successful answer for the complete state. -/
  accepts : State → Output → Prop

namespace DistributionalSearchProblem

variable {State Input Output : Type*}

/-- Sample a state, run the solver on its observation, and score its answer.
The classical success test is semantic and is not part of the solver's computation. -/
@[expose] noncomputable def experiment (P : DistributionalSearchProblem State Input Output)
    (solver : Input → PMF Output) : PMF Bool := by
  classical
  exact P.distribution.bind fun state =>
    (solver (P.observe state)).map fun output => decide (P.accepts state output)

/-- Ordinary distributional relation search, with the full input revealed to the solver.
The relation need not be total: an input with no acceptable output contributes failure probability
one. A promise on the distribution's support can exclude such inputs when desired. -/
@[expose] def ofRelation (distribution : PMF Input) (accepts : Input → Output → Prop) :
    DistributionalSearchProblem Input Input Output where
  distribution := distribution
  observe := id
  accepts := accepts

open scoped Classical in
/-- For a deterministic solver, the experiment is the pushforward of the state law by success. -/
theorem experiment_pure (P : DistributionalSearchProblem State Input Output)
    (solver : Input → Output) :
    P.experiment (fun input => PMF.pure (solver input)) =
      P.distribution.map fun state => decide (P.accepts state (solver (P.observe state))) := by
  simp only [experiment, PMF.pure_map]
  rfl

/-- A deterministic solver's failure probability is the mass of states where its answer fails. -/
theorem experiment_pure_false (P : DistributionalSearchProblem State Input Output)
    (solver : Input → Output) :
    P.experiment (fun input => PMF.pure (solver input)) false =
      P.distribution.toOuterMeasure {state | ¬ P.accepts state (solver (P.observe state))} := by
  classical
  rw [experiment_pure, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  congr 1
  ext state
  simp

/-- Solvers with the same output laws on possible observations have the same success experiment. -/
theorem experiment_congr (P : DistributionalSearchProblem State Input Output)
    {solver solver' : Input → PMF Output}
    (h : ∀ state ∈ P.distribution.support,
      solver (P.observe state) = solver' (P.observe state)) :
    P.experiment solver = P.experiment solver' := by
  classical
  exact PMF.bind_congr_on_support P.distribution _ _ fun state hstate => by
    rw [h state hstate]

section Families

variable {State Input Output : ℕ → Type*} {Program Program' : Type*}

/-- One admitted program solves the entire problem family with failure at most `ε n`.
The admissibility predicate applies to a whole program, before the parameter is quantified.
The evaluator determines which observations that program can inspect and the law of its output. -/
@[expose] def HasSolver
    (P : ∀ n, DistributionalSearchProblem (State n) (Input n) (Output n))
    (eval : Program → ∀ n, Input n → PMF (Output n))
    (Admissible : Program → Prop) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ program, Admissible program ∧
    ∀ n, (P n).experiment (eval program n) false ≤ ε n

variable {P : ∀ n, DistributionalSearchProblem (State n) (Input n) (Output n)}
  {eval : Program → ∀ n, Input n → PMF (Output n)}
  {Admissible Admissible' : Program → Prop} {ε δ : ℕ → ℝ≥0∞}

/-- Relaxing the failure bound preserves the existence of an admitted solver. -/
theorem HasSolver.mono_error (h : HasSolver P eval Admissible ε)
    (hεδ : ∀ n, ε n ≤ δ n) : HasSolver P eval Admissible δ := by
  obtain ⟨program, hprogram, herror⟩ := h
  exact ⟨program, hprogram, fun n => (herror n).trans (hεδ n)⟩

/-- Enlarging the admitted program class preserves the existence of a solver. -/
theorem HasSolver.mono_admissible (h : HasSolver P eval Admissible ε)
    (hmodel : ∀ program, Admissible program → Admissible' program) :
    HasSolver P eval Admissible' ε := by
  obtain ⟨program, hprogram, herror⟩ := h
  exact ⟨program, hmodel program hprogram, herror⟩

/-- Transport a solver through a compiler preserving admissibility and its output law on every
possible observation. This semantic lemma does not assert that any particular compiler or model
has these properties; concrete models supply those proofs. -/
theorem HasSolver.of_simulation (h : HasSolver P eval Admissible ε)
    {eval' : Program' → ∀ n, Input n → PMF (Output n)}
    {Admissible' : Program' → Prop} (compile : Program → Program')
    (hadmissible : ∀ program, Admissible program → Admissible' (compile program))
    (hsimulate : ∀ program, Admissible program → ∀ n state,
      state ∈ (P n).distribution.support →
        eval' (compile program) n ((P n).observe state) =
          eval program n ((P n).observe state)) :
    HasSolver P eval' Admissible' ε := by
  obtain ⟨program, hprogram, herror⟩ := h
  refine ⟨compile program, hadmissible program hprogram, fun n => ?_⟩
  rw [(P n).experiment_congr (hsimulate program hprogram n)]
  exact herror n

end Families

end DistributionalSearchProblem

end Cslib.Probability
