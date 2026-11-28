/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Norm
public import CslibFrontier.Languages.Probabilistic.Oracle.Norm.Init
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith

/-!
# Priority-ordered normalization of stateful and stateless oracle runs

Tags the lemmas of the simp set `runWith_norm`. Combined with `pmf_norm`,
`simp only [runWith_norm, pmf_norm]` reduces concrete `ProbOracleComp` and `OracleComp` `do`-blocks
to `PMF.bind`, `PMF.pure`, and `PMF.map` in one pass, while stopping cleanly at
`ProbOracleComp.runWith oracle (adversary n pk) s` or `OracleComp.evalWith handler (adversary n pk)`
when `adversary` is a black-box parameter:

* folding `ProbOracleComp.run` and spelled-out runs into `ProbOracleComp.runWith` or
  `OracleComp.evalWith`:
  `ProbOracleComp.eval_interpret_eq_evalWith`, `ProbOracleComp.eval_run_eq_evalWith`,
  `ProbOracleComp.eval_run_interpret_eq_runWith`, `ProbOracleComp.runWith_eq_run_interpret`;
* composing `ProbOracleComp.simulate` and spelled-out handlers inside `ProbOracleComp.runWith` or
  `OracleComp.evalWith`:
  `ProbOracleComp.evalWith_run_interpret`, `ProbOracleComp.evalWith_sumHandler_simulate`,
  `ProbOracleComp.evalWith_interpret_sumHandler`, `ProbOracleComp.runWith_interpret_sumHandler_eta`,
  `ProbOracleComp.runWith_simulate_eta`, `ProbOracleComp.runWith_run_interpret`;
* stepping `ProbOracleComp.runWith` over program syntax, lifted sub-interfaces, and memoryless
  oracles:
  `ProbOracleComp.runWith_lift`, `ProbOracleComp.runWith_memoryless`,
  `ProbOracleComp.runWith_pure_state`, `ProbOracleComp.runWith_sample_bind`,
  `ProbOracleComp.runWith_pure`, `ProbOracleComp.runWith_bind`, `ProbOracleComp.runWith_map`,
  `ProbOracleComp.runWith_query`, `ProbOracleComp.runWith_sample`,
  `ProbOracleComp.runWith_liftLeft`, `ProbOracleComp.runWith_liftRight`;
* stepping generic `OracleComp.runWith` and stateless `OracleComp.evalWith`:
  `OracleComp.runWith_lift`, `OracleComp.runWith_memoryless`, `OracleComp.runWith_pure`,
  `OracleComp.runWith_bind`, `OracleComp.runWith_map`, `OracleComp.runWith_query`,
  `OracleComp.runWith_sumHandler_liftLeft`, `OracleComp.runWith_sumHandler_liftRight`,
  `OracleComp.evalWith_pure`, `OracleComp.evalWith_bind`, `OracleComp.evalWith_map`,
  `OracleComp.evalWith_query`, `OracleComp.evalWith_interpret`,
  `OracleComp.evalWith_sumHandler_liftLeft`, `OracleComp.evalWith_sumHandler_liftRight`,
  `OracleComp.sumHandler_inl`, `OracleComp.sumHandler_inr`,
  `ProbOracleComp.evalWith_sumHandler_unifOracle_sample`,
  `ProbOracleComp.evalWith_sumHandler_sample`, `ProbOracleComp.evalWith_sumHandler_query`;
* normalizing embedded private sampling and identity/tuple maps produced by `runWith_map` and
  memoryless runs:
  `ProbOracleComp.sample_pure`, `ProbOracleComp.sample_bind`, `ProbOracleComp.sample_map`,
  `Probability.PMF.map_id'`, `PMF.map_id`, `Prod.map_apply`, `Prod.map_fst`, `Prod.map_snd`,
  `id_eq`.

`OracleComp.interpret_bind`, `ProbOracleComp.run_bind`, `ProbOracleComp.simulate_bind`, and
`StateT.run_bind` are deliberately excluded: bottom-up `simp` would otherwise rewrite inside
`((OracleComp.interpret …).run s)`, `(program.run oracle)`, or `(ProbOracleComp.simulate …)` before
the enclosing priority-1200 run-folding or handler-composition rules match.

The set is priority-ordered and is not claimed to be confluent: when several rules match the same
term, the run-folding and handler-composition rules (priority 1200) and the memoryless-oracle and
embedded-sampling rules (priority 1100) take precedence over the default-priority syntax-stepping
rules.

## Main results

* `Cslib.ProbOracleComp.eval_interpret_eq_evalWith`,
  `Cslib.ProbOracleComp.eval_run_eq_evalWith`: fold closed stateless `ProbComp.eval` runs into
  `OracleComp.evalWith`.
* `Cslib.ProbOracleComp.evalWith_run_interpret`: folds a stateful reduction run inside a stateless
  `OracleComp.evalWith` into `ProbOracleComp.runWith`.
* `Cslib.ProbOracleComp.evalWith_sumHandler_simulate`,
  `Cslib.ProbOracleComp.evalWith_interpret_sumHandler`: fold stateless `ProbOracleComp.simulate` and
  spelled-out sum-handler substitutions under `OracleComp.evalWith`.
* `Cslib.ProbOracleComp.runWith_eq_run_interpret`: folds the spelled-out `ProbComp.unifOracle` sum
  handler run into `ProbOracleComp.runWith`.
* `Cslib.ProbOracleComp.runWith_interpret_sumHandler_eta`,
  `Cslib.ProbOracleComp.runWith_simulate_eta`: eta-expanded forms of
  `ProbOracleComp.runWith_interpret_sumHandler` and `ProbOracleComp.runWith_simulate` so
  `runWith_norm` also steps concrete handler bodies when the client program is a black-box
  parameter.
* `Cslib.ProbOracleComp.runWith_pure_state`: folds a deterministic memoryless raw oracle
  `fun q state => PMF.pure (f q, state)` into `OracleComp.evalWith` after `PMF.pure_map`
  simplifies `(PMF.pure (f q)).map (·, state)`.
* `Cslib.ProbOracleComp.runWith_liftLeft`, `Cslib.ProbOracleComp.runWith_liftRight`: step
  `ProbOracleComp.runWith` across `OracleComp.liftLeft` and `OracleComp.liftRight`.
* `Cslib.ProbOracleComp.evalWith_sumHandler_unifOracle_sample`,
  `Cslib.ProbOracleComp.evalWith_sumHandler_sample`,
  `Cslib.ProbOracleComp.evalWith_sumHandler_query`: step `OracleComp.evalWith` across
  `ProbOracleComp.sample` and `ProbOracleComp.query`.
* `Cslib.Probability.PMF.map_id'`: eta-expanded `p.map (fun x => x) = p` rule matching
  composed projections `(p.map (·, s)).map Prod.fst`.
-/

public section

namespace Cslib

/-- Evaluating a `ProbOracleComp` against a stateless `ProbComp` oracle is `OracleComp.evalWith`
with `ProbComp.unifOracle` and the evaluated oracle. -/
theorem ProbOracleComp.eval_interpret_eq_evalWith {Query α : Type} {spec : Query → Type}
    (oracle : (q : Query) → ProbComp (spec q)) (program : ProbOracleComp spec α) :
    ProbComp.eval (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin oracle) program) =
      OracleComp.evalWith
        (OracleComp.sumHandler ProbComp.unifOracle (fun q => ProbComp.eval (oracle q)))
        program :=
  (ProbOracleComp.eval_interpret oracle program).trans
    (OracleComp.evalWith_eq_interpret _ _).symm

/-- Evaluating `program.run oracle` is `OracleComp.evalWith` with `ProbComp.unifOracle` and the
evaluated oracle. -/
theorem ProbOracleComp.eval_run_eq_evalWith {Query α : Type} {spec : Query → Type}
    (oracle : (q : Query) → ProbComp (spec q)) (program : ProbOracleComp spec α) :
    ProbComp.eval (program.run oracle) =
      OracleComp.evalWith
        (OracleComp.sumHandler ProbComp.unifOracle (fun q => ProbComp.eval (oracle q)))
        program :=
  ProbOracleComp.eval_interpret_eq_evalWith oracle program

/-- Evaluating a stateful `ProbOracleComp` handler run under a stateless `PMF` external oracle is
`ProbOracleComp.runWith` against the evaluated handler. -/
theorem ProbOracleComp.evalWith_run_interpret {Query Query' State α : Type}
    {spec : Query → Type} {spec' : Query' → Type}
    (oracle : (q : Query) → PMF (spec q))
    (handler : (q : Query') → StateT State (ProbOracleComp spec) (spec' q))
    (program : ProbOracleComp spec' α) (s : State) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle oracle)
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          handler)
        program).run s) =
      ProbOracleComp.runWith
        (fun q state =>
          OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle oracle)
            ((handler q).run state))
        program s := by
  induction program using ProbOracleComp.induction generalizing s with
  | pure a => rfl
  | sample_bind n cont ih =>
    rw [ProbOracleComp.runWith_sample_bind]
    simp only [OracleComp.interpret_bind, StateT.run_bind, OracleComp.evalWith_bind,
      ProbOracleComp.run_interpret_lift_sample, OracleComp.evalWith_map, PMF.bind_map,
      Function.comp_def, ih]
    rfl
  | query_bind q cont ih =>
    simp only [OracleComp.interpret_bind, StateT.run_bind, OracleComp.evalWith_bind,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, ProbOracleComp.interpret_query,
      ih]

/-- Eta-expanded form of `ProbOracleComp.runWith_interpret_sumHandler` supplying the state argument
to the inner `ProbOracleComp.runWith`, so `runWith_norm` normalizes concrete handler programs even
when `program` is an opaque adversary. -/
theorem ProbOracleComp.runWith_interpret_sumHandler_eta {Query Query' State α : Type}
    {spec : Query → Type} {spec' : Query' → Type}
    (oracle : (q : Query) → StateT State PMF (spec q))
    (handler : (q : Query') → ProbOracleComp spec (spec' q)) (program : ProbOracleComp spec' α)
    (s : State) :
    ProbOracleComp.runWith oracle
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n)) handler)
        program) s =
      ProbOracleComp.runWith (fun q state => ProbOracleComp.runWith oracle (handler q) state)
        program s :=
  ProbOracleComp.runWith_interpret_sumHandler oracle handler program s

/-- Eta-expanded form of `ProbOracleComp.runWith_simulate` supplying the state argument to the inner
`ProbOracleComp.runWith`, so `runWith_norm` normalizes concrete handler programs even when `program`
is an opaque adversary. -/
theorem ProbOracleComp.runWith_simulate_eta.{u, v, w} {Query : Type u} {Query' : Type v}
    {State : Type} {α : Type w} {spec : Query → Type} {spec' : Query' → Type}
    (oracle : (q : Query) → StateT State PMF (spec q))
    (handler : (q : Query') → ProbOracleComp spec (spec' q)) (program : ProbOracleComp spec' α)
    (s : State) :
    ProbOracleComp.runWith oracle (ProbOracleComp.simulate handler program) s =
      ProbOracleComp.runWith (fun q state => ProbOracleComp.runWith oracle (handler q) state)
        program s :=
  ProbOracleComp.runWith_simulate oracle handler program s

/-- Evaluating `ProbOracleComp.simulate handler program` under a stateless sum handler evaluates
`program` against the evaluated handler programs while preserving uniform private sampling. -/
theorem ProbOracleComp.evalWith_sumHandler_simulate.{u, v, w} {Query : Type u} {Query' : Type v}
    {α : Type w} {spec : Query → Type} {spec' : Query' → Type}
    (oracle : (q : Query) → PMF (spec q))
    (handler : (q : Query') → ProbOracleComp spec (spec' q))
    (program : ProbOracleComp spec' α) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle oracle)
      (ProbOracleComp.simulate handler program) =
      OracleComp.evalWith
        (OracleComp.sumHandler ProbComp.unifOracle
          (fun q =>
            OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle oracle) (handler q)))
        program := by
  rw [ProbOracleComp.simulate, OracleComp.evalWith_substitute, OracleComp.evalWith_sumHandler]
  congr 2 with n : 1
  rw [ProbOracleComp.sample_eq_liftLeft, OracleComp.evalWith_sumHandler_liftLeft,
    ← ProbComp.eval_eq_evalWith, ProbComp.eval_unifFin]
  rfl

/-- Spelled-out `OracleComp.interpret` counterpart of `ProbOracleComp.evalWith_sumHandler_simulate`,
folding a stateless handler substitution under `OracleComp.evalWith` while preserving
`ProbComp.unifOracle` on private samples. -/
theorem ProbOracleComp.evalWith_interpret_sumHandler {Query Query' α : Type}
    {spec : Query → Type} {spec' : Query' → Type}
    (oracle : (q : Query) → PMF (spec q))
    (handler : (q : Query') → ProbOracleComp spec (spec' q))
    (program : ProbOracleComp spec' α) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle oracle)
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n)) handler)
        program) =
      OracleComp.evalWith
        (OracleComp.sumHandler ProbComp.unifOracle
          (fun q =>
            OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle oracle) (handler q)))
        program := by
  rw [← OracleComp.substitute_eq_interpret]
  exact ProbOracleComp.evalWith_sumHandler_simulate oracle handler program

/-- Against a deterministic memoryless raw oracle returning `(f q, state)`, `ProbOracleComp.runWith`
evaluates `program` against `fun q => PMF.pure (f q)` and leaves `s` unchanged. Unlike
`ProbOracleComp.runWith_memoryless`, this matches after `PMF.pure_map` simplifies
`(PMF.pure (f q)).map (·, state)` inside `simp only [runWith_norm, pmf_norm]`. -/
theorem ProbOracleComp.runWith_pure_state.{u, w, s} {Query : Type u} {spec : Query → Type}
    {State : Type s} {α : Type w} (f : (q : Query) → spec q) (program : ProbOracleComp spec α)
    (s : State) :
    ProbOracleComp.runWith (fun q state => PMF.pure (f q, state)) program s =
      (OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle (fun q => PMF.pure (f q)))
        program).map (·, s) := by
  simpa only [PMF.pure_map] using
    ProbOracleComp.runWith_memoryless (fun q => PMF.pure (f q)) program s

/-- Evaluating an embedded private sample under a sum handler uses only the sampling handler. -/
theorem ProbOracleComp.evalWith_sumHandler_sample {Query α : Type} {spec : Query → Type}
    (random : (n : ℕ) → PMF (Fin (n + 1))) (oracle : (q : Query) → PMF (spec q))
    (program : ProbComp α) :
    OracleComp.evalWith (OracleComp.sumHandler random oracle)
      (ProbOracleComp.sample (spec := spec) program) =
      OracleComp.evalWith random program :=
  OracleComp.evalWith_sumHandler_liftLeft random oracle program

/-- Evaluating a single external query under a sum handler invokes the external handler. -/
theorem ProbOracleComp.evalWith_sumHandler_query {Query : Type} {spec : Query → Type}
    (random : (n : ℕ) → PMF (Fin (n + 1))) (oracle : (q : Query) → PMF (spec q))
    (q : Query) :
    OracleComp.evalWith (OracleComp.sumHandler random oracle)
      (ProbOracleComp.query (spec := spec) q) =
      oracle q :=
  OracleComp.evalWith_query _ (Sum.inr q)

/-- Evaluating an embedded private sample under `ProbComp.unifOracle` and an external handler gives
`ProbComp.eval`. -/
theorem ProbOracleComp.evalWith_sumHandler_unifOracle_sample {Query α : Type}
    {spec : Query → Type} (oracle : (q : Query) → PMF (spec q)) (program : ProbComp α) :
    OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle oracle)
      (ProbOracleComp.sample (spec := spec) program) =
      ProbComp.eval program :=
  OracleComp.evalWith_sumHandler_liftLeft ProbComp.unifOracle oracle program

/-- Running an embedded left (`ProbComp`) program under `ProbOracleComp.runWith` evaluates the
program and leaves the oracle state unchanged. -/
theorem ProbOracleComp.runWith_liftLeft {Query State α : Type} {spec : Query → Type}
    (oracle : (q : Query) → StateT State PMF (spec q))
    (program : ProbComp α) (s : State) :
    ProbOracleComp.runWith oracle (OracleComp.liftLeft (spec₂ := spec) program) s =
      (ProbComp.eval program).map (·, s) :=
  ProbOracleComp.runWith_sample oracle program s

/-- Running an embedded right (`OracleComp spec`) program under `ProbOracleComp.runWith` runs it
directly against `oracle` via `OracleComp.runWith`. -/
theorem ProbOracleComp.runWith_liftRight {Query State α : Type} {spec : Query → Type}
    (oracle : (q : Query) → StateT State PMF (spec q))
    (program : OracleComp spec α) (s : State) :
    ProbOracleComp.runWith oracle (OracleComp.liftRight program) s =
      OracleComp.runWith oracle program s :=
  OracleComp.runWith_sumHandler_liftRight _ oracle program s

/-- Eta-expanded form of `PMF.map_id`, matching `p.map (fun x => x)` after `PMF.map_comp` and
`Function.comp_def` unfold `(p.map (·, s)).map Prod.fst`. -/
theorem Probability.PMF.map_id' {α : Type*} (p : PMF α) : p.map (fun x => x) = p :=
  PMF.map_id p

end Cslib

-- Handler composition and memoryless oracle rules get higher priority than syntax-stepping rules so
-- `runWith` and `evalWith` fold composite handlers and memoryless oracles before unfolding concrete
-- `do` syntax.
attribute [runWith_norm 1200]
  Cslib.ProbOracleComp.eval_interpret_eq_evalWith
  Cslib.ProbOracleComp.eval_run_eq_evalWith
  Cslib.ProbOracleComp.evalWith_run_interpret
  Cslib.ProbOracleComp.evalWith_sumHandler_simulate
  Cslib.ProbOracleComp.evalWith_interpret_sumHandler
  Cslib.ProbOracleComp.eval_run_interpret_eq_runWith
  Cslib.ProbOracleComp.runWith_interpret_sumHandler_eta
  Cslib.ProbOracleComp.runWith_simulate_eta
  Cslib.ProbOracleComp.runWith_run_interpret

attribute [runWith_norm ← 1200] Cslib.ProbOracleComp.runWith_eq_run_interpret

attribute [runWith_norm 1100]
  Cslib.ProbOracleComp.runWith_lift
  Cslib.ProbOracleComp.runWith_memoryless
  Cslib.ProbOracleComp.runWith_pure_state
  Cslib.ProbOracleComp.runWith_sample_bind
  Cslib.ProbOracleComp.evalWith_sumHandler_unifOracle_sample
  Cslib.OracleComp.runWith_lift
  Cslib.OracleComp.runWith_memoryless

attribute [runWith_norm]
  Cslib.ProbOracleComp.runWith_pure
  Cslib.ProbOracleComp.runWith_bind
  Cslib.ProbOracleComp.runWith_map
  Cslib.ProbOracleComp.runWith_query
  Cslib.ProbOracleComp.runWith_sample
  Cslib.ProbOracleComp.runWith_liftLeft
  Cslib.ProbOracleComp.runWith_liftRight
  Cslib.OracleComp.runWith_pure
  Cslib.OracleComp.runWith_bind
  Cslib.OracleComp.runWith_map
  Cslib.OracleComp.runWith_query
  Cslib.OracleComp.runWith_sumHandler_liftLeft
  Cslib.OracleComp.runWith_sumHandler_liftRight
  Cslib.OracleComp.evalWith_pure
  Cslib.OracleComp.evalWith_bind
  Cslib.OracleComp.evalWith_map
  Cslib.OracleComp.evalWith_query
  Cslib.OracleComp.evalWith_interpret
  Cslib.OracleComp.evalWith_sumHandler_liftLeft
  Cslib.OracleComp.evalWith_sumHandler_liftRight
  Cslib.OracleComp.sumHandler_inl
  Cslib.OracleComp.sumHandler_inr
  Cslib.ProbOracleComp.evalWith_sumHandler_sample
  Cslib.ProbOracleComp.evalWith_sumHandler_query
  Cslib.ProbOracleComp.sample_pure
  Cslib.ProbOracleComp.sample_bind
  Cslib.ProbOracleComp.sample_map
  Cslib.Probability.PMF.map_id'
  PMF.map_id
  Prod.map_apply
  Prod.map_fst
  Prod.map_snd
  id_eq

end
