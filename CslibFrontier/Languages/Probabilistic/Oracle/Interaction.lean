/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.Semantics
import CslibFrontier.Languages.Probabilistic.Sum.Lift

/-!
# Running a program against a stateful oracle

A program with private samples and typed external calls (`Cslib.ProbOracleComp`) interacts with a
stateful probabilistic oracle answering each call `q` with an element of `spec q`, possibly at
random and updating a private state. `Cslib.ProbOracleComp.runWith` is the joint law of the result
and the final oracle state, with fresh fair samples for the private coins, and
`Cslib.ProbOracleComp.acceptProbWith` the probability that a Boolean program returns `true`.
A prover of an interactive proof is such an oracle; `Cslib.Complexity.Prover.run` is the case of
word queries and replies (`Cslib.Complexity.Prover.run_eq_runWith`).

`runWith` is the instance of the generic `OracleComp.runWith` whose handler is the sum
`OracleComp.sumHandler` of fresh uniform draws for private samples, which keep the state, and
`oracle` for external calls. Against a memoryless oracle it is `OracleComp.evalWith` of the sum of
the uniform handler and the oracle, with the state unchanged (`runWith_lift`). Its structural
rules are those of `OracleComp.runWith`; `Languages.Probabilistic.Oracle.Simulation` gives its
simulation and state-representation rules.

## Main definitions

* `Cslib.ProbOracleComp.runWith`: the joint law of the result and the final oracle state.
* `Cslib.ProbOracleComp.acceptProbWith`: the acceptance probability.

## Main results

* `Cslib.ProbOracleComp.runWith_memoryless`: against a memoryless raw oracle with
  independently-universed state, the instance of `OracleComp.evalWith`; `.runWith_lift` and
  `.acceptProbWith_lift` preserve the same-universe `StateT.lift` interface.
* `Cslib.ProbOracleComp.induction`: structural induction over returned values, private uniform
  draws and external calls; `Cslib.ProbOracleComp.sample_unifFin` identifies a draw with its
  sampling request.
* `Cslib.ProbOracleComp.runWith_pure`, `Cslib.ProbOracleComp.runWith_bind`,
  `Cslib.ProbOracleComp.runWith_map`, `Cslib.ProbOracleComp.runWith_query`,
  `Cslib.ProbOracleComp.runWith_sample`: ordinary same-universe structural rules for `runWith`;
  `.runWith_freeMBind` and `.runWith_freeMMap` are the heterogeneous forms.
* `Cslib.ProbOracleComp.eval_run_interpret_eq_runWith`: evaluating a closed run is `runWith`
  against the evaluated handler.
* `Cslib.ProbOracleComp.runWith_sample_bind`: a private sample averages the continuation's run;
  `Cslib.ProbOracleComp.runWith_sample_bind_congr` exchanges samples with the same law, and
  `Cslib.ProbOracleComp.runWith_sample_bind_comm` moves a sample past any program.
* `Cslib.ProbOracleComp.runWith_interpret`, `Cslib.ProbOracleComp.runWith_interpret_sumHandler`:
  running an interpreted program runs the original program against the handler programs' runs.
* `Cslib.ProbOracleComp.acceptProbWith_bind`: sequencing for acceptance probability.
* `Cslib.ProbOracleComp.acceptProbWith_query_bind`,
  `Cslib.ProbOracleComp.acceptProbWith_sample_bind`: averages over replies and samples.
* `Cslib.ProbOracleComp.acceptProbWith_bind_ite_le`: a check run only after another one accepted
  accepts at most as often.
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open scoped ENNReal

universe u v w s

variable {Query : Type} {spec : Query → Type} {State α β : Type}
  (oracle : (q : Query) → StateT State PMF (spec q))

/-- A private uniform draw is the sampling request that it embeds. -/
theorem sample_unifFin (n : ℕ) :
    sample (spec := spec) (ProbComp.unifFin n) = OracleComp.query (Sum.inl n) := by
  simp [sample, ProbComp.unifFin]

/-- Structural induction on a program with private samples and external calls: a returned value,
a private uniform draw followed by a continuation, or an external call followed by a
continuation. -/
@[elab_as_elim] theorem induction {motive : ProbOracleComp spec α → Prop}
    (pure : ∀ a, motive (pure a))
    (sample_bind : ∀ n (cont : Fin (n + 1) → ProbOracleComp spec α), (∀ i, motive (cont i)) →
      motive (sample (ProbComp.unifFin n) >>= cont))
    (query_bind : ∀ q (cont : spec q → ProbOracleComp spec α), (∀ a, motive (cont a)) →
      motive (query q >>= cont))
    (program : ProbOracleComp spec α) : motive program := by
  induction program using OracleComp.induction with
  | pure a => exact pure a
  | query_bind q cont ih =>
    cases q with
    | inl n => rw [← sample_unifFin]; exact sample_bind n cont ih
    | inr q => exact query_bind q cont ih

/-- The joint law of the result of `program` and the final state of the oracle answering its
external calls, starting from the state `s`. Private samples are fresh. This is the generic
stateful run `OracleComp.runWith` of the sum handler. -/
noncomputable def runWith {Query : Type u} {spec : Query → Type} {State : Type s}
    {α : Type w} (oracle : (q : Query) → State → PMF (spec q × State))
    (program : ProbOracleComp spec α) (s : State) : PMF (α × State) :=
  OracleComp.runWith
    (OracleComp.sumHandler (m := fun α => State → PMF (α × State))
      (fun n state => (ProbComp.unifOracle n).map (·, state)) oracle) program s

/-- On the single object universe supported by generic `StateT` interpretation, `runWith` agrees
with the original interpreter presentation. -/
theorem runWith_eq_run_interpret (program : ProbOracleComp spec α) (s : State) :
    runWith oracle program s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
        program).run s := by
  rw [runWith, OracleComp.runWith_eq_run_interpret]
  have hhandler :
      (OracleComp.sumHandler (m := fun α => State → PMF (α × State))
        (fun n state => (ProbComp.unifOracle n).map (·, state)) oracle) =
      OracleComp.sumHandler (m := StateT State PMF)
        (fun n => StateT.lift (ProbComp.unifOracle n)) oracle := by
    funext q state
    cases q with
    | inl n => simp only [OracleComp.sumHandler, StateT.lift, bind_pure_comp,
        PMF.monad_map_eq_map]
    | inr q => rfl
  exact congrArg
    (fun handler => (OracleComp.interpret (m := StateT State PMF) handler program).run s)
    hhandler

/-- The probability that `program` returns `true` against the raw oracle from the state `s`.
The query and state types may live in independent universes; replies remain small as required by
`ProbOracleComp`. -/
noncomputable def acceptProbWith {Query : Type u} {spec : Query → Type} {State : Type s}
    (oracle : (q : Query) → State → PMF (spec q × State))
    (program : ProbOracleComp spec Bool) (s : State) : ℝ≥0∞ :=
  (runWith oracle program s).map Prod.fst true

/-- Against a memoryless raw oracle with independently-universed state, the run is
`OracleComp.evalWith` of the uniform handler on the sampling side and the oracle on the other,
with the state unchanged. -/
theorem runWith_memoryless {Query : Type u} {spec : Query → Type} {State : Type s} {α : Type w}
    (h : (q : Query) → PMF (spec q)) (program : ProbOracleComp spec α) (s : State) :
    runWith (fun q state => (h q).map (·, state)) program s =
      (OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle h) program).map (·, s) := by
  have hsum :
      OracleComp.sumHandler (m := fun α => State → PMF (α × State))
          (fun n state => (ProbComp.unifOracle n).map (·, state))
          (fun q state => (h q).map (·, state)) =
        (fun q state =>
          (OracleComp.sumHandler ProbComp.unifOracle h q).map (·, state)) := by
    funext q state
    cases q <;> rfl
  rw [runWith, hsum, OracleComp.runWith_memoryless]

/-- Against a memoryless same-universe oracle expressed with `StateT.lift`, the run is
`OracleComp.evalWith` of the uniform handler and the oracle, with the state unchanged. -/
theorem runWith_lift (h : (q : Query) → PMF (spec q)) (program : ProbOracleComp spec α)
    (s : State) :
    runWith (fun q => StateT.lift (h q)) program s =
      (OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle h) program).map (·, s) := by
  rw [runWith_eq_run_interpret, OracleComp.sumHandler_lift, OracleComp.run_interpret_lift,
    ← OracleComp.evalWith_eq_interpret, _root_.PMF.monad_map_eq_map]

/-- Against a memoryless same-universe oracle expressed with `StateT.lift`, the acceptance
probability is the probability of `true` under `OracleComp.evalWith`. -/
theorem acceptProbWith_lift (h : (q : Query) → PMF (spec q)) (program : ProbOracleComp spec Bool)
    (s : State) :
    acceptProbWith (fun q => StateT.lift (h q)) program s =
      OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle h) program true := by
  rw [acceptProbWith, runWith_lift, PMF.map_comp,
    show (Prod.fst ∘ fun a : Bool => (a, s)) = id from rfl, PMF.map_id]

/-- A pure program returns its value and leaves the oracle state unchanged. -/
@[simp] theorem runWith_pure {Query : Type u} {spec : Query → Type} {State : Type s}
    {α : Type w} (oracle : (q : Query) → State → PMF (spec q × State)) (a : α) (s : State) :
    runWith oracle (pure a) s = PMF.pure (a, s) :=
  OracleComp.runWith_pure _ _ _

/-- Running a heterogeneous sequence runs the first program, then runs the continuation at its
result from the oracle state it reached. -/
@[simp] theorem runWith_freeMBind {Query : Type u} {spec : Query → Type} {State : Type s}
    {α : Type w} {β : Type v} (oracle : (q : Query) → State → PMF (spec q × State))
    (program : ProbOracleComp spec α) (next : α → ProbOracleComp spec β) (s : State) :
    runWith oracle (PFunctor.FreeM.bind program next) s =
      (runWith oracle program s).bind fun x => runWith oracle (next x.1) x.2 :=
  OracleComp.runWith_freeMBind _ _ _ _

/-- Running an ordinary same-universe sequence runs the first program, then runs the continuation
at its result from the oracle state it reached. -/
@[simp] theorem runWith_bind {Query : Type u} {spec : Query → Type} {State : Type s}
    {α β : Type w}
    (oracle : (q : Query) → State → PMF (spec q × State))
    (program : ProbOracleComp spec α) (next : α → ProbOracleComp spec β) (s : State) :
    runWith oracle (program >>= next) s =
      (runWith oracle program s).bind fun x => runWith oracle (next x.1) x.2 := by
  simpa only [PFunctor.FreeM.bind_eq_bind] using runWith_freeMBind oracle program next s

/-- Heterogeneously mapping `f` over a program maps it over the result and keeps the final oracle
state. -/
@[simp] theorem runWith_freeMMap {Query : Type u} {spec : Query → Type} {State : Type s}
    {α : Type w} {β : Type v} (oracle : (q : Query) → State → PMF (spec q × State))
    (f : α → β) (program : ProbOracleComp spec α) (s : State) :
    runWith oracle (PFunctor.FreeM.map f program) s =
      (runWith oracle program s).map (Prod.map f id) :=
  OracleComp.runWith_freeMMap _ _ _ _

/-- Ordinarily mapping `f` over a same-universe program maps it over the result and keeps the
final oracle state. -/
@[simp] theorem runWith_map {Query : Type u} {spec : Query → Type} {State : Type s}
    {α β : Type w}
    (oracle : (q : Query) → State → PMF (spec q × State))
    (f : α → β) (program : ProbOracleComp spec α) (s : State) :
    runWith oracle (f <$> program) s =
      (runWith oracle program s).map (Prod.map f id) := by
  simpa only [PFunctor.FreeM.map_eq_map] using runWith_freeMMap oracle f program s

/-- A single external call is answered by the oracle from the current state. -/
@[simp] theorem runWith_query {Query : Type u} {spec : Query → Type} {State : Type s}
    (oracle : (q : Query) → State → PMF (spec q × State)) (q : Query) (s : State) :
    runWith oracle (query (spec := spec) q) s = oracle q s :=
  OracleComp.runWith_query _ (Sum.inr q) _

/-- A private sample has the law of the sampled program and leaves the oracle state unchanged. -/
@[simp] theorem runWith_sample {Query : Type u} {spec : Query → Type} {State : Type s}
    {α : Type w} (oracle : (q : Query) → State → PMF (spec q × State))
    (program : ProbComp α) (s : State) :
    runWith oracle (sample (spec := spec) program) s = (ProbComp.eval program).map (·, s) :=
  by
    rw [runWith, sample_eq_liftLeft, OracleComp.runWith_sumHandler_liftLeft]
    exact OracleComp.runWith_memoryless _ _ _

/-- A private sample followed by a continuation averages the continuation's run over the sample,
from the same oracle state. -/
theorem runWith_sample_bind {Query : Type u} {spec : Query → Type} {State : Type s}
    {α β : Type w} (oracle : (q : Query) → State → PMF (spec q × State))
    (program : ProbComp α) (next : α → ProbOracleComp spec β)
    (s : State) :
    runWith oracle (sample program >>= next) s =
      (ProbComp.eval program).bind fun a => runWith oracle (next a) s := by
  rw [runWith_bind, runWith_sample, PMF.bind_map]
  rfl

/-- Private samples with the same law can be exchanged in front of any continuation. -/
theorem runWith_sample_bind_congr {Query : Type u} {spec : Query → Type} {State : Type s}
    {α β : Type w} (oracle : (q : Query) → State → PMF (spec q × State))
    {program program' : ProbComp α}
    (h : ProbComp.eval program = ProbComp.eval program') (next : α → ProbOracleComp spec β)
    (s : State) :
    runWith oracle (sample program >>= next) s = runWith oracle (sample program' >>= next) s := by
  rw [runWith_sample_bind, runWith_sample_bind, h]

/-- A private sample commutes with any program: since the draw neither reads nor changes the
oracle state, drawing it before or after the program gives the same run. -/
theorem runWith_sample_bind_comm {Query : Type u} {spec : Query → Type} {State : Type s}
    {α β γ : Type w} (oracle : (q : Query) → State → PMF (spec q × State))
    (program : ProbComp α)
    (other : ProbOracleComp spec β) (next : α → β → ProbOracleComp spec γ) (s : State) :
    runWith oracle (sample program >>= fun a => other >>= fun b => next a b) s =
      runWith oracle (other >>= fun b => sample program >>= fun a => next a b) s := by
  rw [runWith_sample_bind]
  conv_lhs => arg 2; ext a; rw [runWith_bind]
  rw [PMF.bind_comm, runWith_bind]
  congr 1
  funext b
  rw [← runWith_sample_bind]

/-- Running a program whose calls a handler answers with `ProbOracleComp spec` programs is a
stateful run of the original program, each call answered by running its handler program. -/
theorem runWith_interpret {ι : Type} {spec' : OracleSpec ι}
    (handler : (q : ι) → ProbOracleComp spec (spec' q)) (program : OracleComp spec' α)
    (s : State) :
    runWith oracle (OracleComp.interpret handler program) s =
      OracleComp.runWith (fun q => runWith oracle (handler q)) program s := by
  rw [runWith, ← OracleComp.substitute_eq_interpret handler program,
    OracleComp.runWith_substitute]
  rfl

/-- A program whose private draws are forwarded and whose external calls a handler answers with
`ProbOracleComp spec` programs runs against the oracle that runs each handler program. -/
theorem runWith_interpret_sumHandler {Query' : Type} {spec' : Query' → Type}
    (handler : (q : Query') → ProbOracleComp spec (spec' q)) (program : ProbOracleComp spec' α)
    (s : State) :
    runWith oracle (OracleComp.interpret
        (OracleComp.sumHandler (fun n => sample (ProbComp.unifFin n)) handler) program) s =
      runWith (fun q => runWith oracle (handler q)) program s := by
  rw [runWith_interpret, runWith]
  congr 1 with q t : 2
  cases q with
  | inl n =>
    simp [OracleComp.sumHandler, ProbComp.unifOracle, PMF.map, Function.comp_def]
  | inr q => rfl

/-- Evaluating a closed run, in which a handler program answers the external calls, is `runWith`
against the evaluated handler. -/
theorem eval_run_interpret_eq_runWith (oracle : (q : Query) → StateT State ProbComp (spec q))
    (program : ProbOracleComp spec α) (s : State) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) oracle) program).run s) =
      runWith (fun q state => ProbComp.eval (oracle q state)) program s :=
  (eval_run_interpret oracle program s).trans
    (OracleComp.runWith_eq_run_interpret _ _ _).symm

/-- A pure program accepts with probability `1` if it returns `true` and `0` otherwise. -/
theorem acceptProbWith_pure {Query : Type u} {spec : Query → Type} {State : Type s}
    (oracle : (q : Query) → State → PMF (spec q × State)) (b : Bool) (s : State) :
    acceptProbWith oracle (pure b) s = if b then 1 else 0 := by
  rw [acceptProbWith, runWith_pure, PMF.pure_map, PMF.pure_apply]
  cases b <;> simp

/-- An acceptance probability is at most `1`. -/
theorem acceptProbWith_le_one {Query : Type u} {spec : Query → Type} {State : Type s}
    (oracle : (q : Query) → State → PMF (spec q × State))
    (program : ProbOracleComp spec Bool) (s : State) :
    acceptProbWith oracle program s ≤ 1 :=
  PMF.coe_le_one _ _

/-- The acceptance probability of `program >>= next` averages the acceptance probability of `next`
over the joint law of the result and oracle state of `program`. -/
theorem acceptProbWith_bind {Query : Type u} {spec : Query → Type} {State : Type s}
    {α : Type} (oracle : (q : Query) → State → PMF (spec q × State))
    (program : ProbOracleComp spec α)
    (next : α → ProbOracleComp spec Bool) (s : State) :
    acceptProbWith oracle (program >>= next) s =
      ∑' x, runWith oracle program s x * acceptProbWith oracle (next x.1) x.2 := by
  rw [acceptProbWith, runWith_bind, PMF.map_bind, PMF.bind_apply]
  rfl

/-- The acceptance probability after an external call `q` averages over the oracle's replies and
next states. -/
theorem acceptProbWith_query_bind {Query : Type u} {spec : Query → Type} {State : Type s}
    (oracle : (q : Query) → State → PMF (spec q × State))
    (q : Query) (next : spec q → ProbOracleComp spec Bool) (s : State) :
    acceptProbWith oracle (query (spec := spec) q >>= next) s =
      ∑' x, oracle q s x * acceptProbWith oracle (next x.1) x.2 := by
  rw [acceptProbWith_bind, runWith_query]

/-- The acceptance probability after a private sample averages over the law of the sample, with
the oracle state unchanged. -/
theorem acceptProbWith_sample_bind {Query : Type u} {spec : Query → Type} {State : Type s}
    {α : Type} (oracle : (q : Query) → State → PMF (spec q × State))
    (program : ProbComp α) (next : α → ProbOracleComp spec Bool) (s : State) :
    acceptProbWith oracle (sample program >>= next) s =
      ∑' a, ProbComp.eval program a * acceptProbWith oracle (next a) s := by
  rw [acceptProbWith, runWith_bind, runWith_sample, PMF.bind_map, PMF.map_bind, PMF.bind_apply]
  rfl

/-- Running a second check only after a first one accepted accepts at most as often as the first
check. -/
theorem acceptProbWith_bind_ite_le {Query : Type u} {spec : Query → Type} {State : Type s}
    (oracle : (q : Query) → State → PMF (spec q × State))
    (program : ProbOracleComp spec Bool) (next : ProbOracleComp spec Bool) (s : State) :
    acceptProbWith oracle (program >>= fun b => if b then next else pure false) s ≤
      acceptProbWith oracle program s := by
  conv_rhs => rw [← bind_pure program, acceptProbWith_bind]
  rw [acceptProbWith_bind]
  refine tsum_le_tsum fun x => mul_le_mul_right ?_ _
  cases x.1
  · simp only [Bool.false_eq_true, ↓reduceIte, le_refl]
  · simp only [↓reduceIte, acceptProbWith_pure]
    exact acceptProbWith_le_one _ _ _

end Cslib.ProbOracleComp
