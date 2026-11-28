/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SSP.Basic
public import CslibFrontier.Crypto.Protocols.UC.Reactive
public import CslibFrontier.Languages.Probabilistic.Iteration
import CslibFrontier.Languages.Probabilistic.QueryCount.Iterate

/-!
# Single-Token Push Execution for UC Interactive Machines

This file defines the fuel-bounded single-token push runtime over a `PushSystem` of `m` reactive
nodes, iterating `step S` via `OracleComp.iterate` against the parallel composition
`SSP.parFin (S.node κ)` of the system's nodes.

The operational model follows the single-token activation model of [Canetti2020], §3.1.2
(JACM pp. 28:23–28:24) and §3.3.2, "Deleting ITIs" (JACM p. 28:33), with the following library
conventions:
- All `m` nodes are fixed in advance and initialized eagerly via `SSP.parFin`.
- `fuel` counts scheduler steps (including steps whose target is already in `ts.halted`, which
  make no network query and return control to `S.initial`), not node activations or running time.
- `pushRun` returns `Option Bool`, yielding `none` if the initial node has not halted within
  `fuel` steps; `pushExec` reads `none` as `false`.

Relating this push execution to the pull-style execution of
`CslibFrontier.Crypto.Protocols.UC.Execution`, as well as bounding running time rather than
scheduler steps and oracle call counts (computational polynomial-time UC execution), remain open
under `#6043`.

## Main definitions

* `step`: one scheduler step of a push system (together with its `@[simp]` branch equations
  `step_of_output_isSome`, `step_of_mem_halted`, and `step_of_not_mem_halted`).
* `pushRun`: fuel-bounded push execution via `OracleComp.iterate fuel (step S)`, returning
  `Option Bool`.
* `pushExec`: fuel-bounded push execution returning `Bool` (fuel exhaustion read as `false`).

## Main results

* `runFrom_iterate_step_succ_of_not_mem_halted`, `runFrom_iterate_step_succ_of_mem_halted`,
  `runFrom_iterate_step_of_output_isSome`: three-branch operational unfolding of
  `OracleComp.iterate _ (step S)` against `SSP.parFin`, with
  `runFrom_iterate_step_succ_of_handle_eq_pure` for deterministic handler steps.
* `isQueryBounded_step`, `isQueryBounded_iterate_step`, `isQueryBounded_pushRun`: query-count
  budgets for single steps, `fuel`-step runs, and closed push executions of bounded reactive
  nodes (call-count budgets only; computational polynomial time is open in `#6043`).
* `eval_pushRun`, `eval_pushRun_of_init_pure`, `eval_pushRun_zero`: output distribution of
  `pushRun`, specialization to deterministic node initializers, and zero-fuel base case.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], §3.1.2 (JACM pp. 28:23–28:24)
  and §3.3.2, "Deleting ITIs" (JACM p. 28:33).
-/

public section

namespace Cslib.Crypto.Protocols.UC.Push

variable {m : ℕ} {Msg : Type}

/-- Library construction (no cited definition): one scheduler step of a push system `S` from state
`ts`, in this library's push reading of [Canetti2020], §3.1.2 (JACM pp. 28:23–28:24) and §3.3.2,
"Deleting ITIs" (JACM p. 28:33). A finished run (`ts.output.isSome`) is left unchanged with no
network query. A halted target performs no operation and the initial node is activated next with
`.resume` (§3.3.2, "Deleting ITIs", of [Canetti2020], JACM p. 28:33), costing one unit of fuel and
making no network query (a library convention). Otherwise `ts.target` is activated with
`ts.delivery` (one query to the network, ending the activation at its outcome) and `TokenState.next`
applies its outcome. -/
@[expose] def step (S : PushSystem m Msg) (ts : TokenState m Msg) :
    ProbOracleComp (SSP.sessionSpec m (netSpec (Delivery m Msg) (Outcome m Msg)))
      (TokenState m Msg) :=
  match ts.output with
  | some _ => pure ts
  | none =>
    if ts.target ∈ ts.halted then
      pure { ts with target := S.initial, delivery := .resume }
    else do
      let a ← ProbOracleComp.query (ts.target, ts.delivery)
      return ts.next S a

/-- Library infrastructure (no cited result): a finished run performs no network query and leaves
the scheduler state unchanged. -/
@[simp] theorem step_of_output_isSome (S : PushSystem m Msg) {ts : TokenState m Msg}
    (h : ts.output.isSome) : step S ts = pure ts := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  simp [step, hb]

/-- Library infrastructure (no cited result): activating a halted non-initial node makes no
network query and returns control to the initial node with `.resume`. -/
@[simp] theorem step_of_mem_halted (S : PushSystem m Msg) {ts : TokenState m Msg}
    (ho : ts.output = none) (hh : ts.target ∈ ts.halted) :
    step S ts = pure { ts with target := S.initial, delivery := .resume } := by
  simp [step, ho, hh]

/-- Library infrastructure (no cited result): activating a running, non-halted node queries the
network once and applies `TokenState.next`. -/
@[simp] theorem step_of_not_mem_halted (S : PushSystem m Msg) {ts : TokenState m Msg}
    (ho : ts.output = none) (hh : ts.target ∉ ts.halted) :
    step S ts = (do
      let a ← ProbOracleComp.query (ts.target, ts.delivery)
      return ts.next S a) := by
  simp [step, ho, hh]

/-- Library construction (no cited definition): the single-token execution of a push system, in
this library's push reading of [Canetti2020], §3.1.2 (JACM pp. 28:23–28:24) and §3.3.2, "Deleting
ITIs" (JACM p. 28:33), narrower in having a fixed node set initialized eagerly, nodes addressed by
index, every write forced and sender-revealing, a control function over the delivered log, and an
activation that ends without a write returning control to the initial node (a library convention).
The result is the initial node's output bit, or `none` if it has not halted within `fuel` steps
(a library convention, where `fuel` counts scheduler steps rather than running time). Relating this
push execution to `CslibFrontier.Crypto.Protocols.UC.Execution` and bounding computational running
time remain open under `#6043`. -/
@[expose] def pushRun (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel : ℕ) :
    ProbComp (Option Bool) :=
  TokenState.output <$>
    (SSP.parFin (S.node κ)).run
      (OracleComp.iterate fuel (step S) (TokenState.initialFor S.initial z))

/-- Library construction (no cited definition): the output bit of a push execution, in this
library's push reading of [Canetti2020], §3.1.2 (JACM pp. 28:23–28:24) and §3.3.2, "Deleting ITIs"
(JACM p. 28:33), narrower as in `pushRun` and with fuel exhaustion read as `false` (a library
convention). -/
@[expose] def pushExec (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel : ℕ) :
    ProbComp Bool :=
  (fun r => r.getD false) <$> pushRun S κ z fuel

/-- Library infrastructure (no cited result): one scheduler step makes at most one network query
(zero when the run has finished or the target is halted). -/
theorem isQueryBounded_step (S : PushSystem m Msg) (ts : TokenState m Msg) :
    (step S ts).IsQueryBounded 1 := by
  unfold step
  cases ts.output with
  | some _ => exact OracleComp.IsCostBounded.pure _ 1
  | none =>
    split_ifs
    · exact OracleComp.IsCostBounded.pure _ 1
    · simp only [bind_pure_comp, ProbOracleComp.query]
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- Library infrastructure (no cited result): a run of `fuel` scheduler steps makes at most
`fuel` network queries (activating nodes at most `fuel` times). -/
theorem isQueryBounded_iterate_step (S : PushSystem m Msg) (fuel : ℕ) (ts : TokenState m Msg) :
    (OracleComp.iterate fuel (step S) ts).IsQueryBounded fuel := by
  simpa using OracleComp.IsCostBounded.iterate (isQueryBounded_step S) fuel ts

/-- Library infrastructure (no cited result): when every node of `S` at security parameter `κ` has
per-activation call budget `t`, a `fuel`-step push run makes at most `m * t + fuel * (m * t + 1)`
coin draws (toward `#6043`; call-count budgets only, while computational polynomial-time UC
execution is open in `#6043`). -/
theorem isQueryBounded_pushRun (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel t : ℕ)
    (h : ∀ j : Fin m, (S.node κ j).IsBounded t) :
    (pushRun S κ z fuel).IsQueryBounded (m * t + fuel * (m * t + 1)) :=
  (OracleComp.isCostBounded_map_iff _ _ _).mpr
    (Machine.isQueryBounded_closeProgram
      (Machine.isQueryBounded_link (SSP.isBounded_parFin h)
        (isQueryBounded_iterate_step S fuel (TokenState.initialFor S.initial z))))

/-- Library infrastructure (no cited result): one active scheduler step against `SSP.parFin`
runs `ts.target`'s handler on `ts.delivery`, updates `ts.target`'s state slot, and continues with
`ts.next S`. -/
theorem runFrom_iterate_step_succ_of_not_mem_halted (S : PushSystem m Msg) (κ f : ℕ)
    {ts : TokenState m Msg} (ho : ts.output = none) (hh : ts.target ∉ ts.halted)
    (s : (SSP.parFin (S.node κ)).State) :
    (SSP.parFin (S.node κ)).runFrom (OracleComp.iterate (f + 1) (step S) ts) s =
      (((S.node κ ts.target).handle ts.delivery).run (s ts.target)) >>= fun x =>
        (SSP.parFin (S.node κ)).runFrom (OracleComp.iterate f (step S) (ts.next S x.1))
          (Function.update s ts.target x.2) := by
  rw [OracleComp.iterate_succ_bind, step_of_not_mem_halted S ho hh, bind_assoc]
  simp only [pure_bind, Machine.runFrom_bind, Machine.runFrom_query, SSP.parFin_handle,
    bind_map_left]

/-- Library infrastructure (no cited result): when `ts.target`'s handler on `ts.delivery`
deterministically returns `(out, v)`, one active scheduler step against `SSP.parFin` continues
with `ts.next S out` from the state `s'` obtained by writing `v` into `ts.target`'s slot. -/
theorem runFrom_iterate_step_succ_of_handle_eq_pure (S : PushSystem m Msg) (κ f : ℕ)
    {ts : TokenState m Msg} (ho : ts.output = none) (hh : ts.target ∉ ts.halted)
    {s s' : (SSP.parFin (S.node κ)).State} {out : Outcome m Msg}
    {v : (S.node κ ts.target).State}
    (hstep : ((S.node κ ts.target).handle ts.delivery).run (s ts.target) = pure (out, v))
    (hs : (Function.update s ts.target v : (SSP.parFin (S.node κ)).State) = s') :
    (SSP.parFin (S.node κ)).runFrom (OracleComp.iterate (f + 1) (step S) ts) s =
      (SSP.parFin (S.node κ)).runFrom (OracleComp.iterate f (step S) (ts.next S out)) s' := by
  rw [runFrom_iterate_step_succ_of_not_mem_halted S κ f ho hh s, hstep, pure_bind, hs]

/-- Library infrastructure (no cited result): one scheduler step on a halted target against
`SSP.parFin` makes no node activation and returns control to `S.initial` with `.resume`. -/
theorem runFrom_iterate_step_succ_of_mem_halted (S : PushSystem m Msg) (κ f : ℕ)
    {ts : TokenState m Msg} (ho : ts.output = none) (hh : ts.target ∈ ts.halted)
    (s : (SSP.parFin (S.node κ)).State) :
    (SSP.parFin (S.node κ)).runFrom (OracleComp.iterate (f + 1) (step S) ts) s =
      (SSP.parFin (S.node κ)).runFrom
        (OracleComp.iterate f (step S) { ts with target := S.initial, delivery := .resume }) s := by
  rw [OracleComp.iterate_succ_bind, step_of_mem_halted S ho hh, pure_bind]

/-- Library infrastructure (no cited result): once `ts.output.isSome`, any remaining scheduler
steps against `SSP.parFin` perform no node activation and return `(ts, s)` unchanged. -/
theorem runFrom_iterate_step_of_output_isSome (S : PushSystem m Msg) (κ f : ℕ)
    {ts : TokenState m Msg} (ho : ts.output.isSome)
    (s : (SSP.parFin (S.node κ)).State) :
    (SSP.parFin (S.node κ)).runFrom (OracleComp.iterate f (step S) ts) s = pure (ts, s) := by
  rw [OracleComp.iterate_eq_pure f (step S) ts (step_of_output_isSome S ho),
    Machine.runFrom_pure]

/-- Library infrastructure (no cited result): the output distribution of `pushRun` binds the
joint initial-state distribution `(SSP.parFin (S.node κ)).init.eval` into the closed `fuel`-step
execution from that joint state. Unlike `Cslib.Crypto.Protocols.SSP.eval_run`, which translates a
run into an `OracleComp.interpret` over `PMF` handlers for state-simulation proofs, this lemma
keeps the `Machine.closeProgram`/`Machine.runFrom` form so callers can step
`OracleComp.iterate _ (step S)` directly via `runFrom_iterate_step_succ_of_not_mem_halted`,
`runFrom_iterate_step_succ_of_mem_halted`, and `runFrom_iterate_step_of_output_isSome` before
closing. -/
theorem eval_pushRun (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel : ℕ) :
    (pushRun S κ z fuel).eval =
      ((SSP.parFin (S.node κ)).init).eval.bind fun s₀ =>
        ((TokenState.output ∘ Prod.fst) <$>
          Machine.closeProgram
            ((SSP.parFin (S.node κ)).runFrom
              (OracleComp.iterate fuel (step S) (TokenState.initialFor S.initial z)) s₀)).eval := by
  simp only [pushRun, Machine.run, Machine.link, map_bind, Functor.map_map,
    Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_map,
    ProbComp.eval_bind, Function.comp_def]

/-- Library infrastructure (no cited result): when every node of `S` at security parameter `κ`
initializes deterministically to `s₀ j`, `pushRun` runs directly from the joint state `s₀`. -/
theorem eval_pushRun_of_init_pure (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel : ℕ)
    (s₀ : (SSP.parFin (S.node κ)).State) (h : ∀ j, (S.node κ j).init = pure (s₀ j)) :
    (pushRun S κ z fuel).eval =
      ((TokenState.output ∘ Prod.fst) <$>
        Machine.closeProgram
          ((SSP.parFin (S.node κ)).runFrom
            (OracleComp.iterate fuel (step S) (TokenState.initialFor S.initial z)) s₀)).eval := by
  rw [eval_pushRun, show (SSP.parFin (S.node κ)).init.eval = PMF.pure s₀ from
    (ProbComp.eval_pi_congr fun j => by rw [h j, ProbComp.eval_pure]).trans
      (ProbComp.eval_pi_pure s₀), PMF.pure_bind]

/-- Library infrastructure (no cited result): a zero-fuel push run evaluates to `PMF.pure none`
(node initial states are sampled and discarded). -/
theorem eval_pushRun_zero (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) :
    (pushRun S κ z 0).eval = PMF.pure none := by
  simp only [eval_pushRun, OracleComp.iterate_zero, Machine.runFrom_pure,
    Machine.closeProgram_pure, map_pure, Function.comp_apply, TokenState.initialFor,
    ProbComp.eval_pure]
  exact PMF.bind_const _ _

end Cslib.Crypto.Protocols.UC.Push
