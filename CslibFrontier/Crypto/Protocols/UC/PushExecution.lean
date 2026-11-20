/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SSP.Basic
public import CslibFrontier.Crypto.Protocols.UC.Reactive

/-!
# Single-Token Push Execution for UC Interactive Machines

This file defines the fuel-bounded single-token push runtime over a `PushSystem` of `m` reactive
nodes, running the scheduler `steps` against the parallel composition `SSP.parFin (S.node κ)` of
the system's nodes.

The operational model follows the single-token activation model of §3.1.2 of [Canetti2020]
(JACM pp. 28:22–28:24, 28:33; ePrint pp. 23–24, 34), with the following library conventions:
- All `m` nodes are fixed in advance and initialized eagerly via `SSP.parFin`.
- `fuel` counts scheduler steps (including steps whose target is already in `ts.halted`, which
  make no network query and return control to `S.initial`), not node activations or running time.
- `pushRun` returns `Option Bool`, yielding `none` if the initial node has not halted within
  `fuel` steps; `pushExec` reads `none` as `false`.

The relation to the pull-style execution of `CslibFrontier.Crypto.Protocols.UC.Execution` is not
proved here.

## Main definitions

* `step`: one scheduler step of a push system.
* `steps`: `fuel` scheduler steps composed sequentially.
* `pushRun`: fuel-bounded push execution returning `Option Bool`.
* `pushExec`: fuel-bounded push execution returning `Bool` (fuel exhaustion read as `false`).

## Main results

* `step_of_output_isSome`, `step_of_mem_halted`, `step_of_not_mem_halted`: `@[simp]` equations
  for each branch of `step`.
* `steps_zero`, `steps_succ`, `steps_add`, `steps_of_output_isSome`: structural laws for `steps`.
* `runFrom_steps_succ_of_not_mem_halted`, `runFrom_steps_succ_of_mem_halted`: single-step
  operational unfolding of `steps` against `SSP.parFin`.
* `isQueryBounded_step`, `isQueryBounded_steps`, `isQueryBounded_pushRun`: query-count bounds for
  single steps, `fuel`-step runs, and closed push executions of bounded reactive nodes.
* `eval_pushRun`, `eval_pushRun_of_init_pure`, `eval_pushRun_zero`: output distribution of
  `pushRun`, specialization to deterministic node initializers, and zero-fuel base case.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], §3.1.2
  (JACM pp. 28:22–28:24, 28:33; ePrint pp. 23–24, 34).
-/

public section

namespace Cslib.Crypto.Protocols.UC.Push

variable {m : ℕ} {Msg : Type}

/-- One scheduler step of a push system `S` from state `ts`. A finished run (`ts.output.isSome`)
is left unchanged with no network query. A halted target performs no operation and the initial
node is activated next with `.resume` (§3.1.2 of [Canetti2020], JACM p. 28:33, ePrint p. 34),
costing one unit of fuel and making no network query. Otherwise `ts.target` is activated with
`ts.delivery` (one query to the network) and `TokenState.next` applies its outcome. -/
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

/-- `fuel` scheduler steps of a push system `S` starting from `ts`. Fuel counts scheduler steps
(including steps on halted targets, which make no network query), not node activations or
running time (a library convention). -/
@[expose] def steps (S : PushSystem m Msg) : ℕ → TokenState m Msg →
    ProbOracleComp (SSP.sessionSpec m (netSpec (Delivery m Msg) (Outcome m Msg)))
      (TokenState m Msg)
  | 0, ts => pure ts
  | f + 1, ts => do
    let ts' ← step S ts
    steps S f ts'

/-- Library infrastructure (no cited result): zero scheduler steps return the current state. -/
@[simp] theorem steps_zero (S : PushSystem m Msg) (ts : TokenState m Msg) :
    steps S 0 ts = pure ts := rfl

/-- Library infrastructure (no cited result): unfolding one scheduler step from `steps`. -/
theorem steps_succ (S : PushSystem m Msg) (f : ℕ) (ts : TokenState m Msg) :
    steps S (f + 1) ts = step S ts >>= steps S f := rfl

/-- Library infrastructure (no cited result): running two prefix lengths in sequence is running
their sum. -/
theorem steps_add (S : PushSystem m Msg) (a b : ℕ) (ts : TokenState m Msg) :
    steps S (a + b) ts = steps S a ts >>= steps S b := by
  induction a generalizing ts with
  | zero => simp [steps_zero]
  | succ a ih =>
    rw [Nat.succ_add, steps_succ, steps_succ, bind_assoc]
    exact bind_congr fun ts' => ih ts'

/-- Library infrastructure (no cited result): once the initial node has halted, further scheduler
steps change nothing. -/
@[simp] theorem steps_of_output_isSome (S : PushSystem m Msg) (f : ℕ)
    {ts : TokenState m Msg} (h : ts.output.isSome) : steps S f ts = pure ts := by
  induction f with
  | zero => rfl
  | succ f ih => rw [steps_succ, step_of_output_isSome S h, pure_bind, ih]

/-- The single-token execution of a push system, in this library's push reading of §3.1.2 of
[Canetti2020] (JACM pp. 28:22–28:24, 28:33; ePrint pp. 23–24, 34): a fixed node set initialized
eagerly, nodes addressed by index, every write forced and sender-revealing, a control function
over the delivered log, and an activation that ends without a write returning control to the
initial node (a library convention). The result is the initial node's output bit, or `none` if
it has not halted within `fuel` steps (a library convention). The relation to the pull execution
of `CslibFrontier.Crypto.Protocols.UC.Execution` is not proved here. -/
@[expose] def pushRun (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel : ℕ) :
    ProbComp (Option Bool) :=
  TokenState.output <$>
    (SSP.parFin (S.node κ)).run (steps S fuel (TokenState.initialFor S.initial z))

/-- The output bit of a push execution, in this library's push reading of §3.1.2 of [Canetti2020]
(JACM pp. 28:22–28:24, 28:33; ePrint pp. 23–24, 34), with fuel exhaustion read as `false`
(a library convention). -/
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
theorem isQueryBounded_steps (S : PushSystem m Msg) (fuel : ℕ) (ts : TokenState m Msg) :
    (steps S fuel ts).IsQueryBounded fuel := by
  induction fuel generalizing ts with
  | zero => exact OracleComp.IsCostBounded.pure ts 0
  | succ f ih =>
    rw [steps_succ, Nat.add_comm]
    exact (isQueryBounded_step S ts).bind fun ts' => ih ts'

/-- Library infrastructure (no cited result): when every node of `S` at security parameter `κ`
has per-activation call budget `t`, a `fuel`-step push run makes at most
`m * t + fuel * (m * t + 1)` coin draws. -/
theorem isQueryBounded_pushRun (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel t : ℕ)
    (h : ∀ j : Fin m, (S.node κ j).IsBounded t) :
    (pushRun S κ z fuel).IsQueryBounded (m * t + fuel * (m * t + 1)) :=
  (OracleComp.isCostBounded_map_iff _ _ _).mpr
    (Machine.isQueryBounded_closeProgram
      (Machine.isQueryBounded_link (SSP.isBounded_parFin h)
        (isQueryBounded_steps S fuel (TokenState.initialFor S.initial z))))

/-- Library infrastructure (no cited result): one active scheduler step against `SSP.parFin`
runs `ts.target`'s handler on `ts.delivery`, updates `ts.target`'s state slot, and continues with
`ts.next S`. -/
theorem runFrom_steps_succ_of_not_mem_halted (S : PushSystem m Msg) (κ f : ℕ)
    {ts : TokenState m Msg} (ho : ts.output = none) (hh : ts.target ∉ ts.halted)
    (s : (SSP.parFin (S.node κ)).State) :
    (SSP.parFin (S.node κ)).runFrom (steps S (f + 1) ts) s =
      (((S.node κ ts.target).handle ts.delivery).run (s ts.target)) >>= fun x =>
        (SSP.parFin (S.node κ)).runFrom (steps S f (ts.next S x.1))
          (Function.update s ts.target x.2) := by
  rw [steps_succ, step_of_not_mem_halted S ho hh, bind_assoc]
  simp only [pure_bind, Machine.runFrom_bind, Machine.runFrom_query, SSP.parFin_handle,
    bind_map_left]

/-- Library infrastructure (no cited result): one scheduler step on a halted target against
`SSP.parFin` makes no node activation and returns control to `S.initial` with `.resume`. -/
theorem runFrom_steps_succ_of_mem_halted (S : PushSystem m Msg) (κ f : ℕ)
    {ts : TokenState m Msg} (ho : ts.output = none) (hh : ts.target ∈ ts.halted)
    (s : (SSP.parFin (S.node κ)).State) :
    (SSP.parFin (S.node κ)).runFrom (steps S (f + 1) ts) s =
      (SSP.parFin (S.node κ)).runFrom
        (steps S f { ts with target := S.initial, delivery := .resume }) s := by
  rw [steps_succ, step_of_mem_halted S ho hh, pure_bind]

/-- Library infrastructure (no cited result): the output distribution of `pushRun` binds the
joint initial-state distribution `(SSP.parFin (S.node κ)).init.eval` into the closed `fuel`-step
execution from that joint state. -/
theorem eval_pushRun (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) (fuel : ℕ) :
    (pushRun S κ z fuel).eval =
      ((SSP.parFin (S.node κ)).init).eval.bind fun s₀ =>
        ((TokenState.output ∘ Prod.fst) <$>
          Machine.closeProgram
            ((SSP.parFin (S.node κ)).runFrom
              (steps S fuel (TokenState.initialFor S.initial z)) s₀)).eval := by
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
            (steps S fuel (TokenState.initialFor S.initial z)) s₀)).eval := by
  rw [eval_pushRun, show (SSP.parFin (S.node κ)).init.eval = PMF.pure s₀ from
    (ProbComp.eval_pi_congr fun j => by rw [h j, ProbComp.eval_pure]).trans
      (ProbComp.eval_pi_pure s₀), PMF.pure_bind]

/-- Library infrastructure (no cited result): a zero-fuel push run evaluates to `PMF.pure none`
(node initial states are sampled and discarded). -/
theorem eval_pushRun_zero (S : PushSystem m Msg) (κ : ℕ) (z : List Bool) :
    (pushRun S κ z 0).eval = PMF.pure none := by
  simp only [eval_pushRun, steps_zero, Machine.runFrom_pure, Machine.closeProgram_pure,
    map_pure, Function.comp_apply, TokenState.initialFor, ProbComp.eval_pure]
  exact PMF.bind_const _ _

end Cslib.Crypto.Protocols.UC.Push
