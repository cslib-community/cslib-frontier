/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: local-only (test)

-- `import all`: the `fuel = 4` run is evaluated by `rfl` through the unexposed body of
-- `ucPushSystem` and its private nodes `envNode`, `advNode`, `protoNode`, from the initial state
-- built with the private `ucState3` and `AdvState.idle`.
import all CslibFrontier.Crypto.Protocols.UC.PushProperties

/-!
# Fuel boundary of the UC pull-to-push bridge

A tight witness for the fuel budget `2 * bZ * (tA + 1) + 1` of
`Cslib.Crypto.Protocols.UC.Push.eval_pushRun_ucPushSystem` with `bZ = 1` and `tA = 1`: the
environment `tightEnv` makes one adversary query and the adversary `tightAdv` makes one network
query. At `fuel = 5` the push run of `ucPushSystem` halts with `UC.exec`'s output `some true`; at
the off-by-one budget `fuel = 4` it has not halted and returns `none` with probability `1`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPushBridgeFuel

open Cslib
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.UC
open Cslib.Crypto.Protocols.UC.Push
open Cslib.Probability

/-- A one-party protocol whose network port negates its query bit. -/
private abbrev tightProto : Protocol 1 Unit Unit Bool Bool :=
  fun _ _ => {
    State := Unit
    init := pure ()
    handle
      | .inl _, s => pure (none, s)
      | .inr q, s => pure (!q, s) }

/-- An adversary making exactly one network query per activation. -/
private abbrev tightAdv : ExecAdversary 1 Unit Unit Bool Bool Unit Bool :=
  fun _ _ => {
    State := Unit
    init := pure ()
    handle
      | (), () => do
        let r : Option Unit ⊕ Bool ← ProbOracleComp.query (.inr false)
        pure (match r with | .inl _ => false | .inr b => b, ()) }

/-- An environment making exactly one adversary query and outputting its answer. -/
private abbrev tightEnv : Environment 1 Unit Unit Unit Bool :=
  fun _ _ => ProbOracleComp.query (Sum.inr ())

private abbrev tightSystem := ucPushSystem tightProto tightAdv ∅ tightEnv

private theorem tightEnv_bounded (κ : ℕ) (z : List Bool) :
    ProbOracleComp.IsQueryBounded (tightEnv κ z) 1 :=
  ProbOracleComp.isCostBounded_query (fun _ => 1) _

private theorem tightAdv_bounded (κ : ℕ) : (tightAdv κ ∅).IsBounded 1 := by
  refine ⟨OracleComp.IsCostBounded.pure _ 1, fun () () => ?_⟩
  dsimp only [tightAdv, StateT.run, OracleComp.IsQueryBounded, ProbOracleComp.query]
  exact (OracleComp.IsCostBounded.query _).bind fun _ => OracleComp.IsCostBounded.pure _ 0

private theorem eval_exec_tight (κ : ℕ) (z : List Bool) :
    (exec tightProto tightAdv ∅ tightEnv κ z).eval = PMF.pure true :=
  rfl

/-- Tight fuel boundary of `eval_pushRun_ucPushSystem` at `bZ = 1`, `tA = 1`: with
`fuel = 5 = 2 * bZ * (tA + 1) + 1` the push run of `tightSystem` agrees with `UC.exec` and outputs
`some true`, while with `fuel = 4` it outputs `none` with probability `1` and so differs from
`UC.exec`. -/
theorem tightSystem_fuel_boundary (κ : ℕ) (z : List Bool) :
    (pushRun tightSystem κ z 5).eval = (exec tightProto tightAdv ∅ tightEnv κ z).eval.map some ∧
      (pushRun tightSystem κ z 5).eval = PMF.pure (some true) ∧
      (pushRun tightSystem κ z 4).eval = PMF.pure none ∧
      (pushRun tightSystem κ z 4).eval ≠
        (exec tightProto tightAdv ∅ tightEnv κ z).eval.map some := by
  have h5 := eval_pushRun_ucPushSystem tightProto tightAdv ∅ tightEnv κ z
    (tightEnv_bounded κ z) (tightAdv_bounded κ) (le_refl 5)
  have h4 : (pushRun tightSystem κ z 4).eval = PMF.pure none := by
    rw [eval_pushRun_of_init_pure tightSystem κ z 4
      (ucState3 tightProto tightAdv ∅ tightEnv κ none (.idle ()) ())
      (fun j => by fin_cases j <;> rfl)]
    rfl
  refine ⟨h5, by rw [h5, eval_exec_tight, PMF.pure_map], h4, ?_⟩
  rw [h4, eval_exec_tight, PMF.pure_map]
  intro h
  have := congrArg (fun p : PMF (Option Bool) => p none) h
  simp at this

end CslibFrontierTests.Crypto.UCPushBridgeFuel
