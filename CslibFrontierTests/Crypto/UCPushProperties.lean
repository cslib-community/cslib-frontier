/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Protocols.UC.PushProperties

/-!
# Tests for Fuel Properties and Pull-to-Push Bridge of UC Push Execution

Concrete witnesses exercising `Cslib.Crypto.Protocols.UC.Push`:
* **Probabilistic adaptive-halting witness**: a 2-node push system where node `0` halts immediately
  in 1 step on coin `0` (with `false`) and routes through node `1` to halt in 3 steps on coin `1`
  (with `true`), witnessing strict probability monotonicity (`0 < 1/2`), support monotonicity, tight
  two-fuel truncation bound (`|0 - 1/2| = 1/2 ≤ 1/2`), fuel exhaustion (`none`), and halting
  invariance for all `fuel ≥ 3`.
* **Concrete 3-node pull-to-push bridge witness**: a 2-party stateful protocol `testProto`, a
  coin-flipping adversary `testAdv` querying corrupted party `1 ∈ {1}` and the network port, and an
  environment `testEnv` querying honest party `0`, blocked corrupted party `1`, and `testAdv`,
  verifying `eval_pushRun_ucPushSystem`, `eval_pushExec_ucPushSystem`, and
  `eval_pushExec_ucPushSystem_of_polyBounded` against the explicitly computed asymmetric output
  distribution (`true` with probability `1/4`, `false` with probability `3/4`) as well as the
  zero-fuel separation at `fuel = 0` (which holds for every push system). The positive under-fueled
  boundary of the bridge (`fuel = 5` halts, `fuel = 4` returns `none` at `bZ = 1`, `tA = 1`) is
  checked in `CslibFrontierTests/Crypto/UCPushBridgeFuel.lean`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPushProperties

open Cslib
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.UC
open Cslib.Crypto.Protocols.UC.Push
open Cslib.Probability

/-! ### Probabilistic Adaptive-Halting Witness (Fuel Monotonicity, Truncation, Invariance) -/

private abbrev branchEnv : ReactiveNode 2 Bool where
  State := Unit
  init := pure ()
  handle
    | .start _, _ => do
      let c ← ProbOracleComp.sample (ProbComp.unifFin 1)
      if c = 0 then
        pure (.halt false, ())
      else
        pure (.write 1 .input true, ())
    | .deliver e, _ => pure (.halt e.payload, ())
    | .resume, _ => pure (.halt false, ())

private abbrev echoPeer : ReactiveNode 2 Bool where
  State := Unit
  init := pure ()
  handle
    | .deliver e, _ => pure (.write 0 .subroutineOutput e.payload, ())
    | _, _ => pure (.yield, ())

private abbrev branchSystem : PushSystem 2 Bool where
  node _
    | 0 => branchEnv
    | 1 => echoPeer
  initial := 0
  control := fun _ _ => true

private def bState (κ : ℕ) : (SSP.parFin (branchSystem.node κ)).State
  | 0 => ()
  | 1 => ()

private theorem bState_update_0 (κ : ℕ) :
    (Function.update (bState κ) 0 () : (SSP.parFin (branchSystem.node κ)).State) = bState κ := by
  funext j; fin_cases j <;> rfl

private theorem bState_update_1 (κ : ℕ) :
    (Function.update (bState κ) 1 () : (SSP.parFin (branchSystem.node κ)).State) = bState κ := by
  funext j; fin_cases j <;> rfl

private theorem branchEnv_start (z : List Bool) :
    (branchEnv.handle (.start z)).run () =
      ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun c =>
        pure (if c = 0 then (.halt false, ()) else (.write 1 .input true, ())) := by
  simp only [branchEnv]
  refine bind_congr fun c => ?_
  split_ifs <;> rfl

private theorem branchSystem_run0 (κ : ℕ) (z : List Bool) :
    (pushRun branchSystem κ z 0).eval = PMF.pure none :=
  eval_pushRun_zero branchSystem κ z

private theorem branchSystem_run1 (κ : ℕ) (z : List Bool) :
    (pushRun branchSystem κ z 1).eval =
      (PMF.uniformOfFintype (Fin 2)).map (fun c => if c = 0 then some false else none) := by
  rw [eval_pushRun_of_init_pure branchSystem κ z 1 (bState κ)
    (fun j => by fin_cases j <;> rfl)]
  rw [runFrom_iterate_step_succ_of_not_mem_halted branchSystem κ 0 rfl
    (by simp [TokenState.initialFor])]
  dsimp only [TokenState.initialFor]
  have h0 : ((branchSystem.node κ 0).handle (.start z)).run (bState κ 0) =
      ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun c =>
        pure (if c = 0 then (.halt false, ()) else (.write 1 .input true, ())) :=
    branchEnv_start z
  rw [h0, bind_assoc]
  simp only [Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_pure,
    map_bind, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_unifFin, PMF.pure_bind]
  refine congrArg ((PMF.uniformOfFintype (Fin 2)).bind) (funext fun c => ?_)
  fin_cases c
  · erw [Machine.runFrom_pure]
    simp [Machine.closeProgram_pure]
  · erw [Machine.runFrom_pure]
    simp [Machine.closeProgram_pure]

private theorem branchSystem_run3 (κ : ℕ) (z : List Bool) :
    (pushRun branchSystem κ z 3).eval =
      (PMF.uniformOfFintype (Fin 2)).map (fun c => some (decide (c ≠ 0))) := by
  rw [eval_pushRun_of_init_pure branchSystem κ z 3 (bState κ)
    (fun j => by fin_cases j <;> rfl)]
  rw [runFrom_iterate_step_succ_of_not_mem_halted branchSystem κ 2 rfl
    (by simp [TokenState.initialFor])]
  dsimp only [TokenState.initialFor]
  have h0 : ((branchSystem.node κ 0).handle (.start z)).run (bState κ 0) =
      ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun c =>
        pure (if c = 0 then (.halt false, ()) else (.write 1 .input true, ())) :=
    branchEnv_start z
  rw [h0, bind_assoc]
  simp only [Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_pure,
    map_bind, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_unifFin, PMF.pure_bind]
  refine congrArg ((PMF.uniformOfFintype (Fin 2)).bind) (funext fun c => ?_)
  fin_cases c
  · split_ifs with hc
    · erw [runFrom_iterate_step_of_output_isSome branchSystem κ 2 (by simp)]
      simp [Machine.closeProgram_pure]
    · exact absurd rfl hc
  · split_ifs with hc
    · contradiction
    · erw [runFrom_iterate_step_succ_of_handle_eq_pure branchSystem κ 1
        (by simp) (by simp) (by simp; rfl)
        (by rw [bState_update_0]; exact bState_update_1 κ)]
      erw [runFrom_iterate_step_succ_of_handle_eq_pure branchSystem κ 0
        (by simp) (by simp) (by simp; rfl) (bState_update_0 κ)]
      erw [Machine.runFrom_pure]
      simp [Machine.closeProgram_pure]

/-- At `fuel = 1`, `branchSystem` outputs `some true` with probability `0`, `some false` with
probability `1/2`, and exhausts fuel (`none`) with probability `1/2`. -/
theorem branchSystem_eval1 (κ : ℕ) (z : List Bool) :
    (pushRun branchSystem κ z 1).eval (some true) = 0 ∧
      (pushRun branchSystem κ z 1).eval (some false) = 1 / 2 ∧
      (pushRun branchSystem κ z 1).eval none = 1 / 2 := by
  rw [branchSystem_run1]
  refine ⟨?_, ?_, ?_⟩
  · rw [PMF.map_apply, tsum_fintype]
    simp
  · rw [PMF.map_apply, tsum_fintype]
    simp [PMF.uniformOfFintype_apply]
  · rw [PMF.map_apply, tsum_fintype]
    simp [PMF.uniformOfFintype_apply]

/-- At `fuel = 3`, `branchSystem` halts with probability `1`: `some true` has probability `1/2`,
`some false` has probability `1/2`, and `none` has probability `0`. -/
theorem branchSystem_eval3 (κ : ℕ) (z : List Bool) :
    (pushRun branchSystem κ z 3).eval (some true) = 1 / 2 ∧
      (pushRun branchSystem κ z 3).eval (some false) = 1 / 2 ∧
      (pushRun branchSystem κ z 3).eval none = 0 := by
  rw [branchSystem_run3]
  refine ⟨?_, ?_, ?_⟩
  · rw [PMF.map_apply, tsum_fintype]
    simp [PMF.uniformOfFintype_apply]
  · rw [PMF.map_apply, tsum_fintype]
    simp [PMF.uniformOfFintype_apply]
  · rw [PMF.map_apply, tsum_fintype]
    simp

/-- Strict monotonicity, support preservation, tight two-fuel truncation bound, and halting
invariance on `branchSystem` for all `fuel ≥ 3`. -/
theorem branchSystem_properties (κ : ℕ) (z : List Bool) :
    (pushRun branchSystem κ z 1).eval (some true) <
        (pushRun branchSystem κ z 3).eval (some true) ∧
      some false ∈ (pushRun branchSystem κ z 1).eval.support ∧
      some false ∈ (pushRun branchSystem κ z 3).eval.support ∧
      |((pushExec branchSystem κ z 1).eval true).toReal -
          ((pushExec branchSystem κ z 3).eval true).toReal| =
        ((pushRun branchSystem κ z 1).eval none).toReal ∧
      (∀ fuel ≥ 3,
        (pushRun branchSystem κ z fuel).eval = (pushRun branchSystem κ z 3).eval ∧
          (pushExec branchSystem κ z fuel).eval = (pushExec branchSystem κ z 3).eval) := by
  obtain ⟨h1t, h1f, h1n⟩ := branchSystem_eval1 κ z
  obtain ⟨h3t, _, h3n⟩ := branchSystem_eval3 κ z
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h1t, h3t]
    norm_num
  · rw [PMF.mem_support_iff, h1f]
    norm_num
  · refine support_pushRun_some_mono branchSystem κ z (by omega : 1 ≤ 3) ?_
    rw [PMF.mem_support_iff, h1f]
    norm_num
  · have _hle := abs_toReal_pushExec_sub_le branchSystem κ z (by omega : 1 ≤ 3)
    rw [eval_pushExec_true_eq, eval_pushExec_true_eq, h1t, h3t, h1n]
    norm_num
  · intro fuel hfuel
    exact ⟨eval_pushRun_eq_of_none_eq_zero branchSystem κ z h3n hfuel,
      eval_pushExec_eq_of_none_eq_zero branchSystem κ z h3n hfuel⟩

/-! ### Concrete 3-Node Pull-to-Push Bridge Witness -/

/-- A 2-party stateful protocol: party `0` records its input bit and returns its negation; party `1`
echoes its input bit; network queries return `xor q s`. -/
private abbrev testProto : Protocol 2 Bool Bool Bool Bool :=
  fun _ _ => {
    State := Bool
    init := pure false
    handle
      | .inl (0, x), _ => pure (some (!x), x)
      | .inl (_, x), s => pure (some x, s)
      | .inr q, s => pure (xor q s, s) }

/-- A coin-flipping adversary querying corrupted party `1 ∈ {1}` and the protocol network port. -/
private abbrev testAdv : ExecAdversary 2 Bool Bool Bool Bool Bool Bool :=
  fun _ _ => {
    State := Unit
    init := pure ()
    handle
      | q, () => do
        let c ← ProbOracleComp.sample (ProbComp.unifFin 1)
        let r₁ : Option Bool ⊕ Bool ← ProbOracleComp.query (.inl (1, q))
        let r₂ : Option Bool ⊕ Bool ← ProbOracleComp.query (.inr q)
        let b₁ := match r₁ with | .inl o => o.getD false | .inr b => b
        let b₂ := match r₂ with | .inl o => o.getD false | .inr b => b
        pure (xor (decide (c = 0)) (xor b₁ b₂), ()) }

/-- An environment querying honest party `0`, blocked corrupted party `1`, and `testAdv`. -/
private abbrev testEnv : Environment 2 Bool Bool Bool Bool :=
  fun _ _ => do
    let b₀ ← ProbOracleComp.sample (ProbComp.unifFin 1)
    let o₀ : Option Bool ← ProbOracleComp.query (Sum.inl (0, decide (b₀ = 0)))
    let o₁ : Option Bool ← ProbOracleComp.query (Sum.inl (1, true))
    let a : Bool ← ProbOracleComp.query (Sum.inr true)
    pure (o₀.getD false && (o₁.isSome || a))

private theorem testEnv_bounded (κ : ℕ) (z : List Bool) :
    ProbOracleComp.IsQueryBounded (testEnv κ z) 3 := by
  dsimp only [testEnv, ProbOracleComp.IsQueryBounded]
  exact (ProbOracleComp.IsQueryBounded.sample _).bind fun _ =>
    (ProbOracleComp.isCostBounded_query (fun _ => 1) _).bind fun _ =>
      (ProbOracleComp.isCostBounded_query (fun _ => 1) _).bind fun _ =>
        (ProbOracleComp.isCostBounded_query (fun _ => 1) _).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0

private theorem testEnv_totalBounded (κ : ℕ) (z : List Bool) :
    OracleComp.IsQueryBounded (testEnv κ z) 4 := by
  dsimp only [testEnv, OracleComp.IsQueryBounded, ProbOracleComp.query]
  exact (OracleComp.IsCostBounded.query (cost := fun _ => 1) (Sum.inl 1)).bind fun _ =>
    (OracleComp.IsCostBounded.query (cost := fun _ => 1) _).bind fun _ =>
      (OracleComp.IsCostBounded.query (cost := fun _ => 1) _).bind fun _ =>
        (OracleComp.IsCostBounded.query (cost := fun _ => 1) _).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0

private theorem testAdv_bounded (κ : ℕ) : (testAdv κ {1}).IsBounded 3 := by
  refine ⟨?_, fun q () => ?_⟩
  · dsimp only [testAdv]
    exact OracleComp.IsCostBounded.pure _ 3
  · dsimp only [testAdv, StateT.run, OracleComp.IsQueryBounded, ProbOracleComp.query]
    exact (OracleComp.IsCostBounded.query (Sum.inl 1)).bind fun _ =>
      (OracleComp.IsCostBounded.query _).bind fun _ =>
        (OracleComp.IsCostBounded.query _).bind fun _ =>
          OracleComp.IsCostBounded.pure _ 0

private theorem exec_test_eval (κ : ℕ) (z : List Bool) :
    (exec testProto testAdv {1} testEnv κ z).eval =
      (PMF.uniformOfFintype (Fin 2)).bind fun b₀ =>
        (PMF.uniformOfFintype (Fin 2)).map fun c =>
          !decide (b₀ = 0) && decide (c = 0) := by
  have hrun : (execMachine testProto testAdv κ {1}).runFrom (testEnv κ z) ((), false) =
      ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun b₀ =>
        ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun c =>
          pure (!decide (b₀ = 0) && decide (c = 0), ((), decide (b₀ = 0))) := by
    dsimp only [testEnv]
    erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left]
    refine bind_congr fun b₀ => ?_
    erw [Machine.runFrom_bind]
    have hq0 : (execMachine testProto testAdv κ {1}).runFrom
        (ProbOracleComp.query (.inl (0, decide (b₀ = 0)))) ((), false) =
        pure (some (!decide (b₀ = 0)), ((), decide (b₀ = 0))) := rfl
    erw [hq0, pure_bind, Machine.runFrom_bind]
    have hq1 : (execMachine testProto testAdv κ {1}).runFrom
        (ProbOracleComp.query (.inl (1, true))) ((), decide (b₀ = 0)) =
        pure (none, ((), decide (b₀ = 0))) := rfl
    erw [hq1, pure_bind, Machine.runFrom_bind]
    have hqA : (execMachine testProto testAdv κ {1}).runFrom
        (ProbOracleComp.query (.inr true)) ((), decide (b₀ = 0)) =
        ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun c =>
          pure (xor (decide (c = 0)) (xor true (xor true (decide (b₀ = 0)))),
            ((), decide (b₀ = 0))) := by
      change (Prod.map _root_.id id <$>
          (Equiv.prodAssoc _ _ _ <$>
            (corruptRouter {1} (testProto κ {1})).runFrom
              (Machine.liftRightProgram (partySpec 2 Bool Bool)
                (((testAdv κ {1}).handle true).run ())) (decide (b₀ = 0)))) = _
      change Equiv.prodAssoc _ _ _ <$>
          ((corruptRouter {1} (testProto κ {1})).runFrom
            (ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun c =>
              ProbOracleComp.query (Sum.inr (Sum.inl (1, true))) >>=
                fun (r₁ : Option Bool ⊕ Bool) =>
                ProbOracleComp.query (Sum.inr (Sum.inr true)) >>=
                  fun (r₂ : Option Bool ⊕ Bool) =>
                  let b₁ := match r₁ with | .inl o => o.getD false | .inr b => b
                  let b₂ := match r₂ with | .inl o => o.getD false | .inr b => b
                  pure (xor (decide (c = 0)) (xor b₁ b₂), ())) (decide (b₀ = 0))) = _
      erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left, map_bind]
      refine bind_congr fun c => ?_
      erw [Machine.runFrom_bind]
      have hcr1 : (corruptRouter {1} (testProto κ {1})).runFrom
          (ProbOracleComp.query (.inr (.inl (1, true)))) (decide (b₀ = 0)) =
          pure (.inl (some true), decide (b₀ = 0)) := rfl
      erw [hcr1, pure_bind, Machine.runFrom_bind]
      have hcr2 : (corruptRouter {1} (testProto κ {1})).runFrom
          (ProbOracleComp.query (.inr (.inr true))) (decide (b₀ = 0)) =
          pure (.inr (xor true (decide (b₀ = 0))), decide (b₀ = 0)) := rfl
      erw [hcr2, pure_bind]
      rfl
    erw [hqA, bind_assoc]
    refine bind_congr fun c => ?_
    erw [pure_bind, Machine.runFrom_pure]
    simp only [Option.getD_some, Option.isSome_none, Bool.false_or]
    cases b₀ using Fin.cases with
    | zero =>
      have hz : (!decide ((0 : Fin 2) = 0) &&
          (decide (c = 0) ^^ (true ^^ (true ^^ decide ((0 : Fin 2) = 0))))) =
          (!decide ((0 : Fin 2) = 0) && decide (c = 0)) := by revert c; decide
      erw [hz]; rfl
    | succ j =>
      fin_cases j
      have hs : (!decide ((1 : Fin 2) = 0) &&
          (decide (c = 0) ^^ (true ^^ (true ^^ decide ((1 : Fin 2) = 0))))) =
          (!decide ((1 : Fin 2) = 0) && decide (c = 0)) := by revert c; decide
      erw [hs]; rfl
  rw [exec, Machine.run]
  change (Machine.closeProgram
      (ProbOracleComp.sample (execMachine testProto testAdv κ {1}).init >>= fun x =>
        Prod.fst <$> (execMachine testProto testAdv κ {1}).runFrom (testEnv κ z) x)).eval = _
  have hinit : (execMachine testProto testAdv κ {1}).init = pure ((), false) := rfl
  rw [Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_bind]
  erw [hinit, ProbComp.eval_pure, PMF.pure_bind, hrun]
  erw [map_bind]
  simp only [Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_bind,
    ProbComp.eval_unifFin]
  refine congrArg ((PMF.uniformOfFintype (Fin 2)).bind) (funext fun b₀ => ?_)
  erw [map_bind, Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_bind,
    ProbComp.eval_unifFin]
  refine congrArg ((PMF.uniformOfFintype (Fin 2)).bind) (funext fun c => ?_)
  erw [map_pure, Machine.closeProgram_pure, ProbComp.eval_pure]
  rfl

/-- Exact pull-to-push bridge equality and asymmetric output distribution (`1/4` true, `3/4` false)
for `ucPushSystem testProto testAdv {1} testEnv` for all `fuel ≥ 25`, together with
`eval_pushExec_ucPushSystem_of_polyBounded` (`fuel ≥ 33`) and zero-fuel separation (`fuel = 0`). -/
theorem ucBridge_properties (κ : ℕ) (z : List Bool) :
    (∀ fuel ≥ 25,
      (pushRun (ucPushSystem testProto testAdv {1} testEnv) κ z fuel).eval =
        (exec testProto testAdv {1} testEnv κ z).eval.map some ∧
      (pushExec (ucPushSystem testProto testAdv {1} testEnv) κ z fuel).eval =
        (exec testProto testAdv {1} testEnv κ z).eval ∧
      (pushExec (ucPushSystem testProto testAdv {1} testEnv) κ z fuel).eval true = 1 / 4 ∧
      (pushExec (ucPushSystem testProto testAdv {1} testEnv) κ z fuel).eval false = 3 / 4) ∧
    (∀ fuel ≥ 33,
      (pushExec (ucPushSystem testProto testAdv {1} testEnv) κ z fuel).eval =
        (exec testProto testAdv {1} testEnv κ z).eval) ∧
    (pushRun (ucPushSystem testProto testAdv {1} testEnv) κ z 0).eval = PMF.pure none ∧
    (pushRun (ucPushSystem testProto testAdv {1} testEnv) κ z 0).eval ≠
      (exec testProto testAdv {1} testEnv κ z).eval.map some := by
  have hpZ : testEnv.PolyBounded (Polynomial.C 4) := fun κ z => by
    simpa only [Polynomial.eval_C] using testEnv_totalBounded κ z
  have hpA : testAdv.PolyBounded (Polynomial.C 3) := fun κ _ => by
    simpa only [Polynomial.eval_C] using testAdv_bounded κ
  have hTrue : (exec testProto testAdv {1} testEnv κ z).eval true = 1 / 4 := by
    rw [exec_test_eval, PMF.bind_apply, tsum_fintype, Fin.sum_univ_two]
    simp only [PMF.map_apply, tsum_fintype, Fin.sum_univ_two, PMF.uniformOfFintype_apply,
      Fintype.card_fin]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    simp
    norm_num
  have hFalse : (exec testProto testAdv {1} testEnv κ z).eval false = 3 / 4 := by
    rw [exec_test_eval, PMF.bind_apply, tsum_fintype, Fin.sum_univ_two]
    simp only [PMF.map_apply, tsum_fintype, Fin.sum_univ_two, PMF.uniformOfFintype_apply,
      Fintype.card_fin]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp
    norm_num
  have hfuel0 : (pushRun (ucPushSystem testProto testAdv {1} testEnv) κ z 0).eval = PMF.pure none :=
    eval_pushRun_zero (ucPushSystem testProto testAdv {1} testEnv) κ z
  refine ⟨fun fuel hfuel => ?_, fun fuel hfuel => ?_, hfuel0, ?_⟩
  · refine ⟨eval_pushRun_ucPushSystem testProto testAdv {1} testEnv κ z
        (testEnv_bounded κ z) (testAdv_bounded κ) (by omega),
      eval_pushExec_ucPushSystem testProto testAdv {1} testEnv κ z
        (testEnv_bounded κ z) (testAdv_bounded κ) (by omega), ?_, ?_⟩
    · rw [eval_pushExec_ucPushSystem testProto testAdv {1} testEnv κ z
        (testEnv_bounded κ z) (testAdv_bounded κ) (by omega), hTrue]
    · rw [eval_pushExec_ucPushSystem testProto testAdv {1} testEnv κ z
        (testEnv_bounded κ z) (testAdv_bounded κ) (by omega), hFalse]
  · exact eval_pushExec_ucPushSystem_of_polyBounded testProto testAdv {1} testEnv
      hpZ hpA κ z (by simp only [Polynomial.eval_C]; omega)
  · intro heq
    have hnone := congrArg (fun p : PMF (Option Bool) => p none) heq
    rw [hfuel0, PMF.pure_apply, PMF.map_apply] at hnone
    simp at hnone

end CslibFrontierTests.Crypto.UCPushProperties
