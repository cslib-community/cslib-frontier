/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.SSP.ParFinLazy
import CslibFrontier.Crypto.Protocols.UC.JointState

/-! # Lazy multi-session UC (c1a) witness tests -/
namespace CslibFrontierTests.Crypto.UCJointState
open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.UC

/-- Uniform-bit ideal functionality (`n = 2`): samples a bit at `init` and outputs it on poll. -/
def coinFunc : IdealFunctionality 2 Unit Bool Unit Unit where
  State := Bool
  init _ _ := (fun r : Fin 2 => decide (r.val = 0)) <$> ProbComp.unifFin 1
  onInput _ _ s := pure (some s, s)
  onBackdoor _ s := pure ((), s)

/-- Deliberately wrong shared-copy functionality: ignores `ssid` and shares one global coin. -/
def wrongSharedCoinFunc :
    IdealFunctionality 2 (SubSessionInput (Fin 2) Unit) Bool
      (SubSessionBackdoor (Fin 2) Unit) Unit where
  State := Bool
  init _ _ := (fun r : Fin 2 => decide (r.val = 0)) <$> ProbComp.unifFin 1
  onInput _ _ s := pure (some s, s)
  onBackdoor _ s := pure ((), s)

/-- Single-session coin machine used to witness lazy sampling (`run_parFinLazy_eq_parFin`). -/
def coinMachine : Machine OracleSpec.empty (fun _ : Unit => Bool) where
  State := Bool
  init := (fun r : Fin 2 => decide (r.val = 0)) <$> ProbComp.unifFin 1
  handle _ s := pure (s, s)

/-- Witness 1 (lazy creation is real): polling only copy `1` leaves `sessions 0 = none` and
initializes copy `1`. -/
theorem lazy_creation_witness :
    ((Machine.closeProgram
        ((fun (_, s') => decide (s'.sessions 0 = none ∧ (s'.sessions 1).isSome)) <$>
          (corruptRouter ∅ ((coinFunc.multiSession (Fin 2)).toProtocol 0 ∅)).runFrom
            (ProbOracleComp.query (Sum.inl ((0 : Fin 2), ⟨(1 : Fin 2), ()⟩)))
            { secParam := 0, corrupted := ∅, sessions := fun _ => none })).eval) =
      PMF.pure true := by
  simp only [corruptRouter, IdealFunctionality.multiSession, IdealFunctionality.toProtocol,
    coinFunc, Machine.runFrom_query, StateT.run, Machine.closeProgram_map,
    Machine.closeProgram_sample, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_unifFin, Finset.notMem_empty, ↓reduceIte, pure_bind, bind_map_left,
    PMF.map_bind]
  ext b
  simp only [PMF.bind_apply, Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
    tsum_fintype, Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one, decide_true,
    PMF.pure_apply]
  cases b <;> simp [ENNReal.inv_two_add_inv_two]

private def twoCopiesEnv : Environment 2 (SubSessionInput (Fin 2) Unit) Bool
    (RoutedNetQ 2 (SubSessionInput (Fin 2) Unit) (SubSessionBackdoor (Fin 2) Unit))
    (RoutedNetR Bool Unit) := fun _ _ => do
  let b₀ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), ⟨(0 : Fin 2), ()⟩))
  let b₁ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), ⟨(1 : Fin 2), ()⟩))
  pure (decide (b₀ = b₁))

/-- Witness 2 (copies are independent, not shared): `coinFunc.multiSession` yields
`Pr[b₀ = b₁] = 1/2`, whereas the wrong shared-state functionality yields `1`, so the executions
differ. -/
theorem copies_independent_witness :
    (exec (coinFunc.multiSession (Fin 2)).toProtocol
        (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval true = (2 : ENNReal)⁻¹ ∧
      (exec wrongSharedCoinFunc.toProtocol
        (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval true = 1 ∧
      (exec (coinFunc.multiSession (Fin 2)).toProtocol
        (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval ≠
      (exec wrongSharedCoinFunc.toProtocol
        (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval := by
  have hInd : (exec (coinFunc.multiSession (Fin 2)).toProtocol
      (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval true = (2 : ENNReal)⁻¹ := by
    rw [exec_dummyAdversary]
    simp only [twoCopiesEnv, corruptRouter, IdealFunctionality.multiSession,
      IdealFunctionality.toProtocol, coinFunc, Machine.run, Machine.link,
      Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure,
      Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_map,
      Machine.closeProgram_pure, ProbOracleComp.sample_pure, pure_bind, map_bind,
      bind_map_left, StateT.run, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_unifFin, Function.update_of_ne Fin.zero_ne_one.symm,
      Finset.notMem_empty, ↓reduceIte, PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
    simp only [PMF.bind_apply, Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
      tsum_fintype, Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one, PMF.pure_apply,
      Nat.one_ne_zero, decide_false, decide_true, Option.some.injEq, Bool.true_eq_false,
      Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add]
    rw [← mul_add]
    simp [ENNReal.inv_two_add_inv_two]
  have hShared : (exec wrongSharedCoinFunc.toProtocol
      (dummyAdversary 2 _ _) ∅ twoCopiesEnv 0 []).eval true = 1 := by
    rw [exec_dummyAdversary]
    simp only [twoCopiesEnv, corruptRouter, IdealFunctionality.toProtocol, wrongSharedCoinFunc,
      Machine.run, Machine.link, Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure,
      Machine.closeProgram_bind, Machine.closeProgram_sample, ProbOracleComp.sample_pure, pure_bind,
      bind_map_left, StateT.run, ProbComp.eval_bind,
      ProbComp.eval_unifFin, Finset.notMem_empty, ↓reduceIte]
    simp only [PMF.bind_apply, Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
      tsum_fintype, Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one]
    simp [ENNReal.inv_two_add_inv_two]
  refine ⟨hInd, hShared, fun heq => ?_⟩
  have h12 := congrArg (fun p : PMF Bool => p true) heq
  rw [hInd, hShared] at h12
  norm_num at h12

/-- Witness 3 (lazy sampling via `SSP.run_parFinLazy_eq_parFin` at `m = 2` touching `1, 0, 1`):
session `1` keeps the same coin across two calls while session `0` samples independently. -/
theorem lazy_sampling_witness :
    let prog : ProbOracleComp
        (SSP.sessionSpec 2 (fun _ : Unit => Bool)) Bool := do
      let b₁ ← ProbOracleComp.query ((1 : Fin 2), ())
      let b₀ ← ProbOracleComp.query ((0 : Fin 2), ())
      let b₁' ← ProbOracleComp.query ((1 : Fin 2), ())
      pure (decide (b₁ = b₁' ∧ b₀ = b₁))
    ((SSP.parFinLazy (fun _ : Fin 2 => coinMachine)).run prog).eval true = (2 : ENNReal)⁻¹ ∧
      ((SSP.parFin (fun _ : Fin 2 => coinMachine)).run prog).eval true = (2 : ENNReal)⁻¹ := by
  intro prog
  have hE : ((SSP.parFin (fun _ : Fin 2 => coinMachine)).run prog).eval true =
      (2 : ENNReal)⁻¹ := by
    simp only [Machine.run, Machine.link, SSP.parFin, coinMachine, prog,
      OracleComp.pi_succ, OracleComp.pi_zero, Machine.runFrom_bind, Machine.runFrom_query,
      Machine.runFrom_pure, Machine.closeProgram_bind, Machine.closeProgram_sample,
      Machine.closeProgram_map, Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, ProbComp.eval_unifFin, pure_bind, map_bind, Functor.map_map,
      bind_map_left, StateT.run, Fin.cons_zero, PMF.bind_bind, PMF.pure_bind, PMF.pure_map,
      show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
    simp only [PMF.bind_apply, Probability.PMF.uniformOfFintype_apply, Fintype.card_fin,
      tsum_fintype, Fin.sum_univ_two, Fin.isValue, Fin.val_zero, Fin.val_one, PMF.pure_apply,
      Nat.one_ne_zero, decide_false, decide_true]
    rw [← mul_add]
    simp [ENNReal.inv_two_add_inv_two]
  refine ⟨?_, hE⟩
  rw [SSP.run_parFinLazy_eq_parFin]
  exact hE

end CslibFrontierTests.Crypto.UCJointState
