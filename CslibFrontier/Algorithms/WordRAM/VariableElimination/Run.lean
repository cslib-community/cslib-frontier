/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Instance
public import CslibFrontier.Algorithms.WordRAM.VariableElimination.ElimLoop
public import CslibFrontier.Algorithms.WordRAM.VariableElimination.FinalProd
public import CslibFrontier.Algorithms.WordRAM.VariableElimination.InitFactors
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

/-!
# Top-Level `runProg` Compilation and Realization

Combines `initFactors`, `elimOrderLoop`, and `finalResultProd` into the complete exact-basis
`Memory.Prog` `runProg` with end-to-end word-width, frontier, and `stepBound` guarantees.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.runProg`: top-level bucket-elimination program.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

private theorem holdsIn_stateInit (words : List ℕ) :
    HoldsIn 1 words (Memory.State.init words) := by
  refine ⟨by simp [Memory.State.init]; omega, fun i => ?_⟩
  have h := Data.init_realizes_append (r := 0) [] words [] i
  simpa [Memory.State.init] using h

private theorem capFactor_le_maxEntry {inst : ElimInstance} {f : FactorTable ℕ ℕ}
    (hf : f ∈ inst.factors) :
    capFactor f ≤ max 1 inst.maxEntry := by
  unfold capFactor ElimInstance.maxEntry
  refine max_le (le_max_left 1 _) (le_trans ?_ (le_max_right 1 _))
  exact List.mem_le_foldl_max (List.mem_map.mpr ⟨f, hf, rfl⟩)

private theorem initState_stateCap_le (inst : ElimInstance) :
    stateCap inst.initState ≤ (max 1 inst.maxEntry) ^ inst.factors.length := by
  unfold stateCap ElimInstance.initState ElimState.ofFactors
  dsimp only
  simp only [max_self, Nat.one_mul]
  simpa [List.length_map] using
    List.prod_le_pow_length (inst.factors.map capFactor) (max 1 inst.maxEntry) fun _ hn => by
      rcases List.mem_map.mp hn with ⟨f, hf, rfl⟩
      exact capFactor_le_maxEntry hf

private theorem stateCap_eliminateOrder_le (d : ℕ) :
    ∀ (ord : List ℕ) (es : ElimState ℕ ℕ),
      stateCap (eliminateOrder d ord es) ≤ (max 1 d) ^ ord.length * stateCap es
  | [], es => by simp [eliminateOrder]
  | x :: xs, es => by
      simp only [eliminateOrder, List.length_cons, Nat.pow_succ]
      calc stateCap (eliminateOrder d xs (elimVar d x es))
          ≤ (max 1 d) ^ xs.length * stateCap (elimVar d x es) :=
            stateCap_eliminateOrder_le d xs (elimVar d x es)
        _ ≤ (max 1 d) ^ xs.length * (max 1 d * stateCap es) :=
            Nat.mul_le_mul_left _ (stateCap_elimVar_le d x es)
        _ = (max 1 d) ^ xs.length * max 1 d * stateCap es := by ring

/-- Top-level Word-RAM memory program executing bucket elimination on `ElimInstance`. -/
def runProg (_ : Unit) : Memory.Prog ℕ :=
  Memory.read 1 >>= fun dom =>
  Memory.read 2 >>= fun declLen =>
  Memory.read 3 >>= fun ordLen =>
  Memory.read 4 >>= fun facLen =>
  initFactors (5 + declLen + ordLen, facLen) >>= fun livePtr =>
  elimOrderLoop ⟨dom, 5 + declLen, ordLen, 1, livePtr, facLen, 5, declLen⟩ >>= fun finalSt =>
  finalResultProd ⟨finalSt.livePtr, finalSt.liveLen, finalSt.scalar⟩

private theorem decode_init_layout (inst : ElimInstance) :
    let s₀ := Memory.State.init inst.encode
    5 ≤ s₀.frontier ∧
      s₀.mem 1 = inst.domain ∧
      s₀.mem 2 = inst.declared.length ∧
      s₀.mem 3 = inst.order.length ∧
      s₀.mem 4 = inst.factors.length ∧
      HoldsIn 5 inst.declared s₀ ∧
      HoldsIn (5 + inst.declared.length) inst.order s₀ ∧
      HoldsIn (5 + inst.declared.length + inst.order.length)
        (inst.factors.flatMap encodeFactor) s₀ := by
  dsimp only
  have hall : HoldsIn 1 inst.encode (Memory.State.init inst.encode) :=
    holdsIn_stateInit inst.encode
  have henc : inst.encode = inst.domain :: inst.declared.length :: inst.order.length ::
      inst.factors.length ::
      (inst.declared ++ (inst.order ++ inst.factors.flatMap encodeFactor)) := by
    simp [ElimInstance.encode, List.append_assoc]
  nth_rw 1 [henc] at hall
  obtain ⟨_, hm1, hr1⟩ := holdsIn_cons_shift hall
  obtain ⟨_, hm2, hr2⟩ := holdsIn_cons_shift hr1
  obtain ⟨_, hm3, hr3⟩ := holdsIn_cons_shift hr2
  obtain ⟨h4_lt, hm4, hr4⟩ := holdsIn_cons_shift hr3
  have h5 : 1 + 1 + 1 + 1 + 1 = 5 := rfl
  rw [h5] at hr4
  obtain ⟨hdecl, hr5⟩ := holdsIn_append_split hr4
  obtain ⟨hord, hfac⟩ := holdsIn_append_split hr5
  exact ⟨by omega, hm1, hm2, hm3, hm4, hdecl, hord, hfac⟩

theorem runProg_spec {w : ℕ} (inst : ElimInstance)
    (hin : InputFits w inst.encode) (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (runProg ())) ∧
      (Memory.spec 0).clientResult s₀ (runProg ()) = inst.result ∧
      memoryCost (runProg ()) s₀ ≤ inst.stepBound := by
  dsimp only
  let s₀ := Memory.State.init inst.encode
  have hf_init : Fits w (inst.encode.length + 1) :=
    hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  have hwf₀ : Memory.WellFormed w s₀ := Memory.wellFormed_init hin hf_init
  obtain ⟨hs0_5, hm1, hm2, hm3, hm4, hdecl₀, hord₀, hfac₀⟩ := decode_init_layout inst
  change 5 ≤ s₀.frontier at hs0_5
  let d := inst.domain
  let R := inst.declared.length
  let T := inst.order.length
  let M := inst.factors.length
  let W := maxJointScopeLen d inst.order inst.initState
  let SW := max (maxScopeLen inst.factors) W
  let B := (max 1 d) ^ T * (max 1 inst.maxEntry) ^ M
  have h1 : Fits w 1 := hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  have hB : Fits w B := hw.of_le (by unfold ElimInstance.wordBound; dsimp only [B, d, T, M]; omega)
  have hpowSW : Fits w ((max 1 d) ^ SW) :=
    hw.of_le (by unfold ElimInstance.wordBound; dsimp only [d, W, SW]; omega)
  have hs0_fr : s₀.frontier = inst.encode.length + 1 := rfl
  have hfit_initF : Fits w (s₀.frontier + 4 * M) := hw.of_le (by
    rw [hs0_fr]; unfold ElimInstance.wordBound; dsimp only [M]; omega)
  have hif_spec := initFactors_spec (w := w) (rawPtr := 5 + R + T) (facLen := M)
    hwf₀ rfl hfac₀ hfit_initF
  dsimp only at hif_spec
  generalize hs₁ : (Memory.spec 0).clientState s₀ (initFactors (5 + R + T, M)) = s₁ at hif_spec
  generalize hlivePtr :
    (Memory.spec 0).clientResult s₀ (initFactors (5 + R + T, M)) = livePtr at hif_spec
  obtain ⟨hif_val, hif_fr, hif_pres, _, hif_holds, hif_cost⟩ := hif_spec
  have hwf₁ : Memory.WellFormed w s₁ :=
    by rw [← hs₁]; exact wellFormed_clientState hwf₀ hif_val
  have hdecl₁ : HoldsIn 5 inst.declared s₁ := hdecl₀.mono_frontier hif_pres
  have hord₁ : HoldsIn (5 + R) inst.order s₁ := hord₀.mono_frontier hif_pres
  have hes₁ : HoldsElimState ⟨1, livePtr, M, 5, R⟩ inst.initState s₁ :=
    ⟨by rw [hif_fr, hs0_fr]; omega, rfl, rfl, rfl, hif_holds, hdecl₁⟩
  have hSW₀ : ∀ f ∈ inst.initState.live, f.scope.length ≤ SW :=
    fun f hf => (each_mem_le_maxScopeLen f hf).trans (le_max_left _ _)
  have hW₀ : ∀ st ∈ traceOrder d inst.order inst.initState, st.jointScopeVars ≤ W :=
    fun _ hst => mem_traceOrder_joint_le d inst.order inst.initState hst
  have hcap₀ : (max 1 d) ^ T * stateCap inst.initState ≤ B :=
    Nat.mul_le_mul_left _ (initState_stateCap_le inst)
  have hfit_loop : Fits w (s₁.frontier + T * stepMemDelta R M SW d W) := hw.of_le (by
    rw [hif_fr, hs0_fr]
    unfold ElimInstance.wordBound
    dsimp only [d, R, T, M, W, SW, stepMemDelta]
    omega)
  let eoArgs : ElimOrderArgs := ⟨d, 5 + R, T, 1, livePtr, M, 5, R⟩
  have heo_spec := elimOrderLoop_spec (w := w) (args := eoArgs) (R := R) (M := M)
    hwf₁ hord₁ rfl hes₁ le_rfl le_rfl hSW₀ hW₀ (le_max_right _ _) hcap₀ hB h1 hpowSW hfit_loop
  dsimp only at heo_spec
  generalize hs₂ : (Memory.spec 0).clientState s₁ (elimOrderLoop eoArgs) = s₂ at heo_spec
  generalize hfinalSt :
    (Memory.spec 0).clientResult s₁ (elimOrderLoop eoArgs) = finalSt at heo_spec
  obtain ⟨heo_val, _, _, heo_es, heo_cost⟩ := heo_spec
  dsimp only [eoArgs] at heo_es heo_cost
  let esFinal := eliminateOrder d inst.order inst.initState
  have hcap_final : stateCap esFinal ≤ B :=
    (stateCap_eliminateOrder_le d inst.order inst.initState).trans hcap₀
  obtain ⟨_, hsc_f, hliveLen_f, _, hlive_f, _⟩ := heo_es
  dsimp only at hsc_f hliveLen_f hlive_f
  let fpArgs : FinalProdArgs := ⟨finalSt.livePtr, finalSt.liveLen, finalSt.scalar⟩
  obtain ⟨hfp_val, _, hfp_res, hfp_cost⟩ :=
    finalResultProd_spec (w := w) (args := fpArgs) hB hcap_final hsc_f hliveLen_f hlive_f
  dsimp only [fpArgs] at hfp_cost
  have hliveLen_le_M : finalSt.liveLen ≤ M := by
    rw [hliveLen_f]
    exact liveLength_eliminateOrder_le d inst.order inst.initState
  have hr_st (addr : ℕ) : (Memory.spec 0).clientState s₀ (Memory.read addr) = s₀ := rfl
  have hr_res (addr : ℕ) : (Memory.spec 0).clientResult s₀ (Memory.read addr) = s₀.mem addr := rfl
  unfold runProg
  rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res, hm1,
    StateTransitionSpec.clientResult_bind, hr_st, hr_res, hm2,
    StateTransitionSpec.clientResult_bind, hr_st, hr_res, hm3,
    StateTransitionSpec.clientResult_bind, hr_st, hr_res, hm4]
  change (Memory.spec w).ValidHistory s₀ _ ∧
    (Memory.spec 0).clientResult s₀
      (initFactors (5 + R + T, M) >>= fun lp =>
        elimOrderLoop ⟨d, 5 + R, T, 1, lp, M, 5, R⟩ >>= fun fs =>
          finalResultProd ⟨fs.livePtr, fs.liveLen, fs.scalar⟩) = inst.result ∧ _
  rw [StateTransitionSpec.clientResult_bind, hs₁, hlivePtr,
    StateTransitionSpec.clientResult_bind, hs₂, hfinalSt, hfp_res]
  refine ⟨?_, rfl, ?_⟩
  · refine validHistory_read_bind (by omega) ?_
    rw [hm1]
    refine validHistory_read_bind (by omega) ?_
    rw [hm2]
    refine validHistory_read_bind (by omega) ?_
    rw [hm3]
    refine validHistory_read_bind (by omega) ?_
    rw [hm4]
    refine validHistory_bind_step hif_val ?_
    rw [hs₁, hlivePtr]
    refine validHistory_bind_step heo_val ?_
    rw [hs₂, hfinalSt]
    exact hfp_val
  · rw [memoryCost_bind', memoryCost_read, hr_st, hr_res, hm1,
      memoryCost_bind', memoryCost_read, hr_st, hr_res, hm2,
      memoryCost_bind', memoryCost_read, hr_st, hr_res, hm3,
      memoryCost_bind', memoryCost_read, hr_st, hr_res, hm4,
      memoryCost_bind', hs₁, hlivePtr,
      memoryCost_bind', hs₂, hfinalSt]
    unfold ElimInstance.stepBound
    dsimp only [d, R, T, M, W, SW, stepFixedCost, stepBucketUnitCost]
      at hif_cost heo_cost hfp_cost hliveLen_le_M ⊢
    omega

theorem runProg_realizes :
    Realizes .exact runProg WordEncoding.encode WordEncoding.encode
      (fun w _ s =>
        ∃ inst : ElimInstance,
          s = Memory.State.init inst.encode ∧
          InputFits w inst.encode ∧
          Fits w inst.wordBound)
      (fun _ _ => 0) := by
  unfold runProg
  realize [initFactors_realizes, elimOrderLoop_realizes, finalResultProd_realizes]
  all_goals
    obtain ⟨inst, hs_eq, hin, hw⟩ := h
    subst hs_eq
    obtain ⟨hs0_5, hm1, hm2, hm3, hm4, hdecl₀, hord₀, hfac₀⟩ := decode_init_layout inst
    have hord_le : 5 + inst.declared.length + inst.order.length ≤ inst.encode.length + 1 :=
      hord₀.1
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · simp only [hm2, hm3, hm4]
    refine ⟨inst.factors,
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega), ?_, rfl, hfac₀⟩
    exact hw.of_le (by
      change inst.encode.length + 1 + 4 * inst.factors.length ≤ inst.wordBound
      unfold ElimInstance.wordBound; dsimp only; omega)
  · rw [hm2]
    exact hmem.frontier_fits.of_le (by have := hdecl₀.1; omega)
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · simp only [hm1, hm2, hm3, hm4]
    let s₀ := Memory.State.init inst.encode
    let d := inst.domain
    let R := inst.declared.length
    let T := inst.order.length
    let M := inst.factors.length
    let W := maxJointScopeLen d inst.order inst.initState
    let SW := max (maxScopeLen inst.factors) W
    let B := (max 1 d) ^ T * (max 1 inst.maxEntry) ^ M
    have hfit_initF : Fits w (s₀.frontier + 4 * M) := hw.of_le (by
      change inst.encode.length + 1 + 4 * M ≤ inst.wordBound
      unfold ElimInstance.wordBound; dsimp only [M]; omega)
    have hif_spec := initFactors_spec (w := w) (rawPtr := 5 + R + T) (facLen := M)
      hmem rfl hfac₀ hfit_initF
    dsimp only at hif_spec
    obtain ⟨_, hif_fr, hif_pres, _, hif_holds, _⟩ := hif_spec
    exact ⟨inst.order, inst.initState, R, M, SW, W, B,
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega),
      rfl,
      hord₀.mono_frontier hif_pres,
      ⟨by rw [hif_fr]; change 0 < inst.encode.length + 1 + 4 * M; omega,
        rfl, rfl, rfl, hif_holds, hdecl₀.mono_frontier hif_pres⟩,
      le_rfl, le_rfl,
      fun f hf => (each_mem_le_maxScopeLen f hf).trans (le_max_left _ _),
      fun _ hst => mem_traceOrder_joint_le d inst.order inst.initState hst,
      le_max_right _ _,
      Nat.mul_le_mul_left _ (initState_stateCap_le inst),
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only [B, d, T, M]; omega),
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only [d, W, SW]; omega),
      hw.of_le (by
        rw [hif_fr]
        change inst.encode.length + 1 + 4 * M + T * stepMemDelta R M SW d W ≤ inst.wordBound
        unfold ElimInstance.wordBound
        dsimp only [d, R, T, M, W, SW, stepMemDelta]
        omega)⟩
  · simp only [hm1, hm2, hm3, hm4]
    let s₀ := Memory.State.init inst.encode
    let d := inst.domain
    let R := inst.declared.length
    let T := inst.order.length
    let M := inst.factors.length
    let W := maxJointScopeLen d inst.order inst.initState
    let SW := max (maxScopeLen inst.factors) W
    let B := (max 1 d) ^ T * (max 1 inst.maxEntry) ^ M
    have hfit_initF : Fits w (s₀.frontier + 4 * M) := hw.of_le (by
      change inst.encode.length + 1 + 4 * M ≤ inst.wordBound
      unfold ElimInstance.wordBound; dsimp only [M]; omega)
    have hif_spec := initFactors_spec (w := w) (rawPtr := 5 + R + T) (facLen := M)
      hmem rfl hfac₀ hfit_initF
    dsimp only at hif_spec
    generalize hs₁ : (Memory.spec 0).clientState s₀ (initFactors (5 + R + T, M)) = s₁ at hif_spec
    generalize hlivePtr :
      (Memory.spec 0).clientResult s₀ (initFactors (5 + R + T, M)) = livePtr at hif_spec
    obtain ⟨hif_val, hif_fr, hif_pres, _, hif_holds, _⟩ := hif_spec
    have hwf₁ : Memory.WellFormed w s₁ :=
      by rw [← hs₁]; exact wellFormed_clientState hmem hif_val
    have hes₁ : HoldsElimState ⟨1, livePtr, M, 5, R⟩ inst.initState s₁ :=
      ⟨by rw [hif_fr]; change 0 < inst.encode.length + 1 + 4 * M; omega,
        rfl, rfl, rfl, hif_holds, hdecl₀.mono_frontier hif_pres⟩
    have hcap₀ : (max 1 d) ^ T * stateCap inst.initState ≤ B :=
      Nat.mul_le_mul_left _ (initState_stateCap_le inst)
    let eoArgs : ElimOrderArgs := ⟨d, 5 + R, T, 1, livePtr, M, 5, R⟩
    have heo_spec := elimOrderLoop_spec (w := w) (args := eoArgs) (R := R) (M := M) (SW := SW)
      hwf₁ (hord₀.mono_frontier hif_pres) rfl hes₁ le_rfl le_rfl
      (fun f hf => (each_mem_le_maxScopeLen f hf).trans (le_max_left _ _))
      (fun _ hst => mem_traceOrder_joint_le d inst.order inst.initState hst)
      (le_max_right _ _) hcap₀
      (hw.of_le (by unfold ElimInstance.wordBound; dsimp only [B, d, T, M]; omega))
      (hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega))
      (hw.of_le (by unfold ElimInstance.wordBound; dsimp only [eoArgs, d, W, SW]; omega))
      (hw.of_le (by
        rw [hif_fr]
        change inst.encode.length + 1 + 4 * M + T * stepMemDelta R M SW d W ≤ inst.wordBound
        unfold ElimInstance.wordBound
        dsimp only [d, R, T, M, W, SW, stepMemDelta]
        omega))
    dsimp only at heo_spec
    obtain ⟨_, _, _, heo_es, _⟩ := heo_spec
    obtain ⟨_, hsc_f, hliveLen_f, _, hlive_f, _⟩ := heo_es
    dsimp only [eoArgs] at hsc_f hliveLen_f hlive_f
    let esFinal := eliminateOrder d inst.order inst.initState
    have hcap_final : esFinal.scalar * (esFinal.live.map capFactor).prod ≤ B :=
      (Nat.mul_le_mul_right _ (le_max_right 1 esFinal.scalar)).trans
        ((stateCap_eliminateOrder_le d inst.order inst.initState).trans hcap₀)
    exact ⟨esFinal.live, B,
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega),
      hliveLen_f.symm, hlive_f,
      by rw [hsc_f]; exact hcap_final,
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only [B, d, T, M]; omega)⟩

end Cslib.Algorithms.WordRAM.VariableElimination
