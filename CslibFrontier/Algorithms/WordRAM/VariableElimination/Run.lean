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
        _ = (max 1 d) ^ xs.length * max 1 d * stateCap es := (Nat.mul_assoc ..).symm

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
    holdsIn_init inst.encode
  have henc : inst.encode = inst.domain :: inst.declared.length :: inst.order.length ::
      inst.factors.length ::
      (inst.declared ++ (inst.order ++ inst.factors.flatMap encodeFactor)) := by
    simp [ElimInstance.encode, List.append_assoc]
  nth_rw 1 [henc] at hall
  obtain ⟨_, hm1, hr1⟩ := hall.cons
  obtain ⟨_, hm2, hr2⟩ := hr1.cons
  obtain ⟨_, hm3, hr3⟩ := hr2.cons
  obtain ⟨h4_lt, hm4, hr4⟩ := hr3.cons
  change HoldsIn 5 _ _ at hr4
  obtain ⟨hdecl, hr5⟩ := HoldsIn.append_iff.mp hr4
  obtain ⟨hord, hfac⟩ := HoldsIn.append_iff.mp hr5
  exact ⟨by omega, hm1, hm2, hm3, hm4, hdecl, hord, hfac⟩

/-- Word-size and capacity bounds on `inst` that feed `elimOrderLoop`'s precondition. -/
private theorem runProg_bounds {w : ℕ} (inst : ElimInstance) (hw : Fits w inst.wordBound) :
    let d := inst.domain
    let W := maxJointScopeLen d inst.order inst.initState
    let SW := max (maxScopeLen inst.factors) W
    let B := (max 1 d) ^ inst.order.length * (max 1 inst.maxEntry) ^ inst.factors.length
    Fits w 1 ∧ Fits w B ∧ Fits w ((max 1 d) ^ SW) ∧
      (∀ f ∈ inst.initState.live, f.scope.length ≤ SW) ∧
      (∀ st ∈ traceOrder d inst.order inst.initState, st.jointScopeVars ≤ W) ∧
      (max 1 d) ^ inst.order.length * stateCap inst.initState ≤ B :=
  ⟨hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega),
    hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega),
    hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega),
    fun f hf => (each_mem_le_maxScopeLen f hf).trans (le_max_left _ _),
    fun _ hst => mem_traceOrder_joint_le _ _ _ hst,
    Nat.mul_le_mul_left _ (initState_stateCap_le inst)⟩

/-- The `initFactors` stage of `runProg`, ending in `elimOrderLoop`'s memory precondition. -/
private theorem runProg_init {w : ℕ} (inst : ElimInstance)
    (hwf : Memory.WellFormed w (Memory.State.init inst.encode)) (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    let d := inst.domain
    let R := inst.declared.length
    let T := inst.order.length
    let M := inst.factors.length
    let W := maxJointScopeLen d inst.order inst.initState
    let p := initFactors (5 + R + T, M)
    let s₁ := (Memory.spec 0).clientState s₀ p
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ p) ∧
      memoryCost p s₀ ≤ 1 + 6 * M ∧ Memory.WellFormed w s₁ ∧ HoldsIn (5 + R) inst.order s₁ ∧
      HoldsElimState ⟨1, (Memory.spec 0).clientResult s₀ p, M, 5, R⟩ inst.initState s₁ ∧
      Fits w (s₁.frontier + T * stepMemDelta R M (max (maxScopeLen inst.factors) W) d W) := by
  obtain ⟨-, -, -, -, -, hdecl, hord, hfac⟩ := decode_init_layout inst
  have hfr : (Memory.State.init inst.encode).frontier = inst.encode.length + 1 := rfl
  obtain ⟨hv, hfr₁, hpres, -, hholds, hcost⟩ := initFactors_spec hwf rfl hfac
    (hw.of_le (by rw [hfr]; unfold ElimInstance.wordBound; dsimp only; omega))
  refine ⟨hv, hcost, wellFormed_clientState hwf hv, hord.mono_frontier hpres,
    ⟨by rw [hfr₁]; omega, rfl, rfl, rfl, hholds, hdecl.mono_frontier hpres⟩, hw.of_le ?_⟩
  rw [hfr₁, hfr]
  unfold ElimInstance.wordBound
  dsimp only [stepMemDelta]
  omega

/-- The `elimOrderLoop` stage of `runProg`, ending in `finalResultProd`'s precondition. -/
private theorem runProg_loop {w : ℕ} (inst : ElimInstance)
    (hwf : Memory.WellFormed w (Memory.State.init inst.encode)) (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    let d := inst.domain
    let R := inst.declared.length
    let T := inst.order.length
    let M := inst.factors.length
    let W := maxJointScopeLen d inst.order inst.initState
    let SW := max (maxScopeLen inst.factors) W
    let p₁ := initFactors (5 + R + T, M)
    let s₁ := (Memory.spec 0).clientState s₀ p₁
    let p₂ := elimOrderLoop ⟨d, 5 + R, T, 1, (Memory.spec 0).clientResult s₀ p₁, M, 5, R⟩
    let r := (Memory.spec 0).clientResult s₁ p₂
    let es := eliminateOrder d inst.order inst.initState
    (Memory.spec w).ValidHistory s₁ ((Memory.spec w).clientHistory s₁ p₂) ∧
      memoryCost p₂ s₁ ≤ T * (1 + stepFixedCost R M SW d W) + (M + T) * stepBucketUnitCost SW d W ∧
      r.scalar = es.scalar ∧ r.liveLen = es.live.length ∧
      HoldsFactorList r.livePtr es.live ((Memory.spec 0).clientState s₁ p₂) ∧
      stateCap es ≤ (max 1 d) ^ T * (max 1 inst.maxEntry) ^ M := by
  obtain ⟨h1, hB, hpow, hSW, hW, hcap⟩ := runProg_bounds inst hw
  obtain ⟨-, -, hwf₁, hord₁, hes₁, hfit⟩ := runProg_init inst hwf hw
  obtain ⟨hv, -, -, ⟨-, hsc, hlen, -, hlive, -⟩, hcost⟩ := elimOrderLoop_spec
    (args := ⟨_, _, _, 1, _, _, 5, _⟩) (R := inst.declared.length) (M := inst.factors.length)
    hwf₁ hord₁ rfl hes₁ le_rfl le_rfl hSW hW (le_max_right _ _) hcap hB h1 hpow hfit
  exact ⟨hv, hcost, hsc, hlen, hlive,
    (stateCap_eliminateOrder_le inst.domain inst.order inst.initState).trans hcap⟩

/-- The `finalResultProd` stage of `runProg`. -/
private theorem runProg_final {w : ℕ} (inst : ElimInstance)
    (hwf : Memory.WellFormed w (Memory.State.init inst.encode)) (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    let R := inst.declared.length
    let T := inst.order.length
    let M := inst.factors.length
    let p₁ := initFactors (5 + R + T, M)
    let s₁ := (Memory.spec 0).clientState s₀ p₁
    let p₂ := elimOrderLoop ⟨inst.domain, 5 + R, T, 1, (Memory.spec 0).clientResult s₀ p₁, M, 5, R⟩
    let r := (Memory.spec 0).clientResult s₁ p₂
    let s₂ := (Memory.spec 0).clientState s₁ p₂
    let p₃ := finalResultProd ⟨r.livePtr, r.liveLen, r.scalar⟩
    (Memory.spec w).ValidHistory s₂ ((Memory.spec w).clientHistory s₂ p₃) ∧
      (Memory.spec 0).clientResult s₂ p₃ = inst.result ∧ memoryCost p₃ s₂ ≤ 3 * M := by
  intro s₀ R T M p₁ s₁ p₂ r s₂ p₃
  obtain ⟨-, hB, -⟩ := runProg_bounds inst hw
  obtain ⟨-, -, hsc, hlen, hlive, hcap⟩ := runProg_loop inst hwf hw
  obtain ⟨hv, -, hres, hcost⟩ :=
    finalResultProd_spec (args := ⟨r.livePtr, r.liveLen, r.scalar⟩) hB hcap hsc hlen hlive
  exact ⟨hv, hres, hcost.trans
    (Nat.mul_le_mul_left 3 (hlen.trans_le (liveLength_eliminateOrder_le _ _ _)))⟩

theorem runProg_spec {w : ℕ} (inst : ElimInstance)
    (hin : InputFits w inst.encode) (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (runProg ())) ∧
      (Memory.spec 0).clientResult s₀ (runProg ()) = inst.result ∧
      memoryCost (runProg ()) s₀ ≤ inst.stepBound := by
  have hwf : Memory.WellFormed w (Memory.State.init inst.encode) :=
    Memory.wellFormed_init hin (hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega))
  obtain ⟨h5, hm1, hm2, hm3, hm4, -, -, -⟩ := decode_init_layout inst
  obtain ⟨hv₁, hcost₁, -⟩ := runProg_init inst hwf hw
  obtain ⟨hv₂, hcost₂, -⟩ := runProg_loop inst hwf hw
  obtain ⟨hv₃, hres, hcost₃⟩ := runProg_final inst hwf hw
  dsimp only
  unfold runProg
  rw [clientResult_bind_read, hm1, clientResult_bind_read, hm2, clientResult_bind_read, hm3,
    clientResult_bind_read, hm4, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientResult_bind, hres]
  refine ⟨?_, rfl, ?_⟩
  · refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
      (validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)))
    rw [hm1, hm2, hm3, hm4]
    exact validHistory_bind_step hv₁ (validHistory_bind_step hv₂ hv₃)
  · rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read, hm1,
      memoryCost_bind', memoryCost_read, clientState_read, clientResult_read, hm2,
      memoryCost_bind', memoryCost_read, clientState_read, clientResult_read, hm3,
      memoryCost_bind', memoryCost_read, clientState_read, clientResult_read, hm4,
      memoryCost_bind', memoryCost_bind']
    unfold ElimInstance.stepBound
    dsimp only [stepFixedCost, stepBucketUnitCost] at hcost₂ ⊢
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
    obtain ⟨inst, rfl, hin, hw⟩ := h
    obtain ⟨-, hm1, hm2, hm3, hm4, -, hord₀, hfac₀⟩ := decode_init_layout inst
    have hord_le : 5 + inst.declared.length + inst.order.length ≤ inst.encode.length + 1 :=
      hord₀.1
  -- Word-size side conditions on literals and header fields.
  any_goals exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · simp only [hm2, hm3, hm4]
    refine ⟨inst.factors,
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega), ?_, rfl, hfac₀⟩
    exact hw.of_le (by
      change inst.encode.length + 1 + 4 * inst.factors.length ≤ inst.wordBound
      unfold ElimInstance.wordBound; dsimp only; omega)
  · simp only [hm1, hm2, hm3, hm4]
    obtain ⟨h1, hB, hpow, hSW, hW, hcap⟩ := runProg_bounds inst hw
    obtain ⟨-, -, -, hord₁, hes₁, hfit⟩ := runProg_init inst hmem hw
    exact ⟨inst.order, inst.initState, inst.declared.length, inst.factors.length, _, _, _, h1,
      rfl, hord₁, hes₁, le_rfl, le_rfl, hSW, hW, le_max_right _ _, hcap, hB, hpow, hfit⟩
  · simp only [hm1, hm2, hm3, hm4]
    obtain ⟨-, hB, -⟩ := runProg_bounds inst hw
    obtain ⟨-, -, hsc, hlen, hlive, hcap⟩ := runProg_loop inst hmem hw
    exact ⟨_, _, hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega), hlen.symm, hlive,
      by rw [hsc]; exact (Nat.mul_le_mul_right _ (le_max_right 1 _)).trans hcap, hB⟩

end Cslib.Algorithms.WordRAM.VariableElimination
