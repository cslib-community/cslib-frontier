/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.BuildEntries
public import CslibFrontier.Algorithms.WordRAM.VariableElimination.OutScope
public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Partition
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Ring

/-!
# Single-Variable Elimination Step (`elimVarProg`)

Composes `partitionLive`, `filterNe`, `buildOutScope`, `buildOutEntries`, `writeDesc`, and
`copyWords` to implement one exact-basis step of `eliminateVar`.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.HoldsElimState`: heap invariant for `ElimState`.
* `Cslib.Algorithms.WordRAM.VariableElimination.elimVarProg`: single-step elimination program.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- Word-RAM representation `(remPtr, remLen, livePtr, liveLen)` of `ElimState`. -/
structure ElimStepState where
  /-- Field `scalar` of `ElimStepState`. -/
  scalar : ℕ
  /-- Field `livePtr` of `ElimStepState`. -/
  livePtr : ℕ
  /-- Field `liveLen` of `ElimStepState`. -/
  liveLen : ℕ
  /-- Field `remPtr` of `ElimStepState`. -/
  remPtr : ℕ
  /-- Field `remLen` of `ElimStepState`. -/
  remLen : ℕ

/-- Product equivalence encoding `ElimStepState` as words. -/
@[expose] def ElimStepState.equiv : ElimStepState ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((s.scalar, s.livePtr), s.liveLen), s.remPtr), s.remLen)
  invFun := fun ((((scalar, livePtr), liveLen), remPtr), remLen) =>
    ⟨scalar, livePtr, liveLen, remPtr, remLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ElimStepState := .ofEquiv ElimStepState.equiv

/-- Arguments for running one bucket-elimination step on variable `x`. -/
structure ElimVarArgs where
  /-- Field `dom` of `ElimVarArgs`. -/
  dom : ℕ
  /-- Field `x` of `ElimVarArgs`. -/
  x : ℕ
  /-- Field `scalar` of `ElimVarArgs`. -/
  scalar : ℕ
  /-- Field `livePtr` of `ElimVarArgs`. -/
  livePtr : ℕ
  /-- Field `liveLen` of `ElimVarArgs`. -/
  liveLen : ℕ
  /-- Field `remPtr` of `ElimVarArgs`. -/
  remPtr : ℕ
  /-- Field `remLen` of `ElimVarArgs`. -/
  remLen : ℕ

/-- Product equivalence encoding `ElimVarArgs` as words. -/
@[expose] def ElimVarArgs.equiv :
    ElimVarArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((((s.dom, s.x), s.scalar), s.livePtr), s.liveLen), s.remPtr), s.remLen)
  invFun := fun ((((((dom, x), scalar), livePtr), liveLen), remPtr), remLen) =>
    ⟨dom, x, scalar, livePtr, liveLen, remPtr, remLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ElimVarArgs := .ofEquiv ElimVarArgs.equiv

/-- Memory invariant matching `ElimStepState` to a pure `ElimState ℕ ℕ`. -/
@[expose] def HoldsElimState (st : ElimStepState) (es : ElimState ℕ ℕ) (s : Memory.State) : Prop :=
  0 < s.frontier ∧
  st.scalar = es.scalar ∧
  st.liveLen = es.live.length ∧
  st.remLen = es.remaining.length ∧
  HoldsFactorList st.livePtr es.live s ∧
  HoldsIn st.remPtr es.remaining s

/-- Execute a single `eliminateVar` bucket contraction on the Word-RAM heap. -/
def elimVarProg (args : ElimVarArgs) : Memory.Prog ElimStepState :=
  memScan ⟨args.x, args.remPtr, args.remLen⟩ >>= fun inRem =>
  if inRem = 0 then
    pure ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩
  else
    filterNe ⟨args.x, args.remPtr, args.remLen⟩ >>= fun remPair =>
    partitionLive ⟨args.x, args.livePtr, args.liveLen⟩ >>= fun part =>
    if part.bucketLen = 0 then
      pure ⟨args.scalar * args.dom, args.livePtr, args.liveLen, remPair.1, remPair.2⟩
    else
      buildOutScope ⟨args.x, part.bucketPtr, part.bucketLen⟩ >>= fun outPair =>
      buildOutEntries
        ⟨args.dom, args.x, outPair.1, outPair.2, part.bucketPtr, part.bucketLen⟩ >>=
        fun entPair =>
      writeDesc ⟨part.newLiveBuf, outPair.1, outPair.2, entPair.1, entPair.2⟩ >>= fun _ =>
      pure ⟨args.scalar, part.newLiveBuf, 1 + part.restLen, remPair.1, remPair.2⟩

/-- Heap frontier growth bound for one `eliminateVar` step. -/
abbrev stepMemDelta (R M SW d W : ℕ) : ℕ :=
  R + 4 + 8 * M + 2 * (M * SW) + (max 1 d) ^ W

/-- Fixed instruction/oracle cost bound for one `eliminateVar` step. -/
abbrev stepFixedCost (R M SW d W : ℕ) : ℕ :=
  12 + 3 * R + M * (8 + SW) + W + 4 * (max 1 d) ^ W

/-- Per-bucket-factor amortized cost bound for one `eliminateVar` step. -/
abbrev stepBucketUnitCost (SW d W : ℕ) : ℕ :=
  3 + SW * (4 + W) + (max 1 d) ^ W * (5 + SW * W)

theorem elimVarProg_spec {w : ℕ} {args : ElimVarArgs} {es : ElimState ℕ ℕ}
    {R M SW W B : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hes : HoldsElimState ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩ es s)
    (hM : es.live.length ≤ M) (hR : es.remaining.length ≤ R)
    (hSW : ∀ f ∈ es.live, f.scope.length ≤ SW)
    (hW : (stepStats args.dom args.x es).jointScopeVars ≤ W) (_hW_SW : W ≤ SW)
    (hcapB : max 1 args.dom * stateCap es ≤ B) (hB : Fits w B)
    (_h1 : Fits w 1) (_hpowSW : Fits w ((max 1 args.dom) ^ SW))
    (hfit_fr : Fits w (s.frontier + stepMemDelta R M SW args.dom W)) :
    let res := (Memory.spec 0).clientResult s (elimVarProg args)
    let s' := (Memory.spec 0).clientState s (elimVarProg args)
    let es' := elimVar args.dom args.x es
    let bk := (stepStats args.dom args.x es).bucketFactors
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (elimVarProg args)) ∧
      PreservesBelow s.frontier s s' ∧
      s'.frontier ≤ s.frontier + stepMemDelta R M SW args.dom W ∧
      HoldsElimState res es' s' ∧
      memoryCost (elimVarProg args) s ≤
        stepFixedCost R M SW args.dom W + bk * stepBucketUnitCost SW args.dom W := by
  dsimp only
  unfold elimVarProg
  obtain ⟨hs0, hsc_eq, hlive_len, hrem_len, hlive_h, hrem_h⟩ := hes
  dsimp only at hsc_eq hlive_len hrem_len hlive_h hrem_h
  have hms_val := memScan_valid (w := w) ⟨args.x, args.remPtr, args.remLen⟩
    (by dsimp only; rw [hrem_len]; exact hrem_h.1)
  have hms_res := memScan_result (args := ⟨args.x, args.remPtr, args.remLen⟩) hrem_h.2
    hrem_len.symm
  have hms_cost := memScan_cost ⟨args.x, args.remPtr, args.remLen⟩ s
  dsimp only at hms_res hms_cost
  rw [validHistory_bind', StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, memoryCost_bind', memScan_state, hms_res]
  by_cases hx : args.x ∈ es.remaining
  swap
  · have hes'_eq : elimVar args.dom args.x es = es := by simp [elimVar, hx]
    have hbk_eq : (stepStats args.dom args.x es).bucketFactors = 0 := by simp [stepStats, hx]
    rw [ite_eq_right hx, ite_eq_left rfl, StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientState_pure, memoryCost_pure, hes'_eq, hbk_eq]
    exact ⟨⟨hms_val, validHistory_pure w s _⟩, PreservesBelow.refl le_rfl, Nat.le_add_right _ _,
      ⟨hs0, hsc_eq, hlive_len, hrem_len, hlive_h, hrem_h⟩, by dsimp only [stepFixedCost]; omega⟩
  have hfn := filterNe_spec (w := w) ⟨args.x, args.remPtr, args.remLen⟩ hwf hrem_h hrem_len.symm
    (hfit_fr.of_le (by dsimp only [stepMemDelta]; omega))
  have hfn_cost := filterNe_cost ⟨args.x, args.remPtr, args.remLen⟩ s
  dsimp only at hfn hfn_cost
  have hwf₁ := wellFormed_clientState hwf hfn.1
  rw [ite_eq_left hx, ite_eq_right Nat.one_ne_zero, validHistory_bind',
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind, memoryCost_bind']
  generalize (Memory.spec 0).clientState s (filterNe ⟨args.x, args.remPtr, args.remLen⟩) =
    s₁ at hfn hwf₁ ⊢
  generalize (Memory.spec 0).clientResult s (filterNe ⟨args.x, args.remPtr, args.remLen⟩) =
    remPair at hfn ⊢
  obtain ⟨hfn_val, hfn_fr, hfn_pres, -, hfn_len, hfn_holds⟩ := hfn
  have hpl := partitionLive_spec (w := w) (args := ⟨args.x, args.livePtr, args.liveLen⟩) hwf₁
    (hlive_h.mono_frontier hfn_pres) hlive_len.symm hSW
    (hfit_fr.of_le (by rw [hfn_fr]; dsimp only [stepMemDelta]; omega))
  dsimp only at hpl
  have hwf₂ := wellFormed_clientState hwf₁ hpl.1
  rw [validHistory_bind', StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, memoryCost_bind']
  generalize (Memory.spec 0).clientState s₁ (partitionLive ⟨args.x, args.livePtr, args.liveLen⟩) =
    s₂ at hpl hwf₂ ⊢
  generalize (Memory.spec 0).clientResult s₁ (partitionLive ⟨args.x, args.livePtr, args.liveLen⟩) =
    part at hpl ⊢
  obtain ⟨hpl_val, hpl_fr, hpl_pres, -, hpl_rBuf, hpl_bLen, hpl_rLen, hpl_bH, -, hpl_rH, hpl_rD,
    hpl_cost⟩ := hpl
  let bucket := es.live.filter fun f => decide (args.x ∈ f.scope)
  let rest := es.live.filter fun f => decide (args.x ∉ f.scope)
  let rem' := es.remaining.filter fun v => decide (v ≠ args.x)
  change part.bucketLen = bucket.length at hpl_bLen
  change part.restLen = rest.length at hpl_rLen
  change HoldsFactorList part.bucketPtr bucket s₂ at hpl_bH
  change HoldsFactorList (part.newLiveBuf + 4) rest s₂ at hpl_rH
  change AllDataBelow s₁.frontier (part.newLiveBuf + 4) rest s₂ at hpl_rD
  have hs2_fr : s₂.frontier = s.frontier + args.remLen + 4 + 8 * args.liveLen := by
    rw [hpl_fr, hfn_fr]
  have hM_mul : args.liveLen * (8 + SW) ≤ M * (8 + SW) := Nat.mul_le_mul_right _ (by omega)
  by_cases hbk0 : bucket.isEmpty = true
  · have hp_bLen0 : part.bucketLen = 0 := by rw [hpl_bLen, List.isEmpty_iff.mp hbk0]; rfl
    have hes'_eq : elimVar args.dom args.x es =
        { scalar := es.scalar * args.dom, live := es.live, remaining := rem' } := by
      unfold elimVar
      rw [ite_eq_left hx]
      dsimp only
      change (if bucket.isEmpty then _ else _) = _
      rw [ite_eq_left hbk0]
      simp only [Nat.cast_id]
      rfl
    have hbk_eq : (stepStats args.dom args.x es).bucketFactors = 0 := by
      unfold stepStats
      rw [ite_eq_left hx]
      dsimp only
      change ElimStepStats.bucketFactors (if bucket.isEmpty then _ else _) = 0
      rw [ite_eq_left hbk0]
    have hpres_all : PreservesBelow s.frontier s s₂ :=
      hfn_pres.trans_frontier hpl_pres
    rw [ite_eq_left hp_bLen0, StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientState_pure, memoryCost_pure, hes'_eq, hbk_eq]
    exact ⟨⟨hms_val, hfn_val, hpl_val, validHistory_pure w s₂ _⟩, hpres_all,
      by rw [hs2_fr]; dsimp only [stepMemDelta]; omega,
      ⟨by rw [hs2_fr]; omega, by dsimp only; rw [hsc_eq], hlive_len, hfn_len,
        hlive_h.mono_frontier hpres_all, hfn_holds.mono_frontier hpl_pres⟩,
      by dsimp only [stepFixedCost]; omega⟩
  have hb_ne : bucket ≠ [] := fun h => hbk0 (List.isEmpty_iff.mpr h)
  have hp_bLen_ne : ¬ (part.bucketLen = 0) := by
    rw [hpl_bLen]; exact (List.length_pos_iff.mpr hb_ne).ne'
  have hes'_eq : elimVar args.dom args.x es =
      { scalar := es.scalar, live := elimBucketTable args.dom args.x bucket :: rest,
        remaining := rem' } := by
    simp [elimVar, hx, hbk0, bucket, rest, rem']
  have hbk_eq : (stepStats args.dom args.x es).bucketFactors = bucket.length := by
    simp [stepStats, hx, hbk0, bucket]
  have hj_le : (bucketJointScope bucket).length ≤ W := by
    simpa [stepStats, hx, hbk0, bucket] using hW
  have hb_SW : ∀ f ∈ bucket, f.scope.length ≤ SW :=
    fun f hf => hSW f (List.mem_filter.mp hf).1
  have hb_le_M : part.bucketLen ≤ M := by
    rw [hpl_bLen]; exact (List.length_filter_le _ _).trans hM
  have hbmul_le : part.bucketLen * SW ≤ M * SW := Nat.mul_le_mul_right SW hb_le_M
  have hbos := buildOutScope_spec (w := w) (args := ⟨args.x, part.bucketPtr, part.bucketLen⟩)
    hwf₂ hpl_bH hpl_bLen.symm hb_SW ((List.length_filter_le _ _).trans hj_le)
    (hfit_fr.of_le (by dsimp only [stepMemDelta]; rw [hs2_fr]; omega))
  dsimp only at hbos
  have hwf₃ := wellFormed_clientState hwf₂ hbos.1
  rw [ite_eq_right hp_bLen_ne, validHistory_bind', StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, memoryCost_bind']
  generalize
    (Memory.spec 0).clientState s₂ (buildOutScope ⟨args.x, part.bucketPtr, part.bucketLen⟩) = s₃
    at hbos hwf₃ ⊢
  generalize
    (Memory.spec 0).clientResult s₂ (buildOutScope ⟨args.x, part.bucketPtr, part.bucketLen⟩) =
      outPair at hbos ⊢
  obtain ⟨hbos_val, hbos_fr, hbos_pres, hbos_lo, hbos_len, hbos_holds, hbos_cost⟩ := hbos
  have hout_succ_le_W : outPair.2 + 1 ≤ W := by
    rw [hbos_len, length_bucketOutScope_add_one hb_ne fun f hf => by
      simpa using (List.mem_filter.mp hf).2]
    exact hj_le
  have hpow_out_le : (max 1 args.dom) ^ outPair.2 ≤ (max 1 args.dom) ^ W :=
    Nat.pow_le_pow_right (le_max_left 1 args.dom) (by omega)
  have hpow_joint_le : (max 1 args.dom) ^ outPair.2 * args.dom ≤ (max 1 args.dom) ^ W :=
    (Nat.mul_le_mul_left _ (le_max_right 1 args.dom)).trans
      ((Nat.pow_succ _ _).symm.le.trans
        (Nat.pow_le_pow_right (le_max_left 1 args.dom) hout_succ_le_W))
  have hboe := buildOutEntries_spec (w := w)
    (args := ⟨args.dom, args.x, outPair.1, outPair.2, part.bucketPtr, part.bucketLen⟩) hwf₃
    (lt_of_lt_of_le hs0 (hfn_pres.2.1.trans (hpl_pres.2.1.trans hbos_pres.2.1)))
    hbos_holds rfl hbos_len.symm (hpl_bH.mono_frontier hbos_pres) hpl_bLen.symm hb_SW
    (hfit_fr.of_le (by dsimp only [stepMemDelta]; rw [hs2_fr] at hbos_fr; omega))
    ((Nat.mul_le_mul_left _ (bucket_prod_le_stateCap args.x es)).trans hcapB) hB
  dsimp only at hboe
  have hwf₄ := wellFormed_clientState hwf₃ hboe.1
  rw [validHistory_bind', StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, memoryCost_bind']
  generalize (Memory.spec 0).clientState s₃
    (buildOutEntries ⟨args.dom, args.x, outPair.1, outPair.2, part.bucketPtr, part.bucketLen⟩) =
      s₄ at hboe hwf₄ ⊢
  generalize (Memory.spec 0).clientResult s₃
    (buildOutEntries ⟨args.dom, args.x, outPair.1, outPair.2, part.bucketPtr, part.bucketLen⟩) =
      entPair at hboe ⊢
  obtain ⟨hboe_val, hboe_pres, hboe_fr, hboe_lo, hboe_len, hboe_holds, hboe_cost⟩ := hboe
  let newTab := elimBucketTable args.dom args.x bucket
  change entPair.2 = newTab.entries.size at hboe_len
  change HoldsIn entPair.1 newTab.entries.toList s₄ at hboe_holds
  have hs2_le_s3 : s₂.frontier ≤ s₃.frontier := hbos_pres.2.1
  have hs3_le_s4 : s₃.frontier ≤ s₄.frontier := hboe_pres.2.1
  have hout_s4 : HoldsIn outPair.1 newTab.scope s₄ := hbos_holds.mono_frontier hboe_pres
  have hsc_eq_new : newTab.scope = bucketOutScope args.x bucket := rfl
  have hfit_o1 : Fits w outPair.1 := hwf₄.frontier_fits.of_le (by have := hout_s4.1; omega)
  have hfit_o2 : Fits w outPair.2 := hwf₄.frontier_fits.of_le (by
    have hbd := hout_s4.1; rw [hsc_eq_new, ← hbos_len] at hbd; omega)
  have hfit_e1 : Fits w entPair.1 := hwf₄.frontier_fits.of_le (by have := hboe_holds.1; omega)
  have hfit_e2 : Fits w entPair.2 := hwf₄.frontier_fits.of_le (by
    have hbd := hboe_holds.1; rw [Array.length_toList, ← hboe_len] at hbd; omega)
  have hwd_val := writeDesc_valid (s := s₄)
    ⟨part.newLiveBuf, outPair.1, outPair.2, entPair.1, entPair.2⟩ (by dsimp only; omega)
    hfit_o1 hfit_o2 hfit_e1 hfit_e2
  have hst5_def : (Memory.spec 0).clientState s₄
      (writeDesc ⟨part.newLiveBuf, outPair.1, outPair.2, entPair.1, entPair.2⟩) =
      ⟨Function.update (Function.update (Function.update
        (Function.update s₄.mem part.newLiveBuf outPair.1) (part.newLiveBuf + 1) outPair.2)
        (part.newLiveBuf + 2) entPair.1) (part.newLiveBuf + 3) entPair.2, s₄.frontier⟩ := rfl
  obtain ⟨hs5_fr, hwd_out⟩ :=
    writeDesc_frame ⟨part.newLiveBuf, outPair.1, outPair.2, entPair.1, entPair.2⟩ s₄
  rw [validHistory_bind', StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, memoryCost_bind', writeDesc_cost]
  generalize (Memory.spec 0).clientState s₄
    (writeDesc ⟨part.newLiveBuf, outPair.1, outPair.2, entPair.1, entPair.2⟩) = s₅
    at hs5_fr hwd_out hst5_def ⊢
  dsimp only at hwd_out
  obtain ⟨hm0, hm1, hm2, hm3⟩ : s₅.mem part.newLiveBuf = outPair.1 ∧
      s₅.mem (part.newLiveBuf + 1) = outPair.2 ∧ s₅.mem (part.newLiveBuf + 2) = entPair.1 ∧
      s₅.mem (part.newLiveBuf + 3) = entPair.2 := by
    rw [hst5_def]; simp
  have hpres_25 : PreservesBelow s₁.frontier s₂ s₅ :=
    ⟨hpl_pres.2.1, by omega, fun a ha => by
      rw [hwd_out a (Or.inl (by omega)), hboe_pres.2.2 a (by omega)]
      exact hbos_pres.2.2 a (by omega)⟩
  have hpres_15 := hpl_pres.trans hpres_25
  have hpres_all : PreservesBelow s.frontier s s₅ :=
    hfn_pres.trans_frontier hpres_15
  have hnew_f : HoldsFactor part.newLiveBuf newTab s₅ := by
    unfold HoldsFactor
    rw [hm0, hm1, hm2, hm3]
    refine ⟨by omega, hbos_len, hboe_len,
      ⟨by rw [hs5_fr]; exact hout_s4.1, hout_s4.2.frame fun a hlo _ => ?_⟩,
      ⟨by rw [hs5_fr]; exact hboe_holds.1, hboe_holds.2.frame fun a hlo _ => ?_⟩⟩
    · exact hwd_out a (Or.inr (by omega))
    · exact hwd_out a (Or.inr (by omega))
  have hrest_s5 : HoldsFactorList (part.newLiveBuf + 4) rest s₅ :=
    hpl_rH.frame_outside hpl_rD hpres_25 fun a hlo hhi => by
      have hr_le : rest.length ≤ args.liveLen := (List.length_filter_le _ _).trans hlive_len.ge
      rw [hwd_out a (Or.inr hlo), hboe_pres.2.2 a (by omega)]
      exact hbos_pres.2.2 a (by omega)
  rw [StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientState_pure,
    memoryCost_pure, hes'_eq, hbk_eq]
  refine ⟨⟨hms_val, hfn_val, hpl_val, hbos_val, hboe_val, hwd_val, validHistory_pure w _ _⟩,
    hpres_all, by dsimp only [stepMemDelta]; omega,
    ⟨lt_of_lt_of_le hs0 hpres_all.2.1, hsc_eq, ?_, hfn_len, ⟨hnew_f, hrest_s5⟩,
      hfn_holds.mono_frontier hpres_15⟩, ?_⟩
  · dsimp only
    rw [hpl_rLen, List.length_cons, Nat.add_comm]
  have hboe_c : memoryCost (buildOutEntries
      ⟨args.dom, args.x, outPair.1, outPair.2, part.bucketPtr, part.bucketLen⟩) s₃ ≤
        3 + W + 4 * (max 1 args.dom) ^ W +
          bucket.length * ((max 1 args.dom) ^ W * (5 + SW * W)) :=
    calc _ ≤ 3 + outPair.2 + (max 1 args.dom) ^ outPair.2 *
              (3 + args.dom * (1 + part.bucketLen * (5 + SW * (outPair.2 + 1)))) := hboe_cost
      _ = 3 + outPair.2 + (max 1 args.dom) ^ outPair.2 * 3 +
            ((max 1 args.dom) ^ outPair.2 * args.dom) * 1 +
            bucket.length * (((max 1 args.dom) ^ outPair.2 * args.dom) *
              (5 + SW * (outPair.2 + 1))) := by
          rw [hpl_bLen]; ring
      _ ≤ 3 + W + (max 1 args.dom) ^ W * 3 + (max 1 args.dom) ^ W * 1 +
            bucket.length * ((max 1 args.dom) ^ W * (5 + SW * W)) := by gcongr; omega
      _ = _ := by ring
  have hunit_split : part.bucketLen * (3 + 2 * SW + SW * (2 + W)) +
      bucket.length * ((max 1 args.dom) ^ W * (5 + SW * W)) =
      bucket.length * stepBucketUnitCost SW args.dom W := by
    rw [hpl_bLen]; dsimp only [stepBucketUnitCost]; ring
  dsimp only [stepFixedCost]
  omega

theorem elimVarProg_realizes :
    Realizes .exact elimVarProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧
        ∃ es R M SW W B,
          HoldsElimState
            ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩ es s ∧
          es.live.length ≤ M ∧
          es.remaining.length ≤ R ∧
          (∀ f ∈ es.live, f.scope.length ≤ SW) ∧
          (stepStats args.dom args.x es).jointScopeVars ≤ W ∧
          W ≤ SW ∧
          max 1 args.dom * stateCap es ≤ B ∧
          Fits w B ∧
          Fits w ((max 1 args.dom) ^ SW) ∧
          Fits w (s.frontier + stepMemDelta R M SW args.dom W))
      (fun _ _ => 0) := by
  unfold elimVarProg
  realize [memScan_realizes, filterNe_realizes, partitionLive_realizes,
    buildOutScope_realizes, buildOutEntries_realizes, writeDesc_realizes]
  all_goals
    obtain ⟨h1, es, R, M, SW, W, B, hes, hM, hR, hSW, hW, _hW_SW, hcapB, hB, hpowSW, hfit_fr⟩ := h
    obtain ⟨_hs0, hsc_eq, hlive_len, hrem_len, hlive_h, hrem_h⟩ := hes
    dsimp only at hsc_eq hlive_len hrem_len hlive_h hrem_h
    obtain ⟨hfn_val, hfn_fr, hfn_pres, _, _, _⟩ :=
      filterNe_spec (w := w) ⟨d.x, d.remPtr, d.remLen⟩ hmem hrem_h hrem_len.symm
        (hfit_fr.of_le (by dsimp only [stepMemDelta]; omega))
    dsimp only at hfn_fr
    have hwf₁ := wellFormed_clientState hmem hfn_val
    obtain ⟨hpl_val, hpl_fr, _, _, hpl_rBuf, hpl_bLen, hpl_rLen, hpl_bH, _, _, _, _⟩ :=
      partitionLive_spec (w := w) (args := ⟨d.x, d.livePtr, d.liveLen⟩) hwf₁
        (hlive_h.mono_frontier hfn_pres) hlive_len.symm hSW
        (hfit_fr.of_le (by rw [hfn_fr]; dsimp only [stepMemDelta]; omega))
    dsimp only at hpl_fr hpl_rBuf hpl_bLen hpl_rLen hpl_bH
    have hwf₂ := wellFormed_clientState hwf₁ hpl_val
    let s₁ := (Memory.spec 0).clientState s (filterNe ⟨d.x, d.remPtr, d.remLen⟩)
    let part := (Memory.spec 0).clientResult s₁ (partitionLive ⟨d.x, d.livePtr, d.liveLen⟩)
    let bucket := es.live.filter fun f => decide (d.x ∈ f.scope)
    have hb_SW : ∀ f ∈ bucket, f.scope.length ≤ SW :=
      fun f hf => hSW f (List.mem_filter.mp hf).1
    have hb_le_M : part.bucketLen ≤ M := by
      rw [hpl_bLen]; exact (List.length_filter_le _ _).trans hM
    obtain ⟨_, hbos_fr, hbos_pres, _, hbos_len, hbos_holds, _⟩ :=
      buildOutScope_spec (w := w) (args := ⟨d.x, part.bucketPtr, part.bucketLen⟩)
        hwf₂ hpl_bH hpl_bLen.symm hb_SW le_rfl
        (hfit_fr.of_le (by
          dsimp only [stepMemDelta]
          rw [hpl_fr, hfn_fr]
          have := Nat.mul_le_mul_right SW hb_le_M; omega))
    dsimp only [part, s₁] at hbos_fr hbos_len hbos_holds hb_le_M
  · exact h1
  · exact hfit_fr.of_le (by have := hrem_h.1; rw [← hrem_len] at this; omega)
  · exact hfit_fr.of_le (by have := hrem_h.1; rw [← hrem_len] at this; omega)
  · rw [memScan_state]
    exact hfit_fr.of_le (by dsimp only [stepMemDelta]; omega)
  · exact h1
  · rw [memScan_state, hfn_fr]
    exact hfit_fr.of_le (by dsimp only [stepMemDelta]; omega)
  · rw [memScan_state]
    exact ⟨es.live, hlive_len.symm, hlive_h.mono_frontier hfn_pres⟩
  · refine hB.of_le (le_trans ?_ hcapB)
    calc d.scalar * d.dom ≤ max 1 d.dom * max 1 es.scalar := by
          rw [hsc_eq, Nat.mul_comm]
          exact Nat.mul_le_mul (le_max_right 1 d.dom) (le_max_right 1 es.scalar)
      _ ≤ (max 1 d.dom * max 1 es.scalar) * (es.live.map capFactor).prod :=
          Nat.le_mul_of_pos_right _
            (List.one_le_prod_of_one_le (l := es.live.map capFactor) (by simp [one_le_capFactor]))
      _ = max 1 d.dom * stateCap es := by unfold stateCap; ring
  · exact h1
  · rw [memScan_state]
    have hK_le : (bucket.flatMap FactorTable.scope).length ≤ M * SW :=
      (List.length_flatMap_le hb_SW).trans
        (Nat.mul_le_mul_right SW ((List.length_filter_le _ _).trans hM))
    refine ⟨bucket, hpl_bLen.symm, hpl_bH, hfit_fr.of_le ?_⟩
    rw [hpl_fr, hfn_fr]
    dsimp only [stepMemDelta]
    omega
  · rw [memScan_state]
    have hbd := hbos_holds.1
    rw [← hbos_len] at hbd
    exact hbd
  · rw [memScan_state] at hc ⊢
    have hx : d.x ∈ es.remaining := by
      by_contra hnx
      exact absurd ((memScan_result (args := ⟨d.x, d.remPtr, d.remLen⟩) hrem_h.2
        hrem_len.symm).trans (ite_eq_right hnx)) ‹_›
    have hbk_ne : bucket.isEmpty = false :=
      Bool.eq_false_iff.mpr fun hb =>
        hc (hpl_bLen.trans (List.length_eq_zero_iff.mpr (List.isEmpty_iff.mp hb)))
    have hj_le : (bucketJointScope bucket).length ≤ W := by
      simpa [stepStats, hx, hbk_ne, bucket] using hW
    have hpow_le := Nat.pow_le_pow_right (le_max_left 1 d.dom)
      (hbos_len.trans_le ((List.length_filter_le _ _).trans hj_le))
    refine hfit_fr.of_le ?_
    have hbmul := Nat.mul_le_mul_right SW hb_le_M
    rw [hpl_fr, hfn_fr] at hbos_fr
    dsimp only [stepMemDelta]
    omega
  · rw [memScan_state]
    exact ⟨bucket, B, SW, hpl_bLen.symm, hpl_bH.mono_frontier hbos_pres, hb_SW, hpowSW,
      (Nat.mul_le_mul_left _ (bucket_prod_le_stateCap d.x es)).trans hcapB, hB⟩
  · rw [memScan_state, hpl_rBuf, hfn_fr]
    exact hfit_fr.of_le (by dsimp only [stepMemDelta]; omega)
  · rw [memScan_state, hpl_rLen]
    have hr_le : (es.live.filter fun f => decide (d.x ∉ f.scope)).length ≤ M :=
      (List.length_filter_le _ _).trans hM
    exact hfit_fr.of_le (by dsimp only [stepMemDelta]; omega)

end Cslib.Algorithms.WordRAM.VariableElimination
