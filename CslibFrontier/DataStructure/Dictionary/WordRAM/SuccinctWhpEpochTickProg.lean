/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSmallCsrProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.Common
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.Tick
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.CheckOk
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg
import CslibFrontier.Tactic.Realize

/-!
# Global Epoch Ticks and Fast-Mode Step `Memory.Prog` Subroutines

This module exports the parameter-free combined fast-mode operation dispatcher
`fastStepPureGenProg`, its `Realizes .exact` certificate `realizes_fastStepPureGen`, and the
`c`-only cost and `FastStateStep` bound `fastStepPureGenProg_spec` for `SuccinctWhpModel`.

The underlying global deamortized epoch-rebuild subroutines and proofs live under
`CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal` (built on
shared header and step combinators in `Internal.Common`):

1. `Internal.RebScan` (`rebScanLoopGenProg`): `16`-coordinate Stage-2 candidate-salt scan loop
   via `Realizes.iterate₀`, refining `rebScanSteps c U n_max θ b 16 fs` in `O_c(1)` worst-case
   `memoryCost`.
2. `Internal.Stage0` .. `Internal.Stage4` and `Internal.Tick` (`epochTickGenProg`): Stage `0 .. 5`
   deamortization and epoch rollover, refining `epochTick c U n_max θ fs = some fs'` whenever
   `epochTickWillSucceed n_max fs` holds.
3. `Internal.CheckOk` (`checkEpochTickOkGenProg`) and this module (`fastStepPureGenProg`): `O(1)`
   read-only rollover pre-check and combined `fastQuery` / `fastDelete` / `fastInsert` +
   `epochTick` execution, guaranteeing `clientState s prog = s` whenever
   `fastStepPure c U n_max θ fs op = none`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastStepPureGenProg`, `fastOpCostWhp`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastStepPureGen`,
  `fastStepPureGenProg_spec`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-- `c`-only worst-case `memoryCost` bound for a fast-mode operation (`fastStepPureGenProg`). -/
@[expose] def fastOpCostWhp (c : ℕ) : ℕ :=
  32 * cTabWhp c + 73 * hashEvalCostWhp c + 90000

@[irreducible] private def fastStepQueryProg :
    (WhpParams × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((wp, base), u_val) => do
    let z1 ← pure 1
    let res ← fastQueryGenProg ((wp, base), u_val)
    epochTickGenProg (wp, base)
    pure (z1, res)

private theorem realizes_fastStepQuery :
    Realizes .exact fastStepQueryProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((wp, base), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U)
            (u : Fin U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val = u.val)
      (fun _ _ => 0) := by
  unfold fastStepQueryProg
  have hfq := realizes_fastQueryGen
  have het := realizes_epochTickGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, u, henv, heq_wp, hseed, hrep, hv, rfl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hfq_st, _, _, _⟩ := fastQueryGenProg_spec henv hseed hrep hv u (s := s)
    simp only [hfq_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | (rw [hcp_eq, wp_large_U hth]; exact u.isLt)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv.toCore,
        hv.stage_valid.toPreTick⟩
  )

@[irreducible] private def fastStepInsertProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (((wp, base), u_val), v_val) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let insOk ← fastInsertGenProg (((wp, base), u_val), v_val)
    if insOk = z1 then
      epochTickGenProg (wp, base)
      pure (z1, (z0, z0))
    else
      pure (z0, (z0, z0))

private theorem realizes_fastStepInsert :
    Realizes .exact fastStepInsertProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (((wp, base), u_val), v_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U)
            (u : Fin U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          Dynamic.valid V n_max dict (.insert u v_val) ∧
          u_val = u.val)
      (fun _ _ => 0) := by
  unfold fastStepInsertProg
  have hfi := realizes_fastInsertGen
  have het := realizes_epochTickGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, u_val⟩, v_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, u, henv, heq_wp, hseed, hrep, hv, hval_op, rfl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hnU := henv.2.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨_, _, hfi_m⟩ := fastInsertGenProg_spec henv hseed hrep hv u hval_op.2 (s := s)
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | (rw [hcp_eq, wp_large_U hth]; exact u.isLt)
    | (rw [hcp_eq, wp_large_V hth]; exact hval_op.2)
    | (cases hins : fastInsert c U n_max θ fs u v_val with
       | none =>
         rw [hins] at hfi_m
         have hhit : (Memory.spec 0).clientResult s
           (fastInsertGenProg (((mkWhpParams c U V w n_max, base), u.val), v_val)) = 1 :=
             by assumption
         rw [hfi_m.1] at hhit; cases hhit
       | some fs1 =>
         rw [hins] at hfi_m
         obtain ⟨hcore1, _, hst1, _⟩ := hv.fastInsert_spec hnU hval_op hins
         exact ⟨c, U, V, w, n_max, θ, fs1, (Dynamic.step dict (.insert u v_val)).1,
           henv, rfl, hfi_m.2.2.1, hfi_m.2.2.2.1, hcore1, hst1.toPreTick⟩)
  )

@[irreducible] private def fastStepDeleteProg :
    (WhpParams × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((wp, base), u_val) => do
    let z0 ← pure 0
    let z1 ← pure 1
    fastDeleteGenProg ((wp, base), u_val)
    epochTickGenProg (wp, base)
    pure (z1, (z0, z0))

private theorem realizes_fastStepDelete :
    Realizes .exact fastStepDeleteProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((wp, base), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U)
            (u : Fin U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val = u.val)
      (fun _ _ => 0) := by
  unfold fastStepDeleteProg
  have hfd := realizes_fastDeleteGen
  have het := realizes_epochTickGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, u, henv, heq_wp, hseed, hrep, hv, rfl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨_, _, hfd_step⟩ := fastDeleteGenProg_fastStep henv hseed hrep hv u (s := s)
    obtain ⟨hcore1, _, hpre1, _⟩ := hv.fastDelete_spec u
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | (rw [hcp_eq, wp_large_U hth]; exact u.isLt)
    | exact ⟨c, U, V, w, n_max, θ, fastDelete c U n_max θ fs u,
        (Dynamic.step dict (.delete u)).1, henv, rfl,
        hfd_step.2.1, hfd_step.2.2.1, hcore1, hpre1⟩
  )

/-- Combined fast-mode operation dispatcher (`d = ((wp, base), (opTag, (u_val, v_val)))`),
returning `(1, encodeOptRes res)` when `fastStepPure = some (fs', res)` and `(0, (0, 0))` without
mutating memory when `fastStepPure = none`. -/
@[irreducible] def fastStepPureGenProg :
    (WhpParams × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((wp, base), (opTag, (u_val, v_val))) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let tickOk ← checkEpochTickOkGenProg (wp.1, base)
    if tickOk = z1 then
      if opTag = z0 then
        fastStepQueryProg ((wp, base), u_val)
      else if opTag = z1 then
        fastStepInsertProg (((wp, base), u_val), v_val)
      else
        fastStepDeleteProg ((wp, base), u_val)
    else
      pure (z0, (z0, z0))

theorem realizes_fastStepPureGen :
    Realizes .exact fastStepPureGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((wp, base), (opTag, (u_val, v_val))) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U)
            (op : Dynamic.Op U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          Dynamic.valid V n_max dict op ∧
          encodeOpWhp op = (opTag, (u_val, v_val)))
      (fun _ _ => 0) := by
  unfold fastStepPureGenProg
  have hck := realizes_checkEpochTickOkGen
  have hsq := realizes_fastStepQuery
  have hsi := realizes_fastStepInsert
  have hsd := realizes_fastStepDelete
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, ⟨opTag, ⟨u_val, v_val⟩⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, op, henv, heq_wp, hseed, hrep, hv, hval_op,
      hop_enc⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hck_st, hck_res, _, _⟩ :=
      checkEpochTickOkGenProg_spec henv hv.curEp_or hrep (s := s)
    simp only [hcp_eq] at *
    simp only [hck_st, hck_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hv.curEp_or, hv.epochClock_lt⟩
    | (cases op with
       | query u =>
         dsimp only [encodeOpWhp] at hop_enc
         rcases Prod.mk.inj hop_enc with ⟨rfl, hp2⟩
         rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
         first
         | (exfalso; omega)
         | exact ⟨c, U, V, w, n_max, θ, fs, dict, u, henv, rfl, hseed, hrep, hv, rfl⟩
       | insert u v =>
         dsimp only [encodeOpWhp] at hop_enc
         rcases Prod.mk.inj hop_enc with ⟨rfl, hp2⟩
         rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
         first
         | (exfalso; omega)
         | exact ⟨c, U, V, w, n_max, θ, fs, dict, u, henv, rfl, hseed, hrep, hv, hval_op, rfl⟩
       | delete u =>
         dsimp only [encodeOpWhp] at hop_enc
         rcases Prod.mk.inj hop_enc with ⟨rfl, hp2⟩
         rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
         first
         | (exfalso; omega)
         | exact ⟨c, U, V, w, n_max, θ, fs, dict, u, henv, rfl, hseed, hrep, hv, rfl⟩)
  )

private theorem epochTick_eq_none_of_false {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} (hle : fs.rebStage ≤ 5) (hnot : epochTickWillSucceed n_max fs = false) :
    epochTick c U n_max θ fs = none := by
  have his := epochTick_isSome_iff θ hle
  rw [hnot] at his
  cases h : epochTick c U n_max θ fs with
  | none => rfl
  | some _ => rw [h] at his; cases his

private theorem fastStepPure_notOk_tail {c U V w n_max base : ℕ} {s : Memory.State}
    {fs : FastState} {pThen : Memory.Prog (ℕ × (ℕ × ℕ))}
    (hnot : epochTickWillSucceed n_max fs = false)
    (hck_st : (Memory.spec 0).clientState s
      (checkEpochTickOkGenProg (mkWhpCoreParams c U V w n_max, base)) = s)
    (hck_res : (Memory.spec 0).clientResult s
      (checkEpochTickOkGenProg (mkWhpCoreParams c U V w n_max, base)) =
      (if epochTickWillSucceed n_max fs then 1 else 0))
    (hck_mc : memoryCost (checkEpochTickOkGenProg (mkWhpCoreParams c U V w n_max, base)) s ≤ 5)
    (hck_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (checkEpochTickOkGenProg (mkWhpCoreParams c U V w n_max, base))) :
    let prog := checkEpochTickOkGenProg (mkWhpCoreParams c U V w n_max, base) >>= fun tickOk =>
      if tickOk = 1 then pThen else pure (0, (0, 0))
    memoryCost prog s ≤ 32 * cTabWhp c + 73 * hashEvalCostWhp c + 90000 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (Memory.spec 0).clientResult s prog = (0, (0, 0)) ∧
    (Memory.spec 0).clientState s prog = s := by
  rw [hnot] at hck_res; simp only [Bool.false_eq_true, ↓reduceIte] at hck_res
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hck_st, hck_res]; simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]; omega
  · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]
    simp only [zero_ne_one, ↓reduceIte]; exact validProg_pure _
  · rw [clientResult_bind, hck_st, hck_res]; rfl
  · rw [clientState_bind, hck_st, hck_res]; rfl

theorem fastStepPureGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    {op : Dynamic.Op U} (hval_op : Dynamic.valid V n_max dict op) :
    let prog := fastStepPureGenProg ((mkWhpParams c U V w n_max, base), encodeOpWhp op)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ fastOpCostWhp c ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    match fastStepPure c U n_max θ fs op with
    | some (fs', res) =>
      (Memory.spec 0).clientResult s prog = (1, encodeOptRes res) ∧
      FastStateStep base c U V w n_max θ fs' s s'
    | none =>
      (Memory.spec 0).clientResult s prog = (0, (0, 0)) ∧
      s' = s := by
  have hth := henv.2.2.2.1
  have hnU := henv.2.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hck_st, hck_res, hck_mc, hck_vp⟩ :=
    checkEpochTickOkGenProg_spec henv hv.curEp_or hrep (s := s)
  dsimp only [fastOpCostWhp]
  cases op with
  | query u =>
    dsimp only [encodeOpWhp, fastStepPure]
    unfold fastStepPureGenProg fastStepQueryProg; dsimp only
    rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    simp only [pure_bind]
    by_cases hok : epochTickWillSucceed n_max fs = true
    · rw [hok] at hck_res; simp only [↓reduceIte] at hck_res
      obtain ⟨hfq_st, hfq_res, hfq_mc, hfq_vp⟩ :=
        fastQueryGenProg_spec henv hseed hrep hv u (s := s)
      obtain ⟨fs', het_eq, het_mc, het_vp, het_step⟩ :=
        epochTickGenProg_fastStep henv hv.toCore hv.stage_valid.toPreTick hok hseed hrep (s := s)
      rw [het_eq]
      have hres_eq : (Memory.spec 0).clientResult s
          (fastQueryGenProg ((mkWhpParams c U V w n_max, base), u.val)) =
          encodeOptRes (fastQuery c U n_max θ fs u) := by
        refine hfq_res.trans ?_
        cases fastQuery c U n_max θ fs u <;> rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        dsimp only [cp] at hck_st hck_res hck_mc ⊢
        rw [hck_st, hck_res]; simp only [↓reduceIte, memoryCost_bind]
        rw [hfq_st, hres_eq, memoryCost_pure]; omega
      · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]; simp only [↓reduceIte]
        refine validProg_bind hfq_vp ?_; rw [hfq_st, hres_eq]
        exact validProg_bind het_vp (validProg_pure _)
      · rw [clientResult_bind, hck_st, hck_res]; simp only [↓reduceIte]
        rw [clientResult_bind, hfq_st, hres_eq, clientResult_bind]; rfl
      · rw [clientState_bind, hck_st, hck_res]; simp only [↓reduceIte]
        rw [clientState_bind, hfq_st, clientState_bind, clientState_pure_whp]
        exact het_step
    · have hnot : epochTickWillSucceed n_max fs = false := Bool.eq_false_iff.mpr hok
      rw [epochTick_eq_none_of_false hv.rebStage_le hnot]
      exact fastStepPure_notOk_tail hnot hck_st hck_res hck_mc hck_vp
  | insert u v =>
    dsimp only [encodeOpWhp, fastStepPure]
    unfold fastStepPureGenProg fastStepInsertProg; dsimp only
    rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    simp only [pure_bind, one_ne_zero, ↓reduceIte]
    by_cases hok : epochTickWillSucceed n_max fs = true
    · rw [hok] at hck_res; simp only [↓reduceIte] at hck_res
      obtain ⟨hfi_mc, hfi_vp, hfi_m⟩ :=
        fastInsertGenProg_spec henv hseed hrep hv u hval_op.2 (s := s)
      set progIns := fastInsertGenProg (((mkWhpParams c U V w n_max, base), u.val), v)
      set s1 := (Memory.spec 0).clientState s progIns
      cases hins : fastInsert c U n_max θ fs u v with
      | none =>
        rw [hins] at hfi_m
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          dsimp only [cp] at hck_st hck_res hck_mc ⊢
          rw [hck_st, hck_res]; simp only [↓reduceIte, memoryCost_bind]
          dsimp only [progIns] at hfi_m hfi_mc ⊢
          rw [hfi_m.1]; simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]; omega
        · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]; simp only [↓reduceIte]
          refine validProg_bind hfi_vp ?_; dsimp only [progIns] at hfi_m
          rw [hfi_m.1]; simp only [zero_ne_one, ↓reduceIte]; exact validProg_pure _
        · rw [clientResult_bind, hck_st, hck_res]; simp only [↓reduceIte]
          rw [clientResult_bind]; dsimp only [progIns] at hfi_m; rw [hfi_m.1]; rfl
        · rw [clientState_bind, hck_st, hck_res]; simp only [↓reduceIte]
          rw [clientState_bind]; dsimp only [progIns, s1] at hfi_m
          rw [hfi_m.1, hfi_m.2]; rfl
      | some fs1 =>
        rw [hins] at hfi_m; dsimp only
        obtain ⟨hcore1, _, hst1, _⟩ := hv.fastInsert_spec hnU hval_op hins
        have hok1 : epochTickWillSucceed n_max fs1 = true :=
          (epochTickWillSucceed_fastInsert hv hins).trans hok
        obtain ⟨fs', het_eq, het_mc, het_vp, het_step⟩ :=
          epochTickGenProg_fastStep henv hcore1 hst1.toPreTick hok1
            hfi_m.2.2.1 hfi_m.2.2.2.1 (s := s1)
        rw [het_eq]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          dsimp only [cp] at hck_st hck_res hck_mc ⊢
          rw [hck_st, hck_res]; simp only [↓reduceIte, memoryCost_bind]
          dsimp only [progIns, s1] at hfi_m hfi_mc het_mc ⊢
          rw [hfi_m.1]; simp only [↓reduceIte, memoryCost_bind, memoryCost_pure]; omega
        · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]; simp only [↓reduceIte]
          refine validProg_bind hfi_vp ?_; dsimp only [progIns] at hfi_m
          rw [hfi_m.1]; simp only [↓reduceIte]
          exact validProg_bind het_vp (validProg_pure _)
        · rw [clientResult_bind, hck_st, hck_res]; simp only [↓reduceIte]
          rw [clientResult_bind]; dsimp only [progIns] at hfi_m; rw [hfi_m.1]
          simp only [↓reduceIte]; rw [clientResult_bind]; rfl
        · rw [clientState_bind, hck_st, hck_res]; simp only [↓reduceIte]
          rw [clientState_bind]; dsimp only [progIns] at hfi_m; rw [hfi_m.1]
          simp only [↓reduceIte]; rw [clientState_bind, clientState_pure_whp]
          exact hfi_m.2.trans het_step
    · have hnot : epochTickWillSucceed n_max fs = false := Bool.eq_false_iff.mpr hok
      have hfail := fastStepPure_notOk_tail (fs := fs)
        (pThen := fastInsertGenProg (((mkWhpParams c U V w n_max, base), u.val), v) >>=
          fun insOk => if insOk = 1 then
            epochTickGenProg (mkWhpParams c U V w n_max, base) >>= fun _ => pure (1, (0, 0))
          else pure (0, (0, 0)))
        hnot hck_st hck_res hck_mc hck_vp
      refine ⟨hfail.1, hfail.2.1, ?_⟩
      cases hins : fastInsert c U n_max θ fs u v with
      | none => exact hfail.2.2
      | some fs1 =>
        obtain ⟨hcore1, _, _, _⟩ := hv.fastInsert_spec hnU hval_op hins
        have hnot1 : epochTickWillSucceed n_max fs1 = false :=
          (epochTickWillSucceed_fastInsert hv hins).trans hnot
        dsimp only; rw [epochTick_eq_none_of_false hcore1.rebStage_le hnot1]
        exact hfail.2.2
  | delete u =>
    dsimp only [encodeOpWhp, fastStepPure]
    unfold fastStepPureGenProg fastStepDeleteProg; dsimp only
    rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    simp only [pure_bind, show ¬((2 : ℕ) = 0) by decide, show ¬((2 : ℕ) = 1) by decide,
      ↓reduceIte]
    obtain ⟨hcore1, _, hpre1, _⟩ := hv.fastDelete_spec u
    by_cases hok : epochTickWillSucceed n_max fs = true
    · rw [hok] at hck_res; simp only [↓reduceIte] at hck_res
      obtain ⟨hfd_mc, hfd_vp, hfd_step⟩ := fastDeleteGenProg_fastStep henv hseed hrep hv u (s := s)
      set s1 := (Memory.spec 0).clientState s
        (fastDeleteGenProg ((mkWhpParams c U V w n_max, base), u.val))
      have hok1 : epochTickWillSucceed n_max (fastDelete c U n_max θ fs u) = true :=
        (epochTickWillSucceed_fastDelete hv u).trans hok
      obtain ⟨fs', het_eq, het_mc, het_vp, het_step⟩ :=
        epochTickGenProg_fastStep henv hcore1 hpre1 hok1 hfd_step.2.1 hfd_step.2.2.1 (s := s1)
      rw [het_eq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        dsimp only [cp] at hck_st hck_res hck_mc ⊢
        rw [hck_st, hck_res]; simp only [↓reduceIte, memoryCost_bind]
        dsimp only [s1] at hfd_mc het_mc ⊢
        rw [memoryCost_pure]; omega
      · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]; simp only [↓reduceIte]
        refine validProg_bind hfd_vp ?_
        exact validProg_bind het_vp (validProg_pure _)
      · rw [clientResult_bind, hck_st, hck_res]; simp only [↓reduceIte]
        rw [clientResult_bind, clientResult_bind]; rfl
      · rw [clientState_bind, hck_st, hck_res]; simp only [↓reduceIte]
        rw [clientState_bind, clientState_bind, clientState_pure_whp]
        exact hfd_step.trans het_step
    · have hnot : epochTickWillSucceed n_max fs = false := Bool.eq_false_iff.mpr hok
      have hnot1 : epochTickWillSucceed n_max (fastDelete c U n_max θ fs u) = false :=
        (epochTickWillSucceed_fastDelete hv u).trans hnot
      rw [epochTick_eq_none_of_false hcore1.rebStage_le hnot1]
      exact fastStepPure_notOk_tail hnot hck_st hck_res hck_mc hck_vp

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
