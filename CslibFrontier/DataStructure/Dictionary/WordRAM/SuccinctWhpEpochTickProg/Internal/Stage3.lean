/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.Common
import CslibFrontier.Tactic.Realize

/-!
# Stage 3 of `epochTick`

Implements and verifies `epochTickStage3GenProg`, which scans active slots of `buf oldEp`,
deletes them from the buffer trie, marks their coordinates clean (`locState := 1`), and
transitions `rebStage` to `4`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

attribute [local simp] clientResult_pure_whp clientState_pure_whp

private theorem bufDelete_allocs (cTab bChar : ℕ) (tr : BufTrie) (rKey : ℕ) :
    (bufDelete cTab bChar tr rKey).nodeAlloc = tr.nodeAlloc ∧
    (bufDelete cTab bChar tr rKey).itemAlloc = tr.itemAlloc := by
  dsimp only [bufDelete]
  cases bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => exact ⟨rfl, rfl⟩
  | some _ => dsimp only; split_ifs <;> exact ⟨rfl, rfl⟩

/-- Stage 3 `some (b, loc)` helper: delete `rKeyAt b loc` from `buf oldEp` and set
`locState b loc := 1` (`d = (((wp, base), oldEp), (b, loc))`). -/
@[irreducible] private def stage3ClearActiveProg :
    ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((wp, base), oldEp), (b, loc)) => do
    let z1 ← pure 1
    let rKey ← rKeyAtGenProg (((wp, base), b), loc)
    bufDeleteGenProg (((wp.1, base), oldEp), rKey)
    writeFastLocGenProg ((((wp.1, base), b), loc), z1)

private theorem realizes_stage3ClearActive :
    Realizes .exact stage3ClearActiveProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), oldEp), (b, loc)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
            (oldMap : ℕ → Option (ℕ × ℕ)),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (oldEp = 0 ∨ oldEp = 1) ∧
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf oldEp) oldMap ∧
          (∀ p, fs.quotArr p < 2 ^ quotBitsWhp U n_max) ∧
          b < numBucketsWhp n_max ∧
          loc < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max))
      (fun _ _ => 0) := by
  unfold stage3ClearActiveProg
  have hrk := realizes_rKeyAtGen
  have hbd := realizes_bufDeleteGen
  have hwl := realizes_writeFastLocGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, oldEp⟩, ⟨b, loc⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, oldMap, henv, heq_wp, hseed, hrep, hold_or, hv_o,
      hq_all, hb, hloc, hbp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hrk_st, hrk_res, _, _⟩ :=
      rKeyAtGenProg_spec henv hseed hrep hb hloc hbp (s := s)
    simp only [hcp_eq] at *
    simp only [hrk_st, hrk_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_M hth]; exact hb)
    | (rw [wp_large_totalLoc hth]; exact hloc)
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, fun p _ => hq_all p, hb, hloc, hbp⟩
    | exact ⟨c, U, V, w, n_max, fs.buf oldEp, oldMap, henv, rfl, hold_or,
        hrep.buf_rep hold_or, hv_o⟩
  )

private theorem stage3ClearActiveProg_fastStep {c U V w n_max base oldEp b loc : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {oldMap : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hold_or : oldEp = 0 ∨ oldEp = 1)
    (hv_o : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf oldEp) oldMap)
    (hb : b < numBucketsWhp n_max)
    (hloc : loc < totalLocalCoordsWhp n_max)
    (hbp : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage3ClearActiveProg (((mkWhpParams c U V w n_max, base), oldEp), (b, loc))
    let s' := (Memory.spec 0).clientState s prog
    let rKey := fs.rKeyAt c U n_max θ b loc
    let tr' := bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf oldEp) rKey
    memoryCost prog s ≤ 2 * cTabWhp c + hashEvalCostWhp c + 17 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        buf := Function.update fs.buf oldEp tr'
        locState := Function.update fs.locState b
          (Function.update (fs.locState b) loc 1) } s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    rKeyAtGenProg_spec henv hseed hrep hb hloc hbp (s := s)
  set rKey := fs.rKeyAt c U n_max θ b loc
  obtain ⟨hbd_mc, hbd_vp, hbd_step⟩ :=
    bufDeleteGenProg_fastStep henv hold_or hseed hrep hv_o (rKey := rKey) (s := s)
  set s1 := (Memory.spec 0).clientState s (bufDeleteGenProg (((cp, base), oldEp), rKey))
  set tr' := bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf oldEp) rKey
  set fs1 : FastState := { fs with buf := Function.update fs.buf oldEp tr' }
  obtain ⟨hwl_mc, hwl_vp, hwl_step⟩ :=
    writeFastLocGenProg_fastStep (fs := fs1) henv hb hloc (by decide : 1 < 4)
      hbd_step.2.1 hbd_step.2.2.1 (s := s1)
  dsimp only
  unfold stage3ClearActiveProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (rKeyAtGenProg (((mkWhpParams c U V w n_max, base), b), loc) >>= fun rk =>
        bufDeleteGenProg (((cp, base), oldEp), rk) >>= fun _ =>
        writeFastLocGenProg ((((cp, base), b), loc), 1)) =
      (Memory.spec 0).clientState s1 (writeFastLocGenProg ((((cp, base), b), loc), 1)) := by
    rw [clientState_bind, hrk_st, hrk_res, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, hbd_step.trans hwl_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrk_st, hrk_res]
    dsimp only [s1, cp, rKey] at hrk_mc hbd_mc hwl_mc ⊢; omega
  · refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res]
    exact validProg_bind hbd_vp hwl_vp

/-- Advance Stage 3 cursor and transition to Stage 4 if `ia ≤ nextCur`
(`d = ((base, ia), nextCur)`). -/
@[irreducible] private def stage3AdvanceProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((base, ia), nextCur) => do
    let z4 ← pure 4
    writeHdrProg ((base, hdrStageCursor), nextCur)
    if ia ≤ nextCur then
      writeHdrProg ((base, hdrRebStage), z4)
    else
      pure ()

private theorem realizes_stage3Advance :
    Realizes .exact stage3AdvanceProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((base, _), _) _ => 3 ≤ w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold stage3AdvanceProg
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨⟨base, ia⟩, nextCur⟩
    obtain ⟨h3w, hfit32⟩ := h
    have h8 : 8 ≤ 2 ^ w := (by decide : 8 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right two_pos h3w)
    first
    | (change 4 < 2 ^ w; omega)
    | exact hfit32.of_le (by dsimp [hdrStageCursor, hdrRebStage]; omega)
  )

private theorem stage3AdvanceProg_fastStep {c U V w n_max base ia nextCur : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcur_fit : Fits w nextCur)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage3AdvanceProg ((base, ia), nextCur)
    let s' := (Memory.spec 0).clientState s prog
    let fs1 : FastState := { fs with stageCursor := nextCur }
    let fsOut : FastState := if ia ≤ nextCur then { fs1 with rebStage := 4 } else fs1
    memoryCost prog s ≤ 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsOut s s' := by
  have h1 := writeHdrStep (fs := fs) henv (by dsimp [hdrStageCursor]; decide) hcur_fit
    (fun h6 => by dsimp [hdrStageCursor] at h6; omega) hseed hrep
    (hdrOff := hdrStageCursor) (val := nextCur)
  dsimp only
  unfold stage3AdvanceProg; simp only [pure_bind]
  by_cases hdone : ia ≤ nextCur
  · rw [ite_eq_left hdone, ite_eq_left hdone]
    have h2 := thenWriteHdr (hdrOff := hdrRebStage) (val := 4) henv
      (by dsimp [hdrRebStage]; decide) (henv.fits_const (by decide))
      (fun h6 => by dsimp [hdrRebStage] at h6; omega) h1
    exact ⟨h2.1, h2.2.1, h2.2.2⟩
  · rw [ite_eq_right hdone, ite_eq_right hdone]
    refine ⟨?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
      have := h1.1; omega
    · exact validProg_bind h1.2.1 (validProg_pure _)
    · rw [clientState_bind, clientState_pure_whp]; exact h1.2.2

/-- Execute Stage 3 of `epochTick` (`d = (wp, base)`). -/
@[irreducible] def epochTickStage3GenProg :
    WhpParams × ℕ → Memory.Prog Unit
  | (wp, base) => do
    let z1 ← pure 1
    let z4 ← pure 4
    let oldEp ← readOldEpProg base
    let allocs ← readBufAllocsProg (base, oldEp)
    let ia ← pure allocs.2
    let sc ← readHdrProg (base, hdrStageCursor)
    if sc < ia then
      let cs ← bufCheckSlotGenProg (((wp.1, base), oldEp), sc)
      let nextCur ← pure (sc + 1)
      if cs.1 = z1 then
        stage3ClearActiveProg (((wp, base), oldEp), cs.2)
        stage3AdvanceProg ((base, ia), nextCur)
      else
        stage3AdvanceProg ((base, ia), nextCur)
    else
      writeHdrProg ((base, hdrRebStage), z4)

/-- `Realizes .exact` certificate for `epochTickStage3GenProg`. -/
theorem realizes_epochTickStage3Gen :
    Realizes .exact epochTickStage3GenProg
      (WordEncoding.encode (α := WhpParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (wp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          CoreFastInv c U V n_max θ fs dict ∧
          fs.rebStage = 3)
      (fun _ _ => 0) := by
  unfold epochTickStage3GenProg
  have hro := realizes_readOldEp
  have hra := realizes_readBufAllocs
  have hrh := realizes_readHdr
  have hcs := realizes_bufCheckSlotGen
  have hca := realizes_stage3ClearActive
  have had := realizes_stage3Advance
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨wp, base⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hcore, hs3⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h3w := henv.three_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hcore.curEp_or with h01 | h01 <;> simp [FastState.oldEp, h01]
    have hbo := hcore.bufOld_valid
    rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
    obtain ⟨hia_o, _, oldMap, hv_o, hrel_o⟩ := hbo
    have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    have hr := stageCursorReads_spec henv hcore.curEp_or hold_or hrep (s := s)
    obtain ⟨hcs_st, hcs_res, _, _⟩ :=
      bufCheckSlotGenProg_spec henv hold_or (hrep.buf_rep hold_or) hv_o
        (id := fs.stageCursor) (s := s)
    simp only [hcp_eq] at *
    simp only [hr.ro_st, hr.ro_res, hr.ra_st, hr.ra_res, hr.sc_st, hr.sc_res, hcs_st] at *
    first
    | exact h3w
    | exact h2w
    | exact henv.2.1
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrCurEp, hdrStageCursor, hdrRebStage]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, fs.buf fs.oldEp, oldMap, henv, rfl, hold_or,
        hrep.buf_rep hold_or, hv_o⟩
    | (cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
       | none =>
         rw [hchk] at hcs_res
         have hhit : ((Memory.spec 0).clientResult s
           (bufCheckSlotGenProg (((mkWhpCoreParams c U V w n_max, base), fs.oldEp),
             fs.stageCursor))).1 = 1 := by assumption
         rw [hcs_res] at hhit; cases hhit
       | some p =>
         rcases p with ⟨b₀, loc₀⟩
         rw [hchk] at hcs_res
         obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
         obtain ⟨hb₀, hloc_b, _, _⟩ := (hrel_o.2 k b₀ loc₀).mp hmk
         have hloc₀ : loc₀ < totalLocalCoordsWhp n_max :=
           hloc_b.trans_le (hcore.bktCount_le b₀ hb₀)
         have hbp₀ : capFrontWhp n_max ≤ loc₀ →
             fs.backPtr b₀ (loc₀ - capFrontWhp n_max) < poolSizeWhp n_max :=
           fun hcf => (hcore.backPtr_valid b₀ hb₀ _ (by omega)).1
         rw [hcs_res]; dsimp only
         exact ⟨c, U, V, w, n_max, θ, fs, oldMap, henv, rfl, hseed, hrep, hold_or, hv_o,
           fun idx => (hcore.qv_global idx).1, hb₀, hloc₀, hbp₀⟩)
  )

/-- `FastStateStep` specification for `epochTickStage3GenProg`. -/
theorem epochTickStage3GenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcore : CoreFastInv c U V n_max θ fs dict)
    (hs3 : fs.rebStage = 3)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := epochTickStage3GenProg (mkWhpParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 2 * cTabWhp c + hashEvalCostWhp c + 40 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (epochTickStage3 c U n_max θ fs) s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hcore.curEp_or with h | h <;> simp [FastState.oldEp, h]
  have hbo := hcore.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_o, _, oldMap, hv_o, hrel_o⟩ := hbo
  have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  have hr := stageCursorReads_spec henv hcore.curEp_or hold_or hrep (s := s)
  dsimp only
  unfold epochTickStage3GenProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  simp only [pure_bind]
  dsimp only [epochTickStage3]
  set oldTr := fs.buf fs.oldEp
  by_cases hlt : fs.stageCursor < oldTr.itemAlloc
  · rw [ite_eq_left hlt]
    obtain ⟨hcs_st, hcs_res, hcs_mc, hcs_vp⟩ :=
      bufCheckSlotGenProg_spec henv hold_or (hrep.buf_rep hold_or) hv_o
        (id := fs.stageCursor) (s := s)
    have hcur1_fit : Fits w (fs.stageCursor + 1) := henv.fits_of_le_n_max (by omega)
    set kSlot : ℕ × (ℕ × ℕ) → Memory.Prog Unit := fun cs =>
      let tail := stage3AdvanceProg ((base, oldTr.itemAlloc), fs.stageCursor + 1)
      if cs.1 = 1 then
        stage3ClearActiveProg (((mkWhpParams c U V w n_max, base), fs.oldEp), cs.2) >>=
          fun _ => tail
      else tail
    cases hchk : bufCheckSlot oldTr fs.stageCursor with
    | some p =>
      rcases p with ⟨b₀, loc₀⟩
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
      obtain ⟨hb₀, hloc_b, _, _⟩ := (hrel_o.2 k b₀ loc₀).mp hmk
      have hloc₀ : loc₀ < totalLocalCoordsWhp n_max := hloc_b.trans_le (hcore.bktCount_le b₀ hb₀)
      have hbp₀ : capFrontWhp n_max ≤ loc₀ →
          fs.backPtr b₀ (loc₀ - capFrontWhp n_max) < poolSizeWhp n_max :=
        fun hcf => (hcore.backPtr_valid b₀ hb₀ _ (by omega)).1
      obtain ⟨hca_mc, hca_vp, hca_step⟩ :=
        stage3ClearActiveProg_fastStep henv hold_or hv_o hb₀ hloc₀ hbp₀ hseed hrep (s := s)
      set rKey := fs.rKeyAt c U n_max θ b₀ loc₀
      set tr' := bufDelete (cTabWhp c) (bCharWhp n_max) oldTr rKey
      set fs_ca : FastState :=
        { fs with
          buf := Function.update fs.buf fs.oldEp tr'
          locState := Function.update fs.locState b₀ (Function.update (fs.locState b₀) loc₀ 1) }
      have hia_upd :
          (Function.update fs.buf fs.oldEp tr' fs.oldEp).itemAlloc = oldTr.itemAlloc := by
        rw [Function.update_self]
        exact (bufDelete_allocs (cTabWhp c) (bCharWhp n_max) oldTr rKey).2
      obtain ⟨had_mc, had_vp, had_step⟩ := stage3AdvanceProg_fastStep (fs := fs_ca) henv
        hcur1_fit hca_step.2.1 hca_step.2.2.1 (ia := oldTr.itemAlloc)
        (nextCur := fs.stageCursor + 1)
        (s := (Memory.spec 0).clientState s
          (stage3ClearActiveProg (((mkWhpParams c U V w n_max, base), fs.oldEp), (b₀, loc₀))))
      rw [hia_upd]
      refine stageSlotCheckSeq_fastStep (kSlot := kSlot)
        (midCost := 2 * cTabWhp c + hashEvalCostWhp c + 17) (tailCost := 2)
        hr hlt ?_ hcs_st hcs_res hcs_mc hcs_vp ?_
        hca_mc hca_vp hca_step had_mc had_vp had_step (by omega)
      · rfl
      · dsimp only [kSlot, oldTr]; simp
    | none =>
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      obtain ⟨had_mc, had_vp, had_step⟩ := stage3AdvanceProg_fastStep (fs := fs) henv
        hcur1_fit hseed hrep (ia := oldTr.itemAlloc) (nextCur := fs.stageCursor + 1) (s := s)
      refine stageSlotCheckSeq_fastStep (kSlot := kSlot) (fsMid := fs) (pMid := pure ())
        (midCost := 0) (tailCost := 2) hr hlt ?_ hcs_st hcs_res hcs_mc hcs_vp ?_
        (by simp) (validProg_pure ()) (FastStateStep.refl hseed hrep)
        had_mc had_vp had_step (by omega)
      · rfl
      · simp [kSlot, oldTr, zero_ne_one, pure_bind]
  · rw [ite_eq_right hlt]
    obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrStep (fs := fs) henv
      (by dsimp [hdrRebStage]; decide) (henv.fits_const (by decide))
      (fun h6 => by dsimp [hdrRebStage] at h6; omega) hseed hrep
      (hdrOff := hdrRebStage) (val := 4) (s := s)
    refine stageCursorPrefix_ge_fastStep (tailCost := 1)
      hr hlt ?_ hw_mc hw_vp hw_step (by omega)
    rfl

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

end
