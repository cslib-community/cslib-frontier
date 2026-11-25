/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.Witness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Active-Epoch Migration Arena Growth and Rightward Item Shift (`migrateSetupShiftCode`)

Internal second half of `migrateSetupCode`: grows `[x.frontier, peakF)` with zeroed words, shifts
the compacted old item region rightward to `mOldItemDst` (`copyRightwardProg`), writes the new
epoch header/parameters at `mNewMeta`, and prepares `mHashBase = mNewMeta + 225`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise
open Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
open Cslib.Probability
open scoped BigOperators ENNReal

/-- Second half of `migrateSetupCode`: grows `[x.frontier, peakF)` with zeroed words, shifts old
items rightward to `mOldItemDst`, writes new header/params at `mNewMeta`, and sets `mHashBase`. -/
noncomputable def migrateSetupShiftCode : RCode .exact rResize :=
  .seq (growZeroCode mK mRes mCur mIdx mZero mOne) <|
  .seq (.op (.copy mFr mPeakFront)) <|
  .seq (RCode.ofCode (wCopyRight.code mFr srcCopyRight tmpCopyRight)) <|
  .seq (.op (.copy mTmpA mNewMeta)) <|
  .seq (RCode.ofCode (wWriteParams.code mFr srcWriteParams tmpWriteParams)) <|
  .seq (.op (.const mCur 225))
       (.op (.exactBin .add mHashBase mNewMeta mCur))

theorem not_readsWidth_migrateSetupShiftCode : ¬migrateSetupShiftCode.ReadsWidth := by
  simp [migrateSetupShiftCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    growZeroCode_not_readsWidth]

theorem migrateSetupShiftCode_exec {U V w N_old n n_init base : ℕ}
    {θ_old : QuotHashSeed U N_old} {s_abs : Dictionary.State U} {x s₈ : RData rResize}
    (hn : 1 ≤ n) (hev : EpochValid U n N_old)
    (hfr : x.frontier = base + compactedEpochWords U V w N_old n)
    (hfit_peak : Fits w (base + migratePeakWords U V w N_old n))
    (hs₈b : s₈.Bounded w) (hs₈f : s₈.frontier = x.frontier)
    (habi₈ : abiPreserved x s₈)
    (hbelow₈ : ∀ addr < base, s₈.mem addr = x.mem addr)
    (hsplit₈ : CompactedSplitRep base (base + offCompItems U w N_old) U V w N_old n n_init θ_old
      s_abs ⟨s₈.mem, s₈.frontier⟩)
    (hs₈_base : s₈.regs mBase = base)
    (hs₈_cnt : s₈.regs mCnt = n)
    (hs₈_nn : s₈.regs mNNew = targetCap U n)
    (hs₈_nm : s₈.regs mNewMeta = base + offCompItems U w N_old)
    (hs₈_off : s₈.regs mOffNew = offCompItems U w (targetCap U n))
    (hs₈_iwo : s₈.regs mIwOld = compactedItemWords U V w N_old n)
    (hs₈_iwn : s₈.regs mIwNew = compactedItemWords U V w (targetCap U n) n)
    (hs₈_ar : s₈.regs mArena = base + offCompItems U w N_old + offCompItems U w (targetCap U n))
    (hs₈_pf : s₈.regs mPeakFront = base + migratePeakWords U V w N_old n)
    (hs₈_k : s₈.regs mK = (base + migratePeakWords U V w N_old n) - x.frontier)
    (hs₈_oid : s₈.regs mOldItemDst =
      (base + offCompItems U w N_old + offCompItems U w (targetCap U n)) +
        (migrateArenaWords U V w N_old (targetCap U n) n - compactedItemWords U V w N_old n))
    (hs₈_ohp : ∀ i : Fin 19, s₈.regs (mOldHp i) =
      mkHashParams w (epochQBits U N_old) (epochHashB N_old) (totalMicroBits N_old) 3 i)
    (hs₈_ocp : ∀ i : Fin 36, s₈.regs (mOldCp i) = mkCompParams U V w N_old i)
    (hs₈_nhp : ∀ i : Fin 19, s₈.regs (mNewHp i) =
      mkHashParams w (epochQBits U (targetCap U n)) (epochHashB (targetCap U n))
        (totalMicroBits (targetCap U n)) 3 i)
    (hs₈_ncp : ∀ i : Fin 36, s₈.regs (mNewCp i) = mkCompParams U V w (targetCap U n) i) :
    let N_new := targetCap U n
    let newMeta := base + offCompItems U w N_old
    let offNew := offCompItems U w N_new
    let iwOld := compactedItemWords U V w N_old n
    let iwNew := compactedItemWords U V w N_new n
    let arenaW := migrateArenaWords U V w N_old N_new n
    let arenaB := newMeta + offNew
    let peakF := base + migratePeakWords U V w N_old n
    ∃ (y : RData rResize) (steps_s : ℕ),
      RDemonicExec w peakF migrateSetupShiftCode s₈ steps_s (· = y) ∧
      steps_s ≤ (132 * migFactor + 12050) * n ∧
      y.Bounded w ∧
      y.frontier = peakF ∧
      abiPreserved x y ∧
      (∀ addr < base, y.mem addr = x.mem addr) ∧
      RootHeaderValid U V w N_new n n newMeta y.mem ∧
      EpochParamsStored U V w N_new newMeta y.mem ∧
      ReducedKWise.Rep (base + epochHdrWords) w (qBits U N_old) (hashB N_old)
        (totalMicroBits N_old) 3 θ_old y.mem ∧
      (∃ s_fix_old : Memory.State,
        DictStateInv U V (ghostW w) N_old 0 θ_old s_abs s_fix_old ∧
        totalSlots N_old (compGmAt base U w N_old y.mem) = n ∧
        FixedCoupled base (arenaB + (arenaW - iwOld)) U V w N_old s_fix_old ⟨y.mem, y.frontier⟩) ∧
      y.regs mBase = base ∧
      y.regs mCnt = n ∧
      y.regs mFr = peakF ∧
      y.regs mNewMeta = newMeta ∧
      y.regs mOffNew = offNew ∧
      y.regs mIwNew = iwNew ∧
      y.regs mArena = arenaB ∧
      y.regs mPeakFront = peakF ∧
      y.regs mOldItemDst = arenaB + (arenaW - iwOld) ∧
      y.regs mHashBase = newMeta + epochHdrWords ∧
      (∀ i : Fin 19, y.regs (mOldHp i) =
        mkHashParams w (epochQBits U N_old) (epochHashB N_old) (totalMicroBits N_old) 3 i) ∧
      (∀ i : Fin 36, y.regs (mOldCp i) = mkCompParams U V w N_old i) ∧
      (∀ i : Fin 19, y.regs (mNewHp i) =
        mkHashParams w (epochQBits U N_new) (epochHashB N_new) (totalMicroBits N_new) 3 i) ∧
      (∀ i : Fin 36, y.regs (mNewCp i) = mkCompParams U V w N_new i) := by
  intro N_new newMeta offNew iwOld iwNew arenaW arenaB peakF
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hs₈b hsplit₈.root_hdr
  have hNU_old : N_old ≤ U := by rcases hev with ⟨rfl, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  have hn_old : n ≤ N_old := by rcases hev with ⟨rfl, _⟩ | ⟨_, hnN, _, _⟩ <;> omega
  have hnU : n ≤ U := hn_old.trans hNU_old
  obtain ⟨hN_new_pos, hn_new, hN_new_2n, hNU_new⟩ := targetCap_bounds_of_pos hn hnU
  have hce_old : compactedEpochWords U V w N_old n = offCompItems U w N_old + iwOld := by
    unfold compactedEpochWords; rw [ite_eq_right (by omega)]
  have h225_old : 225 ≤ offCompItems U w N_old := le_offCompItems_225 U w N_old
  have h225_new : 225 ≤ offNew := le_offCompItems_225 U w N_new
  have hpeak_raw : base + migratePeakWords U V w N_old n = arenaB + arenaW := by
    unfold migratePeakWords
    dsimp only [arenaB, arenaW, newMeta, offNew, N_new, iwOld, iwNew]
    ring
  have hpeak_eq : peakF = arenaB + arenaW := hpeak_raw
  have hfit_ar : Fits w (arenaB + arenaW) := hpeak_raw ▸ hfit_peak
  have hiwo_le_aw : iwOld ≤ arenaW := (le_max_left _ _).trans (Nat.le_add_right _ 6)
  have hfr_le_peak : x.frontier ≤ peakF := by
    rw [hfr, hce_old, hpeak_eq]; dsimp only [arenaB, newMeta]
    linarith only [hiwo_le_aw]
  have hfit1 : Fits w 1 := hfit_ar.of_le (by dsimp only [arenaB]; linarith only [h225_new])
  have hfit225 : Fits w 225 := hfit_ar.of_le (by dsimp only [arenaB]; linarith only [h225_new])
  have hfit_n : Fits w n := hsplit₈.root_hdr.fits_U.of_le hnU
  -- 7. `growZeroCode` + `mFr := mPeakFront`
  have hsum_grow : s₈.frontier + s₈.regs mK = peakF := by
    rw [hs₈f, hs₈_k]; exact Nat.add_sub_of_le hfr_le_peak
  have hex_gz := growZeroCode_exec (w := w) (L_peak := peakF)
    (count := mK) (result := mRes) (cur := mCur) (idx := mIdx) (zero := mZero) (one := mOne)
    hs₈b mGrow_nodup hfit1 hsum_grow.le (hsum_grow ▸ hfit_peak)
  rw [hs₈_k] at hex_gz
  set s₉ := growZeroPost mK mRes mCur mIdx mZero mOne s₈
  have hs₉b : s₉.Bounded w := growZeroPost_bounded hs₈b hfit1 (hsum_grow ▸ hfit_peak)
  have hs₉m_eq : s₉.mem = s₈.mem := rfl
  have hs₉f_eq : s₉.frontier = peakF := hsum_grow
  have hs₉_keep8 : ∀ reg, reg ∉ ([mRes, mCur, mIdx, mZero, mOne] : List (Fin rResize)) →
      s₉.regs reg = s₈.regs reg := fun _ hreg => growZeroPost_regs_of_not_mem hreg
  set s₁₀ := s₉.set mFr peakF
  have hs₉_pf : s₉.regs mPeakFront = peakF := (hs₉_keep8 mPeakFront (by simp)).trans hs₈_pf
  have hex_fr10 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := peakF)
    (d := mFr) (s := mPeakFront) (x := s₉) hs₉f_eq.le
  rw [hs₉_pf] at hex_fr10
  have hs₁₀b : s₁₀.Bounded w := hs₉b.set hfit_peak
  have hms₁₀ : memoryState mFr s₁₀.toData = ⟨s₈.mem, peakF⟩ :=
    Memory.State.ext hs₉m_eq (by simp [memoryState, s₁₀, RData.set])
  -- 8. `wCopyRight` shifting `[newMeta, newMeta + iwOld)` to `[oldItemDst, oldItemDst + iwOld)`
  let oldItemDst := arenaB + (arenaW - iwOld)
  have hdst_end : oldItemDst + iwOld = arenaB + arenaW := by
    dsimp only [oldItemDst]; rw [Nat.add_assoc, Nat.sub_add_cancel hiwo_le_aw]
  have hs₁₀_keep : ∀ reg, reg ≠ mFr →
      reg ∉ ([mRes, mCur, mIdx, mZero, mOne] : List (Fin rResize)) →
      s₁₀.regs reg = s₈.regs reg := fun reg h1 h =>
    (Function.update_of_ne h1 _ _).trans (hs₉_keep8 reg h)
  have hs₁₀_nm : s₁₀.regs mNewMeta = newMeta := (hs₁₀_keep _ (by simp) (by simp)).trans hs₈_nm
  have hs₁₀_oid : s₁₀.regs mOldItemDst = oldItemDst :=
    (hs₁₀_keep _ (by simp) (by simp)).trans hs₈_oid
  have hs₁₀_iwo : s₁₀.regs mIwOld = iwOld := (hs₁₀_keep _ (by simp) (by simp)).trans hs₈_iwo
  have hin_cr : s₁₀.regs ∘ srcCopyRight = WordEncoding.encode ((newMeta, oldItemDst), iwOld) :=
    (regs_pairSrc (regs_pairSrc (regs_reg1_eq mNewMeta hs₁₀_nm)
      (regs_reg1_eq mOldItemDst hs₁₀_oid)) (regs_reg1_eq mIwOld hs₁₀_iwo)).eq
  obtain ⟨hpre_cr, hv_cr, hc_cr, hfr_cr, hcp_cr, hout_cr⟩ :=
    copyRightwardProg_spec (w := w) (srcBase := newMeta) (dstBase := oldItemDst) (len := iwOld)
      (s₀ := ⟨s₈.mem, peakF⟩) (fun a _ => hs₈b.mem_fits a)
      (by dsimp only [oldItemDst, arenaB]; linarith only [h225_new])
      (by change oldItemDst + iwOld ≤ peakF; rw [hdst_end, hpeak_eq]) hfit1
  obtain ⟨s₁₁, hex_cr, hs₁₁b, hs₁₁f, hm_cr, _, hframe_reg_cr⟩ :=
    execWitness wCopyRight factor_wCopyRight_le mFr srcCopyRight tmpCopyRight
      tmpCopyRight_inj srcCopyRight_ne_tmp tmpCopyRight_ne_mFr srcCopyRight_ne_mFr
      ((newMeta, oldItemDst), iwOld) hs₁₀b hs₉f_eq.le
      hin_cr (hms₁₀ ▸ hpre_cr) (hms₁₀ ▸ hv_cr)
      (by rw [hms₁₀, hfr_cr]; exact hs₉f_eq.symm.le)
  rw [hms₁₀] at hm_cr hex_cr
  have hs₁₁f_eq : s₁₁.frontier = peakF := hs₁₁f.trans hs₉f_eq
  have hs₁₁_fr_reg : s₁₁.regs mFr = peakF :=
    (congrArg Memory.State.frontier hm_cr).trans hfr_cr
  have hs₁₁_mem_eq : s₁₁.mem = ((Memory.spec 0).clientState ⟨s₈.mem, peakF⟩
      (copyRightwardProg ((newMeta, oldItemDst), iwOld))).mem :=
    congrArg Memory.State.mem hm_cr
  have hs₁₁_keep10 : ∀ reg, reg ≠ mFr → reg.val < 160 → s₁₁.regs reg = s₁₀.regs reg :=
    fun reg h1 h160 => hframe_reg_cr reg h1 (mkTmp_ne_reg _ h160 (fun a => Fin.elim0 a))
  -- 9. `mTmpA := mNewMeta; wWriteParams` #2 at `dstMetaBase = newMeta`
  set s₁₂ := s₁₁.set mTmpA newMeta
  have hs₁₁_nm : s₁₁.regs mNewMeta = newMeta :=
    (hs₁₁_keep10 mNewMeta (mReg_ne (by decide)) (mReg_lt_160 _)).trans hs₁₀_nm
  have hex_cp12 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := peakF)
    (d := mTmpA) (s := mNewMeta) (x := s₁₁) hs₁₁f_eq.le
  rw [hs₁₁_nm] at hex_cp12
  have hfit_dst2 : Fits w (newMeta + offNew) := hfit_ar.of_le (Nat.le_add_right _ _)
  have hs₁₂b : s₁₂.Bounded w := hs₁₁b.set (hfit_dst2.of_le (Nat.le_add_right _ _))
  have hms₁₂ : memoryState mFr s₁₂.toData = ⟨s₁₁.mem, peakF⟩ :=
    Memory.State.ext rfl (by simp [memoryState, s₁₂, RData.set, RData.toData, hs₁₁_fr_reg])
  have hkeep_8_to_12 : ∀ reg : Fin rResize, reg.val < 160 →
      reg ∉ ([mFr, mTmpA, mRes, mCur, mIdx, mZero, mOne] : List (Fin rResize)) →
      s₁₂.regs reg = s₈.regs reg := fun reg h160 hnot => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    obtain ⟨hfr', hta, hres, hcur, hidx, hz, ho⟩ := hnot
    rw [← hs₁₀_keep reg hfr' (by simp [hres, hcur, hidx, hz, ho]), ← hs₁₁_keep10 reg hfr' h160]
    exact Function.update_of_ne hta _ _
  have hs₁₂_base : s₁₂.regs mBase = base :=
    (hkeep_8_to_12 _ (mReg_lt_160 _) (by simp)).trans hs₈_base
  have hs₁₂_cnt : s₁₂.regs mCnt = n := (hkeep_8_to_12 _ (mReg_lt_160 _) (by simp)).trans hs₈_cnt
  have hs₁₂_nn : s₁₂.regs mNNew = N_new := (hkeep_8_to_12 _ (mReg_lt_160 _) (by simp)).trans hs₈_nn
  have hin_wp2 : s₁₂.regs ∘ srcWriteParams =
      WordEncoding.encode (((base, newMeta), (N_new, (n, n)))) := by
    refine (regs_pairSrc
      (regs_pairSrc (regs_reg1_eq mBase hs₁₂_base)
        (regs_reg1_eq mTmpA (by simp [s₁₂, RData.set])))
      (regs_pairSrc (regs_reg1_eq mNNew hs₁₂_nn)
        (regs_pairSrc (regs_reg1_eq mCnt hs₁₂_cnt) (regs_reg1_eq mCnt hs₁₂_cnt)))).eq
  have hnm_le_oid : newMeta ≤ oldItemDst := by
    dsimp only [oldItemDst, arenaB]; linarith only [h225_new]
  have hhdr₁₁ : RootHeaderValid U V w N_old n n_init base s₁₁.mem :=
    rootHeaderValid_congr hsplit₈.root_hdr fun a ha => by
      rw [hs₁₁_mem_eq]
      exact hout_cr a (fun h => by
        dsimp only [newMeta] at hnm_le_oid
        linarith only [ha.2, h.1, h225_old, hnm_le_oid])
  obtain ⟨hpre_wp2, hv_wp2, hres_wp2, hfr_wp2, hhdr_wp2, hpar_wp2, hframe_wp2, hc_wp2⟩ :=
    writeEpochParamsGenProg_spec (s := ⟨s₁₁.mem, peakF⟩) (dstMetaBase := newMeta)
      (N := N_new) (n_cur := n) (n_init_new := n)
      hw hN_new_pos hNU_new hV hfit_n hfit_n hhdr₁₁
      (by
        change base + 5 ≤ peakF
        rw [hpeak_eq]; dsimp only [arenaB, newMeta]; linarith only [h225_old])
      (by change newMeta + 63 ≤ peakF; rw [hpeak_eq]; dsimp only [arenaB]; linarith only [h225_new])
      hfit_dst2
  obtain ⟨s₁₃, hex_wp2, hs₁₃b, hs₁₃f, hm_wp2, hout_wp2, hframe_reg_wp2⟩ :=
    execWitness wWriteParams factor_wWriteParams_le mFr srcWriteParams tmpWriteParams
      tmpWriteParams_inj srcWriteParams_ne_tmp tmpWriteParams_ne_mFr srcWriteParams_ne_mFr
      ((base, newMeta), (N_new, (n, n))) hs₁₂b hs₁₁f_eq.le
      hin_wp2 (hms₁₂ ▸ hpre_wp2) (hms₁₂ ▸ hv_wp2)
      (by rw [hms₁₂, hfr_wp2]; exact hs₁₁f_eq.symm.le)
  rw [hms₁₂] at hm_wp2 hout_wp2 hex_wp2
  rw [hres_wp2] at hout_wp2
  have hs₁₃f_eq : s₁₃.frontier = peakF := hs₁₃f.trans hs₁₁f_eq
  have hs₁₃_fr_reg : s₁₃.regs mFr = peakF :=
    (congrArg Memory.State.frontier hm_wp2).trans hfr_wp2
  have hs₁₃_off : s₁₃.regs mOffNew = offNew := by
    have h0 := hout_wp2 0; rwa [tmpWriteParams_out_0] at h0
  have hs₁₃_mem_eq : s₁₃.mem = ((Memory.spec 0).clientState ⟨s₁₁.mem, peakF⟩
      (writeEpochParamsGenProg ((base, newMeta), (N_new, (n, n))))).mem :=
    congrArg Memory.State.mem hm_wp2
  have hs₁₃_keep12 : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mOffNew → reg ≠ mHSpaceNew →
      s₁₃.regs reg = s₁₂.regs reg := fun reg h1 h160 ho hh =>
    hframe_reg_wp2 reg h1
      (mkTmp_ne_reg _ h160 (fun a => by fin_cases a <;> [exact ho.symm; exact hh.symm]))
  -- 10. `mCur := 225; mHashBase := mNewMeta + mCur`
  set s₁₄ := s₁₃.set mCur 225
  have hex_c225 := RDemonicExec.const (B := .exact) (d := mCur) (v := 225) (x := s₁₃)
    hs₁₃f_eq.le hfit225
  set y := s₁₄.set mHashBase (newMeta + epochHdrWords)
  have hs₁₃_nm : s₁₃.regs mNewMeta = newMeta :=
    (hs₁₃_keep12 mNewMeta (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
      (mReg_ne (by decide))).trans (by simp [s₁₂, RData.set, hs₁₁_nm])
  have hfit_hb : Fits w (newMeta + epochHdrWords) :=
    hfit_dst2.of_le (by unfold epochHdrWords; linarith only [h225_new])
  have hex_hb := RDemonicExec.exactBin (f := .add) (d := mHashBase) (i := mNewMeta) (j := mCur)
    (w := w) (L_peak := peakF) (x := s₁₄) hs₁₃f_eq.le (v := newMeta + epochHdrWords)
    (by
      change some (s₁₄.regs mNewMeta + s₁₄.regs mCur) = some (newMeta + 225)
      simp [s₁₄, RData.set, hs₁₃_nm])
    hfit_hb
  have hyb : y.Bounded w := (hs₁₃b.set hfit225).set hfit_hb
  have hyf : y.frontier = peakF := hs₁₃f_eq
  have hym : y.mem = s₁₃.mem := rfl
  have hold_meta_eq : ∀ a, base + epochHdrWords ≤ a ∧ a < newMeta → y.mem a = s₈.mem a :=
    fun a ha => by
      rw [hym, hs₁₃_mem_eq,
        hframe_wp2 a (fun h => by linarith only [ha.2, h.1]), hs₁₁_mem_eq]
      exact hout_cr a (fun h => by linarith only [ha.2, h.1, hnm_le_oid])
  have hold_item_eq : ∀ j < iwOld, y.mem (oldItemDst + j) = s₈.mem (newMeta + j) :=
    fun j hj => by
      rw [hym, hs₁₃_mem_eq,
        hframe_wp2 (oldItemDst + j) (fun h => by
          unfold offScratch at h; dsimp only [oldItemDst, arenaB] at h
          linarith only [h.2, h225_new]),
        hs₁₁_mem_eq]
      exact hcp_cr j hj
  have hrep_old_y : ReducedKWise.Rep (base + epochHdrWords) w (qBits U N_old) (hashB N_old)
      (totalMicroBits N_old) 3 θ_old y.mem := by
    have hlm : offCompLM U w N_old ≤ offCompItems U w N_old := by
      unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
    refine ⟨ReducedKWise.tableRep_congr hsplit₈.hash_rep.1 fun a h₁ h₂ =>
        (hold_meta_eq a ⟨h₁, ?_⟩).symm,
      ReducedKWise.seedRep_congr (w := w) hsplit₈.hash_rep.2 fun a h₁ h₂ =>
        (hold_meta_eq a ⟨h₁, ?_⟩).symm⟩
    all_goals dsimp only [newMeta, offCompLM, epochHdrWords, epochHashSpace, epochQBits,
      epochHashB, qBits, hashB] at hlm h₂ ⊢
    all_goals linarith only [h₂, hlm]
  obtain ⟨s_fix_old, hinv_old, htot_old, hcpl_old⟩ := hsplit₈.coupled
  have hlm_old_ge : epochHdrWords ≤ offCompLM U w N_old := Nat.le_add_right _ _
  obtain ⟨hcpl_old_y, hgm_old_y⟩ := fixedCoupled_of_shift (s₀ := ⟨s₈.mem, s₈.frontier⟩)
    (s₁ := ⟨y.mem, y.frontier⟩) (dstItemBase := oldItemDst) hw hcpl_old htot_old
    (fun a ha => hold_meta_eq a ⟨by linarith only [ha.1, hlm_old_ge], ha.2⟩) hold_item_eq
  have hkeep_8_to_y : ∀ reg : Fin rResize, reg.val < 160 →
      reg ∉ ([mFr, mTmpA, mRes, mCur, mIdx, mZero, mOne, mOffNew, mHSpaceNew, mHashBase] :
        List (Fin rResize)) →
      y.regs reg = s₈.regs reg := fun reg h160 hnot => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    obtain ⟨hfr', hta, hres, hcur, hidx, hz, ho, hoff, hhs, hhb⟩ := hnot
    rw [← hkeep_8_to_12 reg h160 (by simp [hfr', hta, hres, hcur, hidx, hz, ho]),
      ← hs₁₃_keep12 reg hfr' h160 hoff hhs]
    exact (Function.update_of_ne hhb _ _).trans (Function.update_of_ne hcur _ _)
  have hky : ∀ reg : Fin rResize, 16 ≤ reg.val ∧ reg.val < 150 → y.regs reg = s₈.regs reg :=
    fun reg h => hkeep_8_to_y reg (by omega) (by clear * - h; simp [Fin.ext_iff]; omega)
  have hpeak_lin := migratePeakWords_le_linear (V := V) hw hsplit₈.root_hdr.fits_U hV hn hev
  have hiwo_lin := compactedItemWords_le_linear (U := U) (V := V) (w := w) (N := N_old) (n := n)
    hw hU.le hV
  have hf1 := one_le_migFactor
  have hc_cr_mul : migFactor * (memoryCost
      (copyRightwardProg ((newMeta, oldItemDst), iwOld)) ⟨s₈.mem, peakF⟩ + 1) ≤
      migFactor * (4 * n + 5) :=
    Nat.mul_le_mul_left migFactor (by dsimp only [iwOld] at hc_cr; linarith only [hc_cr, hiwo_lin])
  have hc_wp2_mul : migFactor * (memoryCost
      (writeEpochParamsGenProg ((base, newMeta), (N_new, (n, n)))) ⟨s₁₁.mem, peakF⟩ + 1) ≤
      migFactor * (22 * n + 101) :=
    Nat.mul_le_mul_left migFactor
      (by dsimp only [N_new] at hc_wp2; linarith only [hc_wp2, hN_new_2n])
  have hc_gz : 5 * (peakF - x.frontier) + 6 ≤ 7570 * n + 4436 := by
    have hsub : peakF - x.frontier ≤ migratePeakWords U V w N_old n := by
      rw [hfr]; dsimp only [peakF]
      rw [Nat.add_sub_add_left]; exact Nat.sub_le _ _
    linarith only [hsub, hpeak_lin]
  have hex_shift :=
    (hex_gz.mono hc_gz (fun _ h => h)).seq_eq (hex_fr10.seq_eq
      ((hex_cr.mono hc_cr_mul (fun _ h => h)).seq_eq (hex_cp12.seq_eq
        ((hex_wp2.mono hc_wp2_mul (fun _ h => h)).seq_eq
          (hex_c225.seq_eq hex_hb)))))
  refine ⟨y, _, hex_shift, by nlinarith only [hn, hf1], hyb, hyf, ?_, ?_,
    (hym.trans hs₁₃_mem_eq).symm ▸ hhdr_wp2, (hym.trans hs₁₃_mem_eq).symm ▸ hpar_wp2, hrep_old_y,
    ⟨s_fix_old, hinv_old, (congrArg (totalSlots N_old) hgm_old_y).trans htot_old, hcpl_old_y⟩,
    ?_, ?_, ?_, hs₁₃_nm, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact abiPreserved_trans habi₈ (abiPreserved_of_lt_five fun r h5 hr =>
      hkeep_8_to_y r (by omega) (by clear * - h5 hr; simp [Fin.ext_iff] at hr ⊢; omega))
  · intro addr haddr
    rw [hym, hs₁₃_mem_eq,
      hframe_wp2 addr (fun h => by dsimp only [newMeta] at h; linarith only [haddr, h.1]),
      hs₁₁_mem_eq,
      hout_cr addr (fun h => by
        dsimp only [newMeta] at hnm_le_oid
        linarith only [haddr, h.1, hnm_le_oid])]
    exact hbelow₈ addr haddr
  · exact (hkeep_8_to_y mBase (mReg_lt_160 _) (by simp)).trans hs₈_base
  · exact (hkeep_8_to_y mCnt (mReg_lt_160 _) (by simp)).trans hs₈_cnt
  · simp [y, s₁₄, RData.set, hs₁₃_fr_reg]
  · simp [y, s₁₄, RData.set, hs₁₃_off]
  · exact (hkeep_8_to_y mIwNew (mReg_lt_160 _) (by simp)).trans hs₈_iwn
  · exact (hkeep_8_to_y mArena (mReg_lt_160 _) (by simp)).trans hs₈_ar
  · exact (hkeep_8_to_y mPeakFront (mReg_lt_160 _) (by simp)).trans hs₈_pf
  · exact (hkeep_8_to_y mOldItemDst (mReg_lt_160 _) (by simp)).trans hs₈_oid
  · simp [y, RData.set]
  · exact (hky _ (by simp only [val_mOldHp]; omega)).trans (hs₈_ohp i)
  · exact (hky _ (by simp only [val_mOldCp]; omega)).trans (hs₈_ocp i)
  · exact (hky _ (by simp only [val_mNewHp]; omega)).trans (hs₈_nhp i)
  · exact (hky _ (by simp only [val_mNewCp]; omega)).trans (hs₈_ncp i)


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
