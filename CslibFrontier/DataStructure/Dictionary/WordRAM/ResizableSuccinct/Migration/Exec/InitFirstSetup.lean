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
# First-Epoch Initialization Parameter-Write and Arena-Growth Setup (`initFirstSetupCode`)

Internal deterministic setup half of `initFirstEpochCode` before `resampleHashCode`: computes
`N₁ = targetCap U 1`, grows `[base + 8, base + 63)` and writes first-epoch parameters, loads
`mNewHp` / `mNewCp`, evaluates `iw₁`, and grows to `base + compactedEpochWords U V w N₁ 1`.
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

private noncomputable def initFirstParamsCode : RCode .exact rResize :=
  .seq (.op (.const mCur 8)) <|
  .seq (.op (.exactBin .add mFr mBase mCur)) <|
  .seq (.op (.const mCnt 1)) <|
  .seq (RCode.ofCode (wTargetCap.code mFr srcTargetCap tmpTargetCap)) <|
  .seq (.op (.const mK 55)) <|
  .seq (growZeroCode mK mRes mCur mIdx mZero mOne) <|
  .seq (.op (.const mCur 63)) <|
  .seq (.op (.exactBin .add mFr mBase mCur)) <|
  .seq (.op (.copy mTmpA mBase)) <|
  .seq (RCode.ofCode (wWriteParams.code mFr srcWriteParams tmpWriteParams)) <|
  .seq (loadBlockUpTo mBase mCur mNewHp offHashParams 18 (by decide)) <|
  .seq (loadBlockUpTo mBase mCur mNewCp offCompParams 35 (by decide))
       (RCode.ofCode (wItemWords.code mFr srcNewIw tmpNewIw))

private noncomputable def initFirstGrowCode : RCode .exact rResize :=
  .seq (.op (.exactBin .add mItemBase mBase mOffNew)) <|
  .seq (.op (.exactBin .add mPeakFront mItemBase mIwNew)) <|
  .seq (.op (.exactBin .sub mK mPeakFront mFr)) <|
  .seq (growZeroCode mK mRes mCur mIdx mZero mOne) <|
  .seq (.op (.copy mFr mPeakFront)) <|
  .seq (.op (.const mCur 225))
       (.op (.exactBin .add mHashBase mBase mCur))

/-- Deterministic setup half of `initFirstEpochCode` before `resampleHashCode`. -/
noncomputable def initFirstSetupCode : RCode .exact rResize :=
  .seq initFirstParamsCode initFirstGrowCode


theorem not_readsWidth_initFirstSetupCode : ¬initFirstSetupCode.ReadsWidth := by
  have hb1 := not_readsWidth_loadBlockUpTo mBase mCur mNewHp offHashParams 18 (by decide)
  have hb2 := not_readsWidth_loadBlockUpTo mBase mCur mNewCp offCompParams 35 (by decide)
  simp [initFirstSetupCode, initFirstParamsCode, initFirstGrowCode,
    RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin, growZeroCode_not_readsWidth, hb1, hb2]

private theorem initFirstParamsCode_exec {U V w base : ℕ} {x : RData rResize}
    (hx : x.Bounded w)
    (hfr : x.frontier = base + 8)
    (hhdr : RootHeaderValid U V w 0 0 0 base x.mem)
    (hfit_peak : Fits w (base + compactedEpochWords U V w (targetCap U 1) 1))
    (hbase : x.regs mBase = base) :
    let N₁ := targetCap U 1
    let off₁ := offCompItems U w N₁
    let iw₁ := compactedItemWords U V w N₁ 1
    let fr₁ := base + compactedEpochWords U V w N₁ 1
    ∃ (s₁₀ : RData rResize) (steps_p : ℕ),
      RDemonicExec w fr₁ initFirstParamsCode x steps_p (· = s₁₀) ∧
      steps_p ≤ 126 * migFactor + 460 ∧
      s₁₀.Bounded w ∧
      s₁₀.frontier = base + 63 ∧
      abiPreserved x s₁₀ ∧
      (∀ addr < base, s₁₀.mem addr = x.mem addr) ∧
      RootHeaderValid U V w N₁ 1 1 base s₁₀.mem ∧
      EpochParamsStored U V w N₁ base s₁₀.mem ∧
      s₁₀.regs mBase = base ∧
      s₁₀.regs mFr = base + 63 ∧
      s₁₀.regs mOffNew = off₁ ∧
      s₁₀.regs mIwNew = iw₁ ∧
      (∀ i : Fin 19, s₁₀.regs (mNewHp i) =
        mkHashParams w (epochQBits U N₁) (epochHashB N₁) (totalMicroBits N₁) 3 i) ∧
      (∀ i : Fin 36, s₁₀.regs (mNewCp i) = mkCompParams U V w N₁ i) := by
  intro N₁ off₁ iw₁ fr₁
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hx hhdr
  obtain ⟨hN₁_pos, _, hN₁_le2, hN₁U⟩ := targetCap_bounds_of_pos (le_rfl : 1 ≤ 1) hhdr.pos_U
  have hce₁ : compactedEpochWords U V w N₁ 1 = off₁ + iw₁ := by
    unfold compactedEpochWords; simp [off₁, iw₁]
  have h225_le : 225 ≤ off₁ := le_offCompItems_225 U w N₁
  have hfr₁_eq : fr₁ = base + off₁ + iw₁ := by dsimp only [fr₁]; rw [hce₁, Nat.add_assoc]
  have hfit_off : Fits w (base + off₁) := hfit_peak.of_le (by rw [hce₁]; linarith only)
  have hfit225 : Fits w 225 := fits_const_of_offCompItems hfit_off le_rfl
  have hfit1 : Fits w 1 := hfit225.of_le (by decide)
  have hfr_le : x.frontier ≤ fr₁ := by rw [hfr, hfr₁_eq]; linarith only [h225_le]
  -- 1. `mCur := 8; mFr := mBase + mCur; mCnt := 1`
  set s₁ := x.set mCur 8
  have hex₁ := RDemonicExec.const (B := .exact) (d := mCur) (v := 8) (x := x) hfr_le
    (hfit225.of_le (by decide))
  set s₂ := s₁.set mFr (base + 8)
  have hex₂ := RDemonicExec.exactBin (f := .add) (d := mFr) (i := mBase) (j := mCur)
    (w := w) (L_peak := fr₁) (x := s₁) hfr_le (v := base + 8)
    (by simp [BinOp.evalExact, s₁, RData.set, hbase])
    (hfit_off.of_le (by linarith only [h225_le]))
  set s₃ := s₂.set mCnt 1
  have hex₃ := RDemonicExec.const (B := .exact) (d := mCnt) (v := 1) (x := s₂) hfr_le hfit1
  have hs₃b : s₃.Bounded w :=
    ((hx.set (hfit225.of_le (by decide))).set (hfit_off.of_le (by linarith only [h225_le]))).set
      hfit1
  have hms₃ : memoryState mFr s₃.toData = ⟨x.mem, x.frontier⟩ :=
    Memory.State.ext rfl (by
      dsimp only [memoryState, s₃, s₂, s₁, RData.set, RData.toData]
      rw [Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mCnt), Function.update_self]
      exact hfr.symm)
  have hin_tc : s₃.regs ∘ srcTargetCap = WordEncoding.encode (base, 1) :=
    (regs_pairSrc (regs_reg1_eq mBase (by simp [s₃, s₂, s₁, RData.set, hbase]))
      (regs_reg1_eq mCnt (by simp [s₃, RData.set]))).eq
  obtain ⟨hpre_tc, hv_tc, hst_tc, hres_tc, hc_tc⟩ :=
    computeTargetCapProg_spec (s := ⟨x.mem, x.frontier⟩) hhdr
      (by change base < x.frontier; rw [hfr]; omega) hhdr.pos_U hfit1
  obtain ⟨s₄, hex_tc, hs₄b, hs₄f, hm_tc, hout_tc, hframe_tc⟩ :=
    execWitness wTargetCap factor_wTargetCap_le mFr srcTargetCap tmpTargetCap
      tmpTargetCap_inj srcTargetCap_ne_tmp tmpTargetCap_ne_mFr srcTargetCap_ne_mFr
      (base, 1) hs₃b hfr_le hin_tc (hms₃ ▸ hpre_tc) (hms₃ ▸ hv_tc)
      (by rw [hms₃, hst_tc]; exact le_rfl)
  rw [hms₃, hst_tc] at hm_tc
  rw [hms₃, hres_tc] at hout_tc
  rw [hms₃] at hex_tc
  have hs₄m : s₄.mem = x.mem := congrArg Memory.State.mem hm_tc
  have hs₄f_eq : s₄.frontier = base + 8 := hs₄f.trans hfr
  have hs₄_nn : s₄.regs mNNew = N₁ := by
    have h0 := hout_tc 0; rwa [tmpTargetCap_out] at h0
  have hs₄_keep3 : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mNNew → s₄.regs reg = s₃.regs reg :=
    fun reg h1 h160 hnn =>
      hframe_tc reg h1 (mkTmp_ne_reg _ h160 (fun a => by fin_cases a; exact hnn.symm))
  -- 2. `mK := 55; growZeroCode` (`frontier = base + 63`)
  set s₅ := s₄.set mK 55
  have hex₅ := RDemonicExec.const (B := .exact) (L_peak := fr₁) (d := mK) (v := 55) (x := s₄)
    (hs₄f_eq.le.trans (by rw [hfr₁_eq]; linarith only [h225_le])) (hfit225.of_le (by decide))
  have hs₅b : s₅.Bounded w := hs₄b.set (hfit225.of_le (by decide))
  have hs₅_k : s₅.regs mK = 55 := by simp [s₅, RData.set]
  have hsum_55 : s₅.frontier + s₅.regs mK = base + 63 := by
    rw [show s₅.frontier = base + 8 from hs₄f_eq, hs₅_k]
  have h63_le : base + 63 ≤ fr₁ := by rw [hfr₁_eq]; linarith only [h225_le]
  have hfit_b63 : Fits w (base + 63) := hfit_off.of_le (by linarith only [h225_le])
  have hex_gz1 := growZeroCode_exec (w := w) (L_peak := fr₁)
    (count := mK) (result := mRes) (cur := mCur) (idx := mIdx) (zero := mZero) (one := mOne)
    hs₅b mGrow_nodup hfit1 (hsum_55.le.trans h63_le) (hsum_55 ▸ hfit_b63)
  rw [hs₅_k] at hex_gz1
  set s₆ := growZeroPost mK mRes mCur mIdx mZero mOne s₅
  have hs₆b : s₆.Bounded w := growZeroPost_bounded hs₅b hfit1 (hsum_55 ▸ hfit_b63)
  have hs₆m : s₆.mem = x.mem := hs₄m
  have hs₆f : s₆.frontier = base + 63 := hsum_55
  have hs₆_keep5 : ∀ reg, reg ∉ ([mRes, mCur, mIdx, mZero, mOne] : List (Fin rResize)) →
      s₆.regs reg = s₅.regs reg := fun _ hreg => growZeroPost_regs_of_not_mem hreg
  -- 3. `mCur := 63; mFr := mBase + mCur; mTmpA := mBase; wWriteParams`
  have hs₆_base : s₆.regs mBase = base :=
    (hs₆_keep5 mBase
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans <|
    (by simp [s₅, RData.set] : s₅.regs mBase = s₄.regs mBase).trans <|
    (hs₄_keep3 mBase (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
      (by simp [s₃, s₂, s₁, RData.set, hbase])
  set s₆a := s₆.set mCur 63
  have hex_6a := RDemonicExec.const (B := .exact) (d := mCur) (v := 63) (x := s₆)
    (hs₆f.le.trans h63_le) (hfit225.of_le (by decide))
  set s₆b := s₆a.set mFr (base + 63)
  have hex_6b := RDemonicExec.exactBin (f := .add) (d := mFr) (i := mBase) (j := mCur)
    (w := w) (L_peak := fr₁) (x := s₆a) (hs₆f.le.trans h63_le) (v := base + 63)
    (by simp [BinOp.evalExact, s₆a, RData.set, hs₆_base]) hfit_b63
  set s₆c := s₆b.set mTmpA base
  have hex_6c := RDemonicExec.copy (B := .exact) (w := w) (L_peak := fr₁)
    (d := mTmpA) (s := mBase) (x := s₆b) (hs₆f.le.trans h63_le)
  have hs₆b_base : s₆b.regs mBase = base := by simp [s₆b, s₆a, RData.set, hs₆_base]
  rw [hs₆b_base] at hex_6c
  have hs₆cb : s₆c.Bounded w :=
    ((hs₆b.set (hfit225.of_le (by decide))).set hfit_b63).set
      (hfit_b63.of_le (Nat.le_add_right _ _))
  have hms₆c : memoryState mFr s₆c.toData = ⟨x.mem, base + 63⟩ :=
    Memory.State.ext hs₆m (by
      dsimp only [memoryState, s₆c, s₆b, RData.set, RData.toData]
      rw [Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mTmpA), Function.update_self])
  have hs₆c_cnt : s₆c.regs mCnt = 1 := by
    dsimp only [s₆c, s₆b, s₆a, RData.set]
    rw [Function.update_of_ne (mReg_ne (by decide)),
      Function.update_of_ne (mReg_ne (by decide)),
      Function.update_of_ne (mReg_ne (by decide)),
      hs₆_keep5 mCnt (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)]
    dsimp only [s₅, RData.set]
    rw [Function.update_of_ne (mReg_ne (by decide)),
      hs₄_keep3 mCnt (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))]
    simp [s₃, RData.set]
  have hs₆c_nn : s₆c.regs mNNew = N₁ := by
    dsimp only [s₆c, s₆b, s₆a, RData.set]
    rw [Function.update_of_ne (mReg_ne (by decide)),
      Function.update_of_ne (mReg_ne (by decide)),
      Function.update_of_ne (mReg_ne (by decide)),
      hs₆_keep5 mNNew (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)]
    simp [s₅, RData.set, hs₄_nn]
  have hin_wp : s₆c.regs ∘ srcWriteParams =
      WordEncoding.encode (((base, base), (N₁, (1, 1)))) :=
    (regs_pairSrc
      (regs_pairSrc (regs_reg1_eq mBase (by simp [s₆c, s₆b, s₆a, RData.set, hs₆_base]))
        (regs_reg1_eq mTmpA (by simp [s₆c, RData.set])))
      (regs_pairSrc (regs_reg1_eq mNNew hs₆c_nn)
        (regs_pairSrc (regs_reg1_eq mCnt hs₆c_cnt) (regs_reg1_eq mCnt hs₆c_cnt)))).eq
  obtain ⟨hpre_wp, hv_wp, hres_wp, hfr_wp, hhdr_wp, hpar_wp, hframe_wp, hc_wp⟩ :=
    writeEpochParamsGenProg_spec (s := ⟨x.mem, base + 63⟩) (dstMetaBase := base)
      (N := N₁) (n_cur := 1) (n_init_new := 1)
      hw hN₁_pos hN₁U hV hfit1 hfit1 hhdr
      (by change base + 5 ≤ base + 63; omega) le_rfl hfit_off
  obtain ⟨s₇, hex_wp, hs₇b, hs₇f, hm_wp, hout_wp, hframe_reg_wp⟩ :=
    execWitness wWriteParams factor_wWriteParams_le mFr srcWriteParams tmpWriteParams
      tmpWriteParams_inj srcWriteParams_ne_tmp tmpWriteParams_ne_mFr srcWriteParams_ne_mFr
      ((base, base), (N₁, (1, 1))) hs₆cb (hs₆f.le.trans h63_le)
      hin_wp (hms₆c ▸ hpre_wp) (hms₆c ▸ hv_wp)
      (by rw [hms₆c, hfr_wp]; exact hs₆f.symm.le)
  rw [hms₆c] at hm_wp hout_wp hex_wp
  rw [hres_wp] at hout_wp
  have hs₇f_eq : s₇.frontier = base + 63 := hs₇f.trans hs₆f
  have hs₇_fr_reg : s₇.regs mFr = base + 63 :=
    (congrArg Memory.State.frontier hm_wp).trans hfr_wp
  have hs₇_off : s₇.regs mOffNew = off₁ := by
    have h0 := hout_wp 0; rwa [tmpWriteParams_out_0] at h0
  have hs₇_mem_eq : s₇.mem = ((Memory.spec 0).clientState ⟨x.mem, base + 63⟩
      (writeEpochParamsGenProg ((base, base), (N₁, (1, 1))))).mem :=
    congrArg Memory.State.mem hm_wp
  have hs₇_keep6c : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mOffNew → reg ≠ mHSpaceNew →
      s₇.regs reg = s₆c.regs reg := fun reg h1 h160 ho hh =>
    hframe_reg_wp reg h1
      (mkTmp_ne_reg _ h160 (fun a => by fin_cases a <;> [exact ho.symm; exact hh.symm]))
  -- 4. Load `mNewHp`, `mNewCp`, and run `wItemWords`
  have hs₇_base : s₇.regs mBase = base :=
    (hs₇_keep6c mBase (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
      (mReg_ne (by decide))).trans (by simp [s₆c, s₆b, s₆a, RData.set, hs₆_base])
  obtain ⟨s₈, hex_nhp, hs₈b, hs₈m, hs₈f, hs₈_nhp, hs₈_r⟩ :=
    loadBlockUpTo_exec mBase mCur (mReg_ne (by decide)) mNewHp mNewHp_inj
      (fun i => mNewHp_ne_mReg i (Or.inl (by decide)))
      (fun i => mNewHp_ne_mReg i (Or.inl (by decide)))
      offHashParams 18 (by decide) hs₇b (hs₇f_eq.le.trans h63_le) hs₇_base
      (by change base + 8 + 19 ≤ s₇.frontier; rw [hs₇f_eq]; omega)
  have hs₈_base : s₈.regs mBase = base :=
    (hs₈_r mBase (mReg_ne (by decide)) (fun i => mNewHp_ne_mReg i (Or.inl (by decide)))).trans
      hs₇_base
  obtain ⟨s₉, hex_ncp, hs₉b, hs₉m, hs₉f, hs₉_ncp, hs₉_r⟩ :=
    loadBlockUpTo_exec mBase mCur (mReg_ne (by decide)) mNewCp mNewCp_inj
      (fun i => mNewCp_ne_mReg i (Or.inl (by decide)))
      (fun i => mNewCp_ne_mReg i (Or.inl (by decide)))
      offCompParams 35 (by decide) hs₈b ((hs₈f.trans hs₇f_eq).le.trans h63_le) hs₈_base
      (by change base + 27 + 36 ≤ s₈.frontier; rw [hs₈f, hs₇f_eq])
  have hs₉m_eq : s₉.mem = s₇.mem := hs₉m.trans hs₈m
  have hs₉f_eq : s₉.frontier = base + 63 := hs₉f.trans (hs₈f.trans hs₇f_eq)
  have hs₉_nhp_all : ∀ i : Fin 19, s₉.regs (mNewHp i) =
      mkHashParams w (epochQBits U N₁) (epochHashB N₁) (totalMicroBits N₁) 3 i := fun i => by
    rw [hs₉_r (mNewHp i) (mNewHp_ne_mReg i (Or.inl (by decide)))
      (fun j => by intro h; have hv := congrArg Fin.val h; simp at hv; omega),
      hs₈_nhp i (by omega), hs₇_mem_eq]
    exact hpar_wp.hp_eq i
  have hs₉_ncp_all : ∀ i : Fin 36, s₉.regs (mNewCp i) = mkCompParams U V w N₁ i := fun i => by
    rw [hs₉_ncp i (by omega), hs₈m, hs₇_mem_eq]
    exact hpar_wp.cp_eq i
  have hs₉_keep7 : ∀ {c : Fin 160}, (c.val < 90 ∨ 146 ≤ c.val) → c ≠ 9 →
      s₉.regs (mReg c) = s₇.regs (mReg c) := fun {c} hc h9 => by
    rw [hs₉_r (mReg c) (mReg_ne h9) (fun i => mNewCp_ne_mReg i (by omega)),
      hs₈_r (mReg c) (mReg_ne h9) (fun i => mNewHp_ne_mReg i (by omega))]
  have hs₉_cnt : s₉.regs mCnt = 1 :=
    (hs₉_keep7 (c := 13) (Or.inl (by decide)) (by decide)).trans <|
    (hs₇_keep6c mCnt (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
      (mReg_ne (by decide))).trans hs₆c_cnt
  have hs₉_fr_reg : s₉.regs mFr = base + 63 :=
    (hs₉_keep7 (c := 1) (Or.inl (by decide)) (by decide)).trans hs₇_fr_reg
  have hin_niw : s₉.regs ∘ srcNewIw = WordEncoding.encode (mkCompParams U V w N₁, 1) :=
    (regs_pairSrc (regs_cp_eq hs₉_ncp_all) (regs_reg1_eq mCnt hs₉_cnt)).eq
  have hfit_iw4 : Fits w (4 + iw₁) :=
    hfit_peak.of_le (by rw [hce₁]; linarith only [h225_le])
  have hsafe_niw : CompItemWordsPre w (mkCompParams U V w N₁, 1) (memoryState mFr s₉.toData) :=
    ⟨U, V, N₁, hw, hN₁U, hU, hV, rfl, fits_wOffQ_add_three_of_itemWords hw hfit_iw4⟩
  have hv_niw := validProg_compItemWordsGen (mkCompParams U V w N₁, 1)
    (memoryState mFr s₉.toData) ⟨wellFormed_memoryState hs₉b.1, Nat.zero_le _⟩
  obtain ⟨s₁₀, hex_niw, hs₁₀b, hs₁₀f, hm_niw, hout_niw, hframe_niw⟩ :=
    execWitness wItemWords factor_mItemWords_le mFr srcNewIw tmpNewIw
      tmpNewIw_inj srcNewIw_ne_tmp tmpNewIw_ne_mFr srcNewIw_ne_mFr
      (mkCompParams U V w N₁, 1) hs₉b (hs₉f_eq.le.trans h63_le)
      hin_niw hsafe_niw hv_niw
      (by rw [clientState_compItemWordsGenProg]; change s₉.regs mFr ≤ s₉.frontier; omega)
  rw [memoryCost_compItemWordsGenProg, zero_add, mul_one] at hex_niw
  rw [clientState_compItemWordsGenProg] at hm_niw
  have hs₁₀m_eq : s₁₀.mem = s₇.mem := (congrArg Memory.State.mem hm_niw).trans hs₉m_eq
  have hs₁₀f_eq : s₁₀.frontier = base + 63 := hs₁₀f.trans hs₉f_eq
  have hs₁₀_fr_reg : s₁₀.regs mFr = base + 63 :=
    (congrArg Memory.State.frontier hm_niw).trans hs₉_fr_reg
  have hs₁₀_iw : s₁₀.regs mIwNew = iw₁ := by
    have h0 := hout_niw 0; rwa [tmpNewIw_out, clientResult_compItemWordsGenProg hw] at h0
  have hs₁₀_keep9 : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mIwNew → s₁₀.regs reg = s₉.regs reg :=
    fun reg h1 h160 hiw => hframe_niw reg h1
      (mkTmp_ne_reg _ h160 (fun a => by fin_cases a; exact hiw.symm))
  have hs₁₀_abi_of : ∀ reg : Fin rResize, reg.val < 5 → reg ≠ mFr →
      s₁₀.regs reg = x.regs reg := fun reg h5 hne_fr => by
    have h160 : reg.val < 160 := by omega
    calc s₁₀.regs reg
        = s₉.regs reg := hs₁₀_keep9 reg hne_fr h160 (ne_mReg_of_lt_five h5 (by decide))
      _ = s₈.regs reg := hs₉_r reg (ne_mReg_of_lt_five h5 (by decide))
            (fun i => by intro h; have hv := congrArg Fin.val h; simp at hv; omega)
      _ = s₇.regs reg := hs₈_r reg (ne_mReg_of_lt_five h5 (by decide))
            (fun i => by intro h; have hv := congrArg Fin.val h; simp at hv; omega)
      _ = s₆c.regs reg := hs₇_keep6c reg hne_fr h160
            (ne_mReg_of_lt_five h5 (by decide)) (ne_mReg_of_lt_five h5 (by decide))
      _ = s₆.regs reg := by
            dsimp only [s₆c, s₆b, s₆a, RData.set]
            rw [Function.update_of_ne (ne_mReg_of_lt_five h5 (by decide)),
              Function.update_of_ne hne_fr,
              Function.update_of_ne (ne_mReg_of_lt_five h5 (by decide))]
      _ = s₅.regs reg := hs₆_keep5 reg (by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨ne_mReg_of_lt_five h5 (by decide), ne_mReg_of_lt_five h5 (by decide),
              ne_mReg_of_lt_five h5 (by decide), ne_mReg_of_lt_five h5 (by decide),
              ne_mReg_of_lt_five h5 (by decide)⟩)
      _ = s₄.regs reg := by
            dsimp only [s₅, RData.set]
            rw [Function.update_of_ne (ne_mReg_of_lt_five h5 (by decide))]
      _ = s₃.regs reg := hs₄_keep3 reg hne_fr h160 (ne_mReg_of_lt_five h5 (by decide))
      _ = x.regs reg := by
            dsimp only [s₃, s₂, s₁, RData.set]
            rw [Function.update_of_ne (ne_mReg_of_lt_five h5 (by decide)),
              Function.update_of_ne hne_fr,
              Function.update_of_ne (ne_mReg_of_lt_five h5 (by decide))]
  have hf1 := one_le_migFactor
  have hc_tc_mul : migFactor * (memoryCost (computeTargetCapProg (base, 1)) ⟨x.mem, x.frontier⟩ + 1)
      ≤ 2 * migFactor := by
    have hmul := Nat.mul_le_mul_left migFactor (Nat.add_le_add_right hc_tc 1)
    linarith only [hmul]
  have hc_wp_mul : migFactor * (memoryCost
      (writeEpochParamsGenProg ((base, base), (N₁, (1, 1)))) ⟨x.mem, base + 63⟩ + 1) ≤
      migFactor * 123 :=
    Nat.mul_le_mul_left migFactor (by dsimp only [N₁] at hc_wp; linarith only [hc_wp, hN₁_le2])
  have hex_all :=
    hex₁.seq_eq (hex₂.seq_eq (hex₃.seq_eq
      ((hex_tc.mono hc_tc_mul (fun _ h => h)).seq_eq
        (hex₅.seq_eq (hex_gz1.seq_eq (hex_6a.seq_eq (hex_6b.seq_eq (hex_6c.seq_eq
          ((hex_wp.mono hc_wp_mul (fun _ h => h)).seq_eq
            (hex_nhp.seq_eq (hex_ncp.seq_eq hex_niw)))))))))))
  refine ⟨s₁₀, _, hex_all, by linarith only [hf1], hs₁₀b, hs₁₀f_eq,
    abiPreserved_of_lt_five hs₁₀_abi_of,
    fun addr haddr => by
      rw [hs₁₀m_eq, hs₇_mem_eq]; exact hframe_wp addr (fun h => by linarith only [haddr, h.1]),
    (hs₁₀m_eq.trans hs₇_mem_eq).symm ▸ hhdr_wp,
    (hs₁₀m_eq.trans hs₇_mem_eq).symm ▸ hpar_wp,
    (hs₁₀_abi_of mBase (by decide) (mReg_ne (by decide))).trans hbase,
    hs₁₀_fr_reg,
    (hs₁₀_keep9 mOffNew (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
      (hs₉_keep7 (c := 150) (Or.inr (by decide)) (by decide)).trans hs₇_off,
    hs₁₀_iw,
    fun i => (hs₁₀_keep9 (mNewHp i) (mNewHp_ne_mReg i (Or.inl (by decide))) (mNewHp_lt_160 i)
      (mNewHp_ne_mReg i (Or.inr (by decide)))).trans (hs₉_nhp_all i),
    fun i => (hs₁₀_keep9 (mNewCp i) (mNewCp_ne_mReg i (Or.inl (by decide))) (mNewCp_lt_160 i)
      (mNewCp_ne_mReg i (Or.inr (by decide)))).trans (hs₉_ncp_all i)⟩

private theorem initFirstGrowCode_exec {U V w base : ℕ} {x s₁₀ : RData rResize}
    (hfit_peak : Fits w (base + compactedEpochWords U V w (targetCap U 1) 1))
    (hs₁₀b : s₁₀.Bounded w)
    (hs₁₀f : s₁₀.frontier = base + 63)
    (habi₁₀ : abiPreserved x s₁₀)
    (hbelow₁₀ : ∀ addr < base, s₁₀.mem addr = x.mem addr)
    (hhdr₁₀ : RootHeaderValid U V w (targetCap U 1) 1 1 base s₁₀.mem)
    (hpar₁₀ : EpochParamsStored U V w (targetCap U 1) base s₁₀.mem)
    (hs₁₀_base : s₁₀.regs mBase = base)
    (hs₁₀_fr : s₁₀.regs mFr = base + 63)
    (hs₁₀_off : s₁₀.regs mOffNew = offCompItems U w (targetCap U 1))
    (hs₁₀_iw : s₁₀.regs mIwNew = compactedItemWords U V w (targetCap U 1) 1)
    (hs₁₀_nhp : ∀ i : Fin 19, s₁₀.regs (mNewHp i) =
      mkHashParams w (epochQBits U (targetCap U 1)) (epochHashB (targetCap U 1))
        (totalMicroBits (targetCap U 1)) 3 i)
    (hs₁₀_ncp : ∀ i : Fin 36, s₁₀.regs (mNewCp i) = mkCompParams U V w (targetCap U 1) i) :
    let N₁ := targetCap U 1
    let off₁ := offCompItems U w N₁
    let fr₁ := base + compactedEpochWords U V w N₁ 1
    ∃ (y : RData rResize) (steps_g : ℕ),
      RDemonicExec w fr₁ initFirstGrowCode s₁₀ steps_g (· = y) ∧
      steps_g ≤ 4800 ∧
      y.Bounded w ∧
      y.frontier = fr₁ ∧
      abiPreserved x y ∧
      (∀ addr < base, y.mem addr = x.mem addr) ∧
      RootHeaderValid U V w N₁ 1 1 base y.mem ∧
      EpochParamsStored U V w N₁ base y.mem ∧
      y.regs mBase = base ∧
      y.regs mFr = fr₁ ∧
      y.regs mItemBase = base + off₁ ∧
      y.regs mHashBase = base + epochHdrWords ∧
      (∀ i : Fin 19, y.regs (mNewHp i) =
        mkHashParams w (epochQBits U N₁) (epochHashB N₁) (totalMicroBits N₁) 3 i) ∧
      (∀ i : Fin 36, y.regs (mNewCp i) = mkCompParams U V w N₁ i) := by
  intro N₁ off₁ fr₁
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hs₁₀b hhdr₁₀
  obtain ⟨_, _, hN₁_le2, hN₁U⟩ := targetCap_bounds_of_pos (le_rfl : 1 ≤ 1) hhdr₁₀.pos_U
  set iw₁ := compactedItemWords U V w N₁ 1
  have hce₁ : compactedEpochWords U V w N₁ 1 = off₁ + iw₁ := by
    unfold compactedEpochWords; simp [off₁, iw₁]
  have hfr₁_eq : fr₁ = base + off₁ + iw₁ := by dsimp only [fr₁]; rw [hce₁, Nat.add_assoc]
  have h225_le : 225 ≤ off₁ := le_offCompItems_225 U w N₁
  have h63_le : base + 63 ≤ fr₁ := by rw [hfr₁_eq]; linarith only [h225_le]
  have hfit_off : Fits w (base + off₁) := hfit_peak.of_le (by rw [hce₁]; linarith only)
  have hfit225 : Fits w 225 := fits_const_of_offCompItems hfit_off le_rfl
  have hfit1 : Fits w 1 := hfit225.of_le (by decide)
  set y₁ := s₁₀.set mItemBase (base + off₁)
  have hex₁ := RDemonicExec.exactBin (f := .add) (d := mItemBase) (i := mBase) (j := mOffNew)
    (w := w) (L_peak := fr₁) (x := s₁₀) (hs₁₀f.le.trans h63_le) (v := base + off₁)
    (by simp [BinOp.evalExact, hs₁₀_base, hs₁₀_off, off₁, N₁]) hfit_off
  set y₂ := y₁.set mPeakFront fr₁
  have hex₂ := RDemonicExec.exactBin (f := .add) (d := mPeakFront) (i := mItemBase) (j := mIwNew)
    (w := w) (L_peak := fr₁) (x := y₁) (hs₁₀f.le.trans h63_le) (v := fr₁)
    (by simp [BinOp.evalExact, y₁, RData.set, hs₁₀_iw, hfr₁_eq, off₁, iw₁, N₁]) hfit_peak
  set y₃ := y₂.set mK (fr₁ - (base + 63))
  have hex₃ := RDemonicExec.exactBin (f := .sub) (d := mK) (i := mPeakFront) (j := mFr)
    (w := w) (L_peak := fr₁) (x := y₂) (hs₁₀f.le.trans h63_le) (v := fr₁ - (base + 63))
    (by simp [BinOp.evalExact, y₂, y₁, RData.set, hs₁₀_fr, h63_le])
    (hfit_peak.of_le (Nat.sub_le _ _))
  have hy₃b : y₃.Bounded w :=
    ((hs₁₀b.set hfit_off).set hfit_peak).set (hfit_peak.of_le (Nat.sub_le _ _))
  have hy₃_k : y₃.regs mK = fr₁ - (base + 63) := by simp [y₃, RData.set]
  have hsum_fr₁ : y₃.frontier + y₃.regs mK = fr₁ := by
    rw [show y₃.frontier = base + 63 from hs₁₀f, hy₃_k]; exact Nat.add_sub_of_le h63_le
  have hex_gz := growZeroCode_exec (w := w) (L_peak := fr₁)
    (count := mK) (result := mRes) (cur := mCur) (idx := mIdx) (zero := mZero) (one := mOne)
    hy₃b mGrow_nodup hfit1 hsum_fr₁.le (hsum_fr₁ ▸ hfit_peak)
  rw [hy₃_k] at hex_gz
  set y₄ := growZeroPost mK mRes mCur mIdx mZero mOne y₃
  have hy₄b : y₄.Bounded w := growZeroPost_bounded hy₃b hfit1 (hsum_fr₁ ▸ hfit_peak)
  have hy₄m : y₄.mem = s₁₀.mem := rfl
  have hy₄f : y₄.frontier = fr₁ := hsum_fr₁
  have hy₄_keep3 : ∀ reg, reg ∉ ([mRes, mCur, mIdx, mZero, mOne] : List (Fin rResize)) →
      y₄.regs reg = y₃.regs reg := fun _ hreg => growZeroPost_regs_of_not_mem hreg
  set y₅ := y₄.set mFr fr₁
  have hy₄_pf : y₄.regs mPeakFront = fr₁ :=
    (hy₄_keep3 mPeakFront
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans
      (by simp [y₃, y₂, RData.set])
  have hex₅ := RDemonicExec.copy (B := .exact) (w := w) (L_peak := fr₁)
    (d := mFr) (s := mPeakFront) (x := y₄) hy₄f.le
  rw [hy₄_pf] at hex₅
  set y₆ := y₅.set mCur 225
  have hex₆ := RDemonicExec.const (B := .exact) (d := mCur) (v := 225) (x := y₅) hy₄f.le hfit225
  set y := y₆.set mHashBase (base + epochHdrWords)
  have hy₆_base : y₆.regs mBase = base := by
    dsimp only [y₆, y₅, RData.set]
    rw [Function.update_of_ne (mReg_ne (by decide) : mBase ≠ mCur),
      Function.update_of_ne (mReg_ne (by decide) : mBase ≠ mFr),
      hy₄_keep3 mBase (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)]
    simp [y₃, y₂, y₁, RData.set, hs₁₀_base]
  have hfit_hb : Fits w (base + epochHdrWords) :=
    hfit_off.of_le (by unfold epochHdrWords; linarith only [h225_le])
  have hex₇ := RDemonicExec.exactBin (f := .add) (d := mHashBase) (i := mBase) (j := mCur)
    (w := w) (L_peak := fr₁) (x := y₆) hy₄f.le (v := base + epochHdrWords)
    (by
      change some (y₆.regs mBase + y₆.regs mCur) = some (base + 225)
      rw [hy₆_base]; simp [y₆, RData.set])
    hfit_hb
  have hyb : y.Bounded w := ((hy₄b.set hfit_peak).set hfit225).set hfit_hb
  have hkeep_10_y : ∀ reg : Fin rResize,
      reg ∉ ([mFr, mCur, mHashBase, mRes, mIdx, mZero, mOne, mK, mPeakFront, mItemBase] :
        List (Fin rResize)) →
      y.regs reg = s₁₀.regs reg := fun reg hnot => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    obtain ⟨hfr', hcur, hhb, hres, hidx, hz, ho, hk, hpf, hib⟩ := hnot
    calc y.regs reg
        = y₄.regs reg := by
            dsimp only [y, y₆, y₅, RData.set]
            rw [Function.update_of_ne hhb, Function.update_of_ne hcur, Function.update_of_ne hfr']
      _ = y₃.regs reg := hy₄_keep3 reg (by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨hres, hcur, hidx, hz, ho⟩)
      _ = s₁₀.regs reg := by
            dsimp only [y₃, y₂, y₁, RData.set]
            rw [Function.update_of_ne hk, Function.update_of_ne hpf, Function.update_of_ne hib]
  have hoff_lin : off₁ ≤ 943 :=
    (offCompItems_le_linear hw hN₁U hhdr₁₀.fits_U).trans (by linarith only [hN₁_le2])
  have hiw_lin : iw₁ ≤ 4 :=
    (compactedItemWords_le_linear (U := U) (V := V) (w := w) (N := N₁) (n := 1) hw hU.le hV).trans
      (by decide)
  have hc_gz : 5 * (fr₁ - (base + 63)) + 6 ≤ 4750 := by
    have hsub : fr₁ - (base + 63) ≤ off₁ + iw₁ := by
      rw [hfr₁_eq]
      exact (Nat.sub_le_sub_left (Nat.le_add_right base 63) _).trans_eq
        (by rw [Nat.add_assoc, Nat.add_sub_cancel_left])
    linarith only [hsub, hoff_lin, hiw_lin]
  have hex_all :=
    hex₁.seq_eq (hex₂.seq_eq (hex₃.seq_eq
      ((hex_gz.mono hc_gz (fun _ h => h)).seq_eq (hex₅.seq_eq (hex₆.seq_eq hex₇)))))
  refine ⟨y, _, hex_all, by linarith only, hyb, hy₄f,
    abiPreserved_trans habi₁₀
      ⟨hkeep_10_y mBase
         (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide),
       hkeep_10_y mTag
         (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide),
       hkeep_10_y mArgU
         (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide),
       hkeep_10_y mArgV
         (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)⟩,
    hbelow₁₀, hhdr₁₀, hpar₁₀,
    (hkeep_10_y mBase
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₁₀_base,
    by simp [y, y₆, y₅, RData.set],
    by
      dsimp only [y, y₆, y₅, RData.set]
      rw [Function.update_of_ne (mReg_ne (by decide)),
        Function.update_of_ne (mReg_ne (by decide)),
        Function.update_of_ne (mReg_ne (by decide)),
        hy₄_keep3 mItemBase
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)]
      simp [y₃, y₂, y₁, RData.set],
    by simp [y, RData.set],
    fun i => (hkeep_10_y (mNewHp i) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
        mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
        mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
        mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
        mNewHp_ne_mReg i (Or.inr (by decide)), mNewHp_ne_mReg i (Or.inl (by decide))⟩)).trans
      (hs₁₀_nhp i),
    fun i => (hkeep_10_y (mNewCp i) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
        mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
        mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
        mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
        mNewCp_ne_mReg i (Or.inr (by decide)), mNewCp_ne_mReg i (Or.inl (by decide))⟩)).trans
      (hs₁₀_ncp i)⟩

theorem initFirstSetupCode_exec {U V w base : ℕ} {x : RData rResize}
    (hx : x.Bounded w)
    (hfr : x.frontier = base + 8)
    (hhdr : RootHeaderValid U V w 0 0 0 base x.mem)
    (hfit_peak : Fits w (base + compactedEpochWords U V w (targetCap U 1) 1))
    (hbase : x.regs mBase = base) :
    let N₁ := targetCap U 1
    let off₁ := offCompItems U w N₁
    let fr₁ := base + compactedEpochWords U V w N₁ 1
    ∃ (y_set : RData rResize) (steps_set : ℕ),
      RDemonicExec w fr₁ initFirstSetupCode x steps_set (· = y_set) ∧
      steps_set ≤ 126 * migFactor + 5260 ∧
      y_set.Bounded w ∧
      y_set.frontier = fr₁ ∧
      abiPreserved x y_set ∧
      (∀ addr < base, y_set.mem addr = x.mem addr) ∧
      RootHeaderValid U V w N₁ 1 1 base y_set.mem ∧
      EpochParamsStored U V w N₁ base y_set.mem ∧
      y_set.regs mBase = base ∧
      y_set.regs mFr = fr₁ ∧
      y_set.regs mItemBase = base + off₁ ∧
      y_set.regs mHashBase = base + epochHdrWords ∧
      (∀ i : Fin 19, y_set.regs (mNewHp i) =
        mkHashParams w (epochQBits U N₁) (epochHashB N₁) (totalMicroBits N₁) 3 i) ∧
      (∀ i : Fin 36, y_set.regs (mNewCp i) = mkCompParams U V w N₁ i) := by
  intro N₁ off₁ fr₁
  obtain ⟨s₁₀, steps_p, hex_p, hc_p, hs₁₀b, hs₁₀f, habi₁₀, hbelow₁₀, hhdr₁₀, hpar₁₀,
      hs₁₀_base, hs₁₀_fr, hs₁₀_off, hs₁₀_iw, hs₁₀_nhp, hs₁₀_ncp⟩ :=
    initFirstParamsCode_exec hx hfr hhdr hfit_peak hbase
  obtain ⟨y_set, steps_g, hex_g, hc_g, hrest⟩ :=
    initFirstGrowCode_exec hfit_peak hs₁₀b hs₁₀f habi₁₀ hbelow₁₀ hhdr₁₀ hpar₁₀
      hs₁₀_base hs₁₀_fr hs₁₀_off hs₁₀_iw hs₁₀_nhp hs₁₀_ncp
  exact ⟨y_set, steps_p + steps_g, hex_p.seq_eq hex_g, by linarith only [hc_p, hc_g], hrest⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
