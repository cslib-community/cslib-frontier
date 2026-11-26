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
# Active-Epoch Migration Parameter-Staging Subprogram (`migrateSetupParamsCode`)

Internal first half of `migrateSetupCode`: loads active-epoch header and parameter blocks, stages
the new capacity parameters `(targetCap U n, n, n)` in scratch `[base + 63, base + 126)`, loads
`mNewHp` / `mNewCp`, evaluates `mIwNew`, and computes the single-tape `1 · OPT` arena bounds.
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

/-- Load `n`, `oldHp`, `oldCp`, evaluate `iwOld`, reconstruct `mNewMeta = base + offOld` and
`mFr = x.frontier`, and evaluate `mNNew = targetCap U n`. -/
private noncomputable def migrateLoadOldCode : RCode .exact rResize :=
  .seq (loadAtOffCode mBase mCnt mCur 6) <|
  .seq (loadBlockUpTo mBase mCur mOldHp offHashParams 18 (by decide)) <|
  .seq (loadBlockUpTo mBase mCur mOldCp offCompParams 35 (by decide)) <|
  .seq (.op (.const mFr 0)) <|
  .seq (RCode.ofCode (wItemWords.code mFr srcOldIw tmpOldIw)) <|
  .seq (.op (.exactBin .add mNewMeta mBase (mOldCp ⟨34, by decide⟩))) <|
  .seq (.op (.exactBin .add mFr mNewMeta mIwOld))
       (RCode.ofCode (wTargetCap.code mFr srcTargetCap tmpTargetCap))

/-- Compute `mArenaWords = max iwOld iwNew + 6`, `mArena = newMetaBase + offNew`,
`mPeakFront = mArena + mArenaWords`, `mK = mPeakFront - mFr`, and
`mOldItemDst = mPeakFront - mIwOld`. -/
private noncomputable def migrateComputeArenaCode : RCode .exact rResize :=
  .seq (.branch (.lt mIwOld mIwNew)
    (.op (.copy mArenaWords mIwNew))
    (.op (.copy mArenaWords mIwOld))) <|
  .seq (.op (.const mCur 6)) <|
  .seq (.op (.exactBin .add mArenaWords mArenaWords mCur)) <|
  .seq (.op (.exactBin .add mArena mNewMeta mOffNew)) <|
  .seq (.op (.exactBin .add mPeakFront mArena mArenaWords)) <|
  .seq (.op (.exactBin .sub mK mPeakFront mFr))
       (.op (.exactBin .sub mOldItemDst mPeakFront mIwOld))

/-- First half of `migrateSetupCode`: loads old epoch parameters, stages new parameters at
`base + 63`, loads `mNewHp`/`mNewCp`, computes `mIwNew`, and computes arena bounds. -/
noncomputable def migrateSetupParamsCode : RCode .exact rResize :=
  .seq migrateLoadOldCode <|
  .seq (.op (.const mCur 63)) <|
  .seq (.op (.exactBin .add mTmpA mBase mCur)) <|
  .seq (RCode.ofCode (wWriteParams.code mFr srcWriteParams tmpWriteParams)) <|
  .seq (loadBlockUpTo mBase mCur mNewHp (63 + offHashParams) 18 (by decide)) <|
  .seq (loadBlockUpTo mBase mCur mNewCp (63 + offCompParams) 35 (by decide)) <|
  .seq (RCode.ofCode (wItemWords.code mFr srcNewIw tmpNewIw))
       migrateComputeArenaCode

private theorem not_readsWidth_migrateLoadOldCode : ¬migrateLoadOldCode.ReadsWidth := by
  have hb1 := not_readsWidth_loadBlockUpTo mBase mCur mOldHp offHashParams 18 (by decide)
  have hb2 := not_readsWidth_loadBlockUpTo mBase mCur mOldCp offCompParams 35 (by decide)
  simp [migrateLoadOldCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    not_readsWidth_loadAtOffCode, hb1, hb2]

private theorem not_readsWidth_migrateComputeArenaCode : ¬migrateComputeArenaCode.ReadsWidth := by
  simp [migrateComputeArenaCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

theorem not_readsWidth_migrateSetupParamsCode : ¬migrateSetupParamsCode.ReadsWidth := by
  simp [migrateSetupParamsCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    not_readsWidth_migrateLoadOldCode, not_readsWidth_migrateComputeArenaCode,
    not_readsWidth_loadBlockUpTo]

private theorem exec_add_bdd {w L_peak : ℕ} (d i j : Fin rResize) (v : ℕ) {x : RData rResize}
    (hx : x.Bounded w) (hL : x.frontier ≤ L_peak)
    (hv : x.regs i + x.regs j = v) (hfit : Fits w v) :
    RDemonicExec (B := .exact) w L_peak (.op (.exactBin .add d i j)) x 1 (· = x.set d v) ∧
      (x.set d v).Bounded w :=
  ⟨RDemonicExec.exactBin hL (congrArg some hv) hfit, hx.set hfit⟩

private theorem exec_sub_bdd {w L_peak : ℕ} (d i j : Fin rResize) (v : ℕ) {x : RData rResize}
    (hx : x.Bounded w) (hL : x.frontier ≤ L_peak)
    (hle : x.regs j ≤ x.regs i) (hv : x.regs i - x.regs j = v) (hfit : Fits w v) :
    RDemonicExec (B := .exact) w L_peak (.op (.exactBin .sub d i j)) x 1 (· = x.set d v) ∧
      (x.set d v).Bounded w :=
  ⟨RDemonicExec.exactBin hL (by simp [BinOp.evalExact, hle, hv]) hfit, hx.set hfit⟩

private theorem migrateLoadOldCode_exec {U V w N_old n n_init base L_peak : ℕ}
    {θ_old : QuotHashSeed U N_old} {s_abs : Dictionary.State U} {x : RData rResize}
    (hx : x.Bounded w) (hn : 1 ≤ n) (hev : EpochValid U n N_old)
    (hfr : x.frontier = base + compactedEpochWords U V w N_old n)
    (hL : x.frontier ≤ L_peak)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N_old) U V w N_old n n_init θ_old
      s_abs ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base) :
    ∃ y : RData rResize,
      RDemonicExec w L_peak migrateLoadOldCode x (3 * migFactor + 175) (· = y) ∧
      y.Bounded w ∧ y.mem = x.mem ∧ y.frontier = x.frontier ∧
      abiPreserved x y ∧
      y.regs mCnt = n ∧
      y.regs mIwOld = compactedItemWords U V w N_old n ∧
      y.regs mNewMeta = base + offCompItems U w N_old ∧
      y.regs mFr = x.frontier ∧
      y.regs mNNew = targetCap U n ∧
      (∀ i : Fin 19, y.regs (mOldHp i) =
        mkHashParams w (epochQBits U N_old) (epochHashB N_old) (totalMicroBits N_old) 3 i) ∧
      (∀ i : Fin 36, y.regs (mOldCp i) = mkCompParams U V w N_old i) := by
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  have hNU_old : N_old ≤ U := by rcases hev with ⟨rfl, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  have hn_old : n ≤ N_old := by rcases hev with ⟨rfl, _⟩ | ⟨_, hnN, _, _⟩ <;> omega
  have hnU : n ≤ U := hn_old.trans hNU_old
  have hce_old : compactedEpochWords U V w N_old n =
      offCompItems U w N_old + compactedItemWords U V w N_old n := by
    unfold compactedEpochWords; rw [ite_eq_right (by omega)]
  have h225_old : 225 ≤ offCompItems U w N_old := le_offCompItems_225 U w N_old
  have hfit_fr : Fits w x.frontier := hx.frontier_fits
  have hfit6 : Fits w 6 := hfit_fr.of_le (by rw [hfr, hce_old]; omega)
  have hfit1 : Fits w 1 := hfit6.of_le (by decide)
  obtain ⟨hex_ldn, hx₁b⟩ := loadAtOffCode_exec (rAddr := mBase) (rDst := mCnt) (rTmp := mCur)
    hx hL (mReg_ne (by decide)) hbase hfit6
    (by rw [hfr, hce_old]; omega)
  set x₁ := (x.set mCur (base + 6)).set mCnt (x.mem (base + 6))
  have hx₁_cnt : x₁.regs mCnt = n :=
    (by simp [x₁, RData.set] : x₁.regs mCnt = x.mem (base + 6)).trans hsplit.root_hdr.hdr_n
  have hx₁_base : x₁.regs mBase = base := by simp [x₁, RData.set, hbase]
  obtain ⟨x₂, hex_hp, hx₂b, hx₂m, hx₂f, hx₂_hp, hx₂_r⟩ :=
    loadBlockUpTo_exec mBase mCur (mReg_ne (by decide)) mOldHp mOldHp_inj
      (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))
      (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))
      offHashParams 18 (by decide) hx₁b hL hx₁_base
      (by change base + 8 + 19 ≤ x.frontier; rw [hfr, hce_old]; omega)
  have hx₂_base : x₂.regs mBase = base :=
    (hx₂_r mBase (mReg_ne (by decide)) (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))).trans
      hx₁_base
  obtain ⟨x₃, hex_cp, hx₃b, hx₃m, hx₃f, hx₃_cp, hx₃_r⟩ :=
    loadBlockUpTo_exec mBase mCur (mReg_ne (by decide)) mOldCp mOldCp_inj
      (fun i => mOldCp_ne_mReg i (Or.inl (by decide)))
      (fun i => mOldCp_ne_mReg i (Or.inl (by decide)))
      offCompParams 35 (by decide) hx₂b (hx₂f.le.trans hL) hx₂_base
      (by change base + 27 + 36 ≤ x₂.frontier; rw [hx₂f]; dsimp [x₁]; rw [hfr, hce_old]; omega)
  have hx₃m_eq : x₃.mem = x.mem := hx₃m.trans hx₂m
  have hx₃f_eq : x₃.frontier = x.frontier := hx₃f.trans hx₂f
  have hpres₃ : ∀ {c : Fin 160}, (c.val < 32 ∨ 88 ≤ c.val) → c ≠ 9 → c ≠ 13 →
      x₃.regs (mReg c) = x.regs (mReg c) := fun {c} hc h9 h13 => by
    rw [hx₃_r (mReg c) (mReg_ne h9) (fun i => mOldCp_ne_mReg i (by omega)),
      hx₂_r (mReg c) (mReg_ne h9) (fun i => mOldHp_ne_mReg i (by omega))]
    simp [x₁, RData.set, Function.update_of_ne (mReg_ne h13), Function.update_of_ne (mReg_ne h9)]
  have hx₃_cnt : x₃.regs mCnt = n :=
    (hx₃_r mCnt (mReg_ne (by decide)) (fun i => mOldCp_ne_mReg i (Or.inl (by decide)))).trans <|
      (hx₂_r mCnt (mReg_ne (by decide)) (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))).trans
        hx₁_cnt
  have hx₃_hp_all : ∀ i : Fin 19, x₃.regs (mOldHp i) =
      mkHashParams w (epochQBits U N_old) (epochHashB N_old) (totalMicroBits N_old) 3 i := fun i =>
    by
      rw [hx₃_r (mOldHp i) (mOldHp_ne_mReg i (Or.inl (by decide)))
        (fun j => by intro h; have hv := congrArg Fin.val h; simp at hv; omega),
        hx₂_hp i (by omega)]
      exact hsplit.params_stored.hp_eq i
  have hx₃_cp_all : ∀ i : Fin 36, x₃.regs (mOldCp i) = mkCompParams U V w N_old i := fun i =>
    (hx₃_cp i (by omega)).trans (by rw [hx₂m]; exact hsplit.params_stored.cp_eq i)
  set x₄ := x₃.set mFr 0
  have hex_zfr := RDemonicExec.const (B := .exact) (d := mFr) (x := x₃)
    (hx₃f_eq.le.trans hL) (fits_zero w)
  have hx₄b : x₄.Bounded w := hx₃b.set (fits_zero w)
  have hin_iw : x₄.regs ∘ srcOldIw = WordEncoding.encode (mkCompParams U V w N_old, n) := by
    refine (regs_pairSrc (regs_cp_eq fun i => ?_) (regs_reg1_eq mCnt ?_)).eq
    · dsimp only [x₄, RData.set]
      rw [Function.update_of_ne (mOldCp_ne_mReg i (c := 1) (Or.inl (by decide)))]
      exact hx₃_cp_all i
    · simp [x₄, RData.set, hx₃_cnt]
  have hfit_iw4 : Fits w (4 + compactedItemWords U V w N_old n) :=
    hfit_fr.of_le (by rw [hfr, hce_old]; omega)
  have hsafe_iw : CompItemWordsPre w (mkCompParams U V w N_old, n) (memoryState mFr x₄.toData) :=
    ⟨U, V, N_old, hw, hNU_old, hU, hV, rfl, fits_wOffQ_add_three_of_itemWords hw hfit_iw4⟩
  have hv_iw := validProg_compItemWordsGen (mkCompParams U V w N_old, n)
    (memoryState mFr x₄.toData) ⟨wellFormed_memoryState hx₄b.1, Nat.zero_le _⟩
  have hnoalloc_iw : ((Memory.spec 0).clientState (memoryState mFr x₄.toData)
      (compItemWordsGenProg (mkCompParams U V w N_old, n))).frontier ≤ x₄.frontier := by
    rw [clientState_compItemWordsGenProg]; change 0 ≤ x₄.frontier; omega
  obtain ⟨x₅, hex_iw, hx₅b, hx₅f, hm_iw, hout_iw, hframe_iw⟩ :=
    execWitness wItemWords factor_mItemWords_le mFr srcOldIw tmpOldIw
      tmpOldIw_inj srcOldIw_ne_tmp tmpOldIw_ne_mFr srcOldIw_ne_mFr
      (mkCompParams U V w N_old, n) hx₄b (hx₃f_eq.le.trans hL) hin_iw hsafe_iw hv_iw hnoalloc_iw
  rw [memoryCost_compItemWordsGenProg, zero_add, mul_one] at hex_iw
  rw [clientState_compItemWordsGenProg] at hm_iw
  have hx₅m : x₅.mem = x.mem := (congrArg Memory.State.mem hm_iw).trans hx₃m_eq
  have hx₅f_eq : x₅.frontier = x.frontier := hx₅f.trans hx₃f_eq
  have hx₅_iw : x₅.regs mIwOld = compactedItemWords U V w N_old n := by
    rw [← tmpOldIw_out, hout_iw 0, clientResult_compItemWordsGenProg hw]; rfl
  have hx₅_keep : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mIwOld → x₅.regs reg = x₃.regs reg :=
    fun reg hfr' h160 hiw =>
      (hframe_iw reg hfr'
        (mkTmp_ne_reg _ h160 (fun a => by fin_cases a; exact hiw.symm))).trans
      (by simp [x₄, RData.set, Function.update_of_ne hfr'])
  have hx₅_base : x₅.regs mBase = base :=
    (hx₅_keep mBase (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
      ((hpres₃ (c := 0) (Or.inl (by decide)) (by decide) (by decide)).trans hbase)
  let idx34 : Fin 36 := ⟨34, by decide⟩
  have hx₅_cp34 : x₅.regs (mOldCp idx34) = offCompItems U w N_old :=
    (hx₅_keep (mOldCp idx34) (mOldCp_ne_mReg _ (Or.inl (by decide))) (mOldCp_lt_160 _)
      (mOldCp_ne_mReg _ (Or.inr (by decide)))).trans (hx₃_cp_all idx34)
  obtain ⟨hex_nm, hx₆b⟩ := exec_add_bdd mNewMeta mBase (mOldCp idx34)
    (base + offCompItems U w N_old) hx₅b (hx₅f_eq.le.trans hL)
    (by rw [hx₅_base, hx₅_cp34])
    (hfit_fr.of_le (by rw [hfr, hce_old]; omega))
  set x₆ := x₅.set mNewMeta (base + offCompItems U w N_old)
  obtain ⟨hex_fr, hx₇b⟩ := exec_add_bdd mFr mNewMeta mIwOld x.frontier hx₆b
    (hx₅f_eq.le.trans hL) (by simp [x₆, RData.set, hx₅_iw, hfr, hce_old]; omega) hfit_fr
  set x₇ := x₆.set mFr x.frontier
  have hms₇ : memoryState mFr x₇.toData = ⟨x.mem, x.frontier⟩ :=
    Memory.State.ext hx₅m (by simp [memoryState, x₇, RData.set, RData.toData])
  have hx₇_base : x₇.regs mBase = base := by simp [x₇, x₆, RData.set, hx₅_base]
  have hx₇_cnt : x₇.regs mCnt = n := by
    simpa [x₇, x₆, RData.set] using
      (hx₅_keep mCnt (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans hx₃_cnt
  have hin_tc : x₇.regs ∘ srcTargetCap = WordEncoding.encode (base, n) :=
    (regs_pairSrc (regs_reg1_eq mBase hx₇_base) (regs_reg1_eq mCnt hx₇_cnt)).eq
  obtain ⟨hpre_tc, hv_tc, hst_tc, hres_tc, hc_tc⟩ :=
    computeTargetCapProg_spec (s := ⟨x.mem, x.frontier⟩) hsplit.root_hdr
      (by change base < x.frontier; rw [hfr, hce_old]; omega) hnU hfit1
  have hnoalloc_tc : ((Memory.spec 0).clientState (memoryState mFr x₇.toData)
      (computeTargetCapProg (base, n))).frontier ≤ x₇.frontier := by
    rw [hms₇, hst_tc]
    exact hx₅f_eq.symm.le
  obtain ⟨y, hex_tc, hyb, hyf, hm_tc, hout_tc, hframe_tc⟩ :=
    execWitness wTargetCap factor_wTargetCap_le mFr srcTargetCap tmpTargetCap
      tmpTargetCap_inj srcTargetCap_ne_tmp tmpTargetCap_ne_mFr srcTargetCap_ne_mFr
      (base, n) hx₇b (hx₅f_eq.le.trans hL) hin_tc (hms₇ ▸ hpre_tc) (hms₇ ▸ hv_tc) hnoalloc_tc
  simp only [hms₇, hst_tc, hres_tc] at hm_tc hout_tc
  have hym : y.mem = x.mem := congrArg Memory.State.mem hm_tc
  have hy_fr_reg : y.regs mFr = x.frontier := congrArg Memory.State.frontier hm_tc
  have hy_nnew : y.regs mNNew = targetCap U n := by
    rw [← tmpTargetCap_out, hout_tc 0]; rfl
  have hy_keep : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mNNew → y.regs reg = x₇.regs reg :=
    fun reg hfr' h160 hnn =>
      hframe_tc reg hfr' (mkTmp_ne_reg _ h160 (fun a => by fin_cases a; exact hnn.symm))
  have hf1 := one_le_migFactor
  have hcost_tc : migFactor * (memoryCost (computeTargetCapProg (base, n))
      (memoryState mFr x₇.toData) + 1) ≤ 2 * migFactor :=
    hms₇.symm ▸ (Nat.mul_le_mul_left migFactor (Nat.add_le_add_right hc_tc 1)).trans_eq
      (Nat.mul_comm _ _)
  have hex_all := hex_ldn.seq_eq (hex_hp.seq_eq (hex_cp.seq_eq (hex_zfr.seq_eq
    (hex_iw.seq_eq (hex_nm.seq_eq (hex_fr.seq_eq
      (hex_tc.mono hcost_tc (fun _ h => h))))))))
  have hy_x : ∀ reg : Fin rResize, reg.val < 160 →
      reg ∉ ([mFr, mNNew, mNewMeta, mIwOld] : List (Fin rResize)) → y.regs reg = x₃.regs reg :=
    fun reg h160 h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      rw [hy_keep reg h.1 h160 h.2.1, ← hx₅_keep reg h.1 h160 h.2.2.2]
      exact (Function.update_of_ne h.1 _ _).trans (Function.update_of_ne h.2.2.1 _ _)
  refine ⟨y, hex_all.mono (by omega) (fun _ h => h), hyb, hym, hyf.trans hx₅f_eq, ⟨?_, ?_, ?_, ?_⟩,
    (hy_x _ (mReg_lt_160 _) (by simp)).trans hx₃_cnt,
    (hy_keep _ (by simp) (mReg_lt_160 _) (by simp)).trans (by simp [x₇, x₆, hx₅_iw]),
    (hy_keep _ (by simp) (mReg_lt_160 _) (by simp)).trans (by simp [x₇, x₆]), hy_fr_reg, hy_nnew,
    fun i => (hy_x _ (mOldHp_lt_160 i) (by clear * -; simp [Fin.ext_iff]; omega)).trans
      (hx₃_hp_all i),
    fun i => (hy_x _ (mOldCp_lt_160 i) (by clear * -; simp [Fin.ext_iff]; omega)).trans
      (hx₃_cp_all i)⟩
  all_goals refine (hy_x _ (mReg_lt_160 _) ?_).trans (hpres₃ (Or.inl ?_) ?_ ?_) <;> simp

private theorem migrateComputeArenaCode_exec {w L_peak newMeta offNew iwOld iwNew frOld : ℕ}
    {x : RData rResize}
    (hx : x.Bounded w) (hL : x.frontier ≤ L_peak)
    (hfr_eq : frOld = newMeta + iwOld)
    (hfit_peak : Fits w (newMeta + offNew + (max iwOld iwNew + 6)))
    (h_nm : x.regs mNewMeta = newMeta)
    (h_on : x.regs mOffNew = offNew)
    (h_iwo : x.regs mIwOld = iwOld)
    (h_iwn : x.regs mIwNew = iwNew)
    (h_fr : x.regs mFr = frOld) :
    let arenaW := max iwOld iwNew + 6
    let arenaB := newMeta + offNew
    let peakF := arenaB + arenaW
    ∃ y : RData rResize,
      RDemonicExec w L_peak migrateComputeArenaCode x 10 (· = y) ∧
      y.Bounded w ∧ y.mem = x.mem ∧ y.frontier = x.frontier ∧
      y.regs mArenaWords = arenaW ∧
      y.regs mArena = arenaB ∧
      y.regs mPeakFront = peakF ∧
      y.regs mK = peakF - frOld ∧
      y.regs mOldItemDst = arenaB + (arenaW - iwOld) ∧
      ∀ reg, reg ∉ ([mArenaWords, mCur, mArena, mPeakFront, mK, mOldItemDst] : List (Fin rResize)) →
        y.regs reg = x.regs reg := by
  intro arenaW arenaB peakF
  set x₁ := x.set mArenaWords (max iwOld iwNew)
  have hex₁ : RDemonicExec (B := .exact) w L_peak
      (.branch (.lt mIwOld mIwNew) (.op (.copy mArenaWords mIwNew))
        (.op (.copy mArenaWords mIwOld))) x 3 (· = x₁) := by
    by_cases hlt : iwOld < iwNew
    · have hcp := RDemonicExec.copy (B := .exact) (w := w) (d := mArenaWords) (s := mIwNew)
        (x := x) hL
      rw [h_iwn, ← Nat.max_eq_right hlt.le] at hcp
      exact (RDemonicExec.branch_pos (c := .lt mIwOld mIwNew)
        (h_iwo.trans_lt (hlt.trans_eq h_iwn.symm)) hcp).mono (by omega) (fun _ h => h)
    · have hcp := RDemonicExec.copy (B := .exact) (w := w) (d := mArenaWords) (s := mIwOld)
        (x := x) hL
      rw [h_iwo, ← Nat.max_eq_left (Nat.le_of_not_lt hlt)] at hcp
      exact RDemonicExec.branch_neg (c := .lt mIwOld mIwNew)
        (fun h : x.regs mIwOld < x.regs mIwNew => hlt (h_iwo.symm.trans_lt (h.trans_eq h_iwn))) hcp
  have hx₁b : x₁.Bounded w := hx.set (hfit_peak.of_le (by omega))
  set x₂ := x₁.set mCur 6
  have hex₂ := RDemonicExec.const (B := .exact) (d := mCur) (v := 6) (x := x₁) hL
    (hfit_peak.of_le (by omega))
  have hx₂b : x₂.Bounded w := hx₁b.set (hfit_peak.of_le (by omega))
  obtain ⟨hex₃, hx₃b⟩ := exec_add_bdd mArenaWords mArenaWords mCur arenaW hx₂b hL
    (by simp [x₂, x₁, RData.set]; rfl)
    (hfit_peak.of_le (by dsimp only [arenaW]; omega))
  set x₃ := x₂.set mArenaWords arenaW
  obtain ⟨hex₄, hx₄b⟩ := exec_add_bdd mArena mNewMeta mOffNew arenaB hx₃b hL
    (by simp [x₃, x₂, x₁, RData.set, h_nm, h_on]; rfl)
    (hfit_peak.of_le (by dsimp only [arenaB]; omega))
  set x₄ := x₃.set mArena arenaB
  obtain ⟨hex₅, hx₅b⟩ := exec_add_bdd mPeakFront mArena mArenaWords peakF hx₄b hL
    (by simp [x₄, x₃, RData.set]; rfl) hfit_peak
  set x₅ := x₄.set mPeakFront peakF
  have hiwo_le_aw : iwOld ≤ arenaW := (le_max_left _ _).trans (Nat.le_add_right _ 6)
  have hfr_le_peak : frOld ≤ peakF := by omega
  obtain ⟨hex₆, hx₆b⟩ := exec_sub_bdd mK mPeakFront mFr (peakF - frOld) hx₅b hL
    (by simpa [x₅, x₄, x₃, x₂, x₁, RData.set, h_fr] using hfr_le_peak)
    (by simp [x₅, x₄, x₃, x₂, x₁, RData.set, h_fr])
    (hfit_peak.of_le (Nat.sub_le _ _))
  set x₆ := x₅.set mK (peakF - frOld)
  obtain ⟨hex₇, hyb⟩ := exec_sub_bdd mOldItemDst mPeakFront mIwOld
    (arenaB + (arenaW - iwOld)) hx₆b hL
    (by simp [x₆, x₅, x₄, x₃, x₂, x₁, RData.set, h_iwo]; omega)
    (by simp [x₆, x₅, x₄, x₃, x₂, x₁, RData.set, h_iwo]; omega)
    (hfit_peak.of_le (by omega))
  set y := x₆.set mOldItemDst (arenaB + (arenaW - iwOld))
  refine ⟨y,
    (hex₁.seq_eq (hex₂.seq_eq (hex₃.seq_eq (hex₄.seq_eq (hex₅.seq_eq
      (hex₆.seq_eq hex₇)))))).mono (by omega) (fun _ h => h),
    hyb, rfl, rfl, by simp [y, x₆, x₅, x₄, x₃, RData.set],
    by simp [y, x₆, x₅, x₄, RData.set], by simp [y, x₆, x₅, RData.set],
    by simp [y, x₆, RData.set], by simp [y, RData.set], fun reg hreg => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
  simp [y, x₆, x₅, x₄, x₃, x₂, x₁, RData.set, hreg]


theorem migrateSetupParamsCode_exec {U V w N_old n n_init base : ℕ}
    {θ_old : QuotHashSeed U N_old} {s_abs : Dictionary.State U} {x : RData rResize}
    (hx : x.Bounded w) (hn : 1 ≤ n) (hev : EpochValid U n N_old)
    (hfr : x.frontier = base + compactedEpochWords U V w N_old n)
    (hfit_peak : Fits w (base + migratePeakWords U V w N_old n))
    (hsplit : CompactedSplitRep base (base + offCompItems U w N_old) U V w N_old n n_init θ_old
      s_abs ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base) :
    let N_new := targetCap U n
    let newMeta := base + offCompItems U w N_old
    let offNew := offCompItems U w N_new
    let iwOld := compactedItemWords U V w N_old n
    let iwNew := compactedItemWords U V w N_new n
    let arenaW := migrateArenaWords U V w N_old N_new n
    let arenaB := newMeta + offNew
    let peakF := base + migratePeakWords U V w N_old n
    ∃ (s₈ : RData rResize) (steps_p : ℕ),
      RDemonicExec w peakF migrateSetupParamsCode x steps_p (· = s₈) ∧
      steps_p ≤ (131 * migFactor + 350) * n ∧
      s₈.Bounded w ∧
      s₈.frontier = x.frontier ∧
      abiPreserved x s₈ ∧
      (∀ addr < base, s₈.mem addr = x.mem addr) ∧
      CompactedSplitRep base newMeta U V w N_old n n_init θ_old s_abs ⟨s₈.mem, s₈.frontier⟩ ∧
      s₈.regs mBase = base ∧
      s₈.regs mCnt = n ∧
      s₈.regs mNNew = N_new ∧
      s₈.regs mNewMeta = newMeta ∧
      s₈.regs mOffNew = offNew ∧
      s₈.regs mIwOld = iwOld ∧
      s₈.regs mIwNew = iwNew ∧
      s₈.regs mArena = arenaB ∧
      s₈.regs mPeakFront = peakF ∧
      s₈.regs mK = peakF - x.frontier ∧
      s₈.regs mOldItemDst = arenaB + (arenaW - iwOld) ∧
      (∀ i : Fin 19, s₈.regs (mOldHp i) =
        mkHashParams w (epochQBits U N_old) (epochHashB N_old) (totalMicroBits N_old) 3 i) ∧
      (∀ i : Fin 36, s₈.regs (mOldCp i) = mkCompParams U V w N_old i) ∧
      (∀ i : Fin 19, s₈.regs (mNewHp i) =
        mkHashParams w (epochQBits U N_new) (epochHashB N_new) (totalMicroBits N_new) 3 i) ∧
      (∀ i : Fin 36, s₈.regs (mNewCp i) = mkCompParams U V w N_new i) := by
  intro N_new newMeta offNew iwOld iwNew arenaW arenaB peakF
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  have hNU_old : N_old ≤ U := by rcases hev with ⟨rfl, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  have hn_old : n ≤ N_old := by rcases hev with ⟨rfl, _⟩ | ⟨_, hnN, _, _⟩ <;> omega
  have hnU : n ≤ U := hn_old.trans hNU_old
  obtain ⟨hN_new_pos, hn_new, hN_new_2n, hNU_new⟩ := targetCap_bounds_of_pos hn hnU
  have hce_old : compactedEpochWords U V w N_old n = offCompItems U w N_old + iwOld := by
    unfold compactedEpochWords; rw [ite_eq_right (by omega)]
  have h225_old : 225 ≤ offCompItems U w N_old := le_offCompItems_225 U w N_old
  have h225_new : 225 ≤ offNew := le_offCompItems_225 U w N_new
  have hpeak_eq : peakF = arenaB + arenaW := by
    dsimp only [peakF, arenaB, arenaW, newMeta, offNew, N_new, iwOld, iwNew, migratePeakWords]
    omega
  have hfit_ar : Fits w (arenaB + arenaW) := hpeak_eq ▸ hfit_peak
  have haw_def : arenaW = max iwOld iwNew + 6 := rfl
  have hiwn_le_aw : iwNew ≤ arenaW := (le_max_right _ _).trans (Nat.le_add_right _ 6)
  have hfr_le_peak : x.frontier ≤ peakF := by
    simp only [hfr, hce_old, hpeak_eq, arenaB, newMeta]; omega
  have hfit63 : Fits w 63 := hfit_ar.of_le (by dsimp only [arenaB]; omega)
  have hfit_n : Fits w n := hsplit.root_hdr.fits_U.of_le hnU
  obtain ⟨s₁, hex₁, hs₁b, hs₁m, hs₁f, habi₁, hs₁_cnt, hs₁_iwo, hs₁_nm, hs₁_fr, hs₁_nn,
      hs₁_ohp, hs₁_ocp⟩ :=
    migrateLoadOldCode_exec hx hn hev hfr hfr_le_peak hsplit hbase
  set s₂ := s₁.set mCur 63
  have hex₂ := RDemonicExec.const (B := .exact) (d := mCur) (v := 63) (x := s₁)
    (hs₁f.le.trans hfr_le_peak) hfit63
  have hs₁_base : s₁.regs mBase = base := habi₁.1.trans hbase
  obtain ⟨hex₃, hs₃b⟩ := exec_add_bdd mTmpA mBase mCur (base + 63)
    (hs₁b.set hfit63 : s₂.Bounded w) (hs₁f.le.trans hfr_le_peak)
    (by simp [RData.set, hs₁_base])
    (hfit_ar.of_le (by dsimp only [arenaB, newMeta]; omega))
  set s₃ := s₂.set mTmpA (base + 63)
  have hms₃ : memoryState mFr s₃.toData = ⟨x.mem, x.frontier⟩ :=
    Memory.State.ext hs₁m (by simp [memoryState, s₃, s₂, RData.set, RData.toData, hs₁_fr])
  have hin_wp1 : s₃.regs ∘ srcWriteParams =
      WordEncoding.encode (((base, base + 63), (N_new, (n, n)))) :=
    (regs_pairSrc
      (regs_pairSrc
        (regs_reg1_eq mBase (by simp [s₃, s₂, RData.set, hs₁_base]))
        (regs_reg1_eq mTmpA (by simp [s₃, RData.set])))
      (regs_pairSrc
        (regs_reg1_eq mNNew (by simp [s₃, s₂, RData.set, hs₁_nn]; rfl))
        (regs_pairSrc
          (regs_reg1_eq mCnt (by simp [s₃, s₂, RData.set, hs₁_cnt]))
          (regs_reg1_eq mCnt (by simp [s₃, s₂, RData.set, hs₁_cnt]))))).eq
  have hfit_dst1 : Fits w ((base + 63) + offNew) :=
    hfit_ar.of_le (by dsimp only [arenaB, newMeta]; omega)
  obtain ⟨hpre_wp1, hv_wp1, hres_wp1, hfr_wp1, _, hpar_wp1, hframe_wp1, hc_wp1⟩ :=
    writeEpochParamsGenProg_spec (s := ⟨x.mem, x.frontier⟩) (dstMetaBase := base + 63)
      (N := N_new) (n_cur := n) (n_init_new := n)
      hw hN_new_pos hNU_new hV hfit_n hfit_n hsplit.root_hdr
      (by change base + 5 ≤ x.frontier; rw [hfr, hce_old]; omega)
      (by change (base + 63) + 63 ≤ x.frontier; rw [hfr, hce_old]; omega)
      hfit_dst1
  obtain ⟨s₄, hex_wp1, hs₄b, hs₄f, hm_wp1, hout_wp1, hframe_reg_wp1⟩ :=
    execWitness wWriteParams factor_wWriteParams_le mFr srcWriteParams tmpWriteParams
      tmpWriteParams_inj srcWriteParams_ne_tmp tmpWriteParams_ne_mFr srcWriteParams_ne_mFr
      ((base, base + 63), (N_new, (n, n))) hs₃b (hs₁f.le.trans hfr_le_peak)
      hin_wp1 (hms₃ ▸ hpre_wp1) (hms₃ ▸ hv_wp1)
      (by rw [hms₃, hfr_wp1]; exact hs₁f.symm.le)
  simp only [hms₃, hres_wp1] at hm_wp1 hout_wp1 hex_wp1
  have hs₄f_eq : s₄.frontier = x.frontier := hs₄f.trans hs₁f
  have hs₄_fr_reg : s₄.regs mFr = x.frontier :=
    (congrArg Memory.State.frontier hm_wp1).trans hfr_wp1
  have hs₄_off : s₄.regs mOffNew = offNew := by
    rw [← tmpWriteParams_out_0, hout_wp1 0]; rfl
  have hs₄_mem_eq : s₄.mem = ((Memory.spec 0).clientState ⟨x.mem, x.frontier⟩
      (writeEpochParamsGenProg ((base, base + 63), (N_new, (n, n))))).mem :=
    congrArg Memory.State.mem hm_wp1
  have hs₄_out : ∀ a, (a < base + offScratch ∨ base + epochHdrWords ≤ a) → s₄.mem a = x.mem a :=
    fun a ha => hs₄_mem_eq ▸ hframe_wp1 a (by simp only [offScratch, epochHdrWords] at *; omega)
  have hsplit₄ : CompactedSplitRep base newMeta U V w N_old n n_init θ_old s_abs
      ⟨s₄.mem, s₄.frontier⟩ :=
    compactedSplitRep_of_scratch_mod hw hsplit hs₄f_eq hs₄_out
  have hs₄_keep : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mOffNew → reg ≠ mHSpaceNew →
      s₄.regs reg = s₃.regs reg := fun reg hfr' h160 ho hh =>
    hframe_reg_wp1 reg hfr'
      (mkTmp_ne_reg _ h160 (fun a => by fin_cases a <;> [exact ho.symm; exact hh.symm]))
  have hs₄_base : s₄.regs mBase = base :=
    (hs₄_keep mBase (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
      (mReg_ne (by decide))).trans (by simp [s₃, s₂, RData.set, hs₁_base])
  obtain ⟨s₅, hex_nhp, hs₅b, hs₅m, hs₅f, hs₅_nhp, hs₅_r⟩ :=
    loadBlockUpTo_exec mBase mCur (mReg_ne (by decide)) mNewHp mNewHp_inj
      (fun i => mNewHp_ne_mReg i (Or.inl (by decide)))
      (fun i => mNewHp_ne_mReg i (Or.inl (by decide)))
      (63 + offHashParams) 18 (by decide) hs₄b (hs₄f_eq.le.trans hfr_le_peak) hs₄_base
      (by change base + (63 + 8) + 19 ≤ s₄.frontier; rw [hs₄f_eq, hfr, hce_old]; omega)
  have hs₅_base : s₅.regs mBase = base :=
    (hs₅_r mBase (mReg_ne (by decide)) (fun i => mNewHp_ne_mReg i (Or.inl (by decide)))).trans
      hs₄_base
  obtain ⟨s₆, hex_ncp, hs₆b, hs₆m, hs₆f, hs₆_ncp, hs₆_r⟩ :=
    loadBlockUpTo_exec mBase mCur (mReg_ne (by decide)) mNewCp mNewCp_inj
      (fun i => mNewCp_ne_mReg i (Or.inl (by decide)))
      (fun i => mNewCp_ne_mReg i (Or.inl (by decide)))
      (63 + offCompParams) 35 (by decide) hs₅b ((hs₅f.trans hs₄f_eq).le.trans hfr_le_peak) hs₅_base
      (by change base + (63 + 27) + 36 ≤ s₅.frontier; rw [hs₅f, hs₄f_eq, hfr, hce_old]; omega)
  have hs₆m_eq : s₆.mem = s₄.mem := hs₆m.trans hs₅m
  have hs₆f_eq : s₆.frontier = x.frontier := hs₆f.trans (hs₅f.trans hs₄f_eq)
  have hs₆_nhp_all : ∀ i : Fin 19, s₆.regs (mNewHp i) =
      mkHashParams w (epochQBits U N_new) (epochHashB N_new) (totalMicroBits N_new) 3 i :=
    fun i => by
      rw [hs₆_r (mNewHp i) (mNewHp_ne_mReg i (Or.inl (by decide)))
        (fun j => by intro h; have hv := congrArg Fin.val h; simp at hv; omega),
        hs₅_nhp i (by omega), hs₄_mem_eq, ← Nat.add_assoc base 63]
      exact hpar_wp1.hp_eq i
  have hs₆_ncp_all : ∀ i : Fin 36, s₆.regs (mNewCp i) = mkCompParams U V w N_new i := fun i => by
    rw [hs₆_ncp i (by omega), hs₅m, hs₄_mem_eq, ← Nat.add_assoc base 63]
    exact hpar_wp1.cp_eq i
  have hs₆_keep4 : ∀ {c : Fin 160}, (c.val < 90 ∨ 146 ≤ c.val) → c ≠ 9 →
      s₆.regs (mReg c) = s₄.regs (mReg c) := fun {c} hc h9 => by
    rw [hs₆_r (mReg c) (mReg_ne h9) (fun i => mNewCp_ne_mReg i (by omega)),
      hs₅_r (mReg c) (mReg_ne h9) (fun i => mNewHp_ne_mReg i (by omega))]
  have hs₆_cnt : s₆.regs mCnt = n :=
    (hs₆_keep4 (c := 13) (Or.inl (by decide)) (by decide)).trans <|
      (hs₄_keep mCnt (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
        (mReg_ne (by decide))).trans (by simp [s₃, s₂, RData.set, hs₁_cnt])
  have hs₆_fr_reg : s₆.regs mFr = x.frontier :=
    (hs₆_keep4 (c := 1) (Or.inl (by decide)) (by decide)).trans hs₄_fr_reg
  have hin_niw : s₆.regs ∘ srcNewIw = WordEncoding.encode (mkCompParams U V w N_new, n) :=
    (regs_pairSrc (regs_cp_eq hs₆_ncp_all) (regs_reg1_eq mCnt hs₆_cnt)).eq
  have hfit_niw4 : Fits w (4 + iwNew) :=
    hfit_ar.of_le (by rw [haw_def]; dsimp only [arenaB]; omega)
  have hsafe_niw : CompItemWordsPre w (mkCompParams U V w N_new, n) (memoryState mFr s₆.toData) :=
    ⟨U, V, N_new, hw, hNU_new, hU, hV, rfl, fits_wOffQ_add_three_of_itemWords hw hfit_niw4⟩
  have hv_niw := validProg_compItemWordsGen (mkCompParams U V w N_new, n)
    (memoryState mFr s₆.toData)
    ⟨wellFormed_memoryState hs₆b.1, Nat.zero_le _⟩
  obtain ⟨s₇, hex_niw, hs₇b, hs₇f, hm_niw, hout_niw, hframe_niw⟩ :=
    execWitness wItemWords factor_mItemWords_le mFr srcNewIw tmpNewIw
      tmpNewIw_inj srcNewIw_ne_tmp tmpNewIw_ne_mFr srcNewIw_ne_mFr
      (mkCompParams U V w N_new, n) hs₆b (hs₆f_eq.le.trans hfr_le_peak)
      hin_niw hsafe_niw hv_niw
      (by rw [clientState_compItemWordsGenProg]; change s₆.regs mFr ≤ s₆.frontier; omega)
  rw [memoryCost_compItemWordsGenProg, zero_add, mul_one] at hex_niw
  rw [clientState_compItemWordsGenProg] at hm_niw
  have hs₇m_eq : s₇.mem = s₄.mem := (congrArg Memory.State.mem hm_niw).trans hs₆m_eq
  have hs₇f_eq : s₇.frontier = x.frontier := hs₇f.trans hs₆f_eq
  have hs₇_fr_reg : s₇.regs mFr = x.frontier :=
    (congrArg Memory.State.frontier hm_niw).trans hs₆_fr_reg
  have hs₇_iwn : s₇.regs mIwNew = iwNew := by
    have h0 := hout_niw 0; rwa [tmpNewIw_out, clientResult_compItemWordsGenProg hw] at h0
  have hs₇_keep6 : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mIwNew → s₇.regs reg = s₆.regs reg :=
    fun reg h1 h160 hiw => hframe_niw reg h1
      (mkTmp_ne_reg _ h160 (fun a => by fin_cases a; exact hiw.symm))
  have hs₇_nm : s₇.regs mNewMeta = newMeta :=
    (hs₇_keep6 mNewMeta (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
    (hs₆_keep4 (c := 146) (Or.inr (by decide)) (by decide)).trans <|
    (hs₄_keep mNewMeta (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
      (mReg_ne (by decide))).trans (by simp [s₃, s₂, RData.set, hs₁_nm, newMeta])
  have hs₇_off : s₇.regs mOffNew = offNew :=
    (hs₇_keep6 mOffNew (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
    (hs₆_keep4 (c := 150) (Or.inr (by decide)) (by decide)).trans hs₄_off
  have hs₇_iwo : s₇.regs mIwOld = iwOld :=
    (hs₇_keep6 mIwOld (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
    (hs₆_keep4 (c := 152) (Or.inr (by decide)) (by decide)).trans <|
    (hs₄_keep mIwOld (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
      (mReg_ne (by decide))).trans (by simp [s₃, s₂, RData.set, hs₁_iwo, iwOld])
  obtain ⟨s₈, hex_ca, hs₈b, hs₈m, hs₈f, hs₈_aw, hs₈_ar, hs₈_pf, hs₈_k, hs₈_oid, hs₈_keep⟩ :=
    migrateComputeArenaCode_exec hs₇b (hs₇f_eq.le.trans hfr_le_peak)
      (by rw [hfr, hce_old]; dsimp only [newMeta]; omega)
      (by simpa only [arenaB, haw_def] using hfit_ar)
      hs₇_nm hs₇_off hs₇_iwo hs₇_iwn hs₇_fr_reg
  have hs₈m_eq : s₈.mem = s₄.mem := hs₈m.trans hs₇m_eq
  have hs₈f_eq : s₈.frontier = x.frontier := hs₈f.trans hs₇f_eq
  have hf1 := one_le_migFactor
  have hex_params :=
    hex₁.seq_eq (hex₂.seq_eq (hex₃.seq_eq
      ((hex_wp1.mono (Nat.mul_le_mul_left migFactor (by omega : _ ≤ 22 * n + 101))
        (fun _ h => h)).seq_eq (hex_nhp.seq_eq (hex_ncp.seq_eq (hex_niw.seq_eq hex_ca))))))
  have hs₈_new : ∀ reg : Fin rResize, 16 ≤ reg.val ∧ reg.val < 146 → s₈.regs reg = s₆.regs reg :=
    fun reg h => (hs₈_keep reg (by clear * - h; simp [Fin.ext_iff]; omega)).trans <|
      hs₇_keep6 reg (by clear * - h; simp [Fin.ext_iff]; omega) (by omega)
        (by clear * - h; simp [Fin.ext_iff]; omega)
  have hs₈_s₁ : ∀ reg : Fin rResize, reg.val < 160 → (reg.val < 90 ∨ 146 ≤ reg.val) →
      reg ∉ ([mFr, mIwNew, mArenaWords, mCur, mArena, mPeakFront, mK, mOldItemDst, mOffNew,
        mHSpaceNew, mTmpA] : List (Fin rResize)) → s₈.regs reg = s₁.regs reg :=
    fun reg h160 hr h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      obtain ⟨h1, hiwn, haw, hcur, har, hpf, hk, hoid, hoff, hhs, hta⟩ := h
      rw [hs₈_keep reg (by simp [haw, hcur, har, hpf, hk, hoid]), hs₇_keep6 reg h1 h160 hiwn,
        hs₆_r reg hcur (fun i h => by clear * - h hr; rw [← h, val_mNewCp] at hr; omega),
        hs₅_r reg hcur (fun i h => by clear * - h hr; rw [← h, val_mNewHp] at hr; omega),
        hs₄_keep reg h1 h160 hoff hhs]
      exact (Function.update_of_ne hta _ _).trans (Function.update_of_ne hcur _ _)
  have hs₈_old : ∀ reg : Fin rResize, 16 ≤ reg.val ∧ reg.val < 90 → s₈.regs reg = s₁.regs reg :=
    fun reg h => hs₈_s₁ reg (by omega) (Or.inl h.2) (by clear * - h; simp [Fin.ext_iff]; omega)
  refine ⟨s₈, _, hex_params, by nlinarith only [hn, hf1], hs₈b, hs₈f_eq,
    abiPreserved_trans habi₁ ⟨hs₈_s₁ _ (mReg_lt_160 _) (by simp) (by simp),
      hs₈_s₁ _ (mReg_lt_160 _) (by simp) (by simp), hs₈_s₁ _ (mReg_lt_160 _) (by simp) (by simp),
      hs₈_s₁ _ (mReg_lt_160 _) (by simp) (by simp)⟩,
    fun addr haddr => (congrFun hs₈m_eq addr).trans
      (hs₄_out addr (Or.inl (by unfold offScratch; omega))),
    Memory.State.ext (x := ⟨s₈.mem, s₈.frontier⟩) (y := ⟨s₄.mem, s₄.frontier⟩)
      hs₈m_eq (hs₈f_eq.trans hs₄f_eq.symm) ▸ hsplit₄,
    (hs₈_s₁ _ (mReg_lt_160 _) (by simp) (by simp)).trans hs₁_base,
    (hs₈_s₁ _ (mReg_lt_160 _) (by simp) (by simp)).trans hs₁_cnt,
    (hs₈_s₁ _ (mReg_lt_160 _) (by simp) (by simp)).trans hs₁_nn,
    (hs₈_keep _ (by simp)).trans hs₇_nm, (hs₈_keep _ (by simp)).trans hs₇_off,
    (hs₈_keep _ (by simp)).trans hs₇_iwo, (hs₈_keep _ (by simp)).trans hs₇_iwn,
    hs₈_ar, hs₈_pf.trans hpeak_eq.symm,
    hs₈_k.trans (congrArg (· - x.frontier) hpeak_eq.symm), hs₈_oid,
    fun i => (hs₈_old _ (by simp only [val_mOldHp]; omega)).trans (hs₁_ohp i),
    fun i => (hs₈_old _ (by simp only [val_mOldCp]; omega)).trans (hs₁_ocp i),
    fun i => (hs₈_new _ (by simp only [val_mNewHp]; omega)).trans (hs₆_nhp_all i),
    fun i => (hs₈_new _ (by simp only [val_mNewCp]; omega)).trans (hs₆_ncp_all i)⟩


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
