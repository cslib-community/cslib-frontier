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
# Post-Rebuild Leftward Compaction and Tail Shrink (`migrateCompactBackCode`)

Internal second half of `migrateFinishCleanCode`: copies the rebuilt metadata and item regions
leftward from `(mNewMeta, mArena)` back to `(base, base + offNew)` and shrinks `[frNew, peakF)`.
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

/-- Second half of `migrateFinishCleanCode`: copies `(mNewMeta, mArena)` leftward to
`(base, base + offNew)` and shrinks `[frNew, peakF)`. -/
noncomputable def migrateCompactBackCode : RCode .exact rResize :=
  .seq (.op (.copy mTmpA mNewMeta)) <|
  .seq (.op (.copy mTmpB mBase)) <|
  .seq (.op (.copy mCur mOffNew)) <|
  .seq (RCode.ofCode (wCopyLeft.code mFr srcCopyLeft tmpCopyLeft)) <|
  .seq (.op (.exactBin .add mItemBase mBase mOffNew)) <|
  .seq (.op (.copy mTmpA mArena)) <|
  .seq (.op (.copy mTmpB mItemBase)) <|
  .seq (.op (.copy mCur mIwNew)) <|
  .seq (RCode.ofCode (wCopyLeft.code mFr srcCopyLeft tmpCopyLeft)) <|
  .seq (.op (.exactBin .add mCur mItemBase mIwNew)) <|
  .seq (.op (.exactBin .sub mK mPeakFront mCur))
       (shrinkCode mK mIdx mZero mOne)

theorem not_readsWidth_migrateCompactBackCode : ¬migrateCompactBackCode.ReadsWidth := by
  simp [migrateCompactBackCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    shrinkCode_not_readsWidth]

theorem migrateCompactBackCode_exec {U V w N_old N_new n base : ℕ}
    {θ_new : QuotHashSeed U N_new} {s_abs : Dictionary.State U} {z₄ : RData rResize}
    (hw : 0 < w) (hn : 1 ≤ n) (hev : EpochValid U n N_old)
    (hNU_new : N_new ≤ U) (hN_new_2n : N_new ≤ 2 * n)
    (hcard : (Dictionary.dom s_abs).card = n)
    (hvals : Dictionary.ValuesBounded V s_abs)
    (hfit_peak : Fits w (base + migratePeakWords U V w N_old n))
    (hpeak_eq : base + migratePeakWords U V w N_old n =
      base + offCompItems U w N_old + offCompItems U w N_new +
        migrateArenaWords U V w N_old N_new n)
    (hz₄b : z₄.Bounded w)
    (hz₄f_eq : z₄.frontier = base + migratePeakWords U V w N_old n)
    (hz₄_fr_reg : z₄.regs mFr = base + migratePeakWords U V w N_old n)
    (hz₄_nm : z₄.regs mNewMeta = base + offCompItems U w N_old)
    (hz₄_base : z₄.regs mBase = base)
    (hz₄_off : z₄.regs mOffNew = offCompItems U w N_new)
    (hz₄_ar : z₄.regs mArena = base + offCompItems U w N_old + offCompItems U w N_new)
    (hz₄_iwn : z₄.regs mIwNew = compactedItemWords U V w N_new n)
    (hz₄_pf : z₄.regs mPeakFront = base + migratePeakWords U V w N_old n)
    (hhdr_z₄ : RootHeaderValid U V w N_new n n (base + offCompItems U w N_old) z₄.mem)
    (hpar_z₄ : EpochParamsStored U V w N_new (base + offCompItems U w N_old) z₄.mem)
    (hrep_z₄ : ReducedKWise.Rep (base + offCompItems U w N_old + epochHdrWords) w
      (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 θ_new z₄.mem)
    (hcpl_z₄ : ∃ s_fix' : Memory.State,
      DictStateInv U V (ghostW w) N_new 0 θ_new s_abs s_fix' ∧
      FixedCoupled (base + offCompItems U w N_old)
        (base + offCompItems U w N_old + offCompItems U w N_new)
        U V w N_new s_fix' ⟨z₄.mem, base + migratePeakWords U V w N_old n⟩) :
    let peakF := base + migratePeakWords U V w N_old n
    ∃ (z : RData rResize) (steps_back : ℕ),
      RDemonicExec w peakF migrateCompactBackCode z₄ steps_back (· = z) ∧
      steps_back ≤ (1900 * migFactor + 9620) * n ∧
      z.Bounded w ∧
      z.frontier = base + compactedEpochWords U V w N_new n ∧
      CompactedSplitRep base (base + offCompItems U w N_new) U V w N_new n n θ_new s_abs
        ⟨z.mem, z.frontier⟩ ∧
      compGmAt base U w N_new z.mem =
        compGmAt (base + offCompItems U w N_old) U w N_new z₄.mem ∧
      abiPreserved z₄ z ∧
      (∀ addr < base, z.mem addr = z₄.mem addr) := by
  intro peakF
  obtain ⟨_, hU, hV⟩ := rootHeaderValid_bounds hz₄b hhdr_z₄
  set newMeta := base + offCompItems U w N_old
  set offNew := offCompItems U w N_new
  set iwNew := compactedItemWords U V w N_new n
  set arenaW := migrateArenaWords U V w N_old N_new n
  set arenaB := newMeta + offNew
  have h225_old : 225 ≤ offCompItems U w N_old := le_offCompItems_225 U w N_old
  have h225_new : 225 ≤ offNew := le_offCompItems_225 U w N_new
  have hpeak_ar : peakF = arenaB + arenaW := hpeak_eq
  have hfit_ar : Fits w (arenaB + arenaW) := hpeak_ar ▸ hfit_peak
  have hiwn_le_aw : iwNew ≤ arenaW := (le_max_right _ _).trans (Nat.le_add_right _ 6)
  have hfit_nm : Fits w (newMeta + offNew) := hfit_ar.of_le (Nat.le_add_right _ _)
  have hfit1 : Fits w 1 := hfit_nm.of_le (by linarith only [h225_new])
  -- Leftward copy #1: `[newMeta, newMeta + offNew)` -> `[base, base + offNew)`
  set z₅ := z₄.set mTmpA newMeta
  have hex_c5 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := peakF)
    (d := mTmpA) (s := mNewMeta) (x := z₄) hz₄f_eq.le
  rw [hz₄_nm] at hex_c5
  set z₆ := z₅.set mTmpB base
  have hex_c6 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := peakF)
    (d := mTmpB) (s := mBase) (x := z₅) hz₄f_eq.le
  have hz₅_base : z₅.regs mBase = base := by simp [z₅, RData.set, hz₄_base]
  rw [hz₅_base] at hex_c6
  set z₇ := z₆.set mCur offNew
  have hex_c7 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := peakF)
    (d := mCur) (s := mOffNew) (x := z₆) hz₄f_eq.le
  have hz₆_off : z₆.regs mOffNew = offNew := by simp [z₆, z₅, RData.set, hz₄_off]
  rw [hz₆_off] at hex_c7
  have hz₇b : z₇.Bounded w :=
    ((hz₄b.set (hfit_nm.of_le (Nat.le_add_right _ _))).set
      (hfit_nm.of_le (by dsimp only [newMeta]; linarith only [h225_old]))).set
      (hfit_nm.of_le (Nat.le_add_left _ _))
  have hms₇ : memoryState mFr z₇.toData = ⟨z₄.mem, peakF⟩ :=
    Memory.State.ext rfl (by
      dsimp only [memoryState, z₇, z₆, z₅, RData.set, RData.toData]
      rw [Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mCur),
        Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mTmpB),
        Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mTmpA)]
      exact hz₄_fr_reg)
  have hin_cl1 : z₇.regs ∘ srcCopyLeft = WordEncoding.encode ((newMeta, base), offNew) :=
    (regs_pairSrc
      (regs_pairSrc (regs_reg1_eq mTmpA (by simp [z₇, z₆, z₅, RData.set]))
        (regs_reg1_eq mTmpB (by simp [z₇, z₆, RData.set])))
      (regs_reg1_eq mCur (by simp [z₇, RData.set]))).eq
  obtain ⟨hpre_cl1, hv_cl1, hc_cl1, hfr_cl1, hcp_cl1, hout_cl1⟩ :=
    copyLeftwardProg_spec (w := w) (srcBase := newMeta) (dstBase := base) (len := offNew)
      (s₀ := ⟨z₄.mem, peakF⟩) (fun a _ => hz₄b.mem_fits a)
      (Nat.le_add_right _ _)
      (by change newMeta + offNew ≤ peakF; rw [hpeak_ar]; exact Nat.le_add_right _ _) hfit1
  obtain ⟨z₈, hex_cl1, hz₈b, hz₈f, hm_cl1, _, hframe_reg_cl1⟩ :=
    execWitness wCopyLeft factor_wCopyLeft_le mFr srcCopyLeft tmpCopyLeft
      tmpCopyLeft_inj srcCopyLeft_ne_tmp tmpCopyLeft_ne_mFr srcCopyLeft_ne_mFr
      ((newMeta, base), offNew) hz₇b hz₄f_eq.le
      hin_cl1 (hms₇ ▸ hpre_cl1) (hms₇ ▸ hv_cl1)
      (by rw [hms₇, hfr_cl1]; exact hz₄f_eq.symm.le)
  rw [hms₇] at hm_cl1 hex_cl1
  have hz₈f_eq : z₈.frontier = peakF := hz₈f.trans hz₄f_eq
  have hz₈_fr_reg : z₈.regs mFr = peakF := (congrArg Memory.State.frontier hm_cl1).trans hfr_cl1
  have hz₈_mem_eq : z₈.mem = ((Memory.spec 0).clientState ⟨z₄.mem, peakF⟩
      (copyLeftwardProg ((newMeta, base), offNew))).mem :=
    congrArg Memory.State.mem hm_cl1
  have hz₈_keep7 : ∀ reg, reg ≠ mFr → reg.val < 160 → z₈.regs reg = z₇.regs reg :=
    fun reg h1 h160 => hframe_reg_cl1 reg h1 (mkTmp_ne_reg _ h160 (fun a => Fin.elim0 a))
  -- Leftward copy #2: `[arenaB, arenaB + iwNew)` -> `[base + offNew, base + offNew + iwNew)`
  have hz₈_base : z₈.regs mBase = base :=
    (hz₈_keep7 mBase (mReg_ne (by decide)) (mReg_lt_160 _)).trans
      (by simp [z₇, z₆, z₅, RData.set, hz₄_base])
  have hz₈_off : z₈.regs mOffNew = offNew :=
    (hz₈_keep7 mOffNew (mReg_ne (by decide)) (mReg_lt_160 _)).trans
      (by simp [z₇, z₆, z₅, RData.set, hz₄_off])
  have hz₈_ar : z₈.regs mArena = arenaB :=
    (hz₈_keep7 mArena (mReg_ne (by decide)) (mReg_lt_160 _)).trans
      (by simp [z₇, z₆, z₅, RData.set, hz₄_ar])
  have hz₈_iwn : z₈.regs mIwNew = iwNew :=
    (hz₈_keep7 mIwNew (mReg_ne (by decide)) (mReg_lt_160 _)).trans
      (by simp [z₇, z₆, z₅, RData.set, hz₄_iwn])
  have hz₈_pf : z₈.regs mPeakFront = peakF :=
    (hz₈_keep7 mPeakFront (mReg_ne (by decide)) (mReg_lt_160 _)).trans
      (by simp [z₇, z₆, z₅, RData.set, hz₄_pf, peakF])
  set z₉ := z₈.set mItemBase (base + offNew)
  have hfit_ib : Fits w (base + offNew) :=
    hfit_nm.of_le (by dsimp only [newMeta]; linarith only [h225_old])
  have hex_ib := RDemonicExec.exactBin (f := .add) (d := mItemBase) (i := mBase) (j := mOffNew)
    (w := w) (L_peak := peakF) (x := z₈) hz₈f_eq.le (v := base + offNew)
    (by simp [BinOp.evalExact, hz₈_base, hz₈_off]) hfit_ib
  set z₁₀ := z₉.set mTmpA arenaB
  have hex_c10 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := peakF)
    (d := mTmpA) (s := mArena) (x := z₉) hz₈f_eq.le
  have hz₉_ar : z₉.regs mArena = arenaB := by simp [z₉, RData.set, hz₈_ar]
  rw [hz₉_ar] at hex_c10
  set z₁₁ := z₁₀.set mTmpB (base + offNew)
  have hex_c11 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := peakF)
    (d := mTmpB) (s := mItemBase) (x := z₁₀) hz₈f_eq.le
  have hz₁₀_ib : z₁₀.regs mItemBase = base + offNew := by simp [z₁₀, z₉, RData.set]
  rw [hz₁₀_ib] at hex_c11
  set z₁₂ := z₁₁.set mCur iwNew
  have hex_c12 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := peakF)
    (d := mCur) (s := mIwNew) (x := z₁₁) hz₈f_eq.le
  have hz₁₁_iwn : z₁₁.regs mIwNew = iwNew := by simp [z₁₁, z₁₀, z₉, RData.set, hz₈_iwn]
  rw [hz₁₁_iwn] at hex_c12
  have hz₁₂b : z₁₂.Bounded w :=
    (((hz₈b.set hfit_ib).set hfit_nm).set hfit_ib).set
      (hfit_ar.of_le (by linarith only [hiwn_le_aw]))
  have hms₁₂ : memoryState mFr z₁₂.toData = ⟨z₈.mem, peakF⟩ :=
    Memory.State.ext rfl (by
      dsimp only [memoryState, z₁₂, z₁₁, z₁₀, z₉, RData.set, RData.toData]
      rw [Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mCur),
        Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mTmpB),
        Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mTmpA),
        Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mItemBase)]
      exact hz₈_fr_reg)
  have hin_cl2 : z₁₂.regs ∘ srcCopyLeft = WordEncoding.encode ((arenaB, base + offNew), iwNew) :=
    (regs_pairSrc
      (regs_pairSrc (regs_reg1_eq mTmpA (by simp [z₁₂, z₁₁, z₁₀, RData.set]))
        (regs_reg1_eq mTmpB (by simp [z₁₂, z₁₁, RData.set])))
      (regs_reg1_eq mCur (by simp [z₁₂, RData.set]))).eq
  obtain ⟨hpre_cl2, hv_cl2, hc_cl2, hfr_cl2, hcp_cl2, hout_cl2⟩ :=
    copyLeftwardProg_spec (w := w) (srcBase := arenaB) (dstBase := base + offNew) (len := iwNew)
      (s₀ := ⟨z₈.mem, peakF⟩) (fun a _ => hz₈b.mem_fits a)
      (by dsimp only [arenaB, newMeta]; linarith only [h225_old])
      (by change arenaB + iwNew ≤ peakF; rw [hpeak_ar]; exact Nat.add_le_add_left hiwn_le_aw _)
      hfit1
  obtain ⟨z₁₃, hex_cl2, hz₁₃b, hz₁₃f, hm_cl2, _, hframe_reg_cl2⟩ :=
    execWitness wCopyLeft factor_wCopyLeft_le mFr srcCopyLeft tmpCopyLeft
      tmpCopyLeft_inj srcCopyLeft_ne_tmp tmpCopyLeft_ne_mFr srcCopyLeft_ne_mFr
      ((arenaB, base + offNew), iwNew) hz₁₂b hz₈f_eq.le
      hin_cl2 (hms₁₂ ▸ hpre_cl2) (hms₁₂ ▸ hv_cl2)
      (by rw [hms₁₂, hfr_cl2]; exact hz₈f_eq.symm.le)
  rw [hms₁₂] at hm_cl2 hex_cl2
  have hz₁₃f_eq : z₁₃.frontier = peakF := hz₁₃f.trans hz₈f_eq
  have hz₁₃_mem_eq : z₁₃.mem = ((Memory.spec 0).clientState ⟨z₈.mem, peakF⟩
      (copyLeftwardProg ((arenaB, base + offNew), iwNew))).mem :=
    congrArg Memory.State.mem hm_cl2
  have hz₁₃_keep12 : ∀ reg, reg ≠ mFr → reg.val < 160 → z₁₃.regs reg = z₁₂.regs reg :=
    fun reg h1 h160 => hframe_reg_cl2 reg h1 (mkTmp_ne_reg _ h160 (fun a => Fin.elim0 a))
  -- Shrink `[frNew, peakF)`
  have hz₁₃_ib : z₁₃.regs mItemBase = base + offNew :=
    (hz₁₃_keep12 mItemBase (mReg_ne (by decide)) (mReg_lt_160 _)).trans
      (by simp [z₁₂, z₁₁, z₁₀, z₉, RData.set])
  have hz₁₃_iwn : z₁₃.regs mIwNew = iwNew :=
    (hz₁₃_keep12 mIwNew (mReg_ne (by decide)) (mReg_lt_160 _)).trans
      (by simp [z₁₂, z₁₁, z₁₀, z₉, RData.set, hz₈_iwn])
  have hz₁₃_pf : z₁₃.regs mPeakFront = peakF :=
    (hz₁₃_keep12 mPeakFront (mReg_ne (by decide)) (mReg_lt_160 _)).trans
      (by simp [z₁₂, z₁₁, z₁₀, z₉, RData.set, hz₈_pf])
  let frNew := base + offNew + iwNew
  have hfrNew_le : frNew ≤ peakF := by
    rw [hpeak_ar]; dsimp only [frNew, arenaB, newMeta]
    linarith only [h225_old, hiwn_le_aw]
  set z₁₄ := z₁₃.set mCur frNew
  have hex_c14 := RDemonicExec.exactBin (f := .add) (d := mCur) (i := mItemBase) (j := mIwNew)
    (w := w) (L_peak := peakF) (x := z₁₃) hz₁₃f_eq.le (v := frNew)
    (by simp [BinOp.evalExact, hz₁₃_ib, hz₁₃_iwn, frNew]) (hfit_peak.of_le hfrNew_le)
  set z₁₅ := z₁₄.set mK (peakF - frNew)
  have hex_c15 := RDemonicExec.exactBin (f := .sub) (d := mK) (i := mPeakFront) (j := mCur)
    (w := w) (L_peak := peakF) (x := z₁₄) hz₁₃f_eq.le (v := peakF - frNew)
    (by simp [BinOp.evalExact, z₁₄, RData.set, hz₁₃_pf, hfrNew_le])
    (hfit_peak.of_le (Nat.sub_le _ _))
  have hz₁₅b : z₁₅.Bounded w :=
    (hz₁₃b.set (hfit_peak.of_le hfrNew_le)).set (hfit_peak.of_le (Nat.sub_le _ _))
  have hz₁₅_k : z₁₅.regs mK = peakF - frNew := by simp [z₁₅, RData.set]
  have hsub_le_z15 : z₁₅.regs mK ≤ z₁₅.frontier := by
    rw [hz₁₅_k, show z₁₅.frontier = peakF from hz₁₃f_eq]; exact Nat.sub_le _ _
  have hsub_frNew : z₁₅.frontier - z₁₅.regs mK = frNew := by
    rw [show z₁₅.frontier = peakF from hz₁₃f_eq, hz₁₅_k]; exact Nat.sub_sub_self hfrNew_le
  have hex_sh := shrinkCode_exec (w := w) (L_peak := peakF)
    (count := mK) (idx := mIdx) (zero := mZero) (one := mOne)
    hz₁₅b mShrink_nodup hfit1 hz₁₃f_eq.le hsub_le_z15
  rw [hz₁₅_k] at hex_sh
  set z := shrinkPost mK mIdx mZero mOne z₁₅
  have hzb : z.Bounded w := shrinkPost_bounded hz₁₅b hfit1 hsub_le_z15
  have hce_new : compactedEpochWords U V w N_new n = offNew + iwNew := by
    unfold compactedEpochWords; rw [ite_eq_right (Nat.ne_of_gt hn)]
  have hzf : z.frontier = base + compactedEpochWords U V w N_new n := by
    change z₁₅.frontier - z₁₅.regs mK = _
    rw [hsub_frNew, hce_new]; dsimp only [frNew]; ring
  have hz_clear_lt : ∀ a < frNew, z.mem a = z₁₃.mem a := fun a ha => by
    change clear z₁₃.mem (z₁₅.frontier - z₁₅.regs mK) (z₁₅.regs mK) a = z₁₃.mem a
    rw [hsub_frNew]
    exact clear_of_not_owns (by simp only [Block.Owns, not_and_or, not_le]; exact Or.inl ha)
  have hmeta_reloc : ∀ j < offNew, z.mem (base + j) = z₄.mem (newMeta + j) := fun j hj => by
    rw [hz_clear_lt (base + j) (by dsimp only [frNew]; linarith only [hj]),
      hz₁₃_mem_eq, hout_cl2 (base + j) (fun h => by linarith only [hj, h.1]),
      hz₈_mem_eq, hcp_cl1 j hj]
  have hitem_reloc : ∀ j < iwNew, z.mem (base + offNew + j) = z₄.mem (arenaB + j) := fun j hj => by
    rw [hz_clear_lt (base + offNew + j) (by dsimp only [frNew]; linarith only [hj]),
      hz₁₃_mem_eq, hcp_cl2 j hj, hz₈_mem_eq,
      hout_cl1 (arenaB + j) (fun h => by
        dsimp only [arenaB, newMeta] at h; linarith only [h.2, h225_old])]
  obtain ⟨hsplit_z, hgm_z⟩ := compactedSplitRep_of_reloc (s_src := ⟨z₄.mem, peakF⟩)
    (s_dst := ⟨z.mem, z.frontier⟩) (srcItemBase := arenaB) hw hhdr_z₄ hpar_z₄
    hrep_z₄ hcard hvals hcpl_z₄ hmeta_reloc hitem_reloc
  have hz_abi_of : ∀ reg : Fin rResize, reg.val < 5 → reg ≠ mFr → z.regs reg = z₄.regs reg :=
    fun reg hlt5 hne_fr => by
      have h160 : reg.val < 160 := Nat.lt_trans hlt5 (by decide)
      have hne_idx : reg ≠ mIdx := ne_mReg_of_lt_five hlt5 (by decide)
      have hne_one : reg ≠ mOne := ne_mReg_of_lt_five hlt5 (by decide)
      have hne_zero : reg ≠ mZero := ne_mReg_of_lt_five hlt5 (by decide)
      have hne_k : reg ≠ mK := ne_mReg_of_lt_five hlt5 (by decide)
      have hne_cur : reg ≠ mCur := ne_mReg_of_lt_five hlt5 (by decide)
      have hne_ta : reg ≠ mTmpA := ne_mReg_of_lt_five hlt5 (by decide)
      have hne_tb : reg ≠ mTmpB := ne_mReg_of_lt_five hlt5 (by decide)
      have hne_ib : reg ≠ mItemBase := ne_mReg_of_lt_five hlt5 (by decide)
      calc z.regs reg
          = z₁₅.regs reg := by
              dsimp only [z, shrinkPost]
              rw [Function.update_of_ne hne_idx, Function.update_of_ne hne_one,
                Function.update_of_ne hne_zero]
        _ = z₁₃.regs reg := by
              dsimp only [z₁₅, z₁₄, RData.set]
              rw [Function.update_of_ne hne_k, Function.update_of_ne hne_cur]
        _ = z₁₂.regs reg := hz₁₃_keep12 reg hne_fr h160
        _ = z₈.regs reg := by
              dsimp only [z₁₂, z₁₁, z₁₀, z₉, RData.set]
              rw [Function.update_of_ne hne_cur, Function.update_of_ne hne_tb,
                Function.update_of_ne hne_ta, Function.update_of_ne hne_ib]
        _ = z₇.regs reg := hz₈_keep7 reg hne_fr h160
        _ = z₄.regs reg := by
              dsimp only [z₇, z₆, z₅, RData.set]
              rw [Function.update_of_ne hne_cur, Function.update_of_ne hne_tb,
                Function.update_of_ne hne_ta]
  have hpeak_lin := migratePeakWords_le_linear (V := V) hw hhdr_z₄.fits_U hV hn hev
  have hoff_lin : offNew ≤ 504 * n + 439 :=
    (offCompItems_le_linear hw hNU_new hhdr_z₄.fits_U).trans (by linarith only [hN_new_2n])
  have hiwn_lin := compactedItemWords_le_linear (U := U) (V := V) (w := w) (N := N_new) (n := n)
    hw hU.le hV
  have hf1 := one_le_migFactor
  have hc_cl1_mul : migFactor * (memoryCost
      (copyLeftwardProg ((newMeta, base), offNew)) ⟨z₄.mem, peakF⟩ + 1) ≤
      migFactor * (1008 * n + 879) :=
    Nat.mul_le_mul_left migFactor (by linarith only [hc_cl1, hoff_lin])
  have hc_cl2_mul : migFactor * (memoryCost
      (copyLeftwardProg ((arenaB, base + offNew), iwNew)) ⟨z₈.mem, peakF⟩ + 1) ≤
      migFactor * (4 * n + 5) :=
    Nat.mul_le_mul_left migFactor (by
      dsimp only [iwNew] at hc_cl2; linarith only [hc_cl2, hiwn_lin])
  have hc_sh_lin : 4 * (peakF - frNew) + 5 ≤ 6056 * n + 3549 := by
    have hsub : peakF - frNew ≤ migratePeakWords U V w N_old n := by
      dsimp only [peakF, frNew]
      exact (Nat.sub_le_sub_left
        (by linarith only [h225_new] : base ≤ base + offNew + iwNew) _).trans_eq
        (Nat.add_sub_cancel_left _ _)
    linarith only [hsub, hpeak_lin]
  have hex_back :=
    hex_c5.seq_eq (hex_c6.seq_eq (hex_c7.seq_eq
      ((hex_cl1.mono hc_cl1_mul (fun _ h => h)).seq_eq
        (hex_ib.seq_eq (hex_c10.seq_eq (hex_c11.seq_eq (hex_c12.seq_eq
          ((hex_cl2.mono hc_cl2_mul (fun _ h => h)).seq_eq
            (hex_c14.seq_eq (hex_c15.seq_eq
              (hex_sh.mono hc_sh_lin (fun _ h => h))))))))))))
  refine ⟨z, _, hex_back, by nlinarith only [hn, hf1], hzb, hzf, hsplit_z, hgm_z,
    abiPreserved_of_lt_five hz_abi_of,
    fun addr haddr => by
      rw [hz_clear_lt addr (by dsimp only [frNew]; linarith only [haddr]),
        hz₁₃_mem_eq, hout_cl2 addr (fun h => by linarith only [haddr, h.1]),
        hz₈_mem_eq, hout_cl1 addr (fun h => by linarith only [haddr, h.1])]⟩


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
