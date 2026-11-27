/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.Registers
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.WitnessBase
-- Unfolds `rResize` and `migFactor` solely to discharge witness scratch and factor bounds.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.Registers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Internal Migration Register Banks, Witness Arrays, and Frame Helpers

Internal register banks (`mOldHp`, `mOldCp`, `mNewHp`, `mNewCp`), `RealizesBounded` source/scratch
register arrays (`src*`, `tmp*`), width-independence simp lemmas, and shared representation/ABI
framing lemmas used privately across `Migration.Exec` submodules.
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

theorem mReg_lt_160 (i : Fin 160) : (mReg i).val < 160 := i.isLt

/-- Hardware frontier register `1` (`= epochEmb rFr`). -/
noncomputable abbrev mFr : Fin rResize := mReg 1
/-- Relocated item-base register `14`. -/
noncomputable abbrev mItemBase : Fin rResize := mReg 14
/-- Hash-seed base register `15` (`metaBase + 225`). -/
noncomputable abbrev mHashBase : Fin rResize := mReg 15

/-- New-epoch metadata base address register `146` (`base + offCompItems U w N_old`). -/
noncomputable abbrev mNewMeta : Fin rResize := mReg 146
/-- New-epoch arena base address register `147` (`mNewMeta + mOffNew`). -/
noncomputable abbrev mArena : Fin rResize := mReg 147
/-- Right-shifted old-item destination base register `148`. -/
noncomputable abbrev mOldItemDst : Fin rResize := mReg 148
/-- Target capacity `N_new = targetCap U n` register `149`. -/
noncomputable abbrev mNNew : Fin rResize := mReg 149
/-- New-epoch item-offset `offCompItems U w N_new` register `150`. -/
noncomputable abbrev mOffNew : Fin rResize := mReg 150
/-- New-epoch hash-space output scratch register `151`. -/
noncomputable abbrev mHSpaceNew : Fin rResize := mReg 151
/-- Old-epoch compacted item-word count register `152`. -/
noncomputable abbrev mIwOld : Fin rResize := mReg 152
/-- New-epoch compacted item-word count register `153`. -/
noncomputable abbrev mIwNew : Fin rResize := mReg 153
/-- Migration arena word-count register `154` (`max iwOld iwNew + 6`). -/
noncomputable abbrev mArenaWords : Fin rResize := mReg 154
/-- Migration peak hardware-frontier register `155`. -/
noncomputable abbrev mPeakFront : Fin rResize := mReg 155
/-- Temporary address scratch register `156`. -/
noncomputable abbrev mTmpA : Fin rResize := mReg 156
/-- Secondary temporary address scratch register `157`. -/
noncomputable abbrev mTmpB : Fin rResize := mReg 157
/-- Reconstructed key output register `158` (`deleteLastOneCode`). -/
noncomputable abbrev mU0 : Fin rResize := mReg 158
/-- Reconstructed value output register `159` (`deleteLastOneCode`). -/
noncomputable abbrev mV0 : Fin rResize := mReg 159

/-- Old-epoch `HashParams` register bank (`32..50`). -/
@[expose] noncomputable def mOldHp (i : Fin 19) : Fin rResize := mReg ⟨32 + i.val, by omega⟩
/-- Old-epoch `CompParams` register bank (`52..87`). -/
@[expose] noncomputable def mOldCp (i : Fin 36) : Fin rResize := mReg ⟨52 + i.val, by omega⟩
/-- New-epoch `HashParams` register bank (`90..108`). -/
@[expose] noncomputable def mNewHp (i : Fin 19) : Fin rResize := mReg ⟨90 + i.val, by omega⟩
/-- New-epoch `CompParams` register bank (`110..145`). -/
@[expose] noncomputable def mNewCp (i : Fin 36) : Fin rResize := mReg ⟨110 + i.val, by omega⟩

@[simp] theorem val_mOldHp (i : Fin 19) : (mOldHp i).val = 32 + i.val := rfl
@[simp] theorem val_mOldCp (i : Fin 36) : (mOldCp i).val = 52 + i.val := rfl
@[simp] theorem val_mNewHp (i : Fin 19) : (mNewHp i).val = 90 + i.val := rfl
@[simp] theorem val_mNewCp (i : Fin 36) : (mNewCp i).val = 110 + i.val := rfl

theorem mOldHp_lt_160 (i : Fin 19) : (mOldHp i).val < 160 := by rw [val_mOldHp]; omega
theorem mOldCp_lt_160 (i : Fin 36) : (mOldCp i).val < 160 := by rw [val_mOldCp]; omega
theorem mNewHp_lt_160 (i : Fin 19) : (mNewHp i).val < 160 := by rw [val_mNewHp]; omega
theorem mNewCp_lt_160 (i : Fin 36) : (mNewCp i).val < 160 := by rw [val_mNewCp]; omega

theorem mOldHp_inj : Function.Injective mOldHp := fun i j h =>
  Fin.ext (by have hv := congrArg Fin.val h; dsimp [mOldHp] at hv; omega)
theorem mOldCp_inj : Function.Injective mOldCp := fun i j h =>
  Fin.ext (by have hv := congrArg Fin.val h; dsimp [mOldCp] at hv; omega)
theorem mNewHp_inj : Function.Injective mNewHp := fun i j h =>
  Fin.ext (by have hv := congrArg Fin.val h; dsimp [mNewHp] at hv; omega)
theorem mNewCp_inj : Function.Injective mNewCp := fun i j h =>
  Fin.ext (by have hv := congrArg Fin.val h; dsimp [mNewCp] at hv; omega)

theorem mOldHp_ne_mReg (i : Fin 19) {c : Fin 160} (hc : c.val < 32 ∨ 51 ≤ c.val) :
    mOldHp i ≠ mReg c := fun h => by
  have hv := congrArg Fin.val h; rw [val_mOldHp, val_mReg] at hv; omega

theorem mOldCp_ne_mReg (i : Fin 36) {c : Fin 160} (hc : c.val < 52 ∨ 88 ≤ c.val) :
    mOldCp i ≠ mReg c := fun h => by
  have hv := congrArg Fin.val h; rw [val_mOldCp, val_mReg] at hv; omega

theorem mNewHp_ne_mReg (i : Fin 19) {c : Fin 160} (hc : c.val < 90 ∨ 109 ≤ c.val) :
    mNewHp i ≠ mReg c := fun h => by
  have hv := congrArg Fin.val h; rw [val_mNewHp, val_mReg] at hv; omega

theorem mNewCp_ne_mReg (i : Fin 36) {c : Fin 160} (hc : c.val < 110 ∨ 146 ≤ c.val) :
    mNewCp i ≠ mReg c := fun h => by
  have hv := congrArg Fin.val h; rw [val_mNewCp, val_mReg] at hv; omega

theorem mShrink_nodup : ([mK, mIdx, mZero, mOne] : List (Fin rResize)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
    mK, mIdx, mZero, mOne, mReg_inj]
  decide

theorem mResample_nodup :
    ([mHashBase, mNewHp ⟨3, by decide⟩, mNewHp ⟨2, by decide⟩, mNewHp ⟨10, by decide⟩,
      mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp [mHashBase, mNewHp, mCur, mIdx, mK, mOne, mRes] at hv ⊢


theorem inEpochFactor_le_migFactor : inEpochFactor ≤ migFactor := le_max_left _ _
theorem one_le_migFactor
    : 1 ≤ migFactor := one_le_inEpochFactor.trans inEpochFactor_le_migFactor

theorem factor_mItemWords_le : wItemWords.factor ≤ migFactor :=
  factor_wItemWords_le.trans inEpochFactor_le_migFactor
theorem factor_wTargetCap_le : wTargetCap.factor ≤ migFactor :=
  le_max_of_le_right (le_max_left _ _)
theorem factor_wWriteParams_le : wWriteParams.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
theorem factor_wCopyRight_le : wCopyRight.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
theorem factor_wCopyLeft_le : wCopyLeft.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_left _ _))))
theorem factor_wInitNewMeta_le : wInitNewMeta.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_left _ _)))))
theorem factor_wReadOldKV_le : wReadOldKV.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))
theorem factor_wStreamIns_le : wStreamIns.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))
theorem factor_wStreamAll_le : wStreamAll.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))))


theorem migTmpHb {n : ℕ} (hb : n ≤ scratchMigrate) : 160 + n ≤ rResize :=
  (Nat.add_le_add_left hb 160).trans (le_max_right _ _)

/-- Source register map for old-epoch `compItemWordsGenProg`. -/
@[expose] noncomputable def srcOldIw := pairSrc mOldCp (reg1 mCnt)
/-- Output/scratch register map for old-epoch `compItemWordsGenProg`. -/
@[expose] noncomputable def tmpOldIw :=
  mkTmp (baseOff := 160) ![mIwOld] (migTmpHb scratch_wItemWords_le)

/-- Source register map for new-epoch `compItemWordsGenProg`. -/
@[expose] noncomputable def srcNewIw := pairSrc mNewCp (reg1 mCnt)
/-- Output/scratch register map for new-epoch `compItemWordsGenProg`. -/
@[expose] noncomputable def tmpNewIw :=
  mkTmp (baseOff := 160) ![mIwNew] (migTmpHb scratch_wItemWords_le)

/-- Source register map for `computeTargetCapProg`. -/
@[expose] noncomputable def srcTargetCap := pairSrc (reg1 mBase) (reg1 mCnt)
/-- Output/scratch register map for `computeTargetCapProg`. -/
@[expose] noncomputable def tmpTargetCap :=
  mkTmp (baseOff := 160) ![mNNew] (migTmpHb scratch_wTargetCap_le)

/-- Source register map for `writeEpochParamsGenProg`. -/
@[expose] noncomputable def srcWriteParams :=
  pairSrc (pairSrc (reg1 mBase) (reg1 mTmpA))
    (pairSrc (reg1 mNNew) (pairSrc (reg1 mCnt) (reg1 mCnt)))
/-- Output/scratch register map for `writeEpochParamsGenProg`. -/
@[expose] noncomputable def tmpWriteParams :=
  mkTmp (baseOff := 160) ![mOffNew, mHSpaceNew] (migTmpHb scratch_wWriteParams_le)

/-- Source register map for `copyRightwardProg`. -/
@[expose] noncomputable def srcCopyRight :=
  pairSrc (pairSrc (reg1 mNewMeta) (reg1 mOldItemDst)) (reg1 mIwOld)
/-- Scratch register map for `copyRightwardProg`. -/
@[expose] noncomputable def tmpCopyRight :=
  mkTmp (baseOff := 160) ![] (migTmpHb scratch_wCopyRight_le)

/-- Source register map for `copyLeftwardProg`. -/
@[expose] noncomputable def srcCopyLeft :=
  pairSrc (pairSrc (reg1 mTmpA) (reg1 mTmpB)) (reg1 mCur)
/-- Scratch register map for `copyLeftwardProg`. -/
@[expose] noncomputable def tmpCopyLeft :=
  mkTmp (baseOff := 160) ![] (migTmpHb scratch_wCopyLeft_le)

/-- Source register map for `initNewEpochMetaProg`. -/
@[expose] noncomputable def srcInitNewMeta :=
  pairSrc (pairSrc mNewHp mNewCp) (reg1 mTmpA)
/-- Scratch register map for `initNewEpochMetaProg`. -/
@[expose] noncomputable def tmpInitNewMeta :=
  mkTmp (baseOff := 160) ![] (migTmpHb scratch_wInitNewMeta_le)

/-- Source register map for `readOldItemKeyValGenProg`. -/
@[expose] noncomputable def srcReadOldKV :=
  pairSrc (pairSrc (pairSrc mOldHp mOldCp) (pairSrc (reg1 mBase) (reg1 mItemBase)))
    (reg1 mZero)
/-- Output/scratch register map for `readOldItemKeyValGenProg`. -/
@[expose] noncomputable def tmpReadOldKV :=
  mkTmp (baseOff := 160) ![mU0, mV0] (migTmpHb scratch_wReadOldKV_le)

/-- Source register map for `streamInsertFreshGenProg`. -/
@[expose] noncomputable def srcStreamIns :=
  pairSrc (pairSrc (pairSrc mNewHp mNewCp) (pairSrc (reg1 mBase) (reg1 mItemBase)))
    (pairSrc (reg1 mArgU) (reg1 mArgV))
/-- Scratch register map for `streamInsertFreshGenProg`. -/
@[expose] noncomputable def tmpStreamIns :=
  mkTmp (baseOff := 160) ![] (migTmpHb scratch_wStreamIns_le)

/-- Source register map for `streamAllItemsProg`. -/
@[expose] noncomputable def srcStreamAll :=
  pairSrc
    (pairSrc
      (pairSrc
        (pairSrc (pairSrc mOldHp mOldCp) (pairSrc (reg1 mBase) (reg1 mOldItemDst)))
        (pairSrc (pairSrc mNewHp mNewCp) (pairSrc (reg1 mNewMeta) (reg1 mArena))))
      (reg1 mZero))
    (reg1 mCnt)
/-- Scratch register map for `streamAllItemsProg`. -/
@[expose] noncomputable def tmpStreamAll :=
  mkTmp (baseOff := 160) ![mCur] (migTmpHb scratch_wStreamAll_le)

theorem tmpOldIw_inj : Function.Injective tmpOldIw :=
  mkTmp_injective _ (outs1_inj mIwOld) (fun i => by fin_cases i; exact mReg_lt_160 _)
theorem srcOldIw_ne_tmp : ∀ i j, srcOldIw i ≠ tmpOldIw j :=
  src_ne_mkTmp _ (pairSrc_lt mOldCp_lt_160 (fun _ => mReg_lt_160 _)) <|
    pairSrc_ne_outs (fun i a => by fin_cases a; exact mOldCp_ne_mReg i (Or.inr (by decide)))
      (fun _ a => by fin_cases a; exact mReg_ne (by decide))
theorem tmpOldIw_ne_mFr : ∀ j, tmpOldIw j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a; exact mReg_ne (by decide))
theorem srcOldIw_ne_mFr : ∀ i, srcOldIw i ≠ mFr :=
  pairSrc_ne_reg (fun i => mOldCp_ne_mReg i (Or.inl (by decide))) (fun _ => mReg_ne (by decide))

theorem tmpNewIw_inj : Function.Injective tmpNewIw :=
  mkTmp_injective _ (outs1_inj mIwNew) (fun i => by fin_cases i; exact mReg_lt_160 _)
theorem srcNewIw_ne_tmp : ∀ i j, srcNewIw i ≠ tmpNewIw j :=
  src_ne_mkTmp _ (pairSrc_lt mNewCp_lt_160 (fun _ => mReg_lt_160 _)) <|
    pairSrc_ne_outs (fun i a => by fin_cases a; exact mNewCp_ne_mReg i (Or.inr (by decide)))
      (fun _ a => by fin_cases a; exact mReg_ne (by decide))
theorem tmpNewIw_ne_mFr : ∀ j, tmpNewIw j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a; exact mReg_ne (by decide))
theorem srcNewIw_ne_mFr : ∀ i, srcNewIw i ≠ mFr :=
  pairSrc_ne_reg (fun i => mNewCp_ne_mReg i (Or.inl (by decide))) (fun _ => mReg_ne (by decide))

theorem tmpTargetCap_inj : Function.Injective tmpTargetCap :=
  mkTmp_injective _ (outs1_inj mNNew) (fun i => by fin_cases i; exact mReg_lt_160 _)
theorem srcTargetCap_ne_tmp : ∀ i j, srcTargetCap i ≠ tmpTargetCap j :=
  src_ne_mkTmp _ (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _)) <|
    pairSrc_ne_outs (fun _ a => by fin_cases a; exact mReg_ne (by decide))
      (fun _ a => by fin_cases a; exact mReg_ne (by decide))
theorem tmpTargetCap_ne_mFr : ∀ j, tmpTargetCap j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a; exact mReg_ne (by decide))
theorem srcTargetCap_ne_mFr : ∀ i, srcTargetCap i ≠ mFr :=
  pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide))

theorem tmpWriteParams_inj : Function.Injective tmpWriteParams :=
  mkTmp_injective _ (outs2_inj (mReg_ne (by decide)))
    (fun i => by fin_cases i <;> exact mReg_lt_160 _)
theorem srcWriteParams_ne_tmp : ∀ i j, srcWriteParams i ≠ tmpWriteParams j :=
  src_ne_mkTmp _
    (pairSrc_lt (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _))
      (pairSrc_lt (fun _ => mReg_lt_160 _)
        (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _)))) <|
    pairSrc_ne_outs
      (pairSrc_ne_outs (fun _ a => by fin_cases a <;> exact mReg_ne (by decide))
        (fun _ a => by fin_cases a <;> exact mReg_ne (by decide)))
      (pairSrc_ne_outs (fun _ a => by fin_cases a <;> exact mReg_ne (by decide))
        (pairSrc_ne_outs (fun _ a => by fin_cases a <;> exact mReg_ne (by decide))
          (fun _ a => by fin_cases a <;> exact mReg_ne (by decide))))
theorem tmpWriteParams_ne_mFr : ∀ j, tmpWriteParams j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a <;> exact mReg_ne (by decide))
theorem srcWriteParams_ne_mFr : ∀ i, srcWriteParams i ≠ mFr :=
  pairSrc_ne_reg
    (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide)))
    (pairSrc_ne_reg (fun _ => mReg_ne (by decide))
      (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide))))

theorem tmpCopyRight_inj : Function.Injective tmpCopyRight :=
  mkTmp_injective _ (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
theorem srcCopyRight_ne_tmp : ∀ i j, srcCopyRight i ≠ tmpCopyRight j :=
  src_ne_mkTmp _
    (pairSrc_lt (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _))
      (fun _ => mReg_lt_160 _))
    (fun _ a => Fin.elim0 a)
theorem tmpCopyRight_ne_mFr : ∀ j, tmpCopyRight j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => Fin.elim0 a)
theorem srcCopyRight_ne_mFr : ∀ i, srcCopyRight i ≠ mFr :=
  pairSrc_ne_reg (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide)))
    (fun _ => mReg_ne (by decide))

theorem tmpCopyLeft_inj : Function.Injective tmpCopyLeft :=
  mkTmp_injective _ (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
theorem srcCopyLeft_ne_tmp : ∀ i j, srcCopyLeft i ≠ tmpCopyLeft j :=
  src_ne_mkTmp _
    (pairSrc_lt (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _))
      (fun _ => mReg_lt_160 _))
    (fun _ a => Fin.elim0 a)
theorem tmpCopyLeft_ne_mFr : ∀ j, tmpCopyLeft j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => Fin.elim0 a)
theorem srcCopyLeft_ne_mFr : ∀ i, srcCopyLeft i ≠ mFr :=
  pairSrc_ne_reg (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide)))
    (fun _ => mReg_ne (by decide))

theorem tmpInitNewMeta_inj : Function.Injective tmpInitNewMeta :=
  mkTmp_injective _ (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
theorem srcInitNewMeta_ne_tmp : ∀ i j, srcInitNewMeta i ≠ tmpInitNewMeta j :=
  src_ne_mkTmp _
    (pairSrc_lt (pairSrc_lt mNewHp_lt_160 mNewCp_lt_160) (fun _ => mReg_lt_160 _))
    (fun _ a => Fin.elim0 a)
theorem tmpInitNewMeta_ne_mFr : ∀ j, tmpInitNewMeta j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => Fin.elim0 a)
theorem srcInitNewMeta_ne_mFr : ∀ i, srcInitNewMeta i ≠ mFr :=
  pairSrc_ne_reg
    (pairSrc_ne_reg (fun i => mNewHp_ne_mReg i (Or.inl (by decide)))
      (fun i => mNewCp_ne_mReg i (Or.inl (by decide))))
    (fun _ => mReg_ne (by decide))

theorem tmpReadOldKV_inj : Function.Injective tmpReadOldKV :=
  mkTmp_injective _ (outs2_inj (mReg_ne (by decide)))
    (fun i => by fin_cases i <;> exact mReg_lt_160 _)
theorem srcReadOldKV_ne_tmp : ∀ i j, srcReadOldKV i ≠ tmpReadOldKV j :=
  src_ne_mkTmp _
    (pairSrc_lt
      (pairSrc_lt (pairSrc_lt mOldHp_lt_160 mOldCp_lt_160)
        (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _)))
      (fun _ => mReg_lt_160 _)) <|
    pairSrc_ne_outs
      (pairSrc_ne_outs
        (pairSrc_ne_outs
          (fun i a => by fin_cases a <;> exact mOldHp_ne_mReg i (Or.inr (by decide)))
          (fun i a => by fin_cases a <;> exact mOldCp_ne_mReg i (Or.inr (by decide))))
        (pairSrc_ne_outs (fun _ a => by fin_cases a <;> exact mReg_ne (by decide))
          (fun _ a => by fin_cases a <;> exact mReg_ne (by decide))))
      (fun _ a => by fin_cases a <;> exact mReg_ne (by decide))
theorem tmpReadOldKV_ne_mFr : ∀ j, tmpReadOldKV j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a <;> exact mReg_ne (by decide))
theorem srcReadOldKV_ne_mFr : ∀ i, srcReadOldKV i ≠ mFr :=
  pairSrc_ne_reg
    (pairSrc_ne_reg
      (pairSrc_ne_reg (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))
        (fun i => mOldCp_ne_mReg i (Or.inl (by decide))))
      (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide))))
    (fun _ => mReg_ne (by decide))

theorem tmpStreamIns_inj : Function.Injective tmpStreamIns :=
  mkTmp_injective _ (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
theorem srcStreamIns_ne_tmp : ∀ i j, srcStreamIns i ≠ tmpStreamIns j :=
  src_ne_mkTmp _
    (pairSrc_lt
      (pairSrc_lt (pairSrc_lt mNewHp_lt_160 mNewCp_lt_160)
        (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _)))
      (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _)))
    (fun _ a => Fin.elim0 a)
theorem tmpStreamIns_ne_mFr : ∀ j, tmpStreamIns j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => Fin.elim0 a)
theorem srcStreamIns_ne_mFr : ∀ i, srcStreamIns i ≠ mFr :=
  pairSrc_ne_reg
    (pairSrc_ne_reg
      (pairSrc_ne_reg (fun i => mNewHp_ne_mReg i (Or.inl (by decide)))
        (fun i => mNewCp_ne_mReg i (Or.inl (by decide))))
      (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide))))
    (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide)))

theorem tmpStreamAll_inj : Function.Injective tmpStreamAll :=
  mkTmp_injective _ (outs1_inj mCur) (fun i => by fin_cases i; exact mReg_lt_160 _)
theorem srcStreamAll_ne_tmp : ∀ i j, srcStreamAll i ≠ tmpStreamAll j :=
  src_ne_mkTmp _
    (pairSrc_lt
      (pairSrc_lt
        (pairSrc_lt
          (pairSrc_lt (pairSrc_lt mOldHp_lt_160 mOldCp_lt_160)
            (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _)))
          (pairSrc_lt (pairSrc_lt mNewHp_lt_160 mNewCp_lt_160)
            (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _))))
        (fun _ => mReg_lt_160 _))
      (fun _ => mReg_lt_160 _)) <|
    pairSrc_ne_outs
      (pairSrc_ne_outs
        (pairSrc_ne_outs
          (pairSrc_ne_outs
            (pairSrc_ne_outs
              (fun i a => by fin_cases a; exact mOldHp_ne_mReg i (Or.inl (by decide)))
              (fun i a => by fin_cases a; exact mOldCp_ne_mReg i (Or.inl (by decide))))
            (pairSrc_ne_outs (fun _ a => by fin_cases a; exact mReg_ne (by decide))
              (fun _ a => by fin_cases a; exact mReg_ne (by decide))))
          (pairSrc_ne_outs
            (pairSrc_ne_outs
              (fun i a => by fin_cases a; exact mNewHp_ne_mReg i (Or.inl (by decide)))
              (fun i a => by fin_cases a; exact mNewCp_ne_mReg i (Or.inl (by decide))))
            (pairSrc_ne_outs (fun _ a => by fin_cases a; exact mReg_ne (by decide))
              (fun _ a => by fin_cases a; exact mReg_ne (by decide)))))
        (fun _ a => by fin_cases a; exact mReg_ne (by decide)))
      (fun _ a => by fin_cases a; exact mReg_ne (by decide))
theorem tmpStreamAll_ne_mFr : ∀ j, tmpStreamAll j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a; exact mReg_ne (by decide))
theorem srcStreamAll_ne_mFr : ∀ i, srcStreamAll i ≠ mFr :=
  pairSrc_ne_reg
    (pairSrc_ne_reg
      (pairSrc_ne_reg
        (pairSrc_ne_reg
          (pairSrc_ne_reg (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))
            (fun i => mOldCp_ne_mReg i (Or.inl (by decide))))
          (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide))))
        (pairSrc_ne_reg
          (pairSrc_ne_reg (fun i => mNewHp_ne_mReg i (Or.inl (by decide)))
            (fun i => mNewCp_ne_mReg i (Or.inl (by decide))))
          (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide)))))
      (fun _ => mReg_ne (by decide)))
    (fun _ => mReg_ne (by decide))

theorem tmpOldIw_out :
    tmpOldIw (Fin.castAdd (wItemWords.scratchSize + 1) 0) = mIwOld := mkTmp_castAdd _ _ 0
theorem tmpNewIw_out :
    tmpNewIw (Fin.castAdd (wItemWords.scratchSize + 1) 0) = mIwNew := mkTmp_castAdd _ _ 0
theorem tmpTargetCap_out :
    tmpTargetCap (Fin.castAdd (wTargetCap.scratchSize + 1) 0) = mNNew := mkTmp_castAdd _ _ 0
theorem tmpWriteParams_out_0 :
    tmpWriteParams (Fin.castAdd (wWriteParams.scratchSize + 1) 0) = mOffNew :=
  mkTmp_castAdd _ _ 0
theorem tmpReadOldKV_out_0 :
    tmpReadOldKV (Fin.castAdd (wReadOldKV.scratchSize + 1) 0) = mU0 := mkTmp_castAdd _ _ 0


@[simp] theorem not_readsWidth_code_oldIw :
    ¬(wItemWords.code mFr srcOldIw tmpOldIw).ReadsWidth :=
  (wItemWords.code_spec mFr srcOldIw tmpOldIw
    tmpOldIw_inj srcOldIw_ne_tmp tmpOldIw_ne_mFr srcOldIw_ne_mFr).1

@[simp] theorem not_readsWidth_code_newIw :
    ¬(wItemWords.code mFr srcNewIw tmpNewIw).ReadsWidth :=
  (wItemWords.code_spec mFr srcNewIw tmpNewIw
    tmpNewIw_inj srcNewIw_ne_tmp tmpNewIw_ne_mFr srcNewIw_ne_mFr).1

@[simp] theorem not_readsWidth_code_targetCap :
    ¬(wTargetCap.code mFr srcTargetCap tmpTargetCap).ReadsWidth :=
  (wTargetCap.code_spec mFr srcTargetCap tmpTargetCap
    tmpTargetCap_inj srcTargetCap_ne_tmp tmpTargetCap_ne_mFr srcTargetCap_ne_mFr).1

@[simp] theorem not_readsWidth_code_writeParams :
    ¬(wWriteParams.code mFr srcWriteParams tmpWriteParams).ReadsWidth :=
  (wWriteParams.code_spec mFr srcWriteParams tmpWriteParams
    tmpWriteParams_inj srcWriteParams_ne_tmp tmpWriteParams_ne_mFr srcWriteParams_ne_mFr).1

@[simp] theorem not_readsWidth_code_copyRight :
    ¬(wCopyRight.code mFr srcCopyRight tmpCopyRight).ReadsWidth :=
  (wCopyRight.code_spec mFr srcCopyRight tmpCopyRight
    tmpCopyRight_inj srcCopyRight_ne_tmp tmpCopyRight_ne_mFr srcCopyRight_ne_mFr).1

@[simp] theorem not_readsWidth_code_copyLeft :
    ¬(wCopyLeft.code mFr srcCopyLeft tmpCopyLeft).ReadsWidth :=
  (wCopyLeft.code_spec mFr srcCopyLeft tmpCopyLeft
    tmpCopyLeft_inj srcCopyLeft_ne_tmp tmpCopyLeft_ne_mFr srcCopyLeft_ne_mFr).1

@[simp] theorem not_readsWidth_code_initNewMeta :
    ¬(wInitNewMeta.code mFr srcInitNewMeta tmpInitNewMeta).ReadsWidth :=
  (wInitNewMeta.code_spec mFr srcInitNewMeta tmpInitNewMeta
    tmpInitNewMeta_inj srcInitNewMeta_ne_tmp tmpInitNewMeta_ne_mFr srcInitNewMeta_ne_mFr).1

@[simp] theorem not_readsWidth_code_readOldKV :
    ¬(wReadOldKV.code mFr srcReadOldKV tmpReadOldKV).ReadsWidth :=
  (wReadOldKV.code_spec mFr srcReadOldKV tmpReadOldKV
    tmpReadOldKV_inj srcReadOldKV_ne_tmp tmpReadOldKV_ne_mFr srcReadOldKV_ne_mFr).1

@[simp] theorem not_readsWidth_code_streamIns :
    ¬(wStreamIns.code mFr srcStreamIns tmpStreamIns).ReadsWidth :=
  (wStreamIns.code_spec mFr srcStreamIns tmpStreamIns
    tmpStreamIns_inj srcStreamIns_ne_tmp tmpStreamIns_ne_mFr srcStreamIns_ne_mFr).1

@[simp] theorem not_readsWidth_code_streamAll :
    ¬(wStreamAll.code mFr srcStreamAll tmpStreamAll).ReadsWidth :=
  (wStreamAll.code_spec mFr srcStreamAll tmpStreamAll
    tmpStreamAll_inj srcStreamAll_ne_tmp tmpStreamAll_ne_mFr srcStreamAll_ne_mFr).1

theorem le_offCompItems_225 (U w N : ℕ) : 225 ≤ offCompItems U w N := by
  unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega

theorem growZeroPost_regs_of_not_mem {s : RData rResize} {reg : Fin rResize}
    (hreg : reg ∉ ([mRes, mCur, mIdx, mZero, mOne] : List (Fin rResize))) :
    (growZeroPost mK mRes mCur mIdx mZero mOne s).regs reg = s.regs reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
  simp only [growZeroPost, Function.update_of_ne hreg.2.1, Function.update_of_ne hreg.2.2.1,
    Function.update_of_ne hreg.1, Function.update_of_ne hreg.2.2.2.2,
    Function.update_of_ne hreg.2.2.2.1]

theorem fixedCoupled_of_shift {metaBase srcItemBase dstItemBase U V w N n : ℕ}
    {s_fix s₀ s₁ : Memory.State} (hw : 0 < w)
    (hcpl : FixedCoupled metaBase srcItemBase U V w N s_fix s₀)
    (htot : totalSlots N (compGmAt metaBase U w N s₀.mem) = n)
    (hmeta : ∀ a, metaBase + offCompLM U w N ≤ a ∧ a < metaBase + offCompItems U w N →
      s₁.mem a = s₀.mem a)
    (hitem : ∀ j < compactedItemWords U V w N n,
      s₁.mem (dstItemBase + j) = s₀.mem (srcItemBase + j)) :
    FixedCoupled metaBase dstItemBase U V w N s_fix s₁ ∧
    compGmAt metaBase U w N s₁.mem = compGmAt metaBase U w N s₀.mem := by
  have h0_off : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1_off : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h2_off : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h3_off : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  have hlm_eq := compLmAt_congr (metaBase := metaBase) (U := U) (N := N) hw
    fun a ha => hmeta a ⟨ha.1, by omega⟩
  have hgm_eq := compGmAt_congr (metaBase := metaBase) (U := U) (N := N) hw
    fun a ha => hmeta a ⟨by omega, by omega⟩
  have htd_eq := compTDAt_congr (metaBase := metaBase) (U := U) (N := N) hw
    fun a ha => hmeta a ⟨by omega, by omega⟩
  have hdt_eq := compDTAt_congr (metaBase := metaBase) (U := U) (N := N) hw
    fun a ha => hmeta a ⟨by omega, ha.2⟩
  let mem_sh (a : ℕ) : ℕ := s₁.mem (dstItemBase + (a - srcItemBase))
  have hitem_congr : ∀ a, srcItemBase ≤ a ∧ a < srcItemBase + compactedItemWords U V w N n →
      mem_sh a = s₀.mem a := fun a ha => by
    dsimp only [mem_sh]
    rw [hitem (a - srcItemBase) (by omega), Nat.add_sub_of_le ha.1]
  have hmem_sh_add : ∀ off, mem_sh (srcItemBase + off) = s₁.mem (dstItemBase + off) := fun off => by
    dsimp only [mem_sh]; rw [Nat.add_sub_cancel_left]
  have hq_eq :
      compQuotAt dstItemBase U V w N n s₁.mem = compQuotAt srcItemBase U V w N n s₀.mem := by
    rw [← compQuotAt_congr (itemBase := srcItemBase) (U := U) (V := V) (N := N) (n := n) hw
      hitem_congr]
    exact funext fun _ => by simp only [compQuotAt, readBitSlice, Nat.add_assoc, hmem_sh_add]
  have hv_eq :
      compValAt dstItemBase U V w N n s₁.mem = compValAt srcItemBase U V w N n s₀.mem := by
    rw [← compValAt_congr (itemBase := srcItemBase) (U := U) (V := V) (N := N) (n := n) hw
      hitem_congr]
    exact funext fun _ => by simp only [compValAt, readBitSlice, Nat.add_assoc, hmem_sh_add]
  have hd_bd (d : ℕ) (hd : d < epochTotalSlots N (compGmAt metaBase U w N s₁.mem)) :
      d < n ∧ d < epochTotalSlots N (compGmAt metaBase U w N s₀.mem) :=
    ⟨lt_of_lt_of_eq (hgm_eq ▸ hd) htot, hgm_eq ▸ hd⟩
  refine ⟨⟨hgm_eq.trans hcpl.gm_eq, hlm_eq.trans hcpl.lm_eq,
      by rw [hgm_eq, htd_eq, hdt_eq]; exact hcpl.win_inv,
      fun i => by rw [htd_eq]; exact hcpl.td_lt i,
      fun i => by rw [hdt_eq]; exact hcpl.dt_lt i,
      fun d hd => by
        rw [compQuotAt_of_lt s₁.mem hd (hd_bd d hd).1, hq_eq,
          compQuotAt_of_lt s₀.mem (hd_bd d hd).1 (hd_bd d hd).2, hgm_eq, hdt_eq]
        exact hcpl.quot_eq d (hd_bd d hd).2,
      fun d hd => by
        rw [compValAt_of_lt s₁.mem hd (hd_bd d hd).1, hv_eq,
          compValAt_of_lt s₀.mem (hd_bd d hd).1 (hd_bd d hd).2, hgm_eq, hdt_eq]
        exact hcpl.val_eq d (hd_bd d hd).2⟩,
    hgm_eq⟩

/-- Agreement on the caller-supplied ABI input registers `(mBase, mTag, mArgU, mArgV)`. -/
@[expose] def abiPreserved (x y : RData rResize) : Prop :=
  y.regs mBase = x.regs mBase ∧
  y.regs mTag = x.regs mTag ∧
  y.regs mArgU = x.regs mArgU ∧
  y.regs mArgV = x.regs mArgV

theorem abiPreserved_trans {x y z : RData rResize}
    (h₁ : abiPreserved x y) (h₂ : abiPreserved y z) : abiPreserved x z :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩


theorem rootHeaderValid_congr {U V w N n n_init metaBase : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hhdr : RootHeaderValid U V w N n n_init metaBase mem₂)
    (heq : ∀ a, metaBase ≤ a ∧ a < metaBase + 8 → mem₁ a = mem₂ a) :
    RootHeaderValid U V w N n n_init metaBase mem₁ :=
  ⟨hhdr.fits_U, hhdr.pos_U, hhdr.pos_V,
    (heq _ ⟨le_rfl, by omega⟩).trans hhdr.hdr_U,
    (heq _ ⟨by omega, by omega⟩).trans hhdr.hdr_V,
    (heq _ ⟨by omega, by omega⟩).trans hhdr.hdr_w,
    (heq _ ⟨by omega, by omega⟩).trans hhdr.hdr_keyBits,
    (heq _ ⟨by omega, by omega⟩).trans hhdr.hdr_valBits,
    (heq _ ⟨by omega, by omega⟩).trans hhdr.hdr_N,
    (heq _ ⟨by omega, by omega⟩).trans hhdr.hdr_n,
    (heq _ ⟨by omega, by omega⟩).trans hhdr.hdr_n_init⟩

theorem epochParamsStored_congr {U V w N metaBase : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hpar : EpochParamsStored U V w N metaBase mem₂)
    (heq : ∀ a, metaBase ≤ a ∧ a < metaBase + 63 → mem₁ a = mem₂ a) :
    EpochParamsStored U V w N metaBase mem₁ :=
  ⟨fun i => (heq _ ⟨by unfold offHashParams; omega, by unfold offHashParams; omega⟩).trans
      (hpar.hp_eq i),
   fun i => (heq _ ⟨by unfold offCompParams; omega, by unfold offCompParams; omega⟩).trans
      (hpar.cp_eq i)⟩

theorem ne_mReg_of_lt_five {reg : Fin rResize} (h5 : reg.val < 5)
    {c : Fin 160} (hc : 5 ≤ c.val) : reg ≠ mReg c := fun h => by
  have hv := congrArg Fin.val h; rw [val_mReg] at hv; omega


theorem abiPreserved_of_lt_five {x y : RData rResize}
    (h : ∀ reg : Fin rResize, reg.val < 5 → reg ≠ mFr → y.regs reg = x.regs reg) :
    abiPreserved x y :=
  ⟨h mBase (by decide) (mReg_ne (by decide)),
   h mTag (by decide) (mReg_ne (by decide)),
   h mArgU (by decide) (mReg_ne (by decide)),
   h mArgV (by decide) (mReg_ne (by decide))⟩

theorem hashSpace_bounds_of_fits_offCompItems {U w N metaBase : ℕ}
    (hU : U < 2 ^ w) (hNU : N ≤ U) (hfit_nm : Fits w (metaBase + offCompItems U w N)) :
    225 + ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3 ≤
      offCompItems U w N ∧
    ReducedKWise.seedWords (qBits U N) (hashB N) (totalMicroBits N) 3 ≤
      ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3 ∧
    Fits w ((metaBase + epochHdrWords) +
      ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3) ∧
    2 * reducedChunkBits
      (reducedTrinomialStep (qBits U N) (hashB N) (totalMicroBits N)) < w := by
  have h225 : 225 < 2 ^ w := fits_const_of_offCompItems hfit_nm le_rfl
  have hw2 : 2 ≤ w := by rcases w with _ | _ | _ <;> omega
  have hsp_le : 225 + ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3 ≤
      offCompItems U w N := by
    dsimp only [offCompItems, offDenseToTail, offTailToDense, offCompGM, offCompLM,
      epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits, hashB]
    omega
  have hfit_h : Fits w ((metaBase + epochHdrWords) +
      ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3) :=
    hfit_nm.of_le (by unfold epochHdrWords; omega)
  exact ⟨hsp_le, Nat.le_add_right _ _, hfit_h,
    ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space
      (two_mul_reducedChunkBits_hash_le hw2 hNU hU.le) hfit_h⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
