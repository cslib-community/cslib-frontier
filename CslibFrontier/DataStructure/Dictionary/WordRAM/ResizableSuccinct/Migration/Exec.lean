/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Resizable.Rename
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.StreamStep
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch
public import CslibFrontier.Probability.PMF.Expect
public import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Native `RCode` Epoch-Migration, First-Epoch Initialization, and Last-Delete Subroutines

Compiles the verified `Memory.Prog` subroutines from `Migration.ParamsCompute` and
`Migration.StreamStep` together with `growZeroCode`, `shrinkCode`, and `resampleHashCode` into
parameter-free (`¬ReadsWidth`) native `RCode .exact rResize` epoch-transition programs on the
**Resizable Word RAM**:

1. **`migrateActiveCode`**: single-tape `1 · OPT` streaming rebuild from `(N_old, n, n_init_old)` to
   `(targetCap U n, n, n)` (`1 ≤ n ≤ U`, `EpochValid U n N_old`), keeping the hardware frontier
   `≤ base + migratePeakWords U V w N_old n` (`≤ base + Dynamic.succinctWords 2699 888 U V w n`,
   never `2 · OPT`), sampling a fresh uniform `QuotHashSeed U (targetCap U n)`, and bounding
   expected instructions plus post-migration `inEpochPotential` by `migLinearFactor * n`.
2. **`initFirstEpochCode`**: empty-to-active transition (`n = 0 → n' = 1`, `N₁ = targetCap U 1`) on
   `insert u v` in `O(1)` instructions within `base + compactedEpochWords U V w (targetCap U 1) 1`.
3. **`deleteLastOneCode`**: singleton deletion (`n = 1 → 1` or `1 → 0`) on `delete u` in `O(1)`
   deterministic instructions, collapsing to the 8-word empty header when the sole key matches `u`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.rResize`, `epochEmb`, `migFactor`,
  `migLinearFactor`, `initFirstCharge`, `deleteLastOneCharge`: parameter-free register budget,
  `rEpoch` embedding, and cost constants.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.migrateActiveCode`,
  `initFirstEpochCode`, `deleteLastOneCode`: parameter-free `RCode .exact rResize` epoch-boundary
  subroutines.

## Main results

* `not_readsWidth_migrateActiveCode`, `not_readsWidth_initFirstEpochCode`,
  `not_readsWidth_deleteLastOneCode`: width-independence (`¬ReadsWidth`) of all three subroutines.
* `migrateActiveCode_execRCodeDist`: `ExecRCodeDist` specification for single-tape `1 · OPT`
  capacity doubling and halving.
* `initFirstEpochCode_execRCodeDist`: `ExecRCodeDist` specification for `0 → 1` epoch creation.
* `deleteLastOneCode_demonicExec`: `RDemonicExec` specification for `n = 1` deletion and empty
  collapse.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select: Bypassing the Tree-Structure
  Bottleneck*, Section 5.1][KuszmaulLiangZhou2026]
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

/-! ## Section 1: Retained Migration Witnesses, Register Space `rResize`, and `migFactor` -/

private noncomputable def wTargetCap :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_computeTargetCap
private noncomputable def wWriteParams :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_writeEpochParamsGen
private noncomputable def wCopyRight :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_copyRightward
private noncomputable def wCopyLeft :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_copyLeftward
private noncomputable def wInitNewMeta :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_initNewEpochMeta
private noncomputable def wReadOldKV :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_readOldItemKeyValGen
private noncomputable def wStreamIns :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_streamInsertFreshGen
private noncomputable def wStreamAll :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_streamAllItems

private noncomputable def scratchMigrate : ℕ :=
  max (1 + wItemWords.scratchSize + 1) <|
  max (1 + wTargetCap.scratchSize + 1) <|
  max (2 + wWriteParams.scratchSize + 1) <|
  max (0 + wCopyRight.scratchSize + 1) <|
  max (0 + wCopyLeft.scratchSize + 1) <|
  max (0 + wInitNewMeta.scratchSize + 1) <|
  max (2 + wReadOldKV.scratchSize + 1) <|
  max (0 + wStreamIns.scratchSize + 1)
      (1 + wStreamAll.scratchSize + 1)

/-- Parameter-free register budget for the full resizable succinct dictionary (`rEpoch` plus
new-epoch parameter banks `90..145`, migration control registers `146..159`, and migration
`RealizesBounded` scratch `160..`). -/
noncomputable def rResize : ℕ :=
  max rEpoch (160 + scratchMigrate)

theorem rEpoch_le_rResize : rEpoch ≤ rResize := le_max_left _ _

theorem le_rResize_160 : 160 ≤ rResize :=
  (Nat.le_add_right 160 scratchMigrate).trans (le_max_right _ _)

/-- Canonical injective embedding `Fin rEpoch → Fin rResize` aligning registers `0..87`. -/
@[expose]
noncomputable def epochEmb : Fin rEpoch → Fin rResize :=
  Fin.castLE rEpoch_le_rResize

theorem epochEmb_injective : Function.Injective epochEmb :=
  Fin.castLE_injective rEpoch_le_rResize

@[simp]
theorem val_epochEmb (i : Fin rEpoch) : (epochEmb i).val = i.val := rfl

/-- Fixed register bank `0..159` inside `Fin rResize`. -/
@[expose]
noncomputable def mReg : Fin 160 → Fin rResize :=
  Fin.castLE le_rResize_160

private theorem mReg_injective : Function.Injective mReg :=
  Fin.castLE_injective le_rResize_160

@[simp]
theorem mReg_inj {i j : Fin 160} : mReg i = mReg j ↔ i = j :=
  mReg_injective.eq_iff

@[simp]
theorem val_mReg (i : Fin 160) : (mReg i).val = i.val := rfl

private theorem mReg_lt_160 (i : Fin 160) : (mReg i).val < 160 := i.isLt

theorem mReg_ne {i j : Fin 160} (h : i ≠ j) : mReg i ≠ mReg j :=
  fun heq => h (mReg_injective heq)

/-- Persistent base-address register `0` (`= epochEmb rBase`). -/
noncomputable abbrev mBase : Fin rResize := mReg 0
/-- Hardware frontier register `1` (`= epochEmb rFr`). -/
private noncomputable abbrev mFr : Fin rResize := mReg 1
/-- Operation tag input register `2` (`= epochEmb rTag`). -/
noncomputable abbrev mTag : Fin rResize := mReg 2
/-- Input key register `3` (`= epochEmb rArgU`). -/
noncomputable abbrev mArgU : Fin rResize := mReg 3
/-- Input value register `4` (`= epochEmb rArgV`). -/
noncomputable abbrev mArgV : Fin rResize := mReg 4
/-- Output presence tag register `5` (`= epochEmb rOutTag`). -/
noncomputable abbrev mOutTag : Fin rResize := mReg 5
/-- Output value register `6` (`= epochEmb rOutVal`). -/
noncomputable abbrev mOutVal : Fin rResize := mReg 6
/-- Word count delta / mask scratch register `7`. -/
noncomputable abbrev mK : Fin rResize := mReg 7
/-- Result / random sample scratch register `8`. -/
noncomputable abbrev mRes : Fin rResize := mReg 8
/-- Current address / pointer scratch register `9`. -/
noncomputable abbrev mCur : Fin rResize := mReg 9
/-- Loop index / end pointer scratch register `10`. -/
noncomputable abbrev mIdx : Fin rResize := mReg 10
/-- Constant-`0` register `11`. -/
noncomputable abbrev mZero : Fin rResize := mReg 11
/-- Constant-`1` register `12`. -/
noncomputable abbrev mOne : Fin rResize := mReg 12
/-- Active element count `n` register `13`. -/
noncomputable abbrev mCnt : Fin rResize := mReg 13
/-- Relocated item-base register `14`. -/
private noncomputable abbrev mItemBase : Fin rResize := mReg 14
/-- Hash-seed base register `15` (`metaBase + 225`). -/
private noncomputable abbrev mHashBase : Fin rResize := mReg 15

private noncomputable abbrev mNewMeta : Fin rResize := mReg 146
private noncomputable abbrev mArena : Fin rResize := mReg 147
private noncomputable abbrev mOldItemDst : Fin rResize := mReg 148
private noncomputable abbrev mNNew : Fin rResize := mReg 149
private noncomputable abbrev mOffNew : Fin rResize := mReg 150
private noncomputable abbrev mHSpaceNew : Fin rResize := mReg 151
private noncomputable abbrev mIwOld : Fin rResize := mReg 152
private noncomputable abbrev mIwNew : Fin rResize := mReg 153
private noncomputable abbrev mArenaWords : Fin rResize := mReg 154
private noncomputable abbrev mPeakFront : Fin rResize := mReg 155
private noncomputable abbrev mTmpA : Fin rResize := mReg 156
private noncomputable abbrev mTmpB : Fin rResize := mReg 157
private noncomputable abbrev mU0 : Fin rResize := mReg 158
private noncomputable abbrev mV0 : Fin rResize := mReg 159

@[simp] theorem epochEmb_rBase : epochEmb rBase = mBase := Fin.ext (by simp)
@[simp] theorem epochEmb_rTag : epochEmb rTag = mTag := Fin.ext (by simp)
@[simp] theorem epochEmb_rArgU : epochEmb rArgU = mArgU := Fin.ext (by simp)
@[simp] theorem epochEmb_rArgV : epochEmb rArgV = mArgV := Fin.ext (by simp)
@[simp] theorem epochEmb_rOutTag : epochEmb rOutTag = mOutTag := Fin.ext (by simp)
@[simp] theorem epochEmb_rOutVal : epochEmb rOutVal = mOutVal := Fin.ext (by simp)

private noncomputable def mOldHp (i : Fin 19) : Fin rResize := mReg ⟨32 + i.val, by omega⟩
private noncomputable def mOldCp (i : Fin 36) : Fin rResize := mReg ⟨52 + i.val, by omega⟩
private noncomputable def mNewHp (i : Fin 19) : Fin rResize := mReg ⟨90 + i.val, by omega⟩
private noncomputable def mNewCp (i : Fin 36) : Fin rResize := mReg ⟨110 + i.val, by omega⟩

@[simp] private theorem val_mOldHp (i : Fin 19) : (mOldHp i).val = 32 + i.val := rfl
@[simp] private theorem val_mOldCp (i : Fin 36) : (mOldCp i).val = 52 + i.val := rfl
@[simp] private theorem val_mNewHp (i : Fin 19) : (mNewHp i).val = 90 + i.val := rfl
@[simp] private theorem val_mNewCp (i : Fin 36) : (mNewCp i).val = 110 + i.val := rfl

private theorem mOldHp_lt_160 (i : Fin 19) : (mOldHp i).val < 160 := by rw [val_mOldHp]; omega
private theorem mOldCp_lt_160 (i : Fin 36) : (mOldCp i).val < 160 := by rw [val_mOldCp]; omega
private theorem mNewHp_lt_160 (i : Fin 19) : (mNewHp i).val < 160 := by rw [val_mNewHp]; omega
private theorem mNewCp_lt_160 (i : Fin 36) : (mNewCp i).val < 160 := by rw [val_mNewCp]; omega

private theorem mOldHp_inj : Function.Injective mOldHp := fun i j h =>
  Fin.ext (by have hv := congrArg Fin.val h; dsimp [mOldHp] at hv; omega)
private theorem mOldCp_inj : Function.Injective mOldCp := fun i j h =>
  Fin.ext (by have hv := congrArg Fin.val h; dsimp [mOldCp] at hv; omega)
private theorem mNewHp_inj : Function.Injective mNewHp := fun i j h =>
  Fin.ext (by have hv := congrArg Fin.val h; dsimp [mNewHp] at hv; omega)
private theorem mNewCp_inj : Function.Injective mNewCp := fun i j h =>
  Fin.ext (by have hv := congrArg Fin.val h; dsimp [mNewCp] at hv; omega)

private theorem mOldHp_ne_mReg (i : Fin 19) {c : Fin 160} (hc : c.val < 32 ∨ 51 ≤ c.val) :
    mOldHp i ≠ mReg c := fun h => by
  have hv := congrArg Fin.val h; rw [val_mOldHp, val_mReg] at hv; omega

private theorem mOldCp_ne_mReg (i : Fin 36) {c : Fin 160} (hc : c.val < 52 ∨ 88 ≤ c.val) :
    mOldCp i ≠ mReg c := fun h => by
  have hv := congrArg Fin.val h; rw [val_mOldCp, val_mReg] at hv; omega

private theorem mNewHp_ne_mReg (i : Fin 19) {c : Fin 160} (hc : c.val < 90 ∨ 109 ≤ c.val) :
    mNewHp i ≠ mReg c := fun h => by
  have hv := congrArg Fin.val h; rw [val_mNewHp, val_mReg] at hv; omega

private theorem mNewCp_ne_mReg (i : Fin 36) {c : Fin 160} (hc : c.val < 110 ∨ 146 ≤ c.val) :
    mNewCp i ≠ mReg c := fun h => by
  have hv := congrArg Fin.val h; rw [val_mNewCp, val_mReg] at hv; omega

theorem mGrow_nodup : ([mK, mRes, mCur, mIdx, mZero, mOne] : List (Fin rResize)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
    mK, mRes, mCur, mIdx, mZero, mOne, mReg_inj]
  decide

private theorem mShrink_nodup : ([mK, mIdx, mZero, mOne] : List (Fin rResize)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
    mK, mIdx, mZero, mOne, mReg_inj]
  decide

private theorem mResample_nodup :
    ([mHashBase, mNewHp ⟨3, by decide⟩, mNewHp ⟨2, by decide⟩, mNewHp ⟨10, by decide⟩,
      mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp [mHashBase, mNewHp, mCur, mIdx, mK, mOne, mRes] at hv ⊢

/-- Combined parameter-free exchange factor dominating `inEpochFactor` and all migration
`RealizesBounded` witnesses. -/
noncomputable def migFactor : ℕ :=
  max inEpochFactor <|
  max wTargetCap.factor <|
  max wWriteParams.factor <|
  max wCopyRight.factor <|
  max wCopyLeft.factor <|
  max wInitNewMeta.factor <|
  max wReadOldKV.factor <|
  max wStreamIns.factor
      wStreamAll.factor

private theorem inEpochFactor_le_migFactor : inEpochFactor ≤ migFactor := le_max_left _ _
private theorem one_le_migFactor
    : 1 ≤ migFactor := one_le_inEpochFactor.trans inEpochFactor_le_migFactor

private theorem factor_mItemWords_le : wItemWords.factor ≤ migFactor :=
  factor_wItemWords_le.trans inEpochFactor_le_migFactor
private theorem factor_wTargetCap_le : wTargetCap.factor ≤ migFactor :=
  le_max_of_le_right (le_max_left _ _)
private theorem factor_wWriteParams_le : wWriteParams.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
private theorem factor_wCopyRight_le : wCopyRight.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
private theorem factor_wCopyLeft_le : wCopyLeft.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_left _ _))))
private theorem factor_wInitNewMeta_le : wInitNewMeta.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_left _ _)))))
private theorem factor_wReadOldKV_le : wReadOldKV.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))
private theorem factor_wStreamIns_le : wStreamIns.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))
private theorem factor_wStreamAll_le : wStreamAll.factor ≤ migFactor :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))))

/-! ## Section 3: Witness Register Arrays (`src*`, `tmp*`) and Disjointness Proofs -/

private theorem migTmpHb {n : ℕ} (hb : n ≤ scratchMigrate) : 160 + n ≤ rResize :=
  (Nat.add_le_add_left hb 160).trans (le_max_right _ _)

private noncomputable def srcOldIw := pairSrc mOldCp (reg1 mCnt)
private noncomputable def tmpOldIw :=
  mkTmp (baseOff := 160) ![mIwOld] (migTmpHb (by dsimp [scratchMigrate]; exact le_max_left _ _))

private noncomputable def srcNewIw := pairSrc mNewCp (reg1 mCnt)
private noncomputable def tmpNewIw :=
  mkTmp (baseOff := 160) ![mIwNew] (migTmpHb (by dsimp [scratchMigrate]; exact le_max_left _ _))

private noncomputable def srcTargetCap := pairSrc (reg1 mBase) (reg1 mCnt)
private noncomputable def tmpTargetCap :=
  mkTmp (baseOff := 160) ![mNNew]
    (migTmpHb (by dsimp [scratchMigrate]; exact le_max_of_le_right (le_max_left _ _)))

private noncomputable def srcWriteParams :=
  pairSrc (pairSrc (reg1 mBase) (reg1 mTmpA))
    (pairSrc (reg1 mNNew) (pairSrc (reg1 mCnt) (reg1 mCnt)))
private noncomputable def tmpWriteParams :=
  mkTmp (baseOff := 160) ![mOffNew, mHSpaceNew]
    (migTmpHb (by
      dsimp [scratchMigrate]; exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))

private noncomputable def srcCopyRight :=
  pairSrc (pairSrc (reg1 mNewMeta) (reg1 mOldItemDst)) (reg1 mIwOld)
private noncomputable def tmpCopyRight :=
  mkTmp (baseOff := 160) ![] (migTmpHb (by
    dsimp [scratchMigrate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))

private noncomputable def srcCopyLeft :=
  pairSrc (pairSrc (reg1 mTmpA) (reg1 mTmpB)) (reg1 mCur)
private noncomputable def tmpCopyLeft :=
  mkTmp (baseOff := 160) ![] (migTmpHb (by
    dsimp [scratchMigrate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))))))

private noncomputable def srcInitNewMeta :=
  pairSrc (pairSrc mNewHp mNewCp) (reg1 mTmpA)
private noncomputable def tmpInitNewMeta :=
  mkTmp (baseOff := 160) ![] (migTmpHb (by
    dsimp [scratchMigrate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))

private noncomputable def srcReadOldKV :=
  pairSrc (pairSrc (pairSrc mOldHp mOldCp) (pairSrc (reg1 mBase) (reg1 mItemBase)))
    (reg1 mZero)
private noncomputable def tmpReadOldKV :=
  mkTmp (baseOff := 160) ![mU0, mV0] (migTmpHb (by
    dsimp [scratchMigrate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))))

private noncomputable def srcStreamIns :=
  pairSrc (pairSrc (pairSrc mNewHp mNewCp) (pairSrc (reg1 mBase) (reg1 mItemBase)))
    (pairSrc (reg1 mArgU) (reg1 mArgV))
private noncomputable def tmpStreamIns :=
  mkTmp (baseOff := 160) ![] (migTmpHb (by
    dsimp [scratchMigrate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))

private noncomputable def srcStreamAll :=
  pairSrc
    (pairSrc
      (pairSrc
        (pairSrc (pairSrc mOldHp mOldCp) (pairSrc (reg1 mBase) (reg1 mOldItemDst)))
        (pairSrc (pairSrc mNewHp mNewCp) (pairSrc (reg1 mNewMeta) (reg1 mArena))))
      (reg1 mZero))
    (reg1 mCnt)
private noncomputable def tmpStreamAll :=
  mkTmp (baseOff := 160) ![mCur] (migTmpHb (by
    dsimp [scratchMigrate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))))))

private theorem tmpOldIw_inj : Function.Injective tmpOldIw :=
  mkTmp_injective _ (outs1_inj mIwOld) (fun i => by fin_cases i; exact mReg_lt_160 _)
private theorem srcOldIw_ne_tmp : ∀ i j, srcOldIw i ≠ tmpOldIw j :=
  src_ne_mkTmp _ (pairSrc_lt mOldCp_lt_160 (fun _ => mReg_lt_160 _)) <|
    pairSrc_ne_outs (fun i a => by fin_cases a; exact mOldCp_ne_mReg i (Or.inr (by decide)))
      (fun _ a => by fin_cases a; exact mReg_ne (by decide))
private theorem tmpOldIw_ne_mFr : ∀ j, tmpOldIw j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a; exact mReg_ne (by decide))
private theorem srcOldIw_ne_mFr : ∀ i, srcOldIw i ≠ mFr :=
  pairSrc_ne_reg (fun i => mOldCp_ne_mReg i (Or.inl (by decide))) (fun _ => mReg_ne (by decide))

private theorem tmpNewIw_inj : Function.Injective tmpNewIw :=
  mkTmp_injective _ (outs1_inj mIwNew) (fun i => by fin_cases i; exact mReg_lt_160 _)
private theorem srcNewIw_ne_tmp : ∀ i j, srcNewIw i ≠ tmpNewIw j :=
  src_ne_mkTmp _ (pairSrc_lt mNewCp_lt_160 (fun _ => mReg_lt_160 _)) <|
    pairSrc_ne_outs (fun i a => by fin_cases a; exact mNewCp_ne_mReg i (Or.inr (by decide)))
      (fun _ a => by fin_cases a; exact mReg_ne (by decide))
private theorem tmpNewIw_ne_mFr : ∀ j, tmpNewIw j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a; exact mReg_ne (by decide))
private theorem srcNewIw_ne_mFr : ∀ i, srcNewIw i ≠ mFr :=
  pairSrc_ne_reg (fun i => mNewCp_ne_mReg i (Or.inl (by decide))) (fun _ => mReg_ne (by decide))

private theorem tmpTargetCap_inj : Function.Injective tmpTargetCap :=
  mkTmp_injective _ (outs1_inj mNNew) (fun i => by fin_cases i; exact mReg_lt_160 _)
private theorem srcTargetCap_ne_tmp : ∀ i j, srcTargetCap i ≠ tmpTargetCap j :=
  src_ne_mkTmp _ (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _)) <|
    pairSrc_ne_outs (fun _ a => by fin_cases a; exact mReg_ne (by decide))
      (fun _ a => by fin_cases a; exact mReg_ne (by decide))
private theorem tmpTargetCap_ne_mFr : ∀ j, tmpTargetCap j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a; exact mReg_ne (by decide))
private theorem srcTargetCap_ne_mFr : ∀ i, srcTargetCap i ≠ mFr :=
  pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide))

private theorem tmpWriteParams_inj : Function.Injective tmpWriteParams :=
  mkTmp_injective _ (outs2_inj (mReg_ne (by decide)))
    (fun i => by fin_cases i <;> exact mReg_lt_160 _)
private theorem srcWriteParams_ne_tmp : ∀ i j, srcWriteParams i ≠ tmpWriteParams j :=
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
private theorem tmpWriteParams_ne_mFr : ∀ j, tmpWriteParams j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a <;> exact mReg_ne (by decide))
private theorem srcWriteParams_ne_mFr : ∀ i, srcWriteParams i ≠ mFr :=
  pairSrc_ne_reg
    (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide)))
    (pairSrc_ne_reg (fun _ => mReg_ne (by decide))
      (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide))))

private theorem tmpCopyRight_inj : Function.Injective tmpCopyRight :=
  mkTmp_injective _ (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
private theorem srcCopyRight_ne_tmp : ∀ i j, srcCopyRight i ≠ tmpCopyRight j :=
  src_ne_mkTmp _
    (pairSrc_lt (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _))
      (fun _ => mReg_lt_160 _))
    (fun _ a => Fin.elim0 a)
private theorem tmpCopyRight_ne_mFr : ∀ j, tmpCopyRight j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => Fin.elim0 a)
private theorem srcCopyRight_ne_mFr : ∀ i, srcCopyRight i ≠ mFr :=
  pairSrc_ne_reg (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide)))
    (fun _ => mReg_ne (by decide))

private theorem tmpCopyLeft_inj : Function.Injective tmpCopyLeft :=
  mkTmp_injective _ (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
private theorem srcCopyLeft_ne_tmp : ∀ i j, srcCopyLeft i ≠ tmpCopyLeft j :=
  src_ne_mkTmp _
    (pairSrc_lt (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _))
      (fun _ => mReg_lt_160 _))
    (fun _ a => Fin.elim0 a)
private theorem tmpCopyLeft_ne_mFr : ∀ j, tmpCopyLeft j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => Fin.elim0 a)
private theorem srcCopyLeft_ne_mFr : ∀ i, srcCopyLeft i ≠ mFr :=
  pairSrc_ne_reg (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide)))
    (fun _ => mReg_ne (by decide))

private theorem tmpInitNewMeta_inj : Function.Injective tmpInitNewMeta :=
  mkTmp_injective _ (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
private theorem srcInitNewMeta_ne_tmp : ∀ i j, srcInitNewMeta i ≠ tmpInitNewMeta j :=
  src_ne_mkTmp _
    (pairSrc_lt (pairSrc_lt mNewHp_lt_160 mNewCp_lt_160) (fun _ => mReg_lt_160 _))
    (fun _ a => Fin.elim0 a)
private theorem tmpInitNewMeta_ne_mFr : ∀ j, tmpInitNewMeta j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => Fin.elim0 a)
private theorem srcInitNewMeta_ne_mFr : ∀ i, srcInitNewMeta i ≠ mFr :=
  pairSrc_ne_reg
    (pairSrc_ne_reg (fun i => mNewHp_ne_mReg i (Or.inl (by decide)))
      (fun i => mNewCp_ne_mReg i (Or.inl (by decide))))
    (fun _ => mReg_ne (by decide))

private theorem tmpReadOldKV_inj : Function.Injective tmpReadOldKV :=
  mkTmp_injective _ (outs2_inj (mReg_ne (by decide)))
    (fun i => by fin_cases i <;> exact mReg_lt_160 _)
private theorem srcReadOldKV_ne_tmp : ∀ i j, srcReadOldKV i ≠ tmpReadOldKV j :=
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
private theorem tmpReadOldKV_ne_mFr : ∀ j, tmpReadOldKV j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a <;> exact mReg_ne (by decide))
private theorem srcReadOldKV_ne_mFr : ∀ i, srcReadOldKV i ≠ mFr :=
  pairSrc_ne_reg
    (pairSrc_ne_reg
      (pairSrc_ne_reg (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))
        (fun i => mOldCp_ne_mReg i (Or.inl (by decide))))
      (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide))))
    (fun _ => mReg_ne (by decide))

private theorem tmpStreamIns_inj : Function.Injective tmpStreamIns :=
  mkTmp_injective _ (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
private theorem srcStreamIns_ne_tmp : ∀ i j, srcStreamIns i ≠ tmpStreamIns j :=
  src_ne_mkTmp _
    (pairSrc_lt
      (pairSrc_lt (pairSrc_lt mNewHp_lt_160 mNewCp_lt_160)
        (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _)))
      (pairSrc_lt (fun _ => mReg_lt_160 _) (fun _ => mReg_lt_160 _)))
    (fun _ a => Fin.elim0 a)
private theorem tmpStreamIns_ne_mFr : ∀ j, tmpStreamIns j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => Fin.elim0 a)
private theorem srcStreamIns_ne_mFr : ∀ i, srcStreamIns i ≠ mFr :=
  pairSrc_ne_reg
    (pairSrc_ne_reg
      (pairSrc_ne_reg (fun i => mNewHp_ne_mReg i (Or.inl (by decide)))
        (fun i => mNewCp_ne_mReg i (Or.inl (by decide))))
      (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide))))
    (pairSrc_ne_reg (fun _ => mReg_ne (by decide)) (fun _ => mReg_ne (by decide)))

private theorem tmpStreamAll_inj : Function.Injective tmpStreamAll :=
  mkTmp_injective _ (outs1_inj mCur) (fun i => by fin_cases i; exact mReg_lt_160 _)
private theorem srcStreamAll_ne_tmp : ∀ i j, srcStreamAll i ≠ tmpStreamAll j :=
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
private theorem tmpStreamAll_ne_mFr : ∀ j, tmpStreamAll j ≠ mFr :=
  mkTmp_ne_reg _ (mReg_lt_160 _) (fun a => by fin_cases a; exact mReg_ne (by decide))
private theorem srcStreamAll_ne_mFr : ∀ i, srcStreamAll i ≠ mFr :=
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

private theorem tmpOldIw_out :
    tmpOldIw (Fin.castAdd (wItemWords.scratchSize + 1) 0) = mIwOld := mkTmp_castAdd _ _ 0
private theorem tmpNewIw_out :
    tmpNewIw (Fin.castAdd (wItemWords.scratchSize + 1) 0) = mIwNew := mkTmp_castAdd _ _ 0
private theorem tmpTargetCap_out :
    tmpTargetCap (Fin.castAdd (wTargetCap.scratchSize + 1) 0) = mNNew := mkTmp_castAdd _ _ 0
private theorem tmpWriteParams_out_0 :
    tmpWriteParams (Fin.castAdd (wWriteParams.scratchSize + 1) 0) = mOffNew :=
  mkTmp_castAdd _ _ 0
private theorem tmpReadOldKV_out_0 :
    tmpReadOldKV (Fin.castAdd (wReadOldKV.scratchSize + 1) 0) = mU0 := mkTmp_castAdd _ _ 0

attribute [local irreducible]
  wTargetCap wWriteParams wCopyRight wCopyLeft
  wInitNewMeta wReadOldKV wStreamIns wStreamAll
  scratchMigrate rResize migFactor

/-! ## Section 4: Single-Tape `1 · OPT` Active Epoch Migration (`migrateActiveCode`) -/

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
private noncomputable def migrateSetupParamsCode : RCode .exact rResize :=
  .seq migrateLoadOldCode <|
  .seq (.op (.const mCur 63)) <|
  .seq (.op (.exactBin .add mTmpA mBase mCur)) <|
  .seq (RCode.ofCode (wWriteParams.code mFr srcWriteParams tmpWriteParams)) <|
  .seq (loadBlockUpTo mBase mCur mNewHp (63 + offHashParams) 18 (by decide)) <|
  .seq (loadBlockUpTo mBase mCur mNewCp (63 + offCompParams) 35 (by decide)) <|
  .seq (RCode.ofCode (wItemWords.code mFr srcNewIw tmpNewIw))
       migrateComputeArenaCode

/-- Second half of `migrateSetupCode`: grows `[x.frontier, peakF)` with zeroed words, shifts old
items rightward to `mOldItemDst`, writes new header/params at `mNewMeta`, and sets `mHashBase`. -/
private noncomputable def migrateSetupShiftCode : RCode .exact rResize :=
  .seq (growZeroCode mK mRes mCur mIdx mZero mOne) <|
  .seq (.op (.copy mFr mPeakFront)) <|
  .seq (RCode.ofCode (wCopyRight.code mFr srcCopyRight tmpCopyRight)) <|
  .seq (.op (.copy mTmpA mNewMeta)) <|
  .seq (RCode.ofCode (wWriteParams.code mFr srcWriteParams tmpWriteParams)) <|
  .seq (.op (.const mCur 225))
       (.op (.exactBin .add mHashBase mNewMeta mCur))

/-- Deterministic setup half of `migrateActiveCode` before `resampleHashCode`. -/
private noncomputable def migrateSetupCode : RCode .exact rResize :=
  .seq migrateSetupParamsCode migrateSetupShiftCode

/-- Zero the 5 scratch registers written by `resampleHashCode` (`5` instructions). -/
private noncomputable def zeroResampleRegsCode : RCode .exact rResize :=
  .seq (.op (.const mCur 0)) <|
  .seq (.op (.const mIdx 0)) <|
  .seq (.op (.const mK 0)) <|
  .seq (.op (.const mOne 0))
       (.op (.const mRes 0))

/-- First half of `migrateFinishCleanCode`: initializes new-epoch table/metadata and streams all
`n` entries from the right-aligned old item suffix into `(mNewMeta, mArena)`. -/
private noncomputable def migrateStreamBuildCode : RCode .exact rResize :=
  .seq (.op (.copy mTmpA mNewMeta)) <|
  .seq (RCode.ofCode (wInitNewMeta.code mFr srcInitNewMeta tmpInitNewMeta)) <|
  .seq (.op (.const mZero 0))
       (RCode.ofCode (wStreamAll.code mFr srcStreamAll tmpStreamAll))

/-- Second half of `migrateFinishCleanCode`: copies `(mNewMeta, mArena)` leftward to
`(base, base + offNew)` and shrinks `[frNew, peakF)`. -/
private noncomputable def migrateCompactBackCode : RCode .exact rResize :=
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

/-- Deterministic finish body after `zeroResampleRegsCode`. -/
private noncomputable def migrateFinishCleanCode : RCode .exact rResize :=
  .seq migrateStreamBuildCode migrateCompactBackCode

/-- Deterministic finish half of `migrateActiveCode` after `resampleHashCode`. -/
private noncomputable def migrateFinishCode : RCode .exact rResize :=
  .seq zeroResampleRegsCode migrateFinishCleanCode

/-- Parameter-free (`¬ReadsWidth`) native `RCode .exact rResize` single-tape `1 · OPT` streaming
rebuild from `(N_old, n, n_init_old)` to `(targetCap U n, n, n)`. -/
noncomputable def migrateActiveCode : RCode .exact rResize :=
  .seq migrateSetupCode <|
  .seq (resampleHashCode mHashBase (mNewHp ⟨3, by decide⟩) (mNewHp ⟨2, by decide⟩)
         (mNewHp ⟨10, by decide⟩) mCur mIdx mK mOne mRes)
       migrateFinishCode

private theorem not_readsWidth_zeroResampleRegsCode : ¬zeroResampleRegsCode.ReadsWidth := by
  simp [zeroResampleRegsCode, RCode.ReadsWidth, Op.ReadsWidth]

private theorem not_readsWidth_migrateLoadOldCode : ¬migrateLoadOldCode.ReadsWidth := by
  have h1 : ¬(RCode.ofCode (wItemWords.code mFr srcOldIw tmpOldIw)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wItemWords.code_spec mFr srcOldIw tmpOldIw
      tmpOldIw_inj srcOldIw_ne_tmp tmpOldIw_ne_mFr srcOldIw_ne_mFr).1
  have h2 : ¬(RCode.ofCode (wTargetCap.code mFr srcTargetCap tmpTargetCap)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wTargetCap.code_spec mFr srcTargetCap tmpTargetCap
      tmpTargetCap_inj srcTargetCap_ne_tmp tmpTargetCap_ne_mFr srcTargetCap_ne_mFr).1
  have hb1 := not_readsWidth_loadBlockUpTo mBase mCur mOldHp offHashParams 18 (by decide)
  have hb2 := not_readsWidth_loadBlockUpTo mBase mCur mOldCp offCompParams 35 (by decide)
  simp [migrateLoadOldCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    not_readsWidth_loadAtOffCode, hb1, hb2, h1, h2]

private theorem not_readsWidth_migrateComputeArenaCode : ¬migrateComputeArenaCode.ReadsWidth := by
  simp [migrateComputeArenaCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

private theorem not_readsWidth_migrateSetupCode : ¬migrateSetupCode.ReadsWidth := by
  have hwp : ¬(RCode.ofCode (wWriteParams.code mFr srcWriteParams tmpWriteParams)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wWriteParams.code_spec mFr srcWriteParams tmpWriteParams
      tmpWriteParams_inj srcWriteParams_ne_tmp tmpWriteParams_ne_mFr srcWriteParams_ne_mFr).1
  have hiw : ¬(RCode.ofCode (wItemWords.code mFr srcNewIw tmpNewIw)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wItemWords.code_spec mFr srcNewIw tmpNewIw
      tmpNewIw_inj srcNewIw_ne_tmp tmpNewIw_ne_mFr srcNewIw_ne_mFr).1
  have hcr : ¬(RCode.ofCode (wCopyRight.code mFr srcCopyRight tmpCopyRight)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wCopyRight.code_spec mFr srcCopyRight tmpCopyRight
      tmpCopyRight_inj srcCopyRight_ne_tmp tmpCopyRight_ne_mFr srcCopyRight_ne_mFr).1
  have hb1 := not_readsWidth_loadBlockUpTo mBase mCur mNewHp (63 + offHashParams) 18 (by decide)
  have hb2 := not_readsWidth_loadBlockUpTo mBase mCur mNewCp (63 + offCompParams) 35 (by decide)
  simp [migrateSetupCode, migrateSetupParamsCode, migrateSetupShiftCode,
    RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    not_readsWidth_migrateLoadOldCode, not_readsWidth_migrateComputeArenaCode,
    growZeroCode_not_readsWidth, hwp, hiw, hcr, hb1, hb2]

private theorem not_readsWidth_migrateFinishCode : ¬migrateFinishCode.ReadsWidth := by
  have him : ¬(RCode.ofCode (wInitNewMeta.code mFr srcInitNewMeta tmpInitNewMeta)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wInitNewMeta.code_spec mFr srcInitNewMeta tmpInitNewMeta
      tmpInitNewMeta_inj srcInitNewMeta_ne_tmp tmpInitNewMeta_ne_mFr srcInitNewMeta_ne_mFr).1
  have hsa : ¬(RCode.ofCode (wStreamAll.code mFr srcStreamAll tmpStreamAll)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wStreamAll.code_spec mFr srcStreamAll tmpStreamAll
      tmpStreamAll_inj srcStreamAll_ne_tmp tmpStreamAll_ne_mFr srcStreamAll_ne_mFr).1
  have hcl : ¬(RCode.ofCode (wCopyLeft.code mFr srcCopyLeft tmpCopyLeft)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wCopyLeft.code_spec mFr srcCopyLeft tmpCopyLeft
      tmpCopyLeft_inj srcCopyLeft_ne_tmp tmpCopyLeft_ne_mFr srcCopyLeft_ne_mFr).1
  simp [migrateFinishCode, migrateFinishCleanCode, migrateStreamBuildCode, migrateCompactBackCode,
    RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    not_readsWidth_zeroResampleRegsCode, shrinkCode_not_readsWidth, him, hsa, hcl]

/-- `migrateActiveCode` does not inspect the ambient word width `w` (`¬ReadsWidth`). -/
theorem not_readsWidth_migrateActiveCode : ¬migrateActiveCode.ReadsWidth := by
  simp [migrateActiveCode, RCode.ReadsWidth, not_readsWidth_migrateSetupCode,
    not_readsWidth_resampleHashCode, not_readsWidth_migrateFinishCode]

private theorem targetCap_bounds_of_pos {U n : ℕ} (hn : 1 ≤ n) (hnU : n ≤ U) :
    1 ≤ targetCap U n ∧ n ≤ targetCap U n ∧ targetCap U n ≤ 2 * n ∧ targetCap U n ≤ U := by
  unfold targetCap
  rw [ite_eq_right (by omega)]
  exact ⟨le_min (by omega) (hn.trans hnU), le_min (by omega) hnU,
    min_le_left _ _, min_le_right _ _⟩

private theorem fixedCoupled_of_shift {metaBase srcItemBase dstItemBase U V w N n : ℕ}
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
  have hq_eq : compQuotAt dstItemBase U V w N n s₁.mem = compQuotAt srcItemBase U V w N n s₀.mem :=
    by
      rw [← compQuotAt_congr (itemBase := srcItemBase) (U := U) (V := V) (N := N) (n := n) hw
        hitem_congr]
      funext idx; unfold compQuotAt readBitSlice; dsimp only
      split_ifs <;> [simp only [Nat.add_assoc, hmem_sh_add]; rfl]
  have hv_eq : compValAt dstItemBase U V w N n s₁.mem = compValAt srcItemBase U V w N n s₀.mem :=
    by
      rw [← compValAt_congr (itemBase := srcItemBase) (U := U) (V := V) (N := N) (n := n) hw
        hitem_congr]
      funext idx; unfold compValAt readBitSlice; dsimp only
      split_ifs <;> [simp only [Nat.add_assoc, hmem_sh_add]; rfl]
  have htot₁ : totalSlots N (compGmAt metaBase U w N s₁.mem) = n :=
    (congrArg (totalSlots N) hgm_eq).trans htot
  refine ⟨⟨hgm_eq.trans hcpl.gm_eq, hlm_eq.trans hcpl.lm_eq,
      by rw [hgm_eq, htd_eq, hdt_eq]; exact hcpl.win_inv,
      fun i => by rw [htd_eq]; exact hcpl.td_lt i,
      fun i => by rw [hdt_eq]; exact hcpl.dt_lt i,
      fun d hd => by
        have hd_n : d < n := by change d < totalSlots N _ at hd; omega
        have hd₀ : d < epochTotalSlots N (compGmAt metaBase U w N s₀.mem) := by
          change d < totalSlots N _; omega
        rw [compQuotAt_of_lt s₁.mem hd hd_n, hq_eq, compQuotAt_of_lt s₀.mem hd_n hd₀,
          hgm_eq, hdt_eq]
        exact hcpl.quot_eq d hd₀,
      fun d hd => by
        have hd_n : d < n := by change d < totalSlots N _ at hd; omega
        have hd₀ : d < epochTotalSlots N (compGmAt metaBase U w N s₀.mem) := by
          change d < totalSlots N _; omega
        rw [compValAt_of_lt s₁.mem hd hd_n, hv_eq, compValAt_of_lt s₀.mem hd_n hd₀,
          hgm_eq, hdt_eq]
        exact hcpl.val_eq d hd₀⟩,
    hgm_eq⟩

private def abiPreserved (x y : RData rResize) : Prop :=
  y.regs mBase = x.regs mBase ∧
  y.regs mTag = x.regs mTag ∧
  y.regs mArgU = x.regs mArgU ∧
  y.regs mArgV = x.regs mArgV

private theorem abiPreserved_trans {x y z : RData rResize}
    (h₁ : abiPreserved x y) (h₂ : abiPreserved y z) : abiPreserved x z :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

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
  have h225_old : 225 ≤ offCompItems U w N_old := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
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
  have hx₃_cnt : x₃.regs mCnt = n := by
    rw [hx₃_r mCnt (mReg_ne (by decide)) (fun i => mOldCp_ne_mReg i (Or.inl (by decide))),
      hx₂_r mCnt (mReg_ne (by decide)) (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))]
    exact hx₁_cnt
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
    have h0 := hout_iw 0
    rwa [tmpOldIw_out, clientResult_compItemWordsGenProg hw] at h0
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
  set x₆ := x₅.set mNewMeta (base + offCompItems U w N_old)
  have hex_nm := RDemonicExec.exactBin (f := .add) (d := mNewMeta) (i := mBase)
    (j := mOldCp idx34) (w := w) (L_peak := L_peak) (x := x₅)
    (hx₅f_eq.le.trans hL) (v := base + offCompItems U w N_old)
    (by
      change some (x₅.regs mBase + x₅.regs (mOldCp idx34)) = some (base + offCompItems U w N_old)
      rw [hx₅_base, hx₅_cp34])
    (hfit_fr.of_le (by rw [hfr, hce_old]; omega))
  have hx₆b : x₆.Bounded w := hx₅b.set (hfit_fr.of_le (by rw [hfr, hce_old]; omega))
  set x₇ := x₆.set mFr x.frontier
  have hfr_sum : (base + offCompItems U w N_old) + compactedItemWords U V w N_old n = x.frontier :=
    by rw [hfr, hce_old]; omega
  have hex_fr := RDemonicExec.exactBin (f := .add) (d := mFr) (i := mNewMeta) (j := mIwOld)
    (w := w) (L_peak := L_peak) (x := x₆) (hx₅f_eq.le.trans hL) (v := x.frontier)
    (by
      change some (x₆.regs mNewMeta + x₆.regs mIwOld) = some x.frontier
      simp [x₆, RData.set, hx₅_iw, hfr_sum])
    hfit_fr
  have hx₇b : x₇.Bounded w := hx₆b.set hfit_fr
  have hx₇m : x₇.mem = x.mem := hx₅m
  have hx₇f : x₇.frontier = x.frontier := hx₅f_eq
  have hms₇ : memoryState mFr x₇.toData = ⟨x.mem, x.frontier⟩ :=
    Memory.State.ext hx₇m (by dsimp [memoryState, x₇, RData.set, RData.toData]; simp)
  have hx₇_base : x₇.regs mBase = base := by simp [x₇, x₆, RData.set, hx₅_base]
  have hx₇_cnt : x₇.regs mCnt = n := by
    dsimp only [x₇, x₆, RData.set]
    rw [Function.update_of_ne (mReg_ne (by decide) : mCnt ≠ mFr),
      Function.update_of_ne (mReg_ne (by decide) : mCnt ≠ mNewMeta)]
    exact (hx₅_keep mCnt (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans hx₃_cnt
  have hin_tc : x₇.regs ∘ srcTargetCap = WordEncoding.encode (base, n) :=
    (regs_pairSrc (regs_reg1_eq mBase hx₇_base) (regs_reg1_eq mCnt hx₇_cnt)).eq
  obtain ⟨hpre_tc, hv_tc, hst_tc, hres_tc, hc_tc⟩ :=
    computeTargetCapProg_spec (s := ⟨x.mem, x.frontier⟩) hsplit.root_hdr
      (by change base < x.frontier; rw [hfr, hce_old]; omega) hnU hfit1
  have hnoalloc_tc : ((Memory.spec 0).clientState (memoryState mFr x₇.toData)
      (computeTargetCapProg (base, n))).frontier ≤ x₇.frontier := by
    rw [hms₇, hst_tc, hx₇f]
  obtain ⟨y, hex_tc, hyb, hyf, hm_tc, hout_tc, hframe_tc⟩ :=
    execWitness wTargetCap factor_wTargetCap_le mFr srcTargetCap tmpTargetCap
      tmpTargetCap_inj srcTargetCap_ne_tmp tmpTargetCap_ne_mFr srcTargetCap_ne_mFr
      (base, n) hx₇b (hx₇f.le.trans hL) hin_tc (hms₇ ▸ hpre_tc) (hms₇ ▸ hv_tc) hnoalloc_tc
  rw [hms₇, hst_tc] at hm_tc
  rw [hms₇, hres_tc] at hout_tc
  have hym : y.mem = x.mem := congrArg Memory.State.mem hm_tc
  have hy_fr_reg : y.regs mFr = x.frontier := congrArg Memory.State.frontier hm_tc
  have hy_nnew : y.regs mNNew = targetCap U n := by
    have h0 := hout_tc 0; rwa [tmpTargetCap_out] at h0
  have hy_keep : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mNNew → y.regs reg = x₇.regs reg :=
    fun reg hfr' h160 hnn =>
      hframe_tc reg hfr' (mkTmp_ne_reg _ h160 (fun a => by fin_cases a; exact hnn.symm))
  have hf1 := one_le_migFactor
  have hcost_tc : migFactor * (memoryCost (computeTargetCapProg (base, n))
      (memoryState mFr x₇.toData) + 1) ≤ 2 * migFactor := by
    rw [hms₇]
    have hmul := Nat.mul_le_mul_left migFactor (Nat.add_le_add_right hc_tc 1)
    omega
  have hex_all := hex_ldn.seq_eq (hex_hp.seq_eq (hex_cp.seq_eq (hex_zfr.seq_eq
    (hex_iw.seq_eq (hex_nm.seq_eq (hex_fr.seq_eq
      (hex_tc.mono hcost_tc (fun _ h => h))))))))
  refine ⟨y, hex_all.mono (by omega) (fun _ h => h), hyb, hym, hyf.trans hx₇f, ?_, ?_, ?_, ?_,
    hy_fr_reg, hy_nnew, fun i => ?_, fun i => ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hy_keep mBase (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
        (hx₇_base.trans hbase.symm)
    · exact (hy_keep mTag (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
        (by
          dsimp only [x₇, x₆, RData.set]
          rw [Function.update_of_ne (mReg_ne (by decide) : mTag ≠ mFr),
            Function.update_of_ne (mReg_ne (by decide) : mTag ≠ mNewMeta)]
          exact (hx₅_keep mTag (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
            (hpres₃ (c := 2) (Or.inl (by decide)) (by decide) (by decide)))
    · exact (hy_keep mArgU (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
        (by
          dsimp only [x₇, x₆, RData.set]
          rw [Function.update_of_ne (mReg_ne (by decide) : mArgU ≠ mFr),
            Function.update_of_ne (mReg_ne (by decide) : mArgU ≠ mNewMeta)]
          exact (hx₅_keep mArgU (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
            (hpres₃ (c := 3) (Or.inl (by decide)) (by decide) (by decide)))
    · exact (hy_keep mArgV (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
        (by
          dsimp only [x₇, x₆, RData.set]
          rw [Function.update_of_ne (mReg_ne (by decide) : mArgV ≠ mFr),
            Function.update_of_ne (mReg_ne (by decide) : mArgV ≠ mNewMeta)]
          exact (hx₅_keep mArgV (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
            (hpres₃ (c := 4) (Or.inl (by decide)) (by decide) (by decide)))
  · exact (hy_keep mCnt (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans hx₇_cnt
  · exact (hy_keep mIwOld (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
      (by simp [x₇, x₆, RData.set, hx₅_iw])
  · exact (hy_keep mNewMeta (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
      (by simp [x₇, x₆, RData.set])
  · rw [hy_keep (mOldHp i) (mOldHp_ne_mReg i (Or.inl (by decide))) (mOldHp_lt_160 i)
      (mOldHp_ne_mReg i (Or.inr (by decide)))]
    dsimp only [x₇, x₆, RData.set]
    rw [Function.update_of_ne (mOldHp_ne_mReg i (c := 1) (Or.inl (by decide))),
      Function.update_of_ne (mOldHp_ne_mReg i (c := 146) (Or.inr (by decide)))]
    exact (hx₅_keep (mOldHp i) (mOldHp_ne_mReg i (Or.inl (by decide))) (mOldHp_lt_160 i)
      (mOldHp_ne_mReg i (Or.inr (by decide)))).trans (hx₃_hp_all i)
  · rw [hy_keep (mOldCp i) (mOldCp_ne_mReg i (Or.inl (by decide))) (mOldCp_lt_160 i)
      (mOldCp_ne_mReg i (Or.inr (by decide)))]
    dsimp only [x₇, x₆, RData.set]
    rw [Function.update_of_ne (mOldCp_ne_mReg i (c := 1) (Or.inl (by decide))),
      Function.update_of_ne (mOldCp_ne_mReg i (c := 146) (Or.inr (by decide)))]
    exact (hx₅_keep (mOldCp i) (mOldCp_ne_mReg i (Or.inl (by decide))) (mOldCp_lt_160 i)
      (mOldCp_ne_mReg i (Or.inr (by decide)))).trans (hx₃_cp_all i)

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
  have hex_max : ∃ x₁ : RData rResize,
      RDemonicExec (B := .exact) w L_peak
        (.branch (.lt mIwOld mIwNew) (.op (.copy mArenaWords mIwNew))
          (.op (.copy mArenaWords mIwOld))) x 3 (· = x₁) ∧
      x₁ = x.set mArenaWords (max iwOld iwNew) := by
    by_cases hlt : iwOld < iwNew
    · have hc : (Cond.lt mIwOld mIwNew).Holds x.toData := by
        change x.regs mIwOld < x.regs mIwNew; omega
      have hcp := RDemonicExec.copy (B := .exact) (w := w) (d := mArenaWords) (s := mIwNew)
        (x := x) hL
      rw [h_iwn, ← Nat.max_eq_right hlt.le] at hcp
      exact ⟨_, (RDemonicExec.branch_pos hc hcp).mono (by omega) (fun _ h => h), rfl⟩
    · have hnc : ¬(Cond.lt mIwOld mIwNew).Holds x.toData := by
        change ¬x.regs mIwOld < x.regs mIwNew; omega
      have hcp := RDemonicExec.copy (B := .exact) (w := w) (d := mArenaWords) (s := mIwOld)
        (x := x) hL
      rw [h_iwo, ← Nat.max_eq_left (Nat.le_of_not_lt hlt)] at hcp
      exact ⟨_, RDemonicExec.branch_neg hnc hcp, rfl⟩
  obtain ⟨x₁, hex₁, hx₁_eq⟩ := hex_max
  have hle_max : max iwOld iwNew ≤ newMeta + offNew + (max iwOld iwNew + 6) := by omega
  have hx₁b : x₁.Bounded w := hx₁_eq ▸ hx.set (hfit_peak.of_le hle_max)
  have hx₁f : x₁.frontier = x.frontier := by rw [hx₁_eq]; rfl
  have hx₁m : x₁.mem = x.mem := by rw [hx₁_eq]; rfl
  set x₂ := x₁.set mCur 6
  have hex₂ := RDemonicExec.const (B := .exact) (d := mCur) (v := 6) (x := x₁) (hx₁f.le.trans hL)
    (hfit_peak.of_le (by omega))
  have hx₂b : x₂.Bounded w := hx₁b.set (hfit_peak.of_le (by omega))
  set x₃ := x₂.set mArenaWords arenaW
  have hex₃ := RDemonicExec.exactBin (f := .add) (d := mArenaWords) (i := mArenaWords) (j := mCur)
    (w := w) (L_peak := L_peak) (x := x₂) (hx₁f.le.trans hL) (v := arenaW)
    (by simp [BinOp.evalExact, x₂, hx₁_eq, RData.set, arenaW])
    (hfit_peak.of_le (by dsimp only [arenaW]; omega))
  have hx₃b : x₃.Bounded w := hx₂b.set (hfit_peak.of_le (by dsimp only [arenaW]; omega))
  set x₄ := x₃.set mArena arenaB
  have hex₄ := RDemonicExec.exactBin (f := .add) (d := mArena) (i := mNewMeta) (j := mOffNew)
    (w := w) (L_peak := L_peak) (x := x₃) (hx₁f.le.trans hL) (v := arenaB)
    (by simp [BinOp.evalExact, x₃, x₂, hx₁_eq, RData.set, h_nm, h_on, arenaB])
    (hfit_peak.of_le (by dsimp only [arenaB]; omega))
  have hx₄b : x₄.Bounded w := hx₃b.set (hfit_peak.of_le (by dsimp only [arenaB]; omega))
  set x₅ := x₄.set mPeakFront peakF
  have hex₅ := RDemonicExec.exactBin (f := .add) (d := mPeakFront) (i := mArena) (j := mArenaWords)
    (w := w) (L_peak := L_peak) (x := x₄) (hx₁f.le.trans hL) (v := peakF)
    (by simp [BinOp.evalExact, x₄, x₃, RData.set, peakF])
    hfit_peak
  have hx₅b : x₅.Bounded w := hx₄b.set hfit_peak
  have hfr_le_peak : frOld ≤ peakF := by
    have : iwOld ≤ arenaW := (le_max_left _ _).trans (Nat.le_add_right _ 6)
    dsimp only [peakF, arenaB]; omega
  set x₆ := x₅.set mK (peakF - frOld)
  have hex₆ := RDemonicExec.exactBin (f := .sub) (d := mK) (i := mPeakFront) (j := mFr)
    (w := w) (L_peak := L_peak) (x := x₅) (hx₁f.le.trans hL) (v := peakF - frOld)
    (by simp [BinOp.evalExact, x₅, x₄, x₃, x₂, hx₁_eq, RData.set, h_fr, hfr_le_peak])
    (hfit_peak.of_le (Nat.sub_le _ _))
  have hx₆b : x₆.Bounded w := hx₅b.set (hfit_peak.of_le (Nat.sub_le _ _))
  have hiwo_le_aw : iwOld ≤ arenaW := (le_max_left _ _).trans (Nat.le_add_right _ 6)
  have hdst_eq : peakF - iwOld = arenaB + (arenaW - iwOld) := by dsimp only [peakF]; omega
  have hiwo_le_peak : iwOld ≤ peakF := by dsimp only [peakF]; omega
  set y := x₆.set mOldItemDst (arenaB + (arenaW - iwOld))
  have hex₇ := RDemonicExec.exactBin (f := .sub) (d := mOldItemDst) (i := mPeakFront) (j := mIwOld)
    (w := w) (L_peak := L_peak) (x := x₆) (hx₁f.le.trans hL) (v := arenaB + (arenaW - iwOld))
    (by simp [BinOp.evalExact, x₆, x₅, x₄, x₃, x₂, hx₁_eq, RData.set, h_iwo, hiwo_le_peak, hdst_eq])
    (hfit_peak.of_le (by omega))
  have hyb : y.Bounded w := hx₆b.set (hfit_peak.of_le (by omega))
  refine ⟨y,
    (hex₁.seq_eq (hex₂.seq_eq (hex₃.seq_eq (hex₄.seq_eq (hex₅.seq_eq
      (hex₆.seq_eq hex₇)))))).mono (by omega) (fun _ h => h),
    hyb, hx₁m, hx₁f, ?_, ?_, ?_, ?_, ?_, fun reg hreg => ?_⟩
  · simp [y, x₆, x₅, x₄, x₃, RData.set]
  · simp [y, x₆, x₅, x₄, RData.set]
  · simp [y, x₆, x₅, RData.set]
  · simp [y, x₆, RData.set]
  · simp [y, RData.set]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hreg
    simp [y, x₆, x₅, x₄, x₃, x₂, hx₁_eq, RData.set,
      Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6]

/-- Parameter-free linear instruction factor `120000 * migFactor` per migrated item (`1 ≤ n`),
covering `migrateSetupCode`, `resampleHashCode`, `migrateFinishCode`, and the post-migration
`inEpochPotential` of the rebuilt epoch. -/
@[expose]
noncomputable def migLinearFactor : ℕ :=
  120000 * migFactor

private theorem zeroResampleRegsCode_exec {w L_peak w₀ b b' hashBase : ℕ}
    {θ : ReducedPolySeed w₀ b b' 3} {x y : RData rResize}
    (hx : x.Bounded w) (hy_fr : y.frontier = x.frontier) (hL : x.frontier ≤ L_peak)
    (hw₀ : w₀ ≤ w)
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfr_h : hashBase + ReducedKWise.seedWords w₀ b b' 3 ≤ x.frontier)
    (hseed : ReducedKWise.SeedRep hashBase w₀ b b' 3 θ y.mem)
    (hframe_mem : ∀ a, (a < hashBase ∨ hashBase + ReducedKWise.seedWords w₀ b b' 3 ≤ a) →
      y.mem a = x.mem a)
    (hframe_reg : ∀ j, j ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
      y.regs j = x.regs j) :
    ∃ z : RData rResize,
      z = (((((y.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0) ∧
      RDemonicExec w L_peak zeroResampleRegsCode y 5 (· = z) ∧
      z.Bounded w ∧ z.mem = y.mem ∧ z.frontier = x.frontier ∧
      ∀ j, j ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) → z.regs j = x.regs j := by
  have hyL : y.frontier ≤ L_peak := hy_fr.le.trans hL
  have hfz : Fits w 0 := fits_zero w
  set z₁ := y.set mCur 0
  have s1 := RDemonicExec.const (B := .exact) (d := mCur) (v := 0) (x := y) hyL hfz
  set z₂ := z₁.set mIdx 0
  have s2 := RDemonicExec.const (B := .exact) (d := mIdx) (v := 0) (x := z₁) hyL hfz
  set z₃ := z₂.set mK 0
  have s3 := RDemonicExec.const (B := .exact) (d := mK) (v := 0) (x := z₂) hyL hfz
  set z₄ := z₃.set mOne 0
  have s4 := RDemonicExec.const (B := .exact) (d := mOne) (v := 0) (x := z₃) hyL hfz
  set z := z₄.set mRes 0
  have s5 := RDemonicExec.const (B := .exact) (d := mRes) (v := 0) (x := z₄) hyL hfz
  refine ⟨z, rfl,
    (s1.seq_eq (s2.seq_eq (s3.seq_eq (s4.seq_eq s5)))).mono (by omega) (fun _ h => h),
    ⟨⟨fun j => ?_, fun a => ?_⟩, hy_fr ▸ hx.frontier_fits, fun a ha => ?_⟩,
    rfl, hy_fr, fun j hj => ?_⟩
  · dsimp only [z, z₄, z₃, z₂, z₁, RData.set, RData.toData]
    by_cases h1 : j = mRes
    · subst h1; rw [Function.update_self]; exact hfz
    rw [Function.update_of_ne h1]
    by_cases h2 : j = mOne
    · subst h2; rw [Function.update_self]; exact hfz
    rw [Function.update_of_ne h2]
    by_cases h3 : j = mK
    · subst h3; rw [Function.update_self]; exact hfz
    rw [Function.update_of_ne h3]
    by_cases h4 : j = mIdx
    · subst h4; rw [Function.update_self]; exact hfz
    rw [Function.update_of_ne h4]
    by_cases h5 : j = mCur
    · subst h5; rw [Function.update_self]; exact hfz
    rw [Function.update_of_ne h5]
    have hj_not : j ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h5, h4, h3, h2, h1⟩
    rw [hframe_reg j hj_not]
    exact hx.regs_fits j
  · dsimp only [z, z₄, z₃, z₂, z₁, RData.set, RData.toData]
    by_cases ha_out : a < hashBase ∨ hashBase + ReducedKWise.seedWords w₀ b b' 3 ≤ a
    · rw [hframe_mem a ha_out]; exact hx.mem_fits a
    · rw [not_or, not_lt, not_le] at ha_out
      rcases eq_or_lt_of_le ha_out.1 with rfl | ha_gt
      · rw [hseed.1]
        exact lt_of_lt_of_le θ.1.isLt (Nat.pow_le_pow_right two_pos (by omega))
      · set t := reducedTrinomialStep w₀ b b'
        set c := reducedChunkBits t
        set L := reducedLimbCount t
        have hsw : ReducedKWise.seedWords w₀ b b' 3 = 1 + 3 * L := rfl
        have hoff_lt : a - (hashBase + 1) < 3 * L := by omega
        have hL_pos : 0 < L := by omega
        let m : Fin L := ⟨(a - (hashBase + 1)) % L, Nat.mod_lt _ hL_pos⟩
        let j : Fin 3 := ⟨(a - (hashBase + 1)) / L,
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩
        have haddr : hashBase + 1 + (m.val + L * j.val) = a := by
          have hmod := Nat.mod_add_div (a - (hashBase + 1)) L
          dsimp only [m, j]; omega
        rw [← haddr, hseed.2 j m]
        exact lt_of_lt_of_le (getLimb_lt c _ _) (Nat.pow_le_pow_right two_pos (by omega))
  · dsimp only [z, z₄, z₃, z₂, z₁, RData.set] at ha ⊢
    rw [hframe_mem a (Or.inr (by omega))]
    exact hx.zero_above (hy_fr ▸ ha)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    obtain ⟨h5, h4, h3, h2, h1⟩ := hj
    dsimp only [z, z₄, z₃, z₂, z₁, RData.set]
    rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5]
    exact hframe_reg j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h5, h4, h3, h2, h1⟩)

private theorem rootHeaderValid_congr {U V w N n n_init metaBase : ℕ} {mem₁ mem₂ : ℕ → ℕ}
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

private theorem epochParamsStored_congr {U V w N metaBase : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hpar : EpochParamsStored U V w N metaBase mem₂)
    (heq : ∀ a, metaBase ≤ a ∧ a < metaBase + 63 → mem₁ a = mem₂ a) :
    EpochParamsStored U V w N metaBase mem₁ :=
  ⟨fun i => (heq _ ⟨by unfold offHashParams; omega, by unfold offHashParams; omega⟩).trans
      (hpar.hp_eq i),
   fun i => (heq _ ⟨by unfold offCompParams; omega, by unfold offCompParams; omega⟩).trans
      (hpar.cp_eq i)⟩

private theorem ne_mReg_of_lt_five {reg : Fin rResize} (h5 : reg.val < 5)
    {c : Fin 160} (hc : 5 ≤ c.val) : reg ≠ mReg c := fun h => by
  have hv := congrArg Fin.val h; rw [val_mReg] at hv; omega

private theorem migrateSetupParamsCode_exec {U V w N_old n n_init base : ℕ}
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
  have h225_old : 225 ≤ offCompItems U w N_old := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
  have h225_new : 225 ≤ offNew := by
    dsimp only [offNew]
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
  have hpeak_raw : base + migratePeakWords U V w N_old n = arenaB + arenaW := by
    unfold migratePeakWords
    dsimp only [arenaB, arenaW, newMeta, offNew, N_new, iwOld, iwNew]
    omega
  have hpeak_eq : peakF = arenaB + arenaW := hpeak_raw
  have hfit_ar : Fits w (arenaB + arenaW) := hpeak_raw ▸ hfit_peak
  have haw_def : arenaW = max iwOld iwNew + 6 := rfl
  have hiwn_le_aw : iwNew ≤ arenaW := (le_max_right _ _).trans (Nat.le_add_right _ 6)
  have hfr_le_peak : x.frontier ≤ peakF := by
    rw [hfr, hce_old, hpeak_eq]; dsimp only [arenaB, newMeta]; omega
  have hfit63 : Fits w 63 := hfit_ar.of_le (by dsimp only [arenaB]; omega)
  have hfit_n : Fits w n := hsplit.root_hdr.fits_U.of_le hnU
  obtain ⟨s₁, hex₁, hs₁b, hs₁m, hs₁f, habi₁, hs₁_cnt, hs₁_iwo, hs₁_nm, hs₁_fr, hs₁_nn,
      hs₁_ohp, hs₁_ocp⟩ :=
    migrateLoadOldCode_exec hx hn hev hfr hfr_le_peak hsplit hbase
  set s₂ := s₁.set mCur 63
  have hex₂ := RDemonicExec.const (B := .exact) (d := mCur) (v := 63) (x := s₁)
    (hs₁f.le.trans hfr_le_peak) hfit63
  set s₃ := s₂.set mTmpA (base + 63)
  have hs₁_base : s₁.regs mBase = base := habi₁.1.trans hbase
  have hex₃ := RDemonicExec.exactBin (f := .add) (d := mTmpA) (i := mBase) (j := mCur)
    (w := w) (L_peak := peakF) (x := s₂) (hs₁f.le.trans hfr_le_peak) (v := base + 63)
    (by simp [BinOp.evalExact, s₂, RData.set, hs₁_base])
    (hfit_ar.of_le (by dsimp only [arenaB, newMeta]; omega))
  have hs₃b : s₃.Bounded w := (hs₁b.set hfit63).set
    (hfit_ar.of_le (by dsimp only [arenaB, newMeta]; omega))
  have hms₃ : memoryState mFr s₃.toData = ⟨x.mem, x.frontier⟩ :=
    Memory.State.ext hs₁m (by
      dsimp only [memoryState, s₃, s₂, RData.set, RData.toData]
      rw [Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mTmpA),
        Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mCur)]
      exact hs₁_fr)
  have hin_wp1 : s₃.regs ∘ srcWriteParams =
      WordEncoding.encode (((base, base + 63), (N_new, (n, n)))) := by
    refine (regs_pairSrc
      (regs_pairSrc (regs_reg1_eq mBase ?_) (regs_reg1_eq mTmpA ?_))
      (regs_pairSrc (regs_reg1_eq mNNew ?_)
        (regs_pairSrc (regs_reg1_eq mCnt ?_) (regs_reg1_eq mCnt ?_)))).eq
    · simp [s₃, s₂, RData.set, hs₁_base]
    · simp [s₃, RData.set]
    · simp [s₃, s₂, RData.set, hs₁_nn, N_new]
    · simp [s₃, s₂, RData.set, hs₁_cnt]
    · simp [s₃, s₂, RData.set, hs₁_cnt]
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
  rw [hms₃] at hm_wp1 hout_wp1 hex_wp1
  rw [hres_wp1] at hout_wp1
  have hs₄f_eq : s₄.frontier = x.frontier := hs₄f.trans hs₁f
  have hs₄_fr_reg : s₄.regs mFr = x.frontier :=
    (congrArg Memory.State.frontier hm_wp1).trans hfr_wp1
  have hs₄_off : s₄.regs mOffNew = offNew := by
    have h0 := hout_wp1 0; rwa [tmpWriteParams_out_0] at h0
  have hs₄_mem_eq : s₄.mem = ((Memory.spec 0).clientState ⟨x.mem, x.frontier⟩
      (writeEpochParamsGenProg ((base, base + 63), (N_new, (n, n))))).mem :=
    congrArg Memory.State.mem hm_wp1
  have hs₄_out : ∀ a, (a < base + offScratch ∨ base + epochHdrWords ≤ a) → s₄.mem a = x.mem a :=
    fun a ha => by
      rw [hs₄_mem_eq]
      exact hframe_wp1 a (by unfold offScratch epochHdrWords at *; omega)
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
      mkHashParams w (epochQBits U N_new) (epochHashB N_new) (totalMicroBits N_new) 3 i := fun i =>
    by
      rw [hs₆_r (mNewHp i) (mNewHp_ne_mReg i (Or.inl (by decide)))
        (fun j => by intro h; have hv := congrArg Fin.val h; simp at hv; omega),
        hs₅_nhp i (by omega), hs₄_mem_eq,
        show base + (63 + offHashParams) + i.val = (base + 63) + offHashParams + i.val by omega]
      exact hpar_wp1.hp_eq i
  have hs₆_ncp_all : ∀ i : Fin 36, s₆.regs (mNewCp i) = mkCompParams U V w N_new i := fun i => by
    rw [hs₆_ncp i (by omega), hs₅m, hs₄_mem_eq,
      show base + (63 + offCompParams) + i.val = (base + 63) + offCompParams + i.val by omega]
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
  have hc_wp1_mul : migFactor * (memoryCost
      (writeEpochParamsGenProg ((base, base + 63), (N_new, (n, n)))) ⟨x.mem, x.frontier⟩ + 1) ≤
      migFactor * (22 * n + 101) :=
    Nat.mul_le_mul_left migFactor (by omega)
  have hf1 := one_le_migFactor
  have hex_params :=
    hex₁.seq_eq (hex₂.seq_eq (hex₃.seq_eq
      ((hex_wp1.mono hc_wp1_mul (fun _ h => h)).seq_eq
        (hex_nhp.seq_eq (hex_ncp.seq_eq (hex_niw.seq_eq hex_ca))))))
  have hkeep_6_to_8 : ∀ reg : Fin rResize, reg.val < 160 → reg ≠ mFr → reg ≠ mIwNew →
      reg ∉ ([mArenaWords, mCur, mArena, mPeakFront, mK, mOldItemDst] : List (Fin rResize)) →
      s₈.regs reg = s₆.regs reg := fun reg h160 hfr' hiwn hnot =>
    (hs₈_keep reg hnot).trans (hs₇_keep6 reg hfr' h160 hiwn)
  have hs₈_base : s₈.regs mBase = base :=
    (hkeep_6_to_8 mBase (mReg_lt_160 _) (mReg_ne (by decide)) (mReg_ne (by decide))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans
      ((hs₆_keep4 (c := 0) (Or.inl (by decide)) (by decide)).trans hs₄_base)
  refine ⟨s₈, _, hex_params, by nlinarith only [hn, hf1], hs₈b, hs₈f_eq, ?_,
    fun addr haddr => (congrFun hs₈m_eq addr).trans
      (hs₄_out addr (Or.inl (by unfold offScratch; omega))),
    by have hst : ({ mem := s₈.mem, frontier := s₈.frontier } : Memory.State) =
           ⟨s₄.mem, s₄.frontier⟩ :=
         Memory.State.ext hs₈m_eq (hs₈f_eq.trans hs₄f_eq.symm)
       rwa [hst],
    hs₈_base, ?_, ?_, ?_, ?_, ?_, ?_, hs₈_ar, hs₈_pf.trans hpeak_eq.symm,
    hs₈_k.trans (by dsimp only [peakF]; rw [hpeak_raw]; rfl), hs₈_oid,
    fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · refine abiPreserved_trans habi₁ ⟨hs₈_base.trans hs₁_base.symm, ?_, ?_, ?_⟩
    · exact (hkeep_6_to_8 mTag (mReg_lt_160 _) (mReg_ne (by decide)) (mReg_ne (by decide))
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans <|
        (hs₆_keep4 (c := 2) (Or.inl (by decide)) (by decide)).trans <|
        (hs₄_keep mTag (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
          (mReg_ne (by decide))).trans (by simp [s₃, s₂, RData.set])
    · exact (hkeep_6_to_8 mArgU (mReg_lt_160 _) (mReg_ne (by decide)) (mReg_ne (by decide))
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans <|
        (hs₆_keep4 (c := 3) (Or.inl (by decide)) (by decide)).trans <|
        (hs₄_keep mArgU (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
          (mReg_ne (by decide))).trans (by simp [s₃, s₂, RData.set])
    · exact (hkeep_6_to_8 mArgV (mReg_lt_160 _) (mReg_ne (by decide)) (mReg_ne (by decide))
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans <|
        (hs₆_keep4 (c := 4) (Or.inl (by decide)) (by decide)).trans <|
        (hs₄_keep mArgV (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
          (mReg_ne (by decide))).trans (by simp [s₃, s₂, RData.set])
  · exact (hkeep_6_to_8 mCnt (mReg_lt_160 _) (mReg_ne (by decide)) (mReg_ne (by decide))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₆_cnt
  · exact (hkeep_6_to_8 mNNew (mReg_lt_160 _) (mReg_ne (by decide)) (mReg_ne (by decide))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans <|
      (hs₆_keep4 (c := 149) (Or.inr (by decide)) (by decide)).trans <|
      (hs₄_keep mNNew (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
        (mReg_ne (by decide))).trans (by simp [s₃, s₂, RData.set, hs₁_nn, N_new])
  · exact (hs₈_keep mNewMeta
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₇_nm
  · exact (hs₈_keep mOffNew
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₇_off
  · exact (hs₈_keep mIwOld
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₇_iwo
  · exact (hs₈_keep mIwNew
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₇_iwn
  · rw [hkeep_6_to_8 (mOldHp i) (mOldHp_lt_160 i) (mOldHp_ne_mReg i (Or.inl (by decide)))
      (mOldHp_ne_mReg i (Or.inr (by decide))) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨mOldHp_ne_mReg i (Or.inr (by decide)), mOldHp_ne_mReg i (Or.inl (by decide)),
          mOldHp_ne_mReg i (Or.inr (by decide)), mOldHp_ne_mReg i (Or.inr (by decide)),
          mOldHp_ne_mReg i (Or.inl (by decide)), mOldHp_ne_mReg i (Or.inr (by decide))⟩),
      hs₆_r (mOldHp i) (mOldHp_ne_mReg i (Or.inl (by decide)))
        (fun j h => by have hv := congrArg Fin.val h; simp at hv; omega),
      hs₅_r (mOldHp i) (mOldHp_ne_mReg i (Or.inl (by decide)))
        (fun j h => by have hv := congrArg Fin.val h; simp at hv; omega),
      hs₄_keep (mOldHp i) (mOldHp_ne_mReg i (Or.inl (by decide))) (mOldHp_lt_160 i)
        (mOldHp_ne_mReg i (Or.inr (by decide))) (mOldHp_ne_mReg i (Or.inr (by decide)))]
    dsimp only [s₃, s₂, RData.set]
    rw [Function.update_of_ne (mOldHp_ne_mReg i (c := 156) (Or.inr (by decide))),
      Function.update_of_ne (mOldHp_ne_mReg i (c := 9) (Or.inl (by decide)))]
    exact hs₁_ohp i
  · rw [hkeep_6_to_8 (mOldCp i) (mOldCp_lt_160 i) (mOldCp_ne_mReg i (Or.inl (by decide)))
      (mOldCp_ne_mReg i (Or.inr (by decide))) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨mOldCp_ne_mReg i (Or.inr (by decide)), mOldCp_ne_mReg i (Or.inl (by decide)),
          mOldCp_ne_mReg i (Or.inr (by decide)), mOldCp_ne_mReg i (Or.inr (by decide)),
          mOldCp_ne_mReg i (Or.inl (by decide)), mOldCp_ne_mReg i (Or.inr (by decide))⟩),
      hs₆_r (mOldCp i) (mOldCp_ne_mReg i (Or.inl (by decide)))
        (fun j h => by have hv := congrArg Fin.val h; simp at hv; omega),
      hs₅_r (mOldCp i) (mOldCp_ne_mReg i (Or.inl (by decide)))
        (fun j h => by have hv := congrArg Fin.val h; simp at hv; omega),
      hs₄_keep (mOldCp i) (mOldCp_ne_mReg i (Or.inl (by decide))) (mOldCp_lt_160 i)
        (mOldCp_ne_mReg i (Or.inr (by decide))) (mOldCp_ne_mReg i (Or.inr (by decide)))]
    dsimp only [s₃, s₂, RData.set]
    rw [Function.update_of_ne (mOldCp_ne_mReg i (c := 156) (Or.inr (by decide))),
      Function.update_of_ne (mOldCp_ne_mReg i (c := 9) (Or.inl (by decide)))]
    exact hs₁_ocp i
  · exact (hkeep_6_to_8 (mNewHp i) (mNewHp_lt_160 i) (mNewHp_ne_mReg i (Or.inl (by decide)))
      (mNewHp_ne_mReg i (Or.inr (by decide))) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨mNewHp_ne_mReg i (Or.inr (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
          mNewHp_ne_mReg i (Or.inr (by decide)), mNewHp_ne_mReg i (Or.inr (by decide)),
          mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inr (by decide))⟩)).trans
      (hs₆_nhp_all i)
  · exact (hkeep_6_to_8 (mNewCp i) (mNewCp_lt_160 i) (mNewCp_ne_mReg i (Or.inl (by decide)))
      (mNewCp_ne_mReg i (Or.inr (by decide))) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨mNewCp_ne_mReg i (Or.inr (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
          mNewCp_ne_mReg i (Or.inr (by decide)), mNewCp_ne_mReg i (Or.inr (by decide)),
          mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inr (by decide))⟩)).trans
      (hs₆_ncp_all i)

private theorem migrateSetupShiftCode_exec {U V w N_old n n_init base : ℕ}
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
  have h225_old : 225 ≤ offCompItems U w N_old := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
  have h225_new : 225 ≤ offNew := by
    dsimp only [offNew]
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
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
      s₉.regs reg = s₈.regs reg := fun reg hreg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
    obtain ⟨h1, h2, h3, h4, h5⟩ := hreg
    dsimp only [s₉, growZeroPost]
    rw [Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1,
      Function.update_of_ne h5, Function.update_of_ne h4]
  set s₁₀ := s₉.set mFr peakF
  have hs₉_pf : s₉.regs mPeakFront = peakF :=
    (hs₉_keep8 mPeakFront
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_pf
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
  have hs₁₀_nm : s₁₀.regs mNewMeta = newMeta :=
    (by simp [s₁₀, RData.set] : s₁₀.regs mNewMeta = s₉.regs mNewMeta).trans <|
    (hs₉_keep8 mNewMeta
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_nm
  have hs₁₀_oid : s₁₀.regs mOldItemDst = oldItemDst :=
    (by simp [s₁₀, RData.set] : s₁₀.regs mOldItemDst = s₉.regs mOldItemDst).trans <|
    (hs₉_keep8 mOldItemDst
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_oid
  have hs₁₀_iwo : s₁₀.regs mIwOld = iwOld :=
    (by simp [s₁₀, RData.set] : s₁₀.regs mIwOld = s₉.regs mIwOld).trans <|
    (hs₉_keep8 mIwOld
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_iwo
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
    Memory.State.ext rfl (by
      dsimp only [memoryState, s₁₂, RData.set, RData.toData]
      rw [Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mTmpA)]
      exact hs₁₁_fr_reg)
  have hkeep_8_to_12 : ∀ reg : Fin rResize, reg.val < 160 →
      reg ∉ ([mFr, mTmpA, mRes, mCur, mIdx, mZero, mOne] : List (Fin rResize)) →
      s₁₂.regs reg = s₈.regs reg := fun reg h160 hnot => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    obtain ⟨hfr', hta, hres, hcur, hidx, hz, ho⟩ := hnot
    calc s₁₂.regs reg
        = s₁₁.regs reg := by simp [s₁₂, RData.set, Function.update_of_ne hta]
      _ = s₁₀.regs reg := hs₁₁_keep10 reg hfr' h160
      _ = s₉.regs reg := by simp [s₁₀, RData.set, Function.update_of_ne hfr']
      _ = s₈.regs reg := hs₉_keep8 reg (by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨hres, hcur, hidx, hz, ho⟩)
  have hs₁₂_base : s₁₂.regs mBase = base :=
    (hkeep_8_to_12 mBase (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_base
  have hs₁₂_cnt : s₁₂.regs mCnt = n :=
    (hkeep_8_to_12 mCnt (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_cnt
  have hs₁₂_nn : s₁₂.regs mNNew = N_new :=
    (hkeep_8_to_12 mNNew (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_nn
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
    have hsp_le : 225 + ReducedKWise.space w (qBits U N_old) (hashB N_old) (totalMicroBits N_old) 3
        ≤ offCompItems U w N_old := by
      have hlm : offCompLM U w N_old ≤ offCompItems U w N_old := by
        unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
      dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits, hashB]
        at hlm ⊢
      exact hlm
    have heh : epochHdrWords = 225 := rfl
    exact ⟨ReducedKWise.tableRep_congr hsplit₈.hash_rep.1
        (fun a h1 h2 =>
          (hold_meta_eq a ⟨h1, by dsimp only [newMeta]; linarith only [h2, hsp_le, heh]⟩).symm),
      ReducedKWise.seedRep_congr (w := w) hsplit₈.hash_rep.2
        (fun a h1 h2 =>
          have hsw_le :
              ReducedKWise.seedWords (qBits U N_old) (hashB N_old) (totalMicroBits N_old) 3 ≤
                ReducedKWise.space w (qBits U N_old) (hashB N_old) (totalMicroBits N_old) 3 :=
            Nat.le_add_right _ _
          (hold_meta_eq a
            ⟨h1, by dsimp only [newMeta]; linarith only [h2, hsw_le, hsp_le, heh]⟩).symm)⟩
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
    calc y.regs reg
        = s₁₃.regs reg := by
            dsimp only [y, s₁₄, RData.set]
            rw [Function.update_of_ne hhb, Function.update_of_ne hcur]
      _ = s₁₂.regs reg := hs₁₃_keep12 reg hfr' h160 hoff hhs
      _ = s₈.regs reg :=
            hkeep_8_to_12 reg h160 (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨hfr', hta, hres, hcur, hidx, hz, ho⟩)
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
  · refine abiPreserved_trans habi₈ ⟨?_, ?_, ?_, ?_⟩
    · exact hkeep_8_to_y mBase (mReg_lt_160 _)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)
    · exact hkeep_8_to_y mTag (mReg_lt_160 _)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)
    · exact hkeep_8_to_y mArgU (mReg_lt_160 _)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)
    · exact hkeep_8_to_y mArgV (mReg_lt_160 _)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)
  · intro addr haddr
    rw [hym, hs₁₃_mem_eq,
      hframe_wp2 addr (fun h => by dsimp only [newMeta] at h; linarith only [haddr, h.1]),
      hs₁₁_mem_eq,
      hout_cr addr (fun h => by
        dsimp only [newMeta] at hnm_le_oid
        linarith only [haddr, h.1, hnm_le_oid])]
    exact hbelow₈ addr haddr
  · exact (hkeep_8_to_y mBase (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_base
  · exact (hkeep_8_to_y mCnt (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_cnt
  · simp [y, s₁₄, RData.set, hs₁₃_fr_reg]
  · simp [y, s₁₄, RData.set, hs₁₃_off]
  · exact (hkeep_8_to_y mIwNew (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_iwn
  · exact (hkeep_8_to_y mArena (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_ar
  · exact (hkeep_8_to_y mPeakFront (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_pf
  · exact (hkeep_8_to_y mOldItemDst (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hs₈_oid
  · simp [y, RData.set]
  · refine (hkeep_8_to_y (mOldHp i) (mOldHp_lt_160 i) ?_).trans (hs₈_ohp i)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨mOldHp_ne_mReg i (Or.inl (by decide)), mOldHp_ne_mReg i (Or.inr (by decide)),
      mOldHp_ne_mReg i (Or.inl (by decide)), mOldHp_ne_mReg i (Or.inl (by decide)),
      mOldHp_ne_mReg i (Or.inl (by decide)), mOldHp_ne_mReg i (Or.inl (by decide)),
      mOldHp_ne_mReg i (Or.inl (by decide)), mOldHp_ne_mReg i (Or.inr (by decide)),
      mOldHp_ne_mReg i (Or.inr (by decide)), mOldHp_ne_mReg i (Or.inl (by decide))⟩
  · refine (hkeep_8_to_y (mOldCp i) (mOldCp_lt_160 i) ?_).trans (hs₈_ocp i)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨mOldCp_ne_mReg i (Or.inl (by decide)), mOldCp_ne_mReg i (Or.inr (by decide)),
      mOldCp_ne_mReg i (Or.inl (by decide)), mOldCp_ne_mReg i (Or.inl (by decide)),
      mOldCp_ne_mReg i (Or.inl (by decide)), mOldCp_ne_mReg i (Or.inl (by decide)),
      mOldCp_ne_mReg i (Or.inl (by decide)), mOldCp_ne_mReg i (Or.inr (by decide)),
      mOldCp_ne_mReg i (Or.inr (by decide)), mOldCp_ne_mReg i (Or.inl (by decide))⟩
  · refine (hkeep_8_to_y (mNewHp i) (mNewHp_lt_160 i) ?_).trans (hs₈_nhp i)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inr (by decide)),
      mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
      mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
      mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inr (by decide)),
      mNewHp_ne_mReg i (Or.inr (by decide)), mNewHp_ne_mReg i (Or.inl (by decide))⟩
  · refine (hkeep_8_to_y (mNewCp i) (mNewCp_lt_160 i) ?_).trans (hs₈_ncp i)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inr (by decide)),
      mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
      mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
      mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inr (by decide)),
      mNewCp_ne_mReg i (Or.inr (by decide)), mNewCp_ne_mReg i (Or.inl (by decide))⟩

private theorem migrateSetupCode_exec {U V w N_old n n_init base : ℕ}
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
    ∃ (y : RData rResize) (steps_setup : ℕ),
      RDemonicExec w peakF migrateSetupCode x steps_setup (· = y) ∧
      steps_setup ≤ (265 * migFactor + 12400) * n ∧
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
  obtain ⟨s₈, steps_p, hex_p, hc_p, hs₈b, hs₈f, habi₈, hbelow₈, hsplit₈,
      hs₈_base, hs₈_cnt, hs₈_nn, hs₈_nm, hs₈_off, hs₈_iwo, hs₈_iwn, hs₈_ar, hs₈_pf, hs₈_k, hs₈_oid,
      hs₈_ohp, hs₈_ocp, hs₈_nhp, hs₈_ncp⟩ :=
    migrateSetupParamsCode_exec hx hn hev hfr hfit_peak hsplit hbase
  obtain ⟨y, steps_s, hex_s, hc_s, hrest⟩ :=
    migrateSetupShiftCode_exec hn hev hfr hfit_peak hs₈b hs₈f habi₈ hbelow₈ hsplit₈
      hs₈_base hs₈_cnt hs₈_nn hs₈_nm hs₈_off hs₈_iwo hs₈_iwn hs₈_ar hs₈_pf hs₈_k hs₈_oid
      hs₈_ohp hs₈_ocp hs₈_nhp hs₈_ncp
  refine ⟨y, steps_p + steps_s, hex_p.seq_eq hex_s, ?_, hrest⟩
  have hf1 := one_le_migFactor
  nlinarith only [hc_p, hc_s, hn, hf1]

private theorem migrateCompactBackCode_exec {U V w N_old N_new n base : ℕ}
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
  have h225_old : 225 ≤ offCompItems U w N_old := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
  have h225_new : 225 ≤ offNew := by
    dsimp only [offNew]
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
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
    ⟨hz_abi_of mBase (by decide) (mReg_ne (by decide)),
     hz_abi_of mTag (by decide) (mReg_ne (by decide)),
     hz_abi_of mArgU (by decide) (mReg_ne (by decide)),
     hz_abi_of mArgV (by decide) (mReg_ne (by decide))⟩,
    fun addr haddr => by
      rw [hz_clear_lt addr (by dsimp only [frNew]; linarith only [haddr]),
        hz₁₃_mem_eq, hout_cl2 addr (fun h => by linarith only [haddr, h.1]),
        hz₈_mem_eq, hout_cl1 addr (fun h => by linarith only [haddr, h.1])]⟩

private theorem migrateFinishCode_exec {U V w N_old n base : ℕ}
    {θ_old : QuotHashSeed U N_old} {θ_new : QuotHashSeed U (targetCap U n)}
    {s_abs : Dictionary.State U} {x y_set y_rs : RData rResize}
    (hn : 1 ≤ n) (hev : EpochValid U n N_old)
    (hcard : (Dictionary.dom s_abs).card = n)
    (hvals : Dictionary.ValuesBounded V s_abs)
    (hfit_peak : Fits w (base + migratePeakWords U V w N_old n))
    (hy_set_b : y_set.Bounded w)
    (hy_set_fr : y_set.frontier = base + migratePeakWords U V w N_old n)
    (habi_set : abiPreserved x y_set)
    (hbelow_set : ∀ addr < base, y_set.mem addr = x.mem addr)
    (hhdr_set : RootHeaderValid U V w (targetCap U n) n n (base + offCompItems U w N_old)
      y_set.mem)
    (hpar_set : EpochParamsStored U V w (targetCap U n) (base + offCompItems U w N_old) y_set.mem)
    (hrep_old : ReducedKWise.Rep (base + epochHdrWords) w (qBits U N_old) (hashB N_old)
      (totalMicroBits N_old) 3 θ_old y_set.mem)
    (hcpl_old : ∃ s_fix_old : Memory.State,
      DictStateInv U V (ghostW w) N_old 0 θ_old s_abs s_fix_old ∧
      totalSlots N_old (compGmAt base U w N_old y_set.mem) = n ∧
      FixedCoupled base
        ((base + offCompItems U w N_old + offCompItems U w (targetCap U n)) +
          (migrateArenaWords U V w N_old (targetCap U n) n - compactedItemWords U V w N_old n))
        U V w N_old s_fix_old ⟨y_set.mem, y_set.frontier⟩)
    (hr_base : y_set.regs mBase = base)
    (hr_cnt : y_set.regs mCnt = n)
    (hr_fr : y_set.regs mFr = base + migratePeakWords U V w N_old n)
    (hr_nm : y_set.regs mNewMeta = base + offCompItems U w N_old)
    (hr_off : y_set.regs mOffNew = offCompItems U w (targetCap U n))
    (hr_iwn : y_set.regs mIwNew = compactedItemWords U V w (targetCap U n) n)
    (hr_ar : y_set.regs mArena = base + offCompItems U w N_old + offCompItems U w (targetCap U n))
    (hr_pf : y_set.regs mPeakFront = base + migratePeakWords U V w N_old n)
    (hr_oid : y_set.regs mOldItemDst =
      (base + offCompItems U w N_old + offCompItems U w (targetCap U n)) +
        (migrateArenaWords U V w N_old (targetCap U n) n - compactedItemWords U V w N_old n))
    (hr_ohp : ∀ i : Fin 19, y_set.regs (mOldHp i) =
      mkHashParams w (epochQBits U N_old) (epochHashB N_old) (totalMicroBits N_old) 3 i)
    (hr_ocp : ∀ i : Fin 36, y_set.regs (mOldCp i) = mkCompParams U V w N_old i)
    (hr_nhp : ∀ i : Fin 19, y_set.regs (mNewHp i) =
      mkHashParams w (epochQBits U (targetCap U n)) (epochHashB (targetCap U n))
        (totalMicroBits (targetCap U n)) 3 i)
    (hr_ncp : ∀ i : Fin 36, y_set.regs (mNewCp i) = mkCompParams U V w (targetCap U n) i)
    (hrs_fr : y_rs.frontier = y_set.frontier)
    (hrs_seed : ReducedKWise.SeedRep (base + offCompItems U w N_old + epochHdrWords)
      (qBits U (targetCap U n)) (hashB (targetCap U n)) (totalMicroBits (targetCap U n)) 3
      θ_new y_rs.mem)
    (hrs_mem : ∀ a,
      (a < base + offCompItems U w N_old + epochHdrWords ∨
        base + offCompItems U w N_old + epochHdrWords +
          ReducedKWise.seedWords (qBits U (targetCap U n)) (hashB (targetCap U n))
            (totalMicroBits (targetCap U n)) 3 ≤ a) →
      y_rs.mem a = y_set.mem a)
    (hrs_reg : ∀ j, j ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
      y_rs.regs j = y_set.regs j) :
    let N_new := targetCap U n
    let peakF := base + migratePeakWords U V w N_old n
    ∃ (z : RData rResize) (steps_clean : ℕ),
      RDemonicExec w peakF migrateFinishCleanCode
        (((((y_rs.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0)
        steps_clean (· = z) ∧
      z.Bounded w ∧
      z.frontier = base + compactedEpochWords U V w N_new n ∧
      CompactedSplitRep base (base + offCompItems U w N_new) U V w N_new n n θ_new s_abs
        ⟨z.mem, z.frontier⟩ ∧
      abiPreserved x z ∧
      (∀ addr < base, z.mem addr = x.mem addr) ∧
      (5 + steps_clean) + inEpochPotential U w N_new base z ≤
        (93500 * migFactor + 10000) * n := by
  intro N_new peakF
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hy_set_b hhdr_set
  have hNU_old : N_old ≤ U := by rcases hev with ⟨rfl, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  have hn_old : n ≤ N_old := by rcases hev with ⟨rfl, _⟩ | ⟨_, hnN, _, _⟩ <;> omega
  have hnU : n ≤ U := hn_old.trans hNU_old
  obtain ⟨hN_new_pos, hn_new, hN_new_2n, hNU_new⟩ := targetCap_bounds_of_pos hn hnU
  set newMeta := base + offCompItems U w N_old
  set offNew := offCompItems U w N_new
  set iwOld := compactedItemWords U V w N_old n
  set iwNew := compactedItemWords U V w N_new n
  set arenaW := migrateArenaWords U V w N_old N_new n
  set arenaB := newMeta + offNew
  set oldItemDst := arenaB + (arenaW - iwOld)
  have hpeak_raw : base + migratePeakWords U V w N_old n = arenaB + arenaW := by
    unfold migratePeakWords
    dsimp only [arenaB, arenaW, newMeta, offNew, N_new, iwOld, iwNew]
    ring
  have hpeak_eq : peakF = arenaB + arenaW := hpeak_raw
  have hfit_ar : Fits w (arenaB + arenaW) := hpeak_raw ▸ hfit_peak
  have hfit_nm : Fits w (newMeta + offNew) := hfit_ar.of_le (Nat.le_add_right _ _)
  have h225_fit : Fits w 225 := fits_const_of_offCompItems hfit_nm le_rfl
  have hw2 : 2 ≤ w := by
    by_contra hlt2; have hw1 : w ≤ 1 := by omega
    have hpow := Nat.pow_le_pow_right two_pos hw1
    change 225 < 2 ^ w at h225_fit; linarith only [hpow, h225_fit]
  have hlm_le_new : offCompLM U w N_new ≤ offNew := by
    dsimp only [offNew]; unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
  have hsp_le_new : 225 + ReducedKWise.space w (qBits U N_new) (hashB N_new)
      (totalMicroBits N_new) 3 ≤ offNew := by
    dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits, hashB]
      at hlm_le_new ⊢
    exact hlm_le_new
  have hsw_le_sp : ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 ≤
      ReducedKWise.space w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 :=
    Nat.le_add_right _ _
  have hfit_h_new : Fits w ((newMeta + 225) +
      ReducedKWise.space w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3) :=
    hfit_nm.of_le (by linarith only [hsp_le_new])
  have hc_lt_new : 2 * reducedChunkBits
      (reducedTrinomialStep (qBits U N_new) (hashB N_new) (totalMicroBits N_new)) < w :=
    ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space
      (two_mul_reducedChunkBits_hash_le hw2 hNU_new hU.le) hfit_h_new
  obtain ⟨z₀, hz₀_def, _hex_zr, hz₀b, hz₀m, hz₀f_set, hz₀_reg⟩ :=
    zeroResampleRegsCode_exec hy_set_b hrs_fr hy_set_fr.le
      (qBits_le_of_le_pow hw hU.le) hc_lt_new
      (by
        rw [hy_set_fr, hpeak_raw]; dsimp only [arenaB]; unfold epochHdrWords
        linarith only [hsw_le_sp, hsp_le_new])
      hrs_seed hrs_mem hrs_reg
  have hz₀f : z₀.frontier = peakF := hz₀f_set.trans hy_set_fr
  set z₁ := z₀.set mTmpA newMeta
  have hz₀_nm : z₀.regs mNewMeta = newMeta :=
    (hz₀_reg mNewMeta
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_nm
  have hex_c1 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := peakF)
    (d := mTmpA) (s := mNewMeta) (x := z₀) hz₀f.le
  rw [hz₀_nm] at hex_c1
  have hz₁b : z₁.Bounded w := hz₀b.set (hfit_nm.of_le (Nat.le_add_right _ _))
  have hz₀_fr_reg : z₀.regs mFr = peakF :=
    (hz₀_reg mFr
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_fr
  have hms₁ : memoryState mFr z₁.toData = ⟨y_rs.mem, peakF⟩ :=
    Memory.State.ext hz₀m (by
      dsimp only [memoryState, z₁, RData.set, RData.toData]
      rw [Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mTmpA)]
      exact hz₀_fr_reg)
  have hz₁_nhp : ∀ i : Fin 19, z₁.regs (mNewHp i) =
      mkHashParams w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 i := fun i => by
    dsimp only [z₁, RData.set]
    rw [Function.update_of_ne (mNewHp_ne_mReg i (c := 156) (Or.inr (by decide))),
      hz₀_reg (mNewHp i) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
          mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
          mNewHp_ne_mReg i (Or.inl (by decide))⟩)]
    exact hr_nhp i
  have hz₁_ncp : ∀ i : Fin 36, z₁.regs (mNewCp i) = mkCompParams U V w N_new i := fun i => by
    dsimp only [z₁, RData.set]
    rw [Function.update_of_ne (mNewCp_ne_mReg i (c := 156) (Or.inr (by decide))),
      hz₀_reg (mNewCp i) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
          mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
          mNewCp_ne_mReg i (Or.inl (by decide))⟩)]
    exact hr_ncp i
  have hin_im : z₁.regs ∘ srcInitNewMeta =
      WordEncoding.encode ((mkHashParams w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3,
        mkCompParams U V w N_new), newMeta) :=
    (regs_pairSrc (regs_pairSrc (regs_hp_eq hz₁_nhp) (regs_cp_eq hz₁_ncp))
      (regs_reg1_eq mTmpA (by simp [z₁, RData.set]))).eq
  obtain ⟨hpre_im, hv_im, hc_im, hfr_im, hrep_new_im, _, hpot_im, h_empty_im, hframe_im⟩ :=
    initNewEpochMetaProg_spec (w := w) (U := U) (V := V) (N := N_new) (newMetaBase := newMeta)
      (arenaBase := arenaB) (θ_new := θ_new) (s₀ := ⟨y_rs.mem, peakF⟩)
      hw hN_new_pos hNU_new hhdr_set.fits_U hV
      (by change newMeta + offNew ≤ peakF; rw [hpeak_eq]; exact Nat.le_add_right _ _)
      hfit_nm hrs_seed
  obtain ⟨z₂, hex_im, hz₂b, hz₂f, hm_im, _, hframe_reg_im⟩ :=
    execWitness wInitNewMeta factor_wInitNewMeta_le mFr srcInitNewMeta tmpInitNewMeta
      tmpInitNewMeta_inj srcInitNewMeta_ne_tmp tmpInitNewMeta_ne_mFr srcInitNewMeta_ne_mFr
      ((mkHashParams w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3,
        mkCompParams U V w N_new), newMeta) hz₁b hz₀f.le
      hin_im (hms₁ ▸ hpre_im) (hms₁ ▸ hv_im)
      (by rw [hms₁, hfr_im]; exact hz₀f.symm.le)
  rw [hms₁] at hm_im hex_im
  have hz₂f_eq : z₂.frontier = peakF := hz₂f.trans hz₀f
  have hz₂_fr_reg : z₂.regs mFr = peakF := (congrArg Memory.State.frontier hm_im).trans hfr_im
  have hz₂_mem_eq : z₂.mem = ((Memory.spec 0).clientState ⟨y_rs.mem, peakF⟩
      (initNewEpochMetaProg ((mkHashParams w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3,
        mkCompParams U V w N_new), newMeta))).mem :=
    congrArg Memory.State.mem hm_im
  have hz₂_keep1 : ∀ reg, reg ≠ mFr → reg.val < 160 → z₂.regs reg = z₁.regs reg :=
    fun reg h1 h160 => hframe_reg_im reg h1 (mkTmp_ne_reg _ h160 (fun a => Fin.elim0 a))
  set z₃ := z₂.set mZero 0
  have hex_z3 := RDemonicExec.const (B := .exact) (d := mZero) (v := 0) (x := z₂) hz₂f_eq.le
    (fits_zero w)
  have hz₃b : z₃.Bounded w := hz₂b.set (fits_zero w)
  have hms₃ : memoryState mFr z₃.toData = ⟨z₂.mem, peakF⟩ :=
    Memory.State.ext rfl (by
      dsimp only [memoryState, z₃, RData.set, RData.toData]
      rw [Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mZero)]
      exact hz₂_fr_reg)
  have hkeep_set_to_3 : ∀ reg : Fin rResize, reg.val < 160 →
      reg ∉ ([mFr, mTmpA, mZero, mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
      z₃.regs reg = y_set.regs reg := fun reg h160 hnot => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    obtain ⟨hfr', hta, hz, hcur, hidx, hk, ho, hres⟩ := hnot
    calc z₃.regs reg
        = z₂.regs reg := by dsimp only [z₃, RData.set]; rw [Function.update_of_ne hz]
      _ = z₁.regs reg := hz₂_keep1 reg hfr' h160
      _ = z₀.regs reg := by dsimp only [z₁, RData.set]; rw [Function.update_of_ne hta]
      _ = y_set.regs reg := hz₀_reg reg (by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨hcur, hidx, hk, ho, hres⟩)
  let d_sa := (((((mkHashParams w (qBits U N_old) (hashB N_old) (totalMicroBits N_old) 3,
      mkCompParams U V w N_old), (base, oldItemDst)),
    ((mkHashParams w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3,
      mkCompParams U V w N_new), (newMeta, arenaB))), 0), n)
  have hin_sa : z₃.regs ∘ srcStreamAll = WordEncoding.encode d_sa := by
    refine (regs_pairSrc
      (regs_pairSrc
        (regs_pairSrc
          (regs_pairSrc
            (regs_pairSrc (regs_hp_eq fun i => ?_) (regs_cp_eq fun i => ?_))
            (regs_pairSrc (regs_reg1_eq mBase ?_) (regs_reg1_eq mOldItemDst ?_)))
          (regs_pairSrc
            (regs_pairSrc (regs_hp_eq fun i => ?_) (regs_cp_eq fun i => ?_))
            (regs_pairSrc (regs_reg1_eq mNewMeta ?_) (regs_reg1_eq mArena ?_))))
        (regs_reg1_eq mZero (by simp [z₃, RData.set])))
      (regs_reg1_eq mCnt ?_)).eq
    · refine (hkeep_set_to_3 (mOldHp i) (mOldHp_lt_160 i) ?_).trans (hr_ohp i)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨mOldHp_ne_mReg i (Or.inl (by decide)), mOldHp_ne_mReg i (Or.inr (by decide)),
        mOldHp_ne_mReg i (Or.inl (by decide)), mOldHp_ne_mReg i (Or.inl (by decide)),
        mOldHp_ne_mReg i (Or.inl (by decide)), mOldHp_ne_mReg i (Or.inl (by decide)),
        mOldHp_ne_mReg i (Or.inl (by decide)), mOldHp_ne_mReg i (Or.inl (by decide))⟩
    · refine (hkeep_set_to_3 (mOldCp i) (mOldCp_lt_160 i) ?_).trans (hr_ocp i)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨mOldCp_ne_mReg i (Or.inl (by decide)), mOldCp_ne_mReg i (Or.inr (by decide)),
        mOldCp_ne_mReg i (Or.inl (by decide)), mOldCp_ne_mReg i (Or.inl (by decide)),
        mOldCp_ne_mReg i (Or.inl (by decide)), mOldCp_ne_mReg i (Or.inl (by decide)),
        mOldCp_ne_mReg i (Or.inl (by decide)), mOldCp_ne_mReg i (Or.inl (by decide))⟩
    · exact (hkeep_set_to_3 mBase (mReg_lt_160 _)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_base
    · exact (hkeep_set_to_3 mOldItemDst (mReg_lt_160 _)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_oid
    · refine (hkeep_set_to_3 (mNewHp i) (mNewHp_lt_160 i) ?_).trans (hr_nhp i)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inr (by decide)),
        mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
        mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
        mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide))⟩
    · refine (hkeep_set_to_3 (mNewCp i) (mNewCp_lt_160 i) ?_).trans (hr_ncp i)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inr (by decide)),
        mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
        mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
        mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide))⟩
    · exact (hkeep_set_to_3 mNewMeta (mReg_lt_160 _)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_nm
    · exact (hkeep_set_to_3 mArena (mReg_lt_160 _)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_ar
    · exact (hkeep_set_to_3 mCnt (mReg_lt_160 _)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_cnt
  have heh_val : epochHdrWords = 225 := rfl
  have hz₂_not_im : ∀ a, ¬(newMeta + epochHdrWords ≤ a ∧ a < newMeta + offNew) →
      z₂.mem a = y_set.mem a := fun a ha => by
    rw [hz₂_mem_eq, hframe_im a ha]
    have hsw_le_off : 225 + ReducedKWise.seedWords (qBits U (targetCap U n))
        (hashB (targetCap U n)) (totalMicroBits (targetCap U n)) 3 ≤ offNew := by
      change 225 + ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 ≤
        offNew
      linarith only [hsw_le_sp, hsp_le_new]
    rcases not_and_or.mp ha with hlt | hge
    · exact hrs_mem a (Or.inl (not_le.mp hlt))
    · refine hrs_mem a (Or.inr ?_)
      have hge' : newMeta + offNew ≤ a := not_lt.mp hge
      linarith only [hge', hsw_le_off, heh_val]
  obtain ⟨s_fix_old, hinv_old, htot_old, hcpl_old_set⟩ := hcpl_old
  have hsp_le_old : 225 + ReducedKWise.space w (qBits U N_old) (hashB N_old)
      (totalMicroBits N_old) 3 ≤ offCompItems U w N_old := by
    have hlm : offCompLM U w N_old ≤ offCompItems U w N_old := by
      unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
    dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits, hashB]
      at hlm ⊢
    exact hlm
  have hrep_old_z₂ : ReducedKWise.Rep (base + epochHdrWords) w (qBits U N_old) (hashB N_old)
      (totalMicroBits N_old) 3 θ_old z₂.mem :=
    ⟨ReducedKWise.tableRep_congr hrep_old.1
      (fun a _ h2 => (hz₂_not_im a (fun h => by
        dsimp only [newMeta] at h; linarith only [h.1, h2, hsp_le_old, heh_val])).symm),
     ReducedKWise.seedRep_congr (w := w) hrep_old.2
      (fun a _ h2 =>
        have hsw_old :
            ReducedKWise.seedWords (qBits U N_old) (hashB N_old) (totalMicroBits N_old) 3 ≤
              ReducedKWise.space w (qBits U N_old) (hashB N_old) (totalMicroBits N_old) 3 :=
          Nat.le_add_right _ _
        (hz₂_not_im a (fun h => by
          dsimp only [newMeta] at h; linarith only [h.1, h2, hsw_old, hsp_le_old, heh_val])).symm)⟩
  obtain ⟨hcpl_old_z₂, hgm_old_z₂⟩ := fixedCoupled_of_shift (s₀ := ⟨y_set.mem, y_set.frontier⟩)
    (s₁ := ⟨z₂.mem, peakF⟩) (dstItemBase := oldItemDst) hw hcpl_old_set htot_old
    (fun a ha => hz₂_not_im a (fun h => by dsimp only [newMeta] at h; linarith only [ha.2, h.1]))
    (fun j _ => hz₂_not_im (oldItemDst + j) (fun h => by
      dsimp only [oldItemDst, arenaB] at h; linarith only [h.2]))
  have henv_sa : StreamRebuildEnv U V w N_old N_new n base newMeta arenaB θ_old θ_new s_abs
      ⟨z₂.mem, peakF⟩ :=
    ⟨hw, hn, hn_old, hNU_old, hn_new, hNU_new, hhdr_set.fits_U, hV, hvals,
      le_rfl, le_rfl, by change arenaB + arenaW ≤ peakF; rw [hpeak_eq], hfit_nm,
      hrep_old_z₂,
      ⟨s_fix_old, hinv_old, (congrArg (totalSlots N_old) hgm_old_z₂).trans htot_old, hcpl_old_z₂⟩,
      hz₂_mem_eq ▸ hrep_new_im,
      hz₂_mem_eq ▸ hpot_im,
      by obtain ⟨s_fix₀, hi₀, hc₀⟩ := h_empty_im
         exact ⟨s_fix₀, hi₀, by
           have hs_eq : ({ mem := z₂.mem, frontier := peakF } : Memory.State) =
               (Memory.spec 0).clientState ⟨y_rs.mem, peakF⟩
                 (initNewEpochMetaProg
                   ((mkHashParams w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3,
                     mkCompParams U V w N_new), newMeta)) :=
             Memory.State.ext hz₂_mem_eq hfr_im.symm
           rwa [hs_eq]⟩⟩
  obtain ⟨hpre_sa, hvp_sa, hc_sa, hfr_sa, hrep_sa, _, hcpl_sa, hlo_sa, hmid_sa⟩ :=
    streamAllItemsProg_spec henv_sa
  have hv_sa : (Memory.spec w).ValidHistory (memoryState mFr z₃.toData)
      ((Memory.spec w).clientHistory (memoryState mFr z₃.toData) (streamAllItemsProg d_sa)) := by
    have hwf₃ : Memory.WellFormed w (memoryState mFr z₃.toData) := wellFormed_memoryState hz₃b.1
    rw [hms₃] at hwf₃ ⊢
    exact hvp_sa ⟨hwf₃, Nat.zero_le _⟩
  obtain ⟨z₄, hex_sa, hz₄b, hz₄f, hm_sa, _, hframe_reg_sa⟩ :=
    execWitness wStreamAll factor_wStreamAll_le mFr srcStreamAll tmpStreamAll
      tmpStreamAll_inj srcStreamAll_ne_tmp tmpStreamAll_ne_mFr srcStreamAll_ne_mFr
      d_sa hz₃b hz₂f_eq.le hin_sa (hms₃ ▸ hpre_sa) hv_sa
      (by rw [hms₃, hfr_sa]; exact hz₂f_eq.symm.le)
  rw [hms₃] at hm_sa hex_sa
  have hz₄f_eq : z₄.frontier = peakF := hz₄f.trans hz₂f_eq
  have hz₄_fr_reg : z₄.regs mFr = peakF := (congrArg Memory.State.frontier hm_sa).trans hfr_sa
  have hz₄_mem_eq : z₄.mem = ((Memory.spec 0).clientState ⟨z₂.mem, peakF⟩
      (streamAllItemsProg d_sa)).mem :=
    congrArg Memory.State.mem hm_sa
  have hz₄_keep3 : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mCur → z₄.regs reg = z₃.regs reg :=
    fun reg h1 h160 hcur => hframe_reg_sa reg h1
      (mkTmp_ne_reg _ h160 (fun a => by fin_cases a; exact hcur.symm))
  have hz₄_nm : z₄.regs mNewMeta = newMeta :=
    (hz₄_keep3 mNewMeta (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
    (hkeep_set_to_3 mNewMeta (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_nm
  have hz₄_base : z₄.regs mBase = base :=
    (hz₄_keep3 mBase (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
    (hkeep_set_to_3 mBase (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_base
  have hz₄_off : z₄.regs mOffNew = offNew :=
    (hz₄_keep3 mOffNew (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
    (hkeep_set_to_3 mOffNew (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_off
  have hz₄_ar : z₄.regs mArena = arenaB :=
    (hz₄_keep3 mArena (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
    (hkeep_set_to_3 mArena (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_ar
  have hz₄_iwn : z₄.regs mIwNew = iwNew :=
    (hz₄_keep3 mIwNew (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
    (hkeep_set_to_3 mIwNew (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_iwn
  have hz₄_pf : z₄.regs mPeakFront = peakF :=
    (hz₄_keep3 mPeakFront (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
    (hkeep_set_to_3 mPeakFront (mReg_lt_160 _)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_pf
  have hlow_z₄ : ∀ a, newMeta ≤ a ∧ a < newMeta + 63 → z₄.mem a = y_set.mem a := fun a ha => by
    rw [hz₄_mem_eq, hmid_sa a ha]
    exact hz₂_not_im a (fun h => by linarith only [ha.2, h.1, heh_val])
  have hhdr_z₄ : RootHeaderValid U V w N_new n n newMeta z₄.mem :=
    rootHeaderValid_congr hhdr_set fun a ha => hlow_z₄ a ⟨ha.1, by linarith only [ha.2]⟩
  have hpar_z₄ : EpochParamsStored U V w N_new newMeta z₄.mem :=
    epochParamsStored_congr hpar_set hlow_z₄
  have hs_z₄_eq : ({ mem := z₄.mem, frontier := peakF } : Memory.State) =
      (Memory.spec 0).clientState ⟨z₂.mem, peakF⟩ (streamAllItemsProg d_sa) :=
    Memory.State.ext hz₄_mem_eq hfr_sa.symm
  obtain ⟨z, steps_back, hex_back, hc_back, hzb, hzf, hsplit_z, hgm_z, habi_4z, hbelow_4z⟩ :=
    migrateCompactBackCode_exec hw hn hev hNU_new hN_new_2n hcard hvals hfit_peak hpeak_raw
      hz₄b hz₄f_eq hz₄_fr_reg hz₄_nm hz₄_base hz₄_off hz₄_ar hz₄_iwn hz₄_pf
      hhdr_z₄ hpar_z₄ (hz₄_mem_eq ▸ hrep_sa)
      (by obtain ⟨s_fix', hi', hc'⟩ := hcpl_sa; exact ⟨s_fix', hi', hs_z₄_eq ▸ hc'⟩)
  have habi_set_4 : abiPreserved y_set z₄ :=
    ⟨(hz₄_keep3 mBase (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
        (hkeep_set_to_3 mBase (mReg_lt_160 _)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)),
     (hz₄_keep3 mTag (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
        (hkeep_set_to_3 mTag (mReg_lt_160 _)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)),
     (hz₄_keep3 mArgU (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
        (hkeep_set_to_3 mArgU (mReg_lt_160 _)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)),
     (hz₄_keep3 mArgV (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans
        (hkeep_set_to_3 mArgV (mReg_lt_160 _)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide))⟩
  have hf1 := one_le_migFactor
  have hc_im_mul : migFactor * (memoryCost
      (initNewEpochMetaProg ((mkHashParams w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3,
        mkCompParams U V w N_new), newMeta)) ⟨y_rs.mem, peakF⟩ + 1) ≤
      migFactor * (512 * n + 476) :=
    Nat.mul_le_mul_left migFactor (by dsimp only [N_new] at hc_im; linarith only [hc_im, hN_new_2n])
  have hpot_le : inEpochPotential U w N_new base z ≤
      (98 * migFactor) * slotPotential N_new (compGmAt newMeta U w N_new z₄.mem) := by
    unfold inEpochPotential
    rw [hgm_z]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 98 inEpochFactor_le_migFactor)
  have hsa_pot : migFactor * (memoryCost (streamAllItemsProg d_sa) ⟨z₂.mem, peakF⟩ + 1) +
      inEpochPotential U w N_new base z ≤ (90540 * migFactor) * n + migFactor := by
    have hmul := Nat.mul_le_mul_left migFactor hc_sa
    rw [← hz₄_mem_eq] at hmul
    linarith only [hmul, hpot_le]
  have hex_build : RDemonicExec w peakF migrateStreamBuildCode z₀ _ (· = z₄) :=
    hex_c1.seq_eq ((hex_im.mono hc_im_mul (fun _ h => h)).seq_eq (hex_z3.seq_eq hex_sa))
  have hex_clean := hex_build.seq_eq hex_back
  rw [hz₀_def] at hex_clean
  refine ⟨z, _, hex_clean, hzb, hzf, hsplit_z,
    abiPreserved_trans habi_set (abiPreserved_trans habi_set_4 habi_4z),
    fun addr haddr => ?_, ?_⟩
  · exact (hbelow_4z addr haddr).trans <|
      (congrFun hz₄_mem_eq addr).trans <|
      (hlo_sa addr (by linarith only [haddr])).trans <|
      (hz₂_not_im addr (fun h => by dsimp only [newMeta] at h; linarith only [haddr, h.1])).trans <|
      hbelow_set addr haddr
  · nlinarith only [hsa_pot, hc_back, hn, hf1]

private theorem exec_setup_resample_finish
    {U w N_new metaBase base peakF steps_set finBound : ℕ}
    {setupCode finishCleanCode : RCode .exact rResize} {x y_set : RData rResize}
    {P : QuotHashSeed U N_new → RData rResize → Prop}
    (hw : 0 < w) (hU : U < 2 ^ w) (hNU : N_new ≤ U)
    (hex_set : RDemonicExec w peakF setupCode x steps_set (· = y_set))
    (hy_set_b : y_set.Bounded w) (hy_set_fr : y_set.frontier = peakF)
    (hfit_nm : Fits w (metaBase + offCompItems U w N_new))
    (hnm_le_peak : metaBase + offCompItems U w N_new ≤ peakF)
    (hr_hb : y_set.regs mHashBase = metaBase + epochHdrWords)
    (hr_nhp : ∀ j : Fin 19, y_set.regs (mNewHp j) =
      mkHashParams w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 j)
    (hfin_spec : ∀ (θ : QuotHashSeed U N_new) (y_rs : RData rResize),
      y_rs.frontier = y_set.frontier →
      ReducedKWise.SeedRep (metaBase + epochHdrWords) (qBits U N_new) (hashB N_new)
        (totalMicroBits N_new) 3 θ y_rs.mem →
      (∀ a, a < metaBase + epochHdrWords ∨
          metaBase + epochHdrWords +
            ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 ≤ a →
          y_rs.mem a = y_set.mem a) →
      (∀ j : Fin rResize, j ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
          y_rs.regs j = y_set.regs j) →
      ∃ (z : RData rResize) (stepsClean : ℕ),
        RDemonicExec w peakF finishCleanCode
          (((((y_rs.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0)
          stepsClean (· = z) ∧
        P θ z ∧
        (5 + stepsClean) + inEpochPotential U w N_new base z ≤ finBound) :
    ∃ (zOf : QuotHashSeed U N_new → RData rResize) (T_all : ℝ≥0∞),
      ExecRCodeDist w
        (.seq setupCode <|
          .seq (resampleHashCode mHashBase (mNewHp ⟨3, by decide⟩) (mNewHp ⟨2, by decide⟩)
                 (mNewHp ⟨10, by decide⟩) mCur mIdx mK mOne mRes)
               (.seq zeroResampleRegsCode finishCleanCode))
        x ((PMF.uniformOfFintype (QuotHashSeed U N_new)).map zOf) T_all peakF ∧
      (∀ θ, P θ (zOf θ)) ∧
      T_all + (∑' θ, (PMF.uniformOfFintype (QuotHashSeed U N_new)) θ *
          (inEpochPotential U w N_new base (zOf θ) : ℝ≥0∞)) ≤
        ((steps_set + 826 + finBound : ℕ) : ℝ≥0∞) := by
  have h225_fit : Fits w 225 := fits_const_of_offCompItems hfit_nm le_rfl
  have hw2 : 2 ≤ w := by
    by_contra hlt2; have hw1 : w ≤ 1 := by omega
    have := Nat.pow_le_pow_right two_pos hw1
    change 225 < 2 ^ w at h225_fit; omega
  have hlm_le : offCompLM U w N_new ≤ offCompItems U w N_new := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
  have hsp_le : 225 + ReducedKWise.space w (qBits U N_new) (hashB N_new)
      (totalMicroBits N_new) 3 ≤ offCompItems U w N_new := by
    dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits, hashB]
      at hlm_le ⊢
    exact hlm_le
  have hsw_le_sp : ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 ≤
      ReducedKWise.space w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 :=
    Nat.le_add_right _ _
  have hfit_h : Fits w ((metaBase + epochHdrWords) +
      ReducedKWise.space w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3) :=
    hfit_nm.of_le (by unfold epochHdrWords; omega)
  have hc_lt : 2 * reducedChunkBits
      (reducedTrinomialStep (qBits U N_new) (hashB N_new) (totalMicroBits N_new)) < w :=
    ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space
      (two_mul_reducedChunkBits_hash_le hw2 hNU hU.le) hfit_h
  have hsw_le_fr : metaBase + epochHdrWords +
      ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 ≤
      y_set.frontier := by
    rw [hy_set_fr]; unfold epochHdrWords; omega
  obtain ⟨μ_rs, hex_rs, hmap_unif, hrs_supp⟩ :=
    resampleHashCode_execRCodeDist (w := w) (L_peak := peakF)
      (w₀ := qBits U N_new) (b := hashB N_new) (b' := totalMicroBits N_new) (k := 3)
      (hashBase := metaBase + epochHdrWords) (x := y_set)
      mResample_nodup (qBits_le_of_le_pow hw hU.le) hc_lt hy_set_fr.le hsw_le_fr
      (hfit_h.of_le (by omega)) hr_hb
      (by rw [hr_nhp ⟨3, by decide⟩]; rfl)
      (by rw [hr_nhp ⟨2, by decide⟩]; rfl)
      (by rw [hr_nhp ⟨10, by decide⟩]; rfl)
  let extSeed (y : RData rResize) : QuotHashSeed U N_new :=
    ReducedKWise.extractSeed (metaBase + epochHdrWords) (qBits U N_new) (hashB N_new)
      (totalMicroBits N_new) 3 y.mem
  have hcanon_z₀ : ∀ {y₁ y₂ : RData rResize}, y₁ ∈ μ_rs.support → y₂ ∈ μ_rs.support →
      extSeed y₁ = extSeed y₂ →
      (((((y₁.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0) =
      (((((y₂.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0) := by
    intro y₁ y₂ hy₁ hy₂ heq_seed
    obtain ⟨hfr₁, hseed₁, hmem₁, hreg₁⟩ := hrs_supp y₁ hy₁
    obtain ⟨hfr₂, hseed₂, hmem₂, hreg₂⟩ := hrs_supp y₂ hy₂
    change ReducedKWise.SeedRep _ _ _ _ _ (extSeed y₁) y₁.mem at hseed₁
    change ReducedKWise.SeedRep _ _ _ _ _ (extSeed y₂) y₂.mem at hseed₂
    rw [heq_seed] at hseed₁
    apply RData.ext
    · funext j
      dsimp only [RData.set]
      by_cases h1 : j = mRes
      · subst h1; rw [Function.update_self, Function.update_self]
      rw [Function.update_of_ne h1, Function.update_of_ne h1]
      by_cases h2 : j = mOne
      · subst h2; rw [Function.update_self, Function.update_self]
      rw [Function.update_of_ne h2, Function.update_of_ne h2]
      by_cases h3 : j = mK
      · subst h3; rw [Function.update_self, Function.update_self]
      rw [Function.update_of_ne h3, Function.update_of_ne h3]
      by_cases h4 : j = mIdx
      · subst h4; rw [Function.update_self, Function.update_self]
      rw [Function.update_of_ne h4, Function.update_of_ne h4]
      by_cases h5 : j = mCur
      · subst h5; rw [Function.update_self, Function.update_self]
      rw [Function.update_of_ne h5, Function.update_of_ne h5]
      have hj_not : j ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h5, h4, h3, h2, h1⟩
      rw [hreg₁ j hj_not, hreg₂ j hj_not]
    · funext a
      dsimp only [RData.set]
      by_cases ha_out :
          a < metaBase + epochHdrWords ∨
            metaBase + epochHdrWords +
              ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 ≤ a
      · exact (hmem₁ a ha_out).trans (hmem₂ a ha_out).symm
      · rw [not_or, not_lt, not_le] at ha_out
        rcases eq_or_lt_of_le ha_out.1 with rfl | ha_gt
        · exact hseed₁.1.trans hseed₂.1.symm
        · set L := reducedLimbCount
            (reducedTrinomialStep (qBits U N_new) (hashB N_new) (totalMicroBits N_new))
          have hsw : ReducedKWise.seedWords (qBits U N_new) (hashB N_new)
              (totalMicroBits N_new) 3 = 1 + 3 * L := rfl
          have hoff_lt : a - (metaBase + epochHdrWords + 1) < 3 * L := by omega
          have hL_pos : 0 < L := by omega
          let m : Fin L := ⟨(a - (metaBase + epochHdrWords + 1)) % L, Nat.mod_lt _ hL_pos⟩
          let j : Fin 3 := ⟨(a - (metaBase + epochHdrWords + 1)) / L,
            Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hoff_lt)⟩
          have haddr : metaBase + epochHdrWords + 1 + (m.val + L * j.val) = a := by
            have hmod := Nat.mod_add_div (a - (metaBase + epochHdrWords + 1)) L
            dsimp only [m, j]; omega
          rw [← haddr]
          exact (hseed₁.2 j m).trans (hseed₂.2 j m).symm
    · exact hfr₁.trans hfr₂.symm
  have hex_rep : ∀ θ : QuotHashSeed U N_new,
      ∃ y_rs ∈ μ_rs.support, extSeed y_rs = θ := fun θ => by
    have hmem_u : θ ∈ (PMF.uniformOfFintype (QuotHashSeed U N_new)).support :=
      Cslib.Probability.PMF.mem_support_uniformOfFintype θ
    rw [← hmap_unif, PMF.mem_support_map_iff] at hmem_u
    exact hmem_u
  choose yRep hyRep_supp hyRep_seed using hex_rep
  have hfin_rep := fun θ =>
    hfin_spec θ (yRep θ) (hrs_supp _ (hyRep_supp θ)).1
      (by
        have hs := (hrs_supp _ (hyRep_supp θ)).2.1
        change ReducedKWise.SeedRep _ _ _ _ _ (extSeed (yRep θ)) _ at hs
        rw [hyRep_seed θ] at hs
        exact hs)
      (hrs_supp _ (hyRep_supp θ)).2.2.1
      (hrs_supp _ (hyRep_supp θ)).2.2.2
  choose zOf stepsClean hfin_res using hfin_rep
  have hfin_any : ∀ y_rs ∈ μ_rs.support,
      ExecRCodeDist w (.seq zeroResampleRegsCode finishCleanCode) y_rs
        (PMF.pure (zOf (extSeed y_rs))) ((5 + stepsClean (extSeed y_rs) : ℕ) : ℝ≥0∞) peakF := by
    intro y_rs hy_rs
    obtain ⟨hfr_y, hseed_y, hmem_y, hreg_y⟩ := hrs_supp y_rs hy_rs
    obtain ⟨z₀, hz₀_def, hex_zr, _, _, _, _⟩ :=
      zeroResampleRegsCode_exec hy_set_b hfr_y hy_set_fr.le
        (qBits_le_of_le_pow hw hU.le) hc_lt hsw_le_fr hseed_y hmem_y hreg_y
    have hz₀_eq : z₀ =
        ((((( (yRep (extSeed y_rs)).set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0) :=
      hz₀_def.trans (hcanon_z₀ hy_rs (hyRep_supp (extSeed y_rs)) (hyRep_seed (extSeed y_rs)).symm)
    have hex_cl := hz₀_eq ▸ (hfin_res (extSeed y_rs)).1
    exact ExecRCodeDist.of_demonicExec (hex_zr.seq_eq hex_cl)
  have hex_tail := hex_rs.seq hfin_any
  have hmu_eq : μ_rs.bind (fun y_rs => PMF.pure (zOf (extSeed y_rs))) =
      (PMF.uniformOfFintype (QuotHashSeed U N_new)).map zOf := by
    have h1 : μ_rs.bind (fun y_rs => PMF.pure (zOf (extSeed y_rs))) =
        μ_rs.map (zOf ∘ extSeed) := rfl
    rw [h1, ← PMF.map_comp, hmap_unif]
  have hex_full := (ExecRCodeDist.of_demonicExec hex_set).seq_pure (hmu_eq ▸ hex_tail)
  set μ_u := PMF.uniformOfFintype (QuotHashSeed U N_new)
  have htsum_fin : (∑' y_rs, μ_rs y_rs * ((5 + stepsClean (extSeed y_rs) : ℕ) : ℝ≥0∞)) =
      ∑' θ, μ_u θ * ((5 + stepsClean θ : ℕ) : ℝ≥0∞) := by
    rw [← Cslib.Probability.PMF.tsum_map_mul μ_rs extSeed
      (fun θ => ((5 + stepsClean θ : ℕ) : ℝ≥0∞)), hmap_unif]
  have hsw_le_163 :
      ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 ≤ 163 :=
    (ReducedKWise.seedWords_le _ _ _ 3).trans (by decide)
  have hpt_bound : ∀ θ,
      ((5 + stepsClean θ : ℕ) : ℝ≥0∞) +
        (inEpochPotential U w N_new base (zOf θ) : ℝ≥0∞) ≤ (finBound : ℝ≥0∞) := fun θ => by
    rw [← Nat.cast_add]
    exact (Nat.cast_le (α := ℝ≥0∞)).mpr (hfin_res θ).2.2
  have hsum_fin_pot :
      (∑' θ, μ_u θ * ((5 + stepsClean θ : ℕ) : ℝ≥0∞)) +
        (∑' θ, μ_u θ * (inEpochPotential U w N_new base (zOf θ) : ℝ≥0∞)) ≤
        (finBound : ℝ≥0∞) := by
    rw [← CompleteLattice.summable.tsum_add CompleteLattice.summable]
    calc (∑' θ, (μ_u θ * ((5 + stepsClean θ : ℕ) : ℝ≥0∞) +
            μ_u θ * (inEpochPotential U w N_new base (zOf θ) : ℝ≥0∞)))
        = ∑' θ, μ_u θ * (((5 + stepsClean θ : ℕ) : ℝ≥0∞) +
            (inEpochPotential U w N_new base (zOf θ) : ℝ≥0∞)) :=
          tsum_congr fun _ => (mul_add _ _ _).symm
      _ ≤ ∑' θ, μ_u θ * (finBound : ℝ≥0∞) :=
          tsum_le_tsum fun θ => mul_le_mul_right (hpt_bound θ) _
      _ = (finBound : ℝ≥0∞) := by
          rw [ENNReal.tsum_mul_right, μ_u.tsum_coe, one_mul]
  refine ⟨zOf, _, hex_full, fun θ => (hfin_res θ).2.1, ?_⟩
  rw [htsum_fin, add_assoc, add_assoc]
  have hsw_b : ((5 * ReducedKWise.seedWords (qBits U N_new) (hashB N_new)
      (totalMicroBits N_new) 3 + 11 : ℕ) : ℝ≥0∞) ≤ ((826 : ℕ) : ℝ≥0∞) :=
    (Nat.cast_le (α := ℝ≥0∞)).mpr (by omega)
  calc (steps_set : ℝ≥0∞) +
        (((5 * ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 +
            11 : ℕ) : ℝ≥0∞) +
          ((∑' θ, μ_u θ * ((5 + stepsClean θ : ℕ) : ℝ≥0∞)) +
            (∑' θ, μ_u θ * (inEpochPotential U w N_new base (zOf θ) : ℝ≥0∞))))
      ≤ (steps_set : ℝ≥0∞) + (((826 : ℕ) : ℝ≥0∞) + (finBound : ℝ≥0∞)) := by gcongr
    _ = ((steps_set + 826 + finBound : ℕ) : ℝ≥0∞) := by push_cast; ring

/-- **Distributional Single-Tape `1 · OPT` Rebuild (`migrateActiveCode_execRCodeDist`):**
From any active compacted epoch `(N_old, n, n_init_old)` (`1 ≤ n`, `EpochValid U n N_old`),
`migrateActiveCode` resamples a fresh uniform `QuotHashSeed U (targetCap U n)` and streams all `n`
entries into `(targetCap U n, n, n)` at `base` without ever exceeding hardware frontier
`base + migratePeakWords U V w N_old n` (`≤ base + Dynamic.succinctWords 2699 888 U V w n`),
bounding expected instructions plus post-migration `inEpochPotential` by `migLinearFactor * n`. -/
theorem migrateActiveCode_execRCodeDist {U V w N_old n n_init base : ℕ}
    {θ_old : QuotHashSeed U N_old} {s_abs : Dictionary.State U} {x : RData rResize}
    (hx : x.Bounded w) (hn : 1 ≤ n) (hev : EpochValid U n N_old)
    (hfr : x.frontier = base + compactedEpochWords U V w N_old n)
    (hfit_peak : Fits w (base + migratePeakWords U V w N_old n))
    (hsplit : CompactedSplitRep base (base + offCompItems U w N_old) U V w N_old n n_init θ_old
      s_abs ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base) :
    let N_new := targetCap U n
    let peakF := base + migratePeakWords U V w N_old n
    ∃ (zOf : QuotHashSeed U N_new → RData rResize) (T_mig : ℝ≥0∞),
      ExecRCodeDist w migrateActiveCode x
        ((PMF.uniformOfFintype (QuotHashSeed U N_new)).map zOf) T_mig peakF ∧
      (∀ θ_new,
        (zOf θ_new).Bounded w ∧
        (zOf θ_new).frontier = base + compactedEpochWords U V w N_new n ∧
        CompactedSplitRep base (base + offCompItems U w N_new) U V w N_new n n θ_new s_abs
          ⟨(zOf θ_new).mem, (zOf θ_new).frontier⟩ ∧
        (zOf θ_new).regs mBase = base ∧
        (zOf θ_new).regs mTag = x.regs mTag ∧
        (zOf θ_new).regs mArgU = x.regs mArgU ∧
        (zOf θ_new).regs mArgV = x.regs mArgV ∧
        (∀ addr < base, (zOf θ_new).mem addr = x.mem addr)) ∧
      T_mig + (∑' θ_new, (PMF.uniformOfFintype (QuotHashSeed U N_new)) θ_new *
          (inEpochPotential U w N_new base (zOf θ_new) : ℝ≥0∞)) ≤
        ((migLinearFactor * n : ℕ) : ℝ≥0∞) := by
  intro N_new peakF
  obtain ⟨hw, hU, _⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  have hNU_old : N_old ≤ U := by rcases hev with ⟨rfl, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  have hn_old : n ≤ N_old := by rcases hev with ⟨rfl, _⟩ | ⟨_, hnN, _, _⟩ <;> omega
  have hnU : n ≤ U := hn_old.trans hNU_old
  obtain ⟨_, _, _, hNU_new⟩ := targetCap_bounds_of_pos hn hnU
  obtain ⟨y_set, steps_set, hex_set, hc_set, hy_set_b, hy_set_fr, habi_set, hbelow_set,
      hhdr_set, hpar_set, hrep_old, hcpl_old,
      hr_base, hr_cnt, hr_fr, hr_nm, hr_off, hr_iwn, hr_ar, hr_pf, hr_oid, hr_hb,
      hr_ohp, hr_ocp, hr_nhp, hr_ncp⟩ :=
    migrateSetupCode_exec hx hn hev hfr hfit_peak hsplit hbase
  set newMeta := base + offCompItems U w N_old
  have hpeak_def : peakF =
      newMeta + offCompItems U w N_new + migrateArenaWords U V w N_old N_new n := by
    dsimp only [peakF, newMeta, N_new]; unfold migratePeakWords; omega
  have hnm_le : newMeta + offCompItems U w N_new ≤ peakF := by rw [hpeak_def]; omega
  obtain ⟨zOf, T_mig, hex_full, hpost, hcost⟩ :=
    exec_setup_resample_finish (metaBase := newMeta) (base := base)
      (finBound := (93500 * migFactor + 10000) * n)
      (finishCleanCode := migrateFinishCleanCode)
      (P := fun θ_new z =>
        z.Bounded w ∧
        z.frontier = base + compactedEpochWords U V w N_new n ∧
        CompactedSplitRep base (base + offCompItems U w N_new) U V w N_new n n θ_new s_abs
          ⟨z.mem, z.frontier⟩ ∧
        z.regs mBase = base ∧
        z.regs mTag = x.regs mTag ∧
        z.regs mArgU = x.regs mArgU ∧
        z.regs mArgV = x.regs mArgV ∧
        (∀ addr < base, z.mem addr = x.mem addr))
      hw hU hNU_new hex_set hy_set_b hy_set_fr (hfit_peak.of_le hnm_le) hnm_le hr_hb hr_nhp
      (fun θ_new y_rs hfr_y hseed_y hmem_y hreg_y => by
        obtain ⟨z, stepsClean, hex_cl, hzb, hzf, hsp, habi, hbel, hbd⟩ :=
          migrateFinishCode_exec hn hev hsplit.card_eq hsplit.vals_lt hfit_peak
            hy_set_b hy_set_fr habi_set hbelow_set hhdr_set hpar_set hrep_old hcpl_old
            hr_base hr_cnt hr_fr hr_nm hr_off hr_iwn hr_ar hr_pf hr_oid hr_ohp hr_ocp hr_nhp hr_ncp
            hfr_y hseed_y hmem_y hreg_y
        exact ⟨z, stepsClean, hex_cl,
          ⟨hzb, hzf, hsp, habi.1.trans hbase, habi.2.1, habi.2.2.1, habi.2.2.2, hbel⟩, hbd⟩)
  refine ⟨zOf, T_mig, hex_full, hpost, hcost.trans ((Nat.cast_le (α := ℝ≥0∞)).mpr ?_)⟩
  have hf1 := one_le_migFactor
  unfold migLinearFactor
  nlinarith only [hc_set, hn, hf1]

/-! ## Section 5: First-Epoch Creation (`initFirstEpochCode`) and Singleton Delete
(`deleteLastOneCode`) -/

/-- Parameter-free $O(1)$ expected amortized instruction charge for `0 → 1` first-epoch creation
(`initFirstEpochCode`). -/
noncomputable def initFirstCharge : ℕ :=
  50000 * migFactor + 10000

/-- Parameter-free $O(1)$ deterministic instruction charge for `n = 1` deletion and empty-epoch
collapse (`deleteLastOneCode`). -/
noncomputable def deleteLastOneCharge : ℕ :=
  46000 * migFactor + 6500

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

private noncomputable def initFirstSetupCode : RCode .exact rResize :=
  .seq initFirstParamsCode initFirstGrowCode

private noncomputable def initFirstFinishCleanCode : RCode .exact rResize :=
  .seq (.op (.copy mTmpA mBase)) <|
  .seq (RCode.ofCode (wInitNewMeta.code mFr srcInitNewMeta tmpInitNewMeta))
       (RCode.ofCode (wStreamIns.code mFr srcStreamIns tmpStreamIns))

private noncomputable def initFirstFinishCode : RCode .exact rResize :=
  .seq zeroResampleRegsCode initFirstFinishCleanCode

/-- Empty-to-active epoch transition (`n = 0 → n' = 1`, `N₁ = targetCap U 1`) on `insert u v`:
grows `[base + 8, base + compactedEpochWords U V w N₁ 1)`, writes epoch parameters, samples a
uniform `QuotHashSeed U N₁`, initializes metadata, and inserts `(u, v)` (`¬ReadsWidth`). -/
noncomputable def initFirstEpochCode : RCode .exact rResize :=
  .seq initFirstSetupCode <|
  .seq (resampleHashCode mHashBase (mNewHp ⟨3, by decide⟩) (mNewHp ⟨2, by decide⟩)
        (mNewHp ⟨10, by decide⟩) mCur mIdx mK mOne mRes)
       initFirstFinishCode

private noncomputable def deleteLastReadCode : RCode .exact rResize :=
  .seq (loadBlockUpTo mBase mCur mOldHp offHashParams 18 (by decide)) <|
  .seq (loadBlockUpTo mBase mCur mOldCp offCompParams 35 (by decide)) <|
  .seq (.op (.const mCnt 1)) <|
  .seq (.op (.const mFr 0)) <|
  .seq (RCode.ofCode (wItemWords.code mFr srcOldIw tmpOldIw)) <|
  .seq (.op (.exactBin .add mItemBase mBase (mOldCp ⟨34, by decide⟩))) <|
  .seq (.op (.exactBin .add mFr mItemBase mIwOld)) <|
  .seq (.op (.const mZero 0))
       (RCode.ofCode (wReadOldKV.code mFr srcReadOldKV tmpReadOldKV))

private noncomputable def deleteLastHitTailCode : RCode .exact rResize :=
  .seq (.op (.const mZero 0)) <|
  .seq (storeAtOffCode mBase mZero mCur 5) <|
  .seq (storeAtOffCode mBase mZero mCur 6) <|
  .seq (storeAtOffCode mBase mZero mCur 7) <|
  .seq (.op (.const mCur 8)) <|
  .seq (.op (.exactBin .add mCur mBase mCur)) <|
  .seq (.op (.exactBin .sub mK mFr mCur))
       (shrinkCode mK mIdx mZero mOne)

/-- Singleton deletion (`n = 1 → 1` or `1 → 0`) on `delete u`: reconstructs the sole live key
`u₀` at dense slot `0`, and on `u₀ = u` zeros `(N, n, n_init)` at `base + 5..7` and shrinks back
to the 8-word empty header (`¬ReadsWidth`). -/
noncomputable def deleteLastOneCode : RCode .exact rResize :=
  .seq deleteLastReadCode
       (.branch (.eq mU0 mArgU)
         deleteLastHitTailCode
         (.op (.copy mZero mZero)))

private theorem not_readsWidth_initFirstSetupCode : ¬initFirstSetupCode.ReadsWidth := by
  have htc : ¬(RCode.ofCode (wTargetCap.code mFr srcTargetCap tmpTargetCap)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wTargetCap.code_spec mFr srcTargetCap tmpTargetCap
      tmpTargetCap_inj srcTargetCap_ne_tmp tmpTargetCap_ne_mFr srcTargetCap_ne_mFr).1
  have hwp : ¬(RCode.ofCode (wWriteParams.code mFr srcWriteParams tmpWriteParams)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wWriteParams.code_spec mFr srcWriteParams tmpWriteParams
      tmpWriteParams_inj srcWriteParams_ne_tmp tmpWriteParams_ne_mFr srcWriteParams_ne_mFr).1
  have hiw : ¬(RCode.ofCode (wItemWords.code mFr srcNewIw tmpNewIw)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wItemWords.code_spec mFr srcNewIw tmpNewIw
      tmpNewIw_inj srcNewIw_ne_tmp tmpNewIw_ne_mFr srcNewIw_ne_mFr).1
  have hb1 := not_readsWidth_loadBlockUpTo mBase mCur mNewHp offHashParams 18 (by decide)
  have hb2 := not_readsWidth_loadBlockUpTo mBase mCur mNewCp offCompParams 35 (by decide)
  simp [initFirstSetupCode, initFirstParamsCode, initFirstGrowCode,
    RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin, growZeroCode_not_readsWidth,
    htc, hwp, hiw, hb1, hb2]

private theorem not_readsWidth_initFirstFinishCode : ¬initFirstFinishCode.ReadsWidth := by
  have him : ¬(RCode.ofCode (wInitNewMeta.code mFr srcInitNewMeta tmpInitNewMeta)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wInitNewMeta.code_spec mFr srcInitNewMeta tmpInitNewMeta
      tmpInitNewMeta_inj srcInitNewMeta_ne_tmp tmpInitNewMeta_ne_mFr srcInitNewMeta_ne_mFr).1
  have hsi : ¬(RCode.ofCode (wStreamIns.code mFr srcStreamIns tmpStreamIns)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wStreamIns.code_spec mFr srcStreamIns tmpStreamIns
      tmpStreamIns_inj srcStreamIns_ne_tmp tmpStreamIns_ne_mFr srcStreamIns_ne_mFr).1
  simp [initFirstFinishCode, initFirstFinishCleanCode, RCode.ReadsWidth, Op.ReadsWidth,
    not_readsWidth_zeroResampleRegsCode, him, hsi]

/-- `initFirstEpochCode` does not inspect the ambient word width `w` (`¬ReadsWidth`). -/
theorem not_readsWidth_initFirstEpochCode : ¬initFirstEpochCode.ReadsWidth := by
  simp [initFirstEpochCode, RCode.ReadsWidth, not_readsWidth_initFirstSetupCode,
    not_readsWidth_resampleHashCode, not_readsWidth_initFirstFinishCode]

private theorem not_readsWidth_deleteLastReadCode : ¬deleteLastReadCode.ReadsWidth := by
  have hiw : ¬(RCode.ofCode (wItemWords.code mFr srcOldIw tmpOldIw)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wItemWords.code_spec mFr srcOldIw tmpOldIw
      tmpOldIw_inj srcOldIw_ne_tmp tmpOldIw_ne_mFr srcOldIw_ne_mFr).1
  have hro : ¬(RCode.ofCode (wReadOldKV.code mFr srcReadOldKV tmpReadOldKV)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wReadOldKV.code_spec mFr srcReadOldKV tmpReadOldKV
      tmpReadOldKV_inj srcReadOldKV_ne_tmp tmpReadOldKV_ne_mFr srcReadOldKV_ne_mFr).1
  have hb1 := not_readsWidth_loadBlockUpTo mBase mCur mOldHp offHashParams 18 (by decide)
  have hb2 := not_readsWidth_loadBlockUpTo mBase mCur mOldCp offCompParams 35 (by decide)
  simp [deleteLastReadCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin, hiw, hro, hb1, hb2]

/-- `deleteLastOneCode` does not inspect the ambient word width `w` (`¬ReadsWidth`). -/
theorem not_readsWidth_deleteLastOneCode : ¬deleteLastOneCode.ReadsWidth := by
  simp [deleteLastOneCode, deleteLastHitTailCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    not_readsWidth_deleteLastReadCode, not_readsWidth_storeAtOffCode,
    shrinkCode_not_readsWidth]

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
  have h225_le : 225 ≤ off₁ := by
    dsimp only [off₁]
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
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
      s₆.regs reg = s₅.regs reg := fun reg hreg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
    obtain ⟨h1, h2, h3, h4, h5⟩ := hreg
    dsimp only [s₆, growZeroPost]
    rw [Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1,
      Function.update_of_ne h5, Function.update_of_ne h4]
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
    ⟨hs₁₀_abi_of mBase (by decide) (mReg_ne (by decide)),
     hs₁₀_abi_of mTag (by decide) (mReg_ne (by decide)),
     hs₁₀_abi_of mArgU (by decide) (mReg_ne (by decide)),
     hs₁₀_abi_of mArgV (by decide) (mReg_ne (by decide))⟩,
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
  have h225_le : 225 ≤ off₁ := by
    dsimp only [off₁]
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
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
      y₄.regs reg = y₃.regs reg := fun reg hreg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
    obtain ⟨h1, h2, h3, h4, h5⟩ := hreg
    dsimp only [y₄, growZeroPost]
    rw [Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1,
      Function.update_of_ne h5, Function.update_of_ne h4]
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

private theorem initFirstFinishCode_exec {U V w base : ℕ} (u : Fin U) (v : ℕ)
    {θ : QuotHashSeed U (targetCap U 1)} {x y_set y_rs : RData rResize}
    (hv_lt : v < V)
    (hfit_peak : Fits w (base + compactedEpochWords U V w (targetCap U 1) 1))
    (hy_set_b : y_set.Bounded w)
    (hy_set_fr : y_set.frontier = base + compactedEpochWords U V w (targetCap U 1) 1)
    (habi_set : abiPreserved x y_set)
    (hbelow_set : ∀ addr < base, y_set.mem addr = x.mem addr)
    (hhdr_set : RootHeaderValid U V w (targetCap U 1) 1 1 base y_set.mem)
    (hpar_set : EpochParamsStored U V w (targetCap U 1) base y_set.mem)
    (hr_base : y_set.regs mBase = base)
    (hr_fr : y_set.regs mFr = base + compactedEpochWords U V w (targetCap U 1) 1)
    (hr_ib : y_set.regs mItemBase = base + offCompItems U w (targetCap U 1))
    (hr_u : x.regs mArgU = u.val)
    (hr_v : x.regs mArgV = v)
    (hr_nhp : ∀ i : Fin 19, y_set.regs (mNewHp i) =
      mkHashParams w (epochQBits U (targetCap U 1)) (epochHashB (targetCap U 1))
        (totalMicroBits (targetCap U 1)) 3 i)
    (hr_ncp : ∀ i : Fin 36, y_set.regs (mNewCp i) = mkCompParams U V w (targetCap U 1) i)
    (hrs_fr : y_rs.frontier = y_set.frontier)
    (hrs_seed : ReducedKWise.SeedRep (base + epochHdrWords) (qBits U (targetCap U 1))
      (hashB (targetCap U 1)) (totalMicroBits (targetCap U 1)) 3 θ y_rs.mem)
    (hrs_mem : ∀ a,
      a < base + epochHdrWords ∨
        base + epochHdrWords +
          ReducedKWise.seedWords (qBits U (targetCap U 1)) (hashB (targetCap U 1))
            (totalMicroBits (targetCap U 1)) 3 ≤ a →
      y_rs.mem a = y_set.mem a)
    (hrs_reg : ∀ reg, reg ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
      y_rs.regs reg = y_set.regs reg) :
    let N₁ := targetCap U 1
    let fr₁ := base + compactedEpochWords U V w N₁ 1
    let z₀ := (((((y_rs.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0)
    ∃ (z : RData rResize) (steps_clean : ℕ),
      RDemonicExec w fr₁ initFirstFinishCleanCode z₀ steps_clean (· = z) ∧
      z.Bounded w ∧
      z.frontier = fr₁ ∧
      CompactedSplitRep base (base + offCompItems U w N₁) U V w N₁ 1 1 θ
        (Function.update (Dictionary.empty U) u (some v)) ⟨z.mem, z.frontier⟩ ∧
      abiPreserved x z ∧
      (∀ addr < base, z.mem addr = x.mem addr) ∧
      (5 + steps_clean) + inEpochPotential U w N₁ base z ≤ 46350 * migFactor + 6 := by
  intro N₁ fr₁ z₀
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hy_set_b hhdr_set
  obtain ⟨hN₁_pos, _, hN₁_le2, hN₁U⟩ := targetCap_bounds_of_pos (le_rfl : 1 ≤ 1) hhdr_set.pos_U
  set off₁ := offCompItems U w N₁
  set iw₁ := compactedItemWords U V w N₁ 1
  have hce₁ : compactedEpochWords U V w N₁ 1 = off₁ + iw₁ := by
    unfold compactedEpochWords; simp [off₁, iw₁]
  have hfr₁_eq : fr₁ = base + off₁ + iw₁ := by dsimp only [fr₁]; rw [hce₁, Nat.add_assoc]
  have hfit_off : Fits w (base + off₁) := hfit_peak.of_le (by rw [hce₁]; linarith only)
  have h225_fit : Fits w 225 := fits_const_of_offCompItems hfit_off le_rfl
  have hw2 : 2 ≤ w := by
    by_contra hlt2; have hw1 : w ≤ 1 := by omega
    have := Nat.pow_le_pow_right two_pos hw1
    change 225 < 2 ^ w at h225_fit; omega
  have hlm_le : offCompLM U w N₁ ≤ off₁ := by
    dsimp only [off₁]; unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
  have hsp_le :
      225 + ReducedKWise.space w (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3 ≤ off₁ := by
    dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits, hashB]
      at hlm_le ⊢
    exact hlm_le
  have hsw_le_sp : ReducedKWise.seedWords (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3 ≤
      ReducedKWise.space w (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3 :=
    Nat.le_add_right _ _
  have hfit_h : Fits w ((base + 225) +
      ReducedKWise.space w (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3) :=
    hfit_off.of_le (by linarith only [hsp_le])
  have hc_lt : 2 * reducedChunkBits
      (reducedTrinomialStep (qBits U N₁) (hashB N₁) (totalMicroBits N₁)) < w :=
    ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space
      (two_mul_reducedChunkBits_hash_le hw2 hN₁U hU.le) hfit_h
  obtain ⟨z₀', hz₀'_def, _hex_zr, hz₀b, hz₀m, hz₀f_set, hz₀_reg⟩ :=
    zeroResampleRegsCode_exec hy_set_b hrs_fr hy_set_fr.le
      (qBits_le_of_le_pow hw hU.le) hc_lt
      (by
        rw [hy_set_fr]; change _ ≤ fr₁; rw [hfr₁_eq]; unfold epochHdrWords
        linarith only [hsw_le_sp, hsp_le])
      hrs_seed hrs_mem hrs_reg
  have hz₀_eq : z₀' = z₀ := hz₀'_def
  subst hz₀_eq
  have hz₀f : z₀.frontier = fr₁ := hz₀f_set.trans hy_set_fr
  set z₁ := z₀.set mTmpA base
  have hz₀_base : z₀.regs mBase = base :=
    (hz₀_reg mBase
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_base
  have hex_c1 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := fr₁)
    (d := mTmpA) (s := mBase) (x := z₀) hz₀f.le
  rw [hz₀_base] at hex_c1
  have hz₁b : z₁.Bounded w := hz₀b.set (hfit_off.of_le (Nat.le_add_right _ _))
  have hz₀_fr_reg : z₀.regs mFr = fr₁ :=
    (hz₀_reg mFr
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans hr_fr
  have hms₁ : memoryState mFr z₁.toData = ⟨y_rs.mem, fr₁⟩ :=
    Memory.State.ext hz₀m (by
      dsimp only [memoryState, z₁, RData.set, RData.toData]
      rw [Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mTmpA)]
      exact hz₀_fr_reg)
  have hz₁_nhp : ∀ i : Fin 19, z₁.regs (mNewHp i) =
      mkHashParams w (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3 i := fun i => by
    dsimp only [z₁, RData.set]
    rw [Function.update_of_ne (mNewHp_ne_mReg i (c := 156) (Or.inr (by decide))),
      hz₀_reg (mNewHp i) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
          mNewHp_ne_mReg i (Or.inl (by decide)), mNewHp_ne_mReg i (Or.inl (by decide)),
          mNewHp_ne_mReg i (Or.inl (by decide))⟩)]
    exact hr_nhp i
  have hz₁_ncp : ∀ i : Fin 36, z₁.regs (mNewCp i) = mkCompParams U V w N₁ i := fun i => by
    dsimp only [z₁, RData.set]
    rw [Function.update_of_ne (mNewCp_ne_mReg i (c := 156) (Or.inr (by decide))),
      hz₀_reg (mNewCp i) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
          mNewCp_ne_mReg i (Or.inl (by decide)), mNewCp_ne_mReg i (Or.inl (by decide)),
          mNewCp_ne_mReg i (Or.inl (by decide))⟩)]
    exact hr_ncp i
  have hin_im : z₁.regs ∘ srcInitNewMeta =
      WordEncoding.encode ((mkHashParams w (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3,
        mkCompParams U V w N₁), base) :=
    (regs_pairSrc (regs_pairSrc (regs_hp_eq hz₁_nhp) (regs_cp_eq hz₁_ncp))
      (regs_reg1_eq mTmpA (by simp [z₁, RData.set]))).eq
  obtain ⟨hpre_im, hv_im, hc_im, hfr_im, hrep_im, htot_im, hpot_im, ⟨s_fix₀, hinv₀, hcpl₀⟩,
      hframe_im⟩ :=
    initNewEpochMetaProg_spec (w := w) (U := U) (V := V) (N := N₁) (newMetaBase := base)
      (arenaBase := base + off₁) (θ_new := θ) (s₀ := ⟨y_rs.mem, fr₁⟩)
      hw hN₁_pos hN₁U hhdr_set.fits_U hV
      (by change base + off₁ ≤ fr₁; rw [hfr₁_eq]; exact Nat.le_add_right _ _)
      hfit_off hrs_seed
  obtain ⟨z₂, hex_im, hz₂b, hz₂f, hm_im, _, hframe_reg_im⟩ :=
    execWitness wInitNewMeta factor_wInitNewMeta_le mFr srcInitNewMeta tmpInitNewMeta
      tmpInitNewMeta_inj srcInitNewMeta_ne_tmp tmpInitNewMeta_ne_mFr srcInitNewMeta_ne_mFr
      ((mkHashParams w (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3,
        mkCompParams U V w N₁), base) hz₁b hz₀f.le
      hin_im (hms₁ ▸ hpre_im) (hms₁ ▸ hv_im)
      (by rw [hms₁, hfr_im]; exact hz₀f.symm.le)
  rw [hms₁] at hm_im hex_im
  have hz₂f_eq : z₂.frontier = fr₁ := hz₂f.trans hz₀f
  have hz₂_fr_reg : z₂.regs mFr = fr₁ := (congrArg Memory.State.frontier hm_im).trans hfr_im
  have hz₂_mem_eq : z₂.mem = ((Memory.spec 0).clientState ⟨y_rs.mem, fr₁⟩
      (initNewEpochMetaProg ((mkHashParams w (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3,
        mkCompParams U V w N₁), base))).mem :=
    congrArg Memory.State.mem hm_im
  have hms₂ : memoryState mFr z₂.toData = ⟨z₂.mem, fr₁⟩ := Memory.State.ext rfl hz₂_fr_reg
  have hz₂_keep1 : ∀ reg, reg ≠ mFr → reg.val < 160 → z₂.regs reg = z₁.regs reg :=
    fun reg h1 h160 => hframe_reg_im reg h1 (mkTmp_ne_reg _ h160 (fun a => Fin.elim0 a))
  have hkeep_set_2 : ∀ reg : Fin rResize, reg.val < 160 →
      reg ∉ ([mFr, mTmpA, mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
      z₂.regs reg = y_set.regs reg := fun reg h160 hnot => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    obtain ⟨hfr', hta, hcur, hidx, hk, ho, hres⟩ := hnot
    calc z₂.regs reg
        = z₁.regs reg := hz₂_keep1 reg hfr' h160
      _ = z₀.regs reg := by dsimp only [z₁, RData.set]; rw [Function.update_of_ne hta]
      _ = y_set.regs reg := hz₀_reg reg (by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨hcur, hidx, hk, ho, hres⟩)
  let d_si := (((mkHashParams w (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3,
    mkCompParams U V w N₁), (base, base + off₁)), (u.val, v))
  have hin_si : z₂.regs ∘ srcStreamIns = WordEncoding.encode d_si := by
    refine (regs_pairSrc
      (regs_pairSrc
        (regs_pairSrc
          (regs_hp_eq fun i => (hz₂_keep1 (mNewHp i) (mNewHp_ne_mReg i (Or.inl (by decide)))
            (mNewHp_lt_160 i)).trans (hz₁_nhp i))
          (regs_cp_eq fun i => (hz₂_keep1 (mNewCp i) (mNewCp_ne_mReg i (Or.inl (by decide)))
            (mNewCp_lt_160 i)).trans (hz₁_ncp i)))
        (regs_pairSrc
          (regs_reg1_eq mBase ((hkeep_set_2 mBase (mReg_lt_160 _)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans
            hr_base))
          (regs_reg1_eq mItemBase ((hkeep_set_2 mItemBase (mReg_lt_160 _)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans
            hr_ib))))
      (regs_pairSrc
        (regs_reg1_eq mArgU ((hkeep_set_2 mArgU (mReg_lt_160 _)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans
          (habi_set.2.2.1.trans hr_u)))
        (regs_reg1_eq mArgV ((hkeep_set_2 mArgV (mReg_lt_160 _)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)).trans
          (habi_set.2.2.2.trans hr_v))))).eq
  have hs₂_st_eq : ({ mem := z₂.mem, frontier := fr₁ } : Memory.State) =
      (Memory.spec 0).clientState ⟨y_rs.mem, fr₁⟩
        (initNewEpochMetaProg ((mkHashParams w (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3,
          mkCompParams U V w N₁), base)) :=
    Memory.State.ext hz₂_mem_eq hfr_im.symm
  have henv_si : CompEpochEnv U V w N₁ base (base + off₁) 1 ⟨z₂.mem, fr₁⟩ :=
    ⟨hw, hN₁_pos, hN₁U, hhdr_set.fits_U, hV, le_rfl,
      by change base + off₁ + iw₁ ≤ fr₁; rw [hfr₁_eq]⟩
  obtain ⟨hpre_si, hvp_si, hc_si, hfr_si, hrep_si, ⟨s_fix₁, hinv₁, hcpl₁⟩, hout_si⟩ :=
    streamInsertFreshGenProg_spec (s₀ := ⟨z₂.mem, fr₁⟩) u.isLt henv_si hfit_off
      (hz₂_mem_eq ▸ hrep_im) hinv₀ (hs₂_st_eq ▸ hcpl₀)
      (by rw [hz₂_mem_eq, htot_im]; exact hN₁_pos)
      (by rw [hz₂_mem_eq, htot_im])
      hv_lt (by simp [Dictionary.empty])
  have hv_si : (Memory.spec w).ValidHistory (memoryState mFr z₂.toData)
      ((Memory.spec w).clientHistory (memoryState mFr z₂.toData)
        (streamInsertFreshGenProg d_si)) := by
    have hwf₂ : Memory.WellFormed w (memoryState mFr z₂.toData) := wellFormed_memoryState hz₂b.1
    rw [hms₂] at hwf₂ ⊢
    exact hvp_si ⟨hwf₂, Nat.zero_le _⟩
  obtain ⟨z, hex_si, hzb, hzf, hm_si, _, hframe_reg_si⟩ :=
    execWitness wStreamIns factor_wStreamIns_le mFr srcStreamIns tmpStreamIns
      tmpStreamIns_inj srcStreamIns_ne_tmp tmpStreamIns_ne_mFr srcStreamIns_ne_mFr
      d_si hz₂b hz₂f_eq.le hin_si (hms₂ ▸ hpre_si) hv_si
      (by rw [hms₂, hfr_si]; exact hz₂f_eq.symm.le)
  rw [hms₂] at hm_si hex_si
  have hzf_eq : z.frontier = fr₁ := hzf.trans hz₂f_eq
  have hz_mem_eq : z.mem = ((Memory.spec 0).clientState ⟨z₂.mem, fr₁⟩
      (streamInsertFreshGenProg d_si)).mem :=
    congrArg Memory.State.mem hm_si
  have hs_z_eq : ({ mem := z.mem, frontier := z.frontier } : Memory.State) =
      (Memory.spec 0).clientState ⟨z₂.mem, fr₁⟩ (streamInsertFreshGenProg d_si) :=
    Memory.State.ext hz_mem_eq (hzf_eq.trans hfr_si.symm)
  have hlow_z : ∀ a < base + 63, z.mem a = y_set.mem a := fun a ha => by
    have heh : epochHdrWords = 225 := rfl
    have h0_lm : epochHdrWords ≤ offCompLM U w N₁ := Nat.le_add_right _ _
    have h225_off : 225 ≤ off₁ := by linarith only [heh, h0_lm, hlm_le]
    rw [hz_mem_eq,
      hout_si a (fun h => by linarith only [ha, h.1])
        (fun h => by linarith only [ha, h.1, heh, h0_lm])
        (fun h => by linarith only [ha, h.1, h225_off]),
      hz₂_mem_eq,
      hframe_im a (fun h => by linarith only [ha, h.1, heh])]
    exact hrs_mem a (Or.inl (by linarith only [ha, heh]))
  have hhdr_z : RootHeaderValid U V w N₁ 1 1 base z.mem :=
    rootHeaderValid_congr hhdr_set fun a ha => hlow_z a (by linarith only [ha.2])
  have hpar_z : EpochParamsStored U V w N₁ base z.mem :=
    epochParamsStored_congr hpar_set fun a ha => hlow_z a ha.2
  have hcard₁ : (Dictionary.dom (Function.update (Dictionary.empty U) u (some v))).card = 1 := by
    rw [Dictionary.dom_insert, Dictionary.dom_empty]; rfl
  have hvals₁ : Dictionary.ValuesBounded V (Function.update (Dictionary.empty U) u (some v)) := by
    intro k val hk
    by_cases hku : k = u
    · subst hku; simp only [Function.update_self, Option.some.injEq] at hk; subst hk; exact hv_lt
    · rw [Function.update_of_ne hku] at hk; cases hk
  have hcpl_z : FixedCoupled base (base + off₁) U V w N₁ s_fix₁ ⟨z.mem, z.frontier⟩ :=
    hs_z_eq ▸ hcpl₁
  have htot_z : totalSlots N₁ (compGmAt base U w N₁ z.mem) = 1 :=
    (congrArg (totalSlots N₁) hcpl_z.gm_eq).trans (hinv₁.htot.trans hcard₁)
  have hsplit_z : CompactedSplitRep base (base + off₁) U V w N₁ 1 1 θ
      (Function.update (Dictionary.empty U) u (some v)) ⟨z.mem, z.frontier⟩ :=
    ⟨hhdr_z, hpar_z, hz_mem_eq ▸ hrep_si, hcard₁, hvals₁, s_fix₁, hinv₁, htot_z, hcpl_z⟩
  have hz_keep2 : ∀ reg, reg ≠ mFr → reg.val < 160 → z.regs reg = z₂.regs reg :=
    fun reg h1 h160 => hframe_reg_si reg h1 (mkTmp_ne_reg _ h160 (fun a => Fin.elim0 a))
  have habi_set_z : abiPreserved y_set z :=
    ⟨(hz_keep2 mBase (mReg_ne (by decide)) (mReg_lt_160 _)).trans
        (hkeep_set_2 mBase (mReg_lt_160 _)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)),
     (hz_keep2 mTag (mReg_ne (by decide)) (mReg_lt_160 _)).trans
        (hkeep_set_2 mTag (mReg_lt_160 _)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)),
     (hz_keep2 mArgU (mReg_ne (by decide)) (mReg_lt_160 _)).trans
        (hkeep_set_2 mArgU (mReg_lt_160 _)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide)),
     (hz_keep2 mArgV (mReg_ne (by decide)) (mReg_lt_160 _)).trans
        (hkeep_set_2 mArgV (mReg_lt_160 _)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, mReg_inj]; decide))⟩
  have hf1 := one_le_migFactor
  have hc_im_mul : migFactor * (memoryCost
      (initNewEpochMetaProg ((mkHashParams w (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3,
        mkCompParams U V w N₁), base)) ⟨y_rs.mem, fr₁⟩ + 1) ≤ migFactor * 988 :=
    Nat.mul_le_mul_left migFactor (by dsimp only [N₁] at hc_im; linarith only [hc_im, hN₁_le2])
  have hpot_le : inEpochPotential U w N₁ base z ≤
      (98 * migFactor) * slotPotential N₁ (compGmAt base U w N₁ z.mem) := by
    unfold inEpochPotential
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 98 inEpochFactor_le_migFactor)
  have hsi_pot : migFactor * (memoryCost (streamInsertFreshGenProg d_si) ⟨z₂.mem, fr₁⟩ + 1) +
      inEpochPotential U w N₁ base z ≤ 45361 * migFactor := by
    have hpot₂ : slotPotential N₁ (compGmAt base U w N₁ z₂.mem) = 0 := by
      rw [hz₂_mem_eq]; exact hpot_im
    dsimp only at hc_si
    rw [hpot₂, Nat.mul_zero, Nat.zero_add] at hc_si
    have hmul := Nat.mul_le_mul_left migFactor (Nat.add_le_add_right hc_si 1)
    rw [← hz_mem_eq] at hmul
    nlinarith only [hmul, hpot_le, hf1]
  have hex_clean := hex_c1.seq_eq ((hex_im.mono hc_im_mul (fun _ h => h)).seq_eq hex_si)
  refine ⟨z, _, hex_clean, hzb, hzf_eq, hsplit_z, abiPreserved_trans habi_set habi_set_z,
    fun addr haddr => (hlow_z addr (by linarith only [haddr])).trans (hbelow_set addr haddr),
    by linarith only [hsi_pot]⟩

/-- **Distributional `0 → 1` Epoch Creation (`initFirstEpochCode_execRCodeDist`):**
From the 8-word empty dictionary state (`n = 0`, `N = 0`) at `base`, `initFirstEpochCode` creates
the first active epoch `(N₁, 1, 1)` (`N₁ = targetCap U 1`) containing `(u, v)` under a fresh
uniform `QuotHashSeed U N₁`, never exceeding `base + compactedEpochWords U V w N₁ 1` and bounding
expected instructions plus post-step `inEpochPotential` by `initFirstCharge`. -/
theorem initFirstEpochCode_execRCodeDist {U V w base : ℕ} (u : Fin U) (v : ℕ) {x : RData rResize}
    (hx : x.Bounded w)
    (hfr : x.frontier = base + 8)
    (hhdr : RootHeaderValid U V w 0 0 0 base x.mem)
    (hv_lt : v < V)
    (hfit_peak : Fits w (base + compactedEpochWords U V w (targetCap U 1) 1))
    (hbase : x.regs mBase = base)
    (hu_reg : x.regs mArgU = u.val)
    (hv_reg : x.regs mArgV = v) :
    let N₁ := targetCap U 1
    let fr₁ := base + compactedEpochWords U V w N₁ 1
    ∃ (zOf : QuotHashSeed U N₁ → RData rResize) (T_init : ℝ≥0∞),
      ExecRCodeDist w initFirstEpochCode x
        ((PMF.uniformOfFintype (QuotHashSeed U N₁)).map zOf) T_init fr₁ ∧
      (∀ θ,
        (zOf θ).Bounded w ∧
        (zOf θ).frontier = fr₁ ∧
        CompactedSplitRep base (base + offCompItems U w N₁) U V w N₁ 1 1 θ
          (Function.update (Dictionary.empty U) u (some v))
          ⟨(zOf θ).mem, (zOf θ).frontier⟩ ∧
        (zOf θ).regs mBase = base ∧
        (∀ addr < base, (zOf θ).mem addr = x.mem addr)) ∧
      T_init + (∑' θ, (PMF.uniformOfFintype (QuotHashSeed U N₁)) θ *
          (inEpochPotential U w N₁ base (zOf θ) : ℝ≥0∞)) ≤
        (initFirstCharge : ℝ≥0∞) := by
  intro N₁ fr₁
  obtain ⟨hw, hU, _⟩ := rootHeaderValid_bounds hx hhdr
  obtain ⟨_, _, _, hN₁U⟩ := targetCap_bounds_of_pos (le_rfl : 1 ≤ 1) hhdr.pos_U
  obtain ⟨s₁₀, steps_p, hex_p, hc_p, hs₁₀b, hs₁₀f, habi₁₀, hbelow₁₀, hhdr₁₀, hpar₁₀,
      hs₁₀_base, hs₁₀_fr, hs₁₀_off, hs₁₀_iw, hs₁₀_nhp, hs₁₀_ncp⟩ :=
    initFirstParamsCode_exec hx hfr hhdr hfit_peak hbase
  obtain ⟨y_set, steps_g, hex_g, hc_g, hy_set_b, hy_set_fr, habi_set, hbelow_set,
      hhdr_set, hpar_set, hr_base, hr_fr, hr_ib, hr_hb, hr_nhp, hr_ncp⟩ :=
    initFirstGrowCode_exec hfit_peak hs₁₀b hs₁₀f habi₁₀ hbelow₁₀ hhdr₁₀ hpar₁₀
      hs₁₀_base hs₁₀_fr hs₁₀_off hs₁₀_iw hs₁₀_nhp hs₁₀_ncp
  have hex_set : RDemonicExec w fr₁ initFirstSetupCode x (steps_p + steps_g) (· = y_set) :=
    hex_p.seq_eq hex_g
  have hce₁ : compactedEpochWords U V w N₁ 1 =
      offCompItems U w N₁ + compactedItemWords U V w N₁ 1 := by
    unfold compactedEpochWords; simp
  have hnm_le : base + offCompItems U w N₁ ≤ fr₁ := by
    dsimp only [fr₁]; rw [hce₁]; omega
  obtain ⟨zOf, T_init, hex_full, hpost, hcost⟩ :=
    exec_setup_resample_finish (metaBase := base) (base := base)
      (finBound := 46350 * migFactor + 6)
      (finishCleanCode := initFirstFinishCleanCode)
      (P := fun θ z =>
        z.Bounded w ∧
        z.frontier = fr₁ ∧
        CompactedSplitRep base (base + offCompItems U w N₁) U V w N₁ 1 1 θ
          (Function.update (Dictionary.empty U) u (some v))
          ⟨z.mem, z.frontier⟩ ∧
        z.regs mBase = base ∧
        (∀ addr < base, z.mem addr = x.mem addr))
      hw hU hN₁U hex_set hy_set_b hy_set_fr (hfit_peak.of_le hnm_le) hnm_le hr_hb hr_nhp
      (fun θ y_rs hfr_y hseed_y hmem_y hreg_y => by
        obtain ⟨z, stepsClean, hex_cl, hzb, hzf, hsp, habi, hbel, hbd⟩ :=
          initFirstFinishCode_exec u v hv_lt hfit_peak hy_set_b hy_set_fr habi_set hbelow_set
            hhdr_set hpar_set hr_base hr_fr hr_ib hu_reg hv_reg hr_nhp hr_ncp
            hfr_y hseed_y hmem_y hreg_y
        exact ⟨z, stepsClean, hex_cl, ⟨hzb, hzf, hsp, habi.1.trans hbase, hbel⟩, hbd⟩)
  refine ⟨zOf, T_init, hex_full, hpost, hcost.trans ((Nat.cast_le (α := ℝ≥0∞)).mpr ?_)⟩
  have hf1 := one_le_migFactor
  unfold initFirstCharge
  linarith only [hc_p, hc_g, hf1]

private theorem deleteLastReadCode_exec {U V w N n_init base : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {x : RData rResize}
    (hx : x.Bounded w) (hev : EpochValid U 1 N)
    (hfr : x.frontier = base + compactedEpochWords U V w N 1)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N 1 n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base) :
    let u₀ := reconstructKeyAt base (base + offCompItems U w N) U V w N 1 θ x.mem 0
    ∃ (y : RData rResize) (steps_r : ℕ),
      RDemonicExec w x.frontier deleteLastReadCode x steps_r (· = y) ∧
      steps_r ≤ 45182 * migFactor + 170 ∧
      y.Bounded w ∧
      y.frontier = x.frontier ∧
      y.regs mFr = x.frontier ∧
      y.regs mBase = base ∧
      y.regs mArgU = x.regs mArgU ∧
      y.regs mU0 = u₀ ∧
      (∀ a, ¬(base + 63 ≤ a ∧ a < base + 225) → y.mem a = x.mem a) := by
  intro u₀
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  have h1N : 1 ≤ N := by rcases hev with ⟨h0, _⟩ | ⟨_, h1N, _, _⟩ <;> omega
  have hNU : N ≤ U := by rcases hev with ⟨h0, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  set off := offCompItems U w N
  set iw := compactedItemWords U V w N 1
  have hce : compactedEpochWords U V w N 1 = off + iw := by
    unfold compactedEpochWords; simp [off, iw]
  have hfr_eq : x.frontier = base + off + iw := by rw [hfr, hce, Nat.add_assoc]
  have h225 : 225 ≤ off := by
    dsimp only [off]
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
  have hfit_fr : Fits w x.frontier := hx.frontier_fits
  have hfit_off : Fits w (base + off) := hfit_fr.of_le (by rw [hfr_eq]; linarith only)
  have hfit1 : Fits w 1 := hfit_off.of_le (by linarith only [h225])
  obtain ⟨x₁, hex_hp, hx₁b, hx₁m, hx₁f, hx₁_hp, hx₁_r⟩ :=
    loadBlockUpTo_exec mBase mCur (mReg_ne (by decide)) mOldHp mOldHp_inj
      (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))
      (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))
      offHashParams 18 (by decide) hx le_rfl hbase
      (by change base + 8 + 19 ≤ x.frontier; rw [hfr_eq]; omega)
  have hx₁_base : x₁.regs mBase = base :=
    (hx₁_r mBase (mReg_ne (by decide)) (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))).trans hbase
  obtain ⟨x₂, hex_cp, hx₂b, hx₂m, hx₂f, hx₂_cp, hx₂_r⟩ :=
    loadBlockUpTo_exec mBase mCur (mReg_ne (by decide)) mOldCp mOldCp_inj
      (fun i => mOldCp_ne_mReg i (Or.inl (by decide)))
      (fun i => mOldCp_ne_mReg i (Or.inl (by decide)))
      offCompParams 35 (by decide) hx₁b hx₁f.le hx₁_base
      (by change base + 27 + 36 ≤ x₁.frontier; rw [hx₁f, hfr_eq]; omega)
  have hx₂m_eq : x₂.mem = x.mem := hx₂m.trans hx₁m
  have hx₂f_eq : x₂.frontier = x.frontier := hx₂f.trans hx₁f
  have hx₂_hp_all : ∀ i : Fin 19, x₂.regs (mOldHp i) =
      mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i := fun i => by
    rw [hx₂_r (mOldHp i) (mOldHp_ne_mReg i (Or.inl (by decide)))
      (fun j => by intro h; have hv := congrArg Fin.val h; simp at hv; omega),
      hx₁_hp i (by omega)]
    exact hsplit.params_stored.hp_eq i
  have hx₂_cp_all : ∀ i : Fin 36, x₂.regs (mOldCp i) = mkCompParams U V w N i := fun i => by
    rw [hx₂_cp i (by omega), hx₁m]; exact hsplit.params_stored.cp_eq i
  set x₃ := (x₂.set mCnt 1).set mFr 0
  have hex_c1 := RDemonicExec.const (B := .exact) (d := mCnt) (v := 1) (x := x₂) hx₂f_eq.le hfit1
  have hex_zfr := RDemonicExec.const (B := .exact) (d := mFr) (v := 0) (x := x₂.set mCnt 1)
    hx₂f_eq.le (fits_zero w)
  have hx₃b : x₃.Bounded w := (hx₂b.set hfit1).set (fits_zero w)
  have hin_iw : x₃.regs ∘ srcOldIw = WordEncoding.encode (mkCompParams U V w N, 1) := by
    refine (regs_pairSrc (regs_cp_eq fun i => ?_) (regs_reg1_eq mCnt ?_)).eq
    · dsimp only [x₃, RData.set]
      rw [Function.update_of_ne (mOldCp_ne_mReg i (c := 1) (Or.inl (by decide))),
        Function.update_of_ne (mOldCp_ne_mReg i (c := 13) (Or.inl (by decide)))]
      exact hx₂_cp_all i
    · simp [x₃, RData.set]
  have hfit_iw4 : Fits w (4 + iw) := hfit_fr.of_le (by rw [hfr_eq]; linarith only [h225])
  have hsafe_iw : CompItemWordsPre w (mkCompParams U V w N, 1) (memoryState mFr x₃.toData) :=
    ⟨U, V, N, hw, hNU, hU, hV, rfl, fits_wOffQ_add_three_of_itemWords hw hfit_iw4⟩
  have hv_iw := validProg_compItemWordsGen (mkCompParams U V w N, 1)
    (memoryState mFr x₃.toData) ⟨wellFormed_memoryState hx₃b.1, Nat.zero_le _⟩
  obtain ⟨x₄, hex_iw, hx₄b, hx₄f, hm_iw, hout_iw, hframe_iw⟩ :=
    execWitness wItemWords factor_mItemWords_le mFr srcOldIw tmpOldIw
      tmpOldIw_inj srcOldIw_ne_tmp tmpOldIw_ne_mFr srcOldIw_ne_mFr
      (mkCompParams U V w N, 1) hx₃b hx₂f_eq.le hin_iw hsafe_iw hv_iw
      (by rw [clientState_compItemWordsGenProg]; change 0 ≤ x₃.frontier; omega)
  rw [memoryCost_compItemWordsGenProg, zero_add, mul_one] at hex_iw
  rw [clientState_compItemWordsGenProg] at hm_iw
  have hx₄m : x₄.mem = x.mem := (congrArg Memory.State.mem hm_iw).trans hx₂m_eq
  have hx₄f_eq : x₄.frontier = x.frontier := hx₄f.trans hx₂f_eq
  have hx₄_iw : x₄.regs mIwOld = iw := by
    have h0 := hout_iw 0; rwa [tmpOldIw_out, clientResult_compItemWordsGenProg hw] at h0
  have hx₄_keep3 : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mIwOld → x₄.regs reg = x₃.regs reg :=
    fun reg h1 h160 hiw => hframe_iw reg h1
      (mkTmp_ne_reg _ h160 (fun a => by fin_cases a; exact hiw.symm))
  have hx₄_base : x₄.regs mBase = base :=
    (hx₄_keep3 mBase (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
    (by simp [x₃, RData.set] : x₃.regs mBase = x₂.regs mBase).trans <|
    (hx₂_r mBase (mReg_ne (by decide)) (fun i => mOldCp_ne_mReg i (Or.inl (by decide)))).trans
      hx₁_base
  have hx₄_cp34 : x₄.regs (mOldCp ⟨34, by decide⟩) = off := by
    rw [hx₄_keep3 (mOldCp ⟨34, by decide⟩) (mOldCp_ne_mReg _ (Or.inl (by decide)))
      (mOldCp_lt_160 _) (mOldCp_ne_mReg _ (Or.inr (by decide)))]
    dsimp only [x₃, RData.set]
    rw [Function.update_of_ne (mOldCp_ne_mReg _ (c := 1) (Or.inl (by decide))),
      Function.update_of_ne (mOldCp_ne_mReg _ (c := 13) (Or.inl (by decide))),
      hx₂_cp_all ⟨34, by decide⟩]
    exact cpOffItems_mk U V w N
  set x₅ := x₄.set mItemBase (base + off)
  have hex_ib := RDemonicExec.exactBin (f := .add) (d := mItemBase) (i := mBase)
    (j := mOldCp ⟨34, by decide⟩) (w := w) (L_peak := x.frontier) (x := x₄) hx₄f_eq.le
    (v := base + off)
    (by change some (x₄.regs mBase + x₄.regs (mOldCp ⟨34, by decide⟩)) = some (base + off)
        rw [hx₄_base, hx₄_cp34])
    hfit_off
  set x₆ := x₅.set mFr x.frontier
  have hex_fr := RDemonicExec.exactBin (f := .add) (d := mFr) (i := mItemBase) (j := mIwOld)
    (w := w) (L_peak := x.frontier) (x := x₅) hx₄f_eq.le (v := x.frontier)
    (by simp [BinOp.evalExact, x₅, RData.set, hx₄_iw, hfr_eq]) hfit_fr
  set x₇ := x₆.set mZero 0
  have hex_z := RDemonicExec.const (B := .exact) (d := mZero) (v := 0) (x := x₆) hx₄f_eq.le
    (fits_zero w)
  have hx₇b : x₇.Bounded w := ((hx₄b.set hfit_off).set hfit_fr).set (fits_zero w)
  have hms₇ : memoryState mFr x₇.toData = ⟨x.mem, x.frontier⟩ :=
    Memory.State.ext hx₄m (by
      dsimp only [memoryState, x₇, x₆, RData.set, RData.toData]
      rw [Function.update_of_ne (mReg_ne (by decide) : mFr ≠ mZero), Function.update_self])
  let d_ro := (((mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3,
    mkCompParams U V w N), (base, base + off)), 0)
  have hin_ro : x₇.regs ∘ srcReadOldKV = WordEncoding.encode d_ro := by
    refine (regs_pairSrc
      (regs_pairSrc
        (regs_pairSrc (regs_hp_eq fun i => ?_) (regs_cp_eq fun i => ?_))
        (regs_pairSrc (regs_reg1_eq mBase (by simp [x₇, x₆, x₅, RData.set, hx₄_base]))
          (regs_reg1_eq mItemBase (by simp [x₇, x₆, x₅, RData.set]))))
      (regs_reg1_eq mZero (by simp [x₇, RData.set]))).eq
    · dsimp only [x₇, x₆, x₅, RData.set]
      rw [Function.update_of_ne (mOldHp_ne_mReg i (c := 11) (Or.inl (by decide))),
        Function.update_of_ne (mOldHp_ne_mReg i (c := 1) (Or.inl (by decide))),
        Function.update_of_ne (mOldHp_ne_mReg i (c := 14) (Or.inl (by decide))),
        hx₄_keep3 (mOldHp i) (mOldHp_ne_mReg i (Or.inl (by decide))) (mOldHp_lt_160 i)
          (mOldHp_ne_mReg i (Or.inr (by decide)))]
      dsimp only [x₃, RData.set]
      rw [Function.update_of_ne (mOldHp_ne_mReg i (c := 1) (Or.inl (by decide))),
        Function.update_of_ne (mOldHp_ne_mReg i (c := 13) (Or.inl (by decide)))]
      exact hx₂_hp_all i
    · dsimp only [x₇, x₆, x₅, RData.set]
      rw [Function.update_of_ne (mOldCp_ne_mReg i (c := 11) (Or.inl (by decide))),
        Function.update_of_ne (mOldCp_ne_mReg i (c := 1) (Or.inl (by decide))),
        Function.update_of_ne (mOldCp_ne_mReg i (c := 14) (Or.inl (by decide))),
        hx₄_keep3 (mOldCp i) (mOldCp_ne_mReg i (Or.inl (by decide))) (mOldCp_lt_160 i)
          (mOldCp_ne_mReg i (Or.inr (by decide)))]
      dsimp only [x₃, RData.set]
      rw [Function.update_of_ne (mOldCp_ne_mReg i (c := 1) (Or.inl (by decide))),
        Function.update_of_ne (mOldCp_ne_mReg i (c := 13) (Or.inl (by decide)))]
      exact hx₂_cp_all i
  obtain ⟨s_fix, hinv, htot, hcpl⟩ := hsplit.coupled
  obtain ⟨L_b, hb_inv⟩ := hinv.hbucket
  have hslot : SlotStoreInv N (compGmAt base U w N x.mem) := by
    rw [hcpl.gm_eq]; exact hb_inv.hslot
  have htd : 0 < bucketBits N →
      TailDenseInv N (compGmAt base U w N x.mem 0) (compGmAt base U w N x.mem 1)
        (compTDAt base U w N x.mem) (compDTAt base U w N x.mem) :=
    fun hb => hcpl.tailDenseInv hb
  obtain ⟨hrec_val, _, _⟩ := reconstructKeyAt_spec hsplit.vals_lt hNU hinv hcpl htot
  obtain ⟨hu₀_lt, _, _⟩ := hrec_val 0 zero_lt_one
  obtain ⟨hpre_ro, hvp_ro, hc_ro, hres_ro, hfr_ro, hout_ro⟩ :=
    readOldItemKeyValGenProg_spec (s₀ := ⟨x.mem, x.frontier⟩) hw h1N hNU hsplit.root_hdr.fits_U hV
      le_rfl (by change base + off + iw ≤ x.frontier; rw [hfr_eq]) hfit_off hsplit.hash_rep
      hslot htd htot zero_lt_one hu₀_lt
  have hv_ro : (Memory.spec w).ValidHistory (memoryState mFr x₇.toData)
      ((Memory.spec w).clientHistory (memoryState mFr x₇.toData)
        (readOldItemKeyValGenProg d_ro)) := by
    have hwf₇ : Memory.WellFormed w (memoryState mFr x₇.toData) := wellFormed_memoryState hx₇b.1
    rw [hms₇] at hwf₇ ⊢
    exact hvp_ro ⟨hwf₇, Nat.zero_le _⟩
  obtain ⟨y, hex_ro, hyb, hyf, hm_ro, hout_reg_ro, hframe_ro⟩ :=
    execWitness wReadOldKV factor_wReadOldKV_le mFr srcReadOldKV tmpReadOldKV
      tmpReadOldKV_inj srcReadOldKV_ne_tmp tmpReadOldKV_ne_mFr srcReadOldKV_ne_mFr
      d_ro hx₇b hx₄f_eq.le hin_ro (hms₇ ▸ hpre_ro) hv_ro
      (by rw [hms₇, hfr_ro]; exact hx₄f_eq.symm.le)
  rw [hms₇] at hm_ro hout_reg_ro hex_ro
  rw [hres_ro] at hout_reg_ro
  have hyf_eq : y.frontier = x.frontier := hyf.trans hx₄f_eq
  have hy_fr_reg : y.regs mFr = x.frontier := (congrArg Memory.State.frontier hm_ro).trans hfr_ro
  have hy_u0 : y.regs mU0 = u₀ := by
    have h0 := hout_reg_ro 0; rwa [tmpReadOldKV_out_0] at h0
  have hy_keep7 : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mU0 → reg ≠ mV0 →
      y.regs reg = x₇.regs reg := fun reg h1 h160 hu0 hv0 =>
    hframe_ro reg h1
      (mkTmp_ne_reg _ h160 (fun a => by fin_cases a <;> [exact hu0.symm; exact hv0.symm]))
  have hy_argu : y.regs mArgU = x.regs mArgU := by
    rw [hy_keep7 mArgU (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
      (mReg_ne (by decide))]
    dsimp only [x₇, x₆, x₅, RData.set]
    rw [Function.update_of_ne (mReg_ne (by decide)),
      Function.update_of_ne (mReg_ne (by decide)),
      Function.update_of_ne (mReg_ne (by decide)),
      hx₄_keep3 mArgU (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))]
    dsimp only [x₃, RData.set]
    rw [Function.update_of_ne (mReg_ne (by decide)),
      Function.update_of_ne (mReg_ne (by decide)),
      hx₂_r mArgU (mReg_ne (by decide)) (fun i => mOldCp_ne_mReg i (Or.inl (by decide))),
      hx₁_r mArgU (mReg_ne (by decide)) (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))]
  have hc_ro_mul :
      migFactor * (memoryCost (readOldItemKeyValGenProg d_ro) ⟨x.mem, x.frontier⟩ + 1) ≤
        migFactor * 45181 :=
    Nat.mul_le_mul_left migFactor (Nat.add_le_add_right hc_ro 1)
  have hf1 := one_le_migFactor
  have hex_all :=
    hex_hp.seq_eq (hex_cp.seq_eq (hex_c1.seq_eq (hex_zfr.seq_eq (hex_iw.seq_eq
      (hex_ib.seq_eq (hex_fr.seq_eq (hex_z.seq_eq
        (hex_ro.mono hc_ro_mul (fun _ h => h)))))))))
  refine ⟨y, _, hex_all, by linarith only [hf1], hyb, hyf_eq, hy_fr_reg,
    (hy_keep7 mBase (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
      (mReg_ne (by decide))).trans (by simp [x₇, x₆, x₅, RData.set, hx₄_base]),
    hy_argu, hy_u0,
    fun a ha => (congrArg (fun s => s.mem a) hm_ro).trans (hout_ro a ha)⟩

private theorem deleteLastHitTailCode_exec {U V w N n_init base : ℕ} {x y : RData rResize}
    (hev : EpochValid U 1 N)
    (hfr : x.frontier = base + compactedEpochWords U V w N 1)
    (hhdr : RootHeaderValid U V w N 1 n_init base x.mem)
    (hyb : y.Bounded w)
    (hyf : y.frontier = x.frontier)
    (hy_fr_reg : y.regs mFr = x.frontier)
    (hy_base : y.regs mBase = base)
    (hy_mem : ∀ a, ¬(base + 63 ≤ a ∧ a < base + 225) → y.mem a = x.mem a) :
    ∃ (z : RData rResize) (steps_h : ℕ),
      RDemonicExec w x.frontier deleteLastHitTailCode y steps_h (· = z) ∧
      steps_h ≤ 5830 ∧
      CompactedRep U V w 0 0 0 base (Dictionary.empty U) z ∧
      z.regs mBase = base ∧
      (∀ addr < base, z.mem addr = x.mem addr) := by
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hyb
    (rootHeaderValid_congr hhdr fun a ha => hy_mem a (fun h => by linarith only [ha.2, h.1]))
  have hN4 : N ≤ 4 := by rcases hev with ⟨h0, _⟩ | ⟨_, _, hN4, _⟩ <;> omega
  have hNU : N ≤ U := by rcases hev with ⟨h0, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  set off := offCompItems U w N
  set iw := compactedItemWords U V w N 1
  have hce : compactedEpochWords U V w N 1 = off + iw := by
    unfold compactedEpochWords; simp [off, iw]
  have hfr_eq : x.frontier = base + off + iw := by rw [hfr, hce, Nat.add_assoc]
  have h225 : 225 ≤ off := by
    dsimp only [off]
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
  have hfit_fr : Fits w x.frontier := hyf ▸ hyb.frontier_fits
  have hfit8 : Fits w 8 := hfit_fr.of_le (by rw [hfr_eq]; linarith only [h225])
  have hfit1 : Fits w 1 := hfit8.of_le (by decide)
  set y₁ := y.set mZero 0
  have hex_z0 := RDemonicExec.const (B := .exact) (d := mZero) (v := 0) (x := y) hyf.le
    (fits_zero w)
  have hy₁b : y₁.Bounded w := hyb.set (fits_zero w)
  obtain ⟨hex_st5, hy₂b⟩ := storeAtOffCode_exec (rAddr := mBase) (rSrc := mZero) (rTmp := mCur)
    (base := base) (off := 5) (val := 0) hy₁b hyf.le (mReg_ne (by decide)) (mReg_ne (by decide))
    (by simp [y₁, RData.set, hy_base]) (by simp [y₁, RData.set]) (hfit8.of_le (by decide))
    (by change base + 5 < y.frontier; rw [hyf, hfr_eq]; omega)
  set y₂ := (y₁.set mCur (base + 5)).write (base + 5) 0
  obtain ⟨hex_st6, hy₃b⟩ := storeAtOffCode_exec (rAddr := mBase) (rSrc := mZero) (rTmp := mCur)
    (base := base) (off := 6) (val := 0) hy₂b hyf.le (mReg_ne (by decide)) (mReg_ne (by decide))
    (by simp [y₂, y₁, RData.set, RData.write, hy_base])
    (by simp [y₂, y₁, RData.set, RData.write])
    (hfit8.of_le (by decide)) (by change base + 6 < y.frontier; rw [hyf, hfr_eq]; omega)
  set y₃ := (y₂.set mCur (base + 6)).write (base + 6) 0
  obtain ⟨hex_st7, hy₄b⟩ := storeAtOffCode_exec (rAddr := mBase) (rSrc := mZero) (rTmp := mCur)
    (base := base) (off := 7) (val := 0) hy₃b hyf.le (mReg_ne (by decide)) (mReg_ne (by decide))
    (by simp [y₃, y₂, y₁, RData.set, RData.write, hy_base])
    (by simp [y₃, y₂, y₁, RData.set, RData.write])
    (hfit8.of_le (by decide)) (by change base + 7 < y.frontier; rw [hyf, hfr_eq]; omega)
  set y₄ := (y₃.set mCur (base + 7)).write (base + 7) 0
  set y₅ := y₄.set mCur 8
  have hex_c8 := RDemonicExec.const (B := .exact) (d := mCur) (v := 8) (x := y₄) hyf.le hfit8
  set y₆ := y₅.set mCur (base + 8)
  have hy₄_base : y₄.regs mBase = base := by
    simp [y₄, y₃, y₂, y₁, RData.set, RData.write, hy_base]
  have hy₄_fr : y₄.regs mFr = x.frontier := by
    simp [y₄, y₃, y₂, y₁, RData.set, RData.write, hy_fr_reg]
  have hfit_b8 : Fits w (base + 8) := hfit_fr.of_le (by rw [hfr_eq]; linarith only [h225])
  have hex_add := RDemonicExec.exactBin (f := .add) (d := mCur) (i := mBase) (j := mCur)
    (w := w) (L_peak := x.frontier) (x := y₅) hyf.le (v := base + 8)
    (by simp [BinOp.evalExact, y₅, RData.set, hy₄_base]) hfit_b8
  have hy₆_eq : (y₅.set mCur (base + 8)) = y₄.set mCur (base + 8) := by
    ext j <;> simp [y₅, RData.set]
  have hb8_le : base + 8 ≤ x.frontier := by rw [hfr_eq]; linarith only [h225]
  set y₇ := (y₄.set mCur (base + 8)).set mK (x.frontier - (base + 8))
  have hex_sub := RDemonicExec.exactBin (f := .sub) (d := mK) (i := mFr) (j := mCur)
    (w := w) (L_peak := x.frontier) (x := y₄.set mCur (base + 8)) hyf.le
    (v := x.frontier - (base + 8))
    (by simp [BinOp.evalExact, RData.set, hy₄_fr, hb8_le])
    (hfit_fr.of_le (Nat.sub_le _ _))
  rw [hy₆_eq] at hex_add
  have hy₇b : y₇.Bounded w := (hy₄b.set hfit_b8).set (hfit_fr.of_le (Nat.sub_le _ _))
  have hy₇_k : y₇.regs mK = x.frontier - (base + 8) := by simp [y₇, RData.set]
  have hk_le_fr : y₇.regs mK ≤ y₇.frontier := by
    rw [hy₇_k, show y₇.frontier = x.frontier from hyf]; exact Nat.sub_le _ _
  have hfr_sub : y₇.frontier - y₇.regs mK = base + 8 := by
    rw [show y₇.frontier = x.frontier from hyf, hy₇_k]; exact Nat.sub_sub_self hb8_le
  have hex_sh := shrinkCode_exec (w := w) (L_peak := x.frontier)
    (count := mK) (idx := mIdx) (zero := mZero) (one := mOne)
    hy₇b mShrink_nodup hfit1 hyf.le hk_le_fr
  rw [hy₇_k] at hex_sh
  set z := shrinkPost mK mIdx mZero mOne y₇
  have hzb : z.Bounded w := shrinkPost_bounded hy₇b hfit1 hk_le_fr
  have hzf : z.frontier = base + 8 := hfr_sub
  have hz_lt8 : ∀ a < base + 8, z.mem a = y₄.mem a := fun a ha => by
    change clear y₄.mem (y₇.frontier - y₇.regs mK) (y₇.regs mK) a = y₄.mem a
    rw [hfr_sub]
    exact clear_of_not_owns (by simp only [Block.Owns, not_and_or, not_le]; exact Or.inl ha)
  have hy₄_lt5 : ∀ a < base + 5, y₄.mem a = x.mem a := fun a ha => by
    dsimp only [y₄, y₃, y₂, y₁, RData.write, RData.set]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hy_mem a (fun h => by linarith only [ha, h.1])
  have hhdr_z : RootHeaderValid U V w 0 0 0 base z.mem :=
    ⟨hhdr.fits_U, hhdr.pos_U, hhdr.pos_V,
      (hz_lt8 base (by omega)).trans ((hy₄_lt5 base (by omega)).trans hhdr.hdr_U),
      (hz_lt8 (base + 1) (by omega)).trans ((hy₄_lt5 (base + 1) (by omega)).trans hhdr.hdr_V),
      (hz_lt8 (base + 2) (by omega)).trans ((hy₄_lt5 (base + 2) (by omega)).trans hhdr.hdr_w),
      (hz_lt8 (base + 3) (by omega)).trans ((hy₄_lt5 (base + 3) (by omega)).trans hhdr.hdr_keyBits),
      (hz_lt8 (base + 4) (by omega)).trans ((hy₄_lt5 (base + 4) (by omega)).trans hhdr.hdr_valBits),
      (hz_lt8 (base + 5) (by omega)).trans (by
        dsimp only [y₄, y₃, y₂, RData.write, RData.set]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]),
      (hz_lt8 (base + 6) (by omega)).trans (by
        dsimp only [y₄, y₃, RData.write, RData.set]
        rw [Function.update_of_ne (by omega), Function.update_self]),
      (hz_lt8 (base + 7) (by omega)).trans (by
        dsimp only [y₄, RData.write, RData.set]; rw [Function.update_self])⟩
  have hoff_lin : off ≤ 1447 :=
    (offCompItems_le_linear hw hNU hhdr.fits_U).trans (by linarith only [hN4])
  have hiw_lin : iw ≤ 4 :=
    (compactedItemWords_le_linear (U := U) (V := V) (w := w) (N := N) (n := 1) hw hU.le hV).trans
      (by decide)
  have hc_sh : 4 * (x.frontier - (base + 8)) + 5 ≤ 5810 := by
    have hsub : x.frontier - (base + 8) ≤ off + iw := by
      rw [hfr_eq]
      exact (Nat.sub_le_sub_left (Nat.le_add_right base 8) _).trans_eq
        (by rw [Nat.add_assoc, Nat.add_sub_cancel_left])
    linarith only [hsub, hoff_lin, hiw_lin]
  have hex_tail :=
    hex_z0.seq_eq (hex_st5.seq_eq (hex_st6.seq_eq (hex_st7.seq_eq
      (hex_c8.seq_eq (hex_add.seq_eq (hex_sub.seq_eq
        (hex_sh.mono hc_sh (fun _ h => h))))))))
  refine ⟨z, _, hex_tail, by linarith only, compactedRep_empty hzb hzf hhdr_z, ?_,
    fun addr haddr => (hz_lt8 addr (by omega)).trans (hy₄_lt5 addr (by omega))⟩
  dsimp only [z, shrinkPost, y₇, RData.set]
  rw [Function.update_of_ne (mReg_ne (by decide)),
    Function.update_of_ne (mReg_ne (by decide)),
    Function.update_of_ne (mReg_ne (by decide)),
    Function.update_of_ne (mReg_ne (by decide)),
    Function.update_of_ne (mReg_ne (by decide))]
  exact hy₄_base

/-- **Deterministic Singleton Delete (`deleteLastOneCode_demonicExec`):**
From an active singleton epoch (`n = 1`, `EpochValid U 1 N`) at `base` with seed `θ`:
* when `(s_abs u).isSome` (`Function.update s_abs u none = Dictionary.empty U`), `deleteLastOneCode`
  collapses to the 8-word empty `CompactedRep U V w 0 0 0` in `≤ deleteLastOneCharge` steps;
* when `¬(s_abs u).isSome` (`Function.update s_abs u none = s_abs`), `deleteLastOneCode` preserves
  `CompactedSplitRep` with the **same** seed `θ` and unchanged `inEpochPotential` in
  `≤ deleteLastOneCharge` steps. -/
theorem deleteLastOneCode_demonicExec {U V w N n_init base : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} (u : Fin U) {x : RData rResize}
    (hx : x.Bounded w) (hev : EpochValid U 1 N)
    (hfr : x.frontier = base + compactedEpochWords U V w N 1)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N 1 n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base)
    (hu_reg : x.regs mArgU = u.val) :
    ∃ (z : RData rResize) (steps : ℕ),
      RDemonicExec w x.frontier deleteLastOneCode x steps (· = z) ∧
      z.Bounded w ∧
      z.regs mBase = base ∧
      (∀ addr < base, z.mem addr = x.mem addr) ∧
      (if (s_abs u).isSome then
        Function.update s_abs u none = Dictionary.empty U ∧
        CompactedRep U V w 0 0 0 base (Dictionary.empty U) z ∧
        steps ≤ deleteLastOneCharge
      else
        Function.update s_abs u none = s_abs ∧
        z.frontier = base + compactedEpochWords U V w N 1 ∧
        CompactedSplitRep base (base + offCompItems U w N) U V w N 1 n_init θ s_abs
          ⟨z.mem, z.frontier⟩ ∧
        inEpochPotential U w N base z = inEpochPotential U w N base x ∧
        steps ≤ deleteLastOneCharge) := by
  obtain ⟨hw, _, _⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  have hNU : N ≤ U := by rcases hev with ⟨h0, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  obtain ⟨s_fix, hinv, htot, hcpl⟩ := hsplit.coupled
  obtain ⟨hrec_val, _, hrec_surj⟩ := reconstructKeyAt_spec hsplit.vals_lt hNU hinv hcpl htot
  obtain ⟨hu₀_lt, hs₀, _⟩ := hrec_val 0 zero_lt_one
  set u₀ := reconstructKeyAt base (base + offCompItems U w N) U V w N 1 θ x.mem 0
  obtain ⟨y, steps_r, hex_r, hc_r, hyb, hyf, hy_fr_reg, hy_base, hy_argu, hy_u0, hy_mem⟩ :=
    deleteLastReadCode_exec hx hev hfr hsplit hbase
  have hf1 := one_le_migFactor
  by_cases hsome : (s_abs u).isSome
  · obtain ⟨d, hd, hd_eq⟩ := hrec_surj u hsome
    have hd0 : d = 0 := Nat.lt_one_iff.mp hd
    subst hd0
    change u₀ = u.val at hd_eq
    have hc_eq : (Cond.eq mU0 mArgU).Holds y.toData := by
      change y.regs mU0 = y.regs mArgU
      rw [hy_u0, hy_argu, hu_reg]; exact hd_eq
    obtain ⟨z, steps_h, hex_h, hc_h, hrep_z, hz_base, hbelow_z⟩ :=
      deleteLastHitTailCode_exec hev hfr hsplit.root_hdr hyb hyf hy_fr_reg hy_base hy_mem
    have hs_empty : Function.update s_abs u none = Dictionary.empty U := by
      funext k
      by_cases hku : k = u
      · subst hku; simp [Dictionary.empty]
      · rw [Function.update_of_ne hku]
        cases hk_eq : s_abs k with
        | none => rfl
        | some val =>
          obtain ⟨d', hd', hd'_eq⟩ := hrec_surj k (by rw [hk_eq]; simp)
          have hd'0 : d' = 0 := Nat.lt_one_iff.mp hd'
          subst hd'0
          exact absurd (Fin.ext (hd'_eq.symm.trans hd_eq)) hku
    refine ⟨z, _, hex_r.seq_eq (RDemonicExec.branch_pos hc_eq hex_h),
      hrep_z.bounded, hz_base, hbelow_z, ?_⟩
    rw [ite_eq_left hsome]
    refine ⟨hs_empty, hrep_z, ?_⟩
    unfold deleteLastOneCharge
    linarith only [hc_r, hc_h, hf1]
  · have hne_u : u₀ ≠ u.val := fun heq => by
      have hu_eq : u = ⟨u₀, hu₀_lt⟩ := Fin.ext heq.symm
      rw [hu_eq, hs₀] at hsome
      exact hsome rfl
    have hnc_eq : ¬(Cond.eq mU0 mArgU).Holds y.toData := by
      change y.regs mU0 ≠ y.regs mArgU
      rw [hy_u0, hy_argu, hu_reg]; exact hne_u
    have hex_nop := RDemonicExec.copy (B := .exact) (w := w) (L_peak := x.frontier)
      (d := mZero) (s := mZero) (x := y) hyf.le
    set z := y.set mZero (y.regs mZero)
    have hzb : z.Bounded w := hyb.set (hyb.regs_fits mZero)
    have hzf : z.frontier = x.frontier := hyf
    have hzm : z.mem = y.mem := rfl
    have hs_same : Function.update s_abs u none = s_abs := by
      funext k
      by_cases hku : k = u
      · subst hku; simp only [Function.update_self]
        cases hk_eq : s_abs k with
        | none => rfl
        | some _ => exact absurd (by rw [hk_eq]; simp) hsome
      · exact Function.update_of_ne hku _ _
    have hout_scr : ∀ a, (a < base + offScratch ∨ base + epochHdrWords ≤ a) → z.mem a = x.mem a :=
      fun a ha => hy_mem a (by unfold offScratch epochHdrWords at ha; omega)
    have hsplit_z : CompactedSplitRep base (base + offCompItems U w N) U V w N 1 n_init θ s_abs
        ⟨z.mem, z.frontier⟩ :=
      compactedSplitRep_of_scratch_mod hw hsplit hzf hout_scr
    have hpot_eq : inEpochPotential U w N base z = inEpochPotential U w N base x := by
      unfold inEpochPotential
      rw [compGmAt_eq_of_scratch_mod hw hout_scr]
    refine ⟨z, _, hex_r.seq_eq (RDemonicExec.branch_neg hnc_eq hex_nop),
      hzb, by simp [z, RData.set, hy_base],
      fun addr haddr => hy_mem addr (fun h => by linarith only [haddr, h.1]), ?_⟩
    rw [ite_eq_right hsome]
    refine ⟨hs_same, hzf.trans hfr, hsplit_z, hpot_eq, ?_⟩
    unfold deleteLastOneCharge
    linarith only [hc_r, hf1]

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
