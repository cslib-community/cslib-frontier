/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.WitnessBase

/-!
# Register Budget `rResize`, `epochEmb`, ABI Registers, and Migration Cost Factors

Parameter-free register space `rResize`, injective embedding `epochEmb : Fin rEpoch → Fin rResize`,
named register aliases `mBase..mCnt`, and parameter-free exchange/linear cost factors
`migFactor` and `migLinearFactor` for epoch-boundary transitions on the Resizable Word RAM.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.rResize`, `epochEmb`, `mReg`:
  parameter-free register budget, `rEpoch` embedding, and fixed register bank `0..159`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.mBase`, `mTag`, `mArgU`, `mArgV`,
  `mOutTag`, `mOutVal`, `mK`, `mRes`, `mCur`, `mIdx`, `mZero`, `mOne`, `mCnt`: caller-visible ABI
  and shared control registers.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.migFactor`, `migLinearFactor`:
  parameter-free exchange and per-item migration cost factors.

## Main results

* `rEpoch_le_rResize`, `le_rResize_160`, `epochEmb_injective`, `mReg_ne`, `mGrow_nodup`:
  register-space bounds, injectivity, and distinctness of `growZeroCode` registers.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

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


theorem mReg_ne {i j : Fin 160} (h : i ≠ j) : mReg i ≠ mReg j :=
  fun heq => h (mReg_injective heq)

/-- Persistent base-address register `0` (`= epochEmb rBase`). -/
noncomputable abbrev mBase : Fin rResize := mReg 0

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

@[simp] theorem epochEmb_rBase : epochEmb rBase = mBase := Fin.ext (by simp)
@[simp] theorem epochEmb_rTag : epochEmb rTag = mTag := Fin.ext (by simp)
@[simp] theorem epochEmb_rArgU : epochEmb rArgU = mArgU := Fin.ext (by simp)
@[simp] theorem epochEmb_rArgV : epochEmb rArgV = mArgV := Fin.ext (by simp)
@[simp] theorem epochEmb_rOutTag : epochEmb rOutTag = mOutTag := Fin.ext (by simp)
@[simp] theorem epochEmb_rOutVal : epochEmb rOutVal = mOutVal := Fin.ext (by simp)

theorem mGrow_nodup : ([mK, mRes, mCur, mIdx, mZero, mOne] : List (Fin rResize)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
    mK, mRes, mCur, mIdx, mZero, mOne, mReg_inj]
  decide

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

/-- Parameter-free linear instruction factor `120000 * migFactor` per migrated item (`1 ≤ n`),
covering `migrateSetupCode`, `resampleHashCode`, `migrateFinishCode`, and the post-migration
`inEpochPotential` of the rebuilt epoch. -/
@[expose]
noncomputable def migLinearFactor : ℕ :=
  120000 * migFactor

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
