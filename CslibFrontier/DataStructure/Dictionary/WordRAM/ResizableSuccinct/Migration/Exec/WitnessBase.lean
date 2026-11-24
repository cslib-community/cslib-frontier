/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.StreamStep

/-!
# Retained `RealizesBounded` Witnesses and Scratch Budget for Epoch Migration

Internal module retaining the `RealizesBounded.Witness` instances and combined scratch-register
budget `scratchMigrate` shared privately across `Migration.Exec` submodules (never re-exported
publicly by `CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec`).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM.Realization

/-- Retained `RealizesBounded` witness for `computeTargetCapProg`. -/
noncomputable def wTargetCap :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_computeTargetCap
/-- Retained `RealizesBounded` witness for `writeEpochParamsGenProg`. -/
noncomputable def wWriteParams :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_writeEpochParamsGen
/-- Retained `RealizesBounded` witness for `copyRightwardProg`. -/
noncomputable def wCopyRight :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_copyRightward
/-- Retained `RealizesBounded` witness for `copyLeftwardProg`. -/
noncomputable def wCopyLeft :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_copyLeftward
/-- Retained `RealizesBounded` witness for `initNewEpochMetaProg`. -/
noncomputable def wInitNewMeta :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_initNewEpochMeta
/-- Retained `RealizesBounded` witness for `readOldItemKeyValGenProg`. -/
noncomputable def wReadOldKV :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_readOldItemKeyValGen
/-- Retained `RealizesBounded` witness for `streamInsertFreshGenProg`. -/
noncomputable def wStreamIns :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_streamInsertFreshGen
/-- Retained `RealizesBounded` witness for `streamAllItemsProg`. -/
noncomputable def wStreamAll :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_streamAllItems

/-- Combined `RealizesBounded` scratch-register budget above register `160` across all epoch
migration subroutines. -/
noncomputable def scratchMigrate : ℕ :=
  max (1 + wItemWords.scratchSize + 1) <|
  max (1 + wTargetCap.scratchSize + 1) <|
  max (2 + wWriteParams.scratchSize + 1) <|
  max (0 + wCopyRight.scratchSize + 1) <|
  max (0 + wCopyLeft.scratchSize + 1) <|
  max (0 + wInitNewMeta.scratchSize + 1) <|
  max (2 + wReadOldKV.scratchSize + 1) <|
  max (0 + wStreamIns.scratchSize + 1)
      (1 + wStreamAll.scratchSize + 1)

theorem scratch_wItemWords_le : 1 + wItemWords.scratchSize + 1 ≤ scratchMigrate :=
  le_max_left _ _
theorem scratch_wTargetCap_le : 1 + wTargetCap.scratchSize + 1 ≤ scratchMigrate :=
  le_max_of_le_right (le_max_left _ _)
theorem scratch_wWriteParams_le : 2 + wWriteParams.scratchSize + 1 ≤ scratchMigrate :=
  le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
theorem scratch_wCopyRight_le : 0 + wCopyRight.scratchSize + 1 ≤ scratchMigrate :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
theorem scratch_wCopyLeft_le : 0 + wCopyLeft.scratchSize + 1 ≤ scratchMigrate :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_left _ _))))
theorem scratch_wInitNewMeta_le : 0 + wInitNewMeta.scratchSize + 1 ≤ scratchMigrate :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))
theorem scratch_wReadOldKV_le : 2 + wReadOldKV.scratchSize + 1 ≤ scratchMigrate :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))
theorem scratch_wStreamIns_le : 0 + wStreamIns.scratchSize + 1 ≤ scratchMigrate :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))
theorem scratch_wStreamAll_le : 1 + wStreamAll.scratchSize + 1 ≤ scratchMigrate :=
  le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))))

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
