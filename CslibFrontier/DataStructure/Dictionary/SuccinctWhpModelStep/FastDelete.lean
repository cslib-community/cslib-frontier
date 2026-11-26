/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.Invariants
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.Overmars
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.DeleteLast
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.DeleteReloc

/-!
# Fast-Mode Deletion Refinement (`ValidFastState.fastDelete_spec`)

This module combines `fastFindLoc_spec`, `fastDelete_afterDel_last_spec`,
`fastDelete_afterDel_reloc_spec`, and `overmarsStep_spec` to establish top-level fast-mode deletion
refinement `ValidFastState.fastDelete_spec`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidFastState.fastDelete_spec`: fast-mode deletion
  refines `Dynamic.step dict (.delete u)` and preserves `CoreFastInv`, `OvermarsBucketInv`, and
  `ValidEpochStagePreTick`.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient

/-- `fastDelete` refines `Dynamic.step dict (.delete u)` and yields `CoreFastInv`,
`OvermarsBucketInv` on all buckets, and `ValidEpochStagePreTick` (ready for `epochTick`). -/
theorem ValidFastState.fastDelete_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict) (u : Fin U) :
    let fs' := fastDelete c U n_max θ fs u
    CoreFastInv c U V n_max θ fs' (Dynamic.step dict (.delete u)).1 ∧
    (∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b') ∧
    ValidEpochStagePreTick c U n_max θ fs' ∧
    fs'.epochClock = fs.epochClock := by
  have hfl := hv.fastFindLoc_spec u
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  dsimp only [fastDelete, Dynamic.step]
  cases hfind : fastFindLoc c U n_max θ fs u with
  | none =>
    rw [hfind] at hfl
    rw [Function.update_eq_self_iff.mpr hfl.symm]
    obtain ⟨hc', hom', _, hpre', _, hclk', _, _⟩ := overmarsStep_spec hv.toCore hb
      (fun b' hb' _ => hv.overmars_valid b' hb') (hv.overmars_valid b hb).toPre
    exact ⟨hc', hom', hpre' hv.stage_valid.toPreTick, hclk'⟩
  | some loc_del =>
    rw [hfind] at hfl
    dsimp only
    by_cases hlt : loc_del < fs.bktCount b - 1
    · rw [ite_eq_left hlt]
      obtain ⟨hcA, homA, hpreB, hpreA⟩ := fastDelete_afterDel_reloc_spec hv u hfl.1 hfl.2 hlt
      obtain ⟨hc', hom', _, hpre', _, hclk', _, _⟩ := overmarsStep_spec hcA hb homA hpreB
      exact ⟨hc', hom', hpre' hpreA, hclk'⟩
    · rw [ite_eq_right hlt]
      obtain ⟨hcA, homA, hpreB, hpreA⟩ := fastDelete_afterDel_last_spec hv u hfl.1 hfl.2 hlt
      obtain ⟨hc', hom', _, hpre', _, hclk', _, _⟩ := overmarsStep_spec hcA hb homA hpreB
      exact ⟨hc', hom', hpre' hpreA, hclk'⟩

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
