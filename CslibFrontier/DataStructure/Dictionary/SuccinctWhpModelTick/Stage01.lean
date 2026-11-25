/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep
-- `import all`: reads private invariant-transfer helpers (`core_and_om_of_inLiveTree_eq`,
-- `step_of_inLiveTree_eq`) from `Common`.
import all CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.Common

/-!
# Epoch Rebuild Stages 0 and 1 (Flag Reset and Dirty-Bucket Collection)

Internal correctness proofs for `epochTickStage0` and `epochTickStage1`
[BenderFarachColtonKuszmaulKuszmaul2024].

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.epochTickStage0_spec`: Stage 0 preserves
  `CoreFastInv` and `OvermarsBucketInv` and restores `ValidEpochStage`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.epochTickStage1_spec`: Stage 1 preserves
  `CoreFastInv` and `OvermarsBucketInv` and restores `ValidEpochStage`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

/-- Stage-0 tick clears `rebQueued` and `rebDoneFlag` across `buf oldEp` slots. -/
theorem epochTickStage0_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hs0 : fs.rebStage = 0)
    (hpre : ValidEpochStagePreTick c U n_max θ fs) :
    let fs1 := epochTickStage0 fs
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = fs.epochClock := by
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_left hs0] at hpre
  obtain ⟨hsc_le, hzero0⟩ := hpre
  let oldTr := fs.buf fs.oldEp
  have hinL_eq : ∀ stg, (stg = 0 ∨ stg = 1) → ∀ (df : ℕ → ℕ) b,
      inLiveTree stg fs.oldEp (df b) = inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) := by
    intro stg hstg df b; funext st
    rcases hstg with rfl | rfl <;> simp [inLiveTree, hs0]
  have hbo_01 : ∀ stg, stg ≤ 3 →
      (if stg ≤ 3 then
        oldTr.itemAlloc ≤ 2 * sMaxWhp c n_max ∧
        oldTr.nodeAlloc ≤ 1 + cTabWhp c * oldTr.itemAlloc ∧
        ∃ oldMap,
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) oldTr oldMap ∧
          BufMapRel (numBucketsWhp n_max) (2 + fs.oldEp) fs.bktCount fs.locState
            (fs.rKeyAt c U n_max θ) oldMap
      else if stg = 4 then
        (∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b, fs.locState b loc ≠ 2 + fs.oldEp) ∧
        ClearableBufTrie oldTr ∧
        oldTr.nodeAlloc ≤ 1 + cTabWhp c * (2 * sMaxWhp c n_max)
      else
        (∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b, fs.locState b loc ≠ 2 + fs.oldEp) ∧
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) oldTr (fun _ => none) ∧
        oldTr.nodeAlloc = 1 ∧ oldTr.itemAlloc = 0) := by
    intro stg hle3
    have hbo := hc.bufOld_valid
    rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
    rw [ite_eq_left hle3]; exact hbo
  dsimp only [epochTickStage0]
  by_cases hlt : fs.stageCursor < oldTr.itemAlloc
  · rw [ite_eq_left hlt]
    cases hchk : bufCheckSlot oldTr fs.stageCursor with
    | some bloc =>
      rcases bloc with ⟨b₀, loc₀⟩
      dsimp only
      have hzero_next : ∀ id < fs.stageCursor + 1, ∀ b' loc',
          bufCheckSlot oldTr id = some (b', loc') →
          Function.update fs.rebQueued b₀ 0 b' = 0 ∧
          Function.update fs.rebDoneFlag b₀ 0 b' = 0 := by
        intro id hid b' loc' hc'
        by_cases hbb : b' = b₀
        · subst hbb; simp
        · rw [Function.update_of_ne hbb, Function.update_of_ne hbb]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
          · exact hzero0 id hid' b' loc' hc'
          · rw [hchk] at hc'
            injection hc' with hp; injection hp with hb_eq _
            exact absurd hb_eq.symm hbb
      by_cases hdone : oldTr.itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
          (show 1 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun b _ loc _ => congrFun (hinL_eq 1 (Or.inr rfl) _ b) _)
          (hbo_01 1 (by decide)) ?_ rfl
        dsimp only [ValidEpochStage]
        simp only [show ¬(1 = 0) by decide, ↓reduceIte]
        exact ⟨Nat.zero_le _, le_rfl, fun _ h => absurd h (Nat.not_lt_zero _),
          fun _ h => absurd h (Nat.not_lt_zero _),
          fun id hid b' loc' hc' => Or.inl (hzero_next id (hid.trans_le hdone) b' loc' hc'),
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · rw [ite_eq_right hdone]
        refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
          hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun b _ loc _ => congrFun (hinL_eq fs.rebStage (Or.inl hs0) _ b) _)
          (hbo_01 fs.rebStage (by omega)) ?_ rfl
        dsimp only [ValidEpochStage]; rw [ite_eq_left hs0]
        exact ⟨Nat.le_of_lt (Nat.lt_of_not_le hdone), hzero_next⟩
    | none =>
      dsimp only
      have hzero_next : ∀ id < fs.stageCursor + 1, ∀ b' loc',
          bufCheckSlot oldTr id = some (b', loc') →
          fs.rebQueued b' = 0 ∧ fs.rebDoneFlag b' = 0 := by
        intro id hid b' loc' hc'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
        · exact hzero0 id hid' b' loc' hc'
        · rw [hchk] at hc'; cases hc'
      by_cases hdone : oldTr.itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
          (show 1 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun b _ loc _ => congrFun (hinL_eq 1 (Or.inr rfl) _ b) _)
          (hbo_01 1 (by decide)) ?_ rfl
        dsimp only [ValidEpochStage]
        simp only [show ¬(1 = 0) by decide, ↓reduceIte]
        exact ⟨Nat.zero_le _, le_rfl, fun _ h => absurd h (Nat.not_lt_zero _),
          fun _ h => absurd h (Nat.not_lt_zero _),
          fun id hid b' loc' hc' => Or.inl (hzero_next id (hid.trans_le hdone) b' loc' hc'),
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · rw [ite_eq_right hdone]
        refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
          hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun _ _ _ _ => rfl) (hbo_01 fs.rebStage (by omega)) ?_ rfl
        dsimp only [ValidEpochStage]; rw [ite_eq_left hs0]
        exact ⟨Nat.le_of_lt (Nat.lt_of_not_le hdone), hzero_next⟩
  · rw [ite_eq_right hlt]
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      (show 1 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun b _ loc _ => congrFun (hinL_eq 1 (Or.inr rfl) _ b) _)
      (hbo_01 1 (by decide)) ?_ rfl
    dsimp only [ValidEpochStage]
    simp only [show ¬(1 = 0) by decide, ↓reduceIte]
    exact ⟨Nat.zero_le _, le_rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _),
      fun id hid b' loc' hc' =>
        Or.inl (hzero0 id (hid.trans_le (Nat.le_of_not_lt hlt)) b' loc' hc'),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩

private theorem epochTickStage1Finish_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {s : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ s dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ s b)
    (hs1 : s.rebStage = 1)
    (hdc_le : s.dirtyCount ≤ (s.buf s.oldEp).itemAlloc)
    (hd_props : ∀ j < s.dirtyCount,
      s.dirtyBuckets j < numBucketsWhp n_max ∧
      s.rebQueued (s.dirtyBuckets j) = 1 ∧
      s.rebDoneFlag (s.dirtyBuckets j) = 0)
    (hd_inj : ∀ j₁ < s.dirtyCount, ∀ j₂ < s.dirtyCount,
      s.dirtyBuckets j₁ = s.dirtyBuckets j₂ → j₁ = j₂)
    (hall_queued : ∀ id < (s.buf s.oldEp).itemAlloc, ∀ b loc,
      bufCheckSlot (s.buf s.oldEp) id = some (b, loc) →
        ∃ j < s.dirtyCount, s.dirtyBuckets j = b) :
    let fs1 := epochTickStage1Finish s
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = s.epochClock := by
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : s.rebStage ≤ 3)] at hbo
  obtain ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩ := hbo
  have hold_dirty : ∀ b < numBucketsWhp n_max, ∀ loc < s.bktCount b,
      s.locState b loc = 2 + s.oldEp → ∃ j < s.dirtyCount, s.dirtyBuckets j = b := by
    intro b hb loc hloc hst
    have hm_some : oldMap (s.rKeyAt c U n_max θ b loc) = some (b, loc) :=
      (hrel_o.2 _ b loc).mpr ⟨hb, hloc, hst, rfl⟩
    obtain ⟨id, hid, hchk⟩ := hv_o.exists_checkSlot_of_map_some hm_some
    exact hall_queued id hid b loc hchk
  dsimp only [epochTickStage1Finish]
  by_cases hdc0 : s.dirtyCount = 0
  · rw [ite_eq_left hdc0]
    have hno_old : ∀ b < numBucketsWhp n_max, ∀ loc < s.bktCount b,
        s.locState b loc ≠ 2 + s.oldEp := by
      intro b hb loc hloc hst
      obtain ⟨j, hj, _⟩ := hold_dirty b hb loc hloc hst
      omega
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      (show 3 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun b hb loc hloc => by
        have hne := hno_old b hb loc hloc
        change inLiveTree 3 s.oldEp (s.rebDoneFlag b) (s.locState b loc) =
          inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc)
        simp [inLiveTree, hs1, hne])
      (by
        dsimp only [FastState.oldEp]
        simp only [show (3 : ℕ) ≤ 3 by decide, ↓reduceIte]
        exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩) ?_ rfl
    dsimp only [ValidEpochStage]
    simp only [show ¬(3 = 0) by decide, show ¬(3 = 1) by decide, show ¬(3 = 2) by decide,
      ↓reduceIte]
    exact ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · rw [ite_eq_right hdc0]
    have hdc_pos : 0 < s.dirtyCount := Nat.pos_of_ne_zero hdc0
    set b0 := s.dirtyBuckets 0
    have hb0 : b0 < numBucketsWhp n_max := (hd_props 0 hdc_pos).1
    set rIdx0 := s.rebSliceIdx b0
    obtain ⟨hlr0, hor0, hne0⟩ := hc.roles_valid b0 hb0
    have hrr0 : s.rebRole b0 < 3 ∧ s.rebRole b0 ≠ s.liveRole b0 ∧
        s.rebRole b0 ≠ s.overmarsRole b0 := by
      dsimp only [FastState.rebRole]; omega
    have hne_live : ∀ b < numBucketsWhp n_max, s.liveSliceIdx b ≠ rIdx0 := by
      intro b hb; dsimp only [FastState.liveSliceIdx, rIdx0, FastState.rebSliceIdx]
      by_cases hbb : b = b0
      · subst hbb; omega
      · intro heq; exact hbb (sliceIdx_inj (hc.roles_valid b hb).1 hrr0.1 heq).1
    have hne_om : ∀ b < numBucketsWhp n_max, s.overmarsSliceIdx b ≠ rIdx0 := by
      intro b hb; dsimp only [FastState.overmarsSliceIdx, rIdx0, FastState.rebSliceIdx]
      by_cases hbb : b = b0
      · subst hbb; omega
      · intro heq; exact hbb (sliceIdx_inj (hc.roles_valid b hb).2.1 hrr0.1 heq).1
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      (show 2 ≤ 5 by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
      (fun b hb => Function.update_of_ne (hne_live b hb) _ _)
      (fun b hb => Function.update_of_ne (hne_om b hb) _ _)
      (fun b hb loc hloc => by
        change inLiveTree 2 s.oldEp (s.rebDoneFlag b) (s.locState b loc) =
          inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc)
        by_cases hst : s.locState b loc = 2 + s.oldEp
        · obtain ⟨j, hj, hdb_eq⟩ := hold_dirty b hb loc hloc hst
          have hdf0 : s.rebDoneFlag b = 0 := hdb_eq ▸ (hd_props j hj).2.2
          simp [inLiveTree, hs1, hst, hdf0]
        · simp [inLiveTree, hs1, hst])
      (by
        dsimp only [FastState.oldEp]
        simp only [show (2 : ℕ) ≤ 3 by decide, ↓reduceIte]
        exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩) ?_ rfl
    dsimp only [ValidEpochStage]
    simp only [show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte]
    refine ⟨hdc_le.trans hia_o, hdc_pos, fun j hj => (hd_props j hj).1, hd_inj,
      fun j hj => ⟨fun h => absurd h (Nat.not_lt_zero _), fun _ => (hd_props j hj).2.2⟩,
      hold_dirty, fun _ => ⟨Or.inl ⟨trivial, trivial⟩,
        fun _ hl => absurd (hl.trans_le (Nat.min_le_right _ _)) (Nat.not_lt_zero _),
        fun _ => none, ?_,
        by
          rw [Nat.min_zero]
          exact SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    change ValidWhpSlice n_max 0
      (Function.update s.slices rIdx0 (resetBTreeSlice (s.slices rIdx0)) rIdx0)
      (fun _ => none)
    rw [Function.update_self]
    exact validWhpSlice_zero _ 0 _

/-- Stage-1 tick collects distinct dirty buckets from `buf oldEp` into `dirtyBuckets`. -/
theorem epochTickStage1_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hs1 : fs.rebStage = 1)
    (hpre : ValidEpochStagePreTick c U n_max θ fs) :
    let fs1 := epochTickStage1 fs
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = fs.epochClock := by
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)), ite_eq_left hs1] at hpre
  rcases hpre with ⟨hsc_le, hdc_sc, hd_props, hd_inj, hall_or, hlt_sc⟩
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩ := hbo
  let oldTr := fs.buf fs.oldEp
  dsimp only [epochTickStage1]
  by_cases hlt : fs.stageCursor < oldTr.itemAlloc
  · rw [ite_eq_left hlt]
    let nextCur := fs.stageCursor + 1
    set fs' : FastState :=
      match bufCheckSlot oldTr fs.stageCursor with
      | some (b, _) =>
        if fs.rebQueued b = 0 then
          { fs with
            rebQueued := Function.update fs.rebQueued b 1
            dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b
            dirtyCount := fs.dirtyCount + 1
            stageCursor := nextCur }
        else { fs with stageCursor := nextCur }
      | none => { fs with stageCursor := nextCur }
    have hstep :
        CoreFastInv c U V n_max θ fs' dict ∧
        (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b) ∧
        fs'.rebStage = 1 ∧
        fs'.epochClock = fs.epochClock ∧
        fs'.buf fs'.oldEp = oldTr ∧
        fs'.stageCursor = nextCur ∧
        fs'.dirtyCount ≤ nextCur ∧
        (∀ j < fs'.dirtyCount,
          fs'.dirtyBuckets j < numBucketsWhp n_max ∧
          fs'.rebQueued (fs'.dirtyBuckets j) = 1 ∧
          fs'.rebDoneFlag (fs'.dirtyBuckets j) = 0) ∧
        (∀ j₁ < fs'.dirtyCount, ∀ j₂ < fs'.dirtyCount,
          fs'.dirtyBuckets j₁ = fs'.dirtyBuckets j₂ → j₁ = j₂) ∧
        (∀ id < oldTr.itemAlloc, ∀ b loc,
          bufCheckSlot oldTr id = some (b, loc) →
            (fs'.rebQueued b = 0 ∧ fs'.rebDoneFlag b = 0) ∨
            ∃ j < fs'.dirtyCount, fs'.dirtyBuckets j = b) ∧
        (∀ id < nextCur, ∀ b loc,
          bufCheckSlot oldTr id = some (b, loc) →
            ∃ j < fs'.dirtyCount, fs'.dirtyBuckets j = b) := by
      cases hchk : bufCheckSlot oldTr fs.stageCursor with
      | some bloc =>
        rcases bloc with ⟨b₀, loc₀⟩
        obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
        have hb₀ : b₀ < numBucketsWhp n_max := ((hrel_o.2 k b₀ loc₀).mp hmk).1
        by_cases hq0 : fs.rebQueued b₀ = 0
        · have hfs'_eq : fs' =
              { fs with
                rebQueued := Function.update fs.rebQueued b₀ 1
                dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b₀
                dirtyCount := fs.dirtyCount + 1
                stageCursor := nextCur } := by
            dsimp only [fs']; rw [hchk]; exact ite_eq_left hq0
          have hdf₀ : fs.rebDoneFlag b₀ = 0 := by
            rcases hall_or fs.stageCursor hlt b₀ loc₀ hchk with ⟨_, hd⟩ | ⟨j, hj, hdb⟩
            · exact hd
            · have := (hd_props j hj).2.1; rw [hdb, hq0] at this; omega
          have hne_prev : ∀ j < fs.dirtyCount, fs.dirtyBuckets j ≠ b₀ := by
            intro j hj heq
            have := (hd_props j hj).2.1; rw [heq, hq0] at this; omega
          rw [hfs'_eq]
          dsimp only
          obtain ⟨hc', hom'⟩ := core_and_om_of_inLiveTree_eq
            { fs with
              rebQueued := Function.update fs.rebQueued b₀ 1
              dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b₀
              dirtyCount := fs.dirtyCount + 1
              stageCursor := nextCur }
            hc hom rfl hc.epochClock_lt
            hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
            (by dsimp only [FastState.oldEp]; rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]
                exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩)
          refine ⟨hc', hom', hs1, rfl, rfl, rfl, by omega, ?_, ?_, ?_, ?_⟩
          · intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
            · rw [Function.update_of_ne (by omega : j ≠ fs.dirtyCount),
                Function.update_of_ne (hne_prev j hj')]
              exact hd_props j hj'
            · simp [hb₀, hdf₀]
          · intro j₁ hj₁ j₂ hj₂ heq
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj₁ with hj₁' | rfl <;>
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj₂ with hj₂' | rfl
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at heq
              exact hd_inj j₁ hj₁' j₂ hj₂' heq
            · rw [Function.update_of_ne (by omega), Function.update_self] at heq
              exact absurd heq (hne_prev j₁ hj₁')
            · rw [Function.update_self, Function.update_of_ne (by omega)] at heq
              exact absurd heq.symm (hne_prev j₂ hj₂')
            · rfl
          · intro id hid b' loc' hc'
            by_cases hbb : b' = b₀
            · subst hbb; right; exact ⟨fs.dirtyCount, Nat.lt_succ_self _, by simp⟩
            · rw [Function.update_of_ne hbb]
              rcases hall_or id hid b' loc' hc' with hleft | ⟨j, hj, hdb⟩
              · exact Or.inl hleft
              · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, by
                  rw [Function.update_of_ne (by omega)]; exact hdb⟩
          · intro id hid b' loc' hc'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
            · obtain ⟨j, hj, hdb⟩ := hlt_sc id hid' b' loc' hc'
              exact ⟨j, Nat.lt_succ_of_lt hj, by
                rw [Function.update_of_ne (by omega)]; exact hdb⟩
            · rw [hchk] at hc'; injection hc' with hp; injection hp with hbb _
              exact ⟨fs.dirtyCount, Nat.lt_succ_self _, by simp [hbb]⟩
        · have hfs'_eq : fs' = { fs with stageCursor := nextCur } := by
            dsimp only [fs']; rw [hchk]; exact ite_eq_right hq0
          have hex₀ : ∃ j < fs.dirtyCount, fs.dirtyBuckets j = b₀ := by
            rcases hall_or fs.stageCursor hlt b₀ loc₀ hchk with ⟨hq, _⟩ | hex
            · exact absurd hq hq0
            · exact hex
          rw [hfs'_eq]
          dsimp only
          obtain ⟨hc', hom'⟩ := core_and_om_of_inLiveTree_eq { fs with stageCursor := nextCur }
            hc hom rfl hc.epochClock_lt
            hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
            (by dsimp only [FastState.oldEp]; rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]
                exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩)
          refine ⟨hc', hom', hs1, rfl, rfl, rfl, by omega, hd_props, hd_inj, hall_or, ?_⟩
          intro id hid b' loc' hc'
          rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
          · exact hlt_sc id hid' b' loc' hc'
          · rw [hchk] at hc'; injection hc' with hp; injection hp with hbb _
            rwa [← hbb]
      | none =>
        have hfs'_eq : fs' = { fs with stageCursor := nextCur } := by
          dsimp only [fs']; rw [hchk]
        rw [hfs'_eq]
        dsimp only
        obtain ⟨hc', hom'⟩ := core_and_om_of_inLiveTree_eq { fs with stageCursor := nextCur }
          hc hom rfl hc.epochClock_lt
          hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
          (by dsimp only [FastState.oldEp]; rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]
              exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩)
        refine ⟨hc', hom', hs1, rfl, rfl, rfl, by omega, hd_props, hd_inj, hall_or, ?_⟩
        intro id hid b' loc' hc'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
        · exact hlt_sc id hid' b' loc' hc'
        · rw [hchk] at hc'; cases hc'
    rcases hstep with ⟨hc', hom', hs1', hclk', hbuf', hsc', hdc', hd_p', hd_i', hall_o', hlt_s'⟩
    by_cases hdone : oldTr.itemAlloc ≤ nextCur
    · rw [ite_eq_left hdone]
      obtain ⟨hcF, homF, hstF, hclkF⟩ := epochTickStage1Finish_spec hc' hom' hs1'
        (by rw [hbuf']; exact hdc'.trans (by omega))
        hd_p' hd_i'
        (fun id hid b loc hchk => hlt_s' id (by rw [hbuf'] at hid; omega) b loc (hbuf' ▸ hchk))
      exact ⟨hcF, homF, hstF, hclkF.trans hclk'⟩
    · rw [ite_eq_right hdone]
      refine ⟨hc', hom', ?_, hclk'⟩
      change ValidEpochStage c U n_max θ fs'
      dsimp only [ValidEpochStage]
      rw [ite_eq_right (by omega : ¬(fs'.rebStage = 0)), ite_eq_left hs1', hbuf', hsc']
      exact ⟨by omega, hdc', hd_p', hd_i', hall_o', hlt_s'⟩
  · rw [ite_eq_right hlt]
    exact epochTickStage1Finish_spec hc hom hs1 (hdc_sc.trans hsc_le) hd_props hd_inj
      (fun id hid b loc hchk => hlt_sc id (hid.trans_le (Nat.le_of_not_lt hlt)) b loc hchk)


end Cslib.DataStructure.Dictionary.SuccinctWhp

end
