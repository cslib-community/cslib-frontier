/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick
import Mathlib.Tactic.Ring

/-!
# Bucket Bijection and Rebuild/Overmars Metadata Lemmas for `SuccinctWhpFastProb`

Internal cardinality, `rebScanSteps`, `ClearableBufTrie`, `overmarsStep`, and `bufDelete` helper
lemmas used across the `SuccinctWhpFastProb` proof submodules (not re-exported by
`SuccinctWhpFastProb`).
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset

/-- Helper: every active coordinate `(b, loc)` (`b < M`, `loc < fs.bktCount b`) in `CoreFastInv`
yields a key `u : Fin U` in `Dictionary.dom dict` with bucket `b` and quotient
`fs.quotArr (fs.physSlot n_max b loc)`. -/
theorem CoreFastInv.mem_dom_of_loc {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    {b loc : ℕ} (hb : b < numBucketsWhp n_max) (hloc : loc < fs.bktCount b) :
    let u : Fin U := ⟨fs.keyValAt c U n_max θ.1 b loc, (hc.active_item b hb loc hloc).1⟩
    u ∈ Dictionary.dom dict ∧
    feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b := by
  obtain ⟨hkv_lt, hfb, hq_eq, _⟩ := hc.active_item b hb loc hloc
  let u : Fin U := ⟨fs.keyValAt c U n_max θ.1 b loc, hkv_lt⟩
  refine ⟨Dictionary.mem_dom_iff.mpr ⟨fs.valArr (fs.physSlot n_max b loc), ?_⟩, hfb⟩
  exact ((hc.dict_map u).2 _).mpr ⟨loc, hfb.symm ▸ hloc, hfb.symm ▸ hq_eq.symm, hfb.symm ▸ rfl⟩

/-- In any `CoreFastInv` state, `fs.bktCount b` equals the exact number of keys in
`Dictionary.dom dict` hashing to Feistel bucket `b`. -/
theorem CoreFastInv.bktCount_eq_card_filter {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    {b : ℕ} (hb : b < numBucketsWhp n_max) :
    fs.bktCount b =
      #((Dictionary.dom dict).filter
        fun u => feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b) := by
  classical
  let S := (Dictionary.dom dict).filter
    fun u => feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b
  let toKey : (loc : Fin (fs.bktCount b)) → Fin U :=
    fun loc => ⟨fs.keyValAt c U n_max θ.1 b loc.val, (hc.active_item b hb loc.val loc.isLt).1⟩
  have hmem (loc : Fin (fs.bktCount b)) : toKey loc ∈ S :=
    mem_filter.mpr (hc.mem_dom_of_loc hb loc.isLt)
  have hinj : Function.Injective toKey := fun l₁ l₂ heq =>
    Fin.ext (hc.quot_inj b hb l₁.val l₁.isLt l₂.val l₂.isLt
      ((hc.active_item b hb l₁.val l₁.isLt).2.2.1.symm.trans
        ((show fs.keyValAt c U n_max θ.1 b l₁.val = _ from congrArg Fin.val heq) ▸
          (hc.active_item b hb l₂.val l₂.isLt).2.2.1)))
  have hsurj : ∀ u ∈ S, ∃ loc : Fin (fs.bktCount b), toKey loc = u := by
    intro u hu
    rw [mem_filter, Dictionary.mem_dom_iff] at hu
    obtain ⟨⟨v, hv⟩, hfb⟩ := hu
    obtain ⟨loc, hloc, hq_loc, _⟩ := ((hc.dict_map u).2 v).mp hv
    rw [hfb] at hloc hq_loc
    refine ⟨⟨loc, hloc⟩, Fin.ext ?_⟩
    dsimp only [toKey, FastState.keyValAt]
    rw [hq_loc, ← hfb]
    exact feistelReconstruct_feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  exact (by simp : fs.bktCount b = #(univ : Finset (Fin (fs.bktCount b)))).trans
    (Finset.card_bij (fun loc _ => toKey loc) (fun loc _ => hmem loc)
      (fun _ _ _ _ h => hinj h) fun u hu => (hsurj u hu).elim fun loc hl => ⟨loc, mem_univ loc, hl⟩)

/-- When `fs.fpAt c U n_max θ fs.rebCandSalt b` is injective on all active Stage-2 coordinates of
bucket `b`, `rebScanSteps` never sets `rebCollision` to non-zero. -/
theorem rebScanSteps_rebCollision_eq_zero_of_inj {c U n_max b : ℕ}
    (hth : whpThreshold c ≤ n_max)
    (θ : SeedWhp c U n_max) (rem : ℕ) (fs : FastState)
    (hcoll0 : fs.rebCollision = 0)
    (hcnt_le : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12)
    (hins_ub : fs.rebInsCount + rem ≤ 8 * (slabScale n_max) ^ 12)
    (hinj_all : ∀ l₁ < fs.bktCount b, ∀ l₂ < fs.bktCount b,
      (fs.locState b l₁ = 1 ∨ fs.locState b l₁ = 2 + fs.oldEp) →
      (fs.locState b l₂ = 1 ∨ fs.locState b l₂ = 2 + fs.oldEp) →
      fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fs.fpAt c U n_max θ fs.rebCandSalt b l₂ →
      l₁ = l₂)
    (hreb0 : ∃ rebMap,
      ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rebMap ∧
      SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b)
        (fun loc => fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp)
        (min (fs.bktCount b) fs.rebScanCursor) rebMap) :
    (rebScanSteps c U n_max θ b rem fs).rebCollision = 0 := by
  induction rem generalizing fs with
  | zero => exact hcoll0
  | succ rem ih =>
    obtain ⟨rm0, hvr0, hrr0⟩ := hreb0
    dsimp only [rebScanSteps]
    rw [ite_eq_right (not_not.mpr hcoll0)]
    set cur := fs.rebScanCursor
    set rIdx := fs.rebSliceIdx b
    by_cases hact : cur < fs.bktCount b ∧ (fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp)
    · rw [ite_eq_left hact]
      set fp := fs.fpAt c U n_max θ fs.rebCandSalt b cur
      have hfp_lt : fp < 2 ^ fpBitsWhp n_max := by
        dsimp only [fp, FastState.fpAt]
        split_ifs with hs hu
        exacts [fpHash_lt c U n_max θ.2 ⟨_, hs⟩ ⟨_, hu⟩, Nat.two_pow_pos _, Nat.two_pow_pos _]
      cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices rIdx) fp with
      | some prev_loc =>
        exfalso
        rw [hvr0.lookup_eq hth (by omega) hfp_lt] at hlk
        obtain ⟨hprev_min, hp_prev, hfp_prev⟩ := (hrr0.2 fp prev_loc).mp hlk
        have heq := hinj_all prev_loc (hprev_min.trans_le (Nat.min_le_left _ _)) cur hact.1
          hp_prev hact.2 hfp_prev
        exact (hprev_min.trans_le (Nat.min_le_right _ _)).ne heq
      | none =>
        dsimp only
        have hcur_val : cur < 2 ^ valLaneBitsWhp n_max := by
          have : 2 ^ valLaneBitsWhp n_max = 256 * (slabScale n_max) ^ 12 := by
            unfold valLaneBitsWhp slabScale
            rw [Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm _ 12]; ring
          omega
        have hins := hvr0.insert_spec hth (by omega) hfp_lt hcur_val
        set sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices rIdx) fp cur
        let fs1 : FastState :=
          { fs with
            slices := Function.update fs.slices rIdx sl'
            rebScanCursor := cur + 1
            rebInsCount := fs.rebInsCount + 1 }
        refine ih fs1 hcoll0 hcnt_le (by dsimp only [fs1]; omega) hinj_all
          ⟨Function.update rm0 fp (some cur), ?_, ?_⟩
        · change ValidWhpSlice n_max (fs.rebInsCount + 1)
            (Function.update fs.slices rIdx sl' rIdx) _
          rw [Function.update_self]; exact hins.2
        · rw [Nat.min_eq_right hact.1.le] at hrr0
          change SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b) _
            (min (fs.bktCount b) (cur + 1)) _
          rw [Nat.min_eq_right (Nat.succ_le_of_lt hact.1)]
          exact SliceMapRel.step_true hrr0 hact.2 fun loc hlt hp =>
            fun heq => Nat.ne_of_lt hlt (hinj_all loc (hlt.trans hact.1) cur hact.1 hp hact.2 heq)
    · rw [ite_eq_right hact]
      let fs1 : FastState := { fs with rebScanCursor := cur + 1 }
      refine ih fs1 hcoll0 hcnt_le (by dsimp only [fs1]; omega) hinj_all ⟨rm0, hvr0, ?_⟩
      change SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b)
        (fun loc => fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp)
        (min (fs.bktCount b) (cur + 1)) rm0
      by_cases hlt_cnt : cur < fs.bktCount b
      · rw [Nat.min_eq_right hlt_cnt.le] at hrr0
        rw [Nat.min_eq_right (Nat.succ_le_of_lt hlt_cnt)]
        exact SliceMapRel.step_false hrr0 fun hp => hact ⟨hlt_cnt, hp⟩
      · have hmin : min (fs.bktCount b) (cur + 1) = min (fs.bktCount b) cur := by omega
        rwa [hmin]

/-- `bufClearSteps k` on a `ClearableBufTrie` sets `nodeAlloc = max 1 (tr.nodeAlloc - k)`. -/
theorem ClearableBufTrie.clearSteps_nodeAlloc_eq :
    ∀ (k : ℕ) {tr : BufTrie}, ClearableBufTrie tr →
      (bufClearSteps k tr).nodeAlloc = max 1 (tr.nodeAlloc - k)
  | 0, _, hc => (Nat.max_eq_right hc.bounds.1).symm
  | k + 1, tr, hc => by
    obtain ⟨hc1, hna1⟩ := hc.clearOne_step
    dsimp only [bufClearSteps]
    rw [hc1.clearSteps_nodeAlloc_eq k, hna1]
    have := hc.bounds.1
    omega

theorem rebScanSteps_meta (c U n_max b : ℕ) (θ : SeedWhp c U n_max) :
    ∀ (k : ℕ) (s : FastState),
      (rebScanSteps c U n_max θ b k s).epochClock = s.epochClock ∧
      (rebScanSteps c U n_max θ b k s).curEp = s.curEp ∧
      (rebScanSteps c U n_max θ b k s).buf = s.buf ∧
      (rebScanSteps c U n_max θ b k s).rebStage = s.rebStage ∧
      (rebScanSteps c U n_max θ b k s).dirtyCount = s.dirtyCount ∧
      (rebScanSteps c U n_max θ b k s).dirtyIdx = s.dirtyIdx ∧
      (rebScanSteps c U n_max θ b k s).dirtyBuckets = s.dirtyBuckets ∧
      (rebScanSteps c U n_max θ b k s).rebCandSalt = s.rebCandSalt ∧
      (rebScanSteps c U n_max θ b k s).bktCount = s.bktCount := by
  intro k; induction k with
  | zero => intro s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    intro s; dsimp only [rebScanSteps]
    split_ifs
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (s.slices (s.rebSliceIdx b))
        (s.fpAt c U n_max θ s.rebCandSalt b s.rebScanCursor) <;> exact ih _
    · exact ih _

theorem rebScanSteps_cursor_of_zero (c U n_max b : ℕ) (θ : SeedWhp c U n_max) :
    ∀ (k : ℕ) (s : FastState),
      (rebScanSteps c U n_max θ b k s).rebCollision = 0 →
      (rebScanSteps c U n_max θ b k s).rebScanCursor = s.rebScanCursor + k := by
  intro k; induction k with
  | zero => intro s _; simp [rebScanSteps]
  | succ k ih =>
    intro s hcz; dsimp only [rebScanSteps] at hcz ⊢
    by_cases hsnz : s.rebCollision ≠ 0
    · rw [ite_eq_left hsnz] at hcz; exact absurd hcz hsnz
    rw [ite_eq_right hsnz] at hcz ⊢
    split_ifs at hcz ⊢
    · cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (s.slices (s.rebSliceIdx b))
        (s.fpAt c U n_max θ s.rebCandSalt b s.rebScanCursor)
      · rw [hlk] at hcz; dsimp only at hcz ⊢
        have h := ih _ hcz; dsimp only at h; omega
      · rw [hlk] at hcz; dsimp only at hcz
        have h1 : ∀ m (t : FastState), t.rebCollision = 1 →
            (rebScanSteps c U n_max θ b m t).rebCollision = 1 := by
          intro m; induction m <;> intro t ht
          · exact ht
          · dsimp only [rebScanSteps]; rw [ite_eq_left (by omega)]; exact ht
        have := h1 k { s with rebCollision := 1 } rfl; rw [hcz] at this; cases this
    · have h := ih _ hcz; dsimp only at h; omega

private theorem overmarsScanSteps_meta (c U n_max b : ℕ) (θ : SeedWhp c U n_max) :
    ∀ (k : ℕ) (s : FastState),
      (overmarsScanSteps c U n_max θ b k s).epochClock = s.epochClock ∧
      (overmarsScanSteps c U n_max θ b k s).curEp = s.curEp ∧
      (overmarsScanSteps c U n_max θ b k s).buf = s.buf ∧
      (overmarsScanSteps c U n_max θ b k s).rebStage = s.rebStage ∧
      (overmarsScanSteps c U n_max θ b k s).stageCursor = s.stageCursor ∧
      (overmarsScanSteps c U n_max θ b k s).dirtyCount = s.dirtyCount ∧
      (overmarsScanSteps c U n_max θ b k s).dirtyIdx = s.dirtyIdx ∧
      (overmarsScanSteps c U n_max θ b k s).dirtyBuckets = s.dirtyBuckets ∧
      (overmarsScanSteps c U n_max θ b k s).rebCandSalt = s.rebCandSalt ∧
      (overmarsScanSteps c U n_max θ b k s).rebScanCursor = s.rebScanCursor := by
  intro k; induction k with
  | zero => intro s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    intro s; dsimp only [overmarsScanSteps]; split_ifs <;> exact ih _

theorem overmarsStep_meta (c U n_max b : ℕ) (θ : SeedWhp c U n_max) (s : FastState) :
    (overmarsStep c U n_max θ b s).epochClock = s.epochClock ∧
    (overmarsStep c U n_max θ b s).curEp = s.curEp ∧
    (overmarsStep c U n_max θ b s).buf = s.buf ∧
    (overmarsStep c U n_max θ b s).rebStage = s.rebStage ∧
    (overmarsStep c U n_max θ b s).stageCursor = s.stageCursor ∧
    (overmarsStep c U n_max θ b s).dirtyCount = s.dirtyCount ∧
    (overmarsStep c U n_max θ b s).dirtyIdx = s.dirtyIdx ∧
    (overmarsStep c U n_max θ b s).dirtyBuckets = s.dirtyBuckets ∧
    (overmarsStep c U n_max θ b s).rebCandSalt = s.rebCandSalt ∧
    (overmarsStep c U n_max θ b s).rebScanCursor = s.rebScanCursor := by
  unfold overmarsStep overmarsAfterActivate
  dsimp only
  split_ifs <;> simp only [overmarsScanSteps_meta, and_self]

theorem bufDelete_everPresent (cTab bChar : ℕ) (tr : BufTrie) (rKey k : ℕ) :
    bufEverPresent cTab bChar (bufDelete cTab bChar tr rKey) k =
      bufEverPresent cTab bChar tr k := by
  dsimp only [bufDelete]
  cases bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => rfl
  | some leaf => dsimp only; split_ifs <;> rfl


theorem ValidBufTrie.everPresent_of_map_some {cTab bChar k b loc : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hk : k < 2 ^ (cTab * bChar)) (hm : mapFn k = some (b, loc)) :
    bufEverPresent cTab bChar tr k = true := by
  have hlk : bufLookup cTab bChar tr k = some (b, loc) := (hv.lookup_eq hk).trans hm
  dsimp only [bufLookup, bufEverPresent] at hlk ⊢
  cases hw : bufWalk bChar tr.trieChild k cTab 0 0 with
  | none => simp [hw] at hlk
  | some leaf => by_cases hz : tr.nodeLeafItem leaf = 0 <;> simp [hw, hz] at hlk ⊢

end Cslib.DataStructure.Dictionary.SuccinctWhp
