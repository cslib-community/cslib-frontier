/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg

/-!
# Shared Bucket & Value-Lane Bounds for Fast Operations

Internal helper lemmas extracting buffer/slice invariants on a bucket from `ValidFastState` and
bounding dense local coordinates by `2 ^ valLaneBitsWhp n_max`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.validFastState_delete_bounds`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.loc_lt_two_pow_valLaneBits`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-- Extract buffer and slice invariants on bucket `b` from `ValidFastState`. -/
theorem validFastState_delete_bounds {c U V n_max b : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict) (hb : b < numBucketsWhp n_max) :
    (∀ loc < fs.bktCount b, fs.locState b loc = 2 →
      (fs.buf 0).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf 0).itemAlloc < qEpochWhp n_max ∧
      ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 0) m0) ∧
    (∀ loc < fs.bktCount b, fs.locState b loc = 3 →
      (fs.buf 1).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf 1).itemAlloc < qEpochWhp n_max ∧
      ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 1) m1) ∧
    fs.liveSliceIdx b < 3 * numBucketsWhp n_max ∧
    fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max ∧
    fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
    fs.liveSliceIdx b ≠ fs.overmarsSliceIdx b ∧
    fs.liveSliceIdx b ≠ fs.rebSliceIdx b ∧
    fs.overmarsSliceIdx b ≠ fs.rebSliceIdx b ∧
    (fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ lm, ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm) ∧
    (fs.overmarsActive b = 1 →
      fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
      ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om) ∧
    (decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0) = true →
      fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm) := by
  have hL12 : 4096 ≤ (slabScale n_max) ^ 12 :=
    (by decide : 4096 ≤ 2 ^ 12).trans (Nat.pow_le_pow_left (two_le_slabScale n_max) 12)
  have hcnt3 : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12 :=
    (hv.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
  obtain ⟨hlr, hor, hne_ro⟩ := hv.roles_valid b hb
  have hbuf_of_tag : ∀ ep, (ep = 0 ∨ ep = 1) →
      ∀ loc < fs.bktCount b, fs.locState b loc = 2 + ep →
        (fs.buf ep).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
        (fs.buf ep).itemAlloc < qEpochWhp n_max ∧
        ∃ mp, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) mp := by
    intro ep hep loc hloc htag
    by_cases hce : ep = fs.curEp
    · subst hce
      obtain ⟨hia, hna, mp, hvb, _⟩ := hv.bufCur_valid
      exact (bufTrie_caps_of_bounds hv.hth hia hna).imp_right (⟨·, mp, hvb⟩)
    · obtain rfl : ep = fs.oldEp := by
        rcases hep with rfl | rfl <;> rcases hv.curEp_or with hc | hc <;>
          simp_all [FastState.oldEp]
      have hbo := hv.bufOld_valid
      split_ifs at hbo
      · obtain ⟨hia, hna, mp, hvb, _⟩ := hbo
        exact (bufTrie_caps_of_bounds hv.hth hia hna).imp_right (⟨·, mp, hvb⟩)
      all_goals exact absurd htag (hbo.1 b hb loc hloc)
  dsimp only [FastState.liveSliceIdx, FastState.overmarsSliceIdx, FastState.rebSliceIdx,
    FastState.rebRole]
  refine ⟨hbuf_of_tag 0 (Or.inl rfl), hbuf_of_tag 1 (Or.inr rfl),
    by omega,
    by omega,
    by omega,
    by omega,
    by omega,
    by omega,
    ⟨liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb),
     let ⟨lm, hvl, _⟩ := hv.live_valid b hb; ⟨lm, hvl⟩⟩,
    fun ha1 => ?_, fun hreb_b => ?_⟩
  · rcases hv.overmars_valid b hb with ⟨h0, _⟩ | ⟨_, _, hcur_lt, _, hins, om, hv_om, _⟩
    · omega
    · exact ⟨by omega, om, hv_om⟩
  · obtain ⟨hs2, _, hdb, hcs, _⟩ := of_decide_eq_true hreb_b
    have hstg := hv.stage_valid
    dsimp only [ValidEpochStage] at hstg
    simp only [hs2, Nat.reduceEqDiff, ↓reduceIte] at hstg
    obtain ⟨hcur_r, _, rm, hv_rm, _⟩ := hstg.2.2.2.2.2.2 hcs
    rw [hdb] at hcur_r hv_rm
    rcases hcur_r with ⟨_, hi0⟩ | ⟨_, hcur_lt, hins⟩ <;> exact ⟨by omega, rm, hv_rm⟩

theorem loc_lt_two_pow_valLaneBits {n_max loc : ℕ}
    (hloc : loc < totalLocalCoordsWhp n_max) : loc < 2 ^ valLaneBitsWhp n_max := by
  have := hloc.trans_le totalLocalCoordsWhp_le_three_mul
  have : 0 < (slabScale n_max) ^ 12 := Nat.pow_pos (Nat.two_pow_pos _)
  rw [two_pow_valLaneBitsWhp]; omega

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
