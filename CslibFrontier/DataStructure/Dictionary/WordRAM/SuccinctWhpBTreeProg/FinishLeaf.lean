/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Helpers
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.SplitOps
import CslibFrontier.Tactic.Realize

/-!
# Non-Full Leaf Update or Sorted Lane Insertion (`finishLeafInsertGenProg`)

Implements and certifies phase 3 of `btreeInsertGenProg`: ranking `q` in a guaranteed non-full leaf
and either updating the value lane in place on a key hit or inserting `(q, val)` into the packed
key/value words.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

private def checkLeafHitBody
    (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let z0 ← pure 0
  let z1 ← pure 1
  if d.1.2.1 < d.1.2.2 then do
    let k_r ← laneGetGenProg ((d.1.1.1, d.1.1.2), d.1.2.1)
    if k_r = d.2 then pure z1 else pure z0
  else pure z0

private theorem realizes_checkLeafHitBody :
    Realizes .exact checkLeafHitBody
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => 1 < w ∧ d.1.1.1 < w ∧ Fits w (d.1.2.1 * d.1.1.1))
      (fun _ _ => 0) := by
  have hlg := realizes_laneGetGen
  realize
  exacts [Nat.one_lt_two_pow (by linarith [h.1]), h.2.1, h.2.2]

/-- Opaque helper checking `r < cnt ∧ laneGet wKey keysWord r = q` (`d = (((wKey, keysWord), (r,
  cnt)), q)`),
returning `1` on a hit and `0` on a miss without putting an `if` on the LHS of `>>=`. -/
@[irreducible] private def checkLeafHitGenProg
    (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ :=
  checkLeafHitBody d

private theorem checkLeafHit_eq_one_imp_lt
    (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State)
    (h : (Memory.spec 0).clientResult s (checkLeafHitGenProg d) = 1) :
    d.1.2.1 < d.1.2.2 := by
  unfold checkLeafHitGenProg checkLeafHitBody at h
  simp only [pure_bind] at h
  by_contra hge
  simp [hge, StateTransitionSpec.clientResult_pure] at h

private theorem realizes_checkLeafHitGen :
    Realizes .exact checkLeafHitGenProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => 1 < w ∧ d.1.1.1 < w ∧ Fits w (d.1.2.1 * d.1.1.1))
      (fun _ _ => 0) := by
  unfold checkLeafHitGenProg; exact realizes_checkLeafHitBody


/-- Precondition for `finishLeafInsertGenProg`
(`d = (((((cp, base), sIdx), leafIdx), q), val)`). -/
@[expose] def FinishLeafGenPre (w : ℕ) :
    ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((((cp, base), sIdx), leafIdx), q), val), s =>
    ∃ c U V w₀ n_max sl isR cntL loL hiL mapFn,
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      sIdx < 3 * numBucketsWhp n_max ∧
      BTreeSliceMemRep base c U V w₀ n_max sIdx sl s.mem ∧
      cntL < 2 * tMinWhp n_max - 1 ∧
      loL ≤ q ∧ q ≤ hiL ∧ hiL < 2 ^ fpBitsWhp n_max ∧
      val < 2 ^ valLaneBitsWhp n_max ∧
      ValidSubtree isR (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl.alloc sl.nodes loL hiL mapFn (.leaf leafIdx cntL)

/-- Parameter-free `finishLeafInsert` (`d = (((((cp, base), sIdx), leafIdx), q), val)`). -/
def finishLeafInsertGenProg :
    ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((((cp, base), sIdx), leafIdx), q), val) => do
    let nd ← readBTreeNodeGenProg (((cp, base), sIdx), leafIdx)
    let (mW, kv) := nd
    let (kW, vW) := kv
    let cnt ← pure (mW / 2)
    let r ← swarRankGenProg (cp, ((cnt, q), kW))
    let wKey ← pure (wpWKey cp)
    let hit ← checkLeafHitGenProg (((wKey, kW), (r, cnt)), q)
    let z1 ← pure 1
    if hit = z1 then do
      let v' ← wordUpdateAtGenProg (((wpWVal cp, r), val), vW)
      writeNodeOpProg ((((cp, base), sIdx), leafIdx), (mW, (kW, v')))
    else do
      let m' ← pure (1 + 2 * (cnt + 1))
      let k' ← wordInsertOpProg (((wKey, r), q), kW)
      let v' ← wordInsertOpProg (((wpWVal cp, r), val), vW)
      writeNodeOpProg ((((cp, base), sIdx), leafIdx), (m', (k', v')))

private theorem swarRank_le_cntL {c n_max cntL q kw : ℕ}
    (hth : whpThreshold c ≤ n_max)
    (hcntL : cntL < 2 * tMinWhp n_max - 1)
    (hq : q < 2 ^ fpBitsWhp n_max)
    (hkw : kw < 2 ^ (cntL * keyLaneBitsWhp n_max))
    (hlanes : ∀ j < cntL, laneGet (keyLaneBitsWhp n_max) kw j < 2 ^ fpBitsWhp n_max) :
    swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) cntL q kw ≤ cntL := by
  have ht8 := eight_le_tMinWhp hth
  have hkey_lt := (btree_slice_param_bounds hth).1.2.2.1
  rw [swarRank_eq_count_lt (by omega) hkey_lt hq hkw hlanes]
  exact (card_filter_le _ _).trans_eq (card_range _)

theorem finishLeafInsertGenProg_spec {isR : Bool}
    {c U V w n_max base sIdx leafIdx cntL loL hiL q val : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hcntL : cntL < 2 * tMinWhp n_max - 1)
    (_hqlo : loL ≤ q) (hqhi : q ≤ hiL) (hhi : hiL < 2 ^ fpBitsWhp n_max)
    (hval : val < 2 ^ valLaneBitsWhp n_max)
    (hv_leaf : ValidSubtree isR (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.alloc sl.nodes loL hiL mapFn (.leaf leafIdx cntL)) :
    let prog := finishLeafInsertGenProg
      (((((mkWhpCoreParams c U V w n_max, base), sIdx), leafIdx), q), val)
    let sl' := finishLeafInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl leafIdx q val
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 18 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx sl' s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ a, a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  obtain ⟨ht3, hmeta_cap, hkey_lt, _⟩ := (btree_slice_param_bounds hth).1
  obtain ⟨hleaf_lt, _, hm_lt, hkw_cnt, hk_lt, _, hlanes⟩ := validSubtree_root_bounds hth hhi hv_leaf
  dsimp only [BTreeTree.rootIdx] at hleaf_lt hm_lt hkw_cnt hk_lt hlanes
  obtain ⟨hnd_st, hnd_res, hnd_mc, hnd_vp⟩ :=
    readBTreeNodeGenProg_spec hth hw hsIdx hleaf_lt hrep (s := s)
  dsimp only at hnd_st hnd_res hnd_mc hnd_vp
  have hcnt_eq_L : metaCount (sl.nodes leafIdx).metaWord = cntL := by
    rw [hv_leaf.2.1, metaCount_mkNodeMeta]
  set cnt := metaCount (sl.nodes leafIdx).metaWord
  set r := swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) cnt q (sl.nodes leafIdx).keysWord
  have hr_def : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max)
      ((sl.nodes leafIdx).metaWord / 2) q (sl.nodes leafIdx).keysWord = r := rfl
  have hcnt_lt : cnt < 2 * tMinWhp n_max - 1 := by dsimp only [cnt]; omega
  have hr_le : r ≤ cnt :=
    swarRank_le_cntL hth hcnt_lt (hqhi.trans_lt hhi) (hcnt_eq_L ▸ hkw_cnt) (hcnt_eq_L ▸ hlanes)
  have hoff := largeOffsetChain c U V w n_max
  unfold finishLeafInsertGenProg checkLeafHitGenProg checkLeafHitBody writeNodeOpProg
    wordInsertOpProg
  simp only [wp_large_wKey hth, wp_large_wVal hth, pure_bind]
  set hitProg : Memory.Prog ℕ :=
    if r < cnt then
      laneGetGenProg ((keyLaneBitsWhp n_max, (sl.nodes leafIdx).keysWord), r) >>= fun k_r =>
      if k_r = q then pure 1 else pure 0
    else pure 0
  have hhit_st : (Memory.spec 0).clientState s hitProg = s := by
    dsimp only [hitProg]
    split_ifs with hrc
    · rw [clientState_bind, clientState_laneGetGenProg]
      split_ifs <;> rfl
    · rfl
  have hhit_mc : memoryCost hitProg s = 0 := by
    dsimp only [hitProg]
    split_ifs with hrc
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, clientState_laneGetGenProg,
        memoryCost_laneGetGenProg]
      split_ifs <;> rfl
    · rfl
  have hhit_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s hitProg := by
    dsimp only [hitProg]
    split_ifs with hrc
    · refine validProg_bind (validWhpProg_laneGetGenProg _) ?_
      rw [clientState_laneGetGenProg]
      split_ifs <;> exact validProg_pure _
    · exact validProg_pure _
  set p0 := (mkWhpCoreParams c U V w n_max, base)
  set P : Memory.Prog Unit :=
    readBTreeNodeGenProg ((p0, sIdx), leafIdx) >>= fun nd =>
      swarRankGenProg (p0.1, ((nd.1 / 2, q), nd.2.1)) >>= fun r0 =>
      (if r0 < nd.1 / 2 then
        laneGetGenProg ((keyLaneBitsWhp n_max, nd.2.1), r0) >>= fun k_r =>
        if k_r = q then pure 1 else pure 0
      else pure 0) >>= fun ht =>
      if ht = 1 then
        wordUpdateAtGenProg (((valLaneBitsWhp n_max, r0), val), nd.2.2) >>= fun v' =>
        writeBTreeNodeGenProg (((p0, sIdx), leafIdx), (nd.1, (nd.2.1, v')))
      else
        wordInsertAtGenProg (((keyLaneBitsWhp n_max, r0), q), nd.2.1) >>= fun k' =>
        wordInsertAtGenProg (((valLaneBitsWhp n_max, r0), val), nd.2.2) >>= fun v' =>
        writeBTreeNodeGenProg (((p0, sIdx), leafIdx), (1 + 2 * (nd.1 / 2 + 1), (k', v')))
    with hP
  have hfinish (nd' : BTreeNode)
      (hm'_lt : nd'.metaWord < 2 ^ nodeMetaBitsWhp n_max)
      (hk'_lt : nd'.keysWord < 2 ^ keysWordBitsWhp n_max)
      (hv'_lt : nd'.valsWord < 2 ^ valsWordBitsWhp n_max)
      (hfin_eq : finishLeafInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl leafIdx q val = { sl with nodes := Function.update sl.nodes leafIdx nd' })
      {tailProg : Memory.Prog Unit}
      (htail_eq : (if (Memory.spec 0).clientResult s hitProg = 1 then
          wordUpdateAtGenProg (((valLaneBitsWhp n_max, r), val), (sl.nodes leafIdx).valsWord) >>=
            fun v' => writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
              ((sl.nodes leafIdx).metaWord, ((sl.nodes leafIdx).keysWord, v')))
        else
          wordInsertAtGenProg (((keyLaneBitsWhp n_max, r), q), (sl.nodes leafIdx).keysWord) >>=
            fun k' => wordInsertAtGenProg (((valLaneBitsWhp n_max, r), val),
              (sl.nodes leafIdx).valsWord) >>=
            fun v' => writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
              (1 + 2 * ((sl.nodes leafIdx).metaWord / 2 + 1), (k', v')))) = tailProg)
      (htail_st : (Memory.spec 0).clientState s tailProg = (Memory.spec 0).clientState s
        (writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
          (nd'.metaWord, (nd'.keysWord, nd'.valsWord)))))
      (htail_mc : memoryCost tailProg s = 12)
      (htail_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
        (writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
          (nd'.metaWord, (nd'.keysWord, nd'.valsWord)))) →
        ValidProg w (base + largeSpaceWhp c U V w n_max) s tailProg) :
      ((Memory.spec 0).clientState s P).frontier = s.frontier ∧
      memoryCost P s = 18 ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s P ∧
      BTreeSliceMemRep base c U V w n_max sIdx
        (finishLeafInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          sl leafIdx q val) ((Memory.spec 0).clientState s P).mem ∧
      (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
        BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
        BTreeSliceMemRep base c U V w n_max sIdx' sl₂ ((Memory.spec 0).clientState s P).mem) ∧
      (∀ a, a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a →
        ((Memory.spec 0).clientState s P).mem a = s.mem a) := by
    obtain ⟨hwn_fr, _, hwn_vp, hwn_up, hwn_other, hwn_out⟩ :=
      writeBTreeNodeGenProg_spec (nd := nd') henv hsIdx (hleaf_lt.trans_le hrep.1)
        hm'_lt hk'_lt hv'_lt (s := s)
    dsimp only at hwn_fr hwn_vp hwn_up hwn_other hwn_out
    have hs'_wn : (Memory.spec 0).clientState s P = (Memory.spec 0).clientState s
        (writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
          (nd'.metaWord, (nd'.keysWord, nd'.valsWord)))) := by
      rw [hP, clientState_bind, hnd_st, hnd_res,
        clientState_bind, clientState_swarRankGenProg,
        clientResult_swarRankGenProg hth, hr_def]
      change (Memory.spec 0).clientState s (hitProg >>= _) = _
      rw [clientState_bind, hhit_st, htail_eq, htail_st]
    rw [hs'_wn]
    refine ⟨hwn_fr, ?_, ?_, ?_, hwn_other, hwn_out⟩
    · rw [hP, Realization.memoryCost_bind', hnd_st, hnd_mc, hnd_res,
        Realization.memoryCost_bind', clientState_swarRankGenProg,
        memoryCost_swarRankGenProg, clientResult_swarRankGenProg hth, hr_def]
      change 6 + (0 + memoryCost (hitProg >>= _) s) = 18
      rw [Realization.memoryCost_bind', hhit_st, hhit_mc, htail_eq, htail_mc]
    · rw [hP]
      refine validProg_bind hnd_vp ?_
      rw [hnd_st, hnd_res]
      refine validProg_bind (validWhpProg_swarRankGenProg _) ?_
      rw [clientState_swarRankGenProg, clientResult_swarRankGenProg hth, hr_def]
      change ValidProg w _ s (hitProg >>= _)
      refine validProg_bind hhit_vp ?_
      rw [hhit_st, htail_eq]
      exact htail_vp hwn_vp
    · rw [hfin_eq]
      have hbm_eq : ∀ i < 16 * numBucketsWhp n_max,
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w
            ((Memory.spec 0).clientState s
              (writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
                (nd'.metaWord, (nd'.keysWord, nd'.valsWord))))).mem i =
            readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem i :=
        fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ => hwn_out a (Or.inl (by omega))
      exact ⟨hrep.1, (hbm_eq _ (by omega)).trans hrep.2.1,
        (hbm_eq _ (by omega)).trans hrep.2.2.1, hwn_up sl hrep.1 fun v hv _ => hrep.2.2.2 v hv⟩
  have hvw0 : (sl.nodes leafIdx).valsWord < 2 ^ (cnt * valLaneBitsWhp n_max) :=
    hcnt_eq_L ▸ hv_leaf.2.2.2.2.1
  by_cases hhit : r < cnt ∧ laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r = q
  · obtain ⟨hrc, hkeq⟩ := hhit
    have hhit_res : (Memory.spec 0).clientResult s hitProg = 1 := by
      simp [hitProg, hrc, clientResult_bind, clientResult_laneGetGenProg, keyLaneBitsWhp, hkeq,
        StateTransitionSpec.clientResult_pure]
    let nd' : BTreeNode :=
      ⟨(sl.nodes leafIdx).metaWord, (sl.nodes leafIdx).keysWord,
        wordUpdateAt (valLaneBitsWhp n_max) r val (sl.nodes leafIdx).valsWord⟩
    have hv'_lt : nd'.valsWord < 2 ^ valsWordBitsWhp n_max := by
      unfold valsWordBitsWhp
      exact (wordUpdateAt_lt hrc hval hvw0).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
    refine hfinish nd' hm_lt hk_lt hv'_lt
      (by simp [finishLeafInsert, cnt, r, hrc, hkeq, nd'])
      (ite_eq_left hhit_res)
      (by rw [clientState_bind, clientState_wordUpdateAtGenProg, clientResult_wordUpdateAtGenProg])
      (by
        rw [Realization.memoryCost_bind', clientState_wordUpdateAtGenProg,
          memoryCost_wordUpdateAtGenProg, memoryCost_writeBTreeNodeGenProg])
      fun hwn_vp => validProg_bind (validWhpProg_wordUpdateAtGenProg _)
        (by rwa [clientState_wordUpdateAtGenProg, clientResult_wordUpdateAtGenProg])
  · -- Miss: insert `(q, val)` at lane `r` (`cnt + 1 ≤ 2 * tMin - 1`)
    have hne : r < cnt → laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
      fun hrc heq => hhit ⟨hrc, heq⟩
    have hhit_res : (Memory.spec 0).clientResult s hitProg = 0 := by
      dsimp only [hitProg]
      by_cases hrc : r < cnt
      · simp [hrc, clientResult_bind, clientResult_laneGetGenProg, keyLaneBitsWhp, hne hrc,
          StateTransitionSpec.clientResult_pure]
      · simp [hrc, StateTransitionSpec.clientResult_pure]
    let nd' : BTreeNode :=
      ⟨mkNodeMeta true (cnt + 1),
        wordInsertAt (fpBitsWhp n_max + 2) r q (sl.nodes leafIdx).keysWord,
        wordInsertAt (valLaneBitsWhp n_max) r val (sl.nodes leafIdx).valsWord⟩
    have hm'_lt : nd'.metaWord < 2 ^ nodeMetaBitsWhp n_max := by
      simp only [nd', mkNodeMeta, ↓reduceIte]; omega
    have hq_kl : q < 2 ^ (fpBitsWhp n_max + 2) :=
      (hqhi.trans_lt hhi).trans (Nat.pow_lt_pow_right (by decide) (by omega))
    have hk'_lt : nd'.keysWord < 2 ^ keysWordBitsWhp n_max := by
      dsimp only [nd', keysWordBitsWhp, keyLaneBitsWhp]
      exact (wordInsertAt_lt hr_le hq_kl hkw_cnt).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
    have hv'_lt : nd'.valsWord < 2 ^ valsWordBitsWhp n_max := by
      dsimp only [nd', valsWordBitsWhp]
      exact (wordInsertAt_lt hr_le hval hvw0).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
    refine hfinish nd' hm'_lt hk'_lt hv'_lt
      (by
        by_cases hrc : r < cnt <;> simp [finishLeafInsert, cnt, r, hrc, hne, nd'])
      (ite_eq_right fun h => absurd (hhit_res.symm.trans h) zero_ne_one)
      (by
        rw [clientState_bind, clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg,
          clientState_bind, clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg]
        dsimp only [nd', cnt, metaCount, mkNodeMeta, keyLaneBitsWhp]
        rfl)
      (by
        rw [Realization.memoryCost_bind', clientState_wordInsertAtGenProg,
          memoryCost_wordInsertAtGenProg, Realization.memoryCost_bind',
          clientState_wordInsertAtGenProg, memoryCost_wordInsertAtGenProg,
          memoryCost_writeBTreeNodeGenProg])
      fun hwn_vp => validProg_bind (validWhpProg_wordInsertAtGenProg _) (by
        rw [clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg]
        exact validProg_bind (validWhpProg_wordInsertAtGenProg _)
          (by rwa [clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg]))

theorem realizes_finishLeafInsertGen :
    Realizes .exact finishLeafInsertGenProg
      (WordEncoding.encode (α := ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      FinishLeafGenPre
      (fun _ _ => 0) := by
  unfold finishLeafInsertGenProg
  have hrn := realizes_readBTreeNodeGen
  have hsr := realizes_swarRankGen
  have hch := realizes_checkLeafHitGen
  have hwu := realizes_wordUpdateAtGen
  have hwi := realizes_wordInsertOp
  have hwn := realizes_writeNodeOp
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨⟨cp, base⟩, sIdx⟩, leafIdx⟩, q⟩, val⟩
    dsimp only [FinishLeafGenPre] at h
    obtain ⟨c, U, V, w₀, n_max, sl, isR, cntL, loL, hiL, mapFn,
      henv, rfl, hsIdx, hrep, hcntL, hqlo, hqhi, hhi, hval, hv_leaf⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    simp only [wp_large_M hth, wp_large_nSlice hth, wp_large_wKey hth, wp_large_wVal hth] at *
    try first
      | decide
      | exact henv.fits_const (by decide)
      | exact ⟨c, U, V, w, n_max, henv, rfl⟩
      | exact hsIdx
  all_goals
    have ht8 := eight_le_tMinWhp hth
    obtain ⟨hleaf_lt, _, _, hkw_cnt, _, _, hlanes⟩ := validSubtree_root_bounds hth hhi hv_leaf
    dsimp only [BTreeTree.rootIdx] at hleaf_lt hkw_cnt hlanes
    obtain ⟨hnd_st, hnd_res, _, _⟩ := readBTreeNodeGenProg_spec hth henv.2.1 hsIdx hleaf_lt hrep
      (s := s)
    dsimp only at hnd_st hnd_res
    have hcnt_eq_L : metaCount (sl.nodes leafIdx).metaWord = cntL := by
      rw [hv_leaf.2.1, metaCount_mkNodeMeta]
    have hcnt_div : (sl.nodes leafIdx).metaWord / 2 = cntL := hcnt_eq_L
    have hr_le := swarRank_le_cntL hth hcntL (hqhi.trans_lt hhi)
      (hcnt_eq_L ▸ hkw_cnt) (hcnt_eq_L ▸ hlanes)
    have hmul_kl : 2 * tMinWhp n_max * 2 ≤ 2 * tMinWhp n_max * keyLaneBitsWhp n_max :=
      Nat.mul_le_mul_left _ (Nat.le_add_left 2 _)
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    simp only [hnd_st, hnd_res, hcnt_div, clientResult_swarRankGenProg hth] at *
    try exact hleaf_lt.trans_le hrep.1
  · refine ⟨⟨base, c, U, V, w, n_max, henv, rfl⟩, ?_, ?_, ?_, ?_⟩
    · simp only [wp_large_capLanes hth]; omega
    · simp only [wp_large_powFp hth]; exact hqhi.trans_lt hhi
    · simp only [wp_large_wKey hth, ← hcnt_eq_L]; exact hkw_cnt
    · simp only [wp_large_wKey hth, wp_large_powFp hth, ← hcnt_eq_L]; exact hlanes
  · omega
  · exact (Nat.le_mul_of_pos_left _ (by omega)).trans_lt hkw_lt
  · exact ((Nat.mul_le_mul_right _ (hr_le.trans (by omega))).trans_lt hkw_lt).trans
      Nat.lt_two_pow_self
  · have hrc := checkLeafHit_eq_one_imp_lt _ _ hc
    refine ⟨cntL, by unfold valLaneBitsWhp; positivity, hrc,
      (Nat.mul_le_mul_right _ (by omega)).trans_lt hvw_lt, hval, hv_leaf.2.2.2.2.1⟩
  · exact (by omega : 1 + 2 * (cntL + 1) < w).trans Nat.lt_two_pow_self
  · exact (by omega : cntL + 1 < w).trans Nat.lt_two_pow_self
  · exact ⟨cntL, hr_le, (Nat.mul_le_mul_right _ (by omega)).trans_lt hkw_lt,
      (hqhi.trans_lt hhi).trans
        (Nat.pow_lt_pow_right Nat.one_lt_two (Nat.lt_add_of_pos_right two_pos)),
      hcnt_eq_L ▸ hkw_cnt⟩
  · exact ⟨cntL, hr_le, (Nat.mul_le_mul_right _ (by omega)).trans_lt hvw_lt, hval,
      hv_leaf.2.2.2.2.1⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
