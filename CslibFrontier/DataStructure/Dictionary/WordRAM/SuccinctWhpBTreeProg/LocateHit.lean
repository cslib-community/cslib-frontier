/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Pre
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Helpers
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Descend
import CslibFrontier.Tactic.Realize

/-!
# Shared Leaf-Locate Prefix (`btreeLocateHitGenProg`) and In-Place Node Write Frame

Shared leaf-descent and SWAR rank hit-detection subroutine for `btreeLookupGenProg`,
`btreeDeleteGenProg`, and `btreeUpdateGenProg`, plus in-place node update preservation.
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

/-- Writing an updated node `nd'` at an already-allocated index `u < sl.alloc` preserves
`BTreeSliceMemRep` for `{ sl with nodes := Function.update sl.nodes u nd' }` and frames all other
slices and non-B+-tree memory words. -/
theorem writeBTreeNodeGenProg_inPlace_sliceRep {c U V w n_max base sIdx u : ℕ}
    {sl : BTreeSlice} {nd' : BTreeNode} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hu : u < sl.alloc)
    (hm_lt : nd'.metaWord < 2 ^ nodeMetaBitsWhp n_max)
    (hk_lt : nd'.keysWord < 2 ^ keysWordBitsWhp n_max)
    (hv_lt : nd'.valsWord < 2 ^ valsWordBitsWhp n_max) :
    let prog := writeBTreeNodeGenProg
      ((((mkWhpCoreParams c U V w n_max, base), sIdx), u),
        (nd'.metaWord, (nd'.keysWord, nd'.valsWord)))
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx { sl with nodes := Function.update sl.nodes u nd' }
      s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ a, a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a →
      s'.mem a = s.mem a) := by
  have hw := henv.2.1
  have hoff := largeOffsetChain c U V w n_max
  obtain ⟨hwn_fr, hwn_mc, hwn_vp, hwn_up, hwn_other, hwn_out⟩ :=
    writeBTreeNodeGenProg_spec (nd := nd') henv hsIdx (hu.trans_le hrep.1) hm_lt hk_lt hv_lt
      (s := s)
  dsimp only at hwn_fr hwn_mc hwn_vp hwn_up hwn_other hwn_out ⊢
  have hbm_eq : ∀ i < 16 * numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w
        ((Memory.spec 0).clientState s
          (writeBTreeNodeGenProg
            ((((mkWhpCoreParams c U V w n_max, base), sIdx), u),
              (nd'.metaWord, (nd'.keysWord, nd'.valsWord))))).mem i =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem i :=
    fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ => hwn_out a (Or.inl (by omega))
  exact ⟨hwn_fr, hwn_mc, hwn_vp,
    ⟨hrep.1, (hbm_eq _ (by omega)).trans hrep.2.1, (hbm_eq _ (by omega)).trans hrep.2.2.1,
      hwn_up sl hrep.1 fun v hv _ => hrep.2.2.2 v hv⟩,
    hwn_other, hwn_out⟩

/-- Shared leaf-locate prefix for `btreeLookupGenProg`, `btreeDeleteGenProg`, and
`btreeUpdateGenProg`: descends to the leaf for `q`, ranks `q` in `keysWord`, and returns
`(1, ((leafIdx, r), (mW, (kW, vW))))` on an exact key hit (`k_r = q`) or
`(0, ((0, 0), (0, (0, 0))))` on miss. -/
@[irreducible] def btreeLocateHitGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
  | (((cp, base), sIdx), q) => do
    let hdr ← readSliceHeaderGenProg ((cp, base), sIdx)
    let z0 ← pure 0
    if hdr.1 = z0 then
      pure (z0, ((z0, z0), (z0, (z0, z0))))
    else do
      let leafIdx ← descendLoopGenProg (((((cp, base), sIdx), q), hdr.2), wpHMaxBTree cp)
      let nd ← readBTreeNodeGenProg (((cp, base), sIdx), leafIdx)
      let (mW, kv) := nd
      let (kW, vW) := kv
      let cnt ← pure (mW / 2)
      let r ← swarRankGenProg (cp, ((cnt, q), kW))
      if r < cnt then do
        let k_r ← laneGetGenProg ((wpWKey cp, kW), r)
        if k_r = q then do
          let z1 ← pure 1
          pure (z1, ((leafIdx, r), (mW, (kW, vW))))
        else
          pure (z0, ((z0, z0), (z0, (z0, z0))))
      else
        pure (z0, ((z0, z0), (z0, (z0, z0))))

theorem btreeLocateHitGenProg_spec {c U V w n_max base sIdx insCount q : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) :
    let prog := btreeLocateHitGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤ 262 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (((Memory.spec 0).clientResult s prog = (0, ((0, 0), (0, (0, 0)))) ∧
        mapFn q = none ∧
        btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q = sl ∧
        ∀ newVal,
          btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q newVal = sl) ∨
      ∃ leafIdx r,
        let nd := sl.nodes leafIdx
        let cnt := metaCount nd.metaWord
        (Memory.spec 0).clientResult s prog =
          (1, ((leafIdx, r), (nd.metaWord, (nd.keysWord, nd.valsWord)))) ∧
        leafIdx < sl.alloc ∧
        r < cnt ∧
        cnt ≤ 2 * tMinWhp n_max - 1 ∧
        nd.metaWord < 2 ^ nodeMetaBitsWhp n_max ∧
        nd.keysWord < 2 ^ keysWordBitsWhp n_max ∧
        nd.keysWord < 2 ^ (cnt * keyLaneBitsWhp n_max) ∧
        nd.valsWord < 2 ^ (cnt * valLaneBitsWhp n_max) ∧
        mapFn q = some (laneGet (valLaneBitsWhp n_max) nd.valsWord r) ∧
        btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q =
          { sl with nodes := (Function.update sl.nodes leafIdx
              ⟨mkNodeMeta true (cnt - 1),
                wordDeleteAt (fpBitsWhp n_max + 2) r nd.keysWord,
                wordDeleteAt (valLaneBitsWhp n_max) r nd.valsWord⟩) } ∧
        ∀ newVal,
          btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q newVal =
            { sl with nodes := (Function.update sl.nodes leafIdx
                ⟨nd.metaWord, nd.keysWord,
                  wordUpdateAt (valLaneBitsWhp n_max) r newVal nd.valsWord⟩) }) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hlk_eq := hv.lookup_eq hth hins hq
  obtain ⟨hcs_h, hres_h, hmc_h, hvp_h⟩ := readSliceHeaderGenProg_spec hth hw hsIdx hrep (s := s)
  dsimp only at hcs_h hres_h hmc_h hvp_h
  unfold btreeLocateHitGenProg
  have hHeader := bind_of_readOnly hcs_h hres_h hvp_h
  simp only [wp_large_hMaxBTree hth, wp_large_wKey hth, pure_bind, (hHeader _ _).1,
    (hHeader _ _).2.1, (hHeader _ _).2.2.1, (hHeader _ _).2.2.2, hmc_h]
  obtain ⟨_, ⟨ha0, rfl⟩ | ⟨ha_pos, T, hrt, hht_lt, _, _, hT⟩⟩ :=
    hv.alloc_and_height_lt hth hins
  · simp only [ha0, ↓reduceIte, memoryCost_pure, Nat.add_zero]
    exact ⟨rfl, by decide, validProg_pure _, Or.inl ⟨rfl, trivial, by simp [btreeDelete, ha0],
      fun _ => by simp [btreeUpdate, ha0]⟩⟩
  · have ha_ne := Nat.ne_of_gt ha_pos
    simp only [ha_ne, ↓reduceIte]
    obtain ⟨ht3, _, hkey_lt, _⟩ := (btree_slice_param_bounds hth).1
    have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
      Nat.sub_lt (Nat.two_pow_pos _) one_pos
    obtain ⟨hdl_st, hdl_res, hdl_mc, hdl_vp, _⟩ :=
      descendLoopGenProg_spec henv hsIdx hrep hrt (Nat.zero_le q) (by omega) hhi hT
        (fuel := hMaxBTree)
    dsimp only at hdl_st hdl_res hdl_mc hdl_vp
    obtain ⟨cntL, loL, hiL, hhiL, hv_leaf⟩ :=
      descendToLeaf_leaf (by omega) hkey_lt hT hhi (Nat.zero_le q) (by omega) hht_lt.le
    rw [hrt] at hv_leaf
    set leafIdx := descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.nodes hMaxBTree sl.root q
    obtain ⟨hleaf_lt, hcnt_le, hm_lt, hkw_cnt, hk_lt, _, _⟩ :=
      validSubtree_root_bounds hth (hhiL.trans_lt hhi) hv_leaf
    dsimp only [BTreeTree.rootIdx] at hleaf_lt hcnt_le hm_lt hkw_cnt hk_lt
    obtain ⟨hnd_st, hnd_res, hnd_mc, hnd_vp⟩ :=
      readBTreeNodeGenProg_spec hth hw hsIdx hleaf_lt hrep (s := s)
    dsimp only at hnd_st hnd_res hnd_mc hnd_vp
    set cnt := metaCount (sl.nodes leafIdx).metaWord
    set r := swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) cnt q (sl.nodes leafIdx).keysWord
      with ← hr_def
    have hcnt_div : (sl.nodes leafIdx).metaWord / 2 = cnt := rfl
    have hvw_cnt : (sl.nodes leafIdx).valsWord < 2 ^ (cnt * valLaneBitsWhp n_max) := by
      obtain ⟨_, hm0, _, _, hvw0, _⟩ := hv_leaf
      have : cnt = cntL := by dsimp [cnt]; rw [hm0, metaCount_mkNodeMeta]
      rwa [this]
    have hDescend := bind_of_readOnly hdl_st hdl_res hdl_vp
    have hNode := bind_of_readOnly hnd_st hnd_res hnd_vp
    let rankInput := (mkWhpCoreParams c U V w n_max,
      (((sl.nodes leafIdx).metaWord / 2, q), (sl.nodes leafIdx).keysWord))
    have hRankResult : (Memory.spec 0).clientResult s (swarRankGenProg rankInput) = r := by
      dsimp only [rankInput]
      rw [clientResult_swarRankGenProg hth, hcnt_div, hr_def]
    have hRank := bind_of_readOnly (clientState_swarRankGenProg rankInput s) hRankResult
      (validWhpProg_swarRankGenProg (w := w) (F := base + largeSpaceWhp c U V w n_max) rankInput)
    simp only [(hDescend _ _).1, (hDescend _ _).2.1, (hDescend _ _).2.2.1,
      (hDescend _ _).2.2.2, (hNode _ _).1, (hNode _ _).2.1, (hNode _ _).2.2.1,
      (hNode _ _).2.2.2]
    rw [(hRank _ _).1, (hRank _ _).2.1, (hRank _ _).2.2.1, (hRank _ _).2.2.2]
    rw [hdl_mc]
    simp only [hnd_mc, memoryCost_swarRankGenProg, hMaxBTree_eq, Nat.zero_add, hcnt_div]
    refine ⟨?_, ?_, ?_, ?_⟩
    · split_ifs with hrc
      · rw [clientState_bind, clientState_laneGetGenProg]
        split_ifs <;> rfl
      · rfl
    · split_ifs with hrc
      · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, clientState_laneGetGenProg,
          memoryCost_laneGetGenProg]
        split_ifs <;> simp [memoryCost_pure]
      · simp [memoryCost_pure]
    · split_ifs with hrc
      · refine validProg_bind (validWhpProg_laneGetGenProg _) ?_
        rw [clientState_laneGetGenProg]
        split_ifs <;> exact validProg_pure _
      · exact validProg_pure _
    by_cases hhit : r < cnt ∧ laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r = q
    · obtain ⟨hrc, hkeq⟩ := hhit
      right
      refine ⟨leafIdx, r, ?_, hleaf_lt, hrc, hcnt_le, hm_lt, hk_lt, hkw_cnt, hvw_cnt, ?_,
        by simp [btreeDelete, ha_ne, leafIdx, cnt, r, hrc, hkeq],
        fun _ => by simp [btreeUpdate, ha_ne, leafIdx, cnt, r, hrc, hkeq]⟩
      · simp only [hrc, ↓reduceIte]
        rw [clientResult_bind, clientState_laneGetGenProg, clientResult_laneGetGenProg]
        simp [keyLaneBitsWhp, hkeq, StateTransitionSpec.clientResult_pure]
      · simp [← hlk_eq, btreeLookup, ha_ne, leafIdx, cnt, r, hrc, hkeq]
    · left
      have hne : r < cnt → laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
        fun hrc heq => hhit ⟨hrc, heq⟩
      refine ⟨?_, by simp +contextual [← hlk_eq, btreeLookup, ha_ne, leafIdx, cnt, r, hne],
        by simp +contextual [btreeDelete, ha_ne, leafIdx, cnt, r, hne],
        fun _ => by simp +contextual [btreeUpdate, ha_ne, leafIdx, cnt, r, hne]⟩
      by_cases hrc : r < cnt
      · simp only [hrc, ↓reduceIte]
        rw [clientResult_bind, clientState_laneGetGenProg, clientResult_laneGetGenProg]
        simp [keyLaneBitsWhp, hne hrc, StateTransitionSpec.clientResult_pure]
      · simp [hrc, StateTransitionSpec.clientResult_pure]

theorem realizes_btreeLocateHitGen :
    Realizes .exact btreeLocateHitGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      BTreeQueryGenPre
      (fun _ _ => 0) := by
  unfold btreeLocateHitGenProg
  realize [realizes_readSliceHeaderGen, realizes_descendLoopGen, realizes_readBTreeNodeGen,
    realizes_swarRankGen, realizes_laneGetGen]
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, sIdx⟩, q⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, insCount, sl, mapFn,
      henv, rfl, hsIdx, hins, hrep, hv, hq⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
      Nat.sub_lt (Nat.two_pow_pos _) one_pos
    obtain ⟨hcs_h, hres_h, _, _⟩ := readSliceHeaderGenProg_spec hth henv.2.1 hsIdx hrep (s := s)
    dsimp only at hcs_h hres_h
    simp only [hcs_h, hres_h, wp_large_M hth, wp_large_hMaxBTree hth, wp_large_nSlice hth,
      wp_large_wKey hth] at *
  all_goals try first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hsIdx
    | decide
    | exact henv.fits_const (by decide)
    | exact (Nat.le_mul_of_pos_left _ (by have := eight_le_tMinWhp hth; omega)).trans_lt
        henv.keysWordBits_lt_w
  all_goals
    obtain ⟨_, ⟨ha0, _⟩ | ⟨_, T, hrt, hht_lt, _, _, hT⟩⟩ := hv.alloc_and_height_lt hth hins
    · simp_all
    obtain ⟨ht3, _, hkey_lt, _⟩ := (btree_slice_param_bounds hth).1
    obtain ⟨hdl_st, hdl_res, _, _, hdl_pre⟩ := descendLoopGenProg_spec henv hsIdx hrep hrt
      (Nat.zero_le q) (by omega) hhi hT (fuel := hMaxBTree)
    dsimp only at hdl_st hdl_res
    obtain ⟨cntL, loL, hiL, hhiL, hv_leaf⟩ :=
      descendToLeaf_leaf (by omega) hkey_lt hT hhi (Nat.zero_le q) (by omega) hht_lt.le
    rw [hrt] at hv_leaf
    obtain ⟨hleaf_lt, hcnt_le, _, hkw_cnt, _, _, hlanes⟩ :=
      validSubtree_root_bounds hth (hhiL.trans_lt hhi) hv_leaf
    dsimp only [BTreeTree.rootIdx] at hleaf_lt hcnt_le hkw_cnt hlanes
    obtain ⟨hnd_st, hnd_res, _, _⟩ :=
      readBTreeNodeGenProg_spec hth henv.2.1 hsIdx hleaf_lt hrep (s := s)
    dsimp only at hnd_st hnd_res
  · exact hdl_pre
  · exact hdl_res.symm ▸ hleaf_lt.trans_le hrep.1
  · rw [hdl_st, hdl_res, hnd_res]
    refine ⟨⟨base, c, U, V, w, n_max, henv, rfl⟩,
      (wp_large_capLanes hth).symm ▸ Nat.lt_of_le_of_lt hcnt_le (by omega),
      (wp_large_powFp hth).symm ▸ hq, (wp_large_wKey hth).symm ▸ hkw_cnt, ?_⟩
    rwa [wp_large_wKey hth, wp_large_powFp hth]
  · set leafIdx := descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.nodes hMaxBTree sl.root q
    simp only [hdl_st, hdl_res, hnd_st, hnd_res, clientResult_swarRankGenProg hth] at *
    let mW := (sl.nodes leafIdx).metaWord
    have hrc : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) (mW / 2) q
        (sl.nodes leafIdx).keysWord < mW / 2 := by assumption
    exact ((Nat.mul_le_mul_right _ (hrc.le.trans (hcnt_le.trans (Nat.sub_le _ _)))).trans_lt
      henv.keysWordBits_lt_w).trans Nat.lt_two_pow_self

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
