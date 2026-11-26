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
# Root Initialization and Proactive Root Split (`ensureAndSplitRootGenProg`)

Implements and certifies phase 1 of `btreeInsertGenProg`: initializing an empty slice (`alloc = 0`)
to a single empty leaf or proactively splitting a full `(2t - 1)`-key root before descent.
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

private def initEmptyRootBody (d : (WhpCoreParams × ℕ) × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let z0 ← pure 0
  let z1 ← pure 1
  writeNodeOpProg ((d, z0), (z1, (z0, z0)))
  writeSliceHeaderGenProg (d, (z1, z0))
  pure (z1, z0)

private theorem realizes_initEmptyRootBody :
    Realizes .exact initEmptyRootBody
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => WhpLargeEnvGen w d.1.1 d.1.2 ∧ d.2 < 3 * wpM d.1.1)
      (fun _ _ => 0) := by
  have hwn := realizes_writeNodeOp
  have hwh := realizes_writeSliceHeaderGen
  realize
  all_goals
    rcases d with ⟨⟨cp, base⟩, sIdx⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hsIdx⟩ := h
    have hth := henv.2.2.2.1
    have h64 := sixty_four_le_nSliceWhp n_max
    simp only [wp_large_M hth, wp_large_nSlice hth] at hsIdx ⊢
    first
    | omega
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w₀, n_max, henv, rfl⟩

/-- Opaque empty-root initialization subroutine for `ensureAndSplitRootGenProg`. -/
@[irreducible] private def initEmptyRootOpProg (d : (WhpCoreParams × ℕ) × ℕ) :
    Memory.Prog (ℕ × ℕ) :=
  initEmptyRootBody d

private theorem realizes_initEmptyRootOp :
    Realizes .exact initEmptyRootOpProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => WhpLargeEnvGen w d.1.1 d.1.2 ∧ d.2 < 3 * wpM d.1.1)
      (fun _ _ => 0) := by
  unfold initEmptyRootOpProg; exact realizes_initEmptyRootBody

private def SplitFullRootPre (w : ℕ)
    (x : ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) (_s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max,
    WhpLargeEnv c U V w₀ n_max w x.1.1.2 ∧
    x.1.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    x.1.2 < 3 * numBucketsWhp n_max ∧
    x.2.1.1 + 2 ≤ nSliceWhp n_max ∧
    x.2.1.2 < x.2.1.1

private def splitFullRootBody
    (x : ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) : Memory.Prog (ℕ × ℕ) := do
  let sp ← splitNodeOpProg (x.1.1.1, x.2.2)
  let leftIdx ← pure x.2.1.1
  let rightIdx ← pure (x.2.1.1 + 1)
  let newAlloc ← pure (x.2.1.1 + 2)
  let rShift ← pure (rightIdx <<< wpWVal x.1.1.1)
  let newVals ← pure (leftIdx + rShift)
  let mRoot ← pure 2
  writeSplitFourOpProg (x.1, (((leftIdx, sp.1), (rightIdx, sp.2.2)),
    ((x.2.1.2, (mRoot, (sp.2.1, newVals))), newAlloc)))
  pure (newAlloc, x.2.1.2)

private theorem realizes_splitFullRootBody :
    Realizes .exact splitFullRootBody
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ℕ × ℕ))
      SplitFullRootPre
      (fun _ _ => 0) := by
  have hsp := realizes_splitNodeOp
  have hsf := realizes_writeSplitFourOp
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, sIdx⟩, ⟨⟨alloc, root⟩, ⟨mW, ⟨kW, vW⟩⟩⟩⟩
    obtain ⟨c, U, V, _, n_max, henv, rfl, hsIdx, halloc2, hrt_lt⟩ := h
    rcases henv.2.2.1 with rfl
    have hth := henv.2.2.2.1
    have ht8 := eight_le_tMinWhp hth
    have hns_lt_n := (large_bounds_lt_n_max hth).2.1
    obtain ⟨_, _, _, hns_lt_v⟩ := (btree_slice_param_bounds hth).1
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    simp only [wp_large_M hth] at *
    try simp only [wp_large_nSlice hth] at *
    try simp only [wp_large_wVal hth] at *
    have h2v : alloc + ((alloc + 1) <<< valLaneBitsWhp n_max) <
        2 ^ (2 * valLaneBitsWhp n_max) := by
      rw [Nat.shiftLeft_eq, two_mul, Nat.pow_add]
      have h1 : alloc + 2 ≤ 2 ^ valLaneBitsWhp n_max :=
        (by omega : alloc + 1 < nSliceWhp n_max).trans hns_lt_v
      calc alloc + (alloc + 1) * 2 ^ valLaneBitsWhp n_max
          < 2 ^ valLaneBitsWhp n_max + (alloc + 1) * 2 ^ valLaneBitsWhp n_max := by omega
        _ = (alloc + 2) * 2 ^ valLaneBitsWhp n_max := by ring
        _ ≤ 2 ^ valLaneBitsWhp n_max * 2 ^ valLaneBitsWhp n_max := Nat.mul_le_mul_right _ h1
    have h2v_w : 2 * valLaneBitsWhp n_max < w :=
      (Nat.mul_le_mul_right _ (by omega : 2 ≤ 2 * tMinWhp n_max)).trans_lt hvw_lt
    have hfit2 : alloc + ((alloc + 1) <<< valLaneBitsWhp n_max) < 2 ^ w :=
      h2v.trans (Nat.pow_lt_pow_right (by decide) h2v_w)
    first
    | omega
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨base, c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact (Nat.le_add_left _ _).trans_lt hfit2
    | exact hfit2

/-- Opaque full-root split subroutine for `ensureAndSplitRootGenProg`. -/
@[irreducible] private def splitFullRootOpProg
    (x : ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) : Memory.Prog (ℕ × ℕ) :=
  splitFullRootBody x

private theorem realizes_splitFullRootOp :
    Realizes .exact splitFullRootOpProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ℕ × ℕ))
      SplitFullRootPre
      (fun _ _ => 0) := by
  unfold splitFullRootOpProg; exact realizes_splitFullRootBody


/-- Precondition for `ensureAndSplitRootGenProg` (`d = ((cp, base), sIdx)`). -/
@[expose] def EnsureRootGenPre (w : ℕ) :
    (WhpCoreParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, base), sIdx), s =>
    ∃ c U V w₀ n_max insCount sl mapFn,
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      sIdx < 3 * numBucketsWhp n_max ∧
      insCount ≤ 8 * (slabScale n_max) ^ 12 ∧
      BTreeSliceMemRep base c U V w₀ n_max sIdx sl s.mem ∧
      ValidWhpSlice n_max insCount sl mapFn

/-- Parameter-free `splitRootIfFull ∘ ensureRootSlice` (`d = ((cp, base), sIdx)`), returning
`(alloc1, root1)`. -/
def ensureAndSplitRootGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, base), sIdx) => do
    let hdr ← readSliceHeaderGenProg ((cp, base), sIdx)
    let z0 ← pure 0
    if hdr.1 = z0 then
      initEmptyRootOpProg ((cp, base), sIdx)
    else do
      let rootNd ← readBTreeNodeGenProg (((cp, base), sIdx), hdr.2)
      let cnt ← pure (rootNd.1 / 2)
      let fullCnt ← pure (2 * wpTMin cp - 1)
      if cnt = fullCnt then
        splitFullRootOpProg (((cp, base), sIdx), (hdr, rootNd))
      else
        pure hdr

/-- Running a program `p` that leaves the state unchanged and returns `r`, then `k`, has the
state, result, validity and (up to the cost of `p`) cost of running `k r`. -/
private theorem bind_of_readOnly {α : Type} {w B : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {r : α} (hst : (Memory.spec 0).clientState s p = s)
    (hres : (Memory.spec 0).clientResult s p = r)
    (hvp : ValidProg w B s p) : ∀ (β : Type) (k : α → Memory.Prog β),
    (Memory.spec 0).clientState s (p >>= k) = (Memory.spec 0).clientState s (k r) ∧
    (Memory.spec 0).clientResult s (p >>= k) = (Memory.spec 0).clientResult s (k r) ∧
    memoryCost (p >>= k) s = memoryCost p s + memoryCost (k r) s ∧
    (ValidProg w B s (p >>= k) ↔ ValidProg w B s (k r)) := fun _ k => by
  refine ⟨by rw [clientState_bind, hst, hres], by rw [clientResult_bind, hst, hres],
    by rw [memoryCost_bind', hst, hres], fun h hm => ?_, fun h => validProg_bind hvp ?_⟩
  · have := ((validHistory_bind' w p k s).mp (h hm)).2
    rwa [hst, hres] at this
  · rwa [hst, hres]

theorem ensureAndSplitRootGenProg_spec {c U V w n_max base sIdx insCount : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hv : ValidWhpSlice n_max insCount sl mapFn) :
    let prog := ensureAndSplitRootGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx)
    let sl1 := splitRootIfFull (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (ensureRootSlice sl)
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    (Memory.spec 0).clientResult s prog = (sl1.alloc, sl1.root) ∧
    memoryCost prog s ≤ 50 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx sl1 s'.mem ∧
    sl1.alloc + hMaxBTree < nSliceWhp n_max ∧
    (∃ T1 : BTreeTree,
      T1.rootIdx = sl1.root ∧
      T1.height ≤ hMaxBTree ∧
      metaCount (sl1.nodes sl1.root).metaWord < 2 * tMinWhp n_max - 1 ∧
      ValidSubtree true (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl1.alloc sl1.nodes 0 (2 ^ fpBitsWhp n_max - 1) mapFn T1) ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ idx < 16 * numBucketsWhp n_max,
      idx ≠ 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) →
      idx ≠ 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3) →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, (a < base + offBktMeta c U V w n_max ∨
        (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
        base + offTrieChild0 c U V w n_max ≤ a) →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have ht8 := eight_le_tMinWhp hth
  have h64 := sixty_four_le_nSliceWhp n_max
  obtain ⟨ht3, hmeta_cap, _, hns_lt⟩ := (btree_slice_param_bounds hth).1
  obtain ⟨hcs_h, hres_h, hmc_h, hvp_h⟩ := readSliceHeaderGenProg_spec hth hw hsIdx hrep (s := s)
  have hH := bind_of_readOnly hcs_h hres_h hvp_h
  unfold ensureAndSplitRootGenProg initEmptyRootOpProg initEmptyRootBody
    splitFullRootOpProg splitFullRootBody writeNodeOpProg splitNodeOpProg
  simp only [wp_large_tMin hth, wp_large_wVal hth, pure_bind]
  rw [(hH _ _).1, (hH _ _).2.1, (hH _ _).2.2.1, (hH _ _).2.2.2, hmc_h]
  obtain ⟨halloc_lt, ⟨ha0, rfl⟩ | ⟨ha_pos, T, hrt, hht_T, _, _, hT⟩⟩ :=
    hv.alloc_and_height_lt hth hins
  · -- Case 1: `sl.alloc = 0` (`ensureRootSlice` creates a 1-node empty leaf, no root split)
    have hsl1_eq : splitRootIfFull (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (ensureRootSlice sl) =
        { alloc := 1, root := 0, nodes := Function.update sl.nodes 0 ⟨1, 0, 0⟩ } := by
      have hne0 : 0 ≠ 2 * tMinWhp n_max - 1 := by omega
      simp [ensureRootSlice, splitRootIfFull, ha0, mkNodeMeta, metaCount, hne0]
    set p0 := (mkWhpCoreParams c U V w n_max, base)
    set wN := writeBTreeNodeGenProg (((p0, sIdx), 0), (1, (0, 0)))
    set wH := writeSliceHeaderGenProg ((p0, sIdx), (1, 0))
    set s1 := (Memory.spec 0).clientState s wN
    have h1_meta : 1 < 2 ^ nodeMetaBitsWhp n_max :=
      Nat.one_lt_two_pow (by unfold nodeMetaBitsWhp; have := one_le_logLogFactor n_max; omega)
    obtain ⟨hfrN, hmcN, hvpN, hupN, hothN, houtN⟩ :=
      writeBTreeNodeGenProg_spec (u := 0) (nd := ⟨1, 0, 0⟩) henv hsIdx (by omega)
        h1_meta (Nat.two_pow_pos _) (Nat.two_pow_pos _) (s := s)
    dsimp only at hfrN hmcN hvpN hupN hothN houtN
    have hnodes_s1 : ∀ u < 1,
        let idx := sIdx * nSliceWhp n_max + u
        readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s1.mem idx =
          (Function.update sl.nodes 0 ⟨1, 0, 0⟩ u).metaWord ∧
        readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s1.mem idx =
          (Function.update sl.nodes 0 ⟨1, 0, 0⟩ u).keysWord ∧
        readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s1.mem idx =
          (Function.update sl.nodes 0 ⟨1, 0, 0⟩ u).valsWord :=
      hupN ⟨1, 0, sl.nodes⟩ (by dsimp; omega)
        fun v hv hne => absurd (by dsimp at hv; omega : v = 0) hne
    obtain ⟨hfrH, hmcH, hvpH, hrepH, hothH, hbmH, houtH⟩ :=
      writeSliceHeaderGenProg_sliceRep (newA := 1) (newR := 0)
        (nodes := Function.update sl.nodes 0 ⟨1, 0, 0⟩)
        henv hsIdx (by omega) (by omega) hnodes_s1 (s := s1)
    have hoff := largeOffsetChain c U V w n_max
    simp only [ha0, ↓reduceIte]
    rw [clientState_bind, clientState_bind_pure, clientResult_bind, clientResult_bind_pure, hsl1_eq]
    refine ⟨hfrH.trans hfrN, rfl, ?_, validProg_bind hvpN (validProg_bind hvpH (validProg_pure _)),
      hrepH, by simp only [hMaxBTree_eq]; omega, ?_,
      fun sIdx' hsIdx' hne sl₂ hr₂ => hothH sIdx' hsIdx' hne sl₂ (hothN sIdx' hsIdx' hne sl₂ hr₂),
      fun idx hidx h1 h2 => (hbmH idx hidx h1 h2).trans
        (readPacked_congr hw (hidx := hidx) fun a ⟨_, ha2⟩ => houtN a (Or.inl (by omega))), ?_⟩
    · dsimp only [wN, wH, p0]
      rw [memoryCost_bind', memoryCost_bind', hmcN, hmcH, memoryCost_pure]
      omega
    · refine ⟨.leaf 0 0, rfl, by simp [BTreeTree.height],
        by simp [metaCount]; omega, ?_⟩
      dsimp only [ValidSubtree]
      rw [Function.update_self]
      exact ⟨by omega, rfl, by omega, by positivity, by positivity,
        fun _ hj => absurd hj (Nat.not_lt_zero _),
        fun _ _ _ hj => absurd hj (Nat.not_lt_zero _),
        fun _ _ _ => Or.inr ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), rfl⟩⟩
    · intro a ha
      rcases ha with ha1 | ⟨ha2, ha3⟩ | ha4
      · exact (houtH a (Or.inl ha1)).trans (houtN a (Or.inl (by omega)))
      · exact (houtH a (Or.inr ha2)).trans (houtN a (Or.inl ha3))
      · exact (houtH a (Or.inr (by omega))).trans (houtN a (Or.inr ha4))
  · -- Case 2: `1 ≤ sl.alloc` (`ensureRootSlice sl = sl`)
    have ha_ne : sl.alloc ≠ 0 := by omega
    have hens : ensureRootSlice sl = sl := by unfold ensureRootSlice; simp [ha_ne]
    have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
      Nat.sub_lt (Nat.two_pow_pos _) one_pos
    obtain ⟨hrt_lt, hcnt_le, hm_rt, _, hk_rt, hv_rt, _⟩ := validSubtree_root_bounds hth hhi hT
    rw [hrt] at hrt_lt hcnt_le hm_rt hk_rt hv_rt
    obtain ⟨hnd_st, hnd_res, hnd_mc, hnd_vp⟩ :=
      readBTreeNodeGenProg_spec hth hw hsIdx hrt_lt hrep (s := s)
    dsimp only at hnd_st hnd_res hnd_mc hnd_vp
    have halloc_val : sl.alloc + 1 < 2 ^ valLaneBitsWhp n_max :=
      (by omega : sl.alloc + 1 < nSliceWhp n_max).trans hns_lt
    obtain ⟨_, ha1_le, hrt1, T1, hT1_rt, hT1_nf, hT1_ht, _, hv1⟩ :=
      splitRootIfFull_spec ht3 ha_pos halloc_val hrt hT
    set sl1 := splitRootIfFull (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl
    have hcnt_div : (sl.nodes sl.root).metaWord / 2 = metaCount (sl.nodes sl.root).metaWord := rfl
    have hN := bind_of_readOnly hnd_st hnd_res hnd_vp
    simp only [ha_ne, ↓reduceIte]
    rw [(hN _ _).1, (hN _ _).2.1, (hN _ _).2.2.1, (hN _ _).2.2.2, hnd_mc]
    dsimp only
    rw [hcnt_div]
    by_cases hfull : metaCount (sl.nodes sl.root).metaWord = 2 * tMinWhp n_max - 1
    · -- Subcase 2a: Full root (`splitRootIfFull` splits into `sl.alloc`, `sl.alloc + 1`, `sl.root`)
      set spPure := splitFullNode (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (sl.nodes sl.root)
      obtain ⟨hlM, hlK, hlV, hsep_lt, hrM, hrK, hrV⟩ := splitFullNode_bits_lt hth hk_rt hv_rt
      let newVals := sl.alloc + ((sl.alloc + 1) <<< valLaneBitsWhp n_max)
      let newRootNd : BTreeNode := ⟨2, spPure.sep, newVals⟩
      have hm3 : newRootNd.metaWord < 2 ^ nodeMetaBitsWhp n_max := by dsimp only [newRootNd]; omega
      have hk3 : newRootNd.keysWord < 2 ^ keysWordBitsWhp n_max :=
        hsep_lt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by omega)))
      have hv3 : newRootNd.valsWord < 2 ^ valsWordBitsWhp n_max := by
        dsimp only [newRootNd, newVals]
        have h2v : sl.alloc + ((sl.alloc + 1) <<< valLaneBitsWhp n_max) <
            2 ^ (2 * valLaneBitsWhp n_max) := by
          rw [Nat.shiftLeft_eq, two_mul, Nat.pow_add]
          calc sl.alloc + (sl.alloc + 1) * 2 ^ valLaneBitsWhp n_max
              < 2 ^ valLaneBitsWhp n_max + (sl.alloc + 1) * 2 ^ valLaneBitsWhp n_max := by omega
            _ = (sl.alloc + 2) * 2 ^ valLaneBitsWhp n_max := by ring
            _ ≤ 2 ^ valLaneBitsWhp n_max * 2 ^ valLaneBitsWhp n_max :=
              Nat.mul_le_mul_right _ halloc_val
        unfold valsWordBitsWhp
        exact h2v.trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
      obtain ⟨hfr4, hmc4, hvp4, hrep4, hoth4, hbm4, hout4⟩ :=
        threeNodeWrites_and_alloc_sliceRep (newA := sl.alloc + 2)
          (idx1 := sl.alloc) (idx2 := sl.alloc + 1) (idx3 := sl.root)
          (nd1 := spPure.left) (nd2 := spPure.right) (nd3 := newRootNd)
          henv hsIdx hrep (by omega) (by omega) (by omega) (by omega)
          (fun v hv => by omega) hlM hlK hlV hrM hrK hrV hm3 hk3 hv3 (s := s)
      have hsl1_def : sl1 = ⟨sl.alloc + 2, sl.root,
          Function.update (Function.update (Function.update sl.nodes sl.alloc spPure.left)
            (sl.alloc + 1) spPure.right) sl.root newRootNd⟩ := by
        simp [sl1, splitRootIfFull, hfull, mkNodeMeta]; rfl
      have hsp_res := clientResult_splitFullNodeGenProg (U := U) (V := V) (w := w)
        hth (sl.nodes sl.root) s
      dsimp only at hsp_res
      have hS := bind_of_readOnly (clientState_splitFullNodeGenProg _ s) hsp_res
        (validWhpProg_splitFullNodeGenProg (w := w) (F := base + largeSpaceWhp c U V w n_max) _)
      simp only [hfull, ↓reduceIte]
      rw [(hS _ _).1, (hS _ _).2.1, (hS _ _).2.2.1, (hS _ _).2.2.2, memoryCost_splitFullNodeGenProg]
      dsimp only
      rw [clientState_bind_pure, clientResult_bind_pure, memoryCost_bind', memoryCost_pure,
        writeSplitFourOpProg_eq]
      dsimp only [sl1] at hsl1_def ha1_le hrt1 hT1_rt hT1_nf hv1
      rw [hens]
      refine ⟨hfr4, by rw [hsl1_def], by rw [hmc4], validProg_bind hvp4 (validProg_pure _),
        hsl1_def.symm ▸ hrep4, by omega, ⟨T1, hT1_rt, by omega, hT1_nf, hv1⟩, hoth4,
        fun idx hidx h1 _ => hbm4 idx hidx h1, hout4⟩
    · -- Subcase 2b: Non-full root (`splitRootIfFull sl = sl`)
      have hsl1_eq : sl1 = sl := by simp [sl1, splitRootIfFull, hfull]
      simp only [hfull, ↓reduceIte]
      dsimp only [sl1] at hsl1_eq
      rw [hens, hsl1_eq, memoryCost_pure]
      exact ⟨rfl, rfl, by omega, validProg_pure _, hrep, by omega, ⟨T, hrt, hht_T.le, by omega, hT⟩,
        fun _ _ _ _ hr => hr, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem realizes_ensureAndSplitRootGen :
    Realizes .exact ensureAndSplitRootGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      EnsureRootGenPre
      (fun _ _ => 0) := by
  unfold ensureAndSplitRootGenProg
  have hrh := realizes_readSliceHeaderGen
  have hie := realizes_initEmptyRootOp
  have hrn := realizes_readBTreeNodeGen
  have hsr := realizes_splitFullRootOp
  realize
  all_goals
    rcases d with ⟨⟨cp, base⟩, sIdx⟩
    obtain ⟨c, U, V, _, n_max, insCount, sl, mapFn, henv, rfl, hsIdx, hins, hrep, hv⟩ := h
    rcases henv.2.2.1 with rfl
    have hth := henv.2.2.2.1
    have ht8 := eight_le_tMinWhp hth
    have h64 := sixty_four_le_nSliceWhp n_max
    obtain ⟨hcs_h, hres_h, _, _⟩ := readSliceHeaderGenProg_spec hth henv.2.1 hsIdx hrep (s := s)
    dsimp only at hcs_h hres_h
    simp only [hcs_h, hres_h] at *
    try simp only [wp_large_M hth] at *
    try simp only [wp_large_nSlice hth] at *
    try simp only [wp_large_tMin hth] at *
    obtain ⟨halloc_lt, ⟨ha0, _⟩ | ⟨ha_pos, T, hrt, _, _, _, hT⟩⟩ :=
      hv.alloc_and_height_lt hth hins
    · first
      | decide
      | omega
      | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    · have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
        Nat.sub_lt (Nat.two_pow_pos _) one_pos
      obtain ⟨hrt_lt, _, _, _, _, _, _⟩ := validSubtree_root_bounds hth hhi hT
      rw [hrt] at hrt_lt
      obtain ⟨hnd_st, hnd_res, _, _⟩ := readBTreeNodeGenProg_spec hth henv.2.1 hsIdx hrt_lt hrep
        (s := s)
      dsimp only at hnd_st hnd_res
      simp only [hnd_st, hnd_res] at *
      have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
      try dsimp only [SplitFullRootPre]
      first
      | decide
      | omega
      | exact henv.fits_const (by decide)
      | exact ⟨c, U, V, w, n_max, henv, rfl⟩
      | exact ((Nat.le_mul_of_pos_right _ (by unfold keyLaneBitsWhp; positivity)).trans_lt
          hkw_lt).trans Nat.lt_two_pow_self
      | exact ⟨c, U, V, w, n_max, henv, rfl, hsIdx, by omega, hrt_lt⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
