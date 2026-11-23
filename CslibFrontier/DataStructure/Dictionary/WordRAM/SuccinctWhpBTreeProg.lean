/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg
import CslibFrontier.Tactic.Realize

/-!
# Certified `Memory.Prog` Implementation of the SWAR Top-Down B+-Tree Query-Mapper

This module implements the bounded-depth SWAR top-down split-only B+-tree operations
(`btreeLookupGenProg`, `btreeDeleteGenProg`, `btreeUpdateGenProg`, `btreeInsertGenProg`) as
parameter-free `Memory.Prog` subroutines certified over `Basis.exact` with zero local work via
`realize` and `Realizes.iterate₀`. Every operation runs in `O(1)` (`≤ 2426`) memory charges and
refines the pure operations (`btreeLookup`, `btreeDelete`, `btreeUpdate`, `btreeInsert`) under
`BTreeSliceMemRep` and `ValidWhpSlice`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeLookupGenProg`,
  `btreeDeleteGenProg`, `btreeUpdateGenProg`, `btreeInsertGenProg`:
  parameter-free `Memory.Prog` implementations of all four SWAR B+-tree operations.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_btreeLookupGen`,
  `realizes_btreeDeleteGen`, `realizes_btreeUpdateGen`, `realizes_btreeInsertGen`:
  parameter-free `Realizes .exact` certificates.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeLookupGenProg_spec`,
  `btreeDeleteGenProg_spec`, `btreeUpdateGenProg_spec`, `btreeInsertGenProg_spec`:
  exact refinement, `O(1)` `memoryCost` bounds, `ValidProg`, and slice/segment frame laws.
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

/-! ## Section 1: Root/Subtree Bit-Width Helpers and Header Write Frame Laws -/

private theorem validWhpProg_laneGetGenProg {w F : ℕ} {s : Memory.State}
    (d : (ℕ × ℕ) × ℕ) : ValidProg w F s (laneGetGenProg d) := by
  unfold laneGetGenProg; simp only [pure_bind]; exact validProg_pure _

private theorem validWhpProg_wordInsertAtGenProg {w F : ℕ} {s : Memory.State}
    (d : ((ℕ × ℕ) × ℕ) × ℕ) : ValidProg w F s (wordInsertAtGenProg d) := by
  unfold wordInsertAtGenProg; simp only [pure_bind]; exact validProg_pure _

private theorem validWhpProg_wordDeleteAtGenProg {w F : ℕ} {s : Memory.State}
    (d : (ℕ × ℕ) × ℕ) : ValidProg w F s (wordDeleteAtGenProg d) := by
  unfold wordDeleteAtGenProg; simp only [pure_bind]; exact validProg_pure _

private theorem validWhpProg_wordUpdateAtGenProg {w F : ℕ} {s : Memory.State}
    (d : ((ℕ × ℕ) × ℕ) × ℕ) : ValidProg w F s (wordUpdateAtGenProg d) := by
  unfold wordUpdateAtGenProg; simp only [pure_bind]; exact validProg_pure _

private theorem validWhpProg_swarRankGenProg {w F : ℕ} {s : Memory.State}
    (d : WhpCoreParams × ((ℕ × ℕ) × ℕ)) : ValidProg w F s (swarRankGenProg d) := by
  unfold swarRankGenProg; simp only [pure_bind]; exact validProg_pure _

private theorem btree_slice_param_bounds {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    (3 ≤ tMinWhp n_max ∧
      4 * tMinWhp n_max ≤ 2 ^ nodeMetaBitsWhp n_max ∧
      2 * tMinWhp n_max < 2 ^ keyLaneBitsWhp n_max ∧
      nSliceWhp n_max < 2 ^ valLaneBitsWhp n_max) ∧
    8 ≤ tMinWhp n_max := by
  have h8 := eight_le_tMinWhp hth
  have hell := one_le_logLogFactor n_max
  have ht_le_L := tMinWhp_le_slabScale n_max
  have hmeta_lt : 4 * tMinWhp n_max ≤ 2 ^ nodeMetaBitsWhp n_max := by
    calc 4 * tMinWhp n_max ≤ 4 * slabScale n_max := Nat.mul_le_mul_left 4 ht_le_L
      _ = 2 ^ 2 * 2 ^ logLogFactor n_max := rfl
      _ = 2 ^ (logLogFactor n_max + 2) := by rw [← Nat.pow_add, add_comm]
      _ ≤ 2 ^ nodeMetaBitsWhp n_max := by
          unfold nodeMetaBitsWhp; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hkey_lt : 2 * tMinWhp n_max < 2 ^ keyLaneBitsWhp n_max := by
    have hpow : slabScale n_max ≤ 2 ^ fpBitsWhp n_max := by
      calc slabScale n_max = 2 ^ logLogFactor n_max := rfl
        _ ≤ 2 ^ fpBitsWhp n_max := by
            unfold fpBitsWhp; exact Nat.pow_le_pow_right (by decide) (by omega)
    have hfp_pos : 0 < 2 ^ fpBitsWhp n_max := Nat.two_pow_pos _
    calc 2 * tMinWhp n_max ≤ 2 * 2 ^ fpBitsWhp n_max :=
          Nat.mul_le_mul_left 2 (ht_le_L.trans hpow)
      _ < 4 * 2 ^ fpBitsWhp n_max := by omega
      _ = 2 ^ keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp; rw [Nat.pow_add]; ring
  have hnslice_lt : nSliceWhp n_max < 2 ^ valLaneBitsWhp n_max := by
    have hL2 := two_le_slabScale n_max
    have hL12_ge : 4096 ≤ (slabScale n_max) ^ 12 := by
      calc 4096 = 2 ^ 12 := by decide
        _ ≤ (slabScale n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
    have hdiv_le : 32 * (slabScale n_max) ^ 12 / (tMinWhp n_max - 1) ≤
        32 * (slabScale n_max) ^ 12 := Nat.div_le_self _ _
    unfold nSliceWhp
    rw [two_pow_valLaneBitsWhp]
    omega
  exact ⟨⟨by omega, hmeta_lt, hkey_lt, hnslice_lt⟩, h8⟩

private theorem validWhpProg_splitFullNodeGenProg {w F : ℕ} {s : Memory.State}
    (d : WhpCoreParams × (ℕ × (ℕ × ℕ))) : ValidProg w F s (splitFullNodeGenProg d) := by
  unfold splitFullNodeGenProg
  simp only [pure_bind]
  refine validProg_bind (validWhpProg_laneGetGenProg _) ?_
  rw [clientState_laneGetGenProg]
  split_ifs <;>
    (unfold wordTakeLowGenProg wordDropLowGenProg
     simp only [pure_bind]
     exact validProg_pure _)

private theorem descendToLeaf_leaf {isRoot : Bool}
    {fpBits W_val tMin alloc lo hi q fuel : ℕ}
    {nodes : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T)
    (hhi : hi < 2 ^ fpBits) (hqlo : lo ≤ q) (hqhi : q ≤ hi) (hfuel : T.height ≤ fuel) :
    ∃ cnt loL hiL,
      hiL ≤ hi ∧
      ValidSubtree false fpBits W_val tMin alloc nodes loL hiL mapFn
        (.leaf (descendToLeaf fpBits W_val tMin nodes fuel T.rootIdx q) cnt) := by
  induction T generalizing isRoot lo hi fuel with
  | leaf idx cnt =>
    have hdesc : descendToLeaf fpBits W_val tMin nodes fuel idx q = idx := by
      cases fuel with
      | zero => rfl
      | succ _ => simp only [descendToLeaf, hv.2.1, metaIsLeaf_mkNodeMeta, ↓reduceIte]
    exact ⟨cnt, lo, hi, le_rfl, by dsimp only [BTreeTree.rootIdx]; rw [hdesc]; exact hv⟩
  | branch idx cnt cs ih =>
    obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by simp only [BTreeTree.height] at hfuel; omega⟩
    obtain ⟨hr_le, hclo_q, hq_chi, _⟩ := branch_child_routing ht2 hcap hv hhi hqlo hqhi
    obtain ⟨_, hmeta, _, _, _, _, _, hhi_last, hmono, _, _, hht, hcs⟩ := hv
    let r_fin : Fin (cnt + 1) := ⟨swarRank fpBits (2 * tMin) cnt q (nodes idx).keysWord,
      Nat.lt_succ_of_le hr_le⟩
    have hdesc_step : descendToLeaf fpBits W_val tMin nodes (fuel' + 1) idx q =
        descendToLeaf fpBits W_val tMin nodes fuel' (cs r_fin).rootIdx q := by
      simp only [descendToLeaf, hmeta, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta,
        Bool.false_eq_true, ↓reduceIte]
      rw [show swarRank fpBits (2 * tMin) cnt q (nodes idx).keysWord = r_fin.val from rfl,
        (hcs r_fin).1]
    have hchi_le : childHi (fpBits + 2) hi cnt (nodes idx).keysWord r_fin.val ≤ hi :=
      childHi_le hhi_last.le hmono
    have hfuel_c : (cs r_fin).height ≤ fuel' := by
      rw [BTreeTree.height_branch_of_eq hht] at hfuel
      rw [hht r_fin]; omega
    obtain ⟨cntL, loL, hiL, hhiL1, hv_leaf⟩ :=
      ih r_fin (hcs r_fin).2 (hchi_le.trans_lt hhi) hclo_q hq_chi hfuel_c
    exact ⟨cntL, loL, hiL, hhiL1.trans hchi_le,
      by dsimp only [BTreeTree.rootIdx]; rwa [hdesc_step]⟩

/-- Packed bit-width and SWAR preconditions at the root of any `ValidSubtree` in the large
regime. -/
private theorem validSubtree_root_bounds {isRoot : Bool} {c n_max alloc lo hi : ℕ}
    {nodes : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (hth : whpThreshold c ≤ n_max) (hhi : hi < 2 ^ fpBitsWhp n_max)
    (hv : ValidSubtree isRoot (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      alloc nodes lo hi mapFn T) :
    let nd := nodes T.rootIdx
    let cnt := metaCount nd.metaWord
    T.rootIdx < alloc ∧
    cnt ≤ 2 * tMinWhp n_max - 1 ∧
    nd.metaWord < 2 ^ nodeMetaBitsWhp n_max ∧
    nd.keysWord < 2 ^ (cnt * keyLaneBitsWhp n_max) ∧
    nd.keysWord < 2 ^ keysWordBitsWhp n_max ∧
    nd.valsWord < 2 ^ valsWordBitsWhp n_max ∧
    (∀ j < cnt, laneGet (keyLaneBitsWhp n_max) nd.keysWord j < 2 ^ fpBitsWhp n_max) := by
  obtain ⟨ht3, hmeta_cap, _, _⟩ := (btree_slice_param_bounds hth).1
  have hbits := hv.node_bits_lt (by omega) hmeta_cap T.rootIdx T.rootIdx_mem_nodeSet
  cases T with
  | leaf idx c0 =>
    obtain ⟨hidx, hmeta, hc_le, hkw, _, hbounds, _, _⟩ := hv
    dsimp only [BTreeTree.rootIdx] at hbits ⊢
    have hcnt_eq : metaCount (nodes idx).metaWord = c0 := by rw [hmeta, metaCount_mkNodeMeta]
    rw [hcnt_eq]
    exact ⟨hidx, hc_le, hbits.1, hkw, hbits.2.1, hbits.2.2,
      fun j hj => ((hbounds j hj).2).trans_lt hhi⟩
  | branch idx c0 cs =>
    obtain ⟨hidx, hmeta, hdeg, hc_le, hkw, _, _, hhi_last, hmono, _, _, _, _⟩ := hv
    dsimp only [BTreeTree.rootIdx] at hbits ⊢
    have hcnt_eq : metaCount (nodes idx).metaWord = c0 := by rw [hmeta, metaCount_mkNodeMeta]
    rw [hcnt_eq]
    refine ⟨hidx, hc_le, hbits.1, hkw, hbits.2.1, hbits.2.2, fun j hj => ?_⟩
    rcases eq_or_lt_of_le (by omega : j ≤ c0 - 1) with rfl | hlt
    · exact hhi_last.trans hhi
    · exact ((hmono j (c0 - 1) hlt (by omega)).trans hhi_last).trans hhi

/-- Write `(alloc, root) = (newA, newR)` for slice `sIdx`. -/
private def writeSliceHeaderGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, base), sIdx), (newA, newR)) => do
    let b ← pure (sIdx / 3)
    let role ← pure (sIdx % 3)
    let idxAlloc ← pure (16 * b + 10 + 2 * role)
    let idxRoot ← pure (16 * b + 11 + 2 * role)
    writePackedGenProg ((((base, wpOffBktMeta cp),
      (wpGlobalPtrBits cp, wpW cp)), idxAlloc), newA)
    writePackedGenProg ((((base, wpOffBktMeta cp),
      (wpGlobalPtrBits cp, wpW cp)), idxRoot), newR)

private theorem realizes_writeSliceHeaderGen :
    Realizes .exact writeSliceHeaderGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), sIdx), _) _ => WhpLargeEnvGen w cp base ∧ sIdx < 3 * wpM cp)
      (fun _ _ => 0) := by
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, sIdx⟩, ⟨newA, newR⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hsIdx⟩ := h
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    simp only [wp_large_M hth, wp_large_offBktMeta hth, wp_large_globalPtrBits hth,
      wp_large_w hth] at hsIdx ⊢
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (by omega)

/-- Updating `(alloc, root)` via `writeSliceHeaderGenProg` establishes `BTreeSliceMemRep` at the new
`(newA, newR)` while framing all other slices, other `bktMeta` fields, and non-`bktMeta` words. -/
private theorem writeSliceHeaderGenProg_sliceRep {c U V w n_max base sIdx newA newR : ℕ}
    {nodes : ℕ → BTreeNode} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hnewA : newA ≤ nSliceWhp n_max) (hnewR : newR ≤ nSliceWhp n_max)
    (hnodes : ∀ u < newA,
      let idx := sIdx * nSliceWhp n_max + u
      readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s.mem idx =
        (nodes u).metaWord ∧
      readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s.mem idx =
        (nodes u).keysWord ∧
      readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s.mem idx =
        (nodes u).valsWord) :
    let prog := writeSliceHeaderGenProg
      (((mkWhpCoreParams c U V w n_max, base), sIdx), (newA, newR))
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx ⟨newA, newR, nodes⟩ s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl',
      BTreeSliceMemRep base c U V w n_max sIdx' sl' s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl' s'.mem) ∧
    (∀ idx < 16 * numBucketsWhp n_max,
      idx ≠ 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) →
      idx ≠ 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3) →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hoff := largeOffsetChain c U V w n_max
  have hba_le : base + offBktMeta c U V w n_max +
      packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by omega
  have hgk : globalPtrBits n_max ≤ w := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hns_lt := (large_bounds_lt_n_max hth).2.1
  have hA_lt : newA < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hR_lt : newR < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  set idxA := 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3)
  set idxR := 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3)
  have hidxA : idxA < 16 * numBucketsWhp n_max := by omega
  have hidxR : idxR < 16 * numBucketsWhp n_max := by omega
  have hAR_ne : idxA ≠ idxR := by omega
  unfold writeSliceHeaderGenProg
  simp only [wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth, pure_bind]
  set mem₁ := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idxA newA
  set mem₂ := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₁ idxR newR
  have hs'_eq : (Memory.spec 0).clientState s
      (writePackedGenProg
        ((((base, offBktMeta c U V w n_max), (globalPtrBits n_max, w)), idxA), newA) >>=
        fun _ => writePackedGenProg
          ((((base, offBktMeta c U V w n_max), (globalPtrBits n_max, w)), idxR), newR)) =
      { mem := mem₂, frontier := s.frontier } := rfl
  rw [hs'_eq]
  have hout : ∀ a, a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a →
      mem₂ a = s.mem a := fun a ha => by
    have hdisj : a < base + offBktMeta c U V w n_max ∨
        base + offBktMeta c U V w n_max +
          packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ≤ a := by omega
    exact (writePacked_outside hw _ hidxR _ (by cases hdisj <;> omega)).trans
      (writePacked_outside hw _ hidxA _ (by cases hdisj <;> omega))
  have hother_bm : ∀ idx < 16 * numBucketsWhp n_max, idx ≠ idxA → idx ≠ idxR →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₂ idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx :=
    fun idx _ h1 h2 =>
      (readPacked_writePacked_of_ne hw mem₁ h2 newR).trans
        (readPacked_writePacked_of_ne hw s.mem h1 newA)
  have hbtM_eq : ∀ i < totalBTreeNodesWhp n_max,
      readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w mem₂ i =
        readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s.mem i :=
    fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega))
  have hbtK_eq : ∀ i < totalBTreeNodesWhp n_max,
      readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w mem₂ i =
        readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s.mem i :=
    fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega))
  have hbtV_eq : ∀ i < totalBTreeNodesWhp n_max,
      readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w mem₂ i =
        readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s.mem i :=
    fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega))
  refine ⟨rfl, rfl, ?_, ?_, ?_, hother_bm, hout⟩
  · refine validProg_bind (validProg_writePacked hw hgk hidxA hba_le) ?_
    change ValidProg w (base + largeSpaceWhp c U V w n_max)
      { mem := mem₁, frontier := s.frontier } _
    exact validProg_writePacked hw hgk hidxR hba_le
  · refine ⟨hnewA, ?_, readPacked_writePacked_self _ _ _ mem₁ idxR hR_lt, fun u hu => ?_⟩
    · exact (readPacked_writePacked_of_ne hw mem₁ hAR_ne newR).trans
        (readPacked_writePacked_self _ _ _ s.mem idxA hA_lt)
    · have hu_ns : u < nSliceWhp n_max := hu.trans_le hnewA
      have hidx_n : sIdx * nSliceWhp n_max + u < totalBTreeNodesWhp n_max := by
        unfold totalBTreeNodesWhp
        calc sIdx * nSliceWhp n_max + u < sIdx * nSliceWhp n_max + nSliceWhp n_max :=
              Nat.add_lt_add_left hu_ns _
          _ = (sIdx + 1) * nSliceWhp n_max := by ring
          _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx
      exact ⟨(hbtM_eq _ hidx_n).trans (hnodes u hu).1,
        (hbtK_eq _ hidx_n).trans (hnodes u hu).2.1,
        (hbtV_eq _ hidx_n).trans (hnodes u hu).2.2⟩
  · intro sIdx' hsIdx' hne sl' hrep'
    dsimp only at hrep' ⊢
    refine ⟨hrep'.1,
      (hother_bm _ (by omega) (by omega) (by omega)).trans hrep'.2.1,
      (hother_bm _ (by omega) (by omega) (by omega)).trans hrep'.2.2.1,
      fun u hu => ?_⟩
    have hu_ns : u < nSliceWhp n_max := hu.trans_le hrep'.1
    have hidx_n : sIdx' * nSliceWhp n_max + u < totalBTreeNodesWhp n_max := by
      unfold totalBTreeNodesWhp
      calc sIdx' * nSliceWhp n_max + u < sIdx' * nSliceWhp n_max + nSliceWhp n_max :=
            Nat.add_lt_add_left hu_ns _
        _ = (sIdx' + 1) * nSliceWhp n_max := by ring
        _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx'
    exact ⟨(hbtM_eq _ hidx_n).trans (hrep'.2.2.2 u hu).1,
      (hbtK_eq _ hidx_n).trans (hrep'.2.2.2 u hu).2.1,
      (hbtV_eq _ hidx_n).trans (hrep'.2.2.2 u hu).2.2⟩

/-- Updating `alloc` alone via `writeSliceAllocGenProg` establishes `BTreeSliceMemRep` at `newA`
while framing all other slices, other `bktMeta` fields, and non-`bktMeta` words. -/
private theorem writeSliceAllocGenProg_sliceRep {c U V w n_max base sIdx newA root0 : ℕ}
    {nodes : ℕ → BTreeNode} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hnewA : newA ≤ nSliceWhp n_max)
    (hroot : readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
      (16 * (sIdx / 3) + 11 + 2 * (sIdx % 3)) = root0)
    (hnodes : ∀ u < newA,
      let idx := sIdx * nSliceWhp n_max + u
      readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s.mem idx =
        (nodes u).metaWord ∧
      readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s.mem idx =
        (nodes u).keysWord ∧
      readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s.mem idx =
        (nodes u).valsWord) :
    let prog := writeSliceAllocGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), newA)
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx ⟨newA, root0, nodes⟩ s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl',
      BTreeSliceMemRep base c U V w n_max sIdx' sl' s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl' s'.mem) ∧
    (∀ idx < 16 * numBucketsWhp n_max,
      idx ≠ 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  obtain ⟨hs'_eq, hcost, hvprog⟩ := writeSliceAllocGenProg_spec hth hw henv.2.2.2.2.1
    henv.2.2.2.2.2.1 hsIdx (s := s) (newAlloc := newA)
  dsimp only at hs'_eq hcost hvprog ⊢
  rw [hs'_eq]
  have hoff := largeOffsetChain c U V w n_max
  have hns_lt := (large_bounds_lt_n_max hth).2.1
  have hA_lt : newA < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  set idxA := 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3)
  set idxR := 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3)
  have hidxA : idxA < 16 * numBucketsWhp n_max := by omega
  set mem₁ := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idxA newA
  have hout : ∀ a, a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a →
      mem₁ a = s.mem a := fun a ha =>
    writePacked_outside hw _ hidxA _ (by omega)
  have hother_bm : ∀ idx < 16 * numBucketsWhp n_max, idx ≠ idxA →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₁ idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx :=
    fun idx _ h1 => readPacked_writePacked_of_ne hw s.mem h1 newA
  have hbtM_eq : ∀ i < totalBTreeNodesWhp n_max,
      readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w mem₁ i =
        readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s.mem i :=
    fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega))
  have hbtK_eq : ∀ i < totalBTreeNodesWhp n_max,
      readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w mem₁ i =
        readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s.mem i :=
    fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega))
  have hbtV_eq : ∀ i < totalBTreeNodesWhp n_max,
      readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w mem₁ i =
        readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s.mem i :=
    fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega))
  refine ⟨rfl, hcost, hvprog, ?_, ?_, hother_bm, hout⟩
  · refine ⟨hnewA, readPacked_writePacked_self _ _ _ s.mem idxA hA_lt,
      (hother_bm idxR (by omega) (by omega)).trans hroot, fun u hu => ?_⟩
    have hu_ns : u < nSliceWhp n_max := hu.trans_le hnewA
    have hidx_n : sIdx * nSliceWhp n_max + u < totalBTreeNodesWhp n_max := by
      unfold totalBTreeNodesWhp
      calc sIdx * nSliceWhp n_max + u < sIdx * nSliceWhp n_max + nSliceWhp n_max :=
            Nat.add_lt_add_left hu_ns _
        _ = (sIdx + 1) * nSliceWhp n_max := by ring
        _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx
    exact ⟨(hbtM_eq _ hidx_n).trans (hnodes u hu).1,
      (hbtK_eq _ hidx_n).trans (hnodes u hu).2.1,
      (hbtV_eq _ hidx_n).trans (hnodes u hu).2.2⟩
  · intro sIdx' hsIdx' hne sl' hrep'
    dsimp only at hrep' ⊢
    refine ⟨hrep'.1,
      (hother_bm _ (by omega) (by omega)).trans hrep'.2.1,
      (hother_bm _ (by omega) (by omega)).trans hrep'.2.2.1,
      fun u hu => ?_⟩
    have hu_ns : u < nSliceWhp n_max := hu.trans_le hrep'.1
    have hidx_n : sIdx' * nSliceWhp n_max + u < totalBTreeNodesWhp n_max := by
      unfold totalBTreeNodesWhp
      calc sIdx' * nSliceWhp n_max + u < sIdx' * nSliceWhp n_max + nSliceWhp n_max :=
            Nat.add_lt_add_left hu_ns _
        _ = (sIdx' + 1) * nSliceWhp n_max := by ring
        _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx'
    exact ⟨(hbtM_eq _ hidx_n).trans (hrep'.2.2.2 u hu).1,
      (hbtK_eq _ hidx_n).trans (hrep'.2.2.2 u hu).2.1,
      (hbtV_eq _ hidx_n).trans (hrep'.2.2.2 u hu).2.2⟩

/-! ## Section 2: Read-Only Root-to-Leaf Descent (`descendStepGenProg`, `descendLoopGenProg`) -/

/-- Precondition for one read-only descent step `d = ((((cp, base), sIdx), q), cur)`. -/
private def DescendStepGenPre (w : ℕ)
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max sl isRoot lo hi mapFn T,
    WhpLargeEnv c U V w₀ n_max w d.1.1.1.2 ∧
    d.1.1.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    d.1.1.2 < 3 * numBucketsWhp n_max ∧
    BTreeSliceMemRep d.1.1.1.2 c U V w₀ n_max d.1.1.2 sl s.mem ∧
    T.rootIdx = d.2 ∧
    lo ≤ d.1.2 ∧ d.1.2 ≤ hi ∧ hi < 2 ^ fpBitsWhp n_max ∧
    ValidSubtree isRoot (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.alloc sl.nodes lo hi mapFn T

/-- Single step of `descendToLeaf` (`d = ((((cp, base), sIdx), q), cur)`). -/
private def descendStepGenProg
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let nd ← readBTreeNodeGenProg (d.1.1, d.2)
  let isLf ← pure (nd.1 % 2)
  let z1 ← pure 1
  if isLf = z1 then
    pure d.2
  else do
    let cnt ← pure (nd.1 / 2)
    let r ← swarRankGenProg (d.1.1.1.1, ((cnt, d.1.2), nd.2.1))
    laneGetGenProg ((wpWVal d.1.1.1.1, nd.2.2), r)

private theorem memoryCost_descendStepGenProg_pos
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (descendStepGenProg d) s := by
  unfold descendStepGenProg
  rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readBTreeNodeGenProg]
  omega

private theorem realizes_descendStepGen :
    Realizes .exact descendStepGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      DescendStepGenPre
      (fun _ _ => 0) := by
  unfold descendStepGenProg
  have hrn := realizes_readBTreeNodeGen
  have hsr := realizes_swarRankGen
  have hlg := realizes_laneGetGen
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨cp, base⟩, sIdx⟩, q⟩, cur⟩
    dsimp only [DescendStepGenPre] at h
    obtain ⟨c, U, V, w₀, n_max, sl, isRoot, lo, hi, mapFn, T,
      henv, rfl, hsIdx, hrep, hrt, hqlo, hqhi, hhi, hv⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    obtain ⟨hcur_lt, hcnt_le, _, hkw_cnt, _, _, hlanes⟩ := validSubtree_root_bounds hth hhi hv
    rw [hrt] at hcur_lt hcnt_le hkw_cnt hlanes
    obtain ⟨hcs_n, hres_n, _, _⟩ := readBTreeNodeGenProg_spec hth henv.2.1 hsIdx hcur_lt hrep
      (s := s)
    dsimp only at hcs_n hres_n
    have ht8 := eight_le_tMinWhp hth
    have hvw_lt := henv.valsWordBits_lt_w
    try simp only [hcs_n, hres_n, wp_large_M hth, wp_large_nSlice hth, wp_large_wVal hth]
  · exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · exact hsIdx
  · exact hcur_lt.trans_le hrep.1
  · decide
  · exact henv.fits_const (by decide)
  · exact henv.fits_const (by decide)
  · decide
  · exact henv.fits_const (by decide)
  · refine ⟨⟨base, c, U, V, w, n_max, henv, rfl⟩, ?_, ?_, ?_, ?_⟩
    · simp only [wp_large_capLanes hth]; change metaCount (sl.nodes cur).metaWord < _; omega
    · simp only [wp_large_powFp hth]; exact hqhi.trans_lt hhi
    · simp only [wp_large_wKey hth]; exact hkw_cnt
    · simp only [wp_large_wKey hth, wp_large_powFp hth]; exact hlanes
  · exact (Nat.le_mul_of_pos_left _ (by omega)).trans_lt hvw_lt
  · rw [clientResult_swarRankGenProg hth]
    obtain ⟨ht3, _, hkey_lt, _⟩ := (btree_slice_param_bounds hth).1
    have hcnt_eq : (sl.nodes cur).metaWord / 2 = metaCount (sl.nodes cur).metaWord := rfl
    rw [hcnt_eq]
    have hlanes' : ∀ j < metaCount (sl.nodes cur).metaWord,
        laneGet (fpBitsWhp n_max + 2) (sl.nodes cur).keysWord j < 2 ^ fpBitsWhp n_max := hlanes
    have hrank_le : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max)
        (metaCount (sl.nodes cur).metaWord) q (sl.nodes cur).keysWord ≤
        metaCount (sl.nodes cur).metaWord := by
      rw [swarRank_eq_count_lt (by omega) hkey_lt (hqhi.trans_lt hhi) hkw_cnt hlanes']
      exact (card_filter_le _ _).trans_eq (card_range _)
    have hsh_lt : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max)
        (metaCount (sl.nodes cur).metaWord) q (sl.nodes cur).keysWord * valLaneBitsWhp n_max < w :=
      (Nat.mul_le_mul_right _ (hrank_le.trans (by omega : _ ≤ 2 * tMinWhp n_max))).trans_lt hvw_lt
    exact hsh_lt.trans Nat.lt_two_pow_self

/-- Bounded `iterate` loop refining `descendToLeaf` (`d = (((((cp, base), sIdx), q), cur),
fuel)`). -/
private def descendLoopGenProg
    (d : ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate descendStepGenProg d.1.1 d.2 d.1.2

private theorem realizes_descendLoopGen :
    Realizes .exact descendLoopGenProg
      (WordEncoding.encode (α := ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => iterationSafe descendStepGenProg DescendStepGenPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizes_descendStepGen memoryCost_descendStepGenProg_pos

private theorem descendLoopGenProg_spec {isRoot : Bool}
    {c U V w n_max base sIdx q cur fuel lo hi : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {T : BTreeTree} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hrt : T.rootIdx = cur) (hqlo : lo ≤ q) (hqhi : q ≤ hi) (hhi : hi < 2 ^ fpBitsWhp n_max)
    (hv : ValidSubtree isRoot (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.alloc sl.nodes lo hi mapFn T) :
    let d0 := (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
    let prog := descendLoopGenProg ((d0, cur), fuel)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl.nodes fuel cur q ∧
    memoryCost prog s = 6 * fuel ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    iterationSafe descendStepGenProg DescendStepGenPre w d0 fuel cur s := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  obtain ⟨ht3, _, hkey_lt, _⟩ := (btree_slice_param_bounds hth).1
  set d0 := (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
  induction fuel generalizing isRoot cur lo hi T with
  | zero =>
    exact ⟨rfl, rfl, rfl, validProg_pure cur, trivial⟩
  | succ f ih =>
    have hsafe1 : DescendStepGenPre w (d0, cur) s :=
      ⟨c, U, V, w, n_max, sl, isRoot, lo, hi, mapFn, T,
        henv, rfl, hsIdx, hrep, hrt, hqlo, hqhi, hhi, hv⟩
    obtain ⟨hcur_lt, _, _, _, _, _, _⟩ := validSubtree_root_bounds hth hhi hv
    rw [hrt] at hcur_lt
    obtain ⟨hcs_n, hres_n, hmc_n, hvp_n⟩ := readBTreeNodeGenProg_spec hth hw hsIdx hcur_lt hrep
      (s := s)
    dsimp only at hcs_n hres_n hmc_n hvp_n
    cases T with
    | leaf idx c0 =>
      dsimp only [BTreeTree.rootIdx] at hrt
      subst idx
      have hmeta : (sl.nodes cur).metaWord = mkNodeMeta true c0 := hv.2.1
      have hmod1 : (sl.nodes cur).metaWord % 2 = 1 := by
        rw [hmeta]; simp [mkNodeMeta, Nat.add_mul_mod_self_left]
      have hstep_st : (Memory.spec 0).clientState s (descendStepGenProg (d0, cur)) = s := by
        unfold descendStepGenProg
        simp only [pure_bind]
        rw [clientState_bind, hcs_n, hres_n]
        simp only [hmod1, ↓reduceIte]
        rfl
      have hstep_res : (Memory.spec 0).clientResult s (descendStepGenProg (d0, cur)) = cur := by
        unfold descendStepGenProg
        simp only [pure_bind]
        rw [clientResult_bind, hcs_n, hres_n]
        simp only [hmod1, ↓reduceIte, StateTransitionSpec.clientResult_pure]
      have hstep_mc : memoryCost (descendStepGenProg (d0, cur)) s = 6 := by
        unfold descendStepGenProg
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
        rw [memoryCost_bind, hcs_n, hmc_n, hres_n]
        simp only [hmod1, ↓reduceIte, memoryCost_pure]
      have hstep_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
          (descendStepGenProg (d0, cur)) := by
        unfold descendStepGenProg
        simp only [pure_bind]
        refine validProg_bind hvp_n ?_
        rw [hcs_n, hres_n]
        simp only [hmod1, ↓reduceIte]
        exact validProg_pure cur
      obtain ⟨ih_st, ih_res, ih_mc, ih_vp, ih_safe⟩ := ih (cur := cur) rfl hqlo hqhi hhi hv
      have hdesc_eq : descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          sl.nodes (f + 1) cur q =
          descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            sl.nodes f cur q := by
        simp only [descendToLeaf, hmeta, metaIsLeaf_mkNodeMeta, ↓reduceIte]
        cases f with
        | zero => rfl
        | succ f' => simp [descendToLeaf, hmeta]
      dsimp only [descendLoopGenProg, iterate]
      refine ⟨?_, ?_, ?_, ?_, hsafe1, ?_⟩
      · rw [clientState_bind, hstep_st, hstep_res]; exact ih_st
      · rw [clientResult_bind, hstep_st, hstep_res, hdesc_eq]; exact ih_res
      · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_st, hstep_res, hstep_mc]
        change 6 + memoryCost (descendLoopGenProg ((d0, cur), f)) s = 6 * (f + 1)
        rw [ih_mc]; omega
      · refine validProg_bind hstep_vp ?_
        rw [hstep_st, hstep_res]; exact ih_vp
      · rw [hstep_st, hstep_res]; exact ih_safe
    | branch idx c0 cs =>
      dsimp only [BTreeTree.rootIdx] at hrt
      subst idx
      obtain ⟨hr_le, hclo_q, hq_chi, _⟩ := branch_child_routing (by omega) hkey_lt hv hhi hqlo hqhi
      obtain ⟨_, hmeta, _, _, _, _, _, hhi_last, hmono, _, _, _, hcs_sub⟩ := hv
      have hmod0 : (sl.nodes cur).metaWord % 2 ≠ 1 := by
        rw [hmeta]; simp [mkNodeMeta]
      have hcnt_div : (sl.nodes cur).metaWord / 2 = c0 := by
        rw [hmeta]; exact metaCount_mkNodeMeta false c0
      let r_fin : Fin (c0 + 1) := ⟨swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q
        (sl.nodes cur).keysWord, Nat.lt_succ_of_le hr_le⟩
      have hval_r : laneGet (valLaneBitsWhp n_max) (sl.nodes cur).valsWord r_fin.val =
          (cs r_fin).rootIdx := (hcs_sub r_fin).1
      have hchi_le : childHi (fpBitsWhp n_max + 2) hi c0 (sl.nodes cur).keysWord r_fin.val ≤
        hi := by
        unfold childHi
        split_ifs with hrc
        · rcases eq_or_lt_of_le (by omega : r_fin.val ≤ c0 - 1) with heq | hlt
          · rw [heq]; exact hhi_last.le
          · exact (hmono r_fin.val (c0 - 1) hlt (by omega)).le.trans hhi_last.le
        · exact le_rfl
      have hstep_st : (Memory.spec 0).clientState s (descendStepGenProg (d0, cur)) = s := by
        unfold descendStepGenProg
        simp only [pure_bind]
        rw [clientState_bind, hcs_n, hres_n]
        simp only [hmod0, ↓reduceIte]
        rw [clientState_bind, clientState_swarRankGenProg,
          clientState_laneGetGenProg]
      have hstep_res : (Memory.spec 0).clientResult s (descendStepGenProg (d0, cur)) =
          (cs r_fin).rootIdx := by
        unfold descendStepGenProg
        simp only [d0, pure_bind]
        rw [clientResult_bind, hcs_n, hres_n]
        simp only [hmod0, ↓reduceIte, hcnt_div, wp_large_wVal hth]
        rw [clientResult_bind, clientState_swarRankGenProg,
          clientResult_swarRankGenProg hth, clientResult_laneGetGenProg]
        exact hval_r
      have hstep_mc : memoryCost (descendStepGenProg (d0, cur)) s = 6 := by
        unfold descendStepGenProg
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
        rw [memoryCost_bind, hcs_n, hmc_n, hres_n]
        simp only [hmod0, ↓reduceIte]
        rw [memoryCost_bind, clientState_swarRankGenProg, memoryCost_swarRankGenProg,
          memoryCost_laneGetGenProg]
      have hstep_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
          (descendStepGenProg (d0, cur)) := by
        unfold descendStepGenProg
        simp only [pure_bind]
        refine validProg_bind hvp_n ?_
        rw [hcs_n, hres_n]
        simp only [hmod0, ↓reduceIte]
        refine validProg_bind (validWhpProg_swarRankGenProg _) ?_
        rw [clientState_swarRankGenProg]
        exact validWhpProg_laneGetGenProg _
      obtain ⟨ih_st, ih_res, ih_mc, ih_vp, ih_safe⟩ :=
        ih (cur := (cs r_fin).rootIdx) rfl hclo_q hq_chi (hchi_le.trans_lt hhi) (hcs_sub r_fin).2
      have hdesc_eq : descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          sl.nodes (f + 1) cur q =
          descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            sl.nodes f (cs r_fin).rootIdx q := by
        simp only [descendToLeaf, hmeta, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta,
          Bool.false_eq_true, ↓reduceIte]
        rw [hval_r]
      dsimp only [descendLoopGenProg, iterate]
      refine ⟨?_, ?_, ?_, ?_, hsafe1, ?_⟩
      · rw [clientState_bind, hstep_st, hstep_res]; exact ih_st
      · rw [clientResult_bind, hstep_st, hstep_res, hdesc_eq]; exact ih_res
      · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_st, hstep_res, hstep_mc]
        change 6 + memoryCost (descendLoopGenProg ((d0, (cs r_fin).rootIdx), f)) s = 6 * (f + 1)
        rw [ih_mc]; omega
      · refine validProg_bind hstep_vp ?_
        rw [hstep_st, hstep_res]; exact ih_vp
      · rw [hstep_st, hstep_res]; exact ih_safe

/-! ## Section 3: `btreeLookupGenProg`, `btreeDeleteGenProg`, and `btreeUpdateGenProg` -/

/-- Shared precondition for `btreeLookupGenProg` and `btreeDeleteGenProg`
(`d = (((cp, base), sIdx), q)`). -/
@[expose] def BTreeQueryGenPre (w : ℕ) :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, base), sIdx), q), s =>
    ∃ c U V w₀ n_max insCount sl mapFn,
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      sIdx < 3 * numBucketsWhp n_max ∧
      insCount ≤ 8 * (slabScale n_max) ^ 12 ∧
      BTreeSliceMemRep base c U V w₀ n_max sIdx sl s.mem ∧
      ValidWhpSlice n_max insCount sl mapFn ∧
      q < 2 ^ fpBitsWhp n_max

/-- Writing an updated node `nd'` at an already-allocated index `u < sl.alloc` preserves
`BTreeSliceMemRep` for `{ sl with nodes := Function.update sl.nodes u nd' }` and frames all other
slices and non-B+-tree memory words. -/
private theorem writeBTreeNodeGenProg_inPlace_sliceRep {c U V w n_max base sIdx u : ℕ}
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
@[irreducible] private def btreeLocateHitGenProg :
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

private theorem btreeLocateHitGenProg_spec {c U V w n_max base sIdx insCount q : ℕ}
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
  simp only [wp_large_hMaxBTree hth, wp_large_wKey hth, pure_bind]
  obtain ⟨_, ⟨ha0, rfl⟩ | ⟨ha_pos, T, hrt, hht_lt, _, _, hT⟩⟩ :=
    hv.alloc_and_height_lt hth hins
  · refine ⟨?_, ?_, ?_, Or.inl ⟨?_, ?_, by simp [btreeDelete, ha0],
      fun _ => by simp [btreeUpdate, ha0]⟩⟩
    · rw [clientState_bind, hcs_h, hres_h]; simp only [ha0, ↓reduceIte]; rfl
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hcs_h, hmc_h, hres_h]; simp [ha0]
    · refine validProg_bind hvp_h ?_
      rw [hcs_h, hres_h]; simp only [ha0, ↓reduceIte]; exact validProg_pure _
    · rw [clientResult_bind, hcs_h, hres_h]; simp [ha0, StateTransitionSpec.clientResult_pure]
    · rw [← hlk_eq]; simp [btreeLookup, ha0]
  · have ha_ne : sl.alloc ≠ 0 := by omega
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
    have hr_def : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) cnt q
        (sl.nodes leafIdx).keysWord = r := rfl
    have hcnt_div : (sl.nodes leafIdx).metaWord / 2 = cnt := rfl
    have hlf_def : descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl.nodes hMaxBTree sl.root q = leafIdx := rfl
    have hvw_cnt : (sl.nodes leafIdx).valsWord < 2 ^ (cnt * valLaneBitsWhp n_max) := by
      obtain ⟨_, hm0, _, _, hvw0, _⟩ := hv_leaf
      have : cnt = cntL := by dsimp [cnt]; rw [hm0, metaCount_mkNodeMeta]
      rwa [this]
    have hst : (Memory.spec 0).clientState s
        (readSliceHeaderGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx) >>= fun hdr =>
          if hdr.1 = 0 then pure (0, ((0, 0), (0, (0, 0)))) else
            descendLoopGenProg (((((mkWhpCoreParams c U V w n_max, base), sIdx), q), hdr.2),
              hMaxBTree) >>= fun lf =>
            readBTreeNodeGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), lf) >>= fun nd =>
            swarRankGenProg (mkWhpCoreParams c U V w n_max, ((nd.1 / 2, q), nd.2.1)) >>= fun r0 =>
            if r0 < nd.1 / 2 then
              laneGetGenProg ((keyLaneBitsWhp n_max, nd.2.1), r0) >>= fun k_r =>
              if k_r = q then pure (1, ((lf, r0), (nd.1, (nd.2.1, nd.2.2))))
              else pure (0, ((0, 0), (0, (0, 0))))
            else pure (0, ((0, 0), (0, (0, 0))))) = s := by
      rw [clientState_bind, hcs_h, hres_h]; simp only [ha_ne, ↓reduceIte]
      rw [clientState_bind, hdl_st, hdl_res, clientState_bind, hnd_st, hnd_res,
        clientState_bind, clientState_swarRankGenProg]
      split_ifs with hrc
      · rw [clientState_bind, clientState_laneGetGenProg]
        split_ifs <;> rfl
      · rfl
    have hmc : memoryCost
        (readSliceHeaderGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx) >>= fun hdr =>
          if hdr.1 = 0 then pure (0, ((0, 0), (0, (0, 0)))) else
            descendLoopGenProg (((((mkWhpCoreParams c U V w n_max, base), sIdx), q), hdr.2),
              hMaxBTree) >>= fun lf =>
            readBTreeNodeGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), lf) >>= fun nd =>
            swarRankGenProg (mkWhpCoreParams c U V w n_max, ((nd.1 / 2, q), nd.2.1)) >>= fun r0 =>
            if r0 < nd.1 / 2 then
              laneGetGenProg ((keyLaneBitsWhp n_max, nd.2.1), r0) >>= fun k_r =>
              if k_r = q then pure (1, ((lf, r0), (nd.1, (nd.2.1, nd.2.2))))
              else pure (0, ((0, 0), (0, (0, 0))))
            else pure (0, ((0, 0), (0, (0, 0))))) s ≤ 262 := by
      rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hcs_h, hmc_h, hres_h]
      simp only [ha_ne, ↓reduceIte]
      rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hdl_st, hdl_mc, hdl_res,
        ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hnd_st, hnd_mc, hnd_res]
      rw [memoryCost_bind, clientState_swarRankGenProg, memoryCost_swarRankGenProg, hMaxBTree_eq]
      split_ifs with hrc
      · rw [memoryCost_bind, clientState_laneGetGenProg, memoryCost_laneGetGenProg]
        split_ifs <;> simp [memoryCost_pure]
      · simp [memoryCost_pure]
    have hvp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
        (readSliceHeaderGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx) >>= fun hdr =>
          if hdr.1 = 0 then pure (0, ((0, 0), (0, (0, 0)))) else
            descendLoopGenProg (((((mkWhpCoreParams c U V w n_max, base), sIdx), q), hdr.2),
              hMaxBTree) >>= fun lf =>
            readBTreeNodeGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), lf) >>= fun nd =>
            swarRankGenProg (mkWhpCoreParams c U V w n_max, ((nd.1 / 2, q), nd.2.1)) >>= fun r0 =>
            if r0 < nd.1 / 2 then
              laneGetGenProg ((keyLaneBitsWhp n_max, nd.2.1), r0) >>= fun k_r =>
              if k_r = q then pure (1, ((lf, r0), (nd.1, (nd.2.1, nd.2.2))))
              else pure (0, ((0, 0), (0, (0, 0))))
            else pure (0, ((0, 0), (0, (0, 0))))) := by
      refine validProg_bind hvp_h ?_
      rw [hcs_h, hres_h]; simp only [ha_ne, ↓reduceIte]
      refine validProg_bind hdl_vp ?_; rw [hdl_st, hdl_res]
      refine validProg_bind hnd_vp ?_; rw [hnd_st, hnd_res]
      refine validProg_bind (validWhpProg_swarRankGenProg _) ?_
      rw [clientState_swarRankGenProg]
      split_ifs with hrc
      · refine validProg_bind (validWhpProg_laneGetGenProg _) ?_
        rw [clientState_laneGetGenProg]
        split_ifs <;> exact validProg_pure _
      · exact validProg_pure _
    refine ⟨hst, hmc, hvp, ?_⟩
    by_cases hhit : r < cnt ∧ laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r = q
    · obtain ⟨hrc, hkeq⟩ := hhit
      right
      refine ⟨leafIdx, r, ?_, hleaf_lt, hrc, hcnt_le, hm_lt, hk_lt, hkw_cnt, hvw_cnt, ?_, ?_, ?_⟩
      · rw [clientResult_bind, hcs_h, hres_h]; simp only [ha_ne, ↓reduceIte]
        rw [clientResult_bind, hdl_st, hdl_res, clientResult_bind, hnd_st, hnd_res,
          clientResult_bind, clientState_swarRankGenProg, clientResult_swarRankGenProg hth,
          hcnt_div, hr_def]
        simp only [hrc, ↓reduceIte]
        rw [clientResult_bind, clientState_laneGetGenProg, clientResult_laneGetGenProg]
        dsimp only [keyLaneBitsWhp]
        simp [hkeq, StateTransitionSpec.clientResult_pure]
      · rw [← hlk_eq]; unfold btreeLookup
        simp [ha_ne, hlf_def, cnt, r, hrc, hkeq]
      · unfold btreeDelete; simp [ha_ne, leafIdx, cnt, r, hrc, hkeq]
      · intro newVal; unfold btreeUpdate; simp [ha_ne, leafIdx, cnt, r, hrc, hkeq]
    · left
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [clientResult_bind, hcs_h, hres_h]; simp only [ha_ne, ↓reduceIte]
        rw [clientResult_bind, hdl_st, hdl_res, clientResult_bind, hnd_st, hnd_res,
          clientResult_bind, clientState_swarRankGenProg, clientResult_swarRankGenProg hth,
          hcnt_div, hr_def]
        by_cases hrc : r < cnt
        · have hne : laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
            fun heq => hhit ⟨hrc, heq⟩
          simp only [hrc, ↓reduceIte]
          rw [clientResult_bind, clientState_laneGetGenProg, clientResult_laneGetGenProg]
          dsimp only [keyLaneBitsWhp]
          simp [hne, StateTransitionSpec.clientResult_pure]
        · simp [hrc, StateTransitionSpec.clientResult_pure]
      · rw [← hlk_eq]; unfold btreeLookup
        by_cases hrc : r < cnt
        · have hne : laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
            fun heq => hhit ⟨hrc, heq⟩
          simp [ha_ne, hlf_def, cnt, r, hrc, hne]
        · simp [ha_ne, hlf_def, cnt, r, hrc]
      · unfold btreeDelete
        by_cases hrc : r < cnt
        · have hne : laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
            fun heq => hhit ⟨hrc, heq⟩
          simp [ha_ne, leafIdx, cnt, r, hrc, hne]
        · simp [ha_ne, leafIdx, cnt, r, hrc]
      · intro newVal; unfold btreeUpdate
        by_cases hrc : r < cnt
        · have hne : laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
            fun heq => hhit ⟨hrc, heq⟩
          simp [ha_ne, leafIdx, cnt, r, hrc, hne]
        · simp [ha_ne, leafIdx, cnt, r, hrc]

private theorem realizes_btreeLocateHitGen :
    Realizes .exact btreeLocateHitGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      BTreeQueryGenPre
      (fun _ _ => 0) := by
  unfold btreeLocateHitGenProg
  have hrh := realizes_readSliceHeaderGen
  have hdl := realizes_descendLoopGen
  have hrn := realizes_readBTreeNodeGen
  have hsr := realizes_swarRankGen
  have hlg := realizes_laneGetGen
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, sIdx⟩, q⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, insCount, sl, mapFn,
      henv, rfl, hsIdx, hins, hrep, hv, hq⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    obtain ⟨hcs_h, hres_h, _, _⟩ := readSliceHeaderGenProg_spec hth henv.2.1 hsIdx hrep (s := s)
    dsimp only at hcs_h hres_h
    simp only [hcs_h, hres_h, wp_large_M hth, wp_large_hMaxBTree hth, wp_large_nSlice hth,
      wp_large_wKey hth] at *
  · exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · exact hsIdx
  · obtain ⟨_, ⟨ha0, _⟩ | ⟨_, T, hrt, _, _, _, hT⟩⟩ := hv.alloc_and_height_lt hth hins
    · simp_all
    · have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
        Nat.sub_lt (Nat.two_pow_pos _) one_pos
      exact (descendLoopGenProg_spec henv hsIdx hrep hrt (Nat.zero_le q) (by omega) hhi hT
        (fuel := hMaxBTree)).2.2.2.2
  · exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · exact hsIdx
  · obtain ⟨_, ⟨ha0, _⟩ | ⟨_, T, hrt, hht_lt, _, _, hT⟩⟩ := hv.alloc_and_height_lt hth hins
    · simp_all
    · obtain ⟨ht3, _, hkey_lt, _⟩ := (btree_slice_param_bounds hth).1
      have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
        Nat.sub_lt (Nat.two_pow_pos _) one_pos
      obtain ⟨hdl_st, hdl_res, _, _, _⟩ := descendLoopGenProg_spec henv hsIdx hrep hrt
        (Nat.zero_le q) (by omega) hhi hT (fuel := hMaxBTree)
      dsimp only at hdl_st hdl_res
      rw [hdl_res]
      obtain ⟨_, _, _, _, hv_leaf⟩ :=
        descendToLeaf_leaf (by omega) hkey_lt hT hhi (Nat.zero_le q) (by omega) hht_lt.le
      rw [hrt] at hv_leaf
      exact hv_leaf.1.trans_le hrep.1
  · decide
  · exact henv.fits_const (by decide)
  · obtain ⟨_, ⟨ha0, _⟩ | ⟨_, T, hrt, hht_lt, _, _, hT⟩⟩ := hv.alloc_and_height_lt hth hins
    · simp_all
    · obtain ⟨ht3, _, hkey_lt, _⟩ := (btree_slice_param_bounds hth).1
      have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
        Nat.sub_lt (Nat.two_pow_pos _) one_pos
      obtain ⟨hdl_st, hdl_res, _, _, _⟩ := descendLoopGenProg_spec henv hsIdx hrep hrt
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
      rw [hdl_st, hdl_res, hnd_res]
      refine ⟨⟨base, c, U, V, w, n_max, henv, rfl⟩, ?_, ?_, ?_, ?_⟩
      · simp only [wp_large_capLanes hth]; change metaCount _ < _; omega
      · simp only [wp_large_powFp hth]; exact hq
      · simp only [wp_large_wKey hth]; exact hkw_cnt
      · simp only [wp_large_wKey hth, wp_large_powFp hth]; exact hlanes
  · exact (Nat.le_mul_of_pos_left _ (by have := eight_le_tMinWhp hth; omega)).trans_lt
      henv.keysWordBits_lt_w
  · obtain ⟨_, ⟨ha0, _⟩ | ⟨_, T, hrt, hht_lt, _, _, hT⟩⟩ := hv.alloc_and_height_lt hth hins
    · simp_all
    · obtain ⟨ht3, _, hkey_lt, _⟩ := (btree_slice_param_bounds hth).1
      have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
        Nat.sub_lt (Nat.two_pow_pos _) one_pos
      obtain ⟨hdl_st, hdl_res, _, _, _⟩ := descendLoopGenProg_spec henv hsIdx hrep hrt
        (Nat.zero_le q) (by omega) hhi hT (fuel := hMaxBTree)
      dsimp only at hdl_st hdl_res
      obtain ⟨cntL, loL, hiL, hhiL, hv_leaf⟩ :=
        descendToLeaf_leaf (by omega) hkey_lt hT hhi (Nat.zero_le q) (by omega) hht_lt.le
      rw [hrt] at hv_leaf
      set leafIdx := descendToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl.nodes hMaxBTree sl.root q
      obtain ⟨hleaf_lt, hcnt_le, _, _, _, _, _⟩ :=
        validSubtree_root_bounds hth (hhiL.trans_lt hhi) hv_leaf
      dsimp only [BTreeTree.rootIdx] at hleaf_lt hcnt_le
      obtain ⟨hnd_st, hnd_res, _, _⟩ :=
        readBTreeNodeGenProg_spec hth henv.2.1 hsIdx hleaf_lt hrep (s := s)
      dsimp only at hnd_st hnd_res
      simp only [hdl_st, hdl_res, hnd_st, hnd_res, clientResult_swarRankGenProg hth] at *
      have hrc : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max)
          ((sl.nodes leafIdx).metaWord / 2) q (sl.nodes leafIdx).keysWord <
          (sl.nodes leafIdx).metaWord / 2 := by assumption
      have hsh : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max)
          ((sl.nodes leafIdx).metaWord / 2) q (sl.nodes leafIdx).keysWord * keyLaneBitsWhp n_max <
          w :=
        (Nat.mul_le_mul_right _ (hrc.le.trans (by change metaCount _ ≤ _; omega))).trans_lt
          henv.keysWordBits_lt_w
      exact hsh.trans Nat.lt_two_pow_self
  · exact henv.fits_const (by decide)

/-- Parameter-free `btreeLookup` (`d = (((cp, base), sIdx), q)`), returning `(1, val)` on hit or
`(0, 0)` on miss. -/
@[irreducible] def btreeLookupGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((cp, base), sIdx), q) => do
    let loc ← btreeLocateHitGenProg (((cp, base), sIdx), q)
    let (hitFlag, rest) := loc
    let (lr, nd) := rest
    let (_, r) := lr
    let (_, kv) := nd
    let (_, vW) := kv
    let z0 ← pure 0
    if hitFlag = z0 then
      pure (z0, z0)
    else do
      let v_r ← laneGetGenProg ((wpWVal cp, vW), r)
      let z1 ← pure 1
      pure (z1, v_r)

theorem btreeLookupGenProg_spec {c U V w n_max base sIdx insCount q : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) :
    let prog := btreeLookupGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match mapFn q with | some v => (1, v) | none => (0, 0)) ∧
    memoryCost prog s ≤ 262 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  obtain ⟨hst, hmc, hvp, hres⟩ :=
    btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
  dsimp only at hst hmc hvp hres ⊢
  unfold btreeLookupGenProg
  simp only [wp_large_wVal hth, pure_bind]
  rcases hres with ⟨hres0, hmap0, _, _⟩ |
      ⟨leafIdx, r, hres1, _, _, _, _, _, _, _, hmap1, _, _⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst, hres0]; rfl
    · rw [clientResult_bind, hst, hres0, hmap0]; rfl
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres0]
      simpa only [↓reduceIte, memoryCost_pure, Nat.add_zero] using hmc
    · refine validProg_bind hvp ?_
      rw [hst, hres0]; exact validProg_pure _
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst, hres1]
      simp only [Nat.one_ne_zero, ↓reduceIte]
      rw [clientState_bind, clientState_laneGetGenProg]; rfl
    · rw [clientResult_bind, hst, hres1, hmap1]
      simp only [Nat.one_ne_zero, ↓reduceIte]
      rw [clientResult_bind, clientState_laneGetGenProg, clientResult_laneGetGenProg,
        StateTransitionSpec.clientResult_pure]
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres1]
      simp only [Nat.one_ne_zero, ↓reduceIte]
      rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, clientState_laneGetGenProg,
        memoryCost_laneGetGenProg, memoryCost_pure]
      omega
    · refine validProg_bind hvp ?_
      rw [hst, hres1]; simp only [Nat.one_ne_zero, ↓reduceIte]
      refine validProg_bind (validWhpProg_laneGetGenProg _) ?_
      rw [clientState_laneGetGenProg]; exact validProg_pure _

theorem realizes_btreeLookupGen :
    Realizes .exact btreeLookupGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      BTreeQueryGenPre
      (fun _ _ => 0) := by
  unfold btreeLookupGenProg
  have hloc := realizes_btreeLocateHitGen
  have hlg := realizes_laneGetGen
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, sIdx⟩, q⟩
    dsimp only [BTreeQueryGenPre] at *
    obtain ⟨c, U, V, w₀, n_max, insCount, sl, mapFn,
      henv, rfl, hsIdx, hins, hrep, hv, hq⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
  · exact ⟨c, U, V, w, n_max, insCount, sl, mapFn, henv, rfl, hsIdx, hins, hrep, hv, hq⟩
  · simp only [wp_large_wVal hth]
    exact (Nat.le_mul_of_pos_left _ (by have := eight_le_tMinWhp hth; omega)).trans_lt
      henv.valsWordBits_lt_w
  · obtain ⟨_, _, _, hres⟩ := btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
    dsimp only at hres
    rcases hres with ⟨hres0, _⟩ | ⟨leafIdx, r, hres1, _, hrc, hcnt_le, _⟩
    · simp_all
    · simp only [hres1] at *
      simp only [wp_large_wVal hth]
      have hsh : r * valLaneBitsWhp n_max < w :=
        (Nat.mul_le_mul_right _ (hrc.le.trans (by omega))).trans_lt henv.valsWordBits_lt_w
      exact hsh.trans Nat.lt_two_pow_self
  · exact henv.fits_const (by decide)

/-- Parameter-free `btreeDelete` (`d = (((cp, base), sIdx), q)`). -/
@[irreducible] def btreeDeleteGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), sIdx), q) => do
    let loc ← btreeLocateHitGenProg (((cp, base), sIdx), q)
    let (hitFlag, rest) := loc
    let (lr, nd) := rest
    let (leafIdx, r) := lr
    let (mW, kv) := nd
    let (kW, vW) := kv
    let z0 ← pure 0
    if hitFlag = z0 then
      pure ()
    else do
      let cnt ← pure (mW / 2)
      let m' ← pure (1 + 2 * (cnt - 1))
      let k' ← wordDeleteAtGenProg ((wpWKey cp, r), kW)
      let v' ← wordDeleteAtGenProg ((wpWVal cp, r), vW)
      writeBTreeNodeGenProg ((((cp, base), sIdx), leafIdx), (m', (k', v')))

theorem btreeDeleteGenProg_spec {c U V w n_max base sIdx insCount q : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) :
    let prog := btreeDeleteGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 274 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx sl' s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ a, a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  obtain ⟨_, hmeta_cap, _, _⟩ := (btree_slice_param_bounds hth).1
  obtain ⟨hst, hmc, hvp, hres⟩ :=
    btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
  dsimp only at hst hmc hvp hres ⊢
  unfold btreeDeleteGenProg
  simp only [wp_large_wKey hth, wp_large_wVal hth, pure_bind]
  rcases hres with ⟨hres0, _, hdel0, _⟩ |
      ⟨leafIdx, r, hres1, hleaf_lt, hrc, hcnt_le, _, _, hkw_cnt, hvw_cnt, _, hdel1, _⟩
  · have hs'_eq : (Memory.spec 0).clientState s
        (btreeLocateHitGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), q) >>= fun loc =>
          if loc.1 = 0 then pure () else
            wordDeleteAtGenProg ((keyLaneBitsWhp n_max, loc.2.1.2), loc.2.2.2.1) >>= fun k' =>
            wordDeleteAtGenProg ((valLaneBitsWhp n_max, loc.2.1.2), loc.2.2.2.2) >>= fun v' =>
            writeBTreeNodeGenProg
              ((((mkWhpCoreParams c U V w n_max, base), sIdx), loc.2.1.1),
                (1 + 2 * (loc.2.2.1 / 2 - 1), (k', v')))) = s := by
      rw [clientState_bind, hst, hres0]; rfl
    rw [hs'_eq, hdel0]
    refine ⟨rfl, ?_, ?_, hrep, fun _ _ _ _ hr => hr, fun _ _ => rfl⟩
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres0]
      simp only [↓reduceIte, memoryCost_pure]; omega
    · refine validProg_bind hvp ?_
      rw [hst, hres0]; exact validProg_pure _
  · set nd := sl.nodes leafIdx
    set cnt := metaCount nd.metaWord
    have hcnt_pos : 1 ≤ cnt := by omega
    have hcnt_div : nd.metaWord / 2 = cnt := rfl
    let nd' : BTreeNode :=
      ⟨mkNodeMeta true (cnt - 1),
        wordDeleteAt (fpBitsWhp n_max + 2) r nd.keysWord,
        wordDeleteAt (valLaneBitsWhp n_max) r nd.valsWord⟩
    have hm'_lt : nd'.metaWord < 2 ^ nodeMetaBitsWhp n_max := by
      dsimp only [nd', mkNodeMeta]; simp only [↓reduceIte]; omega
    have hk'_lt : nd'.keysWord < 2 ^ keysWordBitsWhp n_max := by
      have hd := wordDeleteAt_lt (m := cnt - 1) (Nat.le_sub_one_of_lt hrc)
        (by rwa [Nat.sub_add_cancel hcnt_pos] :
          nd.keysWord < 2 ^ ((cnt - 1 + 1) * (fpBitsWhp n_max + 2)))
      unfold keysWordBitsWhp keyLaneBitsWhp
      exact hd.trans_le (Nat.pow_le_pow_right (by decide)
        (Nat.mul_le_mul_right _ ((Nat.sub_le cnt 1).trans (hcnt_le.trans (Nat.sub_le _ _)))))
    have hv'_lt : nd'.valsWord < 2 ^ valsWordBitsWhp n_max := by
      have hd := wordDeleteAt_lt (m := cnt - 1) (Nat.le_sub_one_of_lt hrc)
        (by rwa [Nat.sub_add_cancel hcnt_pos] :
          nd.valsWord < 2 ^ ((cnt - 1 + 1) * valLaneBitsWhp n_max))
      unfold valsWordBitsWhp
      exact hd.trans_le (Nat.pow_le_pow_right (by decide)
        (Nat.mul_le_mul_right _ ((Nat.sub_le cnt 1).trans (hcnt_le.trans (Nat.sub_le _ _)))))
    obtain ⟨hwn_fr, hwn_mc, hwn_vp, hwn_rep, hwn_other, hwn_out⟩ :=
      writeBTreeNodeGenProg_inPlace_sliceRep (nd' := nd') henv hsIdx hrep hleaf_lt
        hm'_lt hk'_lt hv'_lt (s := s)
    have hs'_wn : (Memory.spec 0).clientState s
        (btreeLocateHitGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), q) >>= fun loc =>
          if loc.1 = 0 then pure () else
            wordDeleteAtGenProg ((keyLaneBitsWhp n_max, loc.2.1.2), loc.2.2.2.1) >>= fun k' =>
            wordDeleteAtGenProg ((valLaneBitsWhp n_max, loc.2.1.2), loc.2.2.2.2) >>= fun v' =>
            writeBTreeNodeGenProg
              ((((mkWhpCoreParams c U V w n_max, base), sIdx), loc.2.1.1),
                (1 + 2 * (loc.2.2.1 / 2 - 1), (k', v')))) =
        (Memory.spec 0).clientState s
          (writeBTreeNodeGenProg
            ((((mkWhpCoreParams c U V w n_max, base), sIdx), leafIdx),
              (nd'.metaWord, (nd'.keysWord, nd'.valsWord)))) := by
      rw [clientState_bind, hst, hres1]
      simp only [Nat.one_ne_zero, ↓reduceIte, hcnt_div]
      rw [clientState_bind, clientState_wordDeleteAtGenProg, clientResult_wordDeleteAtGenProg,
        clientState_bind, clientState_wordDeleteAtGenProg, clientResult_wordDeleteAtGenProg]
      rfl
    rw [hs'_wn, hdel1]
    refine ⟨hwn_fr, ?_, ?_, hwn_rep, hwn_other, hwn_out⟩
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres1]
      simp only [Nat.one_ne_zero, ↓reduceIte, hcnt_div]
      rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, clientState_wordDeleteAtGenProg,
        memoryCost_wordDeleteAtGenProg, memoryCost_bind,
        clientState_wordDeleteAtGenProg, memoryCost_wordDeleteAtGenProg,
        memoryCost_writeBTreeNodeGenProg]
      omega
    · refine validProg_bind hvp ?_
      rw [hst, hres1]; simp only [Nat.one_ne_zero, ↓reduceIte, hcnt_div]
      refine validProg_bind (validWhpProg_wordDeleteAtGenProg _) ?_
      rw [clientState_wordDeleteAtGenProg, clientResult_wordDeleteAtGenProg]
      refine validProg_bind (validWhpProg_wordDeleteAtGenProg _) ?_
      rw [clientState_wordDeleteAtGenProg, clientResult_wordDeleteAtGenProg]
      exact hwn_vp

theorem realizes_btreeDeleteGen :
    Realizes .exact btreeDeleteGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      BTreeQueryGenPre
      (fun _ _ => 0) := by
  unfold btreeDeleteGenProg
  have hloc := realizes_btreeLocateHitGen
  have hwd := realizes_wordDeleteAtGen
  have hwn := realizes_writeBTreeNodeGen
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, sIdx⟩, q⟩
    dsimp only [BTreeQueryGenPre] at *
    obtain ⟨c, U, V, w₀, n_max, insCount, sl, mapFn,
      henv, rfl, hsIdx, hins, hrep, hv, hq⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
  · exact ⟨c, U, V, w, n_max, insCount, sl, mapFn, henv, rfl, hsIdx, hins, hrep, hv, hq⟩
  · decide
  · exact henv.fits_const (by decide)
  all_goals
    obtain ⟨_, _, _, hres⟩ := btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
    dsimp only at hres
    rcases hres with ⟨hres0, _⟩ |
        ⟨leafIdx, r, hres1, hleaf_lt, hrc, hcnt_le, _, _, hkw_cnt, hvw_cnt, _⟩
    · simp_all
    simp only [hres1] at *
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    have ht8 := eight_le_tMinWhp hth
    have hcnt_div : (sl.nodes leafIdx).metaWord / 2 = metaCount (sl.nodes leafIdx).metaWord := rfl
  · rw [hcnt_div]; omega
  · have hkl2 : 2 ≤ keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp fpBitsWhp; omega
    have : 1 + 2 * ((sl.nodes leafIdx).metaWord / 2 - 1) < w := by
      have : 2 * (2 * tMinWhp n_max) ≤ 2 * tMinWhp n_max * keyLaneBitsWhp n_max := by
        rw [Nat.mul_comm 2 (2 * tMinWhp n_max)]; exact Nat.mul_le_mul_left _ hkl2
      rw [hcnt_div]; omega
    exact this.trans Nat.lt_two_pow_self
  · simp only [wp_large_wKey hth]
    refine ⟨metaCount (sl.nodes leafIdx).metaWord - 1,
      by unfold keyLaneBitsWhp; positivity, by omega,
      (Nat.mul_le_mul_right _ (by omega)).trans_lt hkw_lt, ?_⟩
    rwa [Nat.sub_add_cancel (by omega)]
  · simp only [wp_large_wVal hth]
    refine ⟨metaCount (sl.nodes leafIdx).metaWord - 1,
      by unfold valLaneBitsWhp; positivity, by omega,
      (Nat.mul_le_mul_right _ (by omega)).trans_lt hvw_lt, ?_⟩
    rwa [Nat.sub_add_cancel (by omega)]
  · exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · simp only [wp_large_M hth]; exact hsIdx
  · simp only [wp_large_nSlice hth]; exact hleaf_lt.trans_le hrep.1

/-- Precondition for `btreeUpdateGenProg` and `btreeInsertGenProg`
(`d = ((((cp, base), sIdx), q), val)`). -/
@[expose] def BTreeModGenPre (w : ℕ) :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | ((((cp, base), sIdx), q), val), s =>
    ∃ c U V w₀ n_max insCount sl mapFn,
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      sIdx < 3 * numBucketsWhp n_max ∧
      insCount ≤ 8 * (slabScale n_max) ^ 12 ∧
      BTreeSliceMemRep base c U V w₀ n_max sIdx sl s.mem ∧
      ValidWhpSlice n_max insCount sl mapFn ∧
      q < 2 ^ fpBitsWhp n_max ∧
      val < 2 ^ valLaneBitsWhp n_max

/-- Parameter-free `btreeUpdate` (`d = ((((cp, base), sIdx), q), newVal)`). -/
@[irreducible] def btreeUpdateGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), sIdx), q), newVal) => do
    let loc ← btreeLocateHitGenProg (((cp, base), sIdx), q)
    let (hitFlag, rest) := loc
    let (lr, nd) := rest
    let (leafIdx, r) := lr
    let (mW, kv) := nd
    let (kW, vW) := kv
    let z0 ← pure 0
    if hitFlag = z0 then
      pure ()
    else do
      let v' ← wordUpdateAtGenProg (((wpWVal cp, r), newVal), vW)
      writeBTreeNodeGenProg ((((cp, base), sIdx), leafIdx), (mW, (kW, v')))

theorem btreeUpdateGenProg_spec {c U V w n_max base sIdx insCount q newVal : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) (hval : newVal < 2 ^ valLaneBitsWhp n_max) :
    let prog := btreeUpdateGenProg ((((mkWhpCoreParams c U V w n_max, base), sIdx), q), newVal)
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q newVal
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 274 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx sl' s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ a, a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  obtain ⟨hst, hmc, hvp, hres⟩ :=
    btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
  dsimp only at hst hmc hvp hres ⊢
  unfold btreeUpdateGenProg
  simp only [wp_large_wVal hth, pure_bind]
  rcases hres with ⟨hres0, _, _, hupd0⟩ |
      ⟨leafIdx, r, hres1, hleaf_lt, hrc, hcnt_le, hm_lt, hk_lt, _, hvw_cnt, _, _, hupd1⟩
  · have hs'_eq : (Memory.spec 0).clientState s
        (btreeLocateHitGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), q) >>= fun loc =>
          if loc.1 = 0 then pure () else
            wordUpdateAtGenProg (((valLaneBitsWhp n_max, loc.2.1.2), newVal), loc.2.2.2.2) >>=
              fun v' =>
            writeBTreeNodeGenProg
              ((((mkWhpCoreParams c U V w n_max, base), sIdx), loc.2.1.1),
                (loc.2.2.1, (loc.2.2.2.1, v')))) = s := by
      rw [clientState_bind, hst, hres0]; rfl
    rw [hs'_eq, hupd0 newVal]
    refine ⟨rfl, ?_, ?_, hrep, fun _ _ _ _ hr => hr, fun _ _ => rfl⟩
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres0]
      simp only [↓reduceIte, memoryCost_pure]; omega
    · refine validProg_bind hvp ?_
      rw [hst, hres0]; exact validProg_pure _
  · set nd := sl.nodes leafIdx
    set cnt := metaCount nd.metaWord
    let nd' : BTreeNode :=
      ⟨nd.metaWord, nd.keysWord, wordUpdateAt (valLaneBitsWhp n_max) r newVal nd.valsWord⟩
    have hv'_lt : nd'.valsWord < 2 ^ valsWordBitsWhp n_max := by
      unfold valsWordBitsWhp
      exact (wordUpdateAt_lt hrc hval hvw_cnt).trans_le
        (Nat.pow_le_pow_right (by decide)
          (Nat.mul_le_mul_right _ (hcnt_le.trans (Nat.sub_le _ _))))
    obtain ⟨hwn_fr, hwn_mc, hwn_vp, hwn_rep, hwn_other, hwn_out⟩ :=
      writeBTreeNodeGenProg_inPlace_sliceRep (nd' := nd') henv hsIdx hrep hleaf_lt
        hm_lt hk_lt hv'_lt (s := s)
    have hs'_wn : (Memory.spec 0).clientState s
        (btreeLocateHitGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), q) >>= fun loc =>
          if loc.1 = 0 then pure () else
            wordUpdateAtGenProg (((valLaneBitsWhp n_max, loc.2.1.2), newVal), loc.2.2.2.2) >>=
              fun v' =>
            writeBTreeNodeGenProg
              ((((mkWhpCoreParams c U V w n_max, base), sIdx), loc.2.1.1),
                (loc.2.2.1, (loc.2.2.2.1, v')))) =
        (Memory.spec 0).clientState s
          (writeBTreeNodeGenProg
            ((((mkWhpCoreParams c U V w n_max, base), sIdx), leafIdx),
              (nd'.metaWord, (nd'.keysWord, nd'.valsWord)))) := by
      rw [clientState_bind, hst, hres1]
      simp only [Nat.one_ne_zero, ↓reduceIte]
      rw [clientState_bind, clientState_wordUpdateAtGenProg, clientResult_wordUpdateAtGenProg]
    rw [hs'_wn, hupd1 newVal]
    refine ⟨hwn_fr, ?_, ?_, hwn_rep, hwn_other, hwn_out⟩
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres1]
      simp only [Nat.one_ne_zero, ↓reduceIte]
      rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, clientState_wordUpdateAtGenProg,
        memoryCost_wordUpdateAtGenProg, memoryCost_writeBTreeNodeGenProg]
      omega
    · refine validProg_bind hvp ?_
      rw [hst, hres1]; simp only [Nat.one_ne_zero, ↓reduceIte]
      refine validProg_bind (validWhpProg_wordUpdateAtGenProg _) ?_
      rw [clientState_wordUpdateAtGenProg, clientResult_wordUpdateAtGenProg]
      exact hwn_vp

theorem realizes_btreeUpdateGen :
    Realizes .exact btreeUpdateGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      BTreeModGenPre
      (fun _ _ => 0) := by
  unfold btreeUpdateGenProg
  have hloc := realizes_btreeLocateHitGen
  have hwu := realizes_wordUpdateAtGen
  have hwn := realizes_writeBTreeNodeGen
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨cp, base⟩, sIdx⟩, q⟩, newVal⟩
    dsimp only [BTreeModGenPre] at *
    obtain ⟨c, U, V, w₀, n_max, insCount, sl, mapFn,
      henv, rfl, hsIdx, hins, hrep, hv, hq, hval⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
  · exact ⟨c, U, V, w, n_max, insCount, sl, mapFn, henv, rfl, hsIdx, hins, hrep, hv, hq⟩
  all_goals
    obtain ⟨_, _, _, hres⟩ := btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
    dsimp only at hres
    rcases hres with ⟨hres0, _⟩ |
        ⟨leafIdx, r, hres1, hleaf_lt, hrc, hcnt_le, _, _, _, hvw_cnt, _⟩
    · simp_all
    simp only [hres1] at *
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    have ht8 := eight_le_tMinWhp hth
  · simp only [wp_large_wVal hth]
    exact ⟨metaCount (sl.nodes leafIdx).metaWord,
      by unfold valLaneBitsWhp; positivity, hrc,
      (Nat.mul_le_mul_right _ (by omega)).trans_lt hvw_lt, hval, hvw_cnt⟩
  · exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · simp only [wp_large_M hth]; exact hsIdx
  · simp only [wp_large_nSlice hth]; exact hleaf_lt.trans_le hrep.1

/-! ## Section 4: Top-Down Proactive-Split Insertion (`btreeInsertGenProg`) -/

/-- Packed bit-width bounds for all outputs of `splitFullNode`. -/
private theorem splitFullNode_bits_lt {c n_max : ℕ} {nd : BTreeNode}
    (hth : whpThreshold c ≤ n_max)
    (hk : nd.keysWord < 2 ^ keysWordBitsWhp n_max)
    (hv : nd.valsWord < 2 ^ valsWordBitsWhp n_max) :
    let res := splitFullNode (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) nd
    res.left.metaWord < 2 ^ nodeMetaBitsWhp n_max ∧
    res.left.keysWord < 2 ^ keysWordBitsWhp n_max ∧
    res.left.valsWord < 2 ^ valsWordBitsWhp n_max ∧
    res.sep < 2 ^ keyLaneBitsWhp n_max ∧
    res.right.metaWord < 2 ^ nodeMetaBitsWhp n_max ∧
    res.right.keysWord < 2 ^ keysWordBitsWhp n_max ∧
    res.right.valsWord < 2 ^ valsWordBitsWhp n_max := by
  obtain ⟨ht3, hmeta_cap, _, _⟩ := (btree_slice_param_bounds hth).1
  have hsep_lt : laneGet (fpBitsWhp n_max + 2) nd.keysWord (tMinWhp n_max - 1) <
      2 ^ keyLaneBitsWhp n_max := by
    rw [laneGet_eq_div_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have htk_lt : wordTakeLow (fpBitsWhp n_max + 2) (tMinWhp n_max) nd.keysWord <
      2 ^ keysWordBitsWhp n_max := by
    unfold keysWordBitsWhp keyLaneBitsWhp
    exact (wordTakeLow_lt _ _ _).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
  have htk1_lt : wordTakeLow (fpBitsWhp n_max + 2) (tMinWhp n_max - 1) nd.keysWord <
      2 ^ keysWordBitsWhp n_max := by
    unfold keysWordBitsWhp keyLaneBitsWhp
    exact (wordTakeLow_lt _ _ _).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
  have htv_lt : wordTakeLow (valLaneBitsWhp n_max) (tMinWhp n_max) nd.valsWord <
      2 ^ valsWordBitsWhp n_max := by
    unfold valsWordBitsWhp
    exact (wordTakeLow_lt _ _ _).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
  have hdk_lt : wordDropLow (fpBitsWhp n_max + 2) (tMinWhp n_max) nd.keysWord <
      2 ^ keysWordBitsWhp n_max := by
    rw [wordDropLow_eq_div]; exact (Nat.div_le_self _ _).trans_lt hk
  have hdv_lt : wordDropLow (valLaneBitsWhp n_max) (tMinWhp n_max) nd.valsWord <
      2 ^ valsWordBitsWhp n_max := by
    rw [wordDropLow_eq_div]; exact (Nat.div_le_self _ _).trans_lt hv
  unfold splitFullNode
  by_cases hlf : metaIsLeaf nd.metaWord = true
  · simp only [hlf, ↓reduceIte, mkNodeMeta]
    exact ⟨by omega, htk_lt, htv_lt, hsep_lt, by omega, hdk_lt, hdv_lt⟩
  · simp only [hlf, Bool.false_eq_true, ↓reduceIte, mkNodeMeta]
    exact ⟨by omega, htk1_lt, htv_lt, hsep_lt, by omega, hdk_lt, hdv_lt⟩

/-- Shared 4-write frame lemma for proactive root/child splits: writing 3 nodes `(idx1, nd1)`,
`(idx2, nd2)`, `(idx3, nd3)` below `newA` followed by `writeSliceAllocGenProg` establishes
`BTreeSliceMemRep` for the updated slice and frames all other slices, other `bktMeta` fields, and
outside segments. -/
private theorem threeNodeWrites_and_alloc_sliceRep
    {c U V w n_max base sIdx newA idx1 idx2 idx3 : ℕ}
    {sl : BTreeSlice} {nd1 nd2 nd3 : BTreeNode} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hnewA_hi : newA ≤ nSliceWhp n_max)
    (hu1 : idx1 < newA) (hu2 : idx2 < newA) (hu3 : idx3 < newA)
    (hcov : ∀ v < newA, v < sl.alloc ∨ v = idx1 ∨ v = idx2 ∨ v = idx3)
    (hm1 : nd1.metaWord < 2 ^ nodeMetaBitsWhp n_max)
    (hk1 : nd1.keysWord < 2 ^ keysWordBitsWhp n_max)
    (hv1 : nd1.valsWord < 2 ^ valsWordBitsWhp n_max)
    (hm2 : nd2.metaWord < 2 ^ nodeMetaBitsWhp n_max)
    (hk2 : nd2.keysWord < 2 ^ keysWordBitsWhp n_max)
    (hv2 : nd2.valsWord < 2 ^ valsWordBitsWhp n_max)
    (hm3 : nd3.metaWord < 2 ^ nodeMetaBitsWhp n_max)
    (hk3 : nd3.keysWord < 2 ^ keysWordBitsWhp n_max)
    (hv3 : nd3.valsWord < 2 ^ valsWordBitsWhp n_max) :
    let p0 := (mkWhpCoreParams c U V w n_max, base)
    let prog :=
      writeBTreeNodeGenProg (((p0, sIdx), idx1), (nd1.metaWord, (nd1.keysWord, nd1.valsWord))) >>=
      fun _ =>
      writeBTreeNodeGenProg (((p0, sIdx), idx2), (nd2.metaWord, (nd2.keysWord, nd2.valsWord))) >>=
      fun _ =>
      writeBTreeNodeGenProg (((p0, sIdx), idx3), (nd3.metaWord, (nd3.keysWord, nd3.valsWord))) >>=
      fun _ =>
      writeSliceAllocGenProg ((p0, sIdx), newA)
    let nodes3 := Function.update
      (Function.update (Function.update sl.nodes idx1 nd1) idx2 nd2) idx3 nd3
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 40 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx ⟨newA, sl.root, nodes3⟩ s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ idx < 16 * numBucketsWhp n_max,
      idx ≠ 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, (a < base + offBktMeta c U V w n_max ∨
        (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
        base + offTrieChild0 c U V w n_max ≤ a) →
      s'.mem a = s.mem a) := by
  have hw := henv.2.1
  set p0 := (mkWhpCoreParams c U V w n_max, base)
  set w1 := writeBTreeNodeGenProg (((p0, sIdx), idx1), (nd1.metaWord, (nd1.keysWord, nd1.valsWord)))
  set w2 := writeBTreeNodeGenProg (((p0, sIdx), idx2), (nd2.metaWord, (nd2.keysWord, nd2.valsWord)))
  set w3 := writeBTreeNodeGenProg (((p0, sIdx), idx3), (nd3.metaWord, (nd3.keysWord, nd3.valsWord)))
  set w4 := writeSliceAllocGenProg ((p0, sIdx), newA)
  set s1 := (Memory.spec 0).clientState s w1
  set s2 := (Memory.spec 0).clientState s1 w2
  set s3 := (Memory.spec 0).clientState s2 w3
  obtain ⟨hfr1, hmc1, hvp1, hup1, hoth1, hout1⟩ :=
    writeBTreeNodeGenProg_spec (nd := nd1) henv hsIdx (hu1.trans_le hnewA_hi) hm1 hk1 hv1 (s := s)
  obtain ⟨hfr2, hmc2, hvp2, hup2, hoth2, hout2⟩ :=
    writeBTreeNodeGenProg_spec (nd := nd2) henv hsIdx (hu2.trans_le hnewA_hi) hm2 hk2 hv2 (s := s1)
  obtain ⟨hfr3, hmc3, hvp3, hup3, hoth3, hout3⟩ :=
    writeBTreeNodeGenProg_spec (nd := nd3) henv hsIdx (hu3.trans_le hnewA_hi) hm3 hk3 hv3 (s := s2)
  dsimp only at hfr1 hmc1 hvp1 hup1 hoth1 hout1 hfr2 hmc2 hvp2 hup2 hoth2 hout2
  dsimp only at hfr3 hmc3 hvp3 hup3 hoth3 hout3
  have hout123 : ∀ a, a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a →
      s3.mem a = s.mem a := fun a ha =>
    (hout3 a ha).trans ((hout2 a ha).trans (hout1 a ha))
  have hoff := largeOffsetChain c U V w n_max
  have hbm_s3 : ∀ i < 16 * numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s3.mem i =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem i :=
    fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ => hout123 a (Or.inl (by omega))
  let aux0 : ℕ → BTreeNode := fun v =>
    if v < sl.alloc then sl.nodes v
    else ⟨readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s.mem
            (sIdx * nSliceWhp n_max + v),
          readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s.mem
            (sIdx * nSliceWhp n_max + v),
          readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s.mem
            (sIdx * nSliceWhp n_max + v)⟩
  have haux0 : ∀ v < newA,
      let idx_v := sIdx * nSliceWhp n_max + v
      readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s.mem idx_v =
        (aux0 v).metaWord ∧
      readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s.mem idx_v =
        (aux0 v).keysWord ∧
      readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s.mem idx_v =
        (aux0 v).valsWord := fun v _ => by
    dsimp only [aux0]
    split_ifs with hv_lt
    · exact hrep.2.2.2 v hv_lt
    · exact ⟨rfl, rfl, rfl⟩
  have hs1_nd := hup1 ⟨newA, sl.root, aux0⟩ hnewA_hi (fun v hv _ => haux0 v hv)
  have hs2_nd := hup2 ⟨newA, sl.root, Function.update aux0 idx1 nd1⟩ hnewA_hi
    (fun v hv _ => hs1_nd v hv)
  have hs3_nd := hup3
    ⟨newA, sl.root, Function.update (Function.update aux0 idx1 nd1) idx2 nd2⟩ hnewA_hi
    (fun v hv _ => hs2_nd v hv)
  set nodes3 := Function.update
    (Function.update (Function.update sl.nodes idx1 nd1) idx2 nd2) idx3 nd3
  have hnodes_s3 : ∀ u < newA,
      let idx_u := sIdx * nSliceWhp n_max + u
      readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s3.mem idx_u =
        (nodes3 u).metaWord ∧
      readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s3.mem idx_u =
        (nodes3 u).keysWord ∧
      readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s3.mem idx_u =
        (nodes3 u).valsWord := fun u hu => by
    have heq_u : Function.update (Function.update (Function.update aux0 idx1 nd1) idx2 nd2)
        idx3 nd3 u = nodes3 u := by
      dsimp only [nodes3]
      by_cases h3 : u = idx3
      · subst h3; simp
      · rw [Function.update_of_ne h3, Function.update_of_ne h3]
        by_cases h2 : u = idx2
        · subst h2; simp
        · rw [Function.update_of_ne h2, Function.update_of_ne h2]
          by_cases h1 : u = idx1
          · subst h1; simp
          · rw [Function.update_of_ne h1, Function.update_of_ne h1]
            rcases hcov u hu with hlt | h1' | h2' | h3'
            · simp [aux0, hlt]
            · exact absurd h1' h1
            · exact absurd h2' h2
            · exact absurd h3' h3
    simpa only [heq_u] using hs3_nd u hu
  have hroot_s3 : readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s3.mem
      (16 * (sIdx / 3) + 11 + 2 * (sIdx % 3)) = sl.root :=
    (hbm_s3 _ (by omega)).trans hrep.2.2.1
  obtain ⟨hfr4, hmc4, hvp4, hrep4, hoth4, hbm4, hout4⟩ :=
    writeSliceAllocGenProg_sliceRep (nodes := nodes3) henv hsIdx hnewA_hi hroot_s3 hnodes_s3
      (s := s3)
  dsimp only at hfr4 hmc4 hvp4 hrep4 hoth4 hbm4 hout4 ⊢
  have hs'_eq : (Memory.spec 0).clientState s (w1 >>= fun _ => w2 >>= fun _ => w3 >>= fun _ => w4) =
      (Memory.spec 0).clientState s3 w4 := by
    rw [clientState_bind, clientState_bind,
      clientState_bind]
  dsimp only [w1, w2, w3, w4] at hs'_eq ⊢
  rw [hs'_eq]
  refine ⟨hfr4.trans (hfr3.trans (hfr2.trans hfr1)), ?_, ?_, hrep4, ?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    change memoryCost w1 s + (memoryCost w2 s1 + (memoryCost w3 s2 + memoryCost w4 s3)) = 40
    rw [hmc1, hmc2, hmc3, hmc4]
  · refine validProg_bind hvp1 ?_
    refine validProg_bind hvp2 ?_
    exact validProg_bind hvp3 hvp4
  · intro sIdx' hsIdx' hne sl₂ hr₂
    exact hoth4 sIdx' hsIdx' hne sl₂
      (hoth3 sIdx' hsIdx' hne sl₂ (hoth2 sIdx' hsIdx' hne sl₂ (hoth1 sIdx' hsIdx' hne sl₂ hr₂)))
  · intro idx hidx hneA
    exact (hbm4 idx hidx hneA).trans (hbm_s3 idx hidx)
  · intro a ha
    rcases ha with ha1 | ⟨ha2, ha3⟩ | ha4
    · exact (hout4 a (Or.inl ha1)).trans (hout123 a (Or.inl (by omega)))
    · exact (hout4 a (Or.inr ha2)).trans (hout123 a (Or.inl ha3))
    · exact (hout4 a (Or.inr (by omega))).trans (hout123 a (Or.inr ha4))

/-- Opaque call wrapper for `writeBTreeNodeGenProg` so multi-write subroutines do not cause
exponential state unfolding inside `realize`. -/
@[irreducible] private def writeNodeOpProg
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))) : Memory.Prog Unit :=
  writeBTreeNodeGenProg d

private theorem realizes_writeNodeOp :
    Realizes .exact writeNodeOpProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => WhpLargeEnvGen w d.1.1.1.1 d.1.1.1.2 ∧
        d.1.1.2 < 3 * wpM d.1.1.1.1 ∧ d.1.2 < wpNSlice d.1.1.1.1)
      (fun _ _ => 0) := by
  unfold writeNodeOpProg; exact realizes_writeBTreeNodeGen

/-- Opaque call wrapper for `splitFullNodeGenProg`. -/
@[irreducible] private def splitNodeOpProg
    (d : WhpCoreParams × (ℕ × (ℕ × ℕ))) :
    Memory.Prog ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ)))) :=
  splitFullNodeGenProg d

private theorem realizes_splitNodeOp :
    Realizes .exact splitNodeOpProg
      (WordEncoding.encode (α := WhpCoreParams × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ)))))
      (fun w d _ => ∃ base, WhpLargeEnvGen w d.1 base)
      (fun _ _ => 0) := by
  unfold splitNodeOpProg; exact realizes_splitFullNodeGen

private theorem clientResult_splitNodeOpProg {c U V w n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    (nd : BTreeNode) (s : Memory.State) :
    let out := splitFullNode (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) nd
    (Memory.spec 0).clientResult s
      (splitNodeOpProg
        (mkWhpCoreParams c U V w n_max, (nd.metaWord, (nd.keysWord, nd.valsWord)))) =
      ((out.left.metaWord, (out.left.keysWord, out.left.valsWord)),
       (out.sep, (out.right.metaWord, (out.right.keysWord, out.right.valsWord)))) := by
  unfold splitNodeOpProg; exact clientResult_splitFullNodeGenProg hth nd s

/-- Opaque call wrapper for `wordInsertAtGenProg`. -/
@[irreducible] private def wordInsertOpProg (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  wordInsertAtGenProg d

private theorem realizes_wordInsertOp :
    Realizes .exact wordInsertOpProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d _ => ∃ m, d.1.1.2 ≤ m ∧ (m + 1) * d.1.1.1 < w ∧
        d.1.2 < 2 ^ d.1.1.1 ∧ d.2 < 2 ^ (m * d.1.1.1))
      (fun _ _ => 0) := by
  unfold wordInsertOpProg; exact realizes_wordInsertAtGen

private def writeSplitFourBody
    (d : (((WhpCoreParams × ℕ) × ℕ) ×
      (((ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))) × ((ℕ × (ℕ × (ℕ × ℕ))) × ℕ)))) :
    Memory.Prog Unit := do
  let nSlice ← pure (wpNSlice d.1.1.1)
  let w ← pure (wpW d.1.1.1)
  let gBits ← pure (wpGlobalPtrBits d.1.1.1)
  let offBm ← pure (wpOffBktMeta d.1.1.1)
  let offM ← pure (wpOffBtMeta d.1.1.1)
  let bM ← pure (wpNodeMetaBits d.1.1.1)
  let offK ← pure (wpOffBtKeys d.1.1.1)
  let bK ← pure (wpKeysWordBits d.1.1.1)
  let offV ← pure (wpOffBtVals d.1.1.1)
  let bV ← pure (wpValsWordBits d.1.1.1)
  let g1 ← pure (d.1.2 * nSlice + d.2.1.1.1)
  writePackedGenProg ((((d.1.1.2, offM), (bM, w)), g1), d.2.1.1.2.1)
  writePackedGenProg ((((d.1.1.2, offK), (bK, w)), g1), d.2.1.1.2.2.1)
  writePackedGenProg ((((d.1.1.2, offV), (bV, w)), g1), d.2.1.1.2.2.2)
  let g2 ← pure (d.1.2 * nSlice + d.2.1.2.1)
  writePackedGenProg ((((d.1.1.2, offM), (bM, w)), g2), d.2.1.2.2.1)
  writePackedGenProg ((((d.1.1.2, offK), (bK, w)), g2), d.2.1.2.2.2.1)
  writePackedGenProg ((((d.1.1.2, offV), (bV, w)), g2), d.2.1.2.2.2.2)
  let g3 ← pure (d.1.2 * nSlice + d.2.2.1.1)
  writePackedGenProg ((((d.1.1.2, offM), (bM, w)), g3), d.2.2.1.2.1)
  writePackedGenProg ((((d.1.1.2, offK), (bK, w)), g3), d.2.2.1.2.2.1)
  writePackedGenProg ((((d.1.1.2, offV), (bV, w)), g3), d.2.2.1.2.2.2)
  let b ← pure (d.1.2 / 3)
  let role ← pure (d.1.2 % 3)
  let idxA ← pure (16 * b + 10 + 2 * role)
  writePackedGenProg ((((d.1.1.2, offBm), (gBits, w)), idxA), d.2.2.2)

private theorem realizes_writeSplitFourBody :
    Realizes .exact writeSplitFourBody
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) ×
        (((ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))) × ((ℕ × (ℕ × (ℕ × ℕ))) × ℕ)))))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => WhpLargeEnvGen w d.1.1.1 d.1.1.2 ∧
        d.1.2 < 3 * wpM d.1.1.1 ∧
        d.2.1.1.1 < wpNSlice d.1.1.1 ∧
        d.2.1.2.1 < wpNSlice d.1.1.1 ∧
        d.2.2.1.1 < wpNSlice d.1.1.1)
      (fun _ _ => 0) := by
  have hwp := realizes_writePackedGen
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, sIdx⟩, ⟨⟨⟨u1, nd1⟩, ⟨u2, nd2⟩⟩, ⟨⟨u3, nd3⟩, newA⟩⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hsIdx, hu1, hu2, hu3⟩ := h
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    have htot_le := totalBTreeNodesWhp_le_n_max hth
    simp only [wp_large_M hth, wp_large_nSlice hth, wp_large_w hth,
      wp_large_globalPtrBits hth, wp_large_offBktMeta hth,
      wp_large_offBtMeta hth, wp_large_nodeMetaBits hth,
      wp_large_offBtKeys hth, wp_large_keysWordBits hth,
      wp_large_offBtVals hth, wp_large_valsWordBits hth] at hsIdx hu1 hu2 hu3 ⊢
    have hidx1 : sIdx * nSliceWhp n_max + u1 < totalBTreeNodesWhp n_max := by
      unfold totalBTreeNodesWhp
      calc sIdx * nSliceWhp n_max + u1 < sIdx * nSliceWhp n_max + nSliceWhp n_max :=
            Nat.add_lt_add_left hu1 _
        _ = (sIdx + 1) * nSliceWhp n_max := by ring
        _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx
    have hidx2 : sIdx * nSliceWhp n_max + u2 < totalBTreeNodesWhp n_max := by
      unfold totalBTreeNodesWhp
      calc sIdx * nSliceWhp n_max + u2 < sIdx * nSliceWhp n_max + nSliceWhp n_max :=
            Nat.add_lt_add_left hu2 _
        _ = (sIdx + 1) * nSliceWhp n_max := by ring
        _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx
    have hidx3 : sIdx * nSliceWhp n_max + u3 < totalBTreeNodesWhp n_max := by
      unfold totalBTreeNodesWhp
      calc sIdx * nSliceWhp n_max + u3 < sIdx * nSliceWhp n_max + nSliceWhp n_max :=
            Nat.add_lt_add_left hu3 _
        _ = (sIdx + 1) * nSliceWhp n_max := by ring
        _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (hidx1.le.trans htot_le)
    | exact henv.fits_of_le_n_max (hidx2.le.trans htot_le)
    | exact henv.fits_of_le_n_max (hidx3.le.trans htot_le)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.btMeta_safe hidx1
    | exact henv.btKeys_safe hidx1
    | exact henv.btVals_safe hidx1
    | exact henv.btMeta_safe hidx2
    | exact henv.btKeys_safe hidx2
    | exact henv.btVals_safe hidx2
    | exact henv.btMeta_safe hidx3
    | exact henv.btKeys_safe hidx3
    | exact henv.btVals_safe hidx3
    | exact henv.bktMeta_safe (by omega)

/-- Opaque 4-write split helper (`3` node writes + `writeSliceAlloc`) so `ensureAndSplitRootGenProg`
and `descendSplitStepGenProg` perform only a single subroutine reindexing instead of four. -/
@[irreducible] private def writeSplitFourOpProg
    (d : (((WhpCoreParams × ℕ) × ℕ) ×
      (((ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))) × ((ℕ × (ℕ × (ℕ × ℕ))) × ℕ)))) :
    Memory.Prog Unit :=
  writeSplitFourBody d

private theorem realizes_writeSplitFourOp :
    Realizes .exact writeSplitFourOpProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) ×
        (((ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))) × ((ℕ × (ℕ × (ℕ × ℕ))) × ℕ)))))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => WhpLargeEnvGen w d.1.1.1 d.1.1.2 ∧
        d.1.2 < 3 * wpM d.1.1.1 ∧
        d.2.1.1.1 < wpNSlice d.1.1.1 ∧
        d.2.1.2.1 < wpNSlice d.1.1.1 ∧
        d.2.2.1.1 < wpNSlice d.1.1.1)
      (fun _ _ => 0) := by
  unfold writeSplitFourOpProg; exact realizes_writeSplitFourBody

private theorem writeSplitFourOpProg_eq
    (p : (WhpCoreParams × ℕ) × ℕ)
    (idx1 : ℕ) (nd1 : ℕ × (ℕ × ℕ))
    (idx2 : ℕ) (nd2 : ℕ × (ℕ × ℕ))
    (idx3 : ℕ) (nd3 : ℕ × (ℕ × ℕ))
    (newA : ℕ) :
    writeSplitFourOpProg (p, (((idx1, nd1), (idx2, nd2)), ((idx3, nd3), newA))) =
      (writeBTreeNodeGenProg ((p, idx1), nd1) >>= fun _ =>
       writeBTreeNodeGenProg ((p, idx2), nd2) >>= fun _ =>
       writeBTreeNodeGenProg ((p, idx3), nd3) >>= fun _ =>
       writeSliceAllocGenProg (p, newA)) := by
  unfold writeSplitFourOpProg writeSplitFourBody writeBTreeNodeGenProg writeSliceAllocGenProg
  simp only [pure_bind, bind_assoc]

private theorem clientState_bind_pure {α : Type} (m : Memory.Prog Unit)
    (a : α) (s : Memory.State) :
    (Memory.spec 0).clientState s (m >>= fun _ => pure a) =
      (Memory.spec 0).clientState s m := by
  rw [clientState_bind]; rfl

private theorem clientResult_bind_pure {α : Type} (m : Memory.Prog Unit)
    (a : α) (s : Memory.State) :
    (Memory.spec 0).clientResult s (m >>= fun _ => pure a) = a := by
  rw [clientResult_bind, StateTransitionSpec.clientResult_pure]

private theorem clientState_bind_pure_ite {α : Type} (m : Memory.Prog Unit)
    (cond : Prop) [Decidable cond] (a b : α) (s : Memory.State) :
    (Memory.spec 0).clientState s (m >>= fun _ => if cond then pure a else pure b) =
      (Memory.spec 0).clientState s m := by
  rw [clientState_bind]
  split_ifs <;> rfl

private theorem clientResult_bind_pure_ite {α : Type} (m : Memory.Prog Unit)
    (cond : Prop) [Decidable cond] (a b : α) (s : Memory.State) :
    (Memory.spec 0).clientResult s (m >>= fun _ => if cond then pure a else pure b) =
      if cond then a else b := by
  rw [clientResult_bind]
  split_ifs <;> rfl

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
    dsimp only [SplitFullRootPre] at h
    obtain ⟨c, U, V, w₀, n_max, henv, rfl, hsIdx, halloc2, hrt_lt⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have ht8 := eight_le_tMinWhp hth
    have hns_lt_n := (large_bounds_lt_n_max hth).2.1
    obtain ⟨_, _, _, hns_lt_v⟩ := (btree_slice_param_bounds hth).1
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    try simp only [wp_large_M hth] at *
    try simp only [wp_large_nSlice hth] at *
    try simp only [wp_large_wVal hth] at *
    have h2v : alloc + ((alloc + 1) <<< valLaneBitsWhp n_max) <
        2 ^ (2 * valLaneBitsWhp n_max) := by
      rw [Nat.shiftLeft_eq, two_mul, Nat.pow_add]
      have h0 : alloc < 2 ^ valLaneBitsWhp n_max :=
        (by omega : alloc < nSliceWhp n_max).trans hns_lt_v
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
private def EnsureRootGenPre (w : ℕ) (d : (WhpCoreParams × ℕ) × ℕ) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max insCount sl mapFn,
    WhpLargeEnv c U V w₀ n_max w d.1.2 ∧
    d.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    d.2 < 3 * numBucketsWhp n_max ∧
    insCount ≤ 8 * (slabScale n_max) ^ 12 ∧
    BTreeSliceMemRep d.1.2 c U V w₀ n_max d.2 sl s.mem ∧
    ValidWhpSlice n_max insCount sl mapFn

/-- Parameter-free `splitRootIfFull ∘ ensureRootSlice` (`d = ((cp, base), sIdx)`), returning
`(alloc1, root1)`. -/
private def ensureAndSplitRootGenProg (d : (WhpCoreParams × ℕ) × ℕ) :
    Memory.Prog (ℕ × ℕ) := do
  let hdr ← readSliceHeaderGenProg (d.1, d.2)
  let z0 ← pure 0
  if hdr.1 = z0 then
    initEmptyRootOpProg d
  else do
    let rootNd ← readBTreeNodeGenProg (d, hdr.2)
    let cnt ← pure (rootNd.1 / 2)
    let fullCnt ← pure (2 * wpTMin d.1.1 - 1)
    if cnt = fullCnt then
      splitFullRootOpProg (d, (hdr, rootNd))
    else
      pure hdr

private theorem ensureAndSplitRootGenProg_spec {c U V w n_max base sIdx insCount : ℕ}
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
  dsimp only at hcs_h hres_h hmc_h hvp_h
  unfold ensureAndSplitRootGenProg initEmptyRootOpProg initEmptyRootBody
    splitFullRootOpProg splitFullRootBody writeNodeOpProg splitNodeOpProg
  simp only [wp_large_tMin hth, wp_large_wVal hth, pure_bind]
  obtain ⟨halloc_lt, ⟨ha0, rfl⟩ | ⟨ha_pos, T, hrt, hht_T, _, _, hT⟩⟩ :=
    hv.alloc_and_height_lt hth hins
  · -- Case 1: `sl.alloc = 0` (`ensureRootSlice` creates a 1-node empty leaf, no root split)
    have hsl1_eq : splitRootIfFull (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (ensureRootSlice sl) =
        { alloc := 1, root := 0, nodes := Function.update sl.nodes 0 ⟨1, 0, 0⟩ } := by
      have hens : ensureRootSlice sl =
          { alloc := 1, root := 0, nodes := Function.update sl.nodes 0 ⟨1, 0, 0⟩ } := by
        simp [ensureRootSlice, ha0, mkNodeMeta]
      rw [hens]
      unfold splitRootIfFull
      have hmc0 : metaCount ((Function.update sl.nodes 0 ⟨1, 0, 0⟩ 0).metaWord) = 0 := by
        simp [metaCount]
      have hne0 : (0 == 2 * tMinWhp n_max - 1) = false := by simp; omega
      dsimp only
      rw [hmc0, hne0]; rfl
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
    have hs'_eq : (Memory.spec 0).clientState s
        (readSliceHeaderGenProg (p0, sIdx) >>= fun hdr =>
          if hdr.1 = 0 then wN >>= fun _ => wH >>= fun _ => pure (1, 0)
          else
            readBTreeNodeGenProg ((p0, sIdx), hdr.2) >>= fun rootNd =>
            if rootNd.1 / 2 = 2 * tMinWhp n_max - 1 then
              splitFullNodeGenProg (p0.1, rootNd) >>= fun sp =>
              writeSplitFourOpProg ((p0, sIdx),
                (((hdr.1, sp.1), (hdr.1 + 1, sp.2.2)),
                 ((hdr.2, (2, (sp.2.1, hdr.1 + ((hdr.1 + 1) <<< valLaneBitsWhp n_max)))),
                  hdr.1 + 2))) >>= fun _ =>
              pure (hdr.1 + 2, hdr.2)
            else pure hdr) =
        (Memory.spec 0).clientState s1 wH := by
      rw [clientState_bind, hcs_h, hres_h]
      simp only [ha0, ↓reduceIte]
      rw [clientState_bind, clientState_bind_pure]
    rw [hs'_eq, hsl1_eq]
    refine ⟨hfrH.trans hfrN, ?_, ?_, ?_, hrepH, by dsimp only; rw [hMaxBTree_eq]; omega,
      ?_, ?_, ?_, ?_⟩
    · rw [clientResult_bind, hcs_h, hres_h]
      simp only [ha0, ↓reduceIte]
      rw [clientResult_bind, clientResult_bind_pure]
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hcs_h, hmc_h, hres_h]
      simp only [ha0, ↓reduceIte]
      rw [← PFunctor.FreeM.bind_eq_bind]
      rw [memoryCost_bind, memoryCost_bind]
      dsimp only [wN, wH, p0]
      rw [hmcN, hmcH, memoryCost_pure]; omega
    · refine validProg_bind hvp_h ?_
      rw [hcs_h, hres_h]; simp only [ha0, ↓reduceIte]
      refine validProg_bind hvpN ?_
      exact validProg_bind hvpH (validProg_pure _)
    · refine ⟨.leaf 0 0, rfl, by simp [BTreeTree.height], ?_, ?_⟩
      · simp [metaCount]; omega
      · dsimp only [ValidSubtree]
        rw [Function.update_self]
        refine ⟨by omega, rfl, by omega, by positivity, by positivity,
          fun _ hj => absurd hj (Nat.not_lt_zero _),
          fun _ _ _ hj => absurd hj (Nat.not_lt_zero _),
          fun _ _ _ => Or.inr ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), rfl⟩⟩
    · intro sIdx' hsIdx' hne sl₂ hr₂
      exact hothH sIdx' hsIdx' hne sl₂ (hothN sIdx' hsIdx' hne sl₂ hr₂)
    · intro idx hidx h1 h2
      exact (hbmH idx hidx h1 h2).trans
        (readPacked_congr hw (hidx := hidx) fun a ⟨_, ha2⟩ => houtN a (Or.inl (by omega)))
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
    by_cases hfull : metaCount (sl.nodes sl.root).metaWord = 2 * tMinWhp n_max - 1
    · -- Subcase 2a: Full root (`splitRootIfFull` splits into `sl.alloc`, `sl.alloc + 1`, `sl.root`)
      set spPure := splitFullNode (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (sl.nodes sl.root)
      obtain ⟨hlM, hlK, hlV, hsep_lt, hrM, hrK, hrV⟩ := splitFullNode_bits_lt hth hk_rt hv_rt
      let newVals := sl.alloc + ((sl.alloc + 1) <<< valLaneBitsWhp n_max)
      let newRootNd : BTreeNode := ⟨2, spPure.sep, newVals⟩
      have hm3 : newRootNd.metaWord < 2 ^ nodeMetaBitsWhp n_max := by
        dsimp only [newRootNd]; omega
      have hk3 : newRootNd.keysWord < 2 ^ keysWordBitsWhp n_max := by
        dsimp only [newRootNd]
        unfold keysWordBitsWhp
        exact hsep_lt.trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by omega)))
      have hv3 : newRootNd.valsWord < 2 ^ valsWordBitsWhp n_max := by
        dsimp only [newRootNd, newVals]
        have h2v : sl.alloc + ((sl.alloc + 1) <<< valLaneBitsWhp n_max) <
            2 ^ (2 * valLaneBitsWhp n_max) := by
          rw [Nat.shiftLeft_eq, two_mul, Nat.pow_add]
          have h0 : sl.alloc < 2 ^ valLaneBitsWhp n_max := by omega
          have h1 : sl.alloc + 2 ≤ 2 ^ valLaneBitsWhp n_max := halloc_val
          calc sl.alloc + (sl.alloc + 1) * 2 ^ valLaneBitsWhp n_max
              < 2 ^ valLaneBitsWhp n_max + (sl.alloc + 1) * 2 ^ valLaneBitsWhp n_max := by omega
            _ = (sl.alloc + 2) * 2 ^ valLaneBitsWhp n_max := by ring
            _ ≤ 2 ^ valLaneBitsWhp n_max * 2 ^ valLaneBitsWhp n_max := Nat.mul_le_mul_right _ h1
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
        dsimp only [sl1, splitRootIfFull]
        have hc : (metaCount (sl.nodes sl.root).metaWord == 2 * tMinWhp n_max - 1) = true := by
          simp [hfull]
        rw [hc]; simp only [↓reduceIte, mkNodeMeta, Bool.false_eq_true, Nat.zero_add]; rfl
      set p0 := (mkWhpCoreParams c U V w n_max, base)
      set w4prog :=
        writeBTreeNodeGenProg (((p0, sIdx), sl.alloc),
          (spPure.left.metaWord, (spPure.left.keysWord, spPure.left.valsWord))) >>= fun _ =>
        writeBTreeNodeGenProg (((p0, sIdx), sl.alloc + 1),
          (spPure.right.metaWord, (spPure.right.keysWord, spPure.right.valsWord))) >>= fun _ =>
        writeBTreeNodeGenProg (((p0, sIdx), sl.root),
          (newRootNd.metaWord, (newRootNd.keysWord, newRootNd.valsWord))) >>= fun _ =>
        writeSliceAllocGenProg ((p0, sIdx), sl.alloc + 2)
      have hsp_res := clientResult_splitFullNodeGenProg (U := U) (V := V) (w := w)
        hth (sl.nodes sl.root) s
      dsimp only at hsp_res
      have hs'_eq : (Memory.spec 0).clientState s
          (readSliceHeaderGenProg (p0, sIdx) >>= fun hdr =>
            if hdr.1 = 0 then
              writeBTreeNodeGenProg (((p0, sIdx), 0), (1, (0, 0))) >>= fun _ =>
              writeSliceHeaderGenProg ((p0, sIdx), (1, 0)) >>= fun _ =>
              pure (1, 0)
            else
              readBTreeNodeGenProg ((p0, sIdx), hdr.2) >>= fun rootNd =>
              if rootNd.1 / 2 = 2 * tMinWhp n_max - 1 then
                splitFullNodeGenProg (p0.1, rootNd) >>= fun sp =>
                writeSplitFourOpProg ((p0, sIdx),
                  (((hdr.1, sp.1), (hdr.1 + 1, sp.2.2)),
                   ((hdr.2, (2, (sp.2.1, hdr.1 + ((hdr.1 + 1) <<< valLaneBitsWhp n_max)))),
                    hdr.1 + 2))) >>= fun _ =>
                pure (hdr.1 + 2, hdr.2)
              else pure hdr) =
          (Memory.spec 0).clientState s w4prog := by
        rw [clientState_bind, hcs_h, hres_h]
        simp only [ha_ne, ↓reduceIte]
        rw [clientState_bind, hnd_st, hnd_res]
        dsimp only
        rw [hcnt_div]
        simp only [hfull, ↓reduceIte]
        rw [clientState_bind, clientState_splitFullNodeGenProg, hsp_res]
        dsimp only
        rw [clientState_bind_pure, writeSplitFourOpProg_eq]
      dsimp only [sl1] at hsl1_def ha1_le hrt1 hT1_rt hT1_nf hv1
      rw [hens, hs'_eq]
      refine ⟨hfr4, ?_, ?_, ?_, hsl1_def.symm ▸ hrep4, by omega,
        ⟨T1, hT1_rt, by omega, hT1_nf, hv1⟩, hoth4,
        fun idx hidx h1 _ => hbm4 idx hidx h1, hout4⟩
      · rw [clientResult_bind, hcs_h, hres_h]
        simp only [ha_ne, ↓reduceIte]
        rw [clientResult_bind, hnd_st, hnd_res]
        dsimp only
        rw [hcnt_div]
        simp only [hfull, ↓reduceIte]
        rw [clientResult_bind, clientState_splitFullNodeGenProg, hsp_res]
        dsimp only
        rw [clientResult_bind_pure, hsl1_def]
      · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hcs_h, hmc_h, hres_h]
        simp only [ha_ne, ↓reduceIte]
        rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hnd_st, hnd_mc, hnd_res]
        dsimp only
        rw [hcnt_div]
        simp only [hfull, ↓reduceIte]
        rw [← PFunctor.FreeM.bind_eq_bind]
        rw [memoryCost_bind, clientState_splitFullNodeGenProg, memoryCost_splitFullNodeGenProg,
          hsp_res]
        dsimp only
        rw [← PFunctor.FreeM.bind_eq_bind]
        rw [memoryCost_bind, memoryCost_pure, Nat.add_zero, writeSplitFourOpProg_eq]
        dsimp only [w4prog] at hmc4
        rw [hmc4]
      · refine validProg_bind hvp_h ?_
        rw [hcs_h, hres_h]; simp only [ha_ne, ↓reduceIte]
        refine validProg_bind hnd_vp ?_
        rw [hnd_st, hnd_res]; dsimp only; rw [hcnt_div]; simp only [hfull, ↓reduceIte]
        refine validProg_bind (validWhpProg_splitFullNodeGenProg _) ?_
        rw [clientState_splitFullNodeGenProg, hsp_res]; dsimp only
        rw [writeSplitFourOpProg_eq]
        exact validProg_bind hvp4 (validProg_pure _)
    · -- Subcase 2b: Non-full root (`splitRootIfFull sl = sl`)
      have hsl1_eq : sl1 = sl := by
        dsimp only [sl1, splitRootIfFull]
        have hc : (metaCount (sl.nodes sl.root).metaWord == 2 * tMinWhp n_max - 1) = false := by
          simp [hfull]
        rw [hc]; rfl
      set p0 := (mkWhpCoreParams c U V w n_max, base)
      have hs'_eq : (Memory.spec 0).clientState s
          (readSliceHeaderGenProg (p0, sIdx) >>= fun hdr =>
            if hdr.1 = 0 then
              writeBTreeNodeGenProg (((p0, sIdx), 0), (1, (0, 0))) >>= fun _ =>
              writeSliceHeaderGenProg ((p0, sIdx), (1, 0)) >>= fun _ =>
              pure (1, 0)
            else
              readBTreeNodeGenProg ((p0, sIdx), hdr.2) >>= fun rootNd =>
              if rootNd.1 / 2 = 2 * tMinWhp n_max - 1 then
                splitFullNodeGenProg (p0.1, rootNd) >>= fun sp =>
                writeSplitFourOpProg ((p0, sIdx),
                  (((hdr.1, sp.1), (hdr.1 + 1, sp.2.2)),
                   ((hdr.2, (2, (sp.2.1, hdr.1 + ((hdr.1 + 1) <<< valLaneBitsWhp n_max)))),
                    hdr.1 + 2))) >>= fun _ =>
                pure (hdr.1 + 2, hdr.2)
              else pure hdr) = s := by
        rw [clientState_bind, hcs_h, hres_h]
        simp only [ha_ne, ↓reduceIte]
        rw [clientState_bind, hnd_st, hnd_res]
        dsimp only; rw [hcnt_div]; simp only [hfull, ↓reduceIte]; rfl
      dsimp only [sl1] at hsl1_eq
      rw [hens, hs'_eq, hsl1_eq]
      refine ⟨rfl, ?_, ?_, ?_, hrep, by omega,
        ⟨T, hrt, hht_T.le, by omega, hT⟩,
        fun _ _ _ _ hr => hr, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
      · rw [clientResult_bind, hcs_h, hres_h]
        simp only [ha_ne, ↓reduceIte]
        rw [clientResult_bind, hnd_st, hnd_res]
        dsimp only; rw [hcnt_div]; simp only [hfull, ↓reduceIte,
          StateTransitionSpec.clientResult_pure]
      · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hcs_h, hmc_h, hres_h]
        simp only [ha_ne, ↓reduceIte]
        rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hnd_st, hnd_mc, hnd_res]
        dsimp only; rw [hcnt_div]; simp only [hfull, ↓reduceIte, memoryCost_pure]; omega
      · refine validProg_bind hvp_h ?_
        rw [hcs_h, hres_h]; simp only [ha_ne, ↓reduceIte]
        refine validProg_bind hnd_vp ?_
        rw [hnd_st, hnd_res]; dsimp only; rw [hcnt_div]; simp only [hfull, ↓reduceIte]
        exact validProg_pure _

private theorem realizes_ensureAndSplitRootGen :
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
    dsimp only [EnsureRootGenPre] at h
    obtain ⟨c, U, V, w₀, n_max, insCount, sl, mapFn,
      henv, rfl, hsIdx, hins, hrep, hv⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have ht8 := eight_le_tMinWhp hth
    have h64 := sixty_four_le_nSliceWhp n_max
    obtain ⟨hcs_h, hres_h, _, _⟩ := readSliceHeaderGenProg_spec hth henv.2.1 hsIdx hrep (s := s)
    dsimp only at hcs_h hres_h
    simp only [hcs_h] at *
    simp only [hres_h] at *
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
      simp only [hnd_st] at *
      simp only [hnd_res] at *
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

private def SplitFullChildPre (w : ℕ)
    (x : ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) ×
      (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))))) (_s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max,
    WhpLargeEnv c U V w₀ n_max w x.1.1.1.1.2 ∧
    x.1.1.1.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    x.1.1.1.2 < 3 * numBucketsWhp n_max ∧
    x.1.2.1 + 1 ≤ nSliceWhp n_max ∧
    x.1.2.2 < x.1.2.1 ∧
    x.2.2.1 < x.1.2.1 ∧
    x.2.1.1.1 < 2 * tMinWhp n_max - 1 ∧
    x.2.1.1.2 ≤ x.2.1.1.1 ∧
    x.2.1.2.1 < 2 ^ (x.2.1.1.1 * keyLaneBitsWhp n_max) ∧
    x.2.1.2.2 < 2 ^ ((x.2.1.1.1 + 1) * valLaneBitsWhp n_max)

private def splitFullChildBody
    (x : ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) ×
      (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))))) : Memory.Prog (ℕ × ℕ) := do
  let sp ← splitNodeOpProg (x.1.1.1.1.1, x.2.2.2)
  let rightIdx ← pure x.1.2.1
  let newAlloc ← pure (x.1.2.1 + 1)
  let pMeta ← pure (2 * (x.2.1.1.1 + 1))
  let pKeys ← wordInsertOpProg (((wpWKey x.1.1.1.1.1, x.2.1.1.2), sp.2.1), x.2.1.2.1)
  let r1 ← pure (x.2.1.1.2 + 1)
  let pVals ← wordInsertOpProg (((wpWVal x.1.1.1.1.1, r1), rightIdx), x.2.1.2.2)
  writeSplitFourOpProg (x.1.1.1, (((x.2.2.1, sp.1), (rightIdx, sp.2.2)),
    ((x.1.2.2, (pMeta, (pKeys, pVals))), newAlloc)))
  if sp.2.1 < x.1.1.2 then
    pure (newAlloc, rightIdx)
  else
    pure (newAlloc, x.2.2.1)

private theorem realizes_splitFullChildBody :
    Realizes .exact splitFullChildBody
      (WordEncoding.encode (α := ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) ×
        (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))))))
      (WordEncoding.encode (α := ℕ × ℕ))
      SplitFullChildPre
      (fun _ _ => 0) := by
  have hsp := realizes_splitNodeOp
  have hwi := realizes_wordInsertOp
  have hsf := realizes_writeSplitFourOp
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨⟨cp, base⟩, sIdx⟩, q⟩, ⟨alloc, cur⟩⟩, ⟨⟨⟨c0, r0⟩, ⟨pKW, pVW⟩⟩,
      ⟨childIdx, ⟨cmW, ⟨ckW, cvW⟩⟩⟩⟩⟩
    dsimp only [SplitFullChildPre] at h
    obtain ⟨c, U, V, w₀, n_max, henv, rfl, hsIdx, halloc1, hcur, hchild, hc0, hr_le,
      hkw_cnt, hvw_cnt⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    have ht8 := eight_le_tMinWhp hth
    have hns_lt_n := (large_bounds_lt_n_max hth).2.1
    obtain ⟨_, _, _, hns_lt_v⟩ := (btree_slice_param_bounds hth).1
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    have hkl2 : 2 ≤ keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp fpBitsWhp; omega
    try simp only [wp_large_M hth] at *
    try simp only [wp_large_nSlice hth] at *
    try simp only [wp_large_wKey hth] at *
    try simp only [wp_large_wVal hth] at *
    have h2t_k : 2 * tMinWhp n_max ≤ 2 * tMinWhp n_max * keyLaneBitsWhp n_max :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h4t_k : 2 * (2 * tMinWhp n_max) ≤ 2 * tMinWhp n_max * keyLaneBitsWhp n_max := by
      rw [Nat.mul_comm 2 (2 * tMinWhp n_max)]; exact Nat.mul_le_mul_left _ hkl2
    first
    | omega
    | exact ⟨base, c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact henv.fits_of_le_n_max (by omega)
    | exact (by omega : 2 * (c0 + 1) < w).trans Nat.lt_two_pow_self
    | exact (by omega : c0 + 1 < w).trans Nat.lt_two_pow_self
    | exact (by omega : r0 + 1 < w).trans Nat.lt_two_pow_self
    | (refine ⟨c0, hr_le, (Nat.mul_le_mul_right _ (by omega)).trans_lt hkw_lt, ?_, hkw_cnt⟩
       have hres := clientResult_splitNodeOpProg (U := U) (V := V) (w := w) hth ⟨cmW, ckW, cvW⟩ s
       dsimp only at hres
       rw [hres]
       unfold splitFullNode keyLaneBitsWhp
       by_cases hlf : metaIsLeaf cmW = true <;>
         (simp only [hlf, Bool.false_eq_true, ↓reduceIte]
          rw [laneGet_eq_div_mod]
          exact Nat.mod_lt _ (Nat.two_pow_pos _)))
    | refine ⟨c0 + 1, Nat.succ_le_succ hr_le,
        (Nat.mul_le_mul_right _ (by omega)).trans_lt hvw_lt,
        (by omega : alloc < nSliceWhp n_max).trans hns_lt_v, hvw_cnt⟩

/-- Opaque full-child split-and-link subroutine for `descendSplitStepGenProg`. -/
@[irreducible] private def splitFullChildOpProg
    (x : ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) ×
      (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))))) : Memory.Prog (ℕ × ℕ) :=
  splitFullChildBody x

private theorem realizes_splitFullChildOp :
    Realizes .exact splitFullChildOpProg
      (WordEncoding.encode (α := ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) ×
        (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))))))
      (WordEncoding.encode (α := ℕ × ℕ))
      SplitFullChildPre
      (fun _ _ => 0) := by
  unfold splitFullChildOpProg; exact realizes_splitFullChildBody

/-- Precondition for one proactive-splitting descent step
`d = ((((cp, base), sIdx), q), (alloc, cur))`. -/
private def DescendSplitStepGenPre (w : ℕ)
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max sl isRoot lo hi mapFn T,
    WhpLargeEnv c U V w₀ n_max w d.1.1.1.2 ∧
    d.1.1.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    d.1.1.2 < 3 * numBucketsWhp n_max ∧
    BTreeSliceMemRep d.1.1.1.2 c U V w₀ n_max d.1.1.2 sl s.mem ∧
    sl.alloc = d.2.1 ∧
    sl.alloc + 1 ≤ nSliceWhp n_max ∧
    T.rootIdx = d.2.2 ∧
    metaCount (sl.nodes d.2.2).metaWord < 2 * tMinWhp n_max - 1 ∧
    lo ≤ d.1.2 ∧ d.1.2 ≤ hi ∧ hi < 2 ^ fpBitsWhp n_max ∧
    ValidSubtree isRoot (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.alloc sl.nodes lo hi mapFn T

/-- Single step of `descendSplitToLeaf` (`d = ((((cp, base), sIdx), q), (alloc, cur))`). -/
private def descendSplitStepGenProg
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let nd ← readBTreeNodeGenProg (d.1.1, d.2.2)
  let isLf ← pure (nd.1 % 2)
  let z1 ← pure 1
  if isLf = z1 then
    pure d.2
  else do
    let cnt ← pure (nd.1 / 2)
    let r ← swarRankGenProg (d.1.1.1.1, ((cnt, d.1.2), nd.2.1))
    let childIdx ← laneGetGenProg ((wpWVal d.1.1.1.1, nd.2.2), r)
    let childNd ← readBTreeNodeGenProg (d.1.1, childIdx)
    let childCnt ← pure (childNd.1 / 2)
    let fullCnt ← pure (2 * wpTMin d.1.1.1.1 - 1)
    if childCnt = fullCnt then
      splitFullChildOpProg (d, (((cnt, r), (nd.2.1, nd.2.2)), (childIdx, childNd)))
    else
      pure (d.2.1, childIdx)

private theorem memoryCost_descendSplitStepGenProg_pos
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (descendSplitStepGenProg d) s := by
  unfold descendSplitStepGenProg
  rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readBTreeNodeGenProg]
  omega

private theorem realizes_descendSplitStepGen :
    Realizes .exact descendSplitStepGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      DescendSplitStepGenPre
      (fun _ _ => 0) := by
  unfold descendSplitStepGenProg
  have hrn := realizes_readBTreeNodeGen
  have hsr := realizes_swarRankGen
  have hlg := realizes_laneGetGen
  have hsfc := realizes_splitFullChildOp
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨cp, base⟩, sIdx⟩, q⟩, ⟨alloc, cur⟩⟩
    dsimp only [DescendSplitStepGenPre] at h
    obtain ⟨c, U, V, w₀, n_max, sl, isRoot, lo, hi, mapFn, T,
      henv, rfl, hsIdx, hrep, halloc_eq, halloc1, hrt, hnf, hqlo, hqhi, hhi, hv⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    subst halloc_eq
    have ht8 := eight_le_tMinWhp hth
    have hns_lt_n := (large_bounds_lt_n_max hth).2.1
    obtain ⟨ht3, _, hkey_lt, hns_lt_v⟩ := (btree_slice_param_bounds hth).1
    obtain ⟨hcur_lt, hcnt_le, _, hkw_cnt, _, _, hlanes⟩ := validSubtree_root_bounds hth hhi hv
    rw [hrt] at hcur_lt hcnt_le hkw_cnt hlanes
    obtain ⟨hcs_n, hres_n, _, _⟩ := readBTreeNodeGenProg_spec hth henv.2.1 hsIdx hcur_lt hrep
      (s := s)
    dsimp only at hcs_n hres_n
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    have hcnt_div : (sl.nodes cur).metaWord / 2 = metaCount (sl.nodes cur).metaWord := rfl
    simp only [hcs_n] at *
    simp only [hres_n] at *
    try simp only [wp_large_M hth] at *
    try simp only [wp_large_nSlice hth] at *
    try simp only [wp_large_tMin hth] at *
    try simp only [wp_large_wVal hth] at *
    try simp only [clientResult_swarRankGenProg hth] at *
    try simp only [clientResult_laneGetGenProg] at *
    try first
      | decide
      | omega
      | exact henv.fits_const (by decide)
      | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · refine ⟨⟨base, c, U, V, w, n_max, henv, rfl⟩, ?_, ?_, ?_, ?_⟩
    · simp only [wp_large_capLanes hth]; change metaCount _ < _; omega
    · simp only [wp_large_powFp hth]; exact hqhi.trans_lt hhi
    · simp only [wp_large_wKey hth]; exact hkw_cnt
    · simp only [wp_large_wKey hth, wp_large_powFp hth]; exact hlanes
  · exact (Nat.le_mul_of_pos_left _ (by omega)).trans_lt hvw_lt
  · rw [hcnt_div]
    have hlanes' : ∀ j < metaCount (sl.nodes cur).metaWord,
        laneGet (fpBitsWhp n_max + 2) (sl.nodes cur).keysWord j < 2 ^ fpBitsWhp n_max := hlanes
    have hr_le : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max)
        (metaCount (sl.nodes cur).metaWord) q (sl.nodes cur).keysWord ≤
        metaCount (sl.nodes cur).metaWord := by
      rw [swarRank_eq_count_lt (by omega) hkey_lt (hqhi.trans_lt hhi) hkw_cnt hlanes']
      exact (card_filter_le _ _).trans_eq (card_range _)
    exact ((Nat.mul_le_mul_right _ (hr_le.trans (by omega))).trans_lt hvw_lt).trans
      Nat.lt_two_pow_self
  all_goals
    cases T with
    | leaf idx c0 =>
      dsimp only [BTreeTree.rootIdx] at hrt
      subst idx
      have hm1 : (sl.nodes cur).metaWord % 2 = 1 := by
        rw [hv.2.1]; simp [mkNodeMeta, Nat.add_mul_mod_self_left]
      simp_all
    | branch idx c0 childTrees =>
      dsimp only [BTreeTree.rootIdx] at hrt
      subst idx
      obtain ⟨hr_le, _, _, _⟩ := branch_child_routing (by omega) hkey_lt hv hhi hqlo hqhi
      obtain ⟨_, hmeta, _, _, _, hvw_cnt, _, _, _, _, _, _, hcs_sub⟩ := hv
      have hc0_eq : metaCount (sl.nodes cur).metaWord = c0 := by rw [hmeta, metaCount_mkNodeMeta]
      let r_fin : Fin (c0 + 1) := ⟨swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q
        (sl.nodes cur).keysWord, Nat.lt_succ_of_le hr_le⟩
      have hval_r : laneGet (valLaneBitsWhp n_max) (sl.nodes cur).valsWord
          (swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q (sl.nodes cur).keysWord) =
          (childTrees r_fin).rootIdx := (hcs_sub r_fin).1
      have hchild_lt : (childTrees r_fin).rootIdx < sl.alloc :=
        (((hcs_sub r_fin).2).leafCount_le_card_nodeSet).1 _ (childTrees r_fin).rootIdx_mem_nodeSet
      obtain ⟨hndc_st, hndc_res, _, _⟩ :=
        readBTreeNodeGenProg_spec hth henv.2.1 hsIdx hchild_lt hrep (s := s)
      dsimp only at hndc_st hndc_res
      rw [hc0_eq] at hnf hkw_cnt
      simp only [hcnt_div] at *
      simp only [hc0_eq] at *
      simp only [hval_r] at *
      simp only [hndc_st] at *
      simp only [hndc_res] at *
      try dsimp only [SplitFullChildPre]
      have h2t_lt : 2 * tMinWhp n_max < w :=
        (Nat.le_mul_of_pos_right _ (by unfold keyLaneBitsWhp; positivity)).trans_lt hkw_lt
      first
      | omega
      | exact h2t_lt.trans Nat.lt_two_pow_self
      | exact ⟨c, U, V, w, n_max, henv, rfl, hsIdx, halloc1, hcur_lt, hchild_lt, hnf, hr_le,
          hkw_cnt, hvw_cnt⟩

/-- Bounded `iterate` loop refining `descendSplitToLeaf`
(`d = (((((cp, base), sIdx), q), (alloc, cur)), fuel)`). -/
private def descendSplitLoopGenProg
    (d : ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ) : Memory.Prog (ℕ × ℕ) :=
  iterate descendSplitStepGenProg d.1.1 d.2 d.1.2

private theorem realizes_descendSplitLoopGen :
    Realizes .exact descendSplitLoopGenProg
      (WordEncoding.encode (α := ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d s =>
        iterationSafe descendSplitStepGenProg DescendSplitStepGenPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_descendSplitStepGen memoryCost_descendSplitStepGenProg_pos

private theorem descendSplitLoopGenProg_spec {isRoot : Bool}
    {c U V w n_max base sIdx q cur fuel lo hi : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {T : BTreeTree} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (halloc_fuel : sl.alloc + fuel ≤ nSliceWhp n_max)
    (hrt : T.rootIdx = cur)
    (hnf : metaCount (sl.nodes cur).metaWord < 2 * tMinWhp n_max - 1)
    (hht_le : T.height ≤ fuel)
    (hqlo : lo ≤ q) (hqhi : q ≤ hi) (hhi : hi < 2 ^ fpBitsWhp n_max)
    (hv : ValidSubtree isRoot (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.alloc sl.nodes lo hi mapFn T) :
    let d0 := (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
    let prog := descendSplitLoopGenProg ((d0, (sl.alloc, cur)), fuel)
    let p := descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      fuel sl cur q
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    (Memory.spec 0).clientResult s prog = (p.1.alloc, p.2) ∧
    memoryCost prog s ≤ 52 * fuel ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    iterationSafe descendSplitStepGenProg DescendSplitStepGenPre w d0 fuel (sl.alloc, cur) s ∧
    BTreeSliceMemRep base c U V w n_max sIdx p.1 s'.mem ∧
    (∃ isR cntL loL hiL,
      cntL < 2 * tMinWhp n_max - 1 ∧
      loL ≤ q ∧ q ≤ hiL ∧ hiL < 2 ^ fpBitsWhp n_max ∧
      ValidSubtree isR (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        p.1.alloc p.1.nodes loL hiL mapFn (.leaf p.2 cntL)) ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ idx < 16 * numBucketsWhp n_max,
      idx ≠ 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, (a < base + offBktMeta c U V w n_max ∨
        (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
        base + offTrieChild0 c U V w n_max ≤ a) →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have ht8 := eight_le_tMinWhp hth
  obtain ⟨ht3, hmeta_cap, hkey_lt, hns_lt⟩ := (btree_slice_param_bounds hth).1
  set d0 := (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
  induction fuel generalizing isRoot cur lo hi sl T s with
  | zero =>
    cases T with
    | branch idx c0 cs => simp [BTreeTree.height] at hht_le
    | leaf idx c0 =>
      dsimp only [BTreeTree.rootIdx] at hrt
      subst idx
      have hc0 : c0 < 2 * tMinWhp n_max - 1 := by rwa [hv.2.1, metaCount_mkNodeMeta] at hnf
      exact ⟨rfl, rfl, by simp [descendSplitLoopGenProg, iterate, memoryCost_pure],
        validProg_pure _, trivial, hrep,
        ⟨isRoot, c0, lo, hi, hc0, hqlo, hqhi, hhi, hv⟩,
        fun _ _ _ _ hr => hr, fun _ _ _ => rfl, fun _ _ => rfl⟩
  | succ f ih =>
    have hsafe1 : DescendSplitStepGenPre w (d0, (sl.alloc, cur)) s :=
      ⟨c, U, V, w, n_max, sl, isRoot, lo, hi, mapFn, T,
        henv, rfl, hsIdx, hrep, rfl, by omega, hrt, hnf, hqlo, hqhi, hhi, hv⟩
    obtain ⟨hcur_lt, _, _, _, _, _, _⟩ := validSubtree_root_bounds hth hhi hv
    rw [hrt] at hcur_lt
    obtain ⟨hcs_n, hres_n, hmc_n, hvp_n⟩ := readBTreeNodeGenProg_spec hth hw hsIdx hcur_lt hrep
      (s := s)
    dsimp only at hcs_n hres_n hmc_n hvp_n
    cases T with
    | leaf idx c0 =>
      dsimp only [BTreeTree.rootIdx] at hrt
      subst idx
      have hmeta : (sl.nodes cur).metaWord = mkNodeMeta true c0 := hv.2.1
      have hmod1 : (sl.nodes cur).metaWord % 2 = 1 := by
        rw [hmeta]; simp [mkNodeMeta, Nat.add_mul_mod_self_left]
      have hstep_st : (Memory.spec 0).clientState s
          (descendSplitStepGenProg (d0, (sl.alloc, cur))) = s := by
        unfold descendSplitStepGenProg
        simp only [pure_bind]
        rw [clientState_bind, hcs_n, hres_n]
        simp only [hmod1, ↓reduceIte]; rfl
      have hstep_res : (Memory.spec 0).clientResult s
          (descendSplitStepGenProg (d0, (sl.alloc, cur))) = (sl.alloc, cur) := by
        unfold descendSplitStepGenProg
        simp only [pure_bind]
        rw [clientResult_bind, hcs_n, hres_n]
        simp only [hmod1, ↓reduceIte, StateTransitionSpec.clientResult_pure]
      have hstep_mc : memoryCost (descendSplitStepGenProg (d0, (sl.alloc, cur))) s = 6 := by
        unfold descendSplitStepGenProg
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
        rw [memoryCost_bind, hcs_n, hmc_n, hres_n]
        simp only [hmod1, ↓reduceIte, memoryCost_pure]
      have hstep_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
          (descendSplitStepGenProg (d0, (sl.alloc, cur))) := by
        unfold descendSplitStepGenProg
        simp only [pure_bind]
        refine validProg_bind hvp_n ?_
        rw [hcs_n, hres_n]; simp only [hmod1, ↓reduceIte]; exact validProg_pure _
      have hdesc_eq : descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (f + 1) sl cur q =
          descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            f sl cur q := by
        simp only [descendSplitToLeaf, hmeta, metaIsLeaf_mkNodeMeta, ↓reduceIte]
        cases f with
        | zero => rfl
        | succ f' => simp [descendSplitToLeaf, hmeta]
      obtain ⟨ih_fr, ih_res, ih_mc, ih_vp, ih_safe, ih_rep, ih_lf, ih_oth, ih_bm, ih_out⟩ :=
        ih (cur := cur) (T := .leaf cur c0) hrep (by omega) rfl hnf (by simp [BTreeTree.height])
          hqlo hqhi hhi hv (s := s)
      dsimp only [descendSplitLoopGenProg, iterate] at ih_fr ih_res ih_mc ih_vp ih_rep ⊢
      rw [clientState_bind, hstep_st, hstep_res, hdesc_eq]
      refine ⟨ih_fr, ?_, ?_, ?_, ⟨hsafe1, ?_⟩, ih_rep, ih_lf, ih_oth, ih_bm, ih_out⟩
      · rw [clientResult_bind, hstep_st, hstep_res]; exact ih_res
      · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_st, hstep_res, hstep_mc]
        have := ih_mc; omega
      · refine validProg_bind hstep_vp ?_
        rw [hstep_st, hstep_res]; exact ih_vp
      · rw [hstep_st, hstep_res]; exact ih_safe
    | branch idx c0 cs =>
      dsimp only [BTreeTree.rootIdx] at hrt
      subst idx
      obtain ⟨hr_le, hclo_q, hq_chi, _⟩ := branch_child_routing (by omega) hkey_lt hv hhi hqlo hqhi
      obtain ⟨_, hmeta, _, _, hkw_cur, hvw_cur, _, hhi_last, hmono, hnot_cur, _, _, hcs_sub⟩ := hv
      have hc0_lt : c0 < 2 * tMinWhp n_max - 1 := by rwa [hmeta, metaCount_mkNodeMeta] at hnf
      have hmod0 : (sl.nodes cur).metaWord % 2 ≠ 1 := by rw [hmeta]; simp [mkNodeMeta]
      have hcnt_div : (sl.nodes cur).metaWord / 2 = c0 := by
        rw [hmeta]; exact metaCount_mkNodeMeta false c0
      set r := swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q (sl.nodes cur).keysWord
      let r_fin : Fin (c0 + 1) := ⟨r, Nat.lt_succ_of_le hr_le⟩
      set childIdx := (cs r_fin).rootIdx
      have hval_r : laneGet (valLaneBitsWhp n_max) (sl.nodes cur).valsWord r = childIdx :=
        (hcs_sub r_fin).1
      have hchi_le : childHi (fpBitsWhp n_max + 2) hi c0 (sl.nodes cur).keysWord r ≤ hi := by
        unfold childHi
        split_ifs with hrc
        · rcases eq_or_lt_of_le (by omega : r ≤ c0 - 1) with heq | hlt
          · rw [heq]; exact hhi_last.le
          · exact (hmono r (c0 - 1) hlt (by omega)).le.trans hhi_last.le
        · exact le_rfl
      have hchild_ht : (cs r_fin).height ≤ f := by
        have hsup : (cs r_fin).height ≤ univ.sup fun i => (cs i).height :=
          Finset.le_sup (f := fun i => (cs i).height) (mem_univ r_fin)
        simp only [BTreeTree.height] at hht_le; omega
      obtain ⟨hchild_lt, hcnt_c_le, _, _, hk_c, hv_c, _⟩ :=
        validSubtree_root_bounds hth (hchi_le.trans_lt hhi) (hcs_sub r_fin).2
      dsimp only [childIdx] at *
      obtain ⟨hndc_st, hndc_res, hndc_mc, hndc_vp⟩ :=
        readBTreeNodeGenProg_spec hth hw hsIdx hchild_lt hrep (s := s)
      dsimp only at hndc_st hndc_res hndc_mc hndc_vp
      have hcntc_div : (sl.nodes childIdx).metaWord / 2 =
          metaCount (sl.nodes childIdx).metaWord := rfl
      by_cases hfull_c : metaCount (sl.nodes childIdx).metaWord = 2 * tMinWhp n_max - 1
      · -- Subcase B1: Child `childIdx` is full (`splitFullNode` + 3 node writes + alloc)
        set spPure := splitFullNode (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (sl.nodes childIdx)
        obtain ⟨hlM, hlK, hlV, hsep_lt, hrM, hrK, hrV⟩ := splitFullNode_bits_lt hth hk_c hv_c
        let parentNd' : BTreeNode :=
          ⟨mkNodeMeta false (c0 + 1),
            wordInsertAt (fpBitsWhp n_max + 2) r spPure.sep (sl.nodes cur).keysWord,
            wordInsertAt (valLaneBitsWhp n_max) (r + 1) sl.alloc (sl.nodes cur).valsWord⟩
        have hmP : parentNd'.metaWord < 2 ^ nodeMetaBitsWhp n_max := by
          dsimp only [parentNd', mkNodeMeta]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
        have hkP : parentNd'.keysWord < 2 ^ keysWordBitsWhp n_max := by
          dsimp only [parentNd']
          unfold keysWordBitsWhp keyLaneBitsWhp
          exact (wordInsertAt_lt hr_le hsep_lt hkw_cur).trans_le
            (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
        have hvP : parentNd'.valsWord < 2 ^ valsWordBitsWhp n_max := by
          dsimp only [parentNd']
          have hr_v : sl.alloc < 2 ^ valLaneBitsWhp n_max :=
            (by omega : sl.alloc < nSliceWhp n_max).trans hns_lt
          unfold valsWordBitsWhp
          exact (wordInsertAt_lt (Nat.succ_le_succ hr_le) hr_v hvw_cur).trans_le
            (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
        obtain ⟨hfr4, hmc4, hvp4, hrep4, hoth4, hbm4, hout4⟩ :=
          threeNodeWrites_and_alloc_sliceRep (newA := sl.alloc + 1)
            (idx1 := childIdx) (idx2 := sl.alloc) (idx3 := cur)
            (nd1 := spPure.left) (nd2 := spPure.right) (nd3 := parentNd')
            henv hsIdx hrep (by omega) (by omega) (by omega) (by omega)
            (fun v hv_lt => by omega) hlM hlK hlV hrM hrK hrV hmP hkP hvP (s := s)
        set nodes3 := Function.update
          (Function.update (Function.update sl.nodes childIdx spPure.left) sl.alloc spPure.right)
          cur parentNd'
        set sl_mid : BTreeSlice := ⟨sl.alloc + 1, sl.root, nodes3⟩
        set p0 := (mkWhpCoreParams c U V w n_max, base)
        set w4prog :=
          writeBTreeNodeGenProg (((p0, sIdx), childIdx),
            (spPure.left.metaWord, (spPure.left.keysWord, spPure.left.valsWord))) >>= fun _ =>
          writeBTreeNodeGenProg (((p0, sIdx), sl.alloc),
            (spPure.right.metaWord, (spPure.right.keysWord, spPure.right.valsWord))) >>= fun _ =>
          writeBTreeNodeGenProg (((p0, sIdx), cur),
            (parentNd'.metaWord, (parentNd'.keysWord, parentNd'.valsWord))) >>= fun _ =>
          writeSliceAllocGenProg ((p0, sIdx), sl.alloc + 1)
        set s4 := (Memory.spec 0).clientState s w4prog
        set nextCur := if spPure.sep < q then sl.alloc else childIdx
        have hsp_res := clientResult_splitFullNodeGenProg (U := U) (V := V) (w := w)
          hth (sl.nodes childIdx) s
        dsimp only at hsp_res
        have hr_eq_sw : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q
            (sl.nodes cur).keysWord = r := rfl
        have hmP_eq : parentNd'.metaWord = 2 * (c0 + 1) := by
          simp [parentNd', mkNodeMeta]
        have hstep_st : (Memory.spec 0).clientState s
            (descendSplitStepGenProg (d0, (sl.alloc, cur))) = s4 := by
          unfold descendSplitStepGenProg splitFullChildOpProg splitFullChildBody
            splitNodeOpProg wordInsertOpProg
          simp only [d0, pure_bind, wp_large_wVal hth, wp_large_wKey hth, wp_large_tMin hth]
          rw [clientState_bind, hcs_n, hres_n]
          simp only [hmod0, ↓reduceIte, hcnt_div]
          rw [clientState_bind, clientState_swarRankGenProg,
            clientResult_swarRankGenProg hth,
            clientState_bind, clientState_laneGetGenProg,
            clientResult_laneGetGenProg]
          rw [hr_eq_sw, hval_r]
          rw [clientState_bind, hndc_st, hndc_res]
          dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]
          rw [clientState_bind, clientState_splitFullNodeGenProg, hsp_res]
          dsimp only
          rw [clientState_bind, clientState_wordInsertAtGenProg,
            clientResult_wordInsertAtGenProg,
            clientState_bind, clientState_wordInsertAtGenProg,
            clientResult_wordInsertAtGenProg]
          rw [clientState_bind_pure_ite, writeSplitFourOpProg_eq, ← hmP_eq]
          dsimp only [s4, w4prog, parentNd', keyLaneBitsWhp, spPure, childIdx]
        have hstep_res : (Memory.spec 0).clientResult s
            (descendSplitStepGenProg (d0, (sl.alloc, cur))) = (sl.alloc + 1, nextCur) := by
          unfold descendSplitStepGenProg splitFullChildOpProg splitFullChildBody
            splitNodeOpProg wordInsertOpProg
          simp only [d0, pure_bind, wp_large_wVal hth, wp_large_wKey hth, wp_large_tMin hth]
          rw [clientResult_bind, hcs_n, hres_n]
          simp only [hmod0, ↓reduceIte, hcnt_div]
          rw [clientResult_bind, clientState_swarRankGenProg,
            clientResult_swarRankGenProg hth,
            clientResult_bind, clientState_laneGetGenProg,
            clientResult_laneGetGenProg]
          rw [hr_eq_sw, hval_r]
          rw [clientResult_bind, hndc_st, hndc_res]
          dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]
          rw [clientResult_bind, clientState_splitFullNodeGenProg, hsp_res]
          dsimp only
          rw [clientResult_bind, clientState_wordInsertAtGenProg,
            clientResult_wordInsertAtGenProg,
            clientResult_bind, clientState_wordInsertAtGenProg,
            clientResult_wordInsertAtGenProg]
          rw [clientResult_bind_pure_ite]
          dsimp only [nextCur]
          split_ifs <;> rfl
        have hstep_mc : memoryCost (descendSplitStepGenProg (d0, (sl.alloc, cur))) s ≤ 52 := by
          unfold descendSplitStepGenProg splitFullChildOpProg splitFullChildBody
            splitNodeOpProg wordInsertOpProg
          simp only [d0, pure_bind, wp_large_wVal hth, wp_large_wKey hth, wp_large_tMin hth]
          rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hcs_n, hmc_n, hres_n]
          simp only [hmod0, ↓reduceIte, hcnt_div]
          rw [← PFunctor.FreeM.bind_eq_bind]
          rw [memoryCost_bind, clientState_swarRankGenProg, memoryCost_swarRankGenProg,
            clientResult_swarRankGenProg hth]
          rw [← PFunctor.FreeM.bind_eq_bind]
          rw [memoryCost_bind, clientState_laneGetGenProg, memoryCost_laneGetGenProg,
            clientResult_laneGetGenProg]
          rw [hr_eq_sw, hval_r]
          rw [← PFunctor.FreeM.bind_eq_bind]
          rw [memoryCost_bind, hndc_st, hndc_mc, hndc_res]
          dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]
          rw [memoryCost_bind, clientState_splitFullNodeGenProg, memoryCost_splitFullNodeGenProg,
            hsp_res]
          dsimp only
          rw [memoryCost_bind, clientState_wordInsertAtGenProg, memoryCost_wordInsertAtGenProg,
            clientResult_wordInsertAtGenProg]
          rw [memoryCost_bind, clientState_wordInsertAtGenProg, memoryCost_wordInsertAtGenProg,
            clientResult_wordInsertAtGenProg]
          rw [memoryCost_bind]
          have hite_mc : ∀ s_end, memoryCost
              (if spPure.sep < q then pure (sl.alloc + 1, sl.alloc)
               else pure (sl.alloc + 1, (cs r_fin).rootIdx)) s_end = 0 := by
            intro _; split_ifs <;> rfl
          rw [hite_mc, Nat.add_zero, writeSplitFourOpProg_eq, ← hmP_eq]
          dsimp only [w4prog, parentNd', keyLaneBitsWhp, childIdx] at hmc4 ⊢
          rw [hmc4]
        have hstep_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
            (descendSplitStepGenProg (d0, (sl.alloc, cur))) := by
          unfold descendSplitStepGenProg splitFullChildOpProg splitFullChildBody
            splitNodeOpProg wordInsertOpProg
          simp only [d0, pure_bind, wp_large_wVal hth, wp_large_wKey hth, wp_large_tMin hth]
          refine validProg_bind hvp_n ?_
          rw [hcs_n, hres_n]; simp only [hmod0, ↓reduceIte, hcnt_div]
          refine validProg_bind (validWhpProg_swarRankGenProg _) ?_
          rw [clientState_swarRankGenProg, clientResult_swarRankGenProg hth]
          refine validProg_bind (validWhpProg_laneGetGenProg _) ?_
          rw [clientState_laneGetGenProg, clientResult_laneGetGenProg]
          rw [hr_eq_sw, hval_r]
          refine validProg_bind hndc_vp ?_
          rw [hndc_st, hndc_res]; dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]
          refine validProg_bind (validWhpProg_splitFullNodeGenProg _) ?_
          rw [clientState_splitFullNodeGenProg, hsp_res]; dsimp only
          refine validProg_bind (validWhpProg_wordInsertAtGenProg _) ?_
          rw [clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg]
          refine validProg_bind (validWhpProg_wordInsertAtGenProg _) ?_
          rw [clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg]
          rw [writeSplitFourOpProg_eq, ← hmP_eq]
          refine validProg_bind hvp4 ?_
          split_ifs <;> exact validProg_pure _
        -- Downward subtree split witness via `splitFullNode_spec`
        have hchild_ne_cur : childIdx ≠ cur := fun heq =>
          hnot_cur r_fin (heq ▸ (cs r_fin).rootIdx_mem_nodeSet)
        have hlr_ne : childIdx ≠ sl.alloc := by omega
        have hcur_ne_r : cur ≠ sl.alloc := by omega
        have hl_nd : nodes3 childIdx = spPure.left := by
          dsimp only [nodes3]
          rw [Function.update_of_ne hchild_ne_cur, Function.update_of_ne hlr_ne,
            Function.update_self]
        have hr_nd : nodes3 sl.alloc = spPure.right := by
          dsimp only [nodes3]
          rw [Function.update_of_ne hcur_ne_r.symm, Function.update_self]
        have herase : ∀ v ∈ (cs r_fin).nodeSet.erase childIdx,
            nodes3 v = sl.nodes v ∧ v ≠ childIdx ∧ v ≠ sl.alloc := by
          intro v hv_er
          obtain ⟨hv_ne_c, hv_mem⟩ := mem_erase.mp hv_er
          have hv_lt : v < sl.alloc := (((hcs_sub r_fin).2).leafCount_le_card_nodeSet).1 v hv_mem
          have hv_ne_r : v ≠ sl.alloc := by omega
          have hv_ne_cur : v ≠ cur := fun heq => hnot_cur r_fin (heq ▸ hv_mem)
          refine ⟨?_, hv_ne_c, hv_ne_r⟩
          dsimp only [nodes3]
          rw [Function.update_of_ne hv_ne_cur, Function.update_of_ne hv_ne_r,
            Function.update_of_ne hv_ne_c]
        obtain ⟨leftT, rightT, hrtL, hrtR, hcntL_le, hcntR_eq, hhtL, hhtR, _, _,
          _, hclo_sep, hsep_chi, _, hvL, hvR⟩ :=
          splitFullNode_spec (alloc' := sl.alloc + 1) (nodes' := nodes3)
            (leftIdx := childIdx) (rightIdx := sl.alloc) (by omega) (hcs_sub r_fin).2 hfull_c
            (by omega) (by omega) (by omega) hlr_ne hl_nd hr_nd herase
        have hdesc_eq : descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max)
            (tMinWhp n_max) (f + 1) sl cur q =
            descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max)
              (tMinWhp n_max) f sl_mid nextCur q := by
          dsimp only [descendSplitToLeaf]
          have hc : (metaCount (sl.nodes childIdx).metaWord == 2 * tMinWhp n_max - 1) = true := by
            simp [hfull_c]
          rw [hmeta, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta]
          simp only [Bool.false_eq_true, ↓reduceIte]
          change (
            let r0 := swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q
              (sl.nodes cur).keysWord
            let childIdx0 := laneGet (valLaneBitsWhp n_max) (sl.nodes cur).valsWord r0
            if (metaCount (sl.nodes childIdx0).metaWord == 2 * tMinWhp n_max - 1) = true
            then _ else _) = _
          have hr_eq : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q
              (sl.nodes cur).keysWord = r := rfl
          dsimp only
          rw [hr_eq, hval_r, hc]
          simp only [↓reduceIte]
          rfl
        have hih_branch :
            let p := descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              f sl_mid nextCur q
            let s' := (Memory.spec 0).clientState s4
              (descendSplitLoopGenProg ((d0, (sl_mid.alloc, nextCur)), f))
            s'.frontier = s4.frontier ∧
            (Memory.spec 0).clientResult s4
              (descendSplitLoopGenProg ((d0, (sl_mid.alloc, nextCur)), f)) = (p.1.alloc, p.2) ∧
            memoryCost (descendSplitLoopGenProg ((d0, (sl_mid.alloc, nextCur)), f)) s4 ≤ 52 * f ∧
            ValidProg w (base + largeSpaceWhp c U V w n_max) s4
              (descendSplitLoopGenProg ((d0, (sl_mid.alloc, nextCur)), f)) ∧
            iterationSafe descendSplitStepGenProg DescendSplitStepGenPre w d0 f
              (sl_mid.alloc, nextCur) s4 ∧
            BTreeSliceMemRep base c U V w n_max sIdx p.1 s'.mem ∧
            (∃ isR cntL loL hiL,
              cntL < 2 * tMinWhp n_max - 1 ∧
              loL ≤ q ∧ q ≤ hiL ∧ hiL < 2 ^ fpBitsWhp n_max ∧
              ValidSubtree isR (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                p.1.alloc p.1.nodes loL hiL mapFn (.leaf p.2 cntL)) ∧
            (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
              BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s4.mem →
              BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
            (∀ idx < 16 * numBucketsWhp n_max,
              idx ≠ 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) →
              readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
                readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s4.mem idx) ∧
            (∀ a, (a < base + offBktMeta c U V w n_max ∨
                (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
                base + offTrieChild0 c U V w n_max ≤ a) →
              s'.mem a = s4.mem a) := by
          by_cases hsq : spPure.sep < q
          · have hnc : nextCur = sl.alloc := by simp [nextCur, hsq]
            dsimp only [spPure, childIdx] at hsq
            rw [hnc]
            exact ih hrep4 (by dsimp [sl_mid]; omega) hrtR
              (by dsimp [sl_mid]; omega) (by rw [hhtR]; exact hchild_ht)
              (by omega) hq_chi (hchi_le.trans_lt hhi) hvR (s := s4)
          · have hnc : nextCur = childIdx := by simp [nextCur, hsq]
            dsimp only [spPure, childIdx] at hsq
            rw [hnc]
            exact ih hrep4 (by dsimp [sl_mid]; omega) hrtL
              (by dsimp [sl_mid]; omega) (by rw [hhtL]; exact hchild_ht)
              hclo_q (by omega) (hsep_chi.trans_le (hchi_le.trans hhi.le)) hvL (s := s4)
        obtain ⟨ih_fr, ih_res, ih_mc, ih_vp, ih_safe, ih_rep, ih_lf, ih_oth, ih_bm, ih_out⟩ :=
          hih_branch
        dsimp only [sl_mid] at ih_fr ih_res ih_mc ih_vp ih_safe ih_rep ih_oth ih_bm ih_out
        dsimp only [descendSplitLoopGenProg, iterate] at ih_fr ih_res ih_mc ih_vp ih_rep ⊢
        dsimp only [descendSplitLoopGenProg, iterate] at ih_oth ih_bm ih_out
        rw [clientState_bind, hstep_st, hstep_res, hdesc_eq]
        refine ⟨ih_fr.trans hfr4, ?_, ?_, ?_, ⟨hsafe1, ?_⟩, ih_rep, ih_lf, ?_, ?_, ?_⟩
        · rw [clientResult_bind, hstep_st, hstep_res]; exact ih_res
        · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_st, hstep_res]
          omega
        · refine validProg_bind hstep_vp ?_
          rw [hstep_st, hstep_res]; exact ih_vp
        · rw [hstep_st, hstep_res]; exact ih_safe
        · intro sIdx' hsIdx' hne sl₂ hr₂
          exact ih_oth sIdx' hsIdx' hne sl₂ (hoth4 sIdx' hsIdx' hne sl₂ hr₂)
        · intro idx hidx hneA
          exact (ih_bm idx hidx hneA).trans (hbm4 idx hidx hneA)
        · intro a ha
          exact (ih_out a ha).trans (hout4 a ha)
      · -- Subcase B2: Child `childIdx` is already non-full (`< 2 * tMin - 1`)
        have hcnt_c_le' : metaCount (sl.nodes childIdx).metaWord ≤ 2 * tMinWhp n_max - 1 :=
          hcnt_c_le
        have hnf_c : metaCount (sl.nodes childIdx).metaWord < 2 * tMinWhp n_max - 1 := by omega
        set p0 := (mkWhpCoreParams c U V w n_max, base)
        have hr_eq_sw : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q
            (sl.nodes cur).keysWord = r := rfl
        have hstep_st : (Memory.spec 0).clientState s
            (descendSplitStepGenProg (d0, (sl.alloc, cur))) = s := by
          unfold descendSplitStepGenProg
          simp only [d0, pure_bind, wp_large_wVal hth, wp_large_tMin hth]
          rw [clientState_bind, hcs_n, hres_n]
          simp only [hmod0, ↓reduceIte, hcnt_div]
          rw [clientState_bind, clientState_swarRankGenProg,
            clientResult_swarRankGenProg hth,
            clientState_bind, clientState_laneGetGenProg,
            clientResult_laneGetGenProg]
          rw [hr_eq_sw, hval_r]
          rw [clientState_bind, hndc_st, hndc_res]
          dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]; rfl
        have hstep_res : (Memory.spec 0).clientResult s
            (descendSplitStepGenProg (d0, (sl.alloc, cur))) = (sl.alloc, childIdx) := by
          unfold descendSplitStepGenProg
          simp only [d0, pure_bind, wp_large_wVal hth, wp_large_tMin hth]
          rw [clientResult_bind, hcs_n, hres_n]
          simp only [hmod0, ↓reduceIte, hcnt_div]
          rw [clientResult_bind, clientState_swarRankGenProg,
            clientResult_swarRankGenProg hth,
            clientResult_bind, clientState_laneGetGenProg,
            clientResult_laneGetGenProg]
          rw [hr_eq_sw, hval_r]
          rw [clientResult_bind, hndc_st, hndc_res]
          dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte,
            StateTransitionSpec.clientResult_pure]
          rfl
        have hstep_mc : memoryCost (descendSplitStepGenProg (d0, (sl.alloc, cur))) s ≤ 52 := by
          unfold descendSplitStepGenProg
          simp only [d0, pure_bind, wp_large_wVal hth, wp_large_tMin hth]
          rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hcs_n, hmc_n, hres_n]
          simp only [hmod0, ↓reduceIte, hcnt_div]
          rw [← PFunctor.FreeM.bind_eq_bind]
          rw [memoryCost_bind, clientState_swarRankGenProg, memoryCost_swarRankGenProg,
            clientResult_swarRankGenProg hth]
          rw [memoryCost_bind, clientState_laneGetGenProg, memoryCost_laneGetGenProg,
            clientResult_laneGetGenProg]
          rw [hr_eq_sw, hval_r]
          rw [memoryCost_bind, hndc_st, hndc_mc, hndc_res]
          dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte, memoryCost_pure]; omega
        have hstep_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
            (descendSplitStepGenProg (d0, (sl.alloc, cur))) := by
          unfold descendSplitStepGenProg
          simp only [d0, pure_bind, wp_large_wVal hth, wp_large_tMin hth]
          refine validProg_bind hvp_n ?_
          rw [hcs_n, hres_n]; simp only [hmod0, ↓reduceIte, hcnt_div]
          refine validProg_bind (validWhpProg_swarRankGenProg _) ?_
          rw [clientState_swarRankGenProg, clientResult_swarRankGenProg hth]
          refine validProg_bind (validWhpProg_laneGetGenProg _) ?_
          rw [clientState_laneGetGenProg, clientResult_laneGetGenProg]
          rw [hr_eq_sw, hval_r]
          refine validProg_bind hndc_vp ?_
          rw [hndc_st, hndc_res]; dsimp only; rw [hcntc_div]; simp only [hfull_c, ↓reduceIte]
          exact validProg_pure _
        have hdesc_eq : descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max)
            (tMinWhp n_max) (f + 1) sl cur q =
            descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max)
              (tMinWhp n_max) f sl childIdx q := by
          dsimp only [descendSplitToLeaf]
          have hc : (metaCount (sl.nodes childIdx).metaWord == 2 * tMinWhp n_max - 1) = false := by
            simp [hfull_c]
          rw [hmeta, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta]
          simp only [Bool.false_eq_true, ↓reduceIte]
          change (
            let r0 := swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q
              (sl.nodes cur).keysWord
            let childIdx0 := laneGet (valLaneBitsWhp n_max) (sl.nodes cur).valsWord r0
            if (metaCount (sl.nodes childIdx0).metaWord == 2 * tMinWhp n_max - 1) = true
            then _ else _) = _
          have hr_eq : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) c0 q
              (sl.nodes cur).keysWord = r := rfl
          dsimp only; rw [hr_eq, hval_r, hc]; simp only [Bool.false_eq_true, ↓reduceIte]; rfl
        obtain ⟨ih_fr, ih_res, ih_mc, ih_vp, ih_safe, ih_rep, ih_lf, ih_oth, ih_bm, ih_out⟩ :=
          ih (cur := childIdx) hrep (by omega) rfl hnf_c hchild_ht hclo_q hq_chi
            (hchi_le.trans_lt hhi) (hcs_sub r_fin).2 (s := s)
        dsimp only [descendSplitLoopGenProg, iterate] at ih_fr ih_res ih_mc ih_vp ih_rep ⊢
        dsimp only [descendSplitLoopGenProg, iterate] at ih_oth ih_bm ih_out
        rw [clientState_bind, hstep_st, hstep_res, hdesc_eq]
        refine ⟨ih_fr, ?_, ?_, ?_, ⟨hsafe1, ?_⟩, ih_rep, ih_lf, ih_oth, ih_bm, ih_out⟩
        · rw [clientResult_bind, hstep_st, hstep_res]; exact ih_res
        · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_st, hstep_res]
          have := hstep_mc; have := ih_mc; omega
        · refine validProg_bind hstep_vp ?_
          rw [hstep_st, hstep_res]; exact ih_vp
        · rw [hstep_st, hstep_res]; exact ih_safe

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
  all_goals obtain ⟨hw1, h1, h2⟩ := h
  · exact Nat.one_lt_two_pow (by omega)
  · exact h1
  · exact h2

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
private def FinishLeafGenPre (w : ℕ)
    (d : ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max sl isR cntL loL hiL mapFn,
    WhpLargeEnv c U V w₀ n_max w d.1.1.1.1.2 ∧
    d.1.1.1.1.1 = mkWhpCoreParams c U V w₀ n_max ∧
    d.1.1.1.2 < 3 * numBucketsWhp n_max ∧
    BTreeSliceMemRep d.1.1.1.1.2 c U V w₀ n_max d.1.1.1.2 sl s.mem ∧
    cntL < 2 * tMinWhp n_max - 1 ∧
    loL ≤ d.1.2 ∧ d.1.2 ≤ hiL ∧ hiL < 2 ^ fpBitsWhp n_max ∧
    d.2 < 2 ^ valLaneBitsWhp n_max ∧
    ValidSubtree isR (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      sl.alloc sl.nodes loL hiL mapFn (.leaf d.1.1.2 cntL)

/-- Parameter-free `finishLeafInsert` (`d = (((((cp, base), sIdx), leafIdx), q), val)`). -/
private def finishLeafInsertGenProg
    (d : ((((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let nd ← readBTreeNodeGenProg (d.1.1.1, d.1.1.2)
  let cnt ← pure (nd.1 / 2)
  let r ← swarRankGenProg (d.1.1.1.1.1, ((cnt, d.1.2), nd.2.1))
  let wKey ← pure (wpWKey d.1.1.1.1.1)
  let hit ← checkLeafHitGenProg (((wKey, nd.2.1), (r, cnt)), d.1.2)
  let z1 ← pure 1
  if hit = z1 then do
    let v' ← wordUpdateAtGenProg (((wpWVal d.1.1.1.1.1, r), d.2), nd.2.2)
    writeNodeOpProg ((d.1.1.1, d.1.1.2), (nd.1, (nd.2.1, v')))
  else do
    let m' ← pure (1 + 2 * (cnt + 1))
    let k' ← wordInsertOpProg (((wKey, r), d.1.2), nd.2.1)
    let v' ← wordInsertOpProg (((wpWVal d.1.1.1.1.1, r), d.2), nd.2.2)
    writeNodeOpProg ((d.1.1.1, d.1.1.2), (m', (k', v')))

private theorem finishLeafInsertGenProg_spec {isR : Bool}
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
  have hr_def : swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) cnt q
      (sl.nodes leafIdx).keysWord = r := rfl
  have hcnt_div : (sl.nodes leafIdx).metaWord / 2 = cnt := rfl
  have hcnt_lt : cnt < 2 * tMinWhp n_max - 1 := by dsimp [cnt]; omega
  have hr_le : r ≤ cnt := by
    dsimp only [r]
    rw [swarRank_eq_count_lt (by omega) hkey_lt (hqhi.trans_lt hhi) hkw_cnt hlanes]
    exact (card_filter_le _ _).trans_eq (card_range _)
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
  by_cases hhit : r < cnt ∧ laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r = q
  · obtain ⟨hrc, hkeq⟩ := hhit
    have hhit_res : (Memory.spec 0).clientResult s hitProg = 1 := by
      dsimp only [hitProg]
      simp only [hrc, ↓reduceIte]
      rw [clientResult_bind, clientState_laneGetGenProg,
        clientResult_laneGetGenProg]
      dsimp only [keyLaneBitsWhp]
      simp [hkeq, StateTransitionSpec.clientResult_pure]
    have hfin_eq : finishLeafInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl leafIdx q val =
        { sl with nodes := (Function.update sl.nodes leafIdx
            ⟨(sl.nodes leafIdx).metaWord, (sl.nodes leafIdx).keysWord,
              wordUpdateAt (valLaneBitsWhp n_max) r val (sl.nodes leafIdx).valsWord⟩) } := by
      unfold finishLeafInsert; simp [cnt, r, hrc, hkeq]
    let nd' : BTreeNode :=
      ⟨(sl.nodes leafIdx).metaWord, (sl.nodes leafIdx).keysWord,
        wordUpdateAt (valLaneBitsWhp n_max) r val (sl.nodes leafIdx).valsWord⟩
    have hv'_lt : nd'.valsWord < 2 ^ valsWordBitsWhp n_max := by
      have hvw0 : (sl.nodes leafIdx).valsWord < 2 ^ (cnt * valLaneBitsWhp n_max) := by
        rw [hcnt_eq_L]; exact hv_leaf.2.2.2.2.1
      unfold valsWordBitsWhp
      exact (wordUpdateAt_lt hrc hval hvw0).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
    obtain ⟨hwn_fr, hwn_mc, hwn_vp, hwn_up, hwn_other, hwn_out⟩ :=
      writeBTreeNodeGenProg_spec (nd := nd') henv hsIdx (hleaf_lt.trans_le hrep.1)
        hm_lt hk_lt hv'_lt (s := s)
    dsimp only at hwn_fr hwn_mc hwn_vp hwn_up hwn_other hwn_out
    set p0 := (mkWhpCoreParams c U V w n_max, base)
    have hs'_wn : (Memory.spec 0).clientState s
        (readBTreeNodeGenProg ((p0, sIdx), leafIdx) >>= fun nd =>
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
            writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
              (1 + 2 * (nd.1 / 2 + 1), (k', v')))) =
        (Memory.spec 0).clientState s
          (writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
            (nd'.metaWord, (nd'.keysWord, nd'.valsWord)))) := by
      rw [clientState_bind, hnd_st, hnd_res,
        clientState_bind, clientState_swarRankGenProg,
        clientResult_swarRankGenProg hth, hcnt_div, hr_def]
      change (Memory.spec 0).clientState s (hitProg >>= _) = _
      rw [clientState_bind, hhit_st, hhit_res]
      simp only [↓reduceIte]
      rw [clientState_bind, clientState_wordUpdateAtGenProg,
        clientResult_wordUpdateAtGenProg]
    rw [hs'_wn]
    refine ⟨hwn_fr, ?_, ?_, ?_, hwn_other, hwn_out⟩
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hnd_st, hnd_mc, hnd_res]
      rw [← PFunctor.FreeM.bind_eq_bind]
      rw [memoryCost_bind, clientState_swarRankGenProg, memoryCost_swarRankGenProg,
        clientResult_swarRankGenProg hth, hcnt_div, hr_def]
      change 6 + (0 + memoryCost (hitProg >>= _) s) = 18
      rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hhit_st, hhit_mc, hhit_res]
      simp only [↓reduceIte]
      rw [memoryCost_bind, clientState_wordUpdateAtGenProg, memoryCost_wordUpdateAtGenProg,
        memoryCost_writeBTreeNodeGenProg]
    · refine validProg_bind hnd_vp ?_
      rw [hnd_st, hnd_res]
      refine validProg_bind (validWhpProg_swarRankGenProg _) ?_
      rw [clientState_swarRankGenProg, clientResult_swarRankGenProg hth, hcnt_div, hr_def]
      change ValidProg w _ s (hitProg >>= _)
      refine validProg_bind hhit_vp ?_
      rw [hhit_st, hhit_res]; simp only [↓reduceIte]
      refine validProg_bind (validWhpProg_wordUpdateAtGenProg _) ?_
      rw [clientState_wordUpdateAtGenProg, clientResult_wordUpdateAtGenProg]
      exact hwn_vp
    · rw [hfin_eq]
      have hbm_eq : ∀ i < 16 * numBucketsWhp n_max,
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w
            ((Memory.spec 0).clientState s
              (writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
                (nd'.metaWord, (nd'.keysWord, nd'.valsWord))))).mem i =
            readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem i :=
        fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ => hwn_out a (Or.inl (by omega))
      exact ⟨hrep.1,
        (hbm_eq _ (by omega)).trans hrep.2.1,
        (hbm_eq _ (by omega)).trans hrep.2.2.1,
        hwn_up sl hrep.1 fun v hv _ => hrep.2.2.2 v hv⟩
  · -- Miss: insert `(q, val)` at lane `r` (`cnt + 1 ≤ 2 * tMin - 1`)
    have hhit_res : (Memory.spec 0).clientResult s hitProg = 0 := by
      dsimp only [hitProg]
      by_cases hrc : r < cnt
      · have hne : laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
          fun heq => hhit ⟨hrc, heq⟩
        simp only [hrc, ↓reduceIte]
        rw [clientResult_bind, clientState_laneGetGenProg,
          clientResult_laneGetGenProg]
        dsimp only [keyLaneBitsWhp]
        simp [hne, StateTransitionSpec.clientResult_pure]
      · simp [hrc, StateTransitionSpec.clientResult_pure]
    have hfin_eq : finishLeafInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl leafIdx q val =
        { sl with nodes := (Function.update sl.nodes leafIdx
            ⟨mkNodeMeta true (cnt + 1),
              wordInsertAt (fpBitsWhp n_max + 2) r q (sl.nodes leafIdx).keysWord,
              wordInsertAt (valLaneBitsWhp n_max) r val (sl.nodes leafIdx).valsWord⟩) } := by
      unfold finishLeafInsert
      by_cases hrc : r < cnt
      · have hne : laneGet (fpBitsWhp n_max + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
          fun heq => hhit ⟨hrc, heq⟩
        simp [cnt, r, hrc, hne]
      · simp [cnt, r, hrc]
    let nd' : BTreeNode :=
      ⟨mkNodeMeta true (cnt + 1),
        wordInsertAt (fpBitsWhp n_max + 2) r q (sl.nodes leafIdx).keysWord,
        wordInsertAt (valLaneBitsWhp n_max) r val (sl.nodes leafIdx).valsWord⟩
    have hm'_lt : nd'.metaWord < 2 ^ nodeMetaBitsWhp n_max := by
      dsimp only [nd', mkNodeMeta]; simp only [↓reduceIte]; omega
    have hq_kl : q < 2 ^ (fpBitsWhp n_max + 2) :=
      (hqhi.trans_lt hhi).trans (Nat.pow_lt_pow_right (by decide) (by omega))
    have hk'_lt : nd'.keysWord < 2 ^ keysWordBitsWhp n_max := by
      dsimp only [nd']
      unfold keysWordBitsWhp keyLaneBitsWhp
      exact (wordInsertAt_lt hr_le hq_kl hkw_cnt).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
    have hv'_lt : nd'.valsWord < 2 ^ valsWordBitsWhp n_max := by
      have hvw0 : (sl.nodes leafIdx).valsWord < 2 ^ (cnt * valLaneBitsWhp n_max) := by
        rw [hcnt_eq_L]; exact hv_leaf.2.2.2.2.1
      dsimp only [nd']
      unfold valsWordBitsWhp
      exact (wordInsertAt_lt hr_le hval hvw0).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
    obtain ⟨hwn_fr, hwn_mc, hwn_vp, hwn_up, hwn_other, hwn_out⟩ :=
      writeBTreeNodeGenProg_spec (nd := nd') henv hsIdx (hleaf_lt.trans_le hrep.1)
        hm'_lt hk'_lt hv'_lt (s := s)
    dsimp only at hwn_fr hwn_mc hwn_vp hwn_up hwn_other hwn_out
    set p0 := (mkWhpCoreParams c U V w n_max, base)
    have hs'_wn : (Memory.spec 0).clientState s
        (readBTreeNodeGenProg ((p0, sIdx), leafIdx) >>= fun nd =>
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
            writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
              (1 + 2 * (nd.1 / 2 + 1), (k', v')))) =
        (Memory.spec 0).clientState s
          (writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
            (nd'.metaWord, (nd'.keysWord, nd'.valsWord)))) := by
      rw [clientState_bind, hnd_st, hnd_res,
        clientState_bind, clientState_swarRankGenProg,
        clientResult_swarRankGenProg hth, hcnt_div, hr_def]
      change (Memory.spec 0).clientState s (hitProg >>= _) = _
      rw [clientState_bind, hhit_st, hhit_res]
      simp only [zero_ne_one, ↓reduceIte]
      rw [clientState_bind, clientState_wordInsertAtGenProg,
        clientResult_wordInsertAtGenProg,
        clientState_bind, clientState_wordInsertAtGenProg,
        clientResult_wordInsertAtGenProg]
      dsimp only [nd', mkNodeMeta, keyLaneBitsWhp]
      rfl
    rw [hs'_wn]
    refine ⟨hwn_fr, ?_, ?_, ?_, hwn_other, hwn_out⟩
    · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hnd_st, hnd_mc, hnd_res]
      rw [← PFunctor.FreeM.bind_eq_bind]
      rw [memoryCost_bind, clientState_swarRankGenProg, memoryCost_swarRankGenProg,
        clientResult_swarRankGenProg hth, hcnt_div, hr_def]
      change 6 + (0 + memoryCost (hitProg >>= _) s) = 18
      rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hhit_st, hhit_mc, hhit_res]
      simp only [zero_ne_one, ↓reduceIte]
      rw [memoryCost_bind, clientState_wordInsertAtGenProg, memoryCost_wordInsertAtGenProg]
      rw [memoryCost_bind, clientState_wordInsertAtGenProg, memoryCost_wordInsertAtGenProg,
        memoryCost_writeBTreeNodeGenProg]
    · refine validProg_bind hnd_vp ?_
      rw [hnd_st, hnd_res]
      refine validProg_bind (validWhpProg_swarRankGenProg _) ?_
      rw [clientState_swarRankGenProg, clientResult_swarRankGenProg hth, hcnt_div, hr_def]
      change ValidProg w _ s (hitProg >>= _)
      refine validProg_bind hhit_vp ?_
      rw [hhit_st, hhit_res]; simp only [zero_ne_one, ↓reduceIte]
      refine validProg_bind (validWhpProg_wordInsertAtGenProg _) ?_
      rw [clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg]
      refine validProg_bind (validWhpProg_wordInsertAtGenProg _) ?_
      rw [clientState_wordInsertAtGenProg, clientResult_wordInsertAtGenProg]
      exact hwn_vp
    · rw [hfin_eq]
      have hbm_eq : ∀ i < 16 * numBucketsWhp n_max,
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w
            ((Memory.spec 0).clientState s
              (writeBTreeNodeGenProg (((p0, sIdx), leafIdx),
                (nd'.metaWord, (nd'.keysWord, nd'.valsWord))))).mem i =
            readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem i :=
        fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ => hwn_out a (Or.inl (by omega))
      exact ⟨hrep.1,
        (hbm_eq _ (by omega)).trans hrep.2.1,
        (hbm_eq _ (by omega)).trans hrep.2.2.1,
        hwn_up sl hrep.1 fun v hv _ => hrep.2.2.2 v hv⟩

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

private theorem realizes_finishLeafInsertGen :
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
    simp only [wp_large_M hth] at *
    try simp only [wp_large_nSlice hth] at *
    try simp only [wp_large_wKey hth] at *
    try simp only [wp_large_wVal hth] at *
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
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    simp only [hnd_st, hnd_res, hcnt_div, clientResult_swarRankGenProg hth] at *
    try exact hleaf_lt.trans_le hrep.1
  · refine ⟨⟨base, c, U, V, w, n_max, henv, rfl⟩, ?_, ?_, ?_, ?_⟩
    · simp only [wp_large_capLanes hth]; omega
    · simp only [wp_large_powFp hth]; exact hqhi.trans_lt hhi
    · simp only [wp_large_wKey hth, ← hcnt_eq_L]; exact hkw_cnt
    · simp only [wp_large_wKey hth, wp_large_powFp hth, ← hcnt_eq_L]; exact hlanes
  · have hkl2 : 2 ≤ keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp fpBitsWhp; omega
    have h2 : 2 ≤ 2 * tMinWhp n_max * keyLaneBitsWhp n_max :=
      le_trans hkl2 (Nat.le_mul_of_pos_left _ (by omega))
    omega
  · exact (Nat.le_mul_of_pos_left _ (by omega)).trans_lt hkw_lt
  · have hr_le := swarRank_le_cntL hth hcntL (hqhi.trans_lt hhi)
      (hcnt_eq_L ▸ hkw_cnt) (hcnt_eq_L ▸ hlanes)
    exact ((Nat.mul_le_mul_right _ (hr_le.trans (by omega))).trans_lt hkw_lt).trans
      Nat.lt_two_pow_self
  · have hrc := checkLeafHit_eq_one_imp_lt _ _ hc
    refine ⟨cntL, by unfold valLaneBitsWhp; positivity, hrc,
      (Nat.mul_le_mul_right _ (by omega)).trans_lt hvw_lt, hval, hv_leaf.2.2.2.2.1⟩
  · have hkl2 : 2 ≤ keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp fpBitsWhp; omega
    have : 1 + 2 * (cntL + 1) < w := by
      have : 2 * (2 * tMinWhp n_max) ≤ 2 * tMinWhp n_max * keyLaneBitsWhp n_max := by
        rw [Nat.mul_comm 2 (2 * tMinWhp n_max)]; exact Nat.mul_le_mul_left _ hkl2
      omega
    exact this.trans Nat.lt_two_pow_self
  · have : cntL + 1 < w :=
      (by omega : cntL + 1 ≤ 2 * tMinWhp n_max).trans_lt
        ((Nat.le_mul_of_pos_right _ (by unfold keyLaneBitsWhp; positivity)).trans_lt hkw_lt)
    exact this.trans Nat.lt_two_pow_self
  · have hr_le := swarRank_le_cntL hth hcntL (hqhi.trans_lt hhi)
      (hcnt_eq_L ▸ hkw_cnt) (hcnt_eq_L ▸ hlanes)
    refine ⟨cntL, hr_le, (Nat.mul_le_mul_right _ (by omega)).trans_lt hkw_lt, ?_, ?_⟩
    · exact (hqhi.trans_lt hhi).trans
        (Nat.pow_lt_pow_right (by decide) (by unfold keyLaneBitsWhp; omega))
    · rwa [← hcnt_eq_L]
  · have hr_le := swarRank_le_cntL hth hcntL (hqhi.trans_lt hhi)
      (hcnt_eq_L ▸ hkw_cnt) (hcnt_eq_L ▸ hlanes)
    refine ⟨cntL, hr_le, (Nat.mul_le_mul_right _ (by omega)).trans_lt hvw_lt, hval,
      hv_leaf.2.2.2.2.1⟩

/-- Parameter-free `btreeInsert` (`d = ((((cp, base), sIdx), q), val)`), factored cleanly into
`ensureAndSplitRootGenProg`, `descendSplitLoopGenProg`, and `finishLeafInsertGenProg`. -/
@[irreducible] def btreeInsertGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), sIdx), q), val) => do
    let ar1 ← ensureAndSplitRootGenProg ((cp, base), sIdx)
    let ar2 ← descendSplitLoopGenProg (((((cp, base), sIdx), q), ar1), wpHMaxBTree cp)
    finishLeafInsertGenProg (((((cp, base), sIdx), ar2.2), q), val)

theorem btreeInsertGenProg_spec {c U V w n_max base sIdx insCount q val : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) (hval : val < 2 ^ valLaneBitsWhp n_max) :
    let prog := btreeInsertGenProg ((((mkWhpCoreParams c U V w n_max, base), sIdx), q), val)
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q val
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 2426 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx sl' s'.mem ∧
    ValidWhpSlice n_max (insCount + 1) sl' (Function.update mapFn q (some val)) ∧
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
  have hv_ins := (hv.insert_spec hth hins hq hval).2
  obtain ⟨hfr1, hres1, hmc1, hvp1, hrep1, halloc1, ⟨T1, hrt1, hht1, hnf1, hv1⟩,
    hoth1, hbm1, hout1⟩ := ensureAndSplitRootGenProg_spec henv hsIdx hins hrep hv (s := s)
  set s1 := (Memory.spec 0).clientState s
    (ensureAndSplitRootGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx))
  have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
    Nat.sub_lt (Nat.two_pow_pos _) one_pos
  obtain ⟨hfr2, hres2, hmc2, hvp2, _, hrep2, ⟨isR, cntL, loL, hiL, hcntL, hqlo, hqhi, hhiL, hvlf⟩,
    hoth2, hbm2, hout2⟩ :=
    descendSplitLoopGenProg_spec henv hsIdx hrep1 halloc1.le hrt1 hnf1 hht1
      (Nat.zero_le q) (by omega) hhi hv1 (s := s1) (fuel := hMaxBTree)
  set sl1 := splitRootIfFull (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
    (ensureRootSlice sl)
  set d0 := (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
  set s2 := (Memory.spec 0).clientState s1
    (descendSplitLoopGenProg ((d0, (sl1.alloc, sl1.root)), hMaxBTree))
  set p := descendSplitToLeaf (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
    hMaxBTree sl1 sl1.root q
  obtain ⟨hfr3, hmc3, hvp3, hrep3, hoth3, hout3⟩ :=
    finishLeafInsertGenProg_spec henv hsIdx hrep2 hcntL hqlo hqhi hhiL hval hvlf (s := s2)
  have hoff := largeOffsetChain c U V w n_max
  unfold btreeInsertGenProg
  dsimp only [d0]
  simp only [wp_large_hMaxBTree hth]
  have hs'_eq : (Memory.spec 0).clientState s
      (ensureAndSplitRootGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx) >>= fun ar1 =>
        descendSplitLoopGenProg ((d0, ar1), hMaxBTree) >>= fun ar2 =>
        finishLeafInsertGenProg (((d0.1, ar2.2), q), val)) =
      (Memory.spec 0).clientState s2
        (finishLeafInsertGenProg (((d0.1, p.2), q), val)) := by
    dsimp only [d0]
    rw [clientState_bind, hres1,
      clientState_bind, hres2]
  simp only [d0] at hs'_eq ⊢
  rw [hs'_eq]
  refine ⟨hfr3.trans (hfr2.trans hfr1), ?_, ?_, hrep3, hv_ins, ?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s1, s2, d0] at hmc1 hmc2 hmc3 hres1 hres2 ⊢
    rw [hres1, hres2, hmc3]
    rw [hMaxBTree_eq] at hmc2 ⊢
    omega
  · refine validProg_bind hvp1 ?_
    rw [hres1]
    refine validProg_bind hvp2 ?_
    rw [hres2]
    exact hvp3
  · intro sIdx' hsIdx' hne sl₂ hr₂
    exact hoth3 sIdx' hsIdx' hne sl₂ (hoth2 sIdx' hsIdx' hne sl₂ (hoth1 sIdx' hsIdx' hne sl₂ hr₂))
  · intro idx hidx h1 h2
    have hbm3 : readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w
        ((Memory.spec 0).clientState s2
          (finishLeafInsertGenProg (((d0.1, p.2), q), val))).mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s2.mem idx :=
      readPacked_congr hw (hidx := hidx) fun a ⟨_, ha2⟩ => hout3 a (Or.inl (by omega))
    exact hbm3.trans ((hbm2 idx hidx h1).trans (hbm1 idx hidx h1 h2))
  · intro a ha
    have ha3 : a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a := by
      rcases ha with ha1 | ⟨_, ha2⟩ | ha3'
      · exact Or.inl (by omega)
      · exact Or.inl ha2
      · exact Or.inr ha3'
    exact (hout3 a ha3).trans ((hout2 a ha).trans (hout1 a ha))

theorem realizes_btreeInsertGen :
    Realizes .exact btreeInsertGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      BTreeModGenPre
      (fun _ _ => 0) := by
  unfold btreeInsertGenProg
  have her := realizes_ensureAndSplitRootGen
  have hdsl := realizes_descendSplitLoopGen
  have hfl := realizes_finishLeafInsertGen
  realize
  all_goals
    rcases d with ⟨⟨⟨⟨cp, base⟩, sIdx⟩, q⟩, val⟩
    dsimp only [BTreeModGenPre] at h
    obtain ⟨c, U, V, w₀, n_max, insCount, sl, mapFn,
      henv, rfl, hsIdx, hins, hrep, hv, hq, hval⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    obtain ⟨_, hres1, _, _, hrep1, halloc1, ⟨T1, hrt1, hht1, hnf1, hv1⟩, _, _, _⟩ :=
      ensureAndSplitRootGenProg_spec henv hsIdx hins hrep hv (s := s)
    have hhi : 2 ^ fpBitsWhp n_max - 1 < 2 ^ fpBitsWhp n_max :=
      Nat.sub_lt (Nat.two_pow_pos _) one_pos
    simp only [hres1, wp_large_hMaxBTree hth] at *
  · exact ⟨c, U, V, w, n_max, insCount, sl, mapFn, henv, rfl, hsIdx, hins, hrep, hv⟩
  · exact (descendSplitLoopGenProg_spec henv hsIdx hrep1 halloc1.le hrt1 hnf1 hht1
      (Nat.zero_le q) (by omega) hhi hv1
      (s := (Memory.spec 0).clientState s
        (ensureAndSplitRootGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx)))
      (fuel := hMaxBTree)).2.2.2.2.1
  · obtain ⟨_, hres2, _, _, _, hrep2, ⟨isR, cntL, loL, hiL, hcntL, hqlo, hqhi, hhiL, hvlf⟩,
      _, _, _⟩ :=
      descendSplitLoopGenProg_spec henv hsIdx hrep1 halloc1.le hrt1 hnf1 hht1
        (Nat.zero_le q) (by omega) hhi hv1
        (s := (Memory.spec 0).clientState s
          (ensureAndSplitRootGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx)))
        (fuel := hMaxBTree)
    rw [hres2]
    exact ⟨c, U, V, w, n_max, _, isR, cntL, loL, hiL, mapFn,
      henv, rfl, hsIdx, hrep2, hcntL, hqlo, hqhi, hhiL, hval, hvlf⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
