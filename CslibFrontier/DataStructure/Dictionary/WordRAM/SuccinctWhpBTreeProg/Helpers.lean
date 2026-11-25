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
# Internal SWAR B+-Tree Slice Parameter Bounds and Header Write Frame Laws

Internal `ValidProg` wrappers, bit-width bounds (`btree_slice_param_bounds`,
`validSubtree_root_bounds`, `descendToLeaf_leaf`), and `BTreeSliceMemRep` frame lemmas for slice
header updates (`writeSliceHeaderGenProg`, `writeSliceAllocGenProg_sliceRep`).
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

theorem validWhpProg_laneGetGenProg {w F : ℕ} {s : Memory.State}
    (d : (ℕ × ℕ) × ℕ) : ValidProg w F s (laneGetGenProg d) := by
  unfold laneGetGenProg; simp only [pure_bind]; exact validProg_pure _

theorem validWhpProg_wordInsertAtGenProg {w F : ℕ} {s : Memory.State}
    (d : ((ℕ × ℕ) × ℕ) × ℕ) : ValidProg w F s (wordInsertAtGenProg d) := by
  unfold wordInsertAtGenProg; simp only [pure_bind]; exact validProg_pure _

theorem validWhpProg_wordDeleteAtGenProg {w F : ℕ} {s : Memory.State}
    (d : (ℕ × ℕ) × ℕ) : ValidProg w F s (wordDeleteAtGenProg d) := by
  unfold wordDeleteAtGenProg; simp only [pure_bind]; exact validProg_pure _

theorem validWhpProg_wordUpdateAtGenProg {w F : ℕ} {s : Memory.State}
    (d : ((ℕ × ℕ) × ℕ) × ℕ) : ValidProg w F s (wordUpdateAtGenProg d) := by
  unfold wordUpdateAtGenProg; simp only [pure_bind]; exact validProg_pure _

theorem validWhpProg_swarRankGenProg {w F : ℕ} {s : Memory.State}
    (d : WhpCoreParams × ((ℕ × ℕ) × ℕ)) : ValidProg w F s (swarRankGenProg d) := by
  unfold swarRankGenProg; simp only [pure_bind]; exact validProg_pure _

theorem btree_slice_param_bounds {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
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

theorem validWhpProg_splitFullNodeGenProg {w F : ℕ} {s : Memory.State}
    (d : WhpCoreParams × (ℕ × (ℕ × ℕ))) : ValidProg w F s (splitFullNodeGenProg d) := by
  unfold splitFullNodeGenProg
  simp only [pure_bind]
  refine validProg_bind (validWhpProg_laneGetGenProg _) ?_
  rw [clientState_laneGetGenProg]
  split_ifs <;>
    (unfold wordTakeLowGenProg wordDropLowGenProg
     simp only [pure_bind]
     exact validProg_pure _)

theorem descendToLeaf_leaf {isRoot : Bool}
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
theorem validSubtree_root_bounds {isRoot : Bool} {c n_max alloc lo hi : ℕ}
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
def writeSliceHeaderGenProg :
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

theorem realizes_writeSliceHeaderGen :
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
theorem writeSliceHeaderGenProg_sliceRep {c U V w n_max base sIdx newA newR : ℕ}
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
theorem writeSliceAllocGenProg_sliceRep {c U V w n_max base sIdx newA root0 : ℕ}
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

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
