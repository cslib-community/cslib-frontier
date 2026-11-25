/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpSwarBTree
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity

/-!
# Subtree Correctness and Node-Splitting Lemmas for the SWAR B+-Tree

This module proves sorted SWAR rank routing (`swarRank_sorted_spec`, `branch_child_routing`),
subtree lookup, deletion, and in-place value update (`btreeLookup_eq_of_subtree`,
`btreeDelete_subtree_spec`, `btreeUpdate_subtree_spec`), unified proactive full-node splitting
(`splitFullNode_spec`, `splitRootIfFull_spec`), and leaf insertion (`finishLeafInsert_leaf_spec`)
for the top-down split-only SWAR B+-tree defined in
`CslibFrontier.DataStructure.Dictionary.SuccinctWhpSwarBTree`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.btreeLookup_eq_of_subtree`:
  exact lookup agreement `btreeLookup ... sl q = mapFn q`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.btreeDelete_subtree_spec`,
  `Cslib.DataStructure.Dictionary.SuccinctWhp.btreeUpdate_subtree_spec`:
  preservation of `ValidSubtree` and non-increasing `potential` under deletion and update.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.splitFullNode_spec`,
  `Cslib.DataStructure.Dictionary.SuccinctWhp.splitRootIfFull_spec`:
  proactive node splitting with excess-key split-potential drop.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.finishLeafInsert_leaf_spec`:
  exact map refinement and count bound for leaf insertion/overwrite.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Section 4][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Finset
open scoped BigOperators

/-! ## Section 1: Sorted SWAR rank characterization, descent, lookup, delete, and update -/

/-- A strictly increasing lane array is weakly increasing. -/
private theorem lanes_le {f : ℕ → ℕ} {cnt : ℕ} (hmono : ∀ i j, i < j → j < cnt → f i < f j) :
    ∀ i j, i ≤ j → j < cnt → f i ≤ f j :=
  fun i j hij hj => hij.eq_or_lt.elim (· ▸ le_rfl) fun h => (hmono i j h hj).le

/-- Partition property of `swarRank` on a strictly increasing lane array:
`r ≤ cnt`, lanes `< r` are `< q`, and lanes `r .. cnt - 1` are `≥ q`. -/
theorem swarRank_sorted_spec {fpBits capLanes cnt q keysWord : ℕ}
    (hcnt : cnt < capLanes) (hcap : capLanes < 2 ^ (fpBits + 2))
    (hq : q < 2 ^ fpBits) (hkw : keysWord < 2 ^ (cnt * (fpBits + 2)))
    (hlanes : ∀ j < cnt, laneGet (fpBits + 2) keysWord j < 2 ^ fpBits)
    (hmono : ∀ i j, i < j → j < cnt →
      laneGet (fpBits + 2) keysWord i < laneGet (fpBits + 2) keysWord j) :
    let r := swarRank fpBits capLanes cnt q keysWord
    r ≤ cnt ∧
      (∀ j < r, laneGet (fpBits + 2) keysWord j < q) ∧
      (∀ j, r ≤ j → j < cnt → q ≤ laneGet (fpBits + 2) keysWord j) := by
  rw [swarRank_eq_count_lt hcnt hcap hq hkw hlanes]
  refine ⟨(card_filter_le _ _).trans_eq (card_range cnt), fun j hj => ?_, fun j hrj hjc => ?_⟩
  · by_contra hnq
    refine hj.not_ge ((card_le_card fun k hk => ?_).trans_eq (card_range j))
    simp only [mem_filter, mem_range] at hk ⊢
    by_contra hjk
    have := lanes_le hmono _ _ (Nat.le_of_not_lt hjk) hk.1
    omega
  · by_contra hlt_q
    refine (Nat.lt_succ_of_le hrj).not_ge
      ((card_range (j + 1)).symm.trans_le (card_le_card fun k hk => ?_))
    simp only [mem_filter, mem_range] at hk ⊢
    have := lanes_le hmono _ _ (Nat.le_of_lt_succ hk) hjc
    omega

/-- Internal branch routing: `swarRank` selects the unique child interval `[childLo r, childHi r]`
containing `q`, and every other child interval is disjoint from `{q}`. -/
theorem branch_child_routing {isRoot : Bool} {fpBits W_val tMin alloc idx cnt lo hi q : ℕ}
    {nodes : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ} {cs : Fin (cnt + 1) → BTreeTree}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn (.branch idx cnt cs))
    (hhi : hi < 2 ^ fpBits) (hqlo : lo ≤ q) (hqhi : q ≤ hi) :
    let W_key := fpBits + 2
    let nd := nodes idx
    let r := swarRank fpBits (2 * tMin) cnt q nd.keysWord
    r ≤ cnt ∧
      childLo W_key lo nd.keysWord r ≤ q ∧
      q ≤ childHi W_key hi cnt nd.keysWord r ∧
      (∀ i : Fin (cnt + 1), i.val ≠ r →
        ∀ q', childLo W_key lo nd.keysWord i.val ≤ q' →
          q' ≤ childHi W_key hi cnt nd.keysWord i.val → q' ≠ q) := by
  obtain ⟨_, _, hdeg, hcnt_le, hkw, _, hlo0, hhi_last, hmono, _, _, _, _⟩ := hv
  have hcnt1 : 1 ≤ cnt := by cases isRoot <;> simp at hdeg <;> omega
  have hle := lanes_le hmono
  obtain ⟨hr_le, hlt_r, hge_r⟩ := swarRank_sorted_spec (capLanes := 2 * tMin)
    (by omega) hcap (hqhi.trans_lt hhi) hkw
    (fun j hj => (hle _ _ (Nat.le_sub_one_of_lt hj) (by omega)).trans_lt (hhi_last.trans hhi)) hmono
  refine ⟨hr_le, ?_, ?_, fun i hne q' hq'_lo hq'_hi heq => ?_⟩
  · unfold childLo
    split_ifs
    exacts [hqlo, hlt_r _ (by omega)]
  · unfold childHi
    split_ifs with hrc
    exacts [hge_r _ le_rfl hrc, hqhi]
  · subst heq
    have h1 := hlt_r i.val
    have h2 := hge_r _ le_rfl
    have h3 := hle (swarRank fpBits (2 * tMin) cnt q' (nodes idx).keysWord) (i.val - 1)
    simp only [childLo, childHi] at hq'_lo hq'_hi
    split_ifs at hq'_lo hq'_hi <;> omega

/-- Generic root-to-leaf structural lemma for `descendToLeaf`: reaches the unique leaf covering `q`,
and any valid in-place replacement of that leaf lifts back to the whole subtree `T` with identical
`rootIdx`, `nodeSet`, `height`, and bounded `potential`. -/
private theorem descendToLeaf_reaches_leaf {isRoot : Bool}
    {fpBits W_val tMin alloc lo hi q fuel : ℕ}
    {nodes : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T)
    (hhi : hi < 2 ^ fpBits) (hqlo : lo ≤ q) (hqhi : q ≤ hi) (hfuel : T.height ≤ fuel) :
    ∃ cnt loL hiL,
      let leafIdx := descendToLeaf fpBits W_val tMin nodes fuel T.rootIdx q
      leafIdx ∈ T.nodeSet ∧
      lo ≤ loL ∧ loL ≤ q ∧ q ≤ hiL ∧ hiL ≤ hi ∧
      ValidSubtree false fpBits W_val tMin alloc nodes loL hiL mapFn (.leaf leafIdx cnt) ∧
      ∀ (cnt' : ℕ) (nd' : BTreeNode) (mapFn' : ℕ → Option ℕ),
        cnt' ≤ cnt →
        (∀ q', q' ≠ q → mapFn' q' = mapFn q') →
        ValidSubtree false fpBits W_val tMin alloc (Function.update nodes leafIdx nd')
          loL hiL mapFn' (.leaf leafIdx cnt') →
        ∃ T' : BTreeTree,
          T'.rootIdx = T.rootIdx ∧
          T'.nodeSet = T.nodeSet ∧
          T'.height = T.height ∧
          T'.potential tMin ≤ T.potential tMin ∧
          ValidSubtree isRoot fpBits W_val tMin alloc (Function.update nodes leafIdx nd')
            lo hi mapFn' T' := by
  induction T generalizing isRoot lo hi fuel with
  | leaf idx cnt =>
    have hdesc : descendToLeaf fpBits W_val tMin nodes fuel idx q = idx := by
      cases fuel <;> simp [descendToLeaf, hv.2.1]
    refine ⟨cnt, lo, hi, ?_⟩
    simp only [BTreeTree.rootIdx, hdesc]
    exact ⟨by simp [BTreeTree.nodeSet], le_rfl, hqlo, hqhi, le_rfl, hv,
      fun cnt' nd' mapFn' hcnt_le _ hv_new =>
        ⟨.leaf idx cnt', rfl, rfl, rfl, Nat.sub_le_sub_right hcnt_le _, hv_new⟩⟩
  | branch idx cnt cs ih =>
    obtain ⟨hr_le, hclo_q, hq_chi, hother⟩ := branch_child_routing ht2 hcap hv hhi hqlo hqhi
    obtain ⟨hidx, hmeta, hdeg, hcnt_le, hkw, hvw, hlo0, hhi_last, hmono,
      hnot, hdisj, hht, hcs⟩ := hv
    rw [BTreeTree.height_branch_of_eq hht] at hfuel
    obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    let r : Fin (cnt + 1) :=
      ⟨swarRank fpBits (2 * tMin) cnt q (nodes idx).keysWord, Nat.lt_succ_of_le hr_le⟩
    have hdesc : descendToLeaf fpBits W_val tMin nodes (fuel' + 1) idx q =
        descendToLeaf fpBits W_val tMin nodes fuel' (cs r).rootIdx q := by
      simp [descendToLeaf, hmeta, ← (hcs r).1, r]
    have hchi_le := childHi_le (r := r) hhi_last.le hmono
    obtain ⟨cntL, loL, hiL, hmem_c, hloL1, hloL_q, hq_hiL, hhiL1, hv_leaf, hlift_c⟩ :=
      ih (fuel := fuel') r (hcs r).2 (hchi_le.trans_lt hhi) hclo_q hq_chi (by rw [hht r]; omega)
    refine ⟨cntL, loL, hiL, ?_⟩
    rw [BTreeTree.rootIdx, hdesc]
    refine ⟨mem_insert_of_mem (mem_biUnion.mpr ⟨r, mem_univ r, hmem_c⟩),
      (le_childLo hr_le hlo0 hmono).trans hloL1, hloL_q, hq_hiL, hhiL1.trans hchi_le, hv_leaf,
      fun cnt' nd' mapFn' hcnt_le' hmap_other hv_new => ?_⟩
    obtain ⟨T', hroot', hset', hht', hpot', hv'⟩ :=
      hlift_c cnt' nd' mapFn' hcnt_le' hmap_other hv_new
    have hset_eq : ∀ i, (Function.update cs r T' i).nodeSet = (cs i).nodeSet :=
      (Function.forall_update_iff cs fun i t => t.nodeSet = (cs i).nodeSet).2
        ⟨hset', fun _ _ => rfl⟩
    have hht_eq : ∀ i, (Function.update cs r T' i).height = (cs i).height :=
      (Function.forall_update_iff cs fun i t => t.height = (cs i).height).2
        ⟨hht', fun _ _ => rfl⟩
    have hnodes_idx : Function.update nodes _ nd' idx = nodes idx :=
      Function.update_of_ne (ne_of_mem_of_not_mem hmem_c (hnot r)).symm nd' nodes
    refine ⟨.branch idx cnt (Function.update cs r T'), rfl, ?_, ?_,
      Nat.add_le_add_left (sum_le_sum fun i _ => ?_) _, ?_⟩
    · simp only [BTreeTree.nodeSet, hset_eq]
    · simp only [BTreeTree.height, hht_eq]
    · exact (Function.forall_update_iff cs fun i t =>
        t.potential tMin ≤ (cs i).potential tMin).2 ⟨hpot', fun _ _ => le_rfl⟩ i
    · simp only [ValidSubtree, hnodes_idx, hset_eq, hht_eq]
      refine ⟨hidx, hmeta, hdeg, hcnt_le, hkw, hvw, hlo0, hhi_last, hmono, hnot, hdisj, hht,
        fun i => ?_⟩
      rcases eq_or_ne i r with rfl | hi
      · rw [Function.update_self]
        exact ⟨hroot' ▸ (hcs _).1, hv'⟩
      · rw [Function.update_of_ne hi]
        exact ⟨(hcs i).1, (hcs i).2.frame le_rfl
          (fun v hv_in => Function.update_of_ne
            (disjoint_iff_ne.mp (hdisj i r hi) v hv_in _ hmem_c) nd' nodes)
          fun q' hq1 hq2 => hmap_other q' (hother i (Fin.val_ne_of_ne hi) q' hq1 hq2)⟩

/-- Rank of a covered key `q` in a valid leaf: `swarRank` returns the partition point `r` of the
sorted keys, and either lane `r` holds `q` with `mapFn q` its value lane, or no lane holds `q` and
`mapFn q = none`. -/
private theorem ValidSubtree.leaf_rank {isRoot : Bool} {fpBits W_val tMin alloc idx cnt lo hi q : ℕ}
    {nodes : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ}
    (ht1 : 1 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn (.leaf idx cnt))
    (hhi : hi < 2 ^ fpBits) (hqlo : lo ≤ q) (hqhi : q ≤ hi) :
    let keys := laneGet (fpBits + 2) (nodes idx).keysWord
    let r := swarRank fpBits (2 * tMin) cnt q (nodes idx).keysWord
    r ≤ cnt ∧ (∀ j < r, keys j < q) ∧ (∀ j, r ≤ j → j < cnt → q ≤ keys j) ∧
      ((r < cnt ∧ keys r = q ∧ mapFn q = some (laneGet W_val (nodes idx).valsWord r)) ∨
        ((∀ j < cnt, keys j ≠ q) ∧ mapFn q = none)) := by
  obtain ⟨_, _, hcnt_le, hkw, _, hbounds, hmono, href⟩ := hv
  obtain ⟨hr_le, hlt_r, hge_r⟩ := swarRank_sorted_spec (capLanes := 2 * tMin) (by omega) hcap
    (hqhi.trans_lt hhi) hkw (fun j hj => (hbounds j hj).2.trans_lt hhi) hmono
  refine ⟨hr_le, hlt_r, hge_r, (href q hqlo hqhi).imp_left ?_⟩
  rintro ⟨r₀, hr₀, hkey, hmap⟩
  obtain rfl : r₀ = swarRank fpBits (2 * tMin) cnt q (nodes idx).keysWord := by
    have h1 := hge_r _ le_rfl
    have h2 := hmono (swarRank fpBits (2 * tMin) cnt q (nodes idx).keysWord) r₀
    have h3 := hlt_r r₀
    omega
  exact ⟨hr₀, hkey, hmap⟩

/-- Exact lookup specification on any valid subtree `T` with `T.height ≤ hMaxBTree`. -/
theorem btreeLookup_eq_of_subtree {fpBits W_val tMin : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} {T : BTreeTree} {q : ℕ}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (halloc_pos : 1 ≤ sl.alloc) (hroot : T.rootIdx = sl.root)
    (hv : ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T)
    (hfuel : T.height ≤ hMaxBTree) (hq : q < 2 ^ fpBits) :
    btreeLookup fpBits W_val tMin sl q = mapFn q := by
  have hhi : 2 ^ fpBits - 1 < 2 ^ fpBits := Nat.sub_one_lt (Nat.two_pow_pos fpBits).ne'
  obtain ⟨cntL, loL, hiL, _, _, hloL_q, hq_hiL, hhiL_le, hv_leaf, _⟩ :=
    descendToLeaf_reaches_leaf ht2 hcap hv hhi (Nat.zero_le q) (by omega) hfuel
  rw [hroot] at hv_leaf
  rw [btreeLookup, ite_eq_right (by omega)]
  obtain ⟨-, -, -, ⟨hrc, hkey, hmap⟩ | ⟨hno, hmap⟩⟩ :=
    hv_leaf.leaf_rank (by omega) hcap (hhiL_le.trans_lt hhi) hloL_q hq_hiL
  · simp [hv_leaf.2.1, hrc, hkey, hmap]
  · simpa [hv_leaf.2.1, hmap] using hno _

/-- Shared root-to-leaf point-modification template for `btreeDelete_subtree_spec` and
`btreeUpdate_subtree_spec`: descend to the leaf covering `q` and, when its rank lane holds `q`,
replace the leaf node by `mk nd r`. The caller supplies leaf validity of the replaced node. -/
private theorem btreeModifyLeaf_subtree_spec {fpBits W_val tMin : ℕ} {sl : BTreeSlice}
    {mapFn mapFn' : ℕ → Option ℕ} {T : BTreeTree} {q : ℕ} {mk : BTreeNode → ℕ → BTreeNode}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2)) (hroot : T.rootIdx = sl.root)
    (hv : ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T)
    (hfuel : T.height ≤ hMaxBTree) (hq : q < 2 ^ fpBits)
    (hmiss : mapFn q = none → mapFn' = mapFn) (hother : ∀ q', q' ≠ q → mapFn' q' = mapFn q')
    (hhit : ∀ {leafIdx cnt lo hi : ℕ},
      ValidSubtree false fpBits W_val tMin sl.alloc sl.nodes lo hi mapFn (.leaf leafIdx cnt) →
      swarRank fpBits (2 * tMin) cnt q (sl.nodes leafIdx).keysWord < cnt →
      laneGet (fpBits + 2) (sl.nodes leafIdx).keysWord
        (swarRank fpBits (2 * tMin) cnt q (sl.nodes leafIdx).keysWord) = q →
      (mapFn q).isSome →
      ∃ cnt' ≤ cnt, ValidSubtree false fpBits W_val tMin sl.alloc
        (Function.update sl.nodes leafIdx (mk (sl.nodes leafIdx)
          (swarRank fpBits (2 * tMin) cnt q (sl.nodes leafIdx).keysWord)))
        lo hi mapFn' (.leaf leafIdx cnt')) :
    let leafIdx := descendToLeaf fpBits W_val tMin sl.nodes hMaxBTree sl.root q
    let nd := sl.nodes leafIdx
    let r := swarRank fpBits (2 * tMin) (metaCount nd.metaWord) q nd.keysWord
    let sl' := if r < metaCount nd.metaWord && laneGet (fpBits + 2) nd.keysWord r == q then
      { sl with nodes := Function.update sl.nodes leafIdx (mk nd r) } else sl
    sl'.alloc = sl.alloc ∧
      ∃ T' : BTreeTree,
        T'.rootIdx = sl'.root ∧
        T'.height = T.height ∧
        T'.potential tMin ≤ T.potential tMin ∧
        ValidSubtree true fpBits W_val tMin sl'.alloc sl'.nodes 0 (2 ^ fpBits - 1) mapFn' T' := by
  have hhi : 2 ^ fpBits - 1 < 2 ^ fpBits := Nat.sub_one_lt (Nat.two_pow_pos fpBits).ne'
  obtain ⟨cntL, loL, hiL, _, _, hloL_q, hq_hiL, hhiL_le, hv_leaf, hlift⟩ :=
    descendToLeaf_reaches_leaf ht2 hcap hv hhi (Nat.zero_le q) (by omega) hfuel
  rw [hroot] at hv_leaf hlift
  simp only [hv_leaf.2.1, metaCount_mkNodeMeta]
  obtain ⟨-, -, -, ⟨hrc, hkey, hmap⟩ | ⟨hno, hmap⟩⟩ :=
    hv_leaf.leaf_rank (by omega) hcap (hhiL_le.trans_lt hhi) hloL_q hq_hiL
  · obtain ⟨cnt', hcnt', hv_new⟩ := hhit hv_leaf hrc hkey (by simp [hmap])
    obtain ⟨T', hrt', -, hht', hpot', hv'⟩ := hlift cnt' _ mapFn' hcnt' hother hv_new
    rw [ite_eq_left (by simp [hrc, hkey])]
    exact ⟨rfl, T', hrt', hht', hpot', hv'⟩
  · rw [ite_eq_right (by simpa using hno _), hmiss hmap]
    exact ⟨rfl, T, hroot, rfl, le_rfl, hv⟩

/-- Subtree deletion specification: `btreeDelete` preserves `ValidSubtree`, keeps `alloc` and
`height` unchanged, does not increase `potential`, and updates `mapFn` to
`Function.update mapFn q none`. -/
theorem btreeDelete_subtree_spec {fpBits W_val tMin : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} {T : BTreeTree} {q : ℕ}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (halloc_pos : 1 ≤ sl.alloc) (hroot : T.rootIdx = sl.root)
    (hv : ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T)
    (hfuel : T.height ≤ hMaxBTree) (hq : q < 2 ^ fpBits) :
    let sl' := btreeDelete fpBits W_val tMin sl q
    sl'.alloc = sl.alloc ∧
      ∃ T' : BTreeTree,
        T'.rootIdx = sl'.root ∧
        T'.height = T.height ∧
        T'.potential tMin ≤ T.potential tMin ∧
        ValidSubtree true fpBits W_val tMin sl'.alloc sl'.nodes 0 (2 ^ fpBits - 1)
          (Function.update mapFn q none) T' := by
  rw [btreeDelete, ite_eq_right (by omega)]
  refine btreeModifyLeaf_subtree_spec
    (mk := fun nd r => ⟨mkNodeMeta true (metaCount nd.metaWord - 1),
      wordDeleteAt (fpBits + 2) r nd.keysWord, wordDeleteAt W_val r nd.valsWord⟩)
    ht2 hcap hroot hv hfuel hq
    (fun h => h ▸ Function.update_eq_self q mapFn) (fun q' hne => Function.update_of_ne hne _ _)
    fun {leafIdx cnt lo hi} hv_leaf hrc hkey _ => ⟨cnt - 1, Nat.sub_le _ _, ?_⟩
  obtain ⟨hidx_lt, hmeta, hcnt_le, hkw, hvw, hbounds, hmono, href⟩ := hv_leaf
  generalize swarRank fpBits (2 * tMin) cnt q (sl.nodes leafIdx).keysWord = r at *
  have hcnt_eq : cnt - 1 + 1 = cnt := by omega
  simp only [ValidSubtree, Function.update_self, hmeta, metaCount_mkNodeMeta, laneGet_wordDeleteAt]
  refine ⟨hidx_lt, trivial, by omega, wordDeleteAt_lt (by omega) (by rwa [hcnt_eq]),
    wordDeleteAt_lt (by omega) (by rwa [hcnt_eq]), fun j hj => ?_, fun i j hij hjc => ?_,
    fun q' hq1 hq2 => ?_⟩
  · split_ifs
    exacts [hbounds j (by omega), hbounds (j + 1) (by omega)]
  · have h1 := hmono i j
    have h2 := hmono i (j + 1)
    have h3 := hmono (i + 1) (j + 1)
    split_ifs <;> omega
  · rcases eq_or_ne q' q with rfl | hqq
    · refine .inr ⟨fun j hj => ?_, Function.update_self ..⟩
      have h1 := hmono j r
      have h2 := hmono r (j + 1)
      split_ifs <;> omega
    · rw [Function.update_of_ne hqq]
      rcases href q' hq1 hq2 with ⟨j₀, hj₀, hkj₀, hmj₀⟩ | ⟨hno, hmno⟩
      · have hne : j₀ ≠ r := fun h => hqq (by rw [← hkj₀, h, hkey])
        rcases lt_or_gt_of_ne hne with h | h
        · exact .inl ⟨j₀, by omega, by simp [h, hkj₀], by simp [h, hmj₀]⟩
        · have h1 : ¬j₀ - 1 < r := by omega
          have h2 : j₀ - 1 + 1 = j₀ := by omega
          exact .inl ⟨j₀ - 1, by omega, by simp [h1, h2, hkj₀], by simp [h1, h2, hmj₀]⟩
      · exact .inr ⟨fun j hj => by split_ifs <;> exact hno _ (by omega), hmno⟩

/-- Overwriting value lane `r < cnt` of a valid leaf with `val` keeps it valid for the map updated
at the key in lane `r`. -/
private theorem ValidSubtree.leaf_updateVal {isRoot : Bool}
    {fpBits W_val tMin alloc idx cnt lo hi r val : ℕ} {nodes : ℕ → BTreeNode}
    {mapFn : ℕ → Option ℕ}
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn (.leaf idx cnt))
    (hval : val < 2 ^ W_val) (hrc : r < cnt) :
    ValidSubtree isRoot fpBits W_val tMin alloc
      (Function.update nodes idx
        ⟨(nodes idx).metaWord, (nodes idx).keysWord, wordUpdateAt W_val r val (nodes idx).valsWord⟩)
      lo hi (Function.update mapFn (laneGet (fpBits + 2) (nodes idx).keysWord r) (some val))
      (.leaf idx cnt) := by
  obtain ⟨hidx_lt, hmeta, hcnt_le, hkw, hvw, hbounds, hmono, href⟩ := hv
  simp only [ValidSubtree, Function.update_self, laneGet_wordUpdateAt hval]
  refine ⟨hidx_lt, hmeta, hcnt_le, hkw, wordUpdateAt_lt hrc hval hvw, hbounds, hmono,
    fun q' hq1 hq2 => ?_⟩
  rcases eq_or_ne q' (laneGet (fpBits + 2) (nodes idx).keysWord r) with rfl | hqq
  · exact .inl ⟨r, hrc, rfl, by simp⟩
  · rw [Function.update_of_ne hqq]
    refine (href q' hq1 hq2).imp_left fun ⟨j₀, hj₀, hkj₀, hmj₀⟩ => ⟨j₀, hj₀, hkj₀, ?_⟩
    rw [ite_eq_right (by rintro rfl; exact hqq hkj₀.symm), hmj₀]

/-- Subtree in-place value update specification: when `newVal < 2 ^ W_val`, `btreeUpdate` preserves
`ValidSubtree`, `alloc`, `height`, and `potential`, updating `mapFn q` to `some newVal` whenever `q`
is present (and leaving `mapFn` unchanged when `mapFn q = none`). -/
theorem btreeUpdate_subtree_spec {fpBits W_val tMin : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} {T : BTreeTree} {q newVal : ℕ}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (halloc_pos : 1 ≤ sl.alloc) (hroot : T.rootIdx = sl.root)
    (hv : ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T)
    (hfuel : T.height ≤ hMaxBTree) (hq : q < 2 ^ fpBits) (hval : newVal < 2 ^ W_val) :
    let sl' := btreeUpdate fpBits W_val tMin sl q newVal
    let mapFn' := if (mapFn q).isSome then Function.update mapFn q (some newVal) else mapFn
    sl'.alloc = sl.alloc ∧
      ∃ T' : BTreeTree,
        T'.rootIdx = sl'.root ∧
        T'.height = T.height ∧
        T'.potential tMin ≤ T.potential tMin ∧
        ValidSubtree true fpBits W_val tMin sl'.alloc sl'.nodes 0 (2 ^ fpBits - 1) mapFn' T' := by
  rw [btreeUpdate, ite_eq_right (by omega)]
  refine btreeModifyLeaf_subtree_spec
    (mk := fun nd r => ⟨nd.metaWord, nd.keysWord, wordUpdateAt W_val r newVal nd.valsWord⟩)
    ht2 hcap hroot hv hfuel hq (fun h => by simp [h])
    (fun q' hne => by split_ifs <;> simp [Function.update_of_ne hne])
    fun hv_leaf hrc hkey hsome => ⟨_, le_rfl, ?_⟩
  simpa only [hkey, hsome, ↓reduceIte] using hv_leaf.leaf_updateVal hval hrc

/-! ## Section 2: Proactive node splitting (`splitFullNode`, `splitRootIfFull`) -/

/-- The nodes of a child of a valid branch lie in the branch's node set minus its root. -/
private theorem mem_nodeSet_erase_of_child {idx cnt v : ℕ} {cs : Fin (cnt + 1) → BTreeTree}
    (hnot : ∀ i, idx ∉ (cs i).nodeSet) (k : Fin (cnt + 1)) (hv : v ∈ (cs k).nodeSet) :
    v ∈ (BTreeTree.branch idx cnt cs).nodeSet.erase idx :=
  mem_erase.mpr ⟨ne_of_mem_of_not_mem hv (hnot k),
    mem_insert_of_mem (mem_biUnion.mpr ⟨k, mem_univ k, hv⟩)⟩

/-- Left endpoint of child `i` of a window starting at child `a`. -/
private theorem childLo_window {W lo K K' a i m : ℕ}
    (hkeys : ∀ j < m, laneGet W K' j = laneGet W K (a + j)) (him : i ≤ m) :
    childLo W (childLo W lo K a) K' i = childLo W lo K (a + i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [childLo]
  · simp [childLo, hi.ne', hkeys (i - 1) (by omega), show a + (i - 1) = a + i - 1 by omega]

/-- Right endpoint of child `i` of a window of `m + 1` children starting at child `a`. -/
private theorem childHi_window {W hi cnt K K' a i m : ℕ}
    (hkeys : ∀ j < m, laneGet W K' j = laneGet W K (a + j)) (him : i ≤ m) (ham : a + m ≤ cnt) :
    childHi W (childHi W hi cnt K (a + m)) m K' i = childHi W hi cnt K (a + i) := by
  rcases eq_or_lt_of_le him with rfl | hi
  · simp [childHi]
  · simp [childHi, hi, show a + i < cnt by omega, hkeys i hi]

/-- A window of `m + 1` consecutive children `a, …, a + m` of a valid branch, together with a node
`nodes' idx'` holding the `m` separators between them and their `m + 1` child indices, is a valid
non-root branch on the union `[childLo a, childHi (a + m)]` of their intervals. Both halves of a
split branch are such windows. -/
private theorem ValidSubtree.branch_window {isRoot : Bool}
    {fpBits W_val tMin alloc alloc' idx idx' cnt lo hi lo' hi' a m K V : ℕ}
    {nodes nodes' : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ} {cs : Fin (cnt + 1) → BTreeTree}
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn (.branch idx cnt cs))
    (ham : a + m ≤ cnt) (hm : tMin - 1 ≤ m) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 * tMin - 1)
    (halloc : alloc ≤ alloc') (hidx' : idx' < alloc')
    (hnd : nodes' idx' = ⟨mkNodeMeta false m, K, V⟩)
    (hK : K < 2 ^ (m * (fpBits + 2))) (hV : V < 2 ^ ((m + 1) * W_val))
    (hkeys : ∀ j < m, laneGet (fpBits + 2) K j = laneGet (fpBits + 2) (nodes idx).keysWord (a + j))
    (hvals : ∀ j ≤ m, laneGet W_val V j = laneGet W_val (nodes idx).valsWord (a + j))
    (hlo' : lo' = childLo (fpBits + 2) lo (nodes idx).keysWord a)
    (hhi' : hi' = childHi (fpBits + 2) hi cnt (nodes idx).keysWord (a + m))
    (hframe : ∀ v ∈ (BTreeTree.branch idx cnt cs).nodeSet.erase idx,
      nodes' v = nodes v ∧ v ≠ idx') :
    let T' := BTreeTree.branch idx' m fun i : Fin (m + 1) => cs ⟨a + i.val, by omega⟩
    T'.height = (BTreeTree.branch idx cnt cs).height ∧
      T'.nodeSet ⊆ insert idx' ((BTreeTree.branch idx cnt cs).nodeSet.erase idx) ∧
      ValidSubtree false fpBits W_val tMin alloc' nodes' lo' hi' mapFn T' := by
  obtain ⟨_, _, _, _, _, _, hlo0, hhi_last, hmono, hnot, hdisj, hht, hcs⟩ := hv
  subst hlo' hhi'
  have hht' : ∀ i : Fin (m + 1), (cs ⟨a + i.val, by omega⟩).height =
      (cs ⟨a + (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)).val, by omega⟩).height :=
    fun i => (hht _).trans (hht _).symm
  have hch := fun k v => mem_nodeSet_erase_of_child (v := v) hnot k
  refine ⟨?_, fun v hv_in => ?_, ?_⟩
  · rw [BTreeTree.height_branch_of_eq hht', BTreeTree.height_branch_of_eq hht]
    exact congrArg _ (hht _)
  · rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hv_in
    rcases hv_in with rfl | ⟨i, _, hvi⟩
    exacts [mem_insert_self _ _, mem_insert_of_mem (hch _ v hvi)]
  · simp only [ValidSubtree, hnd]
    refine ⟨hidx', trivial, by simpa using hm, hm2, hK, hV, ?_, ?_, fun i j hij hj => ?_,
      fun i hmem => (hframe _ (hch _ _ hmem)).2 rfl,
      fun i j hij => hdisj _ _ (Fin.ne_of_val_ne (by simpa [Fin.ext_iff] using hij)),
      hht', fun i => ?_⟩
    · rw [hkeys 0 hm1, childLo]
      split_ifs with h
      · rwa [h]
      · exact hmono (a - 1) a (by omega) (by omega)
    · rw [hkeys (m - 1) (by omega), childHi]
      split_ifs with h
      · exact hmono _ _ (by omega) h
      · rwa [show a + (m - 1) = cnt - 1 by omega]
    · rw [hkeys i (hij.trans hj), hkeys j hj]
      exact hmono _ _ (by omega) (by omega)
    · rw [hvals i (by omega), childLo_window hkeys (by omega), childHi_window hkeys (by omega) ham]
      have hc := hcs ⟨a + i.val, by omega⟩
      exact ⟨hc.1, hc.2.frame halloc (fun v hv_in => (hframe v (hch _ v hv_in)).1) fun _ _ _ => rfl⟩

/-- Unified specification of `splitFullNode` on any full (`2 * tMin - 1`-key) valid subtree `T`
(leaf or internal branch), covering both `splitRootIfFull` (`leftIdx = alloc`,
`rightIdx = alloc + 1`) and `descendSplitToLeaf` (`leftIdx = T.rootIdx`, `rightIdx = alloc`). -/
theorem splitFullNode_spec {isRoot : Bool} {fpBits W_val tMin alloc alloc' lo hi : ℕ}
    {leftIdx rightIdx : ℕ} {nodes nodes' : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ}
    {T : BTreeTree}
    (ht2 : 2 ≤ tMin)
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T)
    (hfull : metaCount (nodes T.rootIdx).metaWord = 2 * tMin - 1)
    (halloc : alloc ≤ alloc')
    (hl_lt : leftIdx < alloc') (hr_lt : rightIdx < alloc') (hlr_ne : leftIdx ≠ rightIdx)
    (hl_nd : nodes' leftIdx = (splitFullNode fpBits W_val tMin (nodes T.rootIdx)).left)
    (hr_nd : nodes' rightIdx = (splitFullNode fpBits W_val tMin (nodes T.rootIdx)).right)
    (herase : ∀ v ∈ T.nodeSet.erase T.rootIdx,
      nodes' v = nodes v ∧ v ≠ leftIdx ∧ v ≠ rightIdx) :
    let res := splitFullNode fpBits W_val tMin (nodes T.rootIdx)
    let sep := res.sep
    ∃ leftT rightT : BTreeTree,
      leftT.rootIdx = leftIdx ∧
      rightT.rootIdx = rightIdx ∧
      metaCount (nodes' leftIdx).metaWord ≤ tMin ∧
      metaCount (nodes' rightIdx).metaWord = tMin - 1 ∧
      leftT.height = T.height ∧
      rightT.height = T.height ∧
      leftT.nodeSet ⊆ insert leftIdx (T.nodeSet.erase T.rootIdx) ∧
      rightT.nodeSet ⊆ insert rightIdx (T.nodeSet.erase T.rootIdx) ∧
      Disjoint leftT.nodeSet rightT.nodeSet ∧
      lo ≤ sep ∧ sep < hi ∧
      leftT.potential tMin + rightT.potential tMin + (tMin - 1) ≤ T.potential tMin ∧
      ValidSubtree false fpBits W_val tMin alloc' nodes' lo sep mapFn leftT ∧
      ValidSubtree false fpBits W_val tMin alloc' nodes' (sep + 1) hi mapFn rightT := by
  cases T with
  | leaf idx cnt =>
    obtain ⟨_, hmeta, _, hkw, hvw, hbounds, hmono, href⟩ := hv
    simp only [BTreeTree.rootIdx, splitFullNode, hmeta, metaIsLeaf_mkNodeMeta,
      metaCount_mkNodeMeta, ↓reduceIte] at hfull hl_nd hr_nd ⊢
    subst hfull
    have hle := lanes_le hmono
    have hlo_sep := (hbounds (tMin - 1) (by omega)).1
    have hsep_hi := (hmono (tMin - 1) (2 * tMin - 2) (by omega) (by omega)).trans_le
      (hbounds (2 * tMin - 2) (by omega)).2
    have hcnt_sum : tMin + (tMin - 1) = 2 * tMin - 1 := by omega
    refine ⟨.leaf leftIdx tMin, .leaf rightIdx (tMin - 1), rfl, rfl, by simp [hl_nd],
      by simp [hr_nd], rfl, rfl, by simp [BTreeTree.nodeSet], by simp [BTreeTree.nodeSet],
      by simp [BTreeTree.nodeSet, hlr_ne], hlo_sep, hsep_hi,
      by simp only [BTreeTree.potential]; omega, ?_, ?_⟩
    · simp only [ValidSubtree, hl_nd, laneGet_wordTakeLow]
      refine ⟨hl_lt, trivial, by omega, wordTakeLow_lt .., wordTakeLow_lt .., fun j hj => ?_,
        fun i j hij hj => ?_, fun q hq1 hq2 => ?_⟩
      · rw [ite_eq_left hj]
        exact ⟨(hbounds j (by omega)).1, hle _ _ (by omega) (by omega)⟩
      · rw [ite_eq_left (hij.trans hj), ite_eq_left hj]
        exact hmono i j hij (by omega)
      · rcases href q hq1 (hq2.trans hsep_hi.le) with ⟨r₀, hr₀, hkr₀, hmr₀⟩ | ⟨hno, hmno⟩
        · have hr₀_lt : r₀ < tMin := by
            have := hmono (tMin - 1) r₀
            omega
          exact .inl ⟨r₀, hr₀_lt, by rw [ite_eq_left hr₀_lt, hkr₀],
            by rw [ite_eq_left hr₀_lt, hmr₀]⟩
        · exact .inr ⟨fun r hr => by rw [ite_eq_left hr]; exact hno r (by omega), hmno⟩
    · simp only [ValidSubtree, hr_nd, laneGet_wordDropLow]
      refine ⟨hr_lt, trivial, by omega, wordDropLow_lt (by rwa [hcnt_sum]),
        wordDropLow_lt (by rwa [hcnt_sum]), fun j hj => ?_,
        fun i j hij hj => hmono _ _ (by omega) (by omega), fun q hq1 hq2 => ?_⟩
      · exact ⟨hmono (tMin - 1) (tMin + j) (by omega) (by omega), (hbounds _ (by omega)).2⟩
      · rcases href q (by omega) hq2 with ⟨r₀, hr₀, hkr₀, hmr₀⟩ | ⟨hno, hmno⟩
        · have := hle r₀ (tMin - 1)
          exact .inl ⟨r₀ - tMin, by omega, by rw [Nat.add_sub_cancel' (by omega), hkr₀],
            by rw [Nat.add_sub_cancel' (by omega), hmr₀]⟩
        · exact .inr ⟨fun r hr => hno _ (by omega), hmno⟩
  | branch idx cnt cs =>
    have hv' := hv
    obtain ⟨_, hmeta, _, _, hkw, hvw, hlo0, hhi_last, hmono, hnot, hdisj, _, _⟩ := hv
    simp only [BTreeTree.rootIdx, splitFullNode, hmeta, metaIsLeaf_mkNodeMeta,
      metaCount_mkNodeMeta, Bool.false_eq_true, ↓reduceIte] at hfull hl_nd hr_nd herase ⊢
    obtain ⟨hhtL, hsubL, hvL⟩ := hv'.branch_window (a := 0) (m := tMin - 1) (lo' := lo)
      (hi' := laneGet (fpBits + 2) (nodes idx).keysWord (tMin - 1)) (by omega) le_rfl (by omega)
      (by omega) halloc hl_lt hl_nd (wordTakeLow_lt ..)
      (by simpa [show tMin - 1 + 1 = tMin by omega] using wordTakeLow_lt W_val tMin _)
      (fun j hj => by simp [laneGet_wordTakeLow, hj])
      (fun j hj => by simp [laneGet_wordTakeLow, show j < tMin by omega])
      (by simp [childLo]) (by simp [childHi, show tMin - 1 < cnt by omega])
      fun v hv => ⟨(herase v hv).1, (herase v hv).2.1⟩
    obtain ⟨hhtR, hsubR, hvR⟩ := hv'.branch_window (a := tMin) (m := tMin - 1)
      (lo' := laneGet (fpBits + 2) (nodes idx).keysWord (tMin - 1) + 1) (hi' := hi) (by omega)
      le_rfl (by omega) (by omega) halloc hr_lt hr_nd
      (wordDropLow_lt (by rwa [show tMin + (tMin - 1) = cnt by omega]))
      (wordDropLow_lt (by rwa [show tMin + (tMin - 1 + 1) = cnt + 1 by omega]))
      (fun j _ => laneGet_wordDropLow ..) (fun j _ => laneGet_wordDropLow ..)
      (by simp [childLo, show tMin ≠ 0 by omega])
      (by simp [childHi, show ¬tMin + (tMin - 1) < cnt by omega])
      fun v hv => ⟨(herase v hv).1, (herase v hv).2.2⟩
    refine ⟨_, _, by rfl, by rfl, by simp [hl_nd], by simp [hr_nd], hhtL, hhtR, hsubL,
      hsubR, ?_, hlo0.trans (lanes_le hmono _ _ (Nat.zero_le _) (by omega)),
      (hmono (tMin - 1) (cnt - 1) (by omega) (by omega)).trans hhi_last, ?_, hvL, hvR⟩
    · rw [disjoint_left]
      intro v hL hR
      rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hL hR
      rcases hL with rfl | ⟨i, _, hvi⟩ <;> rcases hR with heq | ⟨j, _, hvj⟩
      · exact hlr_ne heq
      · exact (herase _ (mem_nodeSet_erase_of_child hnot _ hvj)).2.1 rfl
      · exact (herase _ (mem_nodeSet_erase_of_child hnot _ hvi)).2.2 heq
      · exact disjoint_left.mp (hdisj _ _ (Fin.ne_of_val_ne (by dsimp; omega))) hvi hvj
    · simp only [BTreeTree.potential]
      have hsum : ∑ i : Fin (tMin - 1 + 1), (cs ⟨0 + i.val, by omega⟩).potential tMin +
          ∑ i : Fin (tMin - 1 + 1), (cs ⟨tMin + i.val, by omega⟩).potential tMin =
          ∑ k : Fin (cnt + 1), (cs k).potential tMin := by
        rw [← Equiv.sum_comp (finCongr (show tMin - 1 + 1 + (tMin - 1 + 1) = cnt + 1 by omega))
          fun k => (cs k).potential tMin, Fin.sum_univ_add (a := tMin - 1 + 1)]
        congr 1 <;> refine sum_congr rfl fun i _ => congrArg (fun k => (cs k).potential tMin) ?_
        · ext; dsimp; omega
        · ext; dsimp; omega
      omega

/-- Specification of `splitRootIfFull`: ensures the root is strictly non-full (`< 2 * tMin - 1`
keys), increases height by at most `1`, allocates at most `2` nodes, and never increases the
excess-key split potential `(tMin - 2) * (alloc - 1) + 2 * T.potential tMin` when `3 ≤ tMin`. -/
theorem splitRootIfFull_spec {fpBits W_val tMin : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (ht3 : 3 ≤ tMin) (halloc_pos : 1 ≤ sl.alloc) (halloc_val : sl.alloc + 1 < 2 ^ W_val)
    (hroot : T.rootIdx = sl.root)
    (hv : ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T) :
    let sl1 := splitRootIfFull fpBits W_val tMin sl
    1 ≤ sl1.alloc ∧ sl1.alloc ≤ sl.alloc + 2 ∧ sl1.root = sl.root ∧
      ∃ T1 : BTreeTree,
        T1.rootIdx = sl1.root ∧
        metaCount (sl1.nodes sl1.root).metaWord < 2 * tMin - 1 ∧
        T1.height ≤ T.height + 1 ∧
        (tMin - 2) * (sl1.alloc - 1) + 2 * T1.potential tMin ≤
          (tMin - 2) * (sl.alloc - 1) + 2 * T.potential tMin ∧
        ValidSubtree true fpBits W_val tMin sl1.alloc sl1.nodes 0 (2 ^ fpBits - 1) mapFn T1 := by
  have hlt := hv.leafCount_le_card_nodeSet.1
  have hroot_lt : sl.root < sl.alloc := hroot ▸ hlt T.rootIdx T.rootIdx_mem_nodeSet
  have hcnt_le : metaCount (sl.nodes sl.root).metaWord ≤ 2 * tMin - 1 := by
    rw [← hroot]
    cases T <;> rw [BTreeTree.rootIdx, hv.2.1, metaCount_mkNodeMeta]
    exacts [hv.2.2.1, hv.2.2.2.1]
  by_cases hfull : metaCount (sl.nodes sl.root).metaWord = 2 * tMin - 1
  · simp only [splitRootIfFull, hfull, beq_self_eq_true, ↓reduceIte]
    generalize hnodes' : Function.update _ sl.root _ = nodes'
    obtain ⟨leftT, rightT, hrtL, hrtR, -, -, hhtL, hhtR, hsubL, hsubR, hdisjLR, -, hsep_hi,
      hpotLR, hvL, hvR⟩ := splitFullNode_spec (alloc' := sl.alloc + 2) (nodes' := nodes')
        (leftIdx := sl.alloc) (rightIdx := sl.alloc + 1) (by omega) hv (by rwa [hroot])
        (by omega) (by omega) (by omega) (by omega)
        (by simp [← hnodes', hroot, hroot_lt.ne'])
        (by simp [← hnodes', hroot, show sl.alloc + 1 ≠ sl.root by omega])
        fun v hv_er => by
          have := hlt v (mem_of_mem_erase hv_er)
          have hne : v ≠ sl.root := hroot ▸ ne_of_mem_erase hv_er
          simp [← hnodes', hne, show v ≠ sl.alloc by omega, show v ≠ sl.alloc + 1 by omega]
    subst hnodes'
    rw [hroot] at hsep_hi hvL hvR hsubL hsubR
    have hht_root : ∀ i : Fin 2, (![leftT, rightT] i).height =
        (![leftT, rightT] ⟨0, by decide⟩).height := Fin.forall_fin_two.2 ⟨rfl, hhtR.trans hhtL.symm⟩
    refine ⟨by omega, le_rfl, trivial, .branch sl.root 1 ![leftT, rightT], rfl,
      by simp; omega, ?_, ?_, ?_⟩
    · rw [BTreeTree.height_branch_of_eq hht_root]
      exact (Nat.add_comm _ _).trans_le (Nat.add_le_add_right hhtL.le 1)
    · have hsum : ∑ i : Fin (1 + 1), (![leftT, rightT] i).potential tMin =
          leftT.potential tMin + rightT.potential tMin := Fin.sum_univ_two _
      rw [show sl.alloc + 2 - 1 = sl.alloc - 1 + 2 by omega, Nat.mul_add, BTreeTree.potential, hsum]
      omega
    · have hsep_lt : (splitFullNode fpBits W_val tMin (sl.nodes sl.root)).sep < 2 ^ (fpBits + 2) :=
        hsep_hi.trans ((Nat.sub_le _ _).trans_lt (Nat.pow_lt_pow_right (by decide) (by omega)))
      have hlane0 := laneGet_eq_div_mod (fpBits + 2)
        (splitFullNode fpBits W_val tMin (sl.nodes sl.root)).sep 0
      simp only [Nat.zero_mul, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hsep_lt] at hlane0
      have hl : sl.alloc < 2 ^ W_val := by omega
      have hval0 : laneGet W_val (sl.alloc + (sl.alloc + 1) <<< W_val) 0 = sl.alloc := by
        simp [laneGet_eq_div_mod, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hl]
      have hval1 : laneGet W_val (sl.alloc + (sl.alloc + 1) <<< W_val) 1 = sl.alloc + 1 := by
        simp [laneGet_eq_div_mod, Nat.shiftLeft_eq, Nat.add_mul_div_right, Nat.div_eq_of_lt hl,
          Nat.mod_eq_of_lt halloc_val]
      have hvals_lt : sl.alloc + (sl.alloc + 1) <<< W_val < 2 ^ ((1 + 1) * W_val) := by
        have := Nat.mul_le_mul_right (2 ^ W_val) (show sl.alloc + 2 ≤ 2 ^ W_val by omega)
        rw [Nat.shiftLeft_eq, show (1 + 1) * W_val = W_val + W_val by omega, Nat.pow_add]
        rw [show sl.alloc + 2 = (sl.alloc + 1) + 1 by omega, Nat.add_mul, Nat.one_mul] at this
        omega
      simp only [ValidSubtree, Function.update_self, ↓reduceIte, le_refl, Nat.one_mul,
        Nat.sub_self, hlane0]
      refine ⟨by omega, trivial, trivial, by omega, hsep_lt, hvals_lt, Nat.zero_le _, hsep_hi,
        fun i j hij hj => by omega, Fin.forall_fin_two.2 ⟨fun h => ?_, fun h => ?_⟩, ?_, hht_root,
        Fin.forall_fin_two.2 ⟨⟨hval0.trans hrtL.symm, ?_⟩, ⟨hval1.trans hrtR.symm, ?_⟩⟩⟩
      · simpa [hroot_lt.ne] using hsubL h
      · simpa [show sl.root ≠ sl.alloc + 1 by omega] using hsubR h
      · simp [Fin.forall_fin_two, hdisjLR, hdisjLR.symm]
      · simpa [childLo, childHi, hlane0] using hvL
      · simpa [childLo, childHi, hlane0] using hvR
  · simp only [splitRootIfFull, beq_iff_eq, hfull, ↓reduceIte]
    exact ⟨halloc_pos, by omega, trivial, T, hroot, by omega, by omega, le_rfl, hv⟩

/-- Exact specification of `finishLeafInsert` on a non-full (`cnt < 2 * tMin - 1`) valid leaf. -/
theorem finishLeafInsert_leaf_spec {isRoot : Bool} {fpBits W_val tMin leafIdx cnt lo hi q val : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ}
    (ht2 : 2 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2)) (hval : val < 2 ^ W_val)
    (hhi : hi < 2 ^ fpBits) (hqlo : lo ≤ q) (hqhi : q ≤ hi)
    (hv : ValidSubtree isRoot fpBits W_val tMin sl.alloc sl.nodes lo hi mapFn (.leaf leafIdx cnt))
    (hnonfull : cnt < 2 * tMin - 1) :
    let sl' := finishLeafInsert fpBits W_val tMin sl leafIdx q val
    sl'.alloc = sl.alloc ∧
      sl'.root = sl.root ∧
      (∀ v, v ≠ leafIdx → sl'.nodes v = sl.nodes v) ∧
      ∃ cnt' : ℕ,
        cnt' ≤ cnt + 1 ∧
        ValidSubtree isRoot fpBits W_val tMin sl'.alloc sl'.nodes lo hi
          (Function.update mapFn q (some val)) (.leaf leafIdx cnt') := by
  obtain ⟨hr_le, hlt_r, hge_r, hrank⟩ := hv.leaf_rank (by omega) hcap hhi hqlo hqhi
  have hv' := hv
  obtain ⟨hidx_lt, hmeta, _, hkw, hvw, hbounds, hmono, href⟩ := hv
  have hcnt : metaCount (sl.nodes leafIdx).metaWord = cnt := by rw [hmeta, metaCount_mkNodeMeta]
  simp only [finishLeafInsert, hcnt]
  generalize swarRank fpBits (2 * tMin) cnt q (sl.nodes leafIdx).keysWord = r at *
  rcases hrank with ⟨hrc, hkey, -⟩ | ⟨hno, -⟩
  · rw [ite_eq_left (by simp [hrc, hkey])]
    exact ⟨rfl, rfl, fun v hv_ne => Function.update_of_ne hv_ne _ _, cnt, Nat.le_succ cnt,
      hkey ▸ hv'.leaf_updateVal hval hrc⟩
  · have hq_lt : q < 2 ^ (fpBits + 2) :=
      (hqhi.trans_lt hhi).trans (Nat.pow_lt_pow_right (by decide) (by omega))
    have hgt_r := fun j hrj hjc => lt_of_le_of_ne (hge_r j hrj hjc) (hno j hjc).symm
    rw [ite_eq_right (by simpa using hno r)]
    refine ⟨rfl, rfl, fun v hv_ne => Function.update_of_ne hv_ne _ _, cnt + 1, le_rfl, ?_⟩
    simp only [ValidSubtree, Function.update_self, laneGet_wordInsertAt hq_lt,
      laneGet_wordInsertAt hval]
    refine ⟨hidx_lt, trivial, by omega, wordInsertAt_lt hr_le hq_lt hkw,
      wordInsertAt_lt hr_le hval hvw, fun j hj => ?_, fun i j hij hj => ?_, fun q' hq1 hq2 => ?_⟩
    · split_ifs
      exacts [hbounds j (by omega), ⟨hqlo, hqhi⟩, hbounds (j - 1) (by omega)]
    · have h1 := hmono i j
      have h2 := hmono (i - 1) (j - 1)
      have h3 := hlt_r i
      have h4 := hgt_r (j - 1)
      split_ifs <;> omega
    · rcases eq_or_ne q' q with rfl | hqq
      · exact .inl ⟨r, by omega, by simp, by simp⟩
      · rw [Function.update_of_ne hqq]
        rcases href q' hq1 hq2 with ⟨j₀, hj₀, hkj₀, hmj₀⟩ | ⟨hno', hmno⟩
        · rcases lt_or_ge j₀ r with h | h
          · exact .inl ⟨j₀, by omega, by simp [h, hkj₀], by simp [h, hmj₀]⟩
          · have h1 : ¬j₀ + 1 < r := by omega
            have h2 : j₀ + 1 ≠ r := by omega
            exact .inl ⟨j₀ + 1, by omega, by simp [h1, h2, hkj₀], by simp [h1, h2, hmj₀]⟩
        · refine .inr ⟨fun j hj => ?_, hmno⟩
          split_ifs
          exacts [hno' j (by omega), hqq.symm, hno' (j - 1) (by omega)]

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
