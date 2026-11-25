/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpParams
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpSwarBTreeSpec
import CslibFrontier.Foundations.Data.Finset.ApplyUpdate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Top-Down Split-Only SWAR B+-Tree Insertion and `ValidWhpSlice` Bundle

This module completes the functional correctness and excess-key split-potential proof for
`descendSplitToLeaf` and `btreeInsert` and packages the slice-level `ValidWhpSlice` invariant
specialized to `SuccinctWhp` parameters.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice`:
  slice-level ordered-map and excess-key split-potential invariant specialized to
  `(fpBitsWhp n_max, valLaneBitsWhp n_max, tMinWhp n_max)`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.btreeInsert_subtree_spec`:
  top-level subtree specification of `btreeInsert`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidSubtree.node_bits_lt`:
  packed single-word bit-width bounds on `metaWord`, `keysWord`, and `valsWord` for every node of a
  valid subtree.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.validWhpSlice_zero`,
  `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice.lookup_eq`,
  `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice.delete_spec`,
  `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice.update_spec`,
  `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice.insert_spec`:
  exact ordered-map refinement and preservation of `ValidWhpSlice` across initialization and all
  four operations.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidWhpSlice.alloc_and_height_lt`:
  every `ValidWhpSlice` with `insCount ≤ 8 * (slabScale n_max) ^ 12` at `whpThreshold c ≤ n_max`
  satisfies `sl.alloc + hMaxBTree + 4 < nSliceWhp n_max` and unpacks (when `1 ≤ sl.alloc`) to a
  `ValidSubtree` witness of height `< hMaxBTree` whose nodes satisfy packed single-word bit-width
  bounds.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Section 4][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

/-! ## Section 1: Inductive correctness and potential bound for `descendSplitToLeaf` -/

/-- Replacing child `r` of `cs` with `T'` shifts the total child potential by `T'.potential` minus
`(cs r).potential`. -/
private theorem sum_potential_update_add {n : ℕ} (cs : Fin n → BTreeTree) (r : Fin n)
    (T' : BTreeTree) (tMin : ℕ) :
    ∑ i, (Function.update cs r T' i).potential tMin + (cs r).potential tMin =
      ∑ i, (cs i).potential tMin + T'.potential tMin := by
  rw [Finset.sum_apply_update_of_mem (mem_univ r) (fun _ T => T.potential tMin) cs T',
    ← Finset.add_sum_erase univ (fun i => (cs i).potential tMin) (mem_univ r)]
  omega

/-- The root node of a valid subtree holds at most `2 * tMin - 1` keys. -/
private theorem ValidSubtree.metaCount_rootIdx_le {isRoot : Bool} {fpBits W_val tMin alloc : ℕ}
    {nodes : ℕ → BTreeNode} {lo hi : ℕ} {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T) :
    metaCount (nodes T.rootIdx).metaWord ≤ 2 * tMin - 1 := by
  cases T <;> rw [BTreeTree.rootIdx, hv.2.1, metaCount_mkNodeMeta]
  exacts [hv.2.2.1, hv.2.2.2.1]

/-! ### Lanes and child intervals after `wordInsertAt`

Splitting child `r` of a branch inserts the promoted separator at key lane `r` and the new right
child at value lane `r + 1`. The right half then sits at position `r.succ` and the old child `k`
(the left half when `k = r`) at position `r.succ.succAbove k`. -/

/-- Value lane of old child `k` after inserting a child index at lane `r + 1`. -/
private theorem laneGet_wordInsertAt_succAbove {W v word n : ℕ} (hv : v < 2 ^ W)
    (r k : Fin (n + 1)) :
    laneGet W (wordInsertAt W (r + 1) v word) (r.succ.succAbove k) = laneGet W word k := by
  grind [Fin.succAbove, laneGet_wordInsertAt]

/-- Left endpoint of old child `k` after inserting a separator at lane `r`. -/
private theorem childLo_wordInsertAt_succAbove {W v word n : ℕ} (hv : v < 2 ^ W) (lo : ℕ)
    (r k : Fin (n + 1)) :
    childLo W lo (wordInsertAt W r v word) (r.succ.succAbove k) = childLo W lo word k := by
  grind [Fin.succAbove, laneGet_wordInsertAt, childLo]

/-- Right endpoint of old child `k` after inserting a separator at lane `r`. -/
private theorem childHi_wordInsertAt_succAbove {W v word n : ℕ} (hv : v < 2 ^ W) (hi : ℕ)
    (r k : Fin (n + 1)) :
    childHi W hi (n + 1) (wordInsertAt W r v word) (r.succ.succAbove k) =
      if k = r then v else childHi W hi n word k := by
  grind [Fin.succAbove, laneGet_wordInsertAt, childHi]

/-- Left endpoint of the new child right of a separator inserted at lane `r`. -/
private theorem childLo_wordInsertAt_succ {W v word n : ℕ} (hv : v < 2 ^ W) (lo : ℕ)
    (r : Fin (n + 1)) : childLo W lo (wordInsertAt W r v word) r.succ = v + 1 := by
  grind [laneGet_wordInsertAt, childLo]

/-- Right endpoint of the new child right of a separator inserted at lane `r`. -/
private theorem childHi_wordInsertAt_succ {W v word n : ℕ} (hv : v < 2 ^ W) (hi : ℕ)
    (r : Fin (n + 1)) :
    childHi W hi (n + 1) (wordInsertAt W r v word) r.succ = childHi W hi n word r := by
  grind [laneGet_wordInsertAt, childHi]

/-- Inserting a separator `v` inside child interval `j` keeps the separators sorted inside
`[lo, hi)`. -/
private theorem wordInsertAt_sorted {W j v word cnt lo hi : ℕ} (hv : v < 2 ^ W) (hj : j ≤ cnt)
    (hlo0 : lo ≤ laneGet W word 0) (hhi_last : laneGet W word (cnt - 1) < hi)
    (hmono : ∀ i k, i < k → k < cnt → laneGet W word i < laneGet W word k)
    (hlo : childLo W lo word j ≤ v) (hhi : v < childHi W hi cnt word j) :
    lo ≤ laneGet W (wordInsertAt W j v word) 0 ∧
      laneGet W (wordInsertAt W j v word) (cnt + 1 - 1) < hi ∧
      ∀ i k, i < k → k < cnt + 1 →
        laneGet W (wordInsertAt W j v word) i < laneGet W (wordInsertAt W j v word) k := by
  simp only [childLo, childHi] at hlo hhi
  simp only [laneGet_wordInsertAt hv, Nat.add_sub_cancel]
  have hle : ∀ i k, i ≤ k → k < cnt → laneGet W word i ≤ laneGet W word k := fun i k h hk =>
    h.eq_or_lt.elim (· ▸ le_rfl) fun h => (hmono i k h hk).le
  refine ⟨by split_ifs at hlo ⊢ <;> omega, by split_ifs at hhi ⊢ <;> omega, fun i k hik hk => ?_⟩
  have h1 := hmono i k
  have h2 := hmono i (k - 1)
  have h3 := hmono (i - 1) (k - 1)
  have h4 := hle i (j - 1)
  have h5 := hle j (k - 1)
  split_ifs at hlo hhi ⊢ <;> omega

/-- Lift an inductive insertion result `(sl', T_c')` on child `r_b` of a valid branch
`.branch idx m cs_b` to the whole branch, preserving `ValidSubtree` and the local excess-key split
potential inequality. -/
private theorem lift_branch_child_insert {isRoot : Bool} {fpBits W_val tMin idx m lo hi q val : ℕ}
    {sl_b sl' : BTreeSlice} {mapFn : ℕ → Option ℕ} {cs_b : Fin (m + 1) → BTreeTree}
    {r_b : Fin (m + 1)}
    (hv_b : ValidSubtree isRoot fpBits W_val tMin sl_b.alloc sl_b.nodes lo hi mapFn
      (.branch idx m cs_b))
    (hother_b : ∀ i : Fin (m + 1), i.val ≠ r_b.val →
      ∀ q', childLo (fpBits + 2) lo (sl_b.nodes idx).keysWord i.val ≤ q' →
        q' ≤ childHi (fpBits + 2) hi m (sl_b.nodes idx).keysWord i.val → q' ≠ q)
    (hrec : sl_b.alloc ≤ sl'.alloc ∧ sl'.root = sl_b.root ∧
      (∀ v, v < sl_b.alloc → v ∉ (cs_b r_b).nodeSet → sl'.nodes v = sl_b.nodes v) ∧
      ∃ T_c' : BTreeTree,
        T_c'.rootIdx = (cs_b r_b).rootIdx ∧
        T_c'.height = (cs_b r_b).height ∧
        (∀ v ∈ T_c'.nodeSet, v ∈ (cs_b r_b).nodeSet ∨ sl_b.alloc ≤ v) ∧
        (tMin - 2) * (sl'.alloc - sl_b.alloc) + 2 * T_c'.potential tMin ≤
          2 * (cs_b r_b).potential tMin + 2 ∧
        ValidSubtree false fpBits W_val tMin sl'.alloc sl'.nodes
          (childLo (fpBits + 2) lo (sl_b.nodes idx).keysWord r_b.val)
          (childHi (fpBits + 2) hi m (sl_b.nodes idx).keysWord r_b.val)
          (Function.update mapFn q (some val)) T_c') :
    sl_b.alloc ≤ sl'.alloc ∧ sl'.root = sl_b.root ∧
    (∀ v, v < sl_b.alloc → v ∉ (BTreeTree.branch idx m cs_b).nodeSet →
      sl'.nodes v = sl_b.nodes v) ∧
    ∃ T' : BTreeTree,
      T'.rootIdx = idx ∧
      T'.height = (BTreeTree.branch idx m cs_b).height ∧
      (∀ v ∈ T'.nodeSet, v ∈ (BTreeTree.branch idx m cs_b).nodeSet ∨ sl_b.alloc ≤ v) ∧
      (tMin - 2) * (sl'.alloc - sl_b.alloc) + 2 * T'.potential tMin ≤
        2 * (BTreeTree.branch idx m cs_b).potential tMin + 2 ∧
      ValidSubtree isRoot fpBits W_val tMin sl'.alloc sl'.nodes lo hi
        (Function.update mapFn q (some val)) T' := by
  obtain ⟨hidx, hmeta, hdeg, hcnt_le, hkw, hvw, hlo0, hhi_last, hmono,
    hnot, hdisj, hht, hcs⟩ := hv_b
  obtain ⟨halloc_le, hroot, hfr, T_c', hrt_c, hht_c, hns_c, hpot_c, hv_c'⟩ := hrec
  have hlt : ∀ i, ∀ v ∈ (cs_b i).nodeSet, v < sl_b.alloc := fun i =>
    (hcs i).2.leafCount_le_card_nodeSet.1
  have hmem : ∀ i, (cs_b i).nodeSet ⊆ (BTreeTree.branch idx m cs_b).nodeSet := fun i v hv =>
    mem_insert_of_mem (mem_biUnion.mpr ⟨i, mem_univ i, hv⟩)
  have hht_eq : ∀ i, (Function.update cs_b r_b T_c' i).height = (cs_b i).height :=
    (Function.forall_update_iff cs_b fun i t => t.height = (cs_b i).height).2
      ⟨hht_c, fun _ _ => rfl⟩
  have hns : ∀ i, ∀ v ∈ (Function.update cs_b r_b T_c' i).nodeSet,
      v ∈ (cs_b i).nodeSet ∨ sl_b.alloc ≤ v :=
    (Function.forall_update_iff cs_b fun i t =>
      ∀ v ∈ t.nodeSet, v ∈ (cs_b i).nodeSet ∨ sl_b.alloc ≤ v).2 ⟨hns_c, fun _ _ _ => .inl⟩
  have hdisj' : ∀ i j, i ≠ j → j ≠ r_b → Disjoint (Function.update cs_b r_b T_c' i).nodeSet
      (Function.update cs_b r_b T_c' j).nodeSet := fun i j hij hj => by
    rw [Function.update_of_ne hj, disjoint_left]
    exact fun v hvi hvj => (hns i v hvi).elim (disjoint_left.mp (hdisj i j hij) · hvj)
      (hlt j v hvj).not_ge
  refine ⟨halloc_le, hroot, fun v hv_lt hv_not => hfr v hv_lt fun hvc => hv_not (hmem r_b hvc),
    .branch idx m (Function.update cs_b r_b T_c'), rfl,
    by simp only [BTreeTree.height, hht_eq], ?_,
    by
      have := sum_potential_update_add cs_b r_b T_c' tMin
      simp only [BTreeTree.potential]
      omega,
    ?_⟩
  · intro v hv_in
    rcases mem_insert.mp hv_in with rfl | hv_bi
    · exact .inl (mem_insert_self _ _)
    · obtain ⟨i, _, hvi⟩ := mem_biUnion.mp hv_bi
      exact (hns i v hvi).imp_left (hmem i ·)
  · dsimp only [ValidSubtree]
    rw [hfr idx hidx (hnot r_b)]
    refine ⟨hidx.trans_le halloc_le, hmeta, hdeg, hcnt_le, hkw, hvw, hlo0, hhi_last, hmono,
      fun i hmem => (hns i idx hmem).elim (hnot i) hidx.not_ge, fun i j hij =>
        if hj : j = r_b then (hdisj' j i hij.symm (hj ▸ hij)).symm else hdisj' i j hij hj,
      fun i => by rw [hht_eq, hht_eq]; exact hht i, fun i => ?_⟩
    rcases eq_or_ne i r_b with rfl | hi
    · rw [Function.update_self]
      exact ⟨(hcs i).1.trans hrt_c.symm, hv_c'⟩
    · rw [Function.update_of_ne hi]
      exact ⟨(hcs i).1, (hcs i).2.frame halloc_le
        (fun v hv => hfr v (hlt i v hv) (disjoint_left.mp (hdisj i r_b hi) hv))
        fun q' h1 h2 => Function.update_of_ne (hother_b i (Fin.val_ne_of_ne hi) q' h1 h2) _ _⟩

/-- Full inductive specification of `descendSplitToLeaf` followed by `finishLeafInsert` on any
non-full valid subtree `T`. -/
private theorem finishLeafInsert_descendSplitToLeaf_spec {isRoot : Bool}
    {fpBits W_val tMin lo hi q val fuel : ℕ} {sl : BTreeSlice} {mapFn : ℕ → Option ℕ}
    {T : BTreeTree}
    (ht3 : 3 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2)) (hval : val < 2 ^ W_val)
    (hhi : hi < 2 ^ fpBits) (hqlo : lo ≤ q) (hqhi : q ≤ hi)
    (hv : ValidSubtree isRoot fpBits W_val tMin sl.alloc sl.nodes lo hi mapFn T)
    (hnonfull : metaCount (sl.nodes T.rootIdx).metaWord < 2 * tMin - 1)
    (hfuel : T.height ≤ fuel) (halloc_val : sl.alloc + T.height ≤ 2 ^ W_val) :
    let p := descendSplitToLeaf fpBits W_val tMin fuel sl T.rootIdx q
    let sl' := finishLeafInsert fpBits W_val tMin p.1 p.2 q val
    sl.alloc ≤ sl'.alloc ∧
      sl'.root = sl.root ∧
      (∀ v, v < sl.alloc → v ∉ T.nodeSet → sl'.nodes v = sl.nodes v) ∧
      ∃ T' : BTreeTree,
        T'.rootIdx = T.rootIdx ∧
        T'.height = T.height ∧
        (∀ v ∈ T'.nodeSet, v ∈ T.nodeSet ∨ sl.alloc ≤ v) ∧
        (tMin - 2) * (sl'.alloc - sl.alloc) + 2 * T'.potential tMin ≤
          2 * T.potential tMin + 2 ∧
        ValidSubtree isRoot fpBits W_val tMin sl'.alloc sl'.nodes lo hi
          (Function.update mapFn q (some val)) T' := by
  induction fuel generalizing T isRoot sl lo hi <;> rcases T with ⟨idx, cnt⟩ | ⟨idx, cnt, cs⟩
  case zero.leaf | succ.leaf =>
    -- A leaf: no descent, `finishLeafInsert` acts on `idx` itself.
    rw [BTreeTree.rootIdx, hv.2.1, metaCount_mkNodeMeta] at hnonfull
    obtain ⟨halloc_eq, hrt_eq, hframe, cnt', hcnt', hv'⟩ :=
      finishLeafInsert_leaf_spec (by omega) hcap hval hhi hqlo hqhi hv hnonfull
    simp only [BTreeTree.rootIdx, show ∀ f, descendSplitToLeaf fpBits W_val tMin f sl idx q =
      (sl, idx) from fun f => by cases f <;> simp [descendSplitToLeaf, hv.2.1]]
    exact ⟨halloc_eq.ge, hrt_eq,
      fun v _ hv_not => hframe v (by simpa [BTreeTree.nodeSet] using hv_not),
      .leaf idx cnt', rfl, rfl, fun _ hv_in => .inl hv_in,
      by simp [halloc_eq, BTreeTree.potential]; omega, hv'⟩
  case zero.branch => simp [BTreeTree.height] at hfuel
  case succ.branch fuel' ih =>
    obtain ⟨hr_le, hclo_q, hq_chi, hother⟩ :=
      branch_child_routing (by omega) hcap hv hhi hqlo hqhi
    lift swarRank fpBits (2 * tMin) cnt q (sl.nodes idx).keysWord to Fin (cnt + 1)
      using Nat.lt_succ_of_le hr_le with r hr
    have hvT := hv
    obtain ⟨hidx, hmeta, hdeg, -, hkw, hvw, hlo0, hhi_last, hmono, hnot, hdisj, hht, hcs⟩ := hv
    dsimp only [BTreeTree.rootIdx] at hnonfull ⊢
    rw [hmeta, metaCount_mkNodeMeta] at hnonfull
    rw [BTreeTree.height_branch_of_eq hht] at hfuel halloc_val
    have hchi_le : childHi (fpBits + 2) hi cnt (sl.nodes idx).keysWord r ≤ hi :=
      childHi_le hhi_last.le hmono
    have hlt : ∀ k, ∀ v ∈ (cs k).nodeSet, v < sl.alloc := fun k =>
      (hcs k).2.leafCount_le_card_nodeSet.1
    have hmem : ∀ k, (cs k).nodeSet ⊆ (BTreeTree.branch idx cnt cs).nodeSet := fun k v hv =>
      mem_insert_of_mem (mem_biUnion.mpr ⟨k, mem_univ k, hv⟩)
    rcases ne_or_eq (metaCount (sl.nodes (cs r).rootIdx).metaWord) (2 * tMin - 1) with
      hfull_c | hfull_c
    · -- Subcase A: child `cs r` is not full; descend into it.
      have hcnt_c := (hcs r).2.metaCount_rootIdx_le
      rw [show descendSplitToLeaf fpBits W_val tMin (fuel' + 1) sl idx q =
          descendSplitToLeaf fpBits W_val tMin fuel' sl (cs r).rootIdx q by
        simp [descendSplitToLeaf, hmeta, ← hr, (hcs r).1, hfull_c]]
      exact lift_branch_child_insert hvT hother
        (ih (hchi_le.trans_lt hhi) hclo_q hq_chi (hcs r).2 (by omega) (by rw [hht r]; omega)
          (by rw [hht r]; omega))
    · -- Subcase B: child `cs r` is full; split it into `(leftT, sep, rightT)` first.
      let res := splitFullNode fpBits W_val tMin (sl.nodes (cs r).rootIdx)
      let sep := res.sep
      let sl_mid : BTreeSlice := { sl with
        alloc := sl.alloc + 1
        nodes := Function.update (Function.update (Function.update sl.nodes (cs r).rootIdx
          res.left) sl.alloc res.right) idx ⟨mkNodeMeta false (cnt + 1),
            wordInsertAt (fpBits + 2) r sep (sl.nodes idx).keysWord,
            wordInsertAt W_val (r + 1) sl.alloc (sl.nodes idx).valsWord⟩ }
      have hmid_alloc : sl_mid.alloc = sl.alloc + 1 := rfl
      -- `sl_mid` differs from `sl` only at `idx`, the split child and the fresh node `sl.alloc`.
      have hmid_nodes : ∀ v, v ≠ idx → v ≠ sl.alloc → v ≠ (cs r).rootIdx →
          sl_mid.nodes v = sl.nodes v := fun v h1 h2 h3 => by
        simp only [sl_mid, Function.update_of_ne h1, Function.update_of_ne h2,
          Function.update_of_ne h3]
      have hchild_lt : (cs r).rootIdx < sl.alloc := hlt r _ (cs r).rootIdx_mem_nodeSet
      have hchild_ne : (cs r).rootIdx ≠ idx := fun h => hnot r (h ▸ (cs r).rootIdx_mem_nodeSet)
      obtain ⟨leftT, rightT, hrtL, hrtR, hcntL, hcntR, hhtL, hhtR, hsubL, hsubR, hdisjLR,
        (hclo_sep : _ ≤ sep), (hsep_chi : sep < _), hpotLR, hvL, hvR⟩ :=
        splitFullNode_spec (alloc' := sl_mid.alloc) (nodes' := sl_mid.nodes)
          (leftIdx := (cs r).rootIdx) (rightIdx := sl.alloc) (by omega) (hcs r).2 hfull_c
          (Nat.le_succ _) (Nat.lt_succ_of_lt hchild_lt) (Nat.lt_succ_self _) hchild_lt.ne
          (by simp [sl_mid, res, Function.update_of_ne, hchild_ne, hchild_lt.ne])
          (by simp [sl_mid, res, Function.update_of_ne, hidx.ne'])
          fun v hv => have ⟨hne, hm⟩ := mem_erase.mp hv
            ⟨hmid_nodes v (fun h => hnot r (h ▸ hm)) (hlt r v hm).ne hne, hne, (hlt r v hm).ne⟩
      have hsep_lt_W : sep < 2 ^ (fpBits + 2) :=
        ((hsep_chi.trans_le hchi_le).trans hhi).trans
          (Nat.pow_lt_pow_right (by decide) (by omega))
      have hright_lt : sl.alloc < 2 ^ W_val := by omega
      have hsubL_c : leftT.nodeSet ⊆ (cs r).nodeSet :=
        hsubL.trans (insert_subset (cs r).rootIdx_mem_nodeSet (erase_subset _ _))
      have hsubR_c : rightT.nodeSet ⊆ insert sl.alloc (cs r).nodeSet :=
        hsubR.trans (insert_subset_insert _ (erase_subset _ _))
      -- The intermediate valid branch `T_mid` on `sl_mid` with `cnt + 1` separators.
      let cs_mid : Fin (cnt + 2) → BTreeTree :=
        r.succ.insertNth (α := fun _ => BTreeTree) rightT (Function.update cs r leftT)
      have hmidR : cs_mid r.succ = rightT := Fin.insertNth_apply_same _ _ _
      have hmidS (k : Fin (cnt + 1)) :
          cs_mid (r.succ.succAbove k) = Function.update cs r leftT k :=
        Fin.insertNth_apply_succAbove _ _ _ _
      have everyChild {P : BTreeTree → Prop} (hl : P leftT) (hr : P rightT)
          (hs : ∀ k, k ≠ r → P (cs k)) : ∀ i, P (cs_mid i) :=
        (Fin.forall_iff_succAbove r.succ).2 ⟨hmidR ▸ hr, fun k => hmidS k ▸
          (Function.forall_update_iff cs fun _ t => P t).2 ⟨hl, hs⟩ k⟩
      have heightOld : ∀ i, (cs_mid i).height = (cs ⟨0, Nat.succ_pos cnt⟩).height :=
        everyChild (P := fun t => t.height = _) (hhtL.trans (hht r)) (hhtR.trans (hht r))
          fun k _ => hht k
      obtain ⟨h7, h8, h9⟩ :=
        wordInsertAt_sorted hsep_lt_W r.is_le hlo0 hhi_last hmono hclo_sep hsep_chi
      have hv_mid : ValidSubtree isRoot fpBits W_val tMin sl_mid.alloc sl_mid.nodes lo hi
          mapFn (.branch idx (cnt + 1) cs_mid) := by
        simp only [ValidSubtree, sl_mid, Function.update_self]
        refine ⟨by omega, trivial, by split_ifs at hdeg ⊢ <;> omega, by omega,
          wordInsertAt_lt r.is_le hsep_lt_W hkw, wordInsertAt_lt (by omega) hright_lt hvw,
          h7, h8, h9, ?_, ?_, fun i => (heightOld i).trans (heightOld _).symm, ?_⟩
        · exact everyChild (P := fun t => idx ∉ t.nodeSet) (fun h => hnot r (hsubL_c h))
            (fun h => (mem_insert.mp (hsubR_c h)).elim hidx.ne (hnot r)) fun k _ => hnot k
        · have hsub : ∀ k, (Function.update cs r leftT k).nodeSet ⊆ (cs k).nodeSet :=
            (Function.forall_update_iff cs fun k t => t.nodeSet ⊆ (cs k).nodeSet).2
              ⟨hsubL_c, fun _ _ => subset_rfl⟩
          have hright : ∀ k, Disjoint (Function.update cs r leftT k).nodeSet rightT.nodeSet :=
            (Function.forall_update_iff cs fun _ t => Disjoint t.nodeSet rightT.nodeSet).2
              ⟨hdisjLR, fun k hk => (disjoint_insert_right.2
                ⟨fun h => (hlt k _ h).false, hdisj k r hk⟩).mono_right hsubR_c⟩
          intro i j hij
          rcases r.succ.eq_self_or_eq_succAbove i with rfl | ⟨k, rfl⟩ <;>
            rcases r.succ.eq_self_or_eq_succAbove j with rfl | ⟨l, rfl⟩
          · exact (hij rfl).elim
          · exact hmidR ▸ hmidS l ▸ (hright l).symm
          · exact hmidS k ▸ hmidR ▸ hright k
          · exact hmidS k ▸ hmidS l ▸
              (hdisj k l fun h => hij (congrArg _ h)).mono (hsub k) (hsub l)
        · refine (Fin.forall_iff_succAbove r.succ).2 ⟨?_, fun k => ?_⟩
          · rw [hmidR, childLo_wordInsertAt_succ hsep_lt_W, childHi_wordInsertAt_succ hsep_lt_W]
            exact ⟨by simp [laneGet_wordInsertAt hright_lt, hrtR], hvR⟩
          · rw [hmidS, laneGet_wordInsertAt_succAbove hright_lt,
              childLo_wordInsertAt_succAbove hsep_lt_W, childHi_wordInsertAt_succAbove hsep_lt_W]
            rcases eq_or_ne k r with rfl | hk
            · rw [Function.update_self, ite_eq_left rfl]
              exact ⟨(hcs k).1.trans hrtL.symm, hvL⟩
            · rw [Function.update_of_ne hk, ite_eq_right hk]
              exact ⟨(hcs k).1, (hcs k).2.frame (Nat.le_succ _) (fun v hv =>
                hmid_nodes v (fun h => hnot k (h ▸ hv)) (hlt k v hv).ne fun h =>
                  disjoint_left.mp (hdisj k r hk) hv (h ▸ (cs r).rootIdx_mem_nodeSet))
                fun _ _ _ => rfl⟩
      -- Potential drop from `T` to `T_mid`.
      have hpot_mid : 2 * (BTreeTree.branch idx (cnt + 1) cs_mid).potential tMin + (tMin - 2) ≤
          2 * (BTreeTree.branch idx cnt cs).potential tMin := by
        have := sum_potential_update_add cs r leftT tMin
        simp only [BTreeTree.potential, Fin.sum_univ_succAbove _ r.succ, hmidR, hmidS]
        omega
      -- Route `q` in `T_mid`: it goes to the right half exactly when `sep < q`.
      obtain ⟨hr'_le, hclo'_q, hq_chi', hother'⟩ :=
        branch_child_routing (by omega) hcap hv_mid hhi hqlo hqhi
      lift swarRank fpBits (2 * tMin) (cnt + 1) q (sl_mid.nodes idx).keysWord to Fin (cnt + 2)
        using Nat.lt_succ_of_le hr'_le with r'
      have hr'_eq : r' = if sep < q then r.succ else r.succ.succAbove r := by
        by_contra hne
        refine hother' _ (fun h => hne (Fin.ext h).symm) q ?_ ?_ rfl <;>
          simp only [sl_mid, Function.update_self] <;> split_ifs <;>
          simp only [childLo_wordInsertAt_succ hsep_lt_W, childHi_wordInsertAt_succ hsep_lt_W,
            childLo_wordInsertAt_succAbove hsep_lt_W, childHi_wordInsertAt_succAbove hsep_lt_W,
            ite_true] <;> omega
      obtain ⟨hnext_rt, hnext_nf⟩ :
          (if sep < q then sl.alloc else (cs r).rootIdx) = (cs_mid r').rootIdx ∧
            metaCount (sl_mid.nodes (cs_mid r').rootIdx).metaWord < 2 * tMin - 1 := by
        rw [hr'_eq]
        split_ifs <;> simp only [hmidR, hmidS, Function.update_self, hrtL, hrtR] <;>
          exact ⟨trivial, by omega⟩
      have hstep : descendSplitToLeaf fpBits W_val tMin (fuel' + 1) sl idx q =
          descendSplitToLeaf fpBits W_val tMin fuel' sl_mid (cs_mid r').rootIdx q := by
        rw [← hnext_rt]
        simp [descendSplitToLeaf, hmeta, ← hr, (hcs r).1, hfull_c, sl_mid, res, sep]
      -- Descend into the non-full child `cs_mid r'` of `T_mid` and lift the result twice.
      obtain ⟨halloc_rec, hrt_rec, hfr_mid, T', hrt_T', hht_T', hns_T', hpot_T', hv_T'⟩ :=
        lift_branch_child_insert hv_mid hother'
          (ih ((childHi_le (by simpa [sl_mid] using h8.le)
              (by simpa [sl_mid] using h9)).trans_lt hhi)
            hclo'_q hq_chi' (hv_mid.2.2.2.2.2.2.2.2.2.2.2.2 r').2 hnext_nf
            (by rw [heightOld]; omega) (by rw [heightOld]; omega))
      have hsub_mid : (BTreeTree.branch idx (cnt + 1) cs_mid).nodeSet ⊆
          insert sl.alloc (BTreeTree.branch idx cnt cs).nodeSet :=
        insert_subset (mem_insert_of_mem (mem_insert_self _ _)) (biUnion_subset.2 fun i _ =>
          everyChild (P := fun t => t.nodeSet ⊆ _)
            ((hsubL_c.trans (hmem r)).trans (subset_insert _ _))
            (hsubR_c.trans (insert_subset_insert _ (hmem r)))
            (fun k _ => (hmem k).trans (subset_insert _ _)) i)
      rw [hstep]
      refine ⟨(Nat.le_succ _).trans halloc_rec, hrt_rec, fun v hv_lt hv_not => ?_, T', hrt_T',
        hht_T'.trans ?_, fun v hv_in => ?_, ?_, hv_T'⟩
      · rw [hfr_mid v (Nat.lt_succ_of_lt hv_lt) fun hvm =>
          (mem_insert.mp (hsub_mid hvm)).elim hv_lt.ne hv_not]
        exact hmid_nodes v (fun h => hv_not (h ▸ mem_insert_self _ _)) hv_lt.ne fun h =>
          hv_not (h ▸ hmem r (cs r).rootIdx_mem_nodeSet)
      · rw [BTreeTree.height_branch_of_eq fun i => (heightOld i).trans (heightOld _).symm,
          BTreeTree.height_branch_of_eq hht, heightOld]
      · rcases hns_T' v hv_in with hvm | hv_ge
        · exact (mem_insert.mp (hsub_mid hvm)).elim (fun h => .inr h.ge) .inl
        · exact .inr (Nat.le_of_succ_le hv_ge)
      · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le halloc_rec
        rw [hd, Nat.add_sub_cancel_left] at hpot_T'
        rw [hd, show sl_mid.alloc + d - sl.alloc = d + 1 by omega, Nat.mul_add_one]
        omega

/-! ## Section 2: Full `btreeInsert` specification and `ValidSlice` invariant -/

/-- Top-level subtree specification of `btreeInsert` on an already-initialized slice (`1 ≤ alloc`):
increases height by at most `1` and excess-key split potential `(tMin - 2) * (alloc - 1) + 2 * pot`
by at most `2`. -/
theorem btreeInsert_subtree_spec {fpBits W_val tMin : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} {T : BTreeTree} {q val : ℕ}
    (ht3 : 3 ≤ tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (halloc_pos : 1 ≤ sl.alloc) (halloc_val : sl.alloc + hMaxBTree + 2 < 2 ^ W_val)
    (hroot : T.rootIdx = sl.root)
    (hv : ValidSubtree true fpBits W_val tMin sl.alloc sl.nodes 0 (2 ^ fpBits - 1) mapFn T)
    (hht_lt : T.height < hMaxBTree)
    (hq : q < 2 ^ fpBits) (hval : val < 2 ^ W_val) :
    let sl' := btreeInsert fpBits W_val tMin sl q val
    1 ≤ sl'.alloc ∧
      sl'.alloc ≤ sl.alloc + hMaxBTree + 2 ∧
      ∃ T' : BTreeTree,
        T'.rootIdx = sl'.root ∧
        T'.height ≤ T.height + 1 ∧
        (tMin - 2) * (sl'.alloc - 1) + 2 * T'.potential tMin ≤
          (tMin - 2) * (sl.alloc - 1) + 2 * T.potential tMin + 2 ∧
        ValidSubtree true fpBits W_val tMin sl'.alloc sl'.nodes 0 (2 ^ fpBits - 1)
          (Function.update mapFn q (some val)) T' := by
  obtain ⟨ha1_pos, ha1_le, -, T1, hT1_rt, hT1_nf, hT1_ht, hT1_pot, hv1⟩ :=
    splitRootIfFull_spec ht3 halloc_pos (by omega) hroot hv
  obtain ⟨halloc_le2, hrt2, -, T', hT'_rt, hT'_ht, -, hpot2, hv'⟩ :=
    finishLeafInsert_descendSplitToLeaf_spec (fuel := hMaxBTree) ht3 hcap hval
      (Nat.sub_lt (Nat.two_pow_pos fpBits) Nat.one_pos) (Nat.zero_le q) (by omega) hv1
      (by rwa [hT1_rt]) (by omega) (by omega)
  have hstep_alloc : ∀ (f cur : ℕ) (s : BTreeSlice),
      (descendSplitToLeaf fpBits W_val tMin f s cur q).1.alloc ≤ s.alloc + f := by
    intro f
    induction f with
    | zero => exact fun _ _ => le_rfl
    | succ f ihf =>
      intro cur s
      simp only [descendSplitToLeaf]
      split_ifs <;> first | exact Nat.le_add_right _ _ | exact (ihf _ _).trans (by grind)
  have hp := hstep_alloc hMaxBTree T1.rootIdx (splitRootIfFull fpBits W_val tMin sl)
  simp only [btreeInsert, show ensureRootSlice sl = sl from ite_eq_right (by omega), ← hT1_rt]
  set p := descendSplitToLeaf fpBits W_val tMin hMaxBTree (splitRootIfFull fpBits W_val tMin sl)
    T1.rootIdx q
  have hfin : (finishLeafInsert fpBits W_val tMin p.1 p.2 q val).alloc = p.1.alloc := by
    simp only [finishLeafInsert]
    split_ifs <;> rfl
  refine ⟨by omega, by omega, T', hT'_rt.trans (hT1_rt.trans hrt2.symm), by omega, ?_, hv'⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le halloc_le2
  rw [hd, Nat.add_sub_cancel_left] at hpot2
  rw [hd, Nat.sub_add_comm ha1_pos, Nat.mul_add]
  omega

/-- Every node inside a `ValidSubtree` automatically satisfies the packed bit-width bounds whenever
`1 ≤ tMin` and `4 * tMin ≤ 2 ^ metaBits`. -/
theorem ValidSubtree.node_bits_lt {isRoot : Bool} {metaBits fpBits W_val tMin alloc : ℕ}
    {nodes : ℕ → BTreeNode} {lo hi : ℕ} {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (ht1 : 1 ≤ tMin) (hmeta_cap : 4 * tMin ≤ 2 ^ metaBits)
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T) :
    ∀ v ∈ T.nodeSet,
      (nodes v).metaWord < 2 ^ metaBits ∧
      (nodes v).keysWord < 2 ^ ((2 * tMin) * (fpBits + 2)) ∧
      (nodes v).valsWord < 2 ^ ((2 * tMin) * W_val) := by
  have hpow : ∀ {c w x : ℕ}, c ≤ 2 * tMin → x < 2 ^ (c * w) → x < 2 ^ (2 * tMin * w) :=
    fun hc hx => hx.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hc))
  induction T generalizing isRoot lo hi with
  | leaf idx cnt =>
    obtain ⟨_, hmeta, hcnt, hkw, hvw, _⟩ := hv
    simp only [BTreeTree.nodeSet, mem_singleton, forall_eq]
    exact ⟨by rw [hmeta, mkNodeMeta]; split_ifs <;> omega, hpow (by omega) hkw,
      hpow (by omega) hvw⟩
  | branch idx cnt cs ih =>
    obtain ⟨_, hmeta, _, hcnt, hkw, hvw, _, _, _, _, _, _, hcs⟩ := hv
    intro v hv_in
    rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hv_in
    rcases hv_in with rfl | ⟨i, _, hvi⟩
    · exact ⟨by rw [hmeta, mkNodeMeta]; split_ifs <;> omega, hpow (by omega) hkw,
        hpow (by omega) hvw⟩
    · exact ih i (hcs i).2 v hvi

/-! ## Section 3: Concrete `SuccinctWhpParams` instantiation (`ValidWhpSlice`) -/

/-- Self-contained `SuccinctWhp` slice invariant coupling `BTreeSlice` (`alloc = 0` empty or
`1 ≤ alloc` rooted `ValidSubtree`) with insertion count `insCount` at capacity `n_max`. -/
def ValidWhpSlice (n_max insCount : ℕ) (sl : BTreeSlice)
    (mapFn : ℕ → Option ℕ) : Prop :=
  (sl.alloc = 0 ∧ mapFn = fun _ => none) ∨
  (1 ≤ sl.alloc ∧
    ∃ T : BTreeTree,
      T.rootIdx = sl.root ∧
      (tMinWhp n_max - 2) * (sl.alloc - 1) + 2 * T.potential (tMinWhp n_max) ≤ 2 * insCount ∧
      ValidSubtree true (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl.alloc sl.nodes 0 (2 ^ fpBitsWhp n_max - 1) mapFn T)

/-- Unallocated slice (`alloc = 0`) satisfies `ValidWhpSlice` for the empty map. -/
theorem validWhpSlice_zero (n_max insCount : ℕ) (nodes : ℕ → BTreeNode) :
    ValidWhpSlice n_max insCount ⟨0, 0, nodes⟩ (fun _ => none) :=
  Or.inl ⟨rfl, rfl⟩

/-- Parameter fit bounds for `ValidWhpSlice` when `whpThreshold c ≤ n_max`. -/
private theorem whpSlice_param_bounds {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    3 ≤ tMinWhp n_max ∧
    4 * tMinWhp n_max ≤ 2 ^ nodeMetaBitsWhp n_max ∧
    2 * tMinWhp n_max < 2 ^ keyLaneBitsWhp n_max ∧
    nSliceWhp n_max < 2 ^ valLaneBitsWhp n_max := by
  have h8 := eight_le_tMinWhp hth
  have ht_le : tMinWhp n_max ≤ 2 ^ Dynamic.logLogFactor n_max := tMinWhp_le_slabScale n_max
  have hpow : 2 ^ Dynamic.logLogFactor n_max ≤ 2 ^ (36 * Dynamic.logLogFactor n_max) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hdiv := Nat.div_le_self (32 * slabScale n_max ^ 12) (tMinWhp n_max - 1)
  have hL := Nat.pow_pos (n := 12) (slabScale_pos n_max)
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [nodeMetaBitsWhp, Nat.pow_add]
    omega
  · rw [keyLaneBitsWhp, fpBitsWhp, Nat.pow_add]
    omega
  · rw [nSliceWhp, two_pow_valLaneBitsWhp]
    omega

/-- `64 ≤ nSliceWhp n_max` unconditionally. -/
theorem sixty_four_le_nSliceWhp (n_max : ℕ) : 64 ≤ nSliceWhp n_max := by
  unfold nSliceWhp
  exact Nat.le_add_left 64 _

/-- **Bounded allocation, height, and packed-word eliminator**
(`ValidWhpSlice.alloc_and_height_lt`): Whenever `whpThreshold c ≤ n_max` and
`insCount ≤ 8 * (slabScale n_max) ^ 12`, any `ValidWhpSlice n_max insCount sl mapFn` has
`sl.alloc + hMaxBTree + 4 < nSliceWhp n_max` and unpacks either to
`sl.alloc = 0 ∧ mapFn = fun _ => none` or to a rooted `ValidSubtree` spine `T` of height
`< hMaxBTree` whose nodes fit within `(nodeMetaBitsWhp, keysWordBitsWhp, valsWordBitsWhp)`. -/
theorem ValidWhpSlice.alloc_and_height_lt {c n_max insCount : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} (hth : whpThreshold c ≤ n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hv : ValidWhpSlice n_max insCount sl mapFn) :
    sl.alloc + hMaxBTree + 4 < nSliceWhp n_max ∧
    ((sl.alloc = 0 ∧ mapFn = fun _ => none) ∨
      (1 ≤ sl.alloc ∧
        ∃ T : BTreeTree,
          T.rootIdx = sl.root ∧
          T.height < hMaxBTree ∧
          (tMinWhp n_max - 2) * (sl.alloc - 1) + 2 * T.potential (tMinWhp n_max) ≤ 2 * insCount ∧
          (∀ v ∈ T.nodeSet,
            (sl.nodes v).metaWord < 2 ^ nodeMetaBitsWhp n_max ∧
            (sl.nodes v).keysWord < 2 ^ keysWordBitsWhp n_max ∧
            (sl.nodes v).valsWord < 2 ^ valsWordBitsWhp n_max) ∧
          ValidSubtree true (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            sl.alloc sl.nodes 0 (2 ^ fpBitsWhp n_max - 1) mapFn T)) := by
  have h8 := eight_le_tMinWhp hth
  obtain ⟨_, hmeta_cap, _, hns_lt⟩ := whpSlice_param_bounds hth
  rcases hv with ⟨h0, hmap0⟩ | ⟨ha_pos, T, hrt, hpot, hT⟩
  · have h64 := sixty_four_le_nSliceWhp n_max
    exact ⟨by rw [hMaxBTree_eq]; omega, Or.inl ⟨h0, hmap0⟩⟩
  · have hmul := Nat.mul_le_mul_right (sl.alloc - 1)
      (show tMinWhp n_max - 1 ≤ 2 * (tMinWhp n_max - 2) by omega)
    rw [Nat.mul_assoc] at hmul
    have hdiv : sl.alloc - 1 ≤ 32 * (slabScale n_max) ^ 12 / (tMinWhp n_max - 1) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; omega)
    have halloc_lt : sl.alloc + hMaxBTree + 4 < nSliceWhp n_max := by
      rw [hMaxBTree_eq, nSliceWhp]
      omega
    refine ⟨halloc_lt, Or.inr ⟨ha_pos, T, hrt, ?_, hpot,
      hT.node_bits_lt (by omega) hmeta_cap, hT⟩⟩
    -- A tree of height `≥ 42` would have more than `alloc` leaves.
    by_contra hge
    rw [hMaxBTree_eq] at hge
    have hleaf := (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega : 0 < tMinWhp n_max)
      (by omega : 41 ≤ T.height - 1))).trans
        (hT.two_mul_pow_height_sub_one_le_leafCount (by omega) (by omega))
    have hle := hleaf.trans (hT.leafCount_le_card_nodeSet.2.trans hT.card_nodeSet_le_alloc)
    have h5 := Nat.pow_le_pow_left h8 5
    have h41 : 256 * slabScale n_max ^ 12 ≤ 2 * tMinWhp n_max ^ 41 :=
      calc 256 * slabScale n_max ^ 12
          ≤ (2 * tMinWhp n_max ^ 5) * (tMinWhp n_max ^ 3) ^ 12 :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (slabScale_le_tMinWhp_cubed hth) 12)
        _ = 2 * tMinWhp n_max ^ 41 := by ring
    rw [two_pow_valLaneBitsWhp] at hns_lt
    omega

/-- Lookup on a `ValidWhpSlice` returns `mapFn q` for every `q < 2 ^ fpBitsWhp n_max`. -/
theorem ValidWhpSlice.lookup_eq {c n_max insCount q : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} (hth : whpThreshold c ≤ n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) :
    btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q = mapFn q := by
  obtain ⟨ht3, _, hkey_lt, _⟩ := whpSlice_param_bounds hth
  obtain ⟨_, ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, hht_lt, _, _, hT⟩⟩ := hv.alloc_and_height_lt hth hins
  · simp [btreeLookup, h0]
  · exact btreeLookup_eq_of_subtree (by omega) hkey_lt ha_pos hrt hT hht_lt.le hq

/-- Deletion on a `ValidWhpSlice` preserves `ValidWhpSlice` at the same `insCount`. -/
theorem ValidWhpSlice.delete_spec {c n_max insCount q : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} (hth : whpThreshold c ≤ n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) :
    ValidWhpSlice n_max insCount
      (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q)
      (Function.update mapFn q none) := by
  obtain ⟨ht3, _, hkey_lt, _⟩ := whpSlice_param_bounds hth
  obtain ⟨_, ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, hht_lt, hpot, _, hT⟩⟩ := hv.alloc_and_height_lt hth hins
  · exact Or.inl ⟨by simp [btreeDelete, h0], Function.update_eq_self q _⟩
  · obtain ⟨halloc_eq, T', hrt', _, hpot', hT'⟩ :=
      btreeDelete_subtree_spec (by omega) hkey_lt ha_pos hrt hT hht_lt.le hq
    exact Or.inr ⟨halloc_eq ▸ ha_pos, T', hrt', by rw [halloc_eq]; omega, hT'⟩

/-- In-place value update on a `ValidWhpSlice` preserves `ValidWhpSlice` at the same `insCount`. -/
theorem ValidWhpSlice.update_spec {c n_max insCount q newVal : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} (hth : whpThreshold c ≤ n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) (hval : newVal < 2 ^ valLaneBitsWhp n_max) :
    ValidWhpSlice n_max insCount
      (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q newVal)
      (if (mapFn q).isSome then Function.update mapFn q (some newVal) else mapFn) := by
  obtain ⟨ht3, _, hkey_lt, _⟩ := whpSlice_param_bounds hth
  obtain ⟨_, ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, hht_lt, hpot, _, hT⟩⟩ := hv.alloc_and_height_lt hth hins
  · exact Or.inl ⟨by simp [btreeUpdate, h0], by simp⟩
  · obtain ⟨halloc_eq, T', hrt', _, hpot', hT'⟩ :=
      btreeUpdate_subtree_spec (by omega) hkey_lt ha_pos hrt hT hht_lt.le hq hval
    exact Or.inr ⟨halloc_eq ▸ ha_pos, T', hrt', by rw [halloc_eq]; omega, hT'⟩

/-- Insertion on a `ValidWhpSlice` produces a `ValidWhpSlice` at `insCount + 1` with `alloc <
nSliceWhp n_max`. -/
theorem ValidWhpSlice.insert_spec {c n_max insCount q val : ℕ} {sl : BTreeSlice}
    {mapFn : ℕ → Option ℕ} (hth : whpThreshold c ≤ n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) (hval : val < 2 ^ valLaneBitsWhp n_max) :
    let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) sl q val
    sl'.alloc < nSliceWhp n_max ∧
    ValidWhpSlice n_max (insCount + 1) sl' (Function.update mapFn q (some val)) := by
  obtain ⟨ht3, _, hkey_lt, hns_lt⟩ := whpSlice_param_bounds hth
  obtain ⟨halloc_lt, ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, hht_lt, hpot, _, hT⟩⟩ :=
    hv.alloc_and_height_lt hth hins
  · -- Empty `alloc = 0` slice: `ensureRootSlice` creates a valid 0-key leaf at `alloc = 1`!
    let sl0 : BTreeSlice := ⟨1, 0, Function.update sl.nodes 0 ⟨mkNodeMeta true 0, 0, 0⟩⟩
    have hv0 : ValidSubtree true (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        sl0.alloc sl0.nodes 0 (2 ^ fpBitsWhp n_max - 1) (fun _ => none) (.leaf 0 0) := by
      simp [ValidSubtree, sl0]
    -- `sl0.alloc = 1` and the empty leaf has potential `0 - (tMin - 1) = 0`.
    obtain ⟨ha'_pos, (ha'_le : _ ≤ 1 + hMaxBTree + 2), T', hrt', -,
        (hpot' : _ ≤ (tMinWhp n_max - 2) * 0 + 2 * (0 - (tMinWhp n_max - 1)) + 2), hT'⟩ :=
      btreeInsert_subtree_spec (sl := sl0) ht3 hkey_lt le_rfl
        (by omega : 1 + hMaxBTree + 2 < 2 ^ valLaneBitsWhp n_max) rfl hv0
        (by simp [BTreeTree.height, hMaxBTree_eq]) hq hval
    have hins_eq : ∀ F V t, btreeInsert F V t sl q val = btreeInsert F V t sl0 q val :=
      fun F V t => by simp [btreeInsert, ensureRootSlice, h0, sl0]
    rw [hins_eq]
    exact ⟨by omega, Or.inr ⟨ha'_pos, T', hrt', by omega, hT'⟩⟩
  · obtain ⟨ha'_pos, ha'_le, T', hrt', _, hpot', hT'⟩ :=
      btreeInsert_subtree_spec ht3 hkey_lt ha_pos (by omega) hrt hT hht_lt hq hval
    exact ⟨by omega, Or.inr ⟨ha'_pos, T', hrt', by omega, hT'⟩⟩

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
