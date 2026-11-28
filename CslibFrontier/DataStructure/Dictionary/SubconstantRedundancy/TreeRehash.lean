/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeBuild

/-!
# Pure Subtree Reconstruction and Local-Splice Step of `Algorithm 4`

This file formalizes the **pure reconstruction and local-splice step of `Algorithm 4`
(`Rehash(u)`) under supplied validated seeds** of Tianxiao Li, Jingxun Liang, Huacheng Yu, and
Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per Key*
([LiLiangYuZhou2024, Section 5.5, Algorithm 4];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 34 / printed p. 33).

Given replacement subtree seeds `seeds'` agreeing with `st.seeds` outside `InSubtree ℓ₀ u₀` and
validated by `hgood' : seeds'.AllGoodSeeds (P.paddedDom d)`, `rehashSubtree` builds a canonical
tree, splices `InSubtree ℓ₀ u₀`, updates only the `ℓ₀ - 1` strict ancestor nodes
`(j, ancestorAt u₀)` (`1 ≤ j < ℓ₀`), and leaves all other root trees and sibling subtrees
untouched. Uniform seed sampling, failed-seed rejection, recursive `Algorithm 4` sampling, and
randomized-history / expected-work obligations belong to Stage 3 under `#5349`.

## Main definitions

* `TreeSchedule.TreeState.rehashSubtree`: pure subtree reconstruction and local splice under
  supplied validated seeds (`Algorithm 4` reconstruction step).

## Main results

* `TreeSchedule.TreeState.seeds_rehashSubtree`, `TreeSchedule.TreeState.sentCount_rehashSubtree`:
  exact seed assignment and sentinel-count preservation.
* `TreeSchedule.TreeState.rehashSubtree_untouched_roots`,
  `TreeSchedule.TreeState.rehashSubtree_untouched_inner`,
  `TreeSchedule.TreeState.rehashSubtree_untouched_leaves`: strict locality outside `u₀`'s subtree
  and ancestor path.
* `TreeSchedule.TreeState.wellFormedPadded_rehashSubtree`: preservation of `WellFormedPadded`.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Finset

namespace TreeSchedule.TreeState

variable {P : TreeSchedule}

/-! ### Outside-subtree seed agreement helpers -/

section OutsideHelpers

variable {seeds seeds' : P.SeedAssignment} {ℓ₀ : ℕ} {u₀ : Fin (P.numNodes ℓ₀)}

private theorem activeAt_eq_of_outside {S : Finset (Fin P.paddedUniv)}
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = seeds.seed j hj v)
    {j : ℕ} (hj : j ≤ P.depth) (v : Fin (P.numNodes j)) (hnot : ¬ P.InSubtree ℓ₀ u₀ j v) :
    seeds'.activeAt S j hj v = seeds.activeAt S j hj v := by
  ext x
  simp only [SeedAssignment.mem_activeAt_iff,
    (SeedAssignment.primCoordAt_congr_ancestors hj v (fun i hi =>
      houtside i (hi.le.trans hj) _ (P.not_inSubtree_ancestor_of_not_inSubtree hi.le hnot)) x).1]

private theorem activeAt_rehash_root {S : Finset (Fin P.paddedUniv)} (hℓ₀ : ℓ₀ ≤ P.depth)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = seeds.seed j hj v) :
    seeds'.activeAt S ℓ₀ hℓ₀ u₀ = seeds.activeAt S ℓ₀ hℓ₀ u₀ := by
  ext x
  simp only [SeedAssignment.mem_activeAt_iff,
    (SeedAssignment.primCoordAt_congr_ancestors hℓ₀ u₀
      (fun i hi => houtside i (hi.le.trans hℓ₀) _ fun ⟨hge, _⟩ => by omega) x).1]

private theorem levelCoordEquiv_eq_of_outside
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = seeds.seed j hj v)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j))
    (hnot : ¬ P.InSubtree ℓ₀ u₀ j v) {x : Fin P.paddedUniv} (hnx : seeds'.nodeAt j hj x = v) :
    seeds'.levelCoordEquiv j hj1 hj x = seeds.levelCoordEquiv j hj1 hj x :=
  SeedAssignment.levelCoordEquiv_congr_ancestors hj1 hj v
    (fun i hi => houtside i (hi.trans hj) _ (P.not_inSubtree_ancestor_of_not_inSubtree hi hnot))
    x hnx

private theorem notMem_A0_of_not_anc_not_sub
    {S : Finset (Fin P.paddedUniv)} (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    {j : ℕ} (hj : j ≤ P.depth) (v : Fin (P.numNodes j)) (hnot_sub : ¬ P.InSubtree ℓ₀ u₀ j v)
    (hnot_anc : ¬ ∃ hlt : j < ℓ₀, v = P.ancestorAt hlt.le u₀)
    {x : Fin P.paddedUniv} (hx : x ∈ seeds'.activeAt S j hj v) :
    x ∉ seeds'.activeAt S ℓ₀ hℓ₀ u₀ := by
  intro hxA
  have hnv := (SeedAssignment.mem_activeAt_iff.mp hx).2
  have hnu₀ := (SeedAssignment.mem_activeAt_iff.mp hxA).2
  by_cases hlt : j < ℓ₀
  · exact hnot_anc ⟨hlt, by rw [← hnv, ← hnu₀, (seeds'.ancestorAt_nodeAt hlt.le hℓ₀ x).symm]⟩
  · exact hnot_sub ⟨by omega, by rw [← hnv, seeds'.ancestorAt_nodeAt (by omega) hj x, hnu₀]⟩

private theorem image_filter_outside_congr {S : Finset (Fin P.paddedUniv)}
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = seeds.seed j hj v)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j))
    {p p' : Fin P.paddedUniv → Prop} [DecidablePred p] [DecidablePred p']
    (hnot : ¬ P.InSubtree ℓ₀ u₀ j v)
    (hp : ∀ x ∈ seeds'.activeAt S j hj v, p x ↔ p' x) :
    ((seeds.activeAt S j hj v).filter p).image (seeds.idAt j hj1 hj) =
      ((seeds'.activeAt S j hj v).filter p').image (seeds'.idAt j hj1 hj) := by
  rw [← activeAt_eq_of_outside houtside hj v hnot, filter_congr hp]
  exact image_congr fun x hx =>
    congrArg (fun c => c.2.1)
      (levelCoordEquiv_eq_of_outside houtside hj1 hj v hnot
        (SeedAssignment.mem_activeAt_iff.mp (mem_filter.mp hx).1).2).symm

variable {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
  {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}

private theorem query_eq_outside (hwf : st.WellFormedPadded scheme d storeLvl)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j))
    {x : Fin P.paddedUniv} {vx : Fin P.valBound} (hnot : ¬ P.InSubtree ℓ₀ u₀ j v)
    (hdx : d x = some vx) (hnx : seeds'.nodeAt j hj x = v) (hsl : storeLvl x = j) :
    st.nodeQuery scheme j hj1 hj v (seeds'.idAt j hj1 hj x) =
      some (seeds'.quotAt j hj1 hj x, vx) := by
  have hc := levelCoordEquiv_eq_of_outside houtside hj1 hj v hnot hnx
  have hnx_old : st.seeds.nodeAt j hj x = v := by
    rw [← st.seeds.levelCoordEquiv_fst hj1 hj x, ← hc, seeds'.levelCoordEquiv_fst hj1 hj x, hnx]
  rw [show seeds'.idAt j hj1 hj x = st.seeds.idAt j hj1 hj x from congrArg (·.2.1) hc,
    show seeds'.quotAt j hj1 hj x = st.seeds.quotAt j hj1 hj x from congrArg (·.2.2) hc,
    hwf.query_eq_of_storeLvl j hj1 hj v x vx hdx hnx_old hsl]

private theorem wait_lookup_eq_outside (hwf : st.WellFormedPadded scheme d storeLvl)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    {j : ℕ} (hj2 : 2 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)) {x : Fin P.paddedUniv}
    (hnot : ¬ P.InSubtree ℓ₀ u₀ j v) (hx : x ∈ seeds'.activeAt (P.paddedDom d) j hj v)
    (hsl : storeLvl x < j) :
    (st.nodeWait j hj2 hj v).lookup (seeds'.idAt j (by omega) hj x) =
      some (seeds'.idAt (j - 1) (by omega) (by omega) x) := by
  have hnx := (SeedAssignment.mem_activeAt_iff.mp hx).2
  have hc := levelCoordEquiv_eq_of_outside houtside (by omega) hj v hnot hnx
  have hc_prev := levelCoordEquiv_eq_of_outside houtside (by omega) (by omega)
    (P.ancestorAt (by omega : j - 1 ≤ j) v)
    (P.not_inSubtree_ancestor_of_not_inSubtree (by omega) hnot)
    (by rw [← hnx, seeds'.ancestorAt_nodeAt])
  rw [show seeds'.idAt j (by omega) hj x = st.seeds.idAt j (by omega) hj x
      from congrArg (·.2.1) hc,
    show seeds'.idAt (j - 1) (by omega) (by omega) x = st.seeds.idAt (j - 1) (by omega) (by omega) x
      from congrArg (·.2.1) hc_prev,
    hwf.wait_lookup_eq j hj2 hj v x (activeAt_eq_of_outside houtside hj v hnot ▸ hx) hsl]

end OutsideHelpers

/-! ### Storage-level assignment `rehashStoreLvlTwo` (`2 ≤ ℓ₀`) -/

section RehashTwo

variable {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
  {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
  (hwf : st.WellFormedPadded scheme d storeLvl)
  {ℓ₀ : ℕ} (h2₀ : 2 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
  {seeds' : P.SeedAssignment}
  (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
    ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
  (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))

include hwf h2₀ houtside

private theorem card_wait_rehash_eq :
    let S := P.paddedDom d
    let A₀ := seeds'.activeAt S ℓ₀ hℓ₀ u₀
    let canonLvl := canonicalStoreLvl seeds' S hgood'
    (A₀.filter fun w => storeLvl w < ℓ₀).card = (A₀.filter fun w => canonLvl w < ℓ₀).card := by
  intro S A₀ canonLvl
  have hp1 := card_filter_add_card_filter_not (s := A₀) (p := fun w => storeLvl w < ℓ₀)
  have hp2 := card_filter_add_card_filter_not (s := A₀) (p := fun w => canonLvl w < ℓ₀)
  have h1 : (A₀.filter fun w => ¬ storeLvl w < ℓ₀).card = P.nLow ℓ₀ := by
    rw [filter_congr (fun _ _ => by omega : ∀ w ∈ A₀, ¬ storeLvl w < ℓ₀ ↔ ℓ₀ ≤ storeLvl w)]
    dsimp only [A₀]; rw [activeAt_rehash_root hℓ₀ houtside]
    exact subtree_stored_card_eq_nLow hwf h2₀ hℓ₀ u₀
  have h2 : (A₀.filter fun w => ¬ canonLvl w < ℓ₀).card = P.nLow ℓ₀ := by
    have hwf_c := P.wellFormedPadded_buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
    have hsc := P.seeds_buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
    rw [filter_congr (fun _ _ => by omega : ∀ w ∈ A₀, ¬ canonLvl w < ℓ₀ ↔ ℓ₀ ≤ canonLvl w),
      show A₀ = (P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood').seeds.activeAt
        S ℓ₀ hℓ₀ u₀ by simp [A₀, hsc]]
    exact subtree_stored_card_eq_nLow hwf_c h2₀ hℓ₀ u₀
  omega

private noncomputable def rehashWaitEquiv :
    { w // w ∈ (seeds'.activeAt (P.paddedDom d) ℓ₀ hℓ₀ u₀).filter fun w => storeLvl w < ℓ₀ } ≃
    { w // w ∈ (seeds'.activeAt (P.paddedDom d) ℓ₀ hℓ₀ u₀).filter
      fun w => canonicalStoreLvl seeds' (P.paddedDom d) hgood' w < ℓ₀ } :=
  (((seeds'.activeAt (P.paddedDom d) ℓ₀ hℓ₀ u₀).filter
    fun w => storeLvl w < ℓ₀).orderIsoOfFin rfl).toEquiv.symm.trans
    (((seeds'.activeAt (P.paddedDom d) ℓ₀ hℓ₀ u₀).filter
      fun w => canonicalStoreLvl seeds' (P.paddedDom d) hgood' w < ℓ₀).orderIsoOfFin
      (card_wait_rehash_eq hwf h2₀ hℓ₀ u₀ houtside hgood').symm).toEquiv

private noncomputable def rehashStoreLvlTwo : Fin P.paddedUniv → ℕ :=
  let S := P.paddedDom d
  let A₀ := seeds'.activeAt S ℓ₀ hℓ₀ u₀
  let canonLvl := canonicalStoreLvl seeds' S hgood'
  let φ := rehashWaitEquiv hwf h2₀ hℓ₀ u₀ houtside hgood'
  fun x =>
    if hxA : x ∈ A₀ then
      if hlt_c : canonLvl x < ℓ₀ then
        storeLvl (φ.symm ⟨x, mem_filter.mpr ⟨hxA, hlt_c⟩⟩).val
      else canonLvl x
    else storeLvl x

private theorem rehashStoreLvlTwo_ge_iff
    {x : Fin P.paddedUniv} (hxA : x ∈ seeds'.activeAt (P.paddedDom d) ℓ₀ hℓ₀ u₀)
    {j : ℕ} (hj : ℓ₀ ≤ j) :
    (rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood' x = j ↔
      canonicalStoreLvl seeds' (P.paddedDom d) hgood' x = j) ∧
    (rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood' x < j ↔
      canonicalStoreLvl seeds' (P.paddedDom d) hgood' x < j) := by
  dsimp only [rehashStoreLvlTwo]; rw [dite_eq_left hxA]
  by_cases hlt_c : canonicalStoreLvl seeds' (P.paddedDom d) hgood' x < ℓ₀
  · rw [dite_eq_left hlt_c]
    have hy_lt := (mem_filter.mp ((rehashWaitEquiv hwf h2₀ hℓ₀ u₀ houtside hgood').symm
      ⟨x, mem_filter.mpr ⟨hxA, hlt_c⟩⟩).property).2
    exact ⟨by constructor <;> intro <;> omega, by constructor <;> intro <;> omega⟩
  · rw [dite_eq_right hlt_c]; exact ⟨Iff.rfl, Iff.rfl⟩

private theorem card_filter_rehashStoreLvlTwo_lt {j : ℕ} (hj_lt : j < ℓ₀) :
    let A₀ := seeds'.activeAt (P.paddedDom d) ℓ₀ hℓ₀ u₀
    (A₀.filter fun x => rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood' x = j).card =
      (A₀.filter fun y => storeLvl y = j).card := by
  intro A₀
  set canonLvl := canonicalStoreLvl seeds' (P.paddedDom d) hgood'
  let φ := rehashWaitEquiv hwf h2₀ hℓ₀ u₀ houtside hgood'
  have hlt_of : ∀ {x}, x ∈ A₀.filter (fun x => rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood' x
      = j) → canonLvl x < ℓ₀ := fun hx => by
    obtain ⟨hxA, hsl⟩ := mem_filter.mp hx
    by_contra hge
    dsimp only [rehashStoreLvlTwo] at hsl; dsimp only [canonLvl] at hge
    rw [dite_eq_left hxA, dite_eq_right hge] at hsl; omega
  refine Finset.card_bij
    (fun x hx => (φ.symm ⟨x, mem_filter.mpr ⟨(mem_filter.mp hx).1, hlt_of hx⟩⟩).val)
    (fun x hx => ?_)
    (fun _ _ _ _ heq => congrArg Subtype.val (φ.symm.injective (Subtype.ext heq)))
    (fun y hy => ?_)
  · obtain ⟨hxA, hsl⟩ := mem_filter.mp hx
    have hlt_c := hlt_of hx
    dsimp only [rehashStoreLvlTwo] at hsl; rw [dite_eq_left hxA, dite_eq_left hlt_c] at hsl
    exact mem_filter.mpr ⟨(mem_filter.mp (φ.symm ⟨x, mem_filter.mpr ⟨hxA, hlt_c⟩⟩).property).1, hsl⟩
  · obtain ⟨hyA, hsly⟩ := mem_filter.mp hy
    let hyU : y ∈ A₀.filter fun w => storeLvl w < ℓ₀ := mem_filter.mpr ⟨hyA, by omega⟩
    let x_sub := φ ⟨y, hyU⟩
    obtain ⟨hxA, hlt_c⟩ := mem_filter.mp x_sub.property
    have hsymm : φ.symm ⟨x_sub.val, mem_filter.mpr ⟨hxA, hlt_c⟩⟩ = ⟨y, hyU⟩ :=
      φ.symm_apply_apply ⟨y, hyU⟩
    refine ⟨x_sub.val, mem_filter.mpr ⟨hxA, ?_⟩, congrArg Subtype.val hsymm⟩
    dsimp only [rehashStoreLvlTwo]; rw [dite_eq_left hxA, dite_eq_left hlt_c]
    exact (congrArg (fun p => storeLvl p.val) hsymm).trans hsly

private theorem validStoreLvl_rehashStoreLvlTwo :
    ValidStoreLvl seeds' (P.paddedDom d)
      (rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood') := by
  set S := P.paddedDom d
  set A₀ := seeds'.activeAt S ℓ₀ hℓ₀ u₀
  set canonLvl := canonicalStoreLvl seeds' S hgood'
  set storeLvl' := rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood'
  have hvsl_old := ValidStoreLvl.of_wellFormedPadded hwf
  have hvsl_can := validStoreLvl_canonicalStoreLvl seeds' S hgood'
  have hsub_filter : ∀ {j : ℕ} (hj : j ≤ P.depth) {u : Fin (P.numNodes j)},
      P.InSubtree ℓ₀ u₀ j u →
      ((seeds'.activeAt S j hj u).filter fun x => storeLvl' x = j) =
        (seeds'.activeAt S j hj u).filter fun x => canonLvl x = j :=
    fun hj u ⟨h0j, hanc_u⟩ => filter_congr fun x hx =>
      (rehashStoreLvlTwo_ge_iff hwf h2₀ hℓ₀ u₀ houtside hgood'
        (hanc_u ▸ seeds'.activeAt_subset_ancestor h0j hj u hx) h0j).1
  have hout_filter : ∀ {j : ℕ} (hj : j ≤ P.depth) (u : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j u → (¬ ∃ hlt : j < ℓ₀, u = P.ancestorAt hlt.le u₀) →
      ((seeds'.activeAt S j hj u).filter fun x => storeLvl' x = j) =
        (st.seeds.activeAt S j hj u).filter fun x => storeLvl x = j := by
    intro j hj u hsub hnot_anc
    rw [← activeAt_eq_of_outside houtside hj u hsub]
    refine filter_congr fun x hx => ?_
    have hxA := notMem_A0_of_not_anc_not_sub hℓ₀ u₀ hj u hsub hnot_anc hx
    dsimp only [storeLvl', rehashStoreLvlTwo]; rw [dite_eq_right hxA]
  exact
    { bounds := fun x hx => by
        dsimp only [storeLvl', rehashStoreLvlTwo]
        split_ifs with hxA hlt_c
        · exact hvsl_old.bounds _ (SeedAssignment.mem_activeAt_iff.mp
            (mem_filter.mp ((rehashWaitEquiv hwf h2₀ hℓ₀ u₀ houtside hgood').symm
              ⟨x, mem_filter.mpr ⟨hxA, hlt_c⟩⟩).property).1).1
        · exact hvsl_can.bounds x hx
        · exact hvsl_old.bounds x hx
      outside := fun x hx => by
        have hxA : x ∉ A₀ := fun hm => hx (SeedAssignment.mem_activeAt_iff.mp hm).1
        dsimp only [storeLvl', rehashStoreLvlTwo]; rw [dite_eq_right hxA]
        exact hvsl_old.outside x hx
      inner_card := fun j h2 hlt u => by
        by_cases hsub : P.InSubtree ℓ₀ u₀ j u
        · rw [hsub_filter hlt.le hsub]; exact hvsl_can.inner_card j h2 hlt u
        · by_cases hanc_ex : ∃ hj_lt : j < ℓ₀, u = P.ancestorAt hj_lt.le u₀
          · obtain ⟨hj_lt, rfl⟩ := hanc_ex
            set B := seeds'.activeAt S j hlt.le (P.ancestorAt hj_lt.le u₀)
            have hA_sub : A₀ ⊆ B := seeds'.activeAt_subset_ancestor hj_lt.le hℓ₀ u₀
            have hcard_split : ∀ f : Fin P.paddedUniv → ℕ,
                (B.filter fun x => f x = j).card =
                  ((B \ A₀).filter fun x => f x = j).card +
                    (A₀.filter fun x => f x = j).card := fun f => by
              rw [← card_union_of_disjoint
                    (disjoint_sdiff_self_left.mono (filter_subset _ _) (filter_subset _ _)),
                ← filter_union, sdiff_union_of_subset hA_sub]
            have hsdiff : ((B \ A₀).filter fun x => storeLvl' x = j) =
                (B \ A₀).filter fun x => storeLvl x = j :=
              filter_congr fun x hx => by
                dsimp only [storeLvl', rehashStoreLvlTwo]
                rw [dite_eq_right (mem_sdiff.mp hx).2]
            rw [hcard_split storeLvl', hsdiff,
              card_filter_rehashStoreLvlTwo_lt hwf h2₀ hℓ₀ u₀ houtside hgood' hj_lt,
              ← hcard_split storeLvl]
            dsimp only [B]; rw [activeAt_eq_of_outside houtside hlt.le _ hsub]
            exact hvsl_old.inner_card j h2 hlt _
          · rw [hout_filter hlt.le u hsub hanc_ex]; exact hvsl_old.inner_card j h2 hlt u
      leaf_card := fun u => by
        by_cases hsub : P.InSubtree ℓ₀ u₀ P.depth u
        · rw [hsub_filter le_rfl hsub]; exact hvsl_can.leaf_card u
        · rw [hout_filter le_rfl u hsub fun ⟨hlt, _⟩ => by omega]
          exact hvsl_old.leaf_card u }

end RehashTwo

/-- **Pure reconstruction and local-splice step of `Algorithm 4` (`Rehash(u₀)`) under supplied
validated seeds** ([LiLiangYuZhou2024, Section 5.5], PDF p. 34 / printed p. 33): given replacement
seeds `seeds'` agreeing with `st.seeds` outside `InSubtree ℓ₀ u₀` and validated by
`hgood' : seeds'.AllGoodSeeds (P.paddedDom d)`, builds a canonical tree and splices
`InSubtree ℓ₀ u₀` while rebuilding only the `ℓ₀ - 1` strict ancestor nodes `(j, ancestorAt u₀)`
(`1 ≤ j < ℓ₀`) and leaving sibling subtrees untouched. Uniform seed sampling, failed-seed
rejection, and recursive `Algorithm 4` sampling remain in Stage 3 (`#5349`). -/
noncomputable def rehashSubtree
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) : P.TreeState :=
  let st_canon := P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  if h0 : ℓ₀ = 0 then
    st_canon
  else if h1 : ℓ₀ = 1 then
    { topSeed := st.topSeed
      roots := fun u₁ => if P.InSubtree ℓ₀ u₀ 1 u₁ then st_canon.roots u₁ else st.roots u₁
      inner := fun ℓ h2 hlt v =>
        if P.InSubtree ℓ₀ u₀ ℓ v then st_canon.inner ℓ h2 hlt v else st.inner ℓ h2 hlt v
      leaves := fun v => if P.InSubtree ℓ₀ u₀ P.depth v then st_canon.leaves v else st.leaves v
      sentCount := st.sentCount }
  else
    have h2₀ : 2 ≤ ℓ₀ := by omega
    have h1lt₀ : 1 < ℓ₀ := by omega
    let storeLvl' := rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood'
    let hvsl' := validStoreLvl_rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood'
    { topSeed := st.topSeed
      roots := fun u₁ =>
        if u₁ = P.ancestorAt h1lt₀.le u₀ then buildRootOfStoreLvl d seeds' storeLvl' u₁
        else st.roots u₁
      inner := fun ℓ h2 hlt v =>
        if P.InSubtree ℓ₀ u₀ ℓ v then st_canon.inner ℓ h2 hlt v
        else if hlt₀ : ℓ < ℓ₀ then
          if v = P.ancestorAt hlt₀.le u₀ then
            buildInnerOfStoreLvl d seeds' hgood' hvsl' ℓ h2 hlt v
          else st.inner ℓ h2 hlt v
        else st.inner ℓ h2 hlt v
      leaves := fun v => if P.InSubtree ℓ₀ u₀ P.depth v then st_canon.leaves v else st.leaves v
      sentCount := st.sentCount }

@[simp]
theorem sentCount_rehashSubtree
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) :
    (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').sentCount = st.sentCount := by
  dsimp only [rehashSubtree]; split_ifs <;> simp

@[simp]
theorem seeds_rehashSubtree
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) :
    (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').seeds = seeds' := by
  set st_c := P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  have hsc : st_c.seeds = seeds' := P.seeds_buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  dsimp only [rehashSubtree]
  by_cases h0 : ℓ₀ = 0
  · rw [dite_eq_left h0]; exact hsc
  rw [dite_eq_right h0]; ext j hj v
  have hc := congrArg (·.seed j hj v) hsc
  have ho := houtside j hj v
  rcases (by omega : j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j < P.depth) ∨ j = P.depth) with
    rfl | rfl | ⟨h2, hlt⟩ | rfl <;>
  by_cases h1 : ℓ₀ = 1 <;>
  simp (disch := omega) only [h1, ↓reduceDIte, seeds_zero, seeds_one, seeds_inner, seeds_depth]
    at hc ho ⊢ <;>
  (try split_ifs) <;>
  first | exact hc | exact (ho ‹_›).symm | exact (ho fun ⟨hg, _⟩ => by omega).symm | simp

/-- Non-ancestor root trees (`u₁ ≠ ancestorAt u₀`, `1 ≤ ℓ₀`) are untouched by `rehashSubtree`. -/
theorem rehashSubtree_untouched_roots
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {ℓ₀ : ℕ} (h1₀ : 1 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    (u₁ : Fin (P.numNodes 1)) (hu₁ : u₁ ≠ P.ancestorAt h1₀ u₀) :
    (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').roots u₁ = st.roots u₁ := by
  dsimp only [rehashSubtree]; rw [dite_eq_right (by omega)]
  by_cases h1 : ℓ₀ = 1
  · subst h1
    have hnot : ¬ P.InSubtree 1 u₀ 1 u₁ := fun ⟨_, he⟩ =>
      hu₁ (by simpa only [P.ancestorAt_refl] using he)
    simp [hnot]
  · rw [dite_eq_right h1]; simp [hu₁]

/-- Inner nodes outside `InSubtree ℓ₀ u₀` and off `u₀`'s ancestor path are untouched. -/
theorem rehashSubtree_untouched_inner
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {ℓ₀ : ℕ} (h1₀ : 1 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth) (v : Fin (P.numNodes ℓ))
    (hnot_sub : ¬ P.InSubtree ℓ₀ u₀ ℓ v)
    (hnot_anc : ∀ hlt₀ : ℓ < ℓ₀, v ≠ P.ancestorAt hlt₀.le u₀) :
    (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').inner ℓ h2 hlt v =
      st.inner ℓ h2 hlt v := by
  dsimp only [rehashSubtree]; rw [dite_eq_right (by omega)]
  by_cases h1 : ℓ₀ = 1
  · rw [dite_eq_left h1]; dsimp only; rw [ite_eq_right hnot_sub]
  · rw [dite_eq_right h1]; dsimp only; rw [ite_eq_right hnot_sub]
    split_ifs with hlt0 heq
    · exact absurd heq (hnot_anc hlt0)
    · rfl
    · rfl

/-- Leaf nodes outside `InSubtree ℓ₀ u₀` (`1 ≤ ℓ₀`) are untouched by `rehashSubtree`. -/
theorem rehashSubtree_untouched_leaves
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {ℓ₀ : ℕ} (h1₀ : 1 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    (v : Fin (P.numNodes P.depth)) (hnot_sub : ¬ P.InSubtree ℓ₀ u₀ P.depth v) :
    (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').leaves v = st.leaves v := by
  dsimp only [rehashSubtree]; rw [dite_eq_right (by omega)]
  split_ifs <;> simp [hnot_sub]

section SpliceHelpers

variable {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
  {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ} {ℓ₀ : ℕ}

private theorem rehashSubtree_node_inSubtree (st : P.TreeState)
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (h1₀ : 1 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀)) (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j))
    (hsub : P.InSubtree ℓ₀ u₀ j v) :
    let st_fin := st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood'
    let st_c := P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
    st_fin.nodeDom j hj1 hj v = st_c.nodeDom j hj1 hj v ∧
    (∀ k, st_fin.nodeQuery scheme j hj1 hj v k = st_c.nodeQuery scheme j hj1 hj v k) ∧
    (∀ hj2 : 2 ≤ j, st_fin.nodeWait j hj2 hj v = st_c.nodeWait j hj2 hj v) ∧
    (∀ (hj2 : 2 ≤ j) (hlt : j < P.depth), st_fin.inner j hj2 hlt v = st_c.inner j hj2 hlt v) := by
  intro st_fin st_c
  by_cases hj_one : j = 1
  · subst hj_one
    have hℓ1 : ℓ₀ = 1 := by have := hsub.1; omega
    have hrt : st_fin.roots v = st_c.roots v := by
      dsimp only [st_fin, rehashSubtree]; subst hℓ1; simp [hsub, st_c]
    exact ⟨by rw [nodeDom_one, nodeDom_one, hrt],
      fun k => by rw [nodeQuery_one, nodeQuery_one, hrt], fun hj2 => by omega, fun hj2 => by omega⟩
  · by_cases hlt : j < P.depth
    · have hin : st_fin.inner j (by omega) hlt v = st_c.inner j (by omega) hlt v := by
        dsimp only [st_fin, rehashSubtree]; rw [dite_eq_right (by omega)]
        by_cases h1 : ℓ₀ = 1 <;> simp [h1, hsub, st_c]
      exact ⟨by rw [nodeDom_inner _ hj1 (by omega) hlt hj, nodeDom_inner _ hj1 (by omega) hlt hj,
          hin],
        fun k => by rw [nodeQuery_inner _ _ hj1 (by omega) hlt hj,
          nodeQuery_inner _ _ hj1 (by omega) hlt hj, hin],
        fun hj2 => by rw [nodeWait_inner _ hj2 hlt hj, nodeWait_inner _ hj2 hlt hj, hin],
        fun _ _ => hin⟩
    · obtain rfl : j = P.depth := by omega
      have hlf : st_fin.leaves v = st_c.leaves v := by
        dsimp only [st_fin, rehashSubtree]; rw [dite_eq_right (by omega)]
        by_cases h1 : ℓ₀ = 1 <;> simp [h1, hsub, st_c]
      exact ⟨by rw [nodeDom_depth, nodeDom_depth, hlf],
        fun k => by rw [nodeQuery_depth, nodeQuery_depth, hlf],
        fun _ => by rw [nodeWait_depth, nodeWait_depth, hlf], fun _ hlt' => absurd hlt' (by omega)⟩

private theorem rehashSubtree_node_outside (st : P.TreeState)
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (h1₀ : 1 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀)) (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j))
    (hnot_sub : ¬ P.InSubtree ℓ₀ u₀ j v)
    (hnot_anc : ¬ ∃ hlt : j < ℓ₀, v = P.ancestorAt hlt.le u₀) :
    let st_fin := st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood'
    st_fin.nodeDom j hj1 hj v = st.nodeDom j hj1 hj v ∧
    (∀ k, st_fin.nodeQuery scheme j hj1 hj v k = st.nodeQuery scheme j hj1 hj v k) ∧
    (∀ hj2 : 2 ≤ j, st_fin.nodeWait j hj2 hj v = st.nodeWait j hj2 hj v) := by
  intro st_fin
  by_cases hj_one : j = 1
  · subst hj_one
    have hneq : v ≠ P.ancestorAt h1₀ u₀ := by
      intro heq
      by_cases h1 : ℓ₀ = 1
      · subst h1; exact hnot_sub ⟨le_rfl, by simpa only [P.ancestorAt_refl] using heq⟩
      · exact hnot_anc ⟨by omega, heq⟩
    have hrt := st.rehashSubtree_untouched_roots hwf h1₀ hℓ₀ u₀ seeds' houtside hgood' v hneq
    exact ⟨by rw [nodeDom_one, nodeDom_one, hrt],
      fun k => by rw [nodeQuery_one, nodeQuery_one, hrt], fun hj2 => by omega⟩
  · by_cases hlt : j < P.depth
    · have hin := st.rehashSubtree_untouched_inner hwf h1₀ hℓ₀ u₀ seeds' houtside hgood'
        (by omega) hlt v hnot_sub fun hlt0 he => hnot_anc ⟨hlt0, he⟩
      exact ⟨by rw [nodeDom_inner _ hj1 (by omega) hlt hj,
          nodeDom_inner _ hj1 (by omega) hlt hj, hin],
        fun k => by rw [nodeQuery_inner _ _ hj1 (by omega) hlt hj,
          nodeQuery_inner _ _ hj1 (by omega) hlt hj, hin],
        fun hj2 => by rw [nodeWait_inner _ hj2 hlt hj, nodeWait_inner _ hj2 hlt hj, hin]⟩
    · obtain rfl : j = P.depth := by omega
      have hlf := st.rehashSubtree_untouched_leaves hwf h1₀ hℓ₀ u₀ seeds' houtside hgood' v hnot_sub
      exact ⟨by rw [nodeDom_depth, nodeDom_depth, hlf],
        fun k => by rw [nodeQuery_depth, nodeQuery_depth, hlf],
        fun _ => by rw [nodeWait_depth, nodeWait_depth, hlf]⟩

/-- Unified splice verification covering both `ℓ₀ = 1` (vacuous strict-ancestor branch) and
`2 ≤ ℓ₀` (strict ancestors rebuilt via `buildRootOfStoreLvl` / `buildInnerOfStoreLvl`). -/
private theorem wellFormedPadded_rehash_pos (st : P.TreeState) {storeLvl' : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (h1₀ : 1 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀)) {seeds' : P.SeedAssignment}
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    (hbounds : ∀ x ∈ P.paddedDom d, 1 ≤ storeLvl' x ∧ storeLvl' x ≤ P.depth)
    (hstore_out : ∀ x, x ∉ P.paddedDom d → storeLvl' x = 0)
    (hsub_iff : ∀ {j : ℕ} (hj : j ≤ P.depth) {v : Fin (P.numNodes j)}, P.InSubtree ℓ₀ u₀ j v →
      ∀ x ∈ seeds'.activeAt (P.paddedDom d) j hj v,
        (storeLvl' x = j ↔ canonicalStoreLvl seeds' (P.paddedDom d) hgood' x = j) ∧
        (storeLvl' x < j ↔ canonicalStoreLvl seeds' (P.paddedDom d) hgood' x < j))
    (hout_eq : ∀ {j : ℕ} (_hj1 : 1 ≤ j) (hj : j ≤ P.depth) {v : Fin (P.numNodes j)},
      ¬ P.InSubtree ℓ₀ u₀ j v → (¬ ∃ hlt : j < ℓ₀, v = P.ancestorAt hlt.le u₀) →
      ∀ x ∈ seeds'.activeAt (P.paddedDom d) j hj v, storeLvl' x = storeLvl x)
    (hanc : ∀ (h1lt : 1 < ℓ₀), ∃ hvsl' : ValidStoreLvl seeds' (P.paddedDom d) storeLvl',
      (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').roots (P.ancestorAt h1lt.le u₀) =
        buildRootOfStoreLvl d seeds' storeLvl' (P.ancestorAt h1lt.le u₀) ∧
      ∀ {j : ℕ} (hj2 : 2 ≤ j) (hlt : j < ℓ₀) (hjd : j < P.depth),
        (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').inner j hj2 hjd
            (P.ancestorAt hlt.le u₀) =
          buildInnerOfStoreLvl d seeds' hgood' hvsl' j hj2 hjd (P.ancestorAt hlt.le u₀)) :
    (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').WellFormedPadded
      scheme d storeLvl' := by
  have hwf_c := P.wellFormedPadded_buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  have hsc := P.seeds_buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  have hsf := st.seeds_rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood'
  have hsub_node := fun {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j))
      (hsub : P.InSubtree ℓ₀ u₀ j v) =>
    st.rehashSubtree_node_inSubtree hwf h1₀ hℓ₀ u₀ seeds' houtside hgood' hj1 hj v hsub
  have hout_node := fun {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j))
      (hns : ¬ P.InSubtree ℓ₀ u₀ j v) (hna : ¬ ∃ hlt : j < ℓ₀, v = P.ancestorAt hlt.le u₀) =>
    st.rehashSubtree_node_outside hwf h1₀ hℓ₀ u₀ seeds' houtside hgood' hj1 hj v hns hna
  have tri : ∀ {j : ℕ} (v : Fin (P.numNodes j)), P.InSubtree ℓ₀ u₀ j v ∨
      (∃ hlt : j < ℓ₀, v = P.ancestorAt hlt.le u₀) ∨
      (¬ P.InSubtree ℓ₀ u₀ j v ∧ ¬ ∃ hlt : j < ℓ₀, v = P.ancestorAt hlt.le u₀) := fun _ => by
    tauto
  exact
    { goodSeeds := by rwa [hsf]
      storeLvl_bounds := hbounds, storeLvl_outside := hstore_out
      dom_eq := fun j hj1 hj v => by
        rw [hsf]
        rcases tri v with hsub | ⟨hlt, rfl⟩ | ⟨hsub, hanc_ex⟩
        · rw [(hsub_node hj1 hj v hsub).1, hwf_c.dom_eq j hj1 hj v, hsc]
          congr 1; exact filter_congr fun x hx => (hsub_iff hj hsub x hx).1.symm
        · obtain ⟨hvsl', hrt, hin⟩ := hanc (by omega)
          by_cases hj_one : j = 1
          · subst hj_one
            rw [nodeDom_one, hrt, dom_buildRootOfStoreLvl d seeds' hgood' hvsl']
          · rw [nodeDom_inner _ hj1 (by omega) (hlt.trans_le hℓ₀), hin (by omega) hlt _,
              dom_buildInnerOfStoreLvl]
        · rw [(hout_node hj1 hj v hsub hanc_ex).1, hwf.dom_eq j hj1 hj v]
          exact image_filter_outside_congr houtside hj1 hj v hsub fun x hx => by
            rw [hout_eq hj1 hj hsub hanc_ex x hx]
      query_eq_of_storeLvl := fun j hj1 hj v x vx hdx hnx hsl => by
        rw [hsf] at hnx ⊢
        have hx_act : x ∈ seeds'.activeAt (P.paddedDom d) j hj v :=
          SeedAssignment.mem_activeAt_iff.mpr ⟨(P.mem_paddedDom_iff d x).mpr (by simp [hdx]), hnx⟩
        rcases tri v with hsub | ⟨hlt, rfl⟩ | ⟨hsub, hanc_ex⟩
        · rw [(hsub_node hj1 hj v hsub).2.1]
          have hq := hwf_c.query_eq_of_storeLvl j hj1 hj v x vx hdx (by rwa [hsc])
            ((hsub_iff hj hsub x hx_act).1.mp hsl)
          rwa [hsc] at hq
        · obtain ⟨hvsl', hrt, hin⟩ := hanc (by omega)
          by_cases hj_one : j = 1
          · subst hj_one; rw [nodeQuery_one, hrt]
            exact query_buildRootOfStoreLvl hgood' hvsl' _ hdx hnx hsl
          · rw [nodeQuery_inner _ _ hj1 (by omega) (hlt.trans_le hℓ₀), hin (by omega) hlt _]
            exact query_buildInnerOfStoreLvl hgood' hvsl' hj1 (by omega) _ _ hdx hnx hsl
        · rw [(hout_node hj1 hj v hsub hanc_ex).2.1]
          exact query_eq_outside hwf houtside hj1 hj v hsub hdx hnx
            (hout_eq hj1 hj hsub hanc_ex x hx_act ▸ hsl)
      inner_full := fun j hj2 hlt v => by
        rcases tri v with hsub | ⟨hlt0, rfl⟩ | ⟨hsub, hanc_ex⟩
        · rw [(hsub_node (by omega) hlt.le v hsub).2.2.2 hj2 hlt]
          exact hwf_c.inner_full j hj2 hlt v
        · obtain ⟨_, _, hin⟩ := hanc (by omega)
          rw [hin hj2 hlt0 hlt]; exact card_dom_buildInnerOfStoreLvl ..
        · rw [st.rehashSubtree_untouched_inner hwf h1₀ hℓ₀ u₀ seeds' houtside hgood' hj2 hlt v
            hsub fun hlt0 he => hanc_ex ⟨hlt0, he⟩]
          exact hwf.inner_full j hj2 hlt v
      wait_dom_eq := fun j hj2 hj v => by
        rw [hsf]
        rcases tri v with hsub | ⟨hlt, rfl⟩ | ⟨hsub, hanc_ex⟩
        · rw [(hsub_node (by omega) hj v hsub).2.2.1 hj2, hwf_c.wait_dom_eq j hj2 hj v, hsc]
          congr 1; exact filter_congr fun x hx => (hsub_iff hj hsub x hx).2.symm
        · obtain ⟨_, _, hin⟩ := hanc (by omega)
          rw [nodeWait_inner _ hj2 (hlt.trans_le hℓ₀), hin hj2 hlt _, wait_dom_buildInnerOfStoreLvl]
        · rw [(hout_node (by omega) hj v hsub hanc_ex).2.2 hj2, hwf.wait_dom_eq j hj2 hj v]
          exact image_filter_outside_congr houtside (by omega) hj v hsub fun x hx => by
            rw [hout_eq (by omega) hj hsub hanc_ex x hx]
      wait_lookup_eq := fun j hj2 hj v x hx hsl => by
        rw [hsf] at hx ⊢
        rcases tri v with hsub | ⟨hlt, rfl⟩ | ⟨hsub, hanc_ex⟩
        · rw [(hsub_node (by omega) hj v hsub).2.2.1 hj2]
          have hw := hwf_c.wait_lookup_eq j hj2 hj v x (by rwa [hsc])
            ((hsub_iff hj hsub x hx).2.mp hsl)
          rwa [hsc] at hw
        · obtain ⟨hvsl', _, hin⟩ := hanc (by omega)
          rw [nodeWait_inner _ hj2 (hlt.trans_le hℓ₀), hin hj2 hlt _]
          exact wait_lookup_buildInnerOfStoreLvl hgood' hvsl' hj2 (hlt.trans_le hℓ₀) _ hx hsl
        · rw [(hout_node (by omega) hj v hsub hanc_ex).2.2 hj2]
          exact wait_lookup_eq_outside hwf houtside hj2 hj v hsub hx
            (hout_eq (by omega) hj hsub hanc_ex x hx ▸ hsl) }

end SpliceHelpers

/-- **Subtree reconstruction (`rehashSubtree`, the pure local-splice step of `Algorithm 4` under
supplied validated seeds) preserves `WellFormedPadded`**. -/
theorem wellFormedPadded_rehashSubtree
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) :
    ∃ storeLvl' : Fin P.paddedUniv → ℕ,
      (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').WellFormedPadded
        scheme d storeLvl' := by
  have hwf_c := P.wellFormedPadded_buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  by_cases h0 : ℓ₀ = 0
  · exact ⟨canonicalStoreLvl seeds' (P.paddedDom d) hgood',
      by dsimp only [rehashSubtree]; rwa [dite_eq_left h0]⟩
  · by_cases h1 : ℓ₀ = 1
    · subst h1
      let h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
      let sl' : Fin P.paddedUniv → ℕ := fun x =>
        if seeds'.nodeAt 1 h1d x = u₀ then canonicalStoreLvl seeds' (P.paddedDom d) hgood' x
        else storeLvl x
      refine ⟨sl', st.wellFormedPadded_rehash_pos hwf le_rfl hℓ₀ u₀ houtside hgood'
        (fun x hx => by dsimp only [sl']; split_ifs <;>
          [exact hwf_c.storeLvl_bounds x hx; exact hwf.storeLvl_bounds x hx])
        (fun x hx => by dsimp only [sl']; split_ifs <;>
          [exact hwf_c.storeLvl_outside x hx; exact hwf.storeLvl_outside x hx])
        (fun {j} hj {v} ⟨h1j, hanc⟩ x hx => by
          have hn1 : seeds'.nodeAt 1 h1d x = u₀ := by
            rw [← seeds'.ancestorAt_nodeAt h1j hj x,
              (SeedAssignment.mem_activeAt_iff.mp hx).2, hanc]
          simp [sl', hn1])
        (fun {j} hj1 hj {v} hsub _ x hx => by
          have hne : seeds'.nodeAt 1 h1d x ≠ u₀ := fun h => hsub
            ⟨hj1, by
              rw [← (SeedAssignment.mem_activeAt_iff.mp hx).2,
                seeds'.ancestorAt_nodeAt hj1 hj x, h]⟩
          simp [sl', hne])
        (fun hlt => absurd hlt (by omega))⟩
    · have h2₀ : 2 ≤ ℓ₀ := by omega
      let storeLvl' := rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood'
      have hvsl' := validStoreLvl_rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood'
      refine ⟨storeLvl', st.wellFormedPadded_rehash_pos hwf (by omega) hℓ₀ u₀ houtside hgood'
        hvsl'.bounds hvsl'.outside
        (fun {j} hj {v} ⟨h0j, hanc⟩ x hx => rehashStoreLvlTwo_ge_iff hwf h2₀ hℓ₀ u₀ houtside hgood'
          (hanc ▸ seeds'.activeAt_subset_ancestor h0j hj v hx) h0j)
        (fun {j} _ hj {v} hsub hanc x hx => by
          dsimp only [storeLvl', rehashStoreLvlTwo]
          exact dite_eq_right (notMem_A0_of_not_anc_not_sub hℓ₀ u₀ hj v hsub hanc hx))
        (fun _ => ⟨hvsl',
          by dsimp only [rehashSubtree]; rw [dite_eq_right h0, dite_eq_right h1]
             dsimp only; rw [ite_eq_left rfl],
          fun {j} hj2 hlt hjd => by
            have hns : ¬ P.InSubtree ℓ₀ u₀ j (P.ancestorAt hlt.le u₀) := fun ⟨hg, _⟩ => by omega
            dsimp only [rehashSubtree]; rw [dite_eq_right h0, dite_eq_right h1]
            dsimp only; rw [ite_eq_right hns, dite_eq_left hlt, ite_eq_left rfl]⟩)⟩

end TreeSchedule.TreeState

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
