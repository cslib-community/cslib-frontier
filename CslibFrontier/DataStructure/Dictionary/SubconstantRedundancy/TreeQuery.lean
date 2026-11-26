/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeCore

/-!
# Root-to-Leaf Query and In-Place Payload Overwrite

This file formalizes deterministic root-to-leaf lookup (`rawQuery`, `query`) and in-place value
overwrite (`overwriteAtNode`, `rawOverwrite`) for the subconstant-redundancy dictionary tree of
Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant
Wasted Bits per Key* ([LiLiangYuZhou2024, Section 5.3];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 30–31 / printed pp. 29–30).

## Main definitions

* `TreeSchedule.TreeState.rawQuery`, `TreeSchedule.TreeState.query`: iterative root-to-leaf lookup.
* `TreeSchedule.TreeState.overwriteAtNode`, `TreeSchedule.TreeState.rawOverwrite`: in-place payload
  update of an active key.

## Main results

* `TreeSchedule.TreeState.rawQuery_eq`, `TreeSchedule.TreeState.query_eq_apply`: exact query
  correctness (rejecting false-positive ID collisions via global `levelCoordEquiv` bijectivity,
  `Footnote 10`).
* `TreeSchedule.TreeState.wellFormedPadded_rawOverwrite`: preservation of `WellFormedPadded` under
  in-place value updates.

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

/-! ## Section 1: Iterative root-to-leaf query (`rawQuery` and `query`) -/

/-- Iterative root-to-leaf query loop starting from `c : P.LevelCoord ℓ` (`Section 5.3`). -/
noncomputable def rawQueryLoop
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (c : P.LevelCoord ℓ) :
    Option (Fin P.valBound) :=
  match st.nodeQuery scheme ℓ h1 hℓ c.1 c.id with
  | some (q, v) =>
    if q == c.quot then some v
    else if hlt : ℓ < P.depth then
      st.rawQueryLoop scheme (ℓ + 1) (by omega) hlt (st.seeds.stepCoordEquiv h1 hlt c)
    else none
  | none =>
    if hlt : ℓ < P.depth then
      st.rawQueryLoop scheme (ℓ + 1) (by omega) hlt (st.seeds.stepCoordEquiv h1 hlt c)
    else none
termination_by P.depth - ℓ

/-- Look up an internal key `x : Fin P.paddedUniv` along its root-to-leaf coordinate path. -/
noncomputable def rawQuery
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (x : Fin P.paddedUniv) : Option (Fin P.valBound) :=
  st.rawQueryLoop scheme 1 le_rfl (Nat.one_le_of_lt P.two_le_depth)
    (st.seeds.levelOneCoordEquiv x)

theorem nodeQuery_match_iff
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (x : Fin P.paddedUniv) :
    (match st.nodeQuery scheme ℓ h1 hℓ (st.seeds.nodeAt ℓ hℓ x) (st.seeds.idAt ℓ h1 hℓ x) with
      | some (q, v) => if q == st.seeds.quotAt ℓ h1 hℓ x then some v else none
      | none => none) =
      if storeLvl x = ℓ then d x else none := by
  have hx_in : storeLvl x = ℓ → x ∈ P.paddedDom d := fun hsl => by
    by_contra hout; have := hwf.storeLvl_outside x hout; omega
  rcases hq : st.nodeQuery scheme ℓ h1 hℓ (st.seeds.nodeAt ℓ hℓ x)
      (st.seeds.idAt ℓ h1 hℓ x) with _ | ⟨q, v⟩
  · split_ifs with hsl
    · obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp ((P.mem_paddedDom_iff d x).mp (hx_in hsl))
      exact nomatch hq.symm.trans (hwf.query_eq_of_storeLvl ℓ h1 hℓ _ x vx hvx rfl hsl)
    · rfl
  · simp only
    have hid_mem : st.seeds.idAt ℓ h1 hℓ x ∈ st.nodeDom ℓ h1 hℓ (st.seeds.nodeAt ℓ hℓ x) :=
      by_contra fun hnot =>
        nomatch hq.symm.trans (st.nodeQuery_eq_none_of_notMem scheme h1 hℓ _ hnot)
    obtain ⟨y, hy_filt, hid_eq⟩ := mem_image.mp (hwf.dom_eq ℓ h1 hℓ _ ▸ hid_mem)
    obtain ⟨hy_act, hsl_y⟩ := mem_filter.mp hy_filt
    obtain ⟨hy_dom, hny⟩ := SeedAssignment.mem_activeAt_iff.mp hy_act
    obtain ⟨vy, hvy⟩ := Option.isSome_iff_exists.mp ((P.mem_paddedDom_iff d y).mp hy_dom)
    have hqy := hwf.query_eq_of_storeLvl ℓ h1 hℓ _ y vy hvy hny hsl_y
    rw [hid_eq, hq, Option.some.injEq, Prod.mk.injEq] at hqy
    obtain ⟨rfl, rfl⟩ := hqy
    by_cases hqx : st.seeds.quotAt ℓ h1 hℓ y == st.seeds.quotAt ℓ h1 hℓ x
    · obtain rfl : y = x := (st.seeds.levelCoordEquiv ℓ h1 hℓ).injective <| Prod.ext
        (by rw [st.seeds.levelCoordEquiv_fst, st.seeds.levelCoordEquiv_fst, hny])
        (Prod.ext hid_eq (eq_of_beq hqx))
      rw [ite_eq_left hqx, ite_eq_left hsl_y, hvy]
    · have hsl_ne : storeLvl x ≠ ℓ := fun hsl => hqx <| by
        rw [st.seeds.injOn_idAt_activeAt hwf.goodSeeds h1 hℓ _ hy_act
          (SeedAssignment.mem_activeAt_iff.mpr ⟨hx_in hsl, rfl⟩) hid_eq, beq_self_eq_true]
      rw [ite_eq_right hqx, ite_eq_right hsl_ne]

/-- **Internal query correctness**: `st.rawQuery scheme x = d x` for every `x : Fin P.paddedUniv`
(both active and absent, `Section 5.3` & `Footnote 10`, PDF p. 30 / printed p. 29). -/
theorem rawQuery_eq
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) (x : Fin P.paddedUniv) :
    st.rawQuery scheme x = d x := by
  have hsl : storeLvl x ≤ P.depth := by
    by_cases hxin : x ∈ P.paddedDom d
    · exact (hwf.storeLvl_bounds x hxin).2
    · rw [hwf.storeLvl_outside x hxin]; omega
  -- One loop step at level `m`, given the answer of the loop from level `m + 1`.
  have hstep (m) (h1 : 1 ≤ m) (hml : m ≤ P.depth)
      (hrec : ∀ hlt : m < P.depth, st.rawQueryLoop scheme (m + 1) (by omega) hlt
        (st.seeds.stepCoordEquiv h1 hlt (st.seeds.levelCoordEquiv m h1 hml x)) =
          if m + 1 ≤ storeLvl x then d x else none) :
      st.rawQueryLoop scheme m h1 hml (st.seeds.levelCoordEquiv m h1 hml x) =
        if m ≤ storeLvl x then d x else none := by
    have hm := nodeQuery_match_iff hwf h1 hml x
    simp only [SeedAssignment.idAt, SeedAssignment.quotAt] at hm
    unfold rawQueryLoop
    rw [st.seeds.levelCoordEquiv_fst h1 hml x]
    simp only [hrec]
    rcases hq : st.nodeQuery scheme m h1 hml (st.seeds.nodeAt m hml x)
        (st.seeds.levelCoordEquiv m h1 hml x).id with _ | ⟨q, v⟩ <;>
      simp only [hq, beq_iff_eq] at hm ⊢ <;>
      split_ifs at hm ⊢ <;> first | rfl | exact hm | omega
  have hgen (k) : ∀ m : ℕ, m + k = P.depth → (h1 : 1 ≤ m) → (hml : m ≤ P.depth) →
      st.rawQueryLoop scheme m h1 hml (st.seeds.levelCoordEquiv m h1 hml x) =
        if m ≤ storeLvl x then d x else none := by
    induction k with
    | zero => exact fun m hsum h1 hml => hstep m h1 hml fun hlt => absurd hlt (by omega)
    | succ k ih =>
      refine fun m hsum h1 hml => hstep m h1 hml fun hlt => ?_
      rw [← Equiv.trans_apply, ← st.seeds.levelCoordEquiv_succ h1 hlt]
      exact ih (m + 1) (by omega) (by omega) hlt
  dsimp only [rawQuery]
  rw [← st.seeds.levelCoordEquiv_one,
    hgen (P.depth - 1) 1 (by have := P.two_le_depth; omega) le_rfl _]
  by_cases hxin : x ∈ P.paddedDom d
  · rw [ite_eq_left (hwf.storeLvl_bounds x hxin).1]
  · rw [ite_eq_right (by rw [hwf.storeLvl_outside x hxin]; omega)]
    exact (Option.not_isSome_iff_eq_none.mp (mt (P.mem_paddedDom_iff d x).mpr hxin)).symm

/-- Deterministic external dictionary lookup `u : Fin P.univ → Option ℕ` (`Section 5.3`). -/
noncomputable def query
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (u : Fin P.univ) : Option ℕ :=
  (st.rawQuery scheme (P.embedReal u)).map Fin.val

/-- **External query correctness**: under `st.WellFormed scheme dict`, `st.query scheme u = dict u`
for every `u : Fin P.univ`. -/
theorem query_eq_apply
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {dict : Dictionary.State P.univ} (hwf : st.WellFormed scheme dict)
    (u : Fin P.univ) :
    st.query scheme u = dict u := by
  obtain ⟨d, storeLvl, hm, hwfp⟩ := hwf
  exact (congrArg (Option.map Fin.val) (rawQuery_eq hwfp _)).trans (hm.real_eq u)

/-! ## Section 2: Uniform node overwrite and `rawOverwrite` -/

private def overwriteRootAt (st : P.TreeState) (u : Fin (P.numNodes 1))
    (k : Fin (2 ^ P.idBits 1)) (qv : Fin (P.quotUniv 1) × Fin P.valBound) : P.TreeState :=
  if hk : k ∈ (st.roots u).table.tableMeta.dom then
    st.updateRoot u { (st.roots u) with table := (st.roots u).table.overwrite k qv hk }
  else st

private def overwriteInnerAt (st : P.TreeState) (L : ℕ) (h2 : 2 ≤ L) (hlt : L < P.depth)
    (u : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound) : P.TreeState :=
  if hk : k ∈ (st.inner L h2 hlt u).table.tableMeta.dom then
    st.updateInner L h2 hlt u
      { (st.inner L h2 hlt u) with table := (st.inner L h2 hlt u).table.overwrite k qv hk }
  else st

private def overwriteLeafAt
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (u : Fin (P.numNodes P.depth)) (k : Fin (2 ^ P.idBits P.depth))
    (qv : Fin (P.quotUniv P.depth) × Fin P.valBound) : P.TreeState :=
  if hk : k ∈ (st.leaves u).dom then
    st.updateLeaf u ((st.leaves u).overwrite scheme k qv hk)
  else st

/-- Overwrite `(quot, val)` of an ID `k` at `(L, uL)` (`1 ≤ L ≤ depth`), acting as identity if
`k ∉ st.nodeDom L h1L hLL uL`. -/
def overwriteAtNode (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (L : ℕ) (_h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound) : P.TreeState :=
  if h_one : L = 1 then
    Eq.ndrec
      (motive := fun m => Fin (P.numNodes m) → Fin (2 ^ P.idBits m) →
        Fin (P.quotUniv m) × Fin P.valBound → P.TreeState)
      (overwriteRootAt st) h_one.symm uL k qv
  else if hlt : L < P.depth then
    overwriteInnerAt st L (by omega) hlt uL k qv
  else
    have hd : L = P.depth := by omega
    Eq.ndrec
      (motive := fun m => Fin (P.numNodes m) → Fin (2 ^ P.idBits m) →
        Fin (P.quotUniv m) × Fin P.valBound → P.TreeState)
      (overwriteLeafAt scheme st) hd.symm uL k qv

private theorem overwriteAtNode_cases
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound) :
    let st' := st.overwriteAtNode scheme L h1L hLL uL k qv
    st' = st ∨
      (∃ (hL1 : L = 1) (nd : P.RootNode),
        nd.seed = (st.roots (hL1 ▸ uL)).seed ∧
        nd.table.tableMeta = (st.roots (hL1 ▸ uL)).table.tableMeta ∧
        st' = st.updateRoot (hL1 ▸ uL) nd) ∨
      (∃ (h2 : 2 ≤ L) (hlt : L < P.depth) (nd : P.InnerNode L),
        nd.seed = (st.inner L h2 hlt uL).seed ∧
        nd.wait = (st.inner L h2 hlt uL).wait ∧
        nd.table.tableMeta = (st.inner L h2 hlt uL).table.tableMeta ∧
        st' = st.updateInner L h2 hlt uL nd) ∨
      (∃ (hd : L = P.depth) (ln : P.LeafNode),
        ln.leafMeta.seed = (st.leaves (hd ▸ uL)).leafMeta.seed ∧
        ln.leafMeta.wait = (st.leaves (hd ▸ uL)).leafMeta.wait ∧
        ln.dom = (st.leaves (hd ▸ uL)).dom ∧
        st' = st.updateLeaf (hd ▸ uL) ln) := by
  dsimp only [overwriteAtNode]
  by_cases hL1 : L = 1
  · subst hL1; rw [dite_eq_left rfl]; dsimp only [overwriteRootAt]
    split_ifs with hk
    · exact Or.inr (Or.inl ⟨rfl,
        { (st.roots uL) with table := (st.roots uL).table.overwrite k qv hk },
        rfl, StorageTable.tableMeta_overwrite .., rfl⟩)
    · exact Or.inl rfl
  · by_cases hLlt : L < P.depth
    · rw [dite_eq_right hL1, dite_eq_left hLlt]; dsimp only [overwriteInnerAt]
      split_ifs with hk
      · have h2 : 2 ≤ L := by omega
        exact Or.inr (Or.inr (Or.inl ⟨h2, hLlt,
          { (st.inner L h2 hLlt uL) with
            table := (st.inner L h2 hLlt uL).table.overwrite k qv hk },
          rfl, rfl, StorageTable.tableMeta_overwrite .., rfl⟩))
      · exact Or.inl rfl
    · obtain rfl : L = P.depth := by omega
      rw [dite_eq_right hL1, dite_eq_right (lt_irrefl _)]; dsimp only [overwriteLeafAt]
      split_ifs with hk
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, (st.leaves uL).overwrite scheme k qv hk,
          rfl, rfl, LeafNode.dom_overwrite scheme (st.leaves uL) k qv hk, rfl⟩))
      · exact Or.inl rfl

theorem seeds_overwriteAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).seeds = st.seeds := by
  rcases st.overwriteAtNode_cases scheme h1L hLL uL k qv with
    h | ⟨rfl, nd, hs, _, h⟩ | ⟨h2, hlt, nd, hs, _, _, h⟩ | ⟨rfl, ln, hs, _, _, h⟩ <;> rw [h]
  · exact st.seeds_updateRoot_of_seed_eq _ _ hs
  · exact st.seeds_updateInner_of_seed_eq h2 hlt _ _ hs
  · exact st.seeds_updateLeaf_of_seed_eq _ _ hs

theorem sentCount_overwriteAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).sentCount = st.sentCount := by
  rcases st.overwriteAtNode_cases scheme h1L hLL uL k qv with
    h | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> rw [h] <;> rfl

theorem nodeDom_overwriteAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).nodeDom ℓ h1 hℓ u =
      st.nodeDom ℓ h1 hℓ u := by
  by_cases hsame : ∃ h_eq : ℓ = L, h_eq ▸ u = uL
  · obtain ⟨rfl, rfl⟩ := hsame
    rcases st.overwriteAtNode_cases scheme h1L hLL u k qv with
      h | ⟨rfl, nd, _, htm, h⟩ | ⟨h2, hlt, nd, _, _, htm, h⟩ | ⟨rfl, ln, _, _, hdom, h⟩ <;> rw [h]
    · simp [updateRoot, htm]
    · simp [nodeDom_inner _ h1 h2 hlt hℓ, updateInner, htm]
    · simp [updateLeaf, hdom]
  · push Not at hsame
    rcases st.overwriteAtNode_cases scheme h1L hLL uL k qv with
      h | ⟨rfl, nd, _, _, h⟩ | ⟨h2, hlt, nd, _, _, _, h⟩ | ⟨rfl, ln, _, _, _, h⟩ <;> rw [h]
    · exact st.nodeDom_updateRoot_other uL nd h1 hℓ u hsame
    · exact st.nodeDom_updateInner_other h2 hlt uL nd h1 hℓ u hsame
    · exact st.nodeDom_updateLeaf_other uL ln h1 hℓ u hsame

theorem nodeWait_overwriteAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).nodeWait ℓ h2 hℓ u =
      st.nodeWait ℓ h2 hℓ u := by
  by_cases hsame : ∃ h_eq : ℓ = L, h_eq ▸ u = uL
  · obtain ⟨rfl, rfl⟩ := hsame
    rcases st.overwriteAtNode_cases scheme h1L hLL u k qv with
      h | ⟨rfl, _, _, _, _⟩ | ⟨_, hlt, nd, _, hw, _, h⟩ | ⟨rfl, ln, _, hw, _, h⟩
    · rw [h]
    · omega
    · rw [h]; simp [nodeWait_inner _ h2 hlt hℓ, updateInner, hw]
    · rw [h]; simp [updateLeaf, hw]
  · push Not at hsame
    rcases st.overwriteAtNode_cases scheme h1L hLL uL k qv with
      h | ⟨rfl, nd, _, _, h⟩ | ⟨h2L, hlt, nd, _, _, _, h⟩ | ⟨rfl, ln, _, _, _, h⟩ <;> rw [h]
    · simp
    · exact st.nodeWait_updateInner_other h2L hlt uL nd h2 hℓ u hsame
    · exact st.nodeWait_updateLeaf_other uL ln h2 hℓ u hsame

theorem nodeQuery_overwriteAtNode_same
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k k' : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound) (hk : k ∈ st.nodeDom L h1L hLL uL) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).nodeQuery scheme L h1L hLL uL k' =
      Function.update (st.nodeQuery scheme L h1L hLL uL) k (some qv) k' := by
  dsimp only [overwriteAtNode]
  by_cases hL1 : L = 1
  · subst hL1
    rw [nodeDom_one] at hk
    simp [overwriteRootAt, hk, updateRoot, nodeQuery_one,
      funext (nodeQuery_one scheme st h1L hLL uL)]
  · by_cases hLlt : L < P.depth
    · have h2 : 2 ≤ L := by omega
      rw [nodeDom_inner st h1L h2 hLlt hLL] at hk
      simp [hL1, hLlt, overwriteInnerAt, hk, updateInner, nodeQuery_inner _ _ h1L h2 hLlt hLL,
        funext (nodeQuery_inner scheme st h1L h2 hLlt hLL uL)]
    · obtain rfl : L = P.depth := by omega
      rw [nodeDom_depth] at hk
      simp [hL1, overwriteLeafAt, hk, updateLeaf, nodeQuery_depth,
        funext (nodeQuery_depth scheme st h1L hLL uL)]

theorem nodeQuery_overwriteAtNode_other
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (k' : Fin (2 ^ P.idBits ℓ)) (hdiff : ∀ h_eq : ℓ = L, h_eq ▸ u ≠ uL) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).nodeQuery scheme ℓ h1 hℓ u k' =
      st.nodeQuery scheme ℓ h1 hℓ u k' := by
  rcases st.overwriteAtNode_cases scheme h1L hLL uL k qv with
    h | ⟨rfl, nd, _, _, h⟩ | ⟨h2, hlt, nd, _, _, _, h⟩ | ⟨rfl, ln, _, _, _, h⟩ <;> rw [h]
  · exact st.nodeQuery_updateRoot_other scheme uL nd h1 hℓ u k' hdiff
  · exact st.nodeQuery_updateInner_other scheme h2 hlt uL nd h1 hℓ u k' hdiff
  · exact st.nodeQuery_updateLeaf_other scheme uL ln h1 hℓ u k' hdiff

/-- Overwrite loop scanning root-to-leaf for the stored level of an active key (`Section 5.3`). -/
noncomputable def rawOverwriteLoop
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (v_new : Fin P.valBound) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (c : P.LevelCoord ℓ) : P.TreeState :=
  match st.nodeQuery scheme ℓ h1 hℓ c.1 c.id with
  | some (q, _) =>
    if q == c.quot then
      st.overwriteAtNode scheme ℓ h1 hℓ c.1 c.id (q, v_new)
    else if hlt : ℓ < P.depth then
      st.rawOverwriteLoop scheme v_new (ℓ + 1) (by omega) hlt
        (st.seeds.stepCoordEquiv h1 hlt c)
    else st
  | none =>
    if hlt : ℓ < P.depth then
      st.rawOverwriteLoop scheme v_new (ℓ + 1) (by omega) hlt
        (st.seeds.stepCoordEquiv h1 hlt c)
    else st
termination_by P.depth - ℓ

/-- Overwrite an active padded key `x ∈ P.paddedDom d` with `v_new : Fin P.valBound`. -/
noncomputable def rawOverwrite
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (x : Fin P.paddedUniv) (v_new : Fin P.valBound) : P.TreeState :=
  st.rawOverwriteLoop scheme v_new 1 le_rfl (Nat.one_le_of_lt P.two_le_depth)
    (st.seeds.levelOneCoordEquiv x)

private theorem sentCount_and_seeds_rawOverwriteLoop
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (v_new : Fin P.valBound) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (c : P.LevelCoord ℓ) :
    (st.rawOverwriteLoop scheme v_new ℓ h1 hℓ c).sentCount = st.sentCount ∧
    (st.rawOverwriteLoop scheme v_new ℓ h1 hℓ c).seeds = st.seeds := by
  generalize hk : P.depth - ℓ = k
  induction k using Nat.strongRecOn generalizing ℓ with
  | ind k ih =>
    unfold rawOverwriteLoop
    split
    · split_ifs with _ hlt
      · exact ⟨st.sentCount_overwriteAtNode scheme h1 hℓ _ _ _,
          st.seeds_overwriteAtNode scheme h1 hℓ _ _ _⟩
      · exact ih _ (by omega) (ℓ + 1) (by omega) hlt _ rfl
      · exact ⟨rfl, rfl⟩
    · split_ifs with hlt
      · exact ih _ (by omega) (ℓ + 1) (by omega) hlt _ rfl
      · exact ⟨rfl, rfl⟩

theorem sentCount_rawOverwrite
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (x : Fin P.paddedUniv) (v_new : Fin P.valBound) :
    (st.rawOverwrite scheme x v_new).sentCount = st.sentCount :=
  (st.sentCount_and_seeds_rawOverwriteLoop scheme v_new 1 le_rfl
    (Nat.one_le_of_lt P.two_le_depth) _).1

theorem seeds_rawOverwrite
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (x : Fin P.paddedUniv) (v_new : Fin P.valBound) :
    (st.rawOverwrite scheme x v_new).seeds = st.seeds :=
  (st.sentCount_and_seeds_rawOverwriteLoop scheme v_new 1 le_rfl
    (Nat.one_le_of_lt P.two_le_depth) _).2

theorem wellFormedPadded_rawOverwrite
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) {x : Fin P.paddedUniv}
    (hx : x ∈ P.paddedDom d) (v_new : Fin P.valBound) :
    (st.rawOverwrite scheme x v_new).WellFormedPadded scheme
      (Function.update d x (some v_new)) storeLvl := by
  have hdom_upd : P.paddedDom (Function.update d x (some v_new)) = P.paddedDom d := by
    rw [P.paddedDom_update_some, insert_eq_of_mem hx]
  obtain ⟨hlo_x, hhi_x⟩ := hwf.storeLvl_bounds x hx
  set L := storeLvl x
  let uL := st.seeds.nodeAt L hhi_x x
  let idL := st.seeds.idAt L hlo_x hhi_x x
  let qL := st.seeds.quotAt L hlo_x hhi_x x
  have hmemL : idL ∈ st.nodeDom L hlo_x hhi_x uL := by
    rw [hwf.dom_eq L hlo_x hhi_x uL]
    exact mem_image_of_mem _ (mem_filter.mpr ⟨SeedAssignment.mem_activeAt_iff.mpr ⟨hx, rfl⟩, rfl⟩)
  let st_target := st.overwriteAtNode scheme L hlo_x hhi_x uL idL (qL, v_new)
  have heq_target : st.rawOverwrite scheme x v_new = st_target := by
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp ((P.mem_paddedDom_iff d x).mp hx)
    have hgen (k) : ∀ m : ℕ, m + k = L → (h1 : 1 ≤ m) → (hmL : m ≤ L) →
        st.rawOverwriteLoop scheme v_new m h1 (hmL.trans hhi_x)
          (st.seeds.levelCoordEquiv m h1 (hmL.trans hhi_x) x) = st_target := by
      induction k with
      | zero =>
        intro m hsum h1 hmL
        obtain rfl : m = L := by omega
        unfold rawOverwriteLoop
        rw [show st.seeds.levelCoordEquiv L h1 _ x = (uL, idL, qL) from
          Prod.ext (st.seeds.levelCoordEquiv_fst h1 hhi_x x) rfl,
          show st.nodeQuery scheme L h1 _ uL idL = some (qL, vx) from
          hwf.query_eq_of_storeLvl L h1 hhi_x uL x vx hvx rfl rfl]
        simp [st_target]
      | succ k ih =>
        intro m hsum h1 hmL
        have hm_lt_d : m < P.depth := by omega
        have hnm := nodeQuery_match_iff hwf h1 (hmL.trans hhi_x) x
        rw [ite_eq_right (by omega : storeLvl x ≠ m)] at hnm
        simp only [SeedAssignment.idAt, SeedAssignment.quotAt] at hnm
        have hrec : ∀ hlt : m < P.depth, st.rawOverwriteLoop scheme v_new (m + 1) (by omega) hlt
            (st.seeds.stepCoordEquiv h1 hlt (st.seeds.levelCoordEquiv m h1 (hmL.trans hhi_x) x)) =
            st_target := fun hlt => by
          rw [← Equiv.trans_apply, ← st.seeds.levelCoordEquiv_succ h1 hlt]
          exact ih (m + 1) (by omega) (by omega) (by omega)
        unfold rawOverwriteLoop
        rw [st.seeds.levelCoordEquiv_fst h1 _ x]
        simp only [hrec, dite_eq_ite, hm_lt_d, ite_true]
        rcases hqm : st.nodeQuery scheme m h1 (hmL.trans hhi_x)
            (st.seeds.nodeAt m (hmL.trans hhi_x) x)
            (st.seeds.levelCoordEquiv m h1 (hmL.trans hhi_x) x).id with _ | ⟨q, w⟩
        · rfl
        · simp only [hqm, beq_iff_eq] at hnm ⊢
          split_ifs at hnm ⊢; rfl
    simpa only [rawOverwrite, ← st.seeds.levelCoordEquiv_one] using
      hgen (L - 1) 1 (by omega) le_rfl hlo_x
  rw [heq_target]
  have hseeds : st_target.seeds = st.seeds :=
    st.seeds_overwriteAtNode scheme hlo_x hhi_x uL idL (qL, v_new)
  dsimp only [st_target] at hseeds ⊢
  refine
    { goodSeeds := by simpa only [hseeds, hdom_upd] using hwf.goodSeeds
      storeLvl_bounds := by simpa only [hdom_upd] using hwf.storeLvl_bounds
      storeLvl_outside := by simpa only [hdom_upd] using hwf.storeLvl_outside
      dom_eq := fun ℓ h1' hℓ' u => by
        simpa only [st.nodeDom_overwriteAtNode scheme hlo_x hhi_x uL idL (qL, v_new) h1' hℓ' u,
          hseeds, hdom_upd] using hwf.dom_eq ℓ h1' hℓ' u
      query_eq_of_storeLvl := fun ℓ h1' hℓ' u y vy hdy hny hsly => ?_
      inner_full := fun ℓ h2' hlt' u => by
        simpa only [nodeDom_inner _ (Nat.one_le_of_lt h2') h2' hlt' hlt'.le,
          hwf.inner_full ℓ h2' hlt' u] using
          congrArg Finset.card (st.nodeDom_overwriteAtNode scheme hlo_x hhi_x uL idL (qL, v_new)
            (Nat.one_le_of_lt h2') hlt'.le u)
      wait_dom_eq := fun ℓ h2' hℓ' u => by
        simpa only [st.nodeWait_overwriteAtNode scheme hlo_x hhi_x uL idL (qL, v_new) h2' hℓ' u,
          hseeds, hdom_upd] using hwf.wait_dom_eq ℓ h2' hℓ' u
      wait_lookup_eq := fun ℓ h2' hℓ' u y hy hsly => by
        rw [hseeds, hdom_upd] at hy
        simpa only [st.nodeWait_overwriteAtNode scheme hlo_x hhi_x uL idL (qL, v_new) h2' hℓ' u,
          hseeds] using hwf.wait_lookup_eq ℓ h2' hℓ' u y hy hsly }
  rw [hseeds] at hny ⊢
  by_cases hyx : y = x
  · subst y
    rw [Function.update_self, Option.some.injEq] at hdy
    obtain rfl : ℓ = L := hsly.symm
    subst hdy hny
    rw [st.nodeQuery_overwriteAtNode_same _ _ _ _ _ _ _ hmemL, Function.update_self]
  · rw [Function.update_of_ne hyx] at hdy
    have hy_in : y ∈ P.paddedDom d := (P.mem_paddedDom_iff d y).mpr (by simp [hdy])
    have hy_old := hwf.query_eq_of_storeLvl ℓ h1' hℓ' u y vy hdy hny hsly
    by_cases hsame : ∃ h_eq : ℓ = L, h_eq ▸ u = uL
    · obtain ⟨rfl, rfl⟩ := hsame
      rw [st.nodeQuery_overwriteAtNode_same _ _ _ _ _ _ _ hmemL]
      have hid_ne : st.seeds.idAt L h1' hℓ' y ≠ idL := fun h =>
        hyx (st.seeds.injOn_idAt_activeAt hwf.goodSeeds hlo_x hhi_x uL
          (SeedAssignment.mem_activeAt_iff.mpr ⟨hy_in, hny⟩)
          (SeedAssignment.mem_activeAt_iff.mpr ⟨hx, rfl⟩) h)
      rw [Function.update_of_ne hid_ne, hy_old]
    · push Not at hsame
      rw [st.nodeQuery_overwriteAtNode_other _ _ _ _ _ _ h1' hℓ' u _ hsame, hy_old]

end TreeSchedule.TreeState

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
