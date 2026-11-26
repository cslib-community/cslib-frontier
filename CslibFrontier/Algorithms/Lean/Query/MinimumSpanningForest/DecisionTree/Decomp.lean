/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Canonical
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Additive Decomposition of Optimal MSF Decision-Tree Depth

A step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), formalizing the additive
decomposition theory of Section 5.1 (pp. 25–26): Property 5.3 cut-vertex sufficiency
(`msfDecomposes_of_card_inter_le_one`), intra-block pruning and adversary lower bound (Lemma 5.4
and Lemma 5.5 binary additivity `optDepth_edgeUnion_eq_add`), general list decomposition
`optDepth_edgeUnionList_eq_sum` (Lemma 5.5), `sum_optDepth_le_optDepthMN` (Corollary 5.6, p. 26),
and the doubling inequality `two_mul_optDepthMN_le` (Corollary 5.7, p. 26).

## Main definitions

* `Cslib.Query.MinimumSpanningForest.edgeUnion`,
  `Cslib.Query.MinimumSpanningForest.edgeUnionList`: disjoint edge unions sharing a common vertex
  set `Fin n`.
* `Cslib.Query.MinimumSpanningForest.MSFDecomposes`,
  `Cslib.Query.MinimumSpanningForest.ValidDecomp`: components sharing at most one vertex whose
  optimal MSFs decompose independently (Property 5.3).

## Main results

* `Cslib.Query.MinimumSpanningForest.msfDecomposes_of_card_inter_le_one`: subgraphs sharing at
  most one vertex satisfy Property 5.3 (`MSFDecomposes`).
* `Cslib.Query.MinimumSpanningForest.optDepth_edgeUnion_eq_add`: binary additivity
  `optDepth (edgeUnion ends₁ ends₂) = optDepth ends₁ + optDepth ends₂` (Lemma 5.4 / Lemma 5.5).
* `Cslib.Query.MinimumSpanningForest.optDepth_edgeUnionList_eq_sum`: Lemma 5.5 of
  [PettieRamachandran2002].
* `Cslib.Query.MinimumSpanningForest.sum_optDepth_le_optDepthMN`: Corollary 5.6 of
  [PettieRamachandran2002] (Section 5.1, p. 26).
* `Cslib.Query.MinimumSpanningForest.two_mul_optDepthMN_le`: Corollary 5.7 of
  [PettieRamachandran2002], `2 * optDepthMN m n ≤ optDepthMN (2 * m) (2 * n)`.
-/

public section

namespace Cslib.Query.MinimumSpanningForest

/-! ## Disjoint Edge Unions and Property 5.3 -/

/-- Disjoint union on the same vertex set `Fin n` of edge-indexed multigraphs `ends₁` and
`ends₂`. -/
@[expose] def edgeUnion {e₁ e₂ n : ℕ} (ends₁ : Fin e₁ → Sym2 (Fin n))
    (ends₂ : Fin e₂ → Sym2 (Fin n)) : Fin (e₁ + e₂) → Sym2 (Fin n) :=
  fun i => if h : i.val < e₁ then ends₁ ⟨i.val, h⟩ else ends₂ ⟨i.val - e₁, by omega⟩

theorem edgeUnion_castAdd {e₁ e₂ n : ℕ} (ends₁ : Fin e₁ → Sym2 (Fin n))
    (ends₂ : Fin e₂ → Sym2 (Fin n)) (i : Fin e₁) :
    edgeUnion ends₁ ends₂ (Fin.castAdd e₂ i) = ends₁ i := by
  dsimp only [edgeUnion]
  have h : (Fin.castAdd e₂ i).val < e₁ := i.isLt
  simp only [h, ↓reduceDIte]
  rfl

theorem edgeUnion_natAdd {e₁ e₂ n : ℕ} (ends₁ : Fin e₁ → Sym2 (Fin n))
    (ends₂ : Fin e₂ → Sym2 (Fin n)) (j : Fin e₂) :
    edgeUnion ends₁ ends₂ (Fin.natAdd e₁ j) = ends₂ j := by
  dsimp only [edgeUnion]
  have h : ¬ ((Fin.natAdd e₁ j).val < e₁) := by simp
  simp only [h, ↓reduceDIte]
  congr 1
  exact Fin.ext (by simp)

private def blockPerm {e₁ e₂ : ℕ} (p₁ : Equiv.Perm (Fin e₁)) (p₂ : Equiv.Perm (Fin e₂)) :
    Equiv.Perm (Fin (e₁ + e₂)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr p₁ p₂)).trans finSumFinEquiv

private theorem blockPerm_castAdd {e₁ e₂ : ℕ} (p₁ : Equiv.Perm (Fin e₁)) (p₂ : Equiv.Perm (Fin e₂))
    (i : Fin e₁) : blockPerm p₁ p₂ (Fin.castAdd e₂ i) = Fin.castAdd e₂ (p₁ i) := by
  dsimp only [blockPerm]
  simp only [Equiv.trans_apply]
  have h1 : finSumFinEquiv (Sum.inl i) = Fin.castAdd e₂ i := rfl
  rw [← h1, Equiv.symm_apply_apply]
  rfl

private theorem blockPerm_natAdd {e₁ e₂ : ℕ} (p₁ : Equiv.Perm (Fin e₁)) (p₂ : Equiv.Perm (Fin e₂))
    (j : Fin e₂) : blockPerm p₁ p₂ (Fin.natAdd e₁ j) = Fin.natAdd e₁ (p₂ j) := by
  dsimp only [blockPerm]
  simp only [Equiv.trans_apply]
  have h1 : finSumFinEquiv (Sum.inr j) = Fin.natAdd e₁ j := rfl
  rw [← h1, Equiv.symm_apply_apply]
  rfl

/-- Property 5.3 of [PettieRamachandran2002] for `(ends₁, ends₂)`: for every permutation on
`Fin (e₁ + e₂)`, `msf (edgeUnion ends₁ ends₂)` decomposes disjointly into the two component MSFs. -/
def MSFDecomposes {e₁ e₂ n : ℕ} (ends₁ : Fin e₁ → Sym2 (Fin n))
    (ends₂ : Fin e₂ → Sym2 (Fin n)) : Prop :=
  ∀ p : Equiv.Perm (Fin (e₁ + e₂)),
    Cslib.Multigraph.msf (edgeUnion ends₁ ends₂) p Finset.univ =
      (Cslib.Multigraph.msf ends₁ (fun i => p (Fin.castAdd e₂ i)) Finset.univ).map
          ⟨Fin.castAdd e₂, Fin.castAdd_injective _ _⟩ ∪
        (Cslib.Multigraph.msf ends₂ (fun j => p (Fin.natAdd e₁ j)) Finset.univ).map
          ⟨Fin.natAdd e₁, Fin.natAdd_injective _ _⟩

theorem msfDecomposes_iff {e₁ e₂ n : ℕ} (ends₁ : Fin e₁ → Sym2 (Fin n))
    (ends₂ : Fin e₂ → Sym2 (Fin n)) :
    MSFDecomposes ends₁ ends₂ ↔ ∀ p : Equiv.Perm (Fin (e₁ + e₂)),
      Cslib.Multigraph.msf (edgeUnion ends₁ ends₂) p Finset.univ =
        (Cslib.Multigraph.msf ends₁ (fun i => p (Fin.castAdd e₂ i)) Finset.univ).map
            ⟨Fin.castAdd e₂, Fin.castAdd_injective _ _⟩ ∪
          (Cslib.Multigraph.msf ends₂ (fun j => p (Fin.natAdd e₁ j)) Finset.univ).map
            ⟨Fin.natAdd e₁, Fin.natAdd_injective _ _⟩ :=
  Iff.rfl

private theorem joins_inter_eq {E V : Type*} (ends : E → Sym2 V)
    (E₁ E₂ S : Set E) (V₁ V₂ : Set V)
    (hcover : ∀ e ∈ S, e ∈ E₁ ∨ e ∈ E₂)
    (hV₁ : ∀ e ∈ E₁, ∀ a b, ends e = s(a, b) → a ∈ V₁ ∧ b ∈ V₁)
    (hV₂ : ∀ e ∈ E₂, ∀ a b, ends e = s(a, b) → a ∈ V₂ ∧ b ∈ V₂)
    (hinter : (V₁ ∩ V₂).Subsingleton)
    {u v : V} (hu : u ∈ V₁) (hv : v ∈ V₁) :
    Cslib.Multigraph.Joins ends S u v ↔ Cslib.Multigraph.Joins ends (S ∩ E₁) u v := by
  classical
  constructor
  · intro hc
    let z : V := if hne : (V₁ ∩ V₂).Nonempty then hne.some else u
    have hz_all : ∀ x ∈ V₂, x ∈ V₁ → x = z := fun x hx₂ hx₁ => by
      have hne : (V₁ ∩ V₂).Nonempty := ⟨x, hx₁, hx₂⟩
      dsimp only [z]
      rw [dite_eq_left_of_eq_true (eq_true hne)]
      exact hinter ⟨hx₁, hx₂⟩ hne.some_mem
    let proj : V → V := fun x => if x ∈ V₁ then x else z
    have hp_eq : ∀ x ∈ V₂, proj x = z := fun x hx₂ => by
      dsimp only [proj]
      split_ifs with hx₁
      · exact hz_all x hx₂ hx₁
      · rfl
    have hlift : Cslib.Multigraph.Joins ends (S ∩ E₁) (proj u) (proj v) := by
      refine Cslib.Multigraph.Joins.lift proj (fun e heS a b hab => ?_) hc
      rcases hcover e heS with he₁ | he₂
      · obtain ⟨ha, hb⟩ := hV₁ e he₁ a b hab
        simp only [proj, ha, hb, ↓reduceIte]
        exact Cslib.Multigraph.Joins.of_mem ⟨heS, he₁⟩ hab
      · obtain ⟨ha, hb⟩ := hV₂ e he₂ a b hab
        rw [hp_eq a ha, hp_eq b hb]
    simpa [proj, hu, hv] using hlift
  · exact Cslib.Multigraph.Joins.mono Set.inter_subset_left

private theorem joins_emb_iff {E₁ E₂ V : Type*} (ends₁ : E₁ → Sym2 V) (ends₂ : E₂ → Sym2 V)
    (ι : E₁ ↪ E₂) (hEnds : ∀ i : E₁, ends₂ (ι i) = ends₁ i)
    (V₁ V₂ : Set V)
    (hV₁ : ∀ i : E₁, ∀ a b : V, ends₁ i = s(a, b) → a ∈ V₁ ∧ b ∈ V₁)
    (hV₂ : ∀ e : E₂, e ∉ Set.range ι → ∀ a b : V, ends₂ e = s(a, b) → a ∈ V₂ ∧ b ∈ V₂)
    (hinter : (V₁ ∩ V₂).Subsingleton)
    (S : Set E₂) {u v : V} (hu : u ∈ V₁) (hv : v ∈ V₁) :
    Cslib.Multigraph.Joins ends₂ S u v ↔ Cslib.Multigraph.Joins ends₁ (ι ⁻¹' S) u v := by
  have h1 := joins_inter_eq ends₂ (Set.range ι) (Set.range ι)ᶜ S V₁ V₂
    (fun e _ => em (e ∈ Set.range ι))
    (fun e he a b hab => by
      obtain ⟨i, rfl⟩ := he
      exact hV₁ i a b (hEnds i ▸ hab))
    (fun e he a b hab => hV₂ e he a b hab)
    hinter hu hv
  rw [h1]
  constructor
  · intro hc
    refine Cslib.Multigraph.Joins.lift id (fun e he a b hab => ?_) hc
    obtain ⟨heS, i, rfl⟩ := he
    exact Cslib.Multigraph.Joins.of_mem heS (hEnds i ▸ hab)
  · intro hc
    refine Cslib.Multigraph.Joins.lift id (fun i hi a b hab => ?_) hc
    exact Cslib.Multigraph.Joins.of_mem ⟨hi, i, rfl⟩ (hab ▸ hEnds i)

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), Property 5.3 (§5.1, p. 25):
if vertex supports `V₁`, `V₂` share at most one vertex, then `MSFDecomposes ends₁ ends₂` holds. -/
theorem msfDecomposes_of_card_inter_le_one {e₁ e₂ n : ℕ}
    (ends₁ : Fin e₁ → Sym2 (Fin n)) (ends₂ : Fin e₂ → Sym2 (Fin n))
    (V₁ V₂ : Finset (Fin n))
    (hV₁ : ∀ i : Fin e₁, ∀ v ∈ ends₁ i, v ∈ V₁)
    (hV₂ : ∀ j : Fin e₂, ∀ v ∈ ends₂ j, v ∈ V₂)
    (hinter : (V₁ ∩ V₂).card ≤ 1) :
    MSFDecomposes ends₁ ends₂ := by
  rw [msfDecomposes_iff]
  intro p
  have hV₁' : ∀ i : Fin e₁, ∀ a b : Fin n, ends₁ i = s(a, b) →
      a ∈ (V₁ : Set (Fin n)) ∧ b ∈ (V₁ : Set (Fin n)) := fun i a b hab =>
    ⟨hV₁ i a (hab ▸ Sym2.mem_mk_left a b), hV₁ i b (hab ▸ Sym2.mem_mk_right a b)⟩
  have hV₂' : ∀ j : Fin e₂, ∀ a b : Fin n, ends₂ j = s(a, b) →
      a ∈ (V₂ : Set (Fin n)) ∧ b ∈ (V₂ : Set (Fin n)) := fun j a b hab =>
    ⟨hV₂ j a (hab ▸ Sym2.mem_mk_left a b), hV₂ j b (hab ▸ Sym2.mem_mk_right a b)⟩
  have hsub12 : ((V₁ : Set (Fin n)) ∩ (V₂ : Set (Fin n))).Subsingleton := fun x hx y hy =>
    Finset.card_le_one.mp hinter x (Finset.mem_inter.mpr hx) y (Finset.mem_inter.mpr hy)
  have hsub21 : ((V₂ : Set (Fin n)) ∩ (V₁ : Set (Fin n))).Subsingleton := by
    rw [Set.inter_comm]; exact hsub12
  let embL : Fin e₁ ↪ Fin (e₁ + e₂) := ⟨Fin.castAdd e₂, Fin.castAdd_injective _ _⟩
  let embR : Fin e₂ ↪ Fin (e₁ + e₂) := ⟨Fin.natAdd e₁, Fin.natAdd_injective _ _⟩
  have hnotL : ∀ e : Fin (e₁ + e₂), e ∉ Set.range embL → ∀ a b : Fin n,
      edgeUnion ends₁ ends₂ e = s(a, b) → a ∈ (V₂ : Set (Fin n)) ∧ b ∈ (V₂ : Set (Fin n)) := by
    intro e he a b hab
    have hge : ¬ (e.val < e₁) := fun h =>
      he ⟨⟨e.val, h⟩, Fin.ext rfl⟩
    let j : Fin e₂ := ⟨e.val - e₁, by omega⟩
    have hje : Fin.natAdd e₁ j = e := Fin.ext (by simp [j]; omega)
    have hend : edgeUnion ends₁ ends₂ e = ends₂ j := by
      rw [← hje, edgeUnion_natAdd]
    exact hV₂' j a b (hend ▸ hab)
  have hnotR : ∀ e : Fin (e₁ + e₂), e ∉ Set.range embR → ∀ a b : Fin n,
      edgeUnion ends₁ ends₂ e = s(a, b) → a ∈ (V₁ : Set (Fin n)) ∧ b ∈ (V₁ : Set (Fin n)) := by
    intro e he a b hab
    have hlt : e.val < e₁ := by
      by_contra hnot
      exact he ⟨⟨e.val - e₁, by omega⟩, Fin.ext (by simp [embR]; omega)⟩
    let i : Fin e₁ := ⟨e.val, hlt⟩
    have hie : Fin.castAdd e₂ i = e := Fin.ext rfl
    have hend : edgeUnion ends₁ ends₂ e = ends₁ i := by
      rw [← hie, edgeUnion_castAdd]
    exact hV₁' i a b (hend ▸ hab)
  ext e
  rw [Finset.mem_union, Finset.mem_map, Finset.mem_map]
  by_cases he : e.val < e₁
  · let i : Fin e₁ := ⟨e.val, he⟩
    have hie : Fin.castAdd e₂ i = e := Fin.ext rfl
    have he_ends : edgeUnion ends₁ ends₂ e = ends₁ i := by rw [← hie, edgeUnion_castAdd]
    induction hi : ends₁ i using Sym2.ind with
    | _ a b =>
      have hab : edgeUnion ends₁ ends₂ e = s(a, b) := he_ends.trans hi
      obtain ⟨ha, hb⟩ := hV₁' i a b hi
      have hconn_iff := joins_emb_iff ends₁ (edgeUnion ends₁ ends₂) embL
        (edgeUnion_castAdd ends₁ ends₂) (V₁ : Set (Fin n)) (V₂ : Set (Fin n))
        hV₁' hnotL hsub12 {f | f ∈ (Finset.univ : Finset (Fin (e₁ + e₂))) ∧ p f < p e} ha hb
      have hpre : embL ⁻¹' {f | f ∈ (Finset.univ : Finset (Fin (e₁ + e₂))) ∧ p f < p e} =
          {x | x ∈ (Finset.univ : Finset (Fin e₁)) ∧
            p (Fin.castAdd e₂ x) < p (Fin.castAdd e₂ i)} := by
        ext x
        simp [embL, hie]
      rw [hpre] at hconn_iff
      rw [Cslib.Multigraph.mem_msf_iff p hab]
      constructor
      · intro h
        refine .inl ⟨i, ?_, hie⟩
        rw [Cslib.Multigraph.mem_msf_iff (fun x => p (Fin.castAdd e₂ x)) hi]
        exact ⟨Finset.mem_univ _, fun hc => h.2 (hconn_iff.mpr hc)⟩
      · rintro (⟨x, hx, hxe⟩ | ⟨y, _, hye⟩)
        · have : x = i := Fin.castAdd_injective e₁ e₂ (hxe.trans hie.symm)
          subst this
          rw [Cslib.Multigraph.mem_msf_iff (fun y => p (Fin.castAdd e₂ y)) hi] at hx
          exact ⟨Finset.mem_univ _, fun hc => hx.2 (hconn_iff.mp hc)⟩
        · exfalso
          have : e.val = e₁ + y.val := congrArg Fin.val hye.symm
          omega
  · let j : Fin e₂ := ⟨e.val - e₁, by omega⟩
    have hje : Fin.natAdd e₁ j = e := Fin.ext (by simp [j]; omega)
    have he_ends : edgeUnion ends₁ ends₂ e = ends₂ j := by rw [← hje, edgeUnion_natAdd]
    induction hj : ends₂ j using Sym2.ind with
    | _ a b =>
      have hab : edgeUnion ends₁ ends₂ e = s(a, b) := he_ends.trans hj
      obtain ⟨ha, hb⟩ := hV₂' j a b hj
      have hconn_iff := joins_emb_iff ends₂ (edgeUnion ends₁ ends₂) embR
        (edgeUnion_natAdd ends₁ ends₂) (V₂ : Set (Fin n)) (V₁ : Set (Fin n))
        hV₂' hnotR hsub21 {f | f ∈ (Finset.univ : Finset (Fin (e₁ + e₂))) ∧ p f < p e} ha hb
      have hpre : embR ⁻¹' {f | f ∈ (Finset.univ : Finset (Fin (e₁ + e₂))) ∧ p f < p e} =
          {x | x ∈ (Finset.univ : Finset (Fin e₂)) ∧
            p (Fin.natAdd e₁ x) < p (Fin.natAdd e₁ j)} := by
        ext x
        simp [embR, hje]
      rw [hpre] at hconn_iff
      rw [Cslib.Multigraph.mem_msf_iff p hab]
      constructor
      · intro h
        refine .inr ⟨j, ?_, hje⟩
        rw [Cslib.Multigraph.mem_msf_iff (fun x => p (Fin.natAdd e₁ x)) hj]
        exact ⟨Finset.mem_univ _, fun hc => h.2 (hconn_iff.mpr hc)⟩
      · rintro (⟨x, _, hxe⟩ | ⟨y, hy, hye⟩)
        · exfalso
          have : x.val = e.val := congrArg Fin.val hxe
          omega
        · have : y = j := Fin.ext (by
            have := congrArg Fin.val (hye.trans hje.symm); simp at this; omega)
          subst this
          rw [Cslib.Multigraph.mem_msf_iff (fun x => p (Fin.natAdd e₁ x)) hj] at hy
          exact ⟨Finset.mem_univ _, fun hc => hy.2 (hconn_iff.mp hc)⟩

/-! ## Intra-Block Pruning, Adversary Lower Bound, and Grafting -/

/-- Prune inter-component comparisons on block-ordered permutations
([PettieRamachandran2002], Lemma 5.4). -/
def MSFTree.restrictBlock (e₁ e₂ : ℕ) {α : Type} :
    MSFTree (e₁ + e₂) α → MSFTree (e₁ + e₂) α
  | .leaf a => .leaf a
  | .node i j l r =>
    if i.val < e₁ ∧ e₁ ≤ j.val then l.restrictBlock e₁ e₂
    else if e₁ ≤ i.val ∧ j.val < e₁ then r.restrictBlock e₁ e₂
    else .node i j (l.restrictBlock e₁ e₂) (r.restrictBlock e₁ e₂)

/-- Predicate asserting all internal comparisons stay within block `[0, e₁)` or `[e₁, e₁ + e₂)`. -/
def MSFTree.IsIntraBlock (e₁ e₂ : ℕ) {α : Type} : MSFTree (e₁ + e₂) α → Prop
  | .leaf _ => True
  | .node i j l r =>
    ((i.val < e₁ ∧ j.val < e₁) ∨ (e₁ ≤ i.val ∧ e₁ ≤ j.val)) ∧
      l.IsIntraBlock e₁ e₂ ∧ r.IsIntraBlock e₁ e₂

theorem MSFTree.restrictBlock_isIntraBlock {e₁ e₂ : ℕ} {α : Type} (T : MSFTree (e₁ + e₂) α) :
    (T.restrictBlock e₁ e₂).IsIntraBlock e₁ e₂ := by
  induction T with
  | leaf _ => trivial
  | node i j l r ihl ihr =>
    dsimp only [MSFTree.restrictBlock]
    split_ifs with h1 h2
    · exact ihl
    · exact ihr
    · refine ⟨?_, ihl, ihr⟩
      by_cases hi : i.val < e₁ <;> by_cases hj : j.val < e₁
      · exact .inl ⟨hi, hj⟩
      · exfalso; exact h1 ⟨hi, Nat.le_of_not_lt hj⟩
      · exfalso; exact h2 ⟨Nat.le_of_not_lt hi, hj⟩
      · exact .inr ⟨Nat.le_of_not_lt hi, Nat.le_of_not_lt hj⟩

theorem MSFTree.restrictBlock_depth_le {e₁ e₂ : ℕ} {α : Type} (T : MSFTree (e₁ + e₂) α) :
    (T.restrictBlock e₁ e₂).depth ≤ T.depth := by
  induction T with
  | leaf _ => rfl
  | node i j l r ihl ihr =>
    dsimp only [MSFTree.restrictBlock, MSFTree.depth]
    split_ifs
    · omega
    · omega
    · dsimp only [MSFTree.depth]; omega

private theorem blockPerm_val_lt {e₁ e₂ : ℕ} (p₁ : Equiv.Perm (Fin e₁))
    (p₂ : Equiv.Perm (Fin e₂)) {i j : Fin (e₁ + e₂)} (hi : i.val < e₁) (hj : e₁ ≤ j.val) :
    (blockPerm p₁ p₂ i).val < (blockPerm p₁ p₂ j).val := by
  have hie : Fin.castAdd e₂ ⟨i.val, hi⟩ = i := Fin.ext rfl
  have hje : Fin.natAdd e₁ ⟨j.val - e₁, by omega⟩ = j := Fin.ext (by simp; omega)
  rw [← hie, ← hje, blockPerm_castAdd, blockPerm_natAdd]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  exact Nat.lt_of_lt_of_le (p₁ _).isLt (Nat.le_add_right _ _)

private theorem MSFTree.restrictBlock_eval {e₁ e₂ : ℕ} {α : Type} (T : MSFTree (e₁ + e₂) α)
    (p₁ : Equiv.Perm (Fin e₁)) (p₂ : Equiv.Perm (Fin e₂)) :
    (T.restrictBlock e₁ e₂).eval (blockPerm p₁ p₂) = T.eval (blockPerm p₁ p₂) := by
  induction T with
  | leaf _ => rfl
  | node i j l r ihl ihr =>
    dsimp only [MSFTree.restrictBlock]
    split_ifs with h1 h2
    · have hlt := blockPerm_val_lt p₁ p₂ h1.1 h1.2
      simp only [MSFTree.eval, hlt, ↓reduceIte]
      exact ihl
    · have hnlt := not_lt_of_gt (blockPerm_val_lt p₁ p₂ h2.2 h2.1)
      simp only [MSFTree.eval, hnlt, ↓reduceIte]
      exact ihr
    · dsimp only [MSFTree.eval]
      split_ifs <;> assumption

theorem MSFTree.IsIntraBlock.mapLeaves {e₁ e₂ : ℕ} {α β : Type} {f : α → β} :
    ∀ {T : MSFTree (e₁ + e₂) α}, T.IsIntraBlock e₁ e₂ →
      (T.mapLeaves f).IsIntraBlock e₁ e₂
  | .leaf _, _ => trivial
  | .node _ _ _ _, ⟨hblk, hl, hr⟩ => ⟨hblk, hl.mapLeaves, hr.mapLeaves⟩

private theorem adversary_branch {eQ : ℕ} {αQ : Type} {fQ : Equiv.Perm (Fin eQ) → αQ}
    {Q : Finset (Equiv.Perm (Fin eQ))} (hQ : Q.Nonempty) (i' j' : Fin eQ) {other dL dR : ℕ}
    (hL_rec : ∀ P' : Finset (Equiv.Perm (Fin eQ)), P'.Nonempty → P' ⊆ Q →
      (∀ p ∈ P', (p i').val < (p j').val) → optDepthOn fQ P' + other ≤ dL)
    (hR_rec : ∀ P' : Finset (Equiv.Perm (Fin eQ)), P'.Nonempty → P' ⊆ Q →
      (∀ p ∈ P', ¬ ((p i').val < (p j').val)) → optDepthOn fQ P' + other ≤ dR) :
    optDepthOn fQ Q + other ≤ 1 + max dL dR := by
  let PL := Q.filter fun p => decide ((p i').val < (p j').val)
  let PR := Q.filter fun p => !decide ((p i').val < (p j').val)
  by_cases hL : PL.Nonempty
  · by_cases hR : PR.Nonempty
    · have hrecL := hL_rec PL hL (Finset.filter_subset _ _) fun p hp =>
        of_decide_eq_true (Finset.mem_filter.mp hp).2
      have hrecR := hR_rec PR hR (Finset.filter_subset _ _) fun p hp => by
        simpa using (Finset.mem_filter.mp hp).2
      obtain ⟨TL, hAgL, hdL⟩ := exists_opt_msfTree fQ PL
      obtain ⟨TR, hAgR, hdR⟩ := exists_opt_msfTree fQ PR
      rw [MSFTree.agreesOn_iff] at hAgL hAgR
      let Tq : MSFTree eQ αQ := .node i' j' TL TR
      have hAgQ : Tq.AgreesOn fQ Q := (MSFTree.agreesOn_iff _ _ _).mpr fun p hp => by
        dsimp only [Tq, MSFTree.eval]
        split_ifs with hlt
        · exact hAgL p (Finset.mem_filter.mpr ⟨hp, decide_eq_true hlt⟩)
        · exact hAgR p (Finset.mem_filter.mpr ⟨hp, by simp [hlt]⟩)
      have hoptQ : optDepthOn fQ Q ≤ 1 + max (optDepthOn fQ PL) (optDepthOn fQ PR) := by
        have := optDepthOn_le_of_agrees hAgQ
        dsimp only [Tq, MSFTree.depth] at this
        rw [hdL, hdR] at this
        exact this
      omega
    · have hsub : ∀ p ∈ Q, (p i').val < (p j').val := fun p hp => by
        by_contra hnot
        exact hR ⟨p, Finset.mem_filter.mpr ⟨hp, by simp [hnot]⟩⟩
      have hrecL := hL_rec Q hQ Finset.Subset.rfl hsub
      omega
  · by_cases hR : PR.Nonempty
    · have hsub : ∀ p ∈ Q, ¬ ((p i').val < (p j').val) := fun p hp hlt =>
        hL ⟨p, Finset.mem_filter.mpr ⟨hp, decide_eq_true hlt⟩⟩
      have hrecR := hR_rec Q hQ Finset.Subset.rfl hsub
      omega
    · obtain ⟨pStar, hpStar⟩ := hQ
      by_cases hlt : (pStar i').val < (pStar j').val
      · exact absurd ⟨pStar, Finset.mem_filter.mpr ⟨hpStar, decide_eq_true hlt⟩⟩ hL
      · exact absurd ⟨pStar, Finset.mem_filter.mpr ⟨hpStar, by simp [hlt]⟩⟩ hR

private theorem adversary_pair {e₁ e₂ : ℕ} {α₁ α₂ : Type}
    (f₁ : Equiv.Perm (Fin e₁) → α₁) (f₂ : Equiv.Perm (Fin e₂) → α₂)
    (T : MSFTree (e₁ + e₂) (α₁ × α₂)) (hintra : T.IsIntraBlock e₁ e₂)
    {P₁ : Finset (Equiv.Perm (Fin e₁))} {P₂ : Finset (Equiv.Perm (Fin e₂))}
    (hP₁ : P₁.Nonempty) (hP₂ : P₂.Nonempty)
    (hAg : ∀ p₁ ∈ P₁, ∀ p₂ ∈ P₂, T.eval (blockPerm p₁ p₂) = (f₁ p₁, f₂ p₂)) :
    optDepthOn f₁ P₁ + optDepthOn f₂ P₂ ≤ T.depth := by
  induction T generalizing P₁ P₂ with
  | leaf ans =>
    obtain ⟨p₂Star, hp₂Star⟩ := hP₂
    obtain ⟨p₁Star, hp₁Star⟩ := hP₁
    have ha₁ : (MSFTree.leaf ans.1 : MSFTree e₁ α₁).AgreesOn f₁ P₁ :=
      (MSFTree.agreesOn_iff _ _ _).mpr fun p₁ hp₁ => by
      have h := congrArg Prod.fst (hAg p₁ hp₁ p₂Star hp₂Star)
      simpa [MSFTree.eval] using h
    have ha₂ : (MSFTree.leaf ans.2 : MSFTree e₂ α₂).AgreesOn f₂ P₂ :=
      (MSFTree.agreesOn_iff _ _ _).mpr fun p₂ hp₂ => by
      have h := congrArg Prod.snd (hAg p₁Star hp₁Star p₂ hp₂)
      simpa [MSFTree.eval] using h
    have h1 : optDepthOn f₁ P₁ ≤ 0 := optDepthOn_le_of_agrees ha₁
    have h2 : optDepthOn f₂ P₂ ≤ 0 := optDepthOn_le_of_agrees ha₂
    dsimp only [MSFTree.depth]
    omega
  | node i j l r ihl ihr =>
    obtain ⟨hblk, hl, hr⟩ := hintra
    dsimp only [MSFTree.depth]
    rcases hblk with ⟨hi1, hj1⟩ | ⟨hi2, hj2⟩
    · let i' : Fin e₁ := ⟨i.val, hi1⟩
      let j' : Fin e₁ := ⟨j.val, hj1⟩
      have hbr : ∀ (p₁ : Equiv.Perm (Fin e₁)) (p₂ : Equiv.Perm (Fin e₂)),
          (blockPerm p₁ p₂ i).val < (blockPerm p₁ p₂ j).val ↔ (p₁ i').val < (p₁ j').val := by
        intro p₁ p₂
        have hie : Fin.castAdd e₂ i' = i := Fin.ext rfl
        have hje : Fin.castAdd e₂ j' = j := Fin.ext rfl
        rw [← hie, ← hje, blockPerm_castAdd, blockPerm_castAdd]
        simp
      exact adversary_branch hP₁ i' j'
        (fun P' hP' hsub hlt => ihl hl hP' hP₂ fun p₁ hp₁ p₂ hp₂ => by
          have h := hAg p₁ (hsub hp₁) p₂ hp₂
          have hcmp : (blockPerm p₁ p₂ i).val < (blockPerm p₁ p₂ j).val :=
            (hbr p₁ p₂).mpr (hlt p₁ hp₁)
          simpa [MSFTree.eval, hcmp] using h)
        (fun P' hP' hsub hge => ihr hr hP' hP₂ fun p₁ hp₁ p₂ hp₂ => by
          have h := hAg p₁ (hsub hp₁) p₂ hp₂
          have hcmp : ¬ ((blockPerm p₁ p₂ i).val < (blockPerm p₁ p₂ j).val) :=
            fun x => hge p₁ hp₁ ((hbr p₁ p₂).mp x)
          simpa [MSFTree.eval, hcmp] using h)
    · let i' : Fin e₂ := ⟨i.val - e₁, by omega⟩
      let j' : Fin e₂ := ⟨j.val - e₁, by omega⟩
      have hbr : ∀ (p₁ : Equiv.Perm (Fin e₁)) (p₂ : Equiv.Perm (Fin e₂)),
          (blockPerm p₁ p₂ i).val < (blockPerm p₁ p₂ j).val ↔ (p₂ i').val < (p₂ j').val := by
        intro p₁ p₂
        have hie : Fin.natAdd e₁ i' = i := Fin.ext (by simp [i']; omega)
        have hje : Fin.natAdd e₁ j' = j := Fin.ext (by simp [j']; omega)
        rw [← hie, ← hje, blockPerm_natAdd, blockPerm_natAdd]
        simp
      rw [Nat.add_comm]
      exact adversary_branch hP₂ i' j'
        (fun P' hP' hsub hlt => by
          rw [Nat.add_comm]
          exact ihl hl hP₁ hP' fun p₁ hp₁ p₂ hp₂ => by
            have h := hAg p₁ hp₁ p₂ (hsub hp₂)
            have hcmp : (blockPerm p₁ p₂ i).val < (blockPerm p₁ p₂ j).val :=
              (hbr p₁ p₂).mpr (hlt p₂ hp₂)
            simpa [MSFTree.eval, hcmp] using h)
        (fun P' hP' hsub hge => by
          rw [Nat.add_comm]
          exact ihr hr hP₁ hP' fun p₁ hp₁ p₂ hp₂ => by
            have h := hAg p₁ hp₁ p₂ (hsub hp₂)
            have hcmp : ¬ ((blockPerm p₁ p₂ i).val < (blockPerm p₁ p₂ j).val) :=
              fun x => hge p₂ hp₂ ((hbr p₁ p₂).mp x)
            simpa [MSFTree.eval, hcmp] using h)

/-- Compose sequential decision trees for two components by grafting `T₂` onto every leaf of
`T₁`. -/
def graftTree {e₁ e₂ : ℕ} (T₁ : MSFDT e₁) (T₂ : MSFDT e₂) : MSFDT (e₁ + e₂) :=
  match T₁ with
  | .leaf A =>
    (T₂.mapLeaves fun B =>
      A.map ⟨Fin.castAdd e₂, Fin.castAdd_injective _ _⟩ ∪
        B.map ⟨Fin.natAdd e₁, Fin.natAdd_injective _ _⟩).liftEmb (Fin.natAdd e₁)
  | .node i j l r =>
    .node (Fin.castAdd e₂ i) (Fin.castAdd e₂ j) (graftTree l T₂) (graftTree r T₂)

theorem graftTree_depth_le {e₁ e₂ : ℕ} (T₁ : MSFDT e₁) (T₂ : MSFDT e₂) :
    (graftTree T₁ T₂).depth ≤ T₁.depth + T₂.depth := by
  induction T₁ with
  | leaf A => simp [graftTree, MSFTree.depth]
  | node i j l r ihl ihr =>
    simp only [graftTree, MSFTree.depth]
    omega

theorem graftTree_eval {e₁ e₂ : ℕ} (T₁ : MSFDT e₁) (T₂ : MSFDT e₂)
    (p : Equiv.Perm (Fin (e₁ + e₂))) :
    (graftTree T₁ T₂).eval p =
      (T₁.eval (orderPerm (fun i => p (Fin.castAdd e₂ i))
          (p.injective.comp (Fin.castAdd_injective _ _)))).map
          ⟨Fin.castAdd e₂, Fin.castAdd_injective _ _⟩ ∪
        (T₂.eval (orderPerm (fun j => p (Fin.natAdd e₁ j))
          (p.injective.comp (Fin.natAdd_injective _ _)))).map
          ⟨Fin.natAdd e₁, Fin.natAdd_injective _ _⟩ := by
  let p₁ := orderPerm (fun i => p (Fin.castAdd e₂ i))
    (p.injective.comp (Fin.castAdd_injective _ _))
  let p₂ := orderPerm (fun j => p (Fin.natAdd e₁ j))
    (p.injective.comp (Fin.natAdd_injective _ _))
  have hord₁ : ∀ a b : Fin e₁, (p₁ a).val < (p₁ b).val ↔
      (p (Fin.castAdd e₂ a)).val < (p (Fin.castAdd e₂ b)).val := fun a b =>
    orderPerm_lt_iff _ _ a b
  have hord₂ : ∀ a b : Fin e₂, (p₂ a).val < (p₂ b).val ↔
      (p (Fin.natAdd e₁ a)).val < (p (Fin.natAdd e₁ b)).val := fun a b =>
    orderPerm_lt_iff _ _ a b
  induction T₁ with
  | leaf A =>
    dsimp only [graftTree]
    rw [MSFTree.liftEmb_eval (Fin.natAdd e₁) _ p₂ p hord₂, MSFTree.mapLeaves_eval]
    rfl
  | node i j l r ihl ihr =>
    dsimp only [graftTree, MSFTree.eval]
    have h := hord₁ i j
    dsimp only [p₁] at h
    by_cases hlt :
        (orderPerm (fun i => p (Fin.castAdd e₂ i))
          (p.injective.comp (Fin.castAdd_injective _ _)) i).val <
        (orderPerm (fun i => p (Fin.castAdd e₂ i))
          (p.injective.comp (Fin.castAdd_injective _ _)) j).val
    · have hlt' : (p (Fin.castAdd e₂ i)).val < (p (Fin.castAdd e₂ j)).val := h.mp hlt
      simp only [hlt, hlt', ↓reduceIte]
      exact ihl
    · have hlt' : ¬ ((p (Fin.castAdd e₂ i)).val < (p (Fin.castAdd e₂ j)).val) :=
        fun x => hlt (h.mpr x)
      simp only [hlt, hlt', ↓reduceIte]
      exact ihr

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), Lemma 5.5 (§5.1, p. 26):
binary additivity `T*(G₁ ∪ G₂) = T*(G₁) + T*(G₂)` under Property 5.3 (`MSFDecomposes`). -/
theorem optDepth_edgeUnion_eq_add {e₁ e₂ n : ℕ} (ends₁ : Fin e₁ → Sym2 (Fin n))
    (ends₂ : Fin e₂ → Sym2 (Fin n)) (h53 : MSFDecomposes ends₁ ends₂) :
    optDepth (edgeUnion ends₁ ends₂) = optDepth ends₁ + optDepth ends₂ := by
  classical
  have hlb : optDepth ends₁ + optDepth ends₂ ≤ optDepth (edgeUnion ends₁ ends₂) := by
    obtain ⟨T, hcorr, hd⟩ := exists_opt_msfDT (edgeUnion ends₁ ends₂)
    rw [MSFDT.correct_iff] at hcorr
    let splitF : Finset (Fin (e₁ + e₂)) → Finset (Fin e₁) × Finset (Fin e₂) := fun S =>
      (S.preimage (Fin.castAdd e₂) (Fin.castAdd_injective _ _).injOn,
       S.preimage (Fin.natAdd e₁) (Fin.natAdd_injective _ _).injOn)
    let Tr := (T.restrictBlock e₁ e₂).mapLeaves splitF
    have hAg : ∀ p₁ ∈ (Finset.univ : Finset (Equiv.Perm (Fin e₁))),
        ∀ p₂ ∈ (Finset.univ : Finset (Equiv.Perm (Fin e₂))),
        Tr.eval (blockPerm p₁ p₂) =
          (Cslib.Multigraph.msf ends₁ p₁ Finset.univ,
           Cslib.Multigraph.msf ends₂ p₂ Finset.univ) := by
      intro p₁ _ p₂ _
      dsimp only [Tr]
      rw [MSFTree.mapLeaves_eval, MSFTree.restrictBlock_eval, hcorr (blockPerm p₁ p₂),
        (msfDecomposes_iff _ _).mp h53 (blockPerm p₁ p₂)]
      have hm₁ : Cslib.Multigraph.msf ends₁
          (fun i => blockPerm p₁ p₂ (Fin.castAdd e₂ i)) Finset.univ =
          Cslib.Multigraph.msf ends₁ p₁ Finset.univ :=
        msf_congr_lt ends₁ _ p₁ Finset.univ fun a b => by
          simp only [blockPerm_castAdd, Fin.lt_def, Fin.val_castAdd]
      have hm₂ : Cslib.Multigraph.msf ends₂
          (fun j => blockPerm p₁ p₂ (Fin.natAdd e₁ j)) Finset.univ =
          Cslib.Multigraph.msf ends₂ p₂ Finset.univ :=
        msf_congr_lt ends₂ _ p₂ Finset.univ fun a b => by
          simp only [blockPerm_natAdd, Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left]
      rw [hm₁, hm₂]
      dsimp only [splitF]
      ext1 <;> ext x <;> simp only [Finset.mem_preimage, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      · constructor
        · rintro (⟨a, ha, hae⟩ | ⟨b, _, hbe⟩)
          · rwa [Fin.castAdd_injective e₁ e₂ hae] at ha
          · exfalso; have : (e₁ + b.val) = x.val := congrArg Fin.val hbe; omega
        · intro hx
          exact .inl ⟨x, hx, rfl⟩
      · constructor
        · rintro (⟨a, _, hae⟩ | ⟨b, hb, hbe⟩)
          · exfalso; have : a.val = e₁ + x.val := congrArg Fin.val hae; omega
          · have hbx : b = x := Fin.ext (by
              have := congrArg Fin.val hbe; simp at this; omega)
            rwa [hbx] at hb
        · intro hx
          exact .inr ⟨x, hx, rfl⟩
    have hintra : Tr.IsIntraBlock e₁ e₂ := (T.restrictBlock_isIntraBlock).mapLeaves
    have hadv := adversary_pair
      (fun p => Cslib.Multigraph.msf ends₁ p Finset.univ)
      (fun p => Cslib.Multigraph.msf ends₂ p Finset.univ) Tr hintra
      Finset.univ_nonempty Finset.univ_nonempty hAg
    have hdepth : Tr.depth ≤ optDepth (edgeUnion ends₁ ends₂) := by
      dsimp only [Tr]
      rw [MSFTree.mapLeaves_depth]
      exact (T.restrictBlock_depth_le).trans hd.le
    rw [optDepth_eq_optDepthOn ends₁, optDepth_eq_optDepthOn ends₂]
    exact hadv.trans hdepth
  have hub : optDepth (edgeUnion ends₁ ends₂) ≤ optDepth ends₁ + optDepth ends₂ := by
    obtain ⟨T₁, hcorr₁, hd₁⟩ := exists_opt_msfDT ends₁
    obtain ⟨T₂, hcorr₂, hd₂⟩ := exists_opt_msfDT ends₂
    rw [MSFDT.correct_iff] at hcorr₁ hcorr₂
    let Tg := graftTree T₁ T₂
    have hcorr : MSFDT.Correct (edgeUnion ends₁ ends₂) Tg :=
        (MSFDT.correct_iff _ _).mpr fun p => by
      dsimp only [Tg]
      rw [graftTree_eval, hcorr₁ _, hcorr₂ _, (msfDecomposes_iff _ _).mp h53 p]
      have hm₁ : Cslib.Multigraph.msf ends₁
          (orderPerm (fun i => p (Fin.castAdd e₂ i))
            (p.injective.comp (Fin.castAdd_injective _ _))) Finset.univ =
          Cslib.Multigraph.msf ends₁ (fun i => p (Fin.castAdd e₂ i)) Finset.univ :=
        msf_congr_lt ends₁ _ _ Finset.univ fun a b => orderPerm_lt_iff _ _ a b
      have hm₂ : Cslib.Multigraph.msf ends₂
          (orderPerm (fun j => p (Fin.natAdd e₁ j))
            (p.injective.comp (Fin.natAdd_injective _ _))) Finset.univ =
          Cslib.Multigraph.msf ends₂ (fun j => p (Fin.natAdd e₁ j)) Finset.univ :=
        msf_congr_lt ends₂ _ _ Finset.univ fun a b => orderPerm_lt_iff _ _ a b
      rw [hm₁, hm₂]
    exact (optDepth_le_of_correct hcorr).trans ((graftTree_depth_le T₁ T₂).trans (by omega))
  exact le_antisymm hub hlb

/-! ## List Decomposition, Lemma 5.5, Corollary 5.6, and Corollary 5.7 -/

/-- Total edge count across a list of component subgraphs (definitionally recursive on `cons`). -/
abbrev edgeCountList {n : ℕ} : List (Σ e, Fin e → Sym2 (Fin n)) → ℕ
  | [] => 0
  | c :: rest => c.1 + edgeCountList rest

theorem edgeCountList_eq_sum {n : ℕ} (Cs : List (Σ e, Fin e → Sym2 (Fin n))) :
    edgeCountList Cs = (Cs.map Sigma.fst).sum := by
  induction Cs with
  | nil => rfl
  | cons c rest ih => simp [edgeCountList, ih]

/-- Disjoint edge union of a list of edge-indexed subgraphs on common vertex set `Fin n`. -/
@[expose] def edgeUnionList {n : ℕ} :
    (Cs : List (Σ e, Fin e → Sym2 (Fin n))) → Fin (edgeCountList Cs) → Sym2 (Fin n)
  | [] => Fin.elim0
  | ⟨_, ends₁⟩ :: rest => edgeUnion ends₁ (edgeUnionList rest)

/-- Vertex support of an edge-indexed multigraph `ends : Fin e → Sym2 (Fin n)`. -/
@[expose] def compVerts {e n : ℕ} (ends : Fin e → Sym2 (Fin n)) : Finset (Fin n) :=
  Finset.univ.biUnion fun i => (ends i).toFinset

theorem ends_mem_compVerts {e n : ℕ} (ends : Fin e → Sym2 (Fin n)) (i : Fin e) :
    ∀ v ∈ ends i, v ∈ compVerts ends := fun v hv => by
  simp only [compVerts, Finset.mem_biUnion, Finset.mem_univ, Sym2.mem_toFinset, true_and]
  exact ⟨i, hv⟩

/-- Cumulative vertex support across a list of component subgraphs on `Fin n`. -/
@[expose] def compVertsList {n : ℕ} : List (Σ e, Fin e → Sym2 (Fin n)) → Finset (Fin n)
  | [] => ∅
  | c :: rest => compVerts c.2 ∪ compVertsList rest

theorem edgeUnionList_ends_mem_compVertsList {n : ℕ}
    (Cs : List (Σ e, Fin e → Sym2 (Fin n))) (i : Fin (edgeCountList Cs)) :
    ∀ v ∈ edgeUnionList Cs i, v ∈ compVertsList Cs := by
  induction Cs with
  | nil => exact Fin.elim0 i
  | cons c rest ih =>
    rcases c with ⟨e₁, ends₁⟩
    intro v hv
    dsimp only [edgeUnionList, compVertsList] at hv ⊢
    by_cases h : i.val < e₁
    · let j : Fin e₁ := ⟨i.val, h⟩
      have hje : Fin.castAdd (edgeCountList rest) j = i := Fin.ext rfl
      have he : edgeUnion ends₁ (edgeUnionList rest) i = ends₁ j := by
        rw [← hje, edgeUnion_castAdd]
      rw [he] at hv
      exact Finset.mem_union_left _ (ends_mem_compVerts ends₁ j v hv)
    · have hi_lt : i.val < e₁ + edgeCountList rest := i.isLt
      let j : Fin (edgeCountList rest) := ⟨i.val - e₁, by omega⟩
      have hje : Fin.natAdd e₁ j = i := Fin.ext (by simp [j]; omega)
      have he : edgeUnion ends₁ (edgeUnionList rest) i = edgeUnionList rest j := by
        rw [← hje, edgeUnion_natAdd]
      rw [he] at hv
      exact Finset.mem_union_right _ (ih j v hv)

/-- Valid sequential Partition decomposition (Property 5.3 hypothesis of [PettieRamachandran2002]
in `cons` order): every component shares at most one vertex with the union of the rest. -/
def ValidDecomp {n : ℕ} : List (Σ e, Fin e → Sym2 (Fin n)) → Prop
  | [] => True
  | c :: rest => (compVerts c.2 ∩ compVertsList rest).card ≤ 1 ∧ ValidDecomp rest

@[simp]
theorem validDecomp_nil {n : ℕ} : ValidDecomp ([] : List (Σ e, Fin e → Sym2 (Fin n))) := trivial

theorem validDecomp_cons {n : ℕ} (c : Σ e, Fin e → Sym2 (Fin n))
    (rest : List (Σ e, Fin e → Sym2 (Fin n))) :
    ValidDecomp (c :: rest) ↔ (compVerts c.2 ∩ compVertsList rest).card ≤ 1 ∧ ValidDecomp rest :=
  Iff.rfl

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), Lemma 5.5 (§5.1, p. 26):
for any valid Property 5.3 decomposition `Cs`,
`optDepth (edgeUnionList Cs) = ∑ c ∈ Cs, optDepth c.2`. -/
theorem optDepth_edgeUnionList_eq_sum {n : ℕ}
    (Cs : List (Σ e, Fin e → Sym2 (Fin n))) (h : ValidDecomp Cs) :
    optDepth (edgeUnionList Cs) = (Cs.map fun c => optDepth c.2).sum := by
  induction Cs with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact optDepth_eq_zero_of_le_one (Nat.zero_le 1) (edgeUnionList [])
  | cons c rest ih =>
    obtain ⟨hinter, hrest⟩ := (validDecomp_cons c rest).mp h
    rcases c with ⟨e₁, ends₁⟩
    dsimp only [edgeUnionList, List.map_cons, List.sum_cons]
    have h53 : MSFDecomposes ends₁ (edgeUnionList rest) :=
      msfDecomposes_of_card_inter_le_one ends₁ (edgeUnionList rest)
        (compVerts ends₁) (compVertsList rest) (ends_mem_compVerts ends₁)
        (edgeUnionList_ends_mem_compVertsList rest) hinter
    have hadd : optDepth (edgeUnion ends₁ (edgeUnionList rest)) =
        optDepth ends₁ + optDepth (edgeUnionList rest) :=
      optDepth_edgeUnion_eq_add ends₁ (edgeUnionList rest) h53
    rw [hadd, ih hrest, List.map_cons, List.sum_cons]

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), Corollary 5.6 (§5.1, p. 26):
if `Cs` is a valid Property 5.3 decomposition whose union `edgeUnionList Cs` is simple and has at
most `m` edges on `n` vertices, then `(Cs.map fun c => optDepth c.2).sum ≤ optDepthMN m n`. -/
theorem sum_optDepth_le_optDepthMN {m n : ℕ} (Cs : List (Σ e, Fin e → Sym2 (Fin n)))
    (hV : ValidDecomp Cs) (hsimp : IsSimple (edgeUnionList Cs))
    (hm : (Cs.map Sigma.fst).sum ≤ m) :
    (Cs.map fun c => optDepth c.2).sum ≤ optDepthMN m n := by
  rw [← optDepth_edgeUnionList_eq_sum Cs hV]
  rw [← edgeCountList_eq_sum] at hm
  exact optDepth_le_optDepthMN_of_isSimple (edgeUnionList Cs) hsimp hm

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), Corollary 5.7 (§5.1, p. 26):
`2 * optDepthMN m n ≤ optDepthMN (2 * m) (2 * n)`. -/
theorem two_mul_optDepthMN_le (m n : ℕ) : 2 * optDepthMN m n ≤ optDepthMN (2 * m) (2 * n) := by
  obtain ⟨mask, hmask, hlen, heq⟩ := exists_endsOfMask_eq_optDepthMN m n
  let G := endsOfMask n mask
  let e := (maskEdgePairs n mask).length
  let castN : Fin n ↪ Fin (2 * n) :=
    ⟨fun x => ⟨x.val, by omega⟩, fun _ _ h => Fin.ext (congrArg (Fin.val : Fin (2 * n) → ℕ) h)⟩
  let shiftN : Fin n ↪ Fin (2 * n) :=
    ⟨fun x => ⟨n + x.val, by omega⟩, fun _ _ h =>
      Fin.ext (by have := congrArg (Fin.val : Fin (2 * n) → ℕ) h; dsimp only at this; omega)⟩
  let C₁ : Fin e → Sym2 (Fin (2 * n)) := fun i => Sym2.map castN (G i)
  let C₂ : Fin e → Sym2 (Fin (2 * n)) := fun i => Sym2.map shiftN (G i)
  have hG_simp := (isSimple_iff _).mp (endsOfMask_isSimple n mask)
  have hopt₁ : optDepth G = optDepth C₁ :=
    optDepth_reindex G C₁ (Equiv.refl _) castN fun _ => rfl
  have hopt₂ : optDepth G = optDepth C₂ :=
    optDepth_reindex G C₂ (Equiv.refl _) shiftN fun _ => rfl
  let V₁ : Finset (Fin (2 * n)) := Finset.univ.map castN
  let V₂ : Finset (Fin (2 * n)) := Finset.univ.map shiftN
  have hV₁ : ∀ i : Fin e, ∀ v ∈ C₁ i, v ∈ V₁ := fun i v hv => by
    dsimp only [C₁, V₁] at hv ⊢
    rcases Sym2.mem_map.mp hv with ⟨w, _, rfl⟩
    exact Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩
  have hV₂ : ∀ j : Fin e, ∀ v ∈ C₂ j, v ∈ V₂ := fun j v hv => by
    dsimp only [C₂, V₂] at hv ⊢
    rcases Sym2.mem_map.mp hv with ⟨w, _, rfl⟩
    exact Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩
  have hinter : (V₁ ∩ V₂).card ≤ 1 := by
    have hemp : V₁ ∩ V₂ = ∅ := by
      dsimp only [V₁, V₂]
      ext v
      simp only [Finset.mem_inter, Finset.mem_map, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false, not_and]
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha' : a.val = v.val := congrArg Fin.val ha
      have hb' : n + b.val = v.val := congrArg Fin.val hb
      have := a.isLt
      omega
    rw [hemp, Finset.card_empty]
    omega
  have h53 : MSFDecomposes C₁ C₂ :=
    msfDecomposes_of_card_inter_le_one C₁ C₂ V₁ V₂ hV₁ hV₂ hinter
  have hu_simp : IsSimple (edgeUnion C₁ C₂) := by
    rw [isSimple_iff]
    refine ⟨fun i => ?_, fun i₁ i₂ he => ?_⟩
    · by_cases hi : i.val < e
      · let j : Fin e := ⟨i.val, hi⟩
        have hje : Fin.castAdd e j = i := Fin.ext rfl
        rw [← hje, edgeUnion_castAdd]
        intro hc
        apply hG_simp.1 j
        induction hGj : G j using Sym2.ind with
        | _ a b =>
          dsimp only [C₁] at hc
          rw [hGj, Sym2.map_mk, Sym2.mk_isDiag_iff] at hc
          change (G j).IsDiag
          rw [hGj, Sym2.mk_isDiag_iff]
          exact castN.injective hc
      · let j : Fin e := ⟨i.val - e, by omega⟩
        have hje : Fin.natAdd e j = i := Fin.ext (by simp [j]; omega)
        rw [← hje, edgeUnion_natAdd]
        intro hc
        apply hG_simp.1 j
        induction hGj : G j using Sym2.ind with
        | _ a b =>
          dsimp only [C₂] at hc
          rw [hGj, Sym2.map_mk, Sym2.mk_isDiag_iff] at hc
          change (G j).IsDiag
          rw [hGj, Sym2.mk_isDiag_iff]
          exact shiftN.injective hc
    · by_cases h1 : i₁.val < e <;> by_cases h2 : i₂.val < e
      · let j₁ : Fin e := ⟨i₁.val, h1⟩
        let j₂ : Fin e := ⟨i₂.val, h2⟩
        have hj1 : Fin.castAdd e j₁ = i₁ := Fin.ext rfl
        have hj2 : Fin.castAdd e j₂ = i₂ := Fin.ext rfl
        rw [← hj1, ← hj2, edgeUnion_castAdd, edgeUnion_castAdd] at he
        have hGj : G j₁ = G j₂ := Sym2.map.injective castN.injective he
        rw [← hj1, ← hj2, hG_simp.2 hGj]
      · exfalso
        let j₁ : Fin e := ⟨i₁.val, h1⟩
        let j₂ : Fin e := ⟨i₂.val - e, by omega⟩
        have hj1 : Fin.castAdd e j₁ = i₁ := Fin.ext rfl
        have hj2 : Fin.natAdd e j₂ = i₂ := Fin.ext (by simp [j₂]; omega)
        rw [← hj1, ← hj2, edgeUnion_castAdd, edgeUnion_natAdd] at he
        induction hG1 : G j₁ using Sym2.ind with
        | _ a₁ _ =>
          have hmem : castN a₁ ∈ C₁ j₁ := by
            simp only [C₁, hG1, Sym2.map_mk]
            exact Sym2.mem_mk_left _ _
          rw [he] at hmem
          rcases Sym2.mem_map.mp hmem with ⟨b, _, hEq⟩
          have hv1 : a₁.val = n + b.val := (congrArg Fin.val hEq).symm
          have := a₁.isLt; omega
      · exfalso
        let j₁ : Fin e := ⟨i₁.val - e, by omega⟩
        let j₂ : Fin e := ⟨i₂.val, h2⟩
        have hj1 : Fin.natAdd e j₁ = i₁ := Fin.ext (by simp [j₁]; omega)
        have hj2 : Fin.castAdd e j₂ = i₂ := Fin.ext rfl
        rw [← hj1, ← hj2, edgeUnion_natAdd, edgeUnion_castAdd] at he
        induction hG2 : G j₂ using Sym2.ind with
        | _ a₂ _ =>
          have hmem : castN a₂ ∈ C₁ j₂ := by
            simp only [C₁, hG2, Sym2.map_mk]
            exact Sym2.mem_mk_left _ _
          rw [← he] at hmem
          rcases Sym2.mem_map.mp hmem with ⟨b, _, hEq⟩
          have hv1 : n + b.val = a₂.val := congrArg Fin.val hEq
          have := a₂.isLt; omega
      · let j₁ : Fin e := ⟨i₁.val - e, by omega⟩
        let j₂ : Fin e := ⟨i₂.val - e, by omega⟩
        have hj1 : Fin.natAdd e j₁ = i₁ := Fin.ext (by simp [j₁]; omega)
        have hj2 : Fin.natAdd e j₂ = i₂ := Fin.ext (by simp [j₂]; omega)
        rw [← hj1, ← hj2, edgeUnion_natAdd, edgeUnion_natAdd] at he
        have hGj : G j₁ = G j₂ := Sym2.map.injective shiftN.injective he
        rw [← hj1, ← hj2, hG_simp.2 hGj]
  have htot : 2 * optDepthMN m n = optDepth (edgeUnion C₁ C₂) := by
    rw [optDepth_edgeUnion_eq_add C₁ C₂ h53, ← hopt₁, ← hopt₂, heq, Nat.two_mul]
  rw [htot]
  exact optDepth_le_optDepthMN_of_isSimple (edgeUnion C₁ C₂) hu_simp (by omega)

end Cslib.Query.MinimumSpanningForest
