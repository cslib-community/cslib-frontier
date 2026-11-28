/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TutteBerge
import CslibFrontier.Foundations.Data.Nat.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# `7/8` vertex-coverage matchings in `3`-regular simple graphs

From the Tutte–Berge deficiency formula
`SimpleGraph.exists_isMatching_ncard_verts_add_ncard_oddComponents_eq`, every finite `3`-regular
simple graph has a matching covering at least `7/8` of its vertices: in the Tutte–Berge maximizer
`U`, any odd component `C` of `G - U` with a single boundary edge to `U` satisfies
`3 |C| - 1 ≤ |C| (|C| - 1)` with `|C|` odd, forcing `|C| ≥ 5`.

## Main results

* `SimpleGraph.exists_isMatching_mul_eight_ge`: every finite `3`-regular simple graph admits a
  matching `M` with `7 * Nat.card V ≤ 8 * M.verts.ncard`.
-/

public section

/-! ### `7/8` vertex-coverage matchings in `3`-regular simple graphs -/

namespace SimpleGraph

/-- **Every finite `3`-regular simple graph has a matching covering at least `7/8` of its
vertices.** In the Tutte–Berge maximizer `U`, every odd component `C` of `G - U` has an odd number
`b_C`
of edges to `U`; when `b_C = 1`, `3 |C| - 1 ≤ |C| (|C| - 1)` with `|C|` odd forces `|C| ≥ 5`. Thus
`q₁ + 3 q₃ ≤ 3 |U|` and `|U| + 5 q₁ + q₃ ≤ |V|`, giving `8 (q₁ + q₃ - |U|) ≤ |V|`. -/
theorem exists_isMatching_mul_eight_ge {V : Type*} [Finite V] (H : SimpleGraph V)
    (h3 : ∀ v : V, (H.neighborSet v).ncard = 3) :
    ∃ M : H.Subgraph, M.IsMatching ∧ 7 * Nat.card V ≤ 8 * M.verts.ncard := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨M, U, hM, hTB⟩ := H.exists_isMatching_ncard_verts_add_ncard_oddComponents_eq
  refine ⟨M, hM, ?_⟩
  set G' := ((⊤ : H.Subgraph).deleteVerts U).coe
  set OddC := G'.oddComponents
  have := Fintype.ofFinite OddC
  let Ufin : Finset V := U.toFinset
  have hUcard : Ufin.card = U.ncard := (Set.ncard_eq_toFinset_card' U).symm
  let S (c : OddC) : Finset V := (Subtype.val '' c.1.supp).toFinset
  have hScard (c : OddC) : (S c).card = c.1.supp.ncard := by
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_image_of_injective _ Subtype.val_injective]
  have hSodd (c : OddC) : Odd (S c).card := by
    rw [hScard]
    exact c.2
  have hS_notU (c : OddC) {v : V} (hv : v ∈ S c) : v ∉ U := by
    simp only [S, Set.mem_toFinset, Set.mem_image] at hv
    obtain ⟨x, -, rfl⟩ := hv
    exact x.2.2
  have hS_disj_U (c : OddC) : Disjoint (S c) Ufin :=
    Finset.disjoint_left.mpr fun v hv hvU => hS_notU c hv (Set.mem_toFinset.mp hvU)
  have hS_pairwise : Set.Pairwise (Set.univ : Set OddC) fun c₁ c₂ => Disjoint (S c₁) (S c₂) := by
    intro c₁ _ c₂ _ hne
    refine Finset.disjoint_left.mpr fun v hv₁ hv₂ => hne ?_
    simp only [S, Set.mem_toFinset, Set.mem_image] at hv₁ hv₂
    obtain ⟨x₁, hx₁, hxv₁⟩ := hv₁
    obtain ⟨x₂, hx₂, hxv₂⟩ := hv₂
    have hx : x₁ = x₂ := Subtype.ext (hxv₁.trans hxv₂.symm)
    exact Subtype.ext (ConnectedComponent.eq_of_common_vertex hx₁ (hx ▸ hx₂))
  have hS_closed (c : OddC) {v w : V} (hv : v ∈ S c) (hw : w ∉ U) (hadj : H.Adj v w) :
      w ∈ S c := by
    simp only [S, Set.mem_toFinset, Set.mem_image] at hv ⊢
    obtain ⟨x, hx, rfl⟩ := hv
    refine ⟨⟨w, trivial, hw⟩, ?_, rfl⟩
    rw [ConnectedComponent.mem_supp_iff] at hx ⊢
    rw [← hx]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj
      (Subgraph.Adj.coe (Subgraph.deleteVerts_adj.mpr ⟨trivial, x.2.2, trivial, hw, hadj⟩))).symm
  have h3fin (v : V) : (H.neighborFinset v).card = 3 := by
    have := h3 v
    rwa [← H.coe_neighborFinset v, Set.ncard_coe_finset] at this
  let intPairs (c : OddC) : Finset (V × V) :=
    (S c ×ˢ S c).filter fun p => H.Adj p.1 p.2
  let cutPairs (c : OddC) : Finset (V × V) :=
    (S c ×ˢ Ufin).filter fun p => H.Adj p.1 p.2
  have hdeg_sum (c : OddC) : 3 * (S c).card = (intPairs c).card + (cutPairs c).card := by
    have hpart : intPairs c ∪ cutPairs c =
        (S c).biUnion fun v => (H.neighborFinset v).map
          ⟨fun w => (v, w), fun _ _ h => Prod.mk.inj h |>.2⟩ := by
      ext ⟨v, w⟩
      simp only [intPairs, cutPairs, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
        Finset.mem_biUnion, Finset.mem_map, mem_neighborFinset]
      constructor
      · rintro (⟨⟨hv, _⟩, hadj⟩ | ⟨⟨hv, _⟩, hadj⟩) <;> exact ⟨v, hv, w, hadj, rfl⟩
      · rintro ⟨v', hv', w', hadj, hpair⟩
        change (v', w') = (v, w) at hpair
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
        by_cases hwU : w' ∈ U
        · exact Or.inr ⟨⟨hv', Set.mem_toFinset.mpr hwU⟩, hadj⟩
        · exact Or.inl ⟨⟨hv', hS_closed c hv' hwU hadj⟩, hadj⟩
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter
      (Finset.disjoint_product.2 (Or.inr (hS_disj_U c)))), hpart, Finset.card_biUnion]
    · simp only [Finset.card_map, h3fin, Finset.sum_const, smul_eq_mul, mul_comm]
    · intro v₁ _ v₂ _ hne
      refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => hne ?_
      simp only [Finset.mem_map] at hp₁ hp₂
      obtain ⟨w₁, -, rfl⟩ := hp₁
      obtain ⟨w₂, -, heq⟩ := hp₂
      exact (Prod.mk.inj heq).1.symm
  let idx : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  have hint_even (c : OddC) : Even (intPairs c).card := by
    let F_lt := (intPairs c).filter fun p => idx p.1 < idx p.2
    let F_gt := (intPairs c).filter fun p => ¬idx p.1 < idx p.2
    have hsplit : (intPairs c).card = F_lt.card + F_gt.card :=
      (Finset.card_filter_add_card_filter_not _).symm
    have hbij : F_lt.card = F_gt.card := by
      refine Finset.card_bij (fun p _ => p.swap) (fun p hp => ?_)
        (fun p₁ _ p₂ _ h => Prod.swap_injective h) (fun p hp => ?_)
      · simp only [F_lt, F_gt, intPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.symm⟩, fun hlt => lt_asymm hp.2 hlt⟩
      · simp only [F_lt, F_gt, intPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
        have hne : idx p.2 ≠ idx p.1 := fun h => hp.1.2.ne (idx.injective h.symm)
        refine ⟨p.swap, ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.symm⟩, ?_⟩, Prod.swap_swap p⟩
        exact lt_of_le_of_ne (not_lt.mp hp.2) hne
    rw [hsplit, hbij]
    exact ⟨F_gt.card, rfl⟩
  have hint_le (c : OddC) : (intPairs c).card ≤ (S c).card * (S c).card - (S c).card := by
    have hsub : intPairs c ⊆ (S c).offDiag := fun p hp => by
      simp only [intPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag] at hp ⊢
      exact ⟨hp.1.1, hp.1.2, hp.2.ne⟩
    exact (Finset.card_le_card hsub).trans_eq (Finset.offDiag_card (S c))
  -- Each odd component pays `8` in vertices plus three times its cut edges: the cut size is odd,
  -- and a single cut edge forces `3 |C| - 1 ≤ |C| (|C| - 1)`, so `|C| ≥ 5`.
  have hpt (c : OddC) : 8 ≤ (S c).card + 3 • (cutPairs c).card := by
    rw [smul_eq_mul]
    obtain ⟨k, hk⟩ := hSodd c
    obtain ⟨m, hm⟩ := hint_even c
    have hsum := hdeg_sum c
    have hle := hint_le c
    rw [hk] at hsum hle
    rcases k with _ | _ | k <;> omega
  have hcut_tot : ∑ c : OddC, (cutPairs c).card ≤ 3 * U.ncard := by
    have hbi_disj : ((Finset.univ : Finset OddC) : Set OddC).PairwiseDisjoint cutPairs :=
      fun c₁ _ c₂ _ hne => Finset.disjoint_filter_filter
        (Finset.disjoint_product.2 (Or.inl (hS_pairwise trivial trivial hne)))
    let allFromU : Finset (V × V) :=
      Ufin.biUnion fun u => (H.neighborFinset u).map
        ⟨fun v => (v, u), fun _ _ h => Prod.mk.inj h |>.1⟩
    have hsub : Finset.univ.biUnion cutPairs ⊆ allFromU := by
      intro ⟨v, u⟩ hp
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, cutPairs, Finset.mem_filter,
        Finset.mem_product] at hp
      obtain ⟨c, ⟨_, hu⟩, hadj⟩ := hp
      simp only [allFromU, Finset.mem_biUnion, Finset.mem_map, mem_neighborFinset]
      exact ⟨u, hu, v, hadj.symm, rfl⟩
    rw [← Finset.card_biUnion hbi_disj, ← hUcard]
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    simp [h3fin, mul_comm]
  have hvert_tot : U.ncard + ∑ c : OddC, (S c).card ≤ Nat.card V := by
    rw [← hUcard, ← Finset.card_biUnion fun c₁ _ c₂ _ hne => hS_pairwise trivial trivial hne,
      ← Finset.card_union_of_disjoint ((Finset.disjoint_biUnion_right _ _ _).2 fun c _ =>
        (hS_disj_U c).symm), Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  have hq := Finset.card_nsmul_le_sum Finset.univ _ 8 fun c _ => hpt c
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Finset.sum_add_distrib,
    Finset.sum_nsmul, smul_eq_mul, smul_eq_mul] at hq
  omega

end SimpleGraph
