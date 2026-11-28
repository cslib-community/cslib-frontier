/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Matrix.Permanent.Split

/-!
# Eliminating a placed gadget from a permanent

Read a square matrix as the weighted adjacency matrix of a digraph, so that its permanent is the
total weight of its cycle covers. Reductions to the permanent, such as Valiant's
[Valiant][Valiant1979], replace parts of a digraph by small weighted digraphs, *gadgets*, which
the rest of the digraph enters only at *entry* vertices and leaves only at *exit* vertices.

Here the gadget sits on the vertices `g a` for an embedding `g : W ↪ V`. Its entries and exits are
given by embeddings `entry : P ↪ W` and `exit : Q ↪ W` of port types `P` and `Q`. The matrix is
`A + D`, where `A` is supported on the gadget block and `D` meets the gadget only in exit rows and
entry columns. `permOn_add_of_gadget` sums over the set `Out` of exits through which a cycle cover
leaves the gadget and the set `In` of entries through which it comes back. Each term is the minor
of the gadget without the rows of `Out` and the columns of `In`, times the permanent sum of `D` in
which the gadget is replaced by those exits (as rows) and entries (as columns). Once the minors
of a gadget are known, this removes the gadget from the analysis.

The minors of a placed gadget are read off in the gadget's own indices by
`permOn_map_sdiff_eq_permOnList`, which evaluates them as `permOnList` on explicit lists.

## Main results

* `Matrix.permOn_add_of_gadget`: elimination of a placed gadget.
* `Matrix.permOn_map_sdiff_eq_permOnList`: a minor of a placed gadget, in the gadget's indices.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
-/

public section

namespace Matrix

open Finset

variable {V W R : Type*} [DecidableEq V] [Fintype W] [CommSemiring R]

/-- **Elimination of a placed gadget.** Let `A` be supported on the block of the gadget vertices
`g a`, and let `D` vanish in the gadget rows other than the exits and in the gadget columns other
than the entries. If the row and column sets contain the gadget, then the permanent sum of `A + D`
is the sum, over the sets `Out` of exits and `In` of entries, of the minor of `A` without the
rows of `Out` and the columns of `In`, times the permanent sum of `D` in which the gadget is
replaced by the exits of `Out` (rows) and the entries of `In` (columns). -/
theorem permOn_add_of_gadget {P Q : Type*} [Fintype V] [Fintype P] [Fintype Q] (g : W ↪ V)
    (entry : P ↪ W) (exit : Q ↪ W) (A D : Matrix V V R)
    (hArow : ∀ i, (∀ a, i ≠ g a) → ∀ j, A i j = 0)
    (hAcol : ∀ j, (∀ b, j ≠ g b) → ∀ i, A i j = 0)
    (hDrow : ∀ a, (∀ q, a ≠ exit q) → ∀ j, D (g a) j = 0)
    (hDcol : ∀ b, (∀ p, b ≠ entry p) → ∀ i, D i (g b) = 0)
    {S T : Finset V} (hS : univ.map g ⊆ S) (hT : univ.map g ⊆ T) :
    permOn (A + D) S T = ∑ Out : Finset Q, ∑ In : Finset P,
      permOn A (univ.map g \ (Out.map exit).map g) (univ.map g \ (In.map entry).map g) *
        permOn D (S \ univ.map g ∪ (Out.map exit).map g)
          (T \ univ.map g ∪ (In.map entry).map g) := by
  set G := univ.map g with hG
  let φ : Finset Q × Finset P → Finset V × Finset V :=
    fun p => (G \ (p.1.map exit).map g, G \ (p.2.map entry).map g)
  have hXG : ∀ (X : Finset W), X.map g ⊆ G := fun X u hu => by
    obtain ⟨a, -, rfl⟩ := mem_map.1 hu
    exact mem_map_of_mem g (mem_univ a)
  have hsd : ∀ (U : Finset V) (X : Finset W), G ⊆ U →
      U \ (G \ X.map g) = U \ G ∪ X.map g := fun U X hU => by
    ext u
    have := @hXG X u
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hu, h⟩
      by_cases huG : u ∈ G
      · exact Or.inr (by by_contra h'; exact h ⟨huG, h'⟩)
      · exact Or.inl ⟨hu, huG⟩
    · rintro (⟨hu, huG⟩ | hu)
      · exact ⟨hu, fun h => huG h.1⟩
      · exact ⟨hU (this hu), fun h => h.2 hu⟩
  rw [permOn_add, ← sum_product']
  have hsub : (univ ×ˢ univ).image φ ⊆ S.powerset ×ˢ T.powerset := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := mem_image.1 hx
    simp only [φ, mem_product, mem_powerset]
    exact ⟨sdiff_subset.trans hS, sdiff_subset.trans hT⟩
  rw [← sum_subset hsub ?zero]
  case zero =>
    rintro ⟨S', T'⟩ hx hnot
    simp only [mem_product, mem_powerset] at hx
    by_contra hne
    have hA0 : permOn A S' T' ≠ 0 := left_ne_zero_of_mul hne
    have hD0 : permOn D (S \ S') (T \ T') ≠ 0 := right_ne_zero_of_mul hne
    have hS'G : S' ⊆ G := fun u hu => by
      by_contra huG
      refine hA0 (permOn_eq_zero_of_row hu fun v _ => hArow u (fun a ha => huG ?_) v)
      exact ha ▸ mem_map_of_mem g (mem_univ a)
    have hT'G : T' ⊆ G := fun v hv => by
      by_contra hvG
      refine hA0 (permOn_eq_zero_of_col hv fun u _ => hAcol v (fun b hb => hvG ?_) u)
      exact hb ▸ mem_map_of_mem g (mem_univ b)
    have hrow : ∀ a, (∀ q, a ≠ exit q) → g a ∈ S' := fun a ha => by
      by_contra h
      exact hD0 (permOn_eq_zero_of_row (mem_sdiff.2 ⟨hS (mem_map_of_mem g (mem_univ a)), h⟩)
        fun v _ => hDrow a ha v)
    have hcol : ∀ b, (∀ p, b ≠ entry p) → g b ∈ T' := fun b hb => by
      by_contra h
      exact hD0 (permOn_eq_zero_of_col (mem_sdiff.2 ⟨hT (mem_map_of_mem g (mem_univ b)), h⟩)
        fun u _ => hDcol b hb u)
    refine hnot (mem_image.2 ⟨(univ.filter fun q => g (exit q) ∉ S',
      univ.filter fun p => g (entry p) ∉ T'), mem_univ _, ?_⟩)
    simp only [φ, Prod.mk.injEq]
    have hpart {I : Type*} [Fintype I] (emb : I ↪ W) (U' : Finset V) (hU'G : U' ⊆ G)
        (hmem : ∀ a, (∀ p, a ≠ emb p) → g a ∈ U') :
        G \ ((univ.filter fun p => g (emb p) ∉ U').map emb).map g = U' := by
      ext u
      simp only [mem_sdiff, mem_map, mem_filter, mem_univ, true_and, hG]
      constructor
      · rintro ⟨⟨a, rfl⟩, h⟩
        by_cases hex : ∃ p, a = emb p
        · obtain ⟨p, rfl⟩ := hex
          by_contra h'
          exact h ⟨emb p, ⟨p, h', rfl⟩, rfl⟩
        · exact hmem a fun p hp => hex ⟨p, hp⟩
      · intro hu
        obtain ⟨a, -, rfl⟩ := mem_map.1 (hU'G hu)
        exact ⟨⟨a, rfl⟩, fun ⟨_, ⟨p, hp, rfl⟩, hb⟩ => hp (g.injective hb ▸ hu)⟩
    exact ⟨hpart exit S' hS'G hrow, hpart entry T' hT'G hcol⟩
  have hφ : Set.InjOn φ ↑(univ ×ˢ univ : Finset (Finset Q × Finset P)) := by
    rintro ⟨O₁, I₁⟩ - ⟨O₂, I₂⟩ - h
    simp only [φ, Prod.mk.injEq] at h
    have key : ∀ (X Y : Finset W), G \ X.map g = G \ Y.map g → X = Y := fun X Y h => by
      have hX := Finset.sdiff_sdiff_eq_self (hXG X)
      have hY := Finset.sdiff_sdiff_eq_self (hXG Y)
      rw [← map_inj (f := g), ← hX, ← hY, h]
    have h1 := key _ _ h.1
    have h2 := key _ _ h.2
    rw [map_inj] at h1 h2
    exact Prod.ext h1 h2
  rw [sum_image hφ, sum_product]
  refine sum_congr rfl fun Out _ => sum_congr rfl fun In _ => ?_
  simp only [φ, hsd S _ hS, hsd T _ hT]

/-- The gadget vertices other than those of `X`, listed by `l`. -/
private theorem sdiff_map_eq_toFinset (g : W ↪ V) (X : Finset W) (l : List W)
    (hl : ∀ a, a ∈ l ↔ a ∉ X) : univ.map g \ X.map g = (l.map g).toFinset := by
  ext u
  simp only [mem_sdiff, mem_map, mem_univ, true_and, List.mem_toFinset, List.mem_map, hl]
  constructor
  · rintro ⟨⟨a, rfl⟩, h⟩
    exact ⟨a, fun ha => h ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, fun ⟨b, hb, hba⟩ => ha (g.injective hba ▸ hb)⟩

/-- **A minor of a placed gadget, in the gadget's indices.** Without the gadget vertices of `X`
(rows) and `Y` (columns), the permanent sum over the gadget is `permOnList` of the gadget along
duplicate-free lists `rows` and `cols` of the remaining vertices. -/
theorem permOn_map_sdiff_eq_permOnList [Fintype V] [DecidableEq W] (g : W ↪ V) (M : Matrix V V R)
    {X Y : Finset W}
    {rows cols : List W} (hr : rows.Nodup) (hc : cols.Nodup)
    (hrows : ∀ a, a ∈ rows ↔ a ∉ X) (hcols : ∀ b, b ∈ cols ↔ b ∉ Y) :
    permOn M (univ.map g \ X.map g) (univ.map g \ Y.map g) =
      permOnList (fun a b => M (g a) (g b)) rows cols := by
  rw [sdiff_map_eq_toFinset g X rows hrows, sdiff_map_eq_toFinset g Y cols hcols,
    permOn_eq_permOnList _ _ _ (hr.map g.injective) (hc.map g.injective)]
  exact permOnList_map (fun u v => M u v) g rows cols

end Matrix
