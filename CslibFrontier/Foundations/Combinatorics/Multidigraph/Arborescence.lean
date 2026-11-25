/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Multidigraph.Basic
public import CslibFrontier.Foundations.Combinatorics.Digraph.MatrixTree
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

/-!
# Spanning in-arborescences of finite multidigraphs

A multidigraph on the vertices `V` with arcs `E`, parallel arcs and loops allowed, is given here by
the maps `src tgt : E → V` sending each arc to its source and its target. A *spanning
in-arborescence rooted at `r`* chooses, for every vertex `v ≠ r`, an arc `f v` out of `v`, such
that following the chosen arcs leads from every vertex to `r`
(`Cslib.Multidigraph.IsInArborescence`, defined in
`CslibFrontier.Foundations.Combinatorics.Multidigraph.Basic`). On the arc multidigraph
`(arcSrc G, arcTgt G)` of a simple digraph `G : Digraph V`, these correspond bijectively to the
spanning in-arborescence subdigraphs `T ≤ G` (`Cslib.Multidigraph.arborescenceEquivSubdigraph`), and
`arcMatrix` specializes to `G.adjMatrix` (`Cslib.Multidigraph.arcMatrix_arcSrc_arcTgt`).

Their number is the determinant of the reduced Laplacian of the *arc-count matrix*, whose entry
`(u, w)` is the number of arcs from `u` to `w` (`Cslib.Multidigraph.arcMatrix`). This is the
directed matrix-tree theorem [Tutte1948] for multidigraphs
(`Cslib.Multidigraph.det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence`), derived from
the parent-function form `Digraph.det_laplacian_submatrix_eq_finsum_reachable` by sorting the
arborescences by the vertices `tgt (f v)` that their arcs reach.

## Main definitions

* `Cslib.Multidigraph.arcMatrix`: the arc-count matrix of a multidigraph.
* `Cslib.Multidigraph.arborescenceEquivSubdigraph`: bijection between multidigraph arborescences of
  `(arcSrc G, arcTgt G)` and subdigraph arborescences `T ≤ G`.

## Main results

* `Cslib.Multidigraph.arcMatrix_arcSrc_arcTgt`: `arcMatrix (arcSrc G) (arcTgt G) R = G.adjMatrix R`.
* `Cslib.Multidigraph.det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence`: the
  directed matrix-tree theorem for multidigraphs.
* `Cslib.Multidigraph.natCard_isInArborescence_eq`: root independence of the spanning
  in-arborescence count on balanced multidigraphs ([Stanley2013], Corollary 10.3).

## References

* [W. T. Tutte, *The dissection of equilateral triangles into equilateral triangles*][Tutte1948]
  (Theorem 3.6, according to [Stanley2013], Chapter 10 notes; the primary source was not
  inspected)
* [R. P. Stanley, *Topics in Algebraic Combinatorics*][Stanley2013], Theorem 10.4 (the directed
  matrix-tree theorem for digraphs with parallel arcs and loops)
-/

public section

open Matrix

namespace Cslib.Multidigraph

variable {V E : Type*} (src tgt : E → V)

variable (R : Type*) [NatCast R] [Fintype E] [DecidableEq V] in
/-- The **arc-count matrix** of a multidigraph: the entry `(u, w)` is the number of arcs from `u`
to `w`. -/
def arcMatrix : Matrix V V R :=
  Matrix.of fun u w => ((Finset.univ.filter fun e => src e = u ∧ tgt e = w).card : R)

/-- The entries of the arc-count matrix. -/
@[simp]
theorem arcMatrix_apply {R : Type*} [NatCast R] [Fintype E] [DecidableEq V] (u w : V) :
    arcMatrix src tgt R u w = ((Finset.univ.filter fun e => src e = u ∧ tgt e = w).card : R) := by
  rw [arcMatrix, Matrix.of_apply]

omit E src tgt in
/-- On the arc multidigraph of `G : Digraph V`, `arcMatrix` equals `G.adjMatrix`. -/
theorem arcMatrix_arcSrc_arcTgt (R : Type*) [AddMonoidWithOne R] [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] :
    arcMatrix (arcSrc G) (arcTgt G) R = G.adjMatrix R := by
  ext u w
  rw [arcMatrix_apply, Digraph.adjMatrix_apply]
  split_ifs with huw
  · have huniq : (Finset.univ.filter fun e : Arc G => arcSrc G e = u ∧ arcTgt G e = w) =
        {⟨(u, w), huw⟩} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, arc_ext_iff,
        arcSrc_mk, arcTgt_mk]
    rw [huniq, Finset.card_singleton, Nat.cast_one]
  · have hempty : (Finset.univ.filter fun e : Arc G => arcSrc G e = u ∧ arcTgt G e = w) = ∅ := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨rfl, rfl⟩
      exact huw e.2
    rw [hempty, Finset.card_empty, Nat.cast_zero]

omit E src tgt in
/-- Spanning in-arborescences of `(arcSrc G, arcTgt G)` correspond bijectively to spanning
in-arborescence subdigraphs `T ≤ G`. -/
noncomputable def arborescenceEquivSubdigraph (G : Digraph V) (r : V) :
    {f : {v // v ≠ r} → Arc G // IsInArborescence (arcSrc G) (arcTgt G) r f} ≃
      {T : Digraph V // T ≤ G ∧ T.IsInArborescence r} := by
  classical
  let mkSub (f : {v // v ≠ r} → Arc G) (hf : IsInArborescence (arcSrc G) (arcTgt G) r f) :
      {T : Digraph V // T ≤ G ∧ T.IsInArborescence r} :=
    ⟨{ Adj := fun v w => ∃ hv : v ≠ r, arcTgt G (f ⟨v, hv⟩) = w },
      fun v w ⟨hv, hw⟩ => by
        have hs : (f ⟨v, hv⟩).1.1 = v := hf.src_eq ⟨v, hv⟩
        have ht : (f ⟨v, hv⟩).1.2 = w := hw
        exact hs ▸ ht ▸ (f ⟨v, hv⟩).2,
      ⟨fun w ⟨hr, _⟩ => hr rfl,
        fun v hv => ⟨arcTgt G (f ⟨v, hv⟩), ⟨hv, rfl⟩, fun w ⟨_, hw⟩ => hw.symm⟩,
        hf.reachable⟩⟩
  have hrel (T : Digraph V) (hT : T.IsInArborescence r) :
      T.Adj = fun x y => ∃ hx : x ≠ r, (hT.existsUnique_adj x hx).choose = y := by
    ext x y
    exact ⟨fun hxy =>
      let hx : x ≠ r := fun h => hT.not_adj_root y (h ▸ hxy)
      ⟨hx, (hT.existsUnique_adj x hx).unique (hT.existsUnique_adj x hx).choose_spec.1 hxy⟩,
      fun ⟨hx, hy⟩ => hy ▸ (hT.existsUnique_adj x hx).choose_spec.1⟩
  refine
    { toFun := fun ⟨f, hf⟩ => mkSub f hf
      invFun := fun ⟨T, hTG, hT⟩ =>
        ⟨fun v => ⟨(v.1, (hT.existsUnique_adj v.1 v.2).choose),
            hTG (hT.existsUnique_adj v.1 v.2).choose_spec.1⟩,
          fun _ => rfl, fun v => hrel T hT ▸ hT.reachable v⟩
      left_inv := fun ⟨f, hf⟩ => Subtype.ext <| funext fun v => by
        apply Subtype.ext
        refine Prod.ext (hf.src_eq v).symm ?_
        obtain ⟨_, hw⟩ := ((mkSub f hf).2.2.existsUnique_adj v.1 v.2).choose_spec.1
        exact hw.symm
      right_inv := fun ⟨T, _, hT⟩ => Subtype.ext (Digraph.ext (hrel T hT).symm) }

/-- **The directed matrix-tree theorem** for multidigraphs [Tutte1948] ([Stanley2013],
Theorem 10.4). The determinant of the reduced Laplacian of the arc-count matrix, the out-degree
matrix minus the arc-count matrix with the row and column of `r` deleted, is the number of spanning
in-arborescences rooted at `r` (arcs directed towards `r`). Loops do not contribute. The source
assumes a connected digraph; connectivity is not needed. -/
theorem det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence (R : Type*) [CommRing R]
    [Fintype V] [DecidableEq V] [Fintype E] (r : V) :
    ((arcMatrix src tgt R).laplacian.submatrix (Subtype.val : {v // v ≠ r} → V)
        Subtype.val).det =
      Nat.card {f : {v // v ≠ r} → E // IsInArborescence src tgt r f} := by
  classical
  rw [Digraph.det_laplacian_submatrix_eq_finsum_reachable]
  let P : ({v // v ≠ r} → V) → Prop := fun g =>
    ∀ v, Relation.ReflTransGen (fun v w => ∃ h : v ≠ r, g ⟨v, h⟩ = w) v r
  let Arb := {f : {v // v ≠ r} → E // IsInArborescence src tgt r f}
  let φ : Arb → {g // P g} := fun f => ⟨fun v => tgt (f.1 v), f.2.reachable⟩
  have hfib : ∀ g : {g // P g}, Nat.card {f // φ f = g} =
      ∏ i : {v // v ≠ r}, (Finset.univ.filter fun e => src e = i ∧ tgt e = g.1 i).card := by
    intro g
    let ψ : {f // φ f = g} ≃ ((i : {v // v ≠ r}) → {e // src e = i ∧ tgt e = g.1 i}) :=
      { toFun := fun f i => ⟨f.1.1 i, f.1.2.src_eq i, congrFun (congrArg Subtype.val f.2) i⟩
        invFun := fun h => ⟨⟨fun i => (h i).1, fun i => (h i).2.1, by
            have hg : (fun v => tgt (h v).1) = g.1 := funext fun i => (h i).2.2
            have := g.2
            simp only [P, ← hg] at this
            exact this⟩,
          Subtype.ext (funext fun i => (h i).2.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr ψ, Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard : Nat.card Arb = ∑ g : {g // P g},
      ∏ i : {v // v ≠ r}, (Finset.univ.filter fun e => src e = i ∧ tgt e = g.1 i).card := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv φ), Nat.card_sigma]
    exact Finset.sum_congr rfl fun g _ => hfib g
  change _ = ((Nat.card Arb : ℕ) : R)
  rw [hcard, Nat.cast_sum, ← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Nat.cast_prod]
  exact Finset.prod_congr rfl fun i _ => arcMatrix_apply src tgt _ _

private theorem card_filter_eq_sum_card_filter {V E : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] (φ ψ : E → V) (x : V) :
    (Finset.univ.filter fun e => φ e = x).card =
      ∑ y : V, (Finset.univ.filter fun e => φ e = x ∧ ψ e = y).card := by
  classical
  simpa only [Finset.filter_filter, Finset.mem_univ, and_true] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ.filter fun e => φ e = x) Finset.univ ψ).symm

/-- **Root independence of the arborescence count** ([Stanley2013], Corollary 10.3). In any finite
balanced multidigraph (`∀ v, outdeg v = indeg v`), the number of spanning in-arborescences rooted
at `u` equals that rooted at `v`. Connectivity and positive out-degree are not required. -/
theorem natCard_isInArborescence_eq [DecidableEq V] [Fintype E]
    (hbal : ∀ v, (Finset.univ.filter fun e => src e = v).card =
      (Finset.univ.filter fun e => tgt e = v).card) (u v : V) :
    Nat.card {f : {x // x ≠ u} → E // IsInArborescence src tgt u f} =
      Nat.card {f : {x // x ≠ v} → E // IsInArborescence src tgt v f} := by
  by_cases hfin : Finite V
  · have := Fintype.ofFinite V
    apply Nat.cast_injective (R := ℤ)
    rw [← det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence src tgt ℤ u,
      ← det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence src tgt ℤ v]
    refine Matrix.det_laplacian_submatrix_eq (arcMatrix src tgt ℤ) (fun x => ?_) u v
    have hrow : ∑ w : V, arcMatrix src tgt ℤ x w =
        ((Finset.univ.filter fun e => src e = x).card : ℤ) := by
      simp only [arcMatrix_apply, ← Nat.cast_sum, ← card_filter_eq_sum_card_filter src tgt x]
    have hcol : ∑ z : V, arcMatrix src tgt ℤ z x =
        ((Finset.univ.filter fun e => tgt e = x).card : ℤ) := by
      simp only [arcMatrix_apply, ← Nat.cast_sum, Nat.cast_inj]
      rw [card_filter_eq_sum_card_filter tgt src x]
      exact Finset.sum_congr rfl fun z _ => congrArg Finset.card (by ext e; simp [and_comm])
    rw [hrow, hcol, hbal x]
  · obtain ⟨w, hw⟩ := @Infinite.exists_notMem_finset V (not_finite_iff_infinite.1 hfin)
      ({u, v} ∪ Finset.univ.image src)
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and, not_or, not_exists] at hw
    have hempty : ∀ r : V, r ≠ w →
        IsEmpty {f : {x // x ≠ r} → E // IsInArborescence src tgt r f} := fun r hr =>
      ⟨fun ⟨f, hf⟩ => hw.2 (f ⟨w, hr.symm⟩) (hf.src_eq ⟨w, hr.symm⟩)⟩
    rw [@Nat.card_of_isEmpty _ (hempty u (Ne.symm hw.1.1)),
      @Nat.card_of_isEmpty _ (hempty v (Ne.symm hw.1.2))]

end Cslib.Multidigraph
