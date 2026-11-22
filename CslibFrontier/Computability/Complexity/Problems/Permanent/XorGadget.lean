/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Matrix.Permanent.Gadget

/-!
# The XOR gadget of Valiant's theorem

A *cycle cover* of a weighted digraph on the vertices `V`, with weight `A x y` on the edge
`x → y`, is a permutation `σ` of `V`: every vertex `x` has the single outgoing edge `x → σ x`.
Its weight is `∏ x, A x (σ x)`, so the permanent of `A` is the total weight of the cycle covers.

The XOR gadget of Arora and Barak's proof of Valiant's theorem
[Arora and Barak, Theorem 9.8 and Figure 9.3][AroraBarak07] replaces two edges `u → u'` and
`v → v'` of a digraph `G` by four new vertices. They are numbered `0, 1, 2, 3`: vertex `0` is
entered from `u` and left towards `v'`, vertex `3` is entered from `v` and left towards `u'`, and
vertices `1` (top) and `2` (bottom) are internal. Their weighted adjacency matrix `gadget`
is read off the figure; unmarked edges have weight `1`. `replace A u u' v v'` is the resulting
digraph `G'` on `V ⊕ Fin 4`.

Exercise 3 of Chapter 9 of the draft states the gadget's property. Let `σ` be a cycle cover of `G`
that uses exactly one of the two edges. The cycle covers of `G'` that follow `σ` and pass through
the gadget in place of that edge form the set `lift u u' v v' σ`. Their total weight is `4` times
the weight of `σ` (`sum_lift`). The cycle covers of `G'` in no such set have total weight `0`
(`sum_filter_notMem_lift`). The sets of distinct covers are disjoint (`disjoint_lift`). Hence
the permanent of `G'` is `4` times the total weight of the cycle covers of `G` that use exactly
one of the two edges (`permanent_replace`). This is the form in which the proof of Theorem 9.8
uses the gadget.

The proof eliminates the gadget with `Matrix.permOn_add_of_gadget`. Read the gadget as two ports,
one per replaced edge. Port `0` (for `u → u'`) enters at vertex `0` and leaves at vertex `3`;
port `1` (for `v → v'`) enters at `3` and leaves at `0`. The minor of the gadget without the exit
rows of a set of ports and the entry columns of another is `4` when both are the same single port,
and `0` otherwise. This is checked by evaluation.

## Source mapping

The source is the public web draft of 2007-01-08, Chapter 9: Exercise 3 (printed p. 185, PDF
p. 201), the text of the proof of Theorem 9.8 (printed pp. 176–178), and the gadget of
Figure 9.3 (printed p. 177). The text's reference to the figure, “Figure count:fig:valiantgad”,
is unresolved, but the figure is present. Two points of the formalization go beyond the draft:

* The figure attaches the gadget by edges of weight `1`. A cover of `G` that uses `u → u'` has
  `A u u'` among its factors, so the claimed total `4w` holds only when the replaced edges have
  weight `1`, as in Theorem 9.8. `replace` gives the entry edges `u → 0` and `v → 3` the weights
  `A u u'` and `A v v'`. This is the figure verbatim when both weights are `1`, and makes the
  statements hold for all weights.
* The two edges must be distinct: `(u, u') ≠ (v, v')`. The vertices need not be.

## Main definitions

* `Cslib.Complexity.XorGadget.gadget`: the gadget of Figure 9.3.
* `Cslib.Complexity.XorGadget.replace`: the digraph `G'` with the two edges replaced.
* `Cslib.Complexity.XorGadget.lift`: the cycle covers of `G'` corresponding to one of `G`.

## Main results

* `Cslib.Complexity.XorGadget.sum_lift`: the corresponding covers weigh `4w` in total.
* `Cslib.Complexity.XorGadget.sum_filter_notMem_lift`: all other covers weigh `0` in total.
* `Cslib.Complexity.XorGadget.disjoint_lift`: distinct covers of `G` correspond to disjoint
  sets.
* `Cslib.Complexity.XorGadget.permanent_replace`: the permanent of `G'`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
-/

public section

open Finset Matrix Equiv Sum Function

namespace Cslib.Complexity.XorGadget

/-- The XOR gadget of Arora and Barak's Figure 9.3, as a weighted adjacency matrix. Vertex `0` is
entered from `u` and left towards `v'`, vertex `3` is entered from `v` and left towards `u'`, and
vertices `1` (top of the figure) and `2` (bottom) are internal. -/
def gadget : Matrix (Fin 4) (Fin 4) ℤ :=
  of ![![0, 1, -1, -1],
       ![1, -1, 1, 1],
       ![0, 1, 1, 2],
       ![0, 1, 3, 0]]

/-- The entry vertices of the two ports: port `0` (the edge `u → u'`) enters at vertex `0`, port
`1` (the edge `v → v'`) at vertex `3`. -/
private def entry : Fin 2 ↪ Fin 4 := ⟨![0, 3], by decide⟩

/-- The exit vertices of the two ports: port `0` leaves at vertex `3`, port `1` at vertex `0`. -/
private def exit : Fin 2 ↪ Fin 4 := ⟨![3, 0], by decide⟩

/-- The gadget vertices outside `X`, in order. -/
private def kept (X : Finset (Fin 4)) : List (Fin 4) :=
  (List.finRange 4).filter fun a => a ∉ X

private theorem mem_kept (X : Finset (Fin 4)) (a : Fin 4) : a ∈ kept X ↔ a ∉ X := by
  simp [kept]

private theorem kept_nodup (X : Finset (Fin 4)) : (kept X).Nodup :=
  (List.nodup_finRange 4).filter _

/-- The minors of the gadget for all sets of ports, checked by evaluation: without the exit rows
of `Out` and the entry columns of `In`, the permanent is `4` when `Out = In` is a single port. -/
private theorem gadget_minor : ∀ Out In : Finset (Fin 2),
    permOnList gadget (kept (Out.map exit)) (kept (In.map entry)) =
      if Out = In ∧ Out.card = 1 then 4 else 0 := by
  decide +kernel

variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- The minors of the gadget, placed on the vertices `inr a` of a matrix over any commutative
ring. -/
private theorem permOn_minor [Fintype V] (N : Matrix (V ⊕ Fin 4) (V ⊕ Fin 4) R)
    (hN : ∀ a b, N (inr a) (inr b) = (gadget a b : R)) (Out In : Finset (Fin 2)) :
    permOn N (univ.map Embedding.inr \ (Out.map exit).map Embedding.inr)
        (univ.map Embedding.inr \ (In.map entry).map Embedding.inr) =
      if Out = In ∧ Out.card = 1 then 4 else 0 := by
  rw [permOn_map_sdiff_eq_permOnList _ N (kept_nodup _) (kept_nodup _) (mem_kept _)
    (mem_kept _)]
  simp only [Embedding.inr_apply, hN]
  rw [show (fun a b => (gadget a b : R)) = fun a b => Int.castRingHom R (gadget a b) from rfl,
    ← map_permOnList (Int.castRingHom R) gadget, gadget_minor]
  split_ifs <;> simp

/-- **The digraph `G'` of Exercise 9.3.** The edges `u → u'` and `v → v'` of the weighted digraph
`A` on `V` are replaced by the XOR gadget on the vertices `inr 0, …, inr 3`. It is attached by the
edges `u → 0` and `v → 3`, of the weights `A u u'` and `A v v'`, and by the edges `3 → u'` and
`0 → v'`, of weight `1`. When the replaced edges have weight `1` this is Figure 9.3 verbatim. -/
def replace (A : Matrix V V R) (u u' v v' : V) : Matrix (V ⊕ Fin 4) (V ⊕ Fin 4) R :=
  of fun
    | inl x, inl y => if x = u ∧ y = u' ∨ x = v ∧ y = v' then 0 else A x y
    | inl x, inr k => if x = u ∧ k = 0 then A u u' else if x = v ∧ k = 3 then A v v' else 0
    | inr k, inl y => if k = 3 ∧ y = u' ∨ k = 0 ∧ y = v' then 1 else 0
    | inr k, inr l => (gadget k l : R)

section Entries

variable (A : Matrix V V R) (u u' v v' : V)

private theorem replace_inl_inl (x y : V) : replace A u u' v v' (inl x) (inl y) =
    if x = u ∧ y = u' ∨ x = v ∧ y = v' then 0 else A x y := rfl

private theorem replace_inl_inr (x : V) (k : Fin 4) : replace A u u' v v' (inl x) (inr k) =
    if x = u ∧ k = 0 then A u u' else if x = v ∧ k = 3 then A v v' else 0 := rfl

private theorem replace_inr_inl (k : Fin 4) (y : V) : replace A u u' v v' (inr k) (inl y) =
    if k = 3 ∧ y = u' ∨ k = 0 ∧ y = v' then 1 else 0 := rfl

private theorem replace_inr_inr (k l : Fin 4) :
    replace A u u' v v' (inr k) (inr l) = (gadget k l : R) := rfl

end Entries

variable [Fintype V]

/-- **The cycle covers of `G'` corresponding to a cycle cover `σ` of `G`.** They follow `σ` on
every vertex of `G` except the one whose edge the gadget replaces. If `σ` uses `u → u'`, they
enter the gadget from `u` at vertex `0` and leave it from vertex `3` to `u'`. Otherwise they
enter from `v` at vertex `3` and leave from vertex `0` to `v'`. These are the covers “that enter
the gadget at `u` and exit at `u'` or enter it at `v` and exit it at `v'`” of the proof of
Theorem 9.8. The set is meant for the covers `σ` that use exactly one of the two edges. -/
def lift (u u' v v' : V) (σ : Perm V) : Finset (Perm (V ⊕ Fin 4)) :=
  univ.filter fun π =>
    if σ u = u' then
      π (inl u) = inr 0 ∧ π (inr 3) = inl u' ∧ ∀ x, x ≠ u → π (inl x) = inl (σ x)
    else
      π (inl v) = inr 3 ∧ π (inr 0) = inl v' ∧ ∀ x, x ≠ v → π (inl x) = inl (σ x)

private theorem mem_lift {u u' v v' : V} {σ : Perm V} {π : Perm (V ⊕ Fin 4)} :
    π ∈ lift u u' v v' σ ↔ if σ u = u' then
      π (inl u) = inr 0 ∧ π (inr 3) = inl u' ∧ ∀ x, x ≠ u → π (inl x) = inl (σ x)
    else
      π (inl v) = inr 3 ∧ π (inr 0) = inl v' ∧ ∀ x, x ≠ v → π (inl x) = inl (σ x) := by
  simp only [lift, mem_filter, mem_univ, true_and]

omit [Fintype V] [DecidableEq V] in
/-- Two permutations that agree outside one point are equal. -/
private theorem eq_of_forall_ne {σ τ : Perm V} (s : V) (h : ∀ x, x ≠ s → σ x = τ x) :
    σ = τ := by
  ext x
  by_cases hx : x = s
  · subst hx
    by_contra hne
    have hy : τ.symm (σ x) ≠ x := fun he => hne (by
      have := τ.apply_symm_apply (σ x)
      rw [he] at this
      exact this.symm)
    exact hy (σ.injective ((h _ hy).trans (apply_symm_apply τ _)))
  · exact h x hx

omit [Fintype V] [DecidableEq V] in
/-- A cover cannot enter the gadget both from `u` at vertex `0` and from `v` at vertex `3`
while following `σ` outside `u`. -/
private theorem not_route_both {u v : V} {σ : Perm V} {π : Perm (V ⊕ Fin 4)}
    (hu : π (inl u) = inr 0) (hσ : ∀ x, x ≠ u → π (inl x) = inl (σ x))
    (hv : π (inl v) = inr 3) : False := by
  by_cases huv : v = u
  · subst huv
    exact absurd (inr_injective (hu.symm.trans hv)) (by decide)
  · exact inr_ne_inl (hv.symm.trans (hσ v huv))

/-- **Distinct cycle covers of `G` correspond to disjoint sets of cycle covers of `G'`.** -/
theorem disjoint_lift {u u' v v' : V} {σ τ : Perm V} (hστ : σ ≠ τ) :
    Disjoint (lift u u' v v' σ) (lift u u' v v' τ) := by
  refine disjoint_left.2 fun π hσ hτ => ?_
  rw [mem_lift] at hσ hτ
  split_ifs at hσ hτ
  · exact hστ (eq_of_forall_ne u fun x hx =>
      inl_injective ((hσ.2.2 x hx).symm.trans (hτ.2.2 x hx)))
  · exact not_route_both hσ.1 hσ.2.2 hτ.1
  · exact not_route_both hτ.1 hτ.2.2 hσ.1
  · exact hστ (eq_of_forall_ne v fun x hx =>
      inl_injective ((hσ.2.2 x hx).symm.trans (hτ.2.2 x hx)))

/-- The rows on which a route through the gadget is prescribed: all vertices of `G` and the
exit `j`. -/
private def routeRows (j : Fin 4) : Finset (V ⊕ Fin 4) :=
  insert (inr j) (univ.map Embedding.inl)

/-- The prescribed successors of a route of `σ` that enters the gadget from `s` at `i`. -/
private def routeTo (s : V) (i : Fin 4) (σ : Perm V) : V ⊕ Fin 4 → V ⊕ Fin 4 :=
  Sum.elim (fun x => if x = s then inr i else inl (σ x)) fun _ => inl (σ s)

private theorem prescribed_iff {s : V} {i j : Fin 4} {σ : Perm V} {π : Perm (V ⊕ Fin 4)} :
    (∀ z ∈ routeRows j, π z = routeTo s i σ z) ↔
      π (inl s) = inr i ∧ π (inr j) = inl (σ s) ∧ ∀ x, x ≠ s → π (inl x) = inl (σ x) := by
  simp only [routeRows, routeTo, mem_insert, mem_map, mem_univ, true_and,
    Embedding.inl_apply, forall_eq_or_imp, Sum.elim_inr, forall_exists_index,
    forall_apply_eq_imp_iff, Sum.elim_inl]
  constructor
  · rintro ⟨h2, h3⟩
    exact ⟨by simpa using h3 s, h2, fun x hx => by simpa [hx] using h3 x⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, fun x => ?_⟩
    split_ifs with hx
    · exact hx ▸ h1
    · exact h3 x hx

private theorem routeTo_injOn (s : V) (i j : Fin 4) (σ : Perm V) :
    Set.InjOn (routeTo s i σ) ↑(routeRows (V := V) j) := by
  have key : ∀ x, routeTo s i σ (inl x) = inl (σ s) → False := fun x h => by
    by_cases hx : x = s <;> simp_all [routeTo]
  rintro (x₁ | k₁) h₁ (x₂ | k₂) h₂ he
  · by_cases hx₁ : x₁ = s <;> by_cases hx₂ : x₂ = s <;> simp_all [routeTo]
  · exact (key x₁ he).elim
  · exact (key x₂ he.symm).elim
  · simp only [routeRows, coe_insert, Set.mem_insert_iff, coe_map, Set.mem_image, coe_univ,
      Set.mem_univ, true_and, Embedding.inl_apply, reduceCtorEq, exists_false, or_false,
      inr.injEq] at h₁ h₂
    rw [h₁, h₂]

private theorem univ_sdiff_routeRows (j : Fin 4) :
    univ \ routeRows (V := V) j = univ.map Embedding.inr \ {inr j} := by
  ext (x | k) <;> simp [routeRows]

private theorem image_routeTo (s : V) (i j : Fin 4) (σ : Perm V) :
    (routeRows j).image (routeTo s i σ) = insert (inr i) (univ.map Embedding.inl) := by
  ext w
  simp only [mem_image, routeRows, mem_insert, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with rfl | ⟨x, rfl⟩
    · exact Or.inr ⟨σ s, rfl⟩
    · by_cases hx : x = s
      · exact Or.inl (by simp [routeTo, hx])
      · exact Or.inr ⟨σ x, by simp [routeTo, hx]⟩
  · rintro (rfl | ⟨y, rfl⟩)
    · exact ⟨inl s, Or.inr ⟨s, rfl⟩, by simp [routeTo]⟩
    · by_cases hy : y = σ s
      · exact ⟨inr j, Or.inl rfl, by simp [routeTo, hy]⟩
      · have hne : σ.symm y ≠ s := fun h => hy (by rw [← h, apply_symm_apply])
        exact ⟨inl (σ.symm y), Or.inr ⟨_, rfl⟩, by simp [routeTo, hne]⟩

private theorem univ_sdiff_image_routeTo (s : V) (i j : Fin 4) (σ : Perm V) :
    univ \ (routeRows j).image (routeTo s i σ) = univ.map Embedding.inr \ {inr i} := by
  rw [image_routeTo]
  ext (y | k) <;> simp

/-- **The covers following a route.** Let `M` be a digraph containing the gadget with an edge
from `s` into its vertex `i` and from its vertex `j` to `s'`. If `σ` uses `s → s'` and not
`r → r'`, the covers of `M` following `σ` through the gadget weigh `4` times `σ` in `A`. -/
private theorem sum_routes (M : Matrix (V ⊕ Fin 4) (V ⊕ Fin 4) R) (A : Matrix V V R)
    {s s' r r' : V} {i j : Fin 4}
    (hV : ∀ x y, M (inl x) (inl y) = if x = s ∧ y = s' ∨ x = r ∧ y = r' then 0 else A x y)
    (hin : M (inl s) (inr i) = A s s') (hout : M (inr j) (inl s') = 1)
    (hminor : permOn M (univ.map Embedding.inr \ {inr j}) (univ.map Embedding.inr \ {inr i}) = 4)
    {σ : Perm V} (hs : σ s = s') (hr : σ r ≠ r') :
    ∑ π : Perm (V ⊕ Fin 4) with ∀ z ∈ routeRows j, π z = routeTo s i σ z, ∏ z, M z (π z) =
      4 * ∏ x, A x (σ x) := by
  rw [sum_perm_filter_eq_mul_permOn M _ _ (routeTo_injOn s i j σ), univ_sdiff_routeRows,
    univ_sdiff_image_routeTo, hminor, mul_comm, routeRows,
    prod_insert (by simp), prod_map]
  simp only [routeTo, Sum.elim_inr, Embedding.inl_apply, Sum.elim_inl, hs, hout, one_mul]
  congr 1
  refine prod_congr rfl fun x _ => ?_
  by_cases hx : x = s
  · subst hx
    rw [ite_eq_left rfl, hin, hs]
  · rw [ite_eq_right hx, hV]
    refine ite_eq_right fun h => ?_
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact hx rfl
    · exact hr h

/-- **Exercise 9.3, the corresponding covers.** Let `σ` be a cycle cover of `G` that uses exactly
one of the edges `u → u'` and `v → v'`. The cycle covers of `G'` corresponding to `σ` have total
weight `4` times the weight of `σ`. -/
theorem sum_lift (A : Matrix V V R) {u u' v v' : V} {σ : Perm V}
    (hσ : Xor (σ u = u') (σ v = v')) :
    ∑ π ∈ lift u u' v v' σ, ∏ z, replace A u u' v v' z (π z) = 4 * ∏ x, A x (σ x) := by
  have hM := replace_inr_inr A u u' v v'
  rcases hσ with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · have hlift : lift u u' v v' σ =
        univ.filter fun π => ∀ z ∈ routeRows 3, π z = routeTo u 0 σ z := by
      ext π
      simp only [mem_lift, hu, ite_true, mem_filter, mem_univ, true_and, prescribed_iff]
    rw [hlift]
    refine sum_routes _ A (replace_inl_inl A u u' v v') (by simp [replace_inl_inr])
      (by simp [replace_inr_inl]) ?_ hu hv
    simpa [exit, entry] using permOn_minor _ hM {0} {0}
  · have hlift : lift u u' v v' σ =
        univ.filter fun π => ∀ z ∈ routeRows 0, π z = routeTo v 3 σ z := by
      ext π
      simp only [mem_lift, hu, hv, ite_false, mem_filter, mem_univ, true_and, prescribed_iff]
    rw [hlift]
    refine sum_routes _ A (fun x y => by rw [replace_inl_inl]; split_ifs <;> first | rfl | tauto) ?_
      (by simp [replace_inr_inl]) ?_ hv hu
    · rw [replace_inl_inr]
      by_cases h : v = u <;> simp [h]
    · simpa [exit, entry] using permOn_minor _ hM {1} {1}

/-- The gadget block of a matrix on `V ⊕ Fin 4`. -/
private def inner (M : Matrix (V ⊕ Fin 4) (V ⊕ Fin 4) R) : Matrix (V ⊕ Fin 4) (V ⊕ Fin 4) R :=
  of fun z w => if z.isRight ∧ w.isRight then M z w else 0

/-- A matrix on `V ⊕ Fin 4` outside its gadget block. -/
private def outer (M : Matrix (V ⊕ Fin 4) (V ⊕ Fin 4) R) : Matrix (V ⊕ Fin 4) (V ⊕ Fin 4) R :=
  of fun z w => if z.isRight ∧ w.isRight then 0 else M z w

omit [Fintype V] [DecidableEq V] in
private theorem inner_add_outer (M : Matrix (V ⊕ Fin 4) (V ⊕ Fin 4) R) :
    inner M + outer M = M := by
  ext z w
  simp only [inner, outer, Matrix.add_apply, Matrix.of_apply]
  split_ifs <;> simp

/-- The vertices of `G`, with `s'` standing for the gadget vertex `i`. -/
private def portCols (s' : V) (i : Fin 4) : V ↪ V ⊕ Fin 4 :=
  ⟨fun y => if y = s' then inr i else inl y, fun y₁ y₂ he => by
    by_cases h₁ : y₁ = s' <;> by_cases h₂ : y₂ = s' <;> simp_all⟩

omit [Fintype V] in
private theorem portCols_apply (s' : V) (i : Fin 4) (y : V) :
    portCols s' i y = if y = s' then inr i else inl y := rfl

private theorem erase_insert_eq_map_portCols (s' : V) (i : Fin 4) :
    (insert (inr i) (univ.map Embedding.inl)).erase (inl s') = univ.map (portCols s' i) := by
  ext (y | k)
  · simp only [mem_erase, ne_eq, inl.injEq, mem_insert, reduceCtorEq, mem_map, mem_univ,
      Embedding.inl_apply, true_and, exists_eq, or_true, and_true, portCols_apply]
    constructor
    · intro hy
      exact ⟨y, by simp [hy]⟩
    · rintro ⟨a, ha⟩ rfl
      by_cases has : a = y <;> simp_all
  · simp only [mem_erase, ne_eq, reduceCtorEq, not_false_eq_true, mem_insert, inr.injEq,
      mem_map, mem_univ, Embedding.inl_apply, exists_false, or_false, true_and, portCols_apply]
    constructor
    · rintro rfl
      exact ⟨s', by simp⟩
    · rintro ⟨a, ha⟩
      by_cases has : a = s' <;> simp_all

/-- **A port of the eliminated gadget.** Let `D` be a digraph with an edge from `s` into the
gadget vertex `i`, of weight `A s s'`, and from the gadget vertex `j` to `s'`, of weight `1`,
which agrees with `A` on `V` except that the edges `s → s'` and `r → r'` are missing. Its
permanent sum from `V` and `j` onto `V` and `i` is the total weight in `A` of the covers that use
`s → s'` and not `r → r'`. -/
private theorem permOn_port (D : Matrix (V ⊕ Fin 4) (V ⊕ Fin 4) R) (A : Matrix V V R)
    {s s' r r' : V} {i j : Fin 4} (hne : (s, s') ≠ (r, r'))
    (hV : ∀ x y, D (inl x) (inl y) = if x = s ∧ y = s' ∨ x = r ∧ y = r' then 0 else A x y)
    (hin : ∀ x, D (inl x) (inr i) = if x = s then A s s' else 0)
    (hout : ∀ y, D (inr j) (inl y) = if y = s' then 1 else 0)
    (hji : D (inr j) (inr i) = 0) :
    permOn D (insert (inr j) (univ.map Embedding.inl)) (insert (inr i) (univ.map Embedding.inl)) =
      ∑ σ : Perm V, if σ s = s' ∧ σ r ≠ r' then ∏ x, A x (σ x) else 0 := by
  have hj : inr j ∉ univ.map (Embedding.inl : V ↪ V ⊕ Fin 4) := by simp
  rw [permOn_laplace D (mem_insert_self _ _), erase_insert hj,
    sum_eq_single_of_mem (inl s') (mem_insert_of_mem (by simp)) fun y hy hys => ?zero]
  case zero =>
    rcases mem_insert.1 hy with rfl | hy
    · rw [hji, zero_mul]
    · obtain ⟨y, -, rfl⟩ := mem_map.1 hy
      rw [Embedding.inl_apply, hout, ite_eq_right (fun h : y = s' => hys (by rw [h]; rfl)),
        zero_mul]
  have hN : ∀ x y, D (inl x) (portCols s' i y) =
      if y = s' then (if x = s then A s s' else 0) else (if x = r ∧ y = r' then 0 else A x y) := by
    intro x y
    by_cases hy : y = s'
    · simp [portCols_apply, hy, hin]
    · simp [portCols_apply, hy, hV]
  rw [hout, ite_eq_left rfl, one_mul, erase_insert_eq_map_portCols, permOn_map_map,
    permOn_univ_eq_sum]
  refine sum_congr rfl fun σ _ => ?_
  simp only [of_apply, Embedding.inl_apply, hN]
  by_cases hs : σ s = s'
  · by_cases hr : σ r = r'
    · rw [ite_eq_right fun h => h.2 hr]
      have hrs : σ r ≠ s' := fun he => hne (by
        have := σ.injective (he.trans hs.symm)
        subst this
        rw [← hs, ← hr])
      exact prod_eq_zero (mem_univ r) (by rw [ite_eq_right hrs, ite_eq_left ⟨rfl, hr⟩])
    · rw [ite_eq_left ⟨hs, hr⟩]
      refine prod_congr rfl fun x _ => ?_
      by_cases hx : σ x = s'
      · have : x = s := σ.injective (hx.trans hs.symm)
        subst this
        simp [hs]
      · rw [ite_eq_right hx, ite_eq_right]
        rintro ⟨rfl, h'⟩
        exact hr h'
  · rw [ite_eq_right fun h => hs h.1]
    refine prod_eq_zero (mem_univ (σ.symm s')) ?_
    rw [apply_symm_apply, ite_eq_left rfl, ite_eq_right]
    intro he
    exact hs (by rw [← he, apply_symm_apply])

/-- **Exercise 9.3, the permanent of `G'`.** If the replaced edges `u → u'` and `v → v'` are
distinct, the permanent of `G'` is `4` times the total weight of the cycle covers of `G` that use
exactly one of them. -/
theorem permanent_replace (A : Matrix V V R) {u u' v v' : V} (huv : (u, u') ≠ (v, v')) :
    (replace A u u' v v').permanent =
      4 * ∑ σ : Perm V with Xor (σ u = u') (σ v = v'), ∏ x, A x (σ x) := by
  set M := replace A u u' v v'
  have hArow : ∀ z, (∀ a, z ≠ Embedding.inr a) → ∀ w, inner M z w = 0 := by
    rintro (x | a) hz w
    · simp [inner]
    · exact absurd rfl (hz a)
  have hAcol : ∀ w, (∀ b, w ≠ Embedding.inr b) → ∀ z, inner M z w = 0 := by
    rintro (y | b) hw z
    · simp [inner]
    · exact absurd rfl (hw b)
  have hDrow : ∀ a, (∀ q, a ≠ exit q) → ∀ w, outer M (Embedding.inr a) w = 0 := by
    intro a ha w
    have h3 : a ≠ 3 := ha 0
    have h0 : a ≠ 0 := ha 1
    rcases w with y | b
    · simp [outer, M, replace_inr_inl, h3, h0]
    · simp [outer]
  have hDcol : ∀ b, (∀ p, b ≠ entry p) → ∀ z, outer M z (Embedding.inr b) = 0 := by
    intro b hb z
    have h0 : b ≠ 0 := hb 0
    have h3 : b ≠ 3 := hb 1
    rcases z with x | a
    · simp [outer, M, replace_inl_inr, h3, h0]
    · simp [outer]
  have hinner : ∀ a b, inner M (inr a) (inr b) = (gadget a b : R) := fun a b => by
    simp [inner, M, replace_inr_inr]
  have hset : ∀ k : Fin 4, univ \ univ.map Embedding.inr ∪ {inr k} =
      insert (inr k) (univ.map (Embedding.inl : V ↪ V ⊕ Fin 4)) := by
    intro k
    ext (x | l) <;> simp [or_comm]
  have hsum : ∀ f : Finset (Fin 2) → Finset (Fin 2) → R,
      ∑ Out, ∑ In, (if Out = In ∧ Out.card = 1 then (4 : R) else 0) * f Out In =
        4 * f {0} {0} + 4 * f {1} {1} := by
    intro f
    simp only [ite_mul, zero_mul, ite_and, sum_ite_eq, mem_univ, ite_true]
    rw [← sum_filter, show univ.filter (fun Out : Finset (Fin 2) => Out.card = 1) = {{0}, {1}}
      by decide, sum_pair (by decide)]
  rw [permanent_eq_permOn, ← inner_add_outer M,
    permOn_add_of_gadget Embedding.inr entry exit (inner M) (outer M) hArow hAcol hDrow hDcol
      (subset_univ _) (subset_univ _)]
  simp only [permOn_minor (inner M) hinner]
  rw [hsum]
  simp only [map_singleton, entry, exit, Embedding.coeFn_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Embedding.inr_apply, hset]
  rw [permOn_port (outer M) A huv (fun x y => by simp [outer, M, replace_inl_inl])
      (fun x => by simp [outer, M, replace_inl_inr]) (fun y => by simp [outer, M, replace_inr_inl])
      (by simp [outer]),
    permOn_port (outer M) A huv.symm
      (fun x y => by
        simp only [outer, M, of_apply, isRight_inl, Bool.false_eq_true, and_false, ite_false,
          replace_inl_inl]
        split_ifs <;> first | rfl | tauto)
      (fun x => by
        simp only [outer, M, of_apply, isRight_inl, Bool.false_eq_true, false_and, ite_false,
          replace_inl_inr]
        by_cases h : x = u <;> simp [h])
      (fun y => by simp [outer, M, replace_inr_inl]) (by simp [outer]),
    ← mul_add, ← sum_add_distrib, sum_filter]
  refine congrArg _ (sum_congr rfl fun σ _ => ?_)
  by_cases h₁ : σ u = u' <;> by_cases h₂ : σ v = v' <;> simp [h₁, h₂, xor_def]

/-- **Exercise 9.3, the remaining covers.** If the replaced edges are distinct, the cycle covers
of `G'` that correspond to no cycle cover of `G` using exactly one of the two edges have total
weight `0`. -/
theorem sum_filter_notMem_lift (A : Matrix V V R) {u u' v v' : V} (huv : (u, u') ≠ (v, v')) :
    ∑ π : Perm (V ⊕ Fin 4) with
        ∀ σ : Perm V, Xor (σ u = u') (σ v = v') → π ∉ lift u u' v v' σ,
      ∏ z, replace A u u' v v' z (π z) = 0 := by
  set L := (univ.filter fun σ : Perm V => Xor (σ u = u') (σ v = v')).biUnion (lift u u' v v')
  have hL : ∑ π ∈ L, ∏ z, replace A u u' v v' z (π z) = (replace A u u' v v').permanent := by
    rw [sum_biUnion fun σ _ τ _ hστ => disjoint_lift hστ, permanent_replace A huv, mul_sum]
    exact sum_congr rfl fun σ hσ => sum_lift A (mem_filter.1 hσ).2
  have hfilter : (univ.filter fun π : Perm (V ⊕ Fin 4) =>
      ∀ σ : Perm V, Xor (σ u = u') (σ v = v') → π ∉ lift u u' v v' σ) = univ \ L := by
    ext π
    simp [L]
  rw [hfilter]
  have htot := sum_sdiff (f := fun π : Perm (V ⊕ Fin 4) => ∏ z, replace A u u' v v' z (π z))
    (subset_univ L)
  rw [hL, ← permOn_univ_eq_sum, ← permanent_eq_permOn] at htot
  exact add_eq_right.1 htot

end Cslib.Complexity.XorGadget
