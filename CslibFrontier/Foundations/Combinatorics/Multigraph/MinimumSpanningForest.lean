/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Multigraph
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Minimum spanning forests of multigraphs

For a multigraph `ends : E → Sym2 V` (parallel edges and self-loops allowed), a finite set
`S : Finset E` of its edges and weights `w : E → W` in a linear order, the minimum spanning
forest `Cslib.Multigraph.msf ends w S` consists of the edges `e ∈ S` whose ends are not joined by
the edges of `S` strictly lighter than `e`. A self-loop is never in it. With distinct weights this
is the usual minimum spanning forest: it is a spanning forest of `S`
(`Cslib.Multigraph.isSpanningForest_msf`) of least total weight among all spanning forests of `S`
(`Cslib.Multigraph.sum_msf_le`).

Edges are joined along walks: `Cslib.Multigraph.Joins ends S u v` says that `u` and `v` are
joined by edges of `S`, that is, are reachable from each other in the multigraph restricted to `S`
(`Cslib.Multigraph.joins_iff_reachable`). An edge `e` is *supported* by a set `F` of edges when
the edges of `F` of weight at most `w e` join its ends (`Cslib.Multigraph.Supported`).

The module proves, in this setting, the standard facts of §2 of
[Khanna, Putterman and Song][KhannaPuttermanSong2026] (the paper's Facts 2.2–2.4, p. 11, and
Fact 2.5, p. 12) and the filtering identity behind line 8 of their Algorithm 2 (§4, p. 25). These
are steps in the proof of their Theorem 4.1 (§4, p. 25), tracked in #8325, and the paper's numbers
are kept as pointers. Distinct weights are assumed, as in the paper, through `Function.Injective w`,
and only where needed: the cut and cycle properties, threshold connectivity and the first filtering
lemma hold for all weights.

The contraction property is stated without changing the vertex type: contracting a set `C` of
edges is the vertex map `q` that identifies exactly the vertices joined by `C`, and the contracted
multigraph is `Sym2.map q ∘ ends` on the same edges. `Cslib.Multigraph.contract` is one such map.

## Main definitions

* `Cslib.Multigraph.Joins`: `u` and `v` are joined by edges of `S`.
* `Cslib.Multigraph.contract`: a vertex map identifying exactly the vertices joined by `C`.
* `Cslib.Multigraph.support`: the non-isolated vertices of a set of edges.
* `Cslib.Multigraph.msf`: the minimum spanning forest of a finite set of edges.
* `Cslib.Multigraph.Supported`, `Cslib.Multigraph.unsupported`: edges whose ends are joined by
  edges of `F` no heavier than them, and the edges of `S` that are not.
* `Cslib.Multigraph.IsAcyclic`: no edge of `F` has its ends joined by the other edges of `F`
  (`Cslib.Multigraph.isAcyclic_iff`, `Cslib.Multigraph.IsAcyclic.mono`).
* `Cslib.Multigraph.IsSpanningForest`: an acyclic subset of `S` joining the ends of every edge of
  `S`.

## Main results

* `Cslib.Multigraph.joins_iff_reachable`: `Joins` is reachability in the underlying simple graph
  of the restriction to `S`.
* `Cslib.Multigraph.joins_insert_iff`, `Cslib.Multigraph.joins_map_iff`: joining with one more
  edge, and joining in a contracted multigraph.
* `Cslib.Multigraph.mem_msf_of_mem_edgeCut`: the cut property (the paper's Fact 2.2): the
  lightest edge of `S` crossing a cut is in `msf S`.
* `Cslib.Multigraph.notMem_msf_of_joins`: the cycle property (the paper's Fact 2.3): an edge whose
  ends are joined by strictly lighter edges of `S` is not in `msf S`.
* `Cslib.Multigraph.msf_eq_union_msf_map`: the contraction property (the paper's Fact 2.4):
  `msf S = C ∪ msf (S \ C)` for `C ⊆ msf S`, the latter in the multigraph with `C` contracted.
* `Cslib.Multigraph.joins_msf_of_joins`: threshold connectivity (the paper's Fact 2.5): `msf S`
  preserves connectivity by the edges of weight at most `k`, for every threshold `k`.
* `Cslib.Multigraph.exists_bottleneck`: distinct vertices joined by `F` have a bottleneck edge
  `g ∈ F`, whose threshold `w g` is the least at which the edges of `F` join them.
* `Cslib.Multigraph.msf_eq_of_subset`, `Cslib.Multigraph.notMem_msf_of_supported`,
  `Cslib.Multigraph.msf_union_unsupported`: filtering. Any `S'` between `msf S` and `S` has the same
  minimum spanning forest; a supported edge outside `F ⊆ S` is not in `msf S`; and so
  `msf S = msf (F ∪ U(F))` (§3.1, p. 13; Algorithm 2, line 8, p. 25).
* `Cslib.Multigraph.isAcyclic_msf`, `Cslib.Multigraph.IsAcyclic.card_le`,
  `Cslib.Multigraph.card_msf_le`: `msf S` is acyclic, so it has at most `|X| - 1` edges when the
  ends of the edges of `S` lie in `X`.
* `Cslib.Multigraph.sum_card_incident_le`: the degrees in `S` add up to at most `2 |S|`.
* `Cslib.Multigraph.isSpanningForest_msf`, `Cslib.Multigraph.sum_msf_le`: `msf S` is a spanning
  forest of `S` of least total weight.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §2, pp. 11–12.
-/

public section

namespace Cslib.Multigraph

open Finset

variable {V V' E W : Type*} {ends : E → Sym2 V}

/-! ### Vertices joined by a set of edges -/

/-- `Joins ends S u v`: the vertices `u` and `v` are joined by a walk along edges of `S`. Every
vertex is joined to itself, by the empty walk. -/
@[expose] def Joins (ends : E → Sym2 V) (S : Set E) : V → V → Prop :=
  Relation.ReflTransGen fun a b => ∃ e ∈ S, ends e = s(a, b)

namespace Joins

variable {S T : Set E} {u v x : V}

@[refl] theorem refl (u : V) : Joins ends S u u :=
  Relation.ReflTransGen.refl

/-- An edge of `S` joins its ends. -/
theorem of_mem {e : E} (he : e ∈ S) (h : ends e = s(u, v)) : Joins ends S u v :=
  Relation.ReflTransGen.single ⟨e, he, h⟩

@[symm] theorem symm (h : Joins ends S u v) : Joins ends S v u := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨e, he, hab⟩ := hstep
    exact Relation.ReflTransGen.head ⟨e, he, hab.trans Sym2.eq_swap⟩ ih

@[trans] theorem trans (h₁ : Joins ends S u v) (h₂ : Joins ends S v x) : Joins ends S u x :=
  Relation.ReflTransGen.trans h₁ h₂

/-- `Joins ends S` is an equivalence relation. -/
theorem equivalence : Equivalence (Joins ends S) :=
  ⟨refl, symm, trans⟩

/-- Walks are carried along a vertex map `f` that sends the ends of every edge of `S` to vertices
joined by `T` in a multigraph `ends'`. -/
theorem lift {E' : Type*} {ends' : E' → Sym2 V'} {T : Set E'} (f : V → V')
    (hf : ∀ e ∈ S, ∀ a b, ends e = s(a, b) → Joins ends' T (f a) (f b))
    (h : Joins ends S u v) : Joins ends' T (f u) (f v) := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih =>
    obtain ⟨e, he, hab⟩ := hstep
    exact ih.trans (hf e he _ _ hab)

/-- If the ends of every edge of `S` are joined by `T`, then so is everything joined by `S`. -/
theorem of_forall (hf : ∀ e ∈ S, ∀ a b, ends e = s(a, b) → Joins ends T a b)
    (h : Joins ends S u v) : Joins ends T u v :=
  lift id hf h

theorem mono (hST : S ⊆ T) (h : Joins ends S u v) : Joins ends T u v :=
  h.of_forall fun _ he _ _ hab => of_mem (hST he) hab

/-- A walk from inside a set of vertices to outside it uses an edge leaving the set. -/
theorem exists_mem_edgeCut {P : Set V} (h : Joins ends S u v) (hu : u ∈ P) (hv : v ∉ P) :
    ∃ e ∈ S, e ∈ (toGraph ends).edgeCut P := by
  induction h with
  | refl => exact absurd hu hv
  | @tail b c _ hstep ih =>
    by_cases hb : b ∈ P
    · obtain ⟨e, he, hbc⟩ := hstep
      exact ⟨e, he, Graph.mem_edgeCut_iff.2 ⟨b, c, hbc, hb, hv⟩⟩
    · exact ih hb

end Joins

/-- No edges join only each vertex to itself. -/
@[simp] theorem joins_empty_iff {u v : V} : Joins ends ∅ u v ↔ u = v := by
  refine ⟨fun h => ?_, fun h => h ▸ Joins.refl _⟩
  induction h with
  | refl => rfl
  | tail _ hstep => exact absurd hstep.choose_spec.1 (Set.notMem_empty _)

/-- The vertices joined by `insert e S` are those joined by `S`, and those joined by `S` to the
two ends of `e`. -/
theorem joins_insert_iff {S : Set E} {e : E} {u v : V} :
    Joins ends (insert e S) u v ↔
      Joins ends S u v ∨ ∃ x y, ends e = s(x, y) ∧ Joins ends S u x ∧ Joins ends S y v := by
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | refl => exact Or.inl (Joins.refl _)
    | @tail b c _ hstep ih =>
      obtain ⟨f, hf, hbc⟩ := hstep
      rcases Set.mem_insert_iff.1 hf with rfl | hf
      · rcases ih with ih | ⟨x, y, hxy, hux, hyb⟩
        · exact Or.inr ⟨b, c, hbc, ih, Joins.refl _⟩
        · rcases Sym2.eq_iff.1 (hxy.symm.trans hbc) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr ⟨x, y, hxy, hux, Joins.refl _⟩
          · exact Or.inl hux
      · rcases ih with ih | ⟨x, y, hxy, hux, hyb⟩
        · exact Or.inl (ih.trans (Joins.of_mem hf hbc))
        · exact Or.inr ⟨x, y, hxy, hux, hyb.trans (Joins.of_mem hf hbc)⟩
  · rintro (h | ⟨x, y, hxy, hux, hyv⟩)
    · exact h.mono (Set.subset_insert _ _)
    · exact (hux.mono (Set.subset_insert _ _)).trans
        ((Joins.of_mem (Set.mem_insert _ _) hxy).trans (hyv.mono (Set.subset_insert _ _)))

/-- **`Joins` is reachability**: `u` and `v` are joined by edges of `S` exactly when they are
reachable from each other in the simple graph underlying the multigraph restricted to `S`. -/
theorem joins_iff_reachable {S : Set E} {u v : V} :
    Joins ends S u v ↔ (toSimpleGraph fun e : S => ends e).Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | @tail a b _ hstep ih =>
      obtain ⟨e, he, hab⟩ := hstep
      by_cases h : a = b
      · exact h ▸ ih
      · exact ih.tail (toSimpleGraph_adj.2 ⟨h, ⟨e, he⟩, hab⟩)
  · intro h
    induction h with
    | refl => exact Joins.refl _
    | tail _ hstep ih =>
      obtain ⟨-, ⟨e, he⟩, hab⟩ := toSimpleGraph_adj.1 hstep
      exact ih.trans (Joins.of_mem he hab)

/-- The ends of an edge are joined in either order, so it is enough to check one. -/
private theorem forall_joins_iff {S : Set E} {e : E} {a b : V} (h : ends e = s(a, b)) :
    (∀ x y, ends e = s(x, y) → Joins ends S x y) ↔ Joins ends S a b := by
  refine ⟨fun H => H a b h, fun hab x y hxy => ?_⟩
  rcases Sym2.eq_iff.1 (h.symm.trans hxy) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hab
  · exact hab.symm

private theorem exists_ends_eq (e : E) : ∃ a b, ends e = s(a, b) := by
  induction ends e using Sym2.ind with
  | _ a b => exact ⟨a, b, rfl⟩

/-! ### Non-isolated vertices -/

open scoped Classical in
/-- The **non-isolated vertices** of the edges `S`: the ends of the edges of `S` other than
self-loops. -/
noncomputable def support (ends : E → Sym2 V) (S : Finset E) : Finset V :=
  S.biUnion fun e => if (ends e).IsDiag then ∅ else (ends e).toFinset

theorem mem_support {S : Finset E} {v : V} :
    v ∈ support ends S ↔ ∃ e ∈ S, ¬(ends e).IsDiag ∧ v ∈ ends e := by
  classical
  simp only [support, mem_biUnion]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  split_ifs with h <;> simp [h, Sym2.mem_toFinset]

/-- **Degree sum**: every edge has at most two ends, so the numbers of edges of `S` at the
vertices of any `X` add up to at most `2 |S|`. A self-loop counts once at its vertex. -/
theorem sum_card_incident_le [DecidableEq V] (ends : E → Sym2 V) (S : Finset E) (X : Finset V) :
    ∑ v ∈ X, #{e ∈ S | v ∈ ends e} ≤ 2 * #S := by
  calc ∑ v ∈ X, #{e ∈ S | v ∈ ends e}
      = ∑ e ∈ S, #{v ∈ X | v ∈ ends e} := by
        simp only [card_filter]
        exact sum_comm
    _ ≤ ∑ _e ∈ S, 2 := sum_le_sum fun e _ => by
        obtain ⟨a, b, hab⟩ := exists_ends_eq (ends := ends) e
        calc #{v ∈ X | v ∈ ends e} ≤ #({a, b} : Finset V) := by
              refine card_le_card fun v hv => ?_
              have := (mem_filter.1 hv).2
              rw [hab] at this
              rcases Sym2.mem_iff.1 this with rfl | rfl <;> simp
          _ ≤ 2 := card_le_two
    _ = 2 * #S := by rw [sum_const, smul_eq_mul, mul_comm]

/-! ### Contraction -/

/-- **Contracted walks.** Let `q` identify exactly the vertices joined by `C`. Then vertices are
joined by `T` in the contracted multigraph `Sym2.map q ∘ ends` exactly when their preimages are
joined by `T ∪ C`. -/
theorem joins_map_iff {q : V → V'} {C T : Set E} (hq : ∀ u v, q u = q v ↔ Joins ends C u v)
    {u v : V} : Joins (Sym2.map q ∘ ends) T (q u) (q v) ↔ Joins ends (T ∪ C) u v := by
  constructor
  · intro h
    generalize hx : q u = x at h
    generalize hy : q v = y at h
    induction h generalizing v with
    | refl => exact ((hq u v).1 (hx.trans hy.symm)).mono Set.subset_union_right
    | @tail b c _ hstep ih =>
      obtain ⟨f, hf, hbc⟩ := hstep
      obtain ⟨a, d, had⟩ := exists_ends_eq (ends := ends) f
      simp only [Function.comp_apply, had, Sym2.map_mk, Sym2.eq_iff] at hbc
      have hfa : Joins ends (T ∪ C) a d := Joins.of_mem (Or.inl hf) had
      rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (ih rfl).trans (hfa.trans (((hq d v).1 hy.symm).mono Set.subset_union_right))
      · exact (ih rfl).trans (hfa.symm.trans (((hq a v).1 hy.symm).mono Set.subset_union_right))
  · refine Joins.lift q fun e he a b hab => ?_
    rcases he with he | he
    · exact Joins.of_mem he (by simp [hab])
    · rw [(hq a b).2 (Joins.of_mem he hab)]

/-- A vertex map identifying exactly the vertices joined by `C`: each vertex goes to a chosen
representative of its class, a vertex of the same type. -/
noncomputable def contract (ends : E → Sym2 V) (C : Set E) (u : V) : V :=
  letI : Setoid V := ⟨Joins ends C, Joins.equivalence⟩
  Quotient.out (⟦u⟧ : Quotient this)

theorem contract_eq_contract_iff {C : Set E} {u v : V} :
    contract ends C u = contract ends C v ↔ Joins ends C u v := by
  let : Setoid V := ⟨Joins ends C, Joins.equivalence⟩
  exact Quotient.out_inj.trans Quotient.eq

/-! ### Minimum spanning forests -/

variable [LinearOrder W] (w : E → W) {S : Finset E}

open scoped Classical in
/-- The **minimum spanning forest** of the edges `S`: the edges `e ∈ S` whose ends are not joined
by the edges of `S` strictly lighter than `e`. A self-loop is never in it. The paper defines the
minimum spanning forest only for distinct weights (§2, p. 11), and for injective `w` this set is
it (`Cslib.Multigraph.isSpanningForest_msf`, `Cslib.Multigraph.sum_msf_le`). With ties it need not
be a forest: two parallel edges of equal weight are both in it. -/
noncomputable def msf (ends : E → Sym2 V) (w : E → W) (S : Finset E) : Finset E :=
  {e ∈ S | ¬∀ a b, ends e = s(a, b) → Joins ends {f | f ∈ S ∧ w f < w e} a b}

/-- An edge with ends `a` and `b` is in `msf S` exactly when it is in `S` and `a` and `b` are not
joined by the strictly lighter edges of `S`. -/
theorem mem_msf_iff {e : E} {a b : V} (h : ends e = s(a, b)) :
    e ∈ msf ends w S ↔ e ∈ S ∧ ¬Joins ends {f | f ∈ S ∧ w f < w e} a b := by
  classical
  simp only [msf, mem_filter, forall_joins_iff h]

theorem msf_subset : msf ends w S ⊆ S := by
  classical
  exact filter_subset _ _

/-- A self-loop is never in `msf S`. -/
theorem notMem_msf_of_isDiag {e : E} (he : (ends e).IsDiag) : e ∉ msf ends w S := by
  obtain ⟨a, b, hab⟩ := exists_ends_eq (ends := ends) e
  rw [hab, Sym2.mk_isDiag_iff] at he
  subst he
  exact fun h => ((mem_msf_iff w hab).1 h).2 (Joins.refl _)

/-- **Cycle property**, a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (the
paper's Fact 2.3, §2, p. 11): an edge whose ends are joined by edges of `S` strictly lighter than
it is not in `msf S`. -/
theorem notMem_msf_of_joins {e : E} {X : Set E} (hX : X ⊆ S) (hlt : ∀ f ∈ X, w f < w e)
    {a b : V} (h : ends e = s(a, b)) (hj : Joins ends X a b) : e ∉ msf ends w S :=
  fun he => ((mem_msf_iff w h).1 he).2 (hj.mono fun f hf => ⟨hX hf, hlt f hf⟩)

/-- **Cut property**, a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (the
paper's Fact 2.2, §2, p. 11): an edge of `S` crossing a cut `(P, Pᶜ)` that is no heavier than any
edge of `S` crossing it is in `msf S`. -/
theorem mem_msf_of_mem_edgeCut {P : Set V} {e : E} (he : e ∈ S)
    (hcut : e ∈ (toGraph ends).edgeCut P)
    (hmin : ∀ f ∈ S, f ∈ (toGraph ends).edgeCut P → w e ≤ w f) : e ∈ msf ends w S := by
  obtain ⟨a, b, hab, ha, hb⟩ := Graph.mem_edgeCut_iff.1 hcut
  refine (mem_msf_iff w hab).2 ⟨he, fun hj => ?_⟩
  obtain ⟨f, ⟨hf, hlt⟩, hfcut⟩ := hj.exists_mem_edgeCut ha hb
  exact (hmin f hf hfcut).not_gt hlt

/-- Every edge of `S` has its ends joined by the edges of `msf S` that are no heavier. -/
theorem joins_msf_of_mem {e : E} (he : e ∈ S) {a b : V} (h : ends e = s(a, b)) :
    Joins ends {f | f ∈ msf ends w S ∧ w f ≤ w e} a b := by
  classical
  induction hn : #{f ∈ S | w f < w e} using Nat.strong_induction_on generalizing e a b with
  | _ n ih =>
  by_cases hm : e ∈ msf ends w S
  · exact Joins.of_mem ⟨hm, le_rfl⟩ h
  have hj : Joins ends {f | f ∈ S ∧ w f < w e} a b := by
    by_contra hj
    exact hm ((mem_msf_iff w h).2 ⟨he, hj⟩)
  refine hj.of_forall ?_
  rintro f ⟨hfS, hfe⟩ c d hf
  have hlt : #{g ∈ S | w g < w f} < n := by
    rw [← hn]
    refine card_lt_card ((ssubset_iff_of_subset fun g hg => ?_).2 ⟨f, ?_, ?_⟩)
    · simp only [mem_filter] at hg ⊢
      exact ⟨hg.1, hg.2.trans hfe⟩
    · simp [hfS, hfe]
    · simp
  exact (ih _ hlt hfS hf rfl).mono (by rintro g ⟨hg, hgf⟩; exact ⟨hg, hgf.trans hfe.le⟩)

/-- **Threshold connectivity**, a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026]
(the paper's Fact 2.5, §2, p. 12): vertices joined by edges of weight at most `k` from some
`X ⊆ S` are joined by the edges of `msf S` of weight at most `k`, for every threshold `k`. -/
theorem joins_msf_of_joins {X : Set E} (hX : X ⊆ S) {k : W} {u v : V}
    (h : Joins ends {f | f ∈ X ∧ w f ≤ k} u v) :
    Joins ends {f | f ∈ msf ends w S ∧ w f ≤ k} u v :=
  h.of_forall (by
    rintro f ⟨hf, hfk⟩ _ _ hab
    exact (joins_msf_of_mem w (hX hf) hab).mono (by
      rintro g ⟨hg, hgf⟩; exact ⟨hg, hgf.trans hfk⟩))

/-- `msf S` also preserves connectivity by the edges strictly lighter than any threshold `k`. -/
theorem joins_msf_lt_iff {k : W} {u v : V} :
    Joins ends {f | f ∈ msf ends w S ∧ w f < k} u v ↔
      Joins ends {f | f ∈ S ∧ w f < k} u v :=
  ⟨Joins.mono (by rintro f ⟨hf, hfk⟩; exact ⟨msf_subset w hf, hfk⟩),
    Joins.of_forall (by
      rintro f ⟨hf, hfk⟩ _ _ hab
      exact (joins_msf_of_mem w hf hab).mono (by
        rintro g ⟨hg, hgf⟩; exact ⟨hg, hgf.trans_lt hfk⟩))⟩

omit [LinearOrder W] in
/-- Distinct vertices are joined by a set of edges only if the set is nonempty. -/
theorem nonempty_of_joins {T : Finset E} {u v : V} (huv : u ≠ v)
    (h : Joins ends (T : Set E) u v) : T.Nonempty := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨b, -, e, he, -⟩
  · exact absurd rfl huv
  · exact ⟨e, he⟩

variable {w} in
/-- **Bottleneck edges.** Distinct vertices joined by a finite set `F` of edges have a
*bottleneck* edge `g ∈ F`: the edges of `F` of weight at most `w g` join them and those of weight
less than `w g` do not. With distinct weights it is unique, and when `F` is acyclic it is the
heaviest edge on the path of `F` between the two vertices. Any weights in a linear order will do. -/
theorem exists_bottleneck {F : Finset E} {u v : V} (huv : u ≠ v)
    (h : Joins ends (F : Set E) u v) :
    ∃ g ∈ F, Joins ends {x | x ∈ F ∧ w x ≤ w g} u v ∧
      ¬Joins ends {x | x ∈ F ∧ w x < w g} u v := by
  classical
  -- the lightest `g` whose threshold joins `u` and `v`; the heaviest edge of `F` is a candidate
  set A := F.filter fun g => Joins ends {x | x ∈ F ∧ w x ≤ w g} u v
  have hA : A.Nonempty := by
    obtain ⟨g, hg, hmax⟩ := F.exists_max_image w (nonempty_of_joins huv h)
    exact ⟨g, mem_filter.2 ⟨hg, h.mono (by intro x hx; exact ⟨hx, hmax x hx⟩)⟩⟩
  obtain ⟨g, hgA, hmin⟩ := A.exists_min_image w hA
  obtain ⟨hgF, hg⟩ := mem_filter.1 hgA
  refine ⟨g, hgF, hg, fun hlt => ?_⟩
  -- otherwise the heaviest edge below `w g` that is needed would be a lighter candidate
  set T := F.filter fun x => w x < w g
  have hT : Joins ends (T : Set E) u v :=
    hlt.mono (by rintro x ⟨hx, hxg⟩; exact mem_coe.2 (mem_filter.2 ⟨hx, hxg⟩))
  obtain ⟨g', hg'T, hg'max⟩ := T.exists_max_image w (nonempty_of_joins huv hT)
  obtain ⟨hg'F, hg'g⟩ := mem_filter.1 hg'T
  have : g' ∈ A := mem_filter.2 ⟨hg'F, hT.mono (by
    intro x hx
    exact ⟨(mem_filter.1 (mem_coe.1 hx)).1, hg'max x (mem_coe.1 hx)⟩)⟩
  exact absurd (hmin g' this) (not_le.2 hg'g)

/-- **Filtering**: any `S'` with `msf S ⊆ S' ⊆ S` has the same minimum spanning forest as
`S`. -/
theorem msf_eq_of_subset {S' : Finset E} (h₁ : msf ends w S ⊆ S') (h₂ : S' ⊆ S) :
    msf ends w S' = msf ends w S := by
  ext e
  obtain ⟨a, b, hab⟩ := exists_ends_eq (ends := ends) e
  have hj : Joins ends {f | f ∈ S' ∧ w f < w e} a b ↔
      Joins ends {f | f ∈ S ∧ w f < w e} a b :=
    ⟨Joins.mono (by rintro f ⟨hf, hfe⟩; exact ⟨h₂ hf, hfe⟩), fun h =>
      ((joins_msf_lt_iff w).2 h).mono (by rintro f ⟨hf, hfe⟩; exact ⟨h₁ hf, hfe⟩)⟩
  rw [mem_msf_iff w hab, mem_msf_iff w hab, hj]
  exact ⟨fun ⟨he, hn⟩ => ⟨h₂ he, hn⟩, fun ⟨he, hn⟩ =>
    ⟨h₁ ((mem_msf_iff w hab).2 ⟨he, hn⟩), hn⟩⟩

omit [LinearOrder W] in
/-- Dropping the self-loops does not change the non-isolated vertices. -/
theorem support_filter_not_isDiag [DecidableEq V] (ends : E → Sym2 V) (S : Finset E) :
    support ends {e ∈ S | ¬(ends e).IsDiag} = support ends S := by
  ext v
  simp only [mem_support, mem_filter]
  exact ⟨fun ⟨e, ⟨he, _⟩, h⟩ => ⟨e, he, h⟩, fun ⟨e, he, h⟩ => ⟨e, ⟨he, h.1⟩, h⟩⟩

/-- Dropping the self-loops does not change the minimum spanning forest. -/
theorem msf_filter_not_isDiag [DecidableEq V] (ends : E → Sym2 V) (S : Finset E) :
    msf ends w {e ∈ S | ¬(ends e).IsDiag} = msf ends w S :=
  msf_eq_of_subset w (fun _ he => mem_filter.2 ⟨msf_subset w he, fun h =>
    notMem_msf_of_isDiag w h he⟩) (filter_subset _ _)

/-! ### Acyclicity -/

/-- The set `F` of edges is **acyclic**: no edge of `F` has its ends joined by the other edges of
`F`. A self-loop, or a pair of parallel edges, is a cycle. -/
def IsAcyclic (ends : E → Sym2 V) (F : Set E) : Prop :=
  ∀ e ∈ F, ∀ a b, ends e = s(a, b) → ¬Joins ends (F \ {e}) a b

theorem isAcyclic_iff {F : Set E} :
    IsAcyclic ends F ↔ ∀ e ∈ F, ∀ a b, ends e = s(a, b) → ¬Joins ends (F \ {e}) a b :=
  Iff.rfl

theorem isAcyclic_empty : IsAcyclic ends (∅ : Set E) :=
  fun _ he => absurd he (Set.notMem_empty _)

/-- A subset of an acyclic set of edges is acyclic. -/
theorem IsAcyclic.mono {F G : Set E} (hG : IsAcyclic ends G) (hFG : F ⊆ G) : IsAcyclic ends F :=
  fun e he a b hab hj => hG e (hFG he) a b hab (hj.mono (by
    rintro f ⟨hf, hfe⟩
    exact ⟨hFG hf, hfe⟩))

/-- No subset `T` of `msf S` avoiding `e ∈ msf S` joins the ends of `e`. Induction on `T`: if
every edge of `T` is lighter than `e`, this is the definition of `msf`; otherwise the heaviest
edge `g` of `T` is either not needed, or its ends are joined through `e` by edges lighter than
`g`. -/
private theorem not_joins_of_subset_msf (hw : Function.Injective w) {e : E}
    (he : e ∈ msf ends w S) {a b : V} (hab : ends e = s(a, b)) (T : Finset E) :
    (T : Set E) ⊆ msf ends w S → e ∉ T → ¬Joins ends T a b := by
  classical
  induction T using Finset.strongInduction with
  | H T ih =>
  intro hT heT hj
  by_cases hlight : ∀ f ∈ T, w f < w e
  · exact notMem_msf_of_joins w (fun f hf => msf_subset w (hT hf)) hlight hab hj he
  push Not at hlight
  obtain ⟨f₀, hf₀T, hf₀⟩ := hlight
  obtain ⟨g, hgT, hgmax⟩ := T.exists_max_image w ⟨f₀, hf₀T⟩
  have hge : w e < w g :=
    lt_of_le_of_ne (hf₀.trans (hgmax f₀ hf₀T)) fun h => heT (hw h ▸ hgT)
  have hT' : ((T.erase g : Finset E) : Set E) ⊆ msf ends w S :=
    fun f hf => hT (mem_of_mem_erase hf)
  rw [← insert_erase hgT, coe_insert, joins_insert_iff] at hj
  rcases hj with hj | ⟨x, y, hxy, hax, hyb⟩
  · exact ih _ (erase_ssubset hgT) hT' (fun h => heT (mem_of_mem_erase h)) hj
  · have hsub : ((T.erase g : Finset E) : Set E) ⊆ {f | f ∈ S ∧ w f < w g} := fun f hf =>
      ⟨msf_subset w (hT' hf), lt_of_le_of_ne (hgmax f (mem_of_mem_erase hf))
        fun h => ne_of_mem_erase hf (hw h)⟩
    have he' : e ∈ {f | f ∈ S ∧ w f < w g} := ⟨msf_subset w he, hge⟩
    exact ((mem_msf_iff w hxy).1 (hT hgT)).2 ((hax.mono hsub).symm.trans
      ((Joins.of_mem he' hab).trans (hyb.mono hsub).symm))

/-- With distinct weights, `msf S` is acyclic. -/
theorem isAcyclic_msf (hw : Function.Injective w) : IsAcyclic ends (msf ends w S) := by
  classical
  intro e he a b hab hj
  refine not_joins_of_subset_msf w hw he hab ((msf ends w S).erase e)
    (fun f hf => mem_of_mem_erase hf) (fun h => (ne_of_mem_erase h) rfl) ?_
  rwa [coe_erase]

/-- An acyclic set of edges whose ends lie in `X` has at most `|X| - 1` edges. Induction on the
number of edges: contracting one edge of an acyclic set leaves an acyclic set on one vertex
fewer. -/
theorem IsAcyclic.card_le {F : Finset E} (hF : IsAcyclic ends F) {X : Finset V}
    (hX : ∀ e ∈ F, ∀ v ∈ ends e, v ∈ X) : #F ≤ #X - 1 := by
  classical
  induction hn : #F generalizing F ends X with
  | zero => exact Nat.zero_le _
  | succ n ih =>
  obtain ⟨e, he⟩ : F.Nonempty := card_pos.1 (by omega)
  obtain ⟨a, b, hab⟩ := exists_ends_eq (ends := ends) e
  have hne : a ≠ b := by
    rintro rfl
    exact hF e he a a hab (Joins.refl _)
  have haX : a ∈ X := hX e he a (by simp [hab])
  have hbX : b ∈ X := hX e he b (by simp [hab])
  -- contract `e`, sending `b` to `a`
  let q : V → V := fun x => if x = b then a else x
  have hq : ∀ u v, q u = q v ↔ Joins ends ({e} : Set E) u v := by
    have he1 : Joins ends ({e} : Set E) a b := Joins.of_mem rfl hab
    intro u v
    constructor
    · intro h
      by_cases hu : u = b <;> by_cases hv : v = b <;>
        simp only [q, hu, hv, ite_true, ite_false] at h
      · subst hu hv; rfl
      · subst hu h; exact he1.symm
      · subst hv h; exact he1
      · subst h; rfl
    · intro h
      induction h with
      | refl => rfl
      | @tail c d _ hstep ih =>
        obtain ⟨f, hf, hcd⟩ := hstep
        rw [Set.mem_singleton_iff.1 hf, hab, Sym2.eq_iff] at hcd
        refine ih.trans ?_
        rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [q]
  have hF' : IsAcyclic (Sym2.map q ∘ ends) (F.erase e) := by
    intro f hf x y hxy hj
    obtain ⟨c, d, hcd⟩ := exists_ends_eq (ends := ends) f
    have hfe : f ≠ e := ne_of_mem_erase hf
    rw [Function.comp_apply, hcd, Sym2.map_mk] at hxy
    have hj' : Joins (Sym2.map q ∘ ends) (↑(F.erase e) \ {f}) (q c) (q d) := by
      rcases Sym2.eq_iff.1 hxy with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rwa [h₁, h₂]
      · rw [h₁, h₂]; exact hj.symm
    refine hF f (mem_of_mem_erase hf) c d hcd (((joins_map_iff hq).1 hj').mono ?_)
    rintro g (⟨hg, hgf⟩ | rfl)
    · exact ⟨mem_of_mem_erase hg, hgf⟩
    · exact ⟨he, Ne.symm hfe⟩
  have hX' : ∀ f ∈ F.erase e, ∀ v ∈ (Sym2.map q ∘ ends) f, v ∈ X.erase b := by
    intro f hf v hv
    rw [Function.comp_apply, Sym2.mem_map] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    by_cases hcb : c = b
    · simp [q, hcb, hne, haX]
    · simp [q, hcb, hX f (mem_of_mem_erase hf) c hc]
  have := ih hF' hX' (by rw [card_erase_of_mem he]; omega)
  have h2 : 2 ≤ #X := by
    calc 2 = #{a, b} := (card_pair hne).symm
      _ ≤ #X := card_le_card (by simp [insert_subset_iff, haX, hbX])
  rw [card_erase_of_mem hbX] at this
  omega

/-- With distinct weights, `msf S` has at most `|X| - 1` edges when the ends of the edges of `S`
lie in `X`. -/
theorem card_msf_le (hw : Function.Injective w) {X : Finset V}
    (hX : ∀ e ∈ S, ∀ v ∈ ends e, v ∈ X) : #(msf ends w S) ≤ #X - 1 :=
  (isAcyclic_msf w hw).card_le fun e he => hX e (msf_subset w he)

/-! ### Contraction -/

/-- **Contraction property**, a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (the
paper's Fact 2.4, §2, p. 11): with distinct weights, if `C ⊆ msf S` and `q` identifies exactly the
vertices joined by `C`, then `msf S` is `C` together with the minimum spanning forest of the
remaining edges `S \ C` in the contracted multigraph `Sym2.map q ∘ ends`. -/
theorem msf_eq_union_msf_map [DecidableEq E] (hw : Function.Injective w) {C : Finset E}
    (hC : C ⊆ msf ends w S) {q : V → V'} (hq : ∀ u v, q u = q v ↔ Joins ends C u v) :
    msf ends w S = C ∪ msf (Sym2.map q ∘ ends) w (S \ C) := by
  classical
  ext e
  by_cases heC : e ∈ C
  · simp [heC, hC heC]
  obtain ⟨a, b, hab⟩ := exists_ends_eq (ends := ends) e
  have hab' : (Sym2.map q ∘ ends) e = s(q a, q b) := by simp [hab]
  rw [mem_union, mem_msf_iff w hab, mem_msf_iff w hab', joins_map_iff hq]
  simp only [heC, false_or, mem_sdiff, not_false_eq_true, and_true]
  refine and_congr_right fun heS => ⟨fun hn hj => ?_, fun hn hj => hn (hj.mono ?_)⟩
  · -- the edges joining the ends of `e` lie in `msf S`, without `e`, contradicting acyclicity
    refine isAcyclic_msf w hw e ((mem_msf_iff w hab).2 ⟨heS, hn⟩) a b hab (hj.of_forall ?_)
    rintro f (⟨hf, hfe⟩ | hf) c d hcd
    · exact (joins_msf_of_mem w hf.1 hcd).mono (by
        rintro g ⟨hg, hgf⟩
        exact ⟨hg, fun h => (hgf.trans_lt hfe).ne (congrArg w h)⟩)
    · exact Joins.of_mem ⟨hC hf, fun h => heC (h ▸ hf)⟩ hcd
  · rintro f ⟨hf, hfe⟩
    by_cases hfC : f ∈ C
    · exact Or.inr hfC
    · exact Or.inl ⟨⟨hf, hfC⟩, hfe⟩

/-! ### Support and filtering -/

/-- The edge `e` is **supported** by the set `F` of edges when the edges of `F` of weight at most
`w e` join its ends (§1.2, p. 5; §3.1, p. 13). -/
def Supported (ends : E → Sym2 V) (w : E → W) (F : Set E) (e : E) : Prop :=
  ∀ a b, ends e = s(a, b) → Joins ends {f | f ∈ F ∧ w f ≤ w e} a b

theorem supported_iff {F : Set E} {e : E} {a b : V} (h : ends e = s(a, b)) :
    Supported ends w F e ↔ Joins ends {f | f ∈ F ∧ w f ≤ w e} a b :=
  forall_joins_iff h

variable {w} in
/-- An edge supported by `F` is supported by every superset of `F`. -/
theorem Supported.mono {F G : Set E} (hFG : F ⊆ G) {e : E} (h : Supported ends w F e) :
    Supported ends w G e := fun a b hab =>
  (h a b hab).mono (by rintro f ⟨hf, hfe⟩; exact ⟨hFG hf, hfe⟩)

/-- Every edge of `F` is supported by `F`. -/
theorem supported_of_mem {F : Set E} {e : E} (he : e ∈ F) : Supported ends w F e :=
  fun _ _ hab => Joins.of_mem (by exact ⟨he, le_rfl⟩) hab

/-- An edge is supported by `msf S` exactly when it is supported by `S`, by Fact 2.5. -/
theorem supported_msf_iff {e : E} :
    Supported ends w ↑(msf ends w S) e ↔ Supported ends w ↑S e := by
  obtain ⟨a, b, hab⟩ := exists_ends_eq (ends := ends) e
  rw [supported_iff w hab, supported_iff w hab]
  exact ⟨Joins.mono (by rintro f ⟨hf, hfe⟩; exact ⟨msf_subset w hf, hfe⟩),
    joins_msf_of_joins w (X := ↑S) subset_rfl⟩

open scoped Classical in
/-- The edges of `S` not supported by `F`, the set `U(F)` of §3.1 (p. 13). -/
noncomputable def unsupported (ends : E → Sym2 V) (w : E → W) (F : Set E) (S : Finset E) :
    Finset E :=
  {e ∈ S | ¬Supported ends w F e}

theorem mem_unsupported {F : Set E} {e : E} :
    e ∈ unsupported ends w F S ↔ e ∈ S ∧ ¬Supported ends w F e := by
  classical
  simp [unsupported]

/-- **Filtering**: with distinct weights, an edge supported by a set `F ⊆ S` of edges and not in
`F` is not in `msf S`. -/
theorem notMem_msf_of_supported (hw : Function.Injective w) {F : Set E} (hFS : F ⊆ S) {e : E}
    (heF : e ∉ F) (hsup : Supported ends w F e) : e ∉ msf ends w S := by
  obtain ⟨a, b, hab⟩ := exists_ends_eq (ends := ends) e
  refine notMem_msf_of_joins w (X := {f | f ∈ F ∧ w f ≤ w e}) (fun f hf => hFS hf.1)
    (fun f ⟨hf, hfe⟩ => lt_of_le_of_ne hfe fun h => heF (hw h ▸ hf)) hab
    ((supported_iff w hab).1 hsup)

/-- **Filtering** (Algorithm 2, line 8, p. 25): with distinct weights, for every `F ⊆ S` the
minimum spanning forest of `S` is that of `F` together with the edges of `S` it does not
support. -/
theorem msf_union_unsupported [DecidableEq E] (hw : Function.Injective w) {F : Finset E}
    (hFS : F ⊆ S) :
    msf ends w (F ∪ unsupported ends w F S) = msf ends w S := by
  classical
  refine msf_eq_of_subset w (fun e he => ?_)
    (union_subset hFS fun e he => ((mem_unsupported w).1 he).1)
  by_cases heF : e ∈ F
  · exact mem_union_left _ heF
  · exact mem_union_right _ ((mem_unsupported w).2 ⟨msf_subset w he,
      fun hsup => notMem_msf_of_supported w hw (coe_subset.2 hFS) (mem_coe.not.2 heF) hsup he⟩)

/-! ### Weight optimality -/

/-- `F` is a **spanning forest** of the edges `S`: an acyclic subset of `S` that joins the ends of
every edge of `S`. -/
structure IsSpanningForest (ends : E → Sym2 V) (S F : Finset E) : Prop where
  /-- The forest consists of edges of `S`. -/
  subset : F ⊆ S
  /-- The forest is acyclic. -/
  isAcyclic : IsAcyclic ends F
  /-- The forest joins the ends of every edge of `S`. -/
  joins : ∀ e ∈ S, ∀ a b, ends e = s(a, b) → Joins ends F a b

/-- With distinct weights, `msf S` is a spanning forest of `S`. -/
theorem isSpanningForest_msf (hw : Function.Injective w) :
    IsSpanningForest ends S (msf ends w S) :=
  ⟨msf_subset w, isAcyclic_msf w hw, fun _ he _ _ hab =>
    (joins_msf_of_mem w he hab).mono (by rintro g ⟨hg, -⟩; exact hg)⟩

/-- Exchanging an edge `f` of an acyclic set for an edge `m` whose ends `F \ {f}` does not join
keeps the set acyclic. -/
private theorem IsAcyclic.exchange [DecidableEq E] {F : Finset E} (hF : IsAcyclic ends F)
    {f m : E} (hm : m ∉ F) {x y : V} (hxy : ends m = s(x, y))
    (hsep : ¬Joins ends ((F : Set E) \ {f}) x y) : IsAcyclic ends ↑(insert m (F.erase f)) := by
  intro h hh c d hcd hj
  rw [coe_insert, coe_erase] at hh
  rcases hh with rfl | ⟨hhF, hhf⟩
  · refine hsep ((forall_joins_iff hcd).2 (hj.mono ?_) x y hxy)
    rintro g ⟨hg, hgh⟩
    rw [coe_insert, coe_erase] at hg
    exact hg.resolve_left hgh
  · have hsub : ((insert m (F.erase f) : Finset E) : Set E) \ {h} ⊆
        insert m (((F : Set E) \ {f}) \ {h}) := by
      rintro g ⟨hg, hgh⟩
      rw [coe_insert, coe_erase] at hg
      rcases hg with rfl | hg
      · exact Or.inl rfl
      · exact Or.inr ⟨hg, hgh⟩
    rcases joins_insert_iff.1 (hj.mono hsub) with hj | ⟨x', y', hxy', hcx, hyd⟩
    · exact hF h hhF c d hcd (hj.mono (by rintro g ⟨⟨hg, -⟩, hgh⟩; exact ⟨hg, hgh⟩))
    · have hsub' : ((F : Set E) \ {f}) \ {h} ⊆ (F : Set E) \ {f} := Set.sdiff_subset
      have hh' : h ∈ (F : Set E) \ {f} := ⟨hhF, hhf⟩
      have hj' : Joins ends ((F : Set E) \ {f}) x' y' :=
        (hcx.mono hsub').symm.trans ((Joins.of_mem hh' hcd).trans (hyd.mono hsub').symm)
      rcases Sym2.eq_iff.1 (hxy.symm.trans hxy') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hsep hj'
      · exact hsep hj'.symm

/-- **Weight optimality**: with distinct weights in an ordered additive monoid, `msf S` has the
least total weight among the spanning forests of `S`. Each spanning forest `F ≠ msf S` exchanges
an edge outside `msf S` for a lighter edge of `msf S`, as in the cut property. -/
theorem sum_msf_le [AddCommMonoid W] [IsOrderedAddMonoid W] (hw : Function.Injective w)
    {F : Finset E} (hF : IsSpanningForest ends S F) :
    ∑ e ∈ msf ends w S, w e ≤ ∑ e ∈ F, w e := by
  classical
  set M := msf ends w S
  induction hn : #(F \ M) using Nat.strong_induction_on generalizing F with
  | _ n ih =>
  by_cases hFM : F \ M = ∅
  · -- `F ⊆ M`, so `F = M`, since `M` is acyclic and `F` joins the ends of every edge
    have hsub : F ⊆ M := sdiff_eq_empty_iff_subset.1 hFM
    have : M ⊆ F := by
      intro m hm
      by_contra hmF
      obtain ⟨a, b, hab⟩ := exists_ends_eq (ends := ends) m
      exact isAcyclic_msf w hw m hm a b hab ((hF.joins m (msf_subset w hm) a b hab).mono
        (by intro g hg; exact ⟨hsub hg, fun h => hmF (h ▸ hg)⟩))
    rw [subset_antisymm hsub this]
  obtain ⟨f, hf⟩ := nonempty_iff_ne_empty.2 hFM
  obtain ⟨hfF, hfM⟩ := mem_sdiff.1 hf
  obtain ⟨a, b, hab⟩ := exists_ends_eq (ends := ends) f
  have hfS := hF.subset hfF
  -- the ends of `f` are joined by edges of `M` lighter than `f`
  have hj : Joins ends {g | g ∈ M ∧ w g < w f} a b := by
    refine (joins_msf_lt_iff w).2 ?_
    by_contra hj
    exact hfM ((mem_msf_iff w hab).2 ⟨hfS, hj⟩)
  -- one of them, `m`, leaves the vertices joined to `a` by `F \ {f}`
  have hFf := hF.isAcyclic f hfF a b hab
  obtain ⟨m, ⟨hmM, hmf⟩, hcut⟩ :=
    hj.exists_mem_edgeCut (P := {v | Joins ends ((F : Set E) \ {f}) a v}) (Joins.refl _) hFf
  obtain ⟨x, y, hxy, hx, hy⟩ := Graph.mem_edgeCut_iff.1 hcut
  simp only [Set.mem_ofPred_eq] at hx hy
  have hsep : ¬Joins ends ((F : Set E) \ {f}) x y := fun h => hy (hx.trans h)
  have hmF : m ∉ F := fun hmF => hsep (Joins.of_mem ⟨hmF, fun h => (h ▸ hmf).false⟩ hxy)
  -- exchange `f` for `m`
  have hF' : IsSpanningForest ends S (insert m (F.erase f)) := by
    refine ⟨insert_subset (msf_subset w hmM) ((erase_subset _ _).trans hF.subset),
      hF.isAcyclic.exchange hmF hxy hsep, fun e he c d hcd => ?_⟩
    refine (hF.joins e he c d hcd).of_forall ?_
    intro g hg c' d' hg'
    by_cases hgf : g = f
    · subst hgf
      -- the ends of `f` are joined through `m`
      have hjxy := hF.joins m (msf_subset w hmM) x y hxy
      rw [← insert_erase hfF, coe_insert, coe_erase, joins_insert_iff] at hjxy
      have hsub : (F : Set E) \ {g} ⊆ ↑(insert m (F.erase g)) := fun h hh => by
        rw [coe_insert, coe_erase]; exact Or.inr hh
      have hm' : m ∈ (↑(insert m (F.erase g)) : Set E) := by simp
      rcases hjxy with h | ⟨x', y', hxy', hxx', hyy'⟩
      · exact absurd h hsep
      · refine (forall_joins_iff hab).2 ?_ c' d' hg'
        rcases Sym2.eq_iff.1 (hab.symm.trans hxy') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (hx.mono hsub).trans ((Joins.of_mem hm' hxy).trans (hyy'.mono hsub).symm)
        · exact absurd (hx.trans hxx') hFf
    · exact Joins.of_mem (by simp [hgf, mem_coe.1 hg]) hg'
  have hlt : #(insert m (F.erase f) \ M) < n := by
    rw [← hn]
    refine card_lt_card ((ssubset_iff_of_subset fun g hg => ?_).2
      ⟨f, hf, by simpa using fun h : f = m => h ▸ hmM⟩)
    simp only [mem_sdiff, mem_insert, mem_erase] at hg ⊢
    rcases hg with ⟨rfl | ⟨-, hg⟩, hgM⟩
    · exact absurd hmM hgM
    · exact ⟨hg, hgM⟩
  calc ∑ e ∈ M, w e ≤ ∑ e ∈ insert m (F.erase f), w e := ih _ hlt hF' rfl
    _ = w m + ∑ e ∈ F.erase f, w e := sum_insert fun h => hmF (mem_of_mem_erase h)
    _ ≤ w f + ∑ e ∈ F.erase f, w e := add_le_add hmf.le le_rfl
    _ = ∑ e ∈ F, w e := add_sum_erase _ _ hfF

end Cslib.Multigraph
