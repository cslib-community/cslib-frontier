/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Reduction
public import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.FinCases

/-!
# TSP polytopes and directed-to-undirected tour splits

This module defines the symmetric traveling salesman polytope `tspPolytope K V` (`TSP(V)`) on the
complete graph over a finite vertex type `V`, and formalizes the directed-to-undirected `3`-split
construction (with edge-subdivision padding on a distinguished vertex `v₀`) used in
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Step (iii) of Lemma 11].

Given an irreflexive directed graph `adjD : W → W → Prop` on `|W| ≥ 2` vertices, `paddedSplitGraph`
replaces each `w ≠ v₀` by a `3`-path `vIn w - vMid w 0 - vOut w` and `v₀` by a `(pad + 3)`-path
`vIn v₀ - vMid v₀ 0 - ... - vMid v₀ pad - vOut v₀`, adding `{vOut u, vIn w}` for each directed arc
`adjD u w`. Every undirected Hamiltonian tour of `paddedSplitGraph` comes from a directed
Hamiltonian cycle `τ : Fin |W| ≃ W` of `adjD` (`exists_dirTour_of_paddedSplitTour`), and every
directed Hamiltonian cycle lifts back to an undirected tour (`paddedSplitTour_of_dirTour`).

## Main definitions

* `tourEdgeSet`, `IsTourEdgeSet`: Hamiltonian tour edge sets on the complete graph `K_V`.
* `tspVertex`, `tspPolytope`: the symmetric TSP polytope `TSP(V)`.
* `SplitV`, `paddedSplitGraph`: the `3`-split undirected graph of a digraph with optional padding.
* `IsDirTour`: cyclic permutation `τ : Fin |W| ≃ W` traversing arcs of `adjD`.

## Main results

* `card_splitV`: `Fintype.card (SplitV W v₀ pad) = 3 * Fintype.card W + pad`.
* `exists_dirTour_of_paddedSplitTour`: every undirected tour of `paddedSplitGraph` induces a
  directed tour of `adjD` with matching inter-gadget edges.
* `paddedSplitTour_of_dirTour`: every directed tour of `adjD` lifts to an undirected tour of
  `paddedSplitGraph`.
* `tspPolytope_inter_subgraph_eq`: intersecting `TSP(V)` with `x_e = 0` for non-edges of `G`
  gives the convex hull of tours of `G`.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.4 (Lemma 11, Step (iii)).
-/

public section

section FinHelpers

private theorem fin_one_val {n : ℕ} [NeZero n] (hn : 1 < n) : (1 : Fin n).1 = 1 :=
  (Fin.val_one' n).trans (Nat.mod_eq_of_lt hn)

private theorem fin_mk_one {n : ℕ} [NeZero n] (hn : 1 < n) : (⟨1, hn⟩ : Fin n) = 1 :=
  Fin.ext (fin_one_val hn).symm

private theorem fin_val_add_one_eq_ite {n : ℕ} [NeZero n] (hn : 1 < n) (i : Fin n) :
    (i + 1).1 = if i.1 + 1 = n then 0 else i.1 + 1 := by
  rw [Fin.val_add, fin_one_val hn]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- `Fin.cast` commutes with the successor. -/
private theorem fin_cast_add_one {a b : ℕ} (hab : a = b) [NeZero a] [NeZero b] (k : Fin a) :
    Fin.cast hab (k + 1) = Fin.cast hab k + 1 := by
  subst hab
  rfl

end FinHelpers

section TSPPolytope

/-- Every vertex pair along a bijection `σ : Fin |V| ≃ V` at step `i` and `i + 1` is distinct
when `3 ≤ |V|`. -/
theorem tourEdge_mem_top_edgeSet {V : Type*} [Fintype V]
    (hV : 3 ≤ Fintype.card V) (σ : Fin (Fintype.card V) ≃ V) (i : Fin (Fintype.card V)) :
    s(σ i, σ (i + ⟨1, by omega⟩)) ∈ (⊤ : SimpleGraph V).edgeSet := by
  have : NeZero (Fintype.card V) := ⟨by omega⟩
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq,
    Fin.ext_iff, fin_mk_one (by omega), fin_val_add_one_eq_ite (by omega)]
  split_ifs <;> omega

/-- The edge set in `K_V` traced by the cyclic ordering `σ : Fin |V| ≃ V`. -/
@[expose] def tourEdgeSet {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Fin (Fintype.card V) ≃ V) (hV : 3 ≤ Fintype.card V) :
    Finset ↥(⊤ : SimpleGraph V).edgeSet :=
  Finset.univ.image fun i => ⟨s(σ i, σ (i + ⟨1, by omega⟩)), tourEdge_mem_top_edgeSet hV σ i⟩

/-- `F` is the edge set of a Hamiltonian cycle (tour) of `K_V` (`|V| ≥ 3`). -/
@[expose] def IsTourEdgeSet {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset ↥(⊤ : SimpleGraph V).edgeSet) : Prop :=
  ∃ (hV : 3 ≤ Fintype.card V) (σ : Fin (Fintype.card V) ≃ V), F = tourEdgeSet σ hV

/-- `F` is a Hamiltonian tour contained in the spanning subgraph `G : SimpleGraph V`. -/
@[expose] def IsSubgraphTour {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F : Finset ↥(⊤ : SimpleGraph V).edgeSet) : Prop :=
  IsTourEdgeSet F ∧ ∀ e ∈ F, e.1 ∈ G.edgeSet

section Polytope

variable (K : Type*) [Semiring K] [PartialOrder K]

/-- Characteristic vector of an edge set `F` in `K_V`. -/
@[expose] def tspVertex {V : Type*} [DecidableEq V]
    (F : Finset ↥(⊤ : SimpleGraph V).edgeSet) : ↥(⊤ : SimpleGraph V).edgeSet → K :=
  fun e => if e ∈ F then 1 else 0

/-- The symmetric **traveling salesman polytope** `TSP(V)`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4]. -/
@[expose] def tspPolytope (V : Type*) [Fintype V] [DecidableEq V] :
    Set (↥(⊤ : SimpleGraph V).edgeSet → K) :=
  convexHull K (Set.range fun F : {F // IsTourEdgeSet F} => tspVertex K F.1)

end Polytope

/-- Intersecting `TSP(V)` with `{x | c_nonEdge ⬝ᵥ x = 0}` selects the face of tours of `G`. -/
theorem tspPolytope_inter_subgraph_eq
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    let c : ↥(⊤ : SimpleGraph V).edgeSet → K := fun e => if e.1 ∈ G.edgeSet then 0 else -1
    tspPolytope K V ∩ {x | c ⬝ᵥ x = 0} =
      convexHull K (Set.range fun F : {F // IsSubgraphTour G F} => tspVertex K F.1) := by
  classical
  intro c
  have hdot (F : Finset ↥(⊤ : SimpleGraph V).edgeSet) :
      c ⬝ᵥ tspVertex K F = -((F.filter fun e => e.1 ∉ G.edgeSet).card : K) := by
    simp [dotProduct, c, tspVertex, Finset.sum_ite]
  rw [tspPolytope, convexHull_inter_dotProduct_eq fun F => by simp [hdot]]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Subtype.exists, hdot, neg_eq_zero,
    Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_not, IsSubgraphTour]
  exact ⟨fun ⟨F, hF, h, e⟩ => ⟨F, ⟨hF, h⟩, e⟩, fun ⟨F, ⟨hF, h⟩, e⟩ => ⟨F, hF, h, e⟩⟩

end TSPPolytope

section SplitGraph

/-- Middle chain length of `w` in `SplitV W v₀ pad`: `pad + 1` at `v₀` and `1` elsewhere. -/
@[expose] def splitMidLen {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (w : W) : ℕ :=
  if w = v₀ then pad + 1 else 1

/-- Vertices of the `3`-split undirected graph of a digraph on `W`, with `pad` extra middle
nodes inserted at `v₀` [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 11, Step (iii)]. -/
inductive SplitV (W : Type*) [DecidableEq W] (v₀ : W) (pad : ℕ) : Type _
  | vIn (w : W)
  | vMid (w : W) (k : Fin (splitMidLen v₀ pad w))
  | vOut (w : W)

private def splitVEquiv {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) :
    SplitV W v₀ pad ≃ W ⊕ (Σ w : W, Fin (splitMidLen v₀ pad w)) ⊕ W where
  toFun
    | .vIn w => Sum.inl w
    | .vMid w k => Sum.inr (Sum.inl ⟨w, k⟩)
    | .vOut w => Sum.inr (Sum.inr w)
  invFun
    | Sum.inl w => .vIn w
    | Sum.inr (Sum.inl ⟨w, k⟩) => .vMid w k
    | Sum.inr (Sum.inr w) => .vOut w
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with w | ⟨w, k⟩ | w <;> rfl

@[no_expose] instance {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) :
    DecidableEq (SplitV W v₀ pad) :=
  (splitVEquiv v₀ pad).decidableEq

@[no_expose] instance {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ) :
    Fintype (SplitV W v₀ pad) :=
  Fintype.ofEquiv _ (splitVEquiv v₀ pad).symm

instance {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) :
    Nonempty (SplitV W v₀ pad) :=
  ⟨.vIn v₀⟩

private theorem sum_splitMidLen {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ) :
    ∑ w : W, splitMidLen v₀ pad w = Fintype.card W + pad := by
  have := Fintype.card_pos_iff.2 ⟨v₀⟩
  simp [splitMidLen, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne']
  omega

/-- `SplitV W v₀ pad` has `3 * |W| + pad` vertices. -/
theorem card_splitV {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ) :
    Fintype.card (SplitV W v₀ pad) = 3 * Fintype.card W + pad := by
  simp only [Fintype.card_congr (splitVEquiv v₀ pad), Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_fin, sum_splitMidLen]
  omega

private def splitAdjRel {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ)
    (adjD : W → W → Prop) : SplitV W v₀ pad → SplitV W v₀ pad → Prop
  | .vIn u, .vMid w k => u = w ∧ k.1 = 0
  | .vMid w k, .vIn u => u = w ∧ k.1 = 0
  | .vMid u k₁, .vMid w k₂ => u = w ∧ (k₁.1 + 1 = k₂.1 ∨ k₂.1 + 1 = k₁.1)
  | .vMid w k, .vOut u => u = w ∧ k.1 + 1 = splitMidLen v₀ pad w
  | .vOut u, .vMid w k => u = w ∧ k.1 + 1 = splitMidLen v₀ pad w
  | .vOut u, .vIn w => adjD u w
  | .vIn w, .vOut u => adjD u w
  | _, _ => False

/-- The undirected `3`-split (plus `pad` vertices on `v₀`) of `adjD`. -/
def paddedSplitGraph {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ)
    (adjD : W → W → Prop) : SimpleGraph (SplitV W v₀ pad) where
  Adj := splitAdjRel v₀ pad adjD
  symm := ⟨fun u v h => by
    cases u <;> cases v <;> simp only [splitAdjRel] at h ⊢ <;> tauto⟩
  loopless := ⟨fun u h => by
    cases u <;> simp only [splitAdjRel] at h
    omega⟩

private theorem splitMidLen_pos {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (w : W) :
    0 < splitMidLen v₀ pad w := by
  dsimp only [splitMidLen]
  split_ifs <;> omega

private def midPrev {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (w : W)
    (k : Fin (splitMidLen v₀ pad w)) : SplitV W v₀ pad :=
  if h : k.1 = 0 then .vIn w else .vMid w ⟨k.1 - 1, by omega⟩

private def midNext {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (w : W)
    (k : Fin (splitMidLen v₀ pad w)) : SplitV W v₀ pad :=
  if h : k.1 + 1 = splitMidLen v₀ pad w then .vOut w
  else .vMid w ⟨k.1 + 1, by have := k.2; omega⟩

private theorem adj_vMid_iff {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ)
    (adjD : W → W → Prop) (w : W) (k : Fin (splitMidLen v₀ pad w)) (x : SplitV W v₀ pad) :
    (paddedSplitGraph v₀ pad adjD).Adj (.vMid w k) x ↔
      x = midPrev v₀ pad w k ∨ x = midNext v₀ pad w k := by
  cases x with
  | vMid u k' =>
    obtain rfl | hu := eq_or_ne w u <;> simp only [paddedSplitGraph, splitAdjRel] <;>
      grind [midPrev, midNext, Fin.ext_iff]
  | _ => simp only [paddedSplitGraph, splitAdjRel]; grind [midPrev, midNext]

/-- A neighbour of `vOut w` is the last middle vertex of `w` or the head `vIn a` of an arc. -/
private theorem adj_vOut {W : Type*} [DecidableEq W] {v₀ : W} {pad : ℕ} {adjD : W → W → Prop}
    {w : W} {x : SplitV W v₀ pad} (h : (paddedSplitGraph v₀ pad adjD).Adj (.vOut w) x) :
    x = .vMid w ⟨splitMidLen v₀ pad w - 1, by have := splitMidLen_pos v₀ pad w; omega⟩ ∨
      ∃ a, adjD w a ∧ x = .vIn a := by
  rcases x with a | ⟨u, k⟩ | u
  · exact .inr ⟨a, h, rfl⟩
  · obtain ⟨rfl, hk⟩ := h
    exact .inl (congrArg _ (Fin.ext (by dsimp only; omega)))
  · exact h.elim

/-- `τ : Fin |W| ≃ W` is a directed Hamiltonian tour of `(W, adjD)`. -/
@[expose] def IsDirTour {W : Type*} [Fintype W] [Nonempty W] (adjD : W → W → Prop)
    (τ : Fin (Fintype.card W) ≃ W) : Prop :=
  ∀ t : Fin (Fintype.card W), adjD (τ t) (τ (t + 1))

/-- Every edge between `vOut u` and `vIn w` belongs to the complete graph on `SplitV W v₀ pad`. -/
theorem splitV_top_edge_vOut_vIn {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (u w : W) :
    s(SplitV.vOut u, SplitV.vIn w) ∈ (⊤ : SimpleGraph (SplitV W v₀ pad)).edgeSet := by
  simp

/-- A cyclic enumeration `τ` steps from `x` to `y` exactly when `y` follows `x`. -/
private theorem tour_exists_iff {V : Type*} {n : ℕ} [NeZero n] {τ : Fin n ≃ V} {x y : V} :
    (∃ t, τ t = x ∧ τ (t + 1) = y) ↔ τ (τ.symm x + 1) = y :=
  ⟨by rintro ⟨t, rfl, rfl⟩; rw [τ.symm_apply_apply], fun h => ⟨_, τ.apply_symm_apply x, h⟩⟩

/-- The pair `{a, b}` is an edge of the tour `σ` exactly when one of the two follows the other. -/
private theorem mem_tourEdgeSet_iff {V : Type*} [Fintype V] [DecidableEq V]
    [NeZero (Fintype.card V)] (σ : Fin (Fintype.card V) ≃ V) (hV : 3 ≤ Fintype.card V)
    (a b : V) (hab : s(a, b) ∈ (⊤ : SimpleGraph V).edgeSet) :
    ⟨s(a, b), hab⟩ ∈ tourEdgeSet σ hV ↔ σ (σ.symm a + 1) = b ∨ σ (σ.symm b + 1) = a := by
  simp only [tourEdgeSet, fin_mk_one (n := Fintype.card V) (by omega), Finset.mem_image,
    Finset.mem_univ, true_and, Subtype.ext_iff, Sym2.eq_iff, exists_or, tour_exists_iff]

/-- A tour lies in `G` exactly when all its steps are edges of `G`. -/
private theorem tourEdgeSet_subset_iff {V : Type*} [Fintype V] [DecidableEq V]
    [NeZero (Fintype.card V)] {G : SimpleGraph V} {σ : Fin (Fintype.card V) ≃ V}
    {hV : 3 ≤ Fintype.card V} :
    (∀ e ∈ tourEdgeSet σ hV, e.1 ∈ G.edgeSet) ↔ ∀ i, G.Adj (σ i) (σ (i + 1)) := by
  simp [tourEdgeSet, fin_mk_one (n := Fintype.card V) (by omega)]

private def splitPos {W : Type*} [Fintype W] [DecidableEq W]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W) (w : W) : ℕ :=
  if w = v₀ then 0 else 3 * (τ'.symm w).1 + pad

private theorem splitPos_add_bound {W : Type*} [Fintype W] [DecidableEq W]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W) (w : W) :
    splitPos v₀ pad τ' w + 1 + splitMidLen v₀ pad w < 3 * Fintype.card W + pad := by
  dsimp only [splitPos, splitMidLen]
  have := (τ'.symm w).2
  by_cases hw : w = v₀ <;> simp only [hw, ↓reduceIte] <;> omega

private def splitFrom {W : Type*} [Fintype W] [DecidableEq W]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W) :
    SplitV W v₀ pad → Fin (3 * Fintype.card W + pad)
  | .vIn w => ⟨splitPos v₀ pad τ' w, by
      have := splitPos_add_bound v₀ pad τ' w
      have := splitMidLen_pos v₀ pad w
      omega⟩
  | .vMid w k => ⟨splitPos v₀ pad τ' w + 1 + k.1, by
      have := splitPos_add_bound v₀ pad τ' w
      have := k.2
      omega⟩
  | .vOut w => ⟨splitPos v₀ pad τ' w + 1 + splitMidLen v₀ pad w,
      splitPos_add_bound v₀ pad τ' w⟩

private def splitTo {W : Type*} [Fintype W] [DecidableEq W]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W)
    (i : Fin (3 * Fintype.card W + pad)) : SplitV W v₀ pad :=
  if _ : i.1 = 0 then .vIn v₀
  else if h1 : i.1 < pad + 2 then
    .vMid v₀ ⟨i.1 - 1, by simp only [splitMidLen, ↓reduceIte]; omega⟩
  else if _ : i.1 = pad + 2 then .vOut v₀
  else
    let j := i.1 - (pad + 3)
    let t : Fin (Fintype.card W) := ⟨j / 3 + 1, by have := i.2; omega⟩
    if j % 3 = 0 then .vIn (τ' t)
    else if j % 3 = 1 then .vMid (τ' t) ⟨0, splitMidLen_pos v₀ pad _⟩
    else .vOut (τ' t)

/-- A directed tour that starts at `v₀` is at `v₀` only at its start. -/
private theorem dirTour_eq_start_iff {W : Type*} [Fintype W] [NeZero (Fintype.card W)] {v₀ : W}
    {τ' : Fin (Fintype.card W) ≃ W} (hτ'0 : τ' 0 = v₀) (t : Fin (Fintype.card W)) :
    τ' t = v₀ ↔ t.1 = 0 := by
  rw [← hτ'0, τ'.apply_eq_iff_eq, Fin.ext_iff, Fin.val_zero]

private theorem splitFrom_splitTo {W : Type*} [Fintype W] [DecidableEq W]
    [NeZero (Fintype.card W)]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W)
    (hτ'0 : τ' 0 = v₀) (i : Fin (3 * Fintype.card W + pad)) :
    splitFrom v₀ pad τ' (splitTo v₀ pad τ' i) = i := by
  ext
  dsimp only [splitTo]
  split_ifs <;> simp [splitFrom, splitPos, splitMidLen, dirTour_eq_start_iff hτ'0] <;> omega

/-- `splitFrom` is a surjection between types of the same cardinality, hence injective, so its
right inverse `splitTo` is also a left inverse. -/
private theorem splitTo_splitFrom {W : Type*} [Fintype W] [DecidableEq W]
    [NeZero (Fintype.card W)]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W)
    (hτ'0 : τ' 0 = v₀) (x : SplitV W v₀ pad) :
    splitTo v₀ pad τ' (splitFrom v₀ pad τ' x) = x :=
  have h : Function.LeftInverse (splitFrom v₀ pad τ') (splitTo v₀ pad τ') :=
    splitFrom_splitTo v₀ pad τ' hτ'0
  h.rightInverse_of_injective ((Fintype.bijective_iff_surjective_and_card _).2
    ⟨h.surjective, by rw [card_splitV, Fintype.card_fin]⟩).1 x

private def splitEquiv {W : Type*} [Fintype W] [DecidableEq W]
    [NeZero (Fintype.card W)]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W)
    (hτ'0 : τ' 0 = v₀) : SplitV W v₀ pad ≃ Fin (3 * Fintype.card W + pad) where
  toFun := splitFrom v₀ pad τ'
  invFun := splitTo v₀ pad τ'
  left_inv := splitTo_splitFrom v₀ pad τ' hτ'0
  right_inv := splitFrom_splitTo v₀ pad τ' hτ'0

private theorem splitEquiv_vIn_add_one {W : Type*} [Fintype W] [DecidableEq W]
    [NeZero (Fintype.card W)]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W) (hτ'0 : τ' 0 = v₀)
    [NeZero (3 * Fintype.card W + pad)] (w : W) :
    splitEquiv v₀ pad τ' hτ'0 (.vIn w) + 1 =
      splitEquiv v₀ pad τ' hτ'0 (.vMid w ⟨0, splitMidLen_pos v₀ pad w⟩) := by
  have hbound := splitPos_add_bound v₀ pad τ' w
  have hmid := splitMidLen_pos v₀ pad w
  ext
  rw [Fin.val_add_one_of_lt' (by simp only [splitEquiv, Equiv.coe_fn_mk, splitFrom]; omega)]
  rfl

private theorem splitEquiv_vMid_add_one {W : Type*} [Fintype W] [DecidableEq W]
    [NeZero (Fintype.card W)]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W) (hτ'0 : τ' 0 = v₀)
    [NeZero (3 * Fintype.card W + pad)] (w : W) (k : Fin (splitMidLen v₀ pad w)) :
    splitEquiv v₀ pad τ' hτ'0 (.vMid w k) + 1 =
      splitEquiv v₀ pad τ' hτ'0 (midNext v₀ pad w k) := by
  have hbound := splitPos_add_bound v₀ pad τ' w
  ext
  rw [Fin.val_add_one_of_lt' (by simp only [splitEquiv, Equiv.coe_fn_mk, splitFrom]; omega)]
  unfold midNext
  split_ifs <;> simp only [splitEquiv, Equiv.coe_fn_mk, splitFrom] <;> omega

private theorem splitEquiv_vOut_add_one {W : Type*} [Fintype W] [DecidableEq W]
    [NeZero (Fintype.card W)]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W) (hW : 2 ≤ Fintype.card W)
    [NeZero (3 * Fintype.card W + pad)] (hτ'0 : τ' 0 = v₀) (t : Fin (Fintype.card W)) :
    splitEquiv v₀ pad τ' hτ'0 (.vOut (τ' t)) + 1 =
      splitEquiv v₀ pad τ' hτ'0 (.vIn (τ' (t + 1))) := by
  ext
  simp only [splitEquiv, Equiv.coe_fn_mk, splitFrom, splitPos, splitMidLen,
    dirTour_eq_start_iff hτ'0, Equiv.symm_apply_apply,
    fin_val_add_one_eq_ite (n := Fintype.card W) (by omega),
    fin_val_add_one_eq_ite (n := 3 * Fintype.card W + pad) (by omega)]
  split_ifs <;> omega

/-- Every directed Hamiltonian tour of `(W, adjD)` lifts to a subgraph tour of
`paddedSplitGraph v₀ pad adjD` matching the inter-gadget arcs. -/
theorem paddedSplitTour_of_dirTour {W : Type*} [Fintype W] [Nonempty W] [DecidableEq W]
    (v₀ : W) (pad : ℕ) (adjD : W → W → Prop) (hW : 2 ≤ Fintype.card W)
    (τ : Fin (Fintype.card W) ≃ W) (hτ : IsDirTour adjD τ) :
    ∃ F : Finset ↥(⊤ : SimpleGraph (SplitV W v₀ pad)).edgeSet,
      IsSubgraphTour (paddedSplitGraph v₀ pad adjD) F ∧
      ∀ u w : W,
        (⟨s(SplitV.vOut u, SplitV.vIn w), splitV_top_edge_vOut_vIn v₀ pad u w⟩ ∈ F ↔
          ∃ t : Fin (Fintype.card W), τ t = u ∧ τ (t + 1) = w) := by
  classical
  have : NeZero (3 * Fintype.card W + pad) := ⟨by omega⟩
  have hM3 : 3 ≤ Fintype.card (SplitV W v₀ pad) := by rw [card_splitV]; omega
  -- The directed tour started at `v₀`, and the tour of the split graph that follows it.
  let τ' : Fin (Fintype.card W) ≃ W := (Equiv.addLeft (τ.symm v₀)).trans τ
  have hτ'0 : τ' 0 = v₀ := by simp [τ']
  let e := splitEquiv v₀ pad τ' hτ'0
  let σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad :=
    (finCongr (card_splitV v₀ pad)).trans e.symm
  have hσ : ∀ {x y : SplitV W v₀ pad}, e x + 1 = e y → σ (σ.symm x + 1) = y := fun h => by
    simp [σ, fin_cast_add_one, h]
  have hIn (w : W) := hσ (splitEquiv_vIn_add_one v₀ pad τ' hτ'0 w)
  have hOut (w : W) : σ (σ.symm (.vOut w) + 1) = .vIn (τ (τ.symm w + 1)) := by
    have := hσ (splitEquiv_vOut_add_one v₀ pad τ' hW hτ'0 (τ'.symm w))
    simpa [τ', add_assoc] using this
  refine ⟨tourEdgeSet σ hM3, ⟨⟨hM3, σ, rfl⟩, tourEdgeSet_subset_iff.2 fun i => ?_⟩, fun u w => ?_⟩
  · obtain ⟨x, rfl⟩ := σ.symm.surjective i
    rw [σ.apply_symm_apply]
    rcases x with w | ⟨w, k⟩ | w
    · rw [hIn]
      exact ⟨rfl, rfl⟩
    · rw [hσ (splitEquiv_vMid_add_one v₀ pad τ' hτ'0 w k)]
      exact (adj_vMid_iff v₀ pad adjD w k _).2 (.inr rfl)
    · rw [hOut]
      exact (by simpa using hτ (τ.symm w) : adjD w (τ (τ.symm w + 1)))
  · rw [mem_tourEdgeSet_iff, hOut, hIn, tour_exists_iff]
    simp

/-- Reindexing a tour by a bijection of the positions that sends each step to a step, in either
direction, does not change its edge set. -/
private theorem tourEdgeSet_congr {V : Type*} [Fintype V] [DecidableEq V]
    [NeZero (Fintype.card V)] {σ σ' : Fin (Fintype.card V) ≃ V} (hV : 3 ≤ Fintype.card V)
    (e : Fin (Fintype.card V) ≃ Fin (Fintype.card V))
    (h : ∀ i, s(σ' i, σ' (i + 1)) = s(σ (e i), σ (e i + 1))) :
    tourEdgeSet σ' hV = tourEdgeSet σ hV := by
  ext ⟨x, hx⟩
  simp only [tourEdgeSet, fin_mk_one (n := Fintype.card V) (by omega), Finset.mem_image,
    Finset.mem_univ, true_and, Subtype.mk.injEq, h]
  exact (e.surjective.exists (p := fun j => s(σ j, σ (j + 1)) = x)).symm

/-- For `3 ≤ M`, `i - 1 ≠ i + 1` in `Fin M`. -/
theorem fin_sub_one_ne_add_one {M : ℕ} [NeZero M] (hM : 3 ≤ M) (i : Fin M) :
    i - 1 ≠ i + 1 := by
  intro h
  have := congrArg Fin.val (sub_eq_iff_eq_add.1 h)
  rw [fin_val_add_one_eq_ite (by omega), fin_val_add_one_eq_ite (by omega)] at this
  split_ifs at this <;> omega

/-- Induction around the cycle `Fin n`: a property that holds at `0` and passes from `i` to
`i + 1` holds everywhere. -/
private theorem fin_cyclic_induction {n : ℕ} [NeZero n] {P : Fin n → Prop} (zero : P 0)
    (succ : ∀ i, P i → P (i + 1)) (i : Fin n) : P i := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero => exact zero
  | succ k ih =>
    convert succ _ (ih (by omega)) using 1
    exact Fin.ext (Fin.val_add_one_of_lt' (i := ⟨k, by omega⟩) hk).symm

private def splitFin {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ) (n : ℕ) :
    Fin (Fintype.card (SplitV W v₀ pad)) :=
  ⟨n % Fintype.card (SplitV W v₀ pad), Nat.mod_lt _ Fintype.card_pos⟩

private theorem splitFin_succ {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ)
    (hM : 1 < Fintype.card (SplitV W v₀ pad)) (n : ℕ) :
    splitFin v₀ pad (n + 1) = splitFin v₀ pad n + 1 :=
  Fin.ext (by simp only [splitFin, Fin.val_add, fin_one_val hM, Nat.mod_add_mod])

private def splitStep {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ)
    (σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad) (n : ℕ) : SplitV W v₀ pad :=
  σ (splitFin v₀ pad n)

section Tour

variable {W : Type*} [Fintype W] [DecidableEq W] {v₀ : W} {pad : ℕ} {adjD : W → W → Prop}
  {σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad}

/-- One more step along the tour leads to the successor of the current vertex. -/
private theorem splitStep_succ (hM : 1 < Fintype.card (SplitV W v₀ pad)) (n : ℕ) :
    splitStep v₀ pad σ (n + 1) = σ (σ.symm (splitStep v₀ pad σ n) + 1) := by
  simp [splitStep, splitFin_succ v₀ pad hM]

/-- The first `|SplitV W v₀ pad|` steps of a tour are at distinct vertices. -/
private theorem splitStep_inj {a b : ℕ} (h : splitStep v₀ pad σ a = splitStep v₀ pad σ b)
    (ha : a < Fintype.card (SplitV W v₀ pad)) (hb : b < Fintype.card (SplitV W v₀ pad)) :
    a = b := by
  simpa [splitStep, splitFin, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using h

/-- After `|SplitV W v₀ pad|` steps a tour is back at its start. -/
private theorem splitStep_card :
    splitStep v₀ pad σ (Fintype.card (SplitV W v₀ pad)) = σ 0 :=
  congrArg σ (Fin.ext (Nat.mod_self _))

variable (hM3 : 3 ≤ Fintype.card (SplitV W v₀ pad))
  (hadj : ∀ i, (paddedSplitGraph v₀ pad adjD).Adj (σ i) (σ (i + 1)))

include hM3 hadj

/-- The two tour neighbours of a middle vertex are its two neighbours in the split graph. -/
private theorem tour_vMid_nbrs {i : Fin (Fintype.card (SplitV W v₀ pad))} {w : W}
    {k : Fin (splitMidLen v₀ pad w)} (h : σ i = .vMid w k) :
    σ (i - 1) = midPrev v₀ pad w k ∧ σ (i + 1) = midNext v₀ pad w k ∨
      σ (i - 1) = midNext v₀ pad w k ∧ σ (i + 1) = midPrev v₀ pad w k := by
  have hp := hadj i
  have hm := (hadj (i - 1)).symm
  rw [sub_add_cancel] at hm
  rw [h, adj_vMid_iff] at hp hm
  have hne := σ.injective.ne (fin_sub_one_ne_add_one hM3 i)
  rcases hm with a | a <;> rcases hp with b | b
  exacts [absurd (a.trans b.symm) hne, .inl ⟨a, b⟩, .inr ⟨a, b⟩, absurd (a.trans b.symm) hne]

/-- A tour of the split graph has a parametrization with the same edge set that starts with
`vIn v₀`, `vMid v₀ 0`. -/
private theorem exists_tour_start :
    ∃ σ' : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad,
      tourEdgeSet σ' hM3 = tourEdgeSet σ hM3 ∧ σ' 0 = .vIn v₀ ∧
        σ' 1 = .vMid v₀ ⟨0, splitMidLen_pos v₀ pad v₀⟩ := by
  obtain ⟨k, hk⟩ := σ.surjective (.vMid v₀ ⟨0, splitMidLen_pos v₀ pad v₀⟩)
  rcases tour_vMid_nbrs hM3 hadj hk with ⟨h, -⟩ | ⟨-, h⟩ <;>
    simp only [midPrev, ↓reduceDIte] at h
  · exact ⟨(Equiv.addLeft (k - 1)).trans σ,
      tourEdgeSet_congr hM3 (Equiv.addLeft (k - 1)) fun i => by simp [add_assoc],
      by simpa using h, by simpa using hk⟩
  · exact ⟨(Equiv.subLeft (k + 1)).trans σ,
      tourEdgeSet_congr hM3 (Equiv.subLeft k) fun i => by
        simp [Sym2.eq_swap, sub_add_eq_add_sub],
      by simpa using h, by simpa using hk⟩

/-- A tour that starts with `vIn v₀`, `vMid v₀ 0` traverses every gadget forwards: it steps from
`vIn w` to `vMid w 0`, from a middle vertex to the next one or to `vOut w`, and from `vOut w`
along an arc of `adjD`. -/
private theorem tour_fwd (h0 : σ 0 = .vIn v₀)
    (h1 : σ 1 = .vMid v₀ ⟨0, splitMidLen_pos v₀ pad v₀⟩)
    (i : Fin (Fintype.card (SplitV W v₀ pad))) :
    (∀ w, σ i = .vIn w → σ (i + 1) = .vMid w ⟨0, splitMidLen_pos v₀ pad w⟩) ∧
    (∀ w k, σ i = .vMid w k → σ (i + 1) = midNext v₀ pad w k) ∧
    (∀ w, σ i = .vOut w → ∃ w', adjD w w' ∧ σ (i + 1) = .vIn w') := by
  induction i using fin_cyclic_induction with
  | zero => simp [h0, h1]
  | succ i ih =>
    obtain ⟨ihI, ihM, ihO⟩ := ih
    have hne := σ.injective.ne (fin_sub_one_ne_add_one hM3 (i + 1))
    rw [add_sub_cancel_right] at hne
    refine ⟨fun w h => ?_, fun w k h => ?_, fun w h => ?_⟩
    · -- `vMid w 0` is next to `vIn w` on the tour, and it is not the vertex before `vIn w`.
      obtain ⟨r, hr⟩ := σ.surjective (.vMid w ⟨0, splitMidLen_pos v₀ pad w⟩)
      rcases tour_vMid_nbrs hM3 hadj hr with ⟨hm, -⟩ | ⟨-, hp⟩
      · rw [← hr, ← sub_eq_iff_eq_add.1 (σ.injective (hm.trans h.symm))]
      · obtain rfl := add_right_cancel (σ.injective (hp.trans h.symm))
        exact absurd ((ihM _ _ hr).symm.trans h) (by unfold midNext; split_ifs <;> simp)
    · -- The vertex before `vMid w k` is not `midNext w k`, from which the tour steps forwards.
      rcases tour_vMid_nbrs hM3 hadj h with ⟨-, h2⟩ | ⟨h1', -⟩
      · exact h2
      · rw [add_sub_cancel_right] at h1'
        unfold midNext at h1'
        split_ifs at h1'
        · obtain ⟨w', -, hw'⟩ := ihO _ h1'
          cases hw'.symm.trans h
        · exact absurd ((ihM _ _ h1').symm.trans h)
            (by unfold midNext; split_ifs <;> simp [Fin.ext_iff, add_assoc])
    · -- The vertex before `vOut w` is not a `vIn`, so it is the last middle vertex of `w`.
      have hz := hadj (i + 1)
      have hx := (hadj i).symm
      rw [h] at hz hx
      rcases adj_vOut hz with hz | hz
      · rcases adj_vOut hx with hx | ⟨a, -, hx⟩
        · exact absurd (hx.trans hz.symm) hne
        · cases (ihI a hx).symm.trans h
      · exact hz

/-- A tour that starts with `vIn v₀`, `vMid v₀ 0` and is at `vIn w` at step `n` runs through the
middle vertices of `w` and is at `vOut w` at step `n + 1 + splitMidLen v₀ pad w`. -/
private theorem splitStep_vOut (h0 : σ 0 = .vIn v₀)
    (h1 : σ 1 = .vMid v₀ ⟨0, splitMidLen_pos v₀ pad v₀⟩) {n : ℕ} {w : W}
    (h : splitStep v₀ pad σ n = .vIn w) :
    splitStep v₀ pad σ (n + 1 + splitMidLen v₀ pad w) = .vOut w := by
  have hfwd := tour_fwd hM3 hadj h0 h1
  have hmid : ∀ k (hk : k < splitMidLen v₀ pad w),
      splitStep v₀ pad σ (n + 1 + k) = .vMid w ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [add_zero, splitStep_succ (by omega), h]
      exact (hfwd _).1 w (σ.apply_symm_apply _)
    | succ k ih =>
      intro hk
      rw [← add_assoc, splitStep_succ (by omega), ih (by omega),
        (hfwd _).2.1 w _ (σ.apply_symm_apply _), midNext, dite_eq_right (by dsimp only; omega)]
  have hpos := splitMidLen_pos v₀ pad w
  rw [show n + 1 + splitMidLen v₀ pad w = n + 1 + (splitMidLen v₀ pad w - 1) + 1 by omega,
    splitStep_succ (by omega), hmid _ (by omega), (hfwd _).2.1 w _ (σ.apply_symm_apply _),
    midNext, dite_eq_left (by dsimp only; omega)]

end Tour

/-- Every undirected tour of `paddedSplitGraph v₀ pad adjD` (`|W| ≥ 2`) induces a directed
Hamiltonian tour of `(W, adjD)` matching the inter-gadget arcs. -/
theorem exists_dirTour_of_paddedSplitTour {W : Type*} [Fintype W] [Nonempty W] [DecidableEq W]
    (v₀ : W) (pad : ℕ) (adjD : W → W → Prop) (hW : 2 ≤ Fintype.card W)
    {F : Finset ↥(⊤ : SimpleGraph (SplitV W v₀ pad)).edgeSet}
    (hF : IsSubgraphTour (paddedSplitGraph v₀ pad adjD) F) :
    ∃ τ : Fin (Fintype.card W) ≃ W, IsDirTour adjD τ ∧
      ∀ u w : W,
        (⟨s(SplitV.vOut u, SplitV.vIn w), splitV_top_edge_vOut_vIn v₀ pad u w⟩ ∈ F ↔
          ∃ t : Fin (Fintype.card W), τ t = u ∧ τ (t + 1) = w) := by
  classical
  obtain ⟨⟨hM3, σ₀, rfl⟩, hsub⟩ := hF
  obtain ⟨σ, htour, hσ0, hσ1⟩ := exists_tour_start hM3 (tourEdgeSet_subset_iff.1 hsub)
  have hadj := tourEdgeSet_subset_iff.1 (htour ▸ hsub)
  have hM := card_splitV v₀ pad
  have hS0 : splitStep v₀ pad σ 0 = .vIn v₀ := hσ0
  have hfwd := tour_fwd hM3 hadj hσ0 hσ1
  -- `next w` is the vertex whose gadget the tour enters when it leaves the gadget of `w`.
  choose next hnext_adj hnext using fun w => (hfwd _).2.2 w (σ.apply_symm_apply (.vOut w))
  have hin : ∀ r, splitStep v₀ pad σ (pad + 2 + 3 * r) = .vOut (next^[r] v₀) →
      splitStep v₀ pad σ (pad + 3 + 3 * r) = .vIn (next^[r + 1] v₀) := fun r h => by
    rw [show pad + 3 + 3 * r = pad + 2 + 3 * r + 1 by omega, splitStep_succ (by omega), h, hnext,
      Function.iterate_succ_apply']
  -- The gadget of `next^[r] v₀` ends at step `pad + 2 + 3 * r` of the tour.
  have hpos : ∀ r, r < Fintype.card W →
      splitStep v₀ pad σ (pad + 2 + 3 * r) = .vOut (next^[r] v₀) := by
    intro r
    induction r with
    | zero =>
      intro _
      have := splitStep_vOut hM3 hadj hσ0 hσ1 hS0
      rwa [splitMidLen, ite_eq_left rfl, show 0 + 1 + (pad + 1) = pad + 2 + 3 * 0 by omega] at this
    | succ r ih =>
      intro hr
      have h := hin r (ih (by omega))
      -- A gadget entered after step `0` is not that of `v₀`, so it has one middle vertex.
      have hne : next^[r + 1] v₀ ≠ v₀ := fun h' => by
        have := splitStep_inj (h.trans ((congrArg _ h').trans hS0.symm)) (by omega) (by omega)
        omega
      have := splitStep_vOut hM3 hadj hσ0 hσ1 h
      rwa [splitMidLen, ite_eq_right hne,
        show pad + 3 + 3 * r + 1 + 1 = pad + 2 + 3 * (r + 1) by omega] at this
  -- After `|W|` gadgets the tour is back at its start, and the gadgets passed are distinct.
  have hm : next^[Fintype.card W] v₀ = v₀ := by
    have := hin _ (hpos (Fintype.card W - 1) (by omega))
    rw [Nat.sub_add_cancel (by omega), show pad + 3 + 3 * (Fintype.card W - 1) =
      Fintype.card (SplitV W v₀ pad) by omega, splitStep_card, hσ0] at this
    exact (SplitV.vIn.inj this).symm
  have hinj : Function.Injective fun t : Fin (Fintype.card W) => next^[t.1] v₀ := fun a b h => by
    have := splitStep_inj ((hpos a a.2).trans ((congrArg _ h).trans (hpos b b.2).symm))
      (by omega) (by omega)
    exact Fin.ext (by omega)
  let τ : Fin (Fintype.card W) ≃ W := Equiv.ofBijective _
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, Fintype.card_fin _⟩)
  have hτ : ∀ t, τ (t + 1) = next (τ t) := fun t => by
    change next^[(t + 1).1] v₀ = next (next^[t.1] v₀)
    rw [← Function.iterate_succ_apply' next, fin_val_add_one_eq_ite (by omega)]
    split_ifs with h
    · simp [h, hm]
    · rfl
  refine ⟨τ, fun t => hτ t ▸ hnext_adj _, fun u w => ?_⟩
  rw [← htour, mem_tourEdgeSet_iff, tour_exists_iff, hτ, τ.apply_symm_apply, hnext,
    (hfwd _).1 w (σ.apply_symm_apply _)]
  simp

end SplitGraph
