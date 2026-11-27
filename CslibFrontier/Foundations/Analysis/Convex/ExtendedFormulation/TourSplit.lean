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
import CslibFrontier.Foundations.Data.Fin.Order
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

private theorem fin_add_one_eq_zero {n : ℕ} [NeZero n] (hn : 1 < n) {i : Fin n}
    (h : i.1 + 1 = n) : i + 1 = 0 :=
  Fin.ext (by rw [fin_val_add_one_eq_ite hn, ite_eq_left h, Fin.val_zero])

private theorem finCongr_add_one {a b : ℕ} (hab : a = b) [NeZero a] [NeZero b] (k : Fin a) :
    finCongr hab (k + 1) = finCongr hab k + 1 := by
  subst hab
  rfl

end FinHelpers

section TSPPolytope

/-- Every vertex pair along a bijection `σ : Fin |V| ≃ V` at step `i` and `i + 1` is distinct
when `3 ≤ |V|`. -/
theorem tourEdge_mem_top_edgeSet {V : Type*} [Fintype V]
    (hV : 3 ≤ Fintype.card V) (σ : Fin (Fintype.card V) ≃ V) (i : Fin (Fintype.card V)) :
    s(σ i, σ (i + ⟨1, by omega⟩)) ∈ (⊤ : SimpleGraph V).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]
  have : NeZero (Fintype.card V) := ⟨by omega⟩
  intro h
  have hval := congrArg Fin.val h
  rw [fin_mk_one (by omega), fin_val_add_one_eq_ite (by omega)] at hval
  split_ifs at hval <;> omega

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
    have hterm (e : ↥(⊤ : SimpleGraph V).edgeSet) :
        c e * tspVertex K F e =
          if e ∈ F.filter (fun e => e.1 ∉ G.edgeSet) then (-1 : K) else 0 := by
      by_cases hg : e.1 ∈ G.edgeSet <;> by_cases hf : e ∈ F <;> simp [c, tspVertex, hg, hf]
    simp only [dotProduct, hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_neg,
      mul_one]
  have htight (F : {F // IsTourEdgeSet F}) :
      c ⬝ᵥ tspVertex K F.1 = 0 ↔ IsSubgraphTour G F.1 := by
    rw [hdot, neg_eq_zero, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact ⟨fun h => ⟨F.2, fun e he => not_not.1 (h he)⟩, fun ⟨_, h⟩ e he => not_not.2 (h e he)⟩
  rw [tspPolytope, convexHull_inter_dotProduct_eq fun F => by
    rw [hdot]; exact neg_nonpos.2 (Nat.cast_nonneg _)]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Subtype.exists]
  constructor
  · rintro ⟨F, hF, hFx, rfl⟩; exact ⟨F, (htight ⟨F, hF⟩).1 hFx, rfl⟩
  · rintro ⟨F, hFG, rfl⟩; exact ⟨F, hFG.1, (htight ⟨F, hFG.1⟩).2 hFG, rfl⟩

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
  have hsplit : ∑ w : W, splitMidLen v₀ pad w = ∑ w : W, (1 + if w = v₀ then pad else 0) :=
    Finset.sum_congr rfl fun w _ => by by_cases h : w = v₀ <;> simp [splitMidLen, h, Nat.add_comm]
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- `SplitV W v₀ pad` has `3 * |W| + pad` vertices. -/
theorem card_splitV {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ) :
    Fintype.card (SplitV W v₀ pad) = 3 * Fintype.card W + pad := by
  rw [Fintype.card_congr (splitVEquiv v₀ pad), Fintype.card_sum, Fintype.card_sum,
    Fintype.card_sigma]
  have hsum : ∑ w : W, Fintype.card (Fin (splitMidLen v₀ pad w)) = Fintype.card W + pad := by
    simpa only [Fintype.card_fin] using sum_splitMidLen v₀ pad
  rw [hsum]
  ring

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
  have hk_lt : k.1 < splitMidLen v₀ pad w := k.2
  cases x with
  | vIn u =>
      by_cases h0 : k.1 = 0 <;>
        simp only [paddedSplitGraph, splitAdjRel, midPrev, midNext, h0, ↓reduceDIte] <;>
        split_ifs <;> simp only [or_false, SplitV.vIn.injEq, eq_comm, and_true, and_false]
  | vMid u k' =>
      simp only [paddedSplitGraph, splitAdjRel]
      constructor
      · rintro ⟨rfl, hstep | hstep⟩
        · right
          simp only [midNext, show ¬ k.1 + 1 = splitMidLen v₀ pad w by have := k'.2; omega,
            ↓reduceDIte, SplitV.vMid.injEq, heq_eq_eq, true_and]
          exact Fin.ext hstep.symm
        · left
          simp only [midPrev, show ¬ k.1 = 0 by omega, ↓reduceDIte, SplitV.vMid.injEq,
            heq_eq_eq, true_and]
          exact Fin.ext (by dsimp; omega)
      · rintro (h | h)
        · dsimp [midPrev] at h; split_ifs at h; cases h; exact ⟨rfl, Or.inr (by dsimp; omega)⟩
        · dsimp [midNext] at h; split_ifs at h; cases h; exact ⟨rfl, Or.inl rfl⟩
  | vOut u =>
      by_cases hlast : k.1 + 1 = splitMidLen v₀ pad w <;>
        simp only [paddedSplitGraph, splitAdjRel, midPrev, midNext, hlast, ↓reduceDIte] <;>
        split_ifs <;> simp only [or_false, false_or, SplitV.vOut.injEq, eq_comm, and_true,
          and_false]

/-- `τ : Fin |W| ≃ W` is a directed Hamiltonian tour of `(W, adjD)`. -/
@[expose] def IsDirTour {W : Type*} [Fintype W] [Nonempty W] (adjD : W → W → Prop)
    (τ : Fin (Fintype.card W) ≃ W) : Prop :=
  ∀ t : Fin (Fintype.card W), adjD (τ t) (τ (t + 1))

/-- Every edge between `vOut u` and `vIn w` belongs to the complete graph on `SplitV W v₀ pad`. -/
theorem splitV_top_edge_vOut_vIn {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (u w : W) :
    s(SplitV.vOut u, SplitV.vIn w) ∈ (⊤ : SimpleGraph (SplitV W v₀ pad)).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
  intro h; cases h

private theorem mem_tourEdgeSet_iff {V : Type*} [Fintype V] [DecidableEq V]
    [NeZero (Fintype.card V)] (σ : Fin (Fintype.card V) ≃ V) (hV : 3 ≤ Fintype.card V)
    (a b : V) (hab : s(a, b) ∈ (⊤ : SimpleGraph V).edgeSet) :
    ⟨s(a, b), hab⟩ ∈ tourEdgeSet σ hV ↔
      ∃ i : Fin (Fintype.card V), s(σ i, σ (i + 1)) = s(a, b) := by
  simp only [tourEdgeSet, fin_mk_one (n := Fintype.card V) (by omega), Finset.mem_image,
    Finset.mem_univ, true_and, Subtype.ext_iff]

private theorem adj_of_tourEdgeSet_subset {V : Type*} [Fintype V] [DecidableEq V]
    [NeZero (Fintype.card V)] {G : SimpleGraph V} {σ : Fin (Fintype.card V) ≃ V}
    {hV : 3 ≤ Fintype.card V} (hsub : ∀ e ∈ tourEdgeSet σ hV, e.1 ∈ G.edgeSet)
    (i : Fin (Fintype.card V)) :
    G.Adj (σ i) (σ (i + 1)) := by
  refine (SimpleGraph.mem_edgeSet _).1 (hsub ⟨s(σ i, σ (i + 1)), ?_⟩ ?_)
  · rw [← fin_mk_one (n := Fintype.card V) (by omega)]
    exact tourEdge_mem_top_edgeSet hV σ i
  · exact (mem_tourEdgeSet_iff σ hV _ _ _).2 ⟨i, rfl⟩

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

private theorem vMid_zero_congr {W : Type*} [DecidableEq W] {v₀ : W} {pad : ℕ}
    {u w : W} (h : u = w) (hu : 0 < splitMidLen v₀ pad u) (hw : 0 < splitMidLen v₀ pad w) :
    (SplitV.vMid u ⟨0, hu⟩ : SplitV W v₀ pad) = .vMid w ⟨0, hw⟩ := by
  subst h; rfl

private theorem splitTo_of_block {W : Type*} [Fintype W] [DecidableEq W]
    [NeZero (Fintype.card W)]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W)
    {i : Fin (3 * Fintype.card W + pad)} {t : Fin (Fintype.card W)} {r : ℕ}
    (ht : t ≠ 0) (hr : r < 3) (hi : i.1 = 3 * t.1 + pad + r) :
    splitTo v₀ pad τ' i =
      if r = 0 then .vIn (τ' t)
      else if r = 1 then .vMid (τ' t) ⟨0, splitMidLen_pos v₀ pad _⟩
      else .vOut (τ' t) := by
  have ht1 : 1 ≤ t.1 := Nat.pos_of_ne_zero fun h => ht (Fin.ext h)
  have ht_eq : (⟨(i.1 - (pad + 3)) / 3 + 1, by have := i.2; omega⟩ : Fin (Fintype.card W)) = t :=
    Fin.ext (by dsimp; omega)
  dsimp only [splitTo]
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    show (i.1 - (pad + 3)) % 3 = r by omega]
  split_ifs
  · rw [ht_eq]
  · exact vMid_zero_congr (congrArg τ' ht_eq) _ _
  · rw [ht_eq]

private theorem splitTo_splitFrom {W : Type*} [Fintype W] [DecidableEq W]
    [NeZero (Fintype.card W)]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W)
    (hτ'0 : τ' 0 = v₀) (x : SplitV W v₀ pad) :
    splitTo v₀ pad τ' (splitFrom v₀ pad τ' x) = x := by
  have hsymm_ne {w : W} (hw : w ≠ v₀) : τ'.symm w ≠ 0 := fun h =>
    hw (by simpa only [h, hτ'0] using (τ'.apply_symm_apply w).symm)
  cases x with
  | vIn w =>
      by_cases hw : w = v₀
      · subst hw; simp only [splitFrom, splitTo, splitPos, ↓reduceIte, ↓reduceDIte]
      · rw [splitTo_of_block v₀ pad τ' (hsymm_ne hw) (r := 0) (by omega)
          (by simp only [splitFrom, splitPos, hw, ↓reduceIte, add_zero])]
        simp only [↓reduceIte, τ'.apply_symm_apply]
  | vMid w k =>
      have hk := k.2
      by_cases hw : w = v₀
      · subst hw
        simp only [splitMidLen, ↓reduceIte] at hk
        simp only [splitFrom, splitTo, splitPos, ↓reduceIte,
          show ¬ 0 + 1 + k.1 = 0 by omega, show 0 + 1 + k.1 < pad + 2 by omega, ↓reduceDIte,
          Nat.zero_add, Nat.add_sub_cancel_left]
      · simp only [splitMidLen, hw, ↓reduceIte] at hk
        rw [splitTo_of_block v₀ pad τ' (hsymm_ne hw) (r := 1) (by omega)
          (by simp only [splitFrom, splitPos, hw, ↓reduceIte]; omega)]
        simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [show k = ⟨0, splitMidLen_pos v₀ pad w⟩ from Fin.ext (by dsimp; omega)]
        exact vMid_zero_congr (τ'.apply_symm_apply w) _ _
  | vOut w =>
      by_cases hw : w = v₀
      · subst hw
        have : (splitFrom w pad τ' (.vOut w)).1 = pad + 2 := by
          simp only [splitFrom, splitPos, splitMidLen, ↓reduceIte]; omega
        dsimp only [splitTo]; split_ifs <;> first | rfl | omega
      · rw [splitTo_of_block v₀ pad τ' (hsymm_ne hw) (r := 2) (by omega)
          (by simp only [splitFrom, splitPos, splitMidLen, hw, ↓reduceIte])]
        simp only [show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte,
          τ'.apply_symm_apply]

private theorem splitFrom_splitTo {W : Type*} [Fintype W] [DecidableEq W]
    [NeZero (Fintype.card W)]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W)
    (hτ'0 : τ' 0 = v₀) (i : Fin (3 * Fintype.card W + pad)) :
    splitFrom v₀ pad τ' (splitTo v₀ pad τ' i) = i := by
  dsimp only [splitTo]
  split_ifs with h0 h1 h2
  · ext; simp [splitFrom, splitPos, h0]
  · ext; simp [splitFrom, splitPos]; omega
  · ext; simp [splitFrom, splitPos, splitMidLen]; omega
  all_goals
    let t : Fin (Fintype.card W) := ⟨(i.1 - (pad + 3)) / 3 + 1, by have := i.2; omega⟩
    have hne : τ' t ≠ v₀ := fun h => by
      have := congrArg Fin.val (τ'.injective (h.trans hτ'0.symm)); simp [t] at this
    ext; simp only [splitFrom, splitPos, splitMidLen, hne, ↓reduceIte, Equiv.symm_apply_apply, t]
    omega

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
  dsimp only [splitEquiv, Equiv.coe_fn_mk]
  have := splitPos_add_bound v₀ pad τ' w
  have := splitMidLen_pos v₀ pad w
  ext; rw [Fin.val_add_one_of_lt' (by simp [splitFrom]; omega)]; simp [splitFrom]

private theorem splitEquiv_vMid_add_one {W : Type*} [Fintype W] [DecidableEq W]
    [NeZero (Fintype.card W)]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W) (hτ'0 : τ' 0 = v₀)
    [NeZero (3 * Fintype.card W + pad)] (w : W) (k : Fin (splitMidLen v₀ pad w)) :
    splitEquiv v₀ pad τ' hτ'0 (.vMid w k) + 1 =
      splitEquiv v₀ pad τ' hτ'0 (midNext v₀ pad w k) := by
  dsimp only [splitEquiv, Equiv.coe_fn_mk]
  have := splitPos_add_bound v₀ pad τ' w
  have := k.2
  ext
  by_cases hlast : k.1 + 1 = splitMidLen v₀ pad w <;>
    simp only [midNext, hlast, ↓reduceDIte] <;>
    rw [Fin.val_add_one_of_lt' (by simp [splitFrom]; omega)] <;>
    simp [splitFrom] <;> omega

private theorem splitEquiv_vOut_add_one {W : Type*} [Fintype W] [DecidableEq W]
    [NeZero (Fintype.card W)]
    (v₀ : W) (pad : ℕ) (τ' : Fin (Fintype.card W) ≃ W) (hW : 2 ≤ Fintype.card W)
    [NeZero (3 * Fintype.card W + pad)] (hτ'0 : τ' 0 = v₀) (t : Fin (Fintype.card W)) :
    splitEquiv v₀ pad τ' hτ'0 (.vOut (τ' t)) + 1 =
      splitEquiv v₀ pad τ' hτ'0 (.vIn (τ' (t + 1))) := by
  dsimp only [splitEquiv, Equiv.coe_fn_mk]
  ext
  rw [fin_val_add_one_eq_ite (by omega)]
  have hτ_eq : ∀ u : Fin (Fintype.card W), τ' u = v₀ ↔ u = 0 := fun u =>
    ⟨fun h => τ'.injective (h.trans hτ'0.symm), fun h => h ▸ hτ'0⟩
  have h1_ne : (1 : Fin (Fintype.card W)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; rw [fin_one_val (by omega), Fin.val_zero] at this; omega
  have ht_lt := t.2
  by_cases ht0 : t = 0
  · subst ht0
    simp only [splitFrom, splitPos, splitMidLen, hτ'0, ↓reduceIte, zero_add, hτ_eq, h1_ne,
      fin_one_val (n := Fintype.card W) (by omega), Equiv.symm_apply_apply]
    split_ifs <;> omega
  · simp only [splitFrom, splitPos, splitMidLen, hτ_eq, ht0, Fin.ext_iff, Fin.val_zero,
      fin_val_add_one_eq_ite (n := Fintype.card W) (by omega), ↓reduceIte, Equiv.symm_apply_apply]
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
  let m := Fintype.card W
  have : NeZero m := ⟨by omega⟩
  have : NeZero (3 * m + pad) := ⟨by omega⟩
  let t₀ : Fin m := τ.symm v₀
  let τ' : Fin m ≃ W := (Equiv.addLeft t₀).trans τ
  have hτ'_adj : ∀ t : Fin m, adjD (τ' t) (τ' (t + 1)) := fun t => by
    change adjD (τ (t₀ + t)) (τ (t₀ + (t + 1))); rw [← add_assoc]; exact hτ (t₀ + t)
  have hτ'0 : τ' 0 = v₀ := by change τ (t₀ + 0) = v₀; rw [add_zero]; exact τ.apply_symm_apply v₀
  have hM_card : Fintype.card (SplitV W v₀ pad) = 3 * m + pad := card_splitV v₀ pad
  have hM3 : 3 ≤ Fintype.card (SplitV W v₀ pad) := by omega
  let eFin : Fin (Fintype.card (SplitV W v₀ pad)) ≃ Fin (3 * m + pad) := finCongr hM_card
  let eSplit : SplitV W v₀ pad ≃ Fin (3 * m + pad) := splitEquiv v₀ pad τ' hτ'0
  let σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad := eFin.trans eSplit.symm
  have hσ_succ (k : Fin (Fintype.card (SplitV W v₀ pad))) :
      eSplit (σ (k + 1)) = eSplit (σ k) + 1 := by
    simp only [σ, Equiv.trans_apply, Equiv.apply_symm_apply]; exact finCongr_add_one hM_card k
  have hσ_step {k x y} (hx : σ k = x) (hxy : eSplit x + 1 = eSplit y) : σ (k + 1) = y :=
    eSplit.injective ((hσ_succ k).trans (hx.symm ▸ hxy))
  have hσ_eq {k x y} (hx : σ k = x) (hy : σ (k + 1) = y) : eSplit x + 1 = eSplit y :=
    hx ▸ hy ▸ (hσ_succ k).symm
  have hσ_adj (k : Fin (Fintype.card (SplitV W v₀ pad))) :
      (paddedSplitGraph v₀ pad adjD).Adj (σ k) (σ (k + 1)) := by
    cases hx : σ k with
    | vIn w => rw [hσ_step hx (splitEquiv_vIn_add_one v₀ pad τ' hτ'0 w)]; exact ⟨rfl, rfl⟩
    | vMid w k' =>
        rw [hσ_step hx (splitEquiv_vMid_add_one v₀ pad τ' hτ'0 w k')]
        exact (adj_vMid_iff v₀ pad adjD w k' _).2 (Or.inr rfl)
    | vOut w =>
        let t := τ'.symm w; have ht : τ' t = w := τ'.apply_symm_apply w
        rw [hσ_step hx (ht ▸ splitEquiv_vOut_add_one v₀ pad τ' hW hτ'0 t), ← ht]
        exact hτ'_adj t
  refine ⟨tourEdgeSet σ hM3, ⟨⟨hM3, σ, rfl⟩, fun e he => ?_⟩, fun u w => ?_⟩
  · rw [tourEdgeSet, Finset.mem_image] at he
    obtain ⟨k, _, rfl⟩ := he
    dsimp only; rw [fin_mk_one (n := Fintype.card (SplitV W v₀ pad)) (by omega)]
    exact (SimpleGraph.mem_edgeSet _).2 (hσ_adj k)
  · rw [mem_tourEdgeSet_iff]
    constructor
    · rintro ⟨k, hk⟩
      rcases Sym2.eq_iff.1 hk with ⟨hu, hw⟩ | ⟨hw, hu⟩
      · have htu := τ'.apply_symm_apply u
        have heq := eSplit.injective
          ((htu ▸ splitEquiv_vOut_add_one v₀ pad τ' hW hτ'0 (τ'.symm u)).symm.trans (hσ_eq hu hw))
        refine ⟨t₀ + τ'.symm u, htu, ?_⟩; rw [add_assoc]; exact SplitV.vIn.inj heq
      · cases eSplit.injective ((splitEquiv_vIn_add_one v₀ pad τ' hτ'0 w).symm.trans (hσ_eq hw hu))
    · rintro ⟨t, rfl, rfl⟩
      let t' : Fin m := t - t₀
      have ht'1 : τ' t' = τ t := by change τ (t₀ + (t - t₀)) = τ t; rw [add_sub_cancel]
      have ht'2 : τ' (t' + 1) = τ (t + 1) := by
        change τ (t₀ + (t - t₀ + 1)) = τ (t + 1); rw [show t₀ + (t - t₀ + 1) = t + 1 by abel]
      let k := eFin.symm (eSplit (.vOut (τ' t')))
      have hsk : σ k = .vOut (τ t) := by
        rw [← ht'1]; simp [σ, k]
      have hsk1 : σ (k + 1) = .vIn (τ (t + 1)) :=
        ht'2 ▸ hσ_step (ht'1 ▸ hsk) (splitEquiv_vOut_add_one v₀ pad τ' hW hτ'0 t')
      exact ⟨k, by rw [hsk, hsk1]⟩

private theorem tourEdgeSet_reverse {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (σ : Fin (Fintype.card V) ≃ V) (hV : 3 ≤ Fintype.card V) :
    tourEdgeSet ((Equiv.neg _).trans σ) hV = tourEdgeSet σ hV := by
  ext ⟨e, he⟩
  simp only [tourEdgeSet, fin_mk_one (n := Fintype.card V) (by omega), Finset.mem_image,
    Finset.mem_univ, true_and, Subtype.mk.injEq, Equiv.trans_apply, Equiv.neg_apply]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨-(i + 1), ?_⟩
    rwa [show -(i + 1) + 1 = -i by abel, Sym2.eq_swap]
  · rintro ⟨j, hj⟩
    refine ⟨-(j + 1), ?_⟩
    rwa [show -(-(j + 1) + 1) = j by abel, show -(-(j + 1)) = j + 1 by abel, Sym2.eq_swap]

private theorem tourEdgeSet_shift {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (σ : Fin (Fintype.card V) ≃ V) (hV : 3 ≤ Fintype.card V) (s : Fin (Fintype.card V)) :
    tourEdgeSet ((Equiv.addLeft s).trans σ) hV = tourEdgeSet σ hV := by
  ext ⟨e, he⟩
  simp only [tourEdgeSet, fin_mk_one (n := Fintype.card V) (by omega), Finset.mem_image,
    Finset.mem_univ, true_and, Subtype.mk.injEq, Equiv.trans_apply, Equiv.coe_addLeft]
  exact ⟨fun ⟨i, hi⟩ => ⟨s + i, add_assoc s i 1 ▸ hi⟩,
    fun ⟨j, hj⟩ => ⟨j - s,
      by rwa [show s + (j - s) = j by abel, show s + (j - s + 1) = j + 1 by abel]⟩⟩

/-- For `3 ≤ M`, `i - 1 ≠ i + 1` in `Fin M`. -/
theorem fin_sub_one_ne_add_one {M : ℕ} [NeZero M] (hM : 3 ≤ M) (i : Fin M) :
    i - 1 ≠ i + 1 := by
  intro h
  have h20 : (1 + 1 : Fin M) = 0 := by rw [← sub_eq_zero.2 h.symm]; abel
  have hv := congrArg Fin.val h20
  rw [Fin.val_add, fin_one_val (by omega), Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
  omega

private theorem tour_vMid_zero_neighbor_vIn {W : Type*} [Fintype W] [DecidableEq W]
    (v₀ : W) (pad : ℕ) (adjD : W → W → Prop)
    (hM3 : 3 ≤ Fintype.card (SplitV W v₀ pad))
    (σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad)
    (hadj : ∀ i, (paddedSplitGraph v₀ pad adjD).Adj (σ i) (σ (i + 1))) (w : W) :
    let r := σ.symm (.vMid w ⟨0, splitMidLen_pos v₀ pad w⟩)
    σ (r - 1) = .vIn w ∨ σ (r + 1) = .vIn w := by
  intro r
  let m0 : SplitV W v₀ pad := .vMid w ⟨0, splitMidLen_pos v₀ pad w⟩
  have hr : σ r = m0 := σ.apply_symm_apply m0
  have hminus : (paddedSplitGraph v₀ pad adjD).Adj m0 (σ (r - 1)) := by
    rw [← hr]; have h := (hadj (r - 1)).symm; rwa [sub_add_cancel] at h
  have hplus : (paddedSplitGraph v₀ pad adjD).Adj m0 (σ (r + 1)) := by rw [← hr]; exact hadj r
  have hm_mem := (adj_vMid_iff v₀ pad adjD w ⟨0, splitMidLen_pos v₀ pad w⟩ _).1 hminus
  have hp_mem := (adj_vMid_iff v₀ pad adjD w ⟨0, splitMidLen_pos v₀ pad w⟩ _).1 hplus
  have hprev : midPrev v₀ pad w ⟨0, splitMidLen_pos v₀ pad w⟩ = .vIn w := by simp [midPrev]
  have hne : σ (r - 1) ≠ σ (r + 1) := fun h => fin_sub_one_ne_add_one hM3 r (σ.injective h)
  rcases hm_mem with hm | hm
  · exact Or.inl (hm.trans hprev)
  · exact Or.inr ((hp_mem.resolve_right fun hp => hne (hm.trans hp.symm)).trans hprev)

private def splitFin {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ) (n : ℕ) :
    Fin (Fintype.card (SplitV W v₀ pad)) :=
  ⟨n % Fintype.card (SplitV W v₀ pad), Nat.mod_lt _ Fintype.card_pos⟩

private theorem splitFin_val {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ)
    (i : Fin (Fintype.card (SplitV W v₀ pad))) : splitFin v₀ pad i.1 = i :=
  Fin.ext (Nat.mod_eq_of_lt i.2)

private theorem splitFin_succ {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ)
    (hM : 1 < Fintype.card (SplitV W v₀ pad)) (n : ℕ) :
    splitFin v₀ pad (n + 1) = splitFin v₀ pad n + 1 :=
  Fin.ext (by simp only [splitFin, Fin.val_add, fin_one_val hM, Nat.mod_add_mod])

private def splitStep {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ)
    (σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad) (n : ℕ) : SplitV W v₀ pad :=
  σ (splitFin v₀ pad n)

private theorem splitStep_fin {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ)
    (σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad)
    (i : Fin (Fintype.card (SplitV W v₀ pad))) :
    splitStep v₀ pad σ i.1 = σ i := by
  dsimp only [splitStep]; rw [splitFin_val]

private theorem splitStep_succ_fin {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ)
    (hM : 1 < Fintype.card (SplitV W v₀ pad))
    (σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad)
    (i : Fin (Fintype.card (SplitV W v₀ pad))) :
    splitStep v₀ pad σ (i.1 + 1) = σ (i + 1) := by
  dsimp only [splitStep]; rw [splitFin_succ v₀ pad hM, splitFin_val]

private theorem splitStep_adj {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ)
    (adjD : W → W → Prop) (hM : 1 < Fintype.card (SplitV W v₀ pad))
    (σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad)
    (hadj : ∀ i, (paddedSplitGraph v₀ pad adjD).Adj (σ i) (σ (i + 1))) (n : ℕ) :
    (paddedSplitGraph v₀ pad adjD).Adj (splitStep v₀ pad σ n) (splitStep v₀ pad σ (n + 1)) := by
  dsimp only [splitStep]
  rw [splitFin_succ v₀ pad hM]
  exact hadj _

private theorem splitStep_ne_add_two {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ)
    (hM3 : 3 ≤ Fintype.card (SplitV W v₀ pad))
    (σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad) (n : ℕ) :
    splitStep v₀ pad σ (n + 2) ≠ splitStep v₀ pad σ n := fun h => by
  have h2 : splitFin v₀ pad (n + 2) = splitFin v₀ pad (n + 1) + 1 :=
    splitFin_succ v₀ pad (by omega) (n + 1)
  have hn : splitFin v₀ pad n = splitFin v₀ pad (n + 1) - 1 := by
    rw [splitFin_succ v₀ pad (by omega) n, add_sub_cancel_right]
  exact fin_sub_one_ne_add_one hM3 (splitFin v₀ pad (n + 1))
    (by rw [← h2, ← hn]; exact (σ.injective h).symm)

private theorem splitTour_block_walk {W : Type*} [Fintype W] [DecidableEq W]
    (v₀ : W) (pad : ℕ) (adjD : W → W → Prop)
    (hM3 : 3 ≤ Fintype.card (SplitV W v₀ pad))
    (σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad)
    (hadj : ∀ i, (paddedSplitGraph v₀ pad adjD).Adj (σ i) (σ (i + 1)))
    (t : ℕ) (w : W)
    (ht0 : splitStep v₀ pad σ t = .vIn w)
    (ht1 : splitStep v₀ pad σ (t + 1) = .vMid w ⟨0, splitMidLen_pos v₀ pad w⟩) :
    (∀ k (hk : k < splitMidLen v₀ pad w),
      splitStep v₀ pad σ (t + 1 + k) = .vMid w ⟨k, hk⟩) ∧
    splitStep v₀ pad σ (t + 1 + splitMidLen v₀ pad w) = .vOut w ∧
    ∃ w', adjD w w' ∧
      splitStep v₀ pad σ (t + 2 + splitMidLen v₀ pad w) = .vIn w' ∧
      splitStep v₀ pad σ (t + 3 + splitMidLen v₀ pad w) =
        .vMid w' ⟨0, splitMidLen_pos v₀ pad w'⟩ := by
  have hlen := splitMidLen_pos v₀ pad w
  have hmid_step (k : ℕ) (hk : k < splitMidLen v₀ pad w)
      (hcur : splitStep v₀ pad σ (t + 1 + k) = .vMid w ⟨k, hk⟩)
      (hprev_eq : splitStep v₀ pad σ (t + k) = midPrev v₀ pad w ⟨k, hk⟩) :
      splitStep v₀ pad σ (t + 1 + k + 1) = midNext v₀ pad w ⟨k, hk⟩ := by
    have hnb := splitStep_adj v₀ pad adjD (by omega) σ hadj (t + 1 + k)
    rw [hcur] at hnb
    refine ((adj_vMid_iff v₀ pad adjD w ⟨k, hk⟩ _).1 hnb).resolve_left fun hprev => ?_
    rw [show t + 1 + k + 1 = t + k + 2 by omega] at hprev
    exact splitStep_ne_add_two v₀ pad hM3 σ (t + k) (hprev.trans hprev_eq.symm)
  have hmid_pair : ∀ k (hk : k < splitMidLen v₀ pad w),
      splitStep v₀ pad σ (t + 1 + k) = .vMid w ⟨k, hk⟩ ∧
      splitStep v₀ pad σ (t + k) = midPrev v₀ pad w ⟨k, hk⟩ := fun k => by
    induction k with
    | zero => exact fun _ => ⟨ht1, by simpa [midPrev] using ht0⟩
    | succ k ih =>
        intro hk1
        obtain ⟨hcur, hprev_eq⟩ := ih (by omega)
        have hnext := hmid_step k (by omega) hcur hprev_eq
        simp only [midNext, show ¬ k + 1 = splitMidLen v₀ pad w by omega, ↓reduceDIte] at hnext
        refine ⟨by simpa only [add_assoc] using hnext, ?_⟩
        rw [show t + (k + 1) = t + 1 + k by omega]
        simpa [midPrev] using hcur
  have hmid (k : ℕ) (hk : k < splitMidLen v₀ pad w) :
      splitStep v₀ pad σ (t + 1 + k) = .vMid w ⟨k, hk⟩ := (hmid_pair k hk).1
  have hout : splitStep v₀ pad σ (t + 1 + splitMidLen v₀ pad w) = .vOut w := by
    have hk : splitMidLen v₀ pad w - 1 < splitMidLen v₀ pad w := by omega
    have hnext := hmid_step _ hk (hmid_pair _ hk).1 (hmid_pair _ hk).2
    simp only [midNext, show splitMidLen v₀ pad w - 1 + 1 = splitMidLen v₀ pad w by omega,
      ↓reduceDIte] at hnext
    rwa [show t + 1 + splitMidLen v₀ pad w = t + 1 + (splitMidLen v₀ pad w - 1) + 1 by omega]
  have hnb_out := splitStep_adj v₀ pad adjD (by omega) σ hadj (t + 1 + splitMidLen v₀ pad w)
  rw [hout, show t + 1 + splitMidLen v₀ pad w + 1 = t + 2 + splitMidLen v₀ pad w by omega]
    at hnb_out
  have hex_in : ∃ w', adjD w w' ∧ splitStep v₀ pad σ (t + 2 + splitMidLen v₀ pad w) = .vIn w' := by
    cases hx : splitStep v₀ pad σ (t + 2 + splitMidLen v₀ pad w) with
    | vIn w' => rw [hx] at hnb_out; exact ⟨w', hnb_out, rfl⟩
    | vMid u k' =>
        exfalso; rw [hx] at hnb_out
        dsimp only [paddedSplitGraph, splitAdjRel] at hnb_out
        obtain ⟨rfl, hk'⟩ := hnb_out
        have hbad : splitStep v₀ pad σ (t + splitMidLen v₀ pad w + 2) =
            splitStep v₀ pad σ (t + splitMidLen v₀ pad w) := by
          rw [show t + splitMidLen v₀ pad w + 2 = t + 2 + splitMidLen v₀ pad w by omega, hx,
            show t + splitMidLen v₀ pad w = t + 1 + (splitMidLen v₀ pad w - 1) by omega,
            hmid _ (by omega)]
          congr 1; exact Fin.ext (by dsimp; omega)
        exact splitStep_ne_add_two v₀ pad hM3 σ _ hbad
    | vOut u => exfalso; rw [hx] at hnb_out; exact hnb_out
  obtain ⟨w', hww', hw'⟩ := hex_in
  have hw'1 : splitStep v₀ pad σ (t + 3 + splitMidLen v₀ pad w) =
      .vMid w' ⟨0, splitMidLen_pos v₀ pad w'⟩ := by
    let m0 : SplitV W v₀ pad := .vMid w' ⟨0, splitMidLen_pos v₀ pad w'⟩
    let r := σ.symm m0
    rcases tour_vMid_zero_neighbor_vIn v₀ pad adjD hM3 σ hadj w' with hm | hp
    · have hid := σ.injective (hw'.trans hm.symm)
      dsimp only [splitStep]
      rw [show t + 3 + splitMidLen v₀ pad w = (t + 2 + splitMidLen v₀ pad w) + 1 by omega,
        splitFin_succ v₀ pad (by omega), hid, sub_add_cancel]
      exact σ.apply_symm_apply m0
    · exfalso
      have hsucc : splitFin v₀ pad (t + 1 + splitMidLen v₀ pad w) + 1 = r + 1 := by
        rw [← σ.injective (hw'.trans hp.symm), ← splitFin_succ v₀ pad (by omega)]
        congr 1; omega
      have hbad : splitStep v₀ pad σ (t + 1 + splitMidLen v₀ pad w) = m0 := by
        dsimp only [splitStep]; rw [add_right_cancel hsucc]; exact σ.apply_symm_apply m0
      rw [hout] at hbad; dsimp only [m0] at hbad; cases hbad
  exact ⟨hmid, hout, w', hww', hw', hw'1⟩

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
  let M := Fintype.card (SplitV W v₀ pad)
  have hM_card : M = 3 * Fintype.card W + pad := card_splitV v₀ pad
  let mid0 : SplitV W v₀ pad := .vMid v₀ ⟨0, splitMidLen_pos v₀ pad v₀⟩
  let k0 : Fin M := σ₀.symm mid0
  have hk0_eq : σ₀ k0 = mid0 := σ₀.apply_symm_apply mid0
  obtain ⟨σ₁, htour₁, k₁, hk₁_eq, hk₁_prev⟩ :
      ∃ (σ₁ : Fin M ≃ SplitV W v₀ pad), tourEdgeSet σ₁ hM3 = tourEdgeSet σ₀ hM3 ∧
        ∃ k₁ : Fin M, σ₁ k₁ = mid0 ∧ σ₁ (k₁ - 1) = .vIn v₀ := by
    rcases tour_vMid_zero_neighbor_vIn v₀ pad adjD hM3 σ₀ (adj_of_tourEdgeSet_subset hsub) v₀ with
      hm | hp
    · exact ⟨σ₀, rfl, k0, hk0_eq, hm⟩
    · refine ⟨(Equiv.neg _).trans σ₀, tourEdgeSet_reverse σ₀ hM3, -k0,
        by change σ₀ (-(-k0)) = mid0; rw [neg_neg]; exact hk0_eq,
        by change σ₀ (-(-k0 - 1)) = .vIn v₀; rw [show -(-k0 - 1) = k0 + 1 by abel]; exact hp⟩
  let σ : Fin M ≃ SplitV W v₀ pad := (Equiv.addLeft (k₁ - 1)).trans σ₁
  have htour : tourEdgeSet σ hM3 = tourEdgeSet σ₀ hM3 :=
    (tourEdgeSet_shift σ₁ hM3 (k₁ - 1)).trans htour₁
  have hadj : ∀ i : Fin M, (paddedSplitGraph v₀ pad adjD).Adj (σ i) (σ (i + 1)) :=
    adj_of_tourEdgeSet_subset (htour ▸ hsub)
  let BlockState := {p : ℕ × W //
    splitStep v₀ pad σ p.1 = .vIn p.2 ∧
    splitStep v₀ pad σ (p.1 + 1) = .vMid p.2 ⟨0, splitMidLen_pos v₀ pad p.2⟩}
  let initBlock : BlockState :=
    ⟨(0, v₀),
      by rw [← Fin.val_zero (n := M), splitStep_fin]; change σ₁ ((k₁ - 1) + 0) = .vIn v₀
         rw [add_zero]; exact hk₁_prev,
      by rw [show (0 + 1 : ℕ) = (1 : Fin M).1 by rw [zero_add, fin_one_val (n := M) (by omega)],
        splitStep_fin]; change σ₁ ((k₁ - 1) + 1) = mid0; rw [sub_add_cancel]; exact hk₁_eq⟩
  let nextBlock (s : BlockState) :
      {s' : BlockState // s'.1.1 = s.1.1 + 2 + splitMidLen v₀ pad s.1.2 ∧ adjD s.1.2 s'.1.2} :=
    let h := splitTour_block_walk v₀ pad adjD hM3 σ hadj s.1.1 s.1.2 s.2.1 s.2.2
    let hw' := Classical.choose_spec h.2.2
    ⟨⟨(s.1.1 + 2 + splitMidLen v₀ pad s.1.2, _), hw'.2.1,
      by rw [show s.1.1 + 2 + splitMidLen v₀ pad s.1.2 + 1 =
          s.1.1 + 3 + splitMidLen v₀ pad s.1.2 by omega]; exact hw'.2.2⟩, rfl, hw'.1⟩
  let seq : ℕ → BlockState := Nat.rec initBlock fun _ s => (nextBlock s).1
  let pos : ℕ → ℕ := fun r => (seq r).1.1
  let vert : ℕ → W := fun r => (seq r).1.2
  have hseq_step (r : ℕ) : pos (r + 1) = pos r + 2 + splitMidLen v₀ pad (vert r) ∧
      adjD (vert r) (vert (r + 1)) := (nextBlock (seq r)).2
  have hmono : StrictMono pos := strictMono_nat_of_lt_succ fun r => by
    rw [(hseq_step r).1]; have := splitMidLen_pos v₀ pad (vert r); omega
  have hsum_pos (k : ℕ) : pos k = ∑ r ∈ Finset.range k, (2 + splitMidLen v₀ pad (vert r)) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Finset.sum_range_succ, ← ih, (hseq_step k).1, Nat.add_assoc]
  have htotal_sum : ∑ w : W, (2 + splitMidLen v₀ pad w) = M := by
    rw [hM_card, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      sum_splitMidLen]; ring
  have hwalk_lt : ∀ k ≤ Fintype.card W,
      Set.InjOn vert (Finset.range k) ∧ (∀ r < k, pos r < M) := by
    intro k hk
    induction k with
    | zero =>
        exact ⟨by simp, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ k ih =>
        obtain ⟨him_inj, hlt⟩ := ih (Nat.le_of_succ_le hk)
        have hpos_k : pos k < M := by
          obtain ⟨w_out, _, hw_out⟩ := Finset.exists_mem_notMem_of_card_lt_card
            (s := (Finset.range k).image vert) (t := Finset.univ)
            (by rw [Finset.card_image_of_injOn him_inj, Finset.card_range, Finset.card_univ]; omega)
          have hsum_le := Finset.sum_le_sum_of_subset (f := fun w => 2 + splitMidLen v₀ pad w)
            (Finset.subset_erase.2 ⟨Finset.subset_univ _, hw_out⟩)
          have herase := Finset.add_sum_erase Finset.univ (fun w => 2 + splitMidLen v₀ pad w)
            (Finset.mem_univ w_out)
          have him_sum := Finset.sum_image (f := fun w => 2 + splitMidLen v₀ pad w) him_inj
          have hpos_out := splitMidLen_pos v₀ pad w_out
          rw [hsum_pos k, ← him_sum]; omega
        have hne_prev : ∀ r₁ < k, vert r₁ ≠ vert k := fun r₁ hr₁ heq => by
          have hneq : (⟨pos r₁, hlt r₁ hr₁⟩ : Fin M) ≠ ⟨pos k, hpos_k⟩ := fun h =>
            Nat.ne_of_lt (hmono hr₁) (congrArg Fin.val h)
          apply hneq; apply σ.injective
          rw [← splitFin_val v₀ pad ⟨pos r₁, hlt r₁ hr₁⟩, ← splitFin_val v₀ pad ⟨pos k, hpos_k⟩]
          change splitStep v₀ pad σ (pos r₁) = splitStep v₀ pad σ (pos k)
          rw [(seq r₁).2.1, (seq k).2.1]
          exact congrArg SplitV.vIn heq
        refine ⟨?_, fun r hr => ?_⟩
        · rw [Finset.range_add_one, Finset.coe_insert, Set.injOn_insert (by simp)]
          exact ⟨him_inj, fun ⟨r, hr, heq⟩ => hne_prev r (by simpa using hr) heq⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr' | rfl <;> [exact hlt r hr'; exact hpos_k]
  obtain ⟨hm_inj, hpos_lt⟩ := hwalk_lt (Fintype.card W) le_rfl
  let m := Fintype.card W
  have : NeZero m := ⟨by omega⟩
  have hτ_inj : Function.Injective (fun t : Fin m => vert t.1) := fun t₁ t₂ heq =>
    Fin.ext (hm_inj (Finset.mem_range.2 t₁.2) (Finset.mem_range.2 t₂.2) heq)
  let τ : Fin m ≃ W := Equiv.ofBijective _
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨hτ_inj, Fintype.card_fin m⟩)
  have hpos_m : pos m = M := by
    have him_univ : (Finset.range m).image vert = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Finset.card_image_of_injOn hm_inj, Finset.card_range])
    rw [hsum_pos m, ← Finset.sum_image (f := fun w => 2 + splitMidLen v₀ pad w) hm_inj,
      him_univ, htotal_sum]
  have hvert_m : vert m = vert 0 := by
    have hstep_m : splitStep v₀ pad σ (pos m) = splitStep v₀ pad σ 0 := by
      simp only [splitStep, splitFin, hpos_m, M, Nat.mod_self, Nat.zero_mod]
    exact SplitV.vIn.inj ((seq m).2.1.symm.trans (hstep_m.trans (seq 0).2.1))
  have hvert_succ (t : Fin m) : vert (t + 1).1 = vert (t.1 + 1) := by
    by_cases hlast : t.1 + 1 = m
    · rw [fin_add_one_eq_zero (by omega) hlast, Fin.val_zero, hlast, hvert_m]
    · rw [Fin.val_add_one_of_lt' (by omega)]
  have hdir : IsDirTour adjD τ := fun t => by
    change adjD (vert t.1) (vert (t + 1).1); rw [hvert_succ]; exact (hseq_step t.1).2
  refine ⟨τ, hdir, fun u w => ?_⟩
  rw [← htour, mem_tourEdgeSet_iff]
  have hmid_ne {x y : SplitV W v₀ pad} {u' : W} {k' : Fin (splitMidLen v₀ pad u')}
      (h : x = .vMid u' k' ∨ y = .vMid u' k') : s(x, y) ≠ s(.vOut u, .vIn w) := by
    rcases h with rfl | rfl <;> intro h <;> simp at h
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨r, hlo, hhi⟩ := Fin.exists_le_lt_adjacent
      (f := fun j : Fin (m + 1) => pos j.val) (x := i.val)
      (by change pos 0 ≤ i.val; change 0 ≤ i.val; omega)
      (by change i.val < pos m; rw [hpos_m]; exact i.isLt)
    rcases r with ⟨r, hr⟩
    change pos r ≤ i.val at hlo
    change i.val < pos (r + 1) at hhi
    rw [← splitStep_fin v₀ pad σ i, ← splitStep_succ_fin v₀ pad (by omega) σ i] at hi
    have hwalk := splitTour_block_walk v₀ pad adjD hM3 σ hadj (pos r) (vert r)
      (seq r).2.1 (seq r).2.2
    have hstep_pos : pos (r + 1) = pos r + 2 + splitMidLen v₀ pad (vert r) := (hseq_step r).1
    by_cases h0 : i.1 = pos r
    · exact absurd hi (hmid_ne (Or.inr (by rw [h0]; exact (seq r).2.2)))
    · by_cases hmid : i.1 < pos r + 1 + splitMidLen v₀ pad (vert r)
      · exact absurd hi (hmid_ne (Or.inl (by
          rw [show i.1 = pos r + 1 + (i.1 - (pos r + 1)) by omega]
          exact hwalk.1 _ (by omega))))
      · have hlast : i.1 = pos r + 1 + splitMidLen v₀ pad (vert r) := by omega
        have hs1 : splitStep v₀ pad σ i.1 = .vOut (vert r) := hlast ▸ hwalk.2.1
        have hs2 : splitStep v₀ pad σ (i.1 + 1) = .vIn (vert (r + 1)) :=
          (show i.1 + 1 = pos (r + 1) by omega) ▸ (seq (r + 1)).2.1
        rw [hs1, hs2, Sym2.eq_iff] at hi
        rcases hi with ⟨hu, hw⟩ | ⟨hbad, _⟩
        · exact ⟨⟨r, hr⟩, SplitV.vOut.inj hu, by
            change vert (⟨r, hr⟩ + 1 : Fin m).1 = w; rw [hvert_succ]; exact SplitV.vIn.inj hw⟩
        · cases hbad
  · rintro ⟨t, rfl, rfl⟩
    let i : Fin M := ⟨pos t.1 + 1 + splitMidLen v₀ pad (vert t.1), by
      have := hpos_lt t.1 t.2; have hstep := (hseq_step t.1).1
      by_cases hlast : t.1 + 1 = m
      · rw [hlast, hpos_m] at hstep; omega
      · have := hpos_lt (t.1 + 1) (by omega); omega⟩
    refine ⟨i, ?_⟩
    rw [← splitStep_fin v₀ pad σ i, ← splitStep_succ_fin v₀ pad (by omega) σ i]
    have h1 := (splitTour_block_walk v₀ pad adjD hM3 σ hadj (pos t.1) (vert t.1)
      (seq t.1).2.1 (seq t.1).2.2).2.1
    have h2 : splitStep v₀ pad σ (i.1 + 1) = .vIn (vert (t + 1).1) := by
      rw [show i.1 + 1 = pos (t.1 + 1) by dsimp [i]; rw [(hseq_step t.1).1]; omega, hvert_succ]
      exact (seq (t.1 + 1)).2.1
    change s(splitStep v₀ pad σ i.1, splitStep v₀ pad σ (i.1 + 1)) =
      s(SplitV.vOut (vert t.1), SplitV.vIn (vert (t + 1).1))
    rw [h1, h2]

end SplitGraph
