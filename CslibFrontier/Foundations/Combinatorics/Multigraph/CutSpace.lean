/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Multigraph
public import CslibFrontier.Foundations.Data.BitString.ZModSpace
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.EndpointIncidence
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The cut space of a multigraph

Taking edge cuts turns symmetric differences of sets of vertices into symmetric differences of sets
of edges (`Cslib.Multigraph.edgeCut_symmDiff`): an edge leaves `S ∆ T` exactly when it leaves one of
`S` and `T` but not both. This and `Cslib.Multigraph.mem_edgeCut_of_ends_eq` are the `Finset` forms
of Mathlib's `Graph.edgeCut_symmDiff` and `Graph.IsLink.mem_edgeCut_iff`, through
`Cslib.Multigraph.coe_edgeCut_eq_toGraph_edgeCut`. The edge cut of a single vertex consists of the
edges at it other than self-loops (`Cslib.Multigraph.edgeCut_singleton`), and on a connected
multigraph the only sets with no edge leaving them are `∅` and the set of all vertices
(`Cslib.Multigraph.eq_empty_or_eq_univ_of_edgeCut_eq_empty`).

Identifying subsets of `E` with their `0`/`1` indicator vectors over `𝔽₂ = ZMod 2` (or `Bool` via
`Cslib.BitString.submoduleZModIso`), the coboundary transpose of the `𝔽₂` vertex–edge incidence
matrix `Cslib.Multigraph.incidenceMatrix` (which agrees with `Matrix.endpointIncidence` for any
endpoint choice, dropping self-loops while retaining parallel edges) sends the indicator of `S` to
the indicator of `edgeCut ends S` (`Cslib.Multigraph.incidenceMatrix_transpose_mulVec_indicator`).
Its image `Cslib.Multigraph.cutSpace` consists of the indicator vectors of all edge cuts
(`Cslib.Multigraph.mem_cutSpace_iff_exists_edgeCut`), is spanned over `𝔽₂` by the vertex incidence
vectors (`Cslib.Multigraph.cutSpace_eq_span_incidence`), has dimension `|V| - 1` on every connected
multigraph (`Cslib.Multigraph.finrank_cutSpace_add_one`), and has the cycle / even-degree space
`ker (incidenceMatrix ends).mulVecLin` of cyclomatic dimension `|E| - |V| + 1` as its orthogonal
complement (`Cslib.Multigraph.orthogonal_cutSpace`,
`Cslib.Multigraph.finrank_ker_incidenceMatrix_add_card`).

A set `S` that fewer than `e(G)` edges leave (`Cslib.Multigraph.minBalancedCut`) is not balanced,
so it has fewer than a third or more than two thirds of the vertices. If moreover `S` has at most
two thirds of the vertices, it has fewer than a third of them
(`Cslib.Multigraph.three_mul_card_lt_of_card_edgeCut_lt`). This dichotomy is how expansion enters
degree lower bounds for Tseitin formulas in algebraic proof systems such as polynomial calculus.

## Main definitions

* `Cslib.Multigraph.incidenceMatrix`: the `𝔽₂` vertex–edge incidence matrix of `ends : E → Sym2 V`.
* `Cslib.Multigraph.cutSpace`: the `𝔽₂` cut space `range (incidenceMatrix ends)ᵀ.mulVecLin`.

## Main results

* `Cslib.Multigraph.edgeCut_symmDiff`: edge cuts turn symmetric differences into symmetric
  differences.
* `Cslib.Multigraph.edgeCut_empty`, `Cslib.Multigraph.edgeCut_singleton`: the edge cuts of `∅` and
  of a single vertex.
* `Cslib.Multigraph.eq_empty_or_eq_univ_of_edgeCut_eq_empty`: on a connected multigraph, only `∅`
  and the set of all vertices have empty edge cuts.
* `Cslib.Multigraph.incidenceMatrix_eq_endpointIncidence`: `incidenceMatrix ends` agrees with
  `Matrix.endpointIncidence u v` for any endpoint functions realizing `ends`.
* `Cslib.Multigraph.mem_cutSpace_iff_exists_edgeCut`,
  `Cslib.Multigraph.cutSpace_eq_span_incidence`: `cutSpace ends` consists of the indicator vectors
  of edge cuts and is spanned by the vertex incidence vectors `incidence ends v`.
* `Cslib.Multigraph.finrank_cutSpace_add_one`, `Cslib.Multigraph.orthogonal_cutSpace`,
  `Cslib.Multigraph.finrank_ker_incidenceMatrix_add_card`: on a connected multigraph, `cutSpace`
  has dimension `|V| - 1` and its orthogonal cycle space has dimension `|E| - |V| + 1`.
* `Cslib.Multigraph.three_mul_card_lt_of_card_edgeCut_lt`: a set of at most two thirds of the
  vertices that fewer than `e(G)` edges leave has fewer than a third of the vertices.

## References

* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
* [R. Diestel, *Graph Theory*][Diestel2025], §1.9
-/

public section

namespace Cslib.Multigraph

open Finset Matrix

section Combinatorial

variable {V E : Type*} (ends : E → Sym2 V) [Fintype V] [Fintype E] [DecidableEq V]

variable {ends} in
/-- An edge with ends `a` and `b` leaves `S` exactly when one of its ends is in `S` and the other
is not. -/
theorem mem_edgeCut_of_ends_eq {S : Finset V} {e : E} {a b : V} (h : ends e = s(a, b)) :
    e ∈ edgeCut ends S ↔ (a ∈ S ↔ b ∉ S) := by
  rw [← Finset.mem_coe, coe_edgeCut_eq_toGraph_edgeCut,
    (show (toGraph ends).IsLink e a b from h).mem_edgeCut_iff]
  simp only [Finset.mem_coe]
  tauto

/-- **Edge cuts turn symmetric differences into symmetric differences**: an edge leaves `S ∆ T`
exactly when it leaves one of `S` and `T` but not both. -/
theorem edgeCut_symmDiff [DecidableEq E] (S T : Finset V) :
    edgeCut ends (symmDiff S T) = symmDiff (edgeCut ends S) (edgeCut ends T) := by
  apply Finset.coe_injective
  rw [Finset.coe_symmDiff, coe_edgeCut_eq_toGraph_edgeCut, coe_edgeCut_eq_toGraph_edgeCut,
    coe_edgeCut_eq_toGraph_edgeCut, Finset.coe_symmDiff, Graph.edgeCut_symmDiff]

/-- No edge leaves the empty set. -/
@[simp] theorem edgeCut_empty : edgeCut ends (∅ : Finset V) = ∅ := by
  ext e
  simp [mem_edgeCut]

/-- The edges leaving a single vertex are the edges at it other than self-loops. -/
theorem edgeCut_singleton (v : V) : edgeCut ends {v} = incidence ends v := by
  ext e
  obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) :=
    Sym2.ind (f := fun z => ∃ a b, z = s(a, b)) (fun a b => ⟨a, b, rfl⟩) (ends e)
  rw [mem_edgeCut_of_ends_eq hab, mem_incidence_of_ends_eq hab, mem_singleton, mem_singleton]
  by_cases ha : a = v <;> by_cases hb : b = v <;> subst_vars <;> simp_all [eq_comm]

variable {ends}

/-- On a connected multigraph, **only `∅` and the set of all vertices have no edge leaving
them**. -/
theorem eq_empty_or_eq_univ_of_edgeCut_eq_empty (hG : (toSimpleGraph ends).Connected)
    {S : Finset V} (hS : edgeCut ends S = ∅) : S = ∅ ∨ S = univ := by
  by_contra! h
  obtain ⟨e, he⟩ := ((connected_toSimpleGraph_iff ends).1 hG).2 S h.1 h.2
  rw [hS] at he
  exact notMem_empty e he

/-- **The expansion dichotomy.** A set of at most two thirds of the vertices that fewer than
`e(G)` edges leave has fewer than a third of the vertices. -/
theorem three_mul_card_lt_of_card_edgeCut_lt {S : Finset V}
    (hS : #(edgeCut ends S) < minBalancedCut ends) (h₂ : 3 * #S ≤ 2 * Fintype.card V) :
    3 * #S < Fintype.card V := by
  by_contra! h₁
  exact absurd (minBalancedCut_le_card_edgeCut ends h₁ h₂) (not_le.2 hS)

end Combinatorial

/-! ### The `𝔽₂` incidence matrix, cut space, and orthogonal cycle space -/

section LinearAlgebra

/-- The `𝔽₂` vertex–edge incidence matrix of `ends : E → Sym2 V`: entry `(v, e)` is `1` when `e` is
a non-loop edge incident to `v`, and `0` otherwise. -/
@[expose] def incidenceMatrix {V E : Type*} [DecidableEq V] (ends : E → Sym2 V) :
    Matrix V E (ZMod 2) :=
  Matrix.of fun v e => if v ∈ ends e ∧ ¬(ends e).IsDiag then 1 else 0

@[simp]
theorem incidenceMatrix_apply {V E : Type*} [DecidableEq V] (ends : E → Sym2 V) (v : V) (e : E) :
    incidenceMatrix ends v e = if v ∈ ends e ∧ ¬(ends e).IsDiag then 1 else 0 :=
  rfl

/-- For any endpoint functions `u v : E → V` realizing `ends e = s(u e, v e)`, `incidenceMatrix`
equals `Matrix.endpointIncidence u v`: self-loops contribute `1 + 1 = 0` in `ZMod 2` while parallel
edges retain distinct columns. -/
theorem incidenceMatrix_eq_endpointIncidence {V E : Type*} [DecidableEq V] (ends : E → Sym2 V)
    {u v : E → V} (h : ∀ e, ends e = s(u e, v e)) :
    incidenceMatrix ends = Matrix.endpointIncidence u v := by
  ext a e
  simp only [incidenceMatrix, of_apply, Matrix.endpointIncidence, h e, Sym2.mem_iff,
    Sym2.mk_isDiag_iff]
  by_cases huv : u e = v e
  · rw [huv, CharTwo.add_self_eq_zero]
    simp
  · by_cases ha : a = u e
    · subst ha
      simp [huv]
    · by_cases hb : a = v e
      · subst hb
        simp [huv, Ne.symm huv]
      · simp [ha, hb]

/-- Row `v` of `incidenceMatrix ends` is the `𝔽₂` indicator vector of `incidence ends v`. -/
theorem incidenceMatrix_row {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (v : V) :
    incidenceMatrix ends v = fun e => if e ∈ incidence ends v then 1 else 0 := by
  ext e
  simp [incidenceMatrix]

/-- Applying `(incidenceMatrix ends)ᵀ` to the `𝔽₂` indicator of `S : Finset V` yields the `𝔽₂`
indicator of `edgeCut ends S`. -/
theorem incidenceMatrix_transpose_mulVec_indicator {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (S : Finset V) :
    (incidenceMatrix ends).transpose.mulVec (fun v => if v ∈ S then 1 else 0) =
      fun e => if e ∈ edgeCut ends S then 1 else 0 := by
  have hends : ∀ e, ends e = s((Quot.out (ends e)).1, (Quot.out (ends e)).2) :=
    fun e => (Quot.out_eq (ends e)).symm
  rw [incidenceMatrix_eq_endpointIncidence ends hends]
  ext e
  rw [Matrix.endpointIncidence_transpose_mulVec]
  simp only [mem_edgeCut_of_ends_eq (hends e)]
  by_cases h1 : (Quot.out (ends e)).1 ∈ S <;> by_cases h2 : (Quot.out (ends e)).2 ∈ S <;>
    simp only [h1, h2, ↓reduceIte, not_true_eq_false, not_false_eq_true, iff_false, iff_true,
      add_zero, zero_add, CharTwo.add_self_eq_zero]

/-- The **`𝔽₂` cut space** of `ends : E → Sym2 V`: the subspace
`LinearMap.range (incidenceMatrix ends)ᵀ.mulVecLin` of `E → ZMod 2`. -/
def cutSpace {V E : Type*} [Fintype V] [DecidableEq V] (ends : E → Sym2 V) :
    Submodule (ZMod 2) (E → ZMod 2) :=
  LinearMap.range (incidenceMatrix ends).transpose.mulVecLin

private theorem zmod_two_eq_indicator {V : Type*} [Fintype V] [DecidableEq V] (s : V → ZMod 2) :
    s = fun v => if v ∈ univ.filter (fun x => s x = 1) then 1 else 0 := by
  ext v
  simp only [mem_filter, mem_univ, true_and]
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (s v) with h0 | h1
  · rw [h0]
    rfl
  · simp [h1]

/-- A vector in `E → ZMod 2` belongs to `cutSpace ends` if and only if it is the indicator vector of
`edgeCut ends S` for some vertex set `S : Finset V`. -/
theorem mem_cutSpace_iff_exists_edgeCut {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] {ends : E → Sym2 V} {w : E → ZMod 2} :
    w ∈ cutSpace ends ↔ ∃ S : Finset V, w = fun e => if e ∈ edgeCut ends S then 1 else 0 := by
  rw [cutSpace, LinearMap.mem_range]
  refine ⟨fun ⟨s, hs⟩ => ⟨univ.filter fun v => s v = 1, ?_⟩, fun ⟨S, hS⟩ =>
    ⟨fun v => if v ∈ S then 1 else 0, hS ▸ incidenceMatrix_transpose_mulVec_indicator ends S⟩⟩
  rw [← hs, mulVecLin_apply]
  conv_lhs => rw [zmod_two_eq_indicator s]
  exact incidenceMatrix_transpose_mulVec_indicator ends _

/-- **Vertex-incidence spanning theorem**: `cutSpace ends` is spanned over `𝔽₂` by the indicator
vectors of the non-loop vertex incidences `incidence ends v`. -/
theorem cutSpace_eq_span_incidence {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (ends : E → Sym2 V) :
    cutSpace ends = Submodule.span (ZMod 2)
      (Set.range fun v : V => fun e : E => if e ∈ incidence ends v then (1 : ZMod 2) else 0) := by
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    have hsum : (incidenceMatrix ends).transpose.mulVecLin s =
        ∑ v : V, s v • incidenceMatrix ends v := by
      ext e
      simp only [mulVecLin_apply, mulVec, dotProduct, transpose_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, mul_comm (s _)]
    rw [hsum]
    refine Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, ?_⟩)
    exact (incidenceMatrix_row ends v).symm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, rfl⟩
    refine mem_cutSpace_iff_exists_edgeCut.mpr ⟨{v}, ?_⟩
    ext e
    rw [edgeCut_singleton]

/-- Under `BitString.submoduleZModIso`, the `Bool`-submodule corresponding to `cutSpace ends` is
spanned by the Boolean vertex-incidence indicators `fun e => decide (e ∈ incidence ends v)`. -/
theorem submoduleZModIso_symm_cutSpace {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (ends : E → Sym2 V) :
    (BitString.submoduleZModIso E).symm (cutSpace ends) =
      Submodule.span Bool (Set.range fun v : V => fun e : E => decide (e ∈ incidence ends v)) := by
  apply (BitString.submoduleZModIso E).injective
  rw [(BitString.submoduleZModIso E).apply_symm_apply, cutSpace_eq_span_incidence,
    BitString.submoduleZModIso_span, ← Set.range_comp]
  refine congrArg (Submodule.span (ZMod 2))
    (congrArg Set.range (funext fun v => funext fun e => ?_))
  change (if e ∈ incidence ends v then (1 : ZMod 2) else 0) =
    BitString.bitEquiv.symm (decide (e ∈ incidence ends v))
  by_cases h : e ∈ incidence ends v <;> simp [h]

/-- On a connected multigraph, the `𝔽₂` cut space has dimension `|V| - 1`. -/
theorem finrank_cutSpace_add_one {V E : Type*} [Fintype V] [Finite E] [DecidableEq V]
    {ends : E → Sym2 V} (hG : (toSimpleGraph ends).Connected) :
    Module.finrank (ZMod 2) (cutSpace ends) + 1 = Fintype.card V := by
  cases nonempty_fintype E
  let u : E → V := fun e => (Quot.out (ends e)).1
  let v : E → V := fun e => (Quot.out (ends e)).2
  have hends : ∀ e, ends e = s(u e, v e) := fun e => (Quot.out_eq (ends e)).symm
  obtain ⟨root⟩ := hG.nonempty
  have hconn : ∀ s : V → ZMod 2, (∀ e, s (u e) = s (v e)) → ∀ a b, s a = s b := by
    intro s hs a b
    let S : Finset V := univ.filter fun x => s x = 1
    have hempty : edgeCut ends S = ∅ := by
      ext e
      simp only [notMem_empty, iff_false]
      rw [mem_edgeCut_of_ends_eq (hends e)]
      simp only [S, mem_filter, mem_univ, true_and, hs e]
      tauto
    have hval : ∀ x, s x = if x ∈ S then 1 else 0 := fun x => congrFun (zmod_two_eq_indicator s) x
    rcases eq_empty_or_eq_univ_of_edgeCut_eq_empty hG hempty with hS | hS
    · simp [hval a, hval b, hS]
    · simp [hval a, hval b, hS]
  have hrank := Matrix.rank_endpointIncidence_add_one u v root hconn
  rw [← incidenceMatrix_eq_endpointIncidence ends hends, ← rank_transpose] at hrank
  exact hrank

/-- The orthogonal complement of `cutSpace ends` under `dotProduct` is the cycle (even-degree)
space `LinearMap.ker (incidenceMatrix ends).mulVecLin`. -/
theorem orthogonal_cutSpace {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (ends : E → Sym2 V) :
    BitString.orthogonal (cutSpace ends) = LinearMap.ker (incidenceMatrix ends).mulVecLin :=
  BitString.orthogonal_range_transpose_mulVecLin (incidenceMatrix ends)

/-- On a connected multigraph, the cycle space `ker (incidenceMatrix ends).mulVecLin` has
cyclomatic dimension `|E| - |V| + 1`, written `dim + |V| = |E| + 1`. -/
theorem finrank_ker_incidenceMatrix_add_card {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {ends : E → Sym2 V} (hG : (toSimpleGraph ends).Connected) :
    Module.finrank (ZMod 2) (LinearMap.ker (incidenceMatrix ends).mulVecLin) + Fintype.card V =
      Fintype.card E + 1 := by
  have h1 := BitString.finrank_orthogonal_add_finrank (cutSpace ends)
  rw [orthogonal_cutSpace] at h1
  have h2 := finrank_cutSpace_add_one hG
  omega

end LinearAlgebra

end Cslib.Multigraph
