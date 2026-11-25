/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Cuts of weighted multigraphs

An undirected weighted multigraph without self-loops on a finite vertex type `V` is given here by
its symmetric weight matrix `W : V → V → ℕ` with zero diagonal (`Cslib.WeightedCut.IsMultigraph`):
`W u v` is the total weight, or the number of parallel edges, joining distinct `u` and `v`. A set
`C` of vertices with `C` and its complement both nonempty is a non-trivial cut, its weight is the
total weight of the edges between `C` and its complement, and the global minimum cut weight is the
least weight of a non-trivial cut.

Contracting a multigraph along a surjective map `part : V → U` of the vertices onto supervertices
sums the weights between the vertices sent to distinct supervertices
(`Cslib.WeightedCut.IsContractionOf`). Pulling a cut of the contracted multigraph back to the
original vertices gives a cut of the same weight (`Cslib.WeightedCut.cutWeight_pullbackCut`), so
contraction never decreases the global minimum cut weight. Karger's contraction algorithm and the
Karger–Stein algorithm (`CslibFrontier.Algorithms.Karger.Graph`) are built on these facts.

The multigraphs given by their ends (`Cslib.Multigraph`) have weight matrices with the same cut
weights; see `CslibFrontier.Foundations.Combinatorics.WeightedCut.Multigraph`.

## Main definitions

* `Cslib.WeightedCut.IsMultigraph`: a symmetric weight matrix with zero diagonal.
* `Cslib.WeightedCut.IsNonTrivialCut`: a set of vertices whose complement is also nonempty.
* `Cslib.WeightedCut.cutWeight`, `Cslib.WeightedCut.minCut`: cut weights and the global minimum cut
  weight.
* `Cslib.WeightedCut.rowDeg`, `Cslib.WeightedCut.totalDoubledWeight`: weighted degrees and their
  sum, twice the total edge weight.
* `Cslib.WeightedCut.pullbackCut`, `Cslib.WeightedCut.IsContractionOf`: cuts pulled back along a
  supervertex map, and contracted multigraphs.

## Main results

* `Cslib.WeightedCut.cutWeight_compl`: a cut and its complement have the same weight.
* `Cslib.WeightedCut.cutWeight_singleton`: a singleton cut weighs the degree of its vertex.
* `Cslib.WeightedCut.cutWeight_fin_two`, `Cslib.WeightedCut.totalDoubledWeight_fin_two`: on two
  vertices, every non-trivial cut weighs the weight of the edge, and the degrees sum to twice it.
* `Cslib.WeightedCut.le_minCut_iff`: with at least two vertices, `m ≤ minCut W` exactly when every
  non-trivial cut weighs at least `m`.
* `Cslib.WeightedCut.mul_minCut_le_totalDoubledWeight`: `|V| * minCut W` is at most the sum of the
  degrees.
* `Cslib.WeightedCut.cutWeight_pullbackCut`: pulling a cut back along a contraction preserves its
  weight.
* `Cslib.WeightedCut.minCut_le_of_isContractionOf`: contraction does not decrease the global
  minimum cut weight.
* `Cslib.WeightedCut.two_vertex_contraction_output`: a contraction to two supervertices gives a
  non-trivial cut of the original multigraph whose weight is the remaining edge weight.
-/

@[expose] public section

namespace Cslib.WeightedCut

variable {V U : Type*}

/-! ### Weighted multigraphs and global minimum cuts -/

/-- An undirected weighted multigraph without self-loops on the vertices `V` is a symmetric weight
matrix `W : V → V → ℕ` with zero diagonal. -/
def IsMultigraph (W : V → V → ℕ) : Prop :=
  (∀ u v, W u v = W v u) ∧ (∀ u, W u u = 0)

variable [Fintype V]

/-- A vertex subset `C` defines a non-trivial cut when both `C` and its complement are
nonempty. -/
def IsNonTrivialCut (C : Finset V) : Prop :=
  C.Nonempty ∧ C ≠ Finset.univ

theorem isNonTrivialCut_iff_card (C : Finset V) :
    IsNonTrivialCut C ↔ 0 < C.card ∧ C.card < Fintype.card V :=
  Finset.card_pos.symm.and (Finset.card_lt_iff_ne_univ C).symm

theorem isNonTrivialCut_singleton (hV : 2 ≤ Fintype.card V) (a : V) :
    IsNonTrivialCut ({a} : Finset V) :=
  (isNonTrivialCut_iff_card _).2 (by simp; omega)

theorem exists_isNonTrivialCut (hV : 2 ≤ Fintype.card V) :
    ∃ C : Finset V, IsNonTrivialCut C :=
  have ⟨a⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  ⟨{a}, isNonTrivialCut_singleton hV a⟩

/-- Weighted degree of vertex `u` in `W`. -/
def rowDeg (W : V → V → ℕ) (u : V) : ℕ :=
  ∑ v : V, W u v

/-- Sum of all row degrees `∑ u, ∑ v, W u v`, equal to twice the total edge weight of `W`. -/
def totalDoubledWeight (W : V → V → ℕ) : ℕ :=
  ∑ u : V, rowDeg W u

theorem entry_le_rowDeg (W : V → V → ℕ) (u v : V) :
    W u v ≤ rowDeg W u :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)

theorem rowDeg_le_totalDoubledWeight (W : V → V → ℕ) (u : V) :
    rowDeg W u ≤ totalDoubledWeight W :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)

theorem entry_le_totalDoubledWeight (W : V → V → ℕ) (u v : V) :
    W u v ≤ totalDoubledWeight W :=
  (entry_le_rowDeg W u v).trans (rowDeg_le_totalDoubledWeight W u)

section Cut

variable [DecidableEq V]

theorem isNonTrivialCut_compl {C : Finset V} (hC : IsNonTrivialCut C) :
    IsNonTrivialCut (Finset.univ \ C) := by
  rcases hC with ⟨⟨x, hx⟩, hnu⟩
  exact ⟨Finset.sdiff_nonempty.2 fun h =>
      hnu (Finset.eq_univ_of_forall fun y => h (Finset.mem_univ y)),
    fun h => (Finset.mem_sdiff.1 (h ▸ Finset.mem_univ x)).2 hx⟩

/-- Total weight of edges crossing `(C, Finset.univ \ C)`, for weights in any additive
commutative monoid (natural numbers for multigraphs, or a linearly ordered field such as `ℝ`). -/
def cutWeight {M : Type*} [AddCommMonoid M] (W : V → V → M) (C : Finset V) : M :=
  ∑ u ∈ C, ∑ v ∈ Finset.univ \ C, W u v

/-- For symmetric weights, the cut `(Finset.univ \ C, C)` weighs as much as `(C, Finset.univ \ C)`.
-/
theorem cutWeight_univ_sdiff_of_symm {M : Type*} [AddCommMonoid M] {W : V → V → M}
    (hW : ∀ u v, W u v = W v u) (C : Finset V) :
    cutWeight W (Finset.univ \ C) = cutWeight W C := by
  simp only [cutWeight, Finset.sdiff_sdiff_eq_self (Finset.subset_univ C)]
  exact Finset.sum_comm.trans <|
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hW v u

theorem cutWeight_compl {W : V → V → ℕ} (hW : IsMultigraph W) (C : Finset V) :
    cutWeight W (Finset.univ \ C) = cutWeight W C :=
  cutWeight_univ_sdiff_of_symm hW.1 C

theorem cutWeight_le_sum_rowDeg (W : V → V → ℕ) (C : Finset V) :
    cutWeight W C ≤ ∑ u ∈ C, rowDeg W u :=
  Finset.sum_le_sum fun _ _ => Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

theorem two_mul_cutWeight_le_totalDoubledWeight {W : V → V → ℕ} (hW : IsMultigraph W)
    (C : Finset V) :
    2 * cutWeight W C ≤ totalDoubledWeight W := by
  have h1 := cutWeight_le_sum_rowDeg W C
  have h2 := cutWeight_compl hW C ▸ cutWeight_le_sum_rowDeg W (Finset.univ \ C)
  have hsum : (∑ u ∈ C, rowDeg W u) + ∑ u ∈ Finset.univ \ C, rowDeg W u = totalDoubledWeight W := by
    rw [← Finset.sum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ C)]
    rfl
  omega

theorem cutWeight_singleton {W : V → V → ℕ} (hW : IsMultigraph W) (a : V) :
    cutWeight W {a} = rowDeg W a := by
  simp only [cutWeight, rowDeg, Finset.sum_singleton, ← Finset.erase_eq]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), hW.2, zero_add]

theorem cutWeight_two_singleton_zero {W : Fin 2 → Fin 2 → ℕ} (hW : IsMultigraph W) :
    cutWeight W ({0} : Finset (Fin 2)) = W 0 1 := by
  simp [cutWeight_singleton hW 0, rowDeg, Fin.sum_univ_two, hW.2]

/-- On two vertices, every non-trivial cut weighs the weight of the edge. -/
theorem cutWeight_fin_two {W : Fin 2 → Fin 2 → ℕ} (hW : IsMultigraph W) {B : Finset (Fin 2)}
    (hB : IsNonTrivialCut B) : cutWeight W B = W 0 1 := by
  rw [isNonTrivialCut_iff_card, Fintype.card_fin] at hB
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp (show B.card = 1 by omega)
  match b with
  | 0 => exact cutWeight_two_singleton_zero hW
  | 1 =>
    rw [show ({1} : Finset (Fin 2)) = Finset.univ \ {0} by decide, cutWeight_compl hW,
      cutWeight_two_singleton_zero hW]

/-- On two vertices, the sum of the degrees is twice the weight of the edge. -/
theorem totalDoubledWeight_fin_two {W : Fin 2 → Fin 2 → ℕ} (hW : IsMultigraph W) :
    totalDoubledWeight W = 2 * W 0 1 := by
  simp only [totalDoubledWeight, rowDeg, Fin.sum_univ_two, hW.2, hW.1 1 0]
  omega

/-- Global minimum cut weight of a multigraph `W`, defined as the greatest lower bound of
`cutWeight W C` over all non-trivial cuts `C`. -/
noncomputable def minCut (W : V → V → ℕ) : ℕ :=
  sInf {k | ∃ C : Finset V, IsNonTrivialCut C ∧ cutWeight W C = k}

theorem minCut_le_cutWeight (W : V → V → ℕ) {C : Finset V} (hC : IsNonTrivialCut C) :
    minCut W ≤ cutWeight W C :=
  Nat.sInf_le ⟨C, hC, rfl⟩

theorem exists_minCut_achiever (hV : 2 ≤ Fintype.card V) (W : V → V → ℕ) :
    ∃ C : Finset V, IsNonTrivialCut C ∧ cutWeight W C = minCut W := by
  obtain ⟨C₀, hC₀⟩ := exists_isNonTrivialCut hV
  exact Nat.sInf_mem (s := {k | ∃ C : Finset V, IsNonTrivialCut C ∧ cutWeight W C = k})
    ⟨_, C₀, hC₀, rfl⟩

theorem le_minCut_iff (hV : 2 ≤ Fintype.card V) (W : V → V → ℕ) (m : ℕ) :
    m ≤ minCut W ↔ ∀ C : Finset V, IsNonTrivialCut C → m ≤ cutWeight W C := by
  refine ⟨fun hm _ hC => hm.trans (minCut_le_cutWeight W hC), fun h => ?_⟩
  obtain ⟨C, hC, hEq⟩ := exists_minCut_achiever hV W
  exact hEq ▸ h C hC

theorem minCut_pos_iff (hV : 2 ≤ Fintype.card V) (W : V → V → ℕ) :
    0 < minCut W ↔ ∀ C : Finset V, IsNonTrivialCut C → 0 < cutWeight W C :=
  le_minCut_iff hV W 1

theorem minCut_le_rowDeg (hV : 2 ≤ Fintype.card V) {W : V → V → ℕ} (hW : IsMultigraph W)
    (a : V) :
    minCut W ≤ rowDeg W a :=
  cutWeight_singleton hW a ▸ minCut_le_cutWeight W (isNonTrivialCut_singleton hV a)

theorem mul_minCut_le_totalDoubledWeight (hV : 2 ≤ Fintype.card V) {W : V → V → ℕ}
    (hW : IsMultigraph W) :
    Fintype.card V * minCut W ≤ totalDoubledWeight W := by
  simpa [totalDoubledWeight] using Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) =>
    minCut_le_rowDeg hV hW u

theorem totalDoubledWeight_pos_of_minCut_pos (hV : 2 ≤ Fintype.card V) {W : V → V → ℕ}
    (hW : IsMultigraph W) (hpos : 0 < minCut W) :
    0 < totalDoubledWeight W :=
  (Nat.mul_pos (by omega) hpos).trans_le (mul_minCut_le_totalDoubledWeight hV hW)

end Cut

/-! ### Supervertex maps and contractions -/

variable [DecidableEq U]

/-- Pull back a cut `B` of the supervertices along a supervertex map `part : V → U`. -/
def pullbackCut (part : V → U) (B : Finset U) : Finset V :=
  Finset.univ.filter fun x => part x ∈ B

theorem mem_pullbackCut (part : V → U) (B : Finset U) (x : V) :
    x ∈ pullbackCut part B ↔ part x ∈ B := by
  simp [pullbackCut]

theorem pullbackCut_empty (part : V → U) :
    pullbackCut part ∅ = ∅ := by
  ext; simp [pullbackCut]

/-- `W : U → U → ℕ` is the contracted multigraph of `W₀ : V → V → ℕ` along the surjective
supervertex assignment `part : V → U`: the weight between distinct supervertices is the total
weight between the vertices sent to them. -/
structure IsContractionOf (W₀ : V → V → ℕ) (part : V → U) (W : U → U → ℕ) : Prop where
  surj : Function.Surjective part
  multigraph : IsMultigraph W
  offDiag : ∀ a b : U, a ≠ b →
    W a b = ∑ x ∈ Finset.univ.filter (part · = a),
      ∑ y ∈ Finset.univ.filter (part · = b), W₀ x y

variable [Fintype U]

theorem pullbackCut_univ (part : V → U) :
    pullbackCut part Finset.univ = Finset.univ := by
  ext; simp [pullbackCut]

theorem isNonTrivialCut_pullbackCut {part : V → U} (hsurj : Function.Surjective part)
    {B : Finset U} (hB : IsNonTrivialCut B) :
    IsNonTrivialCut (pullbackCut part B) := by
  rcases hB with ⟨⟨b, hb⟩, hnu⟩
  obtain ⟨x, rfl⟩ := hsurj b
  refine ⟨⟨x, by simp [pullbackCut, hb]⟩, fun hall => hnu (Finset.eq_univ_of_forall fun b' => ?_)⟩
  obtain ⟨y, rfl⟩ := hsurj b'
  simpa [pullbackCut] using (hall ▸ Finset.mem_univ y : y ∈ pullbackCut part B)

theorem isNonTrivialCut_of_pullbackCut (part : V → U) {B : Finset U}
    (h : IsNonTrivialCut (pullbackCut part B)) :
    IsNonTrivialCut B := by
  rcases h with ⟨⟨x, hx⟩, hnu⟩
  exact ⟨⟨part x, (mem_pullbackCut part B x).mp hx⟩, fun hBu => hnu (hBu ▸ pullbackCut_univ part)⟩

variable [DecidableEq V]

theorem pullbackCut_compl (part : V → U) (B : Finset U) :
    pullbackCut part (Finset.univ \ B) = Finset.univ \ pullbackCut part B := by
  ext; simp [pullbackCut]

theorem isContractionOf_id {W₀ : V → V → ℕ} (hW₀ : IsMultigraph W₀) :
    IsContractionOf W₀ id W₀ where
  surj := Function.surjective_id
  multigraph := hW₀
  offDiag a b _ := by simp [Finset.filter_eq']

theorem cutWeight_pullbackCut {W₀ : V → V → ℕ} {part : V → U} {W : U → U → ℕ}
    (hC : IsContractionOf W₀ part W) (B : Finset U) :
    cutWeight W₀ (pullbackCut part B) = cutWeight W B := by
  have hdecomp (S : Finset U) (f : V → ℕ) :
      ∑ x ∈ pullbackCut part S, f x = ∑ a ∈ S, ∑ x ∈ Finset.univ.filter (part · = a), f x := by
    rw [← Finset.sum_fiberwise_of_maps_to fun _ hx => (mem_pullbackCut part S _).1 hx]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [pullbackCut, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    exact fun h => h ▸ ha
  simp only [cutWeight, ← pullbackCut_compl, hdecomp]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_comm.trans <|
    Finset.sum_congr rfl fun b hb => ?_
  exact (hC.offDiag a b fun h => (Finset.mem_sdiff.1 hb).2 (h ▸ ha)).symm

theorem minCut_le_of_isContractionOf (hU : 2 ≤ Fintype.card U) {W₀ : V → V → ℕ}
    {part : V → U} {W : U → U → ℕ} (hC : IsContractionOf W₀ part W) :
    minCut W₀ ≤ minCut W :=
  (le_minCut_iff hU W _).2 fun B hB =>
    cutWeight_pullbackCut hC B ▸ minCut_le_cutWeight W₀ (isNonTrivialCut_pullbackCut hC.surj hB)

theorem two_vertex_contraction_output {W₀ : V → V → ℕ} {part : V → Fin 2}
    {W : Fin 2 → Fin 2 → ℕ} (hC : IsContractionOf W₀ part W) :
    IsNonTrivialCut (pullbackCut part ({0} : Finset (Fin 2))) ∧
      W 0 1 = cutWeight W₀ (pullbackCut part ({0} : Finset (Fin 2))) ∧
      minCut W₀ ≤ W 0 1 := by
  have hnt : IsNonTrivialCut (pullbackCut part ({0} : Finset (Fin 2))) :=
    isNonTrivialCut_pullbackCut hC.surj (isNonTrivialCut_singleton (by simp) 0)
  have hcw : cutWeight W₀ (pullbackCut part ({0} : Finset (Fin 2))) = W 0 1 := by
    rw [cutWeight_pullbackCut hC, cutWeight_two_singleton_zero hC.multigraph]
  exact ⟨hnt, hcw.symm, hcw ▸ minCut_le_cutWeight W₀ hnt⟩

end Cslib.WeightedCut
