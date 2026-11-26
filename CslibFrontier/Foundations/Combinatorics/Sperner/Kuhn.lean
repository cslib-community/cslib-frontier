/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Fin.Rotate
import CslibFrontier.Tactic.FinIndex
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.ZMod.Basic

/-!
# Sperner's lemma on the Kuhn-triangulated hypergrid

This file proves the `n`-dimensional Sperner lemma in its parity form on the hypergrid
`∏ i, [0, N i]` of Chen, Deng and Teng [ChenDengTeng2009] (Section 4.1, their `A^d_r` with `d = n`
and `r i = N i + 1`), triangulated by the Kuhn (Freudenthal) triangulation. This is the
`n`-dimensional counterpart of the triangulated square grid of `Cslib.Sperner.triangles`.

A Kuhn simplex (`KuhnSimplex`) lies in a unit cube with lower corner `base`; its `n + 1` vertices
(`KuhnSimplex.vertex`) form a maximal chain from the upper corner `base + 1` down to `base`,
lowering one coordinate at a time in the order prescribed by a permutation `rank`. For `n = 2`
these are the two triangles into which the diagonal cuts each grid cell.

Colours are `Fin (n + 1)`; colour `0` is the colour `d + 1` of Chen, Deng and Teng, as in
`Cslib.Sperner.boundaryColor`. A colouring satisfies the *Sperner boundary condition*
(`IsHypergridSperner`) when a point with `p i = 0` has a colour in `{i + 1, …, n}` and a point with
`p i = N i` does not have colour `i + 1`. Every *valid colouring* of Chen, Deng and Teng
(`IsValidColoring`, agreeing on the boundary with `hypergridBoundaryColor`: colour `i + 1` for the
largest `i` with `p i = 0`, colour `0` if there is none) satisfies it. The converse fails: the
condition restricts the boundary colours without fixing them, as the classical Sperner condition
on a simplex does. Note the naming: the two-dimensional `Cslib.Sperner.IsSpernerColoring` fixes the
boundary colours and so corresponds to `IsValidColoring`, not to the weaker `IsHypergridSperner`.

The proof is by induction on `n` and counts *doors*: facets carrying every colour except `0`
(`KuhnSimplex.IsDoor`). A simplex has an odd number of doors exactly when it is panchromatic
(`KuhnSimplex.odd_card_isDoor_iff`, from `odd_card_doors_iff_surjective`). Crossing an interior
facet (`KuhnSimplex.across`, `KuhnSimplex.mate`) is a fixed-point-free involution on the interior
doors, so their number is even. Under the Sperner boundary condition, the doors on the boundary of
the hypergrid lie on the face `x 0 = 0` and are the panchromatic simplices of the induced colouring
of that face, one dimension lower, whose number is odd by induction. No orientation is needed.

## Main definitions

* `Cslib.Sperner.KuhnSimplex`, `Cslib.Sperner.KuhnSimplex.vertex`: Kuhn simplices.
* `Cslib.Sperner.kuhnSimplices`: the simplices of the Kuhn triangulation of the hypergrid
  `∏ i, [0, N i]` (the name is descriptive: that they cover the hypergrid is not proved here).
* `Cslib.Sperner.IsPanchromatic`: a simplex whose vertices carry all `n + 1` colours.
* `Cslib.Sperner.IsHypergridSperner`: the Sperner boundary condition.
* `Cslib.Sperner.hypergridBoundaryColor`, `Cslib.Sperner.IsValidColoring`: the valid colourings of
  Chen, Deng and Teng.
* `Cslib.Sperner.KuhnSimplex.IsDoor`, `Cslib.Sperner.KuhnSimplex.across`,
  `Cslib.Sperner.KuhnSimplex.mate`, `Cslib.Sperner.KuhnSimplex.IsInteriorFacet`: doors and the
  adjacency of the triangulation.

## Main results

* `Cslib.Sperner.odd_card_doors_iff_surjective`: the door count of a single simplex.
* `Cslib.Sperner.KuhnSimplex.across_across`, `Cslib.Sperner.KuhnSimplex.across_mem`: crossing an
  interior facet of a simplex of the hypergrid lands in the hypergrid, and crossing back returns.
* `Cslib.Sperner.IsHypergridSperner.odd_card_isPanchromatic`: **Sperner's lemma**, parity form.
* `Cslib.Sperner.IsHypergridSperner.exists_isPanchromatic`: **Sperner's lemma**.
* `Cslib.Sperner.IsValidColoring.isHypergridSperner`: valid colourings satisfy the Sperner boundary
  condition.
* `Cslib.Sperner.IsValidColoring.exists_panchromatic`: Chen, Deng and Teng, Corollary 4.3.

Chen, Deng and Teng, Theorem 4.1 (a unit cube carrying all colours) follows at once from
`IsValidColoring.exists_panchromatic`, since a panchromatic simplex lies in a unit cube.

## References

* [X. Chen, X. Deng and S.-H. Teng, *Settling the complexity of computing two-player Nash
  equilibria*][ChenDengTeng2009]
-/

@[expose] public section

namespace Cslib.Sperner

open Finset

section Parity

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **Door parity.** Let `f : α → β` be a map between finite types of the same cardinality and
`b₀ : β`. Call `k : α` a *door* if every value other than `b₀` is taken by `f` away from `k`. Then
the number of doors is odd exactly when `f` is surjective. -/
theorem odd_card_doors_iff_surjective (f : α → β) (b₀ : β)
    (hcard : Fintype.card α = Fintype.card β) :
    Odd #{k | ∀ b ≠ b₀, ∃ j ≠ k, f j = b} ↔ Function.Surjective f := by
  by_cases hf : Function.Surjective f
  · simp only [hf, iff_true]
    have hinj : Function.Injective f :=
      (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, hcard⟩ |>.1
    obtain ⟨k₀, hk₀⟩ := hf b₀
    have : ({k | ∀ b ≠ b₀, ∃ j ≠ k, f j = b} : Finset α) = {k₀} := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      refine ⟨fun h => not_ne_iff.mp fun hk => ?_, ?_⟩
      · obtain ⟨j, hjk, hj⟩ := h (f k) fun h' => hk (hinj (h'.trans hk₀.symm))
        exact hjk (hinj hj)
      · rintro rfl b hb
        obtain ⟨j, rfl⟩ := hf b
        exact ⟨j, fun h => hb (h ▸ hk₀), rfl⟩
    rw [this, card_singleton]
    exact odd_one
  · simp only [hf, iff_false, Nat.not_odd_iff_even]
    by_cases hD : ∃ k, ∀ b ≠ b₀, ∃ j ≠ k, f j = b
    · obtain ⟨k, hk⟩ := hD
      obtain ⟨j₁, j₂, h12, hne⟩ := Function.not_injective_iff.1 fun hi =>
        hf ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hi, hcard⟩).2
      -- every door `l` makes `f` injective away from `l`
      have hdoor_inj : ∀ l, (∀ b ≠ b₀, ∃ j ≠ l, f j = b) →
          Set.InjOn f ((univ.erase l : Finset α) : Set α) := by
        intro l hl
        have hsub : univ.erase b₀ ⊆ (univ.erase l).image f := by
          intro b hb
          obtain ⟨j, hj, rfl⟩ := hl b (ne_of_mem_erase hb)
          exact mem_image.mpr ⟨j, mem_erase.mpr ⟨hj, mem_univ _⟩, rfl⟩
        refine card_image_iff.mp (le_antisymm card_image_le ?_)
        simpa [card_erase_of_mem, hcard] using card_le_card hsub
      have hD : ({k | ∀ b ≠ b₀, ∃ j ≠ k, f j = b} : Finset α) = {j₁, j₂} := by
        ext l
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        refine ⟨fun hl => ?_, ?_⟩
        · by_contra! h
          exact hne (hdoor_inj l hl (mem_coe.mpr (mem_erase.mpr ⟨h.1.symm, mem_univ _⟩))
            (mem_coe.mpr (mem_erase.mpr ⟨h.2.symm, mem_univ _⟩)) h12)
        · have key {i i'} (hii' : i ≠ i') (hfi : f i = f i') (b) (hb : b ≠ b₀) :
              ∃ j ≠ i, f j = b := by
            by_cases hbi : b = f i
            · exact ⟨i', hii'.symm, hbi ▸ hfi.symm⟩
            · obtain ⟨j, -, hj⟩ := hk b hb
              exact ⟨j, fun h => hbi (h ▸ hj.symm), hj⟩
          rintro (rfl | rfl)
          exacts [key hne h12, key hne.symm h12.symm]
      rw [hD, card_pair hne]
      exact ⟨1, rfl⟩
    · rw [filter_false_of_mem fun k _ h => hD ⟨k, h⟩, card_empty]
      exact ⟨0, rfl⟩

end Parity

/-- A simplex of the Kuhn triangulation of the integer lattice `ℕ ^ n`. It lies in the unit cube
with lower corner `base`; its vertices are the points of a maximal chain from the upper corner
`base + 1` down to `base`, which lowers the coordinates in the order given by `rank`: coordinate
`i` is lowered in step `rank i`. -/
@[ext]
structure KuhnSimplex (n : ℕ) where
  /-- The lower corner of the unit cube containing the simplex. -/
  base : Fin n → ℕ
  /-- Coordinate `i` is lowered from `base i + 1` to `base i` between vertices `rank i` and
  `rank i + 1`. -/
  rank : Equiv.Perm (Fin n)

namespace KuhnSimplex

variable {n : ℕ}

/-- Vertex `k` of a Kuhn simplex: coordinate `i` is `base i + 1` when `k ≤ rank i` and `base i`
otherwise. Vertex `0` is the upper corner `base + 1` and vertex `n` is the lower corner `base`. -/
def vertex (s : KuhnSimplex n) (k : Fin (n + 1)) (i : Fin n) : ℕ :=
  s.base i + if k ≤ (s.rank i).castSucc then 1 else 0

/-- The vertices of a Kuhn simplex lie above its lower corner. -/
theorem base_le_vertex (s : KuhnSimplex n) (k : Fin (n + 1)) (i : Fin n) :
    s.base i ≤ s.vertex k i :=
  Nat.le_add_right _ _

/-- The vertices of a Kuhn simplex lie below its upper corner. -/
theorem vertex_le_base_add_one (s : KuhnSimplex n) (k : Fin (n + 1)) (i : Fin n) :
    s.vertex k i ≤ s.base i + 1 :=
  Nat.add_le_add_left (by split_ifs <;> decide) _

/-- Kuhn simplices are pairs of a lower corner and a permutation. -/
def equivProd : KuhnSimplex n ≃ (Fin n → ℕ) × Equiv.Perm (Fin n) where
  toFun s := (s.base, s.rank)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : DecidableEq (KuhnSimplex n) := equivProd.decidableEq

end KuhnSimplex

open KuhnSimplex

/-- The simplices of the Kuhn triangulation of the hypergrid `∏ i, [0, N i]`: those whose cube
lies in the hypergrid. -/
def kuhnSimplices (n : ℕ) (N : Fin n → ℕ) : Finset (KuhnSimplex n) :=
  ((Fintype.piFinset fun i => range (N i)) ×ˢ (univ : Finset (Equiv.Perm (Fin n)))).map
    equivProd.symm.toEmbedding

@[simp]
theorem mem_kuhnSimplices {n : ℕ} {N : Fin n → ℕ} {s : KuhnSimplex n} :
    s ∈ kuhnSimplices n N ↔ ∀ i, s.base i < N i := by
  simp [kuhnSimplices, Finset.mem_map_equiv, equivProd]

/-- A Kuhn simplex is *panchromatic* for a colouring `c` with `n + 1` colours when its `n + 1`
vertices carry all the colours. -/
def IsPanchromatic {n : ℕ} (c : (Fin n → ℕ) → Fin (n + 1)) (s : KuhnSimplex n) : Prop :=
  Function.Surjective (c ∘ s.vertex)

instance {n : ℕ} (c : (Fin n → ℕ) → Fin (n + 1)) (s : KuhnSimplex n) :
    Decidable (IsPanchromatic c s) :=
  inferInstanceAs (Decidable (Function.Surjective _))

/-- The *Sperner boundary condition* on the hypergrid `∏ i, [0, N i]`, with colours `Fin (n + 1)`:
a point with `p i = 0` has a colour above `i` (one of `i + 1, …, n`), and a point with `p i = N i`
does not have colour `i + 1`. Interior points are unconstrained. -/
def IsHypergridSperner {n : ℕ} (N : Fin n → ℕ) (c : (Fin n → ℕ) → Fin (n + 1)) : Prop :=
  ∀ p : Fin n → ℕ, (∀ i, p i ≤ N i) → ∀ i,
    (p i = 0 → i.castSucc < c p) ∧ (p i = N i → c p ≠ i.succ)

namespace KuhnSimplex

variable {n : ℕ}

/-- The vertices of a simplex of the hypergrid lie in the hypergrid. -/
theorem vertex_le {N : Fin n → ℕ} {s : KuhnSimplex n} (hs : s ∈ kuhnSimplices n N)
    (k : Fin (n + 1)) (i : Fin n) : s.vertex k i ≤ N i := by
  have := mem_kuhnSimplices.mp hs i
  unfold vertex
  split_ifs <;> omega

/-! ### Facets and doors -/

/-- The facet of `s` opposite vertex `k` is a *door* for `c` when it carries every colour except
`0`. -/
def IsDoor (c : (Fin n → ℕ) → Fin (n + 1)) (s : KuhnSimplex n) (k : Fin (n + 1)) : Prop :=
  ∀ a ≠ 0, ∃ j ≠ k, c (s.vertex j) = a

instance (c : (Fin n → ℕ) → Fin (n + 1)) (s : KuhnSimplex n) (k : Fin (n + 1)) :
    Decidable (IsDoor c s k) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A simplex has an odd number of doors exactly when it is panchromatic. -/
theorem odd_card_isDoor_iff (c : (Fin n → ℕ) → Fin (n + 1)) (s : KuhnSimplex n) :
    Odd #{k | IsDoor c s k} ↔ IsPanchromatic c s := by
  rw [IsPanchromatic, ← odd_card_doors_iff_surjective (c ∘ s.vertex) 0 (by simp)]
  congr! 3

/-- The Kuhn simplex across the facet of `s` opposite vertex `k`. Removing the upper corner
(`k = 0`) lowers the cube along the coordinate lowered first; removing the lower corner
(`k = n + 1`) raises it along the coordinate lowered last; removing an intermediate vertex swaps
two consecutive steps of the chain. -/
def across (s : KuhnSimplex (n + 1)) (k : Fin (n + 2)) : KuhnSimplex (n + 1) :=
  if hk0 : k = 0 then
    ⟨fun i => if s.rank i = 0 then s.base i - 1 else s.base i,
      s.rank.trans (finRotate (n + 1)).symm⟩
  else if hkl : k = Fin.last (n + 1) then
    ⟨fun i => if s.rank i = Fin.last n then s.base i + 1 else s.base i,
      s.rank.trans (finRotate (n + 1))⟩
  else
    ⟨s.base, s.rank.trans (Equiv.swap (k.pred hk0) (k.castPred hkl))⟩

/-- The index of the vertex of `across s k` that is opposite the shared facet. -/
def mate (k : Fin (n + 2)) : Fin (n + 2) :=
  if k = 0 then Fin.last (n + 1) else if k = Fin.last (n + 1) then 0 else k

/-- The facet of `s` opposite vertex `k` is *interior*: it is not contained in a facet `x i = 0` or
`x i = N i` of the hypergrid `∏ i, [0, N i]`. The facet opposite the upper corner lies in the
hyperplane `x i = base i` for the coordinate `i` lowered first, and the facet opposite the lower
corner in the hyperplane `x i = base i + 1` for the coordinate `i` lowered last; the other facets
cross the interior of the cube of `s`. Crossing an interior facet of a simplex of the hypergrid
lands in the hypergrid (`across_mem`), and crossing back returns (`across_across`); that no other
simplex of the hypergrid contains the facet is not needed and not proved. -/
def IsInteriorFacet (N : Fin (n + 1) → ℕ) (s : KuhnSimplex (n + 1)) (k : Fin (n + 2)) : Prop :=
  (k = 0 → ∀ i, s.rank i = 0 → 0 < s.base i) ∧
    (k = Fin.last (n + 1) → ∀ i, s.rank i = Fin.last n → s.base i + 1 < N i)

instance (N : Fin (n + 1) → ℕ) (s : KuhnSimplex (n + 1)) (k : Fin (n + 2)) :
    Decidable (IsInteriorFacet N s k) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `mate` is an involution. -/
theorem mate_mate (k : Fin (n + 2)) : mate (mate k) = k := by
  by_cases hk0 : k = 0 <;> by_cases hkl : k = Fin.last (n + 1) <;>
    simp [mate, hk0, hkl, Fin.last_pos.ne']

private theorem finRotate_symm_zero : (finRotate (n + 1)).symm 0 = Fin.last n := by
  rw [Equiv.symm_apply_eq, finRotate_last]

private theorem val_finRotate_symm (a : Fin (n + 1)) :
    ((finRotate (n + 1)).symm a : ℕ) = if a = 0 then n else a - 1 := by
  split_ifs with h
  · rw [h, finRotate_symm_zero, Fin.val_last]
  · exact coe_finRotate_symm_of_ne_zero h

/-- Crossing the facet opposite the upper corner lowers the coordinate lowered first. -/
theorem base_across_zero (s : KuhnSimplex (n + 1)) (i : Fin (n + 1)) :
    (across s 0).base i = if s.rank i = 0 then s.base i - 1 else s.base i := rfl

/-- Crossing the facet opposite the upper corner rotates the order of the steps. -/
theorem rank_across_zero (s : KuhnSimplex (n + 1)) :
    (across s 0).rank = s.rank.trans (finRotate (n + 1)).symm := rfl

/-- Crossing the facet opposite the lower corner raises the coordinate lowered last. -/
theorem base_across_last (s : KuhnSimplex (n + 1)) (i : Fin (n + 1)) :
    (across s (Fin.last (n + 1))).base i =
      if s.rank i = Fin.last n then s.base i + 1 else s.base i := by
  simp only [across, Fin.last_pos.ne', ↓reduceDIte]

/-- Crossing the facet opposite the lower corner rotates the order of the steps. -/
theorem rank_across_last (s : KuhnSimplex (n + 1)) :
    (across s (Fin.last (n + 1))).rank = s.rank.trans (finRotate (n + 1)) := by
  simp only [across, Fin.last_pos.ne', ↓reduceDIte]

/-- Crossing a facet opposite an intermediate vertex keeps the cube. -/
theorem base_across_of_ne (s : KuhnSimplex (n + 1)) {k : Fin (n + 2)} (hk0 : k ≠ 0)
    (hkl : k ≠ Fin.last (n + 1)) : (across s k).base = s.base := by
  simp only [across, hk0, hkl, ↓reduceDIte]

/-- Crossing the facet opposite an intermediate vertex `k` swaps steps `k - 1` and `k`. -/
theorem rank_across_of_ne (s : KuhnSimplex (n + 1)) {k : Fin (n + 2)} (hk0 : k ≠ 0)
    (hkl : k ≠ Fin.last (n + 1)) :
    (across s k).rank = s.rank.trans (Equiv.swap (k.pred hk0) (k.castPred hkl)) := by
  simp only [across, hk0, hkl, ↓reduceDIte]

/-- Across the facet opposite the upper corner, the shared vertices are shifted down by one. -/
theorem vertex_across_zero {s : KuhnSimplex (n + 1)} (h : ∀ i, s.rank i = 0 → 0 < s.base i)
    (j : Fin (n + 1)) : (across s 0).vertex j.castSucc = s.vertex j.succ := by
  funext i
  simp only [vertex, base_across_zero, rank_across_zero, Equiv.trans_apply]
  have := h i
  fin_index [val_finRotate_symm]

/-- Across the facet opposite the lower corner, the shared vertices are shifted up by one. -/
theorem vertex_across_last (s : KuhnSimplex (n + 1)) (j : Fin (n + 1)) :
    (across s (Fin.last (n + 1))).vertex j.succ = s.vertex j.castSucc := by
  funext i
  simp only [vertex, base_across_last, rank_across_last, Equiv.trans_apply]
  fin_index [coe_finRotate]

/-- Across the facet opposite an intermediate vertex, the shared vertices are unchanged. -/
theorem vertex_across_of_ne {s : KuhnSimplex (n + 1)} {k : Fin (n + 2)} (hk0 : k ≠ 0)
    (hkl : k ≠ Fin.last (n + 1)) {j : Fin (n + 2)} (hj : j ≠ k) :
    (across s k).vertex j = s.vertex j := by
  funext i
  simp only [vertex, base_across_of_ne s hk0 hkl, rank_across_of_ne s hk0 hkl, Equiv.trans_apply]
  congr 1
  rcases eq_or_ne (s.rank i) (k.pred hk0) with h | h
  · rw [h, Equiv.swap_apply_left]
    fin_index
  · rcases eq_or_ne (s.rank i) (k.castPred hkl) with h' | h'
    · rw [h', Equiv.swap_apply_right]
      fin_index
    · rw [Equiv.swap_apply_of_ne_of_ne h h']

/-- The facet opposite the upper corner is opposite the lower corner of the neighbour. -/
theorem mate_zero : mate (0 : Fin (n + 2)) = Fin.last (n + 1) := by
  simp [mate]

/-- The facet opposite the lower corner is opposite the upper corner of the neighbour. -/
theorem mate_last : mate (Fin.last (n + 1)) = 0 := by
  simp [mate, Fin.last_pos.ne']

/-- A facet opposite an intermediate vertex is opposite the same vertex of the neighbour. -/
theorem mate_of_ne {k : Fin (n + 2)} (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1)) :
    mate k = k := by
  simp [mate, hk0, hkl]

private theorem finRotate_symm_eq_last {a : Fin (n + 1)} :
    (finRotate (n + 1)).symm a = Fin.last n ↔ a = 0 := by
  rw [← finRotate_symm_zero, Equiv.apply_eq_iff_eq]

private theorem finRotate_eq_zero {a : Fin (n + 1)} :
    finRotate (n + 1) a = 0 ↔ a = Fin.last n := by
  rw [← finRotate_last, Equiv.apply_eq_iff_eq]

/-- Crossing an interior facet twice returns to the starting simplex. -/
theorem across_across {N : Fin (n + 1) → ℕ} {s : KuhnSimplex (n + 1)} {k : Fin (n + 2)}
    (h : IsInteriorFacet N s k) : across (across s k) (mate k) = s := by
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [mate_zero]
    ext i
    · simp only [base_across_last, base_across_zero, rank_across_zero, Equiv.trans_apply,
        finRotate_symm_eq_last]
      have := h.1 rfl i
      split_ifs <;> omega
    · simp only [rank_across_last, rank_across_zero, Equiv.trans_apply, Equiv.apply_symm_apply]
  · rcases eq_or_ne k (Fin.last (n + 1)) with rfl | hkl
    · rw [mate_last]
      ext i
      · simp only [base_across_zero, base_across_last, rank_across_last, Equiv.trans_apply,
          finRotate_eq_zero]
        split_ifs <;> omega
      · simp only [rank_across_zero, rank_across_last, Equiv.trans_apply, Equiv.symm_apply_apply]
    · rw [mate_of_ne hk0 hkl]
      ext i
      · simp only [base_across_of_ne _ hk0 hkl]
      · simp only [rank_across_of_ne _ hk0 hkl, Equiv.trans_apply, Equiv.swap_apply_self]

/-- Crossing an interior facet stays in the hypergrid. -/
theorem across_mem {N : Fin (n + 1) → ℕ} {s : KuhnSimplex (n + 1)} {k : Fin (n + 2)}
    (hs : s ∈ kuhnSimplices (n + 1) N) (h : IsInteriorFacet N s k) :
    across s k ∈ kuhnSimplices (n + 1) N := by
  rw [mem_kuhnSimplices] at hs ⊢
  intro i
  have := hs i
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [base_across_zero]
    split_ifs <;> omega
  · rcases eq_or_ne k (Fin.last (n + 1)) with rfl | hkl
    · rw [base_across_last]
      split_ifs with hr
      exacts [h.2 rfl i hr, this]
    · rwa [base_across_of_ne _ hk0 hkl]

/-- The shared facet is interior from the other side as well. -/
theorem isInteriorFacet_across {N : Fin (n + 1) → ℕ} {s : KuhnSimplex (n + 1)}
    {k : Fin (n + 2)}
    (hs : s ∈ kuhnSimplices (n + 1) N) (h : IsInteriorFacet N s k) :
    IsInteriorFacet N (across s k) (mate k) := by
  have hl : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := Fin.last_pos.ne'
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [mate_zero]
    refine ⟨fun h' => absurd h' hl, fun _ i hi => ?_⟩
    rw [rank_across_zero, Equiv.trans_apply, finRotate_symm_eq_last] at hi
    rw [base_across_zero, ite_eq_left hi]
    have := h.1 rfl i hi
    have := mem_kuhnSimplices.mp hs i
    omega
  · rcases eq_or_ne k (Fin.last (n + 1)) with rfl | hkl
    · rw [mate_last]
      refine ⟨fun _ i hi => ?_, fun h' => absurd h'.symm hl⟩
      rw [rank_across_last, Equiv.trans_apply, finRotate_eq_zero] at hi
      rw [base_across_last, ite_eq_left hi]
      omega
    · rw [mate_of_ne hk0 hkl]
      exact ⟨fun h' => absurd h' hk0, fun h' => absurd h' hkl⟩

/-- Crossing a facet changes the simplex or the facet. -/
theorem across_ne (s : KuhnSimplex (n + 1)) (k : Fin (n + 2)) :
    (across s k, mate k) ≠ (s, k) := by
  intro h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  rcases eq_or_ne k 0 with rfl | hk0
  · exact Fin.last_pos.ne' (mate_zero ▸ h2)
  · rcases eq_or_ne k (Fin.last (n + 1)) with rfl | hkl
    · exact Fin.last_pos.ne (mate_last ▸ h2)
    · have := congrArg (fun t => t.rank (s.rank.symm (k.pred hk0))) h1
      simp only [rank_across_of_ne _ hk0 hkl, Equiv.trans_apply, Equiv.apply_symm_apply,
        Equiv.swap_apply_left] at this
      fin_index

/-- A door seen from the other side is a door. -/
theorem isDoor_across {c : (Fin (n + 1) → ℕ) → Fin (n + 2)} {N : Fin (n + 1) → ℕ}
    {s : KuhnSimplex (n + 1)} {k : Fin (n + 2)} (hd : IsDoor c s k) (h : IsInteriorFacet N s k) :
    IsDoor c (across s k) (mate k) := by
  intro a ha
  obtain ⟨j, hj, hja⟩ := hd a ha
  rcases eq_or_ne k 0 with rfl | hk0
  · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    exact ⟨j'.castSucc, mate_zero.symm ▸ (Fin.castSucc_lt_last j').ne,
      (congrArg c (vertex_across_zero (h.1 rfl) j')).trans hja⟩
  · rcases eq_or_ne k (Fin.last (n + 1)) with rfl | hkl
    · obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      exact ⟨j'.succ, mate_last.symm ▸ Fin.succ_ne_zero j',
        (congrArg c (vertex_across_last s j')).trans hja⟩
    · exact ⟨j, (mate_of_ne hk0 hkl).symm ▸ hj,
        (congrArg c (vertex_across_of_ne hk0 hkl hj)).trans hja⟩

/-! ### Boundary doors -/

/-- A door of a Sperner colouring that is not interior is the facet opposite the upper corner of a
simplex touching the face `x 0 = 0` along it. -/
theorem eq_zero_of_isDoor_of_not_isInteriorFacet {N : Fin (n + 1) → ℕ}
    {c : (Fin (n + 1) → ℕ) → Fin (n + 2)} (hc : IsHypergridSperner N c) {s : KuhnSimplex (n + 1)}
    (hs : s ∈ kuhnSimplices (n + 1) N) {k : Fin (n + 2)} (hd : IsDoor c s k)
    (hi : ¬IsInteriorFacet N s k) : k = 0 ∧ s.rank 0 = 0 ∧ s.base 0 = 0 := by
  simp only [IsInteriorFacet, not_and_or, not_imp, not_forall, not_lt, Nat.le_zero] at hi
  rcases hi with ⟨rfl, i, hri, hbi⟩ | ⟨rfl, i, hri, hbi⟩
  · obtain ⟨j, hj, hj1⟩ := hd 1 one_ne_zero
    have hv : s.vertex j i = 0 := by
      simp only [vertex, hbi, hri, Fin.castSucc_zero, Fin.le_zero_iff, hj, ite_false]
    have := (hc _ (vertex_le hs j) i).1 hv
    obtain rfl : i = 0 := by fin_index
    exact ⟨rfl, hri, hbi⟩
  · have hbi' := mem_kuhnSimplices.mp hs i
    obtain ⟨j, hj, hji⟩ := hd i.succ (Fin.succ_ne_zero i)
    have hv : s.vertex j i = N i := by
      rw [vertex, hri, ite_eq_left (Fin.le_castSucc_iff.mpr (Fin.lt_last_iff_ne_last.mpr hj))]
      omega
    exact ((hc _ (vertex_le hs j) i).2 hv hji).elim

/-- The facet opposite the upper corner of a simplex touching the face `x 0 = 0` along it is not
interior. -/
theorem not_isInteriorFacet_zero {N : Fin (n + 1) → ℕ} {s : KuhnSimplex (n + 1)}
    (hr : s.rank 0 = 0) (hb : s.base 0 = 0) : ¬IsInteriorFacet N s 0 := fun h => by
  have := h.1 rfl 0 hr
  omega

/-! ### The face `x 0 = 0` -/

/-- The facet opposite the upper corner of a simplex with `rank 0 = 0`, as a Kuhn simplex of the
face `x 0 = 0`. -/
private def face (s : KuhnSimplex (n + 1)) : KuhnSimplex n :=
  ⟨Fin.tail s.base, (Equiv.Perm.decomposeFin s.rank).2⟩

/-- The simplex of `ℕ ^ (n + 1)` with `rank 0 = 0` and `base 0 = 0` whose facet opposite the upper
corner is `t`. -/
private def ofFace (t : KuhnSimplex n) : KuhnSimplex (n + 1) :=
  ⟨Fin.cons 0 t.base, Equiv.Perm.decomposeFin.symm (0, t.rank)⟩

private theorem rank_ofFace_zero (t : KuhnSimplex n) : (ofFace t).rank 0 = 0 :=
  Equiv.Perm.decomposeFin_symm_apply_zero _ _

private theorem face_ofFace (t : KuhnSimplex n) : face (ofFace t) = t := by
  ext1
  · exact Fin.tail_cons (α := fun _ => ℕ) 0 t.base
  · simp only [face, ofFace, Equiv.apply_symm_apply]

private theorem decomposeFin_fst (σ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.decomposeFin σ).1 = σ 0 := by
  conv_rhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply σ]
  rw [Equiv.Perm.decomposeFin_symm_apply_zero]

private theorem ofFace_face {s : KuhnSimplex (n + 1)} (hr : s.rank 0 = 0) (hb : s.base 0 = 0) :
    ofFace (face s) = s := by
  ext1
  · rw [ofFace, face, ← hb]
    exact Fin.cons_self_tail _
  · simp only [ofFace, face]
    rw [← hr, ← decomposeFin_fst, Prod.mk.eta, Equiv.symm_apply_apply]

private theorem vertex_ofFace_succ (t : KuhnSimplex n) (k : Fin (n + 1)) :
    (ofFace t).vertex k.succ = Fin.cons 0 (t.vertex k) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [vertex, ofFace, Fin.cons_zero, Equiv.Perm.decomposeFin_symm_apply_zero,
      Fin.castSucc_zero, Fin.le_zero_iff, Fin.succ_ne_zero, ite_false]
  · simp only [vertex, ofFace, Fin.cons_succ, Equiv.Perm.decomposeFin_symm_apply_succ,
      Equiv.swap_self, Equiv.refl_apply]
    fin_index

private theorem ofFace_mem {N : Fin (n + 1) → ℕ} (hN : 0 < N 0) {t : KuhnSimplex n} :
    ofFace t ∈ kuhnSimplices (n + 1) N ↔ t ∈ kuhnSimplices n (Fin.tail N) := by
  simp only [mem_kuhnSimplices, ofFace]
  exact ⟨fun h i => h i.succ, fun h => Fin.cases hN h⟩

/-- The colouring induced on the face `x 0 = 0`, with colours lowered by one. -/
private def faceColoring (c : (Fin (n + 1) → ℕ) → Fin (n + 2)) (q : Fin n → ℕ) :
    Fin (n + 1) :=
  if h : c (Fin.cons 0 q) = 0 then 0 else (c (Fin.cons 0 q)).pred h

private theorem faceColoring_succ {c : (Fin (n + 1) → ℕ) → Fin (n + 2)} {q : Fin n → ℕ}
    (h : c (Fin.cons 0 q) ≠ 0) : (faceColoring c q).succ = c (Fin.cons 0 q) := by
  rw [faceColoring, dite_eq_right h, Fin.succ_pred]

private theorem cons_le {N : Fin (n + 1) → ℕ} {q : Fin n → ℕ}
    (hq : ∀ i, q i ≤ Fin.tail N i) :
    ∀ i, (Fin.cons 0 q : Fin (n + 1) → ℕ) i ≤ N i := fun i =>
  Fin.cases (Nat.zero_le _) (fun i => hq i) i

private theorem ne_zero_of_cons {N : Fin (n + 1) → ℕ}
    {c : (Fin (n + 1) → ℕ) → Fin (n + 2)}
    (hc : IsHypergridSperner N c) {q : Fin n → ℕ} (hq : ∀ i, q i ≤ Fin.tail N i) :
    c (Fin.cons 0 q) ≠ 0 :=
  ne_of_gt ((hc _ (cons_le hq) 0).1 rfl)

/-- The induced colouring of the face `x 0 = 0` satisfies the Sperner boundary condition. -/
private theorem isHypergridSperner_faceColoring {N : Fin (n + 1) → ℕ}
    {c : (Fin (n + 1) → ℕ) → Fin (n + 2)} (hc : IsHypergridSperner N c) :
    IsHypergridSperner (Fin.tail N) (faceColoring c) := by
  intro q hq i
  have hs := faceColoring_succ (ne_zero_of_cons hc hq)
  obtain ⟨h1, h2⟩ := hc _ (cons_le hq) i.succ
  rw [Fin.cons_succ] at h1 h2
  refine ⟨fun hqi => ?_, fun hqi heq => h2 hqi (hs.symm.trans (congrArg Fin.succ heq))⟩
  have := h1 hqi
  rw [← hs] at this
  fin_index

private theorem isDoor_ofFace_iff {N : Fin (n + 1) → ℕ}
    {c : (Fin (n + 1) → ℕ) → Fin (n + 2)}
    (hc : IsHypergridSperner N c) {t : KuhnSimplex n} (ht : t ∈ kuhnSimplices n (Fin.tail N)) :
    IsDoor c (ofFace t) 0 ↔ IsPanchromatic (faceColoring c) t := by
  have hv : ∀ k, c ((ofFace t).vertex k.succ) = (faceColoring c (t.vertex k)).succ := fun k => by
    rw [vertex_ofFace_succ, faceColoring_succ (ne_zero_of_cons hc (vertex_le ht k))]
  constructor
  · intro h b
    obtain ⟨j, hj, hjb⟩ := h b.succ (Fin.succ_ne_zero b)
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj
    exact ⟨k, Fin.succ_injective _ ((hv k).symm.trans hjb)⟩
  · intro h a ha
    obtain ⟨b, rfl⟩ := Fin.exists_succ_eq.mpr ha
    obtain ⟨k, hk⟩ := h b
    exact ⟨k.succ, Fin.succ_ne_zero k, (hv k).trans (congrArg Fin.succ hk)⟩

end KuhnSimplex

/-- The side lengths of a hypergrid carrying a Sperner colouring are positive. -/
theorem IsHypergridSperner.pos {n : ℕ} {N : Fin n → ℕ} {c : (Fin n → ℕ) → Fin (n + 1)}
    (hc : IsHypergridSperner N c) (i : Fin n) : 0 < N i := by
  by_contra h
  have hN := (hc N (fun _ => le_rfl) i).1 (Nat.eq_zero_of_not_pos h)
  obtain ⟨a, ha⟩ := Fin.exists_succ_eq.mpr (Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hN))
  exact (hc N (fun _ => le_rfl) a).2 rfl ha.symm

/-- A finite set with a fixed-point-free involution has even cardinality. -/
theorem even_card_of_involution {α : Type*} {T : Finset α} (g : α → α)
    (hmem : ∀ x ∈ T, g x ∈ T) (hinv : ∀ x ∈ T, g (g x) = x) (hne : ∀ x ∈ T, g x ≠ x) :
    Even #T := by
  rw [← ZMod.natCast_eq_zero_iff_even, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact sum_involution (fun x _ => g x) (fun _ _ => by decide) (fun x hx _ => hne x hx)
    (fun x hx => hmem x hx) (fun x hx => hinv x hx)

/-- **Sperner's lemma on the Kuhn-triangulated hypergrid**, parity form: a colouring of the
hypergrid `∏ i, [0, N i]` with `n + 1` colours that satisfies the Sperner boundary condition has an
odd number of panchromatic Kuhn simplices. -/
theorem IsHypergridSperner.odd_card_isPanchromatic {n : ℕ} {N : Fin n → ℕ}
    {c : (Fin n → ℕ) → Fin (n + 1)} (hc : IsHypergridSperner N c) :
    Odd #{s ∈ kuhnSimplices n N | IsPanchromatic c s} := by
  induction n with
  | zero =>
    have hall : ∀ s : KuhnSimplex 0, IsPanchromatic c s := fun s a => ⟨0, by omega⟩
    rw [filter_true_of_mem fun s _ => hall s]
    simp [kuhnSimplices]
  | succ n ih =>
    set S := kuhnSimplices (n + 1) N
    set D := (S ×ˢ (univ : Finset (Fin (n + 2)))).filter fun p => IsDoor c p.1 p.2
    -- the number of panchromatic simplices has the parity of the number of doors
    have hD : Odd #{s ∈ S | IsPanchromatic c s} ↔ Odd #D := by
      have : #D = ∑ s ∈ S, #{k | IsDoor c s k} := by simp only [D, card_filter, sum_product]
      simp only [this, odd_sum_iff_odd_card_odd, odd_card_isDoor_iff]
    rw [hD, ← card_filter_add_card_filter_not fun p => IsInteriorFacet N p.1 p.2]
    refine Even.add_odd ?_ ?_
    · -- interior doors are matched by crossing
      refine even_card_of_involution (fun p => (across p.1 p.2, mate p.2)) ?_ ?_ ?_
      · rintro ⟨s, k⟩ hp
        simp only [D, mem_filter, mem_product, mem_univ, and_true] at hp ⊢
        exact ⟨⟨across_mem hp.1.1 hp.2, isDoor_across hp.1.2 hp.2⟩,
          isInteriorFacet_across hp.1.1 hp.2⟩
      · rintro ⟨s, k⟩ hp
        simp only [D, mem_filter, mem_product, mem_univ, and_true] at hp
        simp only [across_across hp.2, mate_mate]
      · exact fun p _ => across_ne p.1 p.2
    · -- boundary doors are the panchromatic simplices of the face `x 0 = 0`
      have hN := hc.pos 0
      have hface := isHypergridSperner_faceColoring hc
      convert ih hface using 1
      refine card_nbij' (fun p => face p.1) (fun t => (ofFace t, 0)) ?_ ?_ ?_ ?_
      · rintro ⟨s, k⟩ hp
        simp only [D, coe_filter, mem_filter, mem_product, mem_univ, and_true,
          Set.mem_ofPred_eq] at hp ⊢
        obtain ⟨rfl, hr, hb⟩ := eq_zero_of_isDoor_of_not_isInteriorFacet hc hp.1.1 hp.1.2 hp.2
        rw [← ofFace_face hr hb] at hp
        rw [← ofFace_mem hN]
        exact ⟨hp.1.1, (isDoor_ofFace_iff hc ((ofFace_mem hN).mp hp.1.1)).mp hp.1.2⟩
      · intro t ht
        simp only [D, coe_filter, mem_filter, mem_product, mem_univ, and_true,
          Set.mem_ofPred_eq] at ht ⊢
        exact ⟨⟨(ofFace_mem hN).mpr ht.1, (isDoor_ofFace_iff hc ht.1).mpr ht.2⟩,
          not_isInteriorFacet_zero (rank_ofFace_zero t) rfl⟩
      · rintro ⟨s, k⟩ hp
        simp only [D, coe_filter, mem_filter, mem_product, mem_univ, and_true,
          Set.mem_ofPred_eq] at hp
        obtain ⟨rfl, hr, hb⟩ := eq_zero_of_isDoor_of_not_isInteriorFacet hc hp.1.1 hp.1.2 hp.2
        simp only [ofFace_face hr hb]
      · exact fun t _ => face_ofFace t

/-- **Sperner's lemma on the Kuhn-triangulated hypergrid**: a colouring satisfying the Sperner
boundary condition has a panchromatic Kuhn simplex. -/
theorem IsHypergridSperner.exists_isPanchromatic {n : ℕ} {N : Fin n → ℕ}
    {c : (Fin n → ℕ) → Fin (n + 1)} (hc : IsHypergridSperner N c) :
    ∃ s ∈ kuhnSimplices n N, IsPanchromatic c s := by
  obtain ⟨s, hs⟩ := card_pos.mp hc.odd_card_isPanchromatic.pos
  exact ⟨s, (mem_filter.mp hs).1, (mem_filter.mp hs).2⟩

/-! ### Valid colourings of Chen, Deng and Teng -/

/-- The boundary colouring of Chen, Deng and Teng: `p` has colour `i + 1` for the largest `i` with
`p i = 0`, and colour `0` (their colour `d + 1`) when no coordinate of `p` is `0`. -/
def hypergridBoundaryColor : {n : ℕ} → (Fin n → ℕ) → Fin (n + 1)
  | 0, _ => 0
  | _ + 1, p =>
    if p (Fin.last _) = 0 then Fin.last _ else (hypergridBoundaryColor (Fin.init p)).castSucc

/-- At a point with `p i = 0`, the boundary colour is above `i`. -/
theorem castSucc_lt_hypergridBoundaryColor {n : ℕ} {p : Fin n → ℕ} {i : Fin n}
    (h : p i = 0) :
    i.castSucc < hypergridBoundaryColor p := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [hypergridBoundaryColor]
    split_ifs with hl
    · exact Fin.castSucc_lt_last i
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr fun hi => hl (hi ▸ h)
      exact Fin.castSucc_lt_castSucc_iff.mpr (ih h)

/-- At a point with `p i ≠ 0`, the boundary colour is not `i + 1`. -/
theorem hypergridBoundaryColor_ne_succ {n : ℕ} {p : Fin n → ℕ} {i : Fin n}
    (h : p i ≠ 0) :
    hypergridBoundaryColor p ≠ i.succ := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [hypergridBoundaryColor]
    split_ifs with hl
    · exact fun he => h (Fin.succ_injective _ (Fin.succ_last n ▸ he) ▸ hl)
    · rcases eq_or_ne i (Fin.last n) with rfl | hi
      · exact Fin.succ_last n ▸ (Fin.castSucc_lt_last _).ne
      · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
        exact Fin.succ_castSucc j ▸ fun he => ih h (Fin.castSucc_injective _ he)

/-- A *valid colouring* of the hypergrid `∏ i, [0, N i]` in the sense of Chen, Deng and Teng: it
agrees with `hypergridBoundaryColor` at the boundary points, those with some `p i ∈ {0, N i}`. -/
def IsValidColoring {n : ℕ} (N : Fin n → ℕ) (c : (Fin n → ℕ) → Fin (n + 1)) : Prop :=
  ∀ p : Fin n → ℕ, (∀ i, p i ≤ N i) → (∃ i, p i = 0 ∨ p i = N i) → c p = hypergridBoundaryColor p

/-- A valid colouring of a hypergrid with positive side lengths satisfies the Sperner boundary
condition. -/
theorem IsValidColoring.isHypergridSperner {n : ℕ} {N : Fin n → ℕ}
    {c : (Fin n → ℕ) → Fin (n + 1)} (hc : IsValidColoring N c) (hN : ∀ i, 0 < N i) :
    IsHypergridSperner N c := fun p hp i =>
  ⟨fun h => hc p hp ⟨i, .inl h⟩ ▸ castSucc_lt_hypergridBoundaryColor h,
    fun h => hc p hp ⟨i, .inr h⟩ ▸ hypergridBoundaryColor_ne_succ (h ▸ (hN i).ne')⟩

/-- **Existence of a panchromatic simplex** (Chen, Deng and Teng, Corollary 4.3): a valid colouring
of a hypergrid with positive side lengths has a panchromatic simplex, a set of `n + 1` points with
`n + 1` distinct colours inside a unit cube `K_p` of the hypergrid. Positive side lengths
(`r i ≥ 2` for Chen, Deng and Teng) are needed: for `n = 1` and `N = ![0]` the hypergrid is a
single point. -/
theorem IsValidColoring.exists_panchromatic {n : ℕ} {N : Fin n → ℕ}
    {c : (Fin n → ℕ) → Fin (n + 1)} (hc : IsValidColoring N c) (hN : ∀ i, 0 < N i) :
    ∃ p : Fin n → ℕ, (∀ i, p i < N i) ∧ ∃ P : Finset (Fin n → ℕ),
      (∀ q ∈ P, ∀ i, q i = p i ∨ q i = p i + 1) ∧ #P = n + 1 ∧ Set.InjOn c P := by
  obtain ⟨s, hs, hpan⟩ := (hc.isHypergridSperner hN).exists_isPanchromatic
  have hinj : Function.Injective (c ∘ s.vertex) :=
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨hpan, rfl⟩).1
  refine ⟨s.base, mem_kuhnSimplices.mp hs, univ.image s.vertex, ?_, ?_, ?_⟩
  · intro q hq i
    obtain ⟨k, -, rfl⟩ := mem_image.mp hq
    unfold vertex
    split_ifs
    exacts [.inr rfl, .inl rfl]
  · rw [card_image_of_injective _ hinj.of_comp, card_univ, Fintype.card_fin]
  · rintro _ hx _ hy hxy
    obtain ⟨k, -, rfl⟩ := mem_image.mp (mem_coe.mp hx)
    obtain ⟨l, -, rfl⟩ := mem_image.mp (mem_coe.mp hy)
    rw [hinj hxy]

end Cslib.Sperner
