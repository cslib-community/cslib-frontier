/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Fintype.Perm

/-!
# Correlated sampling of grid distributions from a finite seed

A *grid distribution* on a finite type `α` with denominator `L` gives every point a probability
that is a multiple of `1 / L`; it is described by its counts `c x` with `∑ x, c x = L`
(`GridDist`). Such a distribution is the projection of the uniform distribution on its set of
*cells* `{(x, u) : u < c x}` in `α × Fin L`, a set of exactly `L` cells.

This module gives Holenstein's correlated sampling protocol for grid distributions with a
finite shared seed: a uniformly random enumeration `σ` of `α × Fin L`. Each party outputs the
point of the first of its own cells in the enumeration (`gridSample`), so it needs only the seed
and its own distribution. Under the uniform seed the first element of a set of cells is uniform on
that set (`toOuterMeasure_first_mem`), so each party samples exactly its own distribution
(`map_gridSample`). The parties agree whenever the first cell of the union of their cell sets is
common to both, so they disagree with probability at most `2 d_TV(P, Q)`
(`gridSample_disagree_le`).

The finite seed is what makes the protocol usable where randomness must be a `PMF`, as in
`Cslib.MachineLearning.Replicable.Algorithm`. Holenstein's protocol for arbitrary distributions
(`Cslib.Probability.CorrelatedSampling.seedSample`) needs a continuous seed.

## Main definitions

* `Cslib.Probability.CorrelatedSampling.first`: the first element of a nonempty set in an
  enumeration.
* `Cslib.Probability.CorrelatedSampling.GridDist`: a grid distribution, given by its counts.
* `Cslib.Probability.CorrelatedSampling.gridSample`: the party's output for a grid distribution.

## Main results

* `Cslib.Probability.CorrelatedSampling.toOuterMeasure_first_mem`: the first element of `S` under
  a uniform enumeration lies in `R` with probability `#(S ∩ R) / #S`.
* `Cslib.Probability.CorrelatedSampling.map_gridSample`: each party samples its own distribution.
* `Cslib.Probability.CorrelatedSampling.gridSample_disagree_le`: the parties disagree with
  probability at most `2 d_TV(P, Q)`.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*]
  [Holenstein2009], §5, Figure 1 and the proof of Lemma 5.2, pp. 152–153: the protocol with a
  continuous seed, sampled with replacement.
-/

public section

namespace Cslib.Probability.CorrelatedSampling

open Finset
open scoped ENNReal Cslib.Probability.PMF

section First

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- An enumeration of the finite type `β`, the shared seed of the protocol. -/
abbrev Enumeration (β : Type*) [Fintype β] := Fin (Fintype.card β) ≃ β

instance : Nonempty (Enumeration β) := ⟨(Fintype.equivFin β).symm⟩

/-- The first element of the nonempty set `S` in the enumeration `σ`. -/
def first (σ : Enumeration β) (S : Finset β) (hS : S.Nonempty) : β :=
  σ ((univ.filter fun i => σ i ∈ S).min'
    (let ⟨b, hb⟩ := hS; ⟨σ.symm b, by simpa using hb⟩))

/-- `b` is the first element of `S` in `σ` exactly when it lies in `S` and no element of `S` comes
before it. -/
theorem first_eq_iff (σ : Enumeration β) {S : Finset β} (hS : S.Nonempty) {b : β} :
    first σ S hS = b ↔ b ∈ S ∧ ∀ i, σ i ∈ S → σ.symm b ≤ i := by
  unfold first
  constructor
  · rintro rfl
    have hm := min'_mem (univ.filter fun i => σ i ∈ S)
      (let ⟨b, hb⟩ := hS; ⟨σ.symm b, by simpa using hb⟩)
    exact ⟨(mem_filter.1 hm).2, fun i hi =>
      (σ.symm_apply_apply _).trans_le (min'_le _ i (by simp [hi]))⟩
  · rintro ⟨hb, hmin⟩
    rw [le_antisymm (min'_le _ _ (by simp [hb]))
      (le_min' _ _ _ fun i hi => hmin i (by simpa using hi)), Equiv.apply_symm_apply]

theorem first_mem (σ : Enumeration β) {S : Finset β} (hS : S.Nonempty) : first σ S hS ∈ S :=
  ((first_eq_iff σ hS).1 rfl).1

/-- Relabelling by a permutation `τ` that preserves `S` relabels the first element. -/
theorem first_trans (σ : Enumeration β) {S : Finset β} (hS : S.Nonempty) (τ : Equiv.Perm β)
    (hτ : ∀ b, τ b ∈ S ↔ b ∈ S) : first (σ.trans τ) S hS = τ (first σ S hS) := by
  obtain ⟨h₁, h₂⟩ := (first_eq_iff σ hS).1 rfl
  refine (first_eq_iff _ hS).2 ⟨(hτ _).2 h₁, fun i hi => ?_⟩
  simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply] at hi ⊢
  exact h₂ i ((hτ _).1 hi)

/-- If the first element of `T` lies in the subset `S`, it is also the first element of `S`. -/
theorem first_of_subset (σ : Enumeration β) {S T : Finset β} (hS : S.Nonempty) (hT : T.Nonempty)
    (hST : S ⊆ T) (h : first σ T hT ∈ S) : first σ S hS = first σ T hT :=
  (first_eq_iff σ hS).2 ⟨h, fun i hi => ((first_eq_iff σ hT).1 rfl).2 i (hST hi)⟩

/-- All elements of `S` are equally likely to come first: each is first in the same number of
enumerations. -/
private theorem card_first_eq (S : Finset β) (hS : S.Nonempty) {a b : β} (ha : a ∈ S)
    (hb : b ∈ S) :
    #(univ.filter fun σ : Enumeration β => first σ S hS = b) =
      #(univ.filter fun σ : Enumeration β => first σ S hS = a) := by
  have hτ : ∀ y, Equiv.swap b a y ∈ S ↔ y ∈ S := fun y => by
    rw [Equiv.swap_apply_def]
    split_ifs with h₁ h₂ <;> simp_all
  refine card_equiv (Equiv.equivCongr (Equiv.refl _) (Equiv.swap b a)) fun σ => ?_
  change σ ∈ _ ↔ σ.trans (Equiv.swap b a) ∈ _
  simp only [mem_filter, mem_univ, true_and, first_trans σ hS _ hτ]
  rw [← (Equiv.swap b a).eq_symm_apply]
  simp

/-- **The first element is uniform.** Under a uniformly random enumeration, the first element of
`S` lies in `R` with probability `#(S ∩ R) / #S`. -/
theorem toOuterMeasure_first_mem (S : Finset β) (hS : S.Nonempty) (R : Set β)
    [DecidablePred (· ∈ R)] :
    ((PMF.uniformOfFintype (Enumeration β)).toOuterMeasure {σ | first σ S hS ∈ R}).toReal =
      #(S.filter (· ∈ R)) / #S := by
  classical
  obtain ⟨a, ha⟩ := id hS
  set F := #(univ.filter fun σ : Enumeration β => first σ S hS = a) with hF
  have hfib : ∀ t ⊆ S, #(univ.filter fun σ : Enumeration β => first σ S hS ∈ t) = #t * F := by
    intro t ht
    rw [card_eq_sum_card_fiberwise (s := univ.filter fun σ => first σ S hS ∈ t)
      (f := fun σ => first σ S hS) (t := t) (fun σ hσ => (mem_filter.1 hσ).2),
      sum_congr rfl fun b hb => ?_, sum_const, smul_eq_mul]
    rw [filter_filter, hF, ← card_first_eq S hS ha (ht hb)]
    exact congrArg card (filter_congr fun σ _ => ⟨And.right, fun h => ⟨h ▸ hb, h⟩⟩)
  have hall := hfib S Subset.rfl
  rw [filter_true_of_mem fun σ _ => first_mem σ hS, card_univ] at hall
  have hfilter : (univ.filter fun σ : Enumeration β => σ ∈ {σ | first σ S hS ∈ R}) =
      univ.filter fun σ => first σ S hS ∈ S.filter (· ∈ R) :=
    Finset.ext fun σ => by simp [first_mem]
  rw [PMF.toOuterMeasure_uniformOfFintype_toReal, hall, hfilter,
    hfib (S.filter (· ∈ R)) (filter_subset _ _)]
  have hF : (F : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.pos_of_mul_pos_left (hall ▸ Fintype.card_pos : 0 < #S * F)).ne'
  push_cast
  field_simp

end First

section Grid

variable {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ}

/-- A **grid distribution** on `α` with denominator `L`: the point `x` has probability
`count x / L`. -/
structure GridDist (α : Type*) [Fintype α] (L : ℕ) where
  /-- The number of cells of each point. -/
  count : α → ℕ
  sum_count : ∑ x, count x = L

namespace GridDist

variable [NeZero L]

/-- The distribution of a grid distribution. -/
noncomputable def toPMF (P : GridDist α L) : PMF α :=
  PMF.ofFintype (fun x => P.count x / L) <| by
    simp only [div_eq_mul_inv, ← sum_mul]
    rw [← Nat.cast_sum, P.sum_count]
    exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 (NeZero.ne L)) (ENNReal.natCast_ne_top L)

omit [DecidableEq α] in
theorem toPMF_apply (P : GridDist α L) (x : α) : P.toPMF x = P.count x / L := by
  rw [toPMF, PMF.ofFintype_apply]

omit [DecidableEq α] in
theorem toPMF_apply_toReal (P : GridDist α L) (x : α) :
    (P.toPMF x).toReal = P.count x / L := by
  simp [toPMF_apply, ENNReal.toReal_div]

omit [DecidableEq α] [NeZero L] in
theorem count_le (P : GridDist α L) (x : α) : P.count x ≤ L :=
  (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ x)).trans_eq P.sum_count

end GridDist

/-- The cells `{(x, u) : u < k x}` of the counts `k`. -/
private def cells (k : α → ℕ) : Finset (α × Fin L) := univ.filter fun p => p.2.val < k p.1

/-- The cells of `x` number `min L (k x)`. -/
private theorem card_cells_filter_fst (k : α → ℕ) (x : α) :
    #((cells (L := L) k).filter fun p => p.1 = x) = min L (k x) := by
  rw [← Fin.card_filter_val_lt]
  refine card_nbij' (fun p => p.2) (fun u => (x, u)) (fun p hp => ?_) (fun u hu => ?_)
    (fun p hp => ?_) (fun u _ => rfl)
  · simp only [cells, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    exact hp.2 ▸ hp.1
  · simp_all [cells]
  · simp only [cells, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp
    exact Prod.ext hp.2.symm rfl

omit [DecidableEq α] in
private theorem card_cells (k : α → ℕ) (hk : ∀ x, k x ≤ L) : #(cells (L := L) k) = ∑ x, k x := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun x _ => ?_
  convert (card_cells_filter_fst k x).trans (min_eq_right (hk x))

omit [DecidableEq α] in
private theorem cells_nonempty [NeZero L] (P : GridDist α L) :
    (cells (L := L) P.count).Nonempty := by
  rw [← card_pos, card_cells _ P.count_le, P.sum_count]
  exact Nat.pos_of_ne_zero (NeZero.ne L)

variable [NeZero L]

/-- **The party's output** for the grid distribution `P` from the shared enumeration `σ`: the point
of the first cell of `P` in `σ`. -/
def gridSample (P : GridDist α L) (σ : Enumeration (α × Fin L)) : α :=
  (first σ (cells P.count) (cells_nonempty P)).1

/-- **Each party samples its own distribution.** -/
theorem map_gridSample (P : GridDist α L) :
    (PMF.uniformOfFintype (Enumeration (α × Fin L))).map (gridSample P) = P.toPMF := by
  classical
  refine PMF.ext fun x => ?_
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    ← ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top _ _),
    ← ENNReal.ofReal_toReal (PMF.apply_ne_top _ x)]
  congr 1
  have hpre : gridSample P ⁻¹' {x} = {σ | first σ _ (cells_nonempty P) ∈ {p | p.1 = x}} := rfl
  rw [hpre, toOuterMeasure_first_mem _ (cells_nonempty P) {p | p.1 = x}]
  simp only [Set.mem_ofPred_eq]
  rw [card_cells_filter_fst, min_eq_right (P.count_le x), card_cells _ P.count_le,
    P.sum_count, GridDist.toPMF_apply_toReal]

/-- **The parties disagree with probability at most `2 d_TV(P, Q)`.** -/
theorem gridSample_disagree_le (P Q : GridDist α L) :
    ((PMF.uniformOfFintype (Enumeration (α × Fin L))).toOuterMeasure
      {σ | gridSample P σ ≠ gridSample Q σ}).toReal ≤ 2 * dist P.toPMF Q.toPMF := by
  classical
  set A := cells (L := L) P.count
  set B := cells (L := L) Q.count
  have hU : (A ∪ B).Nonempty := (cells_nonempty P).mono subset_union_left
  have hsub : {σ | gridSample P σ ≠ gridSample Q σ} ⊆
      {σ | first σ (A ∪ B) hU ∈ {p | p ∉ A ∩ B}} := by
    intro σ hσ hmem
    rw [mem_inter] at hmem
    exact hσ (congrArg Prod.fst ((first_of_subset σ _ hU subset_union_left hmem.1).trans
      (first_of_subset σ _ hU subset_union_right hmem.2).symm))
  refine (ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
    (MeasureTheory.measure_mono hsub)).trans ?_
  rw [toOuterMeasure_first_mem]
  simp only [Set.mem_ofPred_eq]
  have hAB : A ∩ B = cells (L := L) fun x => min (P.count x) (Q.count x) :=
    Finset.ext fun p => by simp [A, B, cells]
  have hI : (#(A ∩ B) : ℝ) = L * (1 - dist P.toPMF Q.toPMF) := by
    rw [hAB, card_cells _ fun x => (min_le_left _ _).trans (P.count_le x),
      ← PMF.sum_min_toReal, mul_sum]
    push_cast
    refine sum_congr rfl fun x _ => ?_
    rw [GridDist.toPMF_apply_toReal, GridDist.toPMF_apply_toReal, min_div_div_right
      (Nat.cast_nonneg L)]
    have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
    field_simp
  have hcard : (#((A ∪ B).filter fun p => p ∉ A ∩ B) : ℝ) = #(A ∪ B) - #(A ∩ B) := by
    rw [filter_not, filter_mem_eq_inter, inter_eq_right.2 inter_subset_union,
      card_sdiff_of_subset inter_subset_union, Nat.cast_sub (card_le_card inter_subset_union)]
  have hunion : (#(A ∪ B) + #(A ∩ B) : ℝ) = 2 * L := by
    exact_mod_cast (card_union_add_card_inter A B).trans
      (by rw [card_cells _ P.count_le, P.sum_count, card_cells _ Q.count_le, Q.sum_count, two_mul])
  have hL : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hd := dist_nonneg (x := P.toPMF) (y := Q.toPMF)
  have hd1 := Cslib.Probability.PMF.dist_le_one P.toPMF Q.toPMF
  rw [hcard, eq_sub_of_add_eq hunion, hI, div_le_iff₀ (by nlinarith)]
  nlinarith

end Grid

end Cslib.Probability.CorrelatedSampling
