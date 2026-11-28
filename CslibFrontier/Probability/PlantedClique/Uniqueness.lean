/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PlantedClique.Degree
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CliqueUniqueness
public import CslibFrontier.Probability.PMF.UniformPattern
public import Mathlib.Data.Finset.Density
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.NNRat.BigOperators

/-!
# Uniqueness of the planted clique

A prescribed set disjoint from the planted set is a clique with probability exactly
`2 ^ (-choose |T| 2)`. A union bound excludes large cliques outside the planted set.
Together with the outside-degree bound, this proves that every clique of size `|S|` is
the planted set, except on the explicitly bounded exceptional event.

This is the uniqueness condition needed by a seed-enumeration algorithm which accepts the
first verified clique. The argument concerns the actual planted experiment and does not
assume independence for adaptively chosen candidate sets.
-/

public section

namespace Cslib.Probability.PlantedClique

open Finset Real

/-- The probability that a fixed set disjoint from the planted set is a clique. -/
theorem prob_isClique_of_disjoint {n : ℕ} (S T : Finset (Fin n))
    (hST : Disjoint S T) :
    ((Cslib.Probability.PMF.uniformOfFintype (Coins n)).toOuterMeasure
      {ω : Coins n | (sample S ω).IsClique (T : Set (Fin n))}).toReal =
      ((2 : ℝ) ^ T.card.choose 2)⁻¹ := by
  classical
  let E := (T ×ˢ T).filter (fun p => p.1 < p.2)
  have hevent : {ω : Coins n | (sample S ω).IsClique (T : Set (Fin n))} =
      {ω : Coins n | ∀ p ∈ E, ω p = true} := by
    ext ω
    constructor
    · intro h p hp
      obtain ⟨hp, hlt⟩ := mem_filter.mp hp
      obtain ⟨hi, hj⟩ := mem_product.mp hp
      have hiS : p.1 ∉ S := fun hiS => Finset.disjoint_left.mp hST hiS hi
      have hadj := h hi hj (ne_of_lt hlt)
      change _ ≠ _ ∧ ((_ ∈ S ∧ _ ∈ S) ∨ _) at hadj
      simpa only [hiS, false_and, false_or, min_eq_left hlt.le, max_eq_right hlt.le]
        using hadj.2
    · intro h i hi j hj hij
      refine ⟨hij, Or.inr ?_⟩
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · simpa only [min_eq_left hlt.le, max_eq_right hlt.le] using
          h (i, j) (mem_filter.mpr ⟨mem_product.mpr ⟨hi, hj⟩, hlt⟩)
      · simpa only [min_eq_right hlt.le, max_eq_left hlt.le] using
          h (j, i) (mem_filter.mpr ⟨mem_product.mpr ⟨hj, hi⟩, hlt⟩)
  rw [hevent, Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_pi_eqOn E
    (fun _ => true)]
  simp [E, card_product_filter_lt]

/-- Density form of the fixed outside-clique probability. -/
theorem dens_isClique_of_disjoint {n : ℕ} (S T : Finset (Fin n))
    (hST : Disjoint S T) :
    (dens ({ω : Coins n | (sample S ω).IsClique (T : Set (Fin n))} : Finset _) : ℝ) =
      ((2 : ℝ) ^ T.card.choose 2)⁻¹ := by
  have h := prob_isClique_of_disjoint S T hST
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal] at h
  simpa only [Set.mem_ofPred_eq, dens_eq_card_div_card, NNRat.cast_div,
    NNRat.cast_natCast] using h

/-- A union bound over all size-`r` subsets excludes a clique outside the planted set. -/
theorem dens_exists_outside_clique_le {n : ℕ} (S : Finset (Fin n)) (r : ℕ) :
    (dens ({ω : Coins n | ∃ T : Finset (Fin n), Disjoint S T ∧ T.card = r ∧
      (sample S ω).IsClique (T : Set (Fin n))} : Finset _) : ℝ) ≤
      n.choose r * ((2 : ℝ) ^ r.choose 2)⁻¹ := by
  classical
  let D : Finset (Fin n) → Finset (Coins n) := fun T =>
    {ω | Disjoint S T ∧ (sample S ω).IsClique (T : Set (Fin n))}
  let W : Finset (Finset (Fin n)) := univ.powersetCard r
  have hD (T : Finset (Fin n)) (hT : T ∈ W) :
      (dens (D T) : ℝ) ≤ ((2 : ℝ) ^ r.choose 2)⁻¹ := by
    have hcard : T.card = r := (mem_powersetCard.mp hT).2
    by_cases hd : Disjoint S T
    · simp only [D, hd, true_and]
      exact (dens_isClique_of_disjoint S T hd).trans_le (by rw [hcard])
    · simp only [D, hd, false_and, filter_false, dens_empty, NNRat.cast_zero]
      positivity
  have hevent : ({ω : Coins n | ∃ T : Finset (Fin n), Disjoint S T ∧ T.card = r ∧
      (sample S ω).IsClique (T : Set (Fin n))} : Finset _) = W.biUnion D := by
    ext ω
    simp [W, D, and_left_comm]
  rw [hevent]
  have h : (dens (W.biUnion D) : ℝ) ≤ ∑ T ∈ W, (dens (D T) : ℝ) := by
    simpa only [NNRat.cast_sum] using
      (NNRat.cast_le (K := ℝ)).2 (dens_biUnion_le (s := W) (t := D))
  calc
    _ ≤ ∑ T ∈ W, ((2 : ℝ) ^ r.choose 2)⁻¹ :=
      h.trans (sum_le_sum fun T hT => hD T hT)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, W, card_powersetCard,
      card_univ, Fintype.card_fin]

/-- Except on the stated event, the planted set is the only clique of its cardinality.
The parameter `r` can be any natural number at most `3 |S| / 8`; for example, `|S| / 4`. -/
theorem dens_exists_clique_ne_le {n : ℕ} (S : Finset (Fin n)) (r : ℕ)
    (hS : 0 < S.card) (hr : 8 * r ≤ 3 * S.card) :
    (dens ({ω : Coins n | ∃ Q : Finset (Fin n),
      (sample S ω).IsClique (Q : Set (Fin n)) ∧ Q.card = S.card ∧ Q ≠ S} : Finset _) : ℝ) ≤
      n * exp (-(S.card : ℝ) / 32) + n.choose r * ((2 : ℝ) ^ r.choose 2)⁻¹ := by
  classical
  let D : Finset (Coins n) := {ω | ∃ v, v ∉ S ∧
    5 * S.card < 8 * (S.filter ((sample S ω).Adj v)).card}
  let O : Finset (Coins n) := {ω | ∃ T : Finset (Fin n), Disjoint S T ∧ T.card = r ∧
    (sample S ω).IsClique (T : Set (Fin n))}
  have hsub : ({ω : Coins n | ∃ Q : Finset (Fin n),
      (sample S ω).IsClique (Q : Set (Fin n)) ∧ Q.card = S.card ∧ Q ≠ S} : Finset _) ⊆ D ∪ O := by
    intro ω hω
    obtain ⟨Q, hQ, hcard, hne⟩ := (mem_filter.mp hω).2
    by_contra hnot
    simp only [mem_union, D, O, mem_filter, mem_univ, true_and, not_or, not_exists, not_and,
      not_lt] at hnot
    exact hne ((sample S ω).clique_eq_of_outside_degree_le_of_no_outside_clique
      hnot.1 hr hnot.2 hQ hcard)
  calc
    _ ≤ (dens (D ∪ O) : ℝ) := by exact_mod_cast dens_le_dens hsub
    _ ≤ (dens D : ℝ) + (dens O : ℝ) := by exact_mod_cast dens_union_le D O
    _ ≤ _ := add_le_add (dens_exists_outside_degree_gt_le S hS)
      (dens_exists_outside_clique_le S r)

/-- Probability-mass-function form of the uniqueness bound. -/
theorem prob_exists_clique_ne_le {n : ℕ} (S : Finset (Fin n)) (r : ℕ)
    (hS : 0 < S.card) (hr : 8 * r ≤ 3 * S.card) :
    ((Cslib.Probability.PMF.uniformOfFintype (Coins n)).toOuterMeasure
      {ω : Coins n | ∃ Q : Finset (Fin n), (sample S ω).IsClique (Q : Set (Fin n)) ∧
        Q.card = S.card ∧ Q ≠ S}).toReal ≤
      n * exp (-(S.card : ℝ) / 32) + n.choose r * ((2 : ℝ) ^ r.choose 2)⁻¹ := by
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal]
  simpa only [Set.mem_ofPred_eq, dens_eq_card_div_card, NNRat.cast_div,
    NNRat.cast_natCast] using dens_exists_clique_ne_le S r hS hr

end Cslib.Probability.PlantedClique
