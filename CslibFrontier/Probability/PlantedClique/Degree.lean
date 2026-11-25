/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PlantedClique.Model
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Probability.BitString.Rademacher.Tail
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Degrees into a planted clique

Each vertex outside a fixed planted set has independent fair edges into that set. A weighted
Rademacher bound and a union bound show that all such degrees are at most `5 |S| / 8`, except
on a set of uniform seeds of density at most `n exp (-|S| / 32)`. Only degrees into the fixed
planted set are treated as independent; no independence is asserted for a set chosen by an
algorithm from the graph.

## Main results

* `Cslib.Probability.PlantedClique.dens_exists_outside_degree_gt_le`: the simultaneous bound.
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.Probability.PlantedClique

private theorem edgeIndex_injective {n : ℕ} (v : Fin n) :
    Function.Injective (fun w : Fin n => (min v w, max v w)) := by
  intro a b hab
  have hmin := congrArg Prod.fst hab
  have hmax := congrArg Prod.snd hab
  by_cases ha : v ≤ a <;> by_cases hb : v ≤ b
  · simpa only [min_eq_left ha, min_eq_left hb, max_eq_right ha, max_eq_right hb] using hmax
  · have hb' := le_of_not_ge hb
    have h1 : v = b := by simpa only [min_eq_left ha, min_eq_right hb'] using hmin
    have h2 : a = v := by simpa only [max_eq_right ha, max_eq_left hb'] using hmax
    exact h2.trans h1
  · have ha' := le_of_not_ge ha
    have h1 : a = v := by simpa only [min_eq_right ha', min_eq_left hb] using hmin
    have h2 : v = b := by simpa only [max_eq_left ha', max_eq_right hb] using hmax
    exact h1.trans h2
  · simpa only [min_eq_right (le_of_not_ge ha), min_eq_right (le_of_not_ge hb)] using hmin

private def edgeIndices {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n × Fin n) :=
  S.image fun w => (min v w, max v w)

private def degreeCoeff {n : ℕ} (S : Finset (Fin n)) (v : Fin n) (p : Fin n × Fin n) : ℝ :=
  if p ∈ edgeIndices S v then -1 else 0

private theorem sum_degreeCoeff_sq {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    ∑ p, degreeCoeff S v p ^ 2 = (S.card : ℝ) := by
  calc
    ∑ p, degreeCoeff S v p ^ 2 =
        ∑ p : Fin n × Fin n, if p ∈ edgeIndices S v then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro p hp
      simp only [degreeCoeff]
      split_ifs <;> norm_num
    _ = ((edgeIndices S v).card : ℝ) := by simp
    _ = (S.card : ℝ) := by rw [edgeIndices, card_image_of_injective _ (edgeIndex_injective v)]

private theorem sum_degreeCoeff_signVal {n : ℕ} (S : Finset (Fin n)) (v : Fin n)
    (hv : v ∉ S) (ω : Coins n) :
    ∑ p, degreeCoeff S v p * BitString.signVal (ω p) =
      2 * ((S.filter ((sample S ω).Adj v)).card : ℝ) - (S.card : ℝ) := by
  have hadj (w : Fin n) (hw : w ∈ S) :
      (sample S ω).Adj v w ↔ ω (min v w, max v w) = true := by
    change (v ≠ w ∧ ((v ∈ S ∧ w ∈ S) ∨ ω (min v w, max v w) = true)) ↔ _
    have hvw : v ≠ w := fun h => hv (h.symm ▸ hw)
    exact ⟨fun h => h.2.resolve_left (fun h => hv h.1), fun h => ⟨hvw, Or.inr h⟩⟩
  have hbits : (∑ w ∈ S, BitString.bitVal ℝ (ω (min v w, max v w))) =
      ((S.filter ((sample S ω).Adj v)).card : ℝ) := by
    calc
      _ = ∑ w ∈ S, if (sample S ω).Adj v w then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro w hw
        simp only [BitString.bitVal, hadj w hw]
      _ = _ := sum_boole _ _
  calc
    ∑ p, degreeCoeff S v p * BitString.signVal (ω p) =
        ∑ p ∈ edgeIndices S v, -BitString.signVal (ω p) := by
      simp only [degreeCoeff, ite_mul, neg_one_mul, zero_mul, ← sum_filter,
        filter_mem_eq_inter, univ_inter]
    _ = ∑ w ∈ S, -BitString.signVal (ω (min v w, max v w)) := by
      rw [edgeIndices, sum_image]
      intro a ha b hb hab
      exact edgeIndex_injective v hab
    _ = 2 * ((S.filter ((sample S ω).Adj v)).card : ℝ) - (S.card : ℝ) := by
      simp_rw [BitString.signVal_eq_one_sub_two_mul_bitVal, neg_sub]
      rw [sum_sub_distrib, ← mul_sum, hbits]
      simp only [sum_const, nsmul_eq_mul, mul_one]

private theorem dens_outside_degree_gt_le {n : ℕ} (S : Finset (Fin n))
    (hS : 0 < S.card) (v : Fin n) (hv : v ∉ S) :
    (dens ({ω : Coins n | 5 * S.card < 8 * (S.filter ((sample S ω).Adj v)).card} :
      Finset _) : ℝ) ≤ exp (-(S.card : ℝ) / 32) := by
  classical
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast hS
  have hsub : ({ω : Coins n | 5 * S.card < 8 * (S.filter ((sample S ω).Adj v)).card} :
      Finset _) ⊆ ({ω : Coins n | (S.card : ℝ) / 4 ≤
        ∑ p, degreeCoeff S v p * BitString.signVal (ω p)} : Finset _) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    rw [sum_degreeCoeff_signVal S v hv]
    have hω' : 5 * (S.card : ℝ) < 8 * (S.filter ((sample S ω).Adj v)).card := by
      exact_mod_cast hω
    linarith
  calc
    (dens ({ω : Coins n | 5 * S.card < 8 * (S.filter ((sample S ω).Adj v)).card} :
        Finset _) : ℝ) ≤
        dens ({ω : Coins n | (S.card : ℝ) / 4 ≤
          ∑ p, degreeCoeff S v p * BitString.signVal (ω p)} : Finset _) := by
      exact_mod_cast dens_le_dens hsub
    _ ≤ exp (-(((S.card : ℝ) / 4) ^ 2) / (2 * (S.card : ℝ))) :=
      BitString.dens_sum_mul_signVal_ge_le (degreeCoeff S v) hpos
        (sum_degreeCoeff_sq S v).le (by positivity)
    _ = exp (-(S.card : ℝ) / 32) := by
      congr 1
      field_simp
      ring

/-- All outside degrees into the planted set are at most five eighths of its size, except
with density at most `n exp (-|S| / 32)`. -/
theorem dens_exists_outside_degree_gt_le {n : ℕ} (S : Finset (Fin n)) (hS : 0 < S.card) :
    (dens ({ω : Coins n | ∃ v, v ∉ S ∧
      5 * S.card < 8 * (S.filter ((sample S ω).Adj v)).card} : Finset _) : ℝ) ≤
      n * exp (-(S.card : ℝ) / 32) := by
  classical
  let D : Fin n → Finset (Coins n) := fun v =>
    {ω | v ∉ S ∧ 5 * S.card < 8 * (S.filter ((sample S ω).Adj v)).card}
  have hD (v : Fin n) : (dens (D v) : ℝ) ≤ exp (-(S.card : ℝ) / 32) := by
    by_cases hv : v ∈ S
    · simp only [D, hv, not_true_eq_false, false_and, filter_false, dens_empty,
        NNRat.cast_zero]
      exact (exp_pos _).le
    · simpa only [D, hv, not_false_eq_true, true_and] using
        dens_outside_degree_gt_le S hS v hv
  have hset : ({ω : Coins n | ∃ v, v ∉ S ∧
      5 * S.card < 8 * (S.filter ((sample S ω).Adj v)).card} : Finset _) = univ.biUnion D := by
    ext ω
    simp only [D, mem_filter, mem_univ, true_and, mem_biUnion]
  rw [hset]
  have h : (dens (univ.biUnion D) : ℝ) ≤ ∑ v, (dens (D v) : ℝ) := by
    simpa only [NNRat.cast_sum] using
      (NNRat.cast_le (K := ℝ)).2 (dens_biUnion_le (s := univ) (t := D))
  calc
    _ ≤ ∑ v : Fin n, exp (-(S.card : ℝ) / 32) := h.trans (sum_le_sum fun v _ => hD v)
    _ = _ := by simp

end Cslib.Probability.PlantedClique
