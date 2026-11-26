/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PlantedClique.CommonNeighbors
public import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Event
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Concentration of a planted seed's common neighborhood

For a seed `T ⊆ S`, every vertex of `S \ T` survives. Each outside vertex survives exactly
when all of its `T.card` seed-edge coins are true. These blocks are disjoint across outside
vertices, so pulling back the uniform coin table gives a uniform product of independent rows.
The finite Hoeffding inequality then controls the number of surviving outside vertices.
-/

public section

namespace Cslib.Probability.PlantedClique

open Cslib.Probability.PMF
open scoped BigOperators

private theorem seedEdgeIndex_injective {n : ℕ} (S T : Finset (Fin n)) (hT : T ⊆ S) :
    Function.Injective (fun p : ↥Sᶜ × ↥T =>
      (min (p.2 : Fin n) (p.1 : Fin n), max (p.2 : Fin n) (p.1 : Fin n))) := by
  rintro ⟨v, t⟩ ⟨w, u⟩ h
  have hmin := congrArg Prod.fst h
  have hmax := congrArg Prod.snd h
  have hv : (v : Fin n) ∉ S := Finset.mem_compl.mp v.property
  have hw : (w : Fin n) ∉ S := Finset.mem_compl.mp w.property
  by_cases htv : (t : Fin n) ≤ v <;> by_cases huw : (u : Fin n) ≤ w
  · simp only [min_eq_left htv, min_eq_left huw] at hmin
    simp only [max_eq_right htv, max_eq_right huw] at hmax
    exact Prod.ext (Subtype.ext hmax) (Subtype.ext hmin)
  · simp only [min_eq_left htv, min_eq_right (le_of_not_ge huw)] at hmin
    exact False.elim (hw (hmin ▸ hT t.property))
  · simp only [min_eq_right (le_of_not_ge htv), min_eq_left huw] at hmin
    exact False.elim (hv (hmin.symm ▸ hT u.property))
  · simp only [min_eq_right (le_of_not_ge htv), min_eq_right (le_of_not_ge huw)] at hmin
    simp only [max_eq_left (le_of_not_ge htv), max_eq_left (le_of_not_ge huw)] at hmax
    exact Prod.ext (Subtype.ext hmin) (Subtype.ext hmax)

/-- The seed-edge rows for distinct outside vertices are independent uniform Boolean rows.
This proves the independence used in the common-neighborhood count from the sampler itself. -/
theorem uniform_seedEdgeRows {n : ℕ} (S T : Finset (Fin n)) (hT : T ⊆ S) :
    (PMF.uniformOfFintype (Coins n)).map
        (fun ω (v : ↥Sᶜ) (t : ↥T) => ω (min (t : Fin n) v, max (t : Fin n) v)) =
      PMF.uniformOfFintype (↥Sᶜ → ↥T → Bool) := by
  let e : ↥Sᶜ × ↥T ↪ Fin n × Fin n :=
    ⟨fun p => (min (p.2 : Fin n) p.1, max (p.2 : Fin n) p.1),
      seedEdgeIndex_injective S T hT⟩
  rw [← PMF.uniformOfFintype_map_equiv (Equiv.curry ↥Sᶜ ↥T Bool),
    ← uniformOfFintype_pi_map_comp_embedding (α := Bool) e, PMF.map_comp]
  rfl

/-- The common neighborhood consists of the surviving planted vertices and one independent
all-true-row indicator for every outside vertex. -/
theorem commonNeighborhood_card_eq {n : ℕ} (S T : Finset (Fin n)) (hT : T ⊆ S)
    (ω : Coins n) :
    ((sample S ω).commonNeighborhood T).card = S.card - T.card +
      ∑ v : ↥Sᶜ, if ∀ t : ↥T, ω (min (t : Fin n) v, max (t : Fin n) v) = true
        then 1 else 0 := by
  classical
  let U := (sample S ω).commonNeighborhood T
  have hclique : (sample S ω).IsClique (S : Set (Fin n)) :=
    fun _ hi _ hj hij => sample_adj_of_mem S ω hi hj hij
  have hinside : U ∩ S = S \ T := by
    rw [Finset.inter_comm]
    exact (sample S ω).inter_commonNeighborhood_eq_sdiff hT hclique
  have houtside : U \ S = Sᶜ.filter (fun v =>
      ∀ t : ↥T, ω (min (t : Fin n) v, max (t : Fin n) v) = true) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_compl,
      SimpleGraph.mem_commonNeighborhood, U]
    constructor
    · rintro ⟨⟨_, hseed⟩, hvS⟩
      exact ⟨hvS, fun t => (hseed t t.property).2.resolve_left fun h => hvS h.2⟩
    · rintro ⟨hvS, hrow⟩
      exact ⟨⟨fun hvT => hvS (hT hvT),
        fun t ht => ⟨fun h => hvS (h ▸ hT ht), Or.inr (hrow ⟨t, ht⟩)⟩⟩, hvS⟩
  rw [← Finset.card_inter_add_card_sdiff U S, hinside, Finset.card_sdiff_of_subset hT,
    houtside, Finset.card_filter, ← Finset.sum_coe_sort]

private theorem mean_allTrue {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∑ row : ι → Bool, ((PMF.uniformOfFintype (ι → Bool)) row).toReal *
      if ∀ i, row i = true then (1 : ℝ) else 0) = (2 ^ Fintype.card ι : ℝ)⁻¹ := by
  classical
  rw [Finset.sum_eq_single (fun _ => true)]
  · simp [PMF.uniformOfFintype_apply]
  · intro row _ hrow
    have h : ¬∀ i, row i = true := fun h => hrow (funext h)
    simp [h]
  · simp

/-- Hoeffding's upper tail for the seed's common-neighborhood size. The mean is
`|S| - |T| + (n - |S|) / 2^|T|`, and no distributional premise is supplied by the caller. -/
theorem prob_commonNeighborhood_card_ge_mean_add {n : ℕ} (S T : Finset (Fin n))
    (hT : T ⊆ S) {ε : ℝ} (hε : 0 ≤ ε) :
    ((PMF.uniformOfFintype (Coins n)).toOuterMeasure {ω |
      (S.card - T.card : ℕ) + ((n - S.card : ℕ) : ℝ) * (2 ^ T.card : ℝ)⁻¹ + ε ≤
        (((sample S ω).commonNeighborhood T).card : ℝ)}).toReal ≤
      Real.exp (-2 * ε ^ 2 / (n - S.card : ℕ)) := by
  classical
  let score : (↥T → Bool) → ℝ := fun row => if ∀ t, row t = true then 1 else 0
  have hb : ∀ (v : ↥Sᶜ) (row : ↥T → Bool),
      row ∈ (PMF.uniformOfFintype (↥T → Bool)).support → score row ∈ Set.Icc 0 1 := by
    intro v row _
    dsimp only [score]
    split_ifs <;> norm_num
  have h := pi_sum_ge_mean_add (fun _ : ↥Sᶜ => PMF.uniformOfFintype (↥T → Bool))
    (fun _ row => score row) zero_le_one hb hε
  have hm : (∑ _v : ↥Sᶜ, ∑ row : ↥T → Bool,
      ((PMF.uniformOfFintype (↥T → Bool)) row).toReal * score row) =
      ((n - S.card : ℕ) : ℝ) * (2 ^ T.card : ℝ)⁻¹ := by
    simp only [score, mean_allTrue, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  rw [hm, pi_uniformOfFintype, ← uniform_seedEdgeRows S T hT,
    PMF.toOuterMeasure_map_apply] at h
  simp only [one_pow, mul_one, Fintype.card_coe, Finset.card_compl, Fintype.card_fin] at h
  convert h using 1
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  have hc := congrArg (fun k : ℕ => (k : ℝ)) (commonNeighborhood_card_eq S T hT ω)
  push_cast at hc
  dsimp only [score]
  constructor <;> intro hω <;> linarith

/-- A convenient uniform upper-tail bound for the common-neighbor reduction: except with
probability `exp (-2 n / 4^|T|)`, the neighborhood has fewer than `|S| + 2 n / 2^|T|` vertices.
The exponent is independent of the size of the planted set. -/
theorem prob_commonNeighborhood_card_ge_twice {n : ℕ} (S T : Finset (Fin n))
    (hT : T ⊆ S) (hn : 1 ≤ n) :
    ((PMF.uniformOfFintype (Coins n)).toOuterMeasure {ω |
      (S.card : ℝ) + 2 * n * (2 ^ T.card : ℝ)⁻¹ ≤
        (((sample S ω).commonNeighborhood T).card : ℝ)}).toReal ≤
      Real.exp (-2 * n * ((2 ^ T.card : ℝ)⁻¹) ^ 2) := by
  classical
  let p : ℝ := (2 ^ T.card : ℝ)⁻¹
  have hp : 0 < p := by dsimp only [p]; positivity
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : S.card ≤ n := (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)
  by_cases hd : n - S.card = 0
  · have hkn : S.card = n := by omega
    have hevent : {ω : Coins n | (S.card : ℝ) + 2 * n * p ≤
        (((sample S ω).commonNeighborhood T).card : ℝ)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hcard : (((sample S ω).commonNeighborhood T).card : ℝ) ≤ n := by
        exact_mod_cast (Finset.card_le_univ ((sample S ω).commonNeighborhood T)).trans_eq
          (Fintype.card_fin n)
      simp only [Set.mem_ofPred_eq, hkn] at hω
      nlinarith [mul_pos hnn hp]
    change ((PMF.uniformOfFintype (Coins n)).toOuterMeasure {ω |
      (S.card : ℝ) + 2 * n * p ≤ (((sample S ω).commonNeighborhood T).card : ℝ)}).toReal ≤ _
    rw [hevent]
    simp only [MeasureTheory.measure_empty, ENNReal.toReal_zero]
    exact (Real.exp_pos _).le
  · have hdpos : (0 : ℝ) < (n - S.card : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hdle : ((n - S.card : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n S.card
    have hsle : ((S.card - T.card : ℕ) : ℝ) ≤ S.card := by
      exact_mod_cast Nat.sub_le S.card T.card
    have hb := prob_commonNeighborhood_card_ge_mean_add S T hT
      (show 0 ≤ (n : ℝ) * p from mul_nonneg hnn.le hp.le)
    have hsub : {ω : Coins n | (S.card : ℝ) + 2 * n * p ≤
        (((sample S ω).commonNeighborhood T).card : ℝ)} ⊆
        {ω : Coins n | (S.card - T.card : ℕ) + ((n - S.card : ℕ) : ℝ) * p + n * p ≤
          (((sample S ω).commonNeighborhood T).card : ℝ)} := by
      intro ω hω
      dsimp only [Set.mem_ofPred_eq] at hω ⊢
      nlinarith [mul_le_mul_of_nonneg_right hdle hp.le]
    refine le_trans (ENNReal.toReal_mono (toOuterMeasure_ne_top _ _)
      ((PMF.uniformOfFintype (Coins n)).toOuterMeasure.mono hsub)) (hb.trans ?_)
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hdpos).mpr
    have hm := mul_le_mul_of_nonpos_left hdle
      (show -2 * (n : ℝ) * p ^ 2 ≤ 0 by
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg p))
    nlinarith

end Cslib.Probability.PlantedClique
