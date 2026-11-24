/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Final
public import CslibFrontier.Probability.PlantedClique.CommonNeighborSize
import CslibFrontier.Probability.PMF.EventBind
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Recovery after exposing a planted seed

The common-neighbor exposure law transfers the base algorithm's recovery bound to the graph
induced on a fixed planted seed's common neighborhood. Averaging the exact exposure coupling
and excluding the Hoeffding size tail gives a finite failure bound with no independence premise.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Cslib.Probability.PlantedClique Cslib.Probability.PMF

/-- For any fixed exposure and increasing enumeration away from the seed, the base recovery
algorithm has exactly its usual planted-graph failure bound. -/
theorem prob_recover_resampleOffSeed_ne_le {n m : ℕ} (S T : Finset (Fin n)) (ω : Coins n)
    (e : Fin m ↪o Fin n) (he : ∀ i, e i ∉ T) :
    let R := Finset.univ.filter fun i => e i ∈ S
    1 ≤ m → 6 ≤ R.card → 1024 * Real.sqrt m ≤ (R.card : ℝ) →
    ((uniformOfFintype (Coins n)).toOuterMeasure {η |
      recover ((sample S (resampleOffSeed T ω η)).comap e) R.card ≠ R}).toReal ≤
      2 * Real.exp (-(m : ℝ)) + m * Real.exp (-(R.card : ℝ) / 32) := by
  classical
  intro R hm hR hsize
  have hlaw := congrArg (fun q : PMF (SimpleGraph (Fin m)) =>
    (q.toOuterMeasure {G | recover G R.card ≠ R}).toReal)
    (uniform_sample_resampleOffSeed_comap S T ω e he)
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq, recover_eq_classical] at hlaw
  have hb := prob_recover_ne_le R hm hR hsize
  simp only [recover_eq_classical] at hb ⊢
  exact hlaw.trans_le hb

/-- The common-neighbor reduction at a fixed planted seed succeeds with high probability once
its reduced clique clears the base algorithm's size threshold. The numerical premise uses only
the original graph and seed sizes, not the realized neighborhood or an assumed conditional law. -/
theorem prob_recover_commonNeighborhood_ne_le {n : ℕ} (S T : Finset (Fin n))
    (hT : T ⊆ S) (hn : 1 ≤ n) (hk : 6 ≤ S.card - T.card)
    (hsize : 1024 * Real.sqrt ((S.card : ℝ) + 2 * n * (2 ^ T.card : ℝ)⁻¹) ≤
      (S.card - T.card : ℕ)) :
    ((uniformOfFintype (Coins n)).toOuterMeasure {ω |
      let U := (sample S ω).commonNeighborhood T
      let e := U.orderEmbOfFin rfl
      recover ((sample S ω).comap e) (S.card - T.card) ≠
        (Finset.univ.filter fun i => e i ∈ S)}).toReal ≤
      Real.exp (-2 * n * ((2 ^ T.card : ℝ)⁻¹) ^ 2) +
        (2 * Real.exp (-((S.card - T.card : ℕ) : ℝ)) +
          n * Real.exp (-((S.card - T.card : ℕ) : ℝ) / 32)) := by
  classical
  let coins := uniformOfFintype (Coins n)
  let failure : Set (Coins n) := {ω |
    let U := (sample S ω).commonNeighborhood T
    let e := U.orderEmbOfFin rfl
    recover ((sample S ω).comap e) (S.card - T.card) ≠
      (Finset.univ.filter fun i => e i ∈ S)}
  let pre : Set (Coins n) := {ω |
    (((sample S ω).commonNeighborhood T).card : ℝ) <
      (S.card : ℝ) + 2 * n * (2 ^ T.card : ℝ)⁻¹}
  let error : ℝ := 2 * Real.exp (-((S.card - T.card : ℕ) : ℝ)) +
    n * Real.exp (-((S.card - T.card : ℕ) : ℝ) / 32)
  have herror : 0 ≤ error := by dsimp only [error]; positivity
  have hlaw : (coins.bind fun ω => coins.map (resampleOffSeed T ω)) = coins := by
    dsimp only [coins]
    simp only [← PMF.bind_pure_comp]
    simpa only [PMF.bind_pure, Function.comp_def] using
      uniform_bind_bind_resampleOffSeed T (PMF.pure : Coins n → PMF (Coins n))
  have hstep : ∀ ω ∈ coins.support, ω ∈ pre →
      ((coins.map (resampleOffSeed T ω)).toOuterMeasure failure).toReal ≤ error := by
    intro ω _ hpre
    let U := (sample S ω).commonNeighborhood T
    let e := U.orderEmbOfFin rfl
    let R := Finset.univ.filter fun i => e i ∈ S
    have hR : R.card = S.card - T.card :=
      card_filter_commonNeighborhood S T hT ω e.toEmbedding
        (U.image_orderEmbOfFin_univ rfl)
    have hkm : S.card - T.card ≤ U.card := by
      rw [← hR]
      exact (Finset.card_le_univ R).trans_eq (Fintype.card_fin U.card)
    have hm : 1 ≤ U.card := by omega
    have hmn : U.card ≤ n := (Finset.card_le_univ U).trans_eq (Fintype.card_fin n)
    have hsizeU : 1024 * Real.sqrt U.card ≤ (R.card : ℝ) := by
      rw [hR]
      exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_of_lt hpre))
        (by norm_num : (0 : ℝ) ≤ 1024)).trans hsize
    have he : ∀ i, e i ∉ T := fun i =>
      (sample S ω).not_mem_of_mem_commonNeighborhood (U.orderEmbOfFin_mem rfl i)
    have hb := prob_recover_resampleOffSeed_ne_le S T ω e he hm
      (show 6 ≤ R.card by rw [hR]; exact hk) hsizeU
    have hevent : (resampleOffSeed T ω) ⁻¹' failure =
        {η | recover ((sample S (resampleOffSeed T ω η)).comap e) R.card ≠ R} := by
      ext η
      have hprop := congrArg (fun V : Finset (Fin n) =>
        @recover V.card ((sample S (resampleOffSeed T ω η)).comap (V.orderEmbOfFin rfl))
          (Classical.decRel _) (S.card - T.card) ≠
            Finset.univ.filter fun i => V.orderEmbOfFin rfl i ∈ S)
        (commonNeighborhood_resampleOffSeed S T ω η)
      simpa only [Set.mem_preimage, failure, Set.mem_ofPred_eq,
        recover_eq_classical, hR, R, e, U] using Iff.of_eq hprop
    rw [PMF.toOuterMeasure_map_apply, hevent]
    refine hb.trans ?_
    dsimp only [error]
    rw [hR]
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      exact Real.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast hkm))
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) (Real.exp_pos _).le
  have hb := toOuterMeasure_bind_failure_toReal_le coins
    (fun ω => coins.map (resampleOffSeed T ω)) pre failure herror hstep
  rw [hlaw] at hb
  refine hb.trans (add_le_add ?_ le_rfl)
  convert prob_commonNeighborhood_card_ge_twice S T hT hn using 1
  congr 2
  ext ω
  simp [pre]

end Cslib.Algorithms.PlantedClique
