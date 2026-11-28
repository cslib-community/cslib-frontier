/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Matching

/-!
# Checked tests for the matched-edge pair-insertion layout

Verifies:
1. Concrete `pairKey` threshold cuts and strict `1 < 2` saving over naive median-of-3 edge scores.
2. Concrete `K₄` cubic graph with perfect matching `M = {e₀₁, e₂₃}` comparing the two threshold
   cost bounds at `t = 0`: `matchingCost = 2 < 4 = #{EdgeStraddles}` (strictly half the naive
   straddling count bound, not a comparison of full layout widths).
3. Concrete theta multigraph (2 vertices, 3 parallel edges) confirming the loopless multigraph
   theory handles parallel edges directly.
4. Non-vacuous instantiation of `layoutBound_of_matching_mean` via `M = ∅`.
-/

open Cslib.Circuits.Frontier

/-! ### 1. Exact `pairKey` evaluation and strict `1 < 2` saving -/

example : pairKey (1 : ℝ) 5 2 8 = 2 := by
  unfold pairKey
  norm_num

example : pairKey (2 : ℝ) 8 1 5 = 2 := by
  unfold pairKey
  norm_num

example : twoVertexCost true false false false = 1 ∧
    starCost true false true + starCost false false true = 2 := by
  decide

example (t : ℝ) :
    twoVertexEnergy (decide ((1 : ℝ) < t)) (decide ((5 : ℝ) < t))
      (decide ((2 : ℝ) < t)) (decide ((8 : ℝ) < t))
      (decide (pairKey (1 : ℝ) 5 2 8 < t)) (decide (pairKey (2 : ℝ) 8 1 5 < t)) =
      twoVertexCost (decide ((1 : ℝ) < t)) (decide ((5 : ℝ) < t))
        (decide ((2 : ℝ) < t)) (decide ((8 : ℝ) < t)) :=
  twoVertexEnergy_pairKey 1 5 2 8 t

/-! ### 2. Concrete `K₄` strict saving (`matchingCost = 2 < 4 = edgeStraddles`) -/

private def k4Src : Fin 6 → Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 1

private def k4Tgt : Fin 6 → Fin 4
  | 0 => 1
  | 1 => 3
  | 2 => 2
  | 3 => 3
  | 4 => 2
  | 5 => 3

private def k4Graph : Multigraph (Fin 4) (Fin 6) :=
  ⟨k4Src, k4Tgt⟩

private def k4Matching : Set (Fin 6) := {0, 1}

-- Edge scores at threshold `0`: matched edges `{0, 1}` score `-1` (`< 0`), edge `2` (`{0, 2}`)
-- scores `-1` (`< 0`), and the remaining three edges `{0, 3}`, `{1, 2}`, `{1, 3}` score `1`.
private def k4Score : Fin 6 → ℝ
  | 0 => -1
  | 1 => -1
  | 2 => -1
  | 3 => 1
  | 4 => 1
  | 5 => 1

private theorem k4Graph_loopless : k4Graph.Loopless := by
  intro e; fin_cases e <;> decide

private theorem k4Graph_isMatching : k4Graph.IsMatching k4Matching := by
  intro e he f hf hne
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · exact (hne rfl).elim
  · rw [Set.disjoint_left]
    intro v hv1 hv2
    simp only [k4Graph, k4Src, k4Tgt, Set.mem_insert_iff, Set.mem_singleton_iff] at hv1 hv2
    omega
  · rw [Set.disjoint_left]
    intro v hv1 hv2
    simp only [k4Graph, k4Src, k4Tgt, Set.mem_insert_iff, Set.mem_singleton_iff] at hv1 hv2
    omega
  · exact (hne rfl).elim

private theorem k4Graph_edgeStraddles_all :
    ∀ v : Fin 4, k4Graph.EdgeStraddles k4Score 0 v := by
  intro v
  fin_cases v
  · exact ⟨⟨0, Or.inl rfl, by norm_num [k4Score]⟩, ⟨3, Or.inl rfl, by norm_num [k4Score]⟩⟩
  · exact ⟨⟨0, Or.inr rfl, by norm_num [k4Score]⟩, ⟨4, Or.inl rfl, by norm_num [k4Score]⟩⟩
  · exact ⟨⟨1, Or.inl rfl, by norm_num [k4Score]⟩, ⟨4, Or.inr rfl, by norm_num [k4Score]⟩⟩
  · exact ⟨⟨1, Or.inr rfl, by norm_num [k4Score]⟩, ⟨3, Or.inr rfl, by norm_num [k4Score]⟩⟩

example : k4Graph.matchingCost k4Matching k4Score 0 = 2 ∧
    {v | k4Graph.EdgeStraddles k4Score 0 v}.ncard = 4 := by
  have hall : {v | k4Graph.EdgeStraddles k4Score 0 v} = Set.univ :=
    Set.eq_univ_iff_forall.mpr k4Graph_edgeStraddles_all
  have hmat : k4Graph.matchedVertices k4Matching = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro v
    fin_cases v
    · exact ⟨0, Or.inl rfl, Or.inl rfl⟩
    · exact ⟨0, Or.inl rfl, Or.inr rfl⟩
    · exact ⟨1, Or.inr rfl, Or.inl rfl⟩
    · exact ⟨1, Or.inr rfl, Or.inr rfl⟩
  have hsingle : {v | v ∉ k4Graph.matchedVertices k4Matching ∧
      k4Graph.EdgeStraddles k4Score 0 v} = ∅ := by
    ext v; simp [hmat]
  have hany0 : k4Graph.PairStraddlesAny k4Score 0 0 :=
    ⟨⟨2, Or.inl ⟨Or.inl rfl, by decide⟩, by norm_num [k4Score]⟩,
      ⟨3, Or.inl ⟨Or.inl rfl, by decide⟩, by norm_num [k4Score]⟩⟩
  have hany1 : k4Graph.PairStraddlesAny k4Score 0 1 :=
    ⟨⟨2, Or.inl ⟨Or.inr rfl, by decide⟩, by norm_num [k4Score]⟩,
      ⟨4, Or.inl ⟨Or.inr rfl, by decide⟩, by norm_num [k4Score]⟩⟩
  have hnotboth0 : ¬k4Graph.PairStraddlesBoth k4Score 0 0 := by
    rintro ⟨-, ⟨f, hf, hlt⟩, -⟩
    fin_cases f <;> simp_all [k4Graph, Multigraph.incidenceSet, k4Src, k4Tgt, k4Score] <;>
      norm_num at hlt
  have hnotboth1 : ¬k4Graph.PairStraddlesBoth k4Score 0 1 := by
    rintro ⟨-, ⟨f, hf, hlt⟩, -⟩
    fin_cases f <;> simp_all [k4Graph, Multigraph.incidenceSet, k4Src, k4Tgt, k4Score] <;>
      norm_num at hlt
  have hA : {e | e ∈ k4Matching ∧ k4Graph.PairStraddlesAny k4Score 0 e} = k4Matching := by
    ext e
    constructor
    · exact And.left
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, hany0⟩
      · exact ⟨Or.inr rfl, hany1⟩
  have hB : {e | e ∈ k4Matching ∧ k4Graph.PairStraddlesBoth k4Score 0 e} = ∅ := by
    ext e
    simp only [Set.mem_empty_iff_false, iff_false, Set.mem_ofPred_eq, not_and]
    rintro (rfl | rfl)
    · exact hnotboth0
    · exact hnotboth1
  constructor
  · rw [Multigraph.matchingCost, hsingle, hA, hB, Set.ncard_empty]
    simp [k4Matching]
  · rw [hall, Set.ncard_univ, Nat.card_fin]

/-! ### 3. Concrete parallel-edge theta multigraph check -/

private def thetaGraph : Multigraph Bool (Fin 3) :=
  ⟨fun _ => false, fun _ => true⟩

private def thetaScore : Fin 3 → ℝ
  | 0 => 0
  | 1 => -1
  | 2 => 1

example : thetaGraph.IsMatching ({0} : Set (Fin 3)) ∧
    (thetaGraph.edgeCut {v | thetaGraph.matchingKey {0} thetaScore v < 0}).ncard ≤
      thetaGraph.matchingCost {0} thetaScore 0 := by
  have hloop : thetaGraph.Loopless := fun _ => Bool.false_ne_true
  have h3 : ∀ v : Bool, (thetaGraph.incidenceSet v).ncard = 3 := by
    intro v
    have : thetaGraph.incidenceSet v = Set.univ := by
      ext e; cases v <;> simp [thetaGraph, Multigraph.incidenceSet]
    rw [this, Set.ncard_univ, Nat.card_fin]
  have hM : thetaGraph.IsMatching ({0} : Set (Fin 3)) := Set.pairwise_singleton _ _
  exact ⟨hM, thetaGraph.ncard_edgeCut_threshold_le_matchingCost hloop h3 hM thetaScore 0⟩

/-! ### 4. Non-vacuous instantiation of `layoutBound_of_matching_mean` via `M = ∅` -/

example : LayoutBound 3 (2 * Gaussian.straddleBound 0) := by
  have hsb : 0 ≤ Gaussian.straddleBound 0 := by
    unfold Gaussian.straddleBound
    exact mul_nonneg (by positivity) (Real.arccos_nonneg _)
  refine Gaussian.layoutBound_of_matching_mean hsb 0 le_rfl 1
    (by norm_num : (-1 : ℝ) < 0) (by norm_num) ?_
  intro V E _ _ G hloop _ h3
  refine ⟨∅, G.isMatching_empty, fun t => ?_⟩
  rw [Gaussian.expectedMatchingCost_empty]
  have hle := Finset.sum_le_sum (s := Finset.univ) fun v _ =>
    Gaussian.measureReal_straddleEvent_le hloop h3 (q := 0) le_rfl (R := 1)
      (ρ₀ := 0) le_rfl (by norm_num) t v
  simpa [Finset.sum_const, nsmul_eq_mul] using hle
