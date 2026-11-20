/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator
import CslibFrontier.Algorithms.Reachability.DoubleCounting.ControllerReplay

/-! A diamond with two distinct paths of different internal weights. -/

namespace CslibFrontierTests.LayeredDigraph

open Cslib

private def diamondLayer (v : Fin 4) : ℕ :=
  if v = 0 then 0 else if v = 3 then 2 else 1

private def diamond : LayeredDigraph (Fin 4) where
  Adj a b := diamondLayer b = diamondLayer a + 1
  layer := diamondLayer
  layer_adj h := h

private theorem adj_of_layer {a b : Fin 4} (h : diamondLayer b = diamondLayer a + 1) :
    diamond.Adj a b := h

private def viaOne : diamond.Path 0 3 :=
  (LayeredDigraph.Path.ofAdj (G := diamond) (b := 1) (adj_of_layer (by decide))).comp
    (LayeredDigraph.Path.ofAdj (G := diamond) (adj_of_layer (by decide)))

private def viaTwo : diamond.Path 0 3 :=
  (LayeredDigraph.Path.ofAdj (G := diamond) (b := 2) (adj_of_layer (by decide))).comp
    (LayeredDigraph.Path.ofAdj (G := diamond) (adj_of_layer (by decide)))

example : viaOne ∈ diamond.pathsThrough 0 3 1 ∧ viaOne ∉ diamond.pathsThrough 0 3 2 := by
  change (1 : Fin 4) ∈ [1] ∧ (2 : Fin 4) ∉ [1]
  decide

example : viaOne.internalWeight Fin.val < viaTwo.internalWeight Fin.val := by
  change 1 < (2 : ℕ)
  decide

example : ∃! v, v ∈ viaTwo.vertices ∧ diamond.layer v = 1 :=
  viaTwo.existsUnique_vertex (by decide) (by decide)

example : IsMinOn (LayeredDigraph.Path.internalWeight Fin.val)
    (diamond.pathsThrough 0 3 1) viaOne := by
  unfold viaOne
  rw [LayeredDigraph.isMinOn_pathsThrough_comp_iff _ _ _
    (by decide : diamond.layer 0 < diamond.layer 1)
    (by decide : diamond.layer 1 < diamond.layer 3)]
  constructor <;> rw [isMinOn_univ_iff] <;> intro q
  · rw [LayeredDigraph.Path.eq_of_layer_le_succ
      (by decide : diamond.layer 1 ≤ diamond.layer 0 + 1) q _]
  · rw [LayeredDigraph.Path.eq_of_layer_le_succ
      (by decide : diamond.layer 3 ≤ diamond.layer 1 + 1) q _]

example : ¬diamond.Adj 0 3 := by
  change ¬diamondLayer 3 = diamondLayer 0 + 1
  decide

private def rectangularDiamond : LayeredDigraph (Fin (2 + 1) × Fin 2) where
  Adj a b := b.1.val = a.1.val + 1
  layer z := z.1.val
  layer_adj h := h

open Cslib.Reachability.Hoza Cslib.Code.JustesenFamily

-- Apply both resource-independent guarantees to an actual graph.
example :
    ∃ seed : Fin (codeLength 2 2) → Bool,
      rectangularDiamond.IsMinIsolating (generatedWeight seed) ∧
        ∃ C : ℕ, ∀ z : Fin 3 × Fin 2, generatedWeight seed z < (2 * (2 * (2 + 1) + 1)) ^ C := by
  obtain ⟨seed, h⟩ := exists_generatedWeight_isMinIsolating rectangularDiamond fun _ => rfl
  obtain ⟨C, hC⟩ := generatedWeight_polynomial
  exact ⟨seed, h, C, hC 2 2 seed⟩

example : codeLength 2 2 ≤ 268435456 * (Nat.log 2 (2 * (2 + 1)) + 1) :=
  (codeLength_bounds 2 2).2

open Cslib.DoubleCounting Relation

private theorem firstRound_unique : ∃! w, Passes diamond.Adj 0 1 w := by
  have hzero := existsUnique_passes_zero diamond.Adj (0 : Fin 4)
  obtain ⟨w, hw⟩ := hzero.exists
  apply (existsUnique_passes_succ_iff hw hzero).mpr
  intro v hv
  obtain ⟨hnew, hold⟩ := (mem_frontier_iff hw).mp hv
  have hnext := mem_round.mp hnew
  rw [reachableWithin_succ, Set.mem_union, Set.mem_ofPred_eq] at hnext
  rcases hnext with h | ⟨u, hu, he⟩
  · exact (hold (mem_round.mpr h)).elim
  · have hu' : u = 0 := by simpa using hu
    subst u
    refine ⟨0, ⟨by simp [mem_round], he⟩, fun y hy => ?_⟩
    simpa [mem_round] using hy.1

private theorem target_outside_first : (3 : Fin 4) ∉ round diamond.Adj 0 1 := by
  rw [mem_round, reachableWithin_succ, Set.mem_union, Set.mem_ofPred_eq]
  rintro (h | ⟨u, hu, he⟩)
  · simp at h
  · have hu' : u = 0 := by simpa using hu
    subst u
    exact (by decide : diamondLayer 3 ≠ diamondLayer 0 + 1) he

example (w : Transcript (Fin 4)) (hw : Passes diamond.Adj 0 1 w) :
    ¬(w 3).isSome ∧ ¬∃! t, Passes diamond.Adj 0 2 t := by
  have hnew : (3 : Fin 4) ∈ round diamond.Adj 0 2 := by
    exact mem_round.mpr ⟨2, le_rfl, (RelatesInSteps.single
      (adj_of_layer (a := 0) (b := 1) (by decide))).trans
        (RelatesInSteps.single (adj_of_layer (b := 3) (by decide)))⟩
  refine ⟨fun h => target_outside_first (mem_round.mpr ((isSome_iff hw).mp h)), ?_⟩
  rw [existsUnique_passes_succ_iff hw firstRound_unique]
  intro h
  obtain ⟨x, _, hx⟩ := h 3 ((mem_frontier_iff hw).mpr ⟨hnew, target_outside_first⟩)
  have hpred (u : Fin 4) (h₁ : diamond.Adj 0 u) (h₂ : diamond.Adj u 3) : u = x :=
    hx u ⟨mem_round.mpr ⟨1, le_rfl, RelatesInSteps.single h₁⟩, h₂⟩
  have h₁ := hpred 1 (adj_of_layer (by decide)) (adj_of_layer (by decide))
  have h₂ := hpred 2 (adj_of_layer (by decide)) (adj_of_layer (by decide))
  exact (by decide : (1 : Fin 4) ≠ 2) (h₁.trans h₂.symm)

-- Before radius two, the diamond reaches the source and then the two middle vertices.
private def diamondScan : MembershipScan List 4 :=
  fun k _ v => [decide (v = 0 ∨ (k > 0 ∧ v ≠ 3))]

private def diamondEdge (u v : Fin 4) : List Bool :=
  [decide (diamondLayer v = diamondLayer u + 1)]

-- The second update flags the tied target and contributes exactly one new vertex.
set_option linter.hashCommand false in
#guard ((scanNextRound diamondEdge diamondScan 1 ⟨3, 2⟩).map
  (fun a => (a.tally.count, a.tally.lengthSum, a.bad))) == [(4, 4, true)]

set_option linter.hashCommand false in
#guard runController diamondEdge diamondScan 3 == [some (.bad 2)]

private def isolatedScan : MembershipScan List 2 := fun _ _ v => [v == 0]

set_option linter.hashCommand false in
#guard runController (fun _ _ => [false]) isolatedScan 0 == [some (.decided true)]

set_option linter.hashCommand false in
#guard runController (fun _ _ => [false]) isolatedScan 1 == [some (.decided false)]

private abbrev emptyEdge : Fin 2 → Fin 2 → Prop := fun _ _ => False

-- Supply the actual typed scan to the controller on a graph stable at round zero.
example (target : Fin 2) : ∃ verdict,
    runController (fun _ _ => [false]) (replayMembership (fun _ _ => false) 0) target =
      [some verdict] ∧
    match verdict with
    | .bad _ => False
    | .decided b => (b = true ↔ ReflTransGen emptyEdge 0 target) := by
  classical
  have hedge : (fun _ _ : Fin 2 => false = true) = emptyEdge := by
    funext u v
    simp
  have hround (k : ℕ) : reachableWithin emptyEdge 0 k = {0} := by
    induction k with
    | zero => exact reachableWithin_zero
    | succ k ih => simp [reachableWithin_succ, ih, emptyEdge]
  obtain ⟨verdict, hrun, hspec⟩ := runController_replay_correct (fun _ _ : Fin 2 => false) 0 target
  refine ⟨verdict, hrun, ?_⟩
  rw [hedge] at hspec
  cases verdict with
  | bad j =>
    apply hspec.2
    have h0 := existsUnique_passes_zero emptyEdge 0
    rw [existsUnique_passes_iff] at h0 ⊢
    simpa [mem_round, hround] using h0
  | decided _ => exact hspec.2

end CslibFrontierTests.LayeredDigraph
