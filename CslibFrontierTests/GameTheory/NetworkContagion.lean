/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Network.Contagion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Networked coordination games and contagion threshold tests

Ordinary-import `module` client exercising `Cslib.GameTheory.Network`:

* Tie-breaking boundary at `q = 1 / 2`: on `intPathGraph` with `S = {0, 1}`, vertex `2` has one of
  two neighbors in `S` (exact payoff tie `1 / 2 = 1 / 2`) and adopts `B` at `q = 1 / 2`, whereas at
  `q = 3 / 5 > 1 / 2` vertex `2` strictly prefers `A` and does not adopt `B`.
* Contagion on `intPathGraph`: `{0, 1}` and `{-1, 0, 1}` are contagious at `q = 1 / 2` (and at
  `q = 1 / 3 ≤ 1 / 2`), whereas at `q = 3 / 5 > 1 / 2` no finite set is contagious (via
  `intPathGraph_connected.preconnected.degree_pos_of_nontrivial` and Theorem 24.2), matching
  `contagionThreshold intPathGraph = 1 / 2`.
* Progressive vs. nonprogressive separation on `{0}` at `q = 1 / 2`: `{0}` is contagious under
  `progressiveStep` but not under `bestResponseStep`, even though
  `⋃ j, (bestResponseStep intPathGraph (1 / 2))^[j] {0} = Set.univ` and `0` returns at step `2`
  (witnessing both why Theorem 24.1 must replace the seed set and why `IsContagious` for `h_q`
  cannot be weakened to `⋃ j, h_q^[j] S = Set.univ`).
* Hypothesis necessity for Theorem 24.2: on the edgeless graph `⊥ : SimpleGraph ℕ` (isolated
  vertices, violating `∀ v, 0 < G.degree v`) and on `⊤ : SimpleGraph (Fin 2)` (finite `K_2`,
  violating `[Infinite V]`), a finite set is contagious at `q = 3 / 4 > 1 / 2` and
  `contagionThreshold = 1 > 1 / 2`.
* General symmetric `2 × 2` coordination payoffs (Exercise 24.2) and `CostGame.IsPureNash` bridge:
  a non-normalized coordination game with `threshold = 1 / 2` agrees with `bestResponseStep` at
  `1 / 2`, a non-coordination payoff matrix fails `IsCoordination`, and all-`A` / all-`B` fixed
  points are pure Nash equilibria.
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.NetworkContagion

open Cslib.GameTheory Cslib.GameTheory.Network

/-! ### Tie boundary at `q = 1 / 2` -/

/-- At `q = 1 / 2` on `intPathGraph`, vertex `2` has 1 of 2 neighbors in `{0, 1}` (an exact payoff
tie `payoffA = 1 / 2 = payoffB`) and adopts `B`; at `q = 3 / 5 > 1 / 2` it stays with `A`. -/
example :
    (2 : ℤ) ∈ bestResponseStep intPathGraph (1 / 2) (({0, 1} : Finset ℤ) : Set ℤ) ∧
      (2 : ℤ) ∉ bestResponseStep intPathGraph (3 / 5) (({0, 1} : Finset ℤ) : Set ℤ) := by
  have hpair : (({0, 1} : Finset ℤ) : Set ℤ) = Set.Icc (0 : ℤ) 1 := by
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_Icc]
    omega
  have hinter : intPathGraph.neighborSet (2 : ℤ) ∩ Set.Icc (0 : ℤ) 1 = {1} := by
    ext y
    simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, intPathGraph_adj_iff, Set.mem_Icc,
      Set.mem_singleton_iff]
    omega
  rw [hpair]
  refine ⟨?_, ?_⟩
  · rw [bestResponseStep_intPathGraph_half_Icc (by omega), Set.mem_Icc]
    omega
  · rw [mem_bestResponseStep_iff, intPathGraph_degree, hinter, Set.ncard_singleton]
    norm_num

/-! ### Contagious and non-contagious witnesses on `ℤ` -/

/-- `{0, 1}` is contagious on `intPathGraph` at `q = 1 / 2` and at every lower threshold such as
`q = 1 / 3`, and `contagionThreshold intPathGraph = 1 / 2`. -/
example :
    IsContagious (bestResponseStep intPathGraph (1 / 2)) (({0, 1} : Finset ℤ) : Set ℤ) ∧
      IsContagious (bestResponseStep intPathGraph (1 / 3)) (({0, 1} : Finset ℤ) : Set ℤ) ∧
      contagionThreshold intPathGraph = 1 / 2 :=
  ⟨isContagious_intPathGraph_half_pair,
    isContagious_bestResponseStep_of_le intPathGraph (by norm_num)
      isContagious_intPathGraph_half_pair,
    contagionThreshold_intPathGraph⟩

/-- The chapter's seed set `{-1, 0, 1}` is also contagious on `intPathGraph` at `q = 1 / 2`
([Kleinberg2007], Section 24.2, p. 616). -/
example :
    IsContagious (bestResponseStep intPathGraph (1 / 2)) (({-1, 0, 1} : Finset ℤ) : Set ℤ) := by
  have htriple : (({-1, 0, 1} : Finset ℤ) : Set ℤ) = Set.Icc (-1 : ℤ) 1 := by
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_Icc]
    omega
  have hiter : ∀ k : ℕ,
      (bestResponseStep intPathGraph (1 / 2))^[k] (Set.Icc (-1 : ℤ) 1) =
        Set.Icc (-1 - (k : ℤ)) (1 + (k : ℤ)) := by
    intro k
    induction k with
    | zero => simp only [Function.iterate_zero_apply, Nat.cast_zero, sub_zero, add_zero]
    | succ k ih =>
        rw [Function.iterate_succ_apply', ih,
          bestResponseStep_intPathGraph_half_Icc (by omega : -1 - (k : ℤ) < 1 + (k : ℤ))]
        ext x
        simp only [Set.mem_Icc]
        omega
  rw [htriple]
  intro w
  refine ⟨w.natAbs, fun j hj => ?_⟩
  rw [hiter j, Set.mem_Icc]
  omega

/-- At `q = 3 / 5 > 1 / 2`, Theorem 24.2 (applied via `intPathGraph_connected`) shows `{0, 1}` is
neither progressive-contagious nor nonprogressive-contagious on `intPathGraph`. -/
example :
    ¬ IsContagious (progressiveStep intPathGraph (3 / 5)) (({0, 1} : Finset ℤ) : Set ℤ) ∧
      ¬ IsContagious (bestResponseStep intPathGraph (3 / 5)) (({0, 1} : Finset ℤ) : Set ℤ) :=
  have hdeg : ∀ v : ℤ, 0 < intPathGraph.degree v :=
    fun v => intPathGraph_connected.preconnected.degree_pos_of_nontrivial v
  ⟨not_isContagious_progressiveStep_of_half_lt intPathGraph hdeg (by norm_num) {0, 1},
    not_isContagious_bestResponseStep_of_half_lt intPathGraph hdeg (by norm_num) {0, 1}⟩

/-! ### Progressive vs. nonprogressive separation and parity oscillation on `{0}` -/

/-- On `intPathGraph` at `q = 1 / 2`, `{0}` is progressive-contagious but not
nonprogressive-contagious, yet `0` returns at step `2` and the union of all nonprogressive iterates
is still `Set.univ`. This separates `progressiveStep` from `bestResponseStep` on the same seed set
and shows `IsContagious` for `h_q` is strictly stronger than `⋃ j, h_q^[j] S = Set.univ`. -/
example :
    IsContagious (progressiveStep intPathGraph (1 / 2)) ({0} : Set ℤ) ∧
      ¬ IsContagious (bestResponseStep intPathGraph (1 / 2)) ({0} : Set ℤ) ∧
      (0 : ℤ) ∈ (bestResponseStep intPathGraph (1 / 2))^[2] ({0} : Set ℤ) ∧
      (⋃ j, (bestResponseStep intPathGraph (1 / 2))^[j] ({0} : Set ℤ)) = Set.univ := by
  refine ⟨isContagious_progressiveStep_intPathGraph_half_singleton,
    not_isContagious_intPathGraph_half_singleton, ?_, ?_⟩
  · rw [bestResponseStep_iterate_intPathGraph_half_singleton]
    simp only [Set.mem_ofPred_eq]
    omega
  · rw [Set.eq_univ_iff_forall]
    intro w
    refine Set.mem_iUnion.mpr ⟨w.natAbs, ?_⟩
    rw [bestResponseStep_iterate_intPathGraph_half_singleton]
    simp only [Set.mem_ofPred_eq]
    omega

/-- Theorem 24.1 witness from `{0}`: because `{0}` is progressive-contagious at `q = 1 / 2`, some
finite set is nonprogressive-contagious at `q = 1 / 2` (though `{0}` itself is not). -/
example : ∃ S : Finset ℤ, IsContagious (bestResponseStep intPathGraph (1 / 2)) (S : Set ℤ) :=
  (exists_finset_isContagious_bestResponseStep_iff_progressiveStep intPathGraph
    (by norm_num : (1 / 2 : ℝ) ≤ 1)).mpr
    ⟨{0}, by simpa only [Finset.coe_singleton] using
      isContagious_progressiveStep_intPathGraph_half_singleton⟩

/-- Equation (24.1) check: on `intPathGraph` at `q = 1 / 2`, the second progressive iterate of `{0}`
equals `{0} ∪ h_{1/2}(h̄_{1/2}({0}))`. -/
example :
    (progressiveStep intPathGraph (1 / 2))^[2] ({0} : Set ℤ) =
      ({0} : Set ℤ) ∪
        bestResponseStep intPathGraph (1 / 2)
          ((progressiveStep intPathGraph (1 / 2))^[1] ({0} : Set ℤ)) :=
  progressiveStep_iterate_succ intPathGraph (1 / 2) {0} 1

/-! ### Hypothesis necessity for Theorem 24.2 -/

private local instance : (⊥ : SimpleGraph ℕ).LocallyFinite := fun _ =>
  Fintype.ofFinset ∅ fun _ => by
    simp only [Finset.notMem_empty, SimpleGraph.mem_neighborSet, SimpleGraph.bot_adj]

/-- Removing `∀ v, 0 < G.degree v` breaks Theorem 24.2: on the edgeless graph `⊥ : SimpleGraph ℕ`,
every vertex has degree `0`, so `∅` is contagious at `q = 3 / 4 > 1 / 2` and
`contagionThreshold (⊥ : SimpleGraph ℕ) = 1`. -/
example :
    IsContagious (bestResponseStep (⊥ : SimpleGraph ℕ) (3 / 4)) ((∅ : Finset ℕ) : Set ℕ) ∧
      contagionThreshold (⊥ : SimpleGraph ℕ) = 1 := by
  have hall : ∀ q : ℝ,
      IsContagious (bestResponseStep (⊥ : SimpleGraph ℕ) q) ((∅ : Finset ℕ) : Set ℕ) := by
    intro q w
    refine ⟨1, fun j hj => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hj
    rw [Function.iterate_succ_apply', mem_bestResponseStep_iff]
    have hdeg : (⊥ : SimpleGraph ℕ).degree w = 0 :=
      (SimpleGraph.degree_eq_zero (G := (⊥ : SimpleGraph ℕ)) (v := w)).mpr
        SimpleGraph.IsIsolated.bot
    rw [hdeg]
    simp only [Nat.cast_zero, mul_zero, Nat.cast_nonneg]
  refine ⟨hall (3 / 4), le_antisymm (contagionThreshold_le_one (⊥ : SimpleGraph ℕ)) ?_⟩
  exact le_contagionThreshold (⊥ : SimpleGraph ℕ) (by norm_num) le_rfl ∅ (hall 1)

/-- Removing `[Infinite V]` breaks Theorem 24.2: on the finite complete graph `K_2`
(`⊤ : SimpleGraph (Fin 2)`), every vertex has degree `1 > 0`, yet `Finset.univ` is contagious for
every `q ≤ 1` (including `q = 3 / 4 > 1 / 2`) and `contagionThreshold K_2 = 1`. -/
example :
    let G : SimpleGraph (Fin 2) := ⊤
    IsContagious (bestResponseStep G (3 / 4)) ((Finset.univ : Finset (Fin 2)) : Set (Fin 2)) ∧
      contagionThreshold G = 1 := by
  let G : SimpleGraph (Fin 2) := ⊤
  have huniv : ∀ q : ℝ, q ≤ 1 → bestResponseStep G q Set.univ = Set.univ := by
    intro q hq
    ext v
    simp only [mem_bestResponseStep_iff, Set.inter_univ, Set.mem_univ, iff_true]
    have hnc : (G.neighborSet v).ncard = G.degree v :=
      calc
        (G.neighborSet v).ncard = (G.neighborFinset v : Set (Fin 2)).ncard := by
          rw [G.coe_neighborFinset]
        _ = (G.neighborFinset v).card := Set.ncard_coe_finset _
        _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
    rw [hnc]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) hq
  have hcont : ∀ q : ℝ, q ≤ 1 →
      IsContagious (bestResponseStep G q) ((Finset.univ : Finset (Fin 2)) : Set (Fin 2)) := by
    intro q hq w
    have hiter : ∀ j, (bestResponseStep G q)^[j] Set.univ = Set.univ := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih, huniv q hq]
    refine ⟨0, fun j _ => ?_⟩
    rw [Finset.coe_univ, hiter j]
    trivial
  refine ⟨hcont (3 / 4) (by norm_num), le_antisymm (contagionThreshold_le_one G) ?_⟩
  exact le_contagionThreshold G (by norm_num) le_rfl Finset.univ (hcont 1 le_rfl)

/-! ### General coordination payoffs (Exercise 24.2) and pure Nash equilibria -/

/-- A non-normalized coordination game with `uAA = 5, uBA = 2, uAB = 1, uBB = 4` satisfies
`IsCoordination`, has `threshold = 1 / 2`, and shares contagion with `bestResponseStep _ (1 / 2)`;
changing `uAA` to `1` violates `IsCoordination`. -/
example :
    let p : CoordinationPayoffs := ⟨5, 2, 1, 4⟩
    let pBad : CoordinationPayoffs := ⟨1, 2, 1, 4⟩
    p.IsCoordination ∧ ¬ pBad.IsCoordination ∧ p.threshold = 1 / 2 ∧
      IsContagious (p.bestResponseStep intPathGraph) (({0, 1} : Finset ℤ) : Set ℤ) ∧
      ¬ IsContagious (p.bestResponseStep intPathGraph) ({0} : Set ℤ) := by
  let p : CoordinationPayoffs := ⟨5, 2, 1, 4⟩
  let pBad : CoordinationPayoffs := ⟨1, 2, 1, 4⟩
  have hp : p.IsCoordination := ⟨by norm_num, by norm_num⟩
  have hpBad : ¬ pBad.IsCoordination := fun h => by
    have : (2 : ℝ) < 1 := h.1
    linarith
  have hq : p.threshold = 1 / 2 := by
    rw [CoordinationPayoffs.threshold_def]
    norm_num [p]
  refine ⟨hp, hpBad, hq, ?_, ?_⟩
  · rw [CoordinationPayoffs.isContagious_iff intPathGraph hp, hq]
    exact isContagious_intPathGraph_half_pair
  · rw [CoordinationPayoffs.isContagious_iff intPathGraph hp, hq]
    exact not_isContagious_intPathGraph_half_singleton

/-- Both uniform profiles (all `A` and all `B`) are fixed points of `bestResponseStep` at
`q = 1 / 2` on `intPathGraph`, hence pure Nash equilibria of the networked coordination `CostGame`.
-/
example :
    ((CoordinationPayoffs.normalized (1 / 2)).toCostGame intPathGraph).IsPureNash (fun _ => false) ∧
      ((CoordinationPayoffs.normalized (1 / 2)).toCostGame intPathGraph).IsPureNash
        (fun _ => true) := by
  refine ⟨CoordinationPayoffs.isPureNash_of_bestResponseStep_eq _ _ ?_,
    CoordinationPayoffs.isPureNash_of_bestResponseStep_eq _ _ ?_⟩
  · rw [CoordinationPayoffs.normalized_bestResponseStep]
    ext v
    simp only [mem_bestResponseStep_iff, intPathGraph_degree, Bool.false_eq_true,
      Set.ofPred_false, Set.inter_empty, Set.ncard_empty]
    norm_num
  · rw [CoordinationPayoffs.normalized_bestResponseStep]
    ext v
    simp only [mem_bestResponseStep_iff, intPathGraph_degree, Set.ofPred_true, Set.inter_univ]
    have hnc : (intPathGraph.neighborSet v).ncard = intPathGraph.degree v := by
      rw [← intPathGraph.coe_neighborFinset, Set.ncard_coe_finset,
        SimpleGraph.card_neighborFinset_eq_degree]
    rw [hnc, intPathGraph_degree]
    norm_num

end CslibFrontierTests.GameTheory.NetworkContagion
