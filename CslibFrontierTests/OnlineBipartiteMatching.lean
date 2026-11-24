/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Online.BipartiteMatching.Ranking
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Tests for online bipartite matching and `RANKING`

Checked finite witnesses for `CslibFrontier.Algorithms.Online.BipartiteMatching.Basic` and
`CslibFrontier.Algorithms.Online.BipartiteMatching.Ranking`:

* degenerate boundaries (empty arrival sequence, empty offline set, isolated arrival);
* the tight `2 + 2` deterministic `1/2` instance vs `RANKING`'s exact `3/4` expected ratio,
  matched by the `n = 2, s = 1` Yao harmonic upper bound;
* concrete monotonicity and dominance checks on `Fin 3`;
* explicit `K = 2` Devanur–Jain–Kleinberg primal-dual feasibility check;
* instantiations of the exact `1 - 1/e` lower bound and asymptotic upper bounds.
-/

public section

namespace CslibFrontierTests.OnlineBipartiteMatching

open Cslib.Algorithms.Lean.MaxFlow Cslib.Algorithms.Online.BipartiteMatching

/-! ### Degenerate and boundary instances -/

/-- Empty arrival sequence, empty offline vertex set, and isolated arrival all give size `0`. -/
example :
    ((rankingDet (Equiv.refl (Fin 2))).runMatching ([] : List (Finset (Fin 2)))).card = 0 ∧
    ((rankingDet (Equiv.refl (Fin 0))).runMatching ([∅] : List (Finset (Fin 0)))).card = 0 ∧
    ((rankingDet (Equiv.refl (Fin 2))).runMatching ([∅] : List (Finset (Fin 2)))).card = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [DetAlg.card_runMatching_eq_countP]; rfl
  · rw [DetAlg.card_runMatching_eq_countP]; rfl
  · rw [DetAlg.card_runMatching_eq_countP]; rfl

example :
    RandAlg.expectedMatchingSize (rankingAlg (Fin 2)) ([] : List (Finset (Fin 2))) = 0 := by
  rw [expectedMatchingSize_rankingAlg]
  simp only [DetAlg.card_runMatching_eq_countP, DetAlg.runChoices_nil, List.countP_nil,
    Nat.cast_zero, Finset.sum_const_zero, zero_div]

/-! ### Tight `2 + 2` instance: deterministic `1/2` vs `RANKING` `3/4` -/

/-- The `2 + 2` graph with arrivals `{0, 1}` followed by `{0}`. -/
def arrivals22 : List (Finset (Fin 2)) :=
  [({0, 1} : Finset (Fin 2)), ({0} : Finset (Fin 2))]

private def opt22 : Finset (Fin 2 × Fin arrivals22.length) :=
  {(1, ⟨0, by decide⟩), (0, ⟨1, by decide⟩)}

private theorem isMatching_opt22 : IsMatching (graphOfArrivals arrivals22) opt22 := by
  decide

private theorem card_opt22 : opt22.card = 2 := by
  decide

private theorem runChoices_id_22 :
    (rankingDet (Equiv.refl (Fin 2))).runChoices arrivals22 = [some 0, none] := by
  decide

private theorem runChoices_swap_22 :
    (rankingDet (Equiv.swap (0 : Fin 2) 1)).runChoices arrivals22 = [some 1, some 0] := by
  decide

/-- Under the identity ranking, `rankingDet` produces a maximal matching of size `1` against
`OPT = 2` (tight deterministic `1/2`). -/
example :
    IsMaximalMatching (graphOfArrivals arrivals22)
      ((rankingDet (Equiv.refl (Fin 2))).runMatching arrivals22) ∧
    ((rankingDet (Equiv.refl (Fin 2))).runMatching arrivals22).card = 1 ∧
    opt22.card = 2 * ((rankingDet (Equiv.refl (Fin 2))).runMatching arrivals22).card := by
  have hcard : ((rankingDet (Equiv.refl (Fin 2))).runMatching arrivals22).card = 1 := by
    rw [DetAlg.card_runMatching_eq_countP, runChoices_id_22]
    rfl
  refine ⟨DetAlg.isMaximalMatching_runMatching_of_isGreedy _ (isGreedy_rankingByKey _ _) arrivals22,
    hcard, by rw [card_opt22, hcard]⟩

/-- On the `2 + 2` graph `arrivals22`, `rankingAlg (Fin 2)` achieves exact expected matching size
`3 / 2 = (3 / 4) * OPT`, strictly beating deterministic `1/2`. -/
example :
    RandAlg.expectedMatchingSize (rankingAlg (Fin 2)) arrivals22 = 3 / 2 := by
  rw [expectedMatchingSize_rankingAlg]
  have hcard_perm : (Fintype.card (Fin 2 ≃ Fin (Fintype.card (Fin 2))) : ℝ) = 2 := by
    rw [Fintype.card_fin, Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hsum :
      (∑ π : Fin 2 ≃ Fin (Fintype.card (Fin 2)),
        (((rankingDet π).runMatching arrivals22).card : ℝ)) = 3 := by
    have hfin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    have hperm : ∀ π : Equiv.Perm (Fin 2), π = Equiv.refl (Fin 2) ∨ π = Equiv.swap 0 1 := by
      intro π
      rcases hfin2 (π 0) with h0 | h0
      · left
        ext x
        rcases hfin2 x with rfl | rfl
        · exact congrArg Fin.val h0
        · rcases hfin2 (π 1) with h1 | h1
          · exact absurd (π.injective (h1.trans h0.symm)) (by decide)
          · exact congrArg Fin.val h1
      · right
        ext x
        rcases hfin2 x with rfl | rfl
        · simpa using congrArg Fin.val h0
        · rcases hfin2 (π 1) with h1 | h1
          · simpa using congrArg Fin.val h1
          · exact absurd (π.injective (h1.trans h0.symm)) (by decide)
    have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
        {Equiv.refl (Fin 2), Equiv.swap 0 1} := by
      ext π
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact hperm π
    have hne : Equiv.refl (Fin 2) ≠ Equiv.swap (0 : Fin 2) 1 := by
      intro h
      have := Equiv.congr_fun h 0
      simp at this
    change (∑ π : Equiv.Perm (Fin 2), (((rankingDet π).runMatching arrivals22).card : ℝ)) = 3
    rw [huniv, Finset.sum_pair hne, DetAlg.card_runMatching_eq_countP,
      DetAlg.card_runMatching_eq_countP, runChoices_id_22, runChoices_swap_22]
    norm_num
  rw [hcard_perm, hsum]

/-- Matching `n = 2` Yao harmonic upper bound (`s = 1`): no randomized online algorithm on `Fin 2`
achieves expected matching size strictly above `3 / 2 = (3 / 4) * OPT` on all permutations of
`triArrivals 2`. -/
example (μ : RandAlg (Fin 2)) :
    ∃ σ : Equiv.Perm (Fin 2),
      RandAlg.expectedMatchingSize μ (triArrivals 2 σ) ≤ 3 / 2 := by
  obtain ⟨σ, hle⟩ := exists_rand_harmonic_upper_bound (n := 2) (s := 1) (by omega) (by omega) μ
  refine ⟨σ, hle.trans_eq ?_⟩
  simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-! ### Concrete monotonicity and dominance on `Fin 3` -/

private def arrivals3 : List (Finset (Fin 3)) :=
  [({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1} : Finset (Fin 3))]

/-- Deleting offline vertex `0` shifts step 0 from `0` to `1`, keeps step 1 at `2`, and leaves
step 2 unmatched (`none`), exercising `rankingByKey_monotone_choice`. -/
example :
    (rankingDet (Equiv.refl (Fin 3))).runChoices arrivals3 = [some 0, some 2, some 1] ∧
    (rankingDet (Equiv.refl (Fin 3))).runChoices (deleteOffline 0 arrivals3) =
      [some 1, some 2, none] := by
  decide

private def arrivals3Dom : List (Finset (Fin 3)) :=
  [({0, 1} : Finset (Fin 3)), ({0} : Finset (Fin 3))]

/-- When offline vertex `1` remains unmatched in `arrivals3Dom`, deleting `1` leaves all choices
unchanged and step 0 matches `0` with `0 < 1`, exercising `rankingByKey_dominance`. -/
example :
    (1 : Fin 3) ∉ (rankingDet (Equiv.refl (Fin 3))).matchedLeft arrivals3Dom ∧
    (rankingDet (Equiv.refl (Fin 3))).runChoices arrivals3Dom =
      (rankingDet (Equiv.refl (Fin 3))).runChoices (deleteOffline 1 arrivals3Dom) ∧
    ((rankingDet (Equiv.refl (Fin 3))).runChoices (deleteOffline 1 arrivals3Dom))[0] =
      some 0 := by
  decide

/-! ### Concrete DJK dual feasibility witness (`K = 2`) -/

private def ord2 : Fin 2 ≃ Fin (Fintype.card (Fin 2)) := Equiv.refl (Fin 2)

/-- Exact `K = 2` DJK weights and primal-dual identity + edge feasibility on `arrivals22`. -/
example :
    djkWeight 2 0 = 4 / 9 ∧
    djkWeight 2 1 = 2 / 3 ∧
    (∑ u : Fin 2, djkDualLeft (fun i : Fin 2 => i) ord2 arrivals22 u) +
      (∑ j : Fin arrivals22.length,
        djkDualRight (fun i : Fin 2 => i) ord2 arrivals22 j) = 1 ∧
    (10 / 9 : ℝ) ≤ ∑ k : Fin 2,
      (djkDualLeft (Function.update (fun i : Fin 2 => i) 1 k) ord2 arrivals22 1 +
        djkDualRight (Function.update (fun i : Fin 2 => i) 1 k) ord2 arrivals22
          ⟨0, by decide⟩) := by
  refine ⟨by norm_num [djkWeight], by norm_num [djkWeight], ?_, ?_⟩
  · rw [sum_djkDual_eq_card]
    have hc : ((rankingGridDet (fun i : Fin 2 => i) ord2).runMatching
        arrivals22).card = 1 := by
      rw [DetAlg.card_runMatching_eq_countP]
      decide
    exact_mod_cast hc
  · have h := sum_djkDual_update_ge (K := 2) (fun i : Fin 2 => i) ord2
      arrivals22 1 ⟨0, by decide⟩ (by decide)
    linarith [show (2 : ℝ) * (1 - ((2 : ℝ) / ((2 : ℝ) + 1)) ^ 2) = 10 / 9 by norm_num]

/-! ### Headline theorem instantiations -/

example :
    (1 - Real.exp (-1)) * 2 ≤ RandAlg.expectedMatchingSize (rankingAlg (Fin 2)) arrivals22 := by
  simpa [card_opt22] using ranking_competitive_ratio arrivals22 isMatching_opt22

example :
    ∃ arrivals : List (Finset (Fin 2)),
      arrivals.length = 2 ∧
      (∃ M, IsMatching (graphOfArrivals arrivals) M ∧ M.card = 2) ∧
      ((rankingDet (Equiv.refl (Fin 2))).runMatching arrivals).card ≤ 1 :=
  exists_det_half_witness (rankingDet (Equiv.refl (Fin 2)))

example :
    ∃ σ : Equiv.Perm (Fin 4),
      RandAlg.expectedMatchingSize (rankingAlg (Fin 4)) (triArrivals 4 σ) ≤
        (1 - Real.exp (-1)) * 4 + 2 :=
  exists_rand_exp_upper_bound (n := 4) (by omega) (rankingAlg (Fin 4))

example :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ μ : RandAlg (Fin n),
      ∃ (arrivals : List (Finset (Fin n))) (M : Finset (Fin n × Fin arrivals.length)),
        IsMatching (graphOfArrivals arrivals) M ∧
        RandAlg.expectedMatchingSize μ arrivals < (3 / 4 : ℝ) * (M.card : ℝ) - 0 := by
  have hlt : 1 - Real.exp (-1) < 3 / 4 := by
    have he := Real.exp_one_lt_d9
    have hinv : (1 / 3 : ℝ) < Real.exp (-1) := by
      rw [Real.exp_neg, one_div, inv_lt_inv₀ (by norm_num) (Real.exp_pos 1)]
      linarith
    linarith
  exact not_rand_competitive_of_gt_one_sub_exp_neg_one hlt 0

end CslibFrontierTests.OnlineBipartiteMatching
