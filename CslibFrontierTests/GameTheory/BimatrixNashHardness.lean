/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Bimatrix.NashHardness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# NP-hardness of Nash equilibrium decision problems: checked instances

Ordinary `module` client of `CslibFrontier.GameTheory.Bimatrix.NashHardness` exercising:

1. Concrete satisfiable CNF witness (`satCNF` on `Fin 3`) in `gilboaZemelGame 3 satCNF`:
   * has at least two distinct mixed Nash equilibria (`default` and the uniform assignment
     strategy for `fun _ => true`);
   * achieves `payoff₁ = 2 ≥ 2` and `payoff₁ + payoff₂ = 4 ≥ 4`;
   * has support cardinality `3 > 1`, contains `lit 0 true`, and omits `default`.
2. Concrete unsatisfiable CNF witness (`unsatCNF` on `Fin 3`) in `gilboaZemelGame 3 unsatCNF`:
   * `(Pi.single .default 1, Pi.single .default 1)` is the unique mixed Nash equilibrium;
   * all six properties fail (no second equilibrium, `payoff₁ = 1 < 2`, `payoff₁ + payoff₂ = 2 < 4`,
     support size `1`, `lit 0 true` has probability `0`, and `default` has probability `1 ≠ 0`).
3. Edge cases and boundaries of `gilboaZemelGame`:
   * empty formula `[]` on `Fin 3` (satisfiable) and empty-clause formula `[[]]` on `Fin 3`
     (unsatisfiable);
   * `N = 2` boundary where `isNash_gilboaZemelGame_iff` holds with assignment payoff `1`;
   * `N = 1` boundary where `gilboaZemelAssignmentStrategy` fails to be a Nash equilibrium
     (confirming `2 ≤ N` cannot be dropped).
4. Concrete `BimatrixCode` decision-problem witnesses and model boundaries:
   * symmetric pure-coordination game `coordCode` satisfying all six decision problems;
   * symmetric strict-dominance game `domCode` (with `matA ≠ matAᵀ`, `matB = matAᵀ`) whose unique
     mixed Nash equilibrium `(![1, 0], ![1, 0])` witnesses non-membership in all six decision
     problems for the corresponding thresholds and strategy indices;
   * asymmetric matrix rejection (`matB ≠ matAᵀ`) and out-of-range strategy index rejection.
5. Ordinary `module` client access to all six `NPHard` theorems for [Papadimitriou2007],
   Theorem 2.3 (p. 33).
-/

public section

namespace CslibFrontierTests.GameTheory.BimatrixNashHardness

open Cslib.Complexity Cslib.GameTheory Cslib.GameTheory.BimatrixCode Cslib.GameTheory.BimatrixGame
  Cslib.Logic.PL Matrix Turing.MultiTapeTM

/-! ### Satisfiable CNF witness on `Fin 3` -/

/-- Satisfiable CNF formula on `Fin 3` forcing variable `0` true. -/
def satCNF : CNF (Fin 3) :=
  [[(0, true)], [(1, true)], [(2, true)], [(0, true), (1, false)]]

private theorem satCNF_eval_allTrue : satCNF.eval (fun _ => true) = true := by
  decide

theorem satCNF_has_two_nash :
    ∃ x₁ y₁ x₂ y₂,
      (gilboaZemelGame 3 satCNF).IsNash x₁ y₁ ∧
      (gilboaZemelGame 3 satCNF).IsNash x₂ y₂ ∧
      (x₁, y₁) ≠ (x₂, y₂) := by
  refine ⟨Pi.single .default 1, Pi.single .default 1,
    gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    (isNash_gilboaZemelGame_iff (by decide) satCNF).2 (Or.inl ⟨rfl, rfl⟩),
    (isNash_gilboaZemelGame_iff (by decide) satCNF).2
      (Or.inr ⟨fun _ => true, satCNF_eval_allTrue, rfl, rfl⟩), ?_⟩
  intro heq
  have h0 := congrFun (Prod.mk.inj heq).1 .default
  simp at h0

theorem satCNF_nash_payoff_ge_two :
    ∃ x y, (gilboaZemelGame 3 satCNF).IsNash x y ∧
      (2 : ℝ) ≤ (gilboaZemelGame 3 satCNF).payoff₁ x y := by
  refine ⟨gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    (isNash_gilboaZemelGame_iff (by decide) satCNF).2
      (Or.inr ⟨fun _ => true, satCNF_eval_allTrue, rfl, rfl⟩), ?_⟩
  rw [payoff₁_gilboaZemelGame_assignment (by decide)]
  norm_num

theorem satCNF_nash_total_payoff_ge_four :
    ∃ x y, (gilboaZemelGame 3 satCNF).IsNash x y ∧
      (4 : ℝ) ≤
        (gilboaZemelGame 3 satCNF).payoff₁ x y + (gilboaZemelGame 3 satCNF).payoff₂ x y := by
  refine ⟨gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    (isNash_gilboaZemelGame_iff (by decide) satCNF).2
      (Or.inr ⟨fun _ => true, satCNF_eval_allTrue, rfl, rfl⟩), ?_⟩
  rw [(isSymmetric_gilboaZemelGame 3 satCNF).payoff₂_eq,
    payoff₁_gilboaZemelGame_assignment (by decide)]
  norm_num

theorem satCNF_nash_support_gt_one :
    ∃ x y, (gilboaZemelGame 3 satCNF).IsNash x y ∧ 1 < (Function.support x).ncard := by
  refine ⟨gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    (isNash_gilboaZemelGame_iff (by decide) satCNF).2
      (Or.inr ⟨fun _ => true, satCNF_eval_allTrue, rfl, rfl⟩), ?_⟩
  rw [ncard_support_gilboaZemelAssignmentStrategy (by decide)]
  decide

theorem satCNF_nash_support_contains_lit0 :
    ∃ x y, (gilboaZemelGame 3 satCNF).IsNash x y ∧ 0 < x (.lit 0 true) := by
  refine ⟨gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    (isNash_gilboaZemelGame_iff (by decide) satCNF).2
      (Or.inr ⟨fun _ => true, satCNF_eval_allTrue, rfl, rfl⟩), ?_⟩
  simp

theorem satCNF_nash_support_omits_default :
    ∃ x y, (gilboaZemelGame 3 satCNF).IsNash x y ∧ x .default = 0 := by
  refine ⟨gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    gilboaZemelAssignmentStrategy satCNF.length (fun _ => true),
    (isNash_gilboaZemelGame_iff (by decide) satCNF).2
      (Or.inr ⟨fun _ => true, satCNF_eval_allTrue, rfl, rfl⟩), ?_⟩
  simp

/-! ### Unsatisfiable CNF witness on `Fin 3` -/

/-- Unsatisfiable CNF formula `(x₀) ∧ (¬x₀)` on `Fin 3`. -/
def unsatCNF : CNF (Fin 3) :=
  [[(0, true)], [(0, false)]]

private theorem unsatCNF_not_eval (α : Fin 3 → Bool) : unsatCNF.eval α ≠ true := by
  intro h
  simp only [unsatCNF, CNF.eval_cons, CNF.eval_nil, Bool.and_true, Bool.and_eq_true,
    Clause.eval_cons, Clause.eval_nil, Bool.or_false, Literal.eval_eq_true_iff] at h
  rw [h.1] at h
  exact absurd h.2 (by decide)

theorem unsatCNF_unique_nash {x y : GilboaZemelStrategy 3 unsatCNF.length → ℝ}
    (hNash : (gilboaZemelGame 3 unsatCNF).IsNash x y) :
    x = Pi.single .default 1 ∧ y = Pi.single .default 1 := by
  rcases (isNash_gilboaZemelGame_iff (by decide) unsatCNF).1 hNash with h | ⟨α, hα, -, -⟩
  · exact h
  · exact absurd hα (unsatCNF_not_eval α)

theorem unsatCNF_not_two_nash :
    ¬ ∃ x₁ y₁ x₂ y₂,
      (gilboaZemelGame 3 unsatCNF).IsNash x₁ y₁ ∧
      (gilboaZemelGame 3 unsatCNF).IsNash x₂ y₂ ∧
      (x₁, y₁) ≠ (x₂, y₂) := by
  rintro ⟨x₁, y₁, x₂, y₂, h₁, h₂, hne⟩
  obtain ⟨rfl, rfl⟩ := unsatCNF_unique_nash h₁
  obtain ⟨rfl, rfl⟩ := unsatCNF_unique_nash h₂
  exact hne rfl

theorem unsatCNF_not_payoff_ge_two :
    ¬ ∃ x y, (gilboaZemelGame 3 unsatCNF).IsNash x y ∧
      (2 : ℝ) ≤ (gilboaZemelGame 3 unsatCNF).payoff₁ x y := by
  rintro ⟨x, y, hNash, hpay⟩
  obtain ⟨rfl, rfl⟩ := unsatCNF_unique_nash hNash
  rw [payoff₁_gilboaZemelGame_default] at hpay
  norm_num at hpay

theorem unsatCNF_not_total_payoff_ge_four :
    ¬ ∃ x y, (gilboaZemelGame 3 unsatCNF).IsNash x y ∧
      (4 : ℝ) ≤
        (gilboaZemelGame 3 unsatCNF).payoff₁ x y + (gilboaZemelGame 3 unsatCNF).payoff₂ x y := by
  rintro ⟨x, y, hNash, hpay⟩
  obtain ⟨rfl, rfl⟩ := unsatCNF_unique_nash hNash
  rw [(isSymmetric_gilboaZemelGame 3 unsatCNF).payoff₂_eq,
    payoff₁_gilboaZemelGame_default] at hpay
  norm_num at hpay

theorem unsatCNF_not_support_gt_one :
    ¬ ∃ x y, (gilboaZemelGame 3 unsatCNF).IsNash x y ∧ 1 < (Function.support x).ncard := by
  rintro ⟨x, y, hNash, hsupp⟩
  obtain ⟨rfl, rfl⟩ := unsatCNF_unique_nash hNash
  have hsing :
      Function.support (Pi.single (.default : GilboaZemelStrategy 3 unsatCNF.length) (1 : ℝ)) =
        {.default} := by
    ext s; by_cases hs : s = .default <;> simp [hs]
  rw [hsing, Set.ncard_singleton] at hsupp
  omega

theorem unsatCNF_not_support_contains_lit0 :
    ¬ ∃ x y, (gilboaZemelGame 3 unsatCNF).IsNash x y ∧ 0 < x (.lit 0 true) := by
  rintro ⟨x, y, hNash, hpos⟩
  obtain ⟨rfl, rfl⟩ := unsatCNF_unique_nash hNash
  simp at hpos

theorem unsatCNF_not_support_omits_default :
    ¬ ∃ x y, (gilboaZemelGame 3 unsatCNF).IsNash x y ∧ x .default = 0 := by
  rintro ⟨x, y, hNash, h0⟩
  obtain ⟨rfl, rfl⟩ := unsatCNF_unique_nash hNash
  simp at h0

/-! ### Edge cases and `N = 1`, `N = 2` boundaries of `gilboaZemelGame` -/

theorem emptyCNF_has_assignment_nash :
    (gilboaZemelGame 3 ([] : CNF (Fin 3))).IsNash
      (gilboaZemelAssignmentStrategy 0 (fun _ => false))
      (gilboaZemelAssignmentStrategy 0 (fun _ => false)) :=
  (isNash_gilboaZemelGame_iff (by decide) ([] : CNF (Fin 3))).2
    (Or.inr ⟨fun _ => false, rfl, rfl, rfl⟩)

theorem emptyClauseCNF_unique_nash
    {x y : GilboaZemelStrategy 3 ([[]] : CNF (Fin 3)).length → ℝ}
    (hNash : (gilboaZemelGame 3 ([[]] : CNF (Fin 3))).IsNash x y) :
    x = Pi.single .default 1 ∧ y = Pi.single .default 1 := by
  rcases (isNash_gilboaZemelGame_iff (by decide) ([[]] : CNF (Fin 3))).1 hNash with
    h | ⟨α, hα, -, -⟩
  · exact h
  · simp at hα

/-- At `N = 2`, `isNash_gilboaZemelGame_iff` holds, and assignment equilibria earn payoff `1`,
matching `(default, default)` (confirming why `N ≥ 3` is used for payoff separation). -/
theorem boundary_N2_assignment_nash_payoff_one :
    let φ : CNF (Fin 2) := [[(0, true)]]
    let x := gilboaZemelAssignmentStrategy φ.length (fun _ => true)
    (gilboaZemelGame 2 φ).IsNash x x ∧ (gilboaZemelGame 2 φ).payoff₁ x x = 1 := by
  refine ⟨(isNash_gilboaZemelGame_iff (by decide) [[(0, true)]]).2
      (Or.inr ⟨fun _ => true, by decide, rfl, rfl⟩), ?_⟩
  rw [payoff₁_gilboaZemelGame_assignment (by decide)]
  norm_num

/-- At `N = 1`, `gilboaZemelAssignmentStrategy` earns `0 < 1 = payoff₁ default`, so it is NOT a
Nash equilibrium (confirming `2 ≤ N` cannot be dropped from `isNash_gilboaZemelGame_iff`). -/
theorem boundary_N1_assignment_not_nash :
    let φ : CNF (Fin 1) := []
    let x := gilboaZemelAssignmentStrategy φ.length (fun _ => true)
    ¬ (gilboaZemelGame 1 φ).IsNash x x := by
  intro φ x hNash
  have hle := (isNash_iff.1 hNash).1.le_payoff₁ .default
  rw [payoff₁_gilboaZemelGame_assignment (by decide)] at hle
  have hmix : IsMixedStrategy x :=
    isMixedStrategy_gilboaZemelAssignmentStrategy (by decide) φ.length (fun _ => true)
  have hdef : ((gilboaZemelGame 1 φ).A *ᵥ x) .default = 1 := by
    simp only [mulVec, dotProduct, gilboaZemelGame_A_default, one_mul, hmix.sum_eq_one]
  rw [hdef] at hle
  norm_num at hle

/-! ### Concrete `BimatrixCode` decision-problem witnesses and boundaries -/

/-- Pure-coordination symmetric game `[[2, 0], [0, 2]]`. -/
def coordCode : BimatrixCode :=
  ⟨[[2, 0], [0, 2]], [[2, 0], [0, 2]]⟩

/-- Strict-dominance symmetric game `matA = [[1, 1], [0, 0]]`, `matB = matAᵀ = [[1, 0], [1, 0]]`
(with `matA ≠ matAᵀ`, exercising the `matB = matAᵀ` transpose convention). -/
def domCode : BimatrixCode :=
  ⟨[[1, 1], [0, 0]], [[1, 0], [1, 0]]⟩

/-- Asymmetric game (`matB ≠ matAᵀ`) whose player-1 matrix matches `coordCode`. -/
def asymCode : BimatrixCode :=
  ⟨[[2, 0], [0, 2]], [[0, 1], [0, 0]]⟩

theorem coordCode_isSymmetric : coordCode.IsSymmetric := by
  refine ⟨⟨by decide, by decide, rfl, ?_, ?_⟩, rfl, fun i j => ?_⟩
  · intro r hr; simp only [coordCode, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · intro r hr; simp only [coordCode, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · fin_cases i <;> fin_cases j <;> rfl

theorem domCode_isSymmetric : domCode.IsSymmetric := by
  refine ⟨⟨by decide, by decide, rfl, ?_, ?_⟩, rfl, fun i j => ?_⟩
  · intro r hr; simp only [domCode, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · intro r hr; simp only [domCode, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · fin_cases i <;> fin_cases j <;> rfl

private theorem sum_fin_coord (f : Fin coordCode.rows → ℝ) :
    ∑ i : Fin coordCode.rows, f i = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ :=
  Fin.sum_univ_two f

private theorem sum_fin_dom (f : Fin domCode.rows → ℝ) :
    ∑ i : Fin domCode.rows, f i = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ :=
  Fin.sum_univ_two f

private theorem coordCode_pure0_isNash :
    coordCode.toSymGame.IsNash (Pi.single ⟨0, by decide⟩ 1) (Pi.single ⟨0, by decide⟩ 1) := by
  have hsym : coordCode.toSymGame.IsSymmetric := rfl
  rw [← IsSymmetricNash, hsym.isSymmetricNash_iff]
  refine ⟨isMixedStrategy_single _, fun i => ?_⟩
  rw [payoff₁_eq_dotProduct]
  fin_cases i <;>
    (simp only [dotProduct, mulVec, sum_fin_coord]; norm_num [toSymGame, coordCode])

private theorem coordCode_pure1_isNash :
    coordCode.toSymGame.IsNash (Pi.single ⟨1, by decide⟩ 1) (Pi.single ⟨1, by decide⟩ 1) := by
  have hsym : coordCode.toSymGame.IsSymmetric := rfl
  rw [← IsSymmetricNash, hsym.isSymmetricNash_iff]
  refine ⟨isMixedStrategy_single _, fun i => ?_⟩
  rw [payoff₁_eq_dotProduct]
  fin_cases i <;>
    (simp only [dotProduct, mulVec, sum_fin_coord]; norm_num [toSymGame, coordCode])

private theorem coordCode_half_isNash :
    coordCode.toSymGame.IsNash (fun _ => 1 / 2) (fun _ => 1 / 2) := by
  have hsym : coordCode.toSymGame.IsSymmetric := rfl
  rw [← IsSymmetricNash, hsym.isSymmetricNash_iff]
  refine ⟨isMixedStrategy_iff.2 ⟨fun _ => by norm_num, by rw [sum_fin_coord]; norm_num⟩,
    fun i => ?_⟩
  rw [payoff₁_eq_dotProduct]
  fin_cases i <;>
    (simp only [dotProduct, mulVec, sum_fin_coord]; norm_num [toSymGame, coordCode])

theorem coordCode_mem_all_six :
    coordCode ∈ SymGameHasTwoNash ∧
      (⟨coordCode, 2⟩ : BimatrixThresholdInstance) ∈ SymGameHasNashPayoffGe ∧
      (⟨coordCode, 4⟩ : BimatrixThresholdInstance) ∈ SymGameHasNashTotalPayoffGe ∧
      (⟨coordCode, 1⟩ : BimatrixSupportBoundInstance) ∈ SymGameHasNashSupportGt ∧
      (⟨coordCode, 0⟩ : BimatrixStrategyIndexInstance) ∈ SymGameHasNashSupportContains ∧
      (⟨coordCode, 0⟩ : BimatrixStrategyIndexInstance) ∈ SymGameHasNashSupportOmits := by
  have hsym : coordCode.toSymGame.IsSymmetric := rfl
  have hpay0 : coordCode.toSymGame.payoff₁
      (Pi.single ⟨0, by decide⟩ 1) (Pi.single ⟨0, by decide⟩ 1) = 2 := by
    rw [payoff₁_eq_dotProduct]
    simp only [dotProduct, mulVec, sum_fin_coord]
    norm_num [toSymGame, coordCode]
  refine ⟨⟨coordCode_isSymmetric, _, _, _, _, coordCode_pure0_isNash, coordCode_pure1_isNash, ?_⟩,
    ⟨coordCode_isSymmetric, _, _, coordCode_pure0_isNash, by rw [hpay0]; norm_num⟩,
    ⟨coordCode_isSymmetric, _, _, coordCode_pure0_isNash, by
      rw [hsym.payoff₂_eq, hpay0]; norm_num⟩,
    ⟨coordCode_isSymmetric, _, _, coordCode_half_isNash, ?_⟩,
    ⟨coordCode_isSymmetric, by decide, _, _, coordCode_pure0_isNash, by simp⟩,
    ⟨coordCode_isSymmetric, by decide, _, _, coordCode_pure1_isNash, by simp⟩⟩
  · intro heq
    have h0 := congrFun (Prod.mk.inj heq).1 ⟨0, by decide⟩
    simp at h0
  · have hsupp : Function.support (fun _ : Fin coordCode.rows => (1 / 2 : ℝ)) = Set.univ := by
      ext i; simp
    rw [hsupp, Set.ncard_univ, Nat.card_fin]
    decide

private theorem domCode_unique_nash {x y : Fin domCode.rows → ℝ}
    (hNash : domCode.toSymGame.IsNash x y) :
    x = Pi.single ⟨0, by decide⟩ 1 ∧ y = Pi.single ⟨0, by decide⟩ 1 := by
  have hsym : domCode.toSymGame.IsSymmetric := rfl
  have hbr₁ := (isNash_iff.1 hNash).1
  have hbr₂ := hsym.isBestResponse₂_iff_isBestResponse₁.1 (isNash_iff.1 hNash).2
  have hdom {u v : Fin domCode.rows → ℝ} (hbr : domCode.toSymGame.IsBestResponse₁ u v)
      (hv : IsMixedStrategy v) : u = Pi.single ⟨0, by decide⟩ 1 := by
    have h0 : (domCode.toSymGame.A *ᵥ v) ⟨0, by decide⟩ = 1 := by
      have hsum := hv.sum_eq_one
      rw [sum_fin_dom] at hsum
      simp only [mulVec, dotProduct, sum_fin_dom]
      have ha0 : domCode.toSymGame.A ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := by
        norm_num [toSymGame, domCode]
      have ha1 : domCode.toSymGame.A ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 := by
        norm_num [toSymGame, domCode]
      rw [ha0, ha1, one_mul, one_mul, hsum]
    have h1 : (domCode.toSymGame.A *ᵥ v) ⟨1, by decide⟩ = 0 := by
      simp only [mulVec, dotProduct, sum_fin_dom]
      have ha0 : domCode.toSymGame.A ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := by
        norm_num [toSymGame, domCode]
      have ha1 : domCode.toSymGame.A ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := by
        norm_num [toSymGame, domCode]
      rw [ha0, ha1, zero_mul, zero_mul, add_zero]
    have hu1 : u ⟨1, by decide⟩ = 0 := by
      by_contra hne
      have hpos : 0 < u ⟨1, by decide⟩ :=
        lt_of_le_of_ne (hbr.isMixedStrategy.nonneg _) (Ne.symm hne)
      have hopt := isPureBestResponse₁_iff.1 ((isBestResponse₁_iff.1 hbr).2 _ hpos) ⟨0, by decide⟩
      linarith
    have hsum := hbr.isMixedStrategy.sum_eq_one
    rw [sum_fin_dom] at hsum
    funext i
    fin_cases i
    · have h0 :
          Pi.single (M := fun _ : Fin domCode.rows => ℝ) ⟨0, by decide⟩ 1 ⟨0, by decide⟩ = 1 :=
        Pi.single_eq_same _ _
      change u ⟨0, by decide⟩ =
        Pi.single (M := fun _ : Fin domCode.rows => ℝ) ⟨0, by decide⟩ 1 ⟨0, by decide⟩
      linarith
    · have h1 :
          Pi.single (M := fun _ : Fin domCode.rows => ℝ) ⟨0, by decide⟩ 1 ⟨1, by decide⟩ = 0 :=
        Pi.single_eq_of_ne (by decide) _
      change u ⟨1, by decide⟩ =
        Pi.single (M := fun _ : Fin domCode.rows => ℝ) ⟨0, by decide⟩ 1 ⟨1, by decide⟩
      linarith
  exact ⟨hdom hbr₁ hbr₂.isMixedStrategy, hdom hbr₂ hbr₁.isMixedStrategy⟩

theorem domCode_notMem_all_six :
    domCode ∉ SymGameHasTwoNash ∧
      (⟨domCode, 2⟩ : BimatrixThresholdInstance) ∉ SymGameHasNashPayoffGe ∧
      (⟨domCode, 3⟩ : BimatrixThresholdInstance) ∉ SymGameHasNashTotalPayoffGe ∧
      (⟨domCode, 1⟩ : BimatrixSupportBoundInstance) ∉ SymGameHasNashSupportGt ∧
      (⟨domCode, 1⟩ : BimatrixStrategyIndexInstance) ∉ SymGameHasNashSupportContains ∧
      (⟨domCode, 0⟩ : BimatrixStrategyIndexInstance) ∉ SymGameHasNashSupportOmits := by
  have hsym : domCode.toSymGame.IsSymmetric := rfl
  have hpay : domCode.toSymGame.payoff₁
      (Pi.single ⟨0, by decide⟩ 1) (Pi.single ⟨0, by decide⟩ 1) = 1 := by
    rw [payoff₁_eq_dotProduct]
    simp only [dotProduct, mulVec, sum_fin_dom]
    norm_num [toSymGame, domCode]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨-, x₁, y₁, x₂, y₂, h₁, h₂, hne⟩
    obtain ⟨rfl, rfl⟩ := domCode_unique_nash h₁
    obtain ⟨rfl, rfl⟩ := domCode_unique_nash h₂
    exact hne rfl
  · rintro ⟨-, x, y, hNash, hge⟩
    obtain ⟨rfl, rfl⟩ := domCode_unique_nash hNash
    rw [hpay] at hge; norm_num at hge
  · rintro ⟨-, x, y, hNash, hge⟩
    obtain ⟨rfl, rfl⟩ := domCode_unique_nash hNash
    rw [hsym.payoff₂_eq, hpay] at hge; norm_num at hge
  · rintro ⟨-, x, y, hNash, hgt⟩
    obtain ⟨rfl, rfl⟩ := domCode_unique_nash hNash
    have hsing :
        Function.support (Pi.single (⟨0, by decide⟩ : Fin domCode.rows) (1 : ℝ)) =
          {⟨0, by decide⟩} := by
      ext s; by_cases hs : s = ⟨0, by decide⟩ <;> simp [hs]
    rw [hsing, Set.ncard_singleton] at hgt
    dsimp only at hgt
    omega
  · rintro ⟨-, ⟨hs, x, y, hNash, hpos⟩⟩
    obtain ⟨rfl, rfl⟩ := domCode_unique_nash hNash
    simp at hpos
  · rintro ⟨-, ⟨hs, x, y, hNash, h0⟩⟩
    obtain ⟨rfl, rfl⟩ := domCode_unique_nash hNash
    simp at h0

/-- Symmetry boundary: an asymmetric bimatrix game (`matB ≠ matAᵀ`) is rejected from
`SymGameHasTwoNash` even though its `toSymGame` has multiple equilibria. -/
theorem asymCode_notMem_SymGameHasTwoNash : asymCode ∉ SymGameHasTwoNash := by
  rintro ⟨⟨-, -, hsym⟩, -⟩
  have h01 := hsym ⟨0, by decide⟩ ⟨1, by decide⟩
  norm_num [asymCode] at h01

/-- Strategy-index boundary: an out-of-range index `strategy ≥ game.rows` is rejected from both
`SymGameHasNashSupportContains` and `SymGameHasNashSupportOmits`. -/
theorem coordCode_oob_strategy_rejected :
    (⟨coordCode, 2⟩ : BimatrixStrategyIndexInstance) ∉ SymGameHasNashSupportContains ∧
      (⟨coordCode, 2⟩ : BimatrixStrategyIndexInstance) ∉ SymGameHasNashSupportOmits := by
  constructor
  · rintro ⟨-, hs, -⟩; simp [coordCode, rows] at hs
  · rintro ⟨-, hs, -⟩; simp [coordCode, rows] at hs

/-! ### Client access to all six NP-hardness headlines (Theorem 2.3, p. 33) -/

theorem client_SymGameHasTwoNash_npHard : NPHard encBimatrix SymGameHasTwoNash :=
  SymGameHasTwoNash_npHard

theorem client_SymGameHasNashPayoffGe_npHard :
    NPHard encBimatrixThresholdInstance SymGameHasNashPayoffGe :=
  SymGameHasNashPayoffGe_npHard

theorem client_SymGameHasNashTotalPayoffGe_npHard :
    NPHard encBimatrixThresholdInstance SymGameHasNashTotalPayoffGe :=
  SymGameHasNashTotalPayoffGe_npHard

theorem client_SymGameHasNashSupportGt_npHard :
    NPHard encBimatrixSupportBoundInstance SymGameHasNashSupportGt :=
  SymGameHasNashSupportGt_npHard

theorem client_SymGameHasNashSupportContains_npHard :
    NPHard encBimatrixStrategyIndexInstance SymGameHasNashSupportContains :=
  SymGameHasNashSupportContains_npHard

theorem client_SymGameHasNashSupportOmits_npHard :
    NPHard encBimatrixStrategyIndexInstance SymGameHasNashSupportOmits :=
  SymGameHasNashSupportOmits_npHard

end CslibFrontierTests.GameTheory.BimatrixNashHardness
