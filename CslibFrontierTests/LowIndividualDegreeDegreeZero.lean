/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.InductionBase
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.Soundness
import Mathlib.Algebra.Field.ZMod

/-! # Degree-zero extraction from honest strategies -/

set_option linter.privateModule false

open Cslib.PCP Cslib.PCP.LowIndividualDegree Cslib.Quantum Matrix
open scoped BigOperators MatrixOrder ComplexOrder

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def constantPoly : MvPolynomial (Fin 2) (ZMod 3) := MvPolynomial.C 2

private noncomputable def strategy :
    QuantumStrategy (Question (ZMod 3) 2) (Question (ZMod 3) 2)
      (Answer (ZMod 3) 2) (Answer (ZMod 3) 2) (Fin 1) (Fin 1) := by
  classical
  exact QuantumStrategy.ofDeterministic (honest constantPoly) (honest constantPoly)

private theorem strategy_projective (q : Question (ZMod 3) 2) :
    (strategy.alice q).toMeasurement.IsProjective := by
  classical
  intro a
  unfold strategy
  simp only [QuantumStrategy.ofDeterministic, POVM.toMeasurement_effect, POVM.const]
  split_ifs <;> simp

private theorem strategy_branch_score (b : Branch) :
    (branchGame (F := ZMod 3) 1 0 b).commutingWinProb strategy.toCommuting = 1 := by
  classical
  rw [TwoProverGame.commutingWinProb_toCommuting]
  unfold strategy
  rw [TwoProverGame.quantumWinProb_ofDeterministic]
  exact winProb_branch_honest constantPoly
    (fun i => (MvPolynomial.degreeOf_C (2 : ZMod 3) i).le) b

/-- The constant-polynomial strategy has zero axis and consistency loss, and the
extracted local measurement matches the honest point answers with mass at least one. -/
example :
    ∃ G : POVM (Option (BoundedPolynomial (ZMod 3) 2 0)) (Fin 1),
      1 ≤ 𝔼 u : Point (ZMod 3) 2, ∑ g : BoundedPolynomial (ZMod 3) 2 0,
        (strategy.toCommuting.state
          ((QuantumStrategy.rightMeasurement (ι := Fin 1) G).effect (some g) *
            (decodedPoint strategy.toCommuting.alice u).effect
              (MvPolynomial.eval u g.val))).re := by
  have hBob : strategy.bob = strategy.alice := rfl
  obtain ⟨G, hG⟩ :=
    exists_degree_zero_polynomial_POVM strategy (fun u => strategy_projective (.point u)) (by
      rw [hBob]
      exact fun u => strategy_projective (.point u))
  refine ⟨G, ?_⟩
  have hAxis := strategy_branch_score .axis
  have hCons := strategy_branch_score .consistency
  rw [hAxis, hCons] at hG
  simpa only [sub_self, mul_zero, add_zero, sub_zero] using hG

private theorem strategy_score : (game (F := ZMod 3) 1 0).quantumWinProb strategy = 1 := by
  rw [← TwoProverGame.commutingWinProb_toCommuting (game 1 0)]
  change (game (F := ZMod 3) 1 0).answersWinProb strategy.toCommuting.answers = 1
  rw [answersWinProb_game]
  change ((branchGame (F := ZMod 3) 1 0 .axis).commutingWinProb strategy.toCommuting +
    (branchGame (F := ZMod 3) 1 0 .consistency).commutingWinProb strategy.toCommuting +
    (branchGame (F := ZMod 3) 1 0 .diagonal).commutingWinProb strategy.toCommuting) / 3 = 1
  rw [strategy_branch_score .axis, strategy_branch_score .consistency,
    strategy_branch_score .diagonal]
  norm_num

private theorem soundnessErrors_polynomial_at_zero :
    (soundnessErrors 2 (10 ^ 30) 0 0).polynomial ≤ 1 / 2 := by
  conv_lhs =>
    norm_num [soundnessErrors, dimensionInductionError, inductionLossTerm, Real.zero_rpow,
      -Real.sqrt_mul, -Real.sqrt_mul']
  let x : ℝ := 3125000000000000000000000
  let σ := 320000 * (4 * Real.exp (-x))
  let ζ := σ + Real.sqrt (4 * σ)
  change ζ + 2 * Real.sqrt (18 * ζ) ≤ 1 / 2
  have he : Real.exp (-x) ≤ 1 / (x + 1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by dsimp [x]; positivity) (Real.add_one_le_exp x)
  have hσ : σ ≤ 1 / 1000000000000 := by
    calc
      _ ≤ 320000 * (4 * (1 / (x + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by norm_num)) (by norm_num)
      _ ≤ _ := by norm_num [x]
  have hroot : Real.sqrt (4 * σ) ≤ 1 / 250000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith only [hσ]
  have hζ : ζ ≤ 1 / 200000 := by
    dsimp only [ζ]
    linarith only [hσ, hroot]
  have hroot' : Real.sqrt (18 * ζ) ≤ 1 / 100 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith only [hζ]
  linarith only [hζ, hroot']

/-- The honest two-coordinate strategy supplies projective polynomial
measurements that agree with probability at least one half. -/
example :
    ∃ (P Q : POVM (BoundedPolynomial (ZMod 3) 2 0) (Fin 1)),
      P.toMeasurement.IsProjective ∧ Q.toMeasurement.IsProjective ∧
      1 / 2 ≤ Measurement.agreement strategy.toCommuting.state
        (QuantumStrategy.leftMeasurement (κ := Fin 1) P)
        (QuantumStrategy.rightMeasurement (ι := Fin 1) Q) := by
  have hBob : strategy.bob = strategy.alice := rfl
  obtain ⟨P, Q, hP, hQ, _, _, hpair⟩ :=
    exists_projective_polynomial_POVMs_of_winProb (k := 10 ^ 30) (n := 1) (d := 0)
      (by simp) strategy strategy_projective (by rw [hBob]; exact strategy_projective)
  simp only [strategy_score, sub_self, Nat.cast_zero, zero_div, Nat.cast_one,
    one_add_one_eq_two] at hpair
  have h := hpair.trans soundnessErrors_polynomial_at_zero
  exact ⟨P, Q, hP, hQ, by linarith⟩

open scoped Kronecker

private noncomputable def weight {A : Type*} [DecidableEq A] (a b x : A) (i : Bool) : ℝ :=
  if i then ((if x = a then 1 else 0) + (if x = b then 1 else 0)) / 2
  else if x = a then 1 else 0

private noncomputable def enlargedPOVM {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A) : POVM A Bool where
  effect x := Matrix.diagonal (fun i => (weight a b x i : ℂ))
  posSemidef x := Matrix.posSemidef_diagonal_iff.mpr fun i => Complex.zero_le_real.mpr (by
    unfold weight
    split_ifs <;> norm_num)
  sum_effect := by
    have hw (i : Bool) : (∑ x, weight a b x i) = 1 := by
      cases i
      · simp [weight, Finset.sum_ite_eq']
      · change (∑ x, (((if x = a then 1 else 0) + (if x = b then 1 else 0)) : ℝ) / 2) = 1
        rw [← Finset.sum_div, Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq']
    ext i j
    by_cases h : i = j
    · subst j
      simpa only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
        ← Complex.ofReal_sum, Complex.ofReal_one] using congrArg Complex.ofReal (hw i)
    · simp [Matrix.sum_apply, h]

private noncomputable def enlargedStrategy :
    QuantumStrategy (Question (ZMod 3) 2) (Question (ZMod 3) 2)
      (Answer (ZMod 3) 2) (Answer (ZMod 3) 2) Bool (Fin 1) := by
  classical
  exact {
    state := EuclideanSpace.single (false, 0) 1
    norm_state := by simp
    alice := fun q => enlargedPOVM (honest constantPoly q) (.inl 0)
    bob := strategy.bob }

private theorem enlarged_not_projective :
    ¬ (enlargedStrategy.alice (.point 0)).toMeasurement.IsProjective := by
  classical
  intro h
  have hm := congrArg (fun M : Matrix Bool Bool ℂ => M true true) (h (.inl 2))
  have hne : Sum.inl (2 : ZMod 3) ≠ (Sum.inl 0 : Answer (ZMod 3) 2) := by decide
  norm_num [enlargedStrategy, enlargedPOVM, POVM.toMeasurement_effect,
    weight, honest_point, constantPoly, hne] at hm

private theorem enlarged_answers (x y : Question (ZMod 3) 2) :
    enlargedStrategy.answers x y = strategy.answers x y := by
  classical
  unfold strategy
  rw [QuantumStrategy.answers_ofDeterministic]
  ext ⟨a, b⟩
  rw [QuantumStrategy.answers_apply, PMF.pure_apply]
  have he : (star enlargedStrategy.state.ofLp ⬝ᵥ
      (((enlargedStrategy.alice x).effect a ⊗ₖ (enlargedStrategy.bob y).effect b) *ᵥ
        enlargedStrategy.state.ofLp)).re =
        if a = honest constantPoly x ∧ b = honest constantPoly y then 1 else 0 := by
    let p : Bool × Fin 1 := (false, 0)
    have hstar : star (Pi.single (M := fun _ => ℂ) p 1) = Pi.single p 1 := by
      funext j
      by_cases hj : j = p <;> simp [hj]
    change (star (Pi.single (M := fun _ => ℂ) p 1) ⬝ᵥ
      (((enlargedStrategy.alice x).effect a ⊗ₖ (enlargedStrategy.bob y).effect b) *ᵥ
        Pi.single p 1)).re = _
    rw [hstar, single_dotProduct, Matrix.mulVec_single_one]
    by_cases hb : b = honest constantPoly y <;>
      simp [p, enlargedStrategy, enlargedPOVM, weight, strategy, QuantumStrategy.ofDeterministic,
        POVM.const, Matrix.col_apply, hb]
  rw [he]
  by_cases ha : a = honest constantPoly x <;> by_cases hb : b = honest constantPoly y <;>
    simp [ha, hb]

/-- A genuinely nonprojective finite tensor strategy has the honest score on
its supported basis coordinates. Soundness returns polynomial POVMs on the
original unequal local spaces with agreement at least one half. -/
example :
    ¬ (enlargedStrategy.alice (.point 0)).toMeasurement.IsProjective ∧
    ∃ (P : POVM (BoundedPolynomial (ZMod 3) 2 0) Bool)
      (Q : POVM (BoundedPolynomial (ZMod 3) 2 0) (Fin 1)),
      1 / 2 ≤ Measurement.agreement enlargedStrategy.toCommuting.state
        (QuantumStrategy.leftMeasurement (κ := Fin 1) P)
        (QuantumStrategy.rightMeasurement (ι := Bool) Q) := by
  refine ⟨enlarged_not_projective, ?_⟩
  have hs : (game (F := ZMod 3) 1 0).quantumWinProb enlargedStrategy = 1 := by
    rw [← strategy_score, TwoProverGame.quantumWinProb, TwoProverGame.quantumWinProb]
    congr 1
    exact funext fun x => funext (enlarged_answers x)
  obtain ⟨P, Q, _, _, hp⟩ := exists_polynomial_POVMs_of_winProb
    (k := 10 ^ 30) (n := 1) (d := 0) (by simp) enlargedStrategy
  simp only [hs, sub_self, Nat.cast_zero, zero_div, Nat.cast_one, one_add_one_eq_two] at hp
  have h := hp.trans soundnessErrors_polynomial_at_zero
  exact ⟨P, Q, by linarith⟩
