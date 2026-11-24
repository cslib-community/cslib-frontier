/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeGranularity
public import CslibFrontier.MachineLearning.UniformLearning.ExactLowDegree
import CslibFrontier.Computability.QueryComplexity.Degree
import CslibFrontier.Foundations.BooleanAnalysis.Degree

/-! # Tests for granularity and exact learning of low-degree functions

The monomial `x₀ x₁` has coefficient `1 / 4` on `∅` and `-1 / 4` on `{0}`. The conjunction of
two bits, read as `0` and `1`, has degree two, so its Fourier coefficients are multiples of
`1 / 4`, both on two bits and on four bits (where the bound for every function, degree four,
gives only `1 / 16`). A
decision tree of depth two on four bits computes a function of degree at most two, so its
coefficients, read as signs, are multiples of `1 / 2`. Every Boolean function of three bits has
degree at most three, so its coefficients, read as signs, are multiples of `1 / 4`, and a constant
has integer coefficients.
Over the two sets `∅` and `{0}`, `16` examples of a parity miss some coefficient by `1 / 2` with
probability at most `4 exp (-2)`. The two examples `(0, 0)` and `(1, 1)` of the one-bit dictator
give its coefficients exactly, so the exact hypothesis of degree one is the dictator; from the
three examples `(0, 0)`, `(0, 0)` and `(1, 1)` the estimate on `∅` is `1 / 3`, and rounding still
recovers the dictator. The functions
of degree at most two on five bits, among them every decision tree of depth at most two, are
learned with error `0` and confidence `9 / 10`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisExactLearning

open Cslib Cslib.BitString Cslib.MachineLearning Cslib.MachineLearning.UniformLearning
  Cslib.MachineLearning.PACLearning Cslib.Probability Finset

/-- The monomial `x₀ x₁` has coefficient `1 / 4` on `∅`. -/
example : fourierCoeff (monomial ℝ ({0, 1} : Finset (Fin 2))) ∅ = 1 / 4 := by
  rw [fourierCoeff_monomial]
  norm_num

/-- The monomial `x₀ x₁` has coefficient `-1 / 4` on `{0}`. -/
example : fourierCoeff (monomial ℝ ({0, 1} : Finset (Fin 2))) {0} = -1 / 4 := by
  rw [fourierCoeff_monomial]
  norm_num

/-- The conjunction of two bits, read as `0` and `1`, has coefficients in `(1 / 4) ℤ`. -/
example (S : Finset (Fin 2)) :
    ∃ z : ℤ, fourierCoeff (fun x : Fin 2 → Bool => ((if x 0 && x 1 then 1 else 0 : ℤ) : ℝ)) S =
      z / 4 := by
  obtain ⟨z, hz⟩ := exists_fourierCoeff_eq_intCast_div_two_pow_of_mem_lowDegree
    (fun x : Fin 2 → Bool => if x 0 && x 1 then 1 else 0) (mem_lowDegree_self _) S
  exact ⟨z, by rw [hz]; norm_num⟩

/-- The conjunction of the first two of four bits, read as `0` and `1`, is the monomial `x₀ x₁`
of degree two, so its coefficients lie in `(1 / 4) ℤ`, not only in `(1 / 16) ℤ`. -/
example (S : Finset (Fin 4)) :
    ∃ z : ℤ, fourierCoeff (fun x : Fin 4 → Bool => ((if x 0 && x 1 then 1 else 0 : ℤ) : ℝ)) S =
      z / 4 := by
  have hg : (fun x : Fin 4 → Bool => ((if x 0 && x 1 then 1 else 0 : ℤ) : ℝ)) =
      monomial ℝ ({0, 1} : Finset (Fin 4)) := by
    funext x
    rw [monomial_apply]
    cases h0 : x 0 <;> cases h1 : x 1 <;> simp [h0, h1]
  obtain ⟨z, hz⟩ := exists_fourierCoeff_eq_intCast_div_two_pow_of_mem_lowDegree
    (fun x : Fin 4 → Bool => if x 0 && x 1 then 1 else 0)
    (hg ▸ monomial_mem_lowDegree (D := 2) (by decide)) S
  exact ⟨z, by rw [hz]; norm_num⟩

/-- A decision tree of depth two on four bits: query `x₀`, then `x₁` or `x₂`. -/
abbrev depthTwoTree : DecisionTree (Fin 4) Bool :=
  .node 0 (.node 1 (.leaf false) (.leaf true)) (.node 2 (.leaf true) (.leaf false))

/-- The Boolean function computed by a decision tree of depth two on four bits has degree at most
two, so its coefficients, read as signs, lie in `(1 / 2) ℤ`. -/
example (S : Finset (Fin 4)) :
    ∃ z : ℤ, fourierCoeff (fun x => signVal (depthTwoTree.eval x)) S = z / 2 := by
  have hdepth : depthTwoTree.depth = 2 := by simp [DecisionTree.depth_node]
  obtain ⟨z, hz⟩ := exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree
    (fun x => depthTwoTree.eval x)
    (hdepth ▸ DecisionTree.comp_eval_mem_lowDegree (fun b => signVal b) depthTwoTree) S
  exact ⟨z, by rw [hz]; norm_num⟩

/-- Every Boolean function of three bits has Fourier coefficients in `(1 / 4) ℤ`. -/
example (f : (Fin 3 → Bool) → Bool) (S : Finset (Fin 3)) :
    ∃ z : ℤ, fourierCoeff (fun x => signVal (f x)) S = z / 4 := by
  obtain ⟨z, hz⟩ := exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree f
    (mem_lowDegree_self _) S
  exact ⟨z, by rw [hz]; norm_num⟩

/-- A constant function, of degree `0`, has integer Fourier coefficients. -/
example (S : Finset (Fin 3)) :
    ∃ z : ℤ, fourierCoeff (fun _ : Fin 3 → Bool => signVal true) S = z := by
  obtain ⟨z, hz⟩ := exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree
    (fun _ : Fin 3 → Bool => true) (const_mem_lowDegree 0 _) S
  exact ⟨z, by rw [hz]; norm_num⟩

/-- From `16` examples of the parity of two bits, some empirical coefficient on `∅` or `{0}` is
off by `1 / 2` with probability at most `4 exp (-2)`. -/
example : (PMF.uniformOfFintype (Fin 16 → Fin 2 → Bool)).toOuterMeasure
    {x | ∃ S ∈ ({∅, {0}} : Finset (Finset (Fin 2))), 1 / 2 ≤
      |empiricalCoeff (examples (fun x => x 0 ^^ x 1) x) S -
        fourierCoeff (fun x => signVal (x 0 ^^ x 1)) S|} ≤
      ENNReal.ofReal (4 * Real.exp (-2)) := by
  refine (uniform_exists_abs_empiricalCoeff_sub_ge_le _ _ (by norm_num)).trans_eq ?_
  norm_num
  ring_nf

/-- The two examples `(0, 0)` and `(1, 1)` of the dictator on one bit. -/
abbrev dictatorSample : LabeledSample (Fin 1 → Bool) Bool 2 :=
  ![(fun _ => false, false), (fun _ => true, true)]

/-- The examples `(0, 0)` and `(1, 1)` give the coefficients of the one-bit dictator exactly, so
the exact hypothesis of degree one is the dictator. -/
example : exactLowDegreeHypothesis 1 dictatorSample = fun x => x 0 := by
  have hchi : (fun x : Fin 1 → Bool => signVal (x 0)) = chi ℝ {0} :=
    funext fun x => (chi_singleton 0 x).symm
  refine exactLowDegreeHypothesis_eq le_rfl ?_ fun S _ => ?_
  · rw [hchi]
    exact chi_mem_lowDegree {0}
  · rw [hchi, fourierCoeff_chi]
    have hS : S = ∅ ∨ S = {0} := by
      rcases S.eq_empty_or_nonempty with h | ⟨i, hi⟩
      · exact Or.inl h
      · exact Or.inr (eq_singleton_iff_unique_mem.2 ⟨Subsingleton.elim i 0 ▸ hi,
          fun j _ => Subsingleton.elim j 0⟩)
    rcases hS with rfl | rfl <;>
      norm_num [empiricalCoeff, dictatorSample, Fin.sum_univ_two, chi_singleton]

/-- The three examples `(0, 0)`, `(0, 0)` and `(1, 1)` of the dictator on one bit. -/
abbrev unbalancedDictatorSample : LabeledSample (Fin 1 → Bool) Bool 3 :=
  ![(fun _ => false, false), (fun _ => false, false), (fun _ => true, true)]

/-- From the unbalanced examples `(0, 0)`, `(0, 0)` and `(1, 1)` the empirical coefficient of the
one-bit dictator on `∅` is `1 / 3`, not its true value `0`; rounding to the nearest integer
recovers `0`, so the exact hypothesis of degree one is still the dictator. -/
example : exactLowDegreeHypothesis 1 unbalancedDictatorSample = fun x => x 0 := by
  have hchi : (fun x : Fin 1 → Bool => signVal (x 0)) = chi ℝ {0} :=
    funext fun x => (chi_singleton 0 x).symm
  have hempty : empiricalCoeff unbalancedDictatorSample ∅ = 1 / 3 := by
    norm_num [empiricalCoeff, unbalancedDictatorSample, Fin.sum_univ_three]
  refine exactLowDegreeHypothesis_eq le_rfl ?_ fun S _ => ?_
  · rw [hchi]
    exact chi_mem_lowDegree {0}
  · rw [hchi, fourierCoeff_chi]
    have hS : S = ∅ ∨ S = {0} := by
      rcases S.eq_empty_or_nonempty with h | ⟨i, hi⟩
      · exact Or.inl h
      · exact Or.inr (eq_singleton_iff_unique_mem.2 ⟨Subsingleton.elim i 0 ▸ hi,
          fun j _ => Subsingleton.elim j 0⟩)
    rcases hS with rfl | rfl
    · rw [hempty]
      norm_num
    · norm_num [empiricalCoeff, unbalancedDictatorSample, Fin.sum_univ_three, chi_singleton]

/-- Exact learning of the functions of degree at most `2` on five bits, confidence `9 / 10`. -/
example : ∃ m, Learns (exactLowDegreeLearner (Fin 5) 2 m)
    {f | (fun x => signVal (f x)) ∈ lowDegree ℝ (Fin 5) 2} 0 (1 / 10) :=
  ⟨_, exactLowDegreeLearner_learns (by norm_num) (by norm_num) (Nat.le_ceil _)⟩

/-- Decision trees of depth at most `2` on five bits are learned with error `0` and confidence
`9 / 10`, since they compute functions of degree at most `2`. -/
example : ∃ m, Learns (exactLowDegreeLearner (Fin 5) 2 m)
    {f | ∃ t : DecisionTree (Fin 5) Bool, t.depth ≤ 2 ∧ f = t.eval} 0 (1 / 10) := by
  refine ⟨_, (exactLowDegreeLearner_learns (by norm_num) (by norm_num) (Nat.le_ceil _)).mono
    ?_ le_rfl le_rfl⟩
  rintro f ⟨t, ht, rfl⟩
  exact lowDegree_mono ht (DecisionTree.comp_eval_mem_lowDegree (fun b => signVal b) t)

end CslibFrontierTests.BooleanAnalysisExactLearning
