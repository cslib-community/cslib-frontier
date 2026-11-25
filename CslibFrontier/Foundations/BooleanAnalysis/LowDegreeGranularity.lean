/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
import CslibFrontier.Foundations.BooleanAnalysis.Degree
import CslibFrontier.Foundations.BooleanAnalysis.Mobius
import CslibFrontier.Foundations.BooleanAnalysis.Subcube
import Mathlib.Algebra.BigOperators.Field

/-!
# Granularity of low-degree functions

An integer-valued function on the cube of degree at most `k` has Fourier coefficients in
`2 ^ (-k) ℤ` (`BitString.exists_fourierCoeff_eq_intCast_div_two_pow_of_mem_lowDegree`): by Möbius
inversion it is an integer combination of the monomials `∏_{i ∈ T} xᵢ` of at most `k` coordinates
(`BitString.eq_sum_subsetMobius_smul_monomial`, `BitString.subsetMobius_eq_zero_of_mem_lowDegree`),
and the monomial of `T`, the indicator of a subcube of codimension `#T`, has coefficients
`± 2 ^ (-#T)` on the subsets of `T` and `0` elsewhere (`BitString.fourierCoeff_monomial`, from
`BitString.fourierCoeff_ite_forall_mem_eq`).
A Boolean function of degree at most `k`, read as signs, is `1 - 2 g` for the integer-valued `g`
reading it as bits, so its coefficients lie in `2 ^ (1 - k) ℤ` when `k ≥ 1` and in `ℤ` when `k = 0`
(`BitString.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree`)
[O'Donnell, Exercise 1.11(b)][ODonnell2014]. Decision trees of depth `k` compute functions of degree
at most `k`, so this gives their granularity
(`DecisionTree.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one`, in
`CslibFrontier.Computability.DecisionTree.Granularity`).

## Usage

Open `Cslib.BitString`. Degree is membership in `lowDegree ℝ ι k`; for an integer-valued `g`,
`exists_fourierCoeff_eq_intCast_div_two_pow_of_mem_lowDegree g hg S` gives an integer `z` with
coefficient `z / 2 ^ k` on `S`, and for a Boolean `f`,
`exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree f hf S` gives
`z / 2 ^ (k - 1)`. Every function is in `lowDegree ℝ ι (Fintype.card ι)` (`mem_lowDegree_self`),
and a function of the output of a decision tree of depth `d` is in `lowDegree ℝ ι d`
(`DecisionTree.comp_eval_mem_lowDegree`, in `CslibFrontier.Computability.QueryComplexity.Degree`).
The exact learner of `CslibFrontier.MachineLearning.UniformLearning.ExactLowDegree` rounds its
estimates to these multiples. Checked clients compute two coefficients of the monomial `x₀ x₁`,
apply the integer-valued lemma to the conjunction of two bits, on two and on four bits (through
`monomial_mem_lowDegree`), and apply the Boolean lemma to a decision tree of depth two on four bits
(through `DecisionTree.comp_eval_mem_lowDegree`), to every Boolean function of three bits and to a
constant, in
[`CslibFrontierTests/BooleanAnalysisExactLearning.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisExactLearning.lean).

## Main results

* `Cslib.BitString.fourierCoeff_monomial`: the Fourier coefficients of a monomial.
* `Cslib.BitString.exists_fourierCoeff_eq_intCast_div_two_pow_of_mem_lowDegree`: integer-valued
  functions of degree at most `k` are `2 ^ (-k)`-granular.
* `Cslib.BitString.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree`: Boolean
  functions of degree at most `k` are `2 ^ (1 - k)`-granular for `k ≥ 1` (integer coefficients when
  `k = 0`).

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Fourier coefficients of a monomial**: reading bits as `0` and `1`, the monomial
`∏_{i ∈ T} xᵢ`, the indicator of the subcube where the bits in `T` are `true`, has coefficient
`(-1) ^ #S / 2 ^ #T` on each subset `S` of `T` and `0` on every other set. -/
theorem fourierCoeff_monomial (T S : Finset ι) :
    fourierCoeff (monomial ℝ T) S = if S ⊆ T then (-1) ^ #S / 2 ^ #T else 0 := by
  rw [show monomial ℝ T = _ from funext (monomial_apply T)]
  convert fourierCoeff_ite_forall_mem_eq T (fun _ => true) S using 2
  · congr!
  · simp [chi]

/-- **Integer-valued functions of low degree are granular**: an integer-valued function of degree
at most `k` has Fourier coefficients in `2 ^ (-k) ℤ`, since its coefficients in the monomials are
integers, as in [O'Donnell, Exercise 1.9(c)][ODonnell2014] for Boolean functions. -/
theorem exists_fourierCoeff_eq_intCast_div_two_pow_of_mem_lowDegree (g : (ι → Bool) → ℤ) {k : ℕ}
    (hg : (fun x => (g x : ℝ)) ∈ lowDegree ℝ ι k) (S : Finset ι) :
    ∃ z : ℤ, fourierCoeff (fun x => (g x : ℝ)) S = z / 2 ^ k := by
  set c : Finset ι → ℤ := subsetMobius fun U => g fun i => decide (i ∈ U)
  have hcR (T : Finset ι) :
      subsetMobius (fun U => ((g fun i => decide (i ∈ U) : ℤ) : ℝ)) T = c T :=
    (map_subsetMobius (Int.castAddHom ℝ) _ T).symm
  have hc (T : Finset ι) (hT : k < #T) : c T = 0 := by
    exact_mod_cast (hcR T).symm.trans (subsetMobius_eq_zero_of_mem_lowDegree hg hT)
  refine ⟨∑ T, if S ⊆ T then c T * (-1) ^ #S * 2 ^ (k - #T) else 0, ?_⟩
  rw [eq_sum_subsetMobius_smul_monomial (fun x => (g x : ℝ)), ← fourierCoeffₗ_apply, map_sum,
    Int.cast_sum, sum_div]
  refine sum_congr rfl fun T _ => ?_
  simp only [map_smul, fourierCoeffₗ_apply, smul_eq_mul, hcR, fourierCoeff_monomial]
  by_cases hST : S ⊆ T
  · by_cases hT : #T ≤ k
    · simp only [hST, ite_true]
      push_cast
      rw [pow_sub₀ _ two_ne_zero hT]
      field_simp
    · simp [hc T (not_le.1 hT)]
  · simp [hST]

/-- **Boolean functions of low degree are granular** [O'Donnell, Exercise 1.11(b)][ODonnell2014]: a
Boolean function of degree at most `k`, read as signs, has Fourier coefficients in
`2 ^ (1 - k) ℤ` when `k ≥ 1`, and in `ℤ` when `k = 0`. -/
theorem exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree
    (f : (ι → Bool) → Bool) {k : ℕ} (hf : (fun x => signVal (f x)) ∈ lowDegree ℝ ι k)
    (S : Finset ι) : ∃ z : ℤ, fourierCoeff (fun x => signVal (f x)) S = z / 2 ^ (k - 1) := by
  have hmem : (fun x => ((bitVal ℤ (f x) : ℤ) : ℝ)) ∈ lowDegree ℝ ι k := by
    convert signVal_comp_mem_lowDegree_iff.1 hf using 2 with x
    cases f x <;> simp
  obtain ⟨z, hz⟩ := exists_fourierCoeff_eq_intCast_div_two_pow_of_mem_lowDegree _ hmem S
  have hsign : (fun x => signVal (f x)) = fun x => 1 - 2 * ((bitVal ℤ (f x) : ℤ) : ℝ) :=
    funext fun x => by cases f x <;> norm_num
  rw [hsign, fourierCoeff_sub, fourierCoeff_const, fourierCoeff_const_mul, hz]
  rcases k with _ | k
  · exact ⟨(if S = ∅ then 1 else 0) - 2 * z, by split_ifs <;> push_cast <;> ring⟩
  · refine ⟨(if S = ∅ then 2 ^ k else 0) - z, ?_⟩
    rw [Nat.add_sub_cancel, pow_succ]
    split_ifs <;> push_cast <;> field_simp
    ring

end Cslib.BitString
