/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
import CslibFrontier.Computability.QueryComplexity.Degree
import CslibFrontier.Foundations.BooleanAnalysis.LowDegreeGranularity

/-!
# Granularity of the Fourier coefficients of decision trees

A decision tree of depth `d` computes functions of degree at most `d`
(`DecisionTree.comp_eval_mem_lowDegree`), so the granularity of low-degree functions
(`BitString.exists_fourierCoeff_eq_intCast_div_two_pow_of_mem_lowDegree`) applies. An
integer-valued function of the output of a decision tree of depth `d` has Fourier coefficients
that are integer multiples of `2 ^ (-d)`
(`DecisionTree.exists_fourierCoeff_eq_intCast_div_two_pow_depth`), and a Boolean function computed
by a tree of depth `d ≥ 1`, read as signs, has coefficients in `2 ^ (1 - d) ℤ`, while one computed
by a tree of depth `0` has integer coefficients
(`DecisionTree.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one`)
[O'Donnell, Section 3.2][ODonnell2014]. The depth is structural, so unreachable paths only weaken
the bound.

## Main results

* `Cslib.DecisionTree.exists_fourierCoeff_eq_intCast_div_two_pow_depth`: granularity for
  integer-valued functions of decision trees.
* `Cslib.DecisionTree.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one`:
  granularity for Boolean functions of decision trees.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.DecisionTree

open BitString

variable {ι β : Type*} [Fintype ι] [DecidableEq ι]

/-- **Granularity of decision trees**: the Fourier coefficients of an integer-valued function of
the output of a decision tree of depth `d` are integer multiples of `2 ^ (-d)`
[O'Donnell, Proposition 3.16, fourth item][ODonnell2014]. -/
theorem exists_fourierCoeff_eq_intCast_div_two_pow_depth (g : β → ℤ) (t : DecisionTree ι β)
    (S : Finset ι) : ∃ m : ℤ, fourierCoeff (fun x => (g (t.eval x) : ℝ)) S = m / 2 ^ t.depth :=
  exists_fourierCoeff_eq_intCast_div_two_pow_of_mem_lowDegree _
    (comp_eval_mem_lowDegree (fun b => (g b : ℝ)) t) S

/-- **Granularity of decision trees** for Boolean functions: a Boolean function of the output of
a decision tree of depth `d`, read as signs, has Fourier coefficients in `2 ^ (1 - d) ℤ` when
`d ≥ 1`, and integer coefficients when `d = 0` [O'Donnell, Section 3.2][ODonnell2014]. -/
theorem exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one (g : β → Bool)
    (t : DecisionTree ι β) (S : Finset ι) :
    ∃ m : ℤ, fourierCoeff (fun x => signVal (g (t.eval x))) S = m / 2 ^ (t.depth - 1) :=
  exists_fourierCoeff_signVal_eq_intCast_div_two_pow_of_mem_lowDegree _
    (comp_eval_mem_lowDegree (fun b => signVal (g b)) t) S

end Cslib.DecisionTree
