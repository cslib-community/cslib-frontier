/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, binomial series)

public import CslibFrontier.Init
public import Mathlib.RingTheory.Binomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Analytic.Binomial

/-!
# The real binomial series

For a real exponent `a` and `|x| < 1`, `(1 + x) ^ a = ∑_n C(a, n) x ^ n`, where `C(a, n)` is the
generalized binomial coefficient `Ring.choose a n`. Mathlib states this as the power series
`Real.one_add_rpow_hasFPowerSeriesOnBall_zero`; this file gives the summation form.

## Main results

* `Real.hasSum_choose_mul_pow`: the binomial series for real exponents.
-/

public section

namespace Real

/-- **The binomial series**: `(1 + x) ^ a = ∑_n C(a, n) x ^ n` for `|x| < 1`. -/
theorem hasSum_choose_mul_pow {a x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => Ring.choose a n * x ^ n) ((1 + x) ^ a) := by
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum (y := x)
    (by simpa [enorm_eq_nnnorm, ← NNReal.coe_lt_coe] using hx)
  simpa [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using h

end Real
