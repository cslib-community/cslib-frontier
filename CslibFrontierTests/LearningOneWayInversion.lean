/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.OneWayInversion
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Tests: inverting the labelling map without weak one-way functions

The inner-product family keys an `n`-bit point by an `n`-bit key and labels it by their inner
product over `𝔽₂`, so its concepts are the `2 ^ n` parities of subsets of the coordinates. Its
labelling map, on a key and two points, outputs the points followed by their labels. Without weak
one-way functions, some uniform strict PPT inverter for that map returns from `3 n` examples, on
infinitely many scales, a key of uniform error at most `1 / 4` except with probability at most
`1 / q n + (27 / 32) ^ n`. The exceptional event can occur: at scale `1` the two keys have
uniform error `1 / 2`, which is checked below. In general two distinct parities disagree on
exactly half of the points, so the event is that the returned key is not the true key; that
general remark explains the instance and is not proved here. Only the inverter is certified PPT.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.LearningOneWayInversion

open Cslib.MachineLearning.UniformLearning Cslib.MachineLearning.UniformLearning.OneWayInversion
open Cslib.MachineLearning.PACLearning Cslib.Crypto Cslib.Probability Turing.MultiTapeTM Filter
open scoped ENNReal

/-- The inner product over `𝔽₂` of the first `n` bits of a word with the rest. -/
private def innerProduct (n : ℕ) (w : List Bool) : Bool :=
  (List.zipWith (· && ·) (w.take n) (w.drop n)).foldl xor false

/-- The key `01` labels the point `11` by their inner product `1`. -/
example : family (fun n => n) innerProduct 2 ![false, true] ![true, true] = true := by
  decide

/-- The labelling map at scale `2` with two samples: key `01`, points `10` and `11`, and three
spare bits. The labels are the inner products `0` and `1`. -/
example : labelMap (fun n => n) (fun _ => 2) innerProduct 2
    [false, true, true, false, true, true, false, false, false] =
    [true, false, true, true, false, true] := by
  decide

private theorem computableInPolyTime_innerProduct :
    ComputableInPolyTime (fun p : ℕ × List Bool => innerProduct p.1 p.2)
      (encPair encUnary encBits) encBool := by
  unfold innerProduct
  fun_prop

/-- At scale `1` the two keys label the point `1` differently and the point `0` alike, so their
uniform error is `1 / 2`, above the threshold `1 / 4` of the next example. -/
example : uniformError (family (fun n => n) innerProduct 1 ![false])
    (family (fun n => n) innerProduct 1 ![true]) = 1 / 2 := by
  have h : hammingDist (family (fun n => n) innerProduct 1 ![true])
      (family (fun n => n) innerProduct 1 ![false]) = 1 := by
    decide
  rw [uniformError, h]
  norm_num

/-- Without weak one-way functions, some uniform strict PPT inverter returns from `3 n` examples of
the inner-product family a key of uniform error at most `1 / 4` except with probability
`1 / q n + (27 / 32) ^ n`, on infinitely many scales. The threshold `1 / 4` lies below the
uniform error `1 / 2` of the previous example, so the exceptional event can occur. -/
example (hOWF : ¬ ∃ f, WeakOneWay f) {q : Polynomial ℕ} (hq : ∀ n, 0 < q.eval n) :
    ∃ A : Inverter, IsPPT encBits A ∧ ∃ᶠ n in atTop,
      (learningExperiment (fun n => n) (fun n => 3 * n) innerProduct A n).toOuterMeasure
          {(K, _, K') | 1 / 4 < uniformError (family (fun n => n) innerProduct n K)
            (family (fun n => n) innerProduct n K')} ≤
        ((q.eval n : ℕ) : ℝ≥0∞)⁻¹ + (27 / 32) ^ n := by
  obtain ⟨A, hA, hfreq⟩ :=
    exists_isPPT_inverter_frequently_learningExperiment_le_of_not_exists_weakOneWay (fun n => n)
      (fun n => 3 * n) innerProduct hOWF (by fun_prop) (by fun_prop)
      computableInPolyTime_innerProduct hq
  refine ⟨A, hA, hfreq.mono fun n hn => (hn (1 / 4) (by norm_num)).trans_eq ?_⟩
  have hreal : (2 : ℝ) ^ n * (3 / 4) ^ (3 * n) = (27 / 32) ^ n := by
    rw [pow_mul, ← mul_pow]
    norm_num
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 4) = ENNReal.ofReal (3 / 4) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
    norm_num
  have hratio : (27 / 32 : ℝ≥0∞) = ENNReal.ofReal (27 / 32) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  rw [hsub, hratio, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 4),
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 27 / 32),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ n), hreal]

end CslibFrontierTests.LearningOneWayInversion
