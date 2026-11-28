/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.AxisTest
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Data.Nat.Size

/-!
# Soundness bounds for the axis and arithmetic checks

If a static proof frequently fails the axis test, a conjunction that runs the axis test rejects
at least as often. Otherwise the point table is close to a multilinear assignment, and the
arithmetic check can use that assignment to bound acceptance. The fair-bit sampling precision
and field-size estimates below quantify both cases.

## Main definitions

* `axisGapDenominator` gives the inverse-polynomial scale of the axis test.

## Main results

* `arithmeticError_le_half` adds the arithmetic, local-correction and sampling errors.
* `axisAnd_accept_le` transfers a sound arithmetic check for nearby assignments to the
  conjunction with the native axis verifier.
-/

public section

namespace Cslib.Complexity.MIP

open Cslib.Code Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

/-- Denominator of the ideal axis-line rejection threshold in dimension `n`. -/
@[expose] def axisGapDenominator (n : ℕ) : ℕ := 10 ^ 6 * (n + 1) ^ 7

/-- The inverse-gap denominator for a unary dimension is polynomial-time computable in unary. -/
@[fun_prop] theorem computableInPolyTime_axisGapDenominator :
    ComputableInPolyTime axisGapDenominator encUnary encUnary := by
  unfold axisGapDenominator
  fun_prop

private theorem denominator_lower (n : ℕ) : 10 ^ 6 ≤ axisGapDenominator n := by
  exact Nat.le_mul_of_pos_right _ (by positivity)

private theorem precision_lower (n : ℕ) :
    (4 : ℝ) * axisGapDenominator n < 2 ^ (4 * axisGapDenominator n).size := by
  exact_mod_cast Nat.lt_size_self (4 * axisGapDenominator n)

/-- In a prime field above the stated size, the arithmetic error, three corrected evaluation
errors and dyadic sampling errors sum to at most one half. The normalized Hamming bound comes
from the axis test. -/
theorem arithmeticError_le_half {n p R d : ℕ} {H : ℝ}
    (hp : 1000 * (n + 1) ^ 3 + 100 * (R + 1) * (d + 1) < p)
    (hH : H < (p : ℝ) ^ n / (100 * (n + 1))) :
    let precision := (4 * axisGapDenominator n).size
    (R : ℝ) * (d + 1) / p +
      3 * ((n + 1 : ℝ) * H / (p : ℝ) ^ n + 1 / 2 ^ precision) +
      (1 / 2 ^ precision + 1 / 2 ^ precision) ≤ 1 / 2 := by
  dsimp only
  have hpos : 0 < p := by omega
  have hp' : 1000 * ((n : ℝ) + 1) ^ 3 + 100 * (R + 1 : ℝ) * (d + 1 : ℝ) < p := by
    exact_mod_cast hp
  have ha : (R : ℝ) * (d + 1) / p ≤ 1 / 100 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [show 0 ≤ ((n : ℝ) + 1) ^ 3 by positivity]
  have hh : (n + 1 : ℝ) * H / (p : ℝ) ^ n ≤ 1 / 100 := by
    apply (div_le_iff₀ (by positivity)).2
    have := (lt_div_iff₀ (by positivity)).1 hH
    linarith
  have hprec : 100 ≤ (2 : ℝ) ^ (4 * axisGapDenominator n).size := by
    have hd : (1000000 : ℝ) ≤ axisGapDenominator n := by exact_mod_cast denominator_lower n
    linarith [precision_lower n]
  have he : 1 / (2 : ℝ) ^ (4 * axisGapDenominator n).size ≤ 1 / 100 := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  linarith only [ha, hh, he]

private theorem run_and_true (π : List Bool → Bool) (a b : WordOracleComp Unit Bool) :
    (((Prover.ofProof π).run (do
      let ok ← a
      if ok then b else pure false) ()).map Prod.fst) true =
      (((Prover.ofProof π).run a ()).map Prod.fst) true *
        (((Prover.ofProof π).run b ()).map Prod.fst) true := by
  rw [Prover.run_bind, _root_.PMF.map_bind]
  simp [_root_.PMF.bind_apply, _root_.PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Prover.run_pure]

/-- If the arithmetic verifier accepts with probability at most one half whenever the proof
table is close to a multilinear assignment, its conjunction with the native axis test rejects
with probability at least `1 / (2 * axisGapDenominator n)`. The phases share the proof. -/
theorem axisAnd_accept_le (π : List Bool → Bool) {n p : ℕ} [NeZero n] [Fact p.Prime]
    (hq : 1000 * (n + 1) ^ 3 ≤ p) (arithmetic : WordOracleComp Unit Bool)
    (hnear : ∀ A ∈ MvPolynomial.restrictDegree (Fin n) (ZMod p) 1,
      (hammingDist (proofPoint π p) (fun x => MvPolynomial.eval x A) : ℝ) <
        p ^ n / (100 * (n + 1)) →
      ((((Prover.ofProof π).run arithmetic ()).map Prod.fst) true).toReal ≤ 1 / 2) :
    let precision := (4 * axisGapDenominator n).size
    (((Prover.ofProof π).run (do
      let ok ← axisRound n p precision
      if ok then arithmetic else pure false) ()).map Prod.fst) true ≤
        1 - (2 * (axisGapDenominator n : ENNReal))⁻¹ := by
  dsimp only
  let D := axisGapDenominator n
  let precision := (4 * D).size
  let axis := ((Prover.ofProof π).run (axisRound n p precision) ()).map Prod.fst
  let alg := ((Prover.ofProof π).run arithmetic ()).map Prod.fst
  rw [run_and_true]
  change axis true * alg true ≤ 1 - (2 * (D : ENNReal))⁻¹
  have hD : (1 : ℝ) ≤ D := by
    have h := denominator_lower n
    exact_mod_cast (show 1 ≤ D by omega)
  have hD0 : 0 < (D : ℝ) := by linarith
  have hgap : (2 * (D : ENNReal))⁻¹ ≤ 1 := by
    apply ENNReal.inv_le_one.mpr
    exact_mod_cast (show 1 ≤ 2 * D by have := denominator_lower n; omega)
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (_root_.PMF.apply_ne_top axis true) (_root_.PMF.apply_ne_top alg true))
    (ENNReal.sub_ne_top ENNReal.one_ne_top)).mp
  simp only [ENNReal.toReal_sub_of_le hgap ENNReal.one_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  have hmass := PMF.toReal_true_add_toReal_false axis
  by_cases hlow : (axis false).toReal < 1 / (2 * D)
  · have hprec := precision_lower n
    change 4 * (D : ℝ) < 2 ^ precision at hprec
    have hsmall : (2 : ℝ) / 2 ^ precision < 1 / (2 * D) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hrej : (axis false).toReal + 2 / 2 ^ precision < 1 / D := by
      calc _ < 1 / (2 * (D : ℝ)) + 1 / (2 * (D : ℝ)) := add_lt_add hlow hsmall
           _ = 1 / (D : ℝ) := by field_simp; norm_num
    have hthreshold : (D : ℝ) = 10 ^ 6 * (n + 1 : ℝ) ^ 7 := by norm_num [D, axisGapDenominator]
    rw [hthreshold] at hrej
    obtain ⟨A, hA, hdist⟩ := exists_assignment_of_axisRound π hq precision hrej
    have hprob : (alg true).toReal ≤ 1 / 2 := hnear A hA hdist
    have half : (2 * (D : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    calc (axis true).toReal * (alg true).toReal ≤ 1 * (alg true).toReal :=
            mul_le_mul_of_nonneg_right (PMF.toReal_apply_le_one axis true) ENNReal.toReal_nonneg
         _ ≤ 1 - (2 * (D : ℝ))⁻¹ := by linarith
  · calc (axis true).toReal * (alg true).toReal ≤ (axis true).toReal * 1 :=
            mul_le_mul_of_nonneg_left (PMF.toReal_apply_le_one alg true) ENNReal.toReal_nonneg
         _ ≤ 1 - (2 * (D : ℝ))⁻¹ := by rw [mul_one, ← one_div]; linarith

end Cslib.Complexity.MIP
