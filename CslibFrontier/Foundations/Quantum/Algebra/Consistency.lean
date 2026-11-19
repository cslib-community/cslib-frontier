/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Approx
public import CslibFrontier.Foundations.Quantum.Algebra.Measurement

/-!
# Consistent measurements are close

Two measurements `P` and `Q` with the same outcomes whose effects commute, typically the
measurements of two provers, can be performed jointly in a state `φ`; they *agree* with
probability `∑_a Re φ(P_a Q_a)` (`Cslib.Quantum.Measurement.agreement`). Consistency is the basic
test of nonlocal games: ask both provers the same question and check that the answers agree.

When they agree with probability `1 - ε`, their effects are close in the state:
`∑_a ‖P_a - Q_a‖²_φ ≤ 2ε` (`Cslib.Quantum.Measurement.sum_norm_sub_sq_le`), for arbitrary
measurements, not only projective ones. The reason is that an effect `0 ≤ E ≤ 1` satisfies
`E² ≤ E` (`Cslib.Quantum.Measurement.effect_mul_self_le`), so
`‖P_a - Q_a‖² = φ(P_a²) + φ(Q_a²) - 2 φ(P_a Q_a) ≤ φ(P_a) + φ(Q_a) - 2 φ(P_a Q_a)`, and summing
over `a` gives `2 - 2(1 - ε)`. This is the step "consistency implies closeness" of rigidity
arguments [Ji, Natarajan, Vidick, Wright and Yuen, §5.2, Fact 5.18(1)][JNVWY2020].

## Main definitions

* `Cslib.Quantum.Measurement.agreement`: the probability that two measurements agree.

## Main results

* `Cslib.Quantum.Measurement.effect_mul_self_le`: `E² ≤ E` for an effect.
* `Cslib.Quantum.Measurement.sum_norm_sub_sq_le`: consistency implies closeness.

## References

* [Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, *MIP* = RE*][JNVWY2020]
-/

@[expose] public section

namespace Cslib.Quantum.Measurement

open Finset

variable {α A : Type*} [Fintype α] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [Algebra ℂ A]

/-- The probability `∑_a Re φ(P_a Q_a)` that the measurements `P` and `Q` agree in the state
`φ`. -/
noncomputable def agreement (φ : AlgState A) (P Q : Measurement α A) : ℝ :=
  ∑ a, (φ (P.effect a * Q.effect a)).re

variable [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-- An element between `0` and `1` satisfies `e² ≤ e`. -/
theorem _root_.Cslib.Quantum.mul_self_le_self_of_nonneg_of_le_one {e : A} (h0 : 0 ≤ e)
    (h1 : e ≤ 1) : e * e ≤ e := by
  have := Commute.mul_nonneg h0 (sub_nonneg.mpr h1)
    ((Commute.one_right _).sub_right (Commute.refl _))
  rw [mul_sub, mul_one, sub_nonneg] at this
  exact this

/-- An effect satisfies `E² ≤ E`. -/
theorem effect_mul_self_le (P : Measurement α A) (a : α) :
    P.effect a * P.effect a ≤ P.effect a :=
  mul_self_le_self_of_nonneg_of_le_one (P.nonneg a) (P.effect_le_one a)

variable [StarModule ℂ A] [SelfAdjointDecompose A]

/-- **Consistency implies closeness**: if the effects of `P` and `Q` commute, then
`∑_a ‖P_a - Q_a‖²_φ ≤ 2 - 2 · agreement`. -/
theorem sum_norm_sub_sq_le (φ : AlgState A) (P Q : Measurement α A)
    (h : ∀ a, Commute (P.effect a) (Q.effect a)) :
    ∑ a, φ.norm (P.effect a - Q.effect a) ^ 2 ≤ 2 - 2 * agreement φ P Q := by
  have key : ∀ a, φ.norm (P.effect a - Q.effect a) ^ 2 ≤
      (φ (P.effect a)).re + (φ (Q.effect a)).re - 2 * (φ (P.effect a * Q.effect a)).re := by
    intro a
    have hP := (P.nonneg a).isSelfAdjoint.star_eq
    have hQ := (Q.nonneg a).isSelfAdjoint.star_eq
    have hexp : star (P.effect a - Q.effect a) * (P.effect a - Q.effect a) =
        P.effect a * P.effect a + Q.effect a * Q.effect a - 2 * (P.effect a * Q.effect a) := by
      have hc := (h a).eq
      rw [star_sub, hP, hQ, two_mul]
      calc (P.effect a - Q.effect a) * (P.effect a - Q.effect a)
          = P.effect a * P.effect a + Q.effect a * Q.effect a -
            (P.effect a * Q.effect a + Q.effect a * P.effect a) := by noncomm_ring
        _ = _ := by rw [← hc]
    have hPP := φ.re_apply_mono (P.effect_mul_self_le a)
    have hQQ := φ.re_apply_mono (Q.effect_mul_self_le a)
    have h2 : (φ (2 * (P.effect a * Q.effect a))).re = 2 * (φ (P.effect a * Q.effect a)).re := by
      rw [two_mul, map_add, Complex.add_re, two_mul]
    rw [AlgState.norm_sq, hexp, map_sub, map_add, Complex.sub_re, Complex.add_re, h2]
    linarith
  have hP : ∑ a, (φ (P.effect a)).re = 1 := by
    simpa [prob] using P.sum_prob φ
  have hQ : ∑ a, (φ (Q.effect a)).re = 1 := by
    simpa [prob] using Q.sum_prob φ
  calc ∑ a, φ.norm (P.effect a - Q.effect a) ^ 2
      ≤ ∑ a, ((φ (P.effect a)).re + (φ (Q.effect a)).re -
          2 * (φ (P.effect a * Q.effect a)).re) := sum_le_sum fun a _ => key a
    _ = 2 - 2 * agreement φ P Q := by
      rw [sum_sub_distrib, sum_add_distrib, hP, hQ, ← mul_sum, agreement]
      ring

/-- Measurements that agree with probability at least `1 - ε` have effects that are close in
the state: `∑_a ‖P_a - Q_a‖²_φ ≤ 2ε`. -/
theorem sum_norm_sub_sq_le_of_agreement (φ : AlgState A) (P Q : Measurement α A)
    (h : ∀ a, Commute (P.effect a) (Q.effect a)) {ε : ℝ} (hε : 1 - ε ≤ agreement φ P Q) :
    ∑ a, φ.norm (P.effect a - Q.effect a) ^ 2 ≤ 2 * ε := by
  linarith [sum_norm_sub_sq_le φ P Q h]

/-- If two binary measurements have commuting effects, the squared distance between their
observables is at most four times the probability that they disagree. -/
theorem norm_observable_sub_sq_le (φ : AlgState A) (P Q : Measurement Bool A)
    (h : ∀ a, Commute (P.effect a) (Q.effect a)) :
    φ.norm (P.observable - Q.observable) ^ 2 ≤ 4 * (1 - agreement φ P Q) := by
  have htrue (M : Measurement Bool A) : M.effect true = 1 - M.effect false := by
    have hsum := M.sum_effect
    rw [Fintype.sum_bool] at hsum
    exact eq_sub_of_add_eq hsum
  have hneg : P.effect true - Q.effect true = -(P.effect false - Q.effect false) := by
    rw [htrue P, htrue Q]
    abel
  have hobs : P.observable - Q.observable = (2 : ℂ) • (P.effect false - Q.effect false) := by
    rw [observable, observable, sub_sub_sub_comm, hneg, sub_neg_eq_add, two_smul]
  have hdist := sum_norm_sub_sq_le φ P Q h
  rw [Fintype.sum_bool, hneg, φ.norm_neg] at hdist
  rw [hobs, φ.norm_smul]
  norm_num
  nlinarith

/-- The squared distance of a binary observable from the identity is bounded by
four times its true outcome probability. -/
theorem norm_observable_sub_one_sq_le (φ : AlgState A) (M : Measurement Bool A) :
    φ.norm (M.observable - 1) ^ 2 ≤ 4 * M.prob φ true := by
  let constant : Measurement Bool A := const false
  have hcomm (b : Bool) : Commute (M.effect b) (constant.effect b) := by
    cases b <;> simp [constant, const]
  have h := norm_observable_sub_sq_le φ M constant hcomm
  have hobs : constant.observable = 1 := by simp [constant, const, observable]
  have hagree : agreement φ M constant = M.prob φ false := by
    simp [agreement, constant, const, prob]
  rw [hobs, hagree] at h
  have htotal := M.sum_prob φ
  rw [Fintype.sum_bool] at htotal
  linarith

end Cslib.Quantum.Measurement
