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
arguments [Ji, Natarajan, Vidick, Wright and Yuen, §4][JNVWY2020].

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

/-- An effect satisfies `E² ≤ E`. -/
theorem effect_mul_self_le (P : Measurement α A) (a : α) :
    P.effect a * P.effect a ≤ P.effect a := by
  have h0 := P.nonneg a
  have h1 : 0 ≤ 1 - P.effect a := sub_nonneg.mpr (P.effect_le_one a)
  have := Commute.mul_nonneg h0 h1 ((Commute.one_right _).sub_right (Commute.refl _))
  rw [mul_sub, mul_one, sub_nonneg] at this
  exact this

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

end Cslib.Quantum.Measurement
