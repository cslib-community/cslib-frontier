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

omit [StarRing A] [StarOrderedRing A] in
/-- Agreement of two postprocessed measurements sums exactly the joint coefficients whose
decoded outcomes match. -/
theorem agreement_map_map {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq γ]
    [IsOrderedAddMonoid A] (φ : AlgState A) (P : Measurement α A) (Q : Measurement β A)
    (f : α → γ) (g : β → γ) :
    agreement φ (P.map f) (Q.map g) =
      ∑ a, ∑ b, if f a = g b then (φ (P.effect a * Q.effect b)).re else 0 := by
  simp only [agreement, map_effect, sum_mul, mul_sum, map_sum, Complex.re_sum, sum_filter]
  let c (z : γ) (b : β) (a : α) :=
    (φ ((if f a = z then P.effect a else 0) * (if g b = z then Q.effect b else 0))).re
  change (∑ z, ∑ b, ∑ a, c z b a) = _
  calc
    _ = ∑ b, ∑ a, ∑ z, c z b a := by
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_comm
    _ = ∑ a, ∑ b, ∑ z, c z b a := sum_comm
    _ = _ := by
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      have hc (z : γ) : c z b a =
          if f a = z then if g b = z then (φ (P.effect a * Q.effect b)).re else 0 else 0 := by
        dsimp only [c]
        split_ifs <;> simp
      simp only [hc, sum_ite_eq', mem_univ, ite_true, eq_comm]

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

omit [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] in
private theorem norm_sub_effect_sq (φ : AlgState A) (P Q : Measurement α A)
    (a : α) (h : Commute (P.effect a) (Q.effect a)) :
    φ.norm (P.effect a - Q.effect a) ^ 2 =
      (φ (P.effect a * P.effect a)).re + (φ (Q.effect a * Q.effect a)).re -
        2 * (φ (P.effect a * Q.effect a)).re := by
  have hP := (P.nonneg a).isSelfAdjoint.star_eq
  have hQ := (Q.nonneg a).isSelfAdjoint.star_eq
  have hexp : star (P.effect a - Q.effect a) * (P.effect a - Q.effect a) =
      P.effect a * P.effect a + Q.effect a * Q.effect a - 2 * (P.effect a * Q.effect a) := by
    have hc := h.eq
    rw [star_sub, hP, hQ, two_mul]
    calc (P.effect a - Q.effect a) * (P.effect a - Q.effect a)
        = P.effect a * P.effect a + Q.effect a * Q.effect a -
          (P.effect a * Q.effect a + Q.effect a * P.effect a) := by noncomm_ring
      _ = _ := by rw [← hc]
  have h2 : (φ (2 * (P.effect a * Q.effect a))).re = 2 * (φ (P.effect a * Q.effect a)).re := by
    rw [two_mul, map_add, Complex.add_re, two_mul]
  rw [AlgState.norm_sq, hexp, map_sub, map_add, Complex.sub_re, Complex.add_re, h2]

omit [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]
  [StarModule ℂ A] [SelfAdjointDecompose A] in
private theorem sum_re_effect_add_sub (φ : AlgState A) (P Q : Measurement α A) :
    (∑ a, ((φ (P.effect a)).re + (φ (Q.effect a)).re -
      2 * (φ (P.effect a * Q.effect a)).re)) = 2 - 2 * agreement φ P Q := by
  have hP : ∑ a, (φ (P.effect a)).re = 1 := by
    simpa [prob] using P.sum_prob φ
  have hQ : ∑ a, (φ (Q.effect a)).re = 1 := by
    simpa [prob] using Q.sum_prob φ
  rw [sum_sub_distrib, sum_add_distrib, hP, hQ, ← mul_sum, agreement]
  ring

omit [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] in
/-- For commuting projective measurements the squared distance is twice the disagreement. -/
theorem sum_norm_sub_sq_eq_of_isProjective (φ : AlgState A) (P Q : Measurement α A)
    (h : ∀ a, Commute (P.effect a) (Q.effect a)) (hP : P.IsProjective) (hQ : Q.IsProjective) :
    ∑ a, φ.norm (P.effect a - Q.effect a) ^ 2 = 2 - 2 * agreement φ P Q := by
  rw [← sum_re_effect_add_sub]
  exact sum_congr rfl fun a _ => by rw [norm_sub_effect_sq φ P Q a (h a), hP a, hQ a]

/-- **Consistency implies closeness**: if the effects of `P` and `Q` commute, then
`∑_a ‖P_a - Q_a‖²_φ ≤ 2 - 2 · agreement`. -/
theorem sum_norm_sub_sq_le (φ : AlgState A) (P Q : Measurement α A)
    (h : ∀ a, Commute (P.effect a) (Q.effect a)) :
    ∑ a, φ.norm (P.effect a - Q.effect a) ^ 2 ≤ 2 - 2 * agreement φ P Q := by
  rw [← sum_re_effect_add_sub]
  refine sum_le_sum fun a _ => ?_
  rw [norm_sub_effect_sq φ P Q a (h a)]
  linarith only [φ.re_apply_mono (P.effect_mul_self_le a),
    φ.re_apply_mono (Q.effect_mul_self_le a)]

/-- Measurements that agree with probability at least `1 - ε` have effects that are close in
the state: `∑_a ‖P_a - Q_a‖²_φ ≤ 2ε`. -/
theorem sum_norm_sub_sq_le_of_agreement (φ : AlgState A) (P Q : Measurement α A)
    (h : ∀ a, Commute (P.effect a) (Q.effect a)) {ε : ℝ} (hε : 1 - ε ≤ agreement φ P Q) :
    ∑ a, φ.norm (P.effect a - Q.effect a) ^ 2 ≤ 2 * ε := by
  linarith [sum_norm_sub_sq_le φ P Q h]

end Cslib.Quantum.Measurement
