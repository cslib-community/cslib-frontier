/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Approx
public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
public import CslibFrontier.Foundations.Data.BitString.Sign

/-!
# Involutions, their projections and joint measurements

A *`±1` observable* is a self-adjoint involution `O`: `O⋆ = O` and `O² = 1`. Its eigenspace
projections are `P_b(O) = (1 + σ_b O)/2` with the sign `σ_b = Cslib.BitString.signVal b`
(`Cslib.Quantum.signProj`): self-adjoint idempotents with `P_false + P_true = 1`, `P_b P_{!b} = 0`
and `O P_b = σ_b P_b`. Measuring `O` gives the outcome `b` with effect `P_b`
(`Cslib.Quantum.Measurement.ofInvolution`). Three pairwise commuting involutions are measured
jointly by the products `P_{a₀}(O₀) P_{a₁}(O₁) P_{a₂}(O₂)`
(`Cslib.Quantum.Measurement.ofInvolution₃`), the measurement a prover performs on a row of a
linear-constraint game such as the magic square.

Two operators that are `0`-close in a state, `X ≈[φ; 0] Y`, can be exchanged at the right end of
any product inside the state: `φ(cX) = φ(cY)`
(`Cslib.Quantum.AlgState.apply_mul_eq_of_approx_zero`).
In a perfect strategy one prover's observables agree in this sense with the other's, and this is
how the operators of one prover are transferred to the other.

## Main definitions

* `Cslib.Quantum.signProj`: the projection `(1 + σ_b O)/2`.
* `Cslib.Quantum.Measurement.ofInvolution`: the measurement of a `±1` observable.
* `Cslib.Quantum.Measurement.ofInvolution₃`: the joint measurement of three commuting `±1`
  observables.

## Main results

* `Cslib.Quantum.signProj_mul_self`, `Cslib.Quantum.signProj_mul_signProj_not`,
  `Cslib.Quantum.signProj_add_signProj_not`: the projections of an involution.
* `Cslib.Quantum.AlgState.apply_mul_eq_of_approx_zero`: exchanging `0`-close operators.
-/

@[expose] public section

namespace Cslib.Quantum

open Finset
open BitString (signVal)

section Sign

variable {A : Type*} [Ring A] [Algebra ℂ A]

private theorem ofReal_signVal_mul_self (b : Bool) :
    (signVal b : ℂ) * signVal b = 1 := by
  rw [← Complex.ofReal_mul, BitString.signVal_mul_self, Complex.ofReal_one]

/-- The eigenspace projection `(1 + σ_b O)/2` of the `±1` observable `O`. -/
noncomputable def signProj (O : A) (b : Bool) : A :=
  (2⁻¹ : ℂ) • (1 + (signVal b : ℂ) • O)

/-- Star-algebra homomorphisms carry projections to projections. -/
theorem map_signProj {B F : Type*} [Ring B] [Algebra ℂ B] [FunLike F A B] [AlgHomClass F ℂ A B]
    (f : F) (O : A) (b : Bool) : f (signProj O b) = signProj (f O) b := by
  simp only [signProj, map_smul, map_add, map_one]

variable {O O' : A}

theorem signProj_add_signProj_not (O : A) (b : Bool) : signProj O b + signProj O (!b) = 1 := by
  simp only [signProj, BitString.signVal_not, Complex.ofReal_neg, neg_smul, ← smul_add]
  rw [show (1 + (signVal b : ℂ) • O + (1 + -((signVal b : ℂ) • O)) : A) = (2 : ℂ) • 1 by
    rw [two_smul]; abel, smul_smul]
  norm_num

theorem sum_signProj (O : A) : ∑ b, signProj O b = 1 := by
  rw [Fintype.sum_bool, add_comm]
  exact signProj_add_signProj_not O false

theorem signProj_sub_signProj (O O' : A) (b : Bool) :
    signProj O b - signProj O' b = ((2⁻¹ : ℂ) * (signVal b : ℂ)) • (O - O') := by
  simp only [signProj, smul_add, smul_sub, mul_smul]
  abel

variable (hO : O * O = 1)
include hO

/-- `O P_b = σ_b P_b`. -/
theorem mul_signProj (b : Bool) : O * signProj O b = (signVal b : ℂ) • signProj O b := by
  simp only [signProj, mul_smul_comm, mul_add, mul_one, smul_add, smul_smul, hO]
  rw [show (signVal b : ℂ) * (2⁻¹ * (signVal b : ℂ)) = 2⁻¹ by
    rw [mul_left_comm, ofReal_signVal_mul_self, mul_one], add_comm, mul_comm]

theorem signProj_mul_self (b : Bool) : signProj O b * signProj O b = signProj O b := by
  have h := mul_signProj hO b
  calc signProj O b * signProj O b =
        (2⁻¹ : ℂ) • (signProj O b + (signVal b : ℂ) • (O * signProj O b))
        := by simp only [signProj, smul_mul_assoc, add_mul, one_mul, smul_add]
    _ = signProj O b := by
      rw [h, smul_smul, ofReal_signVal_mul_self, one_smul, ← two_smul ℂ, smul_smul]; norm_num

theorem signProj_mul_signProj_not (b : Bool) : signProj O b * signProj O (!b) = 0 := by
  have h := congrArg (signProj O b * ·) (signProj_add_signProj_not O b)
  simp only [mul_add, mul_one, signProj_mul_self hO] at h
  exact add_eq_left.mp h

theorem signProj_mul_signProj_of_ne {b c : Bool} (h : b ≠ c) :
    signProj O b * signProj O c = 0 := by
  obtain rfl : c = !b := by cases b <;> cases c <;> simp_all
  exact signProj_mul_signProj_not hO b

end Sign

/-- An observable commuting with `O` commutes with the projections of `O`. -/
theorem _root_.Commute.signProj_left {A : Type*} [Ring A] [Algebra ℂ A] {O O' : A}
    (h : Commute O O') (b : Bool) : Commute (signProj O b) O' :=
  ((Commute.one_left _).add_left (h.smul_left _)).smul_left _

/-- The projections of commuting observables commute. -/
theorem _root_.Commute.signProj {A : Type*} [Ring A] [Algebra ℂ A] {O O' : A}
    (h : Commute O O') (b c : Bool) : Commute (signProj O b) (signProj O' c) := by
  have h₁ : Commute (1 + (signVal b : ℂ) • O) (1 + (signVal c : ℂ) • O') :=
    (Commute.one_left _).add_left
      ((Commute.one_right _).add_right ((h.smul_left _).smul_right _))
  exact (h₁.smul_left _).smul_right _

section Order

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem isSelfAdjoint_signProj {O : A} (hO : IsSelfAdjoint O) (b : Bool) :
    IsSelfAdjoint (signProj O b) := by
  have h2 : IsSelfAdjoint (2⁻¹ : ℂ) := by simp [IsSelfAdjoint]
  have hs : IsSelfAdjoint (signVal b : ℂ) := by cases b <;> simp [IsSelfAdjoint]
  exact IsSelfAdjoint.smul h2 ((IsSelfAdjoint.one A).add (IsSelfAdjoint.smul hs hO))

omit [Algebra ℂ A] [StarModule ℂ A] in
/-- A self-adjoint idempotent is nonnegative. -/
theorem nonneg_of_isSelfAdjoint_of_mul_self {P : A} (hP : IsSelfAdjoint P) (hPP : P * P = P) :
    0 ≤ P := by
  have h : P = star P * P := by rw [hP.star_eq, hPP]
  rw [h]
  exact star_mul_self_nonneg P

/-- The measurement of a `±1` observable: outcome `b` with effect `(1 + σ_b O)/2`. -/
noncomputable def Measurement.ofInvolution {O : A} (hO : IsSelfAdjoint O) (hO' : O * O = 1) :
    Measurement Bool A where
  effect := signProj O
  nonneg b := nonneg_of_isSelfAdjoint_of_mul_self (isSelfAdjoint_signProj hO b)
    (signProj_mul_self hO' b)
  sum_effect := sum_signProj O

theorem Measurement.isProjective_ofInvolution {O : A} (hO : IsSelfAdjoint O) (hO' : O * O = 1) :
    (Measurement.ofInvolution hO hO').IsProjective :=
  signProj_mul_self hO'

/-- The product `P_{a₀}(O₀) P_{a₁}(O₁) P_{a₂}(O₂)` of the projections of three observables. -/
noncomputable def signProj₃ (O₀ O₁ O₂ : A) : Bool × Bool × Bool → A
  | (a₀, a₁, a₂) => signProj O₀ a₀ * signProj O₁ a₁ * signProj O₂ a₂

/-- The joint measurement of three pairwise commuting `±1` observables. -/
noncomputable def Measurement.ofInvolution₃ {O₀ O₁ O₂ : A} (h₀ : IsSelfAdjoint O₀)
    (h₁ : IsSelfAdjoint O₁) (h₂ : IsSelfAdjoint O₂) (h₀' : O₀ * O₀ = 1) (h₁' : O₁ * O₁ = 1)
    (h₂' : O₂ * O₂ = 1) (c₀₁ : Commute O₀ O₁) (c₀₂ : Commute O₀ O₂) (c₁₂ : Commute O₁ O₂) :
    Measurement (Bool × Bool × Bool) A where
  effect := signProj₃ O₀ O₁ O₂
  nonneg := by
    rintro ⟨a₀, a₁, a₂⟩
    set P₀ := signProj O₀ a₀
    set P₁ := signProj O₁ a₁
    set P₂ := signProj O₂ a₂
    have d₀₁ : Commute P₀ P₁ := c₀₁.signProj a₀ a₁
    have d₀₂ : Commute P₀ P₂ := c₀₂.signProj a₀ a₂
    have d₁₂ : Commute P₁ P₂ := c₁₂.signProj a₁ a₂
    have s₀ := isSelfAdjoint_signProj h₀ a₀
    have s₁ := isSelfAdjoint_signProj h₁ a₁
    have s₂ := isSelfAdjoint_signProj h₂ a₂
    refine nonneg_of_isSelfAdjoint_of_mul_self ?_ ?_
    · change star (P₀ * P₁ * P₂) = P₀ * P₁ * P₂
      calc star (P₀ * P₁ * P₂) = P₂ * P₁ * P₀ := by
            rw [star_mul, star_mul, s₀.star_eq, s₁.star_eq, s₂.star_eq, mul_assoc]
        _ = P₁ * (P₂ * P₀) := by rw [← d₁₂.eq, mul_assoc]
        _ = P₀ * P₁ * P₂ := by rw [← d₀₂.eq, ← mul_assoc, ← d₀₁.eq]
    · change P₀ * P₁ * P₂ * (P₀ * P₁ * P₂) = P₀ * P₁ * P₂
      have e₀ := signProj_mul_self h₀' a₀
      have e₁ := signProj_mul_self h₁' a₁
      have e₂ := signProj_mul_self h₂' a₂
      calc P₀ * P₁ * P₂ * (P₀ * P₁ * P₂) = (P₀ * P₀) * (P₁ * P₁) * (P₂ * P₂) := by
            rw [show P₀ * P₁ * P₂ * (P₀ * P₁ * P₂) = P₀ * (P₁ * (P₂ * P₀) * P₁) * P₂ by
              noncomm_ring, ← d₀₂.eq,
              show P₀ * (P₁ * (P₀ * P₂) * P₁) * P₂ = P₀ * (P₁ * P₀) * (P₂ * P₁) * P₂ by
              noncomm_ring, ← d₀₁.eq, ← d₁₂.eq]
            noncomm_ring
        _ = P₀ * P₁ * P₂ := by rw [e₀, e₁, e₂]
  sum_effect := by
    simp only [Fintype.sum_prod_type, signProj₃, ← mul_sum, sum_signProj, mul_one]

end Order

namespace AlgState

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A] [SelfAdjointDecompose A] {φ : AlgState A}

/-- Operators that are `0`-close in a state can be exchanged at the right end of a product:
`φ(cX) = φ(cY)`. -/
theorem apply_mul_eq_of_approx_zero {a b : A} (h : a ≈[φ; 0] b) (c : A) :
    φ (c * a) = φ (c * b) := by
  have hle := φ.norm_apply_star_mul_le (star c) (a - b)
  rw [star_star, (approx_iff.mp h).antisymm (φ.norm_nonneg _), mul_zero, norm_le_zero_iff, mul_sub,
    map_sub, sub_eq_zero] at hle
  exact hle

/-- The projections of `0`-close observables can be exchanged at the right end of a product. -/
theorem apply_mul_signProj_eq_of_approx_zero {X Y : A} (h : X ≈[φ; 0] Y) (c : A) (b : Bool) :
    φ (c * signProj X b) = φ (c * signProj Y b) := by
  rw [← sub_eq_zero, ← map_sub, ← mul_sub, signProj_sub_signProj, mul_smul_comm, map_smul,
    mul_sub, map_sub, apply_mul_eq_of_approx_zero h, sub_self, smul_zero]

end AlgState

end Cslib.Quantum
