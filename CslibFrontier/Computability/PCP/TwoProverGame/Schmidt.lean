/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Quantum
public import CslibFrontier.Foundations.Quantum.DensityMatrix

/-!
# Symmetric quantum strategies in Schmidt coordinates

A symmetric strategy, in the joint Schmidt basis of its state, is specified by a nonnegative
spectrum summing to one and Alice's POVMs. The state has amplitudes `√dᵢ` at `(i,i)`, and
Bob's POVMs are the transposes of Alice's. This is the coordinate form of symmetry from
[Vidick, Definition 2.3][Vidick2022].
-/

public section

open Matrix Finset
open scoped Kronecker ComplexOrder

namespace Cslib.Quantum.POVM

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Transpose every effect of a matrix POVM. -/
def transpose (M : POVM A ι) : POVM A ι where
  effect a := (M.effect a)ᵀ
  posSemidef a := (M.posSemidef a).transpose
  sum_effect := by rw [← Matrix.transpose_sum, M.sum_effect, Matrix.transpose_one]

@[simp] theorem transpose_effect (M : POVM A ι) (a : A) :
    M.transpose.effect a = (M.effect a)ᵀ := by
  unfold transpose
  rfl

end Cslib.Quantum.POVM

namespace Cslib.PCP.QuantumStrategy

open Cslib.Quantum

variable {ι X A : Type*} [DecidableEq ι]

/-- A bipartite vector with squared Schmidt coefficients `d`, in its Schmidt basis. -/
noncomputable def schmidtVector (d : ι → ℝ) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then (Real.sqrt (d p.1) : ℂ) else 0

@[simp] theorem schmidtVector_apply (d : ι → ℝ) (i j : ι) :
    (schmidtVector d).ofLp (i, j) = if i = j then (Real.sqrt (d i) : ℂ) else 0 := by
  unfold schmidtVector
  rfl

variable [Fintype ι] [Fintype A]

/-- The normalized symmetric strategy specified in its Schmidt basis. -/
noncomputable def ofSchmidt (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1)
    (M : X → POVM A ι) : QuantumStrategy X X A A ι ι where
  state := schmidtVector d
  norm_state := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, one_pow, ← htrace]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i]
    · simp [Real.sq_sqrt (hd i)]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  alice := M
  bob x := (M x).transpose

@[simp] theorem ofSchmidt_state (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1)
    (M : X → POVM A ι) : (ofSchmidt d hd htrace M).state = schmidtVector d := by
  unfold ofSchmidt
  rfl

@[simp] theorem ofSchmidt_alice_effect (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (htrace : ∑ i, d i = 1) (M : X → POVM A ι) (x : X) (a : A) :
    ((ofSchmidt d hd htrace M).alice x).effect a = (M x).effect a := by
  unfold ofSchmidt
  rfl

@[simp] theorem ofSchmidt_bob_effect (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (htrace : ∑ i, d i = 1) (M : X → POVM A ι) (x : X) (a : A) :
    ((ofSchmidt d hd htrace M).bob x).effect a = ((M x).effect a)ᵀ := by
  unfold ofSchmidt
  rw [POVM.transpose_effect]

private theorem schmidtVector_kronecker_expectation (d : ι → ℝ) (P Q : Matrix ι ι ℂ) :
    star (schmidtVector d).ofLp ⬝ᵥ ((P ⊗ₖ Q) *ᵥ (schmidtVector d).ofLp) =
      ∑ i, ∑ j, (Real.sqrt (d i) : ℂ) * (P i j * Q i j) * (Real.sqrt (d j) : ℂ) := by
  rw [dotProduct, Fintype.sum_prod_type]
  simp only [Pi.star_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_eq_single i]
  · rw [schmidtVector_apply, ite_eq_left rfl]
    rw [show star (↑(Real.sqrt (d i)) : ℂ) = ↑(Real.sqrt (d i)) by simp]
    rw [Matrix.mulVec_apply, dotProduct, Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_eq_single j]
    · simp [mul_assoc]
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- The probability of a matching answer is the squared-entry sum with geometric-mean weights. -/
theorem prob_ofSchmidt_same (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1)
    (M : X → POVM A ι) (x : X) (a : A) :
    (ofSchmidt d hd htrace M).prob x x a a =
      ∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) * ‖(M x).effect a i j‖ ^ 2 := by
  rw [prob_eq]
  change (star (schmidtVector d).ofLp ⬝ᵥ
    ((((M x).effect a) ⊗ₖ (((M x).effect a)ᵀ)) *ᵥ (schmidtVector d).ofLp)).re = _
  rw [schmidtVector_kronecker_expectation]
  simp only [Complex.re_sum, transpose_apply]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [← ((M x).posSemidef a).isHermitian.apply j i]
  have hn := Complex.mul_conj' ((M x).effect a i j)
  rw [starRingEnd_apply] at hn
  rw [hn, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- On a uniform Schmidt spectrum, the joint probability is the normalized trace of
the product of the two Alice effects. Bob's effect is the transpose of the second effect. -/
theorem prob_ofSchmidt_const (r : ℝ) (hr : 0 ≤ r) (htrace : ∑ _ : ι, r = 1)
    (M : X → POVM A ι) (x y : X) (a b : A) :
    (ofSchmidt (fun _ => r) (fun _ => hr) htrace M).prob x y a b =
      r * (Matrix.trace ((M x).effect a * (M y).effect b)).re := by
  rw [prob_eq, ofSchmidt_state, ofSchmidt_alice_effect, ofSchmidt_bob_effect,
    schmidtVector_kronecker_expectation]
  simp only [transpose_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum,
    Finset.mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have he (z : ℂ) : (Real.sqrt r : ℂ) * z * (Real.sqrt r : ℂ) = (r : ℂ) * z := by
    calc
      _ = ((Real.sqrt r * Real.sqrt r : ℝ) : ℂ) * z := by
        rw [Complex.ofReal_mul]
        ring
      _ = _ := by rw [Real.mul_self_sqrt hr]
  rw [he]
  simp [Complex.mul_re]

/-- Tracing out Bob in the Schmidt basis gives the diagonal matrix of squared coefficients. -/
theorem partialTraceRight_pureState_schmidtVector (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    partialTraceRight (pureState (schmidtVector d)) = diagonal (fun i => (d i : ℂ)) := by
  ext i j
  rw [partialTraceRight_apply, sum_eq_single i]
  · by_cases h : i = j
    · subst j
      simp [schmidtVector_apply, ← Complex.ofReal_mul, Real.mul_self_sqrt (hd i)]
    · simp [schmidtVector_apply, h, Ne.symm h, diagonal_apply_ne]
  · intro k _ hk
    simp [schmidtVector_apply, Ne.symm hk]
  · simp

end Cslib.PCP.QuantumStrategy
