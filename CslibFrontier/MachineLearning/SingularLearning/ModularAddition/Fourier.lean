/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.SingularLearning.ModularAddition.Network
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# The Fourier fit for modular addition

[Levine2026, Section 5.1] says that Fourier inversion gives exact fits of the quadratic network
in which each neuron that contributes nontrivially carries a single frequency, without an
explicit fit. This module constructs the exact fit of [MAISA6, Lemma 4.2] at width `2 p - 1`,
which that document gives for odd `p ≥ 3`, and proves for every odd `p` that it is an exact fit
all of whose neurons have single-frequency form.

The fit has one neuron with constant tables and, for each frequency `k = 1, …, (p - 1) / 2`,
four neurons with tables `(cos, cos)`, `(sin, -sin)`, `(sin, cos)` and `(cos, sin)` of that
frequency. Their squares combine to `2 + 2 cos (ω k (a + b))` and `2 + 2 sin (ω k (a + b))`,
and the output vectors `cos (ω k ·) / p` and `sin (ω k ·) / p` assemble the Fourier expansion
of the coordinate vector at `a + b`. The width `2 p - 1 = 1 + 4 (p - 1) / 2` is the width of
this construction; the least width with an exact fit is a separate open question of [MAISA6].
The definitions below make sense for every `p`. For odd `p` they give an exact fit, which
extends the source's range by `p = 1`; for even `p` the frequency `p / 2` is missing and
`fourierFit p` is not an exact fit.

## Main definitions

* `Cslib.MachineLearning.ModularAddition.FourierIndex`: the neurons of the Fourier fit.
* `Cslib.MachineLearning.ModularAddition.fourierFit`: the Fourier fit `w^F` of
  [MAISA6, Lemma 4.2].

## Main results

* `Cslib.MachineLearning.ModularAddition.isExactFit_fourierFit`: for odd `p` it is an exact fit.
* `Cslib.MachineLearning.ModularAddition.isSingleFrequency_fourierFit`: every neuron of it has
  single-frequency form.
* `Cslib.MachineLearning.ModularAddition.card_fourierIndex`: for odd `p` it has `2 p - 1`
  neurons.

## References

* [L. Levine, *Math for AI safety: an invitation for mathematicians*, Section 5.1][Levine2026]
* [*Does geometric simplicity force a legible mechanism? Singular geometry of modular
  addition*, agenda MAIS-A6, Lemma 4.2][MAISA6]
-/

public section

namespace Cslib.MachineLearning.ModularAddition

open scoped Real
open Finset

variable {p : ℕ} [NeZero p]

/-- The neurons of the Fourier fit: one constant neuron, and four neurons for each frequency
`k = 1, …, (p - 1) / 2`, indexed here by `k - 1`. -/
abbrev FourierIndex (p : ℕ) : Type := Option (Fin ((p - 1) / 2) × Fin 4)

/-- For odd `p` the Fourier fit has `2 p - 1` neurons. -/
theorem card_fourierIndex {p : ℕ} (hp : Odd p) : Fintype.card (FourierIndex p) = 2 * p - 1 := by
  obtain ⟨n, rfl⟩ := hp
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
  omega

/-- The first tables of the Fourier fit. -/
@[expose] noncomputable def fourierLeft (p : ℕ) : FourierIndex p → ZMod p → ℝ
  | none => fun _ => 1 / 2
  | some (k, i) =>
    ![cosTable p (k + 1), sinTable p (k + 1), sinTable p (k + 1), cosTable p (k + 1)] i

/-- The second tables of the Fourier fit. -/
@[expose] noncomputable def fourierRight (p : ℕ) : FourierIndex p → ZMod p → ℝ
  | none => fun _ => 1 / 2
  | some (k, i) =>
    ![cosTable p (k + 1), -sinTable p (k + 1), cosTable p (k + 1), sinTable p (k + 1)] i

/-- The output vectors of the Fourier fit. -/
@[expose] noncomputable def fourierOut (p : ℕ) : FourierIndex p → ZMod p → ℝ
  | none => fun c => 1 / p - 2 / p * ∑ k : Fin ((p - 1) / 2),
      (cosTable p (k + 1) c + sinTable p (k + 1) c)
  | some (k, i) =>
    ![fun c => cosTable p (k + 1) c / p, fun c => cosTable p (k + 1) c / p,
      fun c => sinTable p (k + 1) c / p, fun c => sinTable p (k + 1) c / p] i

/-- The Fourier fit `w^F` of [MAISA6, Lemma 4.2], at width `2 p - 1`. The constant neuron has
both tables `1 / 2`. For frequency `k` the four neurons have tables `(cos, cos)`, `(sin, -sin)`,
`(sin, cos)`, `(cos, sin)` and output vectors `cos / p`, `cos / p`, `sin / p`, `sin / p`. The
output vector of the constant neuron is `1 / p - (2 / p) ∑ k, (cos + sin)`. -/
@[expose] noncomputable def fourierFit (p : ℕ) : Params p (FourierIndex p) :=
  Params.mk (fourierLeft p) (fourierRight p) (fourierOut p)

/-- The four neurons of one frequency: their squares combine to the cosine and the sine of the
sum of the two angles. -/
private theorem four_neurons (α β γ P : ℝ) :
    Real.cos γ / P * (Real.cos α + Real.cos β) ^ 2 +
        Real.cos γ / P * (Real.sin α + -Real.sin β) ^ 2 +
        Real.sin γ / P * (Real.sin α + Real.cos β) ^ 2 +
        Real.sin γ / P * (Real.cos α + Real.sin β) ^ 2 =
      2 / P * (Real.cos γ + Real.sin γ) + 2 / P * Real.cos (α + β - γ) := by
  rw [Real.cos_sub, Real.cos_add, Real.sin_add]
  linear_combination (Real.cos γ / P + Real.sin γ / P) * Real.sin_sq_add_cos_sq α +
    (Real.cos γ / P + Real.sin γ / P) * Real.sin_sq_add_cos_sq β

/-- The Dirichlet kernel: `sin (x / 2) (1 + 2 ∑ κ = 1..n, cos (κ x)) = sin ((n + 1 / 2) x)`. -/
private theorem sin_half_mul_one_add_two_mul_sum_cos (x : ℝ) :
    ∀ n : ℕ, Real.sin (x / 2) * (1 + 2 * ∑ κ ∈ range n, Real.cos ((κ + 1 : ℝ) * x)) =
      Real.sin ((n + 1 / 2 : ℝ) * x)
  | 0 => by
    rw [sum_range_zero, mul_zero, add_zero, mul_one]
    congr 1
    push_cast
    ring
  | n + 1 => by
    have ih := sin_half_mul_one_add_two_mul_sum_cos x n
    have h1 : ((n + 1 : ℕ) + 1 / 2 : ℝ) * x = (n + 1 : ℝ) * x + x / 2 := by push_cast; ring
    have h2 : (n + 1 / 2 : ℝ) * x = (n + 1 : ℝ) * x - x / 2 := by ring
    rw [sum_range_succ, h1, Real.sin_add]
    rw [h2, Real.sin_sub] at ih
    linear_combination ih

/-- Orthogonality in the form the Fourier fit uses: for `p = 2 n + 1` and an integer `m`, the sum
`1 + 2 ∑ κ = 1..n, cos (2π κ m / p)` is `p` when `p` divides `m` and `0` otherwise. -/
private theorem one_add_two_mul_sum_cos (n : ℕ) (m : ℤ) :
    1 + 2 * ∑ κ ∈ range n, Real.cos ((κ + 1 : ℝ) * (2 * π * m / (2 * n + 1 : ℕ))) =
      if ((2 * n + 1 : ℕ) : ℤ) ∣ m then ((2 * n + 1 : ℕ) : ℝ) else 0 := by
  have hp : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  split_ifs with hdvd
  · obtain ⟨q, rfl⟩ := hdvd
    have hcos : ∀ κ ∈ range n,
        Real.cos ((κ + 1 : ℝ) * (2 * π * ((2 * n + 1 : ℕ) * q : ℤ) / (2 * n + 1 : ℕ))) = 1 := by
      intro κ _
      rw [show (κ + 1 : ℝ) * (2 * π * (((2 * n + 1 : ℕ) * q : ℤ) : ℝ) / (2 * n + 1 : ℕ)) =
        (((κ + 1 : ℕ) * q : ℤ) : ℝ) * (2 * π) by push_cast; field_simp]
      exact Real.cos_int_mul_two_pi _
    rw [sum_congr rfl hcos]
    simp
    ring
  · have hkernel := sin_half_mul_one_add_two_mul_sum_cos (2 * π * m / (2 * n + 1 : ℕ)) n
    have hpi : (n + 1 / 2 : ℝ) * (2 * π * m / (2 * n + 1 : ℕ)) = m * π := by
      push_cast
      field_simp
    rw [hpi, Real.sin_int_mul_pi] at hkernel
    refine (mul_eq_zero.1 hkernel).resolve_left fun hsin => hdvd ?_
    obtain ⟨q, hq⟩ := Real.sin_eq_zero_iff.1 hsin
    refine ⟨q, ?_⟩
    have hreal : (m : ℝ) = ((2 * n + 1 : ℕ) : ℝ) * q := by
      have hπ := Real.pi_pos.ne'
      field_simp at hq
      push_cast at hq ⊢
      linarith
    exact_mod_cast hreal

/-- **The Fourier fit is an exact fit**, for every odd `p`. [MAISA6, Lemma 4.2] states this
for odd `p ≥ 3`. -/
theorem isExactFit_fourierFit (hp : Odd p) : IsExactFit (fourierFit p) := by
  intro a b c
  obtain ⟨n, hn⟩ := hp
  have hn' : (p - 1) / 2 = n := by omega
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  -- The contributions, one frequency at a time.
  have hfreq : ∀ k : Fin ((p - 1) / 2), ∑ i : Fin 4,
      contribution (fourierFit p) (some (k, i)) a b c =
        2 / p * (cosTable p (k + 1) c + sinTable p (k + 1) c) +
          2 / p * Real.cos (((k : ℕ) + 1 : ℝ) *
            (2 * π * ((a.val + b.val - c.val : ℤ) : ℝ) / p)) := by
    intro k
    simp only [Fin.sum_univ_four, contribution, fourierFit, left_mk, right_mk, out_mk,
      fourierLeft, fourierRight, fourierOut, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Pi.neg_apply, cosTable, sinTable]
    rw [four_neurons]
    congr 2
    push_cast
    field_simp
  have hconst : contribution (fourierFit p) none a b c =
      1 / p - 2 / p * ∑ k : Fin ((p - 1) / 2), (cosTable p (k + 1) c + sinTable p (k + 1) c) := by
    simp only [contribution, fourierFit, left_mk, right_mk, out_mk, fourierLeft, fourierRight,
      fourierOut]
    norm_num
  have hsplit : ∑ k : Fin ((p - 1) / 2),
      (2 / p * (cosTable p (k + 1) c + sinTable p (k + 1) c) +
        2 / p * Real.cos (((k : ℕ) + 1 : ℝ) *
          (2 * π * ((a.val + b.val - c.val : ℤ) : ℝ) / p))) =
      2 / p * ∑ k : Fin ((p - 1) / 2), (cosTable p (k + 1) c + sinTable p (k + 1) c) +
        2 / p * ∑ k : Fin ((p - 1) / 2), Real.cos (((k : ℕ) + 1 : ℝ) *
          (2 * π * ((a.val + b.val - c.val : ℤ) : ℝ) / p)) := by
    rw [sum_add_distrib, mul_sum, mul_sum]
  rw [net, Fintype.sum_option, Fintype.sum_prod_type, hconst, sum_congr rfl fun k _ => hfreq k,
    hsplit]
  -- What is left is the Fourier expansion of the target.
  have hsum : ∑ k : Fin ((p - 1) / 2), Real.cos (((k : ℕ) + 1 : ℝ) *
      (2 * π * ((a.val + b.val - c.val : ℤ) : ℝ) / p)) =
      ∑ κ ∈ range n, Real.cos ((κ + 1 : ℝ) *
        (2 * π * ((a.val + b.val - c.val : ℤ) : ℝ) / p)) := by
    rw [Fin.sum_univ_eq_sum_range (fun κ => Real.cos ((κ + 1 : ℝ) *
      (2 * π * ((a.val + b.val - c.val : ℤ) : ℝ) / p))), hn']
  have hpR' : ((2 * n + 1 : ℕ) : ℝ) = p := by rw [hn]
  have hdvd : ((2 * n + 1 : ℕ) : ℤ) ∣ (a.val + b.val - c.val : ℤ) ↔ c = a + b := by
    rw [← hn, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, sub_eq_zero,
      eq_comm]
  have horth := one_add_two_mul_sum_cos n (a.val + b.val - c.val : ℤ)
  simp only [hdvd, hpR'] at horth
  rw [hsum, target]
  have key : ∀ S₁ S₂ : ℝ, 1 / p - 2 / p * S₁ + (2 / p * S₁ + 2 / p * S₂) =
      (1 + 2 * S₂) / p := fun S₁ S₂ => by ring
  rw [key, horth]
  split_ifs
  · exact div_self hpR
  · exact zero_div _

omit [NeZero p] in
/-- **Every neuron of the Fourier fit has single-frequency form**: the constant neuron with
frequency `0`, and the four neurons of frequency `k` with that frequency. -/
theorem isSingleFrequency_fourierFit (j : FourierIndex p) :
    IsSingleFrequency (fourierFit p) j := by
  match j with
  | none => exact ⟨0, const_mem_freqSpace p 0 _, const_mem_freqSpace p 0 _⟩
  | some (k, i) =>
    refine ⟨k + 1, ?_, ?_⟩
    · fin_cases i
      · exact cosTable_mem_freqSpace p _
      · exact sinTable_mem_freqSpace p _
      · exact sinTable_mem_freqSpace p _
      · exact cosTable_mem_freqSpace p _
    · fin_cases i
      · exact cosTable_mem_freqSpace p _
      · exact Submodule.neg_mem _ (sinTable_mem_freqSpace p _)
      · exact cosTable_mem_freqSpace p _
      · exact sinTable_mem_freqSpace p _

end Cslib.MachineLearning.ModularAddition
