/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.CharacterFamily
import CslibFrontier.Foundations.BooleanAnalysis.HadamardRectangles

/-!
# The Fourier measurement of a family of observables

Let `A(a)`, for `a ∈ {0,1}ⁿ`, be `±1` observables: self-adjoint with `A(a)² = 1`. Their
**Fourier coefficients** `Â(u) = E_a (-1)^{u·a} A(a)` (`Cslib.Quantum.fourierCoeff`) are
self-adjoint, and by Parseval their squares sum to `1`. So the squares form a measurement with
outcomes `u ∈ {0,1}ⁿ`, the **Fourier measurement** `B_u = Â(u)²`
(`Cslib.Quantum.fourierMeasurement`). It is the measurement in the proof of
[Natarajan and Vidick, §3, Theorem 10][NatarajanVidick2017] (arXiv:1610.03574v1), which rounds
approximately linear observables to exactly linear ones.

The sum `∑_u Â(u)³` is the average `E_{a,b} A(a) A(b) A(a + b)`
(`Cslib.Quantum.sum_fourierCoeff_cube`). So if this average is at least `1 - δ` in a state `φ`,
then, in that state:

* the Walsh sums `χ_B(a) = ∑_u (-1)^{a·u} B_u` of the Fourier measurement (its character
  observables) are close to the observables, `E_a ‖A(a) - χ_B(a)‖²_φ ≤ 2δ`
  (`Cslib.Quantum.expect_norm_sub_walshSum_sq_le`);
* the Fourier measurement is almost projective, `∑_u φ(B_u²) ≥ 1 - 2δ`
  (`Cslib.Quantum.one_sub_le_sum_fourierMeasurement_sq`).

Both hold in any star-ordered algebra and any state. The source instead dilates `B` to a projective
measurement on a larger space (Naimark). Orthogonalizing `B` in place, by de la Salle's theorem,
keeps the rounded observables in the algebra of `A`.

## Main definitions

* `Cslib.Quantum.fourierCoeff`: `Â(u) = E_a (-1)^{u·a} A(a)`.
* `Cslib.Quantum.fourierMeasurement`: the measurement `u ↦ Â(u)²`.

## Main results

* `Cslib.Quantum.sum_walshSum_mul_walshSum`: Parseval for products of Walsh sums.
* `Cslib.Quantum.sum_fourierCoeff_cube`: `∑_u Â(u)³ = E_{a,b} A(a) A(b) A(a + b)`.
* `Cslib.Quantum.expect_norm_sub_walshSum_sq_le`: the characters of the Fourier measurement are
  close to the observables.
* `Cslib.Quantum.one_sub_le_sum_fourierMeasurement_sq`: the Fourier measurement is almost
  projective.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

@[expose] public section

open Finset Cslib.BitString
open scoped BigOperators

namespace Cslib.Quantum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Ring

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- **Parseval for products of Walsh sums**:
`∑_u (∑_x (-1)^{u·x} f(x)) (∑_y (-1)^{u·y} g(y)) = 2ⁿ ∑_x f(x) g(x)`. -/
theorem sum_walshSum_mul_walshSum (f g : (ι → Bool) → R) :
    ∑ u, walshSum f u * walshSum g u = (2 : ℂ) ^ Fintype.card ι • ∑ x, f x * g x := by
  simp only [walshSum, sum_mul, mul_sum, smul_mul_smul_comm]
  rw [sum_comm]
  simp only [smul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  simp only [← sum_smul, ← Complex.ofReal_mul, sum_signVal_mul_signVal, ite_smul, zero_smul,
    sum_ite_eq', mem_univ, ite_true]

/-- A product of Walsh sums is the Walsh sum of a convolution:
`(∑_x (-1)^{u·x} f(x)) (∑_y (-1)^{u·y} g(y)) = ∑_z (-1)^{u·z} ∑_x f(x) g(x + z)`. -/
theorem walshSum_mul_walshSum (f g : (ι → Bool) → R) (u : ι → Bool) :
    walshSum f u * walshSum g u = walshSum (fun z => ∑ x, f x * g (x + z)) u := by
  simp only [walshSum, sum_mul, mul_sum, smul_mul_smul_comm, smul_sum]
  conv_rhs => rw [sum_comm]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← Equiv.sum_comp (Equiv.addLeft x)]
  refine sum_congr rfl fun z _ => ?_
  rw [Equiv.coe_addLeft, dotProduct_add,
    show (u ⬝ᵥ x + u ⬝ᵥ z) = (u ⬝ᵥ x ^^ u ⬝ᵥ z) from rfl, signVal_xor]
  have h : ((signVal (u ⬝ᵥ x) : ℝ) : ℂ) * (signVal (u ⬝ᵥ x) : ℝ) = 1 := by
    rw [← Complex.ofReal_mul, signVal_mul_self, Complex.ofReal_one]
  congr 1
  push_cast
  linear_combination ((signVal (u ⬝ᵥ z) : ℝ) : ℂ) * h

/-- The **Fourier coefficient** `Â(u) = E_a (-1)^{u·a} A(a)` of a family indexed by bit strings. -/
noncomputable def fourierCoeff (A : (ι → Bool) → R) (u : ι → Bool) : R :=
  (((2 : ℝ) ^ Fintype.card ι)⁻¹ : ℝ) • walshSum A u

/-- **Parseval**: the squares of the Fourier coefficients of `±1` observables sum to `1`. -/
theorem sum_fourierCoeff_mul_self {A : (ι → Bool) → R} (hA2 : ∀ a, A a * A a = 1) :
    ∑ u, fourierCoeff A u * fourierCoeff A u = 1 := by
  simp only [fourierCoeff, smul_mul_smul_comm, ← smul_sum, sum_walshSum_mul_walshSum, hA2,
    sum_const, card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Complex.coe_smul, smul_smul, Fintype.card_fun,
    Fintype.card_bool]
  convert one_smul ℂ (1 : R) using 2
  push_cast
  field_simp

/-- `∑_u Â(u)³ = E_{a,b} A(a) A(b) A(a + b)`. -/
theorem sum_fourierCoeff_cube (A : (ι → Bool) → R) :
    ∑ u, fourierCoeff A u * (fourierCoeff A u * fourierCoeff A u) =
      ((((2 : ℝ) ^ Fintype.card ι)⁻¹ ^ 2 : ℝ) : ℂ) • ∑ a, ∑ b, A a * A b * A (a + b) := by
  simp only [fourierCoeff, smul_mul_smul_comm, walshSum_mul_walshSum A A, ← smul_sum,
    sum_walshSum_mul_walshSum, mul_sum, ← mul_assoc]
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  · push_cast
    field_simp
  · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [add_comm b a]

/-- `E_a A(a) (∑_u (-1)^{a·u} D(u)) = ∑_u Â(u) D(u)`. -/
theorem smul_sum_mul_walshSum (A D : (ι → Bool) → R) :
    (((2 : ℝ) ^ Fintype.card ι)⁻¹ : ℝ) • ∑ a, A a * walshSum D a = ∑ u, fourierCoeff A u * D u := by
  simp only [fourierCoeff, walshSum, mul_sum, sum_mul, mul_smul_comm, smul_mul_assoc, smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => sum_congr rfl fun a _ => ?_
  rw [dotProduct_comm]

/-- `E_a (∑_u (-1)^{a·u} D(u)) A(a) = ∑_u D(u) Â(u)`. -/
theorem smul_sum_walshSum_mul (A D : (ι → Bool) → R) :
    (((2 : ℝ) ^ Fintype.card ι)⁻¹ : ℝ) • ∑ a, walshSum D a * A a = ∑ u, D u * fourierCoeff A u := by
  simp only [fourierCoeff, walshSum, mul_sum, sum_mul, mul_smul_comm, smul_mul_assoc, smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => sum_congr rfl fun a _ => ?_
  rw [dotProduct_comm]

end Ring

section State

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] {A : (ι → Bool) → R}

theorem isSelfAdjoint_walshSum {D : (ι → Bool) → R} (hD : ∀ x, IsSelfAdjoint (D x))
    (a : ι → Bool) : IsSelfAdjoint (walshSum D a) :=
  isSelfAdjoint_sum _ fun x _ =>
    (show IsSelfAdjoint ((signVal (a ⬝ᵥ x) : ℂ)) from Complex.conj_ofReal _).smul (hD x)

theorem isSelfAdjoint_fourierCoeff (hA : ∀ a, IsSelfAdjoint (A a)) (u : ι → Bool) :
    IsSelfAdjoint (fourierCoeff A u) :=
  (show IsSelfAdjoint (((((2 : ℝ) ^ Fintype.card ι)⁻¹ : ℝ)) : ℂ) from Complex.conj_ofReal _).smul
    (isSelfAdjoint_walshSum hA u)

variable [PartialOrder R] [StarOrderedRing R]

/-- The **Fourier measurement** `u ↦ Â(u)²` of a family of `±1` observables. -/
noncomputable def fourierMeasurement (A : (ι → Bool) → R) (hA : ∀ a, IsSelfAdjoint (A a))
    (hA2 : ∀ a, A a * A a = 1) : Measurement (ι → Bool) R where
  effect u := fourierCoeff A u * fourierCoeff A u
  nonneg u := by
    simpa only [(isSelfAdjoint_fourierCoeff hA u).star_eq] using
      star_mul_self_nonneg (fourierCoeff A u)
  sum_effect := sum_fourierCoeff_mul_self hA2

variable (hA : ∀ a, IsSelfAdjoint (A a)) (hA2 : ∀ a, A a * A a = 1)

theorem fourierMeasurement_effect (u : ι → Bool) :
    (fourierMeasurement A hA hA2).effect u = fourierCoeff A u * fourierCoeff A u :=
  rfl

/-- The Fourier measurement satisfies `B_u² ≤ B_u`: `B_u - B_u² = Â(u) (1 - B_u) Â(u)`, and
`B_u ≤ 1`. -/
theorem fourierMeasurement_mul_self_le (u : ι → Bool) :
    (fourierMeasurement A hA hA2).effect u * (fourierMeasurement A hA hA2).effect u ≤
      (fourierMeasurement A hA hA2).effect u := by
  set B := fourierMeasurement A hA hA2
  have h := star_left_conjugate_nonneg (sub_nonneg.mpr (B.effect_le_one u)) (fourierCoeff A u)
  rw [(isSelfAdjoint_fourierCoeff hA u).star_eq] at h
  rw [← sub_nonneg]
  convert h using 1
  simp only [B, fourierMeasurement_effect]
  noncomm_ring

variable (φ : AlgState R)

omit [StarRing R] [StarModule ℂ R] [StarOrderedRing R] in
private theorem re_apply_real_smul (r : ℝ) (x : R) : (φ (r • x)).re = r * (φ x).re := by
  rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul]

omit [StarRing R] [StarModule ℂ R] [StarOrderedRing R] in
/-- In a state, `Re φ(∑_u Â(u)³) = E_{a,b} Re φ(A(a) A(b) A(a + b))`. -/
theorem re_apply_sum_fourierCoeff_cube :
    (φ (∑ u, fourierCoeff A u * (fourierCoeff A u * fourierCoeff A u))).re =
      𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re := by
  rw [sum_fourierCoeff_cube, map_smul, smul_eq_mul, Complex.re_ofReal_mul, map_sum, Complex.re_sum]
  simp only [map_sum, Complex.re_sum, Fintype.expect_eq_sum_div_card, Fintype.card_fun,
    Fintype.card_bool, ← sum_div]
  push_cast
  field_simp

/-- **The Fourier measurement is almost projective.** If `E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - δ`,
then `∑_u Re φ(B_u²) ≥ 1 - 2δ`: `(B_u - Â(u))² ≥ 0` gives `B_u² ≥ 2 Â(u)³ - B_u`. -/
theorem one_sub_le_sum_fourierMeasurement_sq {δ : ℝ}
    (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re) :
    1 - 2 * δ ≤ ∑ u, (φ ((fourierMeasurement A hA hA2).effect u *
      (fourierMeasurement A hA hA2).effect u)).re := by
  set B := fourierMeasurement A hA hA2
  set F := fourierCoeff A
  have key : ∀ u, 2 * (φ (F u * (F u * F u))).re - (φ (B.effect u)).re ≤
      (φ (B.effect u * B.effect u)).re := by
    intro u
    have h := φ.re_apply_nonneg (star_mul_self_nonneg (B.effect u - F u))
    have e : star (B.effect u - F u) * (B.effect u - F u) =
        B.effect u * B.effect u - F u * (F u * F u) - F u * (F u * F u) + B.effect u := by
      rw [star_sub, (B.nonneg u).isSelfAdjoint.star_eq, (isSelfAdjoint_fourierCoeff hA u).star_eq]
      simp only [B, fourierMeasurement_effect, F]
      noncomm_ring
    rw [e, map_add, map_sub, map_sub, Complex.add_re, Complex.sub_re, Complex.sub_re] at h
    linarith
  have hB : ∑ u, (φ (B.effect u)).re = 1 := by
    rw [← Complex.re_sum, ← map_sum, B.sum_effect, φ.map_one, Complex.one_re]
  have hT := re_apply_sum_fourierCoeff_cube φ (A := A)
  rw [map_sum, Complex.re_sum] at hT
  have := sum_le_sum fun u (_ : u ∈ univ) => key u
  rw [sum_sub_distrib, ← mul_sum, hB] at this
  linarith

/-- **The characters of the Fourier measurement are close to the observables.** If
`E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - δ`, then `E_a ‖A(a) - ∑_u (-1)^{a·u} B_u‖²_φ ≤ 2δ`. -/
theorem expect_norm_sub_walshSum_sq_le [SelfAdjointDecompose R] {δ : ℝ}
    (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re) :
    𝔼 a, φ.norm (A a - walshSum (fourierMeasurement A hA hA2).effect a) ^ 2 ≤ 2 * δ := by
  set B := fourierMeasurement A hA hA2
  set F := fourierCoeff A
  set χ := walshSum B.effect
  have hBsa : ∀ u, IsSelfAdjoint (B.effect u) := fun u => (B.nonneg u).isSelfAdjoint
  have hχ : ∀ a, IsSelfAdjoint (χ a) := isSelfAdjoint_walshSum hBsa
  have hN : ∀ a, φ.norm (A a - χ a) ^ 2 =
      1 - (φ (A a * χ a)).re - (φ (χ a * A a)).re + φ.norm (χ a) ^ 2 := by
    intro a
    rw [φ.norm_sq, φ.norm_sq, star_sub, (hA a).star_eq, (hχ a).star_eq,
      sub_mul, mul_sub, mul_sub, hA2, map_sub, map_sub, map_sub, φ.map_one, Complex.sub_re,
      Complex.sub_re, Complex.sub_re, Complex.one_re]
    ring
  have hc : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hcard : (Fintype.card (ι → Bool) : ℝ) = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_bool]; push_cast; rfl
  have hT₁ : (φ (∑ u, F u * (F u * F u))).re =
      ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ a, (φ (A a * χ a)).re := by
    rw [← Complex.re_sum, ← map_sum, ← re_apply_real_smul, smul_sum_mul_walshSum]
    rfl
  have hT₂ : (φ (∑ u, F u * (F u * F u))).re =
      ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ a, (φ (χ a * A a)).re := by
    rw [← Complex.re_sum, ← map_sum, ← re_apply_real_smul, smul_sum_walshSum_mul]
    simp only [B, fourierMeasurement_effect, F, mul_assoc]
  have hP : 𝔼 a, φ.norm (χ a) ^ 2 ≤ 1 := by
    rw [expect_norm_walshSum_sq]
    calc ∑ u, φ.norm (B.effect u) ^ 2 ≤ ∑ u, (φ (B.effect u)).re := sum_le_sum fun u _ => by
          rw [φ.norm_sq, (hBsa u).star_eq]
          exact φ.re_apply_mono (fourierMeasurement_mul_self_le hA hA2 u)
      _ = 1 := by rw [← Complex.re_sum, ← map_sum, B.sum_effect, φ.map_one, Complex.one_re]
  have hT := re_apply_sum_fourierCoeff_cube φ (A := A)
  simp only [Fintype.expect_eq_sum_div_card, hcard] at hP hδ hT ⊢
  simp only [hN, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, hcard, nsmul_eq_mul,
    mul_one] at ⊢
  rw [hT₁] at hT
  have hT' : ∑ a, (φ (χ a * A a)).re = ∑ a, (φ (A a * χ a)).re := by
    have := hT₁.symm.trans hT₂
    field_simp at this
    linarith
  rw [hT']
  rw [div_le_iff₀ hc] at hP ⊢
  have : (2 : ℝ) ^ Fintype.card ι * (1 - δ) ≤ ∑ a, (φ (A a * χ a)).re := by
    rw [← hT] at hδ
    field_simp at hδ
    linarith
  linarith

end State

end Cslib.Quantum
