/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.CStar
public import CslibFrontier.Foundations.Quantum.Algebra.Expect
public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.BooleanAnalysis.HadamardRectangles

/-!
# Character observables of measurements with bit-string outcomes

A measurement `M` with outcomes `x ∈ {0,1}ⁿ` defines the **character observables**
`χ_M(a) = ∑_x (-1)^{a·x} M_x` (`Cslib.Quantum.Measurement.charObs`), its Walsh–Fourier
transform, for a supplied measurement with full-bit-string outcomes.

These are *not* the averaged marginals of a strategy in
[Natarajan and Vidick, §4.1, eq. (11)][NatarajanVidick2017] (arXiv:1610.03574v1, p. 18). Those
average a query-dependent measurement over the other query and the other answer. For example, a
strategy that always answers `-1` has marginal `-1` at `a = 0`, while `χ_M(0) = 1` for every `M`.
Constructing such a measurement from a strategy's query-dependent measurements, comparing its
characters with the strategy's marginals, and bounding the defect by the winning probability are
tracked in [#6149](https://github.com/cslib-community/cslib-frontier/issues/6149) (milestone M3).

* For a **projective** measurement they are self-adjoint unitaries and *exactly* linear,
  `χ(a) χ(a') = χ(a + a')` (`Cslib.Quantum.Measurement.IsProjective.charObs_mul`,
  `Cslib.Quantum.Measurement.IsProjective.charObs_mem_unitary`). So, as families `X` or `Z`, they
  satisfy the unitarity hypotheses of the Pauli-family defect bound
  (`Cslib.Quantum.expect_norm_pauliFamily_sub_sq_le`) with linearity defect `0`.
* **Parseval in a state** (`Cslib.Quantum.expect_norm_walshSum_sq`):
  `E_a ‖∑_x (-1)^{a·x} D(x)‖²_φ = ∑_x ‖D(x)‖²_φ` for any family `D`, by orthogonality of the
  characters. So closeness of two measurements, `∑_x ‖M_x - P_x‖²_φ`, is exactly the average
  closeness of their character observables.

## Main definitions

* `Cslib.Quantum.walshSum`: `a ↦ ∑_x (-1)^{a·x} D(x)`.
* `Cslib.Quantum.Measurement.charObs`: the character observables of a measurement.

## Main results

* `Cslib.Quantum.expect_norm_walshSum_sq`: Parseval in a state.
* `Cslib.Quantum.Measurement.IsProjective.charObs_mul`: exact linearity for projective
  measurements.
* `Cslib.Quantum.Measurement.IsProjective.charObs_mem_unitary`: unitarity.

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

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The **Walsh sum** `∑_x (-1)^{a·x} D(x)` of a family indexed by bit strings. -/
noncomputable def walshSum (D : (ι → Bool) → A) (a : ι → Bool) : A :=
  ∑ x, (signVal (a ⬝ᵥ x) : ℂ) • D x

theorem walshSum_sub (D D' : (ι → Bool) → A) (a : ι → Bool) :
    walshSum D a - walshSum D' a = walshSum (D - D') a := by
  simp only [walshSum, ← sum_sub_distrib, ← smul_sub, Pi.sub_apply]

theorem walshSum_zero (D : (ι → Bool) → A) : walshSum D 0 = ∑ x, D x := by
  have h0 : signVal (0 : Bool) = 1 := signVal_false
  simp [walshSum, zero_dotProduct, h0]

end Ring

section State

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A] [SelfAdjointDecompose A]

/-- **Parseval in a state**: `∑_a ‖∑_x (-1)^{a·x} D(x)‖²_φ = 2ⁿ ∑_x ‖D(x)‖²_φ`. -/
theorem sum_norm_walshSum_sq (φ : AlgState A) (D : (ι → Bool) → A) :
    ∑ a, φ.norm (walshSum D a) ^ 2 = 2 ^ Fintype.card ι * ∑ x, φ.norm (D x) ^ 2 := by
  have key : ∀ a, ((φ.norm (walshSum D a) ^ 2 : ℝ) : ℂ) =
      ∑ x, ∑ y, ((signVal (a ⬝ᵥ x) * signVal (a ⬝ᵥ y) : ℝ) : ℂ) * φ (star (D x) * D y) := by
    intro a
    rw [AlgState.ofReal_norm_sq, walshSum, star_sum, sum_mul, map_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum, map_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_smul_comm, map_smul,
      smul_eq_mul]
    push_cast; ring
  have horth : ∀ x y : ι → Bool,
      ∑ a : ι → Bool, ((signVal (a ⬝ᵥ x) * signVal (a ⬝ᵥ y) : ℝ) : ℂ) =
        if x = y then (2 : ℂ) ^ Fintype.card ι else 0 := fun x y => by
    have h := sum_signVal_dotProduct_mul_signVal_dotProduct x y
    simp only [dotProduct_comm x, dotProduct_comm y] at h
    rw [← Complex.ofReal_sum, h]
    split_ifs <;> push_cast <;> rfl
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp only [key]
  rw [sum_comm]
  have hx : ∀ x, ∑ a : ι → Bool, ∑ y, ((signVal (a ⬝ᵥ x) * signVal (a ⬝ᵥ y) : ℝ) : ℂ) *
      φ (star (D x) * D y) = (2 : ℂ) ^ Fintype.card ι * φ (star (D x) * D x) := fun x => by
    rw [sum_comm]
    simp only [← sum_mul, horth, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  rw [sum_congr rfl fun x _ => hx x, Complex.ofReal_mul, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [AlgState.ofReal_norm_sq]
  push_cast
  rfl

/-- **Parseval in a state**, averaged: `E_a ‖∑_x (-1)^{a·x} D(x)‖²_φ = ∑_x ‖D(x)‖²_φ`. -/
theorem expect_norm_walshSum_sq (φ : AlgState A) (D : (ι → Bool) → A) :
    𝔼 a, φ.norm (walshSum D a) ^ 2 = ∑ x, φ.norm (D x) ^ 2 := by
  rw [Fintype.expect_eq_sum_div_card, sum_norm_walshSum_sq, Fintype.card_fun, Fintype.card_bool]
  push_cast
  field_simp

end State

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The **character observable** `χ_M(a) = ∑_x (-1)^{a·x} M_x` of a measurement with bit-string
outcomes. -/
noncomputable def Measurement.charObs (M : Measurement (ι → Bool) A) (a : ι → Bool) : A :=
  walshSum M.effect a

namespace Measurement

variable (M : Measurement (ι → Bool) A)

omit [StarOrderedRing A] in
theorem charObs_zero : M.charObs 0 = 1 := by
  rw [charObs, walshSum_zero, M.sum_effect]

theorem isSelfAdjoint_charObs (a : ι → Bool) : IsSelfAdjoint (M.charObs a) := by
  refine isSelfAdjoint_sum _ fun x _ => ?_
  exact (show IsSelfAdjoint ((signVal (a ⬝ᵥ x) : ℂ)) from Complex.conj_ofReal _).smul
    (M.nonneg x).isSelfAdjoint

variable {M}

/-- The character observables of a **projective** measurement are exactly linear. -/
theorem IsProjective.charObs_mul (hM : M.IsProjective) (a a' : ι → Bool) :
    M.charObs a * M.charObs a' = M.charObs (a + a') := by
  rw [charObs, charObs, charObs, walshSum, walshSum, hM.sum_smul_mul_sum_smul, walshSum]
  refine sum_congr rfl fun x _ => ?_
  rw [add_dotProduct, show (a ⬝ᵥ x + a' ⬝ᵥ x) = (a ⬝ᵥ x ^^ a' ⬝ᵥ x) from rfl, signVal_xor]
  push_cast; rfl

/-- The character observables of a projective measurement are unitary. -/
theorem IsProjective.charObs_mem_unitary (hM : M.IsProjective) (a : ι → Bool) :
    M.charObs a ∈ unitary A := by
  have hsq : M.charObs a * M.charObs a = 1 := by
    rw [hM.charObs_mul, BitString.add_self, charObs_zero]
  rw [Unitary.mem_iff, (M.isSelfAdjoint_charObs a).star_eq]
  exact ⟨hsq, hsq⟩

end Measurement

end CStar

end Cslib.Quantum
