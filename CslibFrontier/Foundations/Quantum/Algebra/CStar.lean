/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Approx
public import CslibFrontier.Foundations.Quantum.Algebra.Consistency
public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# States and measurements in C⋆-algebras

In a C⋆-algebra the state norm is controlled by the C⋆-norm: `‖cx‖_φ ≤ ‖c‖ ‖x‖_φ`
(`Cslib.Quantum.AlgState.norm_mul_le`), because `c⋆c ≤ ‖c‖²`. So closeness in a state survives
left multiplication by any operator, at the price of its norm
(`Cslib.Quantum.AlgState.Approx.mul_left_norm`), and `0`-closeness survives it outright. An effect
with expectation `0` is `0`-close to `0` (`Cslib.Quantum.AlgState.approx_zero_of_apply_eq_zero`).

The effects of a projective measurement are pairwise orthogonal
(`Cslib.Quantum.Measurement.IsProjective.mul_eq_zero`): from `E_a = E_a (∑_c E_c) E_a` the
nonnegative terms `E_a E_c E_a = (E_c E_a)⋆(E_c E_a)` with `c ≠ a` sum to `0`, so each vanishes,
and in a C⋆-algebra `x⋆x = 0` forces `x = 0`. Hence functions of one projective measurement
multiply pointwise (`Cslib.Quantum.Measurement.IsProjective.sum_smul_mul_sum_smul`).

## Main results

* `Cslib.Quantum.AlgState.norm_mul_le`: `‖cx‖_φ ≤ ‖c‖ ‖x‖_φ`.
* `Cslib.Quantum.AlgState.Approx.mul_left_norm`: left multiplication preserves closeness.
* `Cslib.Quantum.Measurement.IsProjective.mul_eq_zero`: orthogonality of projective effects.
* `Cslib.Quantum.Measurement.IsProjective.sum_smul_mul_sum_smul`: functions of a projective
  measurement multiply pointwise.
-/

public section

namespace Cslib.Quantum

open Finset

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace AlgState

variable (φ : AlgState A)

/-- In a C⋆-algebra, `‖cx‖_φ ≤ ‖c‖ ‖x‖_φ`. -/
theorem norm_mul_le (c x : A) : φ.norm (c * x) ≤ ‖c‖ * φ.norm x := by
  have h := star_left_conjugate_le_conjugate (CStarAlgebra.star_mul_le_algebraMap_norm_sq c) x
  rw [IsScalarTower.algebraMap_apply ℝ ℂ A, ← Algebra.commutes, mul_assoc] at h
  have h' := φ.re_apply_mono h
  rw [← Algebra.smul_def, smul_mul_assoc, map_smul, smul_eq_mul, Complex.coe_algebraMap,
    Complex.re_ofReal_mul, ← norm_sq] at h'
  rw [← sq_le_sq₀ (φ.norm_nonneg _) (mul_nonneg (_root_.norm_nonneg c) (φ.norm_nonneg x)), mul_pow,
    norm_sq]
  simpa [star_mul, mul_assoc] using h'

variable {φ} {a b : A} {δ : ℝ}

/-- Left multiplication by `c` turns `δ`-closeness into `‖c‖δ`-closeness. -/
theorem Approx.mul_left_norm (h : a ≈[φ; δ] b) (c : A) : c * a ≈[φ; ‖c‖ * δ] c * b :=
  h.mul_left_of_norm_mul_le (_root_.norm_nonneg c) (φ.norm_mul_le c)

/-- `0`-closeness survives left multiplication by any operator. -/
theorem Approx.mul_left_zero (h : a ≈[φ; 0] b) (c : A) : c * a ≈[φ; 0] c * b := by
  simpa using h.mul_left_norm c

/-- An effect with expectation `0` is `0`-close to `0`. -/
theorem approx_zero_of_apply_eq_zero {E : A} (h0 : 0 ≤ E) (h1 : E ≤ 1) (hE : φ E = 0) :
    E ≈[φ; 0] 0 := by
  have := φ.re_apply_mono (mul_self_le_self_of_nonneg_of_le_one h0 h1)
  rw [hE, Complex.zero_re] at this
  rw [Approx, sub_zero, norm_eq_sqrt, h0.isSelfAdjoint.star_eq, Real.sqrt_eq_zero'.mpr this]

end AlgState

namespace Measurement

variable {α : Type*} [Fintype α] {M : Measurement α A}

/-- **The effects of a projective measurement are orthogonal.** -/
theorem IsProjective.mul_eq_zero (hM : M.IsProjective) {a b : α} (hab : a ≠ b) :
    M.effect a * M.effect b = 0 := by
  classical
  have hsa : ∀ c, star (M.effect c) = M.effect c := fun c => (M.nonneg c).isSelfAdjoint.star_eq
  -- `E_a = E_a (∑_c E_c) E_a` splits off `E_a` and leaves the nonnegative terms `E_a E_c E_a`.
  have hsum : ∑ c ∈ univ.erase a, M.effect a * M.effect c * M.effect a = 0 := by
    have h := congrArg (fun x => M.effect a * x * M.effect a) M.sum_effect
    simp only [mul_one, hM a, mul_sum, sum_mul] at h
    rw [← add_sum_erase _ _ (mem_univ a), hM a, hM a] at h
    exact add_eq_left.mp h
  have hterm : ∀ c, M.effect a * M.effect c * M.effect a =
      star (M.effect c * M.effect a) * (M.effect c * M.effect a) := fun c => by
    rw [star_mul, hsa, hsa, ← mul_assoc (M.effect a * M.effect c),
      mul_assoc (M.effect a) (M.effect c) (M.effect c), hM c]
  have hnn : ∀ c ∈ univ.erase a, 0 ≤ M.effect a * M.effect c * M.effect a := fun c _ => by
    rw [hterm]; exact star_mul_self_nonneg _
  have hb := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum b (mem_erase.mpr ⟨hab.symm, mem_univ b⟩)
  rw [hterm, star_mul_self_eq_zero] at hb
  rw [← hsa a, ← hsa b, ← star_mul, hb, star_zero]

/-- Functions of a projective measurement multiply pointwise:
`(∑_a f(a) E_a)(∑_a g(a) E_a) = ∑_a f(a) g(a) E_a`. -/
theorem IsProjective.sum_smul_mul_sum_smul (hM : M.IsProjective) (f g : α → ℂ) :
    (∑ a, f a • M.effect a) * (∑ a, g a • M.effect a) = ∑ a, (f a * g a) • M.effect a := by
  classical
  rw [sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum, sum_eq_single a (fun b _ hb => by
    rw [smul_mul_smul_comm, hM.mul_eq_zero (Ne.symm hb), smul_zero]) (by simp),
    smul_mul_smul_comm, hM a]

/-- Coarse-graining a projective measurement keeps it projective. -/
theorem IsProjective.map {β : Type*} [Fintype β] [DecidableEq β] (hM : M.IsProjective)
    (f : α → β) : (M.map f).IsProjective := fun b => by
  classical
  simp only [map_effect, sum_mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_eq_single a (fun c _ hc => hM.mul_eq_zero (Ne.symm hc)) (fun ha' => ha'.elim
    ‹a ∈ _›), hM a]

end Measurement

end Cslib.Quantum
