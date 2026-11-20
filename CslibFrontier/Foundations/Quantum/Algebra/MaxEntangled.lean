/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Involution
public import CslibFrontier.Foundations.Quantum.Bell

/-!
# Local observables on the maximally entangled state

On a bipartite system `ℂ^ι ⊗ ℂ^κ`, an observable `M` of the first party acts as `M ⊗ 1` and one of
the second party as `1 ⊗ M`; both embeddings are star-algebra homomorphisms
(`Cslib.Quantum.kroneckerOne`, `Cslib.Quantum.oneKronecker`), so they carry measurements and the
relations between observables from one system to the bipartite one.

On the maximally entangled state `Φ = |ι|^{-1/2} ∑_i |i, i⟩`, the first party's observable can be
moved to the second party by transposition: for every `±1` observable `O`, `O ⊗ 1` and `1 ⊗ Oᵀ`
are `0`-close in the vector state of `Φ`
(`Cslib.Quantum.AlgState.kroneckerOne_approx_oneKronecker_transpose`), because
`⟨Φ|O ⊗ Oᵀ|Φ⟩ = Tr(OO)/|ι| = 1`. This is the agreement that makes the strategies of nonlocal games
built from operator solutions perfect.

## Main definitions

* `Cslib.Quantum.kroneckerOne`, `Cslib.Quantum.oneKronecker`: the local embeddings.

## Main results

* `Cslib.Quantum.AlgState.kroneckerOne_approx_oneKronecker_transpose`: on the maximally entangled
  state, `O ⊗ 1` agrees perfectly with `1 ⊗ Oᵀ`.
-/

@[expose] public section

namespace Cslib.Quantum

open Matrix
open scoped Kronecker MatrixOrder ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The embedding `M ↦ M ⊗ 1` of the first party's observables. -/
noncomputable def kroneckerOne : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix (ι × κ) (ι × κ) ℂ where
  toFun M := M ⊗ₖ 1
  map_one' := one_kronecker_one
  map_mul' M N := by rw [← mul_kronecker_mul, Matrix.mul_one]
  map_zero' := zero_kronecker _
  map_add' M N := add_kronecker _ _ _
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, smul_kronecker, one_kronecker_one]
  map_star' M := by
    change Mᴴ ⊗ₖ 1 = (M ⊗ₖ 1)ᴴ
    rw [conjTranspose_kronecker, conjTranspose_one]

/-- The embedding `M ↦ 1 ⊗ M` of the second party's observables. -/
noncomputable def oneKronecker : Matrix κ κ ℂ →⋆ₐ[ℂ] Matrix (ι × κ) (ι × κ) ℂ where
  toFun M := 1 ⊗ₖ M
  map_one' := one_kronecker_one
  map_mul' M N := by rw [← mul_kronecker_mul, Matrix.mul_one]
  map_zero' := kronecker_zero _
  map_add' M N := kronecker_add _ _ _
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, kronecker_smul, one_kronecker_one]
  map_star' M := by
    change 1 ⊗ₖ Mᴴ = (1 ⊗ₖ M)ᴴ
    rw [conjTranspose_kronecker, conjTranspose_one]

@[simp]
theorem kroneckerOne_apply (M : Matrix ι ι ℂ) : (kroneckerOne (κ := κ) M) = M ⊗ₖ 1 :=
  rfl

@[simp]
theorem oneKronecker_apply (M : Matrix κ κ ℂ) : (oneKronecker (ι := ι) M) = 1 ⊗ₖ M :=
  rfl

/-- The two parties' observables commute. -/
theorem commute_kroneckerOne_oneKronecker (M : Matrix ι ι ℂ) (N : Matrix κ κ ℂ) :
    Commute (kroneckerOne M) (oneKronecker N) := by
  simp only [kroneckerOne_apply, oneKronecker_apply, Commute, SemiconjBy, ← mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]

namespace AlgState

/-- **The transpose trick**: on the maximally entangled state, a `±1` observable `O` of the
first party agrees perfectly with the observable `Oᵀ` of the second. -/
theorem kroneckerOne_approx_oneKronecker_transpose [Nonempty ι] {O : Matrix ι ι ℂ}
    (hO : O.IsHermitian) (hO' : O * O = 1) :
    kroneckerOne O ≈[vector (maxEntangled ι) (norm_maxEntangled); 0] oneKronecker Oᵀ := by
  set φ := vector (maxEntangled ι) (norm_maxEntangled (ι := ι))
  set X : Matrix (ι × ι) (ι × ι) ℂ := O ⊗ₖ 1
  set Y : Matrix (ι × ι) (ι × ι) ℂ := 1 ⊗ₖ Oᵀ
  have hX : star X = X := by
    change (O ⊗ₖ 1)ᴴ = O ⊗ₖ 1
    rw [conjTranspose_kronecker, hO.eq, conjTranspose_one]
  have hY : star Y = Y := by
    change (1 ⊗ₖ Oᵀ)ᴴ = 1 ⊗ₖ Oᵀ
    rw [conjTranspose_kronecker, conjTranspose_one,
      conjTranspose_transpose_eq_transpose_conjTranspose, hO.eq]
  have hXX : X * X = 1 := by
    change O ⊗ₖ 1 * O ⊗ₖ 1 = 1
    rw [← mul_kronecker_mul, hO', Matrix.mul_one, one_kronecker_one]
  have hYY : Y * Y = 1 := by
    change 1 ⊗ₖ Oᵀ * 1 ⊗ₖ Oᵀ = 1
    rw [← mul_kronecker_mul, ← transpose_mul, hO', transpose_one, Matrix.mul_one,
      one_kronecker_one]
  have hXY : X * Y = O ⊗ₖ Oᵀ := by
    change O ⊗ₖ 1 * 1 ⊗ₖ Oᵀ = O ⊗ₖ Oᵀ
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hYX : Y * X = O ⊗ₖ Oᵀ := by
    change 1 ⊗ₖ Oᵀ * O ⊗ₖ 1 = O ⊗ₖ Oᵀ
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hcorr : φ (O ⊗ₖ Oᵀ) = 1 := by
    change star (maxEntangled ι).ofLp ⬝ᵥ ((O ⊗ₖ Oᵀ) *ᵥ (maxEntangled ι).ofLp) = 1
    rw [star_maxEntangled_dotProduct_kronecker_mulVec_eq_trace, ← transpose_mul, hO',
      trace_transpose, trace_one, div_self (by exact_mod_cast Fintype.card_ne_zero)]
  have hsq : star (X - Y) * (X - Y) = 1 + 1 - (O ⊗ₖ Oᵀ + O ⊗ₖ Oᵀ) := by
    rw [star_sub, hX, hY, sub_mul, mul_sub, mul_sub, hXX, hYY, hXY, hYX]
    abel
  rw [Approx, norm_eq_sqrt, show kroneckerOne O - oneKronecker Oᵀ = X - Y from rfl, hsq]
  simp [map_sub, map_add, hcorr]

end AlgState

end Cslib.Quantum
