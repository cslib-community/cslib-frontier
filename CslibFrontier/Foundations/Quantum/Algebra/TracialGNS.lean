/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.AlgState

/-!
# Right multiplication in the GNS space of a tracial state

For a trace, taking adjoints preserves the state seminorm. Right multiplication is consequently
bounded by the same argument as left multiplication and gives a representation of the opposite
algebra on the GNS completion. The left and right representations commute.

## Main definitions

* `Cslib.Quantum.AlgState.IsTracial`: the trace identity for a state.
* `Cslib.Quantum.AlgState.gnsRight`: the right representation on the GNS completion.

## Main results

* `Cslib.Quantum.AlgState.commute_gnsLeft_gnsRight`: the two GNS actions commute.
-/

public section

open scoped ComplexOrder InnerProductSpace
open UniformSpace Completion ContinuousLinearMap MulOpposite

namespace Cslib.Quantum.AlgState

/-- A state is tracial if it is invariant under exchanging two factors in its argument. -/
@[expose] def IsTracial {A : Type*} [Ring A] [PartialOrder A] [Algebra ℂ A]
    (φ : AlgState A) : Prop :=
  ∀ x y, φ (x * y) = φ (y * x)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (φ : AlgState A)

private theorem norm_star_of_isTracial (hφ : φ.IsTracial) (x : A) : φ.norm (star x) = φ.norm x := by
  rw [norm_eq_sqrt, norm_eq_sqrt, star_star, hφ x (star x)]

private noncomputable def rightMulPreGNS (hφ : φ.IsTracial) (a : A) :
    φ.toPositiveLinearMap.PreGNS →L[ℂ] φ.toPositiveLinearMap.PreGNS :=
  (φ.toPreGNS.toLinearMap ∘ₗ (LinearMap.mul ℂ A).flip a ∘ₗ
    φ.toPreGNS.symm.toLinearMap).mkContinuous
    ‖φ.toPositiveLinearMap.leftMulMapPreGNS (star a)‖ fun z => by
      obtain ⟨x, rfl⟩ := φ.toPreGNS.surjective z
      change φ.norm (x * a) ≤ _ * φ.norm x
      rw [← norm_star_of_isTracial φ hφ (x * a), star_mul,
        ← norm_star_of_isTracial φ hφ x]
      exact (φ.toPositiveLinearMap.leftMulMapPreGNS (star a)).le_opNorm (φ.toPreGNS (star x))

private theorem rightMulPreGNS_toPreGNS (hφ : φ.IsTracial) (a x : A) :
    rightMulPreGNS φ hφ a (φ.toPreGNS x) = φ.toPreGNS (x * a) := by
  simp [rightMulPreGNS]

private theorem gns_ext {T R : φ.toPositiveLinearMap.GNS →L[ℂ] φ.toPositiveLinearMap.GNS}
    (h : ∀ x : A, T (φ.toPreGNS x) = R (φ.toPreGNS x)) : T = R := by
  ext z
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq T.continuous R.continuous
  | ih z =>
    obtain ⟨x, rfl⟩ := φ.toPreGNS.surjective z
    exact h x

/-- Right multiplication in the GNS space, as a star-algebra homomorphism from the opposite
algebra. The left action is Mathlib's `PositiveLinearMap.gnsStarAlgHom`. -/
noncomputable def gnsRight (hφ : φ.IsTracial) :
    Aᵐᵒᵖ →⋆ₐ[ℂ] (φ.toPositiveLinearMap.GNS →L[ℂ] φ.toPositiveLinearMap.GNS) where
  toFun a := (rightMulPreGNS φ hφ a.unop).completion
  map_zero' := by
    apply gns_ext φ
    intro x
    simp [rightMulPreGNS_toPreGNS]
  map_one' := by
    apply gns_ext φ
    intro x
    simp [rightMulPreGNS_toPreGNS]
  map_add' a b := by
    apply gns_ext φ
    intro x
    simp [rightMulPreGNS_toPreGNS, mul_add, Completion.coe_add]
  map_mul' a b := by
    apply gns_ext φ
    intro x
    simp [rightMulPreGNS_toPreGNS, mul_assoc]
  commutes' r := by
    apply gns_ext φ
    intro x
    simp [rightMulPreGNS_toPreGNS, Algebra.algebraMap_eq_smul_one,
        ← Completion.coe_smul]
  map_star' a := by
    refine (eq_adjoint_iff _ _).mpr ?_
    intro x y
    induction x, y using Completion.induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x y =>
      obtain ⟨u, rfl⟩ := φ.toPreGNS.surjective x
      obtain ⟨v, rfl⟩ := φ.toPreGNS.surjective y
      simp only [unop_star, completion_apply_coe, rightMulPreGNS_toPreGNS, Completion.inner_coe,
        inner_toPreGNS, star_mul, star_star]
      rw [mul_assoc, hφ a.unop (star u * v), mul_assoc]

/-- Right multiplication acts on the dense copy of the algebra by `x ↦ x * a`. -/
@[simp] theorem gnsRight_toPreGNS (hφ : φ.IsTracial) (a x : A) :
    φ.gnsRight hφ (op a) (φ.toPreGNS x) =
      (φ.toPreGNS (x * a) : φ.toPositiveLinearMap.GNS) := by
  simp [gnsRight, rightMulPreGNS_toPreGNS]

/-- The GNS left action on the dense copy of the state algebra. -/
theorem gnsStarAlgHom_toPreGNS (a x : A) :
    φ.toPositiveLinearMap.gnsStarAlgHom a (φ.toPreGNS x) =
      (φ.toPreGNS (a * x) : φ.toPositiveLinearMap.GNS) := by
  simp [PositiveLinearMap.gnsStarAlgHom, AlgState.toPreGNS]

/-- The GNS left and right actions commute. -/
theorem commute_gnsLeft_gnsRight (hφ : φ.IsTracial) (a b : A) :
    Commute (φ.toPositiveLinearMap.gnsStarAlgHom a) (φ.gnsRight hφ (op b)) := by
  change φ.toPositiveLinearMap.gnsStarAlgHom a * φ.gnsRight hφ (op b) =
    φ.gnsRight hφ (op b) * φ.toPositiveLinearMap.gnsStarAlgHom a
  apply gns_ext φ
  intro x
  change φ.toPositiveLinearMap.gnsStarAlgHom a (φ.gnsRight hφ (op b) (φ.toPreGNS x)) =
    φ.gnsRight hφ (op b) (φ.toPositiveLinearMap.gnsStarAlgHom a (φ.toPreGNS x))
  rw [gnsRight_toPreGNS, gnsStarAlgHom_toPreGNS, gnsStarAlgHom_toPreGNS,
    gnsRight_toPreGNS, mul_assoc]

end Cslib.Quantum.AlgState
