/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Orthogonalization
public import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled

/-!
# Local orthogonalization in a tensor-product strategy

In a tensor-product strategy, each party's measurements act on its own factor, and the joint state
lives on the product. Orthogonalization must keep each party's projective measurement *on its
factor*, so that the two parties' operators still commute. De la Salle's theorem
(`Cslib.Quantum.Measurement.exists_isProjective_sum_norm_sub_sq_le`) holds in *every* state of the
factor, so it suffices to pull the joint state back to the factor.

* `Cslib.Quantum.AlgState.comap` pulls a state back along a monotone star-algebra homomorphism `f`,
  with `‖a‖_{φ ∘ f} = ‖f a‖_φ` (`Cslib.Quantum.AlgState.norm_comap`). A star-algebra
  homomorphism out of `M_ι(ℂ)` into a star-ordered algebra is monotone (Mathlib's
  `StarRingHomClass.instOrderHomClass`), so pulling back along it carries orthogonalization from
  the factor into its image
  (`Cslib.Quantum.Measurement.exists_isProjective_sum_norm_map_sub_sq_le`).
* Applied to the local embeddings `M ↦ M ⊗ 1` and `M ↦ 1 ⊗ M`, both parties
  orthogonalize at once, into projective measurements whose operators commute across the parties
  (`Cslib.Quantum.Measurement.exists_isProjective_local`).
* Character observables are linear in the effects, so the local version of
  `Cslib.Quantum.Measurement.exists_isProjective_charObs` follows
  (`Cslib.Quantum.Measurement.exists_isProjective_charObs_kroneckerOne`).

This is a step toward the robust rigidity of tensor-product strategies of
[Natarajan and Vidick][NatarajanVidick2017] (arXiv:1610.03574v1), which works with projective
measurements of each party; the remaining steps toward `MIP* = RE` are tracked in
cslib-community/cslib-frontier#6149.

## Main results

* `Cslib.Quantum.Measurement.exists_isProjective_sum_norm_map_sub_sq_le`: orthogonalization
  through a star-algebra homomorphism.
* `Cslib.Quantum.Measurement.exists_isProjective_local`: simultaneous local orthogonalization of
  both parties' measurements, with commuting projective measurements.
* `Cslib.Quantum.Measurement.exists_isProjective_charObs_kroneckerOne`: unitary, exactly linear
  local character observables.

## References

* [M. de la Salle, *Orthogonalization of positive operator valued measures*][delaSalle2022]
* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker MatrixOrder ComplexOrder BigOperators

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

namespace Measurement

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Orthogonalization through a homomorphism.** If `f` is a star-algebra homomorphism
out of `M_ι(ℂ)` and the measurement `M` on `ℂ^ι` has `φ(f(∑_a M_a²)) ≥ 1 - ε`, then a projective
measurement `P` on `ℂ^ι` has `∑_a ‖f (M_a - P_a)‖²_φ ≤ 9ε`. -/
theorem exists_isProjective_sum_norm_map_sub_sq_le {B : Type*} [Ring B] [StarRing B]
    [PartialOrder B] [StarOrderedRing B] [Algebra ℂ B] [StarModule ℂ B] [SelfAdjointDecompose B]
    (φ : AlgState B) (f : Matrix ι ι ℂ →⋆ₐ[ℂ] B)
    (M : Measurement α (Matrix ι ι ℂ)) {ε : ℝ}
    (hε : 1 - ε ≤ ∑ a, (φ (f (M.effect a * M.effect a))).re) :
    ∃ P : Measurement α (Matrix ι ι ℂ), P.IsProjective ∧
      ∑ a, φ.norm (f (M.effect a - P.effect a)) ^ 2 ≤ 9 * ε := by
  obtain ⟨P, hP, h⟩ :=
    exists_isProjective_sum_norm_sub_sq_le_of_le (φ.comap f (OrderHomClass.mono f)) M hε
  exact ⟨P, hP, by simpa only [AlgState.norm_comap] using h⟩

/-- **Local orthogonalization** in a tensor-product strategy. If, in the joint state `φ` on
`ℂ^ι ⊗ ℂ^κ`, the first party's measurement `M` has `φ(∑_a M_a² ⊗ 1) ≥ 1 - ε` and the second
party's measurement `N` has `φ(∑_b 1 ⊗ N_b²) ≥ 1 - ε'`, then projective measurements `P` on `ℂ^ι`
and `R` on `ℂ^κ` have `∑_a ‖(M_a - P_a) ⊗ 1‖²_φ ≤ 9ε` and `∑_b ‖1 ⊗ (N_b - R_b)‖²_φ ≤ 9ε'`, and
the operators `P_a ⊗ 1` and `1 ⊗ R_b` commute. -/
theorem exists_isProjective_local (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ))
    (M : Measurement α (Matrix ι ι ℂ)) (N : Measurement β (Matrix κ κ ℂ)) {ε ε' : ℝ}
    (hε : 1 - ε ≤ ∑ a, (φ ((M.effect a * M.effect a) ⊗ₖ 1)).re)
    (hε' : 1 - ε' ≤ ∑ b, (φ (1 ⊗ₖ (N.effect b * N.effect b))).re) :
    ∃ (P : Measurement α (Matrix ι ι ℂ)) (R : Measurement β (Matrix κ κ ℂ)),
      P.IsProjective ∧ R.IsProjective ∧
      ∑ a, φ.norm ((M.effect a - P.effect a) ⊗ₖ 1) ^ 2 ≤ 9 * ε ∧
      ∑ b, φ.norm (1 ⊗ₖ (N.effect b - R.effect b)) ^ 2 ≤ 9 * ε' ∧
      ∀ a b, Commute (P.effect a ⊗ₖ (1 : Matrix κ κ ℂ)) ((1 : Matrix ι ι ℂ) ⊗ₖ R.effect b) := by
  obtain ⟨P, hP, hMP⟩ := exists_isProjective_sum_norm_map_sub_sq_le φ kroneckerOne M hε
  obtain ⟨R, hR, hNR⟩ := exists_isProjective_sum_norm_map_sub_sq_le φ oneKronecker N hε'
  exact ⟨P, R, hP, hR, by simpa only [kroneckerOne_apply] using hMP,
    by simpa only [oneKronecker_apply] using hNR,
    fun _ _ => commute_kroneckerOne_oneKronecker _ _⟩

open scoped Matrix.Norms.L2Operator in
/-- **Local unitary, exactly linear observables.** If, in the joint state `φ` on `ℂ^ι ⊗ ℂ^κ`, the
first party's measurement `M` with bit-string outcomes has `φ(∑_x M_x² ⊗ 1) ≥ 1 - ε`, a projective
measurement `P` on `ℂ^ι` has unitary, exactly linear character observables `χ_P(a)` with
`E_a ‖(χ_M(a) - χ_P(a)) ⊗ 1‖²_φ ≤ 9ε`. -/
theorem exists_isProjective_charObs_kroneckerOne {n : Type*} [Fintype n] [DecidableEq n]
    (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ)) (M : Measurement (n → Bool) (Matrix ι ι ℂ)) {ε : ℝ}
    (hε : 1 - ε ≤ ∑ x, (φ ((M.effect x * M.effect x) ⊗ₖ 1)).re) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm ((M.charObs a - P.charObs a) ⊗ₖ 1) ^ 2 ≤ 9 * ε := by
  obtain ⟨P, hP, hU, hmul, h⟩ :=
    exists_isProjective_charObs (φ.comap kroneckerOne (OrderHomClass.mono _)) M hε
  exact ⟨P, hP, hU, hmul, by simpa only [AlgState.norm_comap, kroneckerOne_apply] using h⟩

end Measurement

end Cslib.Quantum
