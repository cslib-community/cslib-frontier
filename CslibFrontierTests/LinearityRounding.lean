/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingDefect
import CslibFrontier.Foundations.Quantum.PauliTwirl

/-! # Rounding approximately linear observables

Checked clients: Parseval for the Fourier coefficients, the two estimates for the Fourier
measurement in any state of any star-ordered algebra, and rounding, in one algebra and for one
party of a tensor-product strategy. A concrete instance: the Pauli phase flips `Z^a` are exactly
linear, so their linearity defect is `0` in every state, and rounding finds exactly linear
unitaries at zero average distance in the state's seminorm. The contraction
client checks scalar multiples of the identity, and the Pauli client checks
the two local error bounds at zero rejection.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LinearityRounding

open Matrix Cslib Cslib.PCP Cslib.Quantum Finset
open scoped Kronecker MatrixOrder ComplexOrder BigOperators Matrix.Norms.L2Operator Real

/-- **Parseval** for the Fourier coefficients of `±1` observables. -/
example {n R : Type} [Fintype n] [DecidableEq n] [Ring R] [Algebra ℂ R]
    (A : (n → Bool) → R) (hA2 : ∀ a, A a * A a = 1) :
    ∑ u, fourierCoeff A u * fourierCoeff A u = 1 :=
  sum_fourierCoeff_mul_self hA2

/-- **The Fourier measurement**, in any state of any star-ordered algebra: almost projective, and
its characters are close to the observables. -/
example {n R : Type} [Fintype n] [DecidableEq n] [Ring R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] [Algebra ℂ R] [StarModule ℂ R] [SelfAdjointDecompose R]
    (φ : AlgState R) (A : (n → Bool) → R) (hA : ∀ a, IsSelfAdjoint (A a))
    (hA2 : ∀ a, A a * A a = 1) {δ : ℝ}
    (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re) :
    1 - 2 * δ ≤ ∑ u, (φ ((fourierMeasurement A hA hA2).effect u *
      (fourierMeasurement A hA hA2).effect u)).re ∧
    𝔼 a, φ.norm (A a - walshSum (fourierMeasurement A hA hA2).effect a) ^ 2 ≤ 2 * δ :=
  ⟨one_sub_le_sum_fourierMeasurement_sq hA hA2 φ hδ, expect_norm_sub_walshSum_sq_le hA hA2 φ hδ⟩

/-- **Rounding** for one party of a tensor-product strategy. -/
example {ι κ n : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype n]
    [DecidableEq n] (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ)) (A : (n → Bool) → Matrix ι ι ℂ)
    (hA : ∀ a, IsSelfAdjoint (A a)) (hA2 : ∀ a, A a * A a = 1) {δ : ℝ}
    (hδ : 1 - δ ≤ 𝔼 a, 𝔼 b, (φ ((A a * A b * A (a + b)) ⊗ₖ 1)).re) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm ((A a - P.charObs a) ⊗ₖ 1) ^ 2 ≤ 40 * δ :=
  exists_isProjective_charObs_kroneckerOne_of_linear φ A hA hA2 hδ

/-- **Concrete instance.** The phase flips `Z^a` have linearity defect `0` in every state, so
rounding finds exactly linear unitaries at zero average distance. -/
example {n : Type} [Fintype n] [DecidableEq n] (φ : AlgState (Matrix (n → Bool) (n → Bool) ℂ)) :
    ∃ P : Measurement (n → Bool) (Matrix (n → Bool) (n → Bool) ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix (n → Bool) (n → Bool) ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm (pauliZPow a - P.charObs a) ^ 2 ≤ 0 := by
  have hδ : 1 - 0 ≤ 𝔼 a, 𝔼 b,
      (φ (pauliZPow a * pauliZPow b * pauliZPow (a + b))).re := by
    simp only [pauliZPow_mul, BitString.add_self, pauliZPow_zero, φ.map_one, Complex.one_re,
      Fintype.expect_const, sub_zero, le_refl]
  simpa using exists_isProjective_charObs_of_linear φ pauliZPow
    (fun a => (pauliZPow_isHermitian a).isSelfAdjoint) pauliZPow_mul_self hδ

/-- A scalar contraction with parameter strictly below one need not be an involution.
Its triple correlation is the cube of the parameter in every state. -/
example (φ : AlgState (Matrix (Fin 1) (Fin 1) ℂ)) (t : ℝ) (h₀ : 0 ≤ t) (h₁ : t < 1) :
    let A : (Fin 1 → Bool) → Matrix (Fin 1) (Fin 1) ℂ :=
      fun _ => (t : ℂ) • 1
    ∃ P : Measurement (Fin 1 → Bool) (Matrix (Fin 1) (Fin 1) ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix (Fin 1) (Fin 1) ℂ)) ∧
      (∀ a b, P.charObs a * P.charObs b = P.charObs (a + b)) ∧
      𝔼 a, φ.norm (A a - P.charObs a) ^ 2 ≤ 48 * (1 - t ^ 3) := by
  intro A
  have hsa : ∀ a, IsSelfAdjoint (A a) := fun _ =>
    (show IsSelfAdjoint (t : ℂ) from Complex.conj_ofReal _).smul (by
      change star (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1
      exact star_one _)
  have hsq (a : Fin 1 → Bool) : A a * A a = ((t * t : ℝ) : ℂ) • 1 := by
    change ((t : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) * ((t : ℂ) • 1) = _
    rw [smul_mul_smul_comm, mul_one, Complex.ofReal_mul]
  have hcontract (a : Fin 1 → Bool) : A a * A a ≤ 1 := by
    rw [hsq a, ← sub_nonneg]
    have ht : 0 ≤ 1 - t * t := by
      nlinarith only [mul_nonneg h₀ (sub_nonneg.mpr h₁.le), h₁]
    have hpos := (PosSemidef.one (n := Fin 1) (R := ℂ)).smul
      ((RCLike.ofReal_nonneg (K := ℂ)).mpr ht)
    have h := nonneg_iff_posSemidef.mpr hpos
    change 0 ≤ ((↑(1 - t * t) : ℂ)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) at h
    push_cast at h
    rwa [sub_smul, one_smul, ← Complex.ofReal_mul] at h
  have hcube (a b : Fin 1 → Bool) :
      A a * A b * A (a + b) = ((t ^ 3 : ℝ) : ℂ) • 1 := by
    change A a * A a * A a = _
    rw [hsq a]
    change (((t * t : ℝ) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) * ((t : ℂ) • 1) = _
    rw [smul_mul_smul_comm, mul_one, ← Complex.ofReal_mul, pow_succ, pow_two]
  refine exists_isProjective_charObs_of_linear_contractions φ A hsa hcontract ?_
  simp only [hcube, map_smul, AlgState.map_one, smul_eq_mul, mul_one, Complex.ofReal_re,
    Fintype.expect_const, sub_sub_cancel, le_refl]

private abbrev WidthOneTensorStrategy :=
  QuantumStrategy (PauliBraidingQuestion 1 Bool) (PauliBraidingQuestion 1 Bool)
    ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) (Fin 1) (Fin 1)

/-- Perfect linearity-branch play gives zero state-norm error in each basis of the
width-one tensor-product model. -/
example (S : WidthOneTensorStrategy) (basis : Bool)
    (hA : ∀ basis q, (S.alice (.basis basis q)).toMeasurement.IsProjective)
    (hB : ∀ basis q, (S.bob (.basis basis q)).toMeasurement.IsProjective)
    (hwin : (pauliBraidingBranchGame 1 TwoProverGame.chsh id
      (fun _ => id) 0).quantumWinProb S = 1) :
    let T := S.toCommuting
    ∃ (P R : Measurement (Fin 1 → Bool) (Matrix (Fin 1) (Fin 1) ℂ)),
      P.IsProjective ∧ R.IsProjective ∧
      (𝔼 c, T.state.norm ((𝔼 d, pauliBraidingBasisObservable T.alice basis c d) -
        kroneckerOne (P.charObs c)) ^ 2) = 0 ∧
      (𝔼 c, T.state.norm ((𝔼 d, pauliBraidingBasisObservable T.bob basis c d) -
        oneKronecker (R.charObs c)) ^ 2) = 0 := by
  obtain ⟨P, R, hP, hR, hp, hr⟩ := exists_local_charObs_of_pauliBraidingLinearity
    TwoProverGame.chsh id (fun _ => id) S hA hB basis (ε := 0) (by simp [hwin])
  refine ⟨P, R, hP, hR, le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · simpa using hp
  · exact expect_nonneg fun _ _ => sq_nonneg _
  · simpa using hr
  · exact expect_nonneg fun _ _ => sq_nonneg _

/-- At the exact upper score Alice's characters agree with her averaged basis observables
in the state norm, and one local isometry gives zero error on the products and generators. -/
example (S : QuantumStrategy (PauliBraidingQuestion 1 Bool) (PauliBraidingQuestion 1 Bool)
    ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) (Fin 2) (Fin 2))
    (hA : ∀ basis q, (S.alice (.basis basis q)).toMeasurement.IsProjective)
    (hB : ∀ basis q, (S.bob (.basis basis q)).toMeasurement.IsProjective)
    (hwin : (pauliBraidingGame 1 TwoProverGame.chsh id (fun _ => id)).quantumWinProb S =
      (2 + Real.cos (π / 8) ^ 2) / 3) :
    ∃ (P : Bool → Measurement (Fin 1 → Bool) (Matrix (Fin 2) (Fin 2) ℂ))
      (J : Type) (_ : Fintype J) (_ : DecidableEq J)
      (W : Matrix ((Fin 1 → Bool) × J) (Fin 2) ℂ), Wᴴ * W = 1 ∧
      (∀ b x, S.toCommuting.state.norm
        ((𝔼 d, pauliBraidingBasisObservable S.toCommuting.alice b x d) -
          kroneckerOne (κ := Fin 2) ((P b).charObs x)) ^ 2 = 0) ∧
      (∀ x z, S.toCommuting.state.norm (kroneckerOne (κ := Fin 2)
        ((P false).charObs x * (P true).charObs z -
          Wᴴ * ((pauliXPow x * pauliZPow z) ⊗ₖ (1 : Matrix J J ℂ)) * W)) ^ 2 = 0) ∧
      (∀ z, W * (P true).charObs z = (pauliZPow z ⊗ₖ (1 : Matrix J J ℂ)) * W) ∧
      (∀ x, let D := W * (P false).charObs x - (pauliXPow x ⊗ₖ (1 : Matrix J J ℂ)) * W
        (S.toCommuting.state (kroneckerOne (κ := Fin 2) (Dᴴ * D))).re = 0) := by
  obtain ⟨P, _, _, hclose, ⟨J, _, _, W, h⟩, _⟩ :=
    exists_local_pauliCompression_of_pauliBraidingGame S hA hB (ε := 0) (by rw [hwin, sub_zero])
  let f (x z : Fin 1 → Bool) := S.toCommuting.state.norm (kroneckerOne (κ := Fin 2)
    ((P false).charObs x * (P true).charObs z -
      Wᴴ * ((pauliXPow x * pauliZPow z) ⊗ₖ (1 : Matrix J J ℂ)) * W)) ^ 2
  have hzero : (𝔼 x, 𝔼 z, f x z) ≤ 0 := by
    simpa [f, AlgState.norm_comap] using h.products
  let F (p : (Fin 1 → Bool) × (Fin 1 → Bool)) := f p.1 p.2
  have hn : 0 ≤ F := fun _ => sq_nonneg _
  have hmean : (𝔼 p, F p) = 0 := by
    rw [Fintype.expect_prod_type]
    exact le_antisymm hzero (expect_nonneg fun _ _ => expect_nonneg fun _ _ => sq_nonneg _)
  have hF := (Fintype.expect_eq_zero_iff_of_nonneg hn).mp hmean
  refine ⟨P, J, inferInstance, inferInstance, W, h.isometry,
    ?_, fun x z => congrFun hF (x, z), h.intertwinesZ, ?_⟩
  · intro b x
    let g (y : Fin 1 → Bool) := S.toCommuting.state.norm
      ((𝔼 d, pauliBraidingBasisObservable S.toCommuting.alice b y d) -
        kroneckerOne (κ := Fin 2) ((P b).charObs y)) ^ 2
    have hg : 0 ≤ g := fun _ => sq_nonneg _
    have hle : (𝔼 y, g y) ≤ 0 := by simpa [g] using (hclose b).1
    have hmean : (𝔼 y, g y) = 0 := le_antisymm hle (expect_nonneg fun y _ => hg y)
    exact congrFun ((Fintype.expect_eq_zero_iff_of_nonneg hg).mp hmean) x
  · intro x
    let D (a : Fin 1 → Bool) := W * (P false).charObs a -
      (pauliXPow a ⊗ₖ (1 : Matrix J J ℂ)) * W
    let φ := S.toCommuting.state.comap (kroneckerOne (κ := Fin 2)) (OrderHomClass.mono _)
    let g (a : Fin 1 → Bool) := (φ ((D a)ᴴ * D a)).re
    have hn : 0 ≤ g := fun a =>
      φ.re_apply_nonneg (nonneg_iff_posSemidef.mpr (posSemidef_conjTranspose_mul_self (D a)))
    have hle : (𝔼 a, g a) ≤ 0 := by simpa [g, D, φ] using h.intertwinesX
    have hm := le_antisymm hle (expect_nonneg fun a _ => hn a)
    exact congrFun ((Fintype.expect_eq_zero_iff_of_nonneg hn).mp hm) x

end CslibFrontierTests.LinearityRounding
