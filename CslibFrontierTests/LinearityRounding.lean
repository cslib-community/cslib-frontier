/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingEPR
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
  obtain ⟨P, _, _, hclose, _, ⟨J, _, _, W, h⟩, _⟩ :=
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

/-- At the upper score the locally extracted width-one state belongs to the EPR subspace. -/
example (S : QuantumStrategy (PauliBraidingQuestion 1 Bool) (PauliBraidingQuestion 1 Bool)
    ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) (Fin 2) (Fin 2))
    (hwin : (pauliBraidingGame 1 TwoProverGame.chsh id (fun _ => id)).quantumWinProb S =
      (2 + Real.cos (π / 8) ^ 2) / 3) :
    ∃ (J L : Type) (_ : Fintype J) (_ : DecidableEq J) (_ : Fintype L) (_ : DecidableEq L)
      (V : Matrix ((Fin 1 → Bool) × J) (Fin 2) ℂ)
      (W : Matrix ((Fin 1 → Bool) × L) (Fin 2) ℂ),
      Vᴴ * V = 1 ∧ Wᴴ * W = 1 ∧
      let ψ := (V ⊗ₖ W) *ᵥ S.state.ofLp
      extractedEprProjection (Q := Fin 1 → Bool) *ᵥ ψ = ψ := by
  obtain ⟨J, _, _, L, _, _, V, W, hV, hW, h⟩ :=
    exists_local_eprProjection_of_pauliBraidingGame S (ε := 0) (by rw [hwin, sub_zero])
  let E := extractedEprProjection (Q := Fin 1 → Bool) (J := J) (K := L)
  let ψ := (V ⊗ₖ W) *ᵥ S.state.ofLp
  have hle : ‖(WithLp.toLp 2 (E *ᵥ ψ - ψ) :
      EuclideanSpace ℂ (((Fin 1 → Bool) × J) × (Fin 1 → Bool) × L))‖ ^ 2 ≤ 0 := by
    simpa only [E, ψ, zero_mul, mul_zero, pauliBraidingTwistedCommutationError_zero,
      pauliBraidingRoundedConsistencyError_zero,
      ← Matrix.mulVec_mulVec, sub_mulVec, one_mulVec, add_zero] using h
  have hn := le_antisymm hle (sq_nonneg _)
  have hz := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hn)
  exact ⟨J, L, inferInstance, inferInstance, inferInstance, inferInstance, V, W, hV, hW,
    sub_eq_zero.mp (by
      simpa only [WithLp.ofLp_toLp, WithLp.ofLp_zero] using (congrArg WithLp.ofLp hz))⟩


/-- On the width-one computational state `|00⟩`, the leakage is one half and
the paired X and Z disagreements are one and zero, respectively. -/
example :
    let p : (Fin 1 → Bool) × (Fin 1 → Bool) := (0, 0)
    let φ := AlgState.vector (ket p) (norm_ket p)
    (φ.norm (pureState (maxEntangled (Fin 1 → Bool)) - 1) ^ 2 = 1 / 2) ∧
    ((𝔼 x, φ.norm (kroneckerOne (pauliXPow x) - oneKronecker (pauliXPow x)) ^ 2) = 1) ∧
    ((𝔼 z, φ.norm (kroneckerOne (pauliZPow z) - oneKronecker (pauliZPow z)) ^ 2) = 0) := by
  intro p φ
  have hentry (M : Matrix ((Fin 1 → Bool) × (Fin 1 → Bool))
      ((Fin 1 → Bool) × (Fin 1 → Bool)) ℂ) : φ M = M p p := by
    have hk : (ket p).ofLp = Pi.single p (1 : ℂ) := by
      ext q
      simp [Pi.single_apply]
    change AlgState.vector (ket p) (norm_ket p) M = M p p
    rw [AlgState.vector_apply, hk, Pi.star_single, star_one, single_dotProduct,
      one_mul, mulVec_single_one]
    rfl
  have hpair (M : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) (hM : IsSelfAdjoint M)
      (hM2 : M * M = 1) :
      φ.norm (kroneckerOne M - oneKronecker M) ^ 2 = 2 - 2 * (M 0 0 * M 0 0).re := by
    rw [φ.norm_sub_sq_eq_of_mul_self
      (hM.map kroneckerOne) (hM.map oneKronecker)
      (by rw [← map_mul, hM2, map_one]) (by rw [← map_mul, hM2, map_one]),
      kroneckerOne_apply, oneKronecker_apply, ← mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul, hentry]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_sub_eprProjector_sq_eq, map_sub, φ.map_one, Complex.sub_re, Complex.one_re, hentry]
    change 1 - (pureState (maxEntangled (Fin 1 → Bool)) ((0, 0)) ((0, 0))).re = _
    simp only [pureState_apply, maxEntangled_apply, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, pow_one, Nat.cast_ofNat, ite_true, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num), Complex.ofReal_re]
    norm_num
  · have hx (x : Fin 1 → Bool) :
        φ.norm (kroneckerOne (pauliXPow x) - oneKronecker (pauliXPow x)) ^ 2 =
          if x = 0 then 0 else (2 : ℝ) := by
      rw [hpair _ (pauliXPow_isHermitian x).isSelfAdjoint (pauliXPow_mul_self x),
        pauliXPow_apply, zero_add]
      by_cases h : x = 0 <;> simp [h, eq_comm]
    simp only [hx]
    erw [Fintype.expect_unique_bool (fun x : Fin 1 → Bool => if x = 0 then 0 else (2 : ℝ))]
    have hz : (fun _ : Fin 1 => false) = 0 := rfl
    have ho : (fun _ : Fin 1 => true) ≠ 0 := fun h => Bool.false_ne_true (congrFun h 0).symm
    norm_num [hz, ho]
  · have hz (z : Fin 1 → Bool) :
        φ.norm (kroneckerOne (pauliZPow z) - oneKronecker (pauliZPow z)) ^ 2 = 0 := by
      rw [hpair _ (pauliZPow_isHermitian z).isSelfAdjoint (pauliZPow_mul_self z)]
      norm_num [pauliZPow_apply, dotProduct_zero, BitString.signVal,
        show (0 : Bool) = false from rfl]
    simp only [hz, Fintype.expect_const]

end CslibFrontierTests.LinearityRounding
