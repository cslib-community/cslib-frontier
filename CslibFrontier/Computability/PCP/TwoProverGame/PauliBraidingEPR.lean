/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingDefect
public import CslibFrontier.Foundations.Quantum.PauliEPR
import CslibFrontier.Computability.PCP.TwoProverGame.Naimark
import CslibFrontier.Foundations.Quantum.Algebra.Expect
import CslibFrontier.Foundations.Analysis.InnerProductSpace.PiL2

/-!
# EPR projection for the Pauli braiding game

After applying both local isometries, consistency of the rounded measurements
and the generator intertwining estimates give agreement of the two ideal Pauli
families. Their paired average projects onto the EPR subspace.

## Main results

* `Cslib.PCP.norm_sub_extractedEprProjection_sq_le`: squared norm outside the EPR subspace
  from a pair of local intertwining estimates.
* `Cslib.PCP.exists_local_eprProjection_of_pauliBraidingGame`: the corresponding bound from the
  full verifier score for arbitrary finite-dimensional tensor-product strategies.
-/

public section

namespace Cslib.PCP

open Matrix Finset Quantum
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator Real

private theorem squared_disagreement_after_local_isometries
    {I K L M : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype L] [DecidableEq L] [Fintype M] [DecidableEq M]
    (ψ : EuclideanSpace ℂ (I × K)) (hψ : ‖ψ‖ = 1)
    (V : Matrix L I ℂ) (W : Matrix M K ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (A : Matrix I I ℂ) (B : Matrix K K ℂ) (A' : Matrix L L ℂ) (B' : Matrix M M ℂ) :
    let T := V ⊗ₖ W
    let D := (kroneckerOne A' - oneKronecker B') * T
    let DA := V * A - A' * V
    let DB := W * B - B' * W
    let φ := AlgState.vector ψ hψ
    ‖(WithLp.toLp 2 (D *ᵥ ψ.ofLp) : EuclideanSpace ℂ (L × M))‖ ^ 2 ≤
      3 * ((φ (kroneckerOne (DAᴴ * DA))).re +
        φ.norm (kroneckerOne A - oneKronecker B) ^ 2 +
        (φ (oneKronecker (DBᴴ * DB))).re) := by
  intro T D DA DB φ
  let C := kroneckerOne (κ := K) A - oneKronecker (ι := I) B
  have ha : DA ⊗ₖ W = (V * A) ⊗ₖ W - (A' * V) ⊗ₖ W := by
    ext ⟨p, p'⟩ ⟨q, q'⟩
    simp only [DA, kronecker_apply, Matrix.sub_apply, sub_mul]
  have hb : V ⊗ₖ DB = V ⊗ₖ (W * B) - V ⊗ₖ (B' * W) := by
    ext ⟨p, p'⟩ ⟨q, q'⟩
    simp only [DB, kronecker_apply, Matrix.sub_apply, mul_sub]
  have hD : D = T * C + V ⊗ₖ DB - DA ⊗ₖ W := by
    simp only [D, T, C, Matrix.sub_mul, Matrix.mul_sub, ha, hb, kroneckerOne_apply,
      oneKronecker_apply, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  let applyState (E : Matrix (L × M) (I × K) ℂ) : EuclideanSpace ℂ (L × M) :=
    WithLp.toLp 2 (E *ᵥ ψ.ofLp)
  let u := applyState (DA ⊗ₖ W)
  let v := applyState (T * C)
  let w := applyState (V ⊗ₖ DB)
  have htriangle : ‖v + w - u‖ ^ 2 ≤ 3 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
    have ht := (norm_sub_le (v + w) u).trans
      (add_le_add_left (norm_add_le v w) ‖u‖)
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
    nlinarith only [hs, sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖u‖ - ‖w‖),
      sq_nonneg (‖v‖ - ‖w‖)]
  have hu : ‖u‖ ^ 2 = (φ (kroneckerOne (DAᴴ * DA))).re := by
    dsimp only [u, applyState, φ]
    rw [norm_toLp_mulVec_sq_eq, AlgState.vector_apply, conjTranspose_kronecker,
      ← mul_kronecker_mul, hW, kroneckerOne_apply]
  have hv : ‖v‖ ^ 2 = φ.norm C ^ 2 := by
    have hT : Tᴴ * T = 1 := by
      simp only [T, conjTranspose_kronecker, ← mul_kronecker_mul, hV, hW, one_kronecker_one]
    dsimp only [v, applyState, φ]
    rw [norm_toLp_mulVec_sq_eq, AlgState.norm_sq, AlgState.vector_apply,
      Matrix.star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul]
  have hw : ‖w‖ ^ 2 = (φ (oneKronecker (DBᴴ * DB))).re := by
    dsimp only [w, applyState, φ]
    rw [norm_toLp_mulVec_sq_eq, AlgState.vector_apply, conjTranspose_kronecker,
      ← mul_kronecker_mul, hV, oneKronecker_apply]
  change ‖applyState D‖ ^ 2 ≤ _
  rw [hD]
  simp only [applyState, sub_mulVec, add_mulVec, WithLp.toLp_sub, WithLp.toLp_add]
  change ‖v + w - u‖ ^ 2 ≤ _
  simpa only [hu, hv, hw, C] using htriangle

section Game

universe u v

variable {n : ℕ} {I : Type u} {K : Type v} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Local Pauli intertwining and consistency bound the squared norm outside the
extracted EPR subspace for the tensor product of the two isometries. -/
theorem norm_sub_extractedEprProjection_sq_le
    {J : Type u} {L : Type v} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
    (ψ : EuclideanSpace ℂ (I × K)) (hψ : ‖ψ‖ = 1)
    (P : Bool → (Fin n → Bool) → Matrix I I ℂ)
    (Q : Bool → (Fin n → Bool) → Matrix K K ℂ)
    (V : Matrix ((Fin n → Bool) × J) I ℂ) (W : Matrix ((Fin n → Bool) × L) K ℂ)
    {δ ξ η : ℝ}
    (hA : PauliBraidingLocalCompression
      ((AlgState.vector ψ hψ).comap kroneckerOne (OrderHomClass.mono _)) (P false) (P true) V δ ξ)
    (hB : PauliBraidingLocalCompression
      ((AlgState.vector ψ hψ).comap oneKronecker (OrderHomClass.mono _)) (Q false) (Q true) W δ ξ)
    (hcross : ∀ b, let φ := AlgState.vector ψ hψ
      (𝔼 x, φ.norm (kroneckerOne (P b x) - oneKronecker (Q b x)) ^ 2) ≤ η) :
    let T := V ⊗ₖ W
    let E := extractedEprProjection (Q := Fin n → Bool) (J := J) (K := L)
    ‖(WithLp.toLp 2 (((E - 1) * T) *ᵥ ψ.ofLp) :
      EuclideanSpace ℂ (((Fin n → Bool) × J) × (Fin n → Bool) × L))‖ ^ 2 ≤
      3 * ξ + 2 * η := by
  intro T E
  have hT : Tᴴ * T = 1 := by
    simp only [T, conjTranspose_kronecker, ← mul_kronecker_mul, hA.isometry, hB.isometry,
      one_kronecker_one]
  let ψ' : EuclideanSpace ℂ (((Fin n → Bool) × J) × (Fin n → Bool) × L) :=
    WithLp.toLp 2 (T *ᵥ ψ.ofLp)
  have hψ' : ‖ψ'‖ = 1 := (norm_toLp_mulVec_of_conjTranspose_mul_self hT ψ).trans hψ
  let ρ := AlgState.vector ψ' hψ'
  let e := extractedRegisterEmbedding (Q := Fin n → Bool) (J := J) (K := L)
  let σ := ρ.comap e (OrderHomClass.mono _)
  let ideal (b : Bool) (x : Fin n → Bool) := cond b (pauliZPow x) (pauliXPow x)
  let I₁ (b : Bool) (x : Fin n → Bool) := ideal b x ⊗ₖ (1 : Matrix J J ℂ)
  let I₂ (b : Bool) (x : Fin n → Bool) := ideal b x ⊗ₖ (1 : Matrix L L ℂ)
  let φ := AlgState.vector ψ hψ
  let errorA (b : Bool) (x : Fin n → Bool) :=
    let D := V * P b x - I₁ b x * V
    (φ (kroneckerOne (Dᴴ * D))).re
  let errorB (b : Bool) (x : Fin n → Bool) :=
    let D := W * Q b x - I₂ b x * W
    (φ (oneKronecker (Dᴴ * D))).re
  have hA0 : (𝔼 x, errorA false x) ≤ ξ := hA.intertwinesX
  have hB0 : (𝔼 x, errorB false x) ≤ ξ := hB.intertwinesX
  have ht (x : Fin n → Bool) :
      σ.norm (kroneckerOne (ideal false x) - oneKronecker (ideal false x)) ^ 2 ≤
        3 * (errorA false x + φ.norm (kroneckerOne (P false x) - oneKronecker (Q false x)) ^ 2 +
          errorB false x) := by
    simp only [σ, AlgState.norm_comap, map_sub, e, extractedRegisterEmbedding_left,
      extractedRegisterEmbedding_right, ρ, AlgState.norm_vector]
    change ‖(WithLp.toLp 2 ((kroneckerOne (I₁ false x) - oneKronecker (I₂ false x)) *ᵥ
      (T *ᵥ ψ.ofLp)) : EuclideanSpace ℂ (((Fin n → Bool) × J) × (Fin n → Bool) × L))‖ ^ 2 ≤ _
    rw [mulVec_mulVec]
    exact squared_disagreement_after_local_isometries ψ hψ V W hA.isometry hB.isometry
      (P false x) (Q false x) (I₁ false x) (I₂ false x)
  have htZ (x : Fin n → Bool) :
      σ.norm (kroneckerOne (pauliZPow x) - oneKronecker (pauliZPow x)) ^ 2 =
      φ.norm (kroneckerOne (P true x) - oneKronecker (Q true x)) ^ 2 := by
    let C := kroneckerOne (P true x) - oneKronecker (Q true x)
    let D := kroneckerOne (pauliZPow x ⊗ₖ (1 : Matrix J J ℂ)) -
      oneKronecker (pauliZPow x ⊗ₖ (1 : Matrix L L ℂ))
    have hDC : D * T = T * C := by
      simp only [D, T, C, Matrix.sub_mul, Matrix.mul_sub, kroneckerOne_apply,
        oneKronecker_apply, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
      rw [← hA.intertwinesZ x, ← hB.intertwinesZ x]
    simp only [σ, AlgState.norm_comap, map_sub, e, extractedRegisterEmbedding_left,
      extractedRegisterEmbedding_right, ρ, φ, AlgState.norm_vector]
    change ‖(WithLp.toLp 2 (D *ᵥ (T *ᵥ ψ.ofLp)) :
      EuclideanSpace ℂ (((Fin n → Bool) × J) × (Fin n → Bool) × L))‖ ^ 2 = _
    rw [mulVec_mulVec, hDC, ← mulVec_mulVec]
    exact congrArg (· ^ 2) (norm_toLp_mulVec_of_conjTranspose_mul_self hT
      (WithLp.toLp 2 (C *ᵥ ψ.ofLp)))
  have hX := expect_le_expect (s := (univ : Finset (Fin n → Bool))) fun x _ => ht x
  have hZ := expect_le_expect (s := (univ : Finset (Fin n → Bool))) fun x _ => (htZ x).le
  rw [← mul_expect, expect_add_distrib, expect_add_distrib] at hX
  have hE := norm_sub_eprProjector_sq_le σ
  simp only [ideal, Bool.cond_false] at hX
  have hbound : σ.norm (pureState (maxEntangled (Fin n → Bool)) - 1) ^ 2 ≤
      3 * ξ + 2 * η := by
    linarith only [hE, hX, hZ, hA0, hB0, hcross false, hcross true]
  simp only [σ, AlgState.norm_comap, map_sub, map_one, ρ, AlgState.norm_vector] at hbound
  change ‖(WithLp.toLp 2 ((E - 1) *ᵥ (T *ᵥ ψ.ofLp)) :
      EuclideanSpace ℂ (((Fin n → Bool) × J) × (Fin n → Bool) × L))‖ ^ 2 ≤ _ at hbound
  rwa [mulVec_mulVec] at hbound

variable [Nonempty (Fin n)]

/-- A near-optimal finite-dimensional tensor-product strategy admits local
isometries with small squared norm outside the EPR projection of their joint image.
The isometries act on the original strategy's two spaces. -/
theorem exists_local_eprProjection_of_pauliBraidingGame
    (S : QuantumStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) I K)
    {ε : ℝ}
    (hwin : (2 + Real.cos (π / 8) ^ 2) / 3 - ε ≤
      (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).quantumWinProb S) :
    ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J)
      (L : Type v) (_ : Fintype L) (_ : DecidableEq L)
      (V : Matrix ((Fin n → Bool) × J) I ℂ)
      (W : Matrix ((Fin n → Bool) × L) K ℂ),
      Vᴴ * V = 1 ∧ Wᴴ * W = 1 ∧
      let E := extractedEprProjection (Q := Fin n → Bool) (J := J) (K := L)
      ‖(WithLp.toLp 2 (((E - 1) * (V ⊗ₖ W)) *ᵥ S.state.ofLp) :
        EuclideanSpace ℂ (((Fin n → Bool) × J) × (Fin n → Bool) × L))‖ ^ 2 ≤
        3 * pauliBraidingTwistedCommutationError (3 * ε) +
          2 * pauliBraidingRoundedConsistencyError (3 * ε) := by
  let a₀ : (Bool × Bool) ⊕ Bool := .inl (false, false)
  let T := S.dilate a₀ a₀
  have hscore :
      (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).quantumWinProb T =
        (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).quantumWinProb S := by
    have h := funext fun x => funext fun y => S.answers_dilate a₀ a₀ x y
    rw [SeededGame.quantumWinProb, SeededGame.quantumWinProb, show T.answers = S.answers from h]
  obtain ⟨P, Q, _, _, hcross, ⟨J, _, _, V, hV⟩, ⟨L, _, _, W, hW⟩⟩ :=
    exists_local_pauliCompression_of_pauliBraidingGame T
      (fun b q => S.isProjective_alice_dilate a₀ a₀ (.basis b q))
      (fun b q => S.isProjective_bob_dilate a₀ a₀ (.basis b q))
      (by rwa [hscore])
  have h := norm_sub_extractedEprProjection_sq_le T.state T.norm_state
    (fun b => (P b).charObs) (fun b => (Q b).charObs) V W hV hW hcross
  let E := extractedEprProjection (Q := Fin n → Bool) (J := J) (K := L)
  let U := V * ancillaEmbed a₀
  let R := W * ancillaEmbed a₀
  refine ⟨J, inferInstance, inferInstance, L, inferInstance, inferInstance, U, R, ?_, ?_, ?_⟩
  · rw [show U = V * ancillaEmbed a₀ from rfl, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Vᴴ V, hV.isometry, Matrix.one_mul, conjTranspose_ancillaEmbed_mul]
  · rw [show R = W * ancillaEmbed a₀ from rfl, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Wᴴ W, hW.isometry, Matrix.one_mul, conjTranspose_ancillaEmbed_mul]
  change ‖(WithLp.toLp 2 (((E - 1) * (V ⊗ₖ W)) *ᵥ
    (QuantumStrategy.dilateEmbed a₀ a₀ *ᵥ S.state.ofLp)) :
      EuclideanSpace ℂ (((Fin n → Bool) × J) × (Fin n → Bool) × L))‖ ^ 2 ≤ _ at h
  rw [mulVec_mulVec, Matrix.mul_assoc, QuantumStrategy.dilateEmbed, ← mul_kronecker_mul] at h
  exact h

end Game

end Cslib.PCP
