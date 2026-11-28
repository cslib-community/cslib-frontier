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
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Joint extraction for the Pauli braiding game

After applying both local isometries, consistency of the rounded measurements
and the generator intertwining estimates give agreement of the two ideal Pauli
families. Their paired average projects onto the EPR subspace.

The same isometries compare each player's measured basis observables, averaged
over the dummy as in [Natarajan and Vidick, equation (11)][NatarajanVidick2017]
(arXiv:1610.03574v1, p. 18), with the corresponding ideal observables on the
extracted registers. When returning from the dilation to the original spaces,
a local ancilla projection commutes with the opposite player's rounded
observable. The part in the projection's range is bounded by the rounding
error. The orthogonal part is bounded by the disagreement between the players'
rounded observables. Their squared norms add before the Pauli intertwining
error is included.

## Main results

* `Cslib.PCP.norm_sub_extractedEprProjection_sq_le`: squared norm outside the EPR subspace
  from a pair of local intertwining estimates.
* `Cslib.PCP.exists_pauliBraidingExtraction`: one pair of local isometries controls
  the EPR leakage and the two players' observable errors for arbitrary
  finite-dimensional tensor-product strategies.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

public section

namespace Cslib.PCP

open Matrix Finset Quantum
open scoped BigOperators Kronecker ComplexOrder InnerProductSpace MatrixOrder
  Matrix.Norms.L2Operator Real

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
  have ha : DA ⊗ₖ W = (V * A) ⊗ₖ W - (A' * V) ⊗ₖ W := Matrix.ext fun ⟨_, _⟩ ⟨_, _⟩ => sub_mul ..
  have hb : V ⊗ₖ DB = V ⊗ₖ (W * B) - V ⊗ₖ (B' * W) := Matrix.ext fun ⟨_, _⟩ ⟨_, _⟩ => mul_sub ..
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
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      ((norm_sub_le (v + w) u).trans (add_le_add_left (norm_add_le v w) ‖u‖))
    nlinarith only [hs, sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖u‖ - ‖w‖), sq_nonneg (‖v‖ - ‖w‖)]
  have hu : ‖u‖ ^ 2 = (φ (kroneckerOne (DAᴴ * DA))).re := by
    rw [norm_toLp_mulVec_sq_eq, AlgState.vector_apply, conjTranspose_kronecker,
      ← mul_kronecker_mul, hW, kroneckerOne_apply]
  have hv : ‖v‖ ^ 2 = φ.norm C ^ 2 := by
    have hT : Tᴴ * T = 1 := by
      simp only [T, conjTranspose_kronecker, ← mul_kronecker_mul, hV, hW, one_kronecker_one]
    rw [norm_toLp_mulVec_sq_eq, AlgState.norm_sq, AlgState.vector_apply,
      Matrix.star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul]
  have hw : ‖w‖ ^ 2 = (φ (oneKronecker (DBᴴ * DB))).re := by
    rw [norm_toLp_mulVec_sq_eq, AlgState.vector_apply, conjTranspose_kronecker,
      ← mul_kronecker_mul, hV, oneKronecker_apply]
  rw [hu, hv, hw] at htriangle
  simpa only [hD, u, v, w, applyState, sub_mulVec, add_mulVec, WithLp.toLp_sub,
    WithLp.toLp_add, C] using htriangle

private theorem norm_compressed_action_sub_sq_le
    {I H : Type*} [Fintype I] [Fintype H]
    (ψ : EuclideanSpace ℂ I) (E : Matrix H I ℂ)
    (P A B R : Matrix H H ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (hPE : P * E = E) (hPB : Commute P B)
    (A₀ : Matrix I I ℂ) (hA₀ : P * A * E = E * A₀) :
    let ψ' : EuclideanSpace ℂ H := WithLp.toLp 2 (E *ᵥ ψ.ofLp)
    ‖(WithLp.toLp 2 ((E * A₀ - R * E) *ᵥ ψ.ofLp) : EuclideanSpace ℂ H)‖ ^ 2 ≤
      ‖(WithLp.toLp 2 ((A - R) *ᵥ ψ'.ofLp) : EuclideanSpace ℂ H)‖ ^ 2 +
        ‖(WithLp.toLp 2 ((R - B) *ᵥ ψ'.ofLp) : EuclideanSpace ℂ H)‖ ^ 2 := by
  classical
  intro ψ'
  let Q := 1 - P
  have hPQ : P * Q = 0 := by simp [Q, Matrix.mul_sub, hPP]
  have hQ : Qᴴ = Q := by simp [Q, hP]
  have hQQ : Q * Q = Q := by simp [Q, Matrix.sub_mul, Matrix.mul_sub, hPP]
  have hPB' : P * (B * E) = B * E := by
    rw [← Matrix.mul_assoc, hPB.eq, Matrix.mul_assoc, hPE]
  have hPA : P * (A * E) = E * A₀ := by rwa [← Matrix.mul_assoc]
  have hsplit : E * A₀ - R * E = (P * (A - R) - Q * (R - B)) * E := by
    simp only [Q, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, hPA, hPB']
    abel
  let u : EuclideanSpace ℂ H := WithLp.toLp 2 ((A - R) *ᵥ ψ'.ofLp)
  let v : EuclideanSpace ℂ H := WithLp.toLp 2 ((R - B) *ᵥ ψ'.ofLp)
  let u' : EuclideanSpace ℂ H := WithLp.toLp 2 (P *ᵥ u.ofLp)
  let v' : EuclideanSpace ℂ H := WithLp.toLp 2 (Q *ᵥ v.ofLp)
  have hPc : (1 - Pᴴ * P).PosSemidef := by
    simpa only [hP, hPP, hQ, hQQ] using posSemidef_conjTranspose_mul_self Q
  have hQc : (1 - Qᴴ * Q).PosSemidef := by
    simpa only [hQ, hQQ, Q, sub_sub_cancel, hP, hPP] using posSemidef_conjTranspose_mul_self P
  have horth : inner ℂ u' (-v') = 0 := by
    rw [inner_neg_right, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    change -(star (P *ᵥ u.ofLp) ⬝ᵥ (Q *ᵥ v.ofLp)) = 0
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hP, hPQ, zero_mulVec,
      dotProduct_zero, neg_zero]
  have he :
      (WithLp.toLp 2 ((E * A₀ - R * E) *ᵥ ψ.ofLp) : EuclideanSpace ℂ H) = u' - v' := by
    simp only [hsplit, u', v', u, v, ψ', ← mulVec_mulVec, sub_mulVec, WithLp.toLp_sub]
  rw [he, sub_eq_add_neg]
  change ‖u' + -v'‖ ^ 2 ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2
  simp only [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u' (-v') horth,
    norm_neg]
  exact add_le_add (mul_self_le_mul_self (norm_nonneg _) (norm_toLp_mulVec_le_of_posSemidef hPc u))
    (mul_self_le_mul_self (norm_nonneg _) (norm_toLp_mulVec_le_of_posSemidef hQc v))

private theorem expect_norm_compressed_action_sub_sq_le
    {I H K F : Type*} [Fintype I] [Fintype H] [DecidableEq H] [Fintype K] [Fintype F]
    (ψ : EuclideanSpace ℂ I) (E : Matrix H I ℂ)
    (D : Matrix K H ℂ) (hD : Dᴴ * D = 1)
    (P : Matrix H H ℂ) (hP : Pᴴ = P) (hPP : P * P = P) (hPE : P * E = E)
    (A B R : F → Matrix H H ℂ) (A₀ : F → Matrix I I ℂ) (C : F → Matrix K K ℂ)
    (hPB : ∀ x, Commute P (B x)) (hA₀ : ∀ x, P * A x * E = E * A₀ x)
    {δ η ξ : ℝ}
    (hψ' : ‖(WithLp.toLp 2 (E *ᵥ ψ.ofLp) : EuclideanSpace ℂ H)‖ = 1)
    (hr : let φ := AlgState.vector (WithLp.toLp 2 (E *ᵥ ψ.ofLp)) hψ'
      (𝔼 x, φ.norm (A x - R x) ^ 2) ≤ δ)
    (hc : let φ := AlgState.vector (WithLp.toLp 2 (E *ᵥ ψ.ofLp)) hψ'
      (𝔼 x, φ.norm (R x - B x) ^ 2) ≤ η)
    (exactIntertwines : Bool)
    (he : exactIntertwines → ∀ x, D * R x = C x * D)
    (hi : ¬exactIntertwines → let φ := AlgState.vector (WithLp.toLp 2 (E *ᵥ ψ.ofLp)) hψ'
      (𝔼 x, let M := D * R x - C x * D
        (φ (Mᴴ * M)).re) ≤ ξ) :
    (𝔼 x, ‖(WithLp.toLp 2 (((D * E) * A₀ x - C x * (D * E)) *ᵥ ψ.ofLp) :
      EuclideanSpace ℂ K)‖ ^ 2) ≤ if exactIntertwines then δ + η else 2 * (δ + η + ξ) := by
  simp only [AlgState.norm_vector] at hr hc
  let before (x : F) : EuclideanSpace ℂ H :=
    WithLp.toLp 2 ((E * A₀ x - R x * E) *ᵥ ψ.ofLp)
  let after (x : F) : EuclideanSpace ℂ K :=
    WithLp.toLp 2 ((D * R x - C x * D) *ᵥ (E *ᵥ ψ.ofLp))
  have hb : (𝔼 x, ‖before x‖ ^ 2) ≤ δ + η :=
    (expect_le_expect fun x _ => norm_compressed_action_sub_sq_le ψ E P (A x) (B x) (R x)
      hP hPP hPE (hPB x) (A₀ x) (hA₀ x)).trans ((expect_add_distrib ..).le.trans (add_le_add hr hc))
  have hsplit (x : F) :
      (WithLp.toLp 2 (((D * E) * A₀ x - C x * (D * E)) *ᵥ ψ.ofLp) : EuclideanSpace ℂ K) =
        WithLp.toLp 2 (D *ᵥ (before x).ofLp) + after x := by
    have hmat : (D * E) * A₀ x - C x * (D * E) =
        D * (E * A₀ x - R x * E) + (D * R x - C x * D) * E := by
      simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
      abel
    simp only [hmat, before, after, add_mulVec, WithLp.toLp_add, ← mulVec_mulVec]
  simp_rw [hsplit]
  split_ifs with hexact
  · have hzero (x : F) : after x = 0 := by simp [after, he hexact x]
    simpa only [hzero, add_zero, norm_toLp_mulVec_of_conjTranspose_mul_self hD] using hb
  · have hi' : (𝔼 x, ‖after x‖ ^ 2) ≤ ξ :=
      (expect_congr rfl fun x _ => norm_toLp_mulVec_sq_eq _ (WithLp.toLp 2 (E *ᵥ ψ.ofLp))).le.trans
        (hi hexact)
    have ht (x : F) : ‖WithLp.toLp 2 (D *ᵥ (before x).ofLp) + after x‖ ^ 2 ≤
        2 * (‖before x‖ ^ 2 + ‖after x‖ ^ 2) := by
      have hs := norm_add_le (WithLp.toLp 2 (D *ᵥ (before x).ofLp) : EuclideanSpace ℂ K) (after x)
      rw [norm_toLp_mulVec_of_conjTranspose_mul_self hD] at hs
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hs 2
      nlinarith only [hsq, sq_nonneg (‖before x‖ - ‖after x‖)]
    refine (expect_le_expect fun x _ => ht x).trans ?_
    rw [← mul_expect, expect_add_distrib]
    linarith only [hb, hi']

private theorem map_average_basisObservable
    {n : ℕ} {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (e : Matrix I I ℂ →ₗ[ℂ] Matrix K K ℂ)
    (M : PauliBraidingQuestion n Bool → Measurement ((Bool × Bool) ⊕ Bool) (Matrix I I ℂ))
    (N : PauliBraidingQuestion n Bool → Measurement ((Bool × Bool) ⊕ Bool) (Matrix K K ℂ))
    (hN : ∀ q a, (N q).effect a = e ((M q).effect a))
    (b : Bool) (x : Fin n → Bool) :
    e (𝔼 d, pauliBraidingBasisObservable M b x d) =
      𝔼 d, pauliBraidingBasisObservable N b x d := by
  classical
  refine (map_expect (e.restrictScalars ℚ≥0)
    (fun d => pauliBraidingBasisObservable M b x d) univ).trans (expect_congr rfl fun d _ => ?_)
  let q := PauliConsistencyQuestion.ofChecked b x d
  let f : (Bool × Bool) ⊕ Bool → Bool := Sum.elim q.braidingCheckedBit fun _ => false
  change e (((M q.toBraidingQuestion).map f).observable) =
    ((N q.toBraidingQuestion).map f).observable
  simp only [Measurement.observable_map, map_sum, map_smul, hN]

private theorem compress_average_basisObservable
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : PauliBraidingQuestion n Bool → POVM ((Bool × Bool) ⊕ Bool) I)
    (a₀ : (Bool × Bool) ⊕ Bool) (b : Bool) (x : Fin n → Bool) :
    let e := ancillaEmbed (ι := I) a₀
    eᴴ * (𝔼 d, pauliBraidingBasisObservable (fun q => ((M q).dilate a₀).toMeasurement) b x d) *
      e = 𝔼 d, pauliBraidingBasisObservable (fun q => (M q).toMeasurement) b x d := by
  intro e
  let compress := (mulRightLinearMap I ℂ e).comp
    (mulLeftLinearMap (I × ((Bool × Bool) ⊕ Bool)) ℂ eᴴ)
  exact map_average_basisObservable compress _ _
    (fun q a => ((M q).compress_dilate a₀ a).symm) b x

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

/-- The same pair of isometries certifies the EPR subspace and both players'
basis observables from the verifier, averaged over the dummy string.
All comparisons are made on the original strategy's state. -/
structure PauliBraidingExtraction
    {J : Type u} {L : Type v} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
    (S : QuantumStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) I K)
    (V : Matrix ((Fin n → Bool) × J) I ℂ) (W : Matrix ((Fin n → Bool) × L) K ℂ)
    (ε : ℝ) : Prop where
  /-- Alice's local map has orthonormal columns. -/
  alice_isometry : Vᴴ * V = 1
  /-- Bob's local map has orthonormal columns. -/
  bob_isometry : Wᴴ * W = 1
  /-- The extracted state has little squared norm outside the EPR subspace. -/
  epr : let E := extractedEprProjection (Q := Fin n → Bool) (J := J) (K := L)
    ‖(WithLp.toLp 2 (((E - 1) * (V ⊗ₖ W)) *ᵥ S.state.ofLp) :
      EuclideanSpace ℂ (((Fin n → Bool) × J) × (Fin n → Bool) × L))‖ ^ 2 ≤
      3 * pauliBraidingTwistedCommutationError (3 * ε) +
        2 * pauliBraidingRoundedConsistencyError (3 * ε)
  /-- Alice's dummy-averaged observable acts as the corresponding extracted Pauli. -/
  alice : ∀ b,
    let A (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable S.toCommuting.alice b x d
    let C (x : Fin n → Bool) := kroneckerOne
      ((cond b (pauliZPow x) (pauliXPow x)) ⊗ₖ (1 : Matrix J J ℂ))
    let T := V ⊗ₖ W
    (𝔼 x, ‖(WithLp.toLp 2 ((T * A x - C x * T) *ᵥ S.state.ofLp) :
      EuclideanSpace ℂ (((Fin n → Bool) × J) × (Fin n → Bool) × L))‖ ^ 2) ≤
      if b then pauliBraidingRoundingError (3 * ε) + pauliBraidingRoundedConsistencyError (3 * ε)
      else 2 * (pauliBraidingRoundingError (3 * ε) + pauliBraidingRoundedConsistencyError (3 * ε) +
        pauliBraidingTwistedCommutationError (3 * ε))
  /-- Bob's dummy-averaged observable acts as the corresponding extracted Pauli. -/
  bob : ∀ b,
    let B (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable S.toCommuting.bob b x d
    let C (x : Fin n → Bool) := oneKronecker
      ((cond b (pauliZPow x) (pauliXPow x)) ⊗ₖ (1 : Matrix L L ℂ))
    let T := V ⊗ₖ W
    (𝔼 x, ‖(WithLp.toLp 2 ((T * B x - C x * T) *ᵥ S.state.ofLp) :
      EuclideanSpace ℂ (((Fin n → Bool) × J) × (Fin n → Bool) × L))‖ ^ 2) ≤
      if b then pauliBraidingRoundingError (3 * ε) + pauliBraidingRoundedConsistencyError (3 * ε)
      else 2 * (pauliBraidingRoundingError (3 * ε) + pauliBraidingRoundedConsistencyError (3 * ε) +
        pauliBraidingTwistedCommutationError (3 * ε))

/-- A strategy near the optimal CHSH braiding score has one pair of local isometries
certifying the EPR state and the dummy-averaged basis observables. The conclusion applies
to arbitrary finite-dimensional POVMs, with errors independent of the width. -/
theorem exists_pauliBraidingExtraction
    (S : QuantumStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) I K)
    {ε : ℝ}
    (hwin : (2 + Real.cos (π / 8) ^ 2) / 3 - ε ≤
      (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).quantumWinProb S) :
    ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J)
      (L : Type v) (_ : Fintype L) (_ : DecidableEq L)
      (V : Matrix ((Fin n → Bool) × J) I ℂ)
      (W : Matrix ((Fin n → Bool) × L) K ℂ),
      PauliBraidingExtraction S V W ε := by
  let a₀ : (Bool × Bool) ⊕ Bool := .inl (false, false)
  let T := S.dilate a₀ a₀
  have hscore :
      (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).quantumWinProb T =
        (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).quantumWinProb S := by
    rw [SeededGame.quantumWinProb, SeededGame.quantumWinProb]
    exact congrArg _ (funext₂ (S.answers_dilate a₀ a₀))
  obtain ⟨P, Q, _, hclose, hcross, ⟨J, _, _, V, hV⟩, ⟨L, _, _, W, hW⟩⟩ :=
    exists_local_pauliCompression_of_pauliBraidingGame T
      (fun b q => S.isProjective_alice_dilate a₀ a₀ (.basis b q))
      (fun b q => S.isProjective_bob_dilate a₀ a₀ (.basis b q))
      (by rwa [hscore])
  have h := norm_sub_extractedEprProjection_sq_le T.state T.norm_state
    (fun b => (P b).charObs) (fun b => (Q b).charObs) V W hV hW hcross
  let E := extractedEprProjection (Q := Fin n → Bool) (J := J) (K := L)
  let e₁ := ancillaEmbed (ι := I) a₀
  let e₂ := ancillaEmbed (ι := K) a₀
  let U := V * e₁
  let R := W * e₂
  let D := V ⊗ₖ W
  let F := QuantumStrategy.dilateEmbed (ι := I) (κ := K) a₀ a₀
  have he₁ : e₁ᴴ * e₁ = 1 := conjTranspose_ancillaEmbed_mul a₀
  have he₂ : e₂ᴴ * e₂ = 1 := conjTranspose_ancillaEmbed_mul a₀
  have hD : Dᴴ * D = 1 := by
    simp only [D, conjTranspose_kronecker, ← mul_kronecker_mul, hV.isometry, hW.isometry,
      one_kronecker_one]
  have hDF : D * F = U ⊗ₖ R := (mul_kronecker_mul V e₁ W e₂).symm
  let η := pauliBraidingRoundedConsistencyError (3 * ε)
  let ξ := pauliBraidingTwistedCommutationError (3 * ε)
  refine ⟨J, inferInstance, inferInstance, L, inferInstance, inferInstance, U, R,
    ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV.isometry,
      Matrix.one_mul, he₁]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW.isometry,
      Matrix.one_mul, he₂]
  · change ‖(WithLp.toLp 2 (((E - 1) * (V ⊗ₖ W)) *ᵥ
      (QuantumStrategy.dilateEmbed a₀ a₀ *ᵥ S.state.ofLp)) :
        EuclideanSpace ℂ (((Fin n → Bool) × J) × (Fin n → Bool) × L))‖ ^ 2 ≤ _ at h
    rwa [mulVec_mulVec, Matrix.mul_assoc, QuantumStrategy.dilateEmbed, ← mul_kronecker_mul] at h
  · intro b
    let A (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable T.toCommuting.alice b x d
    let A₀ (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable S.toCommuting.alice b x d
    let M (x : Fin n → Bool) :=
      kroneckerOne (κ := K × ((Bool × Bool) ⊕ Bool)) ((P b).charObs x)
    let O (x : Fin n → Bool) :=
      oneKronecker (ι := I × ((Bool × Bool) ⊕ Bool)) ((Q b).charObs x)
    let C (x : Fin n → Bool) := (cond b (pauliZPow x) (pauliXPow x)) ⊗ₖ
      (1 : Matrix J J ℂ)
    let G := kroneckerOne (κ := K × ((Bool × Bool) ⊕ Bool)) (e₁ * e₁ᴴ)
    have hG : Gᴴ = G := by
      simp only [G, kroneckerOne_apply, conjTranspose_kronecker, conjTranspose_mul,
        conjTranspose_conjTranspose, conjTranspose_one]
    have hGG : G * G = G := by
      simp only [G, ← map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc e₁ᴴ e₁,
        he₁, Matrix.one_mul]
    have hGF : G * F = F := by
      simp only [G, F, QuantumStrategy.dilateEmbed, kroneckerOne_apply, ← mul_kronecker_mul,
        Matrix.mul_assoc, e₁, he₁, Matrix.mul_one, Matrix.one_mul]
    have hcompress (x : Fin n → Bool) : G * A x * F = F * A₀ x := by
      dsimp only [A, A₀]
      have hT := map_average_basisObservable kroneckerOne.toLinearMap
        (fun q => (T.alice q).toMeasurement) T.toCommuting.alice (fun _ _ => rfl) b x
      have hS := map_average_basisObservable kroneckerOne.toLinearMap
        (fun q => (S.alice q).toMeasurement) S.toCommuting.alice (fun _ _ => rfl) b x
      change kroneckerOne _ = _ at hT hS
      rw [← hT, ← hS]
      simp only [G, F, QuantumStrategy.dilateEmbed, kroneckerOne_apply, ← mul_kronecker_mul,
        Matrix.one_mul, Matrix.mul_one]
      congr 1
      rw [Matrix.mul_assoc e₁ e₁ᴴ, Matrix.mul_assoc e₁]
      exact congrArg (e₁ * ·) (compress_average_basisObservable S.alice a₀ b x)
    have he (hb : b) (x : Fin n → Bool) : D * M x = kroneckerOne (C x) * D := by
      subst hb
      simp only [D, M, C, Bool.cond_true, kroneckerOne_apply, ← mul_kronecker_mul,
        Matrix.mul_one, Matrix.one_mul, hV.intertwinesZ]
    have hi (hb : ¬b) : (𝔼 x, let N := D * M x - kroneckerOne (C x) * D
        (T.toCommuting.state (Nᴴ * N)).re) ≤ ξ := by
      obtain rfl := Bool.eq_false_iff.2 hb
      have hg (x : Fin n → Bool) :
          D * M x - kroneckerOne (C x) * D = (V * (P false).charObs x - C x * V) ⊗ₖ W := by
        simp only [D, M, kroneckerOne_apply, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
        exact Matrix.ext fun ⟨_, _⟩ ⟨_, _⟩ => (sub_mul ..).symm
      simp only [hg, conjTranspose_kronecker, ← mul_kronecker_mul, hW.isometry,
        ← kroneckerOne_apply]
      exact hV.intertwinesX
    have hh := expect_norm_compressed_action_sub_sq_le S.state F D hD G hG hGG hGF
      A O M A₀ (kroneckerOne ∘ C) (fun _ => commute_kroneckerOne_oneKronecker _ _)
      hcompress T.norm_state (hclose b).1 (hcross b) b he hi
    rwa [hDF] at hh
  · intro b
    let A (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable T.toCommuting.bob b x d
    let A₀ (x : Fin n → Bool) := 𝔼 d, pauliBraidingBasisObservable S.toCommuting.bob b x d
    let M (x : Fin n → Bool) :=
      oneKronecker (ι := I × ((Bool × Bool) ⊕ Bool)) ((Q b).charObs x)
    let O (x : Fin n → Bool) :=
      kroneckerOne (κ := K × ((Bool × Bool) ⊕ Bool)) ((P b).charObs x)
    let C (x : Fin n → Bool) := (cond b (pauliZPow x) (pauliXPow x)) ⊗ₖ
      (1 : Matrix L L ℂ)
    let G := oneKronecker (ι := I × ((Bool × Bool) ⊕ Bool)) (e₂ * e₂ᴴ)
    let φ := T.toCommuting.state
    have hG : Gᴴ = G := by
      simp only [G, oneKronecker_apply, conjTranspose_kronecker, conjTranspose_mul,
        conjTranspose_conjTranspose, conjTranspose_one]
    have hGG : G * G = G := by
      simp only [G, ← map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc e₂ᴴ e₂,
        he₂, Matrix.one_mul]
    have hGF : G * F = F := by
      simp only [G, F, QuantumStrategy.dilateEmbed, oneKronecker_apply, ← mul_kronecker_mul,
        Matrix.mul_assoc, e₂, he₂, Matrix.mul_one, Matrix.one_mul]
    have hcompress (x : Fin n → Bool) : G * A x * F = F * A₀ x := by
      dsimp only [A, A₀]
      have hT := map_average_basisObservable oneKronecker.toLinearMap
        (fun q => (T.bob q).toMeasurement) T.toCommuting.bob (fun _ _ => rfl) b x
      have hS := map_average_basisObservable oneKronecker.toLinearMap
        (fun q => (S.bob q).toMeasurement) S.toCommuting.bob (fun _ _ => rfl) b x
      change oneKronecker _ = _ at hT hS
      rw [← hT, ← hS]
      simp only [G, F, QuantumStrategy.dilateEmbed, oneKronecker_apply, ← mul_kronecker_mul,
        Matrix.one_mul, Matrix.mul_one]
      congr 1
      rw [Matrix.mul_assoc e₂ e₂ᴴ, Matrix.mul_assoc e₂]
      exact congrArg (e₂ * ·) (compress_average_basisObservable S.bob a₀ b x)
    have hc : (𝔼 x, φ.norm (M x - O x) ^ 2) ≤ η := by
      simpa only [φ.norm_sub_comm (M _) (O _)] using hcross b
    have he (hb : b) (x : Fin n → Bool) : D * M x = oneKronecker (C x) * D := by
      subst hb
      simp only [D, M, C, Bool.cond_true, oneKronecker_apply, ← mul_kronecker_mul,
        Matrix.mul_one, Matrix.one_mul, hW.intertwinesZ]
    have hi (hb : ¬b) : (𝔼 x, let N := D * M x - oneKronecker (C x) * D
        (φ (Nᴴ * N)).re) ≤ ξ := by
      obtain rfl := Bool.eq_false_iff.2 hb
      have hg (x : Fin n → Bool) :
          D * M x - oneKronecker (C x) * D = V ⊗ₖ (W * (Q false).charObs x - C x * W) := by
        simp only [D, M, oneKronecker_apply, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
        exact Matrix.ext fun ⟨_, _⟩ ⟨_, _⟩ => (mul_sub ..).symm
      simp only [hg, conjTranspose_kronecker, ← mul_kronecker_mul, hV.isometry,
        ← oneKronecker_apply]
      exact hW.intertwinesX
    have hh := expect_norm_compressed_action_sub_sq_le S.state F D hD G hG hGG hGF
      A O M A₀ (oneKronecker ∘ C) (fun _ => (commute_kroneckerOne_oneKronecker _ _).symm)
      hcompress T.norm_state (hclose b).2 hc b he hi
    rwa [hDF] at hh

end Game

end Cslib.PCP
