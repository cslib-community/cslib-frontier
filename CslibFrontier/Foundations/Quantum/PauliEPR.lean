/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled
public import CslibFrontier.Foundations.Quantum.PauliTwirl
import CslibFrontier.Foundations.Quantum.Algebra.Expect
import CslibFrontier.Foundations.Quantum.DensityMatrix.Pure
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# EPR projection from paired Pauli strings

Averaging the same Pauli string on both halves gives the rank-one projection onto
the maximally entangled state. The phase average removes unequal bit strings and
the translation average makes all remaining diagonal amplitudes equal.

## Main definitions

* `Cslib.Quantum.extractedRegisterEmbedding`: place a two-register operator beside ancillas.
* `Cslib.Quantum.extractedEprProjection`: the EPR projector in player order.

## Main results

* `Cslib.Quantum.expect_pauliString_kronecker_self`: the paired Pauli projection.
* `Cslib.Quantum.norm_sub_eprProjector_sq_le`: disagreement on the two families bounds
  the squared weight outside the EPR subspace.
-/

public section

namespace Cslib.Quantum

open Matrix Finset BitString
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The uniform paired Pauli average is the projection onto the EPR vector on the
two extracted bit-string registers. -/
theorem expect_pauliString_kronecker_self :
    (𝔼 a : ι → Bool, 𝔼 b : ι → Bool, pauliString a b ⊗ₖ pauliString a b) =
      pureState (maxEntangled (ι → Bool)) := by
  have hcard : (Fintype.card (ι → Bool) : ℂ) = (2 : ℂ) ^ Fintype.card ι := by simp
  have hscale :
      (((Real.sqrt (Fintype.card (ι → Bool)))⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt (Fintype.card (ι → Bool)))⁻¹ : ℝ) : ℂ) =
        (Fintype.card (ι → Bool) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _),
      Complex.ofReal_inv, Complex.ofReal_natCast]
  ext ⟨x, x'⟩ ⟨y, y'⟩
  have hentry (a b : ι → Bool) :
      (pauliString a b * single y y' (1 : ℂ) * (pauliString a b)ᴴ :
        Matrix (ι → Bool) (ι → Bool) ℂ) x x' =
        pauliString a b x y * pauliString a b x' y' := by
    rw [Matrix.mul_apply, sum_eq_single y'
      (fun j _ hj => by rw [mul_single_apply_of_ne _ _ _ _ _ hj, zero_mul]) (by simp),
      mul_single_apply_same, mul_one, conjTranspose_apply]
    by_cases hy : y' = x' + a <;> simp [pauliString_apply, hy]
  have he := congrArg (fun M : Matrix (ι → Bool) (ι → Bool) ℂ => M x x')
    (sum_pauliTwirl (single y y' 1))
  simp only [Matrix.sum_apply, hentry, Matrix.smul_apply, smul_eq_mul, ← hcard] at he
  simp only [Finset.expect, Matrix.smul_apply, Matrix.sum_apply, Matrix.kronecker_apply,
    ← NNRat.cast_smul_eq_nnqsmul ℂ, NNRat.cast_inv, NNRat.cast_natCast, Finset.card_univ,
    smul_eq_mul, ← mul_sum, ← mul_assoc, pureState_apply, maxEntangled_apply]
  rw [mul_assoc, he]
  rcases eq_or_ne y y' with rfl | hy
  · rw [trace_single_eq_same, mul_one, Matrix.one_apply]
    have hne : (Fintype.card (ι → Bool) : ℂ) ≠ 0 := mod_cast Fintype.card_ne_zero
    by_cases hx : x = x'
    · simp only [hx, ite_true, inv_mul_cancel₀ hne, mul_one,
        Complex.star_def, Complex.conj_ofReal, hscale]
    · simp [hx]
  · simp [trace_single_eq_of_ne y y' (1 : ℂ) hy, hy]

private theorem one_sub_involution_nonneg
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {U : A} (hU : IsSelfAdjoint U) (hU2 : U * U = 1) : 0 ≤ 1 - U := by
  have h := nonneg_of_isSelfAdjoint_of_mul_self (isSelfAdjoint_signProj hU true)
    (signProj_mul_self hU2 true)
  have hs : (2 : ℂ) • signProj U true = 1 - U := by
    rw [signProj, smul_smul, show (2 : ℂ) * 2⁻¹ = 1 by norm_num, one_smul]
    simp [signVal_true, sub_eq_add_neg]
  rw [← hs]
  exact smul_nonneg (by norm_num : (0 : ℂ) ≤ 2) h

private theorem re_apply_one_sub_kronecker_self
    (φ : AlgState (Matrix ((ι → Bool) × (ι → Bool)) ((ι → Bool) × (ι → Bool)) ℂ))
    (M : Matrix (ι → Bool) (ι → Bool) ℂ) (hM : IsSelfAdjoint M) (hM2 : M * M = 1) :
    (φ (1 - M ⊗ₖ M)).re =
      (φ.norm (kroneckerOne (κ := ι → Bool) M - oneKronecker M) ^ 2) / 2 := by
  have h := φ.norm_sub_sq_eq_of_mul_self
    (hM.map (kroneckerOne (κ := ι → Bool))) (hM.map (oneKronecker (ι := ι → Bool)))
    (by rw [← map_mul, hM2, map_one]) (by rw [← map_mul, hM2, map_one])
  simp only [kroneckerOne_apply, oneKronecker_apply, ← mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul] at h
  rw [map_sub, AlgState.map_one, Complex.sub_re, Complex.one_re, kroneckerOne_apply,
    oneKronecker_apply, h]
  ring

private theorem one_sub_mul_le_of_involutions
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {U V : A} (hsU : IsSelfAdjoint U) (hsV : IsSelfAdjoint V)
    (hU2 : U * U = 1) (hV2 : V * V = 1) (hc : Commute U V) :
    1 - U * V ≤ (1 - U) + (1 - V) := by
  have hcomm : Commute (1 - U) (1 - V) :=
    (Commute.one_right (1 - U)).sub_right ((Commute.one_left V).sub_left hc)
  have hpos : 0 ≤ (1 - U) * (1 - V) :=
    Commute.mul_nonneg (one_sub_involution_nonneg hsU hU2)
      (one_sub_involution_nonneg hsV hV2) hcomm
  rw [← sub_nonneg]
  have he : (1 - U) + (1 - V) - (1 - U * V) = (1 - U) * (1 - V) := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]
    abel
  rwa [he]

private theorem re_apply_one_sub_pairedPauli_le
    (φ : AlgState (Matrix ((ι → Bool) × (ι → Bool)) ((ι → Bool) × (ι → Bool)) ℂ))
    (a b : ι → Bool) :
      (φ (1 - pauliString a b ⊗ₖ pauliString a b)).re ≤
        (φ (1 - pauliXPow a ⊗ₖ pauliXPow a)).re +
        (φ (1 - pauliZPow b ⊗ₖ pauliZPow b)).re := by
  let U := pauliXPow a ⊗ₖ pauliXPow a
  let V := pauliZPow b ⊗ₖ pauliZPow b
  have hsU : IsSelfAdjoint U := by
    change Uᴴ = U
    simp only [U, conjTranspose_kronecker, (pauliXPow_isHermitian a).eq]
  have hsV : IsSelfAdjoint V := by
    change Vᴴ = V
    simp only [V, conjTranspose_kronecker, (pauliZPow_isHermitian b).eq]
  have hU2 : U * U = 1 := by
    simp only [U, ← mul_kronecker_mul, pauliXPow_mul_self, one_kronecker_one]
  have hV2 : V * V = 1 := by
    simp only [V, ← mul_kronecker_mul, pauliZPow_mul_self, one_kronecker_one]
  have hc : Commute U V := by
    change U * V = V * U
    simp only [U, V, ← mul_kronecker_mul, pauliZPow_mul_pauliXPow,
      smul_kronecker, kronecker_smul, smul_smul, ← Complex.ofReal_mul, signVal_mul_self,
      Complex.ofReal_one, one_smul]
  have hp := φ.re_apply_mono (one_sub_mul_le_of_involutions hsU hsV hU2 hV2 hc)
  simpa only [map_add, Complex.add_re, U, V, ← mul_kronecker_mul, pauliString] using hp

/-- Squared leakage is the state's weight on the complementary EPR projection. -/
theorem norm_sub_eprProjector_sq_eq
    (φ : AlgState (Matrix ((ι → Bool) × (ι → Bool)) ((ι → Bool) × (ι → Bool)) ℂ)) :
    let E := pureState (maxEntangled (ι → Bool))
    φ.norm (E - 1) ^ 2 = (φ (1 - E)).re := by
  intro E
  have hE : IsSelfAdjoint E := (posSemidef_pureState _).isHermitian.isSelfAdjoint
  have hE2 : E * E = E := pureState_mul_self_of_norm_eq_one _ norm_maxEntangled
  rw [φ.norm_sq, star_sub, hE.star_eq, star_one, sub_mul, mul_sub, mul_sub,
    hE2, mul_one, one_mul, one_mul]
  congr 2
  abel

/-- Agreement of the two ideal X and Z families controls the part of a state outside
the EPR projection. The state may be the restriction of a state with extra registers. -/
theorem norm_sub_eprProjector_sq_le
    (φ : AlgState (Matrix ((ι → Bool) × (ι → Bool)) ((ι → Bool) × (ι → Bool)) ℂ)) :
    φ.norm (pureState (maxEntangled (ι → Bool)) - 1) ^ 2 ≤
      (1 / 2) * ((𝔼 a, φ.norm (kroneckerOne (pauliXPow a) - oneKronecker (pauliXPow a)) ^ 2) +
        (𝔼 b, φ.norm (kroneckerOne (pauliZPow b) - oneKronecker (pauliZPow b)) ^ 2)) := by
  rw [norm_sub_eprProjector_sq_eq φ, ← expect_pauliString_kronecker_self]
  have hL : (φ (1 - 𝔼 a : ι → Bool, 𝔼 b : ι → Bool, pauliString a b ⊗ₖ pauliString a b)).re =
      𝔼 a : ι → Bool, 𝔼 b : ι → Bool, (φ (1 - pauliString a b ⊗ₖ pauliString a b)).re := by
    simp_rw [← φ.re_apply_expect, expect_sub_distrib, Fintype.expect_const]
  rw [hL]
  refine (expect_le_expect fun a _ => expect_le_expect fun b _ =>
    re_apply_one_sub_pairedPauli_le φ a b).trans_eq ?_
  simp only [expect_add_distrib, Fintype.expect_const,
    re_apply_one_sub_kronecker_self φ _
      (pauliXPow_isHermitian _).isSelfAdjoint (pauliXPow_mul_self _),
    re_apply_one_sub_kronecker_self φ _
      (pauliZPow_isHermitian _).isSelfAdjoint (pauliZPow_mul_self _),
    div_eq_inv_mul, ← mul_expect]
  ring


section Projection

variable {Q J K : Type*} [Fintype Q] [DecidableEq Q]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

/-- Place an operator on the extracted registers, with identities on both ancillas.
The target basis keeps each register beside its player's ancilla. -/
noncomputable def extractedRegisterEmbedding :
    Matrix (Q × Q) (Q × Q) ℂ →⋆ₐ[ℂ] Matrix ((Q × J) × Q × K) ((Q × J) × Q × K) ℂ :=
  (reindexStarAlgEquiv ℂ ℂ (Equiv.prodProdProdComm Q J Q K).symm).toStarAlgHom.comp
    (kroneckerOne (κ := J × K))

/-- A first-side register operator remains on the first side after placing the ancillas. -/
theorem extractedRegisterEmbedding_left (A : Matrix Q Q ℂ) :
    extractedRegisterEmbedding (J := J) (K := K) (kroneckerOne A) =
      kroneckerOne (κ := Q × K) (A ⊗ₖ (1 : Matrix J J ℂ)) := by
  ext ⟨⟨i, j⟩, k, l⟩ ⟨⟨i', j'⟩, k', l'⟩
  change (A i i' * (1 : Matrix Q Q ℂ) k k') * (1 : Matrix (J × K) (J × K) ℂ)
      (j, l) (j', l') =
    (A i i' * (1 : Matrix J J ℂ) j j') * (1 : Matrix (Q × K) (Q × K) ℂ) (k, l) (k', l')
  rw [← one_kronecker_one, ← one_kronecker_one]
  simp only [kronecker_apply]
  ring

/-- A second-side register operator remains on the second side after placing the ancillas. -/
theorem extractedRegisterEmbedding_right (A : Matrix Q Q ℂ) :
    extractedRegisterEmbedding (J := J) (K := K) (oneKronecker A) =
      oneKronecker (ι := Q × J) (A ⊗ₖ (1 : Matrix K K ℂ)) := by
  ext ⟨⟨i, j⟩, k, l⟩ ⟨⟨i', j'⟩, k', l'⟩
  change ((1 : Matrix Q Q ℂ) i i' * A k k') * (1 : Matrix (J × K) (J × K) ℂ)
      (j, l) (j', l') =
    (1 : Matrix (Q × J) (Q × J) ℂ) (i, j) (i', j') * (A k k' * (1 : Matrix K K ℂ) l l')
  rw [← one_kronecker_one, ← one_kronecker_one]
  simp only [kronecker_apply]
  ring

/-- Projection onto the EPR state on the two extracted registers, with the
identity on both ancillary registers. The registers are in player order. -/
@[expose] noncomputable def extractedEprProjection :
    Matrix ((Q × J) × Q × K) ((Q × J) × Q × K) ℂ :=
  extractedRegisterEmbedding (J := J) (K := K) (pureState (maxEntangled Q))


/-- Regrouping the extracted registers puts the pure EPR projector before both ancillas. -/
theorem reindex_extractedEprProjection :
    let e := Equiv.prodProdProdComm Q J Q K
    reindex e e (extractedEprProjection (Q := Q) (J := J) (K := K)) =
      pureState (maxEntangled Q) ⊗ₖ (1 : Matrix (J × K) (J × K) ℂ) := by
  intro e
  ext p q
  change (pureState (maxEntangled Q) ⊗ₖ (1 : Matrix (J × K) (J × K) ℂ))
    (e (e.symm p)) (e (e.symm q)) = _
  rw [e.apply_symm_apply, e.apply_symm_apply]

/-- The extracted EPR projection is self-adjoint. -/
theorem isHermitian_extractedEprProjection :
    (extractedEprProjection (Q := Q) (J := J) (K := K)).IsHermitian := by
  rw [IsHermitian, ← Matrix.star_eq_conjTranspose, extractedEprProjection, ← map_star,
    Matrix.star_eq_conjTranspose, (posSemidef_pureState (maxEntangled Q)).isHermitian.eq]

/-- The extracted EPR projection is idempotent. -/
theorem extractedEprProjection_mul_self [Nonempty Q] :
    extractedEprProjection (Q := Q) (J := J) (K := K) * extractedEprProjection =
      extractedEprProjection := by
  rw [extractedEprProjection, ← map_mul, pureState_mul_self_of_norm_eq_one _ norm_maxEntangled]


end Projection

end Cslib.Quantum
