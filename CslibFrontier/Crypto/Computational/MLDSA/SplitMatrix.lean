/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.CommitmentEntropy
public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204Roots
public import CslibFrontier.Crypto.Computational.SIS.Polynomial
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.HashFamily.MatrixKernel
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.NormNum.Prime

/-!
# Evaluation coordinates for the ML-DSA matrix

The 256 distinct roots of `X^256 + 1` over the FIPS 204 field split the negacyclic coefficient
algebra into 256 copies of that field. Evaluation commutes with each module matrix product.
The kernel of a square coefficient matrix is therefore the product of the finite-field kernels
in the 256 coordinates. Barbosa et al. [BarbosaEtAl2023, Appendix A.2, Lemma 8, p. 35] use
this splitting to express the rank of a uniform ring matrix as the sum of the ranks of
independent uniform field matrices.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Polynomial Finset
open scoped BigOperators

private abbrev F := ZMod 8380417

private instance : Fact (Nat.Prime 8380417) := ⟨by norm_num1⟩

private noncomputable def evalHom :
    AdjoinRoot ((X : F[X]) ^ 256 + 1) →ₐ[F] (Fin 256 → F) :=
  AlgHom.pi fun i => AdjoinRoot.liftAlgHom _ (AlgHom.id F F) (nttNode i) (by
    simp [nttNode_pow])

private theorem evalHom_surjective : Function.Surjective evalHom := fun v =>
  ⟨AdjoinRoot.mk _ (Lagrange.interpolate Finset.univ nttNode v), funext fun i =>
    Lagrange.eval_interpolate_at_node v nttNode_injective.injOn (Finset.mem_univ i)⟩

/-- Evaluation at the 256 odd powers of 1753, the primitive 512th root specified by FIPS 204.
The index orders the roots by exponent. -/
noncomputable def splitPolynomial : Negacyclic (ZMod 8380417) 256 ≃ₐ[ZMod 8380417] Poly :=
  let h := negacyclicEquiv (R := F) (n := 256) (by decide)
  let f := evalHom.comp h.toAlgHom
  AlgEquiv.ofBijective f <| (Fintype.bijective_iff_surjective_and_card f).2
    ⟨evalHom_surjective.comp h.surjective, Fintype.card_congr Negacyclic.coeffsEquiv⟩

private noncomputable def splitVector (m : ℕ) :
    (Fin m → Poly) ≃ (Fin 256 → Fin m → F) :=
  (Equiv.piCongrRight fun _ => Negacyclic.coeffsEquiv.symm.trans splitPolynomial.toEquiv).trans
    (Equiv.piComm _)

/-- The field matrix obtained by evaluating every coefficient polynomial at the same root. -/
noncomputable def matrixBlock {k ℓ : ℕ} (A : Matrix (Fin k) (Fin ℓ) Poly) (r : Fin 256) :
    Matrix (Fin k) (Fin ℓ) (ZMod 8380417) :=
  fun i j => splitPolynomial (Negacyclic.ofCoeffs (A i j)) r

private theorem splitVector_mul {k ℓ : ℕ} (A : Matrix (Fin k) (Fin ℓ) Poly)
    (y : Fin ℓ → Poly) (r : Fin 256) :
    splitVector k (moduleSISMap A y) r = (matrixBlock A r).mulVec (splitVector ℓ y r) := by
  funext i
  change splitPolynomial (Negacyclic.ofCoeffs (innerPoly (A i) y)) r = _
  rw [Negacyclic.ofCoeffs_innerPoly]
  simp only [_root_.dotProduct, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply]
  rfl

/-- The actual coefficient kernel is equivalent to independently choosing a kernel vector for
each evaluation coordinate. This includes singular and zero matrices. -/
noncomputable def splitMatrixKernel {k ℓ : ℕ} (A : Matrix (Fin k) (Fin ℓ) Poly) :
    { y : Fin ℓ → Poly // moduleSISMap A y = 0 } ≃
      { v : Fin 256 → Fin ℓ → ZMod 8380417 // ∀ r, (matrixBlock A r).mulVec (v r) = 0 } := by
  let e := splitVector ℓ
  have hz (x : Fin k → Poly) : splitVector k x = 0 ↔ x = 0 := by
    have hzero : splitVector k 0 = 0 := by
      funext r j
      exact congrFun (map_zero splitPolynomial) r
    rw [← hzero, Equiv.apply_eq_iff_eq]
  have hh (y : Fin ℓ → Poly) : moduleSISMap A y = 0 ↔
      ∀ r, (matrixBlock A r).mulVec (e y r) = 0 := by
    rw [← hz, funext_iff]
    simp only [splitVector_mul, Pi.zero_apply, e]
  exact e.subtypeEquiv hh

private noncomputable def blocksEquiv (k ℓ : ℕ) :
    Matrix (Fin k) (Fin ℓ) Poly ≃ (Fin 256 → Matrix (Fin k) (Fin ℓ) F) :=
  let e := Negacyclic.coeffsEquiv.symm.trans splitPolynomial.toEquiv
  { toFun := matrixBlock
    invFun := fun B i j => e.symm fun r => B r i j
    left_inv := fun A => by
      funext i j
      exact e.symm_apply_apply (A i j)
    right_inv := fun B => by
      funext r i j
      exact congrFun (e.apply_symm_apply fun r => B r i j) r }

private theorem expect_firstRows {k ℓ : ℕ} (h : ℓ ≤ k)
    (g : Matrix (Fin ℓ) (Fin ℓ) Poly → ℝ) :
    (𝔼 A : Matrix (Fin k) (Fin ℓ) Poly, g (A.submatrix (Fin.castLE h) id)) = 𝔼 B, g B := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fintype.expect_comp_fst (β := Fin m → Fin ℓ → Poly) g]
  exact Fintype.expect_equiv (Fin.appendEquiv (α := Fin ℓ → Poly) ℓ m).symm _ _ fun _ => rfl

private theorem mean_sqrt_blockKernel_lt (ℓ : ℕ) :
    (𝔼 D : Fin 256 → Matrix (Fin ℓ) (Fin ℓ) F,
      Real.sqrt (Nat.card {v : Fin 256 → Fin ℓ → F // ∀ r, (D r).mulVec (v r) = 0})) <
      11 / 10 := by
  apply lt_of_le_of_lt (Cslib.Probability.expect_sqrt_card_joint_kernel_le 256)
  rw [ZMod.card]
  have root : (2800 : ℝ) ≤ Real.sqrt 8380417 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  calc
    _ ≤ (1 + (2801 : ℝ)⁻¹) ^ 256 := by
      gcongr
      norm_num1
      linarith
    _ < 11 / 10 := by norm_num

private theorem mean_sqrt_squareKernel_lt (ℓ : ℕ) :
    (𝔼 B : Matrix (Fin ℓ) (Fin ℓ) Poly,
      Real.sqrt (Nat.card {y : Fin ℓ → Poly // moduleSISMap B y = 0})) < 11 / 10 :=
  lt_of_eq_of_lt (Fintype.expect_equiv (blocksEquiv ℓ ℓ) _ _ fun B =>
    congrArg (fun k : ℕ => Real.sqrt (k : ℝ)) (Nat.card_congr (splitMatrixKernel B)))
    (mean_sqrt_blockKernel_lt ℓ)

/-- Over a uniform FIPS coefficient matrix, the mean square root of the top submatrix's kernel
size is below `11/10` at all three levels. Evaluation gives 256 independent uniform field
matrices and preserves the entire kernel, including its size at singular matrices. -/
theorem mean_sqrt_commitmentKernelSize_lt (s : Level) :
    (𝔼 A : PublicMatrix s, Real.sqrt (commitmentKernelSize s A)) < 11 / 10 := by
  have hdim : s.params.ℓ ≤ s.params.k := by cases s <;> decide
  exact lt_of_eq_of_lt (expect_firstRows hdim fun B =>
    Real.sqrt (Nat.card {y : Fin s.params.ℓ → Poly // moduleSISMap B y = 0}))
    (mean_sqrt_squareKernel_lt s.params.ℓ)

/-- Expected square root of the largest commitment probability under the uniform public
matrix. This uses the entire matrix distribution, including singular square submatrices. -/
theorem mean_sqrt_commitmentGuessProbability_le (s : Level) :
    (𝔼 A : PublicMatrix s, Real.sqrt
      (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal) ≤
      (11 / 10) / Real.sqrt (2 ^ s.commitmentBoxBits) := by
  calc
    _ ≤ 𝔼 A : PublicMatrix s, Real.sqrt (commitmentKernelSize s A) /
        Real.sqrt (2 ^ s.commitmentBoxBits) := by
      refine expect_le_expect fun A _ => ?_
      rw [← Real.sqrt_div (Nat.cast_nonneg _)]
      exact Real.sqrt_le_sqrt (commitmentGuessProbability_le_kernel_div_pow s A)
    _ ≤ _ := by
      simp only [div_eq_mul_inv, ← expect_mul]
      gcongr
      exact (mean_sqrt_commitmentKernelSize_lt s).le

/-! ### Statistical distance of the classical signing simulation -/

open Cslib.Probability Cslib.OracleComp Cslib.Crypto.Protocols.ROMSignature
open scoped ENNReal

/-- Discharge the maximum commitment probability in a fixed-matrix game comparison by
averaging over the FIPS matrix. The bound is numerical at all three parameter sets. -/
theorem closeTo_uniformMatrix_of_guessProbability (s : Level) (count : ℕ)
    {α : Type} {real sim : PublicMatrix s → PMF α}
    (h : ∀ A, CloseTo (real A) (sim A)
      (count * commitmentGuessProbability s.params (by cases s <;> decide) A)) :
    CloseTo ((PMF.uniformOfFintype _).bind real) ((PMF.uniformOfFintype _).bind sim)
      (count * ENNReal.ofReal ((11 / 10) / Real.sqrt (2 ^ s.commitmentBoxBits))) := by
  classical
  let p (A : PublicMatrix s) := commitmentGuessProbability s.params (by cases s <;> decide) A
  have hp (A) : p A ≤ 1 := iSup_le fun _ => PMF.coe_le_one _ _
  have hf (A) : p A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hp A)
  have hmean : (𝔼 A : PublicMatrix s, (p A).toReal) ≤
      (11 / 10) / Real.sqrt (2 ^ s.commitmentBoxBits) :=
    (expect_le_expect fun A _ => Real.le_sqrt_of_sq_le <| by
      nlinarith [ENNReal.toReal_nonneg (a := p A),
        show (p A).toReal ≤ 1 by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hp A)]).trans
      (mean_sqrt_commitmentGuessProbability_le s)
  refine (CloseTo.bind_right_tsum (PMF.uniformOfFintype (PublicMatrix s))
    (err := fun A => count * p A) (fun A _ => h A)).mono ?_
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, mul_left_comm _ (count : ℝ≥0∞), ← mul_sum]
  refine mul_le_mul_of_nonneg_left ((ENNReal.le_ofReal_iff_toReal_le
    (ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.mpr fun a _ => hf a)) (by positivity)).2 ?_)
    zero_le
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_sum fun a _ => hf a, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Fintype.expect_eq_sum_div_card, div_eq_inv_mul] using hmean

/-- The adaptive ideal-mask signing simulation under a uniform FIPS matrix, for a digest
expander that always returns a sparse challenge. The error counts all signing attempts and hash
queries. The adversary chooses its program after receiving the public key. -/
theorem closeTo_simulateSigning_uniformMatrix (s : Level) (d ω K : ℕ) {Digest α : Type}
    (dist : PMF Digest) (expand : Digest → Poly)
    (hc : ∀ c, InBall s.params.τ (expand c))
    (s₁ : Fin s.params.ℓ → Poly) (s₂ : Fin s.params.k → Poly)
    (hs₁ : ∀ i j, |(s₁ i j).valMinAbs| ≤ s.params.η)
    (hs₂ : ∀ i j, |(s₂ i j).valMinAbs| ≤ s.params.η)
    (forger : PublicKey s.params → OracleComp (SigningROMSpec s.params Digest) α) {S H : ℕ}
    (hS : ∀ pk, IsCostBounded signingCost (forger pk) S)
    (hH : ∀ pk, IsCostBounded hashCost (forger pk) H) :
    CloseTo ((PMF.uniformOfFintype _).bind fun A =>
      let sk : SecretKey s.params := ⟨A, s₁, s₂⟩
      (runBoundedSigningROM s.params false d ω K (by cases s <;> decide)
        dist expand sk (forger sk.publicKey)).map Prod.fst)
      ((PMF.uniformOfFintype _).bind fun A =>
        let pk := (SecretKey.mk A s₁ s₂ : SecretKey s.params).publicKey
        (runAcceptedSigningROM s.params K dist
          (fun c => simulateFreshSigningAttempt s.params d ω (by cases s <;> decide) pk (expand c))
          (forger pk)).map Prod.fst)
      ((2 * (S * K) * H + (S * K).choose 2 : ℕ) * ENNReal.ofReal
        ((11 / 10) / Real.sqrt (2 ^ s.commitmentBoxBits))) := by
  have hval : s.params.Valid := by
    cases s
    · exact Params.valid_mldsa44
    · exact Params.valid_mldsa65
    · exact Params.valid_mldsa87
  refine closeTo_uniformMatrix_of_guessProbability s _ fun A =>
    closeTo_runBoundedSigningROM_simulate s.params hval
      (by cases s <;> decide)
      (by cases s <;> decide)
      d ω K dist expand ⟨A, s₁, s₂⟩ hs₁ hs₂ hc (hS _) (hH _)

end Cslib.Crypto.MLDSA.FIPS204
