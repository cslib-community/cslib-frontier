/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumEntropy
public import CslibFrontier.Foundations.Quantum.POVM.Density
public import CslibFrontier.Probability.MutualInformation
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefKernel
import CslibFrontier.Foundations.Quantum.DensityMatrix.PartialTracePairing
import CslibFrontier.Foundations.Quantum.DensityMatrix.Pure
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyDataProcessing
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyDomination
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Lagrange

/-!
# Von Neumann entropy, Holevo's bound, and superdense-coding optimality

For a density matrix `ρ` on `ℂ^ι`, the **von Neumann entropy**
`S(ρ) = -tr(ρ log₂ ρ)` (`Cslib.Quantum.vonNeumannEntropy`) equals the Shannon entropy of its
eigenvalues (`vonNeumannEntropy_eq_sum_eigenvalues`), vanishes on pure states
(`vonNeumannEntropy_pureState`), is invariant under rectangular isometries
(`vonNeumannEntropy_conj_isometry`), is additive on Kronecker products
(`vonNeumannEntropy_kronecker`), and satisfies subadditivity (`vonNeumannEntropy_subadditivity`)
and the Araki–Lieb triangle inequality (`vonNeumannEntropy_arakiLieb`).

For a finite ensemble `(p, ρ)` of states `ρ_x` drawn according to `p : PMF X`, the **Holevo
information** `χ(p, ρ) = S(∑_x p(x) ρ_x) - ∑_x p(x) S(ρ_x)` (`Cslib.Quantum.holevoInformation`)
equals the classical–quantum mutual information `mutualInformation (classicalQuantumState p ρ)`
converted from nats to bits (`mutualInformation_classicalQuantumState_eq_holevoInformation`).
Combining Stinespring isometric invariance with partial-trace monotonicity
(`relativeEntropy_partialTraceRight_le`) gives monotonicity of quantum relative entropy and of
Holevo information under arbitrary trace-preserving Kraus channels (`relativeEntropy_kraus_le`,
`holevoInformation_kraus_le`).

Specializing Kraus monotonicity to the quantum-to-classical POVM measurement channel proves
**Holevo's bound** ([Holevo][Holevo1973]; [Nielsen and Chuang][NielsenChuang2010], Theorem 12.1;
[Watrous][Watrous2018], Theorem 5.49): for every prior `p : PMF X`, density-matrix ensemble `ρ`,
and POVM `M : POVM Y ι`, the classical mutual information between `X` and `M`'s outcome `Y`
satisfies `I(X : Y) ≤ χ(p, ρ)` (`mutualInfo_measureDensity_le_holevoInformation`).

Two communication bounds follow immediately:
* **Unassisted quantum communication** ([Watrous][Watrous2018], Corollary 5.50;
  [de Wolf][deWolf2019], Chapter 15, Theorem 3, part 1): without prior entanglement, sending a
  register on `ℂ^ι` conveys at most `log₂ |ι|` bits (`mutualInfo_measureDensity_le_logb_card`),
  and sending `n` qubits conveys at most `n` bits (`mutualInfo_measureDensity_qubits_le`).
* **Entanglement-assisted quantum communication and superdense-coding optimality**
  ([de Wolf][deWolf2019], Chapter 15, Theorem 3, part 2): even when Alice and Bob share an
  arbitrary prior bipartite state `σ` on `ℂ^{ι₀ × κ}` (with Bob's system `ℂ^κ` of arbitrary finite
  dimension) and Alice encodes `x` by any trace-preserving Kraus channel from `ℂ^{ι₀}` to `ℂ^ι`
  before sending the `ι` register to Bob, no-signalling (`partialTraceLeft_kraus`) together with
  subadditivity and Araki–Lieb caps the Holevo information at `2 log₂ |ι|`
  (`holevoInformation_kraus_onFirst_le`), so Bob's joint measurement on `ι × κ` extracts at most
  `2 log₂ |ι|` bits (`mutualInfo_entanglementAssisted_le`), or `2n` bits for `n` transmitted
  qubits (`mutualInfo_entanglementAssisted_qubits_le`). For one qubit (`ι = Bool`) this upper
  bound is `2` bits, attained by superdense coding ([Bennett and Wiesner][BennettWiesner1992]).

## Main definitions

* `Cslib.Quantum.vonNeumannEntropy`: von Neumann entropy `S(ρ) = -tr(ρ log₂ ρ)` in bits.
* `Cslib.Quantum.holevoInformation`: Holevo's `χ` quantity `S(∑_x p_x ρ_x) - ∑_x p_x S(ρ_x)`.

## Main results

* `Cslib.Quantum.relativeEntropy_conj_isometry`, `Cslib.Quantum.relativeEntropy_kraus_le`:
  isometric invariance and Kraus-channel monotonicity of quantum relative entropy.
* `Cslib.Quantum.vonNeumannEntropy_subadditivity`, `Cslib.Quantum.vonNeumannEntropy_arakiLieb`:
  subadditivity and Araki–Lieb triangle inequality for von Neumann entropy.
* `Cslib.Quantum.holevoInformation_nonneg`, `Cslib.Quantum.holevoInformation_le_logb_card`,
  `Cslib.Quantum.holevoInformation_le_entropy`, `Cslib.Quantum.holevoInformation_kraus_le`:
  fundamental bounds and data processing for Holevo information.
* `Cslib.Quantum.mutualInfo_measureDensity_le_holevoInformation`: Holevo's bound `I(X : Y) ≤ χ`.
* `Cslib.Quantum.mutualInfo_measureDensity_le_logb_card`,
  `Cslib.Quantum.mutualInfo_measureDensity_qubits_le`: unassisted `log₂ |ι|` and `n`-qubit caps.
* `Cslib.Quantum.holevoInformation_kraus_onFirst_le`,
  `Cslib.Quantum.mutualInfo_entanglementAssisted_le`,
  `Cslib.Quantum.mutualInfo_entanglementAssisted_qubits_le`,
  `Cslib.Quantum.mutualInfo_unitary_onFirst_le`: entanglement-assisted `2 log₂ |ι|` and `2n`-qubit
  caps (optimality of superdense coding).

## References

* [A. S. Holevo, *Bounds for the Quantity of Information Transmitted by a Quantum Communication
  Channel*][Holevo1973]
* [M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*][NielsenChuang2010],
  Section 12.1.1, Theorem 12.1.
* [J. Watrous, *The Theory of Quantum Information*][Watrous2018], Chapter 5, Proposition 5.19,
  Theorems 5.23–5.25, 5.35, and 5.49, Corollary 5.50.
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019], Chapter 15, Theorem 3.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open Cslib.Probability.PMF
open scoped ComplexOrder Kronecker MatrixOrder

/-! ### Isometric invariance and Kraus monotonicity of quantum relative entropy -/

section KrausDataProcessing

variable {ι ι' κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem pow_succ_conj_isometry {V : Matrix κ ι ℂ} (hV : Vᴴ * V = 1)
    (A : Matrix ι ι ℂ) (n : ℕ) : (V * A * Vᴴ) ^ (n + 1) = V * A ^ (n + 1) * Vᴴ := by
  induction n with
  | zero => simp only [zero_add, pow_one]
  | succ n ih =>
    rw [pow_succ (V * A * Vᴴ) (n + 1), ih]
    calc
      (V * A ^ (n + 1) * Vᴴ) * (V * A * Vᴴ)
          = V * (A ^ (n + 1) * (Vᴴ * V) * A) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * A ^ (n + 2) * Vᴴ := by rw [hV, Matrix.mul_one, ← pow_succ]

private theorem aeval_conj_isometry {V : Matrix κ ι ℂ} (hV : Vᴴ * V = 1)
    (A : Matrix ι ι ℂ) {P : Polynomial ℝ} (hP : P.eval 0 = 0) :
    Polynomial.aeval (V * A * Vᴴ) P = V * Polynomial.aeval A P * Vᴴ := by
  obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr hP
  rw [map_zero, sub_zero] at hQ
  subst hQ
  clear hP
  induction Q using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rw [mul_add, map_add, map_add, Matrix.mul_add, Matrix.add_mul, ihp, ihq]
  | monomial n r =>
    have hmon : Polynomial.X * Polynomial.monomial n r = Polynomial.monomial (n + 1) r := by
      rw [Polynomial.X, Polynomial.monomial_mul_monomial, one_mul, add_comm 1 n]
    rw [hmon, Polynomial.aeval_monomial, Polynomial.aeval_monomial]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
    rw [pow_succ_conj_isometry hV A n]

private theorem cfc_conj_isometry {f : ℝ → ℝ} (hf0 : f 0 = 0) {V : Matrix κ ι ℂ}
    (hV : Vᴴ * V = 1) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    cfc f (V * A * Vᴴ) = V * cfc f A * Vᴴ := by
  classical
  have hVA : IsSelfAdjoint (V * A * Vᴴ) := by
    change (V * A * Vᴴ)ᴴ = V * A * Vᴴ
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
  let T : Set ℝ := insert 0 (spectrum ℝ (V * A * Vᴴ) ∪ spectrum ℝ A)
  have hT : T.Finite :=
    ((V * A * Vᴴ).finite_real_spectrum.union A.finite_real_spectrum).insert 0
  let P := Lagrange.interpolate hT.toFinset id f
  have hp (r : ℝ) (hr : r ∈ T) : P.eval r = f r :=
    Lagrange.eval_interpolate_at_node f (Set.injOn_id _) (hT.mem_toFinset.mpr hr)
  have hcVA : cfc f (V * A * Vᴴ) = Polynomial.aeval (V * A * Vᴴ) P := by
    rw [← cfc_polynomial P (V * A * Vᴴ) hVA]
    exact cfc_congr fun r hr => (hp r (Set.mem_insert_of_mem _ (Or.inl hr))).symm
  have hcA : cfc f A = Polynomial.aeval A P := by
    rw [← cfc_polynomial P A hA.isSelfAdjoint]
    exact cfc_congr fun r hr => (hp r (Set.mem_insert_of_mem _ (Or.inr hr))).symm
  rw [hcVA, hcA, aeval_conj_isometry hV A ((hp 0 (Set.mem_insert 0 _)).trans hf0)]

omit [DecidableEq κ] in
private theorem supportLE_conj_isometry_iff {V : Matrix κ ι ℂ} (hV : Vᴴ * V = 1)
    {ρ σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) :
    SupportLE (V * ρ * Vᴴ) (V * σ * Vᴴ) ↔ SupportLE ρ σ := by
  constructor
  · intro h v hv
    have hVv : Vᴴ *ᵥ (V *ᵥ v) = v := by rw [mulVec_mulVec, hV, one_mulVec]
    have hρw := h (V *ᵥ v) (by rw [← mulVec_mulVec, hVv, ← mulVec_mulVec, hv, mulVec_zero])
    rw [← mulVec_mulVec, hVv, ← mulVec_mulVec] at hρw
    have hmul := congrArg (Vᴴ *ᵥ ·) hρw
    rwa [mulVec_mulVec, hV, one_mulVec, mulVec_zero] at hmul
  · intro h w hw
    have hdot : star (Vᴴ *ᵥ w) ⬝ᵥ (σ *ᵥ (Vᴴ *ᵥ w)) = 0 := by
      rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec, vecMul_vecMul,
        ← dotProduct_mulVec, mulVec_mulVec, hw, dotProduct_zero]
    rw [← mulVec_mulVec, ← mulVec_mulVec, h (Vᴴ *ᵥ w) (hσ.dotProduct_mulVec_zero_iff.mp hdot),
      mulVec_zero]

omit [DecidableEq κ] in
private theorem trace_conj_isometry_mul {V : Matrix κ ι ℂ} (hV : Vᴴ * V = 1)
    (A B : Matrix ι ι ℂ) : ((V * A * Vᴴ) * (V * B * Vᴴ)).trace = (A * B).trace := by
  calc
    ((V * A * Vᴴ) * (V * B * Vᴴ)).trace
        = (V * (A * (Vᴴ * V) * B) * Vᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = (Vᴴ * (V * (A * (Vᴴ * V) * B))).trace := trace_mul_comm _ Vᴴ
    _ = ((Vᴴ * V) * (A * (Vᴴ * V) * B)).trace := by rw [← Matrix.mul_assoc Vᴴ V]
    _ = (A * B).trace := by rw [hV, Matrix.one_mul, Matrix.mul_one]

private theorem relativeEntropyReal_conj_isometry {V : Matrix κ ι ℂ} (hV : Vᴴ * V = 1)
    {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relativeEntropyReal (V * ρ * Vᴴ) (V * σ * Vᴴ) = relativeEntropyReal ρ σ := by
  unfold relativeEntropyReal
  rw [cfc_conj_isometry Real.log_zero hV hρ, cfc_conj_isometry Real.log_zero hV hσ,
    ← Matrix.sub_mul, ← Matrix.mul_sub, trace_conj_isometry_mul hV]

/-- Rectangular isometries preserve quantum relative entropy, including infinite divergence. -/
theorem relativeEntropy_conj_isometry {V : Matrix κ ι ℂ} (hV : Vᴴ * V = 1)
    {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    relativeEntropy (V * ρ * Vᴴ) (V * σ * Vᴴ) = relativeEntropy ρ σ := by
  have hiff : SupportLE (V * ρ * Vᴴ) (V * σ * Vᴴ) ↔ SupportLE ρ σ :=
    supportLE_conj_isometry_iff hV hσ
  by_cases hs : SupportLE ρ σ
  · rw [relativeEntropy_of_supportLE (hiff.mpr hs), relativeEntropy_of_supportLE hs,
      relativeEntropyReal_conj_isometry hV hρ.isHermitian hσ.isHermitian]
  · rw [relativeEntropy_of_not_supportLE (mt hiff.mp hs), relativeEntropy_of_not_supportLE hs]

/-- **Data processing for Kraus channels**: applying a trace-preserving Kraus operation
`ρ ↦ ∑_{a ∈ s} K_a ρ K_aᴴ` with `∑_{a ∈ s} K_aᴴ K_a = 1` cannot increase quantum relative entropy.
Proved via the Stinespring isometry into `ℂ^{ι' × s}` followed by `partialTraceRight`. -/
theorem relativeEntropy_kraus_le [Fintype ι'] [DecidableEq ι']
    {α : Type*} (s : Finset α) (K : α → Matrix ι' ι ℂ) (hK : ∑ a ∈ s, (K a)ᴴ * K a = 1)
    {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    relativeEntropy (∑ a ∈ s, K a * ρ * (K a)ᴴ) (∑ a ∈ s, K a * σ * (K a)ᴴ) ≤
      relativeEntropy ρ σ := by
  classical
  let V : Matrix (ι' × ↥s) ι ℂ := Matrix.of fun p j => K p.2.1 p.1 j
  have hV : Vᴴ * V = 1 := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_prod_type_right]
    calc
      ∑ a : ↥s, ∑ i' : ι', Vᴴ i (i', a) * V (i', a) j
          = ∑ a : ↥s, ((K a.1)ᴴ * K a.1) i j := by
            refine sum_congr rfl fun a _ => ?_
            simp only [Matrix.mul_apply, conjTranspose_apply, V, of_apply]
      _ = (∑ a ∈ s, (K a)ᴴ * K a) i j := by
            rw [Finset.sum_coe_sort s (fun a => ((K a)ᴴ * K a) i j), Matrix.sum_apply]
      _ = (1 : Matrix ι ι ℂ) i j := by rw [hK]
  have htr (A : Matrix ι ι ℂ) :
      partialTraceRight (V * A * Vᴴ) = ∑ a ∈ s, K a * A * (K a)ᴴ := by
    ext i' j'
    rw [partialTraceRight_apply, Matrix.sum_apply,
      ← Finset.sum_coe_sort s (fun a => (K a * A * (K a)ᴴ) i' j')]
    refine sum_congr rfl fun a _ => ?_
    simp only [Matrix.mul_apply, conjTranspose_apply, V, of_apply]
  rw [← htr ρ, ← htr σ, ← relativeEntropy_conj_isometry hV hρ hσ]
  exact relativeEntropy_partialTraceRight_le
    (hρ.mul_mul_conjTranspose_same V) (hσ.mul_mul_conjTranspose_same V)

end KrausDataProcessing

/-! ### Von Neumann entropy -/

section VonNeumannEntropy

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Von Neumann entropy** `S(ρ) = -tr(ρ log₂ ρ)` of a matrix on `ℂ^ι`, in bits. -/
@[expose] noncomputable def vonNeumannEntropy (ρ : Matrix ι ι ℂ) : ℝ :=
  -(ρ * cfc Real.log ρ).trace.re / Real.log 2

private theorem isHermitian_diagonal_real {μ : Type*} [DecidableEq μ] (d : μ → ℝ) :
    (diagonal fun i => (d i : ℂ)).IsHermitian := by
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  ext i
  simp

private theorem cfc_diagonal_real (f : ℝ → ℝ) (d : ι → ℝ) :
    cfc f (diagonal fun i => (d i : ℂ)) = diagonal fun i => (f (d i) : ℂ) := by
  classical
  let D : Matrix ι ι ℂ := diagonal fun i => (d i : ℂ)
  let T : Set ℝ := spectrum ℝ D ∪ Set.range d
  have hT : T.Finite := D.finite_real_spectrum.union (Set.finite_range d)
  let P := Lagrange.interpolate hT.toFinset id f
  have hp (r : ℝ) (hr : r ∈ T) : P.eval r = f r :=
    Lagrange.eval_interpolate_at_node f (Set.injOn_id _) (hT.mem_toFinset.mpr hr)
  have hc : cfc f D = Polynomial.aeval D P := by
    rw [← cfc_polynomial P D (isHermitian_diagonal_real d).isSelfAdjoint]
    exact cfc_congr fun r hr => (hp r (Or.inl hr)).symm
  have haeval (Q : Polynomial ℝ) :
      Polynomial.aeval D Q = diagonal fun i => ((Q.eval (d i) : ℝ) : ℂ) := by
    induction Q using Polynomial.induction_on' with
    | add p q ihp ihq =>
      rw [map_add, ihp, ihq]
      ext i j
      by_cases hij : i = j <;> simp [hij, Polynomial.eval_add]
    | monomial n r =>
      rw [Polynomial.aeval_monomial]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [D, Algebra.algebraMap_eq_smul_one, diagonal_pow, Polynomial.eval_monomial,
          Complex.real_smul]
      · simp [D, Algebra.algebraMap_eq_smul_one, diagonal_pow, hij]
  rw [hc, haeval P]
  congr 1; funext i
  exact congrArg Complex.ofReal (hp (d i) (Or.inr ⟨i, rfl⟩))

/-- Von Neumann entropy of a real diagonal matrix is the binary Shannon sum of its entries. -/
theorem vonNeumannEntropy_diagonal (d : ι → ℝ) :
    vonNeumannEntropy (diagonal fun i => (d i : ℂ)) =
      (∑ i, Real.negMulLog (d i)) / Real.log 2 := by
  unfold vonNeumannEntropy
  rw [cfc_diagonal_real Real.log d, diagonal_mul_diagonal, trace_diagonal, Complex.re_sum]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re, Real.negMulLog]
  ring

/-- Rectangular isometries preserve von Neumann entropy. -/
theorem vonNeumannEntropy_conj_isometry {V : Matrix κ ι ℂ} (hV : Vᴴ * V = 1)
    {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy (V * ρ * Vᴴ) = vonNeumannEntropy ρ := by
  unfold vonNeumannEntropy
  rw [cfc_conj_isometry Real.log_zero hV hρ, trace_conj_isometry_mul hV]

/-- Von Neumann entropy equals `-∑_i λ_i log₂ λ_i` for the eigenvalues `λ_i` of `ρ`. -/
theorem vonNeumannEntropy_eq_sum_eigenvalues {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy ρ = (∑ i, Real.negMulLog (hρ.eigenvalues i)) / Real.log 2 := by
  let U : Matrix ι ι ℂ := hρ.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hρ.eigenvectorUnitary
  have hspec : ρ = U * diagonal (fun i => (hρ.eigenvalues i : ℂ)) * Uᴴ := hρ.spectral_theorem
  conv_lhs => rw [hspec]
  rw [vonNeumannEntropy_conj_isometry hU (isHermitian_diagonal_real _), vonNeumannEntropy_diagonal]

private noncomputable def eigenvaluePMF {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (hρ.posSemidef.isHermitian.eigenvalues i)) <| by
    have hsum : ∑ i, hρ.posSemidef.isHermitian.eigenvalues i = 1 := by
      have ht := hρ.posSemidef.isHermitian.trace_eq_sum_eigenvalues
      rw [hρ.trace_eq_one] at ht
      change (1 : ℂ) = ∑ i, (hρ.posSemidef.isHermitian.eigenvalues i : ℂ) at ht
      exact_mod_cast ht.symm
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hρ.posSemidef.eigenvalues_nonneg i), hsum,
      ENNReal.ofReal_one]

private theorem vonNeumannEntropy_eq_entropy_eigenvaluePMF {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) :
    vonNeumannEntropy ρ = entropy (eigenvaluePMF hρ) := by
  rw [vonNeumannEntropy_eq_sum_eigenvalues hρ.posSemidef.isHermitian, entropy_eq_sum]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [eigenvaluePMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (hρ.posSemidef.eigenvalues_nonneg i)]

/-- Von Neumann entropy of a density matrix is nonnegative. -/
theorem vonNeumannEntropy_nonneg {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    0 ≤ vonNeumannEntropy ρ := by
  rw [vonNeumannEntropy_eq_entropy_eigenvaluePMF hρ]
  exact entropy_nonneg _

/-- Every pure state has zero von Neumann entropy. -/
theorem vonNeumannEntropy_pureState {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    vonNeumannEntropy (pureState ψ) = 0 := by
  let V : Matrix ι Unit ℂ := Matrix.of fun i _ => ψ.ofLp i
  have hV : Vᴴ * V = 1 := by
    ext ⟨⟩ ⟨⟩
    rw [Matrix.mul_apply, Matrix.one_apply_eq]
    have hnorm : ∑ i : ι, ‖ψ.ofLp i‖ ^ 2 = 1 := by
      rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow]
    have hterm (i : ι) : Vᴴ () i * V i () = ((‖ψ.ofLp i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [V, conjTranspose_apply, of_apply]
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [hterm, ← Complex.ofReal_sum, hnorm, Complex.ofReal_one]
  have hpure : pureState ψ = V * (1 : Matrix Unit Unit ℂ) * Vᴴ := by
    ext i j
    simp [pureState_apply, V, Matrix.mul_apply, conjTranspose_apply]
  have hone : (1 : Matrix Unit Unit ℂ) = diagonal fun _ : Unit => ((1 : ℝ) : ℂ) := by
    ext ⟨⟩ ⟨⟩; simp
  rw [hpure, vonNeumannEntropy_conj_isometry hV isHermitian_one, hone, vonNeumannEntropy_diagonal]
  simp [Real.negMulLog]

/-- The maximally mixed state `(1 / |ι|) • 1` on a nonempty register has von Neumann entropy
`log₂ |ι|`. -/
theorem vonNeumannEntropy_maximallyMixed [Nonempty ι] :
    vonNeumannEntropy ((Fintype.card ι : ℂ)⁻¹ • (1 : Matrix ι ι ℂ)) =
      Real.logb 2 (Fintype.card ι) := by
  have hcard_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hdiag : ((Fintype.card ι : ℂ)⁻¹ • (1 : Matrix ι ι ℂ)) =
      diagonal fun _ : ι => (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [hdiag, vonNeumannEntropy_diagonal]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog, Real.log_inv,
    Real.logb]
  field_simp [hcard_pos.ne']

/-- Von Neumann entropy of any density matrix on `ℂ^ι` is at most `log₂ |ι|`. -/
theorem vonNeumannEntropy_le_logb_card {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) :
    vonNeumannEntropy ρ ≤ Real.logb 2 (Fintype.card ι) := by
  rw [vonNeumannEntropy_eq_entropy_eigenvaluePMF hρ]
  simpa only [Finset.card_univ] using
    entropy_le_logb_card_of_support_subset (eigenvaluePMF hρ) (s := Finset.univ)
      (fun _ _ => Finset.mem_univ _)

/-- Von Neumann entropy is additive across Kronecker products of density matrices. -/
theorem vonNeumannEntropy_kronecker {ρ : Matrix ι ι ℂ} {σ : Matrix κ κ ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    vonNeumannEntropy (ρ ⊗ₖ σ) = vonNeumannEntropy ρ + vonNeumannEntropy σ := by
  let hA := hρ.posSemidef.isHermitian
  let hB := hσ.posSemidef.isHermitian
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let W : Matrix κ κ ℂ := hB.eigenvectorUnitary
  let D : Matrix ι ι ℂ := diagonal fun i => (hA.eigenvalues i : ℂ)
  let E : Matrix κ κ ℂ := diagonal fun k => (hB.eigenvalues k : ℂ)
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hW : Wᴴ * W = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hUW : (U ⊗ₖ W)ᴴ * (U ⊗ₖ W) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hW, one_kronecker_one]
  have hkr : ρ ⊗ₖ σ = (U ⊗ₖ W) * (D ⊗ₖ E) * (U ⊗ₖ W)ᴴ := by
    conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem]
    change (U * D * Uᴴ) ⊗ₖ (W * E * Wᴴ) = _
    rw [conjTranspose_kronecker, mul_kronecker_mul, mul_kronecker_mul]
  have hDE_diag : D ⊗ₖ E =
      diagonal fun p : ι × κ => ((hA.eigenvalues p.1 * hB.eigenvalues p.2 : ℝ) : ℂ) := by
    ext ⟨i, k⟩ ⟨i', k'⟩
    by_cases hi : i = i' <;> by_cases hk : k = k' <;> simp [D, E, kroneckerMap_apply, hi, hk]
  rw [hkr, hDE_diag, vonNeumannEntropy_conj_isometry hUW (isHermitian_diagonal_real _),
    vonNeumannEntropy_diagonal, vonNeumannEntropy_eq_entropy_eigenvaluePMF hρ,
    vonNeumannEntropy_eq_entropy_eigenvaluePMF hσ]
  rw [← entropy_prod (eigenvaluePMF hρ) (eigenvaluePMF hσ), entropy_eq_sum]
  congr 1
  refine sum_congr rfl fun ⟨i, k⟩ _ => ?_
  rw [bind_map_prodMk_apply, ENNReal.toReal_mul, eigenvaluePMF, eigenvaluePMF,
    PMF.ofFintype_apply, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (hρ.posSemidef.eigenvalues_nonneg i),
    ENNReal.toReal_ofReal (hσ.posSemidef.eigenvalues_nonneg k)]

private theorem vonNeumannEntropy_transpose {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy ρᵀ = vonNeumannEntropy ρ := by
  let U : Matrix ι ι ℂ := hρ.eigenvectorUnitary
  let V : Matrix ι ι ℂ := U.map star
  let D : Matrix ι ι ℂ := diagonal fun i => (hρ.eigenvalues i : ℂ)
  have hV : Vᴴ * V = 1 := by
    have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hρ.eigenvectorUnitary
    ext i j
    have hij := congrArg star (congrFun (congrFun hU i) j)
    dsimp only [V]
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.map_apply, star_star,
      Matrix.one_apply, star_sum, star_mul'] at hij ⊢
    rw [hij]
    by_cases h : i = j <;> simp [h]
  have hmap : ρᵀ = V * D * Vᴴ := by
    have hspec : ρ = U * D * Uᴴ := hρ.spectral_theorem
    have h1 : ρᵀ = ρ.map star := by
      ext i j
      simpa only [transpose_apply, conjTranspose_apply, Matrix.map_apply] using
        (congrFun (congrFun hρ.eq j) i).symm
    rw [h1]
    conv_lhs => rw [hspec]
    ext i j
    dsimp only [V, D]
    simp only [Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply, star_sum, star_mul',
      star_star, diagonal_apply]
    refine sum_congr rfl fun k _ => congrArg (· * _) <| sum_congr rfl fun l _ => ?_
    by_cases hlk : l = k <;> simp [hlk, Complex.conj_ofReal]
  rw [hmap, vonNeumannEntropy_conj_isometry hV (isHermitian_diagonal_real _)]
  rw [vonNeumannEntropy_diagonal, vonNeumannEntropy_eq_sum_eigenvalues hρ]

/-- Both reduced states of a bipartite pure state have equal von Neumann entropy. -/
theorem vonNeumannEntropy_partialTrace_pureState_eq (ψ : EuclideanSpace ℂ (ι × κ)) :
    vonNeumannEntropy (partialTraceRight (pureState ψ)) =
      vonNeumannEntropy (partialTraceLeft (pureState ψ)) := by
  let M : Matrix ι κ ℂ := coefficients ψ
  have hL : partialTraceLeft (pureState ψ) = (Mᴴ * M)ᵀ := by
    ext k k'
    simp only [partialTraceLeft_apply, pureState_apply, Matrix.mul_apply, conjTranspose_apply,
      transpose_apply, M, coefficients, mul_comm]
  let B : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := fromBlocks 0 M 0 0
  obtain ⟨U, hU, hpolar⟩ := B.exists_unitary_polar
  let H := CFC.sqrt (Bᴴ * B)
  have hH : Hᴴ = H := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian.eq
  have hHsq : H * H = Bᴴ * B :=
    CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self B).nonneg
  have hBB : B * Bᴴ = U * (Bᴴ * B) * Uᴴ := by
    calc
      B * Bᴴ = (U * H) * (U * H)ᴴ := by rw [hpolar]
      _ = U * (H * H) * Uᴴ := by
        rw [conjTranspose_mul, hH]
        simp only [Matrix.mul_assoc]
      _ = U * (Bᴴ * B) * Uᴴ := by rw [hHsq]
  let V₁ : Matrix (ι ⊕ κ) ι ℂ := Matrix.of fun p i => if p = Sum.inl i then 1 else 0
  let V₂ : Matrix (ι ⊕ κ) κ ℂ := Matrix.of fun p k => if p = Sum.inr k then 1 else 0
  have hV₁ : V₁ᴴ * V₁ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    by_cases h : i = j
    · subst h; simp [V₁, conjTranspose_apply]
    · simp [V₁, conjTranspose_apply, h, eq_comm]
  have hV₂ : V₂ᴴ * V₂ = 1 := by
    ext k l
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    by_cases h : k = l
    · subst h; simp [V₂, conjTranspose_apply]
    · simp [V₂, conjTranspose_apply, h, eq_comm]
  have hblock₁ : B * Bᴴ = V₁ * (M * Mᴴ) * V₁ᴴ := by
    have hb : B * Bᴴ = fromBlocks (M * Mᴴ) 0 0 0 := by
      simp [B, fromBlocks_conjTranspose, fromBlocks_multiply]
    rw [hb]
    ext (i | k) (i' | k') <;> simp [V₁, Matrix.mul_apply, conjTranspose_apply]
  have hblock₂ : Bᴴ * B = V₂ * (Mᴴ * M) * V₂ᴴ := by
    have hb : Bᴴ * B = fromBlocks 0 0 0 (Mᴴ * M) := by
      simp [B, fromBlocks_conjTranspose, fromBlocks_multiply]
    rw [hb]
    ext (i | k) (i' | k') <;> simp [V₂, Matrix.mul_apply, conjTranspose_apply]
  rw [partialTraceRight_pureState_eq_coefficients, hL,
    vonNeumannEntropy_transpose (posSemidef_conjTranspose_mul_self M).isHermitian,
    ← vonNeumannEntropy_conj_isometry hV₁ (posSemidef_self_mul_conjTranspose M).isHermitian,
    ← hblock₁, hBB,
    vonNeumannEntropy_conj_isometry ((mem_unitaryGroup_iff').mp hU)
      (posSemidef_conjTranspose_mul_self B).isHermitian,
    hblock₂, vonNeumannEntropy_conj_isometry hV₂ (posSemidef_conjTranspose_mul_self M).isHermitian]

private theorem sum_single_conj_eq_diagonal (A : Matrix ι ι ℂ) :
    ∑ i : ι, single i i (1 : ℂ) * A * (single i i (1 : ℂ))ᴴ = diagonal fun i => A i i := by
  ext j k
  rw [Matrix.sum_apply]
  simp only [conjTranspose_single, star_one, Matrix.single_mul_mul_single, one_mul, mul_one,
    Matrix.single_apply]
  by_cases h : j = k
  · subst h
    simp
  · rw [diagonal_apply_ne _ h]
    exact Finset.sum_eq_zero fun i _ => ite_eq_right fun ⟨hj, hk⟩ => h (hj.symm.trans hk)

private theorem vonNeumannEntropy_le_vonNeumannEntropy_diag {ρ : Matrix ι ι ℂ}
    (hρ : IsDensityMatrix ρ) :
    vonNeumannEntropy ρ ≤ vonNeumannEntropy (diagonal fun i => ((ρ i i).re : ℂ)) := by
  have hne : Nonempty ι := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have ht := hρ.trace_eq_one
    rw [Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty] at ht
    exact zero_ne_one ht
  let K (i : ι) : Matrix ι ι ℂ := single i i 1
  have hK : ∑ i : ι, (K i)ᴴ * K i = 1 := by
    simp only [K, conjTranspose_single, star_one, single_mul_single_same, mul_one, sum_single_one]
  let π : Matrix ι ι ℂ := (Fintype.card ι : ℂ)⁻¹ • 1
  have hπ_real : π = (Fintype.card ι : ℝ)⁻¹ • (1 : Matrix ι ι ℂ) := by
    ext i j
    simp [π]
  have hπ_psd : π.PosSemidef := hπ_real ▸ PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg _))
  let Δρ := diagonal fun i => ((ρ i i).re : ℂ)
  have hΔρ : ∑ i : ι, K i * ρ * (K i)ᴴ = Δρ := by
    rw [sum_single_conj_eq_diagonal]
    congr 1
    funext j
    have hh := congrFun (congrFun hρ.posSemidef.isHermitian.eq j) j
    have hdiag_im : (ρ j j).im = 0 := by
      simpa only [conjTranspose_apply, Complex.star_def, Complex.ext_iff, Complex.conj_im,
        neg_eq_self] using (Complex.ext_iff.mp hh).2
    exact Complex.ext rfl hdiag_im
  have hΔπ : ∑ i : ι, K i * π * (K i)ᴴ = π := by
    rw [sum_single_conj_eq_diagonal]
    ext j k
    by_cases h : j = k <;> simp [π, h]
  have hk := relativeEntropy_kraus_le Finset.univ K hK hρ.posSemidef hπ_psd
  rw [hΔρ, hΔπ] at hk
  have hΔ_tr : Δρ.trace.re = 1 := by
    have ht := congrArg Complex.re hρ.trace_eq_one
    rw [Matrix.trace, Complex.re_sum, Complex.one_re] at ht
    simpa only [Δρ, trace_diagonal, Complex.re_sum, Complex.ofReal_re, diag_apply] using ht
  have hpos : (0 : ℝ) < (Fintype.card ι : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  have hsupp (A : Matrix ι ι ℂ) : SupportLE A 1 := fun v hv => by
    rw [one_mulVec] at hv
    simp [hv]
  have hcfc1 : cfc Real.log (1 : Matrix ι ι ℂ) = 0 := by
    have h1 : (1 : Matrix ι ι ℂ) = diagonal fun _ : ι => ((1 : ℝ) : ℂ) := by
      ext i j
      simp
    rw [h1, cfc_diagonal_real Real.log]
    ext i j; simp
  rw [hπ_real, relativeEntropy_smul_right (isHermitian_diagonal_real _) isHermitian_one hpos,
    relativeEntropy_smul_right hρ.posSemidef.isHermitian isHermitian_one hpos,
    relativeEntropy_of_supportLE (hsupp Δρ), relativeEntropy_of_supportLE (hsupp ρ),
    hΔ_tr, hρ.trace_eq_one, Complex.one_re, ← WithTop.coe_add, ← WithTop.coe_add,
    WithTop.coe_le_coe] at hk
  simp only [relativeEntropyReal, hcfc1, sub_zero] at hk
  rw [vonNeumannEntropy, vonNeumannEntropy,
    div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))]
  linarith

private theorem partialTraceRight_kronecker_conj_unitary
    {ι₁ κ₁ : Type*} [Fintype ι₁] [Fintype κ₁] [DecidableEq κ₁]
    (U : Matrix ι₁ ι₁ ℂ) {W : Matrix κ₁ κ₁ ℂ}
    (hW : W ∈ unitaryGroup κ₁ ℂ) (ρ : Matrix (ι₁ × κ₁) (ι₁ × κ₁) ℂ) :
    partialTraceRight ((U ⊗ₖ W) * ρ * (U ⊗ₖ W)ᴴ) = U * partialTraceRight ρ * Uᴴ := by
  classical
  have hstep : U ⊗ₖ W = (U ⊗ₖ (1 : Matrix κ₁ κ₁ ℂ)) * ((1 : Matrix ι₁ ι₁ ℂ) ⊗ₖ W) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have heq : (U ⊗ₖ W) * ρ * (U ⊗ₖ W)ᴴ =
      (U ⊗ₖ (1 : Matrix κ₁ κ₁ ℂ)) *
        (((1 : Matrix ι₁ ι₁ ℂ) ⊗ₖ W) * ρ * ((1 : Matrix ι₁ ι₁ ℂ) ⊗ₖ W)ᴴ) *
        (Uᴴ ⊗ₖ (1 : Matrix κ₁ κ₁ ℂ)) := by
    rw [hstep, conjTranspose_mul, conjTranspose_kronecker U (1 : Matrix κ₁ κ₁ ℂ),
      conjTranspose_one]
    simp only [Matrix.mul_assoc]
  have htrW : partialTraceRight
      (((1 : Matrix ι₁ ι₁ ℂ) ⊗ₖ W) * ρ * ((1 : Matrix ι₁ ι₁ ℂ) ⊗ₖ W)ᴴ) = partialTraceRight ρ := by
    have := partialTraceRight_kraus {()} (fun _ => W)
      (by rw [Finset.sum_singleton]; exact (mem_unitaryGroup_iff').mp hW) ρ
    rwa [Finset.sum_singleton] at this
  rw [heq, partialTraceRight_mul_kronecker_one, partialTraceRight_kronecker_one_mul, htrW]

private theorem conjTranspose_eigenvectorUnitary_mul {μ : Type*} [Fintype μ] [DecidableEq μ]
    {M : Matrix μ μ ℂ} (hM : M.IsHermitian) :
    (hM.eigenvectorUnitary : Matrix μ μ ℂ)ᴴ * M * (hM.eigenvectorUnitary : Matrix μ μ ℂ) =
      diagonal fun j => (hM.eigenvalues j : ℂ) := by
  let Z : Matrix μ μ ℂ := hM.eigenvectorUnitary
  have hZZ : Zᴴ * Z = 1 := Unitary.coe_star_mul_self hM.eigenvectorUnitary
  change Zᴴ * M * Z = _
  conv_lhs => rw [show M = Z * diagonal (fun j => (hM.eigenvalues j : ℂ)) * Zᴴ from
    hM.spectral_theorem]
  simp only [← Matrix.mul_assoc, hZZ, Matrix.one_mul]
  rw [Matrix.mul_assoc, hZZ, Matrix.mul_one]

/-- **Subadditivity of von Neumann entropy** ([Watrous][Watrous2018], Theorem 5.24):
`S(ρ_{AB}) ≤ S(ρ_A) + S(ρ_B)` for every bipartite density matrix `ρ`. -/
theorem vonNeumannEntropy_subadditivity {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : IsDensityMatrix ρ) :
    vonNeumannEntropy ρ ≤
      vonNeumannEntropy (partialTraceRight ρ) + vonNeumannEntropy (partialTraceLeft ρ) := by
  let hA := hρ.partialTraceRight.posSemidef.isHermitian
  let hB := hρ.partialTraceLeft.posSemidef.isHermitian
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let W : Matrix κ κ ℂ := hB.eigenvectorUnitary
  have hU_mem : Uᴴ ∈ unitaryGroup ι ℂ := Unitary.star_mem hA.eigenvectorUnitary.2
  have hW_mem : Wᴴ ∈ unitaryGroup κ ℂ := Unitary.star_mem hB.eigenvectorUnitary.2
  have hV_mem : (Uᴴ ⊗ₖ Wᴴ) ∈ unitaryGroup (ι × κ) ℂ := kronecker_mem_unitary hU_mem hW_mem
  let σ : Matrix (ι × κ) (ι × κ) ℂ := (Uᴴ ⊗ₖ Wᴴ) * ρ * (Uᴴ ⊗ₖ Wᴴ)ᴴ
  have hσ : IsDensityMatrix σ := hρ.conj_unitary hV_mem
  let q : PMF (ι × κ) := POVM.basis.measureDensity σ hσ
  have hnonneg (p : ι × κ) : 0 ≤ (σ p p).re := by
    simpa only [POVM.densityProb_basis] using POVM.densityProb_nonneg POVM.basis hσ.posSemidef p
  have hdiag : (diagonal fun p : ι × κ => ((σ p p).re : ℂ)) =
      diagonal fun p : ι × κ => ((q p).toReal : ℂ) := by
    ext p p'
    by_cases hp : p = p'
    · subst hp
      simp [q, POVM.measureDensity_apply, POVM.densityProb_basis, ENNReal.toReal_ofReal (hnonneg p)]
    · simp [hp]
  have hfst : q.map Prod.fst = eigenvaluePMF hρ.partialTraceRight := by
    ext i
    rw [PMF.map_apply, tsum_fintype, eigenvaluePMF, PMF.ofFintype_apply, Fintype.sum_prod_type,
      Finset.sum_eq_single i (fun _ _ h => by simp [Ne.symm h]) (by simp)]
    simp only [ite_true, q, POVM.measureDensity_apply, POVM.densityProb_basis]
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hnonneg (i, k), ← Complex.re_sum,
      ← partialTraceRight_apply]
    have h1 : partialTraceRight σ = Uᴴ * partialTraceRight ρ * U := by
      simpa only [σ, conjTranspose_conjTranspose] using
        partialTraceRight_kronecker_conj_unitary Uᴴ hW_mem ρ
    rw [h1, show Uᴴ * partialTraceRight ρ * U = _ from conjTranspose_eigenvectorUnitary_mul hA,
      diagonal_apply_eq, Complex.ofReal_re]
  have hsnd : q.map Prod.snd = eigenvaluePMF hρ.partialTraceLeft := by
    ext k
    rw [PMF.map_apply, tsum_fintype, eigenvaluePMF, PMF.ofFintype_apply,
      Fintype.sum_prod_type_right,
      Finset.sum_eq_single k (fun _ _ h => by simp [Ne.symm h]) (by simp)]
    simp only [ite_true, q, POVM.measureDensity_apply, POVM.densityProb_basis]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hnonneg (i, k), ← Complex.re_sum,
      ← partialTraceLeft_apply]
    have h1 : partialTraceLeft σ = Wᴴ * partialTraceLeft ρ * W := by
      let f := reindexAlgEquiv ℂ ℂ (Equiv.prodComm ι κ)
      have hf_kr (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) : f (A ⊗ₖ B) = B ⊗ₖ A := by
        ext ⟨_, _⟩ ⟨_, _⟩
        exact mul_comm _ _
      have hfσ : f σ = (Wᴴ ⊗ₖ Uᴴ) * f ρ * (Wᴴ ⊗ₖ Uᴴ)ᴴ := by
        dsimp only [σ]
        rw [map_mul, map_mul, show f (Uᴴ ⊗ₖ Wᴴ)ᴴ = (f (Uᴴ ⊗ₖ Wᴴ))ᴴ from rfl, hf_kr]
      rw [← partialTraceRight_reindex_prodComm σ]
      change partialTraceRight (f σ) = _
      rw [hfσ, partialTraceRight_kronecker_conj_unitary Wᴴ hU_mem (f ρ),
        conjTranspose_conjTranspose]
      exact congrArg (fun X => Wᴴ * X * W) (partialTraceRight_reindex_prodComm ρ)
    rw [h1, show Wᴴ * partialTraceLeft ρ * W = _ from conjTranspose_eigenvectorUnitary_mul hB,
      diagonal_apply_eq, Complex.ofReal_re]
  calc
    vonNeumannEntropy ρ = vonNeumannEntropy σ :=
        (vonNeumannEntropy_conj_isometry ((mem_unitaryGroup_iff').mp hV_mem)
          hρ.posSemidef.isHermitian).symm
    _ ≤ vonNeumannEntropy (diagonal fun p : ι × κ => ((σ p p).re : ℂ)) :=
        vonNeumannEntropy_le_vonNeumannEntropy_diag hσ
    _ = entropy q := by rw [hdiag, vonNeumannEntropy_diagonal, entropy_eq_sum]
    _ ≤ entropy (q.map Prod.fst) + entropy (q.map Prod.snd) :=
        entropy_le_entropy_map_fst_add_entropy_map_snd q
    _ = vonNeumannEntropy (partialTraceRight ρ) + vonNeumannEntropy (partialTraceLeft ρ) := by
        rw [hfst, hsnd, ← vonNeumannEntropy_eq_entropy_eigenvaluePMF hρ.partialTraceRight,
          ← vonNeumannEntropy_eq_entropy_eigenvaluePMF hρ.partialTraceLeft]

/-- **Araki–Lieb triangle inequality** ([Watrous][Watrous2018], Theorem 5.25):
`S(ρ_B) - S(ρ_A) ≤ S(ρ_{AB})` for every bipartite density matrix `ρ`. -/
theorem vonNeumannEntropy_arakiLieb {ρ : Matrix (ι × κ) (ι × κ) ℂ}
    (hρ : IsDensityMatrix ρ) :
    vonNeumannEntropy (partialTraceLeft ρ) - vonNeumannEntropy (partialTraceRight ρ) ≤
      vonNeumannEntropy ρ := by
  let S := CFC.sqrt ρ
  have hS_herm : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian.eq
  have hS_sq : S * S = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg
  let e : ((ι × κ) × (ι × κ)) ≃ (κ × (ι × (ι × κ))) :=
    { toFun := fun ⟨⟨i, k⟩, r⟩ => ⟨k, ⟨i, r⟩⟩
      invFun := fun ⟨k, ⟨i, r⟩⟩ => ⟨⟨i, k⟩, r⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  let Ψ : EuclideanSpace ℂ ((ι × κ) × (ι × κ)) := WithLp.toLp 2 fun pq => S pq.1 pq.2
  let Φ : EuclideanSpace ℂ (κ × (ι × (ι × κ))) := WithLp.toLp 2 fun p => Ψ.ofLp (e.symm p)
  have hR_Ψ : partialTraceRight (pureState Ψ) = ρ := by
    rw [partialTraceRight_pureState_eq_coefficients, show coefficients Ψ = S from rfl,
      hS_herm, hS_sq]
  have hR_Φ : partialTraceRight (pureState Φ) = partialTraceLeft ρ := by
    ext k₁ k₂
    simp only [← hR_Ψ, partialTraceLeft_apply, partialTraceRight_apply, pureState_apply,
      Fintype.sum_prod_type]
    rfl
  let ω := partialTraceLeft (pureState Φ)
  have hΦ_norm : ‖Φ‖ = 1 := by
    have hsq : ‖Φ‖ ^ 2 = 1 := by
      have hcomp : (∑ p : κ × (ι × (ι × κ)), ‖Φ.ofLp p‖ ^ 2) =
          ∑ pq : (ι × κ) × (ι × κ), ‖S pq.1 pq.2‖ ^ 2 :=
        e.symm.sum_comp (fun pq => ‖S pq.1 pq.2‖ ^ 2)
      have htr : ∑ pq : (ι × κ) × (ι × κ), ‖S pq.1 pq.2‖ ^ 2 = (S * Sᴴ).trace.re := by
        rw [Fintype.sum_prod_type, Matrix.trace, Complex.re_sum]
        refine sum_congr rfl fun p _ => ?_
        rw [diag_apply, Matrix.mul_apply, Complex.re_sum]
        refine sum_congr rfl fun q _ => ?_
        rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj,
          Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      rw [EuclideanSpace.norm_sq_eq, hcomp, htr, hS_herm, hS_sq, hρ.trace_eq_one, Complex.one_re]
    nlinarith [norm_nonneg Φ]
  have hω_A : partialTraceRight ω = partialTraceRight ρ := by
    ext i₁ i₂
    simp only [ω, ← hR_Ψ, partialTraceRight_apply, partialTraceLeft_apply, pureState_apply]
    rw [Finset.sum_comm]
    rfl
  have hω_R : partialTraceLeft ω = ρᵀ := by
    ext r₁ r₂
    simp only [ω, partialTraceLeft_apply, pureState_apply, transpose_apply, ← hS_sq,
      Matrix.mul_apply, Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
    change S (i, k) r₁ * star (S (i, k) r₂) = S r₂ (i, k) * S (i, k) r₁
    have hs2 : star (S (i, k) r₂) = S r₂ (i, k) := by
      simpa only [conjTranspose_apply] using congrFun (congrFun hS_herm r₂) (i, k)
    rw [hs2, mul_comm]
  have hsub := vonNeumannEntropy_subadditivity (isDensityMatrix_pureState hΦ_norm).partialTraceLeft
  rw [hω_A, hω_R, vonNeumannEntropy_transpose hρ.posSemidef.isHermitian,
    ← vonNeumannEntropy_partialTrace_pureState_eq Φ, hR_Φ] at hsub
  linarith

end VonNeumannEntropy

/-! ### Holevo information and Holevo's bound -/

section HolevoBound

variable {X Y ι ι' κ : Type*} [Fintype ι] [DecidableEq ι]

/-- **Holevo information** `χ(p, ρ) = S(∑_x p(x) ρ_x) - ∑_x p(x) S(ρ_x)` of a finite ensemble
of states on `ℂ^ι`, in bits ([Holevo][Holevo1973]; [Nielsen and Chuang][NielsenChuang2010],
Section 12.1.1). -/
@[expose] noncomputable def holevoInformation [Fintype X] (p : PMF X) (ρ : X → Matrix ι ι ℂ) : ℝ :=
  vonNeumannEntropy (∑ x, (p x).toReal • ρ x) -
    ∑ x, (p x).toReal * vonNeumannEntropy (ρ x)

/-- Classical–quantum mutual information (in nats) equals `ln 2` times the Holevo information
(in bits). -/
theorem mutualInformation_classicalQuantumState_eq_holevoInformation [Fintype X] [DecidableEq X]
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    mutualInformation (classicalQuantumState p ρ) =
      ((Real.log 2 * holevoInformation p ρ : ℝ) : WithTop ℝ) := by
  have hlog2 : (Real.log 2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [mutualInformation_classicalQuantumState_eq_coe_sum p hρ]
  congr 1
  let μ := partialTraceRight (classicalQuantumState p ρ)
  have hμ : μ = ∑ x, (p x).toReal • ρ x := partialTraceRight_classicalQuantumState p ρ
  have hlin : (μ * cfc Real.log μ).trace.re =
      ∑ x, (p x).toReal * (ρ x * cfc Real.log μ).trace.re := by
    rw [hμ, Finset.sum_mul, trace_sum, Complex.re_sum]
    refine sum_congr rfl fun x _ => ?_
    simp only [Matrix.smul_mul, trace_smul, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsum_diff :
      ∑ x, (p x).toReal * relativeEntropyReal (ρ x) μ =
        (∑ x, (p x).toReal * (ρ x * cfc Real.log (ρ x)).trace.re) -
          (μ * cfc Real.log μ).trace.re := by
    rw [hlin, ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun x _ => ?_
    simp only [relativeEntropyReal, mul_sub, trace_sub, Complex.sub_re]
  rw [hsum_diff, holevoInformation, ← hμ, vonNeumannEntropy]
  simp only [vonNeumannEntropy]
  rw [mul_sub, mul_div_cancel₀ _ hlog2, mul_sum]
  have hterm (x : X) :
      Real.log 2 * ((p x).toReal * (-(ρ x * cfc Real.log (ρ x)).trace.re / Real.log 2)) =
        -((p x).toReal * (ρ x * cfc Real.log (ρ x)).trace.re) := by
    field_simp [hlog2]
  simp_rw [hterm, Finset.sum_neg_distrib]
  ring

private theorem log_two_mul_holevoInformation_eq_sum [Fintype X] [DecidableEq X]
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    Real.log 2 * holevoInformation p ρ =
      ∑ x, (p x).toReal *
        relativeEntropyReal (ρ x) (partialTraceRight (classicalQuantumState p ρ)) := by
  have h := mutualInformation_classicalQuantumState_eq_holevoInformation p hρ
  rw [mutualInformation_classicalQuantumState_eq_coe_sum p hρ, WithTop.coe_eq_coe] at h
  exact h.symm

/-- Holevo information is nonnegative (equivalently, von Neumann entropy is concave). -/
theorem holevoInformation_nonneg [Fintype X] (p : PMF X) {ρ : X → Matrix ι ι ℂ}
    (hρ : ∀ x, IsDensityMatrix (ρ x)) : 0 ≤ holevoInformation p ρ := by
  classical
  refine nonneg_of_mul_nonneg_right ?_ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [log_two_mul_holevoInformation_eq_sum p hρ]
  refine Finset.sum_nonneg fun x _ => ?_
  by_cases hx : x ∈ p.support
  · exact mul_nonneg ENNReal.toReal_nonneg
      (relativeEntropyReal_nonneg (hρ x)
        (isDensityMatrix_classicalQuantumState p hρ).partialTraceRight
        (supportLE_partialTraceRight_classicalQuantumState p hρ hx))
  · simp [(p.apply_eq_zero_iff x).mpr hx]

/-- Holevo information is at most the von Neumann entropy of the ensemble average. -/
theorem holevoInformation_le_vonNeumannEntropy [Fintype X] (p : PMF X) {ρ : X → Matrix ι ι ℂ}
    (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    holevoInformation p ρ ≤ vonNeumannEntropy (∑ x, (p x).toReal • ρ x) := by
  rw [holevoInformation]
  have hsum : 0 ≤ ∑ x, (p x).toReal * vonNeumannEntropy (ρ x) :=
    Finset.sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (vonNeumannEntropy_nonneg (hρ x))
  linarith

/-- Holevo information on `ℂ^ι` is at most `log₂ |ι|`. -/
theorem holevoInformation_le_logb_card [Fintype X] (p : PMF X) {ρ : X → Matrix ι ι ℂ}
    (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    holevoInformation p ρ ≤ Real.logb 2 (Fintype.card ι) := by
  classical
  have havg : IsDensityMatrix (∑ x, (p x).toReal • ρ x) := by
    rw [← partialTraceRight_classicalQuantumState p ρ]
    exact (isDensityMatrix_classicalQuantumState p hρ).partialTraceRight
  exact (holevoInformation_le_vonNeumannEntropy p hρ).trans (vonNeumannEntropy_le_logb_card havg)

/-- Holevo information is at most the Shannon entropy of the mixing weights:
`S(∑_x p(x) ρ_x) - ∑_x p(x) S(ρ_x) ≤ H(p)`. -/
theorem holevoInformation_le_entropy [Fintype X] (p : PMF X) {ρ : X → Matrix ι ι ℂ}
    (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    holevoInformation p ρ ≤ entropy p := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine le_of_mul_le_mul_left ?_ hlog2
  rw [log_two_mul_holevoInformation_eq_sum p hρ, entropy_eq_sum, mul_div_cancel₀ _ hlog2.ne']
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : x ∈ p.support
  · have hp_pos : 0 < (p x).toReal := ENNReal.toReal_pos hx (p.apply_ne_top x)
    have hw := relativeEntropy_le_neg_log_weight (fun y => (p y).toReal)
      (fun _ => ENNReal.toReal_nonneg) ρ (fun y => (hρ y).posSemidef) x hp_pos (hρ x)
    rw [← partialTraceRight_classicalQuantumState p ρ,
      relativeEntropy_of_supportLE (supportLE_partialTraceRight_classicalQuantumState p hρ hx),
      WithTop.coe_le_coe] at hw
    simpa only [Real.negMulLog, neg_mul, mul_neg] using mul_le_mul_of_nonneg_left hw hp_pos.le
  · simp [(p.apply_eq_zero_iff x).mpr hx, Real.negMulLog]

/-- **Data processing for Holevo information** ([Watrous][Watrous2018], Section 5.3, eq. (5.272)
and Theorem 5.35): applying a trace-preserving Kraus channel to every state of an ensemble cannot
increase its Holevo information. -/
theorem holevoInformation_kraus_le [Fintype X] [Fintype ι'] [DecidableEq ι']
    {α : Type*} (s : Finset α) (K : α → Matrix ι' ι ℂ) (hK : ∑ a ∈ s, (K a)ᴴ * K a = 1)
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) :
    holevoInformation p (fun x => ∑ a ∈ s, K a * ρ x * (K a)ᴴ) ≤ holevoInformation p ρ := by
  classical
  let Φ (A : Matrix ι ι ℂ) : Matrix ι' ι' ℂ := ∑ a ∈ s, K a * A * (K a)ᴴ
  have hΦ_dens (x : X) : IsDensityMatrix (Φ (ρ x)) :=
    ⟨posSemidef_sum _ fun a _ => (hρ x).posSemidef.mul_mul_conjTranspose_same (K a), by
      calc (∑ a ∈ s, K a * ρ x * (K a)ᴴ).trace
        _ = ∑ a ∈ s, ((K a)ᴴ * K a * ρ x).trace := by
            rw [trace_sum]
            exact sum_congr rfl fun a _ => by
              rw [trace_mul_comm (K a * ρ x) (K a)ᴴ, Matrix.mul_assoc]
        _ = ((∑ a ∈ s, (K a)ᴴ * K a) * ρ x).trace := by rw [← trace_sum, ← Finset.sum_mul]
        _ = 1 := by rw [hK, Matrix.one_mul, (hρ x).trace_eq_one]⟩
  have hΦ_avg : partialTraceRight (classicalQuantumState p (fun x => Φ (ρ x))) =
      Φ (partialTraceRight (classicalQuantumState p ρ)) := by
    rw [partialTraceRight_classicalQuantumState, partialTraceRight_classicalQuantumState]
    dsimp only [Φ]
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    ext i' j'
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply, Complex.real_smul,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun _ _ => ?_
    rw [Finset.sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  refine le_of_mul_le_mul_left ?_ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [log_two_mul_holevoInformation_eq_sum p hΦ_dens, log_two_mul_holevoInformation_eq_sum p hρ]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : x ∈ p.support
  · have hkraus := relativeEntropy_kraus_le s K hK (hρ x).posSemidef
      (isDensityMatrix_classicalQuantumState p hρ).partialTraceRight.posSemidef
    change relativeEntropy (Φ (ρ x)) (Φ (partialTraceRight (classicalQuantumState p ρ))) ≤ _
      at hkraus
    rw [← hΦ_avg,
      relativeEntropy_of_supportLE (supportLE_partialTraceRight_classicalQuantumState p hΦ_dens hx),
      relativeEntropy_of_supportLE (supportLE_partialTraceRight_classicalQuantumState p hρ hx),
      WithTop.coe_le_coe] at hkraus
    exact mul_le_mul_of_nonneg_left hkraus ENNReal.toReal_nonneg
  · simp [(p.apply_eq_zero_iff x).mpr hx]

/-- **Holevo's bound** ([Holevo][Holevo1973]; [Nielsen and Chuang][NielsenChuang2010],
Theorem 12.1; [Watrous][Watrous2018], Theorem 5.49): if Alice samples `x` from `p : PMF X` and
prepares the density matrix `ρ x` on `ℂ^ι`, and Bob measures with any POVM `M : POVM Y ι`, the
classical mutual information between `X` and `Y` is at most the Holevo information `χ(p, ρ)`. -/
theorem mutualInfo_measureDensity_le_holevoInformation [Fintype X] [Fintype Y]
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) (M : POVM Y ι) :
    mutualInfo (p.bind fun x => (M.measureDensity (ρ x) (hρ x)).map (x, ·)) ≤
      holevoInformation p ρ := by
  classical
  have hL_ex (y : Y) : ∃ L : Matrix ι ι ℂ, M.effect y = Lᴴ * L := by
    obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (M.posSemidef y).nonneg
    exact ⟨L, by rwa [star_eq_conjTranspose] at hL⟩
  choose L hL using hL_ex
  let K (yi : Y × ι) : Matrix Y ι ℂ := single yi.1 yi.2 (1 : ℂ) * L yi.1
  have hK : ∑ yi : Y × ι, (K yi)ᴴ * K yi = 1 := by
    rw [Fintype.sum_prod_type]
    have hinner (y : Y) : ∑ i : ι, (K (y, i))ᴴ * K (y, i) = M.effect y := by
      have hs : ∑ i : ι, (K (y, i))ᴴ * K (y, i) =
          (L y)ᴴ * (∑ i : ι, single i i (1 : ℂ)) * L y := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine sum_congr rfl fun i _ => ?_
        dsimp only [K]
        rw [conjTranspose_mul, conjTranspose_single, star_one]
        calc
          (L y)ᴴ * single i y (1 : ℂ) * (single y i (1 : ℂ) * L y)
              = (L y)ᴴ * (single i y (1 : ℂ) * single y i (1 : ℂ)) * L y := by
                simp only [Matrix.mul_assoc]
          _ = (L y)ᴴ * single i i (1 : ℂ) * L y := by rw [single_mul_single_same, mul_one]
      rw [hs, sum_single_one, Matrix.mul_one, hL y]
    simp_rw [hinner]
    exact M.sum_effect
  have hchannel (x : X) :
      ∑ yi : Y × ι, K yi * ρ x * (K yi)ᴴ =
        diagonal fun y => ((M.densityProb (ρ x) y : ℝ) : ℂ) := by
    ext y₁ y₂
    rw [Matrix.sum_apply, Fintype.sum_prod_type]
    have hK_entry (y : Y) (i : ι) :
        (K (y, i) * ρ x * (K (y, i))ᴴ) y₁ y₂ =
          if y = y₁ ∧ y = y₂ then (L y * ρ x * (L y)ᴴ) i i else 0 := by
      dsimp only [K]
      have hassoc : single y i (1 : ℂ) * L y * ρ x * (single y i (1 : ℂ) * L y)ᴴ =
          single y i (1 : ℂ) * (L y * ρ x * (L y)ᴴ) * single i y (1 : ℂ) := by
        rw [conjTranspose_mul, conjTranspose_single, star_one]
        simp only [Matrix.mul_assoc]
      rw [hassoc, Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.single_apply]
    simp_rw [hK_entry]
    by_cases hy : y₁ = y₂
    · subst hy
      rw [diagonal_apply_eq, Finset.sum_eq_single y₁ (fun _ _ h => by simp [h]) (by simp)]
      simp only [and_self, ite_true]
      have him : (L y₁ * ρ x * (L y₁)ᴴ).trace.im = 0 :=
        (Complex.nonneg_iff.mp
          ((hρ x).posSemidef.mul_mul_conjTranspose_same (L y₁)).trace_nonneg).2.symm
      have hcyc : (L y₁ * ρ x * (L y₁)ᴴ).trace = (M.effect y₁ * ρ x).trace := by
        rw [trace_mul_comm (L y₁ * ρ x) (L y₁)ᴴ, ← Matrix.mul_assoc, ← hL y₁]
      change (L y₁ * ρ x * (L y₁)ᴴ).trace = _
      apply Complex.ext
      · rw [hcyc, Complex.ofReal_re]
        rfl
      · rw [him, Complex.ofReal_im]
    · rw [diagonal_apply_ne _ hy]
      exact Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun _ _ =>
        ite_eq_right fun ⟨h1, h2⟩ => hy (h1.symm.trans h2)
  let q (x : X) : PMF Y := M.measureDensity (ρ x) (hρ x)
  let joint : PMF (X × Y) := p.bind fun x => (q x).map (x, ·)
  have hsnd : joint.map Prod.snd = p.bind q := by
    simp only [joint, PMF.map_bind, PMF.map_comp]
    exact congrArg p.bind (funext fun x => PMF.map_id (q x))
  have hq_toReal (x : X) (y : Y) : (q x y).toReal = M.densityProb (ρ x) y := by
    rw [show q x y = M.measureDensity (ρ x) (hρ x) y from rfl, POVM.measureDensity_apply,
      ENNReal.toReal_ofReal (M.densityProb_nonneg (hρ x).posSemidef y)]
  have havg_diag :
      (∑ x, (p x).toReal • diagonal fun y : Y => ((M.densityProb (ρ x) y : ℝ) : ℂ)) =
        diagonal fun y : Y => (((p.bind q) y).toReal : ℂ) := by
    ext y₁ y₂
    by_cases hy : y₁ = y₂
    · subst hy
      rw [Matrix.sum_apply, diagonal_apply_eq, PMF.bind_apply, tsum_fintype,
        ENNReal.toReal_sum
          (fun x _ => ENNReal.mul_ne_top (p.apply_ne_top x) ((q x).apply_ne_top _))]
      push_cast
      refine sum_congr rfl fun x _ => ?_
      simp [Complex.real_smul, ENNReal.toReal_mul, hq_toReal]
    · simp [hy]
  have hmut : mutualInfo joint =
      entropy (joint.map Prod.fst) + entropy (joint.map Prod.snd) - entropy joint := by
    have hid : joint.map (fun ab : X × Y => (ab.1, ab.2)) = joint := PMF.map_id joint
    simpa only [hid] using mutualInfo_map joint Prod.fst Prod.snd
  have hHolevo_out :
      holevoInformation p (fun x => ∑ yi : Y × ι, K yi * ρ x * (K yi)ᴴ) = mutualInfo joint := by
    simp_rw [hchannel]
    have hcond : (∑ x, (p x).toReal *
        vonNeumannEntropy (diagonal fun y : Y => ((M.densityProb (ρ x) y : ℝ) : ℂ))) =
          ∑ x, (p x).toReal * entropy (q x) :=
      sum_congr rfl fun x _ => by
        rw [vonNeumannEntropy_diagonal, entropy_eq_sum]
        simp_rw [hq_toReal x]
    rw [holevoInformation, havg_diag, vonNeumannEntropy_diagonal, ← entropy_eq_sum,
      hcond, hmut, map_fst_bind_pair, hsnd, entropy_bind_pair]
    ring
  rw [← hHolevo_out]
  exact holevoInformation_kraus_le Finset.univ K hK p hρ

/-- **Unassisted quantum communication bound** ([Watrous][Watrous2018], Corollary 5.50;
[de Wolf][deWolf2019], Chapter 15, Theorem 3, part 1): without prior entanglement, sending a state
on `ℂ^ι` conveys at most `log₂ |ι|` bits of mutual information for any POVM readout. -/
theorem mutualInfo_measureDensity_le_logb_card [Finite X] [Fintype Y]
    (p : PMF X) {ρ : X → Matrix ι ι ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x)) (M : POVM Y ι) :
    mutualInfo (p.bind fun x => (M.measureDensity (ρ x) (hρ x)).map (x, ·)) ≤
      Real.logb 2 (Fintype.card ι) := by
  let := Fintype.ofFinite X
  exact (mutualInfo_measureDensity_le_holevoInformation p hρ M).trans
    (holevoInformation_le_logb_card p hρ)

/-- **Unassisted `n`-qubit transmission bound** ([de Wolf][deWolf2019], Chapter 15, Theorem 3,
part 1): sending `n = |α|` qubits without prior entanglement conveys at most `n` classical bits of
mutual information under any POVM measurement. -/
theorem mutualInfo_measureDensity_qubits_le {α : Type*} [Fintype α] [DecidableEq α]
    [Finite X] [Fintype Y] (p : PMF X)
    {ρ : X → Matrix (α → Bool) (α → Bool) ℂ} (hρ : ∀ x, IsDensityMatrix (ρ x))
    (M : POVM Y (α → Bool)) :
    mutualInfo (p.bind fun x => (M.measureDensity (ρ x) (hρ x)).map (x, ·)) ≤ Fintype.card α := by
  refine (mutualInfo_measureDensity_le_logb_card p hρ M).trans_eq ?_
  rw [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb, div_self (Real.log_pos (by norm_num)).ne', mul_one]

/-! ### Entanglement-assisted quantum communication and superdense-coding optimality -/

omit [DecidableEq ι] in
/-- Applying a trace-preserving Kraus operation to the first factor of a joint density matrix
produces a joint density matrix. -/
theorem isDensityMatrix_kraus_onFirst {ι₀ : Type*} [Fintype ι₀] [DecidableEq ι₀]
    [Fintype κ] [DecidableEq κ] {β : Type*} (s : Finset β) (K : β → Matrix ι ι₀ ℂ)
    (hK : ∑ j ∈ s, (K j)ᴴ * K j = 1) {σ : Matrix (ι₀ × κ) (ι₀ × κ) ℂ}
    (hσ : IsDensityMatrix σ) :
    IsDensityMatrix
      (∑ j ∈ s, (K j ⊗ₖ (1 : Matrix κ κ ℂ)) * σ * (K j ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) := by
  constructor
  · exact posSemidef_sum _ fun j _ =>
      hσ.posSemidef.mul_mul_conjTranspose_same (K j ⊗ₖ (1 : Matrix κ κ ℂ))
  · rw [← trace_partialTraceLeft, partialTraceLeft_kraus s K hK σ, trace_partialTraceLeft,
      hσ.trace_eq_one]

/-- **Entanglement-assisted Holevo bound** ([de Wolf][deWolf2019], Chapter 15, Theorem 3, part 2):
if Alice and Bob share any bipartite state `σ` on `ℂ^{ι₀ × κ}` and Alice encodes `x` by applying a
trace-preserving Kraus channel `K x` from `ℂ^{ι₀}` to `ℂ^ι` on her share, the resulting joint
ensemble on `ℂ^{ι × κ}` has Holevo information at most `2 log₂ |ι|`, independent of `ι₀` and `κ`. -/
theorem holevoInformation_kraus_onFirst_le {ι₀ : Type*} [Fintype ι₀] [DecidableEq ι₀]
    [Fintype κ] [DecidableEq κ] [Fintype X] {β : Type*} (s : Finset β)
    (K : X → β → Matrix ι ι₀ ℂ) (hK : ∀ x, ∑ j ∈ s, (K x j)ᴴ * K x j = 1)
    (p : PMF X) {σ : Matrix (ι₀ × κ) (ι₀ × κ) ℂ} (hσ : IsDensityMatrix σ) :
    holevoInformation p
      (fun x => ∑ j ∈ s, (K x j ⊗ₖ (1 : Matrix κ κ ℂ)) * σ * (K x j ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) ≤
      2 * Real.logb 2 (Fintype.card ι) := by
  classical
  let τ (x : X) : Matrix (ι × κ) (ι × κ) ℂ :=
    ∑ j ∈ s, (K x j ⊗ₖ (1 : Matrix κ κ ℂ)) * σ * (K x j ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ
  have hτ (x : X) : IsDensityMatrix (τ x) := isDensityMatrix_kraus_onFirst s (K x) (hK x) hσ
  have hτ_B (x : X) : partialTraceLeft (τ x) = partialTraceLeft σ :=
    partialTraceLeft_kraus s (K x) (hK x) σ
  let bar_τ := ∑ x, (p x).toReal • τ x
  have hbar : IsDensityMatrix bar_τ := by
    rw [show bar_τ = partialTraceRight (classicalQuantumState p τ) from
      (partialTraceRight_classicalQuantumState p τ).symm]
    exact (isDensityMatrix_classicalQuantumState p hτ).partialTraceRight
  have hbar_B : partialTraceLeft bar_τ = partialTraceLeft σ := by
    ext k₁ k₂
    simp only [bar_τ, partialTraceLeft_apply, Matrix.sum_apply, Matrix.smul_apply,
      Complex.real_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← partialTraceLeft_apply, hτ_B, ← Finset.sum_mul]
    have hsum : (∑ x : X, ((p x).toReal : ℂ)) = 1 := by exact_mod_cast sum_toReal p
    rw [hsum, one_mul]
  have hupper : vonNeumannEntropy bar_τ ≤
      Real.logb 2 (Fintype.card ι) + vonNeumannEntropy (partialTraceLeft σ) := by
    have hsub := vonNeumannEntropy_subadditivity hbar
    rw [hbar_B] at hsub
    linarith [vonNeumannEntropy_le_logb_card hbar.partialTraceRight]
  have hlower_each (x : X) :
      vonNeumannEntropy (partialTraceLeft σ) - Real.logb 2 (Fintype.card ι) ≤
        vonNeumannEntropy (τ x) := by
    have hal := vonNeumannEntropy_arakiLieb (hτ x)
    rw [hτ_B x] at hal
    linarith [vonNeumannEntropy_le_logb_card (hτ x).partialTraceRight]
  have hlower_avg :
      vonNeumannEntropy (partialTraceLeft σ) - Real.logb 2 (Fintype.card ι) ≤
        ∑ x, (p x).toReal * vonNeumannEntropy (τ x) := by
    calc
      vonNeumannEntropy (partialTraceLeft σ) - Real.logb 2 (Fintype.card ι)
          = (∑ x : X, (p x).toReal) *
              (vonNeumannEntropy (partialTraceLeft σ) - Real.logb 2 (Fintype.card ι)) := by
            rw [sum_toReal p, one_mul]
      _ = ∑ x : X, (p x).toReal *
            (vonNeumannEntropy (partialTraceLeft σ) - Real.logb 2 (Fintype.card ι)) := by
            rw [Finset.sum_mul]
      _ ≤ ∑ x : X, (p x).toReal * vonNeumannEntropy (τ x) :=
            Finset.sum_le_sum fun x _ =>
              mul_le_mul_of_nonneg_left (hlower_each x) ENNReal.toReal_nonneg
  change vonNeumannEntropy bar_τ - ∑ x, (p x).toReal * vonNeumannEntropy (τ x) ≤ _
  linarith

/-- **Entanglement-assisted classical communication cap** ([de Wolf][deWolf2019], Chapter 15,
Theorem 3, part 2): even with an arbitrary shared bipartite state `σ` on `ℂ^{ι₀ × κ}` and arbitrary
local Kraus encoding `K x` into a register `ℂ^ι` sent to Bob, any joint POVM `M` on `ℂ^{ι × κ}`
extracts at most `2 log₂ |ι|` bits of classical mutual information. -/
theorem mutualInfo_entanglementAssisted_le {ι₀ : Type*} [Fintype ι₀] [DecidableEq ι₀]
    [Fintype κ] [DecidableEq κ] [Finite X] [Fintype Y] {β : Type*} (s : Finset β)
    (K : X → β → Matrix ι ι₀ ℂ) (hK : ∀ x, ∑ j ∈ s, (K x j)ᴴ * K x j = 1)
    (p : PMF X) {σ : Matrix (ι₀ × κ) (ι₀ × κ) ℂ} (hσ : IsDensityMatrix σ)
    (M : POVM Y (ι × κ)) :
    mutualInfo (p.bind fun x =>
      (M.measureDensity
        (∑ j ∈ s, (K x j ⊗ₖ (1 : Matrix κ κ ℂ)) * σ * (K x j ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ)
        (isDensityMatrix_kraus_onFirst s (K x) (hK x) hσ)).map (x, ·)) ≤
      2 * Real.logb 2 (Fintype.card ι) := by
  let := Fintype.ofFinite X
  exact (mutualInfo_measureDensity_le_holevoInformation p
    (fun x => isDensityMatrix_kraus_onFirst s (K x) (hK x) hσ) M).trans
    (holevoInformation_kraus_onFirst_le s K hK p hσ)

/-- **Optimality of superdense coding for `n` qubits** ([de Wolf][deWolf2019], Chapter 15,
Theorem 3, part 2): sending `n = |α|` qubits with arbitrary prior entanglement and local Kraus
encoding conveys at most `2n` classical bits of mutual information. -/
theorem mutualInfo_entanglementAssisted_qubits_le {α ι₀ : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι₀] [DecidableEq ι₀] [Fintype κ] [DecidableEq κ] [Finite X] [Fintype Y]
    {β : Type*} (s : Finset β) (K : X → β → Matrix (α → Bool) ι₀ ℂ)
    (hK : ∀ x, ∑ j ∈ s, (K x j)ᴴ * K x j = 1) (p : PMF X)
    {σ : Matrix (ι₀ × κ) (ι₀ × κ) ℂ} (hσ : IsDensityMatrix σ)
    (M : POVM Y ((α → Bool) × κ)) :
    mutualInfo (p.bind fun x =>
      (M.measureDensity
        (∑ j ∈ s, (K x j ⊗ₖ (1 : Matrix κ κ ℂ)) * σ * (K x j ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ)
        (isDensityMatrix_kraus_onFirst s (K x) (hK x) hσ)).map (x, ·)) ≤
      2 * (Fintype.card α : ℝ) := by
  refine (mutualInfo_entanglementAssisted_le s K hK p hσ M).trans_eq ?_
  rw [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
    Real.logb, div_self (Real.log_pos (by norm_num)).ne', mul_one]

/-- **Local-unitary entanglement-assisted communication cap**: when Alice encodes `x` by applying a
local unitary `U x` to her `ℂ^ι` share of `σ` and sends that share to Bob, Bob's joint POVM on
`ℂ^{ι × κ}` yields at most `2 log₂ |ι|` bits of mutual information (`2` bits for a single qubit
`ι = Bool`, matching `Cslib.Quantum.superdense_coding`). -/
theorem mutualInfo_unitary_onFirst_le [Fintype κ] [DecidableEq κ] [Finite X] [Fintype Y]
    (U : X → unitaryGroup ι ℂ) (p : PMF X) {σ : Matrix (ι × κ) (ι × κ) ℂ}
    (hσ : IsDensityMatrix σ) (M : POVM Y (ι × κ)) :
    mutualInfo (p.bind fun x =>
      (M.measureDensity
        (((U x : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix κ κ ℂ)) * σ *
          ((U x : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ)
        (hσ.conj_unitary (kronecker_mem_unitary (U x).2 (one_mem _)))).map (x, ·)) ≤
      2 * Real.logb 2 (Fintype.card ι) := by
  have hK (x : X) :
      ∑ _j ∈ ({()} : Finset Unit), ((U x : Matrix ι ι ℂ))ᴴ * (U x : Matrix ι ι ℂ) = 1 := by
    rw [Finset.sum_singleton]
    exact (mem_unitaryGroup_iff').mp (U x).2
  have h := mutualInfo_entanglementAssisted_le ({()} : Finset Unit)
    (fun x _ => (U x : Matrix ι ι ℂ)) hK p hσ M
  simpa only [Finset.sum_singleton] using h

end HolevoBound

end Cslib.Quantum
