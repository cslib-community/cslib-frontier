/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Schmidt
public import Mathlib.LinearAlgebra.UnitaryGroup
import CslibFrontier.Foundations.Analysis.InnerProductSpace.PiL2
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Polar
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Schmidt coordinates for arbitrary finite strategies

Local unitary basis changes preserve all joint probabilities. A rectangular singular value
decomposition puts any strategy state into paired Schmidt coordinates in the original two
dimensions. The support of the nonzero coefficients embeds into both coordinate bases.
-/

public section

open Matrix Finset Cslib.Quantum
open scoped Kronecker MatrixOrder ComplexOrder

namespace Cslib.PCP.QuantumStrategy

variable {X Y A B ι κ : Type*} [Fintype A] [Fintype B]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Exchange the two local systems and their measurements. -/
noncomputable def swap (S : QuantumStrategy X Y A B ι κ) : QuantumStrategy Y X B A κ ι where
  state := WithLp.toLp 2 (S.state.ofLp ∘ Equiv.prodComm κ ι)
  norm_state := by
    rw [EuclideanSpace.norm_eq, ← S.norm_state, EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp (Equiv.prodComm κ ι) fun p => ‖S.state p‖ ^ 2
  alice := S.bob
  bob := S.alice

@[simp] theorem swap_alice (S : QuantumStrategy X Y A B ι κ) : S.swap.alice = S.bob := by
  unfold swap
  rfl

@[simp] theorem prob_swap (S : QuantumStrategy X Y A B ι κ) (x : X) (y : Y) (a : A) (b : B) :
    S.swap.prob y x b a = S.prob x y a b := by
  rw [prob_eq, prob_eq]
  unfold swap
  let e := Equiv.prodComm ι κ
  let E := (S.alice x).effect a ⊗ₖ (S.bob y).effect b
  have hE : (S.bob y).effect b ⊗ₖ (S.alice x).effect a = E.submatrix e.symm e.symm := by
    ext ⟨i, k⟩ ⟨j, l⟩
    change (S.bob y).effect b i j * (S.alice x).effect a k l =
      (S.alice x).effect a k l * (S.bob y).effect b i j
    exact mul_comm _ _
  change (star (S.state.ofLp ∘ e.symm) ⬝ᵥ
    (((S.bob y).effect b ⊗ₖ (S.alice x).effect a) *ᵥ (S.state.ofLp ∘ e.symm))).re = _
  rw [hE, star_dotProduct_submatrix_mulVec e]

@[simp] theorem partialTraceRight_pureState_swap (S : QuantumStrategy X Y A B ι κ) :
    partialTraceRight (pureState S.swap.state) = partialTraceLeft (pureState S.state) := by
  ext i j
  rw [partialTraceRight_apply, partialTraceLeft_apply]
  exact sum_congr rfl fun k _ => by
    simp only [pureState_apply, swap]
    rfl

/-- Express a strategy in the local orthonormal bases given by the columns of two unitaries. -/
noncomputable def changeBasis (S : QuantumStrategy X Y A B ι κ)
    (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hV : V ∈ unitaryGroup κ ℂ) :
    QuantumStrategy X Y A B ι κ where
  state := WithLp.toLp 2 ((U ⊗ₖ V)ᴴ *ᵥ S.state.ofLp)
  norm_state := by
    have h := mem_unitaryGroup_iff.mp (kronecker_mem_unitary hU hV)
    rw [star_eq_conjTranspose] at h
    rw [norm_toLp_mulVec_of_conjTranspose_mul_self (by
      rw [conjTranspose_conjTranspose]
      exact h), S.norm_state]
  alice x := (S.alice x).comap U hU
  bob y := (S.bob y).comap V hV

@[simp] theorem changeBasis_state_apply (S : QuantumStrategy X Y A B ι κ)
    (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hV : V ∈ unitaryGroup κ ℂ) (i : ι) (k : κ) :
    (S.changeBasis U V hU hV).state.ofLp (i, k) =
      ((U ⊗ₖ V)ᴴ *ᵥ S.state.ofLp) (i, k) := by
  unfold changeBasis
  rfl

@[simp] theorem changeBasis_alice_effect (S : QuantumStrategy X Y A B ι κ)
    (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hV : V ∈ unitaryGroup κ ℂ) (x : X) (a : A) :
    ((S.changeBasis U V hU hV).alice x).effect a = Uᴴ * (S.alice x).effect a * U := by
  unfold changeBasis
  rfl

/-- Local changes of basis preserve the strategy probabilities. -/
@[simp] theorem prob_changeBasis (S : QuantumStrategy X Y A B ι κ)
    (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hV : V ∈ unitaryGroup κ ℂ)
    (x : X) (y : Y) (a : A) (b : B) :
    (S.changeBasis U V hU hV).prob x y a b = S.prob x y a b := by
  let W := U ⊗ₖ V
  let E := (S.alice x).effect a ⊗ₖ (S.bob y).effect b
  have hWW : W * Wᴴ = 1 := by
    rw [← star_eq_conjTranspose]
    exact mem_unitaryGroup_iff.mp (kronecker_mem_unitary hU hV)
  rw [prob_eq, prob_eq]
  unfold changeBasis
  change (star (Wᴴ *ᵥ S.state.ofLp) ⬝ᵥ
      (((Uᴴ * (S.alice x).effect a * U) ⊗ₖ (Vᴴ * (S.bob y).effect b * V)) *ᵥ
        (Wᴴ *ᵥ S.state.ofLp))).re =
    (star S.state.ofLp ⬝ᵥ (E *ᵥ S.state.ofLp)).re
  rw [mul_kronecker_mul, mul_kronecker_mul, ← conjTranspose_kronecker]
  change (star (Wᴴ *ᵥ S.state.ofLp) ⬝ᵥ
      ((Wᴴ * E * W) *ᵥ (Wᴴ *ᵥ S.state.ofLp))).re = _
  rw [mulVec_mulVec, Matrix.mul_assoc (Wᴴ * E), hWW, Matrix.mul_one,
    ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose,
    vecMul_vecMul, hWW, vecMul_one]

private def stateMatrix (ψ : EuclideanSpace ℂ (ι × κ)) : Matrix κ ι ℂ :=
  fun k i => ψ.ofLp (i, k)

private theorem stateMatrix_changeBasis (S : QuantumStrategy X Y A B ι κ)
    (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hV : V ∈ unitaryGroup κ ℂ) :
    stateMatrix (S.changeBasis U V hU hV).state = Vᴴ * stateMatrix S.state * Uᴴᵀ := by
  ext k i
  unfold stateMatrix
  rw [changeBasis_state_apply, conjTranspose_kronecker]
  change (((Uᴴ ⊗ₖ Vᴴ) *ᵥ vec (stateMatrix S.state)) (i, k)) = _
  rw [kronecker_mulVec_vec]
  rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
private theorem partialTraceRight_eq_stateMatrix_gram (ψ : EuclideanSpace ℂ (ι × κ)) :
    partialTraceRight (pureState ψ) = ((stateMatrix ψ)ᴴ * stateMatrix ψ)ᵀ := by
  ext i j
  rw [partialTraceRight_apply, transpose_apply, Matrix.mul_apply]
  simp only [pureState_apply, conjTranspose_apply, stateMatrix]
  exact sum_congr rfl fun k _ => mul_comm _ _

/-- The reduced state on Alice's side changes by conjugation by her local basis unitary. -/
theorem partialTraceRight_pureState_changeBasis (S : QuantumStrategy X Y A B ι κ)
    (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hV : V ∈ unitaryGroup κ ℂ) :
    partialTraceRight (pureState (S.changeBasis U V hU hV).state) =
      Uᴴ * partialTraceRight (pureState S.state) * U := by
  have hV' : V * Vᴴ = 1 := by
    rw [← star_eq_conjTranspose]
    exact mem_unitaryGroup_iff.mp hV
  rw [partialTraceRight_eq_stateMatrix_gram, stateMatrix_changeBasis,
    partialTraceRight_eq_stateMatrix_gram]
  let Y := stateMatrix S.state
  have hgram : (Vᴴ * Y * Uᴴᵀ)ᴴ * (Vᴴ * Y * Uᴴᵀ) = (Uᴴᵀ)ᴴ * (Yᴴ * Y) * Uᴴᵀ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V Vᴴ, hV', Matrix.one_mul]
  change ((Vᴴ * Y * Uᴴᵀ)ᴴ * (Vᴴ * Y * Uᴴᵀ))ᵀ = _
  rw [hgram]
  simp only [transpose_mul, transpose_transpose, conjTranspose_transpose_eq_transpose_conjTranspose,
    conjTranspose_conjTranspose, Matrix.mul_assoc, Y]

/-- A local change of basis puts the state in paired Schmidt coordinates. The nonzero
coefficients are indexed by their positions on Alice's side and matched into Bob's basis
by an injection. -/
theorem exists_changeBasis_schmidt (S : QuantumStrategy X Y A B ι κ) :
    ∃ (d : ι → ℝ) (e : {i : ι // d i ≠ 0} ↪ κ)
      (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
      (hU : U ∈ unitaryGroup ι ℂ) (hV : V ∈ unitaryGroup κ ℂ),
      (∀ i, 0 ≤ d i) ∧ (∑ i, d i) = 1 ∧
      ∀ i k, (S.changeBasis U V hU hV).state.ofLp (i, k) =
        if hi : d i ≠ 0 then if k = e ⟨i, hi⟩ then (Real.sqrt (d i) : ℂ) else 0 else 0 := by
  classical
  let Y := stateMatrix S.state
  obtain ⟨d, e, L, R, hd, hL, hR, hY⟩ := exists_singular_value_decomposition Y
  let U := Rᴴᵀ
  have hU : U ∈ unitaryGroup ι ℂ := by
    apply mem_unitaryGroup_iff.mpr
    have hr : R * Rᴴ = 1 := by
      rw [← star_eq_conjTranspose]
      exact mem_unitaryGroup_iff.mp hR
    simp only [U, star_eq_conjTranspose, conjTranspose_transpose_eq_transpose_conjTranspose,
      conjTranspose_conjTranspose, ← transpose_mul, hr, transpose_one]
  have hshape (i : ι) (k : κ) :
      (S.changeBasis U L hU hL).state.ofLp (i, k) =
        if hi : d i ≠ 0 then if k = e ⟨i, hi⟩ then (Real.sqrt (d i) : ℂ) else 0 else 0 := by
    rw [changeBasis_state_apply, conjTranspose_kronecker]
    change (((Uᴴ ⊗ₖ Lᴴ) *ᵥ vec Y) (i, k)) = _
    rw [kronecker_mulVec_vec]
    have hR' : Uᴴᵀ = R := by
      simp only [U, conjTranspose_transpose_eq_transpose_conjTranspose,
        conjTranspose_conjTranspose, transpose_transpose]
    rw [hR']
    exact hY k i
  refine ⟨d, e, U, L, hU, hL, hd, ?_, hshape⟩
  have hn := (S.changeBasis U L hU hL).norm_state
  have hs := congrArg (fun r : ℝ => r ^ 2) hn
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, one_pow] at hs
  refine Eq.trans ?_ hs
  refine sum_congr rfl fun i _ => ?_
  simp_rw [hshape]
  by_cases hi : d i ≠ 0
  · simp only [dite_eq_left hi]
    rw [sum_eq_single (e ⟨i, hi⟩)]
    · simp [Real.sq_sqrt (hd i)]
    · intro k _ hk
      simp [hk]
    · simp
  · simp [not_not.mp hi]

omit [DecidableEq ι] in
private theorem sum_paired_schmidt {ψ : ι × κ → ℂ} (d : ι → ℝ)
    (e : {i : ι // d i ≠ 0} ↪ κ)
    (hψ : ∀ i k, ψ (i, k) =
      if hi : d i ≠ 0 then if k = e ⟨i, hi⟩ then (Real.sqrt (d i) : ℂ) else 0 else 0)
    (f : ι × κ → ℂ) :
    (∑ p, ψ p * f p) = ∑ i : {i : ι // d i ≠ 0}, (Real.sqrt (d i.val) : ℂ) * f (i.val, e i) := by
  classical
  rw [Fintype.sum_prod_type]
  rw [← sum_filter_add_sum_filter_not univ (fun i => d i ≠ 0)]
  have hzero : (∑ i ∈ univ.filter (fun i => ¬d i ≠ 0), ∑ k, ψ (i, k) * f (i, k)) = 0 := by
    apply sum_eq_zero
    intro i hi
    have hz := (mem_filter.mp hi).2
    simp [hψ, hz]
  rw [hzero, add_zero]
  rw [Finset.sum_subtype (p := fun i => d i ≠ 0) (univ.filter _) (by simp)]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_eq_single (e i)]
  · simp [hψ, i.property]
  · intro k _ hk
    simp [hψ, i.property, hk]
  · simp

/-- The probability formula in paired Schmidt coordinates keeps only the nonzero coefficients. -/
theorem prob_eq_sum_paired_schmidt (S : QuantumStrategy X Y A B ι κ) (d : ι → ℝ)
    (e : {i : ι // d i ≠ 0} ↪ κ)
    (hψ : ∀ i k, S.state.ofLp (i, k) =
      if hi : d i ≠ 0 then if k = e ⟨i, hi⟩ then (Real.sqrt (d i) : ℂ) else 0 else 0)
    (x : X) (y : Y) (a : A) (b : B) :
    S.prob x y a b =
      ∑ i : {i : ι // d i ≠ 0}, ∑ j : {j : ι // d j ≠ 0},
        (Real.sqrt (d i.val) * Real.sqrt (d j.val)) *
          (((S.alice x).effect a i.val j.val) * ((S.bob y).effect b (e i) (e j))).re := by
  have hs : star S.state.ofLp = S.state.ofLp := by
    funext p
    rcases p with ⟨i, k⟩
    rw [Pi.star_apply, hψ]
    by_cases hi : d i ≠ 0
    · by_cases hk : k = e ⟨i, hi⟩ <;> simp [hi, hk]
    · simp [hi]
  rw [prob_eq, hs, dotProduct, sum_paired_schmidt d e hψ, Complex.re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_apply_eq_sum]
  have he :
      (∑ p, ((S.alice x).effect a ⊗ₖ (S.bob y).effect b) (i.val, e i) p * S.state.ofLp p) =
        ∑ j : {j : ι // d j ≠ 0}, (Real.sqrt (d j.val) : ℂ) *
          ((S.alice x).effect a ⊗ₖ (S.bob y).effect b) (i.val, e i) (j.val, e j) := by
    rw [show (∑ p, ((S.alice x).effect a ⊗ₖ (S.bob y).effect b) (i.val, e i) p * S.state.ofLp p) =
        ∑ p, S.state.ofLp p * ((S.alice x).effect a ⊗ₖ (S.bob y).effect b) (i.val, e i) p by
      exact sum_congr rfl fun p _ => mul_comm _ _]
    exact sum_paired_schmidt d e hψ _
  rw [he, mul_sum, Complex.re_sum]
  refine sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re]
  ring

omit [Fintype ι] in
/-- The reduced density on the first factor has the squared Schmidt coefficients on its diagonal. -/
theorem partialTraceRight_pureState_of_paired_schmidt (ψ : EuclideanSpace ℂ (ι × κ))
    (d : ι → ℝ) (e : {i : ι // d i ≠ 0} ↪ κ) (hd : ∀ i, 0 ≤ d i)
    (hψ : ∀ i k, ψ.ofLp (i, k) =
      if hi : d i ≠ 0 then if k = e ⟨i, hi⟩ then (Real.sqrt (d i) : ℂ) else 0 else 0) :
    partialTraceRight (pureState ψ) = diagonal (fun i => (d i : ℂ)) := by
  ext i j
  simp only [partialTraceRight_apply, pureState_apply]
  by_cases hi : d i ≠ 0
  · rw [sum_eq_single (e ⟨i, hi⟩)]
    · by_cases hij : i = j
      · subst j
        simp [hψ, hi, ← Complex.ofReal_mul, Real.mul_self_sqrt (hd i)]
      · by_cases hj : d j ≠ 0
        · have he : e ⟨i, hi⟩ ≠ e ⟨j, hj⟩ := fun h =>
            hij (congrArg Subtype.val (e.injective h))
          simp [hψ, hi, hj, he, diagonal_apply_ne _ hij]
        · simp [hψ, hi, hj, diagonal_apply_ne _ hij]
    · intro k _ hk
      simp [hψ, hi, hk]
    · simp
  · simp [hψ, not_not.mp hi, diagonal_apply]

end Cslib.PCP.QuantumStrategy
