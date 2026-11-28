/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Forster
public import CslibFrontier.Foundations.BooleanAnalysis.QuadraticForm
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.CutRank
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Foundations.Data.Set.Card
import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Spectral, Frobenius, and sign-rank bounds for quadratic forms over `𝔽₂`

For a quadratic form `BitString.quadForm Q` over `𝔽₂` and a coordinate cut `X : Set ι`, writing each
input via `Equiv.piEquivPiSubtypeProd` across `(X, Xᶜ)` decomposes `Q(x)` into diagonal terms on `X`
and `Xᶜ` plus the bilinear cross-term `(Q + Qᵀ)[X, Xᶜ]` of rank `(Q + Qᵀ).cutRank X`.

1. **Bilinear spectral bound** (`abs_sum_mul_signMatrix_quadForm_le`): Cauchy–Schwarz and Walsh
   orthogonality along the kernel of `(Q + Qᵀ)[X, Xᶜ]` bound the bilinear form of the `±1` sign
   matrix `M` by `√(2 ^ |ι| / 2 ^ (Q + Qᵀ).cutRank X) · ‖p‖₂ · ‖q‖₂`.
2. **Sign-rank lower bound** (`two_pow_cutRank_le_signRank_quadForm_sq`): combining the spectral
   bound with Forster's theorem (`mul_sqrt_card_mul_card_le_mul_signRank`) yields
   `2 ^ (Q + Qᵀ).cutRank X ≤ signRank(Q_{X, Xᶜ})²`.
3. **Low-rank Frobenius inner-product bound** (`sq_sum_mul_signMatrix_quadForm_le_card_of_mul`):
   expanding the columns of any real factorization `U_mat * V_mat` through `κ` in an orthonormal
   basis of `LinearMap.range (Matrix.toEuclideanLin U_mat)` gives
   `(∑_{a, b} M_{a, b} (U_mat * V_mat)_{a, b})² · 2 ^ (Q + Qᵀ).cutRank X ≤
     |κ| · 2 ^ |ι| · ∑_{a, b} (U_mat * V_mat)_{a, b}²`,
   without requiring separate norm bounds on `U_mat` and `V_mat`.

## Main results

* `Cslib.Communication.abs_sum_mul_signMatrix_quadForm_le`: spectral bilinear bound for quadratic
  form sign matrices across `(X, Xᶜ)`.
* `Cslib.Communication.two_pow_cutRank_le_signRank_quadForm_sq`: Forster sign-rank lower bound from
  polar cut rank.
* `Cslib.Communication.sq_sum_mul_signMatrix_quadForm_le_card_of_mul`: low-rank Frobenius inner
  product bound against quadratic form sign matrices.

## References

* [J. Forster, *A linear lower bound on the unbounded error probabilistic communication
  complexity*][Forster2002]
* [S. Jukna, *Extremal Combinatorics*, Ch. 14][Jukna2011]
* [A. A. Sherstov, P. Wu, *Near-Optimal Lower Bounds on the Threshold Degree and Sign-Rank of
  AC⁰*, Theorem A.2][SherstovWu2019]
-/

public section

namespace Cslib.Communication

open Set Matrix
open scoped Finset

private theorem card_add_card_compl {ι : Type*} [Fintype ι] (X : Set ι) [Fintype X]
    [Fintype ↥Xᶜ] : Fintype.card X + Fintype.card ↥Xᶜ = Fintype.card ι := by
  simp only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  exact ncard_add_ncard_compl X

open Classical in
/-- **Bilinear operator-norm bound for quadratic-form sign matrices.** Across any coordinate cut
`X : Set ι`, the `±1` sign matrix `M` of `BitString.quadForm Q` satisfies
`|∑ a, ∑ b, p_vec a * M a b * q_vec b| ≤
  √(2 ^ |ι| / 2 ^ (Q + Qᵀ).cutRank X) * ‖p_vec‖₂ * ‖q_vec‖₂`. -/
theorem abs_sum_mul_signMatrix_quadForm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι (ZMod 2)) (X : Set ι)
    (p_vec : (X → Bool) → ℝ) (q_vec : (↥Xᶜ → Bool) → ℝ) :
    |∑ a, ∑ b, p_vec a *
        signMatrix ℝ (fun a' b' =>
          BitString.quadForm Q ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (a', b')))
          a b * q_vec b| ≤
      √((2 : ℝ) ^ Fintype.card ι / (2 : ℝ) ^ (Q + Qᵀ).cutRank X) *
        √(∑ a, p_vec a ^ 2) * √(∑ b, q_vec b ^ 2) := by
  let glue := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  let f : (X → Bool) → (↥Xᶜ → Bool) → Bool := fun a b => BitString.quadForm Q (glue (a, b))
  set M := signMatrix ℝ f
  let eX : (X → Bool) ≃ (X → ZMod 2) := (BitString.toZModSpace X).toEquiv
  let eY : (↥Xᶜ → Bool) ≃ (↥Xᶜ → ZMod 2) := (BitString.toZModSpace ↥Xᶜ).toEquiv
  let C := (Q + Qᵀ).submatrix ((↑) : X → ι) ((↑) : ↥Xᶜ → ι)
  let g : (X → ZMod 2) → ℝ := fun u =>
    (-1) ^ (u ⬝ᵥ Q.submatrix ((↑) : X → ι) ((↑) : X → ι) *ᵥ u).val
  let h : (↥Xᶜ → ZMod 2) → ℝ := fun w =>
    (-1) ^ (w ⬝ᵥ Q.submatrix ((↑) : ↥Xᶜ → ι) ((↑) : ↥Xᶜ → ι) *ᵥ w).val
  have hM_entry (a : X → Bool) (b : ↥Xᶜ → Bool) :
      M a b = g (eX a) * h (eY b) * (-1) ^ (eX a ⬝ᵥ C *ᵥ eY b).val := by
    have hS : M a b = (-1 : ℝ) ^ ((fun i => BitString.bitVal (ZMod 2) (glue (a, b) i)) ⬝ᵥ
        Q *ᵥ fun i => BitString.bitVal (ZMod 2) (glue (a, b) i)).val :=
      (BitString.neg_one_pow_val_eq Q (glue (a, b))).symm
    have hq := Matrix.dotProduct_mulVec_self_eq_add Q X
      fun i => BitString.bitVal (ZMod 2) (glue (a, b) i)
    have ha_sub : (X.domRestrict fun i => BitString.bitVal (ZMod 2) (glue (a, b) i)) = eX a := by
      ext i
      simp only [glue, Equiv.piEquivPiSubtypeProd_symm_apply, domRestrict_apply, Subtype.coe_prop,
        ↓reduceDIte, Subtype.coe_eta]
      exact (BitString.bitEquiv_symm_apply _).symm
    have hb_sub : (Xᶜ.domRestrict fun i => BitString.bitVal (ZMod 2) (glue (a, b) i)) = eY b := by
      ext j
      simp only [glue, Equiv.piEquivPiSubtypeProd_symm_apply, domRestrict_apply,
        notMem_of_mem_compl j.2, ↓reduceDIte, Subtype.coe_eta]
      exact (BitString.bitEquiv_symm_apply _).symm
    rw [hS, hq, ZMod.neg_one_pow_val_add, ZMod.neg_one_pow_val_add, ha_sub, hb_sub]
  set kerCard := #{z : ↥Xᶜ → ZMod 2 | C *ᵥ z = 0}
  have hker_eq : (kerCard : ℝ) * (2 : ℝ) ^ Fintype.card X =
      (2 : ℝ) ^ Fintype.card ι / (2 : ℝ) ^ (Q + Qᵀ).cutRank X := by
    have h1 : (kerCard : ℝ) * (2 : ℝ) ^ (Q + Qᵀ).cutRank X = (2 : ℝ) ^ Fintype.card ↥Xᶜ := by
      rw [(Q + Qᵀ).cutRank_eq_rank X]
      exact_mod_cast Matrix.card_ker_mul_two_pow_rank C
    rw [eq_div_iff (by positivity), mul_right_comm, h1, ← pow_add, add_comm, card_add_card_compl]
  suffices hrow : ∑ a, (M *ᵥ q_vec) a ^ 2 ≤
      ((kerCard : ℝ) * (2 : ℝ) ^ Fintype.card X) * ∑ b, q_vec b ^ 2 by
    refine (Matrix.abs_sum_mul_le_sqrt_mul_sqrt M p_vec q_vec).trans ?_
    rw [← hker_eq, mul_comm _ √(∑ a, p_vec a ^ 2), mul_assoc,
      ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ kerCard * 2 ^ Fintype.card X)]
    gcongr
  let q' : (↥Xᶜ → ZMod 2) → ℝ := fun w => h w * q_vec (eY.symm w)
  have hgsq (u : X → ZMod 2) : g u ^ 2 = 1 := by
    dsimp only [g]; rw [pow_right_comm, neg_one_sq, one_pow]
  have hhsq (w : ↥Xᶜ → ZMod 2) : h w ^ 2 = 1 := by
    dsimp only [h]; rw [pow_right_comm, neg_one_sq, one_pow]
  have hsum_reidx : (∑ a, (M *ᵥ q_vec) a ^ 2) =
      ∑ u : X → ZMod 2, (∑ w : ↥Xᶜ → ZMod 2, q' w * (-1 : ℝ) ^ (u ⬝ᵥ C *ᵥ w).val) ^ 2 := by
    refine Fintype.sum_equiv eX _ _ fun a => ?_
    have hmv : (M *ᵥ q_vec) a =
        g (eX a) * ∑ w : ↥Xᶜ → ZMod 2, q' w * (-1 : ℝ) ^ (eX a ⬝ᵥ C *ᵥ w).val := by
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Fintype.sum_equiv eY _ _ fun b => ?_
      rw [hM_entry a b]
      simp only [q', Equiv.symm_apply_apply]
      ring
    rw [hmv, mul_pow, hgsq (eX a), one_mul]
  let K (w w' : ↥Xᶜ → ZMod 2) : ℝ :=
    if C *ᵥ w + C *ᵥ w' = 0 then (2 : ℝ) ^ Fintype.card X else 0
  have hexpand : (∑ u : X → ZMod 2,
        (∑ w : ↥Xᶜ → ZMod 2, q' w * (-1 : ℝ) ^ (u ⬝ᵥ C *ᵥ w).val) ^ 2) =
      ∑ w, ∑ w', q' w * q' w' * K w w' := by
    calc ∑ u : X → ZMod 2, (∑ w, q' w * (-1 : ℝ) ^ (u ⬝ᵥ C *ᵥ w).val) ^ 2
        = ∑ u, ∑ w, ∑ w', q' w * q' w' * (-1 : ℝ) ^ (u ⬝ᵥ (C *ᵥ w + C *ᵥ w')).val := by
            refine Fintype.sum_congr _ _ fun u => ?_
            simp only [sq, Finset.sum_mul_sum, dotProduct_add, ZMod.neg_one_pow_val_add]
            exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => by ring
      _ = ∑ w, ∑ w', ∑ u, q' w * q' w' * (-1 : ℝ) ^ (u ⬝ᵥ (C *ᵥ w + C *ᵥ w')).val := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun w _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => by
            rw [← Finset.mul_sum, Matrix.sum_neg_one_pow_val_dotProduct]
  have hfib_eq (w w' : ↥Xᶜ → ZMod 2) : C *ᵥ w + C *ᵥ w' = 0 ↔ C *ᵥ w' = C *ᵥ w := by
    rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self, eq_comm]
  have hfib_card (w : ↥Xᶜ → ZMod 2) :
      ∑ w', K w w' = (kerCard : ℝ) * (2 : ℝ) ^ Fintype.card X := by
    simp_rw [K, hfib_eq]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
    congr 1
    exact_mod_cast Matrix.card_filter_mulVec_eq C w
  have hq'_sum : ∑ w : ↥Xᶜ → ZMod 2, q' w ^ 2 = ∑ b : ↥Xᶜ → Bool, q_vec b ^ 2 := by
    refine Fintype.sum_equiv eY.symm _ _ fun w => ?_
    simp only [q', mul_pow, hhsq w, one_mul]
  rw [hsum_reidx, hexpand]
  calc ∑ w, ∑ w', q' w * q' w' * K w w'
      ≤ ∑ w, ∑ w', (q' w ^ 2 * K w w' / 2 + q' w' ^ 2 * K w' w / 2) :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun w' _ => by
          have hK : 0 ≤ K w w' := by simp only [K]; split_ifs <;> positivity
          rw [show K w' w = K w w' by simp only [K, add_comm]]
          linarith [mul_nonneg (sub_nonneg.2 (two_mul_le_add_sq (q' w) (q' w'))) hK]
    _ = ∑ w, q' w ^ 2 * ∑ w', K w w' := by
          simp only [Finset.sum_add_distrib]
          rw [Finset.sum_comm (f := fun w w' => q' w' ^ 2 * K w' w / 2), ← two_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun w' _ => by ring
    _ = ((kerCard : ℝ) * (2 : ℝ) ^ Fintype.card X) * ∑ b, q_vec b ^ 2 := by
          simp only [hfib_card]
          rw [← Finset.sum_mul, hq'_sum, mul_comm]

open Classical in
/-- **Sign-rank lower bound for quadratic forms via Forster and Lindsey.** For any quadratic form
`BitString.quadForm Q` over `𝔽₂` and any coordinate cut `X : Set ι`, the sign-rank across `(X, Xᶜ)`
satisfies `2 ^ (Q + Qᵀ).cutRank X ≤ signRank ^ 2`. -/
theorem two_pow_cutRank_le_signRank_quadForm_sq {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι (ZMod 2)) (X : Set ι) :
    2 ^ (Q + Qᵀ).cutRank X ≤
      signRank (fun (a : X → Bool) (b : ↥Xᶜ → Bool) =>
        BitString.quadForm Q
          ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (a, b))) ^ 2 := by
  let glue := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  let f : (X → Bool) → (↥Xᶜ → Bool) → Bool := fun a b => BitString.quadForm Q (glue (a, b))
  set M := signMatrix ℝ f
  have hforster := mul_sqrt_card_mul_card_le_mul_signRank f M
    (μ := 1) (lam := √((2 : ℝ) ^ Fintype.card ι / (2 : ℝ) ^ (Q + Qᵀ).cutRank X))
    (fun a b => by
      simp only [M, signMatrix_apply]
      by_cases hfab : f a b = true <;> simp only [hfab, ↓reduceIte] <;> norm_num)
    (abs_sum_mul_signMatrix_quadForm_le Q X)
  have hsq := pow_le_pow_left₀ (by positivity) hforster 2
  have hcard_prod : (Fintype.card (X → Bool) : ℝ) * Fintype.card (↥Xᶜ → Bool) =
      (2 : ℝ) ^ Fintype.card ι := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, ← pow_add,
      card_add_card_compl]
  rw [one_mul, Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity), hcard_prod,
    div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hsq
  exact_mod_cast le_of_mul_le_mul_left hsq (by positivity : (0 : ℝ) < 2 ^ Fintype.card ι)

open Classical in
/-- **Low-rank Frobenius bilinear bound against quadratic forms.** If `P_mat = U_mat * V_mat`
factors through a finite index type `κ`, then across any coordinate cut `X : Set ι`, the inner
product of `P_mat` with the `±1` sign matrix `M` of `BitString.quadForm Q` satisfies
`(∑_{a, b} M_{a, b} P_{a, b})² · 2 ^ (Q + Qᵀ).cutRank X ≤ |κ| · 2 ^ |ι| · ∑_{a, b} P_{a, b}²`. -/
theorem sq_sum_mul_signMatrix_quadForm_le_card_of_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (Q : Matrix ι ι (ZMod 2)) (X : Set ι)
    (U_mat : Matrix (X → Bool) κ ℝ) (V_mat : Matrix κ (↥Xᶜ → Bool) ℝ) :
    (∑ a, ∑ b,
        signMatrix ℝ (fun a' b' =>
          BitString.quadForm Q ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (a', b')))
          a b * (U_mat * V_mat) a b) ^ 2 *
      (2 : ℝ) ^ (Q + Qᵀ).cutRank X ≤
      (Fintype.card κ : ℝ) * (2 : ℝ) ^ Fintype.card ι *
        ∑ a, ∑ b, (U_mat * V_mat) a b ^ 2 := by
  let _ : DecidableEq κ := Classical.decEq κ
  set P_mat := U_mat * V_mat
  let glue := (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm
  let f : (X → Bool) → (↥Xᶜ → Bool) → Bool := fun a b => BitString.quadForm Q (glue (a, b))
  set M := signMatrix ℝ f
  let E := EuclideanSpace ℝ (X → Bool)
  let fLin : EuclideanSpace ℝ κ →ₗ[ℝ] E := Matrix.toEuclideanLin U_mat
  let S : Submodule ℝ E := LinearMap.range fLin
  have hdim : Module.finrank ℝ S ≤ Fintype.card κ :=
    fLin.finrank_range_le.trans_eq finrank_euclideanSpace
  let col (b : ↥Xᶜ → Bool) : E := WithLp.toLp 2 fun a => P_mat a b
  have hcol_mem (b : ↥Xᶜ → Bool) : col b ∈ S := by
    refine ⟨WithLp.toLp 2 fun k => V_mat k b, ?_⟩
    ext a
    change (U_mat *ᵥ fun k => V_mat k b) a = P_mat a b
    simp only [P_mat, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  obtain ⟨onb⟩ : Nonempty (OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S) :=
    ⟨stdOrthonormalBasis ℝ S⟩
  set r := Module.finrank ℝ S
  obtain ⟨e_vec, w_vec, hP_decomp, he_norm, hw_parseval⟩ :
      ∃ (e_vec : Fin r → (X → Bool) → ℝ) (w_vec : Fin r → (↥Xᶜ → Bool) → ℝ),
        (∀ a b, P_mat a b = ∑ j : Fin r, e_vec j a * w_vec j b) ∧
        (∀ j : Fin r, ∑ a : X → Bool, e_vec j a ^ 2 = 1) ∧
        (∀ b : ↥Xᶜ → Bool, ∑ j : Fin r, w_vec j b ^ 2 = ∑ a, P_mat a b ^ 2) := by
    let e₀ (j : Fin r) (a : X → Bool) : ℝ := ((onb j : S) : E).ofLp a
    let w₀ (j : Fin r) (b : ↥Xᶜ → Bool) : ℝ := inner ℝ (onb j) (⟨col b, hcol_mem b⟩ : S)
    refine ⟨e₀, w₀, fun a b => ?_, fun j => ?_, fun b => ?_⟩
    · have hrepr := onb.sum_repr' (⟨col b, hcol_mem b⟩ : S)
      let evala : E →ₗ[ℝ] ℝ :=
        { toFun := fun v => v.ofLp a
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hval := congrArg (evala.comp S.subtype) hrepr
      rw [map_sum] at hval
      simp only [LinearMap.comp_apply, Submodule.coe_subtype, map_smul, evala, smul_eq_mul] at hval
      exact hval.symm.trans (Finset.sum_congr rfl fun j _ => mul_comm (w₀ j b) (e₀ j a))
    · exact (EuclideanSpace.real_norm_sq_eq ((onb j : S) : E)).symm.trans
        (by rw [Submodule.norm_coe, onb.orthonormal.1 j, one_pow])
    · exact (onb.sum_sq_inner_right (⟨col b, hcol_mem b⟩ : S)).trans
        (EuclideanSpace.real_norm_sq_eq (col b))
  have hw_tot : ∑ j : Fin r, ∑ b, w_vec j b ^ 2 = ∑ a, ∑ b, P_mat a b ^ 2 := by
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun b _ => hw_parseval b).trans Finset.sum_comm
  set L := √((2 : ℝ) ^ Fintype.card ι / (2 : ℝ) ^ (Q + Qᵀ).cutRank X)
  have hL_nn : 0 ≤ L := Real.sqrt_nonneg _
  have habs : |∑ a, ∑ b, M a b * P_mat a b| ≤
      L * √(r : ℝ) * √(∑ a, ∑ b, P_mat a b ^ 2) := by
    have hswap : (∑ a, ∑ b, M a b * P_mat a b) =
        ∑ j : Fin r, ∑ a, ∑ b, e_vec j a * M a b * w_vec j b := by
      simp_rw [hP_decomp, Finset.mul_sum]
      refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm.trans ?_).trans Finset.sum_comm
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ =>
        (mul_assoc _ _ _).symm.trans (congrArg (· * w_vec j b) (mul_comm _ _))
    rw [hswap]
    calc |∑ j : Fin r, ∑ a, ∑ b, e_vec j a * M a b * w_vec j b|
        ≤ ∑ j : Fin r, |∑ a, ∑ b, e_vec j a * M a b * w_vec j b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin r, L * √(1 : ℝ) * √(∑ b, w_vec j b ^ 2) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h := abs_sum_mul_signMatrix_quadForm_le Q X (e_vec j) (w_vec j)
          rwa [he_norm j] at h
      _ = L * ∑ j : Fin r, √(1 : ℝ) * √(∑ b, w_vec j b ^ 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => mul_assoc L _ _
      _ ≤ L * (√(∑ _j : Fin r, (1 : ℝ)) * √(∑ j : Fin r, ∑ b, w_vec j b ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (Real.sum_sqrt_mul_sqrt_le _ (fun _ => zero_le_one)
              (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)) hL_nn
      _ = L * √(r : ℝ) * √(∑ a, ∑ b, P_mat a b ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
            hw_tot, mul_assoc]
  have hsq : (∑ a, ∑ b, M a b * P_mat a b) ^ 2 ≤
      L ^ 2 * (r : ℝ) * ∑ a, ∑ b, P_mat a b ^ 2 := by
    have h1 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg r)] at h1
    exact h1.trans_eq (congrArg (L ^ 2 * (r : ℝ) * ·)
      (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)))
  have hL_sq : L ^ 2 * (2 : ℝ) ^ (Q + Qᵀ).cutRank X = (2 : ℝ) ^ Fintype.card ι := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  calc (∑ a, ∑ b, M a b * P_mat a b) ^ 2 * (2 : ℝ) ^ (Q + Qᵀ).cutRank X
      ≤ (L ^ 2 * (r : ℝ) * ∑ a, ∑ b, P_mat a b ^ 2) * (2 : ℝ) ^ (Q + Qᵀ).cutRank X := by gcongr
    _ = (r : ℝ) * (2 : ℝ) ^ Fintype.card ι * ∑ a, ∑ b, P_mat a b ^ 2 := by rw [← hL_sq]; ring
    _ ≤ (Fintype.card κ : ℝ) * (2 : ℝ) ^ Fintype.card ι * ∑ a, ∑ b, P_mat a b ^ 2 := by gcongr

end Cslib.Communication
