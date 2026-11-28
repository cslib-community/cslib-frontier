/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Orthogonalization
public import CslibFrontier.Foundations.Quantum.Algebra.FamApprox
public import CslibFrontier.Foundations.Quantum.Algebra.CharacterFamily
import CslibFrontier.Foundations.Algebra.BigOperators.Selection
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Polar

/-!
# Orthogonalization of measurements

A measurement whose effects are almost idempotent in a state is close to a projective measurement
in that state, with no loss in the dimension: for a measurement `M` on `ℂ^ι` and any state `φ` on
the matrix algebra there is a projective measurement `P` on `ℂ^ι` with

`∑_a ‖M_a - P_a‖²_φ ≤ 9 (1 - φ(∑_a M_a²))`

(`Cslib.Quantum.Measurement.exists_isProjective_sum_norm_sub_sq_le`). This is
[de la Salle, Theorem 1.2][delaSalle2022] (arXiv:2103.14126v2) for the finite von Neumann algebra
`M_ι(ℂ)`. Since `φ` is an arbitrary state, `P` stays on the factor `M` acts on, which rigidity
arguments for tensor-product strategies need. The orthogonalization lemma of Kempe, Kobayashi,
Matsumoto, Toner and Vidick, and its quantitative versions, have error polynomial in `ε`; de la
Salle's is linear.

The proof follows §3 of the paper, with its two lemmas made explicit in finite dimension:

* **Selection** (Lemma 3.1). Diagonalize each effect, `M_a = U_a diag(λ_a) U_aᴴ`, and select
  `|ι|` of the pairs `(a, k)`: the ones of largest weight `λ_{a,k} φ(U_a e_k e_kᴴ U_aᴴ)`. The
  projections `q_a` onto the selected eigenvectors commute with `M_a`, have total rank `|ι|`, and
  satisfy `φ(∑_a M_a²) ≤ φ(∑_a q_a M_a)`: the eigenvalues form a fractional selection of total
  mass `|ι|`, and the largest weights beat every such selection
  (`Finset.exists_card_eq_sum_mul_le`). This replaces the paper's Krein–Milman argument.
* **Polar decomposition** (Lemma 3.2). The rows `√λ_{a,k} (U_a e_k)ᴴ` of the selected pairs form a
  square matrix `y` with `yᴴ y = ∑_a q_a M_a`. Its polar decomposition `y = R |y|`, with `R`
  unitary (`Matrix.exists_polar`), gives the projective measurement
  `P_a = Rᴴ T_a R`, where `T_a` projects onto the selected pairs with outcome `a`, and
  `|y| P_a |y| = q_a M_a`.
* **Estimate.** `Cslib.Quantum.Measurement.sum_norm_sub_sq_le_of_dilation` turns these data into
  the bound, in any star-ordered algebra.

## Main results

* `Cslib.Quantum.Measurement.exists_isProjective_sum_norm_sub_sq_le`,
  `Cslib.Quantum.Measurement.exists_isProjective_sum_norm_sub_sq_le_of_le`: orthogonalization.
* `Cslib.Quantum.Measurement.exists_isProjective_famApprox`: orthogonalization of families, in
  the family relation `≈ᶠ`.
* `Cslib.Quantum.Measurement.exists_isProjective_charObs`: unitary, exactly linear character
  observables close to those of a measurement.

## References

* [M. de la Salle, *Orthogonalization of positive operator valued measures*][delaSalle2022]
-/

@[expose] public section

open Matrix Finset
open scoped MatrixOrder ComplexOrder BigOperators

namespace Cslib.Quantum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `U diag(f) Uᴴ` for a real vector `f`. -/
private noncomputable def conjDiag (U : Matrix ι ι ℂ) (f : ι → ℝ) : Matrix ι ι ℂ :=
  U * diagonal (fun k => (f k : ℂ)) * Uᴴ

variable {U : Matrix ι ι ℂ}

private theorem conjDiag_mul (hU : Uᴴ * U = 1) (f g : ι → ℝ) :
    conjDiag U f * conjDiag U g = conjDiag U (f * g) := by
  simp only [conjDiag, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
    diagonal_mul_diagonal]
  congr 3
  ext k
  simp

private theorem conjDiag_sub (f g : ι → ℝ) : conjDiag U (f - g) = conjDiag U f - conjDiag U g := by
  simp only [conjDiag, ← Matrix.mul_sub, ← Matrix.sub_mul, diagonal_sub]
  congr 3
  ext k
  simp

private theorem conjTranspose_conjDiag (f : ι → ℝ) : (conjDiag U f)ᴴ = conjDiag U f := by
  have : star (fun k => (f k : ℂ)) = fun k => (f k : ℂ) := by
    ext k; simp
  simp only [conjDiag, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc, this]

private theorem posSemidef_conjDiag {f : ι → ℝ} (hf : ∀ k, 0 ≤ f k) : (conjDiag U f).PosSemidef :=
  (posSemidef_diagonal_iff.mpr fun k =>
    Complex.zero_le_real.mpr (hf k)).mul_mul_conjTranspose_same U

private theorem conjDiag_eq_sum (f : ι → ℝ) :
    conjDiag U f = ∑ k, (f k : ℂ) • conjDiag U (Pi.single k 1) := by
  have : diagonal (fun k => (f k : ℂ)) =
      ∑ k, (f k : ℂ) • diagonal (fun j => (((Pi.single k (1 : ℝ) : ι → ℝ) j : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.sum_apply, Pi.single_apply, apply_ite]
    · simp [Matrix.sum_apply, hij]
  simp only [conjDiag, this, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

private theorem trace_conjDiag (hU : Uᴴ * U = 1) (f : ι → ℝ) :
    (conjDiag U f).trace = ∑ k, (f k : ℂ) := by
  rw [conjDiag, trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, trace_diagonal]


/-- A real-diagonal matrix bounded by `1` has diagonal entries at most `1`. -/
private theorem le_one_of_conjDiag_le_one (hU : Uᴴ * U = 1) {f : ι → ℝ}
    (h : conjDiag U f ≤ 1) (k : ι) : f k ≤ 1 := by
  have hd := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same U
  have e : Uᴴ * (1 - conjDiag U f) * U = 1 - diagonal (fun k => (f k : ℂ)) := by
    simp only [conjDiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU, ← Matrix.mul_assoc,
      Matrix.one_mul]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [e] at hd
  have := hd.diag_nonneg (i := k)
  rw [Matrix.sub_apply, one_apply_eq, diagonal_apply_eq] at this
  have h' : ((1 - f k : ℝ) : ℂ) ≥ 0 := by push_cast; exact this
  linarith [Complex.zero_le_real.mp h']

private theorem conjDiag_apply (f : ι → ℝ) (j j' : ι) :
    conjDiag U f j j' = ∑ k, U j k * (f k : ℂ) * star (U j' k) := by
  simp [conjDiag, Matrix.mul_apply, diagonal_apply]

/-- The state of `U diag(f) Uᴴ` is linear in `f`. -/
private theorem re_apply_conjDiag (φ : AlgState (Matrix ι ι ℂ)) (f : ι → ℝ) :
    (φ (conjDiag U f)).re = ∑ k, f k * (φ (conjDiag U (Pi.single k 1))).re := by
  conv_lhs => rw [conjDiag_eq_sum]
  rw [map_sum, Complex.re_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul]

end Cslib.Quantum

namespace Cslib.Quantum.Measurement

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- **Orthogonalization of measurements** [de la Salle, §1, Theorem 1.2][delaSalle2022]: every
measurement `M` on `ℂ^ι` is close to a projective measurement `P` on `ℂ^ι` in any state `φ`:
`∑_a ‖M_a - P_a‖²_φ ≤ 9 (1 - φ(∑_a M_a²))`. -/
theorem exists_isProjective_sum_norm_sub_sq_le (φ : AlgState (Matrix ι ι ℂ))
    (M : Measurement α (Matrix ι ι ℂ)) :
    ∃ P : Measurement α (Matrix ι ι ℂ), P.IsProjective ∧
      ∑ a, φ.norm (M.effect a - P.effect a) ^ 2 ≤
        9 * (1 - ∑ a, (φ (M.effect a * M.effect a)).re) := by
  classical
  have hpsd : ∀ a, (M.effect a).PosSemidef := fun a => nonneg_iff_posSemidef.mp (M.nonneg a)
  let U : α → Matrix ι ι ℂ := fun a => ((hpsd a).1.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU1 : ∀ a, (U a)ᴴ * U a = 1 := fun a => by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  set lam : α → ι → ℝ := fun a => (hpsd a).1.eigenvalues
  have hM : ∀ a, M.effect a = conjDiag (U a) (lam a) := fun a => by
    conv_lhs => rw [(hpsd a).1.spectral_theorem]
    simp [conjDiag, U, lam, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def]
  have hl0 : ∀ a k, 0 ≤ lam a k := fun a => (hpsd a).eigenvalues_nonneg
  have hl1 : ∀ a k, lam a k ≤ 1 := fun a =>
    le_one_of_conjDiag_le_one (hU1 a) (hM a ▸ M.effect_le_one a)
  -- The eigenvalues of all effects sum to the dimension.
  have hsum : ∑ p : α × ι, lam p.1 p.2 = Fintype.card ι := by
    have h := congrArg (fun A : Matrix ι ι ℂ => A.trace) M.sum_effect
    simp only [trace_sum, hM, trace_conjDiag (hU1 _), trace_one] at h
    rw [Fintype.sum_prod_type]
    exact_mod_cast h
  -- Select the `|ι|` largest weights.
  set w : α × ι → ℝ := fun p => lam p.1 p.2 * (φ (conjDiag (U p.1) (Pi.single p.2 1))).re
  obtain ⟨S, hS, hSw⟩ := Finset.exists_card_eq_sum_mul_le w (fun p => lam p.1 p.2)
    (fun p => hl0 _ _) (fun p => hl1 _ _) hsum
  set sel : α → ι → ℝ := fun a k => if (a, k) ∈ S then 1 else 0
  set q : α → Matrix ι ι ℂ := fun a => conjDiag (U a) (sel a)
  have hqM : ∀ a, q a * M.effect a = conjDiag (U a) (sel a * lam a) := fun a => by
    rw [hM, conjDiag_mul (hU1 a)]
  -- The selection beats the measurement: `φ(∑_a M_a²) ≤ φ(∑_a q_a M_a)`.
  have hsel : ∑ a, (φ (M.effect a * M.effect a)).re ≤ (φ (∑ a, q a * M.effect a)).re := by
    have e1 : ∑ a, (φ (M.effect a * M.effect a)).re = ∑ p : α × ι, w p * lam p.1 p.2 := by
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun a _ => ?_
      rw [hM, conjDiag_mul (hU1 a), re_apply_conjDiag]
      refine sum_congr rfl fun k _ => ?_
      simp only [w, Pi.mul_apply]
      ring
    have e2 : (φ (∑ a, q a * M.effect a)).re = ∑ p ∈ S, w p := by
      rw [← Finset.filter_univ_mem S, Finset.sum_filter, Fintype.sum_prod_type, map_sum,
        Complex.re_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [hqM, re_apply_conjDiag]
      refine sum_congr rfl fun k _ => ?_
      simp only [w, sel, Pi.mul_apply]
      split_ifs <;> ring
    rw [e1, e2]
    exact hSw
  -- The square matrix `y` with rows `√λ_{a,k} e_{a,k}ᴴ` over the selection.
  let y : Matrix S ι ℂ :=
    Matrix.of fun s j => (√(lam s.val.1 s.val.2) : ℂ) * star (U s.val.1 j s.val.2)
  have hyT : ∀ t : α → ℝ, yᴴ * diagonal (fun s : S => (t s.val.1 : ℂ)) * y =
      ∑ a, (t a : ℂ) • (q a * M.effect a) := fun t => by
    ext j j'
    simp only [Matrix.mul_apply, conjTranspose_apply, diagonal_apply, y, Matrix.of_apply,
      Matrix.sum_apply, Matrix.smul_apply, hqM, conjDiag_apply, smul_eq_mul, mul_sum]
    have hsq : ∀ s : S, star ((√(lam s.val.1 s.val.2) : ℂ) * star (U s.val.1 j s.val.2)) *
        (√(lam s.val.1 s.val.2) : ℂ) =
          (lam s.val.1 s.val.2 : ℂ) * U s.val.1 j s.val.2 := fun s => by
      have e :
          (√(lam s.val.1 s.val.2) : ℂ) * (√(lam s.val.1 s.val.2) : ℂ) = lam s.val.1 s.val.2 := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hl0 _ _)]
      rw [star_mul', star_star, Complex.star_def, Complex.conj_ofReal]
      linear_combination (U s.val.1 j s.val.2) * e
    simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    let F : α × ι → ℂ := fun p =>
      (t p.1 : ℂ) * ((lam p.1 p.2 : ℂ) * U p.1 j p.2) * star (U p.1 j' p.2)
    have hl : ∀ x : S,
        star ((√(lam x.val.1 x.val.2) : ℂ) * star (U x.val.1 j x.val.2)) * (t x.val.1 : ℂ) *
        ((√(lam x.val.1 x.val.2) : ℂ) * star (U x.val.1 j' x.val.2)) = F x.val := fun x => by
      simp only [F]
      rw [← hsq x]
      ring
    rw [sum_congr rfl fun x _ => hl x, Finset.sum_coe_sort S F, ← Finset.filter_univ_mem S,
      Finset.sum_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => sum_congr rfl fun k _ => ?_
    simp only [F, sel, Pi.mul_apply]
    split_ifs <;> push_cast <;> ring
  have hyy : yᴴ * y = ∑ a, q a * M.effect a := by
    simpa [show diagonal (fun _ : S => (1 : ℂ)) = 1 from rfl] using hyT 1
  -- Indicator of the outcome `a` on the selection.
  let T : α → Matrix S S ℂ := fun a =>
    diagonal fun s : S => (((fun a' : α => if a' = a then (1 : ℝ) else 0) s.val.1 : ℝ) : ℂ)
  have hyTa : ∀ a, yᴴ * T a * y = q a * M.effect a := fun a => by
    simpa using hyT (fun a' => if a' = a then (1 : ℝ) else 0)
  have hTT : ∀ a, T a * T a = T a := fun a => by
    simp only [T, diagonal_mul_diagonal]
    congr 1
    ext s
    split_ifs <;> simp
  have hTsum : ∑ a, T a = 1 := by
    ext s s'
    by_cases hss : s = s'
    · subst hss
      simp [T, Matrix.sum_apply, apply_ite]
    · simp [T, Matrix.sum_apply, hss]
  -- Polar decomposition `y = R h`.
  have hcard : Fintype.card S = Fintype.card ι := by rw [Fintype.card_coe, hS]
  obtain ⟨R, h, hR1, hR2, hh0, hhh, hyR, hle⟩ := Matrix.exists_polar y hcard
  have hqMle : yᴴ * y ≤ 1 := by
    rw [hyy, Matrix.le_iff, ← M.sum_effect, ← sum_sub_distrib]
    refine posSemidef_sum _ fun a _ => ?_
    rw [hqM, hM, ← conjDiag_sub]
    refine posSemidef_conjDiag fun k => ?_
    simp only [sel, Pi.sub_apply, Pi.mul_apply]
    split_ifs <;> simp [hl0 a k]
  -- The projective measurement `p_a = Rᴴ T_a R`.
  let P : Measurement α (Matrix ι ι ℂ) :=
    { effect := fun a => Rᴴ * T a * R
      nonneg := fun a => nonneg_iff_posSemidef.mpr
        ((posSemidef_diagonal_iff.mpr fun s => by
          dsimp only
          split_ifs <;> simp).conjTranspose_mul_mul_same R)
      sum_effect := by
        rw [← Matrix.sum_mul, ← Matrix.mul_sum, hTsum, Matrix.mul_one, hR1] }
  have hP : P.IsProjective := fun a => by
    change Rᴴ * T a * R * (Rᴴ * T a * R) = Rᴴ * T a * R
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R Rᴴ, hR2, Matrix.one_mul, ← Matrix.mul_assoc (T a) (T a), hTT]
  have hhs : hᴴ = h := hh0.1
  have hp : ∀ a, h * P.effect a * h = q a * M.effect a := fun a => by
    change h * (Rᴴ * T a * R) * h = q a * M.effect a
    rw [← hyTa, hyR, conjTranspose_mul, hhs]
    simp only [Matrix.mul_assoc]
  refine ⟨P, hP, sum_norm_sub_sq_le_of_dilation φ M P hP q (fun a => ?_) (fun a => ?_)
    (fun a => ?_) (nonneg_iff_posSemidef.mpr hh0) (hle hqMle) (by rw [hhh, hyy]) hp hsel⟩
  · change conjDiag (U a) (sel a) * conjDiag (U a) (sel a) = conjDiag (U a) (sel a)
    rw [conjDiag_mul (hU1 a)]
    congr 1
    ext k
    simp only [sel, Pi.mul_apply]
    split_ifs <;> simp
  · rw [IsSelfAdjoint, star_eq_conjTranspose]
    exact conjTranspose_conjDiag _
  · change conjDiag (U a) (sel a) * M.effect a = M.effect a * conjDiag (U a) (sel a)
    rw [hM, conjDiag_mul (hU1 a), conjDiag_mul (hU1 a), mul_comm]

/-- **Orthogonalization of measurements**, with the defect as a hypothesis: if
`φ(∑_a M_a²) ≥ 1 - ε`, then `M` is `9ε`-close to a projective measurement. -/
theorem exists_isProjective_sum_norm_sub_sq_le_of_le (φ : AlgState (Matrix ι ι ℂ))
    (M : Measurement α (Matrix ι ι ℂ)) {ε : ℝ}
    (hε : 1 - ε ≤ ∑ a, (φ (M.effect a * M.effect a)).re) :
    ∃ P : Measurement α (Matrix ι ι ℂ), P.IsProjective ∧
      ∑ a, φ.norm (M.effect a - P.effect a) ^ 2 ≤ 9 * ε := by
  obtain ⟨P, hP, h⟩ := exists_isProjective_sum_norm_sub_sq_le φ M
  exact ⟨P, hP, h.trans (by linarith)⟩

/-- Orthogonalize on the original space, measuring the distance in a state
after a unital star-algebra embedding into a larger matrix algebra. -/
theorem exists_isProjective_sum_norm_map_sub_sq_le_of_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (φ : AlgState (Matrix κ κ ℂ)) (e : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix κ κ ℂ)
    (M : Measurement α (Matrix ι ι ℂ)) {ε : ℝ}
    (hε : 1 - ε ≤ ∑ a, (φ (e (M.effect a * M.effect a))).re) :
    ∃ P : Measurement α (Matrix ι ι ℂ), P.IsProjective ∧
      ∑ a, φ.norm (e (M.effect a) - e (P.effect a)) ^ 2 ≤ 9 * ε := by
  let ψ : AlgState (Matrix ι ι ℂ) :=
    { toFun := φ ∘ e
      map_add' := fun X Y => by simp only [Function.comp_apply, map_add]
      map_smul' := fun z X => by simp only [Function.comp_apply, map_smul, RingHom.id_apply]
      monotone' := fun _ _ h => φ.apply_mono (OrderHomClass.mono e h)
      map_one' := by simp only [Function.comp_apply, map_one, φ.map_one] }
  obtain ⟨P, hP, h⟩ := exists_isProjective_sum_norm_sub_sq_le_of_le ψ M hε
  have he (a : α) :
      ψ.norm (M.effect a - P.effect a) ^ 2 =
        φ.norm (e (M.effect a) - e (P.effect a)) ^ 2 := by
    rw [AlgState.norm_sq, AlgState.norm_sq]
    change (φ (e (star (M.effect a - P.effect a) * (M.effect a - P.effect a)))).re = _
    rw [map_mul, map_star, map_sub]
  exact ⟨P, hP, by simpa only [he] using h⟩

/-- **Orthogonalization of families of measurements**: if every measurement of a family has
`φ(∑_a M^q_a²) ≥ 1 - ε`, a family of projective measurements is `√(9ε)`-close to it, in the family
relation `≈ᶠ`, for every question distribution. -/
theorem exists_isProjective_famApprox {Q : Type*} [Fintype Q] (μ : PMF Q)
    (φ : AlgState (Matrix ι ι ℂ)) (M : Q → Measurement α (Matrix ι ι ℂ)) {ε : ℝ}
    (hε : ∀ q, 1 - ε ≤ ∑ a, (φ ((M q).effect a * (M q).effect a)).re) :
    ∃ P : Q → Measurement α (Matrix ι ι ℂ), (∀ q, (P q).IsProjective) ∧
      effects M ≈ᶠ[μ, φ; √(9 * ε)] effects P := by
  choose P hP hMP using fun q => exists_isProjective_sum_norm_sub_sq_le_of_le φ (M q) (hε q)
  exact ⟨P, hP, famApprox_of_forall hMP⟩

open scoped Matrix.Norms.L2Operator in
/-- **Unitary, exactly linear observables from a measurement.** A measurement `M` with bit-string
outcomes and `φ(∑_x M_x²) ≥ 1 - ε` has a projective measurement `P` whose character observables
`χ_P(a)` are unitary and exactly linear, and close on average to those of `M`:
`E_a ‖χ_M(a) - χ_P(a)‖²_φ ≤ 9ε`. -/
theorem exists_isProjective_charObs {n : Type*} [Fintype n] [DecidableEq n]
    (φ : AlgState (Matrix ι ι ℂ)) (M : Measurement (n → Bool) (Matrix ι ι ℂ)) {ε : ℝ}
    (hε : 1 - ε ≤ ∑ x, (φ (M.effect x * M.effect x)).re) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm (M.charObs a - P.charObs a) ^ 2 ≤ 9 * ε := by
  obtain ⟨P, hP, h⟩ := exists_isProjective_sum_norm_sub_sq_le_of_le φ M hε
  refine ⟨P, hP, hP.charObs_mem_unitary, hP.charObs_mul, ?_⟩
  simp only [charObs, walshSum_sub, expect_norm_walshSum_sq]
  exact h

end Cslib.Quantum.Measurement
