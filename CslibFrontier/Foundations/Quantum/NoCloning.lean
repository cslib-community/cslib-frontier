/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Bipartite
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The no-cloning theorem

No physical process copies an unknown pure quantum state [Wootters, Zurek][WoottersZurek1982],
[Dieks][Dieks1982]. This file proves both the **ancilla-free** form ([de Wolf][deWolf2019],
Chapter 1, Exercise 12, where the copying map acts on the two registers `E ⊗ E` alone, input and
blank) and **Wootters and Zurek's apparatus-assisted form** (`|ψ⟩|e⟩|a₀⟩ ↦ |ψ⟩|ψ⟩|a_ψ⟩`, where an
auxiliary apparatus or environment register `A` starts in a ready state `a₀` and ends in an
input-dependent state `a_ψ`; separating the blank target register `e ∈ E` from `A` keeps input and
output in the same space `(E ⊗ E) ⊗ A`, so unitaries are a special case):

* **Inner-product dichotomy** (the inner-product argument). Without an apparatus, if an isometry
  `U` of `E ⊗ E` copies two unit states, `U(ψ ⊗ e) = ψ ⊗ ψ` and `U(φ ⊗ e) = φ ⊗ φ`, then
  `⟪ψ, φ⟫ = ⟪ψ, φ⟫²`, forcing `ψ` and `φ` to be orthogonal or equal
  (`Cslib.Quantum.inner_eq_zero_or_eq_of_clone`). With an apparatus (`U((ψ ⊗ e) ⊗ a₀) =
  (ψ ⊗ ψ) ⊗ a_ψ`), `⟪ψ, φ⟫ = ⟪ψ, φ⟫² ⟪a_ψ, a_φ⟫` and Cauchy–Schwarz force `ψ` and `φ` to be
  orthogonal or equal up to a unit global phase (`φ = c • ψ` with `‖c‖ = 1`, i.e., the same
  physical ray: `Cslib.Quantum.inner_eq_zero_or_exists_smul_of_clone_apparatus`). Unlike the
  ancilla-free case, `ψ` and `-ψ` can both be cloned by absorbing the sign into `a_{-ψ} = -a_ψ`.
* **No linear cloner** (the linearity and superposition argument of Wootters–Zurek and Dieks, and
  of the hint to de Wolf's Exercise 12: basis states, then a superposition). If `dim E ≥ 2`, no
  linear map `L` of `(E ⊗ E) ⊗ A` maps `(ψ ⊗ e) ⊗ a₀` to `(ψ ⊗ ψ) ⊗ a_ψ` with `a_ψ ≠ 0` for
  every unit state `ψ` (`Cslib.Quantum.not_exists_linearMap_clone_apparatus`), and in particular no
  ancilla-free linear map of `E ⊗ E` copies every unit state up to a nonzero factor
  (`Cslib.Quantum.not_exists_linearMap_clone_smul`). For orthonormal `u, v` and `w = (u + v)/√2`,
  linearity makes `L((w ⊗ e) ⊗ a₀)` a combination of `(u ⊗ u) ⊗ a_u` and `(v ⊗ v) ⊗ a_v`,
  orthogonal to `(u ⊗ v) ⊗ a_w`, whereas `(w ⊗ w) ⊗ a_w` has inner product `⟪a_w, a_w⟫/2 ≠ 0`
  with `(u ⊗ v) ⊗ a_w`.

Both forms are stated for Mathlib's tensor products of inner product spaces and in coordinates, for
matrices acting on product states (`Cslib.Quantum.prodState`). For mixed-state cloning under CPTP
Kraus channels, see `CslibFrontier/Foundations/Quantum/DensityMatrix/NoCloning.lean`.

## Main results

* `Cslib.Quantum.inner_eq_zero_or_eq_of_clone`,
  `Cslib.Quantum.inner_eq_zero_or_exists_smul_of_clone_apparatus`: an isometry copying two unit
  states forces them to be orthogonal or equal (ancilla-free), or orthogonal or collinear up to a
  unit phase (with an input-dependent apparatus).
* `Cslib.Quantum.not_exists_linearMap_clone_apparatus`,
  `Cslib.Quantum.not_exists_linearMap_clone_smul`, `Cslib.Quantum.not_exists_linearMap_clone`: if
  `dim E ≥ 2`, no linear map copies every unit state with a nonzero apparatus state or nonzero
  scalar factor.
* `Cslib.Quantum.inner_eq_zero_or_eq_of_unitary_clone`,
  `Cslib.Quantum.inner_eq_zero_or_exists_smul_of_unitary_clone_apparatus`: the dichotomies for
  unitary matrices on `ℂ^{ι × ι}` and `ℂ^{(ι × ι) × α}`.
* `Cslib.Quantum.not_exists_matrix_clone_apparatus`,
  `Cslib.Quantum.not_exists_matrix_clone_smul`, `Cslib.Quantum.not_exists_matrix_clone`: if
  `|ι| ≥ 2`, no matrix copies every unit state of `ℂ^ι` with a nonzero apparatus state or scalar.

## References

* [W. K. Wootters, W. H. Zurek, *A single quantum cannot be cloned*][WoottersZurek1982]
* [D. Dieks, *Communication by EPR devices*][Dieks1982]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped TensorProduct InnerProductSpace

/-! ### The argument, for any multiplicative pairing -/

section Core

variable {E A G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The no-cloning dichotomy for a pairing `T` with `⟪T x y, T x' y'⟫ = ⟪x, x'⟫ ⟪y, y'⟫`. -/
private theorem inner_eq_zero_or_eq_of_clone_core (T : E → E → G)
    (hT : ∀ x y x' y', ⟪T x y, T x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ)
    (U : G →ₗᵢ[ℂ] G) {ψ φ e : E} (hψ₁ : ‖ψ‖ = 1) (hφ₁ : ‖φ‖ = 1) (he : ‖e‖ = 1)
    (hψ : U (T ψ e) = T ψ ψ) (hφ : U (T φ e) = T φ φ) : ⟪ψ, φ⟫_ℂ = 0 ∨ ψ = φ := by
  have h := U.inner_map_map (T ψ e) (T φ e)
  rw [hψ, hφ, hT, hT, inner_self_eq_one_of_norm_eq_one he, mul_one] at h
  exact (eq_zero_or_one_of_sq_eq_self (by rwa [sq])).imp id
    (inner_eq_one_iff_of_norm_eq_one hψ₁ hφ₁).mp

/-- The apparatus-assisted no-cloning dichotomy for a ternary pairing `T` with
`⟪T x y a, T x' y' a'⟫ = ⟪x, x'⟫ ⟪y, y'⟫ ⟪a, a'⟫`. -/
private theorem inner_eq_zero_or_exists_smul_of_clone_apparatus_core (T : E → E → A → G)
    (hT : ∀ x y a x' y' a', ⟪T x y a, T x' y' a'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ * ⟪a, a'⟫_ℂ)
    (U : G →ₗᵢ[ℂ] G) {ψ φ e : E} {a₀ aψ aφ : A}
    (hψ₁ : ‖ψ‖ = 1) (hφ₁ : ‖φ‖ = 1) (he : ‖e‖ = 1) (ha₀ : ‖a₀‖ = 1)
    (hψ : U (T ψ e a₀) = T ψ ψ aψ) (hφ : U (T φ e a₀) = T φ φ aφ) :
    ⟪ψ, φ⟫_ℂ = 0 ∨ ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ψ := by
  have norm_app {x : E} {ax : A} (hx : ‖x‖ = 1) (hUx : U (T x e a₀) = T x x ax) : ‖ax‖ = 1 := by
    have hn := U.inner_map_map (T x e a₀) (T x e a₀)
    rw [hUx, hT, hT, inner_self_eq_one_of_norm_eq_one hx, inner_self_eq_one_of_norm_eq_one he,
      inner_self_eq_one_of_norm_eq_one ha₀, one_mul, one_mul, mul_one] at hn
    refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp ?_
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hn]
    simp
  refine or_iff_not_imp_left.mpr fun h0 => ?_
  set c : ℂ := ⟪ψ, φ⟫_ℂ with hc_def
  have hn := congrArg norm (U.inner_map_map (T ψ e a₀) (T φ e a₀))
  simp only [hψ, hφ, hT, inner_self_eq_one_of_norm_eq_one he,
    inner_self_eq_one_of_norm_eq_one ha₀, mul_one, ← hc_def, norm_mul] at hn
  have hprod : ‖c‖ * ‖⟪aψ, aφ⟫_ℂ‖ = 1 :=
    mul_left_cancel₀ (norm_ne_zero_iff.mpr h0) (by linear_combination hn)
  have hc_le : ‖c‖ ≤ 1 := by simpa only [hc_def, hψ₁, hφ₁, mul_one] using norm_inner_le_norm ψ φ
  have ha_le : ‖⟪aψ, aφ⟫_ℂ‖ ≤ 1 := by
    simpa only [norm_app hψ₁ hψ, norm_app hφ₁ hφ, mul_one] using norm_inner_le_norm aψ aφ
  have hc1 : ‖c‖ = 1 := by nlinarith [norm_nonneg c, norm_nonneg ⟪aψ, aφ⟫_ℂ]
  have hcψ : ‖c • ψ‖ = 1 := by rw [norm_smul, hc1, hψ₁, one_mul]
  refine ⟨c, hc1, ((inner_eq_one_iff_of_norm_eq_one (𝕜 := ℂ) hcψ hφ₁).mp ?_).symm⟩
  rw [inner_smul_left, ← hc_def, RCLike.conj_mul, hc1]; norm_num

/-- No linear apparatus-assisted cloning for a ternary pairing `T` that is multiplicative on inner
products and linear in its first argument, in the presence of an orthonormal pair `u, v`. -/
private theorem not_clone_apparatus_core (T : E → E → A → G)
    (hT : ∀ x y a x' y' a', ⟪T x y a, T x' y' a'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ * ⟪a, a'⟫_ℂ)
    (hadd : ∀ x x' y a, T (x + x') y a = T x y a + T x' y a)
    (hsmul : ∀ (c : ℂ) x y a, T (c • x) y a = c • T x y a)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℂ = 0)
    (e : E) (a₀ : A) (L : G →ₗ[ℂ] G)
    (hL : ∀ ψ, ‖ψ‖ = 1 → ∃ aψ : A, aψ ≠ 0 ∧ L (T ψ e a₀) = T ψ ψ aψ) : False := by
  have hvu : ⟪v, u⟫_ℂ = 0 := inner_eq_zero_symm.mp huv
  have huu : ⟪u, u⟫_ℂ = 1 := inner_self_eq_one_of_norm_eq_one hu
  have hvv : ⟪v, v⟫_ℂ = 1 := inner_self_eq_one_of_norm_eq_one hv
  set s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hs_def
  have hs : starRingEnd ℂ s * s = 1 / 2 := by
    rw [hs_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs0 : s ≠ 0 := by
    rw [hs_def]; exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hw : ‖s • u + s • v‖ = 1 := by
    have h2 : ⟪s • u + s • v, s • u + s • v⟫_ℂ = 1 := by
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, huu, hvv,
        huv, hvu]
      linear_combination 2 * hs
    refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp ?_
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h2]
    simp
  obtain ⟨au, _, hLu⟩ := hL u hu
  obtain ⟨av, _, hLv⟩ := hL v hv
  obtain ⟨aw, haw, hLw⟩ := hL _ hw
  rw [hadd, hsmul, hsmul, map_add, map_smul, map_smul, hLu, hLv] at hLw
  have key := congrArg (⟪T u v aw, ·⟫_ℂ) hLw
  simp only [inner_add_right, inner_smul_right, hT, huu, hvv, huv, hvu] at key
  exact (mul_eq_zero.mp (by linear_combination -key : (s * s) * ⟪aw, aw⟫_ℂ = 0)).elim
    (fun h => hs0 (mul_self_eq_zero.mp h)) (fun h => haw (inner_self_eq_zero.mp h))

/-- No linear cloning, up to nonzero factors, for a pairing `T` that is multiplicative and
linear in its first argument, in the presence of an orthonormal pair `u, v`. -/
private theorem not_clone_core (T : E → E → G)
    (hT : ∀ x y x' y', ⟪T x y, T x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ)
    (hadd : ∀ x x' y, T (x + x') y = T x y + T x' y)
    (hsmul : ∀ (c : ℂ) x y, T (c • x) y = c • T x y)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℂ = 0)
    (e : E) (L : G →ₗ[ℂ] G) (c : E → ℂ) (hc : ∀ ψ, ‖ψ‖ = 1 → c ψ ≠ 0)
    (hL : ∀ ψ, ‖ψ‖ = 1 → L (T ψ e) = c ψ • T ψ ψ) : False :=
  not_clone_apparatus_core (A := ℂ) (fun x y a => a • T x y)
    (fun _ _ _ _ _ _ => by rw [inner_smul_left, inner_smul_right, hT, RCLike.inner_apply]; ring)
    (fun _ _ _ _ => by rw [hadd, smul_add]) (fun _ _ _ _ => by rw [hsmul, smul_comm])
    hu hv huv e 1 L fun ψ hψ => ⟨c ψ, hc ψ hψ, by rw [one_smul, hL ψ hψ]⟩

private theorem exists_orthonormal_pair (h : 1 < Module.rank ℂ E) :
    ∃ u v : E, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪u, v⟫_ℂ = 0 := by
  obtain ⟨x, hx⟩ := rank_pos_iff_exists_ne_zero.mp (zero_lt_one.trans h)
  obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_rank h hx
  have ho := InnerProductSpace.gramSchmidtNormed_orthonormal hxy
  exact ⟨_, _, ho.1 0, ho.1 1, ho.2 (by decide : (0 : Fin 2) ≠ 1)⟩

end Core

/-! ### Tensor products of inner product spaces -/

section TensorProduct

variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup A] [InnerProductSpace ℂ A]

/-- **No-cloning, inner-product form**, ancilla-free: if an isometry `U` of `E ⊗ E` (in particular
a unitary) copies two unit states `ψ` and `φ` onto a unit blank state `e`, then `ψ` and `φ` are
orthogonal or equal. -/
theorem inner_eq_zero_or_eq_of_clone (U : E ⊗[ℂ] E →ₗᵢ[ℂ] E ⊗[ℂ] E) {ψ φ e : E}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (he : ‖e‖ = 1)
    (hUψ : U (ψ ⊗ₜ e) = ψ ⊗ₜ ψ) (hUφ : U (φ ⊗ₜ e) = φ ⊗ₜ φ) : ⟪ψ, φ⟫_ℂ = 0 ∨ ψ = φ :=
  inner_eq_zero_or_eq_of_clone_core (fun x y => x ⊗ₜ[ℂ] y)
    (fun _ _ _ _ => TensorProduct.inner_tmul ℂ _ _ _ _) U hψ hφ he hUψ hUφ

/-- **Apparatus-assisted no-cloning, inner-product form** [Wootters, Zurek][WoottersZurek1982]: if
an isometry `U` of `(E ⊗ E) ⊗ A` (in particular a unitary) copies two unit states `ψ` and `φ` onto
a unit blank state `e` starting from a unit apparatus state `a₀`, leaving the apparatus in states
`aψ` and `aφ`, then `ψ` and `φ` are orthogonal or equal up to a unit global phase. -/
theorem inner_eq_zero_or_exists_smul_of_clone_apparatus
    (U : (E ⊗[ℂ] E) ⊗[ℂ] A →ₗᵢ[ℂ] (E ⊗[ℂ] E) ⊗[ℂ] A) {ψ φ e : E} {a₀ aψ aφ : A}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (he : ‖e‖ = 1) (ha₀ : ‖a₀‖ = 1)
    (hUψ : U ((ψ ⊗ₜ e) ⊗ₜ a₀) = (ψ ⊗ₜ ψ) ⊗ₜ aψ)
    (hUφ : U ((φ ⊗ₜ e) ⊗ₜ a₀) = (φ ⊗ₜ φ) ⊗ₜ aφ) :
    ⟪ψ, φ⟫_ℂ = 0 ∨ ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ψ :=
  inner_eq_zero_or_exists_smul_of_clone_apparatus_core (G := (E ⊗[ℂ] E) ⊗[ℂ] A)
    (fun x y a => (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] a)
    (fun _ _ _ _ _ _ => by simp only [TensorProduct.inner_tmul]) U hψ hφ he ha₀ hUψ hUφ

/-- **Wootters–Zurek no-cloning with an apparatus** [Wootters, Zurek][WoottersZurek1982]: if
`dim E ≥ 2`, no linear map `L` of `(E ⊗ E) ⊗ A` (in particular no unitary) maps `(ψ ⊗ e) ⊗ a₀` to
`(ψ ⊗ ψ) ⊗ a_ψ` with a nonzero post-cloning apparatus state `a_ψ` for every unit state `ψ`,
whatever the blank state `e` and ready apparatus state `a₀`. -/
theorem not_exists_linearMap_clone_apparatus (h : 1 < Module.rank ℂ E) (e : E) (a₀ : A) :
    ¬ ∃ L : (E ⊗[ℂ] E) ⊗[ℂ] A →ₗ[ℂ] (E ⊗[ℂ] E) ⊗[ℂ] A,
      ∀ ψ : E, ‖ψ‖ = 1 → ∃ aψ : A, aψ ≠ 0 ∧ L ((ψ ⊗ₜ e) ⊗ₜ a₀) = (ψ ⊗ₜ ψ) ⊗ₜ aψ := by
  rintro ⟨L, hL⟩
  obtain ⟨u, v, hu, hv, huv⟩ := exists_orthonormal_pair h
  exact not_clone_apparatus_core (G := (E ⊗[ℂ] E) ⊗[ℂ] A) (fun x y a => (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] a)
    (fun _ _ _ _ _ _ => by simp only [TensorProduct.inner_tmul])
    (fun _ _ _ _ => by rw [TensorProduct.add_tmul, TensorProduct.add_tmul])
    (fun _ _ _ _ => by rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul'])
    hu hv huv e a₀ L hL

/-- **No-cloning** [Wootters, Zurek][WoottersZurek1982], [Dieks][Dieks1982], ancilla-free and up
to nonzero factors: if `dim E ≥ 2`, no linear map `L` of `E ⊗ E` maps `ψ ⊗ e` to a nonzero
multiple of `ψ ⊗ ψ` for every unit state `ψ`, whatever the blank state `e`. In dimension `1`, for
every nonzero blank `e`, the identity is such a map (with factor `e / ψ`), so the hypothesis
`1 < Module.rank ℂ E` is needed for this form. Without the factor, no linear cloner exists even in
dimension `1`: cloning both `ψ` and `-ψ` forces `ψ ⊗ ψ = -(ψ ⊗ ψ)`. -/
theorem not_exists_linearMap_clone_smul (h : 1 < Module.rank ℂ E) (e : E) :
    ¬ ∃ (L : E ⊗[ℂ] E →ₗ[ℂ] E ⊗[ℂ] E) (c : E → ℂ),
      ∀ ψ : E, ‖ψ‖ = 1 → c ψ ≠ 0 ∧ L (ψ ⊗ₜ e) = c ψ • ψ ⊗ₜ ψ := by
  rintro ⟨L, c, hL⟩
  obtain ⟨u, v, hu, hv, huv⟩ := exists_orthonormal_pair h
  exact not_clone_core (fun x y => x ⊗ₜ[ℂ] y) (fun _ _ _ _ => TensorProduct.inner_tmul ℂ _ _ _ _)
    (fun _ _ _ => TensorProduct.add_tmul _ _ _) (fun c x y => (TensorProduct.smul_tmul' c x y).symm)
    hu hv huv e L c (fun ψ hψ => (hL ψ hψ).1) fun ψ hψ => (hL ψ hψ).2

/-- **No-cloning** [Wootters, Zurek][WoottersZurek1982], [Dieks][Dieks1982], ancilla-free: if
`dim E ≥ 2`, no linear map of `E ⊗ E` (in particular no unitary) maps `ψ ⊗ e` to `ψ ⊗ ψ` for every
unit state `ψ`. -/
theorem not_exists_linearMap_clone (h : 1 < Module.rank ℂ E) (e : E) :
    ¬ ∃ L : E ⊗[ℂ] E →ₗ[ℂ] E ⊗[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → L (ψ ⊗ₜ e) = ψ ⊗ₜ ψ := fun ⟨L, hL⟩ =>
  not_exists_linearMap_clone_smul h e
    ⟨L, fun _ => 1, fun ψ hψ => ⟨one_ne_zero, by rw [one_smul, hL ψ hψ]⟩⟩

end TensorProduct

/-! ### Coordinates -/

section Coordinates

variable {ι α : Type*} [Fintype ι] [Fintype α]

private lemma exists_isometry_of_unitary {κ : Type*} [Fintype κ] [DecidableEq κ]
    {U : Matrix κ κ ℂ} (hU : U ∈ unitaryGroup κ ℂ) :
    ∃ V : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ κ,
      ∀ x y, U *ᵥ x.ofLp = y.ofLp → V x = y :=
  ⟨(Unitary.linearIsometryEquiv
      ⟨toEuclideanCLM (n := κ) (𝕜 := ℂ) U, Unitary.map_mem _ hU⟩).toLinearIsometry,
    fun _ _ h => WithLp.ofLp_injective 2 h⟩

private lemma exists_orthonormal_ket (ι : Type*) [Fintype ι] [Nontrivial ι] :
    ∃ u v : EuclideanSpace ℂ ι, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪u, v⟫_ℂ = 0 := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  refine ⟨ket i, ket j, norm_ket i, norm_ket j, ?_⟩
  rw [ket, EuclideanSpace.inner_single_left]
  simp [hij]

/-- **No-cloning, inner-product form**, ancilla-free, for a unitary matrix `U` on `ℂ^{ι × ι}`: if
`U` copies two unit states `ψ` and `φ` of `ℂ^ι` onto a unit blank state `e`, then `ψ` and `φ` are
orthogonal or equal. -/
theorem inner_eq_zero_or_eq_of_unitary_clone [DecidableEq ι] {U : Matrix (ι × ι) (ι × ι) ℂ}
    (hU : U ∈ unitaryGroup (ι × ι) ℂ) {ψ φ e : EuclideanSpace ℂ ι}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (he : ‖e‖ = 1)
    (hUψ : U *ᵥ (prodState ψ e).ofLp = (prodState ψ ψ).ofLp)
    (hUφ : U *ᵥ (prodState φ e).ofLp = (prodState φ φ).ofLp) : ⟪ψ, φ⟫_ℂ = 0 ∨ ψ = φ := by
  obtain ⟨V, hV⟩ := exists_isometry_of_unitary hU
  exact inner_eq_zero_or_eq_of_clone_core prodState (fun x y x' y' => inner_prodState x x' y y')
    V hψ hφ he (hV _ _ hUψ) (hV _ _ hUφ)

/-- **Apparatus-assisted no-cloning, inner-product form** in coordinates
[Wootters, Zurek][WoottersZurek1982]: if a unitary matrix `U` on `ℂ^{(ι × ι) × α}` copies two unit
states `ψ` and `φ` of `ℂ^ι` onto a unit blank state `e` starting from a unit apparatus state `a₀`,
leaving the apparatus in states `aψ` and `aφ`, then `ψ` and `φ` are orthogonal or equal up to a
unit global phase. -/
theorem inner_eq_zero_or_exists_smul_of_unitary_clone_apparatus [DecidableEq ι] [DecidableEq α]
    {U : Matrix ((ι × ι) × α) ((ι × ι) × α) ℂ} (hU : U ∈ unitaryGroup ((ι × ι) × α) ℂ)
    {ψ φ e : EuclideanSpace ℂ ι} {a₀ aψ aφ : EuclideanSpace ℂ α}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (he : ‖e‖ = 1) (ha₀ : ‖a₀‖ = 1)
    (hUψ : U *ᵥ (prodState (prodState ψ e) a₀).ofLp = (prodState (prodState ψ ψ) aψ).ofLp)
    (hUφ : U *ᵥ (prodState (prodState φ e) a₀).ofLp = (prodState (prodState φ φ) aφ).ofLp) :
    ⟪ψ, φ⟫_ℂ = 0 ∨ ∃ c : ℂ, ‖c‖ = 1 ∧ φ = c • ψ := by
  obtain ⟨V, hV⟩ := exists_isometry_of_unitary hU
  exact inner_eq_zero_or_exists_smul_of_clone_apparatus_core
    (fun x y a => prodState (prodState x y) a)
    (fun _ _ _ _ _ _ => by rw [inner_prodState, inner_prodState])
    V hψ hφ he ha₀ (hV _ _ hUψ) (hV _ _ hUφ)

/-- **Wootters–Zurek no-cloning with an apparatus** in coordinates
[Wootters, Zurek][WoottersZurek1982]: if `|ι| ≥ 2`, no matrix (in particular no unitary) `U` on
`ℂ^{(ι × ι) × α}` maps `(ψ ⊗ e) ⊗ a₀` to `(ψ ⊗ ψ) ⊗ a_ψ` with `a_ψ ≠ 0` for every unit state `ψ`
of `ℂ^ι`, whatever the blank state `e` and ready apparatus state `a₀`. -/
theorem not_exists_matrix_clone_apparatus [Nontrivial ι] (e : EuclideanSpace ℂ ι)
    (a₀ : EuclideanSpace ℂ α) :
    ¬ ∃ U : Matrix ((ι × ι) × α) ((ι × ι) × α) ℂ,
      ∀ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 →
        ∃ aψ : EuclideanSpace ℂ α, aψ ≠ 0 ∧
          U *ᵥ (prodState (prodState ψ e) a₀).ofLp = (prodState (prodState ψ ψ) aψ).ofLp := by
  classical
  rintro ⟨U, hU⟩
  obtain ⟨u, v, hu, hv, huv⟩ := exists_orthonormal_ket ι
  exact not_clone_apparatus_core (fun x y a => prodState (prodState x y) a)
    (fun _ _ _ _ _ _ => by rw [inner_prodState, inner_prodState])
    (fun _ _ _ _ => by
      ext ⟨⟨p, q⟩, r⟩
      simp [add_mul])
    (fun _ _ _ _ => by
      ext ⟨⟨p, q⟩, r⟩
      simp [mul_assoc])
    hu hv huv e a₀ (Matrix.toEuclideanLin U) fun ψ hψ =>
      let ⟨aψ, haψ, h⟩ := hU ψ hψ
      ⟨aψ, haψ, WithLp.ofLp_injective 2 h⟩

/-- **No-cloning** in coordinates, ancilla-free and up to nonzero factors: if `|ι| ≥ 2`, no
matrix `U` on `ℂ^{ι × ι}` maps `ψ ⊗ e` to a nonzero multiple of `ψ ⊗ ψ` for every unit state `ψ`
of `ℂ^ι`, whatever the blank state `e`. -/
theorem not_exists_matrix_clone_smul [Nontrivial ι] (e : EuclideanSpace ℂ ι) :
    ¬ ∃ (U : Matrix (ι × ι) (ι × ι) ℂ) (c : EuclideanSpace ℂ ι → ℂ),
      ∀ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 →
        c ψ ≠ 0 ∧ U *ᵥ (prodState ψ e).ofLp = c ψ • (prodState ψ ψ).ofLp := by
  classical
  rintro ⟨U, c, hU⟩
  obtain ⟨u, v, hu, hv, huv⟩ := exists_orthonormal_ket ι
  -- The linearity of `prodState` is restated at the `EuclideanSpace` instances; passing
  -- `prodState_add_left` directly makes the elaborator unify the `PiLp` and `WithLp` additions.
  exact not_clone_core prodState (fun x y x' y' => inner_prodState x x' y y')
    (fun _ _ _ => by
      ext p
      simp [add_mul])
    (fun _ _ _ => by
      ext p
      simp [mul_assoc])
    hu hv huv e (Matrix.toEuclideanLin U) c (fun ψ hψ => (hU ψ hψ).1) fun ψ hψ =>
      WithLp.ofLp_injective 2 ((hU ψ hψ).2.trans (WithLp.ofLp_smul ..).symm)

/-- **No-cloning** in coordinates [Wootters, Zurek][WoottersZurek1982], [Dieks][Dieks1982];
[de Wolf][deWolf2019], Chapter 1, Exercise 12, ancilla-free: if `|ι| ≥ 2`, no matrix (in
particular no unitary) `U` on `ℂ^{ι × ι}` maps `ψ ⊗ e` to `ψ ⊗ ψ` for every unit state `ψ` of
`ℂ^ι`. -/
theorem not_exists_matrix_clone [Nontrivial ι] (e : EuclideanSpace ℂ ι) :
    ¬ ∃ U : Matrix (ι × ι) (ι × ι) ℂ, ∀ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 →
      U *ᵥ (prodState ψ e).ofLp = (prodState ψ ψ).ofLp := fun ⟨U, hU⟩ =>
  not_exists_matrix_clone_smul e
    ⟨U, fun _ => 1, fun ψ hψ => ⟨one_ne_zero, by rw [one_smul, hU ψ hψ]⟩⟩

end Coordinates

end Cslib.Quantum
