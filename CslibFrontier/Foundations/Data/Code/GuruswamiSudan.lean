/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import CslibFrontier.Foundations.Data.Code.SudanInterpolant
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Radical.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Positivity

/-!
# Guruswami–Sudan list decoding for Reed–Solomon codes

Let `w : ι → F` be a received word on `n = |ι|` distinct evaluation points `α : ι → F` over an
arbitrary field `F` (of any characteristic). The Guruswami–Sudan list decoder
[GuruswamiSudan1999], [GuruswamiRudraSudan2019, Chapter 19] strengthens Sudan's decoder
(`Cslib.Code.sudan`) by requiring the bivariate interpolant `Q(X, Y) ∈ F[X][Y]` of
`(1, d)`-weighted degree at most `D` to vanish to multiplicity at least `m` at every point
`(α i, w i)`.

Multiplicity-`m` vanishing at `(x, y)` is defined via the shifted polynomial
`Q(X + x, Y + y)` (`Cslib.Code.GuruswamiSudan.shift`): `Q` vanishes to order at least `m` at
`(x, y)` (`Cslib.Code.GuruswamiSudan.VanishesToOrder`) when all coefficients of `X ^ i * Y ^ j`
with `i + j < m` in `shift x y Q` are zero, equivalently when all bivariate Hasse derivatives
`Cslib.Code.GuruswamiSudan.hasseDerivBiv i j Q` with `i + j < m` vanish at `(x, y)`
(`Cslib.Code.GuruswamiSudan.vanishesToOrder_iff_hasseDerivBiv`). Because Hasse derivatives avoid
division by factorials, this formulation works over arbitrary commutative rings and fields of any
characteristic, commutes with arbitrary ring homomorphisms (`Cslib.Code.GuruswamiSudan.map_shift`,
`Cslib.Code.GuruswamiSudan.VanishesToOrder.map`), and satisfies the root-multiplicity divisibility
property `(X - C x) ^ m ∣ Q.eval P` whenever `P.eval x = y`
(`Cslib.Code.GuruswamiSudan.VanishesToOrder.X_sub_C_pow_dvd_eval`).

Each point imposes `m * (m + 1) / 2` homogeneous linear equations on the coefficients of `Q`
(`Cslib.Code.GuruswamiSudan.card_multPairs`), so a nonzero interpolant exists whenever
`n * (m * (m + 1) / 2) < #(Sudan.monomials d D)` (`Cslib.Code.GuruswamiSudan.exists_isInterpolant`),
and in particular when `1 ≤ d` and `n * d * m * (m + 1) < (D + 1) * (D + 2)`
(`Cslib.Code.GuruswamiSudan.exists_isInterpolant_of_lt`). By Gaussian elimination
(`Cslib.LinearAlgebra.kernelVec`), `Cslib.Code.GuruswamiSudan.interpolant` constructs an explicit
interpolant of least `Y`-degree (`Cslib.Code.GuruswamiSudan.isInterpolant_interpolant`,
`Cslib.Code.GuruswamiSudan.natDegree_interpolant_le`). If `P` has `natDegree ≤ d` and agrees with
`w` at more than `D / m` points (`D < m * #{i | P.eval (α i) = w i}`), then `Q.eval P = 0` and
`Y - C P ∣ Q` (`Cslib.Code.GuruswamiSudan.IsInterpolant.eval_eq_zero`,
`Cslib.Code.GuruswamiSudan.IsInterpolant.X_sub_C_dvd`).

The module also provides weighted-degree additivity (`Cslib.Code.GuruswamiSudan.weightedDegree_mul`)
and primitive, square-free, and irreducible factor-refinement helpers over arbitrary fields
(`Cslib.Code.GuruswamiSudan.eval_radical_primPart_eq_zero_iff`,
`Cslib.Code.GuruswamiSudan.exists_eq_C_mul_prod_irreducible`,
`Cslib.Code.GuruswamiSudan.IsInterpolant.rootMultiplicity_le_of_min`) used in proximity-gap
analyses over function fields.

For Reed–Solomon codes of dimension `k ≥ 2`, `Cslib.Code.guruswamiSudan` achieves list decoding up
to the full Johnson radius `n * (k - 1) < (n - e) ^ 2`
(`Cslib.Code.mem_guruswamiSudan_johnson_iff`), and asymptotically up to `δ = 1 - √ρ - ε` for every
`ε > 0` with multiplicity depending only on `ε` (`Cslib.Code.exists_guruswamiSudan_of_eps`). As in
`Cslib.Code.sudan`, roots in `F[X][Y]` are taken noncomputably via `Polynomial.roots` and no
running time is formalized here.

## Main definitions

* `Cslib.Code.GuruswamiSudan.shift`: the shifted bivariate polynomial `Q(X + x, Y + y)`.
* `Cslib.Code.GuruswamiSudan.hasseDerivX`, `Cslib.Code.GuruswamiSudan.hasseDerivBiv`: bivariate
  Hasse derivatives in `X` and in `(X, Y)`.
* `Cslib.Code.GuruswamiSudan.VanishesToOrder`: multiplicity-`m` vanishing at `(x, y)`.
* `Cslib.Code.GuruswamiSudan.weightedDegree`: the `(1, d)`-weighted degree of a bivariate
  polynomial.
* `Cslib.Code.GuruswamiSudan.multPairs`: the `m * (m + 1) / 2` pairs `(r, s)` with `r + s < m`.
* `Cslib.Code.GuruswamiSudan.IsWeightedInterpolant`: per-point multiplicity interpolants for
  arbitrary multiplicity profiles `mult : ι → ℕ`.
* `Cslib.Code.GuruswamiSudan.IsInterpolant`: uniform multiplicity-`m` Guruswami–Sudan interpolants.
* `Cslib.Code.GuruswamiSudan.interpolant`: an explicit multiplicity-`m` interpolant of least
  `Y`-degree.
* `Cslib.Code.guruswamiSudan`: the Guruswami–Sudan list decoder for Reed–Solomon codes.

## Main results

* `Cslib.Code.GuruswamiSudan.coeff_coeff_shift_eq_evalEval_hasseDerivBiv`,
  `Cslib.Code.GuruswamiSudan.vanishesToOrder_iff_hasseDerivBiv`: bivariate Taylor / Hasse
  derivative characterization of multiplicity vanishing.
* `Cslib.Code.GuruswamiSudan.map_shift`, `Cslib.Code.GuruswamiSudan.VanishesToOrder.map`:
  compatibility of multiplicity vanishing with arbitrary ring homomorphisms.
* `Cslib.Code.GuruswamiSudan.VanishesToOrder.X_sub_C_pow_dvd_eval`: multiplicity-`m` vanishing at
  `(x, P(x))` implies `(X - C x) ^ m ∣ Q.eval P`.
* `Cslib.Code.GuruswamiSudan.weightedDegree_mul`,
  `Cslib.Code.GuruswamiSudan.weightedDegreeLE_of_dvd`: additivity and divisibility monotonicity of
  `(1, d)`-weighted degree.
* `Cslib.Code.GuruswamiSudan.eval_radical_primPart_eq_zero_iff`,
  `Cslib.Code.GuruswamiSudan.exists_eq_C_mul_prod_irreducible`,
  `Cslib.Code.GuruswamiSudan.IsInterpolant.rootMultiplicity_le_of_min`: square-free, irreducible,
  and least-`Y`-degree factor refinement.
* `Cslib.Code.GuruswamiSudan.exists_isWeightedInterpolant`,
  `Cslib.Code.GuruswamiSudan.exists_isWeightedInterpolant_min_natDegree`,
  `Cslib.Code.GuruswamiSudan.IsWeightedInterpolant.eval_eq_zero`: per-point multiplicity
  interpolation and root containment.
* `Cslib.Code.GuruswamiSudan.exists_isInterpolant`,
  `Cslib.Code.GuruswamiSudan.exists_isInterpolant_of_lt`,
  `Cslib.Code.GuruswamiSudan.isInterpolant_interpolant`,
  `Cslib.Code.GuruswamiSudan.natDegree_interpolant_le`: existence and least-`Y`-degree
  construction of multiplicity-`m` interpolants.
* `Cslib.Code.GuruswamiSudan.IsInterpolant.eval_eq_zero`,
  `Cslib.Code.GuruswamiSudan.IsInterpolant.X_sub_C_dvd`: multiplicity root-divisibility.
* `Cslib.Code.mem_guruswamiSudan_iff`, `Cslib.Code.mem_guruswamiSudan_iff_of_lt`,
  `Cslib.Code.card_guruswamiSudan_le_natDegree`, `Cslib.Code.card_guruswamiSudan_le`,
  `Cslib.Code.card_guruswamiSudan_mul_le`,
  `Cslib.Code.exists_mem_guruswamiSudan_of_mem_reedSolomon`: completeness, soundness, and list-size
  bounds of the Guruswami–Sudan decoder.
* `Cslib.Code.mem_guruswamiSudan_johnson_iff`,
  `Cslib.Code.exists_guruswamiSudan_of_eps`: list decoding of Reed–Solomon codes up to the full
  Johnson radius `δ < 1 - √ρ`.

## References

* [V. Guruswami, M. Sudan, *Improved Decoding of Reed–Solomon and Algebraic-Geometry Codes*]
  [GuruswamiSudan1999]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*]
  [GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code.GuruswamiSudan

open Finset Polynomial Cslib.LinearAlgebra
open scoped Polynomial.Bivariate

/-! ### Bivariate shift and Hasse derivatives -/

section Shift

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The bivariate Taylor shift `Q(X + x, Y + y)` as a ring homomorphism `R[X][Y] →+* R[X][Y]`. -/
noncomputable def shift (x y : R) : R[X][Y] →+* R[X][Y] :=
  (taylorAlgHom (C y) : R[X][Y] →+* R[X][Y]).comp
    (Polynomial.mapRingHom (taylorAlgHom x : R[X] →+* R[X]))

/-- Unfolding `shift x y Q` into nested univariate `Polynomial.taylor` shifts. -/
theorem shift_apply (x y : R) (Q : R[X][Y]) :
    shift x y Q = taylor (C y) (Q.map (taylorAlgHom x : R[X] →+* R[X])) :=
  rfl

/-- Applying `taylor x` to `Q(X, y)` equals `(Q.map (taylorAlgHom x)).eval (C y)`. -/
private theorem map_taylorAlgHom_eval_C (x y : R) (Q : R[X][Y]) :
    (Q.map (taylorAlgHom x : R[X] →+* R[X])).eval (C y) = taylor x (Q.eval (C y)) := by
  have hCy : C y = (taylorAlgHom x : R[X] →+* R[X]) (C y) := (taylor_C x y).symm
  conv_lhs => rw [hCy, eval_map, eval₂_hom]
  rfl

/-- The constant term of `shift x y Q` is `Q.evalEval x y`. -/
@[simp]
theorem coeff_coeff_shift_zero (x y : R) (Q : R[X][Y]) :
    ((shift x y Q).coeff 0).coeff 0 = Q.evalEval x y := by
  rw [shift_apply, taylor_coeff_zero, map_taylorAlgHom_eval_C, taylor_coeff_zero]

/-- The `(r, s)` coefficient of `shift x y (c * X ^ a * Y ^ b)` is
`(a.choose r) * (b.choose s) * c * x ^ (a - r) * y ^ (b - s)`. -/
theorem coeff_coeff_shift_monomial (x y : R) (a b r s : ℕ) (c : R) :
    ((shift x y (monomial b (monomial a c))).coeff s).coeff r =
      (a.choose r : R) * (b.choose s : R) * c * x ^ (a - r) * y ^ (b - s) := by
  rw [shift_apply, map_monomial, taylor_coeff, hasseDeriv_monomial, eval_monomial]
  have hcast :
      (↑(b.choose s) * (taylorAlgHom x : R[X] →+* R[X]) (monomial a c)) * C y ^ (b - s) =
        taylor x (monomial a c) * C ((b.choose s : R) * y ^ (b - s)) := by
    rw [C_mul, C_pow, C_eq_natCast]
    change (↑(b.choose s) * taylor x (monomial a c)) * C y ^ (b - s) = _
    ring
  rw [hcast, coeff_mul_C, taylor_coeff, hasseDeriv_monomial, eval_monomial]
  ring

/-- The `(r, s)` coefficient of `shift x y` on `Sudan.bivariateOf M c`. -/
theorem coeff_coeff_shift_bivariateOf {F : Type*} [Field F] (M : Finset (ℕ × ℕ))
    (c : ℕ × ℕ → F) (x y : F) (r s : ℕ) :
    ((shift x y (Sudan.bivariateOf M c)).coeff s).coeff r =
      ∑ m ∈ M, c m * ((m.1.choose r : F) * (m.2.choose s : F) *
        x ^ (m.1 - r) * y ^ (m.2 - s)) := by
  rw [Sudan.bivariateOf, map_sum, finsetSum_coeff, finsetSum_coeff]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_coeff_shift_monomial]
  ring

/-- The `i`-th Hasse derivative in the `X`-variable of a bivariate polynomial `Q : R[X][Y]`. -/
noncomputable def hasseDerivX (i : ℕ) (Q : R[X][Y]) : R[X][Y] :=
  Q.sum fun b p => monomial b (hasseDeriv i p)

/-- The `b`-th `Y`-coefficient of `hasseDerivX i Q` is `hasseDeriv i (Q.coeff b)`. -/
@[simp]
theorem coeff_hasseDerivX (i : ℕ) (Q : R[X][Y]) (b : ℕ) :
    (hasseDerivX i Q).coeff b = hasseDeriv i (Q.coeff b) := by
  classical
  rw [hasseDerivX, coeff_sum, sum_def]
  by_cases hb : b ∈ Q.support
  · rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hne
      simp [coeff_monomial, hne]
    · intro h
      exact absurd hb h
  · rw [notMem_support_iff.1 hb, map_zero]
    refine Finset.sum_eq_zero fun b' hb' => ?_
    have hne : b' ≠ b := fun h => hb (h ▸ hb')
    simp [coeff_monomial, hne]

/-- `hasseDerivX i` on `0` is `0`. -/
@[simp]
theorem hasseDerivX_zero (i : ℕ) : hasseDerivX i (0 : R[X][Y]) = 0 := by
  ext b a
  simp

/-- `hasseDerivX i` is additive. -/
theorem hasseDerivX_add (i : ℕ) (P Q : R[X][Y]) :
    hasseDerivX i (P + Q) = hasseDerivX i P + hasseDerivX i Q := by
  ext b a
  simp

/-- `hasseDerivX i` on a monomial in `Y`. -/
@[simp]
theorem hasseDerivX_monomial (i b : ℕ) (p : R[X]) :
    hasseDerivX i (monomial b p) = monomial b (hasseDeriv i p) := by
  ext b' a
  simp only [coeff_hasseDerivX, coeff_monomial]
  split_ifs <;> simp

/-- Evaluating `hasseDerivX i Q` at `Y = C y` commutes with `hasseDeriv i`. -/
theorem eval_C_hasseDerivX (i : ℕ) (Q : R[X][Y]) (y : R) :
    (hasseDerivX i Q).eval (C y) = hasseDeriv i (Q.eval (C y)) := by
  induction Q using Polynomial.induction_on' with
  | add P₁ P₂ h₁ h₂ =>
    rw [hasseDerivX_add, eval_add, eval_add, map_add, h₁, h₂]
  | monomial b p =>
    rw [hasseDerivX_monomial, eval_monomial, eval_monomial, ← C_pow, mul_comm p,
      ← smul_eq_C_mul, map_smul, smul_eq_C_mul, mul_comm]

/-- The `(i, j)`-th bivariate Hasse derivative of `Q : R[X][Y]`: `hasseDeriv i` in `X` and
`hasseDeriv j` in `Y`. -/
noncomputable def hasseDerivBiv (i j : ℕ) (Q : R[X][Y]) : R[X][Y] :=
  hasseDerivX i (hasseDeriv j Q)

/-- The `(a, b)` coefficient of `hasseDerivBiv i j Q`. -/
theorem coeff_coeff_hasseDerivBiv (i j a b : ℕ) (Q : R[X][Y]) :
    ((hasseDerivBiv i j Q).coeff b).coeff a =
      ((a + i).choose i : R) * (((b + j).choose j : R) * (Q.coeff (b + j)).coeff (a + i)) := by
  rw [hasseDerivBiv, coeff_hasseDerivX, hasseDeriv_coeff, hasseDeriv_coeff]
  rw [← C_eq_natCast, coeff_C_mul]

/-- **Bivariate Taylor / Hasse derivative identity.** The coefficient of `X ^ i * Y ^ j` in
`Q(X + x, Y + y)` is the value of the `(i, j)`-th bivariate Hasse derivative of `Q` at `(x, y)`. -/
theorem coeff_coeff_shift_eq_evalEval_hasseDerivBiv (x y : R) (Q : R[X][Y]) (i j : ℕ) :
    ((shift x y Q).coeff j).coeff i = (hasseDerivBiv i j Q).evalEval x y := by
  rw [shift_apply, taylor_coeff, hasseDeriv_map, map_taylorAlgHom_eval_C, taylor_coeff,
    ← eval_C_hasseDerivX]
  rfl

/-- **Base change for bivariate shift.** Mapping the coefficients of `Q` through any ring
homomorphism `φ : R →+* S` commutes with `shift`. -/
theorem map_shift (φ : R →+* S) (x y : R) (Q : R[X][Y]) :
    shift (φ x) (φ y) (Q.map (Polynomial.mapRingHom φ)) =
      (shift x y Q).map (Polynomial.mapRingHom φ) := by
  rw [shift_apply, shift_apply, Polynomial.map_map]
  have hcomp :
      (taylorAlgHom (φ x) : S[X] →+* S[X]).comp (Polynomial.mapRingHom φ) =
        (Polynomial.mapRingHom φ).comp (taylorAlgHom x : R[X] →+* R[X]) := by
    ext p
    · simp
    · simp
  rw [hcomp, ← Polynomial.map_map]
  have hCy : C (φ y) = Polynomial.mapRingHom φ (C y) := by simp
  rw [hCy, ← Polynomial.map_taylor]

end Shift

/-! ### Multiplicity-`m` vanishing -/

section Vanishing

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- `Q : R[X][Y]` *vanishes to multiplicity (order) at least `m`* at `(x, y)` if every monomial
`X ^ i * Y ^ j` with `i + j < m` has zero coefficient in `Q(X + x, Y + y)`. -/
def VanishesToOrder (m : ℕ) (x y : R) (Q : R[X][Y]) : Prop :=
  ∀ i j, i + j < m → ((shift x y Q).coeff j).coeff i = 0

/-- Multiplicity-`m` vanishing is equivalent to the vanishing of all bivariate Hasse derivatives
of total order less than `m` at `(x, y)`. -/
theorem vanishesToOrder_iff_hasseDerivBiv (m : ℕ) (x y : R) (Q : R[X][Y]) :
    VanishesToOrder m x y Q ↔ ∀ i j, i + j < m → (hasseDerivBiv i j Q).evalEval x y = 0 := by
  simp only [VanishesToOrder, coeff_coeff_shift_eq_evalEval_hasseDerivBiv]

/-- Every polynomial vanishes to order `0`. -/
@[simp]
theorem vanishesToOrder_zero (x y : R) (Q : R[X][Y]) : VanishesToOrder 0 x y Q := by
  intro i j h
  omega

/-- Vanishing to order `1` at `(x, y)` is ordinary vanishing `Q(x, y) = 0`. -/
theorem vanishesToOrder_one_iff (x y : R) (Q : R[X][Y]) :
    VanishesToOrder 1 x y Q ↔ Q.evalEval x y = 0 := by
  constructor
  · intro h
    simpa using h 0 0 (by omega)
  · intro h i j hij
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi; subst hj
    simpa using h

/-- Monotonicity of vanishing order. -/
theorem VanishesToOrder.mono {m m' : ℕ} {x y : R} {Q : R[X][Y]}
    (h : VanishesToOrder m x y Q) (hm : m' ≤ m) : VanishesToOrder m' x y Q :=
  fun i j hij => h i j (hij.trans_le hm)

/-- The zero polynomial vanishes to every order. -/
@[simp]
theorem vanishesToOrder_of_zero (m : ℕ) (x y : R) : VanishesToOrder m x y (0 : R[X][Y]) := by
  intro i j _
  simp

/-- Vanishing to order `m` is closed under addition. -/
theorem VanishesToOrder.add {m : ℕ} {x y : R} {P Q : R[X][Y]}
    (hP : VanishesToOrder m x y P) (hQ : VanishesToOrder m x y Q) :
    VanishesToOrder m x y (P + Q) := by
  intro i j hij
  rw [map_add, coeff_add, coeff_add, hP i j hij, hQ i j hij, add_zero]

/-- Vanishing to order `m` is preserved by any ring homomorphism `φ : R →+* S`. -/
theorem VanishesToOrder.map (φ : R →+* S) {m : ℕ} {x y : R} {Q : R[X][Y]}
    (hQ : VanishesToOrder m x y Q) :
    VanishesToOrder m (φ x) (φ y) (Q.map (Polynomial.mapRingHom φ)) := by
  intro i j hij
  rw [map_shift, coeff_map, Polynomial.coe_mapRingHom, coeff_map, hQ i j hij, map_zero]

/-- Vanishing to order `m` reflects along any injective ring homomorphism `φ : R →+* S`. -/
theorem VanishesToOrder.of_map_injective {φ : R →+* S} (hφ : Function.Injective φ)
    {m : ℕ} {x y : R} {Q : R[X][Y]}
    (hQ : VanishesToOrder m (φ x) (φ y) (Q.map (Polynomial.mapRingHom φ))) :
    VanishesToOrder m x y Q := by
  intro i j hij
  have h := hQ i j hij
  rw [map_shift, coeff_map, Polynomial.coe_mapRingHom, coeff_map] at h
  exact hφ (h.trans (map_zero φ).symm)

/-- **Product rule for vanishing order.** If `Q₁` vanishes to order `m₁` and `Q₂` to order `m₂`,
then `Q₁ * Q₂` vanishes to order `m₁ + m₂`. -/
theorem VanishesToOrder.mul {m₁ m₂ : ℕ} {x y : R} {Q₁ Q₂ : R[X][Y]}
    (h₁ : VanishesToOrder m₁ x y Q₁) (h₂ : VanishesToOrder m₂ x y Q₂) :
    VanishesToOrder (m₁ + m₂) x y (Q₁ * Q₂) := by
  intro i j hij
  rw [map_mul, coeff_mul, finsetSum_coeff]
  refine sum_eq_zero fun ab hab => ?_
  rw [mem_antidiagonal] at hab
  rw [coeff_mul]
  refine sum_eq_zero fun cd hcd => ?_
  rw [mem_antidiagonal] at hcd
  by_cases hlt : cd.1 + ab.1 < m₁
  · rw [h₁ cd.1 ab.1 hlt, zero_mul]
  · have hlt₂ : cd.2 + ab.2 < m₂ := by omega
    rw [h₂ cd.2 ab.2 hlt₂, mul_zero]

/-- Power rule for vanishing order. -/
theorem VanishesToOrder.pow {m : ℕ} {x y : R} {Q : R[X][Y]}
    (hQ : VanishesToOrder m x y Q) (r : ℕ) : VanishesToOrder (r * m) x y (Q ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hQ

/-- If `Q₁(x, y) ≠ 0` and `Q₁ * Q₂` vanishes to order `m` at `(x, y)` over a domain, then `Q₂`
already vanishes to order `m` at `(x, y)`. -/
theorem VanishesToOrder.of_mul_left_of_evalEval_ne_zero [NoZeroDivisors R] {m : ℕ} {x y : R}
    {Q₁ Q₂ : R[X][Y]} (h₁ : Q₁.evalEval x y ≠ 0) (h : VanishesToOrder m x y (Q₁ * Q₂)) :
    VanishesToOrder m x y Q₂ := by
  have hmain : ∀ k < m, ∀ i j, i + j = k → ((shift x y Q₂).coeff j).coeff i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hkm i j hij
      have h0 := h i j (hij ▸ hkm)
      rw [map_mul, coeff_mul, finsetSum_coeff] at h0
      have hsum :
          ∑ ab ∈ antidiagonal j, ((shift x y Q₁).coeff ab.1 * (shift x y Q₂).coeff ab.2).coeff i =
            ((shift x y Q₁).coeff 0).coeff 0 * ((shift x y Q₂).coeff j).coeff i := by
        rw [Finset.sum_eq_single (0, j)]
        · rw [coeff_mul, Finset.sum_eq_single (0, i)]
          · intro cd hcd hne
            rw [mem_antidiagonal] at hcd
            have hlt : cd.2 + j < k := by
              have hc1 : cd.1 ≠ 0 := by
                intro hzero
                exact hne (Prod.ext hzero (by omega))
              omega
            rw [ih (cd.2 + j) hlt (hlt.trans hkm) cd.2 j rfl, mul_zero]
          · intro hmem
            exact absurd (mem_antidiagonal.2 (zero_add i)) hmem
        · intro ab hab hne
          rw [mem_antidiagonal] at hab
          rw [coeff_mul]
          refine sum_eq_zero fun cd hcd => ?_
          rw [mem_antidiagonal] at hcd
          have hlt : cd.2 + ab.2 < k := by
            have ha1 : ab.1 ≠ 0 := by
              intro hzero
              exact hne (Prod.ext hzero (by omega))
            omega
          rw [ih (cd.2 + ab.2) hlt (hlt.trans hkm) cd.2 ab.2 rfl, mul_zero]
        · intro hmem
          exact absurd (mem_antidiagonal.2 (zero_add j)) hmem
      rw [hsum, coeff_coeff_shift_zero] at h0
      exact (mul_eq_zero.1 h0).resolve_left h₁
  exact fun i j hij => hmain (i + j) hij i j rfl

/-- Over a commutative ring, if `P(x) = y` then `Y - C P` vanishes to order `1` at `(x, y)`. -/
theorem vanishesToOrder_one_X_sub_C {R : Type*} [CommRing R] {x y : R} {P : R[X]}
    (hP : P.eval x = y) : VanishesToOrder 1 x y (Y - C P) := by
  rw [vanishesToOrder_one_iff, evalEval_sub, evalEval_X, evalEval_C, hP, sub_self]

/-- **Multiplicity root divisibility.** Over any commutative ring `R`, if `Q : R[X][Y]` vanishes to
multiplicity at least `m` at `(x, P(x))`, then `(X - C x) ^ m` divides `Q.eval P` in `R[X]`. -/
theorem VanishesToOrder.X_sub_C_pow_dvd_eval {R : Type*} [CommRing R] {m : ℕ} {x y : R}
    {Q : R[X][Y]} (hQ : VanishesToOrder m x y Q) {P : R[X]} (hP : P.eval x = y) :
    (X - C x) ^ m ∣ Q.eval P := by
  -- Write `P(X + x) = C y + X * R`.
  obtain ⟨R₀, hR₀⟩ : X ∣ taylor x P - C y := by
    rw [← pow_one (X : R[X]), X_pow_dvd_iff]
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [coeff_sub, taylor_coeff_zero, coeff_C_zero, hP, sub_self]
  have hPR : taylor x P = X * R₀ + C y := by
    rw [← hR₀]
    ring
  -- Express `taylor x (Q.eval P)` as `(shift x y Q).eval (X * R₀)`.
  have hshift_eval : taylor x (Q.eval P) = (shift x y Q).eval (X * R₀) := by
    have h1 : taylor x (Q.eval P) =
        (Q.map (taylorAlgHom x : R[X] →+* R[X])).eval (taylor x P) := by
      change (taylorAlgHom x : R[X] →+* R[X]) (Q.eval P) =
        (Q.map (taylorAlgHom x : R[X] →+* R[X])).eval ((taylorAlgHom x : R[X] →+* R[X]) P)
      rw [eval_map, eval₂_hom]
    rw [h1, hPR, shift_apply, taylor_eval]
  -- Every term `(shift x y Q).coeff j * (X * R₀) ^ j` is divisible by `X ^ m`.
  have hdvd_shift : X ^ m ∣ taylor x (Q.eval P) := by
    rw [hshift_eval, eval_eq_sum_range]
    refine Finset.dvd_sum fun j _ => ?_
    rw [mul_pow]
    by_cases hmj : m ≤ j
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmj
      rw [pow_add]
      exact ⟨(shift x y Q).coeff (m + k) * (X ^ k * R₀ ^ (m + k)), by ring⟩
    · have hjlt : j < m := not_le.1 hmj
      have hcoeff : X ^ (m - j) ∣ (shift x y Q).coeff j := by
        rw [X_pow_dvd_iff]
        intro i hi
        exact hQ i j (by omega)
      obtain ⟨T, hT⟩ := hcoeff
      refine ⟨T * R₀ ^ j, ?_⟩
      rw [hT]
      have hpow : (X : R[X]) ^ (m - j) * X ^ j = X ^ m := by
        rw [← pow_add, Nat.sub_add_cancel hjlt.le]
      calc (X ^ (m - j) * T) * (X ^ j * R₀ ^ j) = (X ^ (m - j) * X ^ j) * (T * R₀ ^ j) := by ring
        _ = X ^ m * (T * R₀ ^ j) := by rw [hpow]
  -- Shift back by `-x`.
  obtain ⟨T, hT⟩ := hdvd_shift
  refine ⟨taylor (-x) T, ?_⟩
  have hback : Q.eval P = taylor (-x) (taylor x (Q.eval P)) := by
    rw [taylor_taylor, neg_add_cancel, taylor_zero]
  rw [hback, hT, taylor_mul, taylor_X_pow, C_neg, ← sub_eq_add_neg]

end Vanishing

/-! ### Weighted degree and factorization helpers -/

section WeightedDegree

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The `(1, d)`-weighted degree of a bivariate polynomial `Q : R[X][Y]`: the maximum of `a + d * b`
over all nonzero monomials `X ^ a * Y ^ b` of `Q` (and `0` for `Q = 0`). -/
noncomputable def weightedDegree (d : ℕ) (Q : R[X][Y]) : ℕ :=
  Q.support.sup fun b => (Q.coeff b).support.sup fun a => a + d * b

/-- The weighted degree of `0` is `0`. -/
@[simp]
theorem weightedDegree_zero (d : ℕ) : weightedDegree d (0 : R[X][Y]) = 0 := by
  simp [weightedDegree]

/-- `weightedDegree d Q ≤ D` iff every nonzero coefficient `(Q.coeff b).coeff a` has
`a + d * b ≤ D`. -/
theorem weightedDegree_le_iff {d D : ℕ} {Q : R[X][Y]} :
    weightedDegree d Q ≤ D ↔ ∀ a b, (Q.coeff b).coeff a ≠ 0 → a + d * b ≤ D := by
  simp only [weightedDegree, Finset.sup_le_iff, mem_support_iff]
  constructor
  · intro h a b hab
    have hb : Q.coeff b ≠ 0 := fun h0 => hab (by rw [h0, coeff_zero])
    exact h b hb a hab
  · intro h b _ a hab
    exact h a b hab

/-- Every nonzero monomial `X ^ a * Y ^ b` of `Q` satisfies `a + d * b ≤ weightedDegree d Q`. -/
theorem le_weightedDegree {d a b : ℕ} {Q : R[X][Y]} (hab : (Q.coeff b).coeff a ≠ 0) :
    a + d * b ≤ weightedDegree d Q :=
  weightedDegree_le_iff.1 le_rfl a b hab

/-- Bridge between `weightedDegree d Q ≤ D` and `Sudan.WeightedDegreeLE d D Q`. -/
theorem weightedDegree_le_iff_weightedDegreeLE {F : Type*} [Field F] {d D : ℕ} {Q : F[X][Y]} :
    weightedDegree d Q ≤ D ↔ Sudan.WeightedDegreeLE d D Q :=
  weightedDegree_le_iff

/-- Mapping coefficients through any ring homomorphism `φ : R →+* S` does not increase
`(1, d)`-weighted degree. -/
theorem weightedDegree_map_le (φ : R →+* S) (d : ℕ) (Q : R[X][Y]) :
    weightedDegree d (Q.map (Polynomial.mapRingHom φ)) ≤ weightedDegree d Q := by
  rw [weightedDegree_le_iff]
  intro a b hab
  rw [coeff_map, Polynomial.coe_mapRingHom, coeff_map] at hab
  exact le_weightedDegree fun h0 => hab (by rw [h0, map_zero])

/-- Mapping coefficients through an injective ring homomorphism preserves `(1, d)`-weighted
degree. -/
theorem weightedDegree_map_eq_of_injective {φ : R →+* S} (hφ : Function.Injective φ)
    (d : ℕ) (Q : R[X][Y]) :
    weightedDegree d (Q.map (Polynomial.mapRingHom φ)) = weightedDegree d Q := by
  refine le_antisymm (weightedDegree_map_le φ d Q) (weightedDegree_le_iff.2 fun a b hab => ?_)
  refine le_weightedDegree ?_
  rw [coeff_map, Polynomial.coe_mapRingHom, coeff_map]
  exact fun h0 => hab (hφ (h0.trans (map_zero φ).symm))

/-- Subadditivity of `(1, d)`-weighted degree under multiplication. -/
theorem weightedDegree_mul_le (d : ℕ) (A B : R[X][Y]) :
    weightedDegree d (A * B) ≤ weightedDegree d A + weightedDegree d B := by
  rw [weightedDegree_le_iff]
  intro a b hab
  rw [coeff_mul, finsetSum_coeff] at hab
  obtain ⟨j, hj, hjne⟩ := exists_ne_zero_of_sum_ne_zero hab
  rw [mem_antidiagonal] at hj
  rw [coeff_mul] at hjne
  obtain ⟨i, hi, hine⟩ := exists_ne_zero_of_sum_ne_zero hjne
  rw [mem_antidiagonal] at hi
  have hA : (A.coeff j.1).coeff i.1 ≠ 0 := left_ne_zero_of_mul hine
  have hB : (B.coeff j.2).coeff i.2 ≠ 0 := right_ne_zero_of_mul hine
  have hleA := le_weightedDegree (d := d) hA
  have hleB := le_weightedDegree (d := d) hB
  have hsum : a + d * b = (i.1 + d * j.1) + (i.2 + d * j.2) := by
    rw [← hi, ← hj]
    ring
  omega

/-- Extract a nonzero monomial `(a₀, b₀)` of `Q` maximizing `a + d * b` and, among maximizers,
maximizing `b`. -/
private theorem exists_max_weightedDegree_monomial {d : ℕ} {Q : R[X][Y]} (hQ : Q ≠ 0) :
    ∃ a₀ b₀, (Q.coeff b₀).coeff a₀ ≠ 0 ∧ a₀ + d * b₀ = weightedDegree d Q ∧
      ∀ a b, (Q.coeff b).coeff a ≠ 0 → a + d * b = weightedDegree d Q → b ≤ b₀ := by
  classical
  let supp : Finset (ℕ × ℕ) := Q.support.biUnion fun b => (Q.coeff b).support.image (·, b)
  have hmem : ∀ a b, (Q.coeff b).coeff a ≠ 0 ↔ (a, b) ∈ supp := by
    intro a b
    simp only [supp, mem_biUnion, mem_image, mem_support_iff, Prod.mk.injEq]
    constructor
    · intro hab
      exact ⟨b, fun h => hab (by rw [h, coeff_zero]), a, hab, rfl, rfl⟩
    · rintro ⟨b', -, a', ha', rfl, rfl⟩
      exact ha'
  have hne : supp.Nonempty := by
    obtain ⟨b, hb⟩ : ∃ b, Q.coeff b ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ (Polynomial.ext fun b => by rw [h b, coeff_zero])
    obtain ⟨a, ha⟩ : ∃ a, (Q.coeff b).coeff a ≠ 0 := by
      by_contra h
      push Not at h
      exact hb (Polynomial.ext fun a => by rw [h a, coeff_zero])
    exact ⟨(a, b), (hmem a b).1 ha⟩
  set M₀ := supp.sup' hne fun p => p.1 + d * p.2
  have hM₀_eq : M₀ = weightedDegree d Q := by
    refine le_antisymm ?_ ?_
    · refine sup'_le _ _ fun ⟨a, b⟩ hab => le_weightedDegree ((hmem a b).2 hab)
    · rw [weightedDegree_le_iff]
      intro a b hab
      exact le_sup' (fun p : ℕ × ℕ => p.1 + d * p.2) ((hmem a b).1 hab)
  have htop : (supp.filter fun p => p.1 + d * p.2 = M₀).Nonempty := by
    obtain ⟨p, hp, hpeq⟩ := exists_mem_eq_sup' hne fun p => p.1 + d * p.2
    exact ⟨p, mem_filter.2 ⟨hp, hpeq.symm⟩⟩
  obtain ⟨⟨a₀, b₀⟩, hp₀, hb₀⟩ := exists_mem_eq_sup' htop Prod.snd
  obtain ⟨hp₀, hdeg₀⟩ := mem_filter.1 hp₀
  refine ⟨a₀, b₀, (hmem a₀ b₀).2 hp₀, hdeg₀.trans hM₀_eq, fun a b hab hdeg => ?_⟩
  rw [show b₀ = (a₀, b₀).2 from rfl, ← hb₀]
  exact le_sup' Prod.snd (mem_filter.2 ⟨(hmem a b).1 hab, hdeg.trans hM₀_eq.symm⟩)

/-- **Additivity of `(1, d)`-weighted degree.** Over a domain, if `A ≠ 0` and `B ≠ 0`, then
`weightedDegree d (A * B) = weightedDegree d A + weightedDegree d B`. -/
theorem weightedDegree_mul [NoZeroDivisors R] {d : ℕ} {A B : R[X][Y]}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    weightedDegree d (A * B) = weightedDegree d A + weightedDegree d B := by
  refine le_antisymm (weightedDegree_mul_le d A B) ?_
  obtain ⟨a₁, b₁, ha₁, hdeg₁, hmax₁⟩ := exists_max_weightedDegree_monomial (d := d) hA
  obtain ⟨a₂, b₂, ha₂, hdeg₂, hmax₂⟩ := exists_max_weightedDegree_monomial (d := d) hB
  have hcoeff : ((A * B).coeff (b₁ + b₂)).coeff (a₁ + a₂) =
      (A.coeff b₁).coeff a₁ * (B.coeff b₂).coeff a₂ := by
    rw [coeff_mul, finsetSum_coeff, Finset.sum_eq_single (b₁, b₂)]
    · rw [coeff_mul, Finset.sum_eq_single (a₁, a₂)]
      · intro i hi hne
        rw [mem_antidiagonal] at hi
        by_contra h0
        have h1 := le_weightedDegree (d := d) (left_ne_zero_of_mul h0)
        have h2 := le_weightedDegree (d := d) (right_ne_zero_of_mul h0)
        dsimp only at h1 h2
        have hsum : (i.1 + d * b₁) + (i.2 + d * b₂) = weightedDegree d A + weightedDegree d B := by
          rw [← hdeg₁, ← hdeg₂]
          linarith
        have hi1 : i.1 = a₁ := by linarith
        exact hne (Prod.ext hi1 (by omega))
      · intro hmem
        exact absurd (mem_antidiagonal.2 rfl : (a₁, a₂) ∈ antidiagonal (a₁ + a₂)) hmem
    · intro j hj hne
      rw [mem_antidiagonal] at hj
      rw [coeff_mul]
      refine sum_eq_zero fun i hi => ?_
      rw [mem_antidiagonal] at hi
      by_contra h0
      have h1 := le_weightedDegree (d := d) (left_ne_zero_of_mul h0)
      have h2 := le_weightedDegree (d := d) (right_ne_zero_of_mul h0)
      have hsum : (i.1 + d * j.1) + (i.2 + d * j.2) = weightedDegree d A + weightedDegree d B := by
        rw [← hdeg₁, ← hdeg₂]
        have : i.1 + i.2 = a₁ + a₂ := hi
        have : j.1 + j.2 = b₁ + b₂ := hj
        nlinarith
      have h1eq : i.1 + d * j.1 = weightedDegree d A := by omega
      have h2eq : i.2 + d * j.2 = weightedDegree d B := by omega
      have hj1 : j.1 ≤ b₁ := hmax₁ i.1 j.1 (left_ne_zero_of_mul h0) h1eq
      have hj2 : j.2 ≤ b₂ := hmax₂ i.2 j.2 (right_ne_zero_of_mul h0) h2eq
      have hjeq1 : j.1 = b₁ := by omega
      exact hne (Prod.ext hjeq1 (by omega))
    · intro hmem
      exact absurd (mem_antidiagonal.2 rfl : (b₁, b₂) ∈ antidiagonal (b₁ + b₂)) hmem
  have hne : ((A * B).coeff (b₁ + b₂)).coeff (a₁ + a₂) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero ha₁ ha₂
  have hle := le_weightedDegree (d := d) hne
  have hsum : (a₁ + a₂) + d * (b₁ + b₂) = weightedDegree d A + weightedDegree d B := by
    rw [← hdeg₁, ← hdeg₂]
    ring
  omega

/-- The constant polynomial `1` has `(1, d)`-weighted degree `0`. -/
@[simp]
theorem weightedDegree_one (d : ℕ) : weightedDegree d (1 : R[X][Y]) = 0 := by
  refine Nat.eq_zero_of_le_zero (weightedDegree_le_iff.2 fun a b hab => ?_)
  rcases b with _ | b
  · rcases a with _ | a
    · omega
    · simp only [coeff_one, Nat.succ_ne_zero, ↓reduceIte] at hab
      exact absurd rfl hab
  · simp only [coeff_one, Nat.succ_ne_zero, ↓reduceIte, coeff_zero] at hab
    exact absurd rfl hab

/-- Divisors of a nonzero bivariate polynomial have no larger `(1, d)`-weighted degree. -/
theorem weightedDegree_le_of_dvd [NoZeroDivisors R] {d : ℕ} {A Q : R[X][Y]}
    (hQ : Q ≠ 0) (hdvd : A ∣ Q) : weightedDegree d A ≤ weightedDegree d Q := by
  obtain ⟨B, rfl⟩ := hdvd
  have hA : A ≠ 0 := left_ne_zero_of_mul hQ
  have hB : B ≠ 0 := right_ne_zero_of_mul hQ
  rw [weightedDegree_mul hA hB]
  exact Nat.le_add_right _ _

/-- `Y - C P` has `(1, d)`-weighted degree `d` whenever `P.natDegree ≤ d`. -/
theorem weightedDegree_X_sub_C {R : Type*} [CommRing R] [Nontrivial R] {d : ℕ} {P : R[X]}
    (hP : P.natDegree ≤ d) : weightedDegree d (Y - C P) = d := by
  refine le_antisymm (weightedDegree_le_iff.2 fun a b hab => ?_) ?_
  · rw [coeff_sub, coeff_X, coeff_C] at hab
    rcases b with _ | _ | b
    · simp only [one_ne_zero, ↓reduceIte, zero_sub, coeff_neg, neg_ne_zero] at hab
      have := le_natDegree_of_ne_zero hab
      omega
    · simp only [zero_add, ↓reduceIte, one_ne_zero, sub_zero, coeff_one] at hab
      by_cases ha : a = 0
      · subst ha; omega
      · simp only [ha, ↓reduceIte] at hab
        exact absurd rfl hab
    · have h1 : (1 : ℕ) ≠ b + 2 := by omega
      have h2 : b + 2 ≠ 0 := by omega
      simp only [h1, h2, ↓reduceIte, sub_self, coeff_zero] at hab
      exact absurd rfl hab
  · have h1 : (((Y - C P : R[X][Y]).coeff 1).coeff 0) ≠ 0 := by
      simp [coeff_sub, coeff_X]
    simpa using le_weightedDegree (d := d) h1

/-- Powers `(Y - C P) ^ r` have `(1, d)`-weighted degree `r * d` whenever `P.natDegree ≤ d`. -/
theorem weightedDegree_X_sub_C_pow {R : Type*} [CommRing R] [IsDomain R] {d : ℕ} {P : R[X]}
    (hP : P.natDegree ≤ d) (r : ℕ) : weightedDegree d ((Y - C P) ^ r) = r * d := by
  induction r with
  | zero =>
    rw [pow_zero, zero_mul, weightedDegree_one]
  | succ r ih =>
    rw [pow_succ, weightedDegree_mul (pow_ne_zero r (X_sub_C_ne_zero P)) (X_sub_C_ne_zero P),
      ih, weightedDegree_X_sub_C hP, Nat.succ_mul]

/-- Divisors of a nonzero polynomial preserve `Sudan.WeightedDegreeLE`. -/
theorem weightedDegreeLE_of_dvd {F : Type*} [Field F] {d D : ℕ} {A Q : F[X][Y]}
    (hQ0 : Q ≠ 0) (hQ : Sudan.WeightedDegreeLE d D Q) (hdvd : A ∣ Q) :
    Sudan.WeightedDegreeLE d D A :=
  weightedDegree_le_iff_weightedDegreeLE.1
    ((weightedDegree_le_of_dvd hQ0 hdvd).trans (weightedDegree_le_iff_weightedDegreeLE.2 hQ))

/-- Division by `(Y - C P) ^ r` lowers the `(1, d)`-weighted degree bound by `r * d`. -/
theorem weightedDegreeLE_of_X_sub_C_pow_mul {F : Type*} [Field F] {d D r : ℕ} {P : F[X]}
    (hP : P.natDegree ≤ d) {S : F[X][Y]}
    (h : Sudan.WeightedDegreeLE d D ((Y - C P) ^ r * S)) :
    Sudan.WeightedDegreeLE d (D - r * d) S := by
  rcases eq_or_ne S 0 with rfl | hS0
  · exact Sudan.weightedDegreeLE_zero d (D - r * d)
  · rw [← weightedDegree_le_iff_weightedDegreeLE] at h ⊢
    rw [weightedDegree_mul (pow_ne_zero r (X_sub_C_ne_zero P)) hS0,
      weightedDegree_X_sub_C_pow hP r] at h
    omega

end WeightedDegree

/-! ### Factor refinement over arbitrary fields (primitive, square-free, irreducible) -/

section FactorRefinement

open UniqueFactorizationMonoid

variable {F : Type*} [Field F]

section PrimRadical

variable [DecidableEq F]

/-- `Q.primPart` preserves `Sudan.WeightedDegreeLE d D`. -/
theorem weightedDegreeLE_primPart {d D : ℕ} {Q : F[X][Y]}
    (hQ : Sudan.WeightedDegreeLE d D Q) : Sudan.WeightedDegreeLE d D Q.primPart := by
  rcases eq_or_ne Q 0 with rfl | hQ0
  · rw [primPart_zero, ← weightedDegree_le_iff_weightedDegreeLE, weightedDegree_one]
    exact Nat.zero_le D
  · exact weightedDegreeLE_of_dvd hQ0 hQ Q.primPart_dvd

/-- For `Q ≠ 0`, `Q` and its primitive part `Q.primPart` have the same roots in `F[X]`. -/
theorem eval_primPart_eq_zero_iff {Q : F[X][Y]} (hQ : Q ≠ 0) (P : F[X]) :
    Q.primPart.eval P = 0 ↔ Q.eval P = 0 := by
  conv_rhs => rw [Q.eq_C_content_mul_primPart]
  rw [eval_mul, eval_C, mul_eq_zero]
  have hc : Q.content ≠ 0 := mt content_eq_zero_iff.1 hQ
  simp [hc]

/-- `radical Q.primPart` preserves `Sudan.WeightedDegreeLE d D`. -/
theorem weightedDegreeLE_radical_primPart {d D : ℕ} {Q : F[X][Y]}
    (hQ : Sudan.WeightedDegreeLE d D Q) : Sudan.WeightedDegreeLE d D (radical Q.primPart) :=
  weightedDegreeLE_of_dvd (primPart_ne_zero Q) (weightedDegreeLE_primPart hQ) radical_dvd_self

/-- `radical Q.primPart` is primitive. -/
theorem isPrimitive_radical_primPart (Q : F[X][Y]) : (radical Q.primPart).IsPrimitive :=
  isPrimitive_of_dvd (isPrimitive_primPart Q) radical_dvd_self

/-- `radical Q.primPart` is square-free. -/
theorem squarefree_radical_primPart (Q : F[X][Y]) : Squarefree (radical Q.primPart) :=
  squarefree_radical

/-- The `Y`-degree of `radical Q.primPart` is at most that of `Q`. -/
theorem natDegree_radical_primPart_le (Q : F[X][Y]) :
    (radical Q.primPart).natDegree ≤ Q.natDegree := by
  rw [← natDegree_primPart Q]
  exact natDegree_le_of_dvd radical_dvd_self (primPart_ne_zero Q)

/-- **Square-free root preservation.** For `Q ≠ 0`, `radical Q.primPart` is a nonzero, primitive,
square-free divisor of `Q` having the exact same `F[X]`-roots as `Q`. -/
theorem eval_radical_primPart_eq_zero_iff {Q : F[X][Y]} (hQ : Q ≠ 0) (P : F[X]) :
    (radical Q.primPart).eval P = 0 ↔ Q.eval P = 0 := by
  rw [← eval_primPart_eq_zero_iff hQ]
  change IsRoot (radical Q.primPart) P ↔ IsRoot Q.primPart P
  rw [← dvd_iff_isRoot, ← dvd_iff_isRoot]
  exact dvd_radical_iff_of_irreducible (Polynomial.irreducible_X_sub_C P) (primPart_ne_zero Q)

end PrimRadical

/-- Every root of a square-free bivariate polynomial `Q : F[X][Y]` is a simple root. -/
theorem exists_eq_mul_eval_ne_zero_of_squarefree {Q : F[X][Y]} (hsq : Squarefree Q) {P : F[X]}
    (hQP : Q.eval P = 0) : ∃ S : F[X][Y], Q = (Y - C P) * S ∧ S.eval P ≠ 0 := by
  obtain ⟨S, rfl⟩ := dvd_iff_isRoot.2 hQP
  refine ⟨S, rfl, fun hSP => ?_⟩
  obtain ⟨T, rfl⟩ := dvd_iff_isRoot.2 hSP
  have hu : IsUnit (Y - C P : F[X][Y]) :=
    hsq (Y - C P) ⟨T, by ring⟩
  have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [natDegree_X_sub_C] at hdeg
  omega

/-- Every root `P` of a nonzero `Q : F[X][Y]` factors out with exact positive multiplicity `r`. -/
theorem exists_eq_pow_mul_eval_ne_zero {Q : F[X][Y]} (hQ : Q ≠ 0) {P : F[X]}
    (hQP : Q.eval P = 0) :
    ∃ (r : ℕ) (S : F[X][Y]), 1 ≤ r ∧ Q = (Y - C P) ^ r * S ∧ S.eval P ≠ 0 := by
  let r := Q.rootMultiplicity P
  have hr : 1 ≤ r := Nat.succ_le_of_lt ((rootMultiplicity_pos hQ).2 hQP)
  obtain ⟨S, hQS⟩ := pow_rootMultiplicity_dvd Q P
  refine ⟨r, S, hr, hQS, fun hSP => ?_⟩
  obtain ⟨T, rfl⟩ := dvd_iff_isRoot.2 hSP
  have hdvd : (Y - C P) ^ (r + 1) ∣ Q := ⟨T, by rw [hQS, pow_succ]; ring⟩
  have hle : r + 1 ≤ r := (le_rootMultiplicity_iff hQ).2 hdvd
  omega

/-- **Primitive irreducible factorization.** Every nonzero `Q : F[X][Y]` factors as `C c * fs.prod`
with `c : F[X]` nonzero and every `R ∈ fs` irreducible, primitive, and of positive `Y`-degree,
preserving total `Y`-degree. -/
theorem exists_eq_C_mul_prod_irreducible {Q : F[X][Y]} (hQ : Q ≠ 0) :
    ∃ (c : F[X]) (fs : Multiset F[X][Y]),
      c ≠ 0 ∧
      (∀ R ∈ fs, Irreducible R ∧ R.IsPrimitive ∧ 1 ≤ R.natDegree) ∧
      Q = C c * fs.prod ∧
      (fs.map Polynomial.natDegree).sum = Q.natDegree := by
  classical
  let fs := UniqueFactorizationMonoid.factors Q.primPart
  have hprim : Q.primPart ≠ 0 := primPart_ne_zero Q
  have hassoc : Associated fs.prod Q.primPart := UniqueFactorizationMonoid.factors_prod hprim
  obtain ⟨u, hu⟩ := hassoc
  obtain ⟨a, ha_unit, ha_eq⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have hQeq : Q = C (Q.content * a) * fs.prod := by
    conv_lhs => rw [Q.eq_C_content_mul_primPart]
    rw [← hu, ← ha_eq, C_mul]
    ring
  have hc0 : Q.content * a ≠ 0 :=
    mul_ne_zero (mt content_eq_zero_iff.1 hQ) ha_unit.ne_zero
  have hfs_prop : ∀ R ∈ fs, Irreducible R ∧ R.IsPrimitive ∧ 1 ≤ R.natDegree := by
    intro R hR
    have hirr : Irreducible R := UniqueFactorizationMonoid.irreducible_of_factor R hR
    have hdvd : R ∣ Q.primPart :=
      (Multiset.dvd_prod hR).trans ⟨(u : F[X][Y]), hu.symm⟩
    have hRprim : R.IsPrimitive := isPrimitive_of_dvd (isPrimitive_primPart Q) hdvd
    have hdeg : 1 ≤ R.natDegree := by
      by_contra h0
      have h0' : R.natDegree = 0 := by omega
      have hRC : R = C (R.coeff 0) := eq_C_of_natDegree_eq_zero h0'
      have hcont : normalize (R.coeff 0) = 1 := by
        have := hRprim.content_eq_one
        rw [hRC, content_C] at this
        exact this
      have hunit0 : IsUnit (R.coeff 0) := by
        obtain ⟨v, hv⟩ := associated_normalize (R.coeff 0)
        rw [hcont] at hv
        exact isUnit_iff_exists_inv.2 ⟨(v : F[X]), hv⟩
      exact hirr.not_isUnit (hRC ▸ hunit0.map C)
    exact ⟨hirr, hRprim, hdeg⟩
  have hprod_ne : fs.prod ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hQeq
    exact hQ hQeq
  have hdeg_sum : (fs.map Polynomial.natDegree).sum = Q.natDegree := by
    rw [hQeq, natDegree_C_mul hc0]
    exact (Polynomial.natDegree_multiset_prod fs fun h0 =>
      hprod_ne (Multiset.prod_eq_zero h0)).symm
  exact ⟨Q.content * a, fs, hc0, hfs_prop, hQeq, hdeg_sum⟩

/-- Every factor in a primitive irreducible factorization inherits `Sudan.WeightedDegreeLE d D`,
and their weighted degrees sum to at most `D`. -/
theorem sum_weightedDegree_le_of_eq_C_mul_prod {d D : ℕ} {Q : F[X][Y]} {c : F[X]}
    {fs : Multiset F[X][Y]} (hQ : Sudan.WeightedDegreeLE d D Q) (hc : c ≠ 0)
    (hfs : ∀ R ∈ fs, R ≠ 0) (hQeq : Q = C c * fs.prod) :
    (fs.map (weightedDegree d)).sum ≤ D ∧ ∀ R ∈ fs, Sudan.WeightedDegreeLE d D R := by
  have hsum_aux : ∀ s : Multiset F[X][Y], (∀ R ∈ s, R ≠ 0) →
      (s.map (weightedDegree d)).sum = weightedDegree d s.prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      intro _
      simp only [Multiset.map_zero, Multiset.sum_zero, Multiset.prod_zero, weightedDegree_one]
    | cons R s ih =>
      intro hs
      have hR0 : R ≠ 0 := hs R (Multiset.mem_cons_self R s)
      have hs0 : ∀ R' ∈ s, R' ≠ 0 := fun R' hR' => hs R' (Multiset.mem_cons_of_mem hR')
      have hsprod : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => hs0 0 h0 rfl
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons,
        weightedDegree_mul hR0 hsprod, ih hs0]
  have hprod_ne : fs.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => hfs 0 h0 rfl
  have hQ0 : Q ≠ 0 := by
    rw [hQeq]
    exact mul_ne_zero (C_ne_zero.2 hc) hprod_ne
  have hle : weightedDegree d fs.prod ≤ D := by
    rw [weightedDegree_le_iff_weightedDegreeLE]
    exact weightedDegreeLE_of_dvd hQ0 hQ ⟨C c, by rw [hQeq, mul_comm]⟩
  refine ⟨(hsum_aux fs hfs).trans_le hle, fun R hR => ?_⟩
  exact weightedDegreeLE_of_dvd hQ0 hQ ((Multiset.dvd_prod hR).trans ⟨C c, by rw [hQeq, mul_comm]⟩)

end FactorRefinement

/-! ### Multiplicity-`m` interpolation and root-divisibility -/

section Interpolation

variable {F ι : Type*} [Field F]

/-- The pairs `(r, s)` with `r + s < m`, indexing the multiplicity-`m` vanishing conditions at
each point. -/
def multPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  {rs ∈ range m ×ˢ range m | rs.1 + rs.2 < m}

/-- `(r, s) ∈ multPairs m` iff `r + s < m`. -/
theorem mem_multPairs {m : ℕ} {rs : ℕ × ℕ} : rs ∈ multPairs m ↔ rs.1 + rs.2 < m := by
  simp only [multPairs, mem_filter, mem_product, mem_range]
  omega

/-- Twice the number of multiplicity-`m` pairs is `m * (m + 1)`. -/
theorem two_mul_card_multPairs (m : ℕ) : 2 * #(multPairs m) = m * (m + 1) := by
  induction m with
  | zero =>
    simp [multPairs]
  | succ m ih =>
    have hunion : multPairs (m + 1) = multPairs m ∪ antidiagonal m := by
      ext rs
      simp only [mem_multPairs, mem_union, mem_antidiagonal]
      omega
    have hdisj : Disjoint (multPairs m) (antidiagonal m) := by
      rw [Finset.disjoint_left]
      intro rs h1 h2
      rw [mem_multPairs] at h1
      rw [mem_antidiagonal] at h2
      omega
    rw [hunion, card_union_of_disjoint hdisj, Finset.Nat.card_antidiagonal, mul_add, ih]
    ring

/-- The number of multiplicity-`m` pairs at each point is `m * (m + 1) / 2`. -/
theorem card_multPairs (m : ℕ) : #(multPairs m) = m * (m + 1) / 2 := by
  have := two_mul_card_multPairs m
  omega

/-- `Q` is a *weighted-multiplicity Guruswami–Sudan interpolant* for the received word `w` at
evaluation points `α`, with per-point multiplicities `mult : ι → ℕ`, weight `d`, and weighted
degree bound `D`: a nonzero bivariate polynomial of `(1, d)`-weighted degree at most `D` vanishing
to order at least `mult i` at each `(α i, w i)`. -/
structure IsWeightedInterpolant (α w : ι → F) (mult : ι → ℕ) (d D : ℕ) (Q : F[X][Y]) : Prop where
  /-- The interpolant is nonzero. -/
  ne_zero : Q ≠ 0
  /-- Every monomial `X ^ a * Y ^ b` of `Q` has `(1, d)`-weighted degree `a + d * b` at most
  `D`. -/
  weightedDegree_le : Sudan.WeightedDegreeLE d D Q
  /-- The interpolant vanishes to order at least `mult i` at each point `(α i, w i)`. -/
  vanishes : ∀ i, VanishesToOrder (mult i) (α i) (w i) Q

/-- `Q` is a *multiplicity-`m` Guruswami–Sudan interpolant* for the received word `w` at evaluation
points `α`, with weight `d` and weighted degree bound `D`: a nonzero bivariate polynomial of
`(1, d)`-weighted degree at most `D` that vanishes to multiplicity at least `m` at every point
`(α i, w i)`. -/
structure IsInterpolant (α w : ι → F) (m d D : ℕ) (Q : F[X][Y]) : Prop where
  /-- The interpolant is nonzero. -/
  ne_zero : Q ≠ 0
  /-- Every monomial `X ^ a * Y ^ b` of `Q` has `(1, d)`-weighted degree `a + d * b` at most
  `D`. -/
  weightedDegree_le : Sudan.WeightedDegreeLE d D Q
  /-- The interpolant vanishes to order at least `m` at every point `(α i, w i)`. -/
  vanishes : ∀ i, VanishesToOrder m (α i) (w i) Q

variable {α w : ι → F} {mult : ι → ℕ} {m d D : ℕ} {Q : F[X][Y]}

/-- Uniform multiplicity-`m` interpolants coincide with weighted interpolants with constant
multiplicity `fun _ => m`. -/
theorem isInterpolant_iff_isWeightedInterpolant :
    IsInterpolant α w m d D Q ↔ IsWeightedInterpolant α w (fun _ => m) d D Q :=
  ⟨fun h => ⟨h.ne_zero, h.weightedDegree_le, h.vanishes⟩,
   fun h => ⟨h.ne_zero, h.weightedDegree_le, h.vanishes⟩⟩

/-- The `Y`-degree of a weighted interpolant satisfies `Q.natDegree * d ≤ D`. -/
theorem IsWeightedInterpolant.natDegree_mul_le (hQ : IsWeightedInterpolant α w mult d D Q) :
    Q.natDegree * d ≤ D :=
  hQ.weightedDegree_le.natDegree_mul_le

/-- The `Y`-degree of a Guruswami–Sudan interpolant satisfies `Q.natDegree * d ≤ D`. -/
theorem IsInterpolant.natDegree_mul_le (hQ : IsInterpolant α w m d D Q) :
    Q.natDegree * d ≤ D :=
  hQ.weightedDegree_le.natDegree_mul_le

/-- Multiplicity-`1` Guruswami–Sudan interpolants are Sudan interpolants. -/
theorem isInterpolant_one_iff_sudan :
    IsInterpolant α w 1 d D Q ↔ Sudan.IsInterpolant α w d D Q := by
  constructor
  · intro h
    exact ⟨h.ne_zero, h.weightedDegree_le,
      fun i => (vanishesToOrder_one_iff (α i) (w i) Q).1 (h.vanishes i)⟩
  · intro h
    exact ⟨h.ne_zero, h.weightedDegree_le,
      fun i => (vanishesToOrder_one_iff (α i) (w i) Q).2 (h.evalEval_eq_zero i)⟩

/-- **Least-`Y`-degree multiplicity bound.** If `Q` is a multiplicity-`m` interpolant of minimum
`Y`-degree, then no polynomial `P : F[X]` is a root of `Q` of multiplicity strictly exceeding
`m`. -/
theorem IsInterpolant.rootMultiplicity_le_of_min (hQ : IsInterpolant α w m d D Q)
    (hmin : ∀ Q', IsInterpolant α w m d D Q' → Q.natDegree ≤ Q'.natDegree) (P : F[X]) :
    Q.rootMultiplicity P ≤ m := by
  by_contra hlt
  push Not at hlt
  set r := Q.rootMultiplicity P
  obtain ⟨S, hQS⟩ := pow_rootMultiplicity_dvd Q P
  change Q = (Y - C P) ^ r * S at hQS
  have hS0 : S ≠ 0 := fun h => hQ.ne_zero (by rw [hQS, h, mul_zero])
  let Q' : F[X][Y] := (Y - C P) ^ m * S
  have hQ'0 : Q' ≠ 0 := mul_ne_zero (pow_ne_zero m (X_sub_C_ne_zero P)) hS0
  have hQ'dvd : Q' ∣ Q := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hlt.le
    refine ⟨(Y - C P) ^ t, ?_⟩
    rw [hQS, ht, pow_add]
    dsimp only [Q']
    ring
  have hQ'interp : IsInterpolant α w m d D Q' := by
    refine ⟨hQ'0, weightedDegreeLE_of_dvd hQ.ne_zero hQ.weightedDegree_le hQ'dvd, fun i => ?_⟩
    by_cases hi : P.eval (α i) = w i
    · have hm := (vanishesToOrder_one_X_sub_C hi).pow m
      simpa only [mul_one, add_zero] using hm.mul (vanishesToOrder_zero (α i) (w i) S)
    · have hne : ((Y - C P) ^ r).evalEval (α i) (w i) ≠ 0 := by
        rw [evalEval_pow, evalEval_sub, evalEval_X, evalEval_C]
        exact pow_ne_zero r (sub_ne_zero.2 (Ne.symm hi))
      have hSvan : VanishesToOrder m (α i) (w i) S :=
        VanishesToOrder.of_mul_left_of_evalEval_ne_zero hne (hQS ▸ hQ.vanishes i)
      simpa only [zero_add] using
        (vanishesToOrder_zero (α i) (w i) ((Y - C P) ^ m)).mul hSvan
  have hle := hmin Q' hQ'interp
  have hmon_m : ((Y - C P) ^ m).Monic := (monic_X_sub_C P).pow m
  have hmon_r : ((Y - C P) ^ r).Monic := (monic_X_sub_C P).pow r
  have hdegQ : Q.natDegree = r + S.natDegree := by
    rw [hQS, hmon_r.natDegree_mul' hS0, (monic_X_sub_C P).natDegree_pow, natDegree_X_sub_C, mul_one]
  have hdegQ' : Q'.natDegree = m + S.natDegree := by
    rw [hmon_m.natDegree_mul' hS0, (monic_X_sub_C P).natDegree_pow, natDegree_X_sub_C, mul_one]
  omega

variable [Fintype ι]

/-- **Existence of a weighted-multiplicity interpolant.** Whenever the number of monomials of
`(1, d)`-weighted degree at most `D` exceeds `∑ i, mult i * (mult i + 1) / 2`, every received word
has a nonzero weighted-multiplicity interpolant. -/
theorem exists_isWeightedInterpolant (α w : ι → F)
    (hn : ∑ i : ι, mult i * (mult i + 1) / 2 < #(Sudan.monomials d D)) :
    ∃ Q, IsWeightedInterpolant α w mult d D Q := by
  classical
  let M := Sudan.monomials d D
  let Row := Σ i : ι, multPairs (mult i)
  let A : Matrix Row M F := Matrix.of fun row col =>
    let (r, s) := (row.2 : ℕ × ℕ)
    let (a, b) := (col : ℕ × ℕ)
    (a.choose r : F) * (b.choose s : F) * α row.1 ^ (a - r) * w row.1 ^ (b - s)
  have hcard_lt : Fintype.card Row < Fintype.card M := by
    rw [Fintype.card_sigma, Fintype.card_coe]
    simpa [Fintype.card_coe, card_multPairs] using hn
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by
      rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card])
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  obtain ⟨col₀, hcol₀⟩ := Function.ne_iff.1 hc0
  let c' : ℕ × ℕ → F := fun m' => if h : m' ∈ M then c ⟨m', h⟩ else 0
  refine ⟨Sudan.bivariateOf M c', fun h => hcol₀ ?_,
    Sudan.weightedDegreeLE_bivariateOf Subset.rfl c', fun i r s hrs => ?_⟩
  · have := Sudan.coeff_coeff_bivariateOf M c' (col₀ : ℕ × ℕ).1 (col₀ : ℕ × ℕ).2
    rw [h] at this
    simpa [c', col₀.2] using this.symm
  · rw [coeff_coeff_shift_bivariateOf, ← sum_attach]
    have hrow := congrFun (LinearMap.mem_ker.1 hc) ⟨i, ⟨(r, s), mem_multPairs.2 hrs⟩⟩
    simpa [A, c', Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, mul_assoc] using hrow

/-- Existence of a weighted-multiplicity interpolant of least `Y`-degree. -/
theorem exists_isWeightedInterpolant_min_natDegree (α w : ι → F)
    (hn : ∑ i : ι, mult i * (mult i + 1) / 2 < #(Sudan.monomials d D)) :
    ∃ Q, IsWeightedInterpolant α w mult d D Q ∧
      ∀ Q', IsWeightedInterpolant α w mult d D Q' → Q.natDegree ≤ Q'.natDegree := by
  classical
  have hex : ∃ n : ℕ, ∃ Q, IsWeightedInterpolant α w mult d D Q ∧ Q.natDegree = n := by
    obtain ⟨Q, hQ⟩ := exists_isWeightedInterpolant (mult := mult) (d := d) (D := D) α w hn
    exact ⟨Q.natDegree, Q, hQ, rfl⟩
  let n₀ := Nat.find hex
  obtain ⟨Q, hQ, hdeg⟩ := Nat.find_spec hex
  refine ⟨Q, hQ, fun Q' hQ' => ?_⟩
  rw [hdeg]
  exact Nat.find_min' hex ⟨Q', hQ', rfl⟩

/-- **Existence of a multiplicity-`m` interpolant.** Whenever the number of monomials of
`(1, d)`-weighted degree at most `D` exceeds `|ι| * (m * (m + 1) / 2)`, every received word has a
nonzero multiplicity-`m` interpolant. -/
theorem exists_isInterpolant (α w : ι → F)
    (hn : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials d D)) :
    ∃ Q, IsInterpolant α w m d D Q := by
  have hn' : ∑ _ : ι, m * (m + 1) / 2 < #(Sudan.monomials d D) := by
    simpa [Finset.sum_const, smul_eq_mul] using hn
  obtain ⟨Q, hQ⟩ := exists_isWeightedInterpolant (mult := fun _ => m) (d := d) (D := D) α w hn'
  exact ⟨Q, isInterpolant_iff_isWeightedInterpolant.2 hQ⟩

/-- **Closed-form existence of a multiplicity-`m` interpolant.** For `d ≥ 1`, whenever
`|ι| * d * m * (m + 1) < (D + 1) * (D + 2)`, there are strictly more monomials of `(1, d)`-weighted
degree at most `D` than multiplicity-`m` constraints, so an interpolant exists. -/
theorem card_mul_lt_card_monomials_of_lt {n m d D : ℕ} (hd : 1 ≤ d)
    (h : n * d * m * (m + 1) < (D + 1) * (D + 2)) :
    n * (m * (m + 1) / 2) < #(Sudan.monomials d D) := by
  have hmon := Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials hd D
  have heven : 2 * (m * (m + 1) / 2) = m * (m + 1) := by
    rw [← card_multPairs m, two_mul_card_multPairs m]
  have hmul : 2 * d * (n * (m * (m + 1) / 2)) < 2 * d * #(Sudan.monomials d D) := by
    calc 2 * d * (n * (m * (m + 1) / 2))
        = n * d * (2 * (m * (m + 1) / 2)) := by ring
      _ = n * d * m * (m + 1) := by rw [heven]; ring
      _ < (D + 1) * (D + 2) := h
      _ ≤ 2 * d * #(Sudan.monomials d D) := hmon
  exact Nat.lt_of_mul_lt_mul_left hmul

/-- Existence of a multiplicity-`m` interpolant from `|ι| * d * m * (m + 1) < (D + 1) * (D + 2)`. -/
theorem exists_isInterpolant_of_lt (α w : ι → F) (hd : 1 ≤ d)
    (h : Fintype.card ι * d * m * (m + 1) < (D + 1) * (D + 2)) :
    ∃ Q, IsInterpolant α w m d D Q :=
  exists_isInterpolant α w (card_mul_lt_card_monomials_of_lt hd h)

variable [DecidableEq F]

/-- **Weighted multiplicity root containment.** With distinct points `α`, if `P` has
`natDegree ≤ d` and `D < ∑ i ∈ {i | P.eval (α i) = w i}, mult i`, then `Q.eval P = 0` for every
weighted-multiplicity interpolant `Q`. -/
theorem IsWeightedInterpolant.eval_eq_zero (hα : Function.Injective α)
    (hQ : IsWeightedInterpolant α w mult d D Q) {P : F[X]} (hP : P.natDegree ≤ d)
    (hagree : D < ∑ i ∈ {i | P.eval (α i) = w i}, mult i) : Q.eval P = 0 := by
  classical
  by_contra hne
  let agree : Finset ι := {i | P.eval (α i) = w i}
  let ms : Multiset F := ∑ i ∈ agree, Multiset.replicate (mult i) (α i)
  have hle_roots : ms ≤ (Q.eval P).roots := by
    rw [Multiset.le_iff_count]
    intro x
    rw [Polynomial.count_roots]
    have hcnt : Multiset.count x ms =
        ∑ i ∈ agree, Multiset.count x (Multiset.replicate (mult i) (α i)) := by
      dsimp only [ms]
      induction agree using Finset.cons_induction with
      | empty => simp
      | cons i s hi ih =>
        rw [Finset.sum_cons, Finset.sum_cons, Multiset.count_add, ih]
    rw [hcnt]
    by_cases hx : ∃ i ∈ agree, α i = x
    · obtain ⟨i, hi, rfl⟩ := hx
      rw [Finset.sum_eq_single i]
      · rw [Multiset.count_replicate_self]
        exact (le_rootMultiplicity_iff hne).2
          ((hQ.vanishes i).X_sub_C_pow_dvd_eval (mem_filter.1 hi).2)
      · intro j _ hji
        rw [Multiset.count_replicate, ite_eq_right fun heq => hji (hα heq)]
      · intro hi'
        exact absurd hi hi'
    · push Not at hx
      rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro j hj
        rw [Multiset.count_replicate, ite_eq_right (hx j hj)]
  have hms_card : ms.card = ∑ i ∈ agree, mult i := by
    dsimp only [ms]
    induction agree using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons, Multiset.card_add, Multiset.card_replicate, ih]
  have hcard : ∑ i ∈ agree, mult i ≤ D := by
    calc ∑ i ∈ agree, mult i = ms.card := hms_card.symm
      _ ≤ (Q.eval P).roots.card := Multiset.card_le_card hle_roots
      _ ≤ (Q.eval P).natDegree := Polynomial.card_roots' _
      _ ≤ D := hQ.weightedDegree_le.natDegree_eval_le hP
  exact absurd hcard (not_le.2 hagree)

/-- Under the hypotheses of `IsWeightedInterpolant.eval_eq_zero`, `Y - C P` divides `Q`. -/
theorem IsWeightedInterpolant.X_sub_C_dvd (hα : Function.Injective α)
    (hQ : IsWeightedInterpolant α w mult d D Q) {P : F[X]} (hP : P.natDegree ≤ d)
    (hagree : D < ∑ i ∈ {i | P.eval (α i) = w i}, mult i) : Y - C P ∣ Q :=
  dvd_iff_isRoot.2 (hQ.eval_eq_zero hα hP hagree)

/-- Under the hypotheses of `IsWeightedInterpolant.eval_eq_zero`, `P` is a root of `Q`. -/
theorem IsWeightedInterpolant.mem_roots (hα : Function.Injective α)
    (hQ : IsWeightedInterpolant α w mult d D Q) {P : F[X]} (hP : P.natDegree ≤ d)
    (hagree : D < ∑ i ∈ {i | P.eval (α i) = w i}, mult i) : P ∈ Q.roots :=
  (Polynomial.mem_roots hQ.ne_zero).2 (hQ.eval_eq_zero hα hP hagree)

/-- **Multiplicity root containment.** With distinct points `α`, if `P` has `natDegree ≤ d` and
`D < m * #{i | P.eval (α i) = w i}`, then `Q.eval P = 0` for every multiplicity-`m` interpolant
`Q`. -/
theorem IsInterpolant.eval_eq_zero (hα : Function.Injective α) (hQ : IsInterpolant α w m d D Q)
    {P : F[X]} (hP : P.natDegree ≤ d) (hagree : D < m * #{i | P.eval (α i) = w i}) :
    Q.eval P = 0 := by
  have hagree' : D < ∑ _ ∈ {i | P.eval (α i) = w i}, m := by
    simpa [Finset.sum_const, smul_eq_mul, mul_comm] using hagree
  exact (isInterpolant_iff_isWeightedInterpolant.1 hQ).eval_eq_zero hα hP hagree'

/-- **Multiplicity root divisibility.** Under the hypotheses of `IsInterpolant.eval_eq_zero`,
`Y - C P` divides every multiplicity-`m` interpolant `Q`. -/
theorem IsInterpolant.X_sub_C_dvd (hα : Function.Injective α) (hQ : IsInterpolant α w m d D Q)
    {P : F[X]} (hP : P.natDegree ≤ d) (hagree : D < m * #{i | P.eval (α i) = w i}) :
    Y - C P ∣ Q :=
  dvd_iff_isRoot.2 (hQ.eval_eq_zero hα hP hagree)

/-- Under the hypotheses of `IsInterpolant.eval_eq_zero`, `P` is a root of `Q` in `F[X][Y]`. -/
theorem IsInterpolant.mem_roots (hα : Function.Injective α) (hQ : IsInterpolant α w m d D Q)
    {P : F[X]} (hP : P.natDegree ≤ d) (hagree : D < m * #{i | P.eval (α i) = w i}) :
    P ∈ Q.roots :=
  (Polynomial.mem_roots hQ.ne_zero).2 (hQ.eval_eq_zero hα hP hagree)

/-! ### Explicit least-`Y`-degree multiplicity-`m` interpolant -/

/-- The multiplicity-`m` interpolation matrix: rows index `(i, (r, s)) ∈ ι × multPairs m`, columns
index monomials `m' ∈ M`, and entries give the `(r, s)` coefficient of `shift (α i) (w i)` on each
monomial. -/
noncomputable def interpMatrix (α w : ι → F) (m : ℕ) (M : Finset (ℕ × ℕ)) :
    Fin (Fintype.card (ι × multPairs m)) → Fin #M → F :=
  fun t col =>
    let row := (Fintype.equivFin (ι × multPairs m)).symm t
    let (r, s) := (row.2 : ℕ × ℕ)
    let (a, b) := (M.equivFin.symm col : ℕ × ℕ)
    (a.choose r : F) * (b.choose s : F) * α row.1 ^ (a - r) * w row.1 ^ (b - s)

omit [DecidableEq F] in
/-- The dot product of a row of `interpMatrix` with `u` equals the corresponding shifted
coefficient of `Sudan.bivariateOf M (Sudan.coeffsOf M u)`. -/
theorem interpMatrix_dotProduct (α w : ι → F) (m : ℕ) (M : Finset (ℕ × ℕ)) (u : Fin #M → F)
    (i : ι) (rs : multPairs m) :
    interpMatrix α w m M (Fintype.equivFin (ι × multPairs m) (i, rs)) ⬝ᵥ u =
      ((shift (α i) (w i) (Sudan.bivariateOf M (Sudan.coeffsOf M u))).coeff (rs : ℕ × ℕ).2).coeff
        (rs : ℕ × ℕ).1 := by
  rw [coeff_coeff_shift_bivariateOf, dotProduct]
  let r := (rs : ℕ × ℕ).1
  let s := (rs : ℕ × ℕ).2
  have h := Equiv.sum_comp M.equivFin.symm (fun col : M =>
    let (a, b) := (col : ℕ × ℕ)
    ((a.choose r : F) * (b.choose s : F) * α i ^ (a - r) * w i ^ (b - s)) * u (M.equivFin col))
  simp only [Equiv.apply_symm_apply] at h
  rw [← Finset.sum_coe_sort M (fun col =>
    Sudan.coeffsOf M u col * ((col.1.choose r : F) * (col.2.choose s : F) *
      α i ^ (col.1 - r) * w i ^ (col.2 - s)))]
  simp only [interpMatrix, Equiv.symm_apply_apply]
  rw [h]
  refine Fintype.sum_congr _ _ fun col => ?_
  simp only [Sudan.coeffsOf, Finset.coe_mem, dite_true, Subtype.coe_eta]
  ring

/-- The kernel vector of the multiplicity-`m` interpolation matrix on monomials of `Y`-degree at
most `j`. -/
noncomputable def kernelVecUpTo (α w : ι → F) (m d D j : ℕ) :
    Fin #(Sudan.monomialsUpTo d D j) → F :=
  kernelVec (interpMatrix α w m (Sudan.monomialsUpTo d D j))

/-- The coefficients of the least-`Y`-degree multiplicity-`m` interpolant: those of the first
nonzero kernel vector among `j = 0, 1, …, D / d`. -/
noncomputable def interpolantCoeffs (α w : ι → F) (m d D : ℕ) : ℕ × ℕ → F :=
  ∑ j : Fin (D / d + 1),
    firstFlags
        (fun j : Fin (D / d + 1) => if kernelVecUpTo α w m d D j = 0 then (0 : F) else 1) j •
      Sudan.coeffsOf (Sudan.monomialsUpTo d D j) (kernelVecUpTo α w m d D j)

/-- **An explicit multiplicity-`m` interpolant of least `Y`-degree**, computed by elimination. -/
noncomputable def interpolant (α w : ι → F) (m d D : ℕ) : F[X][Y] :=
  Sudan.bivariateOf (Sudan.monomials d D) (interpolantCoeffs α w m d D)

/-- The elimination interpolant always has `(1, d)`-weighted degree at most `D`. -/
theorem weightedDegreeLE_interpolant (α w : ι → F) (m d D : ℕ) :
    Sudan.WeightedDegreeLE d D (interpolant α w m d D) :=
  Sudan.weightedDegreeLE_bivariateOf Subset.rfl _

/-- The elimination interpolant always has `Y`-degree at most `D` (for all `d`, including
`d = 0`). -/
theorem natDegree_interpolant_le_bound (α w : ι → F) (m d D : ℕ) :
    (interpolant α w m d D).natDegree ≤ D := by
  refine natDegree_le_iff_coeff_eq_zero.2 fun b hb => ?_
  ext a
  rw [interpolant, Sudan.coeff_coeff_bivariateOf, coeff_zero]
  split_ifs with h
  · exact absurd (Sudan.mem_monomials.1 h).2.1 (not_le.2 hb)
  · rfl

omit [Fintype ι] [DecidableEq F] in
/-- The monomials of a multiplicity-`m` interpolant lie in `Sudan.monomials d D` when `1 ≤ d`. -/
private theorem mem_monomials_of_isInterpolant {α w : ι → F} {m d D : ℕ} (hd : 1 ≤ d)
    {Q : F[X][Y]} (hQ : IsInterpolant α w m d D Q) {a b : ℕ}
    (hab : (Q.coeff b).coeff a ≠ 0) : (a, b) ∈ Sudan.monomials d D := by
  have h := hQ.weightedDegree_le a b hab
  refine Sudan.mem_monomials.2 ⟨by omega, ?_, h⟩
  nlinarith

/-- A multiplicity-`m` interpolant of `Y`-degree at most `j` gives a nonzero kernel vector on
`Sudan.monomialsUpTo d D j`. -/
private theorem kernelVecUpTo_ne_zero {α w : ι → F} {m d D : ℕ} (hd : 1 ≤ d) {Q : F[X][Y]}
    (hQ : IsInterpolant α w m d D Q) {j : ℕ} (hj : Q.natDegree ≤ j) :
    kernelVecUpTo α w m d D j ≠ 0 := by
  set M := Sudan.monomialsUpTo d D j
  have hsupp : ∀ a b, (Q.coeff b).coeff a ≠ 0 → (a, b) ∈ M := fun a b hab =>
    mem_filter.2 ⟨mem_monomials_of_isInterpolant hd hQ hab,
      (le_natDegree_of_ne_zero fun h => hab (by rw [h, coeff_zero])).trans hj⟩
  refine kernelVec_ne_zero _ ⟨fun col =>
    let (a, b) := (M.equivFin.symm col : ℕ × ℕ)
    (Q.coeff b).coeff a, ?_, funext fun t => ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b, Q.coeff b ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ.ne_zero (Polynomial.ext fun b => by rw [h b, coeff_zero])
    obtain ⟨a, ha⟩ : ∃ a, (Q.coeff b).coeff a ≠ 0 := by
      by_contra h
      push Not at h
      exact hb (Polynomial.ext fun a => by rw [h a, coeff_zero])
    intro h0
    have := congrFun h0 (M.equivFin ⟨(a, b), hsupp a b ha⟩)
    simp only [Equiv.symm_apply_apply, Pi.zero_apply] at this
    exact ha this
  · change interpMatrix α w m M t ⬝ᵥ _ = 0
    obtain ⟨⟨i, rs⟩, rfl⟩ := (Fintype.equivFin (ι × multPairs m)).surjective t
    rw [interpMatrix_dotProduct]
    have hQeq : Sudan.bivariateOf M (Sudan.coeffsOf M fun col =>
        let (a, b) := (M.equivFin.symm col : ℕ × ℕ)
        (Q.coeff b).coeff a) = Q := by
      refine (Sudan.bivariateOf_congr fun col hcol => ?_).trans (Sudan.eq_bivariateOf hsupp).symm
      simp only [Sudan.coeffsOf, dite_eq_left hcol, Equiv.symm_apply_apply]
    rw [hQeq]
    exact hQ.vanishes i (rs : ℕ × ℕ).1 (rs : ℕ × ℕ).2 (mem_multPairs.1 rs.2)

/-- The elimination interpolant selects the first nonzero kernel vector among `j = 0, …, D / d`. -/
private theorem exists_interpolant_eq {α w : ι → F} {m d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials d D)) :
    ∃ j : Fin (D / d + 1), kernelVecUpTo α w m d D j ≠ 0 ∧
      (∀ i < j, kernelVecUpTo α w m d D i = 0) ∧
      interpolantCoeffs α w m d D =
        Sudan.coeffsOf (Sudan.monomialsUpTo d D j) (kernelVecUpTo α w m d D j) := by
  obtain ⟨Q₀, hQ₀⟩ := exists_isInterpolant (m := m) (d := d) (D := D) α w hn
  have hdeg : Q₀.natDegree ≤ D / d := (Nat.le_div_iff_mul_le hd).2 hQ₀.natDegree_mul_le
  obtain h | h := sum_firstFlags_smul_eq
      (fun j : Fin (D / d + 1) => if kernelVecUpTo α w m d D j = 0 then (0 : F) else 1)
      (fun j => Sudan.coeffsOf (Sudan.monomialsUpTo d D j) (kernelVecUpTo α w m d D j))
  · exfalso
    have := congrFun h.1 ⟨Q₀.natDegree, Nat.lt_succ_of_le hdeg⟩
    simp only [Pi.zero_apply, ite_eq_left_iff, one_ne_zero, imp_false, not_not] at this
    exact kernelVecUpTo_ne_zero hd hQ₀ le_rfl this
  · obtain ⟨j, hj, hlt, hsum⟩ := h
    refine ⟨j, fun h => hj (by simp [h]), fun i hi => ?_, hsum⟩
    have := hlt i hi
    simpa using this

/-- **The elimination interpolant is a multiplicity-`m` interpolant.** For `d ≥ 1` and strictly
more monomials of `(1, d)`-weighted degree at most `D` than multiplicity-`m` constraints,
`interpolant α w m d D` satisfies `IsInterpolant α w m d D`. -/
theorem isInterpolant_interpolant (α w : ι → F) {m d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials d D)) :
    IsInterpolant α w m d D (interpolant α w m d D) := by
  obtain ⟨j, hj, -, hcoeffs⟩ := exists_interpolant_eq (α := α) (w := w) hd hn
  set M := Sudan.monomialsUpTo d D (j : ℕ)
  have hsub : M ⊆ Sudan.monomials d D := filter_subset _ _
  have hcoeff : ∀ a b, ((interpolant α w m d D).coeff b).coeff a =
      Sudan.coeffsOf M (kernelVecUpTo α w m d D j) (a, b) := by
    intro a b
    rw [interpolant, Sudan.coeff_coeff_bivariateOf, hcoeffs]
    split_ifs with h
    · rfl
    · simp only [Sudan.coeffsOf]
      rw [dite_eq_right fun h' => absurd (hsub h') h]
  refine ⟨fun h0 => hj ?_, weightedDegreeLE_interpolant α w m d D, fun i r s hrs => ?_⟩
  · funext col
    have := hcoeff (M.equivFin.symm col : ℕ × ℕ).1 (M.equivFin.symm col : ℕ × ℕ).2
    rw [h0] at this
    simp only [coeff_zero, Sudan.coeffsOf, Prod.mk.eta, coe_mem, dite_eq_left, Subtype.coe_eta,
      Equiv.apply_symm_apply] at this
    exact this.symm
  · let rs : multPairs m := ⟨(r, s), mem_multPairs.2 hrs⟩
    have hzero :
        interpMatrix α w m M (Fintype.equivFin (ι × multPairs m) (i, rs)) ⬝ᵥ
          kernelVecUpTo α w m d D j = 0 :=
      congrFun (mulVec_kernelVec _) _
    rw [interpMatrix_dotProduct, coeff_coeff_shift_bivariateOf] at hzero
    rw [interpolant, hcoeffs, coeff_coeff_shift_bivariateOf, ← hzero]
    refine (Finset.sum_subset hsub fun col _ hcol => ?_).symm
    simp only [Sudan.coeffsOf]
    rw [dite_eq_right fun h => absurd h hcol, zero_mul]

/-- **The elimination interpolant has least `Y`-degree** among all multiplicity-`m` interpolants. -/
theorem natDegree_interpolant_le (α w : ι → F) {m d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials d D)) {Q : F[X][Y]}
    (hQ : IsInterpolant α w m d D Q) :
    (interpolant α w m d D).natDegree ≤ Q.natDegree := by
  obtain ⟨j, -, hlt, hcoeffs⟩ := exists_interpolant_eq (α := α) (w := w) hd hn
  have hdeg : Q.natDegree ≤ D / d := (Nat.le_div_iff_mul_le hd).2 hQ.natDegree_mul_le
  have hj : (j : ℕ) ≤ Q.natDegree := by
    by_contra h
    push Not at h
    exact kernelVecUpTo_ne_zero hd hQ le_rfl
      (hlt ⟨Q.natDegree, Nat.lt_succ_of_le hdeg⟩ (Fin.lt_def.2 h))
  refine (natDegree_le_iff_coeff_eq_zero.2 fun b hb => ?_).trans hj
  ext a
  rw [interpolant, Sudan.coeff_coeff_bivariateOf, hcoeffs, coeff_zero]
  split_ifs
  · simp only [Sudan.coeffsOf]
    split_ifs with h
    · exact absurd (mem_filter.1 h).2 (not_le.2 hb)
    · rfl
  · rfl

end Interpolation

end Cslib.Code.GuruswamiSudan

/-! ### Guruswami–Sudan list decoder for Reed–Solomon codes -/

namespace Cslib.Code

open Finset Polynomial

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]

/-- **Guruswami–Sudan list decoder** [GuruswamiSudan1999] for Reed–Solomon codes of dimension `k`,
multiplicity `m`, and `(1, k - 1)`-weighted degree bound `D`: the roots `P` in `F[X]` of the
least-`Y`-degree multiplicity-`m` interpolant `GuruswamiSudan.interpolant α w m (k - 1) D` that
have degree less than `k` and satisfy `D < m * #{i | P.eval (α i) = w i}`. Roots in `F[X][Y]` are
taken noncomputably via `Polynomial.roots`. -/
noncomputable def guruswamiSudan (α w : ι → F) (m k D : ℕ) : Finset F[X] :=
  {P ∈ (GuruswamiSudan.interpolant α w m (k - 1) D).roots.toFinset |
    P.degree < k ∧ D < m * #{i | P.eval (α i) = w i}}

variable {α w : ι → F} {m k D : ℕ} {P : F[X]}

/-- Every polynomial returned by `guruswamiSudan` has degree less than `k` and satisfies
`D < m * #{i | P.eval (α i) = w i}`. -/
theorem degree_lt_and_lt_mul_card_of_mem_guruswamiSudan (h : P ∈ guruswamiSudan α w m k D) :
    P.degree < k ∧ D < m * #{i | P.eval (α i) = w i} :=
  (mem_filter.1 h).2

/-- The list size of `guruswamiSudan` is at most the `Y`-degree of the elimination interpolant. -/
theorem card_guruswamiSudan_le_natDegree :
    #(guruswamiSudan α w m k D) ≤ (GuruswamiSudan.interpolant α w m (k - 1) D).natDegree :=
  (card_filter_le _ _).trans (Multiset.toFinset_card_le _ |>.trans (card_roots' _))

/-- The list size of `guruswamiSudan` is always at most `D` (including the case `k = 1`). -/
theorem card_guruswamiSudan_le : #(guruswamiSudan α w m k D) ≤ D :=
  card_guruswamiSudan_le_natDegree.trans (GuruswamiSudan.natDegree_interpolant_le_bound _ _ _ _ _)

/-- **List size of the Guruswami–Sudan decoder.** The list size `L` satisfies `L * (k - 1) ≤ D`,
so at most `D / (k - 1)` polynomials are returned when `k ≥ 2`. -/
theorem card_guruswamiSudan_mul_le : #(guruswamiSudan α w m k D) * (k - 1) ≤ D :=
  (Nat.mul_le_mul_right _ card_guruswamiSudan_le_natDegree).trans
    (GuruswamiSudan.weightedDegreeLE_interpolant α w m (k - 1) D).natDegree_mul_le

/-- **Completeness and soundness of Guruswami–Sudan list decoding.** With distinct points `α`,
`k ≥ 2`, and `|ι| * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D)`, the decoder lists exactly
the polynomials of degree less than `k` with `D < m * #{i | P.eval (α i) = w i}`. -/
theorem mem_guruswamiSudan_iff (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D)) :
    P ∈ guruswamiSudan α w m k D ↔ P.degree < k ∧ D < m * #{i | P.eval (α i) = w i} := by
  refine ⟨degree_lt_and_lt_mul_card_of_mem_guruswamiSudan, fun hP => ?_⟩
  have hQ := GuruswamiSudan.isInterpolant_interpolant α w (by omega) hn
  have hPdeg : P.natDegree ≤ k - 1 := by
    rcases eq_or_ne P 0 with rfl | hP0
    · simp
    · have := (natDegree_lt_iff_degree_lt hP0).2 hP.1
      omega
  exact mem_filter.2 ⟨Multiset.mem_toFinset.2 (hQ.mem_roots hα hPdeg hP.2), hP⟩

/-- **Guruswami–Sudan list decoding** [GuruswamiSudan1999] under the closed-form condition
`|ι| * (k - 1) * m * (m + 1) < (D + 1) * (D + 2)`. -/
theorem mem_guruswamiSudan_iff_of_lt (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : Fintype.card ι * (k - 1) * m * (m + 1) < (D + 1) * (D + 2)) :
    P ∈ guruswamiSudan α w m k D ↔ P.degree < k ∧ D < m * #{i | P.eval (α i) = w i} :=
  mem_guruswamiSudan_iff hα hk (GuruswamiSudan.card_mul_lt_card_monomials_of_lt (by omega) hn)

/-- Every Reed–Solomon codeword agreeing with `w` at more than `D / m` points is decoded by
`guruswamiSudan`. -/
theorem exists_mem_guruswamiSudan_of_mem_reedSolomon (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : Fintype.card ι * (k - 1) * m * (m + 1) < (D + 1) * (D + 2)) {c : ι → F}
    (hc : c ∈ reedSolomon α k) (hagree : D < m * #{i | c i = w i}) :
    ∃ P ∈ guruswamiSudan α w m k D, (fun i => P.eval (α i)) = c := by
  obtain ⟨P, hP, rfl⟩ := mem_reedSolomon.1 hc
  exact ⟨P, (mem_guruswamiSudan_iff_of_lt hα hk hn).2 ⟨hP, hagree⟩, rfl⟩

/-! ### List decoding up to the full Johnson radius -/

/-- Exact integer Johnson-bound parameter choice: whenever `n * d < t ^ 2`, choosing
`m = n * d / (t ^ 2 - n * d) + 1` and `D = m * t - 1` satisfies the Guruswami–Sudan interpolation
inequality `n * d * m * (m + 1) < (D + 1) * (D + 2)`. -/
theorem guruswamiSudan_johnson_ineq {n d t : ℕ} (ht : n * d < t ^ 2) :
    let m := n * d / (t ^ 2 - n * d) + 1
    let D := m * t - 1
    1 ≤ m ∧ D + 1 = m * t ∧ n * d * m * (m + 1) < (D + 1) * (D + 2) := by
  intro m D
  have hpos_Δ : 0 < t ^ 2 - n * d := Nat.sub_pos_of_lt ht
  have ht_pos : 0 < t := by
    by_contra h0
    have ht0 : t = 0 := by omega
    subst ht0
    simp at ht
  have hm_pos : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le _)
  have hmt_pos : 1 ≤ m * t := Nat.mul_pos hm_pos ht_pos
  have hD1 : D + 1 = m * t := Nat.sub_add_cancel hmt_pos
  have hD2 : D + 2 = m * t + 1 := by omega
  have hdiv : n * d < m * (t ^ 2 - n * d) := by
    have hlt := Nat.lt_mul_div_succ (n * d) hpos_Δ
    simpa [m, Nat.mul_comm] using hlt
  have hstep : n * d * (m + 1) < t * (m * t + 1) := by
    have hsq : m * (t ^ 2 - n * d) + m * (n * d) = m * t ^ 2 := by
      rw [← Nat.mul_add, Nat.sub_add_cancel ht.le]
    nlinarith
  refine ⟨hm_pos, hD1, ?_⟩
  rw [hD1, hD2]
  have hmul := Nat.mul_lt_mul_of_pos_left hstep hm_pos
  linarith

/-- **Guruswami–Sudan list decoding up to the exact integer Johnson radius** [GuruswamiSudan1999].
With distinct points `α`, `k ≥ 2`, and `n * (k - 1) < (n - e) ^ 2` (equivalently
`e < n - √(n * (k - 1))`), choosing `m = n * (k - 1) / ((n - e) ^ 2 - n * (k - 1)) + 1` and
`D = m * (n - e) - 1`, `guruswamiSudan α w m k D` lists exactly the polynomials of degree less than
`k` whose codeword is within Hamming distance `e` of `w`. -/
theorem mem_guruswamiSudan_johnson_iff (hα : Function.Injective α) (hk : 2 ≤ k) {e : ℕ}
    (he : Fintype.card ι * (k - 1) < (Fintype.card ι - e) ^ 2) :
    let n := Fintype.card ι
    let m := n * (k - 1) / ((n - e) ^ 2 - n * (k - 1)) + 1
    let D := m * (n - e) - 1
    P ∈ guruswamiSudan α w m k D ↔
      P.degree < k ∧ hammingDist (fun i => P.eval (α i)) w ≤ e := by
  intro n m D
  obtain ⟨hm, hD1, hineq⟩ := guruswamiSudan_johnson_ineq he
  change 1 ≤ m at hm
  change D + 1 = m * (n - e) at hD1
  rw [mem_guruswamiSudan_iff_of_lt hα hk hineq]
  have hne : e ≤ n := by
    by_contra hgt
    have hsub : n - e = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hgt)
    rw [hsub] at he
    simp at he
  have hcard_sum : #{i | P.eval (α i) = w i} + hammingDist (fun i => P.eval (α i)) w = n := by
    change #{i | P.eval (α i) = w i} + hammingDist (fun i => P.eval (α i)) w = Fintype.card ι
    rw [hammingDist, ← card_univ]
    exact card_filter_add_card_filter_not _
  constructor
  · rintro ⟨hdeg, hagree⟩
    refine ⟨hdeg, ?_⟩
    change D < m * #{i | P.eval (α i) = w i} at hagree
    have hmt : m * (n - e) ≤ m * #{i | P.eval (α i) = w i} := by omega
    have hle : n - e ≤ #{i | P.eval (α i) = w i} := Nat.le_of_mul_le_mul_left hmt hm
    omega
  · rintro ⟨hdeg, hdist⟩
    refine ⟨hdeg, ?_⟩
    change D < m * #{i | P.eval (α i) = w i}
    have hle : n - e ≤ #{i | P.eval (α i) = w i} := by omega
    have hmt : m * (n - e) ≤ m * #{i | P.eval (α i) = w i} := Nat.mul_le_mul_left m hle
    omega

/-- **Asymptotic / real Johnson-bound corollary** [GuruswamiSudan1999, Theorem 12]. For any
nonempty set of `n` distinct evaluation points `α`, dimension `2 ≤ k ≤ n`, and any `ε > 0`, there
exist multiplicity `m` (bounded by `⌊1 / (2 * ε)⌋₊ + 1`, independent of `n` and `k`) and weighted
degree `D < m * n` such that for every received word `w`, `guruswamiSudan α w m k D` recovers every
polynomial `P` of degree less than `k` within relative Hamming distance
`1 - √(k / n) - ε`, with list size bounded by `D / (k - 1)` (in particular
`#(guruswamiSudan α w m k D) ≤ (1 / (2 * ε) + 1) / ((k - 1) / n)`). -/
theorem exists_guruswamiSudan_of_eps [Nonempty ι] (hα : Function.Injective α)
    (hk : 2 ≤ k) (hkn : k ≤ Fintype.card ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ m D : ℕ, 1 ≤ m ∧ m ≤ ⌊1 / (2 * ε)⌋₊ + 1 ∧ D < m * Fintype.card ι ∧
      ∀ (w : ι → F),
        #(guruswamiSudan α w m k D) * (k - 1) ≤ D ∧
        ∀ P : F[X], P.degree < k →
          (hammingDist (fun i => P.eval (α i)) w : ℝ) ≤
            (1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - ε) * Fintype.card ι →
          P ∈ guruswamiSudan α w m k D := by
  set n := Fintype.card ι
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  set ρ : ℝ := (k : ℝ) / n
  set ρ' : ℝ := ((k - 1 : ℕ) : ℝ) / n
  by_cases hgap : 1 < Real.sqrt ρ + ε
  · refine ⟨1, 0, le_rfl, Nat.le_add_left 1 _, by simpa using hn0, fun w => ?_⟩
    refine ⟨by simpa using card_guruswamiSudan_mul_le (α := α) (w := w) (m := 1) (k := k) (D := 0),
      fun P _ hdist => ?_⟩
    have hnonneg : (0 : ℝ) ≤ hammingDist (fun i => P.eval (α i)) w := Nat.cast_nonneg _
    have hneg : (1 - Real.sqrt ρ - ε) * n < 0 := mul_neg_of_neg_of_pos (by linarith) hnR
    linarith
  · push Not at hgap
    have hρ'pos : 0 < ρ' := by
      have : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
      exact div_pos this hnR
    have hρ'le1 : ρ' ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast (by omega : k - 1 ≤ n)
    have hρ'leρ : ρ' ≤ ρ := by
      dsimp only [ρ', ρ]
      gcongr
      exact_mod_cast Nat.sub_le k 1
    have hsqrt_le1 : Real.sqrt ρ' ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact hρ'le1
    set m : ℕ := ⌊Real.sqrt ρ' / (2 * ε)⌋₊ + 1
    set t : ℕ := ⌈(Real.sqrt ρ + ε) * n⌉₊
    set D : ℕ := m * t - 1
    have hm_pos : 1 ≤ m := Nat.le_add_left 1 _
    have hm_bound : m ≤ ⌊1 / (2 * ε)⌋₊ + 1 := by
      dsimp only [m]
      gcongr
    have ht_ge : (Real.sqrt ρ + ε) * n ≤ (t : ℝ) := Nat.le_ceil _
    have ht_pos : 0 < t := by
      have hpos : (0 : ℝ) < (Real.sqrt ρ + ε) * n := mul_pos (by positivity) hnR
      exact_mod_cast hpos.trans_le ht_ge
    have ht_le_n : t ≤ n := by
      refine Nat.ceil_le.2 ?_
      nlinarith
    have hmt_pos : 1 ≤ m * t := Nat.mul_pos hm_pos ht_pos
    have hD_lt : D < m * n := by
      have hmt_le : m * t ≤ m * n := Nat.mul_le_mul_left m ht_le_n
      omega
    have hD1 : D + 1 = m * t := Nat.sub_add_cancel hmt_pos
    have hD2 : D + 2 = m * t + 1 := by omega
    have hm_gt : Real.sqrt ρ' / (2 * ε) < (m : ℝ) := by
      simpa [m] using Nat.lt_floor_add_one (Real.sqrt ρ' / (2 * ε))
    have hsqrt_le : Real.sqrt ρ' ≤ Real.sqrt ρ := Real.sqrt_le_sqrt hρ'leρ
    have ht_ge' : (Real.sqrt ρ' + ε) * n ≤ (t : ℝ) := by nlinarith
    have htsq : (ρ' + 2 * ε * Real.sqrt ρ' + ε ^ 2) * (n : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 := by
      have h1 : ((Real.sqrt ρ' + ε) * n) ^ 2 ≤ (t : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) ht_ge' 2
      have h2 : ((Real.sqrt ρ' + ε) * n) ^ 2 =
          (ρ' + 2 * ε * Real.sqrt ρ' + ε ^ 2) * (n : ℝ) ^ 2 := by
        have hsq : Real.sqrt ρ' ^ 2 = ρ' := Real.sq_sqrt hρ'pos.le
        ring_nf
        rw [hsq]
        ring
      linarith
    have hmul_gt : ρ' < (m : ℝ) * (2 * ε * Real.sqrt ρ') := by
      have h1 : Real.sqrt ρ' < (m : ℝ) * (2 * ε) := (div_lt_iff₀ (by positivity)).1 hm_gt
      have h2 := mul_lt_mul_of_pos_right h1 (Real.sqrt_pos.2 hρ'pos)
      have hsq : Real.sqrt ρ' * Real.sqrt ρ' = ρ' := Real.mul_self_sqrt hρ'pos.le
      linarith
    have hnd_eq : (n : ℝ) * ((k - 1 : ℕ) : ℝ) = ρ' * (n : ℝ) ^ 2 := by
      dsimp only [ρ']
      field_simp
    have hstepR :
        (n : ℝ) * ((k - 1 : ℕ) : ℝ) * ((m : ℝ) + 1) < (t : ℝ) * ((m : ℝ) * (t : ℝ) + 1) := by
      have h1 : (n : ℝ) * ((k - 1 : ℕ) : ℝ) <
          (m : ℝ) * ((t : ℝ) ^ 2 - (n : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
        have hdiff : (2 * ε * Real.sqrt ρ' + ε ^ 2) * (n : ℝ) ^ 2 ≤
            (t : ℝ) ^ 2 - (n : ℝ) * ((k - 1 : ℕ) : ℝ) := by
          rw [hnd_eq]
          linarith
        have hstrict : ρ' * (n : ℝ) ^ 2 <
            (m : ℝ) * ((2 * ε * Real.sqrt ρ' + ε ^ 2) * (n : ℝ) ^ 2) := by
          have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
          have hpos_eps : (0 : ℝ) < (m : ℝ) * ε ^ 2 := by positivity
          have : ρ' < (m : ℝ) * (2 * ε * Real.sqrt ρ' + ε ^ 2) := by nlinarith
          rw [← mul_assoc]
          exact mul_lt_mul_of_pos_right this hn2
        have hle_m : (m : ℝ) * ((2 * ε * Real.sqrt ρ' + ε ^ 2) * (n : ℝ) ^ 2) ≤
            (m : ℝ) * ((t : ℝ) ^ 2 - (n : ℝ) * ((k - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg m)
        rw [← hnd_eq] at hstrict
        exact hstrict.trans_le hle_m
      have htR : (0 : ℝ) < t := Nat.cast_pos.2 ht_pos
      nlinarith
    have hstepN : n * (k - 1) * (m + 1) < t * (m * t + 1) := by exact_mod_cast hstepR
    have hineq : n * (k - 1) * m * (m + 1) < (D + 1) * (D + 2) := by
      rw [hD1, hD2]
      have hmul := Nat.mul_lt_mul_of_pos_left hstepN hm_pos
      linarith
    refine ⟨m, D, hm_pos, hm_bound, hD_lt,
      fun w => ⟨card_guruswamiSudan_mul_le, fun P hP hdist => ?_⟩⟩
    rw [mem_guruswamiSudan_iff_of_lt hα hk hineq]
    refine ⟨hP, ?_⟩
    have hcard_sum : #{i | P.eval (α i) = w i} + hammingDist (fun i => P.eval (α i)) w = n := by
      change #{i | P.eval (α i) = w i} + hammingDist (fun i => P.eval (α i)) w = Fintype.card ι
      rw [hammingDist, ← card_univ]
      exact card_filter_add_card_filter_not _
    have hcard_sumR : (#{i | P.eval (α i) = w i} : ℝ) +
        (hammingDist (fun i => P.eval (α i)) w : ℝ) = n := by
      exact_mod_cast hcard_sum
    have hagreeR : (Real.sqrt ρ + ε) * n ≤ (#{i | P.eval (α i) = w i} : ℝ) := by linarith
    have htle : t ≤ #{i | P.eval (α i) = w i} := Nat.ceil_le.2 hagreeR
    have hmt : m * t ≤ m * #{i | P.eval (α i) = w i} := Nat.mul_le_mul_left m htle
    omega

end Cslib.Code
