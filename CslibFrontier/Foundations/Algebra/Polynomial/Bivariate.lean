/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate (Mathlib, bivariate shifts, Hasse derivatives, weighted degree)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Radical.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Bivariate polynomial shifts, Hasse derivatives, vanishing order, and weighted degree

General algebra for bivariate polynomials `Q : R[X][Y]` represented as iterated univariate
polynomials `(Polynomial (Polynomial R))`, independent of coding theory:

1. **Bivariate shifts and Hasse derivatives.** The Taylor shift `Q(X + x, Y + y)`
   (`Polynomial.Bivariate.shift`) is a ring homomorphism `R[X][Y] →+* R[X][Y]` whose `(i, j)`-th
   coefficient is the evaluation at `(x, y)` of the `(i, j)`-th bivariate Hasse derivative
   `Polynomial.Bivariate.hasseDerivBiv i j Q`
   (`Polynomial.Bivariate.coeff_coeff_shift_eq_evalEval_hasseDerivBiv`). Because Hasse derivatives
   avoid division by factorials, the theory works over arbitrary commutative semirings and fields
   of any characteristic and commutes with arbitrary ring homomorphisms
   (`Polynomial.Bivariate.map_shift`).
2. **Multiplicity-`m` vanishing.** `Polynomial.Bivariate.VanishesToOrder m x y Q` asserts that
   every monomial `X ^ i * Y ^ j` with `i + j < m` vanishes in `shift x y Q`, equivalently that
   all bivariate Hasse derivatives of total order `< m` vanish at `(x, y)`
   (`Polynomial.Bivariate.vanishesToOrder_iff_hasseDerivBiv`). Over any commutative ring,
   `VanishesToOrder m x (P.eval x) Q` implies `(X - C x) ^ m ∣ Q.eval P`
   (`Polynomial.Bivariate.VanishesToOrder.X_sub_C_pow_dvd_eval`).
3. **`(1, d)`-weighted degree.** `Polynomial.Bivariate.weightedDegree d Q` is the maximum of
   `a + d * b` over nonzero monomials `X ^ a * Y ^ b` of `Q`. Over a domain it is additive on
   nonzero products (`Polynomial.Bivariate.weightedDegree_mul`), monotone under division
   (`Polynomial.Bivariate.weightedDegree_le_of_dvd`), and evaluates to `d` on `Y - C P` whenever
   `P.natDegree ≤ d` (`Polynomial.Bivariate.weightedDegree_X_sub_C`).
4. **Factor refinement.** Primitive, square-free (`radical Q.primPart`), exact root-multiplicity,
   and primitive irreducible factorizations in `F[X][Y]` over arbitrary fields
   (`Polynomial.Bivariate.eval_radical_primPart_eq_zero_iff`,
   `Polynomial.Bivariate.exists_eq_pow_mul_eval_ne_zero`,
   `Polynomial.Bivariate.exists_eq_C_mul_prod_irreducible`).

## Main definitions

* `Polynomial.Bivariate.shift`: the bivariate Taylor shift `Q(X + x, Y + y)`.
* `Polynomial.Bivariate.hasseDerivX`, `Polynomial.Bivariate.hasseDerivBiv`: bivariate Hasse
  derivatives in `X` and in `(X, Y)`.
* `Polynomial.Bivariate.VanishesToOrder`: multiplicity-`m` vanishing at `(x, y)`.
* `Polynomial.Bivariate.weightedDegree`: the `(1, d)`-weighted degree of a bivariate polynomial.

## Main results

* `Polynomial.Bivariate.coeff_coeff_shift_eq_evalEval_hasseDerivBiv`,
  `Polynomial.Bivariate.vanishesToOrder_iff_hasseDerivBiv`: bivariate Taylor / Hasse derivative
  characterization of multiplicity vanishing.
* `Polynomial.Bivariate.map_shift`, `Polynomial.Bivariate.VanishesToOrder.map`: base change for
  bivariate shifts and vanishing order under arbitrary ring homomorphisms.
* `Polynomial.Bivariate.VanishesToOrder.X_sub_C_pow_dvd_eval`: multiplicity-`m` vanishing at
  `(x, P(x))` implies `(X - C x) ^ m ∣ Q.eval P`.
* `Polynomial.Bivariate.weightedDegree_mul`, `Polynomial.Bivariate.weightedDegree_le_of_dvd`,
  `Polynomial.Bivariate.weightedDegree_X_sub_C`,
  `Polynomial.Bivariate.weightedDegree_le_of_X_sub_C_pow_mul`: additivity, divisibility
  monotonicity, and linear-factor laws for `(1, d)`-weighted degree.
* `Polynomial.Bivariate.eval_radical_primPart_eq_zero_iff`,
  `Polynomial.Bivariate.exists_eq_pow_mul_eval_ne_zero`,
  `Polynomial.Bivariate.exists_eq_C_mul_prod_irreducible`,
  `Polynomial.Bivariate.sum_weightedDegree_le_of_eq_C_mul_prod`: square-free, exact-multiplicity,
  and primitive irreducible factor refinement in `F[X][Y]`.
-/

public section

open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

open Finset Polynomial

/-! ### Bivariate shift and Hasse derivatives -/

section Shift

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The bivariate Taylor shift `Q(X + x, Y + y)` as a ring homomorphism `R[X][Y] →+* R[X][Y]`. -/
noncomputable def shift (x y : R) : R[X][Y] →+* R[X][Y] :=
  (taylorAlgHom (C y) : R[X][Y] →+* R[X][Y]).comp
    (Polynomial.mapRingHom (taylorAlgHom x : R[X] →+* R[X]))

/-- Unfolding `shift x y Q` into nested univariate `Polynomial.taylor` shifts. -/
theorem shift_apply (x y : R) (Q : R[X][Y]) :
    shift x y Q = taylor (C y) (Q.map (taylorAlgHom x : R[X] →+* R[X])) := by
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
  by_cases h : b = b' <;> simp [h]

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
@[expose] def VanishesToOrder (m : ℕ) (x y : R) (Q : R[X][Y]) : Prop :=
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
  -- Write `P(X + x) = C y + X * R₀`.
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

/-! ### `(1, d)`-weighted degree -/

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
      exact hQ (by ext b : 2; rw [h b, coeff_zero])
    obtain ⟨a, ha⟩ : ∃ a, (Q.coeff b).coeff a ≠ 0 := by
      by_contra h
      push Not at h
      exact hb (by ext a; rw [h a, coeff_zero])
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
      simp
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

/-- Division by `(Y - C P) ^ r` lowers the `(1, d)`-weighted degree bound by `r * d`. -/
theorem weightedDegree_le_of_X_sub_C_pow_mul {R : Type*} [CommRing R] [IsDomain R]
    {d D r : ℕ} {P : R[X]} (hP : P.natDegree ≤ d) {S : R[X][Y]}
    (h : weightedDegree d ((Y - C P) ^ r * S) ≤ D) :
    weightedDegree d S ≤ D - r * d := by
  rcases eq_or_ne S 0 with rfl | hS0
  · simp
  · rw [weightedDegree_mul (pow_ne_zero r (X_sub_C_ne_zero P)) hS0,
      weightedDegree_X_sub_C_pow hP r] at h
    omega

/-- Over a commutative domain, `(1, d)`-weighted degree is additive on products of nonzero
bivariate polynomials. -/
theorem weightedDegree_multiset_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] {d : ℕ}
    {fs : Multiset R[X][Y]} (hfs : ∀ P ∈ fs, P ≠ 0) :
    weightedDegree d fs.prod = (fs.map (weightedDegree d)).sum := by
  induction fs using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    have hP0 : P ≠ 0 := hfs P (Multiset.mem_cons_self P s)
    have : Nontrivial R[X][Y] := ⟨P, 0, hP0⟩
    have hs0 : ∀ P' ∈ s, P' ≠ 0 := fun P' hP' => hfs P' (Multiset.mem_cons_of_mem hP')
    have hsprod : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => hs0 0 h0 rfl
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      weightedDegree_mul hP0 hsprod, ih hs0]

/-- If `Q = C c * fs.prod` with `c ≠ 0` and nonzero factors in `fs`, then the `(1, d)`-weighted
degrees of the factors sum to at most `weightedDegree d Q`, and every factor has `(1, d)`-weighted
degree at most `weightedDegree d Q`. -/
theorem sum_weightedDegree_le_of_eq_C_mul_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    {d : ℕ} {Q : R[X][Y]} {c : R[X]} {fs : Multiset R[X][Y]} (hc : c ≠ 0)
    (hfs : ∀ P ∈ fs, P ≠ 0) (hQeq : Q = C c * fs.prod) :
    (fs.map (weightedDegree d)).sum ≤ weightedDegree d Q ∧
      ∀ P ∈ fs, weightedDegree d P ≤ weightedDegree d Q := by
  have : Nontrivial R[X][Y] := ⟨C c, 0, C_ne_zero.2 hc⟩
  have hprod_ne : fs.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => hfs 0 h0 rfl
  have hQ0 : Q ≠ 0 := by
    rw [hQeq]
    exact mul_ne_zero (C_ne_zero.2 hc) hprod_ne
  have hle : weightedDegree d fs.prod ≤ weightedDegree d Q :=
    weightedDegree_le_of_dvd hQ0 ⟨C c, by rw [hQeq, mul_comm]⟩
  refine ⟨(weightedDegree_multiset_prod hfs).symm.trans_le hle, fun P hP => ?_⟩
  exact weightedDegree_le_of_dvd hQ0 ((Multiset.dvd_prod hP).trans ⟨C c, by rw [hQeq, mul_comm]⟩)

end WeightedDegree

/-! ### Factor refinement over arbitrary fields (primitive, square-free, irreducible) -/

section FactorRefinement

open UniqueFactorizationMonoid

variable {F : Type*} [Field F]

section PrimRadical

variable [DecidableEq F]

/-- `Q.primPart` has `(1, d)`-weighted degree at most that of `Q`. -/
theorem weightedDegree_primPart_le (d : ℕ) (Q : F[X][Y]) :
    weightedDegree d Q.primPart ≤ weightedDegree d Q := by
  rcases eq_or_ne Q 0 with rfl | hQ0
  · simp
  · exact weightedDegree_le_of_dvd hQ0 Q.primPart_dvd

/-- For `Q ≠ 0`, `Q` and its primitive part `Q.primPart` have the same roots in `F[X]`. -/
theorem eval_primPart_eq_zero_iff {Q : F[X][Y]} (hQ : Q ≠ 0) (P : F[X]) :
    Q.primPart.eval P = 0 ↔ Q.eval P = 0 := by
  conv_rhs => rw [Q.eq_C_content_mul_primPart]
  rw [eval_mul, eval_C, mul_eq_zero]
  have hc : Q.content ≠ 0 := mt content_eq_zero_iff.1 hQ
  simp [hc]

/-- `radical Q.primPart` has `(1, d)`-weighted degree at most that of `Q`. -/
theorem weightedDegree_radical_primPart_le (d : ℕ) (Q : F[X][Y]) :
    weightedDegree d (radical Q.primPart) ≤ weightedDegree d Q :=
  (weightedDegree_le_of_dvd (primPart_ne_zero Q) radical_dvd_self).trans
    (weightedDegree_primPart_le d Q)

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

/-- Every root `P` of a nonzero `Q : R[X][Y]` over a commutative ring factors out with exact
positive multiplicity `r`, derived from `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`.
-/
theorem exists_eq_pow_mul_eval_ne_zero {R : Type*} [CommRing R] {Q : R[X][Y]}
    (hQ : Q ≠ 0) {P : R[X]} (hQP : Q.eval P = 0) :
    ∃ (r : ℕ) (S : R[X][Y]), 1 ≤ r ∧ Q = (Y - C P) ^ r * S ∧ S.eval P ≠ 0 := by
  obtain ⟨S, hQS, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ P
  exact ⟨Q.rootMultiplicity P, S, (rootMultiplicity_pos hQ).2 hQP, hQS,
    fun hSP => hndvd (dvd_iff_isRoot.2 hSP)⟩

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

end FactorRefinement

end Polynomial.Bivariate
