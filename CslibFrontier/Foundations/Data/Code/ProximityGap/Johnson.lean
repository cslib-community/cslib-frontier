/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.Polynomial.Bivariate
public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import CslibFrontier.Foundations.Data.Code.SudanInterpolant
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap
import CslibFrontier.Foundations.Data.Code.GuruswamiSudan
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.SeparableDegree
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.Positivity

/-!
# Proximity gaps for Reed–Solomon codes up to the Johnson bound

This file formalizes explicit-parameter Johnson-bound correlated-agreement steps and original
explicit-constant proximity-gap variants for Reed–Solomon codes over arbitrary fields of arbitrary
characteristic, following Ben-Sasson, Carmon, Ishai, Kopparty, and Saraf
[BenSassonCarmonIshaiKoppartySaraf2020]. All theorem and section locators below follow the
accepted *Journal of the ACM* (2023) manuscript (where Theorem 1.4 states correlated agreement /
proximity gaps over lines, Theorem 5.1 treats unweighted lines, Theorem 6.2 treats degree-`r`
curves, and Theorem 7.2 treats weighted correlated agreement; by contrast, Theorem 7.2 of the
July 2020 ePrint 2020/654 version concerns FRI soundness).

## Scope and relationship to the source theorems

* The four correlated-agreement theorems
  (`Cslib.Code.exists_weighted_correlatedAgreement_curve_johnson`,
  `Cslib.Code.exists_correlatedAgreement_curve_johnson`,
  `Cslib.Code.exists_weighted_correlatedAgreement_line_johnson`,
  `Cslib.Code.exists_correlatedAgreement_line_johnson`) are **explicit-parameter Guruswami–Sudan
  steps** parameterized directly by `(m, D)` (and integer weights `W : ι → ℕ` with `M`, `W_tot`,
  `B_W`) with explicit scalar threshold `Cslib.Code.ProximityGap.johnsonCurveBound`. Deriving the
  paper's displayed finite thresholds directly from the source hypotheses, as well as
  normalized/rational-valued weights and affine-space extensions, are left open outside this file.
* `Cslib.Code.proximityGap_line_johnson` and `Cslib.Code.proximityGap_line_johnson_of_eta` are
  **original explicit-constant variants** in the setting of
  [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.4] (accepted JACM 2023 manuscript) with
  exceptional fraction `1800 * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)` (respectively
  `115200 * n ^ 2 / (ρ * η ^ 6 * |F|)`). While the exponents `(m + 1) ^ 6 / ρ` are asymptotically
  smaller in `m` and `1 / ρ` than the displayed `(m + 1 / 2) ^ 7 / (3 * ρ ^ (3 / 2))` coefficient
  of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 5.1, p. 17] (accepted NSF/JACM manuscript;
  Theorem 1.4 instead references Theorem 1.2's `η`-dependent expression), the bound is not
  uniformly smaller at small finite `m` (e.g., at `m = 3`, `ρ = 1 / 4`, the coefficients are
  `29,491,200` vs. approximately `17,157`), so these bounds do not imply the paper's displayed
  finite constant for all finite `m`.

## Main definitions

* `Cslib.Code.ProximityGap.maxYDeg`: maximum `Y`-degree of monomials in `Sudan.monomials d D`.
* `Cslib.Code.ProximityGap.siegelZDeg`: explicit `Z`-degree bound for zero-denominator Siegel
  interpolation of a degree-`r` polynomial curve.
* `Cslib.Code.ProximityGap.johnsonCurveBound`: explicit `|F|`-independent bound on the number of
  exceptional scalars on a degree-`r` curve with integer coordinate weights summing to at most
  `W_tot`.

## Main results

* `Cslib.Code.ProximityGap.exists_separable_contraction`: positive-characteristic-safe separable
  contraction `S(Z, X, Y ^ μ) = R(Z, X, Y)` with Bézout witness `S * A + S' * B = C Δ` (`Δ ≠ 0`)
  for irreducible polynomials in `F[Z][X][Y]`.
* `Cslib.Code.ProximityGap.johnsonCurveBound_mul_le`: linear weight scaling of `johnsonCurveBound`
  from `n` to `W_tot ≥ n`.
* `Cslib.Code.ProximityGap.johnson_curve_params_bound`,
  `Cslib.Code.ProximityGap.johnson_line_params_bound`,
  `Cslib.Code.ProximityGap.exists_multiplicity_of_eta`: quantitative Guruswami–Sudan parameter
  packaging up to `1 - √ρ - √ρ / (2 * m)` yielding
  `johnsonCurveBound n (m + 1) (k - 1) D r n ≤ 1800 * r * (m + 1) ^ 6 * n ^ 2 / ρ`, together
  with multiplicity selection for any gap `η > 0` below `1 - √ρ`.
* `Cslib.Code.exists_weighted_correlatedAgreement_curve_johnson`: explicit-parameter
  integer-weighted correlated-agreement step on degree-`r` curves over arbitrary fields of
  arbitrary characteristic (toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 5.1, 6.2,
  and 7.2], accepted JACM 2023 manuscript).
* `Cslib.Code.exists_correlatedAgreement_line_johnson`: explicit-parameter unweighted
  correlated-agreement step on lines over arbitrary fields (toward
  [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 5.1], accepted JACM 2023 manuscript).
* `Cslib.Code.exists_correlatedAgreement_curve_johnson`: explicit-parameter unweighted
  correlated-agreement step on degree-`r` curves over arbitrary fields (toward
  [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.2], accepted JACM 2023 manuscript).
* `Cslib.Code.exists_weighted_correlatedAgreement_line_johnson`: explicit-parameter
  integer-weighted correlated-agreement step on lines over arbitrary fields (toward
  [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 7.2], accepted JACM 2023 manuscript).
* `Cslib.Code.proximityGap_line_johnson`, `Cslib.Code.proximityGap_line_johnson_of_eta`:
  original explicit-constant finite-field proximity-gap variants on affine lines up to the
  Johnson bound `1 - √ρ` (variants of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.4],
  accepted JACM 2023 manuscript).

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [V. Guruswami, M. Sudan, *Improved Decoding of Reed–Solomon and Algebraic-Geometry Codes*]
  [GuruswamiSudan1999]
-/

namespace Cslib.Code.ProximityGap

open Cslib.Code Cslib.Code.GuruswamiSudan Finset Polynomial Polynomial.Bivariate

@[expose] public section

/-- Maximum `Y`-degree among monomials `(a, b)` in `Sudan.monomials d D`. -/
def maxYDeg (d D : ℕ) : ℕ :=
  (Sudan.monomials d D).sup Prod.snd

/-- Explicit `Z`-degree budget for zero-denominator Siegel interpolation of a degree-`r` curve. -/
def siegelZDeg (n m d D r : ℕ) : ℕ :=
  let R_eq := n * (m * (m + 1) / 2)
  let C_mon := #(Sudan.monomials d D)
  (R_eq * r * maxYDeg d D) / (C_mon - R_eq)

/-- Explicit `|F|`-independent upper bound on exceptional scalars for Johnson-bound weighted
correlated agreement on degree-`r` curves. -/
def johnsonCurveBound (n m d D r W_tot : ℕ) : ℕ :=
  let D_Y := maxYDeg d D
  let B_Z := siegelZDeg n m d D r
  B_Z + 2 * D_Y * (D + B_Z) + W_tot * D_Y ^ 2 * (4 * D * B_Z + r * D_Y)

end

section SwapAndDegZ

/-- Ring equivalence moving the innermost variable `Z` of `R[Z][X][Y]` to the outermost position
`(R[X][Y])[Z]`. -/
private noncomputable def toOuterZ (R : Type*) [CommSemiring R] : R[X][X][X] ≃+* R[X][X][X] :=
  (Polynomial.mapEquiv (Bivariate.swap (R := R)).toRingEquiv).trans
    (Bivariate.swap (R := R[X])).toRingEquiv

private theorem coeff_coeff_coeff_toOuterZ {R : Type*} [CommSemiring R] (Q : R[X][X][X])
    (t a b : ℕ) :
    ((((toOuterZ R Q).coeff t).coeff b).coeff a) = ((Q.coeff b).coeff a).coeff t := by
  change (((Bivariate.swap (Q.map (Bivariate.swap (R := R)).toRingEquiv.toRingHom)).coeff t).coeff
    b).coeff a = _
  rw [coeff_coeff_swap, coeff_map]
  exact coeff_coeff_swap (Q.coeff b) t a

/-- `Z`-degree of `f ∈ R[Z][X]`. -/
private noncomputable def degZ₂ {R : Type*} [CommSemiring R] (f : R[X][X]) : ℕ :=
  (Bivariate.swap f).natDegree

private theorem degZ₂_zero {R : Type*} [CommSemiring R] : degZ₂ (0 : R[X][X]) = 0 := by
  simp [degZ₂]

private theorem degZ₂_one {R : Type*} [CommSemiring R] : degZ₂ (1 : R[X][X]) = 0 := by
  rw [degZ₂, map_one, natDegree_one]

private theorem degZ₂_neg {R : Type*} [CommRing R] (f : R[X][X]) : degZ₂ (-f) = degZ₂ f := by
  simp [degZ₂]

private theorem degZ₂_add_le {R : Type*} [CommSemiring R] (f g : R[X][X]) :
    degZ₂ (f + g) ≤ max (degZ₂ f) (degZ₂ g) := by
  simpa [degZ₂, map_add] using natDegree_add_le (Bivariate.swap f) (Bivariate.swap g)

private theorem degZ₂_mul_le {R : Type*} [CommSemiring R] (f g : R[X][X]) :
    degZ₂ (f * g) ≤ degZ₂ f + degZ₂ g := by
  simpa [degZ₂, map_mul] using natDegree_mul_le (p := Bivariate.swap f) (q := Bivariate.swap g)

private theorem degZ₂_mul {R : Type*} [CommRing R] [IsDomain R] {f g : R[X][X]}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    degZ₂ (f * g) = degZ₂ f + degZ₂ g := by
  rw [degZ₂, map_mul, natDegree_mul ((map_ne_zero_iff _ Bivariate.swap.injective).2 hf)
    ((map_ne_zero_iff _ Bivariate.swap.injective).2 hg)]
  rfl

private theorem degZ₂_le_iff {R : Type*} [CommSemiring R] {f : R[X][X]} {B : ℕ} :
    degZ₂ f ≤ B ↔ ∀ a, (f.coeff a).natDegree ≤ B :=
  Bivariate.natDegree_swap_le_iff f B

private theorem degZ₂_C {R : Type*} [CommSemiring R] (p : R[X]) :
    degZ₂ (C p) = p.natDegree :=
  le_antisymm (degZ₂_le_iff.2 fun a => by rw [coeff_C]; split_ifs <;> simp)
    (by simpa using degZ₂_le_iff.1 (le_refl (degZ₂ (C p))) 0)

private theorem degZ₂_X {R : Type*} [CommSemiring R] :
    degZ₂ (X : R[X][X]) = 0 :=
  Nat.eq_zero_of_le_zero (degZ₂_le_iff.2 fun a => by rw [coeff_X]; split_ifs <;> simp)

private theorem degZ₂_hasseDeriv_le {R : Type*} [CommSemiring R] (j : ℕ) (f : R[X][X]) :
    degZ₂ (hasseDeriv j f) ≤ degZ₂ f :=
  degZ₂_le_iff.2 fun a => by
    rw [hasseDeriv_coeff,
      show (((a + j).choose j : ℕ) : R[X]) = C (((a + j).choose j : ℕ) : R) by simp]
    exact natDegree_C_mul_le _ _ |>.trans (degZ₂_le_iff.1 le_rfl (a + j))

private theorem degZ₂_derivative_le {R : Type*} [CommSemiring R] (f : R[X][X]) :
    degZ₂ f.derivative ≤ degZ₂ f :=
  hasseDeriv_one' (f := f) ▸ degZ₂_hasseDeriv_le 1 f

private theorem natDegree_eval_C_le_degZ₂ {R : Type*} [CommSemiring R] (f : R[X][X]) (x : R) :
    (f.eval (C x)).natDegree ≤ degZ₂ f := by
  rw [eval_eq_sum_range]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun a _ => natDegree_mul_le.trans ?_)
  rw [← C_pow, natDegree_C, add_zero]
  exact degZ₂_le_iff.1 le_rfl a

private theorem degZ₂_taylor_C_le {R : Type*} [CommRing R] (f : R[X][X]) (x : R) :
    degZ₂ (taylor (C x) f) ≤ degZ₂ f :=
  degZ₂_le_iff.2 fun a => by
    rw [taylor_coeff]
    exact (natDegree_eval_C_le_degZ₂ _ x).trans (degZ₂_hasseDeriv_le a f)

/-- `Z`-degree of `Q ∈ R[Z][X][Y]`. -/
private noncomputable def degZ {R : Type*} [CommSemiring R] (Q : R[X][X][X]) : ℕ :=
  (toOuterZ R Q).natDegree

private theorem degZ_le_iff {R : Type*} [CommSemiring R] {Q : R[X][X][X]} {B : ℕ} :
    degZ Q ≤ B ↔ ∀ a b, ((Q.coeff b).coeff a).natDegree ≤ B := by
  rw [degZ, natDegree_le_iff_coeff_eq_zero]
  refine ⟨fun h a b => natDegree_le_iff_coeff_eq_zero.2 fun t ht => by
    simpa [coeff_coeff_coeff_toOuterZ] using
      congrArg (fun p : R[X][X] => (p.coeff b).coeff a) (h t ht),
    fun h t ht => by
      ext b a; rw [coeff_coeff_coeff_toOuterZ, coeff_zero, coeff_zero]
      exact coeff_eq_zero_of_natDegree_lt ((h a b).trans_lt ht)⟩

private theorem degZ_mul {R : Type*} [CommRing R] [IsDomain R] {A B : R[X][X][X]}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    degZ (A * B) = degZ A + degZ B := by
  rw [degZ, map_mul, natDegree_mul ((map_ne_zero_iff _ (toOuterZ R).injective).2 hA)
    ((map_ne_zero_iff _ (toOuterZ R).injective).2 hB)]
  rfl

private theorem degZ_le_of_dvd {R : Type*} [CommRing R] [IsDomain R] {A B : R[X][X][X]}
    (hB : B ≠ 0) (hdvd : A ∣ B) :
    degZ A ≤ degZ B := by
  rcases hdvd with ⟨C, rfl⟩
  have hA : A ≠ 0 := left_ne_zero_of_mul hB
  have hC : C ≠ 0 := right_ne_zero_of_mul hB
  rw [degZ_mul hA hC]
  exact Nat.le_add_right _ _

private theorem degZ₂_coeff_le_degZ {R : Type*} [CommSemiring R] (Q : R[X][X][X]) (b : ℕ) :
    degZ₂ (Q.coeff b) ≤ degZ Q :=
  degZ₂_le_iff.2 fun a => degZ_le_iff.1 le_rfl a b

/-- Bundler for subadditive degree-like measures `deg : R → ℕ` (covers `natDegree` in `R[X]` and
`degZ₂` in `R[X][X]`). -/
private structure DegBound (R : Type*) [CommRing R] where
  deg : R → ℕ
  zero : deg 0 = 0
  one : deg 1 = 0
  neg : ∀ x, deg (-x) = deg x
  add_le : ∀ x y, deg (x + y) ≤ max (deg x) (deg y)
  mul_le : ∀ x y, deg (x * y) ≤ deg x + deg y

private noncomputable def DegBound.natDegree (R : Type*) [CommRing R] : DegBound R[X] where
  deg := Polynomial.natDegree
  zero := natDegree_zero
  one := natDegree_one
  neg := natDegree_neg
  add_le := natDegree_add_le
  mul_le := fun _ _ => natDegree_mul_le

private noncomputable def DegBound.degZ₂ (R : Type*) [CommRing R] : DegBound R[X][X] where
  deg := ProximityGap.degZ₂
  zero := degZ₂_zero
  one := degZ₂_one
  neg := degZ₂_neg
  add_le := degZ₂_add_le
  mul_le := degZ₂_mul_le

private theorem DegBound.sub_le {R : Type*} [CommRing R] (db : DegBound R) (x y : R) :
    db.deg (x - y) ≤ max (db.deg x) (db.deg y) := by
  rw [sub_eq_add_neg]
  exact (db.add_le x (-y)).trans (by rw [db.neg])

private theorem DegBound.sum_le {R : Type*} [CommRing R] (db : DegBound R) {α : Type*}
    (s : Finset α) (u : α → R) {B : ℕ} (h : ∀ i ∈ s, db.deg (u i) ≤ B) :
    db.deg (∑ i ∈ s, u i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [db.zero]
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (db.add_le _ _).trans (max_le (h a (mem_insert_self a s))
      (ih fun i hi => h i (mem_insert_of_mem hi)))

private theorem DegBound.pow_le {R : Type*} [CommRing R] (db : DegBound R) (x : R) (n : ℕ) :
    db.deg (x ^ n) ≤ n * db.deg x := by
  induction n with
  | zero => simp [db.one]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (db.mul_le _ _).trans (Nat.add_le_add_right ih _)

private theorem DegBound.prod_le {R : Type*} [CommRing R] (db : DegBound R) {α : Type*}
    (s : Finset α) (u : α → R) (B : α → ℕ) (h : ∀ i ∈ s, db.deg (u i) ≤ B i) :
    db.deg (∏ i ∈ s, u i) ≤ ∑ i ∈ s, B i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [db.one]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact (db.mul_le _ _).trans (Nat.add_le_add (h a (mem_insert_self a s))
      (ih fun i hi => h i (mem_insert_of_mem hi)))

private theorem DegBound.natCast_eq_zero {R : Type*} [CommRing R] (db : DegBound R) (n : ℕ) :
    db.deg n = 0 := by
  induction n with
  | zero => simpa using db.zero
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Nat.eq_zero_of_le_zero
      ((db.add_le n 1).trans (max_le (by rw [ih]) (by rw [db.one])))

private theorem DegBound.derivative_coeff_le {R : Type*} [CommRing R] (db : DegBound R)
    {f : R[X]} {B : ℕ} (hf : ∀ b, db.deg (f.coeff b) ≤ B) (b : ℕ) :
    db.deg (f.derivative.coeff b) ≤ B := by
  rw [coeff_derivative]
  refine (db.mul_le _ _).trans ?_
  rw [← Nat.cast_succ, db.natCast_eq_zero (b + 1), add_zero]
  exact hf (b + 1)

private theorem DegBound.resultant_le {R : Type*} [CommRing R] (db : DegBound R)
    {f g : R[X]} (m n : ℕ) {Bf Bg : ℕ}
    (hf : ∀ i, db.deg (f.coeff i) ≤ Bf) (hg : ∀ i, db.deg (g.coeff i) ≤ Bg) :
    db.deg (Polynomial.resultant f g m n) ≤ m * Bg + n * Bf := by
  rw [Polynomial.resultant, Matrix.det_apply]
  refine db.sum_le _ _ fun σ _ => ?_
  have hz : ∀ (s : ℤˣ) (x : R), db.deg (s • x) = db.deg x := fun s x => by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp [Units.smul_def, db.neg]
  rw [hz]
  let bnd : Fin (m + n) → ℕ := Fin.addCases (fun _ => Bg) (fun _ => Bf)
  refine (db.prod_le Finset.univ _ bnd fun j _ => ?_).trans_eq ?_
  · induction j using Fin.addCases with
    | left j =>
      simp only [bnd, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs <;> [exact hg _; exact db.zero ▸ Nat.zero_le _]
    | right j =>
      simp only [bnd, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs <;> [exact hf _; exact db.zero ▸ Nat.zero_le _]
  · simp [bnd, Fin.sum_univ_add]

private theorem DegBound.leadingCoeff_mul_resultant_derivative_le {R : Type*} [CommRing R]
    (db : DegBound R) {f : R[X]} (hf_deg : 1 ≤ f.natDegree) {B : ℕ}
    (hf : ∀ b, db.deg (f.coeff b) ≤ B) :
    db.deg (f.leadingCoeff *
        Polynomial.resultant f f.derivative f.natDegree f.derivative.natDegree) ≤
      2 * f.natDegree * B := by
  have hf'_deg := Polynomial.natDegree_derivative_le f
  have hres := db.resultant_le f.natDegree f.derivative.natDegree hf (db.derivative_coeff_le hf)
  refine (db.mul_le _ _).trans <| (Nat.add_le_add (hf f.natDegree) hres).trans ?_
  rw [← add_mul, show B + (f.natDegree + f.derivative.natDegree) * B =
    (1 + (f.natDegree + f.derivative.natDegree)) * B by ring]
  exact Nat.mul_le_mul_right B (by omega)

/-- Shared root-counting and resultant helpers. -/
private theorem card_filter_eval_eq_zero_le {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] {p : R[X]} (hp : p ≠ 0) (T : Finset R) :
    #(T.filter fun z => p.eval z = 0) ≤ p.natDegree := by
  have hsub : T.filter (fun z => p.eval z = 0) ⊆ p.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot]
    exact (mem_filter.1 hz).2
  exact (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))

private theorem exists_eval_ne_zero_of_natDegree_lt_card {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : p ≠ 0) {T : Finset R} (hlt : p.natDegree < #T) :
    ∃ x ∈ T, p.eval x ≠ 0 := by
  by_contra hall
  push Not at hall
  exact hp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p T hall hlt)

private theorem resultant_ne_zero_of_isCoprime_map {R K : Type*} [CommRing R]
    [Field K] (φ : R →+* K) (hφ : Function.Injective φ) {f g : R[X]}
    (hcop : IsCoprime (f.map φ) (g.map φ)) :
    Polynomial.resultant f g f.natDegree g.natDegree ≠ 0 := by
  intro h0
  have hmap : Polynomial.resultant (f.map φ) (g.map φ) = 0 := by
    change Polynomial.resultant (f.map φ) (g.map φ)
      (f.map φ).natDegree (g.map φ).natDegree = 0
    rw [Polynomial.natDegree_map_eq_of_injective hφ,
      Polynomial.natDegree_map_eq_of_injective hφ,
      Polynomial.resultant_map_map, h0, map_zero]
  exact (Polynomial.resultant_eq_zero_iff.1 hmap).2 hcop

private theorem coeff_sum_Icc_C_mul_X_pow {R : Type*} [Semiring R] (a b k : ℕ) (f : ℕ → R) :
    (∑ j ∈ Icc a b, C (f j) * X ^ j).coeff k = if a ≤ k ∧ k ≤ b then f k else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  have hsum : (∑ j ∈ Icc a b, if k = j then f j else 0) =
      ∑ j ∈ Icc a b, if j = k then f j else 0 :=
    Finset.sum_congr rfl fun j _ => if_congr eq_comm rfl rfl
  rw [hsum, Finset.sum_ite_eq']
  simp only [mem_Icc]

end SwapAndDegZ

section Step1Siegel

variable {F : Type*} [Field F]

/-- Curve polynomial `w_i(Z) = ∑_j u_j(i) Z^j ∈ F[Z]`, built via `Polynomial.ofFn`. -/
private noncomputable abbrev curveWord [DecidableEq F] {ι : Type*} {r : ℕ}
    (u : Fin (r + 1) → (ι → F)) (i : ι) : F[X] :=
  Polynomial.ofFn (r + 1) (fun j => u j i)

private theorem eval_curveWord [DecidableEq F] {ι : Type*} {r : ℕ}
    (u : Fin (r + 1) → (ι → F)) (i : ι) (z : F) :
    (curveWord u i).eval z = ∑ j : Fin (r + 1), z ^ (j : ℕ) * u j i := by
  rw [curveWord, Polynomial.ofFn_eq_sum_monomial, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_monomial, mul_comm]

/-- Polynomial `Q_c ∈ F[Z][X][Y]` constructed from coefficient table `c : (M × Fin (B + 1)) → F`. -/
private noncomputable def polyOfTable (M : Finset (ℕ × ℕ)) (B : ℕ)
    (c : (M × Fin (B + 1)) → F) : F[X][X][X] :=
  ∑ p ∈ M.attach,
    C (C (∑ t : Fin (B + 1), C (c (p, t)) * X ^ (t : ℕ)) * X ^ p.1.1) * X ^ p.1.2

private theorem coeff_coeff_coeff_polyOfTable (M : Finset (ℕ × ℕ)) (B : ℕ)
    (c : (M × Fin (B + 1)) → F) (a b t : ℕ) :
    (((polyOfTable M B c).coeff b).coeff a).coeff t =
      if h : (a, b) ∈ M then
        if ht : t < B + 1 then c (⟨(a, b), h⟩, ⟨t, ht⟩) else 0
      else 0 := by
  rw [polyOfTable, finsetSum_coeff, finsetSum_coeff, finsetSum_coeff]
  have hterm (p : M) :
      (((C (C (∑ u : Fin (B + 1), C (c (p, u)) * X ^ (u : ℕ)) * X ^ p.1.1) *
          X ^ p.1.2).coeff b).coeff a).coeff t =
        if p.1 = (a, b) then if ht : t < B + 1 then c (p, ⟨t, ht⟩) else 0 else 0 := by
    by_cases hpe : p.1 = (a, b)
    · have hpa : p.1.1 = a := congrArg Prod.fst hpe
      have hpb : p.1.2 = b := congrArg Prod.snd hpe
      simp only [hpe, ↓reduceIte, coeff_C_mul_X_pow, finsetSum_coeff]
      by_cases ht : t < B + 1
      · simp only [ht, ↓reduceDIte]
        rw [Finset.sum_eq_single ⟨t, ht⟩
          (fun u _ hne => ite_eq_right fun h => hne (Fin.ext h.symm))
          (fun h => absurd (mem_univ _) h)]
        simp only [↓reduceIte]
      · simp only [ht, ↓reduceDIte]
        exact Finset.sum_eq_zero fun u _ => ite_eq_right (by omega)
    · rw [ite_eq_right hpe, coeff_C_mul_X_pow]
      split_ifs with hpb
      · rw [coeff_C_mul_X_pow, ite_eq_right fun hpa => hpe (Prod.ext hpa.symm hpb.symm),
          coeff_zero]
      · simp only [coeff_zero]
  simp_rw [hterm]
  by_cases hab : (a, b) ∈ M
  · rw [dite_eq_left hab, Finset.sum_eq_single ⟨(a, b), hab⟩
      (fun _ _ hne => ite_eq_right fun h => hne (Subtype.ext h))
      (fun h => absurd (mem_attach M _) h)]; simp
  · rw [dite_eq_right hab]
    exact Finset.sum_eq_zero fun p _ => ite_eq_right fun h : p.1 = (a, b) => hab (h ▸ p.2)

private theorem polyOfTable_eq_zero_iff (M : Finset (ℕ × ℕ)) (B : ℕ)
    (c : (M × Fin (B + 1)) → F) :
    polyOfTable M B c = 0 ↔ c = 0 := by
  constructor
  · intro h0
    funext ⟨⟨⟨a, b⟩, hab⟩, ⟨t, ht⟩⟩
    have hc := congrArg (fun Q : F[X][X][X] => ((Q.coeff b).coeff a).coeff t) h0
    rw [coeff_coeff_coeff_polyOfTable, dite_eq_left hab, dite_eq_left ht] at hc
    simpa using hc
  · rintro rfl
    ext b a t
    rw [coeff_coeff_coeff_polyOfTable]
    split_ifs <;> simp

private theorem weightedDegree_polyOfTable_le (d D B : ℕ)
    (c : (Sudan.monomials d D × Fin (B + 1)) → F) :
    weightedDegree d (polyOfTable (Sudan.monomials d D) B c) ≤ D := by
  rw [weightedDegree_le_iff]
  intro a b hab
  by_contra hlt
  apply hab
  ext t
  rw [coeff_coeff_coeff_polyOfTable, dite_eq_right, coeff_zero]
  intro hmem
  have hle := (Sudan.mem_monomials.1 hmem).2.2
  dsimp only at hle
  omega

private theorem natDegree_polyOfTable_le (d D B : ℕ)
    (c : (Sudan.monomials d D × Fin (B + 1)) → F) :
    (polyOfTable (Sudan.monomials d D) B c).natDegree ≤ maxYDeg d D := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro b hb
  ext a t
  rw [coeff_coeff_coeff_polyOfTable, coeff_zero, coeff_zero]
  by_cases hmem : (a, b) ∈ Sudan.monomials d D
  · have hle : b ≤ maxYDeg d D := Finset.le_sup (f := Prod.snd) hmem
    omega
  · simp [hmem]

private theorem degZ_polyOfTable_le (M : Finset (ℕ × ℕ)) (B : ℕ)
    (c : (M × Fin (B + 1)) → F) :
    degZ (polyOfTable M B c) ≤ B := by
  rw [degZ_le_iff]
  intro a b
  rw [natDegree_le_iff_coeff_eq_zero]
  intro t ht
  rw [coeff_coeff_coeff_polyOfTable]
  split_ifs with h1 h2
  · omega
  · rfl
  · rfl

private theorem natDegree_coeff_shift_polyOfTable_le {d D B r : ℕ}
    (c : (Sudan.monomials d D × Fin (B + 1)) → F) (x : F) (w : F[X]) (hw : w.natDegree ≤ r)
    (u v : ℕ) :
    (((shift (C x) w (polyOfTable (Sudan.monomials d D) B c)).coeff v).coeff u).natDegree ≤
      B + r * maxYDeg d D := by
  rw [polyOfTable, map_sum, finsetSum_coeff, finsetSum_coeff]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun p _ => ?_)
  set cz : F[X] := ∑ t : Fin (B + 1), C (c (p, t)) * X ^ (t : ℕ)
  have hcz_deg : cz.natDegree ≤ B := (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (by omega))
  have hmono : C (C cz * X ^ p.1.1) * X ^ p.1.2 = monomial p.1.2 (monomial p.1.1 cz) := by
    rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial]
  have hshift_c : (((shift (C x) w (C (C cz * X ^ p.1.1) * X ^ p.1.2)).coeff v).coeff u) =
      (p.1.1.choose u : F[X]) * (p.1.2.choose v : F[X]) * cz * (C x) ^ (p.1.1 - u) *
        w ^ (p.1.2 - v) := by
    rw [hmono, coeff_coeff_shift_monomial]
  change ((((shift (C x) w (C (C cz * X ^ p.1.1) * X ^ p.1.2)).coeff v).coeff u).natDegree) ≤ _
  rw [hshift_c]
  refine natDegree_mul_le.trans (Nat.add_le_add ?_ (natDegree_pow_le.trans ?_))
  · have hre : (p.1.1.choose u : F[X]) * (p.1.2.choose v : F[X]) * cz * (C x) ^ (p.1.1 - u) =
        C ((p.1.1.choose u : F) * (p.1.2.choose v : F) * x ^ (p.1.1 - u)) * cz := by
      simp only [map_mul, map_pow, map_natCast]; ring
    exact hre ▸ (natDegree_C_mul_le _ _).trans hcz_deg
  · calc (p.1.2 - v) * w.natDegree ≤ p.1.2 * r := Nat.mul_le_mul (Nat.sub_le _ _) hw
      _ ≤ r * maxYDeg d D :=
        mul_comm _ r ▸ Nat.mul_le_mul_right r (Finset.le_sup (f := Prod.snd) p.2)

/-- Step 1 (Siegel interpolation in `F[Z][X][Y]`): zero-denominator multiplicity-`m` interpolant
with explicit `Z`-degree bound `siegelZDeg n m d D r`. -/
private theorem exists_siegel_interpolant [DecidableEq F] {ι : Type*} [Fintype ι] (α : ι → F)
    {r m d D : ℕ} (u : Fin (r + 1) → (ι → F))
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials d D)) :
    ∃ Q : F[X][X][X],
      Q ≠ 0 ∧
      weightedDegree d Q ≤ D ∧
      Q.natDegree ≤ maxYDeg d D ∧
      degZ Q ≤ siegelZDeg (Fintype.card ι) m d D r ∧
      ∀ i : ι, VanishesToOrder m (C (α i)) (curveWord u i) Q := by
  classical
  set M := Sudan.monomials d D
  set B := siegelZDeg (Fintype.card ι) m d D r
  set D_Y := maxYDeg d D
  set R_eq := Fintype.card ι * (m * (m + 1) / 2)
  let entry : (M × Fin (B + 1)) → (ι × multPairs m × Fin (B + r * D_Y + 1)) → F := fun pt eq =>
    (((shift (C (α eq.1)) (curveWord u eq.1)
        (C (C (X ^ (pt.2 : ℕ)) * X ^ pt.1.1.1) * X ^ pt.1.1.2)).coeff eq.2.1.1.2).coeff
      eq.2.1.1.1).coeff (eq.2.2 : ℕ)
  let Φ : ((M × Fin (B + 1)) → F) →ₗ[F] ((ι × multPairs m × Fin (B + r * D_Y + 1)) → F) :=
    { toFun := fun c eq => ∑ pt : M × Fin (B + 1), c pt * entry pt eq
      map_add' := fun _ _ => funext fun _ => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun _ _ => funext fun _ => by simp [smul_eq_mul, mul_assoc, Finset.mul_sum] }
  have hΦ_eq : ∀ c eq, Φ c eq =
      (((shift (C (α eq.1)) (curveWord u eq.1) (polyOfTable M B c)).coeff eq.2.1.1.2).coeff
        eq.2.1.1.1).coeff (eq.2.2 : ℕ) := fun c eq => by
    change ∑ pt : M × Fin (B + 1), c pt * entry pt eq = _
    rw [polyOfTable, map_sum, finsetSum_coeff, finsetSum_coeff, finsetSum_coeff,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hsplit :
        C (C (∑ t : Fin (B + 1), C (c (p, t)) * X ^ (t : ℕ)) * X ^ p.1.1) * X ^ p.1.2 =
        ∑ t : Fin (B + 1),
          C (C (C (c (p, t)))) * (C (C (X ^ (t : ℕ)) * X ^ p.1.1) * X ^ p.1.2) := by
      simp only [map_sum, Finset.sum_mul, map_mul, mul_assoc]
    rw [hsplit, map_sum, finsetSum_coeff, finsetSum_coeff, finsetSum_coeff]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hshiftC : shift (C (α eq.1)) (curveWord u eq.1) (C (C (C (c (p, t))))) =
        C (C (C (c (p, t)))) := by
      rw [shift_apply, map_C, taylor_C]; change C (taylor (C (α eq.1)) (C (C _))) = _; rw [taylor_C]
    rw [map_mul, hshiftC, coeff_C_mul, coeff_C_mul, coeff_C_mul]
  have hsiegel : R_eq * r * D_Y < (#M - R_eq) * (B + 1) := by
    simpa [B, siegelZDeg, R_eq, D_Y] using
      Nat.lt_mul_div_succ (R_eq * r * D_Y) (Nat.sub_pos_of_lt hinterp)
  have hcard_lt : Fintype.card (ι × multPairs m × Fin (B + r * D_Y + 1)) <
      Fintype.card (M × Fin (B + 1)) := by
    simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, card_multPairs]
    have h1 : Fintype.card ι * (m * (m + 1) / 2 * (B + r * D_Y + 1)) =
        R_eq * (B + 1) + R_eq * r * D_Y := by dsimp only [R_eq]; ring
    have h2 : #M * (B + 1) = R_eq * (B + 1) + (#M - R_eq) * (B + 1) := by
      rw [← add_mul, Nat.add_sub_of_le hinterp.le]
    omega
  obtain ⟨c, hc_mem, hc_ne⟩ := (Submodule.ne_bot_iff _).1 <|
    LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) (by
      simpa only [Module.finrank_fintype_fun_eq_card] using hcard_lt)
  refine ⟨polyOfTable M B c, (not_iff_not.2 (polyOfTable_eq_zero_iff M B c)).2 hc_ne,
    weightedDegree_polyOfTable_le d D B c, natDegree_polyOfTable_le d D B c,
    degZ_polyOfTable_le M B c, fun i u₀ v₀ huv => ?_⟩
  ext t; rw [coeff_zero]
  by_cases ht : t < B + r * D_Y + 1
  · have hz := congrFun (LinearMap.mem_ker.1 hc_mem)
      (i, (⟨(u₀, v₀), mem_multPairs.2 huv⟩ : multPairs m), (⟨t, ht⟩ : Fin (B + r * D_Y + 1)))
    have hΦ := hΦ_eq c (i, (⟨(u₀, v₀), mem_multPairs.2 huv⟩ : multPairs m),
      (⟨t, ht⟩ : Fin (B + r * D_Y + 1)))
    exact hΦ.symm.trans hz
  · have hdeg := natDegree_coeff_shift_polyOfTable_le c (α i) (curveWord u i)
      (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos r) _)) u₀ v₀
    exact coeff_eq_zero_of_natDegree_lt (by dsimp only [M, B, D_Y] at *; omega)

end Step1Siegel

section Step2FactorPigeonhole

variable {F : Type*} [Field F]

/-- Specialization `Z ↦ z` on `F[Z]`. -/
private noncomputable def evZ (z : F) : F[X] →+* F := Polynomial.evalRingHom z

/-- Specialization `Z ↦ z` on `F[Z][X]`. -/
private noncomputable def evZ₁ (z : F) : F[X][X] →+* F[X] := Polynomial.mapRingHom (evZ z)

/-- Specialization `Z ↦ z` on `F[Z][X][Y]`. -/
private noncomputable def evZ₂ (z : F) : F[X][X][X] →+* F[X][X] := Polynomial.mapRingHom (evZ₁ z)

private theorem eval_resultant_eq_zero_of_common_root
    {f g : F[X][X]} (hf : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) {z y : F}
    (hf0 : (f.map (evZ z)).eval y = 0) (hg0 : (g.map (evZ z)).eval y = 0) :
    (Polynomial.resultant f g f.natDegree g.natDegree).eval z = 0 := by
  obtain ⟨U, V, _, _, hbez⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl hf
  have hmap := congrArg (fun p : F[X][X] => (p.map (evZ z)).eval y) hbez
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
    eval_add, eval_mul, eval_mul, eval_C, hf0, hg0, zero_mul, zero_mul, add_zero] at hmap
  exact hmap.symm

private theorem exists_eq_C_mul_prod_irreducible_of_ufd {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {Q : R[X]} (hQ : Q ≠ 0) :
    ∃ (c : R) (fs : Multiset R[X]),
      c ≠ 0 ∧
      (∀ f ∈ fs, Irreducible f ∧ 1 ≤ f.natDegree) ∧
      Q = C c * fs.prod := by
  classical
  let all := UniqueFactorizationMonoid.factors Q
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hQ
  let fs₀ := all.filter (fun f => f.natDegree = 0)
  let fs := all.filter (fun f => 1 ≤ f.natDegree)
  have hsplit : all = fs₀ + fs := by
    have h1 : fs = all.filter (fun f => ¬ f.natDegree = 0) :=
      Multiset.filter_congr (fun _ _ => by omega)
    rw [h1]
    exact (Multiset.filter_add_not (fun f : R[X] => f.natDegree = 0) all).symm
  have hirred : ∀ f ∈ all, Irreducible f := UniqueFactorizationMonoid.irreducible_of_factor
  have hfs₀_deg : fs₀.prod.natDegree = 0 := by
    have hne : ∀ f ∈ fs₀, f ≠ 0 := fun f hf =>
      (hirred f (Multiset.mem_of_mem_filter hf)).ne_zero
    rw [Polynomial.natDegree_multiset_prod fs₀ (fun h0 => hne 0 h0 rfl)]
    exact Multiset.sum_eq_zero fun n hn => by
      obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.1 hn
      exact (Multiset.mem_filter.1 hf).2
  have hu_deg : (u : R[X]).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit u.isUnit
  have hQ_eq : Q = C (fs₀.prod.coeff 0 * (u : R[X]).coeff 0) * fs.prod := by
    rw [C_mul, ← Polynomial.eq_C_of_natDegree_eq_zero hfs₀_deg,
      ← Polynomial.eq_C_of_natDegree_eq_zero hu_deg, ← hu]
    change (all.prod * (u : R[X])) = _
    rw [hsplit, Multiset.prod_add]
    ring
  have hc0 : fs₀.prod.coeff 0 * (u : R[X]).coeff 0 ≠ 0 := by
    intro h0
    apply hQ
    rw [hQ_eq, h0, map_zero, zero_mul]
  exact ⟨_, fs, hc0, fun f hf => ⟨hirred f (Multiset.mem_of_mem_filter hf),
    (Multiset.mem_filter.1 hf).2⟩, hQ_eq⟩

private theorem exists_mem_eval_map_eq_zero {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (ms : Multiset R[X]) (y : S) (h : (ms.prod.map φ).eval y = 0) :
    ∃ f ∈ ms, (f.map φ).eval y = 0 := by
  have hprod : (ms.map fun f => (f.map φ).eval y).prod = 0 := by
    rw [← h, Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod, Multiset.map_map]
    rfl
  exact Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 hprod)

private theorem weightedDegree_evZ₂_le {d : ℕ} (z : F) (Q : F[X][X][X]) :
    weightedDegree d (evZ₂ z Q) ≤ weightedDegree d Q := by
  exact weightedDegree_map_le (evZ z) d Q

private theorem card_filter_evZ₂_eq_zero_le [DecidableEq F] {Q : F[X][X][X]} (hQ : Q ≠ 0)
    (T : Finset F) :
    #(T.filter fun z => evZ₂ z Q = 0) ≤ degZ Q := by
  classical
  have hex : ∃ b a, (Q.coeff b).coeff a ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hQ
    ext b a : 4
    simpa using hall b a
  rcases hex with ⟨b, a, hab⟩
  set c₀ : F[X] := (Q.coeff b).coeff a
  have hsub : T.filter (fun z => evZ₂ z Q = 0) ⊆ T.filter (fun z => c₀.eval z = 0) := by
    intro z hz
    rw [mem_filter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    have hcoeff := congrArg (fun R : F[X][X] => (R.coeff b).coeff a) hz.2
    simpa [evZ₂, evZ₁, evZ, c₀] using hcoeff
  exact (card_le_card hsub).trans
    ((card_filter_eval_eq_zero_le hab T).trans (degZ_le_iff.1 le_rfl a b))

private theorem ceil_div_le_card_of_sum_le {ι : Type*} {W : ι → ℕ} {M B_W : ℕ} (hM : 0 < M)
    (hW_le : ∀ i, W i ≤ M) {A : Finset ι} (hsum : B_W ≤ ∑ i ∈ A, W i) :
    (B_W + M - 1) / M ≤ #A := by
  have h1 : B_W ≤ #A * M :=
    hsum.trans ((Finset.sum_le_sum fun i _ => hW_le i).trans (by simp))
  have h2 : B_W + M - 1 < (#A + 1) * M := by
    rw [add_mul, one_mul]
    omega
  have h3 : (B_W + M - 1) / M < #A + 1 := (Nat.div_lt_iff_lt_mul hM).2 h2
  omega

/-- Helper: a single weighted close point forces `1 ≤ W_tot` and `1 ≤ D` under the interpolation
condition `|ι| * (m * (m + 1) / 2) < #(Sudan.monomials d D)`. -/
private theorem pos_params_of_interpolation {ι : Type*} [Fintype ι] {W : ι → ℕ}
    {k m d D M W_tot B_W : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials d D))
    {A : Finset ι} (hA : B_W ≤ ∑ i ∈ A, W i) :
    1 ≤ W_tot ∧ 1 ≤ D := by
  have hB_pos : 1 ≤ B_W := by
    by_contra h0
    have hdiv : (B_W + M - 1) / M = 0 := by
      rw [show B_W = 0 by omega, zero_add]; exact Nat.div_eq_of_lt (by omega)
    omega
  have hW_tot_pos : 1 ≤ W_tot :=
    hB_pos.trans (hA.trans ((Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans hW_sum))
  have hcard_pos : 1 ≤ Fintype.card ι :=
    (hk.trans hk_le_t).trans ((ceil_div_le_card_of_sum_le hM hW_le hA).trans (card_le_univ _))
  have hD_pos : 1 ≤ D := by
    by_contra h0
    have htri : 1 ≤ m * (m + 1) / 2 := by
      have : 2 ≤ m * (m + 1) := Nat.mul_le_mul hm (by omega : 2 ≤ m + 1)
      omega
    have hmon0 : #(Sudan.monomials d 0) ≤ 1 := by
      refine (card_le_card (t := {(0, 0)}) fun p hp => mem_singleton.2 ?_).trans (by simp)
      obtain ⟨h1, h2, _⟩ := Sudan.mem_monomials.1 hp
      exact Prod.ext (by omega) (by omega)
    rw [show D = 0 by omega] at hinterp
    have := Nat.mul_pos hcard_pos htri
    omega
  exact ⟨hW_tot_pos, hD_pos⟩

/-- Step 2 (UFD factorization in `F[Z][X][Y]` and pigeonhole onto a single irreducible factor `R`).
-/
private theorem exists_irreducible_factor_pigeonhole {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k r m D M W_tot B_W : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * ((B_W + M - 1) / M))
    (u : Fin (r + 1) → (ι → F))
    {T : Finset F}
    (hT : johnsonCurveBound (Fintype.card ι) m (k - 1) D r W_tot < #T)
    (hclose : ∀ z ∈ T, ∃ v ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) * u j i) = v i),
        W i) :
    ∃ (R : F[X][X][X]) (T_R : Finset F),
      Irreducible R ∧ 1 ≤ R.natDegree ∧
      R.natDegree ≤ maxYDeg (k - 1) D ∧
      weightedDegree (k - 1) R ≤ D ∧
      degZ R ≤ siegelZDeg (Fintype.card ι) m (k - 1) D r ∧
      1 ≤ maxYDeg (k - 1) D ∧ 1 ≤ D ∧ 1 ≤ W_tot ∧
      T_R ⊆ T ∧
      2 * R.natDegree * (D + siegelZDeg (Fintype.card ι) m (k - 1) D r) +
        W_tot * R.natDegree * maxYDeg (k - 1) D *
          (4 * D * siegelZDeg (Fintype.card ι) m (k - 1) D r + r * maxYDeg (k - 1) D) < #T_R ∧
      (∀ z ∈ T_R, ∃ P : F[X], P.natDegree ≤ k - 1 ∧ (evZ₂ z R).eval P = 0 ∧
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z),
          W i) := by
  classical
  set d := k - 1; set D_Y := maxYDeg d D; set B_Z := siegelZDeg (Fintype.card ι) m d D r
  obtain ⟨z₀, hz₀⟩ := Finset.card_pos.1 (Nat.zero_lt_of_lt hT)
  obtain ⟨v₀, _, hv₀⟩ := hclose z₀ hz₀
  obtain ⟨hW_tot_pos, hD_pos⟩ :=
    pos_params_of_interpolation hk hm hM hW_le hW_sum hk_le_t hinterp hv₀
  obtain ⟨Q, hQ0, hQwd, hQdeg, hQdegZ, hQvan⟩ := exists_siegel_interpolant α u hinterp
  obtain ⟨c, fs, _, hfs_prop, hQ_eq⟩ := exists_eq_C_mul_prod_irreducible_of_ufd hQ0
  have hsum_deg : ∑ R ∈ fs.toFinset, R.natDegree ≤ D_Y := by
    rw [← Polynomial.natDegree_prod _ _ fun R hR =>
      (hfs_prop R (Multiset.mem_toFinset.1 hR)).1.ne_zero]
    exact (Polynomial.natDegree_le_of_dvd
      ((Multiset.toFinset_prod_dvd_prod fs).trans ⟨C c, by rw [hQ_eq, mul_comm]⟩) hQ0).trans hQdeg
  let T_nz := T.filter fun z => evZ₂ z Q ≠ 0
  have hT_nz_card : #T - B_Z ≤ #T_nz := by
    have h := Finset.card_filter_add_card_filter_not (s := T) (p := fun z => evZ₂ z Q = 0)
    have hbad := (card_filter_evZ₂_eq_zero_le hQ0 T).trans hQdegZ
    change #(T.filter fun z => evZ₂ z Q = 0) + #T_nz = #T at h
    omega
  let T_of : F[X][X][X] → Finset F := fun R =>
    T.filter fun z => ∃ P : F[X], P.natDegree ≤ d ∧ (evZ₂ z R).eval P = 0 ∧
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i
  have hcover : T_nz ⊆ fs.toFinset.biUnion T_of := fun z hz => by
    obtain ⟨hzT, hQz_ne⟩ := mem_filter.1 hz
    obtain ⟨v, hv_rs, hv_agree⟩ := hclose z hzT
    obtain ⟨P, hP_deg, rfl⟩ := mem_reedSolomon.1 hv_rs
    have hP_natDeg : P.natDegree ≤ d := by
      by_cases hP0 : P = 0
      · simp [hP0]
      · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).2 hP_deg; omega
    have hW_P : B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z),
        W i := by
      simpa only [eval_curveWord, eq_comm] using hv_agree
    have hQz_interp : IsInterpolant α (fun i => (curveWord u i).eval z) m d D (evZ₂ z Q) :=
      ⟨hQz_ne,
        Polynomial.Bivariate.weightedDegree_le_iff.1 ((weightedDegree_evZ₂_le z Q).trans hQwd),
        fun i => by simpa [evZ₂, evZ₁, evZ] using (hQvan i).map (evZ z)⟩
    have heval0 : (evZ₂ z Q).eval P = 0 := hQz_interp.eval_eq_zero hα hP_natDeg
      (hroot.trans_le (Nat.mul_le_mul_left m (ceil_div_le_card_of_sum_le hM hW_le hW_P)))
    have hc_ev_ne : evZ₁ z c ≠ 0 := fun h0 => hQz_ne <| by
      rw [hQ_eq, map_mul, evZ₂, Polynomial.coe_mapRingHom, Polynomial.map_C, h0, map_zero, zero_mul]
    rw [hQ_eq, map_mul, eval_mul, evZ₂, Polynomial.coe_mapRingHom, Polynomial.map_C, eval_C]
      at heval0
    obtain ⟨R, hR_mem, hp0⟩ :=
      exists_mem_eval_map_eq_zero (evZ₁ z) fs P ((mul_eq_zero.1 heval0).resolve_left hc_ev_ne)
    exact mem_biUnion.2 ⟨R, Multiset.mem_toFinset.2 hR_mem,
      mem_filter.2 ⟨hzT, P, hP_natDeg, hp0, hW_P⟩⟩
  let B_of : F[X][X][X] → ℕ := fun R =>
    2 * R.natDegree * (D + B_Z) + W_tot * R.natDegree * D_Y * (4 * D * B_Z + r * D_Y)
  have hsum_B : ∑ R ∈ fs.toFinset, B_of R < #T_nz := by
    have h1 : ∑ R ∈ fs.toFinset, B_of R =
        (∑ R ∈ fs.toFinset, R.natDegree) *
          (2 * (D + B_Z) + W_tot * D_Y * (4 * D * B_Z + r * D_Y)) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun R _ => by dsimp only [B_of]; ring
    have h2 : ∑ R ∈ fs.toFinset, B_of R ≤
        2 * D_Y * (D + B_Z) + W_tot * D_Y ^ 2 * (4 * D * B_Z + r * D_Y) :=
      h1 ▸ (Nat.mul_le_mul_right _ hsum_deg).trans_eq (by ring)
    have h3 : B_Z + (2 * D_Y * (D + B_Z) + W_tot * D_Y ^ 2 * (4 * D * B_Z + r * D_Y)) < #T := by
      simpa [johnsonCurveBound, D_Y, B_Z, add_assoc] using hT
    omega
  obtain ⟨R, hR_fin, hR_card⟩ :=
    Finset.exists_lt_of_sum_lt <|
      hsum_B.trans_le ((card_le_card hcover).trans Finset.card_biUnion_le)
  have hR_mem := Multiset.mem_toFinset.1 hR_fin
  obtain ⟨hR_irred, hR_deg⟩ := hfs_prop R hR_mem
  have hR_dvd : R ∣ Q := (Multiset.dvd_prod hR_mem).trans ⟨C c, by rw [hQ_eq, mul_comm]⟩
  have hR_deg_le : R.natDegree ≤ D_Y := (Polynomial.natDegree_le_of_dvd hR_dvd hQ0).trans hQdeg
  exact ⟨R, T_of R, hR_irred, hR_deg, hR_deg_le, (weightedDegree_le_of_dvd hQ0 hR_dvd).trans hQwd,
    (degZ_le_of_dvd hQ0 hR_dvd).trans hQdegZ, hR_deg.trans hR_deg_le, hD_pos, hW_tot_pos,
    Finset.filter_subset _ _, hR_card, fun z hz => (mem_filter.1 hz).2⟩

end Step2FactorPigeonhole

section Step3SeparableContraction

variable {F : Type*} [Field F]

private theorem coeff_expand_eq_zero_of_not_dvd {R : Type*} [CommSemiring R] {μ : ℕ}
    (hμ : 0 < μ) (p : R[X]) {b : ℕ} (hb : ¬ μ ∣ b) :
    (Polynomial.expand R μ p).coeff b = 0 := by
  rw [Polynomial.coeff_expand hμ, ite_eq_right (fun h => absurd h hb)]

/-- Step 3: Positive-characteristic-safe separable contraction `R = expand (F[Z][X]) μ S` directly
in `F[Z][X][Y]`, together with the nonzero resultant `Δ = Res_Y(S, S')` and Bézout identity
`S * A_bez + S' * B_bez = C Δ`. -/
private theorem exists_separable_contraction_and_bezout {d D B_Z : ℕ}
    {R : F[X][X][X]}
    (hR_irred : Irreducible R) (hR_deg : 1 ≤ R.natDegree)
    (hR_wd : weightedDegree d R ≤ D) (hR_degZ : degZ R ≤ B_Z) :
    ∃ (μ : ℕ) (S A_bez B_bez : F[X][X][X]) (Δ : F[X][X]),
      (μ = 1 ∨ ∃ (p e : ℕ), CharP F p ∧ p.Prime ∧ μ = p ^ e) ∧
      1 ≤ μ ∧
      Polynomial.expand (F[X][X]) μ S = R ∧
      1 ≤ S.natDegree ∧
      μ * S.natDegree = R.natDegree ∧
      μ * d ≤ D ∧
      (∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + (μ * d) * b ≤ D) ∧
      degZ S ≤ B_Z ∧
      Δ ≠ 0 ∧
      S * A_bez + S.derivative * B_bez = C Δ ∧
      (S.leadingCoeff * Δ).natDegree ≤ 2 * S.natDegree * D ∧
      degZ₂ (S.leadingCoeff * Δ) ≤ 2 * S.natDegree * B_Z := by
  classical
  let E := FractionRing (F[X][X])
  let ι_E : F[X][X] →+* E := algebraMap (F[X][X]) E
  have hι_E_inj : Function.Injective ι_E := IsFractionRing.injective (F[X][X]) E
  have hR_E_irred : Irreducible (R.map ι_E) :=
    ((hR_irred.isPrimitive (by omega)).irreducible_iff_irreducible_map_fraction_map).1 hR_irred
  obtain ⟨q, hExpF⟩ := ExpChar.exists F
  have hF_to_E : Function.Injective
      (ι_E.comp (Polynomial.C.comp Polynomial.C : F →+* F[X][X])) :=
    hι_E_inj.comp (Polynomial.C_injective.comp Polynomial.C_injective)
  have hExpE : ExpChar E q := expChar_of_injective_ringHom hF_to_E q
  obtain ⟨S_E, hS_E_sep, e_sep, hS_E_exp⟩ := hR_E_irred.hasSeparableContraction q
  set μ := q ^ e_sep
  have hμ_pos : 1 ≤ μ := Nat.one_le_pow e_sep q (by
    cases hExpF with | zero => omega | prime hp => exact hp.pos)
  have hμ_ne : μ ≠ 0 := by omega
  have hμ_char : μ = 1 ∨ ∃ (p e : ℕ), CharP F p ∧ p.Prime ∧ μ = p ^ e := by
    cases hExpF with
    | zero => exact Or.inl (by simp [μ])
    | prime hp => exact Or.inr ⟨q, e_sep, inferInstance, hp, rfl⟩
  set S : F[X][X][X] := Polynomial.contract μ R
  have hexp_S : Polynomial.expand (F[X][X]) μ S = R := by
    ext b : 2
    rw [Polynomial.coeff_expand hμ_pos]
    split_ifs with hdiv
    · rw [Polynomial.coeff_contract hμ_ne, Nat.div_mul_cancel hdiv]
    · exact (hι_E_inj (by
        rw [map_zero, ← coeff_map, ← hS_E_exp, coeff_expand_eq_zero_of_not_dvd hμ_pos S_E hdiv])
        ).symm
  have hS_map : S.map ι_E = S_E := by
    ext b
    rw [coeff_map, Polynomial.coeff_contract hμ_ne, ← coeff_map, ← hS_E_exp,
      Polynomial.coeff_expand_mul hμ_pos]
  have hdeg_mul : μ * S.natDegree = R.natDegree := by
    rw [← hexp_S, Polynomial.natDegree_expand, mul_comm]
  have hS_deg : 1 ≤ S.natDegree := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hdeg_mul; omega
  have hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + (μ * d) * b ≤ D := fun a b hab => by
    rw [Polynomial.coeff_contract hμ_ne] at hab
    have hle := (le_weightedDegree (d := d) hab).trans hR_wd
    linarith [show a + d * (b * μ) = a + (μ * d) * b by ring]
  have hμd_le : μ * d ≤ D := by
    have hlc : S.coeff S.natDegree ≠ 0 := leadingCoeff_ne_zero.2 fun h => by simp [h] at hS_deg
    obtain ⟨a, ha⟩ : ∃ a, (S.coeff S.natDegree).coeff a ≠ 0 := by
      by_contra hall; push Not at hall; exact hlc (by ext a : 2; simpa using hall a)
    have h1 := hS_wd a S.natDegree ha
    have h2 : μ * d * 1 ≤ μ * d * S.natDegree := Nat.mul_le_mul_left _ hS_deg
    omega
  have hS_degZ : degZ S ≤ B_Z := degZ_le_iff.2 fun a b => by
    rw [Polynomial.coeff_contract hμ_ne]; exact degZ_le_iff.1 hR_degZ a (b * μ)
  set Δ : F[X][X] := Polynomial.resultant S S.derivative S.natDegree S.derivative.natDegree
  have hΔ_ne : Δ ≠ 0 := resultant_ne_zero_of_isCoprime_map ι_E hι_E_inj
    (by rwa [← Polynomial.derivative_map, hS_map])
  obtain ⟨A_bez, B_bez, _, _, hbez⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant S S.derivative le_rfl le_rfl (Or.inl (by omega))
  have hS_coeff_degX : ∀ b, (S.coeff b).natDegree ≤ D := fun b =>
    natDegree_le_iff_coeff_eq_zero.2 fun a ha =>
      by_contra fun hne => by have := hS_wd a b hne; omega
  exact ⟨μ, S, A_bez, B_bez, Δ, hμ_char, hμ_pos, hexp_S, hS_deg, hdeg_mul, hμd_le, hS_wd, hS_degZ,
    hΔ_ne, hbez,
    (DegBound.natDegree F[X]).leadingCoeff_mul_resultant_derivative_le hS_deg hS_coeff_degX,
    (DegBound.degZ₂ F).leadingCoeff_mul_resultant_derivative_le hS_deg
      (fun b => (degZ₂_coeff_le_degZ S b).trans hS_degZ)⟩

end Step3SeparableContraction

section Step4ShiftAndFactor

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι]

private theorem exists_eval_C_ne_zero {F : Type*} [Field F] {H : F[X][X]} (hH : H ≠ 0)
    {T : Finset F} (hT : H.natDegree < #T) :
    ∃ x₀ ∈ T, H.eval (C x₀) ≠ 0 := by
  have hex_j : ∃ j, (Bivariate.swap H).coeff j ≠ 0 := by
    by_contra hall; push Not at hall
    exact (map_ne_zero_iff _ Bivariate.swap.injective).2 hH (by ext j : 2; simpa using hall j)
  obtain ⟨j, hj_ne⟩ := hex_j
  have hdeg : ((Bivariate.swap H).coeff j).natDegree ≤ H.natDegree := by
    simpa only [Bivariate.swap_swap_apply] using
      Bivariate.natDegree_coeff_le_natDegree_swap (Bivariate.swap H) j
  obtain ⟨x₀, hx₀, hne⟩ := exists_eval_ne_zero_of_natDegree_lt_card hj_ne (hdeg.trans_lt hT)
  refine ⟨x₀, hx₀, fun hH0 => hne ?_⟩
  have hc := congrArg (fun p : F[X] => p.coeff j) hH0
  rw [eval_eq_sum_range, finsetSum_coeff, coeff_zero] at hc
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), ← hc]
  exact Finset.sum_congr rfl fun a _ => by
    rw [← C_pow, mul_comm (H.coeff a), coeff_C_mul, coeff_coeff_swap, mul_comm]

/-- Step 4: Pick a good shift point `x₀ ∈ T_R` with `(S.leadingCoeff * Δ)(Z, x₀) ≠ 0`, and
pigeonhole onto a primitive irreducible factor `F_* ∈ F[Z][Y]` of `S₀(Z, Y) = S(Z, x₀, Y)`. -/
private theorem exists_good_shift_and_factor
    {α : ι → F} {r d D B_Z D_Y W_tot B_W μ : ℕ}
    {W : ι → ℕ} {u : Fin (r + 1) → (ι → F)}
    {R S A_bez B_bez : F[X][X][X]} {Δ : F[X][X]} {T_R : Finset F}
    (hμ_pos : 1 ≤ μ)
    (hexp_S : Polynomial.expand (F[X][X]) μ S = R)
    (hS_deg : 1 ≤ S.natDegree)
    (hdeg_mul : μ * S.natDegree = R.natDegree)
    (hS_degZ : degZ S ≤ B_Z)
    (hΔ_ne : Δ ≠ 0)
    (hbez : S * A_bez + S.derivative * B_bez = C Δ)
    (hH_degX : (S.leadingCoeff * Δ).natDegree ≤ 2 * S.natDegree * D)
    (hH_degZ : degZ₂ (S.leadingCoeff * Δ) ≤ 2 * S.natDegree * B_Z)
    (hTR_card : 2 * R.natDegree * (D + B_Z) +
        W_tot * R.natDegree * D_Y * (4 * D * B_Z + r * D_Y) < #T_R)
    (hTR_mem : ∀ z ∈ T_R, ∃ P : F[X], P.natDegree ≤ d ∧ (evZ₂ z R).eval P = 0 ∧
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i) :
    ∃ (x₀ : F) (Fstar : F[X][X]) (T'' : Finset F),
      (S.map (Polynomial.evalRingHom (C x₀))).natDegree = S.natDegree ∧
      degZ₂ (S.map (Polynomial.evalRingHom (C x₀))) ≤ B_Z ∧
      Δ.eval (C x₀) ≠ 0 ∧
      (∃ A₀ B₀ : F[X][X],
        (S.map (Polynomial.evalRingHom (C x₀))) * A₀ +
          (S.map (Polynomial.evalRingHom (C x₀))).derivative * B₀ = C (Δ.eval (C x₀))) ∧
      Irreducible Fstar ∧
      Fstar.IsPrimitive ∧
      1 ≤ Fstar.natDegree ∧
      Fstar.natDegree ≤ S.natDegree ∧
      degZ₂ Fstar ≤ B_Z ∧
      Fstar ∣ S.map (Polynomial.evalRingHom (C x₀)) ∧
      T'' ⊆ T_R ∧
      W_tot * D_Y * (4 * D * B_Z + r * D_Y) < #T'' ∧
      (∀ z ∈ T'',
        (S.leadingCoeff.eval (C x₀)).eval z ≠ 0 ∧
        (Δ.eval (C x₀)).eval z ≠ 0 ∧
        ∃ P : F[X], P.natDegree ≤ d ∧
          (evZ₂ z S).eval (P ^ μ) = 0 ∧
          (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 ∧
          ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
            ((P ^ μ).eval x₀) ≠ 0 ∧
          B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z),
            W i) := by
  classical
  set s := S.natDegree
  have hs_le_dR : s ≤ R.natDegree := by
    have := Nat.mul_le_mul_right s hμ_pos; omega
  set H : F[X][X] := S.leadingCoeff * Δ
  have hH_ne : H ≠ 0 := mul_ne_zero (leadingCoeff_ne_zero.2 fun h => by simp [s, h] at hS_deg) hΔ_ne
  obtain ⟨x₀, _, hHx₀_ne⟩ := exists_eval_C_ne_zero hH_ne (hH_degX.trans_lt (by
    have h1 : 2 * s * D ≤ 2 * R.natDegree * (D + B_Z) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hs_le_dR) (Nat.le_add_right D B_Z)
    exact lt_of_le_of_lt (h1.trans (Nat.le_add_right _ _)) hTR_card))
  have hlc_x₀_ne : S.leadingCoeff.eval (C x₀) ≠ 0 := fun h0 => hHx₀_ne (by simp [H, h0])
  have hΔ_x₀_ne : Δ.eval (C x₀) ≠ 0 := fun h0 => hHx₀_ne (by simp [H, h0])
  let φx₀ : F[X][X] →+* F[X] := Polynomial.evalRingHom (C x₀)
  set S₀ : F[X][X] := S.map φx₀
  have hS₀_deg : S₀.natDegree = s := le_antisymm Polynomial.natDegree_map_le
    (le_natDegree_of_ne_zero (by rw [coeff_map]; exact hlc_x₀_ne))
  have hS₀_ne : S₀ ≠ 0 := fun h => by simp [h] at hS₀_deg; omega
  have hS₀_degZ : degZ₂ S₀ ≤ B_Z := degZ₂_le_iff.2 fun b => by
    rw [coeff_map]
    exact (natDegree_eval_C_le_degZ₂ (S.coeff b) x₀).trans ((degZ₂_coeff_le_degZ S b).trans hS_degZ)
  have hbez₀ : ∃ A₀ B₀ : F[X][X], S₀ * A₀ + S₀.derivative * B₀ = C (Δ.eval (C x₀)) :=
    ⟨A_bez.map φx₀, B_bez.map φx₀, by
      simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        ← Polynomial.derivative_map, φx₀, coe_evalRingHom] using congrArg (Polynomial.map φx₀) hbez⟩
  let T'_R := T_R.filter fun z => (H.eval (C x₀)).eval z ≠ 0
  have hT'_card : #T_R - 2 * s * B_Z ≤ #T'_R := by
    have h := Finset.card_filter_add_card_filter_not (s := T_R)
      (p := fun z => (H.eval (C x₀)).eval z = 0)
    have hbad := (card_filter_eval_eq_zero_le hHx₀_ne T_R).trans
      ((natDegree_eval_C_le_degZ₂ H x₀).trans hH_degZ)
    change #(T_R.filter fun z => (H.eval (C x₀)).eval z = 0) + #T'_R = #T_R at h
    omega
  obtain ⟨c₀, gs, _, hgs_prop, hS₀_eq, _⟩ :=
    Polynomial.Bivariate.exists_eq_C_mul_prod_irreducible hS₀_ne
  have hgs_card : #gs.toFinset ≤ s := by
    have hdvd : ∏ G ∈ gs.toFinset, G ∣ S₀ :=
      (Multiset.toFinset_prod_dvd_prod gs).trans ⟨C c₀, by rw [hS₀_eq, mul_comm]⟩
    calc #gs.toFinset = ∑ _G ∈ gs.toFinset, 1 := by simp
      _ ≤ ∑ G ∈ gs.toFinset, G.natDegree :=
          Finset.sum_le_sum fun G hG => (hgs_prop G (Multiset.mem_toFinset.1 hG)).2.2
      _ = (∏ G ∈ gs.toFinset, G).natDegree := (Polynomial.natDegree_prod _ _ fun G hG =>
          (hgs_prop G (Multiset.mem_toFinset.1 hG)).1.ne_zero).symm
      _ ≤ s := hS₀_deg ▸ Polynomial.natDegree_le_of_dvd hdvd hS₀_ne
  have hS₀_map_evZ (z : F) : S₀.map (evZ z) = (evZ₂ z S).map (Polynomial.evalRingHom x₀) := by
    rw [Polynomial.map_map, evZ₂, Polynomial.coe_mapRingHom, Polynomial.map_map]
    congr 1; apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext' <;> [ext c; skip] <;> simp [evZ, evZ₁, φx₀]
    · simp [evZ, evZ₁, φx₀]
  let T_ofG : F[X][X] → Finset F := fun G => T'_R.filter fun z =>
    ∃ P : F[X], P.natDegree ≤ d ∧ (evZ₂ z S).eval (P ^ μ) = 0 ∧
      (G.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 ∧
      (S₀.derivative.map (evZ z)).eval ((P ^ μ).eval x₀) ≠ 0 ∧
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i
  have hcover' : T'_R ⊆ gs.toFinset.biUnion T_ofG := fun z hz => by
    obtain ⟨hz_TR, hHz_ne⟩ := mem_filter.1 hz
    obtain ⟨P, hP_deg, hR_eval0, hW_P⟩ := hTR_mem z hz_TR
    have hS_eval0 : (evZ₂ z S).eval (P ^ μ) = 0 := by
      have hmap : evZ₂ z R = Polynomial.expand F[X] μ (evZ₂ z S) := by
        rw [← hexp_S, evZ₂, Polynomial.coe_mapRingHom, Polynomial.map_expand]
      rwa [hmap, Polynomial.expand_eval] at hR_eval0
    set yz : F := (P ^ μ).eval x₀
    have hS₀_eval0 : (S₀.map (evZ z)).eval yz = 0 := by
      rw [hS₀_map_evZ z, Polynomial.eval_map]
      have hhom := Polynomial.hom_eval₂ (evZ₂ z S) (RingHom.id F[X])
        (Polynomial.evalRingHom x₀) (P ^ μ)
      rw [RingHom.comp_id, Polynomial.eval₂_id] at hhom
      change (evZ₂ z S).eval₂ (Polynomial.evalRingHom x₀) (Polynomial.evalRingHom x₀ (P ^ μ)) = 0
      rw [← hhom, hS_eval0, map_zero]
    have hγ_eval_ne : (S₀.derivative.map (evZ z)).eval yz ≠ 0 := fun hγ0 => by
      obtain ⟨A₀, B₀, hAB⟩ := hbez₀
      have hm := congrArg (fun p : F[X][X] => (p.map (evZ z)).eval yz) hAB
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, eval_add, eval_mul,
        eval_C, hS₀_eval0, zero_mul, zero_add, hγ0] at hm
      exact hHz_ne (by
        have hΔ0 : (Δ.eval (C x₀)).eval z = 0 := by simpa only [evZ, coe_evalRingHom] using hm.symm
        simp only [H, eval_mul, hΔ0, mul_zero])
    have hc₀_z_ne : c₀.eval z ≠ 0 := fun h0 => hHz_ne <| by
      have hlc : S.leadingCoeff.eval (C x₀) = c₀ * gs.prod.leadingCoeff := by
        calc S.leadingCoeff.eval (C x₀) = S₀.coeff S₀.natDegree := by
              rw [hS₀_deg, coeff_map]; rfl
          _ = c₀ * gs.prod.leadingCoeff := by
              change S₀.leadingCoeff = _
              rw [hS₀_eq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      simp only [H, eval_mul, hlc, eval_mul, h0, zero_mul]
    rw [hS₀_eq, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C] at hS₀_eval0
    obtain ⟨G, hG_mem, hv0⟩ :=
      exists_mem_eval_map_eq_zero (evZ z) gs yz ((mul_eq_zero.1 hS₀_eval0).resolve_left hc₀_z_ne)
    exact mem_biUnion.2 ⟨G, Multiset.mem_toFinset.2 hG_mem,
      mem_filter.2 ⟨hz, P, hP_deg, hS_eval0, hv0, hγ_eval_ne, hW_P⟩⟩
  set B_step := W_tot * D_Y * (4 * D * B_Z + r * D_Y)
  have hsum_G : ∑ _G ∈ gs.toFinset, B_step < ∑ G ∈ gs.toFinset, #(T_ofG G) := by
    have h1 : 2 * s * B_Z ≤ 2 * R.natDegree * (D + B_Z) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hs_le_dR) (Nat.le_add_left B_Z D)
    have h2 : s * B_step ≤ W_tot * R.natDegree * D_Y * (4 * D * B_Z + r * D_Y) := by
      rw [show s * B_step = W_tot * s * D_Y * (4 * D * B_Z + r * D_Y) by dsimp [B_step]; ring]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hs_le_dR))
    have h3 : ∑ _G ∈ gs.toFinset, B_step ≤ s * B_step := by
      rw [Finset.sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right B_step hgs_card
    have h4 : #T'_R ≤ ∑ G ∈ gs.toFinset, #(T_ofG G) :=
      (card_le_card hcover').trans Finset.card_biUnion_le
    omega
  obtain ⟨Fstar, hF_fin, hF_card⟩ := Finset.exists_lt_of_sum_lt hsum_G
  have hF_mem := Multiset.mem_toFinset.1 hF_fin
  obtain ⟨hF_irred, hF_prim, hF_deg1⟩ := hgs_prop Fstar hF_mem
  have hF_dvd : Fstar ∣ S₀ := (Multiset.dvd_prod hF_mem).trans ⟨C c₀, by rw [hS₀_eq, mul_comm]⟩
  have hF_degZ : degZ₂ Fstar ≤ B_Z := by
    obtain ⟨Q', hQ'⟩ := hF_dvd
    have hQ'0 : Q' ≠ 0 := fun h => hS₀_ne (by rw [hQ', h, mul_zero])
    have hmul := degZ₂_mul hF_irred.ne_zero hQ'0
    rw [← hQ'] at hmul; omega
  exact ⟨x₀, Fstar, T_ofG Fstar, hS₀_deg, hS₀_degZ, hΔ_x₀_ne, hbez₀, hF_irred, hF_prim, hF_deg1,
    (Polynomial.natDegree_le_of_dvd hF_dvd hS₀_ne).trans hS₀_deg.le, hF_degZ, hF_dvd,
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _), hF_card, fun z hz =>
    let hz1 := mem_filter.1 hz; let hz2 := mem_filter.1 hz1.1
    ⟨fun h0 => hz2.2 (by simp [H, h0]), fun h0 => hz2.2 (by simp [H, h0]), hz1.2⟩⟩

end Step4ShiftAndFactor

section Step5Recurrence

variable {F : Type*} [Field F]

/-- Finite Taylor expansion in arbitrary characteristic via Hasse derivatives. -/
private theorem eval₂_add_eq_sum_hasseDeriv {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (p : R[X]) {s : ℕ} (hs : p.natDegree ≤ s) (y u : A) :
    p.eval₂ f (y + u) = ∑ j ∈ range (s + 1), (hasseDeriv j p).eval₂ f y * u ^ j := by
  rw [← Polynomial.eval_map, add_comm y u, ← Polynomial.taylor_eval y (p.map f) u]
  have hdeg : (taylor y (p.map f)).natDegree < s + 1 :=
    Nat.lt_succ_of_le (by rw [natDegree_taylor]; exact Polynomial.natDegree_map_le.trans hs)
  rw [eval_eq_sum_range' hdeg]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [taylor_coeff, hasseDeriv_map, Polynomial.eval_map]

private theorem coeff_pow_eq_zero_of_lt_of_coeff_zero {R : Type*} [CommSemiring R] {p : R[X]}
    (hp0 : p.coeff 0 = 0) : ∀ j k, k < j → (p ^ j).coeff k = 0 :=
  fun j k hk => X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hp0) j) k hk

private theorem coeff_pow_eq_of_coeff_eq_of_coeff_zero {R : Type*} [CommSemiring R] {p q : R[X]}
    (hp0 : p.coeff 0 = 0) (hq0 : q.coeff 0 = 0) {m : ℕ}
    (heq : ∀ k ≤ m, p.coeff k = q.coeff k) :
    ∀ j, 1 ≤ j → ∀ k ≤ m + j - 1, (p ^ j).coeff k = (q ^ j).coeff k := by
  intro j
  induction j with
  | zero =>
    intro hj
    omega
  | succ j ih =>
    intro _ k hk
    cases j with
    | zero =>
      rw [pow_one, pow_one]
      exact heq k (by omega)
    | succ j =>
      rw [pow_succ p (j + 1), pow_succ q (j + 1), coeff_mul, coeff_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hsum : x.1 + x.2 = k := Finset.mem_antidiagonal.1 hx
      by_cases hx2 : x.2 = 0
      · rw [hx2, hp0, hq0, mul_zero, mul_zero]
      · by_cases hx1 : x.1 < j + 1
        · rw [coeff_pow_eq_zero_of_lt_of_coeff_zero hp0 (j + 1) x.1 hx1,
            coeff_pow_eq_zero_of_lt_of_coeff_zero hq0 (j + 1) x.1 hx1, zero_mul, zero_mul]
        · rw [ih (by omega) x.1 (by omega), heq x.2 (by omega)]

/-- Coefficient `S̃_a(Z, Y) ∈ F[Z][Y]` of `(X - x₀)^a` in `S(Z, X + x₀, Y)`. -/
private noncomputable def shiftedCoeff (S : F[X][X][X]) (x₀ : F) (a : ℕ) : F[X][X] :=
  (Bivariate.swap (S.map (Polynomial.taylorAlgHom (C x₀)).toRingHom)).coeff a

private theorem coeff_shiftedCoeff (S : F[X][X][X]) (x₀ : F) (a b : ℕ) :
    (shiftedCoeff S x₀ a).coeff b = (taylor (C x₀) (S.coeff b)).coeff a := by
  rw [shiftedCoeff, coeff_coeff_swap, coeff_map]
  rfl

private theorem shiftedCoeff_zero (S : F[X][X][X]) (x₀ : F) :
    shiftedCoeff S x₀ 0 = S.map (Polynomial.evalRingHom (C x₀)) := by
  ext b : 2
  rw [coeff_shiftedCoeff, taylor_coeff_zero, coeff_map]
  rfl

private theorem degZ₂_shiftedCoeff_le (S : F[X][X][X]) (x₀ : F) (a : ℕ) :
    degZ₂ (shiftedCoeff S x₀ a) ≤ degZ S := by
  rw [degZ₂_le_iff]
  intro b
  rw [coeff_shiftedCoeff]
  exact (degZ₂_le_iff.1 (degZ₂_taylor_C_le (S.coeff b) x₀) a).trans (degZ₂_coeff_le_degZ S b)

private theorem natDegree_shiftedCoeff_le (S : F[X][X][X]) (x₀ : F) (a : ℕ) :
    (shiftedCoeff S x₀ a).natDegree ≤ S.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro b hb
  rw [coeff_shiftedCoeff, coeff_eq_zero_of_natDegree_lt hb, map_zero, coeff_zero]

private theorem shiftedCoeff_weighted_le {S : F[X][X][X]} {x₀ : F} {w D : ℕ}
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D)
    {a b : ℕ} (hab : (shiftedCoeff S x₀ a).coeff b ≠ 0) :
    a + w * b ≤ D := by
  rw [coeff_shiftedCoeff] at hab
  have ha_le : a ≤ (S.coeff b).natDegree := by
    have h1 := le_natDegree_of_ne_zero hab
    rwa [natDegree_taylor] at h1
  have hSb_ne : S.coeff b ≠ 0 := by
    intro h0
    rw [h0, map_zero, coeff_zero] at hab
    exact hab rfl
  have hlc : (S.coeff b).coeff (S.coeff b).natDegree ≠ 0 := leadingCoeff_ne_zero.2 hSb_ne
  have hle := hS_wd (S.coeff b).natDegree b hlc
  omega

private theorem shiftedCoeff_eq_zero_of_gt {S : F[X][X][X]} {x₀ : F} {w D : ℕ}
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D)
    {a : ℕ} (ha : D < a) :
    shiftedCoeff S x₀ a = 0 := by
  ext b : 2
  rw [coeff_zero]
  by_contra hne
  have hle := shiftedCoeff_weighted_le hS_wd hne
  omega

/-- Expanding `S(Z, X + x₀, Y)` mapped under `ψ : F[Z] →+* A` and evaluated at `W ∈ A[X]`. -/
private theorem eval_map_shifted_eq_sum {A : Type*} [CommRing A]
    (ψ : F[X] →+* A) (S : F[X][X][X]) (x₀ : F) {w D : ℕ}
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D) (W : A[X]) :
    ((S.map (Polynomial.taylorAlgHom (C x₀)).toRingHom).map (Polynomial.mapRingHom ψ)).eval W =
      ∑ a ∈ range (D + 1), (shiftedCoeff S x₀ a).eval₂ (C.comp ψ) W * X ^ a := by
  set Sshift : F[X][X][X] := S.map (Polynomial.taylorAlgHom (C x₀)).toRingHom
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le
    (Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le))]
  have hinner (b : ℕ) : (Sshift.map (Polynomial.mapRingHom ψ)).coeff b =
      ∑ a ∈ range (D + 1), C (ψ ((shiftedCoeff S x₀ a).coeff b)) * X ^ a := by
    have hSc : Sshift.coeff b = taylor (C x₀) (S.coeff b) := by rw [coeff_map]; rfl
    have hdegX : ((Sshift.coeff b).map ψ).natDegree < D + 1 := Nat.lt_succ_of_le <|
      Polynomial.natDegree_map_le.trans <| natDegree_le_iff_coeff_eq_zero.2 fun a ha =>
        by_contra fun hne => by
          have := shiftedCoeff_weighted_le hS_wd (a := a) (b := b)
            (by rw [coeff_shiftedCoeff, ← hSc]; exact hne)
          omega
    rw [coeff_map]
    change (Sshift.coeff b).map ψ = _
    rw [Polynomial.as_sum_range' _ (D + 1) hdegX]
    exact Finset.sum_congr rfl fun a _ => by
      rw [coeff_map, ← C_mul_X_pow_eq_monomial, coeff_shiftedCoeff, hSc]
  calc ∑ b ∈ range (S.natDegree + 1), (Sshift.map (Polynomial.mapRingHom ψ)).coeff b * W ^ b
      = ∑ b ∈ range (S.natDegree + 1),
          ∑ a ∈ range (D + 1), (C (ψ ((shiftedCoeff S x₀ a).coeff b)) * W ^ b) * X ^ a :=
        Finset.sum_congr rfl fun b _ => by
          rw [hinner b, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ a ∈ range (D + 1),
          ∑ b ∈ range (S.natDegree + 1), (C (ψ ((shiftedCoeff S x₀ a).coeff b)) * W ^ b) * X ^ a :=
        Finset.sum_comm
    _ = ∑ a ∈ range (D + 1), (shiftedCoeff S x₀ a).eval₂ (C.comp ψ) W * X ^ a :=
        Finset.sum_congr rfl fun a _ => by
          rw [← Finset.sum_mul,
            eval₂_eq_sum_range' (C.comp ψ) (Nat.lt_succ_of_le (natDegree_shiftedCoeff_le S x₀ a)) W]
          rfl

/-- Shifting `S(Z, X, P(X))` by `x₀` after mapping `F[Z] →+* A` matches evaluating `Sshift` at
`taylor (ψ (C x₀)) P`. -/
private theorem taylor_eval_map_eq_sum {A : Type*} [CommRing A]
    (ψ : F[X] →+* A) (S : F[X][X][X]) (x₀ : F) {w D : ℕ}
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D) (P : A[X]) :
    taylor (ψ (C x₀)) ((S.map (Polynomial.mapRingHom ψ)).eval P) =
      ∑ a ∈ range (D + 1),
        (shiftedCoeff S x₀ a).eval₂ (C.comp ψ) (taylor (ψ (C x₀)) P) * X ^ a := by
  let τ : A[X] →+* A[X] := (Polynomial.taylorAlgHom (ψ (C x₀))).toRingHom
  have hcomm : τ.comp (Polynomial.mapRingHom ψ) =
      (Polynomial.mapRingHom ψ).comp (Polynomial.taylorAlgHom (C x₀)).toRingHom := by
    apply Polynomial.ringHom_ext'
    · apply RingHom.ext; intro p
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, τ,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change taylor (ψ (C x₀)) (C (ψ p)) = (taylor (C x₀) (C p)).map ψ
      rw [taylor_C, taylor_C, Polynomial.map_C]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, τ,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change taylor (ψ (C x₀)) X = (taylor (C x₀) X).map ψ
      rw [taylor_X, taylor_X, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  have h1 : τ ((S.map (Polynomial.mapRingHom ψ)).eval P) =
      ((S.map (Polynomial.taylorAlgHom (C x₀)).toRingHom).map (Polynomial.mapRingHom ψ)).eval
        (τ P) := by
    have hhom := Polynomial.hom_eval₂ (S.map (Polynomial.mapRingHom ψ)) (RingHom.id A[X]) τ P
    rw [RingHom.comp_id, Polynomial.eval₂_id] at hhom
    rw [hhom, Polynomial.eval₂_map, hcomm, ← Polynomial.eval₂_map, ← Polynomial.eval_map,
      Polynomial.map_map]
  change τ ((S.map (Polynomial.mapRingHom ψ)).eval P) = _
  rw [h1]
  exact eval_map_shifted_eq_sum ψ S x₀ hS_wd (τ P)

/-- Universal `γ²`-scaled Taylor recurrence polynomials `N_n(Z, Y) ∈ F[Z][Y]` (zero `PowerSeries`).
-/
private noncomputable def recPoly (S : F[X][X][X]) (x₀ : F) (s : ℕ) : ℕ → F[X][X]
  | 0 => X
  | n + 1 =>
    let S₀ := S.map (Polynomial.evalRingHom (C x₀))
    let γ := S₀.derivative
    let U : (F[X][X])[X] := ∑ k ∈ (Icc 1 n).attach, C (recPoly S x₀ s k.1) * X ^ k.1
    Neg.neg (∑ a ∈ range (n + 2), ∑ j ∈ range (s + 1),
      if (a = 0 ∧ j = 0) ∨ (a = 0 ∧ j = 1) then 0
      else hasseDeriv j (shiftedCoeff S x₀ a) * γ ^ (2 * a + j - 2) *
        (U ^ j).coeff (n + 1 - a))
termination_by n => n
decreasing_by
  have := (Finset.mem_Icc.1 k.2).2
  omega

/-- Truncated universal series `U_M(T) = ∑_{k=1}^M N_k(Z, Y) T^k ∈ (F[Z][Y])[T]`. -/
private noncomputable def recU (S : F[X][X][X]) (x₀ : F) (s M : ℕ) : (F[X][X])[X] :=
  ∑ k ∈ Icc 1 M, C (recPoly S x₀ s k) * X ^ k

private theorem coeff_recU_zero (S : F[X][X][X]) (x₀ : F) (s M : ℕ) :
    (recU S x₀ s M).coeff 0 = 0 := by
  rw [recU, coeff_sum_Icc_C_mul_X_pow, ite_eq_right (by omega)]

private theorem coeff_recU (S : F[X][X][X]) (x₀ : F) (s M k : ℕ) :
    (recU S x₀ s M).coeff k = if 1 ≤ k ∧ k ≤ M then recPoly S x₀ s k else 0 :=
  coeff_sum_Icc_C_mul_X_pow 1 M k (recPoly S x₀ s)

private theorem recPoly_succ (S : F[X][X][X]) (x₀ : F) (s n : ℕ) :
    recPoly S x₀ s (n + 1) =
      -(∑ a ∈ range (n + 2), ∑ j ∈ range (s + 1),
        if (a = 0 ∧ j = 0) ∨ (a = 0 ∧ j = 1) then 0
        else hasseDeriv j (shiftedCoeff S x₀ a) *
          (S.map (Polynomial.evalRingHom (C x₀))).derivative ^ (2 * a + j - 2) *
          ((recU S x₀ s n) ^ j).coeff (n + 1 - a)) := by
  rw [recPoly]
  rw [Finset.sum_attach (Icc 1 n) (fun k => C (recPoly S x₀ s k) * X ^ k)]
  rfl

/-- Degree bound on coefficients of `U ^ j` when `U.coeff 0 = 0` and
`deg (U.coeff k) ≤ (2 * k - 1) * B` for all `k ≥ 1`. -/
private theorem deg_pow_coeff_le {R : Type*} [CommRing R] (db : DegBound R)
    {U : R[X]} {B : ℕ} (hU0 : U.coeff 0 = 0)
    (hUk : ∀ k, 1 ≤ k → U.coeff k ≠ 0 → db.deg (U.coeff k) ≤ (2 * k - 1) * B) :
    ∀ j, 1 ≤ j → ∀ t, (U ^ j).coeff t ≠ 0 →
      j ≤ t ∧ db.deg ((U ^ j).coeff t) ≤ (2 * t - j) * B := by
  intro j
  induction j with
  | zero => intro hj; omega
  | succ j ihj =>
    intro _ t hne
    cases j with
    | zero =>
      rw [pow_one] at hne ⊢
      have ht : 1 ≤ t := Nat.pos_of_ne_zero fun h0 => by subst h0; exact hne hU0
      exact ⟨ht, hUk t ht hne⟩
    | succ j =>
      have ht_ge : j + 2 ≤ t := by_contra fun hlt =>
        hne (coeff_pow_eq_zero_of_lt_of_coeff_zero hU0 (j + 2) t (by omega))
      refine ⟨ht_ge, ?_⟩
      rw [pow_succ, coeff_mul]
      refine db.sum_le _ _ fun x hx => ?_
      have hxsum : x.1 + x.2 = t := Finset.mem_antidiagonal.1 hx
      by_cases h1 : (U ^ (j + 1)).coeff x.1 = 0
      · rw [h1, zero_mul, db.zero]; exact Nat.zero_le _
      · by_cases h2 : U.coeff x.2 = 0
        · rw [h2, mul_zero, db.zero]; exact Nat.zero_le _
        · have hx2 : 1 ≤ x.2 := Nat.pos_of_ne_zero fun h0 => h2 (h0 ▸ hU0)
          have hIH1 := ihj (by omega) x.1 h1
          refine (db.mul_le _ _).trans <| (Nat.add_le_add hIH1.2 (hUk x.2 hx2 h2)).trans_eq ?_
          rw [← add_mul]; congr 1; omega

/-- Generic degree bound for `recPoly` under any `DegBound` on `F[Z][Y]`. -/
private theorem deg_recPoly_le (db : DegBound F[X][X])
    {S : F[X][X][X]} {x₀ : F} {s B : ℕ}
    (hS : ∀ a j, db.deg (hasseDeriv j (shiftedCoeff S x₀ a)) ≤ B)
    (hγ : db.deg (S.map (Polynomial.evalRingHom (C x₀))).derivative ≤ B) :
    ∀ n, 1 ≤ n → db.deg (recPoly S x₀ s n) ≤ (2 * n - 1) * B := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    cases n with
    | zero => omega
    | succ m =>
      have hUpow := deg_pow_coeff_le db (coeff_recU_zero S x₀ s m) (B := B) fun k hk hne => by
        rw [coeff_recU] at hne ⊢
        split_ifs at hne ⊢ with hkm
        · exact ih k (by omega) hkm.1
        · exact absurd rfl hne
      rw [recPoly_succ, db.neg]
      refine db.sum_le _ _ fun a ha => db.sum_le _ _ fun j _ => ?_
      have ha_le : a ≤ m + 1 := Nat.lt_succ_iff.1 (mem_range.1 ha)
      split_ifs with hskip
      · rw [db.zero]; exact Nat.zero_le _
      · by_cases hj0 : j = 0
        · subst hj0
          by_cases han : a = m + 1
          · subst han
            have hcoeff : ((recU S x₀ s m) ^ 0).coeff 0 = 1 := by simp
            rw [Nat.sub_self, hcoeff, mul_one]
            refine (db.mul_le _ _).trans <|
              (Nat.add_le_add (hS (m + 1) 0) ((db.pow_le _ _).trans
                (Nat.mul_le_mul_left _ hγ))).trans_eq ?_
            have : B + (2 * (m + 1) + 0 - 2) * B = (1 + (2 * (m + 1) + 0 - 2)) * B := by ring
            rw [this]; congr 1; omega
          · rw [pow_zero, coeff_one, ite_eq_right (by omega), mul_zero, db.zero]
            exact Nat.zero_le _
        · by_cases hU0 : ((recU S x₀ s m) ^ j).coeff (m + 1 - a) = 0
          · rw [hU0, mul_zero, db.zero]; exact Nat.zero_le _
          · have hUdeg := hUpow j (by omega) (m + 1 - a) hU0
            refine (db.mul_le _ _).trans <| (Nat.add_le_add (db.mul_le _ _) le_rfl).trans ?_
            have h1 := hS a j
            have h2 := (db.pow_le _ (2 * a + j - 2)).trans (Nat.mul_le_mul_left _ hγ)
            have hle := Nat.add_le_add (Nat.add_le_add h1 h2) hUdeg.2
            refine hle.trans_eq ?_
            calc B + (2 * a + j - 2) * B + (2 * (m + 1 - a) - j) * B
                = (1 + (2 * a + j - 2) + (2 * (m + 1 - a) - j)) * B := by ring
              _ = (2 * (m + 1) - 1) * B := by congr 1; have := hUdeg.1; omega

private theorem degZ₂_recPoly_le {S : F[X][X][X]} {x₀ : F} {s B_Z : ℕ}
    (hS_degZ : degZ S ≤ B_Z) :
    ∀ n, 1 ≤ n → degZ₂ (recPoly S x₀ s n) ≤ (2 * n - 1) * B_Z :=
  deg_recPoly_le (DegBound.degZ₂ F)
    (fun a j => (degZ₂_hasseDeriv_le j _).trans ((degZ₂_shiftedCoeff_le S x₀ a).trans hS_degZ))
    ((degZ₂_derivative_le _).trans (by
      rw [← shiftedCoeff_zero]; exact (degZ₂_shiftedCoeff_le S x₀ 0).trans hS_degZ))

private theorem natDegree_recPoly_le {S : F[X][X][X]} {x₀ : F} {s : ℕ}
    (hS_deg : S.natDegree ≤ s) :
    ∀ n, 1 ≤ n → (recPoly S x₀ s n).natDegree ≤ (2 * n - 1) * s := by
  refine deg_recPoly_le (DegBound.natDegree F[X]) (fun a j => ?_) ?_
  · exact (Polynomial.natDegree_hasseDeriv_le _ j).trans
      ((Nat.sub_le _ _).trans ((natDegree_shiftedCoeff_le S x₀ a).trans hS_deg))
  · refine (Polynomial.natDegree_derivative_le _).trans ?_
    have h1 : (S.map (Polynomial.evalRingHom (C x₀))).natDegree ≤ s :=
      Polynomial.natDegree_map_le.trans hS_deg
    omega

private theorem eval₂_shifted_comp_mul_X_coeff {A : Type*} [CommRing A]
    (S : F[X][X][X]) (x₀ : F) {s : ℕ} (hS_deg : S.natDegree ≤ s)
    (φ : F[X][X] →+* A) (g : A) (U : A[X]) {a n : ℕ} (han : a ≤ n) :
    (((shiftedCoeff S x₀ a).eval₂ (C.comp (φ.comp C)) (C (φ X) + C g * U)) *
      (C (g ^ 2) * X) ^ a).coeff n =
      ∑ j ∈ range (s + 1),
        φ (hasseDeriv j (shiftedCoeff S x₀ a)) * g ^ (2 * a + j) * (U ^ j).coeff (n - a) := by
  rw [mul_pow, ← C_pow, ← mul_assoc, coeff_mul_X_pow', ite_eq_left han,
    eval₂_add_eq_sum_hasseDeriv (C.comp (φ.comp C)) _
      ((natDegree_shiftedCoeff_le S x₀ a).trans hS_deg) (C (φ X)) (C g * U),
    Finset.sum_mul, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hev : (hasseDeriv j (shiftedCoeff S x₀ a)).eval₂ (C.comp (φ.comp C)) (C (φ X)) =
      C (φ (hasseDeriv j (shiftedCoeff S x₀ a))) := by
    rw [← Polynomial.hom_eval₂ _ (φ.comp C) (C : A →+* A[X]) (φ X)]
    congr 1
    simpa only [Polynomial.eval₂_C_X] using
      (Polynomial.hom_eval₂ (hasseDeriv j (shiftedCoeff S x₀ a)) C φ X).symm
  rw [hev, mul_pow, ← C_pow,
    show C (φ (hasseDeriv j (shiftedCoeff S x₀ a))) * (C (g ^ j) * U ^ j) * C ((g ^ 2) ^ a) =
      C (φ (hasseDeriv j (shiftedCoeff S x₀ a)) * g ^ (2 * a + j)) * U ^ j by
      rw [pow_add, pow_mul, map_mul, map_mul]; ring,
    coeff_C_mul]

/-- Specialization uniqueness: for any domain homomorphism `φ : F[Z][Y] →+* A` with `φ S₀ = 0`
and `φ γ ≠ 0`, any polynomial `W ∈ A[X]` solving `∑_a S̃_a(W) X^a = 0` with `W(0) = φ Y`
satisfies `(φ γ)^(2 n - 1) * W.coeff n = φ (N_n)` for every `n ≥ 1`. -/
private theorem coeff_eq_map_recPoly {A : Type*} [CommRing A] [IsDomain A]
    {S : F[X][X][X]} {x₀ : F} {s w D : ℕ}
    (hs1 : 1 ≤ s) (hS_deg : S.natDegree ≤ s)
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D)
    (φ : F[X][X] →+* A)
    (hγ_ne : φ (S.map (Polynomial.evalRingHom (C x₀))).derivative ≠ 0)
    {W : A[X]} (hW0 : W.coeff 0 = φ X)
    (hWeq : ∑ a ∈ range (D + 1), (shiftedCoeff S x₀ a).eval₂ (C.comp (φ.comp C)) W * X ^ a = 0) :
    ∀ n, 1 ≤ n →
      (φ (S.map (Polynomial.evalRingHom (C x₀))).derivative) ^ (2 * n - 1) * W.coeff n =
      φ (recPoly S x₀ s n) := by
  set S₀ := S.map (Polynomial.evalRingHom (C x₀))
  set γ := S₀.derivative
  set g : A := φ γ
  set U_W : A[X] := ∑ k ∈ Icc 1 W.natDegree, C (g ^ (2 * k - 1) * W.coeff k) * X ^ k
  have hU_W_zero : U_W.coeff 0 = 0 := by
    rw [coeff_sum_Icc_C_mul_X_pow, ite_eq_right (by omega)]
  have hU_W_coeff : ∀ k, 1 ≤ k → U_W.coeff k = g ^ (2 * k - 1) * W.coeff k := fun k hk1 => by
    rw [coeff_sum_Icc_C_mul_X_pow]
    split_ifs with hk
    · rfl
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  have hW_comp : W.comp (C (g ^ 2) * X) = C (φ X) + C g * U_W := by
    ext k
    rw [Polynomial.comp_C_mul_X_coeff, coeff_add, coeff_C_mul]
    cases k with
    | zero => rw [pow_zero, mul_one, coeff_C_zero, hU_W_zero, mul_zero, add_zero, hW0]
    | succ k =>
      rw [coeff_C_succ, zero_add, hU_W_coeff (k + 1) (by omega), ← pow_mul,
        mul_comm (W.coeff (k + 1)), ← mul_assoc, ← pow_succ']
      rfl
  have hcomp0 : ∑ a ∈ range (D + 1),
      ((shiftedCoeff S x₀ a).eval₂ (C.comp (φ.comp C)) (C (φ X) + C g * U_W)) *
        (C (g ^ 2) * X) ^ a = 0 := by
    have hc := congrArg (fun p : A[X] => p.comp (C (g ^ 2) * X)) hWeq
    rw [Polynomial.zero_comp, Polynomial.sum_comp] at hc
    refine (Finset.sum_congr rfl fun a _ => ?_).symm.trans hc
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, ← hW_comp]
    congr 1
    have hfc : (Polynomial.compRingHom (C (g ^ 2) * X)).comp (C.comp (φ.comp C)) =
        C.comp (φ.comp C) := RingHom.ext fun c => by simp [Polynomial.compRingHom]
    have hhom := Polynomial.hom_eval₂ (shiftedCoeff S x₀ a) (C.comp (φ.comp C))
      (Polynomial.compRingHom (C (g ^ 2) * X)) W
    rw [hfc] at hhom; exact hhom
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    cases n with
    | zero => omega
    | succ m =>
      have hc0 := congrArg (fun p : A[X] => p.coeff (m + 1)) hcomp0
      rw [coeff_zero, finsetSum_coeff] at hc0
      set term : ℕ → A := fun a => ∑ j ∈ range (s + 1),
        φ (hasseDeriv j (shiftedCoeff S x₀ a)) * g ^ (2 * a + j) * (U_W ^ j).coeff (m + 1 - a)
      have hmin_eq : ∑ a ∈ range (min D (m + 1) + 1), term a = 0 := by
        have hsub : ∑ a ∈ range (min D (m + 1) + 1),
            (((shiftedCoeff S x₀ a).eval₂ (C.comp (φ.comp C)) (C (φ X) + C g * U_W)) *
              (C (g ^ 2) * X) ^ a).coeff (m + 1) = 0 :=
          (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_left _ _)))
            fun a ha ha_not => by
              rw [mem_range] at ha ha_not
              rw [mul_pow, ← C_pow, ← mul_assoc, coeff_mul_X_pow',
                ite_eq_right (by omega : ¬ a ≤ m + 1)]).trans hc0
        exact (Finset.sum_congr rfl fun a ha =>
          eval₂_shifted_comp_mul_X_coeff S x₀ hS_deg φ g U_W
            (by rw [mem_range] at ha; omega)).symm.trans hsub
      have hsum_eq : ∑ a ∈ range (m + 2), term a = 0 :=
        (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_right _ _)))
          fun a ha ha_not => Finset.sum_eq_zero fun j _ => by
            rw [mem_range] at ha ha_not
            rw [shiftedCoeff_eq_zero_of_gt hS_wd (by omega),
              map_zero, map_zero, zero_mul, zero_mul]).symm.trans hmin_eq
      set U_map : A[X] := (recU S x₀ s m).map φ
      have hU_map_zero : U_map.coeff 0 = 0 := by rw [coeff_map, coeff_recU_zero, map_zero]
      have hagree : ∀ k ≤ m, U_W.coeff k = U_map.coeff k := fun k hk => by
        rw [coeff_map, coeff_recU]
        by_cases hk1 : 1 ≤ k
        · rw [ite_eq_left ⟨hk1, hk⟩, hU_W_coeff k hk1]; exact ih k (by omega) hk1
        · have hk0 : k = 0 := by omega
          subst hk0; rw [ite_eq_right (by omega), hU_W_zero, map_zero]
      have hsplit : ∀ a ∈ range (m + 2), ∀ j ∈ range (s + 1),
          φ (hasseDeriv j (shiftedCoeff S x₀ a)) * g ^ (2 * a + j) * (U_W ^ j).coeff (m + 1 - a) =
          (if a = 0 ∧ j = 1 then g ^ 2 * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1)) else 0) +
          g ^ 2 * φ (if (a = 0 ∧ j = 0) ∨ (a = 0 ∧ j = 1) then 0
            else hasseDeriv j (shiftedCoeff S x₀ a) * γ ^ (2 * a + j - 2) *
              ((recU S x₀ s m) ^ j).coeff (m + 1 - a)) := fun a ha j _ => by
        have ha_le : a ≤ m + 1 := Nat.lt_succ_iff.1 (mem_range.1 ha)
        by_cases h00 : a = 0 ∧ j = 0
        · rcases h00 with ⟨rfl, rfl⟩
          simp [coeff_one]
        · by_cases h01 : a = 0 ∧ j = 1
          · rcases h01 with ⟨rfl, rfl⟩
            simp only [and_self, ↓reduceIte, or_true, map_zero, mul_zero, add_zero, Nat.sub_zero,
              pow_one, shiftedCoeff_zero, hasseDeriv_one', hU_W_coeff (m + 1) (by omega),
              mul_zero, zero_add]
            change g * g * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1)) = _
            ring
          · rw [ite_eq_right h01, zero_add, ite_eq_right (by tauto : ¬ ((a = 0 ∧ j = 0) ∨ _))]
            have hpow : g ^ (2 * a + j) = g ^ 2 * g ^ (2 * a + j - 2) := by
              rw [← pow_add]; congr 1; omega
            have hUeq : (U_W ^ j).coeff (m + 1 - a) =
                φ (((recU S x₀ s m) ^ j).coeff (m + 1 - a)) := by
              rw [← coeff_map, Polynomial.map_pow]
              rcases eq_or_ne j 0 with rfl | hj0
              · simp
              · exact coeff_pow_eq_of_coeff_eq_of_coeff_zero hU_W_zero hU_map_zero hagree j
                  (by omega) (m + 1 - a) (by omega)
            rw [hpow, hUeq, map_mul, map_mul, map_pow]
            change _ = g ^ 2 * (φ _ * g ^ (2 * a + j - 2) * φ _); ring
      have hsum_split : (∑ a ∈ range (m + 2), ∑ j ∈ range (s + 1),
          if a = 0 ∧ j = 1 then g ^ 2 * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1)) else 0) +
          g ^ 2 * φ (-recPoly S x₀ s (m + 1)) = 0 := by
        rw [recPoly_succ, neg_neg, map_sum, Finset.mul_sum]
        simp_rw [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact (Finset.sum_congr rfl fun a ha =>
          Finset.sum_congr rfl fun j hj => hsplit a ha j hj).symm.trans hsum_eq
      have hmain : (∑ a ∈ range (m + 2), ∑ j ∈ range (s + 1),
          if a = 0 ∧ j = 1 then g ^ 2 * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1)) else 0) =
          g ^ 2 * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1)) := by
        rw [Finset.sum_eq_single 0 (fun a _ ha0 => Finset.sum_eq_zero fun _ _ => by simp [ha0])
          (fun h => absurd (mem_range.2 (by omega)) h),
          Finset.sum_eq_single 1 (fun j _ hj1 => by simp [hj1])
          (fun h => absurd (mem_range.2 (by omega)) h)]
        simp
      rw [hmain, map_neg] at hsum_split
      have hfac : g ^ 2 * (g ^ (2 * (m + 1) - 1) * W.coeff (m + 1) -
          φ (recPoly S x₀ s (m + 1))) = 0 := by linear_combination hsum_split
      exact sub_eq_zero.1 ((mul_eq_zero.1 hfac).resolve_left (pow_ne_zero 2 hγ_ne))

end Step5Recurrence

section Step6ResultantKillAndLift

variable {F : Type*} [Field F]

/-- In prime characteristic `p`, `(Q ^ (p ^ e)).coeff n = 0` whenever `¬ p ^ e ∣ n`. -/
private theorem coeff_pow_prime_pow_eq_zero_of_not_dvd {R : Type*} [CommRing R] {p e : ℕ}
    [CharP R p] (hp : p.Prime) (Q : R[X]) {n : ℕ} (hndiv : ¬ p ^ e ∣ n) :
    (Q ^ (p ^ e)).coeff n = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Polynomial.map_iterateFrobenius_expand p Q e, coeff_map,
    coeff_expand_eq_zero_of_not_dvd (pow_pos hp.pos e) Q hndiv, map_zero]

/-- In a domain whose characteristic matches `μ`, `a ^ μ = b ^ μ → a = b`. -/
private theorem eq_of_pow_eq_of_char_pow {A : Type*} [CommRing A] [IsDomain A] {μ : ℕ}
    (hμ : μ = 1 ∨ ∃ (p e : ℕ), CharP A p ∧ p.Prime ∧ μ = p ^ e) {a b : A} (h : a ^ μ = b ^ μ) :
    a = b := by
  rcases hμ with rfl | ⟨p, e, hcp, hp, rfl⟩
  · simpa using h
  · have : Fact p.Prime := ⟨hp⟩
    exact iterateFrobenius_inj A p e (by simpa only [iterateFrobenius_def] using h)

/-- Evaluation mismatch polynomial `E_i(Z, Y) ∈ F[Z][Y]` capturing
`P*(α i)^μ - w_i(Z)^μ` cleared by `γ^(2 μ d - 1)` (or `Y - w_i(Z)^μ` when `μ * d = 0`). -/
private noncomputable def evalMismatchPoly (S : F[X][X][X]) (x₀ : F) (s μ d : ℕ)
    (a : F) (w : F[X]) : F[X][X] :=
  let γ := (S.map (Polynomial.evalRingHom (C x₀))).derivative
  if μ * d = 0 then
    X - C (w ^ μ)
  else
    X * γ ^ (2 * (μ * d) - 1) +
      (∑ k ∈ Icc 1 (μ * d),
        recPoly S x₀ s k * γ ^ (2 * (μ * d - k)) * C (C ((a - x₀) ^ k))) -
      C (w ^ μ) * γ ^ (2 * (μ * d) - 1)

private theorem deg_evalMismatchPoly_le (db : DegBound F[X][X])
    {S : F[X][X][X]} {x₀ : F} {s μ d Bx B Bw : ℕ}
    (hX : db.deg X ≤ Bx) (hBx : Bx ≤ B)
    (hCC : ∀ c : F, db.deg (C (C c)) = 0)
    (a : F) (w : F[X]) (hw : db.deg (C (w ^ μ)) ≤ Bw)
    (hγ : db.deg (S.map (Polynomial.evalRingHom (C x₀))).derivative ≤ B)
    (hrec : ∀ k, 1 ≤ k → db.deg (recPoly S x₀ s k) ≤ (2 * k - 1) * B) :
    db.deg (evalMismatchPoly S x₀ s μ d a w) ≤
      if μ * d = 0 then max Bx Bw else 2 * (μ * d) * B + Bw := by
  set γ := (S.map (Polynomial.evalRingHom (C x₀))).derivative
  rw [evalMismatchPoly]
  split_ifs with h0
  · exact (db.sub_le _ _).trans (max_le (hX.trans (le_max_left _ _)) (hw.trans (le_max_right _ _)))
  · have hγp (e : ℕ) : db.deg (γ ^ e) ≤ e * B := (db.pow_le _ _).trans (Nat.mul_le_mul_left _ hγ)
    have hmul_sub : B + (2 * (μ * d) - 1) * B = 2 * (μ * d) * B := by
      calc B + (2 * (μ * d) - 1) * B = (1 + (2 * (μ * d) - 1)) * B := by ring
        _ = 2 * (μ * d) * B := by congr 1; omega
    refine (db.sub_le _ _).trans (max_le ((db.add_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact (db.mul_le _ _).trans (by
        have h1 := hγp (2 * (μ * d) - 1)
        exact (Nat.add_le_add (hX.trans hBx) h1).trans (by omega))
    · refine db.sum_le _ _ fun k hk => (db.mul_le _ _).trans ?_
      rw [hCC, add_zero]
      refine (db.mul_le _ _).trans ?_
      have hk_mem := mem_Icc.1 hk
      have h1 := hrec k hk_mem.1; have h2 := hγp (2 * (μ * d - k))
      have hle : (2 * k - 1) * B + 2 * (μ * d - k) * B ≤ 2 * (μ * d) * B := by
        rw [← add_mul]; exact Nat.mul_le_mul_right B (by omega)
      exact (Nat.add_le_add h1 h2).trans (hle.trans (Nat.le_add_right _ _))
    · have h1 := hγp (2 * (μ * d) - 1)
      have hle : (2 * (μ * d) - 1) * B ≤ 2 * (μ * d) * B :=
        Nat.mul_le_mul_right B (by omega)
      exact (db.mul_le _ _).trans ((Nat.add_le_add hw (h1.trans hle)).trans_eq (add_comm _ _))

/-- Evaluating `evalMismatchPoly` under any hom `φ : F[Z][Y] →+* A` matching the recurrence
coefficients of a polynomial `W ∈ A[X]` of degree `≤ μ * d`. -/
private theorem map_evalMismatchPoly {A : Type*} [CommRing A]
    {S : F[X][X][X]} {x₀ : F} {s μ d : ℕ} (a : F) (w : F[X])
    (φ : F[X][X] →+* A) {W : A[X]}
    (hW_deg : W.natDegree ≤ μ * d) (hW0 : W.coeff 0 = φ X)
    (hWk : ∀ k ∈ Icc 1 (μ * d),
      (φ (S.map (Polynomial.evalRingHom (C x₀))).derivative) ^ (2 * k - 1) * W.coeff k =
      φ (recPoly S x₀ s k)) :
    φ (evalMismatchPoly S x₀ s μ d a w) =
      (φ (S.map (Polynomial.evalRingHom (C x₀))).derivative) ^
          (if μ * d = 0 then 0 else 2 * (μ * d) - 1) *
        (W.eval (φ (C (C (a - x₀)))) - (φ (C w)) ^ μ) := by
  set γ := (S.map (Polynomial.evalRingHom (C x₀))).derivative
  set g := φ γ
  rw [evalMismatchPoly]
  split_ifs with h0
  · rw [pow_zero, one_mul, map_sub, C_pow, map_pow,
      Polynomial.eq_C_of_natDegree_eq_zero (p := W) (by omega), hW0, eval_C]
  · have hWeval : g ^ (2 * (μ * d) - 1) * W.eval (φ (C (C (a - x₀)))) =
        φ X * g ^ (2 * (μ * d) - 1) +
          ∑ k ∈ Icc 1 (μ * d),
            φ (recPoly S x₀ s k) * g ^ (2 * (μ * d - k)) * φ (C (C ((a - x₀) ^ k))) := by
      rw [eval_eq_sum_range' (Nat.lt_succ_of_le hW_deg), Finset.mul_sum, Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot (Nat.zero_lt_succ (μ * d)), pow_zero, mul_one, hW0,
        mul_comm (g ^ _), show Finset.Ico 1 (μ * d + 1) = Icc 1 (μ * d) by ext; simp]
      refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
      have ⟨hk1, hkle⟩ := mem_Icc.1 hk
      rw [show g ^ (2 * (μ * d) - 1) = g ^ (2 * (μ * d - k)) * g ^ (2 * k - 1) by
          rw [← pow_add]; congr 1; omega,
        show φ (C (C (a - x₀))) ^ k = φ (C (C ((a - x₀) ^ k))) by rw [← map_pow, ← C_pow, ← C_pow],
        ← hWk k hk]
      ring
    rw [map_sub, map_add, map_mul, map_pow, map_sum, map_mul, C_pow, map_pow, map_pow]
    have hsum_map :
        ∑ k ∈ Icc 1 (μ * d),
          φ (recPoly S x₀ s k * γ ^ (2 * (μ * d - k)) * C (C ((a - x₀) ^ k))) =
        ∑ k ∈ Icc 1 (μ * d),
          φ (recPoly S x₀ s k) * g ^ (2 * (μ * d - k)) * φ (C (C ((a - x₀) ^ k))) :=
      Finset.sum_congr rfl fun k _ => by rw [map_mul, map_mul, map_pow]
    rw [hsum_map]
    change φ X * g ^ (2 * (μ * d) - 1) + _ - φ (C w) ^ μ * g ^ (2 * (μ * d) - 1) = _
    linear_combination -hWeval

private theorem spec_recPoly_at_point {S : F[X][X][X]} {x₀ : F} {w D μ : ℕ}
    (hS_deg : 1 ≤ S.natDegree)
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + w * b ≤ D)
    {z : F} {P : F[X]} (hS_eval0 : (evZ₂ z S).eval (P ^ μ) = 0)
    (hγ_ne : ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
      ((P ^ μ).eval x₀) ≠ 0) :
    ∀ n, 1 ≤ n →
      (((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
        ((P ^ μ).eval x₀)) ^ (2 * n - 1) * (taylor x₀ (P ^ μ)).coeff n =
      ((recPoly S x₀ S.natDegree n).map (evZ z)).eval ((P ^ μ).eval x₀) := by
  let φz : F[X][X] →+* F := Polynomial.eval₂RingHom (evZ z) ((P ^ μ).eval x₀)
  have hφz_eq : ∀ f : F[X][X], φz f = (f.map (evZ z)).eval ((P ^ μ).eval x₀) := fun f => by
    simp [φz, Polynomial.eval_map]
  have hWeq : ∑ a ∈ range (D + 1),
      (shiftedCoeff S x₀ a).eval₂ (C.comp (φz.comp C)) (taylor x₀ (P ^ μ)) * X ^ a = 0 := by
    rw [show φz.comp C = evZ z from RingHom.ext fun p => by simp [φz]]
    have ht := taylor_eval_map_eq_sum (evZ z) S x₀ hS_wd (P ^ μ)
    rw [show (evZ z) (C x₀) = x₀ by simp [evZ]] at ht
    change _ = 0; rw [← ht]
    change taylor x₀ ((evZ₂ z S).eval (P ^ μ)) = 0
    rw [hS_eval0, map_zero]
  intro n hn
  have hrec := coeff_eq_map_recPoly hS_deg le_rfl hS_wd φz (by rwa [hφz_eq])
    (by rw [taylor_coeff_zero]; simp [φz]) hWeq n hn
  change (φz _ ^ (2 * n - 1)) * (taylor x₀ (P ^ μ)).coeff n = φz _ at hrec
  rwa [hφz_eq, hφz_eq] at hrec

private theorem exists_pow_eq_poly_of_not_dvd {L : Type*} [Field L] [IsAlgClosed L]
    {μ d : ℕ} (hμ_pos : 1 ≤ μ)
    (hμ_char : μ = 1 ∨ ∃ (p e : ℕ), CharP L p ∧ p.Prime ∧ μ = p ^ e)
    {Ψ : L[X]} (hΨ_deg : Ψ.natDegree ≤ μ * d) (hndiv : ∀ k, ¬ μ ∣ k → Ψ.coeff k = 0) :
    ∃ Ptilde : L[X], Ptilde.natDegree ≤ d ∧ Ptilde ^ μ = Ψ := by
  classical
  rcases hμ_char with rfl | ⟨p, e, _, hp, rfl⟩
  · exact ⟨Ψ, by simpa only [one_mul] using hΨ_deg, pow_one Ψ⟩
  · have : Fact p.Prime := ⟨hp⟩
    choose c hc using fun m : Fin (d + 1) =>
      IsAlgClosed.exists_pow_nat_eq (Ψ.coeff (m.1 * p ^ e)) (pow_pos hp.pos e)
    refine ⟨Polynomial.ofFn (d + 1) c,
      Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos d) c), ?_⟩
    rw [← Polynomial.map_iterateFrobenius_expand p (Polynomial.ofFn (d + 1) c) e]
    ext k
    rw [coeff_map, iterateFrobenius_def, Polynomial.coeff_expand (pow_pos hp.pos e)]
    split_ifs with hdiv
    · by_cases hm : k / p ^ e < d + 1
      · rw [Polynomial.ofFn_coeff_eq_val_of_lt c hm, hc ⟨k / p ^ e, hm⟩, Nat.div_mul_cancel hdiv]
      · rw [Polynomial.ofFn_coeff_eq_zero_of_ge c (by omega), zero_pow (by omega)]
        have hmul : (d + 1) * p ^ e ≤ k := (Nat.le_div_iff_mul_le hμ_pos).1 (by omega)
        have hadd : p ^ e * d + p ^ e = (d + 1) * p ^ e := by ring
        exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
    · rw [zero_pow (by omega), hndiv k hdiv]

private theorem resultant_evalMismatch_natDegree_le {ι : Type*} [DecidableEq F]
    {r d D B_Z D_Y μ : ℕ} {S : F[X][X][X]} {Fstar : F[X][X]} {x₀ : F}
    {u : Fin (r + 1) → (ι → F)} (α : ι → F) (i : ι)
    (hμ_pos : 1 ≤ μ) (hS_deg : 1 ≤ S.natDegree) (hDY_pos : 1 ≤ D_Y) (hD_pos : 1 ≤ D)
    (hμs_le : μ * S.natDegree ≤ D_Y) (hμd_le : μ * d ≤ D) (hS_degZ : degZ S ≤ B_Z)
    (hF_deg_le : Fstar.natDegree ≤ S.natDegree) (hF_degZ : degZ₂ Fstar ≤ B_Z) :
    let Ei := evalMismatchPoly S x₀ S.natDegree μ d (α i) (curveWord u i)
    (Polynomial.resultant Fstar Ei Fstar.natDegree Ei.natDegree).natDegree ≤
      4 * D * D_Y * B_Z + r * D_Y ^ 2 := by
  intro Ei
  have hs_le_DY : S.natDegree ≤ D_Y := (Nat.le_mul_of_pos_left _ hμ_pos).trans hμs_le
  have hF_le_DY : Fstar.natDegree ≤ D_Y := hF_deg_le.trans hs_le_DY
  have hμF_sq : Fstar.natDegree * (μ * r) ≤ r * D_Y ^ 2 := by
    have h1 : μ * Fstar.natDegree ≤ D_Y := (Nat.mul_le_mul_left μ hF_deg_le).trans hμs_le
    calc Fstar.natDegree * (μ * r) = r * (μ * Fstar.natDegree) := by ring
      _ ≤ r * D_Y := Nat.mul_le_mul_left r h1
      _ ≤ r * (D_Y * D_Y) := Nat.mul_le_mul_left r (Nat.le_mul_of_pos_right D_Y hDY_pos)
      _ = r * D_Y ^ 2 := by ring
  have hw_degZ : degZ₂ (C ((curveWord u i) ^ μ)) ≤ μ * r := by
    rw [degZ₂_C]
    exact natDegree_pow_le.trans (Nat.mul_le_mul_left μ
      (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos r) _)))
  have hγ_degZ : degZ₂ (S.map (Polynomial.evalRingHom (C x₀))).derivative ≤ B_Z :=
    (degZ₂_derivative_le _).trans (by
      rw [← shiftedCoeff_zero]; exact (degZ₂_shiftedCoeff_le S x₀ 0).trans hS_degZ)
  have hEi_degZ := deg_evalMismatchPoly_le (DegBound.degZ₂ F) (s := S.natDegree) (μ := μ)
    (d := d) degZ₂_X.le (Nat.zero_le B_Z)
    (fun c => by change degZ₂ (C (C c)) = 0; rw [degZ₂_C, natDegree_C])
    (α i) (curveWord u i) hw_degZ hγ_degZ (degZ₂_recPoly_le hS_degZ)
  have hγ_degY : (S.map (Polynomial.evalRingHom (C x₀))).derivative.natDegree ≤ S.natDegree :=
    (Polynomial.natDegree_derivative_le _).trans
      ((Nat.sub_le _ _).trans Polynomial.natDegree_map_le)
  have hEi_degY := deg_evalMismatchPoly_le (DegBound.natDegree F[X]) (S := S) (x₀ := x₀)
    (s := S.natDegree) (μ := μ) (d := d) natDegree_X_le hS_deg (fun c => natDegree_C _)
    (α i) (curveWord u i) (by change (C (curveWord u i ^ μ)).natDegree ≤ 0; rw [natDegree_C])
    hγ_degY (natDegree_recPoly_le le_rfl)
  have hres := (DegBound.natDegree F).resultant_le Fstar.natDegree Ei.natDegree
    (degZ₂_le_iff.1 hF_degZ) (degZ₂_le_iff.1 hEi_degZ)
  split_ifs at hres hEi_degZ hEi_degY with h0
  · rw [Nat.zero_max] at hres; rw [Nat.max_zero] at hEi_degY
    have h1 : 1 ≤ 4 * D * D_Y := by
      have := Nat.mul_le_mul (show 1 ≤ 4 * D by omega) hDY_pos; simpa using this
    have h2 : Ei.natDegree * B_Z ≤ 4 * D * D_Y * B_Z :=
      Nat.mul_le_mul_right B_Z (hEi_degY.trans h1)
    exact hres.trans ((Nat.add_le_add hμF_sq h2).trans_eq (add_comm _ _))
  · have ha : Fstar.natDegree * (2 * (μ * d) * B_Z) ≤ 2 * D * D_Y * B_Z :=
      (Nat.mul_le_mul hF_le_DY
        (Nat.mul_le_mul_right B_Z (show 2 * (μ * d) ≤ 2 * D by omega))).trans_eq (by ring)
    have h2 : Ei.natDegree * B_Z ≤ 2 * D * D_Y * B_Z := Nat.mul_le_mul_right B_Z <|
      hEi_degY.trans (by rw [add_zero]; exact Nat.mul_le_mul (by omega) hs_le_DY)
    rw [mul_add] at hres
    exact hres.trans (by linarith [ha, hμF_sq, h2])

private theorem map_recPoly_dvd_of_kill {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} {r d D B_Z D_Y W_tot B_W μ : ℕ}
    {W : ι → ℕ} {u : Fin (r + 1) → (ι → F)}
    {S : F[X][X][X]} {Fstar : F[X][X]} {x₀ : F} {T'' : Finset F}
    (hμ_char : μ = 1 ∨ ∃ (p e : ℕ), CharP F p ∧ p.Prime ∧ μ = p ^ e)
    (hS_deg : 1 ≤ S.natDegree) (hs_le_DY : S.natDegree ≤ D_Y) (hW_tot_pos : 1 ≤ W_tot)
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + (μ * d) * b ≤ D) (hS_degZ : degZ S ≤ B_Z)
    (hF_irred : Irreducible Fstar) (hF_prim : Fstar.IsPrimitive)
    (hF_deg1 : 1 ≤ Fstar.natDegree) (hF_deg_le : Fstar.natDegree ≤ S.natDegree)
    (hF_degZ : degZ₂ Fstar ≤ B_Z)
    (hT''_card : W_tot * D_Y * (4 * D * B_Z + r * D_Y) < #T'')
    (hT''_mem : ∀ z ∈ T'', ∃ P : F[X], P.natDegree ≤ d ∧ (evZ₂ z S).eval (P ^ μ) = 0 ∧
      (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 ∧
      ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
        ((P ^ μ).eval x₀) ≠ 0 ∧
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i)
    {n : ℕ} (hn1 : 1 ≤ n) (hnD : n ≤ D) (hcond : μ * d < n ∨ ¬ μ ∣ n) :
    Fstar.map (algebraMap F[X] (FractionRing F[X])) ∣
      (recPoly S x₀ S.natDegree n).map (algebraMap F[X] (FractionRing F[X])) := by
  let K := FractionRing F[X]
  let ι_K : F[X] →+* K := algebraMap F[X] K
  set Nn := recPoly S x₀ S.natDegree n
  by_cases hNn0 : Nn = 0
  · rw [hNn0, Polynomial.map_zero]; exact dvd_zero _
  · set Res_n : F[X] := Polynomial.resultant Fstar Nn Fstar.natDegree Nn.natDegree
    have hRes_van : ∀ z ∈ T'', Res_n.eval z = 0 := fun z hz => by
      obtain ⟨P, hP_deg, hS_ev0, hF_ev0, hγ_ev_ne, _⟩ := hT''_mem z hz
      have hrec := spec_recPoly_at_point hS_deg hS_wd hS_ev0 hγ_ev_ne n hn1
      have hW0 : (taylor x₀ (P ^ μ)).coeff n = 0 := by
        rcases hcond with hgt | hndiv
        · exact coeff_eq_zero_of_natDegree_lt (by
            rw [natDegree_taylor]
            exact (natDegree_pow_le.trans (Nat.mul_le_mul_left μ hP_deg)).trans_lt hgt)
        · rcases hμ_char with rfl | ⟨p, e, _, hp, rfl⟩
          · exact absurd (one_dvd n) hndiv
          · have ht_pow : taylor x₀ (P ^ p ^ e) = (taylor x₀ P) ^ p ^ e :=
              map_pow (Polynomial.taylorAlgHom x₀) P (p ^ e)
            rw [ht_pow]
            exact coeff_pow_prime_pow_eq_zero_of_not_dvd hp (taylor x₀ P) hndiv
      rw [hW0, mul_zero] at hrec
      exact eval_resultant_eq_zero_of_common_root (Or.inl (by omega)) hF_ev0 hrec.symm
    have hNn_degZ : degZ₂ Nn ≤ (2 * n - 1) * B_Z := degZ₂_recPoly_le hS_degZ n hn1
    have hres := (DegBound.natDegree F).resultant_le Fstar.natDegree Nn.natDegree
      (degZ₂_le_iff.1 hF_degZ) (degZ₂_le_iff.1 hNn_degZ)
    have h1 : Fstar.natDegree * ((2 * n - 1) * B_Z) ≤ 2 * D * D_Y * B_Z :=
      (Nat.mul_le_mul (hF_deg_le.trans hs_le_DY)
        (Nat.mul_le_mul_right B_Z (show 2 * n - 1 ≤ 2 * D by omega))).trans_eq (by ring)
    have h2 : Nn.natDegree * B_Z ≤ 2 * D * D_Y * B_Z := Nat.mul_le_mul_right B_Z <|
      (natDegree_recPoly_le le_rfl n hn1).trans (Nat.mul_le_mul (by omega) hs_le_DY)
    have hlt : Res_n.natDegree < #T'' := by
      have htot : 1 * D_Y * (4 * D * B_Z) ≤ W_tot * D_Y * (4 * D * B_Z + r * D_Y) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right D_Y hW_tot_pos) (Nat.le_add_right _ _)
      have : Res_n.natDegree ≤ 4 * D * D_Y * B_Z :=
        hres.trans ((Nat.add_le_add h1 h2).trans_eq (by ring))
      linarith [show 4 * D * D_Y * B_Z = 1 * D_Y * (4 * D * B_Z) by ring]
    by_contra hndvd
    exact resultant_ne_zero_of_isCoprime_map ι_K (IsFractionRing.injective F[X] K)
      (((hF_prim.irreducible_iff_irreducible_map_fraction_map (K := K)).1 hF_irred
        ).coprime_iff_not_dvd.2 hndvd)
      (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Res_n T'' hRes_van hlt)

/-- Step 6: Resultant-kill excess and non-`μ`-divisible recurrence polynomials, lift to
`L := AlgebraicClosure (FractionRing F[Z])`, truncate to a polynomial root `Ψ_trunc`, extract
its Frobenius `μ`-th root `P* ∈ L[X]`, and package the mismatch resultant bounds for Step 7. -/
private theorem exists_lifted_poly_and_mismatch_bound {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} {r d D B_Z D_Y W_tot B_W μ : ℕ}
    {W : ι → ℕ} {u : Fin (r + 1) → (ι → F)}
    {R S : F[X][X][X]} {Δ Fstar : F[X][X]} {x₀ : F} {T'' : Finset F}
    (hμ_char : μ = 1 ∨ ∃ (p e : ℕ), CharP F p ∧ p.Prime ∧ μ = p ^ e)
    (hμ_pos : 1 ≤ μ)
    (hS_deg : 1 ≤ S.natDegree)
    (hdeg_mul : μ * S.natDegree = R.natDegree)
    (hR_deg_le : R.natDegree ≤ D_Y)
    (hDY_pos : 1 ≤ D_Y) (hD_pos : 1 ≤ D) (hW_tot_pos : 1 ≤ W_tot)
    (hμd_le : μ * d ≤ D)
    (hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + (μ * d) * b ≤ D)
    (hS_degZ : degZ S ≤ B_Z)
    (hΔ_x₀_ne : Δ.eval (C x₀) ≠ 0)
    (hbez₀ : ∃ A₀ B₀ : F[X][X],
      (S.map (Polynomial.evalRingHom (C x₀))) * A₀ +
        (S.map (Polynomial.evalRingHom (C x₀))).derivative * B₀ = C (Δ.eval (C x₀)))
    (hF_irred : Irreducible Fstar)
    (hF_prim : Fstar.IsPrimitive)
    (hF_deg1 : 1 ≤ Fstar.natDegree)
    (hF_deg_le : Fstar.natDegree ≤ S.natDegree)
    (hF_degZ : degZ₂ Fstar ≤ B_Z)
    (hF_dvd : Fstar ∣ S.map (Polynomial.evalRingHom (C x₀)))
    (hT''_card : W_tot * D_Y * (4 * D * B_Z + r * D_Y) < #T'')
    (hT''_mem : ∀ z ∈ T'',
      ∃ P : F[X], P.natDegree ≤ d ∧
        (evZ₂ z S).eval (P ^ μ) = 0 ∧
        (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 ∧
        ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
          ((P ^ μ).eval x₀) ≠ 0 ∧
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i) :
    let K := FractionRing F[X]
    let L := AlgebraicClosure K
    let j_L : F[X] →+* L := (algebraMap K L).comp (algebraMap F[X] K)
    ∃ (Pstar : L[X]) (Istar : Finset ι),
      Pstar.natDegree ≤ d ∧
      (∀ i ∈ Istar, Pstar.eval (j_L (C (α i))) = j_L (curveWord u i)) ∧
      (∀ i ∉ Istar, ∃ res : F[X], res ≠ 0 ∧
        res.natDegree ≤ 4 * D * D_Y * B_Z + r * D_Y ^ 2 ∧
        ∀ z ∈ T'', ∀ P : F[X], P.natDegree ≤ d →
          (evZ₂ z S).eval (P ^ μ) = 0 →
          (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 →
          ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
            ((P ^ μ).eval x₀) ≠ 0 →
          P.eval (α i) = (curveWord u i).eval z → res.eval z = 0) := by
  classical
  set s := S.natDegree
  set γ := (S.map (Polynomial.evalRingHom (C x₀))).derivative
  have hs_le_DY : s ≤ D_Y := (Nat.le_mul_of_pos_left s hμ_pos).trans (hdeg_mul.trans_le hR_deg_le)
  let K := FractionRing F[X]; let L := AlgebraicClosure K
  let ι_K : F[X] →+* K := algebraMap F[X] K; let ι_L : K →+* L := algebraMap K L
  let j_L : F[X] →+* L := ι_L.comp ι_K
  have hι_K_inj : Function.Injective ι_K := IsFractionRing.injective F[X] K
  have hj_L_inj : Function.Injective j_L := (RingHom.injective ι_L).comp hι_K_inj
  have hF_L_deg : (Fstar.map j_L).degree ≠ 0 := fun h => by
    have hm0 : Fstar.map j_L ≠ 0 := (Polynomial.map_ne_zero_iff hj_L_inj).2 hF_irred.ne_zero
    rw [Polynomial.degree_eq_natDegree hm0, Polynomial.natDegree_map_eq_of_injective hj_L_inj] at h
    have : Fstar.natDegree = 0 := by exact_mod_cast h
    omega
  obtain ⟨ystar, hystar⟩ := IsAlgClosed.exists_root (Fstar.map j_L) hF_L_deg
  let φstar : F[X][X] →+* L := Polynomial.eval₂RingHom j_L ystar
  have hφstar_eq (f : F[X][X]) : φstar f = (f.map j_L).eval ystar := by
    simp [φstar, Polynomial.eval_map]
  have hφstar_dvd_zero {g : F[X][X]} (hd : Fstar.map ι_K ∣ g.map ι_K) : φstar g = 0 := by
    rcases hd with ⟨qK, hqK⟩
    have hm := congrArg (Polynomial.map ι_L) hqK
    rw [Polynomial.map_mul, Polynomial.map_map, Polynomial.map_map] at hm
    rw [hφstar_eq, hm, eval_mul, hystar, zero_mul]
  have hφstar_γ : φstar γ ≠ 0 := fun h0 => by
    obtain ⟨A₀, B₀, hAB⟩ := hbez₀
    have hF0 : φstar Fstar = 0 := by rw [hφstar_eq]; exact hystar
    rcases hF_dvd with ⟨Q', hQ'⟩
    have hS0 : φstar (S.map (Polynomial.evalRingHom (C x₀))) = 0 := by
      rw [hQ', map_mul, hF0, zero_mul]
    have hm := congrArg φstar hAB
    simp only [map_add, map_mul, hS0, zero_mul, zero_add, h0] at hm
    exact hΔ_x₀_ne (hj_L_inj (by simpa [φstar] using hm.symm))
  set gstar : L := φstar γ
  set Ψ_trunc : L[X] := C ystar + ∑ k ∈ Icc 1 (μ * d),
    C (φstar (recPoly S x₀ s k) / gstar ^ (2 * k - 1)) * X ^ k
  have hΨ_deg : Ψ_trunc.natDegree ≤ μ * d :=
    (natDegree_add_le _ _).trans <| max_le (by simp) <| (natDegree_sum_le _ _).trans <|
      Finset.sup_le fun k hk => natDegree_mul_le.trans (by
        rw [natDegree_C, zero_add, natDegree_X_pow]; exact (mem_Icc.1 hk).2)
  have hΨ_coeff0 : Ψ_trunc.coeff 0 = ystar := by
    rw [coeff_add, coeff_C_zero, coeff_sum_Icc_C_mul_X_pow, ite_eq_right (by omega), add_zero]
  have hΨ_coeff (k : ℕ) (hk1 : 1 ≤ k) : Ψ_trunc.coeff k =
      if k ≤ μ * d then φstar (recPoly S x₀ s k) / gstar ^ (2 * k - 1) else 0 := by
    rw [coeff_add, coeff_C, ite_eq_right (by omega), zero_add, coeff_sum_Icc_C_mul_X_pow]
    simp [hk1]
  have hμ_char_L : μ = 1 ∨ ∃ (p e : ℕ), CharP L p ∧ p.Prime ∧ μ = p ^ e := by
    rcases hμ_char with rfl | ⟨p, e, _, hp, rfl⟩
    · exact Or.inl rfl
    · have hFL_inj : Function.Injective (j_L.comp C) := hj_L_inj.comp Polynomial.C_injective
      exact Or.inr ⟨p, e, charP_of_injective_ringHom hFL_inj p, hp, rfl⟩
  obtain ⟨Ptilde, hPtilde_deg, hPtilde_pow⟩ := exists_pow_eq_poly_of_not_dvd hμ_pos hμ_char_L
    hΨ_deg fun k hndiv => by
      have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h0 => hndiv (h0 ▸ dvd_zero μ)
      rw [hΨ_coeff k hk1]
      split_ifs with hkle
      · rw [hφstar_dvd_zero (map_recPoly_dvd_of_kill hμ_char hS_deg hs_le_DY hW_tot_pos hS_wd
          hS_degZ hF_irred hF_prim hF_deg1 hF_deg_le hF_degZ hT''_card hT''_mem hk1
          (hkle.trans hμd_le) (Or.inr hndiv)), zero_div]
      · rfl
  set Pstar : L[X] := taylor (-j_L (C x₀)) Ptilde
  let Istar : Finset ι := Finset.univ.filter fun i =>
    Pstar.eval (j_L (C (α i))) = j_L (curveWord u i)
  refine ⟨Pstar, Istar, by rwa [natDegree_taylor], fun i hi => (mem_filter.1 hi).2,
    fun i hi_not => ?_⟩
  set Ei : F[X][X] := evalMismatchPoly S x₀ s μ d (α i) (curveWord u i)
  have hφstar_Ei_ne : φstar Ei ≠ 0 := by
    have hmap := map_evalMismatchPoly (α i) (curveWord u i) φstar hΨ_deg
      (by rw [hΨ_coeff0]; simp [φstar]) fun k hk => by
        rw [hΨ_coeff k (mem_Icc.1 hk).1, ite_eq_left (mem_Icc.1 hk).2]
        exact mul_div_cancel₀ _ (pow_ne_zero _ hφstar_γ)
    have hPstar_pow : Pstar ^ μ = taylor (-j_L (C x₀)) Ψ_trunc := by
      rw [← hPtilde_pow]; exact (map_pow (Polynomial.taylorAlgHom (-j_L (C x₀))) Ptilde μ).symm
    rw [show φstar (C (C (α i - x₀))) = j_L (C (α i)) - j_L (C x₀) by simp [φstar, map_sub],
      show φstar (C (curveWord u i)) = j_L (curveWord u i) by simp [φstar],
      show Ψ_trunc.eval (j_L (C (α i)) - j_L (C x₀)) = (Pstar.eval (j_L (C (α i)))) ^ μ by
        rw [← eval_pow, hPstar_pow, Polynomial.taylor_eval, sub_eq_add_neg]] at hmap
    rw [hmap]
    exact mul_ne_zero (pow_ne_zero _ hφstar_γ) fun h0 =>
      hi_not (mem_filter.2 ⟨mem_univ i, eq_of_pow_eq_of_char_pow hμ_char_L (sub_eq_zero.1 h0)⟩)
  have hcop : IsCoprime (Fstar.map ι_K) (Ei.map ι_K) :=
    ((hF_prim.irreducible_iff_irreducible_map_fraction_map (K := K)).1 hF_irred
      ).coprime_iff_not_dvd.2 fun hd => hφstar_Ei_ne (hφstar_dvd_zero hd)
  refine ⟨Polynomial.resultant Fstar Ei Fstar.natDegree Ei.natDegree,
    resultant_ne_zero_of_isCoprime_map ι_K hι_K_inj hcop,
    resultant_evalMismatch_natDegree_le α i hμ_pos hS_deg hDY_pos hD_pos
      (hdeg_mul.trans_le hR_deg_le) hμd_le hS_degZ hF_deg_le hF_degZ,
    fun z _ P hP_deg hS_ev0 hF_ev0 hγ_ev_ne hagree => ?_⟩
  let φz : F[X][X] →+* F := Polynomial.eval₂RingHom (evZ z) ((P ^ μ).eval x₀)
  have hφz_eq (f : F[X][X]) : φz f = (f.map (evZ z)).eval ((P ^ μ).eval x₀) := by
    simp [φz, Polynomial.eval_map]
  have hEi_z0 : (Ei.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 := by
    rw [← hφz_eq, map_evalMismatchPoly (α i) (curveWord u i) φz (W := taylor x₀ (P ^ μ))
      (by rw [natDegree_taylor]; exact natDegree_pow_le.trans (Nat.mul_le_mul_left μ hP_deg))
      (by rw [taylor_coeff_zero]; simp [φz]) fun k hk => by
        have hrec := spec_recPoly_at_point hS_deg hS_wd hS_ev0 hγ_ev_ne k (mem_Icc.1 hk).1
        rwa [← hφz_eq, ← hφz_eq] at hrec]
    rw [show φz (C (C (α i - x₀))) = α i - x₀ by simp [φz, evZ],
      show φz (C (curveWord u i)) = (curveWord u i).eval z by simp [φz, evZ],
      Polynomial.taylor_eval, sub_add_cancel, eval_pow, hagree, sub_self, mul_zero]
  exact eval_resultant_eq_zero_of_common_root (Or.inl (by omega)) hF_ev0 hEi_z0

end Step6ResultantKillAndLift

section Step7DoubleCountAndLagrange

variable {F : Type*} [Field F]

private theorem weighted_double_count_le {ι α : Type*} [Fintype ι]
    {W : ι → ℕ} {W_tot B_W bad : ℕ} (T : Finset α) (Istar : Finset ι)
    (agree : α → ι → Prop) [∀ z i, Decidable (agree z i)]
    (hW_sum : ∑ i, W i ≤ W_tot) (hT : W_tot * bad < #T)
    (hlo : ∀ z ∈ T, B_W ≤ ∑ i ∈ Finset.univ.filter (agree z), W i)
    (hbad : ∀ i ∉ Istar, #(T.filter fun z => agree z i) ≤ bad) :
    B_W ≤ ∑ i ∈ Istar, W i := by
  classical
  have hswap : ∑ z ∈ T, ∑ i ∈ Finset.univ.filter (agree z), W i =
      ∑ i : ι, #(T.filter fun z => agree z i) * W i := by
    calc _ = ∑ z ∈ T, ∑ i : ι, if agree z i then W i else 0 :=
            Finset.sum_congr rfl fun z _ => Finset.sum_filter _ _
      _ = ∑ i : ι, ∑ z ∈ T, if agree z i then W i else 0 := Finset.sum_comm
      _ = ∑ i : ι, #(T.filter fun z => agree z i) * W i := Finset.sum_congr rfl fun i _ => by
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have hlo' : #T * B_W ≤ ∑ i : ι, #(T.filter fun z => agree z i) * W i :=
    (by rw [Finset.sum_const, smul_eq_mul] : ∑ _z ∈ T, B_W = #T * B_W) ▸
      (Finset.sum_le_sum hlo).trans_eq hswap
  have hpart_in : ∑ i ∈ Istar, #(T.filter fun z => agree z i) * W i ≤ #T * ∑ i ∈ Istar, W i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (card_filter_le _ _)
  have hpart_out : ∑ i ∈ Finset.univ \ Istar, #(T.filter fun z => agree z i) * W i ≤
      W_tot * bad :=
    (Finset.sum_le_sum fun i hi =>
      Nat.mul_le_mul_right (W i) (hbad i (mem_sdiff.1 hi).2)).trans <| by
      rw [← Finset.mul_sum, mul_comm bad]
      exact Nat.mul_le_mul_right bad
        ((Finset.sum_le_sum_of_subset (subset_univ _)).trans hW_sum)
  have hsplit : ∑ i : ι, #(T.filter fun z => agree z i) * W i =
      (∑ i ∈ Finset.univ \ Istar, #(T.filter fun z => agree z i) * W i) +
        ∑ i ∈ Istar, #(T.filter fun z => agree z i) * W i :=
    (Finset.sum_sdiff (subset_univ Istar)).symm
  have hlt : #T * B_W < #T * ((∑ i ∈ Istar, W i) + 1) := by
    calc #T * B_W ≤ #T * ∑ i ∈ Istar, W i + W_tot * bad := by omega
      _ < #T * ∑ i ∈ Istar, W i + #T := Nat.add_lt_add_left hT _
      _ = #T * ((∑ i ∈ Istar, W i) + 1) := by ring
  exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_left hlt)

/-- Step 7: Weighted double-counting shows `B_W ≤ ∑ i ∈ Istar, W i`, giving `k ≤ #Istar`, and
Lagrange interpolation on a `k`-element subset `J ⊆ Istar` pulls `Pstar ∈ L[X]` down to `r + 1`
Reed–Solomon codewords `v : Fin (r + 1) → (ι → F)` agreeing with `u` on `Istar`. -/
private theorem exists_correlatedAgreement_of_lifted_poly {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k r d D B_Z D_Y M W_tot B_W μ : ℕ}
    (hk : 1 ≤ k) (hd : d = k - 1) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    {u : Fin (r + 1) → (ι → F)}
    {S : F[X][X][X]} {Fstar : F[X][X]} {x₀ : F} {T'' : Finset F}
    (hT''_card : W_tot * D_Y * (4 * D * B_Z + r * D_Y) < #T'')
    (hT''_mem : ∀ z ∈ T'',
      ∃ P : F[X], P.natDegree ≤ d ∧
        (evZ₂ z S).eval (P ^ μ) = 0 ∧
        (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 ∧
        ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
          ((P ^ μ).eval x₀) ≠ 0 ∧
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i)
    (Pstar : (AlgebraicClosure (FractionRing F[X]))[X])
    (Istar : Finset ι)
    (hPstar_deg : Pstar.natDegree ≤ d)
    (hIstar_agree : ∀ i ∈ Istar,
      Pstar.eval (((algebraMap (FractionRing F[X]) (AlgebraicClosure (FractionRing F[X]))).comp
        (algebraMap F[X] (FractionRing F[X]))) (C (α i))) =
      ((algebraMap (FractionRing F[X]) (AlgebraicClosure (FractionRing F[X]))).comp
        (algebraMap F[X] (FractionRing F[X]))) (curveWord u i))
    (hIstar_bad : ∀ i ∉ Istar, ∃ res : F[X], res ≠ 0 ∧
      res.natDegree ≤ 4 * D * D_Y * B_Z + r * D_Y ^ 2 ∧
      ∀ z ∈ T'', ∀ P : F[X], P.natDegree ≤ d →
        (evZ₂ z S).eval (P ^ μ) = 0 →
        (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 →
        ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
          ((P ^ μ).eval x₀) ≠ 0 →
        P.eval (α i) = (curveWord u i).eval z → res.eval z = 0) :
    ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v : Fin (r + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  classical
  let K := FractionRing F[X]; let L := AlgebraicClosure K
  let j_L : F[X] →+* L := (algebraMap K L).comp (algebraMap F[X] K)
  have hj_L_inj : Function.Injective j_L :=
    (RingHom.injective (algebraMap K L)).comp (IsFractionRing.injective F[X] K)
  choose P_of hP_deg hS_ev hF_ev hγ_ev hW_agree using fun z : T'' => hT''_mem z.1 z.2
  let agree : F → ι → Prop := fun z i =>
    (if hz : z ∈ T'' then P_of ⟨z, hz⟩ else 0).eval (α i) = (curveWord u i).eval z
  have hW_Istar : B_W ≤ ∑ i ∈ Istar, W i :=
    weighted_double_count_le T'' Istar agree hW_sum (by rwa [← mul_assoc])
      (fun z hz => by simpa only [agree, hz, ↓reduceDIte] using hW_agree ⟨z, hz⟩)
      fun i hi_not => by
        obtain ⟨res, hres_ne, hres_deg, hres_van⟩ := hIstar_bad i hi_not
        have hle := card_filter_eval_eq_zero_le hres_ne (T''.filter fun z => agree z i)
        rw [Finset.filter_true_of_mem fun z hz => by
          obtain ⟨hzT, hag⟩ := mem_filter.1 hz
          exact hres_van z hzT _ (hP_deg ⟨z, hzT⟩) (hS_ev ⟨z, hzT⟩) (hF_ev ⟨z, hzT⟩)
            (hγ_ev ⟨z, hzT⟩) (by simpa only [agree, hzT, ↓reduceDIte] using hag)] at hle
        exact hle.trans (hres_deg.trans_eq (by ring))
  obtain ⟨J, hJ_sub, hJ_card⟩ := Finset.exists_subset_card_eq
    (hk_le_t.trans (ceil_div_le_card_of_sum_le hM hW_le hW_Istar))
  let Pj : Fin (r + 1) → F[X] := fun j => Lagrange.interpolate J α (u j)
  let v : Fin (r + 1) → (ι → F) := fun j i => (Pj j).eval (α i)
  have hPj_deg (j) : (Pj j).degree < k := hJ_card ▸ Lagrange.degree_interpolate_lt _ hα.injOn
  let P_FZ : F[X][X] := ∑ j : Fin (r + 1), (Pj j).map C * C (X ^ (j : ℕ))
  let P_L : L[X] := P_FZ.map j_L
  have hP_L_eval (i : ι) : P_L.eval (j_L (C (α i))) = j_L (curveWord v i) := by
    have hFZ : P_FZ.eval (C (α i)) = curveWord v i := by
      rw [curveWord, Polynomial.ofFn_eq_sum_monomial]
      simp only [P_FZ, eval_finsetSum, eval_mul, eval_C, v]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hhom := (Polynomial.hom_eval₂ (Pj j) (RingHom.id F) Polynomial.C (α i)).symm
      rw [RingHom.comp_id, Polynomial.eval₂_id] at hhom
      rw [Polynomial.eval_map, hhom, Polynomial.C_mul_X_pow_eq_monomial]
    have hhom := (Polynomial.hom_eval₂ P_FZ (RingHom.id F[X]) j_L (C (α i))).symm
    rw [RingHom.comp_id, Polynomial.eval₂_id] at hhom
    rw [Polynomial.eval_map, hhom, hFZ]
  have hP_L_deg_lt : P_L.degree < k := Polynomial.degree_map_le.trans_lt <|
    (degree_sum_le _ _).trans_lt <| (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ =>
      (degree_mul_le _ _).trans_lt <|
        (add_le_add Polynomial.degree_map_le degree_C_le).trans_lt (by simpa using hPj_deg j)
  have hPstar_deg_lt : Pstar.degree < k := by
    rcases eq_or_ne Pstar 0 with rfl | h0
    · exact WithBot.bot_lt_coe k
    · rw [Polynomial.degree_eq_natDegree h0]; exact Nat.cast_lt.2 (by omega)
  have hPstar_eq : Pstar = P_L := sub_eq_zero.1 <| by_contra fun hne => by
    have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hne).2
      ((degree_sub_le _ _).trans_lt (max_lt hPstar_deg_lt hP_L_deg_lt))
    let f_pts : ι → L := fun i => j_L (C (α i))
    have hcard := card_filter_eval_eq_zero_le hne (J.image f_pts)
    have hvan : ∀ x ∈ J.image f_pts, (Pstar - P_L).eval x = 0 := fun x hx => by
      obtain ⟨i, hiJ, rfl⟩ := mem_image.1 hx
      have hcw : curveWord u i = curveWord v i := congrArg (Polynomial.ofFn (r + 1)) <|
        funext fun j => (Lagrange.eval_interpolate_at_node _ hα.injOn hiJ).symm
      rw [eval_sub, hIstar_agree i (hJ_sub hiJ), hP_L_eval i, hcw, sub_self]
    have hf_inj : Function.Injective f_pts := hj_L_inj.comp (Polynomial.C_injective.comp hα)
    rw [Finset.filter_true_of_mem hvan, card_image_of_injective J hf_inj, hJ_card] at hcard
    omega
  refine ⟨Istar, hW_Istar, v, fun j => mem_reedSolomon.2 ⟨Pj j, hPj_deg j, rfl⟩, fun i hi j => ?_⟩
  have hcw : curveWord v i = curveWord u i :=
    hj_L_inj (by rw [← hP_L_eval i, ← hPstar_eq, hIstar_agree i hi])
  simpa only [curveWord, Polynomial.ofFn_coeff_eq_val_of_lt _ j.2] using
    (congrArg (fun p : F[X] => p.coeff (j : ℕ)) hcw).symm

end Step7DoubleCountAndLagrange

section ParameterHelpers

private theorem card_monomials_zero (D : ℕ) : #(Sudan.monomials 0 D) = (D + 1) ^ 2 := by
  have heq : Sudan.monomials 0 D = range (D + 1) ×ˢ range (D + 1) := by
    ext ⟨a, b⟩
    simp only [Sudan.mem_monomials, mem_product, mem_range, Nat.lt_succ_iff, zero_mul, add_zero]
    tauto
  rw [heq, card_product, card_range, sq]

private theorem maxYDeg_zero_le (D : ℕ) : maxYDeg 0 D ≤ D := by
  refine Finset.sup_le fun ab hab => ?_
  exact (Sudan.mem_monomials.1 hab).2.1

private theorem mul_maxYDeg_le (d D : ℕ) : d * maxYDeg d D ≤ D := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hle : maxYDeg d D ≤ D / d := by
      refine Finset.sup_le fun ab hab => ?_
      obtain ⟨_, _, hwd⟩ := Sudan.mem_monomials.1 hab
      exact (Nat.le_div_iff_mul_le hd).2 (by linarith)
    exact (Nat.mul_le_mul_left d hle).trans (Nat.mul_div_le D d)

private theorem sqrt_rate_bounds {n k : ℕ} {ρ : ℝ} (hρ : ρ = (k : ℝ) / (n : ℝ))
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    0 < ρ ∧ ρ ≤ 1 ∧ 0 < Real.sqrt ρ ∧ Real.sqrt ρ ≤ 1 ∧ Real.sqrt ρ ^ 2 = ρ ∧
    (1 : ℝ) ≤ 1 / Real.sqrt ρ ∧ 1 / Real.sqrt ρ ≤ 1 / ρ ∧ 1 / Real.sqrt ρ ≤ (n : ℝ) := by
  subst hρ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hρ_pos : 0 < (k : ℝ) / n := by positivity
  have hρ_le_one : (k : ℝ) / n ≤ 1 := (div_le_one hnR).2 (by exact_mod_cast hkn)
  have hsq_pos : 0 < Real.sqrt ((k : ℝ) / n) := Real.sqrt_pos.2 hρ_pos
  have hsq_le : Real.sqrt ((k : ℝ) / n) ≤ 1 := Real.sqrt_le_one.2 hρ_le_one
  have hsq_sq : Real.sqrt ((k : ℝ) / n) ^ 2 = (k : ℝ) / n := Real.sq_sqrt hρ_pos.le
  refine ⟨hρ_pos, hρ_le_one, hsq_pos, hsq_le, hsq_sq, (one_le_div hsq_pos).2 hsq_le, ?_, ?_⟩
  · rw [div_le_div_iff₀ hsq_pos hρ_pos, one_mul, one_mul]
    calc (k : ℝ) / n = Real.sqrt ((k : ℝ) / n) * Real.sqrt ((k : ℝ) / n) := by rw [← sq, hsq_sq]
      _ ≤ Real.sqrt ((k : ℝ) / n) := mul_le_of_le_one_right hsq_pos.le hsq_le
  · refine le_of_sq_le_sq ?_ hnR.le
    rw [div_pow, one_pow, hsq_sq, one_div_div, div_le_iff₀ hkR, sq, mul_assoc]
    exact le_mul_of_one_le_right hnR.le
      (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hk.trans hkn) (by exact_mod_cast hk))

private theorem johnson_monomial_gap {n k m : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 1 ≤ m) :
    let m' := m + 1
    let t₀ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k)⌉₊
    let D := m' * t₀ - 1
    n * (m' * (m' + 1) / 2) < #(Sudan.monomials (k - 1) D) ∧
      (5 / 8) * (n : ℝ) < ((#(Sudan.monomials (k - 1) D) - n * (m' * (m' + 1) / 2) : ℕ) : ℝ) := by
  set m' := m + 1
  set t₀ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k)⌉₊
  set D := m' * t₀ - 1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm'R : (0 : ℝ) < m' := by positivity
  have h1_le_t₀ : 1 ≤ t₀ := by
    have hsq : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * k) :=
      (Real.le_sqrt (by norm_num) (by positivity)).2 <| (by norm_num : (1 : ℝ) ^ 2 ≤ 1).trans
        (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hk.trans hkn) (by exact_mod_cast hk))
    have hle : (1 : ℝ) ≤ (t₀ : ℝ) := hsq.trans (by
      calc Real.sqrt ((n : ℝ) * k) ≤ (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k) :=
            le_mul_of_one_le_left (Real.sqrt_nonneg _)
              (by linarith [show (0 : ℝ) ≤ 1 / (2 * m) by positivity])
        _ ≤ (t₀ : ℝ) := Nat.le_ceil _)
    exact_mod_cast hle
  have hD_succ : D + 1 = m' * t₀ := by
    have : 1 ≤ m' * t₀ := Nat.mul_pos (by omega) h1_le_t₀; omega
  have hmt_sq_lower :
      ((m' : ℝ) * (m' + 1) + 5 / 4) * ((n : ℝ) * k) < ((m' : ℝ) * t₀) ^ 2 := by
    have hmul : (m' : ℝ) * (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k) ≤
        (m' : ℝ) * t₀ := by
      have := mul_le_mul_of_nonneg_left (Nat.le_ceil _ : _ ≤ (t₀ : ℝ)) hm'R.le; linarith
    have hsq := pow_le_pow_left₀ (by positivity) hmul 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
    have hcoeff : (m' : ℝ) * (m' + 1) + 5 / 4 < ((m' : ℝ) * (1 + 1 / (2 * (m : ℝ)))) ^ 2 := by
      have hm'_cast : (m' : ℝ) = (m : ℝ) + 1 := by exact_mod_cast rfl
      rw [hm'_cast, mul_pow]
      have hdiff : ((m : ℝ) + 1) ^ 2 * (1 + 1 / (2 * m)) ^ 2 -
          (((m : ℝ) + 1) * (m + 1 + 1) + 5 / 4) = (6 * m + 1) / (4 * m ^ 2) := by
        field_simp; ring
      linarith [show (0 : ℝ) < (6 * m + 1) / (4 * m ^ 2) by positivity]
    exact (mul_lt_mul_of_pos_right hcoeff (by positivity)).trans_le hsq
  set R_eq := n * (m' * (m' + 1) / 2); set C_mon := #(Sudan.monomials (k - 1) D)
  have h2Req : 2 * (R_eq : ℝ) ≤ (n : ℝ) * ((m' : ℝ) * (m' + 1)) := by
    exact_mod_cast (by
      have := Nat.mul_le_mul_left n (Nat.div_mul_le_self (m' * (m' + 1)) 2)
      linarith [show 2 * R_eq = n * (m' * (m' + 1) / 2 * 2) by ring] :
        2 * R_eq ≤ n * (m' * (m' + 1)))
  have hgap : (R_eq : ℝ) + (5 / 8) * n < C_mon := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · have hC : (C_mon : ℝ) = ((m' : ℝ) * t₀) ^ 2 := by
        exact_mod_cast (by rw [show C_mon = #(Sudan.monomials 0 D) from rfl,
          card_monomials_zero, hD_succ] : C_mon = (m' * t₀) ^ 2)
      rw [hC]; simp only [Nat.cast_one, mul_one] at hmt_sq_lower; linarith
    · have hsq_lt : (m' * t₀) ^ 2 < 2 * (k - 1) * C_mon := calc
        (m' * t₀) ^ 2 = (D + 1) * (D + 1) := by rw [sq, hD_succ]
        _ < (D + 1) * (D + 2) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        _ ≤ 2 * (k - 1) * C_mon :=
          Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials (by omega) D
      have hdR_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
      have hd_le_k : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      have hstep : (2 * (R_eq : ℝ) + (5 / 4) * n) * ((k - 1 : ℕ) : ℝ) <
          (2 * (C_mon : ℝ)) * ((k - 1 : ℕ) : ℝ) := calc
        _ ≤ (((m' : ℝ) * (m' + 1) + 5 / 4) * n) * ((k - 1 : ℕ) : ℝ) := by gcongr; linarith
        _ ≤ (((m' : ℝ) * (m' + 1) + 5 / 4) * n) * k := by gcongr
        _ = ((m' : ℝ) * (m' + 1) + 5 / 4) * ((n : ℝ) * k) := by ring
        _ < ((m' : ℝ) * t₀) ^ 2 := hmt_sq_lower
        _ < 2 * ((k - 1 : ℕ) : ℝ) * C_mon := by exact_mod_cast hsq_lt
        _ = (2 * (C_mon : ℝ)) * ((k - 1 : ℕ) : ℝ) := by ring
      linarith [lt_of_mul_lt_mul_right hstep hdR_pos.le]
  have hinterp : R_eq < C_mon := by exact_mod_cast (show (R_eq : ℝ) < C_mon by linarith)
  exact ⟨hinterp, by rw [Nat.cast_sub hinterp.le]; linarith⟩

/-- Quantitative gap and degree bounds for `johnson_curve_params_bound`. -/
private theorem johnson_curve_params_gap {n k e m r : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 1 ≤ m)
    (he : (e : ℝ) / (n : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (n : ℝ)) -
        Real.sqrt ((k : ℝ) / (n : ℝ)) / (2 * (m : ℝ))) :
    let ρ := (k : ℝ) / (n : ℝ)
    let m' := m + 1
    let t₀ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * (k : ℝ))⌉₊
    let D := m' * t₀ - 1
    k ≤ n - e ∧
    n * (m' * (m' + 1) / 2) < #(Sudan.monomials (k - 1) D) ∧
    D < m' * (n - e) ∧
    (D : ℝ) ≤ (5 / 2) * (m' : ℝ) * (n : ℝ) * Real.sqrt ρ ∧
    (maxYDeg (k - 1) D : ℝ) ≤ 5 * (m' : ℝ) / Real.sqrt ρ ∧
    (siegelZDeg n m' (k - 1) D r : ℝ) ≤ 6 * (r : ℝ) * (m' : ℝ) ^ 3 / Real.sqrt ρ := by
  intro ρ m' t₀ D
  obtain ⟨hρ_pos, _, hsqρ_pos, _, hsqρ_sq, _⟩ :=
    sqrt_rate_bounds (rfl : ρ = (k : ℝ) / n) hk hkn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm'R : (0 : ℝ) < m' := by positivity
  have hsqnk_eq : Real.sqrt ((n : ℝ) * k) = (n : ℝ) * Real.sqrt ρ := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), mul_pow, hsqρ_sq]
    dsimp only [ρ]; field_simp
  have hmul_he : (e : ℝ) ≤ n - (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k) := by
    have h1 := (div_le_iff₀ hnR).1 he
    rw [hsqnk_eq]
    linarith [show (1 - Real.sqrt ρ - Real.sqrt ρ / (2 * m)) * n =
      n - (1 + 1 / (2 * m)) * (n * Real.sqrt ρ) by field_simp; ring]
  have he_le_n : e ≤ n := by
    have hlt : (e : ℝ) < n := by
      linarith [show (0 : ℝ) < (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k) by positivity]
    exact_mod_cast hlt.le
  have ht₀_le_sub : t₀ ≤ n - e :=
    Nat.ceil_le.2 (by rw [Nat.cast_sub he_le_n]; linarith)
  have hk_le_t₀ : k ≤ t₀ := by
    have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have h1 : (k : ℝ) ≤ Real.sqrt ((n : ℝ) * k) :=
      (Real.le_sqrt (by positivity) (by positivity)).2
        (by rw [sq]; exact mul_le_mul_of_nonneg_right hknR hkR.le)
    have h2 : Real.sqrt ((n : ℝ) * k) ≤
        (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k) :=
      le_mul_of_one_le_left (Real.sqrt_nonneg _)
        (by linarith [show (0 : ℝ) ≤ 1 / (2 * (m : ℝ)) by positivity])
    have h3 : (k : ℝ) ≤ (t₀ : ℝ) := (h1.trans h2).trans (Nat.le_ceil _)
    exact_mod_cast h3
  have hroot : D < m' * (n - e) := by
    have : 1 ≤ m' * t₀ := Nat.mul_pos (by omega) (hk.trans hk_le_t₀)
    have := Nat.mul_le_mul_left m' ht₀_le_sub; omega
  obtain ⟨hinterp, hdiff_lower⟩ := johnson_monomial_gap hk hkn hm
  have hD_upper : (D : ℝ) ≤ (5 / 2) * (m' : ℝ) * n * Real.sqrt ρ := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * k) :=
      (Real.le_sqrt (by norm_num) (by positivity)).2 <| (by norm_num : (1 : ℝ) ^ 2 ≤ 1).trans
        (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hk.trans hkn) (by exact_mod_cast hk))
    have hlt := Nat.ceil_lt_add_one (a := (1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * k))
      (by positivity)
    have hhalf : 1 + 1 / (2 * (m : ℝ)) ≤ 3 / 2 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have : 1 / (2 * (m : ℝ)) ≤ 1 / 2 :=
        (div_le_div_iff₀ (by positivity) (by norm_num)).2 (by linarith)
      linarith
    have ht_up : (t₀ : ℝ) ≤ (5 / 2) * Real.sqrt ((n : ℝ) * k) := by
      linarith [mul_le_mul_of_nonneg_right hhalf (Real.sqrt_nonneg ((n : ℝ) * k))]
    have hD_le : (D : ℝ) ≤ (m' : ℝ) * t₀ := by exact_mod_cast (show D ≤ m' * t₀ by omega)
    have := mul_le_mul_of_nonneg_left ht_up hm'R.le
    rw [hsqnk_eq] at this; linarith
  have hDY_upper : (maxYDeg (k - 1) D : ℝ) ≤ 5 * (m' : ℝ) / Real.sqrt ρ := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · have hle : (maxYDeg (1 - 1) D : ℝ) ≤ D := by exact_mod_cast maxYDeg_zero_le D
      have hρ1 : (n : ℝ) * Real.sqrt ρ = 1 / Real.sqrt ρ := by
        rw [eq_div_iff hsqρ_pos.ne', mul_assoc, ← sq, hsqρ_sq]
        dsimp only [ρ]; push_cast; field_simp
      have : (0 : ℝ) ≤ (m' : ℝ) / Real.sqrt ρ := by positivity
      have heq : (5 / 2) * (m' : ℝ) * n * Real.sqrt ρ = (5 / 2) * ((m' : ℝ) / Real.sqrt ρ) := by
        rw [mul_assoc ((5 / 2) * (m' : ℝ)), hρ1]; ring
      have heq2 : 5 * (m' : ℝ) / Real.sqrt ρ = 5 * ((m' : ℝ) / Real.sqrt ρ) := by ring
      linarith
    · have hmulR : ((k - 1 : ℕ) : ℝ) * (maxYDeg (k - 1) D : ℝ) ≤ D := by
        exact_mod_cast mul_maxYDeg_le (k - 1) D
      have hk_half : (k : ℝ) / 2 ≤ ((k - 1 : ℕ) : ℝ) := by
        have : (k : ℝ) ≤ 2 * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show k ≤ 2 * (k - 1) by omega)
        linarith
      have h1 : (k : ℝ) / 2 * (maxYDeg (k - 1) D : ℝ) ≤ (5 / 2) * m' * n * Real.sqrt ρ :=
        (mul_le_mul_of_nonneg_right hk_half (by positivity)).trans (hmulR.trans hD_upper)
      rw [le_div_iff₀ hsqρ_pos]
      have h2 := mul_le_mul_of_nonneg_right h1 hsqρ_pos.le
      have hsqeq : (5 / 2) * (m' : ℝ) * n * Real.sqrt ρ * Real.sqrt ρ = (5 / 2) * m' * k := by
        calc (5 / 2) * (m' : ℝ) * n * Real.sqrt ρ * Real.sqrt ρ
            = (5 / 2) * (m' : ℝ) * n * (Real.sqrt ρ ^ 2) := by ring
          _ = (5 / 2) * m' * k := by rw [hsqρ_sq]; dsimp only [ρ]; field_simp
      exact le_of_mul_le_mul_left (by linarith) hkR
  have hBZ_upper :
      (siegelZDeg n m' (k - 1) D r : ℝ) ≤ 6 * (r : ℝ) * (m' : ℝ) ^ 3 / Real.sqrt ρ := by
    set R_eq := n * (m' * (m' + 1) / 2); set C_mon := #(Sudan.monomials (k - 1) D)
    have hdiff_pos : (0 : ℝ) < ((C_mon - R_eq : ℕ) : ℝ) := by linarith
    have hdiv_le : (siegelZDeg n m' (k - 1) D r : ℝ) ≤
        (r : ℝ) * ((R_eq : ℝ) * (maxYDeg (k - 1) D : ℝ)) / ((C_mon - R_eq : ℕ) : ℝ) := by
      rw [le_div_iff₀ hdiff_pos]
      have hcast : ((siegelZDeg n m' (k - 1) D r * (C_mon - R_eq) : ℕ) : ℝ) ≤
          ((R_eq * r * maxYDeg (k - 1) D : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self (R_eq * r * maxYDeg (k - 1) D) (C_mon - R_eq)
      push_cast at hcast; linarith
    have hReq_up : (R_eq : ℝ) ≤ (3 / 4) * (n : ℝ) * (m' : ℝ) ^ 2 := by
      have h2Req : 2 * (R_eq : ℝ) ≤ (n : ℝ) * ((m' : ℝ) * (m' + 1)) := by
        exact_mod_cast (by
          have := Nat.mul_le_mul_left n (Nat.div_mul_le_self (m' * (m' + 1)) 2)
          linarith [show 2 * R_eq = n * (m' * (m' + 1) / 2 * 2) by ring] :
            2 * R_eq ≤ n * (m' * (m' + 1)))
      have hm2 : (2 : ℝ) ≤ m' := by exact_mod_cast (show 2 ≤ m' by omega)
      linarith [mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by linarith : (m' : ℝ) + 1 ≤ 3 / 2 * m') hm'R.le) hnR.le,
        show (n : ℝ) * ((m' : ℝ) * (3 / 2 * m')) = 2 * ((3 / 4) * n * m' ^ 2) by ring]
    have hfrac : (r : ℝ) * ((R_eq : ℝ) * (maxYDeg (k - 1) D : ℝ)) / ((C_mon - R_eq : ℕ) : ℝ) ≤
        (r : ℝ) * ((3 / 4 * n * (m' : ℝ) ^ 2) * (5 * m' / Real.sqrt ρ)) / (5 / 8 * n) :=
      div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left (mul_le_mul hReq_up hDY_upper (by positivity) (by positivity))
          (by positivity)) (by positivity) hdiff_lower.le
    exact hdiv_le.trans (hfrac.trans_eq (by field_simp; ring))
  exact ⟨hk_le_t₀.trans ht₀_le_sub, hinterp, hroot, hD_upper, hDY_upper, hBZ_upper⟩

end ParameterHelpers

public section

/-- Weight scaling for `johnsonCurveBound`: since `johnsonCurveBound` is affine in `W_tot` with
nonnegative coefficients, increasing the weight budget from `n` to `W_tot ≥ n` scales the bound by
at most `W_tot / n`. -/
theorem johnsonCurveBound_mul_le {n m d D r W_tot : ℕ} (hW : n ≤ W_tot) :
    johnsonCurveBound n m d D r W_tot * n ≤ johnsonCurveBound n m d D r n * W_tot := by
  dsimp only [johnsonCurveBound]
  have hA : (siegelZDeg n m d D r + 2 * maxYDeg d D * (D + siegelZDeg n m d D r)) * n ≤
      (siegelZDeg n m d D r + 2 * maxYDeg d D * (D + siegelZDeg n m d D r)) * W_tot :=
    Nat.mul_le_mul_left _ hW
  linarith

/-- Quantitative Guruswami–Sudan parameter packaging for degree-`r` curves (`1 ≤ r`): given
`1 ≤ k ≤ n`, `1 ≤ m`, and `(e : ℝ) / n ≤ 1 - √ρ - √ρ / (2 * m)` with `ρ = k / n`, the choice
`m' = m + 1`, `t₀ = ⌈(1 + 1 / (2 * m)) * √(n * k)⌉₊`, `D = m' * t₀ - 1` satisfies all hypotheses of
`Cslib.Code.exists_correlatedAgreement_curve_johnson` and yields
`(johnsonCurveBound n m' (k - 1) D r n : ℝ) ≤ 1800 * r * (m + 1) ^ 6 * n ^ 2 / ρ`. -/
theorem johnson_curve_params_bound {n k e m r : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (he : (e : ℝ) / (n : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (n : ℝ)) -
        Real.sqrt ((k : ℝ) / (n : ℝ)) / (2 * (m : ℝ))) :
    let m' := m + 1
    let t₀ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * (k : ℝ))⌉₊
    let D := m' * t₀ - 1
    k ≤ n - e ∧
    n * (m' * (m' + 1) / 2) < #(Sudan.monomials (k - 1) D) ∧
    D < m' * (n - e) ∧
    (johnsonCurveBound n m' (k - 1) D r n : ℝ) ≤
      1800 * (r : ℝ) * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) / ((k : ℝ) / (n : ℝ)) := by
  intro m' t₀ D
  obtain ⟨hk_le_sub, hinterp, hroot, hD_upper, hDY_upper, hBZ_upper⟩ :=
    johnson_curve_params_gap (r := r) hk hkn hm he
  set ρ := (k : ℝ) / n
  obtain ⟨hρ_pos, _, hsqρ_pos, _, hsqρ_sq, h1_le_invsq, hinvsq_le_invρ, hinvsq_le_n⟩ :=
    sqrt_rate_bounds (rfl : ρ = (k : ℝ) / n) hk hkn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have h1_le_n : (1 : ℝ) ≤ n := by exact_mod_cast hk.trans hkn
  have h1_le_r : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1_le_m' : (1 : ℝ) ≤ (m' : ℝ) := by exact_mod_cast (show 1 ≤ m' by omega)
  have h1_le_invρ : (1 : ℝ) ≤ 1 / ρ := h1_le_invsq.trans hinvsq_le_invρ
  have h1_le_n2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ h1_le_n
  have hn_le_n2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := le_self_pow₀ h1_le_n two_ne_zero
  have hm'p (a : ℕ) (ha : a ≤ 6) : (m' : ℝ) ^ a ≤ (m' : ℝ) ^ 6 := pow_le_pow_right₀ h1_le_m' ha
  set D_Y := maxYDeg (k - 1) D; set B_Z := siegelZDeg n m' (k - 1) D r
  set U := (m' : ℝ) ^ 6 * (n : ℝ) ^ 2 * (1 / ρ)
  have hm'2 := hm'p 2 (by norm_num); have hm'3 := hm'p 3 (by norm_num)
  have hm'4 := hm'p 4 (by norm_num)
  have ht1 : (B_Z : ℝ) ≤ 6 * r * U := calc
    _ ≤ 6 * r * ((m' : ℝ) ^ 3 * (1 * (1 / Real.sqrt ρ))) := by
        linarith [hBZ_upper, show 6 * (r : ℝ) * ((m' : ℝ) ^ 3 * (1 * (1 / Real.sqrt ρ))) =
          6 * r * (m' : ℝ) ^ 3 / Real.sqrt ρ by ring]
    _ ≤ 6 * r * ((m' : ℝ) ^ 6 * ((n : ℝ) ^ 2 * (1 / ρ))) := by gcongr
    _ = 6 * r * U := by ring
  have ht2 : 2 * (D_Y : ℝ) * D ≤ 25 * r * U := by
    have hprod := mul_le_mul hDY_upper hD_upper (by positivity) (by positivity)
    rw [show (5 * (m' : ℝ) / Real.sqrt ρ) * ((5 / 2) * m' * n * Real.sqrt ρ) =
      (25 / 2) * (m' : ℝ) ^ 2 * (n * 1) by field_simp; ring] at hprod
    have hmono : (m' : ℝ) ^ 2 * ((n : ℝ) * 1) ≤ (m' : ℝ) ^ 6 * ((n : ℝ) ^ 2 * (1 / ρ)) := by gcongr
    calc 2 * (D_Y : ℝ) * D ≤ 25 * 1 * U := by linarith
      _ ≤ 25 * (r : ℝ) * U := by gcongr
  have ht3 : 2 * (D_Y : ℝ) * B_Z ≤ 60 * r * U := by
    have hprod := mul_le_mul hDY_upper hBZ_upper (by positivity) (by positivity)
    rw [div_mul_div_comm, show Real.sqrt ρ * Real.sqrt ρ = ρ from by rw [← sq, hsqρ_sq]] at hprod
    have hmono : (m' : ℝ) ^ 4 * (1 * (1 / ρ)) ≤ (m' : ℝ) ^ 6 * ((n : ℝ) ^ 2 * (1 / ρ)) := by gcongr
    have hmono' : 60 * (r : ℝ) * ((m' : ℝ) ^ 4 * (1 * (1 / ρ))) ≤
        60 * (r : ℝ) * ((m' : ℝ) ^ 6 * ((n : ℝ) ^ 2 * (1 / ρ))) := by gcongr
    calc 2 * (D_Y : ℝ) * B_Z ≤ 60 * r * ((m' : ℝ) ^ 4 * (1 * (1 / ρ))) := by
          linarith [show 2 * ((5 * (m' : ℝ) * (6 * r * m' ^ 3)) / ρ) =
            60 * r * (m' ^ 4 * (1 * (1 / ρ))) by ring]
      _ ≤ 60 * r * U := hmono'.trans_eq (by dsimp only [U]; ring)
  have ht4 : 4 * (n : ℝ) * (D_Y : ℝ) ^ 2 * D * B_Z ≤ 1500 * r * U := by
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul (pow_le_pow_left₀ (by positivity) hDY_upper 2)
        (mul_le_mul hD_upper hBZ_upper (by positivity) (by positivity))
        (by positivity) (by positivity))
      (show (0 : ℝ) ≤ 4 * n by positivity)
    have hrhs : 4 * (n : ℝ) * ((5 * m' / Real.sqrt ρ) ^ 2 * (((5 / 2) * m' * n * Real.sqrt ρ) *
        (6 * r * m' ^ 3 / Real.sqrt ρ))) = 1500 * r * U := by
      dsimp only [U]; rw [div_pow, hsqρ_sq]; field_simp; ring
    linarith
  have ht5 : (n : ℝ) * (D_Y : ℝ) ^ 2 * ((r : ℝ) * D_Y) ≤ 125 * r * U := by
    have hDY3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hDY_upper 3) hnR.le
    rw [div_pow, show Real.sqrt ρ ^ 3 = ρ * Real.sqrt ρ by rw [pow_succ, hsqρ_sq]] at hDY3
    have hn_inv : (n : ℝ) * (1 / Real.sqrt ρ) ≤ (n : ℝ) ^ 2 :=
      (mul_le_mul_of_nonneg_left hinvsq_le_n hnR.le).trans_eq (sq _).symm
    have hbase : (n : ℝ) * (D_Y : ℝ) ^ 3 ≤ 125 * U := by
      have hmono : (m' : ℝ) ^ 3 * (n * (1 / Real.sqrt ρ)) * (1 / ρ) ≤
          (m' : ℝ) ^ 6 * (n : ℝ) ^ 2 * (1 / ρ) := by gcongr
      linarith [show (n : ℝ) * ((5 * m') ^ 3 / (ρ * Real.sqrt ρ)) =
        125 * ((m' : ℝ) ^ 3 * (n * (1 / Real.sqrt ρ)) * (1 / ρ)) by field_simp; ring]
    linarith [mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ r by positivity)]
  refine ⟨hk_le_sub, hinterp, hroot, ?_⟩
  have hcast : (johnsonCurveBound n m' (k - 1) D r n : ℝ) =
      (B_Z : ℝ) + 2 * D_Y * D + 2 * D_Y * B_Z + 4 * n * D_Y ^ 2 * D * B_Z +
        n * D_Y ^ 2 * (r * D_Y) := by
    simp only [johnsonCurveBound, D_Y, B_Z]; push_cast; ring
  rw [hcast, show 1800 * (r : ℝ) * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) / ((k : ℝ) / n) =
    1800 * r * U by dsimp only [U, m', ρ]; push_cast; ring]
  have : 0 ≤ (r : ℝ) * U := by positivity
  linarith only [ht1, ht2, ht3, ht4, ht5, this]

/-- Quantitative Guruswami–Sudan parameter packaging for affine lines (`r = 1`), specializing
`johnson_curve_params_bound`. -/
theorem johnson_line_params_bound {n k e m : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 1 ≤ m)
    (he : (e : ℝ) / (n : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (n : ℝ)) -
        Real.sqrt ((k : ℝ) / (n : ℝ)) / (2 * (m : ℝ))) :
    let m' := m + 1
    let t₀ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * (k : ℝ))⌉₊
    let D := m' * t₀ - 1
    k ≤ n - e ∧
    n * (m' * (m' + 1) / 2) < #(Sudan.monomials (k - 1) D) ∧
    D < m' * (n - e) ∧
    (johnsonCurveBound n m' (k - 1) D 1 n : ℝ) ≤
      1800 * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) / ((k : ℝ) / (n : ℝ)) := by
  simpa only [Nat.cast_one, mul_one] using
    johnson_curve_params_bound (r := 1) hk hkn hm le_rfl he

/-- Multiplicity selection for an arbitrary gap `η > 0` below the Johnson bound `1 - √ρ`: given
`1 ≤ k ≤ n`, `0 < η`, and `(e : ℝ) / n ≤ 1 - √(k / n) - η`, choosing
`m = ⌈√ρ / (2 * min η (√ρ / 2))⌉₊` yields `1 ≤ m`,
`(e : ℝ) / n ≤ 1 - √(k / n) - √(k / n) / (2 * m)`, and `(m + 1 : ℝ) ^ 6 ≤ 64 / η ^ 6`. -/
theorem exists_multiplicity_of_eta {n k e : ℕ} {η : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hη : 0 < η)
    (he : (e : ℝ) / (n : ℝ) ≤ 1 - Real.sqrt ((k : ℝ) / (n : ℝ)) - η) :
    ∃ m : ℕ, 1 ≤ m ∧
      (e : ℝ) / (n : ℝ) ≤
        1 - Real.sqrt ((k : ℝ) / (n : ℝ)) -
          Real.sqrt ((k : ℝ) / (n : ℝ)) / (2 * (m : ℝ)) ∧
      ((m + 1 : ℝ) ^ 6) ≤ 64 / (η ^ 6) := by
  set ρ := (k : ℝ) / n
  obtain ⟨_, _, hsqρ_pos, hsqρ_le_one, _⟩ := sqrt_rate_bounds (rfl : ρ = (k : ℝ) / n) hk hkn
  set η' := min η (Real.sqrt ρ / 2)
  have hη'_pos : 0 < η' := lt_min hη (by positivity)
  set m := ⌈Real.sqrt ρ / (2 * η')⌉₊
  have hx1 : (1 : ℝ) ≤ Real.sqrt ρ / (2 * η') :=
    (one_le_div (by positivity)).2 (by linarith [min_le_right η (Real.sqrt ρ / 2)])
  have hm : 1 ≤ m := by exact_mod_cast hx1.trans (Nat.le_ceil _)
  have hfrac : Real.sqrt ρ / (2 * m) ≤ η := by
    have hceil : Real.sqrt ρ / (2 * η') ≤ (m : ℝ) := Nat.le_ceil _
    have : Real.sqrt ρ / (2 * m) ≤ η' :=
      (div_le_iff₀ (by positivity)).2 (by linarith [(div_le_iff₀ (by positivity)).1 hceil])
    exact this.trans (min_le_left _ _)
  have hm1_le : (m : ℝ) + 1 ≤ 2 / η := by
    by_cases hle : η ≤ Real.sqrt ρ / 2
    · have hη'_eq : η' = η := min_eq_left hle
      have hlt : (m : ℝ) < Real.sqrt ρ / (2 * η) + 1 := by
        have h0 := Nat.ceil_lt_add_one (a := Real.sqrt ρ / (2 * η')) (by positivity)
        change (m : ℝ) < _ at h0; rwa [hη'_eq] at h0
      have hx1' : (1 : ℝ) ≤ Real.sqrt ρ / (2 * η) := by rwa [hη'_eq] at hx1
      have : 3 * (Real.sqrt ρ / (2 * η)) ≤ 2 / η := by
        rw [show 3 * (Real.sqrt ρ / (2 * η)) = (3 / 2 * Real.sqrt ρ) / η by ring]
        exact div_le_div_of_nonneg_right (by linarith) hη.le
      linarith
    · have hη'_eq : η' = Real.sqrt ρ / 2 := min_eq_right (le_of_not_ge hle)
      have hm1 : m = 1 := by
        dsimp only [m]; rw [hη'_eq, show Real.sqrt ρ / (2 * (Real.sqrt ρ / 2)) = 1 by field_simp]
        norm_num
      rw [hm1, Nat.cast_one, le_div_iff₀ hη]
      linarith [show (0 : ℝ) ≤ (e : ℝ) / n by positivity]
  refine ⟨m, hm, by linarith, (pow_le_pow_left₀ (by positivity) hm1_le 6).trans_eq ?_⟩
  rw [div_pow]; norm_num

/-- **Positive-characteristic-safe separable contraction in `F[Z][X][Y]`.**

Given an irreducible polynomial `R ∈ F[Z][X][Y]` of positive `Y`-degree over an arbitrary field `F`,
there exist a contraction exponent `μ ≥ 1` (either `μ = 1` or a prime power `μ = p ^ e` in
characteristic `p`), a polynomial `S ∈ F[Z][X][Y]` of positive `Y`-degree with `S(Z, X, Y ^ μ) = R`
and `μ * S.natDegree = R.natDegree`, and a Bézout identity `S * A + S' * B = C Δ` with `Δ ≠ 0`
witnessing separability of `S` over `FractionRing F[Z][X]`. -/
theorem exists_separable_contraction {F : Type*} [Field F] {R : F[X][X][X]}
    (hR_irred : Irreducible R) (hR_deg : 1 ≤ R.natDegree) :
    ∃ (μ : ℕ) (S A B : F[X][X][X]) (Δ : F[X][X]),
      (μ = 1 ∨ ∃ (p e : ℕ), CharP F p ∧ p.Prime ∧ μ = p ^ e) ∧
      1 ≤ μ ∧
      S.comp (X ^ μ) = R ∧
      1 ≤ S.natDegree ∧
      μ * S.natDegree = R.natDegree ∧
      Δ ≠ 0 ∧
      S * A + S.derivative * B = C Δ := by
  obtain ⟨μ, S, A, B, Δ, hμ_char, hμ_pos, hexp, hS_deg, hdeg_mul, _, _, _, hΔ_ne, hbez, _, _⟩ :=
    exists_separable_contraction_and_bezout (d := 0) (D := weightedDegree 0 R) (B_Z := degZ R)
      hR_irred hR_deg le_rfl le_rfl
  refine ⟨μ, S, A, B, Δ, hμ_char, hμ_pos, ?_, hS_deg, hdeg_mul, hΔ_ne, hbez⟩
  rw [← Polynomial.expand_eq_comp_X_pow]
  exact hexp

end

end Cslib.Code.ProximityGap

namespace Cslib.Code

open Cslib.Code.ProximityGap Finset Polynomial

section JohnsonHelpers

private theorem hammingDist_add_smul_le_of_eq_on {F ι : Type*} [Field F] [Fintype ι]
    [DecidableEq F] {u₀ u₁ v₀ v₁ : ι → F} {D' : Finset ι} {e : ℕ}
    (hD' : Fintype.card ι - e ≤ #D')
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i) (z : F) :
    hammingDist (u₀ + z • u₁) (v₀ + z • v₁) ≤ e := by
  have hsub : D' ⊆ Finset.univ.filter fun i => (u₀ + z • u₁) i = (v₀ + z • v₁) i := by
    intro i hi
    obtain ⟨h0, h1⟩ := hagree i hi
    exact mem_filter.2 ⟨mem_univ i, by simp only [Pi.add_apply, Pi.smul_apply, h0, h1]⟩
  have hcard := card_le_card hsub
  have htot := card_filter_eq_add_hammingDist (u₀ + z • u₁) (v₀ + z • v₁)
  omega

end JohnsonHelpers

public section

/-- **Explicit-parameter integer-weighted correlated-agreement step on degree-`r` curves**
(step toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 5.1, 6.2, and 7.2] in the accepted
*Journal of the ACM* 2023 manuscript; note that Theorem 7.2 of the July 2020 ePrint 2020/654
version concerns FRI soundness).

Let `α : ι → F` be distinct evaluation points over an arbitrary field `F` of any characteristic,
let `W : ι → ℕ` be integer coordinate weights with `∀ i, W i ≤ M` (`0 < M`) and
`∑ i, W i ≤ W_tot`, and let `m ≥ 1`, `D : ℕ` satisfy the explicit Guruswami–Sudan interpolation
and root-divisibility conditions for weight threshold `B_W` (with `k ≤ (B_W + M - 1) / M`). For
any `r + 1` words `u : Fin (r + 1) → (ι → F)` and finite set `T : Finset F` with
`johnsonCurveBound |ι| m (k - 1) D r W_tot < #T`, if for every `z ∈ T` the curve point
`∑ j, z ^ j • u j` has `W`-weighted agreement at least `B_W` with some codeword in
`reedSolomon α k`, then there exist a single shared coordinate subset `D' : Finset ι` with
`B_W ≤ ∑ i ∈ D', W i` and codewords `v : Fin (r + 1) → (ι → F)` in `reedSolomon α k` agreeing
with `u` on `D'`.

This theorem is parameterized directly by `(m, D, M, W_tot, B_W)` and integer weights `W : ι → ℕ`;
deriving the paper's displayed finite thresholds or normalized/rational-valued weight statements
is left open as separate work. -/
theorem exists_weighted_correlatedAgreement_curve_johnson {F ι : Type*} [Field F] [Fintype ι]
    [DecidableEq F] {α : ι → F} (hα : Function.Injective α)
    {k r m D M W_tot B_W : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * ((B_W + M - 1) / M))
    (u : Fin (r + 1) → (ι → F)) (T : Finset F)
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D r W_tot < #T)
    (hclose : ∀ z ∈ T, ∃ v ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter
        (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = v i), W i) :
    ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v : Fin (r + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  have hclose' : ∀ z ∈ T, ∃ v ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter
        (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) * u j i) = v i), W i := by
    intro z hz
    obtain ⟨v, hv_rs, hv_w⟩ := hclose z hz
    refine ⟨v, hv_rs, ?_⟩
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hv_w
  -- Step 2: Siegel interpolation + UFD factorization + pigeonhole onto irreducible `R`.
  obtain ⟨R, T_R, hR_irred, hR_deg, hR_deg_le, hR_wd, hR_degZ, hDY_pos, hD_pos, hW_tot_pos,
      _, hTR_card, hTR_mem⟩ :=
    exists_irreducible_factor_pigeonhole hα hk hm hM hW_le hW_sum hk_le_t hinterp hroot u hT hclose'
  -- Step 3: Positive-characteristic-safe separable contraction `R = expand μ S` + Bézout witness.
  obtain ⟨μ, S, A_bez, B_bez, Δ, hμ_char, hμ_pos, hexp_S, hS_deg, hdeg_mul, hμd_le, hS_wd,
      hS_degZ, hΔ_ne, hbez, hH_degX, hH_degZ⟩ :=
    exists_separable_contraction_and_bezout hR_irred hR_deg hR_wd hR_degZ
  -- Step 4: Good shift point `x₀` and primitive irreducible factor `Fstar` of `S(Z, x₀, Y)`.
  obtain ⟨x₀, Fstar, T'', _, _, hΔ_x₀_ne, hbez₀, hF_irred, hF_prim, hF_deg1, hF_deg_le,
      hF_degZ, hF_dvd, _, hT''_card, hT''_mem⟩ :=
    exists_good_shift_and_factor hμ_pos hexp_S hS_deg hdeg_mul hS_degZ hΔ_ne hbez hH_degX hH_degZ
      hTR_card hTR_mem
  have hT''_mem' : ∀ z ∈ T'',
      ∃ P : F[X], P.natDegree ≤ k - 1 ∧
        (evZ₂ z S).eval (P ^ μ) = 0 ∧
        (Fstar.map (evZ z)).eval ((P ^ μ).eval x₀) = 0 ∧
        ((S.map (Polynomial.evalRingHom (C x₀))).derivative.map (evZ z)).eval
          ((P ^ μ).eval x₀) ≠ 0 ∧
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => P.eval (α i) = (curveWord u i).eval z), W i := by
    intro z hz
    obtain ⟨_, _, hP⟩ := hT''_mem z hz
    exact hP
  -- Steps 5–6: Recurrence, resultant kill, lift to `L`, and Frobenius `μ`-th root `Pstar`.
  obtain ⟨Pstar, Istar, hPstar_deg, hIstar_agree, hIstar_bad⟩ :=
    exists_lifted_poly_and_mismatch_bound hμ_char hμ_pos hS_deg hdeg_mul hR_deg_le hDY_pos hD_pos
      hW_tot_pos hμd_le hS_wd hS_degZ hΔ_x₀_ne hbez₀ hF_irred hF_prim hF_deg1 hF_deg_le hF_degZ
      hF_dvd hT''_card hT''_mem'
  -- Step 7: Weighted double-counting and Lagrange interpolation endgame.
  exact exists_correlatedAgreement_of_lifted_poly hα hk rfl hM hW_le hW_sum hk_le_t
    hT''_card hT''_mem' Pstar Istar hPstar_deg hIstar_agree hIstar_bad

/-- **Explicit-parameter unweighted correlated-agreement step on degree-`r` curves**
(step toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.2], accepted JACM 2023 manuscript).

Unweighted specialization of `Cslib.Code.exists_weighted_correlatedAgreement_curve_johnson` over
an arbitrary field `F` of any characteristic, parameterized explicitly by `(m, D)` and
`Cslib.Code.ProximityGap.johnsonCurveBound`. -/
theorem exists_correlatedAgreement_curve_johnson {F ι : Type*} [Field F] [Fintype ι]
    [DecidableEq F] {α : ι → F} (hα : Function.Injective α)
    {k r e m D : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hk_le : k ≤ Fintype.card ι - e)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * (Fintype.card ι - e))
    (u : Fin (r + 1) → (ι → F)) (T : Finset F)
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D r (Fintype.card ι) < #T)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ #D' ∧
      ∃ v : Fin (r + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  have hceil : (Fintype.card ι - e + 1 - 1) / 1 = Fintype.card ι - e := by omega
  have hclose_w : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      Fintype.card ι - e ≤ ∑ _i ∈ Finset.univ.filter
        (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), (1 : ℕ) := by
    intro z hz
    obtain ⟨c, hc_rs, hdist⟩ := hclose z hz
    refine ⟨c, hc_rs, ?_⟩
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    have htot := card_filter_eq_add_hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c
    omega
  obtain ⟨D', hD', v, hv_rs, hagree⟩ :=
    exists_weighted_correlatedAgreement_curve_johnson (W := fun _ => 1) (M := 1)
      (W_tot := Fintype.card ι) (B_W := Fintype.card ι - e) hα hk hm Nat.one_pos
      (fun _ => le_rfl) (by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one])
      (by rwa [hceil]) hinterp (by rwa [hceil]) u T hT hclose_w
  rw [Finset.sum_const, smul_eq_mul, mul_one] at hD'
  exact ⟨D', hD', v, hv_rs, hagree⟩

/-- **Explicit-parameter integer-weighted correlated-agreement step on affine lines**
(step toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 7.2] in the accepted JACM 2023
manuscript; Theorem 7.2 of the July 2020 ePrint 2020/654 version concerns FRI soundness).

Line (`r = 1`) specialization of `Cslib.Code.exists_weighted_correlatedAgreement_curve_johnson` over
an arbitrary field `F` of any characteristic, with explicit `(m, D)` and integer weights
`W : ι → ℕ` (normalized/rational-valued weights are outside this theorem's scope). -/
theorem exists_weighted_correlatedAgreement_line_johnson {F ι : Type*} [Field F] [Fintype ι]
    [DecidableEq F] {α : ι → F} (hα : Function.Injective α)
    {k m D M W_tot B_W : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * ((B_W + M - 1) / M))
    (u₀ u₁ : ι → F) (T : Finset F)
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot < #T)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), W i) :
    ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v₁ ∈ reedSolomon α k,
        ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  obtain ⟨D', hD', v, hv_rs, hagree⟩ :=
    exists_weighted_correlatedAgreement_curve_johnson (r := 1) hα hk hm hM hW_le hW_sum hk_le_t
      hinterp hroot ![u₀, u₁] T hT fun z hz => by
        simpa only [show (∑ j : Fin 2, z ^ (j : ℕ) • ![u₀, u₁] j) = u₀ + z • u₁ by
          simp [Fin.sum_univ_two]] using hclose z hz
  exact ⟨D', hD', v 0, hv_rs 0, v 1, hv_rs 1, fun i hi => ⟨hagree i hi 0, hagree i hi 1⟩⟩

/-- **Explicit-parameter unweighted correlated-agreement step on affine lines**
(step toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 5.1], accepted JACM 2023 manuscript).

Line (`r = 1`), unweighted specialization of
`Cslib.Code.exists_correlatedAgreement_curve_johnson` over an arbitrary field `F` of any
characteristic, parameterized explicitly by `(m, D)` and
`Cslib.Code.ProximityGap.johnsonCurveBound`. -/
theorem exists_correlatedAgreement_line_johnson {F ι : Type*} [Field F] [Fintype ι]
    [DecidableEq F] {α : ι → F} (hα : Function.Injective α)
    {k e m D : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hk_le : k ≤ Fintype.card ι - e)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * (Fintype.card ι - e))
    (u₀ u₁ : ι → F) (T : Finset F)
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 (Fintype.card ι) < #T)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ #D' ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v₁ ∈ reedSolomon α k,
        ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  obtain ⟨D', hD', v, hv_rs, hagree⟩ :=
    exists_correlatedAgreement_curve_johnson (r := 1) hα hk hm hk_le hinterp hroot ![u₀, u₁] T hT
      fun z hz => by
        simpa only [show (∑ j : Fin 2, z ^ (j : ℕ) • ![u₀, u₁] j) = u₀ + z • u₁ by
          simp [Fin.sum_univ_two]] using hclose z hz
  exact ⟨D', hD', v 0, hv_rs 0, v 1, hv_rs 1, fun i hi => ⟨hagree i hi 0, hagree i hi 1⟩⟩

/-- **Proximity gap for affine lines up to the Johnson bound (explicit-constant variant)**
(original quantitative variant of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.4], accepted
JACM 2023 manuscript).

Let `α : ι → F` be distinct evaluation points over a finite field `F` with `n = |ι|` and code rate
`ρ = k / n` (`1 ≤ k ≤ n`), and let `m ≥ 1` be the multiplicity parameter. For any proximity radius
`e : ℕ` with `(e : ℝ) / n ≤ 1 - √ρ - √ρ / (2 * m)` and any two words `u₀, u₁ : ι → F`, either
every point `u₀ + z • u₁` on the affine line lies within Hamming distance `e` of
`reedSolomon α k`, or the fraction of scalars `z : F` that do is at most
`1800 * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`.

Compared to the displayed finite-threshold bound `(m + 1 / 2) ^ 7 / (3 * ρ ^ (3 / 2)) * n ^ 2 / |F|`
of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 5.1, p. 17] (accepted NSF/JACM manuscript;
Theorem 1.4 instead references Theorem 1.2's `η`-dependent expression), this variant has smaller
asymptotic exponents in `m` and `1 / ρ` (`(m + 1) ^ 6 / ρ`) but is **not** uniformly smaller at
small finite `m` (for example, at `m = 3` and `ρ = 1 / 4`, the coefficients are `29,491,200`
versus approximately `17,157`). Thus it does not imply the paper's displayed finite constant for
all finite `m`; matching that exact finite constant remains open. -/
theorem proximityGap_line_johnson {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k m : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hm : 1 ≤ m)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ u₁ : ι → F)
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e] :
    (∀ z : F, ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e) ∨
      ((#(Finset.univ.filter fun z : F =>
          ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e) : ℝ) /
        (Fintype.card F : ℝ)) ≤
        1800 * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  set S : Finset F :=
    Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e
  obtain ⟨hk_sub, hinterp, hroot, hjb⟩ := johnson_line_params_bound hk hkn hm he
  set m' : ℕ := m + 1
  set t₀ : ℕ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((Fintype.card ι : ℝ) * (k : ℝ))⌉₊
  set D : ℕ := m' * t₀ - 1
  by_cases hgt :
      ProximityGap.johnsonCurveBound (Fintype.card ι) m' (k - 1) D 1 (Fintype.card ι) < #S
  · left
    obtain ⟨D', hD', v₀, hv₀, v₁, hv₁, hagree⟩ :=
      exists_correlatedAgreement_line_johnson hα hk (by omega : 1 ≤ m') hk_sub hinterp hroot
        u₀ u₁ S hgt (fun z hz => (mem_filter.1 hz).2)
    intro z
    exact ⟨v₀ + z • v₁, Submodule.add_mem _ hv₀ (Submodule.smul_mem _ z hv₁),
      hammingDist_add_smul_le_of_eq_on hD' hagree z⟩
  · right
    have hcard_le : (#S : ℝ) ≤
        (ProximityGap.johnsonCurveBound (Fintype.card ι) m' (k - 1) D 1 (Fintype.card ι) : ℝ) := by
      exact_mod_cast le_of_not_gt hgt
    have hFpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := F)
    have hdiv := div_le_div_of_nonneg_right (hcard_le.trans hjb) hFpos.le
    rw [div_div] at hdiv
    exact hdiv

/-- **Proximity gap for affine lines up to `1 - √ρ - η` (explicit-constant variant)**
(original `η`-parameterized corollary of `Cslib.Code.proximityGap_line_johnson` in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.4], accepted JACM 2023 manuscript).

For any positive gap `η > 0` below the Johnson bound `1 - √ρ`, either every point on the affine
line lies within Hamming distance `e` of `reedSolomon α k`, or the exceptional fraction is at most
`115200 * n ^ 2 / (ρ * η ^ 6 * |F|)`. -/
theorem proximityGap_line_johnson_of_eta {F ι : Type*} [Field F] [Fintype F] [Fintype ι]
    [DecidableEq F] {α : ι → F} {e k : ℕ} {η : ℝ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hη : 0 < η)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    (u₀ u₁ : ι → F)
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e] :
    (∀ z : F, ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e) ∨
      ((#(Finset.univ.filter fun z : F =>
          ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e) : ℝ) /
        (Fintype.card F : ℝ)) ≤
        115200 * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) := by
  obtain ⟨m, hm, he', hpow⟩ := exists_multiplicity_of_eta hk hkn hη he
  rcases proximityGap_line_johnson hα hk hkn hm he' u₀ u₁ with hall | hbound
  · exact Or.inl hall
  · right
    set n : ℕ := Fintype.card ι
    set ρ : ℝ := (k : ℝ) / (n : ℝ)
    have hn : 1 ≤ n := hk.trans hkn
    have hρ_pos : 0 < ρ := by positivity
    have hFpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := F)
    have hstep :
        1800 * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) / (ρ * (Fintype.card F : ℝ)) ≤
          1800 * (64 / (η ^ 6)) * ((n : ℝ) ^ 2) / (ρ * (Fintype.card F : ℝ)) := by
      gcongr
    have hsimp :
        1800 * (64 / (η ^ 6)) * ((n : ℝ) ^ 2) / (ρ * (Fintype.card F : ℝ)) =
          115200 * ((n : ℝ) ^ 2) / (ρ * (η ^ 6) * (Fintype.card F : ℝ)) := by
      field_simp
      ring
    exact hbound.trans (hstep.trans_eq hsimp)

end

end Cslib.Code
