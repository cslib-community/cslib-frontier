/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ReedSolomon
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Cramer
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap
import CslibFrontier.Foundations.Data.Code.BerlekampWelch
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Proximity gaps for Reed–Solomon codes in the unique-decoding regime

This module proves correlated agreement and proximity gaps for Reed–Solomon codes in the
unique-decoding regime `2 * e + k ≤ |ι|` over arbitrary fields, following Ben-Sasson, Carmon,
Ishai, Kopparty, and Saraf [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 4.1 (affine lines),
Theorem 6.1 (parameterized curves), and Theorem 1.2 (the finite-field proximity-gap dichotomy).

## Mathematical overview

Let `α : ι → F` be distinct evaluation points with `n = |ι|` and let `e, k : ℕ` satisfy
`2 * e + k ≤ n`. Given `d + 1` words `u : Fin (d + 1) → (ι → F)` and a finite set `S : Finset F`
of size strictly greater than `d * n` such that every curve point `∑ j, z ^ (j : ℕ) • u j`
(`z ∈ S`) lies within Hamming distance `e` of `reedSolomon α k`, there exists a single shared
coordinate subset `D' : Finset ι` of size at least `n - e` together with codewords
`v : Fin (d + 1) → (ι → F)` in `reedSolomon α k` such that `u j i = v j i` for all `i ∈ D'` and
all `j` (`Cslib.Code.exists_correlatedAgreement_curve_unique`). Specializing `d = 1` yields
correlated agreement on affine lines `u₀ + z • u₁` above the exact threshold `n < #S`
(`Cslib.Code.exists_correlatedAgreement_unique`).

The proof follows the bivariate Berlekamp–Welch interpolation strategy of
[BenSassonCarmonIshaiKoppartySaraf2020, Section 4]:
1. Form the `n × (2 * e + k + 1)` Berlekamp–Welch linear system over `F[Z]` whose first `k + e`
   columns have `Z`-degree `0` and whose last `e + 1` columns have `Z`-degree at most `d`.
2. Show the system has nontrivial kernel over `FractionRing F[Z]` (using
   `Cslib.Code.BerlekampWelch.exists_isSolution` at every `z ∈ S` to annihilate any square full
   minor of `Z`-degree at most `d * (e + 1) < #S`) and extract a nonzero polynomial kernel vector
   `(A, B) ∈ F[Z][X] × F[Z][X]` via `Matrix.cramer` on a maximal independent column subset, giving
   `deg_X A < k + e`, `deg_X B ≤ e`, `deg_Z A ≤ d * (e + 1)`, and `deg_Z B ≤ d * e`.
3. Divide out the `F[Z]`-content of `B` (using Lagrange interpolation on `k + e` points to show it
   also divides `A`), obtaining primitive `B` so that `B(X, z) ≠ 0` for every `z : F`.
4. Factor out `g = gcd A B` in the GCD domain `F[Z][X]` to obtain relatively prime `A₀, B₀`, and
   apply a padded Sylvester resultant multiplicity bound symmetrically in both `X` and `Z` (via
   `Polynomial.Bivariate.swap`). The two resultant degree bounds force `deg_Z B₀ ≤ d * deg_X B₀`
   and `deg_X B₀ * #S ≤ d * n * deg_X B₀`, forcing `B₀` to be a nonzero scalar in `F`.
5. Thus `B ∣ A` in `F[Z][X]`, and the quotient `P = A / B` has `X`-degree `< k` and agrees with
   `∑ j, u j i * Z ^ j` on `D' = {i | B(α i, Z) ≠ 0}` of size at least `n - e`.

## Main results

* `Cslib.Code.hammingDist_curve_le_of_eq_on`: shared agreement of `d + 1` words on a subset of
  size at least `|ι| - e` implies Hamming distance at most `e` at every point on the curve.
* `Cslib.Code.hammingDist_add_smul_le_of_eq_on`: line specialization of
  `Cslib.Code.hammingDist_curve_le_of_eq_on`.
* `Cslib.Code.exists_correlatedAgreement_curve_unique`: correlated agreement on parameterized
  curves of degree `d` in the unique-decoding regime when `d * |ι| < #S`
  ([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.1]).
* `Cslib.Code.exists_correlatedAgreement_unique`: correlated agreement on affine lines
  `u₀ + z • u₁` in the unique-decoding regime when `|ι| < #S`
  ([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1]).
* `Cslib.Code.exists_uniqueMaximal_correlatedAgreement_of_exists`: generic uniqueness step in the
  unique-decoding regime: given an existing correlated-agreement witness for any indexed word
  family, upgrades it to the unique maximal shared agreement set and unique codewords.
* `Cslib.Code.exists_uniqueMaximal_correlatedAgreement_curve_unique`: unique maximal agreement set
  and unique codewords on degree-`d` parameterized curves in the unique-decoding regime
  ([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.5 & Theorem 6.1]).
* `Cslib.Code.exists_uniqueMaximal_correlatedAgreement_unique`: unique maximal agreement set and
  unique codewords on affine lines in the unique-decoding regime
  ([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.4, Theorem 4.1 & Remark 4.1]).
* `Cslib.Code.proximityGap_curve_unique`: finite-field proximity-gap dichotomy for parameterized
  curves in the unique-decoding regime.
* `Cslib.Code.proximityGap_unique`: finite-field proximity-gap dichotomy for affine lines in the
  unique-decoding regime ([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.2]).

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf,
  *Proximity Gaps for Reed–Solomon Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
-/

public section

namespace Cslib.Code

open Finset Polynomial
open scoped Polynomial.Bivariate

variable {F ι : Type*} [Field F]

/-! ### Private algebraic helpers: degree bounds, Gauss coprimality, and Sylvester resultants -/

section Helpers

private lemma natDegree_det_le_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ F[X]) (d : κ → ℕ) (hM : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.natDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun σ _ => ?_⟩
  rw [Function.comp_apply, Units.smul_def, zsmul_eq_mul]
  refine natDegree_mul_le.trans ?_
  have hunit : ((Equiv.Perm.sign σ : ℤ) : F[X]).natDegree = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hunit, zero_add]
  exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => hM (σ i) i)

private lemma card_filter_eval_ne_zero_ge {R : Type*} [CommRing R] [IsDomain R]
    [Fintype ι] [DecidableEq R] {β : ι → R} (hβ : Function.Injective β)
    {p : R[X]} (hp : p ≠ 0) :
    Fintype.card ι - p.natDegree ≤ (Finset.univ.filter fun i => p.eval (β i) ≠ 0).card := by
  have hcompl : (Finset.univ.filter fun i => p.eval (β i) = 0).card ≤ p.natDegree := by
    rw [← card_image_of_injective _ hβ]
    refine card_le_degree_of_subset_roots fun y hy => ?_
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
    exact (mem_roots hp).2 (mem_filter.1 hi).2
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
    (fun i => p.eval (β i) = 0)
  rw [card_univ] at htot
  change _ + (Finset.univ.filter fun i => p.eval (β i) ≠ 0).card = Fintype.card ι at htot
  omega

private noncomputable def curveCoordPoly [DecidableEq F] {d : ℕ} (u : Fin (d + 1) → (ι → F))
    (i : ι) : F[X] :=
  ofFn (d + 1) fun j => u j i

private lemma eval_curveCoordPoly [DecidableEq F] {d : ℕ} (u : Fin (d + 1) → (ι → F)) (i : ι)
    (z : F) :
    (curveCoordPoly u i).eval z = (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i := by
  simp only [curveCoordPoly, ofFn_eq_sum_monomial, eval_finsetSum, eval_monomial,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private lemma natDegree_curveCoordPoly_le [DecidableEq F] {d : ℕ} (u : Fin (d + 1) → (ι → F))
    (i : ι) : (curveCoordPoly u i).natDegree ≤ d :=
  Nat.lt_succ_iff.1 (ofFn_natDegree_lt (Nat.succ_pos d) _)

private lemma coeff_curveCoordPoly [DecidableEq F] {d : ℕ} (u : Fin (d + 1) → (ι → F)) (i : ι)
    (j : Fin (d + 1)) : (curveCoordPoly u i).coeff (j : ℕ) = u j i :=
  ofFn_coeff_eq_val_of_lt _ j.isLt

private lemma natDegree_swap_mul {p q : F[X][Y]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (Bivariate.swap (p * q)).natDegree =
      (Bivariate.swap p).natDegree + (Bivariate.swap q).natDegree := by
  rw [map_mul, natDegree_mul ((map_ne_zero_iff Bivariate.swap Bivariate.swap.injective).2 hp)
    ((map_ne_zero_iff Bivariate.swap Bivariate.swap.injective).2 hq)]

private lemma degree_coeff_swap_lt {p : F[X][Y]} {k : ℕ} (hp : p.degree < k) (d : ℕ) :
    ((Bivariate.swap p).coeff d).degree < k := by
  rw [degree_lt_iff_coeff_zero]
  intro t ht
  rw [Bivariate.coeff_coeff_swap,
    coeff_eq_zero_of_degree_lt (hp.trans_le (Nat.cast_le.2 ht)), coeff_zero]

private lemma isCoprime_map_fractionRing_of_isRelPrime {f g : F[X][Y]} (hfg : IsRelPrime f g) :
    IsCoprime (f.map (algebraMap F[X] (FractionRing F[X])))
      (g.map (algebraMap F[X] (FractionRing F[X]))) := by
  classical
  let K := FractionRing F[X]
  let i : F[X] →+* K := algebraMap F[X] K
  set d : K[X] := EuclideanDomain.gcd (f.map i) (g.map i)
  have hd_left : d ∣ f.map i := EuclideanDomain.gcd_dvd_left _ _
  have hd_right : d ∣ g.map i := EuclideanDomain.gcd_dvd_right _ _
  have hd_unit : IsUnit d := by
    by_cases hd0 : d = 0
    · have h0 : ∀ {p : F[X][Y]}, d ∣ p.map i → p = 0 := fun hp =>
        map_injective i (IsFractionRing.injective F[X] K) <| by
          simpa only [Polynomial.map_zero] using zero_dvd_iff.1 (hd0 ▸ hp)
      exact absurd (hfg (by rw [h0 hd_left]) (by rw [h0 hd_right])) not_isUnit_zero
    · let d₁ : F[X][Y] := IsLocalization.integerNormalization (nonZeroDivisors F[X]) d
      obtain ⟨c, hc0, hc⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors F[X]) d
      have hc_ne : i c ≠ 0 :=
        ((injective_iff_map_eq_zero i).1 (IsFractionRing.injective F[X] K) c).mt
          (nonZeroDivisors.ne_zero hc0)
      have hd_dvd : d₁.primPart.map i ∣ d := ⟨C ((i c)⁻¹ * i d₁.content), by
        have hmap : C (i c) * d = C (i d₁.content) * d₁.primPart.map i := by
          have h1 : d₁.map i = C (i c) * d := by
            simpa only [Algebra.smul_def, algebraMap_apply] using hc
          rw [← h1]; conv_lhs => rw [d₁.eq_C_content_mul_primPart]
          rw [Polynomial.map_mul, Polynomial.map_C]
        calc d = C (i c)⁻¹ * (C (i c) * d) := by
              rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc_ne, C_1, one_mul]
          _ = d₁.primPart.map i * C ((i c)⁻¹ * i d₁.content) := by
              rw [hmap, C_mul]; ring⟩
      exact isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart hd0
        (hfg (d₁.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hd_dvd.trans hd_left))
          (d₁.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hd_dvd.trans hd_right)))
  obtain ⟨u, hu⟩ := hd_unit
  refine ⟨↑u⁻¹ * EuclideanDomain.gcdA (f.map i) (g.map i),
    ↑u⁻¹ * EuclideanDomain.gcdB (f.map i) (g.map i), ?_⟩
  have hbez := EuclideanDomain.gcd_eq_gcd_ab (f.map i) (g.map i)
  calc _ = (↑u⁻¹ : K[X]) * (f.map i * EuclideanDomain.gcdA (f.map i) (g.map i) +
            g.map i * EuclideanDomain.gcdB (f.map i) (g.map i)) := by ring
    _ = ↑u⁻¹ * (u : K[X]) := by rw [← hbez, hu]
    _ = 1 := Units.inv_mul u

private lemma resultant_ne_zero_of_isRelPrime {f g : F[X][Y]} {M : ℕ}
    (hfg : IsRelPrime f g) (hg0 : g ≠ 0) (hfM : f.natDegree ≤ M) :
    Polynomial.resultant f g M g.natDegree ≠ 0 := by
  let i : F[X] →+* FractionRing F[X] := algebraMap F[X] _
  have hinj : Function.Injective i := IsFractionRing.injective F[X] _
  have hbase : Polynomial.resultant f g f.natDegree g.natDegree ≠ 0 := fun h0 => by
    have h1 := congrArg i h0
    rw [map_zero, ← Polynomial.resultant_map_map,
      ← natDegree_map_eq_of_injective hinj f, ← natDegree_map_eq_of_injective hinj g] at h1
    exact Polynomial.resultant_ne_zero _ _ (isCoprime_map_fractionRing_of_isRelPrime hfg) h1
  rw [← Nat.add_sub_of_le hfM, Polynomial.resultant_add_left_deg _ _ _ _ _ le_rfl]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    (pow_ne_zero _ (leadingCoeff_ne_zero.2 hg0))) hbase

private lemma C_X_sub_C_dvd_of_map_evalRingHom_eq_zero {H : F[X][Y]} {w : F}
    (hH : H.map (evalRingHom w) = 0) : C (X - C w) ∣ H := by
  rw [C_dvd_iff_dvd_coeff]
  intro t
  rw [dvd_iff_isRoot, IsRoot.def]
  simpa only [coeff_map, coeff_zero, coe_evalRingHom] using congrArg (fun p : F[X] => p.coeff t) hH

private lemma X_sub_C_pow_dvd_resultant_of_map_eq_mul {f g : F[X][Y]} {M : ℕ} {w : F} {p : F[X]}
    (hpM : p.natDegree + g.natDegree ≤ M)
    (hmap : f.map (evalRingHom w) = g.map (evalRingHom w) * p) :
    (X - C w) ^ g.natDegree ∣ Polynomial.resultant f g M g.natDegree := by
  let pC : F[X][Y] := p.map C
  have hneg_deg : (-pC).natDegree + g.natDegree ≤ M := by
    rw [natDegree_neg]; exact (Nat.add_le_add_right natDegree_map_le _).trans hpM
  let H : F[X][Y] := f + g * (-pC)
  have hH_map : H.map (evalRingHom w) = 0 := by
    have hcomp : (evalRingHom w).comp C = RingHom.id F := by
      ext x; simp only [RingHom.comp_apply, coe_evalRingHom, eval_C, RingHom.id_apply]
    have hpC_map : pC.map (evalRingHom w) = p := by
      rw [Polynomial.map_map, hcomp, Polynomial.map_id]
    simp only [H, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_neg, hpC_map, hmap,
      mul_neg, add_neg_cancel]
  obtain ⟨H', hH'⟩ := C_X_sub_C_dvd_of_map_evalRingHom_eq_zero hH_map
  refine ⟨Polynomial.resultant H' g M g.natDegree, ?_⟩
  calc Polynomial.resultant f g M g.natDegree
      = Polynomial.resultant H g M g.natDegree :=
        (Polynomial.resultant_add_mul_left f g (-pC) M g.natDegree hneg_deg le_rfl).symm
    _ = Polynomial.resultant (C (X - C w) * H') g M g.natDegree := by rw [hH']
    _ = (X - C w) ^ g.natDegree * Polynomial.resultant H' g M g.natDegree :=
        Polynomial.resultant_C_mul_left H' g M g.natDegree (X - C w)

private lemma natDegree_resultant_le {f g : F[X][Y]} {M n a_T b_T : ℕ}
    (hf : ∀ t, (f.coeff t).natDegree ≤ a_T) (hg : ∀ t, (g.coeff t).natDegree ≤ b_T) :
    (Polynomial.resultant f g M n).natDegree ≤ M * b_T + n * a_T := by
  classical
  let d : Fin (M + n) → ℕ := Fin.addCases (fun _ => b_T) (fun _ => a_T)
  refine (natDegree_det_le_sum (f.sylvester g M n) d fun i j => ?_).trans_eq ?_
  · induction j using Fin.addCases with
    | left j =>
      simp only [d, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs <;> [exact hg _; exact Nat.zero_le _]
    | right j =>
      simp only [d, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs <;> [exact hf _; exact Nat.zero_le _]
  · simp [d, Fin.sum_univ_add]

private lemma card_mul_natDegree_le_of_isRelPrime_resultant {f g : F[X][Y]} {M a_T b_T : ℕ}
    {W : Finset F} (hfg : IsRelPrime f g) (hg0 : g ≠ 0) (hfM : f.natDegree ≤ M)
    (hfT : ∀ t, (f.coeff t).natDegree ≤ a_T) (hgT : ∀ t, (g.coeff t).natDegree ≤ b_T)
    (hW : ∀ w ∈ W, ∃ p : F[X], p.natDegree + g.natDegree ≤ M ∧
      f.map (evalRingHom w) = g.map (evalRingHom w) * p) :
    g.natDegree * W.card ≤ g.natDegree * a_T + M * b_T := by
  let R : F[X] := Polynomial.resultant f g M g.natDegree
  have hprod_dvd : (∏ w ∈ W, (X - C w) ^ g.natDegree) ∣ R :=
    Finset.prod_dvd_of_coprime
      (fun _ _ _ _ hne => (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hne).isUnit).pow)
      fun w hw => let ⟨_, hpM, hmap⟩ := hW w hw; X_sub_C_pow_dvd_resultant_of_map_eq_mul hpM hmap
  have hprod_deg : (∏ w ∈ W, (X - C w) ^ g.natDegree).natDegree = g.natDegree * W.card := by
    rw [natDegree_prod_of_monic _ _ fun w _ => (monic_X_sub_C w).pow _]
    simp only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, one_mul,
      Finset.sum_const, smul_eq_mul, mul_comm]
  have hle1 : g.natDegree * W.card ≤ R.natDegree :=
    hprod_deg ▸ natDegree_le_of_dvd hprod_dvd (resultant_ne_zero_of_isRelPrime hfg hg0 hfM)
  have hle2 : R.natDegree ≤ M * b_T + g.natDegree * a_T := natDegree_resultant_le hfT hgT
  omega

/-! ### Linear algebra helper: invertible submatrix and Cramer kernel extraction -/

private lemma exists_det_ne_zero_submatrix_of_linearIndependent_cols {κ ι' : Type*}
    [Fintype κ] [DecidableEq κ] [Finite ι']
    {K : Type*} [Field K] (A : Matrix ι' κ K)
    (hli : LinearIndependent K fun j : κ => fun i : ι' => A i j) :
    ∃ ρ : κ → ι', (A.submatrix ρ id).det ≠ 0 := by
  classical
  have hdecomp : ∀ x : κ → K, x = ∑ j : κ, x j • Pi.single j (1 : K) := fun x => by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have hspan : Submodule.span K (Set.range fun i : ι' => A i) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ_ne, hφ_le⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let v : κ → K := fun j => φ (Pi.single j 1)
    have hv_zero : ∑ j : κ, v j • (fun i : ι' => A i j) = 0 := by
      ext i
      have h0 : φ (A i) = 0 := hφ_le (Submodule.subset_span ⟨i, rfl⟩)
      conv_lhs at h0 => rw [hdecomp (A i)]
      simp only [map_sum, map_smul, smul_eq_mul] at h0
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm, v] using h0
    have hv : v = 0 := funext (Fintype.linearIndependent_iff.1 hli v hv_zero)
    refine hφ_ne (LinearMap.ext fun x => ?_)
    conv_lhs => rw [hdecomp x]
    simp [map_sum, map_smul, show ∀ j, φ (Pi.single j 1) = 0 from congrFun hv]
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range fun i : ι' => A i)
  rw [hspan] at hs_span
  let _ : Fintype s := ((Set.finite_range fun i : ι' => A i).subset hs_sub).fintype
  let b : Module.Basis s K (κ → K) :=
    Module.Basis.mk hs_li (by rw [Subtype.range_coe_subtype]; exact le_of_eq hs_span.symm)
  let e : κ ≃ s := Fintype.equivOfCardEq <| by
    simpa [Module.finrank_pi] using (Module.finrank_eq_card_basis b)
  choose ρ hρ using fun j : κ => hs_sub (e j).2
  have hrows : LinearIndependent K (A.submatrix ρ id).row := by
    convert hs_li.comp e e.injective using 1; ext j c; exact congrFun (hρ j) c
  exact ⟨ρ, isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.linearIndependent_row_iff_isUnit.1 hrows))⟩

private lemma natDegree_cramer_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    {C : Finset κ} {j₀ : κ} (hj₀ : j₀ ∉ C) (N : Matrix C C F[X]) (v : C → F[X])
    (colDeg : κ → ℕ) (hN : ∀ a b : C, (N a b).natDegree ≤ colDeg b.1)
    (hv : ∀ a : C, (v a).natDegree ≤ colDeg j₀) (c : C) :
    (N.cramer v c).natDegree ≤ ∑ t ∈ Finset.univ.erase c.1, colDeg t := by
  rw [Matrix.cramer_apply]
  let d' : C → ℕ := fun b => if b = c then colDeg j₀ else colDeg b.1
  have hM' : ∀ a b : C, ((N.updateCol c v) a b).natDegree ≤ d' b := fun a b => by
    by_cases hbc : b = c
    · simp only [d', hbc, ↓reduceIte, Matrix.updateCol_self]; exact hv a
    · simp only [d', hbc, ↓reduceIte, Matrix.updateCol_ne hbc]; exact hN a b
  refine (natDegree_det_le_sum (N.updateCol c v) d' hM').trans ?_
  rw [← Finset.add_sum_erase _ _ (mem_univ c)]
  have h1 : d' c = colDeg j₀ := by simp only [d', ↓reduceIte]
  have hrest : ∑ b ∈ Finset.univ.erase c, d' b = ∑ t ∈ C.erase c.1, colDeg t := by
    calc ∑ b ∈ Finset.univ.erase c, d' b
        = ∑ b ∈ Finset.univ.erase c, colDeg b.1 :=
          Finset.sum_congr rfl fun b hb => by simp only [d', (mem_erase.1 hb).1, ↓reduceIte]
      _ = ∑ t ∈ C.erase c.1, colDeg t :=
          Finset.sum_bij (fun b _ => b.1)
            (fun b hb => mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 (Subtype.ext h), b.2⟩)
            (fun _ _ _ _ h => Subtype.ext h)
            (fun t ht => ⟨⟨t, (mem_erase.1 ht).2⟩, mem_erase.2
              ⟨fun h => (mem_erase.1 ht).1 (congrArg Subtype.val h), mem_univ _⟩, rfl⟩)
            (fun _ _ => rfl)
  rw [h1, hrest, ← Finset.sum_insert (fun h => hj₀ (mem_erase.1 h).2)]
  exact Finset.sum_le_sum_of_subset fun t ht => by
    rcases mem_insert.1 ht with rfl | ht'
    · exact mem_erase.2 ⟨fun h => hj₀ (h ▸ c.2), mem_univ _⟩
    · exact mem_erase.2 ⟨(mem_erase.1 ht').1, mem_univ _⟩

private lemma exists_max_indep_cols {κ ι' : Type*} [Finite κ]
    {K : Type*} [Field K]
    (MK : Matrix ι' κ K) (hdep : ¬ LinearIndependent K fun j : κ => fun r : ι' => MK r j) :
    ∃ (C : Finset κ) (j₀ : κ) (w : C → K),
      LinearIndependent K (fun c : C => fun r : ι' => MK r c.1) ∧
      j₀ ∉ C ∧ ∑ c : C, w c • (fun r : ι' => MK r c.1) = fun r : ι' => MK r j₀ := by
  classical
  let _ : Fintype κ := Fintype.ofFinite κ
  let indepSets : Finset (Finset κ) :=
    Finset.univ.filter fun C => LinearIndependent K fun c : C => fun r : ι' => MK r c.1
  obtain ⟨C, hC_mem, hC_max⟩ := Finset.exists_max_image indepSets Finset.card
    ⟨∅, mem_filter.2 ⟨mem_univ _, linearIndependent_empty_type⟩⟩
  have hC_li : LinearIndependent K fun c : C => fun r : ι' => MK r c.1 := (mem_filter.1 hC_mem).2
  have ⟨j₀, hj₀⟩ : ∃ j₀ : κ, j₀ ∉ C := by
    by_contra hall; push Not at hall
    have huniv : C = Finset.univ := Finset.eq_univ_iff_forall.2 hall
    exact hdep (hC_li.comp (fun j : κ => (⟨j, huniv.symm ▸ mem_univ j⟩ : C))
      fun _ _ h => congrArg Subtype.val h)
  have hspan : (fun r : ι' => MK r j₀) ∈
      Submodule.span K (Set.range fun c : C => fun r : ι' => MK r c.1) := by
    by_contra hnot
    have hnot' : (fun r => MK r j₀) ∉ Submodule.span K ((fun j r => MK r j) '' (C : Set κ)) := by
      rwa [Set.image_eq_range]
    have hC_on : LinearIndepOn K (fun j r => MK r j) (C : Set κ) := hC_li
    have hli' : LinearIndependent K fun c : (insert j₀ C : Finset κ) => fun r : ι' => MK r c.1 := by
      have h := hC_on.insert hnot'
      rwa [← Finset.coe_insert] at h
    have hle := hC_max (insert j₀ C) (mem_filter.2 ⟨mem_univ _, hli'⟩)
    rw [card_insert_of_notMem hj₀] at hle; omega
  rw [Submodule.mem_span_range_iff_exists_fun] at hspan
  obtain ⟨w, hw⟩ := hspan
  exact ⟨C, j₀, w, hC_li, hj₀, hw⟩

/-- Extract a nonzero vector in the kernel of a matrix over `F[X]` with linearly dependent columns
over `FractionRing F[X]`, bounding each entry's degree by the sum of all *other* column degrees. -/
private lemma exists_cramer_kernel_vec {κ ι' : Type*} [Fintype κ] [DecidableEq κ] [Finite ι']
    (M : Matrix ι' κ F[X]) (colDeg : κ → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ colDeg j)
    (hdep : ¬ LinearIndependent (FractionRing F[X])
      fun j => fun i => algebraMap F[X] (FractionRing F[X]) (M i j)) :
    ∃ x : κ → F[X], x ≠ 0 ∧ M.mulVec x = 0 ∧
      ∀ j, (x j).natDegree ≤ ∑ c ∈ Finset.univ.erase j, colDeg c := by
  let K := FractionRing F[X]
  let iK : F[X] →+* K := algebraMap F[X] K
  let MK : Matrix ι' κ K := M.map iK
  obtain ⟨C, j₀, w, hC_li, hj₀, hw⟩ := exists_max_indep_cols MK (fun h => hdep h)
  obtain ⟨ρ, hρ_det⟩ := exists_det_ne_zero_submatrix_of_linearIndependent_cols
    (MK.submatrix id (fun c : C => c.1)) hC_li
  let N : Matrix C C F[X] := M.submatrix ρ (·.1)
  have hNK_eq : N.map iK = (MK.submatrix id (fun c : C => c.1)).submatrix ρ id := by ext a b; rfl
  have hNK_det : (N.map iK).det ≠ 0 := by rw [hNK_eq]; exact hρ_det
  have hN_det : N.det ≠ 0 := fun h0 => hNK_det <| by
    rw [show (N.map iK).det = iK N.det from (RingHom.map_det iK N).symm, h0, map_zero]
  let v : C → F[X] := fun c => M (ρ c) j₀
  let x : κ → F[X] := fun j =>
    if j = j₀ then N.det else if hj : j ∈ C then -(N.cramer v ⟨j, hj⟩) else 0
  have hNw : (N.map iK).mulVec w = fun c => iK (v c) := funext fun c => by
    have hrc := congrFun hw (ρ c)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hrc
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, N, Matrix.submatrix_apply, v]
    exact (Finset.sum_congr rfl fun b _ => mul_comm _ _).trans hrc
  have hcramer_eq (c : C) : iK (N.cramer v c) = iK N.det * w c :=
    congrFun (Matrix.map_cramer_eq_det_smul iK hNw) c
  have hMx : M.mulVec x = 0 := funext fun r => IsFractionRing.injective F[X] K <| by
    rw [Pi.zero_apply, map_zero]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [← Finset.add_sum_erase _ _ (mem_univ j₀),
      show x j₀ = N.det by simp only [x, ↓reduceIte]]
    have hsub : C ⊆ Finset.univ.erase j₀ :=
      fun c hc => mem_erase.2 ⟨fun h => hj₀ (h ▸ hc), mem_univ c⟩
    rw [← Finset.sum_subset hsub fun j hj hjC => by
      simp only [x, (mem_erase.1 hj).1, ↓reduceIte, hjC, ↓reduceDIte, map_zero, mul_zero],
      ← Finset.sum_attach C]
    have hsum : ∑ c ∈ C.attach, iK (M r c.1) * iK (x c.1) =
        -(iK N.det * ∑ c : C, w c * MK r c.1) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hne : c.1 ≠ j₀ := fun h => hj₀ (h ▸ c.2)
      simp only [x, hne, ↓reduceIte, c.2, ↓reduceDIte, map_neg, hcramer_eq c, MK, Matrix.map_apply]
      rw [mul_neg, neg_inj, mul_comm (iK (M r c.1)), mul_assoc, mul_comm (w c)]
    have hrw := congrFun hw r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hrw
    change iK (M r j₀) * iK N.det + ∑ c ∈ C.attach, iK (M r c.1) * iK (x c.1) = 0
    rw [hsum, hrw]
    change iK (M r j₀) * iK N.det + -(iK N.det * iK (M r j₀)) = 0
    rw [mul_comm (iK (M r j₀)), add_neg_cancel]
  refine ⟨x, fun hx0 => hN_det (by simpa only [x, ↓reduceIte, Pi.zero_apply] using congrFun hx0 j₀),
    hMx, fun j => ?_⟩
  by_cases hj : j = j₀
  · subst hj; simp only [x, ↓reduceIte]
    exact ((natDegree_det_le_sum N (fun c => colDeg c.1) fun a b => hM (ρ a) b.1).trans_eq
      (Finset.sum_attach C colDeg)).trans (Finset.sum_le_sum_of_subset
        fun c hc => mem_erase.2 ⟨fun h => hj₀ (h ▸ hc), mem_univ c⟩)
  · by_cases hm : j ∈ C
    · simp only [x, hj, ↓reduceIte, hm, ↓reduceDIte, natDegree_neg]
      exact natDegree_cramer_le hj₀ N v colDeg (fun a b => hM (ρ a) b.1) (fun a => hM (ρ a) j₀)
        ⟨j, hm⟩
    · simp only [x, hj, ↓reduceIte, hm, ↓reduceDIte, natDegree_zero, Nat.zero_le]

/-! ### Stage 1: primitive bivariate Berlekamp–Welch interpolant -/

private lemma berlekampWelch_cols_not_linearIndependent [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k d : ℕ}
    (u : Fin (d + 1) → (ι → F)) (S : Finset F) (hde_lt_S : d * (e + 1) < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c ≤ e)
    (hk1 : 1 ≤ k) :
    let Col := Fin (k + e) ⊕ Fin (e + 1)
    let M : Matrix ι Col F[X] := fun i => Sum.elim
      (fun t => C (α i ^ (t : ℕ)))
      (fun t => -(curveCoordPoly u i * C (α i ^ (t : ℕ))))
    ¬ LinearIndependent (FractionRing F[X])
      fun j => fun i => algebraMap F[X] (FractionRing F[X]) (M i j) := by
  intro Col M hli
  let iK := algebraMap F[X] (FractionRing F[X])
  obtain ⟨ρ, hρ_det⟩ := exists_det_ne_zero_submatrix_of_linearIndependent_cols (M.map iK) hli
  let N : Matrix Col Col F[X] := M.submatrix ρ id
  have hN_det : N.det ≠ 0 := by
    intro h0; apply hρ_det
    have heq : (M.map iK).submatrix ρ id = N.map iK := by ext a b; rfl
    have hmap : (N.map iK).det = iK N.det := (RingHom.map_det iK N).symm
    rw [heq, hmap, h0, map_zero]
  have hN_deg : N.det.natDegree ≤ d * (e + 1) := by
    let colDeg : Col → ℕ := Sum.elim (fun _ => 0) (fun _ => d)
    refine (natDegree_det_le_sum N colDeg fun a b => ?_).trans_eq ?_
    · cases b with
      | inl t => exact (natDegree_C _).le
      | inr t =>
        change (-(curveCoordPoly u (ρ a) * C (α (ρ a) ^ (t : ℕ)))).natDegree ≤ d
        rw [natDegree_neg]
        exact natDegree_mul_le.trans (by
          rw [natDegree_C, add_zero]; exact natDegree_curveCoordPoly_le u (ρ a))
    · rw [Fintype.sum_sum_type]
      simp [colDeg, mul_comm]
  have hN_eval_zero : ∀ z ∈ S, N.det.eval z = 0 := fun z hz => by
    obtain ⟨c, hcRS, hdist⟩ := hclose z hz
    obtain ⟨p, hp_deg, rfl⟩ := mem_reedSolomon.1 hcRS
    rw [hammingDist_comm] at hdist
    obtain ⟨E, Q, hsol⟩ := BerlekampWelch.exists_isSolution (α := α)
      (w := ∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) hp_deg hdist
    let y : Col → F := Sum.elim (fun t => Q.coeff t.1) (fun t => E.coeff t.1)
    have hy_ne : y ≠ 0 := fun hy0 => by
      have h1 := congrFun hy0 (Sum.inr ⟨e, Nat.lt_succ_self e⟩)
      simp only [y, Sum.elim_inr, Pi.zero_apply] at h1
      rw [← hsol.natDegree_eq, ← leadingCoeff, hsol.monic.leadingCoeff] at h1
      exact one_ne_zero h1
    have hNy : (N.map (evalRingHom z)).mulVec y = 0 := funext fun a => by
      rw [Pi.zero_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      have hdegQ : Q.natDegree < k + e := by
        by_cases hQ0 : Q = 0
        · rw [hQ0, natDegree_zero]; omega
        · exact (natDegree_lt_iff_degree_lt hQ0).2 (add_comm e k ▸ hsol.degree_lt)
      have hQsum : ∑ t : Fin (k + e), (N.map (evalRingHom z)) a (.inl t) * y (.inl t) =
          Q.eval (α (ρ a)) := by
        rw [eval_eq_sum_range' hdegQ, ← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_congr rfl fun t _ => by
          change eval z (C (α (ρ a) ^ (t : ℕ))) * Q.coeff (t : ℕ) = _
          rw [eval_C, mul_comm]
      have hEsum : ∑ t : Fin (e + 1), (N.map (evalRingHom z)) a (.inr t) * y (.inr t) =
          -((∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) (ρ a) * E.eval (α (ρ a))) := by
        have hdegE : E.natDegree < e + 1 := by rw [hsol.natDegree_eq]; exact Nat.lt_succ_self e
        rw [eval_eq_sum_range' hdegE, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum,
          ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun t _ => by
          change eval z (-(curveCoordPoly u (ρ a) * C (α (ρ a) ^ (t : ℕ)))) * E.coeff (t : ℕ) = _
          rw [eval_neg, eval_mul, eval_C, eval_curveCoordPoly]; ring
      rw [hQsum, hEsum, hsol.eval_eq (ρ a), add_neg_cancel]
    have hdet0 : (N.map (evalRingHom z)).det = 0 := by
      by_contra hnz
      obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hnz)
      have h1 := congrArg (↑U⁻¹ : Matrix Col Col F).mulVec hNy
      rw [Matrix.mulVec_mulVec, ← hU, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
      exact hy_ne h1
    simpa only [coe_evalRingHom] using (RingHom.map_det (evalRingHom z) N).trans hdet0
  exact hN_det (eq_zero_of_degree_lt_of_eval_finset_eq_zero S
    (by rw [degree_eq_natDegree hN_det, Nat.cast_lt]; exact hN_deg.trans_lt hde_lt_S) hN_eval_zero)

private lemma exists_div_C_of_dvd_eval {α : ι → F} (hα : Function.Injective α)
    {J : Finset ι} (hJ_ne : 0 < J.card) {Araw : F[X][Y]} {h : F[X]}
    (hdeg : Araw.degree < (J.card : ℕ)) (hdvd : ∀ i ∈ J, h ∣ Araw.eval (C (α i))) :
    ∃ A : F[X][Y], A.degree < (J.card : ℕ) ∧ Araw = C h * A := by
  classical
  let qJ : ι → F[X] := fun i => if hi : i ∈ J then (hdvd i hi).choose else 0
  let A : F[X][Y] := ∑ j ∈ J, C (qJ j) * (Lagrange.basis J α j).map C
  have hA_deg : A.degree < (J.card : ℕ) := by
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro j hj
    refine (degree_mul_le _ _).trans_lt ?_
    refine (add_le_add degree_C_le degree_map_le).trans_lt ?_
    rw [zero_add, Lagrange.degree_basis hα.injOn hj]
    exact Nat.cast_lt.2 (by omega)
  refine ⟨A, hA_deg, sub_eq_zero.1 (eq_zero_of_degree_lt_of_eval_finset_eq_zero
    (J.image fun i => C (α i)) ?_ ?_)⟩
  · have hinjC : Function.Injective (fun i : ι => (C (α i) : F[X])) := C_injective.comp hα
    rw [card_image_of_injective _ hinjC]
    exact (degree_sub_le _ _).trans_lt (max_lt hdeg ((degree_mul_le _ _).trans_lt
      ((add_le_add degree_C_le le_rfl).trans_lt (by rwa [zero_add]))))
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
    have hAeval : A.eval (C (α i)) = qJ i := by
      simp only [A, eval_finsetSum, eval_mul, eval_C, eval_map_apply]
      rw [Finset.sum_eq_single i
        (fun j _ hji => by rw [Lagrange.eval_basis_of_ne hji hi, C_0, mul_zero])
        (fun hni => absurd hi hni), Lagrange.eval_basis_self hα.injOn hi, C_1, mul_one]
    have hq := (hdvd i hi).choose_spec
    simp only [eval_sub, eval_mul, eval_C, hAeval, qJ, hi, ↓reduceDIte, ← hq, sub_self]

private lemma exists_primitive_bivariate_solution [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k d : ℕ} (hα : Function.Injective α)
    (he : 2 * e + k ≤ Fintype.card ι) (hd : 1 ≤ d) (he1 : 1 ≤ e) (hk1 : 1 ≤ k)
    (u : Fin (d + 1) → (ι → F)) (S : Finset F) (hS : d * Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c ≤ e) :
    ∃ A B : F[X][Y], B.IsPrimitive ∧ A.degree < (k + e : ℕ) ∧ B.natDegree ≤ e ∧
      (Bivariate.swap A).natDegree ≤ d * (e + 1) ∧
      (Bivariate.swap B).natDegree ≤ d * e ∧
      ∀ i : ι, A.eval (C (α i)) = curveCoordPoly u i * B.eval (C (α i)) := by
  classical
  have hde_lt_S : d * (e + 1) < S.card :=
    (Nat.mul_lt_mul_of_pos_left (by omega : e + 1 < Fintype.card ι) (by omega)).trans hS
  let Col := Fin (k + e) ⊕ Fin (e + 1)
  let M : Matrix ι Col F[X] := fun i => Sum.elim
    (fun t => C (α i ^ (t : ℕ))) (fun t => -(curveCoordPoly u i * C (α i ^ (t : ℕ))))
  let colDeg : Col → ℕ := Sum.elim (fun _ => 0) (fun _ => d)
  have hM_deg : ∀ i j, (M i j).natDegree ≤ colDeg j := fun i j => by
    cases j with
    | inl t => exact (natDegree_C _).le
    | inr t =>
      simp only [M, Sum.elim_inr, natDegree_neg, colDeg]
      exact natDegree_mul_le.trans
        (by rw [natDegree_C, add_zero]; exact natDegree_curveCoordPoly_le u i)
  have hdep := berlekampWelch_cols_not_linearIndependent (α := α) (e := e) (k := k) (d := d)
    u S hde_lt_S hclose hk1
  obtain ⟨x, hx_ne, hMx, hx_deg⟩ := exists_cramer_kernel_vec M colDeg hM_deg hdep
  have hsum_colDeg : ∑ c : Col, colDeg c = d * (e + 1) := by
    rw [Fintype.sum_sum_type]
    simp [colDeg, mul_comm]
  let Araw : F[X][Y] := ofFn (k + e) fun t => x (.inl t)
  let Braw : F[X][Y] := ofFn (e + 1) fun t => x (.inr t)
  have hraw_eval : ∀ i : ι, Araw.eval (C (α i)) = curveCoordPoly u i * Braw.eval (C (α i)) := by
    intro i
    have hi := congrFun hMx i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
    rw [Fintype.sum_sum_type] at hi
    simp only [M, Sum.elim_inl, Sum.elim_inr] at hi
    have hneg : ∑ t : Fin (e + 1), -(curveCoordPoly u i * C (α i ^ (t : ℕ))) * x (.inr t) =
        -(∑ t : Fin (e + 1), curveCoordPoly u i * C (α i ^ (t : ℕ)) * x (.inr t)) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ => neg_mul _ _
    have hAeval : Araw.eval (C (α i)) = ∑ t : Fin (k + e), C (α i ^ (t : ℕ)) * x (.inl t) := by
      simp only [Araw, ofFn_eq_sum_monomial, eval_finsetSum, eval_monomial, ← C_pow]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hBeval : curveCoordPoly u i * Braw.eval (C (α i)) =
        ∑ t : Fin (e + 1), curveCoordPoly u i * C (α i ^ (t : ℕ)) * x (.inr t) := by
      simp only [Braw, ofFn_eq_sum_monomial, eval_finsetSum, eval_monomial, ← C_pow,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hAeval, hBeval]; exact eq_of_sub_eq_zero (by rwa [sub_eq_add_neg, ← hneg])
  have hAraw_deg : Araw.degree < (k + e : ℕ) := ofFn_degree_lt _
  have hBraw_deg : Braw.natDegree ≤ e := Nat.lt_succ_iff.1 (ofFn_natDegree_lt (Nat.succ_pos e) _)
  have hdegZ_ofFn : ∀ {m : ℕ} (f : Fin m → F[X]) {bd : ℕ},
      (∀ t, (f t).natDegree ≤ bd) → (Bivariate.swap (ofFn m f)).natDegree ≤ bd := by
    intro m f bd hf
    refine (Bivariate.natDegree_swap_le_iff _ _).2 fun t => ?_
    by_cases ht : t < m
    · rw [ofFn_coeff_eq_val_of_lt _ ht]; exact hf ⟨t, ht⟩
    · rw [ofFn_coeff_eq_zero_of_ge _ (not_lt.1 ht), natDegree_zero]; exact Nat.zero_le _
  have hAraw_degZ : (Bivariate.swap Araw).natDegree ≤ d * (e + 1) :=
    hdegZ_ofFn _ fun t => (hx_deg (.inl t)).trans <| by
      rw [← hsum_colDeg]; exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  have hBraw_degZ : (Bivariate.swap Braw).natDegree ≤ d * e :=
    hdegZ_ofFn _ fun t => (hx_deg (.inr t)).trans_eq <| by
      have h := Finset.add_sum_erase Finset.univ colDeg (mem_univ (Sum.inr t))
      rw [hsum_colDeg] at h; change d + _ = d * (e + 1) at h
      have : d * (e + 1) = d + d * e := by ring
      omega
  have hBraw_ne : Braw ≠ 0 := fun hB0 => by
    have hA0 : Araw = 0 := eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (Finset.univ.image fun i => C (α i))
      (by have hinjC : Function.Injective (fun i : ι => (C (α i) : F[X])) := C_injective.comp hα
          rw [card_image_of_injective _ hinjC, card_univ]
          exact hAraw_deg.trans_le (Nat.cast_le.2 (by omega)))
      (fun y hy => by
        obtain ⟨i, _, rfl⟩ := mem_image.1 hy; rw [hraw_eval i, hB0, eval_zero, mul_zero])
    exact hx_ne <| funext fun j => match j with
      | .inl t => congrFun (injective_ofFn (k + e) (hA0.trans (map_zero _).symm)) t
      | .inr t => congrFun (injective_ofFn (e + 1) (hB0.trans (map_zero _).symm)) t
  let h : F[X] := Braw.content
  have hh0 : h ≠ 0 := content_eq_zero_iff.not.2 hBraw_ne
  let B : F[X][Y] := Braw.primPart
  have hBraw_eq : Braw = C h * B := Braw.eq_C_content_mul_primPart
  obtain ⟨J, -, hJ_card⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (n := k + e) (by rw [card_univ]; omega)
  have hJ_pos : 0 < J.card := by omega
  obtain ⟨A, hA_deg, hAraw_eq⟩ := exists_div_C_of_dvd_eval hα hJ_pos
    (hJ_card ▸ hAraw_deg) fun i _ => by
      rw [hraw_eval i, hBraw_eq, eval_mul, eval_C]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  refine ⟨A, B, Braw.isPrimitive_primPart, hJ_card ▸ hA_deg,
    (natDegree_primPart Braw).symm ▸ hBraw_deg, ?_, ?_, fun i => ?_⟩
  · by_cases hA0 : A = 0
    · simp only [hA0, map_zero, natDegree_zero, Nat.zero_le]
    · have := natDegree_swap_mul (C_ne_zero.2 hh0) hA0; rw [← hAraw_eq] at this; omega
  · have h1 := natDegree_swap_mul (C_ne_zero.2 hh0) Braw.isPrimitive_primPart.ne_zero
    rw [← hBraw_eq] at h1
    change (Bivariate.swap Braw).natDegree = (Bivariate.swap (C h)).natDegree +
      (Bivariate.swap B).natDegree at h1
    omega
  · exact mul_left_cancel₀ hh0 <| by
      have h1 := hraw_eval i; rw [hAraw_eq, hBraw_eq, eval_mul, eval_mul, eval_C] at h1
      simpa only [mul_left_comm] using h1

/-! ### Stage 2: symmetric Sylvester resultant elimination forces `B ∣ A` -/

private lemma resultant_degree_collapse {n k e d aX bX cX aZ bZ sCard iCard : ℕ}
    (he : 2 * e + k ≤ n) (he1 : 1 ≤ e) (hk1 : 1 ≤ k)
    (hS : d * n < sCard) (hbcX : bX + cX ≤ e) (hI : n - cX ≤ iCard)
    (haX : aX ≤ k - 1 + bX) (haZ : aZ ≤ d + bZ)
    (hresX : bX * sCard ≤ bX * aZ + (k - 1 + bX) * bZ)
    (hresZ : bZ * iCard ≤ bZ * aX + (d + bZ) * bX) :
    bX = 0 ∧ bZ = 0 := by
  have hbZ_le : bZ ≤ d * bX := by
    have h1 := Nat.mul_le_mul_left bZ hI
    have h2 := Nat.mul_le_mul_left bZ haX
    have h3 : bZ * (k - 1 + bX) + (d + bZ) * bX = d * bX + (k - 1 + 2 * bX) * bZ := by ring
    have h4 : k - 1 + 2 * bX ≤ n - cX - 1 := by omega
    have h5 : bZ * (n - cX) ≤ d * bX + (n - cX - 1) * bZ :=
      h1.trans (hresZ.trans ((Nat.add_le_add_right h2 _).trans
        (h3 ▸ Nat.add_le_add_left (Nat.mul_le_mul_right bZ h4) _)))
    have h7 : bZ * (n - cX) = (n - cX - 1) * bZ + bZ := by
      have : 1 ≤ n - cX := by omega
      zify [this]; ring
    omega
  have hbX_zero : bX = 0 := by
    by_contra hbX_ne
    have h1 := Nat.mul_le_mul_left bX haZ
    have h2 : bX * (d + bZ) + (k - 1 + bX) * bZ = d * bX + (k - 1 + 2 * bX) * bZ := by ring
    have h3 : k - 1 + 2 * bX ≤ n - 1 := by omega
    have h4 : bX * sCard ≤ d * bX + (n - 1) * (d * bX) :=
      hresX.trans ((Nat.add_le_add_right h1 _).trans (h2 ▸ Nat.add_le_add_left
        ((Nat.mul_le_mul_right bZ h3).trans (Nat.mul_le_mul_left (n - 1) hbZ_le)) _))
    have h5 : d * bX + (n - 1) * (d * bX) = bX * (d * n) := by
      have : 1 ≤ n := by omega
      zify [this]; ring
    have h6 := Nat.le_of_mul_le_mul_left (h5 ▸ h4) (Nat.pos_of_ne_zero hbX_ne)
    omega
  rw [hbX_zero, mul_zero] at hbZ_le
  exact ⟨hbX_zero, Nat.eq_zero_of_le_zero hbZ_le⟩

/-- Symmetric `natDegree` bound on `f : F[X][Y]` from specializations `f(w) = g(w) * p` on a set
`W` exceeding `deg_Z(f)`. -/
private lemma natDegree_le_of_map_eval_eq_mul {f g : F[X][Y]} {m : ℕ} {W : Finset F}
    (hW_deg : (Bivariate.swap f).natDegree < W.card)
    (hmap : ∀ w ∈ W, ∃ p : F[X], p.natDegree ≤ m ∧
      f.map (evalRingHom w) = g.map (evalRingHom w) * p) :
    f.natDegree ≤ m + g.natDegree :=
  natDegree_le_iff_coeff_eq_zero.2 fun t ht =>
    eq_zero_of_degree_lt_of_eval_finset_eq_zero W (by
      by_cases h0 : f.coeff t = 0
      · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
      · rw [degree_eq_natDegree h0, Nat.cast_lt]
        exact (Bivariate.natDegree_coeff_le_natDegree_swap f t).trans_lt hW_deg) fun w hw => by
      obtain ⟨p, hp, hfw⟩ := hmap w hw
      have hc : (f.coeff t).eval w = (g.map (evalRingHom w) * p).coeff t := by
        simpa only [coeff_map, coe_evalRingHom] using congrArg (fun q : F[X] => q.coeff t) hfw
      exact hc ▸ coeff_eq_zero_of_natDegree_lt
        ((natDegree_mul_le.trans (Nat.add_le_add natDegree_map_le hp)).trans_lt (by omega))

private lemma isRelPrime_swap {f g : F[X][Y]} (h : IsRelPrime f g) :
    IsRelPrime (Bivariate.swap f) (Bivariate.swap g) := fun r hrA hrB => by
  have h1 : Bivariate.swap r ∣ f := Bivariate.swap_swap_apply f ▸ map_dvd Bivariate.swap hrA
  have h2 : Bivariate.swap r ∣ g := Bivariate.swap_swap_apply g ▸ map_dvd Bivariate.swap hrB
  exact Bivariate.swap_swap_apply r ▸ (h h1 h2).map Bivariate.swap

private lemma exists_quotient_of_bivariate_solution [Fintype ι]
    {α : ι → F} {e k d : ℕ} (hα : Function.Injective α)
    (he : 2 * e + k ≤ Fintype.card ι) (hd : 1 ≤ d) (he1 : 1 ≤ e) (hk1 : 1 ≤ k)
    (wPoly : ι → F[X]) (hwPoly_deg : ∀ i, (wPoly i).natDegree ≤ d)
    (S : Finset F) (hS : d * Fintype.card ι < S.card)
    {A B : F[X][Y]} (hA0 : A ≠ 0) (hB_prim : B.IsPrimitive) (hB_deg : B.natDegree ≤ e)
    (hA_degZ : (Bivariate.swap A).natDegree ≤ d * (e + 1))
    (hAB_eval : ∀ i : ι, A.eval (C (α i)) = wPoly i * B.eval (C (α i)))
    (hslice : ∀ z ∈ S, ∃ Pz : F[X], Pz.degree < k ∧
      A.map (evalRingHom z) = Pz * B.map (evalRingHom z)) :
    ∃ P : F[X][Y], P.degree < k ∧ A = P * B := by
  classical
  have hB_ne : B ≠ 0 := hB_prim.ne_zero
  have hde_lt_S : d * (e + 1) < S.card :=
    (Nat.mul_lt_mul_of_pos_left (by omega : e + 1 < Fintype.card ι) (by omega)).trans hS
  have hB_map_ne : ∀ z : F, B.map (evalRingHom z) ≠ 0 := fun z h0 => by
    have hdeg0 := natDegree_eq_zero_of_isUnit
      ((isPrimitive_iff_isUnit_of_C_dvd.1 hB_prim) _ (C_X_sub_C_dvd_of_map_evalRingHom_eq_zero h0))
    rw [natDegree_X_sub_C] at hdeg0
    exact one_ne_zero hdeg0
  set g : F[X][Y] := gcd A B with hg_def
  obtain ⟨A₀, hA_eq⟩ : g ∣ A := gcd_dvd_left A B
  obtain ⟨B₀, hB_eq⟩ : g ∣ B := gcd_dvd_right A B
  have hg_ne : g ≠ 0 := fun h0 => hB_ne (by rw [hB_eq, h0, zero_mul])
  have hA₀_ne : A₀ ≠ 0 := fun h0 => hA0 (by rw [hA_eq, h0, mul_zero])
  have hB₀_ne : B₀ ≠ 0 := fun h0 => hB_ne (by rw [hB_eq, h0, mul_zero])
  have hrel : IsRelPrime A₀ B₀ := fun r hrA hrB => by
    obtain ⟨s, hs⟩ := dvd_gcd (hA_eq ▸ mul_dvd_mul_left g hrA) (hB_eq ▸ mul_dvd_mul_left g hrB)
    exact isUnit_iff_exists_inv.2 ⟨s, mul_left_cancel₀ hg_ne (by rw [← mul_assoc, ← hs, mul_one])⟩
  have hbcX : B₀.natDegree + g.natDegree ≤ e := by
    have := natDegree_mul hg_ne hB₀_ne; rw [← hB_eq] at this; omega
  have haZ_raw : (Bivariate.swap A₀).natDegree ≤ d * (e + 1) := by
    have := natDegree_swap_mul hg_ne hA₀_ne; rw [← hA_eq] at this; omega
  have hslice₀ : ∀ z ∈ S, ∃ Pz : F[X], Pz.natDegree ≤ k - 1 ∧
      A₀.map (evalRingHom z) = B₀.map (evalRingHom z) * Pz := fun z hz => by
    obtain ⟨Pz, hPz_deg, hABz⟩ := hslice z hz
    have hgz_ne : g.map (evalRingHom z) ≠ 0 := fun h0 =>
      hB_map_ne z (by rw [hB_eq, Polynomial.map_mul, h0, zero_mul])
    rw [hA_eq, hB_eq, Polynomial.map_mul, Polynomial.map_mul] at hABz
    have hPz_le : Pz.natDegree ≤ k - 1 := by
      by_cases h0 : Pz = 0
      · rw [h0, natDegree_zero]; exact Nat.zero_le _
      · have := (natDegree_lt_iff_degree_lt h0).2 hPz_deg; omega
    exact ⟨Pz, hPz_le, (mul_left_cancel₀ hgz_ne (by simpa only [mul_left_comm] using hABz)).trans
      (mul_comm _ _)⟩
  have haX_le : A₀.natDegree ≤ k - 1 + B₀.natDegree :=
    natDegree_le_of_map_eval_eq_mul (haZ_raw.trans_lt hde_lt_S) hslice₀
  let I : Finset ι := Finset.univ.filter fun i => g.eval (C (α i)) ≠ 0
  have hI_card : Fintype.card ι - g.natDegree ≤ I.card :=
    card_filter_eval_ne_zero_ge (C_injective.comp hα) hg_ne
  have hI_map : ∀ x ∈ I.image α, ∃ p : F[X], p.natDegree ≤ d ∧
      (Bivariate.swap A₀).map (evalRingHom x) = (Bivariate.swap B₀).map (evalRingHom x) * p := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    refine ⟨wPoly i, hwPoly_deg i, ?_⟩
    rw [← Bivariate.eval_C_eq_map_swap, ← Bivariate.eval_C_eq_map_swap]
    have h1 := hAB_eval i; rw [hA_eq, hB_eq, eval_mul, eval_mul] at h1
    exact (mul_left_cancel₀ (mem_filter.1 hi).2 (by simpa only [mul_left_comm] using h1)).trans
      (mul_comm _ _)
  have haZ_le : (Bivariate.swap A₀).natDegree ≤ d + (Bivariate.swap B₀).natDegree :=
    natDegree_le_of_map_eval_eq_mul (by
      rw [Bivariate.swap_swap_apply, card_image_of_injective _ hα]; omega) hI_map
  have hres_X := card_mul_natDegree_le_of_isRelPrime_resultant hrel hB₀_ne haX_le
    (Bivariate.natDegree_coeff_le_natDegree_swap A₀)
    (Bivariate.natDegree_coeff_le_natDegree_swap B₀)
    fun z hz => let ⟨Pz, hP, hm⟩ := hslice₀ z hz; ⟨Pz, Nat.add_le_add_right hP _, hm⟩
  have hres_Z := card_mul_natDegree_le_of_isRelPrime_resultant (W := I.image α)
    (isRelPrime_swap hrel) ((map_ne_zero_iff Bivariate.swap Bivariate.swap.injective).2 hB₀_ne)
    haZ_le (fun t => Bivariate.swap_swap_apply A₀ ▸ Bivariate.natDegree_coeff_le_natDegree_swap _ t)
    (fun t => Bivariate.swap_swap_apply B₀ ▸ Bivariate.natDegree_coeff_le_natDegree_swap _ t)
    fun x hx => let ⟨p, hp, hm⟩ := hI_map x hx; ⟨p, Nat.add_le_add_right hp _, hm⟩
  rw [card_image_of_injective _ hα] at hres_Z
  obtain ⟨hbX_zero, hbZ_zero⟩ :=
    resultant_degree_collapse he he1 hk1 hS hbcX hI_card haX_le haZ_le hres_X hres_Z
  have hB₀_eq_CC : B₀ = C (C ((B₀.coeff 0).coeff 0)) := by
    have h2 : (B₀.coeff 0).natDegree = 0 :=
      Nat.eq_zero_of_le_zero
        ((Bivariate.natDegree_coeff_le_natDegree_swap B₀ 0).trans_eq hbZ_zero)
    conv_lhs => rw [eq_C_of_natDegree_eq_zero hbX_zero, eq_C_of_natDegree_eq_zero h2]
  set c₀ : F := (B₀.coeff 0).coeff 0
  have hc₀_ne : c₀ ≠ 0 := fun h0 => hB₀_ne (by rw [hB₀_eq_CC, h0, C_0, C_0])
  refine ⟨C (C c₀⁻¹) * A₀, ?_, ?_⟩
  · by_cases hP0 : C (C c₀⁻¹) * A₀ = 0
    · rw [hP0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree hP0, Nat.cast_lt]
      have : (C (C c₀⁻¹) * A₀).natDegree ≤ k - 1 :=
        (natDegree_C_mul_le _ _).trans (by rwa [hbX_zero, add_zero] at haX_le)
      omega
  · calc A = g * A₀ := hA_eq
      _ = g * (C (C c₀⁻¹) * C (C c₀) * A₀) := by
          rw [← C_mul, ← C_mul, inv_mul_cancel₀ hc₀_ne, C_1, C_1, one_mul]
      _ = C (C c₀⁻¹) * A₀ * B := by rw [hB_eq, hB₀_eq_CC]; ring

/-! ### Stage 3: assembling the positive-regime curve theorem -/

private lemma exists_correlatedAgreement_curve_unique_pos [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k d : ℕ} (hα : Function.Injective α)
    (he : 2 * e + k ≤ Fintype.card ι) (hd : 1 ≤ d) (he1 : 1 ≤ e) (hk1 : 1 ≤ k)
    (u : Fin (d + 1) → (ι → F)) (S : Finset F) (hS : d * Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v : Fin (d + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  classical
  obtain ⟨A, B, hB_prim, hA_deg, hB_deg, hA_degZ, _, hAB_eval⟩ :=
    exists_primitive_bivariate_solution hα he hd he1 hk1 u S hS hclose
  let D' : Finset ι := Finset.univ.filter fun i => B.eval (C (α i)) ≠ 0
  have hD'_card : Fintype.card ι - e ≤ D'.card :=
    (Nat.sub_le_sub_left hB_deg _).trans
      (card_filter_eval_ne_zero_ge (C_injective.comp hα) hB_prim.ne_zero)
  by_cases hA0 : A = 0
  · refine ⟨D', hD'_card, fun _ => 0, fun _ => Submodule.zero_mem _, fun i hi j => ?_⟩
    have hw0 := (mul_eq_zero.1 (by simpa [hA0] using (hAB_eval i).symm)).resolve_right
      (mem_filter.1 hi).2
    simp [← coeff_curveCoordPoly u i j, hw0]
  have hslice : ∀ z ∈ S, ∃ Pz : F[X], Pz.degree < k ∧
      A.map (evalRingHom z) = Pz * B.map (evalRingHom z) := fun z hz => by
    obtain ⟨c, hcRS, hdist⟩ := hclose z hz
    obtain ⟨Pz, hPz_deg, rfl⟩ := mem_reedSolomon.1 hcRS
    let good : Finset ι := Finset.univ.filter fun i =>
      (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = Pz.eval (α i)
    have hgood := card_filter_eq_add_hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j)
      (fun i => Pz.eval (α i))
    refine ⟨Pz, hPz_deg, sub_eq_zero.1 (eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (good.image α) ?_ fun x hx => ?_)⟩
    · rw [card_image_of_injective _ hα]
      have hmul_deg : (Pz * B.map (evalRingHom z)).degree < (k + e : ℕ) := by
        by_cases hPz0 : Pz = 0
        · rw [hPz0, zero_mul, degree_zero]; exact WithBot.bot_lt_coe _
        · by_cases hBz0 : B.map (evalRingHom z) = 0
          · rw [hBz0, mul_zero, degree_zero]; exact WithBot.bot_lt_coe _
          · have h1 := (natDegree_lt_iff_degree_lt hPz0).2 hPz_deg
            have h2 : (B.map (evalRingHom z)).natDegree ≤ e := natDegree_map_le.trans hB_deg
            refine (degree_mul_le _ _).trans_lt ?_
            rw [degree_eq_natDegree hPz0, degree_eq_natDegree hBz0, ← Nat.cast_add, Nat.cast_lt]
            omega
      change good.card + hammingDist _ _ = Fintype.card ι at hgood
      exact (degree_sub_le _ _).trans_lt ((max_lt (degree_map_le.trans_lt hA_deg)
        hmul_deg).trans_le (Nat.cast_le.2 (by omega)))
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      rw [eval_sub, eval_mul, Polynomial.map_evalRingHom_eval, Polynomial.evalEval,
        Polynomial.map_evalRingHom_eval, Polynomial.evalEval, hAB_eval i, eval_mul,
        eval_curveCoordPoly, (mem_filter.1 hi).2, sub_self]
  obtain ⟨P, hP_deg, hA_eq_PB⟩ := exists_quotient_of_bivariate_solution hα he hd he1 hk1
    (curveCoordPoly u) (natDegree_curveCoordPoly_le u) S hS hA0 hB_prim hB_deg hA_degZ
    hAB_eval hslice
  refine ⟨D', hD'_card, fun j i => ((Bivariate.swap P).coeff (j : ℕ)).eval (α i),
    fun j => eval_mem_reedSolomon α (degree_coeff_swap_lt hP_deg j), fun i hi j => ?_⟩
  have hPi : P.eval (C (α i)) = curveCoordPoly u i :=
    mul_right_cancel₀ (mem_filter.1 hi).2 (by simpa [hA_eq_PB, eval_mul] using hAB_eval i)
  have hcoeff := congrArg (fun q : F[X] => q.coeff (j : ℕ)) hPi
  rw [Bivariate.eval_C_eq_map_swap, coeff_map, coe_evalRingHom, coeff_curveCoordPoly] at hcoeff
  exact hcoeff.symm

end Helpers

/-! ### Public correlated agreement and proximity-gap theorems -/

variable [Fintype ι] [DecidableEq F]

/-- If `d + 1` words `u j` agree with `v j` on a shared subset `D'` of size at least `|ι| - e`,
then every linear combination `∑ j, z ^ j • u j` on the parameterized curve is within Hamming
distance `e` of `∑ j, z ^ j • v j`. -/
theorem hammingDist_curve_le_of_eq_on {e d : ℕ} {D' : Finset ι}
    {u v : Fin (d + 1) → (ι → F)} (hD' : Fintype.card ι - e ≤ D'.card)
    (hagree : ∀ i ∈ D', ∀ j, u j i = v j i) (z : F) :
    hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j)
      (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j) ≤ e := by
  classical
  have hsub : D' ⊆ Finset.univ.filter fun i =>
      (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j) i :=
    fun i hi => mem_filter.2 ⟨mem_univ i, by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [hagree i hi j]⟩
  have htot := card_filter_eq_add_hammingDist
    (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j)
  have := card_le_card hsub; omega

/-- If two words `u₀, u₁` agree with `v₀, v₁` on a shared subset `D'` of size at least `|ι| - e`,
then `u₀ + z • u₁` is within Hamming distance `e` of `v₀ + z • v₁` for every scalar `z : F`. -/
theorem hammingDist_add_smul_le_of_eq_on {e : ℕ} {D' : Finset ι}
    {u₀ u₁ v₀ v₁ : ι → F} (hD' : Fintype.card ι - e ≤ D'.card)
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i) (z : F) :
    hammingDist (u₀ + z • u₁) (v₀ + z • v₁) ≤ e := by
  classical
  have hsub : D' ⊆ Finset.univ.filter fun i => (u₀ + z • u₁) i = (v₀ + z • v₁) i :=
    fun i hi => mem_filter.2 ⟨mem_univ i, by simp [(hagree i hi).1, (hagree i hi).2]⟩
  have htot := card_filter_eq_add_hammingDist (u₀ + z • u₁) (v₀ + z • v₁)
  have := card_le_card hsub; omega

/-- **Correlated agreement on parameterized curves in the unique-decoding regime**
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.1]).

Let `α : ι → F` be distinct evaluation points, `2 * e + k ≤ |ι|`, and `u : Fin (d + 1) → (ι → F)`.
If strictly more than `d * |ι|` scalars `z ∈ S` satisfy that the curve point
`∑ j : Fin (d + 1), z ^ (j : ℕ) • u j` lies within Hamming distance `e` of `reedSolomon α k`,
then there exist a single shared coordinate subset `D' : Finset ι` with `|ι| - e ≤ #D'` and
codewords `v : Fin (d + 1) → (ι → F)` in `reedSolomon α k` agreeing with `u` at every
coordinate in `D'`. -/
theorem exists_correlatedAgreement_curve_unique {α : ι → F} {e k d : ℕ}
    (hα : Function.Injective α) (he : 2 * e + k ≤ Fintype.card ι)
    (u : Fin (d + 1) → (ι → F)) (S : Finset F) (hS : d * Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v : Fin (d + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [zero_mul] at hS
    obtain ⟨z, hz⟩ := Finset.card_pos.1 hS
    obtain ⟨c, hcRS, hdist⟩ := hclose z hz
    have hcurve : (∑ j : Fin 1, z ^ (j : ℕ) • u j) = u 0 := by
      simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul]
    rw [hcurve] at hdist
    have htot := card_filter_eq_add_hammingDist (u 0) c
    exact ⟨Finset.univ.filter fun i => u 0 i = c i, by omega, fun _ => c, fun _ => hcRS,
      fun i hi j => Fin.eq_zero j ▸ (mem_filter.1 hi).2⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · let D' : Finset ι := Finset.univ.filter fun i => ∀ j, u j i = 0
    refine ⟨D', ?_, fun _ => 0, fun _ => Submodule.zero_mem _, fun i hi j => (mem_filter.1 hi).2 j⟩
    by_contra hlt
    let bad : Finset ι := Finset.univ.filter fun i => ¬ ∀ j, u j i = 0
    have hS_sub : S ⊆ bad.biUnion fun i => (curveCoordPoly u i).roots.toFinset := fun z hz => by
      obtain ⟨c, hcRS, hdist⟩ := hclose z hz
      obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hcRS
      have hp0 : p = 0 := by
        rw [degree_lt_iff_coeff_zero] at hp; ext t; exact hp t (Nat.zero_le t)
      have hc0 : (fun i => p.eval (α i)) = 0 :=
        funext fun i => by rw [hp0, eval_zero, Pi.zero_apply]
      rw [hc0] at hdist
      let zeros := Finset.univ.filter fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = (0 : ι → F) i
      have htot : zeros.card + hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) 0 =
          Fintype.card ι := card_filter_eq_add_hammingDist _ _
      have hnot_sub : ¬ zeros ⊆ D' := fun hsub => by
        have := card_le_card hsub; omega
      obtain ⟨i, hiZ, hiD'⟩ := Finset.not_subset.1 hnot_sub
      have hne : ¬ ∀ j, u j i = 0 := fun hall => hiD' (mem_filter.2 ⟨mem_univ i, hall⟩)
      have hw_ne : curveCoordPoly u i ≠ 0 := fun h0 => hne fun j => by
        rw [← coeff_curveCoordPoly u i j, h0, coeff_zero]
      exact mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ i, hne⟩, Multiset.mem_toFinset.2 <|
        (mem_roots hw_ne).2 (by rw [IsRoot.def, eval_curveCoordPoly]; exact (mem_filter.1 hiZ).2)⟩
    have hcard_le : S.card ≤ d * Fintype.card ι := calc
      S.card ≤ (bad.biUnion fun i => (curveCoordPoly u i).roots.toFinset).card :=
        card_le_card hS_sub
      _ ≤ ∑ i ∈ bad, (curveCoordPoly u i).roots.toFinset.card := card_biUnion_le
      _ ≤ ∑ _i ∈ bad, d := Finset.sum_le_sum fun i _ =>
          (Multiset.toFinset_card_le _).trans
            ((card_roots' _).trans (natDegree_curveCoordPoly_le u i))
      _ = bad.card * d := by simp only [Finset.sum_const, smul_eq_mul]
      _ ≤ Fintype.card ι * d := Nat.mul_le_mul_right d (Finset.card_le_univ bad)
      _ = d * Fintype.card ι := mul_comm _ _
    omega
  rcases Nat.eq_zero_or_pos e with rfl | he1
  · have hS_ge : d + 1 ≤ S.card := by
      have := Nat.le_mul_of_pos_right d (by omega : 1 ≤ Fintype.card ι); omega
    obtain ⟨T, hTS, hT_card⟩ := Finset.exists_subset_card_eq hS_ge
    have hT_mem : ∀ z ∈ T, (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) ∈ reedSolomon α k :=
      fun z hz => let ⟨c, hcRS, hdist⟩ := hclose z (hTS hz)
        hammingDist_eq_zero.1 (Nat.eq_zero_of_le_zero hdist) ▸ hcRS
    refine ⟨Finset.univ, by rw [card_univ, Nat.sub_zero], u, fun j => ?_, fun _ _ _ => rfl⟩
    have hu_eq : u j = ∑ z ∈ T, (Lagrange.basis T id z).coeff (j : ℕ) •
        ∑ j' : Fin (d + 1), z ^ (j' : ℕ) • u j' := funext fun i => by
      let qi := Lagrange.interpolate T id fun z => (∑ j' : Fin (d + 1), z ^ (j' : ℕ) • u j') i
      have hpq : curveCoordPoly u i = qi := sub_eq_zero.1 <|
        eq_zero_of_degree_lt_of_eval_finset_eq_zero T
          ((degree_sub_le _ _).trans_lt (max_lt
            (hT_card ▸ ofFn_degree_lt (fun j => u j i))
            (Lagrange.degree_interpolate_lt _ Function.injective_id.injOn)))
          fun z hz => by
            have hqi : qi.eval z = (∑ j' : Fin (d + 1), z ^ (j' : ℕ) • u j') i :=
              Lagrange.eval_interpolate_at_node _ Function.injective_id.injOn hz
            rw [eval_sub, eval_curveCoordPoly, hqi, sub_self]
      have hcoeff := congrArg (fun p : F[X] => p.coeff (j : ℕ)) hpq
      simp only [coeff_curveCoordPoly, qi, Lagrange.interpolate_apply, finsetSum_coeff,
        coeff_C_mul] at hcoeff
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hcoeff
    exact hu_eq ▸ Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (hT_mem z hz)
  · exact exists_correlatedAgreement_curve_unique_pos hα he hd he1 hk u S hS hclose

/-- **Correlated agreement on affine lines in the unique-decoding regime**
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1]).

Let `α : ι → F` be distinct evaluation points, `2 * e + k ≤ |ι|`, and `u₀, u₁ : ι → F`. If
strictly more than `|ι|` scalars `z ∈ S` satisfy that `u₀ + z • u₁` lies within Hamming distance
`e` of `reedSolomon α k`, then there exist a single shared coordinate subset `D' : Finset ι` with
`|ι| - e ≤ #D'` and codewords `v₀, v₁ ∈ reedSolomon α k` agreeing with `u₀, u₁` on `D'`. -/
theorem exists_correlatedAgreement_unique {α : ι → F} {e k : ℕ}
    (hα : Function.Injective α) (he : 2 * e + k ≤ Fintype.card ι)
    (u₀ u₁ : ι → F) (S : Finset F) (hS : Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v₁ ∈ reedSolomon α k,
        ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_correlatedAgreement_curve_unique (d := 1) hα he
    ![u₀, u₁] S (by simpa only [one_mul] using hS) fun z hz => by
      simpa only [show (∑ j : Fin 2, z ^ (j : ℕ) • ![u₀, u₁] j) = u₀ + z • u₁ by
        simp [Fin.sum_univ_two]] using hclose z hz
  exact ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ⟨hagree i hi 0, hagree i hi 1⟩⟩

/-- **Proximity-gap dichotomy for parameterized curves in the unique-decoding regime**
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.1]).

Over a finite field `F`, for any `d + 1` words `u : Fin (d + 1) → (ι → F)` and `2 * e + k ≤ |ι|`,
either every point on the curve `∑ j, z ^ j • u j` lies within Hamming distance `e` of
`reedSolomon α k`, or at most `d * |ι|` scalars `z : F` do. -/
theorem proximityGap_curve_unique [Fintype F] {α : ι → F} {e k d : ℕ}
    (hα : Function.Injective α) (he : 2 * e + k ≤ Fintype.card ι)
    (u : Fin (d + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c ≤ e] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c ≤ e) ∨
      (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c ≤ e).card ≤
          d * Fintype.card ι := by
  by_cases hgt : d * Fintype.card ι <
      (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c ≤ e).card
  · left
    obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_correlatedAgreement_curve_unique hα he u _ hgt
      (fun z hz => (mem_filter.1 hz).2)
    intro z
    refine ⟨∑ j : Fin (d + 1), z ^ (j : ℕ) • v j, ?_,
      hammingDist_curve_le_of_eq_on hD' hagree z⟩
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvRS j)
  · right
    exact le_of_not_gt hgt

/-- **Proximity-gap dichotomy for affine lines in the unique-decoding regime**
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.2]).

Over a finite field `F`, for any two words `u₀, u₁ : ι → F` and `2 * e + k ≤ |ι|`, either every
point `u₀ + z • u₁` on the affine line lies within Hamming distance `e` of `reedSolomon α k`, or
at most `|ι|` scalars `z : F` do. -/
theorem proximityGap_unique [Fintype F] {α : ι → F} {e k : ℕ}
    (hα : Function.Injective α) (he : 2 * e + k ≤ Fintype.card ι)
    (u₀ u₁ : ι → F)
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e] :
    (∀ z : F, ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e) ∨
      (Finset.univ.filter fun z : F =>
        ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e).card ≤ Fintype.card ι := by
  by_cases hgt : Fintype.card ι <
      (Finset.univ.filter fun z : F =>
        ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e).card
  · left
    obtain ⟨D', hD', v₀, hv₀, v₁, hv₁, hagree⟩ := exists_correlatedAgreement_unique hα he u₀ u₁ _
      hgt (fun z hz => (mem_filter.1 hz).2)
    intro z
    exact ⟨v₀ + z • v₁, Submodule.add_mem _ hv₀ (Submodule.smul_mem _ z hv₁),
      hammingDist_add_smul_le_of_eq_on hD' hagree z⟩
  · right
    exact le_of_not_gt hgt

/-! ### Unique maximal agreement set and unique codewords (Theorems 1.4–1.6) -/

omit [DecidableEq F] in
/-- **Generic uniqueness step in the unique-decoding regime:** given an existing
correlated-agreement witness `(D₀, v)` in the unique-decoding regime `2 * e + k ≤ |ι|`, upgrades it
to the unique maximal shared agreement set and unique codewords (used to prove the uniqueness
clauses of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.4, 1.5, and 1.6], accepted JACM 2023
manuscript pp. 5–6; Remark 4.1, p. 13).

Let `α : ι → F` be distinct evaluation points and `2 * e + k ≤ |ι|`. For any indexed family of
words `u : κ → (ι → F)` whose premise already supplies a shared agreement set `D₀` of size at least
`|ι| - e` with codewords `v : κ → (ι → F)` in `reedSolomon α k`, there exist a greatest (hence
unique maximal) shared agreement set `D' : Finset ι` of size at least `|ι| - e` and unique
codewords `v : κ → (ι → F)` in `reedSolomon α k`: every qualifying pair `(D'', w)` satisfies
`D'' ⊆ D'` and `w = v`. -/
theorem exists_uniqueMaximal_correlatedAgreement_of_exists
    {α : ι → F} {e k : ℕ} {κ : Type*}
    (hα : Function.Injective α) (he : 2 * e + k ≤ Fintype.card ι)
    {u : κ → (ι → F)}
    (hex : ∃ D₀ : Finset ι, Fintype.card ι - e ≤ D₀.card ∧
      ∃ v : κ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D₀, ∀ j, u j i = v j i) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v : κ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        (∀ i ∈ D', ∀ j, u j i = v j i) ∧
        ∀ (D'' : Finset ι) (w : κ → (ι → F)),
          Fintype.card ι - e ≤ D''.card → (∀ j, w j ∈ reedSolomon α k) →
          (∀ i ∈ D'', ∀ j, u j i = w j i) →
          D'' ⊆ D' ∧ w = v := by
  classical
  obtain ⟨D₀, hD₀, v, hvRS, hagree₀⟩ := hex
  let D' : Finset ι := Finset.univ.filter fun i => ∀ j, u j i = v j i
  have hD₀_sub : D₀ ⊆ D' := fun i hi => mem_filter.2 ⟨mem_univ i, hagree₀ i hi⟩
  have hD'_card : Fintype.card ι - e ≤ D'.card := hD₀.trans (card_le_card hD₀_sub)
  have hdist_le : ∀ {D : Finset ι} {w : κ → (ι → F)}, Fintype.card ι - e ≤ D.card →
      (∀ i ∈ D, ∀ j, u j i = w j i) → ∀ j, hammingDist (u j) (w j) ≤ e := by
    intro D w hD hag j
    have hsub : D ⊆ Finset.univ.filter fun i => u j i = w j i :=
      fun i hi => mem_filter.2 ⟨mem_univ i, hag i hi j⟩
    have htot := card_filter_eq_add_hammingDist (u j) (w j)
    have hle := card_le_card hsub
    omega
  refine ⟨D', hD'_card, v, hvRS, fun i hi => (mem_filter.1 hi).2, fun D'' w hD'' hwRS hag'' => ?_⟩
  have hw_eq : w = v := funext fun j =>
    eq_of_hammingDist_le_reedSolomon hα he (hwRS j) (hvRS j)
      (hdist_le hD'' hag'' j) (hdist_le hD₀ hagree₀ j)
  refine ⟨fun i hi => mem_filter.2 ⟨mem_univ i, fun j => ?_⟩, hw_eq⟩
  rw [hag'' i hi j, hw_eq]

/-- **Unique maximal correlated agreement on parameterized curves in the unique-decoding regime**
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.5 & Theorem 6.1], accepted JACM 2023 manuscript
pp. 6 and 28).

Extends `Cslib.Code.exists_correlatedAgreement_curve_unique` with the unique-decoding uniqueness
clause: the maximal shared agreement set `D'` of size at least `|ι| - e` and the codewords
`v : Fin (d + 1) → (ι → F)` are uniquely determined, with every qualifying `(D'', w)` satisfying
`D'' ⊆ D'` and `w = v`. -/
theorem exists_uniqueMaximal_correlatedAgreement_curve_unique {α : ι → F} {e k d : ℕ}
    (hα : Function.Injective α) (he : 2 * e + k ≤ Fintype.card ι)
    (u : Fin (d + 1) → (ι → F)) (S : Finset F) (hS : d * Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v : Fin (d + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        (∀ i ∈ D', ∀ j, u j i = v j i) ∧
        ∀ (D'' : Finset ι) (w : Fin (d + 1) → (ι → F)),
          Fintype.card ι - e ≤ D''.card → (∀ j, w j ∈ reedSolomon α k) →
          (∀ i ∈ D'', ∀ j, u j i = w j i) →
          D'' ⊆ D' ∧ w = v :=
  exists_uniqueMaximal_correlatedAgreement_of_exists hα he
    (exists_correlatedAgreement_curve_unique hα he u S hS hclose)

/-- **Unique maximal correlated agreement on affine lines in the unique-decoding regime**
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.4, Theorem 4.1 & Remark 4.1], accepted JACM 2023
manuscript pp. 5 and 13).

Extends `Cslib.Code.exists_correlatedAgreement_unique` with the unique-decoding uniqueness clause:
the maximal shared agreement set `D'` of size at least `|ι| - e` and the codewords `v₀, v₁` are
uniquely determined, with every qualifying `(D'', w₀, w₁)` satisfying `D'' ⊆ D'`, `w₀ = v₀`, and
`w₁ = v₁`. -/
theorem exists_uniqueMaximal_correlatedAgreement_unique {α : ι → F} {e k : ℕ}
    (hα : Function.Injective α) (he : 2 * e + k ≤ Fintype.card ι)
    (u₀ u₁ : ι → F) (S : Finset F) (hS : Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k, hammingDist (u₀ + z • u₁) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v₁ ∈ reedSolomon α k,
        (∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i) ∧
        ∀ (D'' : Finset ι) (w₀ w₁ : ι → F),
          Fintype.card ι - e ≤ D''.card →
          w₀ ∈ reedSolomon α k → w₁ ∈ reedSolomon α k →
          (∀ i ∈ D'', u₀ i = w₀ i ∧ u₁ i = w₁ i) →
          D'' ⊆ D' ∧ w₀ = v₀ ∧ w₁ = v₁ := by
  obtain ⟨D', hD', v, hvRS, hagree, hmax⟩ := exists_uniqueMaximal_correlatedAgreement_curve_unique
    (d := 1) hα he ![u₀, u₁] S (by simpa only [one_mul] using hS) fun z hz => by
      simpa only [show (∑ j : Fin 2, z ^ (j : ℕ) • ![u₀, u₁] j) = u₀ + z • u₁ by
        simp [Fin.sum_univ_two]] using hclose z hz
  refine ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ⟨hagree i hi 0, hagree i hi 1⟩,
    fun D'' w₀ w₁ hD'' hw₀ hw₁ hag => ?_⟩
  obtain ⟨hsub, hweq⟩ := hmax D'' ![w₀, w₁] hD'' (Fin.forall_fin_two.2 ⟨hw₀, hw₁⟩) fun i hi =>
    Fin.forall_fin_two.2 (hag i hi)
  exact ⟨hsub, congrFun hweq 0, congrFun hweq 1⟩

end Cslib.Code
