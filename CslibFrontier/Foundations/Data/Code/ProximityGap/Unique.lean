/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ReedSolomon
import CslibFrontier.Foundations.Algebra.Polynomial.BivariateSwap
import CslibFrontier.Foundations.Data.Code.BerlekampWelch
import CslibFrontier.Foundations.Data.Hamming
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
  dsimp only [Function.comp_apply]
  rw [Units.smul_def, zsmul_eq_mul]
  have hunit : (↑(Equiv.Perm.sign σ : ℤ) : F[X]).natDegree = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  refine (natDegree_mul_le).trans ?_
  rw [hunit, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  exact Finset.sum_le_sum fun i _ => hM (σ i) i

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

private noncomputable def curveCoordPoly {d : ℕ} (u : Fin (d + 1) → (ι → F)) (i : ι) : F[X] :=
  ∑ j : Fin (d + 1), C (u j i) * X ^ (j : ℕ)

private lemma eval_curveCoordPoly {d : ℕ} (u : Fin (d + 1) → (ι → F)) (i : ι) (z : F) :
    (curveCoordPoly u i).eval z = (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i := by
  simp only [curveCoordPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private lemma natDegree_curveCoordPoly_le {d : ℕ} (u : Fin (d + 1) → (ι → F)) (i : ι) :
    (curveCoordPoly u i).natDegree ≤ d := by
  refine (natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun j _ => ?_⟩
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  exact Nat.lt_succ_iff.1 j.isLt

private lemma coeff_curveCoordPoly {d : ℕ} (u : Fin (d + 1) → (ι → F)) (i : ι)
    (j : Fin (d + 1)) : (curveCoordPoly u i).coeff (j : ℕ) = u j i := by
  simp only [curveCoordPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single j]
  · simp only [↓reduceIte, mul_one]
  · intro b _ hbj
    have hne : (j : ℕ) ≠ (b : ℕ) := fun h => hbj (Fin.ext h.symm)
    simp only [hne, ↓reduceIte, mul_zero]
  · intro hmem; exact absurd (mem_univ j) hmem

private lemma natDegree_coeff_le_natDegree_swap (p : F[X][Y]) (t : ℕ) :
    (p.coeff t).natDegree ≤ (Bivariate.swap p).natDegree := by
  refine natDegree_le_iff_coeff_eq_zero.2 fun d hd => ?_
  rw [← Bivariate.coeff_coeff_swap]
  exact congrArg (fun q : F[X] => q.coeff t) (coeff_eq_zero_of_natDegree_lt hd)

private lemma natDegree_swap_le_iff (p : F[X][Y]) (m : ℕ) :
    (Bivariate.swap p).natDegree ≤ m ↔ ∀ t, (p.coeff t).natDegree ≤ m := by
  constructor
  · intro h t
    exact (natDegree_coeff_le_natDegree_swap p t).trans h
  · intro h
    refine natDegree_le_iff_coeff_eq_zero.2 fun d hd => ?_
    ext t
    rw [Bivariate.coeff_coeff_swap, coeff_zero]
    exact coeff_eq_zero_of_natDegree_lt ((h t).trans_lt hd)

private lemma natDegree_swap_mul {p q : F[X][Y]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (Bivariate.swap (p * q)).natDegree =
      (Bivariate.swap p).natDegree + (Bivariate.swap q).natDegree := by
  rw [map_mul, natDegree_mul]
  · exact (map_ne_zero_iff Bivariate.swap Bivariate.swap.injective).2 hp
  · exact (map_ne_zero_iff Bivariate.swap Bivariate.swap.injective).2 hq

private lemma degree_coeff_swap_lt {p : F[X][Y]} {k : ℕ} (hp : p.degree < k) (d : ℕ) :
    ((Bivariate.swap p).coeff d).degree < k := by
  rw [degree_lt_iff_coeff_zero]
  intro t ht
  rw [Bivariate.coeff_coeff_swap]
  have hpt : p.coeff t = 0 := coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp (Nat.cast_le.2 ht))
  rw [hpt, coeff_zero]

private lemma isCoprime_map_fractionRing_of_isRelPrime {f g : F[X][Y]} (hfg : IsRelPrime f g) :
    IsCoprime (f.map (algebraMap F[X] (FractionRing F[X])))
      (g.map (algebraMap F[X] (FractionRing F[X]))) := by
  classical
  let K := FractionRing F[X]
  let i : F[X] →+* K := algebraMap F[X] K
  set d : K[X] := EuclideanDomain.gcd (f.map i) (g.map i) with hd_def
  have hd_left : d ∣ f.map i := EuclideanDomain.gcd_dvd_left (f.map i) (g.map i)
  have hd_right : d ∣ g.map i := EuclideanDomain.gcd_dvd_right (f.map i) (g.map i)
  have hd_unit : IsUnit d := by
    by_cases hd0 : d = 0
    · have hf0 : f.map i = 0 := zero_dvd_iff.1 (hd0 ▸ hd_left)
      have hg0 : g.map i = 0 := zero_dvd_iff.1 (hd0 ▸ hd_right)
      have hinj : Function.Injective i := IsFractionRing.injective F[X] K
      have hf : f = 0 := map_injective i hinj (by simpa only [Polynomial.map_zero] using hf0)
      have hg : g = 0 := map_injective i hinj (by simpa only [Polynomial.map_zero] using hg0)
      have h0u : IsUnit (0 : F[X][Y]) := hfg (by rw [hf]) (by rw [hg])
      exact absurd h0u not_isUnit_zero
    · let d₁ : F[X][Y] := IsLocalization.integerNormalization (nonZeroDivisors F[X]) d
      let d₀ : F[X][Y] := d₁.primPart
      obtain ⟨c, hc0, hc⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors F[X]) d
      have hc_ne : i c ≠ 0 :=
        ((injective_iff_map_eq_zero i).1 (IsFractionRing.injective F[X] K) c).mt
          (nonZeroDivisors.ne_zero hc0)
      have hd_dvd : d₀.map i ∣ d := by
        refine ⟨C ((i c)⁻¹ * i d₁.content), ?_⟩
        have hmap : d₁.map i = C (i c) * d := by
          simpa only [Algebra.smul_def, algebraMap_apply] using hc
        have hprim : d₁.map i = C (i d₁.content) * d₀.map i := by
          conv_lhs => rw [d₁.eq_C_content_mul_primPart]
          rw [Polynomial.map_mul, Polynomial.map_C]
        have hmul : C (i c) * d = C (i d₁.content) * d₀.map i := hmap.symm.trans hprim
        calc
          d = C (i c)⁻¹ * (C (i c) * d) := by
            rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc_ne, C_1, one_mul]
          _ = C (i c)⁻¹ * (C (i d₁.content) * d₀.map i) := by rw [hmul]
          _ = d₀.map i * C ((i c)⁻¹ * i d₁.content) := by
            rw [C_mul, mul_comm (d₀.map i), mul_assoc]
      have hd₀_dvd_f : d₀ ∣ f :=
        d₁.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hd_dvd.trans hd_left)
      have hd₀_dvd_g : d₀ ∣ g :=
        d₁.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hd_dvd.trans hd_right)
      exact isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart hd0
        (hfg hd₀_dvd_f hd₀_dvd_g)
  obtain ⟨u, hu⟩ := hd_unit
  let uinv : K[X] := ↑(u⁻¹)
  refine ⟨uinv * EuclideanDomain.gcdA (f.map i) (g.map i),
    uinv * EuclideanDomain.gcdB (f.map i) (g.map i), ?_⟩
  have hbez : d = f.map i * EuclideanDomain.gcdA (f.map i) (g.map i) +
      g.map i * EuclideanDomain.gcdB (f.map i) (g.map i) :=
    EuclideanDomain.gcd_eq_gcd_ab (f.map i) (g.map i)
  have hu_inv : uinv * d = 1 := by
    rw [← hu]
    exact Units.inv_mul u
  calc
    uinv * EuclideanDomain.gcdA (f.map i) (g.map i) * f.map i +
        uinv * EuclideanDomain.gcdB (f.map i) (g.map i) * g.map i
      = uinv * (f.map i * EuclideanDomain.gcdA (f.map i) (g.map i) +
          g.map i * EuclideanDomain.gcdB (f.map i) (g.map i)) := by ring
    _ = uinv * d := by rw [← hbez]
    _ = 1 := hu_inv

private lemma resultant_ne_zero_of_isRelPrime {f g : F[X][Y]} {M : ℕ}
    (hfg : IsRelPrime f g) (hg0 : g ≠ 0) (hfM : f.natDegree ≤ M) :
    Polynomial.resultant f g M g.natDegree ≠ 0 := by
  let K := FractionRing F[X]
  let i : F[X] →+* K := algebraMap F[X] K
  have hinj : Function.Injective i := IsFractionRing.injective F[X] K
  have hcop : IsCoprime (f.map i) (g.map i) := isCoprime_map_fractionRing_of_isRelPrime hfg
  have hbase_K : Polynomial.resultant (f.map i) (g.map i) ≠ 0 :=
    Polynomial.resultant_ne_zero (f.map i) (g.map i) hcop
  have hf_deg : (f.map i).natDegree = f.natDegree := natDegree_map_eq_of_injective hinj _
  have hg_deg : (g.map i).natDegree = g.natDegree := natDegree_map_eq_of_injective hinj _
  have hbase : Polynomial.resultant f g f.natDegree g.natDegree ≠ 0 := by
    intro h0
    have h1 := congrArg i h0
    rw [map_zero, ← Polynomial.resultant_map_map, ← hf_deg, ← hg_deg] at h1
    exact hbase_K h1
  have hM : f.natDegree + (M - f.natDegree) = M := Nat.add_sub_of_le hfM
  rw [← hM, Polynomial.resultant_add_left_deg _ _ _ _ _ le_rfl]
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ ?_)) hbase
  · exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  · exact leadingCoeff_ne_zero.2 hg0

private lemma C_X_sub_C_dvd_of_map_evalRingHom_eq_zero {H : F[X][Y]} {w : F}
    (hH : H.map (evalRingHom w) = 0) : C (X - C w) ∣ H := by
  rw [C_dvd_iff_dvd_coeff]
  intro t
  rw [dvd_iff_isRoot, IsRoot.def]
  have ht := congrArg (fun p : F[X] => p.coeff t) hH
  simpa only [coeff_map, coeff_zero, coe_evalRingHom] using ht

private lemma X_sub_C_pow_dvd_resultant_of_map_eq_mul {f g : F[X][Y]} {M : ℕ} {w : F} {p : F[X]}
    (hpM : p.natDegree + g.natDegree ≤ M)
    (hmap : f.map (evalRingHom w) = g.map (evalRingHom w) * p) :
    (X - C w) ^ g.natDegree ∣ Polynomial.resultant f g M g.natDegree := by
  let pC : F[X][Y] := p.map C
  have hpC_deg : pC.natDegree ≤ p.natDegree := natDegree_map_le
  have hneg_deg : (-pC).natDegree + g.natDegree ≤ M := by
    rw [natDegree_neg]
    exact (Nat.add_le_add_right hpC_deg _).trans hpM
  let H : F[X][Y] := f + g * (-pC)
  have hH_map : H.map (evalRingHom w) = 0 := by
    have hpC_map : pC.map (evalRingHom w) = p := by
      rw [Polynomial.map_map]
      have hcomp : (evalRingHom w).comp C = RingHom.id F := by
        ext x
        simp only [RingHom.comp_apply, coe_evalRingHom, eval_C, RingHom.id_apply]
      rw [hcomp, Polynomial.map_id]
    simp only [H, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_neg, hpC_map, hmap,
      mul_neg, add_neg_cancel]
  obtain ⟨H', hH'⟩ := C_X_sub_C_dvd_of_map_evalRingHom_eq_zero hH_map
  have hres : Polynomial.resultant f g M g.natDegree =
      (X - C w) ^ g.natDegree * Polynomial.resultant H' g M g.natDegree := by
    calc
      Polynomial.resultant f g M g.natDegree
        = Polynomial.resultant H g M g.natDegree :=
          (Polynomial.resultant_add_mul_left f g (-pC) M g.natDegree hneg_deg le_rfl).symm
      _ = Polynomial.resultant (C (X - C w) * H') g M g.natDegree := by rw [hH']
      _ = (X - C w) ^ g.natDegree * Polynomial.resultant H' g M g.natDegree :=
          Polynomial.resultant_C_mul_left H' g M g.natDegree (X - C w)
  exact ⟨Polynomial.resultant H' g M g.natDegree, hres⟩

private lemma natDegree_resultant_le {f g : F[X][Y]} {M n a_T b_T : ℕ}
    (hf : ∀ t, (f.coeff t).natDegree ≤ a_T) (hg : ∀ t, (g.coeff t).natDegree ≤ b_T) :
    (Polynomial.resultant f g M n).natDegree ≤ M * b_T + n * a_T := by
  classical
  rw [Polynomial.resultant]
  let d : Fin (M + n) → ℕ := fun j => if j.val < M then b_T else a_T
  have hbound : ∀ i j, (f.sylvester g M n i j).natDegree ≤ d j := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      have hd : d (j.castAdd n) = b_T := by
        simp only [d, Fin.val_castAdd, j.isLt, ↓reduceIte]
      rw [hd, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hg _
      · simp only [natDegree_zero, Nat.zero_le]
    | right j =>
      have hd : d (j.natAdd M) = a_T := by
        simp only [d, Fin.val_natAdd, not_lt.2 (Nat.le_add_right M j.val), ↓reduceIte]
      rw [hd, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hf _
      · simp only [natDegree_zero, Nat.zero_le]
  refine (natDegree_det_le_sum (f.sylvester g M n) d hbound).trans_eq ?_
  rw [Fin.sum_univ_add]
  have h1 : ∑ j : Fin M, d (j.castAdd n) = M * b_T := by
    calc
      ∑ j : Fin M, d (j.castAdd n) = ∑ _j : Fin M, b_T :=
        Finset.sum_congr rfl fun j _ => by simp only [d, Fin.val_castAdd, j.isLt, ↓reduceIte]
      _ = M * b_T := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h2 : ∑ j : Fin n, d (j.natAdd M) = n * a_T := by
    calc
      ∑ j : Fin n, d (j.natAdd M) = ∑ _j : Fin n, a_T :=
        Finset.sum_congr rfl fun j _ => by
          simp only [d, Fin.val_natAdd, not_lt.2 (Nat.le_add_right M j.val), ↓reduceIte]
      _ = n * a_T := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h1, h2]

private lemma card_mul_natDegree_le_of_isRelPrime_resultant {f g : F[X][Y]} {M a_T b_T : ℕ}
    {W : Finset F} (hfg : IsRelPrime f g) (hg0 : g ≠ 0) (hfM : f.natDegree ≤ M)
    (hfT : ∀ t, (f.coeff t).natDegree ≤ a_T) (hgT : ∀ t, (g.coeff t).natDegree ≤ b_T)
    (hW : ∀ w ∈ W, ∃ p : F[X], p.natDegree + g.natDegree ≤ M ∧
      f.map (evalRingHom w) = g.map (evalRingHom w) * p) :
    g.natDegree * W.card ≤ g.natDegree * a_T + M * b_T := by
  let R : F[X] := Polynomial.resultant f g M g.natDegree
  have hR0 : R ≠ 0 := resultant_ne_zero_of_isRelPrime hfg hg0 hfM
  have hdvd_each : ∀ w ∈ W, (X - C w) ^ g.natDegree ∣ R := by
    intro w hw
    obtain ⟨p, hpM, hmap⟩ := hW w hw
    exact X_sub_C_pow_dvd_resultant_of_map_eq_mul hpM hmap
  have hpair : (W : Set F).Pairwise fun w₁ w₂ =>
      IsCoprime ((X - C w₁) ^ g.natDegree) ((X - C w₂) ^ g.natDegree) := fun _ _ _ _ hne =>
    (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hne).isUnit).pow
  have hprod_dvd : (∏ w ∈ W, (X - C w) ^ g.natDegree) ∣ R :=
    Finset.prod_dvd_of_coprime hpair hdvd_each
  have hprod_deg : (∏ w ∈ W, (X - C w) ^ g.natDegree).natDegree = g.natDegree * W.card := by
    have hmonic : ∀ w ∈ W, ((X - C w) ^ g.natDegree).Monic := fun w _ =>
      (monic_X_sub_C w).pow g.natDegree
    rw [natDegree_prod_of_monic W _ hmonic]
    calc
      ∑ w ∈ W, ((X - C w) ^ g.natDegree).natDegree = ∑ _w ∈ W, g.natDegree :=
        Finset.sum_congr rfl fun w _ => by
          rw [(monic_X_sub_C w).natDegree_pow, natDegree_X_sub_C, mul_one]
      _ = W.card * g.natDegree := by simp only [Finset.sum_const, smul_eq_mul]
      _ = g.natDegree * W.card := mul_comm _ _
  have hle1 : g.natDegree * W.card ≤ R.natDegree := by
    rw [← hprod_deg]
    exact natDegree_le_of_dvd hprod_dvd hR0
  have hle2 : R.natDegree ≤ M * b_T + g.natDegree * a_T := natDegree_resultant_le hfT hgT
  omega

/-! ### Linear algebra helper: invertible submatrix and Cramer kernel extraction -/

private lemma exists_det_ne_zero_submatrix_of_linearIndependent_cols {κ ι' : Type*}
    [Fintype κ] [DecidableEq κ] [Finite ι']
    {K : Type*} [Field K] (A : Matrix ι' κ K)
    (hli : LinearIndependent K fun j : κ => fun i : ι' => A i j) :
    ∃ ρ : κ → ι', (A.submatrix ρ id).det ≠ 0 := by
  classical
  have hspan : Submodule.span K (Set.range fun i : ι' => A i) = ⊤ := by
    by_contra hne
    have hlt : Submodule.span K (Set.range fun i : ι' => A i) < ⊤ := lt_top_iff_ne_top.2 hne
    obtain ⟨φ, hφ_ne, hφ_le⟩ :=
      Submodule.exists_le_ker_of_lt_top (Submodule.span K (Set.range fun i : ι' => A i)) hlt
    let v : κ → K := fun j => φ (Pi.single j 1)
    have hv_ne : v ≠ 0 := by
      intro hv0
      apply hφ_ne
      apply LinearMap.ext
      intro x
      have hx : x = ∑ j : κ, x j • Pi.single j (1 : K) := by
        ext j'
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        rw [Finset.sum_eq_single j']
        · simp only [↓reduceIte, mul_one]
        · intro b _ hbj; simp only [hbj.symm, ↓reduceIte, mul_zero]
        · intro hmem; exact absurd (Finset.mem_univ j') hmem
      rw [hx, map_sum, LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, show φ (Pi.single j 1) = 0 from congrFun hv0 j, smul_zero]
    have hmul : ∑ j : κ, v j • (fun i : ι' => A i j) = 0 := by
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hAi : A i = ∑ j : κ, A i j • Pi.single j (1 : K) := by
        ext j'
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        rw [Finset.sum_eq_single j']
        · simp only [↓reduceIte, mul_one]
        · intro b _ hbj; simp only [hbj.symm, ↓reduceIte, mul_zero]
        · intro hmem; exact absurd (Finset.mem_univ j') hmem
      have hzero : φ (A i) = 0 := hφ_le (Submodule.subset_span ⟨i, rfl⟩)
      rw [hAi, map_sum] at hzero
      calc
        ∑ j : κ, v j * A i j = ∑ j : κ, A i j * φ (Pi.single j 1) :=
          Finset.sum_congr rfl fun j _ => mul_comm _ _
        _ = 0 := by simpa only [map_smul, smul_eq_mul] using hzero
    have hcoeff := Fintype.linearIndependent_iff.1 hli v hmul
    exact hv_ne (funext hcoeff)
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range fun i : ι' => A i)
  rw [hspan] at hs_span
  have hs_fin : s.Finite := (Set.finite_range fun i : ι' => A i).subset hs_sub
  let _ : Fintype s := hs_fin.fintype
  let b : Module.Basis s K (κ → K) :=
    Module.Basis.mk hs_li (by rw [Subtype.range_coe_subtype]; exact le_of_eq hs_span.symm)
  have hcard : Fintype.card s = Fintype.card κ := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Module.finrank_pi] at h1
    exact h1.symm
  let e : κ ≃ s := Fintype.equivOfCardEq hcard.symm
  have hmem : ∀ j : κ, (e j : κ → K) ∈ Set.range (fun i : ι' => A i) := fun j => hs_sub (e j).2
  choose ρ hρ using hmem
  refine ⟨ρ, ?_⟩
  let B : Matrix κ κ K := A.submatrix ρ id
  have hrows : LinearIndependent K B.row := by
    have heq : B.row = fun j : κ => (e j : κ → K) := by
      ext j c
      exact congrFun (hρ j) c
    rw [heq]
    exact hs_li.comp e e.injective
  exact isUnit_iff_ne_zero.1
    ((Matrix.isUnit_iff_isUnit_det B).1 (Matrix.linearIndependent_row_iff_isUnit.1 hrows))

private lemma exists_cramer_kernel_vec {ι' : Type*} [Finite ι']
    {e k d : ℕ}
    (M : Matrix ι' (Fin (k + e) ⊕ Fin (e + 1)) F[X])
    (hdeg_l : ∀ i j, (M i (Sum.inl j)).natDegree = 0)
    (hdeg_r : ∀ i j, (M i (Sum.inr j)).natDegree ≤ d)
    (hdep : ¬ LinearIndependent (FractionRing F[X])
      fun j => fun i => algebraMap F[X] (FractionRing F[X]) (M i j)) :
    ∃ x : Fin (k + e) ⊕ Fin (e + 1) → F[X], x ≠ 0 ∧ M.mulVec x = 0 ∧
      (∀ j, (x (Sum.inl j)).natDegree ≤ d * (e + 1)) ∧
      (∀ j, (x (Sum.inr j)).natDegree ≤ d * e) := by
  classical
  let Col := Fin (k + e) ⊕ Fin (e + 1)
  let K := FractionRing F[X]
  let iK : F[X] →+* K := algebraMap F[X] K
  let MK : Matrix ι' Col K := M.map iK
  let indepSets : Finset (Finset Col) :=
    Finset.univ.filter fun C : Finset Col =>
      LinearIndependent K fun c : C => fun r : ι' => MK r c.1
  have hempty : (∅ : Finset Col) ∈ indepSets := by
    simp only [indepSets, mem_filter, mem_univ, true_and]
    exact linearIndependent_empty_type
  obtain ⟨C, hC_mem, hC_max⟩ := Finset.exists_max_image indepSets Finset.card ⟨∅, hempty⟩
  have hC_li : LinearIndependent K fun c : C => fun r : ι' => MK r c.1 :=
    (mem_filter.1 hC_mem).2
  have hC_ne_univ : C ≠ Finset.univ := by
    intro huniv
    apply hdep
    have hEq : (fun j : Col => fun r : ι' => iK (M r j)) =
        (fun c : C => fun r : ι' => MK r c.1) ∘
          fun j : Col => (⟨j, huniv.symm ▸ mem_univ j⟩ : C) := rfl
    rw [hEq]
    exact hC_li.comp _ fun a b hab => by simpa only [Subtype.mk.injEq] using hab
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Col, j₀ ∉ C := by
    by_contra hall
    push Not at hall
    exact hC_ne_univ (Finset.eq_univ_iff_forall.2 hall)
  have hspan_j₀ : (fun r : ι' => MK r j₀) ∈
      Submodule.span K (Set.range fun c : C => fun r : ι' => MK r c.1) := by
    by_contra hnot
    have hC_on : LinearIndepOn K (fun j r => MK r j) (C : Set Col) := hC_li
    have hnot' : (fun r => MK r j₀) ∉
        Submodule.span K ((fun j r => MK r j) '' (C : Set Col)) := by
      rwa [Set.image_eq_range]
    have hC'_li : LinearIndependent K fun c : (insert j₀ C : Finset Col) => fun r : ι' =>
        MK r c.1 := by
      have h := hC_on.insert hnot'
      rw [← Finset.coe_insert] at h
      exact h
    have hmem' : insert j₀ C ∈ indepSets := mem_filter.2 ⟨mem_univ _, hC'_li⟩
    have hle := hC_max (insert j₀ C) hmem'
    rw [card_insert_of_notMem hj₀] at hle
    omega
  rw [Submodule.mem_span_range_iff_exists_fun] at hspan_j₀
  obtain ⟨w, hw⟩ := hspan_j₀
  obtain ⟨ρ, hρ_det⟩ :=
    exists_det_ne_zero_submatrix_of_linearIndependent_cols (MK.submatrix id (fun c : C => c.1))
      hC_li
  let N : Matrix C C F[X] := M.submatrix ρ (fun c : C => c.1)
  let NK : Matrix C C K := N.map iK
  have hNK_eq : NK = (MK.submatrix id (fun c : C => c.1)).submatrix ρ id := by
    ext a b; rfl
  have hNK_det : NK.det ≠ 0 := hNK_eq ▸ hρ_det
  have hN_det : N.det ≠ 0 := by
    intro h0
    apply hNK_det
    rw [show NK.det = iK N.det from (RingHom.map_det iK N).symm, h0, map_zero]
  let v : C → F[X] := fun c => M (ρ c) j₀
  let x : Col → F[X] := fun j =>
    if j = j₀ then N.det
    else if hj : j ∈ C then -(N.cramer v ⟨j, hj⟩)
    else 0
  have hx_ne : x ≠ 0 := by
    intro hx0
    have := congrFun hx0 j₀
    simp only [x, ↓reduceIte, Pi.zero_apply] at this
    exact hN_det this
  have hcramer_eq : ∀ c : C, iK (N.cramer v c) = iK N.det * w c := by
    have hNK_w : NK.mulVec w = fun c => iK (v c) := by
      funext c
      have hrc := congrFun hw (ρ c)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hrc
      simp only [Matrix.mulVec, dotProduct, NK, Matrix.map_apply, N, Matrix.submatrix_apply, v]
      calc
        ∑ b : C, iK (M (ρ c) b.1) * w b = ∑ b : C, w b * MK (ρ c) b.1 :=
          Finset.sum_congr rfl fun b _ => mul_comm _ _
        _ = MK (ρ c) j₀ := hrc
    have hmul_eq : NK.mulVec (NK.cramer (fun c => iK (v c))) = NK.mulVec (NK.det • w) := by
      rw [Matrix.mulVec_cramer, Matrix.mulVec_smul, hNK_w]
    have hunit : IsUnit NK := (Matrix.isUnit_iff_isUnit_det NK).2 (isUnit_iff_ne_zero.2 hNK_det)
    obtain ⟨U, hU⟩ := hunit
    have hvec_eq : NK.cramer (fun c => iK (v c)) = NK.det • w := by
      have h1 := congrArg (↑(U⁻¹) : Matrix C C K).mulVec hmul_eq
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hU, Units.inv_mul, Matrix.one_mulVec,
        Matrix.one_mulVec, hU] at h1
      exact h1
    intro c
    have hc1 : iK (N.cramer v c) = NK.cramer (fun c' => iK (v c')) c := by
      rw [Matrix.cramer_apply, Matrix.cramer_apply]
      have hupd : (N.updateCol c v).map iK = NK.updateCol c (fun c' => iK (v c')) := by
        ext a b
        by_cases hbc : b = c
        · simp only [hbc, Matrix.map_apply, Matrix.updateCol_self]
        · simp only [Matrix.map_apply, Matrix.updateCol_ne hbc, NK]
      exact (RingHom.map_det iK (N.updateCol c v)).trans (congrArg Matrix.det hupd)
    rw [hc1, hvec_eq, Pi.smul_apply, smul_eq_mul,
      show NK.det = iK N.det from (RingHom.map_det iK N).symm]
  have hMx : M.mulVec x = 0 := by
    funext r
    apply IsFractionRing.injective F[X] K
    rw [Pi.zero_apply, map_zero]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    have hsplit : ∑ j : Col, iK (M r j) * iK (x j) =
        iK (M r j₀) * iK N.det + ∑ c : C, iK (M r c.1) * (-(iK N.det * w c)) := by
      rw [← Finset.add_sum_erase _ _ (mem_univ j₀)]
      have hleft : iK (M r j₀) * iK (x j₀) = iK (M r j₀) * iK N.det := by
        simp only [x, ↓reduceIte]
      rw [hleft]
      congr 1
      have hsub : C ⊆ Finset.univ.erase j₀ := fun c hc =>
        mem_erase.2 ⟨fun h => hj₀ (h ▸ hc), mem_univ c⟩
      rw [← Finset.sum_subset hsub]
      · rw [← Finset.sum_attach C]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hne : c.1 ≠ j₀ := fun h => hj₀ (h ▸ c.2)
        simp only [x, hne, ↓reduceIte, c.2, ↓reduceDIte, map_neg, hcramer_eq c]
      · intro j hj_erase hjC
        have hj : j ≠ j₀ := (mem_erase.1 hj_erase).1
        simp only [x, hj, ↓reduceIte, hjC, ↓reduceDIte, map_zero, mul_zero]
    rw [hsplit]
    have hrw := congrFun hw r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hrw
    calc
      iK (M r j₀) * iK N.det + ∑ c : C, iK (M r c.1) * -(iK N.det * w c)
        = iK N.det * (MK r j₀ - ∑ c : C, w c * MK r c.1) := by
          rw [mul_sub, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
          congr 1
          · exact mul_comm _ _
          · refine Finset.sum_congr rfl fun c _ => ?_
            simp only [MK, Matrix.map_apply]
            ring
      _ = iK N.det * (MK r j₀ - MK r j₀) := by rw [hrw]
      _ = 0 := by rw [sub_self, mul_zero]
  let colDeg : Col → ℕ := fun j => match j with
    | Sum.inl _ => 0
    | Sum.inr _ => d
  have hcolDeg : ∀ r j, (M r j).natDegree ≤ colDeg j := by
    intro r j
    cases j with
    | inl j => exact (hdeg_l r j).le
    | inr j => exact hdeg_r r j
  have hsum_subset : ∀ T : Finset Col, ∑ j ∈ T, colDeg j ≤ d * (e + 1) := by
    intro T
    calc
      ∑ j ∈ T, colDeg j ≤ ∑ j : Col, colDeg j :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      _ = (∑ _j : Fin (k + e), 0) + (∑ _j : Fin (e + 1), d) := by
        rw [Fintype.sum_sum_type]
      _ = d * (e + 1) := by
        simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, mul_comm]
  have hsum_missing_inr : ∀ (T : Finset Col) (j : Fin (e + 1)), Sum.inr j ∉ T →
      ∑ c ∈ T, colDeg c ≤ d * e := by
    intro T j hjT
    have hsub : T ⊆ Finset.univ.erase (Sum.inr j) := fun c hc =>
      mem_erase.2 ⟨fun h => hjT (h ▸ hc), mem_univ c⟩
    have hle : ∑ c ∈ T, colDeg c ≤ ∑ c ∈ Finset.univ.erase (Sum.inr j), colDeg c :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
    have htot : colDeg (Sum.inr j) + ∑ c ∈ Finset.univ.erase (Sum.inr j), colDeg c =
        d * (e + 1) := by
      rw [Finset.add_sum_erase _ _ (mem_univ (Sum.inr j)), Fintype.sum_sum_type]
      simp only [colDeg, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_comm]
    have hmul : d * (e + 1) = d + d * e := by ring
    change d + ∑ c ∈ Finset.univ.erase (Sum.inr j), colDeg c = d * (e + 1) at htot
    omega
  have hdeg_N : N.det.natDegree ≤ ∑ c ∈ C, colDeg c := by
    have h1 := natDegree_det_le_sum N (fun c : C => colDeg c.1) fun a b => hcolDeg (ρ a) b.1
    calc
      N.det.natDegree ≤ ∑ c : C, colDeg c.1 := h1
      _ = ∑ c ∈ C, colDeg c := Finset.sum_attach C colDeg
  have hdeg_cramer : ∀ c : C,
      (N.cramer v c).natDegree ≤ ∑ t ∈ insert j₀ (C.erase c.1), colDeg t := by
    intro c
    rw [Matrix.cramer_apply]
    let d' : C → ℕ := fun b => if b = c then colDeg j₀ else colDeg b.1
    have hM' : ∀ a b : C, ((N.updateCol c v) a b).natDegree ≤ d' b := by
      intro a b
      by_cases hbc : b = c
      · simp only [d', hbc, ↓reduceIte, Matrix.updateCol_self]
        exact hcolDeg (ρ a) j₀
      · simp only [d', hbc, ↓reduceIte, Matrix.updateCol_ne hbc]
        exact hcolDeg (ρ a) b.1
    refine (natDegree_det_le_sum (N.updateCol c v) d' hM').trans_eq ?_
    rw [← Finset.add_sum_erase _ _ (mem_univ c)]
    have h1 : d' c = colDeg j₀ := by simp only [d', ↓reduceIte]
    rw [h1, Finset.sum_insert (fun h => hj₀ (mem_erase.1 h).2)]
    congr 1
    calc
      ∑ b ∈ Finset.univ.erase c, d' b
        = ∑ b ∈ Finset.univ.erase c, colDeg b.1 :=
          Finset.sum_congr rfl fun b hb => by simp only [d', (mem_erase.1 hb).1, ↓reduceIte]
      _ = ∑ t ∈ C.erase c.1, colDeg t := by
          refine Finset.sum_bij (fun b _ => b.1) ?_ ?_ ?_ (fun _ _ => rfl)
          · intro b hb
            exact mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 (Subtype.ext h), b.2⟩
          · intro a _ b _ hab; exact Subtype.ext hab
          · intro t ht
            refine ⟨⟨t, (mem_erase.1 ht).2⟩, mem_erase.2 ⟨fun h => (mem_erase.1 ht).1
              (congrArg Subtype.val h), mem_univ _⟩, rfl⟩
  refine ⟨x, hx_ne, hMx, ?_, ?_⟩
  · intro j
    by_cases hj : Sum.inl j = j₀
    · simp only [x, hj, ↓reduceIte]
      exact hdeg_N.trans (hsum_subset C)
    · by_cases hmem : Sum.inl j ∈ C
      · simp only [x, hj, ↓reduceIte, hmem, ↓reduceDIte, natDegree_neg]
        exact (hdeg_cramer ⟨Sum.inl j, hmem⟩).trans (hsum_subset _)
      · simp only [x, hj, ↓reduceIte, hmem, ↓reduceDIte, natDegree_zero, Nat.zero_le]
  · intro j
    by_cases hj : Sum.inr j = j₀
    · simp only [x, hj, ↓reduceIte]
      exact hdeg_N.trans (hsum_missing_inr C j (hj.symm ▸ hj₀))
    · by_cases hmem : Sum.inr j ∈ C
      · simp only [x, hj, ↓reduceIte, hmem, ↓reduceDIte, natDegree_neg]
        have hnot : Sum.inr j ∉ insert j₀ (C.erase (Sum.inr j)) := by
          simp only [mem_insert, mem_erase, not_or, not_and]
          exact ⟨hj, fun h => absurd rfl h⟩
        exact (hdeg_cramer ⟨Sum.inr j, hmem⟩).trans (hsum_missing_inr _ j hnot)
      · simp only [x, hj, ↓reduceIte, hmem, ↓reduceDIte, natDegree_zero, Nat.zero_le]

/-! ### Stage 1: primitive bivariate Berlekamp–Welch interpolant -/

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
  let n := Fintype.card ι
  have hde_lt_S : d * (e + 1) < S.card := by
    have h1 : e + 1 < n := by omega
    exact (Nat.mul_lt_mul_of_pos_left h1 (by omega)).trans hS
  let Col := Fin (k + e) ⊕ Fin (e + 1)
  let M : Matrix ι Col F[X] := fun i j => match j with
    | Sum.inl t => C (α i ^ (t : ℕ))
    | Sum.inr t => -(curveCoordPoly u i * C (α i ^ (t : ℕ)))
  have hM_l : ∀ i j, (M i (Sum.inl j)).natDegree = 0 := fun i j => natDegree_C _
  have hM_r : ∀ i j, (M i (Sum.inr j)).natDegree ≤ d := by
    intro i j
    simp only [M, natDegree_neg]
    exact natDegree_mul_le.trans
      (by rw [natDegree_C, add_zero]; exact natDegree_curveCoordPoly_le u i)
  have hdep : ¬ LinearIndependent (FractionRing F[X])
      fun j => fun i => algebraMap F[X] (FractionRing F[X]) (M i j) := by
    intro hli
    obtain ⟨ρ, hρ_det⟩ :=
      exists_det_ne_zero_submatrix_of_linearIndependent_cols
        (M.map (algebraMap F[X] (FractionRing F[X]))) hli
    let N : Matrix Col Col F[X] := M.submatrix ρ id
    have hN_det : N.det ≠ 0 := by
      intro h0
      apply hρ_det
      have heq : (M.map (algebraMap F[X] (FractionRing F[X]))).submatrix ρ id =
          N.map (algebraMap F[X] (FractionRing F[X])) := by ext a b; rfl
      rw [heq]
      have hmap : (N.map (algebraMap F[X] (FractionRing F[X]))).det =
          algebraMap F[X] (FractionRing F[X]) N.det :=
        (RingHom.map_det (algebraMap F[X] (FractionRing F[X])) N).symm
      rw [hmap, h0, map_zero]
    have hN_deg : N.det.natDegree ≤ d * (e + 1) := by
      let colDeg : Col → ℕ := fun j => match j with | Sum.inl _ => 0 | Sum.inr _ => d
      have h1 := natDegree_det_le_sum N colDeg fun a b => by
        cases b with
        | inl j => exact (hM_l (ρ a) j).le
        | inr j => exact hM_r (ρ a) j
      refine h1.trans_eq ?_
      rw [Fintype.sum_sum_type]
      simp only [colDeg, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_comm]
    have hN_eval_zero : ∀ z ∈ S, N.det.eval z = 0 := by
      intro z hz
      obtain ⟨c, hcRS, hdist⟩ := hclose z hz
      obtain ⟨p, hp_deg, rfl⟩ := mem_reedSolomon.1 hcRS
      rw [hammingDist_comm] at hdist
      obtain ⟨E, Q, hsol⟩ := BerlekampWelch.exists_isSolution (α := α)
        (w := ∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) hp_deg hdist
      let y : Col → F := fun j => match j with
        | Sum.inl t => Q.coeff (t : ℕ)
        | Sum.inr t => E.coeff (t : ℕ)
      have hy_ne : y ≠ 0 := by
        intro hy0
        have h1 := congrFun hy0 (Sum.inr ⟨e, Nat.lt_succ_self e⟩)
        simp only [y, Pi.zero_apply] at h1
        rw [← hsol.natDegree_eq, ← leadingCoeff, hsol.monic.leadingCoeff] at h1
        exact one_ne_zero h1
      have hNy : (N.map (evalRingHom z)).mulVec y = 0 := by
        funext a
        rw [Pi.zero_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
        have hQsum : ∑ t : Fin (k + e),
            (N.map (evalRingHom z)) a (Sum.inl t) * y (Sum.inl t) = Q.eval (α (ρ a)) := by
          have hdegQ : Q.natDegree < k + e := by
            by_cases hQ0 : Q = 0
            · rw [hQ0, natDegree_zero]; omega
            · exact (natDegree_lt_iff_degree_lt hQ0).2 (by rw [add_comm]; exact hsol.degree_lt)
          rw [eval_eq_sum_range' hdegQ, ← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl fun t _ => ?_
          change eval z (C (α (ρ a) ^ (t : ℕ))) * Q.coeff (t : ℕ) =
            Q.coeff (t : ℕ) * α (ρ a) ^ (t : ℕ)
          rw [eval_C, mul_comm]
        have hEsum : ∑ t : Fin (e + 1),
            (N.map (evalRingHom z)) a (Sum.inr t) * y (Sum.inr t) =
            -((∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) (ρ a) * E.eval (α (ρ a))) := by
          have hdegE : E.natDegree < e + 1 := by rw [hsol.natDegree_eq]; exact Nat.lt_succ_self e
          rw [eval_eq_sum_range' hdegE, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum,
            ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun t _ => ?_
          change eval z (-(curveCoordPoly u (ρ a) * C (α (ρ a) ^ (t : ℕ)))) * E.coeff (t : ℕ) =
            -((∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) (ρ a) * (E.coeff (t : ℕ) * α (ρ a) ^ (t : ℕ)))
          rw [eval_neg, eval_mul, eval_C, eval_curveCoordPoly]
          ring
        rw [hQsum, hEsum, hsol.eval_eq (ρ a), add_neg_cancel]
      have hdet0 : (N.map (evalRingHom z)).det = 0 := by
        by_contra hnz
        have hunit := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hnz)
        obtain ⟨U, hU⟩ := hunit
        have hy0 : y = 0 := by
          have h1 := congrArg (↑(U⁻¹) : Matrix Col Col F).mulVec hNy
          rw [Matrix.mulVec_mulVec, ← hU, Units.inv_mul, Matrix.one_mulVec,
            Matrix.mulVec_zero] at h1
          exact h1
        exact hy_ne hy0
      have hmap : evalRingHom z N.det = (N.map (evalRingHom z)).det :=
        RingHom.map_det (evalRingHom z) N
      simpa only [coe_evalRingHom] using hmap.trans hdet0
    have hzero : N.det = 0 := by
      refine eq_zero_of_degree_lt_of_eval_finset_eq_zero S ?_ hN_eval_zero
      rw [degree_eq_natDegree hN_det, Nat.cast_lt]
      exact hN_deg.trans_lt hde_lt_S
    exact hN_det hzero
  obtain ⟨x, hx_ne, hMx, hx_deg_l, hx_deg_r⟩ := exists_cramer_kernel_vec M hM_l hM_r hdep
  let Araw : F[X][Y] := ∑ t : Fin (k + e), monomial (t : ℕ) (x (Sum.inl t))
  let Braw : F[X][Y] := ∑ t : Fin (e + 1), monomial (t : ℕ) (x (Sum.inr t))
  have hAraw_coeff : ∀ t, Araw.coeff t = if h : t < k + e then x (Sum.inl ⟨t, h⟩) else 0 := by
    intro t
    simp only [Araw, finsetSum_coeff, coeff_monomial_apply]
    by_cases ht : t < k + e
    · simp only [ht, ↓reduceDIte]
      rw [Finset.sum_eq_single ⟨t, ht⟩]
      · simp only [↓reduceIte]
      · intro b _ hbt
        have hne : (b : ℕ) ≠ t := fun h => hbt (Fin.ext h)
        simp only [hne, ↓reduceIte]
      · intro hmem; exact absurd (mem_univ _) hmem
    · simp only [ht, ↓reduceDIte]
      refine Finset.sum_eq_zero fun b _ => ?_
      have hne : (b : ℕ) ≠ t := fun h => ht (h ▸ b.isLt)
      simp only [hne, ↓reduceIte]
  have hBraw_coeff : ∀ t, Braw.coeff t = if h : t < e + 1 then x (Sum.inr ⟨t, h⟩) else 0 := by
    intro t
    simp only [Braw, finsetSum_coeff, coeff_monomial_apply]
    by_cases ht : t < e + 1
    · simp only [ht, ↓reduceDIte]
      rw [Finset.sum_eq_single ⟨t, ht⟩]
      · simp only [↓reduceIte]
      · intro b _ hbt
        have hne : (b : ℕ) ≠ t := fun h => hbt (Fin.ext h)
        simp only [hne, ↓reduceIte]
      · intro hmem; exact absurd (mem_univ _) hmem
    · simp only [ht, ↓reduceDIte]
      refine Finset.sum_eq_zero fun b _ => ?_
      have hne : (b : ℕ) ≠ t := fun h => ht (h ▸ b.isLt)
      simp only [hne, ↓reduceIte]
  have hAraw_deg : Araw.degree < (k + e : ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro t ht
    simp only [hAraw_coeff, not_lt.2 ht, ↓reduceDIte]
  have hBraw_deg : Braw.natDegree ≤ e := by
    refine natDegree_le_iff_coeff_eq_zero.2 fun t ht => ?_
    have hnt : ¬ t < e + 1 := by omega
    simp only [hBraw_coeff, hnt, ↓reduceDIte]
  have hAraw_degZ : (Bivariate.swap Araw).natDegree ≤ d * (e + 1) := by
    rw [natDegree_swap_le_iff]
    intro t
    rw [hAraw_coeff]
    split_ifs with ht
    · exact hx_deg_l ⟨t, ht⟩
    · simp only [natDegree_zero, Nat.zero_le]
  have hBraw_degZ : (Bivariate.swap Braw).natDegree ≤ d * e := by
    rw [natDegree_swap_le_iff]
    intro t
    rw [hBraw_coeff]
    split_ifs with ht
    · exact hx_deg_r ⟨t, ht⟩
    · simp only [natDegree_zero, Nat.zero_le]
  have hraw_eval : ∀ i : ι, Araw.eval (C (α i)) = curveCoordPoly u i * Braw.eval (C (α i)) := by
    intro i
    have hi := congrFun hMx i
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, M, Pi.zero_apply] at hi
    have hAeval : Araw.eval (C (α i)) = ∑ t : Fin (k + e), C (α i ^ (t : ℕ)) * x (Sum.inl t) := by
      simp only [Araw, eval_finsetSum, eval_monomial, ← C_pow]
      exact Finset.sum_congr rfl fun t _ => mul_comm _ _
    have hBeval : curveCoordPoly u i * Braw.eval (C (α i)) =
        ∑ t : Fin (e + 1), curveCoordPoly u i * C (α i ^ (t : ℕ)) * x (Sum.inr t) := by
      simp only [Braw, eval_finsetSum, eval_monomial, ← C_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    rw [hAeval, hBeval]
    have hneg : ∑ t : Fin (e + 1), -(curveCoordPoly u i * C (α i ^ (t : ℕ))) * x (Sum.inr t) =
        -(∑ t : Fin (e + 1), curveCoordPoly u i * C (α i ^ (t : ℕ)) * x (Sum.inr t)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun t _ => neg_mul _ _
    rw [hneg] at hi
    exact eq_of_sub_eq_zero (by rwa [sub_eq_add_neg])
  have hBraw_ne : Braw ≠ 0 := by
    intro hB0
    have hA0 : Araw = 0 := by
      refine eq_zero_of_degree_lt_of_eval_finset_eq_zero
        (Finset.univ.image (fun i => C (α i))) ?_ ?_
      · have hinjC : Function.Injective (fun i : ι => (C (α i) : F[X])) :=
          C_injective.comp hα
        rw [card_image_of_injective _ hinjC, card_univ]
        exact lt_of_lt_of_le hAraw_deg (Nat.cast_le.2 (by omega))
      · intro y hy
        obtain ⟨i, _, rfl⟩ := mem_image.1 hy
        rw [hraw_eval i, hB0, eval_zero, mul_zero]
    apply hx_ne
    funext j
    cases j with
    | inl t =>
      have h1 := hAraw_coeff t.1
      simp only [hA0, coeff_zero, t.isLt, ↓reduceDIte] at h1
      exact h1.symm
    | inr t =>
      have h1 := hBraw_coeff t.1
      simp only [hB0, coeff_zero, t.isLt, ↓reduceDIte] at h1
      exact h1.symm
  let h : F[X] := Braw.content
  have hh0 : h ≠ 0 := content_eq_zero_iff.not.2 hBraw_ne
  let B : F[X][Y] := Braw.primPart
  have hB_prim : B.IsPrimitive := Braw.isPrimitive_primPart
  have hB_ne : B ≠ 0 := hB_prim.ne_zero
  have hBraw_eq : Braw = C h * B := Braw.eq_C_content_mul_primPart
  obtain ⟨J, -, hJ_card⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (n := k + e) (by rw [card_univ]; omega)
  have hJ_dvd : ∀ i ∈ J, h ∣ Araw.eval (C (α i)) := fun i _ => by
    rw [hraw_eval i, hBraw_eq, eval_mul, eval_C]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  let qJ : ι → F[X] := fun i => if hi : i ∈ J then (hJ_dvd i hi).choose else 0
  have hqJ : ∀ i ∈ J, Araw.eval (C (α i)) = h * qJ i := fun i hi => by
    simp only [qJ, hi, ↓reduceDIte]
    exact (hJ_dvd i hi).choose_spec
  let A : F[X][Y] := ∑ j ∈ J, C (qJ j) * (Lagrange.basis J α j).map C
  have hA_deg : A.degree < (k + e : ℕ) := by
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro j hj
    refine (degree_mul_le _ _).trans_lt ?_
    refine (add_le_add degree_C_le degree_map_le).trans_lt ?_
    rw [zero_add, Lagrange.degree_basis (hα.injOn) hj, hJ_card]
    exact Nat.cast_lt.2 (by omega)
  have hAraw_eq : Araw = C h * A := by
    refine sub_eq_zero.1 (eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (J.image (fun i => C (α i))) ?_ ?_)
    · have hinjC : Function.Injective (fun i : ι => (C (α i) : F[X])) := C_injective.comp hα
      rw [card_image_of_injective _ hinjC, hJ_card]
      refine (degree_sub_le _ _).trans_lt (max_lt hAraw_deg ?_)
      refine (degree_mul_le _ _).trans_lt ?_
      exact (add_le_add degree_C_le le_rfl).trans_lt (by rwa [zero_add])
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
      rw [eval_sub, eval_mul, eval_C, hqJ i hi]
      have hAeval : A.eval (C (α i)) = qJ i := by
        simp only [A, eval_finsetSum, eval_mul, eval_C, eval_map_apply]
        rw [Finset.sum_eq_single i]
        · rw [Lagrange.eval_basis_self (hα.injOn) hi, C_1, mul_one]
        · intro j _ hji
          rw [Lagrange.eval_basis_of_ne hji hi, C_0, mul_zero]
        · intro hni; exact absurd hi hni
      rw [hAeval, sub_self]
  have hB_deg : B.natDegree ≤ e := by
    rwa [← natDegree_primPart Braw] at hBraw_deg
  have hAB_eval : ∀ i : ι, A.eval (C (α i)) = curveCoordPoly u i * B.eval (C (α i)) := by
    intro i
    have h1 := hraw_eval i
    rw [hAraw_eq, hBraw_eq, eval_mul, eval_mul, eval_C] at h1
    exact mul_left_cancel₀ hh0 (by simpa only [mul_left_comm] using h1)
  have hA_degZ : (Bivariate.swap A).natDegree ≤ d * (e + 1) := by
    by_cases hA0 : A = 0
    · simp only [hA0, map_zero, natDegree_zero, Nat.zero_le]
    · have h1 := natDegree_swap_mul (C_ne_zero.2 hh0) hA0
      rw [← hAraw_eq] at h1
      omega
  have hB_degZ : (Bivariate.swap B).natDegree ≤ d * e := by
    have h1 := natDegree_swap_mul (C_ne_zero.2 hh0) hB_ne
    rw [← hBraw_eq] at h1
    omega
  exact ⟨A, B, hB_prim, hA_deg, hB_deg, hA_degZ, hB_degZ, hAB_eval⟩

/-! ### Stage 2: symmetric Sylvester resultant elimination forces `B ∣ A` -/

private lemma resultant_degree_collapse {n k e d aX bX cX aZ bZ sCard iCard : ℕ}
    (he : 2 * e + k ≤ n) (he1 : 1 ≤ e) (hk1 : 1 ≤ k)
    (hS : d * n < sCard) (hbcX : bX + cX ≤ e) (hI : n - cX ≤ iCard)
    (haX : aX ≤ k - 1 + bX) (haZ : aZ ≤ d + bZ)
    (hresX : bX * sCard ≤ bX * aZ + (k - 1 + bX) * bZ)
    (hresZ : bZ * iCard ≤ bZ * aX + (d + bZ) * bX) :
    bX = 0 ∧ bZ = 0 := by
  have hbZ_le : bZ ≤ d * bX := by
    have h1 : bZ * (n - cX) ≤ bZ * iCard := Nat.mul_le_mul_left bZ hI
    have h2 : bZ * aX ≤ bZ * (k - 1 + bX) := Nat.mul_le_mul_left bZ haX
    have h3 : bZ * aX + (d + bZ) * bX ≤ d * bX + (k - 1 + 2 * bX) * bZ := by nlinarith
    have h4 : k - 1 + 2 * bX ≤ n - cX - 1 := by omega
    have h5 : bZ * (n - cX) ≤ d * bX + (n - cX - 1) * bZ :=
      h1.trans (hresZ.trans (h3.trans (Nat.add_le_add_left (Nat.mul_le_mul_right bZ h4) _)))
    have h6 : 1 ≤ n - cX := by omega
    have h7 : bZ * (n - cX) = (n - cX - 1) * bZ + bZ := by
      zify [h6]; ring
    omega
  have hbX_zero : bX = 0 := by
    by_contra hbX_ne
    have hbX_pos : 1 ≤ bX := Nat.pos_of_ne_zero hbX_ne
    have h1 : bX * aZ ≤ bX * (d + bZ) := Nat.mul_le_mul_left bX haZ
    have h2 : bX * aZ + (k - 1 + bX) * bZ ≤ d * bX + (k - 1 + 2 * bX) * bZ := by nlinarith
    have h3 : k - 1 + 2 * bX ≤ n - 1 := by omega
    have h4 : bX * sCard ≤ d * bX + (n - 1) * (d * bX) :=
      hresX.trans (h2.trans (Nat.add_le_add_left
        ((Nat.mul_le_mul_right bZ h3).trans (Nat.mul_le_mul_left (n - 1) hbZ_le)) _))
    have h5 : d * bX + (n - 1) * (d * bX) = bX * (d * n) := by
      have hn1 : 1 ≤ n := by omega
      zify [hn1]; ring
    rw [h5] at h4
    have h6 : sCard ≤ d * n := Nat.le_of_mul_le_mul_left h4 hbX_pos
    omega
  rw [hbX_zero, mul_zero] at hbZ_le
  exact ⟨hbX_zero, by omega⟩

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
  let n := Fintype.card ι
  have hB_ne : B ≠ 0 := hB_prim.ne_zero
  have hde_lt_S : d * (e + 1) < S.card := by
    have h1 : e + 1 < n := by omega
    exact (Nat.mul_lt_mul_of_pos_left h1 (by omega)).trans hS
  have hB_map_ne : ∀ z : F, B.map (evalRingHom z) ≠ 0 := by
    intro z h0
    obtain ⟨B', hB'⟩ := C_X_sub_C_dvd_of_map_evalRingHom_eq_zero h0
    have hunit : IsUnit (X - C z) :=
      (isPrimitive_iff_isUnit_of_C_dvd.1 hB_prim) (X - C z) ⟨B', hB'⟩
    have hdeg0 := natDegree_eq_zero_of_isUnit hunit
    rw [natDegree_X_sub_C] at hdeg0
    exact one_ne_zero hdeg0
  set g : F[X][Y] := gcd A B with hg_def
  obtain ⟨A₀, hA_eq⟩ : g ∣ A := gcd_dvd_left A B
  obtain ⟨B₀, hB_eq⟩ : g ∣ B := gcd_dvd_right A B
  have hg_ne : g ≠ 0 := fun h0 => hB_ne (by rw [hB_eq, h0, zero_mul])
  have hA₀_ne : A₀ ≠ 0 := fun h0 => hA0 (by rw [hA_eq, h0, mul_zero])
  have hB₀_ne : B₀ ≠ 0 := fun h0 => hB_ne (by rw [hB_eq, h0, mul_zero])
  have hrel : IsRelPrime A₀ B₀ := by
    intro r hrA hrB
    have hdvd : g * r ∣ g := by
      have h1 : g * r ∣ A := by rw [hA_eq]; exact mul_dvd_mul_left g hrA
      have h2 : g * r ∣ B := by rw [hB_eq]; exact mul_dvd_mul_left g hrB
      exact dvd_gcd h1 h2
    obtain ⟨s, hs⟩ := hdvd
    have hmul : r * s = 1 := mul_left_cancel₀ hg_ne (by rw [← mul_assoc, ← hs, mul_one])
    exact isUnit_iff_exists_inv.2 ⟨s, hmul⟩
  let aX := A₀.natDegree
  let bX := B₀.natDegree
  let cX := g.natDegree
  let aZ := (Bivariate.swap A₀).natDegree
  let bZ := (Bivariate.swap B₀).natDegree
  have hbcX : bX + cX ≤ e := by
    have h1 : B.natDegree = cX + bX := by rw [hB_eq, natDegree_mul hg_ne hB₀_ne]
    omega
  have haZ_raw : aZ ≤ d * (e + 1) := by
    have h1 := natDegree_swap_mul hg_ne hA₀_ne
    rw [← hA_eq] at h1
    omega
  have hslice₀ : ∀ z ∈ S, ∃ Pz : F[X], Pz.degree < k ∧
      A₀.map (evalRingHom z) = B₀.map (evalRingHom z) * Pz := by
    intro z hz
    obtain ⟨Pz, hPz_deg, hABz⟩ := hslice z hz
    have hgz_ne : g.map (evalRingHom z) ≠ 0 := by
      intro h0
      apply hB_map_ne z
      rw [hB_eq, Polynomial.map_mul, h0, zero_mul]
    rw [hA_eq, hB_eq, Polynomial.map_mul, Polynomial.map_mul] at hABz
    have heq : A₀.map (evalRingHom z) = Pz * B₀.map (evalRingHom z) :=
      mul_left_cancel₀ hgz_ne (by simpa only [mul_left_comm] using hABz)
    exact ⟨Pz, hPz_deg, heq.trans (mul_comm _ _)⟩
  have haX_le : aX ≤ k - 1 + bX := by
    refine natDegree_le_iff_coeff_eq_zero.2 fun t ht => ?_
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero S ?_ ?_
    · by_cases hct0 : A₀.coeff t = 0
      · rw [hct0, degree_zero]; exact WithBot.bot_lt_coe _
      · rw [degree_eq_natDegree hct0, Nat.cast_lt]
        exact (natDegree_coeff_le_natDegree_swap A₀ t).trans_lt (haZ_raw.trans_lt hde_lt_S)
    · intro z hz
      obtain ⟨Pz, hPz_deg, hmap⟩ := hslice₀ z hz
      have hcoeff : (A₀.coeff t).eval z = (B₀.map (evalRingHom z) * Pz).coeff t := by
        have := congrArg (fun q : F[X] => q.coeff t) hmap
        simpa only [coeff_map, coe_evalRingHom] using this
      rw [hcoeff]
      refine coeff_eq_zero_of_natDegree_lt ?_
      have hPz_le : Pz.natDegree ≤ k - 1 := by
        by_cases hPz0 : Pz = 0
        · rw [hPz0, natDegree_zero]; exact Nat.zero_le _
        · have := (natDegree_lt_iff_degree_lt hPz0).2 hPz_deg; omega
      have hB₀z_le : (B₀.map (evalRingHom z)).natDegree ≤ bX := natDegree_map_le
      exact (natDegree_mul_le.trans (Nat.add_le_add hB₀z_le hPz_le)).trans_lt (by omega)
  let I : Finset ι := Finset.univ.filter fun i => g.eval (C (α i)) ≠ 0
  have hI_card : n - cX ≤ I.card :=
    card_filter_eval_ne_zero_ge (C_injective.comp hα) hg_ne
  have hI_eval : ∀ i ∈ I, A₀.eval (C (α i)) = B₀.eval (C (α i)) * wPoly i := by
    intro i hi
    have hgi : g.eval (C (α i)) ≠ 0 := (mem_filter.1 hi).2
    have h1 := hAB_eval i
    rw [hA_eq, hB_eq, eval_mul, eval_mul] at h1
    have h2 : A₀.eval (C (α i)) = wPoly i * B₀.eval (C (α i)) :=
      mul_left_cancel₀ hgi (by simpa only [mul_left_comm] using h1)
    exact h2.trans (mul_comm _ _)
  have haZ_le : aZ ≤ d + bZ := by
    refine natDegree_le_iff_coeff_eq_zero.2 fun t ht => ?_
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero (I.image α) ?_ ?_
    · rw [card_image_of_injective _ hα]
      by_cases hct0 : (Bivariate.swap A₀).coeff t = 0
      · rw [hct0, degree_zero]; exact WithBot.bot_lt_coe _
      · rw [degree_eq_natDegree hct0, Nat.cast_lt]
        have hdeg_le : ((Bivariate.swap A₀).coeff t).natDegree ≤ aX := by
          have := natDegree_coeff_le_natDegree_swap (Bivariate.swap A₀) t
          rwa [Bivariate.swap_swap_apply] at this
        omega
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      have hmap : (Bivariate.swap A₀).map (evalRingHom (α i)) =
          (Bivariate.swap B₀).map (evalRingHom (α i)) * wPoly i := by
        rw [← Bivariate.eval_C_eq_map_swap, ← Bivariate.eval_C_eq_map_swap]
        exact hI_eval i hi
      have hcoeff : ((Bivariate.swap A₀).coeff t).eval (α i) =
          ((Bivariate.swap B₀).map (evalRingHom (α i)) * wPoly i).coeff t := by
        have := congrArg (fun q : F[X] => q.coeff t) hmap
        simpa only [coeff_map, coe_evalRingHom] using this
      rw [hcoeff]
      refine coeff_eq_zero_of_natDegree_lt ?_
      have h1 : ((Bivariate.swap B₀).map (evalRingHom (α i))).natDegree ≤ bZ := natDegree_map_le
      exact (natDegree_mul_le.trans (Nat.add_le_add h1 (hwPoly_deg i))).trans_lt (by omega)
  have hres_X : bX * S.card ≤ bX * aZ + (k - 1 + bX) * bZ := by
    refine card_mul_natDegree_le_of_isRelPrime_resultant hrel hB₀_ne haX_le
      (fun t => natDegree_coeff_le_natDegree_swap A₀ t)
      (fun t => natDegree_coeff_le_natDegree_swap B₀ t) ?_
    intro z hz
    obtain ⟨Pz, hPz_deg, hmap⟩ := hslice₀ z hz
    refine ⟨Pz, ?_, hmap⟩
    by_cases hPz0 : Pz = 0
    · rw [hPz0, natDegree_zero, zero_add]; exact Nat.le_add_left _ _
    · have := (natDegree_lt_iff_degree_lt hPz0).2 hPz_deg; omega
  have hres_Z : bZ * I.card ≤ bZ * aX + (d + bZ) * bX := by
    have hrel_swap : IsRelPrime (Bivariate.swap A₀) (Bivariate.swap B₀) := by
      intro r hrA hrB
      have h1 : Bivariate.swap r ∣ A₀ := by
        rw [← Bivariate.swap_swap_apply A₀]
        exact map_dvd Bivariate.swap hrA
      have h2 : Bivariate.swap r ∣ B₀ := by
        rw [← Bivariate.swap_swap_apply B₀]
        exact map_dvd Bivariate.swap hrB
      have hu := hrel h1 h2
      rw [← Bivariate.swap_swap_apply r]
      exact hu.map Bivariate.swap
    have hB₀s_ne : Bivariate.swap B₀ ≠ 0 :=
      (map_ne_zero_iff Bivariate.swap Bivariate.swap.injective).2 hB₀_ne
    have h1 := card_mul_natDegree_le_of_isRelPrime_resultant (W := I.image α)
      hrel_swap hB₀s_ne haZ_le
      (fun t => by
        have := natDegree_coeff_le_natDegree_swap (Bivariate.swap A₀) t
        rwa [Bivariate.swap_swap_apply] at this)
      (fun t => by
        have := natDegree_coeff_le_natDegree_swap (Bivariate.swap B₀) t
        rwa [Bivariate.swap_swap_apply] at this)
      (fun x hx => by
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
        refine ⟨wPoly i, Nat.add_le_add_right (hwPoly_deg i) bZ, ?_⟩
        rw [← Bivariate.eval_C_eq_map_swap, ← Bivariate.eval_C_eq_map_swap]
        exact hI_eval i hi)
    rwa [card_image_of_injective _ hα] at h1
  obtain ⟨hbX_zero, hbZ_zero⟩ :=
    resultant_degree_collapse he he1 hk1 hS hbcX hI_card haX_le haZ_le hres_X hres_Z
  have hB₀_eq_CC : B₀ = C (C ((B₀.coeff 0).coeff 0)) := by
    have h1 : B₀ = C (B₀.coeff 0) := eq_C_of_natDegree_eq_zero hbX_zero
    have h2 : (B₀.coeff 0).natDegree = 0 :=
      Nat.eq_zero_of_le_zero ((natDegree_coeff_le_natDegree_swap B₀ 0).trans_eq hbZ_zero)
    have h3 : B₀.coeff 0 = C ((B₀.coeff 0).coeff 0) := eq_C_of_natDegree_eq_zero h2
    conv_lhs => rw [h1, h3]
  let c₀ : F := (B₀.coeff 0).coeff 0
  have hc₀_ne : c₀ ≠ 0 := by
    intro h0
    apply hB₀_ne
    rw [hB₀_eq_CC, show (B₀.coeff 0).coeff 0 = 0 from h0, C_0, C_0]
  let P : F[X][Y] := C (C c₀⁻¹) * A₀
  have hA_eq_PB : A = P * B := by
    calc
      A = g * A₀ := hA_eq
      _ = g * (C (C c₀⁻¹) * C (C c₀) * A₀) := by
        rw [← C_mul, ← C_mul, inv_mul_cancel₀ hc₀_ne, C_1, C_1, one_mul]
      _ = C (C c₀⁻¹) * A₀ * (g * C (C c₀)) := by ring
      _ = P * B := by rw [hB_eq, hB₀_eq_CC]
  have hP_deg : P.degree < k := by
    have hP_nat : P.natDegree ≤ k - 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [hbX_zero, add_zero] at haX_le
      exact haX_le
    by_cases hP0 : P = 0
    · rw [hP0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree hP0, Nat.cast_lt]; omega
  exact ⟨P, hP_deg, hA_eq_PB⟩

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
  let n := Fintype.card ι
  obtain ⟨A, B, hB_prim, hA_deg, hB_deg, hA_degZ, _, hAB_eval⟩ :=
    exists_primitive_bivariate_solution hα he hd he1 hk1 u S hS hclose
  have hB_ne : B ≠ 0 := hB_prim.ne_zero
  let D' : Finset ι := Finset.univ.filter fun i => B.eval (C (α i)) ≠ 0
  have hD'_card : n - e ≤ D'.card :=
    (Nat.sub_le_sub_left hB_deg n).trans
      (card_filter_eval_ne_zero_ge (C_injective.comp hα) hB_ne)
  by_cases hA0 : A = 0
  · refine ⟨D', hD'_card, fun _ => 0, fun _ => Submodule.zero_mem _, fun i hi j => ?_⟩
    have hBi : B.eval (C (α i)) ≠ 0 := (mem_filter.1 hi).2
    have hw0 : curveCoordPoly u i = 0 := by
      have h1 := hAB_eval i
      rw [hA0, eval_zero] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_right hBi
    rw [← coeff_curveCoordPoly u i j, hw0, coeff_zero]
    rfl
  have hslice : ∀ z ∈ S, ∃ Pz : F[X], Pz.degree < k ∧
      A.map (evalRingHom z) = Pz * B.map (evalRingHom z) := by
    intro z hz
    obtain ⟨c, hcRS, hdist⟩ := hclose z hz
    obtain ⟨Pz, hPz_deg, rfl⟩ := mem_reedSolomon.1 hcRS
    refine ⟨Pz, hPz_deg, ?_⟩
    let Az := A.map (evalRingHom z)
    let Bz := B.map (evalRingHom z)
    let good : Finset ι := Finset.univ.filter fun i =>
      (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = Pz.eval (α i)
    have hgood_card : good.card + hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j)
        (fun i => Pz.eval (α i)) = n := card_filter_eq_add_hammingDist _ _
    refine sub_eq_zero.1 (eq_zero_of_degree_lt_of_eval_finset_eq_zero (good.image α) ?_ ?_)
    · rw [card_image_of_injective _ hα]
      have hAz_deg : Az.degree < (k + e : ℕ) := degree_map_le.trans_lt hA_deg
      have hPzBz_deg : (Pz * Bz).degree < (k + e : ℕ) := by
        by_cases hPz0 : Pz = 0
        · rw [hPz0, zero_mul, degree_zero]; exact WithBot.bot_lt_coe _
        · by_cases hBz0 : Bz = 0
          · rw [hBz0, mul_zero, degree_zero]; exact WithBot.bot_lt_coe _
          · have hPz_nat : Pz.natDegree < k := (natDegree_lt_iff_degree_lt hPz0).2 hPz_deg
            have hBz_nat : Bz.natDegree ≤ e := natDegree_map_le.trans hB_deg
            refine (degree_mul_le _ _).trans_lt ?_
            rw [degree_eq_natDegree hPz0, degree_eq_natDegree hBz0, ← Nat.cast_add, Nat.cast_lt]
            omega
      refine (degree_sub_le _ _).trans_lt ((max_lt hAz_deg hPzBz_deg).trans_le ?_)
      exact Nat.cast_le.2 (by omega)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      rw [eval_sub, eval_mul]
      have hAz_eval : Az.eval (α i) = (A.eval (C (α i))).eval z := by
        rw [Polynomial.map_evalRingHom_eval, Polynomial.evalEval]
      have hBz_eval : Bz.eval (α i) = (B.eval (C (α i))).eval z := by
        rw [Polynomial.map_evalRingHom_eval, Polynomial.evalEval]
      rw [hAz_eval, hBz_eval, hAB_eval i, eval_mul, eval_curveCoordPoly, (mem_filter.1 hi).2,
        sub_self]
  obtain ⟨P, hP_deg, hA_eq_PB⟩ :=
    exists_quotient_of_bivariate_solution hα he hd he1 hk1 (curveCoordPoly u)
      (natDegree_curveCoordPoly_le u) S hS hA0 hB_prim hB_deg hA_degZ hAB_eval hslice
  let v : Fin (d + 1) → (ι → F) := fun j i => ((Bivariate.swap P).coeff (j : ℕ)).eval (α i)
  refine ⟨D', hD'_card, v, fun j => eval_mem_reedSolomon α (degree_coeff_swap_lt hP_deg j), ?_⟩
  intro i hi j
  have hBi : B.eval (C (α i)) ≠ 0 := (mem_filter.1 hi).2
  have hPi : P.eval (C (α i)) = curveCoordPoly u i := by
    have h1 := hAB_eval i
    rw [hA_eq_PB, eval_mul] at h1
    exact mul_right_cancel₀ hBi h1
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
      (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j) i := by
    intro i hi
    refine mem_filter.2 ⟨mem_univ i, ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [hagree i hi j]
  have hle := card_le_card hsub
  have htot := card_filter_eq_add_hammingDist
    (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j)
  omega

/-- If two words `u₀, u₁` agree with `v₀, v₁` on a shared subset `D'` of size at least `|ι| - e`,
then `u₀ + z • u₁` is within Hamming distance `e` of `v₀ + z • v₁` for every scalar `z : F`. -/
theorem hammingDist_add_smul_le_of_eq_on {e : ℕ} {D' : Finset ι}
    {u₀ u₁ v₀ v₁ : ι → F} (hD' : Fintype.card ι - e ≤ D'.card)
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i) (z : F) :
    hammingDist (u₀ + z • u₁) (v₀ + z • v₁) ≤ e := by
  classical
  have hsub : D' ⊆ Finset.univ.filter fun i => (u₀ + z • u₁) i = (v₀ + z • v₁) i := by
    intro i hi
    refine mem_filter.2 ⟨mem_univ i, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [(hagree i hi).1, (hagree i hi).2]
  have hle := card_le_card hsub
  have htot := card_filter_eq_add_hammingDist (u₀ + z • u₁) (v₀ + z • v₁)
  omega

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
    let D' : Finset ι := Finset.univ.filter fun i => u 0 i = c i
    have hD' : Fintype.card ι - e ≤ D'.card := by
      have htot := card_filter_eq_add_hammingDist (u 0) c
      change D'.card + hammingDist (u 0) c = Fintype.card ι at htot
      omega
    refine ⟨D', hD', fun _ => c, fun _ => hcRS, fun i hi j => ?_⟩
    rw [Fin.eq_zero j]
    exact (mem_filter.1 hi).2
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · let D' : Finset ι := Finset.univ.filter fun i => ∀ j, u j i = 0
    refine ⟨D', ?_, fun _ => 0, fun _ => Submodule.zero_mem _, fun i hi j => (mem_filter.1 hi).2 j⟩
    by_contra hlt
    push Not at hlt
    let bad : Finset ι := Finset.univ.filter fun i => ¬ ∀ j, u j i = 0
    have hS_sub : S ⊆ bad.biUnion fun i => (curveCoordPoly u i).roots.toFinset := by
      intro z hz
      obtain ⟨c, hcRS, hdist⟩ := hclose z hz
      have hc0 : c = 0 := by
        obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hcRS
        have hp0 : p = 0 := by
          rw [degree_lt_iff_coeff_zero] at hp
          ext t; exact hp t (Nat.zero_le t)
        ext i; rw [hp0, eval_zero, Pi.zero_apply]
      rw [hc0] at hdist
      let zeros : Finset ι := Finset.univ.filter fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = (0 : ι → F) i
      have hzeros : zeros.card + hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) 0 =
          Fintype.card ι := card_filter_eq_add_hammingDist _ _
      have hnot_sub : ¬ zeros ⊆ D' := fun hsub => by
        have := card_le_card hsub; omega
      obtain ⟨i, hiZ, hiD'⟩ := Finset.not_subset.1 hnot_sub
      refine mem_biUnion.2 ⟨i, ?_, ?_⟩
      · exact mem_filter.2 ⟨mem_univ i, fun hall => hiD' (mem_filter.2 ⟨mem_univ i, hall⟩)⟩
      · have hw_ne : curveCoordPoly u i ≠ 0 := by
          intro h0
          apply hiD'
          refine mem_filter.2 ⟨mem_univ i, fun j => ?_⟩
          rw [← coeff_curveCoordPoly u i j, h0, coeff_zero]
        rw [Multiset.mem_toFinset, mem_roots hw_ne, IsRoot.def, eval_curveCoordPoly]
        exact (mem_filter.1 hiZ).2
    have hcard_le : S.card ≤ d * Fintype.card ι := by
      calc
        S.card ≤ (bad.biUnion fun i => (curveCoordPoly u i).roots.toFinset).card :=
          card_le_card hS_sub
        _ ≤ ∑ i ∈ bad, (curveCoordPoly u i).roots.toFinset.card := card_biUnion_le
        _ ≤ ∑ _i ∈ bad, d := Finset.sum_le_sum fun i _ =>
            (Multiset.toFinset_card_le _).trans
              ((card_roots' _).trans (natDegree_curveCoordPoly_le u i))
        _ = bad.card * d := by simp only [Finset.sum_const, smul_eq_mul]
        _ ≤ Fintype.card ι * d := Nat.mul_le_mul_right d (by
            simpa only [card_univ] using card_le_card (subset_univ bad))
        _ = d * Fintype.card ι := mul_comm _ _
    omega
  rcases Nat.eq_zero_or_pos e with rfl | he1
  · have hS_ge : d + 1 ≤ S.card := by
      have hn1 : 1 ≤ Fintype.card ι := by omega
      have : d ≤ d * Fintype.card ι := Nat.le_mul_of_pos_right d hn1
      omega
    obtain ⟨T, hTS, hT_card⟩ := Finset.exists_subset_card_eq hS_ge
    have hT_mem : ∀ z ∈ T, (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) ∈ reedSolomon α k := by
      intro z hz
      obtain ⟨c, hcRS, hdist⟩ := hclose z (hTS hz)
      have heq : (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) = c :=
        hammingDist_eq_zero.1 (Nat.eq_zero_of_le_zero hdist)
      rwa [heq]
    have hu_mem : ∀ j : Fin (d + 1), u j ∈ reedSolomon α k := by
      intro j
      have hu_eq : u j = ∑ z ∈ T, ((Lagrange.basis T id z).coeff (j : ℕ)) •
          (∑ j' : Fin (d + 1), z ^ (j' : ℕ) • u j') := by
        ext i
        let qi : F[X] :=
          Lagrange.interpolate T id (fun z => (∑ j' : Fin (d + 1), z ^ (j' : ℕ) • u j') i)
        have hpq : curveCoordPoly u i = qi := by
          refine sub_eq_zero.1 (eq_zero_of_degree_lt_of_eval_finset_eq_zero T ?_ ?_)
          · refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
            · by_cases hp0 : curveCoordPoly u i = 0
              · rw [hp0, degree_zero]; exact WithBot.bot_lt_coe _
              · rw [degree_eq_natDegree hp0, hT_card, Nat.cast_lt]
                exact Nat.lt_succ_of_le (natDegree_curveCoordPoly_le u i)
            · exact Lagrange.degree_interpolate_lt _ Function.injective_id.injOn
          · intro z hz
            rw [eval_sub, eval_curveCoordPoly]
            have hqi : qi.eval z = (∑ j' : Fin (d + 1), z ^ (j' : ℕ) • u j') i :=
              Lagrange.eval_interpolate_at_node _ Function.injective_id.injOn hz
            rw [hqi, sub_self]
        have hcoeff := congrArg (fun p : F[X] => p.coeff (j : ℕ)) hpq
        rw [coeff_curveCoordPoly] at hcoeff
        simp only [qi, Lagrange.interpolate_apply, finsetSum_coeff, coeff_C_mul] at hcoeff
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoeff ⊢
        rw [hcoeff]
        exact Finset.sum_congr rfl fun z _ => mul_comm _ _
      rw [hu_eq]
      exact Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (hT_mem z hz)
    refine ⟨Finset.univ, by rw [card_univ, Nat.sub_zero], u, hu_mem, fun _ _ _ => rfl⟩
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
  let u : Fin 2 → (ι → F) := ![u₀, u₁]
  have hcurve : ∀ z : F, (∑ j : Fin 2, z ^ (j : ℕ) • u j) = u₀ + z • u₁ := by
    intro z
    simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, u,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  obtain ⟨D', hD', v, hvRS, hagree⟩ :=
    exists_correlatedAgreement_curve_unique (d := 1) hα he u S (by simpa only [one_mul] using hS)
      (fun z hz => by rw [hcurve z]; exact hclose z hz)
  refine ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ⟨?_, ?_⟩⟩
  · simpa only [u, Matrix.cons_val_zero] using hagree i hi 0
  · simpa only [u, Matrix.cons_val_one, Matrix.cons_val_zero] using hagree i hi 1

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
  obtain ⟨D₀, hD₀, v₀, hv₀, v₁, hv₁, hag₀⟩ :=
    exists_correlatedAgreement_unique hα he u₀ u₁ S hS hclose
  have hex : ∃ D₀ : Finset ι, Fintype.card ι - e ≤ D₀.card ∧
      ∃ v : Fin 2 → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D₀, ∀ j, (![u₀, u₁] j) i = v j i :=
    ⟨D₀, hD₀, ![v₀, v₁], fun j => by fin_cases j <;> assumption, fun i hi j => by
      fin_cases j
      · exact (hag₀ i hi).1
      · exact (hag₀ i hi).2⟩
  obtain ⟨D', hD', v, hvRS, hagree, hmax⟩ :=
    exists_uniqueMaximal_correlatedAgreement_of_exists hα he hex
  refine ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ⟨hagree i hi 0, hagree i hi 1⟩,
    fun D'' w₀ w₁ hD'' hw₀ hw₁ hag => ?_⟩
  obtain ⟨hsub, hweq⟩ := hmax D'' ![w₀, w₁] hD'' (fun j => by fin_cases j <;> assumption)
    (fun i hi j => by
      fin_cases j
      · exact (hag i hi).1
      · exact (hag i hi).2)
  exact ⟨hsub, congrFun hweq 0, congrFun hweq 1⟩

end Cslib.Code
