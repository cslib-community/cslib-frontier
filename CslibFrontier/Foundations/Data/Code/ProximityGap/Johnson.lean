/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.Bivariate
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.Bounds
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.Params
public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import CslibFrontier.Foundations.Data.Code.SudanInterpolant
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.DegZ
import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.DoubleCount
import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.FactorPigeonhole
import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.Lift
import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.Separable
import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.ShiftAndFactor
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Algebra.Polynomial.Expand
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

The formalization is organized into focused submodules under
`CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson` (all internal step modules are imported
privately so downstream clients see only the public API):

* `Bounds`: exposed degree/error budget definitions (`maxYDeg`, `siegelZDeg`, `johnsonCurveBound`).
* `Params`: real-arithmetic `(m, D)` parameter selection isolating `Mathlib.Analysis.Real.Sqrt`.
* `DegZ`: internal `Z`-degree measures, `DegBound`, `curveWord`, and specialization homomorphisms.
* `Siegel`: Step 1 zero-denominator Siegel interpolation.
* `FactorPigeonhole`: Step 2 UFD factorization and Guruswami–Sudan pigeonhole selection.
* `Separable`: Step 3 separable contraction in arbitrary characteristic.
* `ShiftAndFactor`: Step 4 non-degenerate shift and factor selection.
* `Recurrence`: Step 5 universal `γ²`-scaled Taylor recurrence (`recPoly`).
* `Lift`: Step 6 resultant kill and algebraic-closure root lifting.
* `DoubleCount`: Step 7 weighted double counting and Lagrange interpolation.

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

open Polynomial Polynomial.Bivariate

public section

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
