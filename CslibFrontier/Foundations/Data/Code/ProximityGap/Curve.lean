/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
public import Mathlib.Algebra.Order.Ring.Rat
import CslibFrontier.Foundations.Data.Code.GuruswamiSudan
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Positivity

/-!
# Weighted, curve, and affine-space proximity gaps for Reed–Solomon codes

This module extends `CslibFrontier.Foundations.Data.Code.ProximityGap.Unique` and
`CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson` with weighted correlated agreement,
parameterized-curve proximity gaps, and dimension-independent affine-space proximity gaps and
correlated agreement for Reed–Solomon codes in both the unique-decoding and Johnson-bound regimes,
following Ben-Sasson, Carmon, Ishai, Kopparty, and Saraf
[BenSassonCarmonIshaiKoppartySaraf2020]. All theorem and section locators below follow the accepted
*Journal of the ACM* (2023) manuscript (`https://par.nsf.gov/servlets/purl/10467091`, where
Theorem 1.2 treats affine-space proximity gaps across both the unique-decoding and Johnson-bound
regimes, Theorem 1.4 treats line correlated agreement across both regimes, Theorem 1.5 treats
parameterized curves, Theorem 1.6 on printed p. 6 treats affine-space correlated agreement,
Lemma 6.3 and Section 6.3 on printed pp. 29–31 prove the line-to-affine reduction, Theorems 6.1–6.2
treat unique-decoding and Johnson-bound degree-`r` curves, Theorem 7.1 treats weighted correlated
agreement on curves, Version I, in the `α > √ρ` range, Theorem 7.2 treats weighted correlated
agreement on lines and curves, Version II, and Theorems 7.3–7.4 on printed p. 32 with proof in
Section 7.3 on printed p. 34 treat weighted correlated agreement over affine spaces; by contrast,
Theorem 7.2 of the July 2020 ePrint 2020/654 version concerns FRI soundness).

## Scope and relationship to the source theorems

* **Unique-decoding weighted & affine theorems:**
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_unique`,
  `Cslib.Code.exists_weighted_correlatedAgreement_curve_unique`, and their line/dichotomy
  counterparts give a unique-decoding specialization and signed-weight extension (`μ i ≤ 1`) of
  weighted curve correlated agreement (whereas source Theorem 7.1 treats weighted curves,
  Version I, across the `α > √ρ` range), achieving the sharp `d * |ι| < #S` threshold with zero
  dependence on weight denominators.
  `Cslib.Code.exists_uniqueMaximal_correlatedAgreement_affine_unique` and
  `Cslib.Code.proximityGap_affine_unique` formalize the exact eq. (1.2) threshold
  `|ι| * |F| ^ ℓ < |F| * #T` (`ε_U = n / q`) for unweighted affine spaces together with
  Theorem 1.6's uniqueness and maximality clause in the unique-decoding regime `2 * e + k ≤ |ι|`
  (printed p. 3, p. 6, and pp. 28–31), alongside the generic `(Fˣ)^ℓ × Fˣ` curve reduction
  `Cslib.Code.exists_correlatedAgreement_affine_of_curve` with linear-in-`ℓ` overhead and the
  `ℕ`/`ℚ`-weighted unique-decoding affine theorems
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_unique_sharp`,
  `Cslib.Code.exists_weighted_correlatedAgreement_affine_unique_sharp`,
  `Cslib.Code.weighted_proximityGap_affine_unique_sharp`, and
  `Cslib.Code.ratWeighted_proximityGap_affine_unique_sharp` at threshold
  `|ι| * (|F| ^ ℓ - 1) < (|F| - 1) * #T` (reusing
  `Cslib.Code.exists_uniqueMaximal_correlatedAgreement_affine_unique` for the `ℓ ≥ 1` unweighted
  step while handling `ℓ = 0` explicitly, including `|ι| = |F|`).
* **Johnson-bound curves (`ℚ`-weighted steps and explicit-constant dichotomies):**
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_johnson` and
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_line_johnson` are **explicit-parameter
  `ℚ`-weighted correlated-agreement steps** toward Theorems 6.2, 7.1, and 7.2 parameterized directly
  by `(m, D)` and weight denominator `M` via `Cslib.Code.ProximityGap.johnsonCurveBound`.
  `Cslib.Code.proximityGap_curve_johnson`, `Cslib.Code.proximityGap_curve_johnson_of_eta`,
  `Cslib.Code.weighted_proximityGap_curve_johnson`, and
  `Cslib.Code.ratWeighted_proximityGap_curve_johnson` are **original explicit-constant variants**
  toward Theorems 1.5, 6.2, 7.1, and 7.2 with exceptional fraction
  `1800 * r * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)` (respectively
  `115200 * r * n ^ 2 / (ρ * η ^ 6 * |F|)` and factor `M` in weighted forms); while
  `(m + 1) ^ 6 / ρ` is asymptotically smaller in `m` and `1 / ρ` than the paper's displayed
  `(m + 1 / 2) ^ 7 / (3 * ρ ^ (3 / 2))`, the bound is not uniformly smaller at small finite `m`
  (tracked in `#5968`).
* **Johnson-bound affine spaces without list-size premises (original finite bounds toward
  Theorems 1.6 and 7.4):**
  - `Cslib.Code.exists_weighted_correlatedAgreement_affine_of_divergence` and
    `Cslib.Code.exists_weighted_correlatedAgreement_affine_of_line` formalize the Section 6.3
    (printed pp. 29–31) and Section 7.3 (printed p. 34) line-to-affine correlated-agreement
    reduction over any linear code `C : Submodule F (ι → F)`: Lemma 6.3's parallel-line partition
    plus `(ℓ + 1)`-dimensional homogenization lifts `B_line * |F| ^ ℓ < |F| * #T` (exact
    denominator `|F|`) to everywhere-closeness, and maximal-divergence / minimal-weight-agreement
    pigeonhole over `L < |F|` candidate codewords yields simultaneous correlated agreement on all
    affine generators. To handle zero coordinate weights—where Section 7.3's claim on printed p. 34
    that Section 6.3 applies verbatim breaks because equal `W`-weight no longer forces `D' = D'_i`
    on zero-weight coordinates—the proof intersects each candidate agreement set with
    `supp W = {i | W i ≠ 0}` and models the parameter fiber directly as an `F`-submodule via `C`'s
    restriction image (so the generic linear-code lemma never uses the unique extension from `D'`
    on printed p. 31; for Reed–Solomon codes under Theorem 7.4's `α > ρ` that extension is
    available, so this is a generality gain rather than a source repair), establishing the full
    unweighted and weighted conclusions without restricting `W` or `μ` away from zero.
  - Because `maxYDeg (k - 1) D ≤ johnsonCurveBound |ι| m (k - 1) D 1 W_tot < |F|` holds
    automatically under `B_line * |F| ^ ℓ < |F| * #T`, the Reed–Solomon affine correlated-agreement
    theorems require **no extra list-size / field-size premise**:
    `Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson`,
    `Cslib.Code.exists_correlatedAgreement_affine_johnson`, and
    `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson` give explicit-parameter
    `(m, D)` correlated agreement, while
    `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_multiplicity`,
    `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_eta`,
    `Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity`,
    `Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson_of_eta`,
    `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson_of_multiplicity`, and
    `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson_of_eta` give closed-form
    correlated agreement with explicit Siegel constants
    `1800 * [M *] (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)` and
    `115200 * [M *] n ^ 2 / (ρ * η ^ 6 * |F|)`. These are this library's original finite bounds.
    Eq. (1.3) uses `min(η, √ρ / 20)` in its denominator, whereas these formulas use the gap `η`
    directly, so a density sufficient for (1.3) can fall below the Lean cutoff: for example at
    `q = 11 ^ 10`, `n = 16`, `ρ = 1 / 4`, radius `7 / 16`, `η = 1 / 16` (`> √ρ / 20 = 1 / 40`),
    `m = 4`, a line of codewords has close density one and clears the (1.3) cutoff
    `20,480,000,000 / q < 1`, but not the multiplicity corollary's `28,800,000,000 / q > 1`. The
    unique-decoding uniqueness clause of Theorem 1.6 is formalized separately in
    `Cslib.Code.exists_uniqueMaximal_correlatedAgreement_affine_unique`. The exact cited
    endpoints, including the displayed constants `(m + 1 / 2) ^ 7 / (3 * ρ ^ (3 / 2))`,
    `(2 * m + 1) * (M * n + 1) / √ρ`, and `ρ ^ 2 / (2 * η) ^ 7`, remain tracked in `#5968`.
  - `Cslib.Code.proximityGap_affine_johnson_exact`,
    `Cslib.Code.weighted_proximityGap_affine_johnson_exact`,
    `Cslib.Code.ratWeighted_proximityGap_affine_johnson_exact`,
    `Cslib.Code.proximityGap_affine_johnson`, `Cslib.Code.proximityGap_affine_johnson_of_eta`,
    `Cslib.Code.weighted_proximityGap_affine_johnson`, and
    `Cslib.Code.ratWeighted_proximityGap_affine_johnson` follow directly as contrapositive
    corollaries of the correlated-agreement theorems with exact denominator `|F|` (in the setting
    of Theorem 1.2).

## Mathematical overview

1. **Sharp weighted correlated agreement in the unique-decoding regime**
   (unique-decoding specialization and signed-weight extension of
   [BenSassonCarmonIshaiKoppartySaraf2020, Section 7 / Theorem 7.1], where source Theorem 7.1
   treats weighted curves, Version I, in the `α > √ρ` range):
   Given `d + 1` words `u : Fin (d + 1) → (ι → F)` over an arbitrary field `F`, any weight
   function `μ : ι → ℚ` bounded above by `1`, and a threshold `θ : ℚ` strictly above
   `(|ι| - e : ℕ) - 1` where `2 * e + k ≤ |ι|`: if more than `d * |ι|` scalars `z ∈ S` have
   some codeword `c_z ∈ reedSolomon α k` achieving `μ`-weighted agreement at least `θ` with the
   curve point `∑ j, z ^ (j : ℕ) • u j`, then:
   - unweighted correlated agreement (`Cslib.Code.exists_correlatedAgreement_curve_unique`) gives
     codewords `v : Fin (d + 1) → (ι → F)` agreeing with `u` on at least `|ι| - e` positions;
   - unique decoding forces `c_z = ∑ j, z ^ (j : ℕ) • v j` for every `z ∈ S`;
   - on the maximal shared agreement set `D' = {i | ∀ j, u j i = v j i}`, every `z ∈ S` whose
     `μ`-weighted agreement exceeds `∑ i ∈ D', μ i` must hit at least one index `i ∉ D'`, which
     is a root of the nonzero degree-`≤ d` polynomial `∑ j, (u j i - v j i) Z ^ j`.
   Hence at most `d * |ι|` scalars can exceed `∑ i ∈ D', μ i`, forcing `θ ≤ ∑ i ∈ D', μ i`
   with **no dependence on the total weight or weight denominator**
   (`Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_unique`,
   `Cslib.Code.exists_weighted_correlatedAgreement_curve_unique`,
   `Cslib.Code.exists_weighted_correlatedAgreement_unique`).

2. **Generic affine-space-to-curve reduction (`(Fˣ)^ℓ × Fˣ` bijection)**:
   For any pointwise proximity predicate `P : (ι → F) → Prop` and shared-agreement predicate
   `Q : Finset ι → Prop`, a degree-`ℓ` curve correlated-agreement threshold `B_curve` lifts
   directly to an affine space `u₀ + ∑ j : Fin ℓ, z j • u j` with threshold
   `(B_curve + ℓ) * |F| ^ (ℓ - 1)` — i.e., error fraction `(B_curve + ℓ) / |F|`, linear in `ℓ`
   with no exponential blowup (`Cslib.Code.exists_correlatedAgreement_affine_of_curve`).
   Note that this explicit `(Fˣ)^ℓ × Fˣ` curve reduction introduces an explicit linear `ℓ` factor
   relative to the curve-independent phrasing of
   [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.6], while remaining uniform across arbitrary
   pointwise and shared-agreement predicates.

3. **Dimension-independent affine-space proximity gaps and Section 6.3 / 7.3 divergence lift**:
   By averaging over all `(q ^ ℓ - 1) / (q - 1)` lines passing through a single non-close point
   `y`, any 1D line proximity-gap dichotomy for an arbitrary predicate `P` with exceptional count
   `≤ B_line` lifts to `(q - 1) * #T ≤ B_line * (q ^ ℓ - 1)` with zero dependence on `ℓ`
   (`Cslib.Code.proximityGap_affine_of_line`, yielding the weighted unique-decoding dichotomies
   `Cslib.Code.weighted_proximityGap_affine_unique_sharp` and
   `Cslib.Code.ratWeighted_proximityGap_affine_unique_sharp`, alongside the weighted correlated
   agreement theorems `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_unique_sharp` and
   `Cslib.Code.exists_weighted_correlatedAgreement_affine_unique_sharp`). For
   linear codes with list size `L < |F|` and 1D weighted line correlated agreement, Lemma 6.3's
   parallel-line partition plus homogenization and Section 6.3's minimal-agreement / affine-subspace
   pigeonhole (refined by intersecting candidate agreement sets with `supp W`) yield
   `Cslib.Code.exists_weighted_correlatedAgreement_affine_of_divergence` and
   `Cslib.Code.exists_weighted_correlatedAgreement_affine_of_line` at exact threshold
   `B_line * |F| ^ ℓ < |F| * #T` with zero `ℓ` or `L * B_line` overhead.

4. **Johnson-bound curves and affine spaces** (toward
   [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2, 1.5, 1.6, 6.2, 7.2, 7.3, and 7.4],
   accepted JACM 2023 manuscript):
   - **Parameterized curves (`r : ℕ`):** Reusing
     `Cslib.Code.ProximityGap.johnson_curve_params_bound` and
     `Cslib.Code.ProximityGap.johnsonCurveBound_mul_le` yields original explicit-constant
     finite-field curve proximity-gap dichotomies up to `1 - √ρ - √ρ / (2 * m)` and `1 - √ρ - η`,
     as well as explicit-parameter `ℚ`-weighted curve/line correlated-agreement steps and
     `ℕ`/`ℚ`-weighted curve dichotomies scaling linearly in the weight denominator `M`
     (`Cslib.Code.proximityGap_curve_johnson`, `Cslib.Code.proximityGap_curve_johnson_of_eta`,
     `Cslib.Code.weighted_proximityGap_curve_johnson`,
     `Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_johnson`,
     `Cslib.Code.exists_ratWeighted_correlatedAgreement_line_johnson`,
     `Cslib.Code.ratWeighted_proximityGap_curve_johnson`).
   - **Johnson affine spaces (`ℓ : ℕ`):** Combining
     `Cslib.Code.exists_weighted_correlatedAgreement_affine_of_line` with the uniform
     Guruswami–Sudan list-size bound `maxYDeg (k - 1) D ≤ B_line` and 1D weighted line correlated
     agreement yields unweighted, `ℕ`-weighted, and `ℚ`-weighted Johnson affine correlated
     agreement in both explicit-parameter `(m, D)` form and closed-form `(m)` / `(η)` form with
     exact denominator `|F|` and zero extra list-size premises, from which all seven affine
     proximity-gap dichotomies follow immediately.

## Main results

* `Cslib.Code.hammingDist_affine_le_of_eq_on`: shared agreement on `D'` implies Hamming distance
  at most `e` at every point of an affine space.
* `Cslib.Code.weightedAgree_curve_ge_of_eq_on`, `Cslib.Code.ratWeightedAgree_curve_ge_of_eq_on`,
  `Cslib.Code.weightedAgree_affine_ge_of_eq_on`, &
  `Cslib.Code.ratWeightedAgree_affine_ge_of_eq_on`: converse weighted-agreement bounds for curves
  and affine spaces.
* `Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_unique` &
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_unique`: sharp `ℚ`-weighted correlated
  agreement on curves and lines in the unique-decoding regime over arbitrary fields.
* `Cslib.Code.exists_weighted_correlatedAgreement_curve_unique` &
  `Cslib.Code.exists_weighted_correlatedAgreement_unique`: sharp `ℕ`-weighted correlated
  agreement on curves and lines in the unique-decoding regime.
* `Cslib.Code.weighted_proximityGap_curve_unique`, `Cslib.Code.weighted_proximityGap_unique`,
  `Cslib.Code.ratWeighted_proximityGap_curve_unique`, &
  `Cslib.Code.ratWeighted_proximityGap_unique`: finite-field weighted proximity-gap dichotomies.
* `Cslib.Code.exists_correlatedAgreement_affine_of_curve`: polymorphic affine-space-to-curve
  reduction with linear-in-`ℓ` error overhead.
* `Cslib.Code.proximityGap_affine_of_line`: polymorphic 1D-line-to-affine-space pointwise dichotomy
  with zero dimension overhead (`(|F| - 1) * #T ≤ B_line * (|F| ^ ℓ - 1)`).
* `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_unique_sharp`,
  `Cslib.Code.exists_weighted_correlatedAgreement_affine_unique_sharp`,
  `Cslib.Code.weighted_proximityGap_affine_unique_sharp`, &
  `Cslib.Code.ratWeighted_proximityGap_affine_unique_sharp`: dimension-independent unique-decoding
  `ℕ`/`ℚ`-weighted affine-space correlated agreement and dichotomies at threshold
  `|ι| * (|F| ^ ℓ - 1) < (|F| - 1) * #T` (zero dependence on weight denominators).
* `Cslib.Code.exists_weighted_correlatedAgreement_affine_of_divergence` &
  `Cslib.Code.exists_weighted_correlatedAgreement_affine_of_line`: Section 6.3 / 7.3 divergence
  and Lemma 6.3 homogenization lift from 1D weighted line correlated agreement plus codeword list
  bound `2 ≤ ℓ → L < |F|` to arbitrary-dimensional affine spaces at exact threshold
  `B_line * |F| ^ ℓ < |F| * #T` (returning `D' ⊆ supp W`).
* `Cslib.Code.exists_uniqueMaximal_correlatedAgreement_affine_unique` &
  `Cslib.Code.proximityGap_affine_unique`: exact eq. (1.2) (`|ι| * |F| ^ ℓ < |F| * #T`)
  unique-decoding affine-space correlated agreement with Theorem 1.6's unique maximal agreement set
  and unique generator codewords (printed p. 6, pp. 28–31), together with its exact-`|F|`
  proximity-gap dichotomy (Theorem 1.2, eq. (1.2)).
* `Cslib.Code.proximityGap_curve_johnson` & `Cslib.Code.proximityGap_curve_johnson_of_eta`:
  original explicit-constant finite-field Johnson-bound proximity-gap variants on degree-`r` curves
  (variants of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.5], accepted JACM 2023 manuscript).
* `Cslib.Code.weighted_proximityGap_curve_johnson`,
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_johnson`,
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_line_johnson`, &
  `Cslib.Code.ratWeighted_proximityGap_curve_johnson`: explicit-parameter `ℚ`-weighted steps and
  original explicit-constant `ℕ`/`ℚ`-weighted curve dichotomies toward
  [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 6.2, 7.1, and 7.2] (accepted JACM 2023
  manuscript).
* `Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson`,
  `Cslib.Code.exists_correlatedAgreement_affine_johnson`, &
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson`: explicit-parameter `(m, D)`
  `ℕ`-weighted, unweighted, and `ℚ`-weighted Johnson-bound correlated agreement on affine spaces
  at threshold `B_line * |F| ^ ℓ < |F| * #T` with no list-size premise.
* `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_multiplicity`,
  `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_eta`,
  `Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity`,
  `Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson_of_eta`,
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson_of_multiplicity`, &
  `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson_of_eta`: original
  explicit-constant closed-form unweighted, `ℕ`-weighted, and `ℚ`-weighted Johnson-bound affine
  correlated-agreement variants in the setting of
  [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6, 7.3, and 7.4].
* `Cslib.Code.proximityGap_affine_johnson_exact`,
  `Cslib.Code.weighted_proximityGap_affine_johnson_exact`,
  `Cslib.Code.ratWeighted_proximityGap_affine_johnson_exact`,
  `Cslib.Code.proximityGap_affine_johnson`,
  `Cslib.Code.proximityGap_affine_johnson_of_eta`,
  `Cslib.Code.weighted_proximityGap_affine_johnson`, &
  `Cslib.Code.ratWeighted_proximityGap_affine_johnson`: finite-field Johnson-bound affine
  proximity-gap dichotomies with exact denominator `|F|` in the setting of Theorem 1.2.

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf,
  *Proximity Gaps for Reed–Solomon Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [V. Guruswami, M. Sudan, *Improved Decoding of Reed–Solomon and Algebraic-Geometry Codes*]
  [GuruswamiSudan1999]
-/

public section

namespace Cslib.Code

open scoped BigOperators
open Finset Polynomial

/-! ### Private algebraic and combinatorial helpers -/

private theorem line_sum_fin2 {F ι : Type*} [Field F] (u₀ u₁ : ι → F) (z : F) :
    (∑ j : Fin 2, z ^ (j : ℕ) • ![u₀, u₁] j) = u₀ + z • u₁ := by
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

private theorem subset_filter_curve_eq {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {d : ℕ} {D' : Finset ι} {u v : Fin (d + 1) → (ι → F)}
    (hagree : ∀ i ∈ D', ∀ j : Fin (d + 1), u j i = v j i) (z : F) :
    D' ⊆ Finset.univ.filter fun i =>
      (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j) i :=
  fun i hi => mem_filter.2 ⟨mem_univ i, by
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [hagree i hi j]⟩

private theorem subset_filter_affine_eq {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {ℓ : ℕ} {D' : Finset ι} {u₀ v₀ : ι → F} {u v : Fin ℓ → (ι → F)}
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i) (z : Fin ℓ → F) :
    D' ⊆ Finset.univ.filter fun i =>
      (u₀ + ∑ j : Fin ℓ, z j • u j) i = (v₀ + ∑ j : Fin ℓ, z j • v j) i :=
  fun i hi => mem_filter.2 ⟨mem_univ i, by
    obtain ⟨h0, hj⟩ := hagree i hi
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, h0]
    congr 1; exact Finset.sum_congr rfl fun j _ => by rw [hj j]⟩

private theorem subset_filter_line_eq {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {D' : Finset ι} {u₀ v₀ u₁ v₁ : ι → F}
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i) (z : F) :
    D' ⊆ Finset.univ.filter fun i => (u₀ + z • u₁) i = (v₀ + z • v₁) i :=
  fun i hi => mem_filter.2 ⟨mem_univ i, by
    obtain ⟨h0, h1⟩ := hagree i hi; simp only [Pi.add_apply, Pi.smul_apply, h0, h1]⟩

private theorem hammingDist_le_of_card_filter_eq
    {F : Type*} {ι : Type*} [Fintype ι] [DecidableEq F]
    {e : ℕ} {x y : ι → F}
    (hcard : Fintype.card ι - e ≤ (Finset.univ.filter fun i => x i = y i).card) :
    hammingDist x y ≤ e := by
  have htot := card_filter_eq_add_hammingDist x y; omega

private theorem card_filter_eq_of_hammingDist_le
    {F : Type*} {ι : Type*} [Fintype ι] [DecidableEq F]
    {e : ℕ} {x y : ι → F} (hdist : hammingDist x y ≤ e) :
    Fintype.card ι - e ≤ (Finset.univ.filter fun i => x i = y i).card := by
  have htot := card_filter_eq_add_hammingDist x y; omega

/-- Pointwise conversion from signed `ℚ`-weighted agreement (`∀ i, μ i ≤ 1`) above
`((|ι| - e : ℕ) : ℚ) - 1` to unweighted Hamming distance at most `e`. -/
private theorem hammingDist_le_of_ratWeightedAgree_ge
    {F : Type*} {ι : Type*} [Fintype ι] [DecidableEq F]
    {e : ℕ} {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    {x c : ι → F}
    (hμ_ge : θ ≤ ∑ i ∈ Finset.univ.filter (fun i => x i = c i), μ i) :
    hammingDist x c ≤ e := by
  refine hammingDist_le_of_card_filter_eq ?_
  set A := Finset.univ.filter fun i => x i = c i
  have hsum_le : ∑ i ∈ A, μ i ≤ (A.card : ℚ) :=
    (Finset.sum_le_sum fun i _ => hμ_le i).trans_eq (by simp)
  have hlt : Fintype.card ι - e < A.card + 1 := Nat.cast_lt.1 (by
    have : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < (A.card : ℚ) := hθ.trans_le (hμ_ge.trans hsum_le)
    have hq : ((Fintype.card ι - e : ℕ) : ℚ) < ((A.card + 1 : ℕ) : ℚ) := by push_cast; linarith
    exact hq)
  omega

/-- Unique-decoding weight-upgrade step: if `D'` has total `μ`-weight `< θ` and agrees everywhere,
any point `p` that is `μ`-close to `reedSolomon α k` must agree with `v_at p` at some `i ∉ D'`. -/
private theorem exists_disagree_mem_unique {F ι P : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α) {e k : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1) {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    {u_at v_at : P → ι → F} (hvRS : ∀ p, v_at p ∈ reedSolomon α k)
    (hdist : ∀ p, hammingDist (u_at p) (v_at p) ≤ e)
    (D' : Finset ι) (hD'_sub : ∀ p, ∀ i ∈ D', u_at p i = v_at p i)
    (hlt : ∑ i ∈ D', μ i < θ) {p : P}
    (hcl : ∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ Finset.univ.filter (fun i => u_at p i = c i), μ i) :
    ∃ i ∉ D', u_at p i = v_at p i := by
  obtain ⟨c, hcRS, hμ_ge⟩ := hcl
  obtain rfl : c = v_at p := eq_of_hammingDist_le_reedSolomon hα hunique hcRS (hvRS p)
    (hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge) (hdist p)
  by_contra hnone; push Not at hnone
  have heq : D' = Finset.univ.filter fun i => u_at p i = v_at p i :=
    Finset.Subset.antisymm (fun i hi => mem_filter.2 ⟨mem_univ i, hD'_sub p i hi⟩)
      fun i hi => by_contra fun hn => hnone i hn (mem_filter.1 hi).2
  exact absurd (heq ▸ hμ_ge) (not_le.2 hlt)

private theorem nat_le_sum_iff_div {ι : Type*} {W : ι → ℕ} {M B : ℕ} (hM : 0 < M)
    (S : Finset ι) : B ≤ ∑ i ∈ S, W i ↔ (B : ℚ) / M ≤ ∑ i ∈ S, (W i : ℚ) / M := by
  have hMq : (0 : ℚ) < M := Nat.cast_pos.2 hM
  rw [← Finset.sum_div, div_le_div_iff_of_pos_right hMq, ← Nat.cast_sum, Nat.cast_le]

/-- Counting lemma: in `Fin ℓ → F` with `1 ≤ ℓ`, the hyperplane `{z | z j₀ = 0}` has cardinality
`|F| ^ (ℓ - 1)`. -/
private theorem card_filter_coord_eq_zero
    {F : Type*} [Zero F] [Fintype F] [DecidableEq F]
    {ℓ : ℕ} (j₀ : Fin ℓ) :
    (Finset.univ.filter fun z : Fin ℓ → F => z j₀ = 0).card =
      (Fintype.card F) ^ (ℓ - 1) := by
  classical
  have hbij := Finset.card_bij (s := (Finset.univ : Finset ({j : Fin ℓ // j ≠ j₀} → F)))
    (t := Finset.univ.filter fun z : Fin ℓ → F => z j₀ = 0)
    (fun g _ j => if h : j = j₀ then 0 else g ⟨j, h⟩)
    (fun _ _ => by simp)
    (fun g₁ _ g₂ _ heq => funext fun ⟨j, hj⟩ => by simpa [hj] using congrFun heq j)
    (fun z hz => ⟨fun j => z j.1, mem_univ _, funext fun j => by
      by_cases h : j = j₀ <;> simp [h, (mem_filter.1 hz).2]⟩)
  rw [← hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_subtype]
  congr 1
  have hf : (Finset.univ.filter fun j : Fin ℓ => j ≠ j₀) = Finset.univ.erase j₀ := by ext; simp
  rw [hf, Finset.card_erase_of_mem (mem_univ j₀), Finset.card_univ, Fintype.card_fin]

/-! ### Converse helpers for affine spaces and weighted agreement -/

/-- If `u₀` and `u j` agree with `v₀` and `v j` on a shared subset `D'` of size at least
`|ι| - e`, then every affine combination `u₀ + ∑ j, z j • u j` lies within Hamming distance `e`
of `v₀ + ∑ j, z j • v j`. -/
theorem hammingDist_affine_le_of_eq_on
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {e ℓ : ℕ} {D' : Finset ι} {u₀ v₀ : ι → F} {u v : Fin ℓ → (ι → F)}
    (hD' : Fintype.card ι - e ≤ D'.card)
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i)
    (z : Fin ℓ → F) :
    hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) (v₀ + ∑ j : Fin ℓ, z j • v j) ≤ e :=
  hammingDist_le_of_card_filter_eq
    (hD'.trans (Finset.card_le_card (subset_filter_affine_eq hagree z)))

/-- Converse weighted agreement for curves: if `u` and `v` agree on `D'`, then every point on the
curve `∑ j, z ^ j • u j` achieves at least `∑ i ∈ D', W i` weighted agreement with
`∑ j, z ^ j • v j`. -/
theorem weightedAgree_curve_ge_of_eq_on
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {d : ℕ} {D' : Finset ι} {u v : Fin (d + 1) → (ι → F)}
    (W : ι → ℕ)
    (hagree : ∀ i ∈ D', ∀ j : Fin (d + 1), u j i = v j i)
    (z : F) :
    ∑ i ∈ D', W i ≤
      ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j) i),
        W i :=
  Finset.sum_le_sum_of_subset (subset_filter_curve_eq hagree z)

/-- Converse `ℚ`-weighted agreement for curves (under nonnegative weights `0 ≤ μ i`). -/
theorem ratWeightedAgree_curve_ge_of_eq_on
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {d : ℕ} {D' : Finset ι} {u v : Fin (d + 1) → (ι → F)}
    {μ : ι → ℚ} (hμ_nonneg : ∀ i, 0 ≤ μ i)
    (hagree : ∀ i ∈ D', ∀ j : Fin (d + 1), u j i = v j i)
    (z : F) :
    ∑ i ∈ D', μ i ≤
      ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j) i),
        μ i :=
  Finset.sum_le_sum_of_subset_of_nonneg (subset_filter_curve_eq hagree z) fun i _ _ => hμ_nonneg i

/-- Converse weighted agreement for affine spaces: if `u₀, u` agree with `v₀, v` on `D'`, then
every affine combination achieves at least `∑ i ∈ D', W i` weighted agreement. -/
theorem weightedAgree_affine_ge_of_eq_on
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {ℓ : ℕ} {D' : Finset ι} {u₀ v₀ : ι → F} {u v : Fin ℓ → (ι → F)}
    (W : ι → ℕ)
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i)
    (z : Fin ℓ → F) :
    ∑ i ∈ D', W i ≤
      ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = (v₀ + ∑ j : Fin ℓ, z j • v j) i),
        W i :=
  Finset.sum_le_sum_of_subset (subset_filter_affine_eq hagree z)

/-- Converse `ℚ`-weighted agreement for affine spaces (under nonnegative weights `0 ≤ μ i`). -/
theorem ratWeightedAgree_affine_ge_of_eq_on
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {ℓ : ℕ} {D' : Finset ι} {u₀ v₀ : ι → F} {u v : Fin ℓ → (ι → F)}
    {μ : ι → ℚ} (hμ_nonneg : ∀ i, 0 ≤ μ i)
    (hagree : ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i)
    (z : Fin ℓ → F) :
    ∑ i ∈ D', μ i ≤
      ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = (v₀ + ∑ j : Fin ℓ, z j • v j) i),
        μ i :=
  Finset.sum_le_sum_of_subset_of_nonneg (subset_filter_affine_eq hagree z) fun i _ _ => hμ_nonneg i

/-! ### Part 1: Sharp weighted correlated agreement in the unique-decoding regime -/

/-- **Weighted correlated agreement on parameterized curves in the unique-decoding regime**
(`ℚ`-weights; unique-decoding specialization and signed-weight extension of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.1 & Section 7], where source Theorem 7.1 treats
weighted curves, Version I, in the `α > √ρ` range):

Over an arbitrary field `F`, let `α : ι → F` be distinct evaluation points, `2 * e + k ≤ |ι|`,
and `μ : ι → ℚ` any weight function bounded above by `1` (in particular, any `[0, 1]`-valued
weight function). Suppose `θ : ℚ` satisfies `((|ι| - e : ℕ) : ℚ) - 1 < θ` (so `μ`-weighted
agreement `≥ θ` implies unweighted Hamming distance `≤ e`). If more than `d * |ι|` scalars
`z ∈ S` have a codeword in `reedSolomon α k` achieving `μ`-weighted agreement at least `θ`
with the curve point `∑ j, z ^ (j : ℕ) • u j`, then there exist codewords `v j ∈ reedSolomon α k`
and a single shared coordinate set `D'` with `θ ≤ ∑ i ∈ D', μ i` on which `u j i = v j i` for
all `i ∈ D'` and all `j`.

Notice that the threshold `d * |ι| < #S` has zero dependence on the weight denominator or total
weight. -/
theorem exists_ratWeighted_correlatedAgreement_curve_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {e k d : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u : Fin (d + 1) → (ι → F)) (S : Finset F)
    (hS : d * Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v : Fin (d + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  classical
  obtain ⟨D₀, hD₀, v, hvRS, hagree₀⟩ := exists_correlatedAgreement_curve_unique hα hunique u S hS
    fun z hz => let ⟨c, hcRS, hμ_ge⟩ := hclose z hz
      ⟨c, hcRS, hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge⟩
  let D' : Finset ι := Finset.univ.filter fun i => ∀ j : Fin (d + 1), u j i = v j i
  refine ⟨D', ?_, v, hvRS, fun i hi => (mem_filter.1 hi).2⟩
  by_contra hlt; push Not at hlt
  let f : ι → F[X] := fun i => Polynomial.ofFn (d + 1) fun j => u j i - v j i
  let badI : Finset ι := Finset.univ.filter fun i => ¬ ∀ j : Fin (d + 1), u j i = v j i
  have hf_ne (i : ι) (hi : i ∈ badI) : f i ≠ 0 := fun h0 => (mem_filter.1 hi).2 fun j => by
    have hc := congrArg (fun p : F[X] => p.coeff (j : ℕ)) h0
    simp only [f, Polynomial.ofFn_coeff_eq_val_of_lt _ j.2, coeff_zero] at hc
    exact sub_eq_zero.1 hc
  have hS_sub : S ⊆ badI.biUnion fun i => (f i).roots.toFinset := fun z hz => by
    obtain ⟨i, hi_not, heq⟩ := exists_disagree_mem_unique hα hunique hμ_le hθ
      (u_at := fun z => ∑ j : Fin (d + 1), z ^ (j : ℕ) • u j)
      (v_at := fun z => ∑ j : Fin (d + 1), z ^ (j : ℕ) • v j)
      (fun z => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvRS j))
      (hammingDist_curve_le_of_eq_on hD₀ hagree₀) D'
      (fun z i hi => (mem_filter.1 (subset_filter_curve_eq (fun _ h => (mem_filter.1 h).2) z hi)).2)
      hlt (hclose z hz)
    have hi_bad : i ∈ badI :=
      mem_filter.2 ⟨mem_univ i, fun h => hi_not (mem_filter.2 ⟨mem_univ i, h⟩)⟩
    refine mem_biUnion.2 ⟨i, hi_bad, Multiset.mem_toFinset.2 <|
      (Polynomial.mem_roots (hf_ne i hi_bad)).2 ?_⟩
    change (f i).eval z = 0
    simp only [f, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial]
    have hterm (j : Fin (d + 1)) : (u j i - v j i) * z ^ (j : ℕ) =
        z ^ (j : ℕ) * u j i - z ^ (j : ℕ) * v j i := by ring
    simp only [hterm, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 (by simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using heq)
  have hcard_le : S.card ≤ d * Fintype.card ι := calc
    S.card ≤ (badI.biUnion fun i => (f i).roots.toFinset).card := Finset.card_le_card hS_sub
    _ ≤ ∑ i ∈ badI, ((f i).roots.toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ badI, (f i).natDegree := Finset.sum_le_sum fun i _ =>
        (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
    _ ≤ ∑ _i ∈ badI, d := Finset.sum_le_sum fun i _ =>
        Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos d) _)
    _ = badI.card * d := by simp only [Finset.sum_const, smul_eq_mul]
    _ ≤ d * Fintype.card ι := mul_comm _ d ▸ Nat.mul_le_mul_right d (Finset.card_le_univ badI)
  omega

/-- **Weighted correlated agreement on affine lines in the unique-decoding regime**
(`ℚ`-weights; unique-decoding line specialization and signed-weight extension of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1 & Section 7], where source Theorem 7.1 treats
weighted curves, Version I, in the `α > √ρ` range):
Line specialization (`d = 1`) of `Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_unique`,
with exact threshold `|ι| < #S`. -/
theorem exists_ratWeighted_correlatedAgreement_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {e k : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u₀ u₁ : ι → F) (S : Finset F)
    (hS : Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v₁ ∈ reedSolomon α k,
        ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_ratWeighted_correlatedAgreement_curve_unique hα
    hunique hμ_le hθ ![u₀, u₁] S (by simpa only [one_mul] using hS : 1 * Fintype.card ι < S.card)
    fun z hz => by rw [line_sum_fin2]; exact hclose z hz
  exact ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ⟨hagree i hi 0, hagree i hi 1⟩⟩

/-- Integer-to-rational weight threshold: with `t = ⌈B / M⌉ = (B + M - 1) / M`, the
unique-decoding agreement count `n - (n - t)` satisfies `n - (n - t) - 1 < B / M`. -/
private theorem card_sub_sub_ceilDiv_sub_one_lt {n B M : ℕ} (hM : 0 < M) :
    ((n - (n - (B + M - 1) / M) : ℕ) : ℚ) - 1 < (B : ℚ) / (M : ℚ) := by
  have hdiv : M * ((B + M - 1) / M) ≤ B + M - 1 := Nat.mul_div_le (B + M - 1) M
  generalize (B + M - 1) / M = t at hdiv ⊢
  have hMq : (0 : ℚ) < (M : ℚ) := Nat.cast_pos.2 hM
  have ht_lt : M * (n - (n - t)) < B + M :=
    (Nat.mul_le_mul_left M (by omega : n - (n - t) ≤ t)).trans_lt (by omega)
  have hq_lt : (M : ℚ) * ((n - (n - t) : ℕ) : ℚ) < (B : ℚ) + (M : ℚ) := by exact_mod_cast ht_lt
  rw [lt_div_iff₀ hMq]
  linarith

/-- **Integer-weighted correlated agreement on parameterized curves in the unique-decoding regime**
(unique-decoding specialization of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.1 & Section 7],
where source Theorem 7.1 treats weighted curves, Version I, in the `α > √ρ` range):

Given integer weights `W : ι → ℕ` bounded by `M > 0` (`∀ i, W i ≤ M`) and weighted agreement
threshold `B : ℕ`, let `e := |ι| - (B + M - 1) / M` be the implied unweighted error bound.
Whenever `2 * e + k ≤ |ι|` and `d * |ι| < #S`, weighted agreement `≥ B` on the curve for all
`z ∈ S` implies shared weighted agreement `≥ B` for codewords `v : Fin (d + 1) → (ι → F)`. -/
theorem exists_weighted_correlatedAgreement_curve_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k d M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u : Fin (d + 1) → (ι → F)) (S : Finset F)
    (hS : d * Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), W i) :
    ∃ D' : Finset ι, B ≤ ∑ i ∈ D', W i ∧
      ∃ v : Fin (d + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_ratWeighted_correlatedAgreement_curve_unique hα
    hunique (fun i => (div_le_one (Nat.cast_pos.2 hM)).2 (Nat.cast_le.2 (hW i)))
    (card_sub_sub_ceilDiv_sub_one_lt hM) u S hS fun z hz =>
      let ⟨c, hcRS, hW_ge⟩ := hclose z hz; ⟨c, hcRS, (nat_le_sum_iff_div hM _).1 hW_ge⟩
  exact ⟨D', (nat_le_sum_iff_div hM D').2 hD', v, hvRS, hagree⟩

/-- **Integer-weighted correlated agreement on affine lines in the unique-decoding regime**
(unique-decoding line specialization of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 4.1 &
Section 7], where source Theorem 7.1 treats weighted curves, Version I, in the `α > √ρ` range):
Line specialization (`d = 1`) of `Cslib.Code.exists_weighted_correlatedAgreement_curve_unique`
with exact threshold `|ι| < #S`, directly discharging FRI unique-decoding commit-round soundness
with zero total-weight loss. -/
theorem exists_weighted_correlatedAgreement_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u₀ u₁ : ι → F) (S : Finset F)
    (hS : Fintype.card ι < S.card)
    (hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), W i) :
    ∃ D' : Finset ι, B ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v₁ ∈ reedSolomon α k,
        ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_weighted_correlatedAgreement_curve_unique hα hM hW
    hunique ![u₀, u₁] S (by simpa only [one_mul] using hS : 1 * Fintype.card ι < S.card)
    fun z hz => by rw [line_sum_fin2]; exact hclose z hz
  exact ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ⟨hagree i hi 0, hagree i hi 1⟩⟩

private theorem curve_dichotomy_of_ca {F ι : Type*} [Field F] [Fintype F] {d : ℕ}
    {C : Submodule F (ι → F)} {u : Fin (d + 1) → (ι → F)}
    (Close : (ι → F) → (ι → F) → Prop) (Good : Finset ι → Prop) {B : ℕ}
    (hgood : ∀ {D' : Finset ι}, Good D' → ∀ {v : Fin (d + 1) → (ι → F)},
      (∀ i ∈ D', ∀ j, u j i = v j i) →
      ∀ z : F, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j)
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • v j))
    [DecidablePred fun z : F => ∃ c ∈ C, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c]
    (hca : ∀ S : Finset F, B < S.card →
      (∀ z ∈ S, ∃ c ∈ C, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c) →
      ∃ D' : Finset ι, Good D' ∧ ∃ v : Fin (d + 1) → (ι → F), (∀ j, v j ∈ C) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i) :
    (∀ z : F, ∃ c ∈ C, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c) ∨
      (Finset.univ.filter fun z : F =>
        ∃ c ∈ C, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c).card ≤ B := by
  by_cases hcard : (Finset.univ.filter fun z : F =>
      ∃ c ∈ C, Close (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c).card ≤ B
  · exact Or.inr hcard
  · obtain ⟨D', hD', v, hvC, hag⟩ :=
      hca _ (Nat.lt_of_not_ge hcard) fun _ hz => (mem_filter.1 hz).2
    exact Or.inl fun z => ⟨∑ j : Fin (d + 1), z ^ (j : ℕ) • v j,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvC j), hgood hD' hag z⟩

private theorem line_dichotomy_of_ca {F ι : Type*} [Field F] [Fintype F]
    {C : Submodule F (ι → F)} {u₀ u₁ : ι → F}
    (Close : (ι → F) → (ι → F) → Prop) (Good : Finset ι → Prop) {B : ℕ}
    (hgood : ∀ {D' : Finset ι}, Good D' → ∀ {v₀ v₁ : ι → F},
      (∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i) → ∀ z : F, Close (u₀ + z • u₁) (v₀ + z • v₁))
    [DecidablePred fun z : F => ∃ c ∈ C, Close (u₀ + z • u₁) c]
    (hca : ∀ S : Finset F, B < S.card →
      (∀ z ∈ S, ∃ c ∈ C, Close (u₀ + z • u₁) c) →
      ∃ D' : Finset ι, Good D' ∧ ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i) :
    (∀ z : F, ∃ c ∈ C, Close (u₀ + z • u₁) c) ∨
      (Finset.univ.filter fun z : F => ∃ c ∈ C, Close (u₀ + z • u₁) c).card ≤ B := by
  by_cases hcard : (Finset.univ.filter fun z : F => ∃ c ∈ C, Close (u₀ + z • u₁) c).card ≤ B
  · exact Or.inr hcard
  · obtain ⟨D', hD', v₀, hv₀, v₁, hv₁, hag⟩ :=
      hca _ (Nat.lt_of_not_ge hcard) fun _ hz => (mem_filter.1 hz).2
    exact Or.inl fun z =>
      ⟨v₀ + z • v₁, Submodule.add_mem _ hv₀ (Submodule.smul_mem _ z hv₁), hgood hD' hag z⟩

/-- **Weighted proximity-gap dichotomy on parameterized curves in the unique-decoding regime**
(`ℕ`-weights, `[Fintype F]`): either every curve point has `W`-weighted agreement at least `B`
with `reedSolomon α k`, or at most `d * |ι|` scalars in `F` do. -/
theorem weighted_proximityGap_curve_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F] [Fintype F]
    {α : ι → F} (hα : Function.Injective α)
    {k d M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u : Fin (d + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), W i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), W i) ∨
      (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), W i).card ≤
        d * Fintype.card ι :=
  curve_dichotomy_of_ca (C := reedSolomon α k)
    (fun x c => B ≤ ∑ i ∈ univ.filter (fun i => x i = c i), W i)
    (fun D' => B ≤ ∑ i ∈ D', W i)
    (fun hD' _ hag z => hD'.trans (weightedAgree_curve_ge_of_eq_on W hag z))
    (fun S hS hcl => exists_weighted_correlatedAgreement_curve_unique hα hM hW hunique u S hS hcl)

/-- **Weighted proximity-gap dichotomy on affine lines in the unique-decoding regime**
(`ℕ`-weights, `[Fintype F]`): either every point on `u₀ + z • u₁` achieves `W`-weighted agreement
at least `B` with `reedSolomon α k`, or at most `|ι|` scalars in `F` do. -/
theorem weighted_proximityGap_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F] [Fintype F]
    {α : ι → F} (hα : Function.Injective α)
    {k M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u₀ u₁ : ι → F)
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), W i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), W i) ∨
      (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), W i).card ≤
        Fintype.card ι :=
  line_dichotomy_of_ca (C := reedSolomon α k)
    (fun x c => B ≤ ∑ i ∈ univ.filter (fun i => x i = c i), W i)
    (fun D' => B ≤ ∑ i ∈ D', W i)
    (fun hD' _ _ hag z => hD'.trans (Finset.sum_le_sum_of_subset (subset_filter_line_eq hag z)))
    (fun S hS hcl => exists_weighted_correlatedAgreement_unique hα hM hW hunique u₀ u₁ S hS hcl)

/-- **Weighted proximity-gap dichotomy on parameterized curves in the unique-decoding regime**
(`ℚ`-weights in `[0, 1]`, `[Fintype F]`). -/
theorem ratWeighted_proximityGap_curve_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F] [Fintype F]
    {α : ι → F} (hα : Function.Injective α)
    {e k d : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_nonneg : ∀ i, 0 ≤ μ i) (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u : Fin (d + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), μ i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), μ i) ∨
      (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), μ i).card ≤
        d * Fintype.card ι :=
  curve_dichotomy_of_ca (C := reedSolomon α k)
    (fun x c => θ ≤ ∑ i ∈ univ.filter (fun i => x i = c i), μ i)
    (fun D' => θ ≤ ∑ i ∈ D', μ i)
    (fun hD' _ hag z => hD'.trans (ratWeightedAgree_curve_ge_of_eq_on hμ_nonneg hag z))
    (fun S hS hcl =>
      exists_ratWeighted_correlatedAgreement_curve_unique hα hunique hμ_le hθ u S hS hcl)

/-- **Weighted proximity-gap dichotomy on affine lines in the unique-decoding regime**
(`ℚ`-weights in `[0, 1]`, `[Fintype F]`). -/
theorem ratWeighted_proximityGap_unique
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq F] [Fintype F]
    {α : ι → F} (hα : Function.Injective α)
    {e k : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_nonneg : ∀ i, 0 ≤ μ i) (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u₀ u₁ : ι → F)
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i) ∨
      (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i).card ≤
        Fintype.card ι :=
  line_dichotomy_of_ca (C := reedSolomon α k)
    (fun x c => θ ≤ ∑ i ∈ univ.filter (fun i => x i = c i), μ i)
    (fun D' => θ ≤ ∑ i ∈ D', μ i)
    (fun hD' _ _ hag z => hD'.trans (Finset.sum_le_sum_of_subset_of_nonneg
      (subset_filter_line_eq hag z) fun i _ _ => hμ_nonneg i))
    (fun S hS hcl =>
      exists_ratWeighted_correlatedAgreement_unique hα hunique hμ_le hθ u₀ u₁ S hS hcl)

/-! ### Part 2: Generic affine-space-to-curve reduction (`(Fˣ)^ℓ × Fˣ` bijection) -/

/-- **Generic affine-space-to-curve correlated agreement reduction**:

Given any degree-`ℓ` curve correlated-agreement theorem `hcurve` with scalar threshold `B_curve`
for a pointwise proximity predicate `P : (ι → F) → Prop` and shared-agreement predicate
`Q : Finset ι → Prop`, any affine space `u₀ + ∑ j : Fin ℓ, z j • u j` (`1 ≤ ℓ`) over a finite
field `F` whose good set `T ⊆ (Fin ℓ → F)` satisfies `(B_curve + ℓ) * |F| ^ (ℓ - 1) < #T`
(density strictly greater than `(B_curve + ℓ) / |F|`, linear in `ℓ`) admits a single shared
agreement set `D'` satisfying `Q D'` together with codewords `v₀, v j ∈ reedSolomon α k`.

The proof excludes tuples with a zero coordinate (at most `ℓ * |F| ^ (ℓ - 1)` tuples), averages
over the fiber bijection `(a, t) ↦ (a j * t ^ (j + 1))_j` on `(Fin ℓ → Fˣ) × Fˣ`, applies
`hcurve` along the resulting degree-`ℓ` curve `u₀ + ∑ j, t ^ (j + 1) • (a j • u j)`, and
unscales each recovered codeword by `(a j)⁻¹`. -/
theorem exists_correlatedAgreement_affine_of_curve
    {F : Type*} [Field F] [Fintype F]
    {ι : Type*}
    {α : ι → F} {k ℓ B_curve : ℕ}
    (hℓ : 1 ≤ ℓ)
    {P : (ι → F) → Prop} {Q : Finset ι → Prop}
    (hcurve : ∀ (u' : Fin (ℓ + 1) → (ι → F)) (S : Finset F),
      B_curve < S.card →
      (∀ z ∈ S, P (∑ j : Fin (ℓ + 1), z ^ (j : ℕ) • u' j)) →
      ∃ D' : Finset ι, Q D' ∧
        ∃ v' : Fin (ℓ + 1) → (ι → F), (∀ j, v' j ∈ reedSolomon α k) ∧
          ∀ i ∈ D', ∀ j, u' j i = v' j i)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : (B_curve + ℓ) * (Fintype.card F) ^ (ℓ - 1) < T.card)
    (hclose : ∀ z ∈ T, P (u₀ + ∑ j : Fin ℓ, z j • u j)) :
    ∃ D' : Finset ι, Q D' ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F),
        (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  classical
  let T_nz : Finset (Fin ℓ → F) := T.filter fun z => ∀ j : Fin ℓ, z j ≠ 0
  have hzero_le : (T \ T_nz).card ≤ ℓ * (Fintype.card F) ^ (ℓ - 1) := by
    have hsub : T \ T_nz ⊆ (Finset.univ : Finset (Fin ℓ)).biUnion
        fun j => Finset.univ.filter fun z : Fin ℓ → F => z j = 0 := fun z hz => by
      obtain ⟨hzT, hnz⟩ := mem_sdiff.1 hz
      have hnot : ¬ ∀ j : Fin ℓ, z j ≠ 0 := fun hall => hnz (mem_filter.2 ⟨hzT, hall⟩)
      push Not at hnot; obtain ⟨j, hj⟩ := hnot
      exact mem_biUnion.2 ⟨j, mem_univ j, mem_filter.2 ⟨mem_univ z, hj⟩⟩
    exact (Finset.card_le_card hsub).trans <| Finset.card_biUnion_le.trans_eq <|
      (Finset.sum_congr rfl fun j _ => card_filter_coord_eq_zero j).trans <| by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hT_split : T.card = T_nz.card + (T \ T_nz).card := by
    rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
  have hT_nz : B_curve * (Fintype.card F) ^ (ℓ - 1) < T_nz.card := by
    rw [Nat.add_mul] at hT; omega
  have hFunits_pos : 0 < Fintype.card Fˣ := Fintype.card_pos_iff.2 ⟨1⟩
  have hT_nz_units : B_curve * (Fintype.card Fˣ) ^ ℓ < Fintype.card Fˣ * T_nz.card := by
    have hpow_le : (Fintype.card Fˣ) ^ (ℓ - 1) ≤ (Fintype.card F) ^ (ℓ - 1) :=
      Nat.pow_le_pow_left (Fintype.card_le_of_injective (Units.val : Fˣ → F) Units.val_injective) _
    have hsplit : (Fintype.card Fˣ) ^ ℓ = Fintype.card Fˣ * (Fintype.card Fˣ) ^ (ℓ - 1) := by
      conv_lhs => rw [show ℓ = (ℓ - 1) + 1 by omega, pow_succ, mul_comm]
    rw [hsplit, ← mul_assoc, mul_comm B_curve, mul_assoc]
    exact Nat.mul_lt_mul_of_pos_left ((Nat.mul_le_mul_left _ hpow_le).trans_lt hT_nz) hFunits_pos
  let phi : (Fin ℓ → Fˣ) → Fˣ → (Fin ℓ → F) := fun a t j => (a j : F) * (t : F) ^ ((j : ℕ) + 1)
  have hfiber (t : Fˣ) : (Finset.univ.filter fun a : Fin ℓ → Fˣ => phi a t ∈ T_nz).card =
      T_nz.card :=
    Finset.card_bij (fun a _ => phi a t) (fun _ ha => (mem_filter.1 ha).2)
      (fun _ _ _ _ heq => funext fun j => Units.ext <|
        mul_right_cancel₀ (pow_ne_zero _ t.ne_zero) (congrFun heq j))
      fun z hz =>
        let a : Fin ℓ → Fˣ := fun j =>
          Units.mk0 (z j) ((mem_filter.1 hz).2 j) * (t ^ ((j : ℕ) + 1))⁻¹
        have hphi : phi a t = z := funext fun j => by
          simp only [phi, a, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val,
            Units.val_pow_eq_pow_val, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ t.ne_zero), mul_one]
        ⟨a, mem_filter.2 ⟨mem_univ a, hphi.symm ▸ hz⟩, hphi⟩
  have hsum_lt : (∑ _a : Fin ℓ → Fˣ, B_curve) <
      ∑ a : Fin ℓ → Fˣ, (Finset.univ.filter fun t : Fˣ => phi a t ∈ T_nz).card := by
    have hsum : (∑ a : Fin ℓ → Fˣ, (Finset.univ.filter fun t : Fˣ => phi a t ∈ T_nz).card) =
        Fintype.card Fˣ * T_nz.card := by
      simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
      simp_rw [← Finset.card_filter, hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      smul_eq_mul, mul_comm]
    exact hT_nz_units
  obtain ⟨a, _, ha_gt⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  let S : Finset F := (Finset.univ.filter fun t : Fˣ => phi a t ∈ T_nz).image Units.val
  let u' : Fin (ℓ + 1) → (ι → F) := Fin.cons u₀ fun j => (a j : F) • u j
  obtain ⟨D', hQD', v', hv'RS, hagree'⟩ := hcurve u' S
    (by rwa [Finset.card_image_of_injective _ Units.val_injective]) fun z hz => by
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hz
      have hsum : (∑ j : Fin (ℓ + 1), (t : F) ^ (j : ℕ) • u' j) =
          u₀ + ∑ j : Fin ℓ, phi a t j • u j := by
        rw [Fin.sum_univ_succ]; simp only [u', Fin.val_zero, pow_zero, one_smul, Fin.cons_zero,
          Fin.val_succ, Fin.cons_succ]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [smul_smul, mul_comm])
      rw [hsum]; exact hclose (phi a t) (mem_filter.1 (mem_filter.1 ht).2).1
  refine ⟨D', hQD', v' 0, hv'RS 0, fun j => (a j : F)⁻¹ • v' j.succ,
    fun j => Submodule.smul_mem _ _ (hv'RS j.succ), fun i hi =>
      ⟨by simpa only [u', Fin.cons_zero] using hagree' i hi 0, fun j => ?_⟩⟩
  have hs : (a j : F) * u j i = v' j.succ i := by
    simpa only [u', Fin.cons_succ, Pi.smul_apply, smul_eq_mul] using hagree' i hi j.succ
  simp only [Pi.smul_apply, smul_eq_mul, ← hs, inv_mul_cancel_left₀ (a j).ne_zero]

/-! ### Part 3: Dimension-independent affine-space proximity gaps (zero `ℓ` factor) -/

/-- **Generic 1D-line-to-affine-space proximity-gap dichotomy (dimension-independent)**:

Given any pointwise predicate `P : (ι → F) → Prop` satisfying a 1D line dichotomy with threshold
`B_line` (whenever strictly more than `B_line` points on a line `a + t • b` satisfy `P`, every
point on the line satisfies `P`), every `ℓ`-dimensional affine space `u₀ + ∑ j : Fin ℓ, z j • u j`
over a finite field `F` satisfies either:
* every point of the affine space satisfies `P`, or
* `(|F| - 1) * #{z | P (u₀ + ∑ j, z j • u j)} ≤ B_line * (|F| ^ ℓ - 1)`.

For `ℓ = 1` this recovers `#T ≤ B_line` exactly; for all `ℓ ≥ 1` the density bound is at most
`B_line / (|F| - 1)`, completely independent of the dimension `ℓ`. -/
theorem proximityGap_affine_of_line
    {F : Type*} [Field F] [Fintype F]
    {ι : Type*}
    {ℓ B_line : ℕ}
    {P : (ι → F) → Prop}
    (hline : ∀ (a b : ι → F) (S : Finset F),
      B_line < S.card → (∀ t ∈ S, P (a + t • b)) → ∀ t : F, P (a + t • b))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => P (u₀ + ∑ j : Fin ℓ, z j • u j)] :
    (∀ z : Fin ℓ → F, P (u₀ + ∑ j : Fin ℓ, z j • u j)) ∨
      (Fintype.card F - 1) *
        (Finset.univ.filter fun z : Fin ℓ → F => P (u₀ + ∑ j : Fin ℓ, z j • u j)).card ≤
        B_line * ((Fintype.card F) ^ ℓ - 1) := by
  classical
  by_cases hall : ∀ z : Fin ℓ → F, P (u₀ + ∑ j : Fin ℓ, z j • u j)
  · exact Or.inl hall
  · right
    push Not at hall; obtain ⟨y, hy⟩ := hall
    set T := Finset.univ.filter fun z : Fin ℓ → F => P (u₀ + ∑ j : Fin ℓ, z j • u j)
    let B_nz : Finset (Fin ℓ → F) := Finset.univ.erase 0
    have hB_nz_card : B_nz.card = (Fintype.card F) ^ ℓ - 1 := by
      rw [Finset.card_erase_of_mem (mem_univ 0), Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin]
    let pairs := (B_nz ×ˢ (Finset.univ : Finset Fˣ)).filter fun p => y + (p.2 : F) • p.1 ∈ T
    have hpairs_eq : pairs.card = (Fintype.card F - 1) * T.card := by
      have hbij : pairs.card = (T ×ˢ (Finset.univ : Finset Fˣ)).card :=
        Finset.card_bij (fun p _ => (y + (p.2 : F) • p.1, p.2))
          (fun p hp => mem_product.2 ⟨(mem_filter.1 hp).2, mem_univ p.2⟩)
          (fun p₁ _ p₂ _ heq => by
            obtain ⟨h1, h2⟩ := Prod.mk.inj heq; rw [h2] at h1
            exact Prod.ext (funext fun j => mul_left_cancel₀ p₂.2.ne_zero
              (congrFun (add_left_cancel h1) j)) h2)
          fun q hq => by
            let b : Fin ℓ → F := ((q.2⁻¹ : Fˣ) : F) • (q.1 - y)
            have hyb : y + (q.2 : F) • b = q.1 := by
              simp only [b, smul_smul, Units.mul_inv, one_smul, add_sub_cancel]
            have hb_ne : b ≠ 0 := fun h0 => hy <| (mem_filter.1 (mem_product.1 hq).1).2 |>
              fun hp => (by simpa only [h0, smul_zero, add_zero] using hyb) ▸ hp
            exact ⟨(b, q.2), mem_filter.2 ⟨mem_product.2 ⟨mem_erase.2 ⟨hb_ne, mem_univ _⟩,
              mem_univ _⟩, hyb.symm ▸ (mem_product.1 hq).1⟩, Prod.ext hyb rfl⟩
      rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_units, Nat.mul_comm]
    have hline_eval (b : Fin ℓ → F) (t : F) : u₀ + ∑ j : Fin ℓ, (y + t • b) j • u j =
        (u₀ + ∑ j : Fin ℓ, y j • u j) + t • (∑ j : Fin ℓ, b j • u j) := by
      funext i
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]
    have hfiber_le (b : Fin ℓ → F) :
        ((Finset.univ : Finset Fˣ).filter fun t : Fˣ => y + (t : F) • b ∈ T).card ≤ B_line := by
      by_contra hgt
      set S := ((Finset.univ : Finset Fˣ).filter fun t : Fˣ => y + (t : F) • b ∈ T).image Units.val
      have h0 := hline _ (∑ j : Fin ℓ, b j • u j) S
        (by rw [Finset.card_image_of_injective _ Units.val_injective]; omega)
        (fun t ht => by
          obtain ⟨tu, htu, rfl⟩ := mem_image.1 ht
          exact (hline_eval b tu) ▸ (mem_filter.1 (mem_filter.1 htu).2).2) 0
      exact hy (by rwa [zero_smul, add_zero] at h0)
    have hsum_eq : pairs.card = ∑ b ∈ B_nz,
        ((Finset.univ : Finset Fˣ).filter fun t : Fˣ => y + (t : F) • b ∈ T).card := by
      rw [Finset.card_filter, Finset.sum_product]; simp_rw [Finset.card_filter]
    have hpairs_le := hsum_eq ▸ (Finset.sum_le_sum fun b _ => hfiber_le b).trans_eq (by
      rw [Finset.sum_const, smul_eq_mul, hB_nz_card, Nat.mul_comm])
    omega

/-- Private helper: a nonzero affine linear functional on `Fin ℓ → F` vanishes on at most
`|F| ^ (ℓ - 1)` points. -/
private theorem card_zero_affine_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ℓ : ℕ}
    (a₀ : F) (a : Fin ℓ → F)
    (hne : a₀ ≠ 0 ∨ ∃ j : Fin ℓ, a j ≠ 0) :
    (Finset.univ.filter fun z : Fin ℓ → F => a₀ + ∑ j : Fin ℓ, z j * a j = 0).card ≤
      (Fintype.card F) ^ (ℓ - 1) := by
  classical
  set S := Finset.univ.filter fun z : Fin ℓ → F => a₀ + ∑ j : Fin ℓ, z j * a j = 0
  by_cases hall0 : ∀ j : Fin ℓ, a j = 0
  · have ha₀ := hne.resolve_right (by push Not; exact hall0)
    have hemp : S = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun z hz =>
      ha₀ <| by simpa [hall0] using (mem_filter.1 hz).2
    simp [hemp]
  · push Not at hall0; obtain ⟨j₀, hj₀⟩ := hall0
    let proj : (Fin ℓ → F) → ({j : Fin ℓ // j ≠ j₀} → F) := fun z j => z j.1
    have hinj : Set.InjOn proj (S : Set (Fin ℓ → F)) := fun z₁ hz₁ z₂ hz₂ hproj => by
      have hne_eq : ∀ j : Fin ℓ, j ≠ j₀ → z₁ j = z₂ j := fun j hj => congrFun hproj ⟨j, hj⟩
      have h1 := (mem_filter.1 hz₁).2; have h2 := (mem_filter.1 hz₂).2
      rw [← Finset.add_sum_erase _ _ (mem_univ j₀)] at h1 h2
      have hsum : ∑ j ∈ Finset.univ.erase j₀, z₁ j * a j =
          ∑ j ∈ Finset.univ.erase j₀, z₂ j * a j :=
        Finset.sum_congr rfl fun j hj => by rw [hne_eq j (mem_erase.1 hj).1]
      have hz₀ : z₁ j₀ = z₂ j₀ := sub_eq_zero.1 <|
        (mul_eq_zero.1 (by rw [hsum] at h1; linear_combination h1 - h2)).resolve_right hj₀
      exact funext fun j => if hj : j = j₀ then hj ▸ hz₀ else hne_eq j hj
    have hcard_sub : Fintype.card {j : Fin ℓ // j ≠ j₀} = ℓ - 1 := by
      simpa only [Fintype.card_fin, Fintype.card_unique] using
        Fintype.card_subtype_compl (fun j : Fin ℓ => j = j₀)
    exact (Finset.card_image_of_injOn hinj).symm ▸ (Finset.card_le_univ _).trans_eq (by
      rw [Fintype.card_fun, hcard_sub])

/-- Private helper: the parameters `z` at which some disagreeing coordinate `i ∈ badI` of two
affine spaces collides lie in a union of nonzero affine zero sets, so there are at most
`|ι| · |F| ^ (ℓ - 1)` of them. -/
private theorem card_biUnion_zero_affine_le
    {ι F : Type*} [Fintype ι] [Field F] [Fintype F] [DecidableEq F] {ℓ : ℕ}
    (u₀ v₀ : ι → F) (u v : Fin ℓ → ι → F) (badI : Finset ι)
    (hbad : ∀ i ∈ badI, ¬ (u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i)) :
    (badI.biUnion fun i => Finset.univ.filter fun z : Fin ℓ → F =>
        (u₀ i - v₀ i) + ∑ j : Fin ℓ, z j * (u j i - v j i) = 0).card ≤
      Fintype.card ι * (Fintype.card F) ^ (ℓ - 1) := by
  calc _ ≤ ∑ i ∈ badI, (Finset.univ.filter fun z : Fin ℓ → F =>
          (u₀ i - v₀ i) + ∑ j : Fin ℓ, z j * (u j i - v j i) = 0).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ badI, (Fintype.card F) ^ (ℓ - 1) := by
        refine Finset.sum_le_sum fun i hi => card_zero_affine_le _ _ ?_
        by_cases h0 : u₀ i = v₀ i
        · right
          have hnotj : ¬ ∀ j : Fin ℓ, u j i = v j i := fun hj => hbad i hi ⟨h0, hj⟩
          push Not at hnotj
          obtain ⟨j, hj⟩ := hnotj
          exact ⟨j, sub_ne_zero.2 hj⟩
        · exact Or.inl (sub_ne_zero.2 h0)
    _ = badI.card * (Fintype.card F) ^ (ℓ - 1) := by simp only [Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card ι * (Fintype.card F) ^ (ℓ - 1) :=
        Nat.mul_le_mul_right _ (Finset.card_le_univ badI)

/-- Private helper: the exact affine density threshold `K * |F| ^ ℓ < |F| * #T` for
`T ⊆ (Fin ℓ → F)` forces `K < |F|`. -/
private theorem lt_card_field_of_density_threshold
    {F : Type*} [Fintype F] {K ℓ : ℕ} {T : Finset (Fin ℓ → F)}
    (hT : K * (Fintype.card F) ^ ℓ < Fintype.card F * T.card) :
    K < Fintype.card F := by
  have hT_le : T.card ≤ (Fintype.card F) ^ ℓ := by
    calc T.card ≤ Fintype.card (Fin ℓ → F) := Finset.card_le_univ T
      _ = (Fintype.card F) ^ ℓ := by
          rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact Nat.lt_of_mul_lt_mul_right (hT.trans_le (Nat.mul_le_mul_left _ hT_le))

/-! ### Part 4: Generic Section 6.3 / 7.3 affine correlated-agreement lift -/

/-- Private helper: any proper `F`-submodule of `Fin ℓ → F` has cardinality at most
`|F| ^ (ℓ - 1)`. -/
private theorem card_submodule_le_pow_pred_of_ne_top
    {F : Type*} [Field F] [Fintype F] {ℓ : ℕ}
    {K : Submodule F (Fin ℓ → F)} [Fintype K] (hK : K ≠ ⊤) :
    Fintype.card K ≤ (Fintype.card F) ^ (ℓ - 1) := by
  have hlt : Module.finrank F K < Module.finrank F (Fin ℓ → F) := Submodule.finrank_lt hK
  rw [Module.finrank_fin_fun] at hlt
  have hle : Module.finrank F K ≤ ℓ - 1 := by omega
  rw [Module.card_eq_pow_finrank (K := F)]
  exact Nat.pow_le_pow_right Fintype.card_pos hle

private theorem hyperplane_shift_filter_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m : ℕ} {d : Fin m → F} {j₀ : Fin m} (hj₀ : d j₀ ≠ 0) (T : Finset (Fin m → F)) :
    ∑ z ∈ Finset.univ.filter fun z : Fin m → F => z j₀ = 0,
      ((Finset.univ : Finset F).filter fun t => z + t • d ∈ T).card = T.card := by
  let H := Finset.univ.filter fun z : Fin m → F => z j₀ = 0
  have hprod : ((H ×ˢ (Finset.univ : Finset F)).filter fun p => p.1 + p.2 • d ∈ T).card =
      T.card :=
    Finset.card_bij (fun p _ => p.1 + p.2 • d) (fun _ hp => (mem_filter.1 hp).2)
      (fun p₁ hp₁ p₂ hp₂ heq => by
        have h1 : p₁.1 j₀ = 0 := (mem_filter.1 (mem_product.1 (mem_filter.1 hp₁).1).1).2
        have h2 : p₂.1 j₀ = 0 := (mem_filter.1 (mem_product.1 (mem_filter.1 hp₂).1).1).2
        have hj := congrFun heq j₀
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2, zero_add] at hj
        have ht : p₁.2 = p₂.2 := mul_right_cancel₀ hj₀ hj
        exact Prod.ext (add_right_cancel (ht ▸ heq)) ht)
      fun y hyT =>
        let t := y j₀ * (d j₀)⁻¹
        have hzH : y - t • d ∈ H := mem_filter.2 ⟨mem_univ _, by
          simp only [t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_assoc,
            inv_mul_cancel₀ hj₀, mul_one, sub_self]⟩
        ⟨(y - t • d, t), mem_filter.2 ⟨mem_product.2 ⟨hzH, mem_univ t⟩,
          by simpa only [sub_add_cancel] using hyT⟩, sub_add_cancel y _⟩
  rw [← hprod, Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl fun z _ => by rw [Finset.card_filter]

/-- Private helper (parameter-space [BenSassonCarmonIshaiKoppartySaraf2020, Lemma 6.3], printed
pp. 29–30 of the accepted JACM 2023 manuscript): if `B_line * |F| ^ m < |F| * #T` affine parameters
`z ∈ T` have `W`-weighted agreement at least `B_W` with `C`, then every direction word
`∑ j, d j • u j` in the associated linear span also has `W`-weighted agreement at least `B_W` with
`C`. -/
private theorem all_close_dir_of_line_correlatedAgreement
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {C : Submodule F (ι → F)} {W : ι → ℕ} {B_W B_line m : ℕ}
    (hline : ∀ (a b : ι → F) (S : Finset F),
      B_line < S.card →
      (∀ t ∈ S, ∃ c ∈ C, B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), W i) →
      ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
        ∃ w₀ ∈ C, ∃ w₁ ∈ C, ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i)
    (u₀ : ι → F) (u : Fin m → (ι → F))
    (T : Finset (Fin m → F))
    (hT : B_line * (Fintype.card F) ^ m < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + ∑ j : Fin m, z j • u j) i = c i), W i) :
    ∀ d : Fin m → F, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (∑ j : Fin m, d j • u j) i = c i), W i := by
  classical
  obtain ⟨z_ne, hz_ne⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.mul_zero] at hT; exact Nat.not_lt_zero _ hT)
  have hBW_le_tot : B_W ≤ ∑ i : ι, W i :=
    let ⟨_, _, hge⟩ := hclose z_ne hz_ne
    hge.trans (Finset.sum_le_sum_of_subset fun _ _ => mem_univ _)
  intro d
  by_cases hd0 : ∀ j : Fin m, d j = 0
  · refine ⟨0, C.zero_mem, ?_⟩
    rw [show (∑ j : Fin m, d j • u j) = 0 from Finset.sum_eq_zero fun j _ => by
      rw [hd0 j, zero_smul]]
    simpa only [Pi.zero_apply, eq_self, filter_true_of_mem (fun _ _ => trivial)] using hBW_le_tot
  · push Not at hd0; obtain ⟨j₀, hj₀⟩ := hd0
    have hm_pos : 1 ≤ m := Fin.pos j₀
    have hT_gt : B_line * (Fintype.card F) ^ (m - 1) < T.card := Nat.lt_of_mul_lt_mul_left <| by
      calc Fintype.card F * (B_line * (Fintype.card F) ^ (m - 1))
          = B_line * (Fintype.card F) ^ m := by
              conv_rhs => rw [← Nat.sub_add_cancel hm_pos, pow_succ]
              ring
        _ < Fintype.card F * T.card := hT
    let H := Finset.univ.filter fun z : Fin m → F => z j₀ = 0
    have hsum_lt : (∑ _z ∈ H, B_line) <
        ∑ z ∈ H, ((Finset.univ : Finset F).filter fun t => z + t • d ∈ T).card := by
      rw [hyperplane_shift_filter_card hj₀ T, Finset.sum_const, smul_eq_mul,
        card_filter_coord_eq_zero j₀, Nat.mul_comm]
      exact hT_gt
    obtain ⟨z, _, hz_gt⟩ := Finset.exists_lt_of_sum_lt hsum_lt
    obtain ⟨D', hD'_ge, _, _, w₁, hw₁C, hag⟩ :=
      hline (u₀ + ∑ j : Fin m, z j • u j) (∑ j : Fin m, d j • u j)
        ((Finset.univ : Finset F).filter fun t => z + t • d ∈ T) hz_gt fun t ht => by
          have hrew : (u₀ + ∑ j : Fin m, z j • u j) + t • (∑ j : Fin m, d j • u j) =
              u₀ + ∑ j : Fin m, (z + t • d) j • u j := by
            funext i
            simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul,
              Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]
          exact hrew ▸ hclose (z + t • d) (mem_filter.1 ht).2
    exact ⟨w₁, hw₁C, hD'_ge.trans (Finset.sum_le_sum_of_subset fun i hi =>
      mem_filter.2 ⟨mem_univ i, (hag i hi).2⟩)⟩

/-- Private helper (homogenization `Ū = span(U)` of
[BenSassonCarmonIshaiKoppartySaraf2020, Section 6.3], printed p. 30 lines 16–25 of the accepted
JACM 2023 manuscript): lifts 1D line correlated agreement from `B_line * |F| ^ ℓ < |F| * #T` to
weighted proximity across the entire affine space `u₀ + ∑ j, z j • u j`. -/
private theorem all_close_affine_of_line_correlatedAgreement
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {C : Submodule F (ι → F)} {W : ι → ℕ} {B_W B_line ℓ : ℕ}
    (hline : ∀ (a b : ι → F) (S : Finset F),
      B_line < S.card →
      (∀ t ∈ S, ∃ c ∈ C, B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), W i) →
      ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
        ∃ w₀ ∈ C, ∃ w₁ ∈ C, ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : B_line * (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∀ z : Fin ℓ → F, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i := by
  classical
  have hdir := all_close_dir_of_line_correlatedAgreement hline u₀ u T hT hclose
  let u' : Fin (ℓ + 1) → (ι → F) := Fin.cons (α := fun _ => ι → F) u₀ u
  let consF : F → (Fin ℓ → F) → (Fin (ℓ + 1) → F) := Fin.cons (α := fun _ => F)
  let T₀ : Finset (Fin (ℓ + 1) → F) := (Finset.univ : Finset (Fin ℓ → F)).image (consF 0)
  let T₁ : Finset (Fin (ℓ + 1) → F) :=
    ((Finset.univ : Finset Fˣ) ×ˢ T).image fun p => consF (p.1 : F) ((p.1 : F) • p.2)
  have hT₀_card : T₀.card = (Fintype.card F) ^ ℓ := by
    have hinj : Function.Injective (consF 0) := fun _ _ h => funext fun j => by
      simpa only [consF, Fin.cons_succ] using congrFun h j.succ
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hT₁_card : T₁.card = (Fintype.card F - 1) * T.card := by
    have hinj : Function.Injective (fun p : Fˣ × (Fin ℓ → F) =>
        consF (p.1 : F) ((p.1 : F) • p.2)) := fun p₁ p₂ h => by
      have hs : (p₁.1 : F) = p₂.1 := by simpa only [consF, Fin.cons_zero] using congrFun h 0
      exact Prod.ext (Units.ext hs) (funext fun j => mul_left_cancel₀ p₂.1.ne_zero (by
        simpa only [consF, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, hs] using congrFun h j.succ))
    rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ,
      Fintype.card_units]
  have hdisj : Disjoint T₀ T₁ := Finset.disjoint_left.2 fun _ hx₀ hx₁ => by
    obtain ⟨_, _, rfl⟩ := mem_image.1 hx₀; obtain ⟨p, _, hp⟩ := mem_image.1 hx₁
    exact p.1.ne_zero (by simpa only [consF, Fin.cons_zero] using congrFun hp 0)
  have hT_bar_gt : B_line * (Fintype.card F) ^ (ℓ + 1) < Fintype.card F * (T₀ ∪ T₁).card := by
    have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have h1 := Nat.mul_lt_mul_of_pos_right (lt_card_field_of_density_threshold hT)
      (Nat.pow_pos (Fintype.card_pos (α := F)) (n := ℓ))
    have h2 := Nat.mul_le_mul_left (Fintype.card F - 1) hT.le
    rw [Finset.card_union_of_disjoint hdisj, hT₀_card, hT₁_card]
    calc B_line * (Fintype.card F) ^ (ℓ + 1)
        = (1 + (Fintype.card F - 1)) * (B_line * (Fintype.card F) ^ ℓ) := by
          rw [show 1 + (Fintype.card F - 1) = Fintype.card F by omega, pow_succ]; ring
      _ = B_line * (Fintype.card F) ^ ℓ +
            (Fintype.card F - 1) * (B_line * (Fintype.card F) ^ ℓ) := by ring
      _ < _ := Nat.add_lt_add_of_lt_of_le h1 h2
      _ = Fintype.card F * ((Fintype.card F) ^ ℓ + (Fintype.card F - 1) * T.card) := by ring
  have hall := all_close_dir_of_line_correlatedAgreement hline 0 u' (T₀ ∪ T₁) hT_bar_gt
    fun x hx => by
    rw [zero_add]
    rcases mem_union.1 hx with hx₀ | hx₁
    · obtain ⟨d, _, rfl⟩ := mem_image.1 hx₀
      simpa only [Fin.sum_univ_succ, u', consF, Fin.cons_zero, Fin.cons_succ, zero_smul,
        zero_add] using hdir d
    · obtain ⟨p, hp, rfl⟩ := mem_image.1 hx₁
      obtain ⟨c, hcC, hge⟩ := hclose p.2 (mem_product.1 hp).2
      refine ⟨(p.1 : F) • c, C.smul_mem _ hcC, ?_⟩
      have hfilt : (Finset.univ.filter fun i =>
            (∑ k : Fin (ℓ + 1), consF (p.1 : F) ((p.1 : F) • p.2) k • u' k) i =
              ((p.1 : F) • c) i) =
          Finset.univ.filter fun i => (u₀ + ∑ j : Fin ℓ, p.2 j • u j) i = c i := by
        ext i
        simp only [mem_filter, mem_univ, true_and, Fin.sum_univ_succ, u', consF, Fin.cons_zero,
          Fin.cons_succ, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.add_apply, mul_assoc,
          ← Finset.mul_sum, ← mul_add, mul_right_inj' p.1.ne_zero]
      rwa [hfilt]
  intro z
  simpa only [Fin.sum_univ_succ, u', consF, Fin.cons_zero, Fin.cons_succ, one_smul] using
    hall (consF 1 z)

/-- Submodule of affine directions `d : Fin ℓ → F` whose combination `∑ j, d j • u j` agrees with
some codeword of `C` on `D`. -/
private def agreeDirSubmodule {F ι : Type*} [Field F] {ℓ : ℕ}
    (C : Submodule F (ι → F)) (u : Fin ℓ → (ι → F)) (D : Finset ι) :
    Submodule F (Fin ℓ → F) where
  carrier := {d | ∃ w ∈ C, ∀ i ∈ D, (∑ j : Fin ℓ, d j • u j) i = w i}
  zero_mem' := ⟨0, C.zero_mem, fun _ _ => by simp⟩
  add_mem' := by
    rintro d₁ d₂ ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
    refine ⟨w₁ + w₂, C.add_mem hw₁ hw₂, fun i hi => ?_⟩
    have hadd : (∑ j : Fin ℓ, (d₁ + d₂) j • u j) i =
        (∑ j : Fin ℓ, d₁ j • u j) i + (∑ j : Fin ℓ, d₂ j • u j) i := by
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        Finset.sum_add_distrib]
    rw [hadd, h₁ i hi, h₂ i hi, Pi.add_apply]
  smul_mem' := by
    rintro a d ⟨w, hw, h⟩
    refine ⟨a • w, C.smul_mem a hw, fun i hi => ?_⟩
    simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_assoc, Finset.mul_sum] using
      congrArg (a * ·) (h i hi)

/-- Any finite subset of a weight-maximized agreement set on `supp W` contains the entire
support-filtered agreement set. -/
private theorem suppW_agree_subset_of_sum_le {ι : Type*} [Fintype ι]
    {F : Type*} [DecidableEq F] {W : ι → ℕ} {u₀ w₀ : ι → F} {D_z : Finset ι} {B : ℕ}
    (hDz_sub : ∀ i ∈ D_z, u₀ i = w₀ i) (hDz_ge : B ≤ ∑ i ∈ D_z, W i)
    (hmax : ∑ i ∈ Finset.univ.filter (fun i => u₀ i = w₀ i), W i ≤ B) :
    (Finset.univ.filter fun i => W i ≠ 0).filter (fun i => u₀ i = w₀ i) ⊆ D_z := by
  classical
  intro i₀ hi₀; by_contra hi₀_not
  have hsupp (X : Finset ι) : ∑ i ∈ X ∩ Finset.univ.filter (fun i => W i ≠ 0), W i =
      ∑ i ∈ X, W i := Finset.sum_subset Finset.inter_subset_left fun i hiX hnot =>
    by_contra fun hne => hnot (mem_inter.2 ⟨hiX, mem_filter.2 ⟨mem_univ i, hne⟩⟩)
  set Dstar := (Finset.univ.filter fun i => W i ≠ 0).filter fun i => u₀ i = w₀ i
  have hsub : D_z ∩ Finset.univ.filter (fun i => W i ≠ 0) ⊆ Dstar.erase i₀ := fun i hi =>
    let ⟨hiDz, hiS⟩ := mem_inter.1 hi
    mem_erase.2 ⟨fun heq => hi₀_not (heq ▸ hiDz), mem_filter.2 ⟨hiS, hDz_sub i hiDz⟩⟩
  have hsum_er := hsupp D_z ▸ Finset.sum_le_sum_of_subset hsub
  have hsplit : W i₀ + ∑ i ∈ Dstar.erase i₀, W i =
      ∑ i ∈ Finset.univ.filter (fun i => u₀ i = w₀ i), W i := by
    rw [Finset.add_sum_erase Dstar W hi₀]
    rw [show Dstar = (Finset.univ.filter fun i => u₀ i = w₀ i) ∩
      Finset.univ.filter (fun i => W i ≠ 0) by
      ext i; simp only [Dstar, mem_filter, mem_inter, mem_univ, true_and, and_comm], hsupp]
  have hW_pos : 0 < W i₀ := Nat.pos_of_ne_zero (mem_filter.1 (mem_filter.1 hi₀).1).2
  omega

/-- If `Fin ℓ → F` (`1 ≤ ℓ`) is covered by `L < |F|` translates of `F`-submodules, one of those
submodules is `⊤`. -/
private theorem exists_submodule_eq_top_of_cover {F : Type*} [Field F] [Fintype F]
    {α : Type*} {ℓ L : ℕ} (hℓ : 1 ≤ ℓ) (hL : L < Fintype.card F)
    {L_star : Finset α} (hLne : L_star.Nonempty) (hLcard : L_star.card ≤ L)
    (z_star : Fin ℓ → F) (K : α → Submodule F (Fin ℓ → F))
    (hcover : ∀ z : Fin ℓ → F, ∃ c ∈ L_star, z - z_star ∈ K c) :
    ∃ c ∈ L_star, K c = ⊤ := by
  classical
  let U : α → Finset (Fin ℓ → F) := fun c => Finset.univ.filter fun z => z - z_star ∈ K c
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image L_star (fun c => (U c).card) hLne
  refine ⟨c, hc, by_contra fun hne => ?_⟩
  have hU_pos : 0 < (U c).card := Finset.card_pos.2
    ⟨z_star, mem_filter.2 ⟨mem_univ _, by rw [sub_self]; exact (K c).zero_mem⟩⟩
  have hU_eq : (U c).card = Fintype.card (K c) := by
    rw [← Finset.card_univ]
    exact Finset.card_bij (fun z hz => (⟨z - z_star, (mem_filter.1 hz).2⟩ : K c))
      (fun _ _ => mem_univ _)
      (fun _ _ _ _ h => sub_left_inj.1 (Subtype.ext_iff.1 h))
      fun d _ => ⟨d.1 + z_star, mem_filter.2 ⟨mem_univ _, by rw [add_sub_cancel_right]; exact d.2⟩,
        Subtype.ext (add_sub_cancel_right _ _)⟩
  have hpigeon : (Fintype.card F) ^ ℓ ≤ L * (U c).card := calc
    (Fintype.card F) ^ ℓ = (Finset.univ : Finset (Fin ℓ → F)).card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    _ ≤ (L_star.biUnion U).card := Finset.card_le_card fun z _ =>
        let ⟨a, ha, hm⟩ := hcover z; mem_biUnion.2 ⟨a, ha, mem_filter.2 ⟨mem_univ z, hm⟩⟩
    _ ≤ ∑ a ∈ L_star, (U a).card := Finset.card_biUnion_le
    _ ≤ L_star.card * (U c).card :=
        (Finset.sum_le_sum fun a ha => hmax a ha).trans_eq (by simp)
    _ ≤ L * (U c).card := Nat.mul_le_mul_right _ hLcard
  have hpow : (Fintype.card F) ^ ℓ = Fintype.card F * (Fintype.card F) ^ (ℓ - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hℓ, pow_succ, Nat.mul_comm]
  have hlt := Nat.mul_lt_mul_of_pos_right hL hU_pos
  have hle := Nat.mul_le_mul_left (Fintype.card F)
    (hU_eq.trans_le (card_submodule_le_pow_pred_of_ne_top hne))
  omega

/-- **Generic divergence-and-subspace lift from everywhere-close affine spaces to simultaneous
weighted correlated agreement** ([BenSassonCarmonIshaiKoppartySaraf2020], Section 6.3 on printed
pp. 30–31 and Section 7.3 on printed p. 34 of the accepted JACM 2023 manuscript, refined for zero
coordinate weights).

Given any linear code `C : Submodule F (ι → F)` over a finite field `F` with codeword list-size
bound `L` at `W`-weighted agreement `B_W` (`2 ≤ ℓ → L < |F|`) and full-line weighted correlated
agreement for every threshold `B' ≥ B_W`: if every point of `u₀ + ∑ j : Fin ℓ, z j • u j` achieves
`W`-weighted agreement at least `B_W` with `C`, then there exist a single subset `D' ⊆ supp W`
(`∀ i ∈ D', W i ≠ 0`) with `B_W ≤ ∑ i ∈ D', W i` and codewords `v₀, v_j ∈ C` agreeing with
`u₀, u_j` on `D'`.

Intersecting candidate agreement sets at the minimal-agreement point `u*` with `supp W` repairs
Section 7.3's "verbatim" claim on printed p. 34 when `W` has zero entries. Defining the direction
subspace directly via `C`'s restriction image lets this generic linear-code lemma avoid the unique
extension from `D'` used on printed p. 31 (for Reed–Solomon codes under Theorem 7.4, `α > ρ` makes
that extension available). The support guarantee `∀ i ∈ D', W i ≠ 0` is exported here and dropped
by the Reed–Solomon specializations. -/
theorem exists_weighted_correlatedAgreement_affine_of_divergence
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {C : Submodule F (ι → F)} {W : ι → ℕ} {B_W L ℓ : ℕ}
    (hlist : ∀ u : ι → F, ∃ Lset : Finset (ι → F), Lset.card ≤ L ∧
      ∀ c ∈ C, B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i → c ∈ Lset)
    (hline_all : ∀ {B' : ℕ}, B_W ≤ B' → ∀ a b : ι → F,
      (∀ t : F, ∃ c ∈ C,
        B' ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), W i) →
      ∃ D' : Finset ι, B' ≤ ∑ i ∈ D', W i ∧
        ∃ w₀ ∈ C, ∃ w₁ ∈ C, ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i)
    (hL : 2 ≤ ℓ → L < Fintype.card F)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (hall : ∀ z : Fin ℓ → F, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, (∀ i ∈ D', W i ≠ 0) ∧ B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ C, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ C) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  classical
  let suppW := Finset.univ.filter fun i : ι => W i ≠ 0
  have hsum_supp (X : Finset ι) : ∑ i ∈ X ∩ suppW, W i = ∑ i ∈ X, W i :=
    Finset.sum_subset Finset.inter_subset_left fun i hiX hnot =>
      by_contra fun hne => hnot (mem_inter.2 ⟨hiX, mem_filter.2 ⟨mem_univ i, hne⟩⟩)
  match ℓ with
  | 0 =>
    obtain ⟨v₀, hv₀, hge⟩ := hall 0
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hge
    exact ⟨(Finset.univ.filter fun i => u₀ i = v₀ i) ∩ suppW,
      fun _ hi => (mem_filter.1 (mem_inter.1 hi).2).2,
      by rw [hsum_supp]; exact hge, v₀, hv₀, Fin.elim0,
      fun j => j.elim0, fun _ hi => ⟨(mem_filter.1 (mem_inter.1 hi).1).2, fun j => j.elim0⟩⟩
  | 1 =>
    obtain ⟨D₀, hD₀, v₀, hv₀, v₁, hv₁, hag⟩ := hline_all le_rfl u₀ (u 0) fun t => by
      simpa only [Fin.sum_univ_one] using hall (fun _ => t)
    exact ⟨D₀ ∩ suppW, fun _ hi => (mem_filter.1 (mem_inter.1 hi).2).2,
      by rw [hsum_supp]; exact hD₀,
      v₀, hv₀, fun _ => v₁, fun _ => hv₁, fun i hi =>
      let ⟨h0, h1⟩ := hag i (mem_inter.1 hi).1; ⟨h0, fun j => by fin_cases j; exact h1⟩⟩
  | ℓ' + 2 =>
    let u_aff (z : Fin (ℓ' + 2) → F) := u₀ + ∑ j, z j • u j
    let agreeW (w c : ι → F) := ∑ i ∈ Finset.univ.filter (fun i => w i = c i), W i
    let C_fin := Finset.univ.filter fun c : ι → F => c ∈ C
    have hC_ne : C_fin.Nonempty := ⟨0, mem_filter.2 ⟨mem_univ 0, C.zero_mem⟩⟩
    let score (z : Fin (ℓ' + 2) → F) := C_fin.sup' hC_ne fun c => agreeW (u_aff z) c
    obtain ⟨z_star, _, hz_min⟩ := Finset.exists_min_image Finset.univ score ⟨0, mem_univ 0⟩
    set B_star := score z_star; set u_star := u_aff z_star
    have hBW_le_Bstar : B_W ≤ B_star :=
      let ⟨c₀, hc₀, hge⟩ := hall z_star
      hge.trans (Finset.le_sup' (fun c => agreeW u_star c) (mem_filter.2 ⟨mem_univ c₀, hc₀⟩))
    have hall_Bstar (z : Fin (ℓ' + 2) → F) : ∃ c ∈ C, B_star ≤ agreeW (u_aff z) c :=
      let ⟨c, hc, hce⟩ := Finset.exists_mem_eq_sup' hC_ne fun c => agreeW (u_aff z) c
      ⟨c, (mem_filter.1 hc).2, hce ▸ hz_min z (mem_univ z)⟩
    obtain ⟨Lraw, hLraw_card, hLraw_mem⟩ := hlist u_star
    let L_star := Lraw.filter fun c => c ∈ C ∧ B_star ≤ agreeW u_star c
    have hLstar_ne : L_star.Nonempty := let ⟨c, hc, hge⟩ := hall_Bstar z_star
      ⟨c, mem_filter.2 ⟨hLraw_mem c hc (hBW_le_Bstar.trans hge), hc, hge⟩⟩
    let D_star (c : ι → F) := suppW.filter fun i => u_star i = c i
    obtain ⟨v_star, hv_mem, hK_top⟩ := exists_submodule_eq_top_of_cover (by omega)
      (hL (by omega)) hLstar_ne ((Finset.card_filter_le _ _).trans hLraw_card) z_star
      (fun c => agreeDirSubmodule C u (D_star c)) fun z => by
        let b_dir : ι → F := ∑ j, (z - z_star) j • u j
        obtain ⟨D_z, hDz_ge, w₀, hw₀C, w₁, hw₁C, hag_z⟩ :=
          hline_all hBW_le_Bstar u_star b_dir fun t => by
            have hcomb : u_star + t • b_dir = u_aff (z_star + t • (z - z_star)) := by
              funext i
              simp only [u_star, u_aff, b_dir, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
                Finset.sum_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
                mul_assoc, add_assoc]
            exact hcomb ▸ hall_Bstar (z_star + t • (z - z_star))
        have hw₀_ge : B_star ≤ agreeW u_star w₀ := hDz_ge.trans <|
          Finset.sum_le_sum_of_subset fun i hi => mem_filter.2 ⟨mem_univ i, (hag_z i hi).1⟩
        have hsub := suppW_agree_subset_of_sum_le (fun i hi => (hag_z i hi).1) hDz_ge <|
          Finset.le_sup' (fun c => agreeW u_star c) (mem_filter.2 ⟨mem_univ w₀, hw₀C⟩)
        exact ⟨w₀, mem_filter.2 ⟨hLraw_mem w₀ hw₀C (hBW_le_Bstar.trans hw₀_ge), hw₀C, hw₀_ge⟩,
          w₁, hw₁C, fun i hi => (hag_z i (hsub hi)).2⟩
    have hmem_K (d : Fin (ℓ' + 2) → F) :
        ∃ w ∈ C, ∀ i ∈ D_star v_star, (∑ j, d j • u j) i = w i := by
      have : d ∈ agreeDirSubmodule C u (D_star v_star) := hK_top ▸ Submodule.mem_top
      exact this
    have hex_j (j : Fin (ℓ' + 2)) : ∃ vj ∈ C, ∀ i ∈ D_star v_star, u j i = vj i := by
      obtain ⟨vj, hvj, hag⟩ := hmem_K (Pi.single j 1)
      refine ⟨vj, hvj, fun i hi => ?_⟩
      have hsingle : (∑ r : Fin (ℓ' + 2), Pi.single (M := fun _ => F) j (1 : F) r • u r) = u j := by
        rw [Finset.sum_eq_single j (fun r _ hr => by simp [Pi.single_eq_of_ne hr])
          (fun h => absurd (mem_univ j) h), Pi.single_eq_same, one_smul]
      rw [← hsingle]; exact hag i hi
    choose v hvC hv_ag using hex_j
    obtain ⟨w_neg, hw_negC, hag_neg⟩ := hmem_K (-z_star)
    have hD_sum : ∑ i ∈ D_star v_star, W i = agreeW u_star v_star := by
      rw [show D_star v_star = (Finset.univ.filter fun i => u_star i = v_star i) ∩ suppW by
        ext i; simp only [D_star, mem_inter, mem_filter, mem_univ, true_and, and_comm], hsum_supp]
    refine ⟨D_star v_star, fun _ hi => (mem_filter.1 (mem_filter.1 hi).1).2,
      hD_sum ▸ hBW_le_Bstar.trans (mem_filter.1 hv_mem).2.2, v_star + w_neg,
      C.add_mem (mem_filter.1 hv_mem).2.1 hw_negC, v, hvC, fun i hi => ⟨?_, fun j => hv_ag j i hi⟩⟩
    have h0 : u₀ i = u_star i + (∑ j, (-z_star) j • u j) i := by
      simp only [u_star, u_aff, Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, neg_mul, Finset.sum_neg_distrib, add_neg_cancel_right]
    exact h0.trans <| congrArg₂ (· + ·) (mem_filter.1 hi).2 (hag_neg i hi)

/-- **Dimension-independent lift of 1D weighted line correlated agreement to arbitrary-dimensional
affine spaces** ([BenSassonCarmonIshaiKoppartySaraf2020], Lemma 6.3, Section 6.3 on printed
pp. 29–31, and Section 7.3 on printed p. 34 of the accepted JACM 2023 manuscript).

Given any linear code `C : Submodule F (ι → F)`, coordinate weights `W : ι → ℕ`, threshold `B_W`,
list-size bound `L` (`2 ≤ ℓ → L < |F|`), and 1D weighted line correlated agreement with exceptional
count `≤ B_line` for all thresholds `B' ≥ B_W`: whenever `T ⊆ (Fin ℓ → F)` satisfies
`B_line * |F| ^ ℓ < |F| * #T` (density strictly above `B_line / |F|`, independent of `ℓ`) and every
point in `T` achieves `W`-weighted agreement at least `B_W` with `C`, there exist `D' ⊆ supp W`
with `B_W ≤ ∑ i ∈ D', W i` and codewords `v₀, v_j ∈ C` agreeing with `u₀, u_j` on `D'`. -/
theorem exists_weighted_correlatedAgreement_affine_of_line
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {C : Submodule F (ι → F)} {W : ι → ℕ} {B_W B_line L ℓ : ℕ}
    (hlist : ∀ u : ι → F, ∃ Lset : Finset (ι → F), Lset.card ≤ L ∧
      ∀ c ∈ C, B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i → c ∈ Lset)
    (hline : ∀ {B' : ℕ}, B_W ≤ B' → ∀ (a b : ι → F) (S : Finset F),
      B_line < S.card →
      (∀ t ∈ S, ∃ c ∈ C, B' ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), W i) →
      ∃ D' : Finset ι, B' ≤ ∑ i ∈ D', W i ∧
        ∃ w₀ ∈ C, ∃ w₁ ∈ C, ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i)
    (hL : 2 ≤ ℓ → L < Fintype.card F)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : B_line * (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, (∀ i ∈ D', W i ≠ 0) ∧ B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ C, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ C) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  have hall : ∀ z : Fin ℓ → F, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i :=
    all_close_affine_of_line_correlatedAgreement (fun a b S hS hcl => hline le_rfl a b S hS hcl)
      u₀ u T hT hclose
  exact exists_weighted_correlatedAgreement_affine_of_divergence hlist
    (fun hB' a b hcl =>
      have hB_lt_q : B_line < Fintype.card F := lt_card_field_of_density_threshold hT
      hline hB' a b Finset.univ (by rwa [Finset.card_univ]) (fun t _ => hcl t))
    hL u₀ u hall

/-- **Exact-threshold correlated agreement on affine spaces in the unique-decoding regime, with
unique maximal agreement set and unique codewords**
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.6 & Section 6.3], accepted JACM 2023 manuscript
p. 6 and pp. 28–31, eq. (1.2)).

Over a finite field `F`, given distinct evaluation points `α : ι → F`, `2 * e + k ≤ |ι|`, and an
affine space `u₀ + ∑ j : Fin ℓ, z j • u j`, if `|ι| * |F| ^ ℓ < |F| * #T` (exact density threshold
`#T / |F| ^ ℓ > |ι| / |F| = ε_U` of eq. (1.2), completely independent of `ℓ`) and every `z ∈ T`
lies within Hamming distance `e` of `reedSolomon α k`, then there exist a greatest (hence unique
maximal) shared coordinate subset `D' : Finset ι` of size at least `|ι| - e` and unique codewords
`v₀, v j ∈ reedSolomon α k` matching `u₀, u j` on `D'`: every qualifying `(D'', w₀, w)` satisfies
`D'' ⊆ D'`, `w₀ = v₀`, and `w = v`. -/
theorem exists_uniqueMaximal_correlatedAgreement_affine_unique
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k ℓ : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : Fintype.card ι * (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F),
        (∀ j, v j ∈ reedSolomon α k) ∧
        (∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) ∧
        ∀ (D'' : Finset ι) (w₀ : ι → F) (w : Fin ℓ → (ι → F)),
          Fintype.card ι - e ≤ D''.card →
          w₀ ∈ reedSolomon α k → (∀ j, w j ∈ reedSolomon α k) →
          (∀ i ∈ D'', u₀ i = w₀ i ∧ ∀ j, u j i = w j i) →
          D'' ⊆ D' ∧ w₀ = v₀ ∧ w = v := by
  classical
  have hlist (w : ι → F) : ∃ Lset : Finset (ι → F), Lset.card ≤ 1 ∧
      ∀ c ∈ reedSolomon α k, Fintype.card ι - e ≤
        ∑ i ∈ Finset.univ.filter (fun i => w i = c i), (1 : ℕ) → c ∈ Lset := by
    by_cases hex : ∃ c ∈ reedSolomon α k, hammingDist w c ≤ e
    · exact ⟨{hex.choose}, by simp, fun c hc hs => mem_singleton.2 <|
        eq_of_hammingDist_le_reedSolomon hα hunique hc hex.choose_spec.1
          (hammingDist_le_of_card_filter_eq (by simpa using hs)) hex.choose_spec.2⟩
    · exact ⟨∅, Nat.zero_le 1, fun c hc hs =>
        absurd ⟨c, hc, hammingDist_le_of_card_filter_eq (by simpa using hs)⟩ hex⟩
  have hline : ∀ {B' : ℕ}, Fintype.card ι - e ≤ B' → ∀ (a b : ι → F) (S : Finset F),
      Fintype.card ι < S.card →
      (∀ t ∈ S, ∃ c ∈ reedSolomon α k,
        B' ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), (1 : ℕ)) →
      ∃ D' : Finset ι, B' ≤ ∑ i ∈ D', (1 : ℕ) ∧ ∃ w₀ ∈ reedSolomon α k,
        ∃ w₁ ∈ reedSolomon α k, ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i := fun {B'} hB' a b S hS hcl => by
    obtain ⟨t₀, ht₀⟩ := Finset.card_pos.1 (Nat.zero_lt_of_lt hS)
    have hB'_le : B' ≤ Fintype.card ι := let ⟨_, _, hs⟩ := hcl t₀ ht₀
      (by simpa using hs : B' ≤ _).trans (Finset.card_le_univ _)
    have hsub : Fintype.card ι - (Fintype.card ι - B') = B' := by omega
    obtain ⟨D', hD', w₀, hw₀, w₁, hw₁, hag⟩ := exists_correlatedAgreement_unique hα
      (by omega : 2 * (Fintype.card ι - B') + k ≤ Fintype.card ι) a b S hS
      fun t ht => let ⟨c, hc, hs⟩ := hcl t ht
        ⟨c, hc, hammingDist_le_of_card_filter_eq (hsub.symm ▸ by simpa using hs)⟩
    exact ⟨D', by simpa only [Finset.sum_const, smul_eq_mul, mul_one, hsub] using hD',
      w₀, hw₀, w₁, hw₁, hag⟩
  obtain ⟨D₀, _, hD₀_sum, v₀, hv₀, v, hv, hag₀⟩ :=
    exists_weighted_correlatedAgreement_affine_of_line (C := reedSolomon α k) (W := fun _ => 1)
      (B_W := Fintype.card ι - e) (B_line := Fintype.card ι) (L := 1) hlist hline
      (fun _ => Fintype.one_lt_card) u₀ u T hT fun z hz => let ⟨c, hc, hd⟩ := hclose z hz
        ⟨c, hc, by simpa using card_filter_eq_of_hammingDist_le hd⟩
  obtain ⟨D', hD', v', hv'RS, hagree', hmax'⟩ := exists_uniqueMaximal_correlatedAgreement_of_exists
    hα hunique (u := Fin.cons (α := fun _ => ι → F) u₀ u)
    ⟨D₀, by simpa using hD₀_sum, Fin.cons v₀ v, Fin.cases hv₀ hv,
      fun i hi => Fin.cases (hag₀ i hi).1 (hag₀ i hi).2⟩
  exact ⟨D', hD', v' 0, hv'RS 0, fun j => v' j.succ, fun j => hv'RS j.succ,
    fun i hi => ⟨hagree' i hi 0, fun j => hagree' i hi j.succ⟩,
    fun D'' w₀ w hD'' hw₀ hw hag'' =>
      let ⟨hsub, hweq⟩ := hmax' D'' (Fin.cons w₀ w) hD'' (Fin.cases hw₀ hw)
        fun i hi => Fin.cases (hag'' i hi).1 (hag'' i hi).2
      ⟨hsub, congrFun hweq 0, funext fun j => congrFun hweq j.succ⟩⟩

/-- **Dimension-independent `ℚ`-weighted correlated agreement on affine spaces in the
unique-decoding regime** ([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4]):
At threshold `|ι| * (|F| ^ ℓ - 1) < (|F| - 1) * #T` (completely independent of `ℓ` and weight
denominators), any weight function `μ : ι → ℚ` with `∀ i, μ i ≤ 1` admits shared correlated
agreement `θ ≤ ∑ i ∈ D', μ i`. Handles the one-point `ℓ = 0` case explicitly (including
`|ι| = |F|`), and for `ℓ ≥ 1` delegates the unweighted step to
`Cslib.Code.exists_uniqueMaximal_correlatedAgreement_affine_unique`. -/
theorem exists_ratWeighted_correlatedAgreement_affine_unique_sharp
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k ℓ : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) < (Fintype.card F - 1) * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F),
        (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  classical
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have hpos : 0 < T.card := Nat.pos_of_mul_pos_left
      (by simpa only [pow_zero, tsub_self, mul_zero] using hT)
    obtain ⟨z₀, hz₀⟩ := Finset.card_pos.1 hpos
    obtain ⟨c, hcRS, hμ_ge⟩ := hclose z₀ hz₀
    exact ⟨Finset.univ.filter fun i => u₀ i = c i,
      by simpa only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] using hμ_ge, c, hcRS,
      Fin.elim0, fun j => j.elim0, fun _ hi => ⟨(mem_filter.1 hi).2, fun j => j.elim0⟩⟩
  · have hq_gt1 : 1 < Fintype.card F := Fintype.one_lt_card
    have hpow_pos : 1 ≤ (Fintype.card F) ^ ℓ := Nat.one_le_pow ℓ _ Fintype.card_pos
    have hcard_lt : Fintype.card ι < T.card := Nat.lt_of_mul_lt_mul_right <|
      ((Nat.mul_le_mul_left _ (Nat.sub_le_sub_right
        (Nat.le_self_pow (by omega : ℓ ≠ 0) (Fintype.card F)) 1)).trans_lt hT).trans_eq
        (Nat.mul_comm _ _)
    have hT_exact : Fintype.card ι * (Fintype.card F) ^ ℓ < Fintype.card F * T.card := by
      have h1 : Fintype.card ι * (Fintype.card F) ^ ℓ =
          Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) + Fintype.card ι := by
        calc Fintype.card ι * (Fintype.card F) ^ ℓ
            = Fintype.card ι * ((Fintype.card F) ^ ℓ - 1 + 1) := by
                rw [Nat.sub_add_cancel hpow_pos]
          _ = _ := by ring
      have h2 : Fintype.card F * T.card = (Fintype.card F - 1) * T.card + T.card := by
        calc Fintype.card F * T.card
            = (Fintype.card F - 1 + 1) * T.card := by rw [Nat.sub_add_cancel (by omega)]
          _ = _ := by ring
      omega
    obtain ⟨D₀, hD₀, v₀, hv₀, v, hvRS, hagree₀, _⟩ :=
      exists_uniqueMaximal_correlatedAgreement_affine_unique hα hunique u₀ u T hT_exact
        fun z hz => let ⟨c, hcRS, hμ_ge⟩ := hclose z hz
          ⟨c, hcRS, hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge⟩
    let D' := Finset.univ.filter fun i => u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i
    refine ⟨D', ?_, v₀, hv₀, v, hvRS, fun _ hi => (mem_filter.1 hi).2⟩
    by_contra hlt_θ; push Not at hlt_θ
    let badI : Finset ι := Finset.univ.filter fun i => ¬ (u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i)
    have hT_sub : T ⊆ badI.biUnion fun i => Finset.univ.filter fun z : Fin ℓ → F =>
        (u₀ i - v₀ i) + ∑ j : Fin ℓ, z j * (u j i - v j i) = 0 := by
      intro z hz
      obtain ⟨c, hcRS, hμ_ge⟩ := hclose z hz
      let vz : ι → F := v₀ + ∑ j : Fin ℓ, z j • v j
      have hceq : c = vz := eq_of_hammingDist_le_reedSolomon hα hunique hcRS
        (Submodule.add_mem _ hv₀ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvRS j)))
        (hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge)
        (hammingDist_affine_le_of_eq_on hD₀ hagree₀ z)
      subst hceq
      have hD'_sub : D' ⊆ Finset.univ.filter fun i => (u₀ + ∑ j : Fin ℓ, z j • u j) i = vz i :=
        subset_filter_affine_eq (fun _ hi => (mem_filter.1 hi).2) z
      have hex : ∃ i ∈ Finset.univ.filter (fun i => (u₀ + ∑ j : Fin ℓ, z j • u j) i = vz i),
          i ∉ D' := by
        by_contra hnone; push Not at hnone
        rw [Finset.Subset.antisymm hD'_sub hnone] at hlt_θ
        exact absurd hμ_ge (not_le.2 hlt_θ)
      obtain ⟨i, hi_ag, hi_not⟩ := hex
      refine mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ i, fun h =>
        hi_not (mem_filter.2 ⟨mem_univ i, h⟩)⟩, mem_filter.2 ⟨mem_univ z, ?_⟩⟩
      have heq := (mem_filter.1 hi_ag).2
      simp only [vz, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heq
      have hsum_sub : ∑ j : Fin ℓ, z j * (u j i - v j i) =
          ∑ j : Fin ℓ, z j * u j i - ∑ j : Fin ℓ, z j * v j i := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsum_sub]
      calc u₀ i - v₀ i + (∑ j : Fin ℓ, z j * u j i - ∑ j : Fin ℓ, z j * v j i)
          = (u₀ i + ∑ j : Fin ℓ, z j * u j i) - (v₀ i + ∑ j : Fin ℓ, z j * v j i) := by ring
        _ = 0 := sub_eq_zero.2 heq
    have hT_le := (Finset.card_le_card hT_sub).trans <|
      card_biUnion_zero_affine_le u₀ v₀ u v badI fun _ hi => (mem_filter.1 hi).2
    have hmul_le := (Nat.mul_le_mul_left (Fintype.card F) hT_le).trans_eq (by
      rw [← mul_assoc, mul_comm (Fintype.card F) (Fintype.card ι), mul_assoc, ← pow_succ',
        Nat.sub_add_cancel hℓ])
    omega

/-- **Dimension-independent `ℕ`-weighted correlated agreement on affine spaces in the
unique-decoding regime** ([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4]). -/
theorem exists_weighted_correlatedAgreement_affine_unique_sharp
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) < (Fintype.card F - 1) * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, B ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F),
        (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ :=
    exists_ratWeighted_correlatedAgreement_affine_unique_sharp hα hunique
      (fun i => (div_le_one (Nat.cast_pos.2 hM)).2 (Nat.cast_le.2 (hW i)))
      (card_sub_sub_ceilDiv_sub_one_lt hM) u₀ u T hT fun z hz =>
        let ⟨c, hcRS, hW_ge⟩ := hclose z hz; ⟨c, hcRS, (nat_le_sum_iff_div hM _).1 hW_ge⟩
  exact ⟨D', (nat_le_sum_iff_div hM D').2 hD', v₀, hv₀, v, hvRS, hagree⟩

/-- **Dimension-independent `ℕ`-weighted proximity-gap dichotomy on affine spaces in the
unique-decoding regime** ([BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4]). -/
theorem weighted_proximityGap_affine_unique_sharp
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ M B : ℕ} (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hunique : 2 * (Fintype.card ι - (B + M - 1) / M) + k ≤ Fintype.card ι)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) ∨
      (Fintype.card F - 1) *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i).card ≤
        Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) :=
  proximityGap_affine_of_line
    (P := fun w => ∃ c ∈ reedSolomon α k, B ≤ ∑ i ∈ univ.filter (fun i => w i = c i), W i)
    (B_line := Fintype.card ι)
    (fun a b S hS hcl t =>
      let ⟨_, hD', w₀, hw₀, w₁, hw₁, hag⟩ :=
        exists_weighted_correlatedAgreement_unique hα hM hW hunique a b S hS hcl
      ⟨w₀ + t • w₁, Submodule.add_mem _ hw₀ (Submodule.smul_mem _ t hw₁),
        hD'.trans (Finset.sum_le_sum_of_subset (subset_filter_line_eq hag t))⟩) u₀ u

/-- **Dimension-independent `ℚ`-weighted proximity-gap dichotomy on affine spaces in the
unique-decoding regime** (`ℚ`-weights in `[0, 1]`,
[BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4]). -/
theorem ratWeighted_proximityGap_affine_unique_sharp
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι]
    {α : ι → F} (hα : Function.Injective α)
    {e k ℓ : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    {μ : ι → ℚ} (hμ_nonneg : ∀ i, 0 ≤ μ i) (hμ_le : ∀ i, μ i ≤ 1)
    {θ : ℚ} (hθ : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < θ)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) ∨
      (Fintype.card F - 1) *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i).card ≤
        Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) :=
  proximityGap_affine_of_line
    (P := fun w => ∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ univ.filter (fun i => w i = c i), μ i)
    (B_line := Fintype.card ι)
    (fun a b S hS hcl t =>
      let ⟨_, hD', w₀, hw₀, w₁, hw₁, hag⟩ :=
        exists_ratWeighted_correlatedAgreement_unique hα hunique hμ_le hθ a b S hS hcl
      ⟨w₀ + t • w₁, Submodule.add_mem _ hw₀ (Submodule.smul_mem _ t hw₁),
        hD'.trans (Finset.sum_le_sum_of_subset_of_nonneg (subset_filter_line_eq hag t)
          fun i _ _ => hμ_nonneg i)⟩) u₀ u

/-! ### Part 5: Johnson-bound curves, affine correlated agreement, and dichotomies -/

/-- Private helper: linear weight scaling of `johnsonCurveBound` over `ℝ`. -/
private theorem johnsonCurveBound_mul_cast_le
    {n m d D r M : ℕ} (hn : 1 ≤ n) (hM : 0 < M) {U : ℝ}
    (hU : (ProximityGap.johnsonCurveBound n m d D r n : ℝ) ≤ U) :
    (ProximityGap.johnsonCurveBound n m d D r (M * n) : ℝ) ≤ (M : ℝ) * U := by
  have hmul : (ProximityGap.johnsonCurveBound n m d D r (M * n) : ℝ) * n ≤
      (ProximityGap.johnsonCurveBound n m d D r n : ℝ) * (M * n) := by
    exact_mod_cast ProximityGap.johnsonCurveBound_mul_le (m := m) (d := d) (D := D) (r := r)
      (Nat.le_mul_of_pos_left n hM)
  have hjb : (ProximityGap.johnsonCurveBound n m d D r (M * n) : ℝ) ≤
      (M : ℝ) * ProximityGap.johnsonCurveBound n m d D r n :=
    le_of_mul_le_mul_right (by linarith) (Nat.cast_pos.2 hn)
  exact hjb.trans (mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg M))

/-- Private helper: the Guruswami–Sudan `Y`-degree bound `maxYDeg d D` never exceeds
`johnsonCurveBound n m d D r W_tot` (`0` when `D = 0`, and `≤ 2 * maxYDeg d D * (D + B_Z)` when
`1 ≤ D`). -/
private theorem maxYDeg_le_johnsonCurveBound (n m d D r W_tot : ℕ) :
    ProximityGap.maxYDeg d D ≤ ProximityGap.johnsonCurveBound n m d D r W_tot := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have h0 : ProximityGap.maxYDeg d 0 = 0 :=
      Nat.eq_zero_of_le_zero (Finset.sup_le fun p hp => (Sudan.mem_monomials.1 hp).2.1)
    rw [h0]
    exact Nat.zero_le _
  · calc ProximityGap.maxYDeg d D
        = 1 * (ProximityGap.maxYDeg d D * 1) := by ring
      _ ≤ 2 * (ProximityGap.maxYDeg d D * (D + ProximityGap.siegelZDeg n m d D r)) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
      _ = 2 * ProximityGap.maxYDeg d D * (D + ProximityGap.siegelZDeg n m d D r) := by ring
      _ ≤ ProximityGap.johnsonCurveBound n m d D r W_tot := by
          dsimp only [ProximityGap.johnsonCurveBound]
          omega

/-- Private helper: converts the real density strict inequality `B / q < cardT / q ^ ℓ` (`0 < q`)
to the exact integer form `B * q ^ ℓ < q * cardT` uniformly for all `ℓ : ℕ`. -/
private theorem affine_mul_lt_of_density_lt
    {q ℓ cardT B : ℕ} (hq : 0 < q)
    (hlt : (B : ℝ) / (q : ℝ) < (cardT : ℝ) / ((q : ℝ) ^ ℓ)) :
    B * q ^ ℓ < q * cardT := by
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.2 hq
  have hpowR : (0 : ℝ) < (q : ℝ) ^ ℓ := pow_pos hqR ℓ
  have hmulR : (B : ℝ) * ((q : ℝ) ^ ℓ) < (cardT : ℝ) * (q : ℝ) :=
    (div_lt_div_iff₀ hqR hpowR).1 hlt
  have hcast : ((B * q ^ ℓ : ℕ) : ℝ) < ((q * cardT : ℕ) : ℝ) := by cast_linarith
  exact Nat.cast_lt.1 hcast

/-- Private helper: integer weights bounded by `M` sum to at most `M * |ι|` over any subset. -/
private theorem sum_le_mul_card_of_le {ι : Type*} [Fintype ι] {W : ι → ℕ} {M : ℕ}
    (hW : ∀ i, W i ≤ M) (S : Finset ι) : ∑ i ∈ S, W i ≤ M * Fintype.card ι :=
  calc ∑ i ∈ S, W i ≤ ∑ _i ∈ S, M := Finset.sum_le_sum fun i _ => hW i
    _ = S.card * M := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card ι * M := Nat.mul_le_mul_right M (Finset.card_le_univ S)
    _ = M * Fintype.card ι := Nat.mul_comm _ _

/-- Private helper: clears common denominator `M > 0` from rational weights `μ : ι → ℚ` with
`μ i = a_i / M ≤ 1`, producing integer weights `W : ι → ℕ` and threshold `B_W = ⌈θ * M⌉₊` with
exact subset equivalence `θ ≤ ∑_{i ∈ S} μ i ↔ B_W ≤ ∑_{i ∈ S} W i` and `θ ≤ (B_W + M - 1) / M`. -/
private theorem rat_weights_to_nat
    {ι : Type*} [Fintype ι] {M : ℕ} (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    (θ : ℚ) :
    ∃ W : ι → ℕ,
      (∀ i, 0 ≤ μ i) ∧
      (∀ i, W i ≤ M) ∧
      (∑ i : ι, W i ≤ M * Fintype.card ι) ∧
      (∀ S : Finset ι, θ ≤ ∑ i ∈ S, μ i ↔ ⌈θ * (M : ℚ)⌉₊ ≤ ∑ i ∈ S, W i) ∧
      θ ≤ (((⌈θ * (M : ℚ)⌉₊ + M - 1) / M : ℕ) : ℚ) := by
  let W : ι → ℕ := fun i => Classical.choose (hμ_den i)
  have hW_eq : ∀ i, μ i = (W i : ℚ) / (M : ℚ) := fun i => Classical.choose_spec (hμ_den i)
  have hM_posQ : (0 : ℚ) < (M : ℚ) := Nat.cast_pos.2 hM
  have hμ_nn : ∀ i, 0 ≤ μ i := fun i => by
    rw [hW_eq i]
    exact div_nonneg (Nat.cast_nonneg _) hM_posQ.le
  have hW_le : ∀ i, W i ≤ M := fun i => by
    have h1 : (W i : ℚ) / (M : ℚ) ≤ 1 := hW_eq i ▸ hμ_le i
    exact Nat.cast_le.1 ((div_le_one hM_posQ).1 h1)
  have hW_sum : ∑ i : ι, W i ≤ M * Fintype.card ι := sum_le_mul_card_of_le hW_le Finset.univ
  have hsum_iff : ∀ S : Finset ι, θ ≤ ∑ i ∈ S, μ i ↔ ⌈θ * (M : ℚ)⌉₊ ≤ ∑ i ∈ S, W i := by
    intro S
    have hsum_eq : ∑ i ∈ S, μ i = ((∑ i ∈ S, W i : ℕ) : ℚ) / (M : ℚ) := by
      rw [Nat.cast_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => hW_eq i
    rw [hsum_eq, le_div_iff₀ hM_posQ, Nat.ceil_le]
  have hθ_le_t : θ ≤ (((⌈θ * (M : ℚ)⌉₊ + M - 1) / M : ℕ) : ℚ) := by
    set B_W : ℕ := ⌈θ * (M : ℚ)⌉₊
    set t : ℕ := (B_W + M - 1) / M
    have hBW_le_Mt : B_W ≤ M * t := by
      have hmod : M * t + (B_W + M - 1) % M = B_W + M - 1 := Nat.div_add_mod (B_W + M - 1) M
      have hlt := Nat.mod_lt (B_W + M - 1) hM
      omega
    have h1 : θ * (M : ℚ) ≤ (B_W : ℚ) := Nat.le_ceil _
    have h2 : (B_W : ℚ) ≤ (M : ℚ) * (t : ℚ) := by exact_mod_cast hBW_le_Mt
    exact le_of_mul_le_mul_right (show θ * (M : ℚ) ≤ (t : ℚ) * (M : ℚ) by linarith) hM_posQ
  exact ⟨W, hμ_nn, hW_le, hW_sum, hsum_iff, hθ_le_t⟩

/-- Private helper: uniform Reed–Solomon list-size bound `≤ maxYDeg (k - 1) D` for all `1 ≤ k`
(covering both `k ≥ 2` via `guruswamiSudan` and `k = 1` via disjoint constant-codeword fibers). -/
private theorem card_reedSolomon_list_le_maxYDeg
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k m D M B_W : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * ((B_W + M - 1) / M))
    (u : ι → F) :
    ∃ Lset : Finset (ι → F), Lset.card ≤ ProximityGap.maxYDeg (k - 1) D ∧
      ∀ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i → c ∈ Lset := by
  classical
  set t : ℕ := (B_W + M - 1) / M
  have hagree_ge (c : ι → F) (hcW : B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i) :
      t ≤ (Finset.univ.filter fun i => u i = c i).card := by
    have hsum_le : ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i ≤
        M * (Finset.univ.filter fun i => u i = c i).card :=
      (Finset.sum_le_sum fun i _ => hW_le i).trans_eq
        (by rw [Finset.sum_const, smul_eq_mul, mul_comm])
    rw [Nat.div_le_iff_le_mul_add_pred hM]; omega
  rcases Nat.eq_or_lt_of_le hk with rfl | hk2
  · have ht_pos : 0 < t := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hroot; omega
    let A_good :=
      (Finset.univ.image u).filter fun a => t ≤ (Finset.univ.filter fun i => u i = a).card
    have hmem0 : (0, D) ∈ Sudan.monomials 0 D :=
      Sudan.mem_monomials.2 ⟨Nat.zero_le D, le_rfl, by simp⟩
    have hD_le_maxY : D ≤ ProximityGap.maxYDeg 0 D := Finset.le_sup (f := Prod.snd) hmem0
    have hmon0 : #(Sudan.monomials 0 D) = (D + 1) * (D + 1) := by
      have : Sudan.monomials 0 D = range (D + 1) ×ˢ range (D + 1) := by
        ext ⟨a, b⟩
        simp only [Sudan.mem_monomials, mem_product, mem_range, Nat.lt_succ_iff, zero_mul, add_zero]
        tauto
      rw [this, Finset.card_product, Finset.card_range]
    have hcard_mul : A_good.card * t ≤ Fintype.card ι := calc
      A_good.card * t = ∑ _a ∈ A_good, t := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ a ∈ A_good, (Finset.univ.filter fun i => u i = a).card :=
          Finset.sum_le_sum fun _ ha => (mem_filter.1 ha).2
      _ = (A_good.biUnion fun a => Finset.univ.filter fun i => u i = a).card :=
          (Finset.card_biUnion fun _ _ _ _ hne =>
            Finset.disjoint_filter.2 fun _ _ h1 h2 => hne (h1.symm.trans h2)).symm
      _ ≤ Fintype.card ι := Finset.card_le_univ _
    have hm_le : m ≤ m * (m + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    have hlt_sq : A_good.card * (D + 1) < (D + 1) * (D + 1) := by
      rw [Nat.sub_self, hmon0] at hinterp
      calc A_good.card * (D + 1) ≤ A_good.card * (m * t) := Nat.mul_le_mul_left _ hroot
        _ = A_good.card * t * m := by ring
        _ ≤ Fintype.card ι * m := Nat.mul_le_mul_right _ hcard_mul
        _ ≤ Fintype.card ι * (m * (m + 1) / 2) := Nat.mul_le_mul_left _ hm_le
        _ < (D + 1) * (D + 1) := hinterp
    refine ⟨A_good.image fun a _ => a, Finset.card_image_le.trans
      ((Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_right hlt_sq)).trans hD_le_maxY),
      fun c hcRS hcW => ?_⟩
    obtain ⟨P, hPdeg, rfl⟩ := mem_reedSolomon.1 hcRS
    have hconst : (fun i => P.eval (α i)) = fun _ => P.coeff 0 := funext fun i => by
      rcases eq_or_ne P 0 with rfl | hP0
      · simp
      · have hnd : P.natDegree = 0 := by
          have := (natDegree_lt_iff_degree_lt hP0).2 hPdeg; omega
        conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hnd]
        exact eval_C
    have hcard_a : t ≤ (Finset.univ.filter fun i => u i = P.coeff 0).card := by
      simpa only [congrFun hconst] using hagree_ge (fun i => P.eval (α i)) hcW
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.1 (ht_pos.trans_le hcard_a)
    exact mem_image.2 ⟨P.coeff 0, mem_filter.2
      ⟨mem_image.2 ⟨i₀, mem_univ i₀, (mem_filter.1 hi₀).2⟩, hcard_a⟩, hconst.symm⟩
  · have hmem : (0, D / (k - 1)) ∈ Sudan.monomials (k - 1) D := Sudan.mem_monomials.2
      ⟨Nat.zero_le D, Nat.div_le_self D (k - 1), by rw [zero_add]; exact Nat.mul_div_le D (k - 1)⟩
    have hdiv_le : D / (k - 1) ≤ ProximityGap.maxYDeg (k - 1) D :=
      Finset.le_sup (f := Prod.snd) hmem
    refine ⟨(guruswamiSudan α u m k D).image fun P i => P.eval (α i),
      Finset.card_image_le.trans
        (((Nat.le_div_iff_mul_le (by omega)).2 card_guruswamiSudan_mul_le).trans hdiv_le),
      fun c hcRS hcW => ?_⟩
    obtain ⟨P, hPdeg, rfl⟩ := mem_reedSolomon.1 hcRS
    have ht_le : t ≤ (Finset.univ.filter fun i => P.eval (α i) = u i).card := by
      simpa only [eq_comm] using hagree_ge (fun i => P.eval (α i)) hcW
    exact mem_image.2 ⟨P, (mem_guruswamiSudan_iff hα (by omega) hinterp).2
      ⟨hPdeg, hroot.trans_le (Nat.mul_le_mul_left m ht_le)⟩, rfl⟩

/-! #### 5.1 Johnson-bound parameterized curves and `ℚ`-weighted correlated agreement -/

/-- **Original explicit-constant proximity-gap variant for parameterized curves up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.5 and 6.2], accepted
JACM 2023 manuscript).

Let `α : ι → F` be distinct evaluation points over a finite field `F` with `n = |ι|` and code rate
`ρ = k / n` (`1 ≤ k ≤ n`), and let `m ≥ 1` be the multiplicity parameter. For any degree `r : ℕ`,
any proximity radius `e : ℕ` with `(e : ℝ) / n ≤ 1 - √ρ - √ρ / (2 * m)`, and any `r + 1` words
`u : Fin (r + 1) → (ι → F)`, either every point `∑ j, z ^ j • u j` on the parameterized curve lies
within Hamming distance `e` of `reedSolomon α k`, or the fraction of scalars `z : F` that do is at
most `1800 * r * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`.

While `(m + 1) ^ 6 / ρ` has smaller exponents in `m` and `1 / ρ` than the displayed
`(m + 1 / 2) ^ 7 / (3 * ρ ^ (3 / 2))` expression of
[BenSassonCarmonIshaiKoppartySaraf2020, Theorem 6.2], this bound is not uniformly smaller at small
finite `m`. -/
theorem proximityGap_curve_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k m r : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hm : 1 ≤ m)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u : Fin (r + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e) ∨
      ((#(Finset.univ.filter fun z : F =>
          ∃ c ∈ reedSolomon α k,
            hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e) : ℝ) /
        (Fintype.card F : ℝ)) ≤
        1800 * (r : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · by_cases h0 : ∃ c ∈ reedSolomon α k, hammingDist (u 0) c ≤ e
    · exact Or.inl fun _ => by simpa [Fin.sum_univ_one] using h0
    · right
      have hemp : (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
          hammingDist (∑ j : Fin 1, z ^ (j : ℕ) • u j) c ≤ e) = ∅ := by
        ext; simp [h0]
      simp [hemp]
  · obtain ⟨hk_sub, hinterp, hroot, hjb⟩ := ProximityGap.johnson_curve_params_bound hk hkn hm hr he
    rcases curve_dichotomy_of_ca (C := reedSolomon α k) (u := u)
      (fun x c => hammingDist x c ≤ e) (fun D' => Fintype.card ι - e ≤ D'.card)
      (fun hD' _ hag z => hammingDist_curve_le_of_eq_on hD' hag z)
      (fun S hS hcl => exists_correlatedAgreement_curve_johnson hα hk (by omega) hk_sub hinterp
        hroot u S hS hcl) with hall | hle
    · exact Or.inl hall
    · right
      have hcard : ((Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
          hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e).card : ℝ) ≤ _ :=
        Nat.cast_le.2 hle
      simpa only [div_div] using div_le_div_of_nonneg_right (hcard.trans hjb)
        (Nat.cast_nonneg (Fintype.card F))

/-- Private helper: substitutes `(m + 1) ^ 6 ≤ 64 / η ^ 6` into the explicit Siegel error bound
`1800 * c * (m + 1) ^ 6 * n ^ 2 / (ρ * q)` (`1800 * 64 = 115200`). -/
private theorem siegel_eta_bound_le {n k m q : ℕ} {c η : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hq : 0 < q) (hc : 0 ≤ c) (hη : 0 < η)
    (hpow : ((m + 1 : ℝ) ^ 6) ≤ 64 / (η ^ 6)) :
    1800 * c * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) / (((k : ℝ) / (n : ℝ)) * (q : ℝ)) ≤
      115200 * c * ((n : ℝ) ^ 2) / (((k : ℝ) / (n : ℝ)) * (η ^ 6) * (q : ℝ)) := by
  have hn : 1 ≤ n := hk.trans hkn
  have hρ_pos : 0 < (k : ℝ) / (n : ℝ) := by positivity
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.2 hq
  calc 1800 * c * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) / (((k : ℝ) / (n : ℝ)) * (q : ℝ))
      ≤ 1800 * c * (64 / (η ^ 6)) * ((n : ℝ) ^ 2) / (((k : ℝ) / (n : ℝ)) * (q : ℝ)) := by gcongr
    _ = 115200 * c * ((n : ℝ) ^ 2) / (((k : ℝ) / (n : ℝ)) * (η ^ 6) * (q : ℝ)) := by
        field_simp
        ring

/-- **Original explicit-constant proximity-gap variant for parameterized curves up to
`1 - √ρ - η`** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.5], accepted
JACM 2023 manuscript).

Closed-form corollary of `Cslib.Code.proximityGap_curve_johnson` parameterized directly by any
positive gap `η > 0` below the Johnson bound `1 - √ρ`, yielding an error fraction of at most
`115200 * r * n ^ 2 / (ρ * η ^ 6 * |F|)`. -/
theorem proximityGap_curve_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k r : ℕ} {η : ℝ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hη : 0 < η)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    (u : Fin (r + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e) ∨
      ((#(Finset.univ.filter fun z : F =>
          ∃ c ∈ reedSolomon α k,
            hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e) : ℝ) /
        (Fintype.card F : ℝ)) ≤
        115200 * (r : ℝ) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) := by
  obtain ⟨m, hm, he', hpow⟩ := ProximityGap.exists_multiplicity_of_eta hk hkn hη he
  rcases proximityGap_curve_johnson hα hk hkn hm he' u with hall | hbound
  · exact Or.inl hall
  · exact Or.inr (hbound.trans
      (siegel_eta_bound_le hk hkn Fintype.card_pos (Nat.cast_nonneg r) hη hpow))

/-- **Original explicit-constant `ℕ`-weighted proximity-gap dichotomy on parameterized curves up to
the Johnson bound** (toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 6.2 and 7.2], accepted
JACM 2023 manuscript).

For integer weights `W : ι → ℕ` bounded by `M > 0` (`∀ i, W i ≤ M`), any threshold `B_W : ℕ`
with `((|ι| - (B_W + M - 1) / M : ℕ) : ℝ) / |ι| ≤ 1 - √ρ - √ρ / (2 * m)`, and any degree-`r`
curve `u : Fin (r + 1) → (ι → F)` over a finite field `F`, either every point on the curve has
`W`-weighted agreement at least `B_W` with some codeword in `reedSolomon α k`, or the fraction of
scalars `z : F` that do is at most `1800 * r * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`. -/
theorem weighted_proximityGap_curve_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k m r M B_W : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hB : ((Fintype.card ι - (B_W + M - 1) / M : ℕ) : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u : Fin (r + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter
        (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i) ∨
      ((#(Finset.univ.filter fun z : F =>
          ∃ c ∈ reedSolomon α k,
            B_W ≤ ∑ i ∈ Finset.univ.filter
              (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i) : ℝ) /
        (Fintype.card F : ℝ)) ≤
        1800 * (r : ℝ) * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  set n := Fintype.card ι; set t := (B_W + M - 1) / M
  by_cases ht_le : t ≤ n
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · by_cases h0 : ∃ c ∈ reedSolomon α k, B_W ≤ ∑ i ∈ univ.filter (fun i => u 0 i = c i), W i
      · exact Or.inl fun _ => by simpa [Fin.sum_univ_one] using h0
      · right; have hemp : (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
            B_W ≤ ∑ i ∈ Finset.univ.filter
              (fun i => (∑ j : Fin 1, z ^ (j : ℕ) • u j) i = c i), W i) = ∅ := by
          ext; simp [h0]
        simp [hemp]
    · obtain ⟨hk_sub, hinterp, hroot, hjb⟩ :=
        ProximityGap.johnson_curve_params_bound (e := n - t) hk hkn hm hr hB
      rw [Nat.sub_sub_self ht_le] at hk_sub hroot
      rcases curve_dichotomy_of_ca (C := reedSolomon α k) (u := u)
        (fun x c => B_W ≤ ∑ i ∈ univ.filter (fun i => x i = c i), W i)
        (fun D' => B_W ≤ ∑ i ∈ D', W i)
        (fun hD' _ hag z => hD'.trans (weightedAgree_curve_ge_of_eq_on W hag z))
        (fun S hS hcl => exists_weighted_correlatedAgreement_curve_johnson hα hk (by omega) hM hW
          (sum_le_mul_card_of_le hW univ) hk_sub hinterp hroot u S hS hcl) with hall | hle
      · exact Or.inl hall
      · right
        have hjbM := johnsonCurveBound_mul_cast_le (hk.trans hkn) hM hjb
        have hcard : (#(univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
            B_W ≤ ∑ i ∈ univ.filter (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i),
              W i) : ℝ) ≤ _ := Nat.cast_le.2 hle
        exact (div_le_div_of_nonneg_right (hcard.trans hjbM) (Nat.cast_nonneg _)).trans_eq (by ring)
  · right
    have hMn_lt : M * n < B_W := Nat.lt_of_not_ge fun hle =>
      ht_le ((Nat.div_le_iff_le_mul_add_pred hM).2 (by omega))
    have hemp : (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i) = ∅ := by
      ext z; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      rintro ⟨c, _, hcW⟩
      have hle : ∑ i ∈ univ.filter (fun i =>
          (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i ≤ M * n :=
        sum_le_mul_card_of_le hW _
      omega
    rw [hemp, Finset.card_empty, Nat.cast_zero, zero_div]; positivity

private theorem rat_weights_johnson_nat {ι : Type*} [Fintype ι] {k m D M : ℕ} (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1) (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / M)
    {θ : ℚ} (hk_le : (k : ℚ) ≤ θ) (hroot : (D : ℚ) < m * θ) :
    ∃ W : ι → ℕ, (∀ i, W i ≤ M) ∧ ∑ i : ι, W i ≤ M * Fintype.card ι ∧
      k ≤ (⌈θ * M⌉₊ + M - 1) / M ∧ D < m * ((⌈θ * M⌉₊ + M - 1) / M) ∧
      ∀ S : Finset ι, θ ≤ ∑ i ∈ S, μ i ↔ ⌈θ * M⌉₊ ≤ ∑ i ∈ S, W i := by
  obtain ⟨W, _, hW_le, hW_sum, hsum_iff, hθ_le_t⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  exact ⟨W, hW_le, hW_sum, Nat.cast_le.1 (hk_le.trans hθ_le_t), by
    exact_mod_cast hroot.trans_le (mul_le_mul_of_nonneg_left hθ_le_t (Nat.cast_nonneg m)),
    hsum_iff⟩

/-- **Explicit-parameter `ℚ`-weighted correlated-agreement step on parameterized curves up to the
Johnson bound** (toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 6.2 and 7.2], accepted
JACM 2023 manuscript).

Given rational coordinate weights `μ : ι → ℚ` with values in `{0, 1 / M, …, 1}` (`∀ i, μ i ≤ 1`
and `∀ i, ∃ a : ℕ, μ i = (a : ℚ) / M` for `0 < M`), threshold `θ : ℚ` with `(k : ℚ) ≤ θ` and
`(D : ℚ) < m * θ`, and Guruswami–Sudan interpolation condition
`|ι| * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D)`: over an arbitrary field `F` of any
characteristic, if more than `johnsonCurveBound |ι| m (k - 1) D r (M * |ι|)` scalars `z ∈ T`
have a codeword in `reedSolomon α k` achieving `μ`-weighted agreement at least `θ` with the curve
point `∑ j, z ^ j • u j`, then there exist a single shared coordinate subset `D' : Finset ι` with
`θ ≤ ∑ i ∈ D', μ i` and codewords `v : Fin (r + 1) → (ι → F)` agreeing with `u` on `D'`. -/
theorem exists_ratWeighted_correlatedAgreement_curve_johnson
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k r m D M : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ} (hk_le : (k : ℚ) ≤ θ)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : (D : ℚ) < (m : ℚ) * θ)
    (u : Fin (r + 1) → (ι → F)) (T : Finset F)
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D r
        (M * Fintype.card ι) < #T)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter
        (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v : Fin (r + 1) → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', ∀ j, u j i = v j i := by
  obtain ⟨W, hW_le, hW_sum, hk_le_t, hroot_nat, hsum_iff⟩ :=
    rat_weights_johnson_nat hM hμ_le hμ_den hk_le hroot
  obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_weighted_correlatedAgreement_curve_johnson hα hk hm hM
    hW_le hW_sum hk_le_t hinterp hroot_nat u T hT
    fun z hz => let ⟨c, hcRS, hge⟩ := hclose z hz; ⟨c, hcRS, (hsum_iff _).1 hge⟩
  exact ⟨D', (hsum_iff D').2 hD', v, hvRS, hagree⟩

/-- **Explicit-parameter `ℚ`-weighted correlated-agreement step on affine lines up to the Johnson
bound** (toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 7.2], accepted JACM 2023
manuscript).

Line (`r = 1`) specialization of `Cslib.Code.exists_ratWeighted_correlatedAgreement_curve_johnson`
over an arbitrary field `F` of any characteristic. -/
theorem exists_ratWeighted_correlatedAgreement_line_johnson
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k m D M : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ} (hk_le : (k : ℚ) ≤ θ)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : (D : ℚ) < (m : ℚ) * θ)
    (u₀ u₁ : ι → F) (T : Finset F)
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1
        (M * Fintype.card ι) < #T)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v₁ ∈ reedSolomon α k,
        ∀ i ∈ D', u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  obtain ⟨D', hD', v, hvRS, hagree⟩ := exists_ratWeighted_correlatedAgreement_curve_johnson
    (r := 1) hα hk hm hM hμ_le hμ_den hk_le hinterp hroot ![u₀, u₁] T hT
    fun z hz => by rw [line_sum_fin2]; exact hclose z hz
  exact ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ⟨hagree i hi 0, hagree i hi 1⟩⟩

/-- Private helper: a threshold `θ ≤ n` converted to integer weights with denominator `M`
(`B_W = ⌈θ * M⌉₊`, `t = ⌈B_W / M⌉`) gives a relative radius `(n - t) / n` no larger than any
bound `R` on `1 - θ / n`. -/
private theorem ceilDiv_radius_le {n M : ℕ} {θ : ℚ} {R : ℝ} (hM : 0 < M) (hn : 1 ≤ n)
    (hθ_le_t : θ ≤ (((⌈θ * (M : ℚ)⌉₊ + M - 1) / M : ℕ) : ℚ))
    (hθ_le_n : (θ : ℝ) ≤ (n : ℝ)) (hθ : 1 - (θ : ℝ) / (n : ℝ) ≤ R) :
    ((n - (⌈θ * (M : ℚ)⌉₊ + M - 1) / M : ℕ) : ℝ) / (n : ℝ) ≤ R := by
  set B_W : ℕ := ⌈θ * (M : ℚ)⌉₊
  set t : ℕ := (B_W + M - 1) / M
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hθQ_le_n : θ ≤ (n : ℚ) := by exact_mod_cast hθ_le_n
  have hBW_le_Mn : B_W ≤ M * n := by
    refine Nat.ceil_le.2 ?_
    have h1 : θ * (M : ℚ) ≤ (n : ℚ) * (M : ℚ) :=
      mul_le_mul_of_nonneg_right hθQ_le_n (Nat.cast_nonneg M)
    exact h1.trans_eq (by push_cast; ring)
  have ht_le : t ≤ n := by
    rw [Nat.div_le_iff_le_mul_add_pred hM]
    omega
  have hθR_le_tR : (θ : ℝ) ≤ (t : ℝ) := by exact_mod_cast hθ_le_t
  rw [Nat.cast_sub ht_le, sub_div, div_self hnR.ne']
  have hdiv : (θ : ℝ) / (n : ℝ) ≤ (t : ℝ) / (n : ℝ) :=
    div_le_div_of_nonneg_right hθR_le_tR hnR.le
  linarith

/-- Private helper: weights bounded by `1` sum to at most `|ι|` over any finite subset. -/
private theorem sum_le_card_of_le_one {ι : Type*} [Fintype ι] {μ : ι → ℚ}
    (hμ_le : ∀ i, μ i ≤ 1) (S : Finset ι) : ∑ i ∈ S, μ i ≤ (Fintype.card ι : ℚ) :=
  calc ∑ i ∈ S, μ i ≤ ∑ _i ∈ S, (1 : ℚ) := Finset.sum_le_sum fun i _ => hμ_le i
    _ = (S.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (Fintype.card ι : ℚ) := by exact_mod_cast Finset.card_le_univ _

/-- **Original explicit-constant `ℚ`-weighted proximity-gap dichotomy on parameterized curves up to
the Johnson bound** (toward [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 6.2 and 7.2], accepted
JACM 2023 manuscript).

For rational weights `μ : ι → ℚ` with values in `{0, 1 / M, …, 1}` (`0 < M`), threshold `θ : ℚ`
satisfying `1 - θ / n ≤ 1 - √ρ - √ρ / (2 * m)`, and any degree-`r` curve over a finite field `F`,
either every curve point has `μ`-weighted agreement at least `θ` with some codeword in
`reedSolomon α k`, or the fraction of scalars `z : F` that do is at most
`1800 * r * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`. -/
theorem ratWeighted_proximityGap_curve_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k m r M : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ}
    (hθ : 1 - (θ : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u : Fin (r + 1) → (ι → F))
    [DecidablePred fun z : F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter
        (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i] :
    (∀ z : F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) ∨
      ((#(Finset.univ.filter fun z : F =>
          ∃ c ∈ reedSolomon α k,
            θ ≤ ∑ i ∈ Finset.univ.filter
              (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) : ℝ) /
        (Fintype.card F : ℝ)) ≤
        1800 * (r : ℝ) * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  classical
  obtain ⟨W, _, hW_le, _, hsum_iff, hθ_le_t⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  by_cases hθ_le_n : (θ : ℝ) ≤ Fintype.card ι
  · have hB := ceilDiv_radius_le hM (hk.trans hkn) hθ_le_t hθ_le_n hθ
    have hiff (z : F) : (∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ univ.filter (fun i =>
        (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) ↔
      (∃ c ∈ reedSolomon α k, ⌈θ * M⌉₊ ≤ ∑ i ∈ univ.filter (fun i =>
        (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i) :=
      exists_congr fun _ => and_congr_right fun _ => hsum_iff _
    rcases weighted_proximityGap_curve_johnson (B_W := ⌈θ * M⌉₊) hα hk hkn hm hM hW_le hB u with
      hall | hbound
    · exact Or.inl fun z => (hiff z).2 (hall z)
    · right
      have hf : (univ.filter fun z : F => ∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ univ.filter (fun i =>
          (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) =
        univ.filter fun z : F => ∃ c ∈ reedSolomon α k, ⌈θ * M⌉₊ ≤ ∑ i ∈ univ.filter (fun i =>
          (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i := by
        ext z; simp only [mem_filter, mem_univ, true_and, hiff z]
      simpa only [hf] using hbound
  · right
    have hn_lt : (Fintype.card ι : ℚ) < θ := by exact_mod_cast lt_of_not_ge hθ_le_n
    have hemp : (univ.filter fun z : F => ∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ univ.filter (fun i =>
        (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) = ∅ := by
      ext z; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      rintro ⟨c, _, hcμ⟩; linarith [sum_le_card_of_le_one hμ_le (univ.filter fun i =>
        (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i)]
    rw [hemp, card_empty, Nat.cast_zero, zero_div]; positivity

/-! #### 5.2 Johnson-bound affine spaces: correlated agreement and dichotomies -/

/-- Private helper: strictly positive lower bound on `T.card / |F| ^ ℓ` implies `T.Nonempty`. -/
private theorem nonempty_of_pos_lt_density {F : Type*} [Fintype F] {ℓ : ℕ}
    {T : Finset (Fin ℓ → F)} {B : ℝ} (hB_pos : 0 < B)
    (hT : B < (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ)) : T.Nonempty :=
  Finset.card_pos.1 <| by
    by_contra h0
    have hcz : T.card = 0 := by omega
    rw [hcz, Nat.cast_zero, zero_div] at hT
    exact lt_irrefl 0 (hB_pos.trans hT)

/-- Private helper: reduces `ℚ`-weighted affine correlated agreement with common denominator `M`
to `ℕ`-weighted affine correlated agreement via `rat_weights_to_nat` and `ceilDiv_radius_le`. -/
private theorem ratWeighted_to_nat_affine_ca
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k ℓ M : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ} {R : ℝ} (hθ : 1 - (θ : ℝ) / (Fintype.card ι : ℝ) ≤ R)
    {u₀ : ι → F} {u : Fin ℓ → (ι → F)} {T : Finset (Fin ℓ → F)}
    (hT_ne : T.Nonempty)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i)
    (hw : ∀ {W : ι → ℕ} {B_W : ℕ}, (∀ i, W i ≤ M) →
      ((Fintype.card ι - (B_W + M - 1) / M : ℕ) : ℝ) / (Fintype.card ι : ℝ) ≤ R →
      (∀ z ∈ T, ∃ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) →
      ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
        ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
          ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨W, _, hW_le, _, hsum_iff, hθ_le_t⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  obtain ⟨z₀, hz₀⟩ := hT_ne
  obtain ⟨c₀, _, hc₀_ge⟩ := hclose z₀ hz₀
  have hθ_le_n : (θ : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hc₀_ge.trans (sum_le_card_of_le_one hμ_le _)
  have hB := ceilDiv_radius_le hM (hk.trans hkn) hθ_le_t hθ_le_n hθ
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ := hw hW_le hB fun z hz => by
    obtain ⟨c, hcRS, hge⟩ := hclose z hz
    exact ⟨c, hcRS, (hsum_iff _).1 hge⟩
  exact ⟨D', (hsum_iff D').2 hD', v₀, hv₀, v, hvRS, hagree⟩

/-- **Explicit-parameter `ℕ`-weighted correlated-agreement step on affine spaces up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed p. 6 and
Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript).

Let `B_line = johnsonCurveBound |ι| m (k - 1) D 1 W_tot`. Over any finite field `F` of arbitrary
characteristic and any affine dimension `ℓ : ℕ`, if `B_line * |F| ^ ℓ < |F| * #T` and every
`z ∈ T` has a codeword in `reedSolomon α k` achieving `W`-weighted agreement at least `B_W` with
`u₀ + ∑ j, z j • u j`, then there exist a single shared coordinate subset `D' : Finset ι` of
`W`-weight at least `B_W` and codewords `v₀, v_j ∈ reedSolomon α k` agreeing with `u₀, u_j` on
`D'`. The density premise forces `B_line < |F|`, and `maxYDeg (k - 1) D ≤ B_line` always holds, so
no extra list-size / field-size premise is needed, and zero coordinate weights (`W i = 0`) are
permitted via the `supp W` refinement of
`Cslib.Code.exists_weighted_correlatedAgreement_affine_of_line`. -/
theorem exists_weighted_correlatedAgreement_affine_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ m D M W_tot B_W : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * ((B_W + M - 1) / M))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot *
        (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  have hB_lt_q :
      ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot < Fintype.card F :=
    lt_card_field_of_density_threshold hT
  have hL_lt_q : 2 ≤ ℓ → ProximityGap.maxYDeg (k - 1) D < Fintype.card F := fun _ =>
    (maxYDeg_le_johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot).trans_lt hB_lt_q
  obtain ⟨D', _, hD'_ge, v₀, hv₀, v, hvRS, hagree⟩ :=
    exists_weighted_correlatedAgreement_affine_of_line
      (C := reedSolomon α k) (W := W) (B_W := B_W)
      (B_line := ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot)
      (L := ProximityGap.maxYDeg (k - 1) D)
      (fun w => card_reedSolomon_list_le_maxYDeg hα hk hm hM hW_le hinterp hroot w)
      (fun {B'} hB' a b S hS hcl => by
        have ht_le : (B_W + M - 1) / M ≤ (B' + M - 1) / M :=
          Nat.div_le_div_right (by omega)
        exact exists_weighted_correlatedAgreement_line_johnson hα hk hm hM hW_le hW_sum
          (hk_le_t.trans ht_le) hinterp (hroot.trans_le (Nat.mul_le_mul_left m ht_le))
          a b S hS hcl)
      hL_lt_q u₀ u T hT hclose
  exact ⟨D', hD'_ge, v₀, hv₀, v, hvRS, hagree⟩

/-- **Explicit-parameter correlated-agreement step on affine spaces up to the Johnson bound**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.6], printed p. 6 of the
accepted JACM 2023 manuscript).

Unweighted specialization (`W = 1`) of
`Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson` with exact threshold
`johnsonCurveBound |ι| m (k - 1) D 1 |ι| * |F| ^ ℓ < |F| * #T` and no extra list-size premise. -/
theorem exists_correlatedAgreement_affine_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ e m D : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hk_le : k ≤ Fintype.card ι - e)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * (Fintype.card ι - e))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 (Fintype.card ι) *
        (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  have hceil : (Fintype.card ι - e + 1 - 1) / 1 = Fintype.card ι - e := by omega
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ := exists_weighted_correlatedAgreement_affine_johnson
    (W := fun _ => 1) (M := 1) (W_tot := Fintype.card ι) (B_W := Fintype.card ι - e)
    hα hk hm Nat.one_pos (fun _ => le_rfl) (by simp) (by rwa [hceil]) hinterp (by rwa [hceil])
    u₀ u T hT fun z hz => let ⟨c, hcRS, hd⟩ := hclose z hz
      ⟨c, hcRS, by simpa using card_filter_eq_of_hammingDist_le hd⟩
  exact ⟨D', by simpa using hD', v₀, hv₀, v, hvRS, hagree⟩

/-- **Explicit-parameter `ℚ`-weighted correlated-agreement step on affine spaces up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed p. 6 and
Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript).

For rational coordinate weights `μ : ι → ℚ` in `{0, 1 / M, …, 1}` (`0 < M`, zero weights allowed),
threshold `θ : ℚ` with `(k : ℚ) ≤ θ` and `(D : ℚ) < m * θ`, and Guruswami–Sudan interpolation
condition `|ι| * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D)`, if
`johnsonCurveBound |ι| m (k - 1) D 1 (M * |ι|) * |F| ^ ℓ < |F| * #T` then there exist a shared
coordinate subset `D' : Finset ι` with `θ ≤ ∑ i ∈ D', μ i` and codewords `v₀, v_j ∈ reedSolomon α k`
agreeing with `u₀, u_j` on `D'`, with no list-size premise. -/
theorem exists_ratWeighted_correlatedAgreement_affine_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ m D M : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ} (hk_le : (k : ℚ) ≤ θ)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : (D : ℚ) < (m : ℚ) * θ)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1
        (M * Fintype.card ι) * (Fintype.card F) ^ ℓ < Fintype.card F * T.card)
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨W, hW_le, hW_sum, hk_le_t, hroot_nat, hsum_iff⟩ :=
    rat_weights_johnson_nat hM hμ_le hμ_den hk_le hroot
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ := exists_weighted_correlatedAgreement_affine_johnson
    hα hk hm hM hW_le hW_sum hk_le_t hinterp hroot_nat u₀ u T hT
    fun z hz => let ⟨c, hcRS, hge⟩ := hclose z hz; ⟨c, hcRS, (hsum_iff _).1 hge⟩
  exact ⟨D', (hsum_iff D').2 hD', v₀, hv₀, v, hvRS, hagree⟩

/-- **Original explicit-constant correlated-agreement variant on affine spaces up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.6], printed p. 6 of
the accepted JACM 2023 manuscript).

For any affine dimension `ℓ : ℕ`, `1 ≤ k ≤ n`, multiplicity parameter `m ≥ 1`, and proximity radius
`(e : ℝ) / n ≤ 1 - √ρ - √ρ / (2 * m)` (`ρ = k / n`), if the close parameter subset `T` has density
strictly above `1800 * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)` (independent of `ℓ`, with no list-size
premise), then all affine generators `u₀, u_j` simultaneously agree with codewords
`v₀, v_j ∈ reedSolomon α k` on a shared coordinate subset `D'` of size at least `n - e`. While
`(m + 1) ^ 6 / ρ` has smaller exponents in `m` and `1 / ρ` than the paper's displayed
`(m + 1 / 2) ^ 7 / (3 * ρ ^ (3 / 2))` expression, this explicit constant is not uniformly smaller
at small finite `m`. -/
theorem exists_correlatedAgreement_affine_johnson_of_multiplicity
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k m ℓ : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hm : 1 ≤ m)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : 1800 * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨hk_sub, hinterp, hroot, hjb⟩ := ProximityGap.johnson_line_params_bound hk hkn hm he
  have hdiv := div_le_div_of_nonneg_right hjb (Nat.cast_nonneg (Fintype.card F))
  rw [div_div] at hdiv
  exact exists_correlatedAgreement_affine_johnson hα hk (by omega) hk_sub hinterp hroot
    u₀ u T (affine_mul_lt_of_density_lt Fintype.card_pos (hdiv.trans_lt hT)) hclose

/-- **Original explicit-constant correlated-agreement variant on affine spaces up to
`1 - √ρ - η`** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.6], printed
p. 6 of the accepted JACM 2023 manuscript).

Closed-form corollary of `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_multiplicity`
for any gap `η > 0` below `1 - √ρ`, establishing simultaneous generator correlated agreement on a
shared coordinate subset `D'` of size at least `n - e` whenever `#T / |F| ^ ℓ` exceeds
`115200 * n ^ 2 / (ρ * η ^ 6 * |F|)` (independent of `ℓ`, with no list-size premise). -/
theorem exists_correlatedAgreement_affine_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k ℓ : ℕ} {η : ℝ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hη : 0 < η)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : 115200 * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) :
    ∃ D' : Finset ι, Fintype.card ι - e ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨m, hm, he', hpow⟩ := ProximityGap.exists_multiplicity_of_eta hk hkn hη he
  have hle := by
    simpa only [mul_one] using
      siegel_eta_bound_le hk hkn (Fintype.card_pos (α := F)) zero_le_one hη hpow
  exact exists_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm he' u₀ u T
    (hle.trans_lt hT) hclose

/-- **Original explicit-constant `ℕ`-weighted correlated-agreement variant on affine spaces up to
the Johnson bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on
printed p. 6 and Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript).

For integer weights `W : ι → ℕ` bounded by `M > 0` (zero weights allowed) and threshold `B_W : ℕ`
with `((n - (B_W + M - 1) / M : ℕ) : ℝ) / n ≤ 1 - √ρ - √ρ / (2 * m)`, density strictly above
`1800 * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)` yields simultaneous generator correlated agreement of
`W`-weight at least `B_W`, independent of `ℓ` and with no extra list-size premise. -/
theorem exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k m ℓ M B_W : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hB : ((Fintype.card ι - (B_W + M - 1) / M : ℕ) : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : 1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  have hpos : 0 < 1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
      (((k : ℝ) / Fintype.card ι) * Fintype.card F) := by
    have : 1 ≤ Fintype.card ι := hk.trans hkn
    have : 0 < Fintype.card F := Fintype.card_pos; positivity
  obtain ⟨z₀, hz₀⟩ := nonempty_of_pos_lt_density hpos hT
  have hBW_le : B_W ≤ M * Fintype.card ι :=
    let ⟨_, _, hge⟩ := hclose z₀ hz₀; hge.trans (sum_le_mul_card_of_le hW _)
  have ht_le : (B_W + M - 1) / M ≤ Fintype.card ι :=
    (Nat.div_le_iff_le_mul_add_pred hM).2 (by omega)
  obtain ⟨hk_sub, hinterp, hroot, hjb⟩ := ProximityGap.johnson_line_params_bound
    (e := Fintype.card ι - (B_W + M - 1) / M) hk hkn hm hB
  rw [Nat.sub_sub_self ht_le] at hk_sub hroot
  have hdiv := div_le_div_of_nonneg_right (johnsonCurveBound_mul_cast_le (hk.trans hkn) hM hjb)
    (Nat.cast_nonneg (Fintype.card F))
  exact exists_weighted_correlatedAgreement_affine_johnson hα hk (by omega) hM hW
    (sum_le_mul_card_of_le hW univ) hk_sub hinterp hroot u₀ u T
    (affine_mul_lt_of_density_lt Fintype.card_pos
      ((hdiv.trans_eq (by rw [mul_div_assoc', div_div]; ring)).trans_lt hT)) hclose

/-- **Original explicit-constant `ℕ`-weighted correlated-agreement variant on affine spaces up to
`1 - √ρ - η`** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed
p. 6 and Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript). -/
theorem exists_weighted_correlatedAgreement_affine_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k ℓ M B_W : ℕ} {η : ℝ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hM : 0 < M) (hη : 0 < η)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hB : ((Fintype.card ι - (B_W + M - 1) / M : ℕ) : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : 115200 * (M : ℝ) * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) :
    ∃ D' : Finset ι, B_W ≤ ∑ i ∈ D', W i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  obtain ⟨m, hm, hB', hpow⟩ := ProximityGap.exists_multiplicity_of_eta hk hkn hη hB
  exact exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm hM hW hB'
    u₀ u T
    ((siegel_eta_bound_le hk hkn Fintype.card_pos (Nat.cast_nonneg M) hη hpow).trans_lt hT) hclose

/-- **Original explicit-constant `ℚ`-weighted correlated-agreement variant on affine spaces up to
the Johnson bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on
printed p. 6 and Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript).

For rational coordinate weights `μ : ι → ℚ` in `{0, 1 / M, …, 1}` (`0 < M`, zero weights allowed)
and threshold `θ : ℚ` with `1 - θ / n ≤ 1 - √ρ - √ρ / (2 * m)`, density strictly above
`1800 * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)` yields simultaneous generator correlated agreement of
`μ`-weight at least `θ`, independent of `ℓ` and with no extra list-size premise. -/
theorem exists_ratWeighted_correlatedAgreement_affine_johnson_of_multiplicity
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k m ℓ M : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ}
    (hθ : 1 - (θ : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : 1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  have hB : 0 < (1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
      (((k : ℝ) / Fintype.card ι) * Fintype.card F)) := by
    have : 0 < Fintype.card ι := hk.trans hkn
    have : 0 < Fintype.card F := Fintype.card_pos; positivity
  exact ratWeighted_to_nat_affine_ca hk hkn hM hμ_le hμ_den hθ (nonempty_of_pos_lt_density hB hT)
    hclose fun hW_le hB' hclW => exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity
      hα hk hkn hm hM hW_le hB' u₀ u T hT hclW

/-- **Original explicit-constant `ℚ`-weighted correlated-agreement variant on affine spaces up to
`1 - √ρ - η`** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 1.6 on printed
p. 6 and Theorems 7.3–7.4 on printed p. 32 of the accepted JACM 2023 manuscript).

For rational coordinate weights `μ : ι → ℚ` in `{0, 1 / M, …, 1}` (`0 < M`, zero weights allowed),
any gap `η > 0`, and threshold `θ : ℚ` with `1 - θ / n ≤ 1 - √ρ - η`, density strictly above
`115200 * M * n ^ 2 / (ρ * η ^ 6 * |F|)` yields simultaneous generator correlated agreement of
`μ`-weight at least `θ`, independent of `ℓ` and with no extra list-size premise. -/
theorem exists_ratWeighted_correlatedAgreement_affine_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k ℓ M : ℕ} {η : ℝ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hM : 0 < M) (hη : 0 < η)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ}
    (hθ : 1 - (θ : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    (T : Finset (Fin ℓ → F))
    (hT : 115200 * (M : ℝ) * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) <
      (T.card : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    (hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) :
    ∃ D' : Finset ι, θ ≤ ∑ i ∈ D', μ i ∧
      ∃ v₀ ∈ reedSolomon α k, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ reedSolomon α k) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i := by
  exact ratWeighted_to_nat_affine_ca hk hkn hM hμ_le hμ_den hθ
    (nonempty_of_pos_lt_density (by
      have : 1 ≤ Fintype.card ι := hk.trans hkn
      have : 0 < Fintype.card F := Fintype.card_pos; positivity) hT)
    hclose fun hW_le hB hclW =>
      exists_weighted_correlatedAgreement_affine_johnson_of_eta hα hk hkn hM hη hW_le hB
        u₀ u T hT hclW

/-- Private helper: an affine proximity-gap dichotomy follows from correlated agreement. If every
`Dense` set of close affine parameters yields generators agreeing with codewords on a `Good` shared
coordinate set, and such shared agreement makes every affine point close, then either every affine
point is close or the close parameter set is not dense. -/
private theorem affine_dichotomy_of_correlatedAgreement
    {F ι : Type*} [Field F] [Fintype F] {ℓ : ℕ} {C : Submodule F (ι → F)}
    {u₀ : ι → F} {u : Fin ℓ → (ι → F)}
    (Close : (ι → F) → (ι → F) → Prop) (Good : Finset ι → Prop)
    (hgood : ∀ {D' : Finset ι}, Good D' → ∀ {v₀ : ι → F} {v : Fin ℓ → (ι → F)},
      (∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) →
      ∀ z : Fin ℓ → F, Close (u₀ + ∑ j : Fin ℓ, z j • u j) (v₀ + ∑ j : Fin ℓ, z j • v j))
    (Dense : Finset (Fin ℓ → F) → Prop) {Small : Prop}
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ C, Close (u₀ + ∑ j : Fin ℓ, z j • u j) c]
    (hsmall : ¬ Dense (Finset.univ.filter fun z : Fin ℓ → F =>
      ∃ c ∈ C, Close (u₀ + ∑ j : Fin ℓ, z j • u j) c) → Small)
    (hca : ∀ T : Finset (Fin ℓ → F), Dense T →
      (∀ z ∈ T, ∃ c ∈ C, Close (u₀ + ∑ j : Fin ℓ, z j • u j) c) →
      ∃ D' : Finset ι, Good D' ∧ ∃ v₀ ∈ C, ∃ v : Fin ℓ → (ι → F), (∀ j, v j ∈ C) ∧
        ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) :
    (∀ z : Fin ℓ → F, ∃ c ∈ C, Close (u₀ + ∑ j : Fin ℓ, z j • u j) c) ∨ Small := by
  by_cases hdense : Dense (Finset.univ.filter fun z : Fin ℓ → F =>
      ∃ c ∈ C, Close (u₀ + ∑ j : Fin ℓ, z j • u j) c)
  · obtain ⟨D', hD', v₀, hv₀, v, hv, hagree⟩ :=
      hca _ hdense fun _ hz => (Finset.mem_filter.1 hz).2
    exact Or.inl fun z => ⟨v₀ + ∑ j : Fin ℓ, z j • v j,
      Submodule.add_mem _ hv₀ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hv j)),
      hgood hD' hagree z⟩
  · exact Or.inr (hsmall hdense)

/-- **Exact-threshold proximity-gap dichotomy on affine spaces in the unique-decoding regime**
([BenSassonCarmonIshaiKoppartySaraf2020, Theorem 1.2, eq. (1.2)], accepted JACM 2023 manuscript
p. 3).

Contrapositive corollary of `Cslib.Code.exists_uniqueMaximal_correlatedAgreement_affine_unique`:
either every point of `u₀ + ∑ j, z j • u j` lies within Hamming distance `e` of `reedSolomon α k`,
or `|F| * #T ≤ |ι| * |F| ^ ℓ` (density at most `|ι| / |F| = ε_U`, uniformly for all `ℓ : ℕ`). -/
theorem proximityGap_affine_unique
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {e k ℓ : ℕ} (hunique : 2 * e + k ≤ Fintype.card ι)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) ∨
      Fintype.card F *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e).card ≤
        Fintype.card ι * (Fintype.card F) ^ ℓ :=
  affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => hammingDist x c ≤ e)
    (fun D' => Fintype.card ι - e ≤ D'.card)
    (fun hD' _ _ hag z => hammingDist_affine_le_of_eq_on hD' hag z)
    (fun T' => Fintype.card ι * (Fintype.card F) ^ ℓ < Fintype.card F * T'.card)
    Nat.le_of_not_lt
    fun T' hT' hcl =>
      let ⟨D', hD', v₀, hv₀, v, hv, hag, _⟩ :=
        exists_uniqueMaximal_correlatedAgreement_affine_unique hα hunique u₀ u T' hT' hcl
      ⟨D', hD', v₀, hv₀, v, hv, hag⟩

/-- **Explicit-parameter proximity-gap dichotomy on affine spaces up to the Johnson bound**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2 and 1.6], accepted JACM
2023 manuscript).

Contrapositive corollary of `Cslib.Code.exists_correlatedAgreement_affine_johnson`: either every
point of `u₀ + ∑ j, z j • u j` lies within Hamming distance `e` of `reedSolomon α k`, or
`|F| * #T ≤ johnsonCurveBound |ι| m (k - 1) D 1 |ι| * |F| ^ ℓ` uniformly for all `ℓ : ℕ`. -/
theorem proximityGap_affine_johnson_exact
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ e m D : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hk_le : k ≤ Fintype.card ι - e)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * (Fintype.card ι - e))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) ∨
      Fintype.card F *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e).card ≤
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 (Fintype.card ι) *
          (Fintype.card F) ^ ℓ := by
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => hammingDist x c ≤ e)
    (fun D' => Fintype.card ι - e ≤ D'.card)
    (fun hD' _ _ hag z => hammingDist_affine_le_of_eq_on hD' hag z)
    (fun T' =>
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 (Fintype.card ι) *
          (Fintype.card F) ^ ℓ < Fintype.card F * T'.card)
    Nat.le_of_not_lt
    fun T' hT' hcl =>
      exists_correlatedAgreement_affine_johnson hα hk hm hk_le hinterp hroot u₀ u T' hT' hcl

/-- **Explicit-parameter `ℕ`-weighted proximity-gap dichotomy on affine spaces up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4], accepted
JACM 2023 manuscript).

Contrapositive corollary of `Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson` with
exact denominator `|F|` (`|F| * #T ≤ B_line * |F| ^ ℓ` uniformly for all `ℓ : ℕ`). -/
theorem weighted_proximityGap_affine_johnson_exact
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ m D M W_tot B_W : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW_le : ∀ i, W i ≤ M) (hW_sum : ∑ i, W i ≤ W_tot)
    (hk_le_t : k ≤ (B_W + M - 1) / M)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : D < m * ((B_W + M - 1) / M))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) ∨
      Fintype.card F *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i).card ≤
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot *
          (Fintype.card F) ^ ℓ := by
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => x i = c i), W i)
    (fun D' => B_W ≤ ∑ i ∈ D', W i)
    (fun hD' _ _ hag z => hD'.trans (weightedAgree_affine_ge_of_eq_on W hag z))
    (fun T' =>
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 W_tot *
          (Fintype.card F) ^ ℓ < Fintype.card F * T'.card)
    Nat.le_of_not_lt
    fun T' hT' hcl =>
      exists_weighted_correlatedAgreement_affine_johnson hα hk hm hM hW_le hW_sum hk_le_t hinterp
        hroot u₀ u T' hT' hcl

/-- **Explicit-parameter `ℚ`-weighted proximity-gap dichotomy on affine spaces up to the Johnson
bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4], accepted
JACM 2023 manuscript).

Contrapositive corollary of `Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson` with
exact denominator `|F|` (`|F| * #T ≤ B_line * |F| ^ ℓ` uniformly for all `ℓ : ℕ`). -/
theorem ratWeighted_proximityGap_affine_johnson_exact
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α)
    {k ℓ m D M : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ} (hk_le : (k : ℚ) ≤ θ)
    (hinterp : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D))
    (hroot : (D : ℚ) < (m : ℚ) * θ)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) ∨
      Fintype.card F *
        (Finset.univ.filter fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
          θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i).card ≤
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 (M * Fintype.card ι) *
          (Fintype.card F) ^ ℓ := by
  obtain ⟨_, hμ_nn, _, _, _, _⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => θ ≤ ∑ i ∈ Finset.univ.filter (fun i => x i = c i), μ i)
    (fun D' => θ ≤ ∑ i ∈ D', μ i)
    (fun hD' _ _ hag z => hD'.trans (ratWeightedAgree_affine_ge_of_eq_on hμ_nn hag z))
    (fun T' =>
        ProximityGap.johnsonCurveBound (Fintype.card ι) m (k - 1) D 1 (M * Fintype.card ι) *
          (Fintype.card F) ^ ℓ < Fintype.card F * T'.card)
    Nat.le_of_not_lt
    fun T' hT' hcl =>
      exists_ratWeighted_correlatedAgreement_affine_johnson hα hk hm hM hμ_le hμ_den hk_le hinterp
        hroot u₀ u T' hT' hcl

/-- **Original explicit-constant proximity-gap dichotomy on affine spaces up to the Johnson bound**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2 and 1.6], accepted JACM
2023 manuscript).

Contrapositive corollary of
`Cslib.Code.exists_correlatedAgreement_affine_johnson_of_multiplicity`: for any affine dimension
`ℓ : ℕ`, `1 ≤ k ≤ n`, `m ≥ 1`, and `(e : ℝ) / n ≤ 1 - √ρ - √ρ / (2 * m)` (`ρ = k / n`), either
every point of `u₀ + ∑ j : Fin ℓ, z j • u j` lies within Hamming distance `e` of
`reedSolomon α k`, or the fraction of `z : Fin ℓ → F` that do is at most
`1800 * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`, independent of `ℓ` (with exact denominator `|F|`; the
explicit constant is not uniformly smaller than the paper's displayed finite constant at small `m`).
-/
theorem proximityGap_affine_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k m ℓ : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hm : 1 ≤ m)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) ∨
      ((#(Finset.univ.filter fun z : Fin ℓ → F =>
          ∃ c ∈ reedSolomon α k, hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) : ℝ) /
        ((Fintype.card F : ℝ) ^ ℓ)) ≤
        1800 * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => hammingDist x c ≤ e)
    (fun D' => Fintype.card ι - e ≤ D'.card)
    (fun hD' _ _ hag z => hammingDist_affine_le_of_eq_on hD' hag z)
    (fun T' =>
        1800 * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
        (#T' : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    le_of_not_gt
    fun T' hT' hcl =>
      exists_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm he u₀ u T' hT' hcl

/-- **Original explicit-constant proximity-gap dichotomy on affine spaces up to `1 - √ρ - η`**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.2 and 1.6], accepted JACM
2023 manuscript).

Contrapositive corollary of `Cslib.Code.exists_correlatedAgreement_affine_johnson_of_eta` for any
gap `η > 0` below `1 - √ρ`, yielding an exceptional fraction of at most
`115200 * n ^ 2 / (ρ * η ^ 6 * |F|)` (independent of `ℓ`, with exact denominator `|F|`). -/
theorem proximityGap_affine_johnson_of_eta
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {e k ℓ : ℕ} {η : ℝ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) (hη : 0 < η)
    (he : (e : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) - η)
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) ∨
      ((#(Finset.univ.filter fun z : Fin ℓ → F =>
          ∃ c ∈ reedSolomon α k, hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e) : ℝ) /
        ((Fintype.card F : ℝ) ^ ℓ)) ≤
        115200 * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) := by
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => hammingDist x c ≤ e)
    (fun D' => Fintype.card ι - e ≤ D'.card)
    (fun hD' _ _ hag z => hammingDist_affine_le_of_eq_on hD' hag z)
    (fun T' =>
        115200 * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) <
        (#T' : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    le_of_not_gt
    fun T' hT' hcl =>
      exists_correlatedAgreement_affine_johnson_of_eta hα hk hkn hη he u₀ u T' hT' hcl

/-- **Original explicit-constant `ℕ`-weighted proximity-gap dichotomy on affine spaces up to the
Johnson bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4],
accepted JACM 2023 manuscript).

Contrapositive corollary of
`Cslib.Code.exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity` with exact
denominator `|F|` (`1800 * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`). -/
theorem weighted_proximityGap_affine_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k m ℓ M B_W : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hm : 1 ≤ m) (hM : 0 < M)
    {W : ι → ℕ} (hW : ∀ i, W i ≤ M)
    (hB : ((Fintype.card ι - (B_W + M - 1) / M : ℕ) : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) ∨
      ((#(Finset.univ.filter fun z : Fin ℓ → F =>
          ∃ c ∈ reedSolomon α k, B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i) : ℝ) /
        ((Fintype.card F : ℝ) ^ ℓ)) ≤
        1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => x i = c i), W i)
    (fun D' => B_W ≤ ∑ i ∈ D', W i)
    (fun hD' _ _ hag z => hD'.trans (weightedAgree_affine_ge_of_eq_on W hag z))
    (fun T' =>
        1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
        (#T' : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    le_of_not_gt
    fun T' hT' hcl =>
      exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm hM hW hB
        u₀ u T' hT' hcl

/-- **Original explicit-constant `ℚ`-weighted proximity-gap dichotomy on affine spaces up to the
Johnson bound** (in the setting of [BenSassonCarmonIshaiKoppartySaraf2020, Theorems 1.6 and 7.4],
accepted JACM 2023 manuscript).

Contrapositive corollary of
`Cslib.Code.exists_ratWeighted_correlatedAgreement_affine_johnson_of_multiplicity` with exact
denominator `|F|` (`1800 * M * (m + 1) ^ 6 * n ^ 2 / (ρ * |F|)`). -/
theorem ratWeighted_proximityGap_affine_johnson
    {F ι : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq F]
    {α : ι → F} {k m ℓ M : ℕ}
    (hα : Function.Injective α) (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hm : 1 ≤ m) (hM : 0 < M)
    {μ : ι → ℚ} (hμ_le : ∀ i, μ i ≤ 1)
    (hμ_den : ∀ i, ∃ a : ℕ, μ i = (a : ℚ) / (M : ℚ))
    {θ : ℚ}
    (hθ : 1 - (θ : ℝ) / (Fintype.card ι : ℝ) ≤
      1 - Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) -
        Real.sqrt ((k : ℝ) / (Fintype.card ι : ℝ)) / (2 * (m : ℝ)))
    (u₀ : ι → F) (u : Fin ℓ → (ι → F))
    [DecidablePred fun z : Fin ℓ → F => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i] :
    (∀ z : Fin ℓ → F, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) ∨
      ((#(Finset.univ.filter fun z : Fin ℓ → F =>
          ∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
            (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i) : ℝ) /
        ((Fintype.card F : ℝ) ^ ℓ)) ≤
        1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
  obtain ⟨_, hμ_nn, _, _, _, _⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  exact affine_dichotomy_of_correlatedAgreement (C := reedSolomon α k)
    (fun x c => θ ≤ ∑ i ∈ Finset.univ.filter (fun i => x i = c i), μ i)
    (fun D' => θ ≤ ∑ i ∈ D', μ i)
    (fun hD' _ _ hag z => hD'.trans (ratWeightedAgree_affine_ge_of_eq_on hμ_nn hag z))
    (fun T' =>
        1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
          (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) <
        (#T' : ℝ) / ((Fintype.card F : ℝ) ^ ℓ))
    le_of_not_gt
    fun T' hT' hcl =>
      exists_ratWeighted_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm hM hμ_le
        hμ_den hθ u₀ u T' hT' hcl

end Cslib.Code
