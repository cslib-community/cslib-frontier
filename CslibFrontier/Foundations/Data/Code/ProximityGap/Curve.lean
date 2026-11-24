/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
public import Mathlib.Algebra.Order.Ring.Rat
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.AffineLift
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.AffineReduce
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.Dichotomy
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.JohnsonAffine
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.JohnsonCurve
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.UniqueAffine
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve.UniqueCurve

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


The formalization is organized into focused submodules under
`CslibFrontier.Foundations.Data.Code.ProximityGap.Curve`:

* `Internal`: shared algebraic and counting internal helpers (used by ≥ 2 submodules).
* `UniqueCurve`: converse proximity lemmas and sharp unique-decoding curve/line bounds.
* `AffineReduce`: generic affine-space-to-curve and line-to-affine reductions.
* `AffineLift`: generic Section 6.3 / 7.3 weighted affine correlated-agreement lift.
* `UniqueAffine`: unique maximal and sharp weighted unique-decoding affine bounds.
* `JohnsonHelpers`: shared Johnson-bound scaling and weight-clearing helpers.
* `JohnsonCurve`: Johnson-bound parameterized curve and line proximity gaps.
* `JohnsonAffine`: list-premise-free Johnson-bound affine correlated agreement.
* `Dichotomy`: exact-`|F|` affine proximity-gap dichotomies (unique and Johnson).

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
