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
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.Field.Rat
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

private theorem hammingDist_le_of_card_filter_eq
    {F : Type*} {ι : Type*} [Fintype ι] [DecidableEq F]
    {e : ℕ} {x y : ι → F}
    (hcard : Fintype.card ι - e ≤ (Finset.univ.filter fun i => x i = y i).card) :
    hammingDist x y ≤ e := by
  have htot := card_filter_eq_add_hammingDist x y
  omega

private theorem card_filter_eq_of_hammingDist_le
    {F : Type*} {ι : Type*} [Fintype ι] [DecidableEq F]
    {e : ℕ} {x y : ι → F} (hdist : hammingDist x y ≤ e) :
    Fintype.card ι - e ≤ (Finset.univ.filter fun i => x i = y i).card := by
  have htot := card_filter_eq_add_hammingDist x y
  omega

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
  have hsum_le : ∑ i ∈ A, μ i ≤ (A.card : ℚ) := by
    calc ∑ i ∈ A, μ i ≤ ∑ _i ∈ A, (1 : ℚ) := Finset.sum_le_sum fun i _ => hμ_le i
      _ = (A.card : ℚ) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hlt_q : ((Fintype.card ι - e : ℕ) : ℚ) < ((A.card + 1 : ℕ) : ℚ) := by
    have h1 : ((Fintype.card ι - e : ℕ) : ℚ) - 1 < (A.card : ℚ) :=
      hθ.trans_le (hμ_ge.trans hsum_le)
    push_cast
    linarith
  have hlt_n : Fintype.card ι - e < A.card + 1 := Nat.cast_lt.1 hlt_q
  omega

/-- Counting lemma: in `Fin ℓ → F` with `1 ≤ ℓ`, the hyperplane `{z | z j₀ = 0}` has cardinality
`|F| ^ (ℓ - 1)`. -/
private theorem card_filter_coord_eq_zero
    {F : Type*} [Zero F] [Fintype F] [DecidableEq F]
    {ℓ : ℕ} (j₀ : Fin ℓ) :
    (Finset.univ.filter fun z : Fin ℓ → F => z j₀ = 0).card =
      (Fintype.card F) ^ (ℓ - 1) := by
  classical
  have hbij :
      (Finset.univ : Finset ({j : Fin ℓ // j ≠ j₀} → F)).card =
        (Finset.univ.filter fun z : Fin ℓ → F => z j₀ = 0).card := by
    refine Finset.card_bij
      (fun (g : {j : Fin ℓ // j ≠ j₀} → F) _ =>
        fun j : Fin ℓ => if h : j = j₀ then (0 : F) else g ⟨j, h⟩) ?_ ?_ ?_
    · intro g _
      simp only [mem_filter, mem_univ, ↓reduceDIte, and_self]
    · intro g₁ _ g₂ _ heq
      funext ⟨j, hj⟩
      have h := congrFun heq j
      simp only [hj, ↓reduceDIte] at h
      exact h
    · intro z hz
      have hz0 : z j₀ = 0 := (mem_filter.1 hz).2
      refine ⟨fun j => z j.val, mem_univ _, ?_⟩
      funext j
      by_cases h : j = j₀
      · subst h
        simp only [↓reduceDIte, hz0]
      · simp only [h, ↓reduceDIte]
  rw [← hbij, Finset.card_univ, Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun j : Fin ℓ => j ≠ j₀) = Finset.univ.erase j₀ := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
  rw [hfilter, Finset.card_erase_of_mem (mem_univ j₀), Finset.card_univ, Fintype.card_fin]

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
    hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) (v₀ + ∑ j : Fin ℓ, z j • v j) ≤ e := by
  refine hammingDist_le_of_card_filter_eq (hD'.trans (Finset.card_le_card ?_))
  intro i hi
  refine mem_filter.2 ⟨mem_univ i, ?_⟩
  obtain ⟨h0, hj⟩ := hagree i hi
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, h0]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hj j]

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
        W i := by
  refine Finset.sum_le_sum_of_subset ?_
  intro i hi
  refine mem_filter.2 ⟨mem_univ i, ?_⟩
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hagree i hi j]

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
        μ i := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hμ_nonneg i)
  intro i hi
  refine mem_filter.2 ⟨mem_univ i, ?_⟩
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hagree i hi j]

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
        W i := by
  refine Finset.sum_le_sum_of_subset ?_
  intro i hi
  refine mem_filter.2 ⟨mem_univ i, ?_⟩
  obtain ⟨h0, hj⟩ := hagree i hi
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, h0]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hj j]

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
        μ i := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hμ_nonneg i)
  intro i hi
  refine mem_filter.2 ⟨mem_univ i, ?_⟩
  obtain ⟨h0, hj⟩ := hagree i hi
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, h0]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hj j]

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
  -- Step 1: Weighted agreement `≥ θ` with `μ i ≤ 1` implies unweighted Hamming distance `≤ e`.
  have hclose_unw : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c ≤ e := by
    intro z hz
    obtain ⟨c, hcRS, hμ_ge⟩ := hclose z hz
    exact ⟨c, hcRS, hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge⟩
  -- Step 2: Apply unique-decoding unweighted curve correlated agreement.
  obtain ⟨D₀, hD₀, v, hvRS, hagree₀⟩ :=
    exists_correlatedAgreement_curve_unique hα hunique u S hS hclose_unw
  -- Step 3: Take the maximal shared agreement set `D'` and show `θ ≤ ∑ i ∈ D', μ i`.
  let D' : Finset ι := Finset.univ.filter fun i => ∀ j : Fin (d + 1), u j i = v j i
  refine ⟨D', ?_, v, hvRS, fun i hi => (mem_filter.1 hi).2⟩
  by_contra hlt
  push Not at hlt
  -- Define for each `i : ι` the error-cancellation polynomial `∑ j, (u j i - v j i) Z ^ j`.
  let f : ι → Polynomial F := fun i =>
    ∑ j : Fin (d + 1), Polynomial.C (u j i - v j i) * Polynomial.X ^ (j : ℕ)
  let badI : Finset ι := Finset.univ.filter fun i => ¬ ∀ j : Fin (d + 1), u j i = v j i
  have hf_ne : ∀ i ∈ badI, f i ≠ 0 := by
    intro i hi hzero
    have hnot : ¬ ∀ j : Fin (d + 1), u j i = v j i := (mem_filter.1 hi).2
    push Not at hnot
    obtain ⟨j₀, hj₀⟩ := hnot
    have hcoeff : (f i).coeff (j₀ : ℕ) = u j₀ i - v j₀ i := by
      simp only [f, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single j₀]
      · simp only [↓reduceIte]
      · intro j _ hj
        have hval : (j₀ : ℕ) ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
        simp only [hval, ↓reduceIte]
      · intro h; exact absurd (mem_univ j₀) h
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    exact hj₀ (sub_eq_zero.1 hcoeff.symm)
  have hf_deg : ∀ i : ι, (f i).natDegree ≤ d := by
    intro i
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le ?_)
    intro j _
    exact (Polynomial.natDegree_C_mul_X_pow_le (u j i - v j i) (j : ℕ)).trans
      (Nat.lt_succ_iff.1 j.isLt)
  -- Every `z ∈ S` agrees with `v_z` on a strictly larger set than `D'`, hence is a root of `f i`
  -- for some `i ∈ badI`.
  have hS_sub : S ⊆ badI.biUnion fun i => (f i).roots.toFinset := by
    intro z hz
    obtain ⟨c, hcRS, hμ_ge⟩ := hclose z hz
    have hc_dist : hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) c ≤ e :=
      hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge
    let vz : ι → F := ∑ j : Fin (d + 1), z ^ (j : ℕ) • v j
    have hvz_RS : vz ∈ reedSolomon α k :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvRS j)
    have hvz_dist : hammingDist (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) vz ≤ e :=
      hammingDist_curve_le_of_eq_on hD₀ hagree₀ z
    have hceq : c = vz := eq_of_hammingDist_le_reedSolomon hα hunique hcRS hvz_RS hc_dist hvz_dist
    subst hceq
    let agree_z : Finset ι :=
      Finset.univ.filter fun i => (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = vz i
    have hD'_sub : D' ⊆ agree_z := by
      intro i hi
      refine mem_filter.2 ⟨mem_univ i, ?_⟩
      have hi' := (mem_filter.1 hi).2
      simp only [vz, Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [hi' j]
    have hex : ∃ i ∈ agree_z, i ∉ D' := by
      by_contra hnone
      push Not at hnone
      have heq : D' = agree_z := Finset.Subset.antisymm hD'_sub hnone
      rw [heq] at hlt
      exact absurd hμ_ge (not_le.2 hlt)
    obtain ⟨i, hi_ag, hi_notD'⟩ := hex
    have hi_bad : i ∈ badI := by
      refine mem_filter.2 ⟨mem_univ i, fun hall => hi_notD' (mem_filter.2 ⟨mem_univ i, hall⟩)⟩
    refine mem_biUnion.2 ⟨i, hi_bad, Multiset.mem_toFinset.2 ?_⟩
    refine (Polynomial.mem_roots (hf_ne i hi_bad)).2 ?_
    rw [Polynomial.IsRoot.def, Polynomial.eval_finsetSum]
    have hterm : ∀ j : Fin (d + 1),
        (Polynomial.C (u j i - v j i) * Polynomial.X ^ (j : ℕ)).eval z =
          z ^ (j : ℕ) * u j i - z ^ (j : ℕ) * v j i := by
      intro j
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      ring
    simp only [hterm, Finset.sum_sub_distrib]
    have hi_eq : (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = vz i := (mem_filter.1 hi_ag).2
    exact sub_eq_zero.2
      (by simpa only [vz, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hi_eq)
  -- Count roots across all `i ∈ badI`: `#S ≤ #badI * d ≤ d * |ι|`, contradicting `hS`.
  have hcard_le : S.card ≤ d * Fintype.card ι := by
    calc S.card
        ≤ (badI.biUnion fun i => (f i).roots.toFinset).card := Finset.card_le_card hS_sub
      _ ≤ ∑ i ∈ badI, ((f i).roots.toFinset).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ badI, (f i).roots.card :=
          Finset.sum_le_sum fun i _ => Multiset.toFinset_card_le _
      _ ≤ ∑ i ∈ badI, (f i).natDegree := Finset.sum_le_sum fun i _ => Polynomial.card_roots' _
      _ ≤ ∑ _i ∈ badI, d := Finset.sum_le_sum fun i _ => hf_deg i
      _ = badI.card * d := by simp only [Finset.sum_const, smul_eq_mul]
      _ ≤ Fintype.card ι * d := Nat.mul_le_mul_right d (Finset.card_le_univ badI)
      _ = d * Fintype.card ι := Nat.mul_comm _ _
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
  let u : Fin 2 → (ι → F) := ![u₀, u₁]
  have hcurve_eq : ∀ z : F, (∑ j : Fin 2, z ^ (j : ℕ) • u j) = u₀ + z • u₁ := by
    intro z
    rw [Fin.sum_univ_two]
    simp only [u, Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero, Fin.val_one, pow_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hS' : 1 * Fintype.card ι < S.card := by simpa only [one_mul] using hS
  have hclose' : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin 2, z ^ (j : ℕ) • u j) i = c i), μ i := by
    intro z hz
    simpa only [hcurve_eq z] using hclose z hz
  obtain ⟨D', hD', v, hvRS, hagree⟩ :=
    exists_ratWeighted_correlatedAgreement_curve_unique hα hunique hμ_le hθ u S hS' hclose'
  refine ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ?_⟩
  exact ⟨by simpa only [u, Matrix.cons_val_zero] using hagree i hi 0,
    by simpa only [u, Matrix.cons_val_one, Matrix.cons_val_fin_one] using hagree i hi 1⟩

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
  let μ : ι → ℚ := fun i => (W i : ℚ) / (M : ℚ)
  let θ : ℚ := (B : ℚ) / (M : ℚ)
  have hMq : (0 : ℚ) < (M : ℚ) := Nat.cast_pos.2 hM
  have hμ_le : ∀ i, μ i ≤ 1 := by
    intro i
    exact (div_le_one hMq).2 (Nat.cast_le.2 (hW i))
  have hθ : ((Fintype.card ι - (Fintype.card ι - (B + M - 1) / M) : ℕ) : ℚ) - 1 < θ :=
    card_sub_sub_ceilDiv_sub_one_lt hM
  have hclose' : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), μ i := by
    intro z hz
    obtain ⟨c, hcRS, hW_ge⟩ := hclose z hz
    refine ⟨c, hcRS, ?_⟩
    simp only [μ, θ, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hW_ge) hMq.le
  obtain ⟨D', hD', v, hvRS, hagree⟩ :=
    exists_ratWeighted_correlatedAgreement_curve_unique hα hunique hμ_le hθ u S hS hclose'
  refine ⟨D', ?_, v, hvRS, hagree⟩
  simp only [μ, θ, ← Finset.sum_div] at hD'
  have hq : (B : ℚ) ≤ ((∑ i ∈ D', W i : ℕ) : ℚ) := by
    have := (div_le_div_iff_of_pos_right hMq).1 hD'
    simpa only [Nat.cast_sum] using this
  exact Nat.cast_le.1 hq

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
  let u : Fin 2 → (ι → F) := ![u₀, u₁]
  have hcurve_eq : ∀ z : F, (∑ j : Fin 2, z ^ (j : ℕ) • u j) = u₀ + z • u₁ := by
    intro z
    rw [Fin.sum_univ_two]
    simp only [u, Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero, Fin.val_one, pow_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hS' : 1 * Fintype.card ι < S.card := by simpa only [one_mul] using hS
  have hclose' : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin 2, z ^ (j : ℕ) • u j) i = c i), W i := by
    intro z hz
    simpa only [hcurve_eq z] using hclose z hz
  obtain ⟨D', hD', v, hvRS, hagree⟩ :=
    exists_weighted_correlatedAgreement_curve_unique hα hM hW hunique u S hS' hclose'
  refine ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ?_⟩
  exact ⟨by simpa only [u, Matrix.cons_val_zero] using hagree i hi 0,
    by simpa only [u, Matrix.cons_val_one, Matrix.cons_val_fin_one] using hagree i hi 1⟩

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
        d * Fintype.card ι := by
  set S := Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
    B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
      (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), W i
  by_cases hcard : S.card ≤ d * Fintype.card ι
  · exact Or.inr hcard
  · left
    have hS : d * Fintype.card ι < S.card := Nat.lt_of_not_ge hcard
    have hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), W i :=
      fun _ hz => (mem_filter.1 hz).2
    obtain ⟨D', hD', v, hvRS, hagree⟩ :=
      exists_weighted_correlatedAgreement_curve_unique hα hM hW hunique u S hS hclose
    intro z
    refine ⟨∑ j : Fin (d + 1), z ^ (j : ℕ) • v j,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvRS j),
      hD'.trans (weightedAgree_curve_ge_of_eq_on W hagree z)⟩

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
        Fintype.card ι := by
  set S := Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
    B ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), W i
  by_cases hcard : S.card ≤ Fintype.card ι
  · exact Or.inr hcard
  · left
    have hS : Fintype.card ι < S.card := Nat.lt_of_not_ge hcard
    have hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
        B ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), W i :=
      fun _ hz => (mem_filter.1 hz).2
    obtain ⟨D', hD', v₀, hv₀, v₁, hv₁, hagree⟩ :=
      exists_weighted_correlatedAgreement_unique hα hM hW hunique u₀ u₁ S hS hclose
    intro z
    refine ⟨v₀ + z • v₁, Submodule.add_mem _ hv₀ (Submodule.smul_mem _ z hv₁), ?_⟩
    refine hD'.trans (Finset.sum_le_sum_of_subset ?_)
    intro i hi
    refine mem_filter.2 ⟨mem_univ i, ?_⟩
    obtain ⟨h0, h1⟩ := hagree i hi
    simp only [Pi.add_apply, Pi.smul_apply, h0, h1]

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
        d * Fintype.card ι := by
  set S := Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
    θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
      (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), μ i
  by_cases hcard : S.card ≤ d * Fintype.card ι
  · exact Or.inr hcard
  · left
    have hS : d * Fintype.card ι < S.card := Nat.lt_of_not_ge hcard
    have hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (∑ j : Fin (d + 1), z ^ (j : ℕ) • u j) i = c i), μ i :=
      fun _ hz => (mem_filter.1 hz).2
    obtain ⟨D', hD', v, hvRS, hagree⟩ :=
      exists_ratWeighted_correlatedAgreement_curve_unique hα hunique hμ_le hθ u S hS hclose
    intro z
    refine ⟨∑ j : Fin (d + 1), z ^ (j : ℕ) • v j,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvRS j),
      hD'.trans (ratWeightedAgree_curve_ge_of_eq_on hμ_nonneg hagree z)⟩

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
        Fintype.card ι := by
  set S := Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
    θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i
  by_cases hcard : S.card ≤ Fintype.card ι
  · exact Or.inr hcard
  · left
    have hS : Fintype.card ι < S.card := Nat.lt_of_not_ge hcard
    have hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + z • u₁) i = c i), μ i :=
      fun _ hz => (mem_filter.1 hz).2
    obtain ⟨D', hD', v₀, hv₀, v₁, hv₁, hagree⟩ :=
      exists_ratWeighted_correlatedAgreement_unique hα hunique hμ_le hθ u₀ u₁ S hS hclose
    intro z
    refine ⟨v₀ + z • v₁, Submodule.add_mem _ hv₀ (Submodule.smul_mem _ z hv₁), ?_⟩
    refine hD'.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hμ_nonneg i))
    intro i hi
    refine mem_filter.2 ⟨mem_univ i, ?_⟩
    obtain ⟨h0, h1⟩ := hagree i hi
    simp only [Pi.add_apply, Pi.smul_apply, h0, h1]

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
  -- Step 1: Exclude tuples with at least one zero coordinate.
  let T_nz : Finset (Fin ℓ → F) := T.filter fun z => ∀ j : Fin ℓ, z j ≠ 0
  have hzero_le : (T \ T_nz).card ≤ ℓ * (Fintype.card F) ^ (ℓ - 1) := by
    have hsub : T \ T_nz ⊆
        (Finset.univ : Finset (Fin ℓ)).biUnion
          fun j => Finset.univ.filter fun z : Fin ℓ → F => z j = 0 := by
      intro z hz
      have hzT : z ∈ T := (mem_sdiff.1 hz).1
      have hnot : ¬ ∀ j : Fin ℓ, z j ≠ 0 := fun hall =>
        (mem_sdiff.1 hz).2 (mem_filter.2 ⟨hzT, hall⟩)
      push Not at hnot
      obtain ⟨j, hj⟩ := hnot
      exact mem_biUnion.2 ⟨j, mem_univ j, mem_filter.2 ⟨mem_univ z, hj⟩⟩
    calc (T \ T_nz).card
        ≤ ((Finset.univ : Finset (Fin ℓ)).biUnion
            fun j => Finset.univ.filter fun z : Fin ℓ → F => z j = 0).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ j : Fin ℓ, (Finset.univ.filter fun z : Fin ℓ → F => z j = 0).card :=
          Finset.card_biUnion_le
      _ = ∑ _j : Fin ℓ, (Fintype.card F) ^ (ℓ - 1) :=
          Finset.sum_congr rfl fun j _ => card_filter_coord_eq_zero j
      _ = ℓ * (Fintype.card F) ^ (ℓ - 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hT_split : T.card = T_nz.card + (T \ T_nz).card := by
    have hunion : T_nz ∪ (T \ T_nz) = T := Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
    conv_lhs => rw [← hunion]
    rw [Finset.card_union_of_disjoint Finset.disjoint_sdiff]
  have hT_nz : B_curve * (Fintype.card F) ^ (ℓ - 1) < T_nz.card := by
    have hmul : (B_curve + ℓ) * (Fintype.card F) ^ (ℓ - 1) =
        B_curve * (Fintype.card F) ^ (ℓ - 1) + ℓ * (Fintype.card F) ^ (ℓ - 1) :=
      Nat.add_mul B_curve ℓ _
    omega
  -- Step 2: Bound in terms of `|Fˣ|`.
  have hFunits_pos : 0 < Fintype.card Fˣ := by
    have hne : T_nz.Nonempty := Finset.card_pos.1 (Nat.lt_of_le_of_lt (Nat.zero_le _) hT_nz)
    obtain ⟨z₀, hz₀⟩ := hne
    have hz₀_nz : z₀ ⟨0, hℓ⟩ ≠ 0 := (mem_filter.1 hz₀).2 ⟨0, hℓ⟩
    exact Fintype.card_pos_iff.2 ⟨Units.mk0 (z₀ ⟨0, hℓ⟩) hz₀_nz⟩
  have hFunits_le : Fintype.card Fˣ ≤ Fintype.card F :=
    Fintype.card_le_of_injective Units.val Units.val_injective
  have hpow_le : (Fintype.card Fˣ) ^ (ℓ - 1) ≤ (Fintype.card F) ^ (ℓ - 1) :=
    Nat.pow_le_pow_left hFunits_le _
  have hT_nz_units : B_curve * (Fintype.card Fˣ) ^ ℓ < Fintype.card Fˣ * T_nz.card := by
    have hpow_split : (Fintype.card Fˣ) ^ ℓ = Fintype.card Fˣ * (Fintype.card Fˣ) ^ (ℓ - 1) := by
      conv_lhs => rw [show ℓ = (ℓ - 1) + 1 by omega]
      rw [pow_succ, mul_comm]
    rw [hpow_split, ← mul_assoc, mul_comm B_curve (Fintype.card Fˣ), mul_assoc]
    exact Nat.mul_lt_mul_of_pos_left
      ((Nat.mul_le_mul_left B_curve hpow_le).trans_lt hT_nz) hFunits_pos
  -- Step 3: Fiber bijection `(a, t) ↦ (a j * t ^ (j + 1))_j` on `(Fin ℓ → Fˣ) × Fˣ`.
  let phi : (Fin ℓ → Fˣ) → Fˣ → (Fin ℓ → F) := fun a t j => (a j : F) * (t : F) ^ ((j : ℕ) + 1)
  have hfiber : ∀ t : Fˣ, (Finset.univ.filter fun a : Fin ℓ → Fˣ => phi a t ∈ T_nz).card =
      T_nz.card := by
    intro t
    refine Finset.card_bij (fun a _ => phi a t) ?_ ?_ ?_
    · intro a ha
      exact (mem_filter.1 ha).2
    · intro a₁ _ a₂ _ heq
      funext j
      have hj := congrFun heq j
      have ht_ne : (t : F) ^ ((j : ℕ) + 1) ≠ 0 := pow_ne_zero _ t.ne_zero
      exact Units.ext (mul_right_cancel₀ ht_ne hj)
    · intro z hz
      have hz_nz : ∀ j : Fin ℓ, z j ≠ 0 := (mem_filter.1 hz).2
      let a : Fin ℓ → Fˣ := fun j => Units.mk0 (z j) (hz_nz j) * (t ^ ((j : ℕ) + 1))⁻¹
      have hphi : phi a t = z := by
        funext j
        simp only [phi, a, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val,
          Units.val_pow_eq_pow_val]
        rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ t.ne_zero), mul_one]
      exact ⟨a, mem_filter.2 ⟨mem_univ a, hphi.symm ▸ hz⟩, hphi⟩
  -- Step 4: Double-count and average over `a : Fin ℓ → Fˣ`.
  have hsum_eq :
      (∑ a : Fin ℓ → Fˣ, (Finset.univ.filter fun t : Fˣ => phi a t ∈ T_nz).card) =
        Fintype.card Fˣ * T_nz.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    have hinner : ∀ t : Fˣ,
        (∑ a : Fin ℓ → Fˣ, if phi a t ∈ T_nz then 1 else 0) = T_nz.card := by
      intro t
      rw [← Finset.card_filter]
      exact hfiber t
    simp only [hinner, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hsum_lt :
      (∑ _a : Fin ℓ → Fˣ, B_curve) <
        ∑ a : Fin ℓ → Fˣ, (Finset.univ.filter fun t : Fˣ => phi a t ∈ T_nz).card := by
    rw [hsum_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      smul_eq_mul, mul_comm]
    exact hT_nz_units
  obtain ⟨a, _, ha_gt⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  -- Step 5: Apply `hcurve` along the scaled degree-`ℓ` curve `u'`.
  let S : Finset F := (Finset.univ.filter fun t : Fˣ => phi a t ∈ T_nz).image Units.val
  have hS : B_curve < S.card := by
    rwa [Finset.card_image_of_injective _ Units.val_injective]
  let u' : Fin (ℓ + 1) → (ι → F) := Fin.cons u₀ (fun j => (a j : F) • u j)
  have hcurve_ok : ∀ z ∈ S, P (∑ j : Fin (ℓ + 1), z ^ (j : ℕ) • u' j) := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hz
    have ht_T : phi a t ∈ T := (mem_filter.1 (mem_filter.1 ht).2).1
    have hsum_curve :
        (∑ j : Fin (ℓ + 1), (t : F) ^ (j : ℕ) • u' j) =
          u₀ + ∑ j : Fin ℓ, (phi a t j) • u j := by
      rw [Fin.sum_univ_succ]
      simp only [u', Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.val_succ, Fin.cons_succ]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, mul_comm]
    rw [hsum_curve]
    exact hclose (phi a t) ht_T
  obtain ⟨D', hQD', v', hv'RS, hagree'⟩ := hcurve u' S hS hcurve_ok
  -- Step 6: Unscale by `(a j)⁻¹` to recover codewords for `u₀` and `u j`.
  refine ⟨D', hQD', v' 0, hv'RS 0, fun j => ((a j : F)⁻¹) • v' j.succ,
    fun j => Submodule.smul_mem _ _ (hv'RS j.succ), fun i hi => ?_⟩
  refine ⟨by simpa only [u', Fin.cons_zero] using hagree' i hi 0, fun j => ?_⟩
  have hscaled : (a j : F) * u j i = v' j.succ i := by
    simpa only [u', Fin.cons_succ, Pi.smul_apply, smul_eq_mul] using hagree' i hi j.succ
  simp only [Pi.smul_apply, smul_eq_mul, ← hscaled, inv_mul_cancel_left₀ (a j).ne_zero]

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
    push Not at hall
    obtain ⟨y, hy⟩ := hall
    set T : Finset (Fin ℓ → F) :=
      Finset.univ.filter fun z : Fin ℓ → F => P (u₀ + ∑ j : Fin ℓ, z j • u j)
    have hy_notT : y ∉ T := fun h => hy (mem_filter.1 h).2
    let B_nz : Finset (Fin ℓ → F) := Finset.univ.erase 0
    have hB_nz_card : B_nz.card = (Fintype.card F) ^ ℓ - 1 := by
      rw [Finset.card_erase_of_mem (mem_univ 0), Finset.card_univ, Fintype.card_pi,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    let pairs : Finset ((Fin ℓ → F) × Fˣ) :=
      (B_nz ×ˢ (Finset.univ : Finset Fˣ)).filter fun p => y + (p.2 : F) • p.1 ∈ T
    have hpairs_eq : pairs.card = (Fintype.card F - 1) * T.card := by
      have hbij : pairs.card = (T ×ˢ (Finset.univ : Finset Fˣ)).card := by
        refine Finset.card_bij (fun p _ => (y + (p.2 : F) • p.1, p.2)) ?_ ?_ ?_
        · intro p hp
          exact mem_product.2 ⟨(mem_filter.1 hp).2, mem_univ p.2⟩
        · intro p₁ _ p₂ _ heq
          obtain ⟨h1, h2⟩ := Prod.mk.inj heq
          rw [h2] at h1
          have hsmul : (p₂.2 : F) • p₁.1 = (p₂.2 : F) • p₂.1 := add_left_cancel h1
          have hb : p₁.1 = p₂.1 := by
            funext j
            have hj := congrFun hsmul j
            exact mul_left_cancel₀ p₂.2.ne_zero hj
          exact Prod.ext hb h2
        · intro q hq
          obtain ⟨hzT, _⟩ := mem_product.1 hq
          let b : Fin ℓ → F := ((q.2⁻¹ : Fˣ) : F) • (q.1 - y)
          have hb_ne : b ≠ 0 := by
            intro h0
            have hzy : q.1 - y = 0 := by
              have h1 := congrArg (fun w : Fin ℓ → F => (q.2 : F) • w) h0
              simp only [b, smul_smul, Units.mul_inv, one_smul, smul_zero] at h1
              exact h1
            exact hy_notT (sub_eq_zero.1 hzy ▸ hzT)
          have hmem_pair : (b, q.2) ∈ pairs := by
            refine mem_filter.2 ⟨mem_product.2 ⟨mem_erase.2 ⟨hb_ne, mem_univ b⟩, mem_univ q.2⟩, ?_⟩
            have hyz : y + (q.2 : F) • b = q.1 := by
              simp only [b, smul_smul, Units.mul_inv, one_smul, add_sub_cancel]
            rwa [hyz]
          refine ⟨(b, q.2), hmem_pair, Prod.ext ?_ rfl⟩
          simp only [b, smul_smul, Units.mul_inv, one_smul, add_sub_cancel]
      rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_units, Nat.mul_comm]
    have hline_eval : ∀ (b : Fin ℓ → F) (t : F),
        u₀ + ∑ j : Fin ℓ, (y + t • b) j • u j =
          (u₀ + ∑ j : Fin ℓ, y j • u j) + t • (∑ j : Fin ℓ, b j • u j) := by
      intro b t
      funext i
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
      have hre : ∑ j : Fin ℓ, t * b j * u j i = ∑ j : Fin ℓ, t * (b j * u j i) :=
        Finset.sum_congr rfl fun j _ => by ring
      rw [hre, ← add_assoc]
    have hfiber_le : ∀ b ∈ B_nz,
        ((Finset.univ : Finset Fˣ).filter fun t : Fˣ => y + (t : F) • b ∈ T).card ≤ B_line := by
      intro b _
      set Sb_u := (Finset.univ : Finset Fˣ).filter fun t : Fˣ => y + (t : F) • b ∈ T
      let Sb : Finset F := Sb_u.image fun t : Fˣ => (t : F)
      have hcard_eq : Sb.card = Sb_u.card :=
        Finset.card_image_of_injective _ Units.val_injective
      by_contra hgt
      have hSb_gt : B_line < Sb.card := by omega
      have hclose_b : ∀ t ∈ Sb,
          P ((u₀ + ∑ j : Fin ℓ, y j • u j) + t • (∑ j : Fin ℓ, b j • u j)) := by
        intro t ht
        obtain ⟨tu, htu, rfl⟩ := mem_image.1 ht
        have hmemT : y + (tu : F) • b ∈ T := (mem_filter.1 htu).2
        have hP := (mem_filter.1 hmemT).2
        rwa [hline_eval b (tu : F)] at hP
      have hall_b := hline (u₀ + ∑ j : Fin ℓ, y j • u j) (∑ j : Fin ℓ, b j • u j) Sb hSb_gt
        hclose_b
      have h0 := hall_b 0
      rw [zero_smul, add_zero] at h0
      exact hy h0
    have hpairs_le : pairs.card ≤ B_line * ((Fintype.card F) ^ ℓ - 1) := by
      have hsum_eq : pairs.card =
          ∑ b ∈ B_nz, ((Finset.univ : Finset Fˣ).filter fun t : Fˣ =>
            y + (t : F) • b ∈ T).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.card_filter]
      calc pairs.card
          = ∑ b ∈ B_nz, ((Finset.univ : Finset Fˣ).filter fun t : Fˣ =>
              y + (t : F) • b ∈ T).card := hsum_eq
        _ ≤ ∑ _b ∈ B_nz, B_line := Finset.sum_le_sum fun b hb => hfiber_le b hb
        _ = B_nz.card * B_line := by simp only [Finset.sum_const, smul_eq_mul]
        _ = B_line * ((Fintype.card F) ^ ℓ - 1) := by rw [hB_nz_card, Nat.mul_comm]
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
  · have ha₀ : a₀ ≠ 0 := hne.resolve_right (by push Not; exact hall0)
    have hemp : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      have h0 := (mem_filter.1 hz).2
      have hsum0 : ∑ j : Fin ℓ, z j * a j = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hall0 j, mul_zero]
      rw [hsum0, add_zero] at h0
      exact ha₀ h0
    rw [hemp, Finset.card_empty]
    exact Nat.zero_le _
  · push Not at hall0
    obtain ⟨j₀, hj₀⟩ := hall0
    let proj : (Fin ℓ → F) → ({j : Fin ℓ // j ≠ j₀} → F) := fun z j => z j.1
    have hinj : Set.InjOn proj (S : Set (Fin ℓ → F)) := by
      intro z₁ hz₁ z₂ hz₂ hproj
      have h1 : a₀ + ∑ j : Fin ℓ, z₁ j * a j = 0 := (mem_filter.1 hz₁).2
      have h2 : a₀ + ∑ j : Fin ℓ, z₂ j * a j = 0 := (mem_filter.1 hz₂).2
      have hne_eq : ∀ j : Fin ℓ, j ≠ j₀ → z₁ j = z₂ j :=
        fun j hj => congrFun hproj ⟨j, hj⟩
      have hsum_er : ∑ j ∈ Finset.univ.erase j₀, z₁ j * a j =
          ∑ j ∈ Finset.univ.erase j₀, z₂ j * a j :=
        Finset.sum_congr rfl fun j hj => by rw [hne_eq j (mem_erase.1 hj).1]
      rw [← Finset.add_sum_erase _ _ (mem_univ j₀)] at h1 h2
      have hz₀ : z₁ j₀ = z₂ j₀ := by
        have hmul : (z₁ j₀ - z₂ j₀) * a j₀ = 0 := by
          rw [hsum_er] at h1
          have hsub : (a₀ + (z₁ j₀ * a j₀ + ∑ j ∈ Finset.univ.erase j₀, z₂ j * a j)) -
              (a₀ + (z₂ j₀ * a j₀ + ∑ j ∈ Finset.univ.erase j₀, z₂ j * a j)) = 0 :=
            sub_eq_zero.2 (h1.trans h2.symm)
          calc (z₁ j₀ - z₂ j₀) * a j₀
              = (a₀ + (z₁ j₀ * a j₀ + ∑ j ∈ Finset.univ.erase j₀, z₂ j * a j)) -
                  (a₀ + (z₂ j₀ * a j₀ + ∑ j ∈ Finset.univ.erase j₀, z₂ j * a j)) := by ring
            _ = 0 := hsub
        exact sub_eq_zero.1 ((mul_eq_zero.1 hmul).resolve_right hj₀)
      funext j
      by_cases hj : j = j₀
      · subst hj; exact hz₀
      · exact hne_eq j hj
    have hcard_sub : Fintype.card {j : Fin ℓ // j ≠ j₀} = ℓ - 1 := by
      have h1 := Fintype.card_subtype_compl (fun j : Fin ℓ => j = j₀)
      simp only [Fintype.card_fin, Fintype.card_unique] at h1
      exact h1
    calc S.card
        = (S.image proj).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Fintype.card ({j : Fin ℓ // j ≠ j₀} → F) := Finset.card_le_univ _
      _ = (Fintype.card F) ^ (ℓ - 1) := by
          rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, hcard_sub]

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
  have hT_pos : 0 < T.card := by
    by_contra h0
    have hcz : T.card = 0 := by omega
    rw [hcz, Nat.mul_zero] at hT
    exact Nat.not_lt_zero _ hT
  obtain ⟨z_ne, hz_ne⟩ := Finset.card_pos.1 hT_pos
  obtain ⟨c_ne, _, hc_ne_ge⟩ := hclose z_ne hz_ne
  have hBW_le_tot : B_W ≤ ∑ i : ι, W i :=
    hc_ne_ge.trans (Finset.sum_le_sum_of_subset fun i _ => mem_univ i)
  intro d
  by_cases hd0 : ∀ j : Fin m, d j = 0
  · refine ⟨0, C.zero_mem, ?_⟩
    have hzero : (∑ j : Fin m, d j • u j) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hd0 j, zero_smul]
    rw [hzero]
    simpa only [Pi.zero_apply, eq_self, filter_true_of_mem (fun _ _ => trivial)] using hBW_le_tot
  · push Not at hd0
    obtain ⟨j₀, hj₀⟩ := hd0
    have hm_pos : 1 ≤ m := Fin.pos j₀
    have hq_pos : 0 < Fintype.card F := Fintype.card_pos
    have hpow_split : (Fintype.card F) ^ m = Fintype.card F * (Fintype.card F) ^ (m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm_pos, pow_succ, Nat.mul_comm]
    have hT_gt : B_line * (Fintype.card F) ^ (m - 1) < T.card := by
      have hmul : Fintype.card F * (B_line * (Fintype.card F) ^ (m - 1)) <
          Fintype.card F * T.card := by
        calc Fintype.card F * (B_line * (Fintype.card F) ^ (m - 1))
            = B_line * (Fintype.card F * (Fintype.card F) ^ (m - 1)) := by ring
          _ = B_line * (Fintype.card F) ^ m := by rw [← hpow_split]
          _ < Fintype.card F * T.card := hT
      exact Nat.lt_of_mul_lt_mul_left hmul
    let H : Finset (Fin m → F) := Finset.univ.filter fun z => z j₀ = 0
    have hbij_univ : (H ×ˢ (Finset.univ : Finset F)).card =
        (Finset.univ : Finset (Fin m → F)).card := by
      refine Finset.card_bij (fun p _ => p.1 + p.2 • d) (fun _ _ => mem_univ _) ?_ ?_
      · intro p₁ hp₁ p₂ hp₂ heq
        have hz₁ : p₁.1 j₀ = 0 := (mem_filter.1 (mem_product.1 hp₁).1).2
        have hz₂ : p₂.1 j₀ = 0 := (mem_filter.1 (mem_product.1 hp₂).1).2
        have hj := congrFun heq j₀
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz₁, hz₂, zero_add] at hj
        have ht : p₁.2 = p₂.2 := mul_right_cancel₀ hj₀ hj
        have hz : p₁.1 = p₂.1 := by
          rw [ht] at heq
          exact add_right_cancel heq
        exact Prod.ext hz ht
      · intro y _
        let t : F := y j₀ * (d j₀)⁻¹
        let z : Fin m → F := y - t • d
        have hzH : z ∈ H := by
          refine mem_filter.2 ⟨mem_univ z, ?_⟩
          simp only [z, t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
            mul_assoc, inv_mul_cancel₀ hj₀, mul_one, sub_self]
        refine ⟨(z, t), mem_product.2 ⟨hzH, mem_univ t⟩, ?_⟩
        simp only [z, sub_add_cancel]
    have hH_card : H.card = (Fintype.card F) ^ (m - 1) := by
      rw [Finset.card_product, Finset.card_univ, Finset.card_univ, Fintype.card_pi,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hbij_univ
      have hmul : Fintype.card F * H.card = Fintype.card F * (Fintype.card F) ^ (m - 1) := by
        calc Fintype.card F * H.card
            = H.card * Fintype.card F := Nat.mul_comm _ _
          _ = (Fintype.card F) ^ m := hbij_univ
          _ = Fintype.card F * (Fintype.card F) ^ (m - 1) := hpow_split
      exact Nat.eq_of_mul_eq_mul_left hq_pos hmul
    have hsum_T : (∑ z ∈ H, ((Finset.univ : Finset F).filter fun t => z + t • d ∈ T).card) =
        T.card := by
      have hprod_eq : ((H ×ˢ (Finset.univ : Finset F)).filter fun p => p.1 + p.2 • d ∈ T).card =
          T.card := by
        refine Finset.card_bij (fun p _ => p.1 + p.2 • d)
          (fun p hp => (mem_filter.1 hp).2) ?_ ?_
        · intro p₁ hp₁ p₂ hp₂ heq
          have hz₁ : p₁.1 j₀ = 0 := (mem_filter.1 (mem_product.1 (mem_filter.1 hp₁).1).1).2
          have hz₂ : p₂.1 j₀ = 0 := (mem_filter.1 (mem_product.1 (mem_filter.1 hp₂).1).1).2
          have hj := congrFun heq j₀
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz₁, hz₂, zero_add] at hj
          have ht : p₁.2 = p₂.2 := mul_right_cancel₀ hj₀ hj
          have hz : p₁.1 = p₂.1 := by rw [ht] at heq; exact add_right_cancel heq
          exact Prod.ext hz ht
        · intro y hyT
          let t : F := y j₀ * (d j₀)⁻¹
          let z : Fin m → F := y - t • d
          have hzH : z ∈ H := by
            refine mem_filter.2 ⟨mem_univ z, ?_⟩
            simp only [z, t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
              mul_assoc, inv_mul_cancel₀ hj₀, mul_one, sub_self]
          have heq : z + t • d = y := by simp only [z, sub_add_cancel]
          exact ⟨(z, t), mem_filter.2 ⟨mem_product.2 ⟨hzH, mem_univ t⟩, heq.symm ▸ hyT⟩, heq⟩
      rw [← hprod_eq, Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.card_filter]
    have hsum_lt : (∑ _z ∈ H, B_line) <
        ∑ z ∈ H, ((Finset.univ : Finset F).filter fun t => z + t • d ∈ T).card := by
      rw [hsum_T, Finset.sum_const, smul_eq_mul, hH_card, Nat.mul_comm]
      exact hT_gt
    obtain ⟨z, _, hz_gt⟩ := Finset.exists_lt_of_sum_lt hsum_lt
    set S : Finset F := (Finset.univ : Finset F).filter fun t => z + t • d ∈ T
    have hline_ok : ∀ t ∈ S, ∃ c ∈ C,
        B_W ≤ ∑ i ∈ Finset.univ.filter
          (fun i => ((u₀ + ∑ j : Fin m, z j • u j) + t • (∑ j : Fin m, d j • u j)) i = c i),
          W i := by
      intro t ht
      have hmemT : z + t • d ∈ T := (mem_filter.1 ht).2
      have hrew : (u₀ + ∑ j : Fin m, z j • u j) + t • (∑ j : Fin m, d j • u j) =
          u₀ + ∑ j : Fin m, (z + t • d) j • u j := by
        funext i
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul,
          Finset.sum_add_distrib, Finset.mul_sum]
        have hre : ∑ j : Fin m, t * (d j * u j i) = ∑ j : Fin m, t * d j * u j i :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [hre, add_assoc]
      rw [hrew]
      exact hclose (z + t • d) hmemT
    obtain ⟨D', hD'_ge, _, _, w₁, hw₁C, hag⟩ :=
      hline (u₀ + ∑ j : Fin m, z j • u j) (∑ j : Fin m, d j • u j) S hz_gt hline_ok
    refine ⟨w₁, hw₁C, hD'_ge.trans (Finset.sum_le_sum_of_subset fun i hi => ?_)⟩
    exact mem_filter.2 ⟨mem_univ i, (hag i hi).2⟩

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
  have hT_le : T.card ≤ (Fintype.card F) ^ ℓ := by
    calc T.card ≤ Fintype.card (Fin ℓ → F) := Finset.card_le_univ T
      _ = (Fintype.card F) ^ ℓ := by
          rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpow_pos : 0 < (Fintype.card F) ^ ℓ := Nat.pow_pos Fintype.card_pos
  have hB_lt_q : B_line < Fintype.card F := lt_card_field_of_density_threshold hT
  have hdir : ∀ d : Fin ℓ → F, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (∑ j : Fin ℓ, d j • u j) i = c i), W i :=
    all_close_dir_of_line_correlatedAgreement hline u₀ u T hT hclose
  let u' : Fin (ℓ + 1) → (ι → F) := Fin.cons (α := fun _ => ι → F) u₀ u
  let consF : F → (Fin ℓ → F) → (Fin (ℓ + 1) → F) := Fin.cons (α := fun _ => F)
  let T₀ : Finset (Fin (ℓ + 1) → F) :=
    (Finset.univ : Finset (Fin ℓ → F)).image (consF 0)
  let T₁ : Finset (Fin (ℓ + 1) → F) :=
    ((Finset.univ : Finset Fˣ) ×ˢ T).image fun p => consF (p.1 : F) ((p.1 : F) • p.2)
  have hT₀_card : T₀.card = (Fintype.card F) ^ ℓ := by
    have hinj : Function.Injective (consF 0) := by
      intro d₁ d₂ h
      funext j
      simpa only [consF, Fin.cons_succ] using congrFun h j.succ
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_pi,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hT₁_card : T₁.card = (Fintype.card F - 1) * T.card := by
    have hinj : Function.Injective
        (fun p : Fˣ × (Fin ℓ → F) => consF (p.1 : F) ((p.1 : F) • p.2)) := by
      intro p₁ p₂ h
      have hs_val : (p₁.1 : F) = (p₂.1 : F) := by
        simpa only [consF, Fin.cons_zero] using congrFun h 0
      have hs : p₁.1 = p₂.1 := Units.ext hs_val
      have hz : p₁.2 = p₂.2 := by
        funext j
        have hj := congrFun h j.succ
        simp only [consF, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, hs_val] at hj
        exact mul_left_cancel₀ p₂.1.ne_zero hj
      exact Prod.ext hs hz
    rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ,
      Fintype.card_units]
  have hdisj : Disjoint T₀ T₁ := by
    refine Finset.disjoint_left.2 fun x hx₀ hx₁ => ?_
    obtain ⟨d, _, rfl⟩ := mem_image.1 hx₀
    obtain ⟨p, _, hp_eq⟩ := mem_image.1 hx₁
    have h0 := congrFun hp_eq 0
    simp only [consF, Fin.cons_zero] at h0
    exact p.1.ne_zero h0
  let T_bar : Finset (Fin (ℓ + 1) → F) := T₀ ∪ T₁
  have hT_bar_card : T_bar.card = (Fintype.card F) ^ ℓ + (Fintype.card F - 1) * T.card := by
    rw [Finset.card_union_of_disjoint hdisj, hT₀_card, hT₁_card]
  have hT_bar_gt : B_line * (Fintype.card F) ^ (ℓ + 1) < Fintype.card F * T_bar.card := by
    have hq_ge2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have h1 : B_line * (Fintype.card F) ^ ℓ < Fintype.card F * (Fintype.card F) ^ ℓ :=
      Nat.mul_lt_mul_of_pos_right hB_lt_q hpow_pos
    have h2 : (Fintype.card F - 1) * (B_line * (Fintype.card F) ^ ℓ) ≤
        (Fintype.card F - 1) * (Fintype.card F * T.card) :=
      Nat.mul_le_mul_left _ hT.le
    calc B_line * (Fintype.card F) ^ (ℓ + 1)
        = (1 + (Fintype.card F - 1)) * (B_line * (Fintype.card F) ^ ℓ) := by
            have hq1 : 1 + (Fintype.card F - 1) = Fintype.card F := by omega
            rw [hq1, pow_succ]
            ring
      _ = B_line * (Fintype.card F) ^ ℓ +
            (Fintype.card F - 1) * (B_line * (Fintype.card F) ^ ℓ) := by ring
      _ < Fintype.card F * (Fintype.card F) ^ ℓ +
            (Fintype.card F - 1) * (Fintype.card F * T.card) :=
          Nat.add_lt_add_of_lt_of_le h1 h2
      _ = Fintype.card F * ((Fintype.card F) ^ ℓ + (Fintype.card F - 1) * T.card) := by ring
      _ = Fintype.card F * T_bar.card := by rw [hT_bar_card]
  have hclose_bar : ∀ x ∈ T_bar, ∃ c ∈ C,
      B_W ≤ ∑ i ∈ Finset.univ.filter
        (fun i => ((0 : ι → F) + ∑ k : Fin (ℓ + 1), x k • u' k) i = c i), W i := by
    intro x hx
    rw [zero_add]
    rcases mem_union.1 hx with hx₀ | hx₁
    · obtain ⟨d, _, rfl⟩ := mem_image.1 hx₀
      have hsum : (∑ k : Fin (ℓ + 1), (consF 0 d) k • u' k) =
          ∑ j : Fin ℓ, d j • u j := by
        rw [Fin.sum_univ_succ]
        simp only [u', consF, Fin.cons_zero, Fin.cons_succ, zero_smul, zero_add]
      rw [hsum]
      exact hdir d
    · obtain ⟨p, hp, rfl⟩ := mem_image.1 hx₁
      have hzT : p.2 ∈ T := (mem_product.1 hp).2
      obtain ⟨c, hcC, hc_ge⟩ := hclose p.2 hzT
      refine ⟨(p.1 : F) • c, C.smul_mem (p.1 : F) hcC, ?_⟩
      have hsum : (∑ k : Fin (ℓ + 1), (consF (p.1 : F) ((p.1 : F) • p.2)) k • u' k) =
          (p.1 : F) • (u₀ + ∑ j : Fin ℓ, p.2 j • u j) := by
        rw [Fin.sum_univ_succ]
        simp only [u', consF, Fin.cons_zero, Fin.cons_succ, Pi.smul_apply, smul_add,
          Finset.smul_sum, smul_smul, smul_eq_mul]
      rw [hsum]
      have hfilt : (Finset.univ.filter fun i =>
            ((p.1 : F) • (u₀ + ∑ j : Fin ℓ, p.2 j • u j)) i = ((p.1 : F) • c) i) =
          Finset.univ.filter fun i => (u₀ + ∑ j : Fin ℓ, p.2 j • u j) i = c i := by
        ext i
        simp only [mem_filter, mem_univ, true_and, Pi.smul_apply, smul_eq_mul,
          mul_right_inj' p.1.ne_zero]
      rwa [hfilt]
  have hall_bar := all_close_dir_of_line_correlatedAgreement hline 0 u' T_bar hT_bar_gt hclose_bar
  intro z
  obtain ⟨c, hcC, hc_ge⟩ := hall_bar (consF 1 z)
  have hsum : (∑ k : Fin (ℓ + 1), (consF 1 z) k • u' k) =
      u₀ + ∑ j : Fin ℓ, z j • u j := by
    rw [Fin.sum_univ_succ]
    simp only [u', consF, Fin.cons_zero, Fin.cons_succ, one_smul]
  rw [hsum] at hc_ge
  exact ⟨c, hcC, hc_ge⟩

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
  let suppW : Finset ι := Finset.univ.filter fun i => W i ≠ 0
  have hsum_supp : ∀ X : Finset ι, ∑ i ∈ X ∩ suppW, W i = ∑ i ∈ X, W i := by
    intro X
    refine Finset.sum_subset Finset.inter_subset_left fun i hiX hiNot => ?_
    by_contra hne
    exact hiNot (mem_inter.2 ⟨hiX, mem_filter.2 ⟨mem_univ i, hne⟩⟩)
  by_cases hℓ0 : ℓ = 0
  · subst hℓ0
    obtain ⟨v₀, hv₀, hge⟩ := hall 0
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hge
    let D' : Finset ι := (Finset.univ.filter fun i => u₀ i = v₀ i) ∩ suppW
    refine ⟨D', fun i hi => (mem_filter.1 (mem_inter.1 hi).2).2, ?_,
      v₀, hv₀, Fin.elim0, fun j => j.elim0,
      fun i hi => ⟨(mem_filter.1 (mem_inter.1 hi).1).2, fun j => j.elim0⟩⟩
    rw [hsum_supp]
    exact hge
  · by_cases hℓ1 : ℓ = 1
    · subst hℓ1
      have hline1 : ∀ t : F, ∃ c ∈ C,
          B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + t • u 0) i = c i), W i := by
        intro t
        simpa only [Fin.sum_univ_one] using hall (fun _ => t)
      obtain ⟨D₀, hD₀_ge, v₀, hv₀, v₁, hv₁, hag⟩ := hline_all le_rfl u₀ (u 0) hline1
      refine ⟨D₀ ∩ suppW, fun i hi => (mem_filter.1 (mem_inter.1 hi).2).2, ?_,
        v₀, hv₀, fun _ => v₁, fun _ => hv₁, fun i hi => ?_⟩
      · rw [hsum_supp]
        exact hD₀_ge
      · obtain ⟨h0, h1⟩ := hag i (mem_inter.1 hi).1
        exact ⟨h0, fun j => by fin_cases j; exact h1⟩
    · have hℓ2 : 2 ≤ ℓ := by omega
      have hL_lt : L < Fintype.card F := hL hℓ2
      let u_aff : (Fin ℓ → F) → (ι → F) := fun z => u₀ + ∑ j : Fin ℓ, z j • u j
      let agreeW : (ι → F) → (ι → F) → ℕ :=
        fun w c => ∑ i ∈ Finset.univ.filter (fun i => w i = c i), W i
      let C_fin : Finset (ι → F) := Finset.univ.filter fun c => c ∈ C
      have hC_ne : C_fin.Nonempty := ⟨0, mem_filter.2 ⟨mem_univ 0, C.zero_mem⟩⟩
      let score : (Fin ℓ → F) → ℕ := fun z => C_fin.sup' hC_ne (fun c => agreeW (u_aff z) c)
      obtain ⟨z_star, _, hz_min⟩ :=
        Finset.exists_min_image (Finset.univ : Finset (Fin ℓ → F)) score ⟨0, mem_univ 0⟩
      set B_star : ℕ := score z_star
      set u_star : ι → F := u_aff z_star
      have hBW_le_Bstar : B_W ≤ B_star := by
        obtain ⟨c₀, hc₀C, hc₀_ge⟩ := hall z_star
        have hc₀_le : agreeW u_star c₀ ≤ B_star :=
          Finset.le_sup' (fun c => agreeW u_star c) (mem_filter.2 ⟨mem_univ c₀, hc₀C⟩)
        exact hc₀_ge.trans hc₀_le
      have hall_Bstar : ∀ z : Fin ℓ → F, ∃ c ∈ C, B_star ≤ agreeW (u_aff z) c := by
        intro z
        obtain ⟨c, hc_mem, hc_eq⟩ := Finset.exists_mem_eq_sup' hC_ne (fun c => agreeW (u_aff z) c)
        refine ⟨c, (mem_filter.1 hc_mem).2, ?_⟩
        have hmin : B_star ≤ score z := hz_min z (mem_univ z)
        dsimp only [score] at hmin
        omega
      have hmax_ustar : ∀ c ∈ C, agreeW u_star c ≤ B_star := fun c hcC =>
        Finset.le_sup' (fun c' => agreeW u_star c') (mem_filter.2 ⟨mem_univ c, hcC⟩)
      obtain ⟨Lraw, hLraw_card, hLraw_mem⟩ := hlist u_star
      let L_star : Finset (ι → F) := Lraw.filter fun c => c ∈ C ∧ B_star ≤ agreeW u_star c
      have hLstar_card : L_star.card ≤ L := (Finset.card_filter_le _ _).trans hLraw_card
      have hLstar_ne : L_star.Nonempty := by
        obtain ⟨c_s, hc_sC, hc_s_ge⟩ := hall_Bstar z_star
        exact ⟨c_s, mem_filter.2
          ⟨hLraw_mem c_s hc_sC (hBW_le_Bstar.trans hc_s_ge), hc_sC, hc_s_ge⟩⟩
      let D_star : (ι → F) → Finset ι := fun c => suppW.filter fun i => u_star i = c i
      have hDstar_eq : ∀ c : ι → F,
          (Finset.univ.filter fun i => u_star i = c i) ∩ suppW = D_star c := by
        intro c
        ext i
        simp only [D_star, mem_inter, mem_filter, mem_univ, true_and, and_comm]
      have hDstar_sum : ∀ c : ι → F, ∑ i ∈ D_star c, W i = agreeW u_star c := by
        intro c
        rw [← hDstar_eq c, hsum_supp]
      let K_sub : (ι → F) → Submodule F (Fin ℓ → F) := fun c =>
        { carrier := {d : Fin ℓ → F | ∃ w ∈ C, ∀ i ∈ D_star c, (∑ j : Fin ℓ, d j • u j) i = w i}
          zero_mem' := ⟨0, C.zero_mem, fun i _ => by
            simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]⟩
          add_mem' := by
            rintro d₁ d₂ ⟨w₁, hw₁, hag₁⟩ ⟨w₂, hw₂, hag₂⟩
            refine ⟨w₁ + w₂, C.add_mem hw₁ hw₂, fun i hi => ?_⟩
            have hsum_add : (∑ j : Fin ℓ, (d₁ + d₂) j • u j) i =
                (∑ j : Fin ℓ, d₁ j • u j) i + (∑ j : Fin ℓ, d₂ j • u j) i := by
              simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul,
                Finset.sum_add_distrib]
            rw [hsum_add, hag₁ i hi, hag₂ i hi, Pi.add_apply]
          smul_mem' := by
            rintro a d ⟨w, hw, hag⟩
            refine ⟨a • w, C.smul_mem a hw, fun i hi => ?_⟩
            have hsum_smul : (∑ j : Fin ℓ, (a • d) j • u j) i =
                a * (∑ j : Fin ℓ, d j • u j) i := by
              simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
            rw [hsum_smul, hag i hi, Pi.smul_apply, smul_eq_mul] }
      let U_fin : (ι → F) → Finset (Fin ℓ → F) :=
        fun c => Finset.univ.filter fun z => z - z_star ∈ K_sub c
      have hcover : (Finset.univ : Finset (Fin ℓ → F)) ⊆ L_star.biUnion U_fin := by
        intro z _
        let b_dir : ι → F := ∑ j : Fin ℓ, (z - z_star) j • u j
        have hline_z : ∀ t : F, ∃ c ∈ C, B_star ≤ agreeW (u_star + t • b_dir) c := by
          intro t
          have hcomb : u_star + t • b_dir = u_aff (z_star + t • (z - z_star)) := by
            funext i
            simp only [u_star, u_aff, b_dir, Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
              Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
            have hre : ∑ j : Fin ℓ, t * ((z j - z_star j) * u j i) =
                ∑ j : Fin ℓ, t * (z j - z_star j) * u j i :=
              Finset.sum_congr rfl fun j _ => by ring
            rw [hre, add_assoc]
          rw [hcomb]
          exact hall_Bstar (z_star + t • (z - z_star))
        obtain ⟨D_z, hDz_ge, w₀, hw₀C, w₁, hw₁C, hag_z⟩ :=
          hline_all hBW_le_Bstar u_star b_dir hline_z
        have hw₀_agree_ge : B_star ≤ agreeW u_star w₀ :=
          hDz_ge.trans (Finset.sum_le_sum_of_subset fun i hi =>
            mem_filter.2 ⟨mem_univ i, (hag_z i hi).1⟩)
        have hw₀_mem : w₀ ∈ L_star := mem_filter.2
          ⟨hLraw_mem w₀ hw₀C (hBW_le_Bstar.trans hw₀_agree_ge), hw₀C, hw₀_agree_ge⟩
        have hDstar_sub_Dz : D_star w₀ ⊆ D_z := by
          intro i₀ hi₀
          by_contra hi₀_not
          have hsub_er : D_z ∩ suppW ⊆ (D_star w₀).erase i₀ := by
            intro i hi
            obtain ⟨hiDz, hiSupp⟩ := mem_inter.1 hi
            have hne : i ≠ i₀ := fun heq => hi₀_not (heq ▸ hiDz)
            exact mem_erase.2 ⟨hne, mem_filter.2 ⟨hiSupp, (hag_z i hiDz).1⟩⟩
          have hsum_er_le : ∑ i ∈ D_z ∩ suppW, W i ≤ ∑ i ∈ (D_star w₀).erase i₀, W i :=
            Finset.sum_le_sum_of_subset hsub_er
          have hsplit := Finset.add_sum_erase (D_star w₀) W hi₀
          have hW_pos : 0 < W i₀ :=
            Nat.pos_of_ne_zero (mem_filter.1 (mem_filter.1 hi₀).1).2
          rw [hsum_supp] at hsum_er_le
          rw [hDstar_sum] at hsplit
          have hle_max := hmax_ustar w₀ hw₀C
          omega
        have hz_in_U : z ∈ U_fin w₀ := by
          refine mem_filter.2 ⟨mem_univ z, w₁, hw₁C, fun i hi => ?_⟩
          exact (hag_z i (hDstar_sub_Dz hi)).2
        exact mem_biUnion.2 ⟨w₀, hw₀_mem, hz_in_U⟩
      obtain ⟨v_star, hv_star_mem, hv_star_max⟩ :=
        Finset.exists_max_image L_star (fun c => (U_fin c).card) hLstar_ne
      have hv_starC : v_star ∈ C := (mem_filter.1 hv_star_mem).2.1
      have hv_star_ge : B_star ≤ agreeW u_star v_star := (mem_filter.1 hv_star_mem).2.2
      have hz_star_in : z_star ∈ U_fin v_star :=
        mem_filter.2 ⟨mem_univ z_star, by rw [sub_self]; exact (K_sub v_star).zero_mem⟩
      have hU_pos : 0 < (U_fin v_star).card := Finset.card_pos.2 ⟨z_star, hz_star_in⟩
      have hpigeon : (Fintype.card F) ^ ℓ ≤ L * (U_fin v_star).card := by
        calc (Fintype.card F) ^ ℓ
            = (Finset.univ : Finset (Fin ℓ → F)).card := by
                rw [Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
                  Fintype.card_fin]
          _ ≤ (L_star.biUnion U_fin).card := Finset.card_le_card hcover
          _ ≤ ∑ c ∈ L_star, (U_fin c).card := Finset.card_biUnion_le
          _ ≤ ∑ _c ∈ L_star, (U_fin v_star).card :=
              Finset.sum_le_sum fun c hc => hv_star_max c hc
          _ = L_star.card * (U_fin v_star).card := by simp only [Finset.sum_const, smul_eq_mul]
          _ ≤ L * (U_fin v_star).card := Nat.mul_le_mul_right _ hLstar_card
      have hU_eq_K : (U_fin v_star).card = Fintype.card (K_sub v_star) := by
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun z hz => (⟨z - z_star, (mem_filter.1 hz).2⟩ : K_sub v_star))
          (fun _ _ => mem_univ _) ?_ ?_
        · intro z₁ _ z₂ _ heq
          have hsub : z₁ - z_star = z₂ - z_star := Subtype.ext_iff.1 heq
          exact sub_left_inj.1 hsub
        · intro d _
          refine ⟨d.1 + z_star, mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
          · rw [add_sub_cancel_right]; exact d.2
          · apply Subtype.ext; simp only [add_sub_cancel_right]
      have hK_top : K_sub v_star = ⊤ := by
        by_contra hne_top
        have hK_le := card_submodule_le_pow_pred_of_ne_top hne_top
        rw [← hU_eq_K] at hK_le
        have hpow_split : (Fintype.card F) ^ ℓ =
            Fintype.card F * (Fintype.card F) ^ (ℓ - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ ℓ), pow_succ, Nat.mul_comm]
        have hlt_q : L * (U_fin v_star).card < Fintype.card F * (U_fin v_star).card :=
          Nat.mul_lt_mul_of_pos_right hL_lt hU_pos
        have hle_pow : Fintype.card F * (U_fin v_star).card ≤
            Fintype.card F * (Fintype.card F) ^ (ℓ - 1) := Nat.mul_le_mul_left _ hK_le
        omega
      have hmem_K : ∀ d : Fin ℓ → F, d ∈ K_sub v_star := fun d => hK_top ▸ Submodule.mem_top
      have hex_j : ∀ j : Fin ℓ, ∃ vj ∈ C, ∀ i ∈ D_star v_star, u j i = vj i := by
        intro j
        obtain ⟨vj, hvjC, hag_j⟩ := hmem_K (Pi.single j 1)
        refine ⟨vj, hvjC, fun i hi => ?_⟩
        have hsingle : (∑ r : Fin ℓ, (Pi.single (M := fun _ => F) j (1 : F) r) • u r) = u j := by
          rw [Finset.sum_eq_single j]
          · simp only [Pi.single_eq_same, one_smul]
          · intro r _ hr; simp only [Pi.single_eq_of_ne hr, zero_smul]
          · intro h; exact absurd (mem_univ j) h
        rw [← hsingle]
        exact hag_j i hi
      choose v hvC hv_ag using hex_j
      obtain ⟨w_neg, hw_negC, hag_neg⟩ := hmem_K (-z_star)
      let v₀ : ι → F := v_star + w_neg
      have hv₀C : v₀ ∈ C := C.add_mem hv_starC hw_negC
      refine ⟨D_star v_star, fun i hi => (mem_filter.1 (mem_filter.1 hi).1).2, ?_,
        v₀, hv₀C, v, hvC, fun i hi => ⟨?_, fun j => hv_ag j i hi⟩⟩
      · rw [hDstar_sum]
        exact hBW_le_Bstar.trans hv_star_ge
      · have h_ustar : u_star i = v_star i := (mem_filter.1 hi).2
        have h_neg := hag_neg i hi
        have h_u0 : u₀ i = u_star i + (∑ j : Fin ℓ, (-z_star) j • u j) i := by
          simp only [u_star, u_aff, Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul, neg_mul, Finset.sum_neg_distrib, add_neg_cancel_right]
        rw [h_u0, h_ustar, h_neg]
        rfl

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
  have hlist : ∀ w : ι → F, ∃ Lset : Finset (ι → F), Lset.card ≤ 1 ∧
      ∀ c ∈ reedSolomon α k,
        Fintype.card ι - e ≤ ∑ i ∈ Finset.univ.filter (fun i => w i = c i), (1 : ℕ) →
        c ∈ Lset := by
    intro w
    by_cases hex : ∃ c ∈ reedSolomon α k, hammingDist w c ≤ e
    · refine ⟨{hex.choose}, by simp only [Finset.card_singleton, le_rfl], fun c hc hsum => ?_⟩
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
      have hdist : hammingDist w c ≤ e := hammingDist_le_of_card_filter_eq hsum
      exact mem_singleton.2
        (eq_of_hammingDist_le_reedSolomon hα hunique hc hex.choose_spec.1 hdist hex.choose_spec.2)
    · refine ⟨∅, Nat.zero_le 1, fun c hc hsum => ?_⟩
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
      exact absurd ⟨c, hc, hammingDist_le_of_card_filter_eq hsum⟩ hex
  have hline : ∀ {B' : ℕ}, Fintype.card ι - e ≤ B' → ∀ (a b : ι → F) (S : Finset F),
      Fintype.card ι < S.card →
      (∀ t ∈ S, ∃ c ∈ reedSolomon α k,
        B' ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), (1 : ℕ)) →
      ∃ D' : Finset ι, B' ≤ ∑ i ∈ D', (1 : ℕ) ∧
        ∃ w₀ ∈ reedSolomon α k, ∃ w₁ ∈ reedSolomon α k,
          ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i := by
    intro B' hB' a b S hS hcl
    obtain ⟨t₀, ht₀⟩ := Finset.card_pos.1 (Nat.lt_of_le_of_lt (Nat.zero_le _) hS)
    obtain ⟨c₀, _, hB'_le_sum⟩ := hcl t₀ ht₀
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hB'_le_sum
    have hB'_le_n : B' ≤ Fintype.card ι := hB'_le_sum.trans (Finset.card_le_univ _)
    let e' : ℕ := Fintype.card ι - B'
    have hunique' : 2 * e' + k ≤ Fintype.card ι := by omega
    have hsub_eq : Fintype.card ι - e' = B' := by omega
    have hcl' : ∀ t ∈ S, ∃ c ∈ reedSolomon α k, hammingDist (a + t • b) c ≤ e' := by
      intro t ht
      obtain ⟨c, hc, hsum⟩ := hcl t ht
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
      exact ⟨c, hc, hammingDist_le_of_card_filter_eq (hsub_eq.symm ▸ hsum)⟩
    obtain ⟨D', hD', w₀, hw₀, w₁, hw₁, hag⟩ :=
      exists_correlatedAgreement_unique hα hunique' a b S hS hcl'
    refine ⟨D', ?_, w₀, hw₀, w₁, hw₁, hag⟩
    simpa only [Finset.sum_const, smul_eq_mul, mul_one, hsub_eq] using hD'
  have hclose' : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      Fintype.card ι - e ≤ ∑ i ∈ Finset.univ.filter
        (fun i => (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), (1 : ℕ) := by
    intro z hz
    obtain ⟨c, hc, hdist⟩ := hclose z hz
    refine ⟨c, hc, ?_⟩
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using card_filter_eq_of_hammingDist_le hdist
  obtain ⟨D₀, _, hD₀_sum, v₀, hv₀, v, hv, hag₀⟩ :=
    exists_weighted_correlatedAgreement_affine_of_line (C := reedSolomon α k) (W := fun _ => 1)
      (B_W := Fintype.card ι - e) (B_line := Fintype.card ι) (L := 1)
      hlist hline (fun _ => Fintype.one_lt_card) u₀ u T hT hclose'
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hD₀_sum
  have hex : ∃ D₀ : Finset ι, Fintype.card ι - e ≤ D₀.card ∧
      ∃ v' : Fin (ℓ + 1) → (ι → F), (∀ j, v' j ∈ reedSolomon α k) ∧
        ∀ i ∈ D₀, ∀ j, (Fin.cons (α := fun _ => ι → F) u₀ u j) i = v' j i :=
    ⟨D₀, hD₀_sum, Fin.cons v₀ v, Fin.cases hv₀ hv, fun i hi =>
      Fin.cases (hag₀ i hi).1 (hag₀ i hi).2⟩
  obtain ⟨D', hD', v', hv'RS, hagree', hmax'⟩ :=
    exists_uniqueMaximal_correlatedAgreement_of_exists hα hunique hex
  refine ⟨D', hD', v' 0, hv'RS 0, fun j => v' j.succ, fun j => hv'RS j.succ,
    fun i hi => ⟨hagree' i hi 0, fun j => hagree' i hi j.succ⟩,
    fun D'' w₀ w hD'' hw₀ hw hag'' => ?_⟩
  obtain ⟨hsub, hweq⟩ := hmax' D'' (Fin.cons w₀ w) hD'' (Fin.cases hw₀ hw)
    (fun i hi => Fin.cases (hag'' i hi).1 (hag'' i hi).2)
  exact ⟨hsub, congrFun hweq 0, funext fun j => congrFun hweq j.succ⟩

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
  · have hpos : 0 < T.card := by
      have h1 : 0 < (Fintype.card F - 1) * T.card := by
        simpa only [pow_zero, tsub_self, mul_zero] using hT
      exact Nat.pos_of_mul_pos_left h1
    obtain ⟨z₀, hz₀⟩ := Finset.card_pos.1 hpos
    obtain ⟨c, hcRS, hμ_ge⟩ := hclose z₀ hz₀
    have hμ0 : θ ≤ ∑ i ∈ Finset.univ.filter (fun i => u₀ i = c i), μ i := by
      simpa only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] using hμ_ge
    refine ⟨Finset.univ.filter fun i => u₀ i = c i, hμ0, c, hcRS, Fin.elim0,
      fun j => Fin.elim0 j, fun i hi => ⟨(mem_filter.1 hi).2, fun j => Fin.elim0 j⟩⟩
  · have hclose_unw : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
        hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e := by
      intro z hz
      obtain ⟨c, hcRS, hμ_ge⟩ := hclose z hz
      exact ⟨c, hcRS, hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge⟩
    have hq_gt1 : 1 < Fintype.card F := Fintype.one_lt_card
    have hq_le_pow : Fintype.card F ≤ (Fintype.card F) ^ ℓ :=
      Nat.le_self_pow (by omega : ℓ ≠ 0) (Fintype.card F)
    have hpow_pos : 1 ≤ (Fintype.card F) ^ ℓ := Nat.one_le_pow ℓ (Fintype.card F) Fintype.card_pos
    have hcard_lt : Fintype.card ι < T.card := by
      have hmul : Fintype.card ι * (Fintype.card F - 1) < T.card * (Fintype.card F - 1) := by
        calc Fintype.card ι * (Fintype.card F - 1)
            ≤ Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) :=
              Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hq_le_pow 1)
          _ < (Fintype.card F - 1) * T.card := hT
          _ = T.card * (Fintype.card F - 1) := Nat.mul_comm _ _
      exact Nat.lt_of_mul_lt_mul_right hmul
    have hT_exact : Fintype.card ι * (Fintype.card F) ^ ℓ < Fintype.card F * T.card := by
      have h1 : Fintype.card ι * (Fintype.card F) ^ ℓ =
          Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) + Fintype.card ι := by
        calc Fintype.card ι * (Fintype.card F) ^ ℓ
            = Fintype.card ι * ((Fintype.card F) ^ ℓ - 1 + 1) := by
              rw [Nat.sub_add_cancel hpow_pos]
          _ = Fintype.card ι * ((Fintype.card F) ^ ℓ - 1) + Fintype.card ι := by ring
      have h2 : Fintype.card F * T.card = (Fintype.card F - 1) * T.card + T.card := by
        calc Fintype.card F * T.card
            = (Fintype.card F - 1 + 1) * T.card := by rw [Nat.sub_add_cancel (by omega)]
          _ = (Fintype.card F - 1) * T.card + T.card := by ring
      omega
    obtain ⟨D₀, hD₀, v₀, hv₀, v, hvRS, hagree₀, _⟩ :=
      exists_uniqueMaximal_correlatedAgreement_affine_unique hα hunique u₀ u T hT_exact hclose_unw
    let D' : Finset ι := Finset.univ.filter fun i => u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i
    refine ⟨D', ?_, v₀, hv₀, v, hvRS, fun i hi => (mem_filter.1 hi).2⟩
    by_contra hlt_θ
    push Not at hlt_θ
    let badI : Finset ι := Finset.univ.filter fun i => ¬ (u₀ i = v₀ i ∧ ∀ j : Fin ℓ, u j i = v j i)
    have hT_sub : T ⊆ badI.biUnion fun i => Finset.univ.filter fun z : Fin ℓ → F =>
        (u₀ i - v₀ i) + ∑ j : Fin ℓ, z j * (u j i - v j i) = 0 := by
      intro z hz
      obtain ⟨c, hcRS, hμ_ge⟩ := hclose z hz
      have hc_dist : hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c ≤ e :=
        hammingDist_le_of_ratWeightedAgree_ge hμ_le hθ hμ_ge
      let vz : ι → F := v₀ + ∑ j : Fin ℓ, z j • v j
      have hvz_RS : vz ∈ reedSolomon α k :=
        Submodule.add_mem _ hv₀ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvRS j))
      have hvz_dist : hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) vz ≤ e :=
        hammingDist_affine_le_of_eq_on hD₀ hagree₀ z
      have hceq : c = vz :=
        eq_of_hammingDist_le_reedSolomon hα hunique hcRS hvz_RS hc_dist hvz_dist
      subst hceq
      let agree_z : Finset ι :=
        Finset.univ.filter fun i => (u₀ + ∑ j : Fin ℓ, z j • u j) i = vz i
      have hD'_sub : D' ⊆ agree_z := by
        intro i hi
        refine mem_filter.2 ⟨mem_univ i, ?_⟩
        obtain ⟨h0, hj⟩ := (mem_filter.1 hi).2
        simp only [vz, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, h0]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by rw [hj j]
      have hex : ∃ i ∈ agree_z, i ∉ D' := by
        by_contra hnone
        push Not at hnone
        have heq : D' = agree_z := Finset.Subset.antisymm hD'_sub hnone
        rw [heq] at hlt_θ
        exact absurd hμ_ge (not_le.2 hlt_θ)
      obtain ⟨i, hi_ag, hi_notD'⟩ := hex
      have hi_bad : i ∈ badI :=
        mem_filter.2 ⟨mem_univ i, fun h => hi_notD' (mem_filter.2 ⟨mem_univ i, h⟩)⟩
      refine mem_biUnion.2 ⟨i, hi_bad, mem_filter.2 ⟨mem_univ z, ?_⟩⟩
      have heq := (mem_filter.1 hi_ag).2
      simp only [vz, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heq
      have hsub_sum : ∑ j : Fin ℓ, z j * (u j i - v j i) =
          ∑ j : Fin ℓ, z j * u j i - ∑ j : Fin ℓ, z j * v j i := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsub_sum]
      calc u₀ i - v₀ i + (∑ j : Fin ℓ, z j * u j i - ∑ j : Fin ℓ, z j * v j i)
          = (u₀ i + ∑ j : Fin ℓ, z j * u j i) - (v₀ i + ∑ j : Fin ℓ, z j * v j i) := by ring
        _ = 0 := sub_eq_zero.2 heq
    have hT_le : T.card ≤ Fintype.card ι * (Fintype.card F) ^ (ℓ - 1) := by
      calc T.card
          ≤ (badI.biUnion fun i => Finset.univ.filter fun z : Fin ℓ → F =>
              (u₀ i - v₀ i) + ∑ j : Fin ℓ, z j * (u j i - v j i) = 0).card :=
            Finset.card_le_card hT_sub
        _ ≤ Fintype.card ι * (Fintype.card F) ^ (ℓ - 1) :=
            card_biUnion_zero_affine_le u₀ v₀ u v badI fun _ hi => (mem_filter.1 hi).2
    have hpow_eq : Fintype.card F * (Fintype.card F) ^ (ℓ - 1) = (Fintype.card F) ^ ℓ := by
      conv_rhs => rw [← Nat.sub_add_cancel hℓ, pow_succ']
    have hmul_le : Fintype.card F * T.card ≤ Fintype.card ι * (Fintype.card F) ^ ℓ := by
      calc Fintype.card F * T.card
          ≤ Fintype.card F * (Fintype.card ι * (Fintype.card F) ^ (ℓ - 1)) :=
            Nat.mul_le_mul_left _ hT_le
        _ = Fintype.card ι * (Fintype.card F * (Fintype.card F) ^ (ℓ - 1)) := by ring
        _ = Fintype.card ι * (Fintype.card F) ^ ℓ := by rw [hpow_eq]
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
  let μ : ι → ℚ := fun i => (W i : ℚ) / (M : ℚ)
  let θ : ℚ := (B : ℚ) / (M : ℚ)
  have hMq : (0 : ℚ) < (M : ℚ) := Nat.cast_pos.2 hM
  have hμ_le : ∀ i, μ i ≤ 1 := fun i => (div_le_one hMq).2 (Nat.cast_le.2 (hW i))
  have hθ : ((Fintype.card ι - (Fintype.card ι - (B + M - 1) / M) : ℕ) : ℚ) - 1 < θ :=
    card_sub_sub_ceilDiv_sub_one_lt hM
  have hclose' : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), μ i := by
    intro z hz
    obtain ⟨c, hcRS, hW_ge⟩ := hclose z hz
    refine ⟨c, hcRS, ?_⟩
    simp only [μ, θ, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hW_ge) hMq.le
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ :=
    exists_ratWeighted_correlatedAgreement_affine_unique_sharp hα hunique hμ_le hθ u₀ u T hT
      hclose'
  refine ⟨D', ?_, v₀, hv₀, v, hvRS, hagree⟩
  simp only [μ, θ, ← Finset.sum_div] at hD'
  have hq : (B : ℚ) ≤ ((∑ i ∈ D', W i : ℕ) : ℚ) := by
    have := (div_le_div_iff_of_pos_right hMq).1 hD'
    simpa only [Nat.cast_sum] using this
  exact Nat.cast_le.1 hq

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
    (P := fun w => ∃ c ∈ reedSolomon α k,
      B ≤ ∑ i ∈ Finset.univ.filter (fun i => w i = c i), W i)
    (B_line := Fintype.card ι)
    (fun a b S hS hcl => by
      obtain ⟨D', hD', w₀, hw₀, w₁, hw₁, hag⟩ :=
        exists_weighted_correlatedAgreement_unique hα hM hW hunique a b S hS hcl
      intro t
      refine ⟨w₀ + t • w₁, Submodule.add_mem _ hw₀ (Submodule.smul_mem _ t hw₁),
        hD'.trans (Finset.sum_le_sum_of_subset ?_)⟩
      intro i hi
      refine mem_filter.2 ⟨mem_univ i, ?_⟩
      obtain ⟨h0, h1⟩ := hag i hi
      simp only [Pi.add_apply, Pi.smul_apply, h0, h1])
    u₀ u

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
    (P := fun w => ∃ c ∈ reedSolomon α k,
      θ ≤ ∑ i ∈ Finset.univ.filter (fun i => w i = c i), μ i)
    (B_line := Fintype.card ι)
    (fun a b S hS hcl => by
      obtain ⟨D', hD', w₀, hw₀, w₁, hw₁, hag⟩ :=
        exists_ratWeighted_correlatedAgreement_unique hα hunique hμ_le hθ a b S hS hcl
      intro t
      refine ⟨w₀ + t • w₁, Submodule.add_mem _ hw₀ (Submodule.smul_mem _ t hw₁),
        hD'.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hμ_nonneg i))⟩
      intro i hi
      refine mem_filter.2 ⟨mem_univ i, ?_⟩
      obtain ⟨h0, h1⟩ := hag i hi
      simp only [Pi.add_apply, Pi.smul_apply, h0, h1])
    u₀ u

/-! ### Part 5: Johnson-bound curves, affine correlated agreement, and dichotomies -/

/-- Private helper: linear weight scaling of `johnsonCurveBound` over `ℝ`. -/
private theorem johnsonCurveBound_mul_cast_le
    {n m d D r M : ℕ} (hn : 1 ≤ n) (hM : 0 < M) {U : ℝ}
    (hU : (ProximityGap.johnsonCurveBound n m d D r n : ℝ) ≤ U) :
    (ProximityGap.johnsonCurveBound n m d D r (M * n) : ℝ) ≤ (M : ℝ) * U := by
  have hle_nat : n ≤ M * n := Nat.le_mul_of_pos_left n hM
  have hmul_nat :=
    ProximityGap.johnsonCurveBound_mul_le (m := m) (d := d) (D := D) (r := r) hle_nat
  have hmulR : (ProximityGap.johnsonCurveBound n m d D r (M * n) : ℝ) * (n : ℝ) ≤
      (ProximityGap.johnsonCurveBound n m d D r n : ℝ) * ((M : ℝ) * (n : ℝ)) := by
    have hcast : ((ProximityGap.johnsonCurveBound n m d D r (M * n) * n : ℕ) : ℝ) ≤
        ((ProximityGap.johnsonCurveBound n m d D r n * (M * n) : ℕ) : ℝ) := by
      exact_mod_cast hmul_nat
    push_cast at hcast
    exact hcast
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hjb_le : (ProximityGap.johnsonCurveBound n m d D r (M * n) : ℝ) ≤
      (ProximityGap.johnsonCurveBound n m d D r n : ℝ) * (M : ℝ) := by
    refine le_of_mul_le_mul_right ?_ hnR
    linarith
  have hMR : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  calc (ProximityGap.johnsonCurveBound n m d D r (M * n) : ℝ)
      ≤ (ProximityGap.johnsonCurveBound n m d D r n : ℝ) * (M : ℝ) := hjb_le
    _ = (M : ℝ) * (ProximityGap.johnsonCurveBound n m d D r n : ℝ) := mul_comm _ _
    _ ≤ (M : ℝ) * U := mul_le_mul_of_nonneg_left hU hMR

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
  have hcast : ((B * q ^ ℓ : ℕ) : ℝ) < ((q * cardT : ℕ) : ℝ) := by
    push_cast
    linarith
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
  have hagree_ge : ∀ c : ι → F,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i →
      t ≤ (Finset.univ.filter fun i => u i = c i).card := by
    intro c hcW
    have hsum_le : ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i ≤
        M * (Finset.univ.filter fun i => u i = c i).card := by
      calc ∑ i ∈ Finset.univ.filter (fun i => u i = c i), W i
          ≤ ∑ _i ∈ Finset.univ.filter (fun i => u i = c i), M :=
            Finset.sum_le_sum fun i _ => hW_le i
        _ = (Finset.univ.filter fun i => u i = c i).card * M := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = M * (Finset.univ.filter fun i => u i = c i).card := Nat.mul_comm _ _
    rw [Nat.div_le_iff_le_mul_add_pred hM]
    omega
  rcases Nat.eq_or_lt_of_le hk with rfl | hk2
  · -- `k = 1`: every codeword in `reedSolomon α 1` is constant; fibers are pairwise disjoint.
    have ht_pos : 0 < t := by
      by_contra h0
      have ht0 : t = 0 := Nat.eq_zero_of_not_pos h0
      rw [ht0, Nat.mul_zero] at hroot
      exact Nat.not_lt_zero D hroot
    let A_good : Finset F :=
      (Finset.univ.image u).filter fun a => t ≤ (Finset.univ.filter fun i => u i = a).card
    let Lset : Finset (ι → F) := A_good.image fun a _ => a
    have hD_le_maxY : D ≤ ProximityGap.maxYDeg 0 D := by
      have hmem : (0, D) ∈ Sudan.monomials 0 D :=
        Sudan.mem_monomials.2 ⟨Nat.zero_le D, le_rfl, by simp⟩
      exact Finset.le_sup (f := Prod.snd) hmem
    have hmon0 : #(Sudan.monomials 0 D) = (D + 1) * (D + 1) := by
      have heq : Sudan.monomials 0 D = range (D + 1) ×ˢ range (D + 1) := by
        ext ⟨a, b⟩
        simp only [Sudan.mem_monomials, mem_product, mem_range, Nat.lt_succ_iff, zero_mul,
          add_zero]
        tauto
      rw [heq, Finset.card_product, Finset.card_range]
    have hcard_mul : A_good.card * t ≤ Fintype.card ι := by
      have hdisj : Set.PairwiseDisjoint (A_good : Set F)
          (fun a => Finset.univ.filter fun i => u i = a) := by
        intro a₁ _ a₂ _ hne
        exact Finset.disjoint_filter.2 fun i _ h1 h2 => hne (h1.symm.trans h2)
      calc A_good.card * t
          = ∑ _a ∈ A_good, t := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ a ∈ A_good, (Finset.univ.filter fun i => u i = a).card :=
            Finset.sum_le_sum fun a ha => (mem_filter.1 ha).2
        _ = (A_good.biUnion fun a => Finset.univ.filter fun i => u i = a).card :=
            (Finset.card_biUnion hdisj).symm
        _ ≤ Fintype.card ι := Finset.card_le_univ _
    have hm_le : m ≤ m * (m + 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      nlinarith
    have hlt_sq : A_good.card * (D + 1) < (D + 1) * (D + 1) := by
      rw [Nat.sub_self, hmon0] at hinterp
      calc A_good.card * (D + 1)
          ≤ A_good.card * (m * t) := Nat.mul_le_mul_left _ hroot
        _ = (A_good.card * t) * m := by ring
        _ ≤ Fintype.card ι * m := Nat.mul_le_mul_right _ hcard_mul
        _ ≤ Fintype.card ι * (m * (m + 1) / 2) := Nat.mul_le_mul_left _ hm_le
        _ < (D + 1) * (D + 1) := hinterp
    have hAgood_le : A_good.card ≤ D := by
      have hlt : A_good.card < D + 1 := Nat.lt_of_mul_lt_mul_right hlt_sq
      omega
    refine ⟨Lset, (Finset.card_image_le).trans (hAgood_le.trans hD_le_maxY), fun c hcRS hcW => ?_⟩
    obtain ⟨P, hPdeg, rfl⟩ := mem_reedSolomon.1 hcRS
    have hconst : ∃ a : F, (fun i => P.eval (α i)) = fun _ => a := by
      by_cases hP0 : P = 0
      · exact ⟨0, by funext i; simp only [hP0, eval_zero]⟩
      · have hnd : P.natDegree = 0 := by
          have := (natDegree_lt_iff_degree_lt hP0).2 hPdeg
          omega
        refine ⟨P.coeff 0, ?_⟩
        funext i
        conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hnd]
        rw [eval_C]
    obtain ⟨a, ha_eq⟩ := hconst
    have hcard_a : t ≤ (Finset.univ.filter fun i => u i = a).card := by
      have h := hagree_ge (fun i => P.eval (α i)) hcW
      have ha_pt : ∀ i, P.eval (α i) = a := congrFun ha_eq
      simpa only [ha_pt] using h
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.1 (ht_pos.trans_le hcard_a)
    have ha_mem : a ∈ A_good := mem_filter.2
      ⟨mem_image.2 ⟨i₀, mem_univ i₀, (mem_filter.1 hi₀).2⟩, hcard_a⟩
    exact mem_image.2 ⟨a, ha_mem, ha_eq.symm⟩
  · -- `k ≥ 2`: use `guruswamiSudan` and `card_guruswamiSudan_mul_le`.
    let Lset : Finset (ι → F) := (guruswamiSudan α u m k D).image fun P i => P.eval (α i)
    have hd_pos : 0 < k - 1 := by omega
    have hdiv_le_maxY : D / (k - 1) ≤ ProximityGap.maxYDeg (k - 1) D := by
      have hmem : (0, D / (k - 1)) ∈ Sudan.monomials (k - 1) D :=
        Sudan.mem_monomials.2 ⟨Nat.zero_le D, Nat.div_le_self D (k - 1), by
          rw [zero_add]; exact Nat.mul_div_le D (k - 1)⟩
      exact Finset.le_sup (f := Prod.snd) hmem
    have hcard_le : Lset.card ≤ ProximityGap.maxYDeg (k - 1) D := by
      have hgs : #(guruswamiSudan α u m k D) ≤ D / (k - 1) :=
        (Nat.le_div_iff_mul_le hd_pos).2 card_guruswamiSudan_mul_le
      exact (Finset.card_image_le).trans (hgs.trans hdiv_le_maxY)
    refine ⟨Lset, hcard_le, fun c hcRS hcW => ?_⟩
    obtain ⟨P, hPdeg, rfl⟩ := mem_reedSolomon.1 hcRS
    have ht_le : t ≤ (Finset.univ.filter fun i => P.eval (α i) = u i).card := by
      have h := hagree_ge (fun i => P.eval (α i)) hcW
      have heq : (Finset.univ.filter fun i => u i = P.eval (α i)) =
          (Finset.univ.filter fun i => P.eval (α i) = u i) := by
        ext i
        simp only [mem_filter, mem_univ, true_and, eq_comm]
      rwa [← heq]
    have hD_lt : D < m * (Finset.univ.filter fun i => P.eval (α i) = u i).card :=
      hroot.trans_le (Nat.mul_le_mul_left m ht_le)
    have hP_mem : P ∈ guruswamiSudan α u m k D :=
      (mem_guruswamiSudan_iff hα (by omega) hinterp).2 ⟨hPdeg, hD_lt⟩
    exact mem_image.2 ⟨P, hP_mem, rfl⟩

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
  by_cases hr0 : r = 0
  · subst hr0
    by_cases h0 : ∃ c ∈ reedSolomon α k, hammingDist (u 0) c ≤ e
    · left
      intro z
      have hsum0 : (∑ j : Fin (0 + 1), z ^ (j : ℕ) • u j) = u 0 := by
        rw [Fin.sum_univ_one]
        simp only [Fin.val_zero, pow_zero, one_smul]
      rw [hsum0]
      exact h0
    · right
      have hemp : (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
          hammingDist (∑ j : Fin 1, z ^ (j : ℕ) • u j) c ≤ e) = ∅ := by
        ext z
        simp only [mem_filter, mem_univ, true_and, Fin.sum_univ_one, Fin.val_zero, pow_zero,
          one_smul, notMem_empty, iff_false]
        exact h0
      rw [hemp, Finset.card_empty, Nat.cast_zero, zero_div]
      simp only [mul_zero, zero_mul, zero_div, le_refl]
  · set S : Finset F :=
      Finset.univ.filter fun z : F =>
        ∃ c ∈ reedSolomon α k, hammingDist (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) c ≤ e
    obtain ⟨hk_sub, hinterp, hroot, hjb⟩ :=
      ProximityGap.johnson_curve_params_bound hk hkn hm (by omega : 1 ≤ r) he
    set m' : ℕ := m + 1
    set t₀ : ℕ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((Fintype.card ι : ℝ) * (k : ℝ))⌉₊
    set D : ℕ := m' * t₀ - 1
    by_cases hgt :
        ProximityGap.johnsonCurveBound (Fintype.card ι) m' (k - 1) D r (Fintype.card ι) < #S
    · left
      obtain ⟨D', hD', v, hv_rs, hagree⟩ :=
        exists_correlatedAgreement_curve_johnson hα hk (by omega : 1 ≤ m') hk_sub hinterp hroot
          u S hgt (fun _ hz => (mem_filter.1 hz).2)
      intro z
      exact ⟨∑ j : Fin (r + 1), z ^ (j : ℕ) • v j,
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hv_rs j),
        hammingDist_curve_le_of_eq_on hD' hagree z⟩
    · right
      have hcard_le : (#S : ℝ) ≤
          (ProximityGap.johnsonCurveBound (Fintype.card ι) m' (k - 1) D r (Fintype.card ι) : ℝ) :=
        by exact_mod_cast le_of_not_gt hgt
      have hFpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos (α := F)
      have hdiv := div_le_div_of_nonneg_right (hcard_le.trans hjb) hFpos.le
      rw [div_div] at hdiv
      exact hdiv

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
  set n : ℕ := Fintype.card ι
  set t : ℕ := (B_W + M - 1) / M
  have hn : 1 ≤ n := hk.trans hkn
  by_cases ht_le : t ≤ n
  · by_cases hr0 : r = 0
    · subst hr0
      by_cases h0 : ∃ c ∈ reedSolomon α k,
          B_W ≤ ∑ i ∈ Finset.univ.filter (fun i => u 0 i = c i), W i
      · left
        intro z
        have hsum0 : (∑ j : Fin (0 + 1), z ^ (j : ℕ) • u j) = u 0 := by
          rw [Fin.sum_univ_one]
          simp only [Fin.val_zero, pow_zero, one_smul]
        rw [hsum0]
        exact h0
      · right
        have hemp : (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
            B_W ≤ ∑ i ∈ Finset.univ.filter
              (fun i => (∑ j : Fin 1, z ^ (j : ℕ) • u j) i = c i), W i) = ∅ := by
          ext z
          simp only [mem_filter, mem_univ, true_and, Fin.sum_univ_one, Fin.val_zero, pow_zero,
            one_smul, notMem_empty, iff_false]
          exact h0
        rw [hemp, Finset.card_empty, Nat.cast_zero, zero_div]
        simp only [mul_zero, zero_mul, zero_div, le_refl]
    · set S : Finset F := Finset.univ.filter fun z : F =>
        ∃ c ∈ reedSolomon α k,
          B_W ≤ ∑ i ∈ Finset.univ.filter
            (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i
      set e : ℕ := n - t
      have hne : n - e = t := Nat.sub_sub_self ht_le
      obtain ⟨hk_sub, hinterp, hroot, hjb⟩ :=
        ProximityGap.johnson_curve_params_bound (e := e) hk hkn hm (by omega : 1 ≤ r) hB
      rw [hne] at hk_sub hroot
      set m' : ℕ := m + 1
      set t₀ : ℕ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * (k : ℝ))⌉₊
      set D : ℕ := m' * t₀ - 1
      have hW_sum : ∑ i : ι, W i ≤ M * n := sum_le_mul_card_of_le hW Finset.univ
      by_cases hgt :
          ProximityGap.johnsonCurveBound n m' (k - 1) D r (M * n) < #S
      · left
        obtain ⟨D', hD', v, hv_rs, hagree⟩ :=
          exists_weighted_correlatedAgreement_curve_johnson hα hk (by omega : 1 ≤ m') hM hW hW_sum
            hk_sub hinterp hroot u S hgt (fun _ hz => (mem_filter.1 hz).2)
        intro z
        exact ⟨∑ j : Fin (r + 1), z ^ (j : ℕ) • v j,
          Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hv_rs j),
          hD'.trans (weightedAgree_curve_ge_of_eq_on W hagree z)⟩
      · right
        have hcard_le : (#S : ℝ) ≤
            (ProximityGap.johnsonCurveBound n m' (k - 1) D r (M * n) : ℝ) := by
          exact_mod_cast le_of_not_gt hgt
        have hjbM := johnsonCurveBound_mul_cast_le hn hM hjb
        have hFpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
          exact_mod_cast Fintype.card_pos (α := F)
        have hdiv := div_le_div_of_nonneg_right (hcard_le.trans hjbM) hFpos.le
        have hrhs :
            (M : ℝ) * (1800 * (r : ℝ) * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) /
                ((k : ℝ) / (n : ℝ))) / (Fintype.card F : ℝ) =
              1800 * (r : ℝ) * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) /
                (((k : ℝ) / (n : ℝ)) * (Fintype.card F : ℝ)) := by
          ring
        exact hdiv.trans_eq hrhs
  · -- `n < t`, hence `M * n < B_W`: no codeword can reach weight `B_W`.
    right
    have hMn_lt : M * n < B_W := by
      by_contra hle
      have hle' : B_W ≤ M * n := Nat.le_of_not_lt hle
      have ht_le' : t ≤ n := by
        rw [Nat.div_le_iff_le_mul_add_pred hM]
        omega
      exact ht_le ht_le'
    have hemp : (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        B_W ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i) = ∅ := by
      ext z
      simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      rintro ⟨c, _, hcW⟩
      have hle : ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i ≤ M * n :=
        sum_le_mul_card_of_le hW _
      omega
    rw [hemp, Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

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
  obtain ⟨W, _, hW_le, hW_sum, hsum_iff, hθ_le_t⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  set B_W : ℕ := ⌈θ * (M : ℚ)⌉₊
  have hk_le_t : k ≤ (B_W + M - 1) / M := Nat.cast_le.1 (hk_le.trans hθ_le_t)
  have hroot_nat : D < m * ((B_W + M - 1) / M) := by
    have hlt : (D : ℚ) < (m : ℚ) * (((B_W + M - 1) / M : ℕ) : ℚ) :=
      hroot.trans_le (mul_le_mul_of_nonneg_left hθ_le_t (Nat.cast_nonneg m))
    exact_mod_cast hlt
  have hcloseW : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter
        (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i := by
    intro z hz
    obtain ⟨c, hcRS, hge⟩ := hclose z hz
    exact ⟨c, hcRS, (hsum_iff _).1 hge⟩
  obtain ⟨D', hD', v, hvRS, hagree⟩ :=
    exists_weighted_correlatedAgreement_curve_johnson hα hk hm hM hW_le hW_sum hk_le_t
      hinterp hroot_nat u T hT hcloseW
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
  let u : Fin 2 → (ι → F) := ![u₀, u₁]
  have hcurve : ∀ z : F, (∑ j : Fin 2, z ^ (j : ℕ) • u j) = u₀ + z • u₁ := by
    intro z
    simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, u,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  obtain ⟨D', hD', v, hvRS, hagree⟩ :=
    exists_ratWeighted_correlatedAgreement_curve_johnson (r := 1) hα hk hm hM hμ_le hμ_den hk_le
      hinterp hroot u T hT (fun z hz => by rw [hcurve z]; exact hclose z hz)
  refine ⟨D', hD', v 0, hvRS 0, v 1, hvRS 1, fun i hi => ⟨?_, ?_⟩⟩
  · simpa only [u, Matrix.cons_val_zero] using hagree i hi 0
  · simpa only [u, Matrix.cons_val_one, Matrix.cons_val_zero] using hagree i hi 1

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
  set n : ℕ := Fintype.card ι
  set B_W : ℕ := ⌈θ * (M : ℚ)⌉₊
  set t : ℕ := (B_W + M - 1) / M
  have hn : 1 ≤ n := hk.trans hkn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  by_cases hθ_le_n : (θ : ℝ) ≤ (n : ℝ)
  · have hB : ((n - t : ℕ) : ℝ) / (n : ℝ) ≤
        1 - Real.sqrt ((k : ℝ) / (n : ℝ)) -
          Real.sqrt ((k : ℝ) / (n : ℝ)) / (2 * (m : ℝ)) :=
      ceilDiv_radius_le hM hn hθ_le_t hθ_le_n hθ
    have hequiv : ∀ z : F,
        (∃ c ∈ reedSolomon α k, θ ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) ↔
        (∃ c ∈ reedSolomon α k, B_W ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i) := by
      intro z
      constructor <;> rintro ⟨c, hcRS, hge⟩
      · exact ⟨c, hcRS, (hsum_iff _).1 hge⟩
      · exact ⟨c, hcRS, (hsum_iff _).2 hge⟩
    rcases weighted_proximityGap_curve_johnson (B_W := B_W) hα hk hkn hm hM hW_le hB u with
        hall | hbound
    · exact Or.inl fun z => (hequiv z).2 (hall z)
    · right
      have hfilt : (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
            θ ≤ ∑ i ∈ Finset.univ.filter
              (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) =
          (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
            B_W ≤ ∑ i ∈ Finset.univ.filter
              (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), W i) := by
        ext z
        simp only [mem_filter, mem_univ, true_and]
        exact hequiv z
      simpa only [hfilt] using hbound
  · -- `n < θ`: no codeword can reach `μ`-weighted agreement `θ`.
    right
    have hn_lt_θQ : (n : ℚ) < θ := by exact_mod_cast lt_of_not_ge hθ_le_n
    have hemp : (Finset.univ.filter fun z : F => ∃ c ∈ reedSolomon α k,
        θ ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i) = ∅ := by
      ext z
      simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      rintro ⟨c, _, hcμ⟩
      have hle : ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin (r + 1), z ^ (j : ℕ) • u j) i = c i), μ i ≤ (n : ℚ) :=
        sum_le_card_of_le_one hμ_le _
      linarith
    rw [hemp, Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

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
  have hcloseW : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      Fintype.card ι - e ≤ ∑ _i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), (1 : ℕ) := by
    intro z hz
    obtain ⟨c, hcRS, hdist⟩ := hclose z hz
    refine ⟨c, hcRS, ?_⟩
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    have htot := card_filter_eq_add_hammingDist (u₀ + ∑ j : Fin ℓ, z j • u j) c
    omega
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ :=
    exists_weighted_correlatedAgreement_affine_johnson (W := fun _ => 1) (M := 1)
      (W_tot := Fintype.card ι) (B_W := Fintype.card ι - e) hα hk hm Nat.one_pos
      (fun _ => le_rfl) (by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one])
      (by rwa [hceil]) hinterp (by rwa [hceil]) u₀ u T hT hcloseW
  rw [Finset.sum_const, smul_eq_mul, mul_one] at hD'
  exact ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩

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
  obtain ⟨W, _, hW_le, hW_sum, hsum_iff, hθ_le_t⟩ := rat_weights_to_nat hM hμ_le hμ_den θ
  set B_W : ℕ := ⌈θ * (M : ℚ)⌉₊
  have hk_le_t : k ≤ (B_W + M - 1) / M := Nat.cast_le.1 (hk_le.trans hθ_le_t)
  have hroot_nat : D < m * ((B_W + M - 1) / M) := by
    have hlt : (D : ℚ) < (m : ℚ) * (((B_W + M - 1) / M : ℕ) : ℚ) :=
      hroot.trans_le (mul_le_mul_of_nonneg_left hθ_le_t (Nat.cast_nonneg m))
    exact_mod_cast hlt
  have hcloseW : ∀ z ∈ T, ∃ c ∈ reedSolomon α k,
      B_W ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin ℓ, z j • u j) i = c i), W i := by
    intro z hz
    obtain ⟨c, hcRS, hge⟩ := hclose z hz
    exact ⟨c, hcRS, (hsum_iff _).1 hge⟩
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ :=
    exists_weighted_correlatedAgreement_affine_johnson hα hk hm hM hW_le hW_sum hk_le_t
      hinterp hroot_nat u₀ u T hT hcloseW
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
  set m' : ℕ := m + 1
  set t₀ : ℕ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((Fintype.card ι : ℝ) * (k : ℝ))⌉₊
  set D : ℕ := m' * t₀ - 1
  have hFpos : (0 : ℝ) < (Fintype.card F : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hdiv :
      (ProximityGap.johnsonCurveBound (Fintype.card ι) m' (k - 1) D 1 (Fintype.card ι) : ℝ) /
        (Fintype.card F : ℝ) ≤
      1800 * ((m + 1 : ℝ) ^ 6) * ((Fintype.card ι : ℝ) ^ 2) /
        (((k : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ)) := by
    have h1 := div_le_div_of_nonneg_right hjb hFpos.le
    rwa [div_div] at h1
  have hT_nat := affine_mul_lt_of_density_lt Fintype.card_pos (hdiv.trans_lt hT)
  exact exists_correlatedAgreement_affine_johnson hα hk (by omega : 1 ≤ m') hk_sub hinterp hroot
    u₀ u T hT_nat hclose

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
  set n : ℕ := Fintype.card ι
  set t : ℕ := (B_W + M - 1) / M
  have hn : 1 ≤ n := hk.trans hkn
  have hFpos : (0 : ℝ) < (Fintype.card F : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hρ_pos : 0 < (k : ℝ) / (n : ℝ) := by positivity
  obtain ⟨z₀, hz₀⟩ := nonempty_of_pos_lt_density (by positivity) hT
  obtain ⟨c₀, _, hc₀_ge⟩ := hclose z₀ hz₀
  have hBW_le : B_W ≤ M * n := hc₀_ge.trans (sum_le_mul_card_of_le hW _)
  have ht_le : t ≤ n := by
    rw [Nat.div_le_iff_le_mul_add_pred hM]
    omega
  set e : ℕ := n - t
  have hne : n - e = t := Nat.sub_sub_self ht_le
  obtain ⟨hk_sub, hinterp, hroot, hjb⟩ :=
    ProximityGap.johnson_line_params_bound (e := e) hk hkn hm hB
  rw [hne] at hk_sub hroot
  set m' : ℕ := m + 1
  set t₀ : ℕ := ⌈(1 + 1 / (2 * (m : ℝ))) * Real.sqrt ((n : ℝ) * (k : ℝ))⌉₊
  set D : ℕ := m' * t₀ - 1
  have hjbM := johnsonCurveBound_mul_cast_le hn hM hjb
  have hdiv := div_le_div_of_nonneg_right hjbM hFpos.le
  have hrhs :
      (M : ℝ) * (1800 * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) / ((k : ℝ) / (n : ℝ))) /
          (Fintype.card F : ℝ) =
        1800 * (M : ℝ) * ((m + 1 : ℝ) ^ 6) * ((n : ℝ) ^ 2) /
          (((k : ℝ) / (n : ℝ)) * (Fintype.card F : ℝ)) := by
    rw [mul_div_assoc', div_div]
    ring
  have hT_nat := affine_mul_lt_of_density_lt Fintype.card_pos ((hdiv.trans_eq hrhs).trans_lt hT)
  exact exists_weighted_correlatedAgreement_affine_johnson hα hk (by omega : 1 ≤ m') hM hW
    (sum_le_mul_card_of_le hW Finset.univ) hk_sub hinterp hroot u₀ u T hT_nat hclose

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
  have hn : 1 ≤ Fintype.card ι := hk.trans hkn
  have hρ_pos : 0 < (k : ℝ) / (Fintype.card ι : ℝ) := by positivity
  have hFpos : (0 : ℝ) < (Fintype.card F : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  exact ratWeighted_to_nat_affine_ca hk hkn hM hμ_le hμ_den hθ
    (nonempty_of_pos_lt_density (by positivity) hT) hclose fun hW_le hB hclW =>
    exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity hα hk hkn hm hM hW_le hB
      u₀ u T hT hclW

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
  have hn : 1 ≤ Fintype.card ι := hk.trans hkn
  have hρ_pos : 0 < (k : ℝ) / (Fintype.card ι : ℝ) := by positivity
  have hFpos : (0 : ℝ) < (Fintype.card F : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  exact ratWeighted_to_nat_affine_ca hk hkn hM hμ_le hμ_den hθ
    (nonempty_of_pos_lt_density (by positivity) hT) hclose fun hW_le hB hclW =>
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
