/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.Taxation
import CslibFrontier.GameTheory.Mechanism.Roberts

register_result "nrtv-taxation-principle" where
  title := "Taxation principle: direct characterization of incentive-compatible mechanisms"
  topic := "mechanism design"
  sources := [
    { paper := Nisan2007,
      theorem := "Proposition 9.27",
      locator := "§9.5.1, p. 226" }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.isDSICOn_iff_taxation,
    Cslib.GameTheory.Mechanism.isDSIC_iff_taxation
  ]
  scope := "Direct-revelation mechanisms `Cslib.GameTheory.Mechanism ι Ω` on arbitrary domains \
    `V : ι → Set (Ω → ℝ)` (and unrestricted `Set.univ`), with arbitrary agent type `ι` and \
    outcome type `Ω` (no finiteness assumed). Characterizes `M.IsDSICOn V` by existence, for each \
    agent `i` and others' valid reports `b₋ᵢ`, of outcome prices `p : Ω → ℝ` matching `i`'s \
    payment on every `v ∈ V i` and maximized at `M.outcome (update b i v)` over the induced range \
    `(fun v' => M.outcome (update b i v')) '' V i`. No running-time claim is made. Note: the \
    necessity half of Theorem 9.29 (WMON, §9.5.2, p. 227) is in the same module as a separate \
    unregistered step (`IsDSICOn.isWeaklyMonotoneOn`); the Saks–Yu sufficiency half on convex \
    domains remains open. `isImplementableOn_iff_isCyclicallyMonotoneOn` gives an exact \
    characterization via cyclic monotonicity for arbitrary domains and outcome types."

register_result "nrtv-weighted-groves-dsic" where
  title := "Weighted Groves (weighted VCG) mechanisms are dominant-strategy incentive compatible"
  topic := "mechanism design"
  sources := [
    { paper := Nisan2007,
      theorem := "Proposition 9.31",
      locator := "§9.5.3, p. 228" }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.weightedGroves_isDSIC,
    Cslib.GameTheory.Mechanism.IsAffineMaximizerFor.isImplementable,
    Cslib.GameTheory.Mechanism.weightedGroves_isDSIC_of_nonneg
  ]
  scope := "Direct-revelation mechanisms with finitely many agents `[Fintype ι] [DecidableEq ι]` \
    and arbitrary outcome type `Ω`. For strictly positive weights `∀ i, 0 < w i`, \
    `weightedGroves_isDSIC` reproduces Proposition 9.31 with arbitrary tie-breaking over any \
    subrange `A ⊆ Ω`. `weightedGroves_isDSIC_of_nonneg` extends this to nonnegative weights \
    `0 ≤ w i` when every weight-zero agent `w i = 0` is a dummy (`f (update b i v) = f b`), \
    charging payment `h i b` independent of `b i`; adverse tie-breaking at weight zero can break \
    DSIC (checked in `CslibFrontierTests.GameTheory.Roberts.badTieRule_affine_not_implementable`). \
    No running-time claim is made."

register_result "lavi-neutral-roberts-theorem" where
  title := "Neutral Roberts theorem on unrestricted valuation domains"
  topic := "mechanism design"
  sources := [
    { paper := Lavi2007,
      theorem := "Theorem 12.26",
      locator := "§12.4, p. 318" }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.exists_weightedWelfare_of_isNeutral_of_isWeaklyMonotone,
    Cslib.GameTheory.Mechanism.exists_weightedWelfare_of_isNeutral_of_isImplementable
  ]
  scope := "Finite agent type `[Fintype ι] [DecidableEq ι]` and finite outcome type `[Fintype Ω]` \
    with `3 ≤ Fintype.card Ω` on unrestricted valuations `ℝ^Ω`. Proves every neutral \
    (`IsNeutral`, Definition 12.25) weakly monotone (in particular DSIC-implementable) social \
    choice function maximizes a pure weighted sum `∑ i, w i * b i ω` (all additive outcome \
    constants `c ω = 0`) with nonnegative weights summing to `1` (`∃ i, 0 < w i`). Note that \
    zero weights `w i = 0` must be allowed to cover dictatorships. No running-time claim is made."

register_result "roberts-theorem" where
  title := "Roberts' theorem: surjective DSIC mechanisms on unrestricted domains are affine \
    maximizers"
  topic := "mechanism design"
  sources := [
    { paper := Nisan2007,
      theorem := "Theorem 9.32",
      locator := "§9.5.3, p. 228" },
    { paper := Lavi2007,
      theorem := "Theorem 12.24",
      locator := "§12.4, p. 318 (completed via Exercise 12.8, p. 329)" }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.exists_isAffineMaximizerFor_of_isWeaklyMonotone,
    Cslib.GameTheory.Mechanism.exists_isAffineMaximizerFor_of_isImplementable,
    Cslib.GameTheory.Mechanism.IsImplementable.isAffineMaximizer,
    Cslib.GameTheory.Mechanism.IsDSIC.isAffineMaximizer,
    Cslib.GameTheory.Mechanism.exists_isAffineMaximizerFor_range_of_isWeaklyMonotone
  ]
  scope := "Finite agent type `[Fintype ι] [DecidableEq ι]` and finite outcome type `[Fintype Ω]` \
    with `3 ≤ Fintype.card Ω` (and `exists_isAffineMaximizerFor_range_of_isWeaklyMonotone` for \
    arbitrary `Ω` whenever `Set.range f` is finite with `3 ≤ (Set.range f).ncard`), over the \
    unrestricted valuation domain `ℝ^Ω`. Captures the necessity direction of Theorem 12.24 / full \
    Theorem 9.32: every surjective weakly monotone (in particular DSIC-implementable) rule is an \
    affine maximizer with nonnegative weights summing to `1` (`∃ i, 0 < w i`). Repairs two \
    textbook slips: (1) [Nisan2007] Definition 9.30 writes `wᵢ ∈ ℝ⁺`, which literally excludes \
    dictatorships (checked via `dictatorRule_no_positive_weights`); (2) [Lavi2007] Definition \
    12.23 omits `wᵢ ≥ 0` and `∃ i, wᵢ > 0`, and the converse (`affine maximizer → DSIC`) of \
    Theorem 12.24 holds for arbitrary tie-breaking only with strictly positive weights (or \
    consistent tie-breaking for weight-zero agents; checked via \
    `badTieRule_affine_not_implementable` \
    and `argmin2_not_wmon_not_implementable`). Follows the `P(x, y)` / `γ(x, y)` shift proof of \
    [Lavi2007] Claims 12.31–12.34 and Exercise 12.8. No running-time claim is made."
