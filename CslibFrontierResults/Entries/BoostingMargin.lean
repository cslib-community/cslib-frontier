/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.MachineLearning.Boosting.Margin
import CslibFrontier.MachineLearning.Rademacher.ConvexHull
import CslibFrontier.MachineLearning.Rademacher.UniformMargin

/-!
# Collected results: convex-hull Rademacher complexity, uniform margin bounds,
and AdaBoost margin generalization
-/

register_result "rademacher-convex-hull-invariance" where
  title := "Rademacher complexity is invariant under taking convex hulls"
  topic := "statistical learning"
  sources := [
    { paper := MohriRostamizadehTalwalkar2018, theorem := "Lemma 7.4",
      locator := unverified },
    { paper := ShalevShwartzBenDavid2014, theorem := "Lemma 26.7",
      locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.rademacherAverage_convexHull,
    Cslib.MachineLearning.empiricalRademacherComplexity_convexHull,
    Cslib.MachineLearning.rademacherComplexity_convexHull
  ]
  scope := "One-sided Rademacher complexity of uniformly bounded vector families and function \
    classes. Every pointwise |f x| ≤ B bound transfers from F to convexHull ℝ F, and exact \
    equality R̂_S(conv F) = R̂_S(F) holds on any sample (including empty F). The population form \
    R_m(conv F) = R_m(F) assumes a finite domain Z equipped with a discrete PMF."

register_result "uniform-rademacher-margin-bound" where
  title := "Uniform-in-margin Rademacher generalization bounds"
  topic := "statistical learning"
  sources := [
    { paper := MohriRostamizadehTalwalkar2018, theorem := "Theorem 5.9",
      locator := unverified },
    { paper := KoltchinskiiPanchenko2002, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.uniform_rademacherComplexity_margin_bound,
    Cslib.MachineLearning.uniform_empiricalRademacherComplexity_margin_bound
  ]
  scope := "Uniformly bounded real-valued hypothesis classes on a finite domain α with discrete \
    labeled distribution D : PMF (α × Bool) and scale r > 0. Holds simultaneously for all h ∈ H \
    and all margin thresholds ρ ∈ (0, r] via a dyadic union bound with ρₙ = r / 2^(n+1) and \
    telescoping failure budgets δₙ = δ / ((n+1)(n+2)). The data-dependent variant carries \
    log (4 / δ) from substituting δₙ into the fixed-ρ bound's log (2 / δₙ)."

register_result "convex-hull-margin-bound" where
  title := "Fixed-margin Rademacher generalization bound for convex combinations"
  topic := "statistical learning"
  sources := [
    { paper := MohriRostamizadehTalwalkar2018, theorem := "Corollary 7.5",
      locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.Boosting.convexHull_margin_bound
  ]
  scope := "Fixed-ρ margin generalization bound for convexHull ℝ H over a uniformly bounded base \
    class H on a finite domain α with discrete labeled distribution D : PMF (α × Bool), \
    independent of the number of combined hypotheses. Primary PDF locator not yet verified \
    outside the authoring fleet."

register_result "adaboost-uniform-margin-bound" where
  title := "Uniform-in-margin generalization bounds for convex combinations and AdaBoost"
  topic := "statistical learning"
  sources := [
    { paper := MohriRostamizadehTalwalkar2018, theorem := "Corollary 7.6",
      locator := unverified },
    { paper := SchapireFreundBartlettLee1998, theorem := "Theorem 2",
      locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.Boosting.convexHull_uniform_margin_bound,
    Cslib.MachineLearning.Boosting.convexHull_uniform_empirical_margin_bound,
    Cslib.MachineLearning.Boosting.convexHull_signClass_vc_uniform_margin_bound,
    Cslib.MachineLearning.Boosting.adaBoost_uniform_margin_bound_vc,
    Cslib.MachineLearning.Boosting.adaBoost_generalization_bound_of_edge
  ]
  scope := "Uniform-in-ρ (simultaneous over ρ ∈ (0, r] / (0, 1]) margin generalization bounds over \
    convexHull ℝ H and AdaBoost's normalized voting classifier normalizedScore S A T on finite \
    domains α with deterministic weak learners, independent of the number of boosting rounds T. \
    The end-to-end bound adaBoost_generalization_bound_of_edge combines Theorem 2 / Corollary 7.6 \
    with the empirical margin decay bound (Schapire–Freund–Bartlett–Lee 1998, Theorem 5) for \
    margins ρ ∈ (0, γ] assuming round errors εₜ ≤ 1/2 - γ with 0 < γ < 1/2. Early stopping on \
    εₜ = 0 yields margin +1 everywhere on S; vote ties predict false. Primary PDF locators not \
    yet verified outside the authoring fleet."

register_result "adaboost-empirical-margin-decay" where
  title := "Exponential decay of AdaBoost's empirical margin distribution"
  topic := "statistical learning"
  sources := [
    { paper := SchapireFreundBartlettLee1998, theorem := "Theorem 5",
      locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.Boosting.marginCount_normalizedScore_le_prod,
    Cslib.MachineLearning.Boosting.marginCount_normalizedScore_le_pow,
    Cslib.MachineLearning.Boosting.marginCount_normalizedScore_le_exp
  ]
  scope := "Empirical margin distribution bounds for AdaBoost's normalizedScore S A T on finite \
    labelled samples S : Fin m → α × Bool with deterministic weak learners: product form for all \
    ρ < 1 assuming εₜ < 1/2, edge form for ρ ∈ [0, 2 γ], and exponential form \
    exp(-2 γ (γ - ρ) T) for ρ ∈ [0, γ] (recovering exp(-2 γ² T) at ρ = 0), assuming round errors \
    εₜ ≤ 1/2 - γ with 0 < γ < 1/2. Early stopping on εₜ = 0 yields margin +1 everywhere on S. \
    Primary PDF locator not yet verified outside the authoring fleet."
