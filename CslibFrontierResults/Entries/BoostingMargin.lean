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
      locator := "Section 7.2" },
    { paper := ShalevShwartzBenDavid2014, theorem := "Lemma 26.7",
      locator := "Chapter 26" }
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
      locator := "Section 5.4" },
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

register_result "adaboost-margin-generalization" where
  title := "Margin-based generalization and empirical margin decay for boosting and AdaBoost"
  topic := "statistical learning"
  sources := [
    { paper := MohriRostamizadehTalwalkar2018, theorem := "Corollary 7.5",
      locator := "Chapter 7" },
    { paper := SchapireFreundBartlettLee1998, theorem := "Theorem 5",
      locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.Boosting.convexHull_margin_bound,
    Cslib.MachineLearning.Boosting.convexHull_uniform_margin_bound,
    Cslib.MachineLearning.Boosting.convexHull_uniform_empirical_margin_bound,
    Cslib.MachineLearning.Boosting.convexHull_signClass_vc_uniform_margin_bound,
    Cslib.MachineLearning.Boosting.adaBoost_uniform_margin_bound_vc,
    Cslib.MachineLearning.Boosting.marginCount_normalizedScore_le_prod,
    Cslib.MachineLearning.Boosting.marginCount_normalizedScore_le_pow,
    Cslib.MachineLearning.Boosting.marginCount_normalizedScore_le_exp,
    Cslib.MachineLearning.Boosting.adaBoost_generalization_bound_of_edge
  ]
  scope := "Margin generalization bounds over convexHull ℝ H and AdaBoost's normalized voting \
    classifier normalizedScore S A T on finite domains α with deterministic weak learners. The \
    generalization bounds are independent of the number of boosting rounds T. The empirical \
    margin decay holds for all ρ < 1 (product form), ρ ∈ [0, 2 γ] (edge form), and ρ ∈ [0, γ] \
    (exponential form exp(-2 γ (γ - ρ) T), recovering exp(-2 γ² T) at ρ = 0), assuming round \
    errors εₜ ≤ 1/2 - γ with 0 < γ < 1/2. Early stopping on εₜ = 0 yields margin +1 everywhere \
    on S; vote ties predict false. Does not verify exact book page numbers from PDF."
