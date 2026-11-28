/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Strategic.PotentialCharacterization

/-!
# Collected results: potential game characterizations
-/

register_result "monderer-shapley-tie-free-fip-ordinal-potential" where
  title := "Every finite game with the finite improvement property and no unilateral cost ties \
    admits an ordinal potential"
  topic := "game theory"
  sources := [
    { paper := MondererShapley1996,
      theorem := "Corollary 2.6",
      locator := "Section 2, p. 130" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.exists_isOrdinalPotential_of_hasFIP
  ]
  scope := "For any strategic game G : CostGame ι S with finitely many strategy profiles \
    (Finite (∀ i, S i)) satisfying G.HasFIP and strict unilateral sensitivity \
    (∀ i s a b, a ≠ b → G.cost i (update s i a) ≠ G.cost i (update s i b)), G admits an ordinal \
    potential Φ (CostGame.IsOrdinalPotential)."

register_result "monderer-shapley-exact-potential-cycle-characterization" where
  title := "Exact potential games are characterized by vanishing path integrals on closed, \
    simple closed, length-4 simple closed unilateral paths, and two-player 2x2 rectangles"
  topic := "game theory"
  sources := [
    { paper := MondererShapley1996,
      theorem := "Theorem 2.8 and Corollary 2.9",
      locator := "Section 2, pp. 130–131, and Appendix A, pp. 138–139" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.exists_isExactPotential_iff_closedPath,
    Cslib.GameTheory.CostGame.exists_isExactPotential_iff_simpleClosedPath,
    Cslib.GameTheory.CostGame.exists_isExactPotential_iff_simpleClosedPath_four,
    Cslib.GameTheory.CostGame.exists_isExactPotential_iff_fourCycleZero
  ]
  scope := "For any strategic game G : CostGame ι S in cost-minimization form over finitely many \
    players (Finite ι) and arbitrary strategy types S : ι → Type*, admitting an exact potential \
    (∃ Φ, G.IsExactPotential Φ) is equivalent to: (2) G.pathIntegral γ = 0 for every finite \
    closed unilateral deviation path γ; (3) G.pathIntegral γ = 0 for every finite simple closed \
    unilateral deviation path γ; (4) G.pathIntegral γ = 0 for every finite simple closed \
    unilateral deviation path γ of length 4; and (Corollary 2.9) G.FourCycleZero on all pairs \
    of distinct players i ≠ j and strategy rectangles."

register_result "monderer-shapley-mixed-extension-potential" where
  title := "A finite game is a weighted or exact potential game if and only if its mixed \
    extension is"
  topic := "game theory"
  sources := [
    { paper := MondererShapley1996,
      theorem := "Lemma 2.10",
      locator := "Section 2, pp. 131–132, equation (2.4)" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.exists_isWeightedPotential_mixedExtension_iff,
    Cslib.GameTheory.CostGame.exists_isExactPotential_mixedExtension_iff
  ]
  scope := "For any finite strategic game G : CostGame ι S (Fintype ι, ∀ i, Fintype (S i)) and \
    arbitrary weight vector w : ι → ℝ, G admits a w-potential Φ (CostGame.IsWeightedPotential, \
    which omits positivity 0 < w i relative to [MondererShapley1996] equation (2.2) so Lemma \
    2.10 holds for arbitrary w : ι → ℝ) if and only if its mixed extension G.mixedExtension over \
    product simplices { q : S i → ℝ // IsMixedStrategy q } admits a w-potential, witnessed in \
    the forward direction by the multilinear extension mixedPotential Φ p = \
    ∑ s, productWeight p s * Φ s."
