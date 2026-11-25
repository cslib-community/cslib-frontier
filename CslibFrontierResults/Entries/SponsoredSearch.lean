/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.SponsoredSearch.EnvyFree
import CslibFrontier.GameTheory.Mechanism.SponsoredSearch.GSP

register_result "lahaie-pennock-saberi-vohra-locally-envy-free-iff-optimal" where
  title := "Sponsored search assignments are optimal iff locally envy-free"
  topic := "algorithmic game theory"
  sources := [
    { paper := LahaiePennockSaberiVohra2007,
      theorem := "Theorem 28.1",
      locator := "§28.3.2, p. 706" }
  ]
  theorems := [
    Cslib.GameTheory.SponsoredSearch.isOptimal_iff_exists_isLocallyEnvyFree
  ]
  scope := "Static unit-weight position auction with bidder-independent click-through rates \
    μ : Fin k → ℝ (strictly decreasing and positive: StrictAnti μ and ∀ i, 0 < μ i), finite \
    bidder type ι, full assignments σ : Fin k ↪ ι (k slots filled by distinct bidders; requires \
    k ≤ Fintype.card ι for existence), and arbitrary real values v : ι → ℝ. Uses the standard \
    dummy-slot boundary convention in IsLocallyEnvyFree (unassigned bidders sit in a fictitious \
    slot k with CTR 0 and price 0), adding the boundary conditions lastSlot_nonneg and \
    unassigned_noEnvy absent from the literal matched-pair print of (28.9)–(28.10) on p. 705. \
    For nonnegative values, minEnvyFreePrice provides the pointwise least nonnegative locally \
    envy-free slot price vector (identified with Clarke-pivot VCG payments in \
    CslibFrontier.GameTheory.Mechanism.SponsoredSearch.VCG). LP integrality of (28.1)–(28.4) \
    and separable/weighted CTRs αᵢⱼ = μᵢ βⱼ (Exercises 28.2–28.4) are left open under #7789; \
    no running-time claim is made."

register_result "lahaie-pennock-saberi-vohra-gsp-equilibrium" where
  title := "Existence of a locally envy-free full-information equilibrium of the GSP auction"
  topic := "algorithmic game theory"
  sources := [
    { paper := LahaiePennockSaberiVohra2007,
      theorem := "Theorem 28.2",
      locator := "§28.3.2, pp. 706–707" }
  ]
  theorems := [
    Cslib.GameTheory.SponsoredSearch.exists_isGSPEquilibrium_locallyEnvyFree
  ]
  scope := "Static unit-weight generalized second price (GSP) auction with bidder-independent \
    CTRs μ : Fin k → ℝ (strictly decreasing and positive), nonnegative bidder values v : ι → ℝ, \
    and at least k bidders (k ≤ Fintype.card ι), filling all k slots via full embeddings \
    σ : Fin k ↪ ι. Ties are modeled relationally by IsAssortative (no fixed tie-breaking ranking \
    function); IsGSPEquilibrium is a tie-robust Nash equilibrium requiring stability against \
    every nonnegative deviation z ≥ 0 under every consistent GSP outcome σ' of \
    Function.update b j z. \
    The constructed equilibrium (minEnvyFreeBid μ v σ, σ) yields an optimal assignment that is \
    locally envy-free under the auction's actual slot payments gspSlotPrice, which equal \
    minEnvyFreePrice (the dummy-slot convention as above). Replaces the reversed inequality \
    p*_{j-1}/μ_{j-1} ≥ p*_{j-1}/μ_j printed on p. 706 and supplies the unilateral deviation check \
    omitted on p. 707. Separable/weighted CTRs, GFP (Exercise 28.5), Bayesian remarks, and §28.4 \
    online allocation are left open under #7789; no running-time claim is made."
