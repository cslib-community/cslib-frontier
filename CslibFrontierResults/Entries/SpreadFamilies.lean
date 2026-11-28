/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Probability.Spread.Exceptional

/-!
# Talagrand's spread laws, weak smallness and thinning conjectures
-/

register_result "talagrand-small-family-weakly-small" where
  title := "A small family is weakly small at the same parameter"
  topic := "probability"
  sources := [
    { paper := Talagrand2010Small, theorem := "Proposition 6.2",
      locator := "Author manuscript, p. 6, following (6.3)" }
  ]
  theorems := [Cslib.Probability.Spread.IsSmall.isWeaklySmall]
  scope := "For a finite ground set and p > 0, an integral cover of cost at most one half \
    yields a probability witness whose normalized cover score is at least two on the family."

register_result "talagrand-weak-smallness-spread-witness" where
  title := "Failure of weak smallness yields a spread probability measure"
  topic := "probability"
  sources := [
    { paper := Talagrand2010Small, theorem := "Proposition 6.7(a)",
      locator := "Author manuscript, p. 7, following Definition 6.6" }
  ]
  theorems := [Cslib.Probability.Spread.exists_spread_of_not_isWeaklySmall]
  scope := "For a finite ground set and p > 0, a family that fails weak p-smallness carries a \
    2p-spread probability law supported on that family."

register_result "talagrand-spread-obstruction-to-weak-smallness" where
  title := "A spread probability measure obstructs weak smallness"
  topic := "probability"
  sources := [
    { paper := Talagrand2010Small, theorem := "Proposition 6.7(b)",
      locator := "Author manuscript, p. 7, following Definition 6.6" }
  ]
  theorems := [Cslib.Probability.Spread.not_isWeaklySmall_of_spread]
  scope := "A p-spread law supported on a family in a finite ground set rules out weak \
    p-smallness for p > 0. The weak cover uses a normalized score of at least two."

register_result "talagrand-thinning-conjecture-equivalence" where
  title := "Equivalence of Talagrand’s thinning conjectures 7.8 and 7.11"
  topic := "probability"
  sources := [
    { paper := Talagrand2010Small, theorem := "Equivalence of Conjectures 7.8 and 7.11",
      locator := "Author manuscript, pp. 10–11, after (7.11)" }
  ]
  theorems := [Cslib.Probability.Spread.conjecture78_iff_conjecture711]
  scope := "For up-classes in every finite dimension and 0 < p < 1, domination after thinning \
    and the existence of an event-dependent probability witness majorizing the thinning \
    profile give equivalent universal-constant conjectures."

register_result "talagrand-thinning-exceptional-family" where
  title := "Talagrand’s Conjecture 7.8 implies Conjecture 7.3 at half the thinning parameter"
  topic := "probability"
  sources := [
    { paper := Talagrand2010Small, theorem := "Implication from Conjecture 7.8 to Conjecture 7.3",
      locator := "Author manuscript, p. 10, proof following (7.9)" }
  ]
  theorems := [Cslib.Probability.Spread.conjecture73At_of_conjecture78At]
  scope := "Domination at α implies Conjecture 7.3 at α/2 for 0 < α < 1. For each up-class \
    and 0 < p < 1, the family on which thinning at α/2 exceeds the p-product probability \
    is weakly (αp/2)-small."
