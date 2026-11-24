/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.SocialChoice.SinglePeaked.Ching

/-!
# Collected results: single-peaked social choice and phantom medians
-/

open Cslib.GameTheory.SocialChoice.SinglePeaked in
register_result "single-peaked-onto-unanimous-pareto" where
  title := "On single-peaked preferences, strategy-proofness equates onto, unanimity, and Pareto"
  topic := "game theory"
  sources := [
    { paper := SchummerVohra2007, theorem := "Lemma 10.1",
      locator := "Chapter 10, §10.2, pp. 245–246" }
  ]
  theorems := [
    Rule.IsStrategyProof.surjective_iff_isUnanimous,
    Rule.IsStrategyProof.surjective_iff_isParetoOptimal,
    Rule.IsStrategyProof.isUnanimous_iff_isParetoOptimal
  ]
  scope := "Finite electorate ι (nonempty for the Pareto-optimality equivalences) with ordinal \
    single-peaked weak orders over any closed real interval Set.Icc a b (generalizing [0, 1]). \
    Weak and strong Pareto-optimality are also proved equivalent on this domain \
    (Rule.isParetoOptimal_iff_isStrongParetoOptimal). Source verified against the \
    university-hosted PDF of NRTV Chapter 10."

open Cslib.GameTheory.SocialChoice.SinglePeaked in
register_result "single-peaked-option-set-and-peaks-only" where
  title := "Option sets of strategy-proof onto rules are closed intervals, and Ching's peaks-only"
  topic := "game theory"
  sources := [
    { paper := SchummerVohra2007, theorem := "Exercise 10.3",
      locator := "Chapter 10, §10.2.1 p. 247, footnote 6 p. 249, Exercise 10.3 pp. 264–265" },
    { paper := Ching1997, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Rule.IsStrategyProof.isClosed_optionSet,
    Rule.IsStrategyProof.optionSet_eq_Icc,
    Rule.IsStrategyProof.isPeaksOnly_of_surjective
  ]
  scope := "Finite electorate ι on Set.Icc a b (a ≤ b). Closedness of single-agent option sets \
    holds from strategy-proofness alone; the closed-interval characterization \
    optionSet f P i = Set.Icc l u is proved directly without appealing to Theorem 10.4, and yields \
    Ching's peaks-only theorem as an immediate corollary. Ching (1997) is cited bibliographically \
    via Schummer–Vohra (2007)."

open Cslib.GameTheory.SocialChoice.SinglePeaked in
register_result "moulin-ching-gmvs-characterization" where
  title := "Moulin–Ching GMVS characterization on ordinal single-peaked preferences"
  topic := "game theory"
  sources := [
    { paper := SchummerVohra2007, theorem := "Theorem 10.4",
      locator := "Chapter 10, §10.2.1, Definition 10.3 pp. 250–251 and Theorem 10.4 p. 251" },
    { paper := Moulin1980, theorem := unverified, locator := unverified },
    { paper := Ching1997, theorem := unverified, locator := unverified }
  ]
  theorems := [
    eval_eq_maxMinEval,
    isStrategyProof_and_surjective_iff_exists_moulinScheme,
    isGroupStrategyProof_of_isStrategyProof_of_surjective
  ]
  scope := "Finite nonempty electorate ι on Set.Icc a b (a ≤ b) with full ordinal single-peaked \
    weak orders. Reuses Cslib.GameTheory.FacilityLocation.MoulinScheme and proves pointwise \
    duality with Definition 10.3's max_S min{β_S, p_i : i ∈ S} formula (β_S = α_{Sᶜ}). Strong \
    group strategy-proofness (isGroupStrategyProof_of_isStrategyProof_of_surjective) is proved \
    here and is not part of Schummer–Vohra (2007) Theorem 10.4. Moulin (1980) and Ching (1997) \
    are cited bibliographically via Schummer–Vohra (2007)."

open Cslib.GameTheory.SocialChoice.SinglePeaked in
register_result "moulin-ching-phantom-median-ordinal" where
  title := "Moulin–Ching anonymous (n - 1)-phantom-voter median theorem on ordinal preferences"
  topic := "game theory"
  sources := [
    { paper := SchummerVohra2007, theorem := "Theorem 10.2",
      locator := "Chapter 10, §10.2.1, Theorem 10.2 and Eq. (10.1), pp. 247–250" },
    { paper := Moulin1980, theorem := unverified, locator := unverified },
    { paper := Ching1997, theorem := unverified, locator := unverified }
  ]
  theorems := [
    isStrategyProof_surjective_anonymous_iff_phantomMedian
  ]
  scope := "Finite nonempty electorate ι on Set.Icc a b (a ≤ b) with full ordinal single-peaked \
    weak orders. Matches Schummer–Vohra (2007) Theorem 10.2, Eq. (10.1) verbatim, characterizing \
    strategy-proof, surjective, anonymous rules as medians of the n reported peaks and n - 1 \
    fixed phantom points in Set.Icc a b."

open Cslib.GameTheory.SocialChoice.SinglePeaked in
register_result "single-peaked-public-good-ir-uniqueness" where
  title := "Minimum-peak uniqueness under individual rationality on single-peaked preferences"
  topic := "game theory"
  sources := [
    { paper := SchummerVohra2007, theorem := unverified,
      locator := "Chapter 10, §10.2.2, p. 252 (unnumbered result)" }
  ]
  theorems := [
    isStrategyProof_surjective_isIR_left_iff,
    isStrategyProof_surjective_isIR_right_iff
  ]
  scope := "Finite nonempty electorate ι on Set.Icc a b (a ≤ b). Establishes that the minimum-peak \
    rule is the unique strategy-proof, surjective rule individually rational with respect to the \
    left endpoint a; the right-endpoint dual isStrategyProof_surjective_isIR_right_iff for b is a \
    symmetric library addition not stated in Schummer–Vohra (2007) §10.2.2. Stated directly on \
    the single-peaked interval model rather than the production-function utility wrapper of \
    §10.2.2."

open Cslib.GameTheory.FacilityLocation in
register_result "facility-location-phantom-median" where
  title := "Anonymous (n - 1)-phantom-voter median characterization and GMVS conversion"
  topic := "game theory"
  sources := [
    { paper := SchummerVohra2007, theorem := "Theorem 10.2 and Exercise 10.2",
      locator := "Chapter 10, §10.2.1 pp. 247–250 and Exercise 10.2 p. 264" },
    { paper := Moulin1980, theorem := unverified, locator := unverified }
  ]
  theorems := [
    MoulinScheme.ofPhantoms_eval_eq_phantomMedian,
    isStrategyProof_surjective_anonymous_iff_phantomMedian
  ]
  scope := "Finite nonempty agent index type ι on Set.Icc a b (a ≤ b) with symmetric (Euclidean) \
    single-peaked preferences. Converts monotone (n - 1)-phantom vectors explicitly into \
    MoulinScheme parameters α_S = y_{n - 1 - |S|} (equivalently β_S = y_{|S| - 1}) and proves the \
    complete characterization of deterministic strategy-proof, surjective, anonymous rules."
