/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Cooperative.Nucleolus

/-!
# Collected results: Cooperative game nucleolus, prenucleolus, and Kohlberg's criterion
-/

register_result "schmeidler-nucleolus-existence-uniqueness" where
  title := "Existence, uniqueness, core containment, and axioms of the nucleolus and prenucleolus"
  topic := "cooperative game theory"
  sources := [
    { paper := Schmeidler1969,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.CooperativeGame.exists_isLexMinimizerOn_of_isCompact,
    Cslib.GameTheory.CooperativeGame.unique_isLexMinimizerOn_of_convex,
    Cslib.GameTheory.CooperativeGame.existsUnique_isLexMinimizerOn,
    Cslib.GameTheory.CooperativeGame.existsUnique_nucleolus,
    Cslib.GameTheory.CooperativeGame.existsUnique_prenucleolus,
    Cslib.GameTheory.CooperativeGame.IsNucleolus.inCore,
    Cslib.GameTheory.CooperativeGame.nucleolus_inCore_of_nonemptyCore,
    Cslib.GameTheory.CooperativeGame.prenucleolus_eq_nucleolus_of_mem_imputations,
    Cslib.GameTheory.CooperativeGame.nucleolus_perm,
    Cslib.GameTheory.CooperativeGame.prenucleolus_perm,
    Cslib.GameTheory.CooperativeGame.nucleolus_eq_of_areSymmetric,
    Cslib.GameTheory.CooperativeGame.prenucleolus_eq_of_areSymmetric,
    Cslib.GameTheory.CooperativeGame.nucleolus_mapAffine,
    Cslib.GameTheory.CooperativeGame.prenucleolus_mapAffine,
    Cslib.GameTheory.CooperativeGame.nucleolus_isDummyAgent,
    Cslib.GameTheory.CooperativeGame.prenucleolus_isDummyAgent,
    Cslib.GameTheory.CostSharingGame.nucleolus_inCore_of_nonemptyCore
  ]
  scope := "Finite agent type [Fintype A] with real coalition values normalized by v(∅) = 0 \
    (and cost-sharing dual c = -v). Proves Schmeidler's existence (nonempty compact payoff sets) \
    and uniqueness (convex payoff sets, via midpoint strict descent of the descendingly sorted \
    excess vector sortDesc) theorems for general lexicographic excess minimizers; specializes to \
    unique nucleolus over imputations whenever ∑ i, v({i}) ≤ v(univ) and unconditional unique \
    prenucleolus over preimputations, core containment whenever NonemptyCore holds, coincidence \
    between nucleolus and prenucleolus when the prenucleolus is individually rational (or core is \
    nonempty), anonymity (perm), symmetry (AreSymmetric), S-equivalence covariance (mapAffine), \
    and dummy-player zero payoff (IsDummyAgent). Bibliographic theorem numbers and page locators \
    from Schmeidler (1969) remain marked unverified pending direct printed-page inspection."

register_result "kohlberg-nucleolus-criterion" where
  title := "Kohlberg's balanced-collection characterization of the nucleolus and prenucleolus"
  topic := "cooperative game theory"
  sources := [
    { paper := Kohlberg1971,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.CooperativeGame.isPrenucleolus_iff_kohlberg,
    Cslib.GameTheory.CooperativeGame.isNucleolus_iff_kohlberg
  ]
  scope := "Finite agent type [Fintype A] [DecidableEq A]. Using the affine Farkas lemma \
    (Matrix.exists_dual_le_of_forall_le), characterizes the prenucleolus on preimputations by \
    positivity balancedness (IsPositiveBalancedOn) of every nonempty upper-level coalition family \
    upperLevel x t (t ≤ excess S x over proper nonempty S ⊊ univ), and characterizes the \
    nucleolus on imputations by imputation balancedness (IsImputationBalancedAt, allowing \
    nonnegative singleton weights supported on agents with tight individual rationality \
    v({j}) = x_j). Bibliographic theorem numbers and page locators from Kohlberg (1971) remain \
    marked unverified pending direct printed-page inspection."
