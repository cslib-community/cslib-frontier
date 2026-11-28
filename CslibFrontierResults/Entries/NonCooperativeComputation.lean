/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.RationalCrypto.NonCooperativeComputation

/-!
# Collected results: correlated equilibrium min-max bound and non-cooperatively computable functions
-/

namespace CslibFrontierResults.Entries.NonCooperativeComputation

register_result "ce-minmax-payoff-lower-bound" where
  title := "Correlated equilibrium conditional payoff min-max lower bound"
  topic := "game theory"
  sources := [
    { paper := DodisRabin2007, theorem := "Claim 8.4", locator := "Section 8.4.2, p. 195" }
  ]
  theorems := [
    Cslib.GameTheory.PayoffGame.isMinimaxValue_correlatedMinMax,
    Cslib.GameTheory.PayoffGame.exists_correlatedMinMax_punisher,
    Cslib.GameTheory.PayoffGame.correlatedMinMax_le_condPayoff
  ]
  scope := "Finite complete-information strategic payoff games G : PayoffGame ι S with nonempty \
    finite action spaces (∀ j, Nonempty (S j)). Defines player i's correlated min-max value \
    v_i = inf_{z_{-i} ∈ Δ(S_{-i})} max_{a ∈ S i} u_i(a, z_{-i}) (PayoffGame.correlatedMinMax), \
    proves via von Neumann's minimax theorem (exists_isMinimaxValue) that v_i equals the \
    opponent-vs-player zero-sum value and is attained by a correlated punishment profile z_{-i} \
    (exists_correlatedMinMax_punisher), and proves Claim 8.4: for every correlated equilibrium σ \
    of G.toCostGame and every action a in the support of σ's i-th marginal \
    (0 < marginalWeight σ i a), the conditional expected payoff condPayoff G σ i a is at least \
    G.correlatedMinMax i. The cryptographic MPC punishment preamble built on Claim 8.4 in \
    Section 8.4.2 is not formalized here."

register_result "ncc-functions-characterization" where
  title := "Characterization of non-cooperatively computable (NCC) functions"
  topic := "game theory"
  sources := [
    { paper := DodisRabin2007, theorem := "Theorem 8.6 and Footnote 8",
      locator := "Section 8.5.1, pp. 197–199" }
  ]
  theorems := [
    Cslib.GameTheory.RationalCrypto.IsDominated.isReversible,
    Cslib.GameTheory.RationalCrypto.isNCC_iff_not_dominated_and_not_reversible,
    Cslib.GameTheory.RationalCrypto.not_isNCC_parity,
    Cslib.GameTheory.RationalCrypto.not_isNCC_or,
    Cslib.GameTheory.RationalCrypto.not_isNCC_and,
    Cslib.GameTheory.RationalCrypto.isNCC_majority
  ]
  scope := "Single-output deterministic functions f : (∀ i, T i) → O over finite player sets ι \
    with 2 ≤ Fintype.card ι, finite input spaces T i, full-support prior D (IsMixedStrategy D and \
    ∀ t, 0 < D t), and correctness/exclusivity utilities u : ι → (ι → Bool) → ℝ satisfying \
    high-correctness priority (HighCorrectnessPriority u D, equivalent by \
    highCorrectnessPriority_iff_minProb to u_i(c) > (1 - ε) u_i(c') + ε u_i(c'') at \
    ε = min_t D t). \
    IsNCC (Definition 8.5) is stated as PayoffGame.IsPureNash (honestProfile fallback) on the \
    mediated game mediatedGame f u D over deterministic (report : T i → Option (T i), \
    interpret : T i → Option O → O) deviations (which by linearity of expectation is equivalent \
    to mixed/behavioral deviations). Non-constancy (∃ t₁ t₂, f t₁ ≠ f t₂) replaces the source's \
    stronger p. 197 standing assumption EveryInputMatters f (proved to imply non-constancy via \
    EveryInputMatters.exists_ne), and Theorem 8.6 holds uniformly in the honest error-fallback \
    rule fallback. The coalitional k-NCC extension (isKNCC_iff_not_kDominated_and_not_kReversible \
    and isKNCC_majority_iff, after 'Collusions' on p. 199) is proved in the same module as a \
    library extension and omitted from this numbered-theorem entry."

end CslibFrontierResults.Entries.NonCooperativeComputation
