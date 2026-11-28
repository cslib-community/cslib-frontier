/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.HastadTest
import CslibFrontier.Foundations.BooleanAnalysis.MeanWeight
import CslibFrontier.Logics.Propositional.CSP.RandomizedAssignment
import CslibFrontier.Logics.Propositional.CSP.HastadTest

/-!
# Collected results: the Odd BLR test and Håstad's Dictator-vs.-No-Notables test
-/

register_result "odonnell-mean-bits-fourier-expansion" where
  title := "The expectation under independent bits with given means is the Fourier expansion"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 1.4",
      locator := "arXiv:2105.10386v1, §1.7, printed p. 35" }
  ]
  theorems := [
    Cslib.BitString.sum_meanWeight_mul_eq_sum_fourierCoeff
  ]
  scope := "For a real function f on the cube over any finite coordinate type and any real \
    means μ, Σ_a meanWeight μ a · f a = Σ_S f̂(S) Π_{i ∈ S} μ i, where meanWeight μ a = \
    Π_i (1 + signVal (a i) μ i) / 2 is the probability of a when bit i is an independent sign \
    of mean μ i (true is the sign −1). The identity holds for every real μ; for μ ∈ [−1, 1]^n, \
    the source's hypothesis, meanWeight is a probability distribution (meanWeight_nonneg, \
    sum_meanWeight). The source's F(μ) is the Fourier expansion on the right."

register_result "odonnell-randomized-assignment-multilinear" where
  title := "A constraint at a randomized Boolean assignment is its predicate's multilinear \
    expansion at the means"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 7.20(c)",
      locator := "arXiv:2105.10386v1, §7.5, printed p. 199" }
  ]
  theorems := [
    Cslib.Logic.PL.Constraint.satProb_eq_sum_fourierCoeff
  ]
  scope := "For a constraint of main's CSP Rel V with Boolean truth tables sem and any real \
    g : V → ℝ, Constraint.satProb sem g c, the probability that the relation holds when each \
    position of the scope reads an independent sign of mean g of its variable (true is −1), \
    equals Σ_S ψ̂(S) Π_{i ∈ S} g(scope[i]), the Fourier expansion of the predicate ψ as a 0/1 \
    function of the positions. A variable repeated in a scope is drawn afresh at each \
    position, as Exercise 7.22 reads queries. The identity holds for every real g; satProb is \
    a probability for |g| ≤ 1. Parts (a), (b) and (d) of the exercise are not stated."

register_result "odonnell-odd-blr-test" where
  title := "The acceptance probability of the Odd BLR test"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Proposition 7.46",
      locator := "arXiv:2105.10386v1, §7.4, printed p. 193" }
  ]
  theorems := [
    Cslib.BitString.oddBlrAcceptance_eq_sum,
    Cslib.BitString.oddBlrAcceptance_le_of_fourierCoeff_le
  ]
  scope := "For a Boolean function f on the uniform cube over any finite coordinate type, read \
    as signs F with true = −1, the Odd BLR test (uniform x, y and bit b; accept iff \
    f(x) + f(y) + f(x + y + (b, …, b)) = b) accepts with probability \
    1/2 + 1/2 Σ_{|S| odd} F̂(S)³, and with probability at most 1/2 + 1/2 M for every M ≥ 0 \
    that bounds F̂(S) for all odd |S|. The source's bound with M = max_{|S| odd} F̂(S) is \
    false when that maximum is negative (the NAND of two bits has odd coefficients −1/2 and \
    passes with probability 3/8); its proof needs M ≥ 0, which this statement assumes. The \
    test is stated as its acceptance probability, a real expectation, not as a PCP.LocalTest."

register_result "odonnell-hastad-dictator-vs-no-notables" where
  title := "For every 0 < δ < 1/2 there is a (1/2, 1 − δ)-Dictator-vs.-No-Notables test using \
    Max-E3-Lin predicates"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 7.42",
      locator := "arXiv:2105.10386v1, §7.4, printed p. 192 (proof pp. 194–195)" }
  ]
  theorems := [
    Cslib.Logic.PL.CSP.exists_isDictatorVsNoNotables_e3Lin,
    Cslib.Logic.PL.CSP.isDictatorVsNoNotables_hastadTest
  ]
  scope := "For every real 0 < δ < 1/2 some family T n : CSP Bool (Fin n → Bool) over the \
    Max-E3-Lin predicates (paritySem at arity e3LinArity = 3) is a (1/2, 1 − δ) test in the \
    sense of IsDictatorVsNoNotables: Definition 7.37 for testers that are CSP instances over a \
    finite constraint language, with both amendments of Remark 7.38 (repeated query strings; \
    soundness for every g with values in [−1, 1], each query an independent sign of mean \
    g(w) as in Exercise 7.22), completeness β ≤ satFraction of every dictator, and soundness \
    expectedSatFraction ≤ α + err ε for n ≥ 1, 0 < ε ≤ 1 and every (1 − ε)-stable influence at \
    most ε, with err ε → 0 as ε → 0⁺ chosen before n. The source's λ is the real function err \
    (ε = 0 excluded) and T 0 is unconstrained. The witness is Håstad's test at a rational flip \
    probability a / q realized by uniform digits in Fin q (hastadTest a q), a \
    (1/2, 1 − a / q) test for 0 < a and 2a < q; the source's real-noise test is reached through \
    a rational flip probability at most δ. Theorem 7.40 and Corollary 7.44 are not \
    formalized."
