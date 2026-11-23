/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.Random
import CslibFrontier.Foundations.Data.MvPolynomial.ConsecutiveLayers

register_result "lokam-matrix-rigidity-upper-bound" where
  title := "Every n × n matrix over a field has rigidity at most (n - r)²"
  topic := "algebraic complexity"
  sources := [
    { paper := Lokam2009,
      theorem := "Upper bound on matrix rigidity after Definition 2.1 (unnumbered)",
      locator := "§2.1, printed p. 11 (PDF p. 14), after Definition 2.1" },
    { paper := Valiant1977, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Matrix.rigidity_le_sq_sub,
    Matrix.rigidity_le_mul_sub
  ]
  scope := "Unconditional over any field K ([Field K], [Fintype n] for rigidity_le_sq_sub and \
    [Fintype m] [Fintype n] for the rectangular generalization rigidity_le_mul_sub, with no \
    DecidableEq), where Matrix.rigidity A r = sInf (diffCount A '' {B | B.rank ≤ r}) matches \
    Definition 2.1 by writing C = B - A. Proves the non-strict inequality ≤ (n - r)² (some PDF \
    text extractors read p. 11's typeset glyph as strict < (n - r)², whereas ≤ (n - r)² is the \
    correct bound and is attained with equality by the checked 2 × 2 rational Hadamard matrix at \
    both r = 0 and r = 1). Valiant1977 is cited through Lokam §2.1 and was not inspected \
    directly. Outside-fleet source check (reviewer-codex-edemaine): \
    https://github.com/cslib-community/cslib-frontier/pull/7534#pullrequestreview-6013716059"

register_result "lokam-random-matrix-rigidity-finite-field" where
  title := "Random n × n matrices over a finite field K have rigidity at least \
    ⌊(n - r)² / (4 ⌊log_|K| n⌋ + 6)⌋ with probability > 1 - |K|^(-⌊(n - r)² / 2⌋)"
  topic := "algebraic complexity"
  sources := [
    { paper := Lokam2009,
      theorem := "Finite-field random-matrix rigidity after Definition 2.1 (unnumbered)",
      locator := "§2.1, printed pp. 11–12 (PDF pp. 14–15), after Definition 2.1" },
    { paper := Valiant1977, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Matrix.one_sub_inv_pow_lt_card_sq_div_log_le_rigidity
  ]
  scope := "Counts all square matrices Matrix n n K over any finite field K ([Field K] \
    [Fintype K] [Fintype n] [DecidableEq n]), so the normalized count is the exact uniform-matrix \
    probability, with no sampling-algorithm, circuit, or complexity assumptions. Proves the \
    finite non-asymptotic bound 1 - (|K| : ℝ)⁻¹ ^ ((|n| - r) ^ 2 / 2) < \
    #{A | (|n| - r) ^ 2 / (4 * Nat.log |K| |n| + 6) ≤ A.rigidity r} / Fintype.card (Matrix n n K) \
    with integer floor division and explicit exponential error. The probability tends to 1 \
    whenever |n| - r → ∞, the floor is positive once 4 * Nat.log |K| |n| + 6 ≤ (|n| - r) ^ 2, \
    and for fixed field size and r ≤ (1 - ε) n (fixed ε > 0) it yields Lokam's positive \
    Ω((n - r)² / log n) order (whereas slower growth such as |K| = 2, |n| = 2^(k²), r = |n| - k \
    leaves ⌊k² / (4k² + 6)⌋ = 0). Lokam's \
    Zariski-open infinite-field remark and Open Question 2.1 are outside this entry; Valiant1977 \
    was cited through Lokam §2.1 and not inspected directly. Outside-fleet source check \
    (reviewer-codex-edemaine): \
    https://github.com/cslib-community/cslib-frontier/pull/7534#pullrequestreview-6013716059"

register_result "alman-williams-consecutive-layer-interpolation" where
  title := "Integer multilinear interpolation on consecutive Hamming layers"
  topic := "algebraic complexity"
  sources := [
    { paper := AlmanWilliams2017, theorem := "Lemma 3.2",
      locator := "§3, arXiv v2, printed p. 6 (PDF p. 7)" }
  ]
  theorems := [Cslib.exists_multilinear_of_consecutive_weights]
  scope := "Prescribes any integer value per weight on a band of t consecutive layers. \
    The polynomial has total degree at most t - 1 and individual degree at most one. \
    Lean uses k ≤ |x| < k + t where the paper uses k + 1 ≤ |z| ≤ k + r, and drops the \
    dimension hypothesis n ≥ k + t by prescribing values only on existing layers. \
    Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/7803#pullrequestreview-6016309173"
