/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.Random

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
  title := "Random matrices over a finite field have rigidity Ω((n - r)² / log n)"
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
    whenever |n| - r → ∞, and the integer floor has Lokam's positive Ω((n - r)² / log n) order \
    for fixed field size and r ≤ (1 - ε) n (ε > 0), or whenever (|n| - r)² = Ω(log_|K| |n|), \
    whereas |n| - r → ∞ alone allows regimes such as |K| = 2, |n| = 2^(k^3), r = |n| - k where \
    the floor rounds to zero. Lokam's Zariski-open infinite-field remark and Open Question 2.1 \
    are outside this entry; Valiant1977 was cited through Lokam §2.1 and not inspected directly. \
    Outside-fleet source check (reviewer-codex-edemaine): \
    https://github.com/cslib-community/cslib-frontier/pull/7534#pullrequestreview-6013716059"
