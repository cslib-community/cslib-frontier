/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity.Hadamard

register_result "hadamard-matrix-rigidity-lower-bound" where
  title := "Every n × n Hadamard or generalized Hadamard matrix has rigidity at least \
    n² / (4r) for 1 ≤ r ≤ n / 2"
  topic := "algebraic complexity"
  sources := [
    { paper := Lokam2009,
      theorem := "Theorem 3.8 and Lemma 3.6",
      locator := "§3.2–3.2.1, printed pp. 44–46 (PDF pp. 47–49)" },
    { paper := deWolf2006,
      theorem := "Theorem 1 and Theorem 2",
      locator := "§1.2 and §3, arXiv:quant-ph/0505188v2 (qr-icalp06.tex, lines 133, 286–335)" }
  ]
  theorems := [
    Matrix.IsHadamard.card_sq_le_four_mul_rigidity,
    Matrix.IsHadamard.card_sq_le_four_mul_rigidity_of_trivialStar,
    Matrix.IsHadamard.card_mul_le_rank_submatrix,
    Matrix.IsHadamard.card_mul_le_rank_submatrix_of_trivialStar
  ]
  scope := "Uses Mathlib's Matrix.IsHadamard (unitary entries with H * Hᴴ = |n| • 1 and \
    Hᴴ * H = |n| • 1), which over ℂ is Lokam's Definition 3.3 (generalized Hadamard matrices \
    |h_{ij}| = 1, H H* = n I_n) and over rings with trivial star is the classical ±1 Hadamard \
    condition. Proves the lossless cleared-denominator form |n| ^ 2 ≤ 4 * r * H.rigidity r for \
    1 ≤ r and 2 * r ≤ |n| (together with the submatrix rank step |α| * |β| ≤ |n| * rank M on \
    distinct rows and columns), both over ℝ and ℂ ([RCLike K]) and over any characteristic-zero \
    field with trivial star ([Field K] [CharZero K] [StarRing K] [TrivialStar K], including ℚ). \
    Lokam's printed statement of Theorem 3.8 omits r ≤ n / 2 while selecting 2r rows in the \
    first sentence of its proof; de Wolf (2006), §1.2 and §3, Theorem 2 states r ≤ n / 2 \
    explicitly, and a checked 4 × 4 counterexample at r = 3 shows R(3) = 1 < 16 / 12."

register_result "sylvester-hadamard-rigidity-lower-bound" where
  title := "The 2^k × 2^k Sylvester–Hadamard matrix has rigidity at least \
    2^(2k) / (4r) for 1 ≤ r ≤ 2^(k-1)"
  topic := "algebraic complexity"
  sources := [
    { paper := Lokam2009,
      theorem := "Theorem 2.11",
      locator := "§2.2, eq. (2.3) and printed pp. 20–21 (PDF pp. 23–24)" },
    { paper := Midrijanis2005,
      theorem := "Theorem 1",
      locator := "§1.3 and §2, arXiv:cs/0506081v1 (rigidity.tex, lines 159–205)" }
  ]
  theorems := [
    Matrix.two_pow_le_four_mul_rigidity_sylvesterHadamard_two_pow,
    Matrix.two_pow_le_four_mul_rigidity_sylvesterHadamard
  ]
  scope := "Matrix.sylvesterHadamard R k defines the 2^k × 2^k ±1 Sylvester–Hadamard matrix of \
    Lokam eq. (2.3) (verified by sylvesterHadamard_one and sylvesterHadamard_add_submatrix, with \
    k = 0 giving the 1 × 1 identity). two_pow_le_four_mul_rigidity_sylvesterHadamard_two_pow \
    proves Midrijānis's exact block-tiling bound 2^(2k) ≤ 4 * 2^t * rigidity (2^t) for t < k \
    (power-of-two r = 2^t ≤ 2^k / 2; in Lokam's Theorem 2.11 with r = 2^(t - 1), the 2r ≤ 2^k \
    restriction t ≤ k comes from choosing blocks of side 2^t, which are ±S_t by eq. (2.3) \
    rather than that proof sentence's printed index slip ±S_{k-t}, whereas Midrijānis Theorem 1 \
    states r ≤ n / 2 explicitly) over every field K with (2 : K) ≠ 0, including \
    odd-characteristic finite fields (while failing in characteristic 2, where rank is 1). \
    two_pow_le_four_mul_rigidity_sylvesterHadamard extends the bound to all integers 1 ≤ r with \
    2 * r ≤ 2^k over any characteristic-zero field [Field K] [CharZero K] (including ℚ, ℝ, and ℂ)."
