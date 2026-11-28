/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.Monotone
import CslibFrontier.Foundations.BooleanAnalysis.PolynomialThreshold
import CslibFrontier.Foundations.BooleanAnalysis.Unate
import CslibFrontier.Foundations.BooleanAnalysis.NoiseSensitivityInfluence
import CslibFrontier.Foundations.BooleanAnalysis.Peres

/-!
# Collected results: Peres's theorem and unate functions
-/

register_result "odonnell-ltf-examples" where
  title := "Majority, AND, OR, the literals ±χᵢ and the constants are linear threshold functions"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 2.2",
      locator := "arXiv:2105.10386v1, §2.6, printed p. 61" }
  ]
  theorems := [
    Cslib.BitString.isPTF_one_threshold,
    Cslib.BitString.isPTF_one_xor
  ]
  scope := "Linear threshold function means IsPTF 1: read as signs, the sign of a real \
    polynomial of Fourier degree at most one that vanishes nowhere on the cube. For all n and j, \
    the threshold function threshold n j on Fin n → Bool (true exactly when at least j bits are \
    true) is one, as the sign of j − 1/2 − weight x; this covers majority \
    (majority n = threshold n ⌈n/2⌉), AND (threshold n n), OR (threshold n 1) and the constants \
    ±1 (threshold n 0 and threshold n (n + 1)). On any finite coordinate type, each literal \
    x ↦ b ⊕ x i, read as signs ±χ_i, is one."

register_result "odonnell-unate-influence-degree-one-coefficient" where
  title := "A direction is unate exactly when its influence is its degree-one coefficient"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 2.5(a)",
      locator := "arXiv:2105.10386v1, §2.6, printed p. 61" }
  ]
  theorems := [
    Cslib.BitString.abs_fourierCoeff_singleton_le_influence,
    Cslib.BitString.abs_fourierCoeff_singleton_eq_influence_iff
  ]
  scope := "For a Boolean function f on any finite coordinate type, read as signs, and a \
    coordinate i: |f̂({i})| ≤ Inf_i[f], with equality if and only if f is unate in direction i \
    (IsUnateIn i f: raising bit i from false to true never lowers f, or never raises it, at \
    every point). Exercise 2.5(b), I[f] ≤ √(2/π) √n + O(n^(−1/2)) for unate f via Theorem \
    2.33, is not covered; tracked on https://github.com/cslib-community/cslib-frontier/issues/2131."

register_result "odonnell-ltfs-are-unate" where
  title := "Linear threshold functions are unate"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 2.6",
      locator := "arXiv:2105.10386v1, §2.6, printed p. 61" }
  ]
  theorems := [
    Cslib.BitString.IsPTF.isUnate
  ]
  scope := "Every linear threshold function (IsPTF 1 f: f read as signs is the sign of a \
    real polynomial of Fourier degree at most one that vanishes nowhere on the cube), on any \
    finite coordinate type, is unate in every direction (IsUnate f)."

register_result "odonnell-unate-total-influence" where
  title := "Monotone and unate functions have total influence at most √n"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 2.23",
      locator := "arXiv:2105.10386v1, §2.6, printed p. 63" }
  ]
  theorems := [
    Cslib.BitString.IsUnate.totalInfluence_le_sqrt_card_mul,
    Cslib.BitString.IsUnate.totalInfluence_le_sqrt_card,
    Cslib.BitString.totalInfluence_le_sqrt_card_mul_of_monotone,
    Cslib.BitString.totalInfluence_le_sqrt_card_of_monotone,
    Cslib.BitString.totalInfluence_le_sqrt_card_mul_of_antitone,
    Cslib.BitString.totalInfluence_le_sqrt_card_of_antitone
  ]
  scope := "A unate Boolean function on n coordinates (any finite coordinate type), read as \
    signs with variance σ², has total influence at most √(n σ²), hence at most √n; monotone \
    and antitone functions are unate, and the four monotone and antitone bounds are stated \
    separately. The proof is the exercise's Cauchy–Schwarz and Parseval argument. The bound \
    for linear threshold functions, Cslib.BitString.IsPTF.totalInfluence_le_sqrt_card \
    (Unate.lean), is the step of the proof of Peres's Theorem (§5.5, printed p. 132) and is \
    not registered."

register_result "odonnell-noise-sensitivity-from-total-influence" where
  title := "Noise sensitivity of a class closed under negating and identifying variables"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 5.35",
      locator := "arXiv:2105.10386v1, §5.5, printed p. 131" }
  ]
  theorems := [
    Cslib.BitString.noiseSensitivity_le_div_of_comp_add_comp_mem,
    Cslib.BitString.noiseSensitivity_le_div_of_totalInfluence_le
  ]
  scope := "For 0 < δ ≤ 1/2 and m = ⌊1/δ⌋: if a class B, B n of functions on Fin n → Bool, is \
    closed under f ↦ (w ↦ f (z + w ∘ π)) for every string z and every map π : Fin n → Fin m, \
    and its members on n bits have total influence at most A n, then every member has \
    NS_δ[f] ≤ A(m)/m. These maps negate (z), identify (π not injective) and add dummy \
    variables (π not onto). The book asks only for closure under negation and identification, \
    but its proof applies the hypothesis to maps π that are not onto, so it uses closure under \
    adding dummy variables implicitly. Source issue: without that closure the statement is \
    false; B = {χ₁, −χ₁} on one bit is closed under negation and identification, and \
    A(1) = 1, A(m) = 0 for m ≥ 2 at δ = 1/4 would give NS_{1/4}[χ₁] ≤ 0, while \
    NS_{1/4}[χ₁] = 1/4. The second theorem is the same argument for one function on any \
    finite coordinate type, assuming the bound for its own functions w ↦ f (z + w ∘ π), π \
    into Fin m."

register_result "odonnell-peres-theorem" where
  title := "Peres's Theorem: linear threshold functions have noise sensitivity O(√δ)"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014,
      theorem := "Peres's Theorem (unnumbered), Remark 5.36 (first two sentences, without \
        √δ + O(δ^(3/2))), and the uniform noise stability of LTFs after it (Definition 5.34)",
      locator := "arXiv:2105.10386v1, §5.5, printed pp. 130 and 132" }
  ]
  theorems := [
    Cslib.BitString.IsPTF.noiseSensitivity_le_sqrt_three_div_two_mul,
    Cslib.BitString.IsPTF.noiseSensitivity_le_inv_sqrt_floor,
    Cslib.BitString.isUniformlyNoiseStable_isPTF_one
  ]
  scope := "Linear threshold function means IsPTF 1 f on any finite coordinate type: f read \
    as signs is the sign of a real polynomial of degree at most one that vanishes nowhere on \
    the cube; the book's form sgn(a₀ + Σ aᵢxᵢ) with sgn(0) = 1 reduces to this by perturbing \
    a₀ (printed p. 114), which is not proved here. For such f: NS_δ[f] ≤ 1/√⌊1/δ⌋ for \
    0 < δ ≤ 1/2, the bound the first sentence of Remark 5.36 says the proof attains, and \
    NS_δ[f] ≤ √(3/2) √δ for 0 ≤ δ ≤ 1/2, the bound of its second sentence, which gives the \
    book's O(√δ). Hence the linear threshold functions on Fin n → Bool, over all n, are \
    uniformly noise-stable (Definition 5.34, printed p. 130) in IsUniformlyNoiseStable's form: \
    a real-valued ε with ε(δ) → 0 as δ → 0⁺ bounding NS_δ for δ ∈ (0, 1/2], where the book \
    takes ε : [0, 1/2] → [0, 1] (clamping ε to [0, 1] and the value NS_0 = 0 make these \
    equivalent; not stated as a theorem). The remark's √δ + O(δ^(3/2)) for small δ is not \
    covered, nor is its √(2/π) √δ + O(δ^(3/2)) refinement; tracked on \
    https://github.com/cslib-community/cslib-frontier/issues/2131."
