/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.Bribery
import CslibFrontier.Foundations.BooleanAnalysis.CoalitionalInfluence

/-!
# Collected results: Bribing monotone elections and coalitional influence
-/

register_result "odonnell-bribing-monotone-elections" where
  title := "Bribing O(n / log n) voters biases a monotone election"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Proposition 9.27",
      locator := "arXiv:2105.10386v1, §9.6, printed pp. 265–266" }
  ]
  theorems := [Cslib.BitString.exists_card_le_and_le_expect_signVal_piecewise_false,
    Cslib.BitString.exists_card_le_and_expect_signVal_piecewise_true_le]
  scope := "For monotone f : (ι → Bool) → Bool (Bool's order false < true) on n = card ι ≥ 2 \
    voters, read as signs F through signVal (false ↦ 1, the book's vote 1), and every real \
    0 ≤ a < 1 in place of the book's .99: if −a ≤ 𝔼 F, some J with \
    #J ≤ 8 a n / ((1 − a²) log n) + 1, bribed to vote false \
    (x ↦ f (J.piecewise (fun _ => false) x), the book's f_{J̄|(1,…,1)}), makes the mean at least \
    a; if 𝔼 F ≤ a, some J with the same bound bribed to vote true makes the mean at most −a. \
    The book's O(n / log n) is made explicit with the natural logarithm and the constant 1/4 of \
    the library's KKL theorem; n = 1 is excluded since log 1 = 0."

register_result "odonnell-bribing-monotone-elections-near-unanimity" where
  title := "Bribing a monotone election to near-unanimity; a small coalition controls it"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 9.27(a)–(b)",
      locator := "arXiv:2105.10386v1, §9.7, printed p. 275" }
  ]
  theorems := [Cslib.BitString.exists_card_le_and_one_sub_le_expect_signVal_piecewise_false,
    Cslib.BitString.exists_card_le_and_expect_signVal_piecewise_true_le_sub_one,
    Cslib.BitString.exists_card_le_and_one_sub_le_coalitionInfluence]
  scope := "For monotone f : (ι → Bool) → Bool (false < true) on n = card ι ≥ 2 voters, read as \
    signs F through signVal (false ↦ 1), with variance 𝔼 x, (F x − 𝔼 y, F y) ^ 2 ≥ δ > 0, and \
    0 < ε ≤ 1 (the book takes 0 < ε < 1/2). (a) Some J with \
    #J ≤ 8 n log (2 / (ε δ)) / log n + 2, bribed to vote false, makes the mean at least 1 − ε, \
    and some J with the same bound, bribed to vote true, makes it at most ε − 1. (b) Some J with \
    #J ≤ 16 n log (2 / (ε δ)) / log n + 4 has coalitionInfluence (uniformOfFintype) J f ≥ 1 − ε, \
    the book's Inf~_J[f]. The book's O(log (1 / (ε δ)) · n / log n) is made explicit with the \
    natural logarithm and log (2 / (ε δ)), at most twice log (1 / (ε δ)) when ε < 1/2 and δ ≤ 1. \
    Part (a) is proved by a two-phase geometric argument in place of the book's dyadic hint."

register_result "odonnell-directed-coalitional-influence" where
  title := "Coalitional influence toward an outcome"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 9.25(a)–(e)",
      locator := "arXiv:2105.10386v1, §9.7, printed pp. 274–275" }
  ]
  theorems := [Cslib.BitString.coalitionInfluenceToward_singleton,
    Cslib.BitString.coalitionInfluenceToward_nonneg,
    Cslib.BitString.coalitionInfluenceToward_le_one,
    Cslib.BitString.coalitionInfluence_eq_add,
    Cslib.BitString.coalitionInfluenceToward_eq_of_monotone,
    Cslib.BitString.coalitionInfluence_parityOn_univ]
  scope := "Under the uniform distribution on ι → Bool for a finite ι, \
    coalitionInfluenceToward b J f is Pr_z[∃ y, f (J.piecewise y z) = b] − Pr[f = b], the \
    book's Inf~^b_J[f] with b ∈ {−1, 1} a Bool read through signVal (true ↦ −1). (a) One voter \
    has Inf~^b_{i}[f] = Inf_i[f] / 2 for each b; the book's undirected Inf~_{i}[f] = Inf_i[f] \
    is the existing coalitionInfluence_singleton in another module and is not listed. \
    (b) 0 ≤ Inf~^b_J[f] ≤ 1 for each b. (c) The uniform coalitionInfluence J f is \
    Inf~^true_J[f] + Inf~^false_J[f]. (d) For monotone f (false < true), Inf~^b_J[f] is \
    Pr_z[f (J.piecewise (fun _ => b) z) = b] − Pr[f = b]. (e) Every nonempty J has coalitional \
    influence 1 on parityOn univ, the book's χ_[n]. Parts (f) and (g), on Majority and Tribes, \
    are not covered."
