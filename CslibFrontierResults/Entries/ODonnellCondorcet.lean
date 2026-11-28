/-
Copyright (c) 2026 Vincent Liew, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.CondorcetElection

/-!
# Collected results: Condorcet elections and Kalai's proof of Arrow's Theorem
-/

register_result "odonnell-kalai-condorcet-formula" where
  title := "Kalai's formula for the probability of a Condorcet winner"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 2.56",
      locator := "arXiv:2105.10386v1, §2.5, printed p. 59" }
  ]
  theorems := [Cslib.BitString.condorcetWinnerProb_eq]
  scope := "For every f : (ι → Bool) → Bool over a finite coordinate type ι, used in the three \
    pairwise elections c vs. c + 1 of the candidates Fin 3, with voter rankings given as \
    permutations of Fin 3 drawn independently and uniformly (impartial culture): the \
    probability that some candidate wins both of its pairwise elections (Definition 2.55) is \
    3/4 − 3/4 Stab_{−1/3}[F] for F = signVal ∘ f."

register_result "odonnell-arrow-kalai" where
  title := "Arrow's Theorem for 3-candidate Condorcet elections, by Kalai's proof"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Arrow's Theorem (unnumbered)",
      locator := "arXiv:2105.10386v1, §2.5, printed pp. 58–59" }
  ]
  theorems := [Cslib.BitString.exists_eq_of_forall_exists_isCondorcetWinner]
  scope := "For a finite electorate ι and one rule f : (ι → Bool) → Bool used in all three \
    pairwise elections: if every profile of rankings has a Condorcet winner and \
    f (fun _ => true) = true, then f x = x i for some voter i. The book assumes unanimity in \
    both directions; only this half is used. The variant of Exercise 2.51 with three different \
    rules is entry odonnell-arrow-three-rules."

register_result "odonnell-condorcet-degree-one-bound" where
  title := "The probability of a Condorcet winner is at most 7/9 + 2/9 W¹"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Corollary 2.59",
      locator := "arXiv:2105.10386v1, §2.5, printed p. 60" }
  ]
  theorems := [Cslib.BitString.condorcetWinnerProb_le]
  scope := "For every f : (ι → Bool) → Bool over a finite coordinate type, under impartial \
    culture, the probability of a Condorcet winner is at most 7/9 + 2/9 W¹[signVal ∘ f]."

register_result "odonnell-robust-arrow" where
  title := "Robust Arrow's Theorem: nearly paradox-free elections are nearly dictatorships"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Corollary 2.60",
      locator := "arXiv:2105.10386v1, §2.5, printed p. 60" }
  ]
  theorems := [Cslib.BitString.exists_hammingDist_xor_div_le_of_le_condorcetWinnerProb]
  scope := "For a nonempty finite electorate ι and every f : (ι → Bool) → Bool: if the \
    probability of a Condorcet winner under impartial culture is at least 1 − ε, then for some \
    voter i and bit b, f x = b ⊕ x i (the book's ±χ_i) except on a fraction at most \
    14409/2 · ε of the inputs. The book states probability exactly 1 − ε and closeness O(ε); \
    the constant is 9/2 times the library's FKN constant 1601."

register_result "odonnell-arrow-three-rules" where
  title := "Arrow's Theorem for three different unanimous voting rules"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 2.51(a)",
      locator := "arXiv:2105.10386v1, §2.6, printed p. 65" }
  ]
  theorems := [Cslib.BitString.eq_of_forall_exists_isCondorcetWinner,
    Cslib.BitString.exists_forall_eq_of_forall_exists_isCondorcetWinner]
  scope := "If the elections 0 vs. 1, 1 vs. 2 and 2 vs. 0 are decided by voting rules F 0, F 1, \
    F 2, each unanimous in both directions, and every profile of rankings has a Condorcet \
    winner, then F 0 = F 1 = F 2, and (for a finite electorate) all three are the dictator \
    x ↦ x i for some voter i. Part (b), more than three candidates, is not covered."
