/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Communication.Nondeterministic.UniqueDisjointnessUpper

section
open Cslib.Communication

register_result "sergeev-unique-disjointness-partition-rank" where
  title := "Sergeev: (n + 1)³ C(n, ⌊n / 3⌋) ≤ (n + 1)³ (3 / ∛4)^n ≺ 1.89^n SUM-rank upper bound \
    for unique disjointness"
  topic := "communication complexity"
  sources := [
    { paper := Sergeev2026UniqueDisjointness,
      theorem := "Theorem 1",
      locator := "§2, pp. 3–4 (arXiv:2607.27014v1)" }
  ]
  theorems := [
    Nondeterministic.partitionCoverNumber_uniqueDisjointnessRel_le,
    Nondeterministic.exists_partitionCoverNumber_uniqueDisjointnessRel_le_rpow,
    Nondeterministic.eventually_partitionCoverNumber_uniqueDisjointnessRel_lt
  ]
  scope := "Unconditional over any finite decidable ground type alpha (with asymptotic 1.89^n \
    specialization on Fin n), where partitionCoverNumber true (uniqueDisjointnessRel alpha) \
    Set.univ Set.univ equals the minimum (Nat, +, *)-semiring rank (Matrix.nonnegRank over Nat) \
    over completions of the partial unique-disjointness matrix U_n \
    (partitionCoverNumber_eq_iInf_nonnegRank_nat). Proves the finite non-asymptotic bound \
    <= (|alpha| + 1)^3 * C(|alpha|, |alpha| / 3) <= (|alpha| + 1)^3 * (3 / 4^(1/3))^|alpha| for \
    every alpha via shortened binary Hamming syndrome 3-code partitions \
    (Cslib.Code.exists_partition_minDist_three, Lemma 1) and row/column singleton partitions, \
    together with the strict eventual bound < (189 / 100)^n."

register_result "sergeev-unique-disjointness-covering-rank" where
  title := "Sergeev: 8 (n + 1)⁷ (3 / 2)^n covering-rank upper bound for unique disjointness, \
    matching Kaibel–Weltge up to a polynomial factor"
  topic := "communication complexity"
  sources := [
    { paper := Sergeev2026UniqueDisjointness,
      theorem := "Theorem 2",
      locator := "§3, pp. 4–6 (arXiv:2607.27014v1)" },
    { paper := KaibelWeltge2015,
      theorem := "Unique-disjointness rectangle-covering bound (unnumbered, from the combinatorial \
        part of the proof of Theorem 1)",
      locator := "§3, p. 3, via §2, p. 3 (arXiv:1307.3543v6)" }
  ]
  theorems := [
    Nondeterministic.exists_coverNumber_uniqueDisjointnessRel_le,
    Nondeterministic.two_pow_mul_coverNumber_uniqueDisjointnessRel_le,
    Nondeterministic.exists_poly_coverNumber_uniqueDisjointnessRel
  ]
  scope := "Unconditional over any finite decidable ground type alpha (and all n >= 1 on Fin n \
    with explicit constants C = 1024, k = 7), proving coverNumber true (uniqueDisjointnessRel \
    alpha) Set.univ Set.univ <= 8 * (|alpha| + 1)^7 * (3 / 2)^|alpha| via the \
    Sapozhenko–Lovász–Stein greedy covering lemma (Cslib.exists_subset_cover_card_le_of_uniform, \
    Lemma 2), shortened Hamming 3-code partitions, exact integer-rounded parameters, and \
    Vandermonde hypergeometric mode bounds (resolving the parity and rounding elisions noted in \
    footnote 5 on p. 5 without an asymptotic threshold). Combined with Kaibel–Weltge's lower \
    bound, establishes (3 / 2)^n <= r <= 1024 * n^7 * (3 / 2)^n for every n >= 1."

end
