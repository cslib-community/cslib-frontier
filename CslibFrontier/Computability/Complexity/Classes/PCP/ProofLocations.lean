/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PCP.NP

/-!
# The effective length of PCP proofs

A PCP verifier of query complexity `q` and randomness complexity `r` examines, on a fixed input,
at most `2 ^ (q + r)` locations of its proof oracle over all its coin sequences and all answers it
may receive; a non-adaptive verifier examines at most `2 ^ r · q`
[Goldreich, Exercise 9.15][Goldreich2007DraftR5].

## Statement-to-source mapping

Goldreich's verifier is a probabilistic polynomial-time oracle machine, so it may choose each query
from the answers to the previous ones. On a fixed input `x` and a fixed coin sequence `ρ`, such a
machine is a decision tree over the locations of the proof: its root is the first query, the two
subtrees are the continuations after the answers `0` and `1`, and the leaves are its verdicts. A
query complexity of `q` makes the depth at most `q`, on every answer sequence. The adaptive bound,
`Cslib.DecisionTree.card_biUnion_allQueries_le` in `DecisionTree/Leaves`, is therefore stated for
a family `T ρ`, indexed by the
`r`-bit coin sequences `ρ`, of decision trees of depth at most `q`; the locations examined "for all
possible answers" are the variables at the internal nodes (`DecisionTree.allQueries`), which
contain the locations queried on any proof (`DecisionTree.queries_subset_allQueries`). The input
`x` is fixed and does not appear: for Goldreich's `q(|x|)` and `r(|x|)` take `q` and `r` to be
these values. The locations may be of any type.

The library's PCP verifiers (`Cslib.Complexity.PCPVerifier`) are non-adaptive: the list of
queried locations is a function of the input and the random string. For them the bound
(`Cslib.Complexity.IsPCPVerifier.card_toFinset_queryTable_le`) counts the distinct locations in
`PCPVerifier.queryTable`, which lists the locations queried on all random strings of the right
length (`PCPVerifier.mem_queryTable`). The randomness and query bounds of `IsPCPVerifier` are the
functions `r` and `q` of the encoded length `n` of the instance.

## Main results

* `Cslib.Complexity.IsPCPVerifier.card_toFinset_queryTable_le`: a non-adaptive verifier examines at
  most `2 ^ r(n) · q(n)` locations on an instance of encoded length `n`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft of April 2007,
  Exercise 9.15][Goldreich2007DraftR5]
-/

public section

namespace Cslib

namespace Complexity

variable {α : Type} {enc : α ↪ List Bool} {r q : ℕ → ℕ} {V : PCPVerifier α} {A : Set α}

/-- **The effective length of non-adaptive PCP proofs**
[Goldreich, Exercise 9.15][Goldreich2007DraftR5]: a non-adaptive verifier using at most `r n`
random bits and `q n` queries on instances of encoded length `n` examines, over all its random
strings, at most `2 ^ r(n) · q(n)` distinct locations of the proof. -/
theorem IsPCPVerifier.card_toFinset_queryTable_le (h : IsPCPVerifier enc r q V A) (a : α) :
    (V.queryTable a).toFinset.card ≤ 2 ^ r (enc a).length * q (enc a).length := by
  have hsum : (V.queryTable a).length ≤ 2 ^ V.coins a * q (enc a).length := by
    rw [PCPVerifier.queryTable, List.length_flatMap]
    -- every random string of the enumeration contributes at most `q n` queries
    refine (List.sum_le_length_nsmul (n := q (enc a).length) _ fun m hm => ?_).trans_eq
      (by simp)
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hm
    exact h.length_queries_le a word (BitString.mem_enumList.mp hword)
  exact (List.toFinset_card_le _).trans (hsum.trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right Nat.two_pos (h.coins_le a))))

end Complexity

end Cslib
