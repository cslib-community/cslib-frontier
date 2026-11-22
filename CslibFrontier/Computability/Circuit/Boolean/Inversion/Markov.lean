/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Inversion.Decrease
public import CslibFrontier.Computability.Circuit.Boolean.Inversion.LowerBound
public import CslibFrontier.Computability.Circuit.Boolean.Inversion.UpperBound
public import Mathlib.Data.Nat.Log

/-!
# Markov's inversion-complexity theorem

For a system `target : BitString n → BitString m`, the least number of NOT gates is
`Nat.clog 2 (decrease target + 1)`. Here `decrease` is the maximum number of adjacent output
drops along an increasing input chain, and `Nat.clog` is the ceiling logarithm.

This is [Markov1963, Theorem 4.1]. Markov writes the answer as `D(Des(target))`, where `D(r)`
is the least natural number `k` such that `r < 2 ^ k`. The exact budget characterization
`exists_computes_negationCost_le_iff` uses that form directly. The equality
`ecomplexityFrom_negationCost_eq_clog` expresses the minimum using the existing weighted
native-circuit complexity API, and `exists_computes_negationCost_eq_clog` attains it.

The circuits are the native finite acyclic circuits over AND, OR, NOT and constants, with
unrestricted sharing and any finite number of outputs. Only NOT gates have nonzero cost.
Markov counts distinct negative subformulas in systems of AND/OR/NOT/constant formulas, using
the conventions of his 1957 paper retained in [Markov1963, §2]. Identical negative subformulas
can therefore be shared. The formal theorem uses native shared circuits. The upper proof
synthesizes monotone functions using AND, OR and constants without additional negations. The chain
maximum is attained on a nonempty strictly increasing chain (`exists_strict_chain_decrease`), matching
the source convention. The statements also cover zero inputs and zero outputs.

## Main results

* `Cslib.Circuits.Boolean.exists_computes_negationCost_le_iff`: a circuit with at most `k`
  negations exists exactly when the system's decrease is less than `2 ^ k`.
* `Cslib.Circuits.Boolean.ecomplexityFrom_negationCost_eq_clog`: the exact minimum number
  of negations is the ceiling logarithm of one plus the decrease.
* `Cslib.Circuits.Boolean.exists_computes_negationCost_eq_clog`: attainment of the exact bound.
* `Cslib.Circuits.Boolean.exists_computes_negationCost_le_clog_numInputs`: every system on
  `n` inputs is computable with at most `Nat.clog 2 (n + 1)` negations, independently of its
  number of outputs.

## References

* [A. A. Markov, *On the Inversion Complexity of a System of Boolean Functions*][Markov1963],
  Theorem 4.1, printed p. 478; definitions in §3, pp. 477–478, and proof in §5, pp. 478–479.
-/

public section

namespace Cslib.Circuits.Boolean

variable {n m : ℕ}

/-- A circuit with `k` negations has fewer than `2 ^ k` decreases along every increasing
input chain. -/
theorem decrease_lt_two_pow_negationCost (c : Circuit signature n m) :
    decrease (c.eval interpretation) < 2 ^ c.program.cost negationCost := by
  obtain ⟨rank, hrank, hbound⟩ := exists_descentRank_lt_two_pow_negationCost c
  have hle : decrease (c.eval interpretation) ≤ 2 ^ c.program.cost negationCost - 1 :=
    decrease_le_of_descentRank hrank (fun x => by have := hbound x; omega)
  have hpos := Nat.two_pow_pos (c.program.cost negationCost)
  omega

/-- **Markov's inversion theorem, budget form**: exactly the systems with fewer than
`2 ^ k` chain decreases can be computed using at most `k` negations.
See [Markov1963, Theorem 4.1]. -/
theorem exists_computes_negationCost_le_iff (target : BitString n → BitString m) (k : ℕ) :
    (∃ c : Circuit signature n m,
      c.Computes interpretation target ∧ c.program.cost negationCost ≤ k) ↔
      decrease target < 2 ^ k := by
  constructor
  · rintro ⟨c, hc, hcost⟩
    have heval : c.eval interpretation = target := funext hc
    have h := decrease_lt_two_pow_negationCost c
    rw [heval] at h
    exact h.trans_le (Nat.pow_le_pow_right (by decide) hcost)
  · intro h
    exact exists_computesFrom_of_descentRank id target (decreaseTo target)
      (isDescentRank_decreaseTo target) (fun x => (decreaseTo_le_decrease target x).trans_lt h)

/-- **Markov's inversion theorem, exact complexity form**: the minimum weighted cost on
the native Boolean circuit syntax is `⌈log₂ (decrease target + 1)⌉`.
This uses the existing `ecomplexityFrom` minimum, with the identity source family.
See [Markov1963, Theorem 4.1]. -/
theorem ecomplexityFrom_negationCost_eq_clog (target : BitString n → BitString m) :
    ecomplexityFrom interpretation negationCost target id =
      (Nat.clog 2 (decrease target + 1) : ℕ∞) := by
  apply le_antisymm
  · apply ecomplexityFrom_le_iff.mpr
    apply (exists_computes_negationCost_le_iff target _).mpr
    exact Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _)
  · apply le_ecomplexityFrom_iff.mpr
    intro c hc
    have heval : c.eval interpretation = target := funext hc
    have h := decrease_lt_two_pow_negationCost c
    rw [heval] at h
    exact_mod_cast (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr (Nat.succ_le_of_lt h)

/-- The exact ceiling-logarithm bound is attained by a native multioutput circuit. -/
theorem exists_computes_negationCost_eq_clog (target : BitString n → BitString m) :
    ∃ c : Circuit signature n m, c.Computes interpretation target ∧
      c.program.cost negationCost = Nat.clog 2 (decrease target + 1) := by
  obtain ⟨c, hc, hcost⟩ := (exists_computes_negationCost_le_iff target
    (Nat.clog 2 (decrease target + 1))).mpr
      (Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _))
  refine ⟨c, hc, hcost.antisymm ?_⟩
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  have heval : c.eval interpretation = target := funext hc
  have h := decrease_lt_two_pow_negationCost c
  rw [heval] at h
  exact Nat.succ_le_of_lt h

/-- Every Boolean system on `n` inputs is computable with at most `⌈log₂ (n + 1)⌉`
negations, regardless of its number of outputs. -/
theorem exists_computes_negationCost_le_clog_numInputs (target : BitString n → BitString m) :
    ∃ c : Circuit signature n m, c.Computes interpretation target ∧
      c.program.cost negationCost ≤ Nat.clog 2 (n + 1) := by
  obtain ⟨c, hc, hcost⟩ := exists_computes_negationCost_eq_clog target
  refine ⟨c, hc, hcost.le.trans ?_⟩
  exact Nat.clog_monotone 2 (Nat.add_le_add_right (decrease_le_numInputs target) 1)

end Cslib.Circuits.Boolean
