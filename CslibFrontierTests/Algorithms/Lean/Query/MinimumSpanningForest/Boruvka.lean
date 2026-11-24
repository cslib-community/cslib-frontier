/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Boruvka

/-!
# Tests: Borůvka steps as comparison programs

On a multigraph with a self-loop and a pair of parallel edges: a step on the self-loop alone
selects nothing, a step on the empty edge set selects nothing, and the bounds and the contraction
identity of `k` steps apply.
-/

namespace CslibFrontierTests.Algorithms.Query.MinimumSpanningForest.Boruvka

open Cslib Query Multigraph Finset

/-- Edge `0` is a self-loop at `0`; edges `1` and `2` are parallel edges joining `0` and `1`;
edge `3` joins `1` and `2`, and edge `4` joins `0` and `2`. -/
private def multi : Fin 5 → Sym2 (Fin 3)
  | 0 => s(0, 0)
  | 1 => s(0, 1)
  | 2 => s(0, 1)
  | 3 => s(1, 2)
  | 4 => s(0, 2)

private def weight : Fin 5 → ℕ := Fin.val

/-- A self-loop is never selected: on the self-loop alone, a step selects nothing. -/
example : (boruvkaStep multi {0}).eval (LEQuery.keyOracle weight) = ∅ := by
  refine subset_empty.1 fun e he => ?_
  have hmsf := boruvkaStep_subset_msf multi {0} weight he
  have he0 : e = 0 := mem_singleton.1 (msf_subset weight hmsf)
  subst he0
  exact absurd hmsf (notMem_msf_of_isDiag weight (by decide))

/-- On the empty edge set a step selects nothing, against every oracle, and compares nothing. -/
example (oracle : {ι : Type} → LEQuery (Fin 5) ι → ι) :
    (boruvkaStep multi ∅).countQueries oracle = 0 :=
  Nat.le_zero.1 (countQueries_boruvkaStep_le multi ∅ oracle)

/-- Three steps on five edges make at most `30` comparisons, against every oracle. -/
example (oracle : {ι : Type} → LEQuery (Fin 5) ι → ι) :
    (boruvka multi univ 3).countQueries oracle ≤ 30 :=
  (countQueries_boruvka_le multi univ 3 oracle).trans (by simp)

/-- After one step, at most one of the three vertices is non-isolated, whatever the oracle
answers. -/
example (oracle : {ι : Type} → LEQuery (Fin 5) ι → ι) :
    let r := (boruvka multi univ 1).eval oracle
    #(support (Sym2.map r.proj ∘ multi) r.rest) ≤ 1 :=
  (card_support_boruvka_le multi univ 1 oracle rfl).trans
    ((Nat.div_le_div_right (c := 2 ^ 1) (card_le_univ _)).trans (by simp))

/-- One step against the weights: the contraction identity, and the result is a contraction. -/
example :
    let r := (boruvka multi univ 1).eval (LEQuery.keyOracle weight)
    msf multi weight univ = r.chosen ∪ msf (Sym2.map r.proj ∘ multi) weight r.rest :=
  msf_eq_union_boruvka multi univ 1 weight Fin.val_injective rfl

example (oracle : {ι : Type} → LEQuery (Fin 5) ι → ι) :
    ((boruvka multi univ 2).eval oracle).IsContraction multi univ :=
  isContraction_boruvka multi univ 2 oracle

end CslibFrontierTests.Algorithms.Query.MinimumSpanningForest.Boruvka
