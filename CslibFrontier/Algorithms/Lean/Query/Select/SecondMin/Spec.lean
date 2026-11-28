/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.Sort.LEQuery
public import CslibFrontier.Foundations.Data.List.OrderStatistic

/-!
# Selecting the second smallest key by comparisons

The second smallest key has zero-based rank one. For a comparison lower bound it suffices
to require correctness on lists of at least two distinct keys, under every linear order on the
alphabet. The algorithm can issue any query in `LEQuery`, including queries about keys outside
its input.
-/

public section

namespace Cslib.Query

/-- Against every oracle implementing a linear order, the algorithm returns the key of rank one
on every list of at least two distinct keys. -/
structure IsSecondMinAlg {α : Type} (alg : List α → FreeM (LEQuery α) (Option α)) : Prop where
  /-- The result on a list of distinct keys is its second order statistic. -/
  correct : ∀ (r : α → α → Prop) [DecidableRel r] [IsLinearOrder α r]
    (oracle : {ι : Type} → LEQuery α ι → ι), (∀ a b, oracle (.le a b) = decide (r a b)) →
    ∀ xs : List α, xs.Nodup → 2 ≤ xs.length →
      ∃ y, (alg xs).eval oracle = some y ∧ xs.IsOrderStatistic r 1 y

end Cslib.Query
