/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, unions indexed by `Fin 2`)

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic

/-!
# Unions indexed by `Fin 2`

A union over the two elements of `Fin 2` is the union of its two terms.

## Main results

* `Finset.biUnion_univ_fin_two`: `univ.biUnion f = f 0 ∪ f 1` for `f : Fin 2 → Finset α`.
-/

public section

namespace Finset

/-- A union over the two elements of `Fin 2` is the union of its two terms. -/
theorem biUnion_univ_fin_two {α : Type*} [DecidableEq α] (f : Fin 2 → Finset α) :
    (univ : Finset (Fin 2)).biUnion f = f 0 ∪ f 1 := by
  ext x
  simp only [mem_biUnion, mem_univ, true_and, Fin.exists_fin_two, mem_union]

end Finset
