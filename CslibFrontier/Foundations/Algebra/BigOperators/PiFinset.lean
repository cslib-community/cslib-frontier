/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Fin/Tuple/Finset.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fin.Tuple.Finset

/-!
# Products over the tuples with entries in a finite set

A product over the tuples of `Fin (n + 1)` with all entries in a finite set `s` is a product over
the last entry and over the tuples of the first `n` entries (`Fin.prod_piFinset_const_snoc`).

## Main results

* `Fin.prod_piFinset_const_snoc`, `Fin.sum_piFinset_const_snoc`: splitting off the last entry.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the sums over the cuts of
the letters of the tapes in the evaluator of the proof of Theorem J.3 (p. 54); source module
`Nc.Grp.SumSeg`.
-/

public section

open Finset

namespace Fin

/-- A product over the tuples of `Fin (n + 1)` with entries in `s` is a product over the last
entry and over the tuples of the first `n` entries. -/
@[to_additive /-- A sum over the tuples of `Fin (n + 1)` with entries in `s` is a sum over the
last entry and over the tuples of the first `n` entries. -/]
theorem prod_piFinset_const_snoc {β M : Type*} [CommMonoid M] {n : ℕ} (s : Finset β)
    (f : (Fin (n + 1) → β) → M) :
    ∏ X ∈ Fintype.piFinset (fun _ : Fin (n + 1) => s), f X =
      ∏ Y ∈ s, ∏ X ∈ Fintype.piFinset (fun _ : Fin n => s), f (Fin.snoc X Y) := by
  classical
  have h := Finset.filter_piFinset_eq_map_snocEquiv (fun _ : Fin (n + 1) => s) fun _ => True
  simp only [filter_true] at h
  rw [h, prod_map, prod_product]
  rfl

end Fin
