/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import all Init.Data.List.Control

/-!
# Step equations for monadic list search

Core `List.findM? p xs` runs the effectful test `p` on each element of `xs` from left to right and
returns the first element for which `p` returns `true`, or `none`. Core defines `List.findM?`
without exposing its body and has no `nil` or `cons` equations for a general monad, so this module
imports `Init.Data.List.Control` with `import all`, as
`CslibFrontier.Foundations.Control.Monad.FilterM` does. Both equations are general list lemmas
destined for Lean core or Batteries.

## Main results

* `List.findM?_nil`: `findM?` on the empty list returns `pure none`.
* `List.findM?_cons`: one-step unfolding of `findM?` on a cons cell.
-/

public section

namespace List

universe u

/-- `findM?` finds nothing in the empty list. -/
@[simp] theorem findM?_nil {m : Type → Type u} [Monad m] {α : Type} (p : α → m Bool) :
    ([] : List α).findM? p = pure none :=
  (rfl)

/-- One step of `findM?`: test the head, and search the tail only when the test fails. -/
theorem findM?_cons {m : Type → Type u} [Monad m] {α : Type} (p : α → m Bool) (a : α)
    (as : List α) :
    (a :: as).findM? p = p a >>= fun b => if b then pure (some a) else as.findM? p := by
  simp only [findM?]
  congr 1
  funext b
  cases b <;> rfl

end List
