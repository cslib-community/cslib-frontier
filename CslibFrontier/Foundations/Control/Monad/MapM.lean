/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Lean core, beside `List.mapM_map` in `Init/Data/List/Monadic.lean`)

public import CslibFrontier.Init

/-!
# Mapping over the result of a monadic list traversal

Core `List.mapM_map` moves a function applied to the input list of `List.mapM` into the traversed
program. This module provides the companion for the output list, `List.map_mapM`: mapping a
function over the list that `l.mapM f` returns is traversing with `f` and applying that function
to each result. It is a general list lemma destined for Lean core.
-/

public section

namespace List

universe u v w

/-- Mapping `g` over the results of a traversal is traversing with `g` applied to each result. -/
theorem map_mapM {m : Type u → Type v} [Monad m] [LawfulMonad m] {α : Type w} {β γ : Type u}
    (f : α → m β) (g : β → γ) (l : List α) :
    map g <$> l.mapM f = l.mapM fun a => g <$> f a := by
  induction l with
  | nil => simp
  | cons a l ih => simp [← ih, map_bind, bind_map_left, Functor.map_map]

end List
