/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Fintype/Sum.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Sum

/-!
# Counting with a property on a sum type

The elements of `α ⊕ β` with a property are those of `α` with it plus those of `β` with it
(`Sum.card_filter_univ`), the analogue for sum types of Mathlib's `Fin.card_filter_univ_succ`.
-/

public section

namespace Sum

open Finset

/-- Counting the elements of a sum type with a property splits over the two summands. -/
theorem card_filter_univ {α β : Type*} [Fintype α] [Fintype β] (p : α ⊕ β → Prop)
    [DecidablePred p] : #{x | p x} = #{a | p (inl a)} + #{b | p (inr b)} := by
  rw [← Fintype.card_subtype, Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum,
    Fintype.card_subtype, Fintype.card_subtype]

end Sum
