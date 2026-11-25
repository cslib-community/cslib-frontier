/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Fin/VecNotation.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Fin.VecNotation

/-!
# Composing a function after vector notation

Composing `f` after `![a₀, …, aₙ]` gives `![f a₀, …, f aₙ]`. `Matrix.comp_vecCons` is the
`vecCons` form of Mathlib's `Fin.comp_cons`, and `Matrix.comp_vecEmpty` handles the empty
vector, so that `simp only [Matrix.comp_vecCons, Matrix.comp_vecEmpty]` evaluates
`f ∘ ![a₀, …, aₙ]` for every literal length.
-/

public section

namespace Matrix

variable {α β : Type*}

/-- Composing `f` after `vecCons a v` applies `f` to the head and composes it after the tail. -/
theorem comp_vecCons {n : ℕ} (f : α → β) (a : α) (v : Fin n → α) :
    f ∘ vecCons a v = vecCons (f a) (f ∘ v) :=
  Fin.comp_cons f a v

/-- Composing a function after the empty vector gives the empty vector. -/
theorem comp_vecEmpty (f : α → β) : f ∘ ![] = ![] :=
  empty_eq _

end Matrix
