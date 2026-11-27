/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Set.Finite.List

/-!
# Words of bounded length

Over a finite alphabet there are finitely many words of length at most `T`
(`List.finite_length_le`). `List.wordsLe Γ T` is the finite set of these words, the range of a
finite sum over words of bounded length.

## Main definitions

* `List.wordsLe`: the finite set of the words of length at most `T` over a finite alphabet.
-/

public section

namespace List

/-- The finite set of the words of length at most `T` over a finite alphabet `Γ`. -/
noncomputable def wordsLe (Γ : Type*) [Finite Γ] (T : ℕ) : Finset (List Γ) :=
  (List.finite_length_le Γ T).toFinset

@[simp] theorem mem_wordsLe {Γ : Type*} [Finite Γ] {T : ℕ} {w : List Γ} :
    w ∈ wordsLe Γ T ↔ w.length ≤ T := by
  simp [wordsLe]

end List
