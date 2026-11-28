/-
Copyright (c) 2026 Matthew Doty, Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Alexandre Rademaker
-/

import CslibFrontier.MachineLearning.InductiveInference.FormalLanguages

/-! Checks for identification in the limit: the finite subsets of `ℕ` together with `ℕ` itself are
not identifiable from text, while the finite subsets alone are, and so is a two-language class
whose languages are nested. Also: the empty language has a text (made of pauses), and the
regular languages over `Bool` are not identifiable. -/

namespace CslibFrontierTests.InductiveInference

open Set Cslib.MachineLearning.InductiveInference

/-- The finite languages over `ℕ` together with `ℕ` itself are not identifiable from text. -/
example : ¬Identifiable (insert (univ : Set ℕ) {L | L.Finite}) :=
  not_identifiable_of_finite_subsets (mem_insert _ _) infinite_univ
    fun _ _ hT => mem_insert_of_mem _ hT

/-- The finite languages over `ℕ` alone are identifiable. -/
example : Identifiable {L : Set ℕ | L.Finite} := identifiable_setOf_finite

/-- A nested pair `{0} ⊂ ℕ` is identifiable, since the class is finite. -/
example : Identifiable ({{0}, univ} : Set (Set ℕ)) := identifiable_of_finite (toFinite _)

/-- The empty language has a text. -/
example : ∃ t : Text ℕ, t.content = ∅ := Text.exists_content_eq ∅

/-- The regular languages over a binary alphabet are not identifiable. -/
example : ¬Identifiable {L : Set (List Bool) | Language.IsRegular (L : Language Bool)} :=
  not_identifiable_isRegular

/-- The context-free languages over a binary alphabet are not identifiable. -/
example : ¬Identifiable {L : Set (List Bool) | Language.IsContextFree (L : Language Bool)} :=
  not_identifiable_isContextFree

/-- Clients outside the defining module build and take apart `Identifiable`, and unfold
`Identifies` and `Text.content`. -/
example (𝓛 : Set (Set ℕ)) (φ : Learner ℕ) (h : ∀ L ∈ 𝓛, Identifies φ L) : Identifiable 𝓛 :=
  ⟨φ, h⟩

example (𝓛 : Set (Set ℕ)) (h : Identifiable 𝓛) (L : Set ℕ) (hL : L ∈ 𝓛) (t : Text ℕ)
    (ht : t.content = L) : ∃ φ : Learner ℕ, ∀ᶠ n in Filter.atTop, φ (t.take n) = L := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ, hφ L hL t ht⟩

example (t : Text ℕ) (x : ℕ) (h : t 3 = some x) : x ∈ t.content := ⟨3, h⟩

end CslibFrontierTests.InductiveInference
