/-
Copyright (c) 2026 Matthew Doty, Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Alexandre Rademaker
-/

import CslibFrontier.MachineLearning.InductiveInference.FormalLanguages
import CslibFrontier.MachineLearning.InductiveInference.Informant

/-! Checks for identification in the limit: the finite subsets of `ℕ` together with `ℕ` itself are
not identifiable from text, while the finite subsets alone are, and so is a two-language class
whose languages are nested. Also: the empty language has a text (made of pauses), the regular and
context-free languages over `Bool` are not identifiable, Gold's theorem follows from the
locking-sequence lemma, and every language over `ℕ` has an informant, from which the finite subsets
of `ℕ` together with `ℕ` are identifiable. -/

namespace CslibFrontierTests.InductiveInference

open Set Cslib Cslib.MachineLearning.InductiveInference

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

/-- Gold's theorem for the finite subsets of `ℕ` together with `ℕ`, rederived from the
locking-sequence lemma: a learner locked on `ℕ` by `σ` stays on `ℕ` along a text for the finite
language `content σ` that starts with `σ`. -/
example (φ : Learner ℕ) (h : ∀ L ∈ insert (univ : Set ℕ) {L | L.Finite}, Identifies φ L) :
    False := by
  obtain ⟨σ, -, hlock⟩ := (h univ (mem_insert _ _)).exists_isLockingSequence
  obtain ⟨t', ht'⟩ := Text.exists_content_eq (content σ)
  have htext : Text.content (σ ++ω t') = content σ := by
    rw [Text.content_append, ht', union_self]
  obtain ⟨n, hφn, hn⟩ := ((h _ (mem_insert_of_mem _ (content_finite σ)) _ htext).and
    (Filter.eventually_ge_atTop σ.length)).exists
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Text.take_append, hlock _ (subset_univ _)] at hφn
  exact infinite_univ (by rw [hφn]; exact content_finite σ)

/-- Every language over `ℕ` has an informant, so informant identification is not vacuous. -/
example (L : Set ℕ) : ∃ i : Informant ℕ, i.IsFor L := by
  classical
  exact ⟨⟨fun n ↦ (n, decide (n ∈ L))⟩, fun x ↦ ⟨x, rfl⟩, fun n ↦ by simp [ωSequence.get_fun]⟩

/-- From informant, the finite subsets of `ℕ` together with `ℕ` are identifiable, in contrast with
text. -/
example : IdentifiableFromInformant (insert (univ : Set ℕ) {L | L.Finite}) := by
  refine identifiableFromInformant_of_countable (Countable.insert _ ?_)
  refine (countable_ofPred_finite_subset (countable_univ (α := ℕ))).mono fun L hL ↦ ?_
  exact ⟨hL, subset_univ L⟩

end CslibFrontierTests.InductiveInference
