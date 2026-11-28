/-
Copyright (c) 2026 Matthew Doty, Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Alexandre Rademaker
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.InductiveInference.Basic

/-!
# Identification in the limit from informant

An *informant* for a language `L ⊆ α` presents every string of `α`, each with its membership bit
for `L`; unlike a text it supplies negative data. Gold [Gold1967] contrasted the two: from
informant, every countable class of languages is identifiable, by *identification by
enumeration*: conjecture the first language in an enumeration of the class that agrees with all
data so far. Each wrong language earlier in the enumeration differs from the target at some
string, which the informant eventually presents with its bit, and the target itself never
disagrees. Together with Gold's theorem for texts
(`Cslib.MachineLearning.InductiveInference.not_identifiable_of_finite_subsets`) this shows that
the obstruction to learning from text is the lack of negative data, not the size of the class.

## Main definitions

* `Cslib.MachineLearning.InductiveInference.Informant`, `Informant.IsFor`: an ω-sequence of
  strings with bits, and the condition that it is a complete and correct presentation of `L`.
* `Cslib.MachineLearning.InductiveInference.IdentifiableFromInformant`: identification in the
  limit from informant.

## Main results

* `Cslib.MachineLearning.InductiveInference.identifiableFromInformant_of_countable`: every
  countable class of languages is identifiable from informant.

## Implementation notes

As for texts, learners are arbitrary functions conjecturing languages (the ineffective model).
Classically, informants present the words over a finite alphabet with their bits; here the
strings form an arbitrary type, and the result needs no countability of it (a type with an
informant is countable anyway, since an informant enumerates it).

## References

* [Gold1967]
-/

public section

open Filter Set Cslib

namespace Cslib.MachineLearning.InductiveInference

variable {α : Type*}

/-- An **informant** presents strings together with membership bits. -/
abbrev Informant (α : Type*) := ωSequence (α × Bool)

/-- `i` is an informant **for** `L`: every string is presented, and each with its correct
membership bit for `L`. -/
def Informant.IsFor (i : Informant α) (L : Set α) : Prop :=
  (∀ x, ∃ n, (i n).1 = x) ∧ ∀ n, ((i n).2 = true ↔ (i n).1 ∈ L)

/-- A learner from informant conjectures a language from each finite sequence of labelled
strings. -/
abbrev InformantLearner (α : Type*) := List (α × Bool) → Set α

/-- `φ` **identifies** `L` **in the limit from informant** when on every informant for `L` its
conjectures are eventually `L`. -/
def IdentifiesFromInformant (φ : InformantLearner α) (L : Set α) : Prop :=
  ∀ i : Informant α, i.IsFor L → ∀ᶠ n in atTop, φ (i.take n) = L

/-- A class of languages is **identifiable in the limit from informant** when one learner
identifies each of its languages from informant. -/
def IdentifiableFromInformant (𝓛 : Set (Set α)) : Prop :=
  ∃ φ : InformantLearner α, ∀ L ∈ 𝓛, IdentifiesFromInformant φ L

/-- Every countable class of languages is identifiable in the limit from informant [Gold1967]
(locator not verified), by identification by enumeration: conjecture the first language of an
enumeration of the class that agrees with every labelled string presented so far.

Relative to the classical formulation (the model in the source has not been checked against this
statement): learners are arbitrary functions conjecturing languages rather than names, strings
form an arbitrary type, and the class is any countable class, with no effective enumeration or
effective learner required. -/
theorem identifiableFromInformant_of_countable {𝓛 : Set (Set α)} (hc : 𝓛.Countable) :
    IdentifiableFromInformant 𝓛 := by
  classical
  rcases 𝓛.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ ↦ ∅, by simp⟩
  obtain ⟨A, rfl⟩ := hc.exists_eq_range hne
  let C : ℕ → List (α × Bool) → Prop := fun j σ ↦ ∀ p ∈ σ, (p.2 = true ↔ p.1 ∈ A j)
  refine ⟨fun σ ↦ if h : ∃ j, C j σ then A (Nat.find h) else ∅, ?_⟩
  rintro L ⟨z', rfl⟩ i ⟨hall, hbit⟩
  have hz : ∃ z, A z = A z' := ⟨z', rfl⟩
  have hAz : A (Nat.find hz) = A z' := Nat.find_spec hz
  have hC : ∀ n, C (Nat.find hz) (i.take n) := fun n p hp ↦ by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    rw [ωSequence.take_get, hAz]
    exact hbit k
  have h₂ : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (Nat.find hz), ¬C j (i.take n) := by
    refine (Finset.eventually_all _).mpr fun j hj ↦ ?_
    have hne : A j ≠ A z' := Nat.find_min hz (Finset.mem_range.mp hj)
    obtain ⟨x, hx⟩ : ∃ x, ¬(x ∈ A z' ↔ x ∈ A j) := by
      by_contra hcon
      exact hne (Set.ext fun x ↦ (not_not.mp (not_exists.mp hcon x)).symm)
    obtain ⟨k, hk⟩ := hall x
    filter_upwards [eventually_gt_atTop k] with n hn hCj
    have hmem : i k ∈ i.take n := List.mem_of_getElem? (ωSequence.getElem?_take hn)
    exact hx (hk ▸ (hbit k).symm.trans (hCj _ hmem))
  filter_upwards [h₂] with n hn
  have hex : ∃ j, C j (i.take n) := ⟨_, hC n⟩
  have hfind : Nat.find hex = Nat.find hz :=
    (Nat.find_eq_iff hex).mpr ⟨hC n, fun j hj ↦ hn j (Finset.mem_range.mpr hj)⟩
  simp only [hex, ↓reduceDIte, hfind, hAz]

end Cslib.MachineLearning.InductiveInference
