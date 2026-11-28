/-
Copyright (c) 2026 Robert Hawkins, Matthew Doty, Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins, Matthew Doty, Alexandre Rademaker
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.OmegaSequence.Init
public import Mathlib.Data.Set.Countable
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
import Mathlib.Data.List.Infix

/-!
# Language identification in the limit

Gold's model of learning a language from positive data [Gold1967]. A learner sees the strings of
an unknown language one at a time, in any order, with repetitions and pauses, and after each
presentation conjectures a language. It identifies the language in the limit if on every such
presentation its conjectures are eventually the language itself. A class of languages over a
countable set of strings is identifiable exactly when it is countable and each of its languages
has a *telltale*, a finite subset that no member of the class properly inside the language
contains. Hence no class containing an infinite language and all its finite subsets is
identifiable (Gold's theorem), nor any class containing a strictly increasing chain of languages
and its union.

## Main definitions

* `Cslib.MachineLearning.InductiveInference.Text`: an ω-sequence of presentations, `none` being
  a pause; `Text.content` is the set of strings it presents.
* `Cslib.MachineLearning.InductiveInference.Learner`: a map from finite sequences of
  presentations to conjectured languages.
* `Cslib.MachineLearning.InductiveInference.Identifies`,
  `Cslib.MachineLearning.InductiveInference.Identifiable`: identification in the limit from text,
  of one language and of a class.
* `Cslib.MachineLearning.InductiveInference.IsTelltale`: a finite telltale of a language within a
  class.

## Main results

* `Cslib.MachineLearning.InductiveInference.identifiable_iff`: over a countable set of strings, a
  class is identifiable from text iff it is countable and each of its languages has a telltale.
* `Cslib.MachineLearning.InductiveInference.identifiable_of_finite`: every finite class is
  identifiable.
* `Cslib.MachineLearning.InductiveInference.identifiable_setOf_finite`: the class of all finite
  languages is identifiable.
* `Cslib.MachineLearning.InductiveInference.not_identifiable_of_finite_subsets`: Gold's theorem.
* `Cslib.MachineLearning.InductiveInference.not_identifiable_of_strictMono_iUnion`: a strictly
  increasing chain together with its union is not identifiable.

## Implementation notes

The model is the ineffective one: a learner is any function on finite sequences, computable or
not, and conjectures a language rather than a name (grammar index) for one; the two come to the
same when effectiveness is not required. Gold's learners output names [Gold1967, §2];
Angluin's characterization [Angluin1980] concerns effective learners of indexed families of
recursive languages, which additionally need the telltales to be uniformly enumerable. Neither the
effective model nor Angluin's theorem is formalized here; `identifiable_iff` is the ineffective
counterpart of Angluin's condition. A pause lets the empty language have a text; on nonempty
languages pauses change nothing, since a learner can treat a pause as a repetition of the previous
string. The strings form an arbitrary type, countable where texts must exist; the words over an
alphabet are one instance.

This file is a port of the module `Linglib.Core.Computability.InductiveInference` of Linglib
(<https://github.com/linglib-community/linglib>, commit `64f3d2c6df`, Apache-2.0), by Robert
Hawkins. The definitions, statements and proof strategies are his. The port moves the
development into the `Cslib.MachineLearning.InductiveInference` namespace and replaces Mathlib's
`Stream'` by CSLib's `ωSequence`, adapting the proofs about finite prefixes of texts.

## References

* [Gold1967]
* [Angluin1980]
-/

public section

open Filter Set Cslib

namespace Cslib.MachineLearning.InductiveInference

variable {α : Type*}

/-- A **text** presents strings one at a time, `none` being a pause in which nothing is
presented. -/
abbrev Text (α : Type*) := ωSequence (Option α)

/-- The strings occurring in a finite sequence of presentations. -/
def content (σ : List (Option α)) : Set α := {x | some x ∈ σ}

/-- The strings occurring in a text. A text **for** `L` is one whose content is `L`. -/
def Text.content (t : Text α) : Set α := {x | ∃ n, t n = some x}

/-- A learner conjectures a language from each finite sequence of presentations. -/
abbrev Learner (α : Type*) := List (Option α) → Set α

/-- `φ` **identifies** `L` **in the limit** when on every text for `L` its conjectures are
eventually `L`. -/
def Identifies (φ : Learner α) (L : Set α) : Prop :=
  ∀ t : Text α, t.content = L → ∀ᶠ n in atTop, φ (t.take n) = L

/-- A class of languages is **identifiable in the limit** (from text) when one learner identifies
each of its languages. -/
def Identifiable (𝓛 : Set (Set α)) : Prop :=
  ∃ φ : Learner α, ∀ L ∈ 𝓛, Identifies φ L

/-- `T` is a **telltale** of `L` in `𝓛`: a finite subset of `L` that no language of `𝓛` properly
inside `L` contains. Once `T` has been presented, conjecturing `L` cannot overgeneralize. -/
def IsTelltale (𝓛 : Set (Set α)) (L T : Set α) : Prop :=
  T.Finite ∧ T ⊆ L ∧ ∀ L' ∈ 𝓛, T ⊆ L' → ¬L' ⊂ L

/-! ### Content -/

theorem content_finite (σ : List (Option α)) : (content σ).Finite :=
  (σ.finite_toSet.preimage (Option.some_injective α).injOn).subset fun _ h ↦ h

@[simp] theorem mem_content {σ : List (Option α)} {x : α} : x ∈ content σ ↔ some x ∈ σ := Iff.rfl

@[simp] theorem content_nil : content ([] : List (Option α)) = ∅ := by simp [content]

@[simp] theorem content_append (σ τ : List (Option α)) :
    content (σ ++ τ) = content σ ∪ content τ := by
  ext; simp [content]

namespace Text

@[simp] theorem mem_content {t : Text α} {x : α} : x ∈ t.content ↔ ∃ n, t n = some x := Iff.rfl

theorem content_take_subset (t : Text α) (n : ℕ) :
    InductiveInference.content (t.take n) ⊆ t.content := fun x hx ↦ by
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem (InductiveInference.mem_content.mp hx)
  exact ⟨k, by rw [← hkx, ωSequence.take_get]⟩

/-- Every finite part of a text has been presented after finitely many steps. -/
theorem eventually_subset_content_take {t : Text α} {T : Set α} (hT : T.Finite)
    (hsub : T ⊆ t.content) : ∀ᶠ n in atTop, T ⊆ InductiveInference.content (t.take n) := by
  simp only [Set.subset_def]
  refine (eventually_all_finite hT).mpr fun x hx ↦ ?_
  obtain ⟨k, hk⟩ := hsub hx
  filter_upwards [eventually_gt_atTop k] with n hn
  have := ωSequence.getElem?_take (s := t) hn
  rw [hk] at this
  exact InductiveInference.mem_content.mpr (List.mem_of_getElem? this)

theorem content_append (σ : List (Option α)) (t : Text α) :
    Text.content (σ ++ω t) = InductiveInference.content σ ∪ t.content := by
  ext x
  simp only [mem_content, Set.mem_union, InductiveInference.mem_content]
  constructor
  · rintro ⟨n, hn⟩
    rcases lt_or_ge n σ.length with h | h
    · rw [ωSequence.get_append_left _ _ _ h] at hn
      exact .inl (hn ▸ List.getElem_mem h)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
      exact .inr ⟨m, by rwa [ωSequence.get_append_right] at hn⟩
  · rintro (h | ⟨m, hm⟩)
    · obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem h
      exact ⟨k, by rw [ωSequence.get_append_left _ _ _ hk, hkx]⟩
    · exact ⟨σ.length + m, by rw [ωSequence.get_append_right, hm]⟩

theorem take_append (σ : List (Option α)) (t : Text α) (m : ℕ) :
    (σ ++ω t).take (σ.length + m) = σ ++ t.take m :=
  (ωSequence.append_take _ _ _).symm

/-- Every language over a countable set of strings has a text. -/
theorem exists_content_eq [Countable α] (L : Set α) : ∃ t : Text α, t.content = L := by
  rcases L.eq_empty_or_nonempty with rfl | hL
  · exact ⟨⟨fun _ ↦ none⟩, eq_empty_of_forall_notMem fun x ⟨n, hn⟩ ↦ by
      simp [ωSequence.get_fun] at hn⟩
  · obtain ⟨g, rfl⟩ := L.to_countable.exists_eq_range hL
    refine ⟨⟨fun n ↦ some (g n)⟩, Set.ext fun x ↦ ⟨fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩, fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩⟩⟩
    · simpa [ωSequence.get_fun] using hn
    · simp [ωSequence.get_fun, hn]

/-- A prefix-increasing chain of finite sequences of unbounded length has a limit text. -/
private theorem exists_take_eq (σ : ℕ → List (Option α)) (hpre : ∀ n, σ n <+: σ (n + 1))
    (hlen : ∀ n, n ≤ (σ n).length) : ∃ t : Text α, ∀ n, t.take (σ n).length = σ n := by
  have hmono : ∀ {a b}, a ≤ b → σ a <+: σ b := fun {a b} hab ↦ by
    induction b, hab using Nat.le_induction with
    | base => exact List.prefix_rfl
    | succ b _ ih => exact ih.trans (hpre b)
  refine ⟨⟨fun m ↦ (σ (m + 1)).getD m none⟩, fun n ↦ ?_⟩
  refine List.ext_getElem (ωSequence.length_take _ _) fun m h₁ h₂ ↦ ?_
  have hm : m < (σ (m + 1)).length := hlen (m + 1)
  have key : (σ (m + 1))[m] = (σ n)[m] := by
    rcases le_total n (m + 1) with h | h
    · exact ((hmono h).getElem h₂).symm
    · exact (hmono h).getElem hm
  rw [ωSequence.take_get, ← key, ωSequence.get_fun, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hm, Option.getD_some]

/-- If a property of finite sequences can always be reached by extending within `L`, some text for
`L` meets it infinitely often: the text the proofs of Gold and of Angluin build. -/
theorem exists_frequently {L : Set α} {P : List (Option α) → Prop} {e : Text α}
    (he : e.content = L)
    (hP : ∀ σ, InductiveInference.content σ ⊆ L →
      ∃ τ, InductiveInference.content τ ⊆ L ∧ P (σ ++ τ)) :
    ∃ t : Text α, t.content = L ∧ ∃ᶠ n in atTop, P (t.take n) := by
  have hext : ∀ (n : ℕ) (σ : {σ : List (Option α) // InductiveInference.content σ ⊆ L}),
      ∃ σ' : {σ : List (Option α) // InductiveInference.content σ ⊆ L},
        σ.1 ++ [e n] <+: σ'.1 ∧ P σ'.1 := fun n ⟨σ, hσ⟩ ↦ by
    have hstep : InductiveInference.content (σ ++ [e n]) ⊆ L := by
      rw [InductiveInference.content_append]
      refine union_subset hσ fun x hx ↦ ?_
      have : e n = some x := by simpa [eq_comm] using hx
      exact he ▸ ⟨n, this⟩
    obtain ⟨τ, hτ, hPτ⟩ := hP _ hstep
    exact ⟨⟨_, by rw [InductiveInference.content_append]; exact union_subset hstep hτ⟩,
      List.prefix_append _ _, hPτ⟩
  choose next hnext hPnext using hext
  let σ : ℕ → {σ : List (Option α) // InductiveInference.content σ ⊆ L} :=
    fun n ↦ Nat.rec ⟨[], by simp⟩ (fun k s ↦ next k s) n
  have hstep : ∀ n, (σ n).1 ++ [e n] <+: (σ (n + 1)).1 := fun n ↦ hnext n (σ n)
  have hpre : ∀ n, (σ n).1 <+: (σ (n + 1)).1 := fun n ↦
    (List.prefix_append _ _).trans (hstep n)
  have hlen : ∀ n, n ≤ (σ n).1.length := fun n ↦ by
    induction n with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have := (hstep k).length_le
      simp only [List.length_append, List.length_singleton] at this
      omega
  obtain ⟨t, ht⟩ := exists_take_eq (fun n ↦ (σ n).1) hpre hlen
  refine ⟨t, Set.Subset.antisymm (fun x ⟨k, hk⟩ ↦ ?_) fun x hx ↦ ?_, ?_⟩
  · have hk' : k < (σ (k + 1)).1.length := hlen (k + 1)
    refine (σ (k + 1)).2 ?_
    have := ωSequence.getElem?_take (s := t) hk'
    rw [ht (k + 1), hk] at this
    exact InductiveInference.mem_content.mpr (List.mem_of_getElem? this)
  · rw [← he] at hx
    obtain ⟨n, hn⟩ := hx
    have hmem : some x ∈ (σ (n + 1)).1 := (hstep n).subset (by simp [hn])
    rw [← ht (n + 1)] at hmem
    exact content_take_subset t _ (InductiveInference.mem_content.mpr hmem)
  · refine frequently_atTop.mpr fun N ↦ ⟨(σ (N + 1)).1.length, (by have := hlen (N + 1); omega), ?_⟩
    rw [ht (N + 1)]
    exact hPnext N (σ N)

end Text

/-! ### The characterization -/

theorem Identifiable.mono {𝓛 𝓜 : Set (Set α)} (h : 𝓛 ⊆ 𝓜) (hm : Identifiable 𝓜) :
    Identifiable 𝓛 :=
  hm.imp fun _ hφ L hL ↦ hφ L (h hL)

/-- A learner identifying each language of `𝓛` gives each of them a telltale, the content of a
finite sequence after which it can no longer be moved off `L`. -/
theorem exists_isTelltale [Countable α] {𝓛 : Set (Set α)} {φ : Learner α}
    (hφ : ∀ L ∈ 𝓛, Identifies φ L) {L : Set α} (hL : L ∈ 𝓛) : ∃ T, IsTelltale 𝓛 L T := by
  by_contra hno
  have hno' : ∀ T : Set α, T.Finite → T ⊆ L → ∃ L' ∈ 𝓛, T ⊆ L' ∧ L' ⊂ L := fun T hT hTL ↦ by
    by_contra h
    exact hno ⟨T, hT, hTL, fun L' hL' hTL' hss ↦ h ⟨L', hL', hTL', hss⟩⟩
  obtain ⟨e, he⟩ := Text.exists_content_eq L
  obtain ⟨t, ht, hfreq⟩ := Text.exists_frequently (P := fun σ ↦ φ σ ≠ L) he fun σ hσ ↦ by
    obtain ⟨L', hL', hσL', hssub⟩ := hno' _ (content_finite σ) hσ
    obtain ⟨t', ht'⟩ := Text.exists_content_eq L'
    have htext : Text.content (σ ++ω t') = L' := by
      rw [Text.content_append, ht', union_eq_right.mpr hσL']
    obtain ⟨n, hφn, hn⟩ := ((hφ L' hL' _ htext).and (eventually_ge_atTop σ.length)).exists
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine ⟨t'.take m, (Text.content_take_subset t' m).trans (ht' ▸ hssub.subset), ?_⟩
    rw [← Text.take_append, hφn]
    exact hssub.ne
  exact hfreq (hφ L hL t ht |>.mono fun _ h hne ↦ hne h)

/-- A countable class whose languages have telltales is identifiable, by conjecturing the first
language in an enumeration whose telltale has appeared and which contains the data. -/
theorem identifiable_of_isTelltale {𝓛 : Set (Set α)} (hc : 𝓛.Countable)
    (hT : ∀ L ∈ 𝓛, ∃ T, IsTelltale 𝓛 L T) : Identifiable 𝓛 := by
  classical
  rcases 𝓛.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ ↦ ∅, by simp⟩
  obtain ⟨A, rfl⟩ := hc.exists_eq_range hne
  choose T hT using fun i ↦ hT (A i) (mem_range_self i)
  refine ⟨fun σ ↦ if h : ∃ i, T i ⊆ content σ ∧ content σ ⊆ A i then A (Nat.find h) else ∅, ?_⟩
  rintro L ⟨z', rfl⟩ t ht
  have hz : ∃ z, A z = A z' := ⟨z', rfl⟩
  have hAz : A (Nat.find hz) = A z' := Nat.find_spec hz
  have h₁ : ∀ᶠ n in atTop, T (Nat.find hz) ⊆ content (t.take n) :=
    Text.eventually_subset_content_take (hT _).1
      (((hT _).2.1.trans hAz.subset).trans ht.symm.subset)
  have h₂ : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (Nat.find hz),
      ¬(T i ⊆ content (t.take n) ∧ content (t.take n) ⊆ A i) := by
    refine (Finset.eventually_all _).mpr fun i hi ↦ ?_
    by_cases hsub : A z' ⊆ A i
    · refine .of_forall fun n ⟨hTi, _⟩ ↦ (hT i).2.2 _ (mem_range_self z')
        (hTi.trans ((t.content_take_subset n).trans ht.subset))
        (hsub.ssubset_of_ne (Ne.symm (Nat.find_min hz (Finset.mem_range.mp hi))))
    · obtain ⟨x, hx, hxi⟩ := not_subset.mp hsub
      filter_upwards [Text.eventually_subset_content_take (finite_singleton x)
        (singleton_subset_iff.mpr (ht ▸ hx))] with n hn ⟨_, hsub'⟩
      exact hxi (hsub' (hn rfl))
  filter_upwards [h₁, h₂] with n hn₁ hn₂
  have hcsub : content (t.take n) ⊆ A (Nat.find hz) := by
    rw [hAz, ← ht]; exact t.content_take_subset n
  have hex : ∃ i, T i ⊆ content (t.take n) ∧ content (t.take n) ⊆ A i := ⟨_, hn₁, hcsub⟩
  have hfind : Nat.find hex = Nat.find hz :=
    (Nat.find_eq_iff hex).mpr ⟨⟨hn₁, hcsub⟩, fun i hi ↦ hn₂ i (Finset.mem_range.mpr hi)⟩
  simp only [hex, ↓reduceDIte, hfind, hAz]

/-- A class of languages over a countable set of strings is identifiable in the limit from text
exactly when it is countable and each of its languages has a telltale. This is the ineffective
counterpart of Angluin's characterization [Angluin1980]: Angluin
treats effective learners of indexed families and needs the telltales to be uniformly
enumerable, which this model does not. Countability reflects Gold's observation that a learner
has only countably many conjectures. -/
theorem identifiable_iff [Countable α] {𝓛 : Set (Set α)} :
    Identifiable 𝓛 ↔ 𝓛.Countable ∧ ∀ L ∈ 𝓛, ∃ T, IsTelltale 𝓛 L T :=
  ⟨fun ⟨φ, hφ⟩ ↦ ⟨(countable_range φ).mono fun L hL ↦ by
      obtain ⟨t, ht⟩ := Text.exists_content_eq L
      obtain ⟨n, hn⟩ := (hφ L hL t ht).exists
      exact ⟨_, hn⟩, fun _ hL ↦ exists_isTelltale hφ hL⟩,
    fun h ↦ identifiable_of_isTelltale h.1 h.2⟩

/-- Every finite class is identifiable. -/
theorem identifiable_of_finite {𝓛 : Set (Set α)} (h : 𝓛.Finite) : Identifiable 𝓛 := by
  refine identifiable_of_isTelltale h.countable fun L _ ↦ ?_
  have hx : ∀ L' : {L' // L' ∈ 𝓛 ∧ L' ⊂ L}, ∃ x, x ∈ L ∧ x ∉ L'.1 :=
    fun L' ↦ exists_of_ssubset L'.2.2
  choose x hxL hxL' using hx
  have : Finite {L' // L' ∈ 𝓛 ∧ L' ⊂ L} :=
    (h.subset fun _ hL' ↦ hL'.1 : {L' | L' ∈ 𝓛 ∧ L' ⊂ L}.Finite).to_subtype
  exact ⟨range x, finite_range x, range_subset_iff.mpr hxL,
    fun L' hL' hT hss ↦ hxL' ⟨L', hL', hss⟩ (hT ⟨_, rfl⟩)⟩

/-- The class of finite languages is identifiable from text, by conjecturing the strings presented
so far [Gold1967, §8, p. 460]. -/
theorem identifiable_setOf_finite : Identifiable {L : Set α | L.Finite} :=
  ⟨content, fun _ hL t ht => by
    filter_upwards [Text.eventually_subset_content_take hL ht.symm.subset] with n hn
    exact (ht ▸ t.content_take_subset n).antisymm hn⟩

/-- **Gold's theorem** [Gold1967, §8, "Language identifiability", p. 460]: a class containing an
infinite language and all its finite subsets is not identifiable in the limit from text. Gold
states that, from arbitrary text, the class of finite languages is ineffectively identifiable "but
every proper superclass is not"; this is the case of a class containing every finite language and
an infinite one. His construction (§9, pp. 460–461) uses only the finite subsets of the one
infinite language, which is the hypothesis here.

Deviations from the source: learners conjecture languages rather than names (§2, pp. 450–451),
which loses nothing for ineffective learners; texts may contain pauses, which Gold's texts (§2,
p. 450) do not, and which impose no extra requirement on nonempty languages, since a learner can
treat a pause as a repetition; and strings form an arbitrary countable type rather than the words
over a finite alphabet. -/
theorem not_identifiable_of_finite_subsets [Countable α] {𝓛 : Set (Set α)} {L : Set α}
    (hL : L ∈ 𝓛) (hinf : L.Infinite) (hfin : ∀ T ⊆ L, T.Finite → T ∈ 𝓛) : ¬Identifiable 𝓛 :=
  fun h ↦ by
    obtain ⟨T, hT, hTL, hno⟩ := (identifiable_iff.mp h).2 L hL
    exact hno T (hfin T hTL hT) subset_rfl (hTL.ssubset_of_ne fun e ↦ hinf (e ▸ hT))

/-- A class containing a strictly increasing chain of languages and its union is not identifiable
from text, since the finite telltale of the union would already lie in a member of the chain. -/
theorem not_identifiable_of_strictMono_iUnion [Countable α] {𝓛 : Set (Set α)} {A : ℕ → Set α}
    (hA : StrictMono A) (hmem : ∀ n, A n ∈ 𝓛) (hU : ⋃ n, A n ∈ 𝓛) : ¬Identifiable 𝓛 := fun h ↦ by
  obtain ⟨T, hT, hTU, hno⟩ := (identifiable_iff.mp h).2 _ hU
  have hev : ∀ᶠ n in atTop, ∀ x ∈ T, x ∈ A n := (eventually_all_finite hT).mpr fun x hx ↦ by
    obtain ⟨m, hm⟩ := mem_iUnion.mp (hTU hx)
    filter_upwards [eventually_ge_atTop m] with n hn using hA.monotone hn hm
  obtain ⟨n, hn⟩ := hev.exists
  exact hno _ (hmem n) hn ((hA (Nat.lt_succ_self n)).trans_subset (subset_iUnion A _))

end Cslib.MachineLearning.InductiveInference
