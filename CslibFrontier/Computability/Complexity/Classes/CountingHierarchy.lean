/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PP.Oracle.Closure
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Function
import CslibFrontier.Computability.Complexity.Classes.PP.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime

/-!
# Decision and function levels of the counting hierarchy

`CountingLevel a enc` is C_a P and `CountingFunction a input output` is F_a. Each membership
witness uses one fixed language oracle on raw words and one uniform program. Function output
length is polynomially bounded by the strict oracle machine certificate. Successor decision
levels use the existing fixed-length relativized majority **verifier** characterization; this
module does not claim equivalence with probabilistic oracle machines.

Tagged unions combine a fixed finite collection of oracle languages at the same level. Thus
function composition may be adaptive without increasing the level. This does not collapse
adaptive PP access to PP.

## Main definitions

* `Cslib.Complexity.CountingLevel`: decision levels, starting with P.
* `Cslib.Complexity.CountingFunction`: polynomial-time functions relative to one decision-level
  oracle, with explicit input and output encodings.

## References

* [OpenAI, *Existential--universal real sentences in the counting hierarchy*]
  [OpenAI2026CountingHierarchy], Section 2, uniformity and counting. These are the proposed
  hierarchy operations; the real-feasibility applications are outside this module.
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 17.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Counting-hierarchy decision levels. Every successor witness uses one raw-word oracle from
the preceding level and a uniform strict polynomial-time majority verifier. -/
@[expose] def CountingLevel : (a : ℕ) → {α : Type} → (α ↪ List Bool) → Set (Set α)
  | 0, _, enc => P enc
  | a + 1, _, enc => {L | ∃ A ∈ CountingLevel a encBits, L ∈ PPWithOracle A enc}

/-- Function level F_a, using one fixed oracle in C_a P. Encoded output length is bounded by
the program's strict certificate; the witness cannot depend on the input. -/
@[expose] def CountingFunction {α β : Type} (a : ℕ) (input : α ↪ List Bool)
    (output : β ↪ List Bool) : Set (α → β) :=
  {f | ∃ A ∈ CountingLevel a encBits, ComputableInPolyTimeWithOracle A f input output}

variable {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool}
  {output : γ ↪ List Bool} {a b : ℕ}

/-- The zeroth decision level is P. -/
@[simp] theorem CountingLevel_zero : CountingLevel 0 input = P input := rfl

/-- The first decision level is ordinary PP: a polynomial-time oracle can be eliminated. -/
@[simp] theorem CountingLevel_one : CountingLevel 1 input = PP input :=
  Set.Subset.antisymm (fun _ ⟨_, hA, hL⟩ => PPWithOracle_eq_PP hA input ▸ hL)
    fun _ hL => ⟨∅, empty_mem_P, PP_subset_PPWithOracle ∅ input hL⟩

/-- The zeroth function level is ordinary polynomial-time computation. -/
@[simp] theorem mem_CountingFunction_zero {f : α → β} :
    f ∈ CountingFunction 0 input middle ↔ ComputableInPolyTime f input middle :=
  ⟨fun ⟨_, hA, hf⟩ => hf.computableInPolyTime hA,
    fun hf => ⟨∅, empty_mem_P, hf.computableInPolyTimeWithOracle ∅⟩⟩

/-- Every decision level contains P. -/
theorem P_subset_CountingLevel (a : ℕ) : P input ⊆ CountingLevel a input := by
  induction a generalizing α with
  | zero => exact Set.Subset.rfl
  | succ _ ih =>
    exact fun _ hL => ⟨∅, ih empty_mem_P, PP_subset_PPWithOracle ∅ input (P_subset_PP hL)⟩

/-- The decision levels are increasing. -/
theorem CountingLevel_subset_succ (a : ℕ) :
    CountingLevel a input ⊆ CountingLevel (a + 1) input := by
  induction a generalizing α with
  | zero => exact P_subset_CountingLevel 1
  | succ _ ih => exact fun _ ⟨A, hA, hL⟩ => ⟨A, ih hA, hL⟩

/-- Monotonicity in the level index. -/
theorem CountingLevel_mono (hab : a ≤ b) : CountingLevel a input ⊆ CountingLevel b input := by
  induction hab with
  | refl => exact Set.Subset.refl _
  | step _ ih => exact ih.trans (CountingLevel_subset_succ _)

/-- Polynomial-time many-one reductions preserve every decision level. -/
theorem PolyTimeReducible.mem_CountingLevel {L : Set α} {M : Set β}
    (h : PolyTimeReducible input middle L M) (hM : M ∈ CountingLevel a middle) :
    L ∈ CountingLevel a input := by
  cases a with
  | zero => exact h.mem_P hM
  | succ _ =>
    obtain ⟨A, hA, hM⟩ := hM
    exact ⟨A, hA, h.mem_PPWithOracle hM⟩

/-- Prefixing a false tag reduces the first oracle to its tagged union. -/
theorem reduces_taggedUnion_left (A B : Set (List Bool)) :
    PolyTimeReducible encBits encBits A (taggedUnion A B) :=
  ⟨fun w => false :: w, by fun_prop, fun _ => Iff.rfl⟩

/-- Prefixing a true tag reduces the second oracle to its tagged union. -/
theorem reduces_taggedUnion_right (A B : Set (List Bool)) :
    PolyTimeReducible encBits encBits B (taggedUnion A B) :=
  ⟨fun w => true :: w, by fun_prop, fun _ => Iff.rfl⟩

/-- A fixed pair of same-level languages can share one tagged oracle. Repeating this theorem
combines every fixed finite family, without an input-dependent oracle depth. -/
theorem taggedUnion_mem_CountingLevel {A B : Set (List Bool)}
    (hA : A ∈ CountingLevel a encBits) (hB : B ∈ CountingLevel a encBits) :
    taggedUnion A B ∈ CountingLevel a encBits := by
  induction a generalizing A B with
  | zero =>
    obtain ⟨f, hf, hA⟩ := hA
    obtain ⟨g, hg, hB⟩ := hB
    refine ⟨fun w => if w.headD false then g w.tail else f w.tail,
      ComputableInPolyTime.ite'
        (by fun_prop : ComputableInPolyTime (fun w : List Bool => w.headD false) encBits encBool)
        (hg.comp (by fun_prop)) (hf.comp (by fun_prop)),
      fun w => ?_⟩
    change (if w.headD false then w.tail ∈ B else w.tail ∈ A) ↔
      (if w.headD false then g w.tail else f w.tail) = true
    cases ht : w.headD false
    · simpa only [ht, Bool.false_eq_true, ↓reduceIte] using hA w.tail
    · simpa only [ht, ↓reduceIte] using hB w.tail
  | succ _ ih =>
    obtain ⟨O₀, hO₀, hA⟩ := hA
    obtain ⟨O₁, hO₁, hB⟩ := hB
    exact ⟨taggedUnion O₀ O₁, ih hO₀ hO₁,
      taggedUnion_mem_PPWithOracle
        ((reduces_taggedUnion_left O₀ O₁).PPWithOracle_subset encBits hA)
        ((reduces_taggedUnion_right O₀ O₁).PPWithOracle_subset encBits hB)⟩

/-- A fixed list of languages, joined by successive leading tags. The empty list gives the
empty language; a false tag selects the head and a true tag continues through the list. -/
@[expose] def taggedUnions (languages : List (Set (List Bool))) : Set (List Bool) :=
  languages.foldr taggedUnion ∅

/-- Every fixed finite tagged union stays at the same decision level. -/
theorem taggedUnions_mem_CountingLevel {languages : List (Set (List Bool))}
    (h : ∀ L ∈ languages, L ∈ CountingLevel a encBits) :
    taggedUnions languages ∈ CountingLevel a encBits := by
  induction languages with
  | nil => exact P_subset_CountingLevel a empty_mem_P
  | cons L languages ih =>
    exact taggedUnion_mem_CountingLevel (h L (by simp))
      (ih fun M hM => h M (by simp only [List.mem_cons]; exact Or.inr hM))

/-- Each component of a fixed finite union reduces to the combined oracle by a fixed tag word. -/
theorem reduces_taggedUnions {L : Set (List Bool)} {languages : List (Set (List Bool))}
    (hL : L ∈ languages) : PolyTimeReducible encBits encBits L (taggedUnions languages) := by
  induction languages with
  | nil => simp only [List.not_mem_nil] at hL
  | cons M languages ih =>
    rcases List.mem_cons.mp hL with rfl | hL
    · exact reduces_taggedUnion_left L (taggedUnions languages)
    · exact (ih hL).trans (reduces_taggedUnion_right M (taggedUnions languages))

namespace CountingFunction

/-- A fixed finite family of same-level functions has one common language oracle, independent
of the input and selected member. Its functions retain their strict uniform program witnesses. -/
theorem exists_common_oracle {ι : Type} [Finite ι] {f : ι → α → β}
    (hf : ∀ i, f i ∈ CountingFunction a input middle) :
    ∃ A ∈ CountingLevel a encBits,
      ∀ i, ComputableInPolyTimeWithOracle A (f i) input middle := by
  classical
  let := Fintype.ofFinite ι
  choose oracle hlevel hcert using hf
  refine ⟨taggedUnions (Finset.univ.toList.map oracle),
    taggedUnions_mem_CountingLevel (List.forall_mem_map.2 fun i _ => hlevel i),
    fun i => (hcert i).of_polyTimeReducible
      (reduces_taggedUnions (List.mem_map.mpr ⟨i, by simp, rfl⟩))⟩

/-- Ordinary polynomial-time functions belong to every function level. -/
theorem of_polyTime {f : α → β} (hf : ComputableInPolyTime f input middle) :
    f ∈ CountingFunction a input middle :=
  ⟨∅, P_subset_CountingLevel a empty_mem_P, hf.computableInPolyTimeWithOracle ∅⟩

/-- Increasing the oracle level preserves a function certificate. -/
theorem mono (hab : a ≤ b) {f : α → β} (hf : f ∈ CountingFunction a input middle) :
    f ∈ CountingFunction b input middle :=
  let ⟨A, hA, hf⟩ := hf
  ⟨A, CountingLevel_mono hab hA, hf⟩

/-- Polynomial output length follows from function-level membership. -/
theorem polyBounded_length {f : α → β} (hf : f ∈ CountingFunction a input middle) :
    PolyBounded (fun x => (input x).length) (fun x => (middle (f x)).length) :=
  let ⟨_, _, hf⟩ := hf
  hf.polyBounded_length

/-- Polynomial-time preprocessing does not change the level. -/
theorem preprocess {f : β → γ} {g : α → β}
    (hf : f ∈ CountingFunction a middle output) (hg : ComputableInPolyTime g input middle) :
    (fun x => f (g x)) ∈ CountingFunction a input output :=
  let ⟨A, hA, hf⟩ := hf
  ⟨A, hA, hf.preprocess hg⟩

/-- Adaptive composition combines the two fixed oracle languages by tagging. -/
theorem comp {f : β → γ} {g : α → β}
    (hf : f ∈ CountingFunction a middle output) (hg : g ∈ CountingFunction a input middle) :
    (fun x => f (g x)) ∈ CountingFunction a input output := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  exact ⟨taggedUnion A B, taggedUnion_mem_CountingLevel hA hB,
    (hf.of_polyTimeReducible (reduces_taggedUnion_left A B)).comp
      (hg.of_polyTimeReducible (reduces_taggedUnion_right A B))⟩

/-- A fixed pair of same-level functions can be evaluated together at that level. -/
theorem prod {f : α → β} {g : α → γ}
    (hf : f ∈ CountingFunction a input middle) (hg : g ∈ CountingFunction a input output) :
    (fun x => (f x, g x)) ∈ CountingFunction a input (encPair middle output) := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  exact ⟨taggedUnion A B, taggedUnion_mem_CountingLevel hA hB,
    (hf.of_polyTimeReducible (reduces_taggedUnion_left A B)).prod
      (hg.of_polyTimeReducible (reduces_taggedUnion_right A B))⟩

/-- Retain the input for a later same-level computation. -/
theorem comp_with {f : α × β → γ} {g : α → β}
    (hf : f ∈ CountingFunction a (encPair input middle) output)
    (hg : g ∈ CountingFunction a input middle) :
    (fun x => f (x, g x)) ∈ CountingFunction a input output :=
  comp hf (prod (of_polyTime ComputableInPolyTime.id') hg)

/-- Same-level Boolean control selects between two same-level function values. -/
theorem ite {c : α → Bool} {f g : α → β}
    (hc : c ∈ CountingFunction a input encBool)
    (hf : f ∈ CountingFunction a input middle) (hg : g ∈ CountingFunction a input middle) :
    (fun x => if c x then f x else g x) ∈ CountingFunction a input middle := by
  obtain ⟨A, hA, hpair⟩ := prod hc (prod hf hg)
  have hbranches := ComputableInPolyTime.snd encBool (encPair middle middle)
  exact ⟨A, hA, hpair.map <| ComputableInPolyTime.ite' (.fst _ _) hbranches.fst' hbranches.snd'⟩

/-- Polynomial-time postprocessing preserves the function level. -/
theorem map {f : α → β} {g : β → γ}
    (hf : f ∈ CountingFunction a input middle) (hg : ComputableInPolyTime g middle output) :
    (fun x => g (f x)) ∈ CountingFunction a input output :=
  comp (of_polyTime hg) hf

/-- An F_a Boolean decision is a language in C_(a+1) P, using a verifier that ignores its coins. -/
theorem decision {f : α → Bool} (hf : f ∈ CountingFunction a input encBool) :
    {x | f x = true} ∈ CountingLevel (a + 1) input := by
  obtain ⟨A, hA, hf⟩ := hf
  exact ⟨A, hA, PWithOracle_subset_PPWithOracle A input ⟨f, hf, fun _ => Iff.rfl⟩⟩

end CountingFunction
end Cslib.Complexity
