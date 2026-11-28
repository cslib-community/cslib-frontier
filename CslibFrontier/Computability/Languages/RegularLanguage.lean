/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Cslib/Computability/Languages/RegularLanguage.lean`)

public import CslibFrontier.Computability.Automata.NA.Map
public import Cslib.Computability.Languages.RegularLanguage
import CslibFrontier.Tactic.FinIndex

/-!
# Further closure properties of regular languages

Regular languages are closed under images along letter maps (`Language.map`), the projection
step of the translation of monadic second-order logic into automata
[Thomas, Section 3][Thomas1997]. The alphabet may be infinite. Three families of languages defined
by the positions of letters are regular for every pair of letter predicates `p`, `q`: the words
all of whose letters satisfy `p`, the words with some letter satisfying `p`, and the words with a
letter satisfying `p` strictly before a letter satisfying `q`. They are the atomic languages of
the same translation; the first two are also stated over positions `w[i]`.

Languages given by conditions on words, `{w | P w}`, are closed under the connectives through
the existing CSLib closures, with no set-builder restatement: `hP.inf hQ` proves regularity of
`{w | P w ∧ Q w}`, and likewise `IsRegular.add` for `∨`, `IsRegular.compl` for `¬`, and
`IsRegular.top`/`IsRegular.zero` for `True`/`False`. Finite conjunctions over an index type are
`IsRegular.setOf_forall`.

## Main results

* `Cslib.Language.IsRegular.map`: the image of a regular language along a letter map is regular.
* `Cslib.Language.IsRegular.setOf_forall_mem`, `Cslib.Language.IsRegular.setOf_exists_mem`,
  `Cslib.Language.IsRegular.setOf_exists_lt`, `Cslib.Language.IsRegular.setOf_forall_getElem`,
  `Cslib.Language.IsRegular.setOf_exists_getElem`: regularity of the positional languages.
* `Cslib.Language.IsRegular.setOf_forall`: regularity of a finite conjunction of regular
  conditions.
* `Cslib.Language.IsRegular.of_finite`: every finite language is regular.

## References

* [W. Thomas, *Languages, automata, and logic*][Thomas1997]
-/

public section

namespace Cslib.Language

open Automata Acceptor

variable {Symbol Symbol' : Type*}

/-- The image of a regular language along a letter map is regular. -/
theorem IsRegular.map (f : Symbol → Symbol') {l : Language Symbol} (h : l.IsRegular) :
    (Language.map f l).IsRegular := by
  rw [IsRegular.iff_nfa] at h ⊢
  obtain ⟨State, h_fin, nfa, rfl⟩ := h
  exact ⟨State, h_fin, nfa.map f, nfa.map_language_eq f⟩

/-- The words all of whose letters satisfy `p` form a regular language. -/
theorem IsRegular.setOf_forall_mem (p : Symbol → Prop) :
    Language.IsRegular {w : List Symbol | ∀ a ∈ w, p a} := by
  classical
  let M : DFA Symbol Bool := ⟨fun s a => s && decide (p a), true, {true}⟩
  have key (w : List Symbol) : ∀ s : Bool, M.evalFrom s w = (s && decide (∀ a ∈ w, p a)) := by
    induction w with
    | nil => simp [DFA.evalFrom_nil]
    | cons a w ih => simp [M, DFA.evalFrom_cons, ih, Bool.and_assoc, Bool.decide_and]
  refine ⟨Bool, inferInstance, M, ?_⟩
  ext w
  rw [DFA.mem_accepts, DFA.eval, key]
  change (true && decide (∀ a ∈ w, p a)) ∈ ({true} : Set Bool) ↔ ∀ a ∈ w, p a
  simp

/-- The words with some letter satisfying `p` form a regular language. -/
theorem IsRegular.setOf_exists_mem (p : Symbol → Prop) :
    Language.IsRegular {w : List Symbol | ∃ a ∈ w, p a} := by
  have h : ({w : List Symbol | ∃ a ∈ w, p a} : Language Symbol) = {w | ∀ a ∈ w, ¬ p a}ᶜ := by
    ext w
    simp
  exact h ▸ (IsRegular.setOf_forall_mem _).compl

private theorem exists_lt_iff_mem_mul (p q : Symbol → Prop) (w : List Symbol) :
    (∃ i j : Fin w.length, i < j ∧ p w[i] ∧ q w[j]) ↔
      ∃ a ∈ ({w : List Symbol | ∃ a ∈ w, p a} : Language Symbol),
        ∃ b ∈ ({w : List Symbol | ∃ a ∈ w, q a} : Language Symbol), a ++ b = w := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨w.take j, ⟨w[i], ?_, hi⟩, w.drop j, ⟨w[j], ?_, hj⟩, List.take_append_drop _ _⟩
    · rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_take]; omega, by simp⟩
    · rw [List.mem_iff_getElem]
      exact ⟨0, by rw [List.length_drop]; omega, by simp⟩
  · rintro ⟨a, ⟨x, hxa, hx⟩, b, ⟨y, hyb, hy⟩, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hxa
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hyb
    refine ⟨⟨i, by simp; omega⟩, ⟨a.length + j, by simp; omega⟩, ?_, ?_, ?_⟩
    · fin_index
    · simpa [List.getElem_append_left hi] using hx
    · simpa [List.getElem_append_right] using hy

/-- The words with a letter satisfying `p` strictly before a letter satisfying `q` form a regular
language. -/
theorem IsRegular.setOf_exists_lt (p q : Symbol → Prop) :
    Language.IsRegular {w : List Symbol | ∃ i j : Fin w.length, i < j ∧ p w[i] ∧ q w[j]} := by
  have h := IsRegular.mul (IsRegular.setOf_exists_mem p) (IsRegular.setOf_exists_mem q)
  refine (congrArg Language.IsRegular (Set.ext fun w => ?_)).mp h
  exact Language.mem_mul.trans (exists_lt_iff_mem_mul p q w).symm

/-- The words all of whose positions carry a letter satisfying `p` form a regular language. -/
theorem IsRegular.setOf_forall_getElem (p : Symbol → Prop) :
    Language.IsRegular {w : List Symbol | ∀ i : Fin w.length, p w[i]} :=
  (congrArg Language.IsRegular (Set.ext fun _ => List.forall_mem_iff_get)).mp
    (IsRegular.setOf_forall_mem p)

/-- The words with some position carrying a letter satisfying `p` form a regular language. -/
theorem IsRegular.setOf_exists_getElem (p : Symbol → Prop) :
    Language.IsRegular {w : List Symbol | ∃ i : Fin w.length, p w[i]} :=
  (congrArg Language.IsRegular (Set.ext fun _ => List.exists_mem_iff_get)).mp
    (IsRegular.setOf_exists_mem p)

/-- A finite conjunction of regular conditions on words is regular. -/
theorem IsRegular.setOf_forall {ι : Type*} [Finite ι] {P : ι → List Symbol → Prop}
    (h : ∀ i, Language.IsRegular {w | P i w}) : Language.IsRegular {w | ∀ i, P i w} := by
  refine (congrArg Language.IsRegular (Set.ext fun w => ?_)).mp
    (IsRegular.iInf (s := Set.univ) fun i _ => h i)
  exact Set.mem_iInter₂.trans (by simp)

/-- A single word forms a regular language. -/
theorem IsRegular.singleton (w : List Symbol) : ({w} : Language Symbol).IsRegular := by
  induction w with
  | nil => exact IsRegular.one
  | cons a w ih =>
    refine (congrArg Language.IsRegular (Set.ext fun v => ?_)).mp
      (IsRegular.mul (IsRegular.char a) ih)
    change v ∈ ({[a]} * {w} : Language Symbol) ↔ v = a :: w
    rw [Language.mem_mul]
    exact ⟨fun ⟨x, hx, y, hy, h⟩ => by
      rw [← h, show x = [a] from hx, show y = w from hy]; rfl,
      fun h => ⟨[a], rfl, w, rfl, (show v = a :: w from h).symm⟩⟩

/-- Every finite language is regular. -/
theorem IsRegular.of_finite {l : Language Symbol} (h : Set.Finite (α := List Symbol) l) :
    l.IsRegular := by
  induction l, h using Set.Finite.induction_on with
  | empty => exact IsRegular.zero
  | @insert w s _ _ ih =>
    exact (congrArg Language.IsRegular (Set.insert_eq w s).symm).mp
      ((IsRegular.singleton w).add ih)

end Cslib.Language
