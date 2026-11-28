/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Languages.RegularLanguage

/-!
# Star-free languages

A star-free expression is built from `∅` and single letters by union, complement and
concatenation [Libkin, Definition 7.25][Libkin2004], with complement taken relative to all words
`List α`. A language is star-free when some star-free expression denotes it. Star-free languages
are regular, by the closure properties of regular languages.

Libkin works over a finite alphabet [Libkin, Section 7.4][Libkin2004]. This file allows an
arbitrary alphabet, where the finiteness matters: `{ε}` is star-free exactly when the alphabet is
finite (`isStarFree_one_iff`). Over a finite alphabet `{ε}` is the complement of `⊤ · Σ`; over an
infinite alphabet some letter `c` does not occur in a given expression, and on the words `cⁿ` the
expression's language is all or nothing.

Other presentations start from `∅`, `{ε}` and the letters, or from all finite languages. Over a
finite alphabet they define the same class, because `{ε}` and every finite language are star-free
in the sense above (`IsStarFree.one`, `IsStarFree.of_finite`).

## Main definitions

* `Cslib.Language.StarFreeExpression`: star-free expressions.
* `Cslib.Language.StarFreeExpression.matches'`: the language denoted by an expression.
* `Cslib.Language.StarFreeExpression.matchEpsilon`: whether an expression matches the empty word,
  computed structurally.
* `Cslib.Language.StarFreeExpression.letters`: the letters occurring in an expression.
* `Cslib.Language.IsStarFree`: some star-free expression denotes the language.

## Main results

* `Cslib.Language.StarFreeExpression.matchEpsilon_iff`: `matchEpsilon` decides `[] ∈ e.matches'`.
* `Cslib.Language.StarFreeExpression.isRegular_matches'`, `Cslib.Language.IsStarFree.isRegular`:
  star-free languages are regular.
* `Cslib.Language.StarFreeExpression.replicate_mem_or_notMem`: on the powers of a letter that does
  not occur in an expression, its language is all or nothing.
* `Cslib.Language.IsStarFree.zero`, `char`, `add`, `compl`, `mul`, `top`, `inf`, `iSup`, `iInf`:
  closure properties, the last two for finite unions and intersections.
* `Cslib.Language.IsStarFree.setOf_length_eq_one`, `Cslib.Language.IsStarFree.one`,
  `Cslib.Language.IsStarFree.singleton`, `Cslib.Language.IsStarFree.of_finite`: over a finite
  alphabet, the words of length one, `{ε}`, every one-word language and every finite language are
  star-free.
* `Cslib.Language.not_isStarFree_one`, `Cslib.Language.isStarFree_one_iff`: `{ε}` is star-free if
  and only if the alphabet is finite.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

universe u

namespace Cslib.Language

variable {α : Type u}

/-- Star-free expressions over the alphabet `α` [Libkin, Definition 7.25][Libkin2004]. -/
inductive StarFreeExpression (α : Type u) : Type u
  /-- The empty language `∅`. -/
  | zero : StarFreeExpression α
  /-- The language `{a}` of the one-letter word `a`. -/
  | char : α → StarFreeExpression α
  /-- Union. -/
  | plus : StarFreeExpression α → StarFreeExpression α → StarFreeExpression α
  /-- Complement, relative to all words. -/
  | compl : StarFreeExpression α → StarFreeExpression α
  /-- Concatenation. -/
  | comp : StarFreeExpression α → StarFreeExpression α → StarFreeExpression α

namespace StarFreeExpression

/-- The language denoted by a star-free expression. -/
@[expose] def matches' : StarFreeExpression α → _root_.Language α
  | zero => 0
  | char a => {[a]}
  | plus e f => e.matches' + f.matches'
  | compl e => (e.matches')ᶜ
  | comp e f => e.matches' * f.matches'

@[simp] theorem matches'_zero : (zero : StarFreeExpression α).matches' = 0 := rfl

@[simp] theorem matches'_char (a : α) : (char a).matches' = {[a]} := rfl

@[simp] theorem matches'_plus (e f : StarFreeExpression α) :
    (plus e f).matches' = e.matches' + f.matches' := rfl

@[simp] theorem matches'_compl (e : StarFreeExpression α) :
    (compl e).matches' = (e.matches')ᶜ := rfl

@[simp] theorem matches'_comp (e f : StarFreeExpression α) :
    (comp e f).matches' = e.matches' * f.matches' := rfl

/-- Whether the empty word belongs to the language of an expression, computed structurally. -/
def matchEpsilon : StarFreeExpression α → Bool
  | zero => false
  | char _ => false
  | plus e f => e.matchEpsilon || f.matchEpsilon
  | compl e => !e.matchEpsilon
  | comp e f => e.matchEpsilon && f.matchEpsilon

theorem matchEpsilon_iff : ∀ e : StarFreeExpression α, e.matchEpsilon = true ↔ [] ∈ e.matches'
  | zero => by simp [matchEpsilon]
  | char a => by simp [matchEpsilon]
  | plus e f => by simp [matchEpsilon, Language.mem_add, matchEpsilon_iff e, matchEpsilon_iff f]
  | compl e => by
    rw [matchEpsilon, Bool.not_eq_true', ← Bool.not_eq_true, matchEpsilon_iff e]
    rfl
  | comp e f => by
    simp only [matchEpsilon, Bool.and_eq_true, matches'_comp, Language.mem_mul, matchEpsilon_iff e,
      matchEpsilon_iff f]
    refine ⟨fun ⟨he, hf⟩ => ⟨[], he, [], hf, rfl⟩, ?_⟩
    rintro ⟨_, ha, _, hb, hab⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hab
    exact ⟨ha, hb⟩

/-- The language of a star-free expression is regular. -/
theorem isRegular_matches' : ∀ e : StarFreeExpression α, e.matches'.IsRegular
  | zero => IsRegular.zero
  | char a => IsRegular.char a
  | plus e f => IsRegular.add (isRegular_matches' e) (isRegular_matches' f)
  | compl e => IsRegular.compl (isRegular_matches' e)
  | comp e f => IsRegular.mul (isRegular_matches' e) (isRegular_matches' f)

/-- The letters occurring in an expression. -/
def letters : StarFreeExpression α → Set α
  | zero => ∅
  | char a => {a}
  | plus e f => e.letters ∪ f.letters
  | compl e => e.letters
  | comp e f => e.letters ∪ f.letters

theorem letters_finite : ∀ e : StarFreeExpression α, e.letters.Finite
  | zero => Set.finite_empty
  | char a => Set.finite_singleton a
  | plus e f => (letters_finite e).union (letters_finite f)
  | compl e => letters_finite e
  | comp e f => (letters_finite e).union (letters_finite f)

/-- On the words `cⁿ` over a letter `c` that does not occur in `e`, the language of `e` is all or
nothing. -/
theorem replicate_mem_or_notMem {c : α} : ∀ e : StarFreeExpression α, c ∉ e.letters →
    (∀ n, List.replicate n c ∈ e.matches') ∨ (∀ n, List.replicate n c ∉ e.matches')
  | zero, _ => .inr fun _ => Language.notMem_zero _
  | char a, hc => .inr fun _ h =>
      hc (List.eq_of_mem_replicate (Set.mem_singleton_iff.1 h ▸ List.mem_singleton_self a)).symm
  | plus e f, hc => by
    obtain ⟨he, hf⟩ := not_or.1 hc
    rcases replicate_mem_or_notMem e he with he | he <;>
      rcases replicate_mem_or_notMem f hf with hf | hf
    exacts [.inl fun n => .inl (he n), .inl fun n => .inl (he n), .inl fun n => .inr (hf n),
      .inr fun n h => h.elim (he n) (hf n)]
  | compl e, hc => (replicate_mem_or_notMem e hc).symm.imp
      (fun he n h => he n h) (fun he n h => h (he n))
  | comp e f, hc => by
    obtain ⟨he, hf⟩ := not_or.1 hc
    rcases replicate_mem_or_notMem e he with he | he
    · rcases replicate_mem_or_notMem f hf with hf | hf
      · exact .inl fun n => Language.mem_mul.2 ⟨[], he 0, _, hf n, rfl⟩
      · exact .inr fun _ h => let ⟨_, _, _, hy, hxy⟩ := Language.mem_mul.1 h
          hf _ ((List.append_eq_replicate_iff.1 hxy).2.2 ▸ hy)
    · exact .inr fun _ h => let ⟨_, hx, _, _, hxy⟩ := Language.mem_mul.1 h
        he _ ((List.append_eq_replicate_iff.1 hxy).2.1 ▸ hx)

end StarFreeExpression

/-- A language is **star-free** when some star-free expression denotes it
[Libkin, Definition 7.25][Libkin2004]. -/
@[expose] def IsStarFree (L : _root_.Language α) : Prop :=
  ∃ e : StarFreeExpression α, e.matches' = L

namespace IsStarFree

theorem zero : IsStarFree (0 : _root_.Language α) := ⟨.zero, rfl⟩

theorem char (a : α) : IsStarFree ({[a]} : _root_.Language α) := ⟨.char a, rfl⟩

theorem add {L M : _root_.Language α} (hL : IsStarFree L) (hM : IsStarFree M) :
    IsStarFree (L + M) :=
  let ⟨e, he⟩ := hL
  let ⟨f, hf⟩ := hM
  ⟨.plus e f, by rw [StarFreeExpression.matches'_plus, he, hf]⟩

theorem compl {L : _root_.Language α} (hL : IsStarFree L) : IsStarFree Lᶜ :=
  let ⟨e, he⟩ := hL
  ⟨.compl e, by rw [StarFreeExpression.matches'_compl, he]⟩

theorem mul {L M : _root_.Language α} (hL : IsStarFree L) (hM : IsStarFree M) :
    IsStarFree (L * M) :=
  let ⟨e, he⟩ := hL
  let ⟨f, hf⟩ := hM
  ⟨.comp e f, by rw [StarFreeExpression.matches'_comp, he, hf]⟩

/-- All words form a star-free language, the complement of `∅`. -/
theorem top : IsStarFree (⊤ : _root_.Language α) :=
  have h : (0 : _root_.Language α)ᶜ = ⊤ :=
    Set.ext fun x => iff_of_true (Language.notMem_zero x) trivial
  h ▸ zero.compl

theorem inf {L M : _root_.Language α} (hL : IsStarFree L) (hM : IsStarFree M) :
    IsStarFree (L ⊓ M) := by
  have h : (Lᶜ + Mᶜ)ᶜ = L ⊓ M := Set.ext fun x =>
    ⟨fun hx => ⟨by_contra fun h => hx ((Language.mem_add _ _ x).2 (.inl h)),
      by_contra fun h => hx ((Language.mem_add _ _ x).2 (.inr h))⟩,
      fun ⟨h1, h2⟩ hx => ((Language.mem_add _ _ x).1 hx).elim (· h1) (· h2)⟩
  exact h ▸ (hL.compl.add hM.compl).compl

/-- A finite union of star-free languages is star-free. -/
theorem iSup {ι : Type*} [Finite ι] {L : ι → _root_.Language α} (hL : ∀ i, IsStarFree (L i)) :
    IsStarFree (⨆ i, L i) := by
  classical
  cases nonempty_fintype ι
  rw [← Finset.sup_univ_eq_iSup]
  refine Finset.univ.induction_on zero fun i _ _ ih => ?_
  rw [Finset.sup_insert]
  exact (hL i).add ih

/-- A finite intersection of star-free languages is star-free. -/
theorem iInf {ι : Type*} [Finite ι] {L : ι → _root_.Language α} (hL : ∀ i, IsStarFree (L i)) :
    IsStarFree (⨅ i, L i) := by
  rw [← compl_compl (⨅ i, L i), compl_iInf]
  exact (IsStarFree.iSup fun i => (hL i).compl).compl

/-- Star-free languages are regular. -/
theorem isRegular {L : _root_.Language α} (h : IsStarFree L) : L.IsRegular :=
  let ⟨e, he⟩ := h
  he ▸ e.isRegular_matches'

/-- Over a finite alphabet, the words of length one form a star-free language, the finite union
of the letters. -/
theorem setOf_length_eq_one [Finite α] : IsStarFree {w : List α | w.length = 1} := by
  suffices (⨆ a : α, ({[a]} : _root_.Language α)) = {w | w.length = 1} from this ▸ iSup char
  ext w
  change w ∈ ⨆ a : α, ({[a]} : _root_.Language α) ↔ w.length = 1
  simp [Language.mem_iSup, List.length_eq_one_iff]

/-- Over a finite alphabet, `{ε}` is star-free: it is the complement of `⊤ · Σ`. -/
theorem one [Finite α] : IsStarFree (1 : _root_.Language α) := by
  let S : _root_.Language α := {w | w.length = 1}
  suffices (⊤ * S)ᶜ = (1 : _root_.Language α) from this ▸ (top.mul setOf_length_eq_one).compl
  ext w
  rw [Language.mem_one]
  refine ⟨fun h => (List.eq_nil_or_concat w).resolve_right fun ⟨x, b, hw⟩ =>
    h (hw ▸ Language.mem_mul.2 ⟨x, trivial, [b], rfl, List.concat_eq_append.symm⟩), ?_⟩
  rintro rfl h
  obtain ⟨x, -, y, hy : y.length = 1, hxy⟩ := Language.mem_mul.1 h
  simp [(List.append_eq_nil_iff.1 hxy).2] at hy

/-- Over a finite alphabet, every one-word language `{w}` is star-free: `{ε}` is, and
`{a :: w} = {a} · {w}`. -/
theorem singleton [Finite α] (w : List α) : IsStarFree ({w} : _root_.Language α) := by
  induction w with
  | nil => exact one
  | cons a w ih =>
    suffices ({[a]} * {w} : _root_.Language α) = {a :: w} from this ▸ (char a).mul ih
    ext u
    rw [Language.mem_mul]
    refine ⟨?_, fun hu : u = a :: w => ⟨[a], rfl, w, rfl, hu.symm⟩⟩
    rintro ⟨_, rfl : _ = [a], _, rfl : _ = w, rfl⟩
    rfl

/-- Over a finite alphabet, every finite language is star-free, as a finite union of one-word
languages. -/
theorem of_finite [Finite α] {L : _root_.Language α} (hL : Set.Finite (L : Set (List α))) :
    IsStarFree L := by
  have := hL.to_subtype
  suffices (⨆ v : {w // w ∈ L}, ({v.val} : _root_.Language α)) = L from
    this ▸ iSup fun v => singleton v.val
  ext w
  simp [Language.mem_iSup]

end IsStarFree

/-- Over an infinite alphabet, `{ε}` is not star-free: an expression mentions finitely many
letters, and on the powers of a letter that it does not mention its language is all or nothing. -/
theorem not_isStarFree_one [Infinite α] : ¬ IsStarFree (1 : _root_.Language α) := by
  rintro ⟨e, he⟩
  obtain ⟨c, hc⟩ := e.letters_finite.exists_notMem
  rcases e.replicate_mem_or_notMem hc with h | h
  · exact absurd (he ▸ h 1 : [c] ∈ (1 : _root_.Language α)) (by simp)
  · exact h 0 (he ▸ rfl)

/-- `{ε}` is star-free if and only if the alphabet is finite. -/
theorem isStarFree_one_iff : IsStarFree (1 : _root_.Language α) ↔ Finite α :=
  ⟨fun h => by_contra fun hfin => @not_isStarFree_one _ (not_finite_iff_infinite.1 hfin) h,
    fun _ => .one⟩

end Cslib.Language
