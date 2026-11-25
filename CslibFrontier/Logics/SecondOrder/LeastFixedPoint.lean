/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.SecondOrder.Basic
public import Mathlib.Order.FixedPoints

/-!
# Second-order logic with least fixed points

An inductive predicate in SO(LFP) can take both elements and relations as arguments.
A fixed-point application binds one such predicate and a mixed tuple of arguments in
its body. It tests membership of a specified tuple in the least fixed point of the body.

The polarity check ensures that each inductive predicate occurs positively in its own
body, including below nested fixed-point applications. Second-order quantification
continues to range over ordinary relations on elements
[Immerman1999].

## Main definitions

* `Cslib.Logic.SO.LFP.BoundedFormula`: formulas with typed recursive predicates.
* `Cslib.Logic.SO.LFP.BoundedFormula.Positive`: syntactic polarity check.
* `Cslib.Logic.SO.LFP.BoundedFormula.Realize`: satisfaction for the raw syntax.
* `Cslib.Logic.SO.LFPDefinable`: definability by a checked SO(LFP) sentence.

## Main results

* `Cslib.Logic.SO.LFP.BoundedFormula.Positive.realize_mono`: polarity implies monotonicity.
* `Cslib.Logic.SO.LFP.BoundedFormula.realize_lfp`: a checked application uses Mathlib's least
  fixed point.
-/

public section

universe u v w w'

namespace Cslib.Logic.SO.LFP

open FirstOrder Language Structure

/-- The arities and sorts of the arguments of an inductively defined predicate. -/
structure Shape where
  /-- Number of element arguments. -/
  elements : ℕ
  /-- Number of relation arguments. -/
  relations : ℕ
  /-- Arity of each relation argument. -/
  arity : Fin relations → ℕ

/-- The mixed tuples on which a predicate of this shape is interpreted. -/
abbrev Shape.Value (s : Shape) (M : Type w') := MixedTuple M s.elements s.arity

/-- A recursive predicate variable of shape `s` in the context `Γ`. -/
inductive Var : List Shape → Shape → Type where
  /-- The most recently bound recursive predicate. -/
  | head {Γ s} : Var (s :: Γ) s
  /-- A predicate already in scope before the most recent binder. -/
  | tail {Γ s t} : Var Γ s → Var (t :: Γ) s

/-- Assignments of interpretations to the recursive predicates in a context. -/
abbrev Env (Γ : List Shape) (M : Type w') := ∀ {s}, Var Γ s → Set (s.Value M)

/-- Requested polarity of occurrences of a predicate. `none` permits either sign. -/
abbrev Polarities (Γ : List Shape) := ∀ {s}, Var Γ s → Option Bool

namespace Env

/-- Extend an environment by one recursive predicate. -/
@[expose] def cons {Γ : List Shape} {s : Shape} {M : Type w'}
    (e : Env Γ M) (S : Set (s.Value M)) : Env (s :: Γ) M
  | _, .head => S
  | _, .tail p => e p

/-- A pair of interpretations varies in the direction prescribed by each polarity.
Unrestricted variables have the same interpretation in the two environments. -/
@[expose] def Below {Γ : List Shape} {M : Type w'} (p : Polarities Γ) (e e' : Env Γ M) : Prop :=
  ∀ {s} (r : Var Γ s), match p r with
    | some true => e r ⊆ e' r
    | some false => e' r ⊆ e r
    | none => e r = e' r

end Env

namespace Polarities

/-- The polarity assignment that permits either sign for every variable in scope. -/
@[expose] def unrestricted (Γ : List Shape) : Polarities Γ := fun _ => none

/-- Reverse all specified polarities. -/
@[expose] def flip {Γ : List Shape} (p : Polarities Γ) : Polarities Γ :=
  fun r => (p r).map (! ·)

/-- A fixed-point body requires positive occurrences of its newly bound predicate. -/
@[expose] def bind {Γ : List Shape} (p : Polarities Γ) (s : Shape) : Polarities (s :: Γ)
  | _, .head => some true
  | _, .tail r => p r

end Polarities

namespace Env

variable {Γ : List Shape} {M : Type w'} {p : Polarities Γ} {e e' : Env Γ M}

/-- Reversing polarities reverses the comparison of environments. -/
theorem Below.flip (h : Below p e e') : Below p.flip e' e := by
  intro s r
  specialize h r
  cases hp : p r with
  | none => simpa [Polarities.flip, hp, eq_comm] using h
  | some b => cases b <;> simpa [Polarities.flip, hp] using h

/-- Paired extensions respect the new positive binder when its relation grows. -/
theorem Below.cons (h : Below p e e') {s : Shape} {S S' : Set (s.Value M)} (hS : S ⊆ S') :
    Below (p.bind s) (e.cons S) (e'.cons S') := by
  intro t r
  cases r with
  | head => exact hS
  | tail r => exact h r

/-- Every environment compares to itself at any polarity. -/
theorem Below.refl (p : Polarities Γ) (e : Env Γ M) : Below p e e := by
  intro s r
  cases hp : p r with
  | none => simp [hp]
  | some b => cases b <;> simp [hp]

end Env

/-- SO(LFP) formulas with free element variables `α`, typed recursive predicates `Γ`,
an ordinary vocabulary `L`, and `n` bound elements. -/
inductive BoundedFormula (α : Type w) :
    List Shape → Language.{u, v} → ℕ → Type (max (u + 1) (v + 1) w) where
  /-- Use a plain second-order formula, independent of the recursive predicates. -/
  | ofSO {Γ L n} (φ : SO.Formula α L n) : BoundedFormula α Γ L n
  /-- Apply a recursive predicate to element terms and relation symbols. -/
  | atom {Γ L n s} (r : Var Γ s) (terms : Fin s.elements → L.Term (α ⊕ Fin n))
      (relations : ∀ i, L.Relations (s.arity i)) : BoundedFormula α Γ L n
  /-- Implication, which reverses polarity in the antecedent. -/
  | imp {Γ L n} (φ ψ : BoundedFormula α Γ L n) : BoundedFormula α Γ L n
  /-- Quantify universally over an element. -/
  | all {Γ L n} (φ : BoundedFormula α Γ L (n + 1)) : BoundedFormula α Γ L n
  /-- Quantify universally over a finite block of relations. -/
  | allRel {Γ L n} {ι : Type} (_ : Finite ι) (arity : ι → ℕ)
      (φ : BoundedFormula α Γ (L.sum (ESO.varLanguage arity)) n) :
      BoundedFormula α Γ L n
  /-- Test the inductively defined predicate at the specified mixed tuple.
  The body binds a recursive predicate, a block of elements, and a block of relations. -/
  | lfp {Γ L n s}
      (terms : Fin s.elements → L.Term (α ⊕ Fin n)) (relations : ∀ i, L.Relations (s.arity i))
      (body : BoundedFormula α (s :: Γ) (L.sum (ESO.varLanguage s.arity)) (n + s.elements)) :
      BoundedFormula α Γ L n

namespace BoundedFormula

variable {α : Type w} {Γ : List Shape} {L : Language.{u, v}} {n : ℕ} {M : Type w'}

/-- The occurrences of recursive predicates agree with the specified signs, and each
nested fixed-point binder admits only positive occurrences of the predicate it binds. -/
@[expose] def Positive : {Γ : List Shape} → {L : Language.{u, v}} → {n : ℕ} →
    BoundedFormula α Γ L n → Polarities Γ → Prop
  | _, _, _, .ofSO _, _ => True
  | _, _, _, .atom r _ _, p => p r ≠ some false
  | _, _, _, .imp φ ψ, p => φ.Positive p.flip ∧ ψ.Positive p
  | _, _, _, .all φ, p => φ.Positive p
  | _, _, _, .allRel _ _ φ, p => φ.Positive p
  | _, _, _, .lfp (s := s) _ _ body, p => body.Positive (p.bind s)

/-- A formula is well formed if every fixed-point binder is positive in its own predicate. -/
@[expose] def WellFormed (φ : BoundedFormula α Γ L n) : Prop :=
  φ.Positive (Polarities.unrestricted Γ)

/-- The satisfaction relation for the raw syntax. At a fixed-point binder it uses the
intersection of pre-fixed relations, which is the least fixed point for a monotone body. -/
@[expose] def Realize : {Γ : List Shape} → {L : Language.{u, v}} → {n : ℕ} →
    BoundedFormula α Γ L n → [L.Structure M] → Env Γ M → (α → M) → (Fin n → M) → Prop
  | _, _, _, .ofSO φ, _, _, free, bound => φ.Realize free bound
  | _, _, _, .atom r terms relations, _, e, free, bound =>
    MixedTuple.realize terms relations (Sum.elim free bound) ∈ e r
  | _, _, _, .imp φ ψ, _, e, free, bound =>
    φ.Realize e free bound → ψ.Realize e free bound
  | _, _, _, .all φ, _, e, free, bound => ∀ a : M, φ.Realize e free (Fin.snoc bound a)
  | _, _, _, .allRel (ι := ι) _ arity φ, _, e, free, bound =>
    ∀ R : ∀ i : ι, Set (Fin (arity i) → M),
      letI := ESO.varLanguage.structure R
      φ.Realize e free bound
  | _, _, _, .lfp (s := s) terms relations body, _, e, free, bound =>
    let F (S : Set (s.Value M)) : Set (s.Value M) := {x |
      letI := ESO.varLanguage.structure x.2
      body.Realize (e.cons S) free (Fin.append bound x.1)}
    MixedTuple.realize terms relations (Sum.elim free bound) ∈ sInf {S | F S ⊆ S}

/-- Positive occurrences are monotone under the specified changes of interpretation. -/
theorem Positive.realize_mono {φ : BoundedFormula α Γ L n} {p : Polarities Γ}
    (hφ : φ.Positive p) [inst : L.Structure M] {e e' : Env Γ M} (he : Env.Below p e e')
    (free : α → M) (bound : Fin n → M) :
    φ.Realize e free bound → φ.Realize e' free bound := by
  revert inst free bound
  induction φ with
  | ofSO φ => intro _ _ _; exact id
  | atom r terms relations =>
    intro inst free bound
    change p r ≠ some false at hφ
    have hr := he r
    rcases hp : p r with _ | b
    · have hEq : e r = e' r := by simpa only [hp] using hr
      simp only [Realize, hEq, imp_self]
    · cases b with
      | false => exact (hφ hp).elim
      | true =>
        have hSub : e r ⊆ e' r := by simpa only [hp] using hr
        exact fun h => hSub h
  | imp φ ψ ihφ ihψ =>
    intro inst free bound
    change φ.Positive p.flip ∧ ψ.Positive p at hφ
    intro h q
    exact ihψ hφ.2 he free bound (h (ihφ hφ.1 he.flip free bound q))
  | all φ ih =>
    intro inst free bound h a
    exact ih hφ he free (Fin.snoc bound a) (h a)
  | allRel hfinite arity φ ih =>
    intro inst free bound h R
    let _ := ESO.varLanguage.structure R
    exact ih hφ he free bound (h R)
  | lfp terms relations body ih =>
    intro inst free bound
    rw [Realize, Realize]
    intro h S hS
    apply h S
    intro x hx
    let _ := ESO.varLanguage.structure x.2
    apply hS
    exact ih hφ (he.cons Set.Subset.rfl) free (Fin.append bound x.1) hx

/-- Interpret the body of a positive fixed-point binder as a monotone predicate transformer. -/
@[expose] def operator {s : Shape}
    (body : BoundedFormula α (s :: Γ) (L.sum (ESO.varLanguage s.arity)) (n + s.elements))
    (h : body.Positive (Polarities.bind (Polarities.unrestricted Γ) s))
    [L.Structure M] (e : Env Γ M) (free : α → M) (bound : Fin n → M) :
    Set (s.Value M) →o Set (s.Value M) where
  toFun S := {x |
    letI := ESO.varLanguage.structure x.2
    body.Realize (e.cons S) free (Fin.append bound x.1)}
  monotone' S S' hSS' x hx := by
    let _ := ESO.varLanguage.structure x.2
    have he : Env.Below (Polarities.unrestricted Γ) e e :=
      Env.Below.refl (Polarities.unrestricted Γ) e
    exact h.realize_mono (Env.Below.cons (p := Polarities.unrestricted Γ) he hSS') free
      (Fin.append bound x.1) hx

/-- A positive fixed-point application realizes membership in Mathlib's least fixed point. -/
theorem realize_lfp {s : Shape} {terms : Fin s.elements → L.Term (α ⊕ Fin n)}
    {relations : ∀ i, L.Relations (s.arity i)}
    {body : BoundedFormula α (s :: Γ) (L.sum (ESO.varLanguage s.arity)) (n + s.elements)}
    (h : body.Positive (Polarities.bind (Polarities.unrestricted Γ) s))
    [L.Structure M] (e : Env Γ M) (free : α → M) (bound : Fin n → M) :
    (lfp terms relations body).Realize e free bound ↔
      MixedTuple.realize terms relations (Sum.elim free bound) ∈
        (body.operator h e free bound).lfp := Iff.rfl

end BoundedFormula

/-- A checked SO(LFP) sentence. -/
abbrev Sentence (L : Language.{u, v}) :=
  {φ : BoundedFormula Empty [] L 0 // φ.WellFormed}

/-- Satisfaction of a closed SO(LFP) formula. -/
@[expose] def Sentence.Realize {L : Language.{u, v}} (φ : Sentence L) (M : Type w')
    [L.Structure M] : Prop :=
  φ.val.Realize (M := M) (fun r => nomatch r) default default

/-- Regard a plain SO sentence as an SO(LFP) sentence. -/
@[expose] def Sentence.ofSO {L : Language.{u, v}} (φ : SO.Sentence L) : Sentence L :=
  ⟨.ofSO φ, trivial⟩

/-- The embedding preserves satisfaction in every structure. -/
@[simp] theorem Sentence.realize_ofSO {L : Language.{u, v}} (φ : SO.Sentence L) (M : Type w')
    [L.Structure M] : (ofSO φ).Realize M ↔ φ.Realize M :=
  Iff.rfl

end Cslib.Logic.SO.LFP

namespace Cslib.Logic.SO

open FirstOrder CategoryTheory

/-- A class of finite structures defined by a checked SO(LFP) sentence. -/
@[expose] def LFPDefinable {L : Language.{u, v}} (K : Set (Bundled.{w} L.Structure)) : Prop :=
  ∃ φ : LFP.Sentence L, ∀ (M : Bundled.{w} L.Structure) [Finite M], M ∈ K ↔ φ.Realize M

/-- Every second-order definable class is also SO(LFP)-definable. -/
theorem LFPDefinable.of_so {L : Language.{u, v}} {K : Set (Bundled.{w} L.Structure)}
    (h : Definable K) : LFPDefinable K := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨.ofSO φ, fun M _ => (hφ M).trans (LFP.Sentence.realize_ofSO φ M).symm⟩

end Cslib.Logic.SO
