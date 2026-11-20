/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.SecondOrder.Existential
public import Mathlib.Logic.Relation

/-!
# Relational second-order logic and transitive closure

An element quantifier binds one first-order variable. A relation quantifier binds
a finite block of relation variables of specified arities, reusing the relation-variable
language and expansion of `ESO`. The grammar allows both kinds of quantifier to nest in
either order. Relation quantifiers have full semantics over all relations of their arity
on the carrier [Immerman, Chapter 7][Immerman1999].

First-order subformulas reuse Mathlib's bounded formulas. An existential second-order
sentence embeds by applying one existential relation block to its first-order matrix.
`Definable` is the SO predicate on classes of finite structures.

The transitive-closure extension lets an edge formula bind two tuples of elements and
relations. An application holds when its endpoints are joined by a nonempty finite path
in that edge relation
[Ferrarotti, Van den Bussche and Virtema, §2, Definitions 3–4][FerrarottiVanDenBusscheVirtema2018].
The syntax index enables this constructor only for SO(TC).

Their setting uses finite nonempty carriers, relational vocabularies, and variable tuples
as the TC endpoints. To instantiate that setting, take a relational input language, restrict
the carriers to finite nonempty types, use `Term.var` at the individual endpoints, and
interpret the relation endpoints as input symbols or relation variables in scope.
Here `TCDefinable` also ranges over empty finite carriers, the vocabulary can include fixed
function symbols, and an individual endpoint can be any first-order term. This development
defines satisfaction and finite-structure definability. Complexity capture is a separate result.

## Main definitions

* `BoundedFormula`, `BoundedFormula.Realize`: typed formulas and satisfaction.
* `Formula` and `TCFormula`: the SO and SO(TC) formula types.
* `Sentence`, `Sentence.ofESO`, `Definable`: closed formulas and finite-structure definability.

## Main results

* `Sentence.realize_ofESO`: the existing ESO semantics agree with the full SO semantics.
* `Definable.of_eso`, `Definable.compl`: SO contains ESO and is closed under complement.
-/

@[expose] public section

universe u v w w'

namespace Cslib.Logic.SO

open FirstOrder Language Structure CategoryTheory

/-- A second-order formula with free element variables `α`, `n` bound element variables,
and vocabulary `L`. Relation binders extend the vocabulary for their body. -/
inductive BoundedFormula (allowTC : Bool) (α : Type w) :
    Language.{u, v} → ℕ → Type (max (u + 1) (v + 1) w) where
  /-- Embed a first-order formula. -/
  | ofFirstOrder {L n} (φ : L.BoundedFormula α n) : BoundedFormula allowTC α L n
  /-- Logical implication. -/
  | imp {L n} (φ ψ : BoundedFormula allowTC α L n) : BoundedFormula allowTC α L n
  /-- Quantify universally over one element, appended to the bound-variable list. -/
  | all {L n} (φ : BoundedFormula allowTC α L (n + 1)) : BoundedFormula allowTC α L n
  /-- Quantify universally over a finite block of relations. -/
  | allRel {L n} {ι : Type} (_ : Finite ι) (arity : ι → ℕ)
      (φ : BoundedFormula allowTC α (L.sum (ESO.varLanguage arity)) n) :
      BoundedFormula allowTC α L n
  /-- Apply transitive closure to an edge formula over two tuples of elements and relations. -/
  | tc {L n k} {ι : Type} (_ : allowTC = true) (_ : Finite ι) (arity : ι → ℕ)
      (sourceRelations targetRelations : ∀ i, L.Relations (arity i))
      (sourceTerms targetTerms : Fin k → L.Term (α ⊕ Fin n))
      (edge : BoundedFormula allowTC α
        (L.sum (ESO.varLanguage (Sum.elim arity arity))) (n + k + k)) :
      BoundedFormula allowTC α L n

namespace BoundedFormula

variable {allowTC : Bool} {α : Type w} {L : Language.{u, v}} {n : ℕ} {M : Type w'}

/-- Evaluate a formula in a structure, with assignments for the free and bound elements. -/
def Realize : {L : Language.{u, v}} → {n : ℕ} → BoundedFormula allowTC α L n →
    [L.Structure M] → (α → M) → (Fin n → M) → Prop
  | _, _, .ofFirstOrder ψ, _, free, bound => ψ.Realize free bound
  | _, _, .imp ψ χ, _, free, bound => ψ.Realize free bound → χ.Realize free bound
  | _, _, .all ψ, _, free, bound => ∀ a : M, ψ.Realize free (Fin.snoc bound a)
  | _, _, .allRel (ι := ι) _ arity ψ, _, free, bound =>
    ∀ R : ∀ i : ι, Set (Fin (arity i) → M),
      letI := ESO.varLanguage.structure R
      ψ.Realize free bound
  | _, _, .tc (ι := ι) (k := k) _ _ arity sourceRelations targetRelations
      sourceTerms targetTerms edge, _, free, bound =>
    let step (a b : (Fin k → M) × (∀ i : ι, Set (Fin (arity i) → M))) : Prop :=
      letI := ESO.varLanguage.structure (arity := Sum.elim arity arity) fun
        | .inl i => a.2 i
        | .inr i => b.2 i
      edge.Realize free (Fin.append (Fin.append bound a.1) b.1)
    Relation.TransGen step
      (fun i => (sourceTerms i).realize (Sum.elim free bound),
        fun i => {x | RelMap (sourceRelations i) x})
      (fun i => (targetTerms i).realize (Sum.elim free bound),
        fun i => {x | RelMap (targetRelations i) x})

/-- Negation of a second-order formula. -/
def neg (φ : BoundedFormula allowTC α L n) : BoundedFormula allowTC α L n :=
  .imp φ (.ofFirstOrder ⊥)

/-- Existential first-order quantification. -/
def ex (φ : BoundedFormula allowTC α L (n + 1)) : BoundedFormula allowTC α L n :=
  (BoundedFormula.all φ.neg).neg

/-- Existential quantification over a block of relations. -/
def exRel {ι : Type} [Finite ι] (arity : ι → ℕ)
    (φ : BoundedFormula allowTC α (L.sum (ESO.varLanguage arity)) n) :
    BoundedFormula allowTC α L n :=
  (BoundedFormula.allRel inferInstance arity φ.neg).neg

variable [L.Structure M] {free : α → M} {bound : Fin n → M}

@[simp]
theorem realize_neg (φ : BoundedFormula allowTC α L n) :
    φ.neg.Realize free bound ↔ ¬ φ.Realize free bound := by
  simp [neg, Realize]

@[simp]
theorem realize_ex (φ : BoundedFormula allowTC α L (n + 1)) :
    φ.ex.Realize free bound ↔ ∃ a : M, φ.Realize free (Fin.snoc bound a) := by
  classical
  simp only [ex, realize_neg, Realize, Classical.not_forall, not_not]

@[simp]
theorem realize_exRel {ι : Type} [Finite ι] (arity : ι → ℕ)
    (φ : BoundedFormula allowTC α (L.sum (ESO.varLanguage arity)) n) :
    (exRel arity φ).Realize free bound ↔
      ∃ R : ∀ i, Set (Fin (arity i) → M),
        letI := ESO.varLanguage.structure R
        φ.Realize free bound := by
  classical
  simp only [exRel, realize_neg, Realize, Classical.not_forall, not_not]

end BoundedFormula

/-- A formula of plain second-order logic. -/
abbrev Formula := BoundedFormula false

/-- A formula of second-order logic with transitive closure. -/
abbrev TCFormula := BoundedFormula true

/-- A second-order sentence has no free or bound element variables at its outer level. -/
abbrev Sentence (L : Language.{u, v}) := Formula Empty L 0

/-- An SO(TC) sentence has no free or bound element variables at its outer level. -/
abbrev TCSentence (L : Language.{u, v}) := TCFormula Empty L 0

namespace Sentence

variable {L : Language.{u, v}}

/-- Satisfaction of a second-order sentence. -/
def Realize (φ : Sentence L) (M : Type w) [L.Structure M] : Prop :=
  BoundedFormula.Realize (M := M) φ default default

/-- Embed an existential second-order sentence into second-order logic. -/
def ofESO (φ : ESO.Sentence L) : Sentence L :=
  BoundedFormula.exRel φ.arity (.ofFirstOrder φ.matrix)

/-- The ESO embedding preserves satisfaction. -/
@[simp]
theorem realize_ofESO (φ : ESO.Sentence L) (M : Type w) [L.Structure M] :
    (ofESO φ).Realize M ↔ φ.Realize M := by
  rw [Realize, ofESO, BoundedFormula.realize_exRel]
  simp only [BoundedFormula.Realize, ESO.Sentence.Realize, FirstOrder.Language.Sentence.Realize,
    FirstOrder.Language.Formula.Realize]

end Sentence

variable {L : Language.{u, v}}

/-- A class is second-order definable if a sentence defines its finite members. -/
def Definable (K : Set (Bundled.{w} L.Structure)) : Prop :=
  ∃ φ : Sentence L, ∀ (M : Bundled.{w} L.Structure) [Finite M], M ∈ K ↔ φ.Realize M

/-- A class is SO(TC)-definable if a transitive-closure sentence defines its finite members. -/
def TCDefinable (K : Set (Bundled.{w} L.Structure)) : Prop :=
  ∃ φ : TCSentence L, ∀ (M : Bundled.{w} L.Structure) [Finite M],
    M ∈ K ↔ BoundedFormula.Realize (M := M) φ default default

/-- Every existential second-order definable class is second-order definable. -/
theorem Definable.of_eso {K : Set (Bundled.{w} L.Structure)} (h : ESO.Definable K) :
    Definable K := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨.ofESO φ, fun M _ => (hφ M).trans (Sentence.realize_ofESO φ M).symm⟩

/-- Second-order definability is closed under complement. -/
theorem Definable.compl {K : Set (Bundled.{w} L.Structure)} (h : Definable K) :
    Definable Kᶜ := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.neg, fun M _ => (not_congr (hφ M)).trans (BoundedFormula.realize_neg φ).symm⟩

end Cslib.Logic.SO
