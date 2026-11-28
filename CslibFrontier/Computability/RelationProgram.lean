/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.FixedPoints
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Order.FiniteFixedPoint
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.BitVec
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite Boolean relation programs

This formalizes the six positive equation forms on bit-vector addresses from Section 4.1
of [Balasubramanian and Majumdar][BalasubramanianMajumdar2026Pushdown]. The ground facts form a
finite space. The least closed set is obtained by iterating the consequence operator from the
empty set for at most `r * 2 ^ H` steps. This module gives a semantics and a finite decision
procedure. The construction here does not include the paper's pushdown simulation.

## Main definitions

* `Equation`: the six positive forms of a relation equation.
* `Program`: one equation per predicate.
* `Fact`: a predicate applied to a bit-vector address.
* `Fact.equivFin`: the numbering of ground facts by predicate and address.
* `consequence`: the monotone consequence operator on sets of facts.
* `next`: one executable round of the program.
* `evaluate`: the decision procedure for derivability.

## Main results

* `derives_fixed`: the derivable facts are a fixed point.
* `derives_iff_all_closed`: derivability is membership in every closed set.
* `lfp_consequence`: the derivable facts form the least fixed point.
* `derives_iff_stage_card`: at most one iteration per ground fact suffices.
* `evaluate_eq_true_iff`: the executable iteration decides derivability.

## References

* [A. R. Balasubramanian, R. Majumdar, Pushdown Reachability Requires N² Time on Multitape Turing
  Machines][BalasubramanianMajumdar2026Pushdown], arXiv:2611.27814v2, Section 4.1.
-/

public section

namespace Cslib.RelationProgram

variable {r H : ℕ}

/-- The six positive equation forms in Balasubramanian and Majumdar's
relation programs. Assignment modifies the queried address, not the program. -/
inductive Equation (r H : ℕ)
  | top
  | bot
  | test (position : Fin H) (value : Bool)
  | disj (left right : Fin r)
  | conj (left right : Fin r)
  | write (source : Fin r) (position : Fin H) (value : Bool)

/-- One positive equation for each predicate. -/
abbrev Program (r H : ℕ) := Fin r → Equation r H

/-- An application of a predicate to a Boolean address. -/
structure Fact (r H : ℕ) where
  /-- Predicate applied by this fact. -/
  predicate : Fin r
  /-- Its Boolean address. -/
  address : BitVec H
  deriving DecidableEq

/-- Number the ground facts in predicate and address order. -/
def Fact.equivFin : Fact r H ≃ Fin (r * 2 ^ H) :=
  let pair : Fact r H ≃ Fin r × BitVec H :=
    ⟨fun f => (f.predicate, f.address), fun (a, u) => ⟨a, u⟩, fun _ => rfl, fun _ => rfl⟩
  pair.trans ((Equiv.prodCongr (Equiv.refl _) BitVec.equivFin.toEquiv).trans finProdFinEquiv)

instance : Fintype (Fact r H) :=
  Fintype.ofEquiv (Fin (r * 2 ^ H)) Fact.equivFin.symm

/-- Set one bit of an address, preserving the other bits. -/
@[expose] def overwrite (u : BitVec H) (p : Fin H) (b : Bool) : BitVec H :=
  let mask := BitVec.twoPow H p.val
  if b then u ||| mask else u &&& ~~~mask

/-- Reading an overwritten bit returns the new value. Other bits are unchanged. -/
theorem overwrite_bit (u : BitVec H) (p q : Fin H) (b : Bool) :
    (overwrite u p b).getLsbD q.val = (if p.val = q.val then b else u.getLsbD q.val) := by
  cases b <;> by_cases e : p.val = q.val <;>
    simp [overwrite, q.isLt, e, eq_comm]

/-- Apply all positive equations once to a candidate set of facts. -/
@[expose] def step (P : Program r H) (X : Fact r H → Prop) (f : Fact r H) : Prop :=
  match P f.predicate with
  | .top => True
  | .bot => False
  | .test p b => f.address.getLsbD p.val = b
  | .disj a b => X ⟨a, f.address⟩ ∨ X ⟨b, f.address⟩
  | .conj a b => X ⟨a, f.address⟩ ∧ X ⟨b, f.address⟩
  | .write a p b => X ⟨a, overwrite f.address p b⟩

/-- The consequence operator is monotone. -/
theorem step_mono (P : Program r H) {X Y : Fact r H → Prop}
    (h : ∀ f, X f → Y f) (f : Fact r H) : step P X f → step P Y f := by
  unfold step
  split
  · exact id
  · exact id
  · exact id
  · exact Or.imp (h _) (h _)
  · exact And.imp (h _) (h _)
  · exact h _

/-- Iterate the consequence operator starting with no facts. -/
def stage (P : Program r H) : ℕ → Fact r H → Prop
  | 0 => fun _ => False
  | j + 1 => step P (stage P j)

/-- Later stages contain every fact from earlier stages. -/
theorem stage_le (P : Program r H) {i j : ℕ} (h : i ≤ j) (f : Fact r H) :
    stage P i f → stage P j f := by
  have next (k : ℕ) (f : Fact r H) : stage P k f → stage P (k + 1) f := by
    induction k generalizing f with
    | zero => simp [stage]
    | succ k ih => exact step_mono P ih f
  induction h with
  | refl => exact id
  | step _ ih => exact fun hf => next _ _ (ih hf)

/-- A fact is derivable if it occurs at a finite stage. -/
def derives (P : Program r H) (f : Fact r H) : Prop := ∃ j, stage P j f

/-- A set is closed when it contains all of its immediate consequences. -/
@[expose] def Closed (P : Program r H) (X : Fact r H → Prop) : Prop :=
  ∀ f, step P X f → X f

/-- The set of derivable facts is closed. -/
theorem derives_closed (P : Program r H) : Closed P (derives P) := by
  rintro ⟨a, u⟩
  unfold step
  split
  · intro _
    exact ⟨1, by simp_all [stage, step]⟩
  · exact False.elim
  · intro h
    exact ⟨1, by simpa [stage, step, *] using h⟩
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact ⟨i + 1, by simp_all [stage, step]⟩
    · exact ⟨j + 1, by simp_all [stage, step]⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨max i j + 1, by
      simpa [stage, step, *] using
        And.intro (stage_le P (le_max_left i j) _ hi) (stage_le P (le_max_right i j) _ hj)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i + 1, by simp [stage, step, *]⟩

/-- A fact is derivable exactly when every closed set contains it. -/
theorem derives_iff_all_closed (P : Program r H) (f : Fact r H) :
    derives P f ↔ ∀ X, Closed P X → X f := by
  constructor
  · rintro ⟨j, hj⟩ X hX
    have subset (i : ℕ) : ∀ g, stage P i g → X g := by
      induction i with
      | zero => intro g h; exact h.elim
      | succ i ih => exact fun g hg => hX g (step_mono P ih g hg)
    exact subset j f hj
  · exact fun hall => hall (derives P) (derives_closed P)

/-- One consequence step preserves the derivable facts. -/
theorem derives_fixed (P : Program r H) (f : Fact r H) :
    step P (derives P) f ↔ derives P f := by
  refine ⟨derives_closed P f, ?_⟩
  rintro ⟨_ | j, hj⟩
  · exact hj.elim
  · exact step_mono P (fun g hg => ⟨j, hg⟩) f hj

/-- Enumerate all ground facts in predicate and address order. -/
@[expose] def facts (r H : ℕ) : List (Fact r H) :=
  (List.finRange r).flatMap fun a =>
    (List.finRange (2 ^ H)).map fun u => ⟨a, BitVec.ofFin u⟩

/-- The finite enumeration contains every ground fact. -/
theorem mem_facts (f : Fact r H) : f ∈ facts r H := by
  rcases f with ⟨a, u⟩
  exact List.mem_flatMap.mpr ⟨a, by simp, List.mem_map.mpr ⟨u.toFin, by simp, by simp⟩⟩

/-- There are `r * 2 ^ H` ground facts. -/
theorem facts_length (r H : ℕ) : (facts r H).length = r * 2 ^ H := by
  rw [facts, List.length_flatMap_of_forall_length_eq (k := 2 ^ H) (fun _ _ => by simp),
    List.length_finRange]

/-- The order homomorphism on sets of ground facts induced by a relation program. -/
def consequence (P : Program r H) : Set (Fact r H) →o Set (Fact r H) where
  toFun X := {f | step P (· ∈ X) f}
  monotone' _ _ h := fun f => step_mono P h f

/-- The least fixed point of the consequence operator is the set of derivable facts. -/
theorem lfp_consequence (P : Program r H) : (consequence P).lfp = {f | derives P f} := by
  apply le_antisymm
  · exact OrderHom.lfp_le (consequence P) (derives_closed P)
  · intro f hf
    apply (derives_iff_all_closed P f).mp hf (· ∈ (consequence P).lfp)
    intro g hg
    change g ∈ consequence P (consequence P).lfp at hg
    rwa [OrderHom.map_lfp] at hg

private theorem iterate_consequence (P : Program r H) (i : ℕ) :
    ((consequence P)^[i]) ⊥ = {f | stage P i f} := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

/-- Iteration over the grounded facts reaches the least model in at most one stage per fact. -/
theorem derives_iff_stage_card (P : Program r H) (f : Fact r H) :
    derives P f ↔ stage P (r * 2 ^ H) f := by
  have card : Fintype.card (Fact r H) = r * 2 ^ H := by
    rw [Fintype.card_congr Fact.equivFin, Fintype.card_fin]
  have fixed := OrderHom.iterate_card_bot_eq_lfp (consequence P)
  rw [card, iterate_consequence, lfp_consequence] at fixed
  exact (Set.ext_iff.mp fixed f).symm

/-- One executable round of the positive equations. -/
@[expose] def next (P : Program r H) (X : Fact r H → Bool) (f : Fact r H) : Bool :=
  match P f.predicate with
  | .top => true
  | .bot => false
  | .test p b => f.address.getLsbD p.val == b
  | .disj a b => X ⟨a, f.address⟩ || X ⟨b, f.address⟩
  | .conj a b => X ⟨a, f.address⟩ && X ⟨b, f.address⟩
  | .write a p b => X ⟨a, overwrite f.address p b⟩

private theorem next_eq_true (P : Program r H) (X : Fact r H → Bool) (f : Fact r H) :
    next P X f = true ↔ step P (fun g => X g = true) f := by
  unfold next step
  split <;> simp

private theorem iterate_next_eq_true (P : Program r H) (i : ℕ) (f : Fact r H) :
    ((next P)^[i] (fun _ => false)) f = true ↔ stage P i f := by
  induction i generalizing f with
  | zero => simp [stage]
  | succ i ih =>
    rw [Function.iterate_succ_apply', next_eq_true, stage]
    have eq : (fun g => ((next P)^[i] (fun _ => false)) g = true) = stage P i :=
      funext fun g => propext (ih g)
    rw [eq]

/-- Decide derivability by iterating over the finite address space. -/
@[expose] def evaluate (P : Program r H) (f : Fact r H) : Bool :=
  ((next P)^[r * 2 ^ H] (fun _ => false)) f

/-- The executable iteration returns true exactly on derivable facts. -/
theorem evaluate_eq_true_iff (P : Program r H) (f : Fact r H) :
    evaluate P f = true ↔ derives P f :=
  (iterate_next_eq_true P _ f).trans (derives_iff_stage_card P f).symm

end Cslib.RelationProgram
