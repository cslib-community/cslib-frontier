/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Relation
public import Mathlib.Order.FixedPoints
import CslibFrontier.Foundations.Order.FiniteFixedPoint

/-!
# Computing the reflexive-transitive closure on a finite type

For a decidable relation `r` on a finite type, `Relation.reflTransGenFinset r` is the finite set of
pairs related by `Relation.ReflTransGen r`. It applies the closure rules (a reflexive pair, or an
`r`-step followed by a pair already found) to the empty set once for each pair, which reaches the
least fixed point (`OrderHom.iterate_card_bot_eq_lfp`).

## Main definitions

* `Relation.reflTransGenFinset`: the reflexive-transitive closure as a computable `Finset`.

## Main results

* `Relation.mem_reflTransGenFinset`: membership is `Relation.ReflTransGen r`.
-/

public section

namespace Relation

variable {α : Type*} (r : α → α → Prop)

/-- The closure rules of `ReflTransGen r`: a reflexive pair, or an `r`-step followed by `R`. -/
@[expose] def reflTransGenRule : Set (α × α) →o Set (α × α) where
  toFun R := {p | p.1 = p.2 ∨ ∃ b, r p.1 b ∧ (b, p.2) ∈ R}
  monotone' R R' hR p hp := by
    rcases hp with h | ⟨b, hb, hR'⟩
    · exact .inl h
    · exact .inr ⟨b, hb, hR hR'⟩

theorem lfp_reflTransGenRule : (reflTransGenRule r).lfp = {p | ReflTransGen r p.1 p.2} := by
  apply le_antisymm
  · refine OrderHom.lfp_le _ ?_
    rintro ⟨a, a'⟩ ((rfl : a = a') | ⟨b, hb, hR⟩)
    · exact .refl
    · exact .head hb hR
  · rintro ⟨a, a'⟩ (h : ReflTransGen r a a')
    induction h using ReflTransGen.head_induction_on with
    | refl => exact OrderHom.map_lfp (reflTransGenRule r) ▸ .inl rfl
    | head hb _ ih => exact OrderHom.map_lfp (reflTransGenRule r) ▸ .inr ⟨_, hb, ih⟩

variable [Fintype α] [DecidableEq α] [DecidableRel r]

/-- One application of the closure rules of `ReflTransGen r` to a finite relation. -/
@[expose] def reflTransGenStep (R : Finset (α × α)) : Finset (α × α) :=
  Finset.univ.filter fun p => p.1 = p.2 ∨ ∃ b, r p.1 b ∧ (b, p.2) ∈ R

/-- The reflexive-transitive closure of a decidable relation on a finite type, as a `Finset`. -/
@[expose] def reflTransGenFinset : Finset (α × α) :=
  ((reflTransGenStep r)^[Fintype.card (α × α)]) ∅

theorem coe_iterate_reflTransGenStep (k : ℕ) :
    (((reflTransGenStep r)^[k] ∅ : Finset (α × α)) : Set (α × α)) =
      ((reflTransGenRule r)^[k]) ⊥ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    ext p
    simp only [reflTransGenStep, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq]
    rfl

theorem mem_reflTransGenFinset {a b : α} : (a, b) ∈ reflTransGenFinset r ↔ ReflTransGen r a b := by
  rw [← Finset.mem_coe, reflTransGenFinset, coe_iterate_reflTransGenStep,
    OrderHom.iterate_card_bot_eq_lfp, lfp_reflTransGenRule]
  rfl

end Relation
