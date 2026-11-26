/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Ring.Defs
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Weighted lists

A *weighted list* is a list of pairs (weight, value) with weights in a semiring `A`: the list of
the outcomes of a computation that branches, each with the product of the weights along its
branch. This file has the three operations of such lists:

* the weighted sum of a function of the value;
* sequencing: a second computation at every value of the first one, where the weights multiply;
* a fold of a step over a list, from a state at the beginning.

Weighted lists with these operations are the writer monad of the multiplicative monoid of `A` over
lists; the file keeps the type `List (A × α)` of the pairs, which is what the statements about
programs use.

## Main definitions

* `List.weightedSum`: `∑ (w, a) ∈ l, w * G a`.
* `List.weightedBind`: first `l`, then `f` at every value.
* `List.weightedFoldl`: the weighted list of a fold.

## Main results

* `List.weightedSum_weightedBind`: the weighted sum of a sequence is the iterated weighted sum.
* `List.mem_weightedBind_iff`, `List.weightedBind_assoc`, `List.map_weightedBind`.
* `List.weightedFoldl_singleton_one`: a fold of deterministic steps is `List.foldl`.
* `List.weightedFoldl_ite`: a fold of steps that reject unless a condition holds.
* `List.mem_weightedFoldl_induction`: an invariant of the steps holds at every outcome of a fold.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3 (the semantics of the
evaluator in the proof of Theorem J.3); modules `Nc.Grp.Lang` and `Nc.Grp.Trans`.
-/

public section

namespace List

variable {A α β γ ε : Type*}

/-- The weighted sum `∑ (w, a) ∈ l, w * G a` of a function of the value. -/
@[expose] def weightedSum [Mul A] [Add A] [Zero A] (l : List (A × α)) (G : α → A) : A :=
  (l.map fun p => p.1 * G p.2).sum

/-- First `l`, then `f` at every value of `l`; the weights multiply. -/
@[expose] def weightedBind [Mul A] (l : List (A × α)) (f : α → List (A × β)) : List (A × β) :=
  l.flatMap fun p => (f p.2).map fun r => (p.1 * r.1, r.2)

/-- The weighted list of a fold: the step `f x` at every element `x` of a list, in order, from the
state `s`. -/
@[expose] def weightedFoldl [Mul A] [One A] (f : ε → β → List (A × β)) :
    List ε → β → List (A × β)
  | [], s => [(1, s)]
  | x :: xs, s => (f x s).weightedBind (weightedFoldl f xs)

section Sum

variable [Mul A] [AddMonoid A]

@[simp] theorem weightedSum_nil (G : α → A) : ([] : List (A × α)).weightedSum G = 0 := rfl

@[simp] theorem weightedSum_cons (p : A × α) (l : List (A × α)) (G : α → A) :
    (p :: l).weightedSum G = p.1 * G p.2 + l.weightedSum G := rfl

theorem weightedSum_append (l l' : List (A × α)) (G : α → A) :
    (l ++ l').weightedSum G = l.weightedSum G + l'.weightedSum G := by
  simp [weightedSum]

theorem weightedSum_congr {l : List (A × α)} {G G' : α → A} (h : ∀ p ∈ l, G p.2 = G' p.2) :
    l.weightedSum G = l.weightedSum G' :=
  congrArg sum (map_congr_left fun p hp => by rw [h p hp])

/-- The weighted sum over the images of the values. -/
theorem weightedSum_map (l : List (A × α)) (e : α → β) (G : β → A) :
    (l.map (Prod.map id e)).weightedSum G = l.weightedSum fun a => G (e a) := by
  simp [weightedSum, Function.comp_def]

end Sum

theorem weightedSum_singleton_one [NonAssocSemiring A] (a : α) (G : α → A) :
    [((1 : A), a)].weightedSum G = G a := by
  simp

section NonUnitalSemiring

variable [NonUnitalSemiring A]

/-- A common factor of the weights. -/
theorem weightedSum_map_mul_left (c : A) (l : List (A × α)) (G : α → A) :
    (l.map fun r => (c * r.1, r.2)).weightedSum G = c * l.weightedSum G := by
  simp only [weightedSum, map_map, Function.comp_def, mul_assoc, sum_map_mul_left]

/-- The weighted sum of a sequence of two computations. -/
theorem weightedSum_weightedBind (l : List (A × α)) (f : α → List (A × β)) (G : β → A) :
    (l.weightedBind f).weightedSum G = l.weightedSum fun a => (f a).weightedSum G := by
  simp only [weightedSum, weightedBind, sum_map_flatMap, map_map, Function.comp_def, mul_assoc,
    sum_map_mul_left]

end NonUnitalSemiring

section Bind

theorem mem_weightedBind_iff [Mul A] {l : List (A × α)} {f : α → List (A × β)} {p : A × β} :
    p ∈ l.weightedBind f ↔ ∃ a ∈ l, ∃ r ∈ f a.2, p = (a.1 * r.1, r.2) := by
  simp [weightedBind, eq_comm]

/-- Mapping the values of a sequence maps the values of its second part. -/
theorem map_weightedBind [Mul A] (l : List (A × α)) (f : α → List (A × β)) (e : β → γ) :
    (l.weightedBind f).map (Prod.map id e) =
      l.weightedBind fun a => (f a).map (Prod.map id e) := by
  simp [weightedBind, map_flatMap, Function.comp_def]

theorem weightedBind_assoc [Semigroup A] (l : List (A × α)) (f : α → List (A × β))
    (g : β → List (A × γ)) :
    (l.weightedBind f).weightedBind g = l.weightedBind fun a => (f a).weightedBind g := by
  simp only [weightedBind, flatMap_assoc, flatMap_map, map_flatMap, map_map, Function.comp_def,
    mul_assoc]

variable [MulOneClass A]

@[simp] theorem weightedBind_singleton_one (a : α) (f : α → List (A × β)) :
    [((1 : A), a)].weightedBind f = f a := by
  simp [weightedBind]

/-- A sequence after a list of values of weight `1`. -/
theorem weightedBind_map_one (l : List α) (g : α → β) (f : β → List (A × γ)) :
    (l.map fun t => ((1 : A), g t)).weightedBind f = l.flatMap fun t => f (g t) := by
  simp [weightedBind, flatMap_map]

end Bind

section Foldl

variable [MulOneClass A]

@[simp] theorem weightedFoldl_nil (f : ε → β → List (A × β)) (s : β) :
    weightedFoldl f [] s = [(1, s)] := rfl

@[simp] theorem weightedFoldl_cons (f : ε → β → List (A × β)) (x : ε) (xs : List ε) (s : β) :
    weightedFoldl f (x :: xs) s = (f x s).weightedBind (weightedFoldl f xs) := rfl

/-- A fold of deterministic steps. -/
theorem weightedFoldl_singleton_one (g : ε → β → β) (xs : List ε) (s : β) :
    weightedFoldl (A := A) (fun x s => [(1, g x s)]) xs s =
      [(1, xs.foldl (fun s x => g x s) s)] := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- A fold of steps that reject unless their element satisfies `p`, and otherwise go on
deterministically. -/
theorem weightedFoldl_ite (p : ε → Prop) [DecidablePred p] (g : ε → β → β) (xs : List ε)
    (s : β) :
    weightedFoldl (A := A) (fun x s => if p x then [(1, g x s)] else []) xs s =
      if ∀ x ∈ xs, p x then [(1, xs.foldl (fun s x => g x s) s)] else [] := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih => by_cases hx : p x <;> simp [hx, ih, weightedBind]

/-- An invariant of the steps, with a counter of the steps, holds at every outcome of a fold. -/
theorem mem_weightedFoldl_induction {f : ε → β → List (A × β)} {Inv : ℕ → β → Prop}
    {xs : List ε} {s : β} {m : ℕ}
    (h : ∀ x ∈ xs, ∀ s m, Inv m s → ∀ q ∈ f x s, Inv (m + 1) q.2) (hs : Inv m s) :
    ∀ q ∈ weightedFoldl f xs s, Inv (m + xs.length) q.2 := by
  induction xs generalizing s m with
  | nil => simpa using hs
  | cons x xs ih =>
    intro q hq
    obtain ⟨a, ha, r, hr, rfl⟩ := mem_weightedBind_iff.1 hq
    have := ih (fun y hy => h y (mem_cons_of_mem _ hy)) (h x mem_cons_self s m hs a ha) r hr
    rw [length_cons, ← Nat.add_assoc, Nat.add_right_comm]
    exact this

end Foldl

end List
