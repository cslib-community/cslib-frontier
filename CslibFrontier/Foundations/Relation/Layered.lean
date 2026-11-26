/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Relation.RelatesWithinSteps
import CslibFrontier.Foundations.Relation.Transport
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Layering a bounded reachability problem

A vertex records its time layer and its original vertex. Each edge advances exactly one
layer and either follows the original relation or stays at the original vertex. Thus a walk
of at most `T` original steps is represented at layer `T`, including computations that finish
early. The lifted relation has no self edges, even when the original relation does.

This is the bounded-walk construction used by the native configuration-graph reduction in
#6747, not an unambiguity or resource theorem for a reachability algorithm.

## Main results

* `Relation.LayeredVertex.reachable_iff`: final-layer reachability is bounded reachability.
-/

public section

namespace Relation

/-- A vertex together with its time layer in a layered reachability graph. -/
structure LayeredVertex (α : Type*) where
  /-- The time layer. -/
  layer : ℕ
  /-- The original vertex. -/
  vertex : α
  deriving DecidableEq

namespace LayeredVertex

variable {α : Type*} {r : α → α → Prop} {T : ℕ}

/-- Edges advance one layer, before the horizon, and follow an original edge or wait.
Waiting changes the layered vertex and therefore introduces no self edge. -/
@[expose] def Step (r : α → α → Prop) (T : ℕ)
    (a b : LayeredVertex α) : Prop :=
  b.layer = a.layer + 1 ∧ a.layer < T ∧ ReflGen r a.vertex b.vertex

/-- Layering turns even a reflexive original relation into an irreflexive relation. -/
theorem step_irrefl (a : LayeredVertex α) : ¬ Step r T a a := by
  rintro ⟨h, -⟩
  omega

private theorem lift_walk {a b : α} {n : ℕ}
    (h : RelatesInSteps (ReflGen r) a b n) (hn : n ≤ T) :
    ReflTransGen (Step r T) ⟨0, a⟩ ⟨n, b⟩ := by
  induction h with
  | refl => exact .refl
  | tail b c n h he ih =>
    exact (ih (by omega)).tail ⟨rfl, by change n < T; omega, he⟩

/-- Reachability at the final layer is exactly reachability in at most the horizon many
original steps. In particular, early termination can be padded without changing the answer. -/
theorem reachable_iff (a b : α) :
    ReflTransGen (Step r T) ⟨0, a⟩ ⟨T, b⟩ ↔ RelatesWithinSteps r a b T := by
  rw [relatesWithinSteps_iff_relatesInSteps_reflGen]
  refine ⟨fun h => ?_, fun h => lift_walk h le_rfl⟩
  have invariant {v : LayeredVertex α} (hv : ReflTransGen (Step r T) ⟨0, a⟩ v) :
      RelatesInSteps (ReflGen r) a v.vertex v.layer := by
    induction hv with
    | refl => exact .refl a
    | tail _ he ih => exact he.1 ▸ .tail _ _ _ _ ih he.2.2
  exact invariant h

/-- Vertices in the finite window of layers from zero through the horizon. -/
abbrev Bounded (α : Type*) (T : ℕ) := {v : LayeredVertex α // v.layer ≤ T}

/-- The finite window as a bounded layer index and an original vertex. -/
@[expose] def boundedEquiv (α : Type*) (T : ℕ) : Bounded α T ≃ Fin (T + 1) × α where
  toFun v := (⟨v.val.layer, by have := v.property; omega⟩, v.val.vertex)
  invFun v := ⟨⟨v.1.val, v.2⟩, Nat.le_of_lt_succ v.1.isLt⟩
  left_inv v := by cases v with | mk v h => cases v; rfl
  right_inv v := by cases v; rfl

noncomputable instance {α : Type*} [Fintype α] (T : ℕ) : Fintype (Bounded α T) :=
  Fintype.ofEquiv (Fin (T + 1) × α) (boundedEquiv α T).symm

/-- The finite layered window contains one copy of the original vertices in each layer. -/
theorem card_bounded {α : Type*} (T : ℕ) : Nat.card (Bounded α T) = (T + 1) * Nat.card α := by
  rw [Nat.card_congr (boundedEquiv α T), Nat.card_prod, Nat.card_fin]

/-- Restricting to the finite window loses no layered walk between vertices in the window. -/
theorem bounded_reachable_iff (a b : Bounded α T) :
    ReflTransGen (fun u v : Bounded α T => Step r T u.val v.val) a b ↔
      ReflTransGen (Step r T) a.val b.val := by
  refine reflTransGen_onFun_iff Subtype.val_injective fun v hv => ⟨⟨v, ?_⟩, rfl⟩
  cases hv with
  | refl => exact a.property
  | tail _ hstep => exact hstep.1.trans_le (Nat.succ_le_of_lt hstep.2.1)

end LayeredVertex

end Relation
