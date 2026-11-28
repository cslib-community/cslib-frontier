/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.Simulation
public import Mathlib.Data.Fintype.EquivFin

/-!
# Assembling local realizations

A component has shared boundary bits and a private state. Its internal moves keep the boundary.
A realization supplies a canonical private state and, for each permitted boundary reversal, an
internal preparation, the boundary reversal, and an internal cleanup. Components may share any
number of boundary bits.

The product construction prepares every component in turn, reverses the shared bit once, and
cleans up every component. Thus the local contracts suffice for global reachability, including
when the two ends of an edge both require preparation [HearnDemaine2005, Section 4].

## Main definitions

* `Component`: a system with boundary bits and private state.
* `Realizes`: a component implements one constraint vertex.
* `GraphRealizes`: its canonical states need only cover globally legal source boundaries.
* `Assembly.Model`: the product of components with shared boundary bits.

## Main results

* `Assembly.Model.graphSimulation`: the common graph-relative assembly scheduler.
* `Assembly.Model.simulation`: open realizations instantiate that scheduler.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL

open Relation

universe u v w

variable {V : Type u} {E : Type v}

/-- A local component with shared boundary bits and private state. -/
structure Component (E : Type v) where
  /-- The private state, disjoint from other components' private states. -/
  State : Type w
  /-- The legal private states for a fixed boundary orientation. -/
  Legal : (E → Bool) → State → Prop
  /-- An internal move, with the boundary held fixed. -/
  InnerStep : (E → Bool) → State → State → Prop

namespace Component

/-- A legal internal move at a fixed boundary. -/
@[expose] def Step (C : Component E) (s : E → Bool) (x y : C.State) : Prop :=
  C.Legal s x ∧ C.Legal s y ∧ C.InnerStep s x y

/-- Internal paths preserve legality, including the empty path. -/
theorem legal_of_reachable (C : Component E) {s : E → Bool} {x y : C.State}
    (h : ReflTransGen (C.Step s) x y) (hx : C.Legal s x) : C.Legal s y := by
  cases h with
  | refl => exact hx
  | tail _ hxy => exact hxy.2.1

end Component

/-- An open implementation of one vertex. The boundary bit is changed only between the
preparation and cleanup paths. Unused boundary bits can be ignored by the component. -/
structure Realizes [DecidableEq E] (C : Component E) (spec : Vertex E) where
  /-- A canonical private state for each boundary orientation. -/
  canon : (E → Bool) → C.State
  /-- Every legal private state satisfies the vertex constraint. -/
  sound {s x} : C.Legal s x → spec.Sat s
  /-- A permitted boundary has a legal canonical private state. -/
  legal_canon {s} : spec.Sat s → C.Legal s (canon s)
  /-- Preparation and cleanup for a permitted boundary reversal. -/
  move {s} (e : E) : spec.Sat s → spec.Sat (reverse s e) →
    ∃ u, ReflTransGen (C.Step s) (canon s) u ∧ C.Legal (reverse s e) u ∧
      ReflTransGen (C.Step (reverse s e)) u (canon (reverse s e))

/-- A local realization whose canonical states are required only at globally legal source
boundaries. Its soundness remains local to the implemented constraint vertex. -/
structure GraphRealizes [DecidableEq E] (G : ConstraintGraph V E)
    (C : Component E) (v : V) where
  /-- A total choice of private state for every boundary orientation. -/
  canon : (E → Bool) → C.State
  /-- Every legal private state satisfies the implemented vertex. -/
  sound {s x} : C.Legal s x → (G v).Sat s
  /-- A globally legal boundary has a legal canonical state. -/
  legal_canon {s} : G.Legal s → C.Legal s (canon s)
  /-- Preparation and cleanup for a globally legal boundary reversal. -/
  move {s} (e : E) : G.Legal s → G.Legal (reverse s e) →
    ∃ u, ReflTransGen (C.Step s) (canon s) u ∧ C.Legal (reverse s e) u ∧
      ReflTransGen (C.Step (reverse s e)) u (canon (reverse s e))

/-- An open realization supplies the graph-relative contract at its source vertex. -/
@[expose] def Realizes.toGraphRealizes [DecidableEq E] {G : ConstraintGraph V E}
    {C : Component E} {v : V} (R : Realizes C (G v)) : GraphRealizes G C v where
  canon := R.canon
  sound := R.sound
  legal_canon hs := R.legal_canon (hs v)
  move e hs ht := R.move e (hs v) (ht v)

namespace Assembly

/-- Components indexed by the nodes of a finite assembly shape. -/
structure Model (V : Type u) (E : Type v) where
  /-- The component at each node. -/
  part : V → Component.{v, w} E

namespace Model

variable (M : Model.{u, v, w} V E)

/-- A product state: one shared orientation and all private component states. -/
structure State where
  /-- The bits shared by the components. -/
  boundary : E → Bool
  /-- The private state of each component. -/
  inner : (v : V) → (M.part v).State

/-- Every component is locally legal at the shared boundary. -/
@[expose] def Legal (x : M.State) : Prop := ∀ v, (M.part v).Legal x.boundary (x.inner v)

variable [DecidableEq V] [DecidableEq E]

/-- The product moves: a private move in one component, or one shared boundary reversal. -/
inductive Step : M.State → M.State → Prop
  /-- An internal move changes only one private state. -/
  | inner (s : E → Bool) (x : (v : V) → (M.part v).State) (v : V)
      (y : (M.part v).State) (hl : M.Legal ⟨s, x⟩)
      (hm : (M.part v).Step s (x v) y) :
      Step ⟨s, x⟩ ⟨s, Function.update x v y⟩
  /-- A shared bit is reversed when every incident component permits it. -/
  | flip (s : E → Bool) (x : (v : V) → (M.part v).State) (e : E)
      (hl : M.Legal ⟨s, x⟩) (hr : M.Legal ⟨reverse s e, x⟩) :
      Step ⟨s, x⟩ ⟨reverse s e, x⟩

/-- Product moves start and end at legal states. -/
theorem Step.legal {x y : M.State} (h : M.Step x y) : M.Legal x ∧ M.Legal y := by
  cases h with
  | inner s x v y hl hm =>
    refine ⟨hl, fun w => ?_⟩
    by_cases hw : w = v
    · subst w
      simpa only [Function.update_self] using hm.2.1
    · simpa only [Function.update_of_ne hw] using hl w
  | flip _ _ _ hl hr => exact ⟨hl, hr⟩

/-- Product reachability from a legal state ends at a legal state. -/
theorem legal_of_reachable {x y : M.State} (h : ReflTransGen M.Step x y) (hx : M.Legal x) :
    M.Legal y := by
  rcases h.cases_tail with rfl | ⟨_, _, hy⟩
  · exact hx
  · exact (Step.legal M hy).2

private theorem reachable_update (s : E → Bool) (x : (v : V) → (M.part v).State)
    (v : V) {y : (M.part v).State} (hl : M.Legal ⟨s, x⟩)
    (h : ReflTransGen ((M.part v).Step s) (x v) y) :
    ReflTransGen M.Step ⟨s, x⟩ ⟨s, Function.update x v y⟩ := by
  induction h with
  | refl => simpa only [Function.update_eq_self] using
      (ReflTransGen.refl : ReflTransGen M.Step (State.mk s x) (State.mk s x))
  | @tail y z _ hyz ih =>
    have hl' := legal_of_reachable M ih hl
    have hm : (M.part v).Step s ((Function.update x v y) v) z := by
      simpa only [Function.update_self] using hyz
    simpa only [Function.update_idem] using ih.tail (Step.inner s _ v z hl' hm)

private theorem reachable_private [Finite V] (s : E → Bool)
    (x y : (v : V) → (M.part v).State) (hx : M.Legal ⟨s, x⟩)
    (h : ∀ v, ReflTransGen ((M.part v).Step s) (x v) (y v)) :
    ReflTransGen M.Step ⟨s, x⟩ ⟨s, y⟩ := by
  let := Fintype.ofFinite V
  have aux : ∀ (vs : Finset V), ∃ z : (v : V) → (M.part v).State,
      ReflTransGen M.Step ⟨s, x⟩ ⟨s, z⟩ ∧
        (∀ v ∈ vs, z v = y v) ∧ (∀ v ∉ vs, z v = x v) := by
    intro vs
    induction vs using Finset.induction_on with
    | empty => exact ⟨x, .refl, by simp, by simp⟩
    | @insert v vs hv ih =>
      obtain ⟨z, hp, hy, hz⟩ := ih
      have hl := legal_of_reachable M hp hx
      have hr : ReflTransGen ((M.part v).Step s) (z v) (y v) := hz v hv ▸ h v
      refine ⟨Function.update z v (y v), hp.trans (reachable_update M s z v hl hr), ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact Function.update_self ..
        · simpa only [Function.update_of_ne (ne_of_mem_of_not_mem hw hv)] using hy w hw
      · intro w hw
        have hw' : w ≠ v ∧ w ∉ vs := by simpa only [Finset.mem_insert, not_or] using hw
        simpa only [Function.update_of_ne hw'.1] using hz w hw'.2
  obtain ⟨z, hp, hy, -⟩ := aux Finset.univ
  have heq : z = y := funext fun v => hy v (Finset.mem_univ v)
  exact heq ▸ hp

/-- Canonical product states from graph-relative local realizations. -/
@[expose] def graphCanon (G : ConstraintGraph V E) (real : ∀ v, GraphRealizes G (M.part v) v)
    (s : E → Bool) : M.State := ⟨s, fun v => (real v).canon s⟩

/-- Graph-relative realizations assemble by preparing every component before one shared flip
and then cleaning up every component. -/
@[expose] def graphSimulation [Fintype V] (G : ConstraintGraph V E)
    (real : ∀ v, GraphRealizes G (M.part v) v) : Simulation G.Step (Within M.Step M.Legal) where
  abs := State.boundary
  enc := M.graphCanon G real
  abs_enc _ := rfl
  step_abs := by
    rintro _ _ ⟨_, h⟩
    cases h with
    | inner => exact .refl
    | flip s x e hl hr =>
      exact .single ⟨fun v => (real v).sound (hl v),
        fun v => (real v).sound (hr v), e, rfl⟩
  step_enc := by
    rintro s _ ⟨hs, ht, e, rfl⟩
    choose u hp hl hq using fun v => (real v).move e hs ht
    have hx : M.Legal (M.graphCanon G real s) := fun v => (real v).legal_canon hs
    have hp' := reachable_private M s _ u hx hp
    have hu : M.Legal ⟨s, u⟩ := fun v =>
      (M.part v).legal_of_reachable (hp v) (hx v)
    have hq' := reachable_private M (reverse s e) u _ hl hq
    have hr := hp'.trans ((ReflTransGen.single (Step.flip s u e hu hl)).trans hq')
    exact ReflTransGen.mono (fun _ _ h => ⟨(Step.legal M h).1, h⟩) _ _ hr

/-- Canonical product states use the local canonical state at every node. -/
@[expose] def canon (G : ConstraintGraph V E) (real : ∀ v, Realizes (M.part v) (G v))
    (s : E → Bool) : M.State := ⟨s, fun v => (real v).canon s⟩

/-- Open local realizations use the same graph-relative preparation and cleanup engine. -/
@[expose] def simulation [Fintype V] (G : ConstraintGraph V E)
    (real : ∀ v, Realizes (M.part v) (G v)) : Simulation G.Step (Within M.Step M.Legal) :=
  M.graphSimulation G (fun v => (real v).toGraphRealizes)

end Model

end Assembly

end Cslib.Complexity.NCL
