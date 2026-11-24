/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Basic

/-!
# Checked runs on selected edges

A run lists the edges to reverse and checks legality before and after every move. An edge
predicate restricts the coordinates that may change, so the same checker handles internal
diagram moves and control protocols that expose selected boundary wires.

## Main definitions

* `Cslib.Complexity.NCL.reverseAll`: execute a list of reversals.
* `Cslib.Complexity.NCL.ConstraintGraph.StepOn`,
  `Cslib.Complexity.NCL.ConstraintGraph.ReachableOn`: moves on selected edges and their closure.
* `Cslib.Complexity.NCL.ConstraintGraph.Run`: a checked run on those edges.

## Main results

* `Cslib.Complexity.NCL.ConstraintGraph.Run.reachableOn`: a checked run gives a path.
* `Cslib.Complexity.NCL.ConstraintGraph.ReachableOn.symm`: restricted runs can be undone.

## References

* The move rule is that of [Hearn and Demaine][HearnDemaine2005, Section 2.1].
-/

public section

namespace Cslib.Complexity.NCL

/-- Reverse the listed edges one after another. -/
@[expose] def reverseAll {E : Type*} [DecidableEq E] (t : E → Bool) : List E → E → Bool
  | [] => t
  | y :: ys => reverseAll (reverse t y) ys

namespace ConstraintGraph

variable {V E : Type*} [DecidableEq E] (G : ConstraintGraph V E) (allowed : E → Prop)

/-- A legal move reversing an edge selected by `allowed`. -/
@[expose] def StepOn (s t : E → Bool) : Prop :=
  G.Legal s ∧ G.Legal t ∧ ∃ e, allowed e ∧ t = reverse s e

/-- Reachability using only the selected edges. -/
abbrev ReachableOn : (E → Bool) → (E → Bool) → Prop :=
  Relation.ReflTransGen (G.StepOn allowed)

/-- A certificate checking each selected reversal and both adjacent configurations. -/
@[expose] def Run : (E → Bool) → List E → Prop
  | _, [] => True
  | s, e :: es => allowed e ∧ G.Legal s ∧ G.Legal (reverse s e) ∧
      Run (reverse s e) es

instance instDecidableRun [Fintype V] [DecidablePred allowed] :
    ∀ (s : E → Bool) (es : List E), Decidable (G.Run allowed s es)
  | _, [] => inferInstanceAs (Decidable True)
  | s, e :: es =>
    letI := instDecidableRun (reverse s e) es
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

variable {G allowed}

/-- Every move restricted to selected edges is a move of the graph. -/
theorem StepOn.step {s t : E → Bool} (h : G.StepOn allowed s t) : G.Step s t := by
  obtain ⟨hs, ht, e, _, he⟩ := h
  exact ⟨hs, ht, e, he⟩

/-- A restricted path is a path of the graph. -/
theorem ReachableOn.reachable {s t : E → Bool} (h : G.ReachableOn allowed s t) :
    G.Reachable s t := Relation.ReflTransGen.mono (fun _ _ h => h.step) _ _ h

/-- Lift a selected-edge path along a map that preserves its reversals and whose images are
legal at every reachable state. -/
theorem ReachableOn.map {V' E' : Type*} [DecidableEq E']
    {G' : ConstraintGraph V' E'} {allowed' : E' → Prop} {s t : E → Bool}
    (h : G.ReachableOn allowed s t) (f : (E → Bool) → E' → Bool) (edge : E → E')
    (hlegal : ∀ u, G.ReachableOn allowed s u → G'.Legal (f u))
    (hreverse : ∀ u e, allowed e → f (reverse u e) = reverse (f u) (edge e))
    (hallowed : ∀ e, allowed e → allowed' (edge e)) :
    G'.ReachableOn allowed' (f s) (f t) := by
  induction h with
  | refl => exact .refl
  | @tail u v hr hs ih =>
    have hu := hlegal u hr
    have hv := hlegal v (hr.tail hs)
    obtain ⟨_, _, e, he, rfl⟩ := hs
    exact ih.tail ⟨hu, hv, edge e, hallowed e he, hreverse u e he⟩

/-- Undo a restricted move using the same selected edge. -/
theorem StepOn.symm {s t : E → Bool} (h : G.StepOn allowed s t) : G.StepOn allowed t s := by
  obtain ⟨hs, ht, e, he, rfl⟩ := h
  exact ⟨ht, hs, e, he, (reverse_reverse s e).symm⟩

/-- Undo a restricted path without changing which edges may move. -/
theorem ReachableOn.symm {s t : E → Bool} (h : G.ReachableOn allowed s t) :
    G.ReachableOn allowed t s := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.head hstep.symm

/-- An unselected edge has the same direction before and after a restricted move. -/
theorem StepOn.apply_eq {s t : E → Bool} (h : G.StepOn allowed s t) {e : E}
    (he : ¬allowed e) : s e = t e := by
  obtain ⟨_, _, f, hf, rfl⟩ := h
  have hef : e ≠ f := by
    rintro rfl
    exact he hf
  exact (reverse_of_ne s hef).symm

/-- Unselected edges stay fixed along the entire restricted path. -/
theorem ReachableOn.apply_eq {s t : E → Bool} (h : G.ReachableOn allowed s t) {e : E}
    (he : ¬allowed e) : s e = t e := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hstep.apply_eq he)

/-- Every checked run is a path on its selected edges. -/
theorem Run.reachableOn : ∀ {s : E → Bool} {es : List E}, G.Run allowed s es →
    G.ReachableOn allowed s (reverseAll s es)
  | _, [], _ => .refl
  | _, _ :: _, ⟨he, hs, ht, h⟩ =>
    Relation.ReflTransGen.head ⟨hs, ht, _, he, rfl⟩ h.reachableOn

end ConstraintGraph

end Cslib.Complexity.NCL
