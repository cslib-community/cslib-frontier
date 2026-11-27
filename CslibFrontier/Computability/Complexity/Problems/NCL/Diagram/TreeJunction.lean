/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Run
import Mathlib.Data.Fin.Basic

/-!
# State updates at a one-wire tree junction

Growing a gate tree adds one internal wire between the old subtree and the new binary gate.
Its other wires are the input boundary and the single output. This shared indexing API supplies
the boundary updates and the path between the two possible internal values.

## Main definitions

* `Diagram.TreeJunction.Edge`: input wires, the single intermediate wire, and the output.
* `Diagram.TreeJunction.put`: prescribe the boundary and the intermediate bit.

## Main results

* `Diagram.TreeJunction.reverse_boundary`, `Diagram.TreeJunction.reverse_middle`: update laws.
* `Diagram.TreeJunction.reachable_put`: legal states with the same boundary are connected.
-/

public section

namespace Cslib.Complexity.NCL.Diagram.TreeJunction

/-- The product-of-diagrams edge index: inputs, the old output, and the new output. -/
abbrev Edge (n : ℕ) := Fin n ⊕ ((Empty ⊕ Fin 1) ⊕ Fin 1)

/-- The old subtree's output, which is internal after adjoining the binary gate. -/
@[expose] def middle {n : ℕ} : Edge n := .inr (.inl (.inr 0))

/-- Include the input and final output boundary in the junction. -/
@[expose] def boundary {n : ℕ} : Fin n ⊕ Fin 1 → Edge n
  | .inl i => .inl i
  | .inr i => .inr (.inr i)

/-- Combine prescribed boundary bits with one intermediate bit. -/
@[expose] def put {n : ℕ} (β : Fin n ⊕ Fin 1 → Bool) (c : Bool) : Edge n → Bool
  | .inl i => β (.inl i)
  | .inr (.inl (.inl e)) => e.elim
  | .inr (.inl (.inr _)) => c
  | .inr (.inr i) => β (.inr i)

/-- The prescribed boundary is retained exactly. -/
@[simp] theorem put_boundary {n : ℕ} (β : Fin n ⊕ Fin 1 → Bool) (c : Bool)
    (x : Fin n ⊕ Fin 1) : put β c (boundary x) = β x := by cases x <;> rfl

/-- Reversing the single intermediate wire changes just its prescribed bit. -/
theorem reverse_middle {n : ℕ} (β : Fin n ⊕ Fin 1 → Bool) (c : Bool) :
    reverse (put β c) middle = put β (!c) := by
  funext y
  rcases y with i | ((e | i) | i)
  all_goals try exact e.elim
  all_goals try cases Fin.eq_zero i
  all_goals simp [reverse, put, middle]

/-- Reversing one boundary wire retains the intermediate value. -/
theorem reverse_boundary {n : ℕ} (β : Fin n ⊕ Fin 1 → Bool) (c : Bool)
    (x : Fin n ⊕ Fin 1) : reverse (put β c) (boundary x) = put (reverse β x) c := by
  funext y
  rcases x with j | j <;> rcases y with i | ((e | i) | i)
  all_goals try exact e.elim
  all_goals try by_cases hij : i = j
  all_goals try subst i
  all_goals simp_all [boundary, reverse, put, Function.update]

/-- Two legal intermediate values with a fixed boundary are connected by at most one move. -/
theorem reachable_put {n : ℕ} {V : Type*} (G : ConstraintGraph V (Edge n))
    (allowed : Edge n → Prop) (hm : allowed middle) (β : Fin n ⊕ Fin 1 → Bool)
    (c d : Bool) (hc : G.Legal (put β c)) (hd : G.Legal (put β d)) :
    G.ReachableOn allowed (put β c) (put β d) := by
  cases c <;> cases d
  · exact .refl
  · exact .single ⟨hc, hd, middle, hm, (reverse_middle β false).symm⟩
  · exact .single ⟨hc, hd, middle, hm, (reverse_middle β true).symm⟩
  · exact .refl

/-- Changing a false coordinate to true increases every Boolean coordinate. -/
theorem le_reverse_of_false {E : Type*} [DecidableEq E] (s : E → Bool) (e : E)
    (he : s e = false) (f : E) : s f ≤ reverse s e f := by
  by_cases hf : f = e
  · subst f
    simp only [reverse_self, he, Bool.not_false, Bool.false_le]
  · rw [reverse_of_ne s hf]

/-- Build positive boundary lifts from the unchanged-middle input cases and output independence. -/
theorem positive_lift {n : ℕ} {V : Type*} (G : ConstraintGraph V (Edge n))
    (allowed : Edge n → Prop) (hm : allowed middle)
    (ι : Fin n ⊕ Fin 1 → Edge n) (P : (Fin n ⊕ Fin 1 → Bool) → Prop)
    (active : (Fin n ⊕ Fin 1 → Bool) → Bool)
    (hreverse : ∀ β c x, reverse (put β c) (ι x) = put (reverse β x) c)
    (hcanon : ∀ β, P β → G.Legal (put β (active β)))
    (hinput : ∀ β i, β (.inl i) = false → P β →
      G.Legal (put (reverse β (.inl i)) (active β)))
    (houtput : ∀ β j, active β = active (reverse β (.inr j)))
    (β : Fin n ⊕ Fin 1 → Bool) (x : Fin n ⊕ Fin 1) (_hx : β x = false)
    (hβ : P β) (hγ : P (reverse β x)) :
    ∃ u, G.ReachableOn allowed (put β (active β)) u ∧ G.Legal (reverse u (ι x)) ∧
      G.ReachableOn allowed (reverse u (ι x)) (put (reverse β x) (active (reverse β x))) := by
  refine ⟨put β (active β), .refl, ?_⟩
  rw [hreverse]
  rcases x with i | j
  · exact ⟨hinput β i _hx hβ, reachable_put G allowed hm _ _ _ (hinput β i _hx hβ) (hcanon _ hγ)⟩
  · rw [houtput β j]
    exact ⟨hcanon _ hγ, .refl⟩

end Cslib.Complexity.NCL.Diagram.TreeJunction
