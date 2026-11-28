/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable
import CslibFrontier.Computability.Complexity.Classes.P.Countable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Polynomial-time solvable search problems need not be checkable

Goldreich's class `PF` [Goldreich, Definition 2.2][Goldreich2006DraftR1] consists of the
polynomially bounded relations whose search problem is solved by a polynomial-time algorithm. Its
class `PC` (Definition 2.3) consists of the polynomially bounded relations that are decidable in
polynomial time; in this library `PC` is `Cslib.Complexity.FNP`. Exercise 2.1 asks to show that
`PF` is not contained in `PC`.

The library's `Cslib.Complexity.FPSearch` is `PF ∩ PC` (it asks for `FNP` membership), so the
separation is stated here with `PF` membership spelled out: a length bound on solutions and a
polynomial-time `Cslib.Complexity.SolvesSearch` solver, with outputs encoded by
`encOption encBits`.

The witness is the guideline's. For a set `S`, the relation `Cslib.Complexity.membershipSearch S`
has the solution `[true]` for every instance and the solution `[false]` exactly for the instances
in `S`. The constant algorithm returning `[true]` solves it, but a polynomial-time decider of the
relation decides `S` in polynomial time by asking whether `[false]` is a solution
(`Cslib.Complexity.mem_P_of_membershipSearch_mem_FNP`). With `S` the undecidable self-halting
problem `Turing.MultiTapeTM.selfHaltingProblem` on words, the relation is not in `PC`.

## Main definitions

* `Cslib.Complexity.membershipSearch`: the guideline relation `{(x, 1)} ∪ {(x, 0) : x ∈ S}`.

## Main results

* `Cslib.Complexity.mem_P_of_membershipSearch_mem_FNP`: if `membershipSearch S` is in `PC`, then
  `S ∈ P`.
* `Cslib.Complexity.exists_polyTimeSolvable_not_mem_FNP`: Goldreich, Exercise 2.1.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2006DraftR1],
  Definitions 2.2 and 2.3 and Exercise 2.1 (draft r1.pdf of December 2006, printed pp. 54–55
  and 105).
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool} {S : Set α}

/-- The relation `{(x, 1) : x} ∪ {(x, 0) : x ∈ S}` of the guideline of
[Goldreich, Exercise 2.1][Goldreich2006DraftR1]: every instance has the solution `[true]`, and the
instances in `S` also have the solution `[false]`. -/
@[expose] def membershipSearch (S : Set α) (a : α) (w : List Bool) : Prop :=
  w = [true] ∨ (w = [false] ∧ a ∈ S)

/-- Solutions of `membershipSearch S` have length one. -/
theorem length_eq_one_of_membershipSearch {a : α} {w : List Bool}
    (h : membershipSearch S a w) : w.length = 1 := by
  rcases h with rfl | ⟨rfl, -⟩ <;> rfl

/-- The constant algorithm returning `[true]` solves `membershipSearch S`. -/
theorem solvesSearch_membershipSearch :
    SolvesSearch (membershipSearch S) fun _ => some [true] :=
  solvesSearch_some fun _ => .inl rfl

/-- **A polynomial-time checker of `membershipSearch S` decides `S`.** If the relation is in
`FNP` (Goldreich's `PC`), then `S ∈ P`: `a ∈ S` exactly when `[false]` is a solution of `a`. -/
theorem mem_P_of_membershipSearch_mem_FNP (h : membershipSearch S ∈ FNP enc) : S ∈ P enc := by
  obtain ⟨-, V, hV, hRV⟩ := mem_FNP.mp h
  refine mem_P.mpr ⟨fun a => V (a, [false]), hV.comp (id'.prod (const [false])), fun a => ?_⟩
  rw [← hRV]
  simp [membershipSearch]

/-- **`PF` is not contained in `PC`** [Goldreich, Exercise 2.1][Goldreich2006DraftR1]. Some
relation `R` on words is in Goldreich's `PF` (Definition 2.2): its solutions are polynomially
bounded, and a polynomial-time algorithm returns a solution of every instance that has one and
`none` on the others. Yet `R` is not in `FNP`, which is Goldreich's `PC` (Definition 2.3). The
witness is `membershipSearch` of the undecidable self-halting problem. -/
theorem exists_polyTimeSolvable_not_mem_FNP :
    ∃ R : List Bool → List Bool → Prop,
      (∃ p : Polynomial ℕ, ∀ x y, R x y → y.length ≤ p.eval x.length) ∧
        (∃ A : List Bool → Option (List Bool),
          ComputableInPolyTime A encBits (encOption encBits) ∧ SolvesSearch R A) ∧
        R ∉ FNP encBits :=
  ⟨membershipSearch selfHaltingProblem,
    ⟨1, fun _ _ h => by simp [length_eq_one_of_membershipSearch h]⟩,
    ⟨_, (optionSome encBits).comp (const [true]), solvesSearch_membershipSearch⟩,
    fun h => not_isDecidable_selfHaltingProblem
      (isDecidable_of_mem_P (mem_P_of_membershipSearch_mem_FNP h))⟩

end Cslib.Complexity
