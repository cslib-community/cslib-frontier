/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Lists
public import Mathlib.RingTheory.FiniteType

/-!
# Finitely many named generators

The programs of [AnthropicVPVNP2026] multiply their weights by generators of the ring `A` that
have names (Appendix I.1, p. 48: finitely many generators of `A`, one of which is `−1`, have
names, and every other name has the weight `0`). If `A` is a finitely generated ring, there is
such a table `θ` of the generators, with finite support, and every element of `A` is the value of
a formula in them (`Interpreter.WE.exists_table`).

## Main results

* `Interpreter.WE.exists_table`: a finitely generated ring has a finite table of generators in
  which every element is the value of a formula.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix I.1 (p. 48). Ported from the
source module `Nc.Dl.Last`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

/-- **Finitely many named generators.** A finitely generated ring `A` has a table `θ` of names of
finite support such that every element of `A` is the value of a formula in the named constants:
the name `true ^ k` has the generator `k` of `−1, g₁, …, gₙ`, and every other name the value
`0`. -/
theorem WE.exists_table (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] :
    ∃ θ : List Bool → A, (Function.support θ).Finite ∧ ∀ a, ∃ w : WE, w.val θ = a := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType ℤ A).out
  let gens : List A := (-1) :: s.toList
  let θ : List Bool → A := fun p =>
    if p = List.replicate p.length true then gens.getD p.length 0 else 0
  refine ⟨θ, ((Set.finite_lt_nat gens.length).image (List.replicate · true)).subset fun p hp => ?_,
    fun a => WE.exists_of_adjoin (p₀ := []) (by simp [θ, gens]) ?_⟩
  · by_cases h : p = List.replicate p.length true
    · refine ⟨p.length, Nat.lt_of_not_le fun hl => hp ?_, h.symm⟩
      simp [θ, ← h, List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]
    · exact absurd (ite_eq_right h) hp
  · refine Subring.closure_mono (fun x hx => ?_)
      (Algebra.adjoin_int (R := A) _ ▸ hs ▸ Algebra.mem_top)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_cons_of_mem (-1) (s.mem_toList.2 hx))
    exact ⟨List.replicate k true,
      by simp [θ, gens, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]⟩

end Cslib.Circuits.Arithmetic.Separation.Interpreter
