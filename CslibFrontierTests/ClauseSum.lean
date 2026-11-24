/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.ClauseSum

/-! Tests of clause sums under ordinary imports:

* one-hot encodings of a function on a finite domain;
* a clause sum with one fixed bit, and its monomial extension;
* a clause sum over the functions `Unit → Fin 3`, and its reduction to bits. -/

set_option linter.privateModule false

namespace CslibFrontierTests.ClauseSum

open Cslib.Circuits.Arithmetic MvPolynomial

/-- The one-hot encoding of `g : Unit → Fin 3` with `g () = 1` sets only the bit `⟨(), 1⟩`. -/
example : Pi.oneHot (E := fun _ : Unit => Fin 3) (fun _ => 1) ⟨(), 1⟩ = true ∧
    Pi.oneHot (E := fun _ : Unit => Fin 3) (fun _ => 1) ⟨(), 2⟩ = false := by
  decide

/-- A family of bits on `Unit × Fin 3` with two set bits is no one-hot encoding. -/
example : ¬ ∃ g, Pi.oneHot (E := fun _ : Unit => Fin 3) g = fun p => decide (p.2 ≠ 0) := by
  rw [Pi.exists_oneHot_eq_iff]
  intro h
  obtain ⟨e, -, he⟩ := h ()
  have h1 := he 1 (by decide)
  have h2 := he 2 (by decide)
  exact absurd (h1.trans h2.symm) (by decide)

/-- One clause "the fixed bit and the hidden bit are set", with weight `5`. -/
def lits₁ : Unit → List ((Fin 1 ⊕ Fin 1) × Bool) := fun _ => [(.inl 0, true), (.inr 0, true)]

/-- With the fixed bit set, the hidden bit gives `5 + 1`; with it clear, `1 + 1`. -/
example : clauseSumWith lits₁ (fun _ => (5 : ℤ)) (fun _ => true) = 6 ∧
    clauseSumWith lits₁ (fun _ => (5 : ℤ)) (fun _ => false) = 2 := by
  decide

/-- With the fixed bit as a variable, the clause sum is `2 + 6 X₀`, of degree `1`. -/
example : (clauseSum (withInputs lits₁) (inputWeights fun _ => (5 : ℤ))).totalDegree ≤ 1 := by
  rw [clauseSum_withInputs]
  refine totalDegree_monomialExtension_le _ fun u _ => ?_
  exact (Finset.card_le_univ _).trans (by simp)

/-- One clause "`g () = 1`" with weight `2`, over the functions `g : Unit → Fin 3`: `2 + 1 + 1`. -/
def lits₂ : Unit → List ((Empty ⊕ Σ _ : Unit, Fin 3) × Bool) := fun _ => [(.inr ⟨(), 1⟩, true)]

example : domainClauseSum lits₂ (fun _ => (2 : ℤ)) Empty.elim = 4 := by
  decide

/-- The same as a clause sum over the one-hot bits, with weights in the semiring `ℕ`. -/
example : clauseSumWith (oneHotLits lits₂) (oneHotWeights fun _ => (2 : ℕ)) Empty.elim = 4 := by
  rw [← domainClauseSum_eq_clauseSumWith]
  decide

end CslibFrontierTests.ClauseSum
