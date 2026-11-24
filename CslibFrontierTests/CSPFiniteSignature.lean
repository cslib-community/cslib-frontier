/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Logics.Propositional.CSP.Boolean.FiniteSignature
public import CslibFrontier.Computability.Complexity.Problems.CSP.OneHot3

/-!
# Static six-symbol selection with infinite and repeated target symbols

The client uses the existing OneHot3 semantics and finite Boolean calculations, rather than
a hardness theorem, to exercise a non-Schaefer language. Repeating that relation over
`Nat` tests an infinite target alphabet without a target `Finite` instance. A one-symbol
target forces repetitions. Empty languages and empty nullary relations remain tractable
under the existing criterion's unary constants.
-/

public section

namespace CslibFrontierTests.CSPFiniteSignature

open Cslib.Logic Cslib.Logic.PL.CSP Cslib.Complexity.CSP

-- Each check uses exactly the unary, binary or ternary operation in the existing criterion.
private theorem oneHot_missing : ¬HasSchaeferPolymorphism OneHot3.arity OneHot3.sem := by
  unfold HasSchaeferPolymorphism HasPolymorphism IsPolymorphism booleanRelation OneHot3.arity
  simp only [Set.mem_ofPred_eq, not_or]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

example : OneHot3.sem () [true, false, false] = true ∧
    OneHot3.sem () [false, false, false] = false := by decide

-- Fintype (Fin 6) is inferred for univ; no finiteness instance for Nat is introduced.
/-- Six symbols retain failure over an infinite alphabet, with at most six distinct values. -/
theorem infinite_target_selection : ∃ symbol : Fin 6 → ℕ,
    ¬HasSchaeferPolymorphism ((fun _ : ℕ => OneHot3.arity ()) ∘ symbol)
      ((fun _ : ℕ => OneHot3.sem ()) ∘ symbol) ∧ (Finset.univ.image symbol).card ≤ 6 := by
  have h : ¬HasSchaeferPolymorphism (fun _ : ℕ => OneHot3.arity ())
      (fun _ => OneHot3.sem ()) := by
    simpa only [HasSchaeferPolymorphism, HasPolymorphism, booleanRelation,
      OneHot3.arity, OneHot3.sem, forall_const] using oneHot_missing
  obtain ⟨symbol, hs⟩ := exists_sixSymbol_not_hasSchaeferPolymorphism
    (fun _ : ℕ => OneHot3.arity ()) (fun _ => OneHot3.sem ()) h
  exact ⟨symbol, hs, by simpa using (Finset.card_image_le (s := Finset.univ) (f := symbol))⟩

example : ∃ symbol : Fin 6 → Unit,
    ¬HasSchaeferPolymorphism (fun i => OneHot3.arity (symbol i))
      (fun i => OneHot3.sem (symbol i)) ∧ ¬Function.Injective symbol := by
  obtain ⟨symbol, hs⟩ := exists_sixSymbol_not_hasSchaeferPolymorphism
    OneHot3.arity OneHot3.sem oneHot_missing
  refine ⟨symbol, hs, ?_⟩
  intro hi
  have he : (0 : Fin 6) = 1 := hi (Subsingleton.elim _ _)
  exact (by decide : (0 : Fin 6) ≠ 1) he

example : HasSchaeferPolymorphism (fun r : Empty => r.elim) (fun r => r.elim) :=
  Or.inl (fun r => r.elim)

example : ¬∃ symbol : Fin 6 → Empty,
    ¬HasSchaeferPolymorphism (fun i => (symbol i).elim) (fun i => (symbol i).elim) := by
  rintro ⟨symbol, _⟩
  exact (symbol 0).elim

-- A unary constant preserves the empty relation even when its declared arity is zero.
example : HasSchaeferPolymorphism (fun _ : Unit => 0) (fun _ _ => false) :=
  Or.inl (fun _ _ ha => ha 0)

end CslibFrontierTests.CSPFiniteSignature
