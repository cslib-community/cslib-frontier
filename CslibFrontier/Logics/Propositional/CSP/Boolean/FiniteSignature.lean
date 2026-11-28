/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Boolean
import Mathlib.Data.Fin.VecNotation

/-!
# Six original symbols retain failure of the Schaefer operations

Each failed common operation has an actual original relation witnessing its failure.
Selecting these six symbols gives a finite source signature even when the original
encoded target alphabet is infinite. Symbols may repeat, and their arities are unrestricted.
The construction is static; it does not search a language at runtime.
-/

public section

namespace Cslib.Logic.PL.CSP

/-- Failure of all six common Schaefer operations is already witnessed by six original
relation symbols. The map need not be injective, and no finite target alphabet is assumed. -/
theorem exists_sixSymbol_not_hasSchaeferPolymorphism {Rel : Type}
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬HasSchaeferPolymorphism arity sem) :
    ∃ symbol : Fin 6 → Rel,
      ¬HasSchaeferPolymorphism (fun i => arity (symbol i)) (fun i => sem (symbol i)) := by
  classical
  simp only [HasSchaeferPolymorphism, not_or, HasPolymorphism, not_forall] at h
  obtain ⟨⟨r₀, h₀⟩, ⟨r₁, h₁⟩, ⟨r₂, h₂⟩, ⟨r₃, h₃⟩, ⟨r₄, h₄⟩, ⟨r₅, h₅⟩⟩ := h
  refine ⟨![r₀, r₁, r₂, r₃, r₄, r₅], ?_⟩
  rintro (hz | ho | ha | hr | hm | hp)
  exacts [h₀ (hz 0), h₁ (ho 1), h₂ (ha 2), h₃ (hr 3), h₄ (hm 4), h₅ (hp 5)]

end Cslib.Logic.PL.CSP
