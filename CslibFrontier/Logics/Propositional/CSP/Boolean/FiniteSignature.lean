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
  simp only [HasSchaeferPolymorphism, not_or, HasPolymorphism] at h
  obtain ⟨hzero, hone, hand, hor, hmajority, hminority⟩ := h
  obtain ⟨rzero, hrzero⟩ := not_forall.mp hzero
  obtain ⟨rone, hrone⟩ := not_forall.mp hone
  obtain ⟨rand, hrand⟩ := not_forall.mp hand
  obtain ⟨ror, hror⟩ := not_forall.mp hor
  obtain ⟨rmajority, hrmajority⟩ := not_forall.mp hmajority
  obtain ⟨rminority, hrminority⟩ := not_forall.mp hminority
  refine ⟨![rzero, rone, rand, ror, rmajority, rminority], ?_⟩
  rintro (hz | ho | ha | hr | hm | hp)
  · exact hrzero (hz 0)
  · exact hrone (ho 1)
  · exact hrand (ha 2)
  · exact hror (hr 3)
  · exact hrmajority (hm 4)
  · exact hrminority (hp 5)

end Cslib.Logic.PL.CSP
