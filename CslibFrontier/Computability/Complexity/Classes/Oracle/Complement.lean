/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.Substitution
import CslibFrontier.Computability.Complexity.Classes.Oracle.Lowness

/-!
# Complementing the oracle language

A deterministic oracle algorithm can negate an oracle reply in polynomial time. Substituting
this algorithm for each query shows that complementing the oracle preserves its deterministic
polynomial-time class, even when the class containing the oracle is not complement-closed.
-/

public section
namespace Cslib.Complexity

/-- Complementing the oracle language preserves deterministic polynomial-time oracle access. -/
theorem PWithOracle_compl_eq {α : Type} (A : Set (List Bool)) (enc : α ↪ List Bool) :
    PWithOracle Aᶜ enc = PWithOracle A enc := by
  apply Set.Subset.antisymm
  · exact PWithOracle_subset_of_mem_PWithOracle (mem_PWithOracle_compl_self A) enc
  · exact PWithOracle_subset_of_mem_PWithOracle
      (by simpa only [compl_compl] using mem_PWithOracle_compl_self Aᶜ) enc

end Cslib.Complexity
