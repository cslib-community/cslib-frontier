/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Communication.CliqueIndependentSet

/-! Checked clients of the clique versus independent set protocol
[AroraBarak07, Chapter 12, Exercise 8]: in the complete graph on three vertices, all vertices form
a clique and a single vertex is an independent set that meets it, and the `O(log² n)` bound
applies to every graph on `Fin n`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.CommunicationCliqueIndependentSet

open Finset Cslib.Communication

/-- The hypotheses are satisfiable with a nonempty intersection: in the complete graph on `Fin 3`,
`univ` is a clique, `{0}` is an independent set, and they share exactly one vertex. -/
example : (⊤ : SimpleGraph (Fin 3)).IsClique ((univ : Finset (Fin 3)) : Set (Fin 3)) ∧
    (⊤ : SimpleGraph (Fin 3)).IsIndepSet (({0} : Finset (Fin 3)) : Set (Fin 3)) ∧
    #((univ : Finset (Fin 3)) ∩ {0}) = 1 := by
  refine ⟨fun _ _ _ _ h => h, by simp, by decide⟩

/-- Every graph on `Fin n`: `|C ∩ I|` costs at most `3 (⌊log₂ n⌋ + 1)²` bits. -/
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    Cslib.Communication.Protocol.ecomplexity (fun C I z => z = #(C ∩ I))
        {C : Finset (Fin n) | G.IsClique (C : Set (Fin n))}
        {I : Finset (Fin n) | G.IsIndepSet (I : Set (Fin n))} ≤
      (3 * (Nat.log 2 n + 1) ^ 2 : ℕ) := by
  simpa using ecomplexity_clique_indepSet_le G

end CslibFrontierTests.CommunicationCliqueIndependentSet
