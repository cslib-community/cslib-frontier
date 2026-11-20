/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator
import CslibFrontier.Computability.Complexity.Problems.STCON.LayeredCallback

/-! # Rectangular STCON layering as an isolation input

Check the layer-first graph interface on the implicit native configuration graph, including
the fixed endpoints, Hoza's isolating seed, and the one-read adjacency callback.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LayeredSTCONIsolation

open Cslib.Complexity Cslib.Complexity.STCON Cslib.Reachability.Hoza Cslib.Code.JustesenFamily
open Turing

/-- The same rectangular coordinates feed the min-isolating weights and the existing
adjacency callback. The graph's endpoints still decide the original configuration instance. -/
example {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let e := layeredCoordinates I
    let G := layeredDigraph I
    (∃ seed : Fin (codeLength I.n (I.n - 1)) → Bool, G.IsMinIsolating (generatedWeight seed)) ∧
      (Relation.ReflTransGen G.Adj (e (layeredStart I)) (e (layeredTarget I)) ↔ I ∈ STCON) ∧
      ∀ u v, ∃ answer, (layeredCallback ntm).runFrom w
        (.inl (layeredQueryRequest ntm c w (e.symm u) (e.symm v))) 1 = .inr answer ∧
          (answer = true ↔ G.Adj u v) := by
  refine ⟨exists_generatedWeight_isMinIsolating _ (fun _ => rfl), layeredDigraph_reachable_iff _,
    fun u v => ?_⟩
  exact layeredCallback_agrees ntm c w _ _

end CslibFrontierTests.LayeredSTCONIsolation
