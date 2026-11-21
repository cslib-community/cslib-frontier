/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.DoubleCounting.SeedSearch.OriginalRoots

/-! Checked original-root coverage for the indexed isolation-seed search. -/

set_option linter.privateModule false

namespace CslibFrontierTests.IsolationSeedSearchOriginalRoots

open Cslib Cslib.DoubleCounting Cslib.Reachability.Hoza Cslib.LayeredDigraph.Subdivision
open Cslib.Code.JustesenFamily

private def index : Vertex (Fin (0 + 1) × Fin 2) 1 ≃ Fin 4 :=
  ((equivProd _ _).trans (finProdFinEquiv.prodCongr (Equiv.refl _))).trans finProdFinEquiv

-- The original target is checked as a source, but its auxiliary slot is not.
example : index (root 1 (0, 1)) ∈ originalRootIDs index :=
  (mem_originalRootIDs_iff index _).mpr ⟨_, rfl⟩

example : index ⟨(0, 1), 1⟩ ∉ originalRootIDs index := by
  intro hmem
  obtain ⟨_, hv⟩ := (mem_originalRootIDs_iff index _).mp hmem
  have hoff := congrArg Vertex.offset (index.injective hv)
  exact (by decide : (1 : Fin 2) ≠ 0) hoff

example (G : LayeredDigraph (Fin (0 + 1) × Fin 2)) (hlayer : ∀ v, G.layer v = v.1.val)
    (hb : ∀ (seed : Fin (codeLength 2 0) → Bool) (v : Fin (0 + 1) × Fin 2),
      generatedWeight seed v ≤ 1)
    (controller : (Fin (codeLength 2 0) → Bool) → Fin 4 → List (Option ControllerVerdict))
    (hc : ∀ seed s, ∃ verdict, controller seed s = [some verdict] ∧
      match verdict with
      | .bad j => ¬ ∃! p, Passes (generatedSubdivisionAdj G index seed) s j p
      | .decided b => (∀ j, ∃! p, Passes (generatedSubdivisionAdj G index seed) s j p) ∧
          (b = true ↔ Relation.ReflTransGen (generatedSubdivisionAdj G index seed) s
            (index (root 1 (0, 1))))) :
    ∃ result, runSeedScheduler (fun i _ => controller ((BitString.equivFin _).symm i))
        (originalRootID index) (index (root 1 (0, 0))) =
        [some result] ∧
      G.IsMinIsolating (generatedWeight ((BitString.equivFin _).symm result.seed)) ∧
      (∀ i < result.seed, ¬ G.IsMinIsolating (generatedWeight ((BitString.equivFin _).symm i))) ∧
      (result.reachable = true ↔ Relation.ReflTransGen G.Adj (0, 0) (0, 1)) := by
  rw [← runSeedSearchIndexed_eq_scheduler]
  exact runGeneratedSeedSearch_correct G hlayer index hb (0, 0) (0, 1) controller hc

end CslibFrontierTests.IsolationSeedSearchOriginalRoots
