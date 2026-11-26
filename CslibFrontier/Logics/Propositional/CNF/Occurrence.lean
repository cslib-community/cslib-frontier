/-
Copyright (c) 2026 Erik Demaine, Stefan Langerman, GPT 5.6. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ModelCount
import Mathlib.Data.List.Sigma

/-!
# Uniqueness of indexed literal occurrences

The proof follows the indexed-copy uniqueness argument in `CNF.ThreeOccurrence`.

## Main results

* `Cslib.Logic.PL.occurrences_nodup`: clause and literal indices distinguish all occurrences.
-/

public section

namespace Cslib.Logic.PL

/-- Clause and literal indices distinguish every source occurrence, including repeated literals. -/
theorem occurrences_nodup {V : Type*} (φ : CNF V) : (occurrences φ).Nodup := by
  rw [occurrences, List.nodup_flatMap]
  refine ⟨fun c _ => List.Nodup.of_map Occurrence.pos ?_,
    (List.pairwise_map.mp (List.nodup_zipIdx_map_snd φ)).imp fun hab =>
      List.disjoint_left.mpr fun _ hx hy => ?_⟩
  · simpa only [List.map_map, Function.comp_def] using List.nodup_zipIdx_map_snd c.1
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, _, hj⟩ := List.mem_map.mp hy
    exact hab (congrArg Occurrence.clause hj.symm)

end Cslib.Logic.PL

