/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.WellFormed

/-!
# Weights read from edge incidences

## Main results

* `Cslib.Complexity.NCL.ConstraintGraph.WellFormed.weight_eq_of_mem`: occurrences of the same
  edge have the same weight.
-/

public section

namespace Cslib.Complexity.NCL.ConstraintGraph

/-- Any two listed ports of the same edge have equal weights. -/
theorem WellFormed.weight_eq_of_mem {V E : Type*} [Fintype V] [Fintype E]
    {G : ConstraintGraph V E} (hG : G.WellFormed) {p q : WeightedPort E}
    (hp : p ∈ G.portMultiset) (hq : q ∈ G.portMultiset) (he : p.port.edge = q.port.edge) :
    p.weight = q.weight := by
  classical
  obtain ⟨w, hw⟩ := (wellFormed_iff_filter G).1 hG p.port.edge
  have hmem {r : WeightedPort E} (hr : r ∈ G.portMultiset) (hrp : r.port.edge = p.port.edge) :
      r.weight = w := by
    have hr' := hw ▸ Multiset.mem_filter.mpr ⟨hr, hrp⟩
    rcases Multiset.mem_add.mp hr' with h | h <;>
      exact congrArg WeightedPort.weight (Multiset.mem_singleton.mp h)
  exact (hmem hp rfl).trans (hmem hq he.symm).symm

end Cslib.Complexity.NCL.ConstraintGraph
