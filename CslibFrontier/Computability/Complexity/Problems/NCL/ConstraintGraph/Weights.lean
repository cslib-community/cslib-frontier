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
  have hp' : p ∈ G.portMultiset.filter (fun t => t.port.edge = p.port.edge) :=
    Multiset.mem_filter.mpr ⟨hp, rfl⟩
  have hq' : q ∈ G.portMultiset.filter (fun t => t.port.edge = p.port.edge) :=
    Multiset.mem_filter.mpr ⟨hq, he.symm⟩
  rw [hw] at hp' hq'
  simp only [Multiset.mem_add, Multiset.mem_singleton] at hp' hq'
  have hpw : p.weight = w := by
    rcases hp' with h | h <;> exact congrArg WeightedPort.weight h
  have hqw : q.weight = w := by
    rcases hq' with h | h <;> exact congrArg WeightedPort.weight h
  exact hpw.trans hqw.symm

end Cslib.Complexity.NCL.ConstraintGraph
