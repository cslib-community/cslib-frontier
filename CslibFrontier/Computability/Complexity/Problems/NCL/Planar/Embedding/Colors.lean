/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Weights
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.AndOr
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Basic

/-!
# Recovering edge colors from a finite graph

Scan the actual port list to decide whether an edge is blue. Well-formed AND/OR graphs assign
the resulting color's weight to every occurrence of the edge.

## Main definitions

* `Cslib.Complexity.NCL.Planar.Embedding.color`: a finite scan for a blue port.

## Main results

* `Cslib.Complexity.NCL.Planar.Embedding.port_weight_color`: the recovered edge color agrees
  with every vertex port.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding

/-- An edge is blue when the vertex data list a weight-two port on it. -/
@[expose] def color {m : ℕ} (vs : List (Vertex (Fin m))) (e : Fin m) : Color :=
  if (vs.flatMap Vertex.ports).any (fun p => p.port.edge == e && p.weight == 2) then .blue else .red

private theorem port_mem {m : ℕ} {vs : List (Vertex (Fin m))} {v : Vertex (Fin m)}
    (hv : v ∈ vs) {p : WeightedPort (Fin m)} (hp : p ∈ v.ports) :
    p ∈ ConstraintGraph.portMultiset (fun i : Fin vs.length => vs.get i) := by
  rw [ConstraintGraph.portMultiset_get]
  exact List.mem_flatMap.mpr ⟨v, hv, hp⟩

private theorem port_weight_one_or_two {E : Type*} {v : Vertex E} (hv : v.IsAndOr)
    {p : WeightedPort E} (hp : p ∈ v.ports) : p.weight = 1 ∨ p.weight = 2 := by
  rcases hv with ⟨a, b, c, _, h⟩ | ⟨a, b, c, _, h⟩
  all_goals
    have hh := h.mem_iff.mp hp
    simp only [Vertex.and, Vertex.or, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl <;> simp

/-- The finite color scan agrees with every listed port of a well-formed AND/OR graph. -/
theorem port_weight_color {m : ℕ} {vs : List (Vertex (Fin m))}
    (hA : ∀ v ∈ vs, v.IsAndOr)
    (hW : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    {v : Vertex (Fin m)} (hv : v ∈ vs) {p : WeightedPort (Fin m)} (hp : p ∈ v.ports) :
    p.weight = (color vs p.port.edge).weight := by
  unfold color
  split_ifs with hb
  · obtain ⟨q, hq, heq⟩ := List.any_eq_true.mp hb
    simp only [Bool.and_eq_true, beq_iff_eq] at heq
    have hq' : q ∈ ConstraintGraph.portMultiset (fun i : Fin vs.length => vs.get i) := by
      rw [ConstraintGraph.portMultiset_get]
      exact hq
    exact (hW.weight_eq_of_mem (port_mem hv hp) hq' heq.1.symm).trans heq.2
  · have hw := port_weight_one_or_two (hA v hv) hp
    rcases hw with hw | hw
    · exact hw
    · have hh : (vs.flatMap Vertex.ports).any
          (fun q => q.port.edge == p.port.edge && q.weight == 2) = true := by
        apply List.any_eq_true.mpr
        refine ⟨p, List.mem_flatMap.mpr ⟨v, hv, hp⟩, ?_⟩
        simp [hw]
      exact (hb hh).elim

end Cslib.Complexity.NCL.Planar.Embedding
