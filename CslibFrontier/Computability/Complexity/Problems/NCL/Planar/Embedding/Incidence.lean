/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Bundle
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.WellFormed
import CslibFrontier.Foundations.Data.List.Counting

/-!
# Incidence orders in canonical drawings

A well-formed graph lists every endpoint label exactly once. Its vertex order can therefore be
routed to edge-pair order by the colored permutation construction.

## Main results

* `Planar.Embedding.incidencePerm`: the two incidence orders are permutations.
* `Planar.Embedding.vertexLabels_nodup`, `Planar.Embedding.mem_vertexLabels`: the source labels
  are distinct and exhaustive.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding

variable {E : Type*}

/-- A paired incidence list contains precisely the labels whose edges are listed. -/
theorem mem_pairLabels (es : List E) (p : Port E) : p ∈ Sinks.pairLabels es ↔ p.edge ∈ es := by
  obtain ⟨e, d⟩ := p
  cases d <;> simp [Sinks.pairLabels, List.mem_flatMap, Port.mk.injEq]

/-- Each listed edge contributes its two incidence labels. -/
theorem length_pairLabels (es : List E) : (Sinks.pairLabels es).length = 2 * es.length := by
  rw [Nat.mul_comm]
  exact List.length_flatMap_of_forall_length_eq fun _ _ => rfl

/-- Distinct edges give distinct paired incidence labels. -/
theorem pairLabels_nodup {es : List E} (hn : es.Nodup) : (Sinks.pairLabels es).Nodup := by
  induction es with
  | nil => simp [Sinks.pairLabels]
  | cons e es ih =>
    obtain ⟨he, hn⟩ := List.nodup_cons.1 hn
    change (Port.mk e false :: Port.mk e true :: Sinks.pairLabels es).Nodup
    exact List.nodup_cons.2 ⟨by simpa [mem_pairLabels] using he,
      List.nodup_cons.2 ⟨by simpa [mem_pairLabels] using he, ih hn⟩⟩

private theorem pairLabels_coe (es : List E) :
    (↑(Sinks.pairLabels es) : Multiset (Port E)) =
      (es.map (fun e => ({Port.mk e false} + {Port.mk e true} : Multiset (Port E)))).sum := by
  induction es with
  | nil => simp [Sinks.pairLabels]
  | cons e es ih =>
    change ↑(Port.mk e false :: Port.mk e true :: Sinks.pairLabels es) =
      (({Port.mk e false} + {Port.mk e true} : Multiset (Port E)) + _)
    simp [← Multiset.cons_coe, ih]; rfl

/-- Well-formed vertex data can be reordered into consecutive endpoint pairs. -/
theorem incidencePerm {m : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (Sources.vertexLabels vs).Perm (Sinks.pairLabels (List.finRange m)) := by
  obtain ⟨weight, hw⟩ := hw
  let F : Multiset (WeightedPort (Fin m)) →+ Multiset (Port (Fin m)) :=
    Multiset.mapAddMonoidHom WeightedPort.port
  apply Multiset.coe_eq_coe.1
  calc
    (↑(Sources.vertexLabels vs) : Multiset (Port (Fin m))) =
        F (↑(vs.flatMap Vertex.ports)) := by
      simp [F, Sources.vertexLabels, List.map_flatMap]
    _ = F (ConstraintGraph.portMultiset (fun i : Fin vs.length => vs.get i)) := by
      rw [ConstraintGraph.portMultiset_get]
    _ = ∑ e : Fin m, ({Port.mk e false} + {Port.mk e true} : Multiset (Port (Fin m))) := by
      rw [hw, map_sum]
      simp [F]
    _ = ↑(Sinks.pairLabels (List.finRange m)) := by
      rw [pairLabels_coe, ← List.ofFn_eq_map, List.sum_ofFn]

/-- The incidence labels of a well-formed graph are distinct. -/
theorem vertexLabels_nodup {m : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    (Sources.vertexLabels vs).Nodup :=
  (incidencePerm vs hw).nodup_iff.2 (pairLabels_nodup (List.nodup_finRange m))

/-- Every endpoint appears among the incidence labels of a well-formed graph. -/
theorem mem_vertexLabels {m : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (p : Port (Fin m)) : p ∈ Sources.vertexLabels vs :=
  (incidencePerm vs hw).mem_iff.2 ((mem_pairLabels _ p).2 (List.mem_finRange p.edge))

end Cslib.Complexity.NCL.Planar.Embedding
