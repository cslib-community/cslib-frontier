/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.OfFinite
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding

/-!
# Canonical planarization after finite serialization

Serializing and reading a finite graph retains its exact vertex list. The generic canonical
planarizer consequently builds the same diagram and word, and its canonical orientation bits
are the existing incidence plane simulation's bits for the original finite orientation.

## Main results

* `Planar.planarizeDiagram_ofFinite`, `Planar.planarize_ofFinite`: exact diagram and word.
* `Planar.planarize_bits_ofFinite`: exact canonical simulation configuration bits.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar

open Diagram

private theorem loopFree_ofFinite {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m))
    (hl : ConstraintGraph.LoopFree (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i)) :
    (AndOrGraph.ofFinite G).graph.LoopFree := by
  apply AndOrGraph.ofFinite_loopFree
  rw [listGraph_eq] at hl
  intro i
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    hl ((Cslib.Complexity.NCL.Planar.vertexEquiv G).symm i)

private theorem planeDiagram_congr {m : ℕ} {vs ws : List (Vertex (Fin m))} (he : vs = ws)
    (hv : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (hw : ConstraintGraph.WellFormed (fun i : Fin ws.length => ws.get i)) :
    Embedding.planeDiagram vs hv = Embedding.planeDiagram ws hw := by
  cases he
  rfl

private def planeBits {m : ℕ} (vs : List (Vertex (Fin m)))
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (hl : ConstraintGraph.LoopFree (fun i : Fin vs.length => vs.get i)) (s : Fin m → Bool) :
    List Bool :=
  (Embedding.planeDiagram vs hw).bits ((Embedding.planeSimulation vs ha hw hl).enc s)

private theorem planeBits_congr {m : ℕ} {vs ws : List (Vertex (Fin m))} (he : vs = ws)
    (ha : ∀ v ∈ vs, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (hl : ConstraintGraph.LoopFree (fun i : Fin vs.length => vs.get i))
    (ha' : ∀ v ∈ ws, v.IsAndOr)
    (hw' : ConstraintGraph.WellFormed (fun i : Fin ws.length => ws.get i))
    (hl' : ConstraintGraph.LoopFree (fun i : Fin ws.length => ws.get i)) (s : Fin m → Bool) :
    planeBits vs ha hw hl s = planeBits ws ha' hw' hl' s := by
  cases he
  rfl

/-- Finite serialization retains the exact existing canonical incidence plane diagram. -/
theorem planarizeDiagram_ofFinite {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m))
    (h : (AndOrGraph.ofFinite G).Valid)
    (hw : ConstraintGraph.WellFormed (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i)) :
    planarizeDiagram (AndOrGraph.ofFinite G) h = Embedding.planeDiagram (List.ofFn G) hw :=
  planeDiagram_congr (AndOrGraph.ofFn_graph_ofFinite G) _ hw

/-- Finite serialization retains the exact canonical primitive word and its numbering. -/
theorem planarize_ofFinite {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m))
    (h : (AndOrGraph.ofFinite G).Valid)
    (hw : ConstraintGraph.WellFormed (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i)) :
    planarize (AndOrGraph.ofFinite G) h =
      (Embedding.planeDiagram (List.ofFn G) hw).toWord Prim.interp 0 :=
  congrArg (fun D => D.toWord Prim.interp 0) (planarizeDiagram_ofFinite G h hw)

/-- The generic backend's serialized canonical bits are the original finite plane simulation's
bits, for every orientation, with the same diagram and edge creation order. -/
theorem planarize_bits_ofFinite {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m))
    (h : (AndOrGraph.ofFinite G).Valid)
    (ha : ∀ v ∈ List.ofFn G, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i))
    (hl : ConstraintGraph.LoopFree (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i))
    (s : Fin m → Bool) :
    (planarizeDiagram (AndOrGraph.ofFinite G) h).bits
      ((planarizeDiagramSimulation (AndOrGraph.ofFinite G) h (by exact loopFree_ofFinite G hl)).enc
        ((AndOrGraph.ofFinite G).config (List.ofFn s))) =
      (Embedding.planeDiagram (List.ofFn G) hw).bits
        ((Embedding.planeSimulation (List.ofFn G) ha hw hl).enc s) := by
  let ha₀ := ofFn_andOr (AndOrGraph.ofFinite G).graph h.2.1
  let hw₀ := ofFn_wellFormed (AndOrGraph.ofFinite G).graph h.2.2
  let hl₀ := ofFn_loopFree (AndOrGraph.ofFinite G).graph (loopFree_ofFinite G hl)
  change planeBits (List.ofFn (AndOrGraph.ofFinite G).graph) ha₀ hw₀ hl₀
    ((AndOrGraph.ofFinite G).config (List.ofFn s)) = _
  exact (congrArg
    (planeBits (List.ofFn (AndOrGraph.ofFinite G).graph) ha₀ hw₀ hl₀)
    (AndOrGraph.config_ofFn (AndOrGraph.ofFinite G) s)).trans
      (planeBits_congr (AndOrGraph.ofFn_graph_ofFinite G) ha₀ hw₀ hl₀ ha hw hl s)

end Cslib.Complexity.NCL.Planar
