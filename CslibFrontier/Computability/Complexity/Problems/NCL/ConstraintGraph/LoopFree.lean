/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Basic
import CslibFrontier.Foundations.Data.List.Counting

/-!
# Loop-free constraint graphs

A vertex is loop-free when its ports use distinct edges. Requiring this at every vertex excludes
self-loops while allowing parallel edges between different vertices. Injective edge renaming
preserves this property. A local checker compares only the finite port list.

## Main definitions

* `Cslib.Complexity.NCL.ConstraintGraph.LoopFree`: every vertex uses each incident edge once.
* `Cslib.Complexity.NCL.Vertex.checkLoopFree`: the local port-list check.

## Main results

* `Cslib.Complexity.NCL.ConstraintGraph.LoopFree.map`: injective renaming preserves loop-freedom.

## References

* Loop-free AND/OR graphs are the target of [Hearn and Demaine][HearnDemaine2005].
-/

public section

namespace Cslib.Complexity.NCL

namespace Vertex

variable {E : Type*} [DecidableEq E]

/-- Check that the ports of a vertex use distinct edges. -/
@[expose] def checkLoopFree (v : Vertex E) : Bool :=
  decide (v.ports.map (fun p => p.port.edge)).Nodup

theorem checkLoopFree_eq_true_iff (v : Vertex E) :
    v.checkLoopFree = true ↔ (v.ports.map (fun p => p.port.edge)).Nodup := by
  simp [checkLoopFree]

/-- Injective edge renaming preserves the local loop-freedom check. -/
theorem checkLoopFree_map {E' : Type*} [DecidableEq E'] (v : Vertex E) {f : E → E'}
    (hf : Function.Injective f) : (v.map f).checkLoopFree = v.checkLoopFree := by
  rw [Bool.eq_iff_iff, checkLoopFree_eq_true_iff, checkLoopFree_eq_true_iff]
  simp only [Vertex.map, List.map_map, WeightedPort.map, Port.map, Function.comp_def]
  simpa only [List.map_map, Function.comp_def] using
    (List.nodup_map_iff (l := v.ports.map (fun p => p.port.edge)) hf)

end Vertex

namespace ConstraintGraph

variable {V E E' : Type*} {G : ConstraintGraph V E}

/-- No vertex contains both endpoints of an edge. Its port list uses every edge at most once. -/
@[expose]
def LoopFree (G : ConstraintGraph V E) : Prop := ∀ v, ((G v).ports.map (fun p => p.port.edge)).Nodup

/-- Injective edge renaming preserves loop-freedom. -/
theorem LoopFree.map (h : G.LoopFree) {f : E → E'} (hf : Function.Injective f) :
    (G.map f).LoopFree := by
  intro v
  simp only [ConstraintGraph.map, Vertex.map, List.map_map, WeightedPort.map, Port.map,
    Function.comp_def]
  simpa only [List.map_map, Function.comp_def] using (h v).map hf

end ConstraintGraph

end Cslib.Complexity.NCL
