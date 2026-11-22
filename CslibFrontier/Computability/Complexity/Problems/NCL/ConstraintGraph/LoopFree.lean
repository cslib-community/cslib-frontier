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

* `Cslib.Complexity.NCL.Vertex.checkLoopFree_eq_scan` recognizes distinct edges by counting.

## References

* Loop-free AND/OR graphs are the target of [Hearn and Demaine][HearnDemaine2005].
-/

public section

namespace Cslib.Complexity.NCL

namespace Vertex

variable {E : Type*} [DecidableEq E]

/-- Check that the ports of a vertex use distinct edges. -/
@[expose] def checkLoopFree (v : Vertex E) : Bool := decide (v.ports.map (fun p => p.1.edge)).Nodup

theorem checkLoopFree_eq_true_iff (v : Vertex E) :
    v.checkLoopFree = true ↔ (v.ports.map (fun p => p.1.edge)).Nodup := by
  simp [checkLoopFree]

/-- Repeated edges can be detected by counting occurrences of each listed edge. -/
theorem checkLoopFree_eq_scan (v : Vertex E) :
    v.checkLoopFree = !((v.ports.map (fun p => p.1.edge)).any fun e =>
      decide (1 < (v.ports.map (fun p => p.1.edge)).countP (fun f => decide (f = e)))) := by
  rw [Bool.eq_iff_iff, checkLoopFree_eq_true_iff, List.not_any_one_lt_countP_iff_nodup]

/-- Injective edge renaming preserves the local check. -/
theorem checkLoopFree_map {E' : Type*} [DecidableEq E'] (v : Vertex E) {f : E → E'}
    (hf : Function.Injective f) : (v.map f).checkLoopFree = v.checkLoopFree := by
  rw [Bool.eq_iff_iff, checkLoopFree_eq_true_iff, checkLoopFree_eq_true_iff]
  simp only [Vertex.map, List.map_map, Port.map, Function.comp_def]
  simpa only [List.map_map, Function.comp_def] using
    (List.nodup_map_iff (l := v.ports.map (fun p => p.1.edge)) hf)

end Vertex

namespace ConstraintGraph

variable {V E : Type*}

/-- No vertex contains both endpoints of an edge. Its port list uses every edge at most once. -/
@[expose]
def LoopFree (G : ConstraintGraph V E) : Prop := ∀ v, ((G v).ports.map (fun p => p.1.edge)).Nodup

end ConstraintGraph

end Cslib.Complexity.NCL
