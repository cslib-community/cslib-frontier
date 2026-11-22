/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.GetD

/-!
# Local tests of NCL configurations

For AND/OR vertices, legality is a Boolean condition on the red and blue incident directions.
Reading the explicit vertex records gives the same legality test as their finite graph semantics.

## Main definitions

* `Cslib.Complexity.NCL.Vertex.checkSat`: test an AND/OR vertex against a list of bits.
* `Cslib.Complexity.NCL.AndOrGraph.checkLegal`, `Cslib.Complexity.NCL.AndOrGraph.checkStep`:
  finite legality and single-move checks.

## Main results

* `Cslib.Complexity.NCL.Vertex.checkSat_eq_true_iff`: the local Boolean test matches legality.
* `Cslib.Complexity.NCL.AndOrGraph.checkStep_eq_true_iff`: exactly one legal edge reversal.
-/

public section

namespace Cslib.Complexity.NCL

/-- Check the red/blue inflow condition of an AND/OR vertex against a bit list. -/
@[expose] def Vertex.checkSat (v : Vertex ℕ) (s : List Bool) : Bool :=
  if v.ports.any (fun p => p.2 == 1) then
    v.ports.any (fun p => p.2 == 2 && (s.getD p.1.edge false == p.1.dir)) ||
      v.ports.all (fun p => !(p.2 == 1) || (s.getD p.1.edge false == p.1.dir))
  else v.ports.any (fun p => s.getD p.1.edge false == p.1.dir)

/-- The Boolean red/blue test agrees with the inflow constraint at every AND/OR vertex. -/
theorem Vertex.checkSat_eq_true_iff (v : Vertex ℕ) (hv : v.IsAndOr) (s : List Bool) :
    v.checkSat s = true ↔ v.Sat (fun e => s.getD e false) := by
  rcases hv with ⟨a, b, c, hm, hp⟩ | ⟨a, b, c, hm, hp⟩
  · rw [sat_iff_of_perm hp hm, sat_and]
    simp only [checkSat, hp.any_eq, hp.all_eq]
    simp [Vertex.and, Port.In, Bool.or_eq_true, Bool.and_eq_true]
  · rw [sat_iff_of_perm hp hm, sat_or]
    simp only [checkSat, hp.any_eq, hp.all_eq]
    simp [Vertex.or, Port.In, Bool.or_eq_true]

namespace AndOrGraph

/-- Check the local inflow condition of every listed vertex. -/
@[expose]
def checkLegal (g : AndOrGraph) (s : List Bool) : Bool := g.vertices.all (fun v => v.checkSat s)

/-- On bounded AND/OR data, the Boolean check is exactly finite configuration legality. -/
theorem checkLegal_eq_true_iff (g : AndOrGraph) (hb : g.Bounded) (ha : g.graph.IsAndOr)
    (s : List Bool) : g.checkLegal s = true ↔ g.graph.Legal (g.config s) := by
  rw [checkLegal, List.all_eq_true, List.forall_mem_iff_get]
  apply forall_congr'
  intro i
  rw [← congrFun (graph_map_val g hb) i]
  change ((g.graph i).map Fin.val).checkSat s = true ↔ _
  rw [Vertex.checkSat_eq_true_iff _ ((ha i).map Fin.val), Vertex.sat_map]
  rfl

private theorem getD_modify_not (s : List Bool) (i j : ℕ) (hj : j < s.length) :
    (s.modify i Bool.not).getD j false = if j = i then !s.getD j false else s.getD j false := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem s false hj]
  simp [List.getElem_modify, eq_comm]

/-- Flipping a list coordinate implements the graph's single-edge reversal. -/
theorem config_modify_not (g : AndOrGraph) (s : List Bool) (hs : s.length = g.edgeCount)
    (e : Fin g.edgeCount) : g.config (s.modify e Bool.not) = reverse (g.config s) e := by
  funext i
  change (s.modify e Bool.not).getD i false = _
  rw [getD_modify_not s e i (by rw [hs]; exact i.isLt)]
  by_cases hi : i = e
  · subst i
    rw [ite_eq_left rfl, reverse_self]
    rfl
  · rw [ite_eq_right (Fin.val_injective.ne hi), reverse_of_ne _ hi]
    rfl

/-- Check the declared widths, both local legality constraints, and a single bit reversal. -/
@[expose] def checkStep (g : AndOrGraph) (s t : List Bool) : Bool :=
  (decide (s.length = g.edgeCount) && decide (t.length = g.edgeCount)) &&
    ((g.checkLegal s && g.checkLegal t) &&
      (List.range s.length).any (fun i => decide (t = s.modify i Bool.not)))

/-- The step checker recognizes exactly correctly sized pairs related by one legal NCL move. -/
theorem checkStep_eq_true_iff (g : AndOrGraph) (hb : g.Bounded) (ha : g.graph.IsAndOr)
    (s t : List Bool) : g.checkStep s t = true ↔
      s.length = g.edgeCount ∧ t.length = g.edgeCount ∧ g.graph.Step (g.config s) (g.config t) := by
  simp only [checkStep, Bool.and_eq_true, decide_eq_true_eq,
    checkLegal_eq_true_iff g hb ha, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨hs, ht⟩, ⟨⟨hls, hlt⟩, i, hi, rfl⟩⟩
    let e : Fin g.edgeCount := ⟨i, by omega⟩
    exact ⟨hs, ht, hls, hlt, ⟨e, config_modify_not g s hs e⟩⟩
  · rintro ⟨hs, ht, hls, hlt, e, he⟩
    have hflip : t = s.modify e Bool.not := by
      calc
        _ = List.ofFn (g.config t) := (ofFn_config g t ht).symm
        _ = List.ofFn (g.config (s.modify e Bool.not)) :=
          congrArg List.ofFn (he.trans (config_modify_not g s hs e).symm)
        _ = _ := ofFn_config g _ ((List.length_modify Bool.not s e).trans hs)
    exact ⟨⟨hs, ht⟩, ⟨⟨hls, hlt⟩, e.val, by simpa only [hs] using e.isLt, hflip⟩⟩

end AndOrGraph

end Cslib.Complexity.NCL
