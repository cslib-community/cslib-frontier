/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.Reachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.PlanePolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.TypingPolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.CompilePolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.PSPACE.EdgeToEdge
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Plane AND/OR NCL is in PSPACE

The structural plane-word guard and word compilation run in polynomial time. The three general
graph algorithms therefore decide the corresponding plane-word problems in polynomial space.

## Main results

* `Cslib.Complexity.NCL.PlaneWordAndOrNCL_mem_PSPACE`: fixed-target plane reachability.
* `Cslib.Complexity.NCL.PlaneWordAndOrNCLEdge_mem_PSPACE`: configuration-to-edge plane reachability.
* `Cslib.Complexity.NCL.PlaneWordAndOrNCLEdgeToEdge_mem_PSPACE`: directional plane reachability.
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

private def planeGuard (w : Word) : Bool := w.checkPlane && decide (w.WellTyped [] [])

private theorem computableInPolyTime_planeGuard :
    ComputableInPolyTime planeGuard encWord encBool := by
  exact Word.computableInPolyTime_checkPlane.bool_and' Word.computableInPolyTime_wellTyped

private theorem planeProblem_mem_PSPACE {A B : Type} {encA : A ↪ List Bool}
    {encB : B ↪ List Bool} {S : Set B} (word : A → Word) (compile : A → B)
    (hw : ComputableInPolyTime word encA encWord)
    (hc : ComputableInPolyTime compile encA encB) (hS : S ∈ PSPACE encB) :
    {x | (word x).checkPlane = true ∧ (word x).WellTyped [] [] ∧ compile x ∈ S} ∈
      PSPACE encA := by
  have hr : PolyTimeReducible encA encB (compile ⁻¹' S) S :=
    ⟨compile, hc, fun _ => Iff.rfl⟩
  have hg := computableInPolyTime_planeGuard.comp hw
  have hm : {x | planeGuard (word x) = true} ∈ PSPACE encA :=
    ⟨_, .of_polyTime hg, fun _ => Iff.rfl⟩
  have he : {x | (word x).checkPlane = true ∧ (word x).WellTyped [] [] ∧ compile x ∈ S} =
      {x | planeGuard (word x) = true} ∩ (compile ⁻¹' S) := by
    ext x
    simp [planeGuard, and_assoc]
  rw [he]
  exact inter_mem_PSPACE hm (hr.mem_PSPACE hS)

/-- Fixed-target plane AND/OR NCL is decidable in polynomial space. -/
theorem PlaneWordAndOrNCL_mem_PSPACE : PlaneWordAndOrNCL ∈ PSPACE encPlaneWordAndOrNCL :=
  planeProblem_mem_PSPACE PlaneWordAndOrNCL.Instance.word
    (fun x => AndOrNCL.Instance.mk (Word.compile x.word) x.initial x.target)
    (by fun_prop) (by fun_prop) AndOrNCL_mem_PSPACE

/-- Configuration-to-edge plane AND/OR NCL is decidable in polynomial space. -/
theorem PlaneWordAndOrNCLEdge_mem_PSPACE :
    PlaneWordAndOrNCLEdge ∈ PSPACE encPlaneWordAndOrNCLEdge :=
  planeProblem_mem_PSPACE PlaneWordAndOrNCLEdge.Instance.word
    (fun x => AndOrNCLEdge.Instance.mk (Word.compile x.word) x.initial x.edge)
    (by fun_prop) (by fun_prop) AndOrNCLEdge_mem_PSPACE

/-- Directional edge-to-edge plane AND/OR NCL is decidable in polynomial space. -/
theorem PlaneWordAndOrNCLEdgeToEdge_mem_PSPACE :
    PlaneWordAndOrNCLEdgeToEdge ∈ PSPACE encPlaneWordAndOrNCLEdgeToEdge :=
  planeProblem_mem_PSPACE PlaneWordAndOrNCLEdgeToEdge.Instance.word
    (fun x => AndOrNCLEdgeToEdge.Instance.mk (Word.compile x.word) x.first x.second)
    (by fun_prop) (by fun_prop) AndOrNCLEdgeToEdge_mem_PSPACE

end Cslib.Complexity.NCL
