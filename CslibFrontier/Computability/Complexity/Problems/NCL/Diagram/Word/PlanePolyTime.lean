/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Plane
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.Perm.Basic

/-!
# Polynomial-time recognition of plane layers

Compare the listed ports with the colored boundary ports by counting occurrences in their
combined support. Side-tagged local indices preserve the shape, loop and incidence checks.

## Main results

* `Cslib.Complexity.NCL.Slice.computableInPolyTime_checkPlane`: standard plane layer recognition.
* `Cslib.Complexity.NCL.Word.computableInPolyTime_checkPlane`: all-layer plane recognition.
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM
open scoped Slice

private def checkPerm {α : Type} [BEq α] (l r : List α) : Bool :=
  (l ++ r).all fun a => (l.countP (· == a)) == (r.countP (· == a))

private theorem checkPerm_eq_true_iff {α : Type} [DecidableEq α] (l r : List α) :
    checkPerm l r = true ↔ l.Perm r := by
  simp only [checkPerm, List.all_eq_true, beq_iff_eq, ← List.count_eq_countP]
  rw [List.perm_iff_count]
  constructor
  · intro h a
    by_cases ha : a ∈ l ++ r
    · exact h a ha
    · simp only [List.mem_append, not_or] at ha
      simp [List.count_eq_zero_of_not_mem ha.1, List.count_eq_zero_of_not_mem ha.2]
  · exact fun h a _ => h a

private theorem computableInPolyTime_checkPerm {α : Type} [DecidableEq α]
    (encA : α ↪ List Bool) : ComputableInPolyTime
      (fun p : List α × List α => checkPerm p.1 p.2)
      (encPair (encList encA) (encList encA)) encBool := by
  unfold checkPerm
  exact ComputableInPolyTime.allWithEncoding
    (by fun_prop : ComputableInPolyTime
      (fun p : (List α × List α) × α => p.1.1.countP (· == p.2) == p.1.2.countP (· == p.2))
      (encPair (encPair (encList encA) (encList encA)) encA) encBool)
    .id' (by fun_prop : ComputableInPolyTime (fun p : List α × List α => p.1 ++ p.2)
      (encPair (encList encA) (encList encA)) (encList encA))

private def localPorts (cs : List Color) (side : Bool) : List (WeightedPort (Bool × ℕ)) :=
  (List.range cs.length).map fun i => ⟨⟨(side, i), side⟩, (cs.getD i .red).weight⟩

private theorem localPorts_genVertex (a b : List Color) :
    ((Diagram.genVertex a b 0).map Slice.localIndex).ports =
      localPorts a true ++ localPorts b false := by
  simp only [Diagram.genVertex, Vertex.map, List.map_append, List.map_map, localPorts]
  congr 1 <;> (
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [List.length_map, List.length_finRange] at hi
    simp [WeightedPort.map, Port.map, Slice.localIndex, hi])

private def checkPlaneData (d : Slice.Data) : Bool :=
  !d.isSwap && ((d.vertices.length == 1) && (d.vertices.all Vertex.checkAndOr &&
    (d.vertices.all Vertex.checkLoopFree && checkPerm (d.vertices.flatMap Vertex.ports)
      (localPorts d.inputs true ++ localPorts d.outputs false))))

private theorem checkPlaneData_data (sl : Slice) : checkPlaneData sl.data = sl.checkPlane := by
  cases sl with
  | swap _ => rfl
  | gen k a b vs =>
    have hi := Slice.localIndex_injective (n := a.length) (m := b.length)
    have he : checkPerm ((vs.map (Vertex.map Slice.localIndex)).flatMap Vertex.ports)
        (localPorts a true ++ localPorts b false) = Prim.interp.checkPorts vs := by
      rw [← localPorts_genVertex, Bool.eq_iff_iff, checkPerm_eq_true_iff]
      change _ ↔ decide ((vs.flatMap Vertex.ports).Perm (Diagram.genVertex a b 0).ports) = true
      simpa only [Vertex.map, List.flatMap_map, ← List.map_flatMap, decide_eq_true_eq] using
        List.map_perm_map_iff (WeightedPort.map_injective hi)
    simp only [checkPlaneData, Slice.data, Slice.checkPlane, Bool.not_false, Bool.true_and,
      List.length_map, Prim.checkStandard, he, List.all_map, Function.comp_def,
      Vertex.checkAndOr_map, Vertex.checkLoopFree_map _ hi]

private theorem computableInPolyTime_colorWeight :
    ComputableInPolyTime Color.weight encColor encNat := by
  let _ : Finite Color := Finite.of_injective (fun c : Color => c == .blue)
    (by intro c d h; cases c <;> cases d <;> simp_all)
  exact ComputableInPolyTime.of_finite _

private theorem computableInPolyTime_localPorts (side : Bool) :
    ComputableInPolyTime (fun cs => localPorts cs side) (encList encColor)
      (encWeightedPorts (encPair encBool encUnary)) := by
  have hw := computableInPolyTime_colorWeight
  unfold localPorts
  fun_prop

private theorem computableInPolyTime_checkLoopFree :
    ComputableInPolyTime (Vertex.checkLoopFree : Vertex (Bool × ℕ) → Bool)
      (encVertex (encPair encBool encUnary)) encBool := by
  unfold Vertex.checkLoopFree
  exact .decide_nodup (by fun_prop)

private theorem computableInPolyTime_checkPlaneData :
    ComputableInPolyTime checkPlaneData Slice.encData encBool := by
  have hl := computableInPolyTime_checkLoopFree
  have hp := computableInPolyTime_checkPerm (encWeightedPort (encPair encBool encUnary))
  have ht := computableInPolyTime_localPorts true
  have hb := computableInPolyTime_localPorts false
  unfold checkPlaneData Slice.encData
  fun_prop

/-- Check whether a structurally encoded layer is one standard plane vertex in polynomial time. -/
@[fun_prop]
theorem Slice.computableInPolyTime_checkPlane :
    ComputableInPolyTime Slice.checkPlane encSlice encBool := by
  simpa only [Function.comp_def, checkPlaneData_data] using
    computableInPolyTime_checkPlaneData.comp Slice.computableInPolyTime_data

/-- Check every layer of a structurally encoded word for plane vertex shape in polynomial time. -/
@[fun_prop]
theorem Word.computableInPolyTime_checkPlane :
    ComputableInPolyTime Word.checkPlane encWord encBool := by
  unfold Word.checkPlane encWord
  exact .allWithEncoding
    (by fun_prop : ComputableInPolyTime (fun p : Word × Slice => p.2.checkPlane)
      (encPair encWord encSlice) encBool)
    .id' (.of_eq fun _ => rfl)

end Cslib.Complexity.NCL
