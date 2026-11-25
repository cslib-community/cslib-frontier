/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Step
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Polynomial-time local configuration checks

Compute inflow using binary lookup at port indices and binary summation of the inward weights.
The reversal test scans only the supplied bit lists.

## Main results

* `Cslib.Complexity.NCL.Vertex.computableInPolyTime_checkSat`: local Boolean legality testing.
* `Cslib.Complexity.NCL.AndOrGraph.computableInPolyTime_checkStep`: polynomial-time edge test
  for the finite configuration graph.
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

/-- Inflow testing uses polynomial-time binary lookup, summation and comparison. -/
@[fun_prop]
theorem Vertex.computableInPolyTime_checkSat {α : Type} {input : α ↪ List Bool}
    {v : α → Vertex ℕ} {s : α → List Bool}
    (hv : ComputableInPolyTime v input (encVertex encNat))
    (hs : ComputableInPolyTime s input encBits) :
    ComputableInPolyTime (fun x => (v x).checkSat (s x)) input encBool := by
  have hr := ComputableInPolyTime.listGetD_binary (encA := encBool) false
    (by fun_prop : ComputableInPolyTime (fun p : α × WeightedPort ℕ => s p.1)
      (encPair input (encWeightedPort encNat)) encBits)
    (by fun_prop : ComputableInPolyTime (fun p : α × WeightedPort ℕ => p.2.port.edge)
      (encPair input (encWeightedPort encNat)) encNat)
  have hin := ComputableInPolyTime.mapWithInput
    (f := fun x p => if (s x).getD p.port.edge false == p.port.dir then p.weight else 0)
    (by fun_prop : ComputableInPolyTime (fun x => (v x).ports) input (encWeightedPorts encNat))
    (ComputableInPolyTime.ite (ComputableInPolyTime.beq hr (by fun_prop))
      (by fun_prop) (ComputableInPolyTime.const 0))
  convert ComputableInPolyTime.binary_le'
    (by fun_prop : ComputableInPolyTime (fun x => (v x).minInflow) input encNat)
    (ComputableInPolyTime.binary_sum.comp hin) using 1
  funext x
  simp [Vertex.checkSat, Vertex.Sat, Vertex.inflow, Port.In]

private theorem modify_not_eq_zip (s : List Bool) (i : ℕ) :
    s.modify i Bool.not =
      (s.zip (List.range s.length)).map (fun p => if p.2 = i then !p.1 else p.1) := by
  refine List.ext_getElem (by simp) fun j hj _ => by simp [List.getElem_modify, eq_comm]

private theorem computableInPolyTime_modify_not {α : Type} {input : α ↪ List Bool}
    {s : α → List Bool} {i : α → ℕ}
    (hs : ComputableInPolyTime s input encBits) (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun x => (s x).modify (i x) Bool.not) input encBits := by
  have hl : ComputableInPolyTime s input (encList encBool) :=
    (bits_encList_polyTime encBool).1.comp hs
  have hz : ComputableInPolyTime (fun x => (s x).zip (List.range (s x).length))
      input (encList (encPair encBool encUnary)) := by fun_prop
  have hf : ComputableInPolyTime (fun x => (s x).modify (i x) Bool.not)
      input (encList encBool) := by
    simp only [modify_not_eq_zip]; fun_prop
  exact (bits_encList_polyTime encBool).2.comp hf

/-- Checking every local vertex condition is polynomial-time on raw configuration bits. -/
@[fun_prop]
theorem AndOrGraph.computableInPolyTime_checkLegal {α : Type} {input : α ↪ List Bool}
    {g : α → AndOrGraph} {s : α → List Bool}
    (hg : ComputableInPolyTime g input encAndOrGraph)
    (hs : ComputableInPolyTime s input encBits) :
    ComputableInPolyTime (fun x => (g x).checkLegal (s x)) input encBool := by
  exact ComputableInPolyTime.allWithEncoding
    (Vertex.computableInPolyTime_checkSat
      (by fun_prop : ComputableInPolyTime (fun p : α × Vertex ℕ => p.2)
        (encPair input (encVertex encNat)) (encVertex encNat))
      (by fun_prop : ComputableInPolyTime (fun p : α × Vertex ℕ => s p.1)
        (encPair input (encVertex encNat)) encBits))
    (by fun_prop : ComputableInPolyTime (fun x : α => x) input input)
    (by fun_prop)

private theorem computableInPolyTime_flipTest {α : Type} {input : α ↪ List Bool}
    {s t : α → List Bool} (hs : ComputableInPolyTime s input encBits)
    (ht : ComputableInPolyTime t input encBits) :
    ComputableInPolyTime (fun p : α × ℕ => decide (t p.1 = (s p.1).modify p.2 Bool.not))
      (encPair input encUnary) encBool := by
  exact (by fun_prop : ComputableInPolyTime (fun p : α × ℕ => t p.1)
    (encPair input encUnary) encBits).decide_eq'
    (computableInPolyTime_modify_not (by fun_prop) (by fun_prop))

/-- The explicit single-move checker is polynomial-time in graph data and raw endpoint bits. -/
@[fun_prop]
theorem AndOrGraph.computableInPolyTime_checkStep {α : Type} {input : α ↪ List Bool}
    {g : α → AndOrGraph} {s t : α → List Bool}
    (hg : ComputableInPolyTime g input encAndOrGraph)
    (hs : ComputableInPolyTime s input encBits) (ht : ComputableInPolyTime t input encBits) :
    ComputableInPolyTime (fun x => (g x).checkStep (s x) (t x)) input encBool := by
  have hw : ComputableInPolyTime (fun x => (g x).edgeCount) input encNat := by fun_prop
  have hsizeS := (ComputableInPolyTime.unary_to_binary.comp
    (by fun_prop : ComputableInPolyTime (fun x => (s x).length) input encUnary)).decide_eq' hw
  have hsizeT := (ComputableInPolyTime.unary_to_binary.comp
    (by fun_prop : ComputableInPolyTime (fun x => (t x).length) input encUnary)).decide_eq' hw
  have hany := ComputableInPolyTime.anyWithEncoding (computableInPolyTime_flipTest hs ht)
    (by fun_prop : ComputableInPolyTime (fun x : α => x) input input)
    (by fun_prop : ComputableInPolyTime (fun x => List.range (s x).length)
      input (encList encUnary))
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hsizeS hsizeT)
    (ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.bool_and' (computableInPolyTime_checkLegal hg hs)
        (computableInPolyTime_checkLegal hg ht)) hany)

end Cslib.Complexity.NCL
