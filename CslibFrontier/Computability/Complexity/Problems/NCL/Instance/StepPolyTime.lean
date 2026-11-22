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

Use binary lookup for port indices and scan only the supplied bit lists. List construction
uses framed Boolean lists, with explicit conversions to and from raw bit strings.

## Main results

* `Cslib.Complexity.NCL.Vertex.computableInPolyTime_checkSat`: local Boolean legality testing.
* `Cslib.Complexity.NCL.AndOrGraph.computableInPolyTime_checkStep`: polynomial-time edge test
  for the finite configuration graph.
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

/-- AND/OR inflow testing uses polynomial-time lookup at the binary port indices. -/
@[fun_prop]
theorem Vertex.computableInPolyTime_checkSat {α : Type} {input : α ↪ List Bool}
    {v : α → Vertex ℕ} {s : α → List Bool}
    (hv : ComputableInPolyTime v input (encVertex encNat))
    (hs : ComputableInPolyTime s input encBits) :
    ComputableInPolyTime (fun x => (v x).checkSat (s x)) input encBool := by
  have hp : ComputableInPolyTime (fun x => (v x).ports) input (encWeightedPorts encNat) := by
    fun_prop
  have hl : ComputableInPolyTime (fun p : α × (Port ℕ × ℕ) => s p.1)
      (encPair input (encPair (encPort encNat) encNat)) encBits := by fun_prop
  have hi : ComputableInPolyTime (fun p : α × (Port ℕ × ℕ) => p.2.1.edge)
      (encPair input (encPair (encPort encNat) encNat)) encNat := by fun_prop
  have hr := ComputableInPolyTime.listGetD_binary (encA := encBool) false hl hi
  have hd : ComputableInPolyTime (fun p : α × (Port ℕ × ℕ) => p.2.1.dir)
      (encPair input (encPair (encPort encNat) encNat)) encBool := by fun_prop
  have ha : ComputableInPolyTime (fun p : α × (Port ℕ × ℕ) =>
      (s p.1).getD p.2.1.edge false == p.2.1.dir)
      (encPair input (encPair (encPort encNat) encNat)) encBool :=
    ComputableInPolyTime.beq hr hd
  have hw : ComputableInPolyTime (fun p : α × (Port ℕ × ℕ) => p.2.2)
      (encPair input (encPair (encPort encNat) encNat)) encNat := by fun_prop
  have hred := hw.beq (ComputableInPolyTime.const 1)
  have hblue := hw.beq (ComputableInPolyTime.const 2)
  have hid : ComputableInPolyTime (fun x : α => x) input input := by fun_prop
  have hcond := ComputableInPolyTime.anyWithEncoding hred hid hp
  have hblueIn := ComputableInPolyTime.anyWithEncoding
    (ComputableInPolyTime.bool_and' hblue ha) hid hp
  have hredIn := ComputableInPolyTime.allWithEncoding
    (ComputableInPolyTime.bool_or' (ComputableInPolyTime.bool_not.comp hred) ha) hid hp
  have hany := ComputableInPolyTime.anyWithEncoding ha hid hp
  unfold Vertex.checkSat
  exact ComputableInPolyTime.ite hcond (ComputableInPolyTime.bool_or' hblueIn hredIn) hany

private theorem modify_not_eq_zip (s : List Bool) (i : ℕ) :
    s.modify i Bool.not =
      (s.zip (List.range s.length)).map (fun p => if p.2 = i then !p.1 else p.1) := by
  apply List.ext_getElem (by simp)
  intro j hj _
  simp [List.getElem_modify, eq_comm]

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
    simp only [modify_not_eq_zip]
    fun_prop
  exact (bits_encList_polyTime encBool).2.comp hf

/-- Checking every local vertex condition is polynomial-time on raw configuration bits. -/
@[fun_prop]
theorem AndOrGraph.computableInPolyTime_checkLegal {α : Type} {input : α ↪ List Bool}
    {g : α → AndOrGraph} {s : α → List Bool}
    (hg : ComputableInPolyTime g input encAndOrGraph)
    (hs : ComputableInPolyTime s input encBits) :
    ComputableInPolyTime (fun x => (g x).checkLegal (s x)) input encBool := by
  have hvs : ComputableInPolyTime (fun x => (g x).vertices) input (encList (encVertex encNat)) := by
    fun_prop
  have hv : ComputableInPolyTime (fun p : α × Vertex ℕ => p.2)
      (encPair input (encVertex encNat)) (encVertex encNat) := by fun_prop
  have hl : ComputableInPolyTime (fun p : α × Vertex ℕ => s p.1)
      (encPair input (encVertex encNat)) encBits := by fun_prop
  exact ComputableInPolyTime.allWithEncoding (Vertex.computableInPolyTime_checkSat hv hl)
    (by fun_prop) hvs

private theorem computableInPolyTime_flipTest {α : Type} {input : α ↪ List Bool}
    {s t : α → List Bool} (hs : ComputableInPolyTime s input encBits)
    (ht : ComputableInPolyTime t input encBits) :
    ComputableInPolyTime (fun p : α × ℕ => decide (t p.1 = (s p.1).modify p.2 Bool.not))
      (encPair input encUnary) encBool := by
  have hs' : ComputableInPolyTime (fun p : α × ℕ => s p.1)
      (encPair input encUnary) encBits := by fun_prop
  have ht' : ComputableInPolyTime (fun p : α × ℕ => t p.1)
      (encPair input encUnary) encBits := by fun_prop
  have hi : ComputableInPolyTime (fun p : α × ℕ => p.2)
      (encPair input encUnary) encUnary := by fun_prop
  have hf := computableInPolyTime_modify_not hs' hi
  exact ht'.decide_eq' hf

/-- The explicit single-move checker is polynomial-time in graph data and raw endpoint bits. -/
@[fun_prop]
theorem AndOrGraph.computableInPolyTime_checkStep {α : Type} {input : α ↪ List Bool}
    {g : α → AndOrGraph} {s t : α → List Bool}
    (hg : ComputableInPolyTime g input encAndOrGraph)
    (hs : ComputableInPolyTime s input encBits) (ht : ComputableInPolyTime t input encBits) :
    ComputableInPolyTime (fun x => (g x).checkStep (s x) (t x)) input encBool := by
  have hw : ComputableInPolyTime (fun x => (g x).edgeCount) input encNat := by
    fun_prop
  have hns : ComputableInPolyTime (fun x => (s x).length) input encUnary := by fun_prop
  have hnt : ComputableInPolyTime (fun x => (t x).length) input encUnary := by fun_prop
  have hbs := ComputableInPolyTime.unary_to_binary.comp hns
  have hbt := ComputableInPolyTime.unary_to_binary.comp hnt
  have hsizeS := hbs.decide_eq' hw
  have hsizeT := hbt.decide_eq' hw
  have hlS := computableInPolyTime_checkLegal hg hs
  have hlT := computableInPolyTime_checkLegal hg ht
  have hrange : ComputableInPolyTime (fun x => List.range (s x).length)
      input (encList encUnary) := by fun_prop
  have hany := ComputableInPolyTime.anyWithEncoding (computableInPolyTime_flipTest hs ht)
    (by fun_prop : ComputableInPolyTime (fun x : α => x) input input) hrange
  unfold checkStep
  exact ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hsizeS hsizeT)
    (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hlS hlT) hany)

end Cslib.Complexity.NCL
