/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryAppendProgram
public import CslibFrontier.Computability.PolyTime.Graph.RotationSystem.Reindex
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BlockMove
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Native ordered-probe append table computation

The four block lengths are computed in unary from actual body and boundary lists.
The two supplied tables, their entries, corner indices and reindex maps remain binary.
The certificate covers malformed tables as well; accepted-source correctness separately
identifies this actual output with the structural probe-center splice.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Graph Turing.MultiTapeTM

/-- Compute the actual raw append table in native polynomial time. Unary count witnesses
fund the output list; binary table entries never fund any loop. -/
theorem computableInPolyTime_appendRawCertificate {α : Type} {input : α ↪ List Bool}
    {leftBody leftPorts rightBody rightPorts : α → ℕ}
    {left right : α → RotationCertificate}
    (hlb : ComputableInPolyTime leftBody input encUnary)
    (hlp : ComputableInPolyTime leftPorts input encUnary)
    (hrb : ComputableInPolyTime rightBody input encUnary)
    (hrp : ComputableInPolyTime rightPorts input encUnary)
    (hl : ComputableInPolyTime left input encRotationCertificate)
    (hr : ComputableInPolyTime right input encRotationCertificate) :
    ComputableInPolyTime (fun x => appendRawCertificate (leftBody x) (leftPorts x)
      (rightBody x) (rightPorts x) (left x) (right x)) input encRotationCertificate := by
  let offset (x : α) := 2 * (leftBody x + leftPorts x)
  have hoff : ComputableInPolyTime offset input encUnary := by dsimp [offset]; fun_prop
  have hoffb := ComputableInPolyTime.unary_to_binary.comp hoff
  have hrlen : ComputableInPolyTime (fun x => 2 * (rightBody x + rightPorts x))
      input encUnary := by fun_prop
  have hrlenb := ComputableInPolyTime.unary_to_binary.comp hrlen
  have hleft := RotationCertificate.computableInPolyTime_successor.comp hl
  have hright := RotationCertificate.computableInPolyTime_successor.comp hr
  have hshift : ComputableInPolyTime
      (fun x => (right x).successor.map (offset x + ·)) input (encList encNat) := by
    apply ComputableInPolyTime.mapWithInput hright
    exact ComputableInPolyTime.binary_add'
      (hoffb.comp (ComputableInPolyTime.fst input encNat))
      (ComputableInPolyTime.snd input encNat)
  let disjoint (x : α) : RotationCertificate :=
    ⟨(left x).successor ++ (right x).successor.map (offset x + ·)⟩
  have hd : ComputableInPolyTime disjoint input encRotationCertificate := by
    exact encRotationCertificate_mk_deg.computableInPolyTime.comp
      (ComputableInPolyTime.listAppend' hleft hshift)
  let joined (x : α) := if leftPorts x = 0 ∨ rightPorts x = 0 then disjoint x else
    (disjoint x).swapSuccessors (offset x - 1)
      (offset x + 2 * (rightBody x + rightPorts x) - 1)
  have hj : ComputableInPolyTime joined input encRotationCertificate := by
    unfold joined
    apply ComputableInPolyTime.ite_decide
    · fun_prop
    · exact hd
    · exact RotationCertificate.computableInPolyTime_swapSuccessors hd
        (ComputableInPolyTime.binary_sub' hoffb (ComputableInPolyTime.const 1))
        (ComputableInPolyTime.binary_sub'
          (ComputableInPolyTime.binary_add' hoffb hrlenb) (ComputableInPolyTime.const 1))
  have hn : ComputableInPolyTime
      (fun x => 2 * (leftBody x + leftPorts x + rightBody x + rightPorts x)) input encUnary := by
    fun_prop
  have hbefore : ComputableInPolyTime (fun x => 2 * leftBody x) input encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hmoved : ComputableInPolyTime (fun x => 2 * leftPorts x) input encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have ha := hrlenb
  have hf : ComputableInPolyTime (fun p : α × ℕ =>
      Nat.blockMove (2 * leftBody p.1) (2 * leftPorts p.1)
        (2 * (rightBody p.1 + rightPorts p.1)) p.2) (encPair input encNat) encNat :=
    ComputableInPolyTime.natBlockMove'
      (hbefore.comp (ComputableInPolyTime.fst input encNat))
      (hmoved.comp (ComputableInPolyTime.fst input encNat))
      (ha.comp (ComputableInPolyTime.fst input encNat)) (ComputableInPolyTime.snd input encNat)
  have hb : ComputableInPolyTime (fun p : α × ℕ =>
      Nat.blockMove (2 * leftBody p.1) (2 * (rightBody p.1 + rightPorts p.1))
        (2 * leftPorts p.1) p.2) (encPair input encNat) encNat :=
    ComputableInPolyTime.natBlockMove'
      (hbefore.comp (ComputableInPolyTime.fst input encNat))
      (ha.comp (ComputableInPolyTime.fst input encNat))
      (hmoved.comp (ComputableInPolyTime.fst input encNat)) (ComputableInPolyTime.snd input encNat)
  exact RotationCertificate.computableInPolyTime_reindex hj hn hf hb

end Cslib.Complexity.CSP.OrderedBoundary
