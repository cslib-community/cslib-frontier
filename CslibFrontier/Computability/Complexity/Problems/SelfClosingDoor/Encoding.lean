/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import Mathlib.Data.List.Enum

/-!
# Encodings and local checks for self-closing door networks

Location labels use binary naturals. Each door stores its two directed tunnels and initial bit;
list framing retains independent identities for doors with identical endpoints. Configurations
store the framed binary location followed by the raw state bits.

## Main definitions

* `encTunnel`, `encDoor`, `encInstance`, `encState`: structural bit encodings.
* `checkStep`: the Boolean check for an enabled traversal.

## Main results

* `checkStep_eq_true_iff`: the local check agrees with the traversal semantics.
* `computableInPolyTime_checkStep`: the local check runs in polynomial time.
-/

public section

namespace Cslib.Complexity.SelfClosingDoor

open _root_.Turing.MultiTapeTM

/-- A framed binary entry label followed by a binary exit label. -/
enc_structure encTunnel : Tunnel where
  source : encNat, target : encNat

/-- The two framed tunnels followed by the initial state bit. -/
enc_structure encDoor : Door where
  zero : encTunnel, one : encTunnel, initial : encBool

/-- The framed door list, framed binary start, and binary target location. -/
enc_structure encInstance : Instance where
  doors : (encList encDoor), start : encNat, target : encNat

/-- The framed binary location followed by the raw door-state bits. -/
enc_structure encState : State where
  location : encNat, bits : encBits

/-- Selecting the tunnel enabled by a computed bit takes polynomial time. -/
@[fun_prop] theorem Door.computableInPolyTime_tunnel {α : Type} {input : α ↪ List Bool}
    {door : α → Door} {bit : α → Bool}
    (hd : ComputableInPolyTime door input encDoor)
    (hb : ComputableInPolyTime bit input encBool) :
    ComputableInPolyTime (fun a => (door a).tunnel (bit a)) input encTunnel := by
  unfold Door.tunnel
  fun_prop

/-- Reading the network's prescribed initial configuration is polynomial-time. -/
@[fun_prop] theorem Instance.computableInPolyTime_initial :
    ComputableInPolyTime Instance.initial encInstance encState := by
  have hraw := ComputableInPolyTime.listToBits.comp
    (by fun_prop : ComputableInPolyTime (fun I : Instance => I.doors.map Door.initial)
      encInstance (encList encBool))
  unfold Instance.initial
  fun_prop

/-- Check the state width and each explicitly listed, indexed door. -/
@[expose] def checkStep (doors : List Door) (s t : State) : Bool :=
  decide (s.bits.length = doors.length) &&
    doors.zipIdx.any fun (door, index) =>
      let tunnel := door.tunnel (s.bits.getD index false)
      decide (s.location = tunnel.source) &&
        (decide (t.location = tunnel.target) &&
          decide (t.bits = s.bits.set index (!s.bits.getD index false)))

/-- The local Boolean check recognizes exactly the traversal relation. -/
theorem checkStep_eq_true_iff (doors : List Door) (s t : State) :
    checkStep doors s t = true ↔ Step doors s t := by
  simp only [checkStep, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.exists_mem_zipIdx', Step, State.Valid, Fin.exists_iff, State.ext_iff,
    Fin.getElem_fin]

private theorem checkTraversal_polyTime :
    ComputableInPolyTime
      (fun q : (State × State) × (Door × ℕ) =>
        let tunnel := q.2.1.tunnel (q.1.1.bits.getD q.2.2 false)
        decide (q.1.1.location = tunnel.source) &&
          (decide (q.1.2.location = tunnel.target) &&
            decide (q.1.2.bits = q.1.1.bits.set q.2.2 (!q.1.1.bits.getD q.2.2 false))))
      (encPair (encPair encState encState) (encPair encDoor encUnary)) encBool := by
  have hlist := ComputableInPolyTime.bitsToList.comp
    (by fun_prop : ComputableInPolyTime (fun q : (State × State) × (Door × ℕ) => q.1.1.bits)
      (encPair (encPair encState encState) (encPair encDoor encUnary)) encBits)
  have hi : ComputableInPolyTime (fun q : (State × State) × (Door × ℕ) => q.2.2)
      (encPair (encPair encState encState) (encPair encDoor encUnary)) encUnary := by fun_prop
  have hbit := ComputableInPolyTime.listGetDWithInput hlist hi false
  have hraw := ComputableInPolyTime.listToBits.comp
    (ComputableInPolyTime.listSetWithInput encBool hlist hi
      (ComputableInPolyTime.bool_not.comp hbit))
  have htunnel := Door.computableInPolyTime_tunnel (door := fun q => q.2.1) (by fun_prop) hbit
  exact (ComputableInPolyTime.decide_eq' (left := fun q => q.1.1.location) (by fun_prop)
      (encTunnel_source_polyTime htunnel)).bool_and'
    ((ComputableInPolyTime.decide_eq' (left := fun q => q.1.2.location) (by fun_prop)
        (encTunnel_target_polyTime htunnel)).bool_and'
      (ComputableInPolyTime.decide_eq' (left := fun q => q.1.2.bits) (by fun_prop) hraw))

/-- Checking an enabled traversal is polynomial-time in the network and endpoint states. -/
@[fun_prop] theorem computableInPolyTime_checkStep {α : Type} {input : α ↪ List Bool}
    {doors : α → List Door} {s t : α → State}
    (hd : ComputableInPolyTime doors input (encList encDoor))
    (hs : ComputableInPolyTime s input encState)
    (ht : ComputableInPolyTime t input encState) :
    ComputableInPolyTime (fun a => checkStep (doors a) (s a) (t a)) input encBool := by
  have htest := checkTraversal_polyTime.comp
    (by fun_prop : ComputableInPolyTime
      (fun p : α × (Door × ℕ) => ((s p.1, t p.1), p.2))
      (encPair input (encPair encDoor encUnary))
      (encPair (encPair encState encState) (encPair encDoor encUnary)))
  have hany := ComputableInPolyTime.anyWithEncoding htest
    (by fun_prop : ComputableInPolyTime (fun a : α => a) input input)
    ((ComputableInPolyTime.zipIdx encDoor).comp hd)
  unfold checkStep
  fun_prop

end Cslib.Complexity.SelfClosingDoor
