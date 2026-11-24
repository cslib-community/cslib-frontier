/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Relation
import Mathlib.Data.List.GetD

/-!
# Directed symmetric self-closing door networks

A door has two directed tunnels. In state `b`, only tunnel `b` is enabled;
traversing it flips the door's state. Locations label the connected components of the freely
traversable wiring, so different tunnel endpoints may share a location. Networks have no
planarity restriction. The goal constrains the player's location and leaves all final door
states unrestricted.

This is the directed symmetric case of [AniBosboomDemaineEtAl2021, Section 2.1].

## Main definitions

* `Tunnel`, `Door`, `Instance`, `State`: explicit networks and their configurations.
* `Step`, `Reachable`: traversal semantics and finite paths.
* `Reachability`: the single-player target-location decision problem.

## References

* [Ani et al.][AniBosboomDemaineEtAl2021, Section 2.1 and Corollary 2.4]
-/

public section

namespace Cslib.Complexity.SelfClosingDoor

/-- A directed traversal between two locations, which may coincide. -/
@[ext] structure Tunnel where
  /-- The entry location. -/
  source : ℕ
  /-- The exit location. -/
  target : ℕ
  deriving DecidableEq, Inhabited

/-- A symmetric self-closing door with its prescribed initial state. -/
@[ext] structure Door where
  /-- The directed tunnel enabled in state `false`. -/
  zero : Tunnel
  /-- The directed tunnel enabled in state `true`. -/
  one : Tunnel
  /-- The initial state of this door. -/
  initial : Bool
  deriving DecidableEq, Inhabited

/-- The tunnel enabled by the door's current state. -/
@[expose] def Door.tunnel (d : Door) (b : Bool) : Tunnel := if b then d.one else d.zero

/-- An explicit list of doors with a starting and target location. -/
@[ext] structure Instance where
  /-- Each list entry is an independent door, including when endpoints coincide. -/
  doors : List Door
  /-- The player's initial location. -/
  start : ℕ
  /-- The location the player must reach. -/
  target : ℕ
  deriving DecidableEq, Inhabited

/-- A player's location and one state bit for each listed door. -/
@[ext] structure State where
  /-- The player's current location. -/
  location : ℕ
  /-- Door states in the network's list order. -/
  bits : List Bool
  deriving DecidableEq, Inhabited

/-- A configuration has exactly one state bit for each door. -/
@[expose] def State.Valid (doors : List Door) (s : State) : Prop :=
  s.bits.length = doors.length

/-- Read the prescribed initial states in the network's list order. -/
@[expose] def Instance.initial (I : Instance) : State :=
  ⟨I.start, I.doors.map Door.initial⟩

/-- The prescribed initial state contains exactly one bit per door. -/
@[simp] theorem Instance.initial_valid (I : Instance) : I.initial.Valid I.doors := by
  simp [Instance.initial, State.Valid]

/-- Traverse one currently enabled tunnel and flip precisely that door's state. -/
@[expose] def Step (doors : List Door) (s t : State) : Prop :=
  s.Valid doors ∧ ∃ i : Fin doors.length,
    let tunnel := doors[i].tunnel (s.bits.getD i.val false)
    s.location = tunnel.source ∧
      t = ⟨tunnel.target, s.bits.set i.val (!s.bits.getD i.val false)⟩

/-- A finite sequence of enabled door traversals, including an empty sequence. -/
abbrev Reachable (doors : List Door) := Relation.ReflTransGen (Step doors)

/-- One traversal preserves the number of door-state bits. -/
theorem Step.valid_target {doors : List Door} {s t : State} (h : Step doors s t) :
    t.Valid doors := by
  obtain ⟨hs, i, _, rfl⟩ := h
  simpa only [State.Valid, List.length_set] using hs

/-- Every configuration reached from a valid configuration has one bit per door. -/
theorem Reachable.valid {doors : List Door} {s t : State} (h : Reachable doors s t)
    (hs : s.Valid doors) : t.Valid doors := by
  induction h with
  | refl => exact hs
  | tail _ hstep _ => exact hstep.valid_target

/-- Networks admitting a path from the prescribed start to the target location. -/
@[expose] def Reachability : Set Instance :=
  {I | ∃ s, Reachable I.doors I.initial s ∧ s.location = I.target}

end Cslib.Complexity.SelfClosingDoor
