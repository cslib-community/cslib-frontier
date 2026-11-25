/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Basic
import Mathlib.Data.List.GetD

/-!
# Replacing directed wiring by symmetric self-closing doors

A directed arc is implemented by a door with an opening self-loop at its source and a
consuming tunnel along the arc. This allows constructions to separate directed control wiring
from the doors carrying their persistent state.

## Main definitions

* `Wiring.Step`: door traversals together with directed jumps.
* `Wiring.compile`: replace every directed jump by one symmetric door.

## Main results

* `Wiring.compile_reachability_iff`: directed wiring preserves target-location reachability.
-/

public section

namespace Cslib.Complexity.SelfClosingDoor.Wiring

/-- A door traversal or a directed jump preserving the door bits. -/
@[expose] def Step (doors : List Door) (arcs : List Tunnel) (s t : State) : Prop :=
  SelfClosingDoor.Step doors s t ∨
    (s.Valid doors ∧ ∃ a ∈ arcs, s.location = a.source ∧ t = ⟨a.target, s.bits⟩)

/-- Finite execution with directed wiring. -/
abbrev Reachable (doors : List Door) (arcs : List Tunnel) :=
  Relation.ReflTransGen (Step doors arcs)

/-- A directed arc with an opening self-loop at its source. -/
@[expose] def diode (a : Tunnel) : Door := ⟨⟨a.source, a.source⟩, a, false⟩

/-- Append one symmetric self-closing diode door for each directed arc. -/
@[expose] def compile (doors : List Door) (arcs : List Tunnel) (start target : ℕ) : Instance :=
  ⟨doors ++ arcs.map diode, start, target⟩

/-- Forget the auxiliary diode states. -/
private def project (doors : List Door) (s : State) : State :=
  ⟨s.location, s.bits.take doors.length⟩

/-- A directed jump, like a door traversal, preserves the configuration width. -/
theorem Step.valid_target {doors : List Door} {arcs : List Tunnel} {s t : State}
    (h : Step doors arcs s t) : t.Valid doors := by
  rcases h with h | ⟨hs, a, _, _, rfl⟩
  · exact h.valid_target
  · exact hs

private theorem project_valid {doors : List Door} {arcs : List Tunnel} {s : State}
    (hs : s.Valid (doors ++ arcs.map diode)) : (project doors s).Valid doors := by
  simp only [State.Valid, project, List.length_take]
  simp only [State.Valid, List.length_append, List.length_map] at hs
  omega

/-- Every actual traversal projects to stuttering or a legal step with directed wiring. -/
private theorem project_step {doors : List Door} {arcs : List Tunnel} {s t : State}
    (h : SelfClosingDoor.Step (doors ++ arcs.map diode) s t) :
    project doors s = project doors t ∨ Step doors arcs (project doors s) (project doors t) := by
  obtain ⟨hs, i, hp, rfl⟩ := h
  have hv := project_valid (arcs := arcs) hs
  by_cases hi : i.val < doors.length
  · have hd : (doors ++ arcs.map diode)[i.val] = doors[i.val] :=
      List.getElem_append_left hi
    have hb : (s.bits.take doors.length).getD i.val false = s.bits.getD i.val false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
    right
    left
    refine ⟨hv, ⟨i.val, hi⟩, ?_, ?_⟩
    · simpa only [project, Fin.getElem_fin, hd, hb] using hp
    · simp only [project, Fin.getElem_fin, hd, hb, List.take_set]
  · have hlo : doors.length ≤ i.val := by omega
    have hk : i.val - doors.length < arcs.length := by
      have := i.isLt
      simp only [List.length_append, List.length_map] at this
      omega
    have hd : (doors ++ arcs.map diode)[i.val] = diode arcs[i.val - doors.length] := by
      rw [List.getElem_append_right hlo, List.getElem_map]
    have hb : (s.bits.set i.val (!s.bits.getD i.val false)).take doors.length =
        s.bits.take doors.length := List.take_set_of_le hlo
    cases hbit : s.bits.getD i.val false with
    | false =>
      left
      apply State.ext
      · simpa only [project, Fin.getElem_fin, hd, hbit, diode, Door.tunnel,
          Bool.false_eq_true, ↓reduceIte]
          using hp
      · simpa only [project, hbit] using hb.symm
    | true =>
      right
      right
      refine ⟨hv, arcs[i.val - doors.length], List.getElem_mem hk, ?_, ?_⟩
      · simpa only [project, Fin.getElem_fin, hd, hbit, diode, Door.tunnel, ↓reduceIte] using hp
      · apply State.ext
        · simp only [project, Fin.getElem_fin, hd, diode, Door.tunnel, ↓reduceIte]
        · simpa only [project, hbit] using hb

/-- Forgetting auxiliary diode bits maps complete paths to paths with directed wiring. -/
private theorem project_reachable {doors : List Door} {arcs : List Tunnel} {s t : State}
    (h : SelfClosingDoor.Reachable (doors ++ arcs.map diode) s t) :
    Reachable doors arcs (project doors s) (project doors t) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    rcases project_step hstep with he | he
    · exact he ▸ ih
    · exact ih.tail he

private theorem append_step {doors more : List Door} {s t : State} (aux : List Bool)
    (hlen : aux.length = more.length) (h : SelfClosingDoor.Step doors s t) :
    SelfClosingDoor.Step (doors ++ more) ⟨s.location, s.bits ++ aux⟩
      ⟨t.location, t.bits ++ aux⟩ := by
  obtain ⟨hs, i, hp, rfl⟩ := h
  have hsl : s.bits.length = doors.length := hs
  have hi : i.val < s.bits.length := by omega
  refine ⟨?_, ⟨i.val, by simp only [List.length_append]; omega⟩, ?_, ?_⟩
  · simp only [State.Valid, List.length_append, hlen]
    exact congrArg (· + more.length) hs
  · simpa only [Fin.getElem_fin, List.getElem_append_left i.isLt,
      List.getD_append _ _ _ _ hi] using hp
  · simp only [Fin.getElem_fin, List.getElem_append_left i.isLt,
      List.getD_append _ _ _ _ hi, List.set_append_left _ _ hi]

private theorem diode_step {doors : List Door} {arcs : List Tunnel} (s : State)
    (hs : s.Valid doors) (aux : List Bool) (hlen : aux.length = arcs.length)
    (k : Fin arcs.length) (b : Bool) (hb : aux.getD k.val false = b)
    (hp : s.location = arcs[k].source) :
    SelfClosingDoor.Step (doors ++ arcs.map diode) ⟨s.location, s.bits ++ aux⟩
      ⟨if b then arcs[k].target else arcs[k].source,
        s.bits ++ aux.set k.val (!b)⟩ := by
  have hi : doors.length + k.val < (doors ++ arcs.map diode).length := by
    simp only [List.length_append, List.length_map]
    omega
  have hd : (doors ++ arcs.map diode)[doors.length + k.val] = diode arcs[k] := by
    simp only [List.getElem_append_right (Nat.le_add_right _ _), List.getElem_map,
      Nat.add_sub_cancel_left, Fin.getElem_fin]
  have hsl : s.bits.length = doors.length := hs
  have hbits : (s.bits ++ aux).getD (doors.length + k.val) false = b := by
    rw [List.getD_append_right _ _ _ _ (by omega), hsl, Nat.add_sub_cancel_left, hb]
  have hset : (s.bits ++ aux).set (doors.length + k.val) (!b) =
      s.bits ++ aux.set k.val (!b) := by
    rw [List.set_append_right _ _ (by omega), hsl, Nat.add_sub_cancel_left]
  refine ⟨?_, ⟨doors.length + k.val, hi⟩, ?_, ?_⟩
  · simp only [State.Valid, List.length_append, List.length_map, hlen]
    exact congrArg (· + arcs.length) hs
  · cases b <;>
      simpa only [Fin.getElem_fin, hd, hbits, diode, Door.tunnel, Bool.false_eq_true,
        ↓reduceIte] using hp
  · cases b <;> simp only [Fin.getElem_fin, hd, hbits, diode, Door.tunnel,
      Bool.false_eq_true, ↓reduceIte, hset]

private theorem lift_arc {doors : List Door} {arcs : List Tunnel} (s : State)
    (hs : s.Valid doors) (aux : List Bool) (hlen : aux.length = arcs.length)
    (a : Tunnel) (ha : a ∈ arcs) (hp : s.location = a.source) :
    ∃ aux', aux'.length = arcs.length ∧
      SelfClosingDoor.Reachable (doors ++ arcs.map diode) ⟨s.location, s.bits ++ aux⟩
        ⟨a.target, s.bits ++ aux'⟩ := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.1 ha
  have hak : arcs[k] = a := hk
  cases hb : aux.getD k.val false with
  | true =>
    refine ⟨aux.set k.val false, by simpa only [List.length_set] using hlen, ?_⟩
    exact Relation.ReflTransGen.single (by
      simpa only [hak, Bool.not_true, ↓reduceIte] using diode_step s hs aux hlen k true hb
        (hak.symm ▸ hp))
  | false =>
    let aux' := aux.set k.val true
    have hlen' : aux'.length = arcs.length := by simp only [aux', List.length_set, hlen]
    have hb' : aux'.getD k.val false = true := by
      simp only [aux', List.getD_eq_getElem?_getD,
        List.getElem?_set_self (by omega : k.val < aux.length), Option.getD_some]
    have hfirst := diode_step s hs aux hlen k false hb (hak.symm ▸ hp)
    have hsecond := diode_step s hs aux' hlen' k true hb' (hak.symm ▸ hp)
    refine ⟨aux'.set k.val false, by simp only [List.length_set, hlen'], ?_⟩
    exact (Relation.ReflTransGen.single (by
      simpa only [hak, Bool.not_false, Bool.false_eq_true, ↓reduceIte, ← hp] using hfirst)).tail (by
      simpa only [hak, Bool.not_true, Bool.false_eq_true, ↓reduceIte, aux'] using hsecond)

/-- Every wired step lifts while retaining the principal bits and some auxiliary diode bits. -/
private theorem lift_step {doors : List Door} {arcs : List Tunnel} {s t : State}
    (h : Step doors arcs s t) (aux : List Bool) (hlen : aux.length = arcs.length) :
    ∃ aux', aux'.length = arcs.length ∧
      SelfClosingDoor.Reachable (doors ++ arcs.map diode) ⟨s.location, s.bits ++ aux⟩
        ⟨t.location, t.bits ++ aux'⟩ := by
  rcases h with h | ⟨hs, a, ha, hp, rfl⟩
  · exact ⟨aux, hlen, .single (append_step aux (by simpa only [List.length_map] using hlen) h)⟩
  · exact lift_arc s hs aux hlen a ha hp

/-- A complete wired path lifts for every initial assignment of auxiliary diode states. -/
private theorem lift_reachable {doors : List Door} {arcs : List Tunnel} {s t : State}
    (h : Reachable doors arcs s t) (aux : List Bool) (hlen : aux.length = arcs.length) :
    ∃ aux', aux'.length = arcs.length ∧
      SelfClosingDoor.Reachable (doors ++ arcs.map diode) ⟨s.location, s.bits ++ aux⟩
        ⟨t.location, t.bits ++ aux'⟩ := by
  induction h with
  | refl => exact ⟨aux, hlen, .refl⟩
  | tail _ hstep ih =>
    obtain ⟨aux', hlen', hr⟩ := ih
    obtain ⟨aux'', hlen'', hr'⟩ := lift_step hstep aux' hlen'
    exact ⟨aux'', hlen'', hr.trans hr'⟩

/-- Replacing directed wiring by diode doors preserves the target-location decision problem. -/
theorem compile_reachability_iff (doors : List Door) (arcs : List Tunnel) (start target : ℕ) :
    compile doors arcs start target ∈ Reachability ↔
      ∃ s, Reachable doors arcs ⟨start, doors.map Door.initial⟩ s ∧ s.location = target := by
  constructor
  · rintro ⟨s, hr, hp⟩
    refine ⟨project doors s, ?_, hp⟩
    simpa [project, compile, Instance.initial] using project_reachable hr
  · rintro ⟨s, hr, hp⟩
    let aux := (arcs.map diode).map Door.initial
    obtain ⟨aux', _, hr'⟩ := lift_reachable hr aux (by simp [aux])
    refine ⟨⟨s.location, s.bits ++ aux'⟩, ?_, hp⟩
    simpa only [compile, Instance.initial, List.map_append, aux] using hr'

end Cslib.Complexity.SelfClosingDoor.Wiring
