/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryFusion
import CslibFrontier.Computability.PolyTime.Graph.RotationSystem.Reindex
import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Logic.Function.Basic

/-!
# Native polynomial time for raw head-wire fusion

The existing `CrossInsertion.fuseHead` is certified on every raw state, with the unchanged
`CrossInsertion.encState` layout: the binary-named body, then the binary boundary word, then
the binary successor table. The first two fields are framed. The relation alphabet is arbitrary.

The residual boundary count is computed in unary from the actual twice-tailed port list.
Body occurrence counts and table-walk clocks also come from actual lists. Binary variable
names, queried corners and malformed successor entries are compared or read with the existing
saturating lookup program; their numerical values never fund a loop. No checker invariant,
distinctness, arity bound or bound on table entries is used.

This is the runtime certificate for one original head-identification operation. Sequential
CROSS transposition and its accumulated iteration bound remain objectives of
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main results

* `CrossInsertion.computableInPolyTime_fuseHead`: native polynomial time on all raw states.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph Turing.MultiTapeTM

variable {Rel : Type}

-- The outer range is funded by the computed unary retained-dart count. Each inner range
-- and each successor walk use only the actual table length, even on malformed tables.
private theorem restrictPrefix_polyTime {α : Type} {input : α ↪ List Bool}
    {table : α → RotationCertificate} {count : α → ℕ}
    (hc : ComputableInPolyTime table input encRotationCertificate)
    (hn : ComputableInPolyTime count input encUnary) :
    ComputableInPolyTime (fun a => restrictPrefix (count a) (table a))
      input encRotationCertificate := by
  have hs := RotationCertificate.computableInPolyTime_successor.comp hc
  have hsteps := (ComputableInPolyTime.length_list encNat).comp hs
  have hbound := ComputableInPolyTime.unary_to_binary.comp hn
  have hout : ComputableInPolyTime (fun a => (List.range (count a)).map fun i =>
      (((List.range (table a).successor.length).map fun k =>
        RotationCertificate.walk (table a).successor (k + 1) i).find?
          (fun j => decide (j < count a))).getD 0) input (encList encNat) := by
    apply ComputableInPolyTime.mapWithInput (encA := encUnary)
      (ComputableInPolyTime.range.comp hn)
    have hp := ComputableInPolyTime.fst input encUnary
    have hi := ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.snd input encUnary)
    have hwalks : ComputableInPolyTime (fun p : α × ℕ =>
        (List.range (table p.1).successor.length).map fun k =>
          RotationCertificate.walk (table p.1).successor (k + 1) p.2)
        (encPair input encUnary) (encList encNat) := by
      apply ComputableInPolyTime.mapWithInput (encA := encUnary)
        (ComputableInPolyTime.range.comp (hsteps.comp hp))
      have hq := ComputableInPolyTime.fst (encPair input encUnary) encUnary
      have hk := ComputableInPolyTime.snd (encPair input encUnary) encUnary
      exact RotationCertificate.computableInPolyTime_walk.comp
        ((((hs.comp hp).comp hq).prod (ComputableInPolyTime.unary_succ.comp hk)).prod
          (hi.comp hq))
    have hfind := ComputableInPolyTime.findWithInput
      (test := fun (p : α × ℕ) j => decide (j < count p.1)) hwalks
      (ComputableInPolyTime.binary_lt'
        (ComputableInPolyTime.snd (encPair input encUnary) encNat)
        ((hbound.comp hp).comp (ComputableInPolyTime.fst (encPair input encUnary) encNat)))
    exact ComputableInPolyTime.optionGetDWithInput hfind (ComputableInPolyTime.const 0)
  exact encRotationCertificate_mk_deg.computableInPolyTime.comp hout

/-- Fuse the first two boundary wires in native polynomial time on every raw state.
Names and table entries are binary; all counts are computed in unary from actual lists.
The residual boundary length varies with the input, with no acceptance or arity premise. -/
theorem computableInPolyTime_fuseHead (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fuseHead (Rel := Rel)) (encState encRel) (encState encRel) := by
  let input := encState encRel
  have hbody : ComputableInPolyTime (State.body (Rel := Rel)) input
      (encCSP encRel encNat) := encState_body_polyTime encRel .id'
  have hports : ComputableInPolyTime (State.ports (Rel := Rel)) input
      (encList encNat) := encState_ports_polyTime encRel .id'
  have hrot : ComputableInPolyTime (State.rotation (Rel := Rel)) input
      encRotationCertificate := encState_rotation_polyTime encRel .id'
  have htail := (ComputableInPolyTime.tail (encA := encNat)).comp hports
  have hrest := (ComputableInPolyTime.tail (encA := encNat)).comp htail
  have hfirst := (ComputableInPolyTime.headD (encA := encNat) 0).comp hports
  have hsecond := (ComputableInPolyTime.headD (encA := encNat) 0).comp htail
  let update (I : State Rel) := Function.update id (I.ports.tail.headD 0) (I.ports.headD 0)
  have hupdate : ComputableInPolyTime (fun p : State Rel × ℕ => update p.1 p.2)
      (encPair input encNat) encNat := by
    dsimp only [update]
    simp only [Function.update_apply, id_eq]
    apply ComputableInPolyTime.ite_decide
    · exact ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd input encNat)
        (hsecond.comp (ComputableInPolyTime.fst input encNat))
    · exact hfirst.comp (ComputableInPolyTime.fst input encNat)
    · exact ComputableInPolyTime.snd input encNat
  have hrenamed : ComputableInPolyTime (fun I : State Rel => I.body.relabel (update I))
      input (encCSP encRel encNat) := by
    unfold CSP.relabel Constraint.relabel
    apply ComputableInPolyTime.mapWithInput (encA := encConstraint encRel encNat) hbody
    apply encConstraint_mk_polyTime
    · exact encConstraint_rel_polyTime
        (ComputableInPolyTime.snd input (encConstraint encRel encNat))
    · apply ComputableInPolyTime.mapWithInput (encA := encNat)
        (encConstraint_scope_polyTime
          (ComputableInPolyTime.snd input (encConstraint encRel encNat)))
      exact hupdate.comp (g := fun p : (State Rel × Constraint Rel ℕ) × ℕ => (p.1.1, p.2))
        (by fun_prop)
  have hsurvivors := ComputableInPolyTime.mapWithInput htail hupdate
  let m (I : State Rel) := I.body.occurrences.length
  let n (I : State Rel) := I.ports.tail.tail.length
  have hm : ComputableInPolyTime m input encUnary := by
    have h := (computableInPolyTime_length_vars encRel encNat).comp hbody
    simpa only [m, Function.comp_def, CSP.vars_length_eq_occurrences] using h
  have hn : ComputableInPolyTime n input encUnary :=
    (ComputableInPolyTime.length_list encNat).comp hrest
  have hcount : ComputableInPolyTime (fun I => 2 * (m I + (n I + 1)))
      input encUnary := by fun_prop
  have hleft : ComputableInPolyTime (fun I => 2 * (m I + n I + 1))
      input encUnary := by fun_prop
  have hquery : ComputableInPolyTime (fun I => 2 * (m I + n I))
      input encUnary := by fun_prop
  have hidx := ComputableInPolyTime.idxOfWithInput
    (RotationCertificate.computableInPolyTime_successor.comp hrot)
    (ComputableInPolyTime.unary_to_binary.comp hquery)
  have hswap := RotationCertificate.computableInPolyTime_swapSuccessors hrot
    (ComputableInPolyTime.unary_to_binary.comp hleft)
    (ComputableInPolyTime.unary_to_binary.comp hidx)
  have hcertificate : ComputableInPolyTime (fun I : State Rel =>
      equalDropCertificate I.body (I.ports.tail.tail.length) I.rotation)
      input encRotationCertificate := by
    simpa only [equalDropCertificate, m, n, Function.comp_def] using
      restrictPrefix_polyTime hswap hcount
  have houtput := encState_mk_polyTime encRel hrenamed hsurvivors hcertificate
  have hshort := ComputableInPolyTime.binary_lt'
    (ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.length_list encNat).comp hports)) (ComputableInPolyTime.const 2)
  have hbranch := ComputableInPolyTime.ite_decide hshort
    (ComputableInPolyTime.id' (encIn := input)) houtput
  apply hbranch.of_enc_eq
  intro I
  apply congrArg (encState encRel)
  rcases I with ⟨F, ports, c⟩
  cases ports with
  | nil => rfl
  | cons x ports =>
    cases ports with
    | nil => rfl
    | cons y ps => simp [fuseHead, update]

end Cslib.Complexity.CSP.CrossInsertion
