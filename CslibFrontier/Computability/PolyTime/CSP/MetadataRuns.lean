/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.MetadataRuns
public import CslibFrontier.Computability.PolyTime.CSP.BoundaryGroup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.PolyTime.CSP.StateSize
import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Tactic.EncLen

/-!
# Plain native cost of closing all consecutive metadata runs

A captured, list-funded fold uses the existing first-run certificate. Its own invariant
bounds every reachable outer prefix directly: original rows, occurrences, relation payload,
selected original names and decreasing ports. The table is either the original raw table
or an actual regenerated bounded table. No polynomial output estimate is iterated through
the groups. The envelope is storage, not an exact clock; all statements use plain cost.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph Turing.MultiTapeTM Cslib.BitString

variable {Rel : Type}

private def resource (I J : State Rel) : Prop :=
  J.body.length=I.body.length ∧ J.body.occurrences.length=I.body.occurrences.length ∧
    J.body.map (fun c => (c.rel,c.scope.length))=I.body.map (fun c => (c.rel,c.scope.length)) ∧
    J.ports.length≤I.ports.length ∧ J.body.vars++J.ports ⊆ I.body.vars++I.ports ∧
    (J=I ∨ J.rotation.successor.length=2*(I.body.occurrences.length+J.ports.length) ∧
      ∀ v∈J.rotation.successor, v<2*(I.body.occurrences.length+J.ports.length))

private theorem resource_self (I : State Rel) : resource I I :=
  ⟨rfl,rfl,rfl,le_rfl,fun _ h => h,Or.inl rfl⟩

private theorem resource_step (I J : State Rel) (keys : List ℕ) (h : resource I J) :
    resource I (closeFirstMetadataRun J keys) := by
  have hc := components_closeFirstMetadataRun J keys
  have hn := names_closeFirstMetadataRun_subset J keys
  have hp : (closeFirstMetadataRun J keys).ports.length≤J.ports.length := by
    rw [hc.2.2.2]
    exact Nat.sub_le _ _
  refine ⟨hc.1.trans h.1,hc.2.1.trans h.2.1,hc.2.2.1.trans h.2.2.1,
    hp.trans h.2.2.2.1,fun _ hz => h.2.2.2.2.1 (hn hz),?_⟩
  by_cases hl : keys.length=J.ports.length
  · cases keys with
    | nil => simpa only [closeFirstMetadataRun_eq_self J [] (Or.inr rfl)] using h.2.2.2.2.2
    | cons a ks =>
      have hf := fields_closeFirstMetadataRun J a ks hl
      right
      have hp : (closeFirstMetadataRun J (a::ks)).ports.length = J.ports.length-
          (List.takeWhile (fun b => decide (b=a)) (a::ks)).length := by
        rw [(components_closeFirstMetadataRun J (a::ks)).2.2.2]
        simp only [ite_eq_left hl,List.headD_cons]
        rfl
      have hr : (List.takeWhile (fun b => decide (b=a)) (a::ks)).length ≤ J.ports.length :=
        (List.takeWhile_sublist _).length_le.trans_eq hl
      constructor
      · have hx := hf.2.2.1
        rw [h.2.1] at hx
        omega
      · intro v hv
        have hx := hf.2.2.2 v hv
        rw [h.2.1] at hx
        omega
  · simpa only [closeFirstMetadataRun_eq_self J keys (Or.inl hl)] using h.2.2.2.2.2

private def sizeParameter (encRel : Rel ↪ List Bool) (p : State Rel × List ℕ) : ℕ :=
  (encStateMetadata encRel p).length+p.1.body.occurrences.length+1

private theorem sizeParameter_poly (encRel : Rel ↪ List Bool) :
    PolyBounded (fun p => (encStateMetadata encRel p).length) (sizeParameter encRel) := by
  have hi := ComputableInPolyTime.fst (encState encRel) (encList encNat)
  have hb := encState_body_polyTime encRel hi
  have hm := (computableInPolyTime_length_vars encRel encNat).comp hb
  have hM : PolyBounded (fun p => (encStateMetadata encRel p).length)
      (fun p : State Rel × List ℕ => p.1.body.occurrences.length) := by
    simpa only [Function.comp_apply,encUnary_apply,List.length_replicate,
      CSP.vars_length_eq_occurrences] using hm.polyBounded_length
  exact (PolyBounded.self.add hM).add (.const 1)

private theorem resource_size (encRel : Rel ↪ List Bool) (p : State Rel × List ℕ)
    (J : State Rel) (h : resource p.1 J) :
    (encState encRel J).length ≤ 64*(4*sizeParameter encRel p+1)^3 := by
  let N := sizeParameter encRel p
  have hN : 1≤N := by dsimp only [N,sizeParameter]; omega
  have hS : (encState encRel p.1).length≤N := by
    apply le_trans (show (encState encRel p.1).length≤(encStateMetadata encRel p).length by
      enc_len [encStateMetadata])
    dsimp only [N,sizeParameter]
    omega
  have hM : p.1.body.occurrences.length≤N := by dsimp only [N,sizeParameter]; omega
  have hi := State.component_size_le_encoding encRel p.1
  rcases h.2.2.2.2.2 with rfl | ht
  · exact hS.trans (by nlinarith [Nat.zero_le (N*N*N)])
  · apply State.encoding_length_le encRel J (4*N)
    · rw [h.1]; exact hi.1.trans (by omega)
    · rw [h.2.1]; omega
    · exact h.2.2.2.1.trans (hi.2.1.trans (by omega))
    · rw [ht.1]
      have hp := h.2.2.2.1.trans (hi.2.1.trans hS)
      omega
    · have he := congrArg (List.map Prod.fst) h.2.2.1
      have hr : J.body.map Constraint.rel=p.1.body.map Constraint.rel := by
        simpa only [List.map_map,Function.comp_def] using he
      rw [hr]
      exact hi.2.2.2.1.trans (by omega)
    · intro z hz
      exact (hi.2.2.2.2 z (h.2.2.2.2.1 hz)).trans (by omega)
    · intro v hv
      have hb := ht.2 v hv
      have hp := h.2.2.2.1.trans (hi.2.1.trans hS)
      exact (Nat.size_le_self v).trans (by omega)

private theorem step_poly (encRel : Rel ↪ List Bool) : ComputableInPolyTime
      (fun p : ((List ℕ) × State Rel) × ℕ =>
        closeFirstMetadataRun p.1.2 (p.1.1.drop (p.1.1.length-p.1.2.ports.length)))
      (encPair (encPair (encList encNat) (encState encRel)) encNat) (encState encRel) := by
  let input := encPair (encList encNat) (encState encRel)
  have inner : ComputableInPolyTime
      (fun p : List ℕ × State Rel =>
        closeFirstMetadataRun p.2 (p.1.drop (p.1.length-p.2.ports.length)))
      input (encState encRel) := by
    have hk : ComputableInPolyTime (fun p : List ℕ × State Rel => p.1)
        input (encList encNat) := ComputableInPolyTime.fst _ _
    have hi : ComputableInPolyTime (fun p : List ℕ × State Rel => p.2)
        input (encState encRel) := ComputableInPolyTime.snd _ _
    have hlen : ComputableInPolyTime (fun p : List ℕ × State Rel => p.1.length)
        input encUnary := (ComputableInPolyTime.length_list encNat).comp hk
    have hports : ComputableInPolyTime (fun p : List ℕ × State Rel => p.2.ports.length)
        input encUnary := (ComputableInPolyTime.length_list encNat).comp
          (encState_ports_polyTime encRel hi)
    have hdrop : ComputableInPolyTime
        (fun p : List ℕ × State Rel => p.1.drop (p.1.length-p.2.ports.length))
        input (encList encNat) := ComputableInPolyTime.listDropWithInput hk
          (ComputableInPolyTime.unary_sub' hlen hports)
    have hinput : ComputableInPolyTime
        (fun p : List ℕ × State Rel => (p.2,p.1.drop (p.1.length-p.2.ports.length)))
        input (encStateMetadata encRel) := hi.prod hdrop
    apply ((computableInPolyTime_closeFirstMetadataRun encRel).comp hinput).of_enc_eq
    intro p
    rfl
  apply (inner.comp (ComputableInPolyTime.fst input encNat)).of_enc_eq
  intro p
  rfl


/-- Close every actual consecutive run in plain polynomial time on EVERY raw State and
binary metadata word. The input lists fund counts; relation symbols and malformed huge
entries remain encoded data. All prefix growth is derived internally. -/
theorem computableInPolyTime_closeMetadataRuns (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => closeMetadataRuns p.1 p.2)
      (encStateMetadata encRel) (encState encRel) := by
  have hi := ComputableInPolyTime.fst (encState encRel) (encList encNat)
  have hk := ComputableInPolyTime.snd (encState encRel) (encList encNat)
  have hstep := step_poly encRel
  have hbound : PolyBounded (fun p => (encStateMetadata encRel p).length)
      (fun p => 64*(4*sizeParameter encRel p+1)^3) := by
    exact (PolyBounded.const 64).mul
      ((((PolyBounded.const 4).mul (sizeParameter_poly encRel)).add (.const 1)).pow 3)
  have hfold := ComputableInPolyTime.foldlWith_spec
    (encP := encList encNat) (encA := encNat) (encL := encList encNat)
    (par := fun p : State Rel × List ℕ => p.2) (list := fun p => p.2)
    (init := fun p => p.1)
    (step := fun keys J _ => closeFirstMetadataRun J
      (keys.drop (keys.length-J.ports.length))) hk hk hi hstep
    (fun p _ J => resource p.1 J) (fun p => resource_self p.1)
    (fun p _ J _ _ hJ => resource_step p.1 J _ hJ) hbound
    (fun p _ J _ hJ => resource_size encRel p J hJ)
  have hg : ComputableInPolyTime
      (fun p : State Rel × List ℕ => decide (p.2.length≠p.1.ports.length))
      (encStateMetadata encRel) encBool := by fun_prop
  exact ComputableInPolyTime.ite_decide hg hi hfold.1

end Cslib.Complexity.CSP.CrossInsertion
