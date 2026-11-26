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
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
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
  have hm := (computableInPolyTime_length_vars encRel encNat).comp
    (encState_body_polyTime encRel (ComputableInPolyTime.fst (encState encRel) (encList encNat)))
  growth_poly [fun F => (CSP.vars_length_eq_occurrences (F := F)).symm]

private theorem resource_size (encRel : Rel ↪ List Bool) (p : State Rel × List ℕ)
    (J : State Rel) (h : resource p.1 J) :
    (encState encRel J).length ≤ 64*(4*sizeParameter encRel p+1)^3 := by
  obtain ⟨h1, h2, h3, h4, h5, rfl | ⟨ht1, ht2⟩⟩ := h
  · have hS : (encState encRel p.1).length ≤ sizeParameter encRel p :=
      (show (encState encRel p.1).length ≤ (encStateMetadata encRel p).length by
        enc_len [encStateMetadata]).trans (by dsimp only [sizeParameter]; omega)
    exact hS.trans (by nlinarith [Nat.zero_le (sizeParameter encRel p ^ 3)])
  · let N := sizeParameter encRel p
    have hS : (encState encRel p.1).length ≤ N :=
      (show (encState encRel p.1).length ≤ (encStateMetadata encRel p).length by
        enc_len [encStateMetadata]).trans (by dsimp only [N, sizeParameter]; omega)
    have hM : p.1.body.occurrences.length ≤ N := by dsimp only [N, sizeParameter]; omega
    obtain ⟨hi1, hi2, _, hi4, hi5⟩ := State.component_size_le_encoding encRel p.1
    have hr : J.body.map Constraint.rel = p.1.body.map Constraint.rel := by
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) h3
    refine State.encoding_length_le encRel J (4 * N) (by omega) (by omega) (by omega) (by omega)
      (hr ▸ hi4.trans (by omega))
      (fun z hz => (hi5 z (h5 hz)).trans (by omega))
      (fun v hv => (Nat.size_le_self v).trans (by have := ht2 v hv; omega))

private theorem step_poly (encRel : Rel ↪ List Bool) : ComputableInPolyTime
      (fun p : ((List ℕ) × State Rel) × ℕ =>
        closeFirstMetadataRun p.1.2 (p.1.1.drop (p.1.1.length-p.1.2.ports.length)))
      (encPair (encPair (encList encNat) (encState encRel)) encNat) (encState encRel) := by
  let input := encPair (encPair (encList encNat) (encState encRel)) encNat
  have hp1 := ComputableInPolyTime.fst (encPair (encList encNat) (encState encRel)) encNat
  have hk := (ComputableInPolyTime.fst (encList encNat) (encState encRel)).comp hp1
  have hi := (ComputableInPolyTime.snd (encList encNat) (encState encRel)).comp hp1
  have hdrop := ComputableInPolyTime.listDropWithInput hk
    (ComputableInPolyTime.unary_sub' ((ComputableInPolyTime.length_list encNat).comp hk)
      ((ComputableInPolyTime.length_list encNat).comp (encState_ports_polyTime encRel hi)))
  exact ((computableInPolyTime_closeFirstMetadataRun encRel).comp
    (hi.prod hdrop : ComputableInPolyTime _ input (encStateMetadata encRel))).of_enc_eq fun _ => rfl


/-- Close every actual consecutive run in plain polynomial time on EVERY raw State and
binary metadata word. The input lists fund counts; relation symbols and malformed huge
entries remain encoded data. All prefix growth is derived internally. -/
theorem computableInPolyTime_closeMetadataRuns (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => closeMetadataRuns p.1 p.2)
      (encStateMetadata encRel) (encState encRel) := by
  have hi := ComputableInPolyTime.fst (encState encRel) (encList encNat)
  have hk := ComputableInPolyTime.snd (encState encRel) (encList encNat)
  have hbound : PolyBounded (fun p => (encStateMetadata encRel p).length)
      (fun p => 64 * (4 * sizeParameter encRel p + 1) ^ 3) := by
    growth_poly [sizeParameter_poly encRel]
  have hfold := ComputableInPolyTime.foldlWith_spec
    (encP := encList encNat) (encA := encNat) (encL := encList encNat)
    (par := Prod.snd) (list := Prod.snd) (init := Prod.fst)
    (step := fun keys J _ => closeFirstMetadataRun J (keys.drop (keys.length - J.ports.length)))
    hk hk hi (step_poly encRel) (fun p _ J => resource p.1 J) (fun p => resource_self p.1)
    (fun p _ J _ _ hJ => resource_step p.1 J _ hJ) hbound
    (fun p _ J _ hJ => resource_size encRel p J hJ)
  exact ComputableInPolyTime.ite_decide
    (condition := fun p : State Rel × List ℕ => p.2.length ≠ p.1.ports.length)
    (by fun_prop) hi hfold.1

end Cslib.Complexity.CSP.CrossInsertion
