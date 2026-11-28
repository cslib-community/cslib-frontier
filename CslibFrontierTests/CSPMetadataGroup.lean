/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.SortMetadataGroup
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Crossover
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary

/-!
# Ordinary clients of actual first-run coalescing

Production atom tables and Figure 1(b) supply the real sorting input. Literal fields,
full checker, one-output recovery and universal forwarding are exercised separately from
raw repeated-name and malformed-table cases. Equality is not inferred from values assigned
to names eliminated from the output body.
-/

public section

namespace CslibFrontierTests.CSPMetadataGroup

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open Cslib.Complexity Cslib.Complexity.CSP OrderedBoundary CrossInsertion
open Cslib.AdjacentSortTrace Turing.MultiTapeTM Cslib.BitString

private abbrev g := figureOneB
private abbrev w := figureOneBBoundary
private def atom : State Unit :=
  ⟨[⟨(),[10,20,30,40]⟩],[10,20,30,40],atomBoundaryCertificate 4⟩
private def keys : List ℕ := [2,1,2,1]
private def sigma (z : ℕ) : Bool := decide (z=20 ∨ z=40)
private def C (z : ℕ) : ℕ := if z∈([10,5] : List ℕ) then 10 else z

private theorem computed_keys : compute keys = ⟨[1,1,2,2],[2,0,1]⟩ := by
  simp [keys, compute, Cslib.AdjacentSortTrace.insert, List.range_succ]

example : (compute keys).requests=[2,0,1] ∧
    (sortBoundaryMetadata g w atom keys).ports=[10,5,7,28] := by
  rw [sortBoundaryMetadata, computed_keys]
  decide +kernel

example : sortAndCloseFirstMetadataRun g w atom keys=
    hideHead (fuseHead (sortBoundaryMetadata g w atom keys)) := by
  rw [sortAndCloseFirstMetadataRun, sortBoundaryMetadata, computed_keys]
  rfl

example : (sortAndCloseFirstMetadataRun g w atom keys).ports=[7,28] := by
  rw [sortAndCloseFirstMetadataRun, computed_keys]
  decide +kernel

example : (sortAndCloseFirstMetadataRun g w atom keys).body.length=7 ∧
    (sortAndCloseFirstMetadataRun g w atom keys).body.occurrences.length=28 ∧
    (sortAndCloseFirstMetadataRun g w atom keys).ports.length=2 ∧
    (sortAndCloseFirstMetadataRun g w atom keys).rotation.successor.length=60 := by
  rw [sortAndCloseFirstMetadataRun, computed_keys]
  decide +kernel

example : (sortAndCloseFirstMetadataRun g w atom keys).Accepted :=
  accepted_sortAndCloseFirstMetadataRun g w atom keys (by decide +kernel)

example : OrderedBoundary.verify (sortAndCloseFirstMetadataRun g w atom keys).body
    (sortAndCloseFirstMetadataRun g w atom keys).ports
    (sortAndCloseFirstMetadataRun g w atom keys).rotation=true :=
  (accepted_sortAndCloseFirstMetadataRun g w atom keys (by decide +kernel)).2

example : ∃ τ : ℕ → Bool,
    (sortAndCloseFirstMetadataRun g w atom keys).body.eval nearSem τ = true ∧
    (∀ z,τ (8*z)=sigma z) ∧ τ (8*123456)=false ∧
    (sortAndCloseFirstMetadataRun g w atom keys).ports.map τ=[false,false] := by
  obtain ⟨τ,ht,ha,hv⟩ :=
    forward_sortAndCloseFirstMetadataRun g w atom keys rfl (by decide +kernel) sigma
      (by decide +kernel) (by simp only [computed_keys]; decide +kernel)
  simp only [computed_keys] at ha hv
  change ∀ z,τ (8*z)=sigma z at ha
  change _=[sigma 10,sigma 30] at hv
  exact ⟨τ,ht,ha,by simpa [sigma] using ha 123456,by simpa [sigma] using hv⟩

example (τ : ℕ → Bool)
    (ht : (sortAndCloseFirstMetadataRun g w atom keys).body.eval nearSem τ = true) :
    atom.body.eval nearSem (fun z => τ (C (8*z)))=true ∧
    τ (C (8*20))=τ (C (8*40)) ∧
    (sortAndCloseFirstMetadataRun g w atom keys).ports.map τ=
      [τ (C (8*10)),τ (C (8*30))] := by
  have h := recover_sortAndCloseFirstMetadataRun g w atom keys rfl (by decide +kernel) τ ht
  simp only [sortBoundaryMetadata, computed_keys] at h
  change _ ∧ (∀ b∈[τ (C (8*20)),τ (C (8*40))],b=τ 10) ∧ _ at h
  exact ⟨h.1,(h.2.1 _ (by simp)).trans (h.2.1 _ (by simp)).symm,h.2.2⟩

example : ¬∃ τ : ℕ → Bool,
    (sortAndCloseFirstMetadataRun g w atom keys).body.eval nearSem τ = true ∧
      τ (C (8*20))≠τ (C (8*40)) := by
  rintro ⟨τ,ht,hne⟩
  have h := recover_sortAndCloseFirstMetadataRun g w atom keys rfl (by decide +kernel) τ ht
  simp only [sortBoundaryMetadata, computed_keys] at h
  change _ ∧ (∀ b∈[τ (C (8*20)),τ (C (8*40))],b=τ 10) ∧ _ at h
  exact hne ((h.2.1 _ (by simp)).trans (h.2.1 _ (by simp)).symm)

private def raw (ports : List ℕ) : State Unit := ⟨[],ports,⟨[]⟩⟩

example : closeFirstMetadataRun (raw [9,4,2]) [1,1,1]=
    hideHead (fuseHead (fuseHead (raw [9,4,2]))) := by rfl

example : closeFirstMetadataRun (raw [9,4,2]) [1,1,1]=raw [] := by rfl

example : closeFirstMetadataRun (raw [9,4,2]) [1,2,2]=hideHead (raw [9,4,2]) := by rfl

-- Relabeling is global: the two raw repeated names in later positions also change.
example : (closeFirstMetadataRun (raw [9,4,9,4]) [1,1,2,2]).ports=[9,9] ∧
    (closeFirstMetadataRun (raw [9,4,9,4]) [1,1,2,2]).rotation.successor=[0,0,0,0] := by
  decide +kernel

-- Unsorted helper input consumes the first consecutive run, not every matching key.
example : (closeFirstMetadataRun (raw [9,4,2,3]) [1,1,2,1]).ports=[2,3] := by decide +kernel

private def different (z : ℕ) : Bool := decide (z=4)

-- This is a counterexample to inferring input equality from output/all-name agreement.
example : (∃ τ : ℕ → Bool,
    (closeFirstMetadataRun (raw [9,4]) [1,1]).body.eval nearSem τ = true ∧
    (∀ z,τ z=different z)) ∧ different 9≠different 4 := by
  exact ⟨⟨different,rfl,fun _ => rfl⟩,by decide +kernel⟩

-- Recovering at an eliminated name really changes it; bare old-name recovery is false.
example : let collapse := fun z : ℕ => if z∈([9,4] : List ℕ) then 9 else z
    different (collapse 4)≠different 4 := by decide +kernel

private def broken : State Unit :=
  ⟨[⟨(),[]⟩,⟨(),[17,17]⟩,⟨(),[17,17]⟩], [2^250,17,17,2^250],⟨[2^300,9,9]⟩⟩

example : closeFirstMetadataRun broken [1,1,1]=broken :=
  closeFirstMetadataRun_eq_self _ _ (Or.inl (by decide +kernel))

example : sortAndCloseFirstMetadataRun g w broken [1,1,1]=broken :=
  sortAndCloseFirstMetadataRun_eq_self g w _ _ (Or.inl (by decide +kernel))

example : closeFirstMetadataRun (⟨broken.body,[],broken.rotation⟩ : State Unit) []=
    ⟨broken.body,[],broken.rotation⟩ := closeFirstMetadataRun_eq_self _ _ (Or.inr rfl)

example : sortAndCloseFirstMetadataRun g w (⟨broken.body,[],broken.rotation⟩ : State Unit) []=
    ⟨broken.body,[],broken.rotation⟩ :=
  sortAndCloseFirstMetadataRun_eq_self g w _ _ (Or.inr rfl)

private theorem singleton_raw (F : CSP Unit ℕ) (p H : ℕ) (c : Graph.RotationCertificate) :
    closeFirstMetadataRun (⟨F,[p],c⟩ : State Unit) [H]=hideHead ⟨F,[p],c⟩ := by
  simp only [closeFirstMetadataRun,List.length_cons,List.length_nil,ne_eq,not_true_eq_false,
    ↓reduceIte,List.takeWhile_cons,decide_true,List.takeWhile_nil,List.tail_cons,
    List.foldl_nil]

example : closeFirstMetadataRun (⟨broken.body,[2^250],broken.rotation⟩ : State Unit) [2^300]=
    hideHead ⟨broken.body,[2^250],broken.rotation⟩ := singleton_raw _ _ _ _

-- Huge key equality does not clock the number of fusions; the actual run tail does.
example (H : ℕ) : closeFirstMetadataRun (raw [9,4,2]) [H,H,H]=
    hideHead (fuseHead (fuseHead (raw [9,4,2]))) := by
  simp only [closeFirstMetadataRun, raw, List.length_cons, List.length_nil,
    ne_eq, not_true_eq_false, ↓reduceIte, List.takeWhile_cons, decide_true,
    List.takeWhile_nil, List.tail_cons, List.foldl_cons, List.foldl_nil]

-- Raw global relabeling changes scope names, but retains all indexed duplicate/nullary rows.
example : (closeFirstMetadataRun broken [1,1,2,2]).body.map (fun c => (c.rel,c.scope.length))=
    [((),0),((),2),((),2)] := by
  have h := (components_closeFirstMetadataRun broken [1,1,2,2]).2.2.1
  exact h

example : ¬∃ τ : ℕ → Bool, (closeFirstMetadataRun broken [1,1,2,2]).body.eval nearSem τ = true := by
  rintro ⟨τ,ht⟩
  have hr := (recover_closeFirstMetadataRun nearSem broken 1 [1,2,2] rfl τ ht).1
  change false=true at hr
  cases hr

example : broken.body.eval (fun _ _ => true) different=true := by rfl

example : ¬(closeFirstMetadataRun broken [1,1,2,2]).body.WellFormed (fun _ => 4) := by
  rw [wellFormed_closeFirstMetadataRun_iff]
  decide +kernel

example : ¬(sortAndCloseFirstMetadataRun g w broken keys).body.WellFormed (fun _ => 4) := by
  rw [wellFormed_sortAndCloseFirstMetadataRun_iff]
  decide +kernel

/-- Ordinary all-raw certificate client, without a finite relation alphabet premise. -/
theorem computableInPolyTime_anyRel {Rel : Type} {ar : Rel → ℕ}
    {sem : Rel → List Bool → Bool} (g : PPGadget ar sem cross) (w : GadgetWitness g)
    (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => sortAndCloseFirstMetadataRun g w p.1 p.2)
      (encStateMetadata encRel) (encState encRel) :=
  computableInPolyTime_sortAndCloseFirstMetadataRun g w encRel

example {Rel : Type} (encRel : Rel ↪ List Bool) (p : State Rel × List ℕ) :
    encStateMetadata encRel p=encPair (encState encRel) (encList encNat) p := rfl

example {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
    (g : PPGadget ar sem cross) (w : GadgetWitness g) (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime
      (fun p : State Rel × List ℕ => (sortAndCloseFirstMetadataRun g w p.1 p.2).ports)
      (encStateMetadata encRel) (encList encNat) :=
  encState_ports_polyTime encRel (computableInPolyTime_sortAndCloseFirstMetadataRun g w encRel)

-- Empty relation alphabets need neither a selected symbol nor a CROSS witness for grouping.
example : closeFirstMetadataRun (⟨[],[9,4],⟨[]⟩⟩ : State Empty) [1,1]=
    (⟨[],[],⟨[]⟩⟩ : State Empty) := by rfl

/-- The raw coalescer also has no static gadget or finite-alphabet premise. -/
theorem computableInPolyTime_raw_anyRel {Rel : Type} (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => closeFirstMetadataRun p.1 p.2)
      (encStateMetadata encRel) (encState encRel) :=
  computableInPolyTime_closeFirstMetadataRun encRel

end CslibFrontierTests.CSPMetadataGroup
