/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.CSP.SortMetadata
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Crossover
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary

/-!
# Ordinary clients of the computed stable metadata trace

Production atom tables and Figure 1(b) are used directly. Metadata keys are independent
of actual variable names. Equal metadata retains distinct payloads until group fusion;
repeated actual names already impose equality. Identity tests retain entire malformed
States, and recovery tests refer to one satisfying output and every original name.
-/

public section

namespace CslibFrontierTests.CSPMetadataSort

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open Cslib.Complexity Cslib.Complexity.CSP OrderedBoundary CrossInsertion
open Cslib.AdjacentSortTrace Turing.MultiTapeTM Cslib.BitString List

example : (compute [3,2,1]).requests = [1,0,1] ∧
    (compute [3,2,1]).sortedKeys = [1,2,3] ∧
    (compute [3,2,1]).requests.foldl (fun xs j => xs.swap j (j+1)) [0,1,2] = [2,1,0] := by
  simp [compute, Cslib.AdjacentSortTrace.insert, List.range_succ, List.swap]

example : (compute [2,1,2,1]).requests = [2,0,1] ∧
    (compute [2,1,2,1]).sortedKeys = [1,1,2,2] ∧
    (compute [2,1,2,1]).requests.foldl (fun xs j => xs.swap j (j+1)) [0,1,2,3] =
      [1,3,0,2] := by simp [compute, Cslib.AdjacentSortTrace.insert, List.range_succ, List.swap]

example {α : Type} (a b c d : α) :
    (compute [2,1,2,1]).requests.foldl (fun xs j => xs.swap j (j+1)) [a,b,c,d] =
      [b,d,a,c] := by simp [compute, Cslib.AdjacentSortTrace.insert, List.range_succ, List.swap]

example : [1,3] <+ (compute [2,1,2,1]).requests.foldl
    (fun xs j => xs.swap j (j+1)) [0,1,2,3] :=
  (indices_payload.{0} [2,1,2,1]).2.2 1 3 (by decide +kernel) (by rfl)

-- The generic replay theorem compares only original keys, even on decorated payloads.
example (a b : Bool) :
    (compute [2,1,2,1]).requests.foldl (fun xs j => xs.swap j (j+1))
      [(2,false),(1,a),(2,true),(1,b)] = [(1,a),(1,b),(2,false),(2,true)] := by
  have h := replay_compute (fun p : ℕ × Bool => p.1)
    [(2,false),(1,a),(2,true),(1,b)]
  simpa [List.insertionSort_cons, List.insertionSort_nil] using h

private abbrev g := figureOneB
private abbrev w := figureOneBBoundary
private def keys : List ℕ := [2,1,2,1]

private theorem computed_keys : compute keys = ⟨[1,1,2,2],[2,0,1]⟩ := by
  simp [keys, compute, Cslib.AdjacentSortTrace.insert, List.range_succ]

-- Only this small State wrapper is new; the actual certificate and gadget are production APIs.
private def atom : State Unit :=
  ⟨[⟨(),[10,20,30,40]⟩], [10,20,30,40], atomBoundaryCertificate 4⟩
private def sigma (z : ℕ) : Bool := decide (z=20 ∨ z=40)

example : (sortBoundaryMetadata g w atom keys).Accepted :=
  accepted_sortBoundaryMetadata g w atom keys (by decide +kernel)

example : OrderedBoundary.verify (sortBoundaryMetadata g w atom keys).body
    (sortBoundaryMetadata g w atom keys).ports (sortBoundaryMetadata g w atom keys).rotation =
      true := (accepted_sortBoundaryMetadata g w atom keys (by decide +kernel)).2

-- Literal emitted names differ from the sorted original metadata and its value permutation.
example : (sortBoundaryMetadata g w atom keys).ports = [10,5,7,28] := by
  rw [sortBoundaryMetadata, computed_keys]
  decide +kernel

example : (sortBoundaryMetadata g w atom keys).body.length = 7 ∧
    (sortBoundaryMetadata g w atom keys).body.occurrences.length = 28 ∧
    (sortBoundaryMetadata g w atom keys).ports.length = 4 := by
  have h := components_sortBoundaryMetadata g w atom keys rfl
  have hc := And.intro h.1 (And.intro h.2.1 h.2.2.1)
  simp only [computed_keys] at hc
  simpa [atom, g, figureOneB, figureOneBBody, CSP.length_occurrences] using hc

example : (sortBoundaryMetadata g w atom keys).rotation.successor.length = 64 := by
  rw [sortBoundaryMetadata, computed_keys]
  decide +kernel

example : ∃ τ : ℕ → Bool, (sortBoundaryMetadata g w atom keys).body.eval nearSem τ = true ∧
    (∀ z, τ (8*z)=sigma z) ∧ τ (8*123456)=false ∧
    (sortBoundaryMetadata g w atom keys).ports.map τ = [true,true,false,false] := by
  obtain ⟨τ,ht,he,hv⟩ :=
    (eval_sortBoundaryMetadata_iff g w atom keys rfl sigma).mp (by decide +kernel)
  simp only [computed_keys] at he hv
  change ∀ z, τ (8*z)=sigma z at he
  change _ = [sigma 20,sigma 40,sigma 10,sigma 30] at hv
  exact ⟨τ,ht,he,by simpa [sigma] using he 123456,by simpa [sigma] using hv⟩

example (τ : ℕ → Bool) (ht : (sortBoundaryMetadata g w atom keys).body.eval nearSem τ = true) :
    atom.body.eval nearSem (fun z => τ (8*z)) = true ∧
      (sortBoundaryMetadata g w atom keys).ports.map τ =
        [τ (8*20),τ (8*40),τ (8*10),τ (8*30)] := by
  have hr := recover_sortBoundaryMetadata g w atom keys rfl τ ht
  simp only [computed_keys] at hr
  exact hr

-- A different noncommuting order is impossible under the SAME original-name extension.
example : ¬∃ τ : ℕ → Bool, (sortBoundaryMetadata g w atom keys).body.eval nearSem τ = true ∧
    (∀ z, τ (8*z)=sigma z) ∧
    (sortBoundaryMetadata g w atom keys).ports.map τ = [true,false,true,false] := by
  rintro ⟨τ,ht,he,hv⟩
  have h := (recover_sortBoundaryMetadata g w atom keys rfl τ ht).2
  simp only [computed_keys] at h
  change _ = [τ (8*20),τ (8*40),τ (8*10),τ (8*30)] at h
  simp only [he] at h
  rw [hv] at h
  simp [sigma] at h

-- Equal metadata does not identify distinct payload variables before the later fusion phase.
private def independent : State Unit := ⟨[],[10,20,30,40],⟨[]⟩⟩
example : ∃ τ : ℕ → Bool,
    (sortBoundaryMetadata g w independent keys).body.eval nearSem τ = true ∧
    (∀ z, τ (8*z)=decide (z=20)) ∧
    (sortBoundaryMetadata g w independent keys).ports.map τ = [true,false,false,false] := by
  obtain ⟨τ,ht,he,hv⟩ :=
    (eval_sortBoundaryMetadata_iff g w independent keys rfl (fun z => decide (z=20))).mp rfl
  simp only [computed_keys] at he hv
  exact ⟨τ,ht,he,hv.trans (by decide +kernel)⟩

private def repeated : State Unit := ⟨[],[2^250,17,17,2^250],⟨[2^300]⟩⟩
example : ¬∃ τ : ℕ → Bool,
    (sortBoundaryMetadata g w repeated keys).body.eval nearSem τ = true ∧
    (sortBoundaryMetadata g w repeated keys).ports.map τ = [false,false,true,true] := by
  rintro ⟨τ,ht,hv⟩
  have hr := (recover_sortBoundaryMetadata g w repeated keys rfl τ ht).2
  simp only [computed_keys] at hr
  change _ = [τ (8*17),τ (8*(2^250)),τ (8*(2^250)),τ (8*17)] at hr
  rw [hv] at hr
  simp only [List.cons.injEq, and_true] at hr
  have hbad : true = false := hr.2.2.1.trans hr.2.1.symm
  cases hbad

-- Distinct metadata with huge binary keys has the same bounded trace, not a huge clock.
private theorem requests_large (H : ℕ) (h : 7 < H) :
    (compute [H,7,H,7]).requests = [2,0,1] := by
  simp [compute, Cslib.AdjacentSortTrace.insert, List.range_succ, h, Nat.not_le.mpr h]

example : (compute [2^300,7,2^300,7]).requests = [2,0,1] :=
  requests_large _ (by decide +kernel)

private def broken : State Unit :=
  ⟨[⟨(),[]⟩,⟨(),[17,17]⟩,⟨(),[17,17]⟩], [2^250,17,17,2^250], ⟨[2^300,9,9]⟩⟩

-- Original names are numerically unsorted; sorted metadata still leaves EVERY byte alone.
example : sortBoundaryMetadata g w broken [0,1,2,3] = broken :=
  sortBoundaryMetadata_eq_self g w broken _ (by decide +kernel)

example (H : ℕ) : sortBoundaryMetadata g w broken [H,H,H,H] = broken :=
  sortBoundaryMetadata_eq_self g w broken _ (by
    change (List.replicate 4 _).Pairwise (· ≤ ·)
    exact List.pairwise_replicate.mpr (Or.inr (le_refl _)))

example : sortBoundaryMetadata g w broken [2^300,2^300,2^300,2^300] = broken :=
  sortBoundaryMetadata_eq_self g w broken _ (by
    change (List.replicate 4 _).Pairwise (· ≤ ·)
    exact List.pairwise_replicate.mpr (Or.inr (le_refl _)))

-- Mismatch is checked before trace generation, even on unsorted metadata.
example : sortBoundaryMetadata g w broken [3,2,1] = broken :=
  sortBoundaryMetadata_mismatch g w broken _ (by decide +kernel)

example : sortBoundaryMetadata g w (⟨broken.body,[],broken.rotation⟩ : State Unit) [1,0] =
    ⟨broken.body,[],broken.rotation⟩ :=
  sortBoundaryMetadata_mismatch g w _ _ (by decide +kernel)

example : sortBoundaryMetadata g w (⟨broken.body,[],broken.rotation⟩ : State Unit) [] =
    ⟨broken.body,[],broken.rotation⟩ :=
  sortBoundaryMetadata_eq_self g w _ _ (by constructor)

example : sortBoundaryMetadata g w (⟨broken.body,[17],broken.rotation⟩ : State Unit) [2^300] =
    ⟨broken.body,[17],broken.rotation⟩ :=
  sortBoundaryMetadata_eq_self g w _ _ (by simp only [List.pairwise_singleton])

-- Duplicate indexed rows and closed false/nullary constraints survive in the old prefix.
example : ((sortBoundaryMetadata g w broken keys).body.take 3).map Constraint.scope =
    [[],[136,136],[136,136]] := by
  rw [sortBoundaryMetadata, computed_keys]
  decide +kernel

example : ¬∃ τ : ℕ → Bool, (sortBoundaryMetadata g w broken keys).body.eval nearSem τ = true := by
  rintro ⟨τ,ht⟩
  have hr := (recover_sortBoundaryMetadata g w broken keys rfl τ ht).1
  change false=true at hr
  cases hr

-- Arity checking is syntactic, even when a supplied raw semantics returns true on [] and
-- other wrong-width words. The executor does not silently deduplicate the duplicate rows.
example : broken.body.eval (fun _ _ => true) (fun _ => false) = true := by rfl

example : ¬(sortBoundaryMetadata g w broken keys).body.WellFormed (fun _ => 4) := by
  rw [wellFormed_sortBoundaryMetadata_iff]
  decide +kernel

example (I : State Unit) (ks : List ℕ) :
    (sortBoundaryMetadata g w I ks).body.WellFormed (fun _ => 4) ↔
      I.body.WellFormed (fun _ => 4) := wellFormed_sortBoundaryMetadata_iff g w I ks

-- Encoding layout and generated projection certificates are used through ordinary imports.
example (r : Result) : encResult r =
    encPair (encList encNat) (encList encNat) (r.sortedKeys,r.requests) := by rfl

example : ComputableInPolyTime Result.sortedKeys encResult (encList encNat) := by fun_prop

/-- The guarded metadata caller admits arbitrary encoded relation alphabets. -/
theorem computableInPolyTime_anyRel {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
    (g : PPGadget ar sem cross) (w : GadgetWitness g) (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => sortBoundaryMetadata g w p.1 p.2)
      (encPair (encState encRel) (encList encNat)) (encState encRel) :=
  computableInPolyTime_sortBoundaryMetadata g w encRel

example {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
    (g : PPGadget ar sem cross) (w : GadgetWitness g) (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime
      (fun p : State Rel × List ℕ => (sortBoundaryMetadata g w p.1 p.2).ports)
      (encPair (encState encRel) (encList encNat)) (encList encNat) :=
  encState_ports_polyTime encRel (computableInPolyTime_sortBoundaryMetadata g w encRel)

end CslibFrontierTests.CSPMetadataSort
