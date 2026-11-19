/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CrossTranspositionSchedule
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List.AdjacentTrace
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Sorting original metadata through the actual CROSS executor

`CrossInsertion.sortBoundaryMetadata` first checks alignment, computes a stable trace of
ORIGINAL metadata keys, and executes those exact requests. Actual State names are never
comparison keys. Equal keys retain distinct occurrences and may carry different values;
the later group-fusion compiler phase of [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091)
is not performed here.

The full checker, exact arity, universal old-name extension, direct one-output recovery,
and component recurrences follow from the public schedule contracts and the computed
trace. Native runtime is a fixed composition of two all-raw plain certificates, each with
its own internally proved growth bound. No sorting, routing or growth oracle is supplied.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Crossover
open OrderedBoundary Graph Cslib.BitString Turing.MultiTapeTM
open Cslib.AdjacentSortTrace

variable {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
variable (g : PPGadget ar sem cross) (w : GadgetWitness g)

/-- Guard metadata alignment BEFORE generation. Aligned input executes the actual stable
trace in order; mismatch preserves the entire raw State without tagging or normalization. -/
@[expose] def sortBoundaryMetadata (I : State Rel) (keys : List ℕ) : State Rel :=
  if keys.length=I.ports.length then transposeSchedule g w I (compute keys).requests else I

/-- Mismatched metadata is an exact raw identity, including malformed surplus tables. -/
theorem sortBoundaryMetadata_mismatch (I : State Rel) (keys : List ℕ)
    (h : keys.length ≠ I.ports.length) : sortBoundaryMetadata g w I keys = I := by
  simp only [sortBoundaryMetadata, ite_eq_right h]

/-- Sorted keys make no requests, so even a malformed State remains ENTIRELY unchanged.
This includes all-equal, empty and singleton metadata; no raw cycle is canceled. -/
theorem sortBoundaryMetadata_eq_self (I : State Rel) (keys : List ℕ)
    (h : keys.Pairwise (· ≤ ·)) : sortBoundaryMetadata g w I keys = I := by
  rw [sortBoundaryMetadata, requests_eq_nil_of_pairwise keys h]
  split <;> rfl

/-- Full target checker preservation is derived internally from the actual executed trace. -/
theorem accepted_sortBoundaryMetadata (I : State Rel) (keys : List ℕ) (h : I.Accepted) :
    (sortBoundaryMetadata g w I keys).Accepted := by
  unfold sortBoundaryMetadata
  split
  · exact accepted_transposeSchedule g w I _ h
  · exact h

/-- Exact arity is preserved on EVERY raw input, including mismatch and malformed scopes. -/
theorem wellFormed_sortBoundaryMetadata_iff (I : State Rel) (keys : List ℕ) :
    (sortBoundaryMetadata g w I keys).body.WellFormed ar ↔ I.body.WellFormed ar := by
  unfold sortBoundaryMetadata
  split
  · exact wellFormed_transposeSchedule_iff g w I _
  · rfl

private theorem requests_count (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) :
    (compute keys).requests.countP (fun j => decide (j+1<I.ports.length)) =
      (compute keys).requests.length := by
  apply List.countP_eq_length.mpr
  intro j hj
  simpa only [decide_eq_true_eq, ← hl] using (components_compute keys).2.2 j hj

private theorem value_replay (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) (σ : ℕ → Bool) :
    (compute keys).requests.foldl (fun ps j => ps.swap j (j+1)) (I.ports.map σ) =
      ((compute keys).requests.foldl (fun ps j => ps.swap j (j+1))
        (List.range keys.length)).map (fun i => (I.ports.map σ).getD i false) := by
  have hp := (indices_payload keys).2.1 (fun i => (I.ports.map σ).getD i false)
  have hinit : (List.range keys.length).map (fun i => (I.ports.map σ).getD i false) =
      I.ports.map σ := by
    rw [hl, ← List.length_map (f := σ)]
    exact List.map_getD_range _ false
  rw [hinit] at hp
  exact hp

/-- Exact rows, occurrences, port count and relation-symbol word after the computed trace.
`T` is the actual emitted length (at most `choose P 2`), and every request is valid. -/
theorem components_sortBoundaryMetadata (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) :
    let T := (compute keys).requests.length
    let K := sortBoundaryMetadata g w I keys
    K.body.length = I.body.length+T*g.body.length ∧
      K.body.occurrences.length = I.body.occurrences.length+T*g.body.occurrences.length ∧
      K.ports.length = I.ports.length ∧
      K.body.map Constraint.rel = I.body.map Constraint.rel ++
        (List.replicate T (g.body.map Constraint.rel)).flatten := by
  simpa only [sortBoundaryMetadata, ite_eq_left hl, requests_count I keys hl] using
    components_transposeSchedule g w I (compute keys).requests

/-- ONE satisfying output recovers source truth and the entire original-index-permuted
value word. Every original name, including unused names, is read at `2^T*z`. No checker,
arity, distinctness or semantic alignment premise besides the actual key/port length is
assumed. The index word is the literal computed replay, not a chosen permutation. -/
theorem recover_sortBoundaryMetadata (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) (τ : ℕ → Bool)
    (ht : (sortBoundaryMetadata g w I keys).body.eval sem τ = true) :
    let T := (compute keys).requests.length
    let ids := (compute keys).requests.foldl (fun ps j => ps.swap j (j+1))
      (List.range keys.length)
    I.body.eval sem (fun z => τ (2^T*z)) = true ∧
      (sortBoundaryMetadata g w I keys).ports.map τ =
        ids.map (fun i => (I.ports.map (fun z => τ (2^T*z))).getD i false) := by
  have hr := recover_transposeSchedule g w I (compute keys).requests τ
    (by simpa only [sortBoundaryMetadata, ite_eq_left hl] using ht)
  dsimp only at hr ⊢
  simp_rw [← List.swap_adjacent_eq_take_drop] at hr
  rw [requests_count I keys hl] at hr
  refine ⟨hr.1, ?_⟩
  rw [sortBoundaryMetadata, ite_eq_left hl]
  exact hr.2.trans (value_replay I keys hl _)

/-- Source truth iff a satisfying output extends EVERY old name and has the precise stable
value permutation. Distinct ports with equal metadata may keep different values. Zero
requests use the identity lift; mismatch instead has its separate whole-State identity. -/
theorem eval_sortBoundaryMetadata_iff (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) (σ : ℕ → Bool) :
    let T := (compute keys).requests.length
    let ids := (compute keys).requests.foldl (fun ps j => ps.swap j (j+1))
      (List.range keys.length)
    I.body.eval sem σ = true ↔ ∃ τ : ℕ → Bool,
      (sortBoundaryMetadata g w I keys).body.eval sem τ = true ∧
      (∀ z, τ (2^T*z)=σ z) ∧
      (sortBoundaryMetadata g w I keys).ports.map τ =
        ids.map (fun i => (I.ports.map σ).getD i false) := by
  dsimp only
  constructor
  · intro hs
    obtain ⟨τ, ht, ha, hv⟩ :=
      (eval_transposeSchedule_iff g w I (compute keys).requests σ).mp hs
    simp_rw [← List.swap_adjacent_eq_take_drop] at hv
    rw [requests_count I keys hl] at ha
    refine ⟨τ, ?_, ha, ?_⟩
    · simpa only [sortBoundaryMetadata, ite_eq_left hl] using ht
    · rw [sortBoundaryMetadata, ite_eq_left hl]
      exact hv.trans (value_replay I keys hl σ)
  · rintro ⟨τ, ht, ha, _⟩
    have hr := (recover_sortBoundaryMetadata g w I keys hl τ ht).1
    simpa only [show (fun z => τ (2^((compute keys).requests.length)*z))=σ
      from funext ha] using hr

/-- The length-guarded generator/executor composition is plain polynomial time on EVERY
raw State and binary metadata list, for any encoded target alphabet. The generator proves
its own prefix bound; the executor proves actual CROSS growth, including initial huge
malformed table entries and fixed template symbol payload. -/
theorem computableInPolyTime_sortBoundaryMetadata (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => sortBoundaryMetadata g w p.1 p.2)
      (encPair (encState encRel) (encList encNat)) (encState encRel) := by
  have hi := ComputableInPolyTime.fst (encState encRel) (encList encNat)
  have hk := ComputableInPolyTime.snd (encState encRel) (encList encNat)
  have hr := computableInPolyTime_compute.comp hk
  have hj : ComputableInPolyTime
      (fun p : State Rel × List ℕ => (compute p.2).requests)
      (encPair (encState encRel) (encList encNat)) (encList encNat) := by fun_prop
  have hex := (computableInPolyTime_transposeSchedule g w encRel).comp (hi.prod hj)
  have hg : ComputableInPolyTime
      (fun p : State Rel × List ℕ => decide (p.2.length=p.1.ports.length))
      (encPair (encState encRel) (encList encNat)) encBool := by
    have hkl := (ComputableInPolyTime.length_list encNat).comp hk
    have hpl := (ComputableInPolyTime.length_list encNat).comp (encState_ports_polyTime encRel hi)
    exact hkl.decide_eq' hpl
  exact ComputableInPolyTime.ite_decide hg hex hi

end Cslib.Complexity.CSP.CrossInsertion
