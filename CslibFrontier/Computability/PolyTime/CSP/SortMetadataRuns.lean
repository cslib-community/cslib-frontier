/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.SortMetadata
public import CslibFrontier.Computability.PolyTime.CSP.MetadataRuns
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Data.List.SortedCount
import Mathlib.Data.List.Pairwise

/-!
# Sorting once and closing every metadata group

One computed stable trace is executed once, then all actual sorted runs are closed. Recovery
composes the changing-name collapses AFTER the initial old-name lift; forwarding preserves
every lifted old name for a source assignment consistent at equal ORIGINAL metadata keys.
The table emitted at empty boundary checks the literal final body. Plain cost is fixed
composition with the independently bounded all-runs fold, not repeated polynomial growth.

This original step toward [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091)
does not assemble source atoms, reconstruct original-variable valuations from fresh
occurrences, validate source arity or prove native hardness/recognition.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph Turing.MultiTapeTM Cslib.BitString
open Cslib.AdjacentSortTrace

variable {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
variable (g : PPGadget ar sem cross) (w : GadgetWitness g)

/-- Guard alignment before generating ONE actual Result and executing its schedule ONCE.
Then close every consecutive run in that Result's sorted original metadata. Mismatch
retains the entire raw input, including malformed or surplus successor entries. -/
@[expose] def sortAndCloseMetadataRuns (I : State Rel) (keys : List ℕ) : State Rel :=
  if keys.length≠I.ports.length then I else
    let result := compute keys
    let J := transposeSchedule g w I result.requests
    closeMetadataRuns J result.sortedKeys

private theorem intermediate (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) :
    sortAndCloseMetadataRuns g w I keys = closeMetadataRuns (sortBoundaryMetadata g w I keys)
      (compute keys).sortedKeys := by
  simp only [sortAndCloseMetadataRuns,sortBoundaryMetadata,
    ite_eq_right (not_not.mpr hl),ite_eq_left hl]

/-- Mismatch and aligned empty metadata preserve the entire raw input. A positive number
of groups really executes hides, even if the stable sorter makes no requests. -/
theorem sortAndCloseMetadataRuns_eq_self (I : State Rel) (keys : List ℕ)
    (h : keys.length ≠ I.ports.length ∨ keys = []) : sortAndCloseMetadataRuns g w I keys = I := by
  rcases h with h | rfl
  · simp only [sortAndCloseMetadataRuns,ite_eq_left h]
  · unfold sortAndCloseMetadataRuns
    split
    · rfl
    · exact closeMetadataRuns_eq_self I [] (Or.inr rfl)

/-- Full checker preservation follows internally from the actual stable schedule and all
actual run closures, including closed and nullary components. -/
theorem accepted_sortAndCloseMetadataRuns (I : State Rel) (keys : List ℕ) (hI : I.Accepted) :
    (sortAndCloseMetadataRuns g w I keys).Accepted := by
  unfold sortAndCloseMetadataRuns
  split
  · exact hI
  · exact accepted_closeMetadataRuns _ _ (accepted_transposeSchedule g w I _ hI)

/-- Exact arity iff on EVERY raw input, independently of semantic truth. -/
theorem wellFormed_sortAndCloseMetadataRuns_iff (I : State Rel) (keys : List ℕ) :
    (sortAndCloseMetadataRuns g w I keys).body.WellFormed ar ↔ I.body.WellFormed ar := by
  by_cases hl : keys.length=I.ports.length
  · rw [intermediate g w I keys hl,wellFormed_closeMetadataRuns_iff,
      wellFormed_sortBoundaryMetadata_iff]
  · rw [sortAndCloseMetadataRuns_eq_self g w I keys (Or.inl hl)]

/-- Exact component growth is only the initial computed CROSS schedule: all closures
retain every indexed row/scope width and relation symbol. The final boundary is empty. -/
theorem components_sortAndCloseMetadataRuns (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) :
    let R := compute keys
    let J := sortBoundaryMetadata g w I keys
    let K := sortAndCloseMetadataRuns g w I keys
    K.body.length = I.body.length+R.requests.length*g.body.length ∧
      K.body.occurrences.length =
        I.body.occurrences.length+R.requests.length*g.body.occurrences.length ∧
      K.ports = [] ∧ K.body.map (fun c => (c.rel,c.scope.length)) = J.body.map (fun c =>
        (c.rel,c.scope.length)) ∧
      K.body.map Constraint.rel = I.body.map Constraint.rel++
        (List.replicate R.requests.length (g.body.map Constraint.rel)).flatten ∧
      (keys ≠ [] → K.rotation.successor.length = 2*K.body.occurrences.length ∧
        ∀ v ∈ K.rotation.successor, v < 2*K.body.occurrences.length) := by
  let J := sortBoundaryMetadata g w I keys
  have hs := components_sortBoundaryMetadata g w I keys hl
  have ha := sortedKeys_length_sortBoundaryMetadata g w I keys hl
  have hc := components_closeMetadataRuns J (compute keys).sortedKeys
  have hf := fields_closeMetadataRuns J (compute keys).sortedKeys ha
  rw [intermediate g w I keys hl]
  dsimp only at hs hc hf ⊢
  refine ⟨hc.1.trans hs.1,hc.2.1.trans hs.2.1,hf.2.1,hc.2.2.1,?_,?_⟩
  · have hr := congrArg (List.map Prod.fst) hc.2.2.1
    have he : (closeMetadataRuns J (compute keys).sortedKeys).body.map Constraint.rel=
        J.body.map Constraint.rel := by simpa only [List.map_map,Function.comp_def] using hr
    exact he.trans hs.2.2.2
  · intro hn
    have hsorted : (compute keys).sortedKeys≠[] := by
      intro he
      have hh := congrArg List.length (components_compute keys).1
      simp only [he,List.length_nil,List.length_insertionSort] at hh
      exact hn (List.length_eq_zero_iff.mp hh.symm)
    have ht := hf.2.2 hsorted
    constructor
    · exact ht.1.trans (congrArg (fun n => 2*n) hc.2.1.symm)
    · intro v hv
      exact (ht.2 v hv).trans_eq (congrArg (fun n => 2*n) hc.2.1.symm)

/-- All coalescing steps select post-sort names. The one scheduled linear bit-growth
bound therefore suffices for the full driver, including raw cross-group name repetitions. -/
theorem name_width_sortAndCloseMetadataRuns_le (I : State Rel) (keys : List ℕ) (W : ℕ)
    (hW : ∀ z ∈ I.body.vars ++ I.ports, z.size ≤ W) :
    ∀ z ∈ (sortAndCloseMetadataRuns g w I keys).body.vars++
      (sortAndCloseMetadataRuns g w I keys).ports,
      z.size ≤ max W (2*g.numAux+7).size+(compute keys).requests.length := by
  unfold sortAndCloseMetadataRuns
  split
  · exact fun z hz => (hW z hz).trans (by omega)
  · intro z hz
    apply (name_width_transposeSchedule_le g w I (compute keys).requests W hW z
      (names_closeMetadataRuns_subset _ _ hz)).trans
    exact Nat.add_le_add_left List.countP_le_length _

/-- The actual final successor table, without an additional normalization or choice,
passes the full body checker whenever the aligned source is accepted. -/
theorem body_accepted_sortAndCloseMetadataRuns (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) (hI : I.Accepted) :
    verifyRotationCertificate (sortAndCloseMetadataRuns g w I keys).body
      (sortAndCloseMetadataRuns g w I keys).rotation = true := by
  rw [intermediate g w I keys hl]
  exact body_accepted_closeMetadataRuns _ _ (sortedKeys_length_sortBoundaryMetadata g w I keys hl)
    (accepted_sortBoundaryMetadata g w I keys hI)

private theorem index_keys (keys : List ℕ) :
    let ids := (compute keys).requests.foldl (fun ps j => ps.swap j (j + 1)) (List.range
      keys.length)
    ids.map (fun i => keys.getD i 0) = (compute keys).sortedKeys := by
  have hp := (indices_payload keys).2.1 (fun i => keys.getD i 0)
  rw [List.map_getD_range] at hp
  have hr := replay_compute id keys
  simp only [List.map_id] at hr
  exact hp.symm.trans (hr.trans (components_compute keys).1.symm)

private theorem equal_key_values (xs : List (ℕ × Bool))
    (hs : xs.Pairwise (fun a b => a.1 ≤ b.1))
    (hc : xs.IsChain (fun a b => a.1 = b.1 → a.2 = b.2))
    (x y : ℕ × Bool) (hx : x ∈ xs) (hy : y ∈ xs) (he : x.1 = y.1) : x.2 = y.2 := by
  let block := xs.filter (fun q => q.1=x.1)
  have hb := List.Pairwise.filter_key_eq Prod.fst x.1 hs
  have hchain : block.IsChain (fun a b => a.1=b.1 → a.2=b.2) := by
    rw [show block=xs.filter (fun q => q.1=x.1) from rfl,hb]
    exact (hc.drop _).take _
  have hall : ∀ q∈block, q.1=x.1 := by
    intro q hq
    exact of_decide_eq_true (List.mem_filter.mp hq).2
  have hvalues : (block.map Prod.snd).IsChain (· = ·) := by
    apply (List.isChain_map Prod.snd).mpr
    exact hchain.imp_of_mem_imp (fun a b ha hb hab => hab ((hall a ha).trans (hall b hb).symm))
  have hxm : x.2∈block.map Prod.snd := List.mem_map.mpr ⟨x,by simp [block,hx],rfl⟩
  have hym : y.2∈block.map Prod.snd := List.mem_map.mpr ⟨y,by simp [block,hy,he],rfl⟩
  cases hv : block.map Prod.snd with
  | nil => simp only [hv,List.not_mem_nil] at hxm
  | cons a vs =>
    have hvchain : (a::vs).IsChain (· = ·) := by rwa [hv] at hvalues
    have hconst : ∀ v∈a::vs, v=a := by
      intro v hm
      rcases List.mem_cons.mp hm with rfl | hm
      · rfl
      · exact (hvchain.rel_cons hm).symm
    exact (hconst _ (hv ▸ hxm)).trans (hconst _ (hv ▸ hym)).symm

private theorem paired_word (I : State Rel) (keys : List ℕ) (σ ν : ℕ → Bool)
    (hword : (sortBoundaryMetadata g w I keys).ports.map ν = ((compute keys).requests.foldl (fun
      ps j => ps.swap j (j + 1)) (List.range keys.length)).map
        (fun i => (I.ports.map σ).getD i false)) :
    (compute keys).sortedKeys.zip ((sortBoundaryMetadata g w I keys).ports.map ν) = ((compute
      keys).requests.foldl (fun ps j => ps.swap j (j + 1)) (List.range keys.length)).map
        (fun i => (keys.getD i 0,(I.ports.map σ).getD i false)) := by
  rw [← index_keys keys,hword,List.zip_map']

/-- ONE satisfying final assignment directly recovers source truth, the exact sorted
original-index value word, and agreement at ANY original positions with equal metadata.
The recovery is collapse AFTER `2^T` tagging, including on unused original names. -/
theorem recover_sortAndCloseMetadataRuns (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) (τ : ℕ → Bool)
    (ht : (sortAndCloseMetadataRuns g w I keys).body.eval sem τ = true) :
    let R := compute keys
    let J := sortBoundaryMetadata g w I keys
    let sorted := R.sortedKeys
    let states := fun s => (fun K : State Rel => closeFirstMetadataRun K
      (sorted.drop (sorted.length-K.ports.length)))^[s] J
    let Phi := (List.range sorted.length).foldl (fun f s => fun z =>
      if f z ∈ (states s).ports.take
          ((sorted.drop (sorted.length-(states s).ports.length)).takeWhile
            (fun b => decide (b = (sorted.drop (sorted.length-(states s).ports.length)).headD
              0))).length
      then (states s).ports.headD 0 else f z) id
    let ρ := fun z => τ (Phi (2^R.requests.length*z))
    let ids := R.requests.foldl (fun ps j => ps.swap j (j + 1)) (List.range keys.length)
    I.body.eval sem ρ = true ∧ J.ports.map (τ ∘ Phi) = ids.map (fun i => (I.ports.map ρ).getD i
      false) ∧
      ∀ i j, i < keys.length → j < keys.length → keys.getD i 0 = keys.getD j 0 →
        (I.ports.map ρ).getD i false = (I.ports.map ρ).getD j false := by
  let R := compute keys
  let J := sortBoundaryMetadata g w I keys
  let sorted := R.sortedKeys
  let states := fun s => (fun K : State Rel => closeFirstMetadataRun K
    (sorted.drop (sorted.length-K.ports.length)))^[s] J
  let Phi := (List.range sorted.length).foldl (fun f s => fun z =>
    if f z ∈ (states s).ports.take
        ((sorted.drop (sorted.length-(states s).ports.length)).takeWhile
          (fun b => decide (b=(sorted.drop (sorted.length-(states s).ports.length)).headD
            0))).length
    then (states s).ports.headD 0 else f z) id
  let ρ := fun z => τ (Phi (2^R.requests.length*z))
  let ids := R.requests.foldl (fun ps j => ps.swap j (j + 1)) (List.range keys.length)
  have ha := sortedKeys_length_sortBoundaryMetadata g w I keys hl
  have hlow := recover_closeMetadataRuns sem J sorted ha τ (by
    rw [← intermediate g w I keys hl]
    exact ht)
  change J.body.eval sem (τ ∘ Phi)=true ∧
    (sorted.zip (J.ports.map (τ ∘ Phi))).IsChain (fun a b => a.1=b.1 → a.2=b.2) at hlow
  have hs := recover_sortBoundaryMetadata g w I keys hl (τ ∘ Phi) hlow.1
  change I.body.eval sem ρ=true ∧ J.ports.map (τ ∘ Phi)=
    ids.map (fun i => (I.ports.map ρ).getD i false) at hs
  change I.body.eval sem ρ=true ∧ J.ports.map (τ ∘ Phi)=_ ∧ _
  refine ⟨hs.1,hs.2,?_⟩
  let pairs := sorted.zip (J.ports.map (τ ∘ Phi))
  have hpairs := paired_word g w I keys ρ (τ ∘ Phi) hs.2
  change pairs=ids.map (fun i => (keys.getD i 0,(I.ports.map ρ).getD i false)) at hpairs
  have hsort : sorted.Pairwise (· ≤ ·) := by
    change (compute keys).sortedKeys.Pairwise (· ≤ ·)
    rw [(components_compute keys).1]
    exact List.pairwise_insertionSort _ _
  have hproj : pairs.map Prod.fst=sorted :=
    List.map_fst_zip (by simpa only [List.length_map] using ha.le)
  have horder : pairs.Pairwise (fun a b => a.1≤b.1) := by
    have hh : (pairs.map Prod.fst).Pairwise (· ≤ ·) := by rwa [hproj]
    simpa only [List.pairwise_map] using hh
  intro i j hi hj he
  have hperm : ids.Perm (List.range keys.length) := (indices_payload.{0} keys).1
  have hmi : i∈ids := hperm.mem_iff.mpr (List.mem_range.mpr hi)
  have hmj : j∈ids := hperm.mem_iff.mpr (List.mem_range.mpr hj)
  apply equal_key_values pairs horder hlow.2
    (keys.getD i 0,(I.ports.map ρ).getD i false)
    (keys.getD j 0,(I.ports.map ρ).getD j false)
  · rw [hpairs]; exact List.mem_map.mpr ⟨i,hmi,rfl⟩
  · rw [hpairs]; exact List.mem_map.mpr ⟨j,hmj,rfl⟩
  · exact he

/-- A satisfying source assignment consistent at equal ORIGINAL metadata keys extends on
EVERY `2^T*z`, including unused names. The same actual sorter assignment forwards through
all run closures; no equality is inferred from arbitrary eliminated output labels. -/
theorem forward_sortAndCloseMetadataRuns (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) (σ : ℕ → Bool) (hs : I.body.eval sem σ = true)
    (he : ∀ i j, i < keys.length → j < keys.length → keys.getD i 0 = keys.getD j 0 →
      (I.ports.map σ).getD i false = (I.ports.map σ).getD j false) :
    ∃ τ : ℕ → Bool, (sortAndCloseMetadataRuns g w I keys).body.eval sem τ = true ∧
      ∀ z, τ (2^(compute keys).requests.length*z) = σ z := by
  obtain ⟨ν,hν,hagree,hword⟩ := (eval_sortBoundaryMetadata_iff g w I keys hl σ).mp hs
  let ids := (compute keys).requests.foldl (fun ps j => ps.swap j (j + 1)) (List.range keys.length)
  let J := sortBoundaryMetadata g w I keys
  have hpairs := paired_word g w I keys σ ν hword
  have hperm : ids.Perm (List.range keys.length) := (indices_payload.{0} keys).1
  have hchain : ((compute keys).sortedKeys.zip (J.ports.map ν)).IsChain
      (fun a b => a.1=b.1 → a.2=b.2) := by
    rw [hpairs]
    apply List.isChain_iff_getElem.mpr
    intro s hs'
    have hsids : s+1 < ids.length := by simpa only [List.length_map] using hs'
    have hi : ids[s] < keys.length := List.mem_range.mp
      (hperm.mem_iff.mp (List.getElem_mem _))
    have hj : ids[s+1] < keys.length := List.mem_range.mp
      (hperm.mem_iff.mp (List.getElem_mem _))
    simpa only [List.getElem_map] using he ids[s] ids[s+1] hi hj
  have ht := forward_closeMetadataRuns sem J (compute keys).sortedKeys
    (sortedKeys_length_sortBoundaryMetadata g w I keys hl) ν hν hchain
  refine ⟨ν,?_,hagree⟩
  rwa [intermediate g w I keys hl]

/-- Plain polynomial time on EVERY raw State/key pair, for arbitrary encoded Rel. ONE
Result supplies both projections; its literal schedule and the independently bounded
all-runs driver are composed a fixed number of times. No arity, validity, size, entry,
finite-language or runtime-growth premise is input. -/
theorem computableInPolyTime_sortAndCloseMetadataRuns (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => sortAndCloseMetadataRuns g w p.1 p.2)
      (encStateMetadata encRel) (encState encRel) := by
  have hi := ComputableInPolyTime.fst (encState encRel) (encList encNat)
  have hk := ComputableInPolyTime.snd (encState encRel) (encList encNat)
  have hstored := hi.prod (computableInPolyTime_compute.comp hk)
  have hI := ComputableInPolyTime.fst (encState encRel) encResult
  have hR := ComputableInPolyTime.snd (encState encRel) encResult
  have hscheduled := (computableInPolyTime_transposeSchedule g w encRel).comp
    (hI.prod (encResult_requests_polyTime hR))
  have hclose := (computableInPolyTime_closeMetadataRuns encRel).comp
    (hscheduled.prod (encResult_sortedKeys_polyTime hR))
  have hbad : ComputableInPolyTime
      (fun p : State Rel × List ℕ => decide (p.2.length≠p.1.ports.length))
      (encStateMetadata encRel) encBool := by fun_prop
  apply (ComputableInPolyTime.ite_decide hbad hi (hclose.comp hstored)).of_enc_eq
  intro p
  rfl

end Cslib.Complexity.CSP.CrossInsertion
