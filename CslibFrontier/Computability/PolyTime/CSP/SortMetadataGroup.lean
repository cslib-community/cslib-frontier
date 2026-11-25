/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.SortMetadata
public import CslibFrontier.Computability.PolyTime.CSP.BoundaryGroup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Sorting and closing the first actual metadata group

One computed Result supplies both the literal schedule and its stable metadata word. Only
its first run is closed. Recovery composes the actual collapse AFTER old-name doubling;
forward extension preserves every doubled old name when the selected source values agree.
This original composition does not assemble atoms or drive all groups; those compiler and
recognition obligations remain tracked by [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph Turing.MultiTapeTM Cslib.BitString
open Cslib.AdjacentSortTrace

variable {Rel : Type} {ar : Rel → ℕ} {sem : Rel → List Bool → Bool}
variable (g : PPGadget ar sem cross) (w : GadgetWitness g)

/-- Guard alignment BEFORE generating one Result. Its actual requests are executed, then
its actual sorted word determines the first run. No second generator/router is substituted. -/
@[expose] def sortAndCloseFirstMetadataRun (I : State Rel) (keys : List ℕ) : State Rel :=
  if keys.length≠I.ports.length then I else
    let result := compute keys
    let J := transposeSchedule g w I result.requests
    closeFirstMetadataRun J result.sortedKeys

private theorem intermediate (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) :
    sortAndCloseFirstMetadataRun g w I keys=
      closeFirstMetadataRun (sortBoundaryMetadata g w I keys) (compute keys).sortedKeys := by
  simp only [sortAndCloseFirstMetadataRun, sortBoundaryMetadata,
    ite_eq_right (not_not.mpr hl), ite_eq_left hl]

/-- Mismatch and the zero-port empty case retain the entire original raw State. -/
theorem sortAndCloseFirstMetadataRun_eq_self (I : State Rel) (keys : List ℕ)
    (h : keys.length ≠ I.ports.length ∨ keys = []) :
    sortAndCloseFirstMetadataRun g w I keys = I := by
  rcases h with h | rfl
  · simp only [sortAndCloseFirstMetadataRun, ite_eq_left h]
  · unfold sortAndCloseFirstMetadataRun
    split
    · rfl
    · exact closeFirstMetadataRun_eq_self I [] (Or.inr rfl)

/-- Complete checker preservation is supplied internally by the actual sorter and every
actual fusion/hide, never by a target-acceptance provider. -/
theorem accepted_sortAndCloseFirstMetadataRun (I : State Rel) (keys : List ℕ)
    (hI : I.Accepted) : (sortAndCloseFirstMetadataRun g w I keys).Accepted := by
  by_cases hl : keys.length = I.ports.length
  · rw [intermediate g w I keys hl]
    exact accepted_closeFirstMetadataRun _ _ (accepted_sortBoundaryMetadata g w I keys hI)
  · rwa [sortAndCloseFirstMetadataRun_eq_self g w I keys (Or.inl hl)]

/-- Exact source arity is equivalent on EVERY raw input, without a semantic-width guard. -/
theorem wellFormed_sortAndCloseFirstMetadataRun_iff (I : State Rel) (keys : List ℕ) :
    (sortAndCloseFirstMetadataRun g w I keys).body.WellFormed ar ↔ I.body.WellFormed ar := by
  by_cases hl : keys.length = I.ports.length
  · rw [intermediate g w I keys hl,wellFormed_closeFirstMetadataRun_iff,
      wellFormed_sortBoundaryMetadata_iff]
  · rw [sortAndCloseFirstMetadataRun_eq_self g w I keys (Or.inl hl)]

/-- Closing adds no rows or occurrences and removes the actual first sorted run. Original
relation symbols and all gadget row words remain in their indexed order. -/
theorem components_sortAndCloseFirstMetadataRun (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) :
    let R := compute keys
    let r := (R.sortedKeys.takeWhile (fun b => decide (b = R.sortedKeys.headD 0))).length
    let K := sortAndCloseFirstMetadataRun g w I keys
    K.body.length = I.body.length+R.requests.length*g.body.length ∧
      K.body.occurrences.length = I.body.occurrences.length+
        R.requests.length*g.body.occurrences.length ∧
      K.ports.length = I.ports.length-r ∧
      K.body.map Constraint.rel = I.body.map Constraint.rel++
        (List.replicate R.requests.length (g.body.map Constraint.rel)).flatten := by
  have hs := components_sortBoundaryMetadata g w I keys hl
  have hg := components_closeFirstMetadataRun (sortBoundaryMetadata g w I keys)
    (compute keys).sortedKeys
  dsimp only at hs hg ⊢
  rw [intermediate g w I keys hl]
  simp only [sortedKeys_length_sortBoundaryMetadata g w I keys hl, ↓reduceIte] at hg
  refine ⟨hg.1.trans hs.1, hg.2.1.trans hs.2.1, by rw [hg.2.2.2, hs.2.2.1], ?_⟩
  refine (?_ : _ = (sortBoundaryMetadata g w I keys).body.map Constraint.rel).trans hs.2.2.2
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) hg.2.2.1

/-- The actual coalescer selects existing names, so scheduled linear bit growth is not
iterated through an arbitrary polynomial output bound. This is the real caller of the
shared schedule width theorem. -/
theorem name_width_sortAndCloseFirstMetadataRun_le (I : State Rel) (keys : List ℕ) (W : ℕ)
    (hW : ∀ z ∈ I.body.vars ++ I.ports, z.size ≤ W) :
    ∀ z ∈ (sortAndCloseFirstMetadataRun g w I keys).body.vars++
      (sortAndCloseFirstMetadataRun g w I keys).ports,
      z.size ≤ max W (2*g.numAux+7).size+(compute keys).requests.length := by
  by_cases hl : keys.length = I.ports.length
  · rw [intermediate g w I keys hl]
    intro z hz
    refine (name_width_transposeSchedule_le g w I (compute keys).requests W hW z ?_).trans
      (Nat.add_le_add_left List.countP_le_length _)
    simpa only [sortBoundaryMetadata, ite_eq_left hl] using
      names_closeFirstMetadataRun_subset (sortBoundaryMetadata g w I keys)
        (compute keys).sortedKeys hz
  · rw [sortAndCloseFirstMetadataRun_eq_self g w I keys (Or.inl hl)]
    exact fun z hz => (hW z hz).trans (by omega)

private theorem sorted_cons (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) (hne : keys ≠ []) :
    ∃ a ks, (compute keys).sortedKeys = a::ks ∧
      (a::ks).length = (sortBoundaryMetadata g w I keys).ports.length := by
  have hal := sortedKeys_length_sortBoundaryMetadata g w I keys hl
  cases hks : (compute keys).sortedKeys with
  | nil =>
    refine (hne (List.length_eq_zero_iff.mp ?_)).elim
    simpa only [hks, List.length_nil, List.length_insertionSort] using
      (congrArg List.length (components_compute keys).1).symm
  | cons a ks => exact ⟨a, ks, rfl, by simpa only [hks] using hal⟩

/-- ONE final assignment recovers the source through collapse AFTER doubling, forces the
selected sorted values to agree, and determines the whole remaining ordered value word.
There is no source checker, arity, distinctness or output-consistency premise. -/
theorem recover_sortAndCloseFirstMetadataRun (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) (hne : keys ≠ []) (τ : ℕ → Bool)
    (ht : (sortAndCloseFirstMetadataRun g w I keys).body.eval sem τ = true) :
    let R := compute keys
    let J := sortBoundaryMetadata g w I keys
    let r := (R.sortedKeys.takeWhile (fun b => decide (b = R.sortedKeys.headD 0))).length
    let C := fun z => if z ∈ J.ports.take r then J.ports.headD 0 else z
    let ids := R.requests.foldl (fun ps j => ps.swap j (j + 1)) (List.range keys.length)
    let σ := fun z => τ (C (2^R.requests.length*z))
    I.body.eval sem σ = true ∧
      (∀ b ∈ (ids.take r).map (fun i => (I.ports.map σ).getD i false), b = τ (J.ports.headD 0)) ∧
      (sortAndCloseFirstMetadataRun g w I keys).ports.map τ=
        (ids.drop r).map (fun i => (I.ports.map σ).getD i false) := by
  let J := sortBoundaryMetadata g w I keys
  obtain ⟨a, ks, hks, ha⟩ := sorted_cons g w I keys hl hne
  let r := ((a :: ks).takeWhile (fun b => decide (b = a))).length
  let C := fun z => if z ∈ J.ports.take r then J.ports.headD 0 else z
  have hg := recover_closeFirstMetadataRun sem J a ks ha τ
    (by simpa only [intermediate g w I keys hl, hks] using ht)
  change J.body.eval sem (τ ∘ C) = true ∧ _ at hg
  have hs := recover_sortBoundaryMetadata g w I keys hl (τ ∘ C) hg.1
  dsimp only [Function.comp_def] at hs ⊢
  simp only [hks, List.headD_cons]
  refine ⟨hs.1, fun b hb => ?_, ?_⟩
  · rw [List.map_take, ← congrArg (List.take r) hs.2, ← List.map_take] at hb
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hb
    exact hg.2.1 z hz
  · rw [intermediate g w I keys hl, hks, List.map_drop]
    exact hg.2.2.trans (List.map_drop.trans (congrArg (List.drop r) hs.2))

/-- A source assignment consistent on the selected sorted value run extends on EVERY
`2^T` old name, including unused names. The same sorter assignment forwards through the
coalescer; no equality is inferred from arbitrary eliminated output-name values. -/
theorem forward_sortAndCloseFirstMetadataRun (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) (hne : keys ≠ []) (σ : ℕ → Bool)
    (hs : I.body.eval sem σ = true)
    (he : let R := compute keys
      let ids := R.requests.foldl (fun ps j => ps.swap j (j + 1)) (List.range keys.length)
      let values := ids.map (fun i => (I.ports.map σ).getD i false)
      let r := (R.sortedKeys.takeWhile (fun b => decide (b = R.sortedKeys.headD 0))).length
      ∀ b ∈ values.take r, b = values.headD false) :
    let R := compute keys
    let ids := R.requests.foldl (fun ps j => ps.swap j (j + 1)) (List.range keys.length)
    let r := (R.sortedKeys.takeWhile (fun b => decide (b = R.sortedKeys.headD 0))).length
    ∃ τ : ℕ → Bool, (sortAndCloseFirstMetadataRun g w I keys).body.eval sem τ = true ∧
      (∀ z, τ (2^R.requests.length*z) = σ z) ∧
      (sortAndCloseFirstMetadataRun g w I keys).ports.map τ=
        ((ids.map (fun i => (I.ports.map σ).getD i false)).drop r) := by
  let R := compute keys
  let J := sortBoundaryMetadata g w I keys
  obtain ⟨ν, hν, hagree, hword⟩ := (eval_sortBoundaryMetadata_iff g w I keys hl σ).mp hs
  obtain ⟨a, ks, hks, ha⟩ := sorted_cons g w I keys hl hne
  let r := ((a :: ks).takeWhile (fun b => decide (b = a))).length
  change J.ports.map ν = _ at hword
  change (a :: ks).length = J.ports.length at ha
  have hhead : ν (J.ports.headD 0) =
      (R.requests.foldl (fun ps j => ps.swap j (j + 1)) (List.range keys.length) |>.map
        (fun i => (I.ports.map σ).getD i false)).headD false := by
    cases hp : J.ports with
    | nil => simp [hp] at ha
    | cons x ps =>
      simpa only [hp, List.map_cons, List.headD_cons] using
        congrArg (fun xs : List Bool => xs.headD false) hword
  have hconst : ∀ z ∈ J.ports.take r, ν z = ν (J.ports.headD 0) := fun z hz => by
    have hb : ν z ∈ (J.ports.map ν).take r := List.map_take ▸ List.mem_map_of_mem hz
    rw [hword] at hb
    have he' := he
    dsimp only at he'
    simp only [hks, List.headD_cons] at he'
    exact (he' (ν z) hb).trans hhead.symm
  obtain ⟨τ, ht, haτ, hv⟩ := forward_closeFirstMetadataRun sem J a ks ha ν hν hconst
  dsimp only
  simp only [hks, List.headD_cons]
  refine ⟨τ, by simpa only [intermediate g w I keys hl, hks] using ht,
    fun z => (haτ _).trans (hagree z), ?_⟩
  rw [intermediate g w I keys hl, hks]
  exact hv.trans (List.map_drop.trans (congrArg (List.drop r) hword))

/-- Plain all-raw cost is a FIXED composition of the landed generator and literal executor
with the raw coalescer. One Result is stored and projected. Each fold proves its own prefix
bound internally; no generic repeated-polynomial-size or target-arity premise is supplied. -/
theorem computableInPolyTime_sortAndCloseFirstMetadataRun (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => sortAndCloseFirstMetadataRun g w p.1 p.2)
      (encStateMetadata encRel) (encState encRel) := by
  have hi := ComputableInPolyTime.fst (encState encRel) (encList encNat)
  have hk := ComputableInPolyTime.snd (encState encRel) (encList encNat)
  have hI := ComputableInPolyTime.fst (encState encRel) encResult
  have hres := ComputableInPolyTime.snd (encState encRel) encResult
  have hbody := ((computableInPolyTime_closeFirstMetadataRun encRel).comp
    (((computableInPolyTime_transposeSchedule g w encRel).comp
      (hI.prod (encResult_requests_polyTime hres))).prod
      (encResult_sortedKeys_polyTime hres))).comp (hi.prod (computableInPolyTime_compute.comp hk))
  have hbad : ComputableInPolyTime
      (fun p : State Rel × List ℕ => decide (p.2.length ≠ p.1.ports.length))
      (encStateMetadata encRel) encBool := by fun_prop
  exact ComputableInPolyTime.ite_decide hbad hi hbody

end Cslib.Complexity.CSP.CrossInsertion
