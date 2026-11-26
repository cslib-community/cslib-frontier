/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryGroup
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Probe
public import Mathlib.Data.List.Chain
import Mathlib.Data.List.SplitBy
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.TakeDrop

/-!
# Closing every actual consecutive metadata run

The original metadata list funds a State-only fold. The current port count identifies its
unconsumed suffix; each live callback closes exactly that suffix's first run. Once exhausted,
callbacks are literal identities. No sorting, partition or termination certificate is input.

The original construction tracks global collapses on changing names, including names shared
by different runs. One output assignment pulls back through their actual composition;
forwarding requires the source values to agree within each consecutive metadata run. The
literal final table checks the body when the source is accepted. This is a step toward
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091), not atom assembly,
original-variable reconstruction, a planarization reduction or a hardness theorem.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Rel : Type}

/-- Close all maximal consecutive equal-key runs. Alignment is checked before the actual
original key list funds the fold. Binary key magnitudes never count iterations; exhausted
callbacks, empty input and mismatch preserve the entire current raw State. -/
@[expose] def closeMetadataRuns (I : State Rel) (keys : List ℕ) : State Rel :=
  if keys.length ≠ I.ports.length then I else
    keys.foldl (fun J _ =>
      closeFirstMetadataRun J (keys.drop (keys.length-J.ports.length))) I

private def pending (keys : List ℕ) (I : State Rel) : List ℕ :=
  keys.drop (keys.length-I.ports.length)

private def step (keys : List ℕ) (I : State Rel) : State Rel :=
  closeFirstMetadataRun I (pending keys I)

private def runLength (keys : List ℕ) : ℕ :=
  (keys.takeWhile (fun b => decide (b=keys.headD 0))).length

private def collapse (keys : List ℕ) (I : State Rel) (z : ℕ) : ℕ :=
  if z ∈ I.ports.take (runLength (pending keys I)) then I.ports.headD 0 else z

private def stage (keys : List ℕ) (I : State Rel) : ℕ → State Rel
  | 0 => I
  | s+1 => step keys (stage keys I s)

private def pull (keys : List ℕ) (I : State Rel) : ℕ → ℕ → ℕ
  | 0 => id
  | s+1 => collapse keys (stage keys I s) ∘ pull keys I s

private theorem stage_iterate (keys : List ℕ) (I : State Rel) (s : ℕ) :
    stage keys I s = (step keys)^[s] I := by
  induction s with
  | zero => rfl
  | succ s ih => rw [stage, ih, Function.iterate_succ_apply']

private theorem aligned_output (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) : closeMetadataRuns I keys = stage keys I keys.length := by
  rw [closeMetadataRuns,ite_eq_right (not_not.mpr hl),stage_iterate]
  exact List.foldl_const (step keys) I keys

private theorem pending_length (keys : List ℕ) (I : State Rel)
    (h : I.ports.length ≤ keys.length) : (pending keys I).length = I.ports.length := by
  simp only [pending,List.length_drop]
  omega

private theorem run_length_le (keys : List ℕ) : runLength keys ≤ keys.length :=
  (List.takeWhile_sublist _).length_le

private theorem run_length_pos {keys : List ℕ} (h : keys ≠ []) : 0 < runLength keys := by
  cases keys with
  | nil => exact (h rfl).elim
  | cons a ks => simp [runLength]

private theorem drop_runLength (keys : List ℕ) :
    keys.drop (runLength keys) = keys.dropWhile (fun b => decide (b = keys.headD 0)) := by
  have he := congrArg (List.drop (runLength keys))
    (List.takeWhile_append_dropWhile (p := fun b => decide (b = keys.headD 0)) (l := keys))
  simpa only [runLength, List.drop_left] using he.symm

private theorem step_empty (keys : List ℕ) (I : State Rel) (h : I.ports = []) :
    step keys I = I := by
  apply closeFirstMetadataRun_eq_self
  right
  simp only [pending,h,List.length_nil,Nat.sub_zero,List.drop_length]

private theorem pending_step (keys : List ℕ) (I : State Rel)
    (h : I.ports.length ≤ keys.length) :
    pending keys (step keys I) = (pending keys I).drop (runLength (pending keys I)) := by
  have hl := pending_length keys I h
  have hc := (components_closeFirstMetadataRun I (pending keys I)).2.2.2
  simp only [hl,↓reduceIte] at hc
  have hr := (run_length_le (pending keys I)).trans_eq hl
  change (step keys I).ports.length=I.ports.length-runLength (pending keys I) at hc
  change keys.drop (keys.length-(step keys I).ports.length) = _
  rw [show keys.length-(step keys I).ports.length =
      keys.length-I.ports.length+runLength (pending keys I) by omega]
  simp only [pending,List.drop_drop]

private theorem collapse_of_pending_eq {keys : List ℕ} {I : State Rel} {a : ℕ} {ks : List ℕ}
    (he : pending keys I = a :: ks) :
    collapse keys I = fun z =>
      if z ∈ I.ports.take (runLength (a :: ks)) then I.ports.headD 0 else z := by
  funext z
  simp only [collapse, he]

private theorem stage_fields (keys : List ℕ) (I : State Rel)
    (hl : keys.length = I.ports.length) (s : ℕ) :
    let J := stage keys I s
    let n := I.ports.length-J.ports.length
    J.ports.length ≤ I.ports.length-s ∧
      J.body = I.body.relabel (pull keys I s) ∧
      J.ports = (I.ports.drop n).map (pull keys I s) ∧
      (0 < s → I.ports ≠ [] → J.rotation.successor.length =
        2*(I.body.occurrences.length+J.ports.length) ∧
        ∀ v ∈ J.rotation.successor, v < 2*(I.body.occurrences.length+J.ports.length)) := by
  induction s with
  | zero =>
    have hid : Constraint.relabel (Rel := Rel) (id : ℕ → ℕ) = id := by
      funext c; cases c; simp [Constraint.relabel]
    simp [stage,pull,CSP.relabel,hid]
  | succ s ih =>
    dsimp only [stage, pull] at ih ⊢
    set J := stage keys I s
    have hp : J.ports.length≤keys.length := by omega
    have hk := pending_length keys J hp
    cases he : pending keys J with
    | nil =>
      have hz : J.ports=[] := List.length_eq_zero_iff.mp (by simpa only [he,List.length_nil] using
        hk.symm)
      have hs := step_empty keys J hz
      have hC : collapse keys J=id := by funext z; simp [collapse,he,runLength]
      rw [hs]
      refine ⟨by simp only [hz,List.length_nil]; omega,?_,?_,?_⟩
      · simpa only [hC,Function.id_comp] using ih.2.1
      · simpa only [hC,Function.id_comp] using ih.2.2.1
      · intro _ hn
        by_cases hs0 : s=0
        · subst s
          exact (hn (by simpa only [J,stage] using hz)).elim
        · exact ih.2.2.2 (by omega) hn
    | cons a ks =>
      have ha : (a::ks).length=J.ports.length := by rwa [he] at hk
      have hf := fields_closeFirstMetadataRun J a ks ha
      have hr : 0<runLength (a::ks) := run_length_pos (by simp)
      have hb : runLength (a::ks)≤J.ports.length := (run_length_le _).trans_eq ha
      have hm : J.body.occurrences.length=I.body.occurrences.length := by
        rw [ih.2.1,← CSP.vars_length_eq_occurrences,CSP.vars_relabel,List.length_map,
          CSP.vars_length_eq_occurrences]
      have hbody : (step keys J).body = J.body.relabel (collapse keys J) := by
        rw [step, he, collapse_of_pending_eq he]
        exact hf.1
      have hports : (step keys J).ports = (J.ports.drop (runLength (a::ks))).map
          (collapse keys J) := by
        rw [step, he, collapse_of_pending_eq he]
        exact hf.2.1
      have hlen : (step keys J).ports.length = J.ports.length - runLength (a::ks) := by
        rw [hports, List.length_map, List.length_drop]
      refine ⟨by omega, ?_, ?_, fun _ _ => ?_⟩
      · rw [hbody, ih.2.1]
        simp only [CSP.relabel, Constraint.relabel, List.map_map, Function.comp_def]
        rfl
      · have heq : I.ports.length - J.ports.length + runLength (a::ks) =
            I.ports.length - (step keys J).ports.length := by omega
        rw [← heq, hports]
        conv_lhs => rw [ih.2.2.1, ← List.map_drop, List.map_map, List.drop_drop]
      · have heq : J.body.occurrences.length + J.ports.length - runLength (a::ks) =
            I.body.occurrences.length + (step keys J).ports.length := by omega
        have hrl : runLength (a::ks) = (List.takeWhile (fun b => decide (b=a)) (a::ks)).length :=
          rfl
        have ht := hf.2.2
        rw [← hrl, heq] at ht
        simpa only [step, he] using ht

private theorem pull_range (keys : List ℕ) (I : State Rel) (s : ℕ) :
    pull keys I s = (List.range s).foldl
      (fun f n => collapse keys (stage keys I n) ∘ f) id := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [pull,ih,List.range_succ,List.foldl_append,
      List.foldl_cons,List.foldl_nil]

/-- Mismatch and empty metadata preserve the entire raw input, including surplus or huge
malformed successor entries. Nonempty aligned metadata is not an identity claim. -/
theorem closeMetadataRuns_eq_self (I : State Rel) (keys : List ℕ)
    (h : keys.length ≠ I.ports.length ∨ keys = []) : closeMetadataRuns I keys = I := by
  rcases h with h | rfl
  · simp only [closeMetadataRuns,ite_eq_left h]
  · simp [closeMetadataRuns]

/-- Complete consumption and global relabeling by the actual prefix collapses. The map is
specified from executed prefix states, rather than supplied by the caller. A nonempty
aligned run sequence emits the literal final body-sized table with bounded entries. -/
theorem fields_closeMetadataRuns (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) :
    let states := fun s => (fun J : State Rel => closeFirstMetadataRun J
      (keys.drop (keys.length-J.ports.length)))^[s] I
    let Phi := (List.range keys.length).foldl (fun f s => fun z =>
      if f z ∈ (states s).ports.take
          ((keys.drop (keys.length-(states s).ports.length)).takeWhile
            (fun b => decide (b = (keys.drop (keys.length-(states s).ports.length)).headD
              0))).length
      then (states s).ports.headD 0 else f z) id
    let K := closeMetadataRuns I keys
    K.body = I.body.relabel Phi ∧ K.ports = [] ∧
      (keys ≠ [] → K.rotation.successor.length = 2*I.body.occurrences.length ∧
        ∀ v ∈ K.rotation.successor, v < 2*I.body.occurrences.length) := by
  have hf := stage_fields keys I hl keys.length
  have hp : (stage keys I keys.length).ports=[] := by
    apply List.length_eq_zero_iff.mp
    dsimp only at hf
    omega
  rw [aligned_output I keys hl]
  change (stage keys I keys.length).body=I.body.relabel
      ((List.range keys.length).foldl (fun f s => collapse keys ((step keys)^[s] I) ∘ f) id) ∧ _
  simp_rw [← stage_iterate]
  rw [← pull_range]
  refine ⟨hf.2.1,hp,?_⟩
  intro hn
  have hs : 0<keys.length := List.length_pos_iff.mpr hn
  have hi : I.ports≠[] := by intro h; simp only [h,List.length_nil] at hl; omega
  simpa only [hp,List.length_nil,Nat.add_zero] using hf.2.2.2 hs hi

private theorem fold_accepted (keys fuel : List ℕ) (I : State Rel) (hI : I.Accepted) :
    (fuel.foldl (fun J _ => step keys J) I).Accepted := by
  induction fuel generalizing I with
  | nil => exact hI
  | cons a fuel ih => exact ih _ (accepted_closeFirstMetadataRun I _ hI)

/-- Every executed first-run closure preserves the complete checker internally. -/
theorem accepted_closeMetadataRuns (I : State Rel) (keys : List ℕ) (hI : I.Accepted) :
    (closeMetadataRuns I keys).Accepted := by
  unfold closeMetadataRuns
  split
  exacts [hI, fold_accepted keys keys I hI]

private theorem fold_arity (ar : Rel → ℕ) (keys fuel : List ℕ) (I : State Rel) :
    (fuel.foldl (fun J _ => step keys J) I).body.WellFormed ar ↔ I.body.WellFormed ar := by
  induction fuel generalizing I with
  | nil => rfl
  | cons a fuel ih => exact (ih _).trans (wellFormed_closeFirstMetadataRun_iff ar I _)

/-- Exact arity iff on every raw input. Semantic truth does not replace the arity guard. -/
theorem wellFormed_closeMetadataRuns_iff (ar : Rel → ℕ) (I : State Rel) (keys : List ℕ) :
    (closeMetadataRuns I keys).body.WellFormed ar ↔ I.body.WellFormed ar := by
  unfold closeMetadataRuns
  split
  exacts [Iff.rfl, fold_arity ar keys keys I]

private theorem fold_components (keys fuel : List ℕ) (I : State Rel) :
    let J := fuel.foldl (fun J _ => step keys J) I
    J.body.length = I.body.length ∧ J.body.occurrences.length = I.body.occurrences.length ∧
      J.body.map (fun c => (c.rel,c.scope.length)) = I.body.map (fun c => (c.rel,c.scope.length)) ∧
      J.ports.length ≤ I.ports.length ∧ J.body.vars++J.ports ⊆ I.body.vars++I.ports := by
  induction fuel generalizing I with
  | nil => exact ⟨rfl,rfl,rfl,le_rfl,fun _ h => h⟩
  | cons a fuel ih =>
    have hc := components_closeFirstMetadataRun I (pending keys I)
    have hn := names_closeFirstMetadataRun_subset I (pending keys I)
    have hf := ih (step keys I)
    dsimp only at hc hf ⊢
    refine ⟨hf.1.trans hc.1,hf.2.1.trans hc.2.1,
      hf.2.2.1.trans hc.2.2.1,?_,?_⟩
    · exact hf.2.2.2.1.trans (by
        change (closeFirstMetadataRun I (pending keys I)).ports.length ≤ I.ports.length
        rw [hc.2.2.2]; exact Nat.sub_le _ _)
    · exact fun _ h => hn (hf.2.2.2.2 h)

/-- Closing all runs retains every indexed relation/scope-width pair, including duplicate
rows and nullaries, and consumes all ports exactly on aligned input. -/
theorem components_closeMetadataRuns (I : State Rel) (keys : List ℕ) :
    let K := closeMetadataRuns I keys
    K.body.length = I.body.length ∧ K.body.occurrences.length = I.body.occurrences.length ∧
      K.body.map (fun c => (c.rel,c.scope.length)) = I.body.map (fun c => (c.rel,c.scope.length)) ∧
      K.ports.length = if keys.length = I.ports.length then 0 else I.ports.length := by
  by_cases hl : keys.length=I.ports.length
  · dsimp only
    have hf := fold_components keys keys I
    have hp' : (keys.foldl (fun J _ => step keys J) I).ports = [] := by
      simpa only [closeMetadataRuns, ite_eq_right (not_not.mpr hl), step, pending] using
        (fields_closeMetadataRuns I keys hl).2.1
    rw [closeMetadataRuns, ite_eq_right (not_not.mpr hl)]
    refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
    change (keys.foldl (fun J _ => step keys J) I).ports.length = _
    simp [hp', hl]
  · rw [closeMetadataRuns_eq_self I keys (Or.inl hl)]
    simp [hl]

/-- Every emitted body/port name is selected from the original body/ports; no group step
increases the original maximum name width, even when names occur in multiple runs. -/
theorem names_closeMetadataRuns_subset (I : State Rel) (keys : List ℕ) :
    (closeMetadataRuns I keys).body.vars++(closeMetadataRuns I keys).ports ⊆
      I.body.vars++I.ports := by
  unfold closeMetadataRuns
  split
  exacts [fun _ h => h, (fold_components keys keys I).2.2.2.2]

/-- At exhaustion the literal emitted certificate checks the actual original-language body.
Empty aligned inputs retain their entire certificate; source acceptance supplies this case. -/
theorem body_accepted_closeMetadataRuns (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) (hI : I.Accepted) :
    verifyRotationCertificate (closeMetadataRuns I keys).body
      (closeMetadataRuns I keys).rotation = true := by
  let K := closeMetadataRuns I keys
  have ha := accepted_closeMetadataRuns I keys hI
  have hp : K.ports=[] := (fields_closeMetadataRuns I keys hl).2.1
  have hb := (verify_eq_true_iff K.body K.ports K.rotation).mp ha.2
  rw [hp,verifyRotationCertificate_probeBody_nil] at hb
  exact hb.2

private theorem split_first_run (keys : List ℕ) (hn : keys ≠ []) :
    keys.splitBy (fun a b => decide (a = b)) = keys.takeWhile (fun b => decide (b = keys.headD 0))
      ::
        (keys.drop (runLength keys)).splitBy (fun a b => decide (a = b)) := by
  let p := fun b => decide (b=keys.headD 0)
  let pre := keys.takeWhile p
  let rest := keys.dropWhile p
  have hpre : pre≠[] := by
    cases keys with
    | nil => exact (hn rfl).elim
    | cons a ks => simp [pre,p]
  have hall (b) (hb : b ∈ pre) : b = keys.headD 0 :=
    of_decide_eq_true (List.mem_takeWhile_imp (p := p) hb)
  have hc : pre.IsChain (fun a b => decide (a = b)) :=
    List.isChain_iff_getElem.mpr fun i hi =>
      decide_eq_true ((hall _ (List.getElem_mem _)).trans (hall _ (List.getElem_mem _)).symm)
  have hb : ∀ x ∈ pre.getLast?, ∀ y ∈ rest.head?, decide (x = y) = false := by
    rintro x hx y hy
    rcases hr : rest with _ | ⟨b, bs⟩
    · simp [hr] at hy
    · obtain rfl : b = y := by simpa [hr] using hy
      have hbad : p b = false := by
        simpa only [rest, hr, List.head?_cons] using List.head?_dropWhile_not p keys
      simpa only [p, hall x (List.mem_of_mem_getLast? hx), eq_comm] using hbad
  rw [drop_runLength]
  change keys.splitBy (fun a b => decide (a=b))=pre::rest.splitBy (fun a b => decide (a=b))
  calc
    _ = (pre++rest).splitBy (fun a b => decide (a=b)) :=
      congrArg (List.splitBy (fun a b => decide (a=b)))
        (show pre++rest=keys from List.takeWhile_append_dropWhile).symm
    _ = _ := by rw [List.splitBy_append hb,List.splitBy_of_isChain hpre hc]; rfl

private def closedBlocks (keys : List ℕ) (I : State Rel) (s : ℕ) : List (List ℕ) :=
  ((List.range s).map (fun i => (pending keys (stage keys I i)).takeWhile
    (fun b => decide (b=(pending keys (stage keys I i)).headD 0)))).filter
      (fun xs => decide (xs≠[]))

private theorem closedBlocks_step (keys : List ℕ) (I : State Rel) (s : ℕ) :
    closedBlocks keys I (s+1) = closedBlocks keys I s ++
      if pending keys (stage keys I s) = [] then [] else
        [(pending keys (stage keys I s)).takeWhile
          (fun b => decide (b = (pending keys (stage keys I s)).headD 0))] := by
  simp only [closedBlocks,List.range_succ,List.map_append,List.map_cons,List.map_nil,
    List.filter_append,List.filter_cons,List.filter_nil]
  by_cases h : pending keys (stage keys I s)=[]
  · simp [h]
  · have hp := run_length_pos h
    have hn : (pending keys (stage keys I s)).takeWhile
        (fun b => decide (b=(pending keys (stage keys I s)).headD 0))≠[] := by
      simpa only [← List.length_pos_iff,runLength] using hp
    simp only [ite_eq_right h,decide_eq_true hn,ite_true]

private theorem partition_prefix (keys : List ℕ) (I : State Rel)
    (hl : keys.length = I.ports.length) (s : ℕ) :
    closedBlocks keys I s ++
      (pending keys (stage keys I s)).splitBy (fun a b => decide (a = b)) = keys.splitBy (fun a b
        => decide (a = b)) := by
  induction s with
  | zero => simp [closedBlocks,stage,pending,hl]
  | succ s ih =>
    have hf := stage_fields keys I hl s
    have hp : (stage keys I s).ports.length≤keys.length := by dsimp only at hf; omega
    have he := pending_step keys (stage keys I s) hp
    rw [closedBlocks_step,stage,he]
    by_cases hn : pending keys (stage keys I s)=[]
    · simpa only [hn,List.drop_nil,List.splitBy_nil,↓reduceIte,List.append_nil] using ih
    · rw [ite_eq_right hn,List.append_assoc,List.singleton_append,
        ← split_first_run _ hn]
      exact ih

private theorem split_count (keys : List ℕ) :
    (keys.splitBy (fun a b => decide (a = b))).length = if keys = [] then 0 else 1+(keys.zip
      keys.tail).countP (fun p => decide (p.1 ≠ p.2)) := by
  induction keys using List.twoStepInduction with
  | nil => simp
  | singleton a =>
    rw [List.splitBy_of_isChain (by simp) (by simp)]
    simp
  | cons_cons a b ks _ih ihTail =>
    by_cases hab : a=b
    · subst b
      have h1 := split_first_run (a::a::ks) (by simp)
      have h2 := split_first_run (a::ks) (by simp)
      have he : ((a::a::ks).drop (runLength (a::a::ks)))=
          ((a::ks).drop (runLength (a::ks))) := by
        simp [runLength]
      rw [h1,List.length_cons,he,← List.length_cons,← h2,ihTail]
      simp
    · rw [split_first_run (a::b::ks) (by simp)]
      have hr : runLength (a::b::ks)=1 := by simp [runLength,hab,eq_comm]
      simp only [hr,List.drop_succ_cons,List.drop_zero,List.length_cons,ihTail]
      simp [hab,Nat.add_assoc]

private def fusionCount (keys : List ℕ) (I : State Rel) (s : ℕ) : ℕ :=
  ((List.range s).map (fun i => runLength (pending keys (stage keys I i))-1)).sum

private theorem fusion_potential (keys : List ℕ) (I : State Rel)
    (hl : keys.length = I.ports.length) (s : ℕ) :
    fusionCount keys I s+(closedBlocks keys I s).length+
      (stage keys I s).ports.length = I.ports.length := by
  induction s with
  | zero => simp [fusionCount,closedBlocks,stage]
  | succ s ih =>
    have hf := stage_fields keys I hl s
    have hp : (stage keys I s).ports.length≤keys.length := by dsimp only at hf; omega
    have ha := pending_length keys (stage keys I s) hp
    have hc := (components_closeFirstMetadataRun (stage keys I s)
      (pending keys (stage keys I s))).2.2.2
    simp only [ha,↓reduceIte] at hc
    have hs : fusionCount keys I (s+1)=fusionCount keys I s+
        (runLength (pending keys (stage keys I s))-1) := by
      simp only [fusionCount,List.range_succ,List.map_append,List.map_cons,List.map_nil,
        List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
    rw [hs,closedBlocks_step,stage]
    by_cases hn : pending keys (stage keys I s)=[]
    · simp only [hn,↓reduceIte,List.append_nil,runLength,List.takeWhile_nil,List.length_nil] at hc ⊢
      have hz : (stage keys I s).ports=[] := List.length_eq_zero_iff.mp (by
        simpa only [hn,List.length_nil] using ha.symm)
      rw [step_empty keys _ hz]
      simp only [hz,List.length_nil] at ih ⊢
      omega
    · have hr := run_length_pos hn
      simp only [ite_eq_right hn,List.length_append,List.length_singleton]
      change (step keys (stage keys I s)).ports.length=
        (stage keys I s).ports.length-runLength (pending keys (stage keys I s)) at hc
      have hb := (run_length_le _).trans_eq ha
      omega

/-- The nonempty blocks closed by the ACTUAL prefix callbacks are exactly `List.splitBy`
consecutive equality runs, in order. Thus their concatenation is all metadata, and literal
fusion/hide counts are `P-G` and `G`; no separate instrumented execution is used. -/
theorem partition_closeMetadataRuns (I : State Rel) (keys : List ℕ)
    (hl : keys.length = I.ports.length) :
    let states := fun s => (fun J : State Rel => closeFirstMetadataRun J
      (keys.drop (keys.length-J.ports.length)))^[s] I
    let blocks := ((List.range keys.length).map (fun s =>
      (keys.drop (keys.length-(states s).ports.length)).takeWhile
        (fun b => decide (b = (keys.drop (keys.length-(states s).ports.length)).headD 0)))).filter
          (fun xs => decide (xs ≠ []))
    let F := ((List.range keys.length).map (fun s =>
      ((keys.drop (keys.length-(states s).ports.length)).takeWhile
        (fun b => decide (b = (keys.drop (keys.length-(states s).ports.length)).headD
          0))).length-1)).sum
    let G := if keys = [] then 0 else 1+(keys.zip keys.tail).countP (fun p => decide (p.1 ≠ p.2))
    blocks = keys.splitBy (fun a b => decide (a = b)) ∧ blocks.flatten = keys ∧
      F = I.ports.length-G ∧ blocks.length = G ∧ F+blocks.length = I.ports.length := by
  have hp : (stage keys I keys.length).ports=[] :=
    aligned_output I keys hl ▸ (fields_closeMetadataRuns I keys hl).2.1
  have he : closedBlocks keys I keys.length=keys.splitBy (fun a b => decide (a=b)) := by
    simpa only [pending,hp,List.length_nil,Nat.sub_zero,List.drop_length,
      List.splitBy_nil,List.append_nil] using partition_prefix keys I hl keys.length
  have hn := fusion_potential keys I hl keys.length
  rw [hp, List.length_nil, Nat.add_zero] at hn
  have hlen_eq : (closedBlocks keys I keys.length).length =
      if keys = [] then 0 else 1 + (keys.zip keys.tail).countP (fun p => decide (p.1 ≠ p.2)) :=
    he ▸ split_count keys
  dsimp only
  have hstep_eq : (fun J : State Rel => closeFirstMetadataRun J
      (keys.drop (keys.length - J.ports.length))) = step keys := rfl
  simp_rw [hstep_eq, ← stage_iterate]
  change closedBlocks keys I keys.length = _ ∧ (closedBlocks keys I keys.length).flatten = keys ∧
    fusionCount keys I keys.length = _ ∧ (closedBlocks keys I keys.length).length = _ ∧
    fusionCount keys I keys.length + (closedBlocks keys I keys.length).length = I.ports.length
  exact ⟨he, he ▸ List.flatten_splitBy _ _, by omega, hlen_eq, hn⟩

private theorem first_run_agreement (keys : List ℕ) (values : List Bool)
    (hl : keys.length = values.length) :
    (keys.zip values).IsChain (fun a b => a.1 = b.1 → a.2 = b.2) ↔
      (values.take (runLength keys)).IsChain (· = ·) ∧
      ((keys.drop (runLength keys)).zip (values.drop (runLength keys))).IsChain
        (fun a b => a.1 = b.1 → a.2 = b.2) := by
  let p := fun b => decide (b=keys.headD 0)
  let pre := keys.takeWhile p
  let rest := keys.dropWhile p
  have hk : pre++rest=keys := List.takeWhile_append_dropWhile
  have hdrop : keys.drop (runLength keys)=rest := drop_runLength keys
  have hb : pre.length≤values.length := (List.takeWhile_sublist _).length_le.trans_eq hl
  have hp : pre.length=(values.take pre.length).length := by simp [Nat.min_eq_left hb]
  have hall (q) (hq : q ∈ pre.zip (values.take pre.length)) : q.1 = keys.headD 0 :=
    of_decide_eq_true (List.mem_takeWhile_imp (p := p) (List.of_mem_zip hq).1)
  have hprefix : (pre.zip (values.take pre.length)).IsChain
      (fun a b => a.1 = b.1 → a.2 = b.2) ↔ (values.take pre.length).IsChain (· = ·) := by
    conv_rhs => rw [← List.map_snd_zip hp.ge, List.isChain_map]
    exact ⟨fun h => h.imp_of_mem_imp fun a b ha hb hab =>
        hab ((hall a ha).trans (hall b hb).symm),
      fun h => h.imp fun _ _ h _ => h⟩
  have hboundary : ∀ a ∈ (pre.zip (values.take pre.length)).getLast?,
      ∀ b ∈ (rest.zip (values.drop pre.length)).head?, a.1 = b.1 → a.2 = b.2 := by
    intro a ha b hbb he
    rcases hrest : rest with _ | ⟨x, xs⟩
    · simp [hrest] at hbb
    · rcases hv : values.drop pre.length with _ | ⟨v, vs⟩
      · simp [hv] at hbb
      · obtain rfl : b = (x, v) := by simpa [hrest, hv, eq_comm] using hbb
        have hx : p x = false := by
          simpa only [rest, hrest, List.head?_cons] using List.head?_dropWhile_not p keys
        exact absurd (he.symm.trans (hall a (List.mem_of_mem_getLast? ha)))
          (of_decide_eq_false hx)
  have he : keys.zip values=(pre.zip (values.take pre.length))++
      (rest.zip (values.drop pre.length)) := by
    conv_lhs => rw [← hk,← List.take_append_drop pre.length values,List.zip_append hp]
  rw [he,List.isChain_append,hprefix,hdrop]
  change _ ↔ (values.take pre.length).IsChain (· = ·) ∧ _
  exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,hboundary⟩⟩

private theorem selected_values_constant (I : State Rel) (keys : List ℕ) (σ : ℕ → Bool)
    (hl : keys.length = I.ports.length) (hn : keys ≠ [])
    (h : (keys.zip (I.ports.map σ)).IsChain (fun a b => a.1 = b.1 → a.2 = b.2)) :
    ∀ z ∈ I.ports.take (runLength keys), σ z = σ (I.ports.headD 0) := by
  have hv := (first_run_agreement keys (I.ports.map σ)
    (by simpa only [List.length_map] using hl)).mp h |>.1
  rw [← List.map_take] at hv
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (run_length_pos hn))
  cases he : I.ports with
  | nil =>
    exact (hn (List.length_eq_zero_iff.mp (by simpa only [he,List.length_nil] using hl))).elim
  | cons x xs =>
    rw [hr,he,List.take_succ_cons,List.map_cons] at hv
    have ht := (List.pairwise_cons.mp hv.pairwise).1
    intro z hz
    simp only [hr,List.take_succ_cons,List.mem_cons,List.headD_cons] at hz ⊢
    rcases hz with rfl | hz
    · rfl
    · exact (ht (σ z) (List.mem_map.mpr ⟨z,hz,rfl⟩)).symm

private theorem stage_shift (keys : List ℕ) (I : State Rel) (s : ℕ) :
    stage keys I (s+1) = stage keys (step keys I) s := by
  induction s with
  | zero => rfl
  | succ s ih => exact congrArg (step keys) ih

private theorem pull_shift (keys : List ℕ) (I : State Rel) (s : ℕ) :
    pull keys I (s+1) = pull keys (step keys I) s ∘ collapse keys I := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change collapse keys (stage keys I (s+1)) ∘ pull keys I (s+1) = _
    rw [stage_shift,ih]
    rfl

private theorem empty_execution (keys : List ℕ) (I : State Rel) (hp : I.ports = []) (s : ℕ) :
    stage keys I s = I ∧ pull keys I s = id := by
  induction s with
  | zero => exact ⟨rfl,rfl⟩
  | succ s ih =>
    have hs := step_empty keys I hp
    have hc : collapse keys I=id := by funext z; simp [collapse,hp,pending,runLength]
    simp only [stage,pull,ih.1,ih.2,hs,hc,Function.id_comp,and_self]

private theorem recover_fuel (keys : List ℕ) (fuel : ℕ) (I : State Rel)
    (hp : I.ports.length ≤ keys.length) (hf : I.ports.length ≤ fuel)
    (sem : Rel → List Bool → Bool) (τ : ℕ → Bool)
    (ht : (stage keys I fuel).body.eval sem τ = true) :
    I.body.eval sem (τ ∘ pull keys I fuel) = true ∧
      ((pending keys I).zip (I.ports.map (τ ∘ pull keys I fuel))).IsChain
        (fun a b => a.1 = b.1 → a.2 = b.2) := by
  induction fuel generalizing I with
  | zero =>
    have hz : I.ports=[] := List.length_eq_zero_iff.mp (by omega)
    exact ⟨ht,by simp [hz,pending]⟩
  | succ fuel ih =>
    by_cases hz : I.ports=[]
    · have he := empty_execution keys I hz (fuel+1)
      exact ⟨by simpa only [he.1,he.2,Function.comp_id] using ht,by simp [hz,pending]⟩
    · have hl := pending_length keys I hp
      have hn : pending keys I≠[] := fun he =>
        hz (List.length_eq_zero_iff.mp (by simpa only [he,List.length_nil] using hl.symm))
      obtain ⟨a,ks,he⟩ := List.exists_cons_of_ne_nil hn
      have ha : (a::ks).length=I.ports.length := by rwa [he] at hl
      have hr := run_length_pos hn
      have hc := (components_closeFirstMetadataRun I (pending keys I)).2.2.2
      simp only [hl,↓reduceIte] at hc
      have hJ : (step keys I).ports.length=I.ports.length-runLength (pending keys I) := hc
      have hrec := ih (step keys I) (by omega) (by omega) (by rwa [stage_shift] at ht)
      rw [pull_shift]
      set ν := τ ∘ pull keys (step keys I) fuel
      have hb := recover_closeFirstMetadataRun sem I a ks ha ν
        (by simpa only [step, he] using hrec.1)
      have hbody : I.body.eval sem (ν ∘ collapse keys I) = true := by
        rw [collapse_of_pending_eq he]
        exact hb.1
      refine ⟨by simpa only [ν, Function.comp_assoc] using hbody, ?_⟩
      change ((pending keys I).zip (I.ports.map (ν ∘ collapse keys I))).IsChain _
      apply (first_run_agreement _ _ (by simpa only [List.length_map] using hl)).mpr
      constructor
      · rw [← List.map_take, List.map_congr_left fun z hz' => show (ν ∘ collapse keys I) z =
            ν (I.ports.headD 0) by simp only [Function.comp_apply, collapse, ite_eq_left hz']]
        exact (List.isChain_map _).mpr (List.isChain_iff_getElem.mpr fun _ _ => rfl)
      · have hw : (step keys I).ports.map ν =
            (I.ports.drop (runLength (pending keys I))).map (ν ∘ collapse keys I) := by
          rw [step, collapse_of_pending_eq he, he]
          exact hb.2.2
        have hh := hrec.2
        rw [pending_step keys I hp, hw] at hh
        simpa only [← List.map_drop] using hh

private theorem forward_fuel (keys : List ℕ) (fuel : ℕ) (I : State Rel)
    (hp : I.ports.length ≤ keys.length) (hf : I.ports.length ≤ fuel)
    (sem : Rel → List Bool → Bool) (σ : ℕ → Bool)
    (hs : I.body.eval sem σ = true)
    (he : ((pending keys I).zip (I.ports.map σ)).IsChain
      (fun a b => a.1 = b.1 → a.2 = b.2)) :
    (stage keys I fuel).body.eval sem σ = true ∧ ∀ z, σ (pull keys I fuel z) = σ z := by
  induction fuel generalizing I with
  | zero => exact ⟨hs,fun _ => rfl⟩
  | succ fuel ih =>
    by_cases hz : I.ports=[]
    · have hx := empty_execution keys I hz (fuel+1)
      exact ⟨by simpa only [hx.1] using hs,by simp only [hx.2,id_eq,implies_true]⟩
    · have hl := pending_length keys I hp
      have hn : pending keys I ≠ [] := fun h =>
        hz (List.length_eq_zero_iff.mp (by simpa only [h,List.length_nil] using hl.symm))
      obtain ⟨a,ks,hkeys⟩ := List.exists_cons_of_ne_nil hn
      have ha : (a::ks).length=I.ports.length := by rwa [hkeys] at hl
      have hc := selected_values_constant I (pending keys I) σ hl hn he
      obtain ⟨ν,hν,hνeq,hword⟩ := forward_closeFirstMetadataRun sem I a ks ha σ hs
        (by simpa only [hkeys,runLength,List.headD_cons] using hc)
      have hνfun : ν=σ := funext hνeq
      subst ν
      have hbody : (step keys I).body.eval sem σ=true := by simpa only [step,hkeys] using hν
      have htail := (first_run_agreement _ _ (by simpa only [List.length_map] using hl)).mp he |>.2
      have hw : (step keys I).ports.map σ=(I.ports.drop (runLength (pending keys I))).map σ := by
        simpa only [step,hkeys,runLength,List.headD_cons] using hword
      have he' : ((pending keys (step keys I)).zip ((step keys I).ports.map σ)).IsChain
          (fun a b => a.1=b.1 → a.2=b.2) := by
        rw [pending_step keys I hp,hw]
        simpa only [← List.map_drop] using htail
      have hd := (components_closeFirstMetadataRun I (pending keys I)).2.2.2
      simp only [hl,↓reduceIte] at hd
      change (step keys I).ports.length = I.ports.length-runLength (pending keys I) at hd
      have hr := run_length_pos hn
      have hh := ih (step keys I) (by omega)
        (by omega) hbody he'
      refine ⟨by simpa only [stage_shift] using hh.1,?_⟩
      intro z
      rw [pull_shift,Function.comp_apply,hh.2]
      by_cases hm : z∈I.ports.take (runLength (pending keys I))
      · simpa only [collapse,ite_eq_left hm] using (hc z hm).symm
      · simp only [collapse,ite_eq_right hm]

/-- ONE satisfying final assignment recovers source truth through the composition of the
ACTUAL global collapses. The adjacent chain says precisely that values agree on every
maximal consecutive equal-key run; different separated runs are not identified by metadata.
No source checker, arity, distinctness or disjoint-name premise is used. -/
theorem recover_closeMetadataRuns (sem : Rel → List Bool → Bool) (I : State Rel)
    (keys : List ℕ) (hl : keys.length = I.ports.length) (τ : ℕ → Bool)
    (ht : (closeMetadataRuns I keys).body.eval sem τ = true) :
    let states := fun s => (fun J : State Rel => closeFirstMetadataRun J
      (keys.drop (keys.length-J.ports.length)))^[s] I
    let Phi := (List.range keys.length).foldl (fun f s => fun z =>
      if f z ∈ (states s).ports.take
          ((keys.drop (keys.length-(states s).ports.length)).takeWhile
            (fun b => decide (b = (keys.drop (keys.length-(states s).ports.length)).headD
              0))).length
      then (states s).ports.headD 0 else f z) id
    I.body.eval sem (τ ∘ Phi) = true ∧
      (keys.zip (I.ports.map (τ ∘ Phi))).IsChain
        (fun a b => a.1 = b.1 → a.2 = b.2) := by
  change I.body.eval sem (τ ∘ ((List.range keys.length).foldl
    (fun f s => collapse keys ((step keys)^[s] I) ∘ f) id))=true ∧
    (keys.zip (I.ports.map (τ ∘ ((List.range keys.length).foldl
      (fun f s => collapse keys ((step keys)^[s] I) ∘ f) id)))).IsChain _
  simp_rw [← stage_iterate, ← pull_range]
  have hr := recover_fuel keys keys.length I hl.ge hl.ge sem τ
    (by rwa [← aligned_output I keys hl])
  simpa only [pending,hl,Nat.sub_self,List.drop_zero] using hr

/-- A source assignment already constant within each consecutive metadata run satisfies
the final body UNCHANGED on every natural name, including unused names. This does not infer
source equalities from arbitrary output values at eliminated labels. -/
theorem forward_closeMetadataRuns (sem : Rel → List Bool → Bool) (I : State Rel)
    (keys : List ℕ) (hl : keys.length = I.ports.length) (σ : ℕ → Bool)
    (hs : I.body.eval sem σ = true)
    (he : (keys.zip (I.ports.map σ)).IsChain (fun a b => a.1 = b.1 → a.2 = b.2)) :
    (closeMetadataRuns I keys).body.eval sem σ = true := by
  rw [aligned_output I keys hl]
  exact (forward_fuel keys keys.length I hl.ge hl.ge sem σ hs
    (by simpa only [pending,hl,Nat.sub_self,List.drop_zero] using he)).1

end Cslib.Complexity.CSP.CrossInsertion
