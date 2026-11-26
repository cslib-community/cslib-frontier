/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Lifting
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Lifting
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Exact finite-buffer lifting agreement

Every surviving port, local exchange test and first-exit/arm scan is related to the original
whole-instance lifting construction. This representation bookkeeping is original and preserves
outside comparison changes and repeated copies of original constraints.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.NativeLifting

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open EdgeAugmenting (occurrenceIndex)

private theorem oldRecord_record {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (o : Occurrence F) (ho : o.var ∉ vs) :
    oldRecord F vs o.record = (Blossom.oldPort f vs o ho).record := by
  simp only [oldRecord, scope, Occurrence.record, List.getD_eq_getElem _ _ o.1.isLt,
    Blossom.oldPort_var]
  rfl

/-- The raw finite inverse is exactly the original surviving-port lookup, including its
explicit fallback on malformed connector requests. No edge or validity assumption is needed. -/
theorem restore_code {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (fallback : Occurrence F) (o : Occurrence (Blossom.contract f vs)) :
    restore ⟨F, (incidenceList F).map f⟩ vs (occurrenceIndex fallback) (occurrenceIndex o) =
      occurrenceIndex (Blossom.restorePortOr f vs fallback o) := by
  have hp : (fun p : Occurrence F => !vs.contains p.record.2.2 &&
      oldRecord F vs p.record == o.record) =
      (fun p => if h : p.var ∈ vs then false else Blossom.oldPort f vs p h == o) := by
    funext p
    by_cases h : p.var ∈ vs
    · simp [h, Occurrence.record]
    · simp [show p.record.2.2 = p.var from rfl, h, oldRecord_record f vs p h,
        Occurrence.record_injective.eq_iff]
  unfold restore
  rw [Contraction.contract_eq, EdgeAugmenting.labeling_map, EdgeAugmenting.recordAt_index]
  simp only [occurrences_eq_map_incidenceList, List.find?_map, Option.map_map, Function.comp_def]
  change (((incidenceList F).find? _).map
    (fun p => ((incidenceList F).map Occurrence.record).idxOf p.record)).getD _ = _
  rw [hp, ← occurrences_eq_map_incidenceList, ← Blossom.restorePort]
  cases he : Blossom.restorePort f vs o <;>
    simp [Blossom.restorePortOr, EdgeAugmenting.record_index, he]

/-- Restoring every binary step position gives exactly the source walk map, in source order. -/
theorem restoreWalk_code {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (fallback : Occurrence F) (p : Walk (Blossom.contract f vs)) :
    restoreWalk ⟨F, (incidenceList F).map f⟩ vs (occurrenceIndex fallback)
      (EdgeAugmenting.code p) = EdgeAugmenting.code (Blossom.restoreWalk f vs fallback p) := by
  simp [restoreWalk, EdgeAugmenting.code, Blossom.restoreWalk, Walk.mapPorts,
    List.map_map, Function.comp_def, restore_code]

private theorem valid_pair_buffer {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool)
    (o e : Occurrence F) :
    EdgeAugmenting.valid F
      (NativeWalk.flip (NativeWalk.flip ((incidenceList F).map f) [occurrenceIndex o])
        [occurrenceIndex e]) = decide (ValidLabeling Table.sem (DAG.pairFlip f o e)) := by
  change EdgeAugmenting.valid F (NativeWalk.flip
    (NativeWalk.flip ((incidenceList F).map f) ([o].map occurrenceIndex))
    ([e].map occurrenceIndex)) = _
  rw [NativeWalk.flip_buffer, NativeWalk.flip_buffer, EdgeAugmenting.valid_eq,
    EdgeAugmenting.labeling_map]
  rfl

/-- The finite exit scan has exactly the source's original-port order and pair-flip tests.
Two equal ports cancel, as in the source's sequential pair flip. -/
theorem exitsAt_code {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool)
    (w r : Walk F) (n : ℕ) :
    exitsAt ⟨F, (incidenceList F).map f⟩ (EdgeAugmenting.code w) (EdgeAugmenting.code r) n =
      (Blossom.exitsAt f w r n).map (fun (o, e) => (occurrenceIndex o, occurrenceIndex e)) := by
  simp only [exitsAt, NativeWalk.take_code, NativeWalk.flip_code, EdgeAugmenting.finish_eq]
  simp only [NativeWalk.edges_code, occurrences_eq_map_incidenceList, List.flatMap_map,
    List.filter_map, List.map_map, Function.comp_def, EdgeAugmenting.recordAt_index]
  simp only [← occurrences_eq_map_incidenceList, EdgeAugmenting.record_index, valid_pair_buffer]
  simp [Blossom.exitsAt, List.map_flatMap, List.map_map,
    Function.comp_def, Occurrence.record, List.contains_eq_mem, List.mem_map,
    (EdgeAugmenting.occurrenceIndex_injective F).eq_iff, Bool.beq_eq_decide_eq, Fin.val_inj,
    Bool.and_assoc]

/-- Preserve the unary prefix length and binary original port positions of a source exit. -/
@[expose] def exitCode {F : CSP Table ℕ} (e : Blossom.Exit F) : ExitCode :=
  ⟨e.length, occurrenceIndex e.input, occurrenceIndex e.output⟩

/-- The finite first-exit scan selects exactly the same whole prefix and ordered actual ports. -/
theorem firstExit_code {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool) (w r : Walk F) :
    firstExit ⟨F, (incidenceList F).map f⟩ (EdgeAugmenting.code w) (EdgeAugmenting.code r) =
      (Blossom.firstExit f w r).map exitCode := by
  simp only [firstExit, exitsAt_code, List.isEmpty_map,
    show (EdgeAugmenting.code r).steps.length = r.steps.length by simp [EdgeAugmenting.code]]
  split <;> rename_i hn
  · cases he : Blossom.exitsAt f w r _ <;> simp [Blossom.firstExit, hn, he, exitCode]
  · simp [Blossom.firstExit, hn]

/-- Actual prefix and reversed-suffix arm codes preserve every original copied step. -/
theorem armCandidates_code {F : CSP Table ℕ} (w : Walk F) (o : Occurrence F) :
    armCandidates F (EdgeAugmenting.code w) (occurrenceIndex o) =
      (Blossom.armCandidates w o).map EdgeAugmenting.code := by
  have hlen : (EdgeAugmenting.code w).steps.zipIdx.length = w.steps.length := by
    simp [EdgeAugmenting.code]
  unfold armCandidates Blossom.armCandidates
  rw [← List.ofFn_getElem (xs := (EdgeAugmenting.code w).steps.zipIdx)]
  simp only [hlen, List.ofFn_eq_map, List.flatMap_map, List.map_flatMap]
  refine congrArg ((List.finRange w.steps.length).flatMap ·) (funext fun j => ?_)
  have hget : (EdgeAugmenting.code w).steps.zipIdx[j.val]'(by simp [hlen]) =
      ((occurrenceIndex w.steps[j.val].1, occurrenceIndex w.steps[j.val].2), j.val) := by
    simp [EdgeAugmenting.code]
  simp only [Fin.val_cast, hget, EdgeAugmenting.recordAt_index, Occurrence.record, Fin.val_inj]
  split <;> simp_all [NativeWalk.inputArm, NativeWalk.outputArm, NativeWalk.take_code,
    NativeWalk.drop_code, NativeWalk.reverse_code, NativeWalk.snoc_code,
    Blossom.inputArm, Blossom.outputArm]

/-- Feasible-arm selection uses the exact current outside-prefix labeling. -/
theorem attachment_code {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool)
    (w : Walk F) (o : Occurrence F) :
    attachment ⟨F, (incidenceList F).map f⟩ (EdgeAugmenting.code w) (occurrenceIndex o) =
      (Blossom.attachmentWalk f w o).map EdgeAugmenting.code := by
  simp [attachment, armCandidates_code, List.find?_map, NativeWalk.flip_code,
    EdgeAugmenting.valid_eq, EdgeAugmenting.labeling_map, Blossom.attachmentWalk]

/-- Full finite first-exit/arm lifting has exactly the mathematical constructor's result. -/
theorem liftPrefix_code {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool) (w r : Walk F) :
    liftPrefix ⟨F, (incidenceList F).map f⟩ (EdgeAugmenting.code w) (EdgeAugmenting.code r) =
      (Blossom.liftPrefix f w r).map (fun g => (incidenceList F).map g) := by
  simp only [liftPrefix, firstExit_code]
  cases he : Blossom.firstExit f w r with
  | none => simp [Blossom.liftPrefix, he]
  | some e =>
    simp only [Option.map_some, Option.elim_some, exitCode, NativeWalk.take_code,
      NativeWalk.flip_code, attachment_code]
    cases ha : Blossom.attachmentWalk ((r.take e.length).flip f) w e.input <;>
      simp [Blossom.liftPrefix, he, ha, NativeWalk.flip_code]

/-- Native lifting has the exact source result in both connector cases. It restores every
surviving original port and executes the same shortest-prefix and actual-arm scans. -/
theorem liftWalk_code {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool) (w : Walk F)
    (p : Walk (Blossom.contract f (Blossom.internal w))) :
    liftWalk ⟨F, (incidenceList F).map f⟩ (EdgeAugmenting.code w) (EdgeAugmenting.code p) =
      (Blossom.liftWalk f w p).map (fun g => (incidenceList F).map g) := by
  have hhead : (EdgeAugmenting.code w).steps.head? =
      w.steps.head?.map (fun (a, b) => (occurrenceIndex a, occurrenceIndex b)) := by
    simp [EdgeAugmenting.code]
  unfold liftWalk
  rw [hhead]
  cases hw : w.steps with
  | nil => simp [Blossom.liftWalk, hw]
  | cons pair rest =>
    simp only [List.head?_cons, Option.map_some, Option.elim_some, NativeWalk.internal_code,
      Contraction.connectors_eq, Contraction.contract_eq, EdgeAugmenting.labeling_map]
    have hall : (NativeWalk.edges (EdgeAugmenting.code p)).all
        (fun i => !(Blossom.connectors F (Blossom.internal w)).contains
          (EdgeAugmenting.recordAt (Blossom.contract f (Blossom.internal w)) i).2.2) =
        p.edges.all (fun o => !(Blossom.connectors F (Blossom.internal w)).contains o.var) := by
      simp [NativeWalk.edges_code, List.all_map, Function.comp_def, EdgeAugmenting.recordAt_index,
        Occurrence.record]
    have hboundary :
        (EdgeAugmenting.code p).steps.findIdx (fun pair =>
          (Blossom.connectors F (Blossom.internal w)).contains
            (EdgeAugmenting.recordAt (Blossom.contract f (Blossom.internal w)) pair.2).2.2) =
        p.boundaryIndex (Blossom.connectors F (Blossom.internal w)) := by
      simp [EdgeAugmenting.code, List.findIdx_map, Walk.boundaryIndex, Function.comp_def,
        EdgeAugmenting.recordAt_index, Occurrence.record]
    rw [hall, hboundary]
    split <;> rename_i ha <;>
      simp only [restoreWalk_code, NativeWalk.take_code, NativeWalk.flip_code, liftPrefix_code,
        Blossom.liftWalk, hw, ha, ↓reduceIte, Option.map_some, Bool.false_eq_true]

/-- The full native comparison lifter agrees exactly with the mathematical constructor.
Every comparison bit, including every outside change, is retained by the bridge. -/
theorem liftComparison_code {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool) (w : Walk F)
    (g : OccurrenceLabeling (Blossom.contract f (Blossom.internal w)) Bool) :
    liftComparison ⟨F, (incidenceList F).map f⟩ (EdgeAugmenting.code w)
      ((incidenceList (Blossom.contract f (Blossom.internal w))).map g) =
      (Blossom.liftComparison f w g).map (fun h => (incidenceList F).map h) := by
  simp only [liftComparison, NativeWalk.internal_code, Contraction.connectors_eq,
    Contraction.contract_eq, Contraction.referenceRows_eq, EdgeAugmenting.labeling_map,
    Contraction.flatten_referenceRows]
  unfold Blossom.liftComparison
  by_cases h : Blossom.touched F (Blossom.internal w) = []
  · simp [h, Blossom.connectors]
  · have hs : (Blossom.connectors F (Blossom.internal w)).headD 0 =
        Blossom.baseConnector F (Blossom.internal w) h := by
      cases he : Blossom.touched F (Blossom.internal w) <;>
        simp_all [Blossom.connectors, Blossom.baseConnector]
    have hr := EdgeAugmenting.run_eq
      ⟨Blossom.contract f (Blossom.internal w),
        (incidenceList _).map (Blossom.reference f (Blossom.internal w)),
        (incidenceList _).map g, Blossom.baseConnector F (Blossom.internal w) h⟩
      (by simp) (by simp)
    simp only [EdgeAugmenting.labeling_map] at hr
    have hn : (Blossom.connectors F (Blossom.internal w)).isEmpty = false := by
      simp [Blossom.connectors, h]
    simp only [hn, Bool.false_eq_true, ↓reduceIte, h, ↓reduceDIte, hs, hr]
    cases EdgeInstance.augmentingWalk Table.sem (Blossom.reference f (Blossom.internal w)) g
        (Blossom.baseConnector F (Blossom.internal w) h) <;>
      simp [liftWalk_code]

end Cslib.Complexity.CSP.EdgeSolver.NativeLifting
