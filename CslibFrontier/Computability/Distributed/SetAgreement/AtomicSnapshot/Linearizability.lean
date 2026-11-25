/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Model
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Machine
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Trace
import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.TracePreservation
import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.LinearizationChunks

/-!
# Snapshot correctness and Herlihy–Wing linearizability (`Lemmas 3.2–3.3`, `Theorem 1`)

Proves the unbounded sequence-numbered single-writer snapshot interval and linearizability results
([AfekAttiyaDolevGafniMerrittShavit1993], Lemmas 3.2–3.3 and Theorem 1, pp. 9–10).

## Main results

* `Cslib.Distributed.SetAgreement.unbounded_exists_interval_snapshot_of_trace`: interval snapshot
  theorem (`Lemmas 3.2–3.3`).
* `Cslib.Distributed.SetAgreement.unbounded_snapshotLinearizable_of_reachable`: Herlihy–Wing
  linearizability for every reachable configuration (`Theorem 1`).
-/

public section

namespace Cslib.Distributed.SetAgreement

/-- Unbounded sequence-numbered single-writer step for #7504 (after
[Afek et al., Lemmas 3.2–3.3, pp. 9–10][AfekAttiyaDolevGafniMerrittShavit1993]): for every execution
trace `τ` and every completed `scan` record `(id, resp, snap)` in the final history
`(τ.stateAt τ.events.length).history`, there exists a state index `v` strictly inside the scan's
execution interval (`invStep < v ≤ resp`) at which the instantaneous shared-memory state
`memSnapshot (τ.stateAt v).reg` equals `snap`. -/
theorem unbounded_exists_interval_snapshot_of_trace {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} (τ : SnapshotTrace ord dInit)
    {id : ℕ} (hId : id < (τ.stateAt τ.events.length).history.length)
    {resp : ℕ} {snap : P → Data}
    (hdone : ((τ.stateAt τ.events.length).history[id]'hId).status = .doneScan resp snap) :
    let entry := (τ.stateAt τ.events.length).history[id]'hId
    entry.kind = .scan ∧ entry.invStep < resp ∧ resp < τ.events.length ∧
      ∃ v, entry.invStep + 1 ≤ v ∧ v ≤ resp ∧ memSnapshot (τ.stateAt v).reg = snap :=
  (τ.traceInv_holds τ.events.length le_rfl).hist_doneScan id hId resp snap hdone

/-- Internal trace-level proof of `unbounded_snapshotLinearizable_of_reachable`. -/
private theorem snapshotLinearizable_of_trace {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} (τ : SnapshotTrace ord dInit) :
    SnapshotLinearizable dInit (τ.stateAt τ.events.length).history := by
  set T := τ.events.length
  have inv := τ.traceInv_holds T le_rfl
  refine ⟨τ.linPrefix (T + 1), τ.nodup_linPrefix (T + 1), ?_, ?_, ?_,
    (τ.linPrefix_valid τ.traceInv_holds (T + 1) le_rfl).1⟩
  · -- Every linearized index is in bounds for `(τ.stateAt T).history`.
    intro x hx
    obtain ⟨t, -, hxt⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp hxt with hxt | hxt
    · exact ((τ.mem_linScansAt_iff t x).mp hxt).1
    · exact ((τ.mem_linUpdatesAt_iff t x).mp hxt).1
  · -- Every completed operation appears in some chunk `t < T + 1`.
    intro id hId hcomp
    simp only [SnapshotTrace.linPrefix, List.mem_flatMap, List.mem_range]
    cases hst : ((τ.stateAt T).history[id]'hId).status with
    | pending => simp only [SnapshotOpRecord.isCompleted, hst, Bool.false_eq_true] at hcomp
    | doneUpdate w =>
      obtain ⟨_, -, -, hw_lt, -⟩ := inv.hist_doneUpdate id hId w hst
      exact ⟨w, by omega, List.mem_append_right _ ((τ.mem_linUpdatesAt_iff w id).mpr ⟨hId, hst⟩)⟩
    | doneScan resp snap =>
      have hsc := inv.hist_doneScan id hId resp snap hst
      have hv_spec := τ.linScanPoint_spec hsc.2.2.2
      exact ⟨τ.linScanPoint ((τ.stateAt T).history[id]'hId).invStep resp snap,
        by have := hsc.2.2.1; omega,
        List.mem_append_left _ ((τ.mem_linScansAt_iff _ id).mpr ⟨hId, resp, snap, hst, rfl⟩)⟩
  · -- Real-time order: `t₁ < t₂` places `i` strictly before `j` in `linPrefix (T + 1)`.
    intro i hi j hj r hresp_i recJ hget_j hr_le
    obtain ⟨t₁, ht₁_lt, hi_chunk⟩ : ∃ t₁ < T + 1, i ∈ τ.linChunk t₁ := by
      simpa only [SnapshotTrace.linPrefix, List.mem_flatMap, List.mem_range] using hi
    obtain ⟨t₂, ht₂_lt, hj_chunk⟩ : ∃ t₂ < T + 1, j ∈ τ.linChunk t₂ := by
      simpa only [SnapshotTrace.linPrefix, List.mem_flatMap, List.mem_range] using hj
    have ht₁_lt_t₂ := τ.linChunk_lt_of_realTime inv hi_chunk hj_chunk hresp_i hget_j hr_le
    have hsplit_range : List.range (T + 1) = List.range t₂ ++ (List.range (T + 1)).drop t₂ :=
      (List.take_append_drop t₂ (List.range (T + 1))).symm.trans
        (by rw [List.take_range, Nat.min_eq_left (by omega)])
    have hseq_split : τ.linPrefix (T + 1) =
        (List.range t₂).flatMap τ.linChunk ++
          ((List.range (T + 1)).drop t₂).flatMap τ.linChunk := by
      dsimp only [SnapshotTrace.linPrefix]
      conv_lhs => rw [hsplit_range]; exact List.flatMap_append
    have hi_left : i ∈ (List.range t₂).flatMap τ.linChunk :=
      List.mem_flatMap.mpr ⟨t₁, List.mem_range.mpr ht₁_lt_t₂, hi_chunk⟩
    have hj_not_left : j ∉ (List.range t₂).flatMap τ.linChunk := by
      intro hj_in
      obtain ⟨t', ht'_lt, hj_t'⟩ := List.mem_flatMap.mp hj_in
      have heq := τ.eq_of_mem_linChunk hj_t' hj_chunk
      have := List.mem_range.mp ht'_lt
      omega
    rw [hseq_split, List.idxOf_append_of_mem hi_left, List.idxOf_append_of_notMem hj_not_left]
    exact lt_of_lt_of_le (List.idxOf_lt_length_of_mem hi_left) (Nat.le_add_right _ _)

/-- Unbounded sequence-numbered single-writer snapshot step for #7504 (after
[Afek et al., Theorem 1, p. 10][AfekAttiyaDolevGafniMerrittShavit1993]): every reachable
configuration `s` of `snapshotLTS ord dInit` has a linearizable operation history
`SnapshotLinearizable dInit s.history` against the canonical single-writer snapshot specification
(Section 4 bounded-register and Section 5 multi-writer snapshots remain open in #7504). -/
theorem unbounded_snapshotLinearizable_of_reachable {P Data : Type*} [Fintype P] [DecidableEq P]
    {ord : ScanOrder P} {dInit : Data} {s : SnapshotState P Data}
    (hreach : SnapshotReachable ord dInit s) :
    SnapshotLinearizable dInit s.history := by
  obtain ⟨tr, hmtr⟩ := hreach
  obtain ⟨τ, rfl, rfl⟩ := SnapshotTrace.of_mtr hmtr
  exact snapshotLinearizable_of_trace τ

end Cslib.Distributed.SetAgreement
