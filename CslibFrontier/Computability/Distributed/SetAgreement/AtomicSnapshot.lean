/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Model
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Machine
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.WaitFree
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Trace
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.CleanCollect
public import CslibFrontier.Computability.Distributed.SetAgreement.AtomicSnapshot.Linearizability

/-!
# Wait-free single-writer atomic snapshot memory

As an unbounded sequence-numbered single-writer step toward `#7504`, this module formalizes the
unbounded wait-free single-writer atomic snapshot algorithm of Afek, Attiya, Dolev, Gafni, Merritt,
and Shavit ([AfekAttiyaDolevGafniMerrittShavit1993], §§2.1, 3, Figures 1 and 3, Lemmas 3.1–3.4, and
Theorem 1; author PDF pp. 4–10, JACM 40(4):873–890).

Each process `i : P` owns a single-writer, multi-reader (`SWMR`) atomic register
`SnapshotReg P Data` holding `(data, seq, view)` (initialized to `(dInit, 0, fun _ => dInit)`).
Crucially, `collect` is **not** modeled as an atomic multi-register read: each step of `collectA`
or `collectB` reads **one** register `s.reg j` at a time along a `ScanOrder P`, allowing arbitrary
interleaved reads, writes, invocations, and crashes by other processes between any two register
reads. Relative to Figure 1 (p. 4) and §3.1 (pp. 7–8), which separate internal `Scan_i` /
`Update_i(d)` transitions from external `ScanReturn_i` / `UpdateReturn_i` outputs, `stepSnapshot`
fuses `scan_i`'s final local decision (`finishScan`) with `.doneScan` and fuses `update_i`'s atomic
register write (`readyToWrite`) with `.doneUpdate`.

* **Operations (`Figure 3`):**
  - `scan_i`: maintains `moved : Finset P` (initialized to `∅`) and repeatedly performs two
    sequential single-register-at-a-time collects `a` (`collectA`) and `b` (`collectB`). If
    `∀ j, (a j).seq = (b j).seq`, it returns `fun j => (b j).data` (successful double collect).
    Otherwise, if some process `j` with `(a j).seq ≠ (b j).seq` already belongs to `moved`
    (observed moving twice), `scan_i` borrows and returns `(b j).view`; otherwise all processes
    whose sequence numbers changed are added to `moved` and the loop repeats.
  - `update_i(val)`: executes an embedded `scan_i` to obtain a snapshot `snap`, then performs a
    single atomic write `reg i := ⟨val, (reg i).seq + 1, snap⟩`.
* **Correctness and Linearizability (`Lemmas 3.1–3.3`, `Theorem 1`, steps toward `#7504`):**
  - `SnapshotTrace.memSnapshot_eq_of_clean_double_collect` (after Lemma 3.1): if `a` and `b`
    observe identical sequence numbers across all registers, no register was written between its
    `collectA` read and its `collectB` read, so `fun j => (b j).data` equals the instantaneous
    memory state throughout the interval between the two collects.
  - `unbounded_exists_interval_snapshot_of_trace` (after Lemmas 3.2–3.3): if `scan_i` observes `j`
    move in two distinct double collects, the `update_j` that wrote the second value began strictly
    after `scan_i` started and wrote before `scan_i` finished, so its embedded view is already a
    valid snapshot inside `scan_i`'s interval; hence every completed `scan` returns `memSnapshot` at
    some historical state inside its execution interval.
  - `unbounded_snapshotLinearizable_of_reachable` (after Theorem 1): every reachable execution
    history of the unbounded sequence-numbered single-writer algorithm is Herlihy–Wing linearizable
    against the canonical single-writer snapshot sequential specification (`Figure 1`).
* **Wait-Free `O(n²)` Step Complexity (`Lemma 3.4`):**
  - Because `#moved` strictly increases on every unsuccessful double-collect iteration and is
    bounded by `n = Fintype.card P`, at most `n + 1` iterations occur. The per-process potential
    `remainingSteps` is at most `(2n + 2)(n + 1) + 1 = 2n² + 4n + 3` (`O(n²)`, with at most
    `2n(n + 1)` shared-register reads and at most `1` shared-register write), strictly decreases on
    every step of `i`, and is invariant under all steps of `j ≠ i`, yielding unconditional solo and
    concurrent wait-free termination (`exists_solo_completion`).

### Scope note

This module formalizes the **unbounded** sequence-numbered single-writer construction as a step
toward `#7504` (after [AfekAttiyaDolevGafniMerrittShavit1993], §3, Theorem 1). Their
bounded-register toggle/handshake single-writer (§4, Theorem 2) and multi-writer (§5, Theorem 3)
constructions remain open in `#7504`.

## Main definitions

* `Cslib.Distributed.SetAgreement.SnapshotReg`, `Cslib.Distributed.SetAgreement.memSnapshot`:
  single-writer `(data, seq, view)` register and instantaneous global data vector.
* `Cslib.Distributed.SetAgreement.ScanOrder`, `Cslib.Distributed.SetAgreement.ScanOrder.fin`:
  duplicate-free register collect order covering `P`.
* `Cslib.Distributed.SetAgreement.SnapshotOpKind`,
  `Cslib.Distributed.SetAgreement.SnapshotOpStatus`,
  `Cslib.Distributed.SetAgreement.SnapshotOpRecord`: client `scan` / `update` operations and
  execution history records.
* `Cslib.Distributed.SetAgreement.ScanMode`, `Cslib.Distributed.SetAgreement.CollectPhase`,
  `Cslib.Distributed.SetAgreement.ActiveScan`, `Cslib.Distributed.SetAgreement.ProcSnapshotState`,
  `Cslib.Distributed.SetAgreement.SnapshotState`, `Cslib.Distributed.SetAgreement.SnapshotEvent`:
  operational process states, global configurations, and atomic single-register LTS events.
* `Cslib.Distributed.SetAgreement.snapshotLTS`, `Cslib.Distributed.SetAgreement.SnapshotTrace`:
  labelled transition system and execution traces from `SnapshotState.init`.
* `Cslib.Distributed.SetAgreement.seqSnapshotValid`,
  `Cslib.Distributed.SetAgreement.IsSnapshotLinearization`,
  `Cslib.Distributed.SetAgreement.SnapshotLinearizable`: sequential canonical single-writer
  snapshot semantics and Herlihy–Wing linearizability.
* `Cslib.Distributed.SetAgreement.remainingSteps`,
  `Cslib.Distributed.SetAgreement.remainingRegOps`: per-process wait-free step and shared-register
  operation potentials (`O(n²)`).

## Main results

* `Cslib.Distributed.SetAgreement.SnapshotTrace.memSnapshot_eq_of_clean_double_collect`: unbounded
  clean double-collect step (after Lemma 3.1).
* `Cslib.Distributed.SetAgreement.unbounded_exists_interval_snapshot_of_trace`: unbounded interval
  snapshot step (after Lemmas 3.2–3.3).
* `Cslib.Distributed.SetAgreement.unbounded_snapshotLinearizable_of_reachable`: unbounded
  single-writer snapshot linearizability step (after Theorem 1).
* `Cslib.Distributed.SetAgreement.remainingSteps_le_quad`,
  `Cslib.Distributed.SetAgreement.remainingRegOps_invokeScan`,
  `Cslib.Distributed.SetAgreement.remainingRegOps_invokeUpdate`,
  `Cslib.Distributed.SetAgreement.remainingSteps_lt_of_step`,
  `Cslib.Distributed.SetAgreement.remainingSteps_eq_of_other`,
  `Cslib.Distributed.SetAgreement.exists_solo_completion`: wait-free `O(n²)` step and
  register-access bounds (after Lemma 3.4).

## References

* [Y. Afek, H. Attiya, D. Dolev, E. Gafni, M. Merritt, N. Shavit, *Atomic Snapshots of Shared
  Memory*][AfekAttiyaDolevGafniMerrittShavit1993]
-/
