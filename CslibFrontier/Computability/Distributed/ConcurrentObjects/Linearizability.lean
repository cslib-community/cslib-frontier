/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.Basic
public import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.Locality
public import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.Nonblocking
public import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.Register

/-!
# Herlihy–Wing linearizability, sequential consistency, and locality

This module re-exports the concurrent object linearizability development across focused topic
modules:

* `Linearizability.Basic`: concurrent invocation/response histories over multiple typed shared
  objects, process and object subhistory projections (`History.procSubhistory`,
  `History.objSubhistory`), sequential and well-formed histories, `History.complete`, response
  extensions (`History.IsExtension`), real-time operation precedence (`History.prec`), sequential
  specifications (`SeqSpec`, `SeqSpec.ofMachine`, `SeqSpec.IsTotalOp`), `IsLinearizable`,
  `IsSequentiallyConsistent`, and `IsLinearizable.isSequentiallyConsistent` ([HerlihyWing1990],
  §§2.1–2.2, §3.3, pp. 467–472; [SelaHerlihyPetrank2021], §4, Definition 4.1, p. 6).
* `Linearizability.Locality`: `History.prec_append_resp_iff`, algebraic interval-order cycle
  collapse (`acyclic_sup_of_isIntervalOrder`), and **Herlihy–Wing Theorem 1 (Locality)**
  (`IsLinearizable.objSubhistory`, `isLinearizable_iff_forall_obj`; [HerlihyWing1990], §3.1,
  Theorem 1, pp. 470–471; [SelaHerlihyPetrank2021], §5.2, Theorem 5.1, pp. 7–9).
* `Linearizability.Nonblocking`: incremental pending-operation extension lemmas
  (`History.append_pending_inv_extension`, `History.linearize_pending_in_extension`,
  `History.flush_resp_from_extension`) and **Herlihy–Wing Theorem 2 (Nonblocking)**
  (`exists_linearizable_append_resp_of_total`; [HerlihyWing1990], §3.2, Theorem 2, pp. 471–472;
  [SelaHerlihyPetrank2021], §5.3, Theorem 5.2, p. 9).
* `Linearizability.Register`: atomic read/write register specification (`RegOp`, `RegResp`,
  `registerStep`, `registerSeqSpec`) and explicit register counterparts of `H_7` and `H_8`
  (`exists_sequentiallyConsistent_not_linearizable`, `exists_obj_sequentiallyConsistent_not_global`;
  [HerlihyWing1990], §3.3, p. 472).

## References

* [M. P. Herlihy, J. M. Wing, *Linearizability: A Correctness Condition for Concurrent
  Objects*][HerlihyWing1990]
* [G. Sela, M. Herlihy, E. Petrank, *Brief Announcement: Linearizability: A
  Typo*][SelaHerlihyPetrank2021]
-/
