/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Params
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Program
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Model
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Defill
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Insert
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.ExtractMin
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Collect
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Standard

/-!
# Parametric Single-Heap Word-RAM Soft Heap

Single-heap Word-RAM soft-heap step toward #8624, after [Chazelle2000], Theorem 1.1 and
Section 5.1, Lemmas 5.1–5.2 (NECI TR 99-097 preprint, pp. 2, 12–13), and [PettieRamachandran2002],
Section 2.4, p. 19, Lemma 2.2 and Section 3.2, pp. 21–22, Figure 1 and Lemma 3.3. Supports `insert`,
`extractMin`, and `collectCorrupted` (without `meld` or arbitrary-handle `delete`) for arbitrary
corruption rank threshold `r : ℕ` and `rankThresholdForEps ε = Nat.log 2 (Nat.ceil (12 / ε)) + 1`
(`0 < ε : ℚ`), exported both as composable `Cslib.DataStructure.Memory.Prog` operations and as a
standalone flat deterministic width-blind `Cslib.WordRAM.Program .standard r` batch driver
(`SoftHeap.Standard`).

The dismantling-free binary-tree representation, `defill`
(`targetSize r k = 2 ^ ((k - r + 1) / 2)`), the `12 / 2 ^ r` `sizeCap` recurrence,
`rankThresholdForEps ε` for arbitrary `0 < ε : ℚ` (extending `[Chazelle2000]` Theorem 1.1's
`0 < ε ≤ 1 / 2` and `[PettieRamachandran2002]` Lemma 2.2's `0 < ε < 1 / 2`), and the `+(r : ℚ)`
baseline credit in `itemPhi` are this module's self-contained Word-RAM adaptation of
`[Chazelle2000]` toward `[PettieRamachandran2002]`.

## Cost model and scope

* **Composable `Memory.Prog` operations**: `allocPool`, `defill`, `shInsert`, `shExtractMin`, and
  `shCollectCorrupted` operate on caller-supplied bump-allocated pools (`SHHandle` with
  `rankThreshold`, `maxItems`, `maxNodes`), certifying `O(r + 1)` (`+ (240 * r + 520)`) amortized
  cost per insert, `O(1)` (`+ 250`) amortized cost per extract-min independently of `r`, and
  `≤ 8 * N` for corrupted-item collection alongside uniform `Realizes .exact` (`work := 0`)
  certificates.
* **Standalone `Program .standard r` driver**: `shBatchProg` hides `shFuelBound` and pool
  allocation internally and lowers via `exists_singleSoftHeap_batch_standard_program` and
  `exists_singleSoftHeap_batch_standard_program_eps` to a single fixed width-blind rand-free
  `Program .standard r` (`¬prog.ReadsWidth`, `prog.IsRandFree`) executing `N` insertions and `M`
  extract-mins from `State.init I.encode` under `Fits w I.wordBound` in
  `O(N * (r + 1) + M + 1)` (`O(N * (rankThresholdForEps ε + 1) + M + 1)`) native instructions with
  at most `12 * N / 2 ^ r` (`≤ ε * N`) corrupted items at every step.

## Main definitions

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.rankThresholdForEps`, `shFuelBound`:
  `ε`-derived corruption rank threshold and `shFuelBound r maxItems`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.targetSize`, `sizeCap`, `itemPhi`:
  parametric soft-heap rank parameters and exact closed-form item potential.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHHandle`, `SHExtractResult`, `SHInv`:
  handle, extraction result record, and full representation/amortized invariant.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.allocPool`, `defill`, `shInsert`,
  `shExtractMin`, `shCollectCorrupted`: memory-oracle Soft Heap operations with `Realizes .exact`
  certificates.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHOp`, `SHBatchInput`, `SHBatchResult`,
  `SHBatchExtract`, `SHBatchEntry`, `SHBatchStepRel`, `SHBatchTrace`, `shBatchProg`: flat batch I/O
  types, single-step transition relation, trace witness, and self-contained `Memory.Prog` driver.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.corrupt_sum_bound`,
  `rat_le_eps_mul_of_pow_mul_le`, `corrupt_sum_bound_eps`, `shInv_corrupted_le`,
  `shInv_corrupted_le_eps`: self-contained `12 / 2 ^ r` corruption bounds (`2 ^ r * #corrupted ≤
  12 * N`) and arbitrary rational `0 < ε` specialization.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHInv.origKey_le_ckey`,
  `SHBatchTrace.states_corrupted_bound`, `SHBatchTrace.states_corrupted_le_eps`: every surviving
  entry satisfies `origKey ≤ ckey`, with per-step corruption bounds and `ckey` monotonicity in
  `SHBatchStepRel`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.realizes_allocPool`, `realizes_defill`,
  `realizes_shInsert`, `realizes_shExtractMin`, `realizes_shCollectCorrupted`,
  `realizes_shBatchProg`: uniform `Realizes .exact` native compilation certificates.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.allocPool_spec`, `shInit_inv`, `defill_spec`,
  `shInsert_spec`, `shExtractMin_spec`, `shCollectCorrupted_spec`, `shBatchProg_spec`: full
  correctness, permutation, key-monotonicity, pool framing, and amortized `memoryCost` specs.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.exists_singleSoftHeap_batch_standard_program`,
  `exists_singleSoftHeap_batch_standard_program_eps`: single-heap batch step `Program .standard r`
  specifications toward `#8624`.

## References

* [B. Chazelle, *The Soft Heap: An Approximate Priority Queue with Optimal Error Rate*,
  Journal of the ACM 47(6), 2000][Chazelle2000], Theorem 1.1 and Section 5.1, Lemmas 5.1–5.2
  (NECI TR 99-097 preprint, pp. 2, 12–13).
* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree Algorithm*,
  Journal of the ACM 49(1), 2002][PettieRamachandran2002], Section 2.4, p. 19, Lemma 2.2 and
  Section 3.2, pp. 21–22, Figure 1 and Lemma 3.3.
-/
