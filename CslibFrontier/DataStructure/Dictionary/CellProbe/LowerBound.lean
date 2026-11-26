/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.CellProbe.OuterGame
public import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.Base
public import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.ModifiedInner
public import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.Query
public import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.Update

/-!
# Multi-Level Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries

End-to-end cell-probe lower bounds for dynamic succinct dictionaries from Li, Liang, Yu, and Zhou
([LiLiangYuZhou2023]; locators below follow `arXiv:2306.02253v3`, where printed page `p` is PDF
page `p + 1`):

* **Section 8.1 Modified Inner Game (Lemma 8.1, pp. 28–30 / PDF pp. 29–31):** query-free inner
  communication protocol recovering `(K \ D, v_{A ∪ B}, v_K)` from `(a, b, d)` via `C_mix` and
  `C_B`, yielding both the update-only `OuterLemma` (`outer_lemma_insertDelete`) and large-value
  coverage (`V > U ^ 3`) for the query-inclusive bounds (`outer_lemma_largeVal_insertQueryDelete`).
* **Theorem 1.1 / Theorem 3.1 (pp. 1, 10–13 / PDF pp. 2, 11–14):** `Ω(k)` amortized cell probes
  under `R ≤ O(n log^{(k)} n)` bits of redundancy (`1 ≤ k ≤ log* n`), specializing at `k = log* n`
  to `Ω(log* n)` expected probes per operation for `R = O(n)`.
* **Theorem 1.2 / Theorem 6.1 (pp. 2, 25–26 / PDF pp. 3, 26–27):** `Ω(log(n / max R 1))` amortized
  cell probes for `R`-redundancy dynamic dictionaries (`0 ≤ R ≤ n`), together with the combined
  `Ω(log* n + log(n / max R 1))` trade-off across `0 ≤ R ≤ O(n)` and all `V ≥ 1` (Section 7,
  pp. 26–27 / PDF pp. 27–28).
* **Theorem 1.3(1)–(2) (pp. 2, 27–30 / PDF pp. 3, 28–31):** update-only `Ω(k)` and
  `Ω(log(n / max R 1))` cell-probe lower bounds on `insertDeleteDist` for `U ≥ 3 * n` and
  `V ≥ U ^ (2 + α_V) / n ^ 2` without any query-time constraint.

Original formalization adaptations of [LiLiangYuZhou2023] (`arXiv:2306.02253v3`):
1. **Deterministic `c = 1` probe cap (`Sections 4.2, 5.1, 5.2, and 8.1`):** `IsModeSeedConsistent`
   enforces `|S_A|, |S_B| ≤ m * t` directly inside the consistency event (incurring
   `≤ (1 / 16) * λ_{ℓ+1}` probe-cap loss via Markov's inequality on `nodeProbes` in
   `MetaTree.sum_prob_not_isGoodSeg_le`), so Step 5 of Lemma 8.1 encodes `S_A ∩ S_B ⊆ S_B` and
   `Diff ⊆ S_A ∩ S_B` in `≤ 2 * m * t` bits deterministically on every consistent outcome without
   conditional expectation inflation on `{W = 1}`.
2. **Internal Markov sub-conditioning in Step 6 (`Section 8.1`):** to encode `C_B` prefix-freely
   within its decoded dictionary fiber `stateFiber` on `{W = 1}`, Lemma 8.1 sub-conditions on
   `c(T_B) ≤ 2 ^ (R + 1) * U ^ (γ * m)` over the uniform marginal of `T_B` (`Pr[bad] ≤
   (1 / 2) * U ^ (-γ * m)`), costing `R + 2 + γ * m * log₂ U` bits in Step 6 and tightening Lemma
   8.1's value budget by `2 * γ * m * log₂ U` while leaving Theorem 1.3's asymptotic hypothesis
   `V ≥ U ^ (2 + α_V) / n ^ 2` unchanged (choosing `(5 + c_w) * γ ≤ min (1 / 4) (α_V / 16)`).
3. **Public deterministic `IndexedScheme` endpoints (`Section 3`):** every headline theorem is
   exported first for deterministic step-indexed schemes `D_det : CellProbe.IndexedScheme ...` exact
   on `validHistoriesUpTo`, followed by its zero-error `CellProbe.Randomized.Scheme` corollary via
   Yao coin-fixing (`exists_det_indexedScheme_insertQueryDeleteDist` /
   `exists_det_indexedScheme_insertDeleteDist`).

Model and boundary conventions:
* **Zero-error oblivious randomization:** randomized lower bounds (`expectedSeqProbes_*`) apply to
  zero-error (Las Vegas) `CellProbe.Randomized.Scheme`s on oblivious operation distributions;
  bounded-error (Monte Carlo) schemes and adaptive sequence adversaries are out of scope.
* **Trailing `+ 1` correctness horizon (`4 * n + 1` and `3 * n + 1`):** on `insertDeleteDist`
  (`3 * n` update steps returning `PUnit`), requiring correctness up to length `3 * n + 1` ensures
  one trailing admissible `.query` step can witness `decodeDict` at every step `≤ 3 * n` while
  charging probes only on the `3 * n` update sequence itself.
* **`R = n` boundary in Theorem 1.2 / 1.3(2):** at `R = n` (`n ≥ 1`), `log₂(n / max R 1) = 0`, so
  the standalone sublinear-redundancy bounds reduce to `0 ≤ E[seqProbes]`; the `Ω(n * log* n)` and
  combined `Ω(n * (log* n + log₂(n / max R 1)))` theorems supply the active lower bound for
  `R = Θ(n)`.

The formalization is organized into focused submodules under
`CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound`:

* `LowerBound.CandidateReplay`: `stateFiber` and candidate segment replay (`modeCandidateOps`).
* `LowerBound.PoolSymmetry`: `actSeed8Equiv` symmetry, `pairBOf` uniformity, and Markov fiber cap.
* `LowerBound.TargetFiber`: `(obs8, target8)` stabilizer-orbit fiber upper bound.
* `LowerBound.PrefixMessage`: six-piece prefix-free message proof (`prob_queryFreePool_eq_le`).
* `LowerBound.ModifiedInner`: public Section 8.1 endpoints (`queryFreeInnerDist`, Lemma 8.1,
  `outer_lemma_insertDelete`, `outer_lemma_largeVal_insertQueryDelete`).
* `LowerBound.Base`: `optBits` bridges, base `Ω(n)` bound, and multi-level `MetaTree` aggregation.
* `LowerBound.TreeParams`: numeric inequalities, `NodeOuterHyp`, `iterLog` tree bounds, and Yao
  lifting wrappers (independent of Section 8.1).
* `LowerBound.ModeBounds`: generic `withQueries : Bool` `iterLog` and sublinear-redundancy bounds.
* `LowerBound.Query`: public insert-query-delete lower bounds (Theorems 1.1 and 1.2).
* `LowerBound.Update`: public update-only lower bounds (Theorem 1.3).

## Main definitions

* `Cslib.DataStructure.Dictionary.CellProbe.queryFreeInnerDist`: conditional `(seed, B)`
  distribution for the query-free inner game of Section 8.1 (Lemma 8.1).

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.prob_isModeSeedConsistent_queryFreeInnerDist_le`,
  `Cslib.DataStructure.Dictionary.CellProbe.expected_card_modeConsistent_segmentRest_lt_half_le`,
  `Cslib.DataStructure.Dictionary.CellProbe.outer_lemma_insertDelete`,
  `Cslib.DataStructure.Dictionary.CellProbe.outer_lemma_largeVal_insertQueryDelete`: Lemma 8.1 and
  the update-only and large-value Outer Lemmas.
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_linear`,
  `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_of_outer_tree`,
  `Cslib.DataStructure.Dictionary.CellProbe.optBits_le_benchmarkBits_add`,
  `Cslib.DataStructure.Dictionary.CellProbe.optBits_two_pow_le_benchmarkBits_add_one`: base `Ω(n)`
  bound, multi-level `MetaTree` probe aggregation, and `Dynamic.optBits` bridges.
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_of_iterLog_redundancy`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_of_iterLog_redundancy`,
  `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_iterLogStar`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_iterLogStar`: Theorem 1.1 / 3.1.
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_of_sublinear_redundancy`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_of_sublinear_redundancy`,
  `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_ge_iterLogStar_add_log_div`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_ge_iterLogStar_add_log_div`:
  Theorem 1.2 / 6.1 and combined `Ω(log* n + log(n / max R 1))` bound.
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_iterLog`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_iterLog`,
  `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_iterLogStar`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_iterLogStar`,
  `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_sublinear`,
  `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_sublinear`:
  Theorem 1.3(1)–(2).
* `Cslib.DataStructure.Dictionary.CellProbe.det_expectedSeqProbes_update_ge_iterLogStar_add_log_div`
* `Cslib.DataStructure.Dictionary.CellProbe.expectedSeqProbes_update_ge_iterLogStar_add_log_div`:
  combined update-only trade-off.

## References

* [T. Li, J. Liang, H. Yu and R. Zhou, *Tight Cell-Probe Lower Bounds for Dynamic Succinct
  Dictionaries*][LiLiangYuZhou2023], Sections 1, 3, 4.2, 5.1, 5.2, 6, 7, and 8
  (`arXiv:2306.02253v3`).
* [M. L. Fredman and M. E. Saks, *The cell probe complexity of dynamic data
  structures*][FredmanSaks1989]
* [P. B. Miltersen, *Cell Probe Complexity — a Survey*][Miltersen1999]
* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
-/
