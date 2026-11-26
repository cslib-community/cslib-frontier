/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.SmoothUnique
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.SmoothDiscrete
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.SmoothJohnsonIOP
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.SmoothJohnsonROM
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.BinaryUnique
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.BinaryDiscrete
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.BinaryJohnsonIOP
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.BinaryJohnsonROM

/-!
# Smooth & Binary Summed Batched FRI IOP Soundness, Closed-Form Bounds, and BCS-FRI ROM Composition

This facade re-exports the batched FRI soundness and BCS-FRI ROM composition modules
(`SmoothBridge`, `SmoothUnique`, `SmoothDiscrete`, `SmoothJohnsonIOP`, `SmoothJohnsonROM`,
`BinaryBridge`, `BinaryUnique`, `BinaryDiscrete`, `BinaryJohnsonIOP`, and `BinaryJohnsonROM`),
combining the round-`0` unweighted affine-word escape bounds of
`CslibFrontier.Crypto.Protocols.FRI.BatchSoundness` with the per-round telescoping degree-`(l⁽ⁱ⁾-1)`
curve folding budgets of `CslibFrontier.Crypto.Protocols.FRI.Soundness` and
`CslibFrontier.Crypto.Protocols.FRI.JohnsonSoundness` through the generic interactive IOP union
bounds `Cslib.Crypto.Protocols.BCS.iopCommitPhase_map_true_le_sum` and
`Cslib.Crypto.Protocols.BCS.iopInteractiveGame_le_sum`
(`CslibFrontier.Crypto.Protocols.BCS.Interactive`), yielding unconditional whole-protocol
commit-phase, interactive IOP, and adaptive two-channel BCS random-oracle soundness upper bounds
for the `(params.m + 2)`-round smooth batched FRI protocol
`Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP` (per-round folding arity `l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2`)
and its binary 2-to-1 specialization `Cslib.Crypto.Protocols.FRI.friBatchIOP` across the
unique-decoding, discrete Guruswami–Sudan, closed-form Johnson, and `η`-gap regimes
([BenSassonCarmonIshaiKoppartySaraf2020], accepted *Journal of the ACM* 2023 manuscript,
Section 8.2 on printed pp. 36–40 and Section 8.2.1 on printed pp. 41–43;
[BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).

## Scope and relationship to the source theorems

* **Lemma 8.2, Section 8.2.1, Theorem 8.3, and BCS ROM (`bcs16`):**
  In [BenSassonCarmonIshaiKoppartySaraf2020], **Lemma 8.2** (printed pp. 38–39, Eq. (8.5)) bounds
  the batched FRI commit-phase failure probability `ε_C` and is proved in **Section 8.2.1**
  (printed pp. 41–43) via the union bound over bad events `E⁽⁰⁾, E⁽¹⁾, …, E⁽ʳ⁾` (Eqs. (8.6)–(8.10)
  on printed p. 42) and telescoping across active domains (printed p. 43).
  **Theorem 8.3** (printed p. 39, proved on printed p. 40 by applying Lemma 8.2) combines commit
  failure `ε_C` with `q` independent query repetitions (`≤ α ^ q`) to obtain interactive IOP
  soundness `ε_C + α ^ q` for tuple correlated agreement `batchCorrAgreeLang t α`. Both Lemma 8.2
  and Theorem 8.3 are **interactive IOP theorems**; all `bcsSoundnessGame` results in this module
  are separate **two-channel BCS random-oracle compiler compositions**
  ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).
* **Round-`0` event vs. Section 8.2.1 `E⁽⁰⁾` (defined before Eq. (8.8)), cutoffs, and `t = 0`:**
  Section 8.2.1 (printed pp. 41–42) defines the round-`0` bad event `E⁽⁰⁾` **immediately before
  Eq. (8.8)**—while Eq. (8.8) bounds its probability—via `μ⁽⁰⁾`-weighted agreement of the reported
  oracle `f⁽⁰⁾` strictly above `α⁽⁰⁾(ρ, m) = max(α, √ρ · (1 + 1 / (2 * m)))`, where `μ⁽⁰⁾(s) = 1`
  only where `f⁽⁰⁾(s) = stmt.eval x s` and `0` otherwise. High `μ⁽⁰⁾`-weighted agreement of `f⁽⁰⁾`
  implies at least as much unweighted agreement of `stmt.eval x`, whereas reporting
  `f⁽⁰⁾ ≠ stmt.eval x` everywhere makes `μ⁽⁰⁾ ≡ 0` and shows why the reverse implication can fail
  (in Lean's round ordering, `x = c₀.batchCoeffs` is sampled in round `0` before `f⁽⁰⁾` is chosen in
  round `1`, and `friSmoothDoomed` absorbs any discrepancy `f⁽⁰⁾ ≠ stmt.eval x` via
  `sum_agree_friSmoothOracleFilterWeight_le`). Containment therefore depends on comparing cutoffs:
  - For integer parameters `n = 2 ^ d`, `B = n - e - 1`, and `stmt ∉ params.batchProximityLang t e`,
    Lean's unweighted `stmt.eval x` round-`0` event (`> B / n`) contains `E⁽⁰⁾` whenever
    `B / n ≤ α⁽⁰⁾(ρ, m)` (general integer `(e, α, m)` cutoffs can differ, e.g. at `n = 16, k = 4,
    e = 7, α = 1 / 2, m = 3` where `> 8 / 16` admits nine positions while `> 7 / 12` starts at ten).
  - In the real-`α` commit-phase bounds (`> ⌊α₀ * 2 ^ d⌋₊`, bridged to integer proximity via
    `friBatchFloorThreshold_bounds` from `BatchProtocol.lean`),
    `friSmoothBatchCommitGame_le_of_johnson` uses `α₀ = max(α, √ρ · (1 + 1 / (2 * mJ)))`, so at
    matching Johnson multiplicity `mJ = m` (or whenever `m ≤ mJ`) the cutoffs satisfy
    `α₀ ≤ α⁽⁰⁾(ρ, m)` and Lean's unweighted round-`0` event **unconditionally contains** `E⁽⁰⁾`.
  - By contrast, `friSmoothBatchCommitGame_le_of_unique` uses `α₀ = max(α, (1 + ρ) / 2)` and
    contains `E⁽⁰⁾` under the explicit condition `(1 + ρ) / 2 ≤ α⁽⁰⁾(ρ, m)` (failing in general when
    `(1 + ρ) / 2 > α⁽⁰⁾(ρ, m)`: on `𝔽₁₇ˣ` with `n = 16, k = 4, α = 1 / 2, m = 3`, the paper's cutoff
    is `7 / 12` while the unique-decoding cutoff is `5 / 8`, and setting the base word to `0` on
    `10` positions and `X⁴` on `6` positions with direction `X⁴` satisfies common agreement
    `≤ 4 ≤ 8` yet, at batching scalar `0` with reported oracle equal to the base word so all weights
    are `1`, achieves `10` agreeing positions—clearing `7 / 12` while missing strict `> 5 / 8`).
    Likewise, `friSmoothBatchCommitGame_le_of_johnson_eta` uses `α₀ = max(α, √ρ + η)` and contains
    `E⁽⁰⁾` under the explicit condition `√ρ + η ≤ α⁽⁰⁾(ρ, m)` (for example when `η ≤ √ρ / (2 * m)`
    or `√ρ + η ≤ α`).
  All `t`-uniform theorems state **probability upper bounds** (at `t = 0`, `stmt.eval x = stmt.base`
  is independent of `x` and has round-`0` escape probability `0`).
* **Query schedules and read budgets:**
  `params.proofOracleQueries = kFinal + q * (aritySum + m + 2)` (`length_friSmoothBatchIOP_queries`,
  specializing to `kFinal + q * (3 * m + 2)` at `l⁽ⁱ⁾ = 2`) is the exact committed-proof-oracle
  opening list length (so verifier Merkle cost `q_V = params.proofOracleQueries * (L_path + 1)` is
  independent of `t`), while `friSmoothBatchInputQueries` is the `q`-position direct-read schedule
  and `batchInputWordReads t = (t + 1) * q` /
  `batchTotalWordQueries t = kFinal + q * (aritySum + m + t + 3)` are direct-read and combined
  word-query **budgets** (as an execution can reject early).
* **Original explicit Siegel constants, direct `η`, and smooth `2 ^ stepLog i`-to-1 folding:**
  `friSmoothBatchJohnsonCommitError`
  (`(2 - 1 / 2 ^ totalLog) * 1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / (ρ * |F|)`) and
  `friSmoothBatchJohnsonEtaCommitError`
  (`(2 - 1 / 2 ^ totalLog) * 115200 * (2 ^ d) ^ 2 / (ρ * η ^ 6 * |F|)`, using `η` directly rather
  than `min(η, √ρ / 20)` in Eq. (1.3)) are this library's **original explicit Siegel finite bounds**
  for smooth per-round folding arity `l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2` (specializing to binary `l⁽ⁱ⁾ = 2`
  with `(2 - 1 / 2 ^ m)` via `FRIParams.toSmooth`; `mJ ≥ 1` vs. the paper's `m ≥ 3`), not uniformly
  smaller at small `mJ` than the displayed `(m + 1 / 2) ^ 7 / (2 * ρ ^ (3 / 2))` +
  `(2 * m + 1) * (|D⁰| + 1) / √ρ · ∑ l⁽ⁱ⁾` expressions of JACM Lemma 8.2 / Theorem 8.3. Exact
  correspondence with the paper's displayed constants remains open on `#5968`.

## Main definitions

* `Cslib.Crypto.Protocols.FRI.friSmoothBatchRoundEscape`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchSumError`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchFinalPasses`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame` (and binary counterparts
  `friBatchRoundEscape`, `friBatchSumError`, `friBatchFinalPasses`, `friBatchCommitGame`).
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchUniqueCommitError`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchJohnsonCommitError`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchJohnsonEtaCommitError`: closed-form
  `(2 - 1 / 2 ^ totalLog)` smooth batched commit-phase error bounds (and binary `(2 - 1 / 2 ^ m)`
  counterparts `friBatchUniqueCommitError`, `friBatchJohnsonCommitError`,
  `friBatchJohnsonEtaCommitError`).

## Main results

* `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitRound_escape_le_of_weightedCurveEscapePerRound`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_le_of_escape`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_le_of_escape` (and binary
  corollaries).
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_proximity_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_le_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_proximity_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_proximity_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_le_of_johnson_eta`: unconditional integer-`e`
  and real-`α` (`⌊α₀ * 2 ^ d⌋₊`) smooth batched commit-phase upper bounds in the setting of
  Lemma 8.2 (with binary corollaries).
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_proximity_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_le_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_sound_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_sound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_sound_of_johnson_eta`: unconditional smooth
  interactive batched FRI soundness bounds and contrapositives in the setting of Theorem 8.3 (with
  binary corollaries).
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_romSoundness_bound_of_unique`,
  `FRI.friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_corrAgree_romSoundness_bound_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_romSoundness_bound_of_johnson_discrete`,
  `FRI.friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_romSoundness_bound_of_johnson`,
  `FRI.friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_romSoundness_bound_of_johnson_eta`,
  `FRI.friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchBCS_corrAgree_romSoundness_bound_of_johnson`,
  `FRI.friSmoothBatchBCS_corrAgree_romSoundness_bound_of_prover_verifier_of_johnson`: adaptive
  two-channel smooth batched BCS-FRI ROM soundness bounds (with binary corollaries).

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev, *Fast Reed–Solomon Interactive Oracle Proofs
  of Proximity*][BenSassonBentovHoreshRiabzev2018]
* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
-/
