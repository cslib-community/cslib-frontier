/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.BatchSoundness
public import CslibFrontier.Crypto.Protocols.FRI.JohnsonSoundness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Summed Batched FRI IOP Soundness, Closed-Form Commit Bounds, and BCS-FRI ROM Composition

This module combines the round-`0` unweighted affine-word escape bounds of
`CslibFrontier.Crypto.Protocols.FRI.BatchSoundness` with the per-round geometric folding budgets of
`CslibFrontier.Crypto.Protocols.FRI.Soundness` and
`CslibFrontier.Crypto.Protocols.FRI.JohnsonSoundness` through the generic interactive IOP union
bounds `Cslib.Crypto.Protocols.BCS.iopCommitPhase_map_true_le_sum` and
`Cslib.Crypto.Protocols.BCS.iopInteractiveGame_le_sum`
(`CslibFrontier.Crypto.Protocols.BCS.Interactive`),
yielding unconditional whole-protocol commit-phase, interactive IOP, and adaptive two-channel BCS
random-oracle soundness upper bounds for the `(params.m + 2)`-round batched 2-to-1 FRI protocol
`Cslib.Crypto.Protocols.FRI.friBatchIOP` across the unique-decoding, discrete Guruswami–Sudan,
closed-form Johnson, and `η`-gap regimes ([BenSassonCarmonIshaiKoppartySaraf2020], accepted
*Journal of the ACM* 2023 manuscript, Section 8.2 on printed pp. 36–40 and Section 8.2.1 on printed
pp. 41–43; [BenSassonChiesaSpooner2016]; [ChiesaYogev2024]).

## Scope and relationship to the source theorems

* **Lemma 8.2, Section 8.2.1, Theorem 8.3, and BCS ROM (`bcs16`):**
  In [BenSassonCarmonIshaiKoppartySaraf2020], **Lemma 8.2** (printed pp. 38–39, Eq. (8.5)) bounds
  the batched FRI commit-phase failure probability `ε_C` and is proved in **Section 8.2.1**
  (printed pp. 41–43) via the union bound over bad events `E⁽⁰⁾, E⁽¹⁾, …, E⁽ʳ⁾` (Eqs. (8.6)–(8.10)
  on printed p. 42) and geometric telescoping across active domains (printed p. 43).
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
  round `1`, and `friDoomed` absorbs any discrepancy `f⁽⁰⁾ ≠ stmt.eval x` via
  `sum_agree_friOracleFilterWeight_le`). Containment therefore depends on comparing cutoffs:
  - For integer parameters `n = 2 ^ d`, `B = n - e - 1`, and `stmt ∉ params.batchProximityLang t e`,
    Lean's unweighted `stmt.eval x` round-`0` event (`> B / n`) contains `E⁽⁰⁾` whenever
    `B / n ≤ α⁽⁰⁾(ρ, m)` (general integer `(e, α, m)` cutoffs can differ, e.g. at `n = 16, k = 4,
    e = 7, α = 1 / 2, m = 3` where `> 8 / 16` admits nine positions while `> 7 / 12` starts at ten).
  - In the real-`α` commit-phase bounds (`> ⌊α₀ * 2 ^ d⌋₊`, bridged to integer proximity via
    `batchFloorThreshold_bounds` from `BatchProtocol.lean`), `friBatchCommitGame_le_of_johnson` uses
    `α₀ = max(α, √ρ · (1 + 1 / (2 * mJ)))`, so at matching Johnson multiplicity `mJ = m` (or
    whenever `m ≤ mJ`) the cutoffs satisfy `α₀ ≤ α⁽⁰⁾(ρ, m)` and Lean's unweighted round-`0` event
    **unconditionally contains** `E⁽⁰⁾`.
  - By contrast, `friBatchCommitGame_le_of_unique` uses `α₀ = max(α, (1 + ρ) / 2)` and contains
    `E⁽⁰⁾` under the explicit condition `(1 + ρ) / 2 ≤ α⁽⁰⁾(ρ, m)` (failing in general when
    `(1 + ρ) / 2 > α⁽⁰⁾(ρ, m)`: on `𝔽₁₇ˣ` with `n = 16, k = 4, α = 1 / 2, m = 3`, the paper's cutoff
    is `7 / 12` while the unique-decoding cutoff is `5 / 8`, and setting the base word to `0` on
    `10` positions and `X⁴` on `6` positions with direction `X⁴` satisfies common agreement
    `≤ 4 ≤ 8` yet, at batching scalar `0` with reported oracle equal to the base word so all weights
    are `1`, achieves `10` agreeing positions—clearing `7 / 12` while missing strict `> 5 / 8`).
    Likewise, `friBatchCommitGame_le_of_johnson_eta` uses `α₀ = max(α, √ρ + η)` and contains `E⁽⁰⁾`
    under the explicit condition `√ρ + η ≤ α⁽⁰⁾(ρ, m)` (for example when `η ≤ √ρ / (2 * m)` or
    `√ρ + η ≤ α`).
  All `t`-uniform theorems state **probability upper bounds** (at `t = 0`, `stmt.eval x = stmt.base`
  is independent of `x` and has round-`0` escape probability `0`).
* **Query schedules and read budgets:**
  `params.proofOracleQueries = kFinal + q * (3 * m + 2)` (`length_friBatchIOP_queries`) is the
  exact committed-proof-oracle opening list length (so verifier Merkle cost
  `q_V = params.proofOracleQueries * (L_path + 1)` is independent of `t`), while
  `friBatchInputQueries` is the `q`-position direct-read schedule and
  `batchInputWordReads t = (t + 1) * q` / `batchTotalWordQueries t = kFinal + q * (3 * m + t + 3)`
  are direct-read and combined word-query **budgets** (as an execution can reject early).
* **Original explicit Siegel constants, direct `η`, and binary folding:**
  `friBatchJohnsonCommitError` (`(2 - 1 / 2 ^ m) * 1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / (ρ * |F|)`)
  and `friBatchJohnsonEtaCommitError` (`(2 - 1 / 2 ^ m) * 115200 * (2 ^ d) ^ 2 / (ρ * η ^ 6 * |F|)`,
  using `η` directly rather than `min(η, √ρ / 20)` in Eq. (1.3)) are this library's **original
  explicit Siegel finite bounds** for binary folding (`l⁽ⁱ⁾ = 2`, `mJ ≥ 1` vs. the paper's
  `m ≥ 3`), not uniformly smaller at small `mJ` than the displayed
  `(m + 1 / 2) ^ 7 / (2 * ρ ^ (3 / 2))`
  + `(2 * m + 1) * (|D⁰| + 1) / √ρ · ∑ l⁽ⁱ⁾` expressions of JACM Lemma 8.2 / Theorem 8.3. Exact
  correspondence with the paper's displayed constants remains open on `#5968`.

## Main definitions

* `Cslib.Crypto.Protocols.FRI.friBatchRoundEscape`,
  `Cslib.Crypto.Protocols.FRI.friBatchSumError`: indexed `(m + 2)`-round escape vector and summed
  interactive batched FRI error `ε_batch + (∑ i, ε_commit i) + ((2 ^ d - e - 1) / 2 ^ d) ^ q`.
* `Cslib.Crypto.Protocols.FRI.friBatchFinalPasses`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame`: post-commit single-query acceptance predicate and
  `(m + 1)`-round interactive batched commit-phase game (`[Fintype F]` only).
* `Cslib.Crypto.Protocols.FRI.friBatchUniqueCommitError`,
  `Cslib.Crypto.Protocols.FRI.friBatchJohnsonCommitError`,
  `Cslib.Crypto.Protocols.FRI.friBatchJohnsonEtaCommitError`: closed-form `(2 - 1 / 2 ^ m)`
  batched commit-phase error bounds across the unique-decoding, explicit-multiplicity Johnson, and
  `η`-gap regimes.

## Main results

* `Cslib.Crypto.Protocols.FRI.friBatchCommitRound_escape_le_of_weightedLineEscapePerRound`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_le_of_escape`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_le_of_escape`: conditional per-round and
  summed commit / interactive IOP escape reductions via `Cslib.Crypto.Protocols.BCS`.
* `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_proximity_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_le_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_proximity_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_proximity_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_le_of_johnson_eta`: unconditional integer-`e` and
  real-`α` (`⌊α₀ * 2 ^ d⌋₊`) batched commit-phase upper bounds in the setting of Lemma 8.2.
* `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_proximity_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_le_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_proximity_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_proximity_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_le_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_sound_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_le_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_sound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_le_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_sound_of_johnson_eta`: unconditional integer-`e` and
  real-`α` (`batchCorrAgreeLang t α`) interactive batched FRI soundness bounds and contrapositives
  in the setting of Theorem 8.3.
* `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_prover_verifier_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_corrAgree_romSoundness_bound_of_unique`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_johnson_discrete`,
  `FRI.friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_discrete`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_eta`,
  `Cslib.Crypto.Protocols.FRI.friBatchBCS_corrAgree_romSoundness_bound_of_johnson`,
  `FRI.friBatchBCS_corrAgree_romSoundness_bound_of_prover_verifier_of_johnson`:
  adaptive two-channel batched BCS-FRI ROM soundness bounds.

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [E. Ben-Sasson, I. Bentov, Y. Horesh, M. Riabzev, *Fast Reed–Solomon Interactive Oracle Proofs
  of Proximity*][BenSassonBentovHoreshRiabzev2018]
* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Finset Cslib.Code Cslib.OracleComp Cslib.Crypto.Protocols.BCS Cslib.Probability

/-! ### Section 1: Conditional Summed Batched IOP Bridge -/

section ConditionalSummedBridge

variable {F : Type} [Field F]

/-- **Conditional step (per-round batched folding escape bound assuming
`WeightedLineEscapePerRound`)**: at folding round `i : Fin params.m` (`pref.length = i.val + 1`)
from a prefix doomed at threshold `B`, the escape probability over a uniform `FRIBatchChal` is at
most `ε_commit i`. Discharging `WeightedLineEscapePerRound` is left to the caller. -/
theorem friBatchCommitRound_escape_le_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {B : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params B ε_commit)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    {i : Fin params.m} (hlen : pref.length = i.val + 1) (π : OracleTable params.d F)
    (hdoomed : friBatchDoomed params t B stmt pref) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friBatchGoodStep params t B stmt pref π c} ≤ ε_commit i := by
  cases pref with
  | nil => cases hlen
  | cons head rest =>
    rw [toOuterMeasure_not_friBatchGoodStep_cons]
    have htail_len : (friBatchTailTranscript rest).length = i.val := by
      simp only [List.length_cons] at hlen
      rw [length_friBatchTailTranscript]
      omega
    have hpm : (friBatchTailTranscript rest).length < params.m := htail_len ▸ i.isLt
    have hbound := friCommitRound_escape_le_of_weightedLineEscapePerRound params hesc
      (stmt.eval head.2.batchCoeffs) (friBatchTailTranscript rest) hpm π hdoomed
    have hidx : (⟨(friBatchTailTranscript rest).length, hpm⟩ : Fin params.m) = i :=
      Fin.ext htail_len
    rwa [hidx] at hbound

/-- Per-round escape budget vector for `(params.m + 2)`-round `friBatchIOP`: `ε_batch` in round `0`,
`ε_commit i` in folding rounds `1, …, m`, and `((2 ^ d - e - 1) / 2 ^ d) ^ q` in the final query
round `m + 1`. -/
@[expose] noncomputable def friBatchRoundEscape (params : FRIParams F) (ε_batch : ℝ≥0∞)
    (e : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) : Fin (params.m + 2) → ℝ≥0∞ :=
  Fin.cases ε_batch (friRoundEscape params e ε_commit)

/-- Summed interactive batched FRI soundness error
`ε_batch + (∑ i : Fin m, ε_commit i) + ((2 ^ d - e - 1) / 2 ^ d) ^ q`, combining the commit-phase
bad-event sum (cf. the proof of Lemma 8.2 in [BenSassonCarmonIshaiKoppartySaraf2020, Section 8.2.1,
p. 42]) with the `q`-invocation query bound (cf. the proof of Theorem 8.3 on p. 40). -/
@[expose] noncomputable def friBatchSumError (params : FRIParams F) (ε_batch : ℝ≥0∞)
    (e : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) : ℝ≥0∞ :=
  ε_batch + friSumError params e ε_commit

/-- Exact sum of `friBatchRoundEscape` across all `m + 2` rounds of `friBatchIOP`. -/
theorem sum_friBatchRoundEscape_eq (params : FRIParams F) (ε_batch : ℝ≥0∞)
    (e : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) :
    (∑ j : Fin (params.m + 2), friBatchRoundEscape params ε_batch e ε_commit j) =
      friBatchSumError params ε_batch e ε_commit := by
  rw [Fin.sum_univ_succ, friBatchRoundEscape, Fin.cases_zero, friBatchSumError]
  congr 1
  calc (∑ i : Fin (params.m + 1),
        Fin.cases ε_batch (friRoundEscape params e ε_commit) i.succ)
      = ∑ i : Fin (params.m + 1), friRoundEscape params e ε_commit i :=
        Finset.sum_congr rfl fun i _ => Fin.cases_succ i
    _ = friSumError params e ε_commit := sum_friRoundEscape_eq_friSumError params e ε_commit

/-- Post-commit single-query acceptance predicate for an `(m + 1)`-round batched commit prefix
`pref` and final committed oracle `πFinal` (`False` on `[]`; delegates to `friFinalPasses` on
`(_, c₀) :: rest`). -/
@[expose] def friBatchFinalPasses (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  match pref with
  | [] => False
  | (_, c₀) :: rest =>
    friFinalPasses params (stmt.eval c₀.batchCoeffs) (friBatchTailTranscript rest) πFinal s

/-- Batched FRI commit-phase game (interactive commit-phase setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39 and Section 8.2.1 on
printed pp. 41–43): runs `m + 1` interactive commit rounds (round `0` batching plus `m` folding
rounds) and samples the final committed oracle `πFinal ← P pref`, returning `true` iff strictly
more than `B` starting positions in `Fin (2 ^ d)` pass `friBatchFinalPasses`. -/
@[expose] noncomputable def friBatchCommitGame [Fintype F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) : PMF Bool :=
  (iopRunRounds P (params.m + 1) []).bind fun pref =>
    (P pref).map fun πFinal =>
      letI : DecidablePred (fun s => friBatchFinalPasses params t stmt pref πFinal s) :=
        Classical.decPred _
      decide
        (B < (Finset.univ.filter fun s => friBatchFinalPasses params t stmt pref πFinal s).card)

/-- **Conditional step (batched FRI commit-phase union bound assuming `BatchRound0Escape` and
`WeightedLineEscapePerRound`)**: for `stmt ∉ params.batchProximityLang t e` and any adaptive prover
`P`, `friBatchCommitGame` exceeds agreement `B = 2 ^ d - e - 1` with probability at most
`ε_batch + ∑ i : Fin params.m, ε_commit i` via
`Cslib.Crypto.Protocols.BCS.iopCommitPhase_map_true_le_sum`. Discharging `BatchRound0Escape` and
`WeightedLineEscapePerRound` is left to the caller. -/
theorem friBatchCommitGame_le_of_escape [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {ε_batch : ℝ≥0∞}
    {ε_commit : Fin params.m → ℝ≥0∞}
    (hbatch : BatchRound0Escape params t e ε_batch)
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ε_batch + ∑ i : Fin params.m, ε_commit i := by
  have hrbr := friBatchIOP_rbrSound params t e
  refine (iopCommitPhase_map_true_le_sum (hrbr.init_doomed stmt hfar) (hrbr.step_doomed stmt)
    (params.m + 1) (Fin.cases ε_batch ε_commit)
    (fun j pref π hlen hdoomed => ?_) P _
    (fun pref πFinal hlen hdoomed => ?_)).trans_eq ?_
  · refine Fin.cases (motive := fun j : Fin (params.m + 1) =>
      pref.length = j.val →
      (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friBatchGoodStep params t (2 ^ params.d - e - 1) stmt pref π c} ≤
        Fin.cases ε_batch ε_commit j) ?_ ?_ j hlen
    · intro hlen0
      rw [List.eq_nil_of_length_eq_zero hlen0, Fin.cases_zero]
      exact friBatchRound0_escape_le_of_escape params t hbatch hfar π
    · intro i hleni
      rw [Fin.cases_succ]
      exact friBatchCommitRound_escape_le_of_weightedLineEscapePerRound params t hesc stmt pref
        hleni π hdoomed
  · cases pref with
    | nil => cases hlen
    | cons head rest =>
      have htail_len : (friBatchTailTranscript rest).length = params.m := by
        simp only [List.length_cons] at hlen
        rw [length_friBatchTailTranscript]
        omega
      have hcard := card_filter_friFinalPasses_le_of_friDoomed params htail_len πFinal hdoomed
      have hcongr :
          (@Finset.filter _ (fun s => friBatchFinalPasses params t stmt (head :: rest) πFinal s)
            (Classical.decPred _) Finset.univ).card =
          (Finset.univ.filter fun s =>
            friFinalPasses params (stmt.eval head.2.batchCoeffs)
              (friBatchTailTranscript rest) πFinal s).card := by
        congr 2
      exact decide_eq_false (not_lt_of_ge (hcongr.trans_le hcard))
  · rw [Fin.sum_univ_succ, Fin.cases_zero]
    congr 1

private theorem friBatchPerRoundEscape_of_escape [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {ε_batch : ℝ≥0∞}
    {ε_commit : Fin params.m → ℝ≥0∞}
    (hbatch : BatchRound0Escape params t e ε_batch)
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit) :
    ∀ stmt ∉ params.batchProximityLang t e,
      ∀ (j : Fin (params.m + 2)) pref π,
        pref.length = j.val →
        friBatchDoomed params t (2 ^ params.d - e - 1) stmt pref →
        (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
          {c | ¬ friBatchGoodStep params t (2 ^ params.d - e - 1) stmt pref π c} ≤
        friBatchRoundEscape params ε_batch e ε_commit j := by
  intro stmt hfar j pref π hlen hdoomed
  refine Fin.cases (motive := fun j : Fin (params.m + 2) =>
    pref.length = j.val →
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
      {c | ¬ friBatchGoodStep params t (2 ^ params.d - e - 1) stmt pref π c} ≤
      friBatchRoundEscape params ε_batch e ε_commit j) ?_ ?_ j hlen
  · intro hlen0
    rw [List.eq_nil_of_length_eq_zero hlen0, friBatchRoundEscape, Fin.cases_zero]
    exact friBatchRound0_escape_le_of_escape params t hbatch hfar π
  · intro k hlenk
    rw [friBatchRoundEscape, Fin.cases_succ]
    by_cases hk : k.val < params.m
    · simp only [friRoundEscape, hk, ↓reduceDIte]
      exact friBatchCommitRound_escape_le_of_weightedLineEscapePerRound params t hesc stmt pref
        (i := ⟨k.val, hk⟩) hlenk π hdoomed
    · have hk_eq : k.val = params.m := by omega
      have hlen_m1 : pref.length = params.m + 1 := by
        simpa only [Fin.val_succ, hk_eq] using hlenk
      simpa only [friRoundEscape, hk, ↓reduceDIte] using
        friBatchQueryRound_escape_le params t (2 ^ params.d - e - 1) stmt pref hlen_m1 π hdoomed

/-- **Conditional step (summed interactive soundness for `friBatchIOP` assuming `BatchRound0Escape`
and `WeightedLineEscapePerRound`)**: for `stmt ∉ params.batchProximityLang t e` and any adaptive
(possibly randomized) prover `P`, `iopInteractiveGame (friBatchIOP params t) stmt P true ≤
friBatchSumError params ε_batch e ε_commit` via
`Cslib.Crypto.Protocols.BCS.iopInteractiveGame_le_sum`.
Discharging `BatchRound0Escape` and `WeightedLineEscapePerRound` is left to the caller. -/
theorem friBatchIOP_interactiveGame_le_of_escape [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {ε_batch : ℝ≥0∞}
    {ε_commit : Fin params.m → ℝ≥0∞}
    (hbatch : BatchRound0Escape params t e ε_batch)
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      friBatchSumError params ε_batch e ε_commit :=
  (iopInteractiveGame_le_sum (friBatchIOP_rbrSound params t e)
    (friBatchRoundEscape params ε_batch e ε_commit)
    (friBatchPerRoundEscape_of_escape params t hbatch hesc) hfar P).trans_eq
    (sum_friBatchRoundEscape_eq params ε_batch e ε_commit)

end ConditionalSummedBridge

/-! ### Section 2: Shared Algebraic, Floor, and Ceiling Helpers -/

section Helpers

variable {F : Type} [Field F]

omit [Field F] in
private theorem add_sum_natCast_div_ennreal {ι : Type*} (B₀ : ℕ) (s : Finset ι)
    (x : ι → ℕ) (D : ℕ) :
    ((B₀ : ℝ≥0∞) / (D : ℝ≥0∞)) + (∑ i ∈ s, ((x i : ℕ) : ℝ≥0∞) / (D : ℝ≥0∞)) =
      ((B₀ + ∑ i ∈ s, x i : ℕ) : ℝ≥0∞) / (D : ℝ≥0∞) := by
  rw [Nat.cast_add, ENNReal.add_div]
  congr 1
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Nat.cast_sum]

omit [Field F] in
private theorem one_sub_inv_two_pow_nonneg (m : ℕ) :
    0 ≤ 1 - (1 : ℝ) / (2 : ℝ) ^ m := by
  have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hdiv : (1 : ℝ) / (2 : ℝ) ^ m ≤ 1 := div_le_one_of_le₀ h1le (by positivity)
  linarith

omit [Field F] in
private theorem two_sub_inv_two_pow_nonneg (m : ℕ) :
    0 ≤ 2 - (1 : ℝ) / (2 : ℝ) ^ m := by
  have h := one_sub_inv_two_pow_nonneg m
  linarith

private theorem friCommitGame_eq_zero_of_two_pow_le [Fintype F]
    (params : FRIParams F) (t B : ℕ) (hB : 2 ^ params.d ≤ B)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friBatchCommitGame params t B stmt P true = 0 := by
  have hgame : friBatchCommitGame params t B stmt P = PMF.pure false := by
    rw [friBatchCommitGame]
    have hmap : ∀ pref,
        (P pref).map (fun πFinal =>
          letI : DecidablePred (fun s => friBatchFinalPasses params t stmt pref πFinal s) :=
            Classical.decPred _
          decide
            (B < (Finset.univ.filter fun s =>
              friBatchFinalPasses params t stmt pref πFinal s).card)) =
        PMF.pure false := by
      intro pref
      have hfn :
          (fun πFinal =>
            letI : DecidablePred (fun s => friBatchFinalPasses params t stmt pref πFinal s) :=
              Classical.decPred _
            decide
              (B < (Finset.univ.filter fun s =>
                friBatchFinalPasses params t stmt pref πFinal s).card)) =
          Function.const _ false := by
        funext πFinal
        have hcard :
            (@Finset.filter _ (fun s => friBatchFinalPasses params t stmt pref πFinal s)
              (Classical.decPred _) Finset.univ).card ≤ 2 ^ params.d :=
          (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
        exact decide_eq_false (not_lt_of_ge (hcard.trans hB))
      rw [hfn, PMF.map_const]
    rw [show (fun pref =>
        (P pref).map fun πFinal =>
          letI : DecidablePred (fun s => friBatchFinalPasses params t stmt pref πFinal s) :=
            Classical.decPred _
          decide
            (B < (Finset.univ.filter fun s =>
              friBatchFinalPasses params t stmt pref πFinal s).card)) =
      (fun _ => PMF.pure false) from funext hmap, PMF.bind_const]
  rw [hgame, PMF.pure_apply]
  simp only [Bool.true_eq_false, ↓reduceIte]

private theorem friBatchCommitGame_le_of_floor [Fintype F]
    (params : FRIParams F) (t : ℕ) {α α₀ : ℝ} {ε_C : ℝ≥0∞}
    (hα₀_nn : 0 ≤ α₀) (hα_le_α₀ : α ≤ α₀)
    {stmt : FRIBatchStmt F params.d t}
    (hagree_le : ∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
      v₀ ∈ params.initialCode →
      ∀ v : Fin t → OracleTable params.d F,
        (∀ j, v j ∈ params.initialCode) →
        (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params.d : ℝ) ≤ α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hprox : ∀ e₀ : ℕ, stmt ∉ params.batchProximityLang t e₀ →
      (e₀ : ℝ) / (2 ^ params.d : ℝ) < 1 - α₀ →
      friBatchCommitGame params t (2 ^ params.d - e₀ - 1) stmt P true ≤ ε_C) :
    friBatchCommitGame params t ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ stmt P true ≤ ε_C := by
  by_cases hα₀_lt : α₀ < 1
  · obtain ⟨hiff, _, hB_eq, _, he_lt⟩ :=
      batchFloorThreshold_bounds params t stmt hα₀_nn hα₀_lt
    have hnot :
        stmt ∉ params.batchProximityLang t (2 ^ params.d - 1 - ⌊α₀ * (2 ^ params.d : ℝ)⌋₊) :=
      hiff.mp fun D' v₀ hv₀ v hv hag => (hagree_le D' v₀ hv₀ v hv hag).trans hα_le_α₀
    rw [← hB_eq]
    exact hprox _ hnot he_lt
  · have h1le : 1 ≤ α₀ := not_lt.mp hα₀_lt
    have h2le : 2 ^ params.d ≤ ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ := by
      refine Nat.le_floor ?_
      have hn : (0 : ℝ) ≤ (2 ^ params.d : ℝ) := by positivity
      calc ((2 ^ params.d : ℕ) : ℝ)
          = 1 * (2 ^ params.d : ℝ) := by push_cast; ring
        _ ≤ α₀ * (2 ^ params.d : ℝ) := mul_le_mul_of_nonneg_right h1le hn
    rw [friCommitGame_eq_zero_of_two_pow_le params t _ h2le stmt P]
    exact zero_le

private theorem iopInteractiveGame_le_ofReal_add_pow_of_one_lt [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {α ε_C : ℝ} (hε_nn : 0 ≤ ε_C) (h1lt : 1 < α)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (ε_C + α ^ params.q) := by
  have h1pow : (1 : ℝ) ≤ α ^ params.q := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one h1lt.le params.q
  have h1le : (1 : ℝ) ≤ ε_C + α ^ params.q := by linarith
  calc iopInteractiveGame (friBatchIOP params t) stmt P true
      ≤ 1 := PMF.coe_le_one _ true
    _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
    _ ≤ ENNReal.ofReal (ε_C + α ^ params.q) := ENNReal.ofReal_le_ofReal h1le

private theorem query_pow_le_ofReal_pow {d e q : ℕ} {α : ℝ}
    (hq_lt : (((2 ^ d - e - 1 : ℕ) : ℝ) / (2 ^ d : ℝ)) < α) :
    (((2 ^ d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) ^ q ≤ ENNReal.ofReal (α ^ q) := by
  set r : ℝ := ((2 ^ d - e - 1 : ℕ) : ℝ) / (2 ^ d : ℝ)
  have hr_nn : 0 ≤ r := by positivity
  have hcast : (((2 ^ d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ d : ℝ≥0∞)) = ENNReal.ofReal r := by
    dsimp only [r]
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  rw [hcast, ← ENNReal.ofReal_pow hr_nn q]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr_nn hq_lt.le q)

private theorem friBatchIOP_interactiveGame_le_of_corrAgree_le [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {α ε_C : ℝ} (hε_nn : 0 ≤ ε_C)
    (hα_pos : 0 < α) (hα_le : α ≤ 1)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchCorrAgreeLang t α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hprox : ∀ e : ℕ, stmt ∉ params.batchProximityLang t e →
      (e : ℝ) / (2 ^ params.d : ℝ) ≤ 1 - α →
      iopInteractiveGame (friBatchIOP params t) stmt P true ≤
        ENNReal.ofReal ε_C + (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^
          params.q) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (ε_C + α ^ params.q) := by
  set e : ℕ := 2 ^ params.d - ⌈α * (2 ^ params.d : ℝ)⌉₊
  have hnot_e : stmt ∉ params.batchProximityLang t e := by
    rwa [batchCorrAgreeLang_eq_batchProximityLang params t hα_le] at hfar
  obtain ⟨_, hq_lt, he_le⟩ := batchCeilThreshold_bounds params hα_pos hα_le
  have hpow_nn : 0 ≤ α ^ params.q := pow_nonneg hα_pos.le params.q
  refine (hprox e hnot_e he_le).trans ?_
  calc ENNReal.ofReal ε_C +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q
      ≤ ENNReal.ofReal ε_C + ENNReal.ofReal (α ^ params.q) :=
        add_le_add le_rfl (query_pow_le_ofReal_pow hq_lt)
    _ = ENNReal.ofReal (ε_C + α ^ params.q) := (ENNReal.ofReal_add hε_nn hpow_nn).symm

private theorem friBatchRBRError_ceil_le [Fintype F] (params : FRIParams F)
    (ε_batch : ℝ≥0∞) {α : ℝ} (hα_pos : 0 < α) (hα_le : α ≤ 1) (B_commit : ℕ) :
    friBatchRBRError params ε_batch (2 ^ params.d - ⌈α * (2 ^ params.d : ℝ)⌉₊) B_commit ≤
      max ε_batch
        (max ((B_commit : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) (ENNReal.ofReal (α ^ params.q))) := by
  obtain ⟨_, hq_lt, _⟩ := batchCeilThreshold_bounds params hα_pos hα_le
  simp only [friBatchRBRError, friRBRError]
  exact max_le_max le_rfl (max_le_max le_rfl (query_pow_le_ofReal_pow hq_lt))

end Helpers

/-! ### Section 3: Unconditional Unique-Decoding Batched FRI Soundness & BCS-FRI ROM -/

section UniqueDecoding

variable {F : Type} [Field F]

/-- Closed-form geometric commit-phase error `(2 - 1 / 2 ^ m) * (2 ^ d / |F|)` across round-`0`
batching (`2 ^ d / |F|`) and all `m` binary folding rounds (`(1 - 1 / 2 ^ m) * (2 ^ d / |F|)`) in
the unique-decoding regime (`< 2 * 2 ^ d / |F|` independently of `m` and `t`). -/
@[expose] noncomputable def friBatchUniqueCommitError [Fintype F] (params : FRIParams F) : ℝ :=
  (2 - (1 : ℝ) / (2 : ℝ) ^ params.m) * ((2 ^ params.d : ℝ) / (Fintype.card F : ℝ))

private theorem friBatchUniqueCommitError_nonneg [Fintype F] (params : FRIParams F) :
    0 ≤ friBatchUniqueCommitError params :=
  mul_nonneg (two_sub_inv_two_pow_nonneg params.m) (by positivity)

private theorem unique_round0_add_sum_eq [Fintype F] (params : FRIParams F) :
    (2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        (∑ i : Fin params.m,
          ((2 ^ (params.d - (i.val + 1)) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) =
      ((2 * 2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) := by
  have hle : 2 ^ (params.d - params.m) ≤ 2 ^ params.d :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have hsplit :
      2 ^ params.d + (2 ^ params.d - 2 ^ (params.d - params.m)) =
        2 * 2 ^ params.d - 2 ^ (params.d - params.m) := by omega
  have hcast0 : (2 ^ params.d : ℝ≥0∞) = ((2 ^ params.d : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [hcast0, add_sum_natCast_div_ennreal, params.sum_domainSize_succ, hsplit]

/-- Exact identity between the integer-numerator `ℝ≥0∞` unique-decoding batched commit error
`((2 * 2 ^ d - 2 ^ (d - m)) : ℝ≥0∞) / |F|` and `ENNReal.ofReal (friBatchUniqueCommitError params)`.
-/
theorem friBatchUniqueCommitError_ennreal_eq [Fintype F] (params : FRIParams F) :
    ((2 * 2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) =
      ENNReal.ofReal (friBatchUniqueCommitError params) := by
  have hcR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hr0_nn : 0 ≤ (2 ^ params.d : ℝ) / (Fintype.card F : ℝ) := by positivity
  have hrc_nn : 0 ≤ friUniqueCommitError params :=
    mul_nonneg (one_sub_inv_two_pow_nonneg params.m) hr0_nn
  have hr0_eq :
      (2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) =
        ENNReal.ofReal ((2 ^ params.d : ℝ) / (Fintype.card F : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hcR, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast]
  rw [← unique_round0_add_sum_eq, hr0_eq, sum_friUniqueRoundEscape_eq,
    ← ENNReal.ofReal_add hr0_nn hrc_nn]
  congr 1
  simp only [friUniqueCommitError, friBatchUniqueCommitError]
  ring

/-- **Unconditional unique-decoding batched FRI commit-phase upper bound (`batchProximityLang`)**:
for `2 * e + params.dim 0 ≤ 2 ^ d` and `stmt ∉ params.batchProximityLang t e`, `friBatchCommitGame`
exceeds agreement `2 ^ d - e - 1` with probability at most `(2 * 2 ^ d - 2 ^ (d - m)) / |F|`
(`= ENNReal.ofReal (friBatchUniqueCommitError params)`), uniformly for all `t : ℕ`. -/
theorem friBatchCommitGame_proximity_le_of_unique [Fintype F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ((2 * 2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) := by
  classical
  exact (friBatchCommitGame_le_of_escape params t
    (batchRound0Escape_of_unique params t huniq)
    (weightedLineEscapePerRound_of_gapPerRound params
      (weightedLineGapPerRound_of_unique params huniq)) hfar P).trans_eq
    (unique_round0_add_sum_eq params)

/-- **Unconditional unique-decoding interactive batched FRI soundness upper bound
(`batchProximityLang`)**: for `2 * e + params.dim 0 ≤ 2 ^ d` and
`stmt ∉ params.batchProximityLang t e`,
and any adaptive prover `P`, the acceptance probability of `friBatchIOP params t` is at most
`(2 * 2 ^ d - 2 ^ (d - m)) / |F| + ((2 ^ d - e - 1) / 2 ^ d) ^ q` uniformly for all `t : ℕ`. -/
theorem friBatchIOP_interactiveGame_proximity_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ((2 * 2 ^ params.d - 2 ^ (params.d - params.m) : ℕ) : ℝ≥0∞) /
          (Fintype.card F : ℝ≥0∞) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  refine (friBatchIOP_interactiveGame_le_of_escape params t
    (batchRound0Escape_of_unique params t huniq)
    (weightedLineEscapePerRound_of_gapPerRound params
      (weightedLineGapPerRound_of_unique params huniq)) hfar P).trans_eq ?_
  rw [friBatchSumError, friSumError, ← add_assoc, unique_round0_add_sum_eq]

private theorem two_mul_add_dim_le_of_div_le (params : FRIParams F) {e : ℕ}
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2) :
    2 * e + params.dim 0 ≤ 2 ^ params.d := by
  have hn : (0 : ℝ) < (2 ^ params.d : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right he (by positivity : (0 : ℝ) ≤ 2 * (2 ^ params.d : ℝ))
  have hlhs : ((e : ℝ) / (2 ^ params.d : ℝ)) * (2 * (2 ^ params.d : ℝ)) = 2 * (e : ℝ) := by
    field_simp
  have hrhs :
      (1 - (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2) * (2 * (2 ^ params.d : ℝ)) =
        (2 ^ params.d : ℝ) - (params.dim 0 : ℝ) := by
    field_simp
    ring
  rw [hlhs, hrhs] at hmul
  have hcast : ((2 * e + params.dim 0 : ℕ) : ℝ) ≤ ((2 ^ params.d : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  exact_mod_cast hcast

/-- **Unconditional real-`α` unique-decoding batched FRI commit-phase upper bound** (unique-decoding
counterpart of [BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39, bridged via
`batchFloorThreshold_bounds`): if every common agreement witness of `stmt` with `params.initialCode`
has relative density `≤ α`, then for `α₀ = max α ((1 + ρ) / 2)`, `friBatchCommitGame` exceeds
`⌊α₀ * 2 ^ d⌋₊` with probability at most `ENNReal.ofReal (friBatchUniqueCommitError params)`.
Relative to the `μ⁽⁰⁾`-weighted oracle event `E⁽⁰⁾` defined immediately before Eq. (8.8) on printed
pp. 41–42 (with cutoff `max(α, √ρ · (1 + 1 / (2 * m)))`), this unweighted round-`0` event contains
`E⁽⁰⁾` when `(1 + ρ) / 2 ≤ max(α, √ρ · (1 + 1 / (2 * m)))` and can miss `E⁽⁰⁾` otherwise (for
example on `𝔽₁₇ˣ` at `n = 16, k = 4, α = 1 / 2, m = 3`, where `10` agreeing positions clear `7 / 12`
and miss strict `> 5 / 8`). -/
theorem friBatchCommitGame_le_of_unique [Fintype F]
    (params : FRIParams F) (t : ℕ) {α : ℝ}
    {stmt : FRIBatchStmt F params.d t}
    (hagree_le : ∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
      v₀ ∈ params.initialCode →
      ∀ v : Fin t → OracleTable params.d F,
        (∀ j, v j ∈ params.initialCode) →
        (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params.d : ℝ) ≤ α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    let α₀ := max α ((1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2)
    friBatchCommitGame params t ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ stmt P true ≤
      ENNReal.ofReal (friBatchUniqueCommitError params) := by
  intro α₀
  have hmid_nn : 0 ≤ (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 := by positivity
  refine friBatchCommitGame_le_of_floor params t (hmid_nn.trans (le_max_right _ _))
    (le_max_left _ _) hagree_le P fun e₀ hnot_e₀ he₀_lt => ?_
  have hle_mid : (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 ≤ α₀ := le_max_right _ _
  have huniq : 2 * e₀ + params.dim 0 ≤ 2 ^ params.d :=
    two_mul_add_dim_le_of_div_le params (by linarith)
  exact (friBatchCommitGame_proximity_le_of_unique params t huniq hnot_e₀ P).trans_eq
    (friBatchUniqueCommitError_ennreal_eq params)

/-- **Unconditional real-`α` unique-decoding interactive batched FRI soundness upper bound**
(unique-decoding counterpart of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 8.3 on printed
pp. 39–40): for `(1 + ρ) / 2 ≤ α` and `stmt ∉ params.batchCorrAgreeLang t α`, the acceptance
probability of `friBatchIOP params t` against any adaptive prover `P` is at most
`ENNReal.ofReal (friBatchUniqueCommitError params + α ^ params.q)`. -/
theorem friBatchIOP_interactiveGame_le_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {α : ℝ}
    (hα : (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 ≤ α)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchCorrAgreeLang t α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friBatchUniqueCommitError params + α ^ params.q) := by
  by_cases hα_le : α ≤ 1
  · have hα_pos : 0 < α := lt_of_lt_of_le (by positivity) hα
    refine friBatchIOP_interactiveGame_le_of_corrAgree_le params t
      (friBatchUniqueCommitError_nonneg params) hα_pos hα_le hfar P fun e hnot_e he_le => ?_
    have huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d :=
      two_mul_add_dim_le_of_div_le params (he_le.trans (by linarith))
    refine (friBatchIOP_interactiveGame_proximity_le_of_unique params t huniq hnot_e P).trans_eq ?_
    rw [friBatchUniqueCommitError_ennreal_eq]
  · exact iopInteractiveGame_le_ofReal_add_pow_of_one_lt params t
      (friBatchUniqueCommitError_nonneg params) (not_le.mp hα_le) stmt P

/-- **Contrapositive real-`α` unique-decoding interactive batched FRI soundness**: if an adaptive
prover `P` makes `friBatchIOP params t` accept `stmt` with probability strictly exceeding
`ENNReal.ofReal (friBatchUniqueCommitError params + α ^ params.q)` (which itself excludes the
`1 ≤ α` range since `iopInteractiveGame ... true ≤ 1`), then `stmt ∈ params.batchCorrAgreeLang t α`.
-/
theorem friBatchIOP_sound_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {α : ℝ}
    (hα : (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 ≤ α)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hacc : ENNReal.ofReal (friBatchUniqueCommitError params + α ^ params.q) <
      iopInteractiveGame (friBatchIOP params t) stmt P true) :
    stmt ∈ params.batchCorrAgreeLang t α := by
  by_contra hfar
  exact not_lt_of_ge (friBatchIOP_interactiveGame_le_of_unique params t hα hfar P) hacc

/-- **Unconditional adaptive two-channel batched BCS-FRI ROM soundness in the unique-decoding
regime** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]), composing `batchRound0Escape_of_unique`
and `weightedLineGapBound_of_unique` with `friBatchBCS_romSoundness_bound_of_escape`. -/
theorem friBatchBCS_romSoundness_bound_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params t) encSym (params.batchProximityLang t e) P) Q_MT) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              e (2 ^ (params.d - 1)) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_escape params t
    (batchRound0Escape_of_unique params t huniq)
    (weightedLineGapBound_of_unique params huniq) hdec σ hFS hMT

/-- **Unconditional adaptive two-channel batched BCS-FRI ROM soundness with separate prover/verifier
Merkle budgets in the unique-decoding regime** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]),
composing `batchRound0Escape_of_unique` and `weightedLineGapBound_of_unique` with
`friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape`. -/
theorem friBatchBCS_romSoundness_bound_of_prover_verifier_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              e (2 ^ (params.d - 1)) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape params t
    (batchRound0Escape_of_unique params t huniq)
    (weightedLineGapBound_of_unique params huniq) hdec σ hMT hFS hops

/-- **Unconditional adaptive two-channel batched BCS-FRI ROM soundness on `batchCorrAgreeLang` in
the unique-decoding regime** (`(1 + ρ) / 2 ≤ α ≤ 1`; [BenSassonChiesaSpooner2016];
[ChiesaYogev2024]). -/
theorem friBatchBCS_corrAgree_romSoundness_bound_of_unique [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {α : ℝ}
    (hα : (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 ≤ α) (hα_le : α ≤ 1)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params t) encSym (params.batchCorrAgreeLang t α) P) Q_MT) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchCorrAgreeLang t α) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (max ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
              (max (((2 ^ (params.d - 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
                (ENNReal.ofReal (α ^ params.q))) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  have hα_pos : 0 < α := lt_of_lt_of_le (by positivity) hα
  obtain ⟨_, _, he_le⟩ := batchCeilThreshold_bounds params hα_pos hα_le
  have huniq : 2 * (2 ^ params.d - ⌈α * (2 ^ params.d : ℝ)⌉₊) + params.dim 0 ≤ 2 ^ params.d :=
    two_mul_add_dim_le_of_div_le params (he_le.trans (by linarith))
  rw [batchCorrAgreeLang_eq_batchProximityLang params t hα_le] at hMT ⊢
  refine (friBatchBCS_romSoundness_bound_of_unique params t huniq hdec σ hFS hMT).trans ?_
  have hrbr := friBatchRBRError_ceil_le params
    ((2 ^ params.d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) hα_pos hα_le (2 ^ (params.d - 1))
  gcongr

end UniqueDecoding

/-! ### Section 4: Discrete Guruswami–Sudan Batched FRI Soundness & BCS-FRI ROM -/

section DiscreteJohnson

variable {F : Type} [Field F]

/-- **Explicit-parameter Guruswami–Sudan step toward batched FRI commit-phase soundness** (after
[BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39 and Section 8.2.1 on
printed p. 42): given round-`0` parameters `(m₀, D₀)` with budget `B_batch` and per-round folding
parameters `(mRound, DRound)` across rounds `1, …, m`, bounds `friBatchCommitGame` by the exact
per-round `johnsonCurveBound` sum without inflating later folding rounds to round `0`. -/
theorem friBatchCommitGame_le_of_johnson_discrete [Fintype F]
    (params : FRIParams F) (t : ℕ) {e m₀ D₀ B_batch : ℕ}
    (hm₀ : 1 ≤ m₀)
    (hk₀_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp₀ : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot₀ : D₀ < m₀ * (2 ^ params.d - e))
    (hbound₀ : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      2 ^ (params.d - (i.val + 1)) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i < mRound i * (2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1)))
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ((B_batch + ∑ i : Fin params.m,
          ProximityGap.johnsonCurveBound (2 ^ (params.d - (i.val + 1))) (mRound i)
            (params.dim (i.val + 1) - 1) (DRound i) 1 (2 ^ params.d) : ℕ) : ℝ≥0∞) /
        (Fintype.card F : ℝ≥0∞) := by
  classical
  have he_lt : e < 2 ^ params.d := params.lt_two_pow_of_not_mem_batchProximityLang hfar
  exact (friBatchCommitGame_le_of_escape params t
    (batchRound0Escape_of_johnson_discrete params t hm₀ hk₀_le hinterp₀ hroot₀ hbound₀)
    (weightedLineEscapePerRound_of_gapPerRound params
      (weightedLineGapPerRound_of_johnson_discrete params he_lt mRound DRound hm hk_le hinterp
        hroot)) hfar P).trans_eq (add_sum_natCast_div_ennreal _ _ _ _)

/-- **Explicit-parameter Guruswami–Sudan step toward interactive batched FRI soundness** (after
[BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39 / Section 8.2.1 p. 42 and
Theorem 8.3 on printed pp. 39–40): combines the summed discrete commit-phase escape budget with the
`q`-invocation query bound `((2 ^ d - e - 1) / 2 ^ d) ^ q`. -/
theorem friBatchIOP_interactiveGame_le_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e m₀ D₀ B_batch : ℕ}
    (hm₀ : 1 ≤ m₀)
    (hk₀_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp₀ : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot₀ : D₀ < m₀ * (2 ^ params.d - e))
    (hbound₀ : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      2 ^ (params.d - (i.val + 1)) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i < mRound i * (2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1)))
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ((B_batch + ∑ i : Fin params.m,
            ProximityGap.johnsonCurveBound (2 ^ (params.d - (i.val + 1))) (mRound i)
              (params.dim (i.val + 1) - 1) (DRound i) 1 (2 ^ params.d) : ℕ) : ℝ≥0∞) /
          (Fintype.card F : ℝ≥0∞) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  have he_lt : e < 2 ^ params.d := params.lt_two_pow_of_not_mem_batchProximityLang hfar
  refine (friBatchIOP_interactiveGame_le_of_escape params t
    (batchRound0Escape_of_johnson_discrete params t hm₀ hk₀_le hinterp₀ hroot₀ hbound₀)
    (weightedLineEscapePerRound_of_gapPerRound params
      (weightedLineGapPerRound_of_johnson_discrete params he_lt mRound DRound hm hk_le hinterp
        hroot)) hfar P).trans_eq ?_
  rw [friBatchSumError, friSumError, ← add_assoc, add_sum_natCast_div_ennreal]

/-- **Explicit-parameter Guruswami–Sudan adaptive two-channel batched BCS-FRI ROM soundness**
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]), composing `batchRound0Escape_of_johnson_discrete`
and `weightedLineGapBound_of_johnson_discrete` with `friBatchBCS_romSoundness_bound_of_escape`. -/
theorem friBatchBCS_romSoundness_bound_of_johnson_discrete [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e m₀ D₀ B_batch B_commit : ℕ} (he : e < 2 ^ params.d)
    (hm₀ : 1 ≤ m₀)
    (hk₀_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp₀ : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot₀ : D₀ < m₀ * (2 ^ params.d - e))
    (hbound₀ : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      2 ^ (params.d - (i.val + 1)) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i < mRound i * (2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1)))
    (hbound : ∀ i : Fin params.m,
      ProximityGap.johnsonCurveBound (2 ^ (params.d - (i.val + 1))) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) 1 (2 ^ params.d) ≤ B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params t) encSym (params.batchProximityLang t e) P) Q_MT) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params ((B_batch : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) e B_commit +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_escape params t
    (batchRound0Escape_of_johnson_discrete params t hm₀ hk₀_le hinterp₀ hroot₀ hbound₀)
    (weightedLineGapBound_of_johnson_discrete params he mRound DRound hm hk_le hinterp hroot hbound)
    hdec σ hFS hMT

/-- **Explicit-parameter Guruswami–Sudan adaptive two-channel batched BCS-FRI ROM soundness with
separate prover/verifier Merkle budgets** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_discrete
    [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e m₀ D₀ B_batch B_commit : ℕ} (he : e < 2 ^ params.d)
    (hm₀ : 1 ≤ m₀)
    (hk₀_le : params.dim 0 ≤ 2 ^ params.d - e)
    (hinterp₀ : 2 ^ params.d * (m₀ * (m₀ + 1) / 2) <
      #(Sudan.monomials (params.dim 0 - 1) D₀))
    (hroot₀ : D₀ < m₀ * (2 ^ params.d - e))
    (hbound₀ : ProximityGap.johnsonCurveBound (2 ^ params.d) m₀
      (params.dim 0 - 1) D₀ 1 (2 ^ params.d) ≤ B_batch)
    (mRound DRound : Fin params.m → ℕ)
    (hm : ∀ i : Fin params.m, 1 ≤ mRound i)
    (hk_le : ∀ i : Fin params.m,
      params.dim (i.val + 1) ≤ 2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1))
    (hinterp : ∀ i : Fin params.m,
      2 ^ (params.d - (i.val + 1)) * (mRound i * (mRound i + 1) / 2) <
        #(Sudan.monomials (params.dim (i.val + 1) - 1) (DRound i)))
    (hroot : ∀ i : Fin params.m,
      DRound i < mRound i * (2 ^ (params.d - (i.val + 1)) - e / 2 ^ (i.val + 1)))
    (hbound : ∀ i : Fin params.m,
      ProximityGap.johnsonCurveBound (2 ^ (params.d - (i.val + 1))) (mRound i)
        (params.dim (i.val + 1) - 1) (DRound i) 1 (2 ^ params.d) ≤ B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params ((B_batch : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) e B_commit +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape params t
    (batchRound0Escape_of_johnson_discrete params t hm₀ hk₀_le hinterp₀ hroot₀ hbound₀)
    (weightedLineGapBound_of_johnson_discrete params he mRound DRound hm hk_le hinterp hroot hbound)
    hdec σ hMT hFS hops

end DiscreteJohnson

/-! ### Section 5: Closed-Form Johnson & `η`-Gap Batched FRI Soundness & BCS ROM -/

section ClosedFormJohnson

variable {F : Type} [Field F]

/-- Closed-form geometric Siegel commit-phase error upper bound across round-`0` batching and all
`m` binary folding rounds of `friBatchIOP` with multiplicity parameter `mJ`:
`(2 - 1 / 2 ^ m) * (1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / ((dim 0 / 2 ^ d) * |F|))` (an original
explicit Siegel finite bound bounded independently of `m` and `t`, in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39 and Section 8.2.1 on
printed pp. 41–43; not uniformly smaller at small `mJ` than the paper's displayed constant). -/
@[expose] noncomputable def friBatchJohnsonCommitError [Fintype F]
    (params : FRIParams F) (mJ : ℕ) : ℝ :=
  (2 - (1 : ℝ) / (2 : ℝ) ^ params.m) *
    (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
      (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)))

/-- Closed-form geometric Siegel `η`-gap commit-phase error upper bound across round-`0` batching
and all `m` binary folding rounds of `friBatchIOP`:
`(2 - 1 / 2 ^ m) * (115200 * (2 ^ d) ^ 2 / ((dim 0 / 2 ^ d) * η ^ 6 * |F|))` (an original explicit
finite bound using `η` directly rather than `min(η, √ρ / 20)` in Eq. (1.3)). -/
@[expose] noncomputable def friBatchJohnsonEtaCommitError [Fintype F]
    (params : FRIParams F) (η : ℝ) : ℝ :=
  (2 - (1 : ℝ) / (2 : ℝ) ^ params.m) *
    (115200 * ((2 ^ params.d : ℝ) ^ 2) /
      (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)))

private theorem friBatchJohnsonCommitError_nonneg [Fintype F] (params : FRIParams F) (mJ : ℕ) :
    0 ≤ friBatchJohnsonCommitError params mJ := by
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast params.one_le_dim 0
  exact mul_nonneg (two_sub_inv_two_pow_nonneg params.m) (by positivity)

private theorem friBatchJohnsonEtaCommitError_nonneg [Fintype F] (params : FRIParams F)
    {η : ℝ} (hη : 0 < η) :
    0 ≤ friBatchJohnsonEtaCommitError params η := by
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast params.one_le_dim 0
  exact mul_nonneg (two_sub_inv_two_pow_nonneg params.m) (by positivity)

private theorem round0_add_friJohnsonCommitError_eq [Fintype F] (params : FRIParams F) (mJ : ℕ) :
    ENNReal.ofReal
        (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))) +
      ENNReal.ofReal (friJohnsonCommitError params mJ) =
    ENNReal.ofReal (friBatchJohnsonCommitError params mJ) := by
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast params.one_le_dim 0
  have hr0_nn :
      0 ≤ 1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
        (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)) := by
    positivity
  have hrc_nn : 0 ≤ friJohnsonCommitError params mJ :=
    mul_nonneg (one_sub_inv_two_pow_nonneg params.m) hr0_nn
  rw [← ENNReal.ofReal_add hr0_nn hrc_nn]
  congr 1
  simp only [friJohnsonCommitError, friBatchJohnsonCommitError]
  ring

private theorem friBatchJohnsonCommitError_le_eta [Fintype F] (params : FRIParams F)
    {mJ : ℕ} {η : ℝ} (hη : 0 < η) (hpow : ((mJ + 1 : ℝ) ^ 6) ≤ 64 / (η ^ 6)) :
    friBatchJohnsonCommitError params mJ ≤ friBatchJohnsonEtaCommitError params η := by
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast params.one_le_dim 0
  have hFR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have h2sub_nn : 0 ≤ 2 - (1 : ℝ) / (2 : ℝ) ^ params.m := two_sub_inv_two_pow_nonneg params.m
  refine mul_le_mul_of_nonneg_left ?_ h2sub_nn
  calc 1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
        (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))
      ≤ 1800 * (64 / (η ^ 6)) * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)) := by gcongr
    _ = 115200 * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)) := by
        field_simp
        ring

/-- **Original explicit-constant Johnson batched FRI commit-phase upper bound
(`batchProximityLang`)** up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - √ρ / (2 * mJ)` (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39 and Section 8.2.1 on
printed pp. 41–43): combines `batchRound0Escape_of_johnson` and `weightedLineGapPerRound_of_johnson`
with geometric telescoping across all `m` binary folding rounds (`friBatchJohnsonCommitError params
mJ`, an original explicit Siegel finite bound; exact Lemma 8.2 constants remain open on `#5968`). -/
theorem friBatchCommitGame_proximity_le_of_johnson [Fintype F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonCommitError params mJ) := by
  classical
  refine (friBatchCommitGame_le_of_escape params t
    (batchRound0Escape_of_johnson params t hmJ he)
    (weightedLineEscapePerRound_of_gapPerRound params
      (weightedLineGapPerRound_of_johnson params hmJ he)) hfar P).trans ?_
  exact (add_le_add le_rfl (sum_friJohnsonRoundEscape_le params mJ)).trans_eq
    (round0_add_friJohnsonCommitError_eq params mJ)

/-- **Original explicit-constant Johnson interactive batched FRI soundness upper bound
(`batchProximityLang`)** up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - √ρ / (2 * mJ)` (in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39 / Section 8.2.1 pp. 41–43
and Theorem 8.3 on printed pp. 39–40): bounds `iopInteractiveGame (friBatchIOP params t)` by
`ENNReal.ofReal (friBatchJohnsonCommitError params mJ) + ((2 ^ d - e - 1) / 2 ^ d) ^ q` uniformly
for all `t : ℕ` (exact Theorem 8.3 constants remain open on `#5968`). -/
theorem friBatchIOP_interactiveGame_proximity_le_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonCommitError params mJ) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  refine (friBatchIOP_interactiveGame_le_of_escape params t
    (batchRound0Escape_of_johnson params t hmJ he)
    (weightedLineEscapePerRound_of_gapPerRound params
      (weightedLineGapPerRound_of_johnson params hmJ he)) hfar P).trans ?_
  rw [friBatchSumError, friSumError, ← add_assoc]
  refine add_le_add ?_ le_rfl
  exact (add_le_add le_rfl (sum_friJohnsonRoundEscape_le params mJ)).trans_eq
    (round0_add_friJohnsonCommitError_eq params mJ)

private theorem exists_mJ_and_commitError_le_of_eta [Fintype F]
    (params : FRIParams F) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η) :
    ∃ mJ : ℕ, 1 ≤ mJ ∧
      (e : ℝ) / (2 ^ params.d : ℝ) ≤
        1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
          Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)) ∧
      ENNReal.ofReal (friBatchJohnsonCommitError params mJ) ≤
        ENNReal.ofReal (friBatchJohnsonEtaCommitError params η) := by
  have hk₀_le : params.dim 0 ≤ 2 ^ params.d := by
    simpa only [Nat.sub_zero] using params.dim_le_domainSize (Nat.zero_le params.m)
  obtain ⟨mJ, hmJ, he_mJ, hpow_mJ⟩ :=
    ProximityGap.exists_multiplicity_of_eta (params.one_le_dim 0) hk₀_le hη
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using he)
  exact ⟨mJ, hmJ, by simpa only [Nat.cast_pow, Nat.cast_ofNat] using he_mJ,
    ENNReal.ofReal_le_ofReal (friBatchJohnsonCommitError_le_eta params hη hpow_mJ)⟩

/-- **Original explicit-constant `η`-gap Johnson batched FRI commit-phase upper bound
(`batchProximityLang`)** up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - η` (`0 < η`), in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39 and Section 8.2.1 on
printed pp. 41–43 (using `η` directly rather than `min(η, √ρ / 20)` in Eq. (1.3)). -/
theorem friBatchCommitGame_proximity_le_of_johnson_eta [Fintype F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonEtaCommitError params η) := by
  obtain ⟨mJ, hmJ, he_mJ, hle⟩ := exists_mJ_and_commitError_le_of_eta params hη he
  exact (friBatchCommitGame_proximity_le_of_johnson params t hmJ he_mJ hfar P).trans hle

/-- **Original explicit-constant `η`-gap Johnson interactive batched FRI soundness upper bound
(`batchProximityLang`)** up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - η` (`0 < η`), in the setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 (pp. 38–39 / Section 8.2.1 pp. 41–43) and
Theorem 8.3 (pp. 39–40), using `η` directly rather than `min(η, √ρ / 20)` in Eq. (1.3). -/
theorem friBatchIOP_interactiveGame_proximity_le_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonEtaCommitError params η) +
        (((2 ^ params.d - e - 1 : ℕ) : ℝ≥0∞) / (2 ^ params.d : ℝ≥0∞)) ^ params.q := by
  obtain ⟨mJ, hmJ, he_mJ, hle⟩ := exists_mJ_and_commitError_le_of_eta params hη he
  exact (friBatchIOP_interactiveGame_proximity_le_of_johnson params t hmJ he_mJ hfar P).trans
    (add_le_add hle le_rfl)

/-- **Original explicit-constant real-`α` Johnson batched FRI commit-phase upper bound** (in the
setting of [BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39, Eq. (8.5), and
Section 8.2.1 on printed pp. 41–43, bridged via `batchFloorThreshold_bounds`): for any `α : ℝ` such
that every shared agreement witness of `stmt` with `params.initialCode` has relative density `≤ α`,
setting `α₀ = max α (√ρ * (1 + 1 / (2 * mJ)))`, `friBatchCommitGame` exceeds `⌊α₀ * 2 ^ d⌋₊` with
probability at most `ENNReal.ofReal (friBatchJohnsonCommitError params mJ)` (valid for all `α : ℝ`,
using this library's original explicit Siegel constant; at matching multiplicity `mJ = m`, or
whenever `m ≤ mJ`, the unweighted `stmt.eval x` round-`0` event unconditionally contains the
`μ⁽⁰⁾`-weighted event `E⁽⁰⁾` defined immediately before Eq. (8.8); exact Lemma 8.2 constants remain
open on `#5968`). -/
theorem friBatchCommitGame_le_of_johnson [Fintype F]
    (params : FRIParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    {stmt : FRIBatchStmt F params.d t}
    (hagree_le : ∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
      v₀ ∈ params.initialCode →
      ∀ v : Fin t → OracleTable params.d F,
        (∀ j, v j ∈ params.initialCode) →
        (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params.d : ℝ) ≤ α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    let α₀ := max α (Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))))
    friBatchCommitGame params t ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonCommitError params mJ) := by
  intro α₀
  set cJ : ℝ :=
    Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (1 + 1 / (2 * (mJ : ℝ)))
  have hcJ_nn : 0 ≤ cJ := by positivity
  refine friBatchCommitGame_le_of_floor params t (hcJ_nn.trans (le_max_right _ _))
    (le_max_left _ _) hagree_le P fun e₀ hnot_e₀ he₀_lt => ?_
  have hcJ_le : cJ ≤ α₀ := le_max_right _ _
  have hcJ_expand :
      1 - cJ =
        1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
          Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)) := by
    dsimp only [cJ]
    ring
  exact friBatchCommitGame_proximity_le_of_johnson params t hmJ (by linarith) hnot_e₀ P

/-- **Original explicit-constant real-`α` `η`-gap batched FRI commit-phase upper bound** (in the
setting of [BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39 and
Section 8.2.1 on printed pp. 41–43, bridged via `batchFloorThreshold_bounds` and using `η` directly
rather than `min(η, √ρ / 20)` in Eq. (1.3)): for `0 < η` and `α₀ = max α (√ρ + η)`,
`friBatchCommitGame` exceeds `⌊α₀ * 2 ^ d⌋₊` with probability at most
`ENNReal.ofReal (friBatchJohnsonEtaCommitError params η)` (containing the `μ⁽⁰⁾`-weighted event
`E⁽⁰⁾` defined immediately before Eq. (8.8) when `√ρ + η ≤ max(α, √ρ · (1 + 1 / (2 * m)))`). -/
theorem friBatchCommitGame_le_of_johnson_eta [Fintype F]
    (params : FRIParams F) (t : ℕ) {η α : ℝ} (hη : 0 < η)
    {stmt : FRIBatchStmt F params.d t}
    (hagree_le : ∀ (D' : Finset (Fin (2 ^ params.d))) (v₀ : OracleTable params.d F),
      v₀ ∈ params.initialCode →
      ∀ v : Fin t → OracleTable params.d F,
        (∀ j, v j ∈ params.initialCode) →
        (∀ s ∈ D', stmt.base s = v₀ s ∧ ∀ j, stmt.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params.d : ℝ) ≤ α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    let α₀ := max α (Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) + η)
    friBatchCommitGame params t ⌊α₀ * (2 ^ params.d : ℝ)⌋₊ stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonEtaCommitError params η) := by
  intro α₀
  set cEta : ℝ := Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) + η
  have hcEta_nn : 0 ≤ cEta := by positivity
  refine friBatchCommitGame_le_of_floor params t (hcEta_nn.trans (le_max_right _ _))
    (le_max_left _ _) hagree_le P fun e₀ hnot_e₀ he₀_lt => ?_
  have hcEta_le : cEta ≤ α₀ := le_max_right _ _
  exact friBatchCommitGame_proximity_le_of_johnson_eta params t hη
    (by dsimp only [cEta] at hcEta_le; linarith) hnot_e₀ P

private theorem johnson_slack_of_le (params : FRIParams F) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α x : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α)
    (hx : x ≤ 1 - α) :
    0 < α ∧
      x ≤ 1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)) := by
  have hk₀R : (0 : ℝ) < (params.dim 0 : ℝ) := by exact_mod_cast params.one_le_dim 0
  have hsq_pos : 0 < Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hmJR : (0 : ℝ) < (mJ : ℝ) := by exact_mod_cast hmJ
  have hexpand :
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
          (1 + 1 / (2 * (mJ : ℝ))) =
        1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
          Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)) := by
    ring
  exact ⟨lt_of_lt_of_le (by positivity) hα, by linarith⟩

/-- **Original explicit-constant real-`α` Johnson interactive batched FRI soundness upper bound**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 8.3 on printed p. 39, proved
from Lemma 8.2 on printed p. 40): for `1 ≤ mJ`, `√ρ * (1 + 1 / (2 * mJ)) ≤ α`,
`stmt ∉ params.batchCorrAgreeLang t α`, and any adaptive prover `P`, the acceptance probability of
`friBatchIOP params t` is at most
`ENNReal.ofReal (friBatchJohnsonCommitError params mJ + α ^ params.q)` (using this library's
original explicit Siegel constant; exact Theorem 8.3 constants remain open on `#5968`). -/
theorem friBatchIOP_interactiveGame_le_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchCorrAgreeLang t α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonCommitError params mJ + α ^ params.q) := by
  by_cases hα_le : α ≤ 1
  · refine friBatchIOP_interactiveGame_le_of_corrAgree_le params t
      (friBatchJohnsonCommitError_nonneg params mJ)
      (johnson_slack_of_le params hmJ hα le_rfl).1 hα_le hfar P fun e hnot_e he_le =>
        friBatchIOP_interactiveGame_proximity_le_of_johnson params t hmJ
          (johnson_slack_of_le params hmJ hα he_le).2 hnot_e P
  · exact iopInteractiveGame_le_ofReal_add_pow_of_one_lt params t
      (friBatchJohnsonCommitError_nonneg params mJ) (not_le.mp hα_le) stmt P

/-- **Contrapositive original explicit-constant real-`α` Johnson interactive batched FRI soundness**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 8.3 on printed pp. 39–40; the
strict acceptance premise `hacc` itself excludes the `1 ≤ α` range): if an adaptive prover `P` makes
`friBatchIOP params t` accept `stmt` with probability strictly exceeding
`ENNReal.ofReal (friBatchJohnsonCommitError params mJ + α ^ params.q)`, then
`stmt ∈ params.batchCorrAgreeLang t α`. -/
theorem friBatchIOP_sound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hacc : ENNReal.ofReal (friBatchJohnsonCommitError params mJ + α ^ params.q) <
      iopInteractiveGame (friBatchIOP params t) stmt P true) :
    stmt ∈ params.batchCorrAgreeLang t α := by
  by_contra hfar
  exact not_lt_of_ge (friBatchIOP_interactiveGame_le_of_johnson params t hmJ hα hfar P) hacc

/-- **Original explicit-constant real-`α` `η`-gap interactive batched FRI soundness upper bound**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 8.3 on printed pp. 39–40, using
`η` directly rather than `min(η, √ρ / 20)` in Eq. (1.3)): for `0 < η`, `√ρ + η ≤ α`, and
`stmt ∉ params.batchCorrAgreeLang t α`, `iopInteractiveGame (friBatchIOP params t) stmt P true ≤
ENNReal.ofReal (friBatchJohnsonEtaCommitError params η + α ^ params.q)`. -/
theorem friBatchIOP_interactiveGame_le_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {η α : ℝ} (hη : 0 < η)
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) + η ≤ α)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchCorrAgreeLang t α)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      ENNReal.ofReal (friBatchJohnsonEtaCommitError params η + α ^ params.q) := by
  by_cases hα_le : α ≤ 1
  · have hα_pos : 0 < α := lt_of_lt_of_le (by positivity) hα
    refine friBatchIOP_interactiveGame_le_of_corrAgree_le params t
      (friBatchJohnsonEtaCommitError_nonneg params hη) hα_pos hα_le hfar P fun e hnot_e he_le => ?_
    exact friBatchIOP_interactiveGame_proximity_le_of_johnson_eta params t hη (by linarith) hnot_e P
  · exact iopInteractiveGame_le_ofReal_add_pow_of_one_lt params t
      (friBatchJohnsonEtaCommitError_nonneg params hη) (not_le.mp hα_le) stmt P

/-- **Contrapositive original explicit-constant real-`α` `η`-gap interactive batched FRI soundness**
(in the setting of [BenSassonCarmonIshaiKoppartySaraf2020], Theorem 8.3 on printed pp. 39–40, using
`η` directly rather than `min(η, √ρ / 20)` in Eq. (1.3); the strict acceptance premise `hacc` itself
excludes the `1 ≤ α` range). -/
theorem friBatchIOP_sound_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {η α : ℝ} (hη : 0 < η)
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) + η ≤ α)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t))
    (hacc : ENNReal.ofReal (friBatchJohnsonEtaCommitError params η + α ^ params.q) <
      iopInteractiveGame (friBatchIOP params t) stmt P true) :
    stmt ∈ params.batchCorrAgreeLang t α := by
  by_contra hfar
  exact not_lt_of_ge (friBatchIOP_interactiveGame_le_of_johnson_eta params t hη hα hfar P) hacc

/-- **Original explicit-constant Johnson adaptive two-channel batched BCS-FRI ROM soundness**
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]), composing `batchRound0Escape_of_johnson` and
`weightedLineGapBound_of_johnson` with `friBatchBCS_romSoundness_bound_of_escape` on
`params.batchProximityLang t e` up to `(e : ℝ) / 2 ^ d ≤ 1 - √ρ - √ρ / (2 * mJ)`. -/
theorem friBatchBCS_romSoundness_bound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params t) encSym (params.batchProximityLang t e) P) Q_MT) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params
              (ENNReal.ofReal
                (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))))
              e (friJohnsonCommitBound params mJ) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_escape params t
    (batchRound0Escape_of_johnson params t hmJ he)
    (weightedLineGapBound_of_johnson params hmJ he) hdec σ hFS hMT

/-- **Original explicit-constant Johnson adaptive two-channel batched BCS-FRI ROM soundness with
separate prover/verifier Merkle budgets** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]),
composing `batchRound0Escape_of_johnson` and `weightedLineGapBound_of_johnson` with
`friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape`. -/
theorem friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e mJ : ℕ} (hmJ : 1 ≤ mJ)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) -
        Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / (2 * (mJ : ℝ)))
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params
              (ENNReal.ofReal
                (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))))
              e (friJohnsonCommitBound params mJ) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape params t
    (batchRound0Escape_of_johnson params t hmJ he)
    (weightedLineGapBound_of_johnson params hmJ he) hdec σ hMT hFS hops

/-- **Original explicit-constant `η`-gap Johnson adaptive two-channel batched BCS-FRI ROM
soundness** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]), composing
`batchRound0Escape_of_johnson_eta` and `weightedLineGapBound_of_johnson_eta` with
`friBatchBCS_romSoundness_bound_of_escape` (using `η` directly rather than `min(η, √ρ / 20)`). -/
theorem friBatchBCS_romSoundness_bound_of_johnson_eta [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params t) encSym (params.batchProximityLang t e) P) Q_MT) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params
              (ENNReal.ofReal
                (115200 * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))))
              e (friJohnsonEtaCommitBound params η) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_escape params t
    (batchRound0Escape_of_johnson_eta params t hη he)
    (weightedLineGapBound_of_johnson_eta params hη he) hdec σ hFS hMT

/-- **Original explicit-constant `η`-gap Johnson adaptive two-channel batched BCS-FRI ROM soundness
with separate prover/verifier Merkle budgets** ([BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_eta
    [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {η : ℝ} (hη : 0 < η)
    (he : (e : ℝ) / (2 ^ params.d : ℝ) ≤
      1 - Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) - η)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchProximityLang t e) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (friBatchRBRError params
              (ENNReal.ofReal
                (115200 * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ))))
              e (friJohnsonEtaCommitBound params η) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape params t
    (batchRound0Escape_of_johnson_eta params t hη he)
    (weightedLineGapBound_of_johnson_eta params hη he) hdec σ hMT hFS hops

/-- **Original explicit-constant real-`α` Johnson adaptive two-channel batched BCS-FRI ROM soundness
on `batchCorrAgreeLang`** (`√ρ * (1 + 1 / (2 * mJ)) ≤ α ≤ 1`; [BenSassonChiesaSpooner2016];
[ChiesaYogev2024]). -/
theorem friBatchBCS_corrAgree_romSoundness_bound_of_johnson [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α) (hα_le : α ≤ 1)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params t) encSym (params.batchCorrAgreeLang t α) P) Q_MT) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchCorrAgreeLang t α) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (max (ENNReal.ofReal
                (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))))
              (max ((friJohnsonCommitBound params mJ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
                (ENNReal.ofReal (α ^ params.q))) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  obtain ⟨_, _, he_le⟩ := batchCeilThreshold_bounds params
    (johnson_slack_of_le params hmJ hα le_rfl).1 hα_le
  obtain ⟨hα_pos, he_slack⟩ := johnson_slack_of_le params hmJ hα he_le
  rw [batchCorrAgreeLang_eq_batchProximityLang params t hα_le] at hMT ⊢
  refine (friBatchBCS_romSoundness_bound_of_johnson params t hmJ he_slack hdec σ hFS hMT).trans
    ?_
  have hrbr := friBatchRBRError_ceil_le params
    (ENNReal.ofReal
      (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
        (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))))
    hα_pos hα_le (friJohnsonCommitBound params mJ)
  gcongr

/-- **Original explicit-constant real-`α` Johnson adaptive two-channel batched BCS-FRI ROM soundness
with separate prover/verifier Merkle budgets on `batchCorrAgreeLang`** (`√ρ * (1 + 1 / (2 * mJ)) ≤
α ≤ 1`; [BenSassonChiesaSpooner2016]; [ChiesaYogev2024]). -/
theorem friBatchBCS_corrAgree_romSoundness_bound_of_prover_verifier_of_johnson
    [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {mJ : ℕ} (hmJ : 1 ≤ mJ) {α : ℝ}
    (hα : Real.sqrt ((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) *
      (1 + 1 / (2 * (mJ : ℝ))) ≤ α) (hα_le : α ≤ 1)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friBatchIOP params t) encSym (params.batchCorrAgreeLang t α) P σ true ≤
      ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
          (max (ENNReal.ofReal
                (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
                  (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))))
              (max ((friJohnsonCommitBound params mJ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
                (ENNReal.ofReal (α ^ params.q))) +
            ((t_FS + (params.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal F params.d params.q t))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 2) * (t_FS + (params.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  obtain ⟨_, _, he_le⟩ := batchCeilThreshold_bounds params
    (johnson_slack_of_le params hmJ hα le_rfl).1 hα_le
  obtain ⟨hα_pos, he_slack⟩ := johnson_slack_of_le params hmJ hα he_le
  rw [batchCorrAgreeLang_eq_batchProximityLang params t hα_le]
  refine (friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson params t hmJ he_slack
    hdec σ hMT hFS hops).trans ?_
  have hrbr := friBatchRBRError_ceil_le params
    (ENNReal.ofReal
      (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
        (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ))))
    hα_pos hα_le (friJohnsonCommitBound params mJ)
  gcongr

end ClosedFormJohnson

end Cslib.Crypto.Protocols.FRI
