/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.BatchSoundness
public import CslibFrontier.Crypto.Protocols.FRI.JohnsonSoundness

/-!
# Conditional Smooth Summed Batched FRI IOP Bridge and Commit-Error Definitions

Defines the per-round escape vector (`friSmoothBatchRoundEscape`), summed interactive error
(`friSmoothBatchSumError`), post-commit query predicate (`friSmoothBatchFinalPasses`), interactive
commit-phase game (`friSmoothBatchCommitGame`), and closed-form smooth commit-phase error formulas
(`friSmoothBatchUniqueCommitError`, `friSmoothBatchJohnsonCommitError`,
`friSmoothBatchJohnsonEtaCommitError`), and proves conditional commit-phase and interactive IOP
soundness bounds for `friSmoothBatchIOP` from `SmoothBatchRound0Escape` and
`WeightedCurveEscapePerRound` ([BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2 and
Section 8.2.1).

## Main definitions

* `Cslib.Crypto.Protocols.FRI.friSmoothBatchRoundEscape`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchSumError`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchFinalPasses`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame`: per-round escape schedule, summed error,
  post-commit acceptance predicate, and commit-phase game for `friSmoothBatchIOP`.
* `Cslib.Crypto.Protocols.FRI.friSmoothBatchUniqueCommitError`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchJohnsonCommitError`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchJohnsonEtaCommitError`: closed-form
  `(2 - 1 / 2 ^ totalLog)` smooth batched commit-phase error bounds.

## Main results

* `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitRound_escape_le_of_weightedCurveEscapePerRound`,
  `Cslib.Crypto.Protocols.FRI.sum_friSmoothBatchRoundEscape_eq`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchCommitGame_le_of_escape`,
  `Cslib.Crypto.Protocols.FRI.friSmoothBatchIOP_interactiveGame_le_of_escape`:
  conditional per-round, commit-phase, and interactive IOP union bounds for `friSmoothBatchIOP`.

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Finset Cslib.Code Cslib.OracleComp Cslib.Crypto.Protocols.BCS Cslib.Probability

section SmoothConditionalSummedBridge

variable {F : Type} [Field F]

/-- **Conditional step (per-round smooth batched folding escape bound assuming
`WeightedCurveEscapePerRound`)**: at folding round `i : Fin params.m` (`pref.length = i.val + 1`)
from a prefix doomed at threshold `B`, the escape probability over a uniform `FRIBatchChal` is at
most `ε_commit i`. -/
theorem friSmoothBatchCommitRound_escape_le_of_weightedCurveEscapePerRound [Fintype F]
    [DecidableEq F] (params : FRISmoothParams F) (t : ℕ) {B : ℕ}
    {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params B ε_commit)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    {i : Fin params.m} (hlen : pref.length = i.val + 1) (π : OracleTable params.d F)
    (hdoomed : friSmoothBatchDoomed params t B stmt pref) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friSmoothBatchGoodStep params t B stmt pref π c} ≤ ε_commit i := by
  cases pref with
  | nil => cases hlen
  | cons head rest =>
    rw [toOuterMeasure_not_friSmoothBatchGoodStep_cons]
    have htail_len : (friBatchTailTranscript rest).length = i.val := by
      simpa [List.length_cons] using hlen
    have hpm : (friBatchTailTranscript rest).length < params.m := htail_len ▸ i.isLt
    have hbound := friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound params hesc
      (stmt.eval head.2.batchCoeffs) (friBatchTailTranscript rest) hpm π hdoomed
    have hidx : (⟨(friBatchTailTranscript rest).length, hpm⟩ : Fin params.m) = i :=
      Fin.ext htail_len
    rwa [hidx] at hbound

/-- Per-round escape budget vector for `(params.m + 2)`-round `friSmoothBatchIOP`: `ε_batch` in
round `0`, `ε_commit i` in folding rounds `1, …, m`, and `((2 ^ d - e - 1) / 2 ^ d) ^ q` in the
final query round `m + 1`. -/
@[expose] noncomputable def friSmoothBatchRoundEscape (params : FRISmoothParams F)
    (ε_batch : ℝ≥0∞) (e : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) : Fin (params.m + 2) → ℝ≥0∞ :=
  Fin.cases ε_batch (friSmoothRoundEscape params e ε_commit)

/-- Summed interactive smooth batched FRI soundness error
`ε_batch + (∑ i : Fin m, ε_commit i) + ((2 ^ d - e - 1) / 2 ^ d) ^ q`. -/
@[expose] noncomputable def friSmoothBatchSumError (params : FRISmoothParams F) (ε_batch : ℝ≥0∞)
    (e : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) : ℝ≥0∞ :=
  ε_batch + friSmoothSumError params e ε_commit

/-- Exact sum of `friSmoothBatchRoundEscape` across all `m + 2` rounds of `friSmoothBatchIOP`. -/
theorem sum_friSmoothBatchRoundEscape_eq (params : FRISmoothParams F) (ε_batch : ℝ≥0∞)
    (e : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) :
    (∑ j : Fin (params.m + 2), friSmoothBatchRoundEscape params ε_batch e ε_commit j) =
      friSmoothBatchSumError params ε_batch e ε_commit := by
  rw [Fin.sum_univ_succ, friSmoothBatchRoundEscape, Fin.cases_zero, friSmoothBatchSumError,
    ← sum_friSmoothRoundEscape_eq_friSmoothSumError]
  rfl

/-- Post-commit single-query acceptance predicate for an `(m + 1)`-round smooth batched commit
prefix `pref` and final committed oracle `πFinal`. -/
@[expose] def friSmoothBatchFinalPasses (params : FRISmoothParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  match pref with
  | [] => False
  | (_, c₀) :: rest =>
    friSmoothFinalPasses params (stmt.eval c₀.batchCoeffs) (friBatchTailTranscript rest) πFinal s

/-- Smooth batched FRI commit-phase game (interactive commit-phase setting of
[BenSassonCarmonIshaiKoppartySaraf2020], Lemma 8.2 on printed pp. 38–39 and Section 8.2.1 on
printed pp. 41–43): runs `m + 1` interactive commit rounds (round `0` batching plus `m` smooth
folding rounds) and samples `πFinal ← P pref`, returning `true` iff strictly more than `B`
starting positions in `Fin (2 ^ d)` pass `friSmoothBatchFinalPasses`. -/
@[expose] noncomputable def friSmoothBatchCommitGame [Fintype F] (params : FRISmoothParams F)
    (t B : ℕ) (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) : PMF Bool :=
  (iopRunRounds P (params.m + 1) []).bind fun pref =>
    (P pref).map fun πFinal =>
      letI : DecidablePred (fun s => friSmoothBatchFinalPasses params t stmt pref πFinal s) :=
        Classical.decPred _
      decide
        (B < (Finset.univ.filter fun s =>
          friSmoothBatchFinalPasses params t stmt pref πFinal s).card)

private theorem friSmoothBatchPerRoundEscape_of_escape [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ} {ε_batch : ℝ≥0∞}
    {ε_commit : Fin params.m → ℝ≥0∞}
    (hbatch : SmoothBatchRound0Escape params t e ε_batch)
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit) :
    ∀ stmt ∉ params.batchProximityLang t e,
      ∀ (j : Fin (params.m + 2)) pref π,
        pref.length = j.val →
        friSmoothBatchDoomed params t (2 ^ params.d - e - 1) stmt pref →
        (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
          {c | ¬ friSmoothBatchGoodStep params t (2 ^ params.d - e - 1) stmt pref π c} ≤
        friSmoothBatchRoundEscape params ε_batch e ε_commit j := by
  intro stmt hfar j pref π hlen hdoomed
  cases j using Fin.cases with
  | zero =>
    rw [List.eq_nil_of_length_eq_zero hlen, friSmoothBatchRoundEscape, Fin.cases_zero]
    exact friSmoothBatchRound0_escape_le_of_escape params t hbatch hfar π
  | succ k =>
    rw [friSmoothBatchRoundEscape, Fin.cases_succ]
    by_cases hk : k.val < params.m
    · simp only [friSmoothRoundEscape, hk, ↓reduceDIte]
      exact friSmoothBatchCommitRound_escape_le_of_weightedCurveEscapePerRound params t hesc stmt
        pref (i := ⟨k.val, hk⟩) hlen π hdoomed
    · have hk_eq : k.val = params.m := by omega
      simpa only [friSmoothRoundEscape, hk, ↓reduceDIte] using
        friSmoothBatchQueryRound_escape_le params t (2 ^ params.d - e - 1) stmt pref
          (by simpa only [Fin.val_succ, hk_eq] using hlen) π hdoomed

/-- **Conditional step (smooth batched FRI commit-phase union bound assuming
`SmoothBatchRound0Escape` and `WeightedCurveEscapePerRound`)**. -/
theorem friSmoothBatchCommitGame_le_of_escape [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ} {ε_batch : ℝ≥0∞}
    {ε_commit : Fin params.m → ℝ≥0∞}
    (hbatch : SmoothBatchRound0Escape params t e ε_batch)
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friSmoothBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ε_batch + ∑ i : Fin params.m, ε_commit i := by
  have hrbr := friSmoothBatchIOP_rbrSound params t e
  refine (iopCommitPhase_map_true_le_sum (hrbr.init_doomed stmt hfar) (hrbr.step_doomed stmt)
    (params.m + 1) (Fin.cases ε_batch ε_commit)
    (fun j pref π hlen hdoomed => ?_) P _
    (fun pref πFinal hlen hdoomed => ?_)).trans_eq (by rw [Fin.sum_univ_succ, Fin.cases_zero]; rfl)
  · have hbound := friSmoothBatchPerRoundEscape_of_escape params t hbatch hesc stmt hfar
      j.castSucc pref π hlen hdoomed
    cases j using Fin.cases with
    | zero => simpa [friSmoothBatchRoundEscape] using hbound
    | succ i =>
      simpa [friSmoothBatchRoundEscape, friSmoothRoundEscape, i.isLt] using hbound
  · cases pref with
    | nil => cases hlen
    | cons head rest =>
      have hcard := card_filter_friSmoothFinalPasses_le_of_friSmoothDoomed params
        (by simpa [List.length_cons] using hlen) πFinal hdoomed
      exact decide_eq_false <| not_lt_of_ge <| (congrArg Finset.card <| Finset.ext fun s => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl).trans_le hcard

/-- **Conditional step (summed interactive soundness for `friSmoothBatchIOP` assuming
`SmoothBatchRound0Escape` and `WeightedCurveEscapePerRound`)**. -/
theorem friSmoothBatchIOP_interactiveGame_le_of_escape [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {e : ℕ} {ε_batch : ℝ≥0∞}
    {ε_commit : Fin params.m → ℝ≥0∞}
    (hbatch : SmoothBatchRound0Escape params t e ε_batch)
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friSmoothBatchIOP params t) stmt P true ≤
      friSmoothBatchSumError params ε_batch e ε_commit :=
  (iopInteractiveGame_le_sum (friSmoothBatchIOP_rbrSound params t e)
    (friSmoothBatchRoundEscape params ε_batch e ε_commit)
    (friSmoothBatchPerRoundEscape_of_escape params t hbatch hesc) hfar P).trans_eq
    (sum_friSmoothBatchRoundEscape_eq params ε_batch e ε_commit)

end SmoothConditionalSummedBridge

section SmoothCommitErrors

variable {F : Type} [Field F]

/-- Closed-form telescoping commit-phase error `(2 - 1 / 2 ^ totalLog) * (2 ^ d / |F|)` across
round-`0` batching (`2 ^ d / |F|`) and all `m` smooth folding rounds
(`(1 - 1 / 2 ^ totalLog) * (2 ^ d / |F|)`) in the unique-decoding regime (`< 2 * 2 ^ d / |F|`
independently of `m`, per-round arities `l⁽ⁱ⁾`, and `t`). -/
@[expose] noncomputable def friSmoothBatchUniqueCommitError [Fintype F]
    (params : FRISmoothParams F) : ℝ :=
  (2 - (1 : ℝ) / (2 : ℝ) ^ params.totalLog) * ((2 ^ params.d : ℝ) / (Fintype.card F : ℝ))


/-- Closed-form telescoping Siegel commit-phase error upper bound across round-`0` batching and all
`m` smooth folding rounds of `friSmoothBatchIOP` with multiplicity parameter `mJ`:
`(2 - 1 / 2 ^ totalLog) * (1800 * (mJ + 1) ^ 6 * (2 ^ d) ^ 2 / ((dim 0 / 2 ^ d) * |F|))`
(bounded independently of `m`, per-round arities `l⁽ⁱ⁾`, and `t`; an original explicit Siegel
finite bound). -/
@[expose] noncomputable def friSmoothBatchJohnsonCommitError [Fintype F]
    (params : FRISmoothParams F) (mJ : ℕ) : ℝ :=
  (2 - (1 : ℝ) / (2 : ℝ) ^ params.totalLog) *
    (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
      (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)))

/-- Closed-form telescoping Siegel `η`-gap commit-phase error upper bound across round-`0` batching
and all `m` smooth folding rounds of `friSmoothBatchIOP`:
`(2 - 1 / 2 ^ totalLog) * (115200 * (2 ^ d) ^ 2 / ((dim 0 / 2 ^ d) * η ^ 6 * |F|))` (using `η`
directly rather than `min(η, √ρ / 20)` in Eq. (1.3)). -/
@[expose] noncomputable def friSmoothBatchJohnsonEtaCommitError [Fintype F]
    (params : FRISmoothParams F) (η : ℝ) : ℝ :=
  (2 - (1 : ℝ) / (2 : ℝ) ^ params.totalLog) *
    (115200 * ((2 ^ params.d : ℝ) ^ 2) /
      (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)))


end SmoothCommitErrors

end Cslib.Crypto.Protocols.FRI
