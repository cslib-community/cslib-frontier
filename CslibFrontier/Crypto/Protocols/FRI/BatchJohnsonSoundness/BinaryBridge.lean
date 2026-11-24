/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness.SmoothBridge

/-!
# Binary 2-to-1 Batched FRI Definitions, Smooth Specialization Bridges, and Conditional Escape

Specializes the smooth batched FRI commit-phase game, escape vector, summed error, and closed-form
commit-error formulas to binary 2-to-1 folding (`FRIParams`, `friBatchIOP`) via `FRIParams.toSmooth`
([BenSassonCarmonIshaiKoppartySaraf2020], Section 8.2).

## Main definitions

* `Cslib.Crypto.Protocols.FRI.friBatchRoundEscape`, `Cslib.Crypto.Protocols.FRI.friBatchSumError`,
  `Cslib.Crypto.Protocols.FRI.friBatchFinalPasses`, `Cslib.Crypto.Protocols.FRI.friBatchCommitGame`:
  binary 2-to-1 batched escape vector, summed error, post-commit query predicate, and commit-phase
  game.
* `Cslib.Crypto.Protocols.FRI.friBatchUniqueCommitError`,
  `Cslib.Crypto.Protocols.FRI.friBatchJohnsonCommitError`,
  `Cslib.Crypto.Protocols.FRI.friBatchJohnsonEtaCommitError`: closed-form `(2 - 1 / 2 ^ m)` binary
  batched commit-phase error bounds.

## Main results

* `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_eq_friSmoothBatchCommitGame`: exact agreement
  between `friBatchCommitGame` and `friSmoothBatchCommitGame` at `params.toSmooth`.
* `Cslib.Crypto.Protocols.FRI.friBatchCommitRound_escape_le_of_weightedLineEscapePerRound`,
  `Cslib.Crypto.Protocols.FRI.sum_friBatchRoundEscape_eq`,
  `Cslib.Crypto.Protocols.FRI.friBatchCommitGame_le_of_escape`,
  `Cslib.Crypto.Protocols.FRI.friBatchIOP_interactiveGame_le_of_escape`: conditional per-round,
  commit-phase, and interactive IOP union bounds for `friBatchIOP`.

## References

* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Finset Cslib.Code Cslib.OracleComp Cslib.Crypto.Protocols.BCS Cslib.Probability

section BinaryBatchBridge

variable {F : Type} [Field F]

/-- Per-round escape budget vector for `(params.m + 2)`-round `friBatchIOP`. -/
noncomputable abbrev friBatchRoundEscape (params : FRIParams F) (ε_batch : ℝ≥0∞)
    (e : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) : Fin (params.m + 2) → ℝ≥0∞ :=
  friSmoothBatchRoundEscape params.toSmooth ε_batch e ε_commit

/-- Summed interactive batched FRI soundness error. -/
noncomputable abbrev friBatchSumError (params : FRIParams F) (ε_batch : ℝ≥0∞)
    (e : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) : ℝ≥0∞ :=
  friSmoothBatchSumError params.toSmooth ε_batch e ε_commit

/-- Post-commit single-query acceptance predicate for an `(m + 1)`-round batched commit prefix
`pref` and final committed oracle `πFinal`. -/
@[expose] def friBatchFinalPasses (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) : Prop :=
  match pref with
  | [] => False
  | (_, c₀) :: rest =>
    friFinalPasses params (stmt.eval c₀.batchCoeffs) (friBatchTailTranscript rest) πFinal s

/-- Batched FRI commit-phase game for binary 2-to-1 `friBatchIOP`. -/
@[expose] noncomputable def friBatchCommitGame [Fintype F] (params : FRIParams F) (t B : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) : PMF Bool :=
  (iopRunRounds P (params.m + 1) []).bind fun pref =>
    (P pref).map fun πFinal =>
      letI : DecidablePred (fun s => friBatchFinalPasses params t stmt pref πFinal s) :=
        Classical.decPred _
      decide
        (B < (Finset.univ.filter fun s => friBatchFinalPasses params t stmt pref πFinal s).card)

/-- Closed-form geometric commit-phase error `(2 - 1 / 2 ^ m) * (2 ^ d / |F|)` in the
unique-decoding regime. -/
@[expose] noncomputable def friBatchUniqueCommitError [Fintype F] (params : FRIParams F) : ℝ :=
  (2 - (1 : ℝ) / (2 : ℝ) ^ params.m) * ((2 ^ params.d : ℝ) / (Fintype.card F : ℝ))

/-- Closed-form geometric Siegel commit-phase error upper bound across round-`0` batching and all
`m` binary folding rounds of `friBatchIOP` with multiplicity parameter `mJ`. -/
@[expose] noncomputable def friBatchJohnsonCommitError [Fintype F]
    (params : FRIParams F) (mJ : ℕ) : ℝ :=
  (2 - (1 : ℝ) / (2 : ℝ) ^ params.m) *
    (1800 * ((mJ + 1 : ℝ) ^ 6) * ((2 ^ params.d : ℝ) ^ 2) /
      (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (Fintype.card F : ℝ)))

/-- Closed-form geometric Siegel `η`-gap commit-phase error upper bound across round-`0` batching
and all `m` binary folding rounds of `friBatchIOP`. -/
@[expose] noncomputable def friBatchJohnsonEtaCommitError [Fintype F]
    (params : FRIParams F) (η : ℝ) : ℝ :=
  (2 - (1 : ℝ) / (2 : ℝ) ^ params.m) *
    (115200 * ((2 ^ params.d : ℝ) ^ 2) /
      (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * (η ^ 6) * (Fintype.card F : ℝ)))

private theorem friBatchFinalPasses_iff_smooth (params : FRIParams F) (t : ℕ)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    friBatchFinalPasses params t stmt pref πFinal s ↔
      friSmoothBatchFinalPasses params.toSmooth t stmt pref πFinal s := by
  cases pref with
  | nil => exact Iff.rfl
  | cons head rest =>
    exact friFinalPasses_iff_friSmoothFinalPasses params (stmt.eval head.2.batchCoeffs)
      (friBatchTailTranscript rest) πFinal s

/-- Exact equality between binary `friBatchCommitGame` and smooth `friSmoothBatchCommitGame` at
`params.toSmooth`. -/
theorem friBatchCommitGame_eq_friSmoothBatchCommitGame [Fintype F] (params : FRIParams F)
    (t B : ℕ) (stmt : FRIBatchStmt F params.d t)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friBatchCommitGame params t B stmt P =
      friSmoothBatchCommitGame params.toSmooth t B stmt P := by
  unfold friBatchCommitGame friSmoothBatchCommitGame
  congr 1
  funext pref
  congr 1
  funext πFinal
  congr 2
  exact congrArg Finset.card <| Finset.ext fun s => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, friBatchFinalPasses_iff_smooth]


/-- **Conditional step (per-round batched folding escape bound assuming
`WeightedLineEscapePerRound`)** (corollary of
`friSmoothBatchCommitRound_escape_le_of_weightedCurveEscapePerRound`). -/
theorem friBatchCommitRound_escape_le_of_weightedLineEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {B : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params B ε_commit)
    (stmt : FRIBatchStmt F params.d t)
    (pref : List (OracleTable params.d F × FRIBatchChal F params.d params.q t))
    {i : Fin params.m} (hlen : pref.length = i.val + 1) (π : OracleTable params.d F)
    (hdoomed : friBatchDoomed params t B stmt pref) :
    (PMF.uniformOfFintype (FRIBatchChal F params.d params.q t)).toOuterMeasure
        {c | ¬ friBatchGoodStep params t B stmt pref π c} ≤ ε_commit i := by
  simp only [friBatchGoodStep_iff_friSmoothBatchGoodStep]
  exact friSmoothBatchCommitRound_escape_le_of_weightedCurveEscapePerRound params.toSmooth t
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params B ε_commit).mp hesc)
    stmt pref hlen π ((friBatchDoomed_iff_friSmoothBatchDoomed params t B stmt pref).mp hdoomed)

/-- Exact sum of `friBatchRoundEscape` across all `m + 2` rounds of `friBatchIOP`. -/
theorem sum_friBatchRoundEscape_eq (params : FRIParams F) (ε_batch : ℝ≥0∞)
    (e : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) :
    (∑ j : Fin (params.m + 2), friBatchRoundEscape params ε_batch e ε_commit j) =
      friBatchSumError params ε_batch e ε_commit :=
  sum_friSmoothBatchRoundEscape_eq params.toSmooth ε_batch e ε_commit

/-- **Conditional step (batched FRI commit-phase union bound assuming `BatchRound0Escape` and
`WeightedLineEscapePerRound`)** (corollary of `friSmoothBatchCommitGame_le_of_escape`). -/
theorem friBatchCommitGame_le_of_escape [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {ε_batch : ℝ≥0∞}
    {ε_commit : Fin params.m → ℝ≥0∞}
    (hbatch : BatchRound0Escape params t e ε_batch)
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    friBatchCommitGame params t (2 ^ params.d - e - 1) stmt P true ≤
      ε_batch + ∑ i : Fin params.m, ε_commit i := by
  rw [friBatchCommitGame_eq_friSmoothBatchCommitGame]
  exact friSmoothBatchCommitGame_le_of_escape params.toSmooth t
    (by simpa only [BatchRound0Escape, SmoothBatchRound0Escape, params.toSmooth_initialCode] using
      hbatch)
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ _).mp hesc)
    (by rwa [params.toSmooth_batchProximityLang]) P

/-- **Conditional step (summed interactive soundness for `friBatchIOP` assuming `BatchRound0Escape`
and `WeightedLineEscapePerRound`)** (corollary of
`friSmoothBatchIOP_interactiveGame_le_of_escape`). -/
theorem friBatchIOP_interactiveGame_le_of_escape [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {e : ℕ} {ε_batch : ℝ≥0∞}
    {ε_commit : Fin params.m → ℝ≥0∞}
    (hbatch : BatchRound0Escape params t e ε_batch)
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : FRIBatchStmt F params.d t} (hfar : stmt ∉ params.batchProximityLang t e)
    (P : InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t)) :
    iopInteractiveGame (friBatchIOP params t) stmt P true ≤
      friBatchSumError params ε_batch e ε_commit := by
  rw [friBatchIOP_eq_friSmoothBatchIOP]
  exact friSmoothBatchIOP_interactiveGame_le_of_escape params.toSmooth t
    (by simpa only [BatchRound0Escape, SmoothBatchRound0Escape, params.toSmooth_initialCode] using
      hbatch)
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ _).mp hesc)
    (by rwa [params.toSmooth_batchProximityLang]) P


end BinaryBatchBridge

end Cslib.Crypto.Protocols.FRI
