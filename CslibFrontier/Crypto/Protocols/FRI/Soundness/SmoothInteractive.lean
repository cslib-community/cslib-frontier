/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.SmoothEscape

/-!
# Smooth FRI Per-Round Escape Aggregation and Summed Interactive Soundness

Combines `friSmoothIOP_rbrSound`, `friSmoothQueryRound_escape_le`, and
`friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound` to bound uniform (`sup`)
round-by-round escape, `friSmoothCommitGame`, and full `iopInteractiveGame (friSmoothIOP params)`.
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

section SmoothInteractiveSoundness

variable {F : Type} [Field F]

private theorem friSmoothCommitRound_escape_le_of_length_eq [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {B : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params B ε_commit)
    (stmt : OracleTable params.d F) (i : Fin params.m)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (π : OracleTable params.d F) (hlen : pref.length = i.val)
    (hdoomed : friSmoothDoomed params B stmt pref) :
    (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params B stmt pref π c} ≤ ε_commit i := by
  have hpm : pref.length < params.m := hlen ▸ i.isLt
  have hbound := friSmoothCommitRound_escape_le_of_weightedCurveEscapePerRound params hesc
    stmt pref hpm π hdoomed
  rwa [show (⟨pref.length, hpm⟩ : Fin params.m) = i from Fin.ext hlen] at hbound

/-- **Conditional step (indexed smooth per-round escape bound assuming
`WeightedCurveEscapePerRound`)**: discharging `WeightedCurveEscapePerRound` is left to the caller.
-/
theorem friSmoothPerRoundEscape_of_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ (j : Fin (params.m + 1)) pref π,
      pref.length = j.val →
      friSmoothDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friSmoothRoundEscape params e ε_commit j := by
  intro stmt _ j pref π hlen hdoomed
  by_cases hj : j.val < params.m
  · simpa only [friSmoothRoundEscape, hj, ↓reduceDIte] using
      friSmoothCommitRound_escape_le_of_length_eq params hesc stmt ⟨j.val, hj⟩ pref π hlen hdoomed
  · have hlen_m : pref.length = params.m := hlen.trans (by omega)
    simpa only [friSmoothRoundEscape, hj, ↓reduceDIte] using
      friSmoothQueryRound_escape_le params (2 ^ params.d - e - 1) stmt pref hlen_m π hdoomed

/-- **Conditional step (all-prefix smooth `sup` RBR escape bound assuming
`WeightedCurveEscapePerRound`)**: discharging `WeightedCurveEscapePerRound` is left to the caller.
-/
theorem friSmoothRBREscape_of_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friSmoothDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friSmoothSupRBRError params e ε_commit :=
  iopEscape_le_sup_of_perRound (friSmoothRoundEscape params e ε_commit)
    (friSmoothPerRoundEscape_of_weightedCurveEscapePerRound params hesc)
    (fun _ _ pref _ _ hge => by
      have hgt : ¬ pref.length ≤ params.m := by omega
      simp only [friSmoothGoodStep, hgt, ↓reduceIte])

/-- **Conditional step (uniform smooth round-by-round escape bound assuming
`WeightedCurveGapBound`)**: discharging `WeightedCurveGapBound` is left to the caller. -/
theorem friSmoothRBREscape_of_weightedCurveGap [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e B_commit : ℕ}
    (hgap : WeightedCurveGapBound params (2 ^ params.d - e - 1) B_commit) :
    ∀ stmt ∉ params.proximityLang e, ∀ pref π,
      friSmoothDoomed params (2 ^ params.d - e - 1) stmt pref →
      (PMF.uniformOfFintype (FRIChal F params.d params.q)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params (2 ^ params.d - e - 1) stmt pref π c} ≤
      friSmoothRBRError params e B_commit :=
  fun stmt hfar pref π hdoomed =>
    (friSmoothRBREscape_of_weightedCurveEscapePerRound params
      (weightedCurveEscapePerRound_of_gapPerRound params hgap) stmt hfar pref π hdoomed).trans
      (friSmoothSupRBRError_const_le_friSmoothRBRError params e B_commit)

/-- **Conditional step (single-word smooth FRI commit-phase union bound assuming
`WeightedCurveEscapePerRound`)**: for `stmt ∉ params.proximityLang e`, `friSmoothCommitGame` exceeds
agreement `B = 2 ^ d - e - 1` with probability at most `∑ i : Fin params.m, ε_commit i`. -/
theorem friSmoothCommitGame_le_of_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friSmoothCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ∑ i : Fin params.m, ε_commit i := by
  have hrbr := friSmoothIOP_rbrSound params e
  refine iopCommitPhase_map_true_le_sum (hrbr.init_doomed stmt hfar) (hrbr.step_doomed stmt)
    params.m ε_commit
    (fun i pref π hlen hdoomed =>
      friSmoothCommitRound_escape_le_of_length_eq params hesc stmt i pref π hlen hdoomed)
    P _ (fun pref πFinal hlen hdoomed => ?_)
  have hcard := card_filter_friSmoothFinalPasses_le_of_friSmoothDoomed params hlen πFinal hdoomed
  have hcongr :
      (@Finset.filter _ (fun s => friSmoothFinalPasses params stmt pref πFinal s)
        (Classical.decPred _) Finset.univ).card =
      (Finset.univ.filter fun s => friSmoothFinalPasses params stmt pref πFinal s).card := by
    congr 2
  exact decide_eq_false (not_lt_of_ge (hcongr.trans_le hcard))

/-- **Conditional step (single-word smooth FRI commit-phase union bound assuming
`WeightedCurveGapPerRound`)**: specializes `friSmoothCommitGame_le_of_weightedCurveEscapePerRound`
to integer bad-scalar budgets `B_commit : Fin params.m → ℕ`. -/
theorem friSmoothCommitGame_le_of_weightedCurveGapPerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedCurveGapPerRound params (2 ^ params.d - e - 1) B_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friSmoothCommitGame params (2 ^ params.d - e - 1) stmt P true ≤
      ∑ i : Fin params.m, (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  friSmoothCommitGame_le_of_weightedCurveEscapePerRound params
    (weightedCurveEscapePerRound_of_gapPerRound params hgap) hfar P

/-- **Conditional step (summed interactive soundness for single-word `friSmoothIOP` assuming
`WeightedCurveEscapePerRound`)**: for `stmt ∉ params.proximityLang e` and any adaptive prover `P`,
`iopInteractiveGame (friSmoothIOP params) stmt P true ≤ friSmoothSumError params e ε_commit`. -/
theorem friSmoothIOP_interactiveGame_le_of_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friSmoothIOP params) stmt P true ≤
      friSmoothSumError params e ε_commit :=
  (iopInteractiveGame_le_sum (friSmoothIOP_rbrSound params e)
    (friSmoothRoundEscape params e ε_commit)
    (friSmoothPerRoundEscape_of_weightedCurveEscapePerRound params hesc) hfar P).trans_eq
    (sum_friSmoothRoundEscape_eq_friSmoothSumError params e ε_commit)

/-- **Conditional step (summed interactive soundness for single-word `friSmoothIOP` assuming
`WeightedCurveGapPerRound`)**: specializes
`friSmoothIOP_interactiveGame_le_of_weightedCurveEscapePerRound` to integer bad-scalar budgets
`B_commit : Fin params.m → ℕ`. -/
theorem friSmoothIOP_interactiveGame_le_of_weightedCurveGapPerRound [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) {e : ℕ} {B_commit : Fin params.m → ℕ}
    (hgap : WeightedCurveGapPerRound params (2 ^ params.d - e - 1) B_commit)
    {stmt : OracleTable params.d F} (hfar : stmt ∉ params.proximityLang e)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    iopInteractiveGame (friSmoothIOP params) stmt P true ≤
      friSmoothSumError params e (fun i => (B_commit i : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  friSmoothIOP_interactiveGame_le_of_weightedCurveEscapePerRound params
    (weightedCurveEscapePerRound_of_gapPerRound params hgap) hfar P


end SmoothInteractiveSoundness

end Cslib.Crypto.Protocols.FRI
