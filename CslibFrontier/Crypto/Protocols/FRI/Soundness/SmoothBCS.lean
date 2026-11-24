/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.SmoothInteractive

/-!
# Smooth BCS-FRI Random-Oracle Soundness Composition

Composes `friSmoothIOP_rbrSound` and the conditional smooth round-by-round escape bounds with the
two-channel BCS random-oracle compiler bounds (`bcsROMSoundness_bound`,
`bcsROMSoundness_bound_of_prover_verifier`) for `friSmoothIOP`.
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

section SmoothBCSROMComposition

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Conditional step (adaptive two-channel smooth BCS-FRI ROM soundness assuming
`WeightedCurveEscapePerRound`)**: composes `friSmoothIOP_rbrSound` and
`friSmoothRBREscape_of_weightedCurveEscapePerRound` (`friSmoothSupRBRError`) with
`Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound` ([BenSassonChiesaSpooner2016],
[BenSassonCarmonIshaiKoppartySaraf2020]); discharging `WeightedCurveEscapePerRound` is left to the
caller. -/
theorem friSmoothBCS_romSoundness_bound_of_weightedCurveEscapePerRound
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothSupRBRError params e ε_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound (friSmoothIOP_rbrSound params e)
    (friSmoothRBREscape_of_weightedCurveEscapePerRound params hesc) hdec 0 σ hFS hMT

/-- **Conditional step (adaptive two-channel smooth BCS-FRI ROM soundness with separate
prover/verifier Merkle budgets assuming `WeightedCurveEscapePerRound`)**: bounds verifier Merkle
cost via `isCostBounded_bcsMTCost_friSmoothVerifyROM` (`q_V = params.proofOracleQueries *
(L_path + 1)`) and composes with
`Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound_of_prover_verifier`; discharging
`WeightedCurveEscapePerRound` is left to the caller. -/
theorem friSmoothBCS_romSoundness_bound_of_prover_verifier_of_weightedCurveEscapePerRound
    (params : FRISmoothParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedCurveEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothSupRBRError params e ε_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound_of_prover_verifier (friSmoothIOP_rbrSound params e)
    (friSmoothRBREscape_of_weightedCurveEscapePerRound params hesc) hdec 0 σ hMT hFS
    (fun x prf hmem =>
      isCostBounded_bcsMTCost_friSmoothVerifyROM params encSym x prf (hops x prf hmem))

/-- **Conditional step (adaptive two-channel smooth BCS-FRI ROM soundness assuming
`WeightedCurveGapBound`)**: discharging `WeightedCurveGapBound` is left to the caller. -/
theorem friSmoothBCS_romSoundness_bound_of_weightedCurveGap (params : FRISmoothParams F)
    {e B_commit : ℕ}
    (hgap : WeightedCurveGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothRBRError params e B_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound (friSmoothIOP_rbrSound params e)
    (friSmoothRBREscape_of_weightedCurveGap params hgap) hdec 0 σ hFS hMT

/-- **Conditional step (adaptive two-channel smooth BCS-FRI ROM soundness with separate
prover/verifier Merkle budgets assuming `WeightedCurveGapBound`)**: discharging
`WeightedCurveGapBound` is left to the caller. -/
theorem friSmoothBCS_romSoundness_bound_of_prover_verifier_of_weightedCurveGap
    (params : FRISmoothParams F) {e B_commit : ℕ}
    (hgap : WeightedCurveGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothRBRError params e B_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound_of_prover_verifier (friSmoothIOP_rbrSound params e)
    (friSmoothRBREscape_of_weightedCurveGap params hgap) hdec 0 σ hMT hFS
    (fun x prf hmem =>
      isCostBounded_bcsMTCost_friSmoothVerifyROM params encSym x prf (hops x prf hmem))

/-- **Conditional step (unique-decoding smooth BCS-FRI ROM soundness assuming
`UniqueCurveGapHypothesis`)**: combines `weightedCurveGapBound_of_uniqueCurveGap`
(`B_commit = 2 ^ d - 2 ^ (d - firstStepLog)`) with
`friSmoothBCS_romSoundness_bound_of_weightedCurveGap`; discharging `UniqueCurveGapHypothesis` is
left to the caller. -/
theorem friSmoothBCS_romSoundness_bound_of_uniqueCurveGap (params : FRISmoothParams F)
    {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueCurveGapHypothesis params e)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friSmoothIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothRBRError params e (2 ^ params.d - 2 ^ (params.d - params.firstStepLog)) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friSmoothBCS_romSoundness_bound_of_weightedCurveGap params
    (weightedCurveGapBound_of_uniqueCurveGap params huniq hgap) hdec σ hFS hMT

end SmoothBCSROMComposition

end Cslib.Crypto.Protocols.FRI
