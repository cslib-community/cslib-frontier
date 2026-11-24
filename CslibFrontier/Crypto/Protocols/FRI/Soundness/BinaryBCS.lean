/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.BinaryBridge
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.SmoothBCS

/-!
# Binary 2-to-1 BCS-FRI Random-Oracle Soundness Composition

Derives two-channel BCS random-oracle soundness bounds (`friBCS_romSoundness_bound_of_*`) for
binary 2-to-1 `friIOP` from their smooth `friSmoothIOP` counterparts via `FRIParams.toSmooth`.
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

section BCSROMComposition

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Conditional step (adaptive two-channel binary BCS-FRI ROM soundness assuming
`WeightedLineEscapePerRound`)** (corollary of
`friSmoothBCS_romSoundness_bound_of_weightedCurveEscapePerRound`). -/
theorem friBCS_romSoundness_bound_of_weightedLineEscapePerRound (params : FRIParams F)
    {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSupRBRError params e ε_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friIOP_eq_friSmoothIOP, ← FRIParams.toSmooth_proximityLang] at hMT ⊢
  exact friSmoothBCS_romSoundness_bound_of_weightedCurveEscapePerRound params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    hdec σ hFS hMT

/-- **Conditional step (adaptive two-channel binary BCS-FRI ROM soundness with separate
prover/verifier Merkle budgets assuming `WeightedLineEscapePerRound`)**. -/
theorem friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineEscapePerRound
    (params : FRIParams F) {e : ℕ} {ε_commit : Fin params.m → ℝ≥0∞}
    (hesc : WeightedLineEscapePerRound params (2 ^ params.d - e - 1) ε_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friSupRBRError params e ε_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friIOP_eq_friSmoothIOP, ← FRIParams.toSmooth_proximityLang,
    ← FRIParams.toSmooth_proofOracleQueries]
  exact friSmoothBCS_romSoundness_bound_of_prover_verifier_of_weightedCurveEscapePerRound
    params.toSmooth
    ((weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params _ ε_commit).mp hesc)
    hdec σ hMT hFS hops

/-- **Conditional step (adaptive two-channel binary BCS-FRI ROM soundness assuming
`WeightedLineGapBound`)**. -/
theorem friBCS_romSoundness_bound_of_weightedLineGap (params : FRIParams F)
    {e B_commit : ℕ}
    (hgap : WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friRBRError params e B_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friIOP_eq_friSmoothIOP, ← FRIParams.toSmooth_proximityLang] at hMT ⊢
  exact friSmoothBCS_romSoundness_bound_of_weightedCurveGap params.toSmooth
    ((weightedLineGapPerRound_iff_weightedCurveGapPerRound params _ _).mp hgap)
    hdec σ hFS hMT

/-- **Conditional step (adaptive two-channel binary BCS-FRI ROM soundness with separate
prover/verifier Merkle budgets assuming `WeightedLineGapBound`)**. -/
theorem friBCS_romSoundness_bound_of_prover_verifier_of_weightedLineGap (params : FRIParams F)
    {e B_commit : ℕ}
    (hgap : WeightedLineGapBound params (2 ^ params.d - e - 1) B_commit)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_MT t_FS L_path : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ L_path) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friRBRError params e B_commit +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        ((t_MT + params.proofOracleQueries * (L_path + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + params.proofOracleQueries * (L_path + 1)) +
              (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [friIOP_eq_friSmoothIOP, ← FRIParams.toSmooth_proximityLang,
    ← FRIParams.toSmooth_proofOracleQueries]
  exact friSmoothBCS_romSoundness_bound_of_prover_verifier_of_weightedCurveGap params.toSmooth
    ((weightedLineGapPerRound_iff_weightedCurveGapPerRound params _ _).mp hgap)
    hdec σ hMT hFS hops

/-- **Conditional step (unique-decoding binary BCS-FRI ROM soundness assuming
`UniqueLineGapHypothesis`)**. -/
theorem friBCS_romSoundness_bound_of_uniqueLineGap (params : FRIParams F)
    {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueLineGapHypothesis params e)
    {encSym : F → List Bool} {decSym : List Bool → F}
    (hdec : Function.LeftInverse decSym encSym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F)}
    {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friIOP params) encSym (params.proximityLang e) P) Q_MT) :
    bcsSoundnessGame (friIOP params) encSym (params.proximityLang e) P σ true ≤
      ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
          (friRBRError params e (2 ^ (params.d - 1)) +
            ((t_FS + (params.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal F params.d params.q))) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + (params.m + 1) * (t_FS + (params.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  friBCS_romSoundness_bound_of_weightedLineGap params
    (weightedLineGapBound_of_uniqueLineGap params huniq hgap) hdec σ hFS hMT

end BCSROMComposition

end Cslib.Crypto.Protocols.FRI
