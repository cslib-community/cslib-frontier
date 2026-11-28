/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

public import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness
public import CslibFrontierTests.Crypto.FRISmooth
public import CslibFrontierTests.Crypto.FRIBatchSoundness
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# Concrete Nonvacuous Tests for Smooth `2^{sᵢ}`-to-1 FRI & Batched FRI Soundness + BCS ROM

Exercises every new smooth soundness, curve proximity-gap, commit-phase, interactive IOP, and
adaptive two-channel BCS random-oracle definition and theorem across `Soundness.lean`,
`JohnsonSoundness.lean`, `BatchSoundness.lean`, and `BatchJohnsonSoundness.lean` from an ordinary
`module` client (no `import all`), covering both `![2, 2]` (pure 4-to-1) and `![3, 1]` (mixed
8-to-1 then 2-to-1) smooth folding schedules:

1. **Suite 1 (`ZMod 257`, unique decoding, `d = 5, n = 32, kFinal = 1, dim 0 = 16, e = 7, q = 6`):**
   Reuses `FRISmooth.lean`'s `params257Fold4x4` (`![2, 2]`, round curve budgets `(24, 6)` summing
   to `30`, round-`0` max `24`) and `params257Fold8x2` (`![3, 1]`, round curve budgets `(28, 2)`
   summing to `30`, round-`0` max `28`) together with `farWord32`, `honestBatchStmt32`, and
   `badBatchStmt32`. Exercises single-word and batched (`t = 2` and `t = 0`) commit games,
   interactive IOP bounds (`< 1 / 3` single-word, `< 1 / 2` batched), RBR soundness, contrapositive
   `friSmoothBatchIOP_sound_of_unique` on an honest causal prover (`Pr = 1`), and adaptive BCS ROM
   soundness (`friSmoothBCS_romSoundness_bound_of_uniqueCurveGap`, `_of_unique`,
   `_of_prover_verifier_of_unique`, `friSmoothBatchBCS_romSoundness_bound_of_unique`,
   `_of_prover_verifier_of_unique`, `_corrAgree_romSoundness_bound_of_unique`).
2. **Suite 2 (`ZMod goldilocksP`, beyond unique decoding, `d = 6, n = 64, ω = 8, kFinal = 1,
   dim 0 = 16, ρ = 1 / 4, e = 25 > 24, mJ = 3, η = 1 / 12, α = 3 / 5, q = 5, t = 2`):**
   Both `paramsGold4x4` (`![2, 2]`: `64 → 16 → 4`, `dim: 16 → 4 → 1`) and `paramsGold8x2`
   (`![3, 1]`: `64 → 8 → 4`, `dim: 16 → 2 → 1`). Exercises discrete Guruswami–Sudan (`m₀ = 1`,
   `D₀ = 38`, `mRound = ![1, 1]`, `DRound = ![9, 2]` / `![4, 2]`), closed-form Johnson (`mJ = 3`),
   all smooth `η`-gap theorems (`friSmoothJohnsonEtaCommitBound`,
   `weightedCurveGapBound_of_johnson_eta`, `friSmoothBatchJohnsonEtaCommitError`,
   `friSmoothBatchCommitGame_proximity_le_of_johnson_eta`,
   `friSmoothBatchCommitGame_le_of_johnson_eta`,
   `friSmoothBatchIOP_interactiveGame_proximity_le_of_johnson_eta`,
   `friSmoothBatchIOP_interactiveGame_le_of_johnson_eta`, `friSmoothBatchIOP_sound_of_johnson_eta`,
   `friSmoothBatchBCS_romSoundness_bound_of_johnson_eta`,
   `FRI.friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_eta`), an honest causal
   prover (`Pr = 1`) discharging contrapositive `friSmoothBatchIOP_sound_of_johnson` and `_eta`, a
   prefix-dependent adaptive prover (`adaptiveSmoothBatchProverGold`, deterministic: each
   conditional distribution is a point mass) with explicit witnesses that its output depends on
   the transcript, and all adaptive two-channel BCS ROM bounds (`< 1 / 4` single-word, `< 1 / 3`
   batched at `σ = 32`).
3. **Suite 3 (Binary-specialization soundness bridges):**
   Direct checks on `friDoomed_iff_friSmoothDoomed`, `friGoodStep_iff_friSmoothGoodStep`,
   `friCommitGame_eq_friSmoothCommitGame`, `weightedLineGapPerRound_iff_weightedCurveGapPerRound`,
   `weightedLineEscapePerRound_iff_weightedCurveEscapePerRound`,
   `friBatchDoomed_iff_friSmoothBatchDoomed`, `friBatchGoodStep_iff_friSmoothBatchGoodStep`, and
   `friBatchCommitGame_eq_friSmoothBatchCommitGame`.
-/

namespace CslibFrontierTests.Crypto.FRISmoothSoundness

open scoped BigOperators NNReal ENNReal
open Finset Polynomial
open Cslib Cslib.Code Cslib.OracleComp Cslib.Probability
open Cslib.Crypto.Protocols.BCS Cslib.Crypto.Protocols.FRI
open CslibFrontierTests.Crypto.FRI
open CslibFrontierTests.Crypto.FRIJohnson
open CslibFrontierTests.Crypto.FRIBatchSoundness
open CslibFrontierTests.Crypto.FRISmooth

/-! ### Reusable Smooth Cheater, Honest Causal Prover, and Far-Monomial Helpers -/

section Helpers

/-- Concrete single-word BCS cheating prover for `friSmoothIOP` (0 FS queries, 0 MT queries, empty
openings). -/
def mkSmoothCheater {F : Type} [Field F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F) :
    OracleComp (BCSROMSpec (OracleTable params.d F) (FRIChal F params.d params.q))
      (OracleTable params.d F × BCSProof (params.m + 1) F) :=
  pure (stmt, ⟨fun _ => [], []⟩)

private theorem isCostBounded_FS_mkSmoothCheater {F : Type} [Field F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F) :
    IsCostBounded bcsFSCost (mkSmoothCheater params stmt) 0 :=
  IsCostBounded.pure (cost := bcsFSCost) _ 0

private theorem isCostBounded_MT_mkSmoothCheater {F : Type} [Field F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F) :
    IsCostBounded bcsMTCost (mkSmoothCheater params stmt) 0 :=
  IsCostBounded.pure (cost := bcsMTCost) _ 0

private theorem mkSmoothCheater_openings_le {F : Type} [Field F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F) :
    ∀ x prf, (x, prf) ∈ (mkSmoothCheater params stmt).support →
      ∀ op ∈ prf.openings, op.path.length ≤ 0 := by
  intro x prf hmem op hop
  simp only [mkSmoothCheater, supportWith_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, rfl⟩
  cases hop

private theorem isCostBounded_soundnessProg_mkSmoothCheater {F : Type} [Field F] [DecidableEq F]
    (params : FRISmoothParams F) (encSym : F → List Bool) (L : Set (OracleTable params.d F))
    (stmt : OracleTable params.d F) {Q_MT : ℕ} (hQ : params.proofOracleQueries ≤ Q_MT) :
    IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothIOP params) encSym L (mkSmoothCheater params stmt)) Q_MT :=
  (isCostBounded_bcsMTCost_bcsSoundnessProg (friSmoothIOP params) encSym L
    (isCostBounded_MT_mkSmoothCheater params stmt) fun x prf hmem =>
      isCostBounded_bcsMTCost_friSmoothVerifyROM params encSym x prf
        (mkSmoothCheater_openings_le params stmt x prf hmem)).mono (by simpa using hQ)

/-- Concrete batched BCS cheating prover for `friSmoothBatchIOP` (0 FS queries, 0 MT queries, empty
openings). -/
def mkSmoothBatchCheater {F : Type} [Field F] (params : FRISmoothParams F) {t : ℕ}
    (stmt : FRIBatchStmt F params.d t) :
    OracleComp (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F) :=
  pure (stmt, ⟨fun _ => [], []⟩)

private theorem isCostBounded_FS_mkSmoothBatchCheater {F : Type} [Field F]
    (params : FRISmoothParams F) {t : ℕ} (stmt : FRIBatchStmt F params.d t) :
    IsCostBounded bcsFSCost (mkSmoothBatchCheater params stmt) 0 :=
  IsCostBounded.pure (cost := bcsFSCost) _ 0

private theorem isCostBounded_MT_mkSmoothBatchCheater {F : Type} [Field F]
    (params : FRISmoothParams F) {t : ℕ} (stmt : FRIBatchStmt F params.d t) :
    IsCostBounded bcsMTCost (mkSmoothBatchCheater params stmt) 0 :=
  IsCostBounded.pure (cost := bcsMTCost) _ 0

private theorem mkSmoothBatchCheater_openings_le {F : Type} [Field F]
    (params : FRISmoothParams F) {t : ℕ} (stmt : FRIBatchStmt F params.d t) :
    ∀ x prf, (x, prf) ∈ (mkSmoothBatchCheater params stmt).support →
      ∀ op ∈ prf.openings, op.path.length ≤ 0 := by
  intro x prf hmem op hop
  simp only [mkSmoothBatchCheater, supportWith_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, rfl⟩
  cases hop

private theorem isCostBounded_soundnessProg_mkSmoothBatchCheater {F : Type} [Field F]
    [DecidableEq F] (params : FRISmoothParams F) (encSym : F → List Bool) {t : ℕ}
    (L : Set (FRIBatchStmt F params.d t)) (stmt : FRIBatchStmt F params.d t)
    {Q_MT : ℕ} (hQ : params.proofOracleQueries ≤ Q_MT) :
    IsCostBounded bcsMTCost
      (bcsSoundnessProg (friSmoothBatchIOP params t) encSym L
        (mkSmoothBatchCheater params stmt)) Q_MT :=
  (isCostBounded_bcsMTCost_bcsSoundnessProg (friSmoothBatchIOP params t) encSym L
    (isCostBounded_MT_mkSmoothBatchCheater params stmt) fun x prf hmem =>
      isCostBounded_bcsMTCost_friSmoothBatchVerifyROM params t encSym x prf
        (mkSmoothBatchCheater_openings_le params stmt x prf hmem)).mono (by simpa using hQ)

/-- Lift the honest `friSmoothBatchIOP` round prover on `stmt` to an `InteractiveIOPProver`. -/
noncomputable def honestCausalSmoothBatchProver {F : Type} [Field F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) (stmt : FRIBatchStmt F params.d t) :
    InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t) :=
  InteractiveIOPProver.ofCausal fun j prev =>
    (friSmoothBatchIOP params t).proveRound j stmt () prev

private theorem iopInteractiveGame_honestCausalSmoothBatchProver_true_eq_one
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (params : FRISmoothParams F) (t : ℕ) {stmt : FRIBatchStmt F params.d t}
    (hrel : params.batchCompletenessRel t stmt ()) :
    iopInteractiveGame (friSmoothBatchIOP params t) stmt
      (honestCausalSmoothBatchProver params t stmt) true = 1 := by
  have hgame :
      iopInteractiveGame (friSmoothBatchIOP params t) stmt
        (honestCausalSmoothBatchProver params t stmt) = PMF.pure true := by
    rw [honestCausalSmoothBatchProver, iopInteractiveGame_ofCausal_eq]
    have hacc :
        (fun chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t =>
          iopVerify (friSmoothBatchIOP params t) stmt chals
            (fun j => (friSmoothBatchIOP params t).proveRound j stmt ()
              fun i => chals ⟨i.val, lt_trans i.isLt j.isLt⟩)) =
        Function.const _ true := by
      funext chals
      exact friSmoothBatchIOP_complete params t stmt () hrel chals
    rw [hacc, PMF.map_const]
  rw [hgame, PMF.pure_apply]
  simp only [↓reduceIte]

private theorem card_agree_monomial_le_smooth {F : Type} [Field F] [DecidableEq F]
    (params : FRISmoothParams F) {deg : ℕ} (hdeg : params.dim 0 ≤ deg)
    {c : OracleTable params.d F} (hc : c ∈ params.initialCode) :
    (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
      (params.eval 0 s) ^ deg = c s).card ≤ deg := by
  obtain ⟨p, hp, hpeq⟩ := mem_reedSolomon.mp hc
  have hne : (X ^ deg : Polynomial F) ≠ p := by
    intro heq
    have h1 : (X ^ deg : Polynomial F).degree = (deg : WithBot ℕ) := Polynomial.degree_X_pow deg
    rw [heq] at h1
    have h2 : (deg : WithBot ℕ) < (params.dim 0 : WithBot ℕ) := h1 ▸ hp
    have h3 : deg < params.dim 0 := by exact_mod_cast h2
    omega
  have hP_deg : (X ^ deg : Polynomial F).natDegree ≤ deg := (Polynomial.natDegree_X_pow deg).le
  have hQ_deg : p.natDegree ≤ deg := by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp only [Polynomial.natDegree_zero, Nat.zero_le]
    · have hpnat : p.natDegree < params.dim 0 := by
        rw [Polynomial.degree_eq_natDegree hp0] at hp
        exact_mod_cast hp
      omega
  have hα : Function.Injective (params.eval 0) :=
    cosetEval_injective params.hg params.hω (Nat.zero_le params.d)
  have hle := card_filter_eval_eq_eval_le hα hP_deg hQ_deg hne
  have hfilt :
      (Finset.univ.filter fun s : Fin (2 ^ params.d) => (params.eval 0 s) ^ deg = c s) =
      Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        (X ^ deg : Polynomial F).eval (params.eval 0 s) = p.eval (params.eval 0 s) := by
    ext s
    have hcs : c s = p.eval (params.eval 0 s) := (congrFun hpeq s).symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcs, Polynomial.eval_pow,
      Polynomial.eval_X]
  rw [hfilt]
  exact hle

end Helpers

/-! ### Suite 1: Smooth Unique Decoding (`ZMod 257`, `![2, 2]` 4-to-1 & `![3, 1]` 8+2-to-1) -/

section SmoothUnique257

/-- Batch-size-`0` far statement over `ZMod 257` (`d = 5`) for exercising `t = 0` bounds. -/
def badBatchStmt32Zero : FRIBatchStmt (ZMod 257) 5 0 where
  base := farWord32
  terms := Fin.elim0

private theorem rate257_le_three_quarters (params : FRISmoothParams (ZMod 257))
    (hd : params.d = 5) (hdim : params.dim 0 = 16) :
    (1 + (params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) / 2 ≤ 3 / 4 := by
  rw [hdim, hd]; norm_num

private theorem badBatchStmt32Zero_not_mem_4x4 :
    badBatchStmt32Zero ∉ params257Fold4x4.batchProximityLang 0 7 := fun h =>
  farWord32_not_mem_proximityLang_4x4
    ((mem_friBatchProximityLang_zero_iff params257Fold4x4.initialCode 7 badBatchStmt32Zero).mp h)

private theorem badBatchStmt32_not_mem_corrAgree_4x4 :
    badBatchStmt32 ∉ params257Fold4x4.batchCorrAgreeLang 2 (3 / 4) := by
  rintro ⟨D', hdens, _, _, v, hv, hagree⟩
  have hle : D'.card ≤ 16 :=
    card_agree_farWord32_le_16 (hv 1) fun s hs => (hagree s hs).2 1
  have hleR : (D'.card : ℝ) ≤ 16 := by exact_mod_cast hle
  have hd : (2 ^ params257Fold4x4.d : ℝ) = 32 := by norm_num [params257Fold4x4]
  rw [hd] at hdens
  linarith

private theorem badBatchStmt32_not_mem_corrAgree_8x2 :
    badBatchStmt32 ∉ params257Fold8x2.batchCorrAgreeLang 2 (3 / 4) :=
  badBatchStmt32_not_mem_corrAgree_4x4

private theorem friSmoothUniqueCommitError_257_eq_4x4 :
    friSmoothUniqueCommitError params257Fold4x4 = (30 : ℝ) / 257 := by
  simp only [friSmoothUniqueCommitError, params257Fold4x4, mkParams257Smooth,
    FRISmoothParams.totalLog, FRISmoothParams.cumLog, ZMod.card]
  norm_num [friCumLog]

private theorem friSmoothBatchUniqueCommitError_257_eq_4x4 :
    friSmoothBatchUniqueCommitError params257Fold4x4 = (62 : ℝ) / 257 := by
  simp only [friSmoothBatchUniqueCommitError, params257Fold4x4, mkParams257Smooth,
    FRISmoothParams.totalLog, FRISmoothParams.cumLog, ZMod.card]
  norm_num [friCumLog]

private theorem friSmoothBatchUniqueCommitError_257_eq_8x2 :
    friSmoothBatchUniqueCommitError params257Fold8x2 = (62 : ℝ) / 257 := by
  simp only [friSmoothBatchUniqueCommitError, params257Fold8x2, mkParams257Smooth,
    FRISmoothParams.totalLog, FRISmoothParams.cumLog, ZMod.card]
  norm_num [friCumLog]

-- Single-word smooth commit game, interactive IOP (`< 1 / 3`), and RBR soundness for `![2, 2]` and
-- `![3, 1]`.
theorem smooth257_4x4_single_interactive_lt_third
    (P : InteractiveIOPProver 5 (ZMod 257) (FRIChal (ZMod 257) 5 6)) :
    friSmoothCommitGame params257Fold4x4 24 farWord32 P true ≤ (30 : ℝ≥0∞) / 257 ∧
    iopInteractiveGame (friSmoothIOP params257Fold4x4) farWord32 P true < 1 / 3 := by
  have hcg := friSmoothCommitGame_le_of_unique params257Fold4x4 (e := 7) (by decide)
    farWord32_not_mem_proximityLang_4x4 P
  have hiop := friSmoothIOP_interactiveGame_le_of_unique params257Fold4x4 (e := 7) (by decide)
    farWord32_not_mem_proximityLang_4x4 P
  have h30 : ((2 ^ params257Fold4x4.d - 2 ^ (params257Fold4x4.d - params257Fold4x4.totalLog) :
      ℕ) : ℝ≥0∞) = 30 := by
    have : 2 ^ params257Fold4x4.d - 2 ^ (params257Fold4x4.d - params257Fold4x4.totalLog) = 30 := by
      decide
    rw [this]; norm_num
  have hcard : (Fintype.card (ZMod 257) : ℝ≥0∞) = 257 := by simp only [ZMod.card, Nat.cast_ofNat]
  refine ⟨by rw [h30, hcard] at hcg; exact hcg, lt_of_le_of_lt hiop ?_⟩
  rw [h30, hcard]
  have hlt : (30 / 257 + (24 / 32) ^ 6 : ℝ≥0) < 1 / 3 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (32 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one, params257Fold4x4, mkParams257Smooth,
    (by norm_num : ((2 ^ 5 - 7 - 1 : ℕ) : ℝ≥0∞) = 24),
    (by norm_num : (2 : ℝ≥0∞) ^ 5 = 32)] using ENNReal.coe_lt_coe.mpr hlt

theorem smooth257_8x2_single_interactive_lt_third
    (P : InteractiveIOPProver 5 (ZMod 257) (FRIChal (ZMod 257) 5 6)) :
    friSmoothCommitGame params257Fold8x2 24 farWord32 P true ≤ (30 : ℝ≥0∞) / 257 ∧
    iopInteractiveGame (friSmoothIOP params257Fold8x2) farWord32 P true < 1 / 3 := by
  have hcg := friSmoothCommitGame_le_of_unique params257Fold8x2 (e := 7) (by decide)
    farWord32_not_mem_proximityLang_8x2 P
  have hiop := friSmoothIOP_interactiveGame_le_of_unique params257Fold8x2 (e := 7) (by decide)
    farWord32_not_mem_proximityLang_8x2 P
  have h30 : ((2 ^ params257Fold8x2.d - 2 ^ (params257Fold8x2.d - params257Fold8x2.totalLog) :
      ℕ) : ℝ≥0∞) = 30 := by
    have : 2 ^ params257Fold8x2.d - 2 ^ (params257Fold8x2.d - params257Fold8x2.totalLog) = 30 := by
      decide
    rw [this]; norm_num
  have hcard : (Fintype.card (ZMod 257) : ℝ≥0∞) = 257 := by simp only [ZMod.card, Nat.cast_ofNat]
  refine ⟨by rw [h30, hcard] at hcg; exact hcg, lt_of_le_of_lt hiop ?_⟩
  rw [h30, hcard]
  have hlt : (30 / 257 + (24 / 32) ^ 6 : ℝ≥0) < 1 / 3 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (32 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one, params257Fold8x2, mkParams257Smooth,
    (by norm_num : ((2 ^ 5 - 7 - 1 : ℕ) : ℝ≥0∞) = 24),
    (by norm_num : (2 : ℝ≥0∞) ^ 5 = 32)] using ENNReal.coe_lt_coe.mpr hlt

-- Exercise `friSmoothIOP_rbrSound_of_unique` on both schedules.
example :
    IOPRoundByRoundSoundness (friSmoothIOP params257Fold4x4) (params257Fold4x4.proximityLang 7)
      (friSmoothDoomed params257Fold4x4 24) (friSmoothGoodStep params257Fold4x4 24) ∧
    ∀ stmt ∉ params257Fold4x4.proximityLang 7, ∀ pref π,
      friSmoothDoomed params257Fold4x4 24 stmt pref →
      (PMF.uniformOfFintype (FRIChal (ZMod 257) 5 6)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params257Fold4x4 24 stmt pref π c} ≤
      friSmoothRBRError params257Fold4x4 7 24 :=
  friSmoothIOP_rbrSound_of_unique params257Fold4x4 (e := 7) (by decide)

example :
    IOPRoundByRoundSoundness (friSmoothIOP params257Fold8x2) (params257Fold8x2.proximityLang 7)
      (friSmoothDoomed params257Fold8x2 24) (friSmoothGoodStep params257Fold8x2 24) ∧
    ∀ stmt ∉ params257Fold8x2.proximityLang 7, ∀ pref π,
      friSmoothDoomed params257Fold8x2 24 stmt pref →
      (PMF.uniformOfFintype (FRIChal (ZMod 257) 5 6)).toOuterMeasure
        {c | ¬ friSmoothGoodStep params257Fold8x2 24 stmt pref π c} ≤
      friSmoothRBRError params257Fold8x2 7 28 :=
  friSmoothIOP_rbrSound_of_unique params257Fold8x2 (e := 7) (by decide)

-- Single-word BCS ROM unique-decoding tests (`friSmoothBCS_romSoundness_bound_of_uniqueCurveGap`,
-- `friSmoothBCS_romSoundness_bound_of_unique`,
-- `friSmoothBCS_romSoundness_bound_of_prover_verifier_of_unique`).
private theorem friSmooth257_rbrError_eq (params : FRISmoothParams (ZMod 257)) (hd : params.d = 5)
    (hq : params.q = 6) (B_c : ℕ) (hBc : B_c ≤ 32) :
    friSmoothRBRError params 7 B_c = (729 : ℝ≥0∞) / 4096 := by
  have h1_nn : ((B_c : ℝ≥0) / 257) ≤ 729 / 4096 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have hBcR : (B_c : ℝ) ≤ 32 := by exact_mod_cast hBc
    linarith
  have h1 : (B_c : ℝ≥0∞) / 257 ≤ 729 / 4096 := by
    simpa only [ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (4096 : ℝ≥0) ≠ 0),
      ENNReal.coe_natCast, ENNReal.coe_ofNat] using ENNReal.coe_le_coe.mpr h1_nn
  have hpow : (((24 : ℝ≥0∞) / 32) ^ 6) = (729 : ℝ≥0∞) / 4096 := by
    have hnn : ((24 / 32 : ℝ≥0) ^ 6) = 729 / 4096 := by
      rw [← NNReal.coe_inj]; push_cast; norm_num
    simpa only [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (32 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (4096 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      congrArg ENNReal.ofNNReal hnn
  have hcard : (Fintype.card (ZMod 257) : ℝ≥0∞) = 257 := by simp only [ZMod.card, Nat.cast_ofNat]
  simp only [friSmoothRBRError, hd, hq, hcard,
    (by norm_num : ((2 ^ 5 - 7 - 1 : ℕ) : ℝ≥0∞) = 24),
    (by norm_num : (2 : ℝ≥0∞) ^ 5 = 32), hpow, max_eq_right h1]

private theorem card_friChal257_32 (params : FRISmoothParams (ZMod 257)) (hd : params.d = 5)
    (hq : params.q = 6) :
    (Fintype.card (FRIChal (ZMod 257) params.d params.q) : ℝ≥0∞) = 275951648768 := by
  rw [card_friChal, ZMod.card, hd, hq]
  norm_num

private theorem card_friBatchChal257_32 (params : FRISmoothParams (ZMod 257)) (hd : params.d = 5)
    (hq : params.q = 6) :
    (Fintype.card (FRIBatchChal (ZMod 257) params.d params.q 2) : ℝ≥0∞) = 18226330449477632 := by
  rw [card_friBatchChal, ZMod.card, hd, hq]
  norm_num

theorem smooth257_4x4_bcs_single_lt_three_fifths :
    bcsSoundnessGame (friSmoothIOP params257Fold4x4) (encZMod (p := 257))
      (params257Fold4x4.proximityLang 7) (mkSmoothCheater params257Fold4x4 farWord32) 32 true <
      3 / 5 := by
  refine lt_of_le_of_lt
    (friSmoothBCS_romSoundness_bound_of_unique params257Fold4x4 (e := 7) (by decide)
      (leftInverse_decZMod_encZMod 257) 32
      (isCostBounded_FS_mkSmoothCheater params257Fold4x4 farWord32)
      (isCostBounded_soundnessProg_mkSmoothCheater params257Fold4x4 (encZMod (p := 257))
        (params257Fold4x4.proximityLang 7) farWord32 (by decide : _ ≤ 73))) ?_
  have hrbr : friSmoothRBRError params257Fold4x4 7
      (2 ^ params257Fold4x4.d - 2 ^ (params257Fold4x4.d - params257Fold4x4.firstStepLog)) =
      (729 : ℝ≥0∞) / 4096 := friSmooth257_rbrError_eq params257Fold4x4 rfl rfl 24 (by decide)
  rw [hrbr, card_friChal257_32 _ rfl rfl, show params257Fold4x4.m = 2 from rfl]
  have hnn : (3 * (729 / 4096 + 3 * (1 / 275951648768)) +
      73 * (228 * (1 / 4294967296)) : ℝ≥0) < 3 / 5 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_mul,
    ENNReal.coe_div (by norm_num : (4096 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (275951648768 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (5 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one, params257Fold4x4, mkParams257Smooth, Nat.cast_ofNat,
    (by norm_num : ((0 + (2 + 1) : ℕ) : ℝ≥0∞) = 3),
    (by norm_num : ((3 * 73 + (2 + 1) * (0 + (2 + 1)) : ℕ) : ℝ≥0∞) = 228),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using ENNReal.coe_lt_coe.mpr hnn

-- Also exercise `friSmoothBCS_romSoundness_bound_of_prover_verifier_of_unique` on `8x2` and
-- `friSmoothBCS_romSoundness_bound_of_uniqueCurveGap` on `4x4`.
example :
    bcsSoundnessGame (friSmoothIOP params257Fold8x2) (encZMod (p := 257))
      (params257Fold8x2.proximityLang 7) (mkSmoothCheater params257Fold8x2 farWord32) 32 true <
      3 / 5 := by
  refine lt_of_le_of_lt
    (friSmoothBCS_romSoundness_bound_of_prover_verifier_of_unique params257Fold8x2 (e := 7)
      (by decide) (leftInverse_decZMod_encZMod 257) 32
      (isCostBounded_MT_mkSmoothCheater params257Fold8x2 farWord32)
      (isCostBounded_FS_mkSmoothCheater params257Fold8x2 farWord32)
      (mkSmoothCheater_openings_le params257Fold8x2 farWord32)) ?_
  have hrbr : friSmoothRBRError params257Fold8x2 7
      (2 ^ params257Fold8x2.d - 2 ^ (params257Fold8x2.d - params257Fold8x2.firstStepLog)) =
      (729 : ℝ≥0∞) / 4096 :=
    friSmooth257_rbrError_eq params257Fold8x2 rfl rfl 28 (by decide)
  have hpq : params257Fold8x2.proofOracleQueries = 85 := by decide
  rw [hrbr, card_friChal257_32 _ rfl rfl, hpq, show params257Fold8x2.m = 2 from rfl]
  have hnn : (3 * (729 / 4096 + 3 * (1 / 275951648768)) +
      85 * (264 * (1 / 4294967296)) : ℝ≥0) < 3 / 5 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_mul,
    ENNReal.coe_div (by norm_num : (4096 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (275951648768 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (5 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one, params257Fold8x2, mkParams257Smooth,
    (by norm_num : ((0 + (2 + 1) : ℕ) : ℝ≥0∞) = 3),
    (by norm_num : ((0 + 85 * (0 + 1) : ℕ) : ℝ≥0∞) = 85),
    (by norm_num : ((3 * (0 + 85 * (0 + 1)) + (2 + 1) * (0 + (2 + 1)) : ℕ) : ℝ≥0∞) = 264),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using ENNReal.coe_lt_coe.mpr hnn

example (hgap : UniqueCurveGapHypothesis params257Fold4x4 7) :
    bcsSoundnessGame (friSmoothIOP params257Fold4x4) (encZMod (p := 257))
      (params257Fold4x4.proximityLang 7) (mkSmoothCheater params257Fold4x4 farWord32) 32 true ≤
      ((0 + (params257Fold4x4.m + 1) : ℕ) : ℝ≥0∞) *
          (friSmoothRBRError params257Fold4x4 7
              (2 ^ params257Fold4x4.d -
                2 ^ (params257Fold4x4.d - params257Fold4x4.firstStepLog)) +
            ((0 + (params257Fold4x4.m + 1) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIChal (ZMod 257) 5 6))) +
        (73 : ℝ≥0∞) *
          (((3 * 73 + (params257Fold4x4.m + 1) * (0 + (params257Fold4x4.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ 32)) :=
  friSmoothBCS_romSoundness_bound_of_uniqueCurveGap params257Fold4x4 (e := 7) (by decide) hgap
    (leftInverse_decZMod_encZMod 257) 32
    (isCostBounded_FS_mkSmoothCheater params257Fold4x4 farWord32)
    (isCostBounded_soundnessProg_mkSmoothCheater params257Fold4x4 (encZMod (p := 257))
      (params257Fold4x4.proximityLang 7) farWord32 (by decide : _ ≤ 73))

-- Batched smooth unique-decoding commit game (`t = 2` and `t = 0`), interactive IOP (`< 1 / 2`),
-- contrapositive `friSmoothBatchIOP_sound_of_unique`, and BCS ROM bounds for both schedules.
theorem smooth257_4x4_batch_interactive_lt_half
    (P : InteractiveIOPProver 5 (ZMod 257) (FRIBatchChal (ZMod 257) 5 6 2)) :
    friSmoothBatchCommitGame params257Fold4x4 2 24 badBatchStmt32 P true ≤ (62 : ℝ≥0∞) / 257 ∧
    iopInteractiveGame (friSmoothBatchIOP params257Fold4x4 2) badBatchStmt32 P true < 1 / 2 := by
  have hcg := friSmoothBatchCommitGame_proximity_le_of_unique params257Fold4x4 2 (e := 7)
    (by decide) badBatchStmt32_not_mem_batchProximityLang_4x4 P
  have hiop := friSmoothBatchIOP_interactiveGame_proximity_le_of_unique params257Fold4x4 2 (e := 7)
    (by decide) badBatchStmt32_not_mem_batchProximityLang_4x4 P
  have h62 : ((2 * 2 ^ params257Fold4x4.d -
      2 ^ (params257Fold4x4.d - params257Fold4x4.totalLog) : ℕ) : ℝ≥0∞) = 62 := by
    have : 2 * 2 ^ params257Fold4x4.d -
        2 ^ (params257Fold4x4.d - params257Fold4x4.totalLog) = 62 := by decide
    rw [this]; norm_num
  have hcard : (Fintype.card (ZMod 257) : ℝ≥0∞) = 257 := by simp only [ZMod.card, Nat.cast_ofNat]
  refine ⟨by rw [h62, hcard] at hcg; exact hcg, lt_of_le_of_lt hiop ?_⟩
  rw [h62, hcard]
  have hlt : (62 / 257 + (24 / 32) ^ 6 : ℝ≥0) < 1 / 2 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (32 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one, params257Fold4x4, mkParams257Smooth,
    (by norm_num : ((2 ^ 5 - 7 - 1 : ℕ) : ℝ≥0∞) = 24),
    (by norm_num : (2 : ℝ≥0∞) ^ 5 = 32)] using ENNReal.coe_lt_coe.mpr hlt

example (P : InteractiveIOPProver 5 (ZMod 257) (FRIBatchChal (ZMod 257) 5 6 0)) :
    friSmoothBatchCommitGame params257Fold4x4 0 24 badBatchStmt32Zero P true ≤
      (62 : ℝ≥0∞) / 257 := by
  have hcg := friSmoothBatchCommitGame_proximity_le_of_unique params257Fold4x4 0 (e := 7)
    (by decide) badBatchStmt32Zero_not_mem_4x4 P
  have h62 : ((2 * 2 ^ params257Fold4x4.d -
      2 ^ (params257Fold4x4.d - params257Fold4x4.totalLog) : ℕ) : ℝ≥0∞) = 62 := by
    have : 2 * 2 ^ params257Fold4x4.d -
        2 ^ (params257Fold4x4.d - params257Fold4x4.totalLog) = 62 := by decide
    rw [this]; norm_num
  have hcard : (Fintype.card (ZMod 257) : ℝ≥0∞) = 257 := by simp only [ZMod.card, Nat.cast_ofNat]
  rw [h62, hcard] at hcg
  exact hcg

-- Real-`α` unique-decoding batched interactive bound & contrapositive
-- `friSmoothBatchIOP_sound_of_unique`
-- on both `![2, 2]` and `![3, 1]`.
theorem smooth257_8x2_batch_real_lt_half
    (P : InteractiveIOPProver 5 (ZMod 257) (FRIBatchChal (ZMod 257) 5 6 2)) :
    iopInteractiveGame (friSmoothBatchIOP params257Fold8x2 2) badBatchStmt32 P true < 1 / 2 := by
  refine lt_of_le_of_lt
    (friSmoothBatchIOP_interactiveGame_le_of_unique params257Fold8x2 2 (α := 3 / 4)
      (rate257_le_three_quarters params257Fold8x2 rfl (by decide))
      badBatchStmt32_not_mem_corrAgree_8x2 P) ?_
  rw [friSmoothBatchUniqueCommitError_257_eq_8x2]
  have hlt : ENNReal.ofReal ((62 : ℝ) / 257 + (3 / 4 : ℝ) ^ params257Fold8x2.q) <
      ENNReal.ofReal ((1 : ℝ) / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
      (by norm_num [params257Fold8x2, mkParams257Smooth])
  have hrhs : ENNReal.ofReal ((1 : ℝ) / 2) = (1 : ℝ≥0∞) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]; norm_num
  rwa [hrhs] at hlt

theorem honestBatchStmt32_mem_corrAgree_4x4_via_sound :
    honestBatchStmt32 ∈ params257Fold4x4.batchCorrAgreeLang 2 (3 / 4) := by
  refine friSmoothBatchIOP_sound_of_unique params257Fold4x4 2 (α := 3 / 4)
    (rate257_le_three_quarters params257Fold4x4 rfl (by decide))
    honestBatchStmt32 (honestCausalSmoothBatchProver params257Fold4x4 2 honestBatchStmt32) ?_
  rw [iopInteractiveGame_honestCausalSmoothBatchProver_true_eq_one params257Fold4x4 2
      honestBatchStmt32_completeRel_4x4,
    friSmoothBatchUniqueCommitError_257_eq_4x4, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr
    (by norm_num [params257Fold4x4, mkParams257Smooth])

theorem honestBatchStmt32_mem_corrAgree_8x2_via_sound :
    honestBatchStmt32 ∈ params257Fold8x2.batchCorrAgreeLang 2 (3 / 4) := by
  refine friSmoothBatchIOP_sound_of_unique params257Fold8x2 2 (α := 3 / 4)
    (rate257_le_three_quarters params257Fold8x2 rfl (by decide))
    honestBatchStmt32 (honestCausalSmoothBatchProver params257Fold8x2 2 honestBatchStmt32) ?_
  rw [iopInteractiveGame_honestCausalSmoothBatchProver_true_eq_one params257Fold8x2 2
      honestBatchStmt32_completeRel_8x2,
    friSmoothBatchUniqueCommitError_257_eq_8x2, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr
    (by norm_num [params257Fold8x2, mkParams257Smooth])

-- Batched smooth unique-decoding BCS ROM (`friSmoothBatchBCS_romSoundness_bound_of_unique`,
-- `_of_prover_verifier_of_unique`, `_corrAgree_romSoundness_bound_of_unique`).
theorem smooth257_4x4_batch_bcs_lt_three_quarters :
    bcsSoundnessGame (friSmoothBatchIOP params257Fold4x4 2) (encZMod (p := 257))
      (params257Fold4x4.batchProximityLang 2 7)
      (mkSmoothBatchCheater params257Fold4x4 badBatchStmt32) 32 true < 3 / 4 := by
  refine lt_of_le_of_lt
    (friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_unique params257Fold4x4 2 (e := 7)
      (by decide) (leftInverse_decZMod_encZMod 257) 32
      (isCostBounded_MT_mkSmoothBatchCheater params257Fold4x4 badBatchStmt32)
      (isCostBounded_FS_mkSmoothBatchCheater params257Fold4x4 badBatchStmt32)
      (mkSmoothBatchCheater_openings_le params257Fold4x4 badBatchStmt32)) ?_
  have hrbr_inner : friSmoothRBRError params257Fold4x4 7
      (2 ^ params257Fold4x4.d - 2 ^ (params257Fold4x4.d - params257Fold4x4.firstStepLog)) =
      (729 : ℝ≥0∞) / 4096 := friSmooth257_rbrError_eq params257Fold4x4 rfl rfl 24 (by decide)
  have hle_r0 : (2 ^ params257Fold4x4.d : ℝ≥0∞) / (Fintype.card (ZMod 257) : ℝ≥0∞) ≤
      (729 : ℝ≥0∞) / 4096 := by
    have hnn : (32 / 257 : ℝ≥0) ≤ 729 / 4096 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
    have hcard : (Fintype.card (ZMod 257) : ℝ≥0∞) = 257 := by simp only [ZMod.card, Nat.cast_ofNat]
    simpa only [params257Fold4x4, mkParams257Smooth, hcard, (by norm_num : (2 : ℝ≥0∞) ^ 5 = 32),
      ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (4096 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr hnn
  have hrbr : friSmoothBatchRBRError params257Fold4x4
      ((2 ^ params257Fold4x4.d : ℝ≥0∞) / (Fintype.card (ZMod 257) : ℝ≥0∞)) 7
      (2 ^ params257Fold4x4.d - 2 ^ (params257Fold4x4.d - params257Fold4x4.firstStepLog)) =
      (729 : ℝ≥0∞) / 4096 := by
    rw [friSmoothBatchRBRError, hrbr_inner, max_eq_right hle_r0]
  have hpq : params257Fold4x4.proofOracleQueries = 73 := by decide
  rw [hrbr, card_friBatchChal257_32 _ rfl rfl, hpq, show params257Fold4x4.m = 2 from rfl]
  have hnn : (4 * (729 / 4096 + 4 * (1 / 18226330449477632)) +
      73 * (235 * (1 / 4294967296)) : ℝ≥0) < 3 / 4 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_mul,
    ENNReal.coe_div (by norm_num : (4096 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (18226330449477632 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one, params257Fold4x4, mkParams257Smooth,
    (by norm_num : ((0 + (2 + 2) : ℕ) : ℝ≥0∞) = 4),
    (by norm_num : ((0 + 73 * (0 + 1) : ℕ) : ℝ≥0∞) = 73),
    (by norm_num : ((3 * (0 + 73 * (0 + 1)) + (2 + 2) * (0 + (2 + 2)) : ℕ) : ℝ≥0∞) = 235),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using ENNReal.coe_lt_coe.mpr hnn

end SmoothUnique257

/-! ### Suite 2: Goldilocks Beyond-Unique-Decoding Smooth Johnson & `η`-Gap
(`![2, 2]` & `![3, 1]`) -/

section SmoothJohnsonGoldilocks

/-- `8` is a primitive `64`-th (`2 ^ 6`-th) root of unity in `ZMod goldilocksP`
(`8 ^ 32 = 2 ^ 96 = (2 ^ 32 + 1) * (2 ^ 64 - 2 ^ 32 + 1) - 1 ≡ -1 (mod goldilocksP)`). -/
public theorem isPrimitiveRoot_eight_goldilocks :
    IsPrimitiveRoot (8 : ZMod goldilocksP) (2 ^ 6) := by
  have hneg : (8 : ZMod goldilocksP) ^ (2 ^ 5) = -1 := by
    have hp0 : ((2 ^ 64 - 2 ^ 32 + 1 : ℕ) : ZMod goldilocksP) = 0 := by
      change (goldilocksP : ZMod goldilocksP) = 0
      exact ZMod.natCast_self goldilocksP
    have hp : (2 : ZMod goldilocksP) ^ 64 - (2 : ZMod goldilocksP) ^ 32 + 1 = 0 := by
      have hcast : ((2 ^ 64 - 2 ^ 32 + 1 : ℕ) : ZMod goldilocksP) =
          (2 : ZMod goldilocksP) ^ 64 - (2 : ZMod goldilocksP) ^ 32 + 1 := by
        have hle : 2 ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.cast_add, Nat.cast_sub hle]
        push_cast
        rfl
      rwa [← hcast]
    have hadd : (8 : ZMod goldilocksP) ^ (2 ^ 5) + 1 = 0 := by
      calc (8 : ZMod goldilocksP) ^ (2 ^ 5) + 1
          = ((2 : ZMod goldilocksP) ^ 32 + 1) *
              ((2 : ZMod goldilocksP) ^ 64 - (2 : ZMod goldilocksP) ^ 32 + 1) := by ring
        _ = 0 := by rw [hp, mul_zero]
    exact eq_neg_of_add_eq_zero_left hadd
  exact isPrimitiveRoot_two_pow_of_neg_one (d := 6) (by norm_num) (by decide) hneg

/-- Shared builder for 2-round smooth FRI instances over `ZMod goldilocksP` on the `64`-point
coset `⟨8⟩` (`d = 6, m = 2, totalLog = 4, kFinal = 1, dim 0 = 16, ρ = 1 / 4, q = 5`). -/
public abbrev mkParamsGoldSmooth (stepLog : Fin 2 → ℕ) (hstepPos : ∀ i : Fin 2, 1 ≤ stepLog i)
    (htot : friCumLog stepLog 2 = 4) : FRISmoothParams (ZMod goldilocksP) where
  d := 6
  m := 2
  stepLog := stepLog
  kFinal := 1
  q := 5
  g := 1
  ω := 8
  hstepPos := hstepPos
  htotal := by omega
  hkPos := by omega
  hkLe := by rw [htot]; decide
  hg := one_ne_zero
  h2 := by decide
  hω := isPrimitiveRoot_eight_goldilocks

/-- Pure 4-to-1 Goldilocks smooth FRI parameters: `64 → 16 → 4`, `dim: 16 → 4 → 1`, `ρ = 1 / 4`,
`stepLog = ![2, 2]`, `q = 5`. -/
@[expose] public def paramsGold4x4 : FRISmoothParams (ZMod goldilocksP) :=
  mkParamsGoldSmooth ![2, 2] (fun i => by fin_cases i <;> decide) rfl

/-- Mixed 8-to-1 then 2-to-1 Goldilocks smooth FRI parameters: `64 → 8 → 4`, `dim: 16 → 2 → 1`,
`ρ = 1 / 4`, `stepLog = ![3, 1]`, `q = 5`. -/
@[expose] public def paramsGold8x2 : FRISmoothParams (ZMod goldilocksP) :=
  mkParamsGoldSmooth ![3, 1] (fun i => by fin_cases i <;> decide) rfl

-- Schedule, telescoping (`48 + 12 = 56 + 4 = 60`), and round-0 Johnson bound checks.
example :
    friSmoothJohnsonRoundBound paramsGold4x4 3 ⟨0, by decide⟩ =
      friSmoothJohnsonCommitBound paramsGold4x4 3 :=
  friSmoothJohnsonRoundBound_zero paramsGold4x4 3 (by decide)

example :
    friSmoothJohnsonRoundBound paramsGold8x2 3 ⟨0, by decide⟩ =
      friSmoothJohnsonCommitBound paramsGold8x2 3 :=
  friSmoothJohnsonRoundBound_zero paramsGold8x2 3 (by decide)

/-- Monomial word `X ^ 25` on the `64`-point Goldilocks coset: agrees with every degree-`< 16`
codeword on at most `25` points (Hamming distance `≥ 39 > 25`), strictly beyond unique decoding
(`2 * 25 + 16 = 66 > 64`). -/
@[expose] public def farWordGold : OracleTable 6 (ZMod goldilocksP) :=
  fun idx => (cosetEval (1 : ZMod goldilocksP) 8 6 0 idx) ^ 25

/-- Honest degree-`< 16` codeword `1 + X` on the `64`-point Goldilocks coset. -/
@[expose] public def honestWordGold : OracleTable 6 (ZMod goldilocksP) :=
  fun idx => 1 + cosetEval (1 : ZMod goldilocksP) 8 6 0 idx

/-- Honest batched statement `(honestWordGold, ![0, honestWordGold])` over `ZMod goldilocksP`. -/
@[expose] public def honestBatchStmtGold : FRIBatchStmt (ZMod goldilocksP) 6 2 where
  base := honestWordGold
  terms := ![0, honestWordGold]

/-- Far batched statement `(0, ![0, farWordGold])` over `ZMod goldilocksP` (`e = 25`, `α = 3 / 5`).
-/
@[expose] public def badBatchStmtGold : FRIBatchStmt (ZMod goldilocksP) 6 2 where
  base := 0
  terms := ![0, farWordGold]

private theorem honestWordGold_mem_initialCode_4x4 :
    honestWordGold ∈ paramsGold4x4.initialCode := by
  refine mem_reedSolomon.mpr ⟨C 1 + X, ?_, ?_⟩
  · have h0 : (C (1 : ZMod goldilocksP)).degree < (16 : WithBot ℕ) :=
      lt_of_le_of_lt degree_C_le (by decide)
    have h1 : (X : Polynomial (ZMod goldilocksP)).degree < (16 : WithBot ℕ) := by
      rw [degree_X]; decide
    exact lt_of_le_of_lt (degree_add_le _ _) (max_lt h0 h1)
  · ext idx
    simp only [honestWordGold, FRISmoothParams.eval, friCumLog_zero, paramsGold4x4, eval_add,
      eval_C, eval_X]

private theorem honestBatchStmtGold_rel_4x4 :
    paramsGold4x4.batchCompletenessRel 2 honestBatchStmtGold () := by
  refine ⟨honestWordGold_mem_initialCode_4x4, fun j => ?_⟩
  fin_cases j
  · exact paramsGold4x4.initialCode.zero_mem
  · exact honestWordGold_mem_initialCode_4x4

private theorem honestBatchStmtGold_rel_8x2 :
    paramsGold8x2.batchCompletenessRel 2 honestBatchStmtGold () :=
  honestBatchStmtGold_rel_4x4

private theorem card_agree_farWordGold_le_25 {c : OracleTable 6 (ZMod goldilocksP)}
    (hc : c ∈ paramsGold4x4.initialCode) {D' : Finset (Fin (2 ^ 6))}
    (hagree : ∀ s ∈ D', farWordGold s = c s) : D'.card ≤ 25 := by
  refine le_trans (Finset.card_le_card ?_)
    (card_agree_monomial_le_smooth paramsGold4x4 (deg := 25) (by decide) hc)
  intro s hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hagree s hs⟩

private theorem farWordGold_not_mem_4x4 : farWordGold ∉ paramsGold4x4.proximityLang 25 := by
  rintro ⟨c, hc, hd⟩
  let c' : OracleTable 6 (ZMod goldilocksP) := c
  have hS : (Finset.univ.filter fun s : Fin (2 ^ 6) => farWordGold s = c' s).card ≤ 25 :=
    card_agree_farWordGold_le_25 hc fun s hs => (Finset.mem_filter.mp hs).2
  have htot := card_filter_eq_add_hammingDist farWordGold c'
  rw [Fintype.card_fin] at htot
  have hd' : hammingDist farWordGold c' ≤ 25 := hd
  omega

private theorem farWordGold_not_mem_8x2 : farWordGold ∉ paramsGold8x2.proximityLang 25 :=
  farWordGold_not_mem_4x4

private theorem badBatchStmtGold_not_mem_4x4 :
    badBatchStmtGold ∉ paramsGold4x4.batchProximityLang 2 25 := by
  rintro ⟨D', hge, _, _, v, hv, hagree⟩
  have hle : D'.card ≤ 25 := card_agree_farWordGold_le_25 (hv 1) fun s hs => (hagree s hs).2 1
  have h64 : (2 : ℕ) ^ paramsGold4x4.d = 64 := rfl
  omega

private theorem badBatchStmtGold_not_mem_8x2 :
    badBatchStmtGold ∉ paramsGold8x2.batchProximityLang 2 25 :=
  badBatchStmtGold_not_mem_4x4

private theorem badBatchStmtGold_not_mem_corrAgree_4x4 :
    badBatchStmtGold ∉ paramsGold4x4.batchCorrAgreeLang 2 (3 / 5) := by
  rintro ⟨D', hdens, _, _, v, hv, hagree⟩
  have hleR : (D'.card : ℝ) ≤ 25 := by
    exact_mod_cast card_agree_farWordGold_le_25 (hv 1) fun s hs => (hagree s hs).2 1
  have hd : (2 ^ paramsGold4x4.d : ℝ) = 64 := by norm_num [paramsGold4x4]
  rw [hd] at hdens
  linarith

private theorem badBatchStmtGold_not_mem_corrAgree_8x2 :
    badBatchStmtGold ∉ paramsGold8x2.batchCorrAgreeLang 2 (3 / 5) :=
  badBatchStmtGold_not_mem_corrAgree_4x4

private theorem sqrt_rate_gold :
    Real.sqrt ((paramsGold4x4.dim 0 : ℝ) / (2 ^ paramsGold4x4.d : ℝ)) = 1 / 2 := by
  have h : (paramsGold4x4.dim 0 : ℝ) / (2 ^ paramsGold4x4.d : ℝ) = (1 / 2 : ℝ) ^ 2 := by
    rw [show paramsGold4x4.dim 0 = 16 by decide, show paramsGold4x4.d = 6 from rfl]
    norm_num
  rw [h, Real.sqrt_sq (by norm_num)]

private theorem he_johnson_gold :
    ((25 : ℕ) : ℝ) / (2 ^ paramsGold4x4.d : ℝ) ≤
      1 - Real.sqrt ((paramsGold4x4.dim 0 : ℝ) / (2 ^ paramsGold4x4.d : ℝ)) -
        Real.sqrt ((paramsGold4x4.dim 0 : ℝ) / (2 ^ paramsGold4x4.d : ℝ)) /
          (2 * ((3 : ℕ) : ℝ)) := by
  rw [sqrt_rate_gold]
  norm_num [paramsGold4x4, mkParamsGoldSmooth]

private theorem he_eta_gold :
    ((25 : ℕ) : ℝ) / (2 ^ paramsGold4x4.d : ℝ) ≤
      1 - Real.sqrt ((paramsGold4x4.dim 0 : ℝ) / (2 ^ paramsGold4x4.d : ℝ)) - (1 / 12 : ℝ) := by
  rw [sqrt_rate_gold]
  norm_num [paramsGold4x4, mkParamsGoldSmooth]

private theorem halpha_johnson_gold :
    Real.sqrt ((paramsGold4x4.dim 0 : ℝ) / (2 ^ paramsGold4x4.d : ℝ)) *
      (1 + 1 / (2 * ((3 : ℕ) : ℝ))) ≤ (3 / 5 : ℝ) := by
  rw [sqrt_rate_gold]
  norm_num

private theorem halpha_eta_gold :
    Real.sqrt ((paramsGold4x4.dim 0 : ℝ) / (2 ^ paramsGold4x4.d : ℝ)) + (1 / 12 : ℝ) ≤
      (3 / 5 : ℝ) := by
  rw [sqrt_rate_gold]
  norm_num

/-- **Prefix-dependent adaptive prover** over `ZMod goldilocksP` (`d = 6`, `q = 5`, `t = 2`). It is
deterministic (every conditional distribution is a point mass), and its next oracle depends on the
transcript length (`0` vs. `1`), the round-`0` batching challenge (`c₀.batchCoeffs 0 = 0` vs.
`≠ 0`), and the prior oracle (`π₀ 0 = 0` vs. `≠ 0`). -/
noncomputable def adaptiveSmoothBatchProverGold :
    InteractiveIOPProver 6 (ZMod goldilocksP) (FRIBatchChal (ZMod goldilocksP) 6 5 2)
  | [] => PMF.pure (fun _ => 0)
  | [(π₀, c₀)] =>
      if c₀.batchCoeffs 0 = 0 then
        if π₀ ⟨0, by omega⟩ = 0 then PMF.pure (fun _ => 1) else PMF.pure (fun _ => 2)
      else
        PMF.pure (fun _ => 3)
  | _ => PMF.pure (fun _ => 4)

-- Explicit non-degeneracy witnesses proving `adaptiveSmoothBatchProverGold` genuinely depends on
-- prefix length, prior verifier challenge, and prior prover oracle.
example :
    let cA : FRIBatchChal (ZMod goldilocksP) 6 5 2 := ⟨fun _ => 0, 0, fun _ => ⟨0, by omega⟩⟩
    let cB : FRIBatchChal (ZMod goldilocksP) 6 5 2 := ⟨fun _ => 1, 0, fun _ => ⟨0, by omega⟩⟩
    adaptiveSmoothBatchProverGold [] ≠ adaptiveSmoothBatchProverGold [(fun _ => 0, cA)] ∧
    adaptiveSmoothBatchProverGold [(fun _ => 0, cA)] ≠
      adaptiveSmoothBatchProverGold [(fun _ => 0, cB)] ∧
    adaptiveSmoothBatchProverGold [(fun _ => 0, cA)] ≠
      adaptiveSmoothBatchProverGold [(fun _ => 1, cA)] := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun p : PMF _ => p (fun _ => 0)) h
    simp only [adaptiveSmoothBatchProverGold, ↓reduceIte, PMF.pure_apply] at h0
    have hne : (fun _ : Fin 64 => (0 : ZMod goldilocksP)) ≠ (fun _ => 1) := by
      intro heq
      have := congrFun heq ⟨0, by omega⟩
      exact absurd this (by decide)
    simp [hne] at h0
  · intro h
    have h0 := congrArg (fun p : PMF _ => p (fun _ => 1)) h
    simp only [adaptiveSmoothBatchProverGold, ↓reduceIte, one_ne_zero, PMF.pure_apply] at h0
    have hne : (fun _ : Fin 64 => (1 : ZMod goldilocksP)) ≠ (fun _ => 3) := by
      intro heq
      have := congrFun heq ⟨0, by omega⟩
      exact absurd this (by decide)
    simp [hne] at h0
  · intro h
    have h0 := congrArg (fun p : PMF _ => p (fun _ => 1)) h
    simp only [adaptiveSmoothBatchProverGold, ↓reduceIte, one_ne_zero, PMF.pure_apply] at h0
    have hne : (fun _ : Fin 64 => (1 : ZMod goldilocksP)) ≠ (fun _ => 2) := by
      intro heq
      have := congrFun heq ⟨0, by omega⟩
      exact absurd this (by decide)
    simp [hne] at h0

-- --- Part 2A: Discrete Guruswami–Sudan bounds on Goldilocks (`![2, 2]` and `![3, 1]`) ---

/-- Discrete Sudan multiplicities (`m = 1`) for Goldilocks smooth folding rounds. -/
def mRoundGold : Fin 2 → ℕ := ![1, 1]
/-- Discrete Sudan weighted degrees for Goldilocks `![2, 2]` (`D = ![9, 2]`). -/
def dRoundGold4x4 : Fin 2 → ℕ := ![9, 2]
/-- Discrete Sudan weighted degrees for Goldilocks `![3, 1]` (`D = ![4, 2]`). -/
def dRoundGold8x2 : Fin 2 → ℕ := ![4, 2]

private theorem gold_r0_discrete_hinterp :
    2 ^ paramsGold4x4.d * (1 * (1 + 1) / 2) <
      #(Sudan.monomials (paramsGold4x4.dim 0 - 1) 38) := by decide

private theorem gold_r0_discrete_hbound :
    ProximityGap.johnsonCurveBound (2 ^ paramsGold4x4.d) 1
      (paramsGold4x4.dim 0 - 1) 38 1 (2 ^ paramsGold4x4.d) ≤ 623336 := by decide +kernel

private theorem gold_4x4_discrete_jcb_sum :
    (∑ i : Fin paramsGold4x4.m,
      ProximityGap.johnsonCurveBound (paramsGold4x4.domainSize (i.val + 1)) (mRoundGold i)
        (paramsGold4x4.dim (i.val + 1) - 1) (dRoundGold4x4 i)
        (paramsGold4x4.arity i - 1) (2 ^ paramsGold4x4.d)) = 512826 := by decide

private theorem gold_8x2_discrete_jcb_sum :
    (∑ i : Fin paramsGold8x2.m,
      ProximityGap.johnsonCurveBound (paramsGold8x2.domainSize (i.val + 1)) (mRoundGold i)
        (paramsGold8x2.dim (i.val + 1) - 1) (dRoundGold8x2 i)
        (paramsGold8x2.arity i - 1) (2 ^ paramsGold8x2.d)) = 555853 := by decide

-- Single-word discrete commit & interactive IOP on `![2, 2]` and `![3, 1]`.
theorem smoothGold_4x4_single_discrete
    (P : InteractiveIOPProver 6 (ZMod goldilocksP) (FRIChal (ZMod goldilocksP) 6 5)) :
    friSmoothCommitGame paramsGold4x4 38 farWordGold P true ≤
        (512826 : ℝ≥0∞) / (goldilocksP : ℝ≥0∞) ∧
    iopInteractiveGame (friSmoothIOP paramsGold4x4) farWordGold P true ≤
        (512826 : ℝ≥0∞) / (goldilocksP : ℝ≥0∞) + ((38 : ℝ≥0∞) / 64) ^ 5 := by
  have h1 := friSmoothCommitGame_le_of_johnson_discrete paramsGold4x4 (e := 25) (by decide)
    mRoundGold dRoundGold4x4 (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) farWordGold_not_mem_4x4 P
  have h2 := friSmoothIOP_interactiveGame_le_of_johnson_discrete paramsGold4x4 (e := 25) (by decide)
    mRoundGold dRoundGold4x4 (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) farWordGold_not_mem_4x4 P
  rw [gold_4x4_discrete_jcb_sum, ZMod.card,
    show 2 ^ paramsGold4x4.d - 25 - 1 = 38 from rfl] at h1 h2
  refine ⟨by simpa only [Nat.cast_ofNat] using h1, ?_⟩
  simpa only [paramsGold4x4, mkParamsGoldSmooth, Nat.cast_ofNat,
    (by norm_num : ((2 ^ 6 - 25 - 1 : ℕ) : ℝ≥0∞) = 38),
    (by norm_num : (2 : ℝ≥0∞) ^ 6 = 64)] using h2

theorem smoothGold_8x2_single_discrete
    (P : InteractiveIOPProver 6 (ZMod goldilocksP) (FRIChal (ZMod goldilocksP) 6 5)) :
    friSmoothCommitGame paramsGold8x2 38 farWordGold P true ≤
        (555853 : ℝ≥0∞) / (goldilocksP : ℝ≥0∞) ∧
    iopInteractiveGame (friSmoothIOP paramsGold8x2) farWordGold P true ≤
        (555853 : ℝ≥0∞) / (goldilocksP : ℝ≥0∞) + ((38 : ℝ≥0∞) / 64) ^ 5 := by
  have h1 := friSmoothCommitGame_le_of_johnson_discrete paramsGold8x2 (e := 25) (by decide)
    mRoundGold dRoundGold8x2 (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) farWordGold_not_mem_8x2 P
  have h2 := friSmoothIOP_interactiveGame_le_of_johnson_discrete paramsGold8x2 (e := 25) (by decide)
    mRoundGold dRoundGold8x2 (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) farWordGold_not_mem_8x2 P
  rw [gold_8x2_discrete_jcb_sum, ZMod.card,
    show 2 ^ paramsGold8x2.d - 25 - 1 = 38 from rfl] at h1 h2
  refine ⟨by simpa only [Nat.cast_ofNat] using h1, ?_⟩
  simpa only [paramsGold8x2, mkParamsGoldSmooth, Nat.cast_ofNat,
    (by norm_num : ((2 ^ 6 - 25 - 1 : ℕ) : ℝ≥0∞) = 38),
    (by norm_num : (2 : ℝ≥0∞) ^ 6 = 64)] using h2

-- Batched discrete commit, interactive IOP, and BCS ROM on `![2, 2]` and `![3, 1]` (exercising all
-- four discrete batched endpoints including `adaptiveSmoothBatchProverGold`).
theorem smoothGold_4x4_batch_discrete :
    friSmoothBatchCommitGame paramsGold4x4 2 38 badBatchStmtGold adaptiveSmoothBatchProverGold
        true ≤ (1136162 : ℝ≥0∞) / (goldilocksP : ℝ≥0∞) ∧
    iopInteractiveGame (friSmoothBatchIOP paramsGold4x4 2) badBatchStmtGold
        adaptiveSmoothBatchProverGold true ≤
      (1136162 : ℝ≥0∞) / (goldilocksP : ℝ≥0∞) + ((38 : ℝ≥0∞) / 64) ^ 5 := by
  have h1 := friSmoothBatchCommitGame_le_of_johnson_discrete paramsGold4x4 2 (e := 25) (m₀ := 1)
    (D₀ := 38) (B_batch := 623336) (by decide) (by decide) gold_r0_discrete_hinterp (by decide)
    gold_r0_discrete_hbound mRoundGold dRoundGold4x4 (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) badBatchStmtGold_not_mem_4x4 adaptiveSmoothBatchProverGold
  have h2 := friSmoothBatchIOP_interactiveGame_le_of_johnson_discrete paramsGold4x4 2 (e := 25)
    (m₀ := 1) (D₀ := 38) (B_batch := 623336) (by decide) (by decide) gold_r0_discrete_hinterp
    (by decide) gold_r0_discrete_hbound mRoundGold dRoundGold4x4
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    badBatchStmtGold_not_mem_4x4 adaptiveSmoothBatchProverGold
  rw [gold_4x4_discrete_jcb_sum, ZMod.card,
    show 2 ^ paramsGold4x4.d - 25 - 1 = 38 from rfl] at h1 h2
  refine ⟨by simpa only [(by norm_num : ((623336 + 512826 : ℕ) : ℝ≥0∞) = 1136162)] using h1, ?_⟩
  simpa only [paramsGold4x4, mkParamsGoldSmooth, Nat.cast_ofNat,
    (by norm_num : ((623336 + 512826 : ℕ) : ℝ≥0∞) = 1136162),
    (by norm_num : ((2 ^ 6 - 25 - 1 : ℕ) : ℝ≥0∞) = 38),
    (by norm_num : (2 : ℝ≥0∞) ^ 6 = 64)] using h2

example :
    bcsSoundnessGame (friSmoothBatchIOP paramsGold4x4 2) (encZMod (p := goldilocksP))
      (paramsGold4x4.batchProximityLang 2 25)
      (mkSmoothBatchCheater paramsGold4x4 badBatchStmtGold) 32 true ≤
      ((0 + (paramsGold4x4.m + 2) : ℕ) : ℝ≥0∞) *
          (friSmoothBatchRBRError paramsGold4x4 ((623336 : ℝ≥0∞) / (Fintype.card (ZMod goldilocksP)
              : ℝ≥0∞)) 25 503070 +
            ((0 + (paramsGold4x4.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal (ZMod goldilocksP) 6 5 2))) +
        (61 : ℝ≥0∞) *
          (((3 * 61 + (paramsGold4x4.m + 2) * (0 + (paramsGold4x4.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ 32)) :=
  friSmoothBatchBCS_romSoundness_bound_of_johnson_discrete paramsGold4x4 2 (e := 25) (m₀ := 1)
    (D₀ := 38) (B_batch := 623336) (B_commit := 503070) (by decide) (by decide) (by decide)
    gold_r0_discrete_hinterp (by decide) gold_r0_discrete_hbound mRoundGold dRoundGold4x4
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) (leftInverse_decZMod_encZMod goldilocksP) 32
    (isCostBounded_FS_mkSmoothBatchCheater paramsGold4x4 badBatchStmtGold)
    (isCostBounded_soundnessProg_mkSmoothBatchCheater paramsGold4x4 (encZMod (p := goldilocksP))
      (paramsGold4x4.batchProximityLang 2 25) badBatchStmtGold (by decide : _ ≤ 61))

example :
    bcsSoundnessGame (friSmoothBatchIOP paramsGold8x2 2) (encZMod (p := goldilocksP))
      (paramsGold8x2.batchProximityLang 2 25)
      (mkSmoothBatchCheater paramsGold8x2 badBatchStmtGold) 32 true ≤
      ((0 + (paramsGold8x2.m + 2) : ℕ) : ℝ≥0∞) *
          (friSmoothBatchRBRError paramsGold8x2 ((623336 : ℝ≥0∞) / (Fintype.card (ZMod goldilocksP)
              : ℝ≥0∞)) 25 553280 +
            ((0 + (paramsGold8x2.m + 2) : ℕ) : ℝ≥0∞) *
              ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal (ZMod goldilocksP) 6 5 2))) +
        ((0 + paramsGold8x2.proofOracleQueries * (0 + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (0 + paramsGold8x2.proofOracleQueries * (0 + 1)) +
              (paramsGold8x2.m + 2) * (0 + (paramsGold8x2.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ 32)) :=
  friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_discrete paramsGold8x2 2
    (e := 25) (m₀ := 1) (D₀ := 38) (B_batch := 623336) (B_commit := 553280) (by decide) (by decide)
    (by decide) gold_r0_discrete_hinterp (by decide) gold_r0_discrete_hbound mRoundGold
    dRoundGold8x2 (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide) (leftInverse_decZMod_encZMod goldilocksP) 32
    (isCostBounded_MT_mkSmoothBatchCheater paramsGold8x2 badBatchStmtGold)
    (isCostBounded_FS_mkSmoothBatchCheater paramsGold8x2 badBatchStmtGold)
    (mkSmoothBatchCheater_openings_le paramsGold8x2 badBatchStmtGold)

-- --- Part 2B: Closed-Form Johnson (`mJ = 3`) & `η`-Gap (`η = 1 / 12`) Single & Batched Bounds ---

private theorem friSmoothJohnsonCommitError_gold_lt_4x4 :
    friSmoothJohnsonCommitError paramsGold4x4 3 < (1 : ℝ) / 10000000 := by
  simp only [friSmoothJohnsonCommitError, paramsGold4x4, mkParamsGoldSmooth,
    FRISmoothParams.totalLog, FRISmoothParams.dim, FRISmoothParams.cumLog, ZMod.card]
  norm_num [friCumLog, goldilocksP]

private theorem friSmoothBatchJohnsonCommitError_gold_lt_4x4 :
    friSmoothBatchJohnsonCommitError paramsGold4x4 3 < (1 : ℝ) / 10000000 := by
  simp only [friSmoothBatchJohnsonCommitError, paramsGold4x4, mkParamsGoldSmooth,
    FRISmoothParams.totalLog, FRISmoothParams.dim, FRISmoothParams.cumLog, ZMod.card]
  norm_num [friCumLog, goldilocksP]

private theorem friSmoothBatchJohnsonEtaCommitError_gold_lt_4x4 :
    friSmoothBatchJohnsonEtaCommitError paramsGold4x4 (1 / 12) < (1 : ℝ) / 1000 := by
  simp only [friSmoothBatchJohnsonEtaCommitError, paramsGold4x4, mkParamsGoldSmooth,
    FRISmoothParams.totalLog, FRISmoothParams.dim, FRISmoothParams.cumLog, ZMod.card]
  norm_num [friCumLog, goldilocksP]

private theorem friSmoothBatchJohnsonCommitError_gold_lt_8x2 :
    friSmoothBatchJohnsonCommitError paramsGold8x2 3 < (1 : ℝ) / 10000000 :=
  friSmoothBatchJohnsonCommitError_gold_lt_4x4

private theorem friSmoothBatchJohnsonEtaCommitError_gold_lt_8x2 :
    friSmoothBatchJohnsonEtaCommitError paramsGold8x2 (1 / 12) < (1 : ℝ) / 1000 :=
  friSmoothBatchJohnsonEtaCommitError_gold_lt_4x4

-- Single-word closed-form Johnson commit game, interactive IOP (`< 1 / 10`), RBR, and BCS ROM on
-- `![2, 2]` and `![3, 1]`.
theorem smoothGold_4x4_single_johnson_lt_tenth
    (P : InteractiveIOPProver 6 (ZMod goldilocksP) (FRIChal (ZMod goldilocksP) 6 5)) :
    friSmoothCommitGame paramsGold4x4 38 farWordGold P true < 1 / 10000000 ∧
    iopInteractiveGame (friSmoothIOP paramsGold4x4) farWordGold P true < 1 / 10 := by
  have hcg := friSmoothCommitGame_le_of_johnson paramsGold4x4 (e := 25) (mJ := 3) (by decide)
    he_johnson_gold farWordGold_not_mem_4x4 P
  have hiop := friSmoothIOP_interactiveGame_le_of_johnson paramsGold4x4 (e := 25) (mJ := 3)
    (by decide) he_johnson_gold farWordGold_not_mem_4x4 P
  have hcg_lt : ENNReal.ofReal (friSmoothJohnsonCommitError paramsGold4x4 3) <
      (1 : ℝ≥0∞) / 10000000 := by
    have hlt := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
      friSmoothJohnsonCommitError_gold_lt_4x4
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10000000), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat] using hlt
  refine ⟨lt_of_le_of_lt hcg hcg_lt, lt_of_le_of_lt hiop ?_⟩
  have hsum : (1 : ℝ≥0∞) / 10000000 + ((38 : ℝ≥0∞) / 64) ^ 5 < 1 / 10 := by
    have hnn : (1 / 10000000 + (38 / 64) ^ 5 : ℝ≥0) < 1 / 10 := by
      rw [← NNReal.coe_lt_coe]; push_cast; norm_num
    simpa only [ENNReal.coe_add, ENNReal.coe_pow,
      ENNReal.coe_div (by norm_num : (10000000 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (10 : ℝ≥0) ≠ 0),
      ENNReal.coe_ofNat, ENNReal.coe_one] using ENNReal.coe_lt_coe.mpr hnn
  have hq_eq : (((2 ^ paramsGold4x4.d - 25 - 1 : ℕ) : ℝ≥0∞) /
      (2 ^ paramsGold4x4.d : ℝ≥0∞)) ^ paramsGold4x4.q = ((38 : ℝ≥0∞) / 64) ^ 5 := by
    simp only [paramsGold4x4, mkParamsGoldSmooth,
      (by norm_num : ((2 ^ 6 - 25 - 1 : ℕ) : ℝ≥0∞) = 38),
      (by norm_num : (2 : ℝ≥0∞) ^ 6 = 64)]
  rw [hq_eq]
  exact lt_of_le_of_lt (add_le_add hcg_lt.le le_rfl) hsum

-- Exercise `friSmoothIOP_rbrSound_of_johnson`, `weightedCurveGapBound_of_johnson_eta`,
-- `friSmoothBCS_romSoundness_bound_of_johnson`, and
-- `friSmoothBCS_romSoundness_bound_of_prover_verifier_of_johnson`.
example :
    IOPRoundByRoundSoundness (friSmoothIOP paramsGold8x2) (paramsGold8x2.proximityLang 25)
      (friSmoothDoomed paramsGold8x2 38) (friSmoothGoodStep paramsGold8x2 38) ∧
    ∀ stmt ∉ paramsGold8x2.proximityLang 25, ∀ pref π,
      friSmoothDoomed paramsGold8x2 38 stmt pref →
      (PMF.uniformOfFintype (FRIChal (ZMod goldilocksP) 6 5)).toOuterMeasure
        {c | ¬ friSmoothGoodStep paramsGold8x2 38 stmt pref π c} ≤
      friSmoothRBRError paramsGold8x2 25 (friSmoothJohnsonCommitBound paramsGold8x2 3) :=
  friSmoothIOP_rbrSound_of_johnson paramsGold8x2 (e := 25) (mJ := 3) (by decide) he_johnson_gold

example :
    WeightedCurveGapBound paramsGold4x4 38
      (friSmoothJohnsonEtaCommitBound paramsGold4x4 (1 / 12)) :=
  weightedCurveGapBound_of_johnson_eta paramsGold4x4 (e := 25) (by norm_num) he_eta_gold

example :
    WeightedCurveGapBound paramsGold8x2 38
      (friSmoothJohnsonEtaCommitBound paramsGold8x2 (1 / 12)) :=
  weightedCurveGapBound_of_johnson_eta paramsGold8x2 (e := 25) (by norm_num) he_eta_gold

private theorem gold_rbr_single_johnson_le (params : FRISmoothParams (ZMod goldilocksP))
    (hd : params.d = 6) (hq : params.q = 5) {B_c : ℕ}
    (hBc : (B_c : ℝ) / (goldilocksP : ℝ) ≤ (38 / 64 : ℝ) ^ 5) :
    friSmoothRBRError params 25 B_c ≤ ((38 : ℝ≥0∞) / 64) ^ 5 := by
  rw [friSmoothRBRError, hd, hq, ZMod.card]
  have h1 : ((B_c : ℕ) : ℝ≥0∞) / (goldilocksP : ℝ≥0∞) ≤ ((38 : ℝ≥0∞) / 64) ^ 5 := by
    have hnn : ((B_c : ℝ≥0) / (goldilocksP : ℝ≥0)) ≤ (38 / 64 : ℝ≥0) ^ 5 := by
      rw [← NNReal.coe_le_coe]; push_cast; exact hBc
    simpa only [ENNReal.coe_pow,
      ENNReal.coe_div (by norm_num [goldilocksP] : (goldilocksP : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0), ENNReal.coe_natCast, ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr hnn
  have hq : (((2 ^ 6 - 25 - 1 : ℕ) : ℝ≥0∞) / (2 ^ 6 : ℝ≥0∞)) ^ 5 = ((38 : ℝ≥0∞) / 64) ^ 5 := by
    norm_num
  rw [hq]
  exact max_le h1 le_rfl

private theorem card_friChalGold_ge (params : FRISmoothParams (ZMod goldilocksP))
    (hd : params.d = 6) (hq : params.q = 5) :
    ((1 : ℝ≥0∞) / Fintype.card (FRIChal (ZMod goldilocksP) params.d params.q)) ≤
      1 / 1000000000 := by
  have hle : (1000000000 : ℕ) ≤ Fintype.card (FRIChal (ZMod goldilocksP) params.d params.q) := by
    rw [card_friChal, ZMod.card, hd, hq]
    norm_num [goldilocksP]
  have hle' : (1000000000 : ℝ≥0∞) ≤
      (Fintype.card (FRIChal (ZMod goldilocksP) params.d params.q) : ℝ≥0∞) := by
    exact_mod_cast hle
  exact ENNReal.div_le_div_left hle' 1

private theorem card_friBatchChalGold_ge (params : FRISmoothParams (ZMod goldilocksP))
    (hd : params.d = 6) (hq : params.q = 5) :
    ((1 : ℝ≥0∞) / Fintype.card (FRIBatchChal (ZMod goldilocksP) params.d params.q 2)) ≤
      1 / 1000000000 := by
  have hle : (1000000000 : ℕ) ≤
      Fintype.card (FRIBatchChal (ZMod goldilocksP) params.d params.q 2) := by
    rw [card_friBatchChal, ZMod.card, hd, hq]
    norm_num [goldilocksP]
  have hle' : (1000000000 : ℝ≥0∞) ≤
      (Fintype.card (FRIBatchChal (ZMod goldilocksP) params.d params.q 2) : ℝ≥0∞) := by
    exact_mod_cast hle
  exact ENNReal.div_le_div_left hle' 1

theorem smoothGold_4x4_single_bcs_johnson_lt_quarter :
    bcsSoundnessGame (friSmoothIOP paramsGold4x4) (encZMod (p := goldilocksP))
      (paramsGold4x4.proximityLang 25) (mkSmoothCheater paramsGold4x4 farWordGold) 32 true <
      1 / 4 := by
  refine lt_of_le_of_lt
    (friSmoothBCS_romSoundness_bound_of_johnson paramsGold4x4 (e := 25) (mJ := 3) (by decide)
      he_johnson_gold (leftInverse_decZMod_encZMod goldilocksP) 32
      (isCostBounded_FS_mkSmoothCheater paramsGold4x4 farWordGold)
      (isCostBounded_soundnessProg_mkSmoothCheater paramsGold4x4 (encZMod (p := goldilocksP))
        (paramsGold4x4.proximityLang 25) farWordGold (by decide : _ ≤ 61))) ?_
  have hrbr : friSmoothRBRError paramsGold4x4 25 (friSmoothJohnsonCommitBound paramsGold4x4 3) ≤
      ((38 : ℝ≥0∞) / 64) ^ 5 :=
    gold_rbr_single_johnson_le paramsGold4x4 rfl rfl (by
      have hjb : friSmoothJohnsonCommitBound paramsGold4x4 3 = 90596966400 := by decide
      rw [hjb]; norm_num [goldilocksP])
  have hcard := card_friChalGold_ge paramsGold4x4 rfl rfl
  refine lt_of_le_of_lt (by gcongr; norm_num : _ ≤
      ((0 + (paramsGold4x4.m + 1) : ℕ) : ℝ≥0∞) *
          (((38 : ℝ≥0∞) / 64) ^ 5 +
            ((0 + (paramsGold4x4.m + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 1000000000)) +
        (61 : ℝ≥0∞) *
          (((3 * 61 + (paramsGold4x4.m + 1) * (0 + (paramsGold4x4.m + 1)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ 32))) ?_
  have hnn : (3 * ((38 / 64) ^ 5 + 3 * (1 / 1000000000)) +
      61 * (192 * (1 / 4294967296)) : ℝ≥0) < 1 / 4 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (1000000000 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one, paramsGold4x4, mkParamsGoldSmooth,
    (by norm_num : ((0 + (2 + 1) : ℕ) : ℝ≥0∞) = 3),
    (by norm_num : ((3 * 61 + (2 + 1) * (0 + (2 + 1)) : ℕ) : ℝ≥0∞) = 192),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using ENNReal.coe_lt_coe.mpr hnn

theorem smoothGold_8x2_single_bcs_pv_johnson_lt_quarter :
    bcsSoundnessGame (friSmoothIOP paramsGold8x2) (encZMod (p := goldilocksP))
      (paramsGold8x2.proximityLang 25) (mkSmoothCheater paramsGold8x2 farWordGold) 32 true <
      1 / 4 := by
  refine lt_of_le_of_lt
    (friSmoothBCS_romSoundness_bound_of_prover_verifier_of_johnson paramsGold8x2 (e := 25) (mJ := 3)
      (by decide) he_johnson_gold (leftInverse_decZMod_encZMod goldilocksP) 32
      (isCostBounded_MT_mkSmoothCheater paramsGold8x2 farWordGold)
      (isCostBounded_FS_mkSmoothCheater paramsGold8x2 farWordGold)
      (mkSmoothCheater_openings_le paramsGold8x2 farWordGold)) ?_
  have hrbr : friSmoothRBRError paramsGold8x2 25 (friSmoothJohnsonCommitBound paramsGold8x2 3) ≤
      ((38 : ℝ≥0∞) / 64) ^ 5 :=
    gold_rbr_single_johnson_le paramsGold8x2 rfl rfl (by
      have hjb : friSmoothJohnsonCommitBound paramsGold8x2 3 = 105696460800 := by decide
      rw [hjb]; norm_num [goldilocksP])
  have hcard := card_friChalGold_ge paramsGold8x2 rfl rfl
  have hpq : paramsGold8x2.proofOracleQueries = 71 := by decide
  rw [hpq]
  refine lt_of_le_of_lt (by gcongr : _ ≤
      ((0 + (paramsGold8x2.m + 1) : ℕ) : ℝ≥0∞) *
          (((38 : ℝ≥0∞) / 64) ^ 5 +
            ((0 + (paramsGold8x2.m + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 1000000000)) +
        ((0 + 71 * (0 + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (0 + 71 * (0 + 1)) + (paramsGold8x2.m + 1) * (0 + (paramsGold8x2.m + 1)) : ℕ) :
            ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ 32))) ?_
  have hnn : (3 * ((38 / 64) ^ 5 + 3 * (1 / 1000000000)) +
      71 * (222 * (1 / 4294967296)) : ℝ≥0) < 1 / 4 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (1000000000 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one, paramsGold8x2, mkParamsGoldSmooth,
    (by norm_num : ((0 + (2 + 1) : ℕ) : ℝ≥0∞) = 3),
    (by norm_num : ((0 + 71 * (0 + 1) : ℕ) : ℝ≥0∞) = 71),
    (by norm_num : ((3 * (0 + 71 * (0 + 1)) + (2 + 1) * (0 + (2 + 1)) : ℕ) : ℝ≥0∞) = 222),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using ENNReal.coe_lt_coe.mpr hnn

-- Batched smooth closed-form Johnson (`mJ = 3`) & `η`-gap (`η = 1 / 12`) commit game, interactive
-- IOP (`< 1 / 10`), and contrapositive `friSmoothBatchIOP_sound_of_johnson` / `_eta` on BOTH
-- `![2, 2]` and `![3, 1]` (instantiated on `adaptiveSmoothBatchProverGold` and honest causal
-- prover).
theorem smoothGold_4x4_batch_johnson_and_eta_lt_tenth :
    iopInteractiveGame (friSmoothBatchIOP paramsGold4x4 2) badBatchStmtGold
        adaptiveSmoothBatchProverGold true < 1 / 10 ∧
    friSmoothBatchCommitGame paramsGold4x4 2 38 badBatchStmtGold adaptiveSmoothBatchProverGold
        true < 1 / 1000 := by
  have hiop := friSmoothBatchIOP_interactiveGame_le_of_johnson_eta paramsGold4x4 2 (η := 1 / 12)
    (α := 3 / 5) (by norm_num) halpha_eta_gold badBatchStmtGold_not_mem_corrAgree_4x4
    adaptiveSmoothBatchProverGold
  have hcg := friSmoothBatchCommitGame_proximity_le_of_johnson_eta paramsGold4x4 2 (e := 25)
    (η := 1 / 12) (by norm_num) he_eta_gold badBatchStmtGold_not_mem_4x4
    adaptiveSmoothBatchProverGold
  have hlt1 : ENNReal.ofReal (friSmoothBatchJohnsonEtaCommitError paramsGold4x4 (1 / 12) +
      (3 / 5 : ℝ) ^ paramsGold4x4.q) < (1 : ℝ≥0∞) / 10 := by
    have hR : friSmoothBatchJohnsonEtaCommitError paramsGold4x4 (1 / 12) +
        (3 / 5 : ℝ) ^ paramsGold4x4.q < (1 : ℝ) / 10 := by
      have := friSmoothBatchJohnsonEtaCommitError_gold_lt_4x4
      have hpow : (3 / 5 : ℝ) ^ paramsGold4x4.q = 243 / 3125 := by
        norm_num [paramsGold4x4, mkParamsGoldSmooth]
      linarith
    have hof := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hR
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat] using hof
  have hlt2 : ENNReal.ofReal (friSmoothBatchJohnsonEtaCommitError paramsGold4x4 (1 / 12)) <
      (1 : ℝ≥0∞) / 1000 := by
    have hof := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
      friSmoothBatchJohnsonEtaCommitError_gold_lt_4x4
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1000), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat] using hof
  exact ⟨lt_of_le_of_lt hiop hlt1, lt_of_le_of_lt hcg hlt2⟩

theorem smoothGold_8x2_batch_johnson_lt_tenth :
    iopInteractiveGame (friSmoothBatchIOP paramsGold8x2 2) badBatchStmtGold
        adaptiveSmoothBatchProverGold true < 1 / 10 := by
  refine lt_of_le_of_lt
    (friSmoothBatchIOP_interactiveGame_le_of_johnson paramsGold8x2 2 (mJ := 3) (by decide)
      (α := 3 / 5) halpha_johnson_gold badBatchStmtGold_not_mem_corrAgree_8x2
      adaptiveSmoothBatchProverGold) ?_
  have hR : friSmoothBatchJohnsonCommitError paramsGold8x2 3 +
      (3 / 5 : ℝ) ^ paramsGold8x2.q < (1 : ℝ) / 10 := by
    have := friSmoothBatchJohnsonCommitError_gold_lt_8x2
    have hpow : (3 / 5 : ℝ) ^ paramsGold8x2.q = 243 / 3125 := by
      norm_num [paramsGold8x2, mkParamsGoldSmooth]
    linarith
  have hof := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hR
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10), ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat] using hof

-- Contrapositive `friSmoothBatchIOP_sound_of_johnson` and `friSmoothBatchIOP_sound_of_johnson_eta`
-- discharged on honest causal provers (`Pr = 1`) for both `![2, 2]` and `![3, 1]`.
theorem honestBatchStmtGold_mem_corrAgree_4x4_via_johnson :
    honestBatchStmtGold ∈ paramsGold4x4.batchCorrAgreeLang 2 (3 / 5) := by
  refine friSmoothBatchIOP_sound_of_johnson paramsGold4x4 2 (mJ := 3) (by decide) (α := 3 / 5)
    halpha_johnson_gold honestBatchStmtGold
    (honestCausalSmoothBatchProver paramsGold4x4 2 honestBatchStmtGold) ?_
  rw [iopInteractiveGame_honestCausalSmoothBatchProver_true_eq_one paramsGold4x4 2
      honestBatchStmtGold_rel_4x4, ← ENNReal.ofReal_one]
  refine (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr ?_
  have := friSmoothBatchJohnsonCommitError_gold_lt_4x4
  have hpow : (3 / 5 : ℝ) ^ paramsGold4x4.q = 243 / 3125 := by
    norm_num [paramsGold4x4, mkParamsGoldSmooth]
  linarith

theorem honestBatchStmtGold_mem_corrAgree_8x2_via_eta :
    honestBatchStmtGold ∈ paramsGold8x2.batchCorrAgreeLang 2 (3 / 5) := by
  refine friSmoothBatchIOP_sound_of_johnson_eta paramsGold8x2 2 (η := 1 / 12) (α := 3 / 5)
    (by norm_num) halpha_eta_gold honestBatchStmtGold
    (honestCausalSmoothBatchProver paramsGold8x2 2 honestBatchStmtGold) ?_
  rw [iopInteractiveGame_honestCausalSmoothBatchProver_true_eq_one paramsGold8x2 2
      honestBatchStmtGold_rel_8x2, ← ENNReal.ofReal_one]
  refine (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr ?_
  have := friSmoothBatchJohnsonEtaCommitError_gold_lt_8x2
  have hpow : (3 / 5 : ℝ) ^ paramsGold8x2.q = 243 / 3125 := by
    norm_num [paramsGold8x2, mkParamsGoldSmooth]
  linarith

-- Batched smooth `η`-gap BCS ROM soundness (`friSmoothBatchBCS_romSoundness_bound_of_johnson_eta`
-- and `friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_eta`, `< 1 / 3` at
-- `σ = 32` on both `![2, 2]` and `![3, 1]`).
private theorem gold_batch_rbr_eta_le (params : FRISmoothParams (ZMod goldilocksP))
    (hd : params.d = 6) (hq : params.q = 5) (hdim : params.dim 0 = 16)
    (hfst : 2 ^ params.d - 2 ^ (params.d - params.firstStepLog) ≤ 56) :
    friSmoothBatchRBRError params
      (ENNReal.ofReal
        (115200 * ((2 ^ params.d : ℝ) ^ 2) /
          (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * ((1 / 12 : ℝ) ^ 6) *
            (Fintype.card (ZMod goldilocksP) : ℝ))))
      25 (friSmoothJohnsonEtaCommitBound params (1 / 12)) ≤ ((38 : ℝ≥0∞) / 64) ^ 5 := by
  have hr0_le : ENNReal.ofReal
      (115200 * ((2 ^ params.d : ℝ) ^ 2) /
        (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * ((1 / 12 : ℝ) ^ 6) *
          (Fintype.card (ZMod goldilocksP) : ℝ))) ≤ ((38 : ℝ≥0∞) / 64) ^ 5 := by
    have hR : 115200 * ((2 ^ params.d : ℝ) ^ 2) /
        (((params.dim 0 : ℝ) / (2 ^ params.d : ℝ)) * ((1 / 12 : ℝ) ^ 6) *
          (Fintype.card (ZMod goldilocksP) : ℝ)) ≤ (38 / 64 : ℝ) ^ 5 := by
      rw [hd, hdim, ZMod.card]
      norm_num [goldilocksP]
    have hof := ENNReal.ofReal_le_ofReal hR
    simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 38 / 64),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 64), ENNReal.ofReal_ofNat] using hof
  have hBc_le : (friSmoothJohnsonEtaCommitBound params (1 / 12) : ℝ) / (goldilocksP : ℝ) ≤
      (38 / 64 : ℝ) ^ 5 := by
    have hfl : (friSmoothJohnsonEtaCommitBound params (1 / 12) : ℝ) ≤
        115200 * ((2 ^ params.d - 2 ^ (params.d - params.firstStepLog) : ℕ) : ℝ) *
          ((2 ^ params.d : ℝ) ^ 2) / ((params.dim 0 : ℝ) * ((1 / 12 : ℝ) ^ 6)) :=
      Nat.floor_le (by positivity)
    have hfstR : ((2 ^ 6 - 2 ^ (6 - params.firstStepLog) : ℕ) : ℝ) ≤ 56 := by
      rw [← hd]
      exact_mod_cast hfst
    have hnum : (friSmoothJohnsonEtaCommitBound params (1 / 12) : ℝ) ≤
        115200 * (56 : ℝ) * ((2 ^ 6 : ℝ) ^ 2) / ((16 : ℝ) * ((1 / 12 : ℝ) ^ 6)) := by
      refine hfl.trans ?_
      rw [hd, hdim]
      push_cast
      gcongr
      simpa using hfstR
    have hp_pos : (0 : ℝ) < (goldilocksP : ℝ) := by norm_num [goldilocksP]
    refine (div_le_div_of_nonneg_right hnum hp_pos.le).trans ?_
    norm_num [goldilocksP]
  rw [friSmoothBatchRBRError]
  exact max_le hr0_le (gold_rbr_single_johnson_le params hd hq hBc_le)

theorem smoothGold_4x4_batch_bcs_eta_lt_third :
    bcsSoundnessGame (friSmoothBatchIOP paramsGold4x4 2) (encZMod (p := goldilocksP))
      (paramsGold4x4.batchProximityLang 2 25)
      (mkSmoothBatchCheater paramsGold4x4 badBatchStmtGold) 32 true < 1 / 3 := by
  refine lt_of_le_of_lt
    (friSmoothBatchBCS_romSoundness_bound_of_johnson_eta paramsGold4x4 2 (e := 25) (η := 1 / 12)
      (by norm_num) he_eta_gold (leftInverse_decZMod_encZMod goldilocksP) 32
      (isCostBounded_FS_mkSmoothBatchCheater paramsGold4x4 badBatchStmtGold)
      (isCostBounded_soundnessProg_mkSmoothBatchCheater paramsGold4x4 (encZMod (p := goldilocksP))
        (paramsGold4x4.batchProximityLang 2 25) badBatchStmtGold (by decide : _ ≤ 61))) ?_
  have hrbr := gold_batch_rbr_eta_le paramsGold4x4 rfl rfl rfl (by decide)
  have hcard := card_friBatchChalGold_ge paramsGold4x4 rfl rfl
  refine lt_of_le_of_lt (by gcongr; norm_num : _ ≤
      ((0 + (paramsGold4x4.m + 2) : ℕ) : ℝ≥0∞) *
          (((38 : ℝ≥0∞) / 64) ^ 5 +
            ((0 + (paramsGold4x4.m + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 1000000000)) +
        (61 : ℝ≥0∞) *
          (((3 * 61 + (paramsGold4x4.m + 2) * (0 + (paramsGold4x4.m + 2)) : ℕ) : ℝ≥0∞) *
            ((1 : ℝ≥0∞) / 2 ^ 32))) ?_
  have hnn : (4 * ((38 / 64) ^ 5 + 4 * (1 / 1000000000)) +
      61 * (199 * (1 / 4294967296)) : ℝ≥0) < 1 / 3 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (1000000000 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one, paramsGold4x4, mkParamsGoldSmooth,
    (by norm_num : ((0 + (2 + 2) : ℕ) : ℝ≥0∞) = 4),
    (by norm_num : ((3 * 61 + (2 + 2) * (0 + (2 + 2)) : ℕ) : ℝ≥0∞) = 199),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using ENNReal.coe_lt_coe.mpr hnn

theorem smoothGold_8x2_batch_bcs_pv_eta_lt_third :
    bcsSoundnessGame (friSmoothBatchIOP paramsGold8x2 2) (encZMod (p := goldilocksP))
      (paramsGold8x2.batchProximityLang 2 25)
      (mkSmoothBatchCheater paramsGold8x2 badBatchStmtGold) 32 true < 1 / 3 := by
  refine lt_of_le_of_lt
    (friSmoothBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_eta paramsGold8x2 2
      (e := 25) (η := 1 / 12) (by norm_num) he_eta_gold
      (leftInverse_decZMod_encZMod goldilocksP) 32
      (isCostBounded_MT_mkSmoothBatchCheater paramsGold8x2 badBatchStmtGold)
      (isCostBounded_FS_mkSmoothBatchCheater paramsGold8x2 badBatchStmtGold)
      (mkSmoothBatchCheater_openings_le paramsGold8x2 badBatchStmtGold)) ?_
  have hrbr := gold_batch_rbr_eta_le paramsGold8x2 rfl rfl rfl (by decide)
  have hcard := card_friBatchChalGold_ge paramsGold8x2 rfl rfl
  have hpq : paramsGold8x2.proofOracleQueries = 71 := by decide
  rw [hpq]
  refine lt_of_le_of_lt (by gcongr : _ ≤
      ((0 + (paramsGold8x2.m + 2) : ℕ) : ℝ≥0∞) *
          (((38 : ℝ≥0∞) / 64) ^ 5 +
            ((0 + (paramsGold8x2.m + 2) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 1000000000)) +
        ((0 + 71 * (0 + 1) : ℕ) : ℝ≥0∞) *
          (((3 * (0 + 71 * (0 + 1)) + (paramsGold8x2.m + 2) * (0 + (paramsGold8x2.m + 2)) : ℕ) :
            ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ 32))) ?_
  have hnn : (4 * ((38 / 64) ^ 5 + 4 * (1 / 1000000000)) +
      71 * (229 * (1 / 4294967296)) : ℝ≥0) < 1 / 3 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (1000000000 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one, paramsGold8x2, mkParamsGoldSmooth,
    (by norm_num : ((0 + (2 + 2) : ℕ) : ℝ≥0∞) = 4),
    (by norm_num : ((0 + 71 * (0 + 1) : ℕ) : ℝ≥0∞) = 71),
    (by norm_num : ((3 * (0 + 71 * (0 + 1)) + (2 + 2) * (0 + (2 + 2)) : ℕ) : ℝ≥0∞) = 229),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using ENNReal.coe_lt_coe.mpr hnn

end SmoothJohnsonGoldilocks

/-! ### Suite 3: Binary-Specialization Soundness Equivalence Checks (`FRIParams.toSmooth`) -/

section BinarySoundnessBridges

example (B : ℕ) (stmt : OracleTable params257.d (ZMod 257))
    (pref : List (OracleTable params257.d (ZMod 257) ×
      FRIChal (ZMod 257) params257.d params257.q)) :
    friDoomed params257 B stmt pref ↔ friSmoothDoomed params257.toSmooth B stmt pref :=
  friDoomed_iff_friSmoothDoomed params257 B stmt pref

example (B : ℕ) (stmt : OracleTable params257.d (ZMod 257))
    (pref : List (OracleTable params257.d (ZMod 257) × FRIChal (ZMod 257) params257.d params257.q))
    (π : OracleTable params257.d (ZMod 257)) (c : FRIChal (ZMod 257) params257.d params257.q) :
    friGoodStep params257 B stmt pref π c ↔
      friSmoothGoodStep params257.toSmooth B stmt pref π c :=
  friGoodStep_iff_friSmoothGoodStep params257 B stmt pref π c

example (B : ℕ) (stmt : OracleTable params257.d (ZMod 257))
    (P : InteractiveIOPProver params257.d (ZMod 257) (FRIChal (ZMod 257) params257.d params257.q)) :
    friCommitGame params257 B stmt P = friSmoothCommitGame params257.toSmooth B stmt P :=
  friCommitGame_eq_friSmoothCommitGame params257 B stmt P

example (B : ℕ) (B_c : Fin params257.m → ℕ) :
    WeightedLineGapPerRound params257 B B_c ↔
      WeightedCurveGapPerRound params257.toSmooth B B_c :=
  weightedLineGapPerRound_iff_weightedCurveGapPerRound params257 B B_c

example (B : ℕ) (ε_c : Fin params257.m → ℝ≥0∞) :
    WeightedLineEscapePerRound params257 B ε_c ↔
      WeightedCurveEscapePerRound params257.toSmooth B ε_c :=
  weightedLineEscapePerRound_iff_weightedCurveEscapePerRound params257 B ε_c

example (B : ℕ) (stmt : FRIBatchStmt (ZMod 257) params257.d 2)
    (pref : List (OracleTable params257.d (ZMod 257) ×
      FRIBatchChal (ZMod 257) params257.d params257.q 2)) :
    friBatchDoomed params257 2 B stmt pref ↔
      friSmoothBatchDoomed params257.toSmooth 2 B stmt pref :=
  friBatchDoomed_iff_friSmoothBatchDoomed params257 2 B stmt pref

example (B : ℕ) (stmt : FRIBatchStmt (ZMod 257) params257.d 2)
    (pref : List (OracleTable params257.d (ZMod 257) ×
      FRIBatchChal (ZMod 257) params257.d params257.q 2))
    (π : OracleTable params257.d (ZMod 257))
    (c : FRIBatchChal (ZMod 257) params257.d params257.q 2) :
    friBatchGoodStep params257 2 B stmt pref π c ↔
      friSmoothBatchGoodStep params257.toSmooth 2 B stmt pref π c :=
  friBatchGoodStep_iff_friSmoothBatchGoodStep params257 2 B stmt pref π c

example (B : ℕ) (stmt : FRIBatchStmt (ZMod 257) params257.d 2)
    (P : InteractiveIOPProver params257.d (ZMod 257)
      (FRIBatchChal (ZMod 257) params257.d params257.q 2)) :
    friBatchCommitGame params257 2 B stmt P =
      friSmoothBatchCommitGame params257.toSmooth 2 B stmt P :=
  friBatchCommitGame_eq_friSmoothBatchCommitGame params257 2 B stmt P

end BinarySoundnessBridges

end CslibFrontierTests.Crypto.FRISmoothSoundness
