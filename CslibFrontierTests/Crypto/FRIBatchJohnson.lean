/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

import CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness
import CslibFrontierTests.Crypto.FRIBatchSoundness
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# Concrete Nonvacuous Tests for Summed & Closed-Form Batched FRI Soundness (`BatchJohnsonSoundness`)

Exercises every public definition and theorem of
`CslibFrontier.Crypto.Protocols.FRI.BatchJohnsonSoundness` from an ordinary `module` client (no
`import all`), reusing shared test fixtures from `CslibFrontierTests.Crypto.FRI`,
`CslibFrontierTests.Crypto.FRIJohnson`, and `CslibFrontierTests.Crypto.FRIBatchSoundness` with zero
duplicated root-of-unity, monomial far-word, or `mkBatchCheater` helpers:

1. **Suite 1 (`ZMod 257`, `d = 3, m = 2, kFinal = 1, q = 6, e = 2, α = 3 / 4`, `t = 2` & `t = 0`).**
   Exercises the conditional summed bridge
   (`friBatchCommitRound_escape_le_of_weightedLineEscapePerRound`, `friBatchRoundEscape`,
   `friBatchSumError`, `sum_friBatchRoundEscape_eq`, `friBatchFinalPasses`, `friBatchCommitGame`,
   `friBatchCommitGame_le_of_escape`, `friBatchIOP_interactiveGame_le_of_escape`),
   `batchFloorThreshold_bounds`, `friBatchUniqueCommitError` (`= 14 / 257`),
   `friBatchUniqueCommitError_ennreal_eq`, `friBatchCommitGame_proximity_le_of_unique` (at `t = 2`
   and `t = 0`), `friBatchIOP_interactiveGame_proximity_le_of_unique` (`< 1 / 8`), real-`α`
   `friBatchCommitGame_le_of_unique` & `friBatchIOP_interactiveGame_le_of_unique` (`< 1 / 4`),
   contrapositive `friBatchIOP_sound_of_unique` discharged on an honest causal prover (`Pr = 1`),
   and adaptive BCS-FRI ROM bounds (`friBatchBCS_romSoundness_bound_of_unique`,
   `friBatchBCS_romSoundness_bound_of_prover_verifier_of_unique`,
   `friBatchBCS_corrAgree_romSoundness_bound_of_unique` `< 1 / 3` on `mkBatchCheater`).
2. **Suite 2 (`ZMod 786433`, beyond unique decoding, `d = 4, m = 2, kFinal = 1, q = 8, e = 7,
   t = 2`).**
   Exercises `friBatchCommitGame_le_of_johnson_discrete` (`≤ 51137 / 786433 < 1 / 15`, strictly
   tighter than uniform `67960 / 786433`), `friBatchIOP_interactiveGame_le_of_johnson_discrete`
   (`< 1 / 14`), `friBatchBCS_romSoundness_bound_of_johnson_discrete` (`< 1 / 4`), and
   `friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_discrete` (`< 1 / 4`).
3. **Suite 3 (`ZMod 26214401`, beyond Sudan `m₀ = 2`, `d = 4, m = 2, kFinal = 1, q = 8, e = 8,
   t = 2`).**
   Exercises `friBatchCommitGame_le_of_johnson_discrete` (`≤ 1960365 / 26214401`) and
   `friBatchIOP_interactiveGame_le_of_johnson_discrete` (`< 2 / 25`).
4. **Suite 4 (`ZMod goldilocksP`, `p = 2 ^ 64 - 2 ^ 32 + 1`, `d = 6, m = 2, kFinal = 1, q = 6,
   mJ = 2, η = 1 / 16, α = 5 / 16, e = 44, t = 2`).**
   Rate `ρ = 1 / 16` (exact rational `√ρ = 1 / 4`), strictly beyond unique decoding (`2 * 44 + 4 >
   64`), exercising `friBatchJohnsonCommitError` (`< 1 / 10 ^ 8`), `friBatchJohnsonEtaCommitError`
   (`< 1 / 80`), `friJohnsonEtaCommitBound`, `weightedLineGapBound_of_johnson_eta`, integer-`e` and
   real-`α` commit-phase & Theorem 8.3 bounds across both `mJ = 2` (`< 1 / 1000`) and `η = 1 / 16`
   (`< 1 / 75`), a **genuinely prefix-dependent** randomized `adaptiveBatchProverGoldilocks` (with
   explicit conditional-`PMF` `≠` proofs across prefixes, challenges, and prior oracles), an
   **honest causal prover** (`Pr[accept] = 1`) discharging contrapositive
   `friBatchIOP_sound_of_johnson` and `friBatchIOP_sound_of_johnson_eta`, and all six adaptive
   BCS-FRI ROM corollaries (`< 1 / 10` on `mkBatchCheater` at `σ = 24`).
5. **Suite 5 (`ZMod 17`, `d = 4, n = 16, k = 4, α = 1 / 2`, paper `m = 3` vs. unique decoding).**
   Machine-checked regression test on `𝔽₁₇ˣ` certifying that when `(1 + ρ) / 2 > max(α, √ρ · (1 +
   1 / (2 * m)))` (`5 / 8 > 7 / 12`), a tuple satisfying the common-agreement premise (`≤ 4 ≤ 8`)
   can trigger the paper's `μ⁽⁰⁾`-weighted round-`0` event `E⁽⁰⁾` (`10 / 16 > 7 / 12` at batching
   scalar `0` with all weights `1`) while missing Lean's strict unique-decoding round-`0` cutoff
   (`friBatchGoodStep` holds at `⌊(5 / 8) * 16⌋₊ = 10`).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.FRIBatchJohnson

open scoped BigOperators NNReal ENNReal
open Finset Polynomial
open Cslib Cslib.Code Cslib.OracleComp Cslib.Probability
open Cslib.Crypto.Protocols.BCS Cslib.Crypto.Protocols.FRI
open CslibFrontierTests.Crypto.FRI
open CslibFrontierTests.Crypto.FRIJohnson
open CslibFrontierTests.Crypto.FRIBatchSoundness

/-! ### Reusable Honest Causal `InteractiveIOPProver` Helper -/

section HonestCausalHelper

/-- Lift the honest `friBatchIOP` round prover on `stmt` to an `InteractiveIOPProver`. -/
noncomputable def honestCausalBatchProver {F : Type} [Field F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) (stmt : FRIBatchStmt F params.d t) :
    InteractiveIOPProver params.d F (FRIBatchChal F params.d params.q t) :=
  InteractiveIOPProver.ofCausal fun j prev => (friBatchIOP params t).proveRound j stmt () prev

/-- On any statement satisfying `batchCompletenessRel`, `honestCausalBatchProver` makes
`iopInteractiveGame (friBatchIOP params t)` output `PMF.pure true` (hence `Pr[accept] = 1`). -/
theorem iopInteractiveGame_honestCausalBatchProver_eq_pure_true
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {stmt : FRIBatchStmt F params.d t}
    (hrel : params.batchCompletenessRel t stmt ()) :
    iopInteractiveGame (friBatchIOP params t) stmt (honestCausalBatchProver params t stmt) =
      PMF.pure true := by
  rw [honestCausalBatchProver, iopInteractiveGame_ofCausal_eq]
  have hacc :
      (fun chals : Fin (params.m + 2) → FRIBatchChal F params.d params.q t =>
        iopVerify (friBatchIOP params t) stmt chals
          (fun j => (friBatchIOP params t).proveRound j stmt ()
            fun i => chals ⟨i.val, lt_trans i.isLt j.isLt⟩)) =
      Function.const _ true := by
    funext chals
    exact friBatchIOP_complete params t stmt () hrel chals
  rw [hacc, PMF.map_const]

theorem iopInteractiveGame_honestCausalBatchProver_true_eq_one
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (params : FRIParams F) (t : ℕ) {stmt : FRIBatchStmt F params.d t}
    (hrel : params.batchCompletenessRel t stmt ()) :
    iopInteractiveGame (friBatchIOP params t) stmt (honestCausalBatchProver params t stmt) true =
      1 := by
  rw [iopInteractiveGame_honestCausalBatchProver_eq_pure_true params t hrel, PMF.pure_apply]
  simp only [↓reduceIte]

end HonestCausalHelper

/-! ### Suite 1: Conditional Summed Layer & Unique-Decoding Batched FRI (`ZMod 257`) -/

section Unique257

-- Floor-threshold bridge check via `batchFloorThreshold_bounds` (`⌊(3 / 4) * 8⌋₊ = 6`, `e₀ = 1`).
example :
    let e₀ := 2 ^ params257.d - 1 - ⌊(3 / 4 : ℝ) * (2 ^ params257.d : ℝ)⌋₊
    2 ^ params257.d - e₀ - 1 = ⌊(3 / 4 : ℝ) * (2 ^ params257.d : ℝ)⌋₊ ∧
      (e₀ : ℝ) / (2 ^ params257.d : ℝ) < 1 - (3 / 4 : ℝ) := by
  obtain ⟨_, _, hB, _, he_lt⟩ :=
    batchFloorThreshold_bounds params257 2 badStmt257 (α := 3 / 4) (by norm_num) (by norm_num)
  exact ⟨hB, he_lt⟩

-- Direct checks on `friBatchRoundEscape`, `friBatchSumError`, `sum_friBatchRoundEscape_eq`,
-- `friBatchFinalPasses`, and `friBatchCommitRound_escape_le_of_weightedLineEscapePerRound`.
example (ε_b : ℝ≥0∞) (ε_c : Fin params257.m → ℝ≥0∞) :
    (∑ j : Fin (params257.m + 2), friBatchRoundEscape params257 ε_b 2 ε_c j) =
      friBatchSumError params257 ε_b 2 ε_c :=
  sum_friBatchRoundEscape_eq params257 ε_b 2 ε_c

example (πFinal : OracleTable params257.d (ZMod 257)) (s : Fin (2 ^ params257.d)) :
    ¬ friBatchFinalPasses params257 2 badStmt257 [] πFinal s := by
  simp only [friBatchFinalPasses, not_false_eq_true]

example (π₀ π₁ : OracleTable params257.d (ZMod 257))
    (c₀ : FRIBatchChal (ZMod 257) params257.d params257.q 2)
    (hd : friBatchDoomed params257 2 5 badStmt257 [(π₀, c₀)]) :
    (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) params257.d params257.q 2)).toOuterMeasure
        {c | ¬ friBatchGoodStep params257 2 5 badStmt257 [(π₀, c₀)] π₁ c} ≤
      (4 : ℝ≥0∞) / 257 := by
  refine (friBatchCommitRound_escape_le_of_weightedLineEscapePerRound params257 2
    (weightedLineEscapePerRound_of_gapPerRound params257
      (weightedLineGapPerRound_of_unique params257 (e := 2) (by decide)))
    badStmt257 [(π₀, c₀)] (i := ⟨0, by decide⟩) rfl π₁ hd).trans_eq ?_
  simp only [params257, ZMod.card]
  norm_num

-- Direct conditional checks on `friBatchCommitGame_le_of_escape` and
-- `friBatchIOP_interactiveGame_le_of_escape`.
example (P : InteractiveIOPProver 3 (ZMod 257) (FRIBatchChal (ZMod 257) 3 6 2)) :
    friBatchCommitGame params257 2 5 badStmt257 P true ≤ (14 : ℝ≥0∞) / 257 ∧
    iopInteractiveGame (friBatchIOP params257 2) badStmt257 P true ≤
      (14 : ℝ≥0∞) / 257 + ((5 : ℝ≥0∞) / 8) ^ 6 := by
  have hb := batchRound0Escape_of_unique params257 2 (e := 2) (by decide)
  have hc := weightedLineEscapePerRound_of_gapPerRound params257
    (weightedLineGapPerRound_of_unique params257 (e := 2) (by decide))
  have hsum :
      (2 ^ params257.d : ℝ≥0∞) / (Fintype.card (ZMod 257) : ℝ≥0∞) +
          (∑ i : Fin params257.m,
            ((2 ^ (params257.d - (i.val + 1)) : ℕ) : ℝ≥0∞) /
              (Fintype.card (ZMod 257) : ℝ≥0∞)) =
        (14 : ℝ≥0∞) / 257 := by
    rw [sum_friUniqueRoundEscape_eq]
    simp only [params257, ZMod.card, friUniqueCommitError]
    have h1 : ENNReal.ofReal ((1 - (1 : ℝ) / (2 : ℝ) ^ 2) * ((2 ^ 3 : ℝ) / ((257 : ℕ) : ℝ))) =
        (6 : ℝ≥0∞) / 257 := by
      have hr : (1 - (1 : ℝ) / (2 : ℝ) ^ 2) * ((2 ^ 3 : ℝ) / ((257 : ℕ) : ℝ)) =
          (6 : ℝ) / 257 := by
        norm_num
      rw [hr, ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [h1]
    have hnn : (8 / 257 + 6 / 257 : ℝ≥0) = 14 / 257 := by
      rw [← NNReal.coe_inj]; push_cast; norm_num
    simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
      ENNReal.coe_ofNat, (by norm_num : (2 : ℝ≥0∞) ^ 3 = 8),
      (by norm_num : ((257 : ℕ) : ℝ≥0∞) = 257)] using
      congrArg ENNReal.ofNNReal hnn
  refine ⟨(friBatchCommitGame_le_of_escape params257 2 hb hc badStmt257_not_mem P).trans_eq hsum,
    (friBatchIOP_interactiveGame_le_of_escape params257 2 hb hc badStmt257_not_mem P).trans_eq ?_⟩
  rw [friBatchSumError, friSumError, ← add_assoc, hsum]
  simp only [params257]
  norm_num

-- Closed-form unique-decoding commit error (`= 14 / 257`) & `ℝ≥0∞` identity.
theorem friBatchUniqueCommitError_257_eq :
    friBatchUniqueCommitError params257 = (14 : ℝ) / 257 := by
  simp only [friBatchUniqueCommitError, params257, ZMod.card]
  norm_num

example :
    ((2 * 2 ^ params257.d - 2 ^ (params257.d - params257.m) : ℕ) : ℝ≥0∞) /
        (Fintype.card (ZMod 257) : ℝ≥0∞) =
      ENNReal.ofReal (friBatchUniqueCommitError params257) :=
  friBatchUniqueCommitError_ennreal_eq params257

-- Integer-`e` unique-decoding commit & interactive bounds (for both `t = 2` and `t = 0`).
theorem friBatch257_commitGame_le
    (P : InteractiveIOPProver 3 (ZMod 257) (FRIBatchChal (ZMod 257) 3 6 2)) :
    friBatchCommitGame params257 2 5 badStmt257 P true ≤ (14 : ℝ≥0∞) / 257 := by
  refine (friBatchCommitGame_proximity_le_of_unique params257 2 (e := 2) (by decide)
    badStmt257_not_mem P).trans_eq ?_
  simp only [params257, ZMod.card]
  norm_num

example (P : InteractiveIOPProver 3 (ZMod 257) (FRIBatchChal (ZMod 257) 3 6 0)) :
    friBatchCommitGame params257 0 5 badStmt257Zero P true ≤ (14 : ℝ≥0∞) / 257 := by
  refine (friBatchCommitGame_proximity_le_of_unique params257 0 (e := 2) (by decide)
    badStmt257Zero_not_mem P).trans_eq ?_
  simp only [params257, ZMod.card]
  norm_num

theorem friBatch257_interactiveGame_lt_eighth
    (P : InteractiveIOPProver 3 (ZMod 257) (FRIBatchChal (ZMod 257) 3 6 2)) :
    iopInteractiveGame (friBatchIOP params257 2) badStmt257 P true < 1 / 8 := by
  refine lt_of_le_of_lt
    (friBatchIOP_interactiveGame_proximity_le_of_unique params257 2 (e := 2) (by decide)
      badStmt257_not_mem P) ?_
  simp only [params257, ZMod.card]
  have hlt : (14 / 257 + (5 / 8) ^ 6 : ℝ≥0) < 1 / 8 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one,
    (by norm_num : ((257 : ℕ) : ℝ≥0∞) = 257),
    (by norm_num : ((2 * 2 ^ 3 - 2 ^ (3 - 2) : ℕ) : ℝ≥0∞) = 14),
    (by norm_num : ((2 ^ 3 - 2 - 1 : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : (2 : ℝ≥0∞) ^ 3 = 8)] using ENNReal.coe_lt_coe.mpr hlt

-- Real-`α` unique-decoding Lemma 8.2 (`α = 1 / 2`, `α₀ = max (1 / 2) (3 / 4) = 3 / 4`) and
-- Theorem 8.3 (`α = 3 / 4`, `< 1 / 4`).
theorem badStmt257_not_mem_corrAgree : badStmt257 ∉ params257.batchCorrAgreeLang 2 (3 / 4) := by
  rintro ⟨D', hdens, _, _, v, hv, hagree⟩
  have hle : D'.card ≤ 4 := card_agree_farWord_le_four (hv 1) fun s hs => (hagree s hs).2 1
  have hleR : (D'.card : ℝ) ≤ 4 := by exact_mod_cast hle
  have hd : (2 ^ params257.d : ℝ) = 8 := by norm_num [params257]
  rw [hd] at hdens
  linarith

theorem friBatch257_commitGame_real_le
    (P : InteractiveIOPProver 3 (ZMod 257) (FRIBatchChal (ZMod 257) 3 6 2)) :
    let α₀ := max (1 / 2 : ℝ) ((1 + (params257.dim 0 : ℝ) / (2 ^ params257.d : ℝ)) / 2)
    friBatchCommitGame params257 2 ⌊α₀ * (2 ^ params257.d : ℝ)⌋₊ badStmt257 P true ≤
      ENNReal.ofReal ((14 : ℝ) / 257) := by
  intro α₀
  rw [← friBatchUniqueCommitError_257_eq]
  refine friBatchCommitGame_le_of_unique params257 2 (α := 1 / 2) (stmt := badStmt257) ?_ P
  intro D' _ _ v hv hagree
  have hleR : (D'.card : ℝ) ≤ 4 := by
    exact_mod_cast card_agree_farWord_le_four (hv 1) fun s hs => (hagree s hs).2 1
  have hd : (2 ^ params257.d : ℝ) = 8 := by norm_num [params257]
  rw [hd]
  linarith

theorem friBatch257_interactiveGame_real_lt_quarter
    (P : InteractiveIOPProver 3 (ZMod 257) (FRIBatchChal (ZMod 257) 3 6 2)) :
    iopInteractiveGame (friBatchIOP params257 2) badStmt257 P true < 1 / 4 := by
  refine lt_of_le_of_lt
    (friBatchIOP_interactiveGame_le_of_unique params257 2 (α := 3 / 4)
      (by norm_num [params257, FRIParams.dim]) badStmt257_not_mem_corrAgree P) ?_
  rw [friBatchUniqueCommitError_257_eq]
  have hlt : ENNReal.ofReal ((14 : ℝ) / 257 + (3 / 4 : ℝ) ^ params257.q) <
      ENNReal.ofReal ((1 : ℝ) / 4) := by
    refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr ?_
    norm_num [params257]
  have hrhs : ENNReal.ofReal ((1 : ℝ) / 4) = (1 : ℝ≥0∞) / 4 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  rwa [hrhs] at hlt

-- Nonvacuous contrapositive `friBatchIOP_sound_of_unique` on an honest statement + causal prover.
def honestStmt257 : FRIBatchStmt (ZMod 257) params257.d 2 where
  base := honestWord
  terms := ![0, honestWord]

theorem honestStmt257_rel : params257.batchCompletenessRel 2 honestStmt257 () := by
  refine ⟨honestWord_mem_initialCode, fun j => ?_⟩
  fin_cases j
  · exact params257.initialCode.zero_mem
  · exact honestWord_mem_initialCode

theorem honestStmt257_mem_corrAgree_via_sound :
    honestStmt257 ∈ params257.batchCorrAgreeLang 2 (3 / 4) := by
  refine friBatchIOP_sound_of_unique params257 2 (α := 3 / 4)
    (by norm_num [params257, FRIParams.dim]) honestStmt257
    (honestCausalBatchProver params257 2 honestStmt257) ?_
  rw [iopInteractiveGame_honestCausalBatchProver_true_eq_one params257 2 honestStmt257_rel,
    friBatchUniqueCommitError_257_eq, ← ENNReal.ofReal_one]
  refine (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr ?_
  norm_num [params257]

-- Unconditional unique-decoding batched BCS-FRI ROM bounds (`batchProximityLang` &
-- `batchCorrAgreeLang`, `< 1 / 3` instantiated on `mkBatchCheater`).
private theorem card_friBatchChal257 :
    (Fintype.card (FRIBatchChal (ZMod 257) params257.d params257.q 2) : ℝ≥0∞) = 4449787707392 := by
  rw [card_friBatchChal, ZMod.card]
  norm_num [params257]

private theorem friBatch257_rbrError_eq :
    friBatchRBRError params257 ((2 ^ params257.d : ℝ≥0∞) / (Fintype.card (ZMod 257) : ℝ≥0∞))
      2 (2 ^ (params257.d - 1)) = (15625 : ℝ≥0∞) / 262144 := by
  have h1_nn : (4 / 257 : ℝ≥0) ≤ 15625 / 262144 := by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have h1 : (4 : ℝ≥0∞) / 257 ≤ 15625 / 262144 := by
    simpa only [ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (262144 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr h1_nn
  have h2_nn : (8 / 257 : ℝ≥0) ≤ 15625 / 262144 := by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have h2 : (8 : ℝ≥0∞) / 257 ≤ 15625 / 262144 := by
    simpa only [ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (262144 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr h2_nn
  have hpow : (((5 : ℝ≥0∞) / 8) ^ 6) = (15625 : ℝ≥0∞) / 262144 := by
    have hnn : ((5 / 8 : ℝ≥0) ^ 6) = 15625 / 262144 := by
      rw [← NNReal.coe_inj]; push_cast; norm_num
    simpa only [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (262144 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      congrArg ENNReal.ofNNReal hnn
  have hcard : (Fintype.card (ZMod 257) : ℝ≥0∞) = 257 := by simp only [ZMod.card, Nat.cast_ofNat]
  simp only [friBatchRBRError, friRBRError, params257, hcard,
    (by norm_num : ((2 ^ (3 - 1) : ℕ) : ℝ≥0∞) = 4),
    (by norm_num : ((2 ^ 3 - 2 - 1 : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : (2 : ℝ≥0∞) ^ 3 = 8), hpow, max_eq_right h1, max_eq_right h2]

example :
    bcsSoundnessGame (friBatchIOP params257 2) (encZMod (p := 257))
      (params257.batchProximityLang 2 2) (mkBatchCheater params257 badStmt257) 32 true < 1 / 3 := by
  refine lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_unique params257 2 (e := 2) (by decide)
      (leftInverse_decZMod_encZMod 257) 32
      (isCostBounded_FS_mkBatchCheater params257 badStmt257)
      (isCostBounded_soundnessProg_mkBatchCheater params257 (encZMod (p := 257)) 2 badStmt257
        (by decide : 1 + params257.proofOracleQueries * (params257.d + 1) ≤ 500))) ?_
  rw [friBatch257_rbrError_eq, card_friBatchChal257]
  have hnn :
      (5 * (15625 / 262144 + 5 * (1 / 4449787707392)) +
        500 * (1520 * (1 / 4294967296)) : ℝ≥0) < 1 / 3 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (262144 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4449787707392 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0)] at hcast
  simpa only [params257,
    (by norm_num : ((1 + (2 + 2) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((500 : ℕ) : ℝ≥0∞) = 500),
    (by norm_num : ((3 * 500 + (2 + 2) * (1 + (2 + 2)) : ℕ) : ℝ≥0∞) = 1520),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using hcast

example :
    bcsSoundnessGame (friBatchIOP params257 2) (encZMod (p := 257))
      (params257.batchProximityLang 2 2) (mkBatchCheater params257 badStmt257) 24 true < 1 / 3 := by
  refine lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_prover_verifier_of_unique params257 2 (e := 2) (by decide)
      (leftInverse_decZMod_encZMod 257) 24
      (isCostBounded_MT_mkBatchCheater params257 badStmt257)
      (isCostBounded_FS_mkBatchCheater params257 badStmt257)
      (mkBatchCheater_openings_le params257 badStmt257)) ?_
  rw [friBatch257_rbrError_eq, card_friBatchChal257]
  have hnn :
      (5 * (15625 / 262144 + 5 * (1 / 4449787707392)) +
        197 * (611 * (1 / 16777216)) : ℝ≥0) < 1 / 3 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (262144 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4449787707392 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (16777216 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0)] at hcast
  simpa only [params257, FRIParams.proofOracleQueries,
    (by norm_num : ((1 + (2 + 2) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((1 + (1 + 6 * (3 * 2 + 2)) * (3 + 1) : ℕ) : ℝ≥0∞) = 197),
    (by norm_num :
      ((3 * (1 + (1 + 6 * (3 * 2 + 2)) * (3 + 1)) + (2 + 2) * (1 + (2 + 2)) : ℕ) : ℝ≥0∞) = 611),
    (by norm_num : (2 : ℝ≥0∞) ^ 24 = 16777216)] using hcast

example :
    bcsSoundnessGame (friBatchIOP params257 2) (encZMod (p := 257))
      (params257.batchCorrAgreeLang 2 (3 / 4)) (mkBatchCheater params257 badStmt257) 32 true <
      9 / 10 := by
  refine lt_of_le_of_lt
    (friBatchBCS_corrAgree_romSoundness_bound_of_unique params257 2 (α := 3 / 4)
      (by norm_num [params257, FRIParams.dim]) (by norm_num)
      (leftInverse_decZMod_encZMod 257) 32
      (isCostBounded_FS_mkBatchCheater params257 badStmt257)
      (isCostBounded_soundnessProg_mkBatchCheater_lang params257 (encZMod (p := 257))
        (params257.batchCorrAgreeLang 2 (3 / 4)) badStmt257
        (by decide : 1 + params257.proofOracleQueries * (params257.d + 1) ≤ 500))) ?_
  rw [card_friBatchChal257]
  have hpow : ENNReal.ofReal ((3 / 4 : ℝ) ^ params257.q) = (729 : ℝ≥0∞) / 4096 := by
    have hr : ((3 / 4 : ℝ) ^ params257.q) = (729 : ℝ) / 4096 := by norm_num [params257]
    rw [hr, ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hpow]
  have hcard : (Fintype.card (ZMod 257) : ℝ≥0∞) = 257 := by simp only [ZMod.card, Nat.cast_ofNat]
  have h1_nn : (4 / 257 : ℝ≥0) ≤ 729 / 4096 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have h1 : (4 : ℝ≥0∞) / 257 ≤ 729 / 4096 := by
    simpa only [ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (4096 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr h1_nn
  have h2_nn : (8 / 257 : ℝ≥0) ≤ 729 / 4096 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have h2 : (8 : ℝ≥0∞) / 257 ≤ 729 / 4096 := by
    simpa only [ENNReal.coe_div (by norm_num : (257 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (4096 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr h2_nn
  simp only [hcard, params257,
    (by norm_num : (2 : ℝ≥0∞) ^ 3 = 8),
    (by norm_num : ((2 ^ (3 - 1) : ℕ) : ℝ≥0∞) = 4),
    max_eq_right h1, max_eq_right h2]
  have hnn :
      (5 * (729 / 4096 + 5 * (1 / 4449787707392)) +
        500 * (1520 * (1 / 4294967296)) : ℝ≥0) < 9 / 10 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (4096 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4449787707392 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (10 : ℝ≥0) ≠ 0)] at hcast
  simpa only [(by norm_num : ((1 + (2 + 2) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((500 : ℕ) : ℝ≥0∞) = 500),
    (by norm_num : ((3 * 500 + (2 + 2) * (1 + (2 + 2)) : ℕ) : ℝ≥0∞) = 1520),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using hcast

end Unique257

/-! ### Suite 2: Beyond-Unique Discrete Sudan (`ZMod 786433`, `e = 7 > e_uniq = 6`) -/

section DiscreteJohnson786433

private theorem sum_johnsonCurveBound_786 :
    (∑ i : Fin params786.m,
      ProximityGap.johnsonCurveBound (2 ^ (params786.d - (i.val + 1))) (mRound786 i)
        (params786.dim (i.val + 1) - 1) (DRound786 i) 1 (2 ^ params786.d)) = 18129 := by
  decide

/-- Summed beyond-unique discrete commit-phase bound (`≤ 51137 / 786433 < 1 / 15`, strictly tighter
than inflating folding round `1` to `17476`: `33008 + 18129 = 51137 < 67960`). -/
theorem friBatch786_commitGame_le
    (P : InteractiveIOPProver 4 (ZMod 786433) (FRIBatchChal (ZMod 786433) 4 8 2)) :
    friBatchCommitGame params786 2 8 badStmt786 P true ≤ (51137 : ℝ≥0∞) / 786433 := by
  refine (friBatchCommitGame_le_of_johnson_discrete params786 2 (e := 7) (m₀ := 1) (D₀ := 8)
    (B_batch := 33008) (by decide) (by decide) (by decide) (by decide) (by decide)
    mRound786 DRound786
    (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide)
    badStmt786_not_mem P).trans_eq ?_
  rw [sum_johnsonCurveBound_786]
  simp only [ZMod.card]
  norm_num

/-- Summed beyond-unique discrete interactive soundness (`< 1 / 14`) over `ZMod 786433`. -/
theorem friBatch786_interactiveGame_lt_one_14th
    (P : InteractiveIOPProver 4 (ZMod 786433) (FRIBatchChal (ZMod 786433) 4 8 2)) :
    iopInteractiveGame (friBatchIOP params786 2) badStmt786 P true < 1 / 14 := by
  refine lt_of_le_of_lt
    (friBatchIOP_interactiveGame_le_of_johnson_discrete params786 2 (e := 7) (m₀ := 1) (D₀ := 8)
      (B_batch := 33008) (by decide) (by decide) (by decide) (by decide) (by decide)
      mRound786 DRound786
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      badStmt786_not_mem P) ?_
  rw [sum_johnsonCurveBound_786]
  simp only [ZMod.card, params786]
  have hlt : ((33008 + 18129) / 786433 + (8 / 16) ^ 8 : ℝ≥0) < 1 / 14 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (786433 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (14 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one,
    (by norm_num : ((33008 + 18129 : ℕ) : ℝ≥0∞) = 33008 + 18129),
    (by norm_num : ((786433 : ℕ) : ℝ≥0∞) = 786433),
    (by norm_num : ((2 ^ 4 - 7 - 1 : ℕ) : ℝ≥0∞) = 8),
    (by norm_num : (2 : ℝ≥0∞) ^ 4 = 16)] using ENNReal.coe_lt_coe.mpr hlt

-- Direct checks on `friBatchBCS_romSoundness_bound_of_johnson_discrete` and
-- `friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_discrete` (`< 1 / 4`).
private theorem friBatch786_rbrError_eq :
    friBatchRBRError params786 ((33008 : ℝ≥0∞) / (Fintype.card (ZMod 786433) : ℝ≥0∞)) 7 17476 =
      (33008 : ℝ≥0∞) / 786433 := by
  have h1_nn : (1 / 256 : ℝ≥0) ≤ 17476 / 786433 := by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have h1 : (1 : ℝ≥0∞) / 256 ≤ 17476 / 786433 := by
    simpa only [ENNReal.coe_div (by norm_num : (256 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (786433 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one] using
      ENNReal.coe_le_coe.mpr h1_nn
  have h2_nn : (17476 / 786433 : ℝ≥0) ≤ 33008 / 786433 := by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have h2 : (17476 : ℝ≥0∞) / 786433 ≤ 33008 / 786433 := by
    simpa only [ENNReal.coe_div (by norm_num : (786433 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr h2_nn
  have hpow : (((8 : ℝ≥0∞) / 16) ^ 8) = (1 : ℝ≥0∞) / 256 := by
    have hnn : ((8 / 16 : ℝ≥0) ^ 8) = 1 / 256 := by
      rw [← NNReal.coe_inj]; push_cast; norm_num
    simpa only [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (16 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (256 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one] using
      congrArg ENNReal.ofNNReal hnn
  have hcard : (Fintype.card (ZMod 786433) : ℝ≥0∞) = 786433 := by
    simp only [ZMod.card, Nat.cast_ofNat]
  simp only [friBatchRBRError, friRBRError, params786, hcard,
    (by norm_num : ((17476 : ℕ) : ℝ≥0∞) = 17476),
    (by norm_num : ((2 ^ 4 - 7 - 1 : ℕ) : ℝ≥0∞) = 8),
    (by norm_num : (2 : ℝ≥0∞) ^ 4 = 16), hpow, max_eq_left h1, max_eq_left h2]

private theorem card_friBatchChal786 :
    (Fintype.card (FRIBatchChal (ZMod 786433) params786.d params786.q 2) : ℝ≥0∞) =
      2089031785297652159875121152 := by
  rw [card_friBatchChal, ZMod.card]
  norm_num [params786]

example :
    bcsSoundnessGame (friBatchIOP params786 2) (encZMod (p := 786433))
      (params786.batchProximityLang 2 7) (mkBatchCheater params786 badStmt786) 32 true < 1 / 4 := by
  refine lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_johnson_discrete params786 2 (e := 7) (m₀ := 1) (D₀ := 8)
      (B_batch := 33008) (B_commit := 17476) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) mRound786 DRound786
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (leftInverse_decZMod_encZMod 786433) 32
      (isCostBounded_FS_mkBatchCheater params786 badStmt786)
      (isCostBounded_soundnessProg_mkBatchCheater params786 (encZMod (p := 786433)) 7 badStmt786
        (by decide : 1 + params786.proofOracleQueries * (params786.d + 1) ≤ 500))) ?_
  rw [show ((33008 : ℕ) : ℝ≥0∞) = 33008 from rfl, friBatch786_rbrError_eq, card_friBatchChal786]
  have hnn :
      (5 * (33008 / 786433 + 5 * (1 / 2089031785297652159875121152)) +
        500 * (1520 * (1 / 4294967296)) : ℝ≥0) < 1 / 4 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (786433 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (2089031785297652159875121152 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0)] at hcast
  simpa only [params786,
    (by norm_num : ((1 + (2 + 2) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((500 : ℕ) : ℝ≥0∞) = 500),
    (by norm_num : ((3 * 500 + (2 + 2) * (1 + (2 + 2)) : ℕ) : ℝ≥0∞) = 1520),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using hcast

example :
    bcsSoundnessGame (friBatchIOP params786 2) (encZMod (p := 786433))
      (params786.batchProximityLang 2 7) (mkBatchCheater params786 badStmt786) 24 true < 1 / 4 := by
  refine lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_discrete params786 2 (e := 7)
      (m₀ := 1) (D₀ := 8) (B_batch := 33008) (B_commit := 17476)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      mRound786 DRound786
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (leftInverse_decZMod_encZMod 786433) 24
      (isCostBounded_MT_mkBatchCheater params786 badStmt786)
      (isCostBounded_FS_mkBatchCheater params786 badStmt786)
      (mkBatchCheater_openings_le params786 badStmt786)) ?_
  rw [show ((33008 : ℕ) : ℝ≥0∞) = 33008 from rfl, friBatch786_rbrError_eq, card_friBatchChal786]
  have hnn :
      (5 * (33008 / 786433 + 5 * (1 / 2089031785297652159875121152)) +
        326 * (998 * (1 / 16777216)) : ℝ≥0) < 1 / 4 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (786433 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (2089031785297652159875121152 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (16777216 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0)] at hcast
  simpa only [params786, FRIParams.proofOracleQueries,
    (by norm_num : ((1 + (2 + 2) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((1 + (1 + 8 * (3 * 2 + 2)) * (4 + 1) : ℕ) : ℝ≥0∞) = 326),
    (by norm_num :
      ((3 * (1 + (1 + 8 * (3 * 2 + 2)) * (4 + 1)) + (2 + 2) * (1 + (2 + 2)) : ℕ) : ℝ≥0∞) = 998),
    (by norm_num : (2 : ℝ≥0∞) ^ 24 = 16777216)] using hcast

end DiscreteJohnson786433

/-! ### Suite 3: Beyond-Sudan (`m₀ = 2` Required) at `δ = 1 - √ρ = 1 / 2` (`ZMod 26214401`) -/

section BeyondSudan26214401

private theorem sum_johnsonCurveBound_26M :
    (∑ i : Fin params26M.m,
      ProximityGap.johnsonCurveBound (2 ^ (params26M.d - (i.val + 1))) (mRound26M i)
        (params26M.dim (i.val + 1) - 1) (DRound26M i) 1 (2 ^ params26M.d)) = 37335 := by
  decide

theorem friBatch26M_commitGame_le
    (P : InteractiveIOPProver 4 (ZMod 26214401) (FRIBatchChal (ZMod 26214401) 4 8 2)) :
    friBatchCommitGame params26M 2 7 badStmt26M P true ≤ (1960365 : ℝ≥0∞) / 26214401 := by
  refine (friBatchCommitGame_le_of_johnson_discrete params26M 2 (e := 8) (m₀ := 2) (D₀ := 15)
    (B_batch := 1923030) (by decide) (by decide) (by decide) (by decide) (by decide)
    mRound26M DRound26M
    (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide)
    (fun i => by fin_cases i <;> decide)
    badStmt26M_not_mem P).trans_eq ?_
  rw [sum_johnsonCurveBound_26M]
  simp only [ZMod.card]
  norm_num

theorem friBatch26M_interactiveGame_lt_two_25ths
    (P : InteractiveIOPProver 4 (ZMod 26214401) (FRIBatchChal (ZMod 26214401) 4 8 2)) :
    iopInteractiveGame (friBatchIOP params26M 2) badStmt26M P true < 2 / 25 := by
  refine lt_of_le_of_lt
    (friBatchIOP_interactiveGame_le_of_johnson_discrete params26M 2 (e := 8) (m₀ := 2) (D₀ := 15)
      (B_batch := 1923030) (by decide) (by decide) (by decide) (by decide) (by decide)
      mRound26M DRound26M
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      (fun i => by fin_cases i <;> decide)
      badStmt26M_not_mem P) ?_
  rw [sum_johnsonCurveBound_26M]
  simp only [ZMod.card, params26M]
  have hlt : ((1923030 + 37335) / 26214401 + (7 / 16) ^ 8 : ℝ≥0) < 2 / 25 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (26214401 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (25 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat,
    (by norm_num : ((1923030 + 37335 : ℕ) : ℝ≥0∞) = 1923030 + 37335),
    (by norm_num : ((26214401 : ℕ) : ℝ≥0∞) = 26214401),
    (by norm_num : ((2 ^ 4 - 8 - 1 : ℕ) : ℝ≥0∞) = 7),
    (by norm_num : (2 : ℝ≥0∞) ^ 4 = 16)] using ENNReal.coe_lt_coe.mpr hlt

end BeyondSudan26214401

/-! ### Suite 4: Goldilocks (`2 ^ 64 - 2 ^ 32 + 1`) Closed-Form Johnson & `η`-Gap (`d = 6`) -/

section GoldilocksClosedForm

private theorem omegaBatchGoldilocks_pow_32 : (8 : ZMod goldilocksP) ^ (2 ^ 5) = -1 := by
  rw [show 2 ^ 5 = 32 by norm_num]
  apply eq_neg_of_add_eq_zero_left
  have hdvd : goldilocksP ∣ 8 ^ 32 + 1 := ⟨4294967297, by norm_num [goldilocksP]⟩
  have hcast : (((8 ^ 32 + 1 : ℕ) : ZMod goldilocksP)) = 0 :=
    (ZMod.natCast_eq_zero_iff (8 ^ 32 + 1) goldilocksP).mpr hdvd
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast

/-- Depth-`6` (`|L_0| = 64`), `2`-folding-round (`4` total batched rounds), rate-`1 / 16`
(`kFinal = 1, dim 0 = 4`, exact rational `√ρ = 1 / 4`), `q = 6` batched FRI parameters over the
64-bit Goldilocks prime field `ZMod (2 ^ 64 - 2 ^ 32 + 1)`. -/
def paramsBatchGoldilocks : FRIParams (ZMod goldilocksP) where
  d := 6
  m := 2
  kFinal := 1
  q := 6
  g := 1
  ω := 8
  hm := by omega
  hkPos := by omega
  hkLe := by omega
  hg := one_ne_zero
  h2 := by decide
  hω := isPrimitiveRoot_two_pow_of_neg_one (by omega) (by decide) omegaBatchGoldilocks_pow_32

-- Radius `e = 44` (`α = 5 / 16`) is strictly beyond unique decoding (`2 * 44 + 4 = 92 > 64`).
theorem paramsBatchGoldilocks_beyond_unique :
    ¬ (2 * 44 + paramsBatchGoldilocks.dim 0 ≤ 2 ^ paramsBatchGoldilocks.d) := by
  decide

/-- False `3`-word (`t = 2`) affine batch statement over Goldilocks (`terms 1 = X ^ 4` on `L_0`).
-/
def badStmtGoldilocks : FRIBatchStmt (ZMod goldilocksP) 6 2 where
  base := 0
  terms := ![0, fun idx => (paramsBatchGoldilocks.eval 0 idx) ^ 4]

theorem badStmtGoldilocks_not_mem_44 :
    badStmtGoldilocks ∉ paramsBatchGoldilocks.batchProximityLang 2 44 :=
  not_mem_batchProximityLang_of_monomial_term paramsBatchGoldilocks badStmtGoldilocks ⟨1, by omega⟩
    rfl (by decide)

theorem badStmtGoldilocks_agree_le_four :
    ∀ (D' : Finset (Fin (2 ^ paramsBatchGoldilocks.d)))
      (v₀ : OracleTable paramsBatchGoldilocks.d (ZMod goldilocksP)),
      v₀ ∈ paramsBatchGoldilocks.initialCode →
      ∀ v : Fin 2 → OracleTable paramsBatchGoldilocks.d (ZMod goldilocksP),
        (∀ j, v j ∈ paramsBatchGoldilocks.initialCode) →
        (∀ s ∈ D', badStmtGoldilocks.base s = v₀ s ∧ ∀ j, badStmtGoldilocks.terms j s = v j s) →
        D'.card ≤ 4 := by
  intro D' v₀ hv₀ v hv hagree
  by_contra hgt
  have h59 := not_mem_batchProximityLang_of_monomial_term paramsBatchGoldilocks badStmtGoldilocks
    ⟨1, by omega⟩ (e := 59) rfl (by decide)
  exact h59 ⟨D', by change 2 ^ 6 - 59 ≤ D'.card; omega, v₀, hv₀, v, hv, hagree⟩

theorem badStmtGoldilocks_not_mem_corrAgree :
    badStmtGoldilocks ∉ paramsBatchGoldilocks.batchCorrAgreeLang 2 (5 / 16) := by
  rintro ⟨D', hdens, v₀, hv₀, v, hv, hagree⟩
  have hle : (D'.card : ℝ) ≤ 4 := by
    exact_mod_cast badStmtGoldilocks_agree_le_four D' v₀ hv₀ v hv hagree
  have hd : (2 ^ paramsBatchGoldilocks.d : ℝ) = 64 := by norm_num [paramsBatchGoldilocks]
  rw [hd] at hdens
  linarith

private theorem batchGoldilocks_sqrt_rate :
    Real.sqrt ((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) = 1 / 4 := by
  have hrat :
      ((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) =
        (1 / 4 : ℝ) ^ 2 := by
    norm_num [paramsBatchGoldilocks, FRIParams.dim]
  rw [hrat, Real.sqrt_sq (by norm_num)]

theorem batchGoldilocks_johnson_slack :
    (44 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ) ≤
      1 - Real.sqrt ((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) -
        Real.sqrt ((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) /
          (2 * (2 : ℝ)) := by
  rw [batchGoldilocks_sqrt_rate]
  norm_num [paramsBatchGoldilocks]

theorem batchGoldilocks_eta_slack :
    (44 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ) ≤
      1 - Real.sqrt ((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) -
        (1 / 16 : ℝ) := by
  rw [batchGoldilocks_sqrt_rate]
  norm_num [paramsBatchGoldilocks]

theorem batchGoldilocks_alpha_johnson :
    Real.sqrt ((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) *
      (1 + 1 / (2 * (2 : ℝ))) ≤ (5 / 16 : ℝ) := by
  rw [batchGoldilocks_sqrt_rate]
  norm_num

theorem batchGoldilocks_alpha_eta :
    Real.sqrt ((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) +
      (1 / 16 : ℝ) ≤ (5 / 16 : ℝ) := by
  rw [batchGoldilocks_sqrt_rate]
  norm_num

-- Direct check of `weightedLineGapBound_of_johnson_eta` and `friJohnsonEtaCommitBound`.
theorem batchGoldilocks_etaCommitBound_eq :
    friJohnsonEtaCommitBound paramsBatchGoldilocks (1 / 16) = 63331869759897600 := by
  simp only [friJohnsonEtaCommitBound, paramsBatchGoldilocks, FRIParams.dim]
  exact (Nat.floor_eq_iff (by norm_num)).mpr ⟨by norm_num, by norm_num⟩

example :
    WeightedLineGapBound paramsBatchGoldilocks 19
      (friJohnsonEtaCommitBound paramsBatchGoldilocks (1 / 16)) :=
  weightedLineGapBound_of_johnson_eta paramsBatchGoldilocks (e := 44) (by norm_num)
    batchGoldilocks_eta_slack

private theorem batchGoldilocks_commitError_lt :
    friBatchJohnsonCommitError paramsBatchGoldilocks 2 < (1 : ℝ) / 100000000 := by
  simp only [friBatchJohnsonCommitError, ZMod.card, paramsBatchGoldilocks, FRIParams.dim,
    goldilocksP]
  norm_num

private theorem batchGoldilocks_etaCommitError_lt :
    friBatchJohnsonEtaCommitError paramsBatchGoldilocks (1 / 16) < (1 : ℝ) / 82 := by
  simp only [friBatchJohnsonEtaCommitError, ZMod.card, paramsBatchGoldilocks, FRIParams.dim,
    goldilocksP]
  norm_num

-- Integer-`e` & real-`α` Lemma 8.2 commit-phase bounds (`mJ = 2` `< 1 / 10 ^ 8`,
-- `η = 1 / 16` `< 1 / 80`).
theorem batchGoldilocks_commitGame_proximity_lt
    (P : InteractiveIOPProver 6 (ZMod goldilocksP) (FRIBatchChal (ZMod goldilocksP) 6 6 2)) :
    friBatchCommitGame paramsBatchGoldilocks 2 19 badStmtGoldilocks P true <
      1 / 100000000 := by
  refine lt_of_le_of_lt
    (friBatchCommitGame_proximity_le_of_johnson paramsBatchGoldilocks 2 (e := 44) (mJ := 2)
      (by omega) batchGoldilocks_johnson_slack badStmtGoldilocks_not_mem_44 P) ?_
  have hof := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr batchGoldilocks_commitError_lt
  have hrhs : ENNReal.ofReal ((1 : ℝ) / 100000000) = (1 : ℝ≥0∞) / 100000000 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  rwa [hrhs] at hof

theorem batchGoldilocks_commitGame_proximity_eta_lt
    (P : InteractiveIOPProver 6 (ZMod goldilocksP) (FRIBatchChal (ZMod goldilocksP) 6 6 2)) :
    friBatchCommitGame paramsBatchGoldilocks 2 19 badStmtGoldilocks P true < 1 / 80 := by
  refine lt_of_le_of_lt
    (friBatchCommitGame_proximity_le_of_johnson_eta paramsBatchGoldilocks 2 (e := 44)
      (η := 1 / 16) (by norm_num) batchGoldilocks_eta_slack badStmtGoldilocks_not_mem_44 P) ?_
  have hlt : friBatchJohnsonEtaCommitError paramsBatchGoldilocks (1 / 16) < (1 : ℝ) / 80 :=
    batchGoldilocks_etaCommitError_lt.trans (by norm_num)
  have hof := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hlt
  have hrhs : ENNReal.ofReal ((1 : ℝ) / 80) = (1 : ℝ≥0∞) / 80 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  rwa [hrhs] at hof

theorem batchGoldilocks_commitGame_real_lt
    (P : InteractiveIOPProver 6 (ZMod goldilocksP) (FRIBatchChal (ZMod goldilocksP) 6 6 2)) :
    let α₀ := max (1 / 16 : ℝ)
      (Real.sqrt ((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) *
        (1 + 1 / (2 * (2 : ℝ))))
    friBatchCommitGame paramsBatchGoldilocks 2 ⌊α₀ * (2 ^ paramsBatchGoldilocks.d : ℝ)⌋₊
      badStmtGoldilocks P true < 1 / 100000000 := by
  intro α₀
  refine lt_of_le_of_lt
    (friBatchCommitGame_le_of_johnson paramsBatchGoldilocks 2 (mJ := 2) (by omega)
      (α := 1 / 16) (stmt := badStmtGoldilocks)
      (fun D' v₀ hv₀ v hv hagree => by
        have hle : (D'.card : ℝ) ≤ 4 := by
          exact_mod_cast badStmtGoldilocks_agree_le_four D' v₀ hv₀ v hv hagree
        have hd : (2 ^ paramsBatchGoldilocks.d : ℝ) = 64 := by norm_num [paramsBatchGoldilocks]
        rw [hd]
        linarith) P) ?_
  have hof := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr batchGoldilocks_commitError_lt
  have hrhs : ENNReal.ofReal ((1 : ℝ) / 100000000) = (1 : ℝ≥0∞) / 100000000 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  rwa [hrhs] at hof

theorem batchGoldilocks_commitGame_real_eta_lt
    (P : InteractiveIOPProver 6 (ZMod goldilocksP) (FRIBatchChal (ZMod goldilocksP) 6 6 2)) :
    let α₀ := max (1 / 16 : ℝ)
      (Real.sqrt ((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) +
        (1 / 16 : ℝ))
    friBatchCommitGame paramsBatchGoldilocks 2 ⌊α₀ * (2 ^ paramsBatchGoldilocks.d : ℝ)⌋₊
      badStmtGoldilocks P true < 1 / 80 := by
  intro α₀
  refine lt_of_le_of_lt
    (friBatchCommitGame_le_of_johnson_eta paramsBatchGoldilocks 2 (η := 1 / 16) (α := 1 / 16)
      (by norm_num) (stmt := badStmtGoldilocks)
      (fun D' v₀ hv₀ v hv hagree => by
        have hle : (D'.card : ℝ) ≤ 4 := by
          exact_mod_cast badStmtGoldilocks_agree_le_four D' v₀ hv₀ v hv hagree
        have hd : (2 ^ paramsBatchGoldilocks.d : ℝ) = 64 := by norm_num [paramsBatchGoldilocks]
        rw [hd]
        linarith) P) ?_
  have hlt : friBatchJohnsonEtaCommitError paramsBatchGoldilocks (1 / 16) < (1 : ℝ) / 80 :=
    batchGoldilocks_etaCommitError_lt.trans (by norm_num)
  have hof := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hlt
  have hrhs : ENNReal.ofReal ((1 : ℝ) / 80) = (1 : ℝ≥0∞) / 80 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  rwa [hrhs] at hof

-- Integer-`e` & real-`α` Theorem 8.3 interactive batched FRI soundness (`< 1 / 1000` for `mJ = 2`,
-- `< 1 / 75` for `η = 1 / 16`).
theorem batchGoldilocks_interactiveGame_proximity_lt
    (P : InteractiveIOPProver 6 (ZMod goldilocksP) (FRIBatchChal (ZMod goldilocksP) 6 6 2)) :
    iopInteractiveGame (friBatchIOP paramsBatchGoldilocks 2) badStmtGoldilocks P true <
      1 / 1000 := by
  refine lt_of_le_of_lt
    (friBatchIOP_interactiveGame_proximity_le_of_johnson paramsBatchGoldilocks 2 (e := 44)
      (mJ := 2) (by omega) batchGoldilocks_johnson_slack badStmtGoldilocks_not_mem_44 P) ?_
  have hcommit :
      ENNReal.ofReal (friBatchJohnsonCommitError paramsBatchGoldilocks 2) ≤
        (1 : ℝ≥0∞) / 100000000 := by
    have hof := ENNReal.ofReal_le_ofReal batchGoldilocks_commitError_lt.le
    have hrhs : ENNReal.ofReal ((1 : ℝ) / 100000000) = (1 : ℝ≥0∞) / 100000000 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
      norm_num
    rwa [hrhs] at hof
  refine lt_of_le_of_lt (add_le_add hcommit le_rfl) ?_
  simp only [paramsBatchGoldilocks]
  have hlt : (1 / 100000000 + (19 / 64) ^ 6 : ℝ≥0) < 1 / 1000 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (100000000 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (1000 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one,
    (by norm_num : ((2 ^ 6 - 44 - 1 : ℕ) : ℝ≥0∞) = 19),
    (by norm_num : (2 : ℝ≥0∞) ^ 6 = 64)] using ENNReal.coe_lt_coe.mpr hlt

theorem batchGoldilocks_interactiveGame_proximity_eta_lt
    (P : InteractiveIOPProver 6 (ZMod goldilocksP) (FRIBatchChal (ZMod goldilocksP) 6 6 2)) :
    iopInteractiveGame (friBatchIOP paramsBatchGoldilocks 2) badStmtGoldilocks P true < 1 / 75 := by
  refine lt_of_le_of_lt
    (friBatchIOP_interactiveGame_proximity_le_of_johnson_eta paramsBatchGoldilocks 2 (e := 44)
      (η := 1 / 16) (by norm_num) batchGoldilocks_eta_slack badStmtGoldilocks_not_mem_44 P) ?_
  have hcommit :
      ENNReal.ofReal (friBatchJohnsonEtaCommitError paramsBatchGoldilocks (1 / 16)) ≤
        (1 : ℝ≥0∞) / 82 := by
    have hof := ENNReal.ofReal_le_ofReal batchGoldilocks_etaCommitError_lt.le
    have hrhs : ENNReal.ofReal ((1 : ℝ) / 82) = (1 : ℝ≥0∞) / 82 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
      norm_num
    rwa [hrhs] at hof
  refine lt_of_le_of_lt (add_le_add hcommit le_rfl) ?_
  simp only [paramsBatchGoldilocks]
  have hlt : (1 / 82 + (19 / 64) ^ 6 : ℝ≥0) < 1 / 75 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (82 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (75 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat, ENNReal.coe_one,
    (by norm_num : ((2 ^ 6 - 44 - 1 : ℕ) : ℝ≥0∞) = 19),
    (by norm_num : (2 : ℝ≥0∞) ^ 6 = 64)] using ENNReal.coe_lt_coe.mpr hlt

theorem batchGoldilocks_interactiveGame_real_lt_thousandth
    (P : InteractiveIOPProver 6 (ZMod goldilocksP) (FRIBatchChal (ZMod goldilocksP) 6 6 2)) :
    iopInteractiveGame (friBatchIOP paramsBatchGoldilocks 2) badStmtGoldilocks P true <
      1 / 1000 := by
  refine lt_of_le_of_lt
    (friBatchIOP_interactiveGame_le_of_johnson paramsBatchGoldilocks 2 (mJ := 2) (by omega)
      (α := 5 / 16) batchGoldilocks_alpha_johnson badStmtGoldilocks_not_mem_corrAgree P) ?_
  have hlt_real :
      friBatchJohnsonCommitError paramsBatchGoldilocks 2 + (5 / 16 : ℝ) ^ paramsBatchGoldilocks.q <
        (1 : ℝ) / 1000 := by
    have hc := batchGoldilocks_commitError_lt
    have hq : ((5 / 16 : ℝ) ^ paramsBatchGoldilocks.q) = 15625 / 16777216 := by
      norm_num [paramsBatchGoldilocks]
    linarith
  have hof := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hlt_real
  have hrhs : ENNReal.ofReal ((1 : ℝ) / 1000) = (1 : ℝ≥0∞) / 1000 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  rwa [hrhs] at hof

theorem batchGoldilocks_interactiveGame_real_eta_lt
    (P : InteractiveIOPProver 6 (ZMod goldilocksP) (FRIBatchChal (ZMod goldilocksP) 6 6 2)) :
    iopInteractiveGame (friBatchIOP paramsBatchGoldilocks 2) badStmtGoldilocks P true < 1 / 75 := by
  refine lt_of_le_of_lt
    (friBatchIOP_interactiveGame_le_of_johnson_eta paramsBatchGoldilocks 2 (η := 1 / 16)
      (α := 5 / 16) (by norm_num) batchGoldilocks_alpha_eta
      badStmtGoldilocks_not_mem_corrAgree P) ?_
  have hlt_real :
      friBatchJohnsonEtaCommitError paramsBatchGoldilocks (1 / 16) +
          (5 / 16 : ℝ) ^ paramsBatchGoldilocks.q <
        (1 : ℝ) / 75 := by
    have hc := batchGoldilocks_etaCommitError_lt
    have hq : ((5 / 16 : ℝ) ^ paramsBatchGoldilocks.q) = 15625 / 16777216 := by
      norm_num [paramsBatchGoldilocks]
    linarith
  have hof := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hlt_real
  have hrhs : ENNReal.ofReal ((1 : ℝ) / 75) = (1 : ℝ≥0∞) / 75 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  rwa [hrhs] at hof

/-- **Genuinely prefix-dependent adaptive randomized `InteractiveIOPProver` over Goldilocks**:
* On `[]` (round `0`), commits deterministically to the constant-`0` table (`PMF.pure`).
* On `(π₀, c₀) :: _`, adapts its output distribution to BOTH the observed batching scalar
  `c₀.batchCoeffs 0` and the realized round-`0` table `π₀`: outputs `PMF.pure (fun _ => 1)` when
  `c₀.batchCoeffs 0 = 0` and `π₀ 0 = 0`, and otherwise mixes
  `fun idx => π₀ idx + c₀.batchCoeffs 0 + 2` with `fun _ => c₀.batchCoeffs 0 + 3` uniformly. -/
noncomputable def adaptiveBatchProverGoldilocks :
    InteractiveIOPProver 6 (ZMod goldilocksP) (FRIBatchChal (ZMod goldilocksP) 6 6 2)
  | [] => PMF.pure (fun _ => 0)
  | (π₀, c₀) :: _ =>
    if c₀.batchCoeffs 0 = 0 ∧ π₀ ⟨0, by decide⟩ = 0 then
      PMF.pure (fun _ => 1)
    else
      (PMF.uniformOfFintype Bool).map fun b =>
        if b then fun idx => π₀ idx + c₀.batchCoeffs 0 + 2
        else fun _ => c₀.batchCoeffs 0 + 3

/-- Explicit witness that `adaptiveBatchProverGoldilocks` changes conditional `PMF`s across empty
vs. non-empty prefixes, across distinct round-`0` challenges `c₀.batchCoeffs`, AND across distinct
prior committed oracle tables `π₀`. -/
theorem adaptiveBatchProverGoldilocks_prefix_dependent :
    let cZero : FRIBatchChal (ZMod goldilocksP) 6 6 2 :=
      ⟨fun _ => 0, 0, fun _ => ⟨0, by decide⟩⟩
    let cOne : FRIBatchChal (ZMod goldilocksP) 6 6 2 :=
      ⟨fun _ => 1, 0, fun _ => ⟨0, by decide⟩⟩
    adaptiveBatchProverGoldilocks [] ≠
        adaptiveBatchProverGoldilocks [(fun _ => 0, cZero)] ∧
      adaptiveBatchProverGoldilocks [(fun _ => 0, cZero)] ≠
        adaptiveBatchProverGoldilocks [(fun _ => 0, cOne)] ∧
      adaptiveBatchProverGoldilocks [(fun _ => 0, cZero)] ≠
        adaptiveBatchProverGoldilocks [(fun _ => 1, cZero)] := by
  intro cZero cOne
  have hpure_zero :
      adaptiveBatchProverGoldilocks [(fun _ => 0, cZero)] = PMF.pure (fun _ => 1) := by
    simp only [adaptiveBatchProverGoldilocks, cZero, and_self, ↓reduceIte]
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hmem : (fun _ : Fin 64 => (0 : ZMod goldilocksP)) ∈
        (adaptiveBatchProverGoldilocks [(fun _ => 0, cZero)]).support := by
      rw [← heq, adaptiveBatchProverGoldilocks, PMF.support_pure, Set.mem_singleton_iff]; rfl
    rw [hpure_zero, PMF.support_pure, Set.mem_singleton_iff] at hmem
    exact absurd (congrFun hmem ⟨0, by decide⟩) (by decide)
  · intro heq
    have hmem : (fun _ : Fin 64 => (1 : ZMod goldilocksP)) ∈
        (adaptiveBatchProverGoldilocks [(fun _ => 0, cOne)]).support := by
      rw [← heq, hpure_zero, PMF.support_pure, Set.mem_singleton_iff]; rfl
    have hcond : ¬ (cOne.batchCoeffs 0 = 0 ∧ (0 : ZMod goldilocksP) = 0) := by
      simp only [cOne, one_ne_zero, false_and, not_false_eq_true]
    rw [adaptiveBatchProverGoldilocks, ite_eq_right hcond, PMF.mem_support_map_iff] at hmem
    obtain ⟨b, _, hb⟩ := hmem
    have h0 := congrFun hb ⟨0, by decide⟩
    cases b <;> exact absurd h0 (by decide)
  · intro heq
    have hmem : (fun _ : Fin 64 => (1 : ZMod goldilocksP)) ∈
        (adaptiveBatchProverGoldilocks [(fun _ => 1, cZero)]).support := by
      rw [← heq, hpure_zero, PMF.support_pure, Set.mem_singleton_iff]; rfl
    have hcond : ¬ (cZero.batchCoeffs 0 = 0 ∧ (1 : ZMod goldilocksP) = 0) := by
      simp only [cZero, one_ne_zero, and_false, not_false_eq_true]
    rw [adaptiveBatchProverGoldilocks, ite_eq_right hcond, PMF.mem_support_map_iff] at hmem
    obtain ⟨b, _, hb⟩ := hmem
    have h0 := congrFun hb ⟨0, by decide⟩
    cases b <;> exact absurd h0 (by decide)

example :
    friBatchCommitGame paramsBatchGoldilocks 2 19 badStmtGoldilocks
      adaptiveBatchProverGoldilocks true < 1 / 100000000 ∧
    iopInteractiveGame (friBatchIOP paramsBatchGoldilocks 2) badStmtGoldilocks
      adaptiveBatchProverGoldilocks true < 1 / 1000 :=
  ⟨batchGoldilocks_commitGame_proximity_lt adaptiveBatchProverGoldilocks,
    batchGoldilocks_interactiveGame_real_lt_thousandth adaptiveBatchProverGoldilocks⟩

-- Honest Goldilocks statement + causal prover certifying contrapositive `friBatchIOP_sound_of_*`.
def honestStmtGoldilocks : FRIBatchStmt (ZMod goldilocksP) 6 2 where
  base := fun _ => 1
  terms := ![0, fun _ => 1]

private theorem const_one_mem_initialCode_goldilocks :
    (fun _ : Fin 64 => (1 : ZMod goldilocksP)) ∈ paramsBatchGoldilocks.initialCode := by
  refine mem_reedSolomon.mpr ⟨1, ?_, by ext; simp⟩
  exact Polynomial.degree_one_le.trans_lt
    (WithBot.coe_lt_coe.mpr (by decide : 0 < paramsBatchGoldilocks.dim 0))

theorem honestStmtGoldilocks_rel :
    paramsBatchGoldilocks.batchCompletenessRel 2 honestStmtGoldilocks () := by
  refine ⟨const_one_mem_initialCode_goldilocks, fun j => ?_⟩
  fin_cases j
  · exact paramsBatchGoldilocks.initialCode.zero_mem
  · exact const_one_mem_initialCode_goldilocks

theorem honestStmtGoldilocks_mem_corrAgree_via_johnson :
    honestStmtGoldilocks ∈ paramsBatchGoldilocks.batchCorrAgreeLang 2 (5 / 16) := by
  refine friBatchIOP_sound_of_johnson paramsBatchGoldilocks 2 (mJ := 2) (by omega) (α := 5 / 16)
    batchGoldilocks_alpha_johnson honestStmtGoldilocks
    (honestCausalBatchProver paramsBatchGoldilocks 2 honestStmtGoldilocks) ?_
  rw [iopInteractiveGame_honestCausalBatchProver_true_eq_one paramsBatchGoldilocks 2
      honestStmtGoldilocks_rel, ← ENNReal.ofReal_one]
  refine (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr ?_
  have hc := batchGoldilocks_commitError_lt
  have hq : ((5 / 16 : ℝ) ^ paramsBatchGoldilocks.q) = 15625 / 16777216 := by
    norm_num [paramsBatchGoldilocks]
  linarith

theorem honestStmtGoldilocks_mem_corrAgree_via_eta :
    honestStmtGoldilocks ∈ paramsBatchGoldilocks.batchCorrAgreeLang 2 (5 / 16) := by
  refine friBatchIOP_sound_of_johnson_eta paramsBatchGoldilocks 2 (η := 1 / 16) (α := 5 / 16)
    (by norm_num) batchGoldilocks_alpha_eta honestStmtGoldilocks
    (honestCausalBatchProver paramsBatchGoldilocks 2 honestStmtGoldilocks) ?_
  rw [iopInteractiveGame_honestCausalBatchProver_true_eq_one paramsBatchGoldilocks 2
      honestStmtGoldilocks_rel, ← ENNReal.ofReal_one]
  refine (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr ?_
  have hc := batchGoldilocks_etaCommitError_lt
  have hq : ((5 / 16 : ℝ) ^ paramsBatchGoldilocks.q) = 15625 / 16777216 := by
    norm_num [paramsBatchGoldilocks]
  linarith

-- Adaptive two-channel batched BCS-FRI ROM bounds over Goldilocks (`< 1 / 10` at `σ = 24`,
-- exercising all 6 closed-form Johnson, `η`-gap, and `batchCorrAgreeLang` ROM corollaries).
private theorem card_friBatchChalGoldilocks_ge :
    (1000000000 : ℝ≥0∞) ≤
      Fintype.card
        (FRIBatchChal (ZMod goldilocksP) paramsBatchGoldilocks.d paramsBatchGoldilocks.q 2) := by
  rw [card_friBatchChal, ZMod.card]
  exact_mod_cast (by norm_num [paramsBatchGoldilocks, goldilocksP] :
    1000000000 ≤ goldilocksP ^ (2 + 1) * (2 ^ 6) ^ 6)

private theorem inv_card_friBatchChalGoldilocks_le :
    (1 : ℝ≥0∞) /
        Fintype.card
          (FRIBatchChal (ZMod goldilocksP) paramsBatchGoldilocks.d paramsBatchGoldilocks.q 2) ≤
      (1 : ℝ≥0∞) / 1000000000 :=
  ENNReal.div_le_div_left card_friBatchChalGoldilocks_ge 1

private theorem batchGoldilocks_rbr_johnson_le :
    friBatchRBRError paramsBatchGoldilocks
        (ENNReal.ofReal
          (1800 * (((2 : ℕ) + 1 : ℝ) ^ 6) * ((2 ^ paramsBatchGoldilocks.d : ℝ) ^ 2) /
            (((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) *
              (Fintype.card (ZMod goldilocksP) : ℝ))))
        44 (friJohnsonCommitBound paramsBatchGoldilocks 2) ≤
      (1 : ℝ≥0∞) / 1000 := by
  simp only [friBatchRBRError, friRBRError]
  refine max_le ?_ (max_le ?_ ?_)
  · have hlt :
        1800 * (((2 : ℕ) + 1 : ℝ) ^ 6) * ((2 ^ paramsBatchGoldilocks.d : ℝ) ^ 2) /
            (((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) *
              (Fintype.card (ZMod goldilocksP) : ℝ)) ≤
          (1 : ℝ) / 1000 := by
      simp only [ZMod.card, paramsBatchGoldilocks, FRIParams.dim, goldilocksP]
      norm_num
    refine (ENNReal.ofReal_le_ofReal hlt).trans_eq ?_
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  · rw [show friJohnsonCommitBound paramsBatchGoldilocks 2 = 42998169600 from rfl]
    have hcard : (Fintype.card (ZMod goldilocksP) : ℝ≥0∞) = 18446744069414584321 := by
      simp only [ZMod.card, goldilocksP, Nat.cast_ofNat]
    rw [hcard, show ((42998169600 : ℕ) : ℝ≥0∞) = 42998169600 from rfl]
    have hnn : (42998169600 / 18446744069414584321 : ℝ≥0) ≤ 1 / 1000 := by
      rw [← NNReal.coe_le_coe]; push_cast; norm_num
    simpa only [ENNReal.coe_div (by norm_num : (18446744069414584321 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (1000 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one] using
      ENNReal.coe_le_coe.mpr hnn
  · simp only [paramsBatchGoldilocks]
    have hnn : ((19 / 64 : ℝ≥0) ^ 6) ≤ 1 / 1000 := by
      rw [← NNReal.coe_le_coe]; push_cast; norm_num
    simpa only [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (1000 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one,
      (by norm_num : ((2 ^ 6 - 44 - 1 : ℕ) : ℝ≥0∞) = 19),
      (by norm_num : (2 : ℝ≥0∞) ^ 6 = 64)] using ENNReal.coe_le_coe.mpr hnn

private theorem batchGoldilocks_rbr_eta_le :
    friBatchRBRError paramsBatchGoldilocks
        (ENNReal.ofReal
          (115200 * ((2 ^ paramsBatchGoldilocks.d : ℝ) ^ 2) /
            (((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) *
              ((1 / 16 : ℝ) ^ 6) * (Fintype.card (ZMod goldilocksP) : ℝ))))
        44 (friJohnsonEtaCommitBound paramsBatchGoldilocks (1 / 16)) ≤
      (1 : ℝ≥0∞) / 100 := by
  simp only [friBatchRBRError, friRBRError]
  refine max_le ?_ (max_le ?_ ?_)
  · have hlt :
        115200 * ((2 ^ paramsBatchGoldilocks.d : ℝ) ^ 2) /
            (((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) *
              ((1 / 16 : ℝ) ^ 6) * (Fintype.card (ZMod goldilocksP) : ℝ)) ≤
          (1 : ℝ) / 100 := by
      simp only [ZMod.card, paramsBatchGoldilocks, FRIParams.dim, goldilocksP]
      norm_num
    refine (ENNReal.ofReal_le_ofReal hlt).trans_eq ?_
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  · rw [batchGoldilocks_etaCommitBound_eq]
    have hcard : (Fintype.card (ZMod goldilocksP) : ℝ≥0∞) = 18446744069414584321 := by
      simp only [ZMod.card, goldilocksP, Nat.cast_ofNat]
    rw [hcard, show ((63331869759897600 : ℕ) : ℝ≥0∞) = 63331869759897600 from rfl]
    have hnn : (63331869759897600 / 18446744069414584321 : ℝ≥0) ≤ 1 / 100 := by
      rw [← NNReal.coe_le_coe]; push_cast; norm_num
    simpa only [ENNReal.coe_div (by norm_num : (18446744069414584321 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (100 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one] using
      ENNReal.coe_le_coe.mpr hnn
  · simp only [paramsBatchGoldilocks]
    have hnn : ((19 / 64 : ℝ≥0) ^ 6) ≤ 1 / 100 := by
      rw [← NNReal.coe_le_coe]; push_cast; norm_num
    simpa only [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (100 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one,
      (by norm_num : ((2 ^ 6 - 44 - 1 : ℕ) : ℝ≥0∞) = 19),
      (by norm_num : (2 : ℝ≥0∞) ^ 6 = 64)] using ENNReal.coe_le_coe.mpr hnn

private theorem batchGoldilocks_rbr_corrAgree_le :
    max (ENNReal.ofReal
          (1800 * (((2 : ℕ) + 1 : ℝ) ^ 6) * ((2 ^ paramsBatchGoldilocks.d : ℝ) ^ 2) /
            (((paramsBatchGoldilocks.dim 0 : ℝ) / (2 ^ paramsBatchGoldilocks.d : ℝ)) *
              (Fintype.card (ZMod goldilocksP) : ℝ))))
        (max ((friJohnsonCommitBound paramsBatchGoldilocks 2 : ℝ≥0∞) /
            (Fintype.card (ZMod goldilocksP) : ℝ≥0∞))
          (ENNReal.ofReal ((5 / 16 : ℝ) ^ paramsBatchGoldilocks.q))) ≤
      (1 : ℝ≥0∞) / 1000 := by
  have hrbr := batchGoldilocks_rbr_johnson_le
  simp only [friBatchRBRError, friRBRError] at hrbr
  refine max_le ((le_max_left _ _).trans hrbr) (max_le ((le_max_left _ _).trans
    ((le_max_right _ _).trans hrbr)) ?_)
  have hle : ((5 / 16 : ℝ) ^ paramsBatchGoldilocks.q) ≤ (1 : ℝ) / 1000 := by
    norm_num [paramsBatchGoldilocks]
  refine (ENNReal.ofReal_le_ofReal hle).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
  norm_num

private theorem rom_rhs_500_lt_tenth {ε : ℝ≥0∞} (hε : ε ≤ (1 : ℝ≥0∞) / 100) :
    ((1 + (paramsBatchGoldilocks.m + 2) : ℕ) : ℝ≥0∞) *
        (ε + ((1 + (paramsBatchGoldilocks.m + 2) : ℕ) : ℝ≥0∞) *
          ((1 : ℝ≥0∞) /
            Fintype.card
              (FRIBatchChal (ZMod goldilocksP) paramsBatchGoldilocks.d
                paramsBatchGoldilocks.q 2))) +
      ((500 : ℕ) : ℝ≥0∞) *
        (((3 * 500 + (paramsBatchGoldilocks.m + 2) * (1 + (paramsBatchGoldilocks.m + 2)) : ℕ) :
          ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ 24)) <
      1 / 10 := by
  have hinv := inv_card_friBatchChalGoldilocks_le
  refine lt_of_le_of_lt
    (add_le_add (mul_le_mul_right (add_le_add hε (mul_le_mul_right hinv _)) _) le_rfl) ?_
  have hnn :
      (5 * (1 / 100 + 5 * (1 / 1000000000)) + 500 * (1520 * (1 / 16777216)) : ℝ≥0) < 1 / 10 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (100 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (1000000000 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (16777216 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (10 : ℝ≥0) ≠ 0)] at hcast
  simpa only [paramsBatchGoldilocks,
    (by norm_num : ((1 + (2 + 2) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((500 : ℕ) : ℝ≥0∞) = 500),
    (by norm_num : ((3 * 500 + (2 + 2) * (1 + (2 + 2)) : ℕ) : ℝ≥0∞) = 1520),
    (by norm_num : (2 : ℝ≥0∞) ^ 24 = 16777216)] using hcast

private theorem rom_rhs_pv_lt_tenth {ε : ℝ≥0∞} (hε : ε ≤ (1 : ℝ≥0∞) / 100) :
    ((1 + (paramsBatchGoldilocks.m + 2) : ℕ) : ℝ≥0∞) *
        (ε + ((1 + (paramsBatchGoldilocks.m + 2) : ℕ) : ℝ≥0∞) *
          ((1 : ℝ≥0∞) /
            Fintype.card
              (FRIBatchChal (ZMod goldilocksP) paramsBatchGoldilocks.d
                paramsBatchGoldilocks.q 2))) +
      ((1 + paramsBatchGoldilocks.proofOracleQueries * (6 + 1) : ℕ) : ℝ≥0∞) *
        (((3 * (1 + paramsBatchGoldilocks.proofOracleQueries * (6 + 1)) +
            (paramsBatchGoldilocks.m + 2) * (1 + (paramsBatchGoldilocks.m + 2)) : ℕ) : ℝ≥0∞) *
          ((1 : ℝ≥0∞) / 2 ^ 24)) <
      1 / 10 := by
  have hinv := inv_card_friBatchChalGoldilocks_le
  refine lt_of_le_of_lt
    (add_le_add (mul_le_mul_right (add_le_add hε (mul_le_mul_right hinv _)) _) le_rfl) ?_
  have hnn :
      (5 * (1 / 100 + 5 * (1 / 1000000000)) + 344 * (1052 * (1 / 16777216)) : ℝ≥0) < 1 / 10 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (100 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (1000000000 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (16777216 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (10 : ℝ≥0) ≠ 0)] at hcast
  simpa only [paramsBatchGoldilocks, FRIParams.proofOracleQueries,
    (by norm_num : ((1 + (2 + 2) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((1 + (1 + 6 * (3 * 2 + 2)) * (6 + 1) : ℕ) : ℝ≥0∞) = 344),
    (by norm_num :
      ((3 * (1 + (1 + 6 * (3 * 2 + 2)) * (6 + 1)) + (2 + 2) * (1 + (2 + 2)) : ℕ) : ℝ≥0∞) = 1052),
    (by norm_num : (2 : ℝ≥0∞) ^ 24 = 16777216)] using hcast

private theorem one_thousandth_le_one_hundredth : (1 : ℝ≥0∞) / 1000 ≤ (1 : ℝ≥0∞) / 100 :=
  ENNReal.div_le_div_left (by norm_num) 1

example :
    bcsSoundnessGame (friBatchIOP paramsBatchGoldilocks 2) (encZMod (p := goldilocksP))
      (paramsBatchGoldilocks.batchProximityLang 2 44)
      (mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks) 24 true < 1 / 10 :=
  lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_johnson paramsBatchGoldilocks 2 (e := 44) (mJ := 2)
      (by omega) batchGoldilocks_johnson_slack (leftInverse_decZMod_encZMod goldilocksP) 24
      (isCostBounded_FS_mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks)
      (isCostBounded_soundnessProg_mkBatchCheater paramsBatchGoldilocks
        (encZMod (p := goldilocksP)) 44 badStmtGoldilocks
        (by decide :
          1 + paramsBatchGoldilocks.proofOracleQueries * (paramsBatchGoldilocks.d + 1) ≤ 500)))
    (rom_rhs_500_lt_tenth (batchGoldilocks_rbr_johnson_le.trans one_thousandth_le_one_hundredth))

example :
    bcsSoundnessGame (friBatchIOP paramsBatchGoldilocks 2) (encZMod (p := goldilocksP))
      (paramsBatchGoldilocks.batchProximityLang 2 44)
      (mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks) 24 true < 1 / 10 :=
  lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson paramsBatchGoldilocks 2
      (e := 44) (mJ := 2) (by omega) batchGoldilocks_johnson_slack
      (leftInverse_decZMod_encZMod goldilocksP) 24
      (isCostBounded_MT_mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks)
      (isCostBounded_FS_mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks)
      (mkBatchCheater_openings_le paramsBatchGoldilocks badStmtGoldilocks))
    (rom_rhs_pv_lt_tenth (batchGoldilocks_rbr_johnson_le.trans one_thousandth_le_one_hundredth))

example :
    bcsSoundnessGame (friBatchIOP paramsBatchGoldilocks 2) (encZMod (p := goldilocksP))
      (paramsBatchGoldilocks.batchProximityLang 2 44)
      (mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks) 24 true < 1 / 10 :=
  lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_johnson_eta paramsBatchGoldilocks 2 (e := 44)
      (η := 1 / 16) (by norm_num) batchGoldilocks_eta_slack
      (leftInverse_decZMod_encZMod goldilocksP) 24
      (isCostBounded_FS_mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks)
      (isCostBounded_soundnessProg_mkBatchCheater paramsBatchGoldilocks
        (encZMod (p := goldilocksP)) 44 badStmtGoldilocks
        (by decide :
          1 + paramsBatchGoldilocks.proofOracleQueries * (paramsBatchGoldilocks.d + 1) ≤ 500)))
    (rom_rhs_500_lt_tenth batchGoldilocks_rbr_eta_le)

example :
    bcsSoundnessGame (friBatchIOP paramsBatchGoldilocks 2) (encZMod (p := goldilocksP))
      (paramsBatchGoldilocks.batchProximityLang 2 44)
      (mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks) 24 true < 1 / 10 :=
  lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_prover_verifier_of_johnson_eta paramsBatchGoldilocks 2
      (e := 44) (η := 1 / 16) (by norm_num) batchGoldilocks_eta_slack
      (leftInverse_decZMod_encZMod goldilocksP) 24
      (isCostBounded_MT_mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks)
      (isCostBounded_FS_mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks)
      (mkBatchCheater_openings_le paramsBatchGoldilocks badStmtGoldilocks))
    (rom_rhs_pv_lt_tenth batchGoldilocks_rbr_eta_le)

example :
    bcsSoundnessGame (friBatchIOP paramsBatchGoldilocks 2) (encZMod (p := goldilocksP))
      (paramsBatchGoldilocks.batchCorrAgreeLang 2 (5 / 16))
      (mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks) 24 true < 1 / 10 :=
  lt_of_le_of_lt
    (friBatchBCS_corrAgree_romSoundness_bound_of_johnson paramsBatchGoldilocks 2 (mJ := 2)
      (by omega) (α := 5 / 16) batchGoldilocks_alpha_johnson (by norm_num)
      (leftInverse_decZMod_encZMod goldilocksP) 24
      (isCostBounded_FS_mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks)
      (isCostBounded_soundnessProg_mkBatchCheater_lang paramsBatchGoldilocks
        (encZMod (p := goldilocksP)) (paramsBatchGoldilocks.batchCorrAgreeLang 2 (5 / 16))
        badStmtGoldilocks
        (by decide :
          1 + paramsBatchGoldilocks.proofOracleQueries * (paramsBatchGoldilocks.d + 1) ≤ 500)))
    (rom_rhs_500_lt_tenth
      (batchGoldilocks_rbr_corrAgree_le.trans one_thousandth_le_one_hundredth))

example :
    bcsSoundnessGame (friBatchIOP paramsBatchGoldilocks 2) (encZMod (p := goldilocksP))
      (paramsBatchGoldilocks.batchCorrAgreeLang 2 (5 / 16))
      (mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks) 24 true < 1 / 10 :=
  lt_of_le_of_lt
    (friBatchBCS_corrAgree_romSoundness_bound_of_prover_verifier_of_johnson paramsBatchGoldilocks 2
      (mJ := 2) (by omega) (α := 5 / 16) batchGoldilocks_alpha_johnson (by norm_num)
      (leftInverse_decZMod_encZMod goldilocksP) 24
      (isCostBounded_MT_mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks)
      (isCostBounded_FS_mkBatchCheater paramsBatchGoldilocks badStmtGoldilocks)
      (mkBatchCheater_openings_le paramsBatchGoldilocks badStmtGoldilocks))
    (rom_rhs_pv_lt_tenth
      (batchGoldilocks_rbr_corrAgree_le.trans one_thousandth_le_one_hundredth))

end GoldilocksClosedForm

/-! ### Suite 5: Round-`0` Cutoff Counterexample on `𝔽₁₇ˣ` (`ZMod 17`, `n = 16, k = 4, α = 1 / 2`)

Machine-checked realization of the `𝔽₁₇ˣ` counterexample separating JACM Section 8.2.1's `m = 3`
weighted round-`0` cutoff `max(1 / 2, √(1 / 4) * (1 + 1 / 6)) = 7 / 12` from the unique-decoding
cutoff `max(1 / 2, (1 + 1 / 4) / 2) = 5 / 8` when `(1 + ρ) / 2 > max(α, √ρ · (1 + 1 / (2 * m)))`:
`cutoffStmt17` has common agreement `≤ 4 ≤ 8` with `params17.initialCode`, yet at batching scalar
`0` (reporting `cutoffStmt17.base` so all `μ⁽⁰⁾` weights are `1`), codeword `0` achieves `10`
agreeing positions (`10 / 16 > 7 / 12`), while every codeword in `params17.initialCode` agrees with
`cutoffStmt17.eval 0` on at most `10 = ⌊(5 / 8) * 16⌋₊` positions (`friBatchGoodStep` holds). -/

section CutoffCounterexample17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def params17 : FRIParams (ZMod 17) where
  d := 4
  m := 2
  kFinal := 1
  q := 2
  g := 1
  ω := 3
  hm := by omega
  hkPos := by omega
  hkLe := by omega
  hg := one_ne_zero
  h2 := by decide
  hω := isPrimitiveRoot_two_pow_of_neg_one (by omega) (by decide) (by decide)

def cutoffStmt17 : FRIBatchStmt (ZMod 17) params17.d 1 where
  base := fun idx => if idx.val < 10 then 0 else (params17.eval 0 idx) ^ params17.dim 0
  terms := ![fun idx => (params17.eval 0 idx) ^ params17.dim 0]

def cZero17 : FRIBatchChal (ZMod 17) params17.d params17.q 1 :=
  ⟨fun _ => 0, 0, fun _ => ⟨0, by decide⟩⟩

theorem cutoffStmt17_agree_le_four (D' : Finset (Fin (2 ^ params17.d)))
    (v₀ : OracleTable params17.d (ZMod 17)) (hv₀ : v₀ ∈ params17.initialCode)
    (v : Fin 1 → OracleTable params17.d (ZMod 17))
    (hv : ∀ j, v j ∈ params17.initialCode)
    (hagree : ∀ s ∈ D', cutoffStmt17.base s = v₀ s ∧ ∀ j, cutoffStmt17.terms j s = v j s) :
    D'.card ≤ 4 := by
  by_contra hgt
  have h11 := not_mem_batchProximityLang_of_monomial_term params17 cutoffStmt17 ⟨0, by decide⟩
    (e := 11) rfl (by decide)
  exact h11 ⟨D', by change 2 ^ 4 - 11 ≤ D'.card; omega, v₀, hv₀, v, hv, hagree⟩

theorem cutoffStmt17_eval_cZero17 : cutoffStmt17.eval cZero17.batchCoeffs = cutoffStmt17.base := by
  ext s
  simp only [FRIBatchStmt.eval, cZero17, Fin.sum_univ_one, zero_smul, add_zero]

private theorem cutoffStmt17_card_zero_eq_ten :
    (Finset.univ.filter fun s : Fin (2 ^ params17.d) => cutoffStmt17.base s = 0).card = 10 := by
  decide

theorem cutoffStmt17_clears_paper_m3_cutoff_and_misses_unique_cutoff
    (π : OracleTable params17.d (ZMod 17)) :
    let αPaper := max (1 / 2 : ℝ)
      (Real.sqrt ((params17.dim 0 : ℝ) / (2 ^ params17.d : ℝ)) * (1 + 1 / (2 * (3 : ℝ))))
    let αUniq := max (1 / 2 : ℝ) ((1 + (params17.dim 0 : ℝ) / (2 ^ params17.d : ℝ)) / 2)
    (∀ (D' : Finset (Fin (2 ^ params17.d))) (v₀ : OracleTable params17.d (ZMod 17)),
      v₀ ∈ params17.initialCode →
      ∀ v : Fin 1 → OracleTable params17.d (ZMod 17),
        (∀ j, v j ∈ params17.initialCode) →
        (∀ s ∈ D', cutoffStmt17.base s = v₀ s ∧ ∀ j, cutoffStmt17.terms j s = v j s) →
        (D'.card : ℝ) / (2 ^ params17.d : ℝ) ≤ 1 / 2) ∧
    (∃ c' ∈ params17.initialCode,
      αPaper <
        ((Finset.univ.filter fun s : Fin (2 ^ params17.d) =>
          cutoffStmt17.base s = cutoffStmt17.eval cZero17.batchCoeffs s ∧
            cutoffStmt17.base s = c' s).card : ℝ) / (2 ^ params17.d : ℝ)) ∧
    friBatchGoodStep params17 1 ⌊αUniq * (2 ^ params17.d : ℝ)⌋₊ cutoffStmt17 [] π cZero17 := by
  intro αPaper αUniq
  refine ⟨?_, ?_, ?_⟩
  · intro D' v₀ hv₀ v hv hagree
    have hle : (D'.card : ℝ) ≤ 4 := by
      exact_mod_cast cutoffStmt17_agree_le_four D' v₀ hv₀ v hv hagree
    have hd : (2 ^ params17.d : ℝ) = 16 := by norm_num [params17]
    rw [hd]
    linarith
  · refine ⟨0, params17.initialCode.zero_mem, ?_⟩
    have hfilt :
        (Finset.univ.filter fun s : Fin (2 ^ params17.d) =>
          cutoffStmt17.base s = cutoffStmt17.eval cZero17.batchCoeffs s ∧
            cutoffStmt17.base s = (0 : OracleTable params17.d (ZMod 17)) s) =
        (Finset.univ.filter fun s : Fin (2 ^ params17.d) => cutoffStmt17.base s = 0) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, cutoffStmt17_eval_cZero17,
        Pi.zero_apply]
    have hsq : Real.sqrt ((params17.dim 0 : ℝ) / (2 ^ params17.d : ℝ)) = 1 / 2 := by
      have hr : ((params17.dim 0 : ℝ) / (2 ^ params17.d : ℝ)) = (1 / 2 : ℝ) ^ 2 := by
        norm_num [params17, FRIParams.dim]
      rw [hr, Real.sqrt_sq (by norm_num)]
    rw [hfilt, cutoffStmt17_card_zero_eq_ten]
    dsimp only [αPaper]
    rw [hsq]
    norm_num [params17]
  · have hfloor : ⌊αUniq * (2 ^ params17.d : ℝ)⌋₊ = 10 := by
      dsimp only [αUniq]
      simp only [params17, FRIParams.dim]
      exact (Nat.floor_eq_iff (by positivity)).mpr ⟨by norm_num, by norm_num⟩
    rw [hfloor, friBatchGoodStep_nil_iff]
    intro c' hc'
    rw [cutoffStmt17_eval_cZero17]
    by_contra hgt
    set S := Finset.univ.filter fun s : Fin (2 ^ params17.d) => cutoffStmt17.base s = c' s
    set T := Finset.univ.filter fun s : Fin (2 ^ params17.d) => s.val < 10
    have hT_card : T.card = 10 := by decide
    have hunion_le : (S ∪ T).card ≤ 16 :=
      (Finset.card_le_univ _).trans_eq (by decide : Fintype.card (Fin (2 ^ params17.d)) = 16)
    have hsum := Finset.card_union_add_card_inter S T
    have hinter_ge : 5 ≤ (S ∩ T).card := by omega
    obtain ⟨p, hp_deg, rfl⟩ := mem_reedSolomon.mp hc'
    by_cases hp0 : p = 0
    · subst hp0
      have hS0 : S = Finset.univ.filter fun s => cutoffStmt17.base s = 0 := by
        ext s
        simp only [S, Polynomial.eval_zero]
      have hScard : S.card = 10 := by rw [hS0, cutoffStmt17_card_zero_eq_ten]
      omega
    · have hinj : Function.Injective (params17.eval 0) :=
        cosetEval_injective params17.hg params17.hω (Nat.zero_le _)
      have hsub : S ∩ T ⊆ Finset.univ.filter fun s => p.eval (params17.eval 0 s) = 0 := by
        intro s hs
        obtain ⟨hsS, hsT⟩ := Finset.mem_inter.mp hs
        have hlt10 : s.val < 10 := (Finset.mem_filter.mp hsT).2
        have hbase0 : cutoffStmt17.base s = 0 := by simp only [cutoffStmt17, hlt10, ↓reduceIte]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hsS).2.symm.trans hbase0⟩
      have hle_deg : (S ∩ T).card ≤ p.natDegree :=
        (Finset.card_le_card hsub).trans (card_filter_eval_eq_zero_le hinj hp0)
      have hdeg_lt : p.natDegree < 4 := by
        have hd0 : params17.dim 0 = 4 := by decide
        rw [hd0] at hp_deg
        exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp_deg
      omega

end CutoffCounterexample17

end CslibFrontierTests.Crypto.FRIBatchJohnson
