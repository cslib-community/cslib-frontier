/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

import CslibFrontier.Crypto.Protocols.FRI.BatchSoundness
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import CslibFrontierTests.Crypto.FRI
import CslibFrontierTests.Crypto.FRIJohnson
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# Concrete Nonvacuous Tests for Batched FRI Round-0 Soundness (`BatchSoundness.lean`)

Exercises every public definition and theorem of
`CslibFrontier.Crypto.Protocols.FRI.BatchSoundness` from an ordinary `module` client (no
`import all`) across four concrete prime and extension fields:

1. **Suite 1 (`ZMod 257`, `d = 3, m = 2, kFinal = 1, q = 6, e = 2`, `t = 2` and `t = 0`).**
   Exercises `friBatchTailTranscript` (`_nil`, `_cons`, `_append`, `length_friBatchTailTranscript`),
   `friBatchDoomed`, `friBatchDoomed_nil_iff_not_mem_batchProximityLang`, `friBatchGoodStep`,
   `friBatchGoodStep_nil_iff`, `friBatchGoodStep_cons`, `friBatchIOP_rbrSound` (initialization on
   nonvacuous `badStmt257 ∉ params257.batchProximityLang 2 2`, preservation on good transitions,
   and terminal rejection), marginal challenge laws
   (`uniformOfFintype_friBatchChal_map_batchCoeffs`, `uniformOfFintype_friBatchChal_map_toFRIChal`,
   `toOuterMeasure_uniform_friBatchChal_batchCoeffs`,
   `toOuterMeasure_uniform_friBatchChal_toFRIChal`, `toOuterMeasure_not_friBatchGoodStep_cons`,
   `friBatchQueryRound_escape_le`, `friBatchCommitRound_escape_le_of_weightedLineGap`),
   unique-decoding round-`0` upper bounds (`batchRound0GapBound_of_unique` and
   `batchRound0Escape_of_unique` giving `≤ 8 / 257` for both `t = 2` and `t = 0`, together with
   exact zero round-`0` escape probability `round0Escape257_t0_eq_zero` at `t = 0` where the false
   word is independent of the challenge), contract monotonicity (`.mono`), conditional round-`0`
   escape steps, and end-to-end adaptive two-channel batched BCS-FRI ROM soundness (`< 1 / 3` via
   both `friBatchBCS_romSoundness_bound_of_escape` and
   `friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape`, instantiated on `mkBatchCheater`).
2. **Suite 2 (`ZMod 786433`, beyond-unique-decoding discrete Sudan `m₀ = 1`:
   `d = 4, m = 2, kFinal = 1, q = 8, e = 7, t = 2`).**
   Certifies `2 * 7 + 4 = 18 > 16`, proves `badStmt786 ∉ params786.batchProximityLang 2 7`,
   discharges `batchRound0GapBound_of_johnson_discrete` and
   `batchRound0Escape_of_johnson_discrete` at `(m₀, D₀) = (1, 8)` with exact
   `johnsonCurveBound 16 1 3 8 1 16 = 33008`, and proves adaptive batched BCS-FRI ROM soundness
   `< 1 / 4` instantiated on `mkBatchCheater`.
3. **Suite 3 (`ZMod 26214401`, beyond-Sudan `m₀ = 2` required at `δ = 1 - √ρ = 1 / 2`:
   `d = 4, m = 2, kFinal = 1, q = 8, e = 8, t = 2`).**
   Certifies both `2 * 8 + 4 > 16` and Sudan `m₀ = 1` impossibility (`∀ D₀ < 8,
   #(Sudan.monomials 3 D₀) ≤ 16`), proves `badStmt26M ∉ params26M.batchProximityLang 2 8`,
   discharges `batchRound0GapBound_of_johnson_discrete` and `batchRound0Escape_of_johnson_discrete`
   at `(m₀, D₀) = (2, 15)` (`johnsonCurveBound = 1923030`), and proves adaptive batched BCS-FRI ROM
   soundness `< 2 / 5` instantiated on `mkBatchCheater`.
4. **Suite 4 (`GaloisField 65537 4`, extension field `𝔽_{65537^4}` closed-form Johnson & `η`-gap:
   `d = 6, m = 2, kFinal = 1, q = 6, e = 44, mJ = 2, η = 1 / 16, t = 3`).**
   Certifies `2 * 44 + 4 = 92 > 64` and `badStmtGF ∉ paramsGF.batchProximityLang 3 44`, evaluates
   `friBatchJohnsonRound0Bound paramsGF 2 = 85996339200`, and instantiates
   `batchRound0GapBound_of_johnson`, `batchRound0Escape_of_johnson` (`< 1 / 10 ^ 8`), and
   `batchRound0Escape_of_johnson_eta` (`< 1 / 100`) over `𝔽_{65537^4}`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.FRIBatchSoundness

open scoped BigOperators NNReal ENNReal
open Finset
open Cslib Cslib.Code Cslib.OracleComp Cslib.Probability
open Cslib.Crypto.Protocols.BCS Cslib.Crypto.Protocols.FRI
open CslibFrontierTests.Crypto.FRIJohnson

/-! ### Reusable False-Tuple Projection and Cost-Bounded Batched Cheater Helpers -/

section Helpers

/-- If the `j`-th generator word of `stmt` equals the degree-`dim 0` monomial evaluation on `L_0`
and `e + dim 0 < 2 ^ d`, then `stmt ∉ params.batchProximityLang t e` by projecting any common
batched agreement witness onto word `j` and applying `monomial_far_not_mem_proximityLang`. -/
private theorem not_mem_batchProximityLang_of_monomial_term {F : Type} [Field F]
    (params : FRIParams F) {t e : ℕ} (stmt : FRIBatchStmt F params.d t) (j : Fin t)
    (hterm : stmt.terms j = fun idx => (params.eval 0 idx) ^ params.dim 0)
    (hgap : e + params.dim 0 < 2 ^ params.d) :
    stmt ∉ params.batchProximityLang t e := by
  classical
  rintro ⟨D', hD'_card, _, _, v, hv, hagree⟩
  apply monomial_far_not_mem_proximityLang params hgap
  refine ⟨v j, hv j, ?_⟩
  have hsub : D' ⊆ Finset.univ.filter (fun s : Fin (2 ^ params.d) =>
      (params.eval 0 s) ^ params.dim 0 = v j s) := fun s hs =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ s,
      (congrFun hterm s).symm.trans ((hagree s hs).2 j)⟩
  have hle : D'.card ≤ (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
      (params.eval 0 s) ^ params.dim 0 = v j s).card :=
    Finset.card_le_card hsub
  have htot := card_filter_eq_add_hammingDist
    (fun s : Fin (2 ^ params.d) => (params.eval 0 s) ^ params.dim 0) (v j)
  simp only [Fintype.card_fin] at htot
  omega

/-- Parametric adaptive batched cheating prover (`t_FS = 1`, `t_MT = 1`,
`params.proofOracleQueries` depth-`params.d` openings) for `friBatchIOP params t`. -/
def mkBatchCheater {F : Type} [Field F] (params : FRIParams F) {t : ℕ}
    (badStmt : FRIBatchStmt F params.d t) :
    OracleComp
      (BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
      (FRIBatchStmt F params.d t × BCSProof (params.m + 2) F) := do
  let rootBit ← query
    (spec := BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
    (.inl [true])
  let _c₀ ← query
    (spec := BCSROMSpec (FRIBatchStmt F params.d t) (FRIBatchChal F params.d params.q t))
    (.inr (badStmt, [rootBit], []))
  return (badStmt,
    { roots := fun _ => rootBit
      openings := List.replicate params.proofOracleQueries ⟨0, List.replicate params.d rootBit⟩ })

theorem isCostBounded_FS_mkBatchCheater {F : Type} [Field F] (params : FRIParams F) {t : ℕ}
    (badStmt : FRIBatchStmt F params.d t) :
    IsCostBounded bcsFSCost (mkBatchCheater params badStmt) 1 :=
  IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inl [true]) _ 1 fun rootBit =>
    IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inr (badStmt, [rootBit], [])) _ 0 fun _ =>
      IsCostBounded.pure (cost := bcsFSCost) _ 0

theorem isCostBounded_MT_mkBatchCheater {F : Type} [Field F] (params : FRIParams F) {t : ℕ}
    (badStmt : FRIBatchStmt F params.d t) :
    IsCostBounded bcsMTCost (mkBatchCheater params badStmt) 1 :=
  IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inl [true]) _ 0 fun rootBit =>
    IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inr (badStmt, [rootBit], [])) _ 0 fun _ =>
      IsCostBounded.pure (cost := bcsMTCost) _ 0

theorem mkBatchCheater_openings_le {F : Type} [Field F] (params : FRIParams F) {t : ℕ}
    (badStmt : FRIBatchStmt F params.d t)
    (x : FRIBatchStmt F params.d t) (prf : BCSProof (params.m + 2) F)
    (hmem : (x, prf) ∈ (mkBatchCheater params badStmt).support) :
    ∀ op ∈ prf.openings, op.path.length ≤ params.d := by
  simp only [mkBatchCheater, mem_supportWith_bind_iff, supportWith_query, Set.mem_univ,
    true_and, supportWith_pure, Set.mem_singleton_iff] at hmem
  obtain ⟨rootBit, _, h⟩ := hmem
  cases h
  intro op hop
  rw [(List.mem_replicate.mp hop).2, List.length_replicate]

theorem isCostBounded_soundnessProg_mkBatchCheater {F : Type} [Field F] [DecidableEq F]
    (params : FRIParams F) {t : ℕ} (encSym : F → List Bool) (e : ℕ)
    (badStmt : FRIBatchStmt F params.d t) {Q_MT : ℕ}
    (hQ : 1 + params.proofOracleQueries * (params.d + 1) ≤ Q_MT) :
    IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params t) encSym (params.batchProximityLang t e)
        (mkBatchCheater params badStmt)) Q_MT :=
  (isCostBounded_bcsMTCost_bcsSoundnessProg (friBatchIOP params t) encSym
    (params.batchProximityLang t e) (isCostBounded_MT_mkBatchCheater params badStmt)
    fun x prf hmem =>
      isCostBounded_bcsMTCost_friBatchVerifyROM params t encSym x prf
        (mkBatchCheater_openings_le params badStmt x prf hmem)).mono hQ

end Helpers

/-! ### Suite 1: Invariant, Marginals & Unique-Decoding Batched FRI (`ZMod 257`) -/

section Unique257

open CslibFrontierTests.Crypto.FRI

/-- Nonvacuous false `3`-word (`t = 2`) statement over `ZMod 257` reusing the shared `params257`,
`honestWord`, and `farWord` fixtures from `CslibFrontierTests.Crypto.FRI`. -/
def badStmt257 : FRIBatchStmt (ZMod 257) params257.d 2 where
  base := honestWord
  terms := ![0, farWord]

theorem badStmt257_not_mem : badStmt257 ∉ params257.batchProximityLang 2 2 := by
  rintro ⟨D', hcard, _, _, v, hv, hagree⟩
  have hle : D'.card ≤ 4 := card_agree_farWord_le_four (hv 1) fun s hs => (hagree s hs).2 1
  change 2 ^ 3 - 2 ≤ D'.card at hcard
  omega

/-- Nonvacuous false `1`-word (`t = 0`) statement over `ZMod 257` (`base = farWord`). -/
def badStmt257Zero : FRIBatchStmt (ZMod 257) params257.d 0 where
  base := farWord
  terms := Fin.elim0

theorem badStmt257Zero_not_mem : badStmt257Zero ∉ params257.batchProximityLang 0 2 :=
  (mem_batchProximityLang_zero_iff params257 2 badStmt257Zero).not.mpr farWord_not_mem_proximityLang

-- Direct checks on `friBatchTailTranscript`, `friBatchDoomed`, `friBatchGoodStep`, and
-- `friBatchIOP_rbrSound` (initialization, preservation on good transitions, terminal rejection).
example (π : OracleTable 3 (ZMod 257)) (c : FRIBatchChal (ZMod 257) 3 6 2) :
    friBatchTailTranscript ([] : List (OracleTable 3 (ZMod 257) × FRIBatchChal (ZMod 257) 3 6 2)) =
      [] ∧
    friBatchTailTranscript [(π, c)] = [(π, c.toFRIChal)] ∧
    friBatchTailTranscript ([(π, c)] ++ [(π, c)]) =
      friBatchTailTranscript [(π, c)] ++ friBatchTailTranscript [(π, c)] ∧
    (friBatchTailTranscript [(π, c)]).length = 1 :=
  ⟨friBatchTailTranscript_nil, friBatchTailTranscript_cons π c [],
    friBatchTailTranscript_append [(π, c)] [(π, c)], length_friBatchTailTranscript [(π, c)]⟩

example : friBatchDoomed params257 2 5 badStmt257 [] :=
  (friBatchDoomed_nil_iff_not_mem_batchProximityLang params257 2 badStmt257 (by decide)).mpr
    badStmt257_not_mem

example (π : OracleTable params257.d (ZMod 257))
    (c : FRIBatchChal (ZMod 257) params257.d params257.q 2) :
    (friBatchGoodStep params257 2 5 badStmt257 [] π c ↔
      ∀ c' ∈ params257.initialCode,
        (Finset.univ.filter fun s : Fin (2 ^ params257.d) =>
          badStmt257.eval c.batchCoeffs s = c' s).card ≤ 5) ∧
    (friBatchGoodStep params257 2 5 badStmt257 [(π, c)] π c ↔
      friGoodStep params257 5 (badStmt257.eval c.batchCoeffs) [] π c.toFRIChal) :=
  ⟨friBatchGoodStep_nil_iff params257 2 5 badStmt257 π c,
    friBatchGoodStep_cons params257 2 5 badStmt257 π c [] π c⟩

example :
    friBatchDoomed params257 2 5 badStmt257 [] ∧
    (∀ pref π c,
      friBatchDoomed params257 2 5 badStmt257 pref →
      friBatchGoodStep params257 2 5 badStmt257 pref π c →
      friBatchDoomed params257 2 5 badStmt257 (pref ++ [(π, c)])) ∧
    (∀ oracles chals,
      friBatchDoomed params257 2 5 badStmt257
        (List.ofFn fun j : Fin 4 => (oracles j, chals j)) →
      iopVerify (friBatchIOP params257 2) badStmt257 chals oracles = false) :=
  ⟨(friBatchIOP_rbrSound params257 2 2).init_doomed badStmt257 badStmt257_not_mem,
    (friBatchIOP_rbrSound params257 2 2).step_doomed badStmt257,
    (friBatchIOP_rbrSound params257 2 2).reject_of_doomed badStmt257⟩

-- Direct checks on marginal challenge projections and 1-line tail escape lifts.
example (S₀ : Set (Fin 2 → ZMod 257)) (S₁ : Set (FRIChal (ZMod 257) 3 6)) :
    (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) 3 6 2)).map FRIBatchChal.batchCoeffs =
      PMF.uniformOfFintype (Fin 2 → ZMod 257) ∧
    (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) 3 6 2)).map FRIBatchChal.toFRIChal =
      PMF.uniformOfFintype (FRIChal (ZMod 257) 3 6) ∧
    (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) 3 6 2)).toOuterMeasure
      {c | c.batchCoeffs ∈ S₀} =
      (PMF.uniformOfFintype (Fin 2 → ZMod 257)).toOuterMeasure S₀ ∧
    (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) 3 6 2)).toOuterMeasure
      {c | c.toFRIChal ∈ S₁} =
      (PMF.uniformOfFintype (FRIChal (ZMod 257) 3 6)).toOuterMeasure S₁ :=
  ⟨uniformOfFintype_friBatchChal_map_batchCoeffs 3 6 2,
    uniformOfFintype_friBatchChal_map_toFRIChal 3 6 2,
    toOuterMeasure_uniform_friBatchChal_batchCoeffs S₀,
    toOuterMeasure_uniform_friBatchChal_toFRIChal S₁⟩

example (π₀ π₁ π₂ π₃ : OracleTable params257.d (ZMod 257))
    (c₀ c₁ c₂ : FRIBatchChal (ZMod 257) params257.d params257.q 2)
    (hd₁ : friBatchDoomed params257 2 (2 ^ params257.d - 2 - 1) badStmt257 [(π₀, c₀)])
    (hd₃ : friBatchDoomed params257 2 (2 ^ params257.d - 2 - 1) badStmt257
      [(π₀, c₀), (π₁, c₁), (π₂, c₂)]) :
    (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) params257.d params257.q 2)).toOuterMeasure
        {c | ¬ friBatchGoodStep params257 2 (2 ^ params257.d - 2 - 1) badStmt257 [(π₀, c₀)] π₁ c} =
      (PMF.uniformOfFintype (FRIChal (ZMod 257) params257.d params257.q)).toOuterMeasure
        {c' | ¬ friGoodStep params257 (2 ^ params257.d - 2 - 1) (badStmt257.eval c₀.batchCoeffs)
          [] π₁ c'} ∧
    (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) params257.d params257.q 2)).toOuterMeasure
        {c | ¬ friBatchGoodStep params257 2 (2 ^ params257.d - 2 - 1) badStmt257 [(π₀, c₀)] π₁ c} ≤
      (4 : ℝ≥0∞) / 257 ∧
    (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) params257.d params257.q 2)).toOuterMeasure
        {c | ¬ friBatchGoodStep params257 2 (2 ^ params257.d - 2 - 1) badStmt257
          [(π₀, c₀), (π₁, c₁), (π₂, c₂)] π₃ c} ≤
      ((5 : ℝ≥0∞) / 8) ^ 6 := by
  refine ⟨toOuterMeasure_not_friBatchGoodStep_cons params257 2 (2 ^ params257.d - 2 - 1)
    badStmt257 π₀ c₀ [] π₁, ?_, ?_⟩
  · refine (friBatchCommitRound_escape_le_of_weightedLineGap params257 2
      (weightedLineGapBound_of_unique params257 (e := 2) (by decide))
      badStmt257 [(π₀, c₀)] (by simp) (by simp [params257]) π₁ hd₁).trans_eq ?_
    simp only [params257, ZMod.card]
    norm_num
  · refine (friBatchQueryRound_escape_le params257 2 (2 ^ params257.d - 2 - 1) badStmt257
      [(π₀, c₀), (π₁, c₁), (π₂, c₂)] rfl π₃ hd₃).trans_eq ?_
    simp only [params257]
    norm_num

-- Unique-decoding `BatchRound0GapBound` & `BatchRound0Escape` upper bounds (`≤ 8 / 257` for both
-- `t = 2` and `t = 0`), exact zero round-`0` escape probability at `t = 0`, plus `.mono`,
-- `batchRound0Escape_of_gapBound`, and `friBatchRound0_escape_le_of_escape`.
theorem round0Gap257_t2 : BatchRound0GapBound params257 2 2 8 :=
  batchRound0GapBound_of_unique params257 2 (by decide)

theorem round0Escape257_t2 : BatchRound0Escape params257 2 2 ((8 : ℝ≥0∞) / 257) := by
  simpa only [params257, ZMod.card, Nat.cast_ofNat, (by norm_num : (2 : ℝ≥0∞) ^ 3 = 8)] using
    batchRound0Escape_of_unique params257 2 (e := 2) (by decide)

theorem round0Escape257_t0 : BatchRound0Escape params257 0 2 ((8 : ℝ≥0∞) / 257) := by
  simpa only [params257, ZMod.card, Nat.cast_ofNat, (by norm_num : (2 : ℝ≥0∞) ^ 3 = 8)] using
    batchRound0Escape_of_unique params257 0 (e := 2) (by decide)

/-- At batch size `t = 0`, `badStmt257Zero.eval c.batchCoeffs = farWord` is independent of the
challenge, so the round-`0` escape event is empty and its probability is `0` (`8 / 257` in
`round0Escape257_t0` is a `t`-uniform upper bound). -/
theorem round0Escape257_t0_eq_zero (π : OracleTable params257.d (ZMod 257)) :
    (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) params257.d params257.q 0)).toOuterMeasure
      {c | ¬ friBatchGoodStep params257 0 (2 ^ params257.d - 2 - 1) badStmt257Zero [] π c} =
    0 := by
  have hempty :
      {c : FRIBatchChal (ZMod 257) params257.d params257.q 0 |
        ¬ friBatchGoodStep params257 0 (2 ^ params257.d - 2 - 1) badStmt257Zero [] π c} =
      ∅ := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not,
      friBatchGoodStep_nil_iff, FRIBatchStmt.eval_zero]
    intro c' hc'
    refine (card_agree_farWord_le_four hc' fun s hs => ?_).trans (by decide)
    rw [Finset.mem_filter] at hs
    exact hs.2
  rw [hempty]
  exact MeasureTheory.OuterMeasure.empty _

example (π : OracleTable params257.d (ZMod 257)) :
    BatchRound0GapBound params257 2 2 9 ∧
    BatchRound0Escape params257 2 2 ((9 : ℝ≥0∞) / 257) ∧
    (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) params257.d params257.q 2)).toOuterMeasure
      {c | ¬ friBatchGoodStep params257 2 (2 ^ params257.d - 2 - 1) badStmt257 [] π c} ≤
        (8 : ℝ≥0∞) / 257 ∧
    (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) params257.d params257.q 0)).toOuterMeasure
      {c | ¬ friBatchGoodStep params257 0 (2 ^ params257.d - 2 - 1) badStmt257Zero [] π c} ≤
        (8 : ℝ≥0∞) / 257 := by
  refine ⟨round0Gap257_t2.mono (by omega),
    round0Escape257_t2.mono (ENNReal.div_le_div_right (by norm_num) 257), ?_,
    friBatchRound0_escape_le_of_escape params257 0 round0Escape257_t0 badStmt257Zero_not_mem π⟩
  refine (friBatchRound0_escape_le_of_escape params257 2
    (batchRound0Escape_of_gapBound params257 round0Gap257_t2) badStmt257_not_mem π).trans_eq ?_
  simp only [ZMod.card, Nat.cast_ofNat]

-- Uniform RBR error & escape for batched FRI over `ZMod 257`.
private theorem friBatch257_rbrError_eq :
    friBatchRBRError params257 ((8 : ℝ≥0∞) / 257) 2 (2 ^ (params257.d - 1)) =
      (15625 : ℝ≥0∞) / 262144 := by
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

theorem friBatch257_rbrEscape :
    ∀ stmt ∉ params257.batchProximityLang 2 2, ∀ pref π,
      friBatchDoomed params257 2 5 stmt pref →
      (PMF.uniformOfFintype (FRIBatchChal (ZMod 257) 3 6 2)).toOuterMeasure
        {c | ¬ friBatchGoodStep params257 2 5 stmt pref π c} ≤
      (15625 : ℝ≥0∞) / 262144 := by
  intro stmt hnot pref π hdoomed
  rw [← friBatch257_rbrError_eq]
  exact friBatchRBREscape_of_escape params257 2 round0Escape257_t2
    (weightedLineGapBound_of_unique params257 (e := 2) (by decide)) stmt hnot pref π hdoomed

private theorem card_friBatchChal257 :
    (Fintype.card (FRIBatchChal (ZMod 257) params257.d params257.q 2) : ℝ≥0∞) = 4449787707392 := by
  rw [card_friBatchChal, ZMod.card]
  norm_num [params257]

/-- **End-to-end adaptive two-channel batched BCS-FRI ROM soundness (`< 1 / 3`)** over `ZMod 257`
via `friBatchBCS_romSoundness_bound_of_escape` (`t_FS = 1, Q_MT = 500, σ = 32`). -/
theorem friBatch257_romSoundness_lt_one_third
    (P : OracleComp
      (BCSROMSpec (FRIBatchStmt (ZMod 257) 3 2) (FRIBatchChal (ZMod 257) 3 6 2))
      (FRIBatchStmt (ZMod 257) 3 2 × BCSProof 4 (ZMod 257)))
    (hFS : IsCostBounded bcsFSCost P 1)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params257 2) (encZMod (p := 257))
        (params257.batchProximityLang 2 2) P) 500) :
    bcsSoundnessGame (friBatchIOP params257 2) (encZMod (p := 257))
      (params257.batchProximityLang 2 2) P 32 true < 1 / 3 := by
  refine lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_escape params257 2 round0Escape257_t2
      (weightedLineGapBound_of_unique params257 (e := 2) (by decide))
      (leftInverse_decZMod_encZMod 257) 32 hFS hMT) ?_
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
      (params257.batchProximityLang 2 2) (mkBatchCheater params257 badStmt257) 32 true < 1 / 3 :=
  friBatch257_romSoundness_lt_one_third (mkBatchCheater params257 badStmt257)
    (isCostBounded_FS_mkBatchCheater params257 badStmt257)
    (isCostBounded_soundnessProg_mkBatchCheater params257 (encZMod (p := 257)) 2 badStmt257
      (by decide : 1 + params257.proofOracleQueries * (params257.d + 1) ≤ 500))

/-- **End-to-end prover/verifier-split batched BCS-FRI ROM soundness (`< 1 / 3`)** over `ZMod 257`
via `friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape` (`t_MT = 1, t_FS = 1, L_path = 3,
σ = 24`). -/
theorem friBatch257_prover_verifier_lt_one_third
    (P : OracleComp
      (BCSROMSpec (FRIBatchStmt (ZMod 257) 3 2) (FRIBatchChal (ZMod 257) 3 6 2))
      (FRIBatchStmt (ZMod 257) 3 2 × BCSProof 4 (ZMod 257)))
    (hMT : IsCostBounded bcsMTCost P 1)
    (hFS : IsCostBounded bcsFSCost P 1)
    (hops : ∀ x prf, (x, prf) ∈ P.support → ∀ op ∈ prf.openings, op.path.length ≤ 3) :
    bcsSoundnessGame (friBatchIOP params257 2) (encZMod (p := 257))
      (params257.batchProximityLang 2 2) P 24 true < 1 / 3 := by
  refine lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_prover_verifier_of_escape params257 2 round0Escape257_t2
      (weightedLineGapBound_of_unique params257 (e := 2) (by decide))
      (leftInverse_decZMod_encZMod 257) 24 hMT hFS hops) ?_
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
      (params257.batchProximityLang 2 2) (mkBatchCheater params257 badStmt257) 24 true < 1 / 3 :=
  friBatch257_prover_verifier_lt_one_third (mkBatchCheater params257 badStmt257)
    (isCostBounded_MT_mkBatchCheater params257 badStmt257)
    (isCostBounded_FS_mkBatchCheater params257 badStmt257)
    (mkBatchCheater_openings_le params257 badStmt257)

end Unique257

/-! ### Suite 2: Beyond-Unique-Decoding Discrete Sudan (`ZMod 786433`, `e = 7 > e_uniq = 6`) -/

section DiscreteJohnson786433

instance instPrime786433 : Fact (Nat.Prime 786433) := ⟨by norm_num⟩

/-- `2`-folding-round (`4` total batched rounds), depth-`4` (`|L_0| = 16`), rate-`1/4`
(`dim 0 = 4`), `q = 8` batched FRI parameters over `ZMod 786433`. -/
def params786 : FRIParams (ZMod 786433) where
  d := 4
  m := 2
  kFinal := 1
  q := 8
  g := 1
  ω := 541396
  hm := by omega
  hkPos := by omega
  hkLe := by omega
  hg := one_ne_zero
  h2 := by decide
  hω := isPrimitiveRoot_two_pow_of_neg_one (by decide) (by decide) (by decide)

-- Strictly beyond unique decoding (`2 * 7 + 4 = 18 > 16`).
theorem params786_beyond_unique : ¬ (2 * 7 + params786.dim 0 ≤ 2 ^ params786.d) := by
  decide

def badStmt786 : FRIBatchStmt (ZMod 786433) 4 2 where
  base := 0
  terms := ![0, fun idx => (params786.eval 0 idx) ^ 4]

theorem badStmt786_not_mem : badStmt786 ∉ params786.batchProximityLang 2 7 :=
  not_mem_batchProximityLang_of_monomial_term params786 badStmt786 ⟨1, by omega⟩ rfl (by decide)

/-- Unconditional round-`0` `BatchRound0GapBound` over `ZMod 786433` at radius `e = 7` via
`batchRound0GapBound_of_johnson_discrete` (`m₀ = 1, D₀ = 8, B_batch = 33008`). -/
theorem round0Gap786 : BatchRound0GapBound params786 2 7 33008 :=
  batchRound0GapBound_of_johnson_discrete params786 2 (m₀ := 1) (D₀ := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional round-`0` `BatchRound0Escape` (`≤ 33008 / 786433 < 1 / 20`) over `ZMod 786433`. -/
theorem round0Escape786 : BatchRound0Escape params786 2 7 ((33008 : ℝ≥0∞) / 786433) := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    batchRound0Escape_of_johnson_discrete params786 2 (e := 7) (m₀ := 1) (D₀ := 8)
      (B_batch := 33008) (by decide) (by decide) (by decide) (by decide) (by decide)

private def mRound786 : Fin 2 → ℕ := ![1, 1]
private def DRound786 : Fin 2 → ℕ := ![4, 2]

theorem weightedLineGap786 : WeightedLineGapBound params786 8 17476 := by
  refine weightedLineGapBound_of_johnson_discrete params786 (e := 7) (B_commit := 17476)
    (by decide) mRound786 DRound786 ?_ ?_ ?_ ?_ ?_
  all_goals intro i; fin_cases i <;> decide

private theorem friBatch786_rbrError_eq :
    friBatchRBRError params786 ((33008 : ℝ≥0∞) / 786433) 7 17476 =
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

/-- **End-to-end beyond-unique-decoding batched BCS-FRI ROM soundness (`< 1 / 4`)** over
`ZMod 786433` at radius `e = 7 > e_uniq = 6`. -/
theorem friBatch786_romSoundness_lt_quarter
    (P : OracleComp
      (BCSROMSpec (FRIBatchStmt (ZMod 786433) 4 2) (FRIBatchChal (ZMod 786433) 4 8 2))
      (FRIBatchStmt (ZMod 786433) 4 2 × BCSProof 4 (ZMod 786433)))
    (hFS : IsCostBounded bcsFSCost P 1)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params786 2) (encZMod (p := 786433))
        (params786.batchProximityLang 2 7) P) 500) :
    bcsSoundnessGame (friBatchIOP params786 2) (encZMod (p := 786433))
      (params786.batchProximityLang 2 7) P 32 true < 1 / 4 := by
  refine lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_escape params786 2 round0Escape786 weightedLineGap786
      (leftInverse_decZMod_encZMod 786433) 32 hFS hMT) ?_
  rw [friBatch786_rbrError_eq, card_friBatchChal786]
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
      (params786.batchProximityLang 2 7) (mkBatchCheater params786 badStmt786) 32 true < 1 / 4 :=
  friBatch786_romSoundness_lt_quarter (mkBatchCheater params786 badStmt786)
    (isCostBounded_FS_mkBatchCheater params786 badStmt786)
    (isCostBounded_soundnessProg_mkBatchCheater params786 (encZMod (p := 786433)) 7 badStmt786
      (by decide : 1 + params786.proofOracleQueries * (params786.d + 1) ≤ 500))

end DiscreteJohnson786433

/-! ### Suite 3: Beyond-Sudan (`m₀ = 2` Required) at `δ = 1 - √ρ = 1 / 2` (`ZMod 26214401`) -/

section BeyondSudan26214401

instance instPrime26214401 : Fact (Nat.Prime 26214401) := ⟨by norm_num⟩

/-- `2`-folding-round (`4` total batched rounds), depth-`4` (`|L_0| = 16`), rate-`1/4`
(`dim 0 = 4`), `q = 8` batched FRI parameters over `ZMod 26214401`. -/
def params26M : FRIParams (ZMod 26214401) where
  d := 4
  m := 2
  kFinal := 1
  q := 8
  g := 1
  ω := 12534745
  hm := by omega
  hkPos := by omega
  hkLe := by omega
  hg := one_ne_zero
  h2 := by decide
  hω := isPrimitiveRoot_two_pow_of_neg_one (by decide) (by decide) (by decide)

-- Certify BOTH beyond-unique-decoding (`2 * 8 + 4 = 20 > 16`) AND Sudan `m₀ = 1` impossibility
-- (`∀ D₀ < 1 * (16 - 8), #(Sudan.monomials 3 D₀) ≤ 16`).
theorem params26M_beyond_sudan_m1 :
    ¬ (2 * 8 + params26M.dim 0 ≤ 2 ^ params26M.d) ∧
      ∀ D₀ : Fin 8, #(Sudan.monomials (params26M.dim 0 - 1) D₀.val) ≤ 2 ^ params26M.d := by
  decide

def badStmt26M : FRIBatchStmt (ZMod 26214401) 4 2 where
  base := 0
  terms := ![0, fun idx => (params26M.eval 0 idx) ^ 4]

theorem badStmt26M_not_mem : badStmt26M ∉ params26M.batchProximityLang 2 8 :=
  not_mem_batchProximityLang_of_monomial_term params26M badStmt26M ⟨1, by omega⟩ rfl (by decide)

/-- Unconditional beyond-Sudan (`m₀ = 2, D₀ = 15`) `BatchRound0GapBound` over `ZMod 26214401` at
`e = 8` (`δ = 1 / 2 = 1 - √(1 / 4)`), with exact `johnsonCurveBound = 1923030`. -/
theorem round0Gap26M : BatchRound0GapBound params26M 2 8 1923030 :=
  batchRound0GapBound_of_johnson_discrete params26M 2 (m₀ := 2) (D₀ := 15)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional beyond-Sudan `BatchRound0Escape` (`≤ 1923030 / 26214401 < 1 / 13`). -/
theorem round0Escape26M : BatchRound0Escape params26M 2 8 ((1923030 : ℝ≥0∞) / 26214401) := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    batchRound0Escape_of_johnson_discrete params26M 2 (e := 8) (m₀ := 2) (D₀ := 15)
      (B_batch := 1923030) (by decide) (by decide) (by decide) (by decide) (by decide)

private def mRound26M : Fin 2 → ℕ := ![1, 2]
private def DRound26M : Fin 2 → ℕ := ![3, 3]

theorem weightedLineGap26M : WeightedLineGapBound params26M 7 21270 := by
  refine weightedLineGapBound_of_johnson_discrete params26M (e := 8) (B_commit := 21270)
    (by decide) mRound26M DRound26M ?_ ?_ ?_ ?_ ?_
  all_goals intro i; fin_cases i <;> decide

private theorem friBatch26M_rbrError_eq :
    friBatchRBRError params26M ((1923030 : ℝ≥0∞) / 26214401) 8 21270 =
      (1923030 : ℝ≥0∞) / 26214401 := by
  have h1_nn : (21270 / 26214401 : ℝ≥0) ≤ 5764801 / 4294967296 := by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have h1 : (21270 : ℝ≥0∞) / 26214401 ≤ 5764801 / 4294967296 := by
    simpa only [ENNReal.coe_div (by norm_num : (26214401 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr h1_nn
  have h2_nn : (5764801 / 4294967296 : ℝ≥0) ≤ 1923030 / 26214401 := by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have h2 : (5764801 : ℝ≥0∞) / 4294967296 ≤ 1923030 / 26214401 := by
    simpa only [ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (26214401 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr h2_nn
  have hpow : (((7 : ℝ≥0∞) / 16) ^ 8) = (5764801 : ℝ≥0∞) / 4294967296 := by
    have hnn : ((7 / 16 : ℝ≥0) ^ 8) = 5764801 / 4294967296 := by
      rw [← NNReal.coe_inj]; push_cast; norm_num
    simpa only [ENNReal.coe_pow, ENNReal.coe_div (by norm_num : (16 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using
      congrArg ENNReal.ofNNReal hnn
  have hcard : (Fintype.card (ZMod 26214401) : ℝ≥0∞) = 26214401 := by
    simp only [ZMod.card, Nat.cast_ofNat]
  simp only [friBatchRBRError, friRBRError, params26M, hcard,
    (by norm_num : ((21270 : ℕ) : ℝ≥0∞) = 21270),
    (by norm_num : ((2 ^ 4 - 8 - 1 : ℕ) : ℝ≥0∞) = 7),
    (by norm_num : (2 : ℝ≥0∞) ^ 4 = 16), hpow, max_eq_right h1, max_eq_left h2]

private theorem card_friBatchChal26M :
    (Fintype.card (FRIBatchChal (ZMod 26214401) params26M.d params26M.q 2) : ℝ≥0∞) =
      77371261309773760331756387434496 := by
  rw [card_friBatchChal, ZMod.card]
  norm_num [params26M]

/-- **End-to-end beyond-Sudan (`m₀ = 2`) batched BCS-FRI ROM soundness (`< 2 / 5`)** over
`ZMod 26214401` at `δ = 1 - √ρ = 1 / 2`. -/
theorem friBatch26M_romSoundness_lt_two_fifths
    (P : OracleComp
      (BCSROMSpec (FRIBatchStmt (ZMod 26214401) 4 2) (FRIBatchChal (ZMod 26214401) 4 8 2))
      (FRIBatchStmt (ZMod 26214401) 4 2 × BCSProof 4 (ZMod 26214401)))
    (hFS : IsCostBounded bcsFSCost P 1)
    (hMT : IsCostBounded bcsMTCost
      (bcsSoundnessProg (friBatchIOP params26M 2) (encZMod (p := 26214401))
        (params26M.batchProximityLang 2 8) P) 500) :
    bcsSoundnessGame (friBatchIOP params26M 2) (encZMod (p := 26214401))
      (params26M.batchProximityLang 2 8) P 32 true < 2 / 5 := by
  refine lt_of_le_of_lt
    (friBatchBCS_romSoundness_bound_of_escape params26M 2 round0Escape26M weightedLineGap26M
      (leftInverse_decZMod_encZMod 26214401) 32 hFS hMT) ?_
  rw [friBatch26M_rbrError_eq, card_friBatchChal26M]
  have hnn :
      (5 * (1923030 / 26214401 + 5 * (1 / 77371261309773760331756387434496)) +
        500 * (1520 * (1 / 4294967296)) : ℝ≥0) < 2 / 5 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hnn
  simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_one,
    ENNReal.coe_div (by norm_num : (26214401 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (77371261309773760331756387434496 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (4294967296 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (5 : ℝ≥0) ≠ 0)] at hcast
  simpa only [params26M,
    (by norm_num : ((1 + (2 + 2) : ℕ) : ℝ≥0∞) = 5),
    (by norm_num : ((500 : ℕ) : ℝ≥0∞) = 500),
    (by norm_num : ((3 * 500 + (2 + 2) * (1 + (2 + 2)) : ℕ) : ℝ≥0∞) = 1520),
    (by norm_num : (2 : ℝ≥0∞) ^ 32 = 4294967296)] using hcast

example :
    bcsSoundnessGame (friBatchIOP params26M 2) (encZMod (p := 26214401))
      (params26M.batchProximityLang 2 8) (mkBatchCheater params26M badStmt26M) 32 true < 2 / 5 :=
  friBatch26M_romSoundness_lt_two_fifths (mkBatchCheater params26M badStmt26M)
    (isCostBounded_FS_mkBatchCheater params26M badStmt26M)
    (isCostBounded_soundnessProg_mkBatchCheater params26M (encZMod (p := 26214401)) 8 badStmt26M
      (by decide : 1 + params26M.proofOracleQueries * (params26M.d + 1) ≤ 500))

end BeyondSudan26214401

/-! ### Suite 4: Extension Field `𝔽_{65537^4}` Closed-Form Johnson & `η`-Gap -/

section ExtensionFieldGF65537_4

instance instPrime65537 : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

abbrev GF65537_4 : Type := GaloisField 65537 4

noncomputable local instance : Fintype GF65537_4 := Fintype.ofFinite GF65537_4

private theorem gf65537_4_two_ne_zero : (2 : GF65537_4) ≠ 0 := by
  intro h0
  rw [← Nat.cast_ofNat, CharP.cast_eq_zero_iff GF65537_4 65537] at h0
  omega

private theorem gf65537_4_omega_pow32 :
    (algebraMap (ZMod 65537) GF65537_4 8224) ^ (2 ^ 5) = -1 := by
  rw [← map_pow, (by decide : (8224 : ZMod 65537) ^ (2 ^ 5) = -1), map_neg, map_one]

/-- Depth-`6` (`|L_0| = 64`), `2`-folding-round, rate-`1 / 16` (`dim 0 = 4`, exact rational
`√ρ = 1 / 4`), `q = 6` batched FRI parameters over the degree-`4` extension field
`GaloisField 65537 4` (`|F| = 65537 ^ 4 = 18448995736829952001`). -/
noncomputable def paramsGF : FRIParams GF65537_4 where
  d := 6
  m := 2
  kFinal := 1
  q := 6
  g := 1
  ω := algebraMap (ZMod 65537) GF65537_4 8224
  hm := by omega
  hkPos := by omega
  hkLe := by omega
  hg := one_ne_zero
  h2 := gf65537_4_two_ne_zero
  hω := isPrimitiveRoot_two_pow_of_neg_one (by decide) gf65537_4_two_ne_zero gf65537_4_omega_pow32

-- Strictly beyond unique decoding (`2 * 44 + 4 > 64`) and explicit `friBatchJohnsonRound0Bound`.
example : ¬ (2 * 44 + paramsGF.dim 0 ≤ 2 ^ paramsGF.d) := by decide
example : friBatchJohnsonRound0Bound paramsGF 2 = 85996339200 := rfl

/-- Nonvacuous false `4`-word (`t = 3`) affine batch statement over `𝔽_{65537^4}` at `e = 44`. -/
noncomputable def badStmtGF : FRIBatchStmt GF65537_4 paramsGF.d 3 where
  base := 0
  terms := ![0, 0, fun idx => (paramsGF.eval 0 idx) ^ 4]

theorem badStmtGF_not_mem : badStmtGF ∉ paramsGF.batchProximityLang 3 44 :=
  not_mem_batchProximityLang_of_monomial_term paramsGF badStmtGF ⟨2, by omega⟩ rfl (by decide)

private theorem paramsGF_sqrt_rate :
    Real.sqrt ((paramsGF.dim 0 : ℝ) / (2 ^ paramsGF.d : ℝ)) = 1 / 4 := by
  have hrat : ((paramsGF.dim 0 : ℝ) / (2 ^ paramsGF.d : ℝ)) = (1 / 4 : ℝ) ^ 2 := by
    norm_num [paramsGF, FRIParams.dim]
  rw [hrat, Real.sqrt_sq (by norm_num)]

private theorem paramsGF_johnson_slack :
    (44 : ℝ) / (2 ^ paramsGF.d : ℝ) ≤
      1 - Real.sqrt ((paramsGF.dim 0 : ℝ) / (2 ^ paramsGF.d : ℝ)) -
        Real.sqrt ((paramsGF.dim 0 : ℝ) / (2 ^ paramsGF.d : ℝ)) / (2 * (2 : ℝ)) := by
  rw [paramsGF_sqrt_rate]
  norm_num [paramsGF]

private theorem paramsGF_eta_slack :
    (44 : ℝ) / (2 ^ paramsGF.d : ℝ) ≤
      1 - Real.sqrt ((paramsGF.dim 0 : ℝ) / (2 ^ paramsGF.d : ℝ)) - (1 / 16 : ℝ) := by
  rw [paramsGF_sqrt_rate]
  norm_num [paramsGF]

private theorem card_gf65537_4 : (Fintype.card GF65537_4 : ℝ) = (65537 : ℝ) ^ 4 := by
  have hnat : Fintype.card GF65537_4 = 65537 ^ 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 65537 (n := 4) (by omega)
  exact_mod_cast hnat

/-- Closed-form integer Johnson `BatchRound0GapBound` over `𝔽_{65537^4}` (`t = 3, e = 44, mJ = 2`).
-/
theorem round0GapGF_johnson [DecidableEq GF65537_4] :
    BatchRound0GapBound paramsGF 3 44 85996339200 :=
  batchRound0GapBound_of_johnson paramsGF 3 (e := 44) (mJ := 2) (by omega)
    paramsGF_johnson_slack

/-- Closed-form Johnson `BatchRound0Escape` over `𝔽_{65537^4}` (`t = 3, e = 44, mJ = 2`), strictly
bounded by `< 1 / 10 ^ 8`. -/
theorem round0EscapeGF_johnson_lt [DecidableEq GF65537_4] :
    ∀ stmt ∉ paramsGF.batchProximityLang 3 44,
      (PMF.uniformOfFintype (Fin 3 → GF65537_4)).toOuterMeasure
        {x | ∃ c ∈ paramsGF.initialCode,
          2 ^ paramsGF.d - 44 - 1 <
            (Finset.univ.filter fun s : Fin (2 ^ paramsGF.d) => stmt.eval x s = c s).card} <
        (1 : ℝ≥0∞) / 10 ^ 8 := by
  have hesc := batchRound0Escape_of_johnson paramsGF 3 (e := 44) (mJ := 2) (by omega)
    paramsGF_johnson_slack
  intro stmt hnot
  refine lt_of_le_of_lt (hesc stmt hnot) ?_
  have hlt_real :
      1800 * ((2 + 1 : ℝ) ^ 6) * ((2 ^ paramsGF.d : ℝ) ^ 2) /
        (((paramsGF.dim 0 : ℝ) / (2 ^ paramsGF.d : ℝ)) * (Fintype.card GF65537_4 : ℝ)) <
      (1 : ℝ) / 10 ^ 8 := by
    rw [card_gf65537_4]
    norm_num [paramsGF, FRIParams.dim]
  have hone : ((1 : ℝ≥0∞) / 10 ^ 8) = ENNReal.ofReal ((1 : ℝ) / 10 ^ 8) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one]
    norm_num
  rw [hone]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt_real

/-- Closed-form `η`-gap Johnson `BatchRound0Escape` over `𝔽_{65537^4}`
(`t = 3, e = 44, η = 1 / 16`), strictly bounded by `< 1 / 100`. -/
theorem round0EscapeGF_eta_lt [DecidableEq GF65537_4] :
    ∀ stmt ∉ paramsGF.batchProximityLang 3 44,
      (PMF.uniformOfFintype (Fin 3 → GF65537_4)).toOuterMeasure
        {x | ∃ c ∈ paramsGF.initialCode,
          2 ^ paramsGF.d - 44 - 1 <
            (Finset.univ.filter fun s : Fin (2 ^ paramsGF.d) => stmt.eval x s = c s).card} <
        (1 : ℝ≥0∞) / 100 := by
  have hesc := batchRound0Escape_of_johnson_eta paramsGF 3 (e := 44) (η := 1 / 16)
    (by norm_num) paramsGF_eta_slack
  intro stmt hnot
  refine lt_of_le_of_lt (hesc stmt hnot) ?_
  have hlt_real :
      115200 * ((2 ^ paramsGF.d : ℝ) ^ 2) /
        (((paramsGF.dim 0 : ℝ) / (2 ^ paramsGF.d : ℝ)) * ((1 / 16 : ℝ) ^ 6) *
          (Fintype.card GF65537_4 : ℝ)) <
      (1 : ℝ) / 100 := by
    rw [card_gf65537_4]
    norm_num [paramsGF, FRIParams.dim]
  have hone : ((1 : ℝ≥0∞) / 100) = ENNReal.ofReal ((1 : ℝ) / 100) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one]
    norm_num
  rw [hone]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt_real

-- Nonvacuous instantiations on `badStmtGF ∉ paramsGF.batchProximityLang 3 44`.
example [DecidableEq GF65537_4] :
    (PMF.uniformOfFintype (Fin 3 → GF65537_4)).toOuterMeasure
      {x | ∃ c ∈ paramsGF.initialCode,
        2 ^ paramsGF.d - 44 - 1 <
          (Finset.univ.filter fun s : Fin (2 ^ paramsGF.d) => badStmtGF.eval x s = c s).card} <
      (1 : ℝ≥0∞) / 10 ^ 8 :=
  round0EscapeGF_johnson_lt badStmtGF badStmtGF_not_mem

example [DecidableEq GF65537_4] :
    (PMF.uniformOfFintype (Fin 3 → GF65537_4)).toOuterMeasure
      {x | ∃ c ∈ paramsGF.initialCode,
        2 ^ paramsGF.d - 44 - 1 <
          (Finset.univ.filter fun s : Fin (2 ^ paramsGF.d) => badStmtGF.eval x s = c s).card} <
      (1 : ℝ≥0∞) / 100 :=
  round0EscapeGF_eta_lt badStmtGF badStmtGF_not_mem

end ExtensionFieldGF65537_4

end CslibFrontierTests.Crypto.FRIBatchSoundness
