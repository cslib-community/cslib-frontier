/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Debate.Machine
import CslibFrontier.Foundations.Analysis.ENNRealNatDiv
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Figure 1 is not sound for a machine with steps that are not oracle queries

The soundness step of `Debate.lean` holds under
[BrownCohenIrvingPiliouras2024, Definition 6.1] for machines whose every step queries an
encoding of the whole transcript so far (`soundness_of_lipschitzAt_run_prefixMachine`). That
reading of the source, and what it costs, are recorded in #7579. This module shows that the
assumption that every step is an oracle query is needed: for a machine with deterministic steps
the protocol of [BrownCohenIrvingPiliouras2024, Figure 1], with its own constants, is not sound
under Definition 6.1, and the soundness step of `Debate.lean` fails when its hypothesis is
replaced by that definition. `TwoBlock.lean` shows separately that the query must determine the
transcript.

The witness is the *copy chain*: the machine that writes `false` and then copies the previous
bit. It makes no oracle query, so it is `K`-Lipschitz at every oracle for every `K`, and it
outputs `false` with probability `1`. A proposer that claims a small positive probability `k / N`
for `true` while the last bit is `false`, and probability `1` afterwards, is never rejected: at a
deterministic step the verifier's sample mean is exact, so an abort is accepted whenever
`k / N` is below the verifier's tolerance, and without an abort each round turns the bit to
`true` with probability `k / N`. Against every challenger the verifier accepts with probability
at least `1 - (1 - k / N) ^ rounds`.

## Reading of the source

* Definition 6.1 is written with a strict inequality, which no machine satisfies if the other
  oracle may equal the given one. Here it is `ProbOracleComp.LipschitzAt`, with `≤`. The output
  law of the copy chain is the same against every oracle (`evalWith_run_copyChain`), so the copy
  chain also satisfies the strict inequality for every `K > 0` against every oracle at positive
  distance.
* The protocol is the interpreter `Debate.run`: claims and coins lie on a grid, and the bit of each
  round is computed by the interpreter, as in the authors' formalization, which the source says uses
  external randomness in place of the two shares (`dedebate.tex`, line 294). The verifier's rule
  after an abort is that of Figure 1, and so is the order of events, with the abort after the bit is
  set. The grid does not weaken the refutation: it only restricts the proposer's claims to grid
  points, and with a uniform coin from the proposer's own side the bit has exactly the claimed
  probability, as with real numbers, so against every challenger the attack carries over to the
  real-valued protocol of Figure 1.
* `Params.figure1` takes the constants of Figure 1 and of the proof of Theorem 6.2, with
  ceilings for the sample counts and the natural logarithm.

## Main definitions

* `Cslib.Interactive.Debate.copyChain`: the machine.
* `Cslib.Interactive.Debate.copyChainProposer`: the proposer that wins against it.

## Main results

* `Cslib.Interactive.Debate.lipschitzAt_run_copyChain`,
  `Cslib.Interactive.Debate.evalWith_run_copyChain`: the copy chain satisfies Definition 6.1 with
  every constant and outputs `false`.
* `Cslib.Interactive.Debate.le_evalWith_run_copyChainProposer`: the acceptance bound against
  every challenger, for any parameters with at least one verifier sample and any claim `k / N`
  that is positive and below the verifier's tolerance.
* `Cslib.Interactive.Debate.not_sound_default_of_lipschitzAt_run`: the soundness step of
  `Debate.lean` fails when its hypothesis is replaced by Definition 6.1.
* `Cslib.Interactive.Debate.not_sound_figure1_of_lipschitzAt_run`: the protocol of Figure 1 with
  the constants of the source is not sound under Definition 6.1.

## References

* [J. Brown-Cohen, G. Irving, G. Piliouras, *Scalable AI safety via doubly-efficient debate*,
  Section 6 and Appendix D][BrownCohenIrvingPiliouras2024]
-/

public section

namespace Cslib.Interactive.Debate

open OracleComp (sumHandler)
open ProbOracleComp (LipschitzAt)
open scoped ENNReal NNReal

variable {Query : Type}

/-! ### The copy chain -/

/-- The copy chain: the machine that writes `false` first and then copies the previous bit. It
never queries its oracle. -/
@[expose] def copyChain : Machine Query where
  step bits := .det (bits.headD false)

private theorem evalWith_transcript_copyChain (O : Query → PMF Bool) :
    ∀ n, OracleComp.evalWith (sumHandler ProbComp.unifOracle O)
      ((copyChain : Machine Query).transcript n) = PMF.pure (List.replicate n false)
  | 0 => rfl
  | n + 1 => by
    have hnext (bits : List Bool) :
        (copyChain : Machine Query).next bits = pure (bits.headD false) := rfl
    simp only [Machine.transcript, OracleComp.evalWith_bind, OracleComp.evalWith_pure, hnext,
      evalWith_transcript_copyChain O n, PMF.pure_bind]
    cases n <;> rfl

/-- The copy chain outputs `false` with probability `1` against every oracle. In particular its
output law does not depend on the oracle. -/
theorem evalWith_run_copyChain (O : Query → PMF Bool) (n : ℕ) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle O) ((copyChain : Machine Query).run n) =
      PMF.pure false := by
  rw [Machine.run, OracleComp.evalWith_map, evalWith_transcript_copyChain, PMF.pure_map]
  cases n <;> rfl

/-- The copy chain satisfies [BrownCohenIrvingPiliouras2024, Definition 6.1] at every oracle with
every constant, since it makes no oracle query. -/
theorem lipschitzAt_run_copyChain (K : ℝ≥0) (O : Query → PMF Bool) (n : ℕ) :
    LipschitzAt K O ((copyChain : Machine Query).run n) := by
  intro O' ε _
  rw [evalWith_run_copyChain, evalWith_run_copyChain]
  exact (Probability.CloseTo.refl _).mono zero_le

/-! ### The attack -/

/-- The proposer that wins against the copy chain: it claims `k / N` while the last bit is
`false` (or no bit is written yet) and claims `N / N` once the last bit is `true`. It has no
state, draws no samples, and its copy returns a uniform coin, as the honest proposer's does. -/
noncomputable def copyChainProposer (P : Params) (k : Fin (P.grid + 1)) : Proposer P.grid where
  State := Unit
  init := ()
  claim history := pure (if history.bits.headD false then Fin.last P.grid else k)
  coin := (honestProposer P).coin

/-- The acceptance bound from any history: certain once the last bit is `true`. -/
private theorem le_evalWith_runFrom_copyChainProposer {law : List Bool → PMF Bool}
    (hlaw : ∀ bits, law bits = PMF.pure (bits.headD false)) (P : Params) [NeZero P.grid]
    (k : Fin (P.grid + 1)) (hk0 : 0 < (k.val : ℝ) / P.grid)
    (hk : (k.val : ℝ) / P.grid < P.verifierTolerance) (hsamples : 0 < P.verifierSamples)
    (B : Challenger P.grid) :
    ∀ n (history : History P.grid) (stateA : (copyChainProposer P k).State) (stateB : B.State),
      (if history.bits.headD false then 1 else 1 - (1 - (k.val : ℝ≥0∞) / P.grid) ^ n) ≤
        OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
          (runFrom P (copyChainProposer P k) B n history stateA stateB) true
  | 0, history, stateA, stateB => by
    rw [runFrom, OracleComp.evalWith_pure, PMF.pure_apply]
    cases history.bits.headD false <;> simp
  | n + 1, history, stateA, stateB => by
    have hN : (P.grid : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne P.grid)
    have hcoin (claim : Fin (P.grid + 1)) :
        OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
          ((copyChainProposer P k).coin history claim) =
            Probability.PMF.uniformOfFintype (ZMod P.grid) :=
      evalWith_uniformCoin law
    have hclaim : OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
        (((copyChainProposer P k).claim history).run stateA) =
          PMF.pure (if history.bits.headD false then Fin.last P.grid else k, stateA) := rfl
    simp only [runFrom, OracleComp.evalWith_bind,
      apply_ite (OracleComp.evalWith (sumHandler ProbComp.unifOracle law)), hclaim, hcoin,
      PMF.pure_bind]
    refine Probability.PMF.le_bind_apply_on_support _ fun coinA _ => ?_
    rw [PMF.bind_apply]
    -- Whatever the challenger does after the round, the verifier accepts at least as often as
    -- the bound for the next history.
    have hinner (claim : Fin (P.grid + 1))
        (htol : |(claim.val : ℝ) / P.grid - (if history.bits.headD false then 1 else 0)| <
          P.verifierTolerance) (coinB : ZMod P.grid) :
        (if coinBit claim coinA coinB then 1
          else 1 - (1 - (k.val : ℝ≥0∞) / P.grid) ^ n) ≤
          ((OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
            ((B.abort history ⟨claim, coinA, coinB⟩).run stateB)).bind fun r =>
              if r.1 = true then
                OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
                  (verdict P history.bits claim)
              else
                OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
                  (runFrom P (copyChainProposer P k) B n (⟨claim, coinA, coinB⟩ :: history)
                    stateA r.2)) true := by
      refine Probability.PMF.le_bind_apply_on_support _ fun r _ => ?_
      by_cases hr : r.1 = true
      · simp only [hr, ↓reduceIte]
        rw [evalWith_verdict_of_pure P hsamples (hlaw _) _ htol, PMF.pure_apply_self]
        split_ifs
        · exact le_rfl
        · exact tsub_le_self
      · simp only [hr]
        exact le_evalWith_runFrom_copyChainProposer hlaw P k hk0 hk hsamples B n
          (⟨claim, coinA, coinB⟩ :: history) stateA r.2
    have hsum (claim : Fin (P.grid + 1))
        (htol : |(claim.val : ℝ) / P.grid - (if history.bits.headD false then 1 else 0)| <
          P.verifierTolerance) :
        ((Probability.PMF.uniformOfFintype (ZMod P.grid)).map
            fun coinB => coinBit claim coinA coinB) false *
            (1 - (1 - (k.val : ℝ≥0∞) / P.grid) ^ n) +
          ((Probability.PMF.uniformOfFintype (ZMod P.grid)).map
            fun coinB => coinBit claim coinA coinB) true ≤
        ∑' coinB, Probability.PMF.uniformOfFintype (ZMod P.grid) coinB *
          ((OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
            ((B.abort history ⟨claim, coinA, coinB⟩).run stateB)).bind fun r =>
              if r.1 = true then
                OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
                  (verdict P history.bits claim)
              else
                OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
                  (runFrom P (copyChainProposer P k) B n (⟨claim, coinA, coinB⟩ :: history)
                    stateA r.2)) true := by
      calc _ = ∑' coinB, Probability.PMF.uniformOfFintype (ZMod P.grid) coinB *
            (if coinBit claim coinA coinB then 1
              else 1 - (1 - (k.val : ℝ≥0∞) / P.grid) ^ n) := by
            rw [← Probability.PMF.tsum_map_mul (Probability.PMF.uniformOfFintype (ZMod P.grid))
              (fun coinB => coinBit claim coinA coinB)
              (fun bit => if bit then 1 else 1 - (1 - (k.val : ℝ≥0∞) / P.grid) ^ n), tsum_bool]
            simp
        _ ≤ _ := tsum_le_tsum fun coinB => mul_le_mul_right (hinner claim htol coinB) _
    rcases Bool.eq_false_or_eq_true (history.bits.headD false) with hhead | hhead
    · -- The last bit is `true`: the claim is the whole grid and the next bit is `true`.
      simp only [hhead, ↓reduceIte] at hsum ⊢
      refine le_trans ?_ (hsum (Fin.last P.grid) (by simpa [hN] using hk0.trans hk))
      rw [map_coinBit_uniformOfFintype_right, Fin.val_last,
        ENNReal.div_self (Nat.cast_ne_zero.2 (NeZero.ne P.grid)) (ENNReal.natCast_ne_top _)]
      exact le_add_self
    · -- The last bit is `false`: the next bit is `true` with probability `k / N`.
      simp only [hhead, Bool.false_eq_true, ↓reduceIte] at hsum ⊢
      refine le_trans ?_ (hsum k (by simpa [abs_of_pos hk0] using hk))
      have htrue := map_coinBit_uniformOfFintype_right k coinA
      rw [map_coinBit_uniformOfFintype_right_false, htrue]
      exact ENNReal.one_sub_pow_succ_le (htrue ▸ PMF.coe_le_one _ true) n

/-- **The attack on a deterministic step.** For any parameters with at least one verifier sample
and any claim `k / N` that is positive and below the verifier's tolerance, `copyChainProposer`
makes the verifier accept on the copy chain with probability at least `1 - (1 - k / N) ^ rounds`,
against every challenger, although the copy chain outputs `false` with probability `1`.

The challenger is an arbitrary program with private state. An abort does not help it: the
verifier's samples of a deterministic step are exact, so it accepts the claim. -/
theorem le_evalWith_run_copyChainProposer (P : Params) (k : Fin (P.grid + 1))
    (hk0 : 0 < (k.val : ℝ) / P.grid) (hk : (k.val : ℝ) / P.grid < P.verifierTolerance)
    (hsamples : 0 < P.verifierSamples) (O : Query → PMF Bool) (B : Challenger P.grid) :
    1 - (1 - (k.val : ℝ≥0∞) / P.grid) ^ P.rounds ≤
      OracleComp.evalWith (sumHandler ProbComp.unifOracle ((copyChain : Machine Query).stepLaw O))
        (run P (copyChainProposer P k) B) true := by
  have hN : P.grid ≠ 0 := by
    intro h
    have hcast : (P.grid : ℝ) = 0 := by exact_mod_cast h
    rw [hcast, div_zero] at hk0
    exact lt_irrefl _ hk0
  have : NeZero P.grid := ⟨hN⟩
  exact le_evalWith_runFrom_copyChainProposer (law := (copyChain : Machine Query).stepLaw O)
    (fun _ => rfl) P k hk0 hk hsamples B P.rounds [] (copyChainProposer P k).init B.init

/-- If each round flips with probability at least `δ₀` and `(1 - δ₀) ^ n₀ < 3 / 5`, then
`n ≥ n₀` rounds give acceptance above `2 / 5`. -/
private theorem two_fifths_lt_one_sub_pow {δ : ℝ≥0∞} {δ₀ : ℝ} {n n₀ : ℕ} (h0 : 0 ≤ δ₀)
    (h1 : δ₀ ≤ 1) (hδ : ENNReal.ofReal δ₀ ≤ δ) (hn : n₀ ≤ n) (hpow : (1 - δ₀) ^ n₀ < 3 / 5) :
    2 / 5 < 1 - (1 - δ) ^ n := by
  have hq : (1 - δ) ^ n ≤ ENNReal.ofReal ((1 - δ₀) ^ n₀) := by
    calc (1 - δ) ^ n ≤ (1 - ENNReal.ofReal δ₀) ^ n := pow_le_pow_left' (tsub_le_tsub_left hδ 1) n
      _ = ENNReal.ofReal ((1 - δ₀) ^ n) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h0, ENNReal.ofReal_pow (by linarith)]
      _ ≤ ENNReal.ofReal ((1 - δ₀) ^ n₀) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one (by linarith) (by linarith) hn)
  have h25 : (2 / 5 : ℝ≥0∞) = ENNReal.ofReal (2 / 5) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  calc (2 / 5 : ℝ≥0∞) = ENNReal.ofReal (2 / 5) := h25
    _ < ENNReal.ofReal (1 - (1 - δ₀) ^ n₀) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    _ = 1 - ENNReal.ofReal ((1 - δ₀) ^ n₀) := by
      rw [ENNReal.ofReal_sub _ (pow_nonneg (by linarith) _), ENNReal.ofReal_one]
    _ ≤ 1 - (1 - δ) ^ n := tsub_le_tsub_left hq 1

/-- The attack wins with probability above `2 / 5` once the claim is at least `δ₀` and there
are at least `n₀` rounds with `(1 - δ₀) ^ n₀ < 3 / 5`. -/
private theorem exists_proposer_two_fifths_lt (P : Params) (O : Query → PMF Bool) (k : ℕ)
    (hkN : k ≤ P.grid) (hk0 : 0 < k) (hk : (k : ℝ) / P.grid < P.verifierTolerance)
    (hsamples : 0 < P.verifierSamples) {δ₀ : ℝ} {n₀ : ℕ} (h0 : 0 ≤ δ₀) (h1 : δ₀ ≤ 1)
    (hδ : δ₀ ≤ (k : ℝ) / P.grid) (hn : n₀ ≤ P.rounds) (hpow : (1 - δ₀) ^ n₀ < 3 / 5) :
    ∃ A : Proposer P.grid, ∀ B : Challenger P.grid,
      2 / 5 < OracleComp.evalWith
        (sumHandler ProbComp.unifOracle ((copyChain : Machine Query).stepLaw O))
        (run P A B) true := by
  have hN : 0 < P.grid := hk0.trans_le hkN
  refine ⟨copyChainProposer P ⟨k, Nat.lt_succ_of_le hkN⟩, fun B => ?_⟩
  refine lt_of_lt_of_le (two_fifths_lt_one_sub_pow h0 h1 ?_ hn hpow)
    (le_evalWith_run_copyChainProposer P ⟨k, Nat.lt_succ_of_le hkN⟩
      (div_pos (by exact_mod_cast hk0) (by exact_mod_cast hN)) hk hsamples O B)
  rw [← ENNReal.ofReal_div_natCast k P.grid hN]
  exact ENNReal.ofReal_le_ofReal hδ

/-! ### The archived constants -/

/-- **The soundness step needs its stronger hypothesis.** `soundness_of_lipschitzAt_stepLaw`
fails when its hypothesis, Lipschitz in the whole step law, is replaced by
[BrownCohenIrvingPiliouras2024, Definition 6.1]: for `K = 1` and `T ≥ 51`, the copy chain of
`T + 1` steps is `1`-Lipschitz at every external oracle and outputs `true` with probability `0`,
yet some proposer makes the verifier accept with probability above `2 / 5` against every
challenger, at the parameters `Params.default 1 T`.

Definition 6.1 is read with `≤`, as `ProbOracleComp.LipschitzAt`; the protocol is `Debate.run`,
on a grid and with the bit computed by the interpreter. -/
theorem not_sound_default_of_lipschitzAt_run (T : ℕ) (hT : 51 ≤ T) (O : Query → PMF Bool) :
    LipschitzAt 1 O ((copyChain : Machine Query).run (T + 1)) ∧
      OracleComp.evalWith (sumHandler ProbComp.unifOracle O)
        ((copyChain : Machine Query).run (T + 1)) true ≤ 1 / 3 ∧
      ∃ A : Proposer (Params.default 1 T).grid, ∀ B : Challenger (Params.default 1 T).grid,
        2 / 5 < OracleComp.evalWith
          (sumHandler ProbComp.unifOracle ((copyChain : Machine Query).stepLaw O))
          (run (Params.default 1 T) A B) true := by
  refine ⟨lipschitzAt_run_copyChain 1 O (T + 1), by simp [evalWith_run_copyChain], ?_⟩
  have hT' : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  -- The grid is large.
  have hgrid : (5000 : ℝ) ≤ ((Params.default 1 T).grid : ℝ) := by
    have hfail : (1 : ℝ) / (100 * (T + 1)) / 2 ≤ 1 / 200 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hexp : (1 : ℝ) / 200 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, one_div, inv_le_inv₀ (by norm_num) (Real.exp_pos 1)]
      linarith [Real.exp_one_lt_d9]
    have hlog : Real.log (1 / (100 * (T + 1)) / 2) ≤ -1 :=
      (Real.log_le_iff_le_exp (by positivity)).2 (hfail.trans hexp)
    calc (5000 : ℝ)
        ≤ -Real.log (1 / (100 * (T + 1)) / 2) / (2 * (1 / (100 * ((1 : ℝ≥0) : ℝ))) ^ 2) := by
          rw [NNReal.coe_one, mul_one, le_div_iff₀ (by norm_num)]
          linarith
      _ ≤ _ := Nat.le_ceil _
  have hgridN : 5000 ≤ (Params.default 1 T).grid := by exact_mod_cast hgrid
  have hR : (0 : ℝ) < ((Params.default 1 T).grid : ℝ) := by linarith
  have htol : (Params.default 1 T).verifierTolerance = 3 / 200 := by
    change 3 / (200 * ((1 : ℝ≥0) : ℝ)) = 3 / 200
    rw [NNReal.coe_one, mul_one]
  -- The claim `⌊N / 100⌋ / N` lies in `[49 / 5000, 1 / 100]`.
  have hk1 : 100 * ((Params.default 1 T).grid / 100) ≤ (Params.default 1 T).grid := by omega
  have hk2 : (Params.default 1 T).grid < 100 * ((Params.default 1 T).grid / 100) + 100 := by
    omega
  have hk1' : 100 * (((Params.default 1 T).grid / 100 : ℕ) : ℝ) ≤
      ((Params.default 1 T).grid : ℝ) := by exact_mod_cast hk1
  have hk2' : ((Params.default 1 T).grid : ℝ) <
      100 * (((Params.default 1 T).grid / 100 : ℕ) : ℝ) + 100 := by exact_mod_cast hk2
  refine exists_proposer_two_fifths_lt (Params.default 1 T) O
    ((Params.default 1 T).grid / 100) (by omega) (by omega) ?_
    (Params.default_pos one_pos T).2.2.1 (δ₀ := 49 / 5000) (n₀ := 52) (by norm_num)
    (by norm_num) ?_ (show 52 ≤ T + 1 by omega) (by norm_num)
  · rw [htol, div_lt_div_iff₀ hR (by norm_num)]
    linarith
  · rw [div_le_div_iff₀ (by norm_num) hR]
    linarith

/-! ### The constants of the source -/

/-- `(600 / 601) ^ 307 < 3 / 5`, while `(600 / 601) ^ 306 > 3 / 5`: the threshold `307`. The
exponent is split because `norm_num` does not evaluate powers above `256`. -/
private theorem pow_307_lt : ((600 : ℝ) / 601) ^ 307 < 3 / 5 := by
  have hsplit : ((600 : ℝ) / 601) ^ 307 = (600 / 601) ^ 200 * (600 / 601) ^ 107 := by
    rw [← pow_add]
  rw [hsplit]
  norm_num

/-- **The protocol of Figure 1 is not sound under Definition 6.1.** With the constants of
[BrownCohenIrvingPiliouras2024, Figure 1] for `K = 1` (`Params.figure1 1 T`) and `T ≥ 307`, the
copy chain of `T` steps is `1`-Lipschitz at every external oracle in the sense of Definition 6.1
and outputs `true` with probability `0`, yet some proposer makes the verifier accept with
probability above `2 / 5` against every challenger, where the protocol the source gives for
[BrownCohenIrvingPiliouras2024, Theorem 6.2] (Figure 1, analysed in Appendix D) claims soundness
`2 / 5`. The theorem's existence claim is not refuted: another protocol may meet it.

Definition 6.1 is read with `≤`, as `ProbOracleComp.LipschitzAt`; the copy chain also satisfies
the strict reading against every oracle at positive distance, since its output law does not
depend on the oracle. The protocol is `Debate.run`: claims and coins lie on a grid and the
interpreter computes the bit of each round, while the verifier's rule after an abort is that of
Figure 1. The grid does not weaken the refutation: it only restricts the proposer's claims to
grid points, and with a uniform coin from the proposer's own side the bit has exactly the
claimed probability, as with real numbers, so against every challenger the attack carries over
to the real-valued protocol of Figure 1. The sample counts are rounded up and the logarithm is
natural (`Params.figure1`). -/
theorem not_sound_figure1_of_lipschitzAt_run (T : ℕ) (hT : 307 ≤ T) (O : Query → PMF Bool) :
    LipschitzAt 1 O ((copyChain : Machine Query).run T) ∧
      OracleComp.evalWith (sumHandler ProbComp.unifOracle O)
        ((copyChain : Machine Query).run T) true ≤ 1 / 3 ∧
      ∃ A : Proposer (Params.figure1 1 T).grid, ∀ B : Challenger (Params.figure1 1 T).grid,
        2 / 5 < OracleComp.evalWith
          (sumHandler ProbComp.unifOracle ((copyChain : Machine Query).stepLaw O))
          (run (Params.figure1 1 T) A B) true := by
  refine ⟨lipschitzAt_run_copyChain 1 O T, by simp [evalWith_run_copyChain], ?_⟩
  have hT' : (307 : ℝ) ≤ T := by exact_mod_cast hT
  have hd : ⌈150 * ((1 : ℝ≥0) : ℝ)⌉₊ = 150 := by
    rw [NNReal.coe_one, mul_one]
    exact Nat.ceil_natCast 150
  -- The grid is large.
  have hgrid : (4320000 : ℝ) ≤ ((Params.figure1 1 T).grid : ℝ) := by
    have hlog : (1 : ℝ) ≤ Real.log (100 * T) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith [Real.exp_one_lt_d9]
    calc (4320000 : ℝ) ≤ 192 * ((⌈150 * ((1 : ℝ≥0) : ℝ)⌉₊ : ℕ) : ℝ) ^ 2 * Real.log (100 * T) := by
          rw [hd]
          push_cast
          nlinarith
      _ ≤ _ := Nat.le_ceil _
  have hgridN : 4320000 ≤ (Params.figure1 1 T).grid := by exact_mod_cast hgrid
  have hsamples : 0 < (Params.figure1 1 T).verifierSamples := by
    refine Nat.ceil_pos.2 ?_
    rw [hd]
    have : (0 : ℝ) < Real.log 100 := Real.log_pos (by norm_num)
    positivity
  have htol : (Params.figure1 1 T).verifierTolerance = 1 / 600 := by
    change 1 / (4 * ((⌈150 * ((1 : ℝ≥0) : ℝ)⌉₊ : ℕ) : ℝ)) = 1 / 600
    rw [hd]
    norm_num
  -- The claim `⌈R / 601⌉ / R` lies in `[1 / 601, 1 / 600)`.
  have hR : (0 : ℝ) < ((Params.figure1 1 T).grid : ℝ) := by linarith
  have hk1 : (Params.figure1 1 T).grid ≤ 601 * (((Params.figure1 1 T).grid + 600) / 601) := by
    omega
  have hk2 : 600 * (((Params.figure1 1 T).grid + 600) / 601) < (Params.figure1 1 T).grid := by
    omega
  have hk1' : ((Params.figure1 1 T).grid : ℝ) ≤
      601 * ((((Params.figure1 1 T).grid + 600) / 601 : ℕ) : ℝ) := by exact_mod_cast hk1
  have hk2' : 600 * ((((Params.figure1 1 T).grid + 600) / 601 : ℕ) : ℝ) <
      ((Params.figure1 1 T).grid : ℝ) := by exact_mod_cast hk2
  refine exists_proposer_two_fifths_lt (Params.figure1 1 T) O
    (((Params.figure1 1 T).grid + 600) / 601) (by omega) (by omega) ?_ hsamples
    (δ₀ := 1 / 601) (n₀ := 307) (by norm_num) (by norm_num) ?_ hT
    (by rw [show (1 : ℝ) - 1 / 601 = 600 / 601 by norm_num]; exact pow_307_lt)
  · rw [htol, div_lt_div_iff₀ hR (by norm_num)]
    linarith
  · rw [div_le_div_iff₀ (by norm_num) hR]
    linarith

end Cslib.Interactive.Debate
