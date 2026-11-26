/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.ZMod.Defs
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Coin
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.StatisticalDistance.ClosedForm
import CslibFrontier.Probability.StatisticalDistance.TotalVariation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Debate with a stochastic oracle: the cross-examination protocol

Two provers debate the output of a randomized computation in front of a verifier who samples
only one step of it. The computation is a *step law* `law : List Bool → PMF Bool`: given the
bits written so far, most recent first, the law of the next bit. Its transcript and output are
the oracle programs `Debate.transcript` and `Debate.output`, which query each prefix in turn.

`Debate.run` interprets the protocol of [BrownCohenIrvingPiliouras2024, Figure 1]. In each
round the proposer claims a probability for the next bit; the interpreter asks an independent
copy of each player for a coin, adds the two coins and sets the bit from the claim and the sum; the
challenger may then abort. On an abort the verifier samples the disputed step itself and accepts
exactly when the claim is close to its sample mean. Without an abort the verifier outputs the
last bit. Each player is a program with private state, private coins and sample access to the
step law; a player sees the public history and its own state, never the other player's.

The two theorems are steps toward [BrownCohenIrvingPiliouras2024, Theorem 6.2], not that
theorem. Completeness needs no Lipschitz hypothesis. Soundness assumes that the output is
Lipschitz in the whole step law (`ProbOracleComp.LipschitzAt K law (Debate.output (T + 1))`),
which is stronger than Definition 6.1 of the source; the reason for the stronger hypothesis is
recorded in cslib-frontier issue #7579. Neither theorem makes a claim about running time, about
the number of oracle queries of any party, or about machines given by an encoding.

## Deviations from the source

* The computation is a step law indexed by the whole transcript prefix, as in the Lean
  development accompanying the source (google-deepmind/debate, `Oracle`), in place of a machine
  whose steps read relevant coordinates and query an external oracle.
* Claims and coins lie on a grid: a claim is `k : Fin (N + 1)`, read as the probability `k / N`,
  and a coin is an element of `ZMod N`, in place of real numbers in `[0, 1]`. When either coin is
  uniform, the bit is `true` with probability exactly `k / N`
  (`Debate.map_coinBit_uniformOfFintype_left`, `Debate.map_coinBit_uniformOfFintype_right`).
* The interpreter queries the independent copies and computes the bit; a player never announces
  the bit.
* The sample counts and thresholds (`Debate.Params.default`) are those of the Lean development
  accompanying the source (`Params.defaults`), not those of Figure 1.

## Main definitions

* `Cslib.Interactive.Debate.transcript`, `Cslib.Interactive.Debate.output`: the computation
  under debate, as oracle programs over transcript prefixes.
* `Cslib.Interactive.Debate.Proposer`, `Cslib.Interactive.Debate.Challenger`: the two players.
* `Cslib.Interactive.Debate.run`: the protocol.
* `Cslib.Interactive.Debate.honestProposer`, `Cslib.Interactive.Debate.honestChallenger`: the
  prescribed strategies.

## Main results

* `Cslib.Interactive.Debate.completeness_stepLaw`: the honest proposer wins with probability at
  least `3 / 5` against every challenger when the output is `true` with probability at least
  `2 / 3`.
* `Cslib.Interactive.Debate.soundness_of_lipschitzAt_stepLaw`: against the honest challenger
  every proposer wins with probability at most `2 / 5` when the output is `true` with probability
  at most `1 / 3`.

## References

* [J. Brown-Cohen, G. Irving, G. Piliouras, *Scalable AI safety via doubly-efficient debate*,
  Section 6 and Appendix D][BrownCohenIrvingPiliouras2024]
-/

public section

namespace Cslib.Interactive.Debate

open OracleComp (sumHandler)
open ProbOracleComp (LipschitzAt)
open scoped ENNReal NNReal

/-! ### The computation under debate -/

/-- The oracle interface of a step law: a query is the list of bits written so far, most recent
first, and the reply is the next bit. -/
abbrev StepSpec : List Bool → Type := fun _ => Bool

/-- The transcript of the first `n` steps, most recent bit first: each step queries the bits
written before it. -/
@[expose] def transcript : ℕ → ProbOracleComp StepSpec (List Bool)
  | 0 => pure []
  | n + 1 => do
    let bits ← transcript n
    let bit ← ProbOracleComp.query (spec := StepSpec) bits
    pure (bit :: bits)

/-- The output of an `n`-step computation: the last bit of its transcript (`false` when
`n = 0`). -/
@[expose] def output (n : ℕ) : ProbOracleComp StepSpec Bool :=
  (fun bits => bits.headD false) <$> transcript n

/-- The number of `true` replies among `n` independent samples of the step after `bits`. -/
private def countTrue (bits : List Bool) : (n : ℕ) → ProbOracleComp StepSpec (Fin (n + 1))
  | 0 => pure 0
  | n + 1 => do
    let count ← countTrue bits n
    let bit ← ProbOracleComp.query (spec := StepSpec) bits
    pure (if bit then count.succ else count.castSucc)

/-! ### Rounds and players -/

/-- The bit of a round: `true` exactly when the sum of the two coins, as a number below `N`, is
below the claim `k`. If either coin is uniform on `ZMod N` and `N ≠ 0`, the bit is `true` with
probability `k / N`. -/
def coinBit {N : ℕ} (claim : Fin (N + 1)) (coinA coinB : ZMod N) : Bool :=
  decide ((coinA + coinB).val < claim.val)

/-- The public record of one round on the grid `N`. -/
structure Round (N : ℕ) where
  /-- The proposer's claim `k`, read as the probability `k / N` that the next bit is `true`. -/
  claim : Fin (N + 1)
  /-- The coin obtained from the independent copy of the challenger. -/
  coinA : ZMod N
  /-- The coin obtained from the independent copy of the proposer. -/
  coinB : ZMod N

/-- The bit written in a round. -/
def Round.bit {N : ℕ} (round : Round N) : Bool :=
  coinBit round.claim round.coinA round.coinB

/-- The public history of a debate: its completed rounds, most recent first. -/
abbrev History (N : ℕ) := List (Round N)

/-- The bits written so far, most recent first. -/
def History.bits {N : ℕ} (history : History N) : List Bool :=
  history.map Round.bit

/-- A proposer on the grid `N`: the player claiming that the output is `true`. It keeps a
private state, draws private coins and samples steps of the computation at will. -/
structure Proposer (N : ℕ) where
  /-- The private state carried between rounds. -/
  State : Type
  /-- The initial private state. -/
  init : State
  /-- The claim for the next bit, from the public history and the private state. -/
  claim : History N → StateT State (ProbOracleComp StepSpec) (Fin (N + 1))
  /-- The independent copy asked for a coin. It sees the public history and the current claim,
  and shares no state with the proposer. -/
  coin : History N → Fin (N + 1) → ProbOracleComp StepSpec (ZMod N)

/-- A challenger on the grid `N`: the player disputing that the output is `true`. It keeps a
private state, draws private coins and samples steps of the computation at will. -/
structure Challenger (N : ℕ) where
  /-- The private state carried between rounds. -/
  State : Type
  /-- The initial private state. -/
  init : State
  /-- Whether to abort after a round, from the public history before the round, the round and
  the private state. -/
  abort : History N → Round N → StateT State (ProbOracleComp StepSpec) Bool
  /-- The independent copy asked for a coin. It sees the public history and the current claim,
  and shares no state with the challenger. -/
  coin : History N → Fin (N + 1) → ProbOracleComp StepSpec (ZMod N)

/-! ### The protocol -/

/-- The parameters of the protocol and of its prescribed strategies. -/
structure Params where
  /-- The number of rounds, which is the number of steps of the computation. -/
  rounds : ℕ
  /-- The grid size `N`: claims are multiples of `1 / N`, and the honest proposer draws `N`
  samples for each claim. -/
  grid : ℕ
  /-- The number of samples the honest challenger draws in each round. -/
  challengerSamples : ℕ
  /-- The honest challenger aborts when the claim and its sample mean differ by at least this
  much. -/
  challengerTolerance : ℝ
  /-- The number of samples the verifier draws after an abort. -/
  verifierSamples : ℕ
  /-- The verifier accepts after an abort when the claim and its sample mean differ by less than
  this much. -/
  verifierTolerance : ℝ

/-- The verifier's decision after an abort in the round after `bits` with claim `claim`: draw
`P.verifierSamples` samples of the disputed step and accept exactly when the claim is within
`P.verifierTolerance` of their mean. -/
private noncomputable def verdict (P : Params) (bits : List Bool) (claim : Fin (P.grid + 1)) :
    ProbOracleComp StepSpec Bool := do
  let count ← countTrue bits P.verifierSamples
  pure (decide (|(claim : ℝ) / P.grid - (count : ℝ) / P.verifierSamples| < P.verifierTolerance))

/-- The remaining `rounds` rounds of a debate from the public history `history` and the two
private states. -/
private noncomputable def runFrom (P : Params) (A : Proposer P.grid) (B : Challenger P.grid) :
    ℕ → History P.grid → A.State → B.State → ProbOracleComp StepSpec Bool
  | 0, history, _, _ => pure (history.bits.headD false)
  | rounds + 1, history, stateA, stateB => do
    let (claim, stateA) ← (A.claim history).run stateA
    let coinA ← B.coin history claim
    let coinB ← A.coin history claim
    let round : Round P.grid := ⟨claim, coinA, coinB⟩
    let (stop, stateB) ← (B.abort history round).run stateB
    if stop then verdict P history.bits claim
    else runFrom P A B rounds (round :: history) stateA stateB

/-- The debate protocol of [BrownCohenIrvingPiliouras2024, Figure 1] between the proposer `A`
and the challenger `B`; the result is `true` when the verifier accepts.

In each round the proposer claims a probability for the next bit, the interpreter obtains one
coin from an independent copy of each player and sets the bit by `coinBit`, and the challenger
may abort. After an abort the verifier draws `P.verifierSamples` samples of the disputed step
and accepts exactly when the claim is within `P.verifierTolerance` of their mean; after
`P.rounds` rounds without an abort it outputs the last bit. Every private sample of either
player, of either copy and of the verifier is a fresh draw. -/
noncomputable def run (P : Params) (A : Proposer P.grid) (B : Challenger P.grid) :
    ProbOracleComp StepSpec Bool :=
  runFrom P A B P.rounds [] A.init B.init

/-! ### The prescribed strategies -/

/-- A uniform coin on `ZMod N` (the coin `0` in the degenerate case `N = 0`). -/
private noncomputable def uniformCoin (N : ℕ) : ProbOracleComp StepSpec (ZMod N) :=
  if h : N = 0 then pure 0
  else
    haveI : NeZero N := ⟨h⟩
    ProbOracleComp.sample (ProbComp.uniform (ZMod N))

/-- The honest proposer: in each round it draws `P.grid` fresh samples of the next step and
claims the fraction that are `true`; its copy returns a uniform coin. -/
noncomputable def honestProposer (P : Params) : Proposer P.grid where
  State := Unit
  init := ()
  claim history := StateT.lift (countTrue history.bits P.grid)
  coin _ _ := uniformCoin P.grid

/-- The honest challenger: in each round it draws `P.challengerSamples` fresh samples of the
step just taken and aborts when the claim differs from the fraction that are `true` by at least
`P.challengerTolerance`; its copy returns a uniform coin. -/
noncomputable def honestChallenger (P : Params) : Challenger P.grid where
  State := Unit
  init := ()
  abort history round := StateT.lift do
    let count ← countTrue history.bits P.challengerSamples
    pure (decide (P.challengerTolerance ≤
      |(round.claim : ℝ) / P.grid - (count : ℝ) / P.challengerSamples|))
  coin _ _ := uniformCoin P.grid

/-- The number of samples after which a sample mean of a `Bool`-valued step is within `error` of
its probability except with probability at most `failure` (Hoeffding's inequality). -/
private noncomputable def sampleCount (error failure : ℝ) : ℕ :=
  ⌈-Real.log (failure / 2) / (2 * error ^ 2)⌉₊

/-- The parameters for a `(T + 1)`-step computation with Lipschitz constant `K`, following
`Params.defaults` of the Lean development accompanying the source. An estimate with error `e`
and failure probability `f` uses `⌈-log (f / 2) / (2 e ^ 2)⌉` samples. With `c = 1 / (100 K)`,
`s = 2 / (100 K)` and `b = 5 / (100 K)`: the honest proposer's claim is within `c` of the truth
except with probability `1 / (100 (T + 1))`; the honest challenger, with the same failure
probability, does not abort a claim within `s` and aborts a claim off by `b`; the verifier
accepts a claim within `c` and rejects a claim off by `s`, each except with probability
`1 / 100`. -/
noncomputable def Params.default (K : ℝ≥0) (T : ℕ) : Params where
  rounds := T + 1
  grid := sampleCount (1 / (100 * K)) (1 / (100 * (T + 1)))
  challengerSamples := sampleCount (3 / (200 * K)) (1 / (100 * (T + 1)))
  challengerTolerance := 7 / (200 * K)
  verifierSamples := sampleCount (1 / (200 * K)) (1 / 100)
  verifierTolerance := 3 / (200 * K)

/-! ### Evaluation against a step law -/

section Proofs

open Probability

/-- The law of a program against the step law `law`, with fresh private coins. -/
private noncomputable def ev (law : List Bool → PMF Bool) {α : Type}
    (program : ProbOracleComp StepSpec α) : PMF α :=
  OracleComp.evalWith (sumHandler ProbComp.unifOracle law) program

private theorem ev_pure (law : List Bool → PMF Bool) {α : Type} (a : α) :
    ev law (pure a) = PMF.pure a := rfl

private theorem ev_bind (law : List Bool → PMF Bool) {α β : Type}
    (program : ProbOracleComp StepSpec α) (next : α → ProbOracleComp StepSpec β) :
    ev law (program >>= next) = (ev law program).bind fun a => ev law (next a) :=
  OracleComp.evalWith_bind _ _ _

private theorem ev_map (law : List Bool → PMF Bool) {α β : Type} (f : α → β)
    (program : ProbOracleComp StepSpec α) : ev law (f <$> program) = (ev law program).map f :=
  OracleComp.evalWith_map _ _ _

private theorem ev_query (law : List Bool → PMF Bool) (bits : List Bool) :
    ev law (ProbOracleComp.query (spec := StepSpec) bits) = law bits :=
  OracleComp.evalWith_query _ _

/-- The law of the honest coin on a nonzero grid is uniform. -/
private theorem ev_uniformCoin {N : ℕ} [NeZero N] (law : List Bool → PMF Bool) :
    ev law (uniformCoin N) = PMF.uniformOfFintype (ZMod N) := by
  rw [ev]
  simp only [uniformCoin, NeZero.ne N, ↓reduceDIte]
  rw [OracleComp.evalWith_eq_interpret, ProbOracleComp.interpret_sample,
    ← OracleComp.evalWith_eq_interpret]
  exact ProbComp.eval_uniform (ZMod N)

/-! ### Sample counts -/

/-- The law of the number of `true` among `n` independent draws of `ν`. -/
private noncomputable def countLaw (ν : PMF Bool) : (n : ℕ) → PMF (Fin (n + 1))
  | 0 => PMF.pure 0
  | n + 1 => (countLaw ν n).bind fun count => ν.bind fun bit =>
      PMF.pure (if bit then count.succ else count.castSucc)

private theorem ev_countTrue (law : List Bool → PMF Bool) (bits : List Bool) :
    ∀ n, ev law (countTrue bits n) = countLaw (law bits) n
  | 0 => rfl
  | n + 1 => by
    simp only [countTrue, countLaw, ev_bind, ev_pure, ev_query, ev_countTrue law bits n]

private theorem countLaw_succ_tsum (ν : PMF Bool) (n : ℕ) (F : Fin (n + 2) → ℝ≥0∞) :
    ∑' k, countLaw ν (n + 1) k * F k =
      ∑' c, countLaw ν n c * (ν true * F c.succ + ν false * F c.castSucc) := by
  rw [countLaw, PMF.tsum_bind_mul]
  refine tsum_congr fun c => congrArg (countLaw ν n c * ·) ?_
  change ∑' k, (ν.map fun bit => if bit then c.succ else c.castSucc) k * F k = _
  rw [PMF.tsum_map_mul, tsum_bool, add_comm (ν false * _)]
  simp only [ite_true, Bool.false_eq_true, ite_false]

/-- The expected number of `true` samples. -/
private theorem countLaw_mean_true (ν : PMF Bool) :
    ∀ n, ∑' k, countLaw ν n k * (k.val : ℝ≥0∞) = n * ν true
  | 0 => by simp [countLaw]
  | n + 1 => by
    have hstep (c : Fin (n + 1)) :
        ν true * ((c.succ.val : ℕ) : ℝ≥0∞) + ν false * ((c.castSucc.val : ℕ) : ℝ≥0∞) =
          (c.val : ℝ≥0∞) + ν true := by
      rw [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      calc ν true * ((c.val : ℝ≥0∞) + 1) + ν false * (c.val : ℝ≥0∞)
          = (ν true + ν false) * (c.val : ℝ≥0∞) + ν true := by ring
        _ = (c.val : ℝ≥0∞) + ν true := by rw [PMF.apply_true_add_apply_false, one_mul]
    rw [countLaw_succ_tsum]
    simp only [hstep, mul_add]
    rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, countLaw_mean_true ν n,
      Nat.cast_add, Nat.cast_one]
    ring

/-- The expected number of `false` samples. -/
private theorem countLaw_mean_false (ν : PMF Bool) :
    ∀ n, ∑' k, countLaw ν n k * ((n - k.val : ℕ) : ℝ≥0∞) = n * ν false
  | 0 => by simp [countLaw]
  | n + 1 => by
    have hstep (c : Fin (n + 1)) :
        ν true * ((n + 1 - c.succ.val : ℕ) : ℝ≥0∞) +
            ν false * ((n + 1 - c.castSucc.val : ℕ) : ℝ≥0∞) =
          ((n - c.val : ℕ) : ℝ≥0∞) + ν false := by
      rw [Fin.val_succ, Fin.val_castSucc, Nat.add_sub_add_right, Nat.succ_sub c.is_le,
        Nat.cast_succ]
      calc ν true * ((n - c.val : ℕ) : ℝ≥0∞) + ν false * (((n - c.val : ℕ) : ℝ≥0∞) + 1)
          = (ν true + ν false) * ((n - c.val : ℕ) : ℝ≥0∞) + ν false := by ring
        _ = ((n - c.val : ℕ) : ℝ≥0∞) + ν false := by rw [PMF.apply_true_add_apply_false, one_mul]
    rw [countLaw_succ_tsum]
    simp only [hstep, mul_add]
    rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, countLaw_mean_false ν n,
      Nat.cast_add, Nat.cast_one]
    ring

/-- The number of `true` coordinates of a tuple of bits. -/
private def trueCount {n : ℕ} (v : Fin n → Bool) : ℕ := ∑ i, (v i).toNat

private theorem trueCount_cons {n : ℕ} (a : Bool) (v : Fin n → Bool) :
    trueCount (Fin.cons a v : Fin (n + 1) → Bool) = trueCount v + a.toNat := by
  simp [trueCount, Fin.sum_univ_succ, add_comm]

/-- The sample count is the number of `true` among independent draws. -/
private theorem map_val_countLaw (ν : PMF Bool) :
    ∀ n, (countLaw ν n).map Fin.val = (PMF.iid ν n).map trueCount
  | 0 => by
    simp [countLaw, PMF.iid, trueCount, PMF.pure_map]
  | n + 1 => by
    have hval (c : Fin (n + 1)) (b : Bool) :
        ((if b then c.succ else c.castSucc : Fin (n + 2)) : ℕ) = c.val + b.toNat := by
      cases b <;> simp
    rw [countLaw, PMF.iid]
    simp only [PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_map, hval, PMF.map_comp]
    erw [← PMF.bind_map _ Fin.val fun m => ν.bind fun b => PMF.pure (m + b.toNat)]
    rw [map_val_countLaw ν n, PMF.bind_map]
    simp only [Function.comp_def, PMF.map, trueCount_cons]
    rw [PMF.bind_comm]

/-- **Hoeffding's inequality for the sample count.** -/
private theorem countLaw_tail (ν : PMF Bool) {n : ℕ} (hn : 0 < n) {e : ℝ} (he : 0 ≤ e) :
    ((countLaw ν n).toOuterMeasure {k | e ≤ |(k.val : ℝ) / n - (ν true).toReal|}).toReal ≤
      2 * Real.exp (-2 * n * e ^ 2) := by
  have hset : {k : Fin (n + 1) | e ≤ |(k.val : ℝ) / n - (ν true).toReal|} =
      Fin.val ⁻¹' {m : ℕ | e ≤ |(m : ℝ) / n - (ν true).toReal|} := rfl
  rw [hset, ← PMF.toOuterMeasure_map_apply, map_val_countLaw, PMF.toOuterMeasure_map_apply,
    PMF.iid_eq_pi]
  have h := PMF.pi_sum_abs_sub_mean_ge_card_mul (fun _ : Fin n => ν)
    (fun _ a => if a then (1 : ℝ) else 0) (fun _ a _ => by cases a <;> simp) he
  rw [Fintype.card_fin] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsets : trueCount ⁻¹' {m : ℕ | e ≤ |(m : ℝ) / n - (ν true).toReal|} =
      {outcome : Fin n → Bool | n * e ≤
        |(∑ i, if outcome i = true then (1 : ℝ) else 0) -
          ∑ _i : Fin n, ∑ a, (ν a).toReal * if a = true then (1 : ℝ) else 0|} := by
    ext v
    have hsum : (∑ i : Fin n, if v i = true then (1 : ℝ) else 0) = (trueCount v : ℝ) := by
      rw [trueCount, Nat.cast_sum]
      exact Finset.sum_congr rfl fun i _ => by cases v i <;> simp
    have hmean : (∑ _i : Fin n, ∑ a, (ν a).toReal * if a = true then (1 : ℝ) else 0) =
        n * (ν true).toReal := by simp
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hsum, hmean]
    rw [show (trueCount v : ℝ) / n - (ν true).toReal =
        ((trueCount v : ℝ) - n * (ν true).toReal) / n by field_simp,
      abs_div, abs_of_pos hn', le_div_iff₀ hn', mul_comm]
  rwa [hsets]

private theorem sampleCount_pos {e f : ℝ} (he : 0 < e) (hf0 : 0 < f) (hf : f < 2) :
    0 < sampleCount e f := by
  rw [sampleCount, Nat.ceil_pos]
  have hlog : Real.log (f / 2) < 0 := Real.log_neg (by positivity) (by linarith)
  exact div_pos (by linarith) (by positivity)

private theorem two_mul_exp_sampleCount_le {e f : ℝ} (he : 0 < e) (hf0 : 0 < f) :
    2 * Real.exp (-2 * sampleCount e f * e ^ 2) ≤ f := by
  have hpos : 0 < 2 * e ^ 2 := by positivity
  have hceil : -Real.log (f / 2) / (2 * e ^ 2) ≤ sampleCount e f := Nat.le_ceil _
  rw [div_le_iff₀ hpos] at hceil
  have hexp : Real.exp (-2 * sampleCount e f * e ^ 2) ≤ f / 2 := by
    rw [← Real.exp_log (show (0 : ℝ) < f / 2 by positivity)]
    exact Real.exp_le_exp.2 (by nlinarith)
  linarith

/-- With `sampleCount e f` samples the sample mean is off by `e` or more with probability at
most `f`. -/
private theorem countLaw_sampleCount_tail (ν : PMF Bool) {e f : ℝ} (he : 0 < e) (hf0 : 0 < f)
    (hf : f < 2) :
    (countLaw ν (sampleCount e f)).toOuterMeasure
        {k | e ≤ |(k.val : ℝ) / sampleCount e f - (ν true).toReal|} ≤ ENNReal.ofReal f := by
  rw [ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _) hf0.le]
  exact (countLaw_tail ν (sampleCount_pos he hf0 hf) he.le).trans
    (two_mul_exp_sampleCount_le he hf0)

/-! ### The coin step -/

/-- Exactly `k` elements of `ZMod N` have value below `k ≤ N`. -/
private theorem card_filter_val_lt {N : ℕ} [NeZero N] (k : Fin (N + 1)) :
    (Finset.univ.filter fun u : ZMod N => u.val < k.val).card = k.val := by
  cases N with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ n =>
    have h := Fin.card_filter_val_lt (n := n + 1) (m := k.val)
    rwa [Nat.min_eq_right (Nat.lt_succ_iff.1 k.isLt)] at h

private theorem map_decide_val_lt_uniform {N : ℕ} [NeZero N] (k : Fin (N + 1))
    (e : ZMod N ≃ ZMod N) (f : ZMod N → Bool) (hf : ∀ w, f w = decide ((e w).val < k.val)) :
    (PMF.uniformOfFintype (ZMod N)).map f true = (k.val : ℝ≥0∞) / N := by
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, hf, eq_comm (a := true), decide_eq_true_eq]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ZMod.card, div_eq_mul_inv]
  congr 2
  exact (Finset.card_equiv e (by simp)).trans (card_filter_val_lt k)

/-- A uniform coin from the challenger's copy makes the bit of a round `true` with probability
`k / N`, whatever the coin from the proposer's copy. -/
theorem map_coinBit_uniformOfFintype_left {N : ℕ} [NeZero N] (k : Fin (N + 1)) (z : ZMod N) :
    (PMF.uniformOfFintype (ZMod N)).map (fun w => coinBit k w z) true = (k.val : ℝ≥0∞) / N :=
  map_decide_val_lt_uniform k (Equiv.addRight z) _ fun _ => rfl

/-- A uniform coin from the proposer's copy makes the bit of a round `true` with probability
`k / N`, whatever the coin from the challenger's copy. -/
theorem map_coinBit_uniformOfFintype_right {N : ℕ} [NeZero N] (k : Fin (N + 1)) (z : ZMod N) :
    (PMF.uniformOfFintype (ZMod N)).map (fun w => coinBit k z w) true = (k.val : ℝ≥0∞) / N :=
  map_decide_val_lt_uniform k (Equiv.addLeft z) _ fun _ => rfl

/-- A `Bool`-valued law with mass `k / N` at `true` has mass `(N - k) / N` at `false`. -/
private theorem apply_false_of_apply_true {N : ℕ} [NeZero N] (k : Fin (N + 1)) (ν : PMF Bool)
    (h : ν true = (k.val : ℝ≥0∞) / N) : ν false = ((N - k.val : ℕ) : ℝ≥0∞) / N := by
  have hsum := PMF.apply_true_add_apply_false ν
  have hN : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hone : (k.val : ℝ≥0∞) / N + ((N - k.val : ℕ) : ℝ≥0∞) / N = 1 := by
    rw [ENNReal.div_add_div_same, ← Nat.cast_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.1 k.isLt),
      ENNReal.div_self hN (ENNReal.natCast_ne_top N)]
  rw [h, ← hone] at hsum
  exact (ENNReal.add_right_inj (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hN)).1 hsum

/-- The expectation of a function of a `Bool`-valued statistic, through the law of the
statistic. -/
private theorem tsum_mul_comp_bool {α : Type} (p : PMF α) (f : α → Bool) (g : Bool → ℝ≥0∞) :
    ∑' a, p a * g (f a) = (p.map f) true * g true + (p.map f) false * g false := by
  rw [← PMF.tsum_map_mul, tsum_bool, add_comm]

/-! ### The computation from a prefix -/

/-- The law of the transcript after `n` more steps of the step law `σ` from the prefix `bits`. -/
private noncomputable def traceFrom (σ : List Bool → PMF Bool) : ℕ → List Bool → PMF (List Bool)
  | 0, bits => PMF.pure bits
  | n + 1, bits => (σ bits).bind fun bit => traceFrom σ n (bit :: bits)

/-- The law of the output after `n` more steps of the step law `σ` from the prefix `bits`. -/
private noncomputable def lawFrom (σ : List Bool → PMF Bool) : ℕ → List Bool → PMF Bool
  | 0, bits => PMF.pure (bits.headD false)
  | n + 1, bits => (σ bits).bind fun bit => lawFrom σ n (bit :: bits)

private theorem traceFrom_succ_last (σ : List Bool → PMF Bool) :
    ∀ n bits, traceFrom σ (n + 1) bits =
      (traceFrom σ n bits).bind fun prefix_ => (σ prefix_).bind fun bit => PMF.pure (bit :: prefix_)
  | 0, bits => by simp [traceFrom]
  | n + 1, bits => by
    change (σ bits).bind (fun bit => traceFrom σ (n + 1) (bit :: bits)) =
      ((σ bits).bind fun bit => traceFrom σ n (bit :: bits)).bind _
    simp only [traceFrom_succ_last σ n, PMF.bind_bind]

private theorem ev_transcript (σ : List Bool → PMF Bool) :
    ∀ n, ev σ (transcript n) = traceFrom σ n []
  | 0 => rfl
  | n + 1 => by
    rw [traceFrom_succ_last, ← ev_transcript σ n]
    simp only [transcript, ev_bind, ev_query, ev_pure]

private theorem map_headD_traceFrom (σ : List Bool → PMF Bool) :
    ∀ n bits, (traceFrom σ n bits).map (fun y => y.headD false) = lawFrom σ n bits
  | 0, bits => by simp [traceFrom, lawFrom, PMF.pure_map]
  | n + 1, bits => by
    simp only [traceFrom, lawFrom, PMF.map_bind, map_headD_traceFrom σ n]

private theorem ev_output (σ : List Bool → PMF Bool) (n : ℕ) :
    ev σ (output n) = lawFrom σ n [] := by
  rw [output, ev_map, ev_transcript, map_headD_traceFrom]

/-! ### The honest players and the verifier -/

/-- A test of the sample count that can only come out as `b` when the sample mean is off by `e`
comes out as `b` with probability at most `f`. -/
private theorem map_countLaw_apply_le (ν : PMF Bool) {e f : ℝ} (he : 0 < e) (hf0 : 0 < f)
    (hf : f < 2) (test : Fin (sampleCount e f + 1) → Bool) (b : Bool)
    (h : ∀ count, test count = b →
      e ≤ |(count.val : ℝ) / sampleCount e f - (ν true).toReal|) :
    (countLaw ν (sampleCount e f)).map test b ≤ ENNReal.ofReal f := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  exact ((countLaw ν _).toOuterMeasure_mono fun count hc => h count hc.1).trans
    (countLaw_sampleCount_tail ν he hf0 hf)

/-- The law of the verifier's decision. -/
private theorem ev_verdict (law : List Bool → PMF Bool) (P : Params) (bits : List Bool)
    (claim : Fin (P.grid + 1)) :
    ev law (verdict P bits claim) =
      (countLaw (law bits) P.verifierSamples).map fun count : Fin (P.verifierSamples + 1) =>
        decide (|(claim.val : ℝ) / P.grid - (count.val : ℝ) / P.verifierSamples| <
          P.verifierTolerance) := by
  exact (ev_bind _ _ _).trans (by rw [ev_countTrue]; rfl)

/-- The law of the honest proposer's claim. -/
private theorem ev_honestProposer_claim (law : List Bool → PMF Bool) (P : Params)
    (history : History P.grid) (state : (honestProposer P).State) :
    ev law (((honestProposer P).claim history).run state) =
      (countLaw (law history.bits) P.grid).map fun count => (count, state) := by
  exact (ev_bind _ _ _).trans (by rw [ev_countTrue]; rfl)

/-- The law of the honest challenger's decision to abort. -/
private noncomputable def abortLaw (P : Params) (ν : PMF Bool) (claim : Fin (P.grid + 1)) :
    PMF Bool :=
  (countLaw ν P.challengerSamples).map fun count : Fin (P.challengerSamples + 1) =>
    decide (P.challengerTolerance ≤
      |(claim.val : ℝ) / P.grid - (count.val : ℝ) / P.challengerSamples|)

private theorem ev_honestChallenger_abort (law : List Bool → PMF Bool) (P : Params)
    (history : History P.grid) (round : Round P.grid) (state : (honestChallenger P).State) :
    ev law (((honestChallenger P).abort history round).run state) =
      (abortLaw P (law history.bits) round.claim).map fun stop => (stop, state) := by
  change ev law ((_ : ProbOracleComp StepSpec Bool) >>= fun stop => pure (stop, state)) = _
  simp only [ev_bind, ev_pure, ev_countTrue, abortLaw, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def]

/-- One round of the protocol. -/
private theorem ev_runFrom_succ (law : List Bool → PMF Bool) (P : Params) (A : Proposer P.grid)
    (B : Challenger P.grid) (n : ℕ) (history : History P.grid) (stateA : A.State)
    (stateB : B.State) :
    ev law (runFrom P A B (n + 1) history stateA stateB) =
      (ev law ((A.claim history).run stateA)).bind fun x =>
        (ev law (B.coin history x.1)).bind fun coinA =>
          (ev law (A.coin history x.1)).bind fun coinB =>
            (ev law ((B.abort history ⟨x.1, coinA, coinB⟩).run stateB)).bind fun r =>
              if r.1 then ev law (verdict P history.bits x.1)
              else ev law (runFrom P A B n (⟨x.1, coinA, coinB⟩ :: history) x.2 r.2) := by
  simp only [runFrom, ev_bind, apply_ite (ev law)]

/-! ### The best nearby step law -/

private theorem one_sub_le_of_add_eq_one {a a' q : ℝ≥0∞} (h : a + a' = 1) (ha : a ≤ q) :
    1 - q ≤ a' := by
  exact tsub_le_iff_right.2 (h ▸ add_comm a a' ▸ add_le_add_right ha a')

/-- Moving weight from the smaller value to the larger one increases a mixture. -/
private theorem mix_le_of_le {x x' z z' a b : ℝ≥0∞} (hx : x + x' = 1) (hz : z + z' = 1)
    (hxz : x ≤ z) (hba : b ≤ a) : x * a + x' * b ≤ z * a + z' * b := by
  obtain ⟨d, rfl⟩ := exists_add_of_le hxz
  have hx_top : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hx ▸ le_self_add)
  rw [(ENNReal.add_right_inj hx_top).1 (by rw [hx, ← hz, add_assoc] : x + x' = x + (d + z'))]
  calc x * a + (d + z') * b = x * a + z' * b + d * b := by ring
    _ ≤ x * a + z' * b + d * a := by gcongr
    _ = (x + d) * a + z' * b := by ring

/-- Moving weight from the larger value to the smaller one decreases a mixture. -/
private theorem mix_le_of_ge {x x' z z' a b : ℝ≥0∞} (hx : x + x' = 1) (hz : z + z' = 1)
    (hzx : z ≤ x) (hab : a ≤ b) : x * a + x' * b ≤ z * a + z' * b := by
  obtain ⟨d, rfl⟩ := exists_add_of_le hzx
  have hz_top : z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hz ▸ le_self_add)
  rw [(ENNReal.add_right_inj hz_top).1 (by rw [hz, ← hx, add_assoc] : z + z' = z + (d + x'))]
  calc (z + d) * a + x' * b = z * a + x' * b + d * a := by ring
    _ ≤ z * a + x' * b + d * b := by gcongr
    _ = z * a + (d + x') * b := by ring

/-- The mixture of the values `u` of the two next bits under the law `ν` of the next bit. -/
private noncomputable def mix (ν : PMF Bool) (u : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  ν true * u true + ν false * u false

private theorem mix_le_one (ν : PMF Bool) {u : Bool → ℝ≥0∞} (hu : ∀ bit, u bit ≤ 1) :
    mix ν u ≤ 1 := by
  rw [← PMF.apply_true_add_apply_false ν]
  exact add_le_add (mul_le_of_le_one_right' (hu true)) (mul_le_of_le_one_right' (hu false))

/-- The law of a bit that is `true` with the probability of `ν`, lowered by `b`. -/
private noncomputable def lowLaw (ν : PMF Bool) (b : ℝ) : PMF Bool :=
  PMF.coin ⟨min 1 (max ((ν true).toReal - b) 0),
    le_min zero_le_one (le_max_right _ _), min_le_left _ _⟩

/-- The law of a bit that is `true` with the probability of `ν`, raised by `b`. -/
private noncomputable def highLaw (ν : PMF Bool) (b : ℝ) : PMF Bool :=
  PMF.coin ⟨min 1 (max ((ν true).toReal + b) 0),
    le_min zero_le_one (le_max_right _ _), min_le_left _ _⟩

private theorem lowLaw_true_le (ν μ : PMF Bool) {b : ℝ}
    (h : |(μ true).toReal - (ν true).toReal| ≤ b) : lowLaw ν b true ≤ μ true := by
  rw [lowLaw, PMF.coin_apply, ite_eq_left rfl,
    ENNReal.ofReal_le_iff_le_toReal (μ.apply_ne_top true)]
  exact (min_le_right _ _).trans
    (max_le (by linarith [(abs_le.1 h).1]) ENNReal.toReal_nonneg)

private theorem le_highLaw_true (ν μ : PMF Bool) {b : ℝ}
    (h : |(μ true).toReal - (ν true).toReal| ≤ b) : μ true ≤ highLaw ν b true := by
  rw [highLaw, PMF.coin_apply, ite_eq_left rfl, ENNReal.le_ofReal_iff_toReal_le
    (μ.apply_ne_top true) (le_min zero_le_one (le_max_right _ _))]
  exact le_min (PMF.toReal_apply_le_one μ true) (le_max_of_le_left (by linarith [(abs_le.1 h).2]))

private theorem closeTo_lowLaw (ν : PMF Bool) {b : ℝ} (hb : 0 ≤ b) :
    CloseTo ν (lowLaw ν b) (ENNReal.ofReal b) := by
  rw [closeTo_ofReal_iff_dist_le hb, PMF.dist_bool, lowLaw, PMF.coin_apply_toReal, ite_eq_left rfl]
  have hle : min 1 (max ((ν true).toReal - b) 0) ≤ (ν true).toReal :=
    (min_le_right _ _).trans (max_le (by linarith) ENNReal.toReal_nonneg)
  have hge : (ν true).toReal - b ≤ min 1 (max ((ν true).toReal - b) 0) :=
    le_min (by linarith [PMF.toReal_apply_le_one ν true]) (le_max_left _ _)
  exact abs_le.2 ⟨by linarith, by linarith⟩

private theorem closeTo_highLaw (ν : PMF Bool) {b : ℝ} (hb : 0 ≤ b) :
    CloseTo ν (highLaw ν b) (ENNReal.ofReal b) := by
  rw [closeTo_ofReal_iff_dist_le hb, PMF.dist_bool, highLaw, PMF.coin_apply_toReal, ite_eq_left rfl]
  have hge : (ν true).toReal ≤ min 1 (max ((ν true).toReal + b) 0) :=
    le_min (PMF.toReal_apply_le_one ν true) (le_max_of_le_left (by linarith))
  have hle : min 1 (max ((ν true).toReal + b) 0) ≤ (ν true).toReal + b :=
    (min_le_right _ _).trans (max_le le_rfl (by linarith [ENNReal.toReal_nonneg (a := ν true)]))
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The least probability of the output `false` after `n` more steps from `bits`, over step laws
that move each step of `law` by at most `b`. -/
private noncomputable def rejectValue (law : List Bool → PMF Bool) (b : ℝ) :
    ℕ → List Bool → ℝ≥0∞
  | 0, bits => if bits.headD false then 0 else 1
  | n + 1, bits =>
    min (mix (lowLaw (law bits) b) fun bit => rejectValue law b n (bit :: bits))
      (mix (highLaw (law bits) b) fun bit => rejectValue law b n (bit :: bits))

private theorem rejectValue_le_one (law : List Bool → PMF Bool) (b : ℝ) :
    ∀ n bits, rejectValue law b n bits ≤ 1
  | 0, bits => by rw [rejectValue]; split_ifs <;> simp
  | n + 1, bits => by
    rw [rejectValue]
    exact (min_le_left _ _).trans (mix_le_one _ fun bit => rejectValue_le_one law b n _)

/-- Any law of the next bit within `b` of `law` does no better than the best nearby step law. -/
private theorem rejectValue_succ_le_mix (law : List Bool → PMF Bool) {b : ℝ} (n : ℕ)
    (bits : List Bool) (μ : PMF Bool)
    (h : |(μ true).toReal - (law bits true).toReal| ≤ b) :
    rejectValue law b (n + 1) bits ≤ mix μ fun bit => rejectValue law b n (bit :: bits) := by
  rw [rejectValue]
  rcases le_total (rejectValue law b n (false :: bits)) (rejectValue law b n (true :: bits))
    with hle | hle
  · exact (min_le_left _ _).trans (mix_le_of_le (PMF.apply_true_add_apply_false _)
      (PMF.apply_true_add_apply_false _) (lowLaw_true_le _ μ h) hle)
  · exact (min_le_right _ _).trans (mix_le_of_ge (PMF.apply_true_add_apply_false _)
      (PMF.apply_true_add_apply_false _) (le_highLaw_true _ μ h) hle)

/-- The step law that realizes `rejectValue` for a computation of `T + 1` steps. -/
private noncomputable def bestLaw (law : List Bool → PMF Bool) (b : ℝ) (T : ℕ)
    (bits : List Bool) : PMF Bool :=
  if mix (lowLaw (law bits) b) (fun bit => rejectValue law b (T - bits.length) (bit :: bits)) ≤
      mix (highLaw (law bits) b) (fun bit => rejectValue law b (T - bits.length) (bit :: bits))
  then lowLaw (law bits) b else highLaw (law bits) b

private theorem closeTo_bestLaw (law : List Bool → PMF Bool) {b : ℝ} (hb : 0 ≤ b) (T : ℕ)
    (bits : List Bool) : CloseTo (law bits) (bestLaw law b T bits) (ENNReal.ofReal b) := by
  rw [bestLaw]
  split_ifs
  exacts [closeTo_lowLaw _ hb, closeTo_highLaw _ hb]

private theorem lawFrom_bestLaw (law : List Bool → PMF Bool) (b : ℝ) (T : ℕ) :
    ∀ n bits, bits.length + n = T + 1 →
      lawFrom (bestLaw law b T) n bits false = rejectValue law b n bits
  | 0, bits, _ => by
    rw [lawFrom, rejectValue, PMF.pure_apply]
    cases bits.headD false <;> simp
  | n + 1, bits, h => by
    have hlen : T - bits.length = n := by omega
    rw [lawFrom, PMF.bind_apply, tsum_fintype, Fintype.sum_bool,
      lawFrom_bestLaw law b T n (true :: bits) (by simp; omega),
      lawFrom_bestLaw law b T n (false :: bits) (by simp; omega), rejectValue, bestLaw, hlen]
    split_ifs with hle
    exacts [(min_eq_left hle).symm, (min_eq_right (le_of_not_ge hle)).symm]

/-! ### Rounds -/

private theorem tsum_mul_le_tsum_mul_add {α : Type} (μ : PMF α) {g f : α → ℝ≥0∞} {d : ℝ≥0∞}
    (h : ∀ a, g a ≤ f a + d) : ∑' a, μ a * g a ≤ ∑' a, μ a * f a + d := by
  calc ∑' a, μ a * g a ≤ ∑' a, (μ a * f a + μ a * d) :=
        tsum_le_tsum fun a => (mul_le_mul_right (h a) _).trans_eq (mul_add _ _ _)
    _ = ∑' a, μ a * f a + d := by
        rw [tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

private theorem le_bind_apply_add {α β : Type} (μ : PMF α) {f : α → PMF β} {b : β}
    {c d : ℝ≥0∞} (h : ∀ a, c ≤ f a b + d) : c ≤ μ.bind f b + d := by
  rw [PMF.bind_apply]
  calc c = ∑' a, μ a * c := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
    _ ≤ ∑' a, μ a * f a b + d := tsum_mul_le_tsum_mul_add μ h

/-- The law of the bit of a round when the challenger's copy is honest. -/
private noncomputable def bitLawLeft {N : ℕ} [NeZero N] (k : Fin (N + 1)) (coinB : ZMod N) :
    PMF Bool :=
  (PMF.uniformOfFintype (ZMod N)).map fun coinA => coinBit k coinA coinB

/-- The law of the bit of a round when the proposer's copy is honest. -/
private noncomputable def bitLawRight {N : ℕ} [NeZero N] (k : Fin (N + 1)) (coinA : ZMod N) :
    PMF Bool :=
  (PMF.uniformOfFintype (ZMod N)).map fun coinB => coinBit k coinA coinB

private theorem toReal_div_grid {N : ℕ} (k : Fin (N + 1)) :
    ((k.val : ℝ≥0∞) / N).toReal = (k.val : ℝ) / N := by
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-! ### Soundness -/

/-- One round against the honest challenger, as an inequality between numbers: `aT`, `aF` are
the probabilities that it aborts or not, `vF` that the verifier then rejects, `M` the value of
continuing and `U` the value before the round. -/
private theorem sound_round {aT aF vF M U α qc vc : ℝ≥0∞} (ha : aT + aF = 1) (hU : U ≤ 1)
    (hα : α ≤ 1 - vc)
    (hcases : (1 - qc ≤ aF ∧ U ≤ M) ∨ (1 - vc ≤ vF ∧ U ≤ M) ∨ (1 - qc ≤ aT ∧ 1 - vc ≤ vF)) :
    (1 - qc) * α * U ≤ aT * vF + aF * (α * M) := by
  have hαU : α * U ≤ 1 - vc := (mul_le_of_le_one_right' hU).trans hα
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · calc (1 - qc) * α * U = (1 - qc) * (α * U) := mul_assoc _ _ _
      _ ≤ aF * (α * M) := by gcongr
      _ ≤ aT * vF + aF * (α * M) := le_add_self
  · calc (1 - qc) * α * U = (1 - qc) * (α * U) := mul_assoc _ _ _
      _ ≤ α * U := mul_le_of_le_one_left' tsub_le_self
      _ = aT * (α * U) + aF * (α * U) := by rw [← add_mul, ha, one_mul]
      _ ≤ aT * vF + aF * (α * M) := by gcongr; exact hαU.trans h1
  · calc (1 - qc) * α * U = (1 - qc) * (α * U) := mul_assoc _ _ _
      _ ≤ aT * vF := mul_le_mul' h1 (hαU.trans h2)
      _ ≤ aT * vF + aF * (α * M) := le_self_add

/-- Against the honest challenger, whatever the proposer does, the verifier rejects at least as
often as the best nearby step law outputs `false`, up to the failure probabilities of the
challenger's and the verifier's estimates. -/
private theorem reject_ge (law : List Bool → PMF Bool) (P : Params) [NeZero P.grid]
    (A : Proposer P.grid) {s b : ℝ} {qc vc : ℝ≥0∞} (hsb : s ≤ b)
    (h1 : ∀ bits (k : Fin (P.grid + 1)),
      |(k.val : ℝ) / P.grid - (law bits true).toReal| ≤ s → abortLaw P (law bits) k true ≤ qc)
    (h2 : ∀ bits (k : Fin (P.grid + 1)),
      b ≤ |(k.val : ℝ) / P.grid - (law bits true).toReal| → abortLaw P (law bits) k false ≤ qc)
    (h3 : ∀ bits (k : Fin (P.grid + 1)),
      s ≤ |(k.val : ℝ) / P.grid - (law bits true).toReal| →
        ev law (verdict P bits k) true ≤ vc) :
    ∀ n (history : History P.grid) (stateA : A.State) (stateB : (honestChallenger P).State),
      (1 - vc) * (1 - qc) ^ n * rejectValue law b n history.bits ≤
        ev law (runFrom P A (honestChallenger P) n history stateA stateB) false
  | 0, history, stateA, stateB => by
    change _ ≤ (PMF.pure (history.bits.headD false)) false
    rw [rejectValue, PMF.pure_apply, pow_zero, mul_one]
    cases history.bits.headD false <;> simp
  | n + 1, history, stateA, stateB => by
    rw [ev_runFrom_succ]
    refine PMF.le_bind_apply_on_support _ fun x _ => ?_
    change _ ≤ ((ev law (uniformCoin P.grid)).bind fun coinA =>
      (ev law (A.coin history x.1)).bind fun coinB =>
        (ev law (((honestChallenger P).abort history ⟨x.1, coinA, coinB⟩).run stateB)).bind
          fun r => _) false
    rw [ev_uniformCoin, PMF.bind_comm]
    refine PMF.le_bind_apply_on_support _ fun coinB _ => ?_
    simp only [ev_honestChallenger_abort, PMF.bind_map, Function.comp_def]
    rw [PMF.bind_apply]
    simp only [PMF.bind_apply, tsum_bool, Bool.false_eq_true, ite_false, ite_true]
    have hIH (coinA : ZMod P.grid) :
        (1 - vc) * (1 - qc) ^ n *
            rejectValue law b n (coinBit x.1 coinA coinB :: history.bits) ≤
          ev law (runFrom P A (honestChallenger P) n (⟨x.1, coinA, coinB⟩ :: history) x.2
            stateB) false :=
      reject_ge law P A hsb h1 h2 h3 n (⟨x.1, coinA, coinB⟩ :: history) x.2 stateB
    have ha := PMF.apply_true_add_apply_false (abortLaw P (law history.bits) x.1)
    have hv := PMF.apply_true_add_apply_false (ev law (verdict P history.bits x.1))
    have hbit : (bitLawLeft x.1 coinB true).toReal = (x.1.val : ℝ) / P.grid := by
      rw [bitLawLeft, map_coinBit_uniformOfFintype_left, toReal_div_grid]
    have hM (hD : |(x.1.val : ℝ) / P.grid - (law history.bits true).toReal| ≤ b) :=
      rejectValue_succ_le_mix law (b := b) n history.bits (bitLawLeft x.1 coinB)
        (by rw [hbit]; exact hD)
    have hsum : ∑' coinA, PMF.uniformOfFintype (ZMod P.grid) coinA *
        rejectValue law b n (coinBit x.1 coinA coinB :: history.bits) =
          mix (bitLawLeft x.1 coinB) fun bit => rejectValue law b n (bit :: history.bits) :=
      tsum_mul_comp_bool (PMF.uniformOfFintype (ZMod P.grid)) (fun coinA => coinBit x.1 coinA coinB)
        fun bit => rejectValue law b n (bit :: history.bits)
    calc (1 - vc) * (1 - qc) ^ (n + 1) * rejectValue law b (n + 1) history.bits
        = (1 - qc) * ((1 - vc) * (1 - qc) ^ n) * rejectValue law b (n + 1) history.bits := by
          ring
      _ ≤ abortLaw P (law history.bits) x.1 true * ev law (verdict P history.bits x.1) false +
            abortLaw P (law history.bits) x.1 false * ((1 - vc) * (1 - qc) ^ n *
              mix (bitLawLeft x.1 coinB) fun bit => rejectValue law b n (bit :: history.bits)) := by
          refine sound_round ha (rejectValue_le_one law b _ _)
            (mul_le_of_le_one_right' (pow_le_one' tsub_le_self n)) ?_
          rcases le_total |(x.1.val : ℝ) / P.grid - (law history.bits true).toReal| s
            with hs | hs
          · exact Or.inl ⟨one_sub_le_of_add_eq_one ha (h1 _ _ hs), hM (hs.trans hsb)⟩
          · rcases le_total |(x.1.val : ℝ) / P.grid - (law history.bits true).toReal| b
              with hb | hb
            · exact Or.inr (Or.inl ⟨one_sub_le_of_add_eq_one hv (h3 _ _ hs), hM hb⟩)
            · exact Or.inr (Or.inr ⟨one_sub_le_of_add_eq_one ((add_comm _ _).trans ha)
                (h2 _ _ hb), one_sub_le_of_add_eq_one hv (h3 _ _ hs)⟩)
      _ = ∑' coinA, PMF.uniformOfFintype (ZMod P.grid) coinA *
            (abortLaw P (law history.bits) x.1 false * ((1 - vc) * (1 - qc) ^ n *
              rejectValue law b n (coinBit x.1 coinA coinB :: history.bits)) +
            abortLaw P (law history.bits) x.1 true *
              ev law (verdict P history.bits x.1) false) := by
          rw [← hsum]
          simp only [mul_add, ← ENNReal.tsum_mul_left]
          rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, add_comm]
          congr 1
          exact tsum_congr fun coinA => by ring
      _ ≤ _ := tsum_le_tsum fun coinA => by gcongr; exact hIH coinA

/-! ### Completeness -/

/-- The honest claim is unbiased: averaging the mixture at the claimed probability over the
sample count gives the mixture at the true probability. -/
private theorem tsum_countLaw_mul_mix (ν : PMF Bool) {N : ℕ} [NeZero N] (x y : ℝ≥0∞) :
    ∑' k, countLaw ν N k *
        ((k.val : ℝ≥0∞) / N * x + ((N - k.val : ℕ) : ℝ≥0∞) / N * y) =
      ν true * x + ν false * y := by
  have hN : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hterm (k : Fin (N + 1)) :
      countLaw ν N k * ((k.val : ℝ≥0∞) / N * x + ((N - k.val : ℕ) : ℝ≥0∞) / N * y) =
        countLaw ν N k * (k.val : ℝ≥0∞) * (x / N) +
          countLaw ν N k * ((N - k.val : ℕ) : ℝ≥0∞) * (y / N) := by
    simp only [div_eq_mul_inv]
    ring
  have hcancel (z w : ℝ≥0∞) : N * z * (w / N) = z * w := by
    rw [div_eq_mul_inv]
    calc N * z * (w * (N : ℝ≥0∞)⁻¹) = z * w * (N * (N : ℝ≥0∞)⁻¹) := by ring
      _ = z * w := by rw [ENNReal.mul_inv_cancel hN (ENNReal.natCast_ne_top N), mul_one]
  simp only [hterm]
  rw [tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, countLaw_mean_true,
    countLaw_mean_false, hcancel, hcancel]

/-- Summing a bound that holds up to a slack off an unlikely event. -/
private theorem tsum_mul_le_tsum_mul_add_of_far {α : Type} (μ : PMF α) (far : Set α)
    {g X : α → ℝ≥0∞} {d e qc : ℝ≥0∞} (hclose : ∀ a ∉ far, g a ≤ X a + d)
    (hfar : ∀ a ∈ far, g a ≤ e) (hμ : μ.toOuterMeasure far ≤ qc) :
    ∑' a, μ a * g a ≤ ∑' a, μ a * X a + (d + e * qc) := by
  classical
  have hpoint (a : α) : g a ≤ X a + d + e * far.indicator 1 a := by
    by_cases ha : a ∈ far
    · rw [Set.indicator_of_mem ha, Pi.one_apply, mul_one]
      exact (hfar a ha).trans le_add_self
    · exact (hclose a ha).trans le_self_add
  calc ∑' a, μ a * g a ≤ ∑' a, (μ a * X a + μ a * d + e * (μ a * far.indicator 1 a)) :=
        tsum_le_tsum fun a => (mul_le_mul_right (hpoint a) _).trans_eq (by ring)
    _ = ∑' a, μ a * X a + d + e * μ.toOuterMeasure far := by
        rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul,
          ENNReal.tsum_mul_left, PMF.toOuterMeasure_eq_tsum_mul_indicator]
    _ ≤ ∑' a, μ a * X a + (d + e * qc) := by
        rw [add_assoc]
        gcongr

/-- Against any challenger, the honest proposer makes the verifier accept at least as often as
the computation outputs `true`, up to the failure probabilities of the proposer's and the
verifier's estimates. -/
private theorem accept_ge (law : List Bool → PMF Bool) (P : Params) [NeZero P.grid]
    (B : Challenger P.grid) {c : ℝ} {qc vc : ℝ≥0∞}
    (hfar : ∀ bits, (countLaw (law bits) P.grid).toOuterMeasure
      {k | c ≤ |(k.val : ℝ) / P.grid - (law bits true).toReal|} ≤ qc)
    (hver : ∀ bits (k : Fin (P.grid + 1)),
      |(k.val : ℝ) / P.grid - (law bits true).toReal| ≤ c →
        ev law (verdict P bits k) false ≤ vc) :
    ∀ n (history : History P.grid) (stateA : (honestProposer P).State) (stateB : B.State),
      (1 - vc) * lawFrom law n history.bits true ≤
        ev law (runFrom P (honestProposer P) B n history stateA stateB) true +
          (1 - vc) * n * qc
  | 0, history, stateA, stateB => by
    change _ ≤ (PMF.pure (history.bits.headD false)) true + _
    rw [lawFrom]
    exact (mul_le_of_le_one_left' tsub_le_self).trans le_self_add
  | n + 1, history, stateA, stateB => by
    have hlaw : lawFrom law (n + 1) history.bits true =
        law history.bits true * lawFrom law n (true :: history.bits) true +
          law history.bits false * lawFrom law n (false :: history.bits) true := by
      rw [lawFrom, PMF.bind_apply, tsum_bool, add_comm]
    rw [ev_runFrom_succ, ev_honestProposer_claim, PMF.bind_map, PMF.bind_apply, hlaw,
      ← tsum_countLaw_mul_mix (law history.bits) (N := P.grid), ← ENNReal.tsum_mul_left]
    simp only [Function.comp_def, mul_left_comm (1 - vc) (countLaw _ _ _), Nat.cast_add,
      Nat.cast_one, show (1 - vc) * ((n : ℝ≥0∞) + 1) * qc = (1 - vc) * n * qc + (1 - vc) * qc
        by ring]
    refine tsum_mul_le_tsum_mul_add_of_far _
      {k | c ≤ |(k.val : ℝ) / P.grid - (law history.bits true).toReal|}
      (fun k hk => ?_) (fun k _ => ?_) (hfar history.bits)
    · have hk' : |(k.val : ℝ) / P.grid - (law history.bits true).toReal| < c := not_le.1 hk
      refine le_bind_apply_add _ fun coinA => ?_
      have hT := map_coinBit_uniformOfFintype_right k coinA
      have hF := apply_false_of_apply_true k _ hT
      change _ ≤ ((ev law (uniformCoin P.grid)).bind fun coinB => _) true + _
      rw [ev_uniformCoin, PMF.bind_apply]
      have hmix : (1 - vc) * ((k.val : ℝ≥0∞) / P.grid * lawFrom law n (true :: history.bits) true +
          ((P.grid - k.val : ℕ) : ℝ≥0∞) / P.grid * lawFrom law n (false :: history.bits) true) =
          ∑' coinB, PMF.uniformOfFintype (ZMod P.grid) coinB *
            ((1 - vc) * lawFrom law n (coinBit k coinA coinB :: history.bits) true) := by
        rw [← hT, ← hF, ← tsum_mul_comp_bool (PMF.uniformOfFintype (ZMod P.grid))
          (fun coinB => coinBit k coinA coinB)
          (fun bit => lawFrom law n (bit :: history.bits) true), ← ENNReal.tsum_mul_left]
        exact tsum_congr fun coinB => by ring
      rw [hmix]
      refine tsum_mul_le_tsum_mul_add _ fun coinB => ?_
      refine le_bind_apply_add _ fun r => ?_
      cases hr : r.1
      · exact accept_ge law P B hfar hver n (⟨k, coinA, coinB⟩ :: history) stateA r.2
      · have hv := PMF.apply_true_add_apply_false (ev law (verdict P history.bits k))
        exact ((mul_le_of_le_one_right' (PMF.coe_le_one _ _)).trans
          (one_sub_le_of_add_eq_one ((add_comm _ _).trans hv) (hver _ _ hk'.le))).trans le_self_add
    · have hT := map_coinBit_uniformOfFintype_right k (0 : ZMod P.grid)
      have hF := apply_false_of_apply_true k _ hT
      rw [← hT, ← hF]
      exact mul_le_of_le_one_right' (mix_le_one (bitLawRight k 0)
        (u := fun bit => lawFrom law n (bit :: history.bits) true) fun bit => PMF.coe_le_one _ _)

/-! ### The default parameters -/

/-- If `a` is within `d` of `p` but at least `t` from `x`, then `x` is at least `t - d` from
`p`. -/
private theorem le_abs_sub_of_le_of_le {a p x d t e : ℝ} (h1 : |a - p| ≤ d) (h2 : t ≤ |a - x|)
    (hte : e + d ≤ t) : e ≤ |x - p| := by
  linarith [abs_sub_le a p x, abs_sub_comm p x]

/-- If `a` is at least `d` from `p` but within `t` of `x`, then `x` is at least `d - t` from
`p`. -/
private theorem le_abs_sub_of_le_of_lt {a p x d t e : ℝ} (h1 : d ≤ |a - p|) (h2 : |a - x| < t)
    (hte : e + t ≤ d) : e ≤ |x - p| := by
  linarith [abs_sub_le a x p]

variable {K : ℝ≥0}

private theorem default_failure_lt_two (T : ℕ) : (1 : ℝ) / (100 * (T + 1)) < 2 := by
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- The default parameters are positive: the grid, both sample counts and both tolerances. -/
theorem Params.default_pos (hK : 0 < K) (T : ℕ) :
    0 < (Params.default K T).grid ∧ 0 < (Params.default K T).challengerSamples ∧
      0 < (Params.default K T).verifierSamples ∧ 0 < (Params.default K T).challengerTolerance ∧
        0 < (Params.default K T).verifierTolerance := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  exact ⟨sampleCount_pos (by positivity) (by positivity) (default_failure_lt_two T),
    sampleCount_pos (by positivity) (by positivity) (default_failure_lt_two T),
    sampleCount_pos (by positivity) (by norm_num) (by norm_num),
    by simp only [Params.default]; positivity, by simp only [Params.default]; positivity⟩

private theorem default_claim_tail (hK : 0 < K) (T : ℕ) (ν : PMF Bool) :
    (countLaw ν (Params.default K T).grid).toOuterMeasure
        {k | 1 / (100 * (K : ℝ)) ≤
          |(k.val : ℝ) / (Params.default K T).grid - (ν true).toReal|} ≤
      ENNReal.ofReal (1 / (100 * (T + 1))) :=
  countLaw_sampleCount_tail ν (by positivity) (by positivity) (default_failure_lt_two T)

private theorem default_verdict_false_le (hK : 0 < K) (T : ℕ) (law : List Bool → PMF Bool)
    (bits : List Bool) (k : Fin ((Params.default K T).grid + 1))
    (h : |(k.val : ℝ) / (Params.default K T).grid - (law bits true).toReal| ≤
      1 / (100 * (K : ℝ))) :
    ev law (verdict (Params.default K T) bits k) false ≤ ENNReal.ofReal (1 / 100) := by
  rw [ev_verdict]
  refine map_countLaw_apply_le (law bits) (e := 1 / (200 * (K : ℝ))) (f := 1 / 100)
    (by positivity) (by norm_num) (by norm_num) _ false fun count hcount => ?_
  exact le_abs_sub_of_le_of_le h (not_lt.1 (of_decide_eq_false hcount))
    (le_of_eq (by simp only [Params.default]; field_simp; ring))

private theorem default_verdict_true_le (hK : 0 < K) (T : ℕ) (law : List Bool → PMF Bool)
    (bits : List Bool) (k : Fin ((Params.default K T).grid + 1))
    (h : 2 / (100 * (K : ℝ)) ≤
      |(k.val : ℝ) / (Params.default K T).grid - (law bits true).toReal|) :
    ev law (verdict (Params.default K T) bits k) true ≤ ENNReal.ofReal (1 / 100) := by
  rw [ev_verdict]
  refine map_countLaw_apply_le (law bits) (e := 1 / (200 * (K : ℝ))) (f := 1 / 100)
    (by positivity) (by norm_num) (by norm_num) _ true fun count hcount => ?_
  exact le_abs_sub_of_le_of_lt h (of_decide_eq_true hcount)
    (le_of_eq (by simp only [Params.default]; field_simp; ring))

private theorem default_abort_true_le (hK : 0 < K) (T : ℕ) (ν : PMF Bool)
    (k : Fin ((Params.default K T).grid + 1))
    (h : |(k.val : ℝ) / (Params.default K T).grid - (ν true).toReal| ≤ 2 / (100 * (K : ℝ))) :
    abortLaw (Params.default K T) ν k true ≤ ENNReal.ofReal (1 / (100 * (T + 1))) := by
  refine map_countLaw_apply_le ν (e := 3 / (200 * (K : ℝ))) (f := 1 / (100 * (T + 1)))
    (by positivity) (by positivity) (default_failure_lt_two T) _ true fun count hcount => ?_
  exact le_abs_sub_of_le_of_le h (of_decide_eq_true hcount)
    (le_of_eq (by simp only [Params.default]; field_simp; ring))

private theorem default_abort_false_le (hK : 0 < K) (T : ℕ) (ν : PMF Bool)
    (k : Fin ((Params.default K T).grid + 1))
    (h : 5 / (100 * (K : ℝ)) ≤ |(k.val : ℝ) / (Params.default K T).grid - (ν true).toReal|) :
    abortLaw (Params.default K T) ν k false ≤ ENNReal.ofReal (1 / (100 * (T + 1))) := by
  refine map_countLaw_apply_le ν (e := 3 / (200 * (K : ℝ))) (f := 1 / (100 * (T + 1)))
    (by positivity) (by positivity) (default_failure_lt_two T) _ false fun count hcount => ?_
  exact le_abs_sub_of_le_of_lt h (not_le.1 (of_decide_eq_false hcount))
    (le_of_eq (by simp only [Params.default]; field_simp; ring))

private theorem toReal_one_sub_ofReal {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    (1 - ENNReal.ofReal v).toReal = 1 - v := by
  rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.2 h1) ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_ofReal h0]

end Proofs

/-! ### Correctness -/

/-- **Completeness, as a step.** A step toward [BrownCohenIrvingPiliouras2024, Theorem 6.2], not
that theorem: if the output of a `(T + 1)`-step computation is `true` with probability at least
`2 / 3`, then the honest proposer of the protocol of Figure 1 makes the verifier accept with
probability at least `3 / 5` against every challenger. No Lipschitz hypothesis is needed.

The challenger is an arbitrary program with private state, private coins and unbounded sample
access to the step law. Nothing is claimed about running time or query counts, the grid replaces
the real numbers of the source, and the constants are `Params.default`, which depend on `K`. -/
theorem completeness_stepLaw {K : ℝ≥0} (hK : 0 < K) (T : ℕ) {law : List Bool → PMF Bool}
    (hyes : 2 / 3 ≤
      OracleComp.evalWith (sumHandler ProbComp.unifOracle law) (output (T + 1)) true)
    (B : Challenger (Params.default K T).grid) :
    3 / 5 ≤ OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
      (run (Params.default K T) (honestProposer (Params.default K T)) B) true := by
  have : NeZero (Params.default K T).grid := ⟨(Params.default_pos hK T).1.ne'⟩
  have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hacc := accept_ge law (Params.default K T) B
    (fun bits => default_claim_tail hK T (law bits))
    (fun bits k h => default_verdict_false_le hK T law bits k h) (T + 1) []
    (honestProposer (Params.default K T)).init B.init
  change _ * lawFrom law (T + 1) [] true ≤
    ev law (run (Params.default K T) (honestProposer (Params.default K T)) B) true + _ at hacc
  change 3 / 5 ≤ ev law (run (Params.default K T) (honestProposer (Params.default K T)) B) true
  have hfin := PMF.apply_ne_top
    (ev law (run (Params.default K T) (honestProposer (Params.default K T)) B)) true
  have hyes' : (2 / 3 : ℝ) ≤ (lawFrom law (T + 1) [] true).toReal := by
    rw [← ev_output]
    simpa [ev] using ENNReal.toReal_mono (PMF.apply_ne_top _ _) hyes
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin, by
    simp [ENNReal.mul_eq_top]⟩) hacc
  rw [ENNReal.toReal_add hfin (by simp [ENNReal.mul_eq_top]), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_one_sub_ofReal (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one]
    at hreal
  have hslack : (1 - 1 / 100 : ℝ) * ((T : ℝ) + 1) * (1 / (100 * (T + 1))) = 99 / 10000 := by
    field_simp; ring
  rw [hslack] at hreal
  rw [← ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) (by simp)) hfin]
  linarith [show ((3 / 5 : ℝ≥0∞)).toReal = 3 / 5 by simp]

/-- **Soundness, as a step.** A step toward [BrownCohenIrvingPiliouras2024, Theorem 6.2], not
that theorem: if the output of a `(T + 1)`-step computation is `K`-Lipschitz in its whole step
law (every step and every transcript prefix, which is stronger than Definition 6.1 of the source;
the reason is recorded in cslib-frontier issue #7579) and is `true` with probability at most
`1 / 3`, then against the honest challenger of the protocol of Figure 1 every proposer makes the
verifier accept with probability at most `2 / 5`.

The proposer is an arbitrary program with private state, private coins and unbounded sample
access to the step law. Nothing is claimed about running time or query counts, the grid replaces
the real numbers of the source, and the constants are `Params.default`. -/
theorem soundness_of_lipschitzAt_stepLaw {K : ℝ≥0} (hK : 0 < K) (T : ℕ)
    {law : List Bool → PMF Bool} (hL : LipschitzAt K law (output (T + 1)))
    (hno : OracleComp.evalWith (sumHandler ProbComp.unifOracle law) (output (T + 1)) true ≤
      1 / 3)
    (A : Proposer (Params.default K T).grid) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
      (run (Params.default K T) A (honestChallenger (Params.default K T))) true ≤ 2 / 5 := by
  have : NeZero (Params.default K T).grid := ⟨(Params.default_pos hK T).1.ne'⟩
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hrej := reject_ge law (Params.default K T) A (s := 2 / (100 * (K : ℝ)))
    (b := 5 / (100 * (K : ℝ))) (by gcongr; norm_num)
    (fun bits k h => default_abort_true_le hK T (law bits) k h)
    (fun bits k h => default_abort_false_le hK T (law bits) k h)
    (fun bits k h => default_verdict_true_le hK T law bits k h) (T + 1) [] A.init
    (honestChallenger (Params.default K T)).init
  change _ * rejectValue law (5 / (100 * (K : ℝ))) (T + 1) [] ≤
    ev law (run (Params.default K T) A (honestChallenger (Params.default K T))) false at hrej
  change ev law (run (Params.default K T) A (honestChallenger (Params.default K T))) true ≤ 2 / 5
  have hclose := hL (bestLaw law (5 / (100 * (K : ℝ))) T) (ENNReal.ofReal (5 / (100 * (K : ℝ))))
    (fun bits => closeTo_bestLaw law (by positivity) T bits) {false}
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at hclose
  change ev law (output (T + 1)) false ≤
    ev (bestLaw law (5 / (100 * (K : ℝ))) T) (output (T + 1)) false + _ at hclose
  rw [ev_output (bestLaw law (5 / (100 * (K : ℝ))) T),
    lawFrom_bestLaw law (5 / (100 * (K : ℝ))) T (T + 1) [] (by simp)] at hclose
  have hUtop : rejectValue law (5 / (100 * (K : ℝ))) (T + 1) [] ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (rejectValue_le_one law _ (T + 1) [])
  have hno' : ((ev law (output (T + 1))) true).toReal ≤ 1 / 3 := by
    simpa [ev] using ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) (by simp)) hno
  have hout := Probability.PMF.toReal_true_add_toReal_false (ev law (output (T + 1)))
  have hrun := Probability.PMF.toReal_true_add_toReal_false
    (ev law (run (Params.default K T) A (honestChallenger (Params.default K T))))
  have hclose' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hUtop,
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top⟩) hclose
  rw [ENNReal.toReal_add hUtop (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity),
    show (K : ℝ) * (5 / (100 * (K : ℝ))) = 1 / 20 by field_simp; ring] at hclose'
  have hrej' := ENNReal.toReal_mono (PMF.apply_ne_top _ _) hrej
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    toReal_one_sub_ofReal (by norm_num) (by norm_num),
    toReal_one_sub_ofReal (by positivity) ((div_le_one (by positivity)).2 (by linarith))]
    at hrej'
  have hbern : (99 / 100 : ℝ) ≤ (1 - 1 / (100 * ((T : ℝ) + 1))) ^ (T + 1) := by
    have h := one_add_mul_le_pow (a := -(1 / (100 * ((T : ℝ) + 1))))
      (by linarith [show (0 : ℝ) < 1 / (100 * ((T : ℝ) + 1)) by positivity,
        default_failure_lt_two T]) (T + 1)
    rw [Nat.cast_add, Nat.cast_one,
      show ((T : ℝ) + 1) * -(1 / (100 * ((T : ℝ) + 1))) = -(1 / 100) by field_simp,
      ← sub_eq_add_neg, ← sub_eq_add_neg] at h
    linarith
  have hU' : (37 / 60 : ℝ) ≤ (rejectValue law (5 / (100 * (K : ℝ))) (T + 1) []).toReal := by
    linarith
  rw [← ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _)
    (ENNReal.div_ne_top (by simp) (by simp))]
  nlinarith [hbern, hU', show ((2 / 5 : ℝ≥0∞)).toReal = 2 / 5 by simp]

end Cslib.Interactive.Debate
