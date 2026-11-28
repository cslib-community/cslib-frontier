/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridGame
public import CslibFrontier.Crypto.Protocols.MPC.DDHOT

/-!
# Batched oblivious transfer from sequential single transfers

`batchOTFunctionality k M` transfers `k` values of a type `M` in one invocation. This module
realizes it from `k` sequential invocations of the single 1-out-of-2 transfer `otFunctionality M`,
and bounds the semi-honest advantage against the protocol obtained by substituting a protocol for
the single transfer.

`seqBatchOT k M` runs in the hybrid model whose oracle is the single transfer (`otSpec M`, with the
ideal world `otWorld M`). It has `k` oracle rounds and no messages: in round `j` the sender submits
the pair `(x j false, x j true)` of its two values for transfer `j` and the receiver submits its
`j`-th choice bit; the receiver outputs the `k` answers and the sender outputs `()`. In the hybrid
model every party's view is determined by its input and output, so `seqBatchOT k M` is perfectly
private for every coalition, with the simulator `seqBatchOTSim` that replays the outputs as the
oracle answers (`perfectSemiHonestPrivate_seqBatchOT`).

Substituting a protocol `Sub` for the single transfer (`Protocol.compose`) gives a protocol for
`batchOTFunctionality k M` in the model of `Sub`. `semiHonestAdvantage_seqBatchOT_compose_le` bounds
its semi-honest advantage, for the composed simulator `composeSim`, by
`Composition.replacementBound`: the sum over the `k` transfers of the expected semi-honest advantage
of that transfer's distinguisher `Composition.roundDistinguisher` against `Sub`, where the
expectation is over the real executions of the earlier transfers. When every test has advantage at
most `ε` against `Sub`, the bound is `k * ε` (`semiHonestAdvantage_seqBatchOT_compose_le_mul`).

## Scope

These are concrete, per-instance statements in the style of
`CslibFrontier/Crypto/Protocols/MPC/Composition/Hybrid.lean`, and original library infrastructure;
no cited theorem is claimed. In particular:

* No efficiency of the composed protocol, of its simulator or of the round distinguishers is
  proved, and no asymptotic statement (`ProtocolFamily.SemiHonestSecure`) is derived.
* The hypothesis of `semiHonestAdvantage_seqBatchOT_compose_le_mul` ranges over all tests, so that
  theorem is a statement about statistically secure single transfers. For a computationally secure
  single transfer, such as the DDH transfer `ddhOTProbProtocol`, the bound to use is
  `semiHonestAdvantage_seqBatchOT_compose_le`, applied to the explicit round distinguishers.
* The value type `M` is arbitrary and the single transfer carries values of the same type `M`.
  `M := List Bool` gives `batchOTSpec k (List Bool)` from a single transfer of words; the DDH
  transfer carries group elements, and a transfer of words from a transfer of group elements is not
  provided here.
* The IKNP extension (`CslibFrontier/Crypto/Protocols/MPC/IKNP.lean`) takes
  `batchOTSpec κ (BitString m)` as its base-transfer oracle; `seqBatchOT κ (BitString m)` realizes
  that oracle from single transfers of `m`-bit strings. No statement about that composition is
  proved here.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.otSpec`, `Cslib.Crypto.Protocols.MPC.otWorld`: the single transfer as
  an oracle, with the input and output types of `otFunctionality`.
* `Cslib.Crypto.Protocols.MPC.seqOTSteps`: `k` sequential transfer rounds from a given state.
* `Cslib.Crypto.Protocols.MPC.seqBatchOT`, `Cslib.Crypto.Protocols.MPC.seqBatchOTSim`: the batched
  transfer protocol in the single-transfer hybrid model and its simulators.
* `Cslib.Crypto.Protocols.MPC.composeSeqBatchOTRoundEnv`: the environment of one transfer of one
  call, for an outer protocol whose batched transfers are run by `seqBatchOT`.

## Main results

* `Cslib.Crypto.Protocols.MPC.evalWith_seqBatchOT`: the execution of `seqBatchOT k M` is
  deterministic, with the outputs of `batchOTAnswer`.
* `Cslib.Crypto.Protocols.MPC.perfectSemiHonestPrivate_seqBatchOT`: perfect semi-honest privacy in
  the single-transfer hybrid model, for every coalition.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_seqBatchOT_compose_le`,
  `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_seqBatchOT_compose_le_mul`: the bounds on the
  semi-honest advantage after substituting a protocol for the single transfer.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_seqBatchOT_compose_le_sum_roundGame`: the bound
  by the sum over the `k` transfers of the advantage of one environment per transfer, which runs
  the earlier transfers itself.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_compose_seqBatchOT_compose_le_sum_roundGame`: the
  same for an outer protocol that calls the batched transfer, such as Yao's protocol: the advantage
  of the outer protocol with the ideal batched transfer plus one environment per transfer, which
  also runs the outer protocol up to its call.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped ENNReal

/-! ### The single transfer as an oracle -/

/-- One 1-out-of-2 oblivious transfer of a value in `M` as a two-party oracle: slot `0` (sender)
submits a pair of values and receives `Unit`; slot `1` (receiver) submits a choice bit and receives
the chosen value. Its query and answer parts are the input and output types `OTIn M` and `OTOut M`
of `otFunctionality M`, so that a protocol for `otFunctionality M` can be substituted for this
oracle by `Protocol.compose` as it stands; `batchOTSpec 1 M` is the same transfer with the values
and the bit indexed by `Fin 1`. -/
@[expose, reducible] def otSpec (M : Type) : MultiOracleSpec where
  Op := Unit
  arity _ := 2
  Query _ := OTIn M
  Answer _ := OTOut M

/-- The ideal memoryless world of `otSpec M`: the functionality `otFunctionality M`. -/
@[expose] def otWorld (M : Type) : MultiOracleWorld (otSpec M) :=
  fun _ => otFunctionality M

/-! ### Sequential transfer rounds -/

/-- The schedule of `k` sequential single transfers between the two parties, the sender in slot `0`
and the receiver in slot `1` of every transfer. -/
@[expose, reducible] def seqBatchOTSchedule (k : ℕ) (M : Type) : Schedule 2 (otSpec M) :=
  List.replicate k (.oracle () (Function.Embedding.refl (Fin 2)))

/-- `k` sequential single transfers from the states `State`: in round `j` party `s` submits
`query j s` of its initial state, and at the end party `s` outputs `output s` of its initial state
and of its `k` answers, in the order of the rounds. -/
@[expose] def seqOTSteps {M : Type} {Out : Fin 2 → Type} : (k : ℕ) → {State : Fin 2 → Type} →
    (Fin k → (s : Fin 2) → State s → OTIn M s) →
    ((s : Fin 2) → State s → (Fin k → OTOut M s) → Out s) →
    Steps State Out (seqBatchOTSchedule k M)
  | 0, _, _, output => .done fun s st => output s st Fin.elim0
  | k + 1, _, query, output =>
    Steps.oracle (spec := otSpec M) (op := ()) (parties := Function.Embedding.refl (Fin 2))
      (fun s st => query 0 s st)
      (seqOTSteps k (fun j s st => query j.succ s st.1)
        fun s st ans => output s st.1 (Fin.cons (st.2 s rfl) ans))

/-- The transcript that party `i` receives along `seqBatchOTSchedule k M` when its answer in round
`j` is `ans j`. -/
@[expose] def seqOTReceived {M : Type} : (k : ℕ) → (i : Fin 2) → (Fin k → OTOut M i) →
    (seqBatchOTSchedule k M).Received i
  | 0, _, _ => ()
  | k + 1, i, ans =>
    (fun s hs => (show s = i from hs) ▸ ans 0, seqOTReceived k i fun j => ans j.succ)

/-- In the ideal world `otWorld M` the rounds of `seqOTSteps` are deterministic: party `i` receives
in round `j` its part of `otOutputs` on the queries of round `j`. -/
theorem evalWith_seqOTSteps {M : Type} {Out : Fin 2 → Type} (k : ℕ) {State : Fin 2 → Type}
    (query : Fin k → (s : Fin 2) → State s → OTIn M s)
    (output : (s : Fin 2) → State s → (Fin k → OTOut M s) → Out s)
    (st : (i : Fin 2) → State i) :
    (seqOTSteps k query output).evalWith (otWorld M) st =
      PMF.pure fun i => seqOTReceived k i fun j => otOutputs (fun s => query j s (st s)) i := by
  induction k generalizing State with
  | zero => rfl
  | succ k ih =>
    rw [seqOTSteps, Steps.evalWith_oracle]
    simp only [otWorld, otFunctionality, Functionality.ofDeterministic, ProbComp.eval_pure,
      PMF.pure_bind, ih, PMF.pure_map]
    refine congrArg PMF.pure (funext fun i => Prod.ext (funext fun s => funext fun hs => ?_) rfl)
    subst hs
    rfl

/-- The output of party `i` after `seqOTSteps`, on the transcript in which its answers are `ans`,
is `output i` of its state and `ans`. -/
theorem outputAt_seqOTSteps {M : Type} {Out : Fin 2 → Type} (k : ℕ) {State : Fin 2 → Type}
    (query : Fin k → (s : Fin 2) → State s → OTIn M s)
    (output : (s : Fin 2) → State s → (Fin k → OTOut M s) → Out s)
    (i : Fin 2) (st : State i) (ans : Fin k → OTOut M i) :
    (seqOTSteps k query output).outputAt i st (seqOTReceived k i ans) = output i st ans := by
  induction k generalizing State with
  | zero => exact congrArg (output i st) (funext fun j => j.elim0)
  | succ k ih =>
    rw [seqOTSteps, seqOTReceived, Steps.outputAt, ih]
    exact congrArg (output i st) (Fin.cons_self_tail ans)

/-! ### The batched transfer protocol -/

/-- The query of party `s` in transfer `j` of the batched transfer: the sender submits the pair
`(x j false, x j true)` of its two values for transfer `j`, and the receiver its `j`-th choice
bit. As in `otOutputs`, the choice bit `true` selects the second value of the pair. -/
@[expose] def batchOTQueryAt {k : ℕ} {M : Type} (j : Fin k) (s : Fin 2) :
    (batchOTSpec k M).Query () s → OTIn M s :=
  Fin.cases (motive := fun s => (batchOTSpec k M).Query () s → OTIn M s)
    (fun x => (x j false, x j true)) (fun _ x => x j) s

/-- The answer of `batchOTSpec k M` to party `s` assembled from its answers in the `k` single
transfers. -/
@[expose] def batchOTAnswerOfRounds {k : ℕ} {M : Type} (s : Fin 2) :
    (Fin k → OTOut M s) → (batchOTSpec k M).Answer () s :=
  Fin.cases (motive := fun s => (Fin k → OTOut M s) → (batchOTSpec k M).Answer () s)
    (fun _ => ()) (fun _ ans => ans) s

/-- The answers to party `s` in the `k` single transfers, read off its answer from
`batchOTSpec k M`; the inverse of `batchOTAnswerOfRounds`. -/
@[expose] def batchOTRoundAnswers {k : ℕ} {M : Type} (s : Fin 2) :
    (batchOTSpec k M).Answer () s → Fin k → OTOut M s :=
  Fin.cases (motive := fun s => (batchOTSpec k M).Answer () s → Fin k → OTOut M s)
    (fun _ _ => ()) (fun _ y => y) s

@[simp] theorem batchOTAnswerOfRounds_batchOTRoundAnswers {k : ℕ} {M : Type} (s : Fin 2)
    (y : (batchOTSpec k M).Answer () s) :
    batchOTAnswerOfRounds s (batchOTRoundAnswers s y) = y := by
  induction s using Fin.cases <;> rfl

/-- The answers of the `k` single transfers on the queries `batchOTQueryAt` are the parts of the
batched answer `batchOTAnswer`. -/
theorem otOutputs_batchOTQueryAt {k : ℕ} {M : Type}
    (x : (s : Fin 2) → (batchOTSpec k M).Query () s) (i : Fin 2) :
    (fun j => otOutputs (fun s => batchOTQueryAt j s (x s)) i) =
      batchOTRoundAnswers i (batchOTAnswer x i) := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    funext j
    change (if x 1 j then x 0 j true else x 0 j false) = x 0 j (x 1 j)
    cases x 1 j <;> rfl

/-- **Batched oblivious transfer from `k` sequential single transfers**, in the hybrid model whose
oracle is the single transfer `otSpec M`. In round `j` the sender submits its two values for
transfer `j` and the receiver its `j`-th choice bit (`batchOTQueryAt`); the receiver outputs its
`k` answers and the sender outputs `()`. The protocol uses no coins and sends no messages. -/
@[expose] def seqBatchOT (k : ℕ) (M : Type) :
    Protocol 2 (otSpec M) (seqBatchOTSchedule k M) ((batchOTSpec k M).Query ()) (fun _ => Unit)
      ((batchOTSpec k M).Answer ()) where
  sampleCoins _ := pure ()
  steps := seqOTSteps k (fun j s st => batchOTQueryAt j s st.1)
    fun s _ ans => batchOTAnswerOfRounds s ans

/-- The simulators of `seqBatchOT k M`: each corrupted party's view consists of its input, the
empty coins and, as its answer in transfer `j`, the `j`-th part of its output. -/
@[expose] def seqBatchOTSim (k : ℕ) (M : Type) (I : Finset (Fin 2)) :
    CoalitionSimulator (seqBatchOTSchedule k M) ((batchOTSpec k M).Query ()) (fun _ => Unit)
      ((batchOTSpec k M).Answer ()) I :=
  fun x y => pure fun i => ⟨x i, (), seqOTReceived k i.val (batchOTRoundAnswers i.val (y i))⟩

/-- **The execution of `seqBatchOT k M` is deterministic and correct.** In the ideal world of the
single transfer, on the inputs `x` every party outputs its part of `batchOTAnswer x`, and its view
consists of its input and, as its answer in transfer `j`, the `j`-th part of its output. -/
theorem evalWith_seqBatchOT (k : ℕ) (M : Type) (x : (i : Fin 2) → (batchOTSpec k M).Query () i) :
    (seqBatchOT k M).evalWith (otWorld M) x =
      PMF.pure (fun i => ⟨x i, (), seqOTReceived k i (batchOTRoundAnswers i (batchOTAnswer x i))⟩,
        batchOTAnswer x) := by
  rw [Protocol.evalWith_eq]
  refine (congrArg _ (funext fun _ => ?_)).trans (PMF.bind_const _ _)
  simp only [seqBatchOT, evalWith_seqOTSteps, PMF.pure_map, otOutputs_batchOTQueryAt]
  exact congrArg PMF.pure (Prod.ext rfl (funext fun i =>
    (outputAt_seqOTSteps k _ _ i _ _).trans (batchOTAnswerOfRounds_batchOTRoundAnswers i _)))

/-- **`seqBatchOT k M` is perfectly semi-honest private in the single-transfer hybrid model**: for
every coalition, the simulator `seqBatchOTSim k M` on the coalition's inputs and outputs of
`batchOTFunctionality k M` has the joint distribution of the coalition's views and all outputs in
the execution with the ideal single transfer `otWorld M`. -/
theorem perfectSemiHonestPrivate_seqBatchOT (k : ℕ) (M : Type) :
    PerfectSemiHonestPrivate (seqBatchOT k M) (otWorld M) (batchOTFunctionality k M)
      (seqBatchOTSim k M) := by
  refine perfectSemiHonestPrivate_of_deterministic _ _ batchOTAnswer _ (fun I x => ?_)
    fun x r hr => ?_
  · rw [evalWith_seqBatchOT, PMF.pure_map]
    exact ProbComp.eval_pure _
  · rw [evalWith_seqBatchOT, PMF.support_pure, Set.mem_singleton_iff] at hr
    rw [hr]

/-! ### Substituting a protocol for the single transfer -/

variable {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}

/-- With both parties in their own slots, the slots of a coalition are the coalition. -/
private theorem subCoalition_refl (I : Finset (Fin 2)) :
    subCoalition (Function.Embedding.refl (Fin 2)) I = I :=
  Finset.ext fun _ => mem_subCoalition

/-- **The batched transfer over a substituted single transfer.** For every protocol `Sub` for the
single transfer in a world `W₂` and simulators `S₂` of `Sub`, the semi-honest advantage of `D`
against `(seqBatchOT k M).compose fun _ => Sub`, for `batchOTFunctionality k M` with the composed
simulator, is at most `Composition.replacementBound`: the sum over the `k` transfers of the expected
semi-honest advantage of that transfer's distinguisher `Composition.roundDistinguisher` against
`Sub`, for `otFunctionality M` with the simulator `S₂`, on that transfer's queries. The expectation
is over the real executions of `Sub` in the earlier transfers.

Nothing is assumed about `Sub`, `S₂` or `D`, and no efficiency of the round distinguishers is
claimed. -/
theorem semiHonestAdvantage_seqBatchOT_compose_le (k : ℕ) (M : Type)
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn M) Coins₂ (OTOut M))
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn M) Coins₂ (OTOut M) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → (batchOTSpec k M).Query () i)
    (D : ((i : I) → PartyView ((batchOTSpec k M).Query ())
        (Schedule.ComposedCoins (fun _ => Coins₂) (fun _ => Unit) (seqBatchOTSchedule k M))
        (Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k M)) i) ×
      ((i : Fin 2) → (batchOTSpec k M).Answer () i) → ProbComp Bool) :
    (semiHonestAdvantage ((seqBatchOT k M).compose fun _ => Sub) W₂ (batchOTFunctionality k M) I
        (composeSim (seqBatchOT k M) (seqBatchOTSim k M I) (fun _ => S₂)) x D : ℝ≥0∞) ≤
      replacementBound (otWorld M) W₂ (fun _ => Sub) (fun _ => S₂) I (seqBatchOT k M).steps
        (fun i => (x i, ()))
        (fun res => D (fun i : I => ⟨x i.val, ((), (res.1 i).1), (res.1 i).2⟩, res.2)) := by
  refine (semiHonestAdvantage_compose_le_replacementBound (seqBatchOT k M) (otWorld M) W₂
    (batchOTFunctionality k M) I (seqBatchOTSim k M I) (fun _ => Sub) (fun _ => S₂) x D).trans ?_
  rw [(perfectSemiHonestPrivate_seqBatchOT k M).semiHonestAdvantage_eq_zero, ENNReal.coe_zero,
    zero_add, tsum_eq_single (fun _ => ()) fun c hc => (hc rfl).elim]
  exact mul_le_of_le_one_left' (PMF.coe_le_one _ _)

/-- `k` sequential transfers have `k` oracle rounds. -/
@[simp] theorem oracleRounds_seqBatchOTSchedule (k : ℕ) (M : Type) :
    (seqBatchOTSchedule k M).oracleRounds = k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (· + 1) ih

/-- **The batched transfer over a substituted single transfer, with one environment per
transfer.** For every protocol `Sub` for the single transfer in a world `W₂` and simulators `S₂` of
`Sub`, the semi-honest advantage of `D` against `(seqBatchOT k M).compose fun _ => Sub`, for
`batchOTFunctionality k M` with the composed simulator, is at most the sum over the transfers
`j < k` of the advantage of the environment `composeRoundEnv` of hop `j` between the ideal game of
transfer `j`, for `otFunctionality M` with the simulator `S₂`, and its real game with `Sub`. The
environment runs the transfers before `j` with `Sub` itself and its guessing stage simulates the
transfers after `j` with `S₂`, so each summand is the absolute difference of two acceptance
probabilities of one environment; in `semiHonestAdvantage_seqBatchOT_compose_le` the absolute value
is inside the expectation over the earlier transfers.

Nothing is assumed about `Sub`, `S₂` or `D`, and no efficiency of the environments is claimed. -/
theorem semiHonestAdvantage_seqBatchOT_compose_le_sum_roundGame (k : ℕ) (M : Type)
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn M) Coins₂ (OTOut M))
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn M) Coins₂ (OTOut M) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → (batchOTSpec k M).Query () i)
    (D : ((i : I) → PartyView ((batchOTSpec k M).Query ())
        (Schedule.ComposedCoins (fun _ => Coins₂) (fun _ => Unit) (seqBatchOTSchedule k M))
        (Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k M)) i) ×
      ((i : Fin 2) → (batchOTSpec k M).Answer () i) → ProbComp Bool) :
    semiHonestAdvantage ((seqBatchOT k M).compose fun _ => Sub) W₂ (batchOTFunctionality k M) I
        (composeSim (seqBatchOT k M) (seqBatchOTSim k M I) (fun _ => S₂)) x D ≤
      ∑ j ∈ Finset.range k,
        Game.advantage
          ((composeRoundEnv (seqBatchOT k M) (otWorld M) W₂ (fun _ => Sub) (fun _ => S₂) I x D
            j).bind (roundGame fun op J q => ProbComp.eval (idealJoint (otWorld M op) J (S₂ J) q)))
          ((composeRoundEnv (seqBatchOT k M) (otWorld M) W₂ (fun _ => Sub) (fun _ => S₂) I x D
            j).bind (roundGame fun _ J q => Sub.realJoint W₂ J q)) := by
  simpa only [(perfectSemiHonestPrivate_seqBatchOT k M).semiHonestAdvantage_eq_zero, zero_add,
    oracleRounds_seqBatchOTSchedule] using
    semiHonestAdvantage_compose_le_sum_roundGame (seqBatchOT k M) (otWorld M) W₂
      (fun _ => Sub) (fun _ => S₂) I x D (batchOTFunctionality k M) (seqBatchOTSim k M)

/-- **The environment of transfer `j` of call `i`**, for an outer protocol `P` that calls the
batched transfer `batchOTSpec k M`, with every call run by `seqBatchOT k M` over a protocol `Sub`
for the single transfer. It samples the coins of `P`, runs `P` up to its call `i` with the earlier
calls run by `seqBatchOT k M` over `Sub` (`composeRoundEnv` of `P`), then runs the transfers before
`j` of call `i` with `Sub` and stops at transfer `j` (`composeRoundEnv` of `seqBatchOT k M` on the
challenged call). The guessing stage simulates the later transfers with `S₂` and the later calls
with `seqBatchOTSim k M` and `S₂`, and runs `D`. -/
@[expose] noncomputable def composeSeqBatchOTRoundEnv {m : ℕ} (k : ℕ) (M : Type)
    {sc₁ : Schedule m (batchOTSpec k M)} {In Coins₁ Out : Fin m → Type}
    (P : Protocol m (batchOTSpec k M) sc₁ In Coins₁ Out)
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn M) Coins₂ (OTOut M))
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn M) Coins₂ (OTOut M) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins (fun _ => Coins₂) (fun _ => Unit)
            (seqBatchOTSchedule k M)) Coins₁ sc₁)
        (Schedule.compose
          (fun _ => Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k M)) sc₁) i) ×
      ((i : Fin m) → Out i) → ProbComp Bool) (i j : ℕ) :
    PMF (Bool ⊕ RoundChallenge (spec₁ := otSpec M) (fun _ => sc₂) (fun _ => Coins₂)) :=
  (composeRoundEnv P (batchOTWorld k M) W₂ (fun _ => (seqBatchOT k M).compose fun _ => Sub)
    (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂)) I x D i).bind
      (Sum.elim (fun b => PMF.pure (Sum.inl b)) fun c =>
        composeRoundEnv (seqBatchOT k M) (otWorld M) W₂ (fun _ => Sub) (fun _ => S₂)
          c.coalition c.query c.guess j)

/-- **An outer protocol over the batched transfer run by sequential single transfers, with one
environment per transfer.** Let `P` be any protocol that calls the batched transfer
`batchOTSpec k M`, such as Yao's protocol, with every call run by `seqBatchOT k M` over a protocol
`Sub` for the single transfer in a world `W₂`. The semi-honest advantage of `D` against the
composed protocol, with the simulator composed from `S₁`, `seqBatchOTSim k M` and simulators `S₂`
of `Sub`, is at most the advantage of `composeDistinguisher` against `P` with the ideal batched
transfer, plus the sum over the calls `i` of `P` and the transfers `j < k` of the advantage of the
environment `composeSeqBatchOTRoundEnv` of transfer `j` of call `i` between the ideal game of that
transfer, for `otFunctionality M` with `S₂`, and its real game with `Sub`. Every summand is the
absolute difference of two acceptance probabilities of one environment, which samples the coins of
`P` and runs the earlier calls and transfers itself.

Nothing is assumed about `P`, `Sub`, the simulators or `D`, and no efficiency of the environments
is claimed. -/
theorem semiHonestAdvantage_compose_seqBatchOT_compose_le_sum_roundGame {m : ℕ} (k : ℕ)
    (M : Type) {sc₁ : Schedule m (batchOTSpec k M)} {In Coins₁ Out : Fin m → Type}
    (P : Protocol m (batchOTSpec k M) sc₁ In Coins₁ Out)
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn M) Coins₂ (OTOut M))
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn M) Coins₂ (OTOut M) J)
    (f : Functionality m In Out)
    (S₁ : (I : Finset (Fin m)) → CoalitionSimulator sc₁ In Coins₁ Out I)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins (fun _ => Coins₂) (fun _ => Unit)
            (seqBatchOTSchedule k M)) Coins₁ sc₁)
        (Schedule.compose
          (fun _ => Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k M)) sc₁) i) ×
      ((i : Fin m) → Out i) → ProbComp Bool) :
    semiHonestAdvantage (P.compose fun _ => (seqBatchOT k M).compose fun _ => Sub) W₂ f I
        (composeSim P (S₁ I)
          (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂))) x D ≤
      semiHonestAdvantage P (batchOTWorld k M) f I (S₁ I) x
          (composeDistinguisher P
            (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂)) I x D) +
        ∑ i ∈ Finset.range sc₁.oracleRounds, ∑ j ∈ Finset.range k,
          Game.advantage
            ((composeSeqBatchOTRoundEnv k M P W₂ Sub S₂ I x D i j).bind
              (roundGame fun op J q => ProbComp.eval (idealJoint (otWorld M op) J (S₂ J) q)))
            ((composeSeqBatchOTRoundEnv k M P W₂ Sub S₂ I x D i j).bind
              (roundGame fun _ J q => Sub.realJoint W₂ J q)) := by
  refine (semiHonestAdvantage_compose_le_sum_roundGame P (batchOTWorld k M) W₂
    (fun _ => (seqBatchOT k M).compose fun _ => Sub)
    (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂)) I x D f
    S₁).trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_))
  have h := advantage_bind_compose_le_add_sum_roundGame
    (composeRoundEnv P (batchOTWorld k M) W₂ (fun _ => (seqBatchOT k M).compose fun _ => Sub)
      (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J) (fun _ => S₂)) I x D i)
    (fun _ => seqBatchOT k M) (fun _ => otWorld M) (fun _ => W₂)
    (fun _ => batchOTFunctionality k M) (fun _ => seqBatchOTSim k M) (fun _ _ => Sub)
    (fun _ _ => S₂) (fun c => c.coalition) (fun c => c.query) (fun c => c.guess) k
    (fun _ => (oracleRounds_seqBatchOTSchedule k M).le)
  have h₀ (c : RoundChallenge (spec₁ := batchOTSpec k M)
      (fun _ => Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k M))
      (fun _ => Schedule.ComposedCoins (fun _ => Coins₂) (fun _ => Unit)
        (seqBatchOTSchedule k M))) :=
    perfectSemiHonestPrivate_seqBatchOT k M c.coalition c.query
  simp only [h₀, Game.advantage_self, zero_add] at h
  simp only [composeSeqBatchOTRoundEnv, bind_elim_bind_roundGame]
  exact h

/-- When every test has semi-honest advantage at most `ε` against `Sub` for the coalition `I`, the
hybrid bound of `k` sequential transfers is at most `k * ε`. -/
theorem replacementBound_seqOTSteps_le {M : Type} {Out : Fin 2 → Type}
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn M) Coins₂ (OTOut M))
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn M) Coins₂ (OTOut M) J)
    (I : Finset (Fin 2)) (ε : ℝ≥0∞)
    (hε : ∀ q D, (semiHonestAdvantage Sub W₂ (otFunctionality M) I (S₂ I) q D : ℝ≥0∞) ≤ ε)
    (k : ℕ) {State : Fin 2 → Type} (query : Fin k → (s : Fin 2) → State s → OTIn M s)
    (output : (s : Fin 2) → State s → (Fin k → OTOut M s) → Out s) (st : (i : Fin 2) → State i)
    (D : ((i : I) → Schedule.SubCoins (fun _ => Coins₂) (seqBatchOTSchedule k M) i.val ×
        Schedule.Received (Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k M)) i.val) ×
      ((i : Fin 2) → Out i) → ProbComp Bool) :
    replacementBound (otWorld M) W₂ (fun _ => Sub) (fun _ => S₂) I (seqOTSteps k query output) st
      D ≤ k * ε := by
  have hε' : ∀ J, J = I → ∀ q D,
      (semiHonestAdvantage Sub W₂ (otFunctionality M) J (S₂ J) q D : ℝ≥0∞) ≤ ε := by
    rintro J rfl
    exact hε
  induction k generalizing State with
  | zero =>
    rw [seqOTSteps, replacementBound]
    exact bot_le
  | succ k ih =>
    rw [seqOTSteps, replacementBound]
    calc _ ≤ ε + ∑' r, (Sub.realJoint W₂ (subCoalition (Function.Embedding.refl (Fin 2)) I)
            (fun s => query 0 s (st s))) r * (k * ε) :=
          add_le_add (hε' _ (subCoalition_refl I) _ _)
            (tsum_le_tsum fun r => mul_le_mul' le_rfl (ih _ _ _ _))
      _ = ((k + 1 : ℕ) : ℝ≥0∞) * ε := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, Nat.cast_succ, add_mul, one_mul,
            add_comm]

/-- **The batched transfer over a statistically secure single transfer.** If every test has
semi-honest advantage at most `ε` against `Sub`, for `otFunctionality M` with the simulator `S₂ I`
of the coalition `I`, on every pair of inputs, then every test has advantage at most `k * ε`
against `(seqBatchOT k M).compose fun _ => Sub`, for `batchOTFunctionality k M` with the composed
simulator. The hypothesis ranges over all tests, so it holds with a small `ε` only for a
statistically secure `Sub`. -/
theorem semiHonestAdvantage_seqBatchOT_compose_le_mul (k : ℕ) (M : Type)
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn M) Coins₂ (OTOut M))
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn M) Coins₂ (OTOut M) J)
    (I : Finset (Fin 2)) (ε : ℝ≥0∞)
    (hε : ∀ q D, (semiHonestAdvantage Sub W₂ (otFunctionality M) I (S₂ I) q D : ℝ≥0∞) ≤ ε)
    (x : (i : Fin 2) → (batchOTSpec k M).Query () i)
    (D : ((i : I) → PartyView ((batchOTSpec k M).Query ())
        (Schedule.ComposedCoins (fun _ => Coins₂) (fun _ => Unit) (seqBatchOTSchedule k M))
        (Schedule.compose (fun _ => sc₂) (seqBatchOTSchedule k M)) i) ×
      ((i : Fin 2) → (batchOTSpec k M).Answer () i) → ProbComp Bool) :
    (semiHonestAdvantage ((seqBatchOT k M).compose fun _ => Sub) W₂ (batchOTFunctionality k M) I
        (composeSim (seqBatchOT k M) (seqBatchOTSim k M I) (fun _ => S₂)) x D : ℝ≥0∞) ≤ k * ε :=
  (semiHonestAdvantage_seqBatchOT_compose_le k M W₂ Sub S₂ I x D).trans
    (replacementBound_seqOTSteps_le W₂ Sub S₂ I ε hε k _ _ _ _)

end Cslib.Crypto.Protocols.MPC
