/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Efficient
public import CslibFrontier.Crypto.Primitives.Garbling.Projective
public import CslibFrontier.Crypto.Protocols.MPC.Advantage
public import CslibFrontier.Crypto.Protocols.MPC.Asymptotic
public import CslibFrontier.Crypto.Protocols.MPC.BatchOT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind

/-!
# Yao's protocol over a garbling scheme in the ideal OT hybrid model

This module defines two word-level protocol families (`Cslib.Crypto.Protocols.MPC.ProtocolFamily`)
running Yao's two-party protocol [Yao1986] in the ideal `batchOTWorld` (`batchOTSpec`)
oblivious-transfer hybrid model (#6045), rather than composing with concrete 1-out-of-2
oblivious-transfer executions as in Protocol 2 of Lindell and Pinkas [LindellPinkas2009] (ePrint
2004/175, §4.2, p. 15) or §7.1 of Bellare, Hoang and Rogaway [BellareHoangRogaway2012] (p. 34,
Fig. 16):

* `Yao.oneSidedFamily G` (`Yao.oneSidedProtocol`, `Yao.oneSidedFunctionality`): the two-round
  one-sided output protocol of [BellareHoangRogaway2012], §7.1 (Fig. 16, p. 34), where party `0`
  (the garbler) outputs `[]` and party `1` (the evaluator) outputs `G.ev fn x`;
* `Yao.family G` (`Yao.protocol`, `Yao.functionality`): the three-round symmetric two-output
  protocol of [LindellPinkas2009], Protocol 2 (§4.2, p. 15), where the evaluator sends the decoded
  result back in a final message round so that both parties output `G.ev fn x`.

Both families are parameterized over any garbling scheme `G : Garbling.Scheme Fn` of
[BellareHoangRogaway2012] whose input encoding is `projectiveEncode`: projective in the sense of
§3.2 (p. 8), in the word layout of point-and-permute and half-gates garbling, with `2 n` tokens of
one width.

The public parameters `Yao.Params G` are a function description `fn`, known to both parties, and
the number `garblerLen` of its input bits held by the garbler (party `0`); the evaluator (party
`1`) holds the rest. At the security parameter `n`:

1. the garbler draws `G.coins n fn` fair coins, garbles `fn` to `(F, e, d)` with `G.gb`, and sends
   `F`, the tokens of its own input bits (`projectiveToken`) and `d` (`Yao.garblerMessage`);
2. one batched oblivious transfer gives the evaluator the tokens of its own input bits, from the
   pairs that the garbler offers (`Yao.garblerOffer`);
3. the evaluator evaluates `F` on all the tokens and decodes with `d` (`Yao.evaluatorOutput`): in
   `Yao.oneSidedProtocol` the garbler outputs `[]` and the evaluator outputs this decoding; in
   `Yao.protocol` the evaluator sends it back and both parties output it.

When `G` is correct, the evaluator's decoding equals `G.ev fn x` on the garbler's bits followed by
the evaluator's (`Yao.circuitInput`) in every run at a parameter `n ≥ 1`
(`Yao.oneSided_output_of_mem_support`, `Yao.output_of_mem_support`); the correctness of
`Garbling.Scheme.Correct` is stated for `k ≥ 1`.

`Yao.oneSidedEncoding G encFn` and `Yao.encoding G encFn` write the public parameters, inputs,
outputs and views as words, for the efficiency predicates of `ProtocolFamily.SemiHonestSecure`. A
corrupted garbler sees its input and coins (and, in `Yao.family`, the output returned in the final
round): `Yao.oneSidedGarblerSim` and `Yao.garblerSim` draw fresh coins, match the real joint law at
every `n ≥ 1` (`Yao.idealJoint_oneSidedGarblerSim`, `Yao.idealJoint_garblerSim`), and are PPT when
`G` computes its coin count in polynomial time (`Yao.isPPT_oneSidedGarblerSim`,
`Yao.isPPT_garblerSim`). So both families are semi-honest secure against the garbler in the
`batchOTWorld` hybrid (`Yao.hybridSemiHonestSecure_oneSided_garbler`,
`Yao.hybridSemiHonestSecure_garbler`), with no computational assumption. These are steps towards
Theorem 7 of Lindell and Pinkas (#6045), not that theorem or its Case 1 (p. 16). Case 1 simulates
the garbler's view of the oblivious-transfer protocol and then uses correctness (Claim 6); in the
hybrid model the garbler's view of the transfer is empty, so only the correctness step remains.

## Comparison with [LindellPinkas2009] and [BellareHoangRogaway2009 / 2012]

* **Oblivious transfer.** The transfers are the ideal `batchOTSpec`, one call for all of the
  evaluator's bits; Theorem 7 of [LindellPinkas2009] (p. 15) and Theorem 14 of
  [BellareHoangRogaway2012] (§7.1, p. 35) assume an oblivious transfer protocol, run for each bit.
  Composition with a protocol is not formalized here (#6045).
* **Notion.** `ProtocolFamily.SemiHonestSecure` has uniform PPT environments that choose the inputs
  after seeing the public parameters, drawn from a setup law; Definition 1 (§2.1, p. 5) of
  [LindellPinkas2009] quantifies over all inputs against non-uniform distinguishers, with no setup.
* **Garbling scheme.** Lindell and Pinkas garble with a specific double-encryption construction
  (§4.1, p. 12). Here the garbling scheme is a parameter, and the protocol uses only its
  algorithms and its encoding `projectiveEncode`, as in the modular construction of
  [BellareHoangRogaway2012], §7.1 (p. 34). Its correctness is that of `Garbling.Scheme.Correct`,
  from the security parameter `1` on.
* **Inputs and outputs.** The garbler holds the first `garblerLen` input bits and the evaluator the
  rest, where Lindell and Pinkas have `n` bits each. Outputs are words of any length; in
  `Yao.oneSidedFamily` party `0` outputs `[]` (as in [BellareHoangRogaway2012], §7.1, Fig. 16) and
  in `Yao.family` both parties output `G.ev fn x` (as in [LindellPinkas2009], Protocol 2).
* **Security parameter.** The function description is a public parameter drawn from a setup law,
  not the auxiliary input of a circuit for inputs of length `n`, and the garbling scheme runs at the
  security parameter `n`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Yao.Params`: the public parameters.
* `Cslib.Crypto.Protocols.MPC.Yao.oneSidedProtocol`,
  `Cslib.Crypto.Protocols.MPC.Yao.oneSidedFamily`: the one-sided protocol and protocol family, with
  schedule `Yao.oneSidedSchedule` and functionality `Yao.oneSidedFunctionality`.
* `Cslib.Crypto.Protocols.MPC.Yao.protocol`, `Cslib.Crypto.Protocols.MPC.Yao.family`: the
  two-output protocol and protocol family, with schedule `Yao.schedule` and functionality
  `Yao.functionality`.
* `Cslib.Crypto.Protocols.MPC.Yao.oneSidedGarblerView`,
  `Cslib.Crypto.Protocols.MPC.Yao.oneSidedEvaluatorView`,
  `Cslib.Crypto.Protocols.MPC.Yao.garblerView`,
  `Cslib.Crypto.Protocols.MPC.Yao.evaluatorView`: the parties' views.
* `Cslib.Crypto.Protocols.MPC.Yao.oneSidedEncoding`,
  `Cslib.Crypto.Protocols.MPC.Yao.encoding`: the machine encodings of the two families.
* `Cslib.Crypto.Protocols.MPC.Yao.oneSidedGarblerSim`,
  `Cslib.Crypto.Protocols.MPC.Yao.garblerSim`: the simulators for a corrupted garbler.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.oneSided_output_of_mem_support`,
  `Cslib.Crypto.Protocols.MPC.Yao.output_of_mem_support`: correctness.
* `Cslib.Crypto.Protocols.MPC.Yao.idealJoint_oneSidedGarblerSim`,
  `Cslib.Crypto.Protocols.MPC.Yao.isPPT_oneSidedGarblerSim`,
  `Cslib.Crypto.Protocols.MPC.Yao.idealJoint_garblerSim`,
  `Cslib.Crypto.Protocols.MPC.Yao.isPPT_garblerSim`: the garbler simulators are exact from `n = 1`
  on and PPT.
* `Cslib.Crypto.Protocols.MPC.Yao.hybridSemiHonestSecure_oneSided_garbler`,
  `Cslib.Crypto.Protocols.MPC.Yao.hybridSemiHonestSecure_garbler`: corrupted-garbler steps in the
  ideal `batchOTWorld` hybrid (#6045) towards Theorem 7 of [LindellPinkas2009].

## References

* [A. C. Yao, *How to Generate and Exchange Secrets*][Yao1986]
* [Y. Lindell, B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009], cited in the ePrint version 2004/175 of June 26, 2006:
  Definition 1 (§2.1, p. 5), §4.1 (p. 12), Protocol 2 and Theorem 7 (§4.2, p. 15), Case 1
  (p. 16).
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012],
  §3.2 (p. 8) and §7.1 (Fig. 16, p. 34; Theorem 14, p. 35).
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib.Crypto.Garbling Probability Turing.MultiTapeTM

variable {Fn : Type}

/-! ### The protocol -/

/-- The public parameters of Yao's protocol over the garbling scheme `G`: a function description
`fn`, known to both parties, and the number `garblerLen` of its input bits that the garbler holds,
the first ones. The evaluator holds the other `G.inLen fn - garblerLen`. -/
structure Params (G : Scheme Fn) where
  /-- The function description. -/
  fn : Fn
  /-- The number of input bits that the garbler holds. -/
  garblerLen : ℕ
  /-- The garbler holds at most all the input bits. -/
  garblerLen_le : garblerLen ≤ G.inLen fn

variable {G : Scheme Fn}

/-- The number of input bits that the evaluator holds. -/
abbrev Params.evaluatorLen (c : Params G) : ℕ := G.inLen c.fn - c.garblerLen

/-- The parties' inputs: `c.garblerLen` bits for the garbler (party `0`) and `c.evaluatorLen` bits
for the evaluator (party `1`). -/
abbrev Input (c : Params G) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) (BitString c.garblerLen)
    (fun _ => BitString c.evaluatorLen) i

/-- The parties' coins: the garbler's coin string for `Gb`; the evaluator uses none. -/
abbrev Coins : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) (List Bool) (fun _ => Unit) i

/-- The input of the function: the garbler's bits followed by the evaluator's. -/
@[expose] def circuitInput {c : Params G} (x : (i : Fin 2) → Input c i) : List Bool :=
  List.ofFn (x 0) ++ List.ofFn (x 1)

/-- The input of the function has `G.inLen c.fn` bits. -/
theorem length_circuitInput {c : Params G} (x : (i : Fin 2) → Input c i) :
    (circuitInput x).length = G.inLen c.fn := by
  have := c.garblerLen_le
  simp only [circuitInput, List.length_append, List.length_ofFn (f := x 0),
    List.length_ofFn (f := x 1), Params.evaluatorLen]; omega

/-- The garbler's message: the garbled function `F`, the tokens of the garbler's input bits and the
decoding information `d`. -/
@[ext] structure Message where
  /-- The garbled function `F`. -/
  fn : List Bool
  /-- The tokens of the garbler's input bits. -/
  labels : List (List Bool)
  /-- The decoding information `d`. -/
  decInfo : List Bool

/-- The schedule of the one-sided protocol: the garbler sends its message, and the parties run one
batched oblivious transfer of the tokens of the evaluator's input bits. -/
abbrev oneSidedSchedule (c : Params G) : Schedule 2 (batchOTSpec c.evaluatorLen (List Bool)) :=
  [.message 0 1 Message, .oracle () (Function.Embedding.refl (Fin 2))]

/-- The schedule of the two-output protocol: `oneSidedSchedule c` followed by the evaluator sending
the decoded output to the garbler. -/
abbrev schedule (c : Params G) : Schedule 2 (batchOTSpec c.evaluatorLen (List Bool)) :=
  [.message 0 1 Message, .oracle () (Function.Embedding.refl (Fin 2)),
    .message 1 0 (List Bool)]

/-- A party's local state after the oblivious transfer. -/
abbrev AfterTransfer (c : Params G) (i : Fin 2) : Type :=
  ((Input c i × Coins i) ×
      (Round.message (spec := batchOTSpec c.evaluatorLen (List Bool)) 0 1 Message).Received i) ×
    (Round.oracle (spec := batchOTSpec c.evaluatorLen (List Bool)) ()
      (Function.Embedding.refl (Fin 2))).Received i

/-- A party's final local state in `protocol`. -/
abbrev Final (c : Params G) (i : Fin 2) : Type :=
  AfterTransfer c i ×
    (Round.message (spec := batchOTSpec c.evaluatorLen (List Bool)) 1 0 (List Bool)).Received i

/-- The output tuple of the one-sided protocol for a decoded output `y`: `[]` for the garbler
(party `0`) and `y` for the evaluator (party `1`). -/
@[expose] def oneSidedOutputs (y : List Bool) : Fin 2 → List Bool :=
  fun i => Fin.cases (motive := fun _ => List Bool) [] (fun _ => y) i

variable (G)

/-- The one-sided functionality ([BellareHoangRogaway2012], §7.1, Fig. 16, p. 34): the garbler
outputs `[]` and the evaluator learns `G.ev c.fn` on the garbler's bits followed by the
evaluator's. -/
@[expose] def oneSidedFunctionality (c : Params G) :
    Functionality 2 (Input c) (fun _ => List Bool) :=
  .ofDeterministic fun x => oneSidedOutputs (G.ev c.fn (circuitInput x))

/-- The two-output functionality ([LindellPinkas2009], Protocol 2, §4.2, p. 15): both parties learn
`G.ev c.fn` on the garbler's bits followed by the evaluator's. -/
@[expose] def functionality (c : Params G) : Functionality 2 (Input c) (fun _ => List Bool) :=
  .ofDeterministic fun x _ => G.ev c.fn (circuitInput x)

/-- The garbler's message at parameter `n` on input `x₀` and coins `coins`: garble `c.fn` to
`(F, e, d)` and send `F`, the token of each bit of `x₀` and `d`. -/
@[expose] def garblerMessage (n : ℕ) (c : Params G) (x₀ : BitString c.garblerLen)
    (coins : List Bool) : Message :=
  let g := G.gb n c.fn coins
  ⟨g.fn, List.ofFn fun i => projectiveToken g.encInfo (G.inLen c.fn) i (x₀ i), g.decInfo⟩

/-- The garbler's offer to the oblivious transfer at parameter `n` with coins `coins`: both tokens
of each of the evaluator's input bits. -/
@[expose] def garblerOffer (n : ℕ) (c : Params G) (coins : List Bool) :
    Fin c.evaluatorLen → Bool → List Bool :=
  fun j b => projectiveToken (G.gb n c.fn coins).encInfo (G.inLen c.fn) (c.garblerLen + j) b

/-- The evaluator's output: evaluate `F` on the garbler's tokens followed by the evaluator's own
and decode with `d`, or the empty word if decoding fails. -/
@[expose] def evaluatorOutput (msg : Message) {ℓ : ℕ} (labels : Fin ℓ → List Bool) :
    List Bool :=
  (G.decode msg.decInfo (G.evalGarbled msg.fn (msg.labels ++ List.ofFn labels).flatten)).getD []

/-- The oblivious-transfer queries: the garbler offers both tokens of each of the evaluator's
input bits, and the evaluator chooses with its input bits. -/
@[expose] def transferQuery (n : ℕ) (c : Params G) (s : Fin 2)
    (st : (Input c s × Coins s) ×
      (Round.message (spec := batchOTSpec c.evaluatorLen (List Bool)) 0 1 Message).Received s) :
    (batchOTSpec c.evaluatorLen (List Bool)).Query () s :=
  Fin.cases
    (motive := fun s => (Input c s × Coins s) ×
      (Round.message (spec := batchOTSpec c.evaluatorLen (List Bool)) 0 1 Message).Received s →
        (batchOTSpec c.evaluatorLen (List Bool)).Query () s)
    (fun ((_, coins), _) => garblerOffer G n c coins)
    (fun _ ((x₁, _), _) => x₁) s st

/-- The parties' outputs in `oneSidedProtocol`: `[]` for the garbler and the decoded output for the
evaluator. -/
@[expose] def oneSidedFinalOutput (c : Params G) (i : Fin 2) (st : AfterTransfer c i) : List Bool :=
  Fin.cases (motive := fun i => AfterTransfer c i → List Bool)
    (fun _ => [])
    (fun j ((_, msg), ot) => evaluatorOutput G (msg (Fin.fin_one_eq_zero j ▸ rfl))
      (ot 1 (Fin.fin_one_eq_zero j ▸ rfl)))
    i st

/-- The parties' outputs in `protocol`: the garbler outputs what the evaluator sent, and the
evaluator its decoding. -/
@[expose] def finalOutput (c : Params G) (i : Fin 2) (st : Final c i) : List Bool :=
  Fin.cases (motive := fun i => Final c i → List Bool)
    (fun (_, y) => y rfl)
    (fun j (((_, msg), ot), _) => evaluatorOutput G (msg (Fin.fin_one_eq_zero j ▸ rfl))
      (ot 1 (Fin.fin_one_eq_zero j ▸ rfl)))
    i st

/-- **One-sided Yao's protocol** over the garbling scheme `G` at parameter `n`
([BellareHoangRogaway2012], §7.1, Fig. 16, p. 34, in the ideal `batchOTSpec` oblivious-transfer
hybrid): the garbler garbles `c.fn` with `G.coins n c.fn` fair coins and sends `F`, the tokens of
its input bits and `d`; one batched oblivious transfer gives the evaluator the tokens of its input
bits; the garbler outputs `[]`, and the evaluator evaluates and decodes. -/
@[expose] noncomputable def oneSidedProtocol (n : ℕ) (c : Params G) :
    Protocol 2 (batchOTSpec c.evaluatorLen (List Bool)) (oneSidedSchedule c) (Input c) Coins
      (fun _ => List Bool) where
  sampleCoins i := Fin.cases (motive := fun i => ProbComp (Coins i))
    (BitString.sampleList (G.coins n c.fn)) (fun _ => pure ()) i
  steps := .message (fun (x₀, coins) => garblerMessage G n c x₀ coins)
    (.oracle (transferQuery G n c) (.done (oneSidedFinalOutput G c)))

/-- **One-sided Yao's protocol as a protocol family** over the garbling scheme `G`: at parameter
`n` and public parameters `c`, `Yao.oneSidedProtocol G n c` in the hybrid model of the batched
oblivious transfer `batchOTSpec c.evaluatorLen (List Bool)`, computing
`Yao.oneSidedFunctionality G c`. -/
noncomputable abbrev oneSidedFamily : ProtocolFamily 2 where
  Desc := Params G
  spec _ c := batchOTSpec c.evaluatorLen (List Bool)
  sc _ c := oneSidedSchedule c
  In _ c := Input c
  Coins _ _ := Coins
  Out _ _ _ := List Bool
  protocol n c := oneSidedProtocol G n c
  world _ c := batchOTWorld c.evaluatorLen (List Bool)
  functionality _ c := oneSidedFunctionality G c

/-- **Yao's protocol** over the garbling scheme `G` at parameter `n` (Protocol 2 of
[LindellPinkas2009], §4.2, p. 15, over a projective garbling scheme and one ideal batched
oblivious transfer): the garbler garbles `c.fn` with `G.coins n c.fn` fair coins and sends `F`,
the tokens of its input bits and `d`; one batched oblivious transfer gives the evaluator the tokens
of its input bits; the evaluator evaluates and decodes, sends the result to the garbler, and both
output it. -/
@[expose] noncomputable def protocol (n : ℕ) (c : Params G) :
    Protocol 2 (batchOTSpec c.evaluatorLen (List Bool)) (schedule c) (Input c) Coins
      (fun _ => List Bool) where
  sampleCoins := (oneSidedProtocol G n c).sampleCoins
  steps := .message (fun (x₀, coins) => garblerMessage G n c x₀ coins)
    (.oracle (transferQuery G n c)
      (.message (fun (((_, msg), ot) : AfterTransfer c 1) => evaluatorOutput G (msg rfl) (ot 1 rfl))
        (.done (finalOutput G c))))

/-- **Yao's protocol as a protocol family** over the garbling scheme `G`: at parameter `n` and
public parameters `c`, `Yao.protocol G n c` in the hybrid model of the batched oblivious transfer
`batchOTSpec c.evaluatorLen (List Bool)`, computing `Yao.functionality G c`. -/
noncomputable abbrev family : ProtocolFamily 2 where
  Desc := Params G
  spec _ c := batchOTSpec c.evaluatorLen (List Bool)
  sc _ c := schedule c
  In _ c := Input c
  Coins _ _ := Coins
  Out _ _ _ := List Bool
  protocol n c := protocol G n c
  world _ c := batchOTWorld c.evaluatorLen (List Bool)
  functionality _ c := functionality G c

/-! ### Views and runs -/

variable {G}

/-- The garbler's view in `oneSidedProtocol`, from its input `x₀` and its coins: it receives
nothing. -/
@[expose] def oneSidedGarblerView (c : Params G) (x₀ : BitString c.garblerLen)
    (coins : List Bool) : PartyView (Input c) Coins (oneSidedSchedule c) 0 where
  input := x₀
  coins := coins
  received :=
    (fun h => absurd h (by decide),
      (fun s hs => Fin.cases
        (motive := fun s => s = 0 → (batchOTSpec c.evaluatorLen (List Bool)).Answer () s)
        (fun _ => ()) (fun j hj => absurd hj (Fin.succ_ne_zero j)) s hs, ()))

/-- The evaluator's view in `oneSidedProtocol`, from its input `x₁`, the garbler's message and the
tokens that the oblivious transfer delivers. -/
@[expose] def oneSidedEvaluatorView (c : Params G) (x₁ : BitString c.evaluatorLen) (msg : Message)
    (labels : Fin c.evaluatorLen → List Bool) :
    PartyView (Input c) Coins (oneSidedSchedule c) 1 where
  input := x₁
  coins := ()
  received :=
    (fun _ => msg,
      (fun s _ => Fin.cases
        (motive := fun s => (batchOTSpec c.evaluatorLen (List Bool)).Answer () s)
        () (fun _ => labels) s, ()))

/-- The garbler's view in `protocol`, from its input `x₀`, its coins and the output `y` that the
evaluator sends: it receives nothing else. -/
@[expose] def garblerView (c : Params G) (x₀ : BitString c.garblerLen) (coins : List Bool)
    (y : List Bool) : PartyView (Input c) Coins (schedule c) 0 where
  input := x₀
  coins := coins
  received := Schedule.Received.append (sc₁ := oneSidedSchedule c)
    (oneSidedGarblerView c x₀ coins).received (fun _ => y, ())

/-- The evaluator's view in `protocol`, from its input `x₁`, the garbler's message and the tokens
that the oblivious transfer delivers; it sends the last message and receives nothing in that
round. -/
@[expose] def evaluatorView (c : Params G) (x₁ : BitString c.evaluatorLen) (msg : Message)
    (labels : Fin c.evaluatorLen → List Bool) : PartyView (Input c) Coins (schedule c) 1 where
  input := x₁
  coins := ()
  received := Schedule.Received.append (sc₁ := oneSidedSchedule c)
    (oneSidedEvaluatorView c x₁ msg labels).received (fun h => absurd h (by decide), ())

/-- The coins of a run as a coin tuple. -/
private def coinTuple (coins : List Bool) : (i : Fin 2) → Coins i :=
  fun i => Fin.cases (motive := fun i => Coins i) coins (fun _ => ()) i

variable (G)

/-- The evaluator's decoded output in a run on inputs `x` with the garbler's coins `coins`. -/
@[expose] def runOutput (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) : List Bool :=
  evaluatorOutput G (garblerMessage G n c (x 0) coins) fun j => garblerOffer G n c coins j (x 1 j)

/-- The transcripts that the parties receive in `oneSidedProtocol` on inputs `x` with the garbler's
coins `coins`. -/
private def oneSidedReceived (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) (i : Fin 2) : (oneSidedSchedule c).Received i :=
  (Round.deliverMessage (garblerMessage G n c (x 0) coins) i,
    Round.deliverOracle (spec := batchOTSpec c.evaluatorLen (List Bool)) (op := ())
      (Function.Embedding.refl (Fin 2))
      (batchOTAnswer fun s => transferQuery G n c s ((x s, coinTuple coins s),
        Round.deliverMessage (garblerMessage G n c (x 0) coins) s)) i,
    ())

/-- The transcripts that the parties receive in `protocol` on inputs `x` with the garbler's coins
`coins`. -/
private def received (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i) (coins : List Bool)
    (i : Fin 2) : (schedule c).Received i :=
  Schedule.Received.append (sc₁ := oneSidedSchedule c) (oneSidedReceived G n c x coins i)
    (Round.deliverMessage (runOutput G n c x coins) i, ())

/-- Once the coins are fixed, `oneSidedProtocol`'s steps are deterministic. -/
private theorem evalWith_oneSidedSteps (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) :
    (oneSidedProtocol G n c).steps.evalWith (batchOTWorld c.evaluatorLen (List Bool))
        (fun i => (x i, coinTuple coins i)) =
      PMF.pure (oneSidedReceived G n c x coins) := by
  refine (Steps.evalWith_message _ _ _ _).trans
    ((congrArg (PMF.map _) (Steps.evalWith_oracle _ _ _ _)).trans ?_)
  simp only [pmf_norm, Steps.evalWith_done, batchOTWorld]; rfl

/-- Once the coins are fixed, `protocol`'s steps are deterministic. -/
private theorem evalWith_steps (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) :
    (protocol G n c).steps.evalWith (batchOTWorld c.evaluatorLen (List Bool))
        (fun i => (x i, coinTuple coins i)) =
      PMF.pure (received G n c x coins) := by
  refine (Steps.evalWith_message _ _ _ _).trans
    ((congrArg (PMF.map _) (Steps.evalWith_oracle _ _ _ _)).trans ?_)
  simp only [pmf_norm, Steps.evalWith_message, Steps.evalWith_done, batchOTWorld]; rfl

/-- Independent coin sampling draws the garbler's coin string. -/
private theorem eval_pi_sampleCoins (n : ℕ) (c : Params G) :
    ProbComp.eval (OracleComp.pi (oneSidedProtocol G n c).sampleCoins) =
      (BitString.uniformList (G.coins n c.fn)).map coinTuple := by
  have h1 : ProbComp.eval ((oneSidedProtocol G n c).sampleCoins (Fin.succ 0)) =
      PMF.pure (show Coins (Fin.succ 0) from ()) := rfl
  simp only [OracleComp.pi_succ, OracleComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, h1]
  erw [PMF.pure_bind]
  simp only [PMF.pure_map]
  rw [← PMF.bind_pure_comp]
  exact congrArg₂ PMF.bind (BitString.eval_sampleList _)
    (funext fun _ => congrArg PMF.pure (funext fun i => by fin_cases i <;> rfl))

/-- The views and outputs of a run of `oneSidedProtocol`, from the garbler's coins. -/
private theorem evalWith_oneSidedProtocol (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i) :
    (oneSidedProtocol G n c).evalWith (batchOTWorld c.evaluatorLen (List Bool)) x =
      (BitString.uniformList (G.coins n c.fn)).map fun coins =>
        (fun i => ⟨x i, coinTuple coins i, oneSidedReceived G n c x coins i⟩,
          oneSidedOutputs (runOutput G n c x coins)) := by
  rw [Protocol.evalWith_eq, eval_pi_sampleCoins, PMF.bind_map, ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun coins => ?_)
  simp only [Function.comp_apply, evalWith_oneSidedSteps, PMF.pure_map]
  exact congrArg PMF.pure (Prod.ext rfl (funext fun i => by fin_cases i <;> rfl))

/-- The views and outputs of a run of `protocol`, from the garbler's coins. -/
private theorem evalWith_protocol (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i) :
    (protocol G n c).evalWith (batchOTWorld c.evaluatorLen (List Bool)) x =
      (BitString.uniformList (G.coins n c.fn)).map fun coins =>
        (fun i => ⟨x i, coinTuple coins i, received G n c x coins i⟩,
          fun _ => runOutput G n c x coins) := by
  rw [Protocol.evalWith_eq, show (protocol G n c).sampleCoins =
    (oneSidedProtocol G n c).sampleCoins from rfl, eval_pi_sampleCoins, PMF.bind_map,
    ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun coins => ?_)
  simp only [Function.comp_apply, evalWith_steps, PMF.pure_map]
  exact congrArg PMF.pure (Prod.ext rfl (funext fun i => by fin_cases i <;> rfl))

/-- The garbler's view in a run of `oneSidedProtocol`. -/
private theorem oneSidedReceived_zero (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) :
    (⟨x 0, coinTuple coins 0, oneSidedReceived G n c x coins 0⟩ :
        PartyView (Input c) Coins (oneSidedSchedule c) 0) =
      oneSidedGarblerView c (x 0) coins :=
  PartyView.ext rfl rfl (Prod.ext (Round.received_message_eq_of_ne (by decide) _ _)
    (Prod.ext (Round.received_oracle_ext fun s hs => by fin_cases s <;> [rfl; simp at hs])
      rfl))

/-- The evaluator's view in a run of `oneSidedProtocol`. -/
private theorem oneSidedReceived_one (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) :
    (⟨x 1, coinTuple coins 1, oneSidedReceived G n c x coins 1⟩ :
        PartyView (Input c) Coins (oneSidedSchedule c) 1) =
      oneSidedEvaluatorView c (x 1) (garblerMessage G n c (x 0) coins)
        (fun j => garblerOffer G n c coins j (x 1 j)) :=
  PartyView.ext rfl rfl (Prod.ext rfl
    (Prod.ext (Round.received_oracle_ext fun s hs => by fin_cases s <;> [simp at hs; rfl])
      rfl))

/-- The garbler's view in a run of `protocol`. -/
private theorem received_zero (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) :
    (⟨x 0, coinTuple coins 0, received G n c x coins 0⟩ :
        PartyView (Input c) Coins (schedule c) 0) =
      garblerView c (x 0) coins (runOutput G n c x coins) := by
  have h0 : oneSidedReceived G n c x coins 0 = (oneSidedGarblerView c (x 0) coins).received :=
    congrArg PartyView.received (oneSidedReceived_zero G n c x coins)
  exact PartyView.ext rfl rfl (by simp only [received, garblerView, h0]; rfl)

/-- The evaluator's view in a run of `protocol`. -/
private theorem received_one (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) :
    (⟨x 1, coinTuple coins 1, received G n c x coins 1⟩ :
        PartyView (Input c) Coins (schedule c) 1) =
      evaluatorView c (x 1) (garblerMessage G n c (x 0) coins)
        (fun j => garblerOffer G n c coins j (x 1 j)) := by
  have h1 : oneSidedReceived G n c x coins 1 =
      (oneSidedEvaluatorView c (x 1) (garblerMessage G n c (x 0) coins)
        (fun j => garblerOffer G n c coins j (x 1 j))).received :=
    congrArg PartyView.received (oneSidedReceived_one G n c x coins)
  have h2 : Round.deliverMessage (spec := batchOTSpec c.evaluatorLen (List Bool))
      (sender := (1 : Fin 2)) (receiver := (0 : Fin 2)) (runOutput G n c x coins) 1 =
      fun h => absurd h (by decide) := Round.received_message_eq_of_ne (by decide) _ _
  exact PartyView.ext rfl rfl (by simp only [received, evaluatorView, h1, h2])

/-- Both parties' views in a run of `oneSidedProtocol` on inputs `x` with the garbler's coins
`coins`: `oneSidedGarblerView` for party `0` and `oneSidedEvaluatorView` for party `1`. -/
@[expose] def oneSidedViews (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) (i : Fin 2) : PartyView (Input c) Coins (oneSidedSchedule c) i :=
  Fin.cases (motive := fun i => PartyView (Input c) Coins (oneSidedSchedule c) i)
    (oneSidedGarblerView c (x 0) coins)
    (Fin.cases (motive := fun j => PartyView (Input c) Coins (oneSidedSchedule c) j.succ)
      (oneSidedEvaluatorView c (x 1) (garblerMessage G n c (x 0) coins)
        (fun j => garblerOffer G n c coins j (x 1 j))) fun k => k.elim0) i

/-- The real joint distribution for any static coalition `I` in `oneSidedProtocol`, from the
garbler's coins. -/
theorem realJoint_oneSided (I : Finset (Fin 2)) (n : ℕ) (c : Params G)
    (x : (i : Fin 2) → Input c i) :
    (oneSidedProtocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) I x =
      (BitString.uniformList (G.coins n c.fn)).map fun coins =>
        (I.restrict (oneSidedViews G n c x coins),
          oneSidedOutputs (runOutput G n c x coins)) := by
  rw [Protocol.realJoint, evalWith_oneSidedProtocol, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun coins => Prod.ext (funext fun ⟨i, _⟩ => ?_) rfl)
  fin_cases i
  · exact oneSidedReceived_zero G n c x coins
  · exact oneSidedReceived_one G n c x coins

/-- The real joint distribution for a corrupted garbler in `oneSidedProtocol`: fresh coins and
nothing received, paired with `[]` for the garbler and the evaluator's decoding for the
evaluator. -/
theorem realJoint_oneSided_garbler (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i) :
    (oneSidedProtocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {0} x =
      (BitString.uniformList (G.coins n c.fn)).map fun coins =>
        (singletonView (oneSidedGarblerView c (x 0) coins),
          oneSidedOutputs (runOutput G n c x coins)) := by
  simp only [realJoint_oneSided, restrict_singleton]; rfl

/-- The real joint distribution for a corrupted evaluator in `oneSidedProtocol`: its view holds the
garbler's message and the tokens of its own bits, paired with `[]` for the garbler and its decoding
for the evaluator. -/
theorem realJoint_oneSided_evaluator (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i) :
    (oneSidedProtocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {1} x =
      (BitString.uniformList (G.coins n c.fn)).map fun coins =>
        (singletonView (oneSidedEvaluatorView c (x 1) (garblerMessage G n c (x 0) coins)
            (fun j => garblerOffer G n c coins j (x 1 j))),
          oneSidedOutputs (runOutput G n c x coins)) := by
  simp only [realJoint_oneSided, restrict_singleton, oneSidedViews]; rfl

/-- The real joint distribution for a corrupted garbler in `protocol`: fresh coins, and the
evaluator's decoding as the message of the last round and as both outputs. -/
theorem realJoint_garbler (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i) :
    (protocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {0} x =
      (BitString.uniformList (G.coins n c.fn)).map fun coins =>
        (singletonView (garblerView c (x 0) coins (runOutput G n c x coins)),
          fun _ => runOutput G n c x coins) := by
  rw [Protocol.realJoint, evalWith_protocol, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun coins => ?_)
  simp only [Function.comp_apply, Prod.map, id, restrict_singleton, received_zero]

/-- The real joint distribution for a corrupted evaluator in `protocol`: its view holds the
garbler's message and the tokens of its own bits, and both outputs are its decoding. -/
theorem realJoint_evaluator (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i) :
    (protocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {1} x =
      (BitString.uniformList (G.coins n c.fn)).map fun coins =>
        (singletonView (evaluatorView c (x 1) (garblerMessage G n c (x 0) coins)
            (fun j => garblerOffer G n c coins j (x 1 j))),
          fun _ => runOutput G n c x coins) := by
  rw [Protocol.realJoint, evalWith_protocol, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun coins => ?_)
  simp only [Function.comp_apply, Prod.map, id, restrict_singleton, received_one]

/-! ### Correctness -/

variable {G}

/-- The garbler's tokens followed by the evaluator's are the tokens of the bits of the function's
input. -/
theorem ofFn_projectiveToken_append (e : List Bool) (c : Params G)
    (x : (i : Fin 2) → Input c i) :
    List.ofFn (fun i : Fin c.garblerLen => projectiveToken e (G.inLen c.fn) i (x 0 i)) ++
        List.ofFn (fun j : Fin c.evaluatorLen =>
          projectiveToken e (G.inLen c.fn) (c.garblerLen + j) (x 1 j)) =
      List.ofFn fun i : Fin (circuitInput x).length =>
        projectiveToken e (circuitInput x).length i (circuitInput x)[i] := by
  have hlen := length_circuitInput x
  have hle := c.garblerLen_le
  have htok : projectiveToken e (circuitInput x).length = projectiveToken e (G.inLen c.fn) := by
    rw [hlen]
  have h₀ : (List.ofFn (x 0)).length = c.garblerLen := List.length_ofFn (f := x 0)
  refine List.ext_getElem (by
    simp only [List.length_append, List.length_ofFn, hlen, Params.evaluatorLen]; omega)
    fun i h₁ h₂ => ?_
  simp only [List.getElem_ofFn, Fin.getElem_fin]
  simp only [htok]
  simp only [circuitInput]
  by_cases hi : i < c.garblerLen
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_append_left (by omega),
      List.getElem_ofFn (f := x 0), List.getElem_ofFn]
  · rw [List.getElem_append_right (by simpa using hi), List.getElem_append_right (by omega),
      List.getElem_ofFn (f := x 1), List.getElem_ofFn]
    congr 1
    · simp only [List.length_ofFn]; omega
    · simp only [List.length_ofFn, h₀]

/-- In a run at a parameter `n ≥ 1` with coins of the right length, the evaluator decodes the
function's output, when `G` is correct and its encoding is projective. -/
theorem runOutput_eq (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ}
    (hn : 0 < n) (c : Params G) (x : (i : Fin 2) → Input c i) {coins : List Bool}
    (hcoins : coins.length = G.coins n c.fn) :
    runOutput G n c x coins = G.ev c.fn (circuitInput x) := by
  have hX : ((garblerMessage G n c (x 0) coins).labels ++
      List.ofFn fun j => garblerOffer G n c coins j (x 1 j)).flatten =
        G.encode (G.gb n c.fn coins).encInfo (circuitInput x) := by
    rw [hproj, projectiveEncode_eq_flatten_ofFn, ← ofFn_projectiveToken_append]; rfl
  simp only [runOutput, evaluatorOutput, hX]
  exact congrArg (·.getD []) (hcorrect n hn c.fn (circuitInput x) (length_circuitInput x) _
    (G.mem_support_eval_garble_iff.mpr ⟨coins, hcoins, rfl⟩))

/-- **Correctness of `oneSidedProtocol`**: in every run of `Yao.oneSidedProtocol G n c` at a
parameter `n ≥ 1`, the garbler outputs `[]` and the evaluator outputs `G.ev c.fn` on the garbler's
bits followed by the evaluator's, when `G` is correct and its encoding is projective. -/
theorem oneSided_output_of_mem_support (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    {n : ℕ} (hn : 0 < n) (c : Params G) (x : (i : Fin 2) → Input c i)
    {r : ((i : Fin 2) → PartyView (Input c) Coins (oneSidedSchedule c) i) × (Fin 2 → List Bool)}
    (hr : r ∈ ((oneSidedProtocol G n c).evalWith
      (batchOTWorld c.evaluatorLen (List Bool)) x).support) :
    r.2 = oneSidedOutputs (G.ev c.fn (circuitInput x)) := by
  rw [evalWith_oneSidedProtocol, PMF.mem_support_map_iff] at hr
  obtain ⟨coins, hcoins, rfl⟩ := hr
  exact congrArg oneSidedOutputs
    (runOutput_eq hproj hcorrect hn c x (BitString.mem_support_uniformList_iff.mp hcoins))

/-- **Correctness of `protocol`**: in every run of `Yao.protocol G n c` at a parameter `n ≥ 1`,
both parties output `G.ev c.fn` on the garbler's bits followed by the evaluator's, when `G` is
correct and its encoding is projective. -/
theorem output_of_mem_support (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    {n : ℕ} (hn : 0 < n) (c : Params G) (x : (i : Fin 2) → Input c i)
    {r : ((i : Fin 2) → PartyView (Input c) Coins (schedule c) i) × (Fin 2 → List Bool)}
    (hr : r ∈ ((protocol G n c).evalWith (batchOTWorld c.evaluatorLen (List Bool)) x).support) :
    r.2 = fun _ => G.ev c.fn (circuitInput x) := by
  rw [evalWith_protocol, PMF.mem_support_map_iff] at hr
  obtain ⟨coins, hcoins, rfl⟩ := hr
  exact funext fun _ =>
    runOutput_eq hproj hcorrect hn c x (BitString.mem_support_uniformList_iff.mp hcoins)

/-! ### Encoding for machines -/

/-- The words of a corrupted garbler's view in `oneSidedProtocol`: its input bits and its coins
(it receives nothing). -/
structure OneSidedGarblerViewWords where
  /-- The garbler's input bits. -/
  input : List Bool
  /-- The garbler's coins. -/
  coins : List Bool

/-- The encoding of a one-sided garbler's view words: `input` framed, then `coins`. -/
enc_structure encOneSidedGarblerViewWords : OneSidedGarblerViewWords where
  input : encBits, coins : encBits

/-- The words of a corrupted garbler's view in `protocol`: its input bits, its coins and the output
that the evaluator sends it. -/
structure GarblerViewWords where
  /-- The garbler's input bits. -/
  input : List Bool
  /-- The garbler's coins. -/
  coins : List Bool
  /-- The output received in the last round. -/
  output : List Bool

/-- The encoding of a garbler's view words: each field in turn, all but the last framed. -/
enc_structure encGarblerViewWords : GarblerViewWords where
  input : encBits, coins : encBits, output : encBits

/-- The words of a corrupted evaluator's view: its input bits, the garbler's message (`F`, the
tokens of the garbler's bits and `d`) and the tokens of its own bits. -/
structure EvaluatorViewWords where
  /-- The evaluator's input bits. -/
  input : List Bool
  /-- The garbled function `F`. -/
  fn : List Bool
  /-- The tokens of the garbler's input bits. -/
  garblerLabels : List (List Bool)
  /-- The decoding information `d`. -/
  decInfo : List Bool
  /-- The tokens of the evaluator's input bits, from the oblivious transfer. -/
  evaluatorLabels : List (List Bool)

/-- The encoding of an evaluator's view words: each field in turn, all but the last framed. -/
enc_structure encEvaluatorViewWords : EvaluatorViewWords where
  input : encBits, fn : encBits, garblerLabels : (encList encBits), decInfo : encBits,
  evaluatorLabels : (encList encBits)

/-- The view words of the two parties in `oneSidedProtocol`: `OneSidedGarblerViewWords` for the
garbler (party `0`) and `EvaluatorViewWords` for the evaluator (party `1`). -/
abbrev OneSidedViewWords : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) OneSidedGarblerViewWords
    (fun _ => EvaluatorViewWords) i

/-- The view words of the two parties in `protocol`: `GarblerViewWords` for the garbler (party `0`)
and `EvaluatorViewWords` for the evaluator (party `1`). -/
abbrev ViewWords : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) GarblerViewWords (fun _ => EvaluatorViewWords) i

/-- The words of a garbler's view in `oneSidedProtocol`. -/
@[expose] def oneSidedGarblerViewWords {c : Params G}
    (view : PartyView (Input c) Coins (oneSidedSchedule c) 0) : OneSidedGarblerViewWords :=
  ⟨List.ofFn view.input, view.coins⟩

/-- The words of an evaluator's view in `oneSidedProtocol`. -/
@[expose] def oneSidedEvaluatorViewWords {c : Params G}
    (view : PartyView (Input c) Coins (oneSidedSchedule c) 1) : EvaluatorViewWords :=
  let (msg, ot, _) := view.received
  let m := msg rfl
  ⟨List.ofFn view.input, m.fn, m.labels, m.decInfo, List.ofFn (ot 1 rfl)⟩

/-- The words of a garbler's view in `protocol`. -/
@[expose] def garblerViewWords {c : Params G} (view : PartyView (Input c) Coins (schedule c) 0) :
    GarblerViewWords :=
  let (_, _, y, _) := view.received
  ⟨List.ofFn view.input, view.coins, y rfl⟩

/-- The words of an evaluator's view in `protocol`. -/
@[expose] def evaluatorViewWords {c : Params G}
    (view : PartyView (Input c) Coins (schedule c) 1) : EvaluatorViewWords :=
  oneSidedEvaluatorViewWords
    ⟨view.input, view.coins, (Schedule.Received.split (sc₁ := oneSidedSchedule c) view.received).1⟩

/-- The words determine a garbler's view in `oneSidedProtocol`. -/
theorem oneSidedGarblerViewWords_injective (c : Params G) :
    Function.Injective (oneSidedGarblerViewWords (c := c)) := by
  rintro ⟨x, coins, ⟨m, o, ⟨⟩⟩⟩ ⟨x', coins', ⟨m', o', ⟨⟩⟩⟩ h
  injection h with hx hcoins
  exact PartyView.ext (List.ofFn_injective hx) hcoins
    (Prod.ext (Round.received_message_eq_of_ne (by decide) _ _)
      (Prod.ext (Round.received_oracle_ext fun s hs => by fin_cases s <;> first | rfl | simp at hs)
        rfl))

/-- The words determine an evaluator's view in `oneSidedProtocol`. -/
theorem oneSidedEvaluatorViewWords_injective (c : Params G) :
    Function.Injective (oneSidedEvaluatorViewWords (c := c)) := by
  rintro ⟨x, ⟨⟩, ⟨m, o, ⟨⟩⟩⟩ ⟨x', ⟨⟩, ⟨m', o', ⟨⟩⟩⟩ h
  injection h with hx hfn hlabels hdec hot
  exact PartyView.ext (List.ofFn_injective hx) rfl
    (Prod.ext (Round.received_message_ext fun _ => Message.ext hfn hlabels hdec)
      (Prod.ext (Round.received_oracle_ext fun s hs => by
        fin_cases s <;> [simp at hs; exact List.ofFn_injective hot]) rfl))

/-- The words determine a garbler's view in `protocol`. -/
theorem garblerViewWords_injective (c : Params G) :
    Function.Injective (garblerViewWords (c := c)) := by
  rintro ⟨x, coins, ⟨m, o, y, ⟨⟩⟩⟩ ⟨x', coins', ⟨m', o', y', ⟨⟩⟩⟩ h
  injection h with hx hcoins hy
  have h0 := oneSidedGarblerViewWords_injective c
    (a₁ := ⟨x, coins, ⟨m, o, ()⟩⟩) (a₂ := ⟨x', coins', ⟨m', o', ()⟩⟩)
    (congrArg₂ OneSidedGarblerViewWords.mk hx hcoins)
  refine PartyView.ext (congrArg (fun v => v.input) h0) hcoins
    (Prod.ext (congrArg (fun v => v.received.1) h0)
      (Prod.ext (congrArg (fun v => v.received.2.1) h0) (Prod.ext ?_ rfl)))
  exact Round.received_message_ext fun _ => hy

/-- The words determine an evaluator's view in `protocol`. -/
theorem evaluatorViewWords_injective (c : Params G) :
    Function.Injective (evaluatorViewWords (c := c)) := by
  rintro ⟨x, ⟨⟩, ⟨m, o, r, ⟨⟩⟩⟩ ⟨x', ⟨⟩, ⟨m', o', r', ⟨⟩⟩⟩ h
  have h1 := oneSidedEvaluatorViewWords_injective c h
  exact PartyView.ext (congrArg (fun v => v.input) h1) rfl
    (Prod.ext (congrArg (fun v => v.received.1) h1)
      (Prod.ext (congrArg (fun v => v.received.2.1) h1)
        (Prod.ext (Round.received_message_eq_of_ne (by decide) _ _) rfl)))

/-- The encoding of the public parameters: the function description by `encFn`, framed, then the
garbler's input length in unary. -/
@[expose] def encParams (encFn : Fn ↪ List Bool) : Params G ↪ List Bool where
  toFun c := encPair encFn encUnary (c.fn, c.garblerLen)
  inj' := by
    rintro ⟨f, g, _⟩ ⟨f', g', _⟩ h
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp ((encPair encFn encUnary).injective h)
    rfl

/-- The function description of computed public parameters is computed in polynomial time. -/
theorem encParams_fn_polyTime {encFn : Fn ↪ List Bool} {γ : Type} {enc : γ ↪ List Bool}
    {c : γ → Params G} (h : ComputableInPolyTime c enc (encParams encFn)) :
    ComputableInPolyTime (fun a => (c a).fn) enc encFn :=
  (ComputableInPolyTime.fst' (ComputableInPolyTime.of_eq (encIn := encParams encFn)
    (encOut := encPair encFn encUnary) (f := fun c : Params G => (c.fn, c.garblerLen))
    fun _ => rfl)).comp h

/-- The garbler's input length of computed public parameters is computed in polynomial time. -/
theorem encParams_garblerLen_polyTime {encFn : Fn ↪ List Bool} {γ : Type} {enc : γ ↪ List Bool}
    {c : γ → Params G} (h : ComputableInPolyTime c enc (encParams encFn)) :
    ComputableInPolyTime (fun a => (c a).garblerLen) enc encUnary :=
  (ComputableInPolyTime.snd' (ComputableInPolyTime.of_eq (encIn := encParams encFn)
    (encOut := encPair encFn encUnary) (f := fun c : Params G => (c.fn, c.garblerLen))
    fun _ => rfl)).comp h

/-- **The number of transfers of computed public parameters is computed in polynomial time**, in
unary, when the garbling scheme reads input lengths in polynomial time: it is the input length of
the function less the garbler's share. For a uniform family `c : ℕ → Yao.Params G` it makes
`fun n => (c n).evaluatorLen` polynomially bounded
(`ComputableInPolyTime.polynomiallyBounded`). -/
theorem encParams_evaluatorLen_polyTime {encFn : Fn ↪ List Bool} {γ : Type} {enc : γ ↪ List Bool}
    {c : γ → Params G} (hc : ComputableInPolyTime c enc (encParams encFn))
    (hinLen : ComputableInPolyTime G.inLen encFn encUnary) :
    ComputableInPolyTime (fun a => (c a).evaluatorLen) enc encUnary :=
  ComputableInPolyTime.unary_sub' (hinLen.comp (encParams_fn_polyTime hc))
    (encParams_garblerLen_polyTime hc)

variable (G)

/-- The machine representation of the parties' inputs, shared by `oneSidedEncoding` and `encoding`:
each party's input bit string as its word of bits (`List.ofFn`). -/
@[expose] def inputEncoding : PartyEncoding (Params G) 2 fun _ => Input where
  Rep := fun _ => List Bool
  enc := fun _ => encBits
  rep := fun _ c i => Fin.cases (motive := fun i => Input c i ↪ List Bool)
    ⟨List.ofFn, List.ofFn_injective⟩ (fun _ => ⟨List.ofFn, List.ofFn_injective⟩) i

/-- The machine representation of the parties' outputs, shared by `oneSidedEncoding` and
`encoding`: each party's output word verbatim. -/
@[expose] def outputEncoding : PartyEncoding (Params G) 2 fun _ _ _ => List Bool where
  Rep := fun _ => List Bool
  enc := fun _ => encBits
  rep := fun _ _ _ => Function.Embedding.refl _

/-- The encoding of `Yao.oneSidedFamily G` for machines, with function descriptions encoded by
`encFn`. The public parameters are written by `encParams encFn`. Each party's input is the word of
its bits, and each output is itself. The views are their view words (`oneSidedGarblerViewWords`,
`oneSidedEvaluatorViewWords`), encoded by `encOneSidedGarblerViewWords` and
`encEvaluatorViewWords`. -/
@[expose] noncomputable def oneSidedEncoding (encFn : Fn ↪ List Bool) :
    (oneSidedFamily G).Encoding where
  desc := encParams encFn
  input := inputEncoding G
  output := outputEncoding G
  view :=
    { Rep := OneSidedViewWords
      enc := fun i => Fin.cases (motive := fun i => OneSidedViewWords i ↪ List Bool)
        encOneSidedGarblerViewWords (fun _ => encEvaluatorViewWords) i
      rep := fun _ c i => Fin.cases
        (motive := fun i => PartyView (Input c) Coins (oneSidedSchedule c) i ↪ OneSidedViewWords i)
        ⟨oneSidedGarblerViewWords, oneSidedGarblerViewWords_injective c⟩
        (Fin.cases (motive := fun j =>
            PartyView (Input c) Coins (oneSidedSchedule c) j.succ ↪ OneSidedViewWords j.succ)
          ⟨oneSidedEvaluatorViewWords, oneSidedEvaluatorViewWords_injective c⟩ fun k => k.elim0) i }

/-- The encoding of `Yao.family G` for machines, with function descriptions encoded by `encFn`.
The public parameters are written by `encParams encFn`. Each party's input is the word of its
bits, and each output is itself. The views are their view words (`garblerViewWords`,
`evaluatorViewWords`), encoded by `encGarblerViewWords` and `encEvaluatorViewWords`. -/
@[expose] noncomputable def encoding (encFn : Fn ↪ List Bool) : (family G).Encoding where
  desc := encParams encFn
  input := inputEncoding G
  output := outputEncoding G
  view :=
    { Rep := ViewWords
      enc := fun i => Fin.cases (motive := fun i => ViewWords i ↪ List Bool)
        encGarblerViewWords (fun _ => encEvaluatorViewWords) i
      rep := fun _ c i => Fin.cases
        (motive := fun i => PartyView (Input c) Coins (schedule c) i ↪ ViewWords i)
        ⟨garblerViewWords, garblerViewWords_injective c⟩
        (Fin.cases (motive := fun j =>
            PartyView (Input c) Coins (schedule c) j.succ ↪ ViewWords j.succ)
          ⟨evaluatorViewWords, evaluatorViewWords_injective c⟩ fun k => k.elim0) i }

/-! ### A corrupted garbler -/

/-- The simulator family for a corrupted garbler in `oneSidedFamily`: draw a fresh coin string for
`Gb` and record nothing received. -/
@[expose] noncomputable def oneSidedGarblerSim : SimulatorFamily (oneSidedFamily G) {0} :=
  fun n c xI _ => do
    let coins ← BitString.sampleList (G.coins n c.fn)
    return singletonView (oneSidedGarblerView c (xI ⟨0, Finset.mem_singleton_self 0⟩) coins)

/-- The simulator family for a corrupted garbler in `family`: draw a fresh coin string for `Gb` and
deliver the garbler's output as the evaluator's last message. -/
@[expose] noncomputable def garblerSim : SimulatorFamily (family G) {0} :=
  fun n c xI yI => do
    let coins ← BitString.sampleList (G.coins n c.fn)
    return singletonView (garblerView c (xI ⟨0, Finset.mem_singleton_self 0⟩) coins
      (yI ⟨0, Finset.mem_singleton_self 0⟩))

variable {G}

/-- **The one-sided garbler simulator is exact** at every parameter `n ≥ 1`, when `G` is correct
and its encoding is projective: the ideal joint distribution with `oneSidedGarblerSim` equals the
real one. -/
theorem idealJoint_oneSidedGarblerSim (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    {n : ℕ} (hn : 0 < n) (c : Params G) (x : (i : Fin 2) → Input c i) :
    ProbComp.eval (idealJoint (oneSidedFunctionality G c) {0} (oneSidedGarblerSim G n c) x) =
      (oneSidedProtocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {0} x := by
  rw [realJoint_oneSided_garbler]
  simp only [pmf_norm, idealJoint, oneSidedFunctionality, Functionality.ofDeterministic,
    oneSidedGarblerSim, BitString.eval_sampleList]
  rw [← PMF.bind_pure_comp]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun coins hcoins => ?_
  simp only [Function.comp_apply,
    runOutput_eq hproj hcorrect hn c x (BitString.mem_support_uniformList_iff.mp hcoins)]
  rfl

/-- **The garbler's simulator is exact** at every parameter `n ≥ 1`, when `G` is correct and its
encoding is projective: the ideal joint distribution with `garblerSim` equals the real one. -/
theorem idealJoint_garblerSim (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    {n : ℕ} (hn : 0 < n) (c : Params G) (x : (i : Fin 2) → Input c i) :
    ProbComp.eval (idealJoint (functionality G c) {0} (garblerSim G n c) x) =
      (protocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {0} x := by
  rw [realJoint_garbler]
  simp only [pmf_norm, idealJoint, functionality, Functionality.ofDeterministic, garblerSim,
    BitString.eval_sampleList]
  rw [← PMF.bind_pure_comp]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun coins hcoins => ?_
  simp only [Function.comp_apply,
    runOutput_eq hproj hcorrect hn c x (BitString.mem_support_uniformList_iff.mp hcoins)]
  rfl

/-- Shared PPT witness builder for a simulator family that draws `G.coins x.secParam (fnOf x.desc)`
fair coins and computes the coalition's view representations in polynomial time. -/
private theorem isPPT_sim_of_coins {P : ProtocolFamily 2} {I : Finset (Fin 2)}
    {encFn : Fn ↪ List Bool} (E : P.Encoding) {fnOf : P.Desc → Fn}
    (hfn : ComputableInPolyTime fnOf E.desc encFn)
    (hcoins : ComputableInPolyTime (fun (k, f) => G.coins k f) (encPair encUnary encFn) encUnary)
    {S : SimulatorFamily P I} {reps : SimInput P I × List Bool → ∀ i : I, E.view.Rep i}
    (hreps : ∀ i : I, ComputableInPolyTime (fun p => reps p i)
      (encPair (encSimInput E) encBits) (E.view.enc i))
    (heq : ∀ x : SimInput P I,
      ProbComp.eval ((fun v (i : I) => E.view.rep x.secParam x.desc i (v i)) <$>
          S x.secParam x.desc x.inputs x.outputs) =
        ProbComp.eval ((fun coins => reps (x, coins)) <$>
          BitString.sampleList (G.coins x.secParam (fnOf x.desc)))) :
    S.IsPPT E := by
  have hcount : ComputableInPolyTime
      (fun x : SimInput P I => G.coins x.secParam (fnOf x.desc)) (encSimInput E) encUnary :=
    hcoins.comp ((encSimInput_secParam_polyTime E .id').prod
      (hfn.comp (encSimInput_desc_polyTime E .id')))
  exact (IsPPTOn.of_seeded hcount (ComputableInPolyTime.dpi hreps)).congr fun x => (heq x).symm

/-- The simulator family `oneSidedGarblerSim` for a corrupted garbler is PPT for
`oneSidedEncoding G encFn` when `G` computes its coin count in polynomial time. -/
theorem isPPT_oneSidedGarblerSim {encFn : Fn ↪ List Bool}
    (hcoins : ComputableInPolyTime (fun (k, f) => G.coins k f) (encPair encUnary encFn) encUnary) :
    (oneSidedGarblerSim G).IsPPT (oneSidedEncoding G encFn) := by
  let E := oneSidedEncoding G encFn
  have hx₀ := E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E .id')
    (⟨0, Finset.mem_singleton_self 0⟩ : ({0} : Finset (Fin 2)))
  refine isPPT_sim_of_coins E (encParams_fn_polyTime .id') hcoins
    (reps := fun (p : SimInput (oneSidedFamily G) {0} × List Bool) i =>
      (Finset.mem_singleton.mp i.2).symm ▸
        OneSidedGarblerViewWords.mk
          (E.input.rep p.1.secParam p.1.desc 0 (p.1.inputs ⟨0, Finset.mem_singleton_self 0⟩)) p.2)
    (fun ⟨j, hj⟩ => ?_) (fun ⟨n, c, xs, _⟩ => ?_)
  · obtain rfl := Finset.mem_singleton.mp hj
    exact encOneSidedGarblerViewWords_mk_polyTime (hx₀.comp (.fst _ _)) (.snd _ _)
  · simp only [oneSidedGarblerSim, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
      ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    exact congrArg (PMF.bind _) (funext fun _ => congrArg PMF.pure
      (funext fun ⟨_, hj⟩ => by obtain rfl := Finset.mem_singleton.mp hj; rfl))

/-- The simulator family `garblerSim` for a corrupted garbler is PPT for `encoding G encFn` when
`G` computes its coin count in polynomial time: it draws `G.coins n c.fn` fair coins. -/
theorem isPPT_garblerSim {encFn : Fn ↪ List Bool}
    (hcoins : ComputableInPolyTime (fun (k, f) => G.coins k f) (encPair encUnary encFn) encUnary) :
    (garblerSim G).IsPPT (encoding G encFn) := by
  let E := encoding G encFn
  have hx₀ := E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E .id')
    (⟨0, Finset.mem_singleton_self 0⟩ : ({0} : Finset (Fin 2)))
  have hy := E.output.encCoalition_apply_polyTime (encSimInput_outputs_polyTime E .id')
    (⟨0, Finset.mem_singleton_self 0⟩ : ({0} : Finset (Fin 2)))
  refine isPPT_sim_of_coins E (encParams_fn_polyTime .id') hcoins
    (reps := fun (p : SimInput (family G) {0} × List Bool) i =>
      (Finset.mem_singleton.mp i.2).symm ▸
        GarblerViewWords.mk
          (E.input.rep p.1.secParam p.1.desc 0 (p.1.inputs ⟨0, Finset.mem_singleton_self 0⟩)) p.2
          (E.output.rep p.1.secParam p.1.desc 0 (p.1.outputs ⟨0, Finset.mem_singleton_self 0⟩)))
    (fun ⟨j, hj⟩ => ?_) (fun ⟨n, c, xs, ys⟩ => ?_)
  · obtain rfl := Finset.mem_singleton.mp hj
    exact encGarblerViewWords_mk_polyTime (hx₀.comp (.fst _ _)) (.snd _ _) (hy.comp (.fst _ _))
  · simp only [garblerSim, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
      ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    exact congrArg (PMF.bind _) (funext fun _ => congrArg PMF.pure
      (funext fun ⟨_, hj⟩ => by obtain rfl := Finset.mem_singleton.mp hj; rfl))

/-- Perfect privacy from parameter `n = 1` on with a PPT simulator family gives
`ProtocolFamily.SemiHonestSecure`. -/
private theorem semiHonestSecure_of_pos_perfect {P : ProtocolFamily 2} {setup : ℕ → PMF P.Desc}
    {I : Finset (Fin 2)} {E : P.Encoding} {S : SimulatorFamily P I} (hS : S.IsPPT E)
    (h : ∀ {n : ℕ}, 0 < n → ∀ d x,
      ProbComp.eval (idealJoint (P.functionality n d) I (S n d) x) =
        (P.protocol n d).realJoint (P.world n d) I x) :
    P.SemiHonestSecure setup I E :=
  ⟨S, hS, fun Z _ => negligible_of_eventually_le negligible_zero <|
    (Filter.eventually_gt_atTop 0).mono fun n hn => by
      dsimp only
      rw [show P.realGame setup I Z n = P.idealGame setup I S Z n by
        simp only [ProtocolFamily.realGame, ProtocolFamily.idealGame, h hn], Game.advantage_self]⟩

/-- Step in the ideal `batchOTWorld` oblivious-transfer hybrid model (#6045), with no computational
assumption: semi-honest security of `Yao.oneSidedFamily G` against a corrupted garbler, towards
Theorem 7 of [LindellPinkas2009] (ePrint 2004/175, §4.2, p. 15; Case 1, p. 16) and Theorem 14 of
[BellareHoangRogaway2012] (§7.1, p. 35), which compose with a concrete semi-honest 1-out-of-2
oblivious-transfer protocol. For every setup law of the public parameters, when `G` is correct, its
encoding is `projectiveEncode` and its coin count is computed in polynomial time, the PPT simulator
family `oneSidedGarblerSim` makes the real and ideal games equal at every parameter `n ≥ 1`. -/
theorem hybridSemiHonestSecure_oneSided_garbler {encFn : Fn ↪ List Bool}
    (hcoins : ComputableInPolyTime (fun (k, f) => G.coins k f) (encPair encUnary encFn) encUnary)
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) (setup : ℕ → PMF (Params G)) :
    (oneSidedFamily G).SemiHonestSecure setup {0} (oneSidedEncoding G encFn) :=
  semiHonestSecure_of_pos_perfect (isPPT_oneSidedGarblerSim hcoins)
    (fun hn c x => idealJoint_oneSidedGarblerSim hproj hcorrect hn c x)

/-- Semi-honest security of `Yao.family G` against a corrupted garbler in the ideal `batchOTWorld`
oblivious-transfer hybrid model (#6045), with no computational assumption: a step towards Theorem 7
of [LindellPinkas2009] (ePrint 2004/175, §4.2, p. 15), not plain-model Theorem 7 or its Case 1
(p. 16), which compose with a concrete semi-honest 1-out-of-2 oblivious-transfer protocol. For
every setup law of the public parameters, when `G` is correct, its encoding is `projectiveEncode`
and its coin count is computed in polynomial time, the PPT simulator family `garblerSim` makes the
real and ideal games equal at every parameter `n ≥ 1`. Case 1 simulates the garbler's view of the
oblivious-transfer protocol and then uses correctness; with the ideal `batchOTWorld` (`batchOTSpec`)
the garbler's view of the transfer is empty, so only the correctness step remains. The other
deviations are those of the module documentation: uniform environments that choose the inputs, a
setup law, and the garbling scheme as a parameter, correct from `n = 1` on. -/
theorem hybridSemiHonestSecure_garbler {encFn : Fn ↪ List Bool}
    (hcoins : ComputableInPolyTime (fun (k, f) => G.coins k f) (encPair encUnary encFn) encUnary)
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) (setup : ℕ → PMF (Params G)) :
    (family G).SemiHonestSecure setup {0} (encoding G encFn) :=
  semiHonestSecure_of_pos_perfect (isPPT_garblerSim hcoins)
    (fun hn c x => idealJoint_garblerSim hproj hcorrect hn c x)

end Cslib.Crypto.Protocols.MPC.Yao
