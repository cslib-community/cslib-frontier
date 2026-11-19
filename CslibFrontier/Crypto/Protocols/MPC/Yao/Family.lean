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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind

/-!
# Yao's protocol over a garbling scheme in the ideal OT hybrid model

This module defines the protocol family `Yao.family G` (`Cslib.Crypto.Protocols.MPC.ProtocolFamily`)
running Yao's two-party protocol [Yao1986] in the ideal `batchOTWorld` (`batchOTSpec`)
oblivious-transfer hybrid model (#6045), rather than composing with concrete 1-out-of-2
oblivious-transfer executions as in Protocol 2 of Lindell and Pinkas [LindellPinkas2009] (ePrint
2004/175, §4.2, p. 15). It is parameterized over any garbling scheme `G : Garbling.Scheme Fn` of
Bellare, Hoang and Rogaway [BellareHoangRogaway2012] whose input encoding is `projectiveEncode`:
projective in the sense of §3.2 (p. 8), in the word layout of point-and-permute and half-gates
garbling, with `2 n` tokens of one width.

The public parameters `Yao.Params G` are a function description `fn`, known to both parties, and
the number `garblerLen` of its input bits held by the garbler (party `0`); the evaluator (party
`1`) holds the rest. At the security parameter `n`:

1. the garbler draws `G.coins n fn` fair coins, garbles `fn` to `(F, e, d)` with `G.gb`, and sends
   `F`, the tokens of its own input bits (`projectiveToken`) and `d` (`Yao.garblerMessage`);
2. one batched oblivious transfer gives the evaluator the tokens of its own input bits, from the
   pairs that the garbler offers (`Yao.garblerOffer`);
3. the evaluator evaluates `F` on all the tokens, decodes with `d` (`Yao.evaluatorOutput`), and
   sends the result back, and both parties output it.

The functionality `Yao.functionality` gives both parties `G.ev fn x` on the garbler's bits
followed by the evaluator's (`Yao.circuitInput`): this is a deterministic same-output
functionality, the case Lindell and Pinkas treat. Both parties output the evaluator's decoding,
which is the functionality's output in every run at a parameter `n ≥ 1` when `G` is correct
(`Yao.output_of_mem_support`); the correctness of `Garbling.Scheme.Correct` is stated for `k ≥ 1`.

`Yao.encoding G encFn` writes the public parameters, inputs, outputs and views as words, for the
efficiency predicates of `ProtocolFamily.SemiHonestSecure`. A corrupted garbler sees its input, its
coins and the output: `Yao.garblerSim` draws fresh coins, matches its real view at every `n ≥ 1`
(`Yao.idealJoint_garblerSim`), and is PPT when `G` computes its coin count in polynomial time
(`Yao.isPPT_garblerSim`). So the family is semi-honest secure against the garbler in the
`batchOTWorld` hybrid (`Yao.hybridSemiHonestSecure_garbler`), with no assumption. This is a step
towards Theorem 7 of Lindell and Pinkas (#6045), not that theorem or its Case 1 (p. 16). Case 1
simulates the garbler's view of the oblivious-transfer protocol and then uses correctness (Claim
6); in the hybrid model the garbler's view of the transfer is empty, so only the correctness step
remains. `Yao.realJoint_garbler` and `Yao.realJoint_evaluator` give the real joint laws from the
garbler's coins.

## Comparison with [LindellPinkas2009]

* **Oblivious transfer.** The transfers are the ideal `batchOTSpec`, one call for all of the
  evaluator's bits; Theorem 7 (p. 15) assumes an oblivious transfer protocol, run for each bit.
  Composition with a protocol is not formalized here (#6045).
* **Notion.** `ProtocolFamily.SemiHonestSecure` has uniform PPT environments that choose the inputs
  after seeing the public parameters, drawn from a setup law; Definition 1 (§2.1, p. 5) quantifies
  over all inputs against non-uniform distinguishers, with no setup.
* **Garbling scheme.** Lindell and Pinkas garble with a specific double-encryption construction
  (§4.1, p. 12). Here the garbling scheme is a parameter, and the protocol uses only its
  algorithms and its encoding `projectiveEncode`, as in the modular construction of
  [BellareHoangRogaway2012], §7.1 (p. 34). Its correctness is that of `Garbling.Scheme.Correct`,
  from the security parameter `1` on.
* **Inputs.** The garbler holds the first `garblerLen` input bits and the evaluator the rest,
  where Lindell and Pinkas have `n` bits each. Outputs are words of any length.
* **Security parameter.** The function description is a public parameter drawn from a setup law,
  not the auxiliary input of a circuit for inputs of length `n`, and the garbling scheme runs at the
  security parameter `n`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Yao.Params`: the public parameters.
* `Cslib.Crypto.Protocols.MPC.Yao.protocol`, `Cslib.Crypto.Protocols.MPC.Yao.family`: the protocol
  and the protocol family, with the schedule `Yao.schedule` and the functionality
  `Yao.functionality`.
* `Cslib.Crypto.Protocols.MPC.Yao.garblerView`, `Cslib.Crypto.Protocols.MPC.Yao.evaluatorView`: the
  parties' views.
* `Cslib.Crypto.Protocols.MPC.Yao.encoding`: the encoding of the family for machines.
* `Cslib.Crypto.Protocols.MPC.Yao.garblerSim`: the simulator for a corrupted garbler.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.output_of_mem_support`: correctness.
* `Cslib.Crypto.Protocols.MPC.Yao.idealJoint_garblerSim`,
  `Cslib.Crypto.Protocols.MPC.Yao.isPPT_garblerSim`: the garbler's simulator is exact from `n = 1`
  on and PPT.
* `Cslib.Crypto.Protocols.MPC.Yao.hybridSemiHonestSecure_garbler`: corrupted-garbler step in the
  ideal `batchOTWorld` hybrid (#6045) towards Theorem 7 of [LindellPinkas2009].

## References

* [A. C. Yao, *How to Generate and Exchange Secrets*][Yao1986]
* [Y. Lindell, B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009], cited in the ePrint version 2004/175 of June 26, 2006:
  Definition 1 (§2.1, p. 5), §4.1 (p. 12), Protocol 2 and Theorem 7 (§4.2, p. 15), Case 1
  (p. 16).
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012],
  §3.2 (p. 8) and §7.1 (p. 34).
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
    List.length_ofFn (f := x 1), Params.evaluatorLen]
  omega

/-- The garbler's message: the garbled function `F`, the tokens of the garbler's input bits and the
decoding information `d`. -/
@[ext] structure Message where
  /-- The garbled function `F`. -/
  fn : List Bool
  /-- The tokens of the garbler's input bits. -/
  labels : List (List Bool)
  /-- The decoding information `d`. -/
  decInfo : List Bool

/-- The schedule: the garbler sends its message, the parties run one batched oblivious transfer of
the tokens of the evaluator's input bits, and the evaluator sends the output to the garbler. -/
abbrev schedule (c : Params G) : Schedule 2 (batchOTSpec c.evaluatorLen (List Bool)) :=
  [.message 0 1 Message, .oracle () (Function.Embedding.refl (Fin 2)),
    .message 1 0 (List Bool)]

/-- A party's local state after the oblivious transfer. -/
abbrev AfterTransfer (c : Params G) (i : Fin 2) : Type :=
  ((Input c i × Coins i) ×
      (Round.message (spec := batchOTSpec c.evaluatorLen (List Bool)) 0 1 Message).Received i) ×
    (Round.oracle (spec := batchOTSpec c.evaluatorLen (List Bool)) ()
      (Function.Embedding.refl (Fin 2))).Received i

/-- A party's final local state. -/
abbrev Final (c : Params G) (i : Fin 2) : Type :=
  AfterTransfer c i ×
    (Round.message (spec := batchOTSpec c.evaluatorLen (List Bool)) 1 0 (List Bool)).Received i

variable (G)

/-- The functionality: both parties learn `G.ev c.fn` on the garbler's bits followed by the
evaluator's. -/
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

/-- The parties' outputs: the garbler outputs what the evaluator sent, and the evaluator its
decoding. -/
@[expose] def finalOutput (c : Params G) (i : Fin 2) (st : Final c i) : List Bool :=
  Fin.cases (motive := fun i => Final c i → List Bool)
    (fun (_, y) => y rfl)
    (fun j (((_, msg), ot), _) => evaluatorOutput G (msg (Fin.fin_one_eq_zero j ▸ rfl))
      (ot 1 (Fin.fin_one_eq_zero j ▸ rfl)))
    i st

/-- **Yao's protocol** over the garbling scheme `G` at parameter `n` (Protocol 2 of
[LindellPinkas2009], §4.2, p. 15, over a projective garbling scheme and one ideal batched
oblivious transfer): the garbler garbles `c.fn` with `G.coins n c.fn` fair coins and sends `F`,
the tokens of its input bits and `d`; one batched oblivious transfer gives the evaluator the tokens
of its input bits; the evaluator evaluates and decodes, sends the result to the garbler, and both
output it. -/
@[expose] noncomputable def protocol (n : ℕ) (c : Params G) :
    Protocol 2 (batchOTSpec c.evaluatorLen (List Bool)) (schedule c) (Input c) Coins
      (fun _ => List Bool) where
  sampleCoins i := Fin.cases (motive := fun i => ProbComp (Coins i))
    (BitString.sampleList (G.coins n c.fn)) (fun _ => pure ()) i
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

/-- The garbler's view, from its input `x₀`, its coins and the output `y` that the evaluator sends:
it receives nothing else. -/
@[expose] def garblerView (c : Params G) (x₀ : BitString c.garblerLen) (coins : List Bool)
    (y : List Bool) : PartyView (Input c) Coins (schedule c) 0 where
  input := x₀
  coins := coins
  received :=
    (fun h => absurd h (by decide),
      (fun s hs => Fin.cases
        (motive := fun s => s = 0 → (batchOTSpec c.evaluatorLen (List Bool)).Answer () s)
        (fun _ => ()) (fun j hj => absurd hj (Fin.succ_ne_zero j)) s hs,
        (fun _ => y, ())))

/-- The evaluator's view, from its input `x₁`, the garbler's message and the tokens that the
oblivious transfer delivers; it sends the last message and receives nothing in that round. -/
@[expose] def evaluatorView (c : Params G) (x₁ : BitString c.evaluatorLen) (msg : Message)
    (labels : Fin c.evaluatorLen → List Bool) : PartyView (Input c) Coins (schedule c) 1 where
  input := x₁
  coins := ()
  received :=
    (fun _ => msg,
      (fun s _ => Fin.cases
        (motive := fun s => (batchOTSpec c.evaluatorLen (List Bool)).Answer () s)
        () (fun _ => labels) s,
        (fun h => absurd h (by decide), ())))

/-- The coins of a run as a coin tuple. -/
private def coinTuple (coins : List Bool) : (i : Fin 2) → Coins i :=
  fun i => Fin.cases (motive := fun i => Coins i) coins (fun _ => ()) i

variable (G)

/-- The output of a run of `Yao.protocol G n c` on inputs `x` with the garbler's coins `coins`: the
evaluator's decoding. -/
@[expose] def runOutput (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) : List Bool :=
  evaluatorOutput G (garblerMessage G n c (x 0) coins) fun j => garblerOffer G n c coins j (x 1 j)

/-- The transcripts that the parties receive in a run on inputs `x` with the garbler's coins
`coins`. -/
private def received (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i) (coins : List Bool)
    (i : Fin 2) : (schedule c).Received i :=
  (Round.deliverMessage (garblerMessage G n c (x 0) coins) i,
    Round.deliverOracle (spec := batchOTSpec c.evaluatorLen (List Bool)) (op := ())
      (Function.Embedding.refl (Fin 2))
      (batchOTAnswer fun s => transferQuery G n c s ((x s, coinTuple coins s),
        Round.deliverMessage (garblerMessage G n c (x 0) coins) s)) i,
    Round.deliverMessage (runOutput G n c x coins) i, ())

/-- Once the coins are fixed, the protocol's steps are deterministic. -/
private theorem evalWith_steps (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) :
    (protocol G n c).steps.evalWith (batchOTWorld c.evaluatorLen (List Bool))
        (fun i => (x i, coinTuple coins i)) =
      PMF.pure (received G n c x coins) := by
  refine (Steps.evalWith_message _ _ _ _).trans ?_
  refine (congrArg (PMF.map _) (Steps.evalWith_oracle _ _ _ _)).trans ?_
  simp only [pmf_norm, Steps.evalWith_message, Steps.evalWith_done, batchOTWorld]
  rfl

/-- Independent coin sampling draws the garbler's coin string. -/
private theorem eval_pi_sampleCoins (n : ℕ) (c : Params G) :
    ProbComp.eval (OracleComp.pi (protocol G n c).sampleCoins) =
      (BitString.uniformList (G.coins n c.fn)).map coinTuple := by
  have h1 : ProbComp.eval ((protocol G n c).sampleCoins (Fin.succ 0)) =
      PMF.pure (show Coins (Fin.succ 0) from ()) := rfl
  simp only [OracleComp.pi_succ, OracleComp.pi_zero, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, h1]
  erw [PMF.pure_bind]
  simp only [PMF.pure_map]
  rw [← PMF.bind_pure_comp]
  refine congrArg₂ PMF.bind (BitString.eval_sampleList _)
    (funext fun coins => congrArg PMF.pure (funext fun i => ?_))
  fin_cases i <;> rfl

/-- The views and outputs of a run, from the garbler's coins. -/
private theorem evalWith_protocol (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i) :
    (protocol G n c).evalWith (batchOTWorld c.evaluatorLen (List Bool)) x =
      (BitString.uniformList (G.coins n c.fn)).map fun coins =>
        (fun i => ⟨x i, coinTuple coins i, received G n c x coins i⟩,
          fun _ => runOutput G n c x coins) := by
  rw [Protocol.evalWith_eq, eval_pi_sampleCoins, PMF.bind_map, ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun coins => ?_)
  simp only [Function.comp_apply, evalWith_steps, PMF.pure_map]
  refine congrArg PMF.pure (Prod.ext rfl (funext fun i => ?_))
  fin_cases i <;> rfl

/-- The garbler's view in a run. -/
private theorem received_zero (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) :
    (⟨x 0, coinTuple coins 0, received G n c x coins 0⟩ :
        PartyView (Input c) Coins (schedule c) 0) =
      garblerView c (x 0) coins (runOutput G n c x coins) := by
  refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · refine Round.received_oracle_ext fun s hs => ?_
    fin_cases s
    · rfl
    · simp at hs

/-- The evaluator's view in a run. -/
private theorem received_one (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (coins : List Bool) :
    (⟨x 1, coinTuple coins 1, received G n c x coins 1⟩ :
        PartyView (Input c) Coins (schedule c) 1) =
      evaluatorView c (x 1) (garblerMessage G n c (x 0) coins)
        (fun j => garblerOffer G n c coins j (x 1 j)) := by
  refine PartyView.ext rfl rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · refine Round.received_oracle_ext fun s hs => ?_
    fin_cases s
    · simp at hs
    · rfl
  · exact Round.received_message_eq_of_ne (by decide) _ _

/-- The real joint distribution for a corrupted garbler: fresh coins, and the evaluator's decoding
as the message of the last round and as both outputs. -/
theorem realJoint_garbler (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i) :
    (protocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {0} x =
      (BitString.uniformList (G.coins n c.fn)).map fun coins =>
        (singletonView (garblerView c (x 0) coins (runOutput G n c x coins)),
          fun _ => runOutput G n c x coins) := by
  rw [Protocol.realJoint, evalWith_protocol, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun coins => ?_)
  simp only [Function.comp_apply, Prod.map, id, restrict_singleton]
  rw [received_zero]

/-- The real joint distribution for a corrupted evaluator: its view holds the garbler's message
and the tokens of its own bits, and both outputs are its decoding. -/
theorem realJoint_evaluator (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i) :
    (protocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {1} x =
      (BitString.uniformList (G.coins n c.fn)).map fun coins =>
        (singletonView (evaluatorView c (x 1) (garblerMessage G n c (x 0) coins)
            (fun j => garblerOffer G n c coins j (x 1 j))),
          fun _ => runOutput G n c x coins) := by
  rw [Protocol.realJoint, evalWith_protocol, PMF.map_comp]
  refine congrArg (PMF.map · _) (funext fun coins => ?_)
  simp only [Function.comp_apply, Prod.map, id, restrict_singleton]
  rw [received_one]

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
    · simp only [List.length_ofFn]
      omega
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
    rw [hproj, projectiveEncode_eq_flatten_ofFn, ← ofFn_projectiveToken_append]
    rfl
  have hmem : G.gb n c.fn coins ∈ (ProbComp.eval (G.garble n c.fn)).support :=
    G.mem_support_eval_garble_iff.mpr ⟨coins, hcoins, rfl⟩
  have h := hcorrect n hn c.fn (circuitInput x) (length_circuitInput x) _ hmem
  simp only [runOutput, evaluatorOutput]
  rw [hX]
  exact congrArg (·.getD []) h

/-- **Correctness**: in every run of `Yao.protocol G n c` at a parameter `n ≥ 1`, both parties
output `G.ev c.fn` on the garbler's bits followed by the evaluator's, when `G` is correct and its
encoding is projective. -/
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

/-- The words of a corrupted garbler's view: its input bits, its coins and the output that the
evaluator sends it. -/
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

/-- The view words of the two parties: `GarblerViewWords` for the garbler (party `0`) and
`EvaluatorViewWords` for the evaluator (party `1`). -/
abbrev ViewWords : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) GarblerViewWords (fun _ => EvaluatorViewWords) i

/-- The words of a garbler's view. -/
@[expose] def garblerViewWords {c : Params G} (view : PartyView (Input c) Coins (schedule c) 0) :
    GarblerViewWords :=
  let (_, _, y, _) := view.received
  ⟨List.ofFn view.input, view.coins, y rfl⟩

/-- The words of an evaluator's view. -/
@[expose] def evaluatorViewWords {c : Params G}
    (view : PartyView (Input c) Coins (schedule c) 1) : EvaluatorViewWords :=
  let (msg, ot, _, _) := view.received
  let m := msg rfl
  ⟨List.ofFn view.input, m.fn, m.labels, m.decInfo, List.ofFn (ot 1 rfl)⟩

/-- The words determine a garbler's view. -/
theorem garblerViewWords_injective (c : Params G) :
    Function.Injective (garblerViewWords (c := c)) := by
  rintro ⟨x, coins, ⟨m, o, y, ⟨⟩⟩⟩ ⟨x', coins', ⟨m', o', y', ⟨⟩⟩⟩ h
  injection h with hx hcoins hy
  refine PartyView.ext (List.ofFn_injective hx) hcoins
    (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · refine Round.received_oracle_ext fun s hs => ?_
    fin_cases s
    · rfl
    · simp at hs
  · exact Round.received_message_ext fun _ => hy

/-- The words determine an evaluator's view. -/
theorem evaluatorViewWords_injective (c : Params G) :
    Function.Injective (evaluatorViewWords (c := c)) := by
  rintro ⟨x, ⟨⟩, ⟨m, o, r, ⟨⟩⟩⟩ ⟨x', ⟨⟩, ⟨m', o', r', ⟨⟩⟩⟩ h
  injection h with hx hfn hlabels hdec hot
  refine PartyView.ext (List.ofFn_injective hx) rfl
    (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Round.received_message_ext fun _ => Message.ext hfn hlabels hdec
  · refine Round.received_oracle_ext fun s hs => ?_
    fin_cases s
    · simp at hs
    · exact List.ofFn_injective hot
  · exact Round.received_message_eq_of_ne (by decide) _ _

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

variable (G)

/-- The encoding of `Yao.family G` for machines, with function descriptions encoded by `encFn`.
The public parameters are written by `encParams encFn`. Each party's input is the word of its
bits, and each output is itself. The views are their view words (`garblerViewWords`,
`evaluatorViewWords`), encoded by `encGarblerViewWords` and `encEvaluatorViewWords`. -/
@[expose] noncomputable def encoding (encFn : Fn ↪ List Bool) : (family G).Encoding where
  desc := encParams encFn
  input :=
    { Rep := fun _ => List Bool
      enc := fun _ => encBits
      rep := fun _ c i => Fin.cases (motive := fun i => Input c i ↪ List Bool)
        ⟨List.ofFn, List.ofFn_injective⟩ (fun _ => ⟨List.ofFn, List.ofFn_injective⟩) i }
  output :=
    { Rep := fun _ => List Bool
      enc := fun _ => encBits
      rep := fun _ _ _ => Function.Embedding.refl _ }
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

/-- The simulator family for a corrupted garbler: draw a fresh coin string for `Gb` and deliver the
garbler's output as the evaluator's last message. -/
@[expose] noncomputable def garblerSim : SimulatorFamily (family G) {0} :=
  fun n c xI yI => do
    let coins ← BitString.sampleList (G.coins n c.fn)
    return singletonView (garblerView c (xI ⟨0, Finset.mem_singleton_self 0⟩) coins
      (yI ⟨0, Finset.mem_singleton_self 0⟩))

variable {G}

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

/-- The word that the garbler's simulator writes from the garbler's input word `x₀`, the coins and
the output `y`: the one-entry table of the garbler's view words. -/
private noncomputable def garblerSimWord (x₀ coins y : List Bool) : List Bool :=
  encPi encBits fun _ : ({0} : Finset (Fin 2)) => encGarblerViewWords ⟨x₀, coins, y⟩

/-- The simulator family `garblerSim` for a corrupted garbler is PPT for `encoding G encFn` when
`G` computes its coin count in polynomial time: it draws `G.coins n c.fn` fair coins. -/
theorem isPPT_garblerSim {encFn : Fn ↪ List Bool}
    (hcoins : ComputableInPolyTime (fun (k, f) => G.coins k f) (encPair encUnary encFn) encUnary) :
    (garblerSim G).IsPPT (encoding G encFn) := by
  have hn : ComputableInPolyTime (fun x : SimInput (family G) {0} => x.secParam)
      (encSimInput (encoding G encFn)) encUnary :=
    encSimInput_secParam_polyTime (encoding G encFn) .id'
  have hfn : ComputableInPolyTime (fun x : SimInput (family G) {0} => x.desc.fn)
      (encSimInput (encoding G encFn)) encFn :=
    encParams_fn_polyTime (encSimInput_desc_polyTime (encoding G encFn) .id')
  have hcount : ComputableInPolyTime
      (fun x : SimInput (family G) {0} => G.coins x.secParam x.desc.fn)
      (encSimInput (encoding G encFn)) encUnary :=
    hcoins.comp (hn.prod hfn)
  have hx₀ := (encoding G encFn).input.encCoalition_apply_polyTime
    (encSimInput_inputs_polyTime (encoding G encFn) .id')
    (⟨0, Finset.mem_singleton_self 0⟩ : ({0} : Finset (Fin 2)))
  have hy := (encoding G encFn).output.encCoalition_apply_polyTime
    (encSimInput_outputs_polyTime (encoding G encFn) .id')
    (⟨0, Finset.mem_singleton_self 0⟩ : ({0} : Finset (Fin 2)))
  have hword : ComputableInPolyTime (fun p : SimInput (family G) {0} × List Bool =>
      garblerSimWord ((encoding G encFn).input.rep p.1.secParam p.1.desc 0
          (p.1.inputs ⟨0, Finset.mem_singleton_self 0⟩)) p.2
        ((encoding G encFn).output.rep p.1.secParam p.1.desc 0
          (p.1.outputs ⟨0, Finset.mem_singleton_self 0⟩)))
      (encPair (encSimInput (encoding G encFn)) encBits) encBits :=
    (ComputableInPolyTime.pi fun _ => (encGarblerViewWords_mk_polyTime
      (hx₀.comp (.fst _ _)) (.snd _ _) (hy.comp (.fst _ _))).encoding_comp).encoding_comp
  refine isPPTOn_iff_encoded.mpr ((IsPPTOn.of_seeded hcount hword).congr fun x => ?_)
  obtain ⟨n, c, xs, ys⟩ := x
  simp only [garblerSim, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure,
    ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  refine congrArg _ (funext fun coins => congrArg PMF.pure ?_)
  refine Eq.trans ?_ ((encoding G encFn).view.encCoalition_singleton n c 0 _).symm
  rfl

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
    (family G).SemiHonestSecure setup {0} (encoding G encFn) := by
  refine ⟨garblerSim G, isPPT_garblerSim hcoins, fun Z _ => ?_⟩
  refine negligible_of_eventually_le negligible_zero ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have h : (family G).realGame setup {0} Z n =
      (family G).idealGame setup {0} (garblerSim G) Z n := by
    simp only [ProtocolFamily.realGame, ProtocolFamily.idealGame,
      idealJoint_garblerSim hproj hcorrect hn]
  rw [h, Game.advantage_self]

end Cslib.Crypto.Protocols.MPC.Yao
