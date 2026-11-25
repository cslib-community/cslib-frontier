/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.Hybrid
public import CslibFrontier.Crypto.Protocols.MPC.Yao.Security

/-!
# Yao's protocol over an oblivious-transfer subprotocol: concrete composition bounds

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem. `Yao.oneSidedProtocol` and
`Yao.protocol` run in the ideal `batchOTWorld` oblivious-transfer hybrid model. Here the ideal
transfer round is replaced by an arbitrary two-party subprotocol `OT` for the batched transfer
(`Protocol.compose`), which gives the protocols whose security Theorem 7 states when `OT` is a
plain-model oblivious-transfer protocol:

* `Yao.composedOneSidedProtocol G n c OT`: the one-sided protocol over `OT`;
* `Yao.composedProtocol G n c OT`: the two-output protocol over `OT`.

By the hybrid argument over the oracle rounds (`semiHonestAdvantage_compose_le_replacementBound`),
Yao's protocols call the batched transfer once, after the garbler's message, so the replacement
bound has one term for every coalition `I`: the expectation, over the parties' coins `r`, of the
semi-honest advantage against `OT` on the query tuple `Yao.transferQueries n c x r` of the explicit
distinguisher `Yao.transferDistinguisher` (`Yao.oneSidedTransferDistinguisher`), which finishes the
protocol from the transfer's answers and runs the given distinguisher
(`Yao.semiHonestAdvantage_composedProtocol_le_transfer`,
`Yao.semiHonestAdvantage_composedOneSidedProtocol_le_transfer`). The query tuple depends on the
garbler's coins, which is why the term is an expectation and not one advantage at a fixed input.

* For a **corrupted garbler** (`I = {0}`), the hybrid garbler simulators `Yao.garblerSim` and
  `Yao.oneSidedGarblerSim` are exact, so the outer hybrid advantage vanishes and only the expected
  transfer advantage remains (`Yao.semiHonestAdvantage_composedProtocol_garbler_le_transfer`,
  `Yao.semiHonestAdvantage_composedOneSidedProtocol_garbler_le_transfer`).
* For a **corrupted evaluator** (`I = {1}`) in `Yao.protocol`, with the hybrid evaluator simulator
  `Yao.evaluatorSim G Φ S` built from a garbling simulator `S` for side information `Φ`, the outer
  hybrid advantage equals the `prv.sim` advantage against `S n` of the fixed-instance reduction
  `Yao.evaluatorDistinguisherToPrvSim` (`Yao.semiHonestAdvantage_protocol_evaluator_eq`, derived
  directly from `Yao.idealGame_evaluator_eq` and `Yao.realGame_evaluator_eq` in
  `CslibFrontier/Crypto/Protocols/MPC/Yao/Security.lean`). Composing gives the `prv.sim` advantage
  of that reduction applied to `composeDistinguisher` plus the expected transfer advantage
  (`Yao.semiHonestAdvantage_composedProtocol_evaluator_le_transfer`).

## What is not proved

These bounds are concrete and stated per instance (a fixed parameter, input tuple and
distinguisher), or, for the two `bind_…` equalities, under a sampled first stage. They leave the
expected advantage against the transfer subprotocol and, for a
corrupted evaluator, the `prv.sim` advantage of the reduction as explicit terms. The following
parts of Theorem 7 remain open (#6045):

* a plain-model protocol for the batched transfer of token words with a proof of its semi-honest
  security. The DDH protocol of
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTProbFamily_semiHonestSecure` transfers one group
  element rather than a batch of token words, and no adapter is built here;
* the asymptotic statement `ProtocolFamily.SemiHonestSecure` for the composed family, with strict
  PPT certificates for the composed simulators and for the reductions. In particular the
  per-instance reductions `Yao.evaluatorDistinguisherToPrvSim`, `Yao.transferDistinguisher` and
  `Yao.oneSidedTransferDistinguisher` come with no efficiency certificate here, the transfer
  distinguishers depend on the garbler's coins, which an asymptotic reduction has to fix as
  advice, and no negligible bound on the `prv.sim` advantage is derived from an assumption on `G`;
  the uniform reduction with a PPT certificate in the hybrid model is `Yao.evaluatorToPrvSim`.

The locators for [LindellPinkas2009] are those recorded in
`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Yao.composedOneSidedProtocol`,
  `Cslib.Crypto.Protocols.MPC.Yao.composedProtocol`: Yao's protocols with the batched transfer run
  by a subprotocol.
* `Cslib.Crypto.Protocols.MPC.Yao.evaluatorDistinguisherToPrvSim`: the reduction from a
  distinguisher of a corrupted evaluator's view at a fixed instance to a `prv.sim` adversary.
* `Cslib.Crypto.Protocols.MPC.Yao.evaluatorEnvToPrvSim`: the same reduction for `Yao.protocol`
  when a sampled first stage, run by the adversary, chooses the inputs and the distinguisher.
* `Cslib.Crypto.Protocols.MPC.Yao.transferQueries`: the query tuple of the one batched transfer.
* `Cslib.Crypto.Protocols.MPC.Yao.oneSidedTransferDistinguisher`,
  `Cslib.Crypto.Protocols.MPC.Yao.transferDistinguisher`: the reductions from a distinguisher of
  the composed protocol to a distinguisher of the transfer subprotocol.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_protocol_evaluator_eq`: against a corrupted
  evaluator of `Yao.protocol`, the advantage at a fixed instance is the `prv.sim` advantage of
  `Yao.evaluatorDistinguisherToPrvSim`.
* `Cslib.Crypto.Protocols.MPC.Yao.eval_idealJoint_evaluatorSim_bind_eq_prvSimExperiment`,
  `Cslib.Crypto.Protocols.MPC.Yao.realJoint_protocol_evaluator_bind_eq_prvSimExperiment`: the two
  equalities of games behind it for `Yao.protocol`: the ideal and the real execution followed by
  the distinguisher are the two `prv.sim` experiments of the reduction.
* `Cslib.Crypto.Protocols.MPC.Yao.bind_idealJoint_evaluatorSim_eq_prvSimExperiment`,
  `Cslib.Crypto.Protocols.MPC.Yao.bind_realJoint_protocol_evaluator_eq_prvSimExperiment`: the same
  equalities under a sampled first stage, for the one adversary `Yao.evaluatorEnvToPrvSim`.
* `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedOneSidedProtocol_le_transfer`,
  `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedProtocol_le_transfer`: for every
  coalition, the advantage is at most the advantage of `composeDistinguisher` against the hybrid
  protocol plus the expected advantage of the transfer distinguisher against the subprotocol.
* `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedOneSidedProtocol_garbler_le_transfer`,
  `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedProtocol_garbler_le_transfer`,
  `Cslib.Crypto.Protocols.MPC.Yao.semiHonestAdvantage_composedProtocol_evaluator_le_transfer`:
  corrupted-garbler and corrupted-evaluator bounds with `oneSidedGarblerSim`, `garblerSim` and
  `evaluatorSim`.

## References

* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib.Crypto.Garbling Cslib.Probability

variable {Fn Λ : Type} (G : Scheme Fn)

/-- **One-sided Yao's protocol over a transfer subprotocol**: `Yao.oneSidedProtocol G n c` with its
batched oblivious-transfer round run by the two-party subprotocol `OT` in the oracle model `spec₂`
(`noOracleSpec` for a plain-model `OT`). The garbler is the sender of `OT` and the evaluator its
receiver. -/
noncomputable abbrev composedOneSidedProtocol (n : ℕ) (c : Params G) {spec₂ : MultiOracleSpec}
    {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ())) :
    Protocol 2 spec₂ (Schedule.compose (fun _ => sc₂) (oneSidedSchedule c)) (Input c)
      (Schedule.ComposedCoins (fun _ => Coins₂) Coins (oneSidedSchedule c)) (fun _ => List Bool) :=
  (oneSidedProtocol G n c).compose fun _ => OT

/-- **Yao's protocol over a transfer subprotocol** (Protocol 2 of [LindellPinkas2009], with the
transfers run by one subprotocol for the whole batch): `Yao.protocol G n c` with its batched
oblivious-transfer round run by the two-party subprotocol `OT` in the oracle model `spec₂`
(`noOracleSpec` for a plain-model `OT`). The garbler is the sender of `OT` and the evaluator its
receiver. -/
noncomputable abbrev composedProtocol (n : ℕ) (c : Params G) {spec₂ : MultiOracleSpec}
    {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ())) :
    Protocol 2 spec₂ (Schedule.compose (fun _ => sc₂) (schedule c)) (Input c)
      (Schedule.ComposedCoins (fun _ => Coins₂) Coins (schedule c)) (fun _ => List Bool) :=
  (protocol G n c).compose fun _ => OT

variable {G}

/-- The hybrid garbler simulator of the one-sided protocol is exact: at every parameter `n ≥ 1`,
when `G` is correct with a projective encoding, every distinguisher has semi-honest advantage zero
against `Yao.oneSidedProtocol G n c` for the coalition `{0}` with `Yao.oneSidedGarblerSim`. -/
private theorem semiHonestAdvantage_oneSidedProtocol_garbler_eq_zero
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G) (x : (i : Fin 2) → Input c i)
    (D : ((i : ({0} : Finset (Fin 2))) → PartyView (Input c) Coins (oneSidedSchedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) :
    semiHonestAdvantage (oneSidedProtocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
      (oneSidedFunctionality G c) {0} (oneSidedGarblerSim G n c) x D = 0 :=
  (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ _).mpr
    (idealJoint_oneSidedGarblerSim hproj hcorrect hn c x) D

/-- The hybrid garbler simulator is exact: at every parameter `n ≥ 1`, when `G` is correct with a
projective encoding, every distinguisher has semi-honest advantage zero against
`Yao.protocol G n c` for the coalition `{0}` with `Yao.garblerSim`. -/
private theorem semiHonestAdvantage_protocol_garbler_eq_zero (hproj : G.encode = projectiveEncode)
    (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n) (c : Params G) (x : (i : Fin 2) → Input c i)
    (D : ((i : ({0} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) :
    semiHonestAdvantage (protocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
      (functionality G c) {0} (garblerSim G n c) x D = 0 :=
  (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ _).mpr (idealJoint_garblerSim hproj hcorrect hn c x) D

/-! ### Corrupted evaluator: the hybrid term is simulation privacy of the garbling scheme -/

/-- **The reduction to simulation privacy at a fixed instance**, for a corrupted evaluator of
`Yao.protocol G n c`: from a distinguisher `D` of the evaluator's view and the outputs on the input
tuple `x`, the `prv.sim` adversary that queries `c.fn` on the garbler's bits followed by the
evaluator's, reads the evaluator's view from the view `(F, X, d)` that it is given
(`viewOfPrvView`) and runs `D` on this view with the function's output as both parties' outputs.
It keeps no state. This is `Yao.evaluatorToPrvSim` at fixed public parameters and inputs. -/
@[expose] noncomputable def evaluatorDistinguisherToPrvSim (c : Params G)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) : PrvSimAdversary Fn Unit where
  choose _ := pure (⟨c.fn, circuitInput x⟩, ())
  guess _ V := D (singletonView (viewOfPrvView c (x 1) (V.getD ⟨[], [], []⟩)),
    fun _ => G.ev c.fn (circuitInput x))

open Classical in
/-- Fixed-instance environment on `Yao.family G` concentrating on `(c, x)` and running `D`, used to
specialize `Yao.idealGame_evaluator_eq` and `Yao.realGame_evaluator_eq` from
`CslibFrontier/Crypto/Protocols/MPC/Yao/Security.lean`. -/
private noncomputable def fixedEvaluatorEnv (c : Params G) (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) : Environment (family G) {1} where
  choose _ d :=
    if h : d = c then pure ⟨h ▸ x, []⟩
    else pure ⟨fun i => Fin.cases (fun _ => false) (fun _ _ => false) i, []⟩
  guess _ d _ r :=
    if h : d = c then D (h ▸ r) else pure false

private theorem eval_prvSimExperiment_evaluatorDistinguisherToPrvSim (n : ℕ) (c : Params G)
    (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) (b : Bool) :
    ProbComp.eval (prvSimExperiment G Φ n (S n) (evaluatorDistinguisherToPrvSim c x D) b) =
      ProbComp.eval (prvSimExperiment G Φ n (S n)
        (evaluatorToPrvSim (fun _ => pure c) (fixedEvaluatorEnv c x D) n) b) := by
  simp only [prvSimExperiment, evaluatorDistinguisherToPrvSim, evaluatorToPrvSim, fixedEvaluatorEnv,
    ↓reduceDIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
    BitString.ofList_ofFn (n := c.evaluatorLen) (x 1)]

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): original bookkeeping at a fixed instance, stated as an equality of games.

The ideal execution of `Yao.functionality G c` for the coalition `{1}` with the simulator
`Yao.evaluatorSim G Φ S n c`, followed by a distinguisher `D`, is the simulated `prv.sim`
experiment (`false`) of the reduction `Yao.evaluatorDistinguisherToPrvSim c x D` against `S n`.
Nothing is assumed about `G`, `S` or `D`, and no efficiency certificate for the reduction is
claimed. -/
theorem eval_idealJoint_evaluatorSim_bind_eq_prvSimExperiment (n : ℕ) (c : Params G)
    (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) :
    ProbComp.eval (idealJoint (functionality G c) {1} (evaluatorSim G Φ S n c) x >>= D) =
      ProbComp.eval
        (prvSimExperiment G Φ n (S n) (evaluatorDistinguisherToPrvSim c x D) false) := by
  rw [eval_prvSimExperiment_evaluatorDistinguisherToPrvSim,
    ← idealGame_evaluator_eq (fun _ => pure c) (fixedEvaluatorEnv c x D) Φ S n]
  simp only [ProtocolFamily.idealGame, family, fixedEvaluatorEnv, ↓reduceDIte, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.pure_bind]

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): original bookkeeping at a fixed instance, stated as an equality of games; the transfers
are the ideal `batchOTWorld`.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the real execution of
the hybrid protocol `Yao.protocol G n c` for the coalition `{1}`, followed by a distinguisher
`D`, is the real `prv.sim` experiment (`true`) of the reduction
`Yao.evaluatorDistinguisherToPrvSim c x D`. That experiment does not run the simulator, so `Φ`
and `S` only name it. Nothing is assumed about `D`, and no efficiency certificate for the
reduction is claimed. -/
theorem realJoint_protocol_evaluator_bind_eq_prvSimExperiment
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) :
    ((protocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {1} x).bind
        (fun r => ProbComp.eval (D r)) =
      ProbComp.eval
        (prvSimExperiment G Φ n (S n) (evaluatorDistinguisherToPrvSim c x D) true) := by
  rw [eval_prvSimExperiment_evaluatorDistinguisherToPrvSim,
    ← realGame_evaluator_eq hproj hcorrect hn (fun _ => pure c) (fixedEvaluatorEnv c x D) Φ S]
  simp only [ProtocolFamily.realGame, family, fixedEvaluatorEnv, ↓reduceDIte, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.pure_bind]

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): the transfers are the ideal `batchOTWorld` and the statement is at a fixed instance.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage of any distinguisher `D` against the hybrid protocol `Yao.protocol G n c` for the
coalition `{1}`, with the simulator `Yao.evaluatorSim G Φ S` built from a garbling simulator `S`
for the side information `Φ`, equals the `prv.sim` advantage of the reduction
`Yao.evaluatorDistinguisherToPrvSim c x D` against `S n`. Nothing is assumed about `S` or `D`. -/
theorem semiHonestAdvantage_protocol_evaluator_eq (hproj : G.encode = projectiveEncode)
    (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n) (c : Params G) (Φ : SideInfo Fn Λ)
    (S : ℕ → PrvSimulator Λ) (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) :
    semiHonestAdvantage (protocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
        (functionality G c) {1} (evaluatorSim G Φ S n c) x D =
      prvSimAdvantage G Φ n (S n) (evaluatorDistinguisherToPrvSim c x D) := by
  rw [semiHonestAdvantage, eval_idealJoint_evaluatorSim_bind_eq_prvSimExperiment n c Φ S x D,
    realJoint_protocol_evaluator_bind_eq_prvSimExperiment hproj hcorrect hn c Φ S x D]
  rfl

/-- **The reduction to simulation privacy with a sampled first stage**, for a corrupted evaluator
of `Yao.protocol G n c`: the `prv.sim` adversary that first runs the program `e` itself, to sample
an index `a` (a group description, say) on which the input tuple `x a` and the distinguisher `D a`
may depend, then queries `c.fn` on the garbler's bits followed by the evaluator's, keeps `a` as
its state and guesses as `Yao.evaluatorDistinguisherToPrvSim c (x a) (D a)` does. It is one
adversary for the two `prv.sim` experiments, so the absolute value of its advantage is outside the
expectation over `a`. No efficiency certificate for it is claimed. -/
@[expose] noncomputable def evaluatorEnvToPrvSim {δ : Type} (c : Params G) (e : ProbComp δ)
    (x : δ → (i : Fin 2) → Input c i)
    (D : δ → ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) : PrvSimAdversary Fn δ where
  choose _ := do let a ← e; pure (⟨c.fn, circuitInput (x a)⟩, a)
  guess a V := (evaluatorDistinguisherToPrvSim c (x a) (D a)).guess () V

/-- Either `prv.sim` experiment of `Yao.evaluatorEnvToPrvSim c e x D` samples `a` from `e` and
runs the same experiment of the fixed-instance reduction
`Yao.evaluatorDistinguisherToPrvSim c (x a) (D a)`. -/
private theorem eval_prvSimExperiment_evaluatorEnvToPrvSim {δ : Type} (k : ℕ) (c : Params G)
    (Φ : SideInfo Fn Λ) (S : PrvSimulator Λ) (e : ProbComp δ) (x : δ → (i : Fin 2) → Input c i)
    (D : δ → ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) (b : Bool) :
    ProbComp.eval (prvSimExperiment G Φ k S (evaluatorEnvToPrvSim c e x D) b) =
      (ProbComp.eval e).bind fun a => ProbComp.eval
        (prvSimExperiment G Φ k S (evaluatorDistinguisherToPrvSim c (x a) (D a)) b) := by
  simp only [prvSimExperiment, evaluatorEnvToPrvSim, evaluatorDistinguisherToPrvSim, bind_assoc,
    pure_bind, ProbComp.eval_bind]

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): original bookkeeping under a sampled first stage, stated as an equality of games.

Sampling `a` from `e` and then running the ideal execution of `Yao.functionality G c` for the
coalition `{1}` on the inputs `x a` with the simulator `Yao.evaluatorSim G Φ S n c`, followed by
the distinguisher `D a`, is the simulated `prv.sim` experiment (`false`) of the adversary
`Yao.evaluatorEnvToPrvSim c e x D` against `S n`. The first stage `e` is a program run by the
adversary. Nothing is assumed about `G`, `S`, `e`, `x` or `D`, and no efficiency certificate for
the adversary is claimed. -/
theorem bind_idealJoint_evaluatorSim_eq_prvSimExperiment {δ : Type} (n : ℕ) (c : Params G)
    (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) (e : ProbComp δ)
    (x : δ → (i : Fin 2) → Input c i)
    (D : δ → ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) :
    (ProbComp.eval e).bind (fun a => ProbComp.eval
        (idealJoint (functionality G c) {1} (evaluatorSim G Φ S n c) (x a) >>= D a)) =
      ProbComp.eval (prvSimExperiment G Φ n (S n) (evaluatorEnvToPrvSim c e x D) false) := by
  rw [eval_prvSimExperiment_evaluatorEnvToPrvSim n c Φ (S n) e x D false]
  exact congrArg (PMF.bind _) (funext fun a =>
    eval_idealJoint_evaluatorSim_bind_eq_prvSimExperiment n c Φ S (x a) (D a))

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): original bookkeeping under a sampled first stage, stated as an equality of games; the
transfers are the ideal `batchOTWorld`.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, sampling `a` from `e`
and then running the real execution of the hybrid protocol `Yao.protocol G n c` for the coalition
`{1}` on the inputs `x a`, followed by the distinguisher `D a`, is the real `prv.sim` experiment
`true` of the adversary `Yao.evaluatorEnvToPrvSim c e x D`. That experiment does not run the
simulator, so `Φ` and `S` only name it. The first stage `e` is a program run by the adversary.
Nothing is assumed about `e`, `x` or `D`, and no efficiency certificate for the adversary is
claimed. -/
theorem bind_realJoint_protocol_evaluator_eq_prvSimExperiment {δ : Type}
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) (e : ProbComp δ)
    (x : δ → (i : Fin 2) → Input c i)
    (D : δ → ((i : ({1} : Finset (Fin 2))) → PartyView (Input c) Coins (schedule c) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool) :
    (ProbComp.eval e).bind (fun a =>
        ((protocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) {1} (x a)).bind
          fun r => ProbComp.eval (D a r)) =
      ProbComp.eval (prvSimExperiment G Φ n (S n) (evaluatorEnvToPrvSim c e x D) true) := by
  rw [eval_prvSimExperiment_evaluatorEnvToPrvSim n c Φ (S n) e x D true]
  exact congrArg (PMF.bind _) (funext fun a =>
    realJoint_protocol_evaluator_bind_eq_prvSimExperiment hproj hcorrect hn c Φ S (x a) (D a))

/-! ### The replacement gap: one distinguisher against the transfer subprotocol -/

section Transfer

open scoped ENNReal

variable {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}

/-- The query tuple of the one batched transfer of `Yao.protocol G n c` and
`Yao.oneSidedProtocol G n c` on the inputs `x` with the coins `r`: the garbler offers both tokens
of each of the evaluator's input bits, computed from its coins `r 0` (`Yao.garblerOffer`), and the
evaluator chooses with its input bits `x 1`. -/
@[expose] def transferQueries (n : ℕ) (c : Params G) (x : (i : Fin 2) → Input c i)
    (r : (i : Fin 2) → Coins i) (s : Fin 2) :
    (batchOTSpec c.evaluatorLen (List Bool)).Query () s :=
  transferQuery G n c s ((x s, r s),
    Round.deliverMessage (spec := batchOTSpec c.evaluatorLen (List Bool)) (sender := 0)
      (receiver := 1) (garblerMessage G n c (x 0) (r 0)) s)

/-- **The reduction to the transfer subprotocol**, for `Yao.oneSidedProtocol G n c` on the inputs
`x` with the coins `r`: from a distinguisher `D` of the coalition `I`'s views of the composed
protocol and the outputs, the distinguisher of the views of the corrupted slots and the answers of
the transfer subprotocol that computes the parties' outputs from the answers, puts the garbler's
message and the given transfer views into the coalition's views and runs `D`. It is
`Composition.roundDistinguisher` at the transfer round, after which the protocol ends. -/
@[expose] noncomputable def oneSidedTransferDistinguisher (n : ℕ) (c : Params G)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → Input c i) (r : (i : Fin 2) → Coins i)
    (D : ((i : I) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (oneSidedSchedule c))
        (Schedule.compose (fun _ => sc₂) (oneSidedSchedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    ((s : Composition.subCoalition (Function.Embedding.refl (Fin 2)) I) →
        PartyView ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂ sc₂ s) ×
      ((s : Fin 2) → (batchOTSpec c.evaluatorLen (List Bool)).Answer () s) → ProbComp Bool :=
  Composition.roundDistinguisher (sc₂ := fun _ => sc₂) (Coins₂ := fun _ => Coins₂)
    (batchOTWorld c.evaluatorLen (List Bool)) S₂ I
    (State := fun i => (Input c i × Coins i) ×
      (Round.message (spec := batchOTSpec c.evaluatorLen (List Bool)) 0 1 Message).Received i)
    (op := ()) (parties := Function.Embedding.refl (Fin 2))
    (.done (oneSidedFinalOutput G c))
    (fun i => ((x i, r i),
      Round.deliverMessage (spec := batchOTSpec c.evaluatorLen (List Bool)) (sender := 0)
        (receiver := 1) (garblerMessage G n c (x 0) (r 0)) i))
    (fun res => D (fun i : I => ⟨x i.1, (r i.1, (res.1 i).1),
      (Round.deliverMessage (spec := spec₂) (sender := 0) (receiver := 1)
        (garblerMessage G n c (x 0) (r 0)) i.1, (res.1 i).2)⟩, res.2))

/-- **The reduction to the transfer subprotocol**, for `Yao.protocol G n c` on the inputs `x` with
the coins `r`: from a distinguisher `D` of the coalition `I`'s views of the composed protocol and
the outputs, the distinguisher of the views of the corrupted slots and the answers of the transfer
subprotocol that finishes the protocol from the answers (the evaluator's message to the garbler and
the outputs), puts the garbler's message and the given transfer views into the coalition's views
and runs `D`. It is `Composition.roundDistinguisher` at the transfer round, after which the
protocol makes no oracle call. -/
@[expose] noncomputable def transferDistinguisher (n : ℕ) (c : Params G)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → Input c i) (r : (i : Fin 2) → Coins i)
    (D : ((i : I) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (schedule c))
        (Schedule.compose (fun _ => sc₂) (schedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    ((s : Composition.subCoalition (Function.Embedding.refl (Fin 2)) I) →
        PartyView ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂ sc₂ s) ×
      ((s : Fin 2) → (batchOTSpec c.evaluatorLen (List Bool)).Answer () s) → ProbComp Bool :=
  Composition.roundDistinguisher (sc₂ := fun _ => sc₂) (Coins₂ := fun _ => Coins₂)
    (batchOTWorld c.evaluatorLen (List Bool)) S₂ I
    (State := fun i => (Input c i × Coins i) ×
      (Round.message (spec := batchOTSpec c.evaluatorLen (List Bool)) 0 1 Message).Received i)
    (op := ()) (parties := Function.Embedding.refl (Fin 2))
    (.message (fun (((_, msg), ot) : AfterTransfer c 1) => evaluatorOutput G (msg rfl) (ot 1 rfl))
      (.done (finalOutput G c)))
    (fun i => ((x i, r i),
      Round.deliverMessage (spec := batchOTSpec c.evaluatorLen (List Bool)) (sender := 0)
        (receiver := 1) (garblerMessage G n c (x 0) (r 0)) i))
    (fun res => D (fun i : I => ⟨x i.1, (r i.1, (res.1 i).1),
      (Round.deliverMessage (spec := spec₂) (sender := 0) (receiver := 1)
        (garblerMessage G n c (x 0) (r 0)) i.1, (res.1 i).2)⟩, res.2))

/-- On the steps of `Yao.oneSidedProtocol G n c`, the hybrid bound `Composition.replacementBound`
has one term, for the one transfer round: the semi-honest advantage of
`Yao.oneSidedTransferDistinguisher` against the transfer subprotocol `OT` on the query tuple
`Yao.transferQueries n c x r`. -/
private theorem replacementBound_oneSidedProtocol (n : ℕ) (c : Params G)
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → Input c i) (r : (i : Fin 2) → Coins i)
    (D : ((i : I) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (oneSidedSchedule c))
        (Schedule.compose (fun _ => sc₂) (oneSidedSchedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    Composition.replacementBound (batchOTWorld c.evaluatorLen (List Bool)) W₂ (fun _ => OT) S₂ I
        (oneSidedProtocol G n c).steps (fun i => (x i, r i))
        (fun res => D (fun i : I => ⟨x i.1, (r i.1, (res.1 i).1), (res.1 i).2⟩, res.2)) =
      (semiHonestAdvantage OT W₂ (batchOTFunctionality c.evaluatorLen (List Bool))
        (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I)
        (S₂ () (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I))
        (transferQueries n c x r) (oneSidedTransferDistinguisher n c S₂ I x r D) : ℝ≥0∞) := by
  simp only [oneSidedProtocol, Composition.replacementBound, mul_zero, tsum_zero, add_zero]
  rfl

/-- On the steps of `Yao.protocol G n c`, the hybrid bound `Composition.replacementBound` has one
term, for the one transfer round: the semi-honest advantage of `Yao.transferDistinguisher` against
the transfer subprotocol `OT` on the query tuple `Yao.transferQueries n c x r`. -/
private theorem replacementBound_protocol (n : ℕ) (c : Params G)
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → Input c i) (r : (i : Fin 2) → Coins i)
    (D : ((i : I) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (schedule c))
        (Schedule.compose (fun _ => sc₂) (schedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    Composition.replacementBound (batchOTWorld c.evaluatorLen (List Bool)) W₂ (fun _ => OT) S₂ I
        (protocol G n c).steps (fun i => (x i, r i))
        (fun res => D (fun i : I => ⟨x i.1, (r i.1, (res.1 i).1), (res.1 i).2⟩, res.2)) =
      (semiHonestAdvantage OT W₂ (batchOTFunctionality c.evaluatorLen (List Bool))
        (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I)
        (S₂ () (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I))
        (transferQueries n c x r) (transferDistinguisher n c S₂ I x r D) : ℝ≥0∞) := by
  simp only [protocol, Composition.replacementBound, mul_zero, tsum_zero, add_zero]
  rfl

/-- Step towards [LindellPinkas2009], Theorem 7, not the cited result (#6045): a concrete bound at a
fixed instance for the one-sided protocol, with the advantage against the transfer subprotocol and
the advantage against the hybrid protocol left as terms.

For every coalition `I`, the semi-honest advantage against `Yao.composedOneSidedProtocol G n c OT`
with `composeSim (oneSidedProtocol G n c) S₁ S₂` is at most the advantage of `composeDistinguisher`
against the hybrid protocol `Yao.oneSidedProtocol G n c` with `S₁`, plus the expectation, over the
parties' coins `r`, of the semi-honest advantage of `Yao.oneSidedTransferDistinguisher` against
`OT`, for the batched-transfer functionality with the simulator `S₂ ()`, on the query tuple
`Yao.transferQueries n c x r`. Nothing is assumed about `G`, `OT`, the simulators or `D`. -/
theorem semiHonestAdvantage_composedOneSidedProtocol_le_transfer (n : ℕ) (c : Params G)
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂) (I : Finset (Fin 2))
    (S₁ : CoalitionSimulator (oneSidedSchedule c) (Input c) Coins (fun _ => List Bool) I)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : I) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (oneSidedSchedule c))
        (Schedule.compose (fun _ => sc₂) (oneSidedSchedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    (semiHonestAdvantage (composedOneSidedProtocol G n c OT) W₂ (oneSidedFunctionality G c) I
        (composeSim (oneSidedProtocol G n c) S₁ S₂) x D : ℝ≥0∞) ≤
      semiHonestAdvantage (oneSidedProtocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
          (oneSidedFunctionality G c) I S₁ x
          (composeDistinguisher (oneSidedProtocol G n c) S₂ I x D) +
        ∑' r, ProbComp.eval (OracleComp.pi (oneSidedProtocol G n c).sampleCoins) r *
          (semiHonestAdvantage OT W₂ (batchOTFunctionality c.evaluatorLen (List Bool))
            (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I)
            (S₂ () (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I))
            (transferQueries n c x r) (oneSidedTransferDistinguisher n c S₂ I x r D) : ℝ≥0∞) :=
  (semiHonestAdvantage_compose_le_replacementBound (oneSidedProtocol G n c)
    (batchOTWorld c.evaluatorLen (List Bool)) W₂ (oneSidedFunctionality G c) I S₁ (fun _ => OT) S₂
    x D).trans (add_le_add le_rfl (le_of_eq (tsum_congr fun r =>
      congrArg (ProbComp.eval (OracleComp.pi (oneSidedProtocol G n c).sampleCoins) r * ·)
        (replacementBound_oneSidedProtocol n c OT W₂ S₂ I x r D))))

/-- Step towards [LindellPinkas2009], Theorem 7, not the cited result (#6045): a concrete bound at a
fixed instance, with the advantage against the transfer subprotocol and the advantage against the
hybrid protocol left as terms.

For every coalition `I`, the semi-honest advantage against `Yao.composedProtocol G n c OT` with
`composeSim (protocol G n c) S₁ S₂` is at most the advantage of `composeDistinguisher` against the
hybrid protocol `Yao.protocol G n c` with `S₁`, plus the expectation, over the parties' coins `r`,
of the semi-honest advantage of `Yao.transferDistinguisher` against `OT`, for the batched-transfer
functionality with the simulator `S₂ ()`, on the query tuple `Yao.transferQueries n c x r`. Nothing
is assumed about `G`, `OT`, the simulators or `D`. -/
theorem semiHonestAdvantage_composedProtocol_le_transfer (n : ℕ) (c : Params G)
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂) (I : Finset (Fin 2))
    (S₁ : CoalitionSimulator (schedule c) (Input c) Coins (fun _ => List Bool) I)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : I) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (schedule c))
        (Schedule.compose (fun _ => sc₂) (schedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    (semiHonestAdvantage (composedProtocol G n c OT) W₂ (functionality G c) I
        (composeSim (protocol G n c) S₁ S₂) x D : ℝ≥0∞) ≤
      semiHonestAdvantage (protocol G n c) (batchOTWorld c.evaluatorLen (List Bool))
          (functionality G c) I S₁ x (composeDistinguisher (protocol G n c) S₂ I x D) +
        ∑' r, ProbComp.eval (OracleComp.pi (protocol G n c).sampleCoins) r *
          (semiHonestAdvantage OT W₂ (batchOTFunctionality c.evaluatorLen (List Bool))
            (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I)
            (S₂ () (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I))
            (transferQueries n c x r) (transferDistinguisher n c S₂ I x r D) : ℝ≥0∞) :=
  (semiHonestAdvantage_compose_le_replacementBound (protocol G n c)
    (batchOTWorld c.evaluatorLen (List Bool)) W₂ (functionality G c) I S₁ (fun _ => OT) S₂
    x D).trans (add_le_add le_rfl (le_of_eq (tsum_congr fun r =>
      congrArg (ProbComp.eval (OracleComp.pi (protocol G n c).sampleCoins) r * ·)
        (replacementBound_protocol n c OT W₂ S₂ I x r D))))

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted garbler in the one-sided protocol,
not the cited result (#6045): a concrete bound at a fixed instance that leaves the advantage
against the transfer subprotocol as a term.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage against `Yao.composedOneSidedProtocol G n c OT` for the coalition `{0}`, with the
simulator composed from `Yao.oneSidedGarblerSim G n c` and any simulators `S₂` for `OT`, is at most
the expectation, over the parties' coins `r`, of the semi-honest advantage of
`Yao.oneSidedTransferDistinguisher` against `OT` on `Yao.transferQueries n c x r`. -/
theorem semiHonestAdvantage_composedOneSidedProtocol_garbler_le_transfer
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G)
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({0} : Finset (Fin 2))) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (oneSidedSchedule c))
        (Schedule.compose (fun _ => sc₂) (oneSidedSchedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    (semiHonestAdvantage (composedOneSidedProtocol G n c OT) W₂ (oneSidedFunctionality G c) {0}
        (composeSim (oneSidedProtocol G n c) (oneSidedGarblerSim G n c) S₂) x D : ℝ≥0∞) ≤
      ∑' r, ProbComp.eval (OracleComp.pi (oneSidedProtocol G n c).sampleCoins) r *
        (semiHonestAdvantage OT W₂ (batchOTFunctionality c.evaluatorLen (List Bool))
          (Composition.subCoalition (Function.Embedding.refl (Fin 2)) {0})
          (S₂ () (Composition.subCoalition (Function.Embedding.refl (Fin 2)) {0}))
          (transferQueries n c x r) (oneSidedTransferDistinguisher n c S₂ {0} x r D) : ℝ≥0∞) := by
  have h := semiHonestAdvantage_composedOneSidedProtocol_le_transfer n c OT W₂ {0}
    (oneSidedGarblerSim G n c) S₂ x D
  rwa [semiHonestAdvantage_oneSidedProtocol_garbler_eq_zero hproj hcorrect hn, ENNReal.coe_zero,
    zero_add] at h

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted garbler, not the cited result
(#6045): a concrete bound at a fixed instance that leaves the advantage against the transfer
subprotocol as a term.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage against `Yao.composedProtocol G n c OT` for the coalition `{0}`, with the simulator
composed from `Yao.garblerSim G n c` and any simulators `S₂` for `OT`, is at most the expectation,
over the parties' coins `r`, of the semi-honest advantage of `Yao.transferDistinguisher` against
`OT` on the query tuple `Yao.transferQueries n c x r`. Nothing is assumed about `OT`, `S₂` or
`D`. -/
theorem semiHonestAdvantage_composedProtocol_garbler_le_transfer
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G)
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({0} : Finset (Fin 2))) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (schedule c))
        (Schedule.compose (fun _ => sc₂) (schedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    (semiHonestAdvantage (composedProtocol G n c OT) W₂ (functionality G c) {0}
        (composeSim (protocol G n c) (garblerSim G n c) S₂) x D : ℝ≥0∞) ≤
      ∑' r, ProbComp.eval (OracleComp.pi (protocol G n c).sampleCoins) r *
        (semiHonestAdvantage OT W₂ (batchOTFunctionality c.evaluatorLen (List Bool))
          (Composition.subCoalition (Function.Embedding.refl (Fin 2)) {0})
          (S₂ () (Composition.subCoalition (Function.Embedding.refl (Fin 2)) {0}))
          (transferQueries n c x r) (transferDistinguisher n c S₂ {0} x r D) : ℝ≥0∞) := by
  have h := semiHonestAdvantage_composedProtocol_le_transfer n c OT W₂ {0}
    (garblerSim G n c) S₂ x D
  rwa [semiHonestAdvantage_protocol_garbler_eq_zero hproj hcorrect hn, ENNReal.coe_zero,
    zero_add] at h

/-- Step towards [LindellPinkas2009], Theorem 7 for a corrupted evaluator, not the cited result
(#6045): a concrete bound at a fixed instance that leaves the `prv.sim` advantage of the reduction
and the advantage against the transfer subprotocol as terms.

At every parameter `n ≥ 1`, when `G` is correct with a projective encoding, the semi-honest
advantage against `Yao.composedProtocol G n c OT` for the coalition `{1}`, with the simulator
composed from `Yao.evaluatorSim G Φ S n c` and any simulators `S₂` for `OT`, is at most the
`prv.sim` advantage against the garbling simulator `S n` of the explicit reduction
`Yao.evaluatorDistinguisherToPrvSim` applied to `composeDistinguisher`, plus the expectation, over
the parties' coins `r`, of the semi-honest advantage of `Yao.transferDistinguisher` against `OT` on
the query tuple `Yao.transferQueries n c x r`. Nothing is assumed about `S`, `S₂`, `OT` or `D`. -/
theorem semiHonestAdvantage_composedProtocol_evaluator_le_transfer
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n)
    (c : Params G) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ)
    (OT : Protocol 2 spec₂ sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
      ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()))
    (W₂ : MultiOracleWorld spec₂)
    (S₂ : (_ : Unit) → (J : Finset (Fin 2)) →
      CoalitionSimulator sc₂ ((batchOTSpec c.evaluatorLen (List Bool)).Query ()) Coins₂
        ((batchOTSpec c.evaluatorLen (List Bool)).Answer ()) J)
    (x : (i : Fin 2) → Input c i)
    (D : ((i : ({1} : Finset (Fin 2))) →
      PartyView (Input c) (Schedule.ComposedCoins (fun _ => Coins₂) Coins (schedule c))
        (Schedule.compose (fun _ => sc₂) (schedule c)) i) × ((i : Fin 2) → List Bool) →
        ProbComp Bool) :
    (semiHonestAdvantage (composedProtocol G n c OT) W₂ (functionality G c) {1}
        (composeSim (protocol G n c) (evaluatorSim G Φ S n c) S₂) x D : ℝ≥0∞) ≤
      prvSimAdvantage G Φ n (S n) (evaluatorDistinguisherToPrvSim c x
          (composeDistinguisher (protocol G n c) S₂ {1} x D)) +
        ∑' r, ProbComp.eval (OracleComp.pi (protocol G n c).sampleCoins) r *
          (semiHonestAdvantage OT W₂ (batchOTFunctionality c.evaluatorLen (List Bool))
            (Composition.subCoalition (Function.Embedding.refl (Fin 2)) {1})
            (S₂ () (Composition.subCoalition (Function.Embedding.refl (Fin 2)) {1}))
            (transferQueries n c x r) (transferDistinguisher n c S₂ {1} x r D) : ℝ≥0∞) := by
  have h := semiHonestAdvantage_composedProtocol_le_transfer n c OT W₂ {1}
    (evaluatorSim G Φ S n c) S₂ x D
  rwa [semiHonestAdvantage_protocol_evaluator_eq hproj hcorrect hn c Φ S x] at h

end Transfer

end Cslib.Crypto.Protocols.MPC.Yao
