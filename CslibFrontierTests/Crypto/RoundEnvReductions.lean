/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridChallenge
import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridProg
import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.DDHProb
import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.KDF
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Games

/-!
# Tests for the reductions from a sampled environment of a challenged round

A client of `Composition.ForallChallenge`, `composeRoundEnvProg`, `Protocol.realJointProg`,
`PrimeOrderGroupFamily.roundEnvToDDHDistinguisher` and
`PrimeOrderGroupFamily.roundEnvToKDFDistinguisher` under module encapsulation.

* The boundaries of `ForallChallenge`: it holds at the end of the steps, and a message round passes
  it to the remaining steps from the states after the delivery. Along the steps of `maskedOT`, one
  oracle round followed by one message round, it is the predicate at the corrupted slots
  `subCoalition parties I` and the queries of the current states; a predicate that never holds
  makes it false. A definition that skipped the oracle round, or that read the coalition `I`
  instead of its slots, fails these checks.
* The real execution of the fair-coin DDH transfer in the plain model is a program:
  `Protocol.eval_realJointProg` at `ddhOTProbProtocol` in `noOracleWorld`.
* The support hypothesis of `advantage_bind_roundGame_ddhOTProb_le` holds for an environment that
  really challenges: the program `composeRoundEnvProg` of hop `0` of `maskedOT` over the fair-coin
  DDH transfer, for a corrupted receiver. The theorem is applied to it.
* The support hypothesis of `advantage_bind_roundGame_kdfMaskedOT_eq_kdf` holds for an environment
  that returns a challenge with the corrupted slots `{1}` and a chosen value of the right length.
  The theorem is applied to it.
* An environment that has decided its bit: both distinguishers return it and ignore their inputs.
* A challenge with the corrupted slots `{0}` is rejected: the DDH distinguisher returns `false`, so
  its guard on the coalition is exercised.
* `advantage_bind_padHiding_eq_kdf` and `advantage_bind_padTransfer_le_ddh` apply to a decided
  environment, whose support has no challenge.
* `eval_composeSeqBatchOTRoundEnvProg` is applied to a batch over the fair-coin DDH transfer, and
  `Yao.forallChallenge_protocol_iff` shows that a predicate that never holds fails at the batched
  transfer of Yao's hybrid protocol.
* `advantage_bind_compose_seqBatchOT_maskedOT_le_sum_roundGame` is applied to Yao's protocol over
  the masked transfer with `F.kdfMask` and `F.kdfPads` over the fair-coin DDH transfer, with the
  group description drawn from a setup program.
* `Yao.advantage_setup_composedProtocol_kdfDDHProb_evaluator_le` is applied with all its data and
  hypotheses as variables, and its bound is ascribed: the privacy term of the garbling scheme plus,
  for every transfer, the advantage between the ideal and the real key-derivation game plus the
  advantage between the real and the random DDH game plus `14 / 2 ^ n`. Exchanging the two games of
  a term, or changing the constant, fails the check.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.RoundEnvReductions

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.MPC Cslib.Crypto.Protocols.MPC.Composition
open Cslib.Probability

/-- At the end of the steps `ForallChallenge` holds, whatever the predicate. -/
example {m : ℕ} {spec : MultiOracleSpec} (I : Finset (Fin m))
    (Q : (op : spec.Op) → Finset (Fin (spec.arity op)) →
      ((s : Fin (spec.arity op)) → spec.Query op s) → Prop)
    {State Out : Fin m → Type} (output : (i : Fin m) → State i → Out i)
    (st : (i : Fin m) → State i) :
    ForallChallenge I Q (Steps.done (spec := spec) output) st :=
  trivial

/-- A message round is passed through: the predicate is asked of the remaining steps, from the
states after the delivery. -/
example {m : ℕ} {spec : MultiOracleSpec} (I : Finset (Fin m))
    (Q : (op : spec.Op) → Finset (Fin (spec.arity op)) →
      ((s : Fin (spec.arity op)) → spec.Query op s) → Prop)
    {State Out : Fin m → Type} {s₀ r₀ : Fin m} {Msg : Type} {sc : Schedule m spec}
    (send : State s₀ → Msg)
    (next : Steps (fun i => State i × (Round.message (spec := spec) s₀ r₀ Msg).Received i) Out sc)
    (st : (i : Fin m) → State i) :
    ForallChallenge I Q (Steps.message send next) st ↔
      ForallChallenge I Q next (fun i => (st i, Round.deliverMessage (send (st s₀)) i)) :=
  Iff.rfl

/-- Along `maskedOT`, `ForallChallenge` is the predicate at the slots of the coalition and the
queries of the current states; the message round and the end of the steps add nothing. -/
example {G M : Type} (mask unmask : G → M → M) (samplePads : ProbComp (G × G))
    (I : Finset (Fin 2))
    (Q : Unit → Finset (Fin 2) → ((s : Fin 2) → OTIn G s) → Prop)
    (st : (i : Fin 2) → OTIn M i × MaskedOTCoins G i) :
    ForallChallenge (spec₁ := otSpec G) I Q (maskedOT mask unmask samplePads).steps st ↔
      Q () (subCoalition (Function.Embedding.refl (Fin 2)) I)
        (fun s => maskedOTQuery s (st s)) :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ => trivial⟩⟩

/-- A predicate that never holds fails at the oracle round of `maskedOT`. -/
example {G M : Type} (mask unmask : G → M → M) (samplePads : ProbComp (G × G))
    (I : Finset (Fin 2)) (st : (i : Fin 2) → OTIn M i × MaskedOTCoins G i) :
    ¬ ForallChallenge (spec₁ := otSpec G) I (fun _ _ _ => False)
      (maskedOT mask unmask samplePads).steps st :=
  fun h => h.1

/-- The real joint distribution of the fair-coin DDH transfer in the plain model is the law of a
program. -/
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc) (I : Finset (Fin 2))
    (x : (i : Fin 2) → OTIn (F.Carrier d) i) :
    ProbComp.eval ((F.ddhOTProbProtocol n d).realJointProg noOracleWorld I x) =
      (F.ddhOTProbProtocol n d).realJoint noOracleWorld I x :=
  Protocol.eval_realJointProg _ _ _ _

/-- Non-vacuity of `advantage_bind_roundGame_ddhOTProb_le`: the environment of hop `0` of
`maskedOT` over the fair-coin DDH transfer, as a program, challenges the corrupted receiver only,
so the theorem applies to it. -/
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (n : ℕ) {M : Type}
    (mask unmask : (d : F.Desc) → F.Carrier d → M → M)
    (samplePads : (d : F.Desc) → ProbComp (F.Carrier d × F.Carrier d))
    (S₂ : (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (F.Carrier d))
      (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (hS₂ : ∀ d, S₂ d {1} = F.ddhOTReceiverSimProb n d) (x : (i : Fin 2) → OTIn M i)
    (D : (d : F.Desc) → ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn M)
        (Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) M))
        (Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) M)) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :=
  F.advantage_bind_roundGame_ddhOTProb_le setup n S₂ hS₂
    (fun n d => composeRoundEnvProg (maskedOT (mask d) (unmask d) (samplePads d))
      (otWorld (F.Carrier d))
      (fun _ J q => (F.ddhOTProbProtocol n d).realJointProg noOracleWorld J q)
      (fun _ => S₂ d) {1} x (D d) 0)
    fun d c hc => by
      rw [eval_composeRoundEnvProg (maskedOT (mask d) (unmask d) (samplePads d))
        (otWorld (F.Carrier d)) noOracleWorld (fun _ => F.ddhOTProbProtocol n d)
        (fun _ J q => Protocol.eval_realJointProg _ _ J q)] at hc
      exact ForallChallenge.of_mem_support_composeRoundEnv (Q := fun _ J _ => J = {1})
        (maskedOT (mask d) (unmask d) (samplePads d)) _ _ _ _ {1} _ _ _
        (fun _ _ => ⟨Finset.ext fun _ => mem_subCoalition, fun _ => trivial⟩) hc

/-- Non-vacuity of `advantage_bind_roundGame_kdfMaskedOT_eq_kdf`: an environment that returns a
challenge with the corrupted slots `{1}` and a chosen value of length `msgLen n` satisfies the
support hypothesis, so the theorem applies to it. -/
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) (n : ℕ)
    (Sm : (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (hSm : ∀ d, Sm d {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
      (Cslib.BitString.sampleList (msgLen n)))
    (hH : ∀ d ∈ (setup n).support, ∀ r : F.Carrier d, (H (d, F.encode d r)).length = msgLen n)
    (q : (s : Fin 2) → OTIn (List Bool) s)
    (hq : (otOutputs (M := List Bool) q 1 : List Bool).length = msgLen n)
    (g : (d : F.Desc) → ((s : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool))
        (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)) s) ×
      ((s : Fin 2) → OTOut (List Bool) s) → ProbComp Bool) :=
  F.advantage_bind_roundGame_kdfMaskedOT_eq_kdf setup H msgLen n Sm hSm
    (fun _ d => pure (.inr ⟨(), {1}, q, g d⟩)) hH
    fun d _ c hc => by
      rw [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc
      obtain rfl := Sum.inr.inj hc
      exact ⟨rfl, hq⟩

/-- A decided environment: the DDH distinguisher returns its bit and ignores the triple. -/
example (F : PrimeOrderGroupFamily) (b : Bool) (n : ℕ) (d : F.Desc) (u v w : F.Carrier d) :
    F.roundEnvToDDHDistinguisher (fun _ _ => pure (.inl b)) n d u v w = pure b := by
  simp only [PrimeOrderGroupFamily.roundEnvToDDHDistinguisher, pure_bind]

/-- A decided environment: the key-derivation distinguisher returns its bit and ignores its
inputs. -/
example (F : PrimeOrderGroupFamily) (H : F.Desc × List Bool → List Bool) (b : Bool) (n : ℕ)
    (d : F.Desc) (u v : F.Carrier d) (key : List Bool) :
    F.roundEnvToKDFDistinguisher H (fun _ _ => pure (.inl b)) n d u v key = pure b := by
  simp only [PrimeOrderGroupFamily.roundEnvToKDFDistinguisher, pure_bind]

/-- A challenge with the corrupted slots `{0}` is rejected: the DDH distinguisher returns
`false`. -/
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc) (u v w : F.Carrier d)
    (x : (d : F.Desc) → (i : Fin 2) → OTIn (F.Carrier d) i)
    (g : (d : F.Desc) → ((s : ({0} : Finset (Fin 2))) → PartyView (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (ddhOTSchedule (F.Carrier d)) s) ×
      ((s : Fin 2) → OTOut (F.Carrier d) s) → ProbComp Bool) :
    F.roundEnvToDDHDistinguisher (fun _ d => pure (.inr ⟨(), {0}, x d, g d⟩)) n d u v w =
      pure false := by
  have h : ¬ (({0} : Finset (Fin 2)) = {1}) := by decide
  simp only [PrimeOrderGroupFamily.roundEnvToDDHDistinguisher, pure_bind, h, ↓reduceDIte]

/-- The pad-hiding hop applies to a decided environment: no challenge is in its support. -/
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) (n : ℕ)
    (Sm : (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (hSm : ∀ d, Sm d {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
      (Cslib.BitString.sampleList (msgLen n)))
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (hH : ∀ d (r : F.Carrier d), (H (d, F.encode d r)).length = msgLen n) (b : Bool) :=
  F.advantage_bind_padHiding_eq_kdf setup H msgLen n Sm hSm S₂ hH (fun _ _ => pure (.inl b))
    fun d c hc => by
      rw [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc
      cases hc

/-- The pad-transfer hop applies to a decided environment: no challenge is in its support. -/
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (n : ℕ)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (hS₂ : ∀ d, S₂ n d {1} = F.ddhOTReceiverSimProb n d) (b : Bool) :=
  F.advantage_bind_padTransfer_le_ddh setup H n S₂ hS₂ (fun _ _ => pure (.inl b))
    fun d c hc => by
      rw [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc
      cases hc

/-- The environment of a transfer of a batch over the fair-coin DDH transfer is a program. -/
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc) {m k : ℕ}
    {sc₁ : Schedule m (batchOTSpec k (F.Carrier d))} {In Coins₁ Out : Fin m → Type}
    (P : Protocol m (batchOTSpec k (F.Carrier d)) sc₁ In Coins₁ Out)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (F.Carrier d))
      (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (fun _ => Unit)
            (seqBatchOTSchedule k (F.Carrier d))) Coins₁ sc₁)
        (Schedule.compose
          (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
            (seqBatchOTSchedule k (F.Carrier d))) sc₁) i) ×
      ((i : Fin m) → Out i) → ProbComp Bool) (t j : ℕ) :=
  eval_composeSeqBatchOTRoundEnvProg k (F.Carrier d) P noOracleWorld (F.ddhOTProbProtocol n d) S₂
    I x D t j

section Yao

open Cslib.Crypto.Garbling Cslib.Crypto.Protocols.MPC.Yao

/-- Yao's hybrid protocol has an oracle round: a predicate that never holds fails along its
steps. -/
example {Fn : Type} (Gs : Scheme Fn) (n : ℕ) (c : Params Gs) (I : Finset (Fin 2))
    (x : (i : Fin 2) → Input c i) (r : (i : Fin 2) → Coins i) :
    ¬ ForallChallenge I (fun _ _ _ => False) (protocol Gs n c).steps (fun i => (x i, r i)) :=
  fun h => (Yao.forallChallenge_protocol_iff n c I _ x r).1 h

/-- The sum over the transfers of Yao's protocol over the masked transfer over the fair-coin DDH
transfer, with the group description drawn from a setup program. -/
example {Fn : Type} {Gs : Scheme Fn} (F : PrimeOrderGroupFamily) (setup : ℕ → ProbComp F.Desc)
    (H : F.Desc × List Bool → List Bool) (c : ℕ → Params Gs)
    (T₁ : (n : ℕ) → (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule (c n)) (Input (c n)) Coins (fun _ => List Bool) I)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (x : (n : ℕ) → F.Desc → (i : Fin 2) → Input (c n) i)
    (D : (n : ℕ) → (d : F.Desc) → ((i : ({1} : Finset (Fin 2))) → PartyView (Input (c n))
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins
              (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
              (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))
            (fun _ => Unit) (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
          Coins (schedule (c n)))
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
              (maskedOTSchedule (F.Carrier d) (List Bool)))
            (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
          (schedule (c n))) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool)
    (n N : ℕ) (hN : (schedule (c n)).oracleRounds ≤ N) :=
  advantage_bind_compose_seqBatchOT_maskedOT_le_sum_roundGame
    ((ProbComp.eval (setup n)).map Sum.inr) (c n).evaluatorLen
    (fun _ : F.Desc => protocol Gs n (c n)) (fun d => F.kdfMask H d) (fun d => F.kdfMask H d)
    (fun d => F.kdfPads d) (fun _ => noOracleWorld) (fun d => F.ddhOTProbProtocol n d)
    (fun d => Sm n d) (fun d => S₂ n d) (fun _ => functionality Gs (c n)) (fun _ => T₁ n)
    (fun _ => {1}) (x n) (D n) N (fun _ => hN)

/-- The evaluator bound for Yao's protocol in the plain model, with its terms in order: garbling
privacy, then per transfer the ideal against the real key-derivation game, the real against the
random DDH game, and `14 / 2 ^ n`. -/
example {Fn Λ : Type} {Gs : Scheme Fn}
    (hproj : Gs.encode = projectiveEncode) (hcorrect : Gs.Correct)
    (F : PrimeOrderGroupFamily) (setup : ℕ → ProbComp F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ)
    (c : ℕ → Params Gs) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ)
    (T₁ : (n : ℕ) → (I : Finset (Fin 2)) →
      CoalitionSimulator (schedule (c n)) (Input (c n)) Coins (fun _ => List Bool) I)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (x : (n : ℕ) → F.Desc → (i : Fin 2) → Input (c n) i)
    (D : (n : ℕ) → (d : F.Desc) → ((i : ({1} : Finset (Fin 2))) → PartyView (Input (c n))
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins
              (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
              (MaskedOTCoins (F.Carrier d)) (maskedOTSchedule (F.Carrier d) (List Bool)))
            (fun _ => Unit) (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
          Coins (schedule (c n)))
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
              (maskedOTSchedule (F.Carrier d) (List Bool)))
            (seqBatchOTSchedule (c n).evaluatorLen (List Bool)))
          (schedule (c n))) i) ×
      ((i : Fin 2) → List Bool) → ProbComp Bool)
    {n : ℕ} (hn : 0 < n)
    (hT₁ : T₁ n {1} = evaluatorSim Gs Φ S n (c n))
    (hSm : ∀ d, Sm n d {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
      (Cslib.BitString.sampleList (msgLen n)))
    (hS₂ : ∀ d, S₂ n d {1} = F.ddhOTReceiverSimProb n d)
    (hH : ∀ d (r : F.Carrier d), (H (d, F.encode d r)).length = msgLen n)
    (hlen : ∀ d, ∀ r ∈ (ProbComp.eval (OracleComp.pi (protocol Gs n (c n)).sampleCoins)).support,
      ∀ (t : Fin (c n).evaluatorLen) (b : Bool),
        (transferQueries n (c n) (x n d) r 0 t b).length = msgLen n) :=
  (Yao.advantage_setup_composedProtocol_kdfDDHProb_evaluator_le hproj hcorrect F setup H msgLen c
    Φ S T₁ Sm S₂ x D hn hT₁ hSm hS₂ hH hlen :
    Game.advantage _ _ ≤ prvSimAdvantage _ _ _ _ _ +
      ∑ _j ∈ Finset.range (c n).evaluatorLen,
        (Game.advantage (F.kdfIdealGame _ msgLen _ n) (F.kdfRealGame _ H _ n) +
          (Game.advantage (F.ddhRealGame _ _ n) (F.ddhRandomGame _ _ n) + 14 / 2 ^ n)))

end Yao

end CslibFrontierTests.Crypto.RoundEnvReductions
