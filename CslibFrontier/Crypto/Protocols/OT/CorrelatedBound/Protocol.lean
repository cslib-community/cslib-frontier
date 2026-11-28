/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.OT.CorrelatedBound.Information
public import CslibFrontier.Crypto.Protocols.MPC.Basic
public import CslibFrontier.Crypto.Protocols.MPC.BatchOT
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product
import CslibFrontier.Tactic.UniformRelabel

/-!
# Semi-honest two-party protocols over correlated randomness with a public transcript

This module specializes the synchronous two-party plain-channel protocol model
`Cslib.Crypto.Protocols.MPC.Protocol` (`m = 2`, `spec = noOracleSpec`) to executions over a
correlated source `source : PMF (A × B)` with a public communication transcript, and also connects
adaptive-speaker binary communication trees `Cslib.Communication.Protocol` and
`Cslib.Communication.PrivateCoin` over `(A, B)`.

Every inter-party message round (`sender ≠ receiver`) contributes to the public transcript
`PublicTranscript sc`, which both parties reconstruct deterministically from their views
(`transcriptOfView`). For any `Protocol 2 noOracleSpec sc`, conditioning on the public transcript
never increases the conditional mutual information between the two parties' initial correlated-plus-
coin states (`condMutualInfo_transcript_le_mutualInfo`). Combined with
`natCast_le_mutualInfo_of_rot`,
any protocol realizing `k` independent random OTs (`rotFunctionality k`) or `k` chosen-input OTs
(`batchOTFunctionality k Bool`) with perfect semi-honest privacy over `source` requires
`k ≤ I(A; B)` (`rot_le_mutualInfo`, `chosenOT_le_mutualInfo`, `commProtocol_rot_le_mutualInfo`,
`privateCoin_rot_le_mutualInfo`).

Privacy over a correlated source is the shared MPC notion
`Cslib.Crypto.Protocols.MPC.PerfectSemiHonestPrivateProperWithSetup`, with the source dealt by the
trusted setup `dealSource source` (or `dealSourceWithInput source` next to external inputs) and
simulators `Cslib.Crypto.Protocols.MPC.SetupSimulator` that never see the dealt share.

## Main definitions

* `Cslib.Crypto.Protocols.OT.PublicMsg`, `Cslib.Crypto.Protocols.OT.PublicTranscript`: public
  communication transcript type of a two-party plain-channel schedule.
* `Cslib.Crypto.Protocols.OT.stepsTranscriptOfView`, `Cslib.Crypto.Protocols.OT.transcriptOfView`:
  deterministic reconstruction of the public transcript from either party's `PartyView`.
* `Cslib.Crypto.Protocols.OT.realWithInputDist`, `Cslib.Crypto.Protocols.OT.realCorrelated`: real
  executions over a joint input distribution and over a correlated source.
* `Cslib.Crypto.Protocols.OT.dealSource`, `Cslib.Crypto.Protocols.OT.dealSourceWithInput`: trusted
  setups dealing a correlated source to the two parties, alone or next to their external inputs.
* `Cslib.Crypto.Protocols.OT.idealROT`, `Cslib.Crypto.Protocols.OT.rotFunctionality`: ideal
  distribution and input-free functionality of `k` independent random 1-out-of-2 bit oblivious
  transfers.

## Main results

* `Cslib.Crypto.Protocols.OT.transcriptOfView_zero_eq_one`: both parties reconstruct the same public
  transcript on every supported execution.
* `Cslib.Crypto.Protocols.OT.dealSource_bind_realJoint`: the real side of privacy over
  `dealSource source` is `realCorrelated` restricted to the coalition.
* `Cslib.Crypto.Protocols.OT.condMutualInfo_transcript_le_mutualInfo_input`,
  `Cslib.Crypto.Protocols.OT.condMutualInfo_transcript_le_mutualInfo`: public communication over a
  correlated source satisfies `I((In₀, R₀); (In₁, R₁) | T) ≤ I(In₀; In₁)`.
* `Cslib.Crypto.Protocols.OT.rot_le_mutualInfo`: any perfectly semi-honest private `k`-ROT protocol
  over `source` satisfies `(k : ℝ) ≤ I(A; B)`.
* `Cslib.Crypto.Protocols.OT.chosenOT_le_mutualInfo`: any perfectly semi-honest private chosen-input
  `k`-OT protocol (`batchOTFunctionality k Bool`) over `source` satisfies `(k : ℝ) ≤ I(A; B)`.
* `Cslib.Crypto.Protocols.OT.commProtocol_rot_le_mutualInfo`,
  `Cslib.Crypto.Protocols.OT.privateCoin_rot_le_mutualInfo`: `(k : ℝ) ≤ I(A; B)` for adaptive-
  speaker binary communication trees `Cslib.Communication.Protocol` and
  `Cslib.Communication.PrivateCoin`.

## References

* [R. Ahlswede and I. Csiszár, *Common Randomness in Information Theory and Cryptography.
  Part I: Secret Sharing*][AhlswedeCsiszar1993] (bibliographic metadata verified; primary full text
  uninspected; locators unverified).
* [A. C. A. Nascimento and A. Winter, *On the Oblivious-Transfer Capacity of Noisy
  Resources*][NascimentoWinter2008] (bibliographic metadata verified; primary full text uninspected;
  locators unverified).
* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004]
  (semi-honest simulation background; primary full text uninspected; locators unverified).
-/

public section

namespace Cslib.Crypto.Protocols.OT

open Cslib.Probability Cslib.Probability.PMF Cslib.Crypto.Protocols.MPC Cslib.Communication
open scoped ENNReal

/-- Dependent pair constructor on `Fin 2`. -/
@[expose] def pairVec {F : Fin 2 → Type} (x0 : F 0) (x1 : F 1) : (i : Fin 2) → F i
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1

/-- Restrict a constant value at party `i` to the singleton coalition `{i}`. -/
private def restrictSingleton {F : Fin 2 → Type} (i : Fin 2) (x : F i) :
    (j : ({i} : Finset (Fin 2))) → F j.val :=
  fun ⟨_, hj⟩ => Finset.mem_singleton.mp hj ▸ x

private theorem restrictSingleton_eq {F : Fin 2 → Type} (i : Fin 2) (f : (j : Fin 2) → F j) :
    ({i} : Finset (Fin 2)).restrict f = restrictSingleton i (f i) := by
  funext ⟨_, hj⟩
  obtain rfl := Finset.mem_singleton.mp hj
  rfl

private lemma finite_finCases {A B : Type} [Finite A] [Finite B] (i : Fin 2) :
    Finite (Fin.cases A (fun _ => B) i) := by
  fin_cases i
  · exact ‹Finite A›
  · exact ‹Finite B›

/-! ### Public transcripts of two-party plain-channel schedules -/

/-- Public message payload of a round in a two-party plain-channel schedule: inter-party messages
(`sender ≠ receiver`) are public, while self-messages carry no public payload. -/
@[expose, reducible] def PublicMsg : Round 2 noOracleSpec → Type
  | .message sender receiver Msg => (sender ≠ receiver) → Msg
  | .oracle (op := op) _ => op.elim

/-- Public communication transcript along a two-party plain-channel schedule. -/
@[expose, reducible] def PublicTranscript : Schedule 2 noOracleSpec → Type
  | [] => Unit
  | r :: sc => PublicMsg r × PublicTranscript sc

/-- Reconstruct the public transcript from party `i`'s current local state and received messages. -/
@[expose] noncomputable def stepsTranscriptOfView {State Out : Fin 2 → Type}
    {sc : Schedule 2 noOracleSpec}
    (steps : Steps State Out sc) (i : Fin 2) (st_i : State i)
    (recv_i : sc.Received i) : PublicTranscript sc :=
  match steps, recv_i with
  | .done _, () => ()
  | .message (sender := sender) (receiver := receiver) send next, (r_head, r_tail) =>
      let msgHead : (sender ≠ receiver) → _ := fun hne =>
        if hi : i = sender then
          send (hi ▸ st_i)
        else
          r_head (by omega)
      (msgHead, stepsTranscriptOfView next i (st_i, r_head) r_tail)
  | .oracle (op := op) _ _, _ => op.elim

/-- Reconstruct the public transcript of `proto` from party `i`'s `PartyView`. -/
@[expose] noncomputable def transcriptOfView {sc : Schedule 2 noOracleSpec}
    {In Coins Out : Fin 2 → Type}
    (proto : Protocol 2 noOracleSpec sc In Coins Out) (i : Fin 2)
    (v : PartyView In Coins sc i) : PublicTranscript sc :=
  stepsTranscriptOfView proto.steps i (v.input, v.coins) v.received

/-- Deterministic execution of `steps` in `noOracleWorld`: returns the tuple of received transcripts
for each party. -/
private noncomputable def stepsExecPure {State Out : Fin 2 → Type} {sc : Schedule 2 noOracleSpec}
    (steps : Steps State Out sc) (st : (i : Fin 2) → State i) : (i : Fin 2) → sc.Received i :=
  match steps with
  | .done _ => fun _ => ()
  | .message (sender := sender) send next =>
      let r_head : (i : Fin 2) → _ := Round.deliverMessage (send (st sender))
      let r_tail := stepsExecPure next (fun i => (st i, r_head i))
      fun i => (r_head i, r_tail i)
  | .oracle (op := op) _ _ => op.elim

/-- Deterministic public transcript produced by `steps` from initial states `st`. -/
private noncomputable def stepsTranscriptPure {State Out : Fin 2 → Type}
    {sc : Schedule 2 noOracleSpec} (steps : Steps State Out sc)
    (st : (i : Fin 2) → State i) : PublicTranscript sc :=
  match steps with
  | .done _ => ()
  | .message (sender := sender) send next =>
      let r_head : (i : Fin 2) → _ := Round.deliverMessage (send (st sender))
      (fun _ => send (st sender), stepsTranscriptPure next (fun i => (st i, r_head i)))
  | .oracle (op := op) _ _ => op.elim

private theorem stepsEvalWith_eq_pure :
    ∀ {sc : Schedule 2 noOracleSpec} {State Out : Fin 2 → Type}
      (steps : Steps State Out sc) (st : (i : Fin 2) → State i),
      steps.evalWith noOracleWorld st = PMF.pure (stepsExecPure steps st)
  | [], _, _, .done _, _ => rfl
  | _ :: _, _, _, .message send next, st => by
      rw [Steps.evalWith_message, stepsEvalWith_eq_pure next _, PMF.pure_map]
      rfl
  | _ :: _, _, _, .oracle (op := op) _ _, _ => op.elim

private theorem stepsTranscriptOfView_execPure :
    ∀ {sc : Schedule 2 noOracleSpec} {State Out : Fin 2 → Type}
      (steps : Steps State Out sc) (st : (i : Fin 2) → State i) (i : Fin 2),
      stepsTranscriptOfView steps i (st i) (stepsExecPure steps st i) =
        stepsTranscriptPure steps st
  | [], _, _, .done _, _, _ => rfl
  | _ :: _, _, _, .message (sender := sender) (receiver := receiver) send next, st, i => by
      simp only [stepsTranscriptOfView, stepsExecPure, stepsTranscriptPure]
      refine Prod.ext (funext fun _ => ?_)
        (stepsTranscriptOfView_execPure next
          (fun j => (st j, Round.deliverMessage (send (st sender)) j)) i)
      by_cases hi : i = sender
      · subst hi; simp only [dite_true]
      · obtain rfl : i = receiver := by omega
        simp only [hi, dite_false, Round.deliverMessage]
  | _ :: _, _, _, .oracle (op := op) _ _, _, _ => op.elim

private theorem stepsTranscriptOfView_eq_transcriptPure_of_mem_support
    {State Out : Fin 2 → Type} {sc : Schedule 2 noOracleSpec}
    (steps : Steps State Out sc) {st : (i : Fin 2) → State i}
    {recv : (i : Fin 2) → sc.Received i}
    (h : recv ∈ (steps.evalWith noOracleWorld st).support) (i : Fin 2) :
    stepsTranscriptOfView steps i (st i) (recv i) = stepsTranscriptPure steps st := by
  rw [stepsEvalWith_eq_pure, PMF.mem_support_pure_iff] at h
  subst h
  exact stepsTranscriptOfView_execPure steps st i

/-- In every supported execution of a two-party plain-channel protocol, Alice (`0`) and Bob (`1`)
reconstruct the exact same public transcript from their views. -/
theorem transcriptOfView_zero_eq_one {sc : Schedule 2 noOracleSpec} {In Coins Out : Fin 2 → Type}
    (proto : Protocol 2 noOracleSpec sc In Coins Out) {x : (i : Fin 2) → In i}
    {res : ((i : Fin 2) → PartyView In Coins sc i) × ((i : Fin 2) → Out i)}
    (h : res ∈ (proto.evalWith noOracleWorld x).support) :
    transcriptOfView proto 0 (res.1 0) = transcriptOfView proto 1 (res.1 1) := by
  simp only [Protocol.evalWith_eq, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at h
  rcases h with ⟨_, _, recv, hrecv_supp, rfl⟩
  exact (stepsTranscriptOfView_eq_transcriptPure_of_mem_support proto.steps hrecv_supp 0).trans
    (stepsTranscriptOfView_eq_transcriptPure_of_mem_support proto.steps hrecv_supp 1).symm

/-- Given `st_i` and the public transcript `T`, party `i` deterministically reconstructs its
received messages `sc.Received i` along `steps`. -/
private noncomputable def stepsReceivedOfTranscript {State Out : Fin 2 → Type}
    {sc : Schedule 2 noOracleSpec} (steps : Steps State Out sc) (i : Fin 2) (st_i : State i)
    (T : PublicTranscript sc) : sc.Received i :=
  match steps, T with
  | .done _, () => ()
  | .message (sender := sender) (receiver := receiver) send next, (msgHead, msgTail) =>
      let r_head : (Round.message (spec := noOracleSpec) sender receiver _).Received i := fun hr =>
        if hs : sender = receiver then
          have hi : i = sender := hr.trans hs.symm
          send (hi ▸ st_i)
        else
          msgHead hs
      (r_head, stepsReceivedOfTranscript next i (st_i, r_head) msgTail)
  | .oracle (op := op) _ _, _ => op.elim

private theorem stepsReceivedOfTranscript_transcriptPure :
    ∀ {sc : Schedule 2 noOracleSpec} {State Out : Fin 2 → Type}
      (steps : Steps State Out sc) (st : (i : Fin 2) → State i) (i : Fin 2),
      stepsReceivedOfTranscript steps i (st i) (stepsTranscriptPure steps st) =
        stepsExecPure steps st i
  | [], _, _, .done _, _, _ => rfl
  | _ :: _, _, _, .message (sender := sender) (receiver := receiver) send next, st, i => by
      simp only [stepsReceivedOfTranscript, stepsTranscriptPure, stepsExecPure]
      have hhead :
          (fun hr : i = receiver =>
            if hs : sender = receiver then send ((hr.trans hs.symm) ▸ st i)
            else send (st sender)) =
            Round.deliverMessage (spec := noOracleSpec) (sender := sender) (receiver := receiver)
              (send (st sender)) i :=
        Round.received_message_ext fun hr => by
          by_cases hs : sender = receiver
          · obtain rfl : i = sender := hr.trans hs.symm
            simp only [hs, dite_true, Round.deliverMessage]
          · simp only [hs, dite_false, Round.deliverMessage]
      rw [hhead]
      exact Prod.ext rfl (stepsReceivedOfTranscript_transcriptPure next
        (fun j => (st j, Round.deliverMessage (send (st sender)) j)) i)
  | _ :: _, _, _, .oracle (op := op) _ _, _, _ => op.elim

/-- On every supported execution, each party's view and output are determined by its input, coins,
and the public transcript. -/
private theorem partyView_eq_of_mem_support_evalWith
    {sc : Schedule 2 noOracleSpec} {In Coins Out : Fin 2 → Type}
    (proto : Protocol 2 noOracleSpec sc In Coins Out) {x : (i : Fin 2) → In i}
    {views : (i : Fin 2) → PartyView In Coins sc i} {out : (i : Fin 2) → Out i}
    (hev : (views, out) ∈ (proto.evalWith noOracleWorld x).support) (i : Fin 2) :
    views i = ⟨(views i).input, (views i).coins,
        stepsReceivedOfTranscript proto.steps i ((views i).input, (views i).coins)
          (transcriptOfView proto 0 (views 0))⟩ ∧
      out i = proto.outputOfView i (views i) := by
  have h01 := transcriptOfView_zero_eq_one proto hev
  have hout := Protocol.snd_eq_outputOfView_of_mem_support_evalWith hev
  simp only [Protocol.evalWith_eq, PMF.mem_support_bind_iff, PMF.mem_support_map_iff,
    stepsEvalWith_eq_pure, PMF.mem_support_pure_iff] at hev
  rcases hev with ⟨r, _, _, rfl, hres⟩
  have hv := congrFun (congrArg Prod.fst hres.symm) i
  dsimp only at hv
  refine ⟨?_, congrFun hout i⟩
  have htr : transcriptOfView proto 0 (views 0) = transcriptOfView proto i (views i) := by
    fin_cases i
    · rfl
    · exact h01
  rw [htr]
  dsimp only [transcriptOfView]
  rw [hv]
  refine PartyView.ext rfl rfl ?_
  have h1 := stepsTranscriptOfView_execPure proto.steps (fun j => (x j, r j)) i
  dsimp only at h1 ⊢
  rw [h1]
  exact (stepsReceivedOfTranscript_transcriptPure proto.steps (fun j => (x j, r j)) i).symm

/-- Auxiliary round-by-round induction: conditioning on a public transcript never increases
conditional mutual information between Alice's and Bob's initial correlated-plus-coin states. -/
private theorem exists_state_next_of_party {Ω τ₀ χ : Type*} {State : Fin 2 → Type}
    {sender receiver : Fin 2} {Msg : Type} (send : State sender → Msg)
    (ν : PMF Ω) (T0 : Ω → τ₀) (X : Ω → χ) (st : Ω → (j : Fin 2) → State j)
    (i : Fin 2) (f : χ × τ₀ → State i) (hf : ∀ ω ∈ ν.support, st ω i = f (X ω, T0 ω)) :
    let msgPub : Ω → PublicMsg (Round.message sender receiver Msg) := fun ω _ => send (st ω sender)
    let r_head : Ω → (j : Fin 2) →
        (Round.message (spec := noOracleSpec) sender receiver Msg).Received j :=
      fun ω => Round.deliverMessage (send (st ω sender))
    ∃ f' : χ × (τ₀ × PublicMsg (Round.message sender receiver Msg)) →
        State i × (Round.message (spec := noOracleSpec) sender receiver Msg).Received i,
      ∀ ω ∈ ν.support, (st ω i, r_head ω i) = f' (X ω, (T0 ω, msgPub ω)) := by
  intro msgPub r_head
  by_cases hs : sender = i
  · subst hs
    exact ⟨fun p => (f (p.1, p.2.1), Round.deliverMessage (send (f (p.1, p.2.1))) sender),
      fun ω hω => Prod.ext (hf ω hω) (congrArg (Round.deliverMessage · sender)
        (congrArg send (hf ω hω)))⟩
  · by_cases hr : receiver = i
    · subst hr
      exact ⟨fun p => (f (p.1, p.2.1), fun _ => p.2.2 hs), fun ω hω =>
        Prod.ext (hf ω hω) (Round.received_message_ext fun _ => rfl)⟩
    · exact ⟨fun p => (f (p.1, p.2.1), fun h => absurd h.symm hr), fun ω hω =>
        Prod.ext (hf ω hω) (Round.received_message_eq_of_ne (Ne.symm hr) _ _)⟩

/-- Adding a plain-channel communication schedule cannot increase conditional mutual information
between the parties' local states. -/
private theorem condMutualInfo_steps_transcriptPure_le
    {Ω α₀ β₀ τ₀ : Type*} [Finite α₀] [Finite β₀] [Finite τ₀]
    (ν : PMF Ω) (A0 : Ω → α₀) (B0 : Ω → β₀) (T0 : Ω → τ₀) :
    ∀ {sc : Schedule 2 noOracleSpec} {State Out : Fin 2 → Type}
      [Finite (PublicTranscript sc)]
      (steps : Steps State Out sc) (st0 : Ω → State 0) (st1 : Ω → State 1),
      (∃ f0 : α₀ × τ₀ → State 0, ∀ ω ∈ ν.support, st0 ω = f0 (A0 ω, T0 ω)) →
      (∃ f1 : β₀ × τ₀ → State 1, ∀ ω ∈ ν.support, st1 ω = f1 (B0 ω, T0 ω)) →
      condMutualInfo (ν.map fun ω =>
        ((T0 ω, stepsTranscriptPure steps (fun i => pairVec (st0 ω) (st1 ω) i)),
          A0 ω, B0 ω)) ≤
        condMutualInfo (ν.map fun ω => (T0 ω, A0 ω, B0 ω))
  | [], _, _, _, .done _, _, _, _, _ =>
      (condMutualInfo_map_congr_cond ν A0 B0 (e := (·, ()))
        (fun _ _ h => congrArg Prod.fst h) (fun _ _ => rfl)).le
  | _ :: sc, _, _, _,
      .message (sender := sender) (receiver := receiver) (Msg := Msg) send next,
      st0, st1, ⟨f0, hf0⟩, ⟨f1, hf1⟩ => by
      obtain ⟨ω₀, _⟩ := ν.support_nonempty
      let msgPub : Ω → PublicMsg (Round.message sender receiver Msg) :=
        fun ω _ => send (pairVec (st0 ω) (st1 ω) sender)
      let r_head : Ω → (i : Fin 2) →
          (Round.message (spec := noOracleSpec) sender receiver Msg).Received i :=
        fun ω => Round.deliverMessage (send (pairVec (st0 ω) (st1 ω) sender))
      let tTail₀ := stepsTranscriptPure next (fun i => (pairVec (st0 ω₀) (st1 ω₀) i, r_head ω₀ i))
      have : Finite (PublicMsg (Round.message sender receiver Msg)) :=
        Finite.of_injective (·, tTail₀) fun _ _ h => congrArg Prod.fst h
      have : Finite (PublicTranscript sc) :=
        Finite.of_injective (msgPub ω₀, ·) fun _ _ h => congrArg Prod.snd h
      have hStep : condMutualInfo (ν.map fun ω => ((T0 ω, msgPub ω), A0 ω, B0 ω)) ≤
          condMutualInfo (ν.map fun ω => (T0 ω, A0 ω, B0 ω)) := by
        by_cases hSR : sender = receiver
        · exact (condMutualInfo_map_congr_cond ν (C := T0)
            (C' := fun ω => (T0 ω, msgPub ω)) A0 B0 (e := fun t => (t, msgPub ω₀))
            (fun _ _ h => congrArg Prod.fst h)
            (fun ω _ => Prod.ext rfl (funext fun h => (h hSR).elim))).le
        · fin_cases sender
          · refine condMutualInfo_map_pair_fst_le_of_eq_zero ν T0 msgPub A0 B0 <| by
              rw [condMutualInfo_map_swap]; exact condMutualInfo_map_eq_zero_of_determined ν _ B0
                msgPub (fun t _ => send (f0 (t.2, t.1)))
                fun ω h => funext fun _ => congrArg send (hf0 ω h)
          · refine condMutualInfo_map_pair_snd_le_of_eq_zero ν T0 msgPub A0 B0 <| by
              rw [condMutualInfo_map_swap]; exact condMutualInfo_map_eq_zero_of_determined ν _ A0
                msgPub (fun t _ => send (f1 (t.2, t.1)))
                fun ω h => funext fun _ => congrArg send (hf1 ω h)
      have hIH := condMutualInfo_steps_transcriptPure_le ν A0 B0 (fun ω => (T0 ω, msgPub ω))
        next (fun ω => (st0 ω, r_head ω 0)) (fun ω => (st1 ω, r_head ω 1))
        (exists_state_next_of_party send ν T0 A0 (fun ω => pairVec (st0 ω) (st1 ω)) 0 f0 hf0)
        (exists_state_next_of_party send ν T0 B0 (fun ω => pairVec (st0 ω) (st1 ω)) 1 f1 hf1)
      have hFinStep : ∀ ω, (fun i : Fin 2 => (pairVec (st0 ω) (st1 ω) i, r_head ω i)) =
          pairVec (st0 ω, r_head ω 0) (st1 ω, r_head ω 1) :=
        fun ω => funext fun i => by fin_cases i <;> rfl
      have hAssoc := condMutualInfo_map_congr_cond ν A0 B0
        (C := fun ω => (T0 ω, stepsTranscriptPure (.message send next)
          (fun i => pairVec (st0 ω) (st1 ω) i)))
        (e := (Equiv.prodAssoc τ₀ _ _).symm) (Equiv.prodAssoc τ₀ _ _).symm.injective
        (fun ω _ => by simp only [stepsTranscriptPure, r_head, hFinStep]; rfl)
      exact hAssoc.symm.trans_le (hIH.trans hStep)
  | _ :: _, _, _, _, .oracle (op := op) _ _, _, _, _, _ => op.elim

/-! ### Correlated-source 2PC semantics and privacy -/

section Correlated2PC

variable {A B : Type} {sc : Schedule 2 noOracleSpec} {Coins Out : Fin 2 → Type}

/-- Real execution of a two-party plain-channel protocol over an arbitrary joint input distribution
`inputDist : PMF (In 0 × In 1)`. -/
@[expose] noncomputable def realWithInputDist {In : Fin 2 → Type}
    (proto : Protocol 2 noOracleSpec sc In Coins Out)
    (inputDist : PMF (In 0 × In 1)) :
    PMF (((i : Fin 2) → PartyView In Coins sc i) × ((i : Fin 2) → Out i)) :=
  inputDist.bind fun xy => proto.evalWith noOracleWorld (pairVec xy.1 xy.2)

private theorem bind_evalWith_map_input {Ω α β : Type*} {In Coins Out : Fin 2 → Type}
    (proto : Protocol 2 noOracleSpec sc In Coins Out)
    (μ : PMF Ω) (f : Ω → (i : Fin 2) → In i) (g0 : In 0 → α) (g1 : In 1 → β) :
    ((μ.bind fun ω => proto.evalWith noOracleWorld (f ω)).map fun (views, _) =>
      (g0 (views 0).input, g1 (views 1).input)) = μ.map fun ω => (g0 (f ω 0), g1 (f ω 1)) := by
  simp only [Protocol.evalWith_eq, stepsEvalWith_eq_pure, PMF.pure_map, PMF.map_bind,
    PMF.bind_const]
  exact PMF.bind_pure_comp _ _

/-- Real execution of a two-party plain-channel protocol over correlated source
`source : PMF (A × B)`. -/
@[expose] noncomputable def realCorrelated
    (proto : Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins Out)
    (source : PMF (A × B)) :
    PMF (((i : Fin 2) → PartyView (Fin.cases A (fun _ => B)) Coins sc i) × ((i : Fin 2) → Out i)) :=
  source.bind fun ab => proto.evalWith noOracleWorld (Fin.cases ab.1 (fun _ => ab.2))

/-- The trusted setup dealing correlated source `source : PMF (A × B)` to the two parties: party `0`
receives the `A` share and party `1` the `B` share. Privacy over `source` is
`PerfectSemiHonestPrivateProperWithSetup` with setup `fun _ => dealSource source`. -/
noncomputable def dealSource (source : PMF (A × B)) :
    PMF ((i : Fin 2) → Fin.cases A (fun _ => B) i) :=
  source.map fun ab => Fin.cases ab.1 (fun _ => ab.2)

/-- The real side of privacy over `dealSource source` is the correlated execution restricted to
the coalition. -/
theorem dealSource_bind_realJoint
    (proto : Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins Out)
    (source : PMF (A × B)) (I : Finset (Fin 2)) :
    (dealSource source).bind (proto.realJoint noOracleWorld I) =
      (realCorrelated proto source).map (Prod.map I.restrict id) := by
  rw [Protocol.bind_realJoint, dealSource, PMF.bind_map]
  rfl

/-- The ideal distribution of `k` independent random 1-out-of-2 bit oblivious transfers:
party `0` (sender) receives `k` pairs of independent fair bits, and party `1` (receiver) receives
`k` independent fair choice bits paired with the selected sender bits. -/
@[expose] noncomputable def idealROT (k : ℕ) : PMF ((i : Fin 2) → (Fin k → Bool × Bool)) :=
  (PMF.uniformOfFintype ((Fin k → Bool × Bool) × (Fin k → Bool))).map
    fun (senderBits, choices) =>
      Fin.cases senderBits (fun _ j => (choices j, otSelect (senderBits j) (choices j)))

/-- The input-free functionality of `k` independent random 1-out-of-2 bit oblivious transfers: it
samples uniform sender pairs and receiver choices and outputs the sender pairs to party `0` and
the choices with the selected bits to party `1`. -/
noncomputable def rotFunctionality (k : ℕ) :
    Functionality 2 (fun _ => Unit) (fun _ => Fin k → Bool × Bool) :=
  fun _ => (fun (senderBits, choices) =>
      (Fin.cases senderBits (fun _ j => (choices j, otSelect (senderBits j) (choices j))) :
        (i : Fin 2) → Fin k → Bool × Bool)) <$>
    ProbComp.uniform ((Fin k → Bool × Bool) × (Fin k → Bool))

/-- `rotFunctionality k` samples `idealROT k`. -/
@[simp] theorem eval_rotFunctionality (k : ℕ) (x : (i : Fin 2) → Unit) :
    ProbComp.eval (rotFunctionality k x) = idealROT k := by
  rw [rotFunctionality, ProbComp.eval_map, ProbComp.eval_uniform]
  rfl

/-- The ideal joint distribution of `rotFunctionality k`: sample `idealROT k`, then the simulated
views from the coalition's outputs. -/
private theorem eval_idealJoint_rotFunctionality {k : ℕ} {I : Finset (Fin 2)}
    (S : SetupSimulator sc (fun _ => Unit) (Fin.cases A (fun _ => B)) Coins
      (fun _ => Fin k → Bool × Bool) I) (x : (i : Fin 2) → Unit) :
    ProbComp.eval (idealJoint (rotFunctionality k) I S x) =
      (idealROT k).bind fun y => (ProbComp.eval (S (fun _ => ()) (I.restrict y))).map (·, y) := by
  rw [eval_idealJoint, eval_rotFunctionality]

private theorem realWithInputDist_eq_map_pure {In : Fin 2 → Type}
    (proto : Protocol 2 noOracleSpec sc In Coins Out) (inputDist : PMF (In 0 × In 1)) :
    realWithInputDist proto inputDist =
      (inputDist.bind fun xy => (ProbComp.eval (proto.sampleCoins 0)).bind fun r0 =>
        (ProbComp.eval (proto.sampleCoins 1)).map fun r1 => ((xy.1, r0), (xy.2, r1))).map
        fun ω =>
          let st := pairVec ω.1 ω.2
          let views : (i : Fin 2) → PartyView In Coins sc i :=
            fun i => ⟨(st i).1, (st i).2, stepsExecPure proto.steps st i⟩
          (views, fun i => proto.outputOfView i (views i)) := by
  have hpi : ProbComp.eval (OracleComp.pi proto.sampleCoins) =
      (ProbComp.eval (proto.sampleCoins 0)).bind fun r0 =>
        (ProbComp.eval (proto.sampleCoins 1)).map fun r1 => pairVec r0 r1 := by
    rw [OracleComp.pi_succ, OracleComp.pi_succ, OracleComp.pi_zero]
    simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.map_bind,
      PMF.pure_map]
    congr 1 with r0 : 1
    rw [← PMF.bind_pure_comp]
    congr 1 with r1 : 1
    exact congrArg PMF.pure (funext fun i => by fin_cases i <;> rfl)
  simp only [realWithInputDist, Protocol.evalWith_eq, hpi, stepsEvalWith_eq_pure, PMF.pure_map,
    PMF.map_bind]
  congr 1 with xy : 1
  rw [PMF.bind_bind]
  congr 1 with r0 : 1
  rw [PMF.bind_map, PMF.map_comp, ← PMF.bind_pure_comp]
  congr 1 with r1 : 1
  dsimp only [Function.comp_def]
  congr 1
  have hst : (fun i : Fin 2 => (pairVec xy.1 xy.2 i, pairVec r0 r1 i)) =
      pairVec (xy.1, r0) (xy.2, r1) := funext fun i => by fin_cases i <;> rfl
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  · rw [hst]
    fin_cases i <;> rfl

/-- Public communication over any joint input distribution `inputDist : PMF (In 0 × In 1)` never
increases conditional mutual information: `I((In₀, R₀); (In₁, R₁) | T) ≤ I(In₀; In₁)`. -/
theorem condMutualInfo_transcript_le_mutualInfo_input {In : Fin 2 → Type}
    [Finite (In 0)] [Finite (In 1)] [Finite (Coins 0)] [Finite (Coins 1)]
    [Finite (PublicTranscript sc)]
    (proto : Protocol 2 noOracleSpec sc In Coins Out)
    (inputDist : PMF (In 0 × In 1)) :
    condMutualInfo ((realWithInputDist proto inputDist).map fun (views, _) =>
      (transcriptOfView proto 0 (views 0),
        ((views 0).input, (views 0).coins, transcriptOfView proto 0 (views 0)),
        ((views 1).input, (views 1).coins, transcriptOfView proto 0 (views 0)))) ≤
      mutualInfo inputDist := by
  let ν := inputDist.bind fun xy => (ProbComp.eval (proto.sampleCoins 0)).bind fun r0 =>
    (ProbComp.eval (proto.sampleCoins 1)).map fun r1 => ((xy.1, r0), (xy.2, r1))
  let T_pure (ω : (In 0 × Coins 0) × (In 1 × Coins 1)) :=
    stepsTranscriptPure proto.steps (pairVec ω.1 ω.2)
  have hBase : condMutualInfo (ν.map fun ω => (T_pure ω, ω.1, ω.2)) ≤ mutualInfo inputDist := by
    have hUnit : condMutualInfo (ν.map fun ω => ((), ω.1, ω.2)) = mutualInfo inputDist := by
      rw [condMutualInfo_map, entropy_map_eq_of_comp ν (F := fun ω => ω.1) (e := ((), ·))
          (fun _ _ h => congrArg Prod.snd h) (fun _ _ => rfl),
        entropy_map_eq_of_comp ν (F := fun ω => ω.2) (e := ((), ·))
          (fun _ _ h => congrArg Prod.snd h) (fun _ _ => rfl),
        entropy_map_eq_of_comp ν (F := fun ω => (ω.1, ω.2)) (e := ((), ·))
          (fun _ _ h => congrArg Prod.snd h) (fun _ _ => rfl),
        show (ν.map fun _ => ()).entropy = 0 from
          entropy_eq_zero_of_subsingleton_support _ fun _ _ _ _ => rfl,
        sub_zero, ← mutualInfo_map]
      exact (congrArg mutualInfo (PMF.map_id ν)).trans (mutualInfo_bind_pair_indep inputDist _ _)
    have hStrip := (condMutualInfo_map_congr_cond ν (C := T_pure) Prod.fst Prod.snd (e := ((), ·))
      (fun _ _ h => congrArg Prod.snd h) (fun _ _ => rfl)).symm
    exact hStrip.trans_le ((condMutualInfo_steps_transcriptPure_le ν Prod.fst Prod.snd (fun _ => ())
      proto.steps Prod.fst Prod.snd ⟨Prod.fst, fun _ _ => rfl⟩ ⟨Prod.fst, fun _ _ => rfl⟩).trans_eq
      hUnit)
  refine le_trans ?_ hBase
  rw [realWithInputDist_eq_map_pure proto inputDist, PMF.map_comp, show condMutualInfo (ν.map _) =
      condMutualInfo (ν.map fun ω =>
        (T_pure ω, (ω.1.1, ω.1.2, T_pure ω), (ω.2.1, ω.2.2, T_pure ω))) from
    congrArg (fun f => condMutualInfo (ν.map f)) <| funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => by
      dsimp only [Function.comp_def, transcriptOfView]
      rw [stepsTranscriptOfView_execPure proto.steps (pairVec _ _) 0]; rfl]
  exact (condMutualInfo_map_le_of_comp ν T_pure
    (fun ω => (ω.1, T_pure ω)) (fun ω => (ω.1.1, ω.1.2, T_pure ω))
    (fun ω => (ω.2, T_pure ω)) (fun ω => (ω.2.1, ω.2.2, T_pure ω))
    (fun p => (p.1.1, p.1.2, p.2)) (fun _ _ => rfl)
    (fun p => (p.1.1, p.1.2, p.2)) (fun _ _ => rfl)).trans_eq
    (condMutualInfo_map_pair_self ν T_pure Prod.fst Prod.snd)

/-- Public communication over a correlated source never increases conditional mutual information:
`I((A, R₀); (B, R₁) | T) ≤ I(A; B)`. -/
theorem condMutualInfo_transcript_le_mutualInfo
    [Finite A] [Finite B] [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    (proto : Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins Out)
    (source : PMF (A × B)) :
    condMutualInfo ((realCorrelated proto source).map fun (views, _) =>
      (transcriptOfView proto 0 (views 0),
        ((views 0).input, (views 0).coins, transcriptOfView proto 0 (views 0)),
        ((views 1).input, (views 1).coins, transcriptOfView proto 0 (views 0))) :
        PMF (PublicTranscript sc × (A × Coins 0 × PublicTranscript sc) ×
          (B × Coins 1 × PublicTranscript sc))) ≤
      mutualInfo source := by
  let In : Fin 2 → Type := Fin.cases A (fun _ => B)
  have := finite_finCases (A := A) (B := B) 0
  have := finite_finCases (A := A) (B := B) 1
  have hreal : realCorrelated proto source =
      realWithInputDist proto (source : PMF (In 0 × In 1)) :=
    congrArg source.bind (funext fun ab => congrArg (proto.evalWith noOracleWorld)
      (funext fun i => by fin_cases i <;> rfl))
  refine Eq.trans_le ?_
    (condMutualInfo_transcript_le_mutualInfo_input proto (source : PMF (In 0 × In 1)))
  rw [hreal]; rfl

private theorem partyView_input_eq_of_mem_support_evalWith
    {In Coins Out : Fin 2 → Type} (proto : Protocol 2 noOracleSpec sc In Coins Out)
    {x : (i : Fin 2) → In i} {views : (i : Fin 2) → PartyView In Coins sc i}
    {out : (i : Fin 2) → Out i}
    (h : (views, out) ∈ (proto.evalWith noOracleWorld x).support) (i : Fin 2) :
    (views i).input = x i := by
  simp only [Protocol.evalWith_eq, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at h
  rcases h with ⟨_, _, _, _, hres⟩
  exact congrArg (fun p => (p.1 i).input) hres.symm

private theorem transcriptOfView_zero_eq_one_of_mem_support_bind {Ω : Type*}
    {In Coins Out : Fin 2 → Type} (proto : Protocol 2 noOracleSpec sc In Coins Out)
    (μ : PMF Ω) (f : Ω → (i : Fin 2) → In i)
    {views : (i : Fin 2) → PartyView In Coins sc i} {out : (i : Fin 2) → Out i}
    (h : (views, out) ∈ (μ.bind fun a => proto.evalWith noOracleWorld (f a)).support) :
    transcriptOfView proto 0 (views 0) = transcriptOfView proto 1 (views 1) := by
  obtain ⟨_, _, hev⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
  exact transcriptOfView_zero_eq_one proto hev

private theorem output_eq_of_mem_support_bind {Ω : Type*}
    {In Coins Out : Fin 2 → Type} (proto : Protocol 2 noOracleSpec sc In Coins Out)
    (μ : PMF Ω) (f : Ω → (i : Fin 2) → In i)
    {views : (i : Fin 2) → PartyView In Coins sc i} {out : (i : Fin 2) → Out i}
    (h : (views, out) ∈ (μ.bind fun a => proto.evalWith noOracleWorld (f a)).support)
    (i : Fin 2) :
    out i = proto.outputOfView i ⟨(views i).input, (views i).coins,
      stepsReceivedOfTranscript proto.steps i ((views i).input, (views i).coins)
        (transcriptOfView proto 0 (views 0))⟩ := by
  obtain ⟨_, _, hev⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
  obtain ⟨hvw, hout⟩ := partyView_eq_of_mem_support_evalWith proto hev i
  exact hout.trans (congrArg (proto.outputOfView i) hvw)

private theorem indepUniform_of_map_eq_bind_uniform {Ω α β : Type*}
    [Fintype β] [Nonempty β] {ν : PMF Ω} {X : Ω → α} {Y : Ω → β} (μ : PMF α)
    (h : ν.map (fun ω => (X ω, Y ω)) =
      μ.bind fun x => (PMF.uniformOfFintype β).map (x, ·)) :
    IndepUniform ν X Y := by
  refine ⟨?_⟩
  have hX : ν.map X = μ := by
    rw [show ν.map X = (ν.map fun ω => (X ω, Y ω)).map Prod.fst by rw [PMF.map_comp]; rfl,
      h, map_fst_bind_pair]
  rw [hX, h]

private theorem indepUniform_of_map_eq_bind_bind_uniform {Ω α β γ δ : Type*}
    [Fintype β] [Nonempty β] {ν : PMF Ω} {X : Ω → δ} {Y : Ω → β}
    (μ : PMF α) (sim : α → PMF γ) (f : α → γ → δ)
    (h : ν.map (fun ω => (X ω, Y ω)) =
      μ.bind fun a => (PMF.uniformOfFintype β).bind fun b =>
        (sim a).map fun v => (f a v, b)) :
    IndepUniform ν X Y := by
  refine indepUniform_of_map_eq_bind_uniform (μ.bind fun a => (sim a).map (f a)) ?_
  rw [h, PMF.bind_bind]
  congr 1 with a : 1
  rw [PMF.bind_map]
  simp only [← PMF.bind_pure_comp, Function.comp_def]
  exact PMF.bind_comm _ _ _

private theorem map_eq_map_eval_idealJoint {δ : Type*} {X In Coins Out : Fin 2 → Type}
    {I : Finset (Fin 2)} {f : Functionality 2 X Out}
    {S : SetupSimulator sc X In Coins Out I} {x : (i : Fin 2) → X i}
    {real : PMF (((i : Fin 2) → PartyView In Coins sc i) × ((i : Fin 2) → Out i))}
    (hPriv : ProbComp.eval (idealJoint f I S x) = real.map (Prod.map I.restrict id))
    (g : (((i : Fin 2) → PartyView In Coins sc i) × ((i : Fin 2) → Out i)) → δ)
    (proj : (((i : I) → PartyView In Coins sc i) × ((i : Fin 2) → Out i)) → δ)
    (hproj : ∀ ω ∈ real.support, g ω = proj (I.restrict ω.1, ω.2)) :
    real.map g = (ProbComp.eval (idealJoint f I S x)).map proj := by
  rw [map_congr_on_support real g _ hproj, hPriv, PMF.map_comp]
  rfl

private theorem indepUniform_of_idealJoint_bind_uniform
    {Ω α β δ : Type*} {X In Coins Out : Fin 2 → Type} [Fintype β] [Nonempty β]
    {ν : PMF Ω} {DX : Ω → δ} {DY : Ω → β}
    {f : Functionality 2 X Out} {I : Finset (Fin 2)}
    (S : SetupSimulator sc X In Coins Out I) (x : (i : Fin 2) → X i)
    (proj : (((i : I) → PartyView In Coins sc i) × ((i : Fin 2) → Out i)) → δ × β)
    (hReal : ν.map (fun ω => (DX ω, DY ω)) =
      (ProbComp.eval (idealJoint f I S x)).map proj)
    {μ : PMF α} {g : α → β → (i : Fin 2) → Out i}
    (hf : ProbComp.eval (f x) = μ.bind fun a => (PMF.uniformOfFintype β).map (g a))
    (r : α → (i : I) → Out i) (hr : ∀ a b, I.restrict (g a b) = r a)
    (outF : α → ((i : I) → PartyView In Coins sc i) → δ)
    (hproj : ∀ a b v, proj (v, g a b) = (outF a v, b)) :
    IndepUniform ν DX DY := by
  refine indepUniform_of_map_eq_bind_bind_uniform μ
    (fun a => ProbComp.eval (S (I.restrict x) (r a))) outF ?_
  rw [hReal, eval_idealJoint, hf, PMF.map_bind, PMF.bind_bind]
  congr 1 with a : 1
  rw [PMF.bind_map]
  dsimp only [Function.comp_def]
  congr 1 with b : 1
  rw [hr a b, PMF.map_comp]
  exact congrArg (PMF.map · _) (funext fun v => hproj a b v)

private theorem mutualInfo_map_prodMap {α α' β β' : Type*}
    [Finite α] [Finite α'] [Finite β] [Finite β']
    (p : PMF (α × β)) {e₁ : α → α'} {e₂ : β → β'}
    (he₁ : Function.Injective e₁) (he₂ : Function.Injective e₂) :
    mutualInfo (p.map (Prod.map e₁ e₂)) = mutualInfo p := by
  rw [show (Prod.map e₁ e₂ : α × β → α' × β') = fun x => (e₁ x.1, e₂ x.2) from rfl,
    mutualInfo_map_congr p (fun x => e₁ x.1) he₂ (fun _ _ => rfl),
    ← mutualInfo_map_swap, PMF.map_comp]
  exact (mutualInfo_map_congr p Prod.snd he₁ (fun _ _ => rfl)).trans (mutualInfo_map_swap p)

private theorem idealROT_eq_reparam (k : ℕ) :
    idealROT k =
      (PMF.uniformOfFintype (Fin k → Bool × Bool)).bind fun rb =>
        (PMF.uniformOfFintype (Fin k → Bool)).map fun ub =>
          Fin.cases (fun j => if (rb j).1 then (ub j, (rb j).2) else ((rb j).2, ub j))
            (fun _ => rb) := by
  rw [idealROT]
  relabel_uniform (fun sc : (Fin k → Bool × Bool) × (Fin k → Bool) =>
    (fun j => (sc.2 j, otSelect (sc.1 j) (sc.2 j)),
      fun j => otSelect (sc.1 j) (!(sc.2 j)))) with sc
  · rintro ⟨s₁, c₁⟩ ⟨s₂, c₂⟩ h
    obtain ⟨hr, hu⟩ := Prod.mk.inj h
    obtain rfl : c₁ = c₂ := funext fun j => congrArg Prod.fst (congrFun hr j)
    refine Prod.ext (funext fun j => ?_) rfl
    have hrj := congrArg Prod.snd (congrFun hr j)
    have huj := congrFun hu j
    cases h1 : c₁ j <;> simp_all [otSelect, Prod.ext_iff]
  · funext i
    fin_cases i
    · exact funext fun j => by cases h1 : sc.2 j <;> simp [h1, otSelect]
    · rfl

/-- **Ahlswede–Csiszár-style upper bound for correlated-source MPC protocols**:
any two-party plain-channel protocol over correlated source `source : PMF (A × B)` that realizes
`k` independent random OTs (`rotFunctionality k`) with perfect semi-honest privacy against `{0}`
and `{1}` requires `(k : ℝ) ≤ I(A; B)`. -/
theorem rot_le_mutualInfo
    [Finite A] [Finite B] [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    {k : ℕ}
    (proto : Protocol 2 noOracleSpec sc (Fin.cases A (fun _ => B)) Coins
      (fun _ => Fin k → Bool × Bool))
    (source : PMF (A × B))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc (fun _ => Unit) (Fin.cases A (fun _ => B)) Coins
        (fun _ => Fin k → Bool × Bool) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (fun _ => dealSource source) (rotFunctionality k) S) :
    (k : ℝ) ≤ mutualInfo source := by
  have hFin0 := finite_finCases (A := A) (B := B) 0
  have hFin1 := finite_finCases (A := A) (B := B) 1
  let real := realCorrelated proto source
  let outA (p : A × Coins 0 × PublicTranscript sc) :=
    proto.outputOfView 0 ⟨p.1, p.2.1, stepsReceivedOfTranscript proto.steps 0 (p.1, p.2.1) p.2.2⟩
  let outB (p : B × Coins 1 × PublicTranscript sc) :=
    proto.outputOfView 1 ⟨p.1, p.2.1, stepsReceivedOfTranscript proto.steps 1 (p.1, p.2.1) p.2.2⟩
  have hPriv0 : ProbComp.eval (idealJoint (rotFunctionality k) {0} (S {0}) fun _ => ()) =
      real.map (Prod.map ({0} : Finset (Fin 2)).restrict id) :=
    (hPriv {0} (by decide) _).trans (dealSource_bind_realJoint proto source {0})
  have hPriv1 : ProbComp.eval (idealJoint (rotFunctionality k) {1} (S {1}) fun _ => ()) =
      real.map (Prod.map ({1} : Finset (Fin 2)).restrict id) :=
    (hPriv {1} (by decide) _).trans (dealSource_bind_realJoint proto source {1})
  have hCorrect : ∀ ω ∈ real.support, ∀ j : Fin k,
      (ω.2 1 j).2 = otSelect (ω.2 0 j) (ω.2 1 j).1 := by
    rintro ⟨views, out⟩ hω j
    have hmem : (({0} : Finset (Fin 2)).restrict views, out) ∈
        (ProbComp.eval (idealJoint (rotFunctionality k) {0} (S {0}) fun _ => ())).support := by
      rw [hPriv0]; exact (PMF.mem_support_map_iff _ _ _).mpr ⟨_, hω, rfl⟩
    simp only [eval_idealJoint_rotFunctionality, idealROT, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hmem
    rcases hmem with ⟨_, ⟨⟨sb, ch⟩, _, rfl⟩, _, _, hy_eq⟩
    rw [← congrArg Prod.snd hy_eq]
    rfl
  have hAlicePriv :
      IndepUniform real (fun ω => (ω.2 0, transcriptOfView proto 0 (ω.1 0)))
        (fun ω => rotChoices (ω.2 1)) :=
    indepUniform_of_idealJoint_bind_uniform (S {0}) (fun _ => ())
      (fun (v0, y) => ((y 0, transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩)),
        rotChoices (y 1)))
      (map_eq_map_eval_idealJoint hPriv0 _ _ fun _ _ => rfl)
      (by
        rw [eval_rotFunctionality, idealROT, ← uniformOfFintype_prod, PMF.map_bind]
        congr 1 with sb : 1; rw [PMF.map_comp])
      (fun sb => restrictSingleton (F := fun _ => Fin k → Bool × Bool) 0 sb)
      (fun _ _ => restrictSingleton_eq 0 _)
      (fun sb v0 => (sb, transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩)))
      fun _ _ _ => rfl
  have hBobPriv :
      IndepUniform real (fun ω => (transcriptOfView proto 0 (ω.1 0), ω.2 1))
        (fun ω => rotUnselected (ω.2 0) (ω.2 1)) := by
    refine indepUniform_of_idealJoint_bind_uniform (S {1}) (fun _ => ())
      (fun (v1, y) => ((transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩), y 1),
        rotUnselected (y 0) (y 1)))
      (map_eq_map_eval_idealJoint hPriv1 _ _ fun ⟨_, _⟩ hω =>
        Prod.ext (Prod.ext (transcriptOfView_zero_eq_one_of_mem_support_bind proto source _ hω)
          rfl) rfl)
      (by rw [eval_rotFunctionality, idealROT_eq_reparam])
      (fun rb => restrictSingleton (F := fun _ => Fin k → Bool × Bool) 1 rb)
      (fun _ _ => restrictSingleton_eq 1 _)
      (fun rb v1 => (transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩), rb))
      fun rb _ _ => Prod.ext rfl (funext fun j => ?_)
    dsimp only [rotUnselected]
    rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ, Fin.cases_zero]
    cases hc : (rb j).1 <;> simp only [Bool.not_false, Bool.not_true, otSelect,
      Bool.false_eq_true, ↓reduceIte]
  have hSourceEq : real.map (fun ω => ((ω.1 0).input, (ω.1 1).input)) = source := by
    have h := bind_evalWith_map_input proto source
      (fun ab => (Fin.cases ab.1 (fun _ => ab.2) : (i : Fin 2) → Fin.cases A (fun _ => B) i))
      (fun a : A => a) (fun b : B => b)
    exact h.trans (PMF.map_id source)
  rw [← hSourceEq]
  exact natCast_le_mutualInfo_of_rot real (fun ω => (ω.1 0).input) (fun ω => (ω.1 1).input)
    (fun ω => ((ω.1 0).input, (ω.1 0).coins, transcriptOfView proto 0 (ω.1 0)))
    (fun ω => ((ω.1 1).input, (ω.1 1).coins, transcriptOfView proto 0 (ω.1 0)))
    (fun ω => transcriptOfView proto 0 (ω.1 0)) (fun ω => ω.2 0) (fun ω => ω.2 1)
    (hSourceEq ▸ condMutualInfo_transcript_le_mutualInfo proto source)
    outA (fun ⟨_, _⟩ hω => output_eq_of_mem_support_bind proto source _ hω 0)
    outB (fun ⟨_, _⟩ hω => output_eq_of_mem_support_bind proto source _ hω 1)
    hCorrect hAlicePriv hBobPriv

end Correlated2PC

/-! ### Chosen-input OT protocols over correlated randomness -/

section ChosenInputOT

variable {A B : Type} {sc : Schedule 2 noOracleSpec} {ExtIn Coins Out : Fin 2 → Type}

/-- Real execution of a correlated-source protocol taking external party inputs
`x : (i : Fin 2) → ExtIn i`. -/
@[expose] noncomputable def realCorrelatedWithInput
    (proto : Protocol 2 noOracleSpec sc (fun i => ExtIn i × Fin.cases A (fun _ => B) i) Coins Out)
    (source : PMF (A × B)) (x : (i : Fin 2) → ExtIn i) :
    PMF (((i : Fin 2) → PartyView (fun i => ExtIn i × Fin.cases A (fun _ => B) i) Coins sc i) ×
      ((i : Fin 2) → Out i)) :=
  source.bind fun ab =>
    proto.evalWith noOracleWorld (fun i => (x i, Fin.cases ab.1 (fun _ => ab.2) i))

/-- The trusted setup dealing correlated source `source : PMF (A × B)` next to the external inputs
`x`: party `i` receives `(x i, share i)`. Privacy over `source` with external inputs is
`PerfectSemiHonestPrivateProperWithSetup` with setup `dealSourceWithInput source`. -/
noncomputable def dealSourceWithInput (source : PMF (A × B))
    (x : (i : Fin 2) → ExtIn i) : PMF ((i : Fin 2) → ExtIn i × Fin.cases A (fun _ => B) i) :=
  source.map fun ab i => (x i, Fin.cases ab.1 (fun _ => ab.2) i)

/-- The real side of privacy over `dealSourceWithInput source` on inputs `x` is the correlated
execution on `x` restricted to the coalition. -/
theorem dealSourceWithInput_bind_realJoint
    (proto : Protocol 2 noOracleSpec sc (fun i => ExtIn i × Fin.cases A (fun _ => B) i) Coins Out)
    (source : PMF (A × B)) (I : Finset (Fin 2)) (x : (i : Fin 2) → ExtIn i) :
    (dealSourceWithInput source x).bind (proto.realJoint noOracleWorld I) =
      (realCorrelatedWithInput proto source x).map (Prod.map I.restrict id) := by
  rw [Protocol.bind_realJoint, dealSourceWithInput, PMF.bind_map]
  rfl

/-- Reparametrize `(y1, u)` into sender input tables `Fin k → Bool → Bool` relative to choice
vector `c : Fin k → Bool` so `x0 j (c j) = y1 j` and `x0 j (!(c j)) = u j`. -/
private def otPairEquiv {k : ℕ} (c : Fin k → Bool) :
    ((Fin k → Bool) × (Fin k → Bool)) ≃ (Fin k → Bool → Bool) where
  toFun p j b := if b == c j then p.1 j else p.2 j
  invFun x0 := (fun j => x0 j (c j), fun j => x0 j (!(c j)))
  left_inv p := Prod.ext (funext fun j => by cases hc : c j <;> simp [hc])
    (funext fun j => by cases hc : c j <;> simp [hc])
  right_inv x0 := funext fun j => funext fun b => by cases hc : c j <;> cases b <;> simp [hc]

private theorem eval_idealJoint_batchOT {k : ℕ} {I : Finset (Fin 2)}
    (S : SetupSimulator sc ((batchOTSpec k Bool).Query ())
      (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
      ((batchOTSpec k Bool).Answer ()) I)
    (x : (i : Fin 2) → (batchOTSpec k Bool).Query () i) :
    ProbComp.eval (idealJoint (batchOTFunctionality k Bool) I S x) =
      (ProbComp.eval (S (I.restrict x) (I.restrict (batchOTAnswer x)))).map
        (·, batchOTAnswer x) := by
  rw [eval_idealJoint, batchOTFunctionality, Functionality.ofDeterministic, ProbComp.eval_pure,
    PMF.pure_bind]

private theorem map_realCorrelatedWithInput_eq_ideal_map {k : ℕ} {I : Finset (Fin 2)}
    {proto : Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
      ((batchOTSpec k Bool).Answer ())}
    {source : PMF (A × B)}
    {S : SetupSimulator sc ((batchOTSpec k Bool).Query ())
      (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
      ((batchOTSpec k Bool).Answer ()) I}
    (hPriv : ∀ x, ProbComp.eval (idealJoint (batchOTFunctionality k Bool) I S x) =
      (realCorrelatedWithInput proto source x).map (Prod.map I.restrict id))
    (x : (i : Fin 2) → (batchOTSpec k Bool).Query () i)
    {δ : Type*}
    (g : (((i : Fin 2) → PartyView _ Coins sc i) ×
      ((i : Fin 2) → (batchOTSpec k Bool).Answer () i)) → δ)
    (proj : (((i : I) → PartyView _ Coins sc i) ×
      ((i : Fin 2) → (batchOTSpec k Bool).Answer () i)) → δ)
    (hproj : ∀ ω ∈ (realCorrelatedWithInput proto source x).support,
      g ω = proj (I.restrict ω.1, ω.2)) :
    (realCorrelatedWithInput proto source x).map g =
      (ProbComp.eval (S (I.restrict x) (I.restrict (batchOTAnswer x)))).map
        fun v => proj (v, batchOTAnswer x) := by
  rw [map_eq_map_eval_idealJoint (hPriv x) g proj hproj, eval_idealJoint_batchOT, PMF.map_comp]
  rfl

private theorem chosenOT_inOfSupport {k : ℕ}
    (proto : Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
      ((batchOTSpec k Bool).Answer ()))
    (source : PMF (A × B))
    (x0 : (batchOTSpec k Bool).Query () 0) (x1 : (batchOTSpec k Bool).Query () 1)
    {views : (i : Fin 2) → PartyView _ Coins sc i}
    {out : (i : Fin 2) → (batchOTSpec k Bool).Answer () i}
    (hmem : (views, out) ∈ (realCorrelatedWithInput proto source (pairVec x0 x1)).support) :
    (views 0).input.1 = x0 ∧ (views 1).input.1 = x1 := by
  obtain ⟨_, _, hev⟩ := (PMF.mem_support_bind_iff _ _ _).mp hmem
  exact ⟨congrArg Prod.fst (partyView_input_eq_of_mem_support_evalWith proto hev 0),
    congrArg Prod.fst (partyView_input_eq_of_mem_support_evalWith proto hev 1)⟩

private theorem chosenOT_alicePriv {k : ℕ}
    (proto : Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
      ((batchOTSpec k Bool).Answer ()))
    (source : PMF (A × B))
    (S0 : SetupSimulator sc ((batchOTSpec k Bool).Query ())
      (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
      ((batchOTSpec k Bool).Answer ()) {0})
    (hPriv0 : ∀ x, ProbComp.eval (idealJoint (batchOTFunctionality k Bool) {0} S0 x) =
      (realCorrelatedWithInput proto source x).map (Prod.map ({0} : Finset (Fin 2)).restrict id))
    (eQ0 : (Fin k → Bool → Bool) ≃ (batchOTSpec k Bool).Query () 0)
    (eQ1 : (Fin k → Bool) ≃ (batchOTSpec k Bool).Query () 1)
    (heQ0 : ∀ x0 j b, eQ0 x0 j b = x0 j b) (heQ1 : ∀ x1 j, eQ1 x1 j = x1 j)
    {real : PMF (((i : Fin 2) → PartyView _ Coins sc i) ×
      ((i : Fin 2) → (batchOTSpec k Bool).Answer () i))}
    (hRealUnif : real = (PMF.uniformOfFintype (Fin k → Bool → Bool)).bind fun x0 =>
      (PMF.uniformOfFintype (Fin k → Bool)).bind fun x1 =>
        realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1))) :
    IndepUniform real
      (fun ω => (fun j => ((ω.1 0).input.1 j false, (ω.1 0).input.1 j true),
        transcriptOfView proto 0 (ω.1 0)))
      (fun ω => rotChoices fun j => ((ω.1 1).input.1 j, ω.2 1 j)) := by
  let sOf : (Fin k → Bool → Bool) → (Fin k → Bool × Bool) := fun x0 j => (x0 j false, x0 j true)
  refine indepUniform_of_map_eq_bind_bind_uniform
    (PMF.uniformOfFintype (Fin k → Bool → Bool))
    (fun x0 => ProbComp.eval (S0 (restrictSingleton 0 (eQ0 x0))
      (restrictSingleton 0 (F := (batchOTSpec k Bool).Answer ()) ())))
    (fun x0 v0 => (sOf x0, transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩))) ?_
  rw [hRealUnif, PMF.map_bind]
  congr 1 with x0 : 1
  rw [PMF.map_bind]
  congr 1 with x1 : 1
  refine (map_realCorrelatedWithInput_eq_ideal_map hPriv0 (pairVec (eQ0 x0) (eQ1 x1)) _
    (fun (v0, _) => ((sOf x0, transcriptOfView proto 0 (v0 ⟨0, Finset.mem_singleton_self 0⟩)), x1))
    fun ⟨views, out⟩ hω => ?_).trans ?_
  · obtain ⟨hin0, hin1⟩ := chosenOT_inOfSupport proto source (eQ0 x0) (eQ1 x1) hω
    exact Prod.ext (Prod.ext (funext fun j => by simp only [sOf, hin0, heQ0]) rfl)
      (funext fun j => by simp only [rotChoices, hin1, heQ1])
  · rw [restrictSingleton_eq 0 (pairVec (F := (batchOTSpec k Bool).Query ()) (eQ0 x0) (eQ1 x1)),
      restrictSingleton_eq 0 (batchOTAnswer _)]
    rfl

private theorem chosenOT_bobPriv {k : ℕ}
    (proto : Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
      ((batchOTSpec k Bool).Answer ()))
    (source : PMF (A × B))
    (S1 : SetupSimulator sc ((batchOTSpec k Bool).Query ())
      (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
      ((batchOTSpec k Bool).Answer ()) {1})
    (hPriv1 : ∀ x, ProbComp.eval (idealJoint (batchOTFunctionality k Bool) {1} S1 x) =
      (realCorrelatedWithInput proto source x).map (Prod.map ({1} : Finset (Fin 2)).restrict id))
    (eQ0 : (Fin k → Bool → Bool) ≃ (batchOTSpec k Bool).Query () 0)
    (eQ1 : (Fin k → Bool) ≃ (batchOTSpec k Bool).Query () 1)
    (heQ0 : ∀ x0 j b, eQ0 x0 j b = x0 j b) (heQ1 : ∀ x1 j, eQ1 x1 j = x1 j)
    {real : PMF (((i : Fin 2) → PartyView _ Coins sc i) ×
      ((i : Fin 2) → (batchOTSpec k Bool).Answer () i))}
    (hRealUnif : real = (PMF.uniformOfFintype (Fin k → Bool → Bool)).bind fun x0 =>
      (PMF.uniformOfFintype (Fin k → Bool)).bind fun x1 =>
        realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1))) :
    IndepUniform real
      (fun ω => (transcriptOfView proto 0 (ω.1 0), fun j => ((ω.1 1).input.1 j, ω.2 1 j)))
      (fun ω => rotUnselected
        (fun j => ((ω.1 0).input.1 j false, (ω.1 0).input.1 j true))
        (fun j => ((ω.1 1).input.1 j, ω.2 1 j))) := by
  let eA1 : (Fin k → Bool) ≃ (batchOTSpec k Bool).Answer () 1 := Equiv.cast rfl
  refine indepUniform_of_map_eq_bind_bind_uniform
    (PMF.uniformOfFintype ((Fin k → Bool) × (Fin k → Bool)))
    (fun xy => ProbComp.eval (S1 (restrictSingleton 1 (eQ1 xy.1)) (restrictSingleton 1 (eA1 xy.2))))
    (fun xy v1 => (transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩),
      fun j => (xy.1 j, xy.2 j))) ?_
  have hRealRe : real =
      (PMF.uniformOfFintype ((Fin k → Bool) × (Fin k → Bool))).bind fun xy =>
        (PMF.uniformOfFintype (Fin k → Bool)).bind fun u =>
          realCorrelatedWithInput proto source
            (pairVec (eQ0 (otPairEquiv xy.1 (xy.2, u))) (eQ1 xy.1)) := by
    rw [hRealUnif, PMF.bind_comm, ← uniformOfFintype_prod, PMF.bind_bind]
    simp only [PMF.bind_map]
    congr 1 with x1 : 1
    relabel_uniform (otPairEquiv x1)
  rw [hRealRe, PMF.map_bind]; congr 1 with ⟨x1, y1⟩ : 1
  rw [PMF.map_bind]; congr 1 with u : 1
  let x0 := otPairEquiv x1 (y1, u)
  refine (map_realCorrelatedWithInput_eq_ideal_map hPriv1 (pairVec (eQ0 x0) (eQ1 x1)) _
    (fun (v1, y) => ((transcriptOfView proto 1 (v1 ⟨1, Finset.mem_singleton_self 1⟩),
      fun j => (x1 j, y 1 j)), u))
    fun ⟨views, out⟩ hω => ?_).trans ?_
  · obtain ⟨hin0, hin1⟩ := chosenOT_inOfSupport proto source (eQ0 x0) (eQ1 x1) hω
    refine Prod.ext (Prod.ext (transcriptOfView_zero_eq_one_of_mem_support_bind proto source _ hω)
      (funext fun j => by dsimp only; rw [hin1, heQ1])) (funext fun j => ?_)
    dsimp only [rotUnselected]; rw [hin0, hin1, heQ0, heQ0, heQ1]
    cases hx : x1 j <;> simp only [x0, otPairEquiv, Equiv.coe_fn_mk, otSelect, hx] <;> rfl
  · have hy1 : batchOTAnswer (pairVec (F := (batchOTSpec k Bool).Query ()) (eQ0 x0) (eQ1 x1)) 1 =
        eA1 y1 := funext fun j => by
      change (eQ0 x0) j ((eQ1 x1) j) = y1 j
      rw [heQ0, heQ1]; simp only [x0, otPairEquiv, Equiv.coe_fn_mk, beq_self_eq_true, ↓reduceIte]
    rw [restrictSingleton_eq 1 (pairVec (F := (batchOTSpec k Bool).Query ()) (eQ0 x0) (eQ1 x1)),
      restrictSingleton_eq 1 (batchOTAnswer _), hy1]
    congr 1 with v1 : 1
    exact Prod.ext (Prod.ext rfl (funext fun j => Prod.ext rfl (congrFun hy1 j))) rfl

/-- Choosing uniform random sender tables and receiver choices turns any perfectly semi-honest
private chosen-input `k`-OT protocol (`batchOTFunctionality k Bool`) over correlated source
`source : PMF (A × B)` into a `k`-ROT protocol over `source`, hence `(k : ℝ) ≤ I(A; B)`. -/
theorem chosenOT_le_mutualInfo
    [Finite A] [Finite B] [Finite (Coins 0)] [Finite (Coins 1)] [Finite (PublicTranscript sc)]
    {k : ℕ}
    (proto : Protocol 2 noOracleSpec sc
      (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
      ((batchOTSpec k Bool).Answer ()))
    (source : PMF (A × B))
    (S : (I : Finset (Fin 2)) →
      SetupSimulator sc ((batchOTSpec k Bool).Query ())
        (fun i => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i) Coins
        ((batchOTSpec k Bool).Answer ()) I)
    (hPriv : PerfectSemiHonestPrivateProperWithSetup proto noOracleWorld
      (dealSourceWithInput source) (batchOTFunctionality k Bool) S) :
    (k : ℝ) ≤ mutualInfo source := by
  let eQ0 : (Fin k → Bool → Bool) ≃ (batchOTSpec k Bool).Query () 0 := Equiv.cast rfl
  let eQ1 : (Fin k → Bool) ≃ (batchOTSpec k Bool).Query () 1 := Equiv.cast rfl
  let eA : A ≃ Fin.cases A (fun _ => B) (0 : Fin 2) := Equiv.cast rfl
  let eB : B ≃ Fin.cases A (fun _ => B) (1 : Fin 2) := Equiv.cast rfl
  let In := fun i : Fin 2 => (batchOTSpec k Bool).Query () i × Fin.cases A (fun _ => B) i
  have hFin0 : Finite (In 0) := inferInstanceAs (Finite ((Fin k → Bool → Bool) × A))
  have hFin1 : Finite (In 1) := inferInstanceAs (Finite ((Fin k → Bool) × B))
  let inputDist : PMF (In 0 × In 1) := source.bind fun ab =>
    (PMF.uniformOfFintype (Fin k → Bool → Bool)).bind fun x0 =>
      (PMF.uniformOfFintype (Fin k → Bool)).map fun x1 =>
        ((eQ0 x0, eA ab.1), (eQ1 x1, eB ab.2))
  let real := realWithInputDist proto inputDist
  have hRealUnif : real = (PMF.uniformOfFintype (Fin k → Bool → Bool)).bind fun x0 =>
      (PMF.uniformOfFintype (Fin k → Bool)).bind fun x1 =>
        realCorrelatedWithInput proto source (pairVec (eQ0 x0) (eQ1 x1)) := by
    dsimp only [real, realWithInputDist, inputDist]
    simp only [PMF.bind_bind]
    rw [PMF.bind_comm]; congr 1 with x0 : 1
    simp only [PMF.bind_map]
    rw [PMF.bind_comm]
    congr 1 with x1 : 1
    exact congrArg source.bind (funext fun _ => congrArg (proto.evalWith noOracleWorld)
      (funext fun i => by fin_cases i <;> rfl))
  have hPriv0 : ∀ x, ProbComp.eval (idealJoint (batchOTFunctionality k Bool) {0} (S {0}) x) =
      (realCorrelatedWithInput proto source x).map (Prod.map ({0} : Finset (Fin 2)).restrict id) :=
    fun x => (hPriv {0} (by decide) x).trans (dealSourceWithInput_bind_realJoint proto source {0} x)
  have hPriv1 : ∀ x, ProbComp.eval (idealJoint (batchOTFunctionality k Bool) {1} (S {1}) x) =
      (realCorrelatedWithInput proto source x).map (Prod.map ({1} : Finset (Fin 2)).restrict id) :=
    fun x => (hPriv {1} (by decide) x).trans (dealSourceWithInput_bind_realJoint proto source {1} x)
  have hCorrect : ∀ ω ∈ real.support, ∀ j : Fin k,
      ω.2 1 j = otSelect ((ω.1 0).input.1 j false, (ω.1 0).input.1 j true) ((ω.1 1).input.1 j) := by
    rintro ⟨views, out⟩ hω j
    rw [hRealUnif, PMF.mem_support_bind_iff] at hω
    rcases hω with ⟨x0, _, hω⟩
    rw [PMF.mem_support_bind_iff] at hω
    rcases hω with ⟨x1, _, hω⟩
    obtain ⟨hin0, hin1⟩ := chosenOT_inOfSupport proto source (eQ0 x0) (eQ1 x1) hω
    have hmem : (({0} : Finset (Fin 2)).restrict views, out) ∈
        (ProbComp.eval (idealJoint (batchOTFunctionality k Bool) {0} (S {0})
          (pairVec (eQ0 x0) (eQ1 x1)))).support := by
      rw [hPriv0]; exact (PMF.mem_support_map_iff _ _ _).mpr ⟨_, hω, rfl⟩
    rw [eval_idealJoint_batchOT, PMF.mem_support_map_iff] at hmem
    rcases hmem with ⟨_, _, hy_eq⟩
    rw [hin0, hin1, ← congrFun (congrArg (fun p => p.2 1) hy_eq) j]
    change x0 j (x1 j) = otSelect (x0 j false, x0 j true) (x1 j)
    cases x1 j <;> rfl
  have hInputEq : real.map (fun ω => ((ω.1 0).input, (ω.1 1).input)) = inputDist :=
    (bind_evalWith_map_input proto inputDist (fun xy => pairVec xy.1 xy.2) id id).trans
      (PMF.map_id inputDist)
  have hMutualEq : mutualInfo inputDist = mutualInfo source := by
    let swap0 : In 0 ≃ A × (Fin k → Bool → Bool) := (Equiv.prodCongr eQ0.symm eA.symm).trans
      (Equiv.prodComm _ _)
    let swap1 : In 1 ≃ B × (Fin k → Bool) := (Equiv.prodCongr eQ1.symm eB.symm).trans
      (Equiv.prodComm _ _)
    have hmap : inputDist.map (Prod.map swap0 swap1) = source.bind fun ab =>
        (PMF.uniformOfFintype (Fin k → Bool → Bool)).bind fun x0 =>
          (PMF.uniformOfFintype (Fin k → Bool)).map fun x1 => ((ab.1, x0), (ab.2, x1)) := by
      dsimp only [inputDist]
      simp only [PMF.map_bind, PMF.map_comp]
      rfl
    rw [← mutualInfo_map_prodMap inputDist swap0.injective swap1.injective, hmap]
    exact mutualInfo_bind_pair_indep source _ _
  calc (k : ℝ)
      ≤ mutualInfo (real.map fun ω => ((ω.1 0).input, (ω.1 1).input)) :=
        natCast_le_mutualInfo_of_rot real (fun ω => (ω.1 0).input) (fun ω => (ω.1 1).input)
          (fun ω => ((ω.1 0).input, (ω.1 0).coins, transcriptOfView proto 0 (ω.1 0)))
          (fun ω => ((ω.1 1).input, (ω.1 1).coins, transcriptOfView proto 0 (ω.1 0)))
          (fun ω => transcriptOfView proto 0 (ω.1 0))
          (fun ω j => ((ω.1 0).input.1 j false, (ω.1 0).input.1 j true))
          (fun ω j => ((ω.1 1).input.1 j, ω.2 1 j))
          (hInputEq ▸ condMutualInfo_transcript_le_mutualInfo_input proto inputDist)
          (fun (x, _, _) j => (x.1 j false, x.1 j true)) (fun _ _ => rfl)
          (fun (x, r1, t) j => (x.1 j, proto.outputOfView 1
            ⟨x, r1, stepsReceivedOfTranscript proto.steps 1 (x, r1) t⟩ j))
          (fun ⟨_, _⟩ hω => funext fun j =>
            Prod.ext rfl (congrFun (output_eq_of_mem_support_bind proto inputDist _ hω 1) j))
          hCorrect
          (chosenOT_alicePriv proto source (S {0}) hPriv0 eQ0 eQ1
            (fun _ _ _ => rfl) (fun _ _ => rfl) hRealUnif)
          (chosenOT_bobPriv proto source (S {1}) hPriv1 eQ0 eQ1
            (fun _ _ _ => rfl) (fun _ _ => rfl) hRealUnif)
    _ = mutualInfo source := by rw [hInputEq, hMutualEq]

end ChosenInputOT

/-! ### Adaptive binary communication trees over correlated randomness -/

section CommunicationTrees

variable {X Y A B Z : Type*}

/-- **Ahlswede–Csiszár-style upper bound for binary communication trees**:
any `Cslib.Communication.Protocol` over joint source `μ : PMF (X × Y)` whose leaf-determined
outputs form `k` independent, correct, and perfectly private random OTs satisfies
`(k : ℝ) ≤ I(X; Y)`. -/
theorem commProtocol_rot_le_mutualInfo [Finite X] [Finite Y] {k : ℕ}
    (p : Cslib.Communication.Protocol X Y Z) (μ : PMF (X × Y))
    (outA : X × Fin p.leafCount → Fin k → Bool × Bool)
    (outB : Y × Fin p.leafCount → Fin k → Bool × Bool)
    (hCorrect : ∀ x y j, (x, y) ∈ μ.support →
      (outB (y, p.leaf x y) j).2 = otSelect (outA (x, p.leaf x y) j) (outB (y, p.leaf x y) j).1)
    (hAlicePriv : IndepUniform (p.transcriptLaw μ) (fun (x, _, t) => (outA (x, t), t))
      (fun (_, y, t) => rotChoices (outB (y, t))))
    (hBobPriv : IndepUniform (p.transcriptLaw μ) (fun (_, y, t) => (t, outB (y, t)))
      (fun (x, y, t) => rotUnselected (outA (x, t)) (outB (y, t)))) :
    (k : ℝ) ≤ mutualInfo μ := by
  let ν := p.transcriptLaw μ
  have hTrLaw : ν = PMF.map (fun q => (q.1, q.2, p.leaf q.1 q.2)) μ :=
    Cslib.Communication.Protocol.transcriptLaw_eq p μ
  have hCorr' : ∀ ω ∈ ν.support, ∀ j : Fin k,
      (outB (ω.2.1, ω.2.2) j).2 = otSelect (outA (ω.1, ω.2.2) j) (outB (ω.2.1, ω.2.2) j).1 := by
    rintro ⟨x, y, t⟩ hω j
    rw [hTrLaw, PMF.mem_support_map_iff] at hω
    obtain ⟨⟨x', y'⟩, hxy, heq⟩ := hω
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj heq
    exact hCorrect _ _ j hxy
  have hMu : ν.map (fun q => (q.1, q.2.1)) = μ := by
    rw [hTrLaw, PMF.map_comp]; exact PMF.map_id μ
  have hInfo : condMutualInfo (ν.map fun q => (q.2.2, (q.1, q.2.2), (q.2.1, q.2.2))) ≤
      mutualInfo (ν.map fun q => (q.1, q.2.1)) := by
    rw [condMutualInfo_map_pair_self ν (fun q => q.2.2) Prod.fst (fun q => q.2.1)]
    exact condMutualInfo_le_mutualInfo_of_internal_le_external ν
      (p.internalInfoCost_le_externalInfoCost μ)
  rw [← hMu]
  exact natCast_le_mutualInfo_of_rot ν Prod.fst (fun q => q.2.1)
    (fun q => (q.1, q.2.2)) (fun q => (q.2.1, q.2.2)) (fun q => q.2.2)
    (fun q => outA (q.1, q.2.2)) (fun q => outB (q.2.1, q.2.2))
    hInfo outA (fun _ _ => rfl) outB (fun _ _ => rfl) hCorr' hAlicePriv hBobPriv

/-- **Ahlswede–Csiszár-style upper bound for private-coin binary communication protocols** over
correlated source `source : PMF (A × B)`. -/
theorem privateCoin_rot_le_mutualInfo [Finite A] [Finite B] {a b k : ℕ}
    (P : Cslib.Communication.PrivateCoin a b A B Z) (source : PMF (A × B))
    (outA : (A × BitString a) × Fin P.leafCount → Fin k → Bool × Bool)
    (outB : (B × BitString b) × Fin P.leafCount → Fin k → Bool × Bool)
    (hCorrect : ∀ u v j, (u.1, v.1) ∈ source.support →
      (outB (v, P.leaf u v) j).2 = otSelect (outA (u, P.leaf u v) j) (outB (v, P.leaf u v) j).1)
    (hAlicePriv : IndepUniform (Cslib.Communication.Protocol.transcriptLaw P
        (Cslib.Communication.PrivateCoin.inputLaw a b source))
      (fun (x, _, t) => (outA (x, t), t)) (fun (_, y, t) => rotChoices (outB (y, t))))
    (hBobPriv : IndepUniform (Cslib.Communication.Protocol.transcriptLaw P
        (Cslib.Communication.PrivateCoin.inputLaw a b source))
      (fun (_, y, t) => (t, outB (y, t)))
      (fun (x, y, t) => rotUnselected (outA (x, t)) (outB (y, t)))) :
    (k : ℝ) ≤ mutualInfo source := by
  let μ := Cslib.Communication.PrivateCoin.inputLaw a b source
  have hMu : μ = source.bind fun ab =>
      (PMF.uniformOfFintype (BitString a)).bind fun ra =>
        (PMF.uniformOfFintype (BitString b)).map fun rb => ((ab.1, ra), (ab.2, rb)) := by
    rw [show (source.bind fun ab => (PMF.uniformOfFintype (BitString a)).bind fun ra =>
        (PMF.uniformOfFintype (BitString b)).map fun rb => ((ab.1, ra), (ab.2, rb))) =
        (source.bind fun ab => (PMF.uniformOfFintype (BitString a × BitString b)).map
          (ab, ·)).map (Equiv.prodProdProdComm A B (BitString a) (BitString b)) from by
      rw [PMF.map_bind, ← uniformOfFintype_prod]; congr 1 with ab : 1
      rw [PMF.map_bind, PMF.map_bind]; congr 1 with ra : 1
      rw [PMF.map_comp, PMF.map_comp]; rfl]
    refine PMF.ext fun ((x, r), (y, r')) => ?_
    rw [Cslib.Communication.PrivateCoin.inputLaw_apply, map_equiv_apply,
      bind_map_prodMk_apply, PMF.uniformOfFintype_apply]
    rfl
  have hCorr' : ∀ u v j, (u, v) ∈ μ.support →
      (outB (v, P.leaf u v) j).2 =
        otSelect (outA (u, P.leaf u v) j) (outB (v, P.leaf u v) j).1 := by
    intro ⟨x, r⟩ ⟨y, r'⟩ j huv
    rw [PMF.mem_support_iff, Cslib.Communication.PrivateCoin.inputLaw_apply,
      mul_ne_zero_iff] at huv
    exact hCorrect (x, r) (y, r') j huv.1
  have hBound := commProtocol_rot_le_mutualInfo P μ outA outB hCorr' hAlicePriv hBobPriv
  rwa [hMu, mutualInfo_bind_pair_indep] at hBound

end CommunicationTrees

end Cslib.Crypto.Protocols.OT
