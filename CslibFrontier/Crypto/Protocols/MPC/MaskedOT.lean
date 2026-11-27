/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.BatchOT.Sequential

/-!
# Oblivious transfer of masked values from an oblivious transfer of pads

`maskedOT mask unmask samplePads` is a two-party protocol for the single 1-out-of-2 transfer
`otFunctionality M` of values in `M`, in the hybrid model whose oracle is the single transfer
`otSpec G` of values in a pad type `G`. The sender (party `0`) samples a pair of pads
`r ← samplePads` as its coins. The parties call the pad transfer once: the sender submits the two
pads and the receiver (party `1`) its choice bit, so the receiver obtains the pad of its choice.
The sender then sends the pair `(mask r.1 m.1, mask r.2 m.2)` of its two values masked by the two
pads, and the receiver outputs `unmask` of its pad and the component of its choice.

This is the sender-masking step that turns a transfer of pads into a transfer of values of
another type, for instance a transfer of group elements into a transfer of words with
`mask r m = m ⊕ H r` for a key-derivation function `H`. It is original library infrastructure in
the style of `CslibFrontier/Crypto/Protocols/MPC/BatchOT/Sequential.lean`; no cited theorem is
claimed.

## What is proved

All statements are concrete and per instance (fixed input pair and distinguisher), in the hybrid
model with the ideal pad transfer `otWorld G`. The only hypothesis is that, under every pad `r`,
`unmask r` recovers the receiver's output `otOutputs x 1` from its mask; it is stated for the
value of the instance, so a mask that inverts only on words of a bounded length, such as the xor
with a key of fixed length, satisfies it on inputs of that length. `samplePads` is an arbitrary
joint distribution of the two pads.

* The execution outputs `otOutputs x` (`evalWith_maskedOT`).
* A corrupted sender sees only its input and its pads, so every distinguisher has advantage zero
  with the simulator `maskedOTSenderSim` (`semiHonestAdvantage_maskedOT_sender`).
* A corrupted receiver sees its pad and the two masked values. With the simulator
  `maskedOTReceiverSim`, which masks the receiver's output with its pad and fills the other
  component with a sample of a given distribution `pad`, the advantage of a distinguisher `D`
  *equals* the advantage of the explicit test `maskedOTPadTest mask x D` in telling, next to the
  receiver's pad, the masked unchosen value from a sample of `pad`
  (`semiHonestAdvantage_maskedOT_receiver_eq`). Nothing is assumed about this term.

* Substituting a protocol `Sub` for the pad transfer (`Protocol.compose`) gives a protocol for
  `otFunctionality M` in the model of `Sub`. When, for a coalition, every test has advantage at
  most `ε₁` against `maskedOT` with the ideal pad transfer and at most `ε₂` against `Sub`, every
  test has advantage at most `ε₁ + ε₂` against the composed protocol
  (`semiHonestAdvantage_maskedOT_compose_le_add`).

## What is not proved

* No bound on the pad-hiding term is derived from a property of `mask`: neither the statistical
  case (`mask r m = m ⊕ H r` for a universal hash `H` via a leftover hash lemma) nor a
  computational key-derivation assumption is instantiated here.
* The hypotheses of `semiHonestAdvantage_maskedOT_compose_le_add` range over all tests, so that
  theorem is a statement about statistically secure components. For a computationally secure pad
  transfer, such as the DDH transfer `ddhOTProbProtocol` against a corrupted receiver, the bound
  to use is `semiHonestAdvantage_compose_le_replacementBound` applied to `maskedOT`, with its
  explicit distinguishers; that bound is not specialized here.
* Simulators are provided for the coalitions `{0}` and `{1}` only. The composition theorems take
  a family of simulators over all coalitions, of which these are the members at `{0}` and `{1}`.
* No efficiency statement and no asymptotic statement (`ProtocolFamily.SemiHonestSecure`) is made.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.maskedOT`: the protocol.
* `Cslib.Crypto.Protocols.MPC.maskedOTSenderSim`, `Cslib.Crypto.Protocols.MPC.maskedOTReceiverSim`:
  the simulators of a corrupted sender and of a corrupted receiver.
* `Cslib.Crypto.Protocols.MPC.maskedOTPadTest`: the reduction from a distinguisher of a corrupted
  receiver's view to a test of the masked unchosen value.

## Main results

* `Cslib.Crypto.Protocols.MPC.evalWith_maskedOT`: the execution law, with the outputs of
  `otOutputs`.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_maskedOT_sender`: advantage zero against a
  corrupted sender.
* `Cslib.Crypto.Protocols.MPC.bind_eval_idealJoint_maskedOT_receiver`,
  `Cslib.Crypto.Protocols.MPC.bind_realJoint_maskedOT_receiver`: the ideal and the real game of a
  corrupted receiver against a test are the two pad-test experiments.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_maskedOT_receiver_eq`: the advantage against a
  corrupted receiver is the pad-hiding advantage of `maskedOTPadTest`.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_maskedOT_compose_le_add`: the bound after
  substituting a protocol for the pad transfer, for statistically secure components.
* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_compose_seqBatchOT_maskedOT_le_sum_roundGame`:
  an outer protocol over sequential masked transfers over a substituted pad transfer: per transfer,
  the advantage of one environment against `maskedOT` with the ideal pad transfer and against the
  pad transfer. Neither term is bounded here.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto
open _root_.Cslib.Crypto.Protocols.MPC.Composition
open scoped ENNReal

variable {G M : Type}

/-! ### The protocol -/

/-- Per-party coins of `maskedOT` with pads in `G`: the sender (party `0`) holds its pair of pads
and the receiver (party `1`) has no coins. -/
abbrev MaskedOTCoins (G : Type) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) (G × G) (fun _ => Unit) i

/-- The schedule of `maskedOT`: one transfer of a pad in `G`, the sender in slot `0` and the
receiver in slot `1`, then one message from the sender to the receiver carrying the two masked
values. -/
@[expose, reducible] def maskedOTSchedule (G M : Type) : Schedule 2 (otSpec G) :=
  [.oracle () (Function.Embedding.refl (Fin 2)), .message 0 1 (M × M)]

/-- The coin tuple of `maskedOT` in which the sender's pads are `r`. -/
private def maskedOTCoins (r : G × G) : (i : Fin 2) → MaskedOTCoins G i :=
  fun i => Fin.cases (motive := fun i => MaskedOTCoins G i) r (fun _ => ()) i

/-- The query of party `s` to the pad transfer: the sender submits its two pads and the receiver
its choice bit. -/
@[expose] def maskedOTQuery (s : Fin 2) : OTIn M s × MaskedOTCoins G s → OTIn G s :=
  Fin.cases (motive := fun s => OTIn M s × MaskedOTCoins G s → OTIn G s)
    (fun st => st.2) (fun _ st => st.1) s

/-- The sender's message: its two values masked by its two pads, in the order of the values. -/
@[expose] def maskedOTMsg (mask : G → M → M) (m : M × M) (r : G × G) : M × M :=
  (mask r.1 m.1, mask r.2 m.2)

/-- The local state of party `i` at the end of `maskedOTSchedule G M`: its input and coins, its
answer from the pad transfer and the message it received. -/
abbrev MaskedOTFinal (G M : Type) (i : Fin 2) : Type :=
  ((OTIn M i × MaskedOTCoins G i) ×
      (Round.oracle (spec := otSpec G) () (Function.Embedding.refl (Fin 2))).Received i) ×
    (Round.message (spec := otSpec G) 0 1 (M × M)).Received i

/-- The outputs of `maskedOT`: `()` for the sender; the receiver applies `unmask` of its pad to
the component of the sender's message selected by its choice bit, `true` selecting the second. -/
@[expose] def maskedOTOutput (unmask : G → M → M) (i : Fin 2) (st : MaskedOTFinal G M i) :
    OTOut M i :=
  Fin.cases (motive := fun i => MaskedOTFinal G M i → OTOut M i)
    (fun _ => ())
    (fun j (((σ, _), ans), msg) =>
      let b : Bool := σ
      let c : M × M := msg (Fin.fin_one_eq_zero j ▸ rfl)
      unmask (ans 1 (Fin.fin_one_eq_zero j ▸ rfl)) (if b then c.2 else c.1))
    i st

/-- **Oblivious transfer of masked values**, in the hybrid model whose oracle is the single
transfer `otSpec G` of a pad. The sender's coins are a pair of pads `r ← samplePads`. The parties
call the pad transfer on the two pads and the receiver's choice bit, the sender sends
`maskedOTMsg mask m r`, and the receiver outputs `unmask` of its pad and the component of its
choice (`maskedOTOutput`). -/
@[expose] def maskedOT (mask unmask : G → M → M) (samplePads : ProbComp (G × G)) :
    Protocol 2 (otSpec G) (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) where
  sampleCoins i := Fin.cases (motive := fun i => ProbComp (MaskedOTCoins G i))
    samplePads (fun _ => pure ()) i
  steps :=
    Steps.oracle (spec := otSpec G) (op := ()) (parties := Function.Embedding.refl (Fin 2))
      (fun s st => maskedOTQuery s st)
      (.message (fun ((m, r), _) => maskedOTMsg mask m r) (.done (maskedOTOutput unmask)))

/-! ### Views and the execution law -/

/-- The sender's view in a run with input `m` and pads `r`: it receives `()` from the pad transfer
and no message. -/
@[expose] def maskedOTSenderView (m : M × M) (r : G × G) :
    PartyView (OTIn M) (MaskedOTCoins G) (maskedOTSchedule G M) 0 :=
  ⟨m, r, (fun s hs => (show s = 0 from hs) ▸ (() : OTOut G 0), fun h => absurd h (by decide), ())⟩

/-- The receiver's view with choice bit `σ` when it obtains the pad `r` from the pad transfer and
receives the message `c`. -/
@[expose] def maskedOTReceiverView (σ : Bool) (r : G) (c : M × M) :
    PartyView (OTIn M) (MaskedOTCoins G) (maskedOTSchedule G M) 1 :=
  ⟨σ, (), (fun s hs => (show s = 1 from hs) ▸ (r : OTOut G 1), fun _ => c, ())⟩

/-- The views of both parties in the run of `maskedOT` on the inputs `x` with pads `r`: the
receiver obtains the pad selected by its choice bit and the message `maskedOTMsg mask (x 0) r`. -/
@[expose] def maskedOTViews (mask : G → M → M) (x : (i : Fin 2) → OTIn M i) (r : G × G) :
    (i : Fin 2) → PartyView (OTIn M) (MaskedOTCoins G) (maskedOTSchedule G M) i :=
  fun i => match i with
    | 0 => maskedOTSenderView (x 0) r
    | 1 =>
      let σ : Bool := x 1
      maskedOTReceiverView σ (if σ then r.2 else r.1) (maskedOTMsg mask (x 0) r)

/-- The transcripts of both parties after the two rounds of `maskedOT` from the states `st`. -/
private def maskedOTReceived (mask : G → M → M)
    (st : (i : Fin 2) → OTIn M i × MaskedOTCoins G i) (i : Fin 2) :
    (maskedOTSchedule G M).Received i :=
  (Round.deliverOracle (spec := otSpec G) (op := ()) (Function.Embedding.refl (Fin 2))
      (otOutputs fun s => maskedOTQuery s (st s)) i,
    Round.deliverMessage (maskedOTMsg mask (st 0).1 (st 0).2) i, ())

/-- With the ideal pad transfer the two rounds of `maskedOT` are deterministic. -/
private theorem evalWith_maskedOTSteps (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G)) (st : (i : Fin 2) → OTIn M i × MaskedOTCoins G i) :
    (maskedOT mask unmask samplePads).steps.evalWith (otWorld G) st =
      PMF.pure (maskedOTReceived mask st) := by
  simp only [maskedOT, Steps.evalWith_oracle, Steps.evalWith_message, Steps.evalWith_done,
    otWorld, otFunctionality, Functionality.ofDeterministic, ProbComp.eval_pure, PMF.pure_bind,
    PMF.pure_map]
  rfl

/-- Independent coin sampling draws the sender's pads. -/
private theorem eval_pi_maskedOTSampleCoins (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G)) :
    ProbComp.eval (OracleComp.pi (maskedOT mask unmask samplePads).sampleCoins) =
      (ProbComp.eval samplePads).bind fun r => PMF.pure (maskedOTCoins r) := by
  simp only [maskedOT, OracleComp.pi_succ, ProbComp.eval_bind, Fin.cases_succ]
  refine congrArg (PMF.bind _) (funext fun r => congrArg PMF.pure
    (funext (β := MaskedOTCoins G) fun i => ?_))
  fin_cases i <;> rfl

/-- The sender's view in a run with pads `r`. -/
private theorem maskedOTView_zero (mask : G → M → M) (x : (i : Fin 2) → OTIn M i) (r : G × G) :
    (⟨x 0, maskedOTCoins r 0, maskedOTReceived mask (fun i => (x i, maskedOTCoins r i)) 0⟩ :
        PartyView (OTIn M) (MaskedOTCoins G) (maskedOTSchedule G M) 0) =
      maskedOTViews mask x r 0 := by
  refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact Round.received_oracle_ext fun s hs => by
      obtain rfl : s = 0 := hs
      rfl
  · exact Round.received_message_eq_of_ne (by decide) _ _

/-- The receiver's view in a run with pads `r`. -/
private theorem maskedOTView_one (mask : G → M → M) (x : (i : Fin 2) → OTIn M i) (r : G × G) :
    (⟨x 1, maskedOTCoins r 1, maskedOTReceived mask (fun i => (x i, maskedOTCoins r i)) 1⟩ :
        PartyView (OTIn M) (MaskedOTCoins G) (maskedOTSchedule G M) 1) =
      maskedOTViews mask x r 1 := by
  refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact Round.received_oracle_ext fun s hs => by
      obtain rfl : s = 1 := hs
      rfl
  · exact Round.received_message_ext fun _ => rfl

/-- In a run with pads `r`, the receiver outputs `otOutputs x 1`. -/
private theorem outputOfView_maskedOT_one (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G)) (x : (i : Fin 2) → OTIn M i)
    (hmask : ∀ r, unmask r (mask r (otOutputs x 1)) = otOutputs x 1) (r : G × G) :
    (maskedOT mask unmask samplePads).outputOfView 1
        ⟨x 1, maskedOTCoins r 1, maskedOTReceived mask (fun i => (x i, maskedOTCoins r i)) 1⟩ =
      otOutputs x 1 := by
  have key : ∀ σ : Bool,
      (∀ r, unmask r (mask r (if σ then (x 0).2 else (x 0).1)) =
        if σ then (x 0).2 else (x 0).1) →
      unmask (if σ then r.2 else r.1) (if σ then mask r.2 (x 0).2 else mask r.1 (x 0).1) =
        if σ then (x 0).2 else (x 0).1 := fun σ h => by cases σ <;> exact h _
  exact key (x 1) hmask

/-- **Execution law of `maskedOT`.** When `unmask r` recovers the receiver's output
`otOutputs x 1` from its mask under every pad `r`, the execution with the ideal pad transfer draws
the sender's pads `r ← samplePads` and returns the views `maskedOTViews mask x r` and the outputs
`otOutputs x`: the receiver outputs the value of its choice. -/
theorem evalWith_maskedOT (mask unmask : G → M → M) (samplePads : ProbComp (G × G))
    (x : (i : Fin 2) → OTIn M i)
    (hmask : ∀ r, unmask r (mask r (otOutputs x 1)) = otOutputs x 1) :
    (maskedOT mask unmask samplePads).evalWith (otWorld G) x =
      (ProbComp.eval samplePads).bind fun r => PMF.pure (maskedOTViews mask x r, otOutputs x) := by
  rw [Protocol.evalWith_eq, eval_pi_maskedOTSampleCoins]
  simp only [evalWith_maskedOTSteps, PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
  refine congrArg (ProbComp.eval samplePads).bind
    (funext fun r => congrArg PMF.pure (Prod.ext ?_ ?_))
  · exact funext fun i => Fin.cases (maskedOTView_zero mask x r)
      (fun j => Fin.fin_one_eq_zero j ▸ maskedOTView_one mask x r) i
  · exact funext fun i => Fin.cases rfl
      (fun j => Fin.fin_one_eq_zero j ▸ outputOfView_maskedOT_one mask unmask samplePads x hmask r)
      i

/-! ### A corrupted sender -/

/-- Simulator for a corrupted sender (`{0}`): samples the pads and returns the sender's input and
pads, with no information from the pad transfer. -/
@[expose] def maskedOTSenderSim (samplePads : ProbComp (G × G)) :
    CoalitionSimulator (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) {0} :=
  fun xI _ => do
    let r ← samplePads
    return singletonView (maskedOTSenderView (xI ⟨0, Finset.mem_singleton_self 0⟩) r)

/-- **Perfect privacy against a corrupted sender**: the ideal joint distribution with
`maskedOTSenderSim` equals the real joint distribution with the ideal pad transfer. -/
theorem idealJoint_maskedOT_sender (mask unmask : G → M → M) (samplePads : ProbComp (G × G))
    (x : (i : Fin 2) → OTIn M i)
    (hmask : ∀ r, unmask r (mask r (otOutputs x 1)) = otOutputs x 1) :
    ProbComp.eval (idealJoint (otFunctionality M) {0} (maskedOTSenderSim samplePads) x) =
      (maskedOT mask unmask samplePads).realJoint (otWorld G) {0} x := by
  rw [Protocol.realJoint, evalWith_maskedOT mask unmask samplePads x hmask]
  simp only [idealJoint, otFunctionality, Functionality.ofDeterministic, maskedOTSenderSim,
    pure_bind, bind_assoc, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map,
    Prod.map, id, restrict_singleton]
  rfl

/-- A corrupted sender has advantage zero against every distinguisher. -/
theorem semiHonestAdvantage_maskedOT_sender (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G)) (x : (i : Fin 2) → OTIn M i)
    (hmask : ∀ r, unmask r (mask r (otOutputs x 1)) = otOutputs x 1)
    (D : ((i : ({0} : Finset (Fin 2))) →
        PartyView (OTIn M) (MaskedOTCoins G) (maskedOTSchedule G M) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :
    semiHonestAdvantage (maskedOT mask unmask samplePads) (otWorld G) (otFunctionality M) {0}
      (maskedOTSenderSim samplePads) x D = 0 :=
  (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ x).mpr
    (idealJoint_maskedOT_sender mask unmask samplePads x hmask) D

/-! ### A corrupted receiver -/

/-- The message with the value `c` in the component selected by the choice bit `σ` and `u` in the
other component; `true` selects the second component. -/
@[expose] def maskedOTSimMsg (σ : Bool) (c u : M) : M × M :=
  if σ then (u, c) else (c, u)

/-- The sender's message is its masked chosen value in the chosen component and its masked
unchosen value in the other. -/
private theorem maskedOTSimMsg_mask (mask : G → M → M) (m : M × M) (r : G × G) (σ : Bool) :
    maskedOTSimMsg σ (mask (if σ then r.2 else r.1) (if σ then m.2 else m.1))
      (if σ then mask r.1 m.1 else mask r.2 m.2) = maskedOTMsg mask m r := by
  cases σ <;> rfl

/-- Simulator for a corrupted receiver (`{1}`) with choice bit `σ` and output `y`: samples the
pads and a value `u ← pad`, and returns the view in which the receiver obtains the pad `r` of its
choice and the message with `mask r y` in the chosen component and `u` in the other. -/
@[expose] def maskedOTReceiverSim (mask : G → M → M) (samplePads : ProbComp (G × G))
    (pad : ProbComp M) :
    CoalitionSimulator (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) {1} :=
  fun xI yI => do
    let r ← samplePads
    let u ← pad
    let σ : Bool := xI ⟨1, Finset.mem_singleton_self 1⟩
    let y : M := yI ⟨1, Finset.mem_singleton_self 1⟩
    return singletonView (maskedOTReceiverView σ (if σ then r.2 else r.1)
      (maskedOTSimMsg σ (mask (if σ then r.2 else r.1) y) u))

/-- **The reduction from a corrupted receiver's distinguisher to a test of the masked unchosen
value.** Given the receiver's pad `r` and a candidate `u` for the masked unchosen value, the test
assembles the receiver's view on the inputs `x`, with `mask r` of the receiver's output in the
chosen component of the message and `u` in the other, and runs `D` on it and the outputs. -/
@[expose] def maskedOTPadTest (mask : G → M → M) (x : (i : Fin 2) → OTIn M i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn M) (MaskedOTCoins G) (maskedOTSchedule G M) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) (r : G) (u : M) : ProbComp Bool :=
  let σ : Bool := x 1
  D (singletonView (maskedOTReceiverView σ r (maskedOTSimMsg σ (mask r (otOutputs x 1)) u)),
    otOutputs x)

/-- **The ideal game of a corrupted receiver is the pad test on a sample of `pad`.** The ideal
joint distribution of `otFunctionality M` for the coalition `{1}` with the simulator
`maskedOTReceiverSim mask samplePads pad`, followed by a test `D`, draws the pads
`r ← samplePads` and `u ← pad` and runs `maskedOTPadTest mask x D` on the receiver's pad and `u`.
No hypothesis is needed. -/
theorem bind_eval_idealJoint_maskedOT_receiver (mask : G → M → M)
    (samplePads : ProbComp (G × G)) (pad : ProbComp M) (x : (i : Fin 2) → OTIn M i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn M) (MaskedOTCoins G) (maskedOTSchedule G M) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :
    ((ProbComp.eval (idealJoint (otFunctionality M) {1}
        (maskedOTReceiverSim mask samplePads pad) x)).bind fun r => ProbComp.eval (D r)) =
      ProbComp.eval (do
        let r ← samplePads
        let u ← pad
        let σ : Bool := x 1
        maskedOTPadTest mask x D (if σ then r.2 else r.1) u) := by
  rw [← ProbComp.eval_bind]
  simp only [idealJoint, otFunctionality, Functionality.ofDeterministic, maskedOTReceiverSim,
    pure_bind, bind_assoc]
  rfl

/-- **The real game of a corrupted receiver is the pad test on the masked unchosen value.** When
`unmask r` recovers the receiver's output from its mask under every pad `r`, the real joint
distribution of `maskedOT` with the ideal pad transfer for the coalition `{1}`, followed by a test
`D`, draws the pads `r ← samplePads` and runs `maskedOTPadTest mask x D` on the receiver's pad and
the sender's unchosen value masked by the other pad. -/
theorem bind_realJoint_maskedOT_receiver (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G)) (x : (i : Fin 2) → OTIn M i)
    (hmask : ∀ r, unmask r (mask r (otOutputs x 1)) = otOutputs x 1)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn M) (MaskedOTCoins G) (maskedOTSchedule G M) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :
    (((maskedOT mask unmask samplePads).realJoint (otWorld G) {1} x).bind fun r =>
        ProbComp.eval (D r)) =
      ProbComp.eval (do
        let r ← samplePads
        let σ : Bool := x 1
        maskedOTPadTest mask x D (if σ then r.2 else r.1)
          (if σ then mask r.1 (x 0).1 else mask r.2 (x 0).2)) := by
  rw [Protocol.realJoint, evalWith_maskedOT mask unmask samplePads x hmask]
  simp only [ProbComp.eval_bind, PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind,
    Prod.map, id, restrict_singleton]
  refine congrArg (PMF.bind _) (funext fun r => ?_)
  exact congrArg (fun c => ProbComp.eval
    (D (singletonView (maskedOTReceiverView _ _ c), otOutputs x)))
    (maskedOTSimMsg_mask mask (x 0) r (x 1)).symm

/-- **The advantage against a corrupted receiver is the pad-hiding advantage.** When `unmask r`
recovers the receiver's output from its mask under every pad `r`, the semi-honest advantage of `D`
against `maskedOT` with the ideal pad transfer, for the coalition `{1}` with the simulator
`maskedOTReceiverSim mask samplePads pad`, equals the advantage of the test
`maskedOTPadTest mask x D` between two experiments that both draw the pads `r ← samplePads` and
give the test the receiver's pad: in the first the candidate is a sample of `pad`, and in the
second it is the sender's unchosen value masked by the other pad. Nothing is assumed about `mask`,
`samplePads` or `pad` beyond that recovery, and the right-hand side is not bounded here. -/
theorem semiHonestAdvantage_maskedOT_receiver_eq (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G)) (pad : ProbComp M) (x : (i : Fin 2) → OTIn M i)
    (hmask : ∀ r, unmask r (mask r (otOutputs x 1)) = otOutputs x 1)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn M) (MaskedOTCoins G) (maskedOTSchedule G M) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :
    semiHonestAdvantage (maskedOT mask unmask samplePads) (otWorld G) (otFunctionality M) {1}
        (maskedOTReceiverSim mask samplePads pad) x D =
      Game.advantage
        (ProbComp.eval (do
          let r ← samplePads
          let u ← pad
          let σ : Bool := x 1
          maskedOTPadTest mask x D (if σ then r.2 else r.1) u))
        (ProbComp.eval (do
          let r ← samplePads
          let σ : Bool := x 1
          maskedOTPadTest mask x D (if σ then r.2 else r.1)
            (if σ then mask r.1 (x 0).1 else mask r.2 (x 0).2))) := by
  rw [semiHonestAdvantage]
  exact congrArg₂ Game.advantage
    ((ProbComp.eval_bind ..).trans
      (bind_eval_idealJoint_maskedOT_receiver mask samplePads pad x D))
    (bind_realJoint_maskedOT_receiver mask unmask samplePads x hmask D)

/-! ### Substituting a protocol for the pad transfer -/

variable {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}

/-- **The masked transfer over a substituted pad transfer, with uniform bounds.** Let `Sub` be a
protocol for the pad transfer `otFunctionality G` in a world `W₂`, with simulators `S₂`, and let
`S₁` be simulators of `maskedOT`. If, for the coalition `I`, every test has semi-honest advantage
at most `ε₁` against `maskedOT` with the ideal pad transfer on the inputs `x`, and at most `ε₂`
against `Sub` on every pair of inputs, then every test has advantage at most `ε₁ + ε₂` against
`(maskedOT mask unmask samplePads).compose fun _ => Sub`, for `otFunctionality M` with the composed
simulator.

Both hypotheses range over all tests, so they hold with small bounds only for statistically
secure components: for `I = {0}` the first holds with `ε₁ = 0`
(`semiHonestAdvantage_maskedOT_sender`), and for `I = {1}` it is a bound on the pad-hiding
advantage (`semiHonestAdvantage_maskedOT_receiver_eq`). For a computationally secure `Sub` the
bound to use is `semiHonestAdvantage_compose_le_replacementBound`, with its explicit
distinguishers. -/
theorem semiHonestAdvantage_maskedOT_compose_le_add (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G)) (W₂ : MultiOracleWorld spec₂)
    (Sub : Protocol 2 spec₂ sc₂ (OTIn G) Coins₂ (OTOut G))
    (S₁ : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) J)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn G) Coins₂ (OTOut G) J)
    (I : Finset (Fin 2)) (ε₁ ε₂ : ℝ≥0∞) (x : (i : Fin 2) → OTIn M i)
    (h₁ : ∀ D', (semiHonestAdvantage (maskedOT mask unmask samplePads) (otWorld G)
      (otFunctionality M) I (S₁ I) x D' : ℝ≥0∞) ≤ ε₁)
    (h₂ : ∀ q D', (semiHonestAdvantage Sub W₂ (otFunctionality G) I (S₂ I) q D' : ℝ≥0∞) ≤ ε₂)
    (D : ((i : I) → PartyView (OTIn M)
        (Schedule.ComposedCoins (fun _ => Coins₂) (MaskedOTCoins G) (maskedOTSchedule G M))
        (Schedule.compose (fun _ => sc₂) (maskedOTSchedule G M)) i) ×
      ((i : Fin 2) → OTOut M i) → ProbComp Bool) :
    (semiHonestAdvantage ((maskedOT mask unmask samplePads).compose fun _ => Sub) W₂
        (otFunctionality M) I
        (composeSim (maskedOT mask unmask samplePads) (S₁ I) (fun _ => S₂)) x D : ℝ≥0∞) ≤
      ε₁ + ε₂ := by
  have h₂' : ∀ J, J = I → ∀ q D',
      (semiHonestAdvantage Sub W₂ (otFunctionality G) J (S₂ J) q D' : ℝ≥0∞) ≤ ε₂ := by
    rintro J rfl
    exact h₂
  refine (semiHonestAdvantage_compose_le_replacementBound (maskedOT mask unmask samplePads)
    (otWorld G) W₂ (otFunctionality M) I (S₁ I) (fun _ => Sub) (fun _ => S₂) x D).trans
    (add_le_add (h₁ _) ?_)
  calc _ ≤ ∑' c₁, ProbComp.eval (OracleComp.pi (maskedOT mask unmask samplePads).sampleCoins) c₁ *
        ε₂ := by
        refine tsum_le_tsum fun c₁ => mul_le_mul' le_rfl ?_
        simp only [maskedOT, replacementBound, mul_zero, tsum_zero, add_zero]
        exact h₂' _ (Finset.ext fun _ => mem_subCoalition) _ _
    _ = ε₂ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **An outer protocol over sequential masked transfers over a substituted pad transfer, with one
environment per term.** Let `P` be any protocol that calls the batched transfer `batchOTSpec k M`,
such as Yao's protocol, with every call run by `seqBatchOT k M` over `maskedOT`, and the pad
transfer of `maskedOT` run by a protocol `Sub` in a world `W₂`. The semi-honest advantage of `D`
against the composed protocol, with the composed simulator, is at most the advantage of
`composeDistinguisher` against `P` with the ideal batched transfer, plus, for every call `i` of `P`
and every transfer `j < k`, two advantages of the environment `composeSeqBatchOTRoundEnv` of that
transfer followed by one further stage:

* between the ideal and the real game of `maskedOT` with the ideal pad transfer, against
  `composeDistinguisher` (for a corrupted receiver this is where the pads have to hide the value
  that was not chosen);
* between the ideal game of the pad transfer, with the simulator `S₂`, and its real game with
  `Sub` (`composeRoundEnv` of `maskedOT`).

Every term is the absolute difference of two acceptance probabilities of one environment, which
samples the coins of `P` and the pads and runs the earlier calls and transfers itself. Nothing is
assumed about `P`, `Sub`, `mask`, the simulators or `D`; no term is bounded here and no efficiency
of the environments is claimed. -/
theorem semiHonestAdvantage_compose_seqBatchOT_maskedOT_le_sum_roundGame {m : ℕ} (k : ℕ)
    {sc₁ : Schedule m (batchOTSpec k M)} {In Coins₁ Out : Fin m → Type}
    (P : Protocol m (batchOTSpec k M) sc₁ In Coins₁ Out) (mask unmask : G → M → M)
    (samplePads : ProbComp (G × G)) (W₂ : MultiOracleWorld spec₂)
    (Sub : Protocol 2 spec₂ sc₂ (OTIn G) Coins₂ (OTOut G))
    (Sm : (J : Finset (Fin 2)) →
      CoalitionSimulator (maskedOTSchedule G M) (OTIn M) (MaskedOTCoins G) (OTOut M) J)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn G) Coins₂ (OTOut G) J)
    (f : Functionality m In Out)
    (S₁ : (I : Finset (Fin m)) → CoalitionSimulator sc₁ In Coins₁ Out I)
    (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins
            (fun _ => Schedule.ComposedCoins (fun _ => Coins₂) (MaskedOTCoins G)
              (maskedOTSchedule G M))
            (fun _ => Unit) (seqBatchOTSchedule k M)) Coins₁ sc₁)
        (Schedule.compose
          (fun _ => Schedule.compose
            (fun _ => Schedule.compose (fun _ => sc₂) (maskedOTSchedule G M))
            (seqBatchOTSchedule k M)) sc₁) i) ×
      ((i : Fin m) → Out i) → ProbComp Bool) :
    semiHonestAdvantage
        (P.compose fun _ => (seqBatchOT k M).compose fun _ =>
          (maskedOT mask unmask samplePads).compose fun _ => Sub) W₂ f I
        (composeSim P (S₁ I)
          (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J)
            (fun _ J => composeSim (maskedOT mask unmask samplePads) (Sm J) (fun _ => S₂))))
        x D ≤
      semiHonestAdvantage P (batchOTWorld k M) f I (S₁ I) x
          (composeDistinguisher P
            (fun _ J => composeSim (seqBatchOT k M) (seqBatchOTSim k M J)
              (fun _ J => composeSim (maskedOT mask unmask samplePads) (Sm J) (fun _ => S₂)))
            I x D) +
        ∑ i ∈ Finset.range sc₁.oracleRounds, ∑ j ∈ Finset.range k,
          (Game.advantage
              ((composeSeqBatchOTRoundEnv k M P W₂
                  ((maskedOT mask unmask samplePads).compose fun _ => Sub)
                  (fun J => composeSim (maskedOT mask unmask samplePads) (Sm J) (fun _ => S₂))
                  I x D i j).bind (Sum.elim PMF.pure fun c =>
                (ProbComp.eval (idealJoint (otFunctionality M) c.coalition (Sm c.coalition)
                  c.query)).bind fun r =>
                    ProbComp.eval (composeDistinguisher (maskedOT mask unmask samplePads)
                      (fun _ => S₂) c.coalition c.query c.guess r)))
              ((composeSeqBatchOTRoundEnv k M P W₂
                  ((maskedOT mask unmask samplePads).compose fun _ => Sub)
                  (fun J => composeSim (maskedOT mask unmask samplePads) (Sm J) (fun _ => S₂))
                  I x D i j).bind (Sum.elim PMF.pure fun c =>
                ((maskedOT mask unmask samplePads).realJoint (otWorld G) c.coalition
                  c.query).bind fun r =>
                    ProbComp.eval (composeDistinguisher (maskedOT mask unmask samplePads)
                      (fun _ => S₂) c.coalition c.query c.guess r))) +
            Game.advantage
              ((composeSeqBatchOTRoundEnv k M P W₂
                  ((maskedOT mask unmask samplePads).compose fun _ => Sub)
                  (fun J => composeSim (maskedOT mask unmask samplePads) (Sm J) (fun _ => S₂))
                  I x D i j).bind (Sum.elim PMF.pure fun c =>
                (composeRoundEnv (maskedOT mask unmask samplePads) (otWorld G) W₂ (fun _ => Sub)
                  (fun _ => S₂) c.coalition c.query c.guess 0).bind
                    (roundGame fun op J q =>
                      ProbComp.eval (idealJoint (otWorld G op) J (S₂ J) q))))
              ((composeSeqBatchOTRoundEnv k M P W₂
                  ((maskedOT mask unmask samplePads).compose fun _ => Sub)
                  (fun J => composeSim (maskedOT mask unmask samplePads) (Sm J) (fun _ => S₂))
                  I x D i j).bind (Sum.elim PMF.pure fun c =>
                (composeRoundEnv (maskedOT mask unmask samplePads) (otWorld G) W₂ (fun _ => Sub)
                  (fun _ => S₂) c.coalition c.query c.guess 0).bind
                    (roundGame fun _ J q => Sub.realJoint W₂ J q)))) := by
  refine (semiHonestAdvantage_compose_seqBatchOT_compose_le_sum_roundGame k M P W₂
    ((maskedOT mask unmask samplePads).compose fun _ => Sub)
    (fun J => composeSim (maskedOT mask unmask samplePads) (Sm J) (fun _ => S₂)) f S₁ I x D).trans
    (add_le_add le_rfl (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_))
  have h := advantage_bind_compose_le_add_sum_roundGame
    (composeSeqBatchOTRoundEnv k M P W₂ ((maskedOT mask unmask samplePads).compose fun _ => Sub)
      (fun J => composeSim (maskedOT mask unmask samplePads) (Sm J) (fun _ => S₂)) I x D i j)
    (fun _ => maskedOT mask unmask samplePads) (fun _ => otWorld G) (fun _ => W₂)
    (fun _ => otFunctionality M) (fun _ => Sm) (fun _ _ => Sub) (fun _ _ => S₂)
    (fun c => c.coalition) (fun c => c.query) (fun c => c.guess) 1 (fun _ => le_rfl)
  rw [Finset.sum_range_one] at h
  exact h

end Cslib.Crypto.Protocols.MPC
