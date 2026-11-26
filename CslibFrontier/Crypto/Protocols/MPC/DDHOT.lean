/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.Finite
public import CslibFrontier.Crypto.Protocols.MPC.Advantage
public import CslibFrontier.Crypto.Protocols.MPC.BatchOT
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.Uniform.Translate
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.SuppCases

/-!
# Three-Message DDH 1-out-of-2 Oblivious Transfer

This module formalizes a three-message 1-out-of-2 oblivious transfer protocol from the Decision
Diffie-Hellman (DDH) assumption over a finite additive group `G` that is a `ZMod q`-module, with a
public element `g`, expressed as a two-party protocol `ddhOTProtocol` in
`Cslib.Crypto.Protocols.MPC` computing `otFunctionality G` (compatible with `batchOTSpec 1 G` from
`CslibFrontier/Crypto/Protocols/MPC/BatchOT.lean`). Groups are written additively, so the textbook
`g^a` is `a • g`. The protocol is a variant of the DDH-based protocol of [BonehShoup2023],
Section 23.5.7, Figure 23.17; DDH-based oblivious transfer of this kind goes back to
[NaorPinkas2001]. Its rounds are:

1. **Round 1 (`.message 0 1 G`):** The sender (party `0`) samples `a : ZMod q` and sends
   `u = a • g` to the receiver (party `1`).
2. **Round 2 (`.message 1 0 (G × G)`):** The receiver samples `b : ZMod q`, sets `v = b • g`,
   and sends `(w₀, w₁) = if σ then (u - v, v) else (v, u - v)` so that the chosen branch key
   `w_σ = v` has known discrete logarithm `b`, the unchosen branch key `w_{1-σ} = u - v` has
   unknown discrete logarithm, and `w₀ + w₁ = u`.
3. **Round 3 (`.message 0 1 ((G × G) × (G × G))`):** The sender checks `w₀ + w₁ = u`. If the check
   holds, it encrypts each branch `i ∈ {0, 1}` with fresh randomization coins
   `(rᵢ, sᵢ) : ZMod q × ZMod q` via `ddhOTEncryptBranch g u wᵢ mᵢ rᵢ sᵢ a` (since the sender holds
   `a` with `u = a • g`, this equals ElGamal encryption under `wᵢ` with exponent `rᵢ + a * sᵢ`;
   if the check fails, the sender sends zeros). The receiver decrypts its chosen ciphertext
   `(e_σ, c_σ)` as `c_σ - b • e_σ`.

## Differences from Figure 23.17

* In Figure 23.17 the sender samples its first message `d` uniformly from the group, without
  knowing its discrete logarithm. Here the sender samples `a` and sends `u = a • g`, so it
  knows the discrete logarithm of `u`.
* Figure 23.17 encrypts both branches with one exponent `β` and one first component `g^β`. Here
  each branch `i` has its own coins `(rᵢ, sᵢ)` and its own first component `rᵢ • g + sᵢ • u`.
* Figure 23.17 has no check. Here the sender checks `w₀ + w₁ = u`, the additive form of the check
  in [BonehShoup2023], Section 23.5.7.3, Remark 23.6, and sends zeros instead of aborting when the
  check fails. `ddhOTUncheckedProtocol` omits the check.
* The honest parties of `ddhOTProtocol` draw exact uniform exponents in `ZMod q`
  (`sampleDDHOTSenderCoins` and the receiver's `ProbComp.uniform (ZMod q)`), and their views hold
  these exponents. The source requires the parties' only random objects to be random bit strings,
  from which they derive values statistically indistinguishable from uniform ([BonehShoup2023],
  Section 23.5.7.2, "Further assumptions about randomness", p. 1059). No bounded-time fair-coin
  machine draws an exact uniform element of `ZMod q` when `q` is not a power of two;
  `ddhOTProtocolWith` parameterizes the protocol by arbitrary party coin types, samplers, and
  exponent projections so that `PartyView.coins` retains the actual coin objects drawn by each
  party, and `CslibFrontier/Crypto/Protocols/MPC/DDHOT/Family.lean` instantiates it with raw
  fair-coin bit strings via `sampleExpBits` (`ddhOTProbProtocol`, `ddhOTProbFamily`).
* Theorem 23.7 of [BonehShoup2023] is stated for Figure 23.17 in the restricted interactive
  execution framework of Section 23.5.6. The results below are proved directly for this variant in
  the stand-alone `Protocol` model.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.DDHOTSenderCoins`,
  `Cslib.Crypto.Protocols.MPC.sampleDDHOTSenderCoins`: the sender's five `ZMod q` coins and their
  uniform sampler.
* `Cslib.Crypto.Protocols.MPC.ddhOTSchedule`: the three-message point-to-point schedule.
* `Cslib.Crypto.Protocols.MPC.ddhOTProtocolWith`, `Cslib.Crypto.Protocols.MPC.ddhOTProtocol`: the
  checked three-message DDH OT protocol, parameterized by party coin samplers and exponent
  projections and specialized to exact uniform coins.
* `Cslib.Crypto.Protocols.MPC.ddhOTViewsWith`, `Cslib.Crypto.Protocols.MPC.ddhOTViews`: the pair of
  party views produced by a run of `ddhOTProtocolWith` on given inputs and coins.
* `Cslib.Crypto.Protocols.MPC.ddhOTUncheckedProtocol`: the variant omitting the `w₀ + w₁ = u`
  check.
* `Cslib.Crypto.Protocols.MPC.ddhOTSenderReplyOf`: the honest sender's Round 3 reply in a protocol
  along `ddhOTSchedule G`, for an arbitrary Round 2 message.
* `Cslib.Crypto.Protocols.MPC.ddhOTSenderSim`, `Cslib.Crypto.Protocols.MPC.ddhOTReceiverSim`: the
  semi-honest simulators for a corrupted sender (`{0}`) and a corrupted receiver (`{1}`), which
  draw uniform coins and return `Cslib.Crypto.Protocols.MPC.ddhOTSenderSimWithCoins` and
  `Cslib.Crypto.Protocols.MPC.ddhOTReceiverSimWithCoins`.
* `Cslib.Crypto.Protocols.MPC.ddhOTReductionWithCoins`, `Cslib.Crypto.Protocols.MPC.ddhOTReduction`:
  the DDH reduction induced by a receiver distinguisher, on given coins and on uniform coins.
* `Cslib.Crypto.Protocols.MPC.ddhOTUncheckedRealGame`,
  `Cslib.Crypto.Protocols.MPC.ddhOTUncheckedIdealGame`: the real and ideal games for a malicious
  receiver against `ddhOTUncheckedProtocol`.

## Main results

* `Cslib.Crypto.Protocols.MPC.evalWith_ddhOTProtocolWith`,
  `Cslib.Crypto.Protocols.MPC.ddhOTProtocolWith_output_of_mem_support`: **execution law and
  correctness** — for any party coin samplers and exponent projections, every execution of
  `ddhOTProtocolWith` produces `ddhOTViewsWith` and outputs `m_σ` for the receiver and `()` for the
  sender.
* `Cslib.Crypto.Protocols.MPC.idealJoint_ddhOT_sender_with`,
  `Cslib.Crypto.Protocols.MPC.idealJoint_ddhOT_sender`,
  `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_ddhOT_sender`: **perfect sender privacy** — when
  the honest receiver's exponent is uniform, the ideal joint distribution equals the real one for
  any sender coin sampler, so in `ddhOTProtocol` every distinguisher has advantage zero.
* `Cslib.Crypto.Protocols.MPC.real_receiver_eq_ddhRealExperiment_of`,
  `Cslib.Crypto.Protocols.MPC.ideal_receiver_eq_ddhRandomExperiment_of`,
  `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_ddhOT_receiver_eq`: **receiver privacy as a
  per-instance equality** — when `g` generates `G`, a corrupted receiver's distinguishing
  advantage equals `Cslib.Crypto.ddhAdvantage q g (ddhOTReduction g q x D)`, the fixed-group DDH
  advantage of `CslibFrontier/Crypto/Computational/DiffieHellman/Finite.lean`. There is no
  security parameter and no efficiency certificate for `ddhOTReduction`, so this is not a
  computational privacy theorem. `CslibFrontier/Crypto/Protocols/MPC/DDHOT/Family.lean` runs the
  fair-coin protocol over a `PrimeOrderGroupFamily` with raw bit-string party coins
  (`ddhOTProbProtocol`, `ddhOTProbFamily`) and reduces a corrupted receiver to the DDH assumption
  with a certified reduction (`Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTReceiverGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhOTReceiverToDDHDistinguisher`).
  `CslibFrontier/Crypto/Protocols/MPC/DDHOT/Simulators.lean` gives PPT simulators and proves
  stand-alone asymptotic semi-honest security of `ddhOTProbFamily` across all static coalitions as a
  step toward Theorem 23.7
  (`Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTProbFamily_semiHonestSecure`).
* `Cslib.Crypto.Protocols.MPC.ddhOTSenderReply_eq_unchecked_of_add`,
  `Cslib.Crypto.Protocols.MPC.ddhOTSenderReply_eq_zero_of_add_ne`,
  `Cslib.Crypto.Protocols.MPC.ddhOTAttackBothMessages_eq`,
  `Cslib.Crypto.Protocols.MPC.succProbability_ddhOTUncheckedIdealGame_le`,
  `Cslib.Crypto.Protocols.MPC.ddhOTUnchecked_malicious_receiver_advantage`: **malicious-receiver
  attack on the unchecked variant** — a malicious receiver that sends `(b₀ • g, b₁ • g)` in
  Round 2 of `ddhOTUncheckedProtocol` recovers both `(m₀, m₁)` from one run. A simulator that
  chooses one query bit `τ` and receives only `m_τ` outputs both messages with probability at most
  `(Fintype.card G : ℝ)⁻¹`, so the advantage against every such simulator is at least
  `1 - (Fintype.card G : ℝ)⁻¹`.

## References

* [M. Naor and B. Pinkas, *Efficient Oblivious Transfer Protocols*][NaorPinkas2001]
* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 23.5.7 (Figure 23.17, Theorem 23.7, the randomness assumptions on p. 1059, and
  Remark 23.6).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto
open scoped ENNReal NNReal

variable {G : Type} [AddCommGroup G]

/-! ### 1-out-of-2 Oblivious Transfer functionality and protocol syntax -/

/-- Per-party input types for 1-out-of-2 Oblivious Transfer over message type `M`:
party `0` (sender) holds `(m₀, m₁) : M × M` and party `1` (receiver) holds `σ : Bool`. -/
abbrev OTIn (M : Type) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) (M × M) (fun _ => Bool) i

/-- Per-party output types for 1-out-of-2 Oblivious Transfer over message type `M`:
party `0` (sender) receives `Unit` and party `1` (receiver) receives `m_σ : M`. -/
abbrev OTOut (M : Type) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) Unit (fun _ => M) i

/-- Deterministic output tuple of `otFunctionality M`: `()` for the sender and `m_σ` for the
receiver. -/
@[expose] def otOutputs {M : Type} (x : (i : Fin 2) → OTIn M i) : (i : Fin 2) → OTOut M i :=
  fun i => Fin.cases (motive := fun i => OTOut M i) ()
    (fun _ =>
      let σ : Bool := x 1
      if σ then (x 0).2 else (x 0).1) i

/-- Ideal functionality for 1-out-of-2 Oblivious Transfer over `M`. -/
@[expose] def otFunctionality (M : Type) : Functionality 2 (OTIn M) (OTOut M) :=
  Functionality.ofDeterministic otOutputs

/-- Convert a single-transfer input tuple `x : (i : Fin 2) → OTIn M i` into a query to
`batchOTSpec 1 M` from `CslibFrontier/Crypto/Protocols/MPC/BatchOT.lean`. -/
@[expose] def otInputToBatchOTQuery {M : Type} (x : (i : Fin 2) → OTIn M i)
    (s : Fin 2) : (batchOTSpec 1 M).Query () s :=
  Fin.cases (motive := fun s => (batchOTSpec 1 M).Query () s)
    (fun _ b => if b then (x 0).2 else (x 0).1)
    (fun _ _ => x 1)
    s

/-- `otOutputs` agrees with the single-transfer specialization `k = 1` of `batchOTAnswer`. -/
theorem otOutputs_eq_batchOTAnswer {M : Type} (x : (i : Fin 2) → OTIn M i) :
    otOutputs x 1 = batchOTAnswer (otInputToBatchOTQuery x) 1 0 :=
  rfl

/-- The sender's random coins in the DDH OT protocol over `ZMod q`: the Round 1 exponent `a` and
two encryption coins `(rᵢ, sᵢ)` for each branch `i ∈ {0, 1}`. -/
@[ext] structure DDHOTSenderCoins (q : ℕ) where
  /-- Round 1 exponent `a` for the sender's first message `u = a • g`. -/
  exponent : ZMod q
  /-- Randomizer `r₀` for branch `0` encryption. -/
  coinR₀ : ZMod q
  /-- Randomizer `s₀` for branch `0` encryption. -/
  coinS₀ : ZMod q
  /-- Randomizer `r₁` for branch `1` encryption. -/
  coinR₁ : ZMod q
  /-- Randomizer `s₁` for branch `1` encryption. -/
  coinS₁ : ZMod q
deriving DecidableEq

/-- Per-party random coin types parameterized by sender coin type `C₀` and receiver coin type
`C₁`. -/
abbrev DDHOTCoinsWith (C₀ C₁ : Type) : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) C₀ (fun _ => C₁) i

/-- Per-party random coin types for `ddhOTProtocol`. -/
abbrev DDHOTCoins (q : ℕ) : Fin 2 → Type :=
  DDHOTCoinsWith (DDHOTSenderCoins q) (ZMod q)

/-- Sample the sender's five exponents uniformly from `ZMod q`. -/
@[expose] noncomputable def sampleDDHOTSenderCoins (q : ℕ) [NeZero q] :
    ProbComp (DDHOTSenderCoins q) := do
  let a ← ProbComp.uniform (ZMod q)
  let r₀ ← ProbComp.uniform (ZMod q)
  let s₀ ← ProbComp.uniform (ZMod q)
  let r₁ ← ProbComp.uniform (ZMod q)
  let s₁ ← ProbComp.uniform (ZMod q)
  return ⟨a, r₀, s₀, r₁, s₁⟩

/-- Pair of sender and receiver coins as a dependent tuple over `Fin 2`. -/
private def ddhOTCoinsWith {C₀ C₁ : Type} (c₀ : C₀) (c₁ : C₁) :
    (i : Fin 2) → DDHOTCoinsWith C₀ C₁ i :=
  fun i => Fin.cases (motive := fun i => DDHOTCoinsWith C₀ C₁ i) c₀ (fun _ => c₁) i

/-- Three-message point-to-point schedule for the DDH OT protocol: sender to receiver (`G`),
receiver to sender (`G × G`), and sender to receiver (`(G × G) × (G × G)`). -/
abbrev ddhOTSchedule (G : Type) : Schedule 2 noOracleSpec :=
  [.message 0 1 G, .message 1 0 (G × G), .message 0 1 ((G × G) × (G × G))]

/-- Round 2 receiver message: given `u : G`, choice bit `σ : Bool`, and coin `b : ZMod q`,
outputs `(w₀, w₁)` with `w_σ = b • g` and `w_{1-σ} = u - b • g`. -/
@[expose] def ddhOTReceiverMsg {q : ℕ} [Module (ZMod q) G] (g : G) (σ : Bool) (b : ZMod q)
    (u : G) : G × G :=
  let v := b • g
  if σ then (u - v, v) else (v, u - v)

/-- Honest Round 2 receiver messages always satisfy the sender's check `w.1 + w.2 = u`. -/
theorem ddhOTReceiverMsg_add {q : ℕ} [Module (ZMod q) G] (g : G) (σ : Bool) (b : ZMod q)
    (u : G) : (ddhOTReceiverMsg g σ b u).1 + (ddhOTReceiverMsg g σ b u).2 = u := by
  cases σ <;> simp [ddhOTReceiverMsg]

/-- Encrypt a single branch message `m : G` under `(g, u, w)` using coins `(r, s)` and sender
exponent `a`. When `u = a • g`, this equals ElGamal encryption
`((r + a * s) • g, (r + a * s) • w + m)` under key `w`. -/
@[expose] def ddhOTEncryptBranch {q : ℕ} [Module (ZMod q) G] (g u w m : G) (r s a : ZMod q) :
    G × G :=
  (r • g + s • u, r • w + s • (a • w) + m)

/-- Decrypting an honestly encrypted branch with `w = b • g` and `u = a • g` recovers `m`. -/
theorem ddhOTReceiverOutput_encryptBranch {q : ℕ} [Module (ZMod q) G] (g m : G)
    (a b r s : ZMod q) :
    let u := a • g
    let w := b • g
    let ct := ddhOTEncryptBranch g u w m r s a
    ct.2 - b • ct.1 = m := by
  dsimp only [ddhOTEncryptBranch]
  module

/-- Algebraic identity for the chosen branch ciphertext in `ddhOTProtocol`. -/
private theorem chosen_branch_eq {q : ℕ} [Module (ZMod q) G] (g m : G) (a b r s : ZMod q) :
    ddhOTEncryptBranch g (a • g) (b • g) m r s a =
      let e := r • g + s • (a • g)
      (e, b • e + m) := by
  dsimp only [ddhOTEncryptBranch]
  exact Prod.ext rfl (by module)

/-- Algebraic identity for the unchosen branch ciphertext in `ddhOTProtocol`. -/
private theorem unchosen_branch_eq {q : ℕ} [Module (ZMod q) G] (g m : G) (a b r s : ZMod q) :
    ddhOTEncryptBranch g (a • g) (a • g - b • g) m r s a =
      let u' := (r + a * s) • g
      let w_ddh := (a * (r + a * s)) • g
      (u', w_ddh - b • u' + m) := by
  refine Prod.ext ?_ ?_ <;> dsimp only [ddhOTEncryptBranch] <;> module

/-- Round 3 sender reply in the unchecked variant: omits the `w.1 + w.2 = u` verification. -/
@[expose] def ddhOTSenderReplyUnchecked {q : ℕ} [Module (ZMod q) G] (g : G) (m : G × G)
    (c : DDHOTSenderCoins q) (w : G × G) : (G × G) × (G × G) :=
  let u := c.exponent • g
  (ddhOTEncryptBranch g u w.1 m.1 c.coinR₀ c.coinS₀ c.exponent,
    ddhOTEncryptBranch g u w.2 m.2 c.coinR₁ c.coinS₁ c.exponent)

/-- Receiver output decryption: selects ciphertext `σ` and unmasks by subtracting `b • e_σ`. -/
@[expose] def ddhOTReceiverOutput {q : ℕ} [Module (ZMod q) G] (σ : Bool) (b : ZMod q)
    (reply : (G × G) × (G × G)) : G :=
  let ct := if σ then reply.2 else reply.1
  ct.2 - b • ct.1

/-- Final local state type at the end of `ddhOTSchedule G`, parameterized by coin types `C₀, C₁`. -/
abbrev DDHOTFinalWith (G C₀ C₁ : Type) (i : Fin 2) : Type :=
  (((OTIn G i × DDHOTCoinsWith C₀ C₁ i) ×
    (Round.message (spec := noOracleSpec) 0 1 G).Received i) ×
    (Round.message (spec := noOracleSpec) 1 0 (G × G)).Received i) ×
    (Round.message (spec := noOracleSpec) 0 1 ((G × G) × (G × G))).Received i

/-- Output extraction at the end of `ddhOTSchedule G` under receiver coin projection `proj₁`. -/
@[expose] def ddhOTOutputWith {q : ℕ} [Module (ZMod q) G] {C₀ C₁ : Type} (proj₁ : C₁ → ZMod q)
    (i : Fin 2) (st : DDHOTFinalWith G C₀ C₁ i) : OTOut G i :=
  Fin.cases (motive := fun i => DDHOTFinalWith G C₀ C₁ i → OTOut G i)
    (fun _ => ())
    (fun j ((((σ, raw₁), _), _), reply) => ddhOTReceiverOutput (G := G) σ (proj₁ raw₁)
      (reply (Fin.fin_one_eq_zero j ▸ rfl)))
    i st

/-- **Unchecked three-message DDH OT protocol**: `ddhOTProtocol` without the sender's
`w₀ + w₁ = u` check. [BonehShoup2023], Section 23.5.7.3, Remark 23.6 describes the
malicious-receiver attack that the check is meant to stop; `ddhOTUncheckedRealGame` runs that
attack against this protocol. -/
@[expose] noncomputable def ddhOTUncheckedProtocol (g : G) (q : ℕ) [NeZero q]
    [Module (ZMod q) G] :
    Protocol 2 noOracleSpec (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) where
  sampleCoins i := Fin.cases (motive := fun i => ProbComp (DDHOTCoins q i))
    (sampleDDHOTSenderCoins q) (fun _ => ProbComp.uniform (ZMod q)) i
  steps :=
    .message (fun (_, c) => c.exponent • g)
      (.message (fun ((σ, b), u) => ddhOTReceiverMsg g σ b (u rfl))
        (.message (fun (((m, c), _), w) => ddhOTSenderReplyUnchecked g m c (w rfl))
          (.done (ddhOTOutputWith id))))

omit [AddCommGroup G] in
/-- The honest sender's Round 3 reply in a protocol `proto` along `ddhOTSchedule G`, on input `m`
and coins `c`, when the receiver's Round 2 message is `w`. The sender's local state is built as in
`Steps.run`; a malicious receiver may choose `w` freely. -/
@[expose] def ddhOTSenderReplyOf {q : ℕ}
    (proto : Protocol 2 noOracleSpec (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G))
    (m : G × G) (c : DDHOTSenderCoins q) (w : G × G) : (G × G) × (G × G) :=
  match proto.steps with
  | .message send₁ (.message _ (.message send₃ _)) =>
    send₃ (((m, c), fun _ => send₁ (m, c)), fun _ => w)

/-- The Round 3 reply of `ddhOTUncheckedProtocol` is `ddhOTSenderReplyUnchecked`. -/
theorem ddhOTSenderReplyOf_ddhOTUncheckedProtocol (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (m : G × G) (c : DDHOTSenderCoins q) (w : G × G) :
    ddhOTSenderReplyOf (ddhOTUncheckedProtocol g q) m c w = ddhOTSenderReplyUnchecked g m c w :=
  rfl

/-- Malicious Round 2 message `(b₀ • g, b₁ • g)` with known discrete logs `(b₀, b₁)`. -/
@[expose] def ddhOTAttackMsg {q : ℕ} [Module (ZMod q) G] (g : G) (b₀ b₁ : ZMod q) : G × G :=
  (b₀ • g, b₁ • g)

/-- Simultaneous decryption of both branches from the unchecked sender reply using `(b₀, b₁)`. -/
@[expose] def ddhOTAttackBothMessages {q : ℕ} [Module (ZMod q) G] (b₀ b₁ : ZMod q)
    (reply : (G × G) × (G × G)) : G × G :=
  let ((e₀, c₀), (e₁, c₁)) := reply
  (c₀ - b₀ • e₀, c₁ - b₁ • e₁)

/-- **Simultaneous recovery on the unchecked variant**: when the sender omits `w₀ + w₁ = u`,
a malicious receiver sending `ddhOTAttackMsg g b₀ b₁` recovers both `(m.1, m.2)` from
`ddhOTSenderReplyUnchecked`. -/
theorem ddhOTAttackBothMessages_eq {q : ℕ} [Module (ZMod q) G] (g : G) (m : G × G)
    (c₀ : DDHOTSenderCoins q) (b₀ b₁ : ZMod q) :
    ddhOTAttackBothMessages b₀ b₁
      (ddhOTSenderReplyUnchecked g m c₀ (ddhOTAttackMsg g b₀ b₁)) = m := by
  rcases m with ⟨m₀, m₁⟩
  dsimp only [ddhOTAttackBothMessages, ddhOTSenderReplyUnchecked, ddhOTAttackMsg]
  exact Prod.ext (ddhOTReceiverOutput_encryptBranch g m₀ c₀.exponent b₀ c₀.coinR₀ c₀.coinS₀)
    (ddhOTReceiverOutput_encryptBranch g m₁ c₀.exponent b₁ c₀.coinR₁ c₀.coinS₁)

variable [DecidableEq G]

/-- Round 3 sender reply in the checked protocol: verifies `w.1 + w.2 = c.exponent • g` before
encrypting `(m.1, m.2)`. -/
@[expose] def ddhOTSenderReply {q : ℕ} [Module (ZMod q) G] (g : G) (m : G × G)
    (c : DDHOTSenderCoins q) (w : G × G) : (G × G) × (G × G) :=
  let u := c.exponent • g
  if w.1 + w.2 = u then
    (ddhOTEncryptBranch g u w.1 m.1 c.coinR₀ c.coinS₀ c.exponent,
      ddhOTEncryptBranch g u w.2 m.2 c.coinR₁ c.coinS₁ c.exponent)
  else
    ((0, 0), (0, 0))

/-- When the receiver's Round 2 message satisfies `w.1 + w.2 = c.exponent • g`, the checked sender
reply `ddhOTSenderReply` coincides with `ddhOTSenderReplyUnchecked`. -/
theorem ddhOTSenderReply_eq_unchecked_of_add {q : ℕ} [Module (ZMod q) G] (g : G) (m : G × G)
    (c : DDHOTSenderCoins q) (w : G × G) (hw : w.1 + w.2 = c.exponent • g) :
    ddhOTSenderReply g m c w = ddhOTSenderReplyUnchecked g m c w := by
  simp only [ddhOTSenderReply, ddhOTSenderReplyUnchecked, hw, ↓reduceIte]

/-- When the receiver's Round 2 message violates `w.1 + w.2 = c.exponent • g`, the checked sender
reply `ddhOTSenderReply` aborts to `((0, 0), (0, 0))`. -/
theorem ddhOTSenderReply_eq_zero_of_add_ne {q : ℕ} [Module (ZMod q) G] (g : G) (m : G × G)
    (c : DDHOTSenderCoins q) (w : G × G) (hw : w.1 + w.2 ≠ c.exponent • g) :
    ddhOTSenderReply g m c w = ((0, 0), (0, 0)) := by
  simp only [ddhOTSenderReply, hw, ↓reduceIte]

/-- **Three-message DDH 1-out-of-2 Oblivious Transfer protocol with given coin samplers and
projections**: a variant of [BonehShoup2023], Section 23.5.7, Figure 23.17, with the check
`w₀ + w₁ = u` from Remark 23.6. Party `0` samples `raw₀ ← sample₀` (retained unreduced in
`PartyView.coins`) and derives `proj₀ raw₀ : DDHOTSenderCoins q`; party `1` samples
`raw₁ ← sample₁` (retained unreduced in `PartyView.coins`) and derives `b := proj₁ raw₁`. Unlike in
Figure 23.17, the sender knows the discrete logarithm `a` of its first message `u = a • g` and
encrypts each branch with its own coins `(rᵢ, sᵢ)`; the module docstring lists the differences. -/
@[expose] noncomputable def ddhOTProtocolWith (g : G) (q : ℕ) [Module (ZMod q) G]
    {C₀ C₁ : Type} (sample₀ : ProbComp C₀) (sample₁ : ProbComp C₁)
    (proj₀ : C₀ → DDHOTSenderCoins q) (proj₁ : C₁ → ZMod q) :
    Protocol 2 noOracleSpec (ddhOTSchedule G) (OTIn G) (DDHOTCoinsWith C₀ C₁) (OTOut G) where
  sampleCoins i := Fin.cases (motive := fun i => ProbComp (DDHOTCoinsWith C₀ C₁ i))
    sample₀ (fun _ => sample₁) i
  steps :=
    .message (fun (_, raw₀) => (proj₀ raw₀).exponent • g)
      (.message (fun ((σ, raw₁), u) => ddhOTReceiverMsg g σ (proj₁ raw₁) (u rfl))
        (.message (fun (((m, raw₀), _), w) => ddhOTSenderReply g m (proj₀ raw₀) (w rfl))
          (.done (ddhOTOutputWith proj₁))))

/-- **Three-message DDH 1-out-of-2 Oblivious Transfer protocol with exact uniform coins**:
`ddhOTProtocolWith` specialized to `sampleDDHOTSenderCoins q`, `ProbComp.uniform (ZMod q)`, and
identity projections. -/
noncomputable abbrev ddhOTProtocol (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G] :
    Protocol 2 noOracleSpec (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) :=
  ddhOTProtocolWith g q (sampleDDHOTSenderCoins q) (ProbComp.uniform (ZMod q)) id id

/-! ### Party views and execution characterization -/

/-- The sender's `PartyView` from its input `x₀`, coin object `raw₀`, and received Round 2 message
`w`. -/
@[expose] def ddhOTSenderViewWith {C₀ C₁ : Type} (x₀ : G × G) (raw₀ : C₀) (w : G × G) :
    PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) 0 where
  input := x₀
  coins := raw₀
  received := (fun h => absurd h (by decide), (fun _ => w, (fun h => absurd h (by decide), ())))

/-- The sender's `PartyView` for `ZMod q` coins. -/
abbrev ddhOTSenderView {q : ℕ} (x₀ : G × G) (c₀ : DDHOTSenderCoins q) (w : G × G) :
    PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) 0 :=
  ddhOTSenderViewWith x₀ c₀ w

/-- The receiver's `PartyView` from its input `σ`, coin object `raw₁`, Round 1 message `u`, and
Round 3 reply `reply`. -/
@[expose] def ddhOTReceiverViewWith {C₀ C₁ : Type} (σ : Bool) (raw₁ : C₁) (u : G)
    (reply : (G × G) × (G × G)) :
    PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) 1 where
  input := σ
  coins := raw₁
  received := (fun _ => u, (fun h => absurd h (by decide), (fun _ => reply, ())))

/-- The receiver's `PartyView` for `ZMod q` coins. -/
abbrev ddhOTReceiverView {q : ℕ} (σ : Bool) (b : ZMod q) (u : G)
    (reply : (G × G) × (G × G)) :
    PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) 1 :=
  ddhOTReceiverViewWith σ b u reply

/-- The pair of party views produced by `ddhOTProtocolWith` on inputs `x`, sender coins `raw₀`, and
receiver coin `raw₁`. Because `ddhOTReceiverMsg` always satisfies the sender's check `w₀ + w₁ = u`,
the sender's reply equals `ddhOTSenderReplyUnchecked`. -/
@[expose] def ddhOTViewsWith {q : ℕ} [Module (ZMod q) G] {C₀ C₁ : Type} (g : G)
    (proj₀ : C₀ → DDHOTSenderCoins q) (proj₁ : C₁ → ZMod q) (x : (i : Fin 2) → OTIn G i)
    (raw₀ : C₀) (raw₁ : C₁) :
    (i : Fin 2) → PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) i :=
  let c₀ := proj₀ raw₀
  let b := proj₁ raw₁
  let u := c₀.exponent • g
  let w := ddhOTReceiverMsg g (x 1) b u
  fun i => Fin.cases
    (motive := fun i => PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) i)
    (ddhOTSenderViewWith (x 0) raw₀ w)
    (Fin.cases
      (motive := fun j => PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) j.succ)
      (ddhOTReceiverViewWith (x 1) raw₁ u (ddhOTSenderReplyUnchecked g (x 0) c₀ w))
      fun k => k.elim0) i

/-- The pair of party views for `ZMod q` coins. -/
abbrev ddhOTViews {q : ℕ} [Module (ZMod q) G] (g : G) (x : (i : Fin 2) → OTIn G i)
    (c₀ : DDHOTSenderCoins q) (b : ZMod q) :
    (i : Fin 2) → PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i :=
  ddhOTViewsWith g id id x c₀ b

/-- Received transcript tuple in a run of `ddhOTProtocolWith` from initial local states `st`. -/
private def ddhOTReceivedWith {q : ℕ} [Module (ZMod q) G] {C₀ C₁ : Type} (g : G)
    (proj₀ : C₀ → DDHOTSenderCoins q) (proj₁ : C₁ → ZMod q)
    (st : (i : Fin 2) → OTIn G i × DDHOTCoinsWith C₀ C₁ i) (i : Fin 2) :
    (ddhOTSchedule G).Received i :=
  let (m, raw₀) := st 0
  let (σ, raw₁) := st 1
  let c₀ := proj₀ raw₀
  let u := c₀.exponent • g
  let w := ddhOTReceiverMsg g σ (proj₁ raw₁) u
  let reply := ddhOTSenderReply g m c₀ w
  (Round.deliverMessage u i, (Round.deliverMessage w i, (Round.deliverMessage reply i, ())))

/-- The steps of `ddhOTProtocolWith` are deterministic once the coins are fixed. -/
private theorem evalWith_ddhOTSteps (g : G) (q : ℕ) [Module (ZMod q) G]
    {C₀ C₁ : Type} (sample₀ : ProbComp C₀) (sample₁ : ProbComp C₁)
    (proj₀ : C₀ → DDHOTSenderCoins q) (proj₁ : C₁ → ZMod q)
    (st : (i : Fin 2) → OTIn G i × DDHOTCoinsWith C₀ C₁ i) :
    (ddhOTProtocolWith g q sample₀ sample₁ proj₀ proj₁).steps.evalWith noOracleWorld st =
      PMF.pure (ddhOTReceivedWith g proj₀ proj₁ st) := by
  dsimp only [ddhOTProtocolWith]
  simp only [Steps.evalWith_message, Steps.evalWith_done, PMF.pure_map]
  rfl

/-- Independent coin sampling draws the sender's and receiver's coins. -/
private theorem eval_pi_ddhOTSampleCoins (g : G) (q : ℕ) [Module (ZMod q) G]
    {C₀ C₁ : Type} (sample₀ : ProbComp C₀) (sample₁ : ProbComp C₁)
    (proj₀ : C₀ → DDHOTSenderCoins q) (proj₁ : C₁ → ZMod q) :
    ProbComp.eval
        (OracleComp.pi (ddhOTProtocolWith g q sample₀ sample₁ proj₀ proj₁).sampleCoins) =
      (ProbComp.eval sample₀).bind fun raw₀ =>
        (ProbComp.eval sample₁).map fun raw₁ => ddhOTCoinsWith raw₀ raw₁ := by
  simp only [ddhOTProtocolWith, OracleComp.pi_succ, OracleComp.pi_zero, pmf_norm]
  refine congrArg (PMF.bind _) (funext fun raw₀ => congrArg (PMF.bind _) (funext fun raw₁ =>
    congrArg PMF.pure (funext (β := DDHOTCoinsWith C₀ C₁) fun i => ?_)))
  fin_cases i <;> rfl

/-- Receiver's view in a run with coins `(raw₀, raw₁)`. -/
private theorem ddhOTReceivedWith_one {q : ℕ} [Module (ZMod q) G] {C₀ C₁ : Type} (g : G)
    (proj₀ : C₀ → DDHOTSenderCoins q) (proj₁ : C₁ → ZMod q)
    (x : (i : Fin 2) → OTIn G i) (raw₀ : C₀) (raw₁ : C₁) :
    (⟨x 1, ddhOTCoinsWith raw₀ raw₁ 1,
      ddhOTReceivedWith g proj₀ proj₁ (fun i => (x i, ddhOTCoinsWith raw₀ raw₁ i)) 1⟩ :
        PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) 1) =
      let u := (proj₀ raw₀).exponent • g
      let w := ddhOTReceiverMsg g (x 1) (proj₁ raw₁) u
      ddhOTReceiverViewWith (x 1) raw₁ u (ddhOTSenderReply g (x 0) (proj₀ raw₀) w) := by
  refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Round.received_message_ext fun _ => rfl
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · exact Round.received_message_ext fun _ => rfl

/-- Sender's view in a run with coins `(raw₀, raw₁)`. -/
private theorem ddhOTReceivedWith_zero {q : ℕ} [Module (ZMod q) G] {C₀ C₁ : Type} (g : G)
    (proj₀ : C₀ → DDHOTSenderCoins q) (proj₁ : C₁ → ZMod q)
    (x : (i : Fin 2) → OTIn G i) (raw₀ : C₀) (raw₁ : C₁) :
    (⟨x 0, ddhOTCoinsWith raw₀ raw₁ 0,
      ddhOTReceivedWith g proj₀ proj₁ (fun i => (x i, ddhOTCoinsWith raw₀ raw₁ i)) 0⟩ :
        PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) 0) =
      ddhOTSenderViewWith (x 0) raw₀
        (ddhOTReceiverMsg g (x 1) (proj₁ raw₁) ((proj₀ raw₀).exponent • g)) := by
  refine PartyView.ext rfl rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · exact Round.received_message_ext fun _ => rfl
  · exact Round.received_message_eq_of_ne (by decide) _ _

/-! ### Execution law and correctness -/

/-- In a run with coins `(raw₀, raw₁)`, the receiver outputs `otOutputs x 1`. -/
private theorem outputOfView_ddhOT_one (g : G) (q : ℕ) [Module (ZMod q) G]
    {C₀ C₁ : Type} (sample₀ : ProbComp C₀) (sample₁ : ProbComp C₁)
    (proj₀ : C₀ → DDHOTSenderCoins q) (proj₁ : C₁ → ZMod q)
    (x : (i : Fin 2) → OTIn G i) (raw₀ : C₀) (raw₁ : C₁) :
    (ddhOTProtocolWith g q sample₀ sample₁ proj₀ proj₁).outputOfView 1
        ⟨x 1, ddhOTCoinsWith raw₀ raw₁ 1,
          ddhOTReceivedWith g proj₀ proj₁ (fun i => (x i, ddhOTCoinsWith raw₀ raw₁ i)) 1⟩ =
      otOutputs x 1 := by
  let c := proj₀ raw₀
  let σ : Bool := x 1
  change ddhOTReceiverOutput σ (proj₁ raw₁)
    (ddhOTSenderReply g (x 0) c (ddhOTReceiverMsg g σ (proj₁ raw₁) (c.exponent • g))) =
    if σ then (x 0).2 else (x 0).1
  simp only [ddhOTSenderReply, ddhOTReceiverMsg_add, ↓reduceIte, ddhOTReceiverOutput]
  cases σ <;> simp only [Bool.false_eq_true, ↓reduceIte, ddhOTReceiverMsg]
  · exact ddhOTReceiverOutput_encryptBranch g (x 0).1 c.exponent (proj₁ raw₁) c.coinR₀ c.coinS₀
  · exact ddhOTReceiverOutput_encryptBranch g (x 0).2 c.exponent (proj₁ raw₁) c.coinR₁ c.coinS₁

/-- **Execution law of `ddhOTProtocolWith`**: for any party coin samplers `sample₀, sample₁` and
projections `proj₀, proj₁`, `evalWith` draws `raw₀ ← sample₀` and `raw₁ ← sample₁` and returns
`(ddhOTViewsWith g proj₀ proj₁ x raw₀ raw₁, otOutputs x)`. -/
theorem evalWith_ddhOTProtocolWith (g : G) (q : ℕ) [Module (ZMod q) G]
    {C₀ C₁ : Type} (sample₀ : ProbComp C₀) (sample₁ : ProbComp C₁)
    (proj₀ : C₀ → DDHOTSenderCoins q) (proj₁ : C₁ → ZMod q)
    (x : (i : Fin 2) → OTIn G i) :
    (ddhOTProtocolWith g q sample₀ sample₁ proj₀ proj₁).evalWith noOracleWorld x = do
      let raw₀ ← ProbComp.eval sample₀
      let raw₁ ← ProbComp.eval sample₁
      return (ddhOTViewsWith g proj₀ proj₁ x raw₀ raw₁, otOutputs x) := by
  rw [Protocol.evalWith_eq, eval_pi_ddhOTSampleCoins]
  simp only [evalWith_ddhOTSteps, pmf_norm]
  refine congrArg (ProbComp.eval sample₀).bind (funext fun raw₀ => ?_)
  refine congrArg (ProbComp.eval sample₁).bind
    (funext fun raw₁ => congrArg PMF.pure (Prod.ext ?_ ?_))
  · funext i
    fin_cases i
    · exact ddhOTReceivedWith_zero g proj₀ proj₁ x raw₀ raw₁
    · refine (ddhOTReceivedWith_one g proj₀ proj₁ x raw₀ raw₁).trans ?_
      simp only [ddhOTViewsWith,
        ddhOTSenderReply_eq_unchecked_of_add g (x 0) (proj₀ raw₀) _
          (ddhOTReceiverMsg_add g (x 1) (proj₁ raw₁) _)]
      rfl
  · funext i
    fin_cases i
    · rfl
    · exact outputOfView_ddhOT_one g q sample₀ sample₁ proj₀ proj₁ x raw₀ raw₁

/-- **Correctness**: for any party coin samplers and exponent projections, in every execution of
`ddhOTProtocolWith`, the sender outputs `()` and the receiver outputs
`if x 1 then (x 0).2 else (x 0).1`. -/
theorem ddhOTProtocolWith_output_of_mem_support (g : G) (q : ℕ) [Module (ZMod q) G]
    {C₀ C₁ : Type} {sample₀ : ProbComp C₀} {sample₁ : ProbComp C₁}
    {proj₀ : C₀ → DDHOTSenderCoins q} {proj₁ : C₁ → ZMod q}
    (x : (i : Fin 2) → OTIn G i)
    {r : ((i : Fin 2) → PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i)}
    (hr : r ∈
      ((ddhOTProtocolWith g q sample₀ sample₁ proj₀ proj₁).evalWith noOracleWorld x).support) :
    r.2 = otOutputs x := by
  supp_cases hr [evalWith_ddhOTProtocolWith]
  rfl

/-! ### Perfect privacy against a corrupted sender -/

/-- The simulated view of a corrupted sender (`{0}`) on sender coin object `raw₀` (projected via
`proj₀`) and receiver exponent `b : ZMod q`: the sender's input and unreduced coin `raw₀`, and the
Round 2 message `(b • g, (proj₀ raw₀).exponent • g - b • g)`. -/
@[expose] def ddhOTSenderSimWithCoinsOf {q : ℕ} [Module (ZMod q) G] {C₀ C₁ : Type} (g : G)
    (proj₀ : C₀ → DDHOTSenderCoins q) (raw₀ : C₀) (b : ZMod q)
    (xI : (i : ({0} : Finset (Fin 2))) → OTIn G i) :
    (i : ({0} : Finset (Fin 2))) →
      PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) i :=
  let u := (proj₀ raw₀).exponent • g
  let v := b • g
  singletonView (ddhOTSenderViewWith (xI ⟨0, Finset.mem_singleton_self 0⟩) raw₀ (v, u - v))

/-- The simulated view of a corrupted sender (`{0}`) for `ZMod q` coins. -/
abbrev ddhOTSenderSimWithCoins {q : ℕ} [Module (ZMod q) G] (g : G)
    (c₀ : DDHOTSenderCoins q) (b : ZMod q) (xI : (i : ({0} : Finset (Fin 2))) → OTIn G i) :
    (i : ({0} : Finset (Fin 2))) → PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i :=
  ddhOTSenderSimWithCoinsOf g id c₀ b xI

/-- Simulator for a corrupted sender (`{0}`): samples fresh sender coins `c₀` and a uniform
`b : ZMod q`, and returns `ddhOTSenderSimWithCoins`, whose Round 2 message is
`(b • g, c₀.exponent • g - b • g)`. -/
@[expose] noncomputable def ddhOTSenderSim (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G] :
    CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) {0} :=
  fun xI _ => do
    let c₀ ← sampleDDHOTSenderCoins q
    let b ← ProbComp.uniform (ZMod q)
    return ddhOTSenderSimWithCoins g c₀ b xI

omit [DecidableEq G] in
/-- **Perfect sender simulation under any sender coin sampler** when the honest receiver's
exponent is uniform on `ZMod q`: for every `sample₀` and `proj₀`, drawing `raw₀ ← sample₀` and
`b ← uniform (ZMod q)` gives `ddhOTSenderSimWithCoinsOf` the exact same distribution as the
corrupted sender's real view paired with `otOutputs x`. -/
theorem idealJoint_ddhOT_sender_with (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    {C₀ C₁ : Type} (sample₀ : ProbComp C₀) (proj₀ : C₀ → DDHOTSenderCoins q)
    (x : (i : Fin 2) → OTIn G i) :
    (do
      let raw₀ ← ProbComp.eval sample₀
      let b ← PMF.uniformOfFintype (ZMod q)
      return (ddhOTSenderSimWithCoinsOf (C₁ := C₁) g proj₀ raw₀ b (Finset.restrict {0} x),
        otOutputs x)) =
    (do
      let raw₀ ← ProbComp.eval sample₀
      let b ← PMF.uniformOfFintype (ZMod q)
      return (singletonView (ddhOTSenderViewWith (C₁ := C₁) (x 0) raw₀
        (ddhOTReceiverMsg g (x 1) b ((proj₀ raw₀).exponent • g))), otOutputs x)) := by
  simp only [pmf_norm]
  refine congrArg (PMF.bind _) (funext fun raw₀ => ?_)
  let σ : Bool := x 1
  change (PMF.uniformOfFintype (ZMod q)).bind (fun b =>
      PMF.pure (singletonView (ddhOTSenderViewWith (C₁ := C₁) (x 0) raw₀
        (b • g, (proj₀ raw₀).exponent • g - b • g)), otOutputs x)) =
    (PMF.uniformOfFintype (ZMod q)).bind (fun b =>
      PMF.pure (singletonView (ddhOTSenderViewWith (C₁ := C₁) (x 0) raw₀
        (ddhOTReceiverMsg g σ b ((proj₀ raw₀).exponent • g))), otOutputs x))
  cases σ
  · rfl
  · conv_lhs => rw [← PMF.uniformOfFintype_map_sub_left (proj₀ raw₀).exponent, PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun b => ?_)
    simp only [Function.comp_apply, ddhOTReceiverMsg, ↓reduceIte,
      sub_smul, sub_sub_cancel]

/-- Real joint distribution for a corrupted sender (`{0}`). -/
theorem realJoint_ddhOT_sender (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i) :
    (ddhOTProtocol g q).realJoint noOracleWorld {0} x = do
      let c₀ ← ProbComp.eval (sampleDDHOTSenderCoins q)
      let b ← PMF.uniformOfFintype (ZMod q)
      return (singletonView
        (ddhOTSenderView (x 0) c₀ (ddhOTReceiverMsg g (x 1) b (c₀.exponent • g))),
        otOutputs x) := by
  rw [Protocol.realJoint, evalWith_ddhOTProtocolWith]
  simp only [pmf_norm, ProbComp.eval_uniform]
  refine congrArg (PMF.bind _) (funext fun c₀ =>
    congrArg (PMF.bind _) (funext fun b => congrArg PMF.pure ?_))
  simp only [Prod.map, id, restrict_singleton, ddhOTViewsWith]
  rfl

/-- **Perfect privacy against a corrupted sender**: the ideal joint distribution with
`ddhOTSenderSim` equals the real joint distribution. -/
theorem idealJoint_ddhOT_sender (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i) :
    ProbComp.eval (idealJoint (otFunctionality G) {0} (ddhOTSenderSim g q) x) =
      (ddhOTProtocol g q).realJoint noOracleWorld {0} x := by
  rw [realJoint_ddhOT_sender]
  simp only [idealJoint, otFunctionality, Functionality.ofDeterministic, ddhOTSenderSim,
    pmf_norm, ProbComp.eval_uniform]
  simpa only [pmf_norm, id] using
    idealJoint_ddhOT_sender_with (C₁ := ZMod q) g q (sampleDDHOTSenderCoins q) id x

/-- A corrupted sender has advantage zero against every distinguisher. -/
theorem semiHonestAdvantage_ddhOT_sender (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({0} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool) :
    semiHonestAdvantage (ddhOTProtocol g q) noOracleWorld (otFunctionality G) {0}
      (ddhOTSenderSim g q) x D = 0 :=
  (semiHonestAdvantage_eq_zero_iff _ _ _ _ _ x).mpr (idealJoint_ddhOT_sender g q x) D

/-! ### Computational privacy against a corrupted receiver under DDH -/

/-- The DDH reduction for receiver privacy on a fixed receiver coin object `raw₁` (projected via
`proj₁`) and chosen-branch coins `(r, s)`: embeds `(u, u', w_ddh)` into the unchosen branch,
encrypts the chosen branch with `b := proj₁ raw₁`, records `raw₁` unreduced in the receiver's
`PartyView.coins`, and runs `D`. -/
@[expose] def ddhOTReductionWithCoinsOf {q : ℕ} [Module (ZMod q) G] {C₀ C₁ : Type} (g : G)
    (proj₁ : C₁ → ZMod q) (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool)
    (raw₁ : C₁) (r s : ZMod q) (u u' w_ddh : G) : ProbComp Bool :=
  let b := proj₁ raw₁
  let σ : Bool := x 1
  let e_σ := r • g + s • u
  let m_σ := if σ then (x 0).2 else (x 0).1
  let m_other := if σ then (x 0).1 else (x 0).2
  let c_σ := b • e_σ + m_σ
  let c_other := w_ddh - b • u' + m_other
  let reply := if σ then ((u', c_other), (e_σ, c_σ)) else ((e_σ, c_σ), (u', c_other))
  D (singletonView (ddhOTReceiverViewWith σ raw₁ u reply), otOutputs x)

/-- The DDH reduction for receiver privacy on fixed `ZMod q` coins. -/
abbrev ddhOTReductionWithCoins {q : ℕ} [Module (ZMod q) G] (g : G)
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool)
    (b r s : ZMod q) (u u' w_ddh : G) : ProbComp Bool :=
  ddhOTReductionWithCoinsOf g id x D b r s u u' w_ddh

/-- DDH reduction for receiver privacy under receiver coin sampler `sample₁` and projection
`proj₁`: draws `raw₁ ← sample₁` and uniform `r, s : ZMod q`, then runs
`ddhOTReductionWithCoinsOf`. -/
@[expose] noncomputable def ddhOTReductionOf (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    {C₀ C₁ : Type} (sample₁ : ProbComp C₁) (proj₁ : C₁ → ZMod q)
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool)
    (u u' w_ddh : G) : ProbComp Bool := do
  let raw₁ ← sample₁
  let r ← ProbComp.uniform (ZMod q)
  let s ← ProbComp.uniform (ZMod q)
  ddhOTReductionWithCoinsOf g proj₁ x D raw₁ r s u u' w_ddh

/-- DDH reduction for receiver privacy with uniform `ZMod q` coins. -/
noncomputable abbrev ddhOTReduction (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool)
    (u u' w_ddh : G) : ProbComp Bool :=
  ddhOTReductionOf g q (ProbComp.uniform (ZMod q)) id x D u u' w_ddh

/-- For independent uniform `r, s : ZMod q`, `r + a * s` is uniform on `ZMod q`. -/
private theorem uniform_bind_add_mul {q : ℕ} [NeZero q] {α : Type} (a : ZMod q)
    (f : ZMod q → PMF α) :
    ((PMF.uniformOfFintype (ZMod q)).bind fun r =>
      (PMF.uniformOfFintype (ZMod q)).bind fun s => f (r + a * s)) =
      (PMF.uniformOfFintype (ZMod q)).bind f := by
  rw [PMF.bind_comm]
  simp only [PMF.uniformOfFintype_bind_add_right, PMF.bind_const]

/-- Collapsing the unchosen branch's two uniform exponents `(r', s')` into a single uniform
exponent `k = r' + a * s'` and reordering `(raw₁, r, s, k)` to `(k, raw₁, r, s)` for any receiver
coin law `p₁`. -/
private theorem uniform_bind_branch {q : ℕ} [NeZero q] {C₁ α : Type} (p₁ : PMF C₁)
    (a : ZMod q) (σ : Bool) (f : C₁ → ZMod q → ZMod q → ZMod q → PMF α) :
    (do
      let r₀ ← PMF.uniformOfFintype (ZMod q)
      let s₀ ← PMF.uniformOfFintype (ZMod q)
      let r₁ ← PMF.uniformOfFintype (ZMod q)
      let s₁ ← PMF.uniformOfFintype (ZMod q)
      let raw₁ ← p₁
      if σ then f raw₁ r₁ s₁ (r₀ + a * s₀) else f raw₁ r₀ s₀ (r₁ + a * s₁)) =
    (do
      let k ← PMF.uniformOfFintype (ZMod q)
      let raw₁ ← p₁
      let r ← PMF.uniformOfFintype (ZMod q)
      let s ← PMF.uniformOfFintype (ZMod q)
      f raw₁ r s k) := by
  simp only [PMF.monad_bind_eq_bind]
  cases σ <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · conv_lhs =>
      enter [2, r₀, 2, s₀]
      rw [uniform_bind_add_mul a fun k => p₁.bind fun raw₁ => f raw₁ r₀ s₀ k]
    pmf_swap
  · conv_lhs =>
      rw [uniform_bind_add_mul a fun k =>
        (PMF.uniformOfFintype (ZMod q)).bind fun r₁ =>
          (PMF.uniformOfFintype (ZMod q)).bind fun s₁ =>
            p₁.bind fun raw₁ => f raw₁ r₁ s₁ k]
    pmf_swap

omit [DecidableEq G] in
/-- For any receiver coin sampler `sample₁` and projection `proj₁`, when the honest sender's five
exponents are drawn uniformly via `sampleDDHOTSenderCoins q`, the corrupted receiver's real view
distribution equals `ddhRealExperiment q g` run on `ddhOTReductionOf`. -/
theorem real_receiver_eq_ddhRealExperiment_of (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    {C₀ C₁ : Type} (sample₁ : ProbComp C₁) (proj₁ : C₁ → ZMod q)
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool) :
    (do
      let c₀ ← ProbComp.eval (sampleDDHOTSenderCoins q)
      let raw₁ ← ProbComp.eval sample₁
      ProbComp.eval (D (singletonView (ddhOTReceiverViewWith (x 1) raw₁ (c₀.exponent • g)
        (ddhOTSenderReplyUnchecked g (x 0) c₀
          (ddhOTReceiverMsg g (x 1) (proj₁ raw₁) (c₀.exponent • g)))), otOutputs x))) =
      ProbComp.eval (ddhRealExperiment q g (ddhOTReductionOf g q sample₁ proj₁ x D)) := by
  simp only [pmf_norm, sampleDDHOTSenderCoins, ddhRealExperiment, ddhOTReductionOf,
    ProbComp.eval_uniform]
  congr 1 with a : 1
  refine Eq.trans ?_ (uniform_bind_branch (ProbComp.eval sample₁) a (x 1) fun raw₁ r s k =>
    ProbComp.eval (ddhOTReductionWithCoinsOf g proj₁ x D raw₁ r s (a • g) (k • g) ((a * k) • g)))
  cases hσ : x 1 <;> simp only [PMF.monad_bind_eq_bind, ddhOTReductionWithCoinsOf, hσ,
    ddhOTReceiverMsg, ddhOTSenderReplyUnchecked, Bool.false_eq_true, ↓reduceIte, chosen_branch_eq,
    unchosen_branch_eq]

/-- The real execution for a corrupted receiver is the real DDH world
`Cslib.Crypto.ddhRealExperiment q g` run on `ddhOTReduction`. -/
theorem real_receiver_eq_ddhRealExperiment (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool) :
    ((ddhOTProtocol g q).realJoint noOracleWorld {1} x).bind (fun r => ProbComp.eval (D r)) =
      ProbComp.eval (ddhRealExperiment q g (ddhOTReduction g q x D)) := by
  rw [Protocol.realJoint, evalWith_ddhOTProtocolWith]
  simp only [pmf_norm, Prod.map, id, restrict_singleton]
  exact real_receiver_eq_ddhRealExperiment_of (C₀ := DDHOTSenderCoins q) g q
    (ProbComp.uniform (ZMod q)) id x D

/-- The simulated view of a corrupted receiver (`{1}`) on receiver coin object `raw₁` (projected
via `proj₁`) and exponents `a, r, s, k, c`: given choice bit `σ` and ideal output `m_σ`, records
`raw₁` unreduced in `PartyView.coins`, sets `u = a • g`, encrypts the chosen branch as
`(e_σ, (proj₁ raw₁) • e_σ + m_σ)` with `e_σ = r • g + s • u`, and sets the unchosen branch to
`(k • g, c • g)`. -/
@[expose] def ddhOTReceiverSimWithCoinsOf {q : ℕ} [Module (ZMod q) G] {C₀ C₁ : Type} (g : G)
    (proj₁ : C₁ → ZMod q) (a : ZMod q) (raw₁ : C₁) (r s k c : ZMod q)
    (xI : (i : ({1} : Finset (Fin 2))) → OTIn G i)
    (yI : (i : ({1} : Finset (Fin 2))) → OTOut G i) :
    (i : ({1} : Finset (Fin 2))) →
      PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) i :=
  let b := proj₁ raw₁
  let σ : Bool := xI ⟨1, Finset.mem_singleton_self 1⟩
  let m_σ : G := yI ⟨1, Finset.mem_singleton_self 1⟩
  let u' := k • g
  let w' := c • g
  let u := a • g
  let e_σ := r • g + s • u
  let c_σ := b • e_σ + m_σ
  let reply := if σ then ((u', w'), (e_σ, c_σ)) else ((e_σ, c_σ), (u', w'))
  singletonView (ddhOTReceiverViewWith σ raw₁ u reply)

/-- The simulated view of a corrupted receiver (`{1}`) for `ZMod q` coins. -/
abbrev ddhOTReceiverSimWithCoins {q : ℕ} [Module (ZMod q) G] (g : G) (a b r s k c : ZMod q)
    (xI : (i : ({1} : Finset (Fin 2))) → OTIn G i)
    (yI : (i : ({1} : Finset (Fin 2))) → OTOut G i) :
    (i : ({1} : Finset (Fin 2))) → PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i :=
  ddhOTReceiverSimWithCoinsOf g id a b r s k c xI yI

/-- Simulator for a corrupted receiver (`{1}`) under receiver coin sampler `sample₁` and
projection `proj₁`: draws `raw₁ ← sample₁` and uniform `a, r, s, k, c : ZMod q`, and returns
`ddhOTReceiverSimWithCoinsOf`. -/
@[expose] noncomputable def ddhOTReceiverSimOf (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    {C₀ C₁ : Type} (sample₁ : ProbComp C₁) (proj₁ : C₁ → ZMod q) :
    CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoinsWith C₀ C₁) (OTOut G) {1} :=
  fun xI yI => do
    let a ← ProbComp.uniform (ZMod q)
    let raw₁ ← sample₁
    let r ← ProbComp.uniform (ZMod q)
    let s ← ProbComp.uniform (ZMod q)
    let k ← ProbComp.uniform (ZMod q)
    let c ← ProbComp.uniform (ZMod q)
    return ddhOTReceiverSimWithCoinsOf g proj₁ a raw₁ r s k c xI yI

/-- Simulator for a corrupted receiver (`{1}`) with uniform `ZMod q` coins. -/
noncomputable abbrev ddhOTReceiverSim (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G] :
    CoalitionSimulator (ddhOTSchedule G) (OTIn G) (DDHOTCoins q) (OTOut G) {1} :=
  ddhOTReceiverSimOf g q (ProbComp.uniform (ZMod q)) id

/-- Moving two outer binds over `p` inside `p₁` and two inner binds over `p`. -/
private theorem bind_two_three_comm {C₁ α β : Type} (p : PMF α) (p₁ : PMF C₁)
    (f : α → α → C₁ → α → α → PMF β) :
    p.bind (fun x₁ => p.bind (fun x₂ => p₁.bind (fun y₁ => p.bind (fun y₂ => p.bind (fun y₃ =>
      f x₁ x₂ y₁ y₂ y₃))))) =
    p₁.bind (fun y₁ => p.bind (fun y₂ => p.bind (fun y₃ => p.bind (fun x₁ => p.bind (fun x₂ =>
      f x₁ x₂ y₁ y₂ y₃))))) := by
  pmf_swap

omit [DecidableEq G] in
/-- For any receiver coin sampler `sample₁` and projection `proj₁`, when `g` generates `G`, the
ideal execution for a corrupted receiver with `ddhOTReceiverSimOf` equals `ddhRandomExperiment q g`
run on `ddhOTReductionOf`. -/
theorem ideal_receiver_eq_ddhRandomExperiment_of (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (hgen : ∀ y : G, ∃ k : ZMod q, k • g = y)
    {C₀ C₁ : Type} (sample₁ : ProbComp C₁) (proj₁ : C₁ → ZMod q)
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoinsWith C₀ C₁) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool) :
    ProbComp.eval (idealJoint (otFunctionality G) {1}
        (ddhOTReceiverSimOf g q sample₁ proj₁) x >>= D) =
      ProbComp.eval (ddhRandomExperiment q g (ddhOTReductionOf g q sample₁ proj₁ x D)) := by
  simp only [idealJoint, otFunctionality, Functionality.ofDeterministic, ddhOTReceiverSimOf,
    ddhOTReceiverSimWithCoinsOf, ddhRandomExperiment, ddhOTReductionOf,
    ddhOTReductionWithCoinsOf, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.pure_bind, PMF.bind_bind]
  refine congrArg (PMF.bind _) (funext fun a => ?_)
  conv_rhs => rw [bind_two_three_comm]
  refine congrArg (PMF.bind _) (funext fun raw₁ =>
    congrArg (PMF.bind _) (funext fun r =>
      congrArg (PMF.bind _) (funext fun s =>
        congrArg (PMF.bind _) (funext fun k => ?_))))
  have hshift : ∀ (c : ZMod q) (m : G),
      c • g - (proj₁ raw₁) • k • g + m = c • g + (m - (proj₁ raw₁) • k • g) :=
    fun c m => by abel
  simp_rw [hshift]
  let σ : Bool := x 1
  let e_σ := r • g + s • (a • g)
  let c_σ := (proj₁ raw₁) • e_σ + if σ then (x 0).2 else (x 0).1
  exact (uniformOfFintype_bind_smul_add hgen
    ((if σ then (x 0).1 else (x 0).2) - (proj₁ raw₁) • k • g)
    fun w => ProbComp.eval (D (singletonView (ddhOTReceiverViewWith σ raw₁ (a • g)
      (if σ then ((k • g, w), (e_σ, c_σ)) else ((e_σ, c_σ), (k • g, w)))), otOutputs x))).symm

omit [DecidableEq G] in
/-- When `g` generates `G`, the ideal execution for a corrupted receiver is the random DDH world
`Cslib.Crypto.ddhRandomExperiment q g` run on `ddhOTReduction`. -/
theorem ideal_receiver_eq_ddhRandomExperiment (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (hgen : ∀ y : G, ∃ k : ZMod q, k • g = y)
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool) :
    ProbComp.eval (idealJoint (otFunctionality G) {1} (ddhOTReceiverSim g q) x >>= D) =
      ProbComp.eval (ddhRandomExperiment q g (ddhOTReduction g q x D)) :=
  ideal_receiver_eq_ddhRandomExperiment_of (C₀ := DDHOTSenderCoins q) g q hgen
    (ProbComp.uniform (ZMod q)) id x D

/-- **Privacy against a corrupted receiver, as a per-instance equality**: for a fixed group, input
and distinguisher, the distinguisher's advantage between the ideal joint distribution with
`ddhOTReceiverSim` and the real one equals the fixed-group DDH advantage of `ddhOTReduction`, when
`g` generates `G`. This is not a computational privacy theorem: there is no security parameter,
and `ddhOTReduction` has no efficiency certificate.
`Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTReceiverGame_le` in
`CslibFrontier/Crypto/Protocols/MPC/DDHOT/Family.lean` is the family form, with a certified
reduction. -/
theorem semiHonestAdvantage_ddhOT_receiver_eq (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (hgen : ∀ y : G, ∃ k : ZMod q, k • g = y)
    (x : (i : Fin 2) → OTIn G i)
    (D : ((i : ({1} : Finset (Fin 2))) →
        PartyView (OTIn G) (DDHOTCoins q) (ddhOTSchedule G) i) ×
      ((i : Fin 2) → OTOut G i) → ProbComp Bool) :
    semiHonestAdvantage (ddhOTProtocol g q) noOracleWorld (otFunctionality G) {1}
        (ddhOTReceiverSim g q) x D =
      ddhAdvantage q g (ddhOTReduction g q x D) := by
  rw [semiHonestAdvantage, ideal_receiver_eq_ddhRandomExperiment g q hgen,
    real_receiver_eq_ddhRealExperiment g q, Game.advantage_comm, ddhAdvantage]

/-! ### Malicious-receiver attack on the unchecked variant -/

variable [Fintype G]

/-- Real game for a malicious receiver against `ddhOTUncheckedProtocol`. The sender holds uniform
messages `(m₀, m₁) ← G × G` and coins drawn by the protocol's own sampler. The receiver sends
`ddhOTAttackMsg g b₀ b₁` in Round 2, gets the sender's Round 3 reply
`ddhOTSenderReplyOf (ddhOTUncheckedProtocol g q)`, and wins if it recovers both messages. -/
noncomputable def ddhOTUncheckedRealGame (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (b₀ b₁ : ZMod q) : ProbComp Bool := do
  let m₀ ← ProbComp.uniform G
  let m₁ ← ProbComp.uniform G
  let c : DDHOTSenderCoins q ← (ddhOTUncheckedProtocol g q).sampleCoins 0
  let reply :=
    ddhOTSenderReplyOf (ddhOTUncheckedProtocol g q) (m₀, m₁) c (ddhOTAttackMsg g b₀ b₁)
  return decide (ddhOTAttackBothMessages b₀ b₁ reply = (m₀, m₁))

/-- Ideal game for a malicious receiver against oblivious transfer. The simulator `S` first outputs
a query bit `τ` together with a guessing function, which may share the simulator's randomness. For
uniform messages `(m₀, m₁) ← G × G` the ideal functionality gives it `if τ then m₁ else m₀`, and
the simulator wins if its guess equals `(m₀, m₁)`. -/
noncomputable def ddhOTUncheckedIdealGame
    (S : ProbComp (Bool × (G → ProbComp (G × G)))) : ProbComp Bool := do
  let s ← S
  let m₀ ← ProbComp.uniform G
  let m₁ ← ProbComp.uniform G
  let pair ← s.2 (if s.1 then m₁ else m₀)
  return decide (pair = (m₀, m₁))

/-- In `ddhOTUncheckedRealGame`, the malicious receiver recovers both messages with
probability `1`. -/
theorem succProbability_ddhOTUncheckedRealGame (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (b₀ b₁ : ZMod q) :
    (Game.succProbability (ProbComp.eval (ddhOTUncheckedRealGame g q b₀ b₁)) : ℝ) = 1 := by
  have hcoins : (ddhOTUncheckedProtocol g q).sampleCoins 0 = sampleDDHOTSenderCoins q := rfl
  rw [Game.coe_succProbability]
  simp only [ddhOTUncheckedRealGame, hcoins,
    ddhOTSenderReplyOf_ddhOTUncheckedProtocol, ddhOTAttackBothMessages_eq, decide_true,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_const, PMF.pure_apply, ↓reduceIte,
    ENNReal.toReal_one]

/-- In `ddhOTUncheckedIdealGame`, every simulator `S` outputs both messages with probability at
most `(Fintype.card G : ℝ)⁻¹`: the message it does not query is uniform and independent of its
view. -/
theorem succProbability_ddhOTUncheckedIdealGame_le
    (S : ProbComp (Bool × (G → ProbComp (G × G)))) :
    (Game.succProbability (ProbComp.eval (ddhOTUncheckedIdealGame S)) : ℝ) ≤
      (Fintype.card G : ℝ)⁻¹ := by
  have h_ennreal :
      ProbComp.eval (ddhOTUncheckedIdealGame S) true ≤ (Fintype.card G : ENNReal)⁻¹ := by
    simp only [ddhOTUncheckedIdealGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_uniform]
    refine PMF.bind_apply_le_on_support _ fun ⟨τ, guess⟩ _ => ?_
    cases τ <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · refine PMF.bind_apply_le_on_support _ fun m₀ _ => ?_
      rw [PMF.bind_comm]
      refine PMF.bind_apply_le_on_support _ fun pair _ =>
        PMF.uniformOfFintype_bind_pure_apply_true_le fun y hy y' hy' =>
          congrArg Prod.snd ((of_decide_eq_true hy).symm.trans (of_decide_eq_true hy'))
    · rw [PMF.bind_comm]
      refine PMF.bind_apply_le_on_support _ fun m₁ _ => ?_
      rw [PMF.bind_comm]
      refine PMF.bind_apply_le_on_support _ fun pair _ =>
        PMF.uniformOfFintype_bind_pure_apply_true_le fun y hy y' hy' =>
          congrArg Prod.fst ((of_decide_eq_true hy).symm.trans (of_decide_eq_true hy'))
  rw [Game.coe_succProbability, ← ENNReal.toReal_natCast, ← ENNReal.toReal_inv]
  exact ENNReal.toReal_mono (by simp) h_ennreal

/-- **Malicious-receiver separation for `ddhOTUncheckedProtocol`**: for every simulator `S`, the
distinguishing advantage between `ddhOTUncheckedRealGame` and `ddhOTUncheckedIdealGame S` is at
least `1 - (Fintype.card G : ℝ)⁻¹`. -/
theorem ddhOTUnchecked_malicious_receiver_advantage (g : G) (q : ℕ) [NeZero q] [Module (ZMod q) G]
    (b₀ b₁ : ZMod q)
    (S : ProbComp (Bool × (G → ProbComp (G × G)))) :
    1 - (Fintype.card G : ℝ)⁻¹ ≤
      (Game.advantage (ProbComp.eval (ddhOTUncheckedRealGame g q b₀ b₁))
        (ProbComp.eval (ddhOTUncheckedIdealGame S)) : ℝ) := by
  rw [Game.coe_advantage, succProbability_ddhOTUncheckedRealGame]
  exact (sub_le_sub_left (succProbability_ddhOTUncheckedIdealGame_le S) 1).trans
    (le_abs_self _)

end Cslib.Crypto.Protocols.MPC
