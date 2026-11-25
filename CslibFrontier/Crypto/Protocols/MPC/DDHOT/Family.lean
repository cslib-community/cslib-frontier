/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Protocols.MPC.Asymptotic
public import CslibFrontier.Crypto.Protocols.MPC.DDHOT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Tactic.PMFSwap

/-!
# Fair-coin DDH oblivious transfer as a protocol family, and its reduction to DDH

`Cslib.Crypto.Protocols.MPC.ddhOTProtocolWith` in `CslibFrontier/Crypto/Protocols/MPC/DDHOT.lean`
is a three-message 1-out-of-2 oblivious transfer over a group of prime order, a checked
per-branch-coin variant of the protocol of [BonehShoup2023], Section 23.5.7, Figure 23.17
(p. 1057), parameterized by party coin types, samplers, and exponent projections. Following
Section 23.5.7.2 ("Further assumptions about randomness", Remark 23.5, p. 1059) and [Lindell2017],
Section 4.2, Definition 4.1 (p. 7), this module instantiates the parties' coins as the raw
fair-coin bit strings they actually draw (`sampleExpBits`, width `n + |encNat (F.order d)|`) so
that each party's `PartyView.coins` retains its unreduced bit strings (`DDHOTSenderBitCoins` for
the sender, `List Bool` for the receiver), runs the protocol over a `PrimeOrderGroupFamily` `F` as
`ddhOTProbFamily`, gives the machine encoding `ddhOTEncoding`, and reduces a corrupted receiver to
DDH. `CslibFrontier/Crypto/Protocols/MPC/DDHOT/Simulators.lean` gives PPT simulators across all
static coalitions and proves stand-alone semi-honest security as a step toward Theorem 23.7
(`Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTProbFamily_semiHonestSecure`, #5829, #5293).

`ddhOTEncoding` writes group parameters with `F.encDesc` and group elements as `F.encode d` words.
The sender's input is the pair of words of its two messages and the receiver's input is its choice
bit; the sender's output `()` is the empty word and the receiver's output is the word of its
message. A corrupted party's view is written as its view words (`ddhOTSenderViewWords`,
`ddhOTReceiverViewWords`): the group elements as `F.encode d` words and the party's raw coin bit
strings verbatim (`encBits`). The words determine the view (`ddhOTSenderViewWords_injective`,
`ddhOTReceiverViewWords_injective`).

**Proof of the reduction.** Against a corrupted receiver (`{1}`), `ddhOTReceiverToDDHDistinguisher`
turns an environment `Z` into a DDH distinguisher: it runs `Z`'s input choice, draws the receiver's
raw coin bit string `bBits` from `sampleExpBits` (identical to the real receiver's coin draw, with
zero statistical loss on `PartyView.coins`) together with two chosen-branch bit strings `rBits,
sBits`, and embeds the DDH triple into the unchosen branch via `ddhOTReductionWithCoinsOf`. In the
real game, the honest sender's five bit strings enter the receiver's view only through their
`ZMod (F.order d)` residues, so replacing them with exact uniform exponents costs at most
`5 / 2 ^ n` (`advantage_bind_sampleDDHOTSenderBitCoins_le`), after which the hybrid real and ideal
games equal the real and random DDH experiments of the exact-branch reduction
(`real_receiver_eq_ddhRealExperiment_of`, `ideal_receiver_eq_ddhRandomExperiment_of`). The two
chosen-branch draws in `ddhOTReceiverToDDHDistinguisher` cost at most `2 / 2 ^ n` in each DDH
world, giving `advantage_ddhOTReceiverGame_le` (`≤ ddhAdv + 9 / 2 ^ n`).
`isPPT_ddhOTReceiverToDDHDistinguisher` proves that the reduction is uniform strict PPT whenever
`Z` is.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.DDHOTSenderBitCoins`,
  `Cslib.Crypto.Protocols.MPC.encDDHOTSenderBitCoins`, and
  `Cslib.Crypto.Protocols.MPC.DDHOTSenderBitCoins.toSenderCoins`: the sender's five raw fair-coin
  bit strings, their encoding, and their projection to `DDHOTSenderCoins q`.
* `Cslib.Crypto.Protocols.MPC.DDHOTSenderViewWords`,
  `Cslib.Crypto.Protocols.MPC.DDHOTReceiverViewWords`, their encodings, and
  `Cslib.Crypto.Protocols.MPC.DDHOTViewWords`: a party's view as words, preserving raw coin bit
  strings.
* `Cslib.Crypto.PrimeOrderGroupFamily.sampleExpBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.sampleDDHOTSenderBitCoins`: raw fair-coin bit-string samplers
  for one exponent and for the sender's five exponents.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTProbProtocol`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTProbFamily`: the fair-coin DDH OT protocol with raw
  bit-string coins and its `ProtocolFamily` over `F`.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTSenderViewWords`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTReceiverViewWords`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTEncoding`: view-word maps and machine encoding of
  `ddhOTProbFamily`.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTReceiverToDDHDistinguisher`: the reduction to DDH.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_sampleExpBits`,
  `Cslib.Crypto.PrimeOrderGroupFamily.eval_map_binaryValue_sampleExpBits`: `sampleExpBits` is
  uniform strict PPT and its `ZMod (F.order d)` residue law matches `sampleExp`.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTSenderViewWords_injective`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTReceiverViewWords_injective`: the words determine the
  view, including the unreduced coin bit strings.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTReceiverGame_le`: against a corrupted receiver
  and the exact-sender-mask simulator `ddhOTReceiverSimOf`, every environment's advantage is at
  most the DDH advantage of `ddhOTReceiverToDDHDistinguisher Z` plus `9 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhOTReceiverToDDHDistinguisher`: the reduction is
  uniform strict PPT.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 23.5.7 (Figure 23.17, p. 1057; Remark 23.5, p. 1059).
* [Y. Lindell, *How To Simulate It – A Tutorial on the Simulation Proof Technique*, ECCC
  TR17-112][Lindell2017], Section 4.2 (Definition 4.1, p. 7).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Turing.MultiTapeTM

/-! ### Raw fair-coin bit strings and views as words -/

/-- Raw fair-coin bit strings drawn by the sender in `ddhOTProbProtocol`: one bit string for the
Round 1 exponent `a` and two per branch for Round 3 encryption ([BonehShoup2023], Section 23.5.7.2,
"Further assumptions about randomness", p. 1059). -/
structure DDHOTSenderBitCoins where
  /-- Raw bit string from which the Round 1 exponent `a` is derived. -/
  exponentBits : List Bool
  /-- Raw bit string from which branch `0` coin `r₀` is derived. -/
  coinR₀Bits : List Bool
  /-- Raw bit string from which branch `0` coin `s₀` is derived. -/
  coinS₀Bits : List Bool
  /-- Raw bit string from which branch `1` coin `r₁` is derived. -/
  coinR₁Bits : List Bool
  /-- Raw bit string from which branch `1` coin `s₁` is derived. -/
  coinS₁Bits : List Bool

/-- The encoding of the sender's raw coins in the fair-coin DDH transfer: its five bit strings in
turn, all but the last framed. -/
enc_structure encDDHOTSenderBitCoins : DDHOTSenderBitCoins where
  exponentBits : encBits, coinR₀Bits : encBits, coinS₀Bits : encBits, coinR₁Bits : encBits,
  coinS₁Bits : encBits

/-- Project the sender's five raw bit strings into `DDHOTSenderCoins q` by interpreting each bit
string as a binary natural number modulo `q`. -/
@[expose] def DDHOTSenderBitCoins.toSenderCoins (q : ℕ) (c : DDHOTSenderBitCoins) :
    DDHOTSenderCoins q where
  exponent := (BitString.binaryValue c.exponentBits : ZMod q)
  coinR₀ := (BitString.binaryValue c.coinR₀Bits : ZMod q)
  coinS₀ := (BitString.binaryValue c.coinS₀Bits : ZMod q)
  coinR₁ := (BitString.binaryValue c.coinR₁Bits : ZMod q)
  coinS₁ := (BitString.binaryValue c.coinS₁Bits : ZMod q)

/-- The words of a corrupted sender's view in `ddhOTProbProtocol`: its two messages, its five raw
fair-coin bit strings, and the two branch keys of the receiver's Round 2 message. -/
structure DDHOTSenderViewWords where
  /-- The word of the message `m₀`. -/
  message₀ : List Bool
  /-- The word of the message `m₁`. -/
  message₁ : List Bool
  /-- The raw bit string from which the Round 1 exponent `a` is derived. -/
  exponentBits : List Bool
  /-- The raw bit string from which branch `0` coin `r₀` is derived. -/
  coinR₀Bits : List Bool
  /-- The raw bit string from which branch `0` coin `s₀` is derived. -/
  coinS₀Bits : List Bool
  /-- The raw bit string from which branch `1` coin `r₁` is derived. -/
  coinR₁Bits : List Bool
  /-- The raw bit string from which branch `1` coin `s₁` is derived. -/
  coinS₁Bits : List Bool
  /-- The word of the branch key `w₀`. -/
  branchKey₀ : List Bool
  /-- The word of the branch key `w₁`. -/
  branchKey₁ : List Bool

/-- The encoding of a sender's view words: each field in turn, all but the last framed. -/
enc_structure encDDHOTSenderViewWords : DDHOTSenderViewWords where
  message₀ : encBits, message₁ : encBits, exponentBits : encBits, coinR₀Bits : encBits,
  coinS₀Bits : encBits, coinR₁Bits : encBits, coinS₁Bits : encBits, branchKey₀ : encBits,
  branchKey₁ : encBits

/-- The words of a corrupted receiver's view in `ddhOTProbProtocol`: its choice bit, its raw
fair-coin bit string, the sender's first message, and the two components of each branch ciphertext
of the sender's reply. -/
structure DDHOTReceiverViewWords where
  /-- The receiver's choice bit `σ`. -/
  choiceBit : Bool
  /-- The receiver's raw fair-coin bit string. -/
  coinBits : List Bool
  /-- The word of the sender's first message `u`. -/
  firstMessage : List Bool
  /-- The word of the first component of the ciphertext of branch `0`. -/
  ephemeral₀ : List Bool
  /-- The word of the second component of the ciphertext of branch `0`. -/
  body₀ : List Bool
  /-- The word of the first component of the ciphertext of branch `1`. -/
  ephemeral₁ : List Bool
  /-- The word of the second component of the ciphertext of branch `1`. -/
  body₁ : List Bool

/-- The encoding of a receiver's view words: each field in turn, all but the last framed. -/
enc_structure encDDHOTReceiverViewWords : DDHOTReceiverViewWords where
  choiceBit : encBool, coinBits : encBits, firstMessage : encBits, ephemeral₀ : encBits,
  body₀ : encBits, ephemeral₁ : encBits, body₁ : encBits

/-- The view words of the two parties of `ddhOTProbProtocol`: `DDHOTSenderViewWords` for the sender
(party `0`) and `DDHOTReceiverViewWords` for the receiver (party `1`). -/
abbrev DDHOTViewWords : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) DDHOTSenderViewWords
    (fun _ => DDHOTReceiverViewWords) i

end Cslib.Crypto.Protocols.MPC

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols.MPC
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Raw fair-coin bit-string sampling -/

/-- Sample a raw fair-coin bit string of width `n + |encNat (F.order d)|`, the underlying random
bit string from which `sampleExp n d` derives an approximately uniform residue modulo `F.order d`
([BonehShoup2023], Section 23.5.7.2, Remark 23.5, p. 1059). -/
@[expose] noncomputable def sampleExpBits (n : ℕ) (d : F.Desc) : ProbComp (List Bool) :=
  BitString.sampleList (n + (encNat (F.order d)).length)

/-- `sampleExpBits` is uniform strict PPT whenever `n` and `d` are computable in polynomial
time. -/
theorem isPPTOn_sampleExpBits {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc) :
    IsPPTOn encIn encBits (fun a => F.sampleExpBits (n a) (d a)) := by
  have hord := F.computableInPolyTime_order.comp hd
  exact isPPTOn_sampleList.preprocess
    (hn.unary_add' ((ComputableInPolyTime.encoding_length encNat).comp hord))

/-- Interpreting a `sampleExpBits n d` bit string via `BitString.binaryValue` in `ZMod (F.order d)`
has the exact same residue law as `sampleExp n d`. -/
theorem eval_map_binaryValue_sampleExpBits (n : ℕ) (d : F.Desc) :
    (ProbComp.eval (F.sampleExpBits n d)).map
      (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) =
    (ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d)) := by
  simp only [sampleExpBits, sampleExp, ProbComp.sampleModNat, ProbComp.sampleBinaryNat,
    ProbComp.eval_map, PMF.map_comp]
  exact congrArg (PMF.map · _) (funext fun _ => (ZMod.natCast_mod _ _).symm)

/-- Replacing the `ZMod (F.order d)` residues of `m` independent `sampleExpBits n d` draws by `m`
independent exact uniform draws changes `Game.advantage` by at most `m / 2 ^ n`, via
`PMF.iid_map` and `advantage_bind_iid_sampleExp_le`. -/
private theorem advantage_bind_iid_sampleExpBits_le (n : ℕ) (d : F.Desc) (m : ℕ)
    (k : (Fin m → ZMod (F.order d)) → Game) :
    Game.advantage
      ((PMF.iid (ProbComp.eval (F.sampleExpBits n d)) m).bind fun v =>
        k fun i => (BitString.binaryValue (v i) : ZMod (F.order d)))
      ((PMF.iid (PMF.uniformOfFintype (ZMod (F.order d))) m).bind k) ≤ m / 2 ^ n := by
  have hiid :
      ((PMF.iid (ProbComp.eval (F.sampleExpBits n d)) m).bind fun v =>
        k fun i => (BitString.binaryValue (v i) : ZMod (F.order d))) =
      ((PMF.iid (ProbComp.eval (F.sampleExp n d)) m).bind fun v =>
        k fun i => (v i : ZMod (F.order d))) := by
    calc _ = ((PMF.iid (ProbComp.eval (F.sampleExpBits n d)) m).map
          (fun v i => (BitString.binaryValue (v i) : ZMod (F.order d)))).bind k :=
            (PMF.bind_map _ _ _).symm
      _ = ((PMF.iid (ProbComp.eval (F.sampleExp n d)) m).map
          (fun v i => (v i : ZMod (F.order d)))).bind k := by
            rw [← PMF.iid_map (ProbComp.eval (F.sampleExpBits n d))
              (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) m,
              F.eval_map_binaryValue_sampleExpBits, PMF.iid_map]
      _ = _ := PMF.bind_map _ _ _
  rw [hiid]
  exact F.advantage_bind_iid_sampleExp_le n d m k

/-- Replacing the `ZMod (F.order d)` residue of one `sampleExpBits n d` draw by an exact uniform
draw changes `Game.advantage` by at most `1 / 2 ^ n`. -/
theorem advantage_bind_sampleExpBits_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleExpBits n d)).bind fun bs =>
        k (BitString.binaryValue bs : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind k) ≤ 1 / 2 ^ n := by
  have h := F.advantage_bind_iid_sampleExpBits_le n d 1 fun v => k (v 0)
  simp only [PMF.iid, PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map, PMF.pure_bind,
    Function.comp_def, Nat.cast_one] at h
  exact h

/-- Replacing the `ZMod (F.order d)` residues of two independent `sampleExpBits n d` draws by two
exact uniform draws changes `Game.advantage` by at most `2 / 2 ^ n`. -/
private theorem advantage_bind_sampleExpBits_pair_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleExpBits n d)).bind fun rBits =>
        (ProbComp.eval (F.sampleExpBits n d)).bind fun sBits =>
          k (BitString.binaryValue rBits : ZMod (F.order d))
            (BitString.binaryValue sBits : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun r =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s => k r s) ≤ 2 / 2 ^ n := by
  have h := F.advantage_bind_iid_sampleExpBits_le n d 2 fun v => k (v 0) (v 1)
  simp only [PMF.iid, PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map, PMF.pure_bind,
    Function.comp_def, Nat.cast_ofNat] at h
  exact h

/-- Sample the sender's five raw fair-coin bit strings in `ddhOTProbProtocol` via five independent
`sampleExpBits n d` draws. -/
@[expose] noncomputable def sampleDDHOTSenderBitCoins (n : ℕ) (d : F.Desc) :
    ProbComp DDHOTSenderBitCoins := do
  let aBits ← F.sampleExpBits n d
  let r₀Bits ← F.sampleExpBits n d
  let s₀Bits ← F.sampleExpBits n d
  let r₁Bits ← F.sampleExpBits n d
  let s₁Bits ← F.sampleExpBits n d
  return ⟨aBits, r₀Bits, s₀Bits, r₁Bits, s₁Bits⟩

/-- Replacing the five projected `ZMod (F.order d)` residues of `sampleDDHOTSenderBitCoins n d`
with five exact uniform draws (`sampleDDHOTSenderCoins`) changes `Game.advantage` by at most
`5 / 2 ^ n`. -/
theorem advantage_bind_sampleDDHOTSenderBitCoins_le (n : ℕ) (d : F.Desc)
    (k : DDHOTSenderCoins (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleDDHOTSenderBitCoins n d)).bind fun raw₀ =>
        k (raw₀.toSenderCoins (F.order d)))
      ((ProbComp.eval (sampleDDHOTSenderCoins (F.order d))).bind k) ≤ 5 / 2 ^ n := by
  have h := F.advantage_bind_iid_sampleExpBits_le n d 5 fun v => k ⟨v 0, v 1, v 2, v 3, v 4⟩
  simp only [sampleDDHOTSenderBitCoins, DDHOTSenderBitCoins.toSenderCoins, sampleDDHOTSenderCoins,
    PMF.iid, PMF.monad_bind_eq_bind, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.bind_bind, PMF.bind_map, PMF.pure_bind, Function.comp_def, Nat.cast_ofNat] at h ⊢
  exact h

/-! ### The fair-coin protocol family and its encoding -/

/-- Fair-coin three-message DDH 1-out-of-2 Oblivious Transfer protocol over `F.Carrier d` at
security parameter `n`, with raw fair-coin bit strings (`DDHOTSenderBitCoins` and `List Bool`)
stored unreduced in `PartyView.coins` ([BonehShoup2023], Section 23.5.7.2, Remark 23.5, p. 1059). -/
@[expose] noncomputable def ddhOTProbProtocol (n : ℕ) (d : F.Desc) :
    Protocol 2 noOracleSpec (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
      (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) :=
  ddhOTProtocolWith (F.generator d) (F.order d)
    (F.sampleDDHOTSenderBitCoins n d) (F.sampleExpBits n d)
    (DDHOTSenderBitCoins.toSenderCoins (F.order d))
    (fun bs => (BitString.binaryValue bs : ZMod (F.order d)))

/-- `ddhOTProbProtocol` over the groups of `F` as a `ProtocolFamily`: at security parameter `n` and
public parameters `d`, both parties draw raw fair-coin bit strings via `sampleExpBits n d`, retain
those bit strings in `PartyView.coins`, and compute `otFunctionality (F.Carrier d)`. -/
noncomputable abbrev ddhOTProbFamily : ProtocolFamily 2 where
  Desc := F.Desc
  spec _ _ := noOracleSpec
  sc _ d := ddhOTSchedule (F.Carrier d)
  In _ d := OTIn (F.Carrier d)
  Coins _ _ := DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)
  Out _ d := OTOut (F.Carrier d)
  protocol := F.ddhOTProbProtocol
  world _ _ := noOracleWorld
  functionality _ d := otFunctionality (F.Carrier d)

/-- The words of a sender's view in `ddhOTProbProtocol` over `F.Carrier d`: the messages and branch
keys as `F.encode d` words, and the five raw coin bit strings verbatim. -/
@[expose] def ddhOTSenderViewWords (d : F.Desc)
    (view : PartyView (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
      (ddhOTSchedule (F.Carrier d)) 0) : DDHOTSenderViewWords :=
  let (m₀, m₁) := view.input
  let c := view.coins
  let (_, w, _) := view.received
  let (w₀, w₁) := w rfl
  ⟨F.encode d m₀, F.encode d m₁, c.exponentBits, c.coinR₀Bits, c.coinS₀Bits, c.coinR₁Bits,
    c.coinS₁Bits, F.encode d w₀, F.encode d w₁⟩

/-- The words of a receiver's view in `ddhOTProbProtocol` over `F.Carrier d`: the choice bit, the
raw coin bit string verbatim, and the received group elements as `F.encode d` words. -/
@[expose] def ddhOTReceiverViewWords (d : F.Desc)
    (view : PartyView (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
      (ddhOTSchedule (F.Carrier d)) 1) : DDHOTReceiverViewWords :=
  let (u, _, reply, _) := view.received
  let ((e₀, c₀), (e₁, c₁)) := reply rfl
  ⟨view.input, view.coins, F.encode d (u rfl), F.encode d e₀, F.encode d c₀, F.encode d e₁,
    F.encode d c₁⟩

/-- The words determine a sender's view, including its five unreduced coin bit strings. -/
theorem ddhOTSenderViewWords_injective (d : F.Desc) :
    Function.Injective (F.ddhOTSenderViewWords d) := by
  rintro ⟨⟨m₀, m₁⟩, ⟨a, r₀, s₀, r₁, s₁⟩, ⟨u, w, reply, ⟨⟩⟩⟩
    ⟨⟨m₀', m₁'⟩, ⟨a', r₀', s₀', r₁', s₁'⟩, ⟨u', w', reply', ⟨⟩⟩⟩ h
  simp only [ddhOTSenderViewWords, DDHOTSenderViewWords.mk.injEq] at h
  obtain ⟨hm₀, hm₁, rfl, rfl, rfl, rfl, rfl, hw₀, hw₁⟩ := h
  refine PartyView.ext ?_ rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Prod.ext (F.encode_injective d hm₀) (F.encode_injective d hm₁)
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · exact Round.received_message_ext fun _ =>
      Prod.ext (F.encode_injective d hw₀) (F.encode_injective d hw₁)
  · exact Round.received_message_eq_of_ne (by decide) _ _

/-- The words determine a receiver's view, including its unreduced coin bit string. -/
theorem ddhOTReceiverViewWords_injective (d : F.Desc) :
    Function.Injective (F.ddhOTReceiverViewWords d) := by
  rintro ⟨σ, bBits, ⟨u, w, reply, ⟨⟩⟩⟩ ⟨σ', bBits', ⟨u', w', reply', ⟨⟩⟩⟩ h
  injection h with hσ hb hu he₀ hc₀ he₁ hc₁
  refine PartyView.ext hσ hb (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Round.received_message_ext fun _ => F.encode_injective d hu
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · exact Round.received_message_ext fun _ =>
      Prod.ext (Prod.ext (F.encode_injective d he₀) (F.encode_injective d hc₀))
        (Prod.ext (F.encode_injective d he₁) (F.encode_injective d hc₁))

/-- The encoding of `ddhOTProbFamily` for machines. Group parameters are written with `F.encDesc`.
The sender's input `(m₀, m₁)` is the pair of words `(F.encode d m₀, F.encode d m₁)`
(`encPair encBits encBits`) and the receiver's input is its choice bit (`encBool`). The sender's
output `()` is the empty word (`encUnit`) and the receiver's output `m_σ` is the word
`F.encode d m_σ`. Each party's view is its view words (`ddhOTSenderViewWords`,
`ddhOTReceiverViewWords`, preserving the raw coin bit strings), encoded by
`encDDHOTSenderViewWords` and `encDDHOTReceiverViewWords`. -/
@[expose] noncomputable def ddhOTEncoding : F.ddhOTProbFamily.Encoding where
  desc := F.encDesc
  input :=
    { Rep := OTIn (List Bool)
      enc := fun i => Fin.cases (motive := fun i => OTIn (List Bool) i ↪ List Bool)
        (encPair encBits encBits) (fun _ => encBool) i
      rep := fun _ d i => Fin.cases (motive := fun i => OTIn (F.Carrier d) i ↪ OTIn (List Bool) i)
        ⟨Prod.map (F.encode d) (F.encode d), (F.encode_injective d).prodMap (F.encode_injective d)⟩
        (fun _ => Function.Embedding.refl Bool) i }
  output :=
    { Rep := OTOut (List Bool)
      enc := fun i => Fin.cases (motive := fun i => OTOut (List Bool) i ↪ List Bool) encUnit
        (fun _ => encBits) i
      rep := fun _ d i =>
        Fin.cases (motive := fun i => OTOut (F.Carrier d) i ↪ OTOut (List Bool) i)
          (Function.Embedding.refl Unit) (fun _ => ⟨F.encode d, F.encode_injective d⟩) i }
  view :=
    { Rep := DDHOTViewWords
      enc := fun i => Fin.cases (motive := fun i => DDHOTViewWords i ↪ List Bool)
        encDDHOTSenderViewWords (fun _ => encDDHOTReceiverViewWords) i
      rep := fun _ d i => Fin.cases (motive := fun i =>
          PartyView (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
            (ddhOTSchedule (F.Carrier d)) i ↪ DDHOTViewWords i)
        ⟨F.ddhOTSenderViewWords d, F.ddhOTSenderViewWords_injective d⟩
        (Fin.cases (motive := fun j =>
            PartyView (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
              (ddhOTSchedule (F.Carrier d)) j.succ ↪ DDHOTViewWords j.succ)
          ⟨F.ddhOTReceiverViewWords d, F.ddhOTReceiverViewWords_injective d⟩
          fun k => k.elim0) i }

/-! ### Corrupted receiver: the reduction to DDH -/

/-- The DDH distinguisher built from an environment `Z` that corrupts the receiver: given the
security parameter `n`, group parameters `d` and a DDH triple `(u, v, w)`, run `Z.choose`, draw
the receiver's raw coin bit string `bBits` and two chosen-branch bit strings `rBits, sBits` with
`sampleExpBits n d`, and run `ddhOTReductionWithCoinsOf` with `Z.guess`, recording `bBits`
unreduced in the receiver's `PartyView.coins` and embedding `(u, v, w)` into the unchosen
branch. -/
@[expose] noncomputable def ddhOTReceiverToDDHDistinguisher
    (Z : Environment F.ddhOTProbFamily {1}) :
    F.DDHDistinguisher := fun n d u v w => do
  let c ← Z.choose n d
  let bBits ← F.sampleExpBits n d
  let rBits ← F.sampleExpBits n d
  let sBits ← F.sampleExpBits n d
  let q := F.order d
  ddhOTReductionWithCoinsOf (C₀ := DDHOTSenderBitCoins) (F.generator d)
    (fun bs : List Bool => (BitString.binaryValue bs : ZMod q))
    c.inputs (Z.guess n d c.state) bBits
    (BitString.binaryValue rBits : ZMod q) (BitString.binaryValue sBits : ZMod q) u v w

/-- Intermediate reduction that draws the receiver's raw bit string `bBits ← sampleExpBits n d`
(matching the real receiver) and exact uniform chosen-branch exponents `r, s : ZMod (F.order d)`. -/
private noncomputable def ddhOTReceiverToDDHExact (Z : Environment F.ddhOTProbFamily {1}) :
    F.DDHDistinguisher := fun n d u v w => do
  let c ← Z.choose n d
  ddhOTReductionOf (C₀ := DDHOTSenderBitCoins) (F.generator d) (F.order d) (F.sampleExpBits n d)
    (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))
    c.inputs (Z.guess n d c.state) u v w

/-- Replacing the honest sender's five bit strings in `ddhOTProbFamily.realGame` at `{1}` with five
exact uniform exponents yields `ddhRealGame` of `ddhOTReceiverToDDHExact`, within `5 / 2 ^ n`. -/
private theorem advantage_realGame_receiver_ddhRealGame_le (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTProbFamily {1}) (n : ℕ) :
    Game.advantage (F.ddhOTProbFamily.realGame setup {1} Z n)
      (F.ddhRealGame setup (F.ddhOTReceiverToDDHExact Z) n) ≤ 5 / 2 ^ n := by
  simp only [ProtocolFamily.realGame, ddhOTProbProtocol, Protocol.realJoint,
    evalWith_ddhOTProtocolWith, ddhRealGame, Game.withSetup, eval_ddhRealExperiment,
    ddhOTReceiverToDDHExact, ProbComp.eval_bind, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.pure_map, Prod.map, id, restrict_singleton]
  refine Game.advantage_bind_le_nnreal _ _ _ fun d => ?_
  have hswap (c : InputChoice F.ddhOTProbFamily n d) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun a =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun b =>
          ProbComp.eval (ddhOTReductionOf (C₀ := DDHOTSenderBitCoins) (F.generator d) (F.order d)
            (F.sampleExpBits n d)
            (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))
            c.inputs (Z.guess n d c.state)
            (a • F.generator d) (b • F.generator d) ((a * b) • F.generator d))) =
      ((ProbComp.eval (sampleDDHOTSenderCoins (F.order d))).bind fun c₀ =>
        (ProbComp.eval (F.sampleExpBits n d)).bind fun bBits =>
          ProbComp.eval (Z.guess n d c.state
            (singletonView (ddhOTReceiverViewWith (c.inputs 1) bBits (c₀.exponent • F.generator d)
              (ddhOTSenderReplyUnchecked (F.generator d) (c.inputs 0) c₀
                (ddhOTReceiverMsg (F.generator d) (c.inputs 1)
                  (BitString.binaryValue bBits : ZMod (F.order d))
                  (c₀.exponent • F.generator d)))),
              otOutputs c.inputs))) := by
    simpa only [eval_ddhRealExperiment, PMF.monad_bind_eq_bind] using
      (real_receiver_eq_ddhRealExperiment_of (C₀ := DDHOTSenderBitCoins) (F.generator d)
        (F.order d) (F.sampleExpBits n d)
        (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))
        c.inputs (Z.guess n d c.state)).symm
  have hrhs :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun a =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun b =>
          (ProbComp.eval (Z.choose n d)).bind fun c =>
            ProbComp.eval (ddhOTReductionOf (C₀ := DDHOTSenderBitCoins) (F.generator d) (F.order d)
              (F.sampleExpBits n d)
              (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))
              c.inputs (Z.guess n d c.state)
              (a • F.generator d) (b • F.generator d) ((a * b) • F.generator d))) =
      ((ProbComp.eval (Z.choose n d)).bind fun c =>
        (ProbComp.eval (sampleDDHOTSenderCoins (F.order d))).bind fun c₀ =>
          (ProbComp.eval (F.sampleExpBits n d)).bind fun bBits =>
            ProbComp.eval (Z.guess n d c.state
              (singletonView (ddhOTReceiverViewWith (c.inputs 1) bBits
                (c₀.exponent • F.generator d)
                (ddhOTSenderReplyUnchecked (F.generator d) (c.inputs 0) c₀
                  (ddhOTReceiverMsg (F.generator d) (c.inputs 1)
                    (BitString.binaryValue bBits : ZMod (F.order d))
                    (c₀.exponent • F.generator d)))),
                otOutputs c.inputs))) := by
    calc _ = (ProbComp.eval (Z.choose n d)).bind fun c =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun a =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun b =>
              ProbComp.eval (ddhOTReductionOf (C₀ := DDHOTSenderBitCoins) (F.generator d)
                (F.order d) (F.sampleExpBits n d)
                (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))
                c.inputs (Z.guess n d c.state)
                (a • F.generator d) (b • F.generator d) ((a * b) • F.generator d)) := by pmf_swap
      _ = _ := congrArg (PMF.bind _) (funext hswap)
  rw [hrhs]
  refine Game.advantage_bind_le_nnreal _ _ _ fun c => ?_
  exact F.advantage_bind_sampleDDHOTSenderBitCoins_le n d fun c₀ =>
    (ProbComp.eval (F.sampleExpBits n d)).bind fun bBits =>
      ProbComp.eval (Z.guess n d c.state
        (singletonView (ddhOTReceiverViewWith (c.inputs 1) bBits (c₀.exponent • F.generator d)
          (ddhOTSenderReplyUnchecked (F.generator d) (c.inputs 0) c₀
            (ddhOTReceiverMsg (F.generator d) (c.inputs 1)
              (BitString.binaryValue bBits : ZMod (F.order d))
              (c₀.exponent • F.generator d)))),
          otOutputs c.inputs))

/-- The ideal game against a corrupted receiver with the exact-sender-mask simulator
`ddhOTReceiverSimOf` equals the random DDH game of `ddhOTReceiverToDDHExact`. -/
private theorem idealGame_receiver_eq (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTProbFamily {1}) (n : ℕ) :
    F.ddhOTProbFamily.idealGame setup {1}
        (fun n d => ddhOTReceiverSimOf (F.generator d) (F.order d) (F.sampleExpBits n d)
          (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))) Z n =
      F.ddhRandomGame setup (F.ddhOTReceiverToDDHExact Z) n := by
  simp only [ProtocolFamily.idealGame, ddhRandomGame, Game.withSetup, PMF.monad_bind_eq_bind]
  refine congrArg (PMF.bind _) (funext fun d => ?_)
  simp only [← ProbComp.eval_bind,
    ideal_receiver_eq_ddhRandomExperiment_of (C₀ := DDHOTSenderBitCoins) (F.generator d)
      (F.order d) (F.smul_generator_surjective d) (F.sampleExpBits n d)
      (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))]
  simp only [eval_ddhRandomExperiment, ddhOTReceiverToDDHExact, ProbComp.eval_bind]
  pmf_swap

/-- On every triple, `ddhOTReceiverToDDHExact` and `ddhOTReceiverToDDHDistinguisher` accept with
probabilities within `2 / 2 ^ n` (only the two chosen-branch coins differ; the receiver's raw coin
`bBits ← sampleExpBits n d` is drawn identically in both). -/
private theorem advantage_ddhOTReceiverToDDHExact_le (Z : Environment F.ddhOTProbFamily {1}) (n : ℕ)
    (d : F.Desc) (u v w : F.Carrier d) :
    Game.advantage (ProbComp.eval (F.ddhOTReceiverToDDHExact Z n d u v w))
      (ProbComp.eval (F.ddhOTReceiverToDDHDistinguisher Z n d u v w)) ≤ 2 / 2 ^ n := by
  simp only [ddhOTReceiverToDDHExact, ddhOTReceiverToDDHDistinguisher, ddhOTReductionOf,
    ProbComp.eval_bind, ProbComp.eval_uniform]
  refine Game.advantage_bind_le_nnreal _ _ _ fun c =>
    Game.advantage_bind_le_nnreal _ _ _ fun bBits => ?_
  rw [Game.advantage_comm]
  exact F.advantage_bind_sampleExpBits_pair_le n d fun r s =>
    ProbComp.eval (ddhOTReductionWithCoinsOf (C₀ := DDHOTSenderBitCoins) (F.generator d)
      (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))
      c.inputs (Z.guess n d c.state) bBits r s u v w)

/-- Concrete reduction step for a corrupted receiver in `ddhOTProbFamily` against the
exact-sender-mask simulator `ddhOTReceiverSimOf` (which draws the receiver's raw bit string via
`sampleExpBits n d` and the five sender/mask exponents uniformly): every environment's advantage is
at most the DDH advantage of `ddhOTReceiverToDDHDistinguisher Z` plus `9 / 2 ^ n`. For the
certified PPT simulator `ddhOTReceiverSimProb`, see `advantage_ddhOTProbReceiverGame_le` in
`CslibFrontier/Crypto/Protocols/MPC/DDHOT/Simulators.lean`. -/
theorem advantage_ddhOTReceiverGame_le (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTProbFamily {1}) (n : ℕ) :
    Game.advantage (F.ddhOTProbFamily.realGame setup {1} Z n)
        (F.ddhOTProbFamily.idealGame setup {1}
          (fun n d => ddhOTReceiverSimOf (F.generator d) (F.order d) (F.sampleExpBits n d)
            (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))) Z n) ≤
      Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
        (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) + 9 / 2 ^ n := by
  rw [idealGame_receiver_eq]
  have hreal0 := F.advantage_realGame_receiver_ddhRealGame_le setup Z n
  have hreal1 : Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHExact Z) n)
      (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) ≤ 2 / 2 ^ n := by
    simp only [ddhRealGame, Game.withSetup, eval_ddhRealExperiment]
    exact Game.advantage_bind_le_nnreal _ _ _ fun d =>
      Game.advantage_bind_le_nnreal _ _ _ fun a => Game.advantage_bind_le_nnreal _ _ _ fun b =>
        F.advantage_ddhOTReceiverToDDHExact_le Z n d _ _ _
  have hrandom : Game.advantage (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
      (F.ddhRandomGame setup (F.ddhOTReceiverToDDHExact Z) n) ≤ 2 / 2 ^ n := by
    rw [Game.advantage_comm]
    simp only [ddhRandomGame, Game.withSetup, eval_ddhRandomExperiment]
    exact Game.advantage_bind_le_nnreal _ _ _ fun d =>
      Game.advantage_bind_le_nnreal _ _ _ fun a => Game.advantage_bind_le_nnreal _ _ _ fun b =>
        Game.advantage_bind_le_nnreal _ _ _ fun c =>
          F.advantage_ddhOTReceiverToDDHExact_le Z n d _ _ _
  calc _ ≤ 5 / 2 ^ n + (2 / 2 ^ n +
        (Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
          (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) + 2 / 2 ^ n)) :=
        (Game.advantage_triangle _ (F.ddhRealGame setup (F.ddhOTReceiverToDDHExact Z) n) _).trans
          (add_le_add hreal0 ((Game.advantage_triangle _ _ _).trans (add_le_add hreal1
            ((Game.advantage_triangle _ _ _).trans (add_le_add le_rfl hrandom)))))
    _ = _ := by ring

/-! ### Corrupted receiver: efficiency of the reduction -/

/-- The view words that `ddhOTReceiverToDDHDistinguisher` gives the environment, from the DDH
input `x`, the words `m₀, m₁` of the messages, the choice bit `σ` and the raw bit strings
`bBits, rBits, sBits`. `bBits` is recorded verbatim in `coinBits`, while scalar multiplications use
`BitString.binaryValue`. -/
private def ddhOTReceiverViewWordsOf (x : F.DDHInput) (m₀ m₁ : List Bool) (σ : Bool)
    (bBits rBits sBits : List Bool) : DDHOTReceiverViewWords :=
  let d := x.groupParameters
  let q := F.order d
  let b := BitString.binaryValue bBits
  let r := BitString.binaryValue rBits
  let s := BitString.binaryValue sBits
  let e := (r : ZMod q) • F.generator d + (s : ZMod q) • x.leftPublic
  let chosen := F.encode d ((b : ZMod q) • e)
  let other := F.encode d (x.candidateShared - (b : ZMod q) • x.rightPublic)
  ⟨σ, bBits, F.encode d x.leftPublic, if σ then F.encode d x.rightPublic else F.encode d e,
    F.add (d, if σ then other else chosen, m₀),
    if σ then F.encode d e else F.encode d x.rightPublic,
    F.add (d, if σ then chosen else other, m₁)⟩

/-- The word of the outputs that `ddhOTReceiverToDDHDistinguisher` gives the environment, from the
words `m₀, m₁` of the messages and the choice bit `σ`: the table of the empty word for the sender
and the word of `m_σ` for the receiver. -/
private noncomputable def ddhOTOutputWords (m₀ m₁ : List Bool) (σ : Bool) : List Bool :=
  encPi encBits fun i : Fin 2 =>
    Fin.cases (motive := fun _ => List Bool) [] (fun _ => if σ then m₁ else m₀) i

/-- The words of the guessing-stage input that `ddhOTReceiverToDDHDistinguisher` gives the
environment, laid out as `encGuessInputFields`: the security parameter, the group parameters, the
state, the table of the receiver's view words, and the word of the outputs. -/
private noncomputable def ddhOTReceiverGuessWords (x : F.DDHInput) (m₀ m₁ : List Bool) (σ : Bool)
    (state bBits rBits sBits : List Bool) : ℕ × F.Desc × List Bool × List Bool × List Bool :=
  (x.secParam, x.groupParameters, state,
    encPi encBits fun _ : ({1} : Finset (Fin 2)) =>
      encDDHOTReceiverViewWords (F.ddhOTReceiverViewWordsOf x m₀ m₁ σ bBits rBits sBits),
    ddhOTOutputWords m₀ m₁ σ)

/-- Context read by the final stage of `ddhOTReceiverToDDHDistinguisher`: the DDH input, the words
of the environment's choice, and the three raw bit strings. -/
private structure ReceiverReductionCtx where
  ddh : F.DDHInput
  inputs : (i : Fin 2) → OTIn (List Bool) i
  state : List Bool
  bBits : List Bool
  rBits : List Bool
  sBits : List Bool

noncomputable section

private enc_structure encReceiverReductionCtx (F : PrimeOrderGroupFamily) :
    ReceiverReductionCtx F where
  ddh : F.encDDHInput, inputs : (encDPi F.ddhOTEncoding.input.enc), state : encBits,
  bBits : encBits, rBits : encBits, sBits : encBits

/-- `ddhOTReceiverToDDHDistinguisher Z` is uniform strict PPT whenever `Z` is. -/
theorem isPPT_ddhOTReceiverToDDHDistinguisher
    {Z : Environment F.ddhOTProbFamily {1}}
    (hZ : Z.IsPPT F.ddhOTEncoding) : (F.ddhOTReceiverToDDHDistinguisher Z).IsPPT := by
  obtain ⟨W, hW, hWeq⟩ := hZ.guess.exists_bool_factor (encGuessInput_apply F.ddhOTEncoding)
  let E := encReceiverReductionCtx F
  have hddh := encReceiverReductionCtx_ddh_polyTime F .id'
  have hinputs := encReceiverReductionCtx_inputs_polyTime F .id'
  have hin₀ : ComputableInPolyTime (fun p : F.ReceiverReductionCtx => p.inputs 0) E
      (encPair encBits encBits) :=
    (ComputableInPolyTime.dpi_apply F.ddhOTEncoding.input.enc 0).comp hinputs
  have hσ : ComputableInPolyTime (fun p : F.ReceiverReductionCtx => p.inputs 1) E encBool :=
    (ComputableInPolyTime.dpi_apply F.ddhOTEncoding.input.enc 1).comp hinputs
  have hd := F.encDDHInput_groupParameters_polyTime hddh
  have hview : ComputableInPolyTime (fun p : F.ReceiverReductionCtx =>
      F.ddhOTReceiverViewWordsOf p.ddh (p.inputs 0).1 (p.inputs 0).2 (p.inputs 1)
        p.bBits p.rBits p.sBits) E encDDHOTReceiverViewWords := by
    dsimp only [ddhOTReceiverViewWordsOf]
    fun_prop
  have houtputs : ComputableInPolyTime (fun p : F.ReceiverReductionCtx =>
      ddhOTOutputWords (p.inputs 0).1 (p.inputs 0).2 (p.inputs 1)) E encBits :=
    (ComputableInPolyTime.pi fun i =>
      Fin.cases (ComputableInPolyTime.const []) (fun _ => hσ.ite' hin₀.snd' hin₀.fst')
        i).encoding_comp
  have hwords : ComputableInPolyTime (fun p : F.ReceiverReductionCtx =>
      F.ddhOTReceiverGuessWords p.ddh (p.inputs 0).1 (p.inputs 0).2 (p.inputs 1)
        p.state p.bBits p.rBits p.sBits) E (encGuessInputFields F.ddhOTEncoding) :=
    (F.encDDHInput_secParam_polyTime hddh).prod
      (hd.prod ((encReceiverReductionCtx_state_polyTime F .id').prod
        (((ComputableInPolyTime.pi fun _ => hview.encoding_comp).encoding_comp).prod houtputs)))
  have hsample {α : Type} {enc : α ↪ List Bool} {x : α → F.DDHInput}
      (hx : ComputableInPolyTime x enc F.encDDHInput) :
      IsPPTOn enc encBits fun a => F.sampleExpBits (x a).secParam (x a).groupParameters :=
    F.isPPTOn_sampleExpBits (by fun_prop) (by fun_prop)
  have hprogram : IsPPTOn F.encDDHInput encBool (fun x => do
      let cw ← (fun c => ((fun i => F.ddhOTEncoding.input.rep x.secParam
          x.groupParameters i (c.inputs i)), c.state)) <$> Z.choose x.secParam x.groupParameters
      let bBits ← F.sampleExpBits x.secParam x.groupParameters
      let rBits ← F.sampleExpBits x.secParam x.groupParameters
      let sBits ← F.sampleExpBits x.secParam x.groupParameters
      let ctx : F.ReceiverReductionCtx := ⟨x, cw.1, cw.2, bBits, rBits, sBits⟩
      W (F.ddhOTReceiverGuessWords ctx.ddh (ctx.inputs 0).1 (ctx.inputs 0).2 (ctx.inputs 1)
        ctx.state ctx.bBits ctx.rBits ctx.sBits)) :=
    (hZ.choose.preprocess (prepare := fun x : F.DDHInput => (x.secParam, x.groupParameters))
      (by fun_prop)).bind_with <|
      (hsample (by fun_prop)).bind_with <| (hsample (by fun_prop)).bind_with <|
        (hsample (by fun_prop)).bind_with <| hW.preprocess (hwords.comp (by fun_prop))
  refine hprogram.congr fun x => ?_
  simp only [ddhOTReceiverToDDHDistinguisher, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun c => congrArg (PMF.bind _) (funext fun bBits =>
    congrArg (PMF.bind _) (funext fun rBits => congrArg (PMF.bind _) (funext fun sBits => ?_))))
  obtain ⟨xs, state⟩ := c
  obtain ⟨⟨m₀, m₁⟩, σ, rfl⟩ : ∃ (m : F.Carrier x.groupParameters × F.Carrier x.groupParameters)
      (σ : Bool), xs = fun i =>
        Fin.cases (motive := fun i => OTIn (F.Carrier x.groupParameters) i) m (fun _ => σ) i :=
    ⟨xs 0, xs 1, funext fun i => Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i⟩
  refine congrArg ProbComp.eval (Eq.trans (congrArg W ?_)
    (hWeq ⟨x.secParam, x.groupParameters, state, _, _⟩).symm)
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_)))
  · refine Eq.trans ?_
      (F.ddhOTEncoding.view.encCoalition_singleton x.secParam x.groupParameters 1 _).symm
    refine congrArg (encPi encBits) (funext fun _ => congrArg encDDHOTReceiverViewWords ?_)
    let q := F.order x.groupParameters
    let b := BitString.binaryValue bBits
    let r := BitString.binaryValue rBits
    let s := BitString.binaryValue sBits
    let e := (r : ZMod q) • F.generator x.groupParameters + (s : ZMod q) • x.leftPublic
    cases σ
    · change F.ddhOTReceiverViewWordsOf x (F.encode _ m₀) (F.encode _ m₁) false bBits rBits sBits =
        F.ddhOTReceiverViewWords x.groupParameters (ddhOTReceiverViewWith false bBits x.leftPublic
          ((e, (b : ZMod q) • e + m₀),
            (x.rightPublic, x.candidateShared - (b : ZMod q) • x.rightPublic + m₁)))
      simp only [ddhOTReceiverViewWordsOf, ddhOTReceiverViewWords, ddhOTReceiverViewWith,
        Bool.false_eq_true, ↓reduceIte, F.add_encode]
      rfl
    · change F.ddhOTReceiverViewWordsOf x (F.encode _ m₀) (F.encode _ m₁) true bBits rBits sBits =
        F.ddhOTReceiverViewWords x.groupParameters (ddhOTReceiverViewWith true bBits x.leftPublic
          ((x.rightPublic, x.candidateShared - (b : ZMod q) • x.rightPublic + m₀),
            (e, (b : ZMod q) • e + m₁)))
      simp only [ddhOTReceiverViewWordsOf, ddhOTReceiverViewWords, ddhOTReceiverViewWith,
        ↓reduceIte, F.add_encode]
      rfl
  · simp only [ddhOTReceiverGuessWords, ddhOTOutputWords, PartyEncoding.encAll,
      Function.Embedding.coeFn_mk, encDPi_apply]
    congr 1
    funext i
    refine Fin.cases rfl (fun _ => ?_) i
    cases σ <;> rfl

end

end Cslib.Crypto.PrimeOrderGroupFamily
