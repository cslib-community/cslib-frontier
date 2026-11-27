/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Encoding

/-!
# Tests for the machine encoding of Yao's protocol in the plain model

A client of `CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Encoding` under module
encapsulation. That module provides definitions only, and so does this one: nothing here is a PPT
certificate or a security statement that is proved.

* The words of received messages are computed on a two-message schedule: each party's list holds
  the word of the one message addressed to it and nothing for the other round, so the lists of the
  two parties differ.
* The words of subprotocol coins are computed on two sequential transfers: a party that fills one
  slot of each call has one word for each call, and `Schedule.encComposedCoins` frames the outer
  coins before their list.
* The received words follow `++` and `Round.embed`: along two ping-pongs a party's words are
  appended, in a ping-pong lifted to two of three parties a party receives the words of its slot,
  and the third party receives none.
* In `Yao.kdfDDHProbFamily`, the first received word of the evaluator's view words is
  `Yao.encMessage` of the garbler's message, whatever the number of transfers.
* The encoded view words of `Yao.kdfDDHProbEncoding` distinguish different views.
* `Environment.IsPPT`, `SimulatorFamily.IsPPT` of the composed simulator family
  `Yao.kdfDDHProbSim` at the coalitions `{1}` and `{0}`, and `ProtocolFamily.SemiHonestSecure` are
  statements over `Yao.kdfDDHProbEncoding`; the last one asks for a simulator family and for
  environments that are PPT for this encoding. They are stated, not proved (#6045, criterion 2).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.YaoPlainEncoding

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Protocols.MPC Turing.MultiTapeTM

/-! ### Received words and coin words on small schedules -/

/-- A word from party `0` to party `1`, then a word back. -/
abbrev pingPong : Schedule 2 noOracleSpec :=
  [.message 0 1 (List Bool), .message 1 0 (List Bool)]

/-- Party `1` receives the first message only. -/
example : Schedule.receivedWords (i := 1) pingPong (encBits, encBits, ())
    (fun _ => [true], fun h => absurd h (by decide), ()) = [[true]] := by
  decide

/-- Party `0` receives the second message only. -/
example : Schedule.receivedWords (i := 0) pingPong (encBits, encBits, ())
    (fun h => absurd h (by decide), fun _ => [false, true], ()) = [[false, true]] := by
  decide

/-- The sender of two sequential transfers has one coin word for each transfer. -/
example : Schedule.subCoinsWords (spec₁ := otSpec Unit) (Coins₂ := fun _ _ => List Bool)
    (fun _ _ => encBits) (i := 0) (seqBatchOTSchedule 2 Unit)
    (fun _ _ => [true], fun _ _ => [false], ()) = [[true], [false]] := by
  decide

/-- The word of composed coins is the framed outer word, then the list of the inner words. -/
example : Schedule.encComposedCoins (spec₁ := otSpec Unit) (Coins₂ := fun _ _ => List Bool)
    (Coins₁ := fun _ => List Bool) (sc₁ := seqBatchOTSchedule 2 Unit) (i := 0) encBits
    (fun _ _ => encBits) ([true, true], fun _ _ => [true], fun _ _ => [false], ()) =
      encPair encBits (encList encBits) ([true, true], [[true], [false]]) := by
  decide

/-! ### Received words along the operations of `Schedule.compose` -/

/-- Along two ping-pongs, party `1` receives its word of the first, then its word of the
second. -/
example :
    Schedule.receivedWords (i := 1) (pingPong ++ pingPong)
        (Schedule.MessageEncodings.append pingPong (encBits, encBits, ()) (encBits, encBits, ()))
        (Schedule.Received.append (sc₁ := pingPong) (sc₂ := pingPong)
          (fun _ => [true], fun h => absurd h (by decide), ())
          (fun _ => [false], fun h => absurd h (by decide), ())) = [[true], [false]] :=
  (Schedule.receivedWords_append _ _ _ _ _).trans (by decide)

/-- Two parties as the parties `0` and `2` of three. -/
abbrev outerParties : Fin 2 ↪ Fin 3 := ⟨![0, 2], by decide⟩

/-- In a ping-pong lifted to the parties `0` and `2` of three, party `2` receives the words of
slot `1`. -/
example (recv : (t : Fin 2) → pingPong.Received t) :
    Schedule.receivedWords (i := 2) (pingPong.map (Round.embed outerParties))
        (Schedule.MessageEncodings.embed outerParties pingPong (encBits, encBits, ()))
        (Composition.pushScheduleReceived outerParties pingPong recv 2) =
      Schedule.receivedWords pingPong (encBits, encBits, ()) (recv 1) :=
  Schedule.receivedWords_embed outerParties 1 pingPong _ recv

/-- Party `1` of three takes no part in the lifted ping-pong and receives no word, whatever its
received transcript. -/
example (r : Schedule.Received (pingPong.map (Round.embed outerParties)) 1) :
    Schedule.receivedWords (pingPong.map (Round.embed outerParties))
        (Schedule.MessageEncodings.embed outerParties pingPong (encBits, encBits, ())) r = [] :=
  Schedule.receivedWords_embed_of_forall_ne outerParties (by decide) pingPong _ r

/-! ### The encoding of the plain-model family -/

variable {Fn : Type} (Gs : Scheme Fn) (F : PrimeOrderGroupFamily)
  (H : F.Desc × List Bool → List Bool) (c : ℕ → Yao.Params Gs)

/-- The first received word of the evaluator is the encoded garbler's message, for every number of
transfers. -/
example (n : ℕ) (d : F.Desc)
    (v : PartyView ((Yao.kdfDDHProbFamily Gs F H c).In n d)
      ((Yao.kdfDDHProbFamily Gs F H c).Coins n d) ((Yao.kdfDDHProbFamily Gs F H c).sc n d) 1) :
    (Yao.kdfDDHProbViewWords Gs F H c n d 1 v).received.head? =
      some (Yao.encMessage (v.received.1 rfl)) :=
  rfl

/-- The input word of a view is the word of the party's input bits. -/
example (n : ℕ) (d : F.Desc)
    (v : PartyView ((Yao.kdfDDHProbFamily Gs F H c).In n d)
      ((Yao.kdfDDHProbFamily Gs F H c).Coins n d) ((Yao.kdfDDHProbFamily Gs F H c).sc n d) 0) :
    (Yao.kdfDDHProbViewWords Gs F H c n d 0 v).input = List.ofFn v.input :=
  rfl

/-- **The encoded view words distinguish different views**, for each party. -/
example (n : ℕ) (d : F.Desc) (i : Fin 2)
    (v v' : PartyView ((Yao.kdfDDHProbFamily Gs F H c).In n d)
      ((Yao.kdfDDHProbFamily Gs F H c).Coins n d) ((Yao.kdfDDHProbFamily Gs F H c).sc n d) i)
    (h : v ≠ v') :
    (Yao.kdfDDHProbEncoding Gs F H c).view.enc i
        ((Yao.kdfDDHProbEncoding Gs F H c).view.rep n d i v) ≠
      (Yao.kdfDDHProbEncoding Gs F H c).view.enc i
        ((Yao.kdfDDHProbEncoding Gs F H c).view.rep n d i v') :=
  fun h' => h (((Yao.kdfDDHProbEncoding Gs F H c).view.rep n d i).injective
    (((Yao.kdfDDHProbEncoding Gs F H c).view.enc i).injective h'))

/-- The public parameters are written by the group family's own encoding. -/
example : (Yao.kdfDDHProbEncoding Gs F H c).desc = F.encDesc :=
  rfl

/-- `Environment.IsPPT` is a statement over the encoding, for each corrupted party. Not proved. -/
example (i : Fin 2) (Z : Environment (Yao.kdfDDHProbFamily Gs F H c) {i}) : Prop :=
  Z.IsPPT (Yao.kdfDDHProbEncoding Gs F H c)

/-- `SimulatorFamily.IsPPT` of the composed simulator family is a statement over the encoding, at
the coalitions `{1}` (corrupted evaluator) and `{0}` (corrupted garbler). Not proved. -/
example
    (T₁ : (n : ℕ) → (I : Finset (Fin 2)) →
      CoalitionSimulator (Yao.schedule (c n)) (Yao.Input (c n)) Yao.Coins (fun _ => List Bool) I)
    (Sm : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (S₂ : (n : ℕ) → (d : F.Desc) → (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J) : Prop :=
  (Yao.kdfDDHProbSim F H c T₁ Sm S₂ {1}).IsPPT (Yao.kdfDDHProbEncoding Gs F H c) ∧
    (Yao.kdfDDHProbSim F H c T₁ Sm S₂ {0}).IsPPT (Yao.kdfDDHProbEncoding Gs F H c)

/-- `ProtocolFamily.SemiHonestSecure` for the encoding asks for a simulator family that is PPT for
it and indistinguishability against the environments that are PPT for it. Not proved. -/
example (setup : ℕ → PMF F.Desc) (I : Finset (Fin 2)) :
    (Yao.kdfDDHProbFamily Gs F H c).SemiHonestSecure setup I (Yao.kdfDDHProbEncoding Gs F H c) ↔
      ∃ S : SimulatorFamily (Yao.kdfDDHProbFamily Gs F H c) I,
        S.IsPPT (Yao.kdfDDHProbEncoding Gs F H c) ∧
          Game.Indistinguishable ((Yao.kdfDDHProbFamily Gs F H c).realGame setup I)
            ((Yao.kdfDDHProbFamily Gs F H c).idealGame setup I S)
            (Environment.IsPPT (Yao.kdfDDHProbEncoding Gs F H c)) :=
  Iff.rfl

end CslibFrontierTests.Crypto.YaoPlainEncoding
