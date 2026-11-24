/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.ViewEncoding
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.Games

/-!
# A machine encoding of Yao's protocol in the plain model

This module is a step towards the plain-model statement of Theorem 7 of Lindell and Pinkas
[LindellPinkas2009] (#6045, criterion 2), not that theorem. It provides definitions only: a
`ProtocolFamily.Encoding` of the plain-model family `Yao.kdfDDHProbFamily Gs F H c`, injective by
construction, so that `Environment.IsPPT`, `SimulatorFamily.IsPPT` and
`ProtocolFamily.SemiHonestSecure` can be stated for it. **No PPT certificate and no
`ProtocolFamily.SemiHonestSecure` theorem is proved here**: no simulator or environment is shown to
be efficient for this encoding and no hardness assumption is applied (#6045, criterion 2 stays
open).

## The encoding

`Yao.kdfDDHProbEncoding Gs F H c` writes

* the public parameters, a group description of `F`, by `F.encDesc`;
* each party's input as the word of its bits and each output verbatim, as `Yao.inputEncoding` and
  `Yao.outputEncoding` do for the oblivious-transfer hybrid family;
* each party's view as the record `Yao.PlainViewWords` of its input word, the word of its coins
  (`Yao.kdfDDHProbCoinsEnc`) and the words of the messages it receives, in the order of the rounds
  (`Schedule.receivedWords` with `Yao.kdfDDHProbMessageEncodings`).

The view of the four-level composed schedule is not decomposed by hand: the received messages and
the composed coins are encoded by the generic word encodings of
`CslibFrontier/Crypto/Protocols/MPC/Composition/ViewEncoding.lean` (`Schedule.receivedWords`,
`Schedule.encComposedCoins`), from word encodings of the message types and of the coins of each
level.

## Limitations

* The function descriptions `c n` are a parameter of `Yao.kdfDDHProbFamily` and not part of its
  public parameters, so no machine reads them: `desc` writes the group description only.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Yao.PlainViewWords`,
  `Cslib.Crypto.Protocols.MPC.Yao.encPlainViewWords`: the words of a view and their encoding.
* `Cslib.Crypto.Protocols.MPC.Yao.kdfDDHProbEncoding`: the encoding of the plain-model family.

## References

* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Turing.MultiTapeTM

variable {Fn : Type}

/-! ### The encoding of the plain-model family -/

/-- The encoding of the garbler's message: the garbled function, the tokens of the garbler's bits
and the decoding information in turn, all but the last framed. -/
enc_structure encMessage : Message where
  fn : encBits, labels : (encList encBits), decInfo : encBits

/-- The words of a party's view in the plain-model protocol `Yao.kdfDDHProbFamily`: its input bits,
the word of its coins and the words of the messages it receives. -/
structure PlainViewWords where
  /-- The party's input bits. -/
  input : List Bool
  /-- The word of the party's coins (`Yao.kdfDDHProbCoinsEnc`). -/
  coins : List Bool
  /-- The words of the messages that the party receives, in the order of the rounds. -/
  received : List (List Bool)

/-- The encoding of a party's view words: `input` and `coins` framed, then the list of the received
words. -/
enc_structure encPlainViewWords : PlainViewWords where
  input : encBits, coins : encBits, received : (encList encBits)

/-- The word encodings of the messages of `k` sequential transfers, each run by a protocol with
the schedule `sc`: those of `sc` for each transfer, in order. -/
@[expose] def seqBatchOTMessageEncodings {spec₂ : MultiOracleSpec} {M : Type}
    {sc : Schedule 2 spec₂} (e : sc.MessageEncodings) :
    (k : ℕ) → Schedule.MessageEncodings
      (Schedule.compose (fun _ => sc) (seqBatchOTSchedule k M))
  | 0 => ()
  | k + 1 => Schedule.MessageEncodings.append _ (Schedule.MessageEncodings.embed _ _ e)
      (seqBatchOTMessageEncodings e k)

/-- The word encodings of the messages of `Yao.kdfDDHProbFamily Gs F H c` at `n` and `d`, in the
order of the rounds, with a group element written as its `F.encode d` word:

* the garbler's message by `encMessage`;
* for each of the `(c n).evaluatorLen` transfers, the three messages of the DDH transfer (a group
  element; a pair of group elements by `encPair`; the two ciphertexts, each a pair of group
  elements, by `encPair` of the two pair encodings) and the two masked words by
  `encPair encBits encBits`;
* the output that the evaluator returns, verbatim. -/
@[expose] noncomputable def kdfDDHProbMessageEncodings (Gs : Scheme Fn)
    (F : PrimeOrderGroupFamily) (H : F.Desc × List Bool → List Bool) (c : ℕ → Params Gs) (n : ℕ)
    (d : F.Desc) : ((kdfDDHProbFamily Gs F H c).sc n d).MessageEncodings :=
  let g : F.Carrier d ↪ List Bool := ⟨F.encode d, F.encode_injective d⟩
  (encMessage,
    Schedule.MessageEncodings.append _
      (Schedule.MessageEncodings.embed _ _
        (seqBatchOTMessageEncodings
          (sc := Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
            (maskedOTSchedule (F.Carrier d) (List Bool)))
          (g, encPair g g, encPair (encPair g g) (encPair g g), encPair encBits encBits, ())
          (c n).evaluatorLen))
      (encBits, ()))

/-- The word of party `i`'s coins in `Yao.kdfDDHProbFamily Gs F H c` at `n` and `d`, by
`Schedule.encComposedCoins` at each of the three compositions:

* Yao's protocol: the garbler's coin string verbatim, the empty word for the evaluator, then the
  one word of the party's coins for the batched transfer;
* the batched transfer: the empty word, then one word for each of the `(c n).evaluatorLen`
  transfers;
* a masked transfer: the sender's two pads as a pair of `F.encode d` words (`encPair`), the empty
  word for the receiver, then the one word of the party's coins for the DDH transfer, which is
  `encDDHOTSenderBitCoins` of the sender's five bit strings and the receiver's bit string
  verbatim. -/
@[expose] noncomputable def kdfDDHProbCoinsEnc (Gs : Scheme Fn) (F : PrimeOrderGroupFamily)
    (H : F.Desc × List Bool → List Bool) (c : ℕ → Params Gs) (n : ℕ) (d : F.Desc) (i : Fin 2) :
    (kdfDDHProbFamily Gs F H c).Coins n d i ↪ List Bool :=
  let g : F.Carrier d ↪ List Bool := ⟨F.encode d, F.encode_injective d⟩
  Schedule.encComposedCoins (Coins₁ := Coins)
    (Fin.cases (motive := fun i => Coins i ↪ List Bool) encBits (fun _ => encUnit) i)
    fun _ _ => Schedule.encComposedCoins (Coins₁ := fun _ => Unit) encUnit
      fun _ (s : Fin 2) => Schedule.encComposedCoins (Coins₁ := MaskedOTCoins (F.Carrier d))
        (Fin.cases (motive := fun s => MaskedOTCoins (F.Carrier d) s ↪ List Bool) (encPair g g)
          (fun _ => encUnit) s)
        fun _ (s : Fin 2) => Fin.cases
          (motive := fun s => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool) s ↪ List Bool)
          encDDHOTSenderBitCoins (fun _ => encBits) s

/-- The words of party `i`'s view in `Yao.kdfDDHProbFamily Gs F H c` at `n` and `d`: its input
bits (`Yao.inputEncoding`), the word of its coins (`Yao.kdfDDHProbCoinsEnc`) and the words of the
messages it receives (`Schedule.receivedWords` with `Yao.kdfDDHProbMessageEncodings`). The words
determine the view. -/
@[expose] noncomputable def kdfDDHProbViewWords (Gs : Scheme Fn) (F : PrimeOrderGroupFamily)
    (H : F.Desc × List Bool → List Bool) (c : ℕ → Params Gs) (n : ℕ) (d : F.Desc) (i : Fin 2) :
    PartyView ((kdfDDHProbFamily Gs F H c).In n d) ((kdfDDHProbFamily Gs F H c).Coins n d)
      ((kdfDDHProbFamily Gs F H c).sc n d) i ↪ PlainViewWords where
  toFun view :=
    { input := (inputEncoding Gs).rep n (c n) i view.input
      coins := kdfDDHProbCoinsEnc Gs F H c n d i view.coins
      received := Schedule.receivedWords _ (kdfDDHProbMessageEncodings Gs F H c n d)
        view.received }
  inj' v v' h := by
    obtain ⟨h₁, h₂, h₃⟩ := PlainViewWords.mk.inj h
    exact PartyView.ext (((inputEncoding Gs).rep n (c n) i).injective h₁)
      ((kdfDDHProbCoinsEnc Gs F H c n d i).injective h₂)
      (Schedule.receivedWords_injective _ _ h₃)

/-- **The encoding of the plain-model family** `Yao.kdfDDHProbFamily Gs F H c` for machines. The
public parameters, a group description of `F`, are written by `F.encDesc`; the function
descriptions `c n` are not public parameters of the family and are not written. Each party's input
is the word of its bits and each output is itself, as in `Yao.inputEncoding` and
`Yao.outputEncoding`. Each party's view is its view words `Yao.kdfDDHProbViewWords`, encoded by
`encPlainViewWords`. Only the encoding is defined: nothing is shown to be efficient for it. -/
@[expose] noncomputable def kdfDDHProbEncoding (Gs : Scheme Fn) (F : PrimeOrderGroupFamily)
    (H : F.Desc × List Bool → List Bool) (c : ℕ → Params Gs) :
    (kdfDDHProbFamily Gs F H c).Encoding where
  desc := F.encDesc
  input :=
    { Rep := (inputEncoding Gs).Rep
      enc := (inputEncoding Gs).enc
      rep := fun n _ => (inputEncoding Gs).rep n (c n) }
  output :=
    { Rep := (outputEncoding Gs).Rep
      enc := (outputEncoding Gs).enc
      rep := fun n _ => (outputEncoding Gs).rep n (c n) }
  view :=
    { Rep := fun _ => PlainViewWords
      enc := fun _ => encPlainViewWords
      rep := kdfDDHProbViewWords Gs F H c }

end Cslib.Crypto.Protocols.MPC.Yao
