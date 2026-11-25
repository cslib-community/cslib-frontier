/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition

/-!
# The length of the tokens offered in the oblivious transfer of Yao's protocol

In `Yao.protocol G n c` the garbler offers, in each transfer of the one batched oblivious transfer,
the two tokens of one of the evaluator's input bits (`Yao.transferQueries n c x r 0`). They are
rows of the encoding information `e` of its garbling, each `|e| / (2 * G.inLen c.fn)` bits
(`Garbling.projectiveToken`). So the offered words all have `L` bits when `e` has
`2 * G.inLen c.fn * L` bits, which is a property of the garbling scheme alone:
`Garbling.Scheme.HasTokenLength`.

A transfer subprotocol on words masks messages of one length, so the plain-model statements over
such a subprotocol ask that the offered words have that length. This file derives the condition
from the garbling scheme.

Everything here is original bookkeeping, a step towards the plain-model statement of Theorem 7 of
Lindell and Pinkas [LindellPinkas2009] (#6045, criterion 2), not a cited statement.

## Main definitions

* `Cslib.Crypto.Garbling.Scheme.HasTokenLength`: the encoding information that the scheme outputs
  at a parameter for a function has two tokens of `L` bits for each input bit.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.length_transferQueries_garbler`: over a scheme with tokens of `L`
  bits, both words that the garbler offers in every transfer have `L` bits, for all coins that the
  protocol can draw.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Garbling.Scheme

variable {Fn : Type}

/-- The garbling scheme `G` has **tokens of `L` bits** at the parameter `k` for the function `f`:
the encoding information `e` of every `(F, e, d)` that `G.garble k f` can output has
`2 * G.inLen f * L` bits. In the layout of `projectiveEncode`, where `e` is cut into `2 * G.inLen f`
rows of `|e| / (2 * G.inLen f)` bits, these are two tokens of `L` bits for each input bit. For a
function with no input bit it says that `e` is empty, for every `L`.

Original bookkeeping for the plain-model composition of Yao's protocol (#6045), not a notion of
[BellareHoangRogaway2012], whose length condition (`Scheme.LengthCondition`) fixes no width. -/
@[expose] def HasTokenLength (G : Scheme Fn) (k : ℕ) (f : Fn) (L : ℕ) : Prop :=
  ∀ g ∈ (ProbComp.eval (G.garble k f)).support, g.encInfo.length = 2 * G.inLen f * L

end Cslib.Crypto.Garbling.Scheme

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib.Crypto.Garbling

variable {Fn : Type} {G : Scheme Fn}

/-- **The garbler offers words of the scheme's token length.** Over a garbling scheme with tokens
of `L` bits at the parameter `n` for `c.fn` (`Scheme.HasTokenLength`), both words that the garbler
offers in every transfer of the batched oblivious transfer of `Yao.protocol G n c`
(`Yao.transferQueries n c x r 0`) have `L` bits, on all inputs `x` and for all coins `r` that the
protocol can draw. Nothing is assumed about the encoding or the correctness of `G`: the offered
words are rows of the encoding information by the definition of `Yao.garblerOffer`.

This is the length hypothesis of `Yao.forallChallenge_protocol_evaluator`. Original bookkeeping, a
step towards the plain-model statement of Theorem 7 of [LindellPinkas2009] (#6045, criterion 2),
not a cited statement. -/
theorem length_transferQueries_garbler {n : ℕ} {c : Params G} {L : ℕ}
    (hG : G.HasTokenLength n c.fn L) (x : (i : Fin 2) → Input c i) (r : (i : Fin 2) → Coins i)
    (hr : r ∈ (ProbComp.eval (OracleComp.pi (protocol G n c).sampleCoins)).support)
    (t : Fin c.evaluatorLen) (b : Bool) :
    (transferQueries n c x r 0 t b).length = L := by
  have hmem : (r 0 : List Bool) ∈
      (ProbComp.eval (BitString.sampleList (G.coins n c.fn))).support :=
    (ProbComp.mem_support_pi_iff _ r).mp hr 0
  rw [BitString.eval_sampleList] at hmem
  have hcoins : (r 0 : List Bool).length = G.coins n c.fn :=
    BitString.mem_support_uniformList_iff.mp hmem
  have he := hG _ (G.mem_support_eval_garble_iff.mpr ⟨r 0, hcoins, rfl⟩)
  have hpos : 0 < 2 * G.inLen c.fn := by
    have ht : (t : ℕ) < G.inLen c.fn - c.garblerLen := t.isLt
    omega
  change (projectiveToken (G.gb n c.fn (r 0)).encInfo (G.inLen c.fn) (c.garblerLen + t) b).length
    = L
  rw [projectiveToken, BitString.length_listRow, he, Nat.mul_div_cancel_left L hpos]

end Cslib.Crypto.Protocols.MPC.Yao
