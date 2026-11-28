/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition.HybridChallenge
public import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition

/-!
# The one oracle round of Yao's hybrid protocol

`Yao.protocol G n c` has one oracle round: the batched oblivious transfer, called once after the
garbler's message with the query tuple `Yao.transferQueries n c x r`. So a predicate on the
operation, the corrupted slots and the queries of every oracle round reachable along its steps
(`Composition.ForallChallenge`) is that predicate at this one round. For a corrupted evaluator the
corrupted slots of the transfer are again `{1}`, the receiver.

Everything here is original bookkeeping for the hybrid argument over the oracle rounds of
`CslibFrontier/Crypto/Protocols/MPC/Composition/HybridGame.lean`, a step towards the plain-model
statement of Theorem 7 of Lindell and Pinkas [LindellPinkas2009] (#6045), not a cited statement.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.forallChallenge_protocol_iff`: a predicate holds at every oracle
  round of `Yao.protocol G n c` if and only if it holds at the batched transfer with the queries
  `Yao.transferQueries`.
* `Cslib.Crypto.Protocols.MPC.Yao.forallChallenge_protocol_evaluator`: for a corrupted evaluator,
  every oracle round has the corrupted slots `{1}` and offers words of one length, when the
  garbler's offer does.

## References

* [Y. Lindell and B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib.Crypto.Garbling

variable {Fn : Type} {G : Scheme Fn}

/-- **The only oracle round of Yao's hybrid protocol is the batched transfer.** A predicate `Q` on
the operation, the corrupted slots and the query tuple holds at every oracle round reachable along
the steps of `Yao.protocol G n c`, from the inputs `x` and the coins `r` and for the coalition `I`
(`Composition.ForallChallenge`), if and only if it holds at the one batched transfer: the slots
are the members of `I`, the garbler being the sender and the evaluator the receiver, and the
queries are `Yao.transferQueries n c x r`. Original bookkeeping, not a cited statement. -/
theorem forallChallenge_protocol_iff (n : ℕ) (c : Params G) (I : Finset (Fin 2))
    (Q : (op : (batchOTSpec c.evaluatorLen (List Bool)).Op) →
      Finset (Fin ((batchOTSpec c.evaluatorLen (List Bool)).arity op)) →
      ((s : Fin ((batchOTSpec c.evaluatorLen (List Bool)).arity op)) →
        (batchOTSpec c.evaluatorLen (List Bool)).Query op s) → Prop)
    (x : (i : Fin 2) → Input c i) (r : (i : Fin 2) → Coins i) :
    Composition.ForallChallenge I Q (protocol G n c).steps (fun i => (x i, r i)) ↔
      Q () (Composition.subCoalition (Function.Embedding.refl (Fin 2)) I)
        (transferQueries n c x r) :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ => trivial⟩⟩

/-- **The oracle round of Yao's hybrid protocol for a corrupted evaluator.** For the coalition
`{1}`, every oracle round reachable along the steps of `Yao.protocol G n c` from the inputs `x` and
the coins `r` has the corrupted slots `{1}`, the receiver of the transfer, and a sender's query
whose two words in every transfer have length `L`, when the two words that the garbler offers in
every transfer (`Yao.transferQueries n c x r 0`) have length `L`. Original bookkeeping, not a cited
statement. -/
theorem forallChallenge_protocol_evaluator (n : ℕ) (c : Params G) (L : ℕ)
    (x : (i : Fin 2) → Input c i) (r : (i : Fin 2) → Coins i)
    (hlen : ∀ (t : Fin c.evaluatorLen) (b : Bool), (transferQueries n c x r 0 t b).length = L) :
    Composition.ForallChallenge ({1} : Finset (Fin 2))
      (fun _ J q => J = ({1} : Finset (Fin 2)) ∧
        ∀ (t : Fin c.evaluatorLen) (b : Bool), (q 0 t b).length = L)
      (protocol G n c).steps (fun i => (x i, r i)) :=
  (forallChallenge_protocol_iff n c {1} _ x r).mpr
    ⟨Finset.ext fun _ => Composition.mem_subCoalition, hlen⟩

end Cslib.Crypto.Protocols.MPC.Yao
