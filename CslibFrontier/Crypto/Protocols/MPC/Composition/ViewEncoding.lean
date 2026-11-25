/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Crypto.Protocols.MPC.Composition

/-!
# Word encodings of the views of composed protocols

This module provides word encodings of the two parts of a party's view that protocol composition
(`Schedule.compose`, `Schedule.ComposedCoins`) builds, for use in the `ProtocolFamily.Encoding` of
a composed protocol, with their structural laws. Nothing here is shown to be computable in
polynomial time, and no efficiency or security statement is made.

* **Received messages.** `Schedule.MessageEncodings sc` holds an embedding into words of the
  message type of each round of a schedule without oracle rounds, as the schedule of a protocol in
  the plain model is. `Schedule.MessageEncodings.append` and `Schedule.MessageEncodings.embed`
  build it along `++` and `Round.embed`, the operations of `Schedule.compose`.
  `Schedule.receivedWords` lists the words of the messages addressed to a party, in the order of
  the rounds.
* **Composed coins.** `Schedule.subCoinsWords` lists the words of a party's coins for the
  subprotocol calls along an outer schedule, and `Schedule.encComposedCoins` is the word of its
  `Schedule.ComposedCoins`.

The first property is injectivity: the words determine the received messages
(`Schedule.receivedWords_injective`) and the coins for the subprotocol calls
(`Schedule.subCoinsWords_injective`), which makes `Schedule.encComposedCoins` an embedding.
`CslibFrontier/Crypto/Protocols/MPC/Yao/PlainDDHOT/Encoding.lean` uses them for Yao's protocol in
the plain model.

The received words follow the two operations of `Schedule.compose`: along `sc₁ ++ sc₂` they are
the words along `sc₁` followed by the words along `sc₂` (`Schedule.receivedWords_append`), and
along a schedule lifted by `Round.embed parties` the party `parties s` receives the words of slot
`s` (`Schedule.receivedWords_embed`) and a party outside the embedding receives none
(`Schedule.receivedWords_embed_of_forall_ne`). So the received words of a composed run are the
received words of its parts in the order of the rounds, which is what a machine that writes a view
round by round produces. No such machine is built here, and the coin words have no such laws yet.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Schedule.MessageEncodings`,
  `Cslib.Crypto.Protocols.MPC.Schedule.receivedWords`: the words of the messages that a party
  receives along a schedule without oracle rounds.
* `Cslib.Crypto.Protocols.MPC.Schedule.subCoinsWords`,
  `Cslib.Crypto.Protocols.MPC.Schedule.encComposedCoins`: the word of a party's coins in a composed
  protocol.

## Main results

* `Cslib.Crypto.Protocols.MPC.Schedule.receivedWords_injective`,
  `Cslib.Crypto.Protocols.MPC.Schedule.subCoinsWords_injective`: the words determine the values.
* `Cslib.Crypto.Protocols.MPC.Schedule.receivedWords_append`,
  `Cslib.Crypto.Protocols.MPC.Schedule.receivedWords_embed`,
  `Cslib.Crypto.Protocols.MPC.Schedule.receivedWords_embed_of_forall_ne`: the received words along
  `++` and `Round.embed`.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Turing.MultiTapeTM

variable {m : ℕ} {spec : MultiOracleSpec}

/-! ### Words of the messages received along a schedule without oracle rounds -/

/-- Word encodings of the messages of a schedule without oracle rounds: an embedding into words of
the message type of each round, in the order of the rounds. A schedule with an oracle round has
none. -/
@[expose, reducible] def Schedule.MessageEncodings : Schedule m spec → Type
  | [] => Unit
  | .message _ _ Msg :: rest => (Msg ↪ List Bool) × Schedule.MessageEncodings rest
  | .oracle _ _ :: _ => Empty

/-- The word encodings of the messages of `sc₁ ++ sc₂`: those of `sc₁`, then those of `sc₂`. -/
@[expose] def Schedule.MessageEncodings.append {sc₂ : Schedule m spec} :
    (sc₁ : Schedule m spec) → sc₁.MessageEncodings → sc₂.MessageEncodings →
      Schedule.MessageEncodings (sc₁ ++ sc₂)
  | [], _, e₂ => e₂
  | .message _ _ _ :: rest, e, e₂ => (e.1, Schedule.MessageEncodings.append rest e.2 e₂)
  | .oracle _ _ :: _, e, _ => Empty.elim e

/-- The word encodings of the messages of a schedule lifted along a party embedding: the message
types are those of the schedule. -/
@[expose] def Schedule.MessageEncodings.embed {k : ℕ} (parties : Fin k ↪ Fin m) :
    (sc : Schedule k spec) → sc.MessageEncodings →
      Schedule.MessageEncodings (sc.map (Round.embed parties))
  | [], _ => ()
  | .message _ _ _ :: rest, e => (e.1, Schedule.MessageEncodings.embed parties rest e.2)
  | .oracle _ _ :: _, e => Empty.elim e

/-- The words of the messages that party `i` receives along a schedule without oracle rounds, in
the order of the rounds: the word of each message addressed to `i`, and nothing for a round
addressed to another party. -/
@[expose] def Schedule.receivedWords {i : Fin m} :
    (sc : Schedule m spec) → sc.MessageEncodings → sc.Received i → List (List Bool)
  | [], _, _ => []
  | .message _ receiver _ :: rest, e, r =>
    if h : i = receiver then e.1 (r.1 h) :: Schedule.receivedWords rest e.2 r.2
    else Schedule.receivedWords rest e.2 r.2
  | .oracle _ _ :: _, e, _ => Empty.elim e

/-- The words of the received messages determine them. -/
theorem Schedule.receivedWords_injective {i : Fin m} :
    (sc : Schedule m spec) → (e : sc.MessageEncodings) →
      Function.Injective (Schedule.receivedWords (i := i) sc e)
  | [], _ => fun _ _ _ => rfl
  | .message _ receiver _ :: rest, e => by
    intro r r' h
    by_cases hi : i = receiver
    · simp only [Schedule.receivedWords, dite_eq_left hi, List.cons.injEq] at h
      exact Prod.ext (Round.received_message_ext fun _ => e.1.injective h.1)
        (Schedule.receivedWords_injective rest e.2 h.2)
    · simp only [Schedule.receivedWords, dite_eq_right hi] at h
      exact Prod.ext (Round.received_message_eq_of_ne hi _ _)
        (Schedule.receivedWords_injective rest e.2 h)
  | .oracle _ _ :: _, e => Empty.elim e

/-- **The words received along `sc₁ ++ sc₂`** are the words received along `sc₁` followed by the
words received along `sc₂`: a run adds one word at the end for each message it delivers. -/
theorem Schedule.receivedWords_append {i : Fin m} {sc₂ : Schedule m spec} :
    (sc₁ : Schedule m spec) → (e₁ : sc₁.MessageEncodings) → (e₂ : sc₂.MessageEncodings) →
      (r₁ : sc₁.Received i) → (r₂ : sc₂.Received i) →
      Schedule.receivedWords (sc₁ ++ sc₂) (Schedule.MessageEncodings.append sc₁ e₁ e₂)
          (Schedule.Received.append r₁ r₂) =
        Schedule.receivedWords sc₁ e₁ r₁ ++ Schedule.receivedWords sc₂ e₂ r₂
  | [], _, _, _, _ => rfl
  | .message _ receiver _ :: rest, e₁, e₂, r₁, r₂ => by
    have ih := Schedule.receivedWords_append (i := i) rest e₁.2 e₂ r₁.2 r₂
    by_cases hi : i = receiver
    · simp only [List.cons_append, Schedule.receivedWords, Schedule.MessageEncodings.append,
        Schedule.Received.append, dite_eq_left hi, ih]
    · simp only [List.cons_append, Schedule.receivedWords, Schedule.MessageEncodings.append,
        Schedule.Received.append, dite_eq_right hi, ih]
  | .oracle _ _ :: _, e₁, _, _, _ => Empty.elim e₁

/-- **Lifting a schedule along a party embedding keeps the received words**: in
`sc.map (Round.embed parties)`, party `parties s` receives the words that slot `s` receives along
`sc`. -/
theorem Schedule.receivedWords_embed {k : ℕ} (parties : Fin k ↪ Fin m) (s : Fin k) :
    (sc : Schedule k spec) → (e : sc.MessageEncodings) → (recv : (t : Fin k) → sc.Received t) →
      Schedule.receivedWords (i := parties s) (sc.map (Round.embed parties))
          (Schedule.MessageEncodings.embed parties sc e)
          (Composition.pushScheduleReceived parties sc recv (parties s)) =
        Schedule.receivedWords sc e (recv s)
  | [], _, _ => rfl
  | .message _ receiver _ :: rest, e, recv => by
    have ih := Schedule.receivedWords_embed parties s rest e.2 fun t => (recv t).2
    by_cases hs : s = receiver
    · subst hs
      refine (dite_eq_left rfl).trans ?_
      simp only [Schedule.receivedWords, dite_true]
      exact congrArg (_ :: ·) ih
    · have hne : parties s ≠ parties receiver := fun h => hs (parties.injective h)
      refine (dite_eq_right hne).trans (ih.trans ?_)
      simp only [Schedule.receivedWords, dite_eq_right hs]
  | .oracle _ _ :: _, e, _ => Empty.elim e

/-- A party that fills no slot of a party embedding receives no word along a lifted schedule. -/
theorem Schedule.receivedWords_embed_of_forall_ne {k : ℕ} (parties : Fin k ↪ Fin m) {i : Fin m}
    (hi : ∀ s, parties s ≠ i) :
    (sc : Schedule k spec) → (e : sc.MessageEncodings) →
      (r : Schedule.Received (sc.map (Round.embed parties)) i) →
      Schedule.receivedWords (sc.map (Round.embed parties))
        (Schedule.MessageEncodings.embed parties sc e) r = []
  | [], _, _ => rfl
  | .message _ receiver _ :: rest, e, r => by
    have ih := Schedule.receivedWords_embed_of_forall_ne parties hi rest e.2 r.2
    have hne : i ≠ parties receiver := fun h => hi receiver h.symm
    exact (dite_eq_right hne).trans ih
  | .oracle _ _ :: _, e, _ => Empty.elim e

/-! ### Words of the coins of a composed protocol -/

/-- Equal lists `filterMap f l ++ t` for functions that are defined exactly on `p` have equal
values on `p` and equal tails. -/
private theorem filterMap_dite_append_inj {α β : Type} {p : α → Prop} [DecidablePred p]
    {f g : (a : α) → p a → β} {t t' : List β} :
    (l : List α) →
      l.filterMap (fun a => if ha : p a then some (f a ha) else none) ++ t =
        l.filterMap (fun a => if ha : p a then some (g a ha) else none) ++ t' →
      (∀ a ∈ l, ∀ ha : p a, f a ha = g a ha) ∧ t = t'
  | [], h => ⟨fun _ ha => absurd ha List.not_mem_nil, h⟩
  | a :: l, h => by
    by_cases ha : p a
    · simp only [List.filterMap_cons, dite_eq_left ha, List.cons_append, List.cons.injEq] at h
      obtain ⟨ih, ht⟩ := filterMap_dite_append_inj l h.2
      exact ⟨List.forall_mem_cons.mpr ⟨fun _ => h.1, ih⟩, ht⟩
    · simp only [List.filterMap_cons, dite_eq_right ha] at h
      obtain ⟨ih, ht⟩ := filterMap_dite_append_inj l h
      exact ⟨List.forall_mem_cons.mpr ⟨fun ha' => absurd ha' ha, ih⟩, ht⟩

variable {spec₁ : MultiOracleSpec} {Coins₂ : (op : spec₁.Op) → Fin (spec₁.arity op) → Type}

/-- The words of the coins that party `i` holds for the subprotocol calls along `sc₁`, in the order
of the oracle rounds: for each call, the word of the coins of each slot that party `i` fills, and
nothing for a call in which it takes no part. -/
@[expose] def Schedule.subCoinsWords
    (e : (op : spec₁.Op) → (s : Fin (spec₁.arity op)) → Coins₂ op s ↪ List Bool) {i : Fin m} :
    (sc₁ : Schedule m spec₁) → Schedule.SubCoins Coins₂ sc₁ i → List (List Bool)
  | [], _ => []
  | .message _ _ _ :: rest, c => Schedule.subCoinsWords e rest c
  | .oracle op parties :: rest, c =>
    (List.finRange (spec₁.arity op)).filterMap
        (fun s => if h : parties s = i then some (e op s (c.1 s h)) else none) ++
      Schedule.subCoinsWords e rest c.2

/-- The words of the coins for the subprotocol calls determine them. -/
theorem Schedule.subCoinsWords_injective
    (e : (op : spec₁.Op) → (s : Fin (spec₁.arity op)) → Coins₂ op s ↪ List Bool) {i : Fin m} :
    (sc₁ : Schedule m spec₁) → Function.Injective (Schedule.subCoinsWords e (i := i) sc₁)
  | [] => fun _ _ _ => rfl
  | .message _ _ _ :: rest => Schedule.subCoinsWords_injective e rest
  | .oracle op parties :: rest => by
    intro c c' h
    obtain ⟨hs, ht⟩ := filterMap_dite_append_inj (p := fun s => parties s = i)
      (f := fun s h => e op s (c.1 s h)) (g := fun s h => e op s (c'.1 s h)) _ h
    exact Prod.ext
      (funext fun s => funext fun h => (e op s).injective (hs s (List.mem_finRange s) h))
      (Schedule.subCoinsWords_injective e rest ht)

/-- The word of party `i`'s coins in a composed protocol (`Schedule.ComposedCoins`): the word `e₁`
of its outer coins, framed, then the list (`encList encBits`) of the words of its coins for the
subprotocol calls (`Schedule.subCoinsWords e₂`), one word for each call in which it takes part. -/
@[expose] def Schedule.encComposedCoins {Coins₁ : Fin m → Type} {sc₁ : Schedule m spec₁}
    {i : Fin m} (e₁ : Coins₁ i ↪ List Bool)
    (e₂ : (op : spec₁.Op) → (s : Fin (spec₁.arity op)) → Coins₂ op s ↪ List Bool) :
    Schedule.ComposedCoins Coins₂ Coins₁ sc₁ i ↪ List Bool where
  toFun c := encPair encBits (encList encBits) (e₁ c.1, Schedule.subCoinsWords e₂ sc₁ c.2)
  inj' c c' h := by
    obtain ⟨h₁, h₂⟩ := Prod.ext_iff.mp ((encPair encBits (encList encBits)).injective h)
    exact Prod.ext (e₁.injective h₁) (Schedule.subCoinsWords_injective e₂ sc₁ h₂)

end Cslib.Crypto.Protocols.MPC
