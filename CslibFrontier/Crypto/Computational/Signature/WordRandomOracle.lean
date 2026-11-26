/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.Signature.RandomOracle.Simulation
public import CslibFrontier.Computability.Probabilistic.Oracle.ReplayParameter
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Crypto.Game
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.QueryBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.Substitution
import CslibFrontier.Crypto.Game.Forgery
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen

/-!
# Native word forgers in the typed random-oracle signature world

A native word forger is an oracle machine with two channels: channel `false` signs a word and
channel `true` hashes a word. Every hash payload is retained as a distinct query, and digest replies
use the supplied injective encoding. Signing randomness remains in the shared world, separate from
the forger's private coins. The existing total pair decoder handles arbitrary native output,
including words that are not canonical pair encodings.

`wordEufCmaGame` and `wordSufCmaGame` are the EUF-CMA and SUF-CMA games of such a forger against a
scheme whose keys, messages, signatures and hash points are words. The forger gets the public key
and signs and hashes adaptively. EUF-CMA requires a verified final message that was never signed;
SUF-CMA requires a verified final message-signature pair that was never returned by signing.
Signing, hashing and the final verification share one lazily sampled random oracle. `EUFCMA` and
`SUFCMA` are the corresponding asymptotic notions against uniform oracle-PPT forgers.

The saved-coin adapter returns the empty pair without calls on oversized public keys, and truncates
every supplied tape at the original input-dependent machine clock. Its sampling budget depends only
on the security parameter.
These are bridges between existing models, not a Schnorr security reduction.
The scheme's signer and shared oracle remain the existing typed world; this module does not
certify their native realization or the complete forking reduction.

## Main definitions

* `Cslib.Crypto.Protocols.ROMSignature.wordQuery`: exact Boolean channel routing.
* `Cslib.Crypto.Protocols.ROMSignature.routeWordProgram`: retain private sampling while routing.
* `Cslib.Crypto.Protocols.ROMSignature.wordEufCmaGame`: the EUF-CMA game of a native word forger.
* `Cslib.Crypto.Protocols.ROMSignature.wordSufCmaGame`: the SUF-CMA game of a native word forger.
* `Cslib.Crypto.Protocols.ROMSignature.EUFCMA`: EUF-CMA security in the random-oracle model
  against uniform oracle-PPT word forgers.
* `Cslib.Crypto.Protocols.ROMSignature.SUFCMA`: SUF-CMA security in the random-oracle model
  against uniform oracle-PPT word forgers.
* `Cslib.Crypto.Protocols.ROMSignature.savedCoinForger`: the existing explicit-coin forger model.
* `Cslib.Crypto.Protocols.ROMSignature.encReplayInput`: the encoding of a saved-coin replay's
  input.
* `Cslib.Crypto.Protocols.ROMSignature.RawWordSpec`: the raw channel calls of a native forger.

## Main results

* `Cslib.Crypto.Protocols.ROMSignature.isOraclePPTOn_savedWordReplay`: native efficiency of the
  full guarded, truncated and decoded replay input.
* `Cslib.Crypto.Protocols.ROMSignature.savedWordReplay_eq_interpret`: every guarded replay is the
  raw-call replay, interpreted by its channel calls.
* `Cslib.Crypto.Protocols.ROMSignature.isQueryBounded_savedWordReplay`,
  `Cslib.Crypto.Protocols.ROMSignature.callBounded_savedCoinForger`: every key and tape obey the
  parameter-only call budget, and the signing and hash budgets.
* `Cslib.Crypto.Protocols.ROMSignature.exists_savedCoinForger`: a polynomial length bound on the
  supported public keys and an actual oracle-PPT forger give a joint-state-preserving adapter.
* `Cslib.Crypto.Protocols.ROMSignature.exists_eufCmaGame_savedCoinForger`,
  `Cslib.Crypto.Protocols.ROMSignature.exists_sufCmaGame_savedCoinForger`: equality of each native
  word game and its explicit-coin typed game.

## References

Original adapters for the existing native oracle-PPT and typed ROM signature models.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.ROMSignature

open Probability OracleComp
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

variable {Digest α : Type}

/-- Route the signing channel and hash channel without decoding or identifying hash payloads. -/
def wordQuery (digestEncoding : Digest ↪ List Bool) :
    Bool → List Bool → OracleComp (ForgerSpec (List Bool) (List Bool) (List Bool) Digest)
      (List Bool)
  | false, word =>
    OracleComp.query (spec := ForgerSpec (List Bool) (List Bool) (List Bool) Digest) (.inl word)
  | true, word => digestEncoding <$>
    OracleComp.query (spec := ForgerSpec (List Bool) (List Bool) (List Bool) Digest) (.inr word)

/-- Route a native word program into the existing typed signature world, retaining its private
random sampling. Digest encodings affect replies only; all request words remain distinct. -/
def routeWordProgram (digestEncoding : Digest ↪ List Bool)
    (program : WordOracleComp Bool α) :
    ProbOracleComp (ForgerSpec (List Bool) (List Bool) (List Bool) Digest) α :=
  interpret (sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n))
    (fun request => liftOracleForger (wordQuery digestEncoding request.1 request.2))) program

/-- Routing retains the joint output and state of any typed handler. -/
theorem run_interpret_routeWordProgram (digestEncoding : Digest ↪ List Bool)
    (program : WordOracleComp Bool α) {Store : Type}
    (handler : (q : List Bool ⊕ List Bool) →
      StateT Store PMF (ForgerSpec (List Bool) (List Bool) (List Bool) Digest q)) (s : Store) :
    ProbOracleComp.runWith handler (routeWordProgram digestEncoding program) s =
      ProbOracleComp.runWith
        (fun request => interpret handler (wordQuery digestEncoding request.1 request.2))
        program s := by
  have hlift
      (p : OracleComp (ForgerSpec (List Bool) (List Bool) (List Bool) Digest) (List Bool)) :
      liftOracleForger p = OracleComp.liftRight p :=
    (OracleComp.substitute_eq_interpret _ p).symm
  simp only [routeWordProgram, hlift, runWith_norm]
  refine congrArg (ProbOracleComp.runWith · program s) ?_
  funext _ state
  exact OracleComp.runWith_eq_run_interpret handler _ state

/-- Native replay and typed routing commute as programs, before choosing any oracle world. -/
theorem routeWordProgram_runCoins {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Bool) (digestEncoding : Digest ↪ List Bool)
    (coins input : List Bool) :
    routeWordProgram digestEncoding
      (machine.runCoins (fun op word => ProbOracleComp.query (op, word)) coins input) =
    liftOracleForger (machine.runCoins (wordQuery digestEncoding) coins input) := by
  simp only [routeWordProgram, liftOracleForger, interpret_runCoins,
    ProbOracleComp.query, interpret_query, sumHandler]

/-! ### EUF-CMA and SUF-CMA games of native word forgers -/

/-- **The EUF-CMA game of a native word forger** in the random-oracle model, for a scheme whose
public keys, messages, signatures and hash points are words. The forger receives the public key,
signs words on channel `false` and hashes words on channel `true`, with digests encoded by
`digestEncoding`, and finally outputs a message and a signature. Signing, hashing and the final
verification share one lazily sampled random oracle. The forger wins when the signature verifies
and the message was never asked to be signed; repeated signing requests are allowed. This is
`eufCmaGame` for a forger given as a native program with private randomness
(`exists_eufCmaGame_savedCoinForger`). -/
noncomputable def wordEufCmaGame {SK : Type} [Fintype Digest] [Nonempty Digest]
    (digestEncoding : Digest ↪ List Bool)
    (scheme : Scheme (List Bool) SK (List Bool) (List Bool) (List Bool) Digest)
    (forger : List Bool → WordOracleComp Bool (List Bool × List Bool)) : Game :=
  worldGame scheme (fun pk => routeWordProgram digestEncoding (forger pk))
    (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg)

/-- **The SUF-CMA game of a native word forger** in the random-oracle model. It has the same
execution and shared random oracle as `wordEufCmaGame`, but the candidate wins exactly when it
verifies and its complete `(message, signature)` pair was never returned by the signing oracle.
Thus a different valid signature on a previously signed message can win, while exact replay
cannot. This is the native-program form of the existing typed `sufCmaGame`. -/
noncomputable def wordSufCmaGame {SK : Type} [Fintype Digest] [Nonempty Digest]
    (digestEncoding : Digest ↪ List Bool)
    (scheme : Scheme (List Bool) SK (List Bool) (List Bool) (List Bool) Digest)
    (forger : List Bool → WordOracleComp Bool (List Bool × List Bool)) : Game :=
  worldGame scheme (fun pk => routeWordProgram digestEncoding (forger pk))
    (fun verified msig pairs => verified && !pairs.contains msig)

/-- **Existential unforgeability under adaptive chosen-message attack in the random-oracle
model** (EUF-CMA) of a family of word-interface schemes: every uniform oracle-PPT word forger, run
on the unary security parameter and the public key, wins `wordEufCmaGame` with negligible
probability. The digest type, its encoding and the scheme may depend on the security parameter.
This is the random oracle version of [BonehShoup2023], Attack Game 13.1 and Definition 13.2
(pp. 529–530), formed as in Section 8.10.2 (p. 328) and used for full domain hash in Section 13.3
(p. 535): the challenger and the forger share one random function from words to `Digest n`,
sampled lazily, and every word is a message. Neither `ROMSignature.Scheme` nor `digestEncoding`
carries an efficiency or correctness requirement, where Definition 13.1 (pp. 528–529) asks for
efficient algorithms whose signatures verify. -/
def EUFCMA {Digest : ℕ → Type} [∀ n, Fintype (Digest n)] [∀ n, Nonempty (Digest n)] {SK : Type}
    (digestEncoding : (n : ℕ) → Digest n ↪ List Bool)
    (scheme : (n : ℕ) → Scheme (List Bool) SK (List Bool) (List Bool) (List Bool) (Digest n)) :
    Prop :=
  Game.Indistinguishable
    (fun forger n => wordEufCmaGame (digestEncoding n) (scheme n) (forger n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- **Strong existential unforgeability under adaptive chosen-message attack in the random-oracle
model** (SUF-CMA) of a family of word-interface schemes. The fresh-pair condition and negligible
success requirement are [BonehShoup2023, Attack Game 13.2 and Definition 13.3, p. 530]; this
definition specializes them to the shared classical random function described in
[BonehShoup2023, Section 8.10.2, pp. 327–329], implemented here by one lazy oracle state. Every
uniform oracle-PPT word forger wins
`wordSufCmaGame` with negligible probability. The digest type, its encoding and the scheme may
depend on the security parameter. Only the forger carries an efficiency requirement:
neither `ROMSignature.Scheme` nor `digestEncoding` certifies efficient key generation, signing,
verification or digest encoding, so this is an unforgeability property of a supplied scheme family
rather than a complete efficient-scheme package. Unlike [BonehShoup2023, Definition 13.1,
pp. 528–529], it also does not bundle correctness or finite message and signature spaces: public
keys, messages, signatures and query points are arbitrary-length words. Callers must establish
correctness and nonvacuity separately. In particular, an always-rejecting scheme can satisfy this
predicate vacuously. This is not a QROM notion. -/
def SUFCMA {Digest : ℕ → Type} [∀ n, Fintype (Digest n)] [∀ n, Nonempty (Digest n)] {SK : Type}
    (digestEncoding : (n : ℕ) → Digest n ↪ List Bool)
    (scheme : (n : ℕ) → Scheme (List Bool) SK (List Bool) (List Bool) (List Bool) (Digest n)) :
    Prop :=
  Game.Indistinguishable
    (fun forger n => wordSufCmaGame (digestEncoding n) (scheme n) (forger n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

section EUFCMA

variable {Digest : ℕ → Type} [∀ n, Fintype (Digest n)] [∀ n, Nonempty (Digest n)] {SK : Type}
  {digestEncoding : (n : ℕ) → Digest n ↪ List Bool}
  {scheme : (n : ℕ) → Scheme (List Bool) SK (List Bool) (List Bool) (List Bool) (Digest n)}

/-- EUF-CMA security gives negligible forgery probability for every oracle-PPT word forger. -/
theorem EUFCMA.negligible (h : EUFCMA digestEncoding scheme)
    (forger : ℕ → List Bool → WordOracleComp Bool (List Bool × List Bool))
    (hforger : IsOraclePPT (encPair encBits encBits) forger) :
    Negligible fun n =>
      Game.succProbability (wordEufCmaGame (digestEncoding n) (scheme n) (forger n)) :=
  Game.Indistinguishable.negligible_succProbability h forger hforger

/-- Establish EUF-CMA security by bounding every oracle-PPT word forger's success probability. -/
theorem EUFCMA.of_negligible
    (h : ∀ forger : ℕ → List Bool → WordOracleComp Bool (List Bool × List Bool),
      IsOraclePPT (encPair encBits encBits) forger →
      Negligible fun n =>
        Game.succProbability (wordEufCmaGame (digestEncoding n) (scheme n) (forger n))) :
    EUFCMA digestEncoding scheme :=
  Game.Indistinguishable.of_negligible_succProbability h

end EUFCMA

section SUFCMA

variable {Digest : ℕ → Type} [∀ n, Fintype (Digest n)] [∀ n, Nonempty (Digest n)] {SK : Type}
  {digestEncoding : (n : ℕ) → Digest n ↪ List Bool}
  {scheme : (n : ℕ) → Scheme (List Bool) SK (List Bool) (List Bool) (List Bool) (Digest n)}

/-- SUF-CMA security gives negligible fresh-pair forgery probability for every oracle-PPT word
forger. -/
theorem SUFCMA.negligible (h : SUFCMA digestEncoding scheme)
    (forger : ℕ → List Bool → WordOracleComp Bool (List Bool × List Bool))
    (hforger : IsOraclePPT (encPair encBits encBits) forger) :
    Negligible fun n =>
      Game.succProbability (wordSufCmaGame (digestEncoding n) (scheme n) (forger n)) :=
  Game.Indistinguishable.negligible_succProbability h forger hforger

/-- Establish SUF-CMA security by bounding every oracle-PPT word forger's success probability. -/
theorem SUFCMA.of_negligible
    (h : ∀ forger : ℕ → List Bool → WordOracleComp Bool (List Bool × List Bool),
      IsOraclePPT (encPair encBits encBits) forger →
      Negligible fun n =>
        Game.succProbability (wordSufCmaGame (digestEncoding n) (scheme n) (forger n))) :
    SUFCMA digestEncoding scheme :=
  Game.Indistinguishable.of_negligible_succProbability h

end SUFCMA

/-- A native word forger wins EUF-CMA with probability at most its SUF-CMA probability. Both
games use the identical key law, forger execution, signing transcript, and shared random-oracle
cache; only the final freshness test changes. -/
theorem succProbability_wordEufCmaGame_le_wordSufCmaGame {SK : Type}
    [Fintype Digest] [Nonempty Digest] (digestEncoding : Digest ↪ List Bool)
    (scheme : Scheme (List Bool) SK (List Bool) (List Bool) (List Bool) Digest)
    (forger : List Bool → WordOracleComp Bool (List Bool × List Bool)) :
    Game.succProbability (wordEufCmaGame digestEncoding scheme forger) ≤
      Game.succProbability (wordSufCmaGame digestEncoding scheme forger) := by
  apply Game.succProbability_mono
  unfold wordEufCmaGame wordSufCmaGame worldGame
  simp only [PMF.monad_bind_eq_bind]
  refine PMF.bind_apply_mono_on_support _ true fun keys _ => ?_
  rw [eval_world_worldRealize, eval_world_worldRealize]
  simp only [PMF.monad_bind_eq_bind]
  refine PMF.bind_apply_mono_on_support _ true fun ⟨⟨msig, pairs⟩, _⟩ _ =>
    PMF.bind_apply_mono_on_support _ true fun verified _ => ?_
  by_cases hmem : msig.1 ∈ pairs.map Prod.fst
  · simp [hmem]
  · have hnotPair : msig ∉ pairs := by
      simpa only [freshPair, decide_eq_true_eq] using
        freshPair_of_freshMessage (by simpa [freshMessage] using hmem)
    simp [hmem, hnotPair]

/-- Native ROM SUF-CMA security implies native ROM EUF-CMA security for the same scheme family. -/
theorem SUFCMA.eufCma {Digest : ℕ → Type} [∀ n, Fintype (Digest n)]
    [∀ n, Nonempty (Digest n)] {SK : Type}
    {digestEncoding : (n : ℕ) → Digest n ↪ List Bool}
    {scheme : (n : ℕ) → Scheme (List Bool) SK (List Bool) (List Bool) (List Bool) (Digest n)}
    (h : SUFCMA digestEncoding scheme) : EUFCMA digestEncoding scheme :=
  h.of_succProbability_le fun forger _ n =>
    succProbability_wordEufCmaGame_le_wordSufCmaGame
      (digestEncoding n) (scheme n) (forger n)

/-! ### Saved-coin replay -/

/-- Input `(1ⁿ, pk, tape)` of a saved-coin replay (`savedWordReplay`): the security parameter `n`
in unary, then the public key and the saved coin tape as bit words. The parameter and the public
key are framed. -/
abbrev encReplayInput : ℕ × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits encBits)

/-- Guard the public input, truncate the saved tape, and decode the output, with the original
external channels supplied explicitly. Malformed output uses the existing total pair decoder. -/
def savedWordReplay {k : ℕ} {Control Query : Type} {spec : OracleSpec Query}
    (machine : MultiTapePTM k Bool Control Bool)
    (query : Bool → List Bool → OracleComp spec (List Bool)) (c d keyC keyD : ℕ) :
    ℕ × List Bool × List Bool → OracleComp spec (List Bool × List Bool)
  | (n, pk, tape) =>
    if pk.length ≤ keyC * (n + 1) ^ keyD then
      (Decoder.bits.pair Decoder.bits).decode <$>
        machine.runCoins query
          (tape.take (c * ((encPair encUnary encBits (n, pk)).length + 1) ^ d))
          (encPair encUnary encBits (n, pk))
    else pure ([], [])

/-- The complete guarded, truncated, decoded replay is strict oracle-PPT in its full input,
including the security parameter, public key, and arbitrary saved tape. -/
@[fun_prop] theorem isOraclePPTOn_savedWordReplay {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Bool) (c d keyC keyD : ℕ) :
    IsOraclePPTOn encReplayInput (encPair encBits encBits)
      (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) c d keyC keyD) := by
  change IsOraclePPTOn encReplayInput (encPair encBits encBits) fun p : ℕ × List Bool × List Bool =>
    savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) c d keyC keyD
      (p.1, p.2.1, p.2.2)
  simp only [savedWordReplay]
  refine IsOraclePPTOn.ite (by fun_prop)
    (IsOraclePPTOn.map ?_ (Decoder.bits.pair Decoder.bits).computableInPolyTime) (by fun_prop)
  refine machine.isOraclePPTOn_runCoins.preprocess
    (prepare := fun p : ℕ × List Bool × List Bool =>
      (p.2.2.take (c * ((encPair encUnary encBits (p.1, p.2.1)).length + 1) ^ d),
        encPair encUnary encBits (p.1, p.2.1))) ?_
  exact (ComputableInPolyTime.bitsTakeWithInput (by fun_prop) (by fun_prop)).prod
    (ComputableInPolyTime.encoding_comp (by fun_prop))

/-- The raw calls of a native word forger: a channel bit and a request word, answered by a word. -/
abbrev RawWordSpec : OracleSpec (Bool × List Bool) := fun _ => List Bool

/-- Every guarded replay is the replay with raw calls, interpreted by its channel calls. -/
theorem savedWordReplay_eq_interpret {k : ℕ} {Control Query : Type} {spec : OracleSpec Query}
    (machine : MultiTapePTM k Bool Control Bool)
    (query : Bool → List Bool → OracleComp spec (List Bool)) (c d keyC keyD : ℕ)
    (input : ℕ × List Bool × List Bool) :
    savedWordReplay machine query c d keyC keyD input =
      interpret (fun request => query request.1 request.2)
        (savedWordReplay machine (fun op word => OracleComp.query (spec := RawWordSpec) (op, word))
          c d keyC keyD input) := by
  rcases input with ⟨n, pk, tape⟩
  simp only [savedWordReplay]
  split
  · simp [interpret_map, interpret_runCoins]
  · rfl

/-- A guarded replay whose channel calls each make at most one call makes at most
`savedCoinBudget` calls, for every public key and every saved tape. -/
theorem isQueryBounded_savedWordReplay {k : ℕ} {Control Query : Type} {spec : OracleSpec Query}
    (machine : MultiTapePTM k Bool Control Bool)
    (query : Bool → List Bool → OracleComp spec (List Bool))
    (hquery : ∀ op word, IsQueryBounded (query op word) 1) (c d keyC keyD n : ℕ)
    (pk coins : List Bool) :
    IsQueryBounded (savedWordReplay machine query c d keyC keyD (n, pk, coins))
      (savedCoinBudget c d keyC keyD n) := by
  dsimp only [savedWordReplay]
  split_ifs with hpk
  · refine (isCostBounded_map_iff _ _ _).mpr
      ((machine.isCostBounded_runCoins query 1 hquery _ _).mono ?_)
    simpa only [List.length_take, Nat.mul_one] using
      (Nat.min_le_left _ _).trans (clock_le_savedCoinBudget c d keyC keyD n hpk)
  · exact .pure _ _

/-- Use the existing total pair decoder after native replay. Oversized keys make no calls; all
coin tapes, including overlong ones outside the sampling support, are truncated before replay. -/
noncomputable def savedCoinForger {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Bool) (digestEncoding : Digest ↪ List Bool)
    (c d keyC keyD n : ℕ) :
    Forger (List Bool) (List Bool) (List Bool) (List Bool) Digest where
  Coins := List Bool
  coins := BitString.uniformList (savedCoinBudget c d keyC keyD n)
  forge pk coins := savedWordReplay machine (wordQuery digestEncoding) c d keyC keyD (n, pk, coins)

/-- The efficient native guarded replay is exactly the typed fixed-coin forger after channel
routing, including the oversized-key branch and total decoding of arbitrary output words. -/
theorem routeWordProgram_savedWordReplay {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Bool) (digestEncoding : Digest ↪ List Bool)
    (c d keyC keyD n : ℕ) (pk coins : List Bool) :
    routeWordProgram digestEncoding
      (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word))
        c d keyC keyD (n, pk, coins)) =
    liftOracleForger ((savedCoinForger machine digestEncoding c d keyC keyD n).forge pk coins) := by
  unfold savedCoinForger
  simp only [savedWordReplay]
  split
  · change interpret _ ((Decoder.bits.pair Decoder.bits).decode <$> _) = _
    rw [interpret_map]
    change _ <$> routeWordProgram digestEncoding (machine.runCoins _ _ _) = _
    simp only [routeWordProgram_runCoins, liftOracleForger, interpret_map]
  · simp only [routeWordProgram, liftOracleForger, interpret_pure]

/-- Signing and hashing each cost at most one external call in the word routing. -/
theorem isQueryBounded_wordQuery (digestEncoding : Digest ↪ List Bool) (op : Bool)
    (word : List Bool) : IsQueryBounded (wordQuery digestEncoding op word) 1 := by
  cases op with
  | false => exact IsCostBounded.query _
  | true => exact (isCostBounded_map_iff _ _ _).mpr (IsCostBounded.query _)

/-- The fixed-coin forger has uniform signing and hash budgets for every key and every tape. -/
theorem callBounded_savedCoinForger {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Bool) (digestEncoding : Digest ↪ List Bool)
    (c d keyC keyD n : ℕ) :
    (savedCoinForger machine digestEncoding c d keyC keyD n).CallBounded
      (savedCoinBudget c d keyC keyD n) (savedCoinBudget c d keyC keyD n) := by
  intro pk coins
  change List Bool at coins
  have htotal := isQueryBounded_savedWordReplay machine (wordQuery digestEncoding)
    (isQueryBounded_wordQuery digestEncoding) c d keyC keyD n pk coins
  exact ⟨htotal.of_le (fun q => by cases q <;> simp [signingCost]),
    htotal.of_le (fun q => by cases q <;> simp [hashCost])⟩

private theorem run_interpret_decode_mixture (digestEncoding : Digest ↪ List Bool)
    (program : WordOracleComp Bool (List Bool × List Bool)) (coins : PMF (List Bool))
    (replay : List Bool → WordOracleComp Bool (List Bool))
    (h : ∀ (Store : Type)
      (handler : Bool × List Bool → StateT Store PMF (List Bool)) s,
      ProbOracleComp.runWith handler (encPair encBits encBits <$> program) s =
        coins.bind (fun r => ProbOracleComp.runWith handler (replay r) s))
    (Store : Type) (handler : (q : List Bool ⊕ List Bool) →
      StateT Store PMF (ForgerSpec (List Bool) (List Bool) (List Bool) Digest q)) (s : Store) :
    ProbOracleComp.runWith handler (routeWordProgram digestEncoding program) s =
      coins.bind (fun r => ProbOracleComp.runWith handler
        ((Decoder.bits.pair Decoder.bits).decode <$>
          routeWordProgram digestEncoding (replay r)) s) := by
  have heq := congrArg (PMF.map (Prod.map (Decoder.bits.pair Decoder.bits).decode id))
    (h Store (fun request => interpret handler (wordQuery digestEncoding request.1 request.2)) s)
  simp only [PMF.map_bind, ← ProbOracleComp.runWith_map, Functor.map_map, Decoder.decode_enc,
    id_map'] at heq
  have hmap (p : WordOracleComp Bool (List Bool)) :
      (Decoder.bits.pair Decoder.bits).decode <$> routeWordProgram digestEncoding p =
        routeWordProgram digestEncoding ((Decoder.bits.pair Decoder.bits).decode <$> p) :=
    (interpret_map _ _ _).symm
  simpa only [hmap, run_interpret_routeWordProgram] using heq

/-- An actual uniform native forger has a key-independent saved-coin adapter. The key-size guard
is a polynomial bound `keyC * (n + 1) ^ keyD` on the supported public keys, which a strict-PPT key
generator supplies through `IsPPTOn.length_le`. Equality retains the complete state of every
typed signing/hash handler; in particular the handler's own randomness is not pre-sampled here. -/
theorem exists_savedCoinForger
    {gen : ℕ → ProbComp (List Bool × List Bool)} {keyC keyD : ℕ}
    (hgen : ∀ n keys, keys ∈ (ProbComp.eval (gen n)).support →
      keys.1.length ≤ keyC * (n + 1) ^ keyD)
    {program : ℕ → List Bool → WordOracleComp Bool (List Bool × List Bool)}
    (hprogram : IsOraclePPT (encPair encBits encBits) program) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Bool) (c d : ℕ),
      IsOraclePPTOn encReplayInput (encPair encBits encBits)
        (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) c d keyC keyD) ∧
      ∀ n keys, keys ∈ (ProbComp.eval (gen n)).support →
        ∀ (Digest : Type) (digestEncoding : Digest ↪ List Bool) (Store : Type)
          (handler : (q : List Bool ⊕ List Bool) →
          StateT Store PMF (ForgerSpec (List Bool) (List Bool) (List Bool) Digest q)) s,
        ProbOracleComp.runWith handler (routeWordProgram digestEncoding (program n keys.1)) s =
        (savedCoinForger machine digestEncoding c d keyC keyD n).coins.bind (fun coins =>
          ProbOracleComp.runWith handler
            (liftOracleForger
              ((savedCoinForger machine digestEncoding c d keyC keyD n).forge
                keys.1 coins)) s) := by
  obtain ⟨k, Control, hfinite, machine, c, d, _, _, hrun⟩ :=
    hprogram.exists_savedCoins_of_length_le keyC keyD
  refine ⟨k, Control, hfinite, machine, c, d,
    isOraclePPTOn_savedWordReplay machine c d keyC keyD,
    fun n keys hkeys Digest digestEncoding Store handler s => ?_⟩
  have hpk := hgen n keys hkeys
  simpa only [savedCoinForger, savedWordReplay, savedCoinBudget, ite_eq_left hpk,
    routeWordProgram_runCoins, liftOracleForger, interpret_map] using
    run_interpret_decode_mixture digestEncoding (program n keys.1) _ _
      (hrun n keys.1 hpk) Store handler s

/-- The native private-random word forger and its explicit-coin adapter give exactly the same
EUF-CMA game: `wordEufCmaGame` of the forger is `eufCmaGame` of the adapter. Signing, hash queries,
and final verification share one memoized world; freshness excludes only signing the final message,
so repeated signing queries are allowed. One native replay machine and clock work for every digest
type and encoding, which may therefore vary with the security parameter.
The supported public keys need only a polynomial length bound `keyC * (n + 1) ^ keyD`.
This bridge does not assert unforgeability or a discrete-log reduction. -/
theorem exists_eufCmaGame_savedCoinForger
    {gen : ℕ → ProbComp (List Bool × List Bool)} {keyC keyD : ℕ}
    (hgen : ∀ n keys, keys ∈ (ProbComp.eval (gen n)).support →
      keys.1.length ≤ keyC * (n + 1) ^ keyD)
    {program : ℕ → List Bool → WordOracleComp Bool (List Bool × List Bool)}
    (hprogram : IsOraclePPT (encPair encBits encBits) program) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Bool) (c d : ℕ),
      IsOraclePPTOn encReplayInput (encPair encBits encBits)
        (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) c d keyC keyD) ∧
      ∀ n (Digest : Type) [Fintype Digest] [Nonempty Digest]
        (digestEncoding : Digest ↪ List Bool)
        (scheme : Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) Digest),
        scheme.keyGen = ProbComp.eval (gen n) →
        (savedCoinForger machine digestEncoding c d keyC keyD n).CallBounded
          (savedCoinBudget c d keyC keyD n) (savedCoinBudget c d keyC keyD n) ∧
        wordEufCmaGame digestEncoding scheme (program n) =
          eufCmaGame scheme (savedCoinForger machine digestEncoding c d keyC keyD n) := by
  obtain ⟨k, Control, hfinite, machine, c, d, hefficient, hrun⟩ :=
    exists_savedCoinForger hgen hprogram
  refine ⟨k, Control, hfinite, machine, c, d, hefficient,
    fun n Digest _ _ digestEncoding scheme hgen' =>
      ⟨callBounded_savedCoinForger machine digestEncoding c d keyC keyD n, ?_⟩⟩
  rw [eufCmaGame_eq_worldGame]
  unfold wordEufCmaGame worldGame
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  rw [hgen'] at hkeys
  simpa only [PMF.monad_bind_eq_bind, show ∀ (pairs : List (List Bool × List Bool))
      (msg : List Bool),
      @List.contains (List Bool) instBEqOfDecidableEq (pairs.map Prod.fst) msg =
        (pairs.map Prod.fst).contains msg from fun _ _ => Bool.eq_iff_iff.mpr (by simp)] using
    eval_worldRealize_eq_bind scheme keys.1 keys.2 _ _ _
      (hrun n keys hkeys Digest digestEncoding)
      (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg)

/-- The native private-random word forger and its explicit-coin adapter give exactly the same
SUF-CMA game: `wordSufCmaGame` of the forger is `sufCmaGame` of the adapter. Signing, hash queries,
and final verification share one memoized world; freshness excludes the complete returned
message-signature pairs, so a different valid signature on a signed message may win while exact
replay cannot. The signing and hash call bounds remain separate components of `CallBounded`.
One replay machine and clock work for every digest type and encoding, which may vary with the
security parameter. This bridge asserts neither SUF-CMA security nor a reduction to an ML-DSA
assumption. -/
theorem exists_sufCmaGame_savedCoinForger
    {gen : ℕ → ProbComp (List Bool × List Bool)} {keyC keyD : ℕ}
    (hgen : ∀ n keys, keys ∈ (ProbComp.eval (gen n)).support →
      keys.1.length ≤ keyC * (n + 1) ^ keyD)
    {program : ℕ → List Bool → WordOracleComp Bool (List Bool × List Bool)}
    (hprogram : IsOraclePPT (encPair encBits encBits) program) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Bool) (c d : ℕ),
      IsOraclePPTOn encReplayInput (encPair encBits encBits)
        (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word)) c d keyC keyD) ∧
      ∀ n (Digest : Type) [Fintype Digest] [Nonempty Digest]
        (digestEncoding : Digest ↪ List Bool)
        (scheme : Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) Digest),
        scheme.keyGen = ProbComp.eval (gen n) →
        (savedCoinForger machine digestEncoding c d keyC keyD n).CallBounded
          (savedCoinBudget c d keyC keyD n) (savedCoinBudget c d keyC keyD n) ∧
        wordSufCmaGame digestEncoding scheme (program n) =
          sufCmaGame scheme (savedCoinForger machine digestEncoding c d keyC keyD n) := by
  obtain ⟨k, Control, hfinite, machine, c, d, hefficient, hrun⟩ :=
    exists_savedCoinForger hgen hprogram
  refine ⟨k, Control, hfinite, machine, c, d, hefficient,
    fun n Digest _ _ digestEncoding scheme hgen' =>
      ⟨callBounded_savedCoinForger machine digestEncoding c d keyC keyD n, ?_⟩⟩
  unfold wordSufCmaGame sufCmaGame worldGame
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  rw [hgen'] at hkeys
  simpa only [PMF.monad_bind_eq_bind, show ∀ (pairs : List (List Bool × List Bool))
      (msig : List Bool × List Bool),
      @List.contains (List Bool × List Bool)
        (@instBEqProd (List Bool) (List Bool) instBEqOfDecidableEq instBEqOfDecidableEq)
        pairs msig = pairs.contains msig from fun _ _ => Bool.eq_iff_iff.mpr (by simp)] using
    eval_worldRealize_eq_bind scheme keys.1 keys.2 _ _ _
      (hrun n keys hkeys Digest digestEncoding)
      (fun verified msig pairs => verified && !pairs.contains msig)

end Cslib.Crypto.Protocols.ROMSignature
