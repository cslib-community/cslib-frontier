/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Interactive oracle proofs

A challenge is delivered in full to the prover, which commits the next proof word.
The verifier sees only an empty acknowledgment. A bit query addresses a round
and a position using a framed pair of binary numbers. It reads the corresponding word
without advancing the prover's state. Earlier commitments remain available in all
later rounds.

The shape fixes the number of rounds and the lengths of the verifier challenges
and the prover words. Only the challenge lengths use unary in the shape encoding.
Binary proof lengths let the verifier specify exponentially long messages with a
polynomial-time generator. Padding or truncation interprets an arbitrary response
as a word of the prescribed length. A query outside the committed region returns
false. A run that ends before or after the specified number of rounds rejects.

The strict polynomial clock is on the verifier, with each bit lookup supplied as
an external oracle operation. The prover remains unrestricted. This follows
[BenSassonChiesaSpooner2016, full version, §§4.1–4.2]. The NEXP characterization
in Appendix A is a separate theorem.

## Main definitions

* `Cslib.Complexity.InteractiveOracleProof.proverOracle`: a prover with persistent commitments.
* `Cslib.Complexity.InteractiveOracleProof.acceptProb`: the probability of a valid accepting run.
* `Cslib.Complexity.PromiseIOP` and `Cslib.Complexity.IOP`: the promise and language classes.
-/

public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

namespace InteractiveOracleProof

/-- A challenge commits a new word. A read only observes one bit of a committed word. -/
inductive Request
  /-- Send a challenge word and commit the next proof. -/
  | challenge
  /-- Read one bit at an encoded pair of indices. -/
  | read
  deriving DecidableEq

instance : Fintype Request :=
  ⟨{.challenge, .read}, fun request => by cases request <;> simp⟩

/-- The challenge and proof lengths for each round. -/
abbrev Shape := List (ℕ × ℕ)

/-- Challenge lengths are unary. Proof lengths are binary. -/
abbrev encShape : Shape ↪ List Bool :=
  encList (encPair encUnary encNat)

/-- The round number is framed, and the bit position is binary in the remaining word. -/
abbrev encAddress : (ℕ × ℕ) ↪ List Bool := encPair encNat encNat

/-- Decode the address supplied to a read operation. -/
@[expose] def decodeAddress (address : List Bool) : ℕ × ℕ :=
  (ofBits (unframe address), ofBits (dropFrame address))

/-- The standard address encoding recovers both the round and the bit position. -/
theorem decodeAddress_encAddress (q : ℕ × ℕ) : decodeAddress (encAddress q) = q := by
  obtain ⟨r, i⟩ := q
  change (ofBits (unframe (frame (encNat r) ++ encNat i)),
    ofBits (dropFrame (frame (encNat r) ++ encNat i))) = (r, i)
  simp

/-- Read a committed bit within its prescribed proof length. Missing bits are zero. -/
@[expose] def proofBit (shape : Shape) (words : List (List Bool)) (round pos : ℕ) : Bool :=
  if pos < ((shape[round]?).getD (0, 0)).2 then ((words[round]?).getD [])[pos]?.getD false
  else false

/-- Deliver each challenge to the prover and retain its reply as the next oracle word.
Read operations leave the prover and all commitments unchanged. -/
@[expose] noncomputable def proverOracle (shape : Shape) (P : Prover Unit) : Prover Request where
  State := P.State × List (List Bool)
  init := (P.init, [])
  respond
    | (.challenge, word), (state, words) =>
      let len := ((shape[words.length]?).getD (0, 0)).1
      ((P.respond ((), List.ofFn (BitString.ofList len word))).run state).map fun (reply, next) =>
        ([], next, words ++ [reply])
    | (.read, address), (state, words) =>
      let (round, pos) := decodeAddress address
      PMF.pure ([proofBit shape words round pos], state, words)

/-- The probability of acceptance with the prescribed number of rounds. -/
@[expose] noncomputable def acceptProb (shape : Shape) (V : WordOracleComp Request Bool)
    (P : Prover Unit) : ℝ≥0∞ :=
  let O := proverOracle shape P
  ((O.run V O.init).map fun (verdict, _, words) =>
    verdict && decide (words.length = shape.length)) true

end InteractiveOracleProof

/-- Polynomial-time interactive oracle proofs with perfect completeness and soundness 1/3. -/
@[expose] def PromiseIOP {α : Type} (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {X | ∃ (shape : α → InteractiveOracleProof.Shape)
      (V : α → WordOracleComp InteractiveOracleProof.Request Bool),
    ComputableInPolyTime shape enc InteractiveOracleProof.encShape ∧
    IsOraclePPTOn enc encBool V ∧
    (∀ a ∈ X.yes, ∃ P, InteractiveOracleProof.acceptProb (shape a) (V a) P = 1) ∧
    (∀ a ∈ X.no, ∀ P, InteractiveOracleProof.acceptProb (shape a) (V a) P ≤ 1 / 3)}

/-- Interactive oracle proof systems for languages. -/
@[expose] def IOP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseIOP enc}

end Cslib.Complexity
