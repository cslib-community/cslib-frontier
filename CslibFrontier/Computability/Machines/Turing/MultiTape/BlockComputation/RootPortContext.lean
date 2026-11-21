/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortQuery
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPredecessorContext
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.PairDegree

/-!
# A shared port context for counting root edges

A single framed port is prepended to the predecessor counter's fixed context. The port selects a
vertex side, label coordinate and group. Every candidate index is supplied by the counter.
Both the context preparation and the parser on arbitrary words take linear time and space.
-/

public section

namespace Turing.MultiTapeTM.RootPortContext

open RootPortQuery (Input)
open RootPortFinish (Port encPort)

/-- The port and seed are held fixed as the counter ranges over candidates. -/
@[expose] def withCandidate (a : Input) (j : ℕ) : Input :=
  (a.1, RootPredecessorContext.withCandidate a.2 j)

/-- Store the framed port before the shared seed and graph context. -/
@[expose] def word (a : Input) : List Bool :=
  encPair encPort encBits (a.1, RootPredecessorContext.word a.2)

/-- Computing the shared context scans the original request a constant number of times. -/
theorem word_deg : ComputableInDegree word RootPortQuery.encInput encBits 1 1 :=
  ((ComputableInDegree.fst encPort RootPredecessorQuery.encInput).prod
    (RootPredecessorContext.word_deg.comp
      (ComputableInDegree.snd encPort RootPredecessorQuery.encInput))).of_enc_eq fun _ => rfl

/-- Framing a port adds twice its encoded length and one terminating bit. -/
theorem length_word_le (a : Input) :
    (word a).length ≤ 2 * a.2.raw.length + 2 * RootPortQuery.shortSize a + 4 := by
  have hl := RootPredecessorContext.length_word_le a.2
  rw [RootPredecessorQuery.length_encInput] at hl
  rw [word, length_encPair]
  simp only [encBits_apply]
  unfold RootPortQuery.shortSize RootPredecessorQuery.shortSize
  omega

/-- The only variable field in an instantiated port context is the last binary index. -/
theorem shortSize_withCandidate_le (a : Input) (j : ℕ) :
    RootPortQuery.shortSize (withCandidate a j) ≤ RootPortQuery.shortSize a + j.size := by
  have hj := RootPredecessorContext.shortSize_withCandidate_le a.2 j
  unfold RootPortQuery.shortSize withCandidate
  dsimp only
  omega

private def decoder : Decoder encPort :=
  (Decoder.pair .bool (.pair .unary .nat)).map
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun p => (p.column, p.coordinate, p.group))
    (fun _ => rfl) (fun _ => rfl)

/-- Parse the port and pass the remainder of the word to the predecessor input decoder. -/
def inputOf (p : List Bool × ℕ) : Input :=
  (decoder.decode (unframe p.1), RootPredecessorContext.inputOf (dropFrame p.1, p.2))

/-- Every represented fixed port context is parsed with the correct dynamic leaf index. -/
@[simp] theorem inputOf_word (a : Input) (j : ℕ) : inputOf (word a, j) = withCandidate a j := by
  simp only [inputOf, word, encPair_apply, encBits_apply, unframe_frame_append,
    dropFrame_frame_append, decoder.decode_enc, RootPredecessorContext.inputOf_word, withCandidate]

/-- All port and seed fields are decoded in linear time, including normalization on arbitrary
words and the charge for passing the long schedule to the underlying root decoder. -/
theorem inputOf_deg :
    ComputableInDegree inputOf (encPair encBits encNat) RootPortQuery.encInput 1 1 := by
  have hn : ComputableInDegree Decoder.nat.decode encBits encNat 1 1 :=
    ComputableInO.bitsToNat.computableInDegree DegreeBounded.self DegreeBounded.self le_rfl
  have ht := Decoder.pair_computableInDegree .bool (.pair .unary .nat)
    Internal.DecoderWords.bool_degree
    (Decoder.pair_computableInDegree .unary .nat Internal.DecoderWords.unary_degree hn)
  have hd : ComputableInDegree decoder.decode encBits encPort 1 1 := ht.of_enc_eq fun _ => rfl
  have hw := ComputableInDegree.fst encBits encNat
  have hj := ComputableInDegree.snd encBits encNat
  have htail := (Internal.DecoderWords.dropFrame_degree.comp hw).prod hj
  exact ((hd.comp Internal.DecoderWords.unframe_degree).comp hw).prod
    (RootPredecessorContext.inputOf_deg.comp htail)

/-- The port-membership leaf on an arbitrary bit context and binary candidate. -/
@[expose] def predicate (k : ℕ) (p : List Bool × ℕ) : Bool := RootPortQuery.query k (inputOf p)

@[simp] theorem predicate_word (k : ℕ) (a : Input) (j : ℕ) :
    predicate k (word a, j) = RootPortQuery.query k (withCandidate a j) := by simp [predicate]

/-- One deterministic native leaf checks the requested port. Its resource bound retains the
linear table scan separately from the polynomial in the port and seed fields. -/
theorem exists_computableInO (k : ℕ) : ∃ d, ComputableInO (predicate k)
    (encPair encBits encNat) encBool
    (fun p => (encPair encBits encNat p).length + (inputOf p).2.raw.length +
      RootPortQuery.shortSize (inputOf p) ^ d)
    (fun p => (encPair encBits encNat p).length + (inputOf p).2.raw.length +
      RootPortQuery.shortSize (inputOf p) ^ d) := by
  obtain ⟨d, hd⟩ := RootPortQuery.exists_computableInO k
  exact ⟨d, (hd.comp inputOf_deg.inO_one).mono 1 (fun _ => by omega) (fun _ => by omega)⟩

end Turing.MultiTapeTM.RootPortContext
