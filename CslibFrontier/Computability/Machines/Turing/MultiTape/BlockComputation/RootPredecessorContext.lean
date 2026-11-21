/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPredecessorQuery
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.PairDegree
import Mathlib.Data.Nat.Size

/-!
# Root predecessor tests on the counting machine's context tape

The counter stores one word independently of its leaf index. The final field of the root
predecessor input is the unframed binary candidate. Its encoding at zero is empty, so appending
a leaf index to the fixed word gives exactly the encoding needed by the predicate. A total linear
decoder also defines the machine's behavior on arbitrary words by the usual frame, binary and
unary decoding rules.
-/

public section

namespace Turing.MultiTapeTM.RootPredecessorContext

open Cslib.SeededPredecessor (Context encContext)
open RootPredecessorQuery (Input)

/-- Install the leaf index without changing the edge, hash seed, or graph. -/
@[expose] def withCandidate (a : Input) (j : ℕ) : Input :=
  { a with context := { a.context with candidate := j } }

/-- Shared context for every leaf of the same rank request. -/
@[expose] def word (a : Input) : List Bool := RootPredecessorQuery.encInput (withCandidate a 0)

/-- The counting context can be prepared once from the encoded rank request in linear time
and workspace. Only the last field is replaced. -/
theorem word_deg : ComputableInDegree word RootPredecessorQuery.encInput encBits 1 1 := by
  open Cslib.SeededPredecessor in
  have hfields : ComputableInDegree (fun c : Context =>
      (c.universeSize, c.labelLength, c.c0, c.c1, c.c2, c.c3, c.edge, 0))
      encContext encContextFields 1 1 := by
    exact encContext_universeSize_deg.prod (encContext_labelLength_deg.prod
      (encContext_c0_deg.prod (encContext_c1_deg.prod (encContext_c2_deg.prod
        (encContext_c3_deg.prod (encContext_edge_deg.prod (.const 0)))))))
  have hs : ComputableInDegree (fun c : Context => {c with candidate := 0})
      encContext encContext 1 1 := hfields.of_enc_eq fun _ => rfl
  open RootPredecessorQuery in
  exact (encInput_raw_deg.prod (encInput_copies_deg.prod (hs.comp encInput_context_deg))).of_enc_eq
    fun _ => rfl

private theorem context_append (c : Context) (j : ℕ) :
    encContext { c with candidate := 0 } ++ j.bits = encContext { c with candidate := j } := by
  simp [Cslib.SeededPredecessor.encContext_apply, Cslib.SeededPredecessor.encContextFields,
    encPair_apply, encNat_apply, List.append_assoc]

/-- Appending the new binary index exactly replaces the empty final candidate field. -/
theorem word_append_bits (a : Input) (j : ℕ) :
    word a ++ j.bits = RootPredecessorQuery.encInput (withCandidate a j) := by
  simp only [word, withCandidate, RootPredecessorQuery.encInput_apply,
    RootPredecessorQuery.encInputFields, encPair_apply, List.append_assoc, context_append]

/-- Storing the fixed context uses at most the length of the original encoded request. -/
theorem length_word_le (a : Input) :
    (word a).length ≤ (RootPredecessorQuery.encInput a).length := by
  have hw := congrArg List.length (word_append_bits a a.context.candidate)
  change (word a ++ a.context.candidate.bits).length =
    (RootPredecessorQuery.encInput a).length at hw
  simp only [List.length_append] at hw
  omega

/-- The dynamic candidate adds at most its own binary length to the short arithmetic budget. -/
theorem shortSize_withCandidate_le (a : Input) (j : ℕ) :
    RootPredecessorQuery.shortSize (withCandidate a j) ≤
      RootPredecessorQuery.shortSize a + j.size := by
  have hj := congrArg List.length (context_append a.context j)
  have h₀ := congrArg List.length (context_append a.context a.context.candidate)
  change _ = (encContext a.context).length at h₀
  simp only [List.length_append, Nat.size_eq_bits_len] at hj h₀
  unfold RootPredecessorQuery.shortSize withCandidate
  dsimp only
  omega

private def seedFields : Decoder Cslib.SeededPredecessor.encContextFields :=
  .pair .nat (.pair .unary (.pair .nat (.pair .nat (.pair .nat (.pair .nat (.pair .nat .nat))))))

private def seedDecoder : Decoder encContext :=
  seedFields.map
    (fun ⟨u, a, c₀, c₁, c₂, c₃, e, j⟩ => ⟨u, a, c₀, c₁, c₂, c₃, e, j⟩)
    (fun c => (c.universeSize, c.labelLength, c.c0, c.c1, c.c2, c.c3, c.edge, c.candidate))
    (fun _ => rfl) (fun _ => rfl)

private def decoder : Decoder RootPredecessorQuery.encInput :=
  (Decoder.pair .bits (.pair .nat seedDecoder)).map
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun a => (a.raw, a.copies, a.context))
    (fun _ => rfl) (fun _ => rfl)

/-- Total query input on the arbitrary bit word and runtime candidate of a counting leaf. -/
def inputOf (p : List Bool × ℕ) : Input := decoder.decode (p.1 ++ p.2.bits)

/-- A represented context supplies its original record at every runtime index. -/
@[simp] theorem inputOf_word (a : Input) (j : ℕ) : inputOf (word a, j) = withCandidate a j := by
  unfold inputOf
  rw [word_append_bits, decoder.decode_enc]

/-- An empty buffer at leaf zero decodes to an empty graph. -/
@[simp] theorem inputOf_nil_zero :
    inputOf ([], 0) = ⟨[], 0, ⟨0, 0, 0, 0, 0, 0, 0, 0⟩⟩ := by rfl

/-- Parsing and normalizing the framed context consumes linear time and workspace even on
malformed words. No seed arithmetic or schedule validation is performed by this stage. -/
theorem inputOf_deg :
    ComputableInDegree inputOf (encPair encBits encNat) RootPredecessorQuery.encInput 1 1 := by
  have hn : ComputableInDegree Decoder.nat.decode encBits encNat 1 1 :=
    ComputableInO.bitsToNat.computableInDegree DegreeBounded.self DegreeBounded.self le_rfl
  have hs : ComputableInDegree seedFields.decode encBits
      Cslib.SeededPredecessor.encContextFields 1 1 := by
    unfold seedFields
    repeat'
      apply Decoder.pair_computableInDegree _ _
        (d₁ := 1) (d₂ := 1) (e₁ := 1) (e₂ := 1)
    all_goals first | exact hn | exact Internal.DecoderWords.unary_degree
  have hseed : ComputableInDegree seedDecoder.decode encBits encContext 1 1 :=
    hs.of_enc_eq fun _ => rfl
  have hall := Decoder.pair_computableInDegree .bits (.pair .nat seedDecoder)
    Internal.DecoderWords.bits_degree (Decoder.pair_computableInDegree .nat seedDecoder hn hseed)
  have hparse : ComputableInDegree decoder.decode encBits RootPredecessorQuery.encInput 1 1 :=
    hall.of_enc_eq fun _ => rfl
  have happ : ComputableInDegree (fun p : List Bool × ℕ => p.1 ++ p.2.bits)
      (encPair encBits encNat) encBits 1 1 :=
    (ComputableInDegree.fst encBits encNat).append (ComputableInDegree.snd encBits encNat)
      fun _ => rfl
  exact hparse.comp happ

/-- The predicate called by the counter on its shared context and an individual leaf. -/
@[expose] def predicate (k : ℕ) (p : List Bool × ℕ) : Bool :=
  RootPredecessorQuery.query k (inputOf p)

@[simp] theorem predicate_word (k : ℕ) (a : Input) (j : ℕ) :
    predicate k (word a, j) = RootPredecessorQuery.query k (withCandidate a j) := by
  simp [predicate]

/-- The uniform predicate machine pays linear context and table costs; its polynomial
depends only on the decoded short fields. -/
theorem exists_computableInO (k : ℕ) : ∃ d, ComputableInO (predicate k)
    (encPair encBits encNat) encBool
    (fun p => (encPair encBits encNat p).length + (inputOf p).raw.length +
      RootPredecessorQuery.shortSize (inputOf p) ^ d)
    (fun p => (encPair encBits encNat p).length + (inputOf p).raw.length +
      RootPredecessorQuery.shortSize (inputOf p) ^ d) := by
  obtain ⟨d, hd⟩ := RootPredecessorQuery.exists_computableInO k
  exact ⟨d, (hd.comp inputOf_deg.inO_one).mono 1
    (fun p => by omega) (fun p => by omega)⟩

end Turing.MultiTapeTM.RootPredecessorContext
