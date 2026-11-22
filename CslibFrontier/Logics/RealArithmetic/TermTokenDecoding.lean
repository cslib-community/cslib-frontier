/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.RealArithmetic.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Strict decoding of real-arithmetic term tokens

A raw term word carries unary variable ranks without a separate ambient dimension. The decoder
reads each rank as a natural number, using the binary integer and framed constructor stream of
`encTerm`. This exposes the ranks needed by modular evaluation, as in `TermModularData` from
lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.

The decoder checks token framing and scalar encodings in polynomial time. A later syntax check
can decide whether the resulting stream contains exactly one complete term.
-/

public section

namespace Cslib.Logic.RealArithmetic

open Turing.MultiTapeTM

/-- Decode the complete framed constructor stream, independently of the ambient dimension. -/
@[expose] def termTokensDecoder : PartialDecoder (encList encTermToken) :=
  .list (.sum (.ofDecoder Decoder.intBin) (.sum (.ofDecoder Decoder.unary) (.sum .unit .unit)))

private theorem encTermToken_ofFin {n : ℕ} (token : ℤ ⊕ Fin n ⊕ Unit ⊕ Unit) :
    encTermToken (TermToken.ofFin token) = encTermTokenEncoding n token := by
  rcases token with z | (i | (_ | _))
  · rfl
  · simp only [TermToken.ofFin, encTermToken, encTermTokenEncoding, Sum.map_inr, Sum.map_inl,
      encSum_inr, encSum_inl, EncodingPolicy.BinaryIntUnaryFin.fin, encFinEnum_fin_apply]
  · rfl
  · rfl

/-- A term's word decodes to its original prefix tokens with natural-number ranks. -/
theorem termTokensDecoder_decode_encTerm {n : ℕ} (t : Term n) :
    termTokensDecoder.decode (encTerm n t) = some ((encTerm_tokens n t).map TermToken.ofFin) := by
  apply (termTokensDecoder.decode_eq_some_iff _ _).2
  rw [encTerm_apply]
  change ((encTerm_tokens n t).map TermToken.ofFin).flatMap (frame ∘ encTermToken) =
    (encTerm_tokens n t).flatMap (frame ∘ encTermTokenEncoding n)
  rw [List.flatMap_map]
  congr 1
  funext token
  exact congrArg frame (encTermToken_ofFin token)

/-- Every decoded variable rank is strictly smaller than the length of the input word. -/
theorem termTokenRank_lt_of_decode {word : List Bool} {tokens : List TermToken} {i : ℕ}
    (h : termTokensDecoder.decode word = some tokens) (hi : Sum.inr (Sum.inl i) ∈ tokens) :
    i < word.length := by
  rw [← (termTokensDecoder.decode_eq_some_iff _ _).1 h]
  have hlen := SizedListEncoding.length_elem_le (encA := encTermToken)
    (encL := encList encTermToken) tokens _ hi
  change (true :: false :: encUnary i).length ≤ (encList encTermToken tokens).length at hlen
  simp only [List.length_cons, encUnary_apply, List.length_replicate] at hlen
  omega

end Cslib.Logic.RealArithmetic
