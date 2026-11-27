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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Strict decoding of real-arithmetic formula tokens

The dimension-independent decoder reads the constructor stream of `encFormula` and keeps each
comparison's term word as its payload. The strict framed-list decoder supplies polynomial time
and rejects malformed tags and frames. The shape of the formula and the syntax of its term words
can be checked separately.
-/

public section

namespace Cslib.Logic.RealArithmetic

open Turing.MultiTapeTM

/-- Decode framed formula tags with their comparison words, independently of dimension. -/
@[expose] def formulaTokensDecoder : PartialDecoder (encList encFormulaToken) :=
  let termWord := PartialDecoder.ofDecoder Decoder.bits
  .list (.sum .unit (.sum termWord (.sum termWord (.sum .unit (.sum .unit .unit)))))

private theorem encFormulaToken_encodeTerms {n : ℕ}
    (token : Unit ⊕ Term n ⊕ Term n ⊕ Unit ⊕ Unit ⊕ Unit) :
    encFormulaToken (FormulaToken.encodeTerms token) = encFormulaTokenEncoding n token := by
  rcases token with _ | (_ | (_ | _)) <;> rfl

/-- A canonical formula word decodes to its prefix tokens with encoded comparison terms. -/
theorem formulaTokensDecoder_decode_encFormula {n : ℕ} (p : Formula n) :
    formulaTokensDecoder.decode (encFormula n p) =
      some ((encFormula_tokens n p).map FormulaToken.encodeTerms) := by
  apply (formulaTokensDecoder.decode_eq_some_iff _ _).2
  rw [encFormula_apply]
  change ((encFormula_tokens n p).map FormulaToken.encodeTerms).flatMap (frame ∘ encFormulaToken) =
    (encFormula_tokens n p).flatMap (frame ∘ encFormulaTokenEncoding n)
  rw [List.flatMap_map]
  exact List.flatMap_congr fun token _ => congrArg frame (encFormulaToken_encodeTerms token)

/-- The bits of an equality or inequality term payload fit strictly inside the formula word. -/
theorem formulaTermWord_length_lt_of_decode {word term : List Bool} {tokens : List FormulaToken}
    (h : formulaTokensDecoder.decode word = some tokens)
    (hterm : .inr (.inl term) ∈ tokens ∨ .inr (.inr (.inl term)) ∈ tokens) :
    term.length < word.length := by
  rw [← (formulaTokensDecoder.decode_eq_some_iff _ _).1 h]
  rcases hterm with hterm | hterm
  all_goals
    have hlen := SizedListEncoding.length_elem_le (encA := encFormulaToken)
      (encL := encList encFormulaToken) tokens _ hterm
    simp only [encFormulaToken, encSum_inr, encSum_inl, encBits_apply, List.length_cons] at hlen ⊢
    lia

end Cslib.Logic.RealArithmetic
