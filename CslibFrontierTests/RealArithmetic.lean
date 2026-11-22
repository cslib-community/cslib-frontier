/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (real-arithmetic semantic and codec regression tests)

import CslibFrontier.Computability.Complexity.Classes.ExistsReal
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
public meta import CslibFrontier.Logics.RealArithmetic.Encoding
public meta import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation
public meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Logics.RealArithmetic.TokenEvaluationPolyTime
import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation

/-! Semantic edge cases and strict decoding for the ported real-arithmetic input convention. -/

public section
namespace CslibFrontierTests.RealArithmetic

open Cslib.Logic.RealArithmetic Cslib.Complexity Turing.MultiTapeTM

-- The second coordinate is absent, and the negative constant is reduced modulo a composite.
example :
    let t : Term 2 := .mul (.var 0) (.add (.const (-2)) (.var 1))
    let point : List ℕ := [3]
    (t.toPolynomial.eval₂ (Int.castRingHom (ZMod 8))
      (fun i => ((point[i.val]?.getD 0 : ℕ) : ZMod 8))).val = 2 := by
  intro t point
  rw [← Term.evalResidue_eq (by decide : 0 < 8) point t]
  decide +kernel

-- The prefix evaluator leaves the initial stack beneath the result.
example : Term.evalTokenStack 8 [3] ((encTerm_tokens 2
    (.mul (.var 0) (.add (.const (-2)) (.var 1)))).map TermToken.ofFin) [5] = some [2, 5] := by
  decide +kernel

-- An operator with only one operand fails.
example : Term.evalTokenStack 8 [] [.inr (.inr (.inl ())), .inl 3] [] = none := by
  decide +kernel

-- The step certificate takes a natural-rank token at runtime.
example : ComputableInPolyTime (fun token => Term.evalTokenStep 8 [] token [3])
    encTermToken (encOption (encList encNat)) :=
  Term.evalTokenStep_polyTime (.const 8) (.const []) (.const [3]) .id'

-- The fold certificate charges the entire input token list, even for a composite modulus.
example : ComputableInPolyTime (fun tokens => Term.evalTokenStack 8 [3] tokens [])
    (encList encTermToken) (encOption (encList encNat)) :=
  Term.evalTokenStack_polyTime (.const 8) (fun _ => by decide) (.const [3]) .id'

-- Decoding the word needs no ambient dimension to recover the variable rank.
example : termTokensDecoder.decode (encTerm 2 (.add (.var 1) (.const (-2)))) =
    some [.inr (.inr (.inl ())), .inr (.inl 1), .inl (-2)] := by
  rw [termTokensDecoder_decode_encTerm]
  rfl

-- A complete frame with an empty payload is missing its constructor tag.
example : termTokensDecoder.decode (frame []) = none := by
  decide +kernel

-- Uniform evaluation reads the word directly and zero-pads the missing second coordinate.
example : Term.evalTermWord 8 [3]
    (encTerm 2 (.mul (.var 0) (.add (.const (-2)) (.var 1)))) = some 2 := by
  rw [Term.evalTermWord_encTerm]
  decide +kernel

-- Two complete leaf tokens leave two residues and do not form a single term.
example :
    let word := encList encTermToken [.inl 0, .inl 1]
    ¬ ∃ t : Term word.length, encTerm word.length t = word := by
  intro word
  rintro ⟨t, ht⟩
  have h := (Term.evalTermWord_eq_some_iff (p := 8) (point := [])).2 ⟨t, ht, rfl⟩
  have hnone : Term.evalTermWord 8 [] word = none := by decide +kernel
  rw [hnone] at h
  cases h

/-- A closed test formula with strict inequality, disjunction, and negation. -/
def sentence : Formula 0 :=
  .or (.ltZero (.add (.const (-37)) (.const 12)))
    (.and (.eqZero (.mul (.const 0) (.const 91))) (.not .false))

-- The two comparison payloads survive formula-token decoding as the original term words.
example : formulaTokensDecoder.decode (encFormula 2
    (.and (.eqZero (.var 1)) (.ltZero (.const (-2))))) =
    some [.inr (.inr (.inr (.inr (.inl ())))), .inr (.inl (encTerm 2 (.var 1))),
      .inr (.inr (.inl (encTerm 2 (.const (-2)))))] := by
  rw [formulaTokensDecoder_decode_encFormula]
  rfl

-- The falsity tag carries no payload.
example : formulaTokensDecoder.decode (frame [false, true]) = none := by
  decide +kernel

-- The validator accepts a complete tree with two different term payloads.
example : validFormulaWord (encFormula 2
    (.and (.eqZero (.var 1)) (.ltZero (.const (-2))))) = true :=
  validFormulaWord_encFormula _

-- The conjunction tag is framed correctly but lacks both child formulas.
set_option linter.hashCommand false in
#guard !(validFormulaWord
  (encList encFormulaToken [.inr (.inr (.inr (.inr (.inl ()))))]))

-- The equality is a leaf in the formula tree, but its payload is an incomplete term.
set_option linter.hashCommand false in
#guard !(validFormulaWord
  (encList encFormulaToken [.inr (.inl (encList encTermToken [.inr (.inr (.inl ()))]))]))

-- Two complete formulas cannot appear in one encoded word.
set_option linter.hashCommand false in
#guard !(validFormulaWord (encList encFormulaToken [.inl (), .inl ()]))

-- Normalization keeps an encoded formula with a variable rank and a negative constant.
set_option linter.hashCommand false in
#guard
  let word := encFormula 2 (.and (.eqZero (.var 1)) (.ltZero (.const (-2))))
  normalizeFormulaWord word == word

-- A dangling negation normalizes to the encoding of falsity.
set_option linter.hashCommand false in
#guard normalizeFormulaWord (encList encFormulaToken [.inr (.inr (.inr (.inl ())))]) ==
  encFormula 0 .false

-- The total view preserves the existential semantics of a satisfiable formula.
example :
    (Formula.ofWord (encFormula 0 (.eqZero (.const 0)))).solutionSet.Nonempty := by
  rw [← mem_ETR_iff_ofWord, encFormula_mem_ETR]
  exact ⟨Fin.elim0, by simp [Formula.solutionSet, Term.eval]⟩

-- An asymmetric two-block formula checks that existential coordinates come first.
example : (Formula.eqZero (n := 2) (.var 0)).existsForallSolutionSet
    (r := 1) (s := 1) = {x | x 0 = 0} := by
  ext x
  simp [Formula.existsForallSolutionSet, Formula.solutionSet, Term.eval, Fin.addCases]

-- The encoded language rejects x²+1=0, despite allowing every ambient dimension.
example : encFormula 1 (Formula.eqZero
    (.add (.mul (.var 0) (.var 0)) (.const 1))) ∉ ETR := by
  rw [encFormula_mem_ETR]
  rintro ⟨x, hx⟩
  simp only [Formula.solutionSet, Set.mem_ofPred_eq, Term.eval] at hx
  norm_num at hx
  nlinarith [sq_nonneg (x 0)]

-- The language-level two-block criterion retains the quantifier order.
example : encPair encUnary encBits (1, encFormula 2
    (Formula.eqZero (.var 0))) ∈ ExistsForallTheory := by
  rw [encFormula_mem_ExistsForallTheory (r := 1) (s := 1)]
  refine ⟨fun _ => 0, ?_⟩
  simp [Formula.existsForallSolutionSet, Formula.solutionSet, Term.eval, Fin.addCases]

example : encPair encUnary encBits (0, encFormula 1
    (Formula.eqZero (.var 0))) ∉ ExistsForallTheory := by
  rw [encFormula_mem_ExistsForallTheory (r := 0) (s := 1)]
  rintro ⟨x, hx⟩
  have h := hx (fun _ => 1)
  simp [Formula.solutionSet, Term.eval, Fin.addCases] at h

-- Empty universal and existential blocks have their ordinary logical meanings.
example : (Formula.eqZero (n := 0) (.const 0)).existsForallSolutionSet
    (r := 0) (s := 0) = Set.univ := by
  ext x
  simp [Formula.existsForallSolutionSet, Formula.solutionSet, Term.eval, Fin.addCases]

private def termCodec : PartialDecoder (encTerm 0) :=
  encTerm_decoder 0 (.ofDecoder Decoder.intBin) (.empty _)

private def formulaCodec : PartialDecoder (encFormula 0) :=
  encFormula_decoder 0 termCodec termCodec

-- The generated strict decoder consumes one complete word; a trailing bit is rejected.
set_option linter.hashCommand false in
#guard (formulaCodec.decode (encFormula 0 sentence)).isSome

set_option linter.hashCommand false in
#guard (formulaCodec.decode (encFormula 0 sentence ++ [true])).isNone

-- The public language accepts the actual satisfiable closed formula.
example : encFormula 0 sentence ∈ ETR := by
  refine Set.mem_iUnion.mpr ⟨0, Set.mem_image_of_mem (encFormula 0) ?_⟩
  refine ⟨Fin.elim0, ?_⟩
  simp [sentence, Formula.solutionSet, Term.eval]

end CslibFrontierTests.RealArithmetic
