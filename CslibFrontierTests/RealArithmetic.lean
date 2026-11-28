/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (real-arithmetic semantic and codec regression tests)

import CslibFrontier.Computability.Complexity.Classes.ExistsReal
import CslibFrontier.Computability.Complexity.RealAlgebraic.SingleEquationCounting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
public meta import CslibFrontier.Logics.RealArithmetic.Encoding
public meta import CslibFrontier.Logics.RealArithmetic.FormulaBooleanEvaluation
public meta import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation
public meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Logics.RealArithmetic.TokenEvaluationPolyTime
import CslibFrontier.Logics.RealArithmetic.FormulaBooleanEvaluation
import CslibFrontier.Logics.RealArithmetic.FormulaGatePolynomial
import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation

/-! Semantic edge cases and strict decoding for the ported real-arithmetic input convention. -/

public section
namespace CslibFrontierTests.RealArithmetic

open Cslib.Logic.RealArithmetic Cslib.Complexity Turing.MultiTapeTM

-- Unused ambient coordinates are not part of a constant term's word.
example : encTerm 100 (.const 0) ∈ RealSingleEquation :=
  (encTerm_mem_RealSingleEquation _).mpr ⟨fun _ => 0, by simp [Term.eval]⟩

example : encTerm 0 (.const 1) ∉ RealSingleEquation := by
  intro h
  obtain ⟨x, hx⟩ := (encTerm_mem_RealSingleEquation (.const 1 : Term 0)).mp h
  simp [Term.eval] at hx

-- The empty word encodes no term, even when the evaluation point is empty.
example : [] ∉ RealSingleEquation := by
  rintro ⟨t, ht, _⟩
  have h := Term.evalTermWord_encTerm 1 [] t
  rw [ht] at h
  have hnone : Term.evalTermWord 1 [] [] = none := by decide +kernel
  rw [hnone] at h
  cases h

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

-- Indices follow the formula's prefix order and retain the exact comparison payloads.
set_option linter.hashCommand false in
#guard
  let word := encFormula 2 (.and (.eqZero (.var 1)) (.ltZero (.const (-2))))
  formulaWordTokenAt word 1 == .inr (.inl (encTerm 2 (.var 1))) &&
    formulaWordTokenAt word 2 == .inr (.inr (.inl (encTerm 2 (.const (-2)))))

-- Out-of-range binary indices and malformed formula words give the falsity token.
set_option linter.hashCommand false in
#guard formulaWordTokenAt (encFormula 0 (.eqZero (.const 0))) (2 ^ 80) == .inl () &&
  formulaWordTokenAt (encList encFormulaToken [.inr (.inr (.inr (.inl ())))]) 0 == .inl ()

-- Comparison queries retain different payloads and the distinction between zero and negative.
set_option linter.hashCommand false in
#guard
  let word := encFormula 1 (.and (.eqZero (.var 0)) (.ltZero (.const (-2))))
  decide (formulaWordComparisonRequest word 1 = some ⟨encTerm 1 (.var 0), false⟩) &&
    decide (formulaWordComparisonRequest word 2 = some ⟨encTerm 1 (.const (-2)), true⟩) &&
    (formulaWordComparisonRequest word 0).isNone &&
    (formulaWordComparisonRequest word (2 ^ 80)).isNone &&
    (formulaWordComparisonRequest [] 0).isNone

-- The term source copies comparison payloads and supplies a canonical zero at unused slots.
set_option linter.hashCommand false in
#guard
  let word := encFormula 1 (.and (.eqZero (.var 0)) (.ltZero (.const (-2))))
  formulaWordGateTermWord word 1 == encTerm 1 (.var 0) &&
    formulaWordGateTermWord word 2 == encTerm 1 (.const (-2)) &&
    formulaWordGateTermWord word 0 == encTerm 1 (.const 0) &&
    formulaWordGateTermWord word (2 ^ 80) == encTerm 1 (.const 0) &&
    formulaWordGateTermWord [] 0 == encTerm 0 (.const 0) &&
    decide (0 < (formulaWordGateTermWord [] 0).length)

-- The coefficient and outer variables specialize to different coordinates.
example (x y : ℝ) :
    let word := encFormula 1 (.eqZero (.var 0))
    let coordinates : Fin word.length → Polynomial (Polynomial ℤ) :=
      fun _ => Polynomial.C Polynomial.X + Polynomial.X ^ 2
    Polynomial.aevalAeval x y (formulaWordGatePolynomial word 0 coordinates) = x + y ^ 2 := by
  intro word coordinates
  let formula : Formula 1 := .eqZero (.var 0)
  have hw : word = encFormula 1 formula := rfl
  have hnonempty : 0 < word.length := by decide
  clear_value word
  let first : Fin word.length := ⟨0, hnonempty⟩
  have hterm : formulaWordGateTerm word 0 = .var first := by
    have htokens : formulaWordTokens word =
        [] ++ ((encFormula_tokens 1 formula).map FormulaToken.encodeTerms ++ []) := by
      rw [hw, formulaWordTokens, normalizeFormulaWord,
        ite_eq_left (validFormulaWord_encFormula formula), formulaTokensDecoder_decode_encFormula]
      simp only [List.nil_append, List.append_nil, Option.getD_some]
    have hrequest := formulaWordComparisonRequest_of_prefix formula [] [] htokens
    change formulaWordComparisonRequest word 0 = some ⟨encTerm 1 (.var 0), false⟩ at hrequest
    apply (encTerm _).injective
    rw [encTerm_formulaWordGateTerm, formulaWordGateTermWord, hrequest, Option.elim_some]
    exact (encTerm_rename (fun _ : Fin 1 => first) (fun i => by
      change 0 = i.val
      omega) (.var 0)).symm
  rw [aevalAeval_formulaWordGatePolynomial, hterm]
  simp only [Term.eval, coordinates, map_add, map_pow, Polynomial.aevalAeval_X,
    Polynomial.aevalAeval_Y]

example :
    let word := encFormula 1 (.eqZero (.var 0))
    let coordinates : Fin word.length → Polynomial (Polynomial ℤ) :=
      fun _ => Polynomial.C Polynomial.X + Polynomial.X ^ 2
    (formulaWordGatePolynomial word 0 coordinates).bivariateCoeffNorm1 ≤
      4 ^ formulaWordGateTermBudget word := by
  intro word coordinates
  refine formulaWordGatePolynomial_bivariateCoeffNorm1_le word 0 coordinates (M := 2)
    (by decide) fun _ => ?_
  refine (Polynomial.bivariateCoeffNorm1_add_le _ _).trans ?_
  rw [Polynomial.bivariateCoeffNorm1_C, Polynomial.coeffNorm1_X]
  have h := Polynomial.bivariateCoeffNorm1_mul_X_pow_le 1 2
  simp only [one_mul, Polynomial.bivariateCoeffNorm1_one] at h
  exact Nat.add_le_add_left h 1

-- The same comparison slots evaluate modulo a composite, with missing coordinates set to zero.
set_option linter.hashCommand false in
#guard
  let word := encFormula 1 (.and (.eqZero (.var 0)) (.ltZero (.const (-2))))
  formulaWordComparisonResidue word 1 8 [11] == some 3 &&
    formulaWordComparisonResidue word 1 8 [] == some 0 &&
    formulaWordComparisonResidue word 2 8 [] == some 6 &&
    (formulaWordComparisonResidue word 0 8 []).isNone &&
    (formulaWordComparisonResidue word (2 ^ 80) 8 []).isNone &&
    (formulaWordComparisonResidue [] 0 8 []).isNone &&
    formulaWordGateResidue word 1 8 [11] == 3 &&
    formulaWordGateResidue word 1 8 [] == 0 &&
    formulaWordGateResidue word 2 8 [] == 6 &&
    formulaWordGateResidue word 0 8 [] == 0 &&
    formulaWordGateResidue word (2 ^ 80) 8 [] == 0 &&
    formulaWordGateResidue [] 0 8 [] == 0

-- The left subtree stops at the right child of the conjunction.
set_option linter.hashCommand false in
#guard
  let word := encFormula 0 (.and (.not (.eqZero (.const 0))) (.or .false (.ltZero (.const (-1)))))
  formulaSubtreeSizeAt word 0 == some 6 && formulaSubtreeSizeAt word 1 == some 2 &&
    formulaSubtreeSizeAt word 3 == some 3 && (formulaSubtreeSizeAt word (2 ^ 80)).isNone

-- The total view of the empty word is one falsity token.
set_option linter.hashCommand false in
#guard formulaSubtreeSizeAt [] 0 == some 1 && (formulaSubtreeSizeAt [] 1).isNone

-- Both binary connectives skip their first subtree, and negation has only one child.
set_option linter.hashCommand false in
#guard
  let word := encFormula 0 (.and (.not (.eqZero (.const 0))) (.or .false (.ltZero (.const (-1)))))
  formulaWordChildIndices word 0 == [1, 3] && formulaWordChildIndices word 1 == [2] &&
    formulaWordChildIndices word 3 == [4, 5] && formulaWordChildIndices word 5 == []

-- Neither the malformed formula view nor an oversized index yields a child.
set_option linter.hashCommand false in
#guard formulaWordChildIndices [] 0 == [] &&
  formulaWordChildIndices (encFormula 0 (.not .false)) (2 ^ 80) == []

-- The same negative sign makes the equality false and the strict inequality true.
-- Connectives read their own child indices, including the skipped left subtree at the root.
set_option linter.hashCommand false in
#guard
  let term : Term 0 := .const (-1)
  let word := encFormula 0 (.and (.not (.eqZero term)) (.or .false (.ltZero term)))
  let termSign := fun bits => if bits == encTerm 0 term then (-1 : SignType) else 0
  let gate := fun index => formulaWordGateValue word index termSign
  let value := fun index => index == 1 || index == 3 || index == 5
  gate 0 value && !gate 0 (· == 1) && gate 1 value && !gate 2 value &&
    gate 3 value && !gate 4 value && gate 5 value && !gate (2 ^ 80) value

-- A backward scan computes the operand values without a caller-provided gate table.
set_option linter.hashCommand false in
#guard
  let term : Term 0 := .const (-1)
  let word := encFormula 0 (.and (.not (.eqZero term)) (.or .false (.ltZero term)))
  let termSign := fun bits => if bits == encTerm 0 term then (-1 : SignType) else 0
  formulaWordGateValues word termSign == [true, true, false, true, false, true] &&
    formulaWordGateValuesWithAnswers word (· != 2) == [true, true, false, true, false, true] &&
    formulaWordGateValuesWithAnswers word (fun i => formulaWordComparisonAnswer word i (-1)) ==
      [true, true, false, true, false, true] &&
    formulaWordGateValuesWithSignature (n := 6) word (fun _ => -1) ==
      [true, true, false, true, false, true] &&
    formulaWordGateValuesWithSignature (n := 5) word (fun _ => -1) ==
      [false, true, false, false, false, false] &&
    formulaWordGateValues [] termSign == [false]

-- A huge gate index uses the same suffix offsets as a small one. A child at the gate
-- or beyond the stored suffix reads false even if the suffix starts with true.
set_option linter.hashCommand false in
#guard
  let index := 2 ^ 80
  formulaGateSuffixValue [true, false, true] index (index + 1) &&
    formulaGateSuffixValue [true, false, true] index (index + 3) &&
    !formulaGateSuffixValue [true] index index &&
    !formulaGateSuffixValue [true] index (2 * index)

-- Only comparison gates use the prepared answer. Each step preserves the computed suffix.
set_option linter.hashCommand false in
#guard
  let word := encFormula 0 (.or (.not (.eqZero (.const 0))) (.ltZero (.const (-1))))
  formulaWordGateUpdate word 0 false [false, true, true] == [true, false, true, true] &&
    formulaWordGateUpdate word 1 false [false, true] == [true, false, true] &&
    formulaWordGateUpdate word 3 true [] == [true] &&
    formulaWordGateUpdate word 3 false [] == [false] &&
    formulaWordGateUpdate [] (2 ^ 80) true [] == [false]

-- A positive sign never satisfies either comparison, so this reader uses a constant answer.
example :
    ComputableInPolySpace (fun word : List Bool => formulaWordGateValues word (fun _ => 1))
      encBits encBits := by
  refine formulaWordGateValues_polySpace_of_comparisonAnswers ComputableInPolyTime.id' ?_
  refine ComputableInPolySpace.congr
    (ComputableInPolySpace.of_polyTime (ComputableInPolyTime.const false)) ?_
  rintro ⟨word, index⟩
  cases formulaWordComparisonRequest word index with
  | none => rfl
  | some request =>
    rcases request with ⟨_, strict⟩
    cases strict <;> simp [Option.any, FormulaComparisonRequest.requestedSign]

-- A raw formula word and a framed sign list are ordinary inputs to the space certificate.
example :
    ComputableInPolySpace (fun p : List Bool × List SignType =>
      formulaWordGateValuesWithSignature p.1 (fun index : Fin p.2.length => p.2[index.val]))
      (encPair encBits (encList encSign)) encBits :=
  formulaWordGateValuesWithSignature_polySpace (ComputableInPolyTime.fst _ _)
    (ComputableInPolyTime.snd _ _)

-- A malformed word has no comparison terms, so its sign reader can be arbitrary.
example (termSign : List Bool → SignType) (x : Fin 0 → ℝ) :
    (formulaWordGateValues [] termSign).getD 0 false = true ↔
      x ∈ (Formula.ofWord []).solutionSet := by
  refine formulaWordGateValues_getD_zero_eq_true_iff [] termSign x ?_
  intro _ h
  have hinvalid : validFormulaWord [] ≠ true := by
    intro hvalid
    obtain ⟨p, hp⟩ := validFormulaWord_eq_true_iff.mp hvalid
    cases p <;> simp [encFormula_apply, encFormula_tokens] at hp
  rw [formulaWordTokens_eq, Formula.ofWord_of_not_valid hinvalid] at h
  simp [encFormula_tokens, FormulaToken.encodeTerms] at h

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
