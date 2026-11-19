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
public meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode

/-! Semantic edge cases and strict decoding for the ported real-arithmetic input convention. -/

public section
namespace CslibFrontierTests.RealArithmetic

open Cslib.Logic.RealArithmetic Cslib.Complexity Turing.MultiTapeTM

-- The grammar includes strict inequality and disjunction, negative coefficients and negation.
def sentence : Formula 0 :=
  .or (.ltZero (.add (.const (-37)) (.const 12)))
    (.and (.eqZero (.mul (.const 0) (.const 91))) (.not .false))

-- An asymmetric two-block formula checks that existential coordinates come first.
example : (Formula.eqZero (n := 2) (.var 0)).existsForallSolutionSet
    (r := 1) (s := 1) = {x | x 0 = 0} := by
  ext x
  simp [Formula.existsForallSolutionSet, Formula.solutionSet, Term.eval, Fin.addCases]

-- A polynomial equation can fail for every real assignment.
example : ¬ (Formula.eqZero (n := 1)
    (.add (.mul (.var 0) (.var 0)) (.const 1))).solutionSet.Nonempty := by
  rintro ⟨x, hx⟩
  simp only [Formula.solutionSet, Set.mem_ofPred_eq, Term.eval] at hx
  norm_num at hx
  nlinarith [sq_nonneg (x 0)]

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
