/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.RealArithmetic.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# Existential and existential–universal real truth problems

These are the binary languages in `edemaine/lean-canny`'s formal abstract at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. The input is an integer-polynomial Boolean
formula encoded by a flat constructor stream, with binary integer magnitudes and unary
variable indices. The two-block language prefixes the formula word with a framed unary
existential-block length. Neither problem promises well-formedness: only words in the image
of a true sentence are accepted. This module provides definitions, not complexity bounds.

## Main definitions

* `Cslib.Complexity.ETR`: satisfiable existential real formulas.
* `Cslib.Complexity.ExistsForallTheory`: true existential–universal real sentences.
-/

public section
namespace Cslib.Complexity

open Logic.RealArithmetic Turing.MultiTapeTM

/-- Encodings of satisfiable integer-polynomial formulas, in any finite dimension. -/
@[expose] def ETR : Set (List Bool) :=
  ⋃ n, {p : Formula n | p.solutionSet.Nonempty}.image (encFormula n)

/-- True existential–universal real sentences. The unary existential-block length is framed
before the formula word. Existential variables precede universal variables; either block may
be empty. Noncanonical and malformed words are rejected. -/
@[expose] def ExistsForallTheory : Set (List Bool) :=
  ⋃ r, ⋃ s, {p : Formula (r + s) | p.existsForallSolutionSet.Nonempty}.image (fun p =>
    encPair encUnary encBits (r, encFormula (r + s) p))

end Cslib.Complexity
