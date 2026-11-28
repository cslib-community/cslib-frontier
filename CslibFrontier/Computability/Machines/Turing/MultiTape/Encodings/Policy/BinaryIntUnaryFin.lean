/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Derive
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-!
# An opt-in binary-integer and unary-index encoding policy

`open scoped Turing.MultiTapeTM.EncodingPolicy.BinaryIntUnaryFin` selects `encIntBin` for integers,
`encFinEnum (Fin n)` for unary variable ranks, `encBool` for Booleans, and `encUnit` for unit.
Importing this module alone activates no policy. No natural-number, list or arbitrary finite-type
encoding is selected. Local embedding parameters override these rules. Other active registered
choices of the same field type cause ambiguity rather than silently changing the layout.

The index bound `n` is a uniform, fixed parameter, not a runtime argument. Unary rank encodings do
not certify an efficient algorithm uniform in a growing `n`. These choices register embeddings;
they do not automatically supply partial decoders.
-/

@[expose] public section

namespace Turing.MultiTapeTM.EncodingPolicy.BinaryIntUnaryFin

attribute [scoped encoding_rule] encIntBin encBool encUnit

/-- Unary rank in the constructive enumeration of `Fin n`. -/
@[scoped encoding_rule] abbrev fin (n : ℕ) : Fin n ↪ List Bool := encFinEnum (Fin n)

end Turing.MultiTapeTM.EncodingPolicy.BinaryIntUnaryFin
