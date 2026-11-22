/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.RealArithmetic.Basic
public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Policy.BinaryIntUnaryFin

/-!
# Binary encodings of real-arithmetic expressions and formulas

The flat constructor-stream layout is the one used by the formal abstract of
`edemaine/lean-canny` at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
Integer constants use binary magnitudes and variables use unary ranks. The dimension is a
fixed parameter to each embedding; it is not a separate field in the encoded word.
Constructor tokens are framed individually; comparisons carry complete encoded terms.
The generated constructor, projection and injectivity APIs come from `derive_encoding`.

## Main definitions

* `Cslib.Logic.RealArithmetic.encTerm`: binary-integer/unary-variable expression encoding.
* `Cslib.Logic.RealArithmetic.encFormula`: Boolean formulas over those encoded expressions.
-/

public section
namespace Cslib.Logic.RealArithmetic

open Turing.MultiTapeTM
open scoped Turing.MultiTapeTM.EncodingPolicy.BinaryIntUnaryFin

/-- Flat constructor stream with binary integer constants and unary variable ranks. -/
derive_encoding encTerm (n : ℕ) : Term n
/-- Flat Boolean constructor stream carrying complete binary-integer arithmetic term words. -/
derive_encoding encFormula (n : ℕ) : Formula n

/-- A prefix constructor token with a natural-number variable rank. The four alternatives are
an integer constant, a variable, addition, and multiplication, in that order. -/
abbrev TermToken := ℤ ⊕ ℕ ⊕ Unit ⊕ Unit

/-- The term constructor tags, followed by a binary integer, unary rank, or empty payload. -/
abbrev encTermToken : TermToken ↪ List Bool :=
  encSum encIntBin (encSum encUnary (encSum encUnit encUnit))

/-- Keep the constructor and payload of a typed token, reading a variable as its unary rank. -/
@[expose] def TermToken.ofFin {n : ℕ} : (ℤ ⊕ Fin n ⊕ Unit ⊕ Unit) → TermToken :=
  Sum.map id (Sum.map Fin.val id)

/-- A prefix formula token. The alternatives are falsity, equality to zero, strict inequality
to zero, negation, conjunction, and disjunction. Comparison tokens carry a complete term word. -/
abbrev FormulaToken := Unit ⊕ List Bool ⊕ List Bool ⊕ Unit ⊕ Unit ⊕ Unit

/-- Encode the formula constructor tags followed by the term word or empty payload. -/
abbrev encFormulaToken : FormulaToken ↪ List Bool :=
  encSum encUnit (encSum encBits (encSum encBits (encSum encUnit (encSum encUnit encUnit))))

/-- Keep a typed formula token's constructor and encode any comparison term as a word. -/
@[expose] def FormulaToken.encodeTerms {n : ℕ} :
    (Unit ⊕ Term n ⊕ Term n ⊕ Unit ⊕ Unit ⊕ Unit) → FormulaToken :=
  Sum.map id (Sum.map (encTerm n) (Sum.map (encTerm n) id))

/-- Preserving variable ranks preserves every bit of a term's encoding. -/
theorem encTerm_rename {n m : ℕ} (f : Fin n → Fin m)
    (hf : ∀ i, (f i).val = i.val) (t : Term n) :
    encTerm m (t.rename f) = encTerm n t := by
  induction t <;> simp_all [Term.rename, encTermTokenEncoding,
    Turing.MultiTapeTM.EncodingPolicy.BinaryIntUnaryFin.fin]

/-- Preserving variable ranks preserves every bit of a formula's encoding. -/
theorem encFormula_rename {n m : ℕ} (f : Fin n → Fin m)
    (hf : ∀ i, (f i).val = i.val) (p : Formula n) :
    encFormula m (p.rename f) = encFormula n p := by
  induction p <;> simp_all [Formula.rename, encFormulaTokenEncoding, encTerm_rename f hf]

end Cslib.Logic.RealArithmetic
