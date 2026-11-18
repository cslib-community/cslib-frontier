/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (derive_encoding fixture)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Derive
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Policy.BinaryIntUnaryFin
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode

/-!
# Encoding selection for complete arithmetic syntax

The grammar copies `LeanCanny/Abstract.lean` at
`f119e2398d7cd7b3656acaebf2d653fa0499cc48`: all term and formula constructors are retained.
The tested encoding is the library's constructor stream, rather than that project's shared
term/formula token alphabet. Explicit declarations check the selected scalar layouts.
-/

public section
namespace CslibFrontierTests.DeriveEncoding

open Turing.MultiTapeTM
open scoped Turing.MultiTapeTM.EncodingPolicy.BinaryIntUnaryFin

/-- A bare nonrecursive declaration retains the original sum-of-tuples interface. -/
inductive Message where
  | idle : Message
  | payload : Bool → ℤ → Message

derive_encoding encMessage : Message

enc_inductive explicitMessage : Message where
  | idle
  | payload : encBool, encIntBin

example (message : Message) : encMessage message = explicitMessage message := by
  cases message <;> rfl

-- Parentheses must not select the recursive stream backend for this same type.
derive_encoding encParenthesizedMessage : (Message)

example (message : Message) : encParenthesizedMessage message = explicitMessage message := by
  cases message <;> rfl

/-- Integer polynomial expressions in a fixed number of variables. -/
inductive Term (n : ℕ) where
  | const : ℤ → Term n
  | var : Fin n → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n

derive_encoding encTerm (n : ℕ) : Term n

enc_inductive explicitTerm (n : ℕ) : Term n where
  | const : encIntBin
  | var : (encFinEnum (Fin n))
  | add : _, _
  | mul : _, _

/-- Boolean formulas include both comparisons and all three Boolean connectives. -/
inductive Formula (n : ℕ) where
  | false : Formula n
  | eqZero : Term n → Formula n
  | ltZero : Term n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n

derive_encoding encFormula (n : ℕ) : Formula n

enc_inductive explicitFormula (n : ℕ) : Formula n where
  | false
  | eqZero : (explicitTerm n)
  | ltZero : (explicitTerm n)
  | not : _
  | and : _, _
  | or : _, _

/-- Three recursive children are interspersed with two different scalar fields. -/
inductive Tree (α : Type) where
  | empty : Tree α
  | leaf : α → Tree α
  | fork : Tree α → Bool → Tree α → α → Tree α → Tree α

derive_encoding encTree (α : Type) (eα : α ↪ List Bool) : Tree α

enc_inductive explicitTree (α : Type) (eα : α ↪ List Bool) : Tree α where
  | empty
  | leaf : eα
  | fork : _, encBool, _, eα, _

/-- Resolving a previously derived family must recursively supply its scalar embedding. -/
inductive ForestNode (α : Type) where
  | empty : ForestNode α
  | node : Tree α → ForestNode α → ForestNode α

derive_encoding encForestNode (α : Type) (eα : α ↪ List Bool) : ForestNode α

enc_inductive explicitForestNode (α : Type) (eα : α ↪ List Bool) : ForestNode α where
  | empty
  | node : (explicitTree α eα), _

/-- Automatic scalar selection preserves the fully explicit term words. -/
theorem encTerm_eq_explicitTerm (n : ℕ) (t : Term n) :
    encTerm n t = explicitTerm n t := by
  induction t <;> simp_all [encTermTokenEncoding, explicitTermTokenEncoding]

/-- Local scalar parameters preserve the fully explicit tree words. -/
theorem encTree_eq_explicitTree (α : Type) (eα : α ↪ List Bool) (t : Tree α) :
    encTree α eα t = explicitTree α eα t := by
  induction t <;> simp_all [encTreeTokenEncoding, explicitTreeTokenEncoding]

example (n : ℕ) (f : Formula n) : encFormula n f = explicitFormula n f := by
  induction f <;>
    simp_all [encFormulaTokenEncoding, explicitFormulaTokenEncoding, encTerm_eq_explicitTerm]

example (α : Type) (eα : α ↪ List Bool) (f : ForestNode α) :
    encForestNode α eα f = explicitForestNode α eα f := by
  induction f <;>
    simp_all [encForestNodeTokenEncoding, explicitForestNodeTokenEncoding, encTree_eq_explicitTree]

/-- The zero-variable grammar uses the empty scalar decoder for `Fin 0`. -/
def termCodec : PartialDecoder (encTerm 0) :=
  encTerm_decoder 0 (.ofDecoder Decoder.intBin) (.empty _)

/-- Both comparison constructors need the selected term decoder. -/
def formulaCodec : PartialDecoder (encFormula 0) :=
  encFormula_decoder 0 termCodec termCodec

/-- A nontrivial formula exercises the two constructors absent from the older fixture. -/
def sampleFormula : Formula 0 :=
  .or (.ltZero (.add (.const (-37)) (.const 12)))
    (.and (.eqZero (.mul (.const 0) (.const 91))) (.not .false))

set_option linter.hashCommand false in
#guard (formulaCodec.decode (encFormula 0 sampleFormula)).isSome

set_option linter.hashCommand false in
#guard (formulaCodec.decode (encFormula 0 sampleFormula ++ [true])).isNone

namespace LocalOverride

-- A local embedding wins over the policy's unary finite encoding.
derive_encoding encTermOverride (n : ℕ) (eFin : Fin n ↪ List Bool) : Term n

enc_inductive explicitOverride (n : ℕ) (eFin : Fin n ↪ List Bool) : Term n where
  | const : encIntBin
  | var : eFin
  | add : _, _
  | mul : _, _

example (n : ℕ) (eFin : Fin n ↪ List Bool) (t : Term n) :
    encTermOverride n eFin t = explicitOverride n eFin t := by
  induction t <;> simp_all [encTermOverrideTokenEncoding, explicitOverrideTokenEncoding]

end LocalOverride

end CslibFrontierTests.DeriveEncoding
