/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (test fixture)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Inductive
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
meta import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode

public section
namespace CslibFrontierTests.RecursiveInductiveEncoding
open Turing.MultiTapeTM

/-- Integer arithmetic syntax with a uniform variable bound. -/
inductive Term (n : ℕ) where
  | const : ℤ → Term n
  | var : Fin n → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n

enc_inductive encTerm (n : ℕ) : Term n where
  | const : encIntBin
  | var : (encFinEnum (Fin n))
  | add : _, _
  | mul : _, _

/-- Formulas use the previously encoded term family as a scalar payload. -/
inductive Formula (n : ℕ) where
  | false : Formula n
  | eqZero : Term n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n

enc_inductive encFormula (n : ℕ) : Formula n where
  | false
  | eqZero : (encTerm n)
  | not : _
  | and : _, _

/-- A polymorphic grammar with mixed scalar fields and three recursive operands. -/
inductive Tree (α : Type) where
  | empty : Tree α
  | leaf : α → Tree α
  | fork : Tree α → Bool → Tree α → α → Tree α → Tree α

enc_inductive encTree (α : Type) (eα : α ↪ List Bool) : Tree α where
  | empty
  | leaf : eα
  | fork : _, encBool, _, eα, _

example {n : ℕ} (t : Term n) : encTerm_decodeTokens n (encTerm_tokens n t) = some t :=
  encTerm_decodeTokens_tokens n t

example (f : Formula 0) :
    (encFormula 0 f).length ≤ 11 * encFormula_nodes 0 f + 4 * encFormula_leafSize 0 f :=
  encFormula_length_le 0 f

example (α : Type) (eα : α ↪ List Bool) (t : Tree α) :
    (encTree α eα t).length ≤ 11 * encTree_nodes α eα t + 4 * encTree_leafSize α eα t :=
  encTree_length_le α eα t

-- A nonempty trailing constructor cannot be accepted as a single complete value.
example : encFormula_decodeTokens 0
    (encFormula_tokens 0 .false ++ encFormula_tokens 0 .false) = none := by decide

example : encFormula_decodeTokens 0 [] = none := by decide

example : encFormula_decodeTokens 0
    [Sum.inr (Sum.inr (Sum.inr ()))] = none := by decide

/-- A spine forces every child encoding through the first recursive field. -/
def spine : ℕ → Tree Bool
  | 0 => .empty
  | n + 1 => .fork (spine n) false .empty true .empty

/-- The first-child spine has exactly linear size, including all tags and frames. -/
theorem spine_encoded_length (n : ℕ) :
    (encTree Bool encBool (spine n)).length = 19 * n + 3 := by
  induction n with
  | zero => simp [spine, encTreeTokenEncoding]
  | succ n ih => simp [spine, encTreeTokenEncoding, ih, Nat.mul_add]

example : encFormula 0 .false = [true, false, false] := by
  simp [encFormulaTokenEncoding]

example (α : Type) (encoding : α ↪ List Bool) (left middle right : Tree α)
    (flag : Bool) (label : α) :
    encTree α encoding (.fork left flag middle label right) =
      frame (true :: true :: encPair encBool encoding (flag, label)) ++
        encTree α encoding left ++ encTree α encoding middle ++ encTree α encoding right := by
  simp [encTreeTokenEncoding, List.append_assoc]

-- Repeated framing of the whole first child would exceed this bound by depth 20.
set_option linter.hashCommand false in
#guard (encTree Bool encBool (spine 128)).length ≤ 10000

set_option linter.hashCommand false in
#guard (encTree Bool encBool (spine 20)).length ≤ 2000

/-- Higher-universe phantom parameters do not enlarge the encoded value type. -/
inductive Phantom (α : Type 1) : Type where
  | stop : Phantom α
  | next : Phantom α → Phantom α

enc_inductive encPhantom (α : Type 1) : Phantom α where
  | stop
  | next : _

example (α : Type 1) (value : Phantom α) :
    (encPhantom α value).length ≤ 5 * encPhantom_nodes α value +
      4 * encPhantom_leafSize α value := encPhantom_length_le α value

/-- The zero-variable family needs no inhabitant of its variable type. -/
def termCodecZero : PartialDecoder (encTerm 0) :=
  encTerm_decoder 0 (.ofDecoder Decoder.intBin) (.empty _)

/-- Formulas decode through the previously generated term codec. -/
def formulaCodecZero : PartialDecoder (encFormula 0) :=
  encFormula_decoder 0 termCodecZero

/-- The same scalar decoder is supplied explicitly at each Boolean field occurrence. -/
def treeCodec : PartialDecoder (encTree Bool encBool) :=
  encTree_decoder Bool encBool (.ofDecoder Decoder.bool) (.ofDecoder Decoder.bool)
    (.ofDecoder Decoder.bool)

example (f : Formula 0) : formulaCodecZero.decode (encFormula 0 f) = some f :=
  formulaCodecZero.decode_enc f

example (word : List Bool) : formulaCodecZero.decode word = none ↔
    ¬ ∃ f, encFormula 0 f = word := formulaCodecZero.decode_eq_none_iff word

example : ComputableInPolyTime formulaCodecZero.decode encBits (encOption (encFormula 0)) :=
  formulaCodecZero.computable

-- This is a value-parameter family with an inhabited variable type as well.
def finOneCodec : PartialDecoder (encFinEnum (Fin 1)) :=
  .checked (fun _ => some 0) (fun value => by
    have : value = 0 := Subsingleton.elim _ _
    subst value
    rfl)
    (ComputableInPolyTime.const _)

def termCodecOne : PartialDecoder (encTerm 1) :=
  encTerm_decoder 1 (.ofDecoder Decoder.intBin) finOneCodec

set_option linter.hashCommand false in
#guard (termCodecOne.decode (encTerm 1 (.add (.var 0) (.const (-37))))).isSome

set_option linter.hashCommand false in
#guard (formulaCodecZero.decode
  (encFormula 0 (.and (.eqZero (.mul (.const (-2)) (.const 13))) (.not .false)))).isSome

set_option linter.hashCommand false in
#guard (treeCodec.decode (encTree Bool encBool
  (.fork (.leaf false) true (.fork .empty false (.leaf true) true .empty)
    false (.leaf true)))).isSome

-- Typed parsing and real bit decoding both work on a deep three-child spine.
set_option linter.hashCommand false in
#guard (encTree_decodeTokens Bool encBool (encTree_tokens Bool encBool (spine 128))).map
  (encTree_nodes Bool encBool) == some 385

set_option linter.hashCommand false in
#guard (treeCodec.decode (encTree Bool encBool (spine 64))).map
  (encTree_nodes Bool encBool) == some 193

set_option linter.hashCommand false in
#guard (formulaCodecZero.decode []).isNone

set_option linter.hashCommand false in
#guard (formulaCodecZero.decode (encFormula 0 .false ++ encFormula 0 .false)).isNone

-- Incomplete framing and noncanonical scalar/tag words are rejected.
set_option linter.hashCommand false in
#guard (treeCodec.decode [true]).isNone

set_option linter.hashCommand false in
#guard (treeCodec.decode (encTree Bool encBool (.leaf true) ++ [true])).isNone

-- A complete leaf frame with an overlong Boolean scalar is still malformed.
set_option linter.hashCommand false in
#guard (treeCodec.decode (frame [true, false, true, true])).isNone

set_option linter.hashCommand false in
#guard (treeCodec.decode (frame [])).isNone

-- Removing the final complete child frame leaves a well-framed but incomplete tree.
set_option linter.hashCommand false in
#guard let word := encTree Bool encBool (.fork .empty false .empty true .empty);
  (treeCodec.decode (word.take (word.length - 3))).isNone

namespace BinderHygiene

-- Uniform parameters may use the generator's customary operand and resource-binder names.
enc_inductive encCollision (x0 : ℕ) (γ : ℕ) (encIn : ℕ) : Term (x0 + γ + encIn) where
  | const : encIntBin
  | var : (encFinEnum (Fin (x0 + γ + encIn)))
  | add : _, _
  | mul : _, _

end BinderHygiene

end CslibFrontierTests.RecursiveInductiveEncoding
