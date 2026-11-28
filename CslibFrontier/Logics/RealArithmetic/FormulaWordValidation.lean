/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.RealArithmetic.FormulaTokenDecoding
public import CslibFrontier.Logics.RealArithmetic.TokenEvaluationPolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Basic.Sign.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Recursive

/-!
# Polynomial-time syntax validation for real-arithmetic formula words

This adapts `LeanCanny.ETR.Grammar.recognizeFormula` from lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183` to the frontier formula encoding. The strict
formula-token decoder handles framing. The recursive-encoding checker verifies that the
constructor stream describes one tree, and term recognition at modulus one checks the comparison
payloads. Valid words encode formulas in the dimension given by their length.

The total view adapts `LeanCanny.ETR.FormulaView` at the same revision. It preserves the exact
bits of valid encodings and gives malformed words the semantics of falsity.
Its indexed token reader adapts the constructor and term-word access of
`LeanCanny.ETR.FormulaBooleanCircuitSource` to the frontier prefix token list.
Subtree spans locate the second operand with the native splitter for framed prefix tokens.
The child-index query returns the operands in their syntactic order.
The indexed gate operation adapts the local wire evaluation of
`LeanCanny.ETR.FormulaBooleanCircuitCorrect` at the same revision. It reads comparison signs
from a supplied term-word interpretation and connective operands from supplied wire values.
Comparison requests retain the exact term word and the required sign.
The Boolean part of gate evaluation has a polynomial-time certificate given the comparison
answer and access to the operand values.
-/

public section

namespace Cslib.Logic.RealArithmetic

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

private def validTermWord (word : List Bool) : Bool :=
  (Term.evalTermWord 1 [] word).isSome

private def inspectToken : FormulaToken → ℕ × Bool :=
  Sum.elim (fun _ => (0, true))
    (Sum.elim (fun word => (0, validTermWord word))
      (Sum.elim (fun word => (0, validTermWord word))
        (Sum.elim (fun _ => (1, true))
          (Sum.elim (fun _ => (2, true)) (fun _ => (2, true))))))

/-- Check that a raw bit word encodes one formula, including every comparison's term syntax. -/
def validFormulaWord (word : List Bool) : Bool :=
  (formulaTokensDecoder.decode word).elim false fun tokens =>
    RecursiveEncoding.isTree (fun token => (inspectToken token).1) tokens &&
      tokens.all fun token => (inspectToken token).2

private theorem validTermWord_eq_true_iff {word : List Bool} :
    validTermWord word = true ↔ ∃ t : Term word.length, encTerm word.length t = word := by
  constructor
  · intro h
    obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨t, ht, _⟩ := Term.evalTermWord_eq_some_iff.mp hvalue
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    rw [← ht, validTermWord, Term.evalTermWord_encTerm]
    rfl

private theorem inspectToken_encodeTerms_arity {n : ℕ}
    (token : Unit ⊕ Term n ⊕ Term n ⊕ Unit ⊕ Unit ⊕ Unit) :
    (inspectToken (FormulaToken.encodeTerms token)).1 = encFormula_arity n token := by
  rcases token with _ | (_ | (_ | (_ | (_ | _)))) <;> rfl

private theorem inspectToken_encodeTerms_valid {n : ℕ}
    (token : Unit ⊕ Term n ⊕ Term n ⊕ Unit ⊕ Unit ⊕ Unit) :
    (inspectToken (FormulaToken.encodeTerms token)).2 = true := by
  rcases token with _ | (_ | (_ | (_ | (_ | _)))) <;>
    simp only [FormulaToken.encodeTerms, Sum.map_inr, Sum.map_inl, inspectToken, Sum.elim_inr,
      Sum.elim_inl, id_eq, validTermWord, Term.evalTermWord_encTerm, Option.isSome_some]

private theorem formulaForest_map_encodeTerms {n roots : ℕ}
    (tokens : List (Unit ⊕ Term n ⊕ Term n ⊕ Unit ⊕ Unit ⊕ Unit)) :
    RecursiveEncoding.Forest (fun token => (inspectToken token).1) roots
        (tokens.map FormulaToken.encodeTerms) ↔
      RecursiveEncoding.Forest (encFormula_arity n) roots tokens := by
  induction tokens generalizing roots with
  | nil =>
    constructor <;> intro h <;> cases h <;> exact .nil
  | cons token tokens ih =>
    simp only [List.map_cons]
    constructor
    · intro h
      cases h with
      | cons h =>
        rw [inspectToken_encodeTerms_arity] at h
        exact .cons (ih.mp h)
    · intro h
      cases h with
      | cons h =>
        apply RecursiveEncoding.Forest.cons
        rw [inspectToken_encodeTerms_arity]
        exact ih.mpr h

/-- A canonical formula encoding passes the syntax validator in any variable dimension. -/
theorem validFormulaWord_encFormula {n : ℕ} (p : Formula n) :
    validFormulaWord (encFormula n p) = true := by
  rw [validFormulaWord, formulaTokensDecoder_decode_encFormula, Option.elim_some,
    Bool.and_eq_true, RecursiveEncoding.isTree_eq_true_iff, formulaForest_map_encodeTerms,
    List.all_eq_true]
  refine ⟨encFormula_tokens_forest n p, ?_⟩
  intro token htoken
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp htoken
  exact inspectToken_encodeTerms_valid source

private theorem exists_encodeTerms_of_valid {n : ℕ} (token : FormulaToken)
    (hvalid : (inspectToken token).2 = true)
    (hlen : ∀ word, token = .inr (.inl word) ∨ token = .inr (.inr (.inl word)) →
      word.length ≤ n) :
    ∃ source : Unit ⊕ Term n ⊕ Term n ⊕ Unit ⊕ Unit ⊕ Unit,
      FormulaToken.encodeTerms source = token := by
  have liftTerm {word : List Bool} (h : validTermWord word = true) (hw : word.length ≤ n) :
      ∃ t : Term n, encTerm n t = word := by
    obtain ⟨t, ht⟩ := validTermWord_eq_true_iff.mp h
    exact ⟨t.rename (Fin.castLE hw), (encTerm_rename (Fin.castLE hw) (fun _ => rfl) t).trans ht⟩
  rcases token with u | (word | (word | tail))
  · exact ⟨.inl u, rfl⟩
  · obtain ⟨t, ht⟩ := liftTerm hvalid (hlen word (Or.inl rfl))
    exact ⟨.inr (.inl t), congrArg (fun w => (.inr (.inl w) : FormulaToken)) ht⟩
  · obtain ⟨t, ht⟩ := liftTerm hvalid (hlen word (Or.inr rfl))
    exact ⟨.inr (.inr (.inl t)), congrArg (fun w => (.inr (.inr (.inl w)) : FormulaToken)) ht⟩
  · exact ⟨.inr (.inr (.inr tail)), rfl⟩

private theorem exists_map_encodeTerms {n : ℕ} (tokens : List FormulaToken)
    (h : ∀ token ∈ tokens, ∃ source : Unit ⊕ Term n ⊕ Term n ⊕ Unit ⊕ Unit ⊕ Unit,
      FormulaToken.encodeTerms source = token) :
    ∃ sources : List (Unit ⊕ Term n ⊕ Term n ⊕ Unit ⊕ Unit ⊕ Unit),
      sources.map FormulaToken.encodeTerms = tokens := by
  induction tokens with
  | nil => exact ⟨[], rfl⟩
  | cons token tokens ih =>
    obtain ⟨source, hsource⟩ := h token (List.mem_cons_self ..)
    obtain ⟨sources, hsources⟩ := ih fun t ht => h t (List.mem_cons_of_mem _ ht)
    exact ⟨source :: sources, by rw [List.map_cons, hsource, hsources]⟩

/-- Validation recognizes exactly the formula encodings, using the input length as a variable
dimension large enough to contain every unary variable rank in the word. -/
theorem validFormulaWord_eq_true_iff {word : List Bool} :
    validFormulaWord word = true ↔ ∃ p : Formula word.length, encFormula word.length p = word := by
  constructor
  · intro hvalid
    cases hdecode : formulaTokensDecoder.decode word with
    | none => simp [validFormulaWord, hdecode] at hvalid
    | some tokens =>
      rw [validFormulaWord, hdecode, Option.elim_some, Bool.and_eq_true,
        RecursiveEncoding.isTree_eq_true_iff, List.all_eq_true] at hvalid
      obtain ⟨hforest, hterms⟩ := hvalid
      obtain ⟨sources, rfl⟩ := exists_map_encodeTerms tokens (n := word.length)
        fun token htoken => exists_encodeTerms_of_valid token (hterms token htoken)
          fun term ht => (formulaTermWord_length_lt_of_decode hdecode
            (ht.imp (· ▸ htoken) (· ▸ htoken))).le
      have htree := RecursiveEncoding.isTree_eq_true_iff.mpr
        ((formulaForest_map_encodeTerms sources).mp hforest)
      have hparse := encFormula_decodeTokens_map word.length sources
      simp only [htree, ite_true] at hparse
      obtain ⟨p, _, hp⟩ := Option.map_eq_some_iff.mp hparse
      refine ⟨p, ?_⟩
      have hcanonical := formulaTokensDecoder_decode_encFormula p
      rw [hp] at hcanonical
      exact ((formulaTokensDecoder.decode_eq_some_iff _ _).1 hcanonical).symm.trans
        ((formulaTokensDecoder.decode_eq_some_iff _ _).1 hdecode)
  · rintro ⟨p, hp⟩
    exact (congrArg validFormulaWord hp).symm.trans (validFormulaWord_encFormula p)

private theorem inspectToken_polyTime :
    ComputableInPolyTime inspectToken encFormulaToken (encPair encUnary encBool) := by
  have hterm : ComputableInPolyTime validTermWord encBits encBool :=
    optionIsSome (Term.evalTermWord_polyTime (.const 1) (fun _ => by decide) (.const []) id')
  have hcompare : ComputableInPolyTime (fun word => (0, validTermWord word))
      encBits (encPair encUnary encBool) :=
    (const 0).prod hterm
  exact sumElim (const (0, true))
    (sumElim hcompare
      (sumElim hcompare
        (sumElim (const (1, true))
          (sumElim (const (2, true)) (const (2, true))))))

private theorem inspectToken_arity_le (token : FormulaToken) : (inspectToken token).1 ≤ 2 := by
  rcases token with _ | (_ | (_ | (_ | (_ | _)))) <;>
    simp only [inspectToken, Sum.elim_inl, Sum.elim_inr, Nat.zero_le, Nat.reduceLeDiff, le_refl]

/-- Syntax validation runs in polynomial time uniformly in the raw bit word. -/
theorem validFormulaWord_polyTime :
    ComputableInPolyTime validFormulaWord encBits encBool := by
  let encTokens := encList encFormulaToken
  have harity := (fst encUnary encBool).comp inspectToken_polyTime
  have hshape := RecursiveEncoding.isTree_polyTime harity inspectToken_arity_le
  have hvalid := (snd encUnary encBool).comp inspectToken_polyTime
  have hall := allWith (hvalid.comp (snd encUnit encFormulaToken)) (const ()) id'
  exact optionElimWithInput formulaTokensDecoder.computable (const false)
    ((bool_and' hshape hall).comp (snd encBits encTokens))

/-- Preserve a valid formula word and replace a malformed word with the encoding of falsity. -/
@[expose] def normalizeFormulaWord (word : List Bool) : List Bool :=
  if validFormulaWord word then word else encFormula 0 .false

/-- The total formula denoted by a word, using its length for the ambient variable dimension.
Malformed words denote falsity. -/
noncomputable def Formula.ofWord (word : List Bool) : Formula word.length :=
  if h : validFormulaWord word = true then
    Classical.choose (validFormulaWord_eq_true_iff.mp h)
  else .false

/-- The formula view of a malformed word is falsity. -/
theorem Formula.ofWord_of_not_valid {word : List Bool} (h : validFormulaWord word ≠ true) :
    ofWord word = .false := by
  rw [ofWord, dite_eq_right h]

/-- The bit-level normalization computes the exact encoding of the total formula view. -/
theorem encFormula_ofWord (word : List Bool) :
    encFormula word.length (Formula.ofWord word) = normalizeFormulaWord word := by
  by_cases h : validFormulaWord word = true
  · rw [Formula.ofWord, dite_eq_left h, normalizeFormulaWord, ite_eq_left h]
    exact Classical.choose_spec (validFormulaWord_eq_true_iff.mp h)
  · rw [Formula.ofWord_of_not_valid h, normalizeFormulaWord, ite_eq_right h]
    rfl

/-- Formula word normalization is uniformly polynomial time. -/
theorem normalizeFormulaWord_polyTime :
    ComputableInPolyTime normalizeFormulaWord encBits encBits :=
  validFormulaWord_polyTime.ite' id' (const (encFormula 0 .false))

/-- Re-encoding the total formula view is uniformly polynomial time on raw bit words. -/
theorem encFormula_ofWord_polyTime :
    ComputableInPolyTime (fun word => encFormula word.length (Formula.ofWord word))
      encBits encBits :=
  normalizeFormulaWord_polyTime.of_enc_eq fun word => congrArg encBits (encFormula_ofWord word)

/-- The prefix tokens of the total formula view, retaining the original comparison term words. -/
@[expose] def formulaWordTokens (word : List Bool) : List FormulaToken :=
  (formulaTokensDecoder.decode (normalizeFormulaWord word)).getD []

/-- The executable token stream agrees with the typed formula view on every input. -/
theorem formulaWordTokens_eq (word : List Bool) :
    formulaWordTokens word =
      (encFormula_tokens word.length (Formula.ofWord word)).map FormulaToken.encodeTerms := by
  rw [formulaWordTokens, ← encFormula_ofWord, formulaTokensDecoder_decode_encFormula]
  rfl

/-- Each token of a valid word occupies at least one bit. Malformed words have one falsity
token, including for the empty input. -/
theorem formulaWordTokens_length_le (word : List Bool) :
    (formulaWordTokens word).length ≤ max 1 word.length := by
  by_cases h : validFormulaWord word = true
  · have hnormalize : normalizeFormulaWord word = word := ite_eq_left h
    have hdecode := formulaTokensDecoder_decode_encFormula (Formula.ofWord word)
    rw [encFormula_ofWord, hnormalize, ← formulaWordTokens_eq] at hdecode
    have hword := (formulaTokensDecoder.decode_eq_some_iff _ _).mp hdecode
    calc
      (formulaWordTokens word).length ≤ (encList encFormulaToken (formulaWordTokens word)).length :=
        SizedListEncoding.length_le (encA := encFormulaToken) (encL := encList encFormulaToken) _
      _ ≤ max 1 word.length := by
        rw [hword]
        exact le_max_right ..
  · rw [formulaWordTokens_eq, Formula.ofWord_of_not_valid h]
    exact le_max_left 1 word.length

/-- Recover the framed prefix token stream in polynomial time. -/
theorem formulaWordTokens_polyTime :
    ComputableInPolyTime formulaWordTokens encBits (encList encFormulaToken) :=
  optionGetDWithInput (formulaTokensDecoder.computable.comp normalizeFormulaWord_polyTime)
    (const [])

/-- Read a prefix token by position. Positions beyond the stream return the falsity token. -/
@[expose] def formulaWordTokenAt (word : List Bool) (index : ℕ) : FormulaToken :=
  (formulaWordTokens word).getD index (.inl ())

/-- Token lookup takes polynomial time in the raw word and binary index. -/
theorem formulaWordTokenAt_polyTime :
    ComputableInPolyTime (fun p : List Bool × ℕ => formulaWordTokenAt p.1 p.2)
      (encPair encBits encNat) encFormulaToken :=
  listGetD_binary (encA := encFormulaToken) (.inl ())
    (formulaWordTokens_polyTime.comp (fst encBits encNat)) (snd encBits encNat)

private theorem formulaWordTokenAt_append {word : List Bool} {before rest : List FormulaToken}
    {token : FormulaToken} (h : formulaWordTokens word = before ++ token :: rest) :
    formulaWordTokenAt word before.length = token := by
  rw [formulaWordTokenAt, h, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
    Nat.sub_self]
  rfl

/-- The number of prefix tokens in the subtree beginning at this index of the total formula
view. A position outside the token stream has no subtree. -/
def formulaSubtreeSizeAt (word : List Bool) (index : ℕ) : Option ℕ :=
  (RecursiveEncoding.splitTree (fun token => (inspectToken token).1)
    ((formulaWordTokens word).drop index)).map fun split => split.1.length

/-- A serialized subtree starting at the given position is consumed exactly, leaving any
following tokens out of the span. -/
theorem formulaSubtreeSizeAt_of_prefix {n : ℕ} {word : List Bool} (p : Formula n)
    (before after : List FormulaToken)
    (h : formulaWordTokens word =
      before ++ ((encFormula_tokens n p).map FormulaToken.encodeTerms ++ after)) :
    formulaSubtreeSizeAt word before.length = some (encFormula_tokens n p).length := by
  have htree := (formulaForest_map_encodeTerms (encFormula_tokens n p)).mpr
    (encFormula_tokens_forest n p)
  rw [formulaSubtreeSizeAt, h, List.drop_left, RecursiveEncoding.splitTree_append htree,
    Option.map_some, List.length_map]

/-- Subtree span takes polynomial time with a binary index and an optional binary result.
The index is capped by the number of tokens before converting it to unary for list dropping. -/
theorem formulaSubtreeSizeAt_polyTime :
    ComputableInPolyTime (fun p : List Bool × ℕ => formulaSubtreeSizeAt p.1 p.2)
      (encPair encBits encNat) (encOption encNat) := by
  let encTokens := encList encFormulaToken
  have ht := formulaWordTokens_polyTime.comp (fst encBits encNat)
  have hi := snd encBits encNat
  have hcap := binary_min_unary' ((length_list encFormulaToken).comp ht) hi
  have hdrop : ComputableInPolyTime (fun p : List Bool × ℕ => (formulaWordTokens p.1).drop p.2)
      (encPair encBits encNat) encTokens := by
    refine (listDropWithInput ht hcap).of_enc_eq ?_
    rintro ⟨word, index⟩
    apply congrArg encTokens
    change (formulaWordTokens word).drop index =
      (formulaWordTokens word).drop (min (formulaWordTokens word).length index)
    rcases le_total index (formulaWordTokens word).length with h | h
    · rw [Nat.min_eq_right h]
    · rw [Nat.min_eq_left h, List.drop_length, List.drop_eq_nil_of_le h]
  have harity := (fst encUnary encBool).comp inspectToken_polyTime
  have hsplit := (RecursiveEncoding.splitTree_polyTime harity inspectToken_arity_le).comp hdrop
  have hsize := unary_to_binary.comp ((length_list encFormulaToken).comp (fst encTokens encTokens))
  exact hsplit.optionMapWithInput
    (hsize.comp (snd (encPair encBits encNat) (encPair encTokens encTokens)))

/-- The immediate child indices of a connective in the prefix stream of the total formula
view, in operand order. Leaf tokens and positions outside the stream have no children. -/
def formulaWordChildIndices (word : List Bool) (index : ℕ) : List ℕ :=
  let arity := (inspectToken (formulaWordTokenAt word index)).1
  let first := index + 1
  if arity = 1 then [first]
  else if arity = 2 then
    (formulaSubtreeSizeAt word first).elim [] fun span => [first, first + span]
  else []

/-- At a serialized subformula, the query returns precisely the starting positions of its
immediate operands. A second operand starts just after the first operand's complete token stream. -/
theorem formulaWordChildIndices_of_prefix {n : ℕ} {word : List Bool} (p : Formula n)
    (before after : List FormulaToken)
    (h : formulaWordTokens word =
      before ++ ((encFormula_tokens n p).map FormulaToken.encodeTerms ++ after)) :
    formulaWordChildIndices word before.length =
      match p with
      | .not _ => [before.length + 1]
      | .and left _ | .or left _ => [before.length + 1,
          before.length + 1 + (encFormula_tokens n left).length]
      | _ => [] := by
  have binary (left right : Formula n) {token : FormulaToken}
      (htokens : formulaWordTokens word = before ++ token ::
        ((encFormula_tokens n left).map FormulaToken.encodeTerms ++
          ((encFormula_tokens n right).map FormulaToken.encodeTerms ++ after)))
      (harity : (inspectToken token).1 = 2) :
      formulaWordChildIndices word before.length =
        [before.length + 1, before.length + 1 + (encFormula_tokens n left).length] := by
    have hspan := formulaSubtreeSizeAt_of_prefix (word := word) left (before ++ [token])
      ((encFormula_tokens n right).map FormulaToken.encodeTerms ++ after)
      (by simpa only [List.append_assoc, List.singleton_append] using htokens)
    simp only [List.length_append, List.length_singleton] at hspan
    simp [formulaWordChildIndices, formulaWordTokenAt_append htokens, harity, hspan]
  cases p
  case false | eqZero | ltZero | not =>
    rw [formulaWordChildIndices, formulaWordTokenAt_append h]
    rfl
  case and left right | or left right =>
    simp only [encFormula_tokens, List.map_cons, List.map_append, List.append_nil,
      List.cons_append, List.append_assoc] at h
    exact binary left right h rfl

/-- Child indices are computable in polynomial time from a raw word and a binary index.
The result is a framed list of up to two binary child positions. -/
theorem formulaWordChildIndices_polyTime :
    ComputableInPolyTime (fun p : List Bool × ℕ => formulaWordChildIndices p.1 p.2)
      (encPair encBits encNat) (encList encNat) := by
  let input := encPair encBits encNat
  have htoken := inspectToken_polyTime.comp formulaWordTokenAt_polyTime
  have harity := (fst encUnary encBool).comp htoken
  have hfirst := binary_add' (snd encBits encNat) (const 1)
  have hspan := formulaSubtreeSizeAt_polyTime.comp ((fst encBits encNat).prod hfirst)
  have hleft := hfirst.comp (fst input encNat)
  have hright := binary_add' hleft (snd input encNat)
  have hchildren := hspan.optionElimWithInput
    (body := fun p span => [p.2 + 1, p.2 + 1 + span])
    (const []) (cons' hleft (cons' hright (const [])))
  exact ite_decide (unary_eq' harity (const 1)) (cons' hfirst (const []))
    (ite_decide (unary_eq' harity (const 2)) hchildren (const []))

/-- A comparison gate's arithmetic query. -/
structure FormulaComparisonRequest where
  /-- The term word carried by the comparison token. -/
  termWord : List Bool
  /-- A strict comparison requests a negative sign. An equality requests zero. -/
  isStrict : Bool
  deriving DecidableEq

/-- Frame the raw term word and append one bit indicating strict inequality. -/
enc_structure encFormulaComparisonRequest : FormulaComparisonRequest where
  termWord : encBits,
  isStrict : encBool

/-- The sign that makes the requested comparison true. -/
@[expose] def FormulaComparisonRequest.requestedSign
    (request : FormulaComparisonRequest) : SignType :=
  if request.isStrict then -1 else 0

private def comparisonRequest : FormulaToken → Option FormulaComparisonRequest
  | .inr (.inl term) => some ⟨term, false⟩
  | .inr (.inr (.inl term)) => some ⟨term, true⟩
  | _ => none

/-- Read the comparison request at a binary index of the total formula view.
Connectives, falsity and out-of-range positions have no request. -/
def formulaWordComparisonRequest (word : List Bool) (index : ℕ) :
    Option FormulaComparisonRequest :=
  comparisonRequest (formulaWordTokenAt word index)

private theorem formulaWordComparisonRequest_index_lt {word : List Bool} {index : ℕ}
    {request : FormulaComparisonRequest} (h : formulaWordComparisonRequest word index =
      some request) : index < (formulaWordTokens word).length := by
  by_contra hindex
  simp [formulaWordComparisonRequest, formulaWordTokenAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (Nat.le_of_not_gt hindex), comparisonRequest] at h

private theorem formulaWordTokenAt_mem {word : List Bool} {index : ℕ}
    (hi : index < (formulaWordTokens word).length) :
    formulaWordTokenAt word index ∈ formulaWordTokens word := by
  rw [formulaWordTokenAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]
  exact List.getElem_mem _

/-- A comparison in the total formula view retains the canonical encoding of a term in
the word's dimension. -/
theorem formulaWordComparisonRequest_termWord_exists {word : List Bool} {index : ℕ}
    {request : FormulaComparisonRequest} (hi : index < (formulaWordTokens word).length)
    (h : formulaWordComparisonRequest word index = some request) :
    ∃ t : Term word.length, request.termWord = encTerm word.length t := by
  have hmem := formulaWordTokenAt_mem hi
  rw [formulaWordTokens_eq] at hmem
  obtain ⟨token, _, htoken⟩ := List.mem_map.mp hmem
  rw [formulaWordComparisonRequest, ← htoken] at h
  rcases token with _ | (term | (term | (_ | (_ | _)))) <;> cases h <;> exact ⟨term, rfl⟩

/-- A comparison request's term payload occupies strictly fewer bits than the original
formula word. A malformed word has no comparison requests. -/
theorem formulaWordComparisonRequest_termWord_length_lt {word : List Bool} {index : ℕ}
    {request : FormulaComparisonRequest} (h : formulaWordComparisonRequest word index =
      some request) : request.termWord.length < word.length := by
  have hmem := formulaWordTokenAt_mem (formulaWordComparisonRequest_index_lt h)
  have hterm : .inr (.inl request.termWord) ∈ formulaWordTokens word ∨
      .inr (.inr (.inl request.termWord)) ∈ formulaWordTokens word := by
    rw [formulaWordComparisonRequest] at h
    generalize formulaWordTokenAt word index = token at hmem h
    rcases token with _ | (_ | (_ | (_ | (_ | _)))) <;> cases h
    · exact .inl hmem
    · exact .inr hmem
  by_cases hvalid : validFormulaWord word = true
  · have hdecode := formulaTokensDecoder_decode_encFormula (Formula.ofWord word)
    rw [encFormula_ofWord, normalizeFormulaWord, ite_eq_left hvalid, ← formulaWordTokens_eq]
      at hdecode
    exact formulaTermWord_length_lt_of_decode hdecode hterm
  · rw [formulaWordTokens_eq, Formula.ofWord_of_not_valid hvalid] at hterm
    simp [encFormula_tokens, FormulaToken.encodeTerms] at hterm

private theorem comparisonRequest_polyTime :
    ComputableInPolyTime comparisonRequest encFormulaToken
      (encOption encFormulaComparisonRequest) := by
  let connectives := encSum encUnit (encSum encUnit encUnit)
  let strictTail := encSum encBits connectives
  let comparisonTail := encSum encBits strictTail
  have heq : ComputableInPolyTime (fun term => FormulaComparisonRequest.mk term false)
      encBits encFormulaComparisonRequest := by fun_prop
  have hlt : ComputableInPolyTime (fun term => FormulaComparisonRequest.mk term true)
      encBits encFormulaComparisonRequest := by fun_prop
  let readStrict (token : List Bool ⊕ Unit ⊕ Unit ⊕ Unit) : Option FormulaComparisonRequest :=
    token.getLeft?.map fun term => ⟨term, true⟩
  have hstrict : ComputableInPolyTime readStrict strictTail
      (encOption encFormulaComparisonRequest) :=
    (ComputableInO.getLeft?_deg encBits connectives).computableInPolyTime
      |>.optionMapWithInput (f := fun _ term => FormulaComparisonRequest.mk term true)
        (hlt.comp (snd strictTail encBits))
  have hright := (ComputableInO.getRight?_deg encBits strictTail).computableInPolyTime
    |>.optionElimWithInput (body := fun _ payload => readStrict payload) (const none)
      (hstrict.comp (snd comparisonTail strictTail))
  let readComparison (token : List Bool ⊕ List Bool ⊕ Unit ⊕ Unit ⊕ Unit) :
      Option FormulaComparisonRequest :=
    token.getLeft?.elim (token.getRight?.elim none readStrict) (fun term => some ⟨term, false⟩)
  have hcompare : ComputableInPolyTime readComparison comparisonTail
      (encOption encFormulaComparisonRequest) :=
    (ComputableInO.getLeft?_deg encBits strictTail).computableInPolyTime
      |>.optionElimWithInput
        (body := fun _ term => some (FormulaComparisonRequest.mk term false)) hright
        ((optionSome encFormulaComparisonRequest).comp (heq.comp (snd comparisonTail encBits)))
  have h := (ComputableInO.getRight?_deg encUnit comparisonTail).computableInPolyTime
    |>.optionElimWithInput (body := fun _ payload => readComparison payload) (const none)
      (hcompare.comp (snd encFormulaToken comparisonTail))
  apply h.of_enc_eq
  rintro (_ | (_ | (_ | _))) <;> rfl

/-- Extract the optional comparison request in polynomial time on the raw word and binary
index. The term payload is copied unchanged. -/
theorem formulaWordComparisonRequest_polyTime :
    ComputableInPolyTime (fun p : List Bool × ℕ => formulaWordComparisonRequest p.1 p.2)
      (encPair encBits encNat) (encOption encFormulaComparisonRequest) :=
  comparisonRequest_polyTime.comp formulaWordTokenAt_polyTime

/-- Read an indexed gate's exact comparison term word. Unused slots return the encoding
of the constant zero term. -/
@[expose] def formulaWordGateTermWord (word : List Bool) (index : ℕ) : List Bool :=
  (formulaWordComparisonRequest word index).elim (encTerm 0 (.const 0)) (·.termWord)

/-- The arithmetic term of an indexed formula gate in the word's ambient dimension.
Non-comparisons and indices beyond the token stream have the constant zero term. -/
noncomputable def formulaWordGateTerm (word : List Bool) (index : ℕ) : Term word.length :=
  Function.extend (encTerm word.length) id (fun _ => .const 0) (formulaWordGateTermWord word index)

/-- Encoding the typed gate term recovers the executable reader's exact payload. -/
theorem encTerm_formulaWordGateTerm (word : List Bool) (index : ℕ) :
    encTerm word.length (formulaWordGateTerm word index) = formulaWordGateTermWord word index := by
  have hcanonical : ∃ t : Term word.length, encTerm word.length t =
      formulaWordGateTermWord word index := by
    cases hrequest : formulaWordComparisonRequest word index with
    | none =>
      refine ⟨.const 0, ?_⟩
      rw [formulaWordGateTermWord, hrequest, Option.elim_none]
      rfl
    | some request =>
      obtain ⟨t, ht⟩ := formulaWordComparisonRequest_termWord_exists
        (formulaWordComparisonRequest_index_lt hrequest) hrequest
      exact ⟨t, by rw [formulaWordGateTermWord, hrequest, Option.elim_some, ht]⟩
  obtain ⟨t, ht⟩ := hcanonical
  rw [formulaWordGateTerm, ← ht, (encTerm word.length).injective.extend_apply]
  rfl

/-- The typed gate terms have polynomial-time access under the raw formula word and binary
index encoding. This adapts the term access of `LeanCanny.ETR.FormulaAtomPolynomials.termSource`
to the frontier prefix token view. -/
theorem encTerm_formulaWordGateTerm_polyTime :
    ComputableInPolyTime (fun p : List Bool × ℕ => encTerm p.1.length (formulaWordGateTerm p.1 p.2))
      (encPair encBits encNat) encBits := by
  have hterm : ComputableInPolyTime FormulaComparisonRequest.termWord
      encFormulaComparisonRequest encBits := by fun_prop
  have h := formulaWordComparisonRequest_polyTime.optionElimWithInput
    (body := fun _ request => request.termWord) (const (encTerm 0 (.const 0)))
    (hterm.comp (snd (encPair encBits encNat) encFormulaComparisonRequest))
  exact h.of_enc_eq fun p => congrArg encBits (encTerm_formulaWordGateTerm p.1 p.2)

/-- The common length budget for gate terms, including the encoded constant zero in unused
slots. -/
@[expose] def formulaWordGateTermBudget (word : List Bool) : ℕ :=
  max word.length (encTerm 0 (.const 0)).length

/-- Compute the gate-term budget in binary from the raw formula word. -/
theorem formulaWordGateTermBudget_polyTime {α : Type} {input : α ↪ List Bool}
    {word : α → List Bool} (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => formulaWordGateTermBudget (word a)) input encNat :=
  binary_max' (unary_to_binary.comp (length_bits.comp hword)) (const _)

/-- The term word at every gate fits within the common length budget. -/
theorem formulaWordGateTermWord_length_le (word : List Bool) (index : ℕ) :
    (formulaWordGateTermWord word index).length ≤ formulaWordGateTermBudget word := by
  unfold formulaWordGateTermBudget
  cases h : formulaWordComparisonRequest word index with
  | none =>
    simpa only [formulaWordGateTermWord, h, Option.elim_none] using le_max_right
      word.length (encTerm 0 (.const 0)).length
  | some request =>
    rw [formulaWordGateTermWord, h, Option.elim_some]
    exact (formulaWordComparisonRequest_termWord_length_lt h).le.trans (le_max_left ..)

/-- The formula word gives a single degree and coefficient norm budget for all of its gate
polynomials, including the zero padding at unused slots. -/
theorem formulaWordGateTerm_toPolynomial_bounds (word : List Bool) (index : ℕ) :
    let budget := formulaWordGateTermBudget word
    (formulaWordGateTerm word index).toPolynomial.totalDegree ≤ budget ∧
      (formulaWordGateTerm word index).toPolynomial.coeffNorm1 ≤ 2 ^ budget := by
  have hsize := formulaWordGateTermWord_length_le word index
  obtain ⟨hdegree, hnorm⟩ := (formulaWordGateTerm word index).toPolynomial_bounds
  rw [encTerm_formulaWordGateTerm] at hdegree hnorm
  exact ⟨hdegree.trans hsize, hnorm.trans (Nat.pow_le_pow_right (by decide) hsize)⟩

/-- Evaluate the comparison term at an indexed gate, using zero for missing coordinates.
Gates without a comparison request have no residue. -/
@[expose] def formulaWordComparisonResidue (word : List Bool) (index p : ℕ)
    (point : List ℕ) : Option ℕ :=
  (formulaWordComparisonRequest word index).elim none fun request =>
    Term.evalTermWord p point request.termWord

/-- At an in-bounds gate, the residue is present exactly when a comparison term exists and
its polynomial has that residue. Coordinates missing from `point` are read as zero. -/
theorem formulaWordComparisonResidue_eq_some_iff {word : List Bool} {index p residue : ℕ}
    (hp : 0 < p) (hi : index < (formulaWordTokens word).length) (point : List ℕ) :
    formulaWordComparisonResidue word index p point = some residue ↔
      ∃ (request : FormulaComparisonRequest) (t : Term word.length),
        formulaWordComparisonRequest word index = some request ∧
        request.termWord = encTerm word.length t ∧
        (t.toPolynomial.eval₂ (Int.castRingHom (ZMod p))
          (fun i => ((point[i.val]?.getD 0 : ℕ) : ZMod p))).val = residue := by
  constructor
  · intro h
    cases hrequest : formulaWordComparisonRequest word index with
    | none => simp [formulaWordComparisonResidue, hrequest] at h
    | some request =>
      obtain ⟨t, ht⟩ := formulaWordComparisonRequest_termWord_exists hi hrequest
      rw [formulaWordComparisonResidue, hrequest, Option.elim_some, ht,
        Term.evalTermWord_encTerm, Term.evalResidue_eq hp, Option.some.injEq] at h
      exact ⟨request, t, rfl, ht, h⟩
  · rintro ⟨request, t, hrequest, ht, h⟩
    rw [formulaWordComparisonResidue, hrequest, Option.elim_some, ht,
      Term.evalTermWord_encTerm, Term.evalResidue_eq hp, h]

/-- Comparison residue queries take polynomial time in the raw formula word, binary gate
index and positive binary modulus, and framed binary coordinates. -/
theorem formulaWordComparisonResidue_polyTime {α : Type} {input : α ↪ List Bool}
    {word : α → List Bool} {index modulus : α → ℕ} {point : α → List ℕ}
    (hword : ComputableInPolyTime word input encBits)
    (hindex : ComputableInPolyTime index input encNat)
    (hp : ComputableInPolyTime modulus input encNat) (hpos : ∀ a, 0 < modulus a)
    (hpoint : ComputableInPolyTime point input (encList encNat)) :
    ComputableInPolyTime (fun a => formulaWordComparisonResidue (word a) (index a)
      (modulus a) (point a)) input (encOption encNat) := by
  have hrequest := formulaWordComparisonRequest_polyTime.comp (hword.prod hindex)
  have hcontext := fst input encFormulaComparisonRequest
  have hterm : ComputableInPolyTime FormulaComparisonRequest.termWord
      encFormulaComparisonRequest encBits := by fun_prop
  exact hrequest.optionElimWithInput (const none)
    (Term.evalTermWord_polyTime (hp.comp hcontext) (fun a => hpos a.1)
      (hpoint.comp hcontext) (hterm.comp (snd input encFormulaComparisonRequest)))

/-- Evaluate the indexed gate's arithmetic term at the supplied residues. Unused slots
give zero, and missing coordinates are read as zero. -/
@[expose] def formulaWordGateResidue (word : List Bool) (index p : ℕ) (point : List ℕ) : ℕ :=
  (formulaWordComparisonResidue word index p point).getD 0

/-- For a positive modulus, the executable gate query returns the canonical residue
of the indexed term polynomial at the zero-padded coordinates. -/
theorem formulaWordGateResidue_eq (word : List Bool) (index : ℕ) {p : ℕ}
    (hp : 0 < p) (point : List ℕ) :
    formulaWordGateResidue word index p point =
      (MvPolynomial.aeval (fun k : Fin word.length =>
        ((point[k.val]?.getD 0 : ℕ) : ZMod p))
        (formulaWordGateTerm word index).toPolynomial).val := by
  rw [MvPolynomial.aeval_def, algebraMap_int_eq, ← Term.evalResidue_eq hp]
  have hterm := Term.evalTermWord_encTerm p point (formulaWordGateTerm word index)
  rw [encTerm_formulaWordGateTerm, formulaWordGateTermWord] at hterm
  rw [formulaWordGateResidue, formulaWordComparisonResidue]
  cases hrequest : formulaWordComparisonRequest word index with
  | none =>
    rw [hrequest, Option.elim_none, Term.evalTermWord_encTerm, Option.some.injEq] at hterm
    simpa only [Option.elim_none, Option.getD_none, Term.evalResidue,
      Int.zero_emod, Int.toNat_zero] using hterm
  | some request =>
    rw [hrequest, Option.elim_some] at hterm
    rw [Option.elim_some, hterm, Option.getD_some]

/-- The total residue query is polynomial time in the raw formula word, binary gate index
and positive binary modulus, and framed list of binary coordinate values. -/
theorem formulaWordGateResidue_polyTime {α : Type} {input : α ↪ List Bool}
    {word : α → List Bool} {index modulus : α → ℕ} {point : α → List ℕ}
    (hword : ComputableInPolyTime word input encBits)
    (hindex : ComputableInPolyTime index input encNat)
    (hp : ComputableInPolyTime modulus input encNat) (hpos : ∀ a, 0 < modulus a)
    (hpoint : ComputableInPolyTime point input (encList encNat)) :
    ComputableInPolyTime (fun a => formulaWordGateResidue (word a) (index a)
      (modulus a) (point a)) input encNat :=
  optionGetDWithInput (formulaWordComparisonResidue_polyTime hword hindex hp hpos hpoint) (const 0)

/-- Test a supplied sign against the comparison requested at a gate. Gates without a
comparison request return `false`. -/
@[expose] def formulaWordComparisonAnswer (word : List Bool) (index : ℕ) (sign : SignType) : Bool :=
  (formulaWordComparisonRequest word index).elim false fun request =>
    decide (sign = request.requestedSign)

/-- Testing an indexed comparison is polynomial time in the formula word, binary gate index,
and supplied sign using `encSign`. -/
theorem formulaWordComparisonAnswer_polyTime {α : Type} {input : α ↪ List Bool}
    {word : α → List Bool} {index : α → ℕ} {sign : α → SignType}
    (hword : ComputableInPolyTime word input encBits)
    (hindex : ComputableInPolyTime index input encNat)
    (hsign : ComputableInPolyTime sign input encSign) :
    ComputableInPolyTime (fun a => formulaWordComparisonAnswer (word a) (index a) (sign a))
      input encBool := by
  have hrequest := formulaWordComparisonRequest_polyTime.comp (hword.prod hindex)
  have hstrict : ComputableInPolyTime FormulaComparisonRequest.isStrict
      encFormulaComparisonRequest encBool := by fun_prop
  have htest := of_finite (encIn := encPair encSign encBool) (encOut := encBool)
    (fun p : SignType × Bool => decide (p.1 = if p.2 then -1 else 0))
  exact hrequest.optionElimWithInput (const false)
    (htest.comp ((hsign.comp (fst input encFormulaComparisonRequest)).prod
      (hstrict.comp (snd input encFormulaComparisonRequest))))

/-- Read the comparison request of a serialized subformula, retaining its exact term word. -/
theorem formulaWordComparisonRequest_of_prefix {n : ℕ} {word : List Bool} (p : Formula n)
    (before after : List FormulaToken)
    (h : formulaWordTokens word =
      before ++ ((encFormula_tokens n p).map FormulaToken.encodeTerms ++ after)) :
    formulaWordComparisonRequest word before.length =
      match p with
      | .eqZero t => some ⟨encTerm n t, false⟩
      | .ltZero t => some ⟨encTerm n t, true⟩
      | _ => none := by
  unfold formulaWordComparisonRequest
  cases p <;> rw [formulaWordTokenAt_append h] <;> rfl

private abbrev notToken : FormulaToken := .inr (.inr (.inr (.inl ())))
private abbrev andToken : FormulaToken := .inr (.inr (.inr (.inr (.inl ()))))
private abbrev orToken : FormulaToken := .inr (.inr (.inr (.inr (.inr ()))))

private def gateValueWithAnswer (token : FormulaToken) (children : List ℕ)
    (answer : Bool) (value : ℕ → Bool) : Bool :=
  let left := value (children.getD 0 0)
  let right := value (children.getD 1 0)
  if (comparisonRequest token).isSome then answer
  else if token = notToken then children.length == 1 && !left
  else if token = andToken then children.length == 2 && (left && right)
  else if token = orToken then children.length == 2 && (left || right)
  else false

/-- Evaluate an indexed gate with a supplied comparison answer. Connectives read the
supplied child values, and falsity and positions outside the token stream give `false`. -/
def formulaWordGateValueWithAnswer (word : List Bool) (index : ℕ)
    (answer : Bool) (value : ℕ → Bool) : Bool :=
  gateValueWithAnswer (formulaWordTokenAt word index) (formulaWordChildIndices word index)
    answer value

/-- The Boolean gate reads its value function only at the two child lookup positions. -/
theorem formulaWordGateValueWithAnswer_congr_children (word : List Bool) (index : ℕ)
    (answer : Bool) {v w : ℕ → Bool}
    (hl : v ((formulaWordChildIndices word index).getD 0 0) =
      w ((formulaWordChildIndices word index).getD 0 0))
    (hr : v ((formulaWordChildIndices word index).getD 1 0) =
      w ((formulaWordChildIndices word index).getD 1 0)) :
    formulaWordGateValueWithAnswer word index answer v =
      formulaWordGateValueWithAnswer word index answer w := by
  simp only [formulaWordGateValueWithAnswer, gateValueWithAnswer, hl, hr]

/-- Comparison gates use the supplied answer. -/
theorem formulaWordGateValueWithAnswer_of_request {word : List Bool} {index : ℕ}
    {request : FormulaComparisonRequest} (h : formulaWordComparisonRequest word index =
      some request) (answer : Bool) (value : ℕ → Bool) :
    formulaWordGateValueWithAnswer word index answer value = answer := by
  change comparisonRequest (formulaWordTokenAt word index) = some request at h
  simp [formulaWordGateValueWithAnswer, gateValueWithAnswer, h]

/-- Two supplied answers give the same gate value if they agree whenever the gate requests
a comparison. -/
theorem formulaWordGateValueWithAnswer_congr (word : List Bool) (index : ℕ)
    (value : ℕ → Bool) {a b : Bool}
    (h : (formulaWordComparisonRequest word index).isSome = true → a = b) :
    formulaWordGateValueWithAnswer word index a value =
      formulaWordGateValueWithAnswer word index b value := by
  by_cases hc : (formulaWordComparisonRequest word index).isSome = true
  · rw [h hc]
  · have hn : (comparisonRequest (formulaWordTokenAt word index)).isSome ≠ true := hc
    simp only [formulaWordGateValueWithAnswer, gateValueWithAnswer, ite_eq_right hn]

/-- Evaluate the Boolean part of a gate in polynomial time from a raw word, binary position,
comparison answer, and a certified reader of values at binary positions. -/
theorem formulaWordGateValueWithAnswer_polyTime {α : Type} {input : α ↪ List Bool}
    {word : α → List Bool} {index : α → ℕ} {answer : α → Bool} {value : α → ℕ → Bool}
    (hword : ComputableInPolyTime word input encBits)
    (hindex : ComputableInPolyTime index input encNat)
    (hanswer : ComputableInPolyTime answer input encBool)
    (hvalue : ComputableInPolyTime (fun p : α × ℕ => value p.1 p.2)
      (encPair input encNat) encBool) :
    ComputableInPolyTime (fun a => formulaWordGateValueWithAnswer (word a) (index a)
      (answer a) (value a)) input encBool := by
  have ht := formulaWordTokenAt_polyTime.comp (hword.prod hindex)
  have hc := formulaWordChildIndices_polyTime.comp (hword.prod hindex)
  have hl := hvalue.comp (id'.prod (listGetD_binary 0 hc (const 0)))
  have hr := hvalue.comp (id'.prod (listGetD_binary 0 hc (const 1)))
  have hlen := (length_list encNat).comp hc
  have hone := unary_beq' hlen (const 1)
  have htwo := unary_beq' hlen (const 2)
  have hnot := bool_and' hone (bool_not.comp hl)
  have hand := bool_and' htwo (bool_and' hl hr)
  have hor := bool_and' htwo (bool_or' hl hr)
  have hcomparison := optionIsSome (comparisonRequest_polyTime.comp ht)
  have hnotTag := ht.decide_eq' (const notToken)
  have handTag := ht.decide_eq' (const andToken)
  have horTag := ht.decide_eq' (const orToken)
  exact hcomparison.ite' hanswer
    (ite_decide hnotTag hnot (ite_decide handTag hand (ite_decide horTag hor (const false))))

/-- Evaluate one Boolean gate of the total formula view. Comparison gates ask for the sign
of their encoded term. Connectives read the supplied values at their child indices.
Falsity and positions outside the token stream return `false`. -/
def formulaWordGateValue (word : List Bool) (index : ℕ)
    (termSign : List Bool → SignType) (value : ℕ → Bool) : Bool :=
  let token := formulaWordTokenAt word index
  let answer := (comparisonRequest token).any fun request =>
    decide (termSign request.termWord = request.requestedSign)
  gateValueWithAnswer token (formulaWordChildIndices word index) answer value

/-- Computing the comparison answer from the indexed request recovers the gate's value
under the supplied term signs. -/
theorem formulaWordGateValueWithAnswer_eq (word : List Bool) (index : ℕ)
    (termSign : List Bool → SignType) (value : ℕ → Bool) :
    formulaWordGateValueWithAnswer word index
      ((formulaWordComparisonRequest word index).any fun request =>
        decide (termSign request.termWord = request.requestedSign)) value =
      formulaWordGateValue word index termSign value := by
  rw [formulaWordGateValueWithAnswer, formulaWordGateValue, formulaWordComparisonRequest]

/-- A gate at the start of an encoded subformula reads the exact term payload for a
comparison, or combines the values at the starts of its immediate operands. -/
theorem formulaWordGateValue_of_prefix {n : ℕ} {word : List Bool} (p : Formula n)
    (before after : List FormulaToken)
    (h : formulaWordTokens word =
      before ++ ((encFormula_tokens n p).map FormulaToken.encodeTerms ++ after))
    (termSign : List Bool → SignType) (value : ℕ → Bool) :
    formulaWordGateValue word before.length termSign value =
      match p with
      | .false => false
      | .eqZero t => decide (termSign (encTerm n t) = 0)
      | .ltZero t => decide (termSign (encTerm n t) = -1)
      | .not _ => !(value (before.length + 1))
      | .and left _ => value (before.length + 1) &&
          value (before.length + 1 + (encFormula_tokens n left).length)
      | .or left _ => value (before.length + 1) ||
          value (before.length + 1 + (encFormula_tokens n left).length) := by
  rw [formulaWordGateValue, formulaWordChildIndices_of_prefix p before after h]
  cases p <;> rw [formulaWordTokenAt_append h] <;> rfl

end Cslib.Logic.RealArithmetic
