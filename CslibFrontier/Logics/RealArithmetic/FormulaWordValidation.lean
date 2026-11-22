/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.RealArithmetic.FormulaTokenDecoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Mathlib.Basic.Sign.Defs
import CslibFrontier.Logics.RealArithmetic.TokenEvaluationPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
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

/-- Evaluate one Boolean gate of the total formula view. Comparison gates ask for the sign
of their encoded term. Connectives read the supplied values at their child indices.
Falsity and positions outside the token stream return `false`. -/
def formulaWordGateValue (word : List Bool) (index : ℕ)
    (termSign : List Bool → SignType) (value : ℕ → Bool) : Bool :=
  match formulaWordTokenAt word index, formulaWordChildIndices word index with
  | .inr (.inl term), _ => decide (termSign term = 0)
  | .inr (.inr (.inl term)), _ => decide (termSign term = -1)
  | .inr (.inr (.inr (.inl _))), [child] => !(value child)
  | .inr (.inr (.inr (.inr (.inl _)))), [left, right] => value left && value right
  | .inr (.inr (.inr (.inr (.inr _)))), [left, right] => value left || value right
  | _, _ => false

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
