/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Backward Boolean evaluation of formula words

This adapts the wire scan and its correctness proof from
`LeanCanny.Computation.BooleanCircuitSpace` and `LeanCanny.ETR.FormulaBooleanCircuitCorrect`
at lean-canny revision `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
Every operand follows its parent in the prefix token stream, so visiting tokens from right to
left gives each gate access to its previously computed operands. The scan accepts answers
indexed by gate, as in `LeanCanny.ETR.FormulaBooleanCircuitSource.value_signature` at that same
revision. Supplying the comparisons of term-word signs recovers the term-sign evaluator.
Correct signs for the comparison terms in the word suffice for the root value to characterize
membership in the real solution set.
The backward scan stays in polynomial space when comparison answers are computed in polynomial
space, keeping just one bit per processed gate.
-/

public section

namespace Cslib.Logic.RealArithmetic

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Evaluate a formula with each comparison interpreted by its term's supplied sign. -/
@[expose] def Formula.evalTermSigns {n : ℕ} (termSign : Term n → SignType) : Formula n → Bool
  | .false => Bool.false
  | .eqZero t => decide (termSign t = 0)
  | .ltZero t => decide (termSign t = -1)
  | .not p => !(p.evalTermSigns termSign)
  | .and p q => p.evalTermSigns termSign && q.evalTermSigns termSign
  | .or p q => p.evalTermSigns termSign || q.evalTermSigns termSign

/-- Read an absolute child index from the computed suffix, whose first bit is at
`gateIndex + 1`. Indices at or before the gate or past the suffix read `false`. -/
def formulaGateSuffixValue (suffix : List Bool) (gateIndex childIndex : ℕ) : Bool :=
  if gateIndex < childIndex then suffix.getD (childIndex - (gateIndex + 1)) false else false

/-- Reading a child from the raw suffix bits is polynomial time in the input, with both
positions in binary. The underlying lookup caps the offset at the suffix length. -/
@[fun_prop]
theorem formulaGateSuffixValue_polyTime {α : Type} {input : α ↪ List Bool}
    {suffix : α → List Bool} {gateIndex childIndex : α → ℕ}
    (hsuffix : ComputableInPolyTime suffix input encBits)
    (hgate : ComputableInPolyTime gateIndex input encNat)
    (hchild : ComputableInPolyTime childIndex input encNat) :
    ComputableInPolyTime (fun a => formulaGateSuffixValue (suffix a) (gateIndex a) (childIndex a))
      input encBool :=
  ite_decide (binary_lt' hgate hchild)
    (listGetD_binary false hsuffix (binary_sub' hchild (binary_add' hgate (const 1))))
    (const false)

/-- Prepend the value of an indexed gate to its computed suffix, given the answer to its
comparison request. The answer is ignored at gates without a comparison request. -/
def formulaWordGateUpdate (word : List Bool) (index : ℕ) (answer : Bool)
    (suffix : List Bool) : List Bool :=
  formulaWordGateValueWithAnswer word index answer (formulaGateSuffixValue suffix index) :: suffix

/-- The Boolean gate update is polynomial time in the raw word, binary position,
comparison-answer bit, and raw suffix. -/
theorem formulaWordGateUpdate_polyTime {α : Type} {input : α ↪ List Bool}
    {word : α → List Bool} {index : α → ℕ} {answer : α → Bool} {suffix : α → List Bool}
    (hword : ComputableInPolyTime word input encBits)
    (hindex : ComputableInPolyTime index input encNat)
    (hanswer : ComputableInPolyTime answer input encBool)
    (hsuffix : ComputableInPolyTime suffix input encBits) :
    ComputableInPolyTime (fun a => formulaWordGateUpdate (word a) (index a) (answer a) (suffix a))
      input encBits := by
  have hread := formulaGateSuffixValue_polyTime (hsuffix.comp (fst input encNat))
    (hindex.comp (fst input encNat)) (snd input encNat)
  exact bitsCons (formulaWordGateValueWithAnswer_polyTime hword hindex hanswer hread) hsuffix

/-- Supplying the comparison answer from the term signs gives the scan's next suffix. -/
theorem formulaWordGateUpdate_eq_cons (word : List Bool) (index : ℕ)
    (termSign : List Bool → SignType) (suffix : List Bool) :
    formulaWordGateUpdate word index
      ((formulaWordComparisonRequest word index).any fun request =>
        decide (termSign request.termWord = request.requestedSign)) suffix =
      formulaWordGateValue word index termSign (formulaGateSuffixValue suffix index) :: suffix := by
  rw [formulaWordGateUpdate, formulaWordGateValueWithAnswer_eq]

private def gateValuesAux (word : List Bool) (answer : ℕ → Bool)
    (size : ℕ) : ℕ → List Bool
  | 0 => []
  | k + 1 =>
    let index := size - (k + 1)
    formulaWordGateUpdate word index (answer index) (gateValuesAux word answer size k)

/-- Evaluate the total formula view from right to left, using the supplied answer at each
comparison gate's index. The result lists gate values in prefix order. -/
def formulaWordGateValuesWithAnswers (word : List Bool) (answer : ℕ → Bool) : List Bool :=
  let size := (formulaWordTokens word).length
  gateValuesAux word answer size size

/-- Evaluate all gates of the total formula view from right to left, returning their Boolean
values in prefix order. A child is read from the already evaluated suffix. -/
def formulaWordGateValues (word : List Bool) (termSign : List Bool → SignType) : List Bool :=
  formulaWordGateValuesWithAnswers word fun index =>
    (formulaWordComparisonRequest word index).any fun request =>
      decide (termSign request.termWord = request.requestedSign)

private theorem gateValuesAux_length (word : List Bool) (answer : ℕ → Bool)
    (size count : ℕ) : (gateValuesAux word answer size count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [gateValuesAux, formulaWordGateUpdate, List.length_cons, ih]

/-- The scan stores one Boolean value per token. -/
theorem formulaWordGateValues_length (word : List Bool) (termSign : List Bool → SignType) :
    (formulaWordGateValues word termSign).length = (formulaWordTokens word).length :=
  gateValuesAux_length word _ _ _

/-- Gate-indexed answers recover the term-sign scan when they give the requested comparison
at each comparison gate. -/
theorem formulaWordGateValuesWithAnswers_eq_of_comparisonAnswers (word : List Bool)
    (answer : ℕ → Bool) (termSign : List Bool → SignType)
    (h : ∀ index < (formulaWordTokens word).length, ∀ request,
      formulaWordComparisonRequest word index = some request →
      answer index = decide (termSign request.termWord = request.requestedSign)) :
    formulaWordGateValuesWithAnswers word answer = formulaWordGateValues word termSign := by
  let size := (formulaWordTokens word).length
  let signAnswer (index : ℕ) := (formulaWordComparisonRequest word index).any fun request =>
    decide (termSign request.termWord = request.requestedSign)
  have agree (k : ℕ) (hk : k ≤ size) :
      gateValuesAux word answer size k = gateValuesAux word signAnswer size k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      let index := size - (k + 1)
      have hi : index < size := Nat.sub_lt (Nat.zero_lt_of_lt hk) (Nat.succ_pos k)
      simp only [gateValuesAux, formulaWordGateUpdate, ih (Nat.le_of_succ_le hk)]
      congr 1
      apply formulaWordGateValueWithAnswer_congr
      intro hc
      obtain ⟨request, hreq⟩ := Option.isSome_iff_exists.mp hc
      simpa only [signAnswer, hreq, Option.any_some] using h index hi request hreq
  exact agree size le_rfl

/-- A polynomial-space comparison-answer computation suffices for the whole backward
gate scan. Each query receives the original encoded input and a binary gate index, and the
scan stores a raw suffix bit for each gate it has processed. -/
theorem formulaWordGateValuesWithAnswers_polySpace {α : Type} [Inhabited α]
    {input : α ↪ List Bool} {word : α → List Bool} {answer : α → ℕ → Bool}
    (hword : ComputableInPolyTime word input encBits)
    (hanswer : ComputableInPolySpace (fun p : α × ℕ => answer p.1 p.2)
      (encPair input encNat) encBool) :
    ComputableInPolySpace (fun a => formulaWordGateValuesWithAnswers (word a) (answer a))
      input encBits := by
  let count (a : α) := (formulaWordTokens (word a)).length
  let step (a : α) (k : ℕ) (suffix : List Bool) :=
    let index := count a - (k + 1)
    formulaWordGateUpdate (word a) index (answer a index) suffix
  have htokens := formulaWordTokens_polyTime.comp hword
  have hcount : ComputableInPolyTime count input encNat := length_list_binary' htokens
  let tail := encPair encNat encBits
  let args := encPair input tail
  have hcontext := fst input tail
  have hrest := snd input tail
  have hround := (fst encNat encBits).comp hrest
  have hsuffix := (snd encNat encBits).comp hrest
  have hindex := binary_sub' (hcount.comp hcontext) (binary_add' hround (const 1))
  have hbit := hanswer.comp (ComputableInPolySpace.of_polyTime (hcontext.prod hindex))
  have hkeep := fst args encBool
  have hfinish := formulaWordGateUpdate_polyTime ((hword.comp hcontext).comp hkeep)
    (hindex.comp hkeep) (snd args encBool) (hsuffix.comp hkeep)
  have hstep : ComputableInPolySpace (fun p : α × ℕ × List Bool => step p.1 p.2.1 p.2.2)
      args encBits :=
    (ComputableInPolySpace.of_polyTime hfinish).comp (ComputableInPolySpace.id'.prod hbit)
  have hbound : PolyBounded (fun a => (input a).length) count :=
    htokens.polyBounded_length.mono fun a =>
      SizedListEncoding.length_le (encA := encFormulaToken) (encL := encList encFormulaToken) _
  let invariant (a : α) (k : ℕ) (suffix : List Bool) :=
    suffix = gateValuesAux (word a) (answer a) (count a) k
  obtain ⟨hfold, hcorrect⟩ := ComputableInPolySpace.natFold_spec hcount
    (ComputableInPolySpace.of_polyTime (const [])) hstep invariant
    (fun _ => rfl) (fun _ _ _ _ hs => hs ▸ rfl)
    hbound (fun a k suffix hk hs => by
      change suffix = _ at hs
      simpa only [encBits_apply, hs, gateValuesAux_length] using hk)
  exact hfold.congr hcorrect

/-- The term-sign scan uses polynomial space if each indexed comparison with the supplied
term signs is computable in polynomial space. -/
theorem formulaWordGateValues_polySpace_of_comparisonAnswers {α : Type} [Inhabited α]
    {input : α ↪ List Bool} {word : α → List Bool} {termSign : α → List Bool → SignType}
    (hword : ComputableInPolyTime word input encBits)
    (hanswer : ComputableInPolySpace (fun p : α × ℕ =>
      (formulaWordComparisonRequest (word p.1) p.2).any fun request =>
        decide (termSign p.1 request.termWord = request.requestedSign))
      (encPair input encNat) encBool) :
    ComputableInPolySpace (fun a => formulaWordGateValues (word a) (termSign a)) input encBits :=
  formulaWordGateValuesWithAnswers_polySpace hword hanswer

private theorem gateValuesAux_getD (word : List Bool) (answer : ℕ → Bool)
    (size count offset : ℕ) :
    (gateValuesAux word answer size count).getD offset false =
      (gateValuesAux word answer size (count - offset)).getD 0 false := by
  induction offset generalizing count with
  | zero => rw [Nat.sub_zero]
  | succ offset ih =>
    cases count with
    | zero => simp only [Nat.zero_sub, gateValuesAux, List.getD_nil]
    | succ count =>
      rw [Nat.succ_sub_succ]
      exact ih count

private theorem formulaWordGateValues_getD_step (word : List Bool)
    (termSign : List Bool → SignType) (index : ℕ) (hi : index < (formulaWordTokens word).length) :
    (formulaWordGateValues word termSign).getD index false = formulaWordGateValue word index
      termSign (fun child => if index < child then
        (formulaWordGateValues word termSign).getD child false else false) := by
  obtain ⟨k, hk⟩ : ∃ k, (formulaWordTokens word).length - index = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.sub_pos_of_lt hi).ne'
  have hindex : (formulaWordTokens word).length - (k + 1) = index := by
    rw [← hk, Nat.sub_sub_self hi.le]
  rw [formulaWordGateValues, formulaWordGateValuesWithAnswers, gateValuesAux_getD, hk,
    gateValuesAux, formulaWordGateUpdate_eq_cons, List.getD_cons_zero, hindex]
  congr 1
  funext child
  unfold formulaGateSuffixValue
  split
  · rw [gateValuesAux_getD, gateValuesAux_getD word _ _ (formulaWordTokens word).length child]
    congr 2
    lia
  · rfl

/-- Reading the value of an encoded subformula from the gate scan agrees with interpreting
its comparisons using the signs of their encoded terms. -/
theorem formulaWordGateValues_getD_of_prefix {n : ℕ} {word : List Bool} (p : Formula n)
    (before after : List FormulaToken)
    (h : formulaWordTokens word =
      before ++ ((encFormula_tokens n p).map FormulaToken.encodeTerms ++ after))
    (termSign : List Bool → SignType) :
    (formulaWordGateValues word termSign).getD before.length false =
      p.evalTermSigns (termSign ∘ encTerm n) := by
  induction p generalizing before after
  all_goals
    have hi : before.length < (formulaWordTokens word).length := by
      rw [h, List.length_append, List.length_append, List.length_map]
      simp [encFormula_tokens]
    rw [formulaWordGateValues_getD_step word termSign _ hi,
      formulaWordGateValue_of_prefix _ _ _ h]
  case false | eqZero | ltZero => rfl
  case not p ih =>
    have hp := ih (before ++ [_]) after
      (by simpa only [encFormula_tokens, List.map_cons, List.map_append, List.append_nil,
        List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using h)
    simp only [List.length_append, List.length_singleton] at hp
    simp only [Formula.evalTermSigns, ite_eq_left (Nat.lt_succ_self _), hp]
  case and p q ihp ihq | or p q ihp ihq =>
    simp only [encFormula_tokens, List.map_cons, List.map_append, List.append_nil,
      List.cons_append, List.append_assoc] at h
    have hp := ihp (before ++ [_]) ((encFormula_tokens n q).map FormulaToken.encodeTerms ++ after)
      (by simpa only [List.append_assoc, List.singleton_append] using h)
    have hq := ihq ((before ++ [_]) ++ (encFormula_tokens n p).map FormulaToken.encodeTerms) after
      (by simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
        using h)
    simp only [List.length_append, List.length_singleton, List.length_map] at hp hq
    have hright : before.length < before.length + 1 + (encFormula_tokens n p).length := by omega
    simp only [Formula.evalTermSigns, ite_eq_left (Nat.lt_succ_self _), ite_eq_left hright, hp, hq]

/-- The first gate is the value of the total formula view, under signs assigned to term words. -/
theorem formulaWordGateValues_getD_zero (word : List Bool) (termSign : List Bool → SignType) :
    (formulaWordGateValues word termSign).getD 0 false =
      (Formula.ofWord word).evalTermSigns (termSign ∘ encTerm word.length) :=
  formulaWordGateValues_getD_of_prefix (Formula.ofWord word) [] []
    (by simpa only [List.nil_append, List.append_nil] using formulaWordTokens_eq word) termSign

/-- Evaluate the total formula view using a finite sign signature indexed by gate. A
comparison beyond the signature receives `false`. -/
def formulaWordGateValuesWithSignature {n : ℕ} (word : List Bool)
    (signature : Fin n → SignType) : List Bool :=
  formulaWordGateValuesWithAnswers word fun index =>
    if hi : index < n then formulaWordComparisonAnswer word index (signature ⟨index, hi⟩)
    else false

/-- The finite-signature scan uses polynomial space when the word and the list of signs in
gate order are available in polynomial time. The signs use the framed `encList encSign`
encoding, and each comparison looks up its sign at a binary gate index. -/
theorem formulaWordGateValuesWithSignature_polySpace {α : Type} [Inhabited α]
    {input : α ↪ List Bool} {word : α → List Bool} {signs : α → List SignType}
    (hword : ComputableInPolyTime word input encBits)
    (hsigns : ComputableInPolyTime signs input (encList encSign)) :
    ComputableInPolySpace (fun a => formulaWordGateValuesWithSignature (word a)
      (fun index : Fin (signs a).length => (signs a)[index.val])) input encBits := by
  have hcontext := fst input encNat
  have hindex := snd input encNat
  have hlist := hsigns.comp hcontext
  have hinBounds := binary_lt' hindex (length_list_binary' hlist)
  have hsign := listGetD_binary (encA := encSign) 0 hlist hindex
  have htest := formulaWordComparisonAnswer_polyTime (hword.comp hcontext) hindex hsign
  have hanswer := ite_decide hinBounds htest (const false)
  unfold formulaWordGateValuesWithSignature
  refine formulaWordGateValuesWithAnswers_polySpace hword
    ((ComputableInPolySpace.of_polyTime hanswer).congr ?_)
  rintro ⟨a, index⟩
  by_cases hi : index < (signs a).length
  · simp only [Function.comp_apply, ite_eq_left hi, dite_eq_left hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some]
  · simp only [Function.comp_apply, ite_eq_right hi, dite_eq_right hi]

/-- A finite gate signature covering the formula word's tokens gives the term-sign value
of the total formula view if its sign at every comparison agrees with the requested term's
sign. This adapts `LeanCanny.ETR.FormulaBooleanCircuitSource.value_signature` to the
frontier token view, which only requests signs at comparison gates. -/
theorem formulaWordGateValuesWithSignature_getD_zero {n : ℕ} (word : List Bool)
    (signature : Fin n → SignType) (termSign : List Bool → SignType)
    (hn : (formulaWordTokens word).length ≤ n)
    (hsign : ∀ index (hi : index < (formulaWordTokens word).length) request,
      formulaWordComparisonRequest word index = some request →
      signature ⟨index, hi.trans_le hn⟩ = termSign request.termWord) :
    (formulaWordGateValuesWithSignature word signature).getD 0 false =
      (Formula.ofWord word).evalTermSigns (termSign ∘ encTerm word.length) := by
  rw [formulaWordGateValuesWithSignature,
    formulaWordGateValuesWithAnswers_eq_of_comparisonAnswers word _ termSign ?_,
    formulaWordGateValues_getD_zero]
  intro index hi request hrequest
  rw [dite_eq_left (hi.trans_le hn), formulaWordComparisonAnswer, hrequest]
  change decide (signature ⟨index, hi.trans_le hn⟩ = request.requestedSign) = _
  rw [hsign index hi request hrequest]

private theorem evalTermSigns_eq_true_iff_of_token_signs {n : ℕ} (p : Formula n)
    (termSign : Term n → SignType) (x : Fin n → ℝ)
    (hsign : ∀ t, .inr (.inl t) ∈ encFormula_tokens n p ∨
        .inr (.inr (.inl t)) ∈ encFormula_tokens n p → termSign t = SignType.sign (t.eval x)) :
    p.evalTermSigns termSign = true ↔ x ∈ p.solutionSet := by
  induction p with
  | false => simp [Formula.evalTermSigns, Formula.solutionSet]
  | eqZero t =>
    have ht := hsign t (.inl (by simp [encFormula_tokens]))
    simp [Formula.evalTermSigns, Formula.solutionSet, ht]
  | ltZero t =>
    have ht := hsign t (.inr (by simp [encFormula_tokens]))
    simp [Formula.evalTermSigns, Formula.solutionSet, ht, sign_eq_neg_one_iff]
  | not p ih =>
    simp only [encFormula_tokens, List.append_nil, List.mem_cons] at hsign
    have hp := ih fun t ht => hsign t (ht.imp Or.inr Or.inr)
    simp [Formula.evalTermSigns, Formula.solutionSet, Bool.eq_false_iff, hp]
  | and p q ihp ihq | or p q ihp ihq =>
    simp only [encFormula_tokens, List.append_nil, List.mem_cons, List.mem_append] at hsign
    have hp := ihp fun t ht =>
      hsign t (ht.imp (fun hm => .inr (.inl hm)) (fun hm => .inr (.inl hm)))
    have hq := ihq fun t ht =>
      hsign t (ht.imp (fun hm => .inr (.inr hm)) (fun hm => .inr (.inr hm)))
    simp [Formula.evalTermSigns, Formula.solutionSet, hp, hq]

/-- The root gate holds at a real point if and only if the total formula view holds there,
provided the sign reader gives the true sign for each comparison term in the word. -/
theorem formulaWordGateValues_getD_zero_eq_true_iff (word : List Bool)
    (termSign : List Bool → SignType) (x : Fin word.length → ℝ)
    (hsign : ∀ t : Term word.length, .inr (.inl (encTerm word.length t)) ∈ formulaWordTokens word ∨
        .inr (.inr (.inl (encTerm word.length t))) ∈ formulaWordTokens word →
        termSign (encTerm word.length t) = SignType.sign (t.eval x)) :
    (formulaWordGateValues word termSign).getD 0 false = true ↔
      x ∈ (Formula.ofWord word).solutionSet := by
  rw [formulaWordGateValues_getD_zero]
  apply evalTermSigns_eq_true_iff_of_token_signs
  intro t ht
  apply hsign t
  rw [formulaWordTokens_eq]
  rcases ht with ht | ht
  · exact .inl (List.mem_map_of_mem ht)
  · exact .inr (List.mem_map_of_mem ht)

/-- A gate signature matching the real sign of every requested term gives the truth of the
total formula view at that point. This is the token-view version of
`LeanCanny.ETR.FormulaBooleanCircuitSource.signature_holds` at the revision cited above. -/
theorem formulaWordGateValuesWithSignature_getD_zero_eq_true_iff {n : ℕ} (word : List Bool)
    (signature : Fin n → SignType) (x : Fin word.length → ℝ)
    (hn : (formulaWordTokens word).length ≤ n)
    (hsign : ∀ index (hi : index < (formulaWordTokens word).length) request (t : Term word.length),
      formulaWordComparisonRequest word index = some request →
      request.termWord = encTerm word.length t →
      signature ⟨index, hi.trans_le hn⟩ = SignType.sign (t.eval x)) :
    (formulaWordGateValuesWithSignature word signature).getD 0 false = true ↔
      x ∈ (Formula.ofWord word).solutionSet := by
  let termSign := Function.extend (encTerm word.length) (fun t => SignType.sign (t.eval x))
    (fun _ => 0)
  have hterm (t : Term word.length) :
      termSign (encTerm word.length t) = SignType.sign (t.eval x) :=
    (encTerm word.length).injective.extend_apply _ _ t
  have hagrees (index : ℕ) (hi : index < (formulaWordTokens word).length)
      (request : FormulaComparisonRequest) (hrequest : formulaWordComparisonRequest word index =
        some request) : signature ⟨index, hi.trans_le hn⟩ = termSign request.termWord := by
    obtain ⟨t, hword⟩ := formulaWordComparisonRequest_termWord_exists hi hrequest
    rw [hword, hterm]
    exact hsign index hi request t hrequest hword
  rw [formulaWordGateValuesWithSignature_getD_zero word signature termSign hn hagrees,
    ← formulaWordGateValues_getD_zero]
  exact formulaWordGateValues_getD_zero_eq_true_iff word termSign x fun t _ => hterm t

end Cslib.Logic.RealArithmetic
