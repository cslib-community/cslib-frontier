/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.RealArithmetic.ModularEvaluation
public import CslibFrontier.Logics.RealArithmetic.TermTokenDecoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Tactic.OptionMatch

/-!
# Polynomial-time modular evaluation of term words

Each transition charges the encoded token, binary modulus, coordinate list, and residue stack.
It retains the unary variable ranks of the term encoding and charges the binary modular
arithmetic. This certifies one transition of the constructor-stream evaluator, adapting the
case dispatch of `TermModularFrames` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183` to the frontier encodings.
For a positive modulus, a framed token list can be evaluated from an empty stack in
polynomial time. The number and width of residues bound every intermediate encoding.
The strict token decoder and a singleton-stack check lift this certificate to raw term
words without fixing the ambient dimension. Every successful evaluation comes from a
complete term whose variable ranks fit within the input length.
-/

public section

namespace Cslib.Logic.RealArithmetic.Term

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

private theorem pushResidue_polyTime {γ : Type} {enc : γ ↪ List Bool}
    {value : γ → ℕ} {stack : γ → List ℕ}
    (hvalue : ComputableInPolyTime value enc encNat)
    (hstack : ComputableInPolyTime stack enc (encList encNat)) :
    ComputableInPolyTime (fun a => some (value a :: stack a)) enc
      (encOption (encList encNat)) :=
  (optionSome _).comp ((cons encNat).comp (hvalue.prod hstack))

private def combineResidues (op : ℕ × ℕ → ℕ) (p : ℕ) (stack : List ℕ) : Option (List ℕ) :=
  if stack.tail.isEmpty then none
  else some (op (stack.headD 0, stack.tail.headD 0) % p :: stack.tail.tail)

@[local fun_prop]
private theorem combineResidues_polyTime {γ : Type} {enc : γ ↪ List Bool}
    {op : ℕ × ℕ → ℕ} {modulus : γ → ℕ} {stack : γ → List ℕ}
    (hop : ComputableInPolyTime op (encPair encNat encNat) encNat)
    (hp : ComputableInPolyTime modulus enc encNat)
    (hs : ComputableInPolyTime stack enc (encList encNat)) :
    ComputableInPolyTime (fun a => combineResidues op (modulus a) (stack a)) enc
      (encOption (encList encNat)) := by
  have ht := (listTail encNat).comp hs
  have hl := (headD (encA := encNat) 0).comp hs
  have hr := (headD (encA := encNat) 0).comp ht
  have hvalue := binary_mod' (hop.comp (hl.prod hr)) hp
  exact ((listIsEmpty' encNat).comp ht).ite' (.const none)
    (pushResidue_polyTime hvalue ((listTail encNat).comp ht))

/-- Evaluate one constructor token in polynomial time. The modulus, coordinates and stack
entries use binary naturals, and the token's variable rank uses the term encoding's unary rank.
The result is an optional framed residue list. -/
theorem evalTokenStep_polyTime {γ : Type} {enc : γ ↪ List Bool}
    {modulus : γ → ℕ} {point stack : γ → List ℕ} {token : γ → TermToken}
    (hp : ComputableInPolyTime modulus enc encNat)
    (hx : ComputableInPolyTime point enc (encList encNat))
    (hs : ComputableInPolyTime stack enc (encList encNat))
    (ht : ComputableInPolyTime token enc encTermToken) :
    ComputableInPolyTime (fun a => evalTokenStep (modulus a) (point a) (token a) (stack a))
      enc (encOption (encList encNat)) := by
  have hc := pushResidue_polyTime
    (intBin_emodNat' (snd enc encIntBin) (hp.comp (fst enc encIntBin)))
    (hs.comp (fst enc encIntBin))
  let encVar := encPair (encPair enc (encSum encUnary (encSum encUnit encUnit))) encUnary
  have hp1 := (fst enc (encSum encUnary (encSum encUnit encUnit))).comp
    (fst (encPair enc (encSum encUnary (encSum encUnit encUnit))) encUnary)
  have hvar := pushResidue_polyTime (enc := encVar)
    (binary_mod' (listGetDWithInput (hx.comp hp1) (snd _ encUnary) 0) (hp.comp hp1))
    (hs.comp hp1)
  have h : ComputableInPolyTime (fun a => (token a).elim
      (fun z => some ((z % (modulus a : ℤ)).toNat :: stack a))
      (fun tag => tag.elim
        (fun i => some ((point a).getD i 0 % modulus a :: stack a))
        (fun op => op.elim
          (fun _ => combineResidues (fun p => p.1 + p.2) (modulus a) (stack a))
          (fun _ => combineResidues (fun p => p.1 * p.2) (modulus a) (stack a)))))
      enc (encOption (encList encNat)) := by fun_prop
  refine h.of_enc_eq fun a => congrArg (encOption (encList encNat)) ?_
  rcases token a with z | (i | (_ | _))
  · rfl
  · simp only [evalTokenStep, Sum.elim_inr, Sum.elim_inl, List.getD_eq_getElem?_getD]
  all_goals
    rcases stack a with _ | ⟨l, _ | ⟨r, rest⟩⟩ <;> rfl

/-- Starting with an empty stack, evaluate a framed stream of constructor tokens from right
to left in polynomial time for a positive binary modulus. The output is an optional framed
list of binary residues. The bound also applies to streams that fail with underflow. -/
theorem evalTokenStack_polyTime {γ : Type} {enc : γ ↪ List Bool}
    {modulus : γ → ℕ} {point : γ → List ℕ} {tokens : γ → List TermToken}
    (hp : ComputableInPolyTime modulus enc encNat) (hpos : ∀ a, 0 < modulus a)
    (hx : ComputableInPolyTime point enc (encList encNat))
    (ht : ComputableInPolyTime tokens enc (encList encTermToken)) :
    ComputableInPolyTime (fun a => evalTokenStack (modulus a) (point a) (tokens a) [])
      enc (encOption (encList encNat)) := by
  let stackEnc := encOption (encList encNat)
  let step (a : γ) (state : Option (List ℕ)) (token : TermToken) :=
    state.bind (evalTokenStep (modulus a) (point a) token)
  let stepEnc := encPair (encPair enc stackEnc) encTermToken
  have hstate := (snd enc stackEnc).comp (fst (encPair enc stackEnc) encTermToken)
  have hkeep := fst stepEnc (encList encNat)
  have hparam := ((fst enc stackEnc).comp (fst (encPair enc stackEnc) encTermToken)).comp hkeep
  have htoken := (snd (encPair enc stackEnc) encTermToken).comp hkeep
  have hbody : ComputableInPolyTime
      (fun a => evalTokenStep (modulus a.1.1.1) (point a.1.1.1) a.1.2 a.2)
      (encPair stepEnc (encList encNat)) stackEnc :=
    evalTokenStep_polyTime (hp.comp hparam) (hx.comp hparam) (snd stepEnc (encList encNat)) htoken
  have hstep : ComputableInPolyTime (fun a => step a.1.1 a.1.2 a.2) stepEnc stackEnc := by
    dsimp only [step]
    option_match_to_elim
    exact optionElimWithInput hstate (.const none) hbody
  have hwidth := ((PolyBounded.const 2).mul hp.polyBounded_length).add (.const 1)
  have hsize := (ht.polyBounded_length.mul hwidth).add (.const 1)
  have hfold := foldlWith (encA := encTermToken) (step := step) id'
    ((listReverse encTermToken).comp ht) (.const (some [])) hstep hsize ?_
  · apply hfold.of_enc_eq
    intro a
    change stackEnc (evalTokenStack (modulus a) (point a) (tokens a) []) =
      stackEnc ((tokens a).reverse.foldl (step a) (some []))
    rw [List.foldl_reverse]
    rfl
  intro a i hi
  let suffix := ((tokens a).reverse.take i).reverse
  rw [List.foldl_eq_foldr_reverse]
  change (stackEnc (evalTokenStack (modulus a) (point a) suffix [])).length ≤
    (encList encTermToken (tokens a)).length * (2 * (encNat (modulus a)).length + 1) + 1
  cases h : evalTokenStack (modulus a) (point a) suffix [] with
  | none => exact Nat.zero_le _
  | some residues =>
    obtain ⟨hentries, hresidues⟩ := evalTokenStack_bounds (hpos a) (point a) suffix (by simp) h
    simp only [List.length_nil, Nat.zero_add] at hentries
    have hsuffix : suffix.length ≤ (tokens a).length := by
      change (((tokens a).reverse.take i).reverse).length ≤ (tokens a).length
      rw [List.length_reverse]
      exact (List.length_take_le _ _).trans (by simpa only [Function.comp_apply,
        List.length_reverse] using hi)
    have hcount : residues.length ≤ (encList encTermToken (tokens a)).length :=
      hentries.trans (hsuffix.trans (SizedListEncoding.length_le encTermToken
        (encL := encList encTermToken) (tokens a)))
    have hbits := length_encList_le encNat residues (b := (encNat (modulus a)).length)
      fun residue hr => by
        rw [length_encNat_eq_size, length_encNat_eq_size]
        exact Nat.size_le_size (hresidues residue hr).le
    exact Nat.add_le_add_right
      (hbits.trans (Nat.mul_le_mul_right _ hcount)) 1

/-- Evaluate a raw term word using natural-number variable ranks and zero-padded coordinates.
Return a residue only if strict token decoding and stack evaluation leave a singleton stack. -/
@[expose] def evalTermWord (p : ℕ) (point : List ℕ) (word : List Bool) : Option ℕ := do
  let tokens ← termTokensDecoder.decode word
  let stack ← evalTokenStack p point tokens []
  if stack.tail.isEmpty then stack.head? else none

/-- Evaluation of a canonical term word returns its syntax-directed modular residue. -/
theorem evalTermWord_encTerm {n : ℕ} (p : ℕ) (point : List ℕ) (t : Term n) :
    evalTermWord p point (encTerm n t) = some (t.evalResidue p point) := by
  rw [evalTermWord, termTokensDecoder_decode_encTerm]
  change (evalTokenStack p point ((encTerm_tokens n t).map TermToken.ofFin) []).bind
    (fun stack => if stack.tail.isEmpty then stack.head? else none) = some (t.evalResidue p point)
  rw [evalTokenStack_tokens]
  rfl

private theorem exists_terms_of_evalTokenStack {n p : ℕ} (point : List ℕ)
    (tokens : List TermToken) {residues : List ℕ}
    (hrank : ∀ i, .inr (.inl i) ∈ tokens → i < n)
    (h : evalTokenStack p point tokens [] = some residues) :
    ∃ terms : List (Term n),
      terms.flatMap (fun t => (encTerm_tokens n t).map TermToken.ofFin) = tokens ∧
      terms.map (evalResidue p point) = residues := by
  induction tokens generalizing residues with
  | nil =>
    cases h
    exact ⟨[], rfl, rfl⟩
  | cons token tokens ih =>
    change (evalTokenStack p point tokens []).bind (evalTokenStep p point token) =
      some residues at h
    obtain ⟨intermediate, htail, hstep⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨terms, htokens, hresidues⟩ := ih
      (fun i hi => hrank i (List.mem_cons_of_mem _ hi)) htail
    rw [← hresidues] at hstep
    rcases token with z | (i | (⟨⟩ | ⟨⟩))
    · cases hstep
      refine ⟨.const z :: terms, ?_, rfl⟩
      exact congrArg (List.cons (α := TermToken) (.inl z)) htokens
    · have hi := hrank i (List.mem_cons_self ..)
      cases hstep
      refine ⟨.var ⟨i, hi⟩ :: terms, ?_, rfl⟩
      exact congrArg (List.cons (α := TermToken) (.inr (.inl i))) htokens
    · rcases terms with _ | ⟨l, _ | ⟨r, rest⟩⟩ <;> cases hstep
      refine ⟨.add l r :: rest, ?_, rfl⟩
      simpa [encTerm_tokens, TermToken.ofFin, List.append_assoc] using
        congrArg (Sum.inr (Sum.inr (.inl ())) :: ·) htokens
    · rcases terms with _ | ⟨l, _ | ⟨r, rest⟩⟩ <;> cases hstep
      refine ⟨.mul l r :: rest, ?_, rfl⟩
      simpa [encTerm_tokens, TermToken.ofFin, List.append_assoc] using
        congrArg (Sum.inr (Sum.inr (.inr ())) :: ·) htokens

/-- Raw evaluation succeeds with a residue exactly on words encoding a single term with that
residue. The input length suffices as the ambient dimension for the reconstructed term. -/
theorem evalTermWord_eq_some_iff {p value : ℕ} {point : List ℕ} {word : List Bool} :
    evalTermWord p point word = some value ↔
      ∃ t : Term word.length, encTerm word.length t = word ∧ t.evalResidue p point = value := by
  constructor
  · intro h
    simp only [evalTermWord, Option.bind_eq_bind] at h
    obtain ⟨tokens, hdecode, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨stack, hstack, hvalue⟩ := Option.bind_eq_some_iff.mp h
    rcases stack with _ | ⟨r, _ | ⟨s, rest⟩⟩
    · cases hvalue
    · cases hvalue
      obtain ⟨terms, htokens, hresidues⟩ := exists_terms_of_evalTokenStack point tokens
        (fun _ hi => termTokenRank_lt_of_decode hdecode hi) hstack
      obtain ⟨t, rfl, ht⟩ := List.map_eq_singleton_iff.mp hresidues
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htokens
      have hword := (termTokensDecoder.decode_eq_some_iff _ _).mp hdecode
      have hterm := (termTokensDecoder.decode_eq_some_iff _ _).mp
        (termTokensDecoder_decode_encTerm t)
      exact ⟨t, hterm.symm.trans ((congrArg (encList encTermToken) htokens).trans hword), ht⟩
    · cases hvalue
  · rintro ⟨t, hword, hvalue⟩
    rw [← hword, evalTermWord_encTerm, hvalue]

/-- Uniform polynomial time on raw words, with a positive binary modulus and a framed list
of binary coordinates. The result uses the standard option encoding of a binary residue. -/
theorem evalTermWord_polyTime {γ : Type} {enc : γ ↪ List Bool}
    {modulus : γ → ℕ} {point : γ → List ℕ} {word : γ → List Bool}
    (hp : ComputableInPolyTime modulus enc encNat) (hpos : ∀ a, 0 < modulus a)
    (hx : ComputableInPolyTime point enc (encList encNat))
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => evalTermWord (modulus a) (point a) (word a))
      enc (encOption encNat) := by
  let encTokens := encList encTermToken
  let encStack := encList encNat
  have hinput := fst enc encTokens
  have hstack := evalTokenStack_polyTime (hp.comp hinput) (fun a => hpos a.1)
    (hx.comp hinput) (snd enc encTokens)
  have hsingle : ComputableInPolyTime
      (fun stack : List ℕ => if stack.tail.isEmpty then stack.head? else none)
      encStack (encOption encNat) :=
    ((listIsEmpty' encNat).comp (listTail encNat)).ite' (head? encNat) (.const none)
  have hresult := hstack.optionElimWithInput (body := fun _ stack =>
    if stack.tail.isEmpty then stack.head? else none) (.const none)
    (hsingle.comp (snd (encPair enc encTokens) encStack))
  unfold evalTermWord
  option_match_to_elim
  exact (termTokensDecoder.computable.comp hw).optionElimWithInput (.const none) hresult

end Cslib.Logic.RealArithmetic.Term
