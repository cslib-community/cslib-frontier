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
  exact ((listIsEmpty' encNat).comp ht).ite' (.const none) <| pushResidue_polyTime
    (binary_mod' (hop.comp (((headD 0).comp hs).prod ((headD 0).comp ht))) hp)
    ((listTail encNat).comp ht)

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
  have hp1 := (fst enc (encSum encUnary (encSum encUnit encUnit))).comp (fst _ encUnary)
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
  rcases token a with z | i | _ | _ <;> rcases stack a with _ | ⟨l, _ | ⟨r, rest⟩⟩ <;>
    simp [evalTokenStep, combineResidues, List.getD_eq_getElem?_getD]

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
  have hkeep := fst stepEnc (encList encNat)
  have hparam := ((fst enc stackEnc).comp (fst (encPair enc stackEnc) encTermToken)).comp hkeep
  have hstep : ComputableInPolyTime (fun a => step a.1.1 a.1.2 a.2) stepEnc stackEnc := by
    dsimp only [step]
    option_match_to_elim
    exact optionElimWithInput ((snd enc stackEnc).comp (fst _ encTermToken)) (.const none)
      (evalTokenStep_polyTime (hp.comp hparam) (hx.comp hparam) (snd stepEnc (encList encNat))
        ((snd _ encTermToken).comp hkeep))
  have hsize := (ht.polyBounded_length.mul
    (((PolyBounded.const 2).mul hp.polyBounded_length).add (.const 1))).add (.const 1)
  refine (foldlWith (encA := encTermToken) (step := step) id'
    ((listReverse encTermToken).comp ht) (.const (some [])) hstep hsize ?_).of_enc_eq fun a => ?_
  · intro a i hi
    let suffix := ((tokens a).reverse.take i).reverse
    rw [List.foldl_eq_foldr_reverse]
    change (stackEnc (evalTokenStack (modulus a) (point a) suffix [])).length ≤ _
    cases h : evalTokenStack (modulus a) (point a) suffix [] with
    | none => exact Nat.zero_le _
    | some residues =>
      obtain ⟨hentries, hresidues⟩ := evalTokenStack_bounds (hpos a) (point a) suffix (by simp) h
      have hcount : residues.length ≤ (encList encTermToken (tokens a)).length :=
        (by simpa using hentries : residues.length ≤ suffix.length).trans <|
          ((List.length_reverse.trans_le (List.length_take_le _ _)).trans
            (by simpa [List.length_reverse] using hi)).trans
            (SizedListEncoding.length_le encTermToken (encL := encList encTermToken) (tokens a))
      have hbits := length_encList_le encNat residues (b := (encNat (modulus a)).length) fun r hr =>
        by simpa only [length_encNat_eq_size] using Nat.size_le_size (hresidues r hr).le
      exact Nat.add_le_add_right (hbits.trans (Nat.mul_le_mul_right _ hcount)) 1
  · change stackEnc (evalTokenStack (modulus a) (point a) (tokens a) []) =
      stackEnc ((tokens a).reverse.foldl (step a) (some []))
    rw [List.foldl_reverse]
    rfl

/-- Evaluate a raw term word using natural-number variable ranks and zero-padded coordinates.
Return a residue only if strict token decoding and stack evaluation leave a singleton stack. -/
@[expose] def evalTermWord (p : ℕ) (point : List ℕ) (word : List Bool) : Option ℕ := do
  let tokens ← termTokensDecoder.decode word
  let stack ← evalTokenStack p point tokens []
  if stack.tail.isEmpty then stack.head? else none

/-- Evaluation of a canonical term word returns its syntax-directed modular residue. -/
theorem evalTermWord_encTerm {n : ℕ} (p : ℕ) (point : List ℕ) (t : Term n) :
    evalTermWord p point (encTerm n t) = some (t.evalResidue p point) := by
  simp [evalTermWord, termTokensDecoder_decode_encTerm, evalTokenStack_tokens]

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
    obtain ⟨intermediate, htail, hstep⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨terms, htokens, rfl⟩ := ih (fun i hi => hrank i (List.mem_cons_of_mem _ hi)) htail
    rcases token with z | i | ⟨⟩ | ⟨⟩
    · cases hstep
      exact ⟨.const z :: terms, congrArg (_ :: ·) htokens, rfl⟩
    · cases hstep
      exact ⟨.var ⟨i, hrank i List.mem_cons_self⟩ :: terms, congrArg (_ :: ·) htokens, rfl⟩
    · rcases terms with _ | ⟨l, _ | ⟨r, rest⟩⟩ <;> cases hstep
      exact ⟨.add l r :: rest, by
        simpa [encTerm_tokens, TermToken.ofFin, List.append_assoc] using
          congrArg (Sum.inr (Sum.inr (.inl ())) :: ·) htokens, rfl⟩
    · rcases terms with _ | ⟨l, _ | ⟨r, rest⟩⟩ <;> cases hstep
      exact ⟨.mul l r :: rest, by
        simpa [encTerm_tokens, TermToken.ofFin, List.append_assoc] using
          congrArg (Sum.inr (Sum.inr (.inr ())) :: ·) htokens, rfl⟩

/-- Raw evaluation succeeds with a residue exactly on words encoding a single term with that
residue. The input length suffices as the ambient dimension for the reconstructed term. -/
theorem evalTermWord_eq_some_iff {p value : ℕ} {point : List ℕ} {word : List Bool} :
    evalTermWord p point word = some value ↔
      ∃ t : Term word.length, encTerm word.length t = word ∧ t.evalResidue p point = value := by
  refine ⟨fun h => ?_, fun ⟨t, hword, hvalue⟩ => hword ▸ hvalue ▸ evalTermWord_encTerm p point t⟩
  simp only [evalTermWord, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨tokens, hdecode, _ | ⟨r, _ | _⟩, hstack, hvalue⟩ := h <;> cases hvalue
  obtain ⟨terms, htokens, hresidues⟩ := exists_terms_of_evalTokenStack point tokens
    (fun _ => termTokenRank_lt_of_decode hdecode) hstack
  obtain ⟨t, rfl, ht⟩ := List.map_eq_singleton_iff.mp hresidues
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at htokens
  exact ⟨t, ((termTokensDecoder.decode_eq_some_iff _ _).mp
    (termTokensDecoder_decode_encTerm t)).symm.trans ((congrArg (encList encTermToken)
      htokens).trans ((termTokensDecoder.decode_eq_some_iff _ _).mp hdecode)), ht⟩

/-- Uniform polynomial time on raw words, with a positive binary modulus and a framed list
of binary coordinates. The result uses the standard option encoding of a binary residue. -/
theorem evalTermWord_polyTime {γ : Type} {enc : γ ↪ List Bool}
    {modulus : γ → ℕ} {point : γ → List ℕ} {word : γ → List Bool}
    (hp : ComputableInPolyTime modulus enc encNat) (hpos : ∀ a, 0 < modulus a)
    (hx : ComputableInPolyTime point enc (encList encNat))
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun a => evalTermWord (modulus a) (point a) (word a))
      enc (encOption encNat) := by
  have hinput := fst enc (encList encTermToken)
  have hsingle := (((listIsEmpty' encNat).comp (listTail encNat)).ite'
    (head? encNat) (.const none)).comp (snd (encPair enc (encList encTermToken)) (encList encNat))
  unfold evalTermWord
  option_match_to_elim
  exact (termTokensDecoder.computable.comp hw).optionElimWithInput (.const none) <|
    (evalTokenStack_polyTime (hp.comp hinput) (fun a => hpos a.1) (hx.comp hinput)
      (snd enc (encList encTermToken))).optionElimWithInput (.const none) hsingle

end Cslib.Logic.RealArithmetic.Term
