/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Backward Boolean evaluation of formula words

This adapts the wire scan and its correctness proof from
`LeanCanny.Computation.BooleanCircuitSpace` and `LeanCanny.ETR.FormulaBooleanCircuitCorrect`
at lean-canny revision `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
Every operand follows its parent in the prefix token stream, so visiting tokens from right to
left gives each gate access to its previously computed operands. Arithmetic comparisons use
a supplied interpretation of term-word signs. Correct signs for the comparison terms appearing
in the word suffice for the root value to characterize membership in the real solution set.
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

private def gateValuesAux (word : List Bool) (termSign : List Bool → SignType)
    (size : ℕ) : ℕ → List Bool
  | 0 => []
  | k + 1 =>
    let index := size - (k + 1)
    let suffix := gateValuesAux word termSign size k
    formulaWordGateValue word index termSign (formulaGateSuffixValue suffix index) :: suffix

/-- Evaluate all gates of the total formula view from right to left, returning their Boolean
values in prefix order. A child is read from the already evaluated suffix. -/
def formulaWordGateValues (word : List Bool) (termSign : List Bool → SignType) : List Bool :=
  let size := (formulaWordTokens word).length
  gateValuesAux word termSign size size

/-- The scan stores one Boolean value per token. -/
theorem formulaWordGateValues_length (word : List Bool) (termSign : List Bool → SignType) :
    (formulaWordGateValues word termSign).length = (formulaWordTokens word).length := by
  have length_aux (size count : ℕ) : (gateValuesAux word termSign size count).length = count := by
    induction count with
    | zero => rfl
    | succ count ih => simp only [gateValuesAux, List.length_cons, ih]
  exact length_aux _ _

private theorem gateValuesAux_getD (word : List Bool) (termSign : List Bool → SignType)
    (size count offset : ℕ) :
    (gateValuesAux word termSign size count).getD offset false =
      (gateValuesAux word termSign size (count - offset)).getD 0 false := by
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
    ⟨(formulaWordTokens word).length - index - 1, by omega⟩
  have hindex : (formulaWordTokens word).length - (k + 1) = index := by omega
  rw [formulaWordGateValues, gateValuesAux_getD, hk, gateValuesAux, List.getD_cons_zero, hindex]
  congr 1
  funext child
  unfold formulaGateSuffixValue
  split
  · rw [gateValuesAux_getD,
      gateValuesAux_getD word termSign _ (formulaWordTokens word).length child]
    congr 2
    omega
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

private theorem evalTermSigns_eq_true_iff_of_token_signs {n : ℕ} (p : Formula n)
    (termSign : Term n → SignType) (x : Fin n → ℝ)
    (hsign : ∀ t, .inr (.inl t) ∈ encFormula_tokens n p ∨
        .inr (.inr (.inl t)) ∈ encFormula_tokens n p → termSign t = SignType.sign (t.eval x)) :
    p.evalTermSigns termSign = true ↔ x ∈ p.solutionSet := by
  have restrict {parent child : Formula n} (hsub : encFormula_tokens n child ⊆
      encFormula_tokens n parent)
      (h : ∀ t, .inr (.inl t) ∈ encFormula_tokens n parent ∨
        .inr (.inr (.inl t)) ∈ encFormula_tokens n parent → termSign t = SignType.sign (t.eval x))
      (t : Term n) (ht : .inr (.inl t) ∈ encFormula_tokens n child ∨
        .inr (.inr (.inl t)) ∈ encFormula_tokens n child) :
      termSign t = SignType.sign (t.eval x) :=
    h t (ht.imp (fun hm => hsub hm) (fun hm => hsub hm))
  induction p with
  | false => simp [Formula.evalTermSigns, Formula.solutionSet]
  | eqZero t =>
    have ht := hsign t (.inl (by simp [encFormula_tokens]))
    simp [Formula.evalTermSigns, Formula.solutionSet, ht]
  | ltZero t =>
    have ht := hsign t (.inr (by simp [encFormula_tokens]))
    simp [Formula.evalTermSigns, Formula.solutionSet, ht, sign_eq_neg_one_iff]
  | not p ih =>
    have hp := ih (restrict (by intro token ht; simp [encFormula_tokens, ht]) hsign)
    simp [Formula.evalTermSigns, Formula.solutionSet, Bool.eq_false_iff, hp]
  | and p q ihp ihq | or p q ihp ihq =>
    have hp := ihp (restrict (by intro token ht; simp [encFormula_tokens, ht]) hsign)
    have hq := ihq (restrict (by intro token ht; simp [encFormula_tokens, ht]) hsign)
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

end Cslib.Logic.RealArithmetic
