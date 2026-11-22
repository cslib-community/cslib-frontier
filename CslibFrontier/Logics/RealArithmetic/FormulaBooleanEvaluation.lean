/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation

/-!
# Backward Boolean evaluation of formula words

This adapts the wire scan and its correctness proof from
`LeanCanny.Computation.BooleanCircuitSpace` and `LeanCanny.ETR.FormulaBooleanCircuitCorrect`
at lean-canny revision `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
Every operand follows its parent in the prefix token stream, so visiting tokens from right to
left gives each gate access to its previously computed operands. Arithmetic comparisons use
a supplied interpretation of term-word signs.
-/

public section

namespace Cslib.Logic.RealArithmetic

/-- Evaluate a formula with each comparison interpreted by its term's supplied sign. -/
@[expose] def Formula.evalTermSigns {n : ℕ} (termSign : Term n → SignType) : Formula n → Bool
  | .false => Bool.false
  | .eqZero t => decide (termSign t = 0)
  | .ltZero t => decide (termSign t = -1)
  | .not p => !(p.evalTermSigns termSign)
  | .and p q => p.evalTermSigns termSign && q.evalTermSigns termSign
  | .or p q => p.evalTermSigns termSign || q.evalTermSigns termSign

private def gateValuesAux (word : List Bool) (termSign : List Bool → SignType)
    (size : ℕ) : ℕ → List Bool
  | 0 => []
  | k + 1 =>
    let index := size - (k + 1)
    let suffix := gateValuesAux word termSign size k
    formulaWordGateValue word index termSign
      (fun child => if index < child then suffix.getD (child - (index + 1)) false else false)
      :: suffix

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

end Cslib.Logic.RealArithmetic
