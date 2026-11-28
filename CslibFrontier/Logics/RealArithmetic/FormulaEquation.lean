/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.RealArithmetic.FormulaWordValidation
import CslibFrontier.Logics.RealArithmetic.FormulaBooleanEvaluation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Encoding formula gates by one real equation

Allocate a truth variable and two witness variables for each token of the total formula view.
Local equations constrain an atom's truth value using an inverse or square-root witness.
Connectives use their Boolean truth tables evaluated on their child coordinates. Requiring the
root to be true and combining every equation by a sum of squares gives one equation.
The construction adapts lean-canny's tree-to-equations reduction at
`970f28a5ecefc1327402ade16c068aa4b1b2c183` to the frontier indexed token view.

## Main results

* `formulaWordEquation_eval_zero_iff` characterizes the projection of the equation's real zeros
  onto the original coordinates, on every word including malformed input.
-/

public section

namespace Cslib.Logic.RealArithmetic

private abbrev gateCount (word : List Bool) : ℕ := (formulaWordTokens word).length

/-- The original coordinates followed by the truth, first witness and second witness blocks.
Each auxiliary block has one coordinate per token of the total formula view. -/
abbrev formulaEquationArity (word : List Bool) : ℕ :=
  let gates := (formulaWordTokens word).length
  word.length + (gates + (gates + gates))

private abbrev inputCoord (word : List Bool) : Fin word.length → Fin (formulaEquationArity word) :=
  Fin.castAdd _

private abbrev truthCoord (word : List Bool) : Fin (gateCount word) →
    Fin (formulaEquationArity word) :=
  fun i => Fin.natAdd _ (Fin.castAdd _ i)

private abbrev firstCoord (word : List Bool) : Fin (gateCount word) →
    Fin (formulaEquationArity word) :=
  fun i => Fin.natAdd _ (Fin.natAdd _ (Fin.castAdd _ i))

private abbrev secondCoord (word : List Bool) : Fin (gateCount word) →
    Fin (formulaEquationArity word) :=
  fun i => Fin.natAdd _ (Fin.natAdd _ (Fin.natAdd _ i))

private theorem gateCount_pos (word : List Bool) : 0 < gateCount word := by
  unfold gateCount
  rw [formulaWordTokens_eq, List.length_map]
  cases Formula.ofWord word <;> simp [encFormula_tokens]

private def termSub {n : ℕ} (a b : Term n) : Term n := .add a (.mul (.const (-1)) b)

@[simp] private theorem eval_termSub {n : ℕ} (a b : Term n) (x : Fin n → ℝ) :
    (termSub a b).eval x = a.eval x - b.eval x := by
  simp [termSub, Term.eval, sub_eq_add_neg]

private def bitValue (b : Bool) : ℝ := if b then 1 else 0

private def bitTerm {n : ℕ} (b : Bool) : Term n := .const (if b then 1 else 0)

@[simp] private theorem eval_bitTerm {n : ℕ} (b : Bool) (x : Fin n → ℝ) :
    (bitTerm b).eval x = bitValue b := by
  cases b <;> simp [bitTerm, bitValue, Term.eval]

private theorem bitValue_injective : Function.Injective bitValue := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitValue]

private def selectTerm {n : ℕ} (bit yes no : Term n) : Term n :=
  .add (.mul bit yes) (.mul (termSub (.const 1) bit) no)

private theorem eval_selectTerm {n : ℕ} (bit yes no : Term n) (x : Fin n → ℝ)
    (b : Bool) (h : bit.eval x = bitValue b) :
    (selectTerm bit yes no).eval x = (if b then yes else no).eval x := by
  cases b <;> simp [selectTerm, Term.eval, h, bitValue]

private def childBit (word : List Bool) (index child : ℕ)
    (bits : Fin (gateCount word) → Bool) : Bool :=
  if h : index < child ∧ child < gateCount word then bits ⟨child, h.2⟩ else false

private def childTerm (word : List Bool) (index child : ℕ) : Term (formulaEquationArity word) :=
  if h : index < child ∧ child < gateCount word then .var (truthCoord word ⟨child, h.2⟩)
  else .const 0

private theorem eval_childTerm (word : List Bool) (index child : ℕ)
    (x : Fin (formulaEquationArity word) → ℝ) (bits : Fin (gateCount word) → Bool)
    (hbit : ∀ i, x (truthCoord word i) = bitValue (bits i)) :
    (childTerm word index child).eval x = bitValue (childBit word index child bits) := by
  unfold childTerm childBit
  split <;> simp_all [Term.eval, bitValue]

private def booleanTerm (word : List Bool) (index : ℕ) : Term (formulaEquationArity word) :=
  let children := formulaWordChildIndices word index
  let left := children.getD 0 0
  let right := children.getD 1 0
  let entry (l r : Bool) :=
    bitTerm (formulaWordGateValueWithAnswer word index false (fun j => if j = left then l else r))
  selectTerm (childTerm word index left)
    (selectTerm (childTerm word index right) (entry true true) (entry true false))
    (selectTerm (childTerm word index right) (entry false true) (entry false false))

private theorem eval_booleanTerm (word : List Bool) (index : ℕ)
    (x : Fin (formulaEquationArity word) → ℝ) (bits : Fin (gateCount word) → Bool)
    (hbit : ∀ i, x (truthCoord word i) = bitValue (bits i)) :
    (booleanTerm word index).eval x =
      bitValue (formulaWordGateValueWithAnswer word index false
        (fun child => childBit word index child bits)) := by
  let left := (formulaWordChildIndices word index).getD 0 0
  let right := (formulaWordChildIndices word index).getD 1 0
  let bit (j : ℕ) := childBit word index j bits
  let entry (l r : Bool) := bitTerm (n := formulaEquationArity word)
    (formulaWordGateValueWithAnswer word index false (fun j => if j = left then l else r))
  change (selectTerm (childTerm word index left)
    (selectTerm (childTerm word index right) (entry true true) (entry true false))
    (selectTerm (childTerm word index right) (entry false true) (entry false false))).eval x = _
  have hleft : (childTerm word index left).eval x = bitValue (bit left) :=
    eval_childTerm word index left x bits hbit
  have hright : (childTerm word index right).eval x = bitValue (bit right) :=
    eval_childTerm word index right x bits hbit
  have hcongr : formulaWordGateValueWithAnswer word index false
      (fun j => if j = left then bit left else bit right) =
        formulaWordGateValueWithAnswer word index false bit := by
    apply formulaWordGateValueWithAnswer_congr_children
    · change (if left = left then bit left else bit right) = bit left
      rw [ite_eq_left rfl]
    · change (if right = left then bit left else bit right) = bit right
      split
      · next h => rw [h]
      · rfl
  change _ = bitValue (formulaWordGateValueWithAnswer word index false bit)
  rw [← hcongr, eval_selectTerm _ _ _ _ _ hleft]
  cases bit left <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals
    rw [eval_selectTerm _ _ _ _ _ hright]
    cases bit right <;> simp [entry]

private noncomputable def gateEquations (word : List Bool) (i : Fin (gateCount word)) :
    List (Term (formulaEquationArity word)) :=
  let bit := Term.var (truthCoord word i)
  let off := termSub (.const 1) bit
  let first := Term.var (firstCoord word i)
  let second := Term.var (secondCoord word i)
  let atom := (formulaWordGateTerm word i).rename (inputCoord word)
  match formulaWordComparisonRequest word i with
  | none => [termSub bit (booleanTerm word i)]
  | some request =>
    if request.isStrict then
      [.mul bit (.add (.mul atom (.mul first first)) (.const 1)),
        .mul off (termSub atom (.mul second second))]
    else [.mul bit atom, .mul off (termSub (.mul atom first) (.const 1))]

private def bitConstraint (word : List Bool) (i : Fin (gateCount word)) :
    Term (formulaEquationArity word) :=
  let bit := Term.var (truthCoord word i)
  .mul bit (termSub bit (.const 1))

private def sumSquares {n : ℕ} (terms : List (Term n)) : Term n :=
  terms.foldr (fun term tail => .add (.mul term term) tail) (.const 0)

private theorem eval_sumSquares_zero_iff {n : ℕ} (terms : List (Term n)) (point : Fin n → ℝ) :
    (sumSquares terms).eval point = 0 ↔ ∀ term ∈ terms, term.eval point = 0 := by
  have nonneg (ts : List (Term n)) : 0 ≤ (sumSquares ts).eval point := by
    induction ts with
    | nil => simp [sumSquares, Term.eval]
    | cons t ts ih =>
      change 0 ≤ t.eval point * t.eval point + (sumSquares ts).eval point
      exact add_nonneg (mul_self_nonneg _) ih
  induction terms with
  | nil => simp [sumSquares, Term.eval]
  | cons term tail ih =>
    change term.eval point * term.eval point + (sumSquares tail).eval point = 0 ↔ _
    constructor
    · intro h
      have ht : 0 ≤ term.eval point * term.eval point := mul_self_nonneg _
      have hr := nonneg tail
      have hzero : term.eval point * term.eval point = 0 := by linarith
      have htail : (sumSquares tail).eval point = 0 := by linarith
      exact List.forall_mem_cons.mpr ⟨(mul_eq_zero.mp hzero).elim id id, ih.mp htail⟩
    · intro h
      obtain ⟨ht, hr⟩ := List.forall_mem_cons.mp h
      rw [ht, ih.mpr hr, zero_mul, add_zero]

private def root (word : List Bool) : Fin (gateCount word) := ⟨0, gateCount_pos word⟩

/-- The sum of squares of the root truth requirement and every local gate constraint. -/
noncomputable def formulaWordEquation (word : List Bool) : Term (formulaEquationArity word) :=
  sumSquares (termSub (.var (truthCoord word (root word))) (.const 1) ::
    (List.finRange (gateCount word)).flatMap fun i => bitConstraint word i :: gateEquations word i)

private def gateCondition (word : List Bool) (i : Fin (gateCount word))
    (x : Fin word.length → ℝ) (bits : Fin (gateCount word) → Bool) (first second : ℝ) : Prop :=
  match formulaWordComparisonRequest word i with
  | none => bits i = formulaWordGateValueWithAnswer word i false
      (fun child => childBit word i child bits)
  | some request =>
    let bit := bitValue (bits i)
    let value := (formulaWordGateTerm word i).eval x
    if request.isStrict then
      bit * (value * first ^ 2 + 1) = 0 ∧ (1 - bit) * (value - second ^ 2) = 0
    else bit * value = 0 ∧ (1 - bit) * (value * first - 1) = 0

private theorem eval_gateEquations_iff (word : List Bool) (i : Fin (gateCount word))
    (y : Fin (formulaEquationArity word) → ℝ) (bits : Fin (gateCount word) → Bool)
    (hbits : ∀ j, y (truthCoord word j) = bitValue (bits j)) :
    (∀ term ∈ gateEquations word i, term.eval y = 0) ↔
      gateCondition word i (y ∘ inputCoord word) bits (y (firstCoord word i))
        (y (secondCoord word i)) := by
  unfold gateEquations gateCondition
  cases hrequest : formulaWordComparisonRequest word i with
  | none =>
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true, eval_termSub, Term.eval, eval_booleanTerm word i y bits hbits, hbits,
      sub_eq_zero]
    exact bitValue_injective.eq_iff
  | some request =>
    cases hstrict : request.isStrict <;>
      simp [hstrict, eval_termSub, Term.eval, hbits, Term.eval_rename, pow_two]

private theorem exists_eqAtomWitness_iff (value bit : ℝ) (hbit : bit = 0 ∨ bit = 1) :
    (∃ witness : ℝ, bit * value = 0 ∧ (1 - bit) * (value * witness - 1) = 0) ↔
      (bit = 1 ↔ value = 0) := by
  rcases hbit with rfl | rfl
  · simp only [zero_mul, sub_zero, one_mul, true_and, zero_ne_one, false_iff]
    constructor
    · rintro ⟨w, hw⟩ rfl
      simp at hw
    · intro h
      exact ⟨value⁻¹, by rw [mul_inv_cancel₀ h, sub_self]⟩
  · simp [sub_self]

private theorem exists_ltAtomWitness_iff (value bit : ℝ) (hbit : bit = 0 ∨ bit = 1) :
    (∃ strict weak : ℝ, bit * (value * strict ^ 2 + 1) = 0 ∧
      (1 - bit) * (value - weak ^ 2) = 0) ↔ (bit = 1 ↔ value < 0) := by
  rcases hbit with rfl | rfl
  · simp only [zero_mul, sub_zero, one_mul, true_and, zero_ne_one, false_iff, not_lt]
    constructor
    · rintro ⟨_, w, hw⟩
      rw [sub_eq_zero.mp hw]
      exact sq_nonneg _
    · intro h
      exact ⟨0, Real.sqrt value, by rw [Real.sq_sqrt h, sub_self]⟩
  · simp only [one_mul, sub_self, zero_mul, and_true, true_iff]
    constructor
    · rintro ⟨strict, _, hstrict⟩
      by_contra! h
      have hprod := mul_nonneg h (sq_nonneg strict)
      linarith
    · intro h
      have hpos : 0 < -value := neg_pos.mpr h
      refine ⟨Real.sqrt (-value)⁻¹, 0, ?_⟩
      rw [Real.sq_sqrt (inv_nonneg.mpr hpos.le)]
      have hprod := mul_inv_cancel₀ hpos.ne'
      rw [neg_mul] at hprod
      linarith

private noncomputable def termSign (word : List Bool) (x : Fin word.length → ℝ) :
    List Bool → SignType :=
  Function.extend (encTerm word.length) (fun t => SignType.sign (t.eval x)) (fun _ => 0)

private theorem termSign_encTerm (word : List Bool) (x : Fin word.length → ℝ)
    (t : Term word.length) :
    termSign word x (encTerm word.length t) = SignType.sign (t.eval x) :=
  (encTerm word.length).injective.extend_apply _ _ t

private theorem exists_gateCondition_iff (word : List Bool) (i : Fin (gateCount word))
    (x : Fin word.length → ℝ) (bits : Fin (gateCount word) → Bool) :
    (∃ first second, gateCondition word i x bits first second) ↔
      bits i = formulaWordGateValue word i (termSign word x)
        (fun child => childBit word i child bits) := by
  rw [← formulaWordGateValueWithAnswer_eq]
  unfold gateCondition
  cases hrequest : formulaWordComparisonRequest word i with
  | none => simp
  | some request =>
    rw [Option.any_some]
    have hword := encTerm_formulaWordGateTerm word i
    rw [formulaWordGateTermWord, hrequest, Option.elim_some] at hword
    rw [← hword, termSign_encTerm]
    let value := (formulaWordGateTerm word i).eval x
    let bit := bitValue (bits i)
    have hbit : bit = 0 ∨ bit = 1 := by cases h : bits i <;> simp [bit, bitValue, h]
    cases hstrict : request.isStrict
    · simp only [hstrict, Bool.false_eq_true, ite_false, exists_const,
        FormulaComparisonRequest.requestedSign, sign_eq_zero_iff]
      change (∃ w : ℝ, bit * value = 0 ∧ (1 - bit) * (value * w - 1) = 0) ↔ _
      rw [exists_eqAtomWitness_iff value bit hbit]
      cases h : bits i <;>
        simp [bit, bitValue, h, value, formulaWordGateValueWithAnswer_of_request hrequest]
    · simp only [hstrict, ite_true, FormulaComparisonRequest.requestedSign, sign_eq_neg_one_iff]
      change (∃ a b : ℝ, bit * (value * a ^ 2 + 1) = 0 ∧ (1 - bit) * (value - b ^ 2) = 0) ↔ _
      rw [exists_ltAtomWitness_iff value bit hbit]
      cases h : bits i <;>
        simp [bit, bitValue, h, value, formulaWordGateValueWithAnswer_of_request hrequest]

private noncomputable def computedBits (word : List Bool) (x : Fin word.length → ℝ)
    (i : Fin (gateCount word)) : Bool :=
  (formulaWordGateValues word (termSign word x)).getD i false

private theorem computedBits_step (word : List Bool) (x : Fin word.length → ℝ)
    (i : Fin (gateCount word)) :
    computedBits word x i = formulaWordGateValue word i (termSign word x)
      (fun child => childBit word i child (computedBits word x)) := by
  rw [computedBits, formulaWordGateValues_getD_step word _ _ i.isLt]
  congr 1
  funext child
  unfold childBit
  by_cases h : (i : ℕ) < child
  · by_cases hc : child < gateCount word
    · simp [h, hc, computedBits]
    · rw [ite_eq_left h, dite_eq_right (fun hs => hc hs.2), List.getD_eq_default]
      rw [formulaWordGateValues_length]
      exact Nat.le_of_not_lt hc
  · simp [h]

private theorem bits_eq_computedBits (word : List Bool) (x : Fin word.length → ℝ)
    (bits : Fin (gateCount word) → Bool)
    (h : ∀ i, bits i = formulaWordGateValue word i (termSign word x)
      (fun child => childBit word i child bits)) (i : Fin (gateCount word)) :
    bits i = computedBits word x i := by
  have agree (remaining : ℕ) : ∀ j : Fin (gateCount word), gateCount word - j = remaining →
      bits j = computedBits word x j := by
    induction remaining using Nat.strong_induction_on with
    | ind remaining ih =>
      intro j hj
      rw [h j, computedBits_step word x j]
      congr 1
      funext child
      unfold childBit
      split
      · next hc =>
        exact ih (gateCount word - child) (by have := j.isLt; omega) ⟨child, hc.2⟩ rfl
      · rfl
  exact agree _ i rfl

private theorem computedBits_root_eq_true_iff (word : List Bool) (x : Fin word.length → ℝ) :
    computedBits word x (root word) = true ↔ x ∈ (Formula.ofWord word).solutionSet :=
  formulaWordGateValues_getD_zero_eq_true_iff word (termSign word x) x
    (fun t _ => termSign_encTerm word x t)

private theorem eval_formulaWordEquation_iff (word : List Bool)
    (y : Fin (formulaEquationArity word) → ℝ) :
    (formulaWordEquation word).eval y = 0 ↔ y (truthCoord word (root word)) = 1 ∧
      ∀ i, (y (truthCoord word i) = 0 ∨ y (truthCoord word i) = 1) ∧
        ∀ term ∈ gateEquations word i, term.eval y = 0 := by
  have hbit (i : Fin (gateCount word)) :
      (bitConstraint word i).eval y = 0 ↔
        y (truthCoord word i) = 0 ∨ y (truthCoord word i) = 1 := by
    rw [bitConstraint, Term.eval, eval_termSub]
    simp only [Term.eval, Int.cast_one, mul_eq_zero, sub_eq_zero]
  rw [formulaWordEquation, eval_sumSquares_zero_iff, List.forall_mem_cons, eval_termSub]
  simp only [Term.eval, Int.cast_one, sub_eq_zero]
  apply and_congr_right
  intro _
  constructor
  · intro all i
    have hi : ∀ term ∈ bitConstraint word i :: gateEquations word i, term.eval y = 0 :=
      fun term ht => all term (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ht⟩)
    obtain ⟨hb, hg⟩ := List.forall_mem_cons.mp hi
    exact ⟨(hbit i).mp hb, hg⟩
  · intro all term ht
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp ht
    obtain ⟨hb, hg⟩ := all i
    have hterms : ∀ t ∈ bitConstraint word i :: gateEquations word i, t.eval y = 0 :=
      List.forall_mem_cons.mpr ⟨(hbit i).mpr hb, hg⟩
    exact hterms term hi

/-- A real assignment satisfies the total formula view exactly when it extends to a zero
of its equation. The initial coordinates of the extended assignment are the original ones. -/
theorem formulaWordEquation_eval_zero_iff (word : List Bool) (x : Fin word.length → ℝ) :
    (∃ y : Fin (formulaEquationArity word) → ℝ, y ∘ Fin.castAdd _ = x ∧
      (formulaWordEquation word).eval y = 0) ↔ x ∈ (Formula.ofWord word).solutionSet := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    obtain ⟨hroot, hgate⟩ := (eval_formulaWordEquation_iff word y).mp hy
    let bits (i : Fin (gateCount word)) := decide (y (truthCoord word i) = 1)
    have hbits (i : Fin (gateCount word)) : y (truthCoord word i) = bitValue (bits i) := by
      rcases (hgate i).1 with h | h <;> simp [bits, bitValue, h]
    have hstep (i : Fin (gateCount word)) : bits i = formulaWordGateValue word i
        (termSign word (y ∘ inputCoord word)) (fun child => childBit word i child bits) :=
      (exists_gateCondition_iff word i _ bits).mp
        ⟨_, _, (eval_gateEquations_iff word i y bits hbits).mp (hgate i).2⟩
    have hr : bits (root word) = true := by simp [bits, hroot]
    rw [bits_eq_computedBits word (y ∘ inputCoord word) bits hstep] at hr
    exact (computedBits_root_eq_true_iff word _).mp hr
  · intro hx
    let bits := computedBits word x
    have hw (i : Fin (gateCount word)) : ∃ first second, gateCondition word i x bits first second :=
      (exists_gateCondition_iff word i x bits).mpr (computedBits_step word x i)
    choose first second hw using hw
    let y : Fin (formulaEquationArity word) → ℝ :=
      Fin.addCases x (Fin.addCases (bitValue ∘ bits) (Fin.addCases first second))
    have hinput : y ∘ inputCoord word = x := by
      funext i
      simp only [y, Function.comp_apply, Fin.addCases_left]
    have hbits (i : Fin (gateCount word)) : y (truthCoord word i) = bitValue (bits i) := by
      simp [y]
    have hfirst (i : Fin (gateCount word)) : y (firstCoord word i) = first i := by
      simp [y]
    have hsecond (i : Fin (gateCount word)) : y (secondCoord word i) = second i := by
      simp only [y, Fin.addCases_right]
    refine ⟨y, hinput, (eval_formulaWordEquation_iff word y).mpr ⟨?_, ?_⟩⟩
    · have hr : bits (root word) = true := (computedBits_root_eq_true_iff word x).mpr hx
      rw [hbits, hr]
      rfl
    · intro i
      refine ⟨?_, (eval_gateEquations_iff word i y bits hbits).mpr ?_⟩
      · rw [hbits]
        cases bits i <;> simp [bitValue]
      · rw [hinput, hfirst, hsecond]
        exact hw i

end Cslib.Logic.RealArithmetic
