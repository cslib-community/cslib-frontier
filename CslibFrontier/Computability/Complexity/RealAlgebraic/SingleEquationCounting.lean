/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy
public import CslibFrontier.Logics.RealArithmetic.Encoding
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledFeasibility
import CslibFrontier.Logics.RealArithmetic.TokenEvaluationPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Counting-hierarchy bound for a single real equation

The input encodes the arithmetic term on the left of an equation with zero on the right.
The term evaluator computes residues in polynomial time, and the word length bounds its
arity, degree and coefficient norm exponent. Malformed words are modelled by the constant
one polynomial, so the real-zero test rejects them.

This adapts lean-canny's [term-family realization](
https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/EncodedTermPolynomial.lean)
to the frontier term encoding.

## Main result

* `Cslib.Complexity.realSingleEquation_mem_countingLevel`: single real equation feasibility
  is in `C₂₆P`.
-/

public section

namespace Cslib.Complexity

open Logic.RealArithmetic RealAlgebraic Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Words encoding one integer arithmetic term with a real zero. Since variable indices are
unary, the word length suffices as the ambient dimension. Malformed words are rejected. -/
@[expose] def RealSingleEquation : Set (List Bool) :=
  {word | ∃ t : Term word.length, encTerm word.length t = word ∧ ∃ x, t.eval x = 0}

private theorem exists_eval_eq_zero_rename {n m : ℕ} {f : Fin n → Fin m}
    (hf : Function.Injective f) (t : Term n) :
    (∃ x, (t.rename f).eval x = 0) ↔ ∃ x, t.eval x = 0 := by
  simpa only [Formula.rename, Formula.solutionSet, Set.nonempty_def, Set.mem_ofPred_eq] using
    Formula.solutionSet_nonempty_rename hf (.eqZero t)

/-- Encoding a term preserves real feasibility, even when its ambient dimension contains
unused coordinates and is larger than the encoding length. -/
theorem encTerm_mem_RealSingleEquation {n : ℕ} (t : Term n) :
    encTerm n t ∈ RealSingleEquation ↔ ∃ x, t.eval x = 0 := by
  let word := encTerm n t
  change (∃ u : Term word.length, encTerm word.length u = word ∧ ∃ x, u.eval x = 0) ↔ _
  obtain ⟨u, hu, _⟩ := Term.evalTermWord_eq_some_iff.mp (Term.evalTermWord_encTerm 1 [] t)
  let f := Fin.castLE (Nat.le_max_left n word.length)
  let g := Fin.castLE (Nat.le_max_right n word.length)
  have htu : t.rename f = u.rename g := (encTerm (max n word.length)).injective <| by
    rw [encTerm_rename f (fun _ => rfl), encTerm_rename g (fun _ => rfl), hu]
  have hzero : (∃ x, t.eval x = 0) ↔ ∃ x, u.eval x = 0 := by
    rw [← exists_eval_eq_zero_rename (Fin.castLE_injective (Nat.le_max_left n word.length)) t,
      htu, exists_eval_eq_zero_rename (Fin.castLE_injective (Nat.le_max_right n word.length)) u]
  refine ⟨fun ⟨v, hv, h⟩ => hzero.mpr ?_, fun h => ⟨u, hu, hzero.mp h⟩⟩
  rwa [← (encTerm word.length).injective (hv.trans hu.symm)]

open scoped Classical in
private noncomputable def equationPolynomial (word : List Bool) :
    MvPolynomial (Fin word.length) ℤ :=
  if h : ∃ t : Term word.length, encTerm word.length t = word then
    h.choose.toPolynomial
  else
    1

private theorem equationPolynomial_bounds (word : List Bool) :
    (equationPolynomial word).totalDegree ≤ word.length ∧
      (equationPolynomial word).coeffNorm1 ≤ 2 ^ word.length := by
  unfold equationPolynomial
  split
  · rename_i h
    simpa only [h.choose_spec] using h.choose.toPolynomial_bounds
  · simp [Nat.one_le_two_pow]

private noncomputable def equationControlled : Controlled equationPolynomial encBits 0 where
  arity_computable := length_bits
  degreeBound := List.length
  degree_computable := unary_to_binary.comp length_bits
  degree_le word := (equationPolynomial_bounds word).1
  massExponent := List.length
  mass_computable := unary_to_binary.comp length_bits
  mass_le word := (equationPolynomial_bounds word).2
  cutoff := fun _ => 0
  cutoff_computable := .const 0
  evaluate q := (Term.evalTermWord (max q.2.1 1) q.2.2 q.1).getD (1 % max q.2.1 1)
  evaluate_mem := by
    have hword := fst encBits (encPair encNat (encList encNat))
    have hdata := snd encBits (encPair encNat (encList encNat))
    have hpoint := (snd encNat (encList encNat)).comp hdata
    have hmod := binary_max' ((fst encNat (encList encNat)).comp hdata) (.const 1)
    exact CountingFunction.of_polyTime (optionGetDWithInput
      (Term.evalTermWord_polyTime hmod (fun _ => by positivity) hpoint hword)
      (binary_mod' (.const 1) hmod))
  evaluate_eq word p point hp _ := by
    rw [max_eq_left hp.one_lt.le]
    unfold equationPolynomial
    split
    · rename_i h
      have hvalue := Term.evalTermWord_encTerm p point h.choose
      rw [h.choose_spec] at hvalue
      rw [hvalue, Option.getD_some, Term.evalResidue_eq hp.pos, evaluation]
    · rename_i h
      have hnone : Term.evalTermWord p point word = none := by
        cases hresult : Term.evalTermWord p point word with
        | none => rfl
        | some r =>
          obtain ⟨t, ht, _⟩ := Term.evalTermWord_eq_some_iff.mp hresult
          exact (h ⟨t, ht⟩).elim
      rw [hnone, Option.getD_none, evaluation, MvPolynomial.eval₂_one]
      simpa only [Nat.cast_one] using (ZMod.val_natCast p 1).symm

/-- The encoded single-equation problem is in the twenty-sixth counting level. -/
theorem realSingleEquation_mem_countingLevel :
    RealSingleEquation ∈ CountingLevel 26 encBits := by
  have heq : RealSingleEquation =
      {word | ∃ x : Fin word.length → ℝ,
        MvPolynomial.eval x (equationPolynomial word |>.map (Int.castRingHom ℝ)) = 0} := by
    ext word
    simp only [RealSingleEquation, Set.mem_ofPred_eq, MvPolynomial.eval_map]
    unfold equationPolynomial
    split
    · rename_i h
      simp only [Term.eval_toPolynomial]
      refine ⟨fun ⟨t, ht, x, hx⟩ => ⟨x, ?_⟩, fun ⟨x, hx⟩ => ⟨h.choose, h.choose_spec, x, hx⟩⟩
      rwa [(encTerm word.length).injective (ht.trans h.choose_spec.symm)] at hx
    · rename_i h
      simp only [MvPolynomial.eval₂_one, one_ne_zero, exists_const, iff_false]
      exact fun ⟨t, ht, _⟩ => h ⟨t, ht⟩
  rw [heq]
  exact equationControlled.feasibility_mem Decoder.bits

end Cslib.Complexity
