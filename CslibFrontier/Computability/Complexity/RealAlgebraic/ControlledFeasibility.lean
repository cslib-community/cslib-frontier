/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Aggregation
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalFeasibilityWitness
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalLabelDeterminantSign
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Real zeros of controlled polynomial families

Squaring preserves real zeros and the counting level of modular evaluation. For the square,
the determinant sign decides a fixed-width feasibility witness at level `F_(a+24)`.
Existential quantification over those bits gives a Boolean decision one level higher.

Adapted from `ControlledFeasibilityWitnesses`, `ControlledFeasibilityFunction`, and
`ControlledFeasibility` in lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`, using
the frontier's framed witness and critical determinant. The input is the encoded index of
a controlled family. Its polynomial is a specification accessed through its modular evaluator.

## Main results

* `Controlled.feasibilityFunction_mem`: the real-zero Boolean decision at level `F_(a+25)`.
* `Controlled.feasibility_mem`: the real-zero language at level `C_(a+26)P`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open MvPolynomial

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}

private theorem feasibilityWitnessTest_mem (C : Controlled P enc a) (E : Decoder enc)
    {d : α → ℕ} (hdpos : ∀ w, 1 ≤ d w) (hdegree : ∀ w, (P w).totalDegree ≤ d w + 1)
    (hd : ComputableInPolyTime d enc encNat) :
    (fun (w, word) => decide
      (criticalFeasibilityDeterminant (ell := d w + 1) (by omega) (C.massExponent w) (P w)
        (hdegree w) word < 0)) ∈ CountingFunction (a + 24) (encPair enc encBits) encBool := by
  have hf := fst enc encBits
  have hdecode := decodeCriticalFeasibilityWitness_polyTime.comp (snd enc encBits)
  let C' := C.preprocess Prod.fst hf
  have hsign := C'.criticalLabelDeterminantSign_mem (Decoder.pair E Decoder.bits)
    (fun (w, _) => hdpos w) (fun (w, _) => hdegree w) (hd.comp hf)
    (encCriticalFeasibilityWitness_shift_polyTime hdecode)
    (encCriticalFeasibilityWitness_label_polyTime hdecode)
  have htest := CountingFunction.map hsign (g := fun z : ℤ => decide (z < 0)) (by fun_prop)
  convert htest using 1
  funext q
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, C', preprocess, Function.comp_apply,
    criticalFeasibilityDeterminant, Int.sign_neg_iff]
  exact decide_eq_true_iff

open Classical in
/-- A controlled polynomial family at level `F_a` admits a Boolean real-zero test at
level `F_(a+25)`, using the unary arity and binary bounds supplied by the family. -/
theorem feasibilityFunction_mem (C : Controlled P enc a) (E : Decoder enc) :
    (fun w => decide (∃ x : Fin (n w) → ℝ, eval x ((P w).map (Int.castRingHom ℝ)) = 0)) ∈
      CountingFunction (a + 25) enc encBool := by
  let Q := C.mul C
  let d (w : α) := 2 * (Q.degreeBound w + 1)
  let ell (w : α) := d w + 1
  have hdpos (w : α) : 1 ≤ d w := by dsimp only [d]; omega
  have hdegree (w : α) : (P w * P w).totalDegree ≤ ell w :=
    (Q.degree_le w).trans (by dsimp only [ell, d]; omega)
  have heven (w : α) : Even (ell w + 1) := by
    refine ⟨Q.degreeBound w + 2, ?_⟩
    dsimp only [ell, d]
    omega
  have hd : ComputableInPolyTime d enc encNat :=
    binary_mul' (.const 2) (binary_add' Q.degree_computable (.const 1))
  have hell := binary_add' hd (.const 1)
  have hw := criticalFeasibilityWitnessWidth_polyTime
    (binary_pow' (hbase := hell) (hexponent := Q.arity_computable))
    (unary_mul' Q.arity_computable (binary_size.comp hell))
  have htest := CountingFunction.exists_bits E (Q.feasibilityWitnessTest_mem E hdpos hdegree hd) hw
  have hcorrect (w : α) :
      (∃ word : List Bool, word.length = criticalFeasibilityWitnessWidth (ell w ^ n w)
        (n w * (ell w).size) ∧ criticalFeasibilityDeterminant (ell := ell w) (by dsimp [ell]; omega)
          (Q.massExponent w) (P w * P w) (hdegree w) word < 0) ↔
        (∃ x : Fin (n w) → ℝ, eval x ((P w).map (Int.castRingHom ℝ)) = 0) := by
    have hnonneg (x : Fin (n w) → ℝ) :
        0 ≤ eval x ((P w * P w).map (Int.castRingHom ℝ)) := by
      simpa only [map_mul] using mul_self_nonneg (eval x ((P w).map (Int.castRingHom ℝ)))
    rw [← exists_zero_iff_neg_criticalFeasibilityDeterminant (Nat.succ_le_succ (hdpos w))
      (heven w) (P w * P w) (hdegree w) (Q.mass_le w) hnonneg]
    simp only [map_mul, mul_self_eq_zero]
  convert htest using 1
  funext w
  simp only [decide_eq_true_eq, Function.comp_apply]
  exact congrArg (fun p : Prop => decide p) (propext (hcorrect w).symm)

/-- The real-zero language of an `F_a` controlled polynomial family is in
`C_(a+26)P`. -/
theorem feasibility_mem (C : Controlled P enc a) (E : Decoder enc) :
    {w | ∃ x : Fin (n w) → ℝ, eval x ((P w).map (Int.castRingHom ℝ)) = 0} ∈
      CountingLevel (a + 26) enc := by
  simpa only [decide_eq_true_eq, Nat.add_assoc] using
    CountingFunction.decision (C.feasibilityFunction_mem E)

end Cslib.Complexity.RealAlgebraic.Controlled
