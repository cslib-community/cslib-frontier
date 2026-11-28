/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledRelativeCoefficient
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalParameterEvaluation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValueCoeffNorm
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValueParameterDegree

/-!
# Controlled relative critical-value families

`Controlled.relativeValueFamilyOfDegree` packages the finite relative polynomial and its
evaluator at counting level `a + 10`, with degree, norm, and prime cutoff bounds computed from
the source. `Controlled.relativeValueFamily` chooses an even degree parameter from the source
degree bound, so the deformed potential has an even highest power in the witness variables.

Adapted from `ControlledRelativeCharacteristic` and `NativeRelativeBounds` in lean-canny
at `970f28a5ecefc1327402ade16c068aa4b1b2c183`. The two-block decision theorem remains open
under [#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem

variable {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}

/-- Build the actual relative critical-value family from a controlled source and a supplied
binary degree parameter. Both variable counts are unary. The prime cutoff is the maximum of
the source cutoff, the trace grid cutoff, and one more than the squared quotient dimension. -/
noncomputable def relativeValueFamilyOfDegree (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    (d : α → ℕ) (hd : ComputableInPolyTime d enc encNat)
    (hpos : ∀ w, 1 ≤ d w) (hdeg : ∀ w, (P w).totalDegree ≤ d w + 1) :
    Controlled (fun w => finiteRelativeValuePolynomial (by omega : 1 ≤ d w + 1)
      (P w) (hdeg w)) enc (a + 10) := by
  let ell (w : α) := d w + 1
  let dim (w : α) := ell w ^ n w
  let gridCutoff (w : α) := ell w * (dim w * (ell w + 1) + n w * d w + 1) + 1
  let sizeCutoff (w : α) := dim w * dim w + 1
  have hEll : ∀ w, 2 ≤ ell w := fun w => Nat.succ_le_succ (hpos w)
  have hnBinary := unary_to_binary.comp hn
  have hell := binary_add' hd (.const 1)
  have hellNext := binary_add' hell (.const 1)
  have hdim := binary_pow' hell hn
  refine {
    arity_computable := unary_add' hm (.const 2)
    degreeBound := fun w => dim w * ((ell w + 2 + n w * ell w) * (ell w + 1))
    degree_computable := binary_mul' hdim (binary_mul'
      (binary_add' (binary_add' hell (.const 2)) (binary_mul' hnBinary hell)) hellNext)
    degree_le := ?_
    massExponent := fun w => relativeValueCoeffNormExponent (n w) (ell w) (C.massExponent w)
    mass_computable := ?_
    mass_le := ?_
    cutoff := fun w => max (C.cutoff w) (max (gridCutoff w) (sizeCutoff w))
    cutoff_computable := ?_
    evaluate := C.relativeValue d
    evaluate_mem := C.relativeValue_mem E hn hd
    evaluate_eq := ?_ }
  · intro w
    let F := rename finSumFinEquiv.symm (P w)
    have hF : F.totalDegree ≤ ell w := (totalDegree_rename_le _ _).trans (hdeg w)
    unfold finiteRelativeValuePolynomial
    refine (totalDegree_rename_le _ _).trans
      ((totalDegree_flattenedRelativeValuePolynomial_le (hEll w) F hF).trans ?_)
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hF 1))
  · have hpotential := unary_to_binary.comp
      (binary_size.comp (binary_add' hnBinary hellNext))
    have hrelations := unary_to_binary.comp (binary_size.comp hell)
    exact multiplicationMatrixCharpolyCoeffNormExponent_polyTime hn hell hellNext
      (binary_add' hpotential C.mass_computable) (binary_add' hrelations C.mass_computable)
  · intro w
    let F := rename finSumFinEquiv.symm (P w)
    have hF : F.totalDegree ≤ ell w := (totalDegree_rename_le _ _).trans (hdeg w)
    unfold finiteRelativeValuePolynomial
    exact (coeffNorm1_rename_le _ _).trans
      (coeffNorm1_flattenedRelativeValuePolynomial_le (hEll w) F hF
        ((coeffNorm1_rename_le _ _).trans (C.mass_le w)))
  · have hnum := binary_add' (binary_mul' hdim hellNext) (binary_mul' hnBinary hd)
    have hgrid := binary_add' (binary_mul' hell (binary_add' hnum (.const 1))) (.const 1)
    have hsize := binary_add' (binary_mul' hdim hdim) (.const 1)
    exact binary_max' C.cutoff_computable (binary_max' hgrid hsize)
  · intro w p z hp hcut
    have hsource := (le_max_left (C.cutoff w) _).trans_lt hcut
    have htrace := (le_max_right (C.cutoff w) _).trans_lt hcut
    have hgrid := (le_max_left (gridCutoff w) (sizeCutoff w)).trans_lt htrace
    have hsize := (le_max_right (gridCutoff w) (sizeCutoff w)).trans_lt htrace
    have hdim' : (d w + 1) ^ n w * (d w + 1) ^ n w < p - 1 := by
      dsimp only [sizeCutoff, dim, ell] at hsize
      omega
    rw [evaluation, eval₂_finiteRelativeValuePolynomial]
    exact C.relativeValue_eq d w p z hp hsource (hpos w) (hdeg w) hgrid hdim'

/-- Choose an even degree parameter from the source degree bound. This makes the leading
witness power even for the later coercive deformation. -/
noncomputable def relativeValueFamily (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary) :
    Controlled (fun w => finiteRelativeValuePolynomial
      (by omega : 1 ≤ 2 * (C.degreeBound w + 1) + 1) (P w)
      ((C.degree_le w).trans (by omega))) enc (a + 10) :=
  C.relativeValueFamilyOfDegree E hn hm (fun w => 2 * (C.degreeBound w + 1))
    (binary_mul' (.const 2) (binary_add' C.degree_computable (.const 1)))
    (fun _ => by omega) (fun w => (C.degree_le w).trans (by omega))

end Cslib.Complexity.RealAlgebraic.Controlled
