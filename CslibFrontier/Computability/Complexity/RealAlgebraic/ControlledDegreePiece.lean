/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
public import CslibFrontier.Foundations.Data.MvPolynomial.DegreePiecePolynomial
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledBoundedSum
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledCoordinateLift
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledFirstCoefficient
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.MvPolynomial.FirstVariable

/-!
# Controlled degree-piece polynomials

The inverse equation and the guarded sum of higher coefficient squares operate on the
same controlled family. Coefficient extraction costs one counting level and the bounded
sum costs one more. The inverse coordinate is prepended to the original parameter point.

Adapted from `ControlledLiftedCoefficient` and `ControlledDegreePiece` in lean-canny
at `970f28a5ecefc1327402ade16c068aa4b1b2c183`. The common budgets adapt
`ControlledBoundedDegreePiece` at the same revision.
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + 1)) ℤ}

private noncomputable def liftedFirstCoefficient (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (k : α → ℕ)
    (hk : ComputableInPolyTime k enc encNat) :
    Controlled (fun w => MvPolynomial.rename Fin.succ ((finSuccEquiv ℤ (n w) (P w)).coeff (k w)))
      enc (a + 1) :=
  (C.firstVariableCoefficient E hn k hk).rename (unary_add' hn (.const 1))
    (fun _ => Fin.succ) (fun (_, z) => z.drop 1)
    (listDropWithInput (snd enc (encList encNat)) (.const 1))
    (fun _ z i => by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Fin.val_succ, Nat.add_comm])

private theorem cutoff_liftedFirstCoefficient (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (k : α → ℕ)
    (hk : ComputableInPolyTime k enc encNat) (w : α) :
    (liftedFirstCoefficient C E hn k hk).cutoff w =
      max (C.cutoff w) (max (C.degreeBound w) (k w)) + 1 := by
  simp only [liftedFirstCoefficient, cutoff_rename, cutoff_firstVariableCoefficient]

private noncomputable def degreePieceWithCutoff (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (N k : α → ℕ)
    (hN : ComputableInPolyTime N enc encNat) (hk : ComputableInPolyTime k enc encNat) :
    {L : Controlled (fun w => degreePiecePolynomial (P w) (N w) (k w)) enc (a + 2) //
      ∀ w, L.cutoff w ≤ max (C.cutoff w) (max (C.degreeBound w) (max (N w) (k w))) + 1} := by
  let A (w : α) (j : ℕ) :=
    MvPolynomial.rename Fin.succ ((finSuccEquiv ℤ (n w) (P w)).coeff j)
  let term (w : α) (j : ℕ) := if decide (k w < j) then A w j else MvPolynomial.C 0
  have hArity := unary_add' hn (.const 1)
  have hw := fst enc encNat
  have hj := snd enc encNat
  let indexed := liftedFirstCoefficient (C.preprocess Prod.fst hw) (Decoder.pair E Decoder.nat)
    (hn.comp hw) Prod.snd hj
  let zero := Controlled.constant (a := a + 1) (hArity.comp hw) (fun _ => (0 : ℤ)) (.const 0)
  let guarded : Controlled (fun q : α × ℕ => term q.1 q.2) (encPair enc encNat) (a + 1) :=
    indexed.ite zero (fun (w, j) => decide (k w < j)) (binary_lt' (hk.comp hw) hj)
  let U (w : α) := max (C.cutoff w) (max (C.degreeBound w) (N w)) + 1
  have hU : ComputableInPolyTime U enc encNat :=
    binary_add' (binary_max' C.cutoff_computable (binary_max' C.degree_computable hN)) (.const 1)
  have hdegree (w : α) (j : ℕ) : (term w j).totalDegree ≤ C.degreeBound w := by
    unfold term
    split
    · exact (totalDegree_rename_le _ _).trans
        ((totalDegree_coeff_finSuccEquiv_le _ _).trans (C.degree_le w))
    · simp only [totalDegree_C, Nat.zero_le]
  have hmass (w : α) (j : ℕ) : (term w j).coeffNorm1 ≤ 2 ^ C.massExponent w := by
    unfold term
    split
    · exact (coeffNorm1_rename_le _ _).trans
        ((coeffNorm1_coeff_finSuccEquiv_le _ _).trans (C.mass_le w))
    · simp only [coeffNorm1_C, Int.natAbs_zero, Nat.zero_le]
  have hcut (w : α) (j : ℕ) (hjN : j < N w + 1) : guarded.cutoff (w, j) ≤ U w := by
    simp only [guarded, cutoff_ite, indexed, cutoff_liftedFirstCoefficient,
      preprocess, zero, constant, U, max_eq_left (Nat.zero_le _)]
    exact Nat.add_le_add_right (max_le_max le_rfl
      (max_le_max le_rfl (Nat.lt_succ_iff.mp hjN))) 1
  let squares := guarded.sumSquares E hArity (fun w => N w + 1)
    C.degreeBound C.massExponent U (binary_add' hN (.const 1))
    C.degree_computable C.mass_computable hU
    (fun w j _ => hdegree w j) (fun w j _ => hmass w j) hcut
  let selected := liftedFirstCoefficient C E hn k hk
  let X₀ := Controlled.coordinate (a := a + 1) hArity (fun _ => 0) (.const 0)
  let minusOne := Controlled.constant (a := a + 1) hArity (fun _ => (-1 : ℤ)) (.const (-1))
  let base := ((selected.mul X₀).add minusOne).pow (fun _ => 2) (.const 2)
  let combined := (base.mono (by omega : a + 1 ≤ a + 2)).add squares
  have hshape : (fun w => degreePiecePolynomial (P w) (N w) (k w)) =
      fun w => (A w (k w) * X 0 + MvPolynomial.C (-1)) ^ 2 +
        ∑ j ∈ Finset.range (N w + 1), (term w j) ^ 2 := by
    funext w
    rw [degreePiecePolynomial_eq_sum_range]
    simp only [A, term, decide_eq_true_eq, sub_eq_add_neg, map_neg, map_one, MvPolynomial.C_0]
  rw [hshape]
  refine ⟨combined, fun w => ?_⟩
  simp only [combined, add, mono, base, pow, mul, X₀, minusOne, constant, coordinate,
    selected, cutoff_liftedFirstCoefficient, squares, cutoff_sumSquares, U, Nat.max_zero]
  exact max_le
    (Nat.add_le_add_right (max_le_max le_rfl (max_le_max le_rfl (le_max_right _ _))) 1)
    (Nat.add_le_add_right (max_le_max le_rfl (max_le_max le_rfl (le_max_left _ _))) 1)

/-- The degree-piece lift is controlled at two additional counting levels.
The inverse equation uses coefficient `k` and the sum uses the higher coefficients
through the binary bound `N`. Both addresses and bounds are computed in binary. -/
noncomputable def degreePiece (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (N k : α → ℕ)
    (hN : ComputableInPolyTime N enc encNat) (hk : ComputableInPolyTime k enc encNat) :
    Controlled (fun w => degreePiecePolynomial (P w) (N w) (k w)) enc (a + 2) :=
  (degreePieceWithCutoff C E hn N k hN hk).val

/-- A degree choice bounded by the source degree bound uses common degree, coefficient
norm and prime budgets, independently of the choice. The evaluator is the degree-piece evaluator. -/
noncomputable def boundedDegreePiece (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (k : α → ℕ)
    (hk : ComputableInPolyTime k enc encNat) (hchoice : ∀ w, k w ≤ C.degreeBound w) :
    Controlled (fun w => degreePiecePolynomial (P w) (C.degreeBound w) (k w)) enc (a + 2) :=
  let L := degreePieceWithCutoff C E hn C.degreeBound k C.degree_computable hk
  { arity_computable := unary_add' hn (.const 1)
    degreeBound := fun w => 2 * (C.degreeBound w + 1)
    degree_computable := binary_mul' (.const 2) (binary_add' C.degree_computable (.const 1))
    degree_le := fun w => (totalDegree_degreePiecePolynomial_le _ _ _).trans
      (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (C.degree_le w) 1))
    massExponent := fun w => degreePieceMassExponent (C.degreeBound w) (C.massExponent w)
    mass_computable := by
      unfold degreePieceMassExponent
      exact binary_add' (unary_to_binary.comp (binary_size.comp
        (binary_add' C.degree_computable (.const 2))))
        (binary_mul' (.const 2) (binary_add' C.mass_computable (.const 1)))
    mass_le := fun w => coeffNorm1_degreePiecePolynomial_le _ _ _ _ (C.mass_le w)
    cutoff := fun w => max (C.cutoff w) (C.degreeBound w) + 1
    cutoff_computable :=
      binary_add' (binary_max' C.cutoff_computable C.degree_computable) (.const 1)
    evaluate := L.val.evaluate
    evaluate_mem := L.val.evaluate_mem
    evaluate_eq := fun w p z hp hcut => by
      have h := L.property w
      rw [max_eq_left (hchoice w), max_self] at h
      exact L.val.evaluate_eq w p z hp (h.trans_lt hcut) }

section BoundedDegreePiece

variable (C : Controlled P enc a) (E : Decoder enc)
  (hn : ComputableInPolyTime n enc encUnary) (k : α → ℕ)
  (hk : ComputableInPolyTime k enc encNat) (hchoice : ∀ w, k w ≤ C.degreeBound w)

/-- All bounded degree pieces have the same degree bound. -/
@[simp] theorem degreeBound_boundedDegreePiece (w : α) :
    (C.boundedDegreePiece E hn k hk hchoice).degreeBound w = 2 * (C.degreeBound w + 1) := by
  simp only [boundedDegreePiece]

/-- All bounded degree pieces have the same coefficient norm exponent. -/
@[simp] theorem massExponent_boundedDegreePiece (w : α) :
    (C.boundedDegreePiece E hn k hk hchoice).massExponent w =
      degreePieceMassExponent (C.degreeBound w) (C.massExponent w) := by
  simp only [boundedDegreePiece]

/-- All bounded degree pieces have the same prime cutoff. -/
@[simp] theorem cutoff_boundedDegreePiece (w : α) :
    (C.boundedDegreePiece E hn k hk hchoice).cutoff w = max (C.cutoff w) (C.degreeBound w) + 1 := by
  simp only [boundedDegreePiece]

end BoundedDegreePiece

end Cslib.Complexity.RealAlgebraic.Controlled
