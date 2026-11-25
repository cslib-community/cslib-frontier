/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
public import Mathlib.Algebra.MvPolynomial.Equiv
import CslibFrontier.Computability.Complexity.RealAlgebraic.CoefficientEvaluation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.MvPolynomial.FirstVariable

/-!
# Controlled first-variable coefficients

Extracting a binary-indexed coefficient in the first variable leaves a controlled family
in the remaining variables. Its evaluator uses one additional counting level, and the
original degree and coefficient norm bounds still apply.

Adapted from `ControlledFirstCoefficient` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM MvPolynomial ComputableInPolyTime

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + 1)) ℤ}

private theorem coefficientSample_polyTime (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun q : (α × (ℕ × List ℕ)) × ℕ =>
      (q.1.1, q.1.2.1, q.2 :: q.1.2.2))
      (encPair (encEvaluation enc) encNat) (encEvaluation enc) := by
  have hq := fst (encEvaluation enc) encNat
  have ht := snd (encEvaluation enc) encNat
  exact hq.fst'.prod (hq.snd'.fst'.prod (ht.cons' hq.snd'.snd'))

private theorem firstVariableCoefficient_mem (C : Controlled P enc a) (E : Decoder enc)
    (k : α → ℕ) (hk : ComputableInPolyTime k enc encNat) :
    (fun q : α × (ℕ × List ℕ) => coefficientResidue q.2.1 (k q.1)
      (fun t => C.evaluate (q.1, q.2.1, t :: q.2.2))) ∈
      CountingFunction (a + 1) (encEvaluation enc) encNat := by
  have hw := fst enc (encPair encNat (encList encNat))
  have hp := (snd enc (encPair encNat (encList encNat))).fst'
  have hvalue := CountingFunction.preprocess C.evaluate_mem (coefficientSample_polyTime enc)
  exact coefficientResidue_mem (enc := encEvaluation enc) (a := a)
    (p := fun q => q.2.1) (k := fun q => k q.1)
    (value := fun q => C.evaluate (q.1.1, q.1.2.1, q.2 :: q.1.2.2))
    (Decoder.pair E (Decoder.pair Decoder.nat (Decoder.list Decoder.nat)))
    hp (hk.comp hw) hvalue

/-- Extract the coefficient in coordinate zero, retaining the other coordinates.
The binary prime cutoff exceeds the source cutoff, degree bound, and queried index. -/
noncomputable def firstVariableCoefficient (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (k : α → ℕ)
    (hk : ComputableInPolyTime k enc encNat) :
    Controlled (fun w => (finSuccEquiv ℤ (n w) (P w)).coeff (k w)) enc (a + 1) where
  arity_computable := hn
  degreeBound := C.degreeBound
  degree_computable := C.degree_computable
  degree_le w := (totalDegree_coeff_finSuccEquiv_le (P w) (k w)).trans (C.degree_le w)
  massExponent := C.massExponent
  mass_computable := C.mass_computable
  mass_le w := (coeffNorm1_coeff_finSuccEquiv_le (P w) (k w)).trans (C.mass_le w)
  cutoff w := max (C.cutoff w) (max (C.degreeBound w) (k w)) + 1
  cutoff_computable := binary_add'
    (binary_max' C.cutoff_computable (binary_max' C.degree_computable hk)) (.const 1)
  evaluate := fun q => coefficientResidue q.2.1 (k q.1)
    (fun t => C.evaluate (q.1, q.2.1, t :: q.2.2))
  evaluate_mem := firstVariableCoefficient_mem C E k hk
  evaluate_eq w p z hp hcut := by
    let : Fact p.Prime := ⟨hp⟩
    let φ := Int.castRingHom (ZMod p)
    let x (i : Fin (n w)) : ZMod p := (z[i.val]?.getD 0 : ℕ)
    let Q := (finSuccEquiv ℤ (n w) (P w)).map (eval₂Hom φ x)
    have hC := Nat.le_max_left (C.cutoff w) (max (C.degreeBound w) (k w))
    have hD := (Nat.le_max_left (C.degreeBound w) (k w)).trans
      (Nat.le_max_right (C.cutoff w) (max (C.degreeBound w) (k w)))
    have hk₀ := (Nat.le_max_right (C.degreeBound w) (k w)).trans
      (Nat.le_max_right (C.cutoff w) (max (C.degreeBound w) (k w)))
    have hQdegree : Q.natDegree ≤ C.degreeBound w :=
      Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv _).le.trans
        ((degreeOf_le_totalDegree _ _).trans (C.degree_le w)))
    have hvalue (t : ℕ) (_ : t < p) :
        (C.evaluate (w, p, t :: z) : ZMod p) = Q.eval (t : ZMod p) := by
      have hcoords : (fun i : Fin (n w + 1) =>
          (((t :: z)[i.val]?.getD 0 : ℕ) : ZMod p)) = Fin.cons (t : ZMod p) x := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · simp only [x, Fin.val_succ, List.getElem?_cons_succ, Fin.cons_succ]
      rw [C.evaluate_eq w p _ hp (by omega), evaluation, ZMod.natCast_zmod_val, hcoords]
      dsimp only [Q]
      rw [Polynomial.eval_map, eval₂_finSuccEquiv]
    change coefficientResidue p (k w) (fun t => C.evaluate (w, p, t :: z)) = _
    rw [coefficientResidue_eq_val Q (k w) _ (by omega) (by omega) hvalue]
    simp only [Q, Polynomial.coeff_map, φ, coe_eval₂Hom, x, evaluation]

/-- The evaluator needs the source cutoff and enough field elements for coefficient recovery. -/
theorem cutoff_firstVariableCoefficient (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (k : α → ℕ)
    (hk : ComputableInPolyTime k enc encNat) (w : α) :
    (C.firstVariableCoefficient E hn k hk).cutoff w =
      max (C.cutoff w) (max (C.degreeBound w) (k w)) + 1 := by
  simp only [firstVariableCoefficient]

end Cslib.Complexity.RealAlgebraic.Controlled
