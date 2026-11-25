/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.WordCoordinateFingerprintLabels
public import CslibFrontier.Foundations.Analysis.MvPolynomial.CoordinateCriticalLimit

/-!
# Indexed constraints for coordinate selection

Row zero tests the source polynomial. The next rows test membership in the coordinate
root grid. The strict inequalities are the coordinate fingerprint labels from the shared
witness word. These constraints express the selection conditions without a counting-level
increase for the individual row queries.

Adapted from lean-canny's `SelectionSystem` and `SelectionSystemCorrectness` at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem

/-- The source equation at row zero followed by the coordinate root equations.
Positive addresses read the preceding coordinate address. -/
noncomputable def selectionEquation {n d : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hn : 0 < n) (j : ℕ) : MvPolynomial (Fin n) ℤ :=
  if decide (j = 0) then F else indexedCoordinateEquation F hF hn (j - 1)

/-- Row zero is the source polynomial. -/
@[simp] theorem selectionEquation_zero {n d : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hn : 0 < n) : selectionEquation F hF hn 0 = F := by
  simp [selectionEquation]

/-- Evaluate the source or a coordinate equation selected by a binary row address at
counting level `a + 18`. All rows share polynomial-time bounds independent of the row address. -/
noncomputable def Controlled.selectionEquations {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat) :
    Controlled (fun q : α × ℕ => selectionEquation (F q.1) (hF q.1) (hn q.1) q.2)
      (encPair enc encNat) (a + 18) := by
  have hw := fst enc encNat
  have hj := snd enc encNat
  let CI := (C.indexedCoordinateEquations E hn hdpos hF hd).preprocess
    (fun q : α × ℕ => (q.1, q.2 - 1)) (hw.prod (binary_sub' hj (.const 1)))
  let C₀ := (C.preprocess (fun q : α × ℕ => q.1) hw).mono (Nat.le_add_right a 18)
  have hguard : ComputableInPolyTime (fun q : α × ℕ => decide (q.2 = 0))
      (encPair enc encNat) encBool := by
    simpa only [Nat.le_zero_eq] using binary_le' hj (.const 0)
  exact C₀.ite CI (fun q => decide (q.2 = 0)) hguard

/-- The selection equations share the degree bound, norm exponent and prime cutoff at row zero.
These instance bounds apply to every binary row address. -/
theorem Controlled.selectionEquations_bounds_eq {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (w : α) (j : ℕ) :
    let equations := C.selectionEquations E hn hdpos hF hd
    equations.degreeBound (w, j) = equations.degreeBound (w, 0) ∧
      equations.massExponent (w, j) = equations.massExponent (w, 0) ∧
      equations.cutoff (w, j) = equations.cutoff (w, 0) := by
  obtain ⟨hD, hb, hc⟩ := C.indexedCoordinateEquations_bounds_eq E hn hdpos hF hd w (j - 1)
  simp only [selectionEquations, degreeBound_ite, massExponent_ite, cutoff_ite, mono, preprocess,
    Function.comp_apply, Nat.zero_sub, hD, hb, hc, eq_self, and_self]

/-- The indexed rows express that the point is a source zero in the coordinate root grid
and that every coordinate satisfies the fingerprint label from the shared word. -/
theorem selection_constraints_iff {n d : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (mass : ℕ) (hn : 0 < n) (word : List Bool) (x : Fin n → ℝ) :
    ((∀ j < n + 1, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (selectionEquation F hF hn j) = 0) ∧
      ∀ j < n, 0 < MvPolynomial.eval₂ (Int.castRingHom ℝ) x
        (wordCoordinateFingerprintTest F hF mass hn word j)) ↔
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x F = 0 ∧
        x ∈ coordinateRootGrid (Nat.succ_pos d) F hF ∧
        ∀ i : Fin n, 0 < (wordCoordinateFingerprintLabel F hF mass hn word i.val).eval₂
          (Int.castRingHom ℝ) (x i) := by
  have hrow (i : Fin n) :
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x (selectionEquation F hF hn (i.val + 1)) =
        (Polynomial.Bivariate.swap
          (parametricCoordinatePolynomial (Nat.succ_pos d) F hF i)).leadingCoeff.eval₂
          (Int.castRingHom ℝ) (x i) := by
    simpa only [selectionEquation, decide_eq_true_eq, Nat.succ_ne_zero, ite_false,
      Nat.add_sub_cancel, Nat.mod_eq_of_lt i.isLt] using
      eval₂_indexedCoordinateEquation (Int.castRingHom ℝ) F hF hn x i.val
  have hlabel (i : Fin n) :
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x
        (wordCoordinateFingerprintTest F hF mass hn word i.val) =
        (wordCoordinateFingerprintLabel F hF mass hn word i.val).eval₂
          (Int.castRingHom ℝ) (x i) := by
    simpa only [Nat.mod_eq_of_lt i.isLt] using
      eval₂_wordCoordinateFingerprintTest (Int.castRingHom ℝ) F hF mass hn word x i.val
  simp only [mem_coordinateRootGrid, Polynomial.IsRoot.def, Polynomial.eval_map]
  constructor
  · rintro ⟨heq, hpos⟩
    refine ⟨?_, fun i => ?_, fun i => ?_⟩
    · simpa only [selectionEquation_zero] using heq 0 (Nat.zero_lt_succ n)
    · exact (hrow i).symm.trans (heq (i.val + 1) (Nat.succ_lt_succ i.isLt))
    · simpa only [hlabel i] using hpos i.val i.isLt
  · rintro ⟨hzero, hgrid, hpos⟩
    constructor
    · intro j hj
      cases j with
      | zero => simpa only [selectionEquation_zero] using hzero
      | succ j =>
        let i : Fin n := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
        exact (hrow i).trans (hgrid i)
    · intro j hj
      rw [hlabel (⟨j, hj⟩ : Fin n)]
      exact hpos ⟨j, hj⟩

end Cslib.Complexity.RealAlgebraic
