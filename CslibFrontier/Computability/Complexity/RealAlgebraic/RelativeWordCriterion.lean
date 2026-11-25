/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledDegreePiece
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CoordinateSelection
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.RelativeValueSection
import CslibFrontier.Foundations.Analysis.MvPolynomial.RelativeCandidateCoverage

/-!
# Two feasibility tests for an empty real fiber

An empty real zero fiber can be witnessed by a fixed-width word. Its prefix selects
a degree piece of the relative section, and its suffix selects a point in the
coordinate root grid of the squared lift. The selection polynomial has a zero,
and the counterexample polynomial has none for the same word.

Adapted from `RelativeTwoTestCriterion` and `RelativeWordCriterion` in lean-canny
at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open MvPolynomial MvPolynomial.CriticalSystem

/-- A nonnegative relative polynomial has an empty real zero fiber exactly when a
degree-and-coordinate witness word makes the selection system feasible and the
counterexample system infeasible. The width depends only on the section degree bound
`N` and the parameter arity `m`. -/
theorem exists_emptyFiber_iff_selectionWord {n m ell : ℕ} (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (P : MvPolynomial (Fin (n + m)) ℤ) (hP : P.totalDegree ≤ ell)
    (hpos : ∀ x z, 0 ≤ eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) P)
    (N b : ℕ) (hN : (finiteRelativeValueSection hell P hP).totalDegree ≤ N)
    (hb : (finiteRelativeValueSection hell P hP).coeffNorm1 ≤ 2 ^ b) :
    let E := finiteRelativeValueSection hell P hP
    let D := 2 * (N + 1)
    let d := 2 * (D + 1)
    let mass := degreePieceMassExponent N b * 2
    let W (k : ℕ) := degreePiecePolynomial E N k
    let F (k : ℕ) := W k ^ 2
    let hW (k : ℕ) : (W k).totalDegree ≤ D :=
      (totalDegree_degreePiecePolynomial_le E N k).trans
        (Nat.mul_le_mul_left 2 (Nat.succ_le_succ hN))
    let hF (k : ℕ) : (F k).totalDegree ≤ d + 1 :=
      (totalDegree_pow (W k) 2).trans (by have := hW k; dsimp only [d]; omega)
    (∃ x : Fin m → ℝ, ∀ z : Fin n → ℝ,
      eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) P ≠ 0) ↔
    ∃ word : List Bool,
      word.length = N.size + coordinateFingerprintWitnessWidth ((d + 1) ^ (m + 1)) (m + 1) ∧
      let k := (Controlled.decodeDegreeChoice N word).val
      let suffix := word.drop N.size
      (∃ y : Fin ((m + 1) + (m + 1)) → ℝ, eval₂ (Int.castRingHom ℝ) y
        (selectionFeasibilityPolynomial (F k) (hF k) mass (Nat.succ_pos m) suffix) = 0) ∧
      ¬∃ y : Fin (((m + 1) + n) + (m + 1)) → ℝ, eval₂ (Int.castRingHom ℝ) y
        (selectionCounterexamplePolynomial (F k) (counterexamplePolynomial P) (hF k)
          mass (Nat.succ_pos m) suffix) = 0 := by
  intro E D d mass W F hW hF
  have hd : 1 ≤ d := by dsimp only [d]; omega
  have hmass (k : ℕ) : (F k).coeffNorm1 ≤ 2 ^ mass := by
    change ((W k) ^ 2).coeffNorm1 ≤ 2 ^ (degreePieceMassExponent N b * 2)
    rw [pow_mul]
    exact (coeffNorm1_pow_le _ _).trans
      (Nat.pow_le_pow_left (coeffNorm1_degreePiecePolynomial_le E N k b hb) 2)
  simp only [exists_selectionFeasibilityPolynomial_zero_iff,
    exists_selectionCounterexamplePolynomial_zero_iff, eval₂_counterexamplePolynomial]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨j, hj, y, hy, hyempty, hygrid⟩ :=
      exists_degreePiece_coordinateRootGrid_of_emptyFiber hell he P hP hpos N hN D hW
        ⟨x, fun ⟨z, hz⟩ => hx z hz⟩
    have hyzero : eval₂ (Int.castRingHom ℝ) y (F j) = 0 := by
      change eval₂ (Int.castRingHom ℝ) y (W j ^ 2) = 0
      rw [eval₂_pow, ← eval_map, hy, zero_pow (by decide)]
    obtain ⟨suffix, hlen, hselect⟩ :=
      exists_coordinateSelectionWitness (F j) (hF j) (hmass j) hd (Nat.succ_pos m) hygrid
    let k : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    obtain ⟨word, hword, hdegree, hdrop⟩ := Controlled.exists_degreeChoiceWord k suffix
    refine ⟨word, hword.trans (congrArg (N.size + ·) hlen), ?_⟩
    rw [hdegree, hdrop]
    obtain ⟨hgrid, hlabels⟩ := (hselect y).mpr rfl
    refine ⟨⟨y, hyzero, hgrid, hlabels⟩, ?_⟩
    rintro ⟨v, z, _, hvgrid, hvlabels, hz⟩
    have hv := (hselect v).mp ⟨hvgrid, hvlabels⟩
    subst v
    exact hyempty ⟨z, hz⟩
  · rintro ⟨word, _, ⟨y, hy, hgrid, hlabels⟩, hno⟩
    exact ⟨Fin.tail y, fun z hz => hno ⟨y, z, hy, hgrid, hlabels, hz⟩⟩

end Cslib.Complexity.RealAlgebraic
