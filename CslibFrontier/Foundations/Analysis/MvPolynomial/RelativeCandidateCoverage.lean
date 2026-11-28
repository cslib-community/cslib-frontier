/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, coordinate candidates for real polynomial fibers)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.MvPolynomial.CoordinateCriticalLimit
public import CslibFrontier.Foundations.Data.MvPolynomial.DegreePiecePolynomial
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.RelativeValueSection
import CslibFrontier.Foundations.Analysis.MvPolynomial.RelativeFiberSeparation

/-!
# Coordinate candidates for empty real fibers

The inverse coordinate realizes a fixed-degree piece of the relative section as a polynomial
zero set. On that zero set, the points projecting to empty fibers form a clopen set. If
nonempty, it meets the coordinate root grid of the square of the lift polynomial.

Adapted from `DegreePieceProjection`, `RelativeDegreePieceGeometry`, and
`RelativeCandidateCoverage` in lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial.CriticalSystem

open Set

variable {n m ell : ℕ}

/-- If a nonnegative relative polynomial has an empty real zero fiber, some point of a
degree-piece lift projects to an empty fiber and lies in its finite coordinate root grid.
`N` bounds the total degree of the section and `D` bounds that of the lift polynomials. -/
theorem exists_degreePiece_coordinateRootGrid_of_emptyFiber (hell : 1 ≤ ell)
    (he : Even (ell + 1)) (P : MvPolynomial (Fin (n + m)) ℤ) (hP : P.totalDegree ≤ ell)
    (hpos : ∀ x z, 0 ≤ eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) P)
    (N : ℕ) (hN : (finiteRelativeValueSection hell P hP).totalDegree ≤ N)
    (D : ℕ) (hD : ∀ k,
      (degreePiecePolynomial (finiteRelativeValueSection hell P hP) N k).totalDegree ≤ D)
    (hempty : ∃ x, ¬∃ z : Fin n → ℝ, eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) P = 0) :
    ∃ k ≤ N,
      let W := degreePiecePolynomial (finiteRelativeValueSection hell P hP) N k
      ∃ y : Fin (m + 1) → ℝ, eval y (W.map (Int.castRingHom ℝ)) = 0 ∧
        (¬∃ z : Fin n → ℝ, eval₂ (Int.castRingHom ℝ) (Fin.addCases z (Fin.tail y)) P = 0) ∧
        y ∈ coordinateRootGrid (ell := 2 * (D + 1) + 1) (by omega) (W ^ 2)
          ((totalDegree_pow W 2).trans (by
            have h : W.totalDegree ≤ D := hD k
            omega)) := by
  obtain ⟨x, hx⟩ := hempty
  let E := finiteRelativeValueSection hell P hP
  let Q (r : Fin m → ℝ) := specializedRelativeValueSection hell P hP r
  have hdegree (r : Fin m → ℝ) : (Q r).natDegree ≤ N :=
    (natDegree_specializedRelativeValueSection_le hell P hP r).trans hN
  let k := (Q x).natDegree
  have hk : k ≤ N := hdegree x
  have hlead : (Q x).coeff k ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr
    (specializedRelativeValueSection_ne_zero hell P hP x)
  let W := degreePiecePolynomial E N k
  let F := W ^ 2
  have hWdegree : W.totalDegree ≤ D := hD k
  have hF : F.totalDegree ≤ 2 * (D + 1) + 1 :=
    (totalDegree_pow W 2).trans (by omega)
  have hzero (t : ℝ) (r : Fin m → ℝ) :
      eval₂ (Int.castRingHom ℝ) (Fin.cons t r) W = 0 ↔
        (Q r).coeff k * t = 1 ∧ ∀ j ∈ Finset.Ioc k N, (Q r).coeff j = 0 := by
    simpa only [Q, coeff_specializedRelativeValueSection_eq_eval₂] using
      eval₂_degreePiecePolynomial_eq_zero_iff E N k (Int.castRingHom ℝ) t r
  have heval (y : Fin (m + 1) → ℝ) :
      eval y (F.map (Int.castRingHom ℝ)) = (eval y (W.map (Int.castRingHom ℝ))) ^ 2 := by
    dsimp only [F]
    rw [map_pow, eval_pow]
  let Z := {y : Fin (m + 1) → ℝ // eval y (F.map (Int.castRingHom ℝ)) = 0}
  have hW (y : Z) : eval y.val (W.map (Int.castRingHom ℝ)) = 0 :=
    sq_eq_zero_iff.mp ((heval y.val).symm.trans y.property)
  let r (y : Z) := Fin.tail y.val
  have hpiece (y : Z) :
      (Q (r y)).coeff k * y.val 0 = 1 ∧ ∀ j ∈ Finset.Ioc k N, (Q (r y)).coeff j = 0 := by
    apply (hzero (y.val 0) (r y)).mp
    rw [show Fin.cons (y.val 0) (r y) = y.val from Fin.cons_self_tail _]
    rw [← eval_map]
    exact hW y
  let G : Set Z := {y | ¬∃ z : Fin n → ℝ,
    eval₂ (Int.castRingHom ℝ) (Fin.addCases z (r y)) P = 0}
  have hG : IsClopen G := by
    have hr : Continuous r :=
      continuous_pi fun i => (continuous_apply i.succ).comp continuous_subtypeVal
    refine isClopen_relative_emptyFibers_of_fixed_degree hell he P hP r hr
      (fun y z => hpos (r y) z) k ?_ (fun y => left_ne_zero_of_mul_eq_one (hpiece y).1)
    intro y
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
    by_cases hjN : j ≤ N
    · exact (hpiece y).2 j (Finset.mem_Ioc.mpr ⟨hj, hjN⟩)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((hdegree (r y)).trans_lt (lt_of_not_ge hjN))
  have hinverse : eval₂ (Int.castRingHom ℝ) (Fin.cons ((Q x).coeff k)⁻¹ x) W = 0 :=
    (hzero _ _).mpr ⟨mul_inv_cancel₀ hlead, fun j hj =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (Finset.mem_Ioc.mp hj).1⟩
  have hstart : eval (Fin.cons ((Q x).coeff k)⁻¹ x) (F.map (Int.castRingHom ℝ)) = 0 := by
    rw [heval, eval_map, hinverse]
    exact zero_pow (by decide)
  let y₀ : Z := ⟨Fin.cons ((Q x).coeff k)⁻¹ x, hstart⟩
  have hr₀ : r y₀ = x := Fin.tail_cons _ _
  have hy₀ : y₀ ∈ G := by
    change ¬∃ z : Fin n → ℝ, eval₂ (Int.castRingHom ℝ) (Fin.addCases z (r y₀)) P = 0
    rwa [hr₀]
  obtain ⟨y, hy, hgrid⟩ := exists_mem_coordinateRootGrid_of_isClopen
    (by omega : 1 ≤ 2 * (D + 1) + 1) (show Even (2 * (D + 1) + 1 + 1) from ⟨D + 2, by omega⟩)
    F hF (fun y => by rw [heval]; exact sq_nonneg _) G hG ⟨y₀, hy₀⟩
  exact ⟨k, hk, y.val, hW y, hy, hgrid⟩

end MvPolynomial.CriticalSystem
