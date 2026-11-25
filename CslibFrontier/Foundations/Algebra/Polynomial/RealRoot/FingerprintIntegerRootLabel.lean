/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial root selection)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.AlgebraicValueBounds
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.DerivativeFingerprint
public import CslibFrontier.Foundations.Algebra.Polynomial.SignLabelPolynomialBounds
import Mathlib.Tactic.Linarith

/-!
# Integer fingerprint labels for prescribed real roots

The test at slot zero is the qualifying polynomial. The other slots are the positive
derivative orders of the source, weighted by the modular powers used in its derivative
fingerprint. At a real root the resulting integer polynomial has a uniform sign margin.
A bounded fingerprint selects any prescribed root at which the qualifying test is positive.

Adapted from `FingerprintIntegerRootLabels` in lean-canny at commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open scoped BigOperators

/-- Slot zero qualifies a root. Slot `i.succ` tests derivative order `i.val + 1`. -/
@[expose] noncomputable def fingerprintRootLabelTests (p q : ℤ[X]) (D : ℕ) :
    Fin (D + 1) → ℤ[X] :=
  Fin.cases q (fun i => derivative^[i.val + 1] p)

/-- Clear the weighted derivative-sign label for a prescribed integer fingerprint.
`D` bounds the degrees, `b` bounds the base-two norm exponents, and the weights
are the least residues of powers of `t` modulo `μ`. -/
@[expose] noncomputable def fingerprintIntegerRootLabel (p q : ℤ[X]) (D b μ t : ℕ)
    (target : ℤ) : ℤ[X] :=
  fingerprintLabelPolynomial (derivativeRootLabelPrecision D b) (D * μ)
    (fingerprintRootLabelTests p q D)
    (fun i => t ^ i.val % μ) target

private theorem sum_fingerprint_weights_le (D μ t : ℕ) (hμ : 0 < μ) :
    ∑ i : Fin D, t ^ i.val % μ ≤ D * μ := by
  calc
    _ ≤ ∑ _ : Fin D, μ := Finset.sum_le_sum fun i _ => (Nat.mod_lt _ hμ).le
    _ = _ := by simp

private theorem fingerprintRootLabelTests_bounds {D b : ℕ} {p q : ℤ[X]}
    (hpD : p.natDegree ≤ D) (hqD : q.natDegree ≤ D)
    (hpb : p.coeffNorm1 ≤ 2 ^ b) (hqb : q.coeffNorm1 ≤ 2 ^ b) (i : Fin (D + 1)) :
    let g := fingerprintRootLabelTests p q D i
    g.natDegree ≤ D ∧ g.coeffNorm1 ≤ 2 ^ iterateDerivativeNormExponent D b := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨hqD, hqb.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))⟩
  · exact ⟨(natDegree_iterate_derivative p _).trans ((Nat.sub_le _ _).trans hpD),
      coeffNorm1_iterate_derivative_le_two_pow p hpD hpb _⟩

/-- Degree and coefficient norm bounds for every label with a bounded target fingerprint. -/
theorem fingerprintIntegerRootLabel_bounds {D b μ : ℕ} {p q : ℤ[X]} (t : ℕ) {target : ℤ}
    (hμ : 0 < μ) (hpD : p.natDegree ≤ D) (hqD : q.natDegree ≤ D)
    (hpb : p.coeffNorm1 ≤ 2 ^ b) (hqb : q.coeffNorm1 ≤ 2 ^ b)
    (ht : target.natAbs ≤ D * μ) :
    let B := derivativeRootLabelPrecision D b
    let label := fingerprintIntegerRootLabel p q D b μ t target
    label.natDegree ≤ fingerprintLabelDegreeBound D B (D * μ) D ∧
      label.coeffNorm1 ≤
        2 ^ fingerprintLabelNormExponent D B (D * μ) (iterateDerivativeNormExponent D b) :=
  fingerprintLabelPolynomial_bounds _ _ _ _ _
    (fun i => (fingerprintRootLabelTests_bounds hpD hqD hpb hqb i).1)
    (fun i => (fingerprintRootLabelTests_bounds hpD hqD hpb hqb i).2)
    (sum_fingerprint_weights_le D μ t hμ) ht

/-- At a real root the label has magnitude at least one half. Its sign is positive exactly
when the qualifying polynomial is positive and the derivative fingerprint equals the target. -/
theorem eval₂_fingerprintIntegerRootLabel_margin {D b μ : ℕ} {p q : ℤ[X]}
    (hp : p ≠ 0) (t : ℕ) (target : ℤ) (hμ : 0 < μ)
    (hpD : p.natDegree ≤ D) (hqD : q.natDegree ≤ D)
    (hpb : p.coeffNorm1 ≤ 2 ^ b) (hqb : q.coeffNorm1 ≤ 2 ^ b)
    {x : ℝ} (hx : p.eval₂ (Int.castRingHom ℝ) x = 0) :
    let y := (fingerprintIntegerRootLabel p q D b μ t target).eval₂ (Int.castRingHom ℝ) x
    ((1 : ℝ) / 2 ≤ y ∨ y ≤ -(1 : ℝ) / 2) ∧
      (0 < y ↔ (p.map (Int.castRingHom ℝ)).derivativeFingerprint D μ t x = target ∧
        0 < q.eval₂ (Int.castRingHom ℝ) x) := by
  have h := eval₂_fingerprintLabelPolynomial_margin (derivativeRootLabelPrecision D b) (D * μ)
    (fingerprintRootLabelTests p q D) (fun i => t ^ i.val % μ) target x
    (sum_fingerprint_weights_le D μ t hμ) fun i =>
      let hb := fingerprintRootLabelTests_bounds hpD hqD hpb hqb i
      eval₂_eq_zero_or_dyadic_bounds hp hpD hb.1 hpb hb.2 hx
  simpa only [fingerprintIntegerRootLabel, derivativeFingerprint, fingerprintRootLabelTests,
    Fin.cases_zero, Fin.cases_succ, derivativeSign, iterate_derivative_map, eval_map] using h

/-- A bounded fingerprint and its integer label give a positive margin at any prescribed
qualifying root and a negative margin at every other real root of the source. -/
theorem exists_fingerprintIntegerRootLabel {D b : ℕ} {p q : ℤ[X]} (hp : p ≠ 0)
    (hpD : p.natDegree ≤ D) (hqD : q.natDegree ≤ D)
    (hpb : p.coeffNorm1 ≤ 2 ^ b) (hqb : q.coeffNorm1 ≤ 2 ^ b)
    {x : ℝ} (hx : p.eval₂ (Int.castRingHom ℝ) x = 0) (hxq : 0 < q.eval₂ (Int.castRingHom ℝ) x) :
    ∃ μ t : ℕ, ∃ target : ℤ,
      μ.Prime ∧ 2 < μ ∧ μ ≤ 2 * (D ^ 3 + 2) ∧ t < μ ∧ target.natAbs ≤ D * μ ∧
      (1 : ℝ) / 2 ≤
        (fingerprintIntegerRootLabel p q D b μ t target).eval₂ (Int.castRingHom ℝ) x ∧
      ∀ y : ℝ, p.eval₂ (Int.castRingHom ℝ) y = 0 → y ≠ x →
        (fingerprintIntegerRootLabel p q D b μ t target).eval₂ (Int.castRingHom ℝ) y ≤
          -(1 : ℝ) / 2 := by
  let r := p.map (Int.castRingHom ℝ)
  have hr : r ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  have hroot (y : ℝ) : r.IsRoot y ↔ p.eval₂ (Int.castRingHom ℝ) y = 0 := by
    simp only [r, IsRoot.def, eval_map]
  obtain ⟨μ, t, hμ, hμ₂, hμD, ht, hsep⟩ :=
    exists_derivativeFingerprint_injOn_roots r hr (natDegree_map_le.trans hpD)
  let target := r.derivativeFingerprint D μ t x
  have hmargin {y : ℝ} (hy : p.eval₂ (Int.castRingHom ℝ) y = 0) :=
    eval₂_fingerprintIntegerRootLabel_margin hp t target hμ.pos hpD hqD hpb hqb hy
  refine ⟨μ, t, target, hμ, hμ₂, hμD, ht, natAbs_derivativeFingerprint_le r D μ t x hμ.pos,
    ?_, ?_⟩
  · have hpos := (hmargin hx).2.mpr ⟨rfl, hxq⟩
    exact (hmargin hx).1.resolve_right (by linarith)
  · intro y hy hne
    have hnot : ¬ 0 <
        (fingerprintIntegerRootLabel p q D b μ t target).eval₂ (Int.castRingHom ℝ) y := by
      intro hpos
      exact hne (hsep ((hroot y).mpr hy) ((hroot x).mpr hx) ((hmargin hy).2.mp hpos).1)
    exact (hmargin hy).1.resolve_left (by linarith [not_lt.mp hnot])

end Polynomial
