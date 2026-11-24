/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial root selection)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.AlgebraicValueBounds
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.ThomSign
public import CslibFrontier.Foundations.Algebra.Polynomial.SignLabelPolynomial
public import CslibFrontier.Foundations.Algebra.Polynomial.SignLabelPolynomialBounds
import Mathlib.Tactic.Linarith

/-!
# Integer polynomial labels for sparse real-root selectors

A fixed-width family contains a distinguished positive test and a short list of
derivative signs. An integer polynomial realizes these tests at every real root.
Its degree and coefficient norm have uniform bounds. If a qualifying root
exists and the source degree is at most `2 ^ N`, a list of at most `N` derivative
tests makes the label positive at one qualifying root and negative at every
other real root.

Adapted from `DerivativeRootLabels` and `SparseIntegerRootLabels` in lean-canny
at commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

/-- The qualifying polynomial and its positive target occupy slot zero. The next `N`
slots contain derivatives of `p` and their targets from `L`. Missing slots test zero. -/
@[expose] noncomputable def sparseRootLabelTests {D : ℕ} (p q : Polynomial ℤ)
    (N : ℕ) (L : List (Fin D × SignType)) : Fin (N + 1) → Polynomial ℤ × SignType :=
  Fin.cases (q, 1) fun j =>
    L[j.val]?.elim (0, 0) fun c => (derivative^[c.1.val + 1] p, c.2)

/-- The integer polynomial encoding the qualifying test and the first `N` derivative tests. -/
@[expose] noncomputable def sparseIntegerRootLabel {D : ℕ} (p q : Polynomial ℤ)
    (N b : ℕ) (L : List (Fin D × SignType)) : Polynomial ℤ :=
  signLabelPolynomial (derivativeRootLabelPrecision D b)
    (fun i => (sparseRootLabelTests p q N L i).1) (fun i => (sparseRootLabelTests p q N L i).2)

private theorem sparseRootLabelTests_bounds {D N b : ℕ} {p q : Polynomial ℤ}
    (L : List (Fin D × SignType)) (hpD : p.natDegree ≤ D) (hqD : q.natDegree ≤ D)
    (hpb : p.coeffNorm1 ≤ 2 ^ b) (hqb : q.coeffNorm1 ≤ 2 ^ b) (i : Fin (N + 1)) :
    let g := (sparseRootLabelTests p q N L i).1
    g.natDegree ≤ D ∧ g.coeffNorm1 ≤ 2 ^ iterateDerivativeNormExponent D b := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨hqD, hqb.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))⟩
  · cases h : L[j.val]? with
    | none => simp [sparseRootLabelTests, h]
    | some c =>
      simp only [sparseRootLabelTests, Fin.cases_succ, h, Option.elim_some]
      exact ⟨(natDegree_iterate_derivative p _).trans ((Nat.sub_le _ _).trans hpD),
        coeffNorm1_iterate_derivative_le_two_pow p hpD hpb _⟩

/-- The degree and norm bounds are uniform over the list and its target signs. -/
theorem sparseIntegerRootLabel_bounds {D N b : ℕ} {p q : Polynomial ℤ}
    (L : List (Fin D × SignType)) (hpD : p.natDegree ≤ D) (hqD : q.natDegree ≤ D)
    (hpb : p.coeffNorm1 ≤ 2 ^ b) (hqb : q.coeffNorm1 ≤ 2 ^ b) :
    (sparseIntegerRootLabel p q N b L).natDegree ≤
        signLabelDegreeBound (N + 1) (derivativeRootLabelPrecision D b) D ∧
      (sparseIntegerRootLabel p q N b L).coeffNorm1 ≤
        2 ^ signLabelNormExponent (N + 1) (derivativeRootLabelPrecision D b)
          (iterateDerivativeNormExponent D b) :=
  signLabelPolynomial_bounds _ _ _
    (fun i => (sparseRootLabelTests_bounds L hpD hqD hpb hqb i).1)
    (fun i => (sparseRootLabelTests_bounds L hpD hqD hpb hqb i).2)

private theorem sparseRootLabelTests_match_iff {D N : ℕ} (p q : Polynomial ℤ)
    (L : List (Fin D × SignType)) (hL : L.length ≤ N) (x : ℝ) :
    (∀ i : Fin (N + 1),
      SignType.sign ((sparseRootLabelTests p q N L i).1.eval₂ (Int.castRingHom ℝ) x) =
        (sparseRootLabelTests p q N L i).2) ↔
      0 < q.eval₂ (Int.castRingHom ℝ) x ∧
        ∀ c ∈ L, (p.map (Int.castRingHom ℝ)).derivativeSign x (c.1.val + 1) = c.2 := by
  rw [Fin.forall_fin_succ]
  simp only [sparseRootLabelTests, Fin.cases_zero, Fin.cases_succ, sign_eq_one_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
    have ht := h ⟨j, hj.trans_le hL⟩
    simpa only [List.getElem?_eq_getElem hj, Option.elim_some, derivativeSign,
      iterate_derivative_map, eval_map] using ht
  · intro h j
    cases ht : L[j.val]? with
    | none => simp
    | some c =>
      simpa only [ht, Option.elim_some, derivativeSign, iterate_derivative_map, eval_map] using
        h c (List.mem_of_getElem? ht)

/-- At a real root, the label has magnitude at least one half and is positive exactly
when the qualifying test is positive and every listed derivative sign matches. -/
theorem eval₂_sparseIntegerRootLabel_margin {D N b : ℕ} {p q : Polynomial ℤ} (hp : p ≠ 0)
    (L : List (Fin D × SignType)) (hL : L.length ≤ N)
    (hpD : p.natDegree ≤ D) (hqD : q.natDegree ≤ D)
    (hpb : p.coeffNorm1 ≤ 2 ^ b) (hqb : q.coeffNorm1 ≤ 2 ^ b)
    {x : ℝ} (hx : p.eval₂ (Int.castRingHom ℝ) x = 0) :
    let y := (sparseIntegerRootLabel p q N b L).eval₂ (Int.castRingHom ℝ) x
    ((1 : ℝ) / 2 ≤ y ∨ y ≤ -(1 : ℝ) / 2) ∧
      (0 < y ↔ 0 < q.eval₂ (Int.castRingHom ℝ) x ∧
        ∀ c ∈ L, (p.map (Int.castRingHom ℝ)).derivativeSign x (c.1.val + 1) = c.2) := by
  have h := eval₂_signLabelPolynomial_margin (derivativeRootLabelPrecision D b)
    (fun i => (sparseRootLabelTests p q N L i).1) (fun i => (sparseRootLabelTests p q N L i).2)
    x fun i =>
      let hb := sparseRootLabelTests_bounds L hpD hqD hpb hqb i
      eval₂_eq_zero_or_dyadic_bounds hp hpD hb.1 hpb hb.2 hx
  exact ⟨h.1, h.2.trans (sparseRootLabelTests_match_iff p q L hL x)⟩

/-- If some real root has a positive qualifying test, a label from at most `N` derivative
tests is positive at one such root and negative at every other real root. -/
theorem exists_sparseIntegerRootLabel {D N b : ℕ} {p q : Polynomial ℤ} (hp : p ≠ 0)
    (hpD : p.natDegree ≤ D) (hDN : D ≤ 2 ^ N) (hqD : q.natDegree ≤ D)
    (hpb : p.coeffNorm1 ≤ 2 ^ b) (hqb : q.coeffNorm1 ≤ 2 ^ b)
    (hex : ∃ x : ℝ, p.eval₂ (Int.castRingHom ℝ) x = 0 ∧ 0 < q.eval₂ (Int.castRingHom ℝ) x) :
    ∃ L : List (Fin D × SignType), L.length ≤ N ∧ ∃ x : ℝ,
      p.eval₂ (Int.castRingHom ℝ) x = 0 ∧ 0 < q.eval₂ (Int.castRingHom ℝ) x ∧
      0 < (sparseIntegerRootLabel p q N b L).eval₂ (Int.castRingHom ℝ) x ∧
      ∀ y : ℝ, p.eval₂ (Int.castRingHom ℝ) y = 0 → y ≠ x →
        (sparseIntegerRootLabel p q N b L).eval₂ (Int.castRingHom ℝ) y < 0 := by
  classical
  let r := p.map (Int.castRingHom ℝ)
  have hr : r ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  let S := r.roots.toFinset.filter fun x => 0 < q.eval₂ (Int.castRingHom ℝ) x
  have hmem (x : ℝ) : x ∈ S ↔ p.eval₂ (Int.castRingHom ℝ) x = 0 ∧
      0 < q.eval₂ (Int.castRingHom ℝ) x := by
    simp only [S, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hr, IsRoot.def, r, eval_map]
  obtain ⟨w, hw⟩ := hex
  obtain ⟨L, hL, x, hxS, hselect⟩ :=
    exists_short_derivativeSign_selector r hr (natDegree_map_le.trans hpD) hDN
      ⟨w, (hmem w).mpr hw⟩ fun y hy => by
        simpa only [IsRoot.def, r, eval_map] using ((hmem y).mp hy).1
  obtain ⟨hx, hqx⟩ := (hmem x).mp hxS
  have hmargin {y : ℝ} (hy : p.eval₂ (Int.castRingHom ℝ) y = 0) :=
    eval₂_sparseIntegerRootLabel_margin hp L hL hpD hqD hpb hqb hy
  refine ⟨L, hL, x, hx, hqx, (hmargin hx).2.mpr ⟨hqx, (hselect x hxS).mpr rfl⟩, ?_⟩
  intro y hy hne
  have hypos := (hmargin hy).2
  have hnot : ¬ 0 < (sparseIntegerRootLabel p q N b L).eval₂ (Int.castRingHom ℝ) y := by
    intro hpos
    obtain ⟨hqy, hs⟩ := hypos.mp hpos
    exact hne ((hselect y ((hmem y).mpr ⟨hy, hqy⟩)).mp hs)
  rcases (hmargin hy).1 with h | h <;> linarith

end Polynomial
