/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import CslibFrontier.Foundations.Data.MvPolynomial.Determinant
import CslibFrontier.Foundations.Data.MvPolynomial.Shift
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Combinatorics.Nullstellensatz

/-!
# Schwartz–Zippel over any finite set of variables

Mathlib's `MvPolynomial.schwartz_zippel_totalDegree` bounds the proportion of the points of
`S ^ n` at which a nonzero polynomial in the variables `Fin n` vanishes by `totalDegree / |S|`.
`MvPolynomial.schwartz_zippel_totalDegree_fintype` transports it to the variables of any finite
type `σ`, by renaming along `Fintype.equivFin σ`. For `n` variables over a finite domain with `q`
elements it reads `#zeros * q ≤ d * q ^ n` (`MvPolynomial.card_filter_eval_eq_zero_mul_card_le`).
A nonzero polynomial of total degree below `|S|` does not vanish on all of `S ^ σ`
(`MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card`), a consequence of Mathlib's
`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`.

## Main results

* `MvPolynomial.schwartz_zippel_totalDegree_fintype`: the Schwartz–Zippel lemma for variables
  indexed by a finite type.
* `MvPolynomial.card_filter_eval_eq_zero_mul_card_le`: its counting form over a finite domain.
* `MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card`: a nonzero polynomial of total degree
  below `|S|` has a nonzero value at a point of `S ^ σ`.
-/

public section

namespace MvPolynomial

open Finset Fintype

/-- The **Schwartz–Zippel lemma** for variables indexed by a finite type `σ`: a nonzero polynomial
over an integral domain vanishes on at most a `totalDegree / |S|` proportion of the points of
`S ^ σ`. -/
theorem schwartz_zippel_totalDegree_fintype {R σ : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] [Fintype σ] [DecidableEq σ] {p : MvPolynomial σ R} (hp : p ≠ 0)
    (S : Finset R) :
    #{f ∈ piFinset fun _ : σ => S | eval f p = 0} / (#S ^ card σ : ℚ≥0) ≤
      p.totalDegree / #S := by
  set e := equivFin σ
  have hp' : rename e p ≠ 0 := fun h => hp (rename_injective _ e.injective (by rw [h, map_zero]))
  have hdeg : (rename e p).totalDegree = p.totalDegree := totalDegree_renameEquiv e p
  have hsz := schwartz_zippel_totalDegree hp' S
  rw [hdeg] at hsz
  convert hsz using 3
  refine card_equiv (Equiv.arrowCongr e (Equiv.refl R)) fun f => ?_
  change f ∈ (_ : Finset _) ↔ f ∘ e.symm ∈ (_ : Finset _)
  simp only [mem_filter, mem_piFinset, eval_rename, Function.comp_assoc, e.symm_comp_self,
    Function.comp_id, Function.comp_apply]
  exact and_congr ⟨fun h i => h _, fun h i => by simpa only [e.symm_apply_apply] using h (e i)⟩
    Iff.rfl

/-- The **Schwartz–Zippel lemma** over a finite integral domain with `q` elements, in counting
form: a nonzero polynomial in `n` variables of total degree at most `d` has at most `d * q ^ n / q`
zeros, stated without division as `#zeros * q ≤ d * q ^ n`. -/
theorem card_filter_eval_eq_zero_mul_card_le {R : Type*} [CommRing R] [IsDomain R] [Fintype R]
    [DecidableEq R] {n d : ℕ} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (hd : p.totalDegree ≤ d) :
    #{x | eval x p = 0} * card R ≤ d * card R ^ n := by
  have hq : (0 : ℚ≥0) < card R := by exact_mod_cast Fintype.card_pos
  have hsz := schwartz_zippel_totalDegree hp (univ : Finset R)
  rw [piFinset_univ, card_univ, div_le_div_iff₀ (pow_pos hq n) hq] at hsz
  exact_mod_cast hsz.trans (by gcongr : (p.totalDegree : ℚ≥0) * card R ^ n ≤ d * card R ^ n)

/-- Two distinct polynomials of individual degree at most `d` in `n` variables
can agree on at most a fraction `n * d / |R|` of the evaluation points. -/
theorem card_filter_eval_eq_mul_card_le {R : Type*} [CommRing R] [IsDomain R] [Fintype R]
    [DecidableEq R] {n d : ℕ} {p q : MvPolynomial (Fin n) R} (hne : p ≠ q)
    (hp : ∀ i, p.degreeOf i ≤ d) (hq : ∀ i, q.degreeOf i ≤ d) :
    #{x | eval x p = eval x q} * card R ≤ (n * d) * card R ^ n := by
  have hdeg : (p - q).totalDegree ≤ n * d :=
    (totalDegree_le_card_mul_of_degreeOf_le fun i =>
      (degreeOf_sub_le i _ _).trans (max_le (hp i) (hq i))).trans_eq (by rw [Fintype.card_fin])
  simpa only [map_sub, sub_eq_zero] using
    card_filter_eval_eq_zero_mul_card_le (sub_ne_zero.mpr hne) hdeg

/-- A nonzero polynomial over an integral domain whose total degree is below `|S|` has a nonzero
value at some point of `S ^ σ`. -/
theorem exists_eval_ne_zero_of_totalDegree_lt_card {R σ : Type*} [CommRing R] [IsDomain R]
    [Finite σ] {p : MvPolynomial σ R} (hp : p ≠ 0) {S : Finset R} (hS : p.totalDegree < #S) :
    ∃ x : σ → R, (∀ i, x i ∈ S) ∧ eval x p ≠ 0 := by
  by_contra! h
  exact hp (eq_zero_of_eval_zero_at_prod_finset p (fun _ => S)
    (fun i => (degreeOf_le_totalDegree p i).trans_lt hS) h)

end MvPolynomial
