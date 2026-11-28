/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.ReedMuller
import CslibFrontier.Foundations.Data.MvPolynomial.Shift
import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Low-degree extensions

Let `h : H ↪ F` embed a finite set `H` of size `|H|` in a field `F`. Every function
`f : (Fin m → H) → F` on the grid `H ^ m` is the restriction of a polynomial of low degree: the
*low-degree extension*
`lowDegreeExtension h f x = ∑ u, f u * ∏ i, L (u i) (x i)`, where `L a` is the Lagrange basis
polynomial of the node `h a` among the nodes `h H`
[Babai, Fortnow, Levin, Szegedy][BabaiFortnowLevinSzegedy1991],
[Arora and Barak, Chapter 19][AroraBarak09]. It agrees with `f` on the grid
(`Cslib.Code.lowDegreeExtension_apply_embed`) and is a codeword of the Reed–Muller code of degree
`m * (|H| - 1)` (`Cslib.Code.lowDegreeExtension_mem_reedMuller`). It is also the evaluation of a
polynomial of degree at most `|H| - 1` in each variable
(`Cslib.Code.exists_degreeOf_le_eval_eq_lowDegreeExtension`), which is
[Goldreich, Exercise 7.12][Goldreich2007DraftR4]. For `H = {0, 1}` it is the multilinear extension,
which is not stated here.

Low-degree extensions encode truth tables into Reed–Muller codewords: the truth table of a
function on `n = m * b` bits, read as a function on `(BitString b) ^ m`, extends to a polynomial
in `m` variables of total degree at most `m * (2 ^ b - 1)` over a field with at least `2 ^ b`
elements. Informally, evaluating the extension at a point costs `|H| ^ m` terms, linear in the
size of the truth table, which is what makes encodings of functions computable in exponential time;
no running time is formalized in this module.

## Main definitions

* `Cslib.Code.lowDegreeExtension`: the low-degree extension.

## Main results

* `Cslib.Code.lowDegreeExtension_apply_embed`: it extends `f`.
* `Cslib.Code.lowDegreeExtension_mem_reedMuller`: it is a Reed–Muller codeword.
* `Cslib.Code.exists_degreeOf_le_eval_eq_lowDegreeExtension`: it has individual degree at most
  `|H| - 1` (Goldreich, Exercise 7.12).

## References

* [L. Babai, L. Fortnow, L. Levin, M. Szegedy, *Checking computations in polylogarithmic time*]
  [BabaiFortnowLevinSzegedy1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft `r4.pdf` (March
  2007)][Goldreich2007DraftR4], Exercise 7.12 (printed p. 307)
-/

@[expose] public section

namespace Cslib.Code

open Finset

variable {F : Type*} [Field F] {H : Type*} [Fintype H] [DecidableEq H] {m : ℕ}

/-- The **low-degree extension** of `f : (Fin m → H) → F` along the embedding `h : H ↪ F`. -/
noncomputable def lowDegreeExtension (h : H ↪ F) (f : (Fin m → H) → F) : (Fin m → F) → F :=
  fun x => ∑ u : Fin m → H, f u * ∏ i, (Lagrange.basis univ h (u i)).eval (x i)

/-- **The low-degree extension extends `f`**: it agrees with `f` on the grid. -/
theorem lowDegreeExtension_apply_embed (h : H ↪ F) (f : (Fin m → H) → F) (u : Fin m → H) :
    lowDegreeExtension h f (fun i => h (u i)) = f u := by
  rw [lowDegreeExtension, Finset.sum_eq_single u]
  · rw [prod_eq_one fun i _ => Lagrange.eval_basis_self h.injective.injOn (mem_univ _),
      mul_one]
  · intro u' _ hu'
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu'
    rw [prod_eq_zero (mem_univ i) (Lagrange.eval_basis_of_ne hi (mem_univ _)), mul_zero]
  · exact fun h' => absurd (mem_univ u) h'

/-- A univariate polynomial placed in the variable `i` has degree at most its degree in `i` and
degree zero in every other variable. -/
private theorem degreeOf_toMvPolynomial_le (p : Polynomial F) (i j : Fin m) :
    (p.toMvPolynomial i).degreeOf j ≤ if j = i then p.natDegree else 0 := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  rw [map_sum]
  refine (MvPolynomial.degreeOf_sum_le j _ _).trans <| Finset.sup_le fun k hk => ?_
  rw [map_mul, map_pow, Polynomial.toMvPolynomial_C, Polynomial.toMvPolynomial_X]
  refine (MvPolynomial.degreeOf_C_mul_le _ j _).trans <|
    (MvPolynomial.degreeOf_pow_le j _ k).trans ?_
  rw [MvPolynomial.degreeOf_X]
  split_ifs
  · simpa using Nat.lt_succ_iff.1 (mem_range.1 hk)
  · simp

/-- **Low-degree extension with individual degree**
[Goldreich, Exercise 7.12][Goldreich2007DraftR4]: for `H ⊆ F` (here embedded by `h`) and every
`f : H ^ m → F`, there is an `m`-variate polynomial of degree at most `|H| - 1` in each variable
that agrees with `f` on `H ^ m`. The polynomial evaluates to `lowDegreeExtension h f` everywhere.
The guideline's `f̂ x = ∑ a, f a * ∏ i, ∏ b ≠ a i, (x i - b) / (a i - b)` is this extension, since
`∏ b ≠ a i, (x i - b) / (a i - b)` is the Lagrange basis polynomial of `a i`. The source's `F` is
the finite field of the Theorem 7.12 construction; here `F` is any field. -/
theorem exists_degreeOf_le_eval_eq_lowDegreeExtension (h : H ↪ F) (f : (Fin m → H) → F) :
    ∃ P : MvPolynomial (Fin m) F, (∀ i, P.degreeOf i ≤ Fintype.card H - 1) ∧
      (∀ x, MvPolynomial.eval x P = lowDegreeExtension h f x) ∧
      ∀ u, MvPolynomial.eval (fun i => h (u i)) P = f u := by
  classical
  let L : H → Polynomial F := fun a => Lagrange.basis univ h a
  have hL : ∀ a, (L a).natDegree = Fintype.card H - 1 := fun a => by
    rw [Lagrange.natDegree_basis h.injective.injOn (mem_univ a), card_univ]
  let P : MvPolynomial (Fin m) F := ∑ u : Fin m → H,
    MvPolynomial.C (f u) * ∏ i, (L (u i)).toMvPolynomial i
  have heval : ∀ x, MvPolynomial.eval x P = lowDegreeExtension h f x := fun x => by
    simp only [P, lowDegreeExtension, map_sum, map_mul, MvPolynomial.eval_C, map_prod,
      MvPolynomial.eval_toMvPolynomial, L]
  refine ⟨P, fun j => ?_, heval, fun u => by rw [heval, lowDegreeExtension_apply_embed]⟩
  refine (MvPolynomial.degreeOf_sum_le j _ _).trans <| Finset.sup_le fun u _ => ?_
  refine (MvPolynomial.degreeOf_C_mul_le _ j _).trans <|
    (MvPolynomial.degreeOf_prod_le j _ _).trans ?_
  calc ∑ i, ((L (u i)).toMvPolynomial i).degreeOf j
      ≤ ∑ i, if j = i then Fintype.card H - 1 else 0 :=
        sum_le_sum fun i _ => (degreeOf_toMvPolynomial_le _ i j).trans <| by rw [hL]
    _ = Fintype.card H - 1 := by simp

/-- **The low-degree extension is a Reed–Muller codeword** of degree `m * (|H| - 1)`: its
polynomial has degree at most `|H| - 1` in each of the `m` variables. -/
theorem lowDegreeExtension_mem_reedMuller (h : H ↪ F) (f : (Fin m → H) → F) :
    lowDegreeExtension h f ∈ reedMuller F m (m * (Fintype.card H - 1)) := by
  obtain ⟨P, hdeg, heval, -⟩ := exists_degreeOf_le_eval_eq_lowDegreeExtension h f
  exact mem_reedMuller.2 ⟨P,
    (MvPolynomial.totalDegree_le_card_mul_of_degreeOf_le hdeg).trans_eq (by rw [Fintype.card_fin]),
    funext heval⟩

end Cslib.Code
