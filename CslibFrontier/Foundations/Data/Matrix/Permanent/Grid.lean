/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Permanent
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Sums over two families of bits as permanents

Let `v : N → V` and `w : N → K` be surjections of finite types: every *incidence* `n : N` joins a
bit `x (v n)` of a first family `x : V → Bool` to a bit `r (w n)` of a second family
`r : K → Bool`. A *grid sum* sums over both families the product of one weight `W n` for each
incidence, `∑ x, ∑ r, ∏ n, W n (x (v n)) (r (w n))`. Over a commutative ring in which `2` is
invertible, every grid sum is a permanent of size `3 * |N|`, with entries `0`, `±1`, `±1/2` and
sums of weights (`Matrix.exists_permanent_eq_gridSum`), and so of every larger size, padding with
an identity block.

The proof has three steps. First, the permanent of `M` is the coefficient of the product of all
variables in `∏ i, ∑ j, M i j * X j`, and that coefficient does not change modulo the squares of
the variables. Second, the *grid matrix* has three rows and columns `(n, none)`, `(n, some true)`,
`(n, some false)` for every incidence; modulo squares, the product of its first two rows at `n`
collapses to two terms, so that expanding the product of all rows chooses, at every incidence, a
bit of a cycle of a permutation `σ`, a bit of a cycle of `ρ`, and a weight. The choices whose
columns are all distinct are the families of bits constant on the cycles. Third, `σ` and `ρ` are
chosen with the fibres of `v` and `w` as cycles.

## Main results

* `Matrix.exists_permanent_eq_gridSum`: grid sums are permanents.

## References

* [Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026], Proposition prop:grid
-/

public section

namespace Matrix

open Finset MvPolynomial

section Coeff


variable {R : Type*} [CommRing R]

/-- The exponent of the product of all variables. -/
private noncomputable def ones (γ : Type*) [Fintype γ] : γ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun _ => 1

@[simp] private theorem ones_apply {γ : Type*} [Fintype γ] (c : γ) : ones γ c = 1 := rfl

section Bij

variable {γ I : Type*} [Fintype γ] [Fintype I]

private theorem sum_single_eq_ones (f : I → γ) :
    (∑ i, Finsupp.single (f i) 1 = ones γ) ↔ Function.Bijective f := by
  classical
  have hap : ∀ c, (∑ i, Finsupp.single (f i) 1 : γ →₀ ℕ) c = #{i | f i = c} := fun c => by
    rw [Finsupp.finsetSum_apply, Finset.card_filter]
    exact Finset.sum_congr rfl fun i _ => by rw [Finsupp.single_apply]
  rw [Function.bijective_iff_existsUnique, Finsupp.ext_iff]
  simp only [hap, ones_apply, Finset.card_eq_one, Finset.eq_singleton_iff_unique_mem,
    mem_filter, mem_univ, true_and]
  rfl

variable {N J κ : Type*} [Fintype N] [Fintype J] [Fintype κ] [DecidableEq N]

open scoped Classical in
/-- Expand a product of sums of monomials and take the coefficient of the product of all
variables. -/
private theorem coeff_ones_prod (w : N → κ → R) (g : N → κ → J → γ) :
    (∏ i, ∑ a, C (w i a) * ∏ j, (X (g i a j) : MvPolynomial γ R)).coeff (ones γ) =
      ∑ f : N → κ, if Function.Bijective (fun p : N × J => g p.1 (f p.1) p.2) then ∏ i, w i (f i)
        else 0 := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, coeff_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, coeff_C_mul, ← Fintype.prod_prod_type'
    (f := fun i j => (X (g i (f i) j) : MvPolynomial γ R))]
  have : (∏ p : N × J, (X (g p.1 (f p.1) p.2) : MvPolynomial γ R)) =
      monomial (∑ p : N × J, Finsupp.single (g p.1 (f p.1) p.2) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [this, coeff_monomial]
  simp only [sum_single_eq_ones (fun p : N × J => g p.1 (f p.1) p.2)]
  split_ifs <;> simp

open scoped Classical in
private theorem sum_perm_eq [DecidableEq γ] (w : γ → γ → R) :
    ∑ σ : Equiv.Perm γ, ∏ i, w i (σ i) =
      ∑ f : γ → γ, if Function.Bijective f then ∏ i, w i (f i) else 0 := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (i := fun f hf => Equiv.ofBijective f (Finset.mem_filter.1 hf).2)
    (j := fun σ _ => (σ : γ → γ)) ?_ ?_ ?_ ?_ ?_
  · simp
  · intro σ _
    simp only [mem_filter, mem_univ, true_and]
    exact σ.bijective
  · intros; rfl
  · intros; ext; rfl
  · intros; rfl

/-- The permanent is a coefficient. -/
private theorem permanent_eq_coeff [DecidableEq γ] (M : Matrix γ γ R) :
    M.permanent =
      (∏ i, ∑ j, C (M i j) * (X j : MvPolynomial γ R)).coeff (ones γ) := by
  classical
  have h := coeff_ones_prod (N := γ) (J := Unit) (κ := γ) (γ := γ) (fun i j => M i j)
    (fun _ a _ => a)
  have h2 : M.permanent = ∑ σ : Equiv.Perm γ, ∏ i, M i (σ i) := by
    rw [← Matrix.permanent_transpose]
    rfl
  simp only [Finset.univ_unique, Finset.prod_singleton] at h
  rw [h, h2]
  refine (sum_perm_eq (fun i j => M i j)).trans (Finset.sum_congr rfl fun f _ => ?_)
  have hiff : Function.Bijective f ↔ Function.Bijective fun p : γ × Unit => f p.1 :=
    ⟨fun hb => hb.comp (Equiv.prodPUnit γ).bijective,
      fun hb => hb.comp (Equiv.prodPUnit γ).symm.bijective⟩
  by_cases hb : Function.Bijective f
  · rw [ite_eq_left hb, ite_eq_left (hiff.1 hb)]
  · rw [ite_eq_right hb, ite_eq_right (fun h' => hb (hiff.2 h'))]

end Bij

section Squares

variable {γ : Type*} [Fintype γ]

variable (γ R) in
/-- The ideal of the squares of the variables. -/
private noncomputable def sqIdeal : Ideal (MvPolynomial γ R) :=
  Ideal.span (Set.range fun c => X c * X c)

private theorem coeff_ones_of_mem {p : MvPolynomial γ R} (h : p ∈ sqIdeal R γ) :
    p.coeff (ones γ) = 0 := by
  classical
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← mul_assoc, coeff_mul_X', coeff_mul_X']
  simp [Finsupp.mem_support_iff]

private theorem coeff_ones_congr {p q : MvPolynomial γ R}
    (h : Ideal.Quotient.mk (sqIdeal R γ) p = Ideal.Quotient.mk (sqIdeal R γ) q) :
    p.coeff (ones γ) = q.coeff (ones γ) := by
  have := coeff_ones_of_mem (Ideal.Quotient.eq.1 h)
  rwa [AddMonoidAlgebra.coeff_sub_apply, sub_eq_zero] at this

omit [Fintype γ] in
private theorem mk_X_sq (c : γ) : Ideal.Quotient.mk (sqIdeal R γ) (X c) ^ 2 = 0 := by
  rw [sq, ← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨c, rfl⟩)

omit [Fintype γ] in
/-- Modulo squares, a product of two linear forms in four variables has only two terms. -/
private theorem mk_gadget (h : R) (hh : h * 2 = 1) (p q r s : γ) :
    Ideal.Quotient.mk (sqIdeal R γ)
      ((C h * X p + C h * X q + C h * X r - C h * X s) *
        (X p + X q - X r + X s)) = Ideal.Quotient.mk (sqIdeal R γ) (X p * X q + X r * X s) := by
  simp only [map_mul, map_add, map_sub]
  have h1 := mk_X_sq (R := R) p
  have h2 := mk_X_sq (R := R) q
  have h3 := mk_X_sq (R := R) r
  have h4 := mk_X_sq (R := R) s
  have h5 : Ideal.Quotient.mk (sqIdeal R γ) (C h) * 2 = 1 := by
    rw [← map_ofNat (Ideal.Quotient.mk (sqIdeal R γ)) 2, ← map_mul, ← map_ofNat C 2,
      ← map_mul, hh, map_one, map_one]
  generalize Ideal.Quotient.mk (sqIdeal R γ) (X p) = p at *
  generalize Ideal.Quotient.mk (sqIdeal R γ) (X q) = q at *
  generalize Ideal.Quotient.mk (sqIdeal R γ) (X r) = r at *
  generalize Ideal.Quotient.mk (sqIdeal R γ) (X s) = s at *
  generalize Ideal.Quotient.mk (sqIdeal R γ) (C h) = e at *
  linear_combination e * h1 + e * h2 - e * h3 - e * h4 + (p * q + r * s) * h5

end Squares

end Coeff

section Grid


variable {R : Type*} [CommRing R]
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The row that is chosen at `n`: `n` itself or its successor. -/
private def pick (σ : Equiv.Perm N) (s : N → Bool) (n : N) : N := if s n then n else σ n

omit [Fintype N] [DecidableEq N] in
private theorem pick_injective {σ : Equiv.Perm N} {s : N → Bool} (h : ∀ n, s (σ n) = s n) :
    Function.Injective (pick σ s) := by
  intro n m e
  unfold pick at e
  rcases hn : s n <;> rcases hm : s m <;>
    simp only [hn, hm, ite_true, ite_false, Bool.false_eq_true] at e
  · exact σ.injective e
  · simpa [e, hn, hm] using h n
  · simpa [← e, hn, hm] using h m
  · exact e

omit [Fintype N] [DecidableEq N] in
private theorem inv_of_pick_injective [Finite N] {σ : Equiv.Perm N} {s : N → Bool}
    (h : Function.Injective (pick σ s)) (n : N) :
    s (σ n) = s n := by
  rcases hn : s n <;> rcases hm : s (σ n)
  · rfl
  · have : pick σ s n = pick σ s (σ n) := by simp [pick, hn, hm]
    have := h this
    rw [← this, hn] at hm
    cases hm
  · obtain ⟨m, hm'⟩ := (Finite.injective_iff_surjective.1 h) (σ n)
    unfold pick at hm'
    rcases hs : s m <;> simp only [hs, ite_true, ite_false, Bool.false_eq_true] at hm'
    · have := σ.injective hm'
      rw [this, hn] at hs
      cases hs
    · rw [hm', hm] at hs
      cases hs
  · rfl

/-- The columns used by the three rows of an incidence. -/
private def slot (σ ρ : Equiv.Perm N) (n : N) (a : Bool × Bool × Bool) :
    Option Bool → N × Option Bool
  | none => (if a.1 then n else σ n, none)
  | some true => (n, some a.1)
  | some false => (if a.2.1 then n else ρ n, some !a.2.2)

omit [Fintype N] [DecidableEq N] in
private theorem slot_bijective [Finite N] (σ ρ : Equiv.Perm N) (s r q : N → Bool) :
    Function.Bijective (fun p : N × Option Bool => slot σ ρ p.1 (s p.1, r p.1, q p.1) p.2) ↔
      (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n) ∧ ∀ n, s (pick ρ r n) = q n := by
  constructor
  · rintro ⟨h, -⟩
    have h3 : ∀ n, s (pick ρ r n) = q n := by
      intro n
      by_contra hne
      have : ((n, some false) : N × Option Bool) = (pick ρ r n, some true) := by
        apply h
        simp only [slot, pick] at hne ⊢
        rw [← Bool.eq_not_of_ne hne]
      simp at this
    refine ⟨fun n => inv_of_pick_injective (fun n m e => ?_) n,
      fun n => inv_of_pick_injective (fun n m e => ?_) n, h3⟩
    · have : ((n, none) : N × Option Bool) = (m, none) := h (by
        simp only [slot]
        exact congrArg (fun x => (x, none)) e)
      exact (Prod.mk.inj this).1
    · have : ((n, some false) : N × Option Bool) = (m, some false) := h (by
        simp only [slot]
        rw [← h3 n, ← h3 m, e]
        exact congrArg (fun x => (x, some !s (pick ρ r m))) e)
      exact (Prod.mk.inj this).1
  · intro ⟨h1, h2, h3⟩
    rw [← Finite.injective_iff_bijective]
    have i1 := pick_injective h1
    have i2 := pick_injective h2
    rintro ⟨n, _ | _ | _⟩ ⟨m, _ | _ | _⟩ e <;>
      simp only [slot, Prod.mk.injEq, reduceCtorEq, and_false,
      Option.some.injEq] at e
    · rw [i1 e.1]
    · rw [i2 e.1]
    · exact absurd (e.2.trans ((congrArg s e.1).symm.trans (h3 n))) (by cases q n <;> decide)
    · exact absurd (e.2.symm.trans ((congrArg s e.1).trans (h3 m))) (by cases q m <;> decide)
    · rw [e.1]

/-- The indicator of a column. -/
private def ind (c₀ : N × Option Bool) (a : R) (c : N × Option Bool) : R := if c = c₀ then a else 0

/-- The matrix. -/
private def gridMatrix (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) :
    Matrix (N × Option Bool) (N × Option Bool) R
  | (n, none), c =>
    ind (n, none) h c + ind (n, some true) h c + ind (σ n, none) h c - ind (n, some false) h c
  | (n, some true), c =>
    ind (n, none) 1 c + ind (n, some true) 1 c - ind (σ n, none) 1 c + ind (n, some false) 1 c
  | (n, some false), c =>
    ind (n, some false) (W n true true) c + ind (n, some true) (W n false true) c +
      ind (ρ n, some false) (W (ρ n) true false) c + ind (ρ n, some true) (W (ρ n) false false) c

private theorem sum_ind (c₀ : N × Option Bool) (a : R) :
    ∑ c, C (ind c₀ a c) * (X c : MvPolynomial (N × Option Bool) R) =
      C a * X c₀ := by
  simp [ind, apply_ite C, ite_mul]

/-- The weight of a choice. -/
private def wt (ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) (a : Bool × Bool × Bool) : R :=
  if a.2.1 then W n a.2.2 true else W (ρ n) a.2.2 false

private theorem sum_row_none (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, C (gridMatrix h σ ρ W (n, none) c) * (X c : MvPolynomial (N × Option Bool) R) =
      C h * X (n, none) + C h * X (n, some true) +
        C h * X (σ n, none) - C h * X (n, some false) := by
  simp only [gridMatrix, map_add, map_sub, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_ind]

private theorem sum_row_true (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, C (gridMatrix h σ ρ W (n, some true) c) * (X c : MvPolynomial (N × Option Bool) R) =
      X (n, none) + X (n, some true) - X (σ n, none) + X (n, some false) := by
  simp only [gridMatrix, map_add, map_sub, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_ind, map_one, one_mul]

private theorem sum_row_false (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, C (gridMatrix h σ ρ W (n, some false) c) * (X c : MvPolynomial (N × Option Bool) R) =
      C (W n true true) * X (n, some false) + C (W n false true) * X (n, some true) +
        C (W (ρ n) true false) * X (ρ n, some false) +
        C (W (ρ n) false false) * X (ρ n, some true) := by
  simp only [gridMatrix, map_add, add_mul, Finset.sum_add_distrib, sum_ind]

private theorem gridMatrix_permanent_aux (h : R) (hh : h * 2 = 1) (σ ρ : Equiv.Perm N)
    (W : N → Bool → Bool → R) :
    (gridMatrix h σ ρ W).permanent = (∏ n, ∑ a, C (wt ρ W n a) *
      ∏ j, (X (slot σ ρ n a j) : MvPolynomial (N × Option Bool) R)).coeff
        (ones (N × Option Bool)) := by
  rw [permanent_eq_coeff]
  apply coeff_ones_congr
  rw [Fintype.prod_prod_type, map_prod, map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  simp only [Fintype.prod_option, Fintype.prod_bool]
  rw [sum_row_none, sum_row_true, sum_row_false, ← mul_assoc, map_mul, mk_gadget h hh, ← map_mul]
  congr 1
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, slot, wt, ite_true, ite_false,
    Bool.false_eq_true,
    Bool.not_true, Bool.not_false]
  ring

open scoped Classical in
private theorem gridMatrix_permanent (h : R) (hh : h * 2 = 1) (σ ρ : Equiv.Perm N)
    (W : N → Bool → Bool → R) :
    (gridMatrix h σ ρ W).permanent = ∑ s : N → Bool, ∑ r : N → Bool,
      if (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n) then ∏ n, W n (s n) (r n) else 0 := by
  classical
  rw [gridMatrix_permanent_aux h hh, coeff_ones_prod]
  rw [← (Equiv.arrowProdEquivProdArrow N (fun _ => Bool) (fun _ => Bool × Bool)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← (Equiv.arrowProdEquivProdArrow N (fun _ => Bool) (fun _ => Bool)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single (fun n => s (pick ρ r n))]
  · have key := slot_bijective σ ρ s r (fun n => s (pick ρ r n))
    simp only [implies_true, and_true] at key
    by_cases hc : (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n)
    · rw [ite_eq_left hc]
      refine (ite_eq_left (key.2 hc)).trans ?_
      have e1 : ∀ n, wt ρ W n (s n, r n, s (pick ρ r n)) =
          (if r n then W n (s n) (r n) else 1) *
            (if r (ρ n) then 1 else W (ρ n) (s (ρ n)) (r (ρ n))) := by
        intro n
        rw [hc.2 n]
        rcases hr : r n <;> simp [wt, pick, hr]
      refine (Finset.prod_congr rfl fun n _ => e1 n).trans ?_
      rw [Finset.prod_mul_distrib, Equiv.prod_comp ρ (fun n => if r n then 1 else W n (s n) (r n)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun n _ => ?_
      split_ifs <;> simp
    · rw [ite_eq_right hc]
      exact ite_eq_right fun hb => hc (key.1 hb)
  · exact fun q _ hq => ite_eq_right fun hb =>
      hq (funext fun n => (((slot_bijective σ ρ s r q).1 hb).2.2 n).symm)
  · exact fun hc => absurd (mem_univ _) hc

end Grid

section Fibres

open Finset MvPolynomial

section Fibres

variable {N V : Type*} [Fintype N] [DecidableEq N]

omit [Fintype N] [DecidableEq N] in
/-- A permutation whose cycles are the fibres of a map. -/
private theorem exists_perm_fibres [Finite N] (v : N → V) :
    ∃ σ : Equiv.Perm N, (∀ n, v (σ n) = v n) ∧
      ∀ s : N → Bool, (∀ n, s (σ n) = s n) → ∀ n m, v n = v m → s n = s m := by
  classical
  have := Fintype.ofFinite N
  have h (y : V) : ∃ f : Equiv.Perm {n // v n = y},
      f.IsCycleOn ((univ : Finset {n // v n = y}) : Set _) :=
    (Finset.exists_cycleOn univ).imp fun f hf => hf.1
  choose f hf using h
  let e := Equiv.sigmaFiberEquiv v
  let σ : Equiv.Perm N := (e.symm.trans (Equiv.sigmaCongrRight f)).trans e
  have hσ : ∀ n, σ n = (f (v n) ⟨n, rfl⟩).val := fun n => rfl
  refine ⟨σ, fun n => ?_, fun s hs n m e => ?_⟩
  · rw [hσ]
    exact (f (v n) ⟨n, rfl⟩).property
  · have h1 : ∀ y, ∀ x : {n // v n = y}, s (f y x).val = s x.val := by
      rintro y ⟨x, rfl⟩
      rw [← hσ]
      exact hs x
    obtain ⟨i, -, hi⟩ := (hf (v m)).exists_pow_eq (mem_univ ⟨n, e⟩) (mem_univ ⟨m, rfl⟩)
    have h2 : ∀ i : ℕ, s ((f (v m) ^ i) ⟨n, e⟩).val = s n := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, h1, ih]
    rw [← h2 i, hi]

variable {R : Type*} [CommRing R]

open scoped Classical in
/-- A sum over the functions that are constant on the fibres. -/
private theorem sum_invariant [Fintype V] [DecidableEq V] {v : N → V} (hv : Function.Surjective v)
    {σ : Equiv.Perm N}
    (h1 : ∀ n, v (σ n) = v n)
    (h2 : ∀ s : N → Bool, (∀ n, s (σ n) = s n) → ∀ n m, v n = v m → s n = s m)
    (Φ : (N → Bool) → R) :
    ∑ s : N → Bool, (if ∀ n, s (σ n) = s n then Φ s else 0) =
      ∑ x : V → Bool, Φ fun n => x (v n) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun x _ n => x (v n)) ?_ ?_ ?_ ?_
  · intro x _
    simp [h1]
  · intro x _ y _ e
    exact hv.injective_comp_right e
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    refine ⟨fun y => s (Function.surjInv hv y), mem_univ _, ?_⟩
    funext n
    exact h2 s hs _ _ (Function.surjInv_eq hv _)
  · intros
    rfl

/-- A sum over two families of bits is a permanent. -/
private theorem exists_grid {K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
    (v : N → V) (w : N → K)
    (hv : Function.Surjective v) (hw : Function.Surjective w) :
    ∃ σ ρ : Equiv.Perm N, (∀ n, w (ρ n) = w n) ∧
      ∀ (h : R) (_ : h * 2 = 1) (W : N → Bool → Bool → R),
      (gridMatrix h σ ρ W).permanent =
        ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  obtain ⟨σ, s1, s2⟩ := exists_perm_fibres v
  obtain ⟨ρ, r1, r2⟩ := exists_perm_fibres w
  refine ⟨σ, ρ, r1, fun h hh W => ?_⟩
  rw [gridMatrix_permanent h hh]
  refine Eq.trans ?_ (sum_invariant hv s1 s2 fun s => ∑ r : K → Bool, ∏ n, W n (s n) (r (w n)))
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : ∀ n, s (σ n) = s n
  · rw [ite_eq_left hs]
    refine Eq.trans ?_ (sum_invariant hw r1 r2 fun r => ∏ n, W n (s n) (r n))
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [hs]
  · rw [ite_eq_right hs]
    exact Finset.sum_eq_zero fun r _ => ite_eq_right fun hc => hs hc.1

end Fibres

end Fibres

/-- A square matrix sits in every larger one with the same permanent, the new entries being `0`
and `1`. -/
private theorem exists_permanent_fin {R C : Type*} [CommRing R] [Fintype C] [DecidableEq C]
    (M : Matrix C C R) {S : ℕ} (hS : Fintype.card C ≤ S) :
    ∃ M' : Matrix (Fin S) (Fin S) R, M'.permanent = M.permanent ∧
      ∀ i j, (M' i j = 0 ∨ M' i j = 1) ∨ ∃ c d, M' i j = M c d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hS
  let e : Fin (Fintype.card C + k) ≃ C ⊕ Fin k :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Fintype.equivFin C).symm (Equiv.refl _))
  refine ⟨(fromBlocks M 0 0 (1 : Matrix (Fin k) (Fin k) R)).submatrix e e, ?_, fun i j => ?_⟩
  · rw [permanent_submatrix_equiv, permanent_fromBlocks_zero₂₁, permanent_one, mul_one]
  · rw [submatrix_apply]
    rcases e i with c | a <;> rcases e j with d | b
    · exact Or.inr ⟨c, d, rfl⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inl rfl)
    · rw [fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl rfl)

/-- **Grid sums are permanents** [Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026],
Proposition prop:grid. Let `R` be a commutative ring in which `2` has an inverse `h`, let
`v : N → V` and `w : N → K` be surjections of finite types, and let `W n x r ∈ R`. Then the grid
sum `∑ x, ∑ r, ∏ n, W n (x (v n)) (r (w n))` is the permanent of an `S × S` matrix, for every
`S ≥ 3 * |N|`, whose entries are `0`, `±1`, `±h`, or sums of values `W n x r` with one value of
`w n`. -/
theorem exists_permanent_eq_gridSum {R : Type*} [CommRing R] (h : R) (hh : h * 2 = 1)
    {N V K : Type*} [Fintype N] [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
    (v : N → V) (w : N → K) (hv : Function.Surjective v)
    (hw : Function.Surjective w) (W : N → Bool → Bool → R) {S : ℕ} (hS : 3 * Fintype.card N ≤ S) :
    ∃ M : Matrix (Fin S) (Fin S) R,
      (∀ i j, M i j ∈ ({0, 1, -1, h, -h} : Set R) ∨
        ∃ k, M i j ∈ AddSubmonoid.closure {y | ∃ n x r, w n = k ∧ y = W n x r}) ∧
      M.permanent = ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  obtain ⟨σ, ρ, hρ, H⟩ := exists_grid (R := R) v w hv hw
  have hcard : Fintype.card (N × Option Bool) ≤ S := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_bool]
    omega
  obtain ⟨M, hM, hent⟩ := exists_permanent_fin (gridMatrix h σ ρ W) hcard
  refine ⟨M, fun i j => ?_, hM.trans (H h hh W)⟩
  rcases hent i j with (h0 | h1) | ⟨⟨n, q⟩, d, he⟩
  · exact Or.inl (by simp [h0])
  · exact Or.inl (by simp [h1])
  rw [he]
  have hh2 : h + h = 1 := by rw [← mul_two]; exact hh
  obtain ⟨n', q'⟩ := d
  rcases q with _ | _ | _
  pick_goal 2
  · refine Or.inr ⟨w n, ?_⟩
    have mem (m : N) (c₀ : N × Option Bool) (x r : Bool) (hm : w m = w n) :
        ind c₀ (W m x r) (n', q') ∈
          AddSubmonoid.closure {y : R | ∃ m x r, w m = w n ∧ y = W m x r} := by
      unfold ind
      split_ifs
      · exact AddSubmonoid.subset_closure ⟨m, x, r, hm, rfl⟩
      · exact zero_mem _
    exact add_mem (add_mem (add_mem (mem n _ _ _ rfl) (mem n _ _ _ rfl)) (mem _ _ _ _ (hρ n)))
      (mem _ _ _ _ (hρ n))
  all_goals
    left
    rcases q' with _ | _ | _ <;>
      simp only [gridMatrix, ind, Prod.mk.injEq, reduceCtorEq, Option.some.injEq,
        Bool.false_eq_true, Bool.true_eq_false, and_true, and_false, ite_false, add_zero, zero_add,
        sub_zero] <;> split_ifs <;> simp [hh2]

end Matrix
