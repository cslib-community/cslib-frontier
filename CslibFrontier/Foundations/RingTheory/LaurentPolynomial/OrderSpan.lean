/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate (Mathlib, beside Mathlib/Algebra/Polynomial/Laurent.lean)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Orders, spans and rescaling of Laurent polynomials

For a Laurent polynomial `P : E[T;T⁻¹]` over a commutative `A`-algebra `E`:

* `LaurentPolynomial.OrderGE r P`: `P` has no terms below `T ^ r`;
* `LaurentPolynomial.Span n P`: every exponent of `P` has absolute value at most `n`;
* `LaurentPolynomial.Thin Δ P`: every power `P ^ k` has at most `2 k Δ + 1` terms;
* `LaurentPolynomial.rescale A r`: the `A`-algebra map `T ↦ T ^ r`.

Orders add under products and survive sums, spans add under products and scale under powers and
rescaling, and rescaling raises the order of a polynomial without terms below `T`. These are used
for approximate computation, where the constants are Laurent polynomials in `ε = T`, in
*VP ≠ VNP over every field* [AnthropicVPVNP2026].

## Main definitions

* `LaurentPolynomial.OrderGE`, `LaurentPolynomial.Span`, `LaurentPolynomial.Thin`,
  `LaurentPolynomial.rescale`.

## Main results

* `LaurentPolynomial.OrderGE.mul`, `OrderGE.prod_sub`, `OrderGE.rescale`.
* `LaurentPolynomial.Span.mul`, `Span.pow`, `Span.rescale`, `Span.thin`,
  `LaurentPolynomial.exists_span`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix N of the paper; module `NS1.ApproxOrd`
-/

public section

namespace LaurentPolynomial

variable {A : Type} [CommRing A] {E : Type} [CommRing E] [Algebra A E]

/-- All coefficients of exponents below `r` are 0: the polynomial lies in ε^r E[ε]. -/
@[expose] def OrderGE (r : ℤ) (P : E[T;T⁻¹]) : Prop := ∀ i < r, P.coeff i = 0

/-- All exponents that occur lie between `-n` and `n`. -/
@[expose] def Span (n : ℕ) (P : E[T;T⁻¹]) : Prop := ∀ i, P.coeff i ≠ 0 → i.natAbs ≤ n

theorem coeff_algebraMap (a : A) (i : ℤ) :
    (algebraMap A E[T;T⁻¹] a).coeff i = if i = 0 then algebraMap A E a else 0 := by
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

private theorem exists_coeff_mul_ne_zero {P Q : E[T;T⁻¹]} {i : ℤ} (h : (P * Q).coeff i ≠ 0) :
    ∃ a b, P.coeff a ≠ 0 ∧ Q.coeff b ≠ 0 ∧ a + b = i := by
  classical
  rw [AddMonoidAlgebra.coeff_mul] at h
  obtain ⟨a, ha, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, hb, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  refine ⟨a, b, Finsupp.mem_support_iff.1 ha, Finsupp.mem_support_iff.1 hb, ?_⟩
  by_contra hne
  exact h2 (ite_eq_right hne)

theorem OrderGE.zero (r : ℤ) : OrderGE r (0 : E[T;T⁻¹]) := fun i _ => by simp

theorem OrderGE.mono {r s : ℤ} {P : E[T;T⁻¹]} (h : OrderGE r P) (hs : s ≤ r) : OrderGE s P :=
  fun i hi => h i (lt_of_lt_of_le hi hs)

theorem OrderGE.add {r : ℤ} {P Q : E[T;T⁻¹]} (h : OrderGE r P)
    (h' : OrderGE r Q) : OrderGE r (P + Q) :=
  fun i hi => by simp [h i hi, h' i hi]

theorem OrderGE.mul {r s : ℤ} {P Q : E[T;T⁻¹]} (h : OrderGE r P)
    (h' : OrderGE s Q) : OrderGE (r + s)
    (P * Q) := by
  intro i hi
  by_contra hne
  obtain ⟨a, b, ha, hb, hab⟩ := exists_coeff_mul_ne_zero hne
  have h1 : r ≤ a := by
    by_contra h1
    exact ha (h a (by omega))
  have h2 : s ≤ b := by
    by_contra h2
    exact hb (h' b (by omega))
  omega

theorem OrderGE.list_sum {r : ℤ} {l : List E[T;T⁻¹]} (h : ∀ P ∈ l, OrderGE r P) : OrderGE r
    l.sum := by
  induction l with
  | nil => simpa using OrderGE.zero r
  | cons P l ih =>
    rw [List.sum_cons]
    exact (h P List.mem_cons_self).add (ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))

theorem OrderGE.of_algebraMap (a : A) : OrderGE 0 (algebraMap A E[T;T⁻¹] a) := fun i hi => by
  rw [coeff_algebraMap, ite_eq_right hi.ne]

/-- A product of approximations approximates the product. -/
theorem OrderGE.prod_sub {β : Type*} {r : ℤ} (hr : 0 ≤ r) (l : List β) (f : β → E[T;T⁻¹])
    (g : β → A)
    (h : ∀ y ∈ l, OrderGE r (f y - algebraMap A E[T;T⁻¹] (g y))) :
    OrderGE r ((l.map f).prod - algebraMap A E[T;T⁻¹] (l.map g).prod) := by
  induction l with
  | nil => simpa using OrderGE.zero r
  | cons y l ih =>
    have h1 := h y List.mem_cons_self
    have h2 := ih fun z hz => h z (List.mem_cons_of_mem _ hz)
    obtain ⟨a, ha⟩ : ∃ a, a = algebraMap A E[T;T⁻¹] (g y) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = algebraMap A E[T;T⁻¹] (l.map g).prod := ⟨_, rfl⟩
    rw [← ha] at h1
    rw [← hb] at h2
    have e : ((y :: l).map f).prod - algebraMap A E[T;T⁻¹] ((y :: l).map g).prod =
        (f y - a) * ((l.map f).prod - b) + ((f y - a) * b + a * ((l.map f).prod - b)) := by
      simp only [List.map_cons, List.prod_cons, map_mul, ← ha, ← hb]
      ring
    rw [e]
    refine ((h1.mul h2).mono (by omega)).add ((?_ : OrderGE r _).add ?_)
    · exact (h1.mul (hb ▸ OrderGE.of_algebraMap (E := E) ((l.map g).prod))).mono (by omega)
    · exact ((ha ▸ OrderGE.of_algebraMap (E := E) (g y) : OrderGE 0 a).mul h2).mono (by omega)

theorem Span.mono {n m : ℕ} {P : E[T;T⁻¹]} (h : Span n P) (hm : n ≤ m) : Span m P :=
    fun i hi => (h i hi).trans hm

theorem Span.orderGE {n : ℕ} {P : E[T;T⁻¹]} (h : Span n P) : OrderGE (-(n : ℤ)) P := by
  intro i hi
  by_contra hne
  have := h i hne
  omega

theorem Span.zero (n : ℕ) : Span n (0 : E[T;T⁻¹]) := fun i hi => absurd (by simp) hi

theorem Span.of_algebraMap (a : A) (n : ℕ) : Span n (algebraMap A E[T;T⁻¹] a) := fun i hi => by
  rw [coeff_algebraMap] at hi
  by_cases h : i = 0
  · simp [h]
  · exact absurd (ite_eq_right h) hi

theorem Span.one (n : ℕ) : Span n (1 : E[T;T⁻¹]) := by
  have := Span.of_algebraMap (E := E) (1 : E) n
  rwa [map_one] at this

theorem Span.add {n : ℕ} {P Q : E[T;T⁻¹]} (h : Span n P) (h' : Span n Q) : Span n (P + Q) := by
  intro i hi
  by_cases h1 : P.coeff i = 0
  · exact h' i (by simpa [h1] using hi)
  · exact h i h1

theorem Span.mul {n m : ℕ} {P Q : E[T;T⁻¹]} (h : Span n P) (h' : Span m Q) : Span (n + m)
    (P * Q) := by
  intro i hi
  obtain ⟨a, b, ha, hb, hab⟩ := exists_coeff_mul_ne_zero hi
  have := h a ha
  have := h' b hb
  omega

theorem Span.pow {n : ℕ} {P : E[T;T⁻¹]} (h : Span n P) (k : ℕ) : Span (k * n) (P ^ k) := by
  induction k with
  | zero => simpa using Span.one (E := E) 0
  | succ k ih =>
    rw [pow_succ, add_mul, one_mul]
    exact ih.mul h

private theorem Span.card_support {n : ℕ} {P : E[T;T⁻¹]} (h : Span n P) : P.coeff.support.card ≤
    2 * n +
    1 := by
  refine (Finset.card_le_card (t := Finset.Icc (-(n : ℤ)) n) fun i hi => ?_).trans ?_
  · have := h i (Finsupp.mem_support_iff.1 hi)
    rw [Finset.mem_Icc]
    omega
  · rw [Int.card_Icc]
    omega

/-- ε ↦ ε^r. -/
@[expose] noncomputable def rescale (A : Type)
    [CommRing A] {E : Type} [CommRing E] [Algebra A E] (r : ℕ) :
    E[T;T⁻¹] →ₐ[A] E[T;T⁻¹] :=
  AddMonoidAlgebra.mapDomainAlgHom A E (AddMonoidHom.mulLeft (r : ℤ))

private theorem coeff_rescale_ne_zero {r : ℕ} {P : E[T;T⁻¹]} {i : ℤ}
    (h : (rescale A r P).coeff i ≠ 0) :
    ∃ j, P.coeff j ≠ 0 ∧ i = r * j := by
  classical
  have h1 : i ∈ (Finsupp.mapDomain (fun j : ℤ => (r : ℤ) * j) P.coeff).support :=
      Finsupp.mem_support_iff.2 h
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h1)
  exact ⟨j, Finsupp.mem_support_iff.1 hj, rfl⟩

theorem OrderGE.rescale {r : ℕ} {P : E[T;T⁻¹]} (h : OrderGE 1 P) : OrderGE (r : ℤ)
    (rescale A r P) := by
  intro i hi
  by_contra hne
  obtain ⟨j, hj, rfl⟩ := coeff_rescale_ne_zero hne
  have h1 : 1 ≤ j := by
    by_contra h1
    exact hj (h j (by omega))
  nlinarith

theorem Span.rescale {n : ℕ} {P : E[T;T⁻¹]} (h : Span n P) (r : ℕ) : Span (r * n)
    (rescale A r P) := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := coeff_rescale_ne_zero hi
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (h j hj)

private theorem card_support_rescale (r : ℕ) (P : E[T;T⁻¹]) :
    (rescale A r P).coeff.support.card ≤ P.coeff.support.card := by
  classical
  refine (Finset.card_le_card ?_).trans (Finset.card_image_le (f := fun j : ℤ => (r : ℤ) * j))
  intro i hi
  obtain ⟨j, hj, rfl⟩ := coeff_rescale_ne_zero (Finsupp.mem_support_iff.1 hi)
  exact Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hj)

/-- The powers of `c` have few terms, as few as those of a polynomial of span `Δ`. -/
@[expose] def Thin (Δ : ℕ) (c : E[T;T⁻¹]) : Prop := ∀ n,
    (c ^ n).coeff.support.card ≤ 2 * (n * Δ) + 1

theorem Span.thin {Δ : ℕ} {P : E[T;T⁻¹]} (h : Span Δ P) : Thin Δ P :=
    fun n => (h.pow n).card_support

theorem Thin.rescale {Δ : ℕ} {P : E[T;T⁻¹]} (h : Thin Δ P) (r : ℕ) : Thin Δ (rescale A r P) :=
    fun n => by
  rw [← map_pow]
  exact (card_support_rescale r _).trans (h n)

theorem exists_span (P : E[T;T⁻¹]) : ∃ n, Span n P :=
  ⟨P.coeff.support.sup Int.natAbs, fun _ hi => Finset.le_sup (Finsupp.mem_support_iff.2 hi)⟩

end LaurentPolynomial
