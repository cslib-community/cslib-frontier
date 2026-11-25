/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.LaurentSeries

/-!
# Laurent polynomials as Laurent series

A Laurent polynomial in `T` is read as a Laurent series in `X` with the same coefficients
(`LaurentPolynomial.toLaurentSeries`), and every Laurent series agrees with a Laurent polynomial
below any given power (`LaurentSeries.exists_laurentPolynomial_coeff_eq`).

## Main definitions

* `LaurentPolynomial.toLaurentSeries`: the ring homomorphism `R[T;T⁻¹] →+* R⸨X⸩`.

## Main results

* `LaurentPolynomial.coeff_toLaurentSeries`: it keeps the coefficients.
* `LaurentSeries.exists_laurentPolynomial_coeff_eq`: truncation of a Laurent series.
-/

public section

open scoped LaurentPolynomial LaurentSeries

namespace LaurentPolynomial

variable {R : Type*} [CommSemiring R]

/-- A Laurent polynomial, read as a Laurent series with the same coefficients. -/
noncomputable def toLaurentSeries : R[T;T⁻¹] →+* R⸨X⸩ :=
  AddMonoidAlgebra.liftNCRingHom HahnSeries.C
    { toFun := fun n => HahnSeries.single n.toAdd 1
      map_one' := rfl
      map_mul' := fun a b => by rw [HahnSeries.single_mul_single, toAdd_mul, one_mul] }
    fun _ _ => Commute.all _ _

/-- The Laurent series of a Laurent polynomial has the same coefficients. -/
@[simp] theorem coeff_toLaurentSeries (x : R[T;T⁻¹]) (i : ℤ) :
    (toLaurentSeries x).coeff i = x.coeff i := by
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, HahnSeries.coeff_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | C_mul_T n a =>
    classical
    rw [← single_eq_C_mul_T, toLaurentSeries, AddMonoidAlgebra.liftNCRingHom_single,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, HahnSeries.C_apply,
      HahnSeries.coeff_single_zero_mul]
    change a * (HahnSeries.single n (1 : R)).coeff i = _
    rw [HahnSeries.coeff_single]
    by_cases h : i = n
    · simp [h]
    · simp [h, Ne.symm h]

end LaurentPolynomial

namespace LaurentSeries

variable {R : Type*} [CommRing R]

/-- Every Laurent series agrees below any given power with a Laurent polynomial. -/
theorem exists_laurentPolynomial_coeff_eq (c : R⸨X⸩) (n : ℤ) :
    ∃ c' : R[T;T⁻¹], ∀ i < n, (LaurentPolynomial.toLaurentSeries c').coeff i = c.coeff i := by
  classical
  refine ⟨.ofCoeff <| Finsupp.onFinset (Finset.Ico c.order n)
    (fun i => if i < n then c.coeff i else 0) fun i hi => ?_, fun i hi => ?_⟩
  · split_ifs at hi with h
    · exact Finset.mem_Ico.2 ⟨not_lt.1 fun h' => hi (HahnSeries.coeff_eq_zero_of_lt_order h'), h⟩
    · exact absurd rfl hi
  · rw [LaurentPolynomial.coeff_toLaurentSeries]
    simp [hi]

end LaurentSeries
