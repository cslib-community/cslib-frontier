/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, the space of all partial derivatives)

public import CslibFrontier.Foundations.Data.MvPolynomial.PartialDerivatives

/-!
# The space of all partial derivatives of a polynomial

`MvPolynomial.iteratedPDerivSpan p` is the span of the iterated partial derivatives of `p` of
every order. It contains `p` and is closed under every partial derivative, so it is the least
subspace with these two properties.

## Main definitions

* `MvPolynomial.iteratedPDerivSpan`: the span of all iterated partial derivatives.

## Main results

* `MvPolynomial.self_mem_iteratedPDerivSpan`: the space contains the polynomial.
* `MvPolynomial.pderiv_mem_iteratedPDerivSpan`: the space is closed under partial derivatives.
-/

@[expose] public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The span of the iterated partial derivatives of a polynomial, of every order. -/
noncomputable def iteratedPDerivSpan (p : MvPolynomial σ R) : Submodule R (MvPolynomial σ R) :=
  Submodule.span R (Set.range fun x : Σ k, Fin k → σ => iteratedPDeriv x.2 p)

theorem iteratedPDeriv_mem_iteratedPDerivSpan {k : ℕ} (α : Fin k → σ) (p : MvPolynomial σ R) :
    iteratedPDeriv α p ∈ iteratedPDerivSpan p :=
  Submodule.subset_span ⟨⟨k, α⟩, rfl⟩

theorem self_mem_iteratedPDerivSpan (p : MvPolynomial σ R) : p ∈ iteratedPDerivSpan p :=
  iteratedPDeriv_mem_iteratedPDerivSpan Fin.elim0 p

/-- The space of all partial derivatives of a polynomial is closed under partial derivatives. -/
theorem pderiv_mem_iteratedPDerivSpan (i : σ) {p q : MvPolynomial σ R}
    (hq : q ∈ iteratedPDerivSpan p) : pderiv i q ∈ iteratedPDerivSpan p := by
  change q ∈ (iteratedPDerivSpan p).comap (pderiv i).toLinearMap
  refine Submodule.span_le.mpr ?_ hq
  rintro _ ⟨⟨k, α⟩, rfl⟩
  have h := iteratedPDeriv_mem_iteratedPDerivSpan (Fin.cons i α) p
  rwa [iteratedPDeriv_succ_apply, Fin.cons_zero, Fin.tail_cons] at h

end MvPolynomial
