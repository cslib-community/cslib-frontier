/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, set-multilinear polynomials)

public import CslibFrontier.Foundations.Data.MvPolynomial.SetMultilinear

/-!
# Set-multilinear monomials for variables in a product

When the variables are pairs `(i, j) : Fin d × ι` and the block of a variable is its first
component, a choice of one variable from every block of `S` (`MvPolynomial.BlockChoice`) is a
family `y : Fin d → ι` restricted to `S` (`MvPolynomial.BlockChoice.ofProd`), and its monomial is
the product of the variables `(i, y i)` with `i ∈ S`.

## Main definitions

* `MvPolynomial.BlockChoice.ofProd`: the choice of the variables `(i, y i)`.

## Main results

* `MvPolynomial.BlockChoice.ofProd_injective`: on all blocks, the choice determines the family.
* `MvPolynomial.blockMonomial_ofProd`, `MvPolynomial.prod_X_eq_monomial_blockMonomial_ofProd`: the
  monomial of the choice of a family.
-/

@[expose] public section

namespace MvPolynomial

variable {K ι : Type*} {d : ℕ}

/-- For variables `Fin d × ι` in blocks by their first components, a family `y` chooses the
variable `(i, y i)` of the block `i`. -/
def BlockChoice.ofProd (S : Finset (Fin d)) (y : Fin d → ι) :
    BlockChoice (Prod.fst : Fin d × ι → Fin d) S :=
  fun i => ⟨(i, y i), rfl⟩

/-- On all blocks, the choice of a family determines the family. -/
theorem BlockChoice.ofProd_injective :
    Function.Injective (BlockChoice.ofProd (ι := ι) (Finset.univ : Finset (Fin d))) :=
  fun _ _ h => funext fun i =>
    congrArg (fun c => (c ⟨i, Finset.mem_univ i⟩ : Fin d × ι).2) h

/-- The monomial of the choice of a family has the variables `(i, y i)` with `i ∈ S`. -/
theorem blockMonomial_ofProd (S : Finset (Fin d)) (y : Fin d → ι) :
    blockMonomial Prod.fst S (BlockChoice.ofProd S y) = ∑ i ∈ S, Finsupp.single (i, y i) 1 :=
  Finset.sum_coe_sort S fun i => Finsupp.single (i, y i) 1

/-- The product of the variables `(i, y i)` with `i ∈ S` is the monomial of the choice of `y`. -/
theorem prod_X_eq_monomial_blockMonomial_ofProd [CommSemiring K] (S : Finset (Fin d))
    (y : Fin d → ι) :
    ∏ i ∈ S, (X (i, y i) : MvPolynomial (Fin d × ι) K) =
      monomial (blockMonomial Prod.fst S (BlockChoice.ofProd S y)) 1 := by
  rw [blockMonomial_ofProd, monomial_sum_one]
  rfl

end MvPolynomial
