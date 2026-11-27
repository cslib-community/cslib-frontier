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
* `MvPolynomial.coeff_mul_blockMonomial_ofProd`: the coefficient of a product of set-multilinear
  polynomials on a set of blocks and on its complement, at the monomial of a family.
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

/-- Restricting the choice of a family to fewer blocks gives the choice of the family there. -/
private theorem BlockChoice.restrict_ofProd {S T : Finset (Fin d)} (hTS : T ⊆ S) (y : Fin d → ι) :
    BlockChoice.restrict hTS (BlockChoice.ofProd S y) = BlockChoice.ofProd T y :=
  rfl

/-- The coefficient of the product of a set-multilinear polynomial on `S` and one on the
complement of `S`, at the monomial of a family `y` on all blocks, is the product of their
coefficients at the monomials of `y` on `S` and on the complement. -/
theorem coeff_mul_blockMonomial_ofProd [CommSemiring K] {S : Finset (Fin d)}
    {f g : MvPolynomial (Fin d × ι) K} (hf : IsSetMultilinear Prod.fst S f)
    (hg : IsSetMultilinear Prod.fst Sᶜ g) (y : Fin d → ι) :
    (f * g).coeff (blockMonomial Prod.fst Finset.univ (BlockChoice.ofProd Finset.univ y)) =
      f.coeff (blockMonomial Prod.fst S (BlockChoice.ofProd S y)) *
        g.coeff (blockMonomial Prod.fst Sᶜ (BlockChoice.ofProd Sᶜ y)) := by
  simpa only [BlockChoice.restrict_ofProd, blockMonomial_ofProd, Finset.inter_self,
    Finset.inter_comm Sᶜ S, Finset.inter_compl, Finset.sum_empty, add_zero, zero_add,
    Finset.sum_add_sum_compl] using coeff_mul_blockMonomial hf hg disjoint_compl_right
      Finset.subset_union_left Finset.subset_union_right (BlockChoice.ofProd S y)
      (BlockChoice.ofProd Sᶜ y)

end MvPolynomial
