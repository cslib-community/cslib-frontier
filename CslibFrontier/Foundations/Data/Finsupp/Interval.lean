/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, additions to `Mathlib/Data/Finsupp/Interval`)

public import CslibFrontier.Init
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Lower intervals of exponent vectors over a finite index type

`Finsupp.card_Iic` counts `Iic f` as a product over the support of `f`. Over a finite index type
the product can run over every index: an exponent vector `f : ι →₀ ℕ` has `∏ i, (1 + f i)`
exponent vectors below it (`Finsupp.card_Iic_eq_prod`), the number of monomials in the degree box
`∏ᵢ {0, …, f i}`.
-/

public section

namespace Finsupp

open Finset

/-- Over a finite index type, `f : ι →₀ ℕ` has `∏ i, (1 + f i)` exponent vectors below it. -/
theorem card_Iic_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι →₀ ℕ) :
    #(Iic f) = ∏ i, (1 + f i) := by
  rw [card_Iic]
  refine Finset.prod_subset (subset_univ _) (fun i _ hi => ?_) |>.trans
    (Finset.prod_congr rfl fun i _ => ?_)
  · simp [notMem_support_iff.1 hi]
  · simp [add_comm]

end Finsupp
