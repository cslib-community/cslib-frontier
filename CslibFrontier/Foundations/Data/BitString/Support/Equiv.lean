/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Equiv.Defs

/-!
# Equivalence between Boolean vectors and coordinate subsets

Every Boolean vector `x : ι → Bool` over a finite decidable index type `ι` corresponds to its
support `{i | x i = true} : Finset ι`, with inverse sending `S : Finset ι` to its indicator
`fun i => decide (i ∈ S)`.

## Main definitions

* `Cslib.BitString.supportEquiv`: the bijection `(ι → Bool) ≃ Finset ι` sending `x` to
  `{i | x i = true}`.

## Main results

* `Cslib.BitString.supportEquiv_apply`, `Cslib.BitString.mem_supportEquiv`,
  `Cslib.BitString.supportEquiv_symm_apply`: forward, membership, and inverse characterizations.
-/

@[expose] public section

namespace Cslib.BitString

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bijection between Boolean vectors `x : ι → Bool` and coordinate subsets `S : Finset ι`
sending `x` to its support `{i | x i = true}` and `S` to its indicator `i ↦ decide (i ∈ S)`. -/
def supportEquiv : (ι → Bool) ≃ Finset ι where
  toFun x := Finset.univ.filter (fun i => x i = true)
  invFun S i := decide (i ∈ S)
  left_inv x := by
    funext i
    simp
  right_inv S := by
    ext i
    simp

/-- `supportEquiv` sends `x` to its support `{i | x i = true}`. -/
@[simp] theorem supportEquiv_apply (x : ι → Bool) :
    supportEquiv x = Finset.univ.filter (fun i => x i = true) :=
  rfl

/-- Coordinate `i` belongs to `supportEquiv x` iff `x i = true`. -/
theorem mem_supportEquiv (x : ι → Bool) (i : ι) :
    i ∈ supportEquiv x ↔ x i = true := by
  simp

/-- `supportEquiv.symm` sends `S` to its indicator `i ↦ decide (i ∈ S)`. -/
@[simp] theorem supportEquiv_symm_apply (S : Finset ι) (i : ι) :
    supportEquiv.symm S i = decide (i ∈ S) :=
  rfl

end Cslib.BitString
