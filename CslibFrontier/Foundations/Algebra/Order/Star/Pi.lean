/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/Order/Star/Pi.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Star.Pi

/-!
# Self-adjoint decomposition in products

If every self-adjoint element of each factor is a difference of nonnegative elements, so is every
self-adjoint element of the product, componentwise (`Pi.instSelfAdjointDecompose`). Together with
Mathlib's `Pi.instStarOrderedRing`, this makes a finite product of algebras of observables an
algebra in which positive functionals have GNS spaces; a weighted sum of states on the factors is
a state on the product.
-/

public section

variable {ι : Type*} {A : ι → Type*} [Π i, AddGroup (A i)] [Π i, Star (A i)]
  [Π i, PartialOrder (A i)] [∀ i, SelfAdjointDecompose (A i)]

instance Pi.instSelfAdjointDecompose : SelfAdjointDecompose (Π i, A i) where
  exists_nonneg_sub_nonneg {a} ha := by
    have h i := (IsSelfAdjoint.apply ha i).exists_nonneg_sub_nonneg
    choose b c hb hc habc using h
    exact ⟨b, c, hb, hc, funext habc⟩
