/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Hom.Set

/-!
# The determinant of coincidences of two increasing tuples

For Proposition B.2 (prop:identity) of *VP ≠ VNP over every field* [AnthropicVPVNP2026]: for two
strictly increasing tuples `f, g` of natural numbers, the matrix `[f i = g j]` has determinant
`[f = g]` (`det_coinc`). The value of `Ψ` at `x = 1` reduces to it in the proof of
Proposition B.2.

## Main results

* `det_coinc`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition B.2 of the paper; module `Nc.Cross.One`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Matrix Finset

/-- The matrix of coincidences of two increasing tuples. -/
theorem det_coinc {R : Type*} [CommRing R] {μ : ℕ} (f g : Fin μ → ℕ) (hf : StrictMono f)
    (hg : StrictMono g) :
    (of fun i j => if f i = g j then (1 : R) else 0).det = if f = g then 1 else 0 := by
  by_cases h : f = g
  · subst h
    rw [ite_eq_left rfl]
    have : (of fun i j => if f i = f j then (1 : R) else 0) = (1 : Matrix (Fin μ) (Fin μ) R) := by
      ext i j
      simp [Matrix.one_apply, hf.injective.eq_iff]
    rw [this, det_one]
  · rw [ite_eq_right h]
    have hr : ¬ Set.range f ⊆ Set.range g := by
      intro hsub
      apply h
      have hfin : Set.range f = Set.range g := by
        have h1 : (Finset.univ.image f) ⊆ (Finset.univ.image g) := by
          intro n hn
          have : n ∈ Set.range g := hsub (by simpa using hn)
          simpa using this
        have h2 := Finset.eq_of_subset_of_card_le h1 (by
          rw [Finset.card_image_of_injective _ hf.injective,
              Finset.card_image_of_injective _ hg.injective])
        have h3 := congrArg (fun s : Finset ℕ => (s : Set ℕ)) h2
        simpa using h3
      exact StrictMono.range_inj_of_wellFoundedLT hf hg |>.1 hfin
    rw [Set.not_subset] at hr
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hr
    refine det_eq_zero_of_row_eq_zero i fun j => ?_
    simp only [of_apply]
    rw [ite_eq_right]
    intro hij
    exact hi ⟨j, hij.symm⟩

end Cslib.Circuits.Arithmetic.Separation.Curvature
