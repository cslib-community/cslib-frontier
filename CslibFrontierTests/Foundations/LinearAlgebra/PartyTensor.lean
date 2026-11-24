/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Unit
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Tests for tensors over parties, upper functionals and spectral points

The structures `Cslib.PartyTensor.UpperFunctional` and `Cslib.PartyTensor.SpectralPoint` bundle
several conditions. The *support point*, `1` at a tensor with a nonzero entry and `0` at the zero
tensor, is a spectral point over every field (an example of Definition A.1 of
[AnthropicVPVNP2026]), so the bundle is satisfiable; the lemmas of the library then give
`1 ≤ F (unit K I n) ≤ n` for it. A smaller unit tensor is a restriction of a larger one, and
a wire of dimension one is equivalent to `1`.
-/

public section

namespace Cslib.PartyTensorTests

open Cslib PartyTensor Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

private theorem entry_eq_zero_of_coveredBy {κ : Type} [Fintype κ] {s : PartyTensor K I}
    {b : κ → PartyTensor K I} (h : s.CoveredBy b) (hb : ∀ k y, (b k).entry y = 0) (x) :
    s.entry x = 0 := by
  obtain ⟨L, hL⟩ := h
  rw [hL x]
  exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun y _ => by simp [hb k y]

open Classical in
/-- The support point: `1` at a tensor with a nonzero entry, `0` at the zero tensor. -/
noncomputable def supportPoint : SpectralPoint K I where
  toFun t := if ∃ x, t.entry x ≠ 0 then 1 else 0
  nonneg t := by split_ifs <;> norm_num
  map_one := ite_eq_left ⟨fun _ => (), one_ne_zero⟩
  map_mul s t := by
    have key : (∃ z, (s * t).entry z ≠ 0) ↔ (∃ x, s.entry x ≠ 0) ∧ ∃ y, t.entry y ≠ 0 := by
      constructor
      · rintro ⟨z, hz⟩
        rw [mul_entry] at hz
        exact ⟨⟨_, left_ne_zero_of_mul hz⟩, _, right_ne_zero_of_mul hz⟩
      · rintro ⟨⟨x, hx⟩, y, hy⟩
        exact ⟨fun p => (x p, y p), mul_ne_zero hx hy⟩
    by_cases hs : ∃ x, s.entry x ≠ 0 <;> by_cases ht : ∃ y, t.entry y ≠ 0 <;> simp [key, hs, ht]
  le_sum s b h := by
    have h0 : ∀ k, (0 : ℝ) ≤ if ∃ x, (b k).entry x ≠ 0 then 1 else 0 := fun k => by
      split_ifs <;> norm_num
    split_ifs with hs
    · by_contra hlt
      obtain ⟨x, hx⟩ := hs
      refine hx (entry_eq_zero_of_coveredBy h (fun k y => ?_) x)
      by_contra hy
      have := Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ k)
      rw [ite_eq_left ⟨y, hy⟩] at this
      linarith
    · exact Finset.sum_nonneg fun k _ => h0 k

/-- The support point of the unit tensor of size `n ≥ 1` on a nonempty set of parties is
between `1` and `n`. -/
example [Nonempty I] (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ (supportPoint (K := K) (I := I)).toUpperFunctional (push id (unit K I n)) ∧
      (supportPoint (K := K) (I := I)).toUpperFunctional (push id (unit K I n)) ≤ n :=
  ⟨UpperFunctional.one_le_unit _ id hn, UpperFunctional.unit_le _ id n⟩

/-- A smaller unit tensor is a restriction of a larger one. -/
example : unit K I 1 ≤ unit K I 2 := unit_le_unit (by norm_num)

/-- A wire of dimension one is equivalent to `1`. -/
example (p q : I) : AntisymmRel (· ≤ ·) (wire K 1 p q) 1 := antisymmRel_wire_one p q

end Cslib.PartyTensorTests
