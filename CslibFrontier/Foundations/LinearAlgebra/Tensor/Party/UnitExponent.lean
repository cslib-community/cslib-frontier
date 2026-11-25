/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.WireExponent
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Unit exponents of a spectral point

The unit exponent `F.unitExponent π` of a spectral point `F` is the exponent `g` of the unit
tensor with a leg at `π a` for every `a` (Lemma A.2 of [AnthropicVPVNP2026]). This file has the
simple facts on it that the convexity of hyperedges uses (module `Nc.Price.Hyper`): it depends only
on the set of parties that hold a leg, it is `0` when all legs are at one party and at most
the wire exponent when they are at two, moving the legs raises it at most by the wire exponents
along the moves, and it commutes with pull-backs.

## Main results

* `Cslib.PartyTensor.SpectralPoint.apply_push_unit_two`: the value at the unit tensor of size `2`.
* `Cslib.PartyTensor.SpectralPoint.unitExponent_congr_range`,
  `Cslib.PartyTensor.SpectralPoint.unitExponent_const`,
  `Cslib.PartyTensor.SpectralPoint.unitExponent_le_of_two`: the parties holding legs.
* `Cslib.PartyTensor.SpectralPoint.unitExponent_le_move`: moving legs.
* `Cslib.PartyTensor.SpectralPoint.pull_unitExponent`: pull-backs.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma A.2 (§A.2) and the proof of Lemma E.9 (hyperedges are convex); module `Nc.Price.Hyper`
-/

public section

namespace Cslib.PartyTensor.SpectralPoint

section CommSemiring

variable {K : Type} [CommSemiring K] {I J A B : Type} [Fintype I] [DecidableEq I] [Fintype J]
  [DecidableEq J] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (F : SpectralPoint K I)

/-- The unit exponent depends only on the set of parties that hold a leg. -/
theorem unitExponent_congr_range (π : A → I) (π' : B → I) (h : Set.range π = Set.range π') :
    F.unitExponent π = F.unitExponent π' := by
  rw [unitExponent, unitExponent, F.congr (antisymmRel_push_unit_congr π π' h 2)]

/-- The unit exponents of a pull-back are those of the images. -/
@[simp] theorem pull_unitExponent (f : J → I) (π : A → J) :
    (F.pull f).unitExponent π = F.unitExponent (f ∘ π) := by
  rw [unitExponent, unitExponent, pull_apply, F.congr (antisymmRel_push_push f π _)]

end CommSemiring

section Field

variable {K : Type} [Field K] {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
  (F : SpectralPoint K I)

/-- The value at the unit tensor of size `2` is `2` to the unit exponent. -/
theorem apply_push_unit_two [Nonempty I] (π : A → I) :
    F (push π (unit K A 2)) = 2 ^ F.unitExponent π := by
  exact_mod_cast F.apply_push_unit π (q := 2) (by norm_num)

/-- If all legs are at one party, the unit exponent is `0`. -/
theorem unitExponent_const (q : I) : F.unitExponent (fun _ : A => q) = 0 :=
  have : Nonempty I := ⟨q⟩
  le_antisymm (Real.logb_nonpos (by norm_num) (F.nonneg _)
    (F.toUpperFunctional.push_const_le q _)) (F.unitExponent_nonneg _)

/-- If all legs are at the parties `p` and `q`, the unit exponent is at most their wire
exponent. -/
theorem unitExponent_le_of_two (π : A → I) (p q : I) (h : ∀ a, π a = p ∨ π a = q) :
    F.unitExponent π ≤ F.wireExponent p q := by
  by_cases hp : ∀ a, π a = p
  · rw [show π = fun _ => p from funext hp, unitExponent_const]
    exact F.wireExponent_nonneg p q
  by_cases hq : ∀ a, π a = q
  · rw [show π = fun _ => q from funext hq, unitExponent_const]
    exact F.wireExponent_nonneg p q
  push Not at hp hq
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  refine (F.unitExponent_congr_range π ![p, q] ?_).le
  ext x
  simp only [Set.mem_range, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact h c
  · rintro (rfl | rfl)
    exacts [⟨b, (h b).resolve_right hb⟩, ⟨a, (h a).resolve_left ha⟩]

/-- Moving the leg `a` from `π' a` to `π a` raises the unit exponent at most by the sum of the
wire exponents along the moves. -/
theorem unitExponent_le_move [Nonempty I] (π π' : A → I) :
    F.unitExponent π ≤ F.unitExponent π' + ∑ a, F.wireExponent (π a) (π' a) := by
  have h := F.apply_push_le π π' (unit K A 2)
  have h1 (a : A) : (Fintype.card ((unit K A 2).Index a) : ℝ) = 2 := by
    change (Fintype.card (Fin 2) : ℝ) = 2
    simp
  simp only [h1] at h
  rw [apply_push_unit_two, apply_push_unit_two, ← Real.rpow_sum_of_pos (by norm_num),
    ← Real.rpow_add (by norm_num)] at h
  have h2 := (Real.rpow_le_rpow_left_iff (by norm_num)).1 h
  linarith

end Field

end Cslib.PartyTensor.SpectralPoint
