/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Closeness through a linear map

Approximation arguments compare elements of a vector space `A` that carries no norm of its own
but a linear map `L : A → F` into a seminormed space. Two examples are the state seminorm of an
operator algebra, through the GNS map, and averaged norms of families of operators, through a
weighted map into `ℓ²`. The relation `a ≈[L | δ] b` (`Cslib.Close`) says `‖L (a - b)‖ ≤ δ`. Its
calculus is proved once for every `L`:

* errors add along chains (`Cslib.Close.trans`), with a `Trans` instance, so `calc` chains of
  approximations need no bookkeeping;
* sums, differences, negation and scalar multiples act on errors as expected
  (`Cslib.Close.add`, `Cslib.Close.sub`, `Cslib.Close.neg`, `Cslib.Close.smul`,
  `Cslib.Close.sum`).

Concrete relations, such as closeness in a state, are *named* definitions unfolding to `Close`.
They reuse this calculus through one-line wrappers and carry their own `Trans` instances. Under
binders (`∃ P, …`) the generic relation leaves the codomain of `L` to unification, which fails,
and a named definition fixes it.

## Main definitions

* `Cslib.Close`: `a ≈[L | δ] b`, that is `‖L (a - b)‖ ≤ δ`.

## Main results

* `Cslib.Close.trans`: errors add along chains.
* `Cslib.Close.sum`: errors add over finite sums.
-/

@[expose] public section

open Finset

namespace Cslib

variable {𝕜 A F : Type*} [NormedField 𝕜] [AddCommGroup A] [Module 𝕜 A] [SeminormedAddCommGroup F]
  [NormedSpace 𝕜 F]

/-- `a` and `b` are `δ`-close as seen through the linear map `L`: `‖L (a - b)‖ ≤ δ`. -/
def Close (L : A →ₗ[𝕜] F) (δ : ℝ) (a b : A) : Prop :=
  ‖L (a - b)‖ ≤ δ

@[inherit_doc] notation:50 a " ≈[" L " | " δ "] " b:50 => Close L δ a b

variable {L : A →ₗ[𝕜] F} {a b c a' b' : A} {δ δ' : ℝ}

theorem close_self (L : A →ₗ[𝕜] F) (a : A) : a ≈[L | 0] a := by
  simp [Close]

theorem Close.refl (hδ : 0 ≤ δ) (a : A) : a ≈[L | δ] a := by
  simpa [Close] using hδ

theorem Close.nonneg (h : a ≈[L | δ] b) : 0 ≤ δ :=
  (norm_nonneg _).trans h

theorem Close.symm (h : a ≈[L | δ] b) : b ≈[L | δ] a := by
  rwa [Close, ← neg_sub, map_neg, norm_neg]

theorem close_comm : (a ≈[L | δ] b) ↔ (b ≈[L | δ] a) :=
  ⟨Close.symm, Close.symm⟩

theorem Close.mono (h : a ≈[L | δ] b) (hδ : δ ≤ δ') : a ≈[L | δ'] b :=
  h.trans hδ

theorem close_of_eq (h : a = b) (hδ : 0 ≤ δ) : a ≈[L | δ] b :=
  h ▸ Close.refl hδ a

/-- Errors add along chains of approximations. -/
theorem Close.trans (h₁ : a ≈[L | δ] b) (h₂ : b ≈[L | δ'] c) : a ≈[L | δ + δ'] c := by
  rw [Close, ← sub_add_sub_cancel a b c, map_add]
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)

instance : @Trans A A A (Close L δ) (Close L δ') (Close L (δ + δ')) :=
  ⟨Close.trans⟩

theorem Close.add (h : a ≈[L | δ] b) (h' : a' ≈[L | δ'] b') : a + a' ≈[L | δ + δ'] b + b' := by
  rw [Close, add_sub_add_comm, map_add]
  exact (norm_add_le _ _).trans (add_le_add h h')

theorem Close.neg (h : a ≈[L | δ] b) : -a ≈[L | δ] -b := by
  rwa [Close, neg_sub_neg, ← neg_sub, map_neg, norm_neg]

theorem Close.sub (h : a ≈[L | δ] b) (h' : a' ≈[L | δ'] b') : a - a' ≈[L | δ + δ'] b - b' := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

theorem Close.smul (h : a ≈[L | δ] b) (z : 𝕜) : z • a ≈[L | ‖z‖ * δ] z • b := by
  rw [Close, ← smul_sub, map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg z)

/-- Errors add over finite sums. -/
theorem Close.sum {ι : Type*} (s : Finset ι) {f g : ι → A} {ε : ι → ℝ}
    (h : ∀ i ∈ s, f i ≈[L | ε i] g i) : ∑ i ∈ s, f i ≈[L | ∑ i ∈ s, ε i] ∑ i ∈ s, g i := by
  rw [Close, ← sum_sub_distrib, map_sum]
  exact (norm_sum_le _ _).trans (sum_le_sum h)

end Cslib
