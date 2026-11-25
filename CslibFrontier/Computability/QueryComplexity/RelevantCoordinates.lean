/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Cslib.Computability.QueryComplexity.Measures
public import CslibFrontier.Foundations.Data.BitString.LocalBoundary
public import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Maximum sensitivity bounds the number of relevant coordinates

The set of inputs sensitive to a relevant coordinate has local boundary at most twice the
maximum sensitivity. The cube-cardinality bound and double-counting sensitive incidences give
at most `s(f) * 4 ^ s(f)` relevant coordinates. Consequently, dependence on all `n` coordinates
implies `Nat.clog 2 n ≤ 3 * sensitivity f`, an explicit uniform logarithmic lower bound.
The measures are CSLib's native maximum sensitivity, not average sensitivity or Fourier degree.

## Main results

* `Cslib.BitString.card_relevant_le_sensitivity_mul_four_pow`: relevant-coordinate cardinality.
* `Cslib.BitString.clog_le_three_mul_sensitivity_of_depends_on_all`: the logarithmic corollary.

## References

* [AroraBarak07], Chapter 11 Exercise 1, printed page 218 / PDF page 234.
-/

public section

namespace Cslib.BitString
open Finset

private theorem flip_comm {n : ℕ} (x : BitString n) (i j : Fin n) :
    Function.update (Function.update x j (!x j)) i (!(Function.update x j (!x j)) i) =
      Function.update (Function.update x i (!x i)) j (!(Function.update x i (!x i)) j) := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · simp only [Function.update_of_ne hij, Function.update_of_ne hij.symm]
    exact Function.update_comm hij.symm _ _ _

private theorem sensitiveInputs_boundary {n : ℕ} (f : BooleanFunction n) (i : Fin n)
    (x : BitString n) (hx : IsSensitiveCoord f x i) :
    #{j : Fin n | ¬IsSensitiveCoord f (Function.update x j (!x j)) i} ≤ 2 * sensitivity f := by
  have hsub : ({j : Fin n | ¬IsSensitiveCoord f (Function.update x j (!x j)) i} :
      Finset (Fin n)) ⊆
      sensitiveCoords f x ∪ sensitiveCoords f (Function.update x i (!x i)) := fun j hj => by
    by_contra hn
    rw [Finset.mem_union, mem_sensitiveCoords, mem_sensitiveCoords, not_or] at hn
    have h0 : f (Function.update x j (!x j)) = f x := not_ne_iff.mp hn.1
    have h1 : f (Function.update (Function.update x i (!x i)) j
        (!(Function.update x i (!x i)) j)) = f (Function.update x i (!x i)) := not_ne_iff.mp hn.2
    have h2 := not_ne_iff.mp (Finset.mem_filter.mp hj).2
    exact hx (h1.symm.trans ((congrArg f (flip_comm x i j).symm).trans (h2.trans h0)))
  calc #{j : Fin n | ¬IsSensitiveCoord f (Function.update x j (!x j)) i}
      ≤ (sensitiveCoords f x ∪ sensitiveCoords f (Function.update x i (!x i))).card :=
        card_le_card hsub
    _ ≤ (sensitiveCoords f x).card + (sensitiveCoords f (Function.update x i (!x i))).card :=
        card_union_le _ _
    _ ≤ sensitivity f + sensitivity f := Nat.add_le_add (sensitivityAt_le_sensitivity f x)
        (sensitivityAt_le_sensitivity f (Function.update x i (!x i)))
    _ = 2 * sensitivity f := (Nat.two_mul _).symm

/-- A Boolean function has at most `s(f) * 4 ^ s(f)` relevant coordinates. -/
theorem card_relevant_le_sensitivity_mul_four_pow {n : ℕ} (f : BooleanFunction n) :
    #{i : Fin n | ∃ x, IsSensitiveCoord f x i} ≤ sensitivity f * 4 ^ sensitivity f := by
  classical
  let A : Fin n → Finset (BitString n) := fun i => univ.filter fun x => IsSensitiveCoord f x i
  let R : Finset (Fin n) := univ.filter fun i => ∃ x, IsSensitiveCoord f x i
  have hi (i : Fin n) (hi : i ∈ R) : 2 ^ n ≤ 2 ^ (2 * sensitivity f) * (A i).card := by
    obtain ⟨x, hx⟩ := (mem_filter.mp hi).2
    refine two_pow_le_two_pow_mul_card_of_boundary_bound (A i) (2 * sensitivity f)
      ⟨x, mem_filter.mpr ⟨mem_univ x, hx⟩⟩ fun x hx => ?_
    simpa only [A, mem_filter, mem_univ, true_and] using
      sensitiveInputs_boundary f i x (mem_filter.mp hx).2
  have hdouble : ∑ i, (A i).card = ∑ x : BitString n, sensitivityAt f x := by
    simp only [A, card_filter, sensitivityAt, sensitiveCoords]
    exact sum_comm
  have htotal : ∑ i ∈ R, (A i).card ≤ 2 ^ n * sensitivity f := by
    calc ∑ i ∈ R, (A i).card ≤ ∑ i, (A i).card :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
      _ ≤ ∑ _x : BitString n, sensitivity f :=
          hdouble ▸ sum_le_sum fun x _ => sensitivityAt_le_sensitivity f x
      _ = 2 ^ n * sensitivity f := by simp [BitString]
  have hproduct : R.card * 2 ^ n ≤ 2 ^ (2 * sensitivity f) * (2 ^ n * sensitivity f) := by
    calc R.card * 2 ^ n = ∑ _i ∈ R, 2 ^ n := by simp
      _ ≤ ∑ i ∈ R, 2 ^ (2 * sensitivity f) * (A i).card := sum_le_sum hi
      _ = 2 ^ (2 * sensitivity f) * ∑ i ∈ R, (A i).card := (mul_sum ..).symm
      _ ≤ _ := Nat.mul_le_mul_left _ htotal
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.pow_pos (by decide) : 0 < 2 ^ n)
  simpa only [show 4 = 2 ^ 2 from rfl, pow_mul, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hproduct

/-- Depending on every coordinate forces logarithmic maximum sensitivity: the ceiling of
`log₂ n` is at most three times the sensitivity, including the empty-coordinate case. -/
theorem clog_le_three_mul_sensitivity_of_depends_on_all {n : ℕ} (f : BooleanFunction n)
    (hdep : ∀ i : Fin n, ∃ x, IsSensitiveCoord f x i) :
    Nat.clog 2 n ≤ 3 * sensitivity f := by
  have hn : n ≤ sensitivity f * 4 ^ sensitivity f := by
    simpa [hdep] using card_relevant_le_sensitivity_mul_four_pow f
  refine Nat.clog_le_of_le_pow (hn.trans ?_)
  calc sensitivity f * 4 ^ sensitivity f ≤ 2 ^ sensitivity f * 4 ^ sensitivity f :=
        Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = 2 ^ (3 * sensitivity f) := by
        rw [show 4 = 2 ^ 2 from rfl, ← pow_mul, ← pow_add]
        exact congrArg (2 ^ ·) (by omega)

end Cslib.BitString
