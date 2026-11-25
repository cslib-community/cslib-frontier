/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Parity

/-!
# Interpolating two table entries by a parity

The values of a Boolean table `f` with `f 0 = false` at any two points of the cube agree with
some parity. The zero point and repeated points impose the only consistency conditions on two
answers. The parity can be chosen on finitely many coordinates even when the coordinate type
is infinite. This elementary interpolation lemma is proved by choosing separating coordinates.

## Main results

* `Cslib.BitString.exists_parityOn_agrees_pair`: a normalized table agrees with a parity at two
  specified points.

## References

The interpolation argument in this module is elementary and original to this formalization.
-/

public section

namespace Cslib.BitString

variable {ι : Type*}

private theorem exists_true_of_ne_zero {x : ι → Bool} (hx : x ≠ 0) : ∃ i, x i = true := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ false := by
    by_contra! h
    exact hx (funext h)
  exact ⟨i, Bool.eq_true_of_not_eq_false hi⟩

private theorem exists_parityOn_true_false {x y : ι → Bool} (hx : x ≠ 0) (hxy : x ≠ y) :
    ∃ S : Finset ι, parityOn S x = true ∧ parityOn S y = false := by
  classical
  obtain ⟨i, hi⟩ := exists_true_of_ne_zero hx
  cases hyi : y i
  · exact ⟨{i}, by simpa only [parityOn_singleton] using hi,
      by simpa only [parityOn_singleton] using hyi⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
  cases hxj : x j <;> cases hyj : y j
  · exact (hj (hxj.trans hyj.symm)).elim
  · have hij : i ≠ j := fun h => by subst h; simp [hi] at hxj
    exact ⟨{i, j}, by simp [parityOn_insert, hij, hi, hxj],
      by simp [parityOn_insert, hij, hyi, hyj]⟩
  · exact ⟨{j}, by simpa only [parityOn_singleton] using hxj,
      by simpa only [parityOn_singleton] using hyj⟩
  · exact (hj (hxj.trans hyj.symm)).elim

/-- Any two answers of a table that is false at zero extend to a parity. The two points may
coincide or be zero; no finiteness assumption on the coordinate type is needed. -/
theorem exists_parityOn_agrees_pair {f : (ι → Bool) → Bool} (hf : f 0 = false)
    (x y : ι → Bool) : ∃ S : Finset ι, parityOn S x = f x ∧ parityOn S y = f y := by
  cases hfx : f x <;> cases hfy : f y
  · exact ⟨∅, parityOn_empty x, parityOn_empty y⟩
  · obtain ⟨S, hSy, hSx⟩ := exists_parityOn_true_false (x := y) (y := x)
      (fun h => by simp [h, hf] at hfy) (fun h => by simp [h, hfx] at hfy)
    exact ⟨S, hSx, hSy⟩
  · exact exists_parityOn_true_false (x := x) (y := y)
      (fun h => by simp [h, hf] at hfx) (fun h => by simp [h, hfy] at hfx)
  · have hx : x ≠ 0 := fun h => by simp [h, hf] at hfx
    have hy : y ≠ 0 := fun h => by simp [h, hf] at hfy
    have hxy : x ≠ x + y := fun h => hy (add_left_cancel ((add_zero x).trans h)).symm
    obtain ⟨S, hSx, hSsum⟩ := exists_parityOn_true_false hx hxy
    refine ⟨S, hSx, ?_⟩
    have hadd := parityOn_add S x y
    rw [hSsum, hSx] at hadd
    simpa using hadd.symm

end Cslib.BitString
