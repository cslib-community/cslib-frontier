/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import Mathlib.Data.Nat.Log
public import CslibFrontier.Computability.PolyTime.GaloisRingSeries

/-!
# Starting Newton inversion from a one-bit coefficient list

The initial inverse is computed entirely at precision one. Lifting those same coordinates
to the requested precision gives a seed with even defect. Logarithmically many ordinary
Newton rounds then give the inverse of every unit.
-/

@[expose] public section
namespace Cslib.GaloisRingArith

open Polynomial

/-- Coefficients reduced to the residue precision. -/
def residueCoeffs (x : List ℕ) : List ℕ := x.map (fun n => n % 2)

/-- Compute only a residue-field inverse for the initial Newton guess. -/
def residueSeed (fl x : List ℕ) : List ℕ := inv 1 fl (residueCoeffs x)

/-- The value of the low coordinate digits is the value of the original list at precision one. -/
theorem val_residueCoeffs (fl x : List ℕ) : val 1 fl (residueCoeffs x) = val 1 fl x := by
  apply Finset.sum_congr rfl
  intro i _
  rw [residueCoeffs, getD_map_of_map_zero (f := fun n => n % 2) rfl]
  exact congrArg (fun y : Ring 1 fl => y * AdjoinRoot.root _ ^ i)
    (natCast_mod_two_pow (p := 1) (fl := fl) (x.getD i 0))

/-- Reduction of a list value agrees with interpreting its coordinates at precision one. -/
theorem residue_val {p : ℕ} [NeZero p] (fl x : List ℕ) :
    GaloisRing.residue 2 p (monicOf fl) (val p fl x) = val 1 fl x := by
  simp only [val, map_sum, map_mul, map_natCast, map_pow, GaloisRing.residue_root]
  rfl

/-- Lifting the one-bit inverse into the full ring gives exactly the initial congruence
required by Newton iteration. -/
theorem exists_mul_residueSeed {p : ℕ} [NeZero p] (fl x : List ℕ)
    (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    (hx : IsUnit (val p fl x)) :
    ∃ z : Ring p fl, val p fl x * val p fl (residueSeed fl x) = 1 + 2 * z := by
  have hunit : IsUnit (val 1 fl (residueCoeffs x)) := by
    rw [val_residueCoeffs, ← residue_val (p := p)]
    exact hx.map _
  have hinv := val_mul_inv_of_isUnit hirr hunit
  rw [val_residueCoeffs] at hinv
  have hker : val p fl x * val p fl (residueSeed fl x) - 1 ∈
      RingHom.ker (GaloisRing.residue 2 p (monicOf fl)) := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, residue_val, residue_val]
    exact sub_eq_zero.mpr hinv
  rw [GaloisRing.ker_residue (monic_monicOf fl), Ideal.mem_span_singleton] at hker
  obtain ⟨z, hz⟩ := hker
  exact ⟨z, by rw [← sub_eq_iff_eq_add', hz]; push_cast; rfl⟩

/-- Run a chosen number of Newton steps from any supplied list. -/
def roundsFrom (p : ℕ) (fl x y : List ℕ) (k : ℕ) : List ℕ :=
  (List.range k).foldl (fun r _ => newton p fl x r) y

/-- A seed with even defect works independently of how it was obtained. -/
theorem val_roundsFrom {p : ℕ} (fl x y : List ℕ) {z : Ring p fl}
    (h : val p fl x * val p fl y = 1 + 2 * z) (k : ℕ) :
    ∃ z' : Ring p fl, val p fl x * val p fl (roundsFrom p fl x y k) = 1 + 2 ^ 2 ^ k * z' := by
  induction k with
  | zero => exact ⟨z, by simpa [roundsFrom] using h⟩
  | succ k ih =>
    obtain ⟨z', hz⟩ := ih
    refine ⟨-z' ^ 2, ?_⟩
    unfold roundsFrom at hz ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      val_mul_newton _ _ hz, show 2 ^ (k + 1) = 2 * 2 ^ k by ring]

/-- Actual inversion from one-bit data followed by ceiling-logarithmically many rounds. -/
theorem val_roundsFrom_residueSeed {p : ℕ} (fl x : List ℕ)
    (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2)))) (hx : IsUnit (val p fl x)) :
    val p fl x * val p fl (roundsFrom p fl x (residueSeed fl x) (Nat.clog 2 p)) = 1 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have := subsingleton_ring_zero (fl := fl)
    exact Subsingleton.elim _ _
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨z, hz⟩ := exists_mul_residueSeed fl x hirr hx
  obtain ⟨z', hz'⟩ := val_roundsFrom fl x _ hz (Nat.clog 2 p)
  have hbase : (2 : Ring p fl) ^ p = 0 := by
    exact_mod_cast natCast_two_pow (p := p) (fl := fl)
  rw [hz', pow_eq_zero_of_le (Nat.le_pow_clog (by decide) p) hbase, zero_mul, add_zero]

end Cslib.GaloisRingArith
