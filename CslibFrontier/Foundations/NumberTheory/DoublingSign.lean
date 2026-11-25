/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.DyadicCircle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Recovering a sign by the first flagged doubling

Successive doublings of a small nonzero rational eventually enter a prescribed magnitude
window. A sufficiently accurate approximation modulo one is then flagged, and its first
flag lies on the correct side of one half. The threshold, flag margin, error and final index
are parameters. In particular, a caller supplies the magnitude/product and precision bounds,
not a correctness assertion about the sign procedure.

This is the mathematical first-flag argument of Section 2 of
[OpenAI2026CountingHierarchy], generalized beyond its fixed constants. There is no
complexity membership claim.

## Main definitions

* `Cslib.CircleFlag`: the symmetric interval used to flag an approximation.
* `Cslib.FirstCircleFlag`: the first flagged index of a sequence.

## Main results

* `Cslib.firstCircleFlag_sign`: the side of one half at the first flag determines the sign.

## References

* [OpenAI2026CountingHierarchy], Section 2, proof of Sign from residues.
-/

public section

namespace Cslib

/-- An approximation is flagged when it stays at least `t` away from either endpoint. -/
@[expose] def CircleFlag (t w : ℚ) : Prop := t ≤ w ∧ w ≤ 1 - t

/-- Index `k` is flagged and every preceding index is unflagged. -/
@[expose] def FirstCircleFlag (t : ℚ) (w : ℕ → ℚ) (k : ℕ) : Prop :=
  CircleFlag t (w k) ∧ ∀ j < k, ¬ CircleFlag t (w j)

private lemma eq_zero_of_cast_lt (z : ℤ) (hlo : (-1 : ℚ) < z) (hhi : (z : ℚ) < 1) : z = 0 := by
  norm_cast at hlo hhi; omega

private lemma eq_one_of_cast_lt (z : ℤ) (hlo : (0 : ℚ) < z) (hhi : (z : ℚ) < 2) : z = 1 := by
  norm_cast at hlo hhi; omega

/-- No approximation of zero can be flagged when the error is below the flag margin. -/
theorem CircleClose.not_flag_zero {ε t w : ℚ} (h : CircleClose ε w 0)
    (hε : ε < t) : ¬ CircleFlag t w := by
  rintro hf
  obtain ⟨z, hz⟩ := h
  have := abs_lt.mp hz
  have : (0 : ℤ) < z := by exact_mod_cast (by linarith [hf.1] : (0 : ℚ) < z)
  have : z < (1 : ℤ) := by exact_mod_cast (by linarith [hf.2] : (z : ℚ) < 1)
  omega

/-- A flag excludes wrapping at zero; a small target has the sign indicated by the
side of one half. This also rules out a flag for a zero target. -/
theorem CircleClose.sign_of_flag {ε t b w q : ℚ} (h : CircleClose ε w q)
    (hf : CircleFlag t w) (hε : ε < t) (hb : b + ε ≤ 1 / 2) (hq : |q| < b) :
    (0 < q ↔ w < 1 / 2) ∧ (q < 0 ↔ 1 / 2 < w) := by
  have hnzero : q ≠ 0 := by
    intro hzero
    subst q
    exact h.not_flag_zero hε hf
  obtain ⟨z, hz⟩ := h
  have hz' := abs_lt.mp hz
  have hq' := abs_lt.mp hq
  obtain hpos | hzero | hneg := lt_trichotomy 0 q
  · have hzz : z = 0 := eq_zero_of_cast_lt z (by linarith [hf.1]) (by linarith [hf.2])
    subst z
    norm_num at hz'
    have hw : w < 1 / 2 := by linarith
    exact ⟨iff_of_true hpos hw, iff_of_false (by linarith) (by linarith)⟩
  · exact False.elim (hnzero hzero.symm)
  · have hzz : z = 1 := eq_one_of_cast_lt z (by linarith [hf.1]) (by linarith [hf.2])
    subst z
    norm_num at hz'
    have hw : 1 / 2 < w := by linarith
    exact ⟨iff_of_false (by linarith) (by linarith), iff_of_true hneg hw⟩

/-- A target whose magnitude is between `a` and `b` must be flagged, provided the
rounding error fits between that window and the endpoints. -/
theorem CircleClose.flag_of_magnitude {ε t a b w q : ℚ} (h : CircleClose ε w q)
    (hw : 0 ≤ w ∧ w < 1) (hlo : t + ε ≤ a) (hhi : b + ε ≤ 1 - t)
    (ht : 0 < t) (hqlo : a ≤ |q|) (hqhi : |q| < b) : CircleFlag t w := by
  obtain ⟨z, hz⟩ := h
  have hz' := abs_lt.mp hz
  have hq' := abs_lt.mp hqhi
  have hεpos : 0 < ε := lt_of_le_of_lt (abs_nonneg _) hz
  obtain hpos | hneg := le_total 0 q
  · rw [abs_of_nonneg hpos] at hqlo
    have hzz : z = 0 := eq_zero_of_cast_lt z (by linarith [hw.1]) (by linarith [hw.2])
    subst z
    constructor <;> norm_num at hz' <;> linarith
  · rw [abs_of_nonpos hneg] at hqlo
    have hzz : z = 1 := eq_one_of_cast_lt z (by linarith [hw.1]) (by linarith [hw.2])
    subst z
    constructor <;> norm_num at hz' <;> linarith

/-- At the first doubling reaching magnitude `a`, the magnitude is still below `2a`.
The final-index condition is a numerical bound, not a first-flag correctness premise. -/
theorem exists_first_doubling_magnitude {q a : ℚ} {K : ℕ}
    (hstart : |q| < a) (hend : a ≤ |(2 : ℚ) ^ K * q|) :
    ∃ k ≤ K, a ≤ |(2 : ℚ) ^ k * q| ∧
      ∀ j ≤ k, |(2 : ℚ) ^ j * q| < 2 * a := by
  induction K with
  | zero =>
    norm_num at hend
    linarith
  | succ K ih =>
    by_cases hK : a ≤ |(2 : ℚ) ^ K * q|
    · obtain ⟨k, hk, ha, hlt⟩ := ih hK
      exact ⟨k, by omega, ha, hlt⟩
    · refine ⟨K + 1, le_rfl, hend, fun j hj => ?_⟩
      have hq0 := abs_nonneg q
      have hlt : (2 : ℚ) ^ K * |q| < a := by
        simpa [abs_mul, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ K)] using not_le.mp hK
      rcases Nat.lt_or_eq_of_le hj with hj' | rfl
      · calc |(2 : ℚ) ^ j * q| = (2 : ℚ) ^ j * |q| := by
              rw [abs_mul, abs_of_pos (by positivity)]
          _ ≤ (2 : ℚ) ^ K * |q| :=
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hq0
          _ < 2 * a := by linarith
      · simpa [pow_succ', mul_assoc, abs_mul] using mul_lt_mul_of_pos_left hlt two_pos

/-- Mathematical correctness of first-flag sign recovery. Approximation, magnitude,
precision, flag margin and cutoff conditions are independent explicit inputs. -/
theorem firstCircleFlag_sign {q a ε t : ℚ} {K : ℕ} (w : ℕ → ℚ)
    (hstart : |q| < a) (hend : a ≤ |(2 : ℚ) ^ K * q|)
    (ht : 0 < t) (hε : ε < t) (hlo : t + ε ≤ a) (hhi : 2 * a + ε ≤ 1 / 2)
    (hw : ∀ k ≤ K, 0 ≤ w k ∧ w k < 1)
    (happrox : ∀ k ≤ K, CircleClose ε (w k) ((2 : ℚ) ^ k * q)) :
    ∃ k ≤ K, FirstCircleFlag t w k ∧
      (0 < q ↔ w k < 1 / 2) ∧ (q < 0 ↔ 1 / 2 < w k) := by
  classical
  obtain ⟨k₀, hk₀, hreach, hbound⟩ := exists_first_doubling_magnitude hstart hend
  obtain ⟨_, hz₀⟩ := happrox k₀ hk₀
  have := (abs_nonneg _).trans_lt hz₀
  have hflag : CircleFlag t (w k₀) :=
    (happrox k₀ hk₀).flag_of_magnitude (hw k₀ hk₀) hlo (by linarith) ht hreach (hbound k₀ le_rfl)
  have hex : ∃ k, CircleFlag t (w k) := ⟨k₀, hflag⟩
  let k := Nat.find hex
  have hk₀' : k ≤ k₀ := Nat.find_min' hex hflag
  have hk : k ≤ K := hk₀'.trans hk₀
  have hs := (happrox k hk).sign_of_flag (Nat.find_spec hex) hε hhi (hbound k hk₀')
  have hp : (0 : ℚ) < 2 ^ k := by positivity
  have hneg : (2 : ℚ) ^ k * q < (2 : ℚ) ^ k * 0 ↔ q < 0 := mul_lt_mul_iff_right₀ hp
  rw [mul_zero] at hneg
  exact ⟨k, hk, ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩,
    (mul_pos_iff_of_pos_left hp).symm.trans hs.1, hneg.symm.trans hs.2⟩

/-- The first flagged index is unique, without any approximation hypotheses. -/
theorem FirstCircleFlag.unique {t : ℚ} {w : ℕ → ℚ} {j k : ℕ}
    (hj : FirstCircleFlag t w j) (hk : FirstCircleFlag t w k) : j = k := by
  rcases lt_trichotomy j k with hlt | rfl | hgt
  · exact (hk.2 j hlt hj.1).elim
  · rfl
  · exact (hj.2 k hgt hk.1).elim

/-- Any first flagged index has the correct sign, under the numerical doubling bounds. -/
theorem FirstCircleFlag.sign {q a ε t : ℚ} {K k : ℕ} {w : ℕ → ℚ}
    (hf : FirstCircleFlag t w k)
    (hstart : |q| < a) (hend : a ≤ |(2 : ℚ) ^ K * q|)
    (ht : 0 < t) (hε : ε < t) (hlo : t + ε ≤ a) (hhi : 2 * a + ε ≤ 1 / 2)
    (hw : ∀ j ≤ K, 0 ≤ w j ∧ w j < 1)
    (happrox : ∀ j ≤ K, CircleClose ε (w j) ((2 : ℚ) ^ j * q)) :
    k ≤ K ∧ (0 < q ↔ w k < 1 / 2) ∧ (q < 0 ↔ 1 / 2 < w k) := by
  obtain ⟨j, hj, hf', hs⟩ := firstCircleFlag_sign w hstart hend ht hε hlo hhi hw happrox
  exact hf.unique hf' ▸ ⟨hj, hs⟩


end Cslib
