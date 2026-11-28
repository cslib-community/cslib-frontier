/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests of the frequency-domain gain checks)

import CslibFrontier.Algorithms.LinearAlgebra.FrequencyCertificate

/-! # Tests for kernel-checked gain bounds on frequency bands

A `module` client: every acceptance and rejection is closed by `decide +kernel`, and the real
statements come from the public soundness theorems.

* The RC low-pass `1 / (τ s + 1)` with `τ = 1/1000 s`: `|h| ≤ 1` on `[0, ∞)` (the bound is
  attained at `ω = 0`, a simple root of `Q - N` in `u = ω²`), the DC gain `1`, and the `-3 dB`
  point bracketed in `(997, 999) rad/s`: the gain is at least `-3 dB` for `|ω| ≤ 997` and at most
  `-3 dB` for `|ω| ≥ 999`. The true crossing is `ω = 1000 √(10^0.3 - 1) ≈ 997.6`.
* A unity-gain Sallen–Key low-pass with `R₁ = R₂ = 10 kΩ`, `C₁ = 20 nF` (feedback) and
  `C₂ = 10 nF` (ground): `H = ω₀² / (s² + 10⁴ s + ω₀²)` with `ω₀² = 5 · 10⁷`, a Butterworth
  response `|H|² = 1 / (1 + (ω / ω₀)⁴)`. Passband: between `-0.5 dB` and `0.0005 dB` for
  `|ω| ≤ 4000 rad/s`; stopband: at most `-40 dB` for `|ω| ≥ 75000 rad/s`. The `0 dB` bound itself
  is attained at `ω = 0` with a double root of `Q - N` in `u` and is rejected, as documented.
* Rejections: a passband or stopband that is too wide, a `dB` witness on the wrong side, and an
  undamped LC resonator (`ω = 1` is an eigenvalue) whose `Q` vanishes in the band.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.FrequencyCertificate

open Complex Cslib.LinearAlgebra

/-! ### RC low-pass -/

/-- `ẋ = -1000 x + 1000 u`, `y = x`: `h (s) = 1 / (s / 1000 + 1)`. -/
def rc : RatLTI 1 1 1 := ⟨[[-1000]], [[1000]], [[1]], [[0]]⟩

example : (rc.gainDen == [1000000, 1]) = true := by decide +kernel
example : (rc.gainNum 0 0 == [1000000]) = true := by decide +kernel

theorem rc_le_one : rc.gainLe 0 0 ⟨0, none⟩ (1 ^ 2) = true := by decide +kernel

/-- `|h (i ω)| ≤ 1` for every real `ω`. -/
example (ω : ℝ) : ‖rc.toSystem.transferFunction (ω * I) 0 0‖ ≤ 1 := by
  have e := rc.norm_le_of_gainLe (by norm_num) rc_le_one (ω := ω) ⟨by simp, by simp⟩
  push_cast at e
  exact e

theorem rc_pass : rc.gainGe 0 0 ⟨0, some 997⟩ (50119 / 100000) = true := by decide +kernel
theorem rc_pass_db : dbGe (50119 / 100000) (-3) = true := by decide +kernel
theorem rc_stop : rc.gainLe 0 0 ⟨999, none⟩ (50118 / 100000) = true := by decide +kernel
theorem rc_stop_db : dbLe (50118 / 100000) (-3) = true := by decide +kernel

/-- **The `-3 dB` point is bracketed:** at least `-3 dB` for `|ω| ≤ 997`, at most `-3 dB` for
`|ω| ≥ 999`. -/
example (ω₁ ω₂ : ℝ) (h₁ : |ω₁| ≤ 997) (h₂ : 999 ≤ |ω₂|) :
    (-3 : ℝ) ≤ 20 * Real.logb 10 ‖rc.toSystem.transferFunction (ω₁ * I) 0 0‖ ∧
      ‖rc.toSystem.transferFunction (ω₂ * I) 0 0‖ ≤ (10 : ℝ) ^ ((-3 : ℝ) / 20) := by
  have hm₁ : (⟨0, some 997⟩ : FreqBand).Mem ω₁ := ⟨by simp, by simpa using h₁⟩
  have hm₂ : (⟨999, none⟩ : FreqBand).Mem ω₂ := ⟨by simpa using h₂, by simp⟩
  have e₁ := rc.db_le_of_gainGe rc_pass rc_pass_db hm₁
  have e₂ := rc.norm_le_db_of_gainLe rc_stop rc_stop_db hm₂
  push_cast at e₁ e₂
  exact ⟨e₁, e₂⟩

/-- Too wide a passband, too wide a stopband and a `dB` witness on the wrong side are rejected. -/
example : rc.gainGe 0 0 ⟨0, some 999⟩ (50119 / 100000) = false := by decide +kernel
example : rc.gainLe 0 0 ⟨997, none⟩ (50118 / 100000) = false := by decide +kernel
example : dbLe (50119 / 100000) (-3) = false := by decide +kernel
example : dbGe (50118 / 100000) (-3) = false := by decide +kernel

theorem rc_dc : rc.dcCheck = true := by decide +kernel
example : (rc.dcGain == [[1]]) = true := by decide +kernel

/-- The DC gain `D - C A⁻¹ B = 1`, and `H 0 = 1`. -/
example : rc.toSystem.transferFunction 0 = Matrix.of ![![(1 : ℂ)]] := by
  rw [rc.transferFunction_zero_eq rc_dc, show rc.dcGain = [[1]] by decide +kernel]
  ext i j
  fin_cases i; fin_cases j
  simp [Mathlib.Tactic.Matrix.ofLists_apply, Mathlib.Tactic.Matrix.ofList_apply]

/-! ### Sallen–Key low-pass -/

/-- States `v_C1`, `v_C2`; output `v_C2`. -/
def sk : RatLTI 2 1 1 := ⟨[[-10000, -5000], [10000, 0]], [[5000], [0]], [[0, 1]], [[0]]⟩

example : (sk.charCoeffs == [50000000, 10000, 1]) = true := by decide +kernel
example : (sk.numCoeffs 0 0 == [50000000]) = true := by decide +kernel

theorem sk_pass_lo : sk.gainGe 0 0 ⟨0, some 4000⟩ (8913 / 10000) = true := by decide +kernel
theorem sk_pass_lo_db : dbGe (8913 / 10000) (-1 / 2) = true := by decide +kernel
theorem sk_pass_hi : sk.gainLe 0 0 ⟨0, some 4000⟩ (10001 / 10000) = true := by decide +kernel
theorem sk_pass_hi_db : dbLe (10001 / 10000) (1 / 2000) = true := by decide +kernel
theorem sk_stop : sk.gainLe 0 0 ⟨75000, none⟩ (1 / 10000) = true := by decide +kernel
theorem sk_stop_db : dbLe (1 / 10000) (-40) = true := by decide +kernel

/-- **Sallen–Key specification:** ripple within `[-0.5, 0.0005] dB` for `|ω| ≤ 4000 rad/s` and
attenuation of at least `40 dB` for `|ω| ≥ 75000 rad/s`. -/
example (ω₁ ω₂ : ℝ) (h₁ : |ω₁| ≤ 4000) (h₂ : 75000 ≤ |ω₂|) :
    (-1 / 2 : ℝ) ≤ 20 * Real.logb 10 ‖sk.toSystem.transferFunction (ω₁ * I) 0 0‖ ∧
      ‖sk.toSystem.transferFunction (ω₁ * I) 0 0‖ ≤ (10 : ℝ) ^ ((1 / 2000 : ℝ) / 20) ∧
      ‖sk.toSystem.transferFunction (ω₂ * I) 0 0‖ ≤ (10 : ℝ) ^ ((-40 : ℝ) / 20) := by
  have hm₁ : (⟨0, some 4000⟩ : FreqBand).Mem ω₁ := ⟨by simp, by simpa using h₁⟩
  have hm₂ : (⟨75000, none⟩ : FreqBand).Mem ω₂ := ⟨by simpa using h₂, by simp⟩
  have e₁ := sk.db_le_of_gainGe sk_pass_lo sk_pass_lo_db hm₁
  have e₂ := sk.norm_le_db_of_gainLe sk_pass_hi sk_pass_hi_db hm₁
  have e₃ := sk.norm_le_db_of_gainLe sk_stop sk_stop_db hm₂
  push_cast at e₁ e₂ e₃
  exact ⟨e₁, e₂, e₃⟩

/-- The exact `0 dB` bound is attained at `ω = 0`, where `Q - N = u²` has a double root: the
check rejects it, as documented for `Cslib.RealRoot.nonnegOn`. -/
example : sk.gainLe 0 0 ⟨0, some 4000⟩ 1 = false := by decide +kernel
/-- Too wide a passband and too wide a stopband are rejected. -/
example : sk.gainGe 0 0 ⟨0, some 5000⟩ (8913 / 10000) = false := by decide +kernel
example : sk.gainLe 0 0 ⟨60000, none⟩ (1 / 10000) = false := by decide +kernel
example : dbLe (1 / 10000) (-41) = false := by decide +kernel

/-! ### An undamped resonator -/

/-- `ẍ = -x`: the eigenvalues `± i` lie on the imaginary axis. -/
def lc : RatLTI 2 1 1 := ⟨[[0, 1], [-1, 0]], [[0], [1]], [[1, 0]], [[0]]⟩

/-- `Q` vanishes at `ω = 1`, so no gain bound is accepted on a band containing it, however large;
on a band away from it a bound is accepted. -/
example : lc.gainLe 0 0 ⟨0, some 2⟩ 1000000 = false := by decide +kernel
example : lc.gainLe 0 0 ⟨2, none⟩ (1 / 9) = true := by decide +kernel

end CslibFrontierTests.FrequencyCertificate
