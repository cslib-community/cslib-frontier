/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.ClockSync.ByzantineSync
import CslibFrontier.Computability.Distributed.ClockSync.LundeliusLynch
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Client tests for lockstep drift-free clock synchronization

Representative `module` client tests for `Cslib.Distributed.ClockSync`:

* `decide +kernel`-checked 2-round time-shift indistinguishability (`localView`, `adj`,
  `syncOffset`) on `Fin 4` over `ℚ`;
* `decide +kernel`-checked tightness of `lockstepClockAvg` on `Fin 1`, `Fin 2`, `Fin 3`, and
  `Fin 4` over `ℚ`, attaining `(1 - 1 / n) * (d_max - d_min)` (`0`, `u / 2`, `2 * u / 3`,
  `3 * u / 4`) across every prefix-shifted execution;
* lockstep minimax characterization `exists_achievesLockstepSkew_iff` and lower bound
  `lockstepClockSync_lower_bound` over `ℚ` and continuous time `ℝ`;
* `decide +kernel`-checked `lockstepByzantineClockStep`, `lockstepDriftFreeByzantineOffset`, and
  2-round `lockstepDriftFreeByzantineOffsetIter` on `Fin 4, t = 1` against a wildly equivocating
  Byzantine clock, contrasting with non-resilient `lockstepClockAvg`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Distributed.ClockSync

open Cslib.Distributed.ClockSync

/-! ### 2-round lockstep time-shift indistinguishability on `Fin 4` over `ℚ` -/

/-- A concrete 2-round lockstep protocol whose round-1 send times depend on round-0 arrivals. -/
def twoRoundEcho : LockstepProtocol (Fin 4) ℚ 2 where
  sendTime
    | ⟨0, _⟩, p, _, _ => p.val
    | ⟨1, _⟩, p, v, q => v.lastArrival q + p.val
  adjust p v := (v.lastArrival 0 - v.lastArrival p) / 2

def sampleOffsets : Fin 4 → ℚ
  | 0 => 10
  | 1 => -4
  | 2 => 7 / 2
  | 3 => 0

def sampleShift : Fin 4 → ℚ
  | 0 => 3
  | 1 => -2
  | 2 => 11 / 2
  | 3 => -1

def sampleDelays : ℕ → Fin 4 → Fin 4 → ℚ
  | 0, p, q => 1 + (p.val + q.val : ℚ) / 4
  | _, p, q => 2 + (p.val : ℚ) / 2 - (q.val : ℚ) / 4

-- Both 2-round local views and adjustments are identical under the shifted execution, while
-- synchronized offsets shift by `sampleShift`.
example :
    (∀ p : Fin 4,
      twoRoundEcho.localView (shiftOffsets sampleOffsets sampleShift)
          (shiftDelays sampleDelays sampleShift) 2 le_rfl p =
        twoRoundEcho.localView sampleOffsets sampleDelays 2 le_rfl p) ∧
    (∀ p : Fin 4,
      twoRoundEcho.adj (shiftOffsets sampleOffsets sampleShift)
          (shiftDelays sampleDelays sampleShift) p =
        twoRoundEcho.adj sampleOffsets sampleDelays p) ∧
    (∀ p : Fin 4,
      twoRoundEcho.syncOffset (shiftOffsets sampleOffsets sampleShift)
          (shiftDelays sampleDelays sampleShift) p =
        twoRoundEcho.syncOffset sampleOffsets sampleDelays p + sampleShift p) := by
  decide +kernel

/-! ### Tightness of `(1 - 1 / n) * u` across shifted executions on `Fin 1..4` (`u = 4`) -/

/-- Adversarial base delays `δ₀ _ i j = if i ≤ j then 1 else 5` (`u = 4`). -/
def baseDelays (n : ℕ) : ℕ → Fin n → Fin n → ℚ :=
  fun _ i j => if i ≤ j then 1 else 5

/-- Prefix shift `s_m i = if i < m then 4 else 0`. -/
def prefixShift (n m : ℕ) : Fin n → ℚ :=
  fun i => if i.val < m then 4 else 0

-- Fin 1: (1 - 1 / 1) * 4 = 0, exact zero skew.
example :
    (lockstepClockAvg (P := Fin 1) (1 : ℚ) 5).syncOffset (fun _ => 17 / 3) (baseDelays 1) 0 =
      17 / 3 := by
  decide +kernel

example : AchievesLockstepSkew (lockstepClockAvg (P := Fin 1) (1 : ℚ) 5) 1 5 0 := by
  simpa using lockstepClockAvg_achievesSkew (P := Fin 1) (K := ℚ) (d_min := 1) (d_max := 5)
    (by norm_num)

-- Fin 2: (1 - 1 / 2) * u = u / 2 = 2, attained on both E₀ and shifted E₁.
example :
    let π := lockstepClockAvg (P := Fin 2) (1 : ℚ) 5
    let c₀ : Fin 2 → ℚ := fun _ => 0
    let δ₀ := baseDelays 2
    let c₁ := shiftOffsets c₀ (prefixShift 2 1)
    let δ₁ := shiftDelays δ₀ (prefixShift 2 1)
    π.syncOffset c₀ δ₀ 1 - π.syncOffset c₀ δ₀ 0 = 2 ∧
      π.syncOffset c₁ δ₁ 0 - π.syncOffset c₁ δ₁ 1 = 2 ∧
      π.adj c₁ δ₁ 0 = π.adj c₀ δ₀ 0 ∧
      π.adj c₁ δ₁ 1 = π.adj c₀ δ₀ 1 := by
  decide +kernel

-- Fin 3: (1 - 1 / 3) * u = 2 * u / 3 = 8 / 3, attained on E₀, E₁, and E₂.
example :
    let π := lockstepClockAvg (P := Fin 3) (1 : ℚ) 5
    let c₀ : Fin 3 → ℚ := fun _ => 0
    let δ₀ := baseDelays 3
    let c₁ := shiftOffsets c₀ (prefixShift 3 1)
    let δ₁ := shiftDelays δ₀ (prefixShift 3 1)
    let c₂ := shiftOffsets c₀ (prefixShift 3 2)
    let δ₂ := shiftDelays δ₀ (prefixShift 3 2)
    π.syncOffset c₀ δ₀ 2 - π.syncOffset c₀ δ₀ 0 = 8 / 3 ∧
      π.syncOffset c₁ δ₁ 0 - π.syncOffset c₁ δ₁ 1 = 8 / 3 ∧
      π.syncOffset c₂ δ₂ 1 - π.syncOffset c₂ δ₂ 2 = 8 / 3 := by
  decide +kernel

-- Fin 4: (1 - 1 / 4) * u = 3 * u / 4 = 3, attained on all four executions E₀, E₁, E₂, E₃.
example :
    let π := lockstepClockAvg (P := Fin 4) (1 : ℚ) 5
    let c₀ : Fin 4 → ℚ := fun _ => 0
    let δ₀ := baseDelays 4
    let c₁ := shiftOffsets c₀ (prefixShift 4 1)
    let δ₁ := shiftDelays δ₀ (prefixShift 4 1)
    let c₂ := shiftOffsets c₀ (prefixShift 4 2)
    let δ₂ := shiftDelays δ₀ (prefixShift 4 2)
    let c₃ := shiftOffsets c₀ (prefixShift 4 3)
    let δ₃ := shiftDelays δ₀ (prefixShift 4 3)
    π.syncOffset c₀ δ₀ 3 - π.syncOffset c₀ δ₀ 0 = 3 ∧
      π.syncOffset c₁ δ₁ 0 - π.syncOffset c₁ δ₁ 1 = 3 ∧
      π.syncOffset c₂ δ₂ 1 - π.syncOffset c₂ δ₂ 2 = 3 ∧
      π.syncOffset c₃ δ₃ 2 - π.syncOffset c₃ δ₃ 3 = 3 := by
  decide +kernel

/-! ### Lockstep minimax characterization over `ℚ` and continuous time `ℝ` -/

-- On Fin 4 with [d_min, d_max] = [1, 5], skew 3 is achievable (in 1 lockstep round), whereas
-- 299 / 100 is impossible for any deterministic LockstepProtocol of any round count R.
example : ∃ (R : ℕ) (π : LockstepProtocol (Fin 4) ℚ R), AchievesLockstepSkew π 1 5 3 := by
  rw [exists_achievesLockstepSkew_iff (by norm_num)]
  norm_num

example :
    ¬ ∃ (R : ℕ) (π : LockstepProtocol (Fin 4) ℚ R), AchievesLockstepSkew π 1 5 (299 / 100) := by
  rw [exists_achievesLockstepSkew_iff (by norm_num)]
  norm_num

-- Direct client check of `lockstepClockSync_lower_bound` on `twoRoundEcho` over `ℚ`.
example {γ : ℚ} (h : AchievesLockstepSkew twoRoundEcho 1 5 γ) : 3 ≤ γ := by
  have hlb := lockstepClockSync_lower_bound (d_min := (1 : ℚ)) (d_max := 5) (by norm_num) h
  norm_num at hlb
  exact hlb

-- Continuous-time instantiation over `ℝ` on Fin 4: lockstep minimax skew is (3/4)*(d_max - d_min).
example {d_min d_max γ : ℝ} (hd : d_min ≤ d_max) :
    (∃ (R : ℕ) (π : LockstepProtocol (Fin 4) ℝ R), AchievesLockstepSkew π d_min d_max γ) ↔
      (3 / 4 : ℝ) * (d_max - d_min) ≤ γ := by
  rw [exists_achievesLockstepSkew_iff hd]
  norm_num

/-! ### Lockstep drift-free Byzantine trimmed-midpoint step on `Fin 4, t = 1` over `ℚ` -/

/-- Initial offsets: honest processes `{0, 1, 2}` have skew `δ₀ = 8` (`0, 4, 8`); faulty `3` has
offset `1000`. -/
def byzOffsets : Fin 4 → ℚ
  | 0 => 0
  | 1 => 4
  | 2 => 8
  | 3 => 1000

/-- Honest transit delays lie in `[1, 3]` (`d_min = 1, d_max = 3, u = 2`). -/
def byzDelays : Fin 4 → Fin 4 → ℚ :=
  fun j p => if j ≤ p then 1 else 3

/-- Equivocating faulty clock `3` reports wildly different arrival timestamps to `0, 1, 2`. -/
def byzAdv : Fin 4 → Fin 4 → ℚ
  | _, 0 => -500
  | _, 1 => 999
  | _, _ => 0

-- Plain fault-free averaging is broken by the equivocating clock `3` (skew > 300 between 0 and 1),
-- whereas `lockstepDriftFreeByzantineOffset` trims out the Byzantine outlier and keeps honest
-- pairs `{0, 1, 2}` within `8 / 2 + 2 = 6` after 1 round and within `5` after 2 rounds.
example :
    let F : Finset (Fin 4) := {3}
    let avgRecv (p : Fin 4) : Fin 4 → ℚ :=
      fun j => lockstepByzantineArrival F byzAdv byzOffsets byzDelays j p
    let avgSync (p : Fin 4) : ℚ :=
      byzOffsets p + (∑ j : Fin 4, estDiff 1 3 p (avgRecv p) j) / 4
    let r1 := lockstepDriftFreeByzantineOffset 1 (1 : ℚ) 3 F byzAdv byzOffsets byzDelays
    let r2 := lockstepDriftFreeByzantineOffsetIter 1 (1 : ℚ) 3 F (fun _ => byzAdv) byzOffsets
      (fun _ => byzDelays) 2
    300 < |avgSync 0 - avgSync 1| ∧
      |r1 0 - r1 1| ≤ 6 ∧ |r1 0 - r1 2| ≤ 6 ∧ |r1 1 - r1 2| ≤ 6 ∧
      |r2 0 - r2 1| ≤ 5 ∧ |r2 0 - r2 2| ≤ 5 ∧ |r2 1 - r2 2| ≤ 5 := by
  decide +kernel

-- Checked application of `lockstepDriftFreeByzantineOffset_mem_Icc`,
-- `lockstepDriftFreeByzantineOffset_abs_sub_le`, and
-- `lockstepDriftFreeByzantineOffsetIter_abs_sub_le` on Fin 4, t = 1.
example {c : Fin 4 → ℚ} {adv δ : Fin 4 → Fin 4 → ℚ}
    (hc_Icc : ∀ j ∉ ({3} : Finset (Fin 4)), 0 ≤ c j ∧ c j ≤ 8)
    (hc_skew : ∀ p ∉ ({3} : Finset (Fin 4)), ∀ q ∉ ({3} : Finset (Fin 4)), |c p - c q| ≤ 8)
    (hδ : ∀ j ∉ ({3} : Finset (Fin 4)), ∀ p ∉ ({3} : Finset (Fin 4)), 1 ≤ δ j p ∧ δ j p ≤ 3) :
    (-1 ≤ lockstepDriftFreeByzantineOffset 1 1 3 ({3} : Finset (Fin 4)) adv c δ 0 ∧
        lockstepDriftFreeByzantineOffset 1 1 3 ({3} : Finset (Fin 4)) adv c δ 0 ≤ 9) ∧
      |lockstepDriftFreeByzantineOffset 1 1 3 ({3} : Finset (Fin 4)) adv c δ 0 -
          lockstepDriftFreeByzantineOffset 1 1 3 ({3} : Finset (Fin 4)) adv c δ 2| ≤ 6 ∧
      |lockstepDriftFreeByzantineOffsetIter 1 1 3 ({3} : Finset (Fin 4)) (fun _ => adv) c
            (fun _ => δ) 3 0 -
          lockstepDriftFreeByzantineOffsetIter 1 1 3 ({3} : Finset (Fin 4)) (fun _ => adv) c
            (fun _ => δ) 3 2| ≤ 9 / 2 := by
  have hIcc := lockstepDriftFreeByzantineOffset_mem_Icc (P := Fin 4) (t := 1) (by decide)
    (F := {3}) (by decide) (lo := 0) (hi := 8) adv c δ hc_Icc hδ
    (p := 0) (by decide)
  have h1 := lockstepDriftFreeByzantineOffset_abs_sub_le (P := Fin 4) (t := 1) (by decide)
    (F := {3}) (by decide) (d_min := 1) (d_max := 3) (δ₀ := 8) adv c δ hc_skew hδ
    (p := 0) (q := 2) (by decide) (by decide)
  have h3 := lockstepDriftFreeByzantineOffsetIter_abs_sub_le (P := Fin 4) (t := 1) (by decide)
    (F := {3}) (by decide) (d_min := 1) (d_max := 3) (δ₀ := 8)
    (fun _ => adv) c (fun _ => δ) hc_skew (fun _ => hδ) 3 (p := 0) (q := 2) (by decide) (by decide)
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

end CslibFrontierTests.Computability.Distributed.ClockSync
