/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingInput
public import CslibFrontier.Algorithms.ThreeSum.ChanHe.ShiftedSizes

/-!
# Subquadratic charged native preprocessing cost

The bound counts complete initialized-input execution, trial division, all descriptor loads,
every recursion transition, native collision/heavy computation, array writes and the final halt.
Its polynomial factor is `(n+2)(sqrt(n+2)+1)` and its logarithm has fixed degree thirteen.

## Main definitions

* `rootCoefficient`, `costCoefficient`: explicit constants depending only on the fixed exponent.

## Main results

* `cost_bound`: the actual native instruction count is at most square-root times linear times
  a fixed logarithmic power, uniformly over physical width.

These charged estimates are original. The existing mathematical prime/instance bounds are reused.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- Uniform complete-root coefficient after substituting the actual candidate bound. -/
def rootCoefficient (κ : ℕ) : ℕ :=
  let C := (5 * κ + 16) * (10 * κ + 40) + 1
  70 + 196608 * (C + 4 * C ^ 3)

/-- Explicit whole-program coefficient, independent of input length, data and physical width. -/
def costCoefficient (κ : ℕ) : ℕ :=
  let C := (5 * κ + 16) * (10 * κ + 40) + 1
  Frontend.costCoefficient κ + 60 * C ^ 2 + 77 +
    4 * (κ + 3) ^ 2 * (rootCoefficient κ + 17)

private abbrev paramFactor (κ : ℕ) : ℕ := (5 * κ + 16) * (10 * κ + 40) + 1

private theorem parameter_scale_bounds (κ n : ℕ) :
    let B := n + 2
    let L := Nat.log 2 B + 1
    let S := Nat.sqrt B + 1
    Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * B ^ κ) + 1 ≤ paramFactor κ * S * L ^ 2 ∧
      S ^ 2 ≤ 4 * B := by
  let B := n + 2
  let L := Nat.log 2 B + 1
  let S := Nat.sqrt B + 1
  have hB : 2 ≤ B := by dsimp only [B]; omega
  have hL : 1 ≤ L := by dsimp only [L]; omega
  have hS : 1 ≤ S := by dsimp only [S]; omega
  constructor
  · have hm := Cslib.Algorithms.ThreeSum.ChanHe.mPar_shifted_pow_le n κ
    have hu : 1 ≤ S * L ^ 2 := by
      have hp : 0 < S * L ^ 2 := by positivity
      omega
    calc _ ≤ ((5 * κ + 16) * (10 * κ + 40)) * S * L ^ 2 + S * L ^ 2 :=
        Nat.add_le_add hm hu
      _ = paramFactor κ * S * L ^ 2 := by dsimp only [paramFactor]; ring
  · have hs := Nat.sqrt_le B
    have ht := Nat.sqrt_le_self B
    change S ^ 2 ≤ 4 * B
    dsimp only [S]
    nlinarith only [hs, ht, hB]

/-- The complete root cost at the actual magnitude-derived candidate window. -/
theorem root_cost_bound (κ n : ℕ) :
    let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
    Traversal.rootTime (Cslib.Algorithms.ThreeSum.ChanHe.fuel n) (n + 1) m (2 * m ^ 2) ≤
      rootCoefficient κ * (n + 2) * (Nat.sqrt (n + 2) + 1) *
        (Nat.log 2 (n + 2) + 1) ^ 11 := by
  let B := n + 2
  let L := Nat.log 2 B + 1
  let S := Nat.sqrt B + 1
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * B ^ κ)
  obtain ⟨hmb, hsquare⟩ := parameter_scale_bounds κ n
  change m + 1 ≤ paramFactor κ * S * L ^ 2 at hmb
  change S ^ 2 ≤ 4 * B at hsquare
  have hcube : S ^ 3 ≤ 4 * B * S := by
    rw [show S ^ 3 = S ^ 2 * S by ring]
    exact Nat.mul_le_mul_right S hsquare
  have lp {i j : ℕ} (hij : i ≤ j) : L ^ i ≤ L ^ j :=
    Nat.pow_le_pow_right (by dsimp only [L]; omega) hij
  have hr := Traversal.rootTime_fuel_square_le n (n + 1) m
  have hlog : Nat.log 2 n ≤ Nat.log 2 B := Nat.log_mono_right (by dsimp only [B]; omega)
  have hlogs : 2 * Nat.log 2 n + 2 ≤ 2 * L := by dsimp only [L]; omega
  calc Traversal.rootTime (Cslib.Algorithms.ThreeSum.ChanHe.fuel n) (n + 1) m (2 * m ^ 2)
      ≤ 70 + 6144 * (2 * L) ^ 5 *
        (B * (paramFactor κ * S * L ^ 2) + (paramFactor κ * S * L ^ 2) ^ 3) := by
          apply hr.trans
          change 70 + 6144 * (2 * Nat.log 2 n + 2) ^ 5 *
            (B * (m + 1) + (m + 1) ^ 3) ≤ _
          gcongr
    _ = 70 + 196608 * (paramFactor κ * B * S * L ^ 7 + paramFactor κ ^ 3 * S ^ 3 * L ^ 11) := by
      ring
    _ ≤ 70 + 196608 *
        (paramFactor κ * B * S * L ^ 11 + paramFactor κ ^ 3 * (4 * B * S) * L ^ 11) := by
      gcongr _ + _ * (_ * ?_ + _ * ?_ * _)
      exact lp (by decide)
    _ ≤ rootCoefficient κ * B * S * L ^ 11 := by
      have hu : 1 ≤ B * S * L ^ 11 := Nat.pos_of_ne_zero (by dsimp only [B, S, L]; positivity)
      change _ ≤ (70 + 196608 * (paramFactor κ + 4 * paramFactor κ ^ 3)) * B * S * L ^ 11
      nlinarith only [hu]

private theorem forest_time_bound (κ n : ℕ) :
    let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
    let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
    (Frontend.layout κ n).count * (Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17) ≤
      (4 * (κ + 3) ^ 2 * (rootCoefficient κ + 17)) *
        ((n + 2) * (Nat.sqrt (n + 2) + 1) * (Nat.log 2 (n + 2) + 1) ^ 13) := by
  have hL : 1 ≤ Nat.log 2 (n + 2) + 1 := Nat.succ_pos _
  have hD : (Frontend.layout κ n).count ≤ 4 * (κ + 3) ^ 2 * (Nat.log 2 (n + 2) + 1) ^ 2 := by
    have hb : (Frontend.layout κ n).digits ≤ (κ + 3) * (Nat.log 2 (n + 2) + 1) :=
      (Cslib.Algorithms.ThreeSum.ChanHe.labelBits_pow_le (n + 2) κ).trans (by
        change κ * (Nat.log 2 (n + 2) + 1) + 3 ≤ _; nlinarith only [hL])
    have hh := Nat.pow_le_pow_left hb 2
    have hu : 1 ≤ ((κ + 3) * (Nat.log 2 (n + 2) + 1)) ^ 2 := Nat.pos_of_ne_zero (by positivity)
    dsimp only [Frontend.Layout.count, Frontend.Layout.splits]
    nlinarith only [hh, hu]
  have hu : 1 ≤ (n + 2) * (Nat.sqrt (n + 2) + 1) * (Nat.log 2 (n + 2) + 1) ^ 11 :=
    Nat.pos_of_ne_zero (by positivity)
  have hroot := root_cost_bound κ n
  dsimp only at hroot ⊢
  calc _ ≤ (4 * (κ + 3) ^ 2 * (Nat.log 2 (n + 2) + 1) ^ 2) *
        ((rootCoefficient κ + 17) * ((n + 2) * (Nat.sqrt (n + 2) + 1) *
          (Nat.log 2 (n + 2) + 1) ^ 11)) :=
      Nat.mul_le_mul hD (by nlinarith only [hroot, hu])
    _ = _ := by ring

private theorem prime_time_bound (B S C L m : ℕ)
    (hB : 1 ≤ B) (hS : 1 ≤ S) (hL : 1 ≤ L)
    (hmb : m + 1 ≤ C * S * L ^ 2) (hsquare : S ^ 2 ≤ 4 * B) :
    (m + 1) * (7 * m + 15) + 8 ≤
      (60 * C ^ 2 + 8) * (B * S * L ^ 13) := by
  have hV : 0 < B * S * L ^ 13 := by positivity
  have hsmall : B * L ^ 4 ≤ B * S * L ^ 13 := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _
      ((Nat.pow_le_pow_right hL (by decide)).trans (Nat.le_mul_of_pos_left _ hS))
  have hms : (m + 1) ^ 2 ≤ 4 * C ^ 2 * B * L ^ 4 := by
    nlinarith only [Nat.pow_le_pow_left hmb 2, Nat.mul_le_mul_right (C ^ 2 * L ^ 4) hsquare]
  nlinarith only [hms, Nat.mul_le_mul_left (60 * C ^ 2) hsmall, hV]

private theorem frontend_time_bound (κ n : ℕ) :
    Frontend.cost κ n ≤ Frontend.costCoefficient κ *
      ((n + 2) * (Nat.sqrt (n + 2) + 1) * (Nat.log 2 (n + 2) + 1) ^ 13) := by
  have hclog : Nat.clog 2 (n + 2) ≤ Nat.log 2 (n + 2) + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide) _).le
  have hh := Frontend.cost_bound κ n
  rw [Nat.mul_assoc] at hh
  refine hh.trans (Nat.mul_le_mul_left _ ?_)
  calc (n + 1) * Nat.clog 2 (n + 2) ^ 2 ≤ (n + 2) * 1 * (Nat.log 2 (n + 2) + 1) ^ 13 :=
        Nat.mul_le_mul (by omega)
          ((Nat.pow_le_pow_left hclog 2).trans (Nat.pow_le_pow_right (by omega) (by decide)))
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_add_left 1 _))

/-- The actual native program has a genuinely subquadratic polynomial factor and fixed polylog. -/
theorem cost_bound (κ n : ℕ) :
    cost κ n ≤ costCoefficient κ * (n + 2) * (Nat.sqrt (n + 2) + 1) *
      (Nat.log 2 (n + 2) + 1) ^ 13 := by
  let B := n + 2
  let L := Nat.log 2 B + 1
  let S := Nat.sqrt B + 1
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * B ^ κ)
  let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  let V := B * S * L ^ 13
  have hB : 2 ≤ B := by dsimp only [B]; omega
  have hL : 1 ≤ L := by dsimp only [L]; omega
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have hlog : Nat.log 2 n ≤ Nat.log 2 B := Nat.log_mono_right (by dsimp only [B]; omega)
  obtain ⟨hmb, hsquare⟩ := parameter_scale_bounds κ n
  change m + 1 ≤ paramFactor κ * S * L ^ 2 at hmb
  change S ^ 2 ≤ 4 * B at hsquare
  have hV : 0 < V := by dsimp only [V]; positivity
  have hforest := forest_time_bound κ n
  change (Frontend.layout κ n).count *
    (Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17) ≤
      (4 * (κ + 3) ^ 2 * (rootCoefficient κ + 17)) * V at hforest
  have hprime : (m + 1) * (7 * m + 15) + 8 ≤ (60 * paramFactor κ ^ 2 + 8) * V :=
    prime_time_bound B S (paramFactor κ) L m (by omega) hS hL hmb hsquare
  have hfront : Frontend.cost κ n ≤ Frontend.costCoefficient κ * V := frontend_time_bound κ n
  have hheight : Cslib.Algorithms.ThreeSum.ChanHe.height n ≤ Nat.log 2 n + 2 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hLV : L ≤ V :=
    (Nat.le_self_pow (by decide) L).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hsmall : F ≤ 6 * L := by
    change 3 * Cslib.Algorithms.ThreeSum.ChanHe.height n - 2 ≤ _
    dsimp only [L]
    omega
  change Frontend.cost κ n + (m + 1) * (7 * m + 15) + 8 + 4 * F + 45 +
    (Frontend.layout κ n).count * (Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17) ≤ _
  rw [show costCoefficient κ * (n + 2) * (Nat.sqrt (n + 2) + 1) *
      (Nat.log 2 (n + 2) + 1) ^ 13 = costCoefficient κ * V by dsimp only [V, B, S, L]; ring]
  change _ ≤ (Frontend.costCoefficient κ + 60 * paramFactor κ ^ 2 + 77 +
    4 * (κ + 3) ^ 2 * (rootCoefficient κ + 17)) * V
  linarith only [hfront, hprime, hforest, hsmall, hLV, hV]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
