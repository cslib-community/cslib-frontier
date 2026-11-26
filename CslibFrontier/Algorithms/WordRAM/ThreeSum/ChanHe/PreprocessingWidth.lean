/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingBounds

/-!
# Derived logarithmic width for native Chan–He preprocessing

The positive physical-width threshold depends only on the fixed magnitude exponent and actual
input length. Its signed envelope covers every root, including all shared memory reservations.

## Main definitions

* `width`: positive physical width sufficient for the complete preprocessing envelope.

## Main results

* `arena_ready`: global logarithmic width derives the complete traversal fit contract.
* `input_fits`: the same width derives actual signed-encoded input fitting.

These coarse native resource bounds are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- One positive logarithmic physical width for every native preprocessing component. -/
def width (κ n : ℕ) : ℕ := 65 * Parameters.width κ n

/-- The threshold has a positive exponent-dependent coefficient and no dependence on input data. -/
theorem width_eq (κ n : ℕ) :
    width κ n = (1300 * κ + 7865) * Nat.clog 2 (n + 2) := by
  dsimp only [width, Parameters.width]; ring

/-- Empty inputs and exponent zero also receive a strictly positive word width. -/
theorem width_pos (κ n : ℕ) : 0 < width κ n :=
  Nat.mul_pos (by decide) (Parameters.width_pos κ n)

/-- The signed compiler's two representation bits are always available. -/
theorem three_le_width (κ n : ℕ) : 3 ≤ width κ n := by
  have hL : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by decide) (by omega)
  rw [width_eq]; nlinarith

/-- The whole-frontend threshold is covered by the global preprocessing threshold. -/
theorem frontend_width_le (κ n : ℕ) : Frontend.width κ n ≤ width κ n := by
  dsimp only [Frontend.width, width]; omega

/-- The global logarithmic width derives all local signed kernel fits and allocation bounds. -/
theorem arena_ready {κ n w : ℕ} (hw : width κ n ≤ w) (retained : ℕ → ℕ) :
    (arena κ n retained).Ready (w - 2) := by
  let P := Parameters.Math.budget n ((n + 2) ^ κ)
  let p := Parameters.width κ n
  let a := arena κ n retained
  have hL : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by decide) (by omega)
  have hp : 3 ≤ p := by dsimp only [p, Parameters.width]; nlinarith
  have hwide : 65 * p ≤ w := hw
  have hpow : P ^ 52 < 2 ^ (52 * p) := by
    simpa only [← pow_mul, Nat.mul_comm] using
      Nat.pow_lt_pow_left (Parameters.budget_fits (κ := κ) (n := n) le_rfl) (by decide : 52 ≠ 0)
  have henv : Traversal.envelope a.ceiling a.n a.m a.Λ a.U a.N ≤ P ^ 52 :=
    arena_envelope_le κ n retained
  have hfit : Traversal.envelope a.ceiling a.n a.m a.Λ a.U a.N < 2 ^ (w - 3) :=
    (henv.trans_lt hpow).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hfitZ : ((Traversal.envelope a.ceiling a.n a.m a.Λ a.U a.N : ℕ) : ℤ) <
      (2 : ℤ) ^ (w - 3) := by exact_mod_cast hfit
  refine ⟨?_, le_rfl, by omega, ?_, ?_⟩
  · change 2 ≤ Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
    dsimp only [Cslib.Algorithms.ThreeSum.ChanHe.mPar]; nlinarith
  all_goals
    rw [show w - 2 - 1 = w - 3 by omega]
    omega

/-- The actual native unsigned length header and every signed payload fit the derived width. -/
theorem input_fits {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    InputFits w (input.map Signed.encode) :=
  Frontend.input_fits input ((frontend_width_le κ input.length).trans hw) hvalues

/-- The same global width covers every scalar and address of the native layout controller. -/
theorem setup_fits {κ n w : ℕ} (hw : width κ n ≤ w) (retained : ℕ → ℕ) :
    let a := arena κ n retained
    Fits w (a.floor + a.U + a.N + a.fuel + 16) ∧
      Fits w ((Frontend.layout κ n).endpoint + a.m + 4) ∧
      Fits w (3 ^ (a.fuel + 1)) ∧ Fits w 6 := by
  dsimp only
  set a := arena κ n retained
  let S := a.ceiling + a.n + a.m ^ 2 + a.Λ + a.m + a.U + a.N + 100
  have hs : S ≤ S ^ 4 := Nat.le_self_pow (by decide) S
  have hf : a.fuel ≤ a.floor ∧ a.floor ≤ a.ceiling ∧
      (Frontend.layout κ n).endpoint ≤ a.ceiling := by dsimp only [a, arena]; omega
  have hword := Signed.unsigned_fits_of_signed (arena_ready hw retained).2.2
  have hw3 := (three_le_width κ n).trans hw
  rw [show w - 2 + 2 = w by omega] at hword
  have cover {v : ℕ} (hv : v ≤ 3 * S) : Fits w v := hword.of_le <| by
    change v ≤ 65536 * S ^ 4
    omega
  refine ⟨cover (by omega), cover (by omega), cover ?_, cover (by omega)⟩
  have hmul := Nat.mul_le_mul (show 2 ≤ (Frontend.layout κ n).count by
      dsimp only [Frontend.Layout.count]; omega)
    (Nat.mul_le_mul_left (Traversal.Math.work a.fuel)
      (show 3 ≤ Traversal.allocationSize a.n a.m a.N by
        dsimp only [Traversal.allocationSize]; omega))
  have hceil : (Frontend.layout κ n).count *
      (Traversal.Math.work a.fuel * Traversal.allocationSize a.n a.m a.N) ≤ a.ceiling :=
    Nat.le_add_left _ _
  have := Traversal.Math.work_pos a.fuel
  have := Traversal.Math.work_eq a.fuel
  dsimp only [S]; nlinarith

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
