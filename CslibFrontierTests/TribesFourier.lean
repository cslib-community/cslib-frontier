/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.Tribes

/-! # Tests for the Fourier coefficients of Tribes

`Tribes_{2,2}` on four bits, read as signs. Its tribes are the sets
`{finProdFinEquiv (0, 0), finProdFinEquiv (0, 1)}` and
`{finProdFinEquiv (1, 0), finProdFinEquiv (1, 1)}`. Each coefficient below is computed twice: by
brute force, from the Hamming distance to a parity (`Cslib.BitString.fourierCoeff_signVal`, by
`decide`), and from O'Donnell's Proposition 4.14. The empty set has coefficient `1 / 8`, one
coordinate `3 / 8`, and a whole tribe `-3 / 8`; the last case checks the sign `(-1) ^ (k + |T|)`.
-/

public section

namespace CslibFrontierTests.TribesFourier

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- The first coordinate of `Tribes_{2,2}`. -/
abbrev c₀ : Fin (2 * 2) := finProdFinEquiv ((0 : Fin 2), (0 : Fin 2))

/-- The second coordinate of the first tribe of `Tribes_{2,2}`. -/
abbrev c₁ : Fin (2 * 2) := finProdFinEquiv ((0 : Fin 2), (1 : Fin 2))

/-- The first tribe of `Tribes_{2,2}`. -/
abbrev firstTribe : Finset (Fin (2 * 2)) := {c₀, c₁}

/-- The first coordinate lies in the first tribe, at position `0`. -/
theorem tribePart_c₀ (j : Fin 2) :
    tribePart {c₀} j = if j = 0 then {0} else ∅ := by
  ext i
  fin_cases j <;> fin_cases i <;> simp

/-- The first tribe lies in the first tribe: all of it, and none of the second. -/
theorem tribePart_firstTribe (j : Fin 2) :
    tribePart firstTribe j = if j = 0 then univ else ∅ := by
  ext i
  fin_cases j <;> fin_cases i <;> simp

/-- One coordinate meets one tribe. -/
theorem card_filter_tribePart_c₀ : #{j | tribePart {c₀} j ≠ ∅} = 1 := by
  simp only [tribePart_c₀]
  decide

/-- The first tribe meets one tribe. -/
theorem card_filter_tribePart_firstTribe : #{j | tribePart firstTribe j ≠ ∅} = 1 := by
  simp only [tribePart_firstTribe]
  decide

/-! ### The empty set -/

-- By brute force: `Tribes_{2,2}` is `true` on `7` of the `16` inputs, so the coefficient is
-- `1 - 2 · 7 / 16 = 1 / 8`.
example : fourierCoeff (fun x => signVal (tribes 2 2 x)) ∅ = 1 / 8 := by
  rw [fourierCoeff_signVal, show hammingDist (tribes 2 2) (parityOn ∅) = 7 by decide]
  norm_num

-- Proposition 4.14 agrees: `2 (3 / 4) ^ 2 - 1 = 1 / 8`.
example : fourierCoeff (fun x => signVal (tribes 2 2 x)) ∅ = 1 / 8 := by
  rw [fourierCoeff_signVal_tribes_empty]
  norm_num

/-! ### One coordinate -/

-- By brute force: `Tribes_{2,2}` differs from the first coordinate on `5` of the `16` inputs, so
-- the coefficient is `1 - 2 · 5 / 16 = 3 / 8`.
example : fourierCoeff (fun x => signVal (tribes 2 2 x)) {c₀} = 3 / 8 := by
  rw [fourierCoeff_signVal, show hammingDist (tribes 2 2) (parityOn {c₀}) = 5 by decide]
  norm_num

-- Proposition 4.14 agrees: one coordinate meets `k = 1` tribe, so the coefficient is
-- `2 (-1) ^ (1 + 1) 2 ^ (-2) (3 / 4) = 3 / 8`.
example : fourierCoeff (fun x => signVal (tribes 2 2 x)) {c₀} = 3 / 8 := by
  rw [fourierCoeff_signVal_tribes_of_ne_empty (singleton_ne_empty c₀),
    card_filter_tribePart_c₀, card_singleton]
  norm_num

/-! ### A whole tribe -/

-- By brute force: `Tribes_{2,2}` differs from the parity of the first tribe on `11` of the `16`
-- inputs, so the coefficient is `1 - 2 · 11 / 16 = -3 / 8`.
example : fourierCoeff (fun x => signVal (tribes 2 2 x)) firstTribe = -3 / 8 := by
  rw [fourierCoeff_signVal, show hammingDist (tribes 2 2) (parityOn firstTribe) = 11 by decide]
  norm_num

-- Proposition 4.14 agrees, with the sign `(-1) ^ (k + |T|) = (-1) ^ (1 + 2) = -1`: the first
-- tribe meets `k = 1` tribe in two coordinates, so the coefficient is
-- `2 (-1) ^ 3 2 ^ (-2) (3 / 4) = -3 / 8`.
example : fourierCoeff (fun x => signVal (tribes 2 2 x)) firstTribe = -3 / 8 := by
  rw [fourierCoeff_signVal_tribes_of_ne_empty (by decide), card_filter_tribePart_firstTribe,
    show #firstTribe = 2 by decide]
  norm_num

end CslibFrontierTests.TribesFourier
