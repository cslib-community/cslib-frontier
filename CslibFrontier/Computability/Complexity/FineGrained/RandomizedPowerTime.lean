/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.PowerTime
public import CslibFrontier.Computability.Complexity.FineGrained.Randomized
import CslibFrontier.Computability.Complexity.FineGrained.Bounds

/-!
# Randomized time bounds with a power in the exponent

The power-exponential time bound for seeded promise solvers uses the same parameter and
encoded-length factors as the deterministic bound.

## Main definitions

* `Cslib.Complexity.SolvesWithErrorInPowerExpTime`: a worst-case time bound for seeded solvers.

## Main results

* `Cslib.Complexity.solvesWithErrorInPowerExpTime_deterministic_iff`: at zero error, the
  bound for a language agrees with deterministic decidability.
-/

public section

namespace Cslib.Complexity

open PromiseProblem

variable {α : Type} {enc : α ↪ List Bool} {μ : α → ℕ} {p : ℝ}

/-- A solver with error profile `E` runs in time
`2 ^ (C * (μ a + 1) ^ p) * (L + 1) ^ e` up to constant factors for some `C,e : ℕ`,
where `L` is the encoded input length. The time bound holds on every seed. -/
@[expose] def SolvesWithErrorInPowerExpTime (Q : PromiseProblem α) (enc : α ↪ List Bool)
    (E : ErrorModel) (μ : α → ℕ) (p : ℝ) : Prop :=
  ∃ C e : ℕ, SolvesWithErrorInTimeO Q enc E
    fun a => (2 : ℝ) ^ (C * (μ a + 1 : ℝ) ^ p) * ((enc a).length + 1) ^ e

/-- Relaxing the error profile preserves the power-exponential running time. -/
theorem SolvesWithErrorInPowerExpTime.mono_error {Q : PromiseProblem α} {E₁ E₂ : ErrorModel}
    (h : SolvesWithErrorInPowerExpTime Q enc E₁ μ p) (hE : E₁ ≤ E₂) :
    SolvesWithErrorInPowerExpTime Q enc E₂ μ p := by
  obtain ⟨C, e, h⟩ := h
  exact ⟨C, e, h.mono_error hE⟩

/-- Zero-error seeded solvers of a language and deterministic deciders have the same power
bound. The polynomial factor can absorb the cost of reading the encoded input. -/
theorem solvesWithErrorInPowerExpTime_deterministic_iff {A : Set α} :
    SolvesWithErrorInPowerExpTime (ofSet A) enc ErrorModel.deterministic μ p ↔
      DecidableInPowerExpTime A enc μ p := by
  let time (C e : ℕ) (a : α) :=
    (2 : ℝ) ^ (C * (μ a + 1 : ℝ) ^ p) * ((enc a).length + 1) ^ e
  have hlen (C e : ℕ) (a : α) : ((enc a).length : ℝ) ≤ time C (max e 1) a := by
    have h := pow_le_two_rpow_mul_pow (L := (enc a).length) (d := 1)
      (x := C * (μ a + 1 : ℝ) ^ p) (by positivity) (le_max_right e 1)
    rw [pow_one] at h
    exact (le_add_of_nonneg_right zero_le_one).trans h
  have hpad (C e : ℕ) (a : α) :
      time C e a ≤ (↑(1 : ℕ) : ℝ) * time C (max e 1) a + ↑(1 : ℕ) := by
    rw [Nat.cast_one, one_mul]
    exact (two_rpow_mul_pow_le_two_rpow_mul_pow le_rfl (le_max_left e 1) :
      time C e a ≤ time C (max e 1) a).trans (le_add_of_nonneg_right zero_le_one)
  have hnonneg (C e : ℕ) (a : α) : 0 ≤ time C (max e 1) a := by
    dsimp only [time]
    positivity
  have hbridge (C e : ℕ) :
      SolvesWithErrorInTimeO (ofSet A) enc ErrorModel.deterministic (time C (max e 1)) ↔
        DecidableInTimeO A enc (time C (max e 1)) :=
    (solvesWithErrorInTimeO_deterministic_iff (hlen C e)).trans solvesPromiseInTimeO_ofSet_iff
  constructor
  · rintro ⟨C, e, h⟩
    exact ⟨C, max e 1, (hbridge C e).mp (h.mono 1 (hpad C e) (hnonneg C e))⟩
  · rintro ⟨C, e, h⟩
    exact ⟨C, max e 1, (hbridge C e).mpr (h.mono 1 (hpad C e) (hnonneg C e))⟩

end Cslib.Complexity
