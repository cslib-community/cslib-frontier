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
* `Cslib.Complexity.SolvesWithErrorInPowerExpTime.of_promiseReduction`: transfer the power
  bound through a deterministic promise reduction.
-/

public section

namespace Cslib.Complexity

open PromiseProblem Turing.MultiTapeTM

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

/-- A deterministic promise reduction of power `q` with parameter blowup
`O((μA + 1) ^ b)` transports a target solver of power `p ≥ 0` to power `max q (b * p)`,
preserving its error profile. The reduction's time also bounds the length it writes. -/
theorem SolvesWithErrorInPowerExpTime.of_promiseReduction {β : Type} {encB : β ↪ List Bool}
    {A : PromiseProblem α} {B : PromiseProblem β} {E : ErrorModel} {μB : β → ℕ} {r : α → β}
    {q b : ℝ} (hr : ComputableInPowerExpTime r enc encB μ q)
    (hyes : ∀ a ∈ A.yes, r a ∈ B.yes) (hno : ∀ a ∈ A.no, r a ∈ B.no)
    {K : ℕ} (hsize : ∀ a, (μB (r a) + 1 : ℝ) ≤ (K + 1 : ℝ) * (μ a + 1 : ℝ) ^ b)
    (hp : 0 ≤ p) (hB : SolvesWithErrorInPowerExpTime B encB E μB p) :
    SolvesWithErrorInPowerExpTime A enc E μ (max q (b * p)) := by
  obtain ⟨C, d, hr⟩ := hr
  obtain ⟨D, e, hB⟩ := hB
  let d' := max d 1
  let P (a : α) : ℝ := (2 : ℝ) ^ (C * (μ a + 1 : ℝ) ^ q) * ((enc a).length + 1) ^ d'
  let R : ℝ := D * (K + 1 : ℝ) ^ p
  let X (a : α) : ℝ := (2 : ℝ) ^ (R * (μ a + 1 : ℝ) ^ (b * p))
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hP (a : α) : ((enc a).length + 1 : ℝ) ≤ P a := by
    have h := pow_le_two_rpow_mul_pow (L := (enc a).length) (d := 1)
      (x := C * (μ a + 1 : ℝ) ^ q) (by positivity) (le_max_right d 1)
    simpa only [pow_one] using h
  have hP0 (a : α) : 0 ≤ P a := by dsimp only [P]; positivity
  have hr' : ComputableInTimeO r enc encB P :=
    hr.mono 1 (fun a =>
      (two_rpow_mul_pow_le_two_rpow_mul_pow le_rfl (le_max_left d 1) :
        (2 : ℝ) ^ (C * (μ a + 1 : ℝ) ^ q) * ((enc a).length + 1) ^ d ≤ P a).trans
        (by rw [Nat.cast_one, one_mul]; exact le_add_of_nonneg_right zero_le_one)) hP0
  have hX (a : α) : 1 ≤ X a := by
    dsimp only [X]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hY (a : α) : (2 : ℝ) ^ (D * (μB (r a) + 1 : ℝ) ^ p) ≤ 1 * X a := by
    rw [one_mul]
    exact two_rpow_mul_rpow_le_of_le_mul_rpow (by positivity) (by positivity)
      (by positivity) (hsize a) hp
  have h := hB.of_promiseReduction hr' hyes hno hP hX zero_le_one hY
  refine ⟨⌈R⌉₊ + C * (e + 1), d' * (e + 1), h.mono 1 (fun a => ?_) (fun _ => by positivity)⟩
  rw [Nat.cast_one, one_mul]
  exact (power_reduction_envelope_le (C := C) (d := d') (e := e)
    (x := (μ a + 1 : ℝ)) (y := ((enc a).length + 1 : ℝ)) (q := q) (r := b * p)
    (le_add_of_nonneg_left (Nat.cast_nonneg _)) (by positivity) hR).trans
    (le_add_of_nonneg_right zero_le_one)

/-- A polynomial-time promise reduction with parameter blowup `O((μA + 1) ^ b)` transports
power `p` to `b * p` with the same error profile. -/
theorem SolvesWithErrorInPowerExpTime.of_polyTime_promiseReduction
    {β : Type} {encB : β ↪ List Bool} {A : PromiseProblem α} {B : PromiseProblem β} {E : ErrorModel}
    {μB : β → ℕ} {r : α → β} {b : ℝ} (hr : ComputableInPolyTime r enc encB)
    (hyes : ∀ a ∈ A.yes, r a ∈ B.yes) (hno : ∀ a ∈ A.no, r a ∈ B.no)
    {K : ℕ} (hsize : ∀ a, (μB (r a) + 1 : ℝ) ≤ (K + 1 : ℝ) * (μ a + 1 : ℝ) ^ b)
    (hb : 0 ≤ b) (hp : 0 ≤ p) (hB : SolvesWithErrorInPowerExpTime B encB E μB p) :
    SolvesWithErrorInPowerExpTime A enc E μ (b * p) := by
  obtain ⟨e, he⟩ := ComputableInExpTime.of_computableInPolyTime (μ := fun _ => 0) hr
  rw [← max_eq_right (mul_nonneg hb hp)]
  exact hB.of_promiseReduction ⟨0, e, by simpa only [Nat.cast_zero, zero_mul] using he⟩
    hyes hno hsize hp

end Cslib.Complexity
