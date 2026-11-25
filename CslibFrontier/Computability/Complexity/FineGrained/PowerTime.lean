/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.FunctionRates
import CslibFrontier.Computability.Complexity.FineGrained.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Time bounds with a power in the exponent

The reduction rule charges both the reduction itself and the polynomial dependence on the
length of its output.

## Main definitions

* `Cslib.Complexity.DecidableInPowerExpTime`: time exponential in a power of a parameter,
  times a polynomial in the encoded input length.

## Main results

* `Cslib.Complexity.DecidableInPowerExpTime.mono_measure`: enlarge the instance parameter.
* `Cslib.Complexity.DecidableInPowerExpTime.of_reduction`: transfer along a reduction with an
  exponential time bound and a power bound on the target parameter.
* `Cslib.Complexity.DecidableInPowerExpTime.of_polyTime_reduction`: the polynomial-time
  reduction specialization.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {A : Set α} {B : Set β} {μA : α → ℕ} {μB : β → ℕ}

/-- Decidability in time `2 ^ (C * (μ a + 1) ^ p) * (L + 1) ^ e` up to constant factors, for some
constants `C` and `e`, with `L` the length of the encoded input. -/
@[expose] def DecidableInPowerExpTime (A : Set α) (enc : α ↪ List Bool) (μ : α → ℕ) (p : ℝ) :
    Prop :=
  ∃ C e : ℕ, DecidableInTimeO A enc
    fun a => (2 : ℝ) ^ (C * (μ a + 1 : ℝ) ^ p) * ((enc a).length + 1) ^ e

/-- At a nonnegative power, enlarging the instance parameter only relaxes the time bound. -/
theorem DecidableInPowerExpTime.mono_measure {ν : α → ℕ} {p : ℝ}
    (h : DecidableInPowerExpTime A encA μA p) (hμ : ∀ a, μA a ≤ ν a) (hp : 0 ≤ p) :
    DecidableInPowerExpTime A encA ν p := by
  obtain ⟨C, e, h⟩ := h
  refine ⟨C, e, h.mono 1 (fun a => ?_) (fun _ => by positivity)⟩
  have hbase : (μA a + 1 : ℝ) ≤ (ν a + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right (hμ a) 1
  have hparam := Real.rpow_le_rpow (by positivity : 0 ≤ (μA a + 1 : ℝ)) hbase hp
  exact (two_rpow_mul_pow_le_two_rpow_mul_pow
    (mul_le_mul_of_nonneg_left hparam (Nat.cast_nonneg C)) le_rfl).trans (by simp)

/-- If a many-one reduction takes time exponential in the `q`th power of its source parameter,
times a polynomial in input length, and has parameter blowup `O((μA + 1) ^ b)`, then a target
solver with power `p ≥ 0` gives a source solver with power `max q (b * p)`. -/
theorem DecidableInPowerExpTime.of_reduction {f : α → β} {q b p : ℝ}
    (hf : ∃ C d : ℕ, ComputableInTimeO f encA encB
      fun a => (2 : ℝ) ^ (C * (μA a + 1 : ℝ) ^ q) * ((encA a).length + 1) ^ d)
    (hmem : ∀ a, a ∈ A ↔ f a ∈ B) {K : ℕ}
    (hsize : ∀ a, (μB (f a) + 1 : ℝ) ≤ (K + 1 : ℝ) * (μA a + 1 : ℝ) ^ b)
    (hp : 0 ≤ p) (h : DecidableInPowerExpTime B encB μB p) :
    DecidableInPowerExpTime A encA μA (max q (b * p)) := by
  obtain ⟨C, d, hf⟩ := hf
  obtain ⟨t, c, hf, ht⟩ := hf.exists_computableInO
  obtain ⟨l, hl⟩ := hf.length_le_time
  obtain ⟨D, e, h⟩ := h
  obtain ⟨g, u, k, hg, hgB, hu⟩ := h.exists_computableInO
  let R : ℝ := D * (K + 1 : ℝ) ^ p
  let S : ℕ := ⌈R⌉₊ + C * (e + 1)
  let M : ℝ := (1 + k * (2 * l + 1 : ℝ) ^ e + k) * (2 * c + 1 : ℝ) ^ (e + 1)
  refine ⟨S, d * (e + 1),
    (DecidableInTimeO.of_computableInO (hg.comp hf)
      (fun a => (hmem a).trans (hgB (f a))) (T := fun a =>
        M * ((2 : ℝ) ^ (S * (μA a + 1 : ℝ) ^ max q (b * p)) *
          ((encA a).length + 1) ^ (d * (e + 1)))) fun a => ?_).mono
      ⌈M⌉₊ (fun a => ?_) (fun _ => by positivity)⟩
  · let x : ℝ := μA a + 1
    let y : ℝ := (encA a).length + 1
    let P : ℝ := (2 : ℝ) ^ (C * x ^ q) * y ^ d
    let X : ℝ := (2 : ℝ) ^ (R * x ^ (b * p))
    let P' : ℝ := (2 * c + 1 : ℝ) * P
    have hx : 1 ≤ x := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hP : 1 ≤ P :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (by positivity))
        (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)))
    have hP' : 1 ≤ P' := one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (by positivity)) hP
    have hX : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
    have ht' : (t a : ℝ) ≤ P' :=
      (le_two_mul_mul_of_le_mul_add (ht a) le_rfl hP).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    have hlen : ((encB (f a)).length : ℝ) ≤ l * (P' + 1) := by
      have hlen' : ((encB (f a)).length : ℝ) ≤ l * ((t a : ℝ) + 1) := by
        exact_mod_cast hl a
      exact hlen'.trans
        (mul_le_mul_of_nonneg_left (add_le_add ht' (le_refl (1 : ℝ))) (by positivity))
    have hy : (2 : ℝ) ^ (D * (μB (f a) + 1 : ℝ) ^ p) ≤ 1 * X := by
      rw [one_mul]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hb := Real.rpow_le_rpow (by positivity : 0 ≤ (μB (f a) + 1 : ℝ)) (hsize a) hp
      change _ ≤ R * x ^ (b * p)
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)] at hb
      simpa only [R, mul_assoc] using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg D)
    have hsum := reduction_add_time_le hP' hX (C := 1) (by norm_num) hlen hy (hu (f a))
    have hrate : X * P ^ (e + 1) ≤ (2 : ℝ) ^ (S * x ^ max q (b * p)) *
        y ^ (d * (e + 1)) := by
      dsimp only [X, P]
      rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (C * x ^ q)), ← Real.rpow_mul (by norm_num),
        ← mul_assoc, ← Real.rpow_add (by norm_num), ← pow_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h₁ := Real.rpow_le_rpow_of_exponent_le hx (le_max_left q (b * p))
      have h₂ := Real.rpow_le_rpow_of_exponent_le hx (le_max_right q (b * p))
      have h₃ := Nat.le_ceil R
      dsimp only [S]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left h₁
          (show 0 ≤ (C : ℝ) * (e + 1) by positivity),
        mul_le_mul_of_nonneg_left h₂ (show 0 ≤ R by positivity),
        mul_le_mul_of_nonneg_right h₃ (show 0 ≤ x ^ max q (b * p) by positivity)]
    have hsum' : (t a : ℝ) + u (f a) ≤ M * (X * P ^ (e + 1)) := by
      refine (add_le_add ht' le_rfl).trans (hsum.trans_eq ?_)
      dsimp only [P', M]
      rw [mul_pow]
      ring
    push_cast
    exact hsum'.trans (mul_le_mul_of_nonneg_left hrate (by positivity))
  · exact (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)).trans
      (le_add_of_nonneg_right (Nat.cast_nonneg _))

/-- Along a polynomial-time many-one reduction with parameter blowup `O((μA+1)^b)`, a target
solver with power `p` gives a source solver with power `b*p`. -/
theorem DecidableInPowerExpTime.of_polyTime_reduction {f : α → β} {b p : ℝ}
    (hf : ComputableInPolyTime f encA encB) (hmem : ∀ a, a ∈ A ↔ f a ∈ B) {K : ℕ}
    (hsize : ∀ a, (μB (f a) + 1 : ℝ) ≤ (K + 1 : ℝ) * (μA a + 1 : ℝ) ^ b)
    (hb : 0 ≤ b) (hp : 0 ≤ p) (h : DecidableInPowerExpTime B encB μB p) :
    DecidableInPowerExpTime A encA μA (b * p) := by
  obtain ⟨e, he⟩ := ComputableInExpTime.of_computableInPolyTime (μ := fun _ => 0) hf
  have hmax : max 0 (b * p) = b * p := max_eq_right (mul_nonneg hb hp)
  rw [← hmax]
  exact h.of_reduction ⟨0, e, by simpa [ComputableInExpTime] using he⟩ hmem hsize hp

end Cslib.Complexity
