/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.Optimization
public import CslibFrontier.Computability.Circuit.Boolean.Iteration.SparseLookup

/-!
# Balancing a linear table against orbit length

A family of fixed-power circuits spends `a` gates per step and `2^n / L` gates for a
table of endpoints at length `L`, in addition to a shared half-word decoder. Integer rounding
and that decoder cost a constant factor in the square-root bound. For larger step costs, a
direct lookup of the whole truth table costs at most `19 * 2^n` gates.

## Main results

* `Cslib.Circuits.Boolean.Iteration.exists_circuit_of_endpoint_tradeoff` optimizes the integer
  parameter and chooses between the resulting circuit and the direct lookup.
-/

public section

namespace Cslib.Circuits.Boolean.Iteration

/-- The shared half-word decoder fits under twice the geometric mean whenever the step cost
is positive. -/
private theorem halfWord_le_sqrt {n a : ℕ} (ha : 0 < a) :
    (2 : ℝ) ^ ((n + 1) / 2) ≤ 2 * Real.sqrt ((2 : ℝ) ^ n * a) := by
  have hpow : (2 ^ ((n + 1) / 2) : ℕ) ^ 2 ≤ 2 * 2 ^ n := calc
    _ = 2 ^ (((n + 1) / 2) * 2) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by decide) (by lia)
    _ = _ := by rw [pow_succ, Nat.mul_comm]
  have hpow' : ((2 : ℝ) ^ ((n + 1) / 2)) ^ 2 ≤ 2 * 2 ^ n := by exact_mod_cast hpow
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hN : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ n * a := by
    simpa using mul_le_mul_of_nonneg_left ha' (show 0 ≤ (2 : ℝ) ^ n by positivity)
  have hz := Real.sq_sqrt (show 0 ≤ (2 : ℝ) ^ n * a by positivity)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  nlinarith

private theorem exists_endpointBudget_le {n a : ℕ} (ha : 0 < a) (haN : a ≤ 2 ^ n) :
    ∃ L : ℕ, 0 < L ∧ L ≤ 2 ^ n ∧
      (L * a + 2 ^ n / L + 2 ^ ((n + 1) / 2) : ℕ) ≤
        (8 : ℝ) * Real.sqrt ((2 : ℝ) ^ n * a) := by
  obtain ⟨L, hL, hLN, h⟩ := exists_le_three_mul_add_sqrt a 1 (2 ^ n) (2 ^ n)
    (by decide) ha le_rfl (by positivity)
  have haN' : (a : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast haN
  have haZ : (a : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ n * a) :=
    Real.le_sqrt_of_sq_le (by rw [sq]; gcongr)
  have hhalf := halfWord_le_sqrt (n := n) ha
  refine ⟨L, hL, hLN, ?_⟩
  push_cast at h ⊢
  simp only [one_mul] at h
  rw [mul_comm (L : ℝ)]
  linarith

/-- A full lookup has at most `19 * 2 ^ n` gates, including constants, at every width. -/
private theorem exists_denseLookup {n : ℕ} (f : BitString n → BitString n) :
    ∃ d : Circuit signature n n, d.Computes interpretation f ∧ d.size ≤ 19 * 2 ^ n := by
  obtain ⟨d, hd, hs⟩ := exists_sparseLookup Finset.univ f
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show (n + 1) / 2 ≤ n by lia)
  refine ⟨d, fun _ => hd (by simp), ?_⟩
  simp only [Finset.card_univ, BitString.card] at hs
  lia

/-- Optimize an endpoint tradeoff for an `n`-bit map with positive per-step cost `a`.
The direct full table gives the dense cap at every width. -/
theorem exists_circuit_of_endpoint_tradeoff {n a C : ℕ} (f : BitString n → BitString n)
    (ha : 0 < a) (tradeoff : ∀ L : ℕ, 0 < L → L ≤ 2 ^ n →
      ∃ d : Circuit signature n n, d.Computes interpretation f ∧
        d.size ≤ C * (L * a + 2 ^ n / L + 2 ^ ((n + 1) / 2))) :
    ∃ d : Circuit signature n n, d.Computes interpretation f ∧
      (d.size : ℝ) ≤ max 19 (8 * (C : ℝ)) *
        min ((2 : ℝ) ^ n) (Real.sqrt ((2 : ℝ) ^ n * a)) := by
  by_cases haN : a ≤ 2 ^ n
  · obtain ⟨L, hL, hLN, hopt⟩ := exists_endpointBudget_le ha haN
    obtain ⟨d, hd, hs⟩ := tradeoff L hL hLN
    refine ⟨d, hd, ?_⟩
    have haN' : (a : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast haN
    have hz : Real.sqrt ((2 : ℝ) ^ n * a) ≤ (2 : ℝ) ^ n :=
      (Real.sqrt_le_left (by positivity)).mpr (by rw [sq]; gcongr)
    rw [min_eq_right hz]
    calc
      _ ≤ (C : ℝ) * (L * a + 2 ^ n / L + 2 ^ ((n + 1) / 2) : ℕ) := by exact_mod_cast hs
      _ ≤ C * (8 * Real.sqrt ((2 : ℝ) ^ n * a)) :=
        mul_le_mul_of_nonneg_left hopt (Nat.cast_nonneg _)
      _ = (8 * C) * Real.sqrt ((2 : ℝ) ^ n * a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
  · obtain ⟨d, hd, hs⟩ := exists_denseLookup f
    refine ⟨d, hd, ?_⟩
    have hNa : (2 : ℝ) ^ n ≤ a := by exact_mod_cast (Nat.le_of_not_ge haN)
    have hz : (2 : ℝ) ^ n ≤ Real.sqrt ((2 : ℝ) ^ n * a) :=
      Real.le_sqrt_of_sq_le (by rw [sq]; gcongr)
    rw [min_eq_left hz]
    calc
      _ ≤ 19 * (2 : ℝ) ^ n := by exact_mod_cast hs
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end Cslib.Circuits.Boolean.Iteration
