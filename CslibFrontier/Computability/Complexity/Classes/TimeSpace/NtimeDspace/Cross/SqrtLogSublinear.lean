/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Polylog

/-!
# Sublinearity of `n / √log n`

The scale `SqrtLog n = n / ⌊√⌊log₂ n⌋⌋ + 1` satisfies `c · SqrtLog n + c ≤ n` eventually
for every constant `c`, which supplies the strict separation gap of the space hierarchy theorem.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open Filter

/-- The `n / √log n` scale. -/
def SqrtLog (n : ℕ) : ℕ := n / Nat.sqrt (n.log2) + 1

/-- For `m ≥ 4`, `m² ≤ 2^m`. -/
theorem sq_le_two_pow : ∀ m : ℕ, 4 ≤ m → m * m ≤ 2 ^ m
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, h => by omega
  | 4, _ => by decide
  | m + 5, _ => by
    have hm : 3 ≤ m + 4 := by omega
    have ih := sq_le_two_pow (m + 4) (by omega)
    have h1 : 2 * (m + 4) + 1 ≤ (m + 4) * (m + 4) := by nlinarith
    have h2 : (m + 5) * (m + 5) ≤ 2 * ((m + 4) * (m + 4)) := by
      calc (m + 5) * (m + 5) = (m + 4) * (m + 4) + (2 * (m + 4) + 1) := by ring
      _ ≤ (m + 4) * (m + 4) + (m + 4) * (m + 4) := Nat.add_le_add_left h1 _
      _ = 2 * ((m + 4) * (m + 4)) := by ring
    have h3 : 2 * ((m + 4) * (m + 4)) ≤ 2 * 2 ^ (m + 4) := Nat.mul_le_mul_left 2 ih
    have h4 : 2 * 2 ^ (m + 4) = 2 ^ (m + 5) := by rw [mul_comm, ← pow_succ]
    omega

/-- `log₂ n + 1 ≤ SqrtLog n` for every `n : ℕ`.
This verifies the logarithmic budget condition of `ProgLang.decidable_of_prog_len`. -/
theorem log2_add_one_le_sqrtLog (n : ℕ) : n.log2 + 1 ≤ SqrtLog n := by
  unfold SqrtLog
  rcases n with _ | _ | n
  · simp
  · simp
  have hn : n + 2 ≠ 0 := by omega
  have hl1 : 1 ≤ (n + 2).log2 := (Nat.le_log2 (by omega)).mpr (by omega)
  have hs1 : 1 ≤ ((n + 2).log2).sqrt := Nat.succ_le_of_lt (Nat.sqrt_pos.mpr hl1)
  have hs_le_l : ((n + 2).log2).sqrt ≤ (n + 2).log2 := Nat.sqrt_le_self _
  have hmul : (n + 2).log2 * ((n + 2).log2).sqrt ≤ n + 2 := by
    have hlog_eq : (n + 2).log2 = (n + 2).log2 := rfl
    generalize hL : (n + 2).log2 = L at hl1 hs1 hs_le_l hlog_eq
    have h2L : 2 ^ L ≤ n + 2 := hL ▸ Nat.log2_self_le hn
    rcases L with _ | _ | _ | _ | l'
    · omega
    · -- L = 1
      have : (1 : ℕ).sqrt = 1 := rfl
      rw [this]; omega
    · -- L = 2
      have h1 : 1 ≤ (2 : ℕ).sqrt := Nat.le_sqrt.mpr (by decide)
      have h2 : (2 : ℕ).sqrt < 2 := Nat.sqrt_lt.mpr (by decide)
      have : (2 : ℕ).sqrt = 1 := by omega
      rw [this]; omega
    · -- L = 3
      have h1 : 1 ≤ (3 : ℕ).sqrt := Nat.le_sqrt.mpr (by decide)
      have h2 : (3 : ℕ).sqrt < 2 := Nat.sqrt_lt.mpr (by decide)
      have : (3 : ℕ).sqrt = 1 := by omega
      have h8 : 2 ^ 3 = 8 := rfl
      rw [this]; omega
    · -- L = l' + 4 >= 4:
      have hsq : (l' + 4) * (l' + 4) ≤ 2 ^ (l' + 4) := sq_le_two_pow (l' + 4) (by omega)
      calc (l' + 4) * ((l' + 4).sqrt)
        _ ≤ (l' + 4) * (l' + 4) := Nat.mul_le_mul_left _ (Nat.sqrt_le_self _)
        _ ≤ 2 ^ (l' + 4) := hsq
        _ ≤ n + 2 := h2L
  have hdiv : (n + 2).log2 ≤ (n + 2) / ((n + 2).log2).sqrt :=
    Nat.le_div_iff_mul_le hs1 |>.mpr hmul
  have : (n + 1 + 1) = n + 2 := by omega
  rw [this]
  omega

/-- `√⌊log₂ N⌋ → ∞`. -/
theorem tendsto_sqrt_log2 : Tendsto (fun N : ℕ => Nat.sqrt (N.log2)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N0, hN0⟩ := (tendsto_atTop_atTop.mp NtimeDspace.Polylog.tendsto_log2) (b * b)
  refine ⟨N0, fun N hN => ?_⟩
  have := hN0 N hN
  exact Nat.le_sqrt.mpr this

/-- **Strict sublinearity of the `n / √log n` space bound.** -/
theorem sqrtLog_sublinear (c : ℕ) : ∀ᶠ n in atTop, c * SqrtLog n + c ≤ n := by
  obtain ⟨N0, hN0⟩ := (tendsto_atTop_atTop.mp tendsto_sqrt_log2) (2 * c + 2)
  refine eventually_atTop.mpr ⟨max N0 (4 * c + 4), fun n hn => ?_⟩
  have hn0 : N0 ≤ n := le_of_max_le_left hn
  have hnc : 4 * c + 4 ≤ n := le_of_max_le_right hn
  have hsqrt : 2 * c + 2 ≤ Nat.sqrt (n.log2) := hN0 n hn0
  have hle : (2 * c + 2) * (n / (2 * c + 2)) ≤ n := by
    rw [mul_comm]
    exact Nat.div_mul_le_self n (2 * c + 2)
  have hle2 : 2 * (c * (n / (2 * c + 2))) ≤ (2 * c + 2) * (n / (2 * c + 2)) := by
    have : 2 * c ≤ 2 * c + 2 := by omega
    have := Nat.mul_le_mul_right (n / (2 * c + 2)) this
    linarith
  have hdiv1 : c * (n / Nat.sqrt (n.log2)) ≤ c * (n / (2 * c + 2)) :=
    Nat.mul_le_mul_left c (Nat.div_le_div_left hsqrt (by omega))
  unfold SqrtLog
  rw [mul_add]
  omega

end Cslib.Complexity.NtimeDspace.Cross
