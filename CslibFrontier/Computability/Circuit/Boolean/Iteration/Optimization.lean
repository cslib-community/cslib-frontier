/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Iteration
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Optimizing the checkpoint parameter

Balancing the two terms of `powerBudget` over the integer parameter `L` gives a fixed-power
circuit of size at most `80000 * (s' + √((n + 1) ^ 3 * M * s'))` with `s' = s + (n + 1) ^ 3`
(`fixed_power_on_optimized`): rounding the real balancing point costs at most a factor two.
A fixed checkpoint choice gives every fixed power a circuit of size at most
`120000 * (s + (n + 1) ^ 3) * 2 ^ ((n + 1) / 2)` (`fixed_power_half_exponent`), and transition
circuits of polynomial size give fixed powers of polynomial times half-exponential size
(`fixed_power_polynomial`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.optimizedBudget`: the balanced square-root budget.

## Main results

* `Cslib.Circuits.Boolean.Iteration.fixed_power_optimized`, `fixed_power_on_optimized`: the
  square-root bounds.
* `Cslib.Circuits.Boolean.Iteration.fixed_power_half_exponent`: a closed-form bound.
* `Cslib.Circuits.Boolean.Iteration.fixed_power_polynomial`: polynomial transition circuits.

## References

* Adapted from lean/Proofs/Optimization.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

/-- The polynomial overhead `(n + 1) ^ 3` is at most the fixed-power budget, for every parameter
`L`. -/
theorem cube_le_powerBudget (n s M L : ℕ) : (n + 1) ^ 3 ≤ powerBudget n s M L := by
  unfold powerBudget
  exact (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (Nat.le_add_left _ _)

/-- The balanced budget `s' + √((n + 1) ^ 3 * M * s')` with `s' = s + (n + 1) ^ 3`. -/
noncomputable def optimizedBudget (n s M : ℕ) : ℝ :=
  (s + (n + 1) ^ 3 : ℕ) + Real.sqrt ((n + 1 : ℝ) ^ 3 * M * (s + (n + 1) ^ 3 : ℕ))

/-- Rounding the balancing point of `a * L + b * (M / L + 1)` adds at most `a + b` to twice
the geometric mean. -/
theorem exists_le_add_add_two_mul_sqrt (a b M N : ℕ) (hb : 0 < b) (hba : b ≤ a)
    (hMN : M ≤ N) (hN : 0 < N) :
    ∃ L : ℕ, 0 < L ∧ L ≤ N ∧
      (a * L + b * (M / L + 1) : ℕ) ≤
        (a : ℝ) + b + 2 * Real.sqrt ((b : ℝ) * M * a) := by
  have ha : 0 < (a : ℝ) := by exact_mod_cast lt_of_lt_of_le hb hba
  have hb0 : 0 ≤ (b : ℝ) := by positivity
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast hba
  let q : ℝ := (b : ℝ) * M
  let z : ℝ := Real.sqrt (q * a)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hz2 : z ^ 2 = q * a := Real.sq_sqrt (by dsimp [q]; positivity)
  by_cases hsmall : q ≤ a
  · have hqz : q ≤ z := Real.le_sqrt_of_sq_le <| by
      rw [sq]
      exact mul_le_mul_of_nonneg_left hsmall (by dsimp [q]; positivity)
    refine ⟨1, by omega, hN, ?_⟩
    simp only [Nat.mul_one, Nat.div_one, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    change (a : ℝ) + b * (M + 1) ≤ a + b + 2 * z
    rw [mul_add, mul_one]
    dsimp only [q] at hqz
    linarith only [hqz, hz0]
  have hqa : (a : ℝ) ≤ q := (lt_of_not_ge hsmall).le
  have hza : (a : ℝ) ≤ z := (pow_le_pow_iff_left₀ ha.le hz0 two_ne_zero).mp
    (by rw [hz2, sq]; exact mul_le_mul_of_nonneg_right hqa ha.le)
  have hzpos : 0 < z := lt_of_lt_of_le ha hza
  have hM : 0 < M := Nat.pos_of_ne_zero fun h => by
    simp only [q, h, Nat.cast_zero, mul_zero] at hqa
    linarith only [ha, hqa]
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hzM : z ≤ (a : ℝ) * M := (pow_le_pow_iff_left₀ hz0 (by positivity) two_ne_zero).mp <| by
    rw [hz2]; dsimp [q]
    calc (b : ℝ) * M * a ≤ a * M * a := by gcongr
      _ = a * a * (M * 1) := by ring
      _ ≤ a * a * (M * M) := by gcongr
      _ = (a * M) ^ 2 := by ring
  let L := Nat.ceil (z / a)
  have hL : 0 < L := Nat.one_le_ceil_iff.mpr (div_pos hzpos ha)
  have hLM : L ≤ M := Nat.ceil_le.mpr ((div_le_iff₀ ha).mpr (by simpa [mul_comm] using hzM))
  have hlo : z ≤ (a : ℝ) * L :=
    ((div_le_iff₀ ha).mp (Nat.le_ceil (z / a))).trans_eq (mul_comm _ _)
  have hhi : (a : ℝ) * L ≤ z + a :=
    (mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (div_nonneg hz0 ha.le)) ha).le.trans_eq
      (by rw [mul_add, mul_div_cancel₀ _ ha.ne', mul_one])
  have hquot : ((M / L : ℕ) : ℝ) * L ≤ M := by exact_mod_cast Nat.div_mul_le_self M L
  have hterm : (b : ℝ) * (M / L : ℕ) ≤ z := le_of_mul_le_mul_right (a0 := hzpos) <|
    calc (b : ℝ) * (M / L : ℕ) * z ≤ b * (M / L : ℕ) * ((a : ℝ) * L) := by gcongr
      _ = b * (((M / L : ℕ) : ℝ) * L) * a := by ring
      _ ≤ b * M * a := by gcongr
      _ = z * z := by rw [← sq, hz2]
  refine ⟨L, hL, hLM.trans hMN, ?_⟩
  push_cast
  change (a : ℝ) * L + b * ((M / L : ℕ) + 1) ≤ a + b + 2 * z
  rw [mul_add, mul_one]
  linarith only [hhi, hterm]

/-- For any `M ≤ 2 ^ n`, there is a checkpoint parameter `0 < L ≤ 2 ^ n` with
`powerBudget n s M L ≤ 2 * optimizedBudget n s M`. -/
theorem exists_powerBudget_le_optimizedBudget (n s M : ℕ) (hM : M ≤ 2 ^ n) :
    ∃ L : ℕ, 0 < L ∧ L ≤ 2 ^ n ∧ (powerBudget n s M L : ℝ) ≤ 2 * optimizedBudget n s M := by
  obtain ⟨L, hL, hLN, h⟩ := exists_le_add_add_two_mul_sqrt (s + (n + 1) ^ 3) ((n + 1) ^ 3)
    M (2 ^ n) (by positivity) (by omega) hM (by positivity)
  refine ⟨L, hL, hLN, ?_⟩
  have he : powerBudget n s M L = (s + (n + 1) ^ 3) * L + (n + 1) ^ 3 * (M / L + 1) := by
    unfold powerBudget
    ring
  simp only [he, optimizedBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one] at h ⊢
  linarith only [h, show (0 : ℝ) ≤ s from Nat.cast_nonneg s]

/-- **Square-root fixed powers.** -/
theorem fixed_power_optimized {n : ℕ} (c : Circuit signature n n) (T : ℕ) :
    ∃ out : Circuit signature n n,
      out.Computes interpretation (c.eval interpretation)^[T] ∧
      (out.size : ℝ) ≤ 80000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_powerBudget_le_optimizedBudget n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := fixed_power n c T L hL hLN
  have hs' : (out.size : ℝ) ≤ 40000 * powerBudget n c.size (2 ^ n) L := mod_cast hs
  exact ⟨out, hout, by linarith⟩

/-- **Square-root fixed powers on an invariant set.** -/
theorem fixed_power_on_optimized {n : ℕ} (c : Circuit signature n n) (S : Finset (BitString n))
    (hS : ∀ x ∈ S, c.eval interpretation x ∈ S) (T : ℕ) :
    ∃ out : Circuit signature n n,
      out.ComputesOn interpretation ↑S (c.eval interpretation)^[T] ∧
      (out.size : ℝ) ≤ 80000 * optimizedBudget n c.size S.card := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_powerBudget_le_optimizedBudget n c.size S.card
    (by simpa using Finset.card_le_univ S)
  obtain ⟨out, hout, hs⟩ := fixed_power_on n c S T L hS hL hLN
  have hs' : (out.size : ℝ) ≤ 40000 * powerBudget n c.size S.card L := mod_cast hs
  exact ⟨out, hout, by linarith⟩

/-- A closed-form half-exponential bound. -/
theorem fixed_power_half_exponent {n : ℕ} (c : Circuit signature n n) (T : ℕ) :
    ∃ out : Circuit signature n n,
      out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤ 120000 * (c.size + (n + 1) ^ 3) * 2 ^ ((n + 1) / 2) := by
  let L := 2 ^ (n / 2)
  have hL : 0 < L := by positivity
  have hLN : L ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
  obtain ⟨out, hout, hs⟩ := fixed_power n c T L hL hLN
  have hdiv : 2 ^ n / L = 2 ^ (n - n / 2) := Nat.pow_div (Nat.div_le_self _ _) (by decide)
  have hlow : L ≤ 2 ^ ((n + 1) / 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hupp : 2 ^ (n - n / 2) ≤ 2 ^ ((n + 1) / 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hone : 1 ≤ 2 ^ ((n + 1) / 2) := Nat.one_le_two_pow
  have hp : powerBudget n c.size (2 ^ n) L ≤ 3 * (c.size + (n + 1) ^ 3) * 2 ^ ((n + 1) / 2) := by
    unfold powerBudget; rw [hdiv]
    refine (Nat.add_le_add (Nat.mul_le_mul_right c.size (by omega : L ≤ 3 * 2 ^ ((n + 1) / 2)))
      (Nat.mul_le_mul_left ((n + 1) ^ 3)
        (by omega : L + 2 ^ (n - n / 2) + 1 ≤ 3 * 2 ^ ((n + 1) / 2)))).trans_eq (by ring)
  refine ⟨out, hout, hs.trans ((Nat.mul_le_mul_left 40000 hp).trans_eq (by ring))⟩

/-- Transition circuits of size `K * (n + 1) ^ d` give fixed powers of size
`120000 * (K + 1) * (n + 1) ^ max d 3 * 2 ^ ((n + 1) / 2)`. -/
theorem fixed_power_polynomial {n : ℕ} (c : Circuit signature n n) (K d T : ℕ)
    (hs : c.size ≤ K * (n + 1) ^ d) :
    ∃ out : Circuit signature n n,
      out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤ 120000 * (K + 1) * (n + 1) ^ max d 3 * 2 ^ ((n + 1) / 2) := by
  obtain ⟨out, hout, ho⟩ := fixed_power_half_exponent c T
  have hd : (n + 1) ^ d ≤ (n + 1) ^ max d 3 :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h3 : (n + 1) ^ 3 ≤ (n + 1) ^ max d 3 :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have hc : c.size + (n + 1) ^ 3 ≤ (K + 1) * (n + 1) ^ max d 3 := by
    rw [add_mul, one_mul]; exact Nat.add_le_add (hs.trans (Nat.mul_le_mul_left K hd)) h3
  refine ⟨out, hout, ho.trans ?_⟩
  calc
    _ ≤ 120000 * ((K + 1) * (n + 1) ^ max d 3) * 2 ^ ((n + 1) / 2) := by gcongr
    _ = _ := by ring

end Cslib.Circuits.Boolean.Iteration
