/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.PrimeCollision
public import CslibFrontier.Foundations.NumberTheory.PrimeWindow

/-!
# Collisions in closed prime windows

This is a quantified interpretation of [Goldreich2007DraftR5], Exercise 9.7
(`r5.pdf`, PDF64/printed446). The source says only `L = poly(log M)`;
it specifies neither an error parameter nor a polynomial degree.
For every positive error tolerance, one constant works for all input bounds,
window sizes and fixed distinct pairs. This is a pairwise statement, not a
simultaneous guarantee for every pair. Uniform sampling is among the primes;
no efficient prime sampler or runtime bound is asserted.

## Main results

* `Nat.exists_closedPrimes_collision_bound`: nonempty windows and pairwise error bounds.
* `Nat.exists_ceil_closedPrimes_collision_bound`: natural sizes at the quadratic threshold.
-/

public section

namespace Nat

/-- The primes in the closed interval `[lo, hi]`. -/
@[expose] def closedPrimes (lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc lo hi).filter Nat.Prime

private theorem sqrt_card {c x : ℝ} (hc : 0 < c) (hx : 4 ≤ x)
    {S : Finset ℕ} (hS : c * (x / Real.log x) ≤ (S.card : ℝ)) :
    c * Real.sqrt x / 2 ≤ (S.card : ℝ) := by
  have hs := Real.sq_sqrt (show 0 ≤ x by linarith)
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have := Real.log_le_rpow_div (show 0 ≤ x by linarith)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this
    linarith
  have hp : 0 < Real.log x := Real.log_pos (by linarith)
  have h : Real.sqrt x / 2 ≤ x / Real.log x := (le_div_iff₀ hp).mpr <|
    calc Real.sqrt x / 2 * Real.log x ≤ Real.sqrt x / 2 * (2 * Real.sqrt x) := by gcongr
      _ = Real.sqrt x ^ 2 := by ring
      _ = x := hs
  calc c * Real.sqrt x / 2 = c * (Real.sqrt x / 2) := by ring
    _ ≤ c * (x / Real.log x) := by gcongr
    _ ≤ S.card := hS

/-- One positive density constant bounds both closed windows by a square root. -/
private theorem exists_sqrt_card_closedPrimes :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℕ, 6 ≤ L →
      c * Real.sqrt L / 2 ≤ ((closedPrimes 3 L).card : ℝ) ∧
      c * Real.sqrt L / 2 ≤ ((closedPrimes L (2 * L)).card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := exists_forall_mul_div_log_le_card_primes
  refine ⟨c, hc, fun L hL => ?_⟩
  have hLr : (6 : ℝ) ≤ L := by exact_mod_cast hL
  constructor
  · refine sqrt_card hc (by linarith) (hcount _ (by linarith) _ fun p hp hlo hhi =>
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by exact_mod_cast (by linarith : (3 : ℝ) ≤ p),
        by exact_mod_cast hhi.le⟩, hp⟩)
  · have h := sqrt_card hc (show (4 : ℝ) ≤ 2 * L by linarith)
      (hcount (2 * L) (by linarith) (closedPrimes L (2 * L)) fun p hp hlo hhi =>
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by exact_mod_cast (by linarith : (L : ℝ) ≤ p),
          by exact_mod_cast hhi.le⟩, hp⟩)
    have hs : Real.sqrt (L : ℝ) ≤ Real.sqrt (2 * L) := Real.sqrt_le_sqrt (by linarith)
    exact (by gcongr : c * Real.sqrt L / 2 ≤ c * Real.sqrt (2 * L) / 2).trans h

/-- Quantified interpretation of Exercise 9.7 for both closed prime windows.
The same `C` works for every `M`, `L` and fixed pair `a ≠ b`. -/
theorem exists_closedPrimes_collision_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M L : ℕ, 2 ≤ M →
      C * (Nat.log2 M : ℝ) ^ 2 ≤ L →
      ∀ Q ∈ [closedPrimes 3 L, closedPrimes L (2 * L)],
        Q.Nonempty ∧ ∀ a b : ℕ, a ≤ M → b ≤ M → a ≠ b →
          ((Q.filter fun p => Nat.ModEq p a b).card : ℝ) / Q.card ≤ δ := by
  obtain ⟨c, hc, hcount⟩ := exists_sqrt_card_closedPrimes
  let C : ℝ := max 6 (4 / (c ^ 2 * δ ^ 2))
  refine ⟨C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro M L hM hL Q hQ
  have hk : (1 : ℝ) ≤ Nat.log2 M := by
    exact_mod_cast (show 1 ≤ Nat.log2 M by
      rw [Nat.log2_eq_log_two]
      exact Nat.le_log_of_pow_le (by norm_num) (by simpa using hM))
  have hC6 : 6 ≤ C := le_max_left _ _
  have hC : 4 / (c ^ 2 * δ ^ 2) ≤ C := le_max_right _ _
  have hL6 : 6 ≤ L := by
    exact_mod_cast (calc (6 : ℝ) = 6 * 1 ^ 2 := by norm_num
      _ ≤ C * (Nat.log2 M : ℝ) ^ 2 := by gcongr
      _ ≤ L := hL)
  have hcards := hcount L hL6
  have hcard : c * Real.sqrt L / 2 ≤ (Q.card : ℝ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl
    · exact hcards.1
    · exact hcards.2
  have hpr : ∀ p ∈ Q, p.Prime := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl <;> exact fun p hp => (Finset.mem_filter.mp hp).2
  have hscale : 4 * (Nat.log2 M : ℝ) ^ 2 ≤ (L : ℝ) * (c ^ 2 * δ ^ 2) := by
    have h4 : 4 ≤ C * (c ^ 2 * δ ^ 2) := (div_le_iff₀ (by positivity)).mp hC
    calc 4 * (Nat.log2 M : ℝ) ^ 2 ≤ C * (c ^ 2 * δ ^ 2) * (Nat.log2 M : ℝ) ^ 2 := by gcongr
      _ = C * (Nat.log2 M : ℝ) ^ 2 * (c ^ 2 * δ ^ 2) := by ring
      _ ≤ (L : ℝ) * (c ^ 2 * δ ^ 2) := by gcongr
  have hlarge : (Nat.log2 M : ℝ) ≤ δ * (Q.card : ℝ) := by
    have hsq : (2 * (Nat.log2 M : ℝ)) ^ 2 ≤ (c * δ * Real.sqrt L) ^ 2 :=
      calc (2 * (Nat.log2 M : ℝ)) ^ 2 = 4 * (Nat.log2 M : ℝ) ^ 2 := by ring
        _ ≤ (L : ℝ) * (c ^ 2 * δ ^ 2) := hscale
        _ = (c * δ * Real.sqrt L) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg L)]; ring
    have hlin : 2 * (Nat.log2 M : ℝ) ≤ c * δ * Real.sqrt L :=
      (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
    calc (Nat.log2 M : ℝ) = (2 * (Nat.log2 M : ℝ)) / 2 := by ring
      _ ≤ (c * δ * Real.sqrt L) / 2 := by gcongr
      _ = δ * (c * Real.sqrt L / 2) := by ring
      _ ≤ δ * (Q.card : ℝ) := by gcongr
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hcardpos : 0 < (Q.card : ℝ) := lt_of_lt_of_le (by positivity) hcard
  refine ⟨Finset.card_pos.mp (by exact_mod_cast hcardpos), ?_⟩
  intro a b ha hb hne
  apply (div_le_iff₀ hcardpos).mpr
  have hbad : ((Q.filter fun p => Nat.ModEq p a b).card : ℝ) ≤ Nat.log2 M := by
    exact_mod_cast card_filter_modEq_le_log hpr ha hb hne
  exact hbad.trans hlarge

/-- Choosing the ceiling of the quadratic threshold gives natural window sizes. -/
theorem exists_ceil_closedPrimes_collision_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M →
      let L := ⌈C * (Nat.log2 M : ℝ) ^ 2⌉₊
      ∀ Q ∈ [closedPrimes 3 L, closedPrimes L (2 * L)],
        Q.Nonempty ∧ ∀ a b : ℕ, a ≤ M → b ≤ M → a ≠ b →
          ((Q.filter fun p => Nat.ModEq p a b).card : ℝ) / Q.card ≤ δ := by
  obtain ⟨C, hC, hbound⟩ := exists_closedPrimes_collision_bound hδ
  exact ⟨C, hC, fun M hM => hbound M _ hM (Nat.le_ceil _)⟩

end Nat
