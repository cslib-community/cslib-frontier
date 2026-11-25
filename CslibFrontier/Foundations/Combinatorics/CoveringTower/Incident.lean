/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.CoveringTower.Load
import Mathlib.Algebra.Order.Chebyshev

/-!
# Loads at the chambers of a tower

For a load `n` on the edges of a level of a `Cslib.CoveringTower.Tower`, `Tower.incidentSum n c`
adds the loads of the edges at the chamber `c`. Every edge has two ends, so these sums add up to
twice the load, and by the Cauchy–Schwarz inequality over the at most `h r` edges at a chamber
they are bounded by the norm `Tower.kap` of the load, at every chamber and in total. The file also
counts the edges of a level and the chambers of the level `0`, shows that the norm `Tower.NN2` of
a load on pairs is monotone, and writes the end segments `Tower.nEnd` by the edges and their two
ends.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], modules `Nc.Tow.Load4`, `Nc.Tow.Load3` and
`Nc.Tow.Load2`.

## Main definitions

* `Cslib.CoveringTower.Tower.incidentSum`: the sum of a load over the edges at a chamber.

## Main results

* `Cslib.CoveringTower.Tower.sum_incidentSum`: the sums at all chambers are twice the load.
* `Cslib.CoveringTower.Tower.incidentSum_le`, `Cslib.CoveringTower.Tower.sum_incidentSum_le`:
  the bounds by the norm of the load.
* `Cslib.CoveringTower.Tower.two_mul_card_Ed`, `Cslib.CoveringTower.Tower.card_X_zero`: the
  numbers of edges and of chambers.
* `Cslib.CoveringTower.Tower.NN2_mono`, `Cslib.CoveringTower.Tower.nEnd_eq`: loads on pairs.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2 (proof: "One stage" and "Bounds", p. 47); modules `Nc.Tow.Load4`, `Nc.Tow.Load3`,
  `Nc.Tow.Load2`
-/

public section

namespace Cslib.CoveringTower.Tower

open Finset

variable {h b D J r : ℕ} {T : Tower h b D J r} {j : ℕ}

variable (T) in
/-- The sum of a load on the edges of a level over the edges at the chamber `c`. -/
@[expose] def incidentSum (n : T.Ed j → ℕ) (c : T.X j) : ℕ :=
  ∑ e ∈ univ.filter fun e => T.e0 e = c ∨ T.e1 e = c, n e

/-- Every edge has two ends, so the sums at all chambers add up to twice the load. -/
theorem sum_incidentSum (n : T.Ed j → ℕ) : ∑ c, T.incidentSum n c = 2 * ∑ e, n e := by
  simp only [incidentSum, sum_filter]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [← sum_filter, sum_const, smul_eq_mul,
    show univ.filter (fun c => T.e0 e = c ∨ T.e1 e = c) = {T.e0 e, T.e1 e} by ext; simp [eq_comm],
    card_pair (T.e_ne e), mul_comm]

/-- The edges of all types at a chamber of a level `j ≤ J`. -/
private theorem card_incident_le (hj : j ≤ J) (c : T.X j) :
    (univ.filter fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c).card ≤ h * r := by
  rw [card_eq_sum_card_fiberwise fun e _ => mem_univ (T.ty e)]
  calc _ ≤ ∑ _i : Fin h, r := sum_le_sum fun i _ => (card_le_card fun e he => by
          simp_all [and_comm]).trans (T.deg j hj c i)
    _ = h * r := by simp

/-- The edges of a level `j ≤ J`: `r / 2` of every type per chamber. -/
theorem two_mul_card_Ed (hj : j ≤ J) :
    2 * Fintype.card (T.Ed j) = h * (r * Fintype.card (T.X j)) := by
  rw [← card_univ, card_eq_sum_card_fiberwise fun e _ => mem_univ (T.ty e), mul_sum]
  simp [T.card_ed j hj]

/-- The chambers of the level `0` are `D ^ j` times those of the level `j ≤ J`. -/
theorem card_X_zero (hj : j ≤ J) : Fintype.card (T.X 0) = D ^ j * Fintype.card (T.X j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [ih (by omega), T.card_X j (by omega), pow_succ, mul_assoc]

/-- The sum at a chamber of a level `j ≤ J` is bounded by the norm of the load. -/
theorem incidentSum_le (hj : j ≤ J) (n : T.Ed j → ℕ) (c : T.X j) :
    (T.incidentSum n c : ℝ) ≤ √(2 * h / Fintype.card (T.X j)) * T.kap n := by
  have hX : (0 : ℝ) < Fintype.card (T.X j) := by exact_mod_cast Fintype.card_pos_iff.2 ⟨c⟩
  rw [← Real.sqrt_sq (kap_nonneg n), ← Real.sqrt_mul (by positivity), kap_sq]
  refine (Real.le_sqrt (Nat.cast_nonneg _) (by positivity)).2 ?_
  calc (T.incidentSum n c : ℝ) ^ 2 ≤ (univ.filter fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c).card *
        ∑ e ∈ univ.filter fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c, (n e : ℝ) ^ 2 := by
        rw [incidentSum, Nat.cast_sum]
        exact sq_sum_le_card_mul_sum_sq
    _ ≤ (h * r : ℕ) * ∑ e, (n e : ℝ) ^ 2 := by
        gcongr
        · exact card_incident_le hj c
        · exact subset_univ _
    _ = _ := by
        field_simp
        push_cast
        ring

/-- The sums at all chambers of a level `j ≤ J` are bounded by the norm of the load. -/
theorem sum_incidentSum_le (hj : j ≤ J) (n : T.Ed j → ℕ) :
    ((∑ c, T.incidentSum n c : ℕ) : ℝ) ≤ 2 * (√h * T.kap n) := by
  have h2 : (2 * Fintype.card (T.Ed j) : ℝ) = h * (r * Fintype.card (T.X j)) := by
    exact_mod_cast two_mul_card_Ed hj
  rw [sum_incidentSum, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
  gcongr
  rw [← Real.sqrt_sq (kap_nonneg n), ← Real.sqrt_mul (Nat.cast_nonneg _), kap_sq]
  refine (Real.le_sqrt (sum_nonneg fun e _ => Nat.cast_nonneg _) (by positivity)).2 ?_
  refine sq_sum_le_card_mul_sum_sq.trans_eq ?_
  rw [card_univ, show (Fintype.card (T.Ed j) : ℝ) = h * (r * Fintype.card (T.X j)) / 2 by
    linarith]
  ring

/-- The norm of a load on the pairs of places is monotone. -/
theorem NN2_mono {n n' : Sym2 T.Fl → ℕ} (hn : ∀ q, n q ≤ n' q) : T.NN2 n ≤ T.NN2 n' := by
  have hb : (0 : ℝ) ≤ b * (b - 1) / 2 := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have : (1 : ℝ) ≤ b := by exact_mod_cast hb
      have : (0 : ℝ) ≤ b - 1 := by linarith
      positivity
  rw [NN2_def, NN2_def]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun q _ => ?_) hb
  split_ifs
  · exact le_rfl
  · gcongr
    exact hn q

/-- The end segments on the pair `q` of the vertex `ω`, by the edges of the type `i` and their
two ends. -/
theorem nEnd_eq (i : Fin h) (n : T.Ed j → ℕ) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    T.nEnd i n ω q =
      (∑ e, if T.ty e = i ∧ T.πV (T.vx i (T.e0 e)) = ω ∧
        s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q then n e else 0) +
      ∑ e, if T.ty e = i ∧ T.πV (T.vx i (T.e1 e)) = ω ∧
        s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q then n e else 0 := by
  rw [nEnd_def, ← sum_add_distrib]
  simp only [be_def]
  calc _ = ∑ c, ∑ e, if (T.πV (T.vx i c) = ω ∧ s(T.co i (T.host i (T.vx i c)), T.co i c) = q) ∧
        T.ty e = i ∧ (T.e0 e = c ∨ T.e1 e = c) then n e else 0 :=
        sum_congr rfl fun c _ => by split_ifs with hc <;> simp [hc]
    _ = _ := by
        rw [sum_comm]
        refine sum_congr rfl fun e _ => ?_
        have hne := T.e_ne e
        rw [Fintype.sum_eq_add _ _ hne fun c hc =>
          ite_eq_right_iff.2 fun h => absurd h.2.2 (by rintro (h | h) <;> simp_all)]
        simp [hne, hne.symm, and_comm]

end Cslib.CoveringTower.Tower
