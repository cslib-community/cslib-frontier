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

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], modules `Nc.Tow.Load4`, `Nc.Tow.Load3`,
`Nc.Tow.Load2` and `Nc.Tow.Cards`.

## Main definitions

* `Cslib.CoveringTower.Tower.incidentSum`: the sum of a load over the edges at a chamber.

## Main results

* `Cslib.CoveringTower.Tower.sum_ite_incidentSum`: the sums at the chambers with a property, by
  the edges and their ends.
* `Cslib.CoveringTower.Tower.sum_incidentSum`: the sums at all chambers are twice the load.
* `Cslib.CoveringTower.Tower.incidentSum_le`, `Cslib.CoveringTower.Tower.sum_incidentSum_le`:
  the bounds by the norm of the load.
* `Cslib.CoveringTower.Tower.two_mul_card_Ed`, `Cslib.CoveringTower.Tower.card_X_zero`,
  `Cslib.CoveringTower.Tower.pow_le_card_X_zero`: the numbers of edges and of chambers.
* `Cslib.CoveringTower.Tower.card_X_le`, `Cslib.CoveringTower.Tower.card_Ed_le`,
  `Cslib.CoveringTower.Tower.card_V_le`, `Cslib.CoveringTower.Tower.card_V_mul_card_Nr_le`:
  bounds for the numbers of chambers, edges and vertices by the chambers of the level `0`.
* `Cslib.CoveringTower.Tower.NN2_mono`, `Cslib.CoveringTower.Tower.nEnd_eq`: loads on pairs.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2 (proof: "One stage" and "Bounds", p. 47; "For (d)", p. 48); modules
  `Nc.Tow.Load4`, `Nc.Tow.Load3`, `Nc.Tow.Load2`, `Nc.Tow.Cards`
-/

public section

namespace Cslib.CoveringTower.Tower

open Finset

variable {h b D J r : ℕ} {T : Tower h b D J r} {j : ℕ}

variable (T) in
/-- The sum of a load on the edges of a level over the edges at the chamber `c`. -/
@[expose] def incidentSum (n : T.Ed j → ℕ) (c : T.X j) : ℕ :=
  ∑ e ∈ univ.filter fun e => T.e0 e = c ∨ T.e1 e = c, n e

/-- The sums at the chambers with a property, by the edges: every edge counts once for each of
its ends with the property. -/
theorem sum_ite_incidentSum (p : T.X j → Prop) [DecidablePred p] (n : T.Ed j → ℕ) :
    ∑ c, (if p c then T.incidentSum n c else 0) =
      ∑ e, ((if p (T.e0 e) then n e else 0) + if p (T.e1 e) then n e else 0) := by
  simp only [incidentSum, sum_filter, ite_sum_zero, ← ite_and]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  have hne := T.e_ne e
  rw [Fintype.sum_eq_add _ _ hne fun c hc => by grind]
  simp [hne]

/-- Every edge has two ends, so the sums at all chambers add up to twice the load. -/
theorem sum_incidentSum (n : T.Ed j → ℕ) : ∑ c, T.incidentSum n c = 2 * ∑ e, n e := by
  simpa [two_mul, sum_add_distrib] using sum_ite_incidentSum (T := T) (fun _ => True) n

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

/-- The levels shrink: a level `j ≤ J` has at most as many chambers as the level `0`. -/
theorem card_X_le (hD : 0 < D) (hj : j ≤ J) : Fintype.card (T.X j) ≤ Fintype.card (T.X 0) :=
  (card_X_zero hj).symm ▸ Nat.le_mul_of_pos_left _ (Nat.pow_pos hD)

/-- The level `0` has at least `D ^ J` chambers if the level `J` has one. -/
theorem pow_le_card_X_zero (hX : 0 < Fintype.card (T.X J)) : D ^ J ≤ Fintype.card (T.X 0) :=
  (card_X_zero le_rfl).trans_ge (Nat.le_mul_of_pos_right _ hX)

/-- A level `j ≤ J` has at most `h r` edges for every chamber of the level `0`. -/
theorem card_Ed_le (hD : 0 < D) (hj : j ≤ J) :
    Fintype.card (T.Ed j) ≤ h * r * Fintype.card (T.X 0) := by
  have := two_mul_card_Ed (T := T) hj
  have := Nat.mul_le_mul_left (h * r) (card_X_le (T := T) hD hj)
  rw [mul_assoc] at this
  omega

/-- A level `j ≤ J` has at most as many vertices of a type as the level `0` has chambers. -/
theorem card_V_le (hD : 0 < D) (hb : 0 < b) (hj : j ≤ J) (i : Fin h) :
    Fintype.card (T.V j i) ≤ Fintype.card (T.X 0) :=
  (Nat.le_mul_of_pos_right _ hb).trans ((T.card_V hj i).trans_le (card_X_le hD hj))

/-- The near pairs at the vertices of a type are edges of the other types. -/
theorem card_V_mul_card_Nr_le (hj : j ≤ J) (i : Fin h) :
    Fintype.card (T.V j i) * Fintype.card T.Nr ≤ Fintype.card (T.Ed j) := by
  rw [← Fintype.card_prod, ← Fintype.card_congr (T.nr hj i)]
  exact Fintype.card_subtype_le _

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
    rcases (by exact_mod_cast Nat.eq_zero_or_pos b : (b : ℝ) = 0 ∨ 1 ≤ (b : ℝ)) with h | h <;>
      nlinarith
  rw [NN2_def, NN2_def]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun q _ => ?_) hb
  split_ifs <;> gcongr
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
