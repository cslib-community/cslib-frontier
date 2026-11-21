/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Zones
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Log

/-!
# The cost of moves on a zoned track

A move at level `j` (`ZTrack.trig`) rewrites `O(2 ^ j)` symbols. This file proves that a run of
`n` moves from a *balanced* track, in which every zone is half full, has
`∑ 2 ^ j ≤ n (log₂ (n + 1) + 1)` (`ZTrack.cost_le`).

For a level `ℓ ≥ 1`, let `count ℓ` be the number of symbols in the right zones below `ℓ`, between
`0` and `2 ^ (ℓ + 1) - 2`, and `dist ℓ` its distance to the nearer end. A move reaching level `ℓ`
needs `dist ℓ = 0` (`dist_eq_zero_of_le_trig`) and leaves `dist ℓ = 2 ^ ℓ - 1`
(`dist_move_of_le_trig`), while any other move lowers `dist ℓ` by at most one
(`dist_le_dist_move_add_one`). So moves reaching level `ℓ` are at least `2 ^ ℓ - 1` moves apart
(`nGe_mul_le`), and summing over the levels gives the bound.

## Main definitions

* `Turing.MultiTapeTM.HennieStearns.ZTrack.cost`: `∑ 2 ^ j` over a run of moves.
* `ZTrack.Balanced`: every zone half full.

## Main results

* `Turing.MultiTapeTM.HennieStearns.ZTrack.cost_le`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

namespace ZTrack

variable {Symbol : Type*}

/-- The track after a run of moves. -/
def run : ZTrack Symbol → ℕ → List Side → ZTrack Symbol
  | Z, _, [] => Z
  | Z, J, s :: ss => run (Z.move J s) (J + 1) ss

/-- `∑ 2 ^ j` over the levels `j` of a run of moves. -/
def cost : ZTrack Symbol → ℕ → List Side → ℕ
  | _, _, [] => 0
  | Z, J, s :: ss => 2 ^ Z.trig J s + cost (Z.move J s) (J + 1) ss

/-- The number of moves of a run reaching level `ℓ`. -/
def nGe (ℓ : ℕ) : ZTrack Symbol → ℕ → List Side → ℕ
  | _, _, [] => 0
  | Z, J, s :: ss => (if ℓ ≤ Z.trig J s then 1 else 0) + nGe ℓ (Z.move J s) (J + 1) ss

/-- Every zone is half full. -/
def Balanced (Z : ZTrack Symbol) : Prop := ∀ s j, (Z.zone s j).length = 2 ^ j

/-- The number of symbols in the right zones below level `ℓ`. -/
def count (Z : ZTrack Symbol) (ℓ : ℕ) : ℕ := ((List.range ℓ).map fun k => (Z.zone .R k).length).sum

/-- The distance of `count ℓ` to the nearer of its extremes `0` and `2 ^ (ℓ + 1) - 2`. -/
def dist (Z : ZTrack Symbol) (ℓ : ℕ) : ℕ := min (Z.count ℓ) (2 ^ (ℓ + 1) - 2 - Z.count ℓ)

variable {Z : ZTrack Symbol} {J : ℕ}

lemma count_succ (Z : ZTrack Symbol) (ℓ : ℕ) :
    Z.count (ℓ + 1) = Z.count ℓ + (Z.zone .R ℓ).length := by
  simp [count, List.range_succ]

lemma count_le (hV : Z.Valid J) (ℓ : ℕ) : Z.count ℓ ≤ 2 ^ (ℓ + 1) - 2 := by
  induction ℓ with
  | zero => simp [count]
  | succ ℓ ih =>
    rw [count_succ]
    have := hV.sum ℓ
    have := Nat.one_le_two_pow (n := ℓ)
    rw [pow_succ] at *
    rw [pow_succ]
    omega

lemma dist_le (Z : ZTrack Symbol) (ℓ : ℕ) : Z.dist ℓ ≤ 2 ^ ℓ - 1 := by
  simp only [dist]
  rw [pow_succ]
  omega

/-- The count of a balanced track is in the middle. -/
lemma count_of_balanced (hB : Z.Balanced) (ℓ : ℕ) : Z.count ℓ = 2 ^ ℓ - 1 := by
  induction ℓ with
  | zero => simp [count]
  | succ ℓ ih =>
    rw [count_succ, ih, hB, pow_succ]
    have := Nat.one_le_two_pow (n := ℓ)
    omega

lemma dist_of_balanced (hB : Z.Balanced) (ℓ : ℕ) : Z.dist ℓ = 2 ^ ℓ - 1 := by
  simp only [dist, count_of_balanced hB, pow_succ]
  omega

/-- A move reaching level `ℓ` needs the count below `ℓ` at an extreme. -/
lemma dist_eq_zero_of_le_trig (hV : Z.Valid J) {s : Side} {ℓ : ℕ} (hℓ : ℓ ≤ Z.trig J s) :
    Z.dist ℓ = 0 := by
  cases s with
  | R =>
    have : Z.count ℓ = 0 := List.sum_eq_zero fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      rw [zone_of_lt_trig hV (lt_of_lt_of_le (List.mem_range.1 hk) hℓ), List.length_nil]
    simp [dist, this]
  | L =>
    have : ∀ n ≤ ℓ, Z.count n = 2 ^ (n + 1) - 2 := by
      intro n hn
      induction n with
      | zero => simp [count]
      | succ n ih =>
        rw [count_succ, ih (by omega)]
        have h := length_zone_other_of_lt_trig hV (s := .L) (k := n) (by omega)
        simp only [Side.other] at h
        rw [h]
        have := Nat.one_le_two_pow (n := n)
        rw [pow_succ, pow_succ, pow_succ]
        omega
    simp [dist, this ℓ le_rfl]

/-- A move reaching level `ℓ` leaves the count below `ℓ` in the middle. -/
lemma dist_move_of_le_trig (hV : Z.Valid J) {s : Side} {ℓ : ℕ} (hℓ : ℓ ≤ Z.trig J s) :
    (Z.move J s).dist ℓ = 2 ^ ℓ - 1 := by
  have : ∀ n ≤ ℓ, (Z.move J s).count n = 2 ^ n - 1 := by
    intro n hn
    induction n with
    | zero => simp [count]
    | succ n ih =>
      rw [count_succ, ih (by omega), length_zone_move_of_lt hV _ (by omega), pow_succ]
      have := Nat.one_le_two_pow (n := n)
      omega
  simp only [dist, this ℓ le_rfl, pow_succ]
  omega

/-- Above its level, a move changes the count below `ℓ` by one. -/
lemma count_move_of_trig_lt (hV : Z.Valid J) {s : Side} {ℓ : ℕ} (hℓ : Z.trig J s < ℓ) :
    (Z.move J s).count ℓ + (if s = .R then 1 else 0) =
      Z.count ℓ + (if s = .R then 0 else 1) := by
  induction ℓ with
  | zero => omega
  | succ ℓ ih =>
    rw [count_succ, count_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hℓ with h | h
    · rw [zone_move_of_lt h]
      have := ih h
      omega
    · -- the level of the move: count the levels up to it
      subst h
      have hlow : (Z.move J s).count (Z.trig J s) = 2 ^ Z.trig J s - 1 := by
        have : ∀ n ≤ Z.trig J s, (Z.move J s).count n = 2 ^ n - 1 := by
          intro n hn
          induction n with
          | zero => simp [count]
          | succ n ih' =>
            rw [count_succ, ih' (by omega), length_zone_move_of_lt hV _ (by omega), pow_succ]
            have := Nat.one_le_two_pow (n := n)
            omega
        exact this _ le_rfl
      have hsrc := length_zone_trig hV s
      have := Nat.one_le_two_pow (n := Z.trig J s)
      cases s with
      | R =>
        have hold : Z.count (Z.trig J .R) = 0 := List.sum_eq_zero fun x hx => by
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
          rw [zone_of_lt_trig hV (List.mem_range.1 hk), List.length_nil]
        rw [hlow, hold, length_zone_move_self_trig hV]
        simp only [↓reduceIte]
        omega
      | L =>
        have hold : ∀ n ≤ Z.trig J .L, Z.count n = 2 ^ (n + 1) - 2 := by
          intro n hn
          induction n with
          | zero => simp [count]
          | succ n ih' =>
            rw [count_succ, ih' (by omega)]
            have h := length_zone_other_of_lt_trig hV (s := .L) (k := n) (by omega)
            simp only [Side.other] at h
            rw [h]
            have := Nat.one_le_two_pow (n := n)
            rw [pow_succ, pow_succ, pow_succ]
            omega
        have h := length_zone_move_other_trig hV .L
        simp only [Side.other] at h
        rw [hlow, hold _ le_rfl, h]
        simp only [reduceCtorEq, ↓reduceIte]
        rw [pow_succ]
        omega

/-- Any move lowers `dist ℓ` by at most one. -/
lemma dist_le_dist_move_add_one (hV : Z.Valid J) (s : Side) (ℓ : ℕ) :
    Z.dist ℓ ≤ (Z.move J s).dist ℓ + 1 := by
  by_cases hℓ : ℓ ≤ Z.trig J s
  · rw [dist_eq_zero_of_le_trig hV hℓ]
    omega
  · have h := count_move_of_trig_lt hV (s := s) (ℓ := ℓ) (by omega)
    have h₁ := count_le hV ℓ
    have h₂ := count_le (hV.move s) ℓ
    simp only [dist]
    cases s <;> simp only [↓reduceIte, reduceCtorEq] at h <;> omega

/-- **Moves reaching level `ℓ` are `2 ^ ℓ - 1` apart.** -/
lemma nGe_mul_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∀ (ss : List Side) (Z : ZTrack Symbol) (J : ℕ), Z.Valid J →
      Z.nGe ℓ J ss * (2 ^ ℓ - 1) ≤ ss.length + (2 ^ ℓ - 1 - Z.dist ℓ)
  | [], _, _, _ => by simp [nGe]
  | s :: ss, Z, J, hV => by
    have ih := nGe_mul_le hℓ ss (Z.move J s) (J + 1) (hV.move s)
    simp only [nGe, List.length_cons]
    by_cases h : ℓ ≤ Z.trig J s
    · rw [dist_move_of_le_trig hV h] at ih
      rw [dist_eq_zero_of_le_trig hV h]
      simp only [h, ↓reduceIte]
      have := Nat.one_le_two_pow (n := ℓ)
      rw [add_mul]
      omega
    · have := dist_le_dist_move_add_one hV s ℓ
      have := dist_le (Z.move J s) ℓ
      simp only [h, ↓reduceIte, zero_add]
      omega

lemma one_add_sum_two_pow (B : ℕ) : 1 + ∑ ℓ ∈ Finset.range B, 2 ^ ℓ = 2 ^ B := by
  induction B with
  | zero => simp
  | succ B ih => rw [Finset.sum_range_succ, ← add_assoc, ih, pow_succ]; ring

lemma sum_two_pow_ite {j : ℕ} : ∀ B, j ≤ B →
    ∑ ℓ ∈ Finset.range B, 2 ^ ℓ * (if ℓ + 1 ≤ j then 1 else 0) =
      ∑ ℓ ∈ Finset.range j, 2 ^ ℓ
  | 0, h => by simp [show j = 0 by omega]
  | B + 1, h => by
    rcases Nat.lt_or_ge B j with hB | hB
    · have hj : j = B + 1 := by omega
      subst hj
      exact Finset.sum_congr rfl fun ℓ hℓ => by
        simp [show ℓ + 1 ≤ B + 1 by simp at hℓ; omega]
    · rw [Finset.sum_range_succ, sum_two_pow_ite B hB]
      simp [show ¬ B + 1 ≤ j by omega]

/-- The cost of a run, level by level: a move at level `j ≤ B` costs `1 + ∑_{ℓ < j} 2 ^ ℓ`. -/
lemma cost_eq {B : ℕ} :
    ∀ (ss : List Side) (Z : ZTrack Symbol) (J : ℕ), Z.nGe (B + 1) J ss = 0 →
      Z.cost J ss = ss.length + ∑ ℓ ∈ Finset.range B, 2 ^ ℓ * Z.nGe (ℓ + 1) J ss
  | [], _, _, _ => by simp [cost, nGe]
  | s :: ss, Z, J, h => by
    simp only [nGe, Nat.add_eq_zero_iff, ite_eq_right_iff, one_ne_zero, imp_false,
      not_le] at h
    rw [cost, cost_eq ss _ _ h.2]
    simp only [nGe, List.length_cons, mul_add, Finset.sum_add_distrib]
    have hgeom : 2 ^ Z.trig J s = 1 + ∑ ℓ ∈ Finset.range B,
        2 ^ ℓ * (if ℓ + 1 ≤ Z.trig J s then 1 else 0) := by
      rw [sum_two_pow_ite B (by omega), one_add_sum_two_pow]
    rw [hgeom]
    ring

/-- **The cost of `n` moves from a balanced track is `O(n log n)`.** -/
theorem cost_le (ss : List Side) (hV : Z.Valid J) (hB : Z.Balanced) :
    Z.cost J ss ≤ ss.length * (Nat.log 2 (ss.length + 1) + 1) := by
  have hmul : ∀ ℓ, 1 ≤ ℓ → Z.nGe ℓ J ss * (2 ^ ℓ - 1) ≤ ss.length := fun ℓ hℓ => by
    have := nGe_mul_le hℓ ss Z J hV
    rwa [dist_of_balanced hB, Nat.sub_self, add_zero] at this
  have hlt : ss.length < 2 ^ (Nat.log 2 (ss.length + 1) + 1) - 1 := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (ss.length + 1)
    omega
  have hzero : Z.nGe (Nat.log 2 (ss.length + 1) + 1) J ss = 0 := by
    by_contra h
    have := hmul (Nat.log 2 (ss.length + 1) + 1) (by omega)
    have : 2 ^ (Nat.log 2 (ss.length + 1) + 1) - 1 ≤
        Z.nGe (Nat.log 2 (ss.length + 1) + 1) J ss *
          (2 ^ (Nat.log 2 (ss.length + 1) + 1) - 1) :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h)
    omega
  rw [cost_eq ss Z J hzero]
  have hterm : ∀ ℓ ∈ Finset.range (Nat.log 2 (ss.length + 1)),
      2 ^ ℓ * Z.nGe (ℓ + 1) J ss ≤ ss.length := fun ℓ _ => by
    have := hmul (ℓ + 1) (by omega)
    have h2 : 2 ^ ℓ ≤ 2 ^ (ℓ + 1) - 1 := by
      rw [pow_succ]
      have := Nat.one_le_two_pow (n := ℓ)
      omega
    calc 2 ^ ℓ * Z.nGe (ℓ + 1) J ss ≤ (2 ^ (ℓ + 1) - 1) * Z.nGe (ℓ + 1) J ss :=
          Nat.mul_le_mul_right _ h2
      _ ≤ ss.length := by rw [mul_comm]; exact this
  have := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id] at this
  nlinarith

end ZTrack

end Turing.MultiTapeTM.HennieStearns
