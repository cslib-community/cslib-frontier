/-
Copyright (c) 2026 Samuel Schlesinger, vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, vvauted
-/

module
-- upstream: candidate (Mathlib, next to `Mathlib/Data/Nat/Log.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Iterate

/-!
# Ackermann function and inverse-Ackermann bounds

This module defines the diagonal Ackermann hierarchy `Nat.ackermann k j` from [CLRS2009]
Section 21.4 (pp. 573–581) together with rank-shifted inverses `Nat.inverseAckermannAt d n`,
`Nat.inverseAckermann n`, and `Nat.inverseAckermannTwo m n` used in amortized disjoint-set step
analyses (toward #3558 and #5441).

Every definition is structurally recursive, so small values evaluate by `decide`. For `k = 0`,
`ackermann 0 j = j + 1`; for `k + 1`, `ackermann (k + 1) j = (ackermann k)^[j + 1] j`, matching
[CLRS2009] Section 21.4 (so `ackermann 1 j = 2 * j + 1`, `ackermann 2 1 = 7`, and
`ackermann 3 1 = 2047`). This differs from `Mathlib.Computability.Ackermann` (`ack`, the
Péter–Robinson recurrence with `ack 1 n = n + 2` and `ack 3 n = 2 ^ (n + 3) - 3`) and from
`CslibFrontier.Foundations.Data.Nat.LogStar` (`Nat.twoTower` / `Nat.logStar`, the single-level
tower of twos and iterated logarithm). Because `ackermann k 0 = 1` for every `k`, strict
monotonicity in `k` and unbounded growth require `1 ≤ j`. Shifting the diagonal offset by
`d' := max 1 d ≥ 1`, `inverseAckermannAt d n` returns the least `k ≥ 1` with
`Nat.log 2 n + d' < ackermann k d'`. Taking `d = 1` yields the single-parameter inverse
`inverseAckermann n`, and taking `d = m / n + 1` yields a two-parameter analogue
`inverseAckermannTwo m n` (using shift `d = m / n + 1` in the [CLRS2009] recurrence, differing by
small constants from [Tarjan1975]'s `4 * ⌈m / n⌉` threshold convention).

## Main definitions

* `Nat.ackermann`: two-argument `(j + 1)`-fold Ackermann hierarchy by structural recursion.
* `Nat.inverseAckermannAt`: least `k ≥ 1` with `Nat.log 2 n + max 1 d < ackermann k (max 1 d)`.
* `Nat.inverseAckermann`: single-parameter inverse Ackermann `inverseAckermannAt 1 n`.
* `Nat.inverseAckermannTwo`: shifted two-parameter inverse Ackermann
  `inverseAckermannAt (m / n + 1) n`.

## Main results

* `Nat.lt_ackermann`, `Nat.ackermann_strictMono_right`: strict growth in the second argument.
* `Nat.ackermann_lt_succ_left`, `Nat.ackermann_strictMono_left`, `Nat.add_lt_ackermann`: strict
  growth in the level when `1 ≤ j`.
* `Nat.inverseAckermannAt_le_iff`, `Nat.inverseAckermannAt_mono_right`,
  `Nat.inverseAckermannAt_anti_left`: Galois-style characterization and monotonicity.
* `Nat.inverseAckermannTwo_eq_one_of_mul_log_le`: `inverseAckermannTwo m n = 1` once
  `n * Nat.log 2 n ≤ m`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to Algorithms* (3rd
  ed.), MIT Press, 2009, Section 21.4, pp. 573–581][CLRS2009].
* [R. E. Tarjan, *Efficiency of a Good But Not Linear Set Union Algorithm*, JACM 22(2),
  pp. 215–225, 1975][Tarjan1975].
* [D. C. Kozen, *The Design and Analysis of Algorithms*, Lectures 10–11, pp. 48–57,
  1992][Kozen1992].
-/

public section

namespace Nat

/-- Two-argument Ackermann hierarchy by structural recursion:
`ackermann 0 j = j + 1` and `ackermann (k + 1) j = (ackermann k)^[j + 1] j`. -/
@[expose] def ackermann : ℕ → ℕ → ℕ
  | 0, j => j + 1
  | k + 1, j => (ackermann k)^[j + 1] j

/-- Bounded upward search helper for `inverseAckermannAt`: returns the first `m ≥ k` in at most
`fuel` steps satisfying `target < ackermann m d`. -/
@[expose] def inverseAckermannAux (d target : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k =>
    if target < ackermann k d then k else inverseAckermannAux d target fuel (k + 1)

/-- Shifted inverse Ackermann function: least `k ≥ 1` with
`Nat.log 2 n + max 1 d < ackermann k (max 1 d)`. -/
@[expose] def inverseAckermannAt (d n : ℕ) : ℕ :=
  let d' := max 1 d
  inverseAckermannAux d' (Nat.log 2 n + d') (Nat.log 2 n + 1) 1

/-- Single-parameter inverse Ackermann function `α(n) = inverseAckermannAt 1 n`. -/
@[expose] def inverseAckermann (n : ℕ) : ℕ :=
  inverseAckermannAt 1 n

/-- Shifted two-parameter inverse Ackermann function
`α(m, n) = inverseAckermannAt (m / n + 1) n`, a constant-shift analogue of Tarjan's `α(m, n)`. -/
@[expose] def inverseAckermannTwo (m n : ℕ) : ℕ :=
  inverseAckermannAt (m / n + 1) n

@[simp] theorem ackermann_zero (j : ℕ) : ackermann 0 j = j + 1 := rfl

theorem ackermann_succ (k j : ℕ) : ackermann (k + 1) j = (ackermann k)^[j + 1] j := rfl

private theorem ackermann_zero_iterate (t j : ℕ) : (ackermann 0)^[t] j = j + t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, ackermann_zero]; omega

/-- Closed form at level `1`: `ackermann 1 j = 2 * j + 1`. -/
theorem ackermann_one (j : ℕ) : ackermann 1 j = 2 * j + 1 := by
  rw [ackermann_succ, ackermann_zero_iterate]
  omega

private theorem ackermann_one_iterate (t j : ℕ) :
    (ackermann 1)^[t] j + 1 = 2 ^ t * (j + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ackermann_one, Nat.pow_succ', Nat.mul_assoc]
    omega

/-- Closed form at level `2`: `ackermann 2 j = 2 ^ (j + 1) * (j + 1) - 1`. -/
theorem ackermann_two (j : ℕ) : ackermann 2 j = 2 ^ (j + 1) * (j + 1) - 1 := by
  have h := ackermann_one_iterate (j + 1) j
  change ackermann 2 j + 1 = 2 ^ (j + 1) * (j + 1) at h
  omega

private theorem ackermann_two_one : ackermann 2 1 = 7 := by decide

/-- Concrete value `ackermann 3 1 = 2047`. -/
theorem ackermann_three_one : ackermann 3 1 = 2047 := by
  rw [ackermann_succ, Function.iterate_succ_apply', Function.iterate_one, ackermann_two_one,
    ackermann_two]

/-- Every diagonal value strictly exceeds its second argument. -/
theorem lt_ackermann : ∀ k j : ℕ, j < ackermann k j
  | 0, j => Nat.lt_succ_self j
  | k + 1, j => by
    rw [ackermann_succ, Function.iterate_succ_apply]
    exact (lt_ackermann k j).trans_le
      (Function.id_le_iterate_of_id_le (fun x => Nat.le_of_lt (lt_ackermann k x)) j
        (ackermann k j))

/-- For fixed level `k`, `ackermann k` is strictly increasing. -/
theorem ackermann_strictMono_right : ∀ k : ℕ, StrictMono (ackermann k)
  | 0 => fun _ _ h => Nat.succ_lt_succ h
  | k + 1 => fun j₁ j₂ hj =>
    let ih := ackermann_strictMono_right k
    (ih.iterate (j₁ + 1) hj).trans
      (ih.strictMono_iterate_of_lt_map (lt_ackermann k j₂) (Nat.succ_lt_succ hj))

/-- For fixed level `k`, `ackermann k` is monotone. -/
theorem ackermann_monotone_right (k : ℕ) : Monotone (ackermann k) :=
  (ackermann_strictMono_right k).monotone

/-- `ackermann` is nondecreasing in the level `k`. -/
theorem ackermann_le_succ_left (k j : ℕ) : ackermann k j ≤ ackermann (k + 1) j := by
  rw [ackermann_succ, Function.iterate_succ_apply']
  exact ackermann_monotone_right k
    (Function.id_le_iterate_of_id_le (fun x => Nat.le_of_lt (lt_ackermann k x)) j j)

/-- For fixed `j`, `k ↦ ackermann k j` is monotone. -/
theorem ackermann_monotone_left (j : ℕ) : Monotone (fun k => ackermann k j) :=
  monotone_nat_of_le_succ fun k => ackermann_le_succ_left k j

/-- For `1 ≤ j`, advancing the level strictly increases `ackermann k j`. -/
theorem ackermann_lt_succ_left (k : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    ackermann k j < ackermann (k + 1) j := by
  rw [ackermann_succ]
  simpa only [Function.iterate_one] using
    (ackermann_strictMono_right k).strictMono_iterate_of_lt_map (lt_ackermann k j)
      (Nat.lt_succ_iff.mpr hj)

/-- For `1 ≤ j`, `k ↦ ackermann k j` is strictly increasing. -/
theorem ackermann_strictMono_left {j : ℕ} (hj : 1 ≤ j) : StrictMono (fun k => ackermann k j) :=
  strictMono_nat_of_lt_succ fun k => ackermann_lt_succ_left k hj

/-- For `1 ≤ j`, `j + k < ackermann k j`. -/
theorem add_lt_ackermann : ∀ (k : ℕ) {j : ℕ}, 1 ≤ j → j + k < ackermann k j
  | 0, j, _ => Nat.lt_succ_self j
  | k + 1, _, hj =>
    lt_of_le_of_lt (add_lt_ackermann k hj) (ackermann_lt_succ_left k hj)

private theorem ackermann_add_two_le_succ_right {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    ackermann k j + 2 ≤ ackermann k (j + 1) := by
  rcases k with _ | _ | k'
  · omega
  · rw [ackermann_one, ackermann_one]
    omega
  · let A := ackermann (k' + 2) j
    have h1 : A + 1 ≤ (ackermann (k' + 1))^[j + 1] (j + 1) :=
      (ackermann_strictMono_right (k' + 1)).iterate (j + 1) (Nat.lt_succ_self j)
    have h2 : ackermann (k' + 1) (A + 1) ≤ ackermann (k' + 2) (j + 1) := by
      calc
        ackermann (k' + 1) (A + 1)
            ≤ ackermann (k' + 1) ((ackermann (k' + 1))^[j + 1] (j + 1)) :=
          ackermann_monotone_right (k' + 1) h1
        _ = ackermann (k' + 2) (j + 1) :=
          (Function.iterate_succ_apply' (ackermann (k' + 1)) (j + 1) (j + 1)).symm
    have h3 : 2 * (A + 1) + 1 ≤ ackermann (k' + 1) (A + 1) :=
      ackermann_one (A + 1) ▸
        ackermann_monotone_left (A + 1) (Nat.succ_le_succ (Nat.zero_le k'))
    change A + 2 ≤ ackermann (k' + 2) (j + 1)
    omega

private theorem ackermann_add_sub_le {k d₁ d₂ : ℕ} (hk : 1 ≤ k) (hd : d₁ ≤ d₂) :
    ackermann k d₁ + (d₂ - d₁) ≤ ackermann k d₂ := by
  induction d₂, hd using Nat.le_induction with
  | base => simp
  | succ m _ _ =>
    have := ackermann_add_two_le_succ_right hk m
    omega

private theorem inverseAckermannAux_spec {d target : ℕ} :
    ∀ (fuel k : ℕ), target < ackermann (k + fuel) d →
      k ≤ inverseAckermannAux d target fuel k ∧
      target < ackermann (inverseAckermannAux d target fuel k) d ∧
      ∀ m, k ≤ m → target < ackermann m d → inverseAckermannAux d target fuel k ≤ m
  | 0, k, h => ⟨Nat.le_refl k, h, fun _ hm _ => hm⟩
  | fuel + 1, k, h => by
    rw [inverseAckermannAux]
    split_ifs with hlt
    · exact ⟨Nat.le_refl k, hlt, fun _ hm _ => hm⟩
    · have h' : target < ackermann ((k + 1) + fuel) d := by
        rwa [Nat.add_right_comm]
      obtain ⟨hk1, htarget, hmin⟩ := inverseAckermannAux_spec fuel (k + 1) h'
      refine ⟨(Nat.le_succ k).trans hk1, htarget, fun m hm hm_lt => ?_⟩
      rcases Nat.eq_or_lt_of_le hm with rfl | hkm
      · exact absurd hm_lt hlt
      · exact hmin m hkm hm_lt

private theorem inverseAckermannAt_spec (d n : ℕ) :
    1 ≤ inverseAckermannAt d n ∧
    Nat.log 2 n + max 1 d < ackermann (inverseAckermannAt d n) (max 1 d) ∧
    ∀ m, 1 ≤ m → Nat.log 2 n + max 1 d < ackermann m (max 1 d) →
      inverseAckermannAt d n ≤ m := by
  unfold inverseAckermannAt
  dsimp only
  refine inverseAckermannAux_spec (Nat.log 2 n + 1) 1 ?_
  have hd : 1 ≤ max 1 d := Nat.le_max_left 1 d
  have hlt := add_lt_ackermann (1 + (Nat.log 2 n + 1)) hd
  omega

/-- `inverseAckermannAt d n` is at least `1`. -/
theorem one_le_inverseAckermannAt (d n : ℕ) : 1 ≤ inverseAckermannAt d n :=
  (inverseAckermannAt_spec d n).1

/-- Defining inequality for `inverseAckermannAt d n`. -/
theorem log_add_lt_ackermann_inverseAckermannAt (d n : ℕ) :
    Nat.log 2 n + max 1 d < ackermann (inverseAckermannAt d n) (max 1 d) :=
  (inverseAckermannAt_spec d n).2.1

/-- Equivalence characterization for `inverseAckermannAt d n ≤ k` when `1 ≤ k`. -/
theorem inverseAckermannAt_le_iff {d n k : ℕ} (hk : 1 ≤ k) :
    inverseAckermannAt d n ≤ k ↔ Nat.log 2 n + max 1 d < ackermann k (max 1 d) :=
  ⟨fun h => (log_add_lt_ackermann_inverseAckermannAt d n).trans_le
      (ackermann_monotone_left (max 1 d) h),
    (inverseAckermannAt_spec d n).2.2 k hk⟩

/-- For fixed `d`, `n ↦ inverseAckermannAt d n` is monotone. -/
theorem inverseAckermannAt_mono_right (d : ℕ) : Monotone (inverseAckermannAt d) := by
  intro n₁ n₂ hn
  rw [inverseAckermannAt_le_iff (one_le_inverseAckermannAt d n₂)]
  have hlog : Nat.log 2 n₁ ≤ Nat.log 2 n₂ := Nat.log_mono_right hn
  have hlt := log_add_lt_ackermann_inverseAckermannAt d n₂
  omega

/-- For fixed `n`, `d ↦ inverseAckermannAt d n` is antitone. -/
theorem inverseAckermannAt_anti_left (n : ℕ) : Antitone (fun d => inverseAckermannAt d n) := by
  intro d₁ d₂ hd
  have h1 : 1 ≤ inverseAckermannAt d₁ n := one_le_inverseAckermannAt d₁ n
  rw [inverseAckermannAt_le_iff h1]
  have hlt := log_add_lt_ackermann_inverseAckermannAt d₁ n
  have hd' : max 1 d₁ ≤ max 1 d₂ := max_le_max_left 1 hd
  have hstep := ackermann_add_sub_le h1 hd'
  omega

/-- `inverseAckermann n` is at least `1`. -/
theorem one_le_inverseAckermann (n : ℕ) : 1 ≤ inverseAckermann n :=
  one_le_inverseAckermannAt 1 n

/-- Defining inequality for `inverseAckermann n`. -/
theorem log_add_one_lt_ackermann_inverseAckermann (n : ℕ) :
    Nat.log 2 n + 1 < ackermann (inverseAckermann n) 1 :=
  log_add_lt_ackermann_inverseAckermannAt 1 n

/-- Equivalence characterization for `inverseAckermann n ≤ k` when `1 ≤ k`. -/
theorem inverseAckermann_le_iff {n k : ℕ} (hk : 1 ≤ k) :
    inverseAckermann n ≤ k ↔ Nat.log 2 n + 1 < ackermann k 1 :=
  inverseAckermannAt_le_iff hk

/-- `inverseAckermann` is monotone. -/
theorem inverseAckermann_mono : Monotone inverseAckermann :=
  inverseAckermannAt_mono_right 1

/-- For all `n < 2 ^ 2046`, `inverseAckermann n ≤ 3`. -/
theorem inverseAckermann_le_three_of_lt {n : ℕ} (hn : n < 2 ^ 2046) :
    inverseAckermann n ≤ 3 := by
  rw [inverseAckermann_le_iff (by decide : 1 ≤ 3), ackermann_three_one]
  rcases eq_or_ne n 0 with rfl | hn0
  · decide
  · have := Nat.log_lt_of_lt_pow hn0 hn
    omega

/-- `inverseAckermannTwo m n` is at least `1`. -/
theorem one_le_inverseAckermannTwo (m n : ℕ) : 1 ≤ inverseAckermannTwo m n :=
  one_le_inverseAckermannAt (m / n + 1) n

/-- Defining inequality for `inverseAckermannTwo m n`. -/
theorem log_add_lt_ackermann_inverseAckermannTwo (m n : ℕ) :
    Nat.log 2 n + (m / n + 1) < ackermann (inverseAckermannTwo m n) (m / n + 1) :=
  log_add_lt_ackermann_inverseAckermannAt (m / n + 1) n

/-- Two-parameter `inverseAckermannTwo m n` is always bounded above by `inverseAckermann n`. -/
theorem inverseAckermannTwo_le_inverseAckermann (m n : ℕ) :
    inverseAckermannTwo m n ≤ inverseAckermann n :=
  inverseAckermannAt_anti_left n (Nat.le_add_left 1 (m / n))

/-- For fixed `n`, `m ↦ inverseAckermannTwo m n` is antitone. -/
theorem inverseAckermannTwo_anti_left (n : ℕ) : Antitone (fun m => inverseAckermannTwo m n) := by
  intro m₁ m₂ hm
  exact inverseAckermannAt_anti_left n (Nat.add_le_add_right (Nat.div_le_div_right hm) 1)

/-- When `m < n`, `inverseAckermannTwo m n` coincides with `inverseAckermann n`. -/
theorem inverseAckermannTwo_of_lt {m n : ℕ} (h : m < n) :
    inverseAckermannTwo m n = inverseAckermann n := by
  unfold inverseAckermannTwo inverseAckermann
  rw [Nat.div_eq_of_lt h]

/-- When `Nat.log 2 n ≤ m / n + 1`, `inverseAckermannTwo m n = 1`. -/
theorem inverseAckermannTwo_eq_one_of_log_le {m n : ℕ} (h : Nat.log 2 n ≤ m / n + 1) :
    inverseAckermannTwo m n = 1 := by
  refine Nat.le_antisymm ?_ (one_le_inverseAckermannTwo m n)
  rw [inverseAckermannTwo, inverseAckermannAt_le_iff (Nat.le_refl 1),
    max_eq_right (Nat.succ_pos _), ackermann_one]
  omega

/-- Once `n * Nat.log 2 n ≤ m`, Tarjan's two-parameter inverse Ackermann collapses to `1`. -/
theorem inverseAckermannTwo_eq_one_of_mul_log_le {m n : ℕ} (h : n * Nat.log 2 n ≤ m) :
    inverseAckermannTwo m n = 1 := by
  apply inverseAckermannTwo_eq_one_of_log_le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.le_succ_of_le ((Nat.le_div_iff_mul_le hn).2 (Nat.mul_comm n _ ▸ h))

end Nat
