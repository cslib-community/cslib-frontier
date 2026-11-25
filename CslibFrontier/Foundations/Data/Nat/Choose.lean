/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (to Mathlib's `Mathlib/Combinatorics/Choose/Bounds.lean` or cslib)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Scaling bounds for binomial coefficients

Scaling the ground set by `q` scales the number of `d`-subsets by at least `q ^ d`
(`Nat.pow_mul_choose_le_choose_mul`). Consequently a fixed `d`-subset of the ground set lies in at
most a `q ^ (-d)` fraction of the `k`-subsets when the ground set has at least `q k` elements
(`Nat.pow_mul_choose_sub_le_choose`). Lowering `ℓ` by `s` scales the number of `ℓ`-subsets of an
`m`-set by at most `(ℓ / (m - ℓ + 1)) ^ s` (`Nat.choose_sub_mul_pow_le`), so by at most
`q ^ (-s)` when `(q + 1) ℓ ≤ m` (`Nat.pow_mul_choose_sub_le_choose_of_mul_le`). Conversely,
descending factorials and binomial coefficients grow at least as fast as powers on larger ground
sets (`Nat.descFactorial_mul_pow_le`, `Nat.choose_mul_pow_le`), which gives the block-avoidance
estimate `2 ^ r * C(b * m - m, b * r) ≤ C(b * m, b * r)` (`Nat.two_pow_mul_choose_sub_le`).
Shrinking the ground set from `m` to `d` shrinks the number of `s`-subsets by at most
`((m + 1 - s) / (d + 1 - s)) ^ s` (`Nat.pow_mul_choose_le_choose_mul_pow`), the estimate behind
the Kővári–Sós–Turán bound.

## Main results

* `Nat.pow_mul_descFactorial_le`, `Nat.pow_mul_choose_le_choose_mul`,
  `Nat.pow_mul_choose_sub_le_choose`: scaling the ground set scales descending factorials and
  binomial coefficients.
* `Nat.choose_sub_mul_pow_le`, `Nat.pow_mul_choose_sub_le_choose_of_mul_le`: lowering the subset
  size scales the binomial coefficient.
* `Nat.pow_mul_choose_le_choose_mul_pow`: shrinking the ground set shrinks the binomial
  coefficient by at most a power.
* `Nat.descFactorial_mul_pow_le`, `Nat.choose_mul_pow_le`, `Nat.choose_mul_sub_mul_pow_le`,
  `Nat.two_mul_pred_pow_le`, `Nat.two_pow_mul_choose_sub_le`: power comparisons and the
  block-avoidance binomial estimate.
* `Nat.choose_le_two_pow_mul_choose_sub`, `Nat.choose_le_two_pow_mul_choose_sub_of_two_mul_le`:
  shrinking the ground set by `d` scales `U.choose k` by at most `2 ^ k * (U - d).choose k` (when
  `2 * d + k ≤ U + 1`) or `2 ^ d * (U - d).choose k` (when `2 * k ≤ U - d + 1`).
* `Nat.prod_choose_partition_mul_pow_factorial`: ordered equal-block partition identity
  `(∏ i : Fin F, ((F - i.val) * m).choose m) * m.factorial ^ F = (F * m).factorial`.
-/

public section

open scoped BigOperators

namespace Nat

/-- Termwise comparison of descending factorials: if `A (x - i) ≤ (y - i) B` for every `i < k`,
then `A ^ k x^{(k)} ≤ y^{(k)} B ^ k`. -/
private theorem pow_mul_descFactorial_le_descFactorial_mul_pow {A B x y : ℕ} (k : ℕ)
    (h : ∀ i < k, A * (x - i) ≤ (y - i) * B) :
    A ^ k * x.descFactorial k ≤ y.descFactorial k * B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descFactorial_succ, descFactorial_succ, pow_succ, pow_succ]
    calc A ^ k * A * ((x - k) * x.descFactorial k)
        = A ^ k * x.descFactorial k * (A * (x - k)) := by ring
      _ ≤ y.descFactorial k * B ^ k * ((y - k) * B) :=
          Nat.mul_le_mul (ih fun i hi => h i (by omega)) (h k (by omega))
      _ = (y - k) * y.descFactorial k * (B ^ k * B) := by ring

/-- The binomial form of `pow_mul_descFactorial_le_descFactorial_mul_pow`: if
`A (x - i) ≤ (y - i) B` for every `i < k`, then `A ^ k C(x, k) ≤ C(y, k) B ^ k`. -/
private theorem pow_mul_choose_le_choose_mul_pow_of_le {A B x y : ℕ} (k : ℕ)
    (h : ∀ i < k, A * (x - i) ≤ (y - i) * B) :
    A ^ k * x.choose k ≤ y.choose k * B ^ k := by
  have H := pow_mul_descFactorial_le_descFactorial_mul_pow k h
  rw [descFactorial_eq_factorial_mul_choose, descFactorial_eq_factorial_mul_choose] at H
  exact Nat.le_of_mul_le_mul_left (c := k.factorial) (by linarith) (factorial_pos k)

/-- One factor of `pow_mul_descFactorial_le`: `q (k - i) ≤ q k - i` for `1 ≤ q`, stated with a
factor `1` to fit `pow_mul_descFactorial_le_descFactorial_mul_pow`. -/
private theorem mul_sub_le_mul_sub {q : ℕ} (hq : 1 ≤ q) (k i : ℕ) :
    q * (k - i) ≤ (q * k - i) * 1 := by
  rw [Nat.mul_one, Nat.mul_sub_left_distrib]
  exact Nat.sub_le_sub_left (Nat.le_mul_of_pos_left i (by omega)) (q * k)

/-- Scaling the ground set by `q ≥ 1` scales a descending factorial by at least `q ^ d`. -/
theorem pow_mul_descFactorial_le {q : ℕ} (hq : 1 ≤ q) (k d : ℕ) :
    q ^ d * k.descFactorial d ≤ (q * k).descFactorial d := by
  simpa using pow_mul_descFactorial_le_descFactorial_mul_pow d fun i _ => mul_sub_le_mul_sub hq k i

/-- Scaling the ground set by `q ≥ 1` scales the number of `d`-subsets by at least `q ^ d`. -/
theorem pow_mul_choose_le_choose_mul {q : ℕ} (hq : 1 ≤ q) (k d : ℕ) :
    q ^ d * k.choose d ≤ (q * k).choose d := by
  simpa using pow_mul_choose_le_choose_mul_pow_of_le d fun i _ => mul_sub_le_mul_sub hq k i

/-- A `d`-subset of an `n`-set lies in at most a `q ^ (-d)` fraction of its `k`-subsets when
`q k ≤ n`. -/
theorem pow_mul_choose_sub_le_choose {q n k d : ℕ} (hq : 1 ≤ q) (hd : d ≤ k) (hn : q * k ≤ n) :
    q ^ d * (n - d).choose (k - d) ≤ n.choose k := by
  have h := Nat.mul_le_mul_right ((n - d).choose (k - d))
    ((pow_mul_choose_le_choose_mul hq k d).trans (choose_le_choose d hn))
  rw [← choose_mul (n := n) hd] at h
  exact Nat.le_of_mul_le_mul_left (c := k.choose d) (by linarith) (choose_pos hd)

/-- Lowering `ℓ` by `s` scales the number of `ℓ`-subsets of an `m`-set by at most
`(ℓ / (m - ℓ + 1)) ^ s`. -/
theorem choose_sub_mul_pow_le {m ℓ s : ℕ} (hs : s ≤ ℓ) (hℓ : ℓ ≤ m) :
    m.choose (ℓ - s) * (m - ℓ + 1) ^ s ≤ m.choose ℓ * ℓ ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    -- one step down: `C(m, j) (m - j) = C(m, j + 1) (j + 1)` at `j = ℓ - s - 1`
    have hstep := choose_succ_right_eq m (ℓ - (s + 1))
    rw [show ℓ - (s + 1) + 1 = ℓ - s by omega] at hstep
    have h₁ : m.choose (ℓ - (s + 1)) * (m - ℓ + 1) ≤ m.choose (ℓ - s) * ℓ :=
      (Nat.mul_le_mul_left _ (by omega : m - ℓ + 1 ≤ m - (ℓ - (s + 1)))).trans
        (hstep.symm.trans_le (Nat.mul_le_mul_left _ (by omega)))
    calc m.choose (ℓ - (s + 1)) * (m - ℓ + 1) ^ (s + 1)
        = m.choose (ℓ - (s + 1)) * (m - ℓ + 1) * (m - ℓ + 1) ^ s := by ring
      _ ≤ m.choose ℓ * ℓ ^ s * ℓ :=
          (Nat.mul_le_mul_right _ h₁).trans
            (by rw [mul_right_comm]; exact Nat.mul_le_mul_right _ (ih (by omega)))
      _ = m.choose ℓ * ℓ ^ (s + 1) := by ring

/-- If `ℓ` and `q ℓ` together fit into `m`, lowering `ℓ` by `s ≤ ℓ` divides the number of
`ℓ`-subsets of an `m`-set by at least `q ^ s`. -/
theorem pow_mul_choose_sub_le_choose_of_mul_le {m ℓ s q : ℕ} (hs : s ≤ ℓ)
    (hℓ : (q + 1) * ℓ ≤ m) : q ^ s * m.choose (ℓ - s) ≤ m.choose ℓ := by
  have hℓm : ℓ ≤ m := (Nat.le_mul_of_pos_left ℓ (by omega)).trans hℓ
  have hqℓ : q * ℓ ≤ m - ℓ + 1 := by rw [Nat.add_mul, one_mul] at hℓ; omega
  refine Nat.le_of_mul_le_mul_right (c := (m - ℓ + 1) ^ s) ?_ (Nat.pow_pos (by omega))
  calc q ^ s * m.choose (ℓ - s) * (m - ℓ + 1) ^ s
      ≤ q ^ s * (m.choose ℓ * ℓ ^ s) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (choose_sub_mul_pow_le hs hℓm)
    _ = m.choose ℓ * (q * ℓ) ^ s := by rw [Nat.mul_pow]; ring
    _ ≤ m.choose ℓ * (m - ℓ + 1) ^ s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqℓ s)

/-- One factor of `descFactorial_mul_pow_le`: `n (s - i) ≤ (n - i) s` for `s ≤ n`. -/
private theorem mul_sub_le_sub_mul {s n : ℕ} (h : s ≤ n) (i : ℕ) : n * (s - i) ≤ (n - i) * s := by
  rcases le_or_gt i s with his | his
  · zify [his, his.trans h]
    nlinarith
  · simp [Nat.sub_eq_zero_of_le his.le]

/-- Descending factorials compare like powers: `s^{(k)} / n^{(k)} ≤ (s / n)^k` for `s ≤ n`. -/
theorem descFactorial_mul_pow_le {s n : ℕ} (h : s ≤ n) (k : ℕ) :
    s.descFactorial k * n ^ k ≤ s ^ k * n.descFactorial k := by
  rw [Nat.mul_comm, Nat.mul_comm (s ^ k)]
  exact pow_mul_descFactorial_le_descFactorial_mul_pow k fun i _ => mul_sub_le_sub_mul h i

/-- For `a ≤ s`, `C(a, k) * s ^ k ≤ C(s, k) * a ^ k`. -/
theorem choose_mul_pow_le {a s : ℕ} (has : a ≤ s) (k : ℕ) :
    a.choose k * s ^ k ≤ s.choose k * a ^ k := by
  rw [Nat.mul_comm]
  exact pow_mul_choose_le_choose_mul_pow_of_le k fun i _ => mul_sub_le_sub_mul has i

/-- Shrinking the ground set from `m` to `d ≤ m` shrinks the number of `s`-subsets by at most
`((m + 1 - s) / (d + 1 - s)) ^ s`: `(d + 1 - s) ^ s C(m, s) ≤ C(d, s) (m + 1 - s) ^ s`. -/
theorem pow_mul_choose_le_choose_mul_pow {d m s : ℕ} (hdm : d ≤ m) :
    (d + 1 - s) ^ s * m.choose s ≤ d.choose s * (m + 1 - s) ^ s := by
  rcases Nat.lt_or_ge d s with hds | hsd
  · rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp
    · rw [show d + 1 - s = 0 by omega, zero_pow hs.ne', zero_mul]
      exact Nat.zero_le _
  -- for `i < s ≤ d ≤ m`: `(d + 1 - s) (m - i) ≤ (d - i) (m + 1 - s)`
  refine pow_mul_choose_le_choose_mul_pow_of_le s fun k hk => ?_
  obtain ⟨j, rfl⟩ : ∃ j, s = k + 1 + j := ⟨s - k - 1, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, d = k + 1 + j + a := ⟨d - (k + 1 + j), by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = k + 1 + j + a + b := ⟨m - (k + 1 + j + a), by omega⟩
  rw [show k + 1 + j + a + 1 - (k + 1 + j) = a + 1 by omega,
    show k + 1 + j + a + b - k = 1 + j + a + b by omega,
    show k + 1 + j + a - k = 1 + j + a by omega,
    show k + 1 + j + a + b + 1 - (k + 1 + j) = a + b + 1 by omega]
  nlinarith [Nat.zero_le (b * j)]

/-- `C(b * m - m, k) * b ^ k ≤ C(b * m, k) * (b - 1) ^ k`. -/
theorem choose_mul_sub_mul_pow_le (b m k : ℕ) :
    (b * m - m).choose k * b ^ k ≤ (b * m).choose k * (b - 1) ^ k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases k with _ | k <;> simp
  · rw [show b * m - m = (b - 1) * m by rw [Nat.sub_mul, one_mul]]
    have h := choose_mul_pow_le (Nat.mul_le_mul_right m (Nat.sub_le b 1)) k
    rw [Nat.mul_pow, Nat.mul_pow] at h
    exact Nat.le_of_mul_le_mul_right (c := m ^ k) (by linarith) (by positivity)

/-- Bernoulli's inequality in `ℕ`: for `1 ≤ n`, `d ^ n + n * d ^ (n - 1) ≤ (d + 1) ^ n`. -/
private theorem pow_add_mul_pow_sub_one_le (d : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    d ^ n + n * d ^ (n - 1) ≤ (d + 1) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Nat.add_sub_cancel] at ih ⊢
    calc d ^ (k + 2) + (k + 2) * d ^ (k + 1)
        = (d ^ (k + 1) + (k + 1) * d ^ k) * d + d ^ (k + 1) := by ring
      _ ≤ (d ^ (k + 1) + (k + 1) * d ^ k) * d + d ^ (k + 1) + (k + 1) * d ^ k :=
          Nat.le_add_right _ _
      _ = (d ^ (k + 1) + (k + 1) * d ^ k) * (d + 1) := by ring
      _ ≤ (d + 1) ^ (k + 1) * (d + 1) := Nat.mul_le_mul_right (d + 1) ih
      _ = (d + 1) ^ (k + 2) := by ring

/-- For `1 ≤ b`, `2 * (b - 1) ^ b ≤ b ^ b`. -/
theorem two_mul_pred_pow_le {b : ℕ} (hb : 1 ≤ b) :
    2 * (b - 1) ^ b ≤ b ^ b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
  refine (le_of_eq (by ring : 2 * d ^ (d + 1) = d ^ (d + 1) + d * d ^ d)).trans ?_
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right (d ^ d) (Nat.le_succ d)) _).trans
    (pow_add_mul_pow_sub_one_le d (Nat.succ_pos d))

/-- For `1 ≤ b`, `2 ^ r * C(b * m - m, b * r) ≤ C(b * m, b * r)`. -/
theorem two_pow_mul_choose_sub_le {b m : ℕ} (hb : 1 ≤ b) (r : ℕ) :
    2 ^ r * (b * m - m).choose (b * r) ≤ (b * m).choose (b * r) := by
  have hpow : 2 ^ r * (b - 1) ^ (b * r) ≤ b ^ (b * r) := by
    rw [pow_mul, ← Nat.mul_pow, pow_mul b]
    exact Nat.pow_le_pow_left (two_mul_pred_pow_le hb) r
  have hchoose := choose_mul_sub_mul_pow_le b m (b * r)
  refine Nat.le_of_mul_le_mul_right (c := b ^ (b * r)) ?_ (by positivity)
  calc 2 ^ r * (b * m - m).choose (b * r) * b ^ (b * r)
      = 2 ^ r * ((b * m - m).choose (b * r) * b ^ (b * r)) := by ring
    _ ≤ 2 ^ r * ((b * m).choose (b * r) * (b - 1) ^ (b * r)) := by gcongr
    _ = (b * m).choose (b * r) * (2 ^ r * (b - 1) ^ (b * r)) := by ring
    _ ≤ (b * m).choose (b * r) * b ^ (b * r) := by gcongr

/-- Shrinking `U` by `d` (`k ≤ U - d`, `2 * d + k ≤ U + 1`) multiplies `choose · k` by `≤ 2 ^ k`. -/
theorem choose_le_two_pow_mul_choose_sub {U d k : ℕ} (hk : k ≤ U - d) (h : 2 * d + k ≤ U + 1) :
    U.choose k ≤ 2 ^ k * (U - d).choose k := by
  refine Nat.le_of_mul_le_mul_left (c := (U - d + 1 - k) ^ k) ?_ (Nat.pow_pos (by omega))
  calc (U - d + 1 - k) ^ k * U.choose k
      ≤ (U - d).choose k * (U + 1 - k) ^ k :=
        Nat.pow_mul_choose_le_choose_mul_pow (d := U - d) (m := U) (s := k) (Nat.sub_le U d)
    _ ≤ (U - d).choose k * (2 * (U - d + 1 - k)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
    _ = (U - d + 1 - k) ^ k * (2 ^ k * (U - d).choose k) := by rw [Nat.mul_pow]; ring

/-- Shrinking `N` by `d` (`k ≤ N - d`, `2 * k ≤ N - d + 1`) multiplies `choose · k` by `≤ 2 ^ d`. -/
theorem choose_le_two_pow_mul_choose_sub_of_two_mul_le {N d k : ℕ}
    (hk : k ≤ N - d) (h2k : 2 * k ≤ N - d + 1) :
    N.choose k ≤ 2 ^ d * (N - d).choose k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simpa using Nat.one_le_two_pow
  have h1 := choose_mul (n := N) (k := k + d) (s := k) (Nat.le_add_right k d)
  have h2 := choose_mul (n := N) (k := k + d) (s := d) (Nat.le_add_left d k)
  rw [Nat.add_sub_cancel_left] at h1
  rw [Nat.add_sub_cancel, ← choose_symm_add] at h2
  have hle := Nat.mul_le_mul_right ((N - d).choose k)
    (choose_le_two_pow_mul_choose_sub (U := N) (d := k) (k := d) (by omega) (by omega))
  exact Nat.le_of_mul_le_mul_right (c := (N - k).choose d)
    (by nlinarith [h1.symm.trans h2]) (choose_pos (by omega))

/-- Multinomial identity `(∏_{i < F} C((F - i) * m, m)) * (m!)^F = (F * m)!` counting ordered
partitions of an `(F * m)`-element set into `F` blocks of size `m`. -/
theorem prod_choose_partition_mul_pow_factorial (F m : ℕ) :
    (∏ i : Fin F, ((F - i.val) * m).choose m) * m.factorial ^ F = (F * m).factorial := by
  induction F with
  | zero => simp
  | succ F ih =>
    rw [Fin.prod_univ_succ, Fin.val_zero, Nat.sub_zero, pow_succ,
      show (∏ i : Fin F, ((F + 1 - (Fin.succ i).val) * m).choose m) =
        ∏ i : Fin F, ((F - i.val) * m).choose m from Finset.prod_congr rfl fun i _ => by simp]
    have hchoose := choose_mul_factorial_mul_factorial
      (show m ≤ (F + 1) * m from Nat.le_mul_of_pos_left m (Nat.succ_pos F))
    rw [show (F + 1) * m - m = F * m by rw [Nat.succ_mul, Nat.add_sub_cancel]] at hchoose
    calc ((F + 1) * m).choose m * (∏ i : Fin F, ((F - i.val) * m).choose m) *
          (m.factorial ^ F * m.factorial)
        = ((F + 1) * m).choose m * m.factorial * (F * m).factorial := by rw [← ih]; ring
      _ = ((F + 1) * m).factorial := hchoose

end Nat
