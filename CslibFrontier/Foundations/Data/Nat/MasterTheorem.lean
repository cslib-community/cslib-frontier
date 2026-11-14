/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# The master theorem for divide-and-conquer recurrences

`Nat.DivideConquerBound T a b n₀ T₀ f` says that `T` satisfies the divide-and-conquer inequality
`T n ≤ a T(⌈n/b⌉) + f n` above the threshold `n₀`, with `T n ≤ T₀` up to `n₀`. The recurrence is
stated in a form that cost functions satisfy directly. For every `n > n₀`, every `S` that bounds
`T` on `[0, ⌈n/b⌉]` gives `T n ≤ a S + f n`. Floors, ceilings and several subproblems of
different sizes up to `⌈n/b⌉` are therefore covered. `T` need not be monotone or satisfy an
equality.

The general bound unrolls the recursion: for `a ≥ 1`, monotone `f` and `n ≤ n₀ b ^ k`,

`T n ≤ a ^ k T₀ + ∑ i < k, a ^ i f (n₀ b ^ (k - i))`

(`Nat.DivideConquerBound.le_sum`). For `f n = c n ^ d` the sum is geometric with ratio `a / b ^ d`,
and the three cases of the master theorem follow with explicit constants.

`DivideConquerBound` itself imposes no condition on `a`, `b` or `n₀`. Every bound below assumes
`a ≥ 1`, and the bounds in terms of `n` also assume `b ≥ 2` and `n₀ ≥ 1`. Without them the
conclusions can fail. For example, `T n = n` with `a = b = n₀ = T₀ = 1` and `c = d = 0` satisfies
`DivideConquerBound`, because `⌈n/1⌉ = n`, yet the second bound would give `T 2 ≤ 1`. Write
`K = ⌈log_b n⌉`.

* `a > b ^ d`: `(a - b ^ d) T n ≤ ((a - b ^ d) T₀ + c n₀ ^ d b ^ d) a ^ K`.
* `a = b ^ d`: `T n ≤ (b n) ^ d (T₀ + c n₀ ^ d K)` for `n ≠ 0`.
* `a < b ^ d`: `(b ^ d - a) T n ≤ ((b ^ d - a) T₀ + c n₀ ^ d b ^ d) (b n) ^ d` for `n ≠ 0`.

The first and third bounds hold for all `a ≥ 1`. They are trivial outside their case, where the
left factor is zero. The `n`-forms use `b ^ ⌈log_b n⌉ ≤ b n` (`Nat.pow_clog_le_mul`).
`CslibFrontier.Foundations.Data.Nat.MasterTheoremAsymptotics` converts them into
`O(n ^ log_b a)`, `O(n ^ d log n)` and `O(n ^ d)`.

`Nat.add_mul_two_pow_le_mul_pow_of_halving` (`CslibFrontier.Foundations.Data.Nat.HalvingRecurrence`)
remains the sharper tool for `b = 2`: it carries a subtracted lower-order term through the
induction, which some clients need.

These are upper bounds for inequality recurrences. `Nat.DivideConquerBound.le_mul_of_regular`
covers case 3 under the general regularity condition `q * (a * f ⌈m/b⌉) ≤ p * f m` (`p < q`).
`Nat.DivideConquerLowerBound` is the dual lower-bound contract (`a T(⌊n/b⌋) + f n ≤ T n` on
subproblems in `[⌊n/b⌋, ⌈n/b⌉]` and `T₀ ≤ T n` on `[1, n₀]`), and `Nat.DivideConquerRecurrence`
packages equality recurrences supplying both bounds.
`CslibFrontier.Foundations.Data.Nat.MasterTheoremAsymptotics` turns them into `O`, `Ω` and `Θ`
statements.

## Main definitions

* `Nat.DivideConquerBound`: the divide-and-conquer upper inequality with threshold and base bound.
* `Nat.DivideConquerLowerBound`: the divide-and-conquer lower inequality with threshold and base
  bound.
* `Nat.DivideConquerRecurrence`: equality recurrences with `a` subproblems in `[⌊n/b⌋, ⌈n/b⌉]`.

## Main results

* `Nat.DivideConquerBound.le_sum`: the unrolled upper bound; `Nat.DivideConquerBound.le_geom_sum`
  for `f n = c n ^ d`.
* `Nat.DivideConquerBound.sub_mul_le_pow`, `Nat.DivideConquerBound.le_pow_mul`,
  `Nat.DivideConquerBound.pow_sub_mul_le_pow`: the three cases for `n ≤ n₀ b ^ k`.
* `Nat.DivideConquerBound.sub_mul_le_pow_clog`, `Nat.DivideConquerBound.le_mul_pow_mul_clog`,
  `Nat.DivideConquerBound.pow_sub_mul_le_mul_pow`: the three cases in terms of `n`.
* `Nat.DivideConquerBound.le_mul_of_regular`: case 3 under the general regularity condition.
* `Nat.DivideConquerLowerBound.sum_le`, `Nat.DivideConquerLowerBound.driving_le`: the unrolled
  lower bound and direct driving-term lower bound.
* `Nat.DivideConquerLowerBound.pow_log_mul_le`,
  `Nat.DivideConquerLowerBound.pow_pred_log_mul_le`, `Nat.DivideConquerLowerBound.pow_mul_le`,
  `Nat.DivideConquerLowerBound.mul_pow_mul_log_le`: explicit lower bounds for cases 1 and 2.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Theorem 4.1
  (the master theorem, Section 4.5), Lemmas 4.2–4.4 and Section 4.6.2 (floors and ceilings).
-/

public section

namespace Nat

open Finset

/-- `T` satisfies the divide-and-conquer inequality `T n ≤ a T(⌈n/b⌉) + f n` above `n₀`, with
`T n ≤ T₀` up to `n₀`. The recursive step quantifies over every bound `S` of `T` on
`[0, ⌈n/b⌉]`, so subproblems of any size up to `⌈n/b⌉` may be used. -/
structure DivideConquerBound (T : ℕ → ℕ) (a b n₀ T₀ : ℕ) (f : ℕ → ℕ) : Prop where
  /-- The base case: `T n ≤ T₀` for `n ≤ n₀`. -/
  base : ∀ n ≤ n₀, T n ≤ T₀
  /-- The recursive step: `T n ≤ a S + f n` whenever `S` bounds `T` up to `⌈n/b⌉`. -/
  step : ∀ n, n₀ < n → ∀ S, (∀ m ≤ (n + b - 1) / b, T m ≤ S) → T n ≤ a * S + f n

private theorem sum_pow_mul_poly (c d n₀ a b k : ℕ) :
    ∑ i ∈ range k, a ^ i * (c * (n₀ * b ^ (k - i)) ^ d) =
      c * n₀ ^ d * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i) := by
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k - i) d]
  ring

namespace DivideConquerBound

variable {T f : ℕ → ℕ} {a b n₀ T₀ c d : ℕ}

/-- **Unrolling the recursion.** For monotone `f` and `n ≤ n₀ b ^ k`,
`T n ≤ a ^ k T₀ + ∑ i < k, a ^ i f (n₀ b ^ (k - i))`. -/
theorem le_sum (h : DivideConquerBound T a b n₀ T₀ f) (ha : 1 ≤ a) (hf : Monotone f) :
    ∀ k n, n ≤ n₀ * b ^ k →
      T n ≤ a ^ k * T₀ + ∑ i ∈ range k, a ^ i * f (n₀ * b ^ (k - i)) := by
  intro k
  induction k with
  | zero =>
    intro n hn
    simpa using h.base n (by simpa using hn)
  | succ k ih =>
    intro n hn
    rcases le_or_gt n n₀ with hle | hlt
    · calc T n ≤ T₀ := h.base n hle
        _ ≤ a ^ (k + 1) * T₀ := Nat.le_mul_of_pos_left _ (Nat.pow_pos ha)
        _ ≤ _ := Nat.le_add_right _ _
    · set X := n₀ * b ^ k with hX
      have hn' : n ≤ X * b := by rw [hX, mul_assoc, ← pow_succ]; exact hn
      have hb : 0 < b := by
        rcases Nat.eq_zero_or_pos b with rfl | hb
        · simp only [mul_zero] at hn'; omega
        · exact hb
      have hm : (n + b - 1) / b ≤ X := by
        refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb).mpr ?_)
        rw [Nat.succ_mul]
        omega
      calc T n ≤ a * (a ^ k * T₀ + ∑ i ∈ range k, a ^ i * f (n₀ * b ^ (k - i))) + f n :=
            h.step n hlt _ fun m hm' => ih m (hm'.trans hm)
        _ ≤ a * (a ^ k * T₀ + ∑ i ∈ range k, a ^ i * f (n₀ * b ^ (k - i))) +
            f (n₀ * b ^ (k + 1)) := Nat.add_le_add_left (hf hn) _
        _ = _ := by
          rw [sum_range_succ', mul_add, mul_sum]
          simp only [Nat.add_sub_add_right, Nat.sub_zero, pow_zero, one_mul, pow_succ',
            mul_assoc]
          ac_rfl

/-- The unrolled recursion for `f n = c n ^ d`. -/
theorem le_geom_sum (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d) (ha : 1 ≤ a)
    (k n : ℕ) (hn : n ≤ n₀ * b ^ k) :
    T n ≤ a ^ k * T₀ + c * n₀ ^ d * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i) := by
  have := h.le_sum ha (fun x y hxy => Nat.mul_le_mul_left c (Nat.pow_le_pow_left hxy d)) k n hn
  rwa [sum_pow_mul_poly] at this

end DivideConquerBound

/-! ### Geometric sums -/

/-- The sum `∑ i < k, a ^ i q ^ (k - i)` is `q` times Mathlib's `geom_sum₂` form. -/
private theorem sum_pow_mul_pow_sub (a q k : ℕ) :
    ∑ i ∈ range k, a ^ i * q ^ (k - i) = q * ∑ i ∈ range k, a ^ i * q ^ (k - 1 - i) := by
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have : k - i = (k - 1 - i) + 1 := by have := mem_range.mp hi; omega
  rw [this, pow_succ]
  ring

private theorem sum_pow_mul_pow_sub_self (q k : ℕ) :
    ∑ i ∈ range k, q ^ i * q ^ (k - i) = k * q ^ k := by
  rcases k with _ | k
  · simp
  · rw [sum_pow_mul_pow_sub, geom_sum₂_self, Nat.add_sub_cancel, Nat.cast_id]
    ring

/-! ### The three cases -/

namespace DivideConquerBound

variable {T f : ℕ → ℕ} {a b n₀ T₀ c d : ℕ}

/-- **Master theorem, case 1** (`a > b ^ d`), for `n ≤ n₀ b ^ k`:
`(a - b ^ d) T n ≤ ((a - b ^ d) T₀ + c n₀ ^ d b ^ d) a ^ k`. The bound holds for every `a ≥ 1`
and is trivial when `a ≤ b ^ d`. -/
theorem sub_mul_le_pow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d) (ha : 1 ≤ a)
    (k n : ℕ) (hn : n ≤ n₀ * b ^ k) :
    (a - b ^ d) * T n ≤ ((a - b ^ d) * T₀ + c * n₀ ^ d * b ^ d) * a ^ k := by
  have hT := h.le_geom_sum ha k n hn
  rcases le_or_gt (b ^ d) a with hq | hq
  · have hg : (a - b ^ d) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i) ≤ b ^ d * a ^ k := by
      calc (a - b ^ d) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)
          = b ^ d * ((∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - 1 - i)) * (a - b ^ d)) := by
            rw [sum_pow_mul_pow_sub]; ring
        _ ≤ b ^ d * a ^ k := by
            rw [geom_sum₂_mul_of_ge hq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    calc (a - b ^ d) * T n
        ≤ (a - b ^ d) * (a ^ k * T₀ + c * n₀ ^ d * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)) :=
          Nat.mul_le_mul_left _ hT
      _ = (a - b ^ d) * a ^ k * T₀ +
            c * n₀ ^ d * ((a - b ^ d) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)) := by ring
      _ ≤ (a - b ^ d) * a ^ k * T₀ + c * n₀ ^ d * (b ^ d * a ^ k) := by gcongr
      _ = _ := by ring
  · rw [Nat.sub_eq_zero_of_le hq.le]
    simp

/-- **Master theorem, case 2** (`a = b ^ d`), for `n ≤ n₀ b ^ k`:
`T n ≤ a ^ k (T₀ + c n₀ ^ d k)`. -/
theorem le_pow_mul (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d) (ha : 1 ≤ a)
    (had : a = b ^ d) (k n : ℕ) (hn : n ≤ n₀ * b ^ k) :
    T n ≤ a ^ k * (T₀ + c * n₀ ^ d * k) := by
  have hT := h.le_geom_sum ha k n hn
  rw [← had, sum_pow_mul_pow_sub_self] at hT
  calc T n ≤ _ := hT
    _ = _ := by ring

/-- **Master theorem, case 3** (`a < b ^ d`), for `n ≤ n₀ b ^ k`:
`(b ^ d - a) T n ≤ ((b ^ d - a) T₀ + c n₀ ^ d b ^ d) (b ^ d) ^ k`. The bound holds for every
`a ≥ 1` and is trivial when `a ≥ b ^ d`. -/
theorem pow_sub_mul_le_pow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d) (ha : 1 ≤ a)
    (k n : ℕ) (hn : n ≤ n₀ * b ^ k) :
    (b ^ d - a) * T n ≤ ((b ^ d - a) * T₀ + c * n₀ ^ d * b ^ d) * (b ^ d) ^ k := by
  have hT := h.le_geom_sum ha k n hn
  rcases le_or_gt a (b ^ d) with hq | hq
  · have hg : (b ^ d - a) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i) ≤ b ^ d * (b ^ d) ^ k := by
      calc (b ^ d - a) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)
          = b ^ d * ((∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - 1 - i)) * (b ^ d - a)) := by
            rw [sum_pow_mul_pow_sub]; ring
        _ ≤ b ^ d * (b ^ d) ^ k := by
            rw [geom_sum₂_mul_of_le hq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have hak : a ^ k ≤ (b ^ d) ^ k := Nat.pow_le_pow_left hq k
    calc (b ^ d - a) * T n
        ≤ (b ^ d - a) * (a ^ k * T₀ + c * n₀ ^ d * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)) :=
          Nat.mul_le_mul_left _ hT
      _ = (b ^ d - a) * a ^ k * T₀ +
            c * n₀ ^ d * ((b ^ d - a) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)) := by ring
      _ ≤ (b ^ d - a) * (b ^ d) ^ k * T₀ + c * n₀ ^ d * (b ^ d * (b ^ d) ^ k) := by
          gcongr
      _ = _ := by ring
  · rw [Nat.sub_eq_zero_of_le hq.le]
    simp

end DivideConquerBound

/-! ### Bounds in terms of `n` -/

private theorem le_mul_pow_clog {b n₀ : ℕ} (hb : 1 < b) (hn₀ : 1 ≤ n₀) (n : ℕ) :
    n ≤ n₀ * b ^ clog b n :=
  (le_pow_clog hb n).trans (Nat.le_mul_of_pos_left _ hn₀)

private theorem ceilStep_lt {b m : ℕ} (hb : 1 < b) (hm : 1 < m) : (m + b - 1) / b < m := by
  refine (Nat.div_lt_iff_lt_mul (by omega)).mpr ?_
  have hmul : 1 * (m - 2) ≤ b * (m - 2) := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_comm b (m - 2)] at hmul
  have hlt : m + b - 1 < 2 * b + (m - 2) * b := by omega
  calc m + b - 1 < 2 * b + (m - 2) * b := hlt
    _ = (2 + (m - 2)) * b := (Nat.add_mul 2 (m - 2) b).symm
    _ = m * b := by rw [show 2 + (m - 2) = m by omega]

namespace DivideConquerBound

variable {T f : ℕ → ℕ} {a b n₀ T₀ c d : ℕ}

/-- **Master theorem, case 1** with `K = ⌈log_b n⌉`:
`(a - b ^ d) T n ≤ ((a - b ^ d) T₀ + c n₀ ^ d b ^ d) a ^ K`. -/
theorem sub_mul_le_pow_clog (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) (n : ℕ) :
    (a - b ^ d) * T n ≤ ((a - b ^ d) * T₀ + c * n₀ ^ d * b ^ d) * a ^ clog b n :=
  h.sub_mul_le_pow ha _ n (le_mul_pow_clog hb hn₀ n)

/-- **Master theorem, case 2** with `K = ⌈log_b n⌉`: if `a = b ^ d` and `n ≠ 0`, then
`T n ≤ (b n) ^ d (T₀ + c n₀ ^ d K)`. -/
theorem le_mul_pow_mul_clog (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) (had : a = b ^ d) {n : ℕ} (hn : n ≠ 0) :
    T n ≤ (b * n) ^ d * (T₀ + c * n₀ ^ d * clog b n) := by
  refine (h.le_pow_mul ha had _ n (le_mul_pow_clog hb hn₀ n)).trans
    (Nat.mul_le_mul_right _ ?_)
  rw [had, ← pow_mul, mul_comm d, pow_mul]
  exact Nat.pow_le_pow_left (pow_clog_le_mul hb hn) d

/-- **Master theorem, case 3** in terms of `n`: if `n ≠ 0`, then
`(b ^ d - a) T n ≤ ((b ^ d - a) T₀ + c n₀ ^ d b ^ d) (b n) ^ d`. -/
theorem pow_sub_mul_le_mul_pow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) {n : ℕ} (hn : n ≠ 0) :
    (b ^ d - a) * T n ≤ ((b ^ d - a) * T₀ + c * n₀ ^ d * b ^ d) * (b * n) ^ d := by
  refine (h.pow_sub_mul_le_pow ha _ n (le_mul_pow_clog hb hn₀ n)).trans
    (Nat.mul_le_mul_left _ ?_)
  rw [← pow_mul, mul_comm d, pow_mul]
  exact Nat.pow_le_pow_left (pow_clog_le_mul hb hn) d

/-- Raise the threshold of a divide-and-conquer upper bound from `n₀` to `n₁ ≥ n₀`. -/
theorem lift_threshold (h : DivideConquerBound T a b n₀ T₀ f) {n₁ : ℕ} (hn : n₀ ≤ n₁)
    {T₁ : ℕ} (hbase : ∀ n ≤ n₁, T n ≤ T₁) : DivideConquerBound T a b n₁ T₁ f :=
  ⟨hbase, fun n hlt => h.step n (lt_of_le_of_lt hn hlt)⟩

/-- **Master theorem, case 3 under the general regularity condition.** If `f` is monotone,
`0 < f (n₀ + 1)`, and `q * (a * f ⌈m/b⌉) ≤ p * f m` for all `m > n₀` with `p < q`, then
`(q - p) * T n ≤ q * (a * T₀ + 1) * f n` for all `n > n₀`. -/
theorem le_mul_of_regular (h : DivideConquerBound T a b n₀ T₀ f) (hb : 1 < b) (hn₀ : 1 ≤ n₀)
    (hf : Monotone f) {p q : ℕ} (hpq : p < q)
    (hreg : ∀ m, n₀ < m → q * (a * f ((m + b - 1) / b)) ≤ p * f m)
    (hfpos : 0 < f (n₀ + 1)) :
    ∀ n, n₀ < n → (q - p) * T n ≤ q * (a * T₀ + 1) * f n := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · intro n hn
    have hex : ∀ M : ℕ, ∃ S, ∀ m ≤ M, T m ≤ S := by
      intro M
      induction M with
      | zero => exact ⟨T 0, fun m hm => by rw [Nat.le_zero.mp hm]⟩
      | succ M ih =>
        obtain ⟨S, hS⟩ := ih
        exact ⟨max S (T (M + 1)), fun m hm =>
          (Nat.le_succ_iff.mp hm).elim (fun h => (hS m h).trans (le_max_left _ _))
            (fun h => h ▸ le_max_right _ _)⟩
    obtain ⟨S, hS⟩ := hex ((n + b - 1) / b)
    have hTn : T n ≤ f n := by simpa using h.step n hn S hS
    calc (q - p) * T n ≤ (q - p) * f n := Nat.mul_le_mul_left _ hTn
      _ ≤ q * f n := Nat.mul_le_mul_right _ (Nat.sub_le q p)
      _ = q * (0 * T₀ + 1) * f n := by ring
  · intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      set M := (n + b - 1) / b
      have hM_lt : M < n := ceilStep_lt hb (by omega)
      have hfn_pos : 1 ≤ f n := hfpos.trans_le (hf hn)
      rcases le_or_gt M n₀ with hM | hM
      · have hTn : T n ≤ a * T₀ + f n := h.step n hn T₀ fun m hm => h.base m (hm.trans hM)
        calc (q - p) * T n ≤ (q - p) * (a * T₀ + f n) := Nat.mul_le_mul_left _ hTn
          _ ≤ q * (a * T₀ + f n) := Nat.mul_le_mul_right _ (Nat.sub_le q p)
          _ = q * (a * T₀ * 1 + f n) := by rw [Nat.mul_one]
          _ ≤ q * (a * T₀ * f n + f n) := by gcongr
          _ = q * (a * T₀ + 1) * f n := by ring
      · set C := q * (a * T₀ + 1)
        set S := (C * f M) / (q - p)
        have hqp : 0 < q - p := Nat.sub_pos_of_lt hpq
        have hfM_pos : 1 ≤ f M := hfpos.trans_le (hf hM)
        have hS : ∀ m ≤ M, T m ≤ S := by
          intro m hm
          refine (Nat.le_div_iff_mul_le hqp).mpr ?_
          rw [Nat.mul_comm]
          rcases le_or_gt m n₀ with hm0 | hm0
          · have h1 : (q - p) * T m ≤ q * (a * T₀) :=
              Nat.mul_le_mul (Nat.sub_le q p) ((h.base m hm0).trans (Nat.le_mul_of_pos_left T₀ ha))
            have hC : q * (a * T₀) ≤ C := by
              dsimp [C]
              rw [mul_add, mul_one]
              exact Nat.le_add_right _ _
            calc (q - p) * T m ≤ q * (a * T₀) := h1
              _ ≤ C := hC
              _ = C * 1 := (Nat.mul_one C).symm
              _ ≤ C * f M := Nat.mul_le_mul_left C hfM_pos
          · exact (ih m (hm.trans_lt hM_lt) hm0).trans (Nat.mul_le_mul_left C (hf hm))
        have hTn : T n ≤ a * S + f n := h.step n hn S hS
        have hqS : (q - p) * S ≤ C * f M := Nat.mul_div_le (C * f M) (q - p)
        have hqC : q ≤ C := Nat.le_mul_of_pos_right q (Nat.succ_pos _)
        have hmul : q * ((q - p) * T n) ≤ q * (C * f n) := by
          calc q * ((q - p) * T n) ≤ q * ((q - p) * (a * S + f n)) := by gcongr
            _ = q * (a * ((q - p) * S) + (q - p) * f n) := by ring
            _ ≤ q * (a * (C * f M) + (q - p) * f n) := by gcongr
            _ = C * (q * (a * f M)) + q * (q - p) * f n := by ring
            _ ≤ C * (p * f n) + C * (q - p) * f n := by
                have := hreg n hn
                gcongr
            _ = (p + (q - p)) * (C * f n) := by ring
            _ = q * (C * f n) := by rw [Nat.add_sub_cancel' hpq.le]
        exact Nat.le_of_mul_le_mul_left hmul (by omega)

end DivideConquerBound

/-! ### Lower bounds and equality recurrences -/

/-- `T` satisfies the divide-and-conquer lower inequality `a T(⌊n/b⌋) + f n ≤ T n` above `n₀`,
with `T₀ ≤ T n` on `[1, n₀]`. The recursive step quantifies over every lower bound `S` of `T` on
`[⌊n/b⌋, ⌈n/b⌉]`, so subproblems of any size in that range (such as `⌊n/b⌋`, `⌈n/b⌉`, or a mix of
both) are covered. -/
structure DivideConquerLowerBound (T : ℕ → ℕ) (a b n₀ T₀ : ℕ) (f : ℕ → ℕ) : Prop where
  /-- The base lower bound: `T₀ ≤ T n` for `1 ≤ n ≤ n₀`. -/
  base : ∀ n, 1 ≤ n → n ≤ n₀ → T₀ ≤ T n
  /-- The recursive step: `a S + f n ≤ T n` whenever `S` lower-bounds `T` on `[⌊n/b⌋, ⌈n/b⌉]`. -/
  step : ∀ n, n₀ < n → ∀ S, (∀ m, n / b ≤ m → m ≤ (n + b - 1) / b → S ≤ T m) →
    a * S + f n ≤ T n

namespace DivideConquerLowerBound

variable {T f : ℕ → ℕ} {a b n₀ T₀ c d : ℕ}

/-- Raise the threshold of a divide-and-conquer lower bound from `n₀` to `n₁ ≥ n₀`. -/
theorem lift_threshold (h : DivideConquerLowerBound T a b n₀ T₀ f) {n₁ : ℕ} (hn : n₀ ≤ n₁)
    {T₁ : ℕ} (hbase : ∀ n, 1 ≤ n → n ≤ n₁ → T₁ ≤ T n) :
    DivideConquerLowerBound T a b n₁ T₁ f :=
  ⟨hbase, fun n hlt => h.step n (lt_of_le_of_lt hn hlt)⟩

/-- Weaken the base lower bound to `0`. -/
theorem zero_base (h : DivideConquerLowerBound T a b n₀ T₀ f) :
    DivideConquerLowerBound T a b n₀ 0 f :=
  ⟨fun _ _ _ => Nat.zero_le _, h.step⟩

/-- The driving term lower-bounds `T` above `n₀`: `f n ≤ T n` for `n > n₀`. -/
theorem driving_le (h : DivideConquerLowerBound T a b n₀ T₀ f) {n : ℕ} (hn : n₀ < n) :
    f n ≤ T n := by
  simpa using h.step n hn 0 (fun _ _ _ => Nat.zero_le _)

/-- When `a ≥ 1`, `b ≥ 2` and `b ≤ n₀ + 1`, the base lower bound `T₀ ≤ T n` holds for every
`n ≥ 1`. -/
theorem le_of_base (h : DivideConquerLowerBound T a b n₀ T₀ f) (ha : 1 ≤ a) (hb : 1 < b)
    (hbn₀ : b ≤ n₀ + 1) : ∀ n, 1 ≤ n → T₀ ≤ T n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    rcases le_or_gt n n₀ with hle | hlt
    · exact h.base n hn hle
    · have hS : ∀ m, n / b ≤ m → m ≤ (n + b - 1) / b → T₀ ≤ T m := by
        intro m hlo hhi
        have hm1 : 1 ≤ m :=
          (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.one_mul]; omega) |>.trans hlo
        have hm_lt : m < n := hhi.trans_lt (ceilStep_lt hb (by omega))
        exact ih m hm_lt hm1
      have := h.step n hlt T₀ hS
      have hmul : T₀ ≤ a * T₀ := Nat.le_mul_of_pos_left T₀ ha
      omega

/-- **Unrolling the lower bound.** For monotone `f` and `n₀ b ^ k ≤ n`,
`a ^ k T₀ + ∑ i < k, a ^ i f (n₀ b ^ (k - i)) ≤ T n`, provided `T₀ = 0` or `b ≤ n₀ + 1`. -/
theorem sum_le (h : DivideConquerLowerBound T a b n₀ T₀ f) (ha : 1 ≤ a) (hb : 1 < b)
    (hn₀ : 1 ≤ n₀) (hbn₀ : T₀ = 0 ∨ b ≤ n₀ + 1) (hf : Monotone f) :
    ∀ k n, n₀ * b ^ k ≤ n →
      a ^ k * T₀ + ∑ i ∈ range k, a ^ i * f (n₀ * b ^ (k - i)) ≤ T n := by
  intro k
  induction k with
  | zero =>
    intro n hn
    simp only [pow_zero, mul_one, one_mul, range_zero, sum_empty, add_zero] at hn ⊢
    rcases hbn₀ with rfl | hbn₀'
    · exact Nat.zero_le _
    · exact h.le_of_base ha hb hbn₀' n (hn₀.trans hn)
  | succ k ih =>
    intro n hn
    have hlt : n₀ < n := by
      have h1 : n₀ * 2 ≤ n₀ * b := Nat.mul_le_mul_left n₀ hb
      have h2 : n₀ * b ≤ n₀ * b ^ (k + 1) :=
        Nat.mul_le_mul_left n₀ (Nat.le_self_pow (Nat.succ_ne_zero k) b)
      omega
    have hdiv : n₀ * b ^ k ≤ n / b := by
      refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
      rw [mul_assoc, ← pow_succ]
      exact hn
    have hf_le : f (n₀ * b ^ (k + 1)) ≤ f n := hf hn
    have hstep := h.step n hlt _ fun m hlo _ => ih m (hdiv.trans hlo)
    calc a ^ (k + 1) * T₀ + ∑ i ∈ range (k + 1), a ^ i * f (n₀ * b ^ (k + 1 - i))
        = a * (a ^ k * T₀ + ∑ i ∈ range k, a ^ i * f (n₀ * b ^ (k - i))) +
            f (n₀ * b ^ (k + 1)) := by
          rw [sum_range_succ', mul_add, mul_sum]
          simp only [Nat.add_sub_add_right, Nat.sub_zero, pow_zero, one_mul, pow_succ',
            mul_assoc]
          ac_rfl
      _ ≤ a * (a ^ k * T₀ + ∑ i ∈ range k, a ^ i * f (n₀ * b ^ (k - i))) + f n :=
          Nat.add_le_add_left hf_le _
      _ ≤ T n := hstep

/-- The unrolled lower bound for `f n = c n ^ d`. -/
theorem geom_sum_le (h : DivideConquerLowerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hbn₀ : T₀ = 0 ∨ b ≤ n₀ + 1) :
    ∀ k n, n₀ * b ^ k ≤ n →
      a ^ k * T₀ + c * n₀ ^ d * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i) ≤ T n := by
  intro k n hn
  have := h.sum_le ha hb hn₀ hbn₀
    (fun x y hxy => Nat.mul_le_mul_left c (Nat.pow_le_pow_left hxy d)) k n hn
  rwa [sum_pow_mul_poly] at this

/-- Lower bound from the base value at `k = ⌊log_b (n / n₀)⌋` when `b ≤ n₀ + 1`. -/
theorem pow_log_mul_le (h : DivideConquerLowerBound T a b n₀ T₀ f) (ha : 1 ≤ a) (hb : 1 < b)
    (hn₀ : 1 ≤ n₀) (hbn₀ : b ≤ n₀ + 1) (hf : Monotone f) {n : ℕ} (hn : n₀ ≤ n) :
    a ^ Nat.log b (n / n₀) * T₀ ≤ T n := by
  have hlog : n₀ * b ^ Nat.log b (n / n₀) ≤ n := by
    have h1 : 1 ≤ n / n₀ := (Nat.le_div_iff_mul_le hn₀).mpr (by simpa using hn)
    have h2 : b ^ Nat.log b (n / n₀) ≤ n / n₀ := Nat.pow_log_le_self b (by omega)
    calc n₀ * b ^ Nat.log b (n / n₀) ≤ n₀ * (n / n₀) := Nat.mul_le_mul_left n₀ h2
      _ ≤ n := Nat.mul_div_le n n₀
  exact (Nat.le_add_right _ _).trans (h.sum_le ha hb hn₀ (Or.inr hbn₀) hf _ n hlog)

/-- Lower bound from the driving term `f n = c n ^ d` at `k = ⌊log_b (n / n₀)⌋ - 1`
for `n ≥ n₀ b`. -/
theorem pow_pred_log_mul_le (h : DivideConquerLowerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) {n : ℕ} (hn : n₀ * b ≤ n) :
    c * (n₀ * b) ^ d * a ^ (Nat.log b (n / n₀) - 1) ≤ T n := by
  set k := Nat.log b (n / n₀)
  have hk_pos : 1 ≤ k := by
    refine Nat.le_log_of_pow_le hb ?_
    rw [pow_one]
    exact (Nat.le_div_iff_mul_le hn₀).mpr (by rw [mul_comm]; exact hn)
  have hpow : n₀ * b ^ k ≤ n := by
    have hdiv : 1 ≤ n / n₀ := by
      refine (Nat.le_div_iff_mul_le hn₀).mpr ?_
      calc 1 * n₀ ≤ b * n₀ := Nat.mul_le_mul_right n₀ (by omega)
        _ = n₀ * b := Nat.mul_comm b n₀
        _ ≤ n := hn
    have h1 : b ^ k ≤ n / n₀ := Nat.pow_log_le_self b (by omega)
    calc n₀ * b ^ k ≤ n₀ * (n / n₀) := Nat.mul_le_mul_left n₀ h1
      _ ≤ n := Nat.mul_div_le n n₀
  have hsum := h.zero_base.geom_sum_le ha hb hn₀ (Or.inl rfl) k n hpow
  have hterm : a ^ (k - 1) * (b ^ d) ^ 1 ≤ ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i) := by
    have hmem : k - 1 ∈ range k := mem_range.mpr (by omega)
    have heq : k - (k - 1) = 1 := by omega
    rw [← add_sum_erase _ _ hmem, heq]
    exact Nat.le_add_right _ _
  calc c * (n₀ * b) ^ d * a ^ (k - 1)
      = c * n₀ ^ d * (a ^ (k - 1) * (b ^ d) ^ 1) := by rw [mul_pow, pow_one]; ring
    _ ≤ 0 + c * n₀ ^ d * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i) := by
        rw [zero_add]
        exact Nat.mul_le_mul_left _ hterm
    _ ≤ T n := by simpa using hsum

/-- **Master theorem lower bound, case 2** (`a = b ^ d`), for `n₀ b ^ k ≤ n`:
`a ^ k (T₀ + c n₀ ^ d k) ≤ T n`. -/
theorem pow_mul_le (h : DivideConquerLowerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) (hbn₀ : T₀ = 0 ∨ b ≤ n₀ + 1)
    (had : a = b ^ d) (k n : ℕ) (hn : n₀ * b ^ k ≤ n) :
    a ^ k * (T₀ + c * n₀ ^ d * k) ≤ T n := by
  have hT := h.geom_sum_le ha hb hn₀ hbn₀ k n hn
  rw [← had, sum_pow_mul_pow_sub_self] at hT
  calc a ^ k * (T₀ + c * n₀ ^ d * k) = a ^ k * T₀ + c * n₀ ^ d * (k * a ^ k) := by ring
    _ ≤ T n := hT

/-- **Master theorem lower bound, case 2** (`a = b ^ d`) in terms of `n`:
`c n₀ ^ d ⌊log_b (n / n₀)⌋ n ^ d ≤ (n₀ b) ^ d T n` for `n ≥ n₀`. -/
theorem mul_pow_mul_log_le (h : DivideConquerLowerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) (had : a = b ^ d) {n : ℕ} (hn : n₀ ≤ n) :
    c * n₀ ^ d * Nat.log b (n / n₀) * n ^ d ≤ (n₀ * b) ^ d * T n := by
  set k := Nat.log b (n / n₀)
  have hdiv_pos : 0 < n / n₀ :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one ((Nat.le_div_iff_mul_le hn₀).mpr (by simpa using hn))
  have hpow : n₀ * b ^ k ≤ n := by
    calc n₀ * b ^ k ≤ n₀ * (n / n₀) :=
          Nat.mul_le_mul_left n₀ (Nat.pow_log_le_self b hdiv_pos.ne')
      _ ≤ n := Nat.mul_div_le n n₀
  have hlt : n < n₀ * b ^ (k + 1) := by
    have := Nat.lt_pow_succ_log_self hb (n / n₀)
    have := (Nat.div_lt_iff_lt_mul hn₀).mp this
    rwa [Nat.mul_comm] at this
  have hnd : n ^ d ≤ (n₀ * b) ^ d * a ^ k := by
    calc n ^ d ≤ (n₀ * b ^ (k + 1)) ^ d := Nat.pow_le_pow_left hlt.le d
      _ = (n₀ * b) ^ d * (b ^ d) ^ k := by rw [pow_succ', ← mul_assoc, mul_pow, ← pow_mul,
          ← pow_mul, mul_comm k d]
      _ = (n₀ * b) ^ d * a ^ k := by rw [← had]
  have hT := h.zero_base.pow_mul_le ha hb hn₀ (Or.inl rfl) had k n hpow
  simp only [zero_add] at hT
  calc c * n₀ ^ d * k * n ^ d ≤ c * n₀ ^ d * k * ((n₀ * b) ^ d * a ^ k) :=
        Nat.mul_le_mul_left _ hnd
    _ = (n₀ * b) ^ d * (a ^ k * (c * n₀ ^ d * k)) := by ring
    _ ≤ (n₀ * b) ^ d * T n := Nat.mul_le_mul_left _ hT

end DivideConquerLowerBound

/-- `T` satisfies an equality divide-and-conquer recurrence `T n = ∑ i ∈ range a, T (sub i) + f n`
above `n₀`, with every subproblem size `sub i ∈ [⌊n/b⌋, ⌈n/b⌉]` and base bounds
`T_lo ≤ T n ≤ T_hi` (`T n ≤ T_hi` at `n = 0`). -/
structure DivideConquerRecurrence (T : ℕ → ℕ) (a b n₀ T_lo T_hi : ℕ) (f : ℕ → ℕ) : Prop where
  /-- The upper base bound: `T n ≤ T_hi` for `n ≤ n₀`. -/
  base_le : ∀ n ≤ n₀, T n ≤ T_hi
  /-- The lower base bound: `T_lo ≤ T n` for `1 ≤ n ≤ n₀`. -/
  le_base : ∀ n, 1 ≤ n → n ≤ n₀ → T_lo ≤ T n
  /-- The recursive step: `T n` sums `a` subproblems of sizes in `[⌊n/b⌋, ⌈n/b⌉]` plus `f n`. -/
  step : ∀ n, n₀ < n → ∃ sub : ℕ → ℕ,
    (∀ i < a, n / b ≤ sub i ∧ sub i ≤ (n + b - 1) / b) ∧ T n = (∑ i ∈ range a, T (sub i)) + f n

namespace DivideConquerRecurrence

variable {T f : ℕ → ℕ} {a b n₀ T_lo T_hi : ℕ}

private theorem sum_range_le_mul (g : ℕ → ℕ) {a S : ℕ} (h : ∀ i < a, g i ≤ S) :
    ∑ i ∈ range a, g i ≤ a * S := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, Nat.succ_mul]
    exact Nat.add_le_add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h k (Nat.lt_succ_self k))

private theorem mul_le_sum_range (g : ℕ → ℕ) {a S : ℕ} (h : ∀ i < a, S ≤ g i) :
    a * S ≤ ∑ i ∈ range a, g i := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, Nat.succ_mul]
    exact Nat.add_le_add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h k (Nat.lt_succ_self k))

/-- Extract the upper bound `DivideConquerBound`. -/
theorem toBound (h : DivideConquerRecurrence T a b n₀ T_lo T_hi f) :
    DivideConquerBound T a b n₀ T_hi f where
  base := h.base_le
  step n hn S hS := by
    obtain ⟨sub, hsub, hT⟩ := h.step n hn
    have hsum : ∑ i ∈ range a, T (sub i) ≤ a * S :=
      sum_range_le_mul (fun i => T (sub i)) fun i hi => hS (sub i) (hsub i hi).2
    omega

/-- Extract the lower bound `DivideConquerLowerBound`. -/
theorem toLowerBound (h : DivideConquerRecurrence T a b n₀ T_lo T_hi f) :
    DivideConquerLowerBound T a b n₀ T_lo f where
  base := h.le_base
  step n hn S hS := by
    obtain ⟨sub, hsub, hT⟩ := h.step n hn
    have hsum : a * S ≤ ∑ i ∈ range a, T (sub i) :=
      mul_le_sum_range (fun i => T (sub i)) fun i hi =>
        let hbounds := hsub i hi
        hS (sub i) hbounds.1 hbounds.2
    omega

/-- Construct `DivideConquerRecurrence` from `T n = a * T ⌈n/b⌉ + f n` above `n₀`. -/
theorem of_ceil (hb : 1 ≤ b)
    (base_le : ∀ n ≤ n₀, T n ≤ T_hi)
    (le_base : ∀ n, 1 ≤ n → n ≤ n₀ → T_lo ≤ T n)
    (step : ∀ n, n₀ < n → T n = a * T ((n + b - 1) / b) + f n) :
    DivideConquerRecurrence T a b n₀ T_lo T_hi f where
  base_le := base_le
  le_base := le_base
  step n hn := ⟨fun _ => (n + b - 1) / b,
    fun _ _ => ⟨Nat.div_le_div_right (by omega), le_rfl⟩,
    by simpa [sum_const, card_range, nsmul_eq_mul] using step n hn⟩

/-- Construct `DivideConquerRecurrence` from `T n = a * T ⌊n/b⌋ + f n` above `n₀`. -/
theorem of_floor (hb : 1 ≤ b)
    (base_le : ∀ n ≤ n₀, T n ≤ T_hi)
    (le_base : ∀ n, 1 ≤ n → n ≤ n₀ → T_lo ≤ T n)
    (step : ∀ n, n₀ < n → T n = a * T (n / b) + f n) :
    DivideConquerRecurrence T a b n₀ T_lo T_hi f where
  base_le := base_le
  le_base := le_base
  step n hn := ⟨fun _ => n / b,
    fun _ _ => ⟨le_rfl, Nat.div_le_div_right (by omega)⟩,
    by simpa [sum_const, card_range, nsmul_eq_mul] using step n hn⟩

end DivideConquerRecurrence

end Nat
