/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ColumnAdderAt

/-!
# The scale `n / log n`

`DivLog n = n / (log₂ n + 1) + log₂ n + 1` is the scale `n / log n` written so that it satisfies
the regularity `Scale` of Theorem 2.4 for every `n`. The summand `log₂ n + 1` is needed only for
small `n`: `Scale` asks `log₂ n + 1 ≤ D n` for every `n`, which fails for `n / (log₂ n + 1) + 1` at
`n = 4`. Up to constant factors `DivLog n` is `n / (log₂ n + 1) + 1` (`divLog_le`), the smallest
scale whose values fit the carry of the column adder over schedules (`CarryFits`), so it is the
target scale of the remark of §8.

`DivLog` is not monotone (it drops from `127` to `128`), so, as for `SqrtLog`, linear changes of
the argument are handled by monotonicity up to a factor `2` (`divLog_le_two_mul_of_le`) and a
bound at `a · m + b` (`divLog_mul_add_le`).

## Main definitions

* `Cslib.Complexity.NtimeDspace.Cross.DivLog`.

## Main results

* `Cslib.Complexity.NtimeDspace.Cross.scale_divLog : Scale DivLog`.
* `Cslib.Complexity.NtimeDspace.Cross.carryFits_divLog : Exact.CarryFits DivLog`.
* `Cslib.Complexity.NtimeDspace.Cross.divLog_le`: `DivLog n ≤ 5 · (n / (log₂ n + 1)) + 5`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open Filter

/-- The scale `n / log n`: `n / (log₂ n + 1) + log₂ n + 1`. -/
def DivLog (n : ℕ) : ℕ := n / (n.log2 + 1) + n.log2 + 1

theorem one_le_divLog (n : ℕ) : 1 ≤ DivLog n := Nat.le_add_left _ _

/-- `2 L ≤ 2 ^ L`. -/
theorem two_mul_le_two_pow (L : ℕ) : 2 * L ≤ 2 ^ L := by
  rcases L with _ | L
  · simp
  · have : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
    rw [pow_succ]; omega

/-- `DivLog n ≤ n + 1`. -/
theorem divLog_le_succ (n : ℕ) : DivLog n ≤ n + 1 := by
  unfold DivLog
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  rcases Nat.eq_zero_or_pos n.log2 with hL | hL
  · rw [hL]; simp
  · have h2L : 2 ^ n.log2 ≤ n := Nat.log2_self_le (by omega)
    have h1 := two_mul_le_two_pow n.log2
    have h3 : n / (n.log2 + 1) ≤ n / 2 := Nat.div_le_div_left (by omega) (by omega)
    omega

/-- **`DivLog` is monotone up to a factor `2`.** -/
theorem divLog_le_two_mul_of_le {m m' : ℕ} (h : m ≤ m') : DivLog m ≤ 2 * DivLog m' := by
  unfold DivLog
  have hLL : m.log2 ≤ m'.log2 := log2_mono h
  have hm : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  generalize hL : m.log2 = L at *
  generalize hK : m'.log2 = K at *
  by_cases hcase : K + 1 ≤ 2 * (L + 1)
  · have h1 : m / (L + 1) ≤ m' / (L + 1) := Nat.div_le_div_right h
    have h2 : m' / (L + 1) ≤ 2 * (m' / ((L + 1) * 2)) + 1 := by
      rw [← Nat.div_div_eq_div_mul]; omega
    have h3 : m' / ((L + 1) * 2) ≤ m' / (K + 1) := Nat.div_le_div_left (by omega) (by omega)
    omega
  · push Not at hcase
    -- here `m ≤ 2 · (m' / (K + 1))`
    have hm'0 : m' ≠ 0 := by
      intro h0; subst h0; simp at hK; omega
    have hm' : 2 ^ K ≤ m' := hK ▸ Nat.log2_self_le hm'0
    set j := K + 1 - (L + 1) with hj
    have hj2 : K + 1 ≤ 2 * j := by omega
    have hjpow : K + 1 ≤ 2 ^ j := hj2.trans (two_mul_le_two_pow j)
    have hsplit : 2 ^ (K + 1) = 2 ^ (L + 1) * 2 ^ j := by rw [← pow_add]; congr 1; omega
    have hkey : 2 ^ (L + 1) * (K + 1) ≤ 2 * m' := by
      calc 2 ^ (L + 1) * (K + 1) ≤ 2 ^ (L + 1) * 2 ^ j := Nat.mul_le_mul_left _ hjpow
        _ = 2 ^ (K + 1) := hsplit.symm
        _ = 2 * 2 ^ K := by rw [pow_succ]; ring
        _ ≤ 2 * m' := Nat.mul_le_mul_left _ hm'
    have hdiv : m' < m' / (K + 1) * (K + 1) + (K + 1) := Nat.lt_div_mul_add (by omega)
    have hlt : 2 ^ (L + 1) < 2 * (m' / (K + 1) + 1) := by
      have : 2 ^ (L + 1) * (K + 1) < 2 * (m' / (K + 1) + 1) * (K + 1) := by nlinarith
      exact Nat.lt_of_mul_lt_mul_right this
    have h6 : m / (L + 1) ≤ m := Nat.div_le_self _ _
    omega

/-- **Linear changes of the argument change `DivLog` by a constant factor.** -/
theorem divLog_mul_add_le (a b m : ℕ) (ha : 1 ≤ a) :
    DivLog (a * m + b) ≤ (a + b + 1) * DivLog m := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · -- small `m`: `DivLog (a m + b) ≤ a m + b + 1 ≤ a + b + 1`
    have h1 := divLog_le_succ (a * m + b)
    have h2 : a * m ≤ a := by
      calc a * m ≤ a * 1 := Nat.mul_le_mul_left _ (by omega)
        _ = a := by ring
    have h3 : a + b + 1 ≤ (a + b + 1) * DivLog m := Nat.le_mul_of_pos_right _ (one_le_divLog m)
    omega
  unfold DivLog
  have hmle : m ≤ a * m + b := by nlinarith
  have hLL : m.log2 ≤ (a * m + b).log2 := log2_mono hmle
  have hL1 : 1 ≤ m.log2 := (Nat.le_log2 (by omega)).mpr (by omega)
  -- `log₂ (a m + b) ≤ log₂ m + a + b`
  have hlog : (a * m + b).log2 < m.log2 + 1 + (a + b) := by
    have hm2 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
    have hab : a + b < 2 ^ (a + b) := Nat.lt_two_pow_self
    have hlt : a * m + b < 2 ^ (m.log2 + 1 + (a + b)) := by
      rw [pow_add]
      have : a * m + b ≤ (a + b) * m := by nlinarith
      calc a * m + b ≤ (a + b) * m := this
        _ < 2 ^ (a + b) * 2 ^ (m.log2 + 1) := by
            have := Nat.mul_le_mul_right m hab.le
            have := Nat.mul_lt_mul_of_pos_left hm2 (Nat.two_pow_pos (a + b))
            nlinarith
        _ = 2 ^ (m.log2 + 1) * 2 ^ (a + b) := by ring
    exact (Nat.log2_lt (by omega)).mpr hlt
  generalize hL : m.log2 = L at *
  generalize hK : (a * m + b).log2 = K at *
  have hs0 : 0 < L + 1 := by omega
  have h1 : (a * m + b) / (K + 1) ≤ (a * m + b) / (L + 1) := Nat.div_le_div_left (by omega) hs0
  have h2 : (a * m + b) / (L + 1) < a * (m / (L + 1)) + a + b + 1 := by
    rw [Nat.div_lt_iff_lt_mul hs0]
    have hdm : m < (L + 1) * (m / (L + 1)) + (L + 1) := by
      have := Nat.lt_div_mul_add (a := m) hs0
      rw [mul_comm] at this
      omega
    nlinarith
  have h3 : (a + b + 1) * (m / (L + 1) + L + 1) =
      a * (m / (L + 1)) + (b + 1) * (m / (L + 1)) + (a + b + 1) * (L + 1) := by ring
  have h4 : (a + b) * 2 ≤ (a + b) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  have h5 : (a + b + 1) * (L + 1) = (a + b) * (L + 1) + (L + 1) := by ring
  generalize m / (L + 1) = q at *
  generalize (a * m + b) / (K + 1) = q₁ at *
  generalize (a * m + b) / (L + 1) = q₂ at *
  generalize (a + b) * (L + 1) = r at *
  nlinarith

/-- A value at most linear in `m` changes `DivLog` by a constant factor. -/
theorem divLog_le_of_le_mul_add {τ m : ℕ} (a b : ℕ) (ha : 1 ≤ a) (h : τ ≤ a * m + b) :
    DivLog τ ≤ 2 * (a + b + 1) * DivLog m := by
  have := divLog_le_two_mul_of_le h
  have := divLog_mul_add_le a b m ha
  nlinarith

/-- `c · DivLog n + c ≤ n` eventually. -/
theorem divLog_sublinear (c : ℕ) : ∀ᶠ n in atTop, c * DivLog n + c ≤ n := by
  filter_upwards [Polylog.eventually_polylog_le (4 * c + 4) 1,
    Polylog.tendsto_log2.eventually (eventually_ge_atTop (2 * c))] with n hn hL
  rw [pow_one] at hn
  unfold DivLog
  set L := n.log2
  set q := n / (L + 1)
  have h1 : 2 * c * q ≤ (L + 1) * q := Nat.mul_le_mul_right q (by omega)
  have h2 : (L + 1) * q ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n (L + 1)
  have h3 : c * (q + L + 1) + c = c * q + c * (L + 1) + c := by ring
  nlinarith

/-- **`DivLog` is a scale.** -/
theorem scale_divLog : Scale DivLog :=
  ⟨fun _ => Nat.le_add_left _ _, fun a b ha h => divLog_le_of_le_mul_add a b ha h,
    divLog_sublinear⟩

/-- **`DivLog` fits the carry of the column adder**: `numBlocks n ≤ n / (log₂ n + 1) + 1`. -/
theorem carryFits_divLog : Exact.CarryFits DivLog :=
  Exact.carryFits_of_div_log_le (c := 1) one_le_divLog
    (Eventually.of_forall fun _ => by unfold DivLog; omega)

/-- `(L + 1)² ≤ 4 · 2 ^ L`. -/
theorem sq_succ_le_four_mul_two_pow (L : ℕ) : (L + 1) * (L + 1) ≤ 4 * 2 ^ L := by
  rcases Nat.lt_or_ge L 3 with h | h
  · interval_cases L <;> norm_num
  · have := sq_le_two_pow (L + 1) (by omega)
    rw [pow_succ] at this
    omega

/-- **`DivLog n` is `n / (log₂ n + 1)` up to constants**: `DivLog n ≤ 5 · (n / (log₂ n + 1)) + 5`.
-/
theorem divLog_le (n : ℕ) : DivLog n ≤ 5 * (n / (n.log2 + 1)) + 5 := by
  unfold DivLog
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  have h2L : 2 ^ n.log2 ≤ n := Nat.log2_self_le (by omega)
  have hsq := sq_succ_le_four_mul_two_pow n.log2
  have hdiv : n < n / (n.log2 + 1) * (n.log2 + 1) + (n.log2 + 1) := Nat.lt_div_mul_add (by omega)
  generalize n.log2 = L at *
  generalize n / (L + 1) = q at *
  -- `(L + 1)² ≤ 4 n < 4 (L + 1) (q + 1)`
  have : (L + 1) * (L + 1) < 4 * (q + 1) * (L + 1) := by nlinarith
  have := Nat.lt_of_mul_lt_mul_right this
  omega

end Cslib.Complexity.NtimeDspace.Cross
