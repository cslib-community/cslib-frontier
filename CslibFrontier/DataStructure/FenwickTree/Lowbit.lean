/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Lowest-Set-Bit Combinatorics for Fenwick Trees

This module develops the binary arithmetic and interval combinatorics underlying Fenwick trees
(binary indexed trees, `[Fenwick1994]`, "PRINCIPLES", pp. 328–329, and "OPERATIONS AND CODE TO
HANDLE THE STRUCTURE", pp. 329–330).

For a `1`-based index `m ≥ 1`, `lowbit m` is the value `2 ^ k` of the least significant `1`-bit of
`m` (conventionally written `m & -m` in two's-complement arithmetic), and node `m` aggregates the
half-open `0`-based index interval `[m - lowbit m, m)`:

* **Downward query chains (`downChain`):** stepping `m ↦ m - lowbit m` at least doubles the trailing
  power-of-two factor (`two_mul_lowbit_le_lowbit_sub`), terminating in at most `⌊log₂ m⌋ + 1` steps
  (`length_downChain_le_log`) and partitioning `[0, m)`.
* **Upward update chains (`upChain`):** stepping `m ↦ m + lowbit m` up to `n` likewise at least
  doubles `lowbit` (`two_mul_lowbit_le_lowbit_add`), terminating in at most `⌊log₂ n⌋ + 1` steps
  (`length_upChain_le_log`) and visiting precisely those nodes `idx ≤ n` whose interval
  `[idx - lowbit idx, idx)` contains `m - 1` (`mem_upChain_iff`).
* **Immediate-children partition (`fenwickChildren`):** for every `idx ≥ 1`, the singleton
  `{idx - 1}` together with the intervals `[c - lowbit c, c)` of immediate children
  `c + lowbit c = idx` pairwise-disjointly partition `[idx - lowbit idx, idx)`
  (`insert_biUnion_fenwickChildren`), justifying the standard BIT folklore immediate-parent
  construction (`n` parent-propagation steps).

## Main definitions

* `Cslib.DataStructure.FenwickTree.lowbit`: value of the lowest set bit of `n` (`0` at `0`).
* `Cslib.DataStructure.FenwickTree.downChain`: downward query indices `m, m - lowbit m, …`.
* `Cslib.DataStructure.FenwickTree.upChain`: upward update indices `m, m + lowbit m, … ≤ n`.
* `Cslib.DataStructure.FenwickTree.fenwickChildren`: immediate Fenwick children `c < idx` with
  `c + lowbit c = idx`.

## Main results

* `Cslib.DataStructure.FenwickTree.exists_odd_mul_lowbit`: odd-quotient power-of-two factorization
  `n = (2 * q + 1) * lowbit n` with `lowbit n = 2 ^ k`.
* `Cslib.DataStructure.FenwickTree.two_mul_lowbit_le_lowbit_sub` and
  `two_mul_lowbit_le_lowbit_add`: `lowbit` at least doubles at every downward or upward step.
* `Cslib.DataStructure.FenwickTree.fenwick_parent_bridge`: for `0 < m < idx`,
  `idx - lowbit idx < m ↔ idx - lowbit idx < m + lowbit m ∧ m + lowbit m ≤ idx`.
* `Cslib.DataStructure.FenwickTree.length_downChain_le_log`, `length_upChain_le_log`,
  `length_downChain_le_clog`, `length_upChain_le_clog`: logarithmic chain-length bounds.
* `Cslib.DataStructure.FenwickTree.mem_upChain_iff`: exact ancestor characterization.
* `Cslib.DataStructure.FenwickTree.pairwiseDisjoint_fenwickChildren` and
  `insert_biUnion_fenwickChildren`: disjoint child-interval partition for linear-time construction.

## References

* [P. M. Fenwick, *A New Data Structure for Cumulative Frequency Tables*, pp. 328–332][Fenwick1994]
-/

public section

namespace Cslib.DataStructure.FenwickTree

/-! ## Binary lowest set bit (`lowbit`) -/

/-- Value `2 ^ k` of the least significant `1`-bit of `n` (`0` when `n = 0`), defined by binary
recursion on `ℕ` (modeling two's-complement `n & -n` on fixed-width words). -/
@[expose] def lowbit (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 1 then 1
  else 2 * lowbit (n / 2)
termination_by n

@[simp]
theorem lowbit_zero : lowbit 0 = 0 := by
  rw [lowbit]; simp only [↓reduceIte]

@[simp]
theorem lowbit_one : lowbit 1 = 1 := by
  rw [lowbit]; simp only [Nat.one_ne_zero, ↓reduceIte]

theorem lowbit_pos {n : ℕ} (hn : 0 < n) : 0 < lowbit n := by
  fun_induction lowbit n with
  | case3 n _ _ ih => -- n even: 2 * lowbit (n / 2)
    have := ih (by omega)
    omega
  | _ => omega -- n = 0, or n odd

theorem lowbit_le (n : ℕ) : lowbit n ≤ n := by
  fun_induction lowbit n <;> omega

theorem lowbit_dvd (n : ℕ) : lowbit n ∣ n := by
  fun_induction lowbit n with
  | case1 => exact Nat.dvd_refl 0 -- n = 0
  | case2 n => exact one_dvd n -- n odd
  | case3 n _ _ ih => -- n even: 2 * lowbit (n / 2)
    exact ih.imp fun q hq => by rw [Nat.mul_assoc, ← hq]; omega

/-- Odd-quotient power-of-two factorization of a positive natural via `lowbit`. -/
theorem exists_odd_mul_lowbit {n : ℕ} (hn : 0 < n) :
    ∃ q k : ℕ, lowbit n = 2 ^ k ∧ n = (2 * q + 1) * 2 ^ k := by
  fun_induction lowbit n with
  | case1 => omega -- n = 0
  | case2 n => exact ⟨n / 2, 0, rfl, by omega⟩ -- n odd
  | case3 n _ _ ih => -- n even: 2 * lowbit (n / 2)
    obtain ⟨q, k, hlb, hfact⟩ := ih (by omega)
    refine ⟨q, k + 1, by rw [hlb]; ring, ?_⟩
    rw [Nat.pow_succ, ← Nat.mul_assoc, ← hfact]
    omega

theorem lowbit_odd_mul_pow_two (q k : ℕ) : lowbit ((2 * q + 1) * 2 ^ k) = 2 ^ k := by
  induction k with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one, lowbit]
    simp only [show 2 * q + 1 ≠ 0 by omega, show (2 * q + 1) % 2 = 1 by omega, ↓reduceIte]
  | succ k ih =>
    have hm_pos : 0 < (2 * q + 1) * 2 ^ k := Nat.mul_pos (by omega) (Nat.two_pow_pos k)
    rw [pow_succ', mul_left_comm, lowbit]
    generalize (2 * q + 1) * 2 ^ k = m at hm_pos ih ⊢
    simp only [show 2 * m ≠ 0 by omega, show ¬(2 * m % 2 = 1) by omega, ↓reduceIte,
      show 2 * m / 2 = m by omega, ih]

theorem lowbit_pow_two (k : ℕ) : lowbit (2 ^ k) = 2 ^ k := by
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.one_mul] using lowbit_odd_mul_pow_two 0 k

/-- Any power of two dividing `n > 0` is bounded by `lowbit n`. -/
theorem two_pow_le_lowbit_of_dvd {n k : ℕ} (hn : 0 < n) (hdvd : 2 ^ k ∣ n) :
    2 ^ k ≤ lowbit n := by
  obtain ⟨q, j, hlb, hfact⟩ := exists_odd_mul_lowbit hn
  rw [hlb]
  rcases le_or_gt k j with hle | hgt
  · exact Nat.pow_le_pow_right (by omega) hle
  · have h := (Nat.pow_dvd_pow 2 (hgt : j + 1 ≤ k)).trans hdvd
    rw [hfact, pow_succ, mul_comm (2 * q + 1)] at h
    have := Nat.dvd_of_mul_dvd_mul_left (Nat.two_pow_pos j) h
    omega

/-- Stepping downward `m ↦ m - lowbit m` at least doubles `lowbit` whenever `m - lowbit m > 0`. -/
theorem two_mul_lowbit_le_lowbit_sub {m : ℕ} (hsub : 0 < m - lowbit m) :
    2 * lowbit m ≤ lowbit (m - lowbit m) := by
  obtain ⟨q, k, hlb, hfact⟩ := exists_odd_mul_lowbit (by omega : 0 < m)
  have hdvd : 2 ^ (k + 1) ∣ m - lowbit m := ⟨q, by
    rw [hlb, hfact, show (2 * q + 1) * 2 ^ k = q * 2 ^ (k + 1) + 2 ^ k by ring,
      Nat.add_sub_cancel, mul_comm]⟩
  exact (by rw [hlb, pow_succ'] : 2 * lowbit m = 2 ^ (k + 1)) ▸
    two_pow_le_lowbit_of_dvd hsub hdvd

/-- Stepping upward `m ↦ m + lowbit m` at least doubles `lowbit` for all `m > 0`. -/
theorem two_mul_lowbit_le_lowbit_add {m : ℕ} (hm : 0 < m) :
    2 * lowbit m ≤ lowbit (m + lowbit m) := by
  obtain ⟨q, k, hlb, hfact⟩ := exists_odd_mul_lowbit hm
  have hdvd : 2 ^ (k + 1) ∣ m + lowbit m := ⟨q + 1, by rw [hlb, hfact]; ring⟩
  exact (by rw [hlb, pow_succ'] : 2 * lowbit m = 2 ^ (k + 1)) ▸
    two_pow_le_lowbit_of_dvd (by omega) hdvd

/-! ## Parent-interval bridge -/

private theorem not_dvd_two_pow_succ_between {r j x : ℕ}
    (hdvd : 2 ^ (j + 1) ∣ x)
    (hlo : 2 * r * 2 ^ j < x) (hhi : x ≤ (2 * r + 1) * 2 ^ j) : False := by
  obtain ⟨c, rfl⟩ := hdvd
  rw [show 2 ^ (j + 1) * c = 2 * c * 2 ^ j by ring] at hlo hhi
  have := Nat.lt_of_mul_lt_mul_right hlo
  have := Nat.le_of_mul_le_mul_right hhi (Nat.two_pow_pos j)
  omega

/-- Fundamental Fenwick parent-interval bridge: for `0 < m < idx`, `idx`'s interval
`[idx - lowbit idx, idx)` reaches below `m` iff it reaches below `m`'s Fenwick parent
`m + lowbit m` and `m + lowbit m ≤ idx`. -/
theorem fenwick_parent_bridge {m idx : ℕ} (hm : 0 < m) (hlt : m < idx) :
    idx - lowbit idx < m ↔ idx - lowbit idx < m + lowbit m ∧ m + lowbit m ≤ idx := by
  obtain ⟨q, k, hlb_m, hm_eq⟩ := exists_odd_mul_lowbit hm
  obtain ⟨r, j, hlb_i, hi_eq⟩ := exists_odd_mul_lowbit (Nat.lt_trans hm hlt)
  have hisub : idx - lowbit idx = 2 * r * 2 ^ j := by
    rw [hlb_i, hi_eq, add_one_mul, Nat.add_sub_cancel]
  have hmadd : m + lowbit m = (2 * q + 2) * 2 ^ k := by rw [hlb_m, hm_eq]; ring
  have hp (hkj : k < j) : 2 ^ j = 2 * 2 ^ (j - 1 - k) * 2 ^ k := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  constructor
  · intro hlo
    refine ⟨by omega, ?_⟩
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · refine (not_dvd_two_pow_succ_between ⟨(2 * q + 1) * 2 ^ (k - (j + 1)), ?_⟩
        (hisub ▸ hlo) (hi_eq ▸ hlt.le)).elim
      rw [hm_eq, mul_left_comm, ← pow_add, Nat.add_sub_cancel' (by omega)]
    · have := Nat.lt_of_mul_lt_mul_right (hisub ▸ hm_eq ▸ hlo)
      have := Nat.lt_of_mul_lt_mul_right (hm_eq ▸ hi_eq ▸ hlt)
      omega
    · have hi_k : idx = 2 * ((2 * r + 1) * 2 ^ (j - 1 - k)) * 2 ^ k := by
        rw [hi_eq, hp hkj]; ring
      rw [hm_eq, hi_k] at hlt
      rw [hmadd, hi_k]
      exact Nat.mul_le_mul_right _ (by have := Nat.lt_of_mul_lt_mul_right hlt; omega)
  · rintro ⟨hlo, hhi⟩
    rcases le_or_gt j k with hjk | hkj
    · refine (not_dvd_two_pow_succ_between ⟨(q + 1) * 2 ^ (k - j), ?_⟩
        (hisub ▸ hlo) (hi_eq ▸ hhi)).elim
      rw [hmadd, show (2 * q + 2) * 2 ^ k = (q + 1) * 2 ^ (k + 1) by ring, mul_left_comm,
        ← pow_add]
      congr 2; omega
    · have hisub_k : idx - lowbit idx = 2 * (2 * r * 2 ^ (j - 1 - k)) * 2 ^ k := by
        rw [hisub, hp hkj]; ring
      rw [hisub_k, hmadd] at hlo
      rw [hisub_k, hm_eq]
      exact Nat.mul_lt_mul_of_pos_right (by have := Nat.lt_of_mul_lt_mul_right hlo; omega)
        (Nat.two_pow_pos k)

/-! ## Downward and upward traversal chains -/

/-- Downward Fenwick query chain `m, m - lowbit m, …` down to `0`. -/
@[expose] def downChain (m : ℕ) : List ℕ :=
  if _hm : 0 < m then m :: downChain (m - lowbit m) else []
termination_by m
decreasing_by exact Nat.sub_lt _hm (lowbit_pos _hm)

/-- Upward Fenwick update chain `m, m + lowbit m, …` within `[1, n]`. -/
@[expose] def upChain (n m : ℕ) : List ℕ :=
  if _h : 0 < m ∧ m ≤ n then m :: upChain n (m + lowbit m) else []
termination_by n + 1 - m
decreasing_by
  have := lowbit_pos _h.1
  omega

@[simp]
theorem downChain_zero : downChain 0 = [] := by
  rw [downChain]
  simp only [Nat.lt_irrefl, ↓reduceDIte]

private theorem two_pow_exponent_lt_of_two_mul_le {k k' : ℕ}
    (hle : 2 * 2 ^ k ≤ 2 ^ k') : k + 1 ≤ k' :=
  (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp (by rwa [pow_succ'])

private theorem length_downChain_add_exp_le {m k : ℕ} (hm : 0 < m) (hlb : lowbit m = 2 ^ k) :
    (downChain m).length + k ≤ Nat.log 2 m + 1 := by
  fun_induction downChain m generalizing k with
  | case1 m hm ih => -- 0 < m: m :: downChain (m - lowbit m)
    rw [List.length_cons]
    have hk_log : k ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by omega) (hlb ▸ lowbit_le m)
    rcases Nat.eq_zero_or_pos (m - lowbit m) with h0 | hpos
    · rw [h0, downChain_zero, List.length_nil]
      omega
    · obtain ⟨_, k', hlb', _⟩ := exists_odd_mul_lowbit hpos
      have hk_step : k + 1 ≤ k' :=
        two_pow_exponent_lt_of_two_mul_le (hlb ▸ hlb' ▸ two_mul_lowbit_le_lowbit_sub hpos)
      have hsub := ih hpos hlb'
      have hlog_mono : Nat.log 2 (m - lowbit m) ≤ Nat.log 2 m := Nat.log_mono_right (by omega)
      omega
  | case2 => omega -- m = 0

/-- Every downward Fenwick query chain from `m > 0` has length at most `⌊log₂ m⌋ + 1`. -/
theorem length_downChain_le_log {m : ℕ} (hm : 0 < m) :
    (downChain m).length ≤ Nat.log 2 m + 1 := by
  obtain ⟨_, _, hlb, _⟩ := exists_odd_mul_lowbit hm
  exact Nat.le_of_add_right_le (length_downChain_add_exp_le hm hlb)

/-- Uniform `⌈log₂ (n + 1)⌉` bound on `downChain m` for all `m ≤ n` (`0` when `n = 0`). -/
theorem length_downChain_le_clog {m n : ℕ} (hmn : m ≤ n) :
    (downChain m).length ≤ Nat.clog 2 (n + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [downChain_zero, List.length_nil, Nat.zero_le]
  · have hlog := length_downChain_le_log hm
    have hclog : Nat.log 2 m < Nat.clog 2 (n + 1) :=
      (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr
        (Nat.lt_succ_of_le ((Nat.pow_log_le_self 2 hm.ne').trans hmn))
    omega

private theorem length_upChain_add_exp_le {n m k : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) (hlb : lowbit m = 2 ^ k) :
    (upChain n m).length + k ≤ Nat.log 2 n + 1 := by
  fun_induction upChain n m generalizing k with
  | case1 m _ ih => -- 0 < m ∧ m ≤ n: m :: upChain n (m + lowbit m)
    rw [List.length_cons]
    have hk_log : k ≤ Nat.log 2 n :=
      Nat.le_log_of_pow_le (by omega) ((hlb ▸ lowbit_le m).trans hmn)
    by_cases hnext : m + lowbit m ≤ n
    · obtain ⟨_, k', hlb', _⟩ := exists_odd_mul_lowbit (by omega : 0 < m + lowbit m)
      have hk_step : k + 1 ≤ k' :=
        two_pow_exponent_lt_of_two_mul_le (hlb ▸ hlb' ▸ two_mul_lowbit_le_lowbit_add hm)
      have hsub := ih (by omega) hnext hlb'
      omega
    · rw [upChain]
      simp only [hnext, and_false, ↓reduceDIte, List.length_nil]
      omega
  | case2 => omega -- otherwise: []

/-- Every upward Fenwick update chain from `1 ≤ m ≤ n` has length at most `⌊log₂ n⌋ + 1`. -/
theorem length_upChain_le_log {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    (upChain n m).length ≤ Nat.log 2 n + 1 := by
  obtain ⟨_, _, hlb, _⟩ := exists_odd_mul_lowbit hm
  exact Nat.le_of_add_right_le (length_upChain_add_exp_le hm hmn hlb)

/-- Uniform `⌈log₂ (n + 1)⌉` bound on `upChain n m` (`0` when `n = 0`). -/
theorem length_upChain_le_clog (n m : ℕ) :
    (upChain n m).length ≤ Nat.clog 2 (n + 1) := by
  by_cases h : 0 < m ∧ m ≤ n
  · have hlog := length_upChain_le_log h.1 h.2
    have hclog : Nat.log 2 n < Nat.clog 2 (n + 1) :=
      (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr
        (Nat.lt_succ_of_le (Nat.pow_log_le_self 2 (h.1.trans_le h.2).ne'))
    omega
  · rw [upChain]
    simp only [h, ↓reduceDIte, List.length_nil, Nat.zero_le]

private theorem ge_of_mem_upChain {n m x : ℕ} (hx : x ∈ upChain n m) : m ≤ x := by
  fun_induction upChain n m with
  | case1 m _ ih => -- 0 < m ∧ m ≤ n: m :: upChain n (m + lowbit m)
    rcases List.mem_cons.mp hx with rfl | htail
    · exact Nat.le_refl _
    · have := ih htail
      omega
  | case2 => simp only [List.not_mem_nil] at hx -- otherwise: []

theorem pairwise_lt_upChain (n m : ℕ) : (upChain n m).Pairwise (· < ·) := by
  fun_induction upChain n m with
  | case1 m hguard ih => -- 0 < m ∧ m ≤ n: m :: upChain n (m + lowbit m)
    have hlb_pos : 0 < lowbit m := lowbit_pos hguard.1
    refine List.Pairwise.cons (fun x hx => ?_) ih
    have hge := ge_of_mem_upChain hx
    omega
  | case2 => exact List.Pairwise.nil -- otherwise: []

theorem nodup_upChain (n m : ℕ) : (upChain n m).Nodup :=
  (pairwise_lt_upChain n m).imp (fun h => Nat.ne_of_lt h)

/-- Exact Fenwick ancestor characterization: starting from `m > 0`, `idx` is visited by
`upChain n m` iff `m ≤ idx ≤ n` and `idx`'s Fenwick interval `[idx - lowbit idx, idx)` contains
`m - 1` (i.e. `idx - lowbit idx < m`). -/
theorem mem_upChain_iff {n m idx : ℕ} (hm : 0 < m) :
    idx ∈ upChain n m ↔ m ≤ idx ∧ idx ≤ n ∧ idx - lowbit idx < m := by
  fun_induction upChain n m with
  | case1 m hguard ih => -- 0 < m ∧ m ≤ n: m :: upChain n (m + lowbit m)
    simp only [List.mem_cons]
    have hlb_pos : 0 < lowbit m := lowbit_pos hm
    rcases lt_trichotomy idx m with hlt | rfl | hgt
    · refine ⟨?_, by omega⟩
      rintro (rfl | htail)
      · omega
      · have := ge_of_mem_upChain htail; omega
    · simp only [true_or, Nat.le_refl, hguard.2, true_and, true_iff]
      omega
    · rw [or_iff_right (Nat.ne_of_gt hgt), ih (by omega), fenwick_parent_bridge hm hgt]
      omega
  | case2 m hguard => -- otherwise: []
    simp only [List.not_mem_nil, false_iff]
    rintro ⟨hle, hin, _⟩
    exact hguard ⟨hm, Nat.le_trans hle hin⟩

/-! ## Immediate-children partition of `[idx - lowbit idx, idx)` -/

/-- Immediate Fenwick children of `idx`: positive indices `c < idx` with `c + lowbit c = idx`. -/
@[expose] def fenwickChildren (idx : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (idx - 1)).filter (fun c => c + lowbit c = idx)

/-- Every path in `upChain idx m` from `m < idx` to `idx` has an immediate child `c` of `idx`
visited along `upChain idx m`. -/
private theorem exists_child_of_mem_upChain {idx m : ℕ}
    (hm : 0 < m) (hlt : m < idx) (hmem : idx ∈ upChain idx m) :
    ∃ c ∈ fenwickChildren idx, c ∈ upChain idx m := by
  fun_induction upChain idx m with
  | case1 m _ ih => -- 0 < m ∧ m ≤ idx: m :: upChain idx (m + lowbit m)
    rcases List.mem_cons.mp hmem with rfl | htail
    · omega
    · have hm'_le : m + lowbit m ≤ idx := ge_of_mem_upChain htail
      rcases Nat.eq_or_lt_of_le hm'_le with heq | hlt'
      · refine ⟨m, ?_, List.mem_cons_self⟩
        simp only [fenwickChildren, Finset.mem_filter, Finset.mem_Icc]
        omega
      · exact (ih (by omega) hlt' htail).imp fun _ ⟨hc, hm⟩ => ⟨hc, List.mem_cons_of_mem _ hm⟩
  | case2 => simp only [List.not_mem_nil] at hmem -- otherwise: []

/-- Intervals `[c - lowbit c, c)` of distinct immediate Fenwick children of `idx` are disjoint. -/
theorem pairwiseDisjoint_fenwickChildren (idx : ℕ) :
    (fenwickChildren idx : Set ℕ).PairwiseDisjoint (fun c => Finset.Ico (c - lowbit c) c) := by
  intro c₁ hc₁ c₂ hc₂ hne
  simp only [Finset.mem_coe, fenwickChildren, Finset.mem_filter, Finset.mem_Icc] at hc₁ hc₂
  change Disjoint (Finset.Ico (c₁ - lowbit c₁) c₁) (Finset.Ico (c₂ - lowbit c₂) c₂)
  rw [Finset.disjoint_left]
  intro i hi₁ hi₂
  simp only [Finset.mem_Ico] at hi₁ hi₂
  rcases lt_trichotomy c₁ c₂ with hlt | rfl | hgt
  · have := fenwick_parent_bridge hc₁.1.1 hlt; omega
  · exact hne rfl
  · have := fenwick_parent_bridge hc₂.1.1 hgt; omega

/-- `{idx - 1}` is disjoint from all immediate-child intervals `[c - lowbit c, c)`. -/
theorem notMem_biUnion_fenwickChildren (idx : ℕ) :
    idx - 1 ∉ (fenwickChildren idx).biUnion (fun c => Finset.Ico (c - lowbit c) c) := by
  simp only [Finset.mem_biUnion, fenwickChildren, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ico, not_exists, not_and]
  intro c hc _ _
  omega

/-- For `idx > 0`, `{idx - 1}` and the intervals `[c - lowbit c, c)` of `c ∈ fenwickChildren idx`
partition `[idx - lowbit idx, idx)`. -/
theorem insert_biUnion_fenwickChildren {idx : ℕ} (hidx : 0 < idx) :
    insert (idx - 1) ((fenwickChildren idx).biUnion (fun c => Finset.Ico (c - lowbit c) c)) =
      Finset.Ico (idx - lowbit idx) idx := by
  ext i
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Ico]
  have hlb_idx : 0 < lowbit idx := lowbit_pos hidx
  have hlb_le : lowbit idx ≤ idx := lowbit_le idx
  constructor
  · rintro (rfl | ⟨c, hc, hi⟩)
    · omega
    · simp only [fenwickChildren, Finset.mem_filter, Finset.mem_Icc] at hc
      have h2 := two_mul_lowbit_le_lowbit_add hc.1.1
      rw [hc.2] at h2
      have hcle := lowbit_le c
      omega
  · rintro ⟨hlo, hhi⟩
    rcases Nat.eq_or_lt_of_le (by omega : i ≤ idx - 1) with rfl | hilt
    · exact Or.inl rfl
    · have hmem : idx ∈ upChain idx (i + 1) :=
        (mem_upChain_iff i.succ_pos).mpr ⟨by omega, le_rfl, by omega⟩
      obtain ⟨c, hc_child, hc_mem⟩ := exists_child_of_mem_upChain i.succ_pos (by omega) hmem
      obtain ⟨hc_ge, _, hc_sub⟩ := (mem_upChain_iff i.succ_pos).mp hc_mem
      exact Or.inr ⟨c, hc_child, by omega, by omega⟩

end Cslib.DataStructure.FenwickTree
