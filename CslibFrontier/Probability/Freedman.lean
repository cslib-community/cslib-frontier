/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Azuma
public import CslibFrontier.Probability.BennettStep
public import Mathlib.Data.Fin.Tuple.Take
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ville's maximal inequality and Freedman's martingale concentration inequality

Along a discrete sequential process `Cslib.Probability.PMF.seqProcess step` with history-dependent
transition kernels `step t : (Fin t → α) → PMF α`, this module proves:

1. **Ville's maximal supermartingale inequality** (`seqProcess_ville_le`, [Ville1939]): for any
   nonnegative `ℝ≥0∞`-valued supermartingale `Z` along `seqProcess step` and threshold `c : ℝ≥0∞`,
   stopping `Z` at the first prefix `k ≤ n` where `c ≤ Z k (Fin.take k hk h)` preserves the
   supermartingale property and yields
   `(seqProcess step n).toOuterMeasure {h | ∃ (k : ℕ) (hk : k ≤ n), c ≤ Z k (Fin.take k hk h)} * c ≤
     Z 0 Fin.elim0` on arbitrary outcome types `α` without `[Fintype α]` or `[MeasurableSpace α]`.
2. **Freedman's maximal martingale tail inequality** ([Freedman1975, Theorem (1.6)]): for any
   real-valued supermartingale `X` along `seqProcess step` whose one-step increments on supported
   transitions satisfy the *one-sided* bound `X (k + 1) (Fin.snoc h x) - X k h ≤ b` and predictable
   conditional second-moment bound `∑' x, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h)²
   ≤ V k h` (for a martingale, the exact conditional variance `Var(X_{k+1} - X_k | h)`), the
   compensated exponential process is a nonnegative supermartingale with expectation at most `1`
   (`tsum_seqProcess_freedman_exp_le_one`). Combining with Ville's maximal inequality and optimizing
   the Laplace parameter gives:
   * `seqProcess_exists_prefix_ge_and_var_le_bennett`: the sharp Poisson/Bennett bound
     `exp (-(v / b²) * klFun (1 + b ε / v))` (`b > 0, v > 0, ε ≥ 0`) on the maximal event
     `{h | ∃ (k : ℕ) (hk : k ≤ n), X 0 Fin.elim0 + ε ≤ X k (Fin.take k hk h) ∧
       seqPredVar V k (Fin.take k hk h) ≤ v}`;
   * `seqProcess_exists_prefix_ge_and_var_le`: the rational Bernstein–Freedman bound
     `exp (-ε² / (2 * (v + b ε / 3)))` for *all* `b ≥ 0, v ≥ 0, ε ≥ 0` (including the degenerate
     boundaries `b = 0`, `v = 0`, and `ε = 0`).
3. **Bounded-increment sequential Bernstein corollaries** (`seqProcess_bernstein_maximal_ge_le`,
   `seqProcess_bernstein_ge_le`, `seqProcess_bernstein_le_le`,
   `seqProcess_bernstein_abs_sub_ge_le`): when `|X (k + 1) (Fin.snoc h x) - X k h| ≤ b` on
   supported steps, conditional moment summability holds automatically, yielding maximal and
   fixed-time upper, lower, and two-sided sequential Bernstein bounds.

## Main definitions

* `Cslib.Probability.PMF.seqPredVar`: cumulative predictable quadratic variation
  `∑ j : Fin k, V j.1 (Fin.take j.1 j.isLt.le h)` along a prefix `h : Fin k → α`.

## Main results

* `Cslib.Probability.PMF.seqProcess_ville_le`: Ville's maximal inequality along `seqProcess`.
* `Cslib.Probability.PMF.tsum_seqProcess_freedman_exp_le_one`: Freedman's compensated exponential
  supermartingale bound.
* `Cslib.Probability.PMF.seqProcess_exists_prefix_ge_and_var_le_bennett`,
  `Cslib.Probability.PMF.seqProcess_exists_prefix_ge_and_var_le`: Freedman's maximal tail bounds in
  sharp Poisson (`klFun`) and unconditional Bernstein forms.
* `Cslib.Probability.PMF.seqProcess_bernstein_maximal_ge_le`,
  `Cslib.Probability.PMF.seqProcess_bernstein_ge_le`,
  `Cslib.Probability.PMF.seqProcess_bernstein_le_le`,
  `Cslib.Probability.PMF.seqProcess_bernstein_abs_sub_ge_le`: bounded-increment maximal and
  fixed-time upper, lower, and two-sided sequential Bernstein bounds.

## References

* [J. Ville, *Étude critique de la notion de collectif*][Ville1939]
* [D. A. Freedman, *On tail probabilities for martingales*][Freedman1975]
* [G. Bennett, *Probability inequalities for the sum of independent random variables*][Bennett1962]
-/

public section

namespace Cslib.Probability.PMF

open InformationTheory
open scoped BigOperators ENNReal

variable {α : Type*}

/-! ### Prefix projections and predictable quadratic variation -/

private theorem take_snoc_of_le {k j : ℕ} (hj : j ≤ k) (h : Fin k → α) (a : α) :
    Fin.take j (Nat.le_succ_of_le hj) (Fin.snoc (α := fun _ => α) h a) = Fin.take j hj h := by
  ext i
  simp only [Fin.take_apply]
  have hcast : Fin.castLE (Nat.le_succ_of_le hj) i = (Fin.castLE hj i).castSucc := by
    ext; rfl
  rw [hcast, Fin.snoc_castSucc]

private theorem take_init_eq {k j : ℕ} (hj : j ≤ k) (h : Fin (k + 1) → α) :
    Fin.take j hj (Fin.init h) = Fin.take j (Nat.le_succ_of_le hj) h := by
  ext
  rfl

private theorem take_self_eq {k : ℕ} (hk : k ≤ k) (h : Fin k → α) :
    Fin.take k hk h = h := by
  ext
  rfl

private theorem mem_support_seqProcess_succ (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    {k : ℕ} {h : Fin (k + 1) → α} (hh : h ∈ (seqProcess step (k + 1)).support) :
    Fin.init h ∈ (seqProcess step k).support ∧
      h (Fin.last k) ∈ (step k (Fin.init h)).support := by
  simp only [seqProcess, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hh
  obtain ⟨p, hp, x, hx, heq⟩ := hh
  have hp_eq : p = Fin.init h := by simpa using congrArg Fin.init heq
  have hx_eq : x = h (Fin.last k) := by simpa using congrFun heq (Fin.last k)
  exact ⟨hp_eq ▸ hp, hx_eq ▸ hp_eq ▸ hx⟩

private theorem mem_support_seqProcess_take (step : ∀ t : ℕ, (Fin t → α) → PMF α) :
    ∀ {n k : ℕ} (hk : k ≤ n) {h : Fin n → α},
      h ∈ (seqProcess step n).support → Fin.take k hk h ∈ (seqProcess step k).support
  | 0, k, hk, h, hh => by
    obtain rfl : k = 0 := Nat.eq_zero_of_le_zero hk
    rwa [take_self_eq]
  | m + 1, k, hk, h, hh => by
    rcases Nat.of_le_succ hk with hkm | rfl
    · have hh₀ := (mem_support_seqProcess_succ step hh).1
      rw [← Fin.snoc_init_self h, take_snoc_of_le hkm]
      exact mem_support_seqProcess_take step hkm hh₀
    · rwa [take_self_eq]

/-- Cumulative predictable quadratic variation `∑ j < k, V j (h_{≤ j})` along a trajectory prefix
`h : Fin k → α`. -/
abbrev seqPredVar (V : ∀ j : ℕ, (Fin j → α) → ℝ) (k : ℕ) (h : Fin k → α) : ℝ :=
  ∑ j : Fin k, V j.1 (Fin.take j.1 j.isLt.le h)

@[simp]
theorem seqPredVar_zero (V : ∀ j : ℕ, (Fin j → α) → ℝ) (h : Fin 0 → α) :
    seqPredVar V 0 h = 0 := by
  simp [seqPredVar]

@[simp]
theorem seqPredVar_snoc (V : ∀ j : ℕ, (Fin j → α) → ℝ) (k : ℕ) (h : Fin k → α) (a : α) :
    seqPredVar V (k + 1) (Fin.snoc (α := fun _ => α) h a) = seqPredVar V k h + V k h := by
  simp only [seqPredVar, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [take_snoc_of_le j.isLt.le h a]
  · rw [take_snoc_of_le le_rfl h a, take_self_eq]

/-! ### Ville's maximal supermartingale inequality -/

private noncomputable def stoppedProcess (Z : ∀ k : ℕ, (Fin k → α) → ℝ≥0∞) (c : ℝ≥0∞) :
    ∀ k : ℕ, (Fin k → α) → ℝ≥0∞
  | 0, h => Z 0 h
  | k + 1, h =>
    open Classical in
    if ∃ (j : ℕ) (hj : j ≤ k), c ≤ Z j (Fin.take j hj (Fin.init h)) then
      stoppedProcess Z c k (Fin.init h)
    else
      Z (k + 1) h

private theorem stoppedProcess_eq_of_not_exists (Z : ∀ k : ℕ, (Fin k → α) → ℝ≥0∞) (c : ℝ≥0∞) :
    ∀ {k : ℕ} (h : Fin k → α),
      (¬ ∃ (j : ℕ) (hj : j ≤ k), c ≤ Z j (Fin.take j hj h)) → stoppedProcess Z c k h = Z k h
  | 0, _, _ => rfl
  | k + 1, h, hno => by
    have hno_init : ¬ ∃ (j : ℕ) (hj : j ≤ k), c ≤ Z j (Fin.take j hj (Fin.init h)) := by
      rintro ⟨j, hj, hcj⟩
      rw [take_init_eq hj h] at hcj
      exact hno ⟨j, Nat.le_succ_of_le hj, hcj⟩
    classical
    simp only [stoppedProcess, hno_init, ↓reduceIte]

private theorem le_stoppedProcess_of_exists (Z : ∀ k : ℕ, (Fin k → α) → ℝ≥0∞) (c : ℝ≥0∞) :
    ∀ {k : ℕ} (h : Fin k → α),
      (∃ (j : ℕ) (hj : j ≤ k), c ≤ Z j (Fin.take j hj h)) → c ≤ stoppedProcess Z c k h
  | 0, h, ⟨j, hj, hcj⟩ => by
    obtain rfl := Nat.eq_zero_of_le_zero hj
    rwa [take_self_eq] at hcj
  | k + 1, h, hex => by
    classical
    simp only [stoppedProcess]
    split_ifs with hinit
    · exact le_stoppedProcess_of_exists Z c (Fin.init h) hinit
    · obtain ⟨j, hj, hcj⟩ := hex
      rcases Nat.of_le_succ hj with hjk | rfl
      · exact absurd ⟨j, hjk, by rwa [take_init_eq hjk h]⟩ hinit
      · rwa [take_self_eq] at hcj

/-- **Ville's maximal supermartingale inequality** along `seqProcess` [Ville1939]: if
`Z : ∀ k, (Fin k → α) → ℝ≥0∞` satisfies `∑' x, step k h x * Z (k + 1) (Fin.snoc h x) ≤ Z k h` on
every supported prefix `h` (`k < n`), then for any threshold `c : ℝ≥0∞`,
`(seqProcess step n).toOuterMeasure {h | ∃ (k : ℕ) (hk : k ≤ n), c ≤ Z k (Fin.take k hk h)} * c ≤
  Z 0 Fin.elim0`. -/
theorem seqProcess_ville_le (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (Z : ∀ k : ℕ, (Fin k → α) → ℝ≥0∞) (n : ℕ)
    (hsuper : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, step k h x * Z (k + 1) (Fin.snoc h x) ≤ Z k h)
    (c : ℝ≥0∞) :
    (seqProcess step n).toOuterMeasure
        {h : Fin n → α | ∃ (k : ℕ) (hk : k ≤ n), c ≤ Z k (Fin.take k hk h)} * c ≤
      Z 0 Fin.elim0 := by
  have htsum_le : ∀ m, m ≤ n →
      ∑' h : Fin m → α, seqProcess step m h * stoppedProcess Z c m h ≤ Z 0 Fin.elim0 := by
    intro m hmn
    induction m with
    | zero =>
      rw [seqProcess, tsum_eq_single Fin.elim0 fun h hh =>
        absurd (Subsingleton.elim h Fin.elim0) hh]
      simp [stoppedProcess]
    | succ m ih =>
      have hm_lt : m < n := Nat.lt_of_succ_le hmn
      rw [seqProcess, tsum_bind_mul]
      refine (tsum_le_tsum fun h => ?_).trans (ih hm_lt.le)
      classical
      by_cases hh : h ∈ (seqProcess step m).support
      · rw [tsum_map_mul]
        refine mul_le_mul_right ?_ _
        by_cases hex : ∃ (j : ℕ) (hj : j ≤ m), c ≤ Z j (Fin.take j hj h)
        · simp_rw [show ∀ x, stoppedProcess Z c (m + 1) (Fin.snoc (α := fun _ => α) h x) =
              stoppedProcess Z c m h from fun x => by
                simp only [stoppedProcess, Fin.init_snoc, hex, ↓reduceIte]]
          rw [ENNReal.tsum_mul_right, (step m h).tsum_coe, one_mul]
        · simp_rw [show ∀ x, stoppedProcess Z c (m + 1) (Fin.snoc (α := fun _ => α) h x) =
              Z (m + 1) (Fin.snoc (α := fun _ => α) h x) from fun x => by
                simp only [stoppedProcess, Fin.init_snoc, hex, ↓reduceIte]]
          rw [stoppedProcess_eq_of_not_exists Z c h hex]
          exact hsuper m hm_lt h hh
      · rw [((seqProcess step m).apply_eq_zero_iff h).mpr hh, zero_mul, zero_mul]
  set E : Set (Fin n → α) := {h | ∃ (k : ℕ) (hk : k ≤ n), c ≤ Z k (Fin.take k hk h)}
  rw [toOuterMeasure_eq_tsum_mul_indicator, ← ENNReal.tsum_mul_right]
  refine (tsum_le_tsum fun h => ?_).trans (htsum_le n le_rfl)
  rw [mul_assoc]
  refine mul_le_mul_right ?_ _
  classical
  by_cases hh : h ∈ E
  · simpa only [Set.indicator_of_mem hh, Pi.one_apply, one_mul] using
      le_stoppedProcess_of_exists Z c h hh
  · simp only [Set.indicator_of_notMem hh, zero_mul, zero_le]

/-! ### Freedman's compensated exponential supermartingale and maximal inequality -/

private theorem freedman_step_le (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (X V : ∀ k : ℕ, (Fin k → α) → ℝ) {b : ℝ} (hb : 0 < b) (n : ℕ)
    (hd1 : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      Summable fun x : α => (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h))
    (hd2 : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      Summable fun x : α => (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2)
    (hmean : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ≤ 0)
    (hupper : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∀ x ∈ (step k h).support, X (k + 1) (Fin.snoc h x) - X k h ≤ b)
    (hvar : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2 ≤ V k h)
    {s : ℝ} (hs : 0 ≤ s) :
    let ψ := (Real.exp (s * b) - 1 - s * b) / b ^ 2
    ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, step k h x *
        ENNReal.ofReal (Real.exp (s * (X (k + 1) (Fin.snoc h x) - X 0 Fin.elim0) -
          ψ * seqPredVar V (k + 1) (Fin.snoc h x))) ≤
        ENNReal.ofReal (Real.exp (s * (X k h - X 0 Fin.elim0) - ψ * seqPredVar V k h)) := by
  intro ψ k hk h hh
  have hfactor (x : α) :
      step k h x * ENNReal.ofReal (Real.exp (s * (X (k + 1) (Fin.snoc h x) - X 0 Fin.elim0) -
          ψ * seqPredVar V (k + 1) (Fin.snoc h x))) =
        (ENNReal.ofReal (Real.exp (s * (X k h - X 0 Fin.elim0) - ψ * seqPredVar V k h)) *
          ENNReal.ofReal (Real.exp (-(ψ * V k h)))) *
          (step k h x * ENNReal.ofReal (Real.exp (s * (X (k + 1) (Fin.snoc h x) - X k h)))) := by
    rw [seqPredVar_snoc]
    have hexp : s * (X (k + 1) (Fin.snoc h x) - X 0 Fin.elim0) - ψ * (seqPredVar V k h + V k h) =
        ((s * (X k h - X 0 Fin.elim0) - ψ * seqPredVar V k h) + -(ψ * V k h)) +
          s * (X (k + 1) (Fin.snoc h x) - X k h) := by ring
    rw [hexp, Real.exp_add, Real.exp_add,
      ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  simp_rw [hfactor]
  rw [ENNReal.tsum_mul_left]
  have hben := tsum_mul_exp_le_bennett (step k h) (fun x => X (k + 1) (Fin.snoc h x) - X k h)
    (hd1 k hk h hh) (hd2 k hk h hh) (hmean k hk h hh) hb (hupper k hk h hh) (hvar k hk h hh) hs
  refine (mul_le_mul_right hben _).trans_eq ?_
  rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  have hcancel : -(ψ * V k h) + (V k h / b ^ 2) * (Real.exp (s * b) - 1 - s * b) = 0 := by
    dsimp only [ψ]
    ring
  rw [hcancel, Real.exp_zero, ENNReal.ofReal_one, mul_one]

/-- **Freedman's compensated exponential supermartingale bound** [Freedman1975, §1]: under
one-sided bounded conditional increments `X (k + 1) (Fin.snoc h x) - X k h ≤ b` (`b > 0`),
nonpositive conditional drift, and predictable conditional second-moment bound `V k h`, the
expected value of
`exp (s * (X n h - X 0 Fin.elim0) - ((exp (s b) - 1 - s b) / b²) * seqPredVar V n h)` is at most
`1` for every `s ≥ 0`. -/
theorem tsum_seqProcess_freedman_exp_le_one (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (X V : ∀ k : ℕ, (Fin k → α) → ℝ) {b : ℝ} (hb : 0 < b) (n : ℕ)
    (hd1 : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      Summable fun x : α => (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h))
    (hd2 : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      Summable fun x : α => (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2)
    (hmean : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ≤ 0)
    (hupper : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∀ x ∈ (step k h).support, X (k + 1) (Fin.snoc h x) - X k h ≤ b)
    (hvar : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2 ≤ V k h)
    {s : ℝ} (hs : 0 ≤ s) :
    ∑' h : Fin n → α, seqProcess step n h *
      ENNReal.ofReal (Real.exp (s * (X n h - X 0 Fin.elim0) -
        ((Real.exp (s * b) - 1 - s * b) / b ^ 2) * seqPredVar V n h)) ≤ 1 := by
  set ψ := (Real.exp (s * b) - 1 - s * b) / b ^ 2
  have hstep := freedman_step_le step X V hb n hd1 hd2 hmean hupper hvar hs
  induction n with
  | zero =>
    rw [seqProcess, tsum_eq_single Fin.elim0 fun h hh =>
      absurd (Subsingleton.elim h Fin.elim0) hh]
    simp
  | succ m ih =>
    have ih' := ih (fun k hk => hd1 k (Nat.lt_succ_of_lt hk))
      (fun k hk => hd2 k (Nat.lt_succ_of_lt hk))
      (fun k hk => hmean k (Nat.lt_succ_of_lt hk))
      (fun k hk => hupper k (Nat.lt_succ_of_lt hk))
      (fun k hk => hvar k (Nat.lt_succ_of_lt hk))
      (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    rw [seqProcess, tsum_bind_mul]
    refine (tsum_le_tsum fun h => ?_).trans ih'
    classical
    by_cases hh : h ∈ (seqProcess step m).support
    · rw [tsum_map_mul]
      exact mul_le_mul_right (hstep m (Nat.lt_succ_self m) h hh) _
    · rw [((seqProcess step m).apply_eq_zero_iff h).mpr hh, zero_mul, zero_mul]

/-- **Freedman's maximal martingale inequality, sharp Poisson/Bennett form**
[Freedman1975, Theorem (1.6)]: for any discrete supermartingale `X` along `seqProcess step` with
one-sided increment bound `X (k + 1) (Fin.snoc h x) - X k h ≤ b` (`b > 0`) and predictable
conditional second-moment bound `V k h`, for every `v > 0` and `ε ≥ 0`, the probability that some
prefix `k ≤ n` simultaneously reaches `X 0 Fin.elim0 + ε ≤ X k (Fin.take k hk h)` while
`seqPredVar V k (Fin.take k hk h) ≤ v` is at most `exp (-(v / b²) * klFun (1 + b ε / v))`. -/
theorem seqProcess_exists_prefix_ge_and_var_le_bennett (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (X V : ∀ k : ℕ, (Fin k → α) → ℝ) {b v ε : ℝ} (hb : 0 < b) (hv : 0 < v) (hε : 0 ≤ ε) (n : ℕ)
    (hd1 : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      Summable fun x : α => (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h))
    (hd2 : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      Summable fun x : α => (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2)
    (hmean : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ≤ 0)
    (hupper : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∀ x ∈ (step k h).support, X (k + 1) (Fin.snoc h x) - X k h ≤ b)
    (hvar : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2 ≤ V k h) :
    ((seqProcess step n).toOuterMeasure
        {h : Fin n → α | ∃ (k : ℕ) (hk : k ≤ n),
          X 0 Fin.elim0 + ε ≤ X k (Fin.take k hk h) ∧
            seqPredVar V k (Fin.take k hk h) ≤ v}).toReal ≤
      Real.exp (-(v / b ^ 2) * klFun (1 + b * ε / v)) := by
  obtain ⟨hs, hexp_eq⟩ := Cslib.Probability.bennett_laplace_exponent_eq hb hv hε
  set s := (1 / b) * Real.log (1 + b * ε / v)
  set ψ := (Real.exp (s * b) - 1 - s * b) / b ^ 2
  have hψ_nn : 0 ≤ ψ := div_nonneg (by linarith [Real.add_one_le_exp (s * b)]) (by positivity)
  let Z : ∀ k : ℕ, (Fin k → α) → ℝ≥0∞ := fun k h =>
    ENNReal.ofReal (Real.exp (s * (X k h - X 0 Fin.elim0) - ψ * seqPredVar V k h))
  set c := ENNReal.ofReal (Real.exp (s * ε - ψ * v))
  have hville := (seqProcess_ville_le step Z n
    (freedman_step_le step X V hb n hd1 hd2 hmean hupper hvar hs) c).trans_eq
    (by simp [Z] : Z 0 Fin.elim0 = 1)
  set E := {h : Fin n → α | ∃ (k : ℕ) (hk : k ≤ n),
    X 0 Fin.elim0 + ε ≤ X k (Fin.take k hk h) ∧ seqPredVar V k (Fin.take k hk h) ≤ v}
  have hsub : E ⊆ {h : Fin n → α | ∃ (k : ℕ) (hk : k ≤ n), c ≤ Z k (Fin.take k hk h)} := by
    rintro h ⟨k, hk, hX_ge, hV_le⟩
    refine ⟨k, hk, ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)⟩
    have hX' : ε ≤ X k (Fin.take k hk h) - X 0 Fin.elim0 := by linarith
    linarith [mul_le_mul_of_nonneg_left hX' hs, mul_le_mul_of_nonneg_left hV_le hψ_nn]
  have hm := ENNReal.toReal_mono ENNReal.one_ne_top
    ((mul_le_mul_left (MeasureTheory.measure_mono hsub) c).trans hville)
  rw [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hm
  refine ((le_div_iff₀ (Real.exp_pos _)).mpr hm).trans_eq ?_
  rw [one_div, ← Real.exp_neg, ← hexp_eq]
  exact congrArg Real.exp (by dsimp only [ψ]; ring)

private theorem le_zero_on_support_of_step_nonpos (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (X : ∀ k : ℕ, (Fin k → α) → ℝ) :
    ∀ {k : ℕ} {h : Fin k → α}, h ∈ (seqProcess step k).support →
      (∀ j, j < k → ∀ p ∈ (seqProcess step j).support,
        ∀ x ∈ (step j p).support, X (j + 1) (Fin.snoc p x) - X j p ≤ 0) →
      X k h ≤ X 0 Fin.elim0
  | 0, h, _, _ => by rw [Subsingleton.elim h Fin.elim0]
  | k + 1, h, hh, hle => by
    obtain ⟨hp, hx⟩ := mem_support_seqProcess_succ step hh
    have hstep := hle k (Nat.lt_succ_self k) (Fin.init h) hp (h (Fin.last k)) hx
    rw [Fin.snoc_init_self] at hstep
    have hprev := le_zero_on_support_of_step_nonpos step X hp fun j hj =>
      hle j (Nat.lt_succ_of_lt hj)
    linarith

/-- **Freedman's maximal martingale inequality, unconditional Bernstein form**
[Freedman1975, Theorem (1.6)]: under the hypotheses of
`seqProcess_exists_prefix_ge_and_var_le_bennett`, for *every* `b ≥ 0`, `v ≥ 0`, and `ε ≥ 0`
(including `b = 0`, `v = 0`, and `ε = 0`), the maximal probability that some prefix `k ≤ n` reaches
`X 0 Fin.elim0 + ε ≤ X k (Fin.take k hk h)` with `seqPredVar V k (Fin.take k hk h) ≤ v` is at most
`exp (-ε² / (2 * (v + b ε / 3)))`. -/
theorem seqProcess_exists_prefix_ge_and_var_le (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (X V : ∀ k : ℕ, (Fin k → α) → ℝ) {b v ε : ℝ} (hb : 0 ≤ b) (hv : 0 ≤ v) (hε : 0 ≤ ε) (n : ℕ)
    (hd1 : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      Summable fun x : α => (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h))
    (hd2 : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      Summable fun x : α => (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2)
    (hmean : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ≤ 0)
    (hupper : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∀ x ∈ (step k h).support, X (k + 1) (Fin.snoc h x) - X k h ≤ b)
    (hvar : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2 ≤ V k h) :
    ((seqProcess step n).toOuterMeasure
        {h : Fin n → α | ∃ (k : ℕ) (hk : k ≤ n),
          X 0 Fin.elim0 + ε ≤ X k (Fin.take k hk h) ∧
            seqPredVar V k (Fin.take k hk h) ≤ v}).toReal ≤
      Real.exp (-ε ^ 2 / (2 * (v + b * ε / 3))) := by
  set E := {h : Fin n → α | ∃ (k : ℕ) (hk : k ≤ n),
    X 0 Fin.elim0 + ε ≤ X k (Fin.take k hk h) ∧ seqPredVar V k (Fin.take k hk h) ≤ v}
  have hzero_of_disj (hempty : ∀ h ∈ (seqProcess step n).support, h ∉ E) :
      ((seqProcess step n).toOuterMeasure E).toReal ≤
        Real.exp (-ε ^ 2 / (2 * (v + b * ε / 3))) := by
    rw [(PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr (Set.disjoint_left.mpr hempty),
      ENNReal.toReal_zero]
    exact (Real.exp_pos _).le
  rcases eq_or_lt_of_le hε with rfl | hε_pos
  · simpa only [zero_pow two_ne_zero, neg_zero, zero_div, Real.exp_zero, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (toOuterMeasure_le_one _ E)
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · refine hzero_of_disj fun h hh ⟨k, hk, hge, _⟩ => ?_
      have hle := le_zero_on_support_of_step_nonpos step X
        (mem_support_seqProcess_take step hk hh) fun j hj => hupper j (hj.trans_le hk)
      linarith
    · rcases eq_or_lt_of_le hv with rfl | hv_pos
      · refine hzero_of_disj fun h hh ⟨k, hk, hge, hV_le⟩ => ?_
        set hk_pref := Fin.take k hk h
        have hsupp_k := mem_support_seqProcess_take step hk hh
        have hV_nn (j : Fin k) : 0 ≤ V j.1 (Fin.take j.1 j.isLt.le hk_pref) :=
          (tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)).trans
            (hvar j.1 (j.isLt.trans_le hk) _ (mem_support_seqProcess_take step j.isLt.le hsupp_k))
        have hV_zero (j : Fin k) : V j.1 (Fin.take j.1 j.isLt.le hk_pref) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hV_nn i).mp
            (le_antisymm hV_le (Finset.sum_nonneg fun i _ => hV_nn i)) j (Finset.mem_univ j)
        have hzero_step : ∀ (m : ℕ) (hmk : m ≤ k),
            X m (Fin.take m hmk hk_pref) ≤ X 0 Fin.elim0 := by
          intro m hmk
          induction m with
          | zero => rw [Subsingleton.elim (Fin.take 0 hmk hk_pref) Fin.elim0]
          | succ m ihm =>
            have hm_lt : m < k := Nat.lt_of_succ_le hmk
            set pm := Fin.take m hm_lt.le hk_pref
            set pm1 := Fin.take (m + 1) hmk hk_pref
            have hinit : Fin.init pm1 = pm := by ext; rfl
            obtain ⟨hp_init, hx_init⟩ :=
              mem_support_seqProcess_succ step (mem_support_seqProcess_take step hmk hsupp_k)
            have hp' : pm ∈ (seqProcess step m).support := hinit ▸ hp_init
            have hx : pm1 (Fin.last m) ∈ (step m pm).support := hinit ▸ hx_init
            have hsingle := ((hd2 m (hm_lt.trans_le hk) pm hp').sum_le_tsum {pm1 (Fin.last m)}
              fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)).trans
              (hV_zero ⟨m, hm_lt⟩ ▸ hvar m (hm_lt.trans_le hk) pm hp')
            rw [Finset.sum_singleton] at hsingle
            have hprob_pos :=
              ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hx) (PMF.apply_ne_top _ _)
            have hdiff0 := sq_eq_zero_iff.mp
              (le_antisymm (nonpos_of_mul_nonpos_right hsingle hprob_pos) (sq_nonneg _))
            rw [← hinit, Fin.snoc_init_self, hinit] at hdiff0
            linarith [ihm hm_lt.le]
        have hkend := hzero_step k le_rfl
        rw [take_self_eq] at hkend
        linarith
      · exact (seqProcess_exists_prefix_ge_and_var_le_bennett step X V hb_pos hv_pos hε n
          hd1 hd2 hmean hupper hvar).trans
          (Cslib.Probability.exp_neg_klFun_le_exp_bernstein hb_pos hv_pos hε)

/-! ### Ergonomic bounded-increment sequential Bernstein inequalities -/

/-- **Maximal sequential Bernstein inequality** for processes with two-sided bounded increments
`|X (k + 1) (Fin.snoc h x) - X k h| ≤ b` (`b ≥ 0, v ≥ 0, ε ≥ 0`), requiring no explicit
`Summable` hypotheses. -/
theorem seqProcess_bernstein_maximal_ge_le (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (X V : ∀ k : ℕ, (Fin k → α) → ℝ) {b v ε : ℝ} (hb : 0 ≤ b) (hv : 0 ≤ v) (hε : 0 ≤ ε) (n : ℕ)
    (hmean : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ≤ 0)
    (hbdd : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∀ x ∈ (step k h).support, |X (k + 1) (Fin.snoc h x) - X k h| ≤ b)
    (hvar : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2 ≤ V k h) :
    ((seqProcess step n).toOuterMeasure
        {h : Fin n → α | ∃ (k : ℕ) (hk : k ≤ n),
          X 0 Fin.elim0 + ε ≤ X k (Fin.take k hk h) ∧
            seqPredVar V k (Fin.take k hk h) ≤ v}).toReal ≤
      Real.exp (-ε ^ 2 / (2 * (v + b * ε / 3))) := by
  refine seqProcess_exists_prefix_ge_and_var_le step X V hb hv hε n
    (fun k hk h hh => summable_toReal_mul_of_abs_le (step k h) _ (hbdd k hk h hh))
    (fun k hk h hh => summable_toReal_mul_of_abs_le (step k h) _ (C := b ^ 2) fun x hx => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbdd k hk h hh x hx) 2)
    hmean
    (fun k hk h hh x hx => (le_abs_self _).trans (hbdd k hk h hh x hx))
    hvar

/-- **Sequential Bernstein inequality, upper tail**: if `X` is a supermartingale along `seqProcess`
with `|X (k + 1) (Fin.snoc h x) - X k h| ≤ b` (`b ≥ 0`) and conditional second moment bounded by a
deterministic sequence `vStep k ≥ 0`, then `X 0 Fin.elim0 + ε ≤ X n h` (`ε ≥ 0`) holds with
probability at most `exp (-ε² / (2 * ((∑ k ∈ range n, vStep k) + b ε / 3)))`. -/
theorem seqProcess_bernstein_ge_le (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (X : ∀ k : ℕ, (Fin k → α) → ℝ) (vStep : ℕ → ℝ) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 ≤ ε) (n : ℕ)
    (hvStep : ∀ k, k < n → 0 ≤ vStep k)
    (hmean : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ≤ 0)
    (hbdd : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∀ x ∈ (step k h).support, |X (k + 1) (Fin.snoc h x) - X k h| ≤ b)
    (hvar : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2 ≤ vStep k) :
    ((seqProcess step n).toOuterMeasure {h : Fin n → α | X 0 Fin.elim0 + ε ≤ X n h}).toReal ≤
      Real.exp (-ε ^ 2 / (2 * ((∑ k ∈ Finset.range n, vStep k) + b * ε / 3))) := by
  set v := ∑ k ∈ Finset.range n, vStep k
  have hv : 0 ≤ v := Finset.sum_nonneg fun k hk => hvStep k (Finset.mem_range.mp hk)
  have hmax := seqProcess_bernstein_maximal_ge_le step X (fun k _ => vStep k) hb hv hε n
    hmean hbdd hvar
  have hsub : {h : Fin n → α | X 0 Fin.elim0 + ε ≤ X n h} ⊆
      {h : Fin n → α | ∃ (k : ℕ) (hk : k ≤ n),
        X 0 Fin.elim0 + ε ≤ X k (Fin.take k hk h) ∧
          seqPredVar (fun j _ => vStep j) k (Fin.take k hk h) ≤ v} := by
    intro h hh
    refine ⟨n, le_rfl, ?_, ?_⟩
    · rwa [take_self_eq]
    · simp only [seqPredVar, Fin.sum_univ_eq_sum_range]
      exact le_rfl
  exact (ENNReal.toReal_mono (toOuterMeasure_ne_top _ _)
    (MeasureTheory.measure_mono hsub)).trans hmax

/-- **Sequential Bernstein inequality, lower tail** for submartingales with bounded increments. -/
theorem seqProcess_bernstein_le_le (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (X : ∀ k : ℕ, (Fin k → α) → ℝ) (vStep : ℕ → ℝ) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 ≤ ε) (n : ℕ)
    (hvStep : ∀ k, k < n → 0 ≤ vStep k)
    (hmean : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      0 ≤ ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h))
    (hbdd : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∀ x ∈ (step k h).support, |X (k + 1) (Fin.snoc h x) - X k h| ≤ b)
    (hvar : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2 ≤ vStep k) :
    ((seqProcess step n).toOuterMeasure {h : Fin n → α | X n h ≤ X 0 Fin.elim0 - ε}).toReal ≤
      Real.exp (-ε ^ 2 / (2 * ((∑ k ∈ Finset.range n, vStep k) + b * ε / 3))) := by
  have heq : {h : Fin n → α | X n h ≤ X 0 Fin.elim0 - ε} =
      {h : Fin n → α | -X 0 Fin.elim0 + ε ≤ -X n h} := by
    ext h
    change X n h ≤ X 0 Fin.elim0 - ε ↔ -X 0 Fin.elim0 + ε ≤ -X n h
    constructor <;> intro <;> linarith
  rw [heq]
  refine seqProcess_bernstein_ge_le step (fun k h => -X k h) vStep hb hε n hvStep
    (fun k hk h hh => ?_) (fun k hk h hh x hx => ?_) (fun k hk h hh => ?_)
  · rw [show (fun x : α => (step k h x).toReal * (-X (k + 1) (Fin.snoc h x) - -X k h)) =
      fun x => -((step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h)) from
        funext fun _ => by ring, tsum_neg]
    exact neg_nonpos.mpr (hmean k hk h hh)
  · simpa only [show -X (k + 1) (Fin.snoc h x) - -X k h = -(X (k + 1) (Fin.snoc h x) - X k h)
      by ring, abs_neg] using hbdd k hk h hh x hx
  · simpa only [show ∀ x : α, (-X (k + 1) (Fin.snoc h x) - -X k h) ^ 2 =
      (X (k + 1) (Fin.snoc h x) - X k h) ^ 2 from fun _ => by ring] using hvar k hk h hh

/-- **Sequential Bernstein inequality, two-sided tail** for martingales with bounded increments. -/
theorem seqProcess_bernstein_abs_sub_ge_le (step : ∀ t : ℕ, (Fin t → α) → PMF α)
    (X : ∀ k : ℕ, (Fin k → α) → ℝ) (vStep : ℕ → ℝ) {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 ≤ ε) (n : ℕ)
    (hvStep : ∀ k, k < n → 0 ≤ vStep k)
    (hmean : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) = 0)
    (hbdd : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∀ x ∈ (step k h).support, |X (k + 1) (Fin.snoc h x) - X k h| ≤ b)
    (hvar : ∀ k, k < n → ∀ h ∈ (seqProcess step k).support,
      ∑' x : α, (step k h x).toReal * (X (k + 1) (Fin.snoc h x) - X k h) ^ 2 ≤ vStep k) :
    ((seqProcess step n).toOuterMeasure {h : Fin n → α | ε ≤ |X n h - X 0 Fin.elim0|}).toReal ≤
      2 * Real.exp (-ε ^ 2 / (2 * ((∑ k ∈ Finset.range n, vStep k) + b * ε / 3))) := by
  linarith [toOuterMeasure_abs_sub_ge_toReal_le (seqProcess step n) (X n) (X 0 Fin.elim0) ε,
    seqProcess_bernstein_ge_le step X vStep hb hε n hvStep
      (fun k hk h hh => (hmean k hk h hh).le) hbdd hvar,
    seqProcess_bernstein_le_le step X vStep hb hε n hvStep
      (fun k hk h hh => (hmean k hk h hh).ge) hbdd hvar]

end Cslib.Probability.PMF
