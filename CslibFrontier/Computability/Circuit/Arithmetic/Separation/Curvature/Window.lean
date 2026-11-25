/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.WindowMean
public import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Windows: clamping, the relative place in a window, and two elementary inequalities

Helpers for the theorem that prices are nonpositively curved in *VP ≠ VNP over every field*
[AnthropicVPVNP2026] (module `Nc.Cat.Window`); nothing
here is about prices.

## Main definitions

* `Separation.clamp N i`: the integer `i` clamped to `0, …, N`.
* `Separation.windowPlace`: the relative place `i / n²` of a point in the `n`-th window.

## Main results

* `Separation.windowPlace_natCast`: the relative place at `i ∈ [0, n²]` is `i / n²`.
* `Separation.mean_windowPlace`: the relative place has mean `1/2`.
* `Separation.le_of_second_diff_le`: a sequence with second differences at most `2ω` grows at
  most quadratically.
-/

public section

open Filter Topology Finset

namespace Cslib.Circuits.Arithmetic.Separation

theorem sum_fin_ite_lt {M j : ℕ} (hj : j ≤ M) (x y : ℝ) :
    ∑ l : Fin M, (if (l : ℕ) < j then x else y) = j * x + ((M : ℝ) - j) * y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Fin.sum_univ_eq_sum_range (fun l => if l < j then x else y), Finset.sum_range_add,
    Finset.sum_congr rfl fun l hl => ite_eq_left (Finset.mem_range.1 hl),
    Finset.sum_congr rfl fun l _ => ite_eq_right (by omega : ¬ j + l < j)]
  simp

/-! ### Clamping -/

/-- Clamping an integer to `0, …, N`. -/
def clamp (N : ℕ) (i : ℤ) : ℕ := min i.toNat N

theorem clamp_le (N : ℕ) (i : ℤ) : clamp N i ≤ N := min_le_right _ _

theorem clamp_zero (N : ℕ) : clamp N 0 = 0 := by simp [clamp]

/-- The clamp, cast to `ℝ`, is Mathlib's projection onto `[0, N]`. -/
theorem cast_clamp (N : ℕ) (i : ℤ) :
    ((clamp N i : ℕ) : ℝ) = Set.projIcc (0 : ℝ) N (Nat.cast_nonneg N) i := by
  have hz : ((clamp N i : ℕ) : ℤ) = max 0 (min (N : ℤ) i) := by
    simp only [clamp]
    omega
  rw [Set.coe_projIcc, ← Int.cast_natCast, hz]
  push_cast
  rfl

/-- Clamping is `1`-Lipschitz, since `Set.projIcc` is. -/
theorem abs_clamp_sub_le (N : ℕ) (i i' : ℤ) :
    |((clamp N i : ℕ) : ℝ) - (clamp N i' : ℕ)| ≤ |(i : ℝ) - i'| := by
  have h := (LipschitzWith.projIcc (Nat.cast_nonneg (α := ℝ) N)).dist_le_mul i i'
  simp only [Subtype.dist_eq, NNReal.coe_one, one_mul, Real.dist_eq] at h
  rwa [cast_clamp, cast_clamp]

theorem abs_clamp_sub_clamp_succ_le (N : ℕ) (i : ℤ) :
    |((clamp N i : ℕ) : ℝ) - (clamp N (i + 1) : ℕ)| ≤ 1 := by
  refine (abs_clamp_sub_le _ _ _).trans ?_
  push_cast
  rw [sub_add_cancel_left, abs_neg, abs_one]

theorem clamp_cast {N : ℕ} {i : ℤ} (h0 : 0 ≤ i) (h1 : i ≤ N) :
    ((clamp N i : ℕ) : ℝ) = i := by
  have : ((clamp N i : ℕ) : ℤ) = i := by
    unfold clamp
    omega
  exact_mod_cast this

theorem clamp_window {n T : ℕ} {i k : ℤ} (h0 : 0 ≤ i + k + n) (h1 : i + k + n ≤ n ^ 2 * T) :
    ((clamp (n ^ 2 * T) (i + k + n) : ℕ) : ℝ) = i + k + n := by
  rw [clamp_cast h0 (by exact_mod_cast h1)]
  push_cast
  ring

theorem clamp_sq (n : ℕ) : clamp (n ^ 2) ((n : ℤ) ^ 2) = n ^ 2 := by
  rw [clamp, ← Nat.cast_pow, Int.toNat_natCast, min_self]

/-- What "`n` large" means for the windows: given `T ≥ 2` and `R`, eventually `n ≥ max R 3`,
which gives the listed inequalities. -/
theorem eventually_large {T : ℕ} (hT : 2 ≤ T) (R : ℕ) :
    ∀ᶠ n : ℕ in atTop, max n 1 = n ∧ (1 : ℝ) ≤ n ∧ R ≤ n ∧
      n ^ 2 + 2 * n ≤ n ^ 2 * T ∧ n ^ 2 + 2 * n ≤ 2 * n ^ 2 := by
  filter_upwards [eventually_ge_atTop (max R 3)] with n hn
  have h3 : 3 ≤ n := (le_max_right _ _).trans hn
  have h4 : n ^ 2 + 2 * n ≤ 2 * n ^ 2 := by nlinarith
  exact ⟨by omega, by exact_mod_cast (by omega : 1 ≤ n), (le_max_left _ _).trans hn,
    h4.trans (Nat.mul_le_mul_left _ hT |>.trans_eq' (by ring)), h4⟩

/-! ### The relative place in a window -/

/-- The relative place `i / n²` of a point in the `n`-th window, clamped to `[0, 1]`. -/
noncomputable def windowPlace : WindowFn :=
  fun n _ i _ => (clamp (n ^ 2) i : ℕ) / (n : ℝ) ^ 2

/-- At a point `i ∈ [0, n²]` of the window, the relative place is `i / n²`. -/
theorem windowPlace_natCast {n i : ℕ} (hi : i ≤ n ^ 2) (b : Bool) (k : ℤ) :
    windowPlace n b i k = (i : ℝ) / n ^ 2 := by
  rw [windowPlace, clamp_cast (Int.natCast_nonneg i) (by exact_mod_cast hi)]
  push_cast
  rfl

theorem windowPlace_nonneg (n : ℕ) (b : Bool) (i k : ℤ) : 0 ≤ windowPlace n b i k := by
  unfold windowPlace
  positivity

theorem windowPlace_le_one (n : ℕ) (b : Bool) (i k : ℤ) : windowPlace n b i k ≤ 1 := by
  unfold windowPlace
  exact div_le_one_of_le₀ (by exact_mod_cast clamp_le (n ^ 2) i) (by positivity)

theorem bounded_windowPlace : windowPlace.Bounded :=
  ⟨1, fun n b i k => by
    rw [abs_of_nonneg (windowPlace_nonneg _ _ _ _)]; exact windowPlace_le_one _ _ _ _⟩

/-- The relative place has mean `1/2`. -/
theorem mean_windowPlace : windowPlace.mean = 1 / 2 := by
  apply WindowFn.mean_eq bounded_windowPlace
  have h1 : Tendsto (fun n : ℕ => 1 / 2 - 1 / 2 * (1 / (n : ℝ)) ^ 2) atTop
      (𝓝 (1 / 2 - 1 / 2 * 0 ^ 2)) :=
    ((tendsto_one_div_atTop_nhds_zero_nat.pow 2).const_mul _).const_sub _
  norm_num at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h2 : ∀ b : Bool, ∑ i ∈ range (n ^ 2), ∑ k ∈ range n, windowPlace n b (i : ℕ) (k : ℕ) =
      n * (((n ^ 2 : ℕ) : ℝ) * ((n ^ 2 : ℕ) - 1) / 2 / n ^ 2) := by
    intro b
    have hsum : ∑ i ∈ range (n ^ 2), (i : ℝ) = ((n ^ 2 : ℕ) : ℝ) * ((n ^ 2 : ℕ) - 1) / 2 := by
      rw [← Nat.cast_sum, Finset.sum_range_id, ← Nat.choose_two_right, Nat.cast_choose_two]
    rw [← hsum, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hp : ∀ k ∈ range n, windowPlace n b (i : ℕ) (k : ℕ) = (i : ℝ) / n ^ 2 := fun k _ =>
      windowPlace_natCast (Finset.mem_range.1 hi).le b k
    rw [Finset.sum_congr rfl hp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [windowAvg_eq_sum, Finset.sum_congr rfl fun b _ => h2 b, Finset.sum_const, Finset.card_univ,
    Fintype.card_bool, nsmul_eq_mul]
  push_cast
  field_simp

/-! ### Two elementary inequalities -/

/-- A sequence `f` with second differences at most `2ω`, where `φ` stands for the value `f(−1)`,
satisfies `f(A) ≤ f(0) + A(f(0) − φ + ω) + A²ω`. For `ψ(l) = f(l) − l²ω` this says
`ψ(A) ≤ ψ(0) + A(ψ(0) − ψ(−1))`. -/
theorem le_of_second_diff_le {f : ℕ → ℝ} {φ ω : ℝ} (h0 : f 1 + φ ≤ 2 * f 0 + 2 * ω)
    (h : ∀ j, f (j + 2) + f j ≤ 2 * f (j + 1) + 2 * ω) (A : ℕ) :
    f A ≤ f 0 + A * (f 0 - φ + ω) + A ^ 2 * ω := by
  have key : ∀ j : ℕ, f (j + 1) - f j ≤ (f 0 - φ + ω) + (2 * j + 1) * ω := by
    intro j
    induction j with
    | zero => norm_num; linarith
    | succ j ih => have := h j; push_cast; linarith
  induction A with
  | zero => simp
  | succ A ih => have := key A; push_cast; linarith

/-- Squaring `|r n²(L' − L) + aL'| ≤ W`, with `1 − r ≤ 2θ` and `n²(L'² − L²) ≤ K`:
`W² ≥ a²L'² + a n²(L'² − L²) − 2aθK`. -/
theorem sq_le_of_abs_le {n L' L0 r a θ K W : ℝ} (hr0 : 0 ≤ r) (hr2 : 0 ≤ 1 - r)
    (hr1 : 1 - r ≤ 2 * θ) (ha : 0 ≤ a) (hK : 0 ≤ K) (hZ : n ^ 2 * (L' ^ 2 - L0 ^ 2) ≤ K)
    (h1 : r * (n ^ 2 * (L' - L0)) + a * L' ≤ W) (h2 : -(r * (n ^ 2 * (L' - L0)) + a * L') ≤ W) :
    a ^ 2 * (L' * L') + a * (n ^ 2 * (L' ^ 2 - L0 ^ 2)) - a * (2 * θ * K) ≤ W * W := by
  have E3 : (r * (n ^ 2 * (L' - L0)) + a * L') ^ 2 ≤ W ^ 2 := sq_le_sq' (by linarith) h1
  have Z2 : (1 - r) * (n ^ 2 * (L' ^ 2 - L0 ^ 2)) ≤ 2 * θ * K :=
    (mul_le_mul_of_nonneg_left hZ hr2).trans (mul_le_mul_of_nonneg_right hr1 hK)
  have Z4 : 0 ≤ a * r * (n ^ 2 * (L' - L0) ^ 2) := by positivity
  have Z5 := mul_le_mul_of_nonneg_left Z2 ha
  linarith [sq_nonneg (r * (n ^ 2 * (L' - L0)))]

end Cslib.Circuits.Arithmetic.Separation
