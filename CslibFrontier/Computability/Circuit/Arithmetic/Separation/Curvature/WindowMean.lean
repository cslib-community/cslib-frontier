/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Means over large windows

The price argument of *VP ≠ VNP over every field* [AnthropicVPVNP2026] (module `Nc.Cat.Mean`)
averages functions on two sheets of `ℤ²` over windows: for
every `n` the window has two sheets (`Bool`), `0 ≤ i < n²` and `0 ≤ k < n`. A *window function*
`f : WindowFn` is one function `f n` for every `n`. Its `mean` is the limit of the means over the
`n`-th window along a fixed free ultrafilter (Mathlib's `hyperfilter ℕ`), which exists for bounded
functions. The result is a positive linear functional on bounded window functions that is
invariant under translations and satisfies the inequality of Cauchy and Schwarz.

## Main definitions

* `WindowFn`, `WindowFn.Bounded`: window functions and the bounded ones.
* `window n`, `windowAvg n f`: the `n`-th window and the mean over it (`Finset.expect`).
* `WindowFn.mean`, `WindowFn.rms`: the mean over large windows, and the root of the mean square.

## Main results

* `WindowFn.mean_add`, `WindowFn.mean_smul`, `WindowFn.mean_const`, `WindowFn.mean_mono`:
  linearity and positivity.
* `WindowFn.mean_shift`: invariance under translations.
* `WindowFn.mean_steps`, `WindowFn.le_mean_tele`: telescoping sums of differences.
* `WindowFn.mean_mul_le`, `WindowFn.rms_add_le`: the inequalities of Cauchy–Schwarz and
  Minkowski.
-/

public section

open Filter Topology Finset
open scoped BigOperators

namespace Cslib.Circuits.Arithmetic.Separation

/-- Functions on two sheets of `ℤ²`, one for every window size `n`. -/
abbrev WindowFn := ℕ → Bool → ℤ → ℤ → ℝ

/-- The `n`-th window: two sheets, `0 ≤ i < n²`, `0 ≤ k < n`. -/
@[expose] def window (n : ℕ) : Finset (Bool × ℕ × ℕ) := univ ×ˢ range (n ^ 2) ×ˢ range n

/-- The mean over the `n`-th window, as `Finset.expect`. -/
@[expose] noncomputable def windowAvg (n : ℕ) (f : Bool → ℤ → ℤ → ℝ) : ℝ :=
  𝔼 p ∈ window n, match p with | (b, i, k) => f b i k

theorem mem_window {n : ℕ} {b : Bool} {i k : ℕ} : (b, i, k) ∈ window n ↔ i < n ^ 2 ∧ k < n := by
  simp [window]

/-- The window mean as a normalized sum, for the telescoping arguments. -/
theorem windowAvg_eq_sum (n : ℕ) (f : Bool → ℤ → ℤ → ℝ) :
    windowAvg n f = (∑ b, ∑ i ∈ range (n ^ 2), ∑ k ∈ range n, f b i k) / (2 * n ^ 3) := by
  simp only [windowAvg, Finset.expect_eq_sum_div_card, window, Finset.sum_product,
    Finset.card_product, Finset.card_univ, Fintype.card_bool, Finset.card_range]
  push_cast; ring

namespace WindowFn

/-- Bounded window functions. -/
@[expose] def Bounded (f : WindowFn) : Prop := ∃ C, ∀ n b i k, |f n b i k| ≤ C

theorem Bounded.add {f g : WindowFn} (hf : Bounded f) (hg : Bounded g) : Bounded (f + g) :=
  hf.elim fun C hC => hg.elim fun D hD =>
    ⟨C + D, fun n b i k => (abs_add_le _ _).trans (add_le_add (hC n b i k) (hD n b i k))⟩

theorem Bounded.mul {f g : WindowFn} (hf : Bounded f) (hg : Bounded g) : Bounded (f * g) :=
  hf.elim fun C hC => hg.elim fun D hD => ⟨C * D, fun n b i k =>
    (abs_mul (f n b i k) (g n b i k)).le.trans
      (mul_le_mul (hC n b i k) (hD n b i k) (abs_nonneg _) ((abs_nonneg _).trans (hC n b i k)))⟩

theorem Bounded.smul {f : WindowFn} (hf : Bounded f) (c : ℝ) : Bounded (c • f) :=
  hf.elim fun C hC => ⟨|c| * C, fun n b i k => by
    simpa only [Pi.smul_apply, smul_eq_mul, abs_mul] using
      mul_le_mul_of_nonneg_left (hC n b i k) (abs_nonneg _)⟩

theorem Bounded.const (c : ℝ) : Bounded fun _ _ _ _ => c := ⟨|c|, fun _ _ _ _ => le_rfl⟩

theorem Bounded.shift {f : WindowFn} (hf : Bounded f) (a c : ℤ) :
    Bounded fun n b i k => f n b (i + a) (k + c) :=
  hf.elim fun C hC => ⟨C, fun _ _ _ _ => hC _ _ _ _⟩

end WindowFn

theorem windowAvg_add (n : ℕ) (f g : Bool → ℤ → ℤ → ℝ) :
    windowAvg n (f + g) = windowAvg n f + windowAvg n g :=
  Finset.expect_add_distrib _ _ _

theorem windowAvg_smul (n : ℕ) (c : ℝ) (f : Bool → ℤ → ℤ → ℝ) :
    windowAvg n (c • f) = c * windowAvg n f :=
  (Finset.mul_expect _ _ _).symm

theorem windowAvg_mono {n : ℕ} {f g : Bool → ℤ → ℤ → ℝ}
    (h : ∀ b, ∀ i < n ^ 2, ∀ k < n, f b (i : ℕ) (k : ℕ) ≤ g b (i : ℕ) (k : ℕ)) :
    windowAvg n f ≤ windowAvg n g :=
  Finset.expect_le_expect fun ⟨_, _, _⟩ hp => h _ _ (mem_window.1 hp).1 _ (mem_window.1 hp).2

theorem windowAvg_const {n : ℕ} (hn : n ≠ 0) (c : ℝ) : windowAvg n (fun _ _ _ => c) = c :=
  Finset.expect_const ⟨(true, 0, 0), mem_window.2 ⟨by positivity, Nat.pos_of_ne_zero hn⟩⟩ c

/-- The inequality of Cauchy and Schwarz over one window. -/
theorem windowAvg_mul_sq_le (n : ℕ) (f g : Bool → ℤ → ℤ → ℝ) :
    windowAvg n (f * g) ^ 2 ≤ windowAvg n (f * f) * windowAvg n (g * g) := by
  let at_ (u : Bool → ℤ → ℤ → ℝ) (p : Bool × ℕ × ℕ) : ℝ := match p with | (b, i, k) => u b i k
  have e (u v : Bool → ℤ → ℤ → ℝ) : at_ (u * v) = fun p => at_ u p * at_ v p :=
    funext fun ⟨_, _, _⟩ => rfl
  simpa only [windowAvg, sq, ← e] using Finset.expect_mul_sq_le_sq_mul_sq (window n) (at_ f) (at_ g)

theorem abs_windowAvg_le {n : ℕ} {f : Bool → ℤ → ℤ → ℝ} {C : ℝ} (h : ∀ b i k, |f b i k| ≤ C) :
    |windowAvg n f| ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (h true 0 0)
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [windowAvg_eq_sum] using hC
  rw [abs_le]
  constructor
  · calc -C = windowAvg n (fun _ _ _ => -C) := (windowAvg_const hn _).symm
      _ ≤ _ := windowAvg_mono fun b i _ k _ => (abs_le.1 (h b i k)).1
  · calc windowAvg n f ≤ windowAvg n (fun _ _ _ => C) :=
          windowAvg_mono fun b i _ k _ => (abs_le.1 (h b i k)).2
      _ = C := windowAvg_const hn _

namespace WindowFn

/-- The mean of a window function over large windows: the limit of the window means along
`hyperfilter ℕ`. For bounded functions the limit exists (`WindowFn.tendsto_mean`). -/
noncomputable def mean (f : WindowFn) : ℝ :=
  limUnder (hyperfilter ℕ : Filter ℕ) fun n => windowAvg n (f n)

theorem tendsto_mean {f : WindowFn} (hf : Bounded f) :
    Tendsto (fun n => windowAvg n (f n)) (hyperfilter ℕ : Filter ℕ) (𝓝 (mean f)) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨a, -, ha⟩ := (isCompact_Icc (a := -C) (b := C)).ultrafilter_le_nhds
    ((hyperfilter ℕ).map fun n => windowAvg n (f n))
    (le_principal_iff.2 (Filter.mem_map.2 (Filter.univ_mem' fun n =>
      abs_le.1 (abs_windowAvg_le (hC n)))))
  exact tendsto_nhds_limUnder ⟨a, ha⟩

theorem mean_eq {f : WindowFn} (hf : Bounded f) {c : ℝ}
    (h : Tendsto (fun n => windowAvg n (f n)) atTop (𝓝 c)) : mean f = c :=
  tendsto_nhds_unique (tendsto_mean hf) (h.mono_left Nat.hyperfilter_le_atTop)

theorem mean_add {f g : WindowFn} (hf : Bounded f) (hg : Bounded g) :
    mean (f + g) = mean f + mean g := by
  refine tendsto_nhds_unique (tendsto_mean (hf.add hg)) ?_
  simpa only [Pi.add_apply, windowAvg_add] using (tendsto_mean hf).add (tendsto_mean hg)

theorem mean_smul {f : WindowFn} (hf : Bounded f) (c : ℝ) : mean (c • f) = c * mean f := by
  refine tendsto_nhds_unique (tendsto_mean (hf.smul c)) ?_
  simpa only [Pi.smul_apply, windowAvg_smul] using (tendsto_mean hf).const_mul c

theorem mean_const (c : ℝ) : mean (fun _ _ _ _ => c) = c :=
  mean_eq (Bounded.const c) (tendsto_const_nhds.congr'
    ((eventually_ne_atTop 0).mono fun _ hn => (windowAvg_const hn c).symm))

theorem mean_mono {f g : WindowFn} (hf : Bounded f) (hg : Bounded g)
    (h : ∀ᶠ n : ℕ in atTop, ∀ b, ∀ i < n ^ 2, ∀ k < n,
      f n b (i : ℕ) (k : ℕ) ≤ g n b (i : ℕ) (k : ℕ)) : mean f ≤ mean g :=
  le_of_tendsto_of_tendsto (tendsto_mean hf) (tendsto_mean hg)
    ((h.filter_mono Nat.hyperfilter_le_atTop).mono fun _ hn => windowAvg_mono hn)

theorem mean_le {f g : WindowFn} (hf : Bounded f) (hg : Bounded g)
    (h : ∀ n b i k, f n b i k ≤ g n b i k) : mean f ≤ mean g :=
  mean_mono hf hg (Eventually.of_forall fun _ _ _ _ _ _ => h _ _ _ _)

theorem mean_nonneg {f : WindowFn} (hf : Bounded f) (h : ∀ n b i k, 0 ≤ f n b i k) :
    0 ≤ mean f :=
  mean_const 0 ▸ mean_le (Bounded.const 0) hf h

/-! ### Translations -/

/-- `∑_{i < N} φ (i + 1) = ∑_{i < N} φ i + (φ N − φ 0)`. -/
private theorem sum_range_shift (φ : ℤ → ℝ) (N : ℕ) :
    ∑ i ∈ range N, φ ((i : ℤ) + 1) = ∑ i ∈ range N, φ (i : ℤ) + (φ N - φ 0) := by
  simpa only [Finset.sum_sub_distrib, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
    sub_eq_iff_eq_add'] using Finset.sum_range_sub (fun i : ℕ => φ (i : ℤ)) N

/-- Two bounded window functions whose window means differ by `O(1/n)` have the same mean. -/
private theorem mean_eq_of_abs_sub_le {f g : WindowFn} (hf : Bounded f) (hg : Bounded g)
    (D : ℝ) (h : ∀ᶠ n : ℕ in atTop, |windowAvg n (f n) - windowAvg n (g n)| ≤ D * (1 / n)) :
    mean f = mean g := by
  have h1 := (tendsto_mean hf).sub (tendsto_mean hg)
  have h2 : Tendsto (fun n => windowAvg n (f n) - windowAvg n (g n)) atTop (𝓝 0) :=
    squeeze_zero_norm' h (by simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul D)
  linarith [tendsto_nhds_unique h1 (h2.mono_left Nat.hyperfilter_le_atTop)]

/-- The boundary estimate behind `mean_shift_one` and `mean_shift_one'`: a sum over both sheets
and a face of length `L ≤ n²` of terms bounded by `2C`, divided by `2n³`, is at most `2C/n`. -/
private theorem abs_boundary_le {n L : ℕ} (hn : n ≠ 0) (hL : L ≤ n ^ 2) {C : ℝ} (hC : 0 ≤ C)
    (g : Bool → ℕ → ℝ) (hg : ∀ b j, |g b j| ≤ 2 * C) :
    |(∑ b, ∑ j ∈ range L, g b j) / (2 * n ^ 3)| ≤ 2 * C * (1 / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hL' : (L : ℝ) ≤ n ^ 2 := by exact_mod_cast hL
  rw [abs_div, abs_of_pos (mul_pos two_pos (pow_pos hn' 3)), div_le_iff₀ (by positivity)]
  calc |∑ b, ∑ j ∈ range L, g b j| ≤ ∑ b : Bool, ∑ j ∈ range L, 2 * C :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hg b j))
    _ = 2 * L * (2 * C) := by simp; ring
    _ ≤ 2 * n ^ 2 * (2 * C) := by gcongr
    _ = 2 * C * (1 / n) * (2 * n ^ 3) := by field_simp

private theorem mean_eq_of_sheet_diff {f g : WindowFn} (hf : Bounded f) (hg : Bounded g)
    (L : ℕ → ℕ) (hL : ∀ n, L n ≤ n ^ 2) (d : ℕ → Bool → ℕ → ℝ)
    (hdiff : ∀ n b,
      (∑ i ∈ range (n ^ 2), ∑ k ∈ range n, g n b i k) -
          (∑ i ∈ range (n ^ 2), ∑ k ∈ range n, f n b i k) =
        ∑ j ∈ range (L n), d n b j)
    (hd : ∀ C, (∀ n b i k, |f n b i k| ≤ C) → ∀ n b j, |d n b j| ≤ 2 * C) :
    mean g = mean f := by
  obtain ⟨C, hC⟩ := id hf
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 true 0 0)
  refine mean_eq_of_abs_sub_le hg hf (2 * C) ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [windowAvg_eq_sum, windowAvg_eq_sum, ← sub_div, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun b _ => hdiff n b]
  exact abs_boundary_le hn (hL n) hC0 (d n) (hd C hC n)

private theorem mean_shift_one {f : WindowFn} (hf : Bounded f) :
    mean (fun n b i k => f n b (i + 1) k) = mean f := by
  refine mean_eq_of_sheet_diff hf (by simpa using hf.shift 1 0) id
    (fun n => Nat.le_self_pow two_ne_zero n)
    (fun n b k => f n b ((n ^ 2 : ℕ) : ℤ) k - f n b 0 k) (fun n b => ?_)
    (fun C hC n b k =>
      (abs_sub _ _).trans (by linarith [hC n b ((n ^ 2 : ℕ) : ℤ) k, hC n b 0 k]))
  rw [Finset.sum_comm, Finset.sum_comm (s := range (n ^ 2)), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [sum_range_shift (fun i => f n b i k)]; ring

private theorem mean_shift_one' {f : WindowFn} (hf : Bounded f) :
    mean (fun n b i k => f n b i (k + 1)) = mean f := by
  refine mean_eq_of_sheet_diff hf (by simpa using hf.shift 0 1) (· ^ 2) (fun _ => le_rfl)
    (fun n b i => f n b i (n : ℕ) - f n b i 0) (fun n b => ?_)
    (fun C hC n b i => (abs_sub _ _).trans (by linarith [hC n b i (n : ℕ), hC n b i 0]))
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [sum_range_shift (fun k => f n b i k)]; ring

/-- From invariance under one step to invariance under every integer number of steps, for a
family of translations `T a` with `T a ∘ T c = T (a + c)`. -/
private theorem mean_shift_int (T : ℤ → WindowFn → WindowFn)
    (hT : ∀ a c f, T a (T c f) = T (a + c) f) (h0 : ∀ f, T 0 f = f)
    (hb : ∀ a f, Bounded f → Bounded (T a f)) (h1 : ∀ f, Bounded f → mean (T 1 f) = mean f)
    {f : WindowFn} (hf : Bounded f) (a : ℤ) : mean (T a f) = mean f := by
  induction a using Int.induction_on with
  | zero => rw [h0]
  | succ a ih => rw [← ih, ← h1 _ (hb a f hf), hT, add_comm]
  | pred a ih =>
    rw [← ih, ← h1 _ (hb _ f hf), hT]
    ring_nf

theorem mean_shift_left {f : WindowFn} (hf : Bounded f) (a : ℤ) :
    mean (fun n b i k => f n b (i + a) k) = mean f :=
  mean_shift_int (fun a f n b i k => f n b (i + a) k)
    (fun a c f => by funext n b i k; simp only [add_assoc])
    (fun f => by simp) (fun a f hf => by simpa using hf.shift a 0) (fun _ hf => mean_shift_one hf)
    hf a

theorem mean_shift_right {f : WindowFn} (hf : Bounded f) (a : ℤ) :
    mean (fun n b i k => f n b i (k + a)) = mean f :=
  mean_shift_int (fun a f n b i k => f n b i (k + a))
    (fun a c f => by funext n b i k; simp only [add_assoc])
    (fun f => by simp) (fun a f hf => by simpa using hf.shift 0 a) (fun _ hf => mean_shift_one' hf)
    hf a

/-- The mean is invariant under translations. -/
theorem mean_shift {f : WindowFn} (hf : Bounded f) (a c : ℤ) :
    mean (fun n b i k => f n b (i + a) (k + c)) = mean f := by
  rw [mean_shift_left (f := fun n b i k => f n b i (k + c)) (by simpa using hf.shift 0 c) a,
    mean_shift_right hf c]

/-- A telescoping sum: the mean of the scaled differences `n² (F(i+1) − F(i))` is at least
`c₀/2` when the differences across the window, summed over both sheets, are eventually at least
`c n → c₀`. -/
theorem le_mean_tele {F : WindowFn}
    (hX : Bounded fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k))
    {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀))
    (h : ∀ᶠ n : ℕ in atTop, ∀ k < n,
      c n ≤ ∑ b, (F n b ((n ^ 2 : ℕ) : ℤ) (k : ℕ) - F n b 0 (k : ℕ))) :
    c₀ / 2 ≤ mean fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k) := by
  refine le_of_tendsto_of_tendsto ((hc.div_const 2).mono_left Nat.hyperfilter_le_atTop)
    (tendsto_mean hX) (Eventually.filter_mono Nat.hyperfilter_le_atTop ?_)
  filter_upwards [h, eventually_ne_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have h1 : (windowAvg n fun b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k)) =
      (∑ k ∈ range n, ∑ b, (F n b ((n ^ 2 : ℕ) : ℤ) k - F n b 0 k)) / (2 * n) := by
    rw [windowAvg_eq_sum, Finset.sum_comm (s := range n)]
    have hsum (b : Bool) : ∑ i ∈ range (n ^ 2), ∑ k ∈ range n,
        (n : ℝ) ^ 2 * (F n b ((i : ℤ) + 1) k - F n b i k) =
        (n : ℝ) ^ 2 * ∑ k ∈ range n, (F n b ((n ^ 2 : ℕ) : ℤ) k - F n b 0 k) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_range_shift (fun i => F n b i k)]; ring
    rw [Finset.sum_congr rfl fun b _ => hsum b, ← Finset.mul_sum]
    field_simp
  rw [h1, div_le_div_iff₀ (by norm_num) (by positivity)]
  have h2 := Finset.sum_le_sum fun k hk => hn k (Finset.mem_range.1 hk)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  linarith

/-- Many steps of a telescoping sum: the scaled differences over `S` steps are bounded and have
`S` times the mean of one step. -/
theorem mean_steps {F : WindowFn}
    (hX : Bounded fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k)) (S : ℕ) :
    Bounded (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S) k - F n b i k)) ∧
      mean (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S) k - F n b i k)) =
        S * mean fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k) := by
  induction S with
  | zero => simpa using ⟨Bounded.const 0, mean_const 0⟩
  | succ S ih =>
    have hs := hX.shift S 0
    simp only [add_zero] at hs
    have : (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + (S + 1 : ℕ)) k - F n b i k) : WindowFn) =
        (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S + 1) k - F n b (i + S) k) : WindowFn) +
          (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S) k - F n b i k) : WindowFn) := by
      funext n b i k
      simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one, ← add_assoc]; ring
    rw [this, mean_add hs ih.1, ih.2, mean_shift_left hX S]
    exact ⟨hs.add ih.1, by push_cast; ring⟩

/-! ### Cauchy and Schwarz -/

/-- The root of the mean square. -/
@[expose] noncomputable def rms (f : WindowFn) : ℝ := √(mean (f * f))

theorem rms_nonneg (f : WindowFn) : 0 ≤ rms f := Real.sqrt_nonneg _

theorem rms_sq {f : WindowFn} (hf : Bounded f) : rms f ^ 2 = mean (f * f) :=
  Real.sq_sqrt (mean_nonneg (hf.mul hf) fun _ _ _ _ => mul_self_nonneg _)

/-- The inequality of Cauchy and Schwarz: `windowAvg_mul_sq_le` passes to the limit. -/
theorem mean_mul_le {f g : WindowFn} (hf : Bounded f) (hg : Bounded g) :
    mean (f * g) ≤ rms f * rms g := by
  have h : mean (f * g) ^ 2 ≤ mean (f * f) * mean (g * g) :=
    le_of_tendsto_of_tendsto ((tendsto_mean (hf.mul hg)).pow 2)
      ((tendsto_mean (hf.mul hf)).mul (tendsto_mean (hg.mul hg)))
      (Eventually.of_forall fun n => windowAvg_mul_sq_le n (f n) (g n))
  rw [rms, rms, ← Real.sqrt_mul (mean_nonneg (hf.mul hf) fun _ _ _ _ => mul_self_nonneg _)]
  exact Real.le_sqrt_of_sq_le h

theorem rms_mono {f g : WindowFn} (hf : Bounded f) (hg : Bounded g) (h0 : ∀ n b i k, 0 ≤ f n b i k)
    (h : ∀ᶠ n : ℕ in atTop, ∀ b, ∀ i < n ^ 2, ∀ k < n,
      f n b (i : ℕ) (k : ℕ) ≤ g n b (i : ℕ) (k : ℕ)) : rms f ≤ rms g := by
  refine Real.sqrt_le_sqrt (mean_mono (hf.mul hf) (hg.mul hg) ?_)
  filter_upwards [h] with n hn b i hi k hk
  exact mul_self_le_mul_self (h0 _ _ _ _) (hn b i hi k hk)

/-- The inequality of Minkowski. -/
theorem rms_add_le {f g : WindowFn} (hf : Bounded f) (hg : Bounded g) :
    rms (f + g) ≤ rms f + rms g := by
  refine (pow_le_pow_iff_left₀ (rms_nonneg _) (by positivity [rms_nonneg f, rms_nonneg g])
    two_ne_zero).1 ?_
  rw [rms_sq (hf.add hg), add_sq, rms_sq hf, rms_sq hg]
  have h1 : (f + g) * (f + g) = f * f + (2 : ℝ) • (f * g) + g * g := by
    funext n b i k
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h1, mean_add ((hf.mul hf).add ((hf.mul hg).smul 2)) (hg.mul hg),
    mean_add (hf.mul hf) ((hf.mul hg).smul 2), mean_smul (hf.mul hg)]
  linarith [mean_mul_le hf hg]

theorem mean_le_rms {f : WindowFn} (hf : Bounded f) : mean f ≤ rms f := by
  have h1 : rms (fun _ _ _ _ => (1 : ℝ)) = 1 := by simp [rms, Pi.mul_def, mean_const]
  simpa only [Pi.mul_def, mul_one, h1] using mean_mul_le hf (Bounded.const 1)

theorem rms_shift {f : WindowFn} (hf : Bounded f) (a c : ℤ) :
    rms (fun n b i k => f n b (i + a) (k + c)) = rms f := by
  exact congrArg Real.sqrt (mean_shift (hf.mul hf) a c)

end WindowFn

end Cslib.Circuits.Arithmetic.Separation
