/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Languages.Probabilistic.Iteration
import CslibFrontier.Probability.PMF.SupportTsum

/-!
# Extended-nonnegative-real expectation on `ProbComp`

Expected value `Cslib.ProbComp.expect m f = ∑' a, (eval m) a * f a` for a closed probabilistic
program `m : ProbComp α` and cost function `f : α → ℝ≥0∞`.

Working in `ℝ≥0∞` makes expectation total without `[Fintype α]`, `[MeasurableSpace α]`, or
summability hypotheses. Every `PMF` has countable support, while program state spaces such as
machine configurations with infinite memory `ℕ → ℕ` need not be finite or carry a measurable space.
Unbounded or faulting branches naturally evaluate to `⊤`.

## Main definitions

* `Cslib.ProbComp.expect`: `ℝ≥0∞`-valued expectation `∑' a, (eval m) a * f a` over `ProbComp`.

## Main results

* `Cslib.ProbComp.expect_pure`, `Cslib.ProbComp.expect_bind`, `Cslib.ProbComp.expect_map`:
  monadic laws for `expect` (return, tower/law of total expectation, and postprocessing).
* `Cslib.ProbComp.expect_const`, `Cslib.ProbComp.expect_add`, `Cslib.ProbComp.expect_mul_left`,
  `Cslib.ProbComp.expect_mul_right`: linearity over `ℝ≥0∞`.
* `Cslib.ProbComp.expect_congr_on_support`, `Cslib.ProbComp.expect_mono_on_support`,
  `Cslib.ProbComp.expect_eq_top_of_mem_support`: support-localized congruence, monotonicity, and
  divergence propagation.
* `Cslib.ProbComp.expect_unifFin`, `Cslib.ProbComp.expect_uniform`: uniform finite averages.
* `Cslib.ProbComp.pow_mul_expect_iterate_le`: geometric contraction of `expect` across
  `OracleComp.iterate`.

## References

* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.ProbComp

variable {α β : Type}

/-- Expected value of `f : α → ℝ≥0∞` under a closed `ProbComp` computation. -/
noncomputable def expect (m : ProbComp α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, (eval m) a * f a

/-- The expected value of `f` under a deterministic computation `pure a` is `f a`. -/
@[simp]
theorem expect_pure (a : α) (f : α → ℝ≥0∞) : expect (pure a) f = f a := by
  classical
  rw [expect, eval_pure, tsum_eq_single a]
  · simp
  · intro b hb
    simp [hb]

/-- The expected value of a constant function `c` is `c`. -/
@[simp]
theorem expect_const (m : ProbComp α) (c : ℝ≥0∞) : expect m (fun _ => c) = c := by
  rw [expect, ENNReal.tsum_mul_right, (eval m).tsum_coe, one_mul]

/-- The expected value of the constant zero function is `0`. -/
theorem expect_zero (m : ProbComp α) : expect m (fun _ => 0) = 0 :=
  expect_const m 0

/-- Expectation distributes over pointwise addition in `ℝ≥0∞`. -/
theorem expect_add (m : ProbComp α) (f g : α → ℝ≥0∞) :
    expect m (fun a => f a + g a) = expect m f + expect m g := by
  simp only [expect, mul_add, tsum_add]

/-- Expectation pulls out a left scalar factor `c : ℝ≥0∞`. -/
theorem expect_mul_left (m : ProbComp α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    expect m (fun a => c * f a) = c * expect m f := by
  rw [expect, expect, ← ENNReal.tsum_mul_left]
  congr 1 with a : 1
  exact mul_left_comm ((eval m) a) c (f a)

/-- Expectation pulls out a right scalar factor `c : ℝ≥0∞`. -/
theorem expect_mul_right (m : ProbComp α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    expect m (fun a => f a * c) = expect m f * c := by
  simp only [expect, ← mul_assoc, ENNReal.tsum_mul_right]

/-- Law of total expectation (tower property) for monadic bind `m >>= k`. -/
theorem expect_bind (m : ProbComp α) (k : α → ProbComp β) (f : β → ℝ≥0∞) :
    expect (m >>= k) f = expect m (fun a => expect (k a) f) := by
  simp only [expect, eval_bind, PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [tsum_comm]
  congr 1 with a : 1
  simp only [mul_assoc, ENNReal.tsum_mul_left]

/-- Expectation after mapping `g` over `m` equals the expectation of `f ∘ g` under `m`. -/
theorem expect_map (g : α → β) (m : ProbComp α) (f : β → ℝ≥0∞) :
    expect (g <$> m) f = expect m (fun a => f (g a)) := by
  rw [← bind_pure_comp, expect_bind]
  simp only [expect_pure]

/-- Two functions that agree on the support of `m` have the same expectation under `m`. -/
theorem expect_congr_on_support {m : ProbComp α} {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ m.support, f a = g a) : expect m f = expect m g :=
  Probability.PMF.tsum_mul_congr_support (eval m) fun a ha => h a (by rwa [← support_eval])

/-- If `f a ≤ g a` for every `a` in the support of `m`, then `expect m f ≤ expect m g`. -/
theorem expect_mono_on_support {m : ProbComp α} {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ m.support, f a ≤ g a) : expect m f ≤ expect m g :=
  Probability.PMF.tsum_mul_mono_support (eval m) fun a ha => h a (by rwa [← support_eval])

/-- Expectation is monotone with respect to pointwise inequality. -/
theorem expect_mono {m : ProbComp α} {f g : α → ℝ≥0∞}
    (h : ∀ a, f a ≤ g a) : expect m f ≤ expect m g :=
  expect_mono_on_support fun a _ => h a

/-- An upper bound `B` holding on the support of `m` bounds `expect m f`. -/
theorem expect_le_of_forall_support {m : ProbComp α} {f : α → ℝ≥0∞} {B : ℝ≥0∞}
    (h : ∀ a ∈ m.support, f a ≤ B) : expect m f ≤ B :=
  (expect_mono_on_support h).trans_eq (expect_const m B)

/-- If `f` takes the value `⊤` at some outcome in the support of `m`, then `expect m f = ⊤`. -/
theorem expect_eq_top_of_mem_support {m : ProbComp α} {f : α → ℝ≥0∞} {a : α}
    (ha : a ∈ m.support) (hf : f a = ⊤) : expect m f = ⊤ := by
  have hpos : (eval m) a ≠ 0 :=
    (PMF.mem_support_iff (eval m) a).mp (by rwa [support_eval])
  refine top_unique ?_
  calc
    (⊤ : ℝ≥0∞) = (eval m) a * f a := by rw [hf, ENNReal.mul_top hpos]
    _ ≤ expect m f := le_tsum (f := fun b => (eval m) b * f b) a

/-- Expectation under `unifFin n` is the arithmetic average of `f` over `Fin (n + 1)`. -/
theorem expect_unifFin (n : ℕ) (f : Fin (n + 1) → ℝ≥0∞) :
    expect (unifFin n) f = (∑ k : Fin (n + 1), f k) / (n + 1 : ℝ≥0∞) := by
  rw [expect, eval_unifFin, tsum_fintype]
  simp only [Probability.PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]
  simp

/-- Expectation under `uniform α` is the arithmetic average of `f` over `α`. -/
theorem expect_uniform [Fintype α] [Nonempty α] (f : α → ℝ≥0∞) :
    expect (uniform α) f = (∑ a : α, f a) / (Fintype.card α : ℝ≥0∞) := by
  rw [expect, eval_uniform, tsum_fintype]
  simp only [Probability.PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

/-- If one step satisfies `c * E[f(step s)] ≤ d * f s` for every state `s`, then `k` iterated
steps satisfy `c ^ k * E[f(iterate k step init)] ≤ d ^ k * f init`. -/
theorem pow_mul_expect_iterate_le {c d : ℝ≥0∞} (step : α → ProbComp α) (init : α)
    (f : α → ℝ≥0∞) (hstep : ∀ s, c * expect (step s) f ≤ d * f s) (k : ℕ) :
    c ^ k * expect (OracleComp.iterate k step init) f ≤ d ^ k * f init := by
  induction k with
  | zero => simp [pow_zero]
  | succ k ih =>
    calc c ^ (k + 1) * expect (OracleComp.iterate (k + 1) step init) f
        = c ^ k * expect (OracleComp.iterate k step init) (fun a => c * expect (step a) f) := by
          rw [pow_succ', mul_assoc, OracleComp.iterate_succ, expect_bind, expect_mul_left,
            mul_left_comm]
      _ ≤ c ^ k * expect (OracleComp.iterate k step init) (fun a => d * f a) := by
          gcongr
          exact expect_mono hstep
      _ = d * (c ^ k * expect (OracleComp.iterate k step init) f) := by
          rw [expect_mul_left, mul_left_comm]
      _ ≤ d * (d ^ k * f init) := by gcongr
      _ = d ^ (k + 1) * f init := by rw [← mul_assoc, ← pow_succ']

end Cslib.ProbComp
