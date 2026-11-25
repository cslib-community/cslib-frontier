/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Event
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Hockey-stick divergence of discrete distributions

For discrete distributions `p, q : PMF α` and a scale factor `c : ℝ≥0∞`, the *hockey-stick
divergence* `hockeyStick c p q = ∑' a, (p a - c * q a)` is the total truncated excess of `p` over
`c · q`. At `c = 1` it is total variation distance
(`hockeyStick_one_le_iff_closeTo`), and at `c = exp ε` it is the optimal additive slack `δ` for
`(ε, δ)`-differential privacy (`forall_toOuterMeasure_le_iff_hockeyStick_le`, [DworkRoth2014]).

## Main definitions

* `Cslib.Probability.PMF.hockeyStick`: the hockey-stick divergence `∑' a, (p a - c * q a)`.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_le_mul_add_hockeyStick`,
  `Cslib.Probability.PMF.forall_toOuterMeasure_le_iff_hockeyStick_le`: variational event
  characterization.
* `Cslib.Probability.PMF.hockeyStick_eq_zero_iff`,
  `Cslib.Probability.PMF.hockeyStick_one_le_iff_closeTo`: pure-ratio and `c = 1` characterizations.
* `Cslib.Probability.PMF.tsum_mul_le_mul_tsum_mul_add_hockeyStick`: `[0, 1]`-valued expectation
  transfer.
* `Cslib.Probability.PMF.hockeyStick_bind_le`, `Cslib.Probability.PMF.hockeyStick_map_le`: data
  processing under Markov kernels and deterministic maps.
* `Cslib.Probability.PMF.hockeyStick_mul_le`: multiplicative triangle inequality across an
  intermediate distribution.
* `Cslib.Probability.PMF.hockeyStick_bind_pair_le`: adaptive two-stage composition.
* `Cslib.Probability.PMF.exists_subprob_of_hockeyStick_le`: decomposition of a pair with symmetric
  hockey-stick bound `δ` at `c ≥ 1` into `c`-close sub-probability weights retaining `1 - δ` mass.
* `Cslib.Probability.tsum_tsub_le_mul_rpow_tsum`,
  `Cslib.Probability.PMF.hockeyStick_le_mul_rpow_tsum`: Markov conversion from power-ratio moments
  to truncated excess / hockey-stick divergence.

## References

* [DworkRoth2014]
* [KairouzOhViswanath2017]
-/

public section

open scoped ENNReal

namespace Cslib.Probability

section MomentBound

variable {α : Type*}

/-- Pointwise Markov bound for likelihood ratios: either `p ≤ exp ε' · q`, or the excess is
controlled by `exp (-t ε') · p · (p / q) ^ t`. -/
private theorem tsub_mul_exp_le_mul_rpow {t : ℝ} (ht : 0 ≤ t) (ε' : ℝ) (p q : ℝ≥0∞) :
    p - ENNReal.ofReal (Real.exp ε') * q ≤
      ENNReal.ofReal (Real.exp (-(t * ε'))) * (p * (p / q) ^ t) := by
  set E := ENNReal.ofReal (Real.exp ε')
  rcases le_or_gt p (E * q) with h | h
  · simp [tsub_eq_zero_of_le h]
  refine tsub_le_self.trans ?_
  have hE0 : E ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hEt : E ^ t = ENNReal.ofReal (Real.exp (t * ε')) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ht, ← Real.exp_mul, mul_comm]
  have hq : q ≠ ⊤ := by rintro rfl; rw [ENNReal.mul_top hE0] at h; exact not_top_lt h
  have hdiv : E ≤ p / q := (ENNReal.le_div_iff_mul_le (Or.inr (ne_bot_of_gt h)) (Or.inl hq)).2 h.le
  calc p = ENNReal.ofReal (Real.exp (-(t * ε'))) * E ^ t * p := by
        rw [hEt, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
          Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(t * ε'))) * (p / q) ^ t * p := by gcongr
    _ = _ := by ring

/-- **Markov conversion from power-ratio moments to truncated excess**: for `t ≥ 0` and any mass
functions `p, q : α → ℝ≥0∞`,
`∑' a, (p a - exp ε' · q a) ≤ exp (-t ε') · ∑' a, p a · (p a / q a) ^ t`. -/
theorem tsum_tsub_le_mul_rpow_tsum {t : ℝ} (ht : 0 ≤ t) (ε' : ℝ) (p q : α → ℝ≥0∞) :
    ∑' a, (p a - ENNReal.ofReal (Real.exp ε') * q a) ≤
      ENNReal.ofReal (Real.exp (-(t * ε'))) * ∑' a, p a * (p a / q a) ^ t := by
  rw [← ENNReal.tsum_mul_left]
  exact tsum_le_tsum fun a => tsub_mul_exp_le_mul_rpow ht ε' (p a) (q a)

end MomentBound

namespace PMF

variable {α β : Type*}

/-- The hockey-stick divergence `∑' a, (p a - c * q a)` of `p` from `q` at factor `c`. -/
@[expose] noncomputable def hockeyStick (c : ℝ≥0∞) (p q : PMF α) : ℝ≥0∞ :=
  ∑' a, (p a - c * q a)

theorem hockeyStick_def (c : ℝ≥0∞) (p q : PMF α) :
    hockeyStick c p q = ∑' a, (p a - c * q a) :=
  rfl

/-- On a finite type, the hockey-stick divergence is an ordinary finite sum. -/
theorem hockeyStick_eq_sum [Fintype α] (c : ℝ≥0∞) (p q : PMF α) :
    hockeyStick c p q = ∑ a, (p a - c * q a) :=
  tsum_fintype _

theorem hockeyStick_le_one (c : ℝ≥0∞) (p q : PMF α) : hockeyStick c p q ≤ 1 :=
  (tsum_le_tsum fun _ => tsub_le_self).trans p.tsum_coe.le

theorem hockeyStick_ne_top (c : ℝ≥0∞) (p q : PMF α) : hockeyStick c p q ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hockeyStick_le_one c p q)

/-- Every event `S` satisfies `p(S) ≤ c · q(S) + hockeyStick c p q`. -/
theorem toOuterMeasure_le_mul_add_hockeyStick (c : ℝ≥0∞) (p q : PMF α) (S : Set α) :
    p.toOuterMeasure S ≤ c * q.toOuterMeasure S + hockeyStick c p q := by
  calc p.toOuterMeasure S = ∑' a, S.indicator p a := _root_.PMF.toOuterMeasure_apply p S
    _ ≤ ∑' a, (c * S.indicator q a + (p a - c * q a)) := by
      refine tsum_le_tsum fun a => ?_
      by_cases ha : a ∈ S
      · simp only [Set.indicator_of_mem ha]; exact le_add_tsub
      · simp [Set.indicator_of_notMem ha]
    _ = c * q.toOuterMeasure S + hockeyStick c p q := by
      rw [tsum_add, ENNReal.tsum_mul_left, _root_.PMF.toOuterMeasure_apply, hockeyStick]

/-- For a finite factor `c`, the event bounds `p(S) ≤ c · q(S) + δ` hold for all events `S`
if and only if `hockeyStick c p q ≤ δ`. The event `{a | c · q a < p a}` attains the excess. -/
theorem forall_toOuterMeasure_le_iff_hockeyStick_le {c : ℝ≥0∞} (hc : c ≠ ⊤) (p q : PMF α)
    (δ : ℝ≥0∞) :
    (∀ S : Set α, p.toOuterMeasure S ≤ c * q.toOuterMeasure S + δ) ↔ hockeyStick c p q ≤ δ := by
  classical
  constructor
  · intro h
    set T : Set α := {a | c * q a < p a}
    have hsplit : p.toOuterMeasure T = c * q.toOuterMeasure T + hockeyStick c p q := by
      rw [_root_.PMF.toOuterMeasure_apply, _root_.PMF.toOuterMeasure_apply, hockeyStick,
        ← ENNReal.tsum_mul_left, ← tsum_add]
      refine tsum_congr fun a => ?_
      by_cases ha : a ∈ T
      · simp only [Set.indicator_of_mem ha]; exact (add_tsub_cancel_of_le ha.le).symm
      · have hle : p a ≤ c * q a := not_lt.mp ha
        simp only [Set.indicator_of_notMem ha, mul_zero, zero_add, tsub_eq_zero_of_le hle]
    have hfin : c * q.toOuterMeasure T ≠ ⊤ :=
      ENNReal.mul_ne_top hc (toOuterMeasure_ne_top q T)
    exact (ENNReal.add_le_add_iff_left hfin).mp (by rw [← hsplit]; exact h T)
  · exact fun h S => (toOuterMeasure_le_mul_add_hockeyStick c p q S).trans (add_le_add le_rfl h)

/-- The hockey-stick divergence vanishes if and only if `p` is pointwise bounded by `c · q`. -/
theorem hockeyStick_eq_zero_iff (c : ℝ≥0∞) (p q : PMF α) :
    hockeyStick c p q = 0 ↔ ∀ a, p a ≤ c * q a := by
  rw [hockeyStick, tsum_eq_zero_iff]
  exact forall_congr' fun _ => tsub_eq_zero_iff_le

/-- For `1 ≤ c`, a distribution has zero hockey-stick divergence from itself. -/
theorem hockeyStick_self {c : ℝ≥0∞} (hc : 1 ≤ c) (p : PMF α) : hockeyStick c p p = 0 :=
  (hockeyStick_eq_zero_iff c p p).mpr fun _ => le_mul_of_one_le_left' hc

/-- The hockey-stick divergence is antitone in the scale factor `c`. -/
theorem hockeyStick_anti {c₁ c₂ : ℝ≥0∞} (hc : c₁ ≤ c₂) (p q : PMF α) :
    hockeyStick c₂ p q ≤ hockeyStick c₁ p q :=
  tsum_le_tsum fun a => tsub_le_tsub_left (mul_le_mul_of_nonneg_right hc zero_le) (p a)

/-- At `c = 1`, the hockey-stick divergence characterizes statistical closeness (`CloseTo`). -/
theorem hockeyStick_one_le_iff_closeTo {α : Type} (p q : PMF α) (δ : ℝ≥0∞) :
    hockeyStick 1 p q ≤ δ ↔ CloseTo p q δ := by
  simpa [hockeyStick] using closeTo_iff_tsum_tsub_le.symm

/-- At `c = 1`, the hockey-stick divergence is symmetric. -/
theorem hockeyStick_one_comm (p q : PMF α) : hockeyStick 1 p q = hockeyStick 1 q p := by
  simpa [hockeyStick] using tsum_tsub_comm p q

/-- Expectations of a `[0, 1]`-valued function under `p` and `q` differ by at most the
hockey-stick divergence: `E_p[g] ≤ c · E_q[g] + hockeyStick c p q`. -/
theorem tsum_mul_le_mul_tsum_mul_add_hockeyStick (c : ℝ≥0∞) (p q : PMF α) {g : α → ℝ≥0∞}
    (hg : ∀ a, g a ≤ 1) :
    ∑' a, p a * g a ≤ c * ∑' a, q a * g a + hockeyStick c p q := by
  calc ∑' a, p a * g a ≤ ∑' a, (c * (q a * g a) + (p a - c * q a)) := by
        refine tsum_le_tsum fun a => ?_
        calc p a * g a ≤ (c * q a + (p a - c * q a)) * g a := by gcongr; exact le_add_tsub
          _ = c * (q a * g a) + (p a - c * q a) * g a := by ring
          _ ≤ c * (q a * g a) + (p a - c * q a) := by
            gcongr; exact mul_le_of_le_one_right' (hg a)
    _ = c * ∑' a, q a * g a + hockeyStick c p q := by
        rw [tsum_add, ENNReal.tsum_mul_left, hockeyStick]

/-- **Data processing**: applying a Markov kernel `K` cannot increase the hockey-stick
divergence. -/
theorem hockeyStick_bind_le (c : ℝ≥0∞) (p q : PMF α) (K : α → PMF β) :
    hockeyStick c (p.bind K) (q.bind K) ≤ hockeyStick c p q := by
  have hpt (b : β) :
      (p.bind K) b - c * (q.bind K) b ≤ ∑' a, (p a - c * q a) * K a b := by
    rw [_root_.PMF.bind_apply, _root_.PMF.bind_apply, ← ENNReal.tsum_mul_left,
      tsub_le_iff_left, ← tsum_add]
    refine tsum_le_tsum fun a => ?_
    calc p a * K a b ≤ (c * q a + (p a - c * q a)) * K a b := by gcongr; exact le_add_tsub
      _ = c * (q a * K a b) + (p a - c * q a) * K a b := by ring
  calc hockeyStick c (p.bind K) (q.bind K)
      ≤ ∑' b, ∑' a, (p a - c * q a) * K a b := tsum_le_tsum hpt
    _ = ∑' a, ∑' b, (p a - c * q a) * K a b := tsum_comm
    _ = hockeyStick c p q :=
        tsum_congr fun a => by rw [ENNReal.tsum_mul_left, (K a).tsum_coe, mul_one]

/-- Deterministic post-processing cannot increase the hockey-stick divergence. -/
theorem hockeyStick_map_le (c : ℝ≥0∞) (p q : PMF α) (f : α → β) :
    hockeyStick c (p.map f) (q.map f) ≤ hockeyStick c p q := by
  rw [← _root_.PMF.bind_pure_comp, ← _root_.PMF.bind_pure_comp]
  exact hockeyStick_bind_le c p q _

/-- **Multiplicative triangle inequality** (group privacy step): comparing `p` to `r` at factor
`c₁ * c₂` is bounded by `hockeyStick c₁ p q + c₁ * hockeyStick c₂ q r`. -/
theorem hockeyStick_mul_le (c₁ c₂ : ℝ≥0∞) (p q r : PMF α) :
    hockeyStick (c₁ * c₂) p r ≤ hockeyStick c₁ p q + c₁ * hockeyStick c₂ q r := by
  rw [hockeyStick, hockeyStick, hockeyStick, ← ENNReal.tsum_mul_left, ← tsum_add]
  refine tsum_le_tsum fun a => ?_
  rw [tsub_le_iff_left]
  calc p a ≤ c₁ * q a + (p a - c₁ * q a) := le_add_tsub
    _ ≤ c₁ * (c₂ * r a + (q a - c₂ * r a)) + (p a - c₁ * q a) := by
        gcongr; exact le_add_tsub
    _ = c₁ * c₂ * r a + ((p a - c₁ * q a) + c₁ * (q a - c₂ * r a)) := by ring

/-- **Adaptive two-stage composition** for hockey-stick divergence: if `K a` and `L a` have
hockey-stick divergence at most `δ₂` at factor `c₂` for every `a ∈ p.support`, the joint pairs
`(a, b)` have hockey-stick divergence at most `hockeyStick c₁ p q + δ₂` at factor `c₁ * c₂`. -/
theorem hockeyStick_bind_pair_le {c₁ c₂ : ℝ≥0∞} (hc₁ : c₁ ≠ ⊤) (hc₂ : c₂ ≠ ⊤)
    (p q : PMF α) {K L : α → PMF β} {δ₂ : ℝ≥0∞}
    (hKL : ∀ a ∈ p.support, hockeyStick c₂ (K a) (L a) ≤ δ₂) :
    hockeyStick (c₁ * c₂)
      (p.bind fun a => (K a).bind fun b => _root_.PMF.pure (a, b))
      (q.bind fun a => (L a).bind fun b => _root_.PMF.pure (a, b)) ≤
      hockeyStick c₁ p q + δ₂ := by
  rw [← forall_toOuterMeasure_le_iff_hockeyStick_le (ENNReal.mul_ne_top hc₁ hc₂)]
  intro S
  have hsec (M : α → PMF β) (a : α) :
      ((M a).bind fun b => _root_.PMF.pure (a, b)).toOuterMeasure S =
        (M a).toOuterMeasure (Prod.mk a ⁻¹' S) := by
    rw [← _root_.PMF.toOuterMeasure_map_apply]
    rfl
  simp only [_root_.PMF.toOuterMeasure_bind_apply, hsec]
  set A : α → ℝ≥0∞ := fun a => (K a).toOuterMeasure (Prod.mk a ⁻¹' S)
  set B : α → ℝ≥0∞ := fun a => (L a).toOuterMeasure (Prod.mk a ⁻¹' S)
  have hA (a : α) : p a * A a ≤ p a * (min 1 (c₂ * B a) + δ₂) := by
    by_cases h0 : p a = 0
    · simp [h0]
    gcongr
    rw [← min_add_add_right]
    exact le_min ((toOuterMeasure_le_one _ _).trans le_self_add)
      ((toOuterMeasure_le_mul_add_hockeyStick c₂ (K a) (L a) _).trans
        (add_le_add le_rfl (hKL a h0)))
  calc ∑' a, p a * A a
      ≤ ∑' a, (p a * min 1 (c₂ * B a) + p a * δ₂) :=
        tsum_le_tsum fun a => by rw [← mul_add]; exact hA a
    _ = ∑' a, p a * min 1 (c₂ * B a) + δ₂ := by
        rw [tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
    _ ≤ (c₁ * ∑' a, q a * min 1 (c₂ * B a) + hockeyStick c₁ p q) + δ₂ :=
        add_le_add (tsum_mul_le_mul_tsum_mul_add_hockeyStick c₁ p q fun _ => min_le_left _ _) le_rfl
    _ ≤ (c₁ * ∑' a, q a * (c₂ * B a) + hockeyStick c₁ p q) + δ₂ := by
        gcongr with a; exact min_le_right _ _
    _ = c₁ * c₂ * ∑' a, q a * B a + (hockeyStick c₁ p q + δ₂) := by
        rw [add_assoc]
        congr 1
        simp only [mul_left_comm _ c₂, ENNReal.tsum_mul_left, mul_assoc]

/-- **Markov conversion** for `PMF`s: `hockeyStick (exp ε') p q` is bounded by `exp (-t ε')` times
the power-ratio moment `∑' a, p a · (p a / q a) ^ t`. -/
theorem hockeyStick_le_mul_rpow_tsum {t : ℝ} (ht : 0 ≤ t) (ε' : ℝ) (p q : PMF α) :
    hockeyStick (ENNReal.ofReal (Real.exp ε')) p q ≤
      ENNReal.ofReal (Real.exp (-(t * ε'))) * ∑' a, p a * (p a / q a) ^ t :=
  tsum_tsub_le_mul_rpow_tsum ht ε' p q

/-! ### Sub-probability decomposition -/

section Subprob

private theorem min_le_mul_min {c : ℝ≥0∞} (hc : 1 ≤ c) (x y : ℝ≥0∞) :
    min y (c * x) ≤ c * min x (c * y) := by
  rcases le_total x (c * y) with h | h
  · rw [min_eq_left h]
    exact min_le_right _ _
  · rw [min_eq_right h]
    exact (min_le_left _ _).trans ((le_mul_of_one_le_left' hc).trans (le_mul_of_one_le_left' hc))

private theorem exists_mix {P : α → ℝ≥0∞} {c : ℝ≥0∞} (hc : 1 ≤ c) (p₀ q₀ : α → ℝ≥0∞)
    (hp₀ : ∀ a, p₀ a ≤ P a) (hpq : ∀ a, p₀ a ≤ c * q₀ a) (hqp : ∀ a, q₀ a ≤ c * p₀ a)
    (hfin : ∑' a, p₀ a ≠ ⊤) (hlt : ∑' a, q₀ a < ∑' a, p₀ a) :
    ∃ p : α → ℝ≥0∞, (∀ a, p a ≤ P a) ∧ (∀ a, p a ≤ c * q₀ a) ∧ (∀ a, q₀ a ≤ c * p a) ∧
      ∑' a, p a = ∑' a, q₀ a := by
  set u : α → ℝ≥0∞ := fun a => min (p₀ a) (q₀ a)
  have hup : ∀ a, u a ≤ p₀ a := fun a => min_le_left _ _
  have huq : ∀ a, u a ≤ q₀ a := fun a => min_le_right _ _
  have hfq : ∑' a, q₀ a ≠ ⊤ := ne_top_of_lt hlt
  have hfu : ∑' a, u a ≠ ⊤ := ne_top_of_le_ne_top hfin (tsum_le_tsum hup)
  set mp := ∑' a, p₀ a with hmp
  set mq := ∑' a, q₀ a
  set mu := ∑' a, u a with hmu
  have hmuq : mu.toReal ≤ mq.toReal := (ENNReal.toReal_le_toReal hfu hfq).mpr (tsum_le_tsum huq)
  have hmqp : mq.toReal < mp.toReal := (ENNReal.toReal_lt_toReal hfq hfin).mpr hlt
  have hden : 0 < mp.toReal - mu.toReal := by linarith
  set s := (mp.toReal - mq.toReal) / (mp.toReal - mu.toReal)
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hden.le
  have hs1 : s ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hsden : s * (mp.toReal - mu.toReal) = mp.toReal - mq.toReal := div_mul_cancel₀ _ hden.ne'
  have hθ : ENNReal.ofReal (1 - s) + ENNReal.ofReal s = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hs0, sub_add_cancel, ENNReal.ofReal_one]
  have hcu : ∀ a, q₀ a ≤ c * u a := fun a => by
    change q₀ a ≤ c * min (p₀ a) (q₀ a)
    rcases le_total (p₀ a) (q₀ a) with h | h
    · rw [min_eq_left h]; exact hqp a
    · rw [min_eq_right h]; exact le_mul_of_one_le_left' hc
  refine ⟨fun a => ENNReal.ofReal (1 - s) * p₀ a + ENNReal.ofReal s * u a, fun a => ?_,
    fun a => ?_, fun a => ?_, ?_⟩
  · calc ENNReal.ofReal (1 - s) * p₀ a + ENNReal.ofReal s * u a
        ≤ ENNReal.ofReal (1 - s) * P a + ENNReal.ofReal s * P a := by
          gcongr; exacts [hp₀ a, (hup a).trans (hp₀ a)]
      _ = P a := by rw [← add_mul, hθ, one_mul]
  · calc ENNReal.ofReal (1 - s) * p₀ a + ENNReal.ofReal s * u a
        ≤ ENNReal.ofReal (1 - s) * (c * q₀ a) + ENNReal.ofReal s * (c * q₀ a) := by
          gcongr; exacts [hpq a, (huq a).trans (le_mul_of_one_le_left' hc)]
      _ = c * q₀ a := by rw [← add_mul, hθ, one_mul]
  · calc q₀ a = ENNReal.ofReal (1 - s) * q₀ a + ENNReal.ofReal s * q₀ a := by
          rw [← add_mul, hθ, one_mul]
      _ ≤ ENNReal.ofReal (1 - s) * (c * p₀ a) + ENNReal.ofReal s * (c * u a) := by
          gcongr; exacts [hqp a, hcu a]
      _ = c * (ENNReal.ofReal (1 - s) * p₀ a + ENNReal.ofReal s * u a) := by ring
  · rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← hmp, ← hmu,
      ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hfu, ← ENNReal.ofReal_toReal hfq,
      ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hs0,
      ← ENNReal.ofReal_add (mul_nonneg (by linarith) ENNReal.toReal_nonneg)
        (mul_nonneg hs0 ENNReal.toReal_nonneg)]
    congr 1
    linear_combination -hsden

/-- **Sub-probability decomposition**: if both hockey-stick divergences of `P` and `Q` at factor
`c ≥ 1` are at most `δ`, there exist sub-probability weights `p ≤ P` and `q ≤ Q` whose likelihood
ratio lies in `[c⁻¹, c]`, with `∑' p ≤ ∑' q` and `1 ≤ ∑' p + δ`. -/
theorem exists_subprob_of_hockeyStick_le (P Q : PMF α) {c : ℝ≥0∞} (hc : 1 ≤ c) {δ : ℝ≥0∞}
    (hPQ : hockeyStick c P Q ≤ δ) (hQP : hockeyStick c Q P ≤ δ) :
    ∃ p q : α → ℝ≥0∞, (∀ a, p a ≤ P a) ∧ (∀ a, q a ≤ Q a) ∧ (∀ a, p a ≤ c * q a) ∧
      (∀ a, q a ≤ c * p a) ∧ ∑' a, p a ≤ ∑' a, q a ∧ 1 ≤ ∑' a, p a + δ := by
  have hmass : ∀ P Q : PMF α, hockeyStick c P Q ≤ δ →
      1 ≤ ∑' a, min (P a) (c * Q a) + δ := fun P Q h => by
    calc (1 : ℝ≥0∞) = ∑' a, P a := P.tsum_coe.symm
      _ = hockeyStick c P Q + ∑' a, min (P a) (c * Q a) := by
          rw [hockeyStick, ← tsum_add]
          exact tsum_congr fun a => tsub_add_min.symm
      _ ≤ ∑' a, min (P a) (c * Q a) + δ := by rw [add_comm]; gcongr
  have hpq : ∀ a, min (P a) (c * Q a) ≤ c * min (Q a) (c * P a) := fun a => min_le_mul_min hc _ _
  have hqp : ∀ a, min (Q a) (c * P a) ≤ c * min (P a) (c * Q a) := fun a => min_le_mul_min hc _ _
  rcases le_or_gt (∑' a, min (P a) (c * Q a)) (∑' a, min (Q a) (c * P a)) with hle | hlt
  · exact ⟨_, _, fun a => min_le_left _ _, fun a => min_le_left _ _, hpq, hqp, hle,
      hmass P Q hPQ⟩
  · have hfin : ∑' a, min (P a) (c * Q a) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top
        ((tsum_le_tsum fun a => min_le_left _ _).trans P.tsum_coe.le)
    obtain ⟨p, hpP, hpq', hqp', hsum⟩ := exists_mix hc _ _ (fun a => min_le_left _ _) hpq hqp
      hfin hlt
    refine ⟨p, _, hpP, fun a => min_le_left _ _, hpq', hqp', hsum.le, ?_⟩
    exact hsum ▸ hmass Q P hQP

end Subprob

end PMF

end Cslib.Probability
