/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Probability.PMF
public import CslibFrontier.Probability.HockeyStick
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rényi moments and Rényi divergence for discrete distributions

For nonnegative weight functions `p, q : X → ℝ≥0∞` and order `α : ℝ`, the *Rényi moment*
`renyiMoment α p q = ∑' x, p x * (p x / q x) ^ (α - 1)` is the power-ratio moment
`E_{x ~ p}[(p x / q x) ^ (α - 1)]` (equivalently `exp ((α - 1) D_α(p ‖ q))` for probability
distributions when `1 < α`). Writing the summand as `p x * (p x / q x) ^ (α - 1)` rather than
`q x * (p x / q x) ^ α` ensures that for `1 < α`, any off-support atom (`p x ≠ 0` and `q x = 0`)
contributes `p x * ⊤ = ⊤` instead of vanishing under `0 * ⊤ = 0`.

For discrete probability distributions `p, q : PMF X` and `1 < α`, `PMF.renyiDiv α p q : ℝ≥0∞` is
the Rényi divergence `D_α(p ‖ q) = log (renyiMoment α p q) / (α - 1)` in natural logarithms
[Renyi1961, §3, eq. (3.3), p. 554; Mironov2017, Definition 3] (where [Renyi1961] states the finite
positive-reference formula in `log₂`), taking the value `⊤` when `renyiMoment α p q = ⊤` (matching
`InformationTheory.klDiv`). `InformationTheory.klDiv` is a separate definition in
`CslibFrontier.Probability.RelativeEntropy`; this module covers finite orders `1 < α` and supplies
neither an `α → 1` limit theorem nor an `α = ∞` max-divergence endpoint. Weighted AM–GM
(`Real.geom_mean_le_arith_mean2_weighted`) yields joint convexity / sub-additivity of
`(u, v) ↦ u * (u / v) ^ (α - 1)` on arbitrary countable support, giving both nonnegativity
(`1 ≤ renyiMoment α p q`, [Mironov2017, Appendix A]) and the data-processing inequality under
Markov kernels (`renyiMoment_bind_le`, `renyiDiv_bind_le`, [Mironov2017, Section III]) without
`[Fintype]` or `[MeasurableSpace]` hypotheses.

## Main definitions

* `Cslib.Probability.renyiMoment`: power-ratio moment `∑' x, p x * (p x / q x) ^ (α - 1)` on
  `X → ℝ≥0∞`.
* `Cslib.Probability.PMF.renyiDiv`: extended `ℝ≥0∞`-valued Rényi divergence `D_α(p ‖ q)` on
  `PMF X`.

## Main results

* `Cslib.Probability.renyiMoment_comp_of_injective`,
  `Cslib.Probability.renyiMoment_mul_prod`: reindexing and conditional product factorization of
  `renyiMoment`.
* `Cslib.Probability.PMF.one_le_renyiMoment`, `Cslib.Probability.PMF.renyiDiv_self`:
  `1 ≤ renyiMoment α p q` for `1 < α` and `D_α(p ‖ p) = 0`.
* `Cslib.Probability.PMF.renyiDiv_le_ofReal_iff`: finite-bound characterization
  `renyiDiv α p q ≤ ofReal ε ↔ renyiMoment α p q ≤ ofReal (exp ((α - 1) ε))`.
* `Cslib.Probability.PMF.renyiMoment_bind_le`, `Cslib.Probability.PMF.renyiDiv_bind_le`,
  `Cslib.Probability.PMF.renyiDiv_map_le`: data-processing / post-processing inequalities.
* `Cslib.Probability.PMF.renyiDiv_bind_pair_le`: adaptive two-stage sequential composition
  [Mironov2017, Proposition 1].
* `Cslib.Probability.PMF.hockeyStick_le_of_renyiDiv_le`: conversion from Rényi divergence to
  `hockeyStick` divergence [Mironov2017, Proposition 3].

## References

* [A. Rényi, *On measures of entropy and information*][Renyi1961]
* [I. Mironov, *Rényi differential privacy*][Mironov2017]
-/

public section

open scoped ENNReal

namespace Cslib.Probability

section Moment

variable {X Y : Type*}

/-- The order-`α` Rényi power-ratio moment `∑' x, p x * (p x / q x) ^ (α - 1)` of nonnegative
weight functions `p, q : X → ℝ≥0∞` (allowing sub-probability weights as well as `PMF`s). -/
@[expose] noncomputable def renyiMoment (α : ℝ) (p q : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, p x * (p x / q x) ^ (α - 1)

/-- Markov's inequality from `renyiMoment` to truncated excess: for `1 ≤ α` and any mass functions
`p, q : X → ℝ≥0∞`,
`∑' x, (p x - exp ε' · q x) ≤ exp (-(α - 1) ε') · renyiMoment α p q`. -/
theorem tsum_tsub_le_renyiMoment {α : ℝ} (hα : 1 ≤ α) (ε' : ℝ) (p q : X → ℝ≥0∞) :
    ∑' x, (p x - ENNReal.ofReal (Real.exp ε') * q x) ≤
      ENNReal.ofReal (Real.exp (-((α - 1) * ε'))) * renyiMoment α p q :=
  tsum_tsub_le_mul_rpow_tsum (sub_nonneg.mpr hα) ε' p q

/-- Reindexing `renyiMoment` along an injective map `f : X → Y` when `p` vanishes outside
`Set.range f`. -/
theorem renyiMoment_comp_of_injective {f : X → Y} (hf : Function.Injective f) (α : ℝ)
    {p q : Y → ℝ≥0∞} (hp : ∀ y, y ∉ Set.range f → p y = 0) :
    renyiMoment α p q = renyiMoment α (p ∘ f) (q ∘ f) := by
  rw [renyiMoment, renyiMoment, ← hf.tsum_eq]
  · rfl
  · intro y hy
    by_contra hnot
    exact hy (by dsimp only; rw [hp y hnot, zero_mul])

/-- Conditional product factorization of `renyiMoment` on `X × Y`: for `1 ≤ α` and finite
denominator weights `q₁`, `q₂`, the Rényi moment of `(x, y) ↦ p₁ x * p₂ x y` against
`(x, y) ↦ q₁ x * q₂ x y` factors through the conditional moments `renyiMoment α (p₂ x) (q₂ x)`. -/
theorem renyiMoment_mul_prod {α : ℝ} (hα : 1 ≤ α) {p₁ q₁ : X → ℝ≥0∞} {p₂ q₂ : X → Y → ℝ≥0∞}
    (hq₁ : ∀ x, q₁ x ≠ ⊤) (hq₂ : ∀ x y, q₂ x y ≠ ⊤) :
    renyiMoment α (fun z : X × Y => p₁ z.1 * p₂ z.1 z.2)
        (fun z : X × Y => q₁ z.1 * q₂ z.1 z.2) =
      ∑' x, p₁ x * (p₁ x / q₁ x) ^ (α - 1) * renyiMoment α (p₂ x) (q₂ x) := by
  rw [renyiMoment]
  refine (tsum_prod (f := fun x y =>
    p₁ x * p₂ x y * ((p₁ x * p₂ x y) / (q₁ x * q₂ x y)) ^ (α - 1))).trans ?_
  refine tsum_congr fun x => ?_
  rw [renyiMoment, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  rw [ENNReal.mul_div_mul_comm (Or.inr (hq₂ x y)) (Or.inl (hq₁ x)),
    ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hα)]
  ring

private theorem young_mul_rpow {α a b R : ℝ} (hα : 1 < α) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R) :
    a * R ^ (α - 1) ≤
      (1 / α) * (a * (a / b) ^ (α - 1)) + ((α - 1) / α) * (b * R ^ α) := by
  have hα0 : 0 < α := by linarith
  have hab : 0 < a / b := div_pos ha hb
  have hw : 1 / α + (α - 1) / α = 1 := by field_simp; ring
  have hz₁ : a * (a / b) ^ (α - 1) = b * (a / b) ^ α := by
    rw [Real.rpow_sub_one hab.ne']; field_simp
  have hgm := Real.geom_mean_le_arith_mean2_weighted (by positivity)
    (div_nonneg (by linarith) hα0.le) (by positivity : 0 ≤ a * (a / b) ^ (α - 1))
    (by positivity : 0 ≤ b * R ^ α) hw
  calc a * R ^ (α - 1) = (a * (a / b) ^ (α - 1)) ^ (1 / α) * (b * R ^ α) ^ ((α - 1) / α) := by
        rw [hz₁, Real.mul_rpow hb.le (Real.rpow_nonneg hab.le _), ← Real.rpow_mul hab.le,
          mul_one_div_cancel hα0.ne', Real.rpow_one, Real.mul_rpow hb.le (Real.rpow_nonneg hR.le _),
          ← Real.rpow_mul hR.le, mul_div_cancel₀ _ hα0.ne', mul_mul_mul_comm, ← Real.rpow_add hb,
          hw, Real.rpow_one, ← mul_assoc, mul_div_cancel₀ a hb.ne']
    _ ≤ _ := hgm

/-- Joint sub-additivity of `(u, v) ↦ u * (u / v) ^ (α - 1)` over countable sums for `1 < α`. -/
private theorem mul_div_rpow_tsum_le {α : ℝ} (hα : 1 < α) {u v : X → ℝ≥0∞}
    (hU : ∑' x, u x ≠ ⊤) (hV : ∑' x, v x ≠ ⊤) :
    (∑' x, u x) * ((∑' x, u x) / (∑' x, v x)) ^ (α - 1) ≤
      ∑' x, u x * (u x / v x) ^ (α - 1) := by
  set t : ℝ := α - 1
  have ht : 0 < t := sub_pos.mpr hα
  have hα0 : 0 < α := by linarith
  set U : ℝ≥0∞ := ∑' x, u x
  set V : ℝ≥0∞ := ∑' x, v x
  rcases eq_or_ne U 0 with hU0 | hU0
  · simp [hU0]
  by_cases hsupp : ∃ x, u x ≠ 0 ∧ v x = 0
  · obtain ⟨x₀, hu₀, hv₀⟩ := hsupp
    have htop : u x₀ * (u x₀ / v x₀) ^ t = ⊤ := by
      rw [hv₀, ENNReal.div_zero hu₀, ENNReal.top_rpow_of_pos ht, ENNReal.mul_top hu₀]
    have hle := le_tsum (fun x => u x * (u x / v x) ^ t) x₀
    rw [htop, top_le_iff] at hle
    exact le_top.trans_eq hle.symm
  have hsupp' (x : X) (hu : u x ≠ 0) : v x ≠ 0 := fun hv => hsupp ⟨x, hu, hv⟩
  have hV0 : V ≠ 0 := by
    intro h0
    apply hU0
    rw [tsum_eq_zero_iff] at h0 ⊢
    exact fun x => by_contra fun hu => hsupp' x hu (h0 x)
  set M : ℝ≥0∞ := ∑' x, u x * (u x / v x) ^ t
  rcases eq_or_ne M ⊤ with hM_top | hM_top
  · exact hM_top ▸ le_top
  have hu_top (x : X) : u x ≠ ⊤ := ne_top_of_le_ne_top hU (le_tsum u x)
  have hv_top (x : X) : v x ≠ ⊤ := ne_top_of_le_ne_top hV (le_tsum v x)
  have hUV0 : U / V ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hU0, hV⟩
  have hUV_top : U / V ≠ ⊤ := ENNReal.div_ne_top hU hV0
  set R : ℝ := (U / V).toReal
  have hR : 0 < R := by dsimp only [R]; ennreal_to_real using pos_iff_ne_zero.mpr hUV0
  have hUV_rpow_t : (U / V) ^ t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht.le hUV_top
  have hUV_rpow_α : (U / V) ^ α ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hα0.le hUV_top
  have hpt (x : X) :
      u x * (U / V) ^ t ≤
        ENNReal.ofReal (1 / α) * (u x * (u x / v x) ^ t) +
          ENNReal.ofReal (t / α) * (v x * (U / V) ^ α) := by
    rcases eq_or_ne (u x) 0 with hux0 | hux0
    · simp [hux0]
    have hvx0 : v x ≠ 0 := hsupp' x hux0
    have hux_top := hu_top x
    have hvx_top := hv_top x
    have ha : 0 < (u x).toReal := by ennreal_to_real using pos_iff_ne_zero.mpr hux0
    have hb : 0 < (v x).toReal := by ennreal_to_real using pos_iff_ne_zero.mpr hvx0
    have huv_rpow : (u x / v x) ^ t ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg ht.le (ENNReal.div_ne_top hux_top hvx0)
    have hyoung : (u x).toReal * ((U / V).toReal) ^ t ≤
        1 / α * ((u x).toReal * ((u x).toReal / (v x).toReal) ^ t) +
          t / α * ((v x).toReal * ((U / V).toReal) ^ α) := young_mul_rpow hα ha hb hR
    ennreal_to_real
    ennreal_to_real at hyoung
    exact hyoung
  have hsum_ineq :
      U * (U / V) ^ t ≤
        ENNReal.ofReal (1 / α) * M + ENNReal.ofReal (t / α) * (V * (U / V) ^ α) := by
    calc U * (U / V) ^ t
        = ∑' x, u x * (U / V) ^ t := (ENNReal.tsum_mul_right).symm
      _ ≤ ∑' x, (ENNReal.ofReal (1 / α) * (u x * (u x / v x) ^ t) +
            ENNReal.ofReal (t / α) * (v x * (U / V) ^ α)) := tsum_le_tsum hpt
      _ = ENNReal.ofReal (1 / α) * M + ENNReal.ofReal (t / α) * (V * (U / V) ^ α) := by
          rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  have hV_eq : V * (U / V) ^ α = U * (U / V) ^ t := by
    rw [show α = 1 + t by dsimp only [t]; ring, ENNReal.rpow_add _ _ hUV0 hUV_top, ENNReal.rpow_one,
      ← mul_assoc, ENNReal.mul_div_cancel hV0 hV]
  rw [hV_eq] at hsum_ineq
  have hL_top : U * (U / V) ^ t ≠ ⊤ := ENNReal.mul_ne_top hU hUV_rpow_t
  generalize U * (U / V) ^ t = L at hsum_ineq hL_top ⊢
  ennreal_to_real at hsum_ineq ⊢
  have h1L : 1 / α * L.toReal + t / α * L.toReal = L.toReal := by
    rw [← add_mul, ← add_div, show 1 + t = α by dsimp only [t]; ring, div_self hα0.ne', one_mul]
  exact le_of_mul_le_mul_left (by linarith : 1 / α * L.toReal ≤ 1 / α * M.toReal) (by positivity)

end Moment

namespace PMF

variable {X Y : Type*}

/-- The Rényi divergence `D_α(p ‖ q) = log (renyiMoment α p q) / (α - 1)` of discrete
distributions `p, q : PMF X` for orders `1 < α`, valued in `ℝ≥0∞` (equal to `⊤` when
`renyiMoment α p q = ⊤`) [Renyi1961, §3, eq. (3.3), p. 554; Mironov2017, Definition 3].

This finite-order formula applies to `1 < α`: at `α = 1`, `renyiMoment 1 p q = 1` and division by
`α - 1 = 0` evaluates to `0`, whereas `InformationTheory.klDiv` in
`CslibFrontier.Probability.RelativeEntropy` is a separate Kullback–Leibler definition (no `α → 1`
limit theorem or `α = ∞` max-divergence endpoint is proved here). -/
noncomputable def renyiDiv (α : ℝ) (p q : PMF X) : ℝ≥0∞ :=
  open Classical in
  if renyiMoment α p q = ⊤ then ⊤
  else ENNReal.ofReal (Real.log (renyiMoment α p q).toReal / (α - 1))

/-- `renyiDiv α p q` is infinite if and only if `renyiMoment α p q` is infinite. -/
@[simp] theorem renyiDiv_eq_top_iff (α : ℝ) (p q : PMF X) :
    renyiDiv α p q = ⊤ ↔ renyiMoment α p q = ⊤ := by
  classical
  simp [renyiDiv]

/-- Value of `renyiDiv α p q` when `renyiMoment α p q ≠ ⊤`. -/
theorem renyiDiv_of_ne_top {α : ℝ} {p q : PMF X} (h : renyiMoment α p q ≠ ⊤) :
    renyiDiv α p q = ENNReal.ofReal (Real.log (renyiMoment α p q).toReal / (α - 1)) := by
  classical
  simp [renyiDiv, h]

/-- **Nonnegativity of Rényi divergence** (moment form) [Mironov2017, Appendix A]: for `1 < α`
and any `p, q : PMF X`, `1 ≤ renyiMoment α p q`. -/
theorem one_le_renyiMoment {α : ℝ} (hα : 1 < α) (p q : PMF X) :
    1 ≤ renyiMoment α p q := by
  have hp : ∑' x, p x ≠ ⊤ := by rw [p.tsum_coe]; exact ENNReal.one_ne_top
  have hq : ∑' x, q x ≠ ⊤ := by rw [q.tsum_coe]; exact ENNReal.one_ne_top
  have h := mul_div_rpow_tsum_le hα hp hq
  rw [p.tsum_coe, q.tsum_coe, div_one, ENNReal.one_rpow, mul_one] at h
  exact h

/-- A distribution has zero Rényi divergence from itself. -/
@[simp] theorem renyiDiv_self (α : ℝ) (p : PMF X) : renyiDiv α p p = 0 := by
  have hmom : renyiMoment α p p = 1 := by
    rw [renyiMoment, ← p.tsum_coe]
    refine tsum_congr fun x => ?_
    rcases eq_or_ne (p x) 0 with hx0 | hx0
    · simp [hx0]
    · rw [ENNReal.div_self hx0 (p.apply_ne_top x), ENNReal.one_rpow, mul_one]
  simp [renyiDiv, hmom]

/-- Finite-bound characterization of Rényi divergence: for `1 < α` and `0 ≤ ε`,
`renyiDiv α p q ≤ ofReal ε` holds iff `renyiMoment α p q ≤ ofReal (exp ((α - 1) * ε))`. -/
theorem renyiDiv_le_ofReal_iff {α ε : ℝ} (hα : 1 < α) (p q : PMF X) (hε : 0 ≤ ε) :
    renyiDiv α p q ≤ ENNReal.ofReal ε ↔
      renyiMoment α p q ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε)) := by
  have ht : 0 < α - 1 := sub_pos.mpr hα
  have h1 : 1 ≤ renyiMoment α p q := one_le_renyiMoment hα p q
  classical
  dsimp only [renyiDiv]
  split_ifs with htop
  · simp [htop]
  · have hM1 : 1 ≤ (renyiMoment α p q).toReal := by ennreal_to_real using h1
    have hM0 : 0 < (renyiMoment α p q).toReal := zero_lt_one.trans_le hM1
    rw [ENNReal.ofReal_le_ofReal_iff hε, div_le_iff₀ ht, mul_comm ε (α - 1),
      Real.log_le_iff_le_exp hM0, ← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
      ENNReal.ofReal_toReal htop]

private theorem mul_div_mul_right_le_rpow {t : ℝ} (a b c : ℝ≥0∞) (hc : c ≠ ⊤) :
    (a * c) * ((a * c) / (b * c)) ^ t ≤ a * (a / b) ^ t * c := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  have hdiv : (a * c) / (b * c) = a / b := by
    rw [ENNReal.mul_div_mul_comm (Or.inr hc) (Or.inr hc0), ENNReal.div_self hc0 hc, mul_one]
  rw [hdiv]
  exact le_of_eq (by ring)

/-- **Data-processing inequality** for `renyiMoment` [Mironov2017, Section III]: for `1 ≤ α`,
applying a Markov kernel `K : X → PMF Y` cannot increase `renyiMoment α`. -/
theorem renyiMoment_bind_le {α : ℝ} (hα : 1 ≤ α) (p q : PMF X) (K : X → PMF Y) :
    renyiMoment α (p.bind K) (q.bind K) ≤ renyiMoment α p q := by
  rcases hα.eq_or_lt with rfl | hα_lt
  · simp only [renyiMoment, sub_self, ENNReal.rpow_zero, mul_one, (p.bind K).tsum_coe,
      p.tsum_coe, le_rfl]
  have hstep (y : Y) :
      (p.bind K) y * ((p.bind K) y / (q.bind K) y) ^ (α - 1) ≤
        ∑' x, p x * (p x / q x) ^ (α - 1) * K x y := by
    have hp_ne : ∑' x, p x * K x y ≠ ⊤ := by
      simpa only [_root_.PMF.bind_apply] using (p.bind K).apply_ne_top y
    have hq_ne : ∑' x, q x * K x y ≠ ⊤ := by
      simpa only [_root_.PMF.bind_apply] using (q.bind K).apply_ne_top y
    calc (p.bind K) y * ((p.bind K) y / (q.bind K) y) ^ (α - 1)
        = (∑' x, p x * K x y) * ((∑' x, p x * K x y) / (∑' x, q x * K x y)) ^ (α - 1) := by
          simp only [_root_.PMF.bind_apply]
      _ ≤ ∑' x, (p x * K x y) * ((p x * K x y) / (q x * K x y)) ^ (α - 1) :=
          mul_div_rpow_tsum_le hα_lt hp_ne hq_ne
      _ ≤ ∑' x, p x * (p x / q x) ^ (α - 1) * K x y :=
          tsum_le_tsum fun x => mul_div_mul_right_le_rpow (p x) (q x)
            (K x y) ((K x).apply_ne_top y)
  calc renyiMoment α (p.bind K) (q.bind K)
      ≤ ∑' y, ∑' x, p x * (p x / q x) ^ (α - 1) * K x y := tsum_le_tsum hstep
    _ = ∑' x, ∑' y, p x * (p x / q x) ^ (α - 1) * K x y := tsum_comm
    _ = renyiMoment α p q := by
        rw [renyiMoment]
        refine tsum_congr fun x => ?_
        rw [ENNReal.tsum_mul_left, (K x).tsum_coe, mul_one]

/-- **Data-processing inequality** for Rényi divergence [Mironov2017, Section III]: for `1 < α`,
applying a Markov kernel `K : X → PMF Y` cannot increase `renyiDiv α`. -/
theorem renyiDiv_bind_le {α : ℝ} (hα : 1 < α) (p q : PMF X) (K : X → PMF Y) :
    renyiDiv α (p.bind K) (q.bind K) ≤ renyiDiv α p q := by
  classical
  by_cases htop : renyiMoment α p q = ⊤
  · simp [renyiDiv, htop]
  have hmom := renyiMoment_bind_le hα.le p q K
  have htop_bind : renyiMoment α (p.bind K) (q.bind K) ≠ ⊤ := ne_top_of_le_ne_top htop hmom
  have h1_bind : 1 ≤ (renyiMoment α (p.bind K) (q.bind K)).toReal := by
    ennreal_to_real using one_le_renyiMoment hα (p.bind K) (q.bind K)
  have hle_real : (renyiMoment α (p.bind K) (q.bind K)).toReal ≤ (renyiMoment α p q).toReal := by
    ennreal_to_real using hmom
  simp only [renyiDiv, htop, htop_bind, ↓reduceIte]
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (sub_pos.mpr hα).le)
  exact Real.log_le_log (zero_lt_one.trans_le h1_bind) hle_real

/-- Deterministic post-processing cannot increase Rényi divergence [Mironov2017, Section III]. -/
theorem renyiDiv_map_le {α : ℝ} (hα : 1 < α) (p q : PMF X) (f : X → Y) :
    renyiDiv α (p.map f) (q.map f) ≤ renyiDiv α p q := by
  rw [← _root_.PMF.bind_pure_comp, ← _root_.PMF.bind_pure_comp]
  exact renyiDiv_bind_le hα p q _

/-- **Adaptive sequential composition** for Rényi divergence [Mironov2017, Proposition 1]: if
`K x` and `L x` have Rényi divergence at most `B` for every `x ∈ p.support`, then the joint
distributions `(x, y)` have Rényi divergence at most `renyiDiv α p q + B`. -/
theorem renyiDiv_bind_pair_le {α : ℝ} (hα : 1 < α) (p q : PMF X) {K L : X → PMF Y}
    {B : ℝ≥0∞} (hKL : ∀ x ∈ p.support, renyiDiv α (K x) (L x) ≤ B) :
    renyiDiv α (p.bind fun x => (K x).bind fun y => _root_.PMF.pure (x, y))
      (q.bind fun x => (L x).bind fun y => _root_.PMF.pure (x, y)) ≤
      renyiDiv α p q + B := by
  rcases eq_or_ne (renyiDiv α p q) ⊤ with hp_top | hp_top
  · simp [hp_top]
  rcases eq_or_ne B ⊤ with hB_top | hB_top
  · simp [hB_top]
  set ε₁ : ℝ := (renyiDiv α p q).toReal
  set ε₂ : ℝ := B.toReal
  have hε₁_nn : 0 ≤ ε₁ := ENNReal.toReal_nonneg
  have hε₂_nn : 0 ≤ ε₂ := ENNReal.toReal_nonneg
  have hp_eq : renyiDiv α p q = ENNReal.ofReal ε₁ := (ENNReal.ofReal_toReal hp_top).symm
  have hB_eq : B = ENNReal.ofReal ε₂ := (ENNReal.ofReal_toReal hB_top).symm
  have hmom₁ : renyiMoment α p q ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε₁)) :=
    (renyiDiv_le_ofReal_iff hα p q hε₁_nn).mp (le_of_eq hp_eq)
  rw [hp_eq, hB_eq, ← ENNReal.ofReal_add hε₁_nn hε₂_nn,
    renyiDiv_le_ofReal_iff hα _ _ (add_nonneg hε₁_nn hε₂_nn)]
  set P₂ := p.bind fun x => (K x).bind fun y => _root_.PMF.pure (x, y)
  set Q₂ := q.bind fun x => (L x).bind fun y => _root_.PMF.pure (x, y)
  have hP₂ : (P₂ : X × Y → ℝ≥0∞) = fun z => p z.1 * K z.1 z.2 :=
    funext fun ⟨x, y⟩ => bind_pair_apply p K x y
  have hQ₂ : (Q₂ : X × Y → ℝ≥0∞) = fun z => q z.1 * L z.1 z.2 :=
    funext fun ⟨x, y⟩ => bind_pair_apply q L x y
  rw [hP₂, hQ₂,
    renyiMoment_mul_prod (p₁ := p) (q₁ := q) (p₂ := fun x y => K x y) (q₂ := fun x y => L x y)
      hα.le (fun x => q.apply_ne_top x) (fun x y => (L x).apply_ne_top y)]
  calc ∑' x, p x * (p x / q x) ^ (α - 1) * renyiMoment α (K x) (L x)
      ≤ ∑' x, p x * (p x / q x) ^ (α - 1) * ENNReal.ofReal (Real.exp ((α - 1) * ε₂)) := by
        refine tsum_le_tsum fun x => ?_
        classical
        by_cases hx : x ∈ p.support
        · refine mul_le_mul_right ?_ _
          exact (renyiDiv_le_ofReal_iff hα (K x) (L x) hε₂_nn).mp (hB_eq ▸ hKL x hx)
        · rw [(p.apply_eq_zero_iff x).mpr hx, zero_mul, zero_mul, zero_mul]
    _ = renyiMoment α p q * ENNReal.ofReal (Real.exp ((α - 1) * ε₂)) := by
        rw [ENNReal.tsum_mul_right, renyiMoment]
    _ ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε₁)) *
          ENNReal.ofReal (Real.exp ((α - 1) * ε₂)) := mul_le_mul_left hmom₁ _
    _ = ENNReal.ofReal (Real.exp ((α - 1) * (ε₁ + ε₂))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_add]

/-- **Conversion from Rényi divergence to hockey-stick divergence** [Mironov2017, Proposition 3]:
if `1 < α`, `0 ≤ ε`, `0 < δ`, and `renyiDiv α p q ≤ ofReal ε`, then
`hockeyStick (exp (ε + log (1 / δ) / (α - 1))) p q ≤ ofReal δ`. -/
theorem hockeyStick_le_of_renyiDiv_le {α ε δ : ℝ} (hα : 1 < α) (hε : 0 ≤ ε) (hδ : 0 < δ)
    {p q : PMF X} (h : renyiDiv α p q ≤ ENNReal.ofReal ε) :
    hockeyStick (ENNReal.ofReal (Real.exp (ε + Real.log (1 / δ) / (α - 1)))) p q ≤
      ENNReal.ofReal δ := by
  have ht : 0 < α - 1 := sub_pos.mpr hα
  have hmom : renyiMoment α p q ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε)) :=
    (renyiDiv_le_ofReal_iff hα p q hε).mp h
  calc hockeyStick (ENNReal.ofReal (Real.exp (ε + Real.log (1 / δ) / (α - 1)))) p q
      ≤ ENNReal.ofReal (Real.exp (-((α - 1) * (ε + Real.log (1 / δ) / (α - 1))))) *
          renyiMoment α p q :=
        hockeyStick_le_mul_rpow_tsum ht.le (ε + Real.log (1 / δ) / (α - 1)) p q
    _ ≤ ENNReal.ofReal (Real.exp (-((α - 1) * (ε + Real.log (1 / δ) / (α - 1))))) *
          ENNReal.ofReal (Real.exp ((α - 1) * ε)) := mul_le_mul_right hmom _
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        have hexp : -((α - 1) * (ε + Real.log (1 / δ) / (α - 1))) + (α - 1) * ε =
            Real.log δ := by
          rw [one_div, Real.log_inv]
          field_simp [ht.ne']
          ring
        rw [hexp, Real.exp_log hδ]

end PMF

end Cslib.Probability
