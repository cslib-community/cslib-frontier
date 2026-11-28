/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Planar quadrilateral and reflected-cone volume bounds

Lebesgue area upper bounds for the planar cross-straddling region
`planarRectSet b1 b2 rb vx vy ξ η` arising after orthogonal conditioning of a matched pair of
degree-`3` stars on their sum projections:

* `volume_planarRectSet_le_out`: global piecewise-trapezoid and reflected-cone upper bound valid
  for all `(ξ, η) ∈ ℝ × ℝ` whenever `detM = (1 - x1) * (1 - x2) - P > 0`.
* `volume_planarRectSet_le_in`: exact Cramer–shoelace quadrilateral identity on the interior cone
  `k2 * |ξ| ≤ |η| ∧ k1 * |η| ≤ |ξ|` (where the linear `O(|b1| + |b2|)` area terms cancel across
  quadrants to purely quadratic `O(|b1| * |b2|)` residuals), combined with
  `volume_planarRectSet_le_out` on the boundary cones `{|η| < k2 * |ξ|}` and `{|ξ| < k1 * |η|}`.
-/

public section

open MeasureTheory Real Set
open scoped ENNReal NNReal Interval

namespace Cslib.Circuits.Frontier.Gaussian.PairBound

/-- Planar cross-straddling fiber `{ (x, y) | |x| < |ξ - b1*rb*x + b1*vx*y| ∧
|y| < |η + b2*vy*x - b2*rb*y| }`. -/
@[expose] def planarRectSet (b1 b2 rb vx vy ξ η : ℝ) : Set (ℝ × ℝ) :=
  {p | |p.1| < |ξ - b1 * rb * p.1 + b1 * vx * p.2| ∧
       |p.2| < |η + b2 * vy * p.1 - b2 * rb * p.2|}

theorem measurableSet_planarRectSet_quad (b1 b2 rb vx vy : ℝ) :
    MeasurableSet {q : (ℝ × ℝ) × (ℝ × ℝ) |
      let (p, r) := q
      p ∈ planarRectSet b1 b2 rb vx vy r.1 r.2} := by
  dsimp [planarRectSet]
  have h1 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1| := by fun_prop
  have h2 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      |q.2.1 - b1 * rb * q.1.1 + b1 * vx * q.1.2| := by fun_prop
  have h3 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.2| := by fun_prop
  have h4 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      |q.2.2 + b2 * vy * q.1.1 - b2 * rb * q.1.2| := by fun_prop
  exact (measurableSet_lt h1 h2).inter (measurableSet_lt h3 h4)

theorem measurableSet_planarRectSet (b1 b2 rb vx vy ξ η : ℝ) :
    MeasurableSet (planarRectSet b1 b2 rb vx vy ξ η) := by
  dsimp [planarRectSet]
  have h1 : Measurable fun p : ℝ × ℝ => |p.1| := by fun_prop
  have h2 : Measurable fun p : ℝ × ℝ => |ξ - b1 * rb * p.1 + b1 * vx * p.2| := by fun_prop
  have h3 : Measurable fun p : ℝ × ℝ => |p.2| := by fun_prop
  have h4 : Measurable fun p : ℝ × ℝ => |η + b2 * vy * p.1 - b2 * rb * p.2| := by fun_prop
  exact (measurableSet_lt h1 h2).inter (measurableSet_lt h3 h4)

private theorem volume_between_linear_le {U₀ U₁ α₀ β₀ α₁ β₁ : ℝ} (hU : U₀ ≤ U₁)
    (hlin : ∀ u, U₀ ≤ u → u < U₁ → α₀ + β₀ * u ≤ α₁ + β₁ * u) :
    volume {p : ℝ × ℝ | U₀ ≤ p.1 ∧ p.1 < U₁ ∧
        α₀ + β₀ * p.1 ≤ p.2 ∧ p.2 < α₁ + β₁ * p.1} ≤
      ENNReal.ofReal ((α₁ - α₀) * (U₁ - U₀) + (β₁ - β₀) / 2 * (U₁ ^ 2 - U₀ ^ 2)) := by
  let S : Set (ℝ × ℝ) := {p | U₀ ≤ p.1 ∧ p.1 < U₁ ∧
    α₀ + β₀ * p.1 ≤ p.2 ∧ p.2 < α₁ + β₁ * p.1}
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_const).inter
        ((measurableSet_le (by fun_prop) measurable_snd).inter
          (measurableSet_lt measurable_snd (by fun_prop))))
  rw [Measure.volume_eq_prod, Measure.prod_apply hSm]
  let g : ℝ → ℝ := (Ico U₀ U₁).indicator fun u => (α₁ - α₀) + (β₁ - β₀) * u
  have hg_le (u : ℝ) : volume (Prod.mk u ⁻¹' S) ≤ ENNReal.ofReal (g u) := by
    dsimp only [g]
    by_cases hu : u ∈ Ico U₀ U₁
    · have hsub : Prod.mk u ⁻¹' S = Ico (α₀ + β₀ * u) (α₁ + β₁ * u) := by
        ext v; simp [S, hu.1, hu.2]
      rw [hsub, Real.volume_Ico, indicator_of_mem hu]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · have hemp : Prod.mk u ⁻¹' S = ∅ := by
        ext v; simp only [S, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro h; exact hu ⟨h.1, h.2.1⟩
      rw [hemp, measure_empty, indicator_of_notMem hu, ENNReal.ofReal_zero]
  have hg_nn : ∀ u, 0 ≤ g u := fun u => by
    dsimp only [g]
    by_cases hu : u ∈ Ico U₀ U₁
    · rw [indicator_of_mem hu]; linarith [hlin u hu.1 hu.2]
    · rw [indicator_of_notMem hu]
  have hcont : Continuous fun u : ℝ => (α₁ - α₀) + (β₁ - β₀) * u := by fun_prop
  have hg_int : Integrable g :=
    (integrable_indicator_iff measurableSet_Ico).mpr
      (hcont.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self)
  refine (lintegral_mono hg_le).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ hg_nn)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  dsimp only [g]
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hU]
  have hd : ∀ x ∈ uIcc U₀ U₁,
      HasDerivAt (fun y => (α₁ - α₀) * y + (β₁ - β₀) / 2 * y ^ 2)
        ((α₁ - α₀) + (β₁ - β₀) * x) x := fun x _ => by
    refine (((hasDerivAt_id x).const_mul (α₁ - α₀)).add
      ((hasDerivAt_pow 2 x).const_mul ((β₁ - β₀) / 2))).congr_deriv ?_
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable U₀ U₁)]
  ring

private theorem volume_between_linear_swap_le {V₀ V₁ α₀ β₀ α₁ β₁ : ℝ} (hV : V₀ ≤ V₁)
    (hlin : ∀ v, V₀ ≤ v → v < V₁ → α₀ + β₀ * v ≤ α₁ + β₁ * v) :
    volume {p : ℝ × ℝ | V₀ ≤ p.2 ∧ p.2 < V₁ ∧
        α₀ + β₀ * p.2 ≤ p.1 ∧ p.1 < α₁ + β₁ * p.2} ≤
      ENNReal.ofReal ((α₁ - α₀) * (V₁ - V₀) + (β₁ - β₀) / 2 * (V₁ ^ 2 - V₀ ^ 2)) := by
  have hpre : {p : ℝ × ℝ | V₀ ≤ p.2 ∧ p.2 < V₁ ∧
        α₀ + β₀ * p.2 ≤ p.1 ∧ p.1 < α₁ + β₁ * p.2} =
      Prod.swap ⁻¹' {q : ℝ × ℝ | V₀ ≤ q.1 ∧ q.1 < V₁ ∧
        α₀ + β₀ * q.1 ≤ q.2 ∧ q.2 < α₁ + β₁ * q.1} := rfl
  have hSm : MeasurableSet {q : ℝ × ℝ | V₀ ≤ q.1 ∧ q.1 < V₁ ∧
      α₀ + β₀ * q.1 ≤ q.2 ∧ q.2 < α₁ + β₁ * q.1} :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_const).inter
        ((measurableSet_le (by fun_prop) measurable_snd).inter
          (measurableSet_lt measurable_snd (by fun_prop))))
  rw [hpre, Measure.volume_eq_prod,
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).measure_preimage
      hSm.nullMeasurableSet,
    ← Measure.volume_eq_prod]
  exact volume_between_linear_le hV hlin

private theorem volume_origin_triangle_le {m00 m01 A u_star v_star : ℝ}
    (hm00 : 0 < m00) (hA_nn : 0 ≤ A) (hv_pos : 0 < v_star)
    (hA : m00 * u_star + m01 * v_star = A) :
    volume {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
        u_star * p.2 ≤ v_star * p.1 ∧ m00 * p.1 + m01 * p.2 < A} ≤
      ENNReal.ofReal (A * v_star / (2 * m00)) := by
  rcases eq_or_lt_of_le hA_nn with rfl | hA_pos
  · have hemp : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
        u_star * p.2 ≤ v_star * p.1 ∧ m00 * p.1 + m01 * p.2 < 0} = ∅ := by
      ext p; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨hp1, hp2, hdiag, hlt⟩
      have h1 : m00 * (u_star * p.2) ≤ m00 * (v_star * p.1) :=
        mul_le_mul_of_nonneg_left hdiag hm00.le
      have h2 : v_star * (m00 * p.1 + m01 * p.2) < 0 :=
        mul_neg_of_pos_of_neg hv_pos hlt
      nlinarith
    rw [hemp, measure_empty]; simp
  · have hsub : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
        u_star * p.2 ≤ v_star * p.1 ∧ m00 * p.1 + m01 * p.2 < A} ⊆
        {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 < v_star ∧
          0 + u_star / v_star * p.2 ≤ p.1 ∧ p.1 < A / m00 + (-m01 / m00) * p.2} := by
      rintro p ⟨_, hp2, hdiag, hlt⟩
      have hp2_lt : p.2 < v_star := by
        have h1 : m00 * (u_star * p.2) ≤ m00 * (v_star * p.1) :=
          mul_le_mul_of_nonneg_left hdiag hm00.le
        have h2 : v_star * (m00 * p.1 + m01 * p.2) < v_star * A :=
          mul_lt_mul_of_pos_left hlt hv_pos
        have h3 : A * p.2 < A * v_star := by nlinarith
        exact lt_of_mul_lt_mul_left h3 hA_pos.le
      refine ⟨hp2, hp2_lt, ?_, ?_⟩
      · rw [zero_add, div_mul_eq_mul_div, div_le_iff₀ hv_pos]; linarith
      · rw [show A / m00 + -m01 / m00 * p.2 = (A - m01 * p.2) / m00 by ring, lt_div_iff₀ hm00]
        linarith
    refine (measure_mono hsub).trans ((volume_between_linear_swap_le hv_pos.le ?_).trans_eq ?_)
    · intro v _ hv1
      have hid : A / m00 + -m01 / m00 * v - (0 + u_star / v_star * v) =
          A * (v_star - v) / (m00 * v_star) := by
        rw [← hA]; field_simp [hm00.ne', hv_pos.ne']; ring
      have hpos : 0 ≤ A * (v_star - v) / (m00 * v_star) :=
        div_nonneg (mul_nonneg hA_pos.le (by linarith)) (by positivity)
      linarith
    · congr 1
      rw [← hA]; field_simp [hm00.ne', hv_pos.ne']; ring

private theorem volume_quad_shoelace_le {m00 m01 m10 m11 A B : ℝ}
    (hm00 : 0 < m00) (hm11 : 0 < m11) (hdM : 0 < m00 * m11 - m01 * m10)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu_nn : 0 ≤ (m11 * A - m01 * B) / (m00 * m11 - m01 * m10))
    (hv_nn : 0 ≤ (m00 * B - m10 * A) / (m00 * m11 - m01 * m10)) :
    volume {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
        m00 * p.1 + m01 * p.2 < A ∧ m10 * p.1 + m11 * p.2 < B} ≤
      ENNReal.ofReal (A * B / (m00 * m11 - m01 * m10) -
        m10 * A ^ 2 / (2 * m00 * (m00 * m11 - m01 * m10)) -
        m01 * B ^ 2 / (2 * m11 * (m00 * m11 - m01 * m10))) := by
  set dM := m00 * m11 - m01 * m10
  set u_s := (m11 * A - m01 * B) / dM
  set v_s := (m00 * B - m10 * A) / dM
  have hdM_ne : m00 * m11 - m01 * m10 ≠ 0 := hdM.ne'
  have hdM_ne2 : m11 * m00 - m10 * m01 ≠ 0 := by linarith
  have hcram1 : m00 * u_s + m01 * v_s = A := by
    dsimp [u_s, v_s, dM]; field_simp [hdM_ne]; ring
  have hcram2 : m11 * v_s + m10 * u_s = B := by
    dsimp [u_s, v_s, dM]; field_simp [hdM_ne2]; ring
  have hshoelace : A * v_s / (2 * m00) + B * u_s / (2 * m11) =
      A * B / dM - m10 * A ^ 2 / (2 * m00 * dM) - m01 * B ^ 2 / (2 * m11 * dM) := by
    dsimp [u_s, v_s]; field_simp [hm00.ne', hm11.ne', hdM.ne']; ring
  let M : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
    m00 * p.1 + m01 * p.2 < A ∧ m10 * p.1 + m11 * p.2 < B}
  change volume M ≤ _
  have hQm : MeasurableSet {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧
      v_s * q.2 ≤ u_s * q.1 ∧ m11 * q.1 + m10 * q.2 < B} := by
    have hf1 : Measurable fun q : ℝ × ℝ => v_s * q.2 := by fun_prop
    have hf2 : Measurable fun q : ℝ × ℝ => u_s * q.1 := by fun_prop
    have hf3 : Measurable fun q : ℝ × ℝ => m11 * q.1 + m10 * q.2 := by fun_prop
    exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        ((measurableSet_le hf1 hf2).inter (measurableSet_lt hf3 measurable_const)))
  rcases eq_or_lt_of_le hv_nn with hv0 | hv_pos
  · rcases eq_or_lt_of_le hu_nn with hu0 | hu_pos
    · have hA0 : A = 0 := by rw [← hcram1, ← hu0, ← hv0]; ring
      have hB0 : B = 0 := by rw [← hcram2, ← hu0, ← hv0]; ring
      have hemp : M = ∅ := by
        ext p; simp only [M, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hp1, hp2, h1, h2⟩
        rw [hA0] at h1; rw [hB0] at h2
        rcases le_or_gt 0 m01 with hm01 | hm01
        · nlinarith
        · have : (m00 * m11 - m01 * m10) * p.1 < 0 := by nlinarith
          nlinarith [show 0 < m00 * m11 - m01 * m10 from hdM]
      rw [hemp, measure_empty]; simp
    · have hsub : M ⊆ Prod.swap ⁻¹' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧
          v_s * q.2 ≤ u_s * q.1 ∧ m11 * q.1 + m10 * q.2 < B} := by
        rintro p ⟨hp1, hp2, _, h2⟩
        refine ⟨hp2, hp1, ?_, by change m11 * p.2 + m10 * p.1 < B; linarith⟩
        change v_s * p.1 ≤ u_s * p.2
        rw [← hv0, zero_mul]; exact mul_nonneg hu_pos.le hp2
      refine (measure_mono hsub).trans ?_
      rw [Measure.volume_eq_prod,
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).measure_preimage
          hQm.nullMeasurableSet,
        ← Measure.volume_eq_prod]
      refine (volume_origin_triangle_le hm11 hB hu_pos hcram2).trans_eq ?_
      rw [← hshoelace, ← hv0, mul_zero, zero_div, zero_add]
  · rcases eq_or_lt_of_le hu_nn with hu0 | hu_pos
    · have hsub : M ⊆ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
          u_s * p.2 ≤ v_s * p.1 ∧ m00 * p.1 + m01 * p.2 < A} := by
        rintro p ⟨hp1, hp2, h1, _⟩
        refine ⟨hp1, hp2, ?_, h1⟩
        rw [← hu0, zero_mul]; exact mul_nonneg hv_pos.le hp1
      refine (measure_mono hsub).trans
        ((volume_origin_triangle_le hm00 hA hv_pos hcram1).trans_eq ?_)
      rw [← hshoelace, ← hu0, mul_zero, zero_div, add_zero]
    · let T₁ : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
        u_s * p.2 ≤ v_s * p.1 ∧ m00 * p.1 + m01 * p.2 < A}
      let T₂ : Set (ℝ × ℝ) := Prod.swap ⁻¹' {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧
        v_s * q.2 ≤ u_s * q.1 ∧ m11 * q.1 + m10 * q.2 < B}
      have hsub : M ⊆ T₁ ∪ T₂ := fun p ⟨hp1, hp2, h1, h2⟩ => by
        rcases le_total (u_s * p.2) (v_s * p.1) with hle | hle
        · exact Or.inl ⟨hp1, hp2, hle, h1⟩
        · exact Or.inr ⟨hp2, hp1, hle, by change m11 * p.2 + m10 * p.1 < B; linarith⟩
      have hvT₁ := volume_origin_triangle_le hm00 hA hv_pos hcram1
      have hvT₂ : volume T₂ ≤ ENNReal.ofReal (B * u_s / (2 * m11)) := by
        dsimp only [T₂]
        rw [Measure.volume_eq_prod,
          (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
            (ν := volume)).measure_preimage hQm.nullMeasurableSet,
          ← Measure.volume_eq_prod]
        exact volume_origin_triangle_le hm11 hB hu_pos hcram2
      refine (measure_mono hsub).trans ((measure_union_le T₁ T₂).trans ?_)
      refine (add_le_add hvT₁ hvT₂).trans_eq ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), hshoelace]

private def quadrantRectSet (m00 m00p m01 m10 m11 m11p A B : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
    (m00 * p.1 + m01 * p.2 < A ∨ m00p * p.1 - m01 * p.2 < -A) ∧
    (m10 * p.1 + m11 * p.2 < B ∨ -m10 * p.1 + m11p * p.2 < -B)}

private theorem measurableSet_quadrantRectSet (m00 m00p m01 m10 m11 m11p A B : ℝ) :
    MeasurableSet (quadrantRectSet m00 m00p m01 m10 m11 m11p A B) := by
  dsimp [quadrantRectSet]
  have hf1 : Measurable fun p : ℝ × ℝ => m00 * p.1 + m01 * p.2 := by fun_prop
  have hf2 : Measurable fun p : ℝ × ℝ => m00p * p.1 - m01 * p.2 := by fun_prop
  have hf3 : Measurable fun p : ℝ × ℝ => m10 * p.1 + m11 * p.2 := by fun_prop
  have hf4 : Measurable fun p : ℝ × ℝ => -m10 * p.1 + m11p * p.2 := by fun_prop
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (((measurableSet_lt hf1 measurable_const).union (measurableSet_lt hf2 measurable_const)).inter
        ((measurableSet_lt hf3 measurable_const).union (measurableSet_lt hf4 measurable_const))))

private noncomputable def quadOutTerm (m00 m00p m01 m10 m11 m11p A B : ℝ) : ℝ :=
  (if 0 ≤ m01 ∧ 0 ≤ m10 then A * B / (m00 * m11)
   else if 0 ≤ m01 ∧ m10 < 0 then
     A * B / (m00 * m11) + (-m10) * A ^ 2 / (2 * m11 * m00 ^ 2)
   else if m01 < 0 ∧ 0 ≤ m10 then
     A * B / (m00 * m11) + (-m01) * B ^ 2 / (2 * m00 * m11 ^ 2)
   else
     A * B / (m00 * m11 - m01 * m10) +
       (-m10) * A ^ 2 / (2 * m00 * (m00 * m11 - m01 * m10)) +
       (-m01) * B ^ 2 / (2 * m11 * (m00 * m11 - m01 * m10))) +
  (if 0 < m10 then
     if 0 ≤ m01 then m10 * A ^ 2 / (2 * m11p * m00 ^ 2)
     else m10 * m11p * A ^ 2 / (2 * (m00 * m11p + m01 * m10) ^ 2)
   else 0) +
  (if 0 < m01 then
     if 0 ≤ m10 then m01 * B ^ 2 / (2 * m00p * m11 ^ 2)
     else m01 * m00p * B ^ 2 / (2 * (m00p * m11 + m01 * m10) ^ 2)
   else 0)

private def mixedRegion (a b c d A B : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ a * p.1 + b * p.2 < A ∧ -c * p.1 + d * p.2 < -B}

private theorem volume_mixedRegion_le {a b c d A B : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hdet : 0 < a * d + b * c) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    volume (mixedRegion a b c d A B) ≤ ENNReal.ofReal (if 0 < c then
      if 0 ≤ b then c * A ^ 2 / (2 * d * a ^ 2)
      else c * d * A ^ 2 / (2 * (a * d + b * c) ^ 2) else 0) := by
  by_cases hc : 0 < c
  · simp only [hc, ↓reduceIte]
    have triangle {U : ℝ} (hU : 0 ≤ U) (hcut : ∀ p ∈ mixedRegion a b c d A B, p.1 < U) :
        volume (mixedRegion a b c d A B) ≤ ENNReal.ofReal (c / d * U ^ 2 / 2) := by
      have hsub : mixedRegion a b c d A B ⊆ {p | 0 ≤ p.1 ∧ p.1 < U ∧
          0 + 0 * p.1 ≤ p.2 ∧ p.2 < 0 + (c / d) * p.1} := by
        intro p hp
        have hpU := hcut p hp
        obtain ⟨hp1, hp2, _, h2⟩ := hp
        refine ⟨hp1, hpU, by linarith, ?_⟩
        rw [zero_add, div_mul_eq_mul_div, lt_div_iff₀ hd]
        linarith
      refine (measure_mono hsub).trans ((volume_between_linear_le hU ?_).trans_eq ?_)
      · intro u hu _
        simpa only [zero_mul, add_zero, zero_add] using mul_nonneg (div_nonneg hc.le hd.le) hu
      · congr 1; ring
    by_cases hb : 0 ≤ b
    · simp only [hb, ↓reduceIte]
      refine (triangle (div_nonneg hA ha.le) ?_).trans_eq ?_
      · rintro p ⟨_, hp2, h1, _⟩
        exact (lt_div_iff₀ ha).mpr (by nlinarith)
      · congr 1; field_simp [ha.ne', hd.ne']
    · simp only [hb, ↓reduceIte]
      refine (triangle (div_nonneg (mul_nonneg hd.le hA) hdet.le) ?_).trans_eq ?_
      · rintro p ⟨_, _, h1, h2⟩
        exact (lt_div_iff₀ hdet).mpr (by nlinarith [not_le.mp hb])
      · congr 1; field_simp [hd.ne', hdet.ne']
  · simp only [hc, ↓reduceIte]
    have hemp : mixedRegion a b c d A B = ∅ := by
      ext p; simp only [mixedRegion, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨hp1, hp2, _, h2⟩; nlinarith [not_lt.mp hc]
    rw [hemp, measure_empty, ENNReal.ofReal_zero]

private theorem volume_quadrantRectSet_le_out {m00 m00p : ℝ} (m01 m10 : ℝ) {m11 m11p A B : ℝ}
    (hm00 : 0 < m00) (hm00p : 0 < m00p) (hm11 : 0 < m11) (hm11p : 0 < m11p)
    (hdM : 0 < m00 * m11 - m01 * m10)
    (hdN2 : 0 < m00 * m11p + m01 * m10) (hdN1 : 0 < m00p * m11 + m01 * m10)
    (hdNN : 0 < m00p * m11p - m01 * m10) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    volume (quadrantRectSet m00 m00p m01 m10 m11 m11p A B) ≤
      ENNReal.ofReal (quadOutTerm m00 m00p m01 m10 m11 m11p A B) := by
  let MM : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
    m00 * p.1 + m01 * p.2 < A ∧ m10 * p.1 + m11 * p.2 < B}
  let MN := mixedRegion m00 m01 m10 m11p A B
  let NM := Prod.swap ⁻¹' mixedRegion m11 m10 m01 m00p B A
  have hcover : quadrantRectSet m00 m00p m01 m10 m11 m11p A B ⊆ (MM ∪ MN) ∪ NM := by
    rintro p ⟨hp1, hp2, h1 | h1, h2 | h2⟩
    · exact Or.inl (Or.inl ⟨hp1, hp2, h1, h2⟩)
    · exact Or.inl (Or.inr ⟨hp1, hp2, h1, h2⟩)
    · apply Or.inr
      change 0 ≤ p.2 ∧ 0 ≤ p.1 ∧ m11 * p.2 + m10 * p.1 < B ∧ -m01 * p.2 + m00p * p.1 < -A
      exact ⟨hp2, hp1, by linarith, by linarith⟩
    · exfalso
      have hp10 : 0 < m01 := by
        by_contra hc; have : m01 ≤ 0 := not_lt.mp hc; nlinarith
      have : (m00p * m11p - m01 * m10) * p.1 + m11p * A + m01 * B < 0 := by nlinarith
      nlinarith
  have hvMM : volume MM ≤ ENNReal.ofReal (
      if 0 ≤ m01 ∧ 0 ≤ m10 then A * B / (m00 * m11)
      else if 0 ≤ m01 ∧ m10 < 0 then
        A * B / (m00 * m11) + (-m10) * A ^ 2 / (2 * m11 * m00 ^ 2)
      else if m01 < 0 ∧ 0 ≤ m10 then
        A * B / (m00 * m11) + (-m01) * B ^ 2 / (2 * m00 * m11 ^ 2)
      else
        A * B / (m00 * m11 - m01 * m10) +
          (-m10) * A ^ 2 / (2 * m00 * (m00 * m11 - m01 * m10)) +
          (-m01) * B ^ 2 / (2 * m11 * (m00 * m11 - m01 * m10))) := by
    rcases le_or_gt 0 m01 with hm01 | hm01 <;> rcases le_or_gt 0 m10 with hm10 | hm10
    · simp only [hm01, hm10, and_self, ↓reduceIte]
      have hsub : MM ⊆ {p | 0 ≤ p.1 ∧ p.1 < A / m00 ∧ 0 + 0 * p.1 ≤ p.2 ∧
          p.2 < B / m11 + 0 * p.1} := fun p ⟨hp1, hp2, h1, h2⟩ =>
        ⟨hp1, (lt_div_iff₀ hm00).mpr (by nlinarith), by linarith,
          by rw [zero_mul, add_zero, lt_div_iff₀ hm11]; nlinarith⟩
      refine (measure_mono hsub).trans
        ((volume_between_linear_le (div_nonneg hA hm00.le) fun _ _ _ => ?_).trans_eq ?_)
      · linarith [div_nonneg hB hm11.le]
      · congr 1; ring
    · simp only [hm01, not_le.mpr hm10, hm10, and_self, and_false, ↓reduceIte]
      have hsub : MM ⊆ {p | 0 ≤ p.1 ∧ p.1 < A / m00 ∧ 0 + 0 * p.1 ≤ p.2 ∧
          p.2 < B / m11 + (-m10 / m11) * p.1} := fun p ⟨hp1, hp2, h1, h2⟩ =>
        ⟨hp1, (lt_div_iff₀ hm00).mpr (by nlinarith), by linarith, by
          rw [show B / m11 + -m10 / m11 * p.1 = (B - m10 * p.1) / m11 by ring, lt_div_iff₀ hm11]
          linarith⟩
      refine (measure_mono hsub).trans
        ((volume_between_linear_le (div_nonneg hA hm00.le) fun u hu0 _ => ?_).trans_eq ?_)
      · rw [zero_mul, add_zero]
        exact add_nonneg (div_nonneg hB hm11.le)
          (mul_nonneg (div_nonneg (by linarith) hm11.le) hu0)
      · congr 1; field_simp [hm00.ne', hm11.ne']; ring
    · simp only [not_le.mpr hm01, hm01, hm10, and_self, false_and, ↓reduceIte]
      have hsub : MM ⊆ {p | 0 ≤ p.2 ∧ p.2 < B / m11 ∧ 0 + 0 * p.2 ≤ p.1 ∧
          p.1 < A / m00 + (-m01 / m00) * p.2} := fun p ⟨hp1, hp2, h1, h2⟩ =>
        ⟨hp2, (lt_div_iff₀ hm11).mpr (by nlinarith), by linarith, by
          rw [show A / m00 + -m01 / m00 * p.2 = (A - m01 * p.2) / m00 by ring, lt_div_iff₀ hm00]
          linarith⟩
      refine (measure_mono hsub).trans
        ((volume_between_linear_swap_le (div_nonneg hB hm11.le) fun v hv0 _ => ?_).trans_eq ?_)
      · rw [zero_mul, add_zero]
        exact add_nonneg (div_nonneg hA hm00.le)
          (mul_nonneg (div_nonneg (by linarith) hm00.le) hv0)
      · congr 1; field_simp [hm00.ne', hm11.ne']; ring
    · simp only [not_le.mpr hm01, not_le.mpr hm10, false_and, and_false, ↓reduceIte]
      have hu_nn : 0 ≤ (m11 * A - m01 * B) / (m00 * m11 - m01 * m10) :=
        div_nonneg (by nlinarith) hdM.le
      have hv_nn : 0 ≤ (m00 * B - m10 * A) / (m00 * m11 - m01 * m10) :=
        div_nonneg (by nlinarith) hdM.le
      refine (volume_quad_shoelace_le hm00 hm11 hdM hA hB hu_nn hv_nn).trans_eq ?_
      congr 1; ring
  have hvMN := volume_mixedRegion_le hm00 hm11p hdN2 hA hB
  have hvNM : volume NM ≤ ENNReal.ofReal (if 0 < m01 then
      if 0 ≤ m10 then m01 * B ^ 2 / (2 * m00p * m11 ^ 2)
      else m01 * m00p * B ^ 2 / (2 * (m00p * m11 + m01 * m10) ^ 2) else 0) := by
    dsimp only [NM]
    rw [Measure.volume_eq_prod, Measure.measurePreserving_swap.measure_preimage_emb
      MeasurableEquiv.prodComm.measurableEmbedding, ← Measure.volume_eq_prod]
    simpa only [mul_comm m11 m00p, mul_comm m10 m01] using
      volume_mixedRegion_le hm11 hm00p (b := m10) (c := m01) (by linarith) hB hA
  have hnn1 : 0 ≤ (if 0 ≤ m01 ∧ 0 ≤ m10 then A * B / (m00 * m11)
      else if 0 ≤ m01 ∧ m10 < 0 then
        A * B / (m00 * m11) + (-m10) * A ^ 2 / (2 * m11 * m00 ^ 2)
      else if m01 < 0 ∧ 0 ≤ m10 then
        A * B / (m00 * m11) + (-m01) * B ^ 2 / (2 * m00 * m11 ^ 2)
      else
        A * B / (m00 * m11 - m01 * m10) +
          (-m10) * A ^ 2 / (2 * m00 * (m00 * m11 - m01 * m10)) +
          (-m01) * B ^ 2 / (2 * m11 * (m00 * m11 - m01 * m10))) := by
    split_ifs with h1 h2 h3
    · positivity
    · exact add_nonneg (by positivity) (div_nonneg (by nlinarith [h2.2]) (by positivity))
    · exact add_nonneg (by positivity) (div_nonneg (by nlinarith [h3.1]) (by positivity))
    · have hm01 : m01 < 0 := by
        by_contra h
        exact h2 ⟨not_lt.mp h, by by_contra h'; exact h1 ⟨not_lt.mp h, not_lt.mp h'⟩⟩
      have hm10 : m10 < 0 := by by_contra h; exact h3 ⟨hm01, not_lt.mp h⟩
      exact add_nonneg (add_nonneg (by positivity)
        (div_nonneg (by nlinarith) (by positivity)))
        (div_nonneg (by nlinarith) (by positivity))
  have hnn2 : 0 ≤ (if 0 < m10 then
      if 0 ≤ m01 then m10 * A ^ 2 / (2 * m11p * m00 ^ 2)
      else m10 * m11p * A ^ 2 / (2 * (m00 * m11p + m01 * m10) ^ 2)
    else 0) := by split_ifs <;> positivity
  have hnn3 : 0 ≤ (if 0 < m01 then
      if 0 ≤ m10 then m01 * B ^ 2 / (2 * m00p * m11 ^ 2)
      else m01 * m00p * B ^ 2 / (2 * (m00p * m11 + m01 * m10) ^ 2)
    else 0) := by split_ifs <;> positivity
  have hunion : volume ((MM ∪ MN) ∪ NM) ≤ volume MM + volume MN + volume NM :=
    (measure_union_le (MM ∪ MN) NM).trans (add_le_add (measure_union_le MM MN) le_rfl)
  refine (measure_mono hcover).trans (hunion.trans ?_)
  refine (add_le_add (add_le_add hvMM hvMN) hvNM).trans_eq ?_
  unfold quadOutTerm
  rw [← ENNReal.ofReal_add hnn1 hnn2, ← ENNReal.ofReal_add (add_nonneg hnn1 hnn2) hnn3]

/-! ### Four-quadrant rational assembly -/

/-- Constant rational term in the four-quadrant planar rectangle volume upper bound. -/
@[expose] noncomputable def pairCAB (x1 x2 P detM : ℝ) : ℝ :=
  4 / ((1 - x1 ^ 2) * (1 - x2 ^ 2)) + P / ((1 - x1) * (1 - x2) * detM)

/-- Positive-branch linear rational coefficient in the planar rectangle volume bound. -/
@[expose] noncomputable def pairCxp (u2 vy x1 x2 detM : ℝ) : ℝ :=
  u2 * vy / 2 * (1 / ((1 + x2) * (1 - x1) ^ 2) + 1 / ((1 + x1) ^ 2 * (1 - x2)) +
    (1 - x2) / detM ^ 2 + 1 / (1 + x1))

/-- Negative-branch linear rational coefficient in the planar rectangle volume bound. -/
@[expose] noncomputable def pairCxm (u2 vy x1 x2 detM : ℝ) : ℝ :=
  u2 * vy / 2 * (1 / ((1 - x2) * (1 + x1) ^ 2) + 1 / ((1 - x1) ^ 2 * (1 + x2)) +
    1 / (1 + x2) + 1 / ((1 - x1) * detM))

/-- Envelope `max pairCxp pairCxm` of the linear rational planar volume coefficients. -/
@[expose] noncomputable def pairCxMax (u2 vy x1 x2 detM : ℝ) : ℝ :=
  max (pairCxp u2 vy x1 x2 detM) (pairCxm u2 vy x1 x2 detM)

/-- Positive quadratic denominator `(1 + b1 * rb)^2 - b2^2 * (rb - b1 * D)^2`. -/
@[expose] noncomputable def pairQp (b1 b2 rb D : ℝ) : ℝ :=
  (1 + b1 * rb) ^ 2 - b2 ^ 2 * (rb - b1 * D) ^ 2

/-- Negative quadratic denominator `(1 - b1 * rb)^2 - b2^2 * (rb + b1 * D)^2`. -/
@[expose] noncomputable def pairQm (b1 b2 rb D : ℝ) : ℝ :=
  (1 - b1 * rb) ^ 2 - b2 ^ 2 * (rb + b1 * D) ^ 2

/-- Bilinear cross-term rational coefficient in the planar rectangle volume bound. -/
@[expose] noncomputable def pairCxe (b1 b2 rb D : ℝ) : ℝ :=
  2 * (1 + b1 * rb) / pairQp b1 b2 rb D + 2 * (1 - b1 * rb) / pairQm b1 b2 rb D

/-- Quadratic `ξ^2` rational coefficient in the planar rectangle volume bound. -/
@[expose] noncomputable def pairAbsCx2 (b1 b2 rb vy D : ℝ) : ℝ :=
  4 * |b1| * |b2| * rb * vy * (1 + b2 ^ 2 * D) / (pairQp b1 b2 rb D * pairQm b1 b2 rb D)

/-- Quadratic `η^2` rational coefficient in the planar rectangle volume bound. -/
@[expose] noncomputable def pairAbsCe2 (b1 b2 rb vx D : ℝ) : ℝ :=
  4 * |b1| * |b2| * rb * vx * (1 + b1 ^ 2 * D) / (pairQp b1 b2 rb D * pairQm b1 b2 rb D)

private theorem volume_planarRectSet_neg_b (b1 b2 rb vx vy ξ η : ℝ) :
    volume (planarRectSet b1 b2 rb vx vy ξ η) =
      volume (planarRectSet (-b1) (-b2) rb vx vy ξ η) := by
  have hmp : MeasurePreserving (Prod.map (@Neg.neg ℝ _) (@Neg.neg ℝ _)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg volume).prod (Measure.measurePreserving_neg volume)
  have hpre : planarRectSet b1 b2 rb vx vy ξ η =
      (Prod.map (@Neg.neg ℝ _) (@Neg.neg ℝ _)) ⁻¹'
        planarRectSet (-b1) (-b2) rb vx vy ξ η := by
    ext ⟨x, y⟩
    simp only [planarRectSet, mem_ofPred_eq, mem_preimage, Prod.map_apply, abs_neg]
    ring_nf
  rw [hpre, hmp.measure_preimage (measurableSet_planarRectSet _ _ _ _ _ _ _).nullMeasurableSet]

private theorem volume_planarRectSet_neg_xi (b1 b2 rb vx vy ξ η : ℝ) :
    volume (planarRectSet b1 b2 rb vx vy ξ η) =
      volume (planarRectSet b1 b2 rb vx vy (-ξ) (-η)) := by
  have hmp : MeasurePreserving (Prod.map (@Neg.neg ℝ _) (@Neg.neg ℝ _)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg volume).prod (Measure.measurePreserving_neg volume)
  have hpre : planarRectSet b1 b2 rb vx vy ξ η =
      (Prod.map (@Neg.neg ℝ _) (@Neg.neg ℝ _)) ⁻¹'
        planarRectSet b1 b2 rb vx vy (-ξ) (-η) := by
    ext ⟨x, y⟩
    simp only [planarRectSet, mem_ofPred_eq, mem_preimage, Prod.map_apply, abs_neg]
    have h1 : |ξ - b1 * rb * x + b1 * vx * y| = |-ξ - b1 * rb * -x + b1 * vx * -y| := by
      rw [← abs_neg]; congr 1; ring
    have h2 : |η + b2 * vy * x - b2 * rb * y| = |-η + b2 * vy * -x - b2 * rb * -y| := by
      rw [← abs_neg]; congr 1; ring
    rw [h1, h2]
  rw [hpre, hmp.measure_preimage (measurableSet_planarRectSet _ _ _ _ _ _ _).nullMeasurableSet]

private theorem planarRectSet_neg_eta (b1 b2 rb vx vy ξ η : ℝ) :
    planarRectSet b1 b2 rb vx vy ξ η = planarRectSet b1 (-b2) rb vx vy ξ (-η) := by
  ext ⟨x, y⟩
  simp only [planarRectSet, mem_ofPred_eq]
  have h2 : |η + b2 * vy * x - b2 * rb * y| = |-η + -b2 * vy * x - -b2 * rb * y| := by
    rw [← abs_neg]; congr 1; ring
  rw [h2]

private theorem volume_planarRectSet_eq_sign (b1 b2 rb vx vy ξ η : ℝ) :
    (0 ≤ b1 * b2 * ξ * η →
      volume (planarRectSet b1 b2 rb vx vy ξ η) =
        volume (planarRectSet |b1| |b2| rb vx vy |ξ| |η|)) ∧
    (b1 * b2 * ξ * η ≤ 0 →
      volume (planarRectSet b1 b2 rb vx vy ξ η) =
        volume (planarRectSet |b1| (-|b2|) rb vx vy |ξ| |η|)) := by
  suffices hmain : ∀ (c1 c2 z1 z2 : ℝ), 0 ≤ c1 → 0 ≤ z1 → 0 ≤ z2 →
      (0 ≤ c1 * c2 * z1 * z2 →
        volume (planarRectSet c1 c2 rb vx vy z1 z2) =
          volume (planarRectSet c1 |c2| rb vx vy z1 z2)) ∧
      (c1 * c2 * z1 * z2 ≤ 0 →
        volume (planarRectSet c1 c2 rb vx vy z1 z2) =
          volume (planarRectSet c1 (-|c2|) rb vx vy z1 z2)) by
    have hb : ∃ c1 c2, 0 ≤ c1 ∧ c1 = |b1| ∧ |c2| = |b2| ∧ c1 * c2 = b1 * b2 ∧
        volume (planarRectSet b1 b2 rb vx vy ξ η) =
          volume (planarRectSet c1 c2 rb vx vy ξ η) := by
      rcases le_or_gt 0 b1 with hb1 | hb1
      · exact ⟨b1, b2, hb1, (abs_of_nonneg hb1).symm, rfl, rfl, rfl⟩
      · exact ⟨-b1, -b2, by linarith, by rw [abs_of_neg hb1], abs_neg b2, by ring,
          volume_planarRectSet_neg_b b1 b2 rb vx vy ξ η⟩
    obtain ⟨c1, c2, hc1, hc1_abs, hc2_abs, hprod_b, hv_b⟩ := hb
    have hz : ∃ c2' z1 z2, 0 ≤ z1 ∧ 0 ≤ z2 ∧ z1 = |ξ| ∧ z2 = |η| ∧ |c2'| = |c2| ∧
        c2' * z1 * z2 = c2 * ξ * η ∧
        volume (planarRectSet c1 c2 rb vx vy ξ η) =
          volume (planarRectSet c1 c2' rb vx vy z1 z2) := by
      rcases le_or_gt 0 ξ with hξ | hξ <;> rcases le_or_gt 0 η with hη | hη
      · exact ⟨c2, ξ, η, hξ, hη, (abs_of_nonneg hξ).symm, (abs_of_nonneg hη).symm, rfl, rfl, rfl⟩
      · exact ⟨-c2, ξ, -η, hξ, by linarith, (abs_of_nonneg hξ).symm, by rw [abs_of_neg hη],
          abs_neg c2, by ring, by rw [planarRectSet_neg_eta]⟩
      · refine ⟨-c2, -ξ, η, by linarith, hη, by rw [abs_of_neg hξ], (abs_of_nonneg hη).symm,
          abs_neg c2, by ring, ?_⟩
        rw [volume_planarRectSet_neg_xi, planarRectSet_neg_eta, neg_neg]
      · exact ⟨c2, -ξ, -η, by linarith, by linarith, by rw [abs_of_neg hξ],
          by rw [abs_of_neg hη], rfl, by ring, volume_planarRectSet_neg_xi c1 c2 rb vx vy ξ η⟩
    obtain ⟨c2', z1, z2, hz1, hz2, hz1_abs, hz2_abs, hc2'_abs, hprod_z, hv_z⟩ := hz
    have hprod_all : c1 * c2' * z1 * z2 = b1 * b2 * ξ * η := by
      calc c1 * c2' * z1 * z2 = c1 * (c2' * z1 * z2) := by ring
        _ = c1 * (c2 * ξ * η) := by rw [hprod_z]
        _ = (c1 * c2) * ξ * η := by ring
        _ = b1 * b2 * ξ * η := by rw [hprod_b]
    obtain ⟨hp, hm⟩ := hmain c1 c2' z1 z2 hc1 hz1 hz2
    rw [hv_b, hv_z, ← hc1_abs, ← hz1_abs, ← hz2_abs, ← hc2_abs, ← hc2'_abs, ← hprod_all]
    exact ⟨hp, hm⟩
  intro c1 c2 z1 z2 hc1 hz1 hz2
  have hflip_zero (h0 : c1 * z1 * z2 = 0) :
      volume (planarRectSet c1 c2 rb vx vy z1 z2) =
        volume (planarRectSet c1 (-c2) rb vx vy z1 z2) := by
    rcases mul_eq_zero.mp h0 with h12 | hz2_0
    · rcases mul_eq_zero.mp h12 with rfl | rfl
      · simpa using volume_planarRectSet_neg_b 0 c2 rb vx vy z1 z2
      · rw [volume_planarRectSet_neg_xi, planarRectSet_neg_eta, neg_zero, neg_neg]
    · subst hz2_0; rw [planarRectSet_neg_eta, neg_zero]
  refine ⟨fun hp => ?_, fun hm => ?_⟩
  · rcases le_or_gt 0 c2 with hc2 | hc2
    · rw [abs_of_nonneg hc2]
    · have h0 : c1 * z1 * z2 = 0 := by
        have hnp : c1 * z1 * z2 * c2 ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg hc1 hz1) hz2) hc2.le
        have hge : 0 ≤ c1 * z1 * z2 * c2 := by
          linarith [show c1 * z1 * z2 * c2 = c1 * c2 * z1 * z2 by ring]
        exact (mul_eq_zero.mp (le_antisymm hnp hge)).resolve_right hc2.ne
      rw [abs_of_neg hc2, hflip_zero h0]
  · rcases le_or_gt c2 0 with hc2 | hc2
    · rw [abs_of_nonpos hc2, neg_neg]
    · have h0 : c1 * z1 * z2 = 0 := by
        have hnn : 0 ≤ c1 * z1 * z2 * c2 :=
          mul_nonneg (mul_nonneg (mul_nonneg hc1 hz1) hz2) hc2.le
        have hle : c1 * z1 * z2 * c2 ≤ 0 := by
          linarith [show c1 * z1 * z2 * c2 = c1 * c2 * z1 * z2 by ring]
        exact (mul_eq_zero.mp (le_antisymm hle hnn)).resolve_right hc2.ne'
      rw [abs_of_pos hc2, hflip_zero h0]

private theorem volume_planarRectSet_abs_xi (b1 b2 rb vx vy ξ η : ℝ) :
    ∃ bb2 : ℝ, (bb2 = b2 ∨ bb2 = -b2) ∧
      volume (planarRectSet b1 b2 rb vx vy ξ η) =
        volume (planarRectSet b1 bb2 rb vx vy |ξ| |η|) := by
  rcases le_or_gt 0 ξ with hξ | hξ <;> rcases le_or_gt 0 η with hη | hη
  · exact ⟨b2, Or.inl rfl, by rw [abs_of_nonneg hξ, abs_of_nonneg hη]⟩
  · refine ⟨-b2, Or.inr rfl, ?_⟩
    rw [abs_of_nonneg hξ, abs_of_neg hη]
    congr 1; ext ⟨x, y⟩
    simp only [planarRectSet, mem_ofPred_eq]
    have h2 : |η + b2 * vy * x - b2 * rb * y| = |-η + -b2 * vy * x - -b2 * rb * y| := by
      rw [← abs_neg]; congr 1; ring
    rw [h2]
  · refine ⟨-b2, Or.inr rfl, ?_⟩
    rw [abs_of_neg hξ, abs_of_nonneg hη]
    rw [volume_planarRectSet_neg_b]
    congr 1; ext ⟨x, y⟩
    simp only [planarRectSet, mem_ofPred_eq]
    have h1 : |ξ - -b1 * rb * x + -b1 * vx * y| = |-ξ - b1 * rb * x + b1 * vx * y| := by
      rw [← abs_neg]; congr 1; ring
    have h2 : |η + -b2 * vy * x - -b2 * rb * y| = |η + -b2 * vy * x - -b2 * rb * y| := rfl
    rw [h1]
  · refine ⟨b2, Or.inl rfl, ?_⟩
    rw [abs_of_neg hξ, abs_of_neg hη, volume_planarRectSet_neg_b]
    congr 1; ext ⟨x, y⟩
    simp only [planarRectSet, mem_ofPred_eq]
    have h1 : |ξ - -b1 * rb * x + -b1 * vx * y| = |-ξ - b1 * rb * x + b1 * vx * y| := by
      rw [← abs_neg]; congr 1; ring
    have h2 : |η + -b2 * vy * x - -b2 * rb * y| = |-η + b2 * vy * x - b2 * rb * y| := by
      rw [← abs_neg]; congr 1; ring
    rw [h1, h2]

private theorem volume_planarRectSet_le_sum_quadrants (b1 bb2 rb vx vy A B : ℝ) :
    volume (planarRectSet b1 bb2 rb vx vy A B) ≤
      volume (quadrantRectSet (1 + b1 * rb) (1 - b1 * rb) (-b1 * vx) (-bb2 * vy)
        (1 + bb2 * rb) (1 - bb2 * rb) A B) +
      volume (quadrantRectSet (1 + b1 * rb) (1 - b1 * rb) (b1 * vx) (-bb2 * vy)
        (1 - bb2 * rb) (1 + bb2 * rb) A B) +
      volume (quadrantRectSet (1 - b1 * rb) (1 + b1 * rb) (-b1 * vx) (bb2 * vy)
        (1 + bb2 * rb) (1 - bb2 * rb) A B) +
      volume (quadrantRectSet (1 - b1 * rb) (1 + b1 * rb) (b1 * vx) (bb2 * vy)
        (1 - bb2 * rb) (1 + bb2 * rb) A B) := by
  let Qpp := quadrantRectSet (1 + b1 * rb) (1 - b1 * rb) (-b1 * vx) (-bb2 * vy)
    (1 + bb2 * rb) (1 - bb2 * rb) A B
  let Qpm := quadrantRectSet (1 + b1 * rb) (1 - b1 * rb) (b1 * vx) (-bb2 * vy)
    (1 - bb2 * rb) (1 + bb2 * rb) A B
  let Qmp := quadrantRectSet (1 - b1 * rb) (1 + b1 * rb) (-b1 * vx) (bb2 * vy)
    (1 + bb2 * rb) (1 - bb2 * rb) A B
  let Qmm := quadrantRectSet (1 - b1 * rb) (1 + b1 * rb) (b1 * vx) (bb2 * vy)
    (1 - bb2 * rb) (1 + bb2 * rb) A B
  let f_pm : ℝ × ℝ → ℝ × ℝ := Prod.map id Neg.neg
  let f_mp : ℝ × ℝ → ℝ × ℝ := Prod.map Neg.neg id
  let f_mm : ℝ × ℝ → ℝ × ℝ := Prod.map Neg.neg Neg.neg
  have hcover : planarRectSet b1 bb2 rb vx vy A B ⊆
      ((Qpp ∪ f_pm ⁻¹' Qpm) ∪ f_mp ⁻¹' Qmp) ∪ f_mm ⁻¹' Qmm := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hlt_abs (u z : ℝ) (hu : 0 ≤ u) (h : u < |z|) : u < z ∨ u < -z := by
      rcases le_or_gt 0 z with hz | hz
      · left; rwa [abs_of_nonneg hz] at h
      · right; rwa [abs_of_neg hz] at h
    rcases le_or_gt 0 x with hx0 | hx0 <;> rcases le_or_gt 0 y with hy0 | hy0
    · rw [abs_of_nonneg hx0] at hx; rw [abs_of_nonneg hy0] at hy
      refine Or.inl (Or.inl (Or.inl ⟨hx0, hy0, ?_, ?_⟩))
      · rcases hlt_abs _ _ hx0 hx with h | h
        · left; linarith
        · right; linarith
      · rcases hlt_abs _ _ hy0 hy with h | h
        · left; linarith
        · right; linarith
    · rw [abs_of_nonneg hx0] at hx; rw [abs_of_neg hy0] at hy
      refine Or.inl (Or.inl (Or.inr ⟨hx0, by change 0 ≤ -y; linarith, ?_, ?_⟩))
      · rcases hlt_abs _ _ hx0 hx with h | h
        · left; change (1 + b1 * rb) * x + b1 * vx * (-y) < A; linarith
        · right; change (1 - b1 * rb) * x - b1 * vx * (-y) < -A; linarith
      · rcases hlt_abs _ _ (by linarith) hy with h | h
        · left; change -bb2 * vy * x + (1 - bb2 * rb) * (-y) < B; linarith
        · right; change -(-bb2 * vy) * x + (1 + bb2 * rb) * (-y) < -B; linarith
    · rw [abs_of_neg hx0] at hx; rw [abs_of_nonneg hy0] at hy
      refine Or.inl (Or.inr ⟨by change 0 ≤ -x; linarith, hy0, ?_, ?_⟩)
      · rcases hlt_abs _ _ (by linarith) hx with h | h
        · left; change (1 - b1 * rb) * (-x) + -b1 * vx * y < A; linarith
        · right; change (1 + b1 * rb) * (-x) - -b1 * vx * y < -A; linarith
      · rcases hlt_abs _ _ hy0 hy with h | h
        · left; change bb2 * vy * (-x) + (1 + bb2 * rb) * y < B; linarith
        · right; change -(bb2 * vy) * (-x) + (1 - bb2 * rb) * y < -B; linarith
    · rw [abs_of_neg hx0] at hx; rw [abs_of_neg hy0] at hy
      refine Or.inr ⟨by change 0 ≤ -x; linarith, by change 0 ≤ -y; linarith, ?_, ?_⟩
      · rcases hlt_abs _ _ (by linarith) hx with h | h
        · left; change (1 - b1 * rb) * (-x) + b1 * vx * (-y) < A; linarith
        · right; change (1 + b1 * rb) * (-x) - b1 * vx * (-y) < -A; linarith
      · rcases hlt_abs _ _ (by linarith) hy with h | h
        · left; change bb2 * vy * (-x) + (1 - bb2 * rb) * (-y) < B; linarith
        · right; change -(bb2 * vy) * (-x) + (1 + bb2 * rb) * (-y) < -B; linarith
  have hmp_pm : MeasurePreserving f_pm volume volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)
  have hmp_mp : MeasurePreserving f_mp volume volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)
  have hmp_mm : MeasurePreserving f_mm volume volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg volume).prod (Measure.measurePreserving_neg volume)
  have hv_pm : volume (f_pm ⁻¹' Qpm) = volume Qpm :=
    hmp_pm.measure_preimage (measurableSet_quadrantRectSet _ _ _ _ _ _ _ _).nullMeasurableSet
  have hv_mp : volume (f_mp ⁻¹' Qmp) = volume Qmp :=
    hmp_mp.measure_preimage (measurableSet_quadrantRectSet _ _ _ _ _ _ _ _).nullMeasurableSet
  have hv_mm : volume (f_mm ⁻¹' Qmm) = volume Qmm :=
    hmp_mm.measure_preimage (measurableSet_quadrantRectSet _ _ _ _ _ _ _ _).nullMeasurableSet
  refine (measure_mono hcover).trans ?_
  calc volume (((Qpp ∪ f_pm ⁻¹' Qpm) ∪ f_mp ⁻¹' Qmp) ∪ f_mm ⁻¹' Qmm)
      ≤ volume ((Qpp ∪ f_pm ⁻¹' Qpm) ∪ f_mp ⁻¹' Qmp) + volume (f_mm ⁻¹' Qmm) :=
        measure_union_le _ _
    _ ≤ volume (Qpp ∪ f_pm ⁻¹' Qpm) + volume (f_mp ⁻¹' Qmp) + volume (f_mm ⁻¹' Qmm) :=
        add_le_add (measure_union_le _ _) le_rfl
    _ ≤ volume Qpp + volume (f_pm ⁻¹' Qpm) + volume (f_mp ⁻¹' Qmp) + volume (f_mm ⁻¹' Qmm) :=
        add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    _ = volume Qpp + volume Qpm + volume Qmp + volume Qmm := by
        rw [hv_pm, hv_mp, hv_mm]

private theorem half_div_eq (u v D A : ℝ) :
    u * v * A / (2 * D) = u * v / 2 * (1 / D) * A := by
  rw [show 2 * D = D * 2 by ring, div_mul_eq_div_div]; ring

private theorem half_div_mul_eq (u v D1 D2 A : ℝ) :
    u * v * A / (2 * D1 * D2) = u * v / 2 * (1 / (D1 * D2)) * A := by
  rw [show 2 * D1 * D2 = (D1 * D2) * 2 by ring, div_mul_eq_div_div]; ring

private theorem half_num_div_eq (u v N D A : ℝ) :
    u * v * N * A / (2 * D) = u * v / 2 * (N / D) * A := by
  rw [show 2 * D = D * 2 by ring, div_mul_eq_div_div]; ring

private theorem quadOut_pos_bounds {u1 u2 rb vx vy x1 x2 P detM A B : ℝ}
    (hu1_nn : 0 ≤ u1) (hu2_nn : 0 ≤ u2) (hvx : 0 ≤ vx) (hvy : 0 ≤ vy)
    (hx1_nn : 0 ≤ x1) (hx2_nn : 0 ≤ x2) (h1mx1 : 0 < 1 - x1) (_h1px1 : 0 < 1 + x1)
    (h1mx2 : 0 < 1 - x2) (_h1px2 : 0 < 1 + x2) (hdetM : 0 < detM)
    (hdpp_ge_one : 1 ≤ (1 + x1) * (1 + x2) - P)
    (hx1_def : u1 * rb = x1) (hx2_def : u2 * rb = x2)
    (hP_def : u1 * u2 * vx * vy = P) (hdet_def : (1 - x1) * (1 - x2) - P = detM)
    (_hA : 0 ≤ A) (_hB : 0 ≤ B) :
    quadOutTerm (1 + u1 * rb) (1 - u1 * rb) (-u1 * vx) (-u2 * vy)
        (1 + u2 * rb) (1 - u2 * rb) A B ≤
      A * B / ((1 + x1) * (1 + x2) - P) +
        u2 * vy / 2 * (1 / (1 + x1)) * A ^ 2 +
        u1 * vx / 2 * (1 / (1 + x2)) * B ^ 2 ∧
    quadOutTerm (1 + u1 * rb) (1 - u1 * rb) (u1 * vx) (-u2 * vy)
        (1 - u2 * rb) (1 + u2 * rb) A B ≤
      A * B / ((1 + x1) * (1 - x2)) +
        u2 * vy / 2 * (1 / ((1 - x2) * (1 + x1) ^ 2)) * A ^ 2 +
        u1 * vx / 2 * ((1 - x1) / detM ^ 2) * B ^ 2 ∧
    quadOutTerm (1 - u1 * rb) (1 + u1 * rb) (-u1 * vx) (u2 * vy)
        (1 + u2 * rb) (1 - u2 * rb) A B ≤
      A * B / ((1 - x1) * (1 + x2)) +
        u2 * vy / 2 * ((1 - x2) / detM ^ 2) * A ^ 2 +
        u1 * vx / 2 * (1 / ((1 - x1) * (1 + x2) ^ 2)) * B ^ 2 ∧
    quadOutTerm (1 - u1 * rb) (1 + u1 * rb) (u1 * vx) (u2 * vy)
        (1 - u2 * rb) (1 + u2 * rb) A B ≤
      A * B / ((1 - x1) * (1 - x2)) +
        u2 * vy / 2 * (1 / ((1 + x2) * (1 - x1) ^ 2)) * A ^ 2 +
        u1 * vx / 2 * (1 / ((1 + x1) * (1 - x2) ^ 2)) * B ^ 2 := by
  have hu1v_nn : 0 ≤ u1 * vx := mul_nonneg hu1_nn hvx
  have hu2v_nn : 0 ≤ u2 * vy := mul_nonneg hu2_nn hvy
  have hnu1v_np : -u1 * vx ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu1_nn) hvx
  have hnu2v_np : -u2 * vy ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu2_nn) hvy
  have hmn_u2 : ¬(0 < -u2 * vy) := not_lt.mpr hnu2v_np
  have hmn_u1 : ¬(0 < -u1 * vx) := not_lt.mpr hnu1v_np
  have hP_mm : -u1 * vx * (-u2 * vy) = P := by rw [← hP_def]; ring
  have hP_pm : u1 * vx * (-u2 * vy) = -P := by rw [← hP_def]; ring
  have hP_mp : -u1 * vx * (u2 * vy) = -P := by rw [← hP_def]; ring
  have hdet_p : (1 - x1) * (1 - x2) + -P = detM := by rw [← hdet_def]; ring
  have hneg_u2v : -(-u2 * vy) = u2 * vy := by ring
  have hneg_u1v : -(-u1 * vx) = u1 * vx := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold quadOutTerm
    simp only [hmn_u2, hmn_u1, ↓reduceIte, add_zero, hx1_def, hx2_def, hP_mm, hneg_u2v, hneg_u1v]
    split_ifs with hc1 hc2 hc3
    · have hu1v : u1 * vx = 0 := by linarith only [hc1.1, hnu1v_np, hu1v_nn, hneg_u1v]
      have hP0 : P = 0 := by rw [← hP_def]; linear_combination u2 * vy * hu1v
      rw [hP0, sub_zero]
      have hnnA : 0 ≤ u2 * vy / 2 * (1 / (1 + x1)) * A ^ 2 := by positivity
      have hnnB : 0 ≤ u1 * vx / 2 * (1 / (1 + x2)) * B ^ 2 := by positivity
      linarith only [hnnA, hnnB]
    · have hu1v : u1 * vx = 0 := by linarith only [hc2.1, hnu1v_np, hu1v_nn, hneg_u1v]
      have hP0 : P = 0 := by rw [← hP_def]; linear_combination u2 * vy * hu1v
      rw [hP0, sub_zero]
      have hden : 1 + x1 ≤ (1 + x2) * (1 + x1) ^ 2 := by nlinarith only [hx1_nn, hx2_nn]
      have hleA : u2 * vy * A ^ 2 / (2 * (1 + x2) * (1 + x1) ^ 2) ≤
          u2 * vy / 2 * (1 / (1 + x1)) * A ^ 2 := by
        rw [show 2 * (1 + x2) * (1 + x1) ^ 2 = 2 * ((1 + x2) * (1 + x1) ^ 2) by ring]
        refine (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 2 * (1 + x1))
          (mul_le_mul_of_nonneg_left hden zero_le_two)).trans_eq ?_
        exact half_div_eq u2 vy (1 + x1) (A ^ 2)
      have hnnB : 0 ≤ u1 * vx / 2 * (1 / (1 + x2)) * B ^ 2 := by positivity
      linarith only [hleA, hnnB]
    · have hu2v : u2 * vy = 0 := by linarith only [hc3.2, hnu2v_np, hu2v_nn, hneg_u2v]
      have hP0 : P = 0 := by rw [← hP_def]; linear_combination u1 * vx * hu2v
      rw [hP0, sub_zero]
      have hden : 1 + x2 ≤ (1 + x1) * (1 + x2) ^ 2 := by nlinarith only [hx1_nn, hx2_nn]
      have hleB : u1 * vx * B ^ 2 / (2 * (1 + x1) * (1 + x2) ^ 2) ≤
          u1 * vx / 2 * (1 / (1 + x2)) * B ^ 2 := by
        rw [show 2 * (1 + x1) * (1 + x2) ^ 2 = 2 * ((1 + x1) * (1 + x2) ^ 2) by ring]
        refine (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 2 * (1 + x2))
          (mul_le_mul_of_nonneg_left hden zero_le_two)).trans_eq ?_
        exact half_div_eq u1 vx (1 + x2) (B ^ 2)
      have hnnA : 0 ≤ u2 * vy / 2 * (1 / (1 + x1)) * A ^ 2 := by positivity
      linarith only [hleB, hnnA]
    · have hleA : u2 * vy * A ^ 2 / (2 * (1 + x1) * ((1 + x1) * (1 + x2) - P)) ≤
          u2 * vy / 2 * (1 / (1 + x1)) * A ^ 2 := by
        refine (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 2 * (1 + x1) * 1)
          (mul_le_mul_of_nonneg_left hdpp_ge_one (by positivity))).trans_eq ?_
        simpa only [mul_one] using half_div_mul_eq u2 vy (1 + x1) 1 (A ^ 2)
      have hleB : u1 * vx * B ^ 2 / (2 * (1 + x2) * ((1 + x1) * (1 + x2) - P)) ≤
          u1 * vx / 2 * (1 / (1 + x2)) * B ^ 2 := by
        refine (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 2 * (1 + x2) * 1)
          (mul_le_mul_of_nonneg_left hdpp_ge_one (by positivity))).trans_eq ?_
        simpa only [mul_one] using half_div_mul_eq u1 vx (1 + x2) 1 (B ^ 2)
      linarith only [hleA, hleB]
  · unfold quadOutTerm
    simp only [hmn_u2, hu1v_nn, true_and, not_lt.mpr hu1v_nn, false_and, ↓reduceIte, add_zero,
      hx1_def, hx2_def, hP_pm, hdet_p, hneg_u2v]
    have h1 : (if 0 ≤ -u2 * vy then A * B / ((1 + x1) * (1 - x2))
        else if -u2 * vy < 0 then
          A * B / ((1 + x1) * (1 - x2)) + u2 * vy * A ^ 2 / (2 * (1 - x2) * (1 + x1) ^ 2)
        else A * B / ((1 + x1) * (1 - x2) - -P) +
          u2 * vy * A ^ 2 / (2 * (1 + x1) * ((1 + x1) * (1 - x2) - -P)) +
          -(u1 * vx) * B ^ 2 / (2 * (1 - x2) * ((1 + x1) * (1 - x2) - -P))) ≤
        A * B / ((1 + x1) * (1 - x2)) +
          u2 * vy / 2 * (1 / ((1 - x2) * (1 + x1) ^ 2)) * A ^ 2 := by
      split_ifs with hc1 hc2
      · have hnn : 0 ≤ u2 * vy / 2 * (1 / ((1 - x2) * (1 + x1) ^ 2)) * A ^ 2 := by positivity
        linarith only [hnn]
      · rw [half_div_mul_eq]
      · exfalso; exact hc2 (lt_of_not_ge hc1)
    have h2 : (if 0 < u1 * vx then
        if 0 ≤ -u2 * vy then u1 * vx * B ^ 2 / (2 * (1 - x1) * (1 - x2) ^ 2)
        else u1 * vx * (1 - x1) * B ^ 2 / (2 * detM ^ 2)
      else 0) ≤ u1 * vx / 2 * ((1 - x1) / detM ^ 2) * B ^ 2 := by
      split_ifs with hc1 hc2
      · have hu2v : u2 * vy = 0 := by linarith only [hc2, hnu2v_np, hu2v_nn, hneg_u2v]
        have hP0 : P = 0 := by rw [← hP_def]; linear_combination u1 * vx * hu2v
        have hd_eq : detM = (1 - x1) * (1 - x2) := by rw [← hdet_def, hP0, sub_zero]
        rw [hd_eq, half_div_mul_eq]
        refine le_of_eq ?_; congr 2; field_simp [h1mx1.ne', h1mx2.ne']
      · exact le_of_eq (half_num_div_eq u1 vx (1 - x1) (detM ^ 2) (B ^ 2))
      · positivity
    linarith only [h1, h2]
  · unfold quadOutTerm
    simp only [hmn_u1, hu2v_nn, and_true, not_lt.mpr hu2v_nn, and_false, ↓reduceIte, add_zero,
      hx1_def, hx2_def, hP_mp, hdet_p, hneg_u1v]
    have h1 : (if 0 ≤ -u1 * vx then A * B / ((1 - x1) * (1 + x2))
        else if -u1 * vx < 0 then
          A * B / ((1 - x1) * (1 + x2)) + u1 * vx * B ^ 2 / (2 * (1 - x1) * (1 + x2) ^ 2)
        else A * B / ((1 - x1) * (1 + x2) - -P) +
          -(u2 * vy) * A ^ 2 / (2 * (1 - x1) * ((1 - x1) * (1 + x2) - -P)) +
          u1 * vx * B ^ 2 / (2 * (1 + x2) * ((1 - x1) * (1 + x2) - -P))) ≤
        A * B / ((1 - x1) * (1 + x2)) +
          u1 * vx / 2 * (1 / ((1 - x1) * (1 + x2) ^ 2)) * B ^ 2 := by
      split_ifs with hc1 hc2
      · have hnn : 0 ≤ u1 * vx / 2 * (1 / ((1 - x1) * (1 + x2) ^ 2)) * B ^ 2 := by positivity
        linarith only [hnn]
      · rw [half_div_mul_eq]
      · exfalso; exact hc2 (lt_of_not_ge hc1)
    have h2 : (if 0 < u2 * vy then
        if 0 ≤ -u1 * vx then u2 * vy * A ^ 2 / (2 * (1 - x2) * (1 - x1) ^ 2)
        else u2 * vy * (1 - x2) * A ^ 2 / (2 * detM ^ 2)
      else 0) ≤ u2 * vy / 2 * ((1 - x2) / detM ^ 2) * A ^ 2 := by
      split_ifs with hc1 hc2
      · have hu1v : u1 * vx = 0 := by linarith only [hc2, hnu1v_np, hu1v_nn, hneg_u1v]
        have hP0 : P = 0 := by rw [← hP_def]; linear_combination u2 * vy * hu1v
        have hd_eq : detM = (1 - x1) * (1 - x2) := by rw [← hdet_def, hP0, sub_zero]
        rw [hd_eq, half_div_mul_eq]
        refine le_of_eq ?_; congr 2; field_simp [h1mx1.ne', h1mx2.ne']
      · exact le_of_eq (half_num_div_eq u2 vy (1 - x2) (detM ^ 2) (A ^ 2))
      · positivity
    linarith only [h1, h2]
  · unfold quadOutTerm
    simp only [hu1v_nn, hu2v_nn, and_self, ↓reduceIte, hx1_def, hx2_def]
    have h2 : (if 0 < u2 * vy then u2 * vy * A ^ 2 / (2 * (1 + x2) * (1 - x1) ^ 2)
        else 0) ≤ u2 * vy / 2 * (1 / ((1 + x2) * (1 - x1) ^ 2)) * A ^ 2 := by
      split_ifs
      · exact le_of_eq (half_div_mul_eq u2 vy (1 + x2) ((1 - x1) ^ 2) (A ^ 2))
      · positivity
    have h3 : (if 0 < u1 * vx then u1 * vx * B ^ 2 / (2 * (1 + x1) * (1 - x2) ^ 2)
        else 0) ≤ u1 * vx / 2 * (1 / ((1 + x1) * (1 - x2) ^ 2)) * B ^ 2 := by
      split_ifs
      · exact le_of_eq (half_div_mul_eq u1 vx (1 + x1) ((1 - x2) ^ 2) (B ^ 2))
      · positivity
    linarith only [h2, h3]

private theorem quadOut_neg_bounds {u1 u2 rb vx vy x1 x2 P detM A B : ℝ}
    (hu1_nn : 0 ≤ u1) (hu2_nn : 0 ≤ u2) (hvx : 0 ≤ vx) (hvy : 0 ≤ vy)
    (hx1_nn : 0 ≤ x1) (hx2_nn : 0 ≤ x2) (h1mx1 : 0 < 1 - x1) (h1px1 : 0 < 1 + x1)
    (h1mx2 : 0 < 1 - x2) (h1px2 : 0 < 1 + x2) (_hdetM : 0 < detM)
    (hP_le_2x : P ≤ 2 * x1 * x2)
    (hx1_def : u1 * rb = x1) (hx2_def : u2 * rb = x2)
    (hP_def : u1 * u2 * vx * vy = P) (hdet_def : (1 - x1) * (1 - x2) - P = detM)
    (_hA : 0 ≤ A) (_hB : 0 ≤ B) :
    quadOutTerm (1 + u1 * rb) (1 - u1 * rb) (-u1 * vx) (-(-u2) * vy)
        (1 + -u2 * rb) (1 - -u2 * rb) A B ≤
      A * B / ((1 + x1) * (1 - x2)) +
        u2 * vy / 2 * (1 / (1 + x2)) * A ^ 2 +
        u1 * vx / 2 * (1 / ((1 + x1) * (1 - x2) ^ 2)) * B ^ 2 ∧
    quadOutTerm (1 + u1 * rb) (1 - u1 * rb) (u1 * vx) (-(-u2) * vy)
        (1 - -u2 * rb) (1 + -u2 * rb) A B ≤
      A * B / ((1 + x1) * (1 + x2)) +
        u2 * vy / 2 * (1 / ((1 - x2) * (1 + x1) ^ 2)) * A ^ 2 +
        u1 * vx / 2 * (1 / ((1 - x1) * (1 + x2) ^ 2)) * B ^ 2 ∧
    quadOutTerm (1 - u1 * rb) (1 + u1 * rb) (-u1 * vx) ((-u2) * vy)
        (1 + -u2 * rb) (1 - -u2 * rb) A B ≤
      A * B / detM +
        u2 * vy / 2 * (1 / ((1 - x1) * detM)) * A ^ 2 +
        u1 * vx / 2 * (1 / ((1 - x2) * detM)) * B ^ 2 ∧
    quadOutTerm (1 - u1 * rb) (1 + u1 * rb) (u1 * vx) ((-u2) * vy)
        (1 - -u2 * rb) (1 + -u2 * rb) A B ≤
      A * B / ((1 - x1) * (1 + x2)) +
        u2 * vy / 2 * (1 / ((1 - x1) ^ 2 * (1 + x2))) * A ^ 2 +
        u1 * vx / 2 * (1 / (1 + x1)) * B ^ 2 := by
  have hu1v_nn : 0 ≤ u1 * vx := mul_nonneg hu1_nn hvx
  have hu2v_nn : 0 ≤ u2 * vy := mul_nonneg hu2_nn hvy
  have hnu1v_np : -u1 * vx ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu1_nn) hvx
  have hnu2v_np : -u2 * vy ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu2_nn) hvy
  have hnu2v_np' : (-u2) * vy ≤ 0 := hnu2v_np
  have hmn_u1 : ¬(0 < -u1 * vx) := not_lt.mpr hnu1v_np
  have hmn_nu2 : ¬(0 < (-u2) * vy) := not_lt.mpr hnu2v_np'
  have hnx2_add : 1 + -u2 * rb = 1 - x2 := by rw [← hx2_def]; ring
  have hnx2_sub : 1 - -u2 * rb = 1 + x2 := by rw [← hx2_def]; ring
  have hP_mp : -u1 * vx * (u2 * vy) = -P := by rw [← hP_def]; ring
  have hP_pm2 : u1 * vx * ((-u2) * vy) = -P := by rw [← hP_def]; ring
  have hP_mm2 : -u1 * vx * ((-u2) * vy) = P := by rw [← hP_def]; ring
  have hneg_nu2v : -((-u2) * vy) = u2 * vy := by ring
  have hneg_u1v : -(-u1 * vx) = u1 * vx := by ring
  have hx1_lt : x1 < 1 := by linarith only [h1mx1]
  have hx2_lt : x2 < 1 := by linarith only [h1mx2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold quadOutTerm
    rw [neg_neg]
    simp only [hmn_u1, hu2v_nn, and_true, not_lt.mpr hu2v_nn, and_false, ↓reduceIte, add_zero,
      hx1_def, hnx2_add, hnx2_sub, hP_mp, hneg_u1v]
    have h1 : (if 0 ≤ -u1 * vx then A * B / ((1 + x1) * (1 - x2))
        else if -u1 * vx < 0 then
          A * B / ((1 + x1) * (1 - x2)) + u1 * vx * B ^ 2 / (2 * (1 + x1) * (1 - x2) ^ 2)
        else A * B / ((1 + x1) * (1 - x2) - -P) +
          -(u2 * vy) * A ^ 2 / (2 * (1 + x1) * ((1 + x1) * (1 - x2) - -P)) +
          u1 * vx * B ^ 2 / (2 * (1 - x2) * ((1 + x1) * (1 - x2) - -P))) ≤
        A * B / ((1 + x1) * (1 - x2)) +
          u1 * vx / 2 * (1 / ((1 + x1) * (1 - x2) ^ 2)) * B ^ 2 := by
      split_ifs with hc1 hc2
      · have hnn : 0 ≤ u1 * vx / 2 * (1 / ((1 + x1) * (1 - x2) ^ 2)) * B ^ 2 := by positivity
        linarith only [hnn]
      · rw [half_div_mul_eq]
      · exfalso; exact hc2 (lt_of_not_ge hc1)
    have h2 : (if 0 < u2 * vy then
        if 0 ≤ -u1 * vx then u2 * vy * A ^ 2 / (2 * (1 + x2) * (1 + x1) ^ 2)
        else u2 * vy * (1 + x2) * A ^ 2 / (2 * ((1 + x1) * (1 + x2) + -P) ^ 2)
      else 0) ≤ u2 * vy / 2 * (1 / (1 + x2)) * A ^ 2 := by
      split_ifs with hc1 hc2
      · have hge : 1 ≤ (1 + x1) ^ 2 := by nlinarith only [hx1_nn]
        refine (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 2 * (1 + x2) * 1)
          (mul_le_mul_of_nonneg_left hge (by positivity : 0 ≤ 2 * (1 + x2)))).trans_eq ?_
        simpa only [mul_one] using half_div_mul_eq u2 vy (1 + x2) 1 (A ^ 2)
      · rw [← sub_eq_add_neg]
        have hge_x2 : 1 + x2 ≤ (1 + x1) * (1 + x2) - P := by
          nlinarith only [hP_le_2x, hx1_nn, hx2_lt, h1mx2]
        have hsq_x2 : (1 + x2) ^ 2 ≤ ((1 + x1) * (1 + x2) - P) ^ 2 :=
          pow_le_pow_left₀ h1px2.le hge_x2 2
        refine (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 2 * (1 + x2) ^ 2)
          (mul_le_mul_of_nonneg_left hsq_x2 zero_le_two)).trans_eq ?_
        rw [half_num_div_eq]; congr 2; field_simp [h1px2.ne']
      · positivity
    linarith only [h1, h2]
  · unfold quadOutTerm
    rw [neg_neg]
    simp only [hu1v_nn, hu2v_nn, and_self, ↓reduceIte, hx1_def, hnx2_add, hnx2_sub]
    have h2 : (if 0 < u2 * vy then u2 * vy * A ^ 2 / (2 * (1 - x2) * (1 + x1) ^ 2)
        else 0) ≤ u2 * vy / 2 * (1 / ((1 - x2) * (1 + x1) ^ 2)) * A ^ 2 := by
      split_ifs
      · exact le_of_eq (half_div_mul_eq u2 vy (1 - x2) ((1 + x1) ^ 2) (A ^ 2))
      · positivity
    have h3 : (if 0 < u1 * vx then u1 * vx * B ^ 2 / (2 * (1 - x1) * (1 + x2) ^ 2)
        else 0) ≤ u1 * vx / 2 * (1 / ((1 - x1) * (1 + x2) ^ 2)) * B ^ 2 := by
      split_ifs
      · exact le_of_eq (half_div_mul_eq u1 vx (1 - x1) ((1 + x2) ^ 2) (B ^ 2))
      · positivity
    linarith only [h2, h3]
  · unfold quadOutTerm
    simp only [hmn_nu2, hmn_u1, ↓reduceIte, add_zero, hx1_def, hnx2_add, hP_mm2,
      hdet_def, hneg_nu2v, hneg_u1v]
    split_ifs with hc1 hc2 hc3
    · have hu1v : u1 * vx = 0 := by linarith only [hc1.1, hnu1v_np, hu1v_nn, hneg_u1v]
      have hP0 : P = 0 := by rw [← hP_def]; linear_combination u2 * vy * hu1v
      have hd_eq : detM = (1 - x1) * (1 - x2) := by rw [← hdet_def, hP0, sub_zero]
      rw [hd_eq]
      have hnnA : 0 ≤ u2 * vy / 2 * (1 / ((1 - x1) * ((1 - x1) * (1 - x2)))) * A ^ 2 := by
        positivity
      have hnnB : 0 ≤ u1 * vx / 2 * (1 / ((1 - x2) * ((1 - x1) * (1 - x2)))) * B ^ 2 := by
        positivity
      linarith only [hnnA, hnnB]
    · have hu1v : u1 * vx = 0 := by linarith only [hc2.1, hnu1v_np, hu1v_nn, hneg_u1v]
      have hP0 : P = 0 := by rw [← hP_def]; linear_combination u2 * vy * hu1v
      have hd_eq : detM = (1 - x1) * (1 - x2) := by rw [← hdet_def, hP0, sub_zero]
      rw [hd_eq, half_div_mul_eq]
      have heqA : u2 * vy / 2 * (1 / ((1 - x2) * (1 - x1) ^ 2)) * A ^ 2 =
          u2 * vy / 2 * (1 / ((1 - x1) * ((1 - x1) * (1 - x2)))) * A ^ 2 := by
        congr 2; ring_nf
      have hnnB : 0 ≤ u1 * vx / 2 * (1 / ((1 - x2) * ((1 - x1) * (1 - x2)))) * B ^ 2 := by
        positivity
      linarith only [heqA, hnnB]
    · have hu2v : u2 * vy = 0 := by linarith only [hc3.2, hnu2v_np', hu2v_nn, hneg_nu2v]
      have hP0 : P = 0 := by rw [← hP_def]; linear_combination u1 * vx * hu2v
      have hd_eq : detM = (1 - x1) * (1 - x2) := by rw [← hdet_def, hP0, sub_zero]
      rw [hd_eq, half_div_mul_eq]
      have heqB : u1 * vx / 2 * (1 / ((1 - x1) * (1 - x2) ^ 2)) * B ^ 2 =
          u1 * vx / 2 * (1 / ((1 - x2) * ((1 - x1) * (1 - x2)))) * B ^ 2 := by
        congr 2; ring_nf
      have hnnA : 0 ≤ u2 * vy / 2 * (1 / ((1 - x1) * ((1 - x1) * (1 - x2)))) * A ^ 2 := by
        positivity
      linarith only [heqB, hnnA]
    · rw [half_div_mul_eq u2 vy (1 - x1) detM (A ^ 2),
        half_div_mul_eq u1 vx (1 - x2) detM (B ^ 2)]
  · unfold quadOutTerm
    simp only [hmn_nu2, hu1v_nn, true_and, not_lt.mpr hu1v_nn, false_and, ↓reduceIte, add_zero,
      hx1_def, hnx2_sub, hP_pm2, hneg_nu2v]
    have h1 : (if 0 ≤ -u2 * vy then A * B / ((1 - x1) * (1 + x2))
        else if -u2 * vy < 0 then
          A * B / ((1 - x1) * (1 + x2)) + u2 * vy * A ^ 2 / (2 * (1 + x2) * (1 - x1) ^ 2)
        else A * B / ((1 - x1) * (1 + x2) - -P) +
          u2 * vy * A ^ 2 / (2 * (1 - x1) * ((1 - x1) * (1 + x2) - -P)) +
          -(u1 * vx) * B ^ 2 / (2 * (1 + x2) * ((1 - x1) * (1 + x2) - -P))) ≤
        A * B / ((1 - x1) * (1 + x2)) +
          u2 * vy / 2 * (1 / ((1 - x1) ^ 2 * (1 + x2))) * A ^ 2 := by
      split_ifs with hc1 hc2
      · have hnn : 0 ≤ u2 * vy / 2 * (1 / ((1 - x1) ^ 2 * (1 + x2))) * A ^ 2 := by positivity
        linarith only [hnn]
      · rw [half_div_mul_eq, mul_comm (1 + x2) ((1 - x1) ^ 2)]
      · exfalso; exact hc2 (lt_of_not_ge hc1)
    have h2 : (if 0 < u1 * vx then
        if 0 ≤ -u2 * vy then u1 * vx * B ^ 2 / (2 * (1 + x1) * (1 + x2) ^ 2)
        else u1 * vx * (1 + x1) * B ^ 2 / (2 * ((1 + x1) * (1 + x2) + -P) ^ 2)
      else 0) ≤ u1 * vx / 2 * (1 / (1 + x1)) * B ^ 2 := by
      split_ifs with hc1 hc2
      · have hge : 1 ≤ (1 + x2) ^ 2 := by nlinarith only [hx2_nn]
        refine (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 2 * (1 + x1) * 1)
          (mul_le_mul_of_nonneg_left hge (by positivity : 0 ≤ 2 * (1 + x1)))).trans_eq ?_
        simpa only [mul_one] using half_div_mul_eq u1 vx (1 + x1) 1 (B ^ 2)
      · rw [← sub_eq_add_neg]
        have hge_x1 : 1 + x1 ≤ (1 + x1) * (1 + x2) - P := by
          nlinarith only [hP_le_2x, hx2_nn, hx1_lt, h1mx1]
        have hsq_x1 : (1 + x1) ^ 2 ≤ ((1 + x1) * (1 + x2) - P) ^ 2 :=
          pow_le_pow_left₀ h1px1.le hge_x1 2
        refine (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 2 * (1 + x1) ^ 2)
          (mul_le_mul_of_nonneg_left hsq_x1 zero_le_two)).trans_eq ?_
        rw [half_num_div_eq]; congr 2; field_simp [h1px1.ne']
      · positivity
    linarith only [h1, h2]

private theorem pairCAB_bounds {x1 x2 P detM : ℝ}
    (hx1_nn : 0 ≤ x1) (hx2_nn : 0 ≤ x2) (h1mx1 : 0 < 1 - x1) (h1px1 : 0 < 1 + x1)
    (h1mx2 : 0 < 1 - x2) (h1px2 : 0 < 1 + x2) (hP_nn : 0 ≤ P) (hdetM : 0 < detM)
    (hdpp_pos : 0 < (1 + x1) * (1 + x2) - P) (hdet_def : (1 - x1) * (1 - x2) - P = detM) :
    1 / ((1 + x1) * (1 + x2)) + 1 / ((1 + x1) * (1 - x2)) +
      1 / ((1 - x1) * (1 + x2)) + 1 / detM = pairCAB x1 x2 P detM ∧
    1 / ((1 + x1) * (1 + x2) - P) + 1 / ((1 + x1) * (1 - x2)) +
      1 / ((1 - x1) * (1 + x2)) + 1 / ((1 - x1) * (1 - x2)) ≤ pairCAB x1 x2 P detM := by
  have h1mx1_sq : 0 < 1 - x1 ^ 2 := by nlinarith [hx1_nn, h1mx1]
  have h1mx2_sq : 0 < 1 - x2 ^ 2 := by nlinarith [hx2_nn, h1mx2]
  have hcAB_eq : 1 / ((1 + x1) * (1 + x2)) + 1 / ((1 + x1) * (1 - x2)) +
      1 / ((1 - x1) * (1 + x2)) + 1 / detM = pairCAB x1 x2 P detM := by
    unfold pairCAB
    field_simp [h1px1.ne', h1mx1.ne', h1px2.ne', h1mx2.ne', h1mx1_sq.ne', h1mx2_sq.ne', hdetM.ne']
    rw [← hdet_def]; ring
  refine ⟨hcAB_eq, ?_⟩
  rw [← hcAB_eq]
  have hdiff : 1 / ((1 + x1) * (1 + x2) - P) - 1 / ((1 + x1) * (1 + x2)) ≤
      1 / detM - 1 / ((1 - x1) * (1 - x2)) := by
    set a := (1 - x1) * (1 - x2)
    set b := (1 + x1) * (1 + x2)
    have ha : 0 < a := mul_pos h1mx1 h1mx2
    have hb : 0 < b := mul_pos h1px1 h1px2
    have hab : a ≤ b := by dsimp [a, b]; nlinarith [hx1_nn, hx2_nn]
    have h1 : 1 / (b - P) - 1 / b = P / (b * (b - P)) := by
      field_simp [hb.ne', hdpp_pos.ne']; ring
    have ha_sub : a - P = detM := hdet_def
    have h2 : 1 / detM - 1 / a = P / (a * detM) := by
      field_simp [ha.ne', hdetM.ne']
      rw [← ha_sub]; ring
    rw [h1, h2]
    exact div_le_div_of_nonneg_left hP_nn (mul_pos ha hdetM)
      (mul_le_mul hab (by linarith) hdetM.le hb.le)
  linarith

private theorem volume_planarRectSet_le_out_pos {u1 u2 rb vx vy x1 x2 P detM A B : ℝ}
    (hu1_nn : 0 ≤ u1) (hu2_nn : 0 ≤ u2) (hvx : 0 ≤ vx) (hvy : 0 ≤ vy)
    (hx1_nn : 0 ≤ x1) (hx2_nn : 0 ≤ x2) (h1mx1 : 0 < 1 - x1) (h1px1 : 0 < 1 + x1)
    (h1mx2 : 0 < 1 - x2) (h1px2 : 0 < 1 + x2) (hP_nn : 0 ≤ P) (hdetM : 0 < detM)
    (hdpp_ge_one : 1 ≤ (1 + x1) * (1 + x2) - P)
    (hx1_def : u1 * rb = x1) (hx2_def : u2 * rb = x2)
    (hP_def : u1 * u2 * vx * vy = P) (hdet_def : (1 - x1) * (1 - x2) - P = detM)
    (hcAB_p_le : 1 / ((1 + x1) * (1 + x2) - P) + 1 / ((1 + x1) * (1 - x2)) +
      1 / ((1 - x1) * (1 + x2)) + 1 / ((1 - x1) * (1 - x2)) ≤ pairCAB x1 x2 P detM)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    volume (planarRectSet u1 u2 rb vx vy A B) ≤
      ENNReal.ofReal (pairCxp u2 vy x1 x2 detM * A ^ 2 +
        pairCxp u1 vx x2 x1 detM * B ^ 2 +
        pairCAB x1 x2 P detM * (A * B)) := by
  have hdpp_pos : 0 < (1 + x1) * (1 + x2) - P := by linarith only [hdpp_ge_one]
  have hd1_1 : 0 < (1 + u1 * rb) * (1 + u2 * rb) - -u1 * vx * (-u2 * vy) := by
    have : (1 + u1 * rb) * (1 + u2 * rb) - -u1 * vx * (-u2 * vy) = (1 + x1) * (1 + x2) - P := by
      rw [← hx1_def, ← hx2_def, ← hP_def]; ring
    linarith only [this, hdpp_pos]
  have hd1_2 : 0 < (1 + u1 * rb) * (1 - u2 * rb) + -u1 * vx * (-u2 * vy) := by
    have : (1 + u1 * rb) * (1 - u2 * rb) + -u1 * vx * (-u2 * vy) = (1 + x1) * (1 - x2) + P := by
      rw [← hx1_def, ← hx2_def, ← hP_def]; ring
    linarith only [this, mul_pos h1px1 h1mx2, hP_nn]
  have hd1_3 : 0 < (1 - u1 * rb) * (1 + u2 * rb) + -u1 * vx * (-u2 * vy) := by
    have : (1 - u1 * rb) * (1 + u2 * rb) + -u1 * vx * (-u2 * vy) = (1 - x1) * (1 + x2) + P := by
      rw [← hx1_def, ← hx2_def, ← hP_def]; ring
    linarith only [this, mul_pos h1mx1 h1px2, hP_nn]
  have hd1_4 : 0 < (1 - u1 * rb) * (1 - u2 * rb) - -u1 * vx * (-u2 * vy) := by
    have : (1 - u1 * rb) * (1 - u2 * rb) - -u1 * vx * (-u2 * vy) = detM := by
      rw [← hdet_def, ← hx1_def, ← hx2_def, ← hP_def]; ring
    linarith only [this, hdetM]
  have hn1 : 0 ≤ A * B / ((1 + x1) * (1 + x2) - P) + u2 * vy / 2 * (1 / (1 + x1)) * A ^ 2 +
      u1 * vx / 2 * (1 / (1 + x2)) * B ^ 2 :=
    add_nonneg (add_nonneg (div_nonneg (mul_nonneg hA hB) hdpp_pos.le)
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu2_nn hvy) zero_le_two)
        (div_nonneg zero_le_one h1px1.le)) (sq_nonneg A)))
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu1_nn hvx) zero_le_two)
        (div_nonneg zero_le_one h1px2.le)) (sq_nonneg B))
  have hn2 : 0 ≤ A * B / ((1 + x1) * (1 - x2)) +
      u2 * vy / 2 * (1 / ((1 - x2) * (1 + x1) ^ 2)) * A ^ 2 +
      u1 * vx / 2 * ((1 - x1) / detM ^ 2) * B ^ 2 :=
    add_nonneg (add_nonneg (div_nonneg (mul_nonneg hA hB) (mul_pos h1px1 h1mx2).le)
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu2_nn hvy) zero_le_two)
        (div_nonneg zero_le_one (mul_pos h1mx2 (sq_pos_of_pos h1px1)).le)) (sq_nonneg A)))
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu1_nn hvx) zero_le_two)
        (div_nonneg h1mx1.le (sq_nonneg detM))) (sq_nonneg B))
  have hn3 : 0 ≤ A * B / ((1 - x1) * (1 + x2)) + u2 * vy / 2 * ((1 - x2) / detM ^ 2) * A ^ 2 +
      u1 * vx / 2 * (1 / ((1 - x1) * (1 + x2) ^ 2)) * B ^ 2 :=
    add_nonneg (add_nonneg (div_nonneg (mul_nonneg hA hB) (mul_pos h1mx1 h1px2).le)
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu2_nn hvy) zero_le_two)
        (div_nonneg h1mx2.le (sq_nonneg detM))) (sq_nonneg A)))
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu1_nn hvx) zero_le_two)
        (div_nonneg zero_le_one (mul_pos h1mx1 (sq_pos_of_pos h1px2)).le)) (sq_nonneg B))
  have hn4 : 0 ≤ A * B / ((1 - x1) * (1 - x2)) +
      u2 * vy / 2 * (1 / ((1 + x2) * (1 - x1) ^ 2)) * A ^ 2 +
      u1 * vx / 2 * (1 / ((1 + x1) * (1 - x2) ^ 2)) * B ^ 2 :=
    add_nonneg (add_nonneg (div_nonneg (mul_nonneg hA hB) (mul_pos h1mx1 h1mx2).le)
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu2_nn hvy) zero_le_two)
        (div_nonneg zero_le_one (mul_pos h1px2 (sq_pos_of_pos h1mx1)).le)) (sq_nonneg A)))
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu1_nn hvx) zero_le_two)
        (div_nonneg zero_le_one (mul_pos h1px1 (sq_pos_of_pos h1mx2)).le)) (sq_nonneg B))
  have h1px1' : 0 < 1 + u1 * rb := by rw [hx1_def]; exact h1px1
  have h1mx1' : 0 < 1 - u1 * rb := by rw [hx1_def]; exact h1mx1
  have h1px2' : 0 < 1 + u2 * rb := by rw [hx2_def]; exact h1px2
  have h1mx2' : 0 < 1 - u2 * rb := by rw [hx2_def]; exact h1mx2
  refine (volume_planarRectSet_le_sum_quadrants u1 u2 rb vx vy A B).trans ?_
  obtain ⟨hb_q1, hb_q2, hb_q3, hb_q4⟩ :=
    quadOut_pos_bounds hu1_nn hu2_nn hvx hvy hx1_nn hx2_nn h1mx1 h1px1 h1mx2 h1px2 hdetM
      hdpp_ge_one hx1_def hx2_def hP_def hdet_def hA hB
  have hq1' := (volume_quadrantRectSet_le_out (-u1 * vx) (-u2 * vy) h1px1' h1mx1' h1px2' h1mx2'
    hd1_1 hd1_2 hd1_3 hd1_4 hA hB).trans (ENNReal.ofReal_le_ofReal hb_q1)
  have hq2' := (volume_quadrantRectSet_le_out (u1 * vx) (-u2 * vy) h1px1' h1mx1' h1mx2' h1px2'
    (by linarith only [hd1_2, show u1 * vx * (-u2 * vy) = -(-u1 * vx * (-u2 * vy)) by ring])
    (by linarith only [hd1_1, show u1 * vx * (-u2 * vy) = -(-u1 * vx * (-u2 * vy)) by ring])
    (by linarith only [hd1_4, show u1 * vx * (-u2 * vy) = -(-u1 * vx * (-u2 * vy)) by ring])
    (by linarith only [hd1_3, show u1 * vx * (-u2 * vy) = -(-u1 * vx * (-u2 * vy)) by ring])
    hA hB).trans (ENNReal.ofReal_le_ofReal hb_q2)
  have hq3' := (volume_quadrantRectSet_le_out (-u1 * vx) (u2 * vy) h1mx1' h1px1' h1px2' h1mx2'
    (by linarith only [hd1_3, show -u1 * vx * (u2 * vy) = -(-u1 * vx * (-u2 * vy)) by ring])
    (by linarith only [hd1_4, show -u1 * vx * (u2 * vy) = -(-u1 * vx * (-u2 * vy)) by ring])
    (by linarith only [hd1_1, show -u1 * vx * (u2 * vy) = -(-u1 * vx * (-u2 * vy)) by ring])
    (by linarith only [hd1_2, show -u1 * vx * (u2 * vy) = -(-u1 * vx * (-u2 * vy)) by ring])
    hA hB).trans (ENNReal.ofReal_le_ofReal hb_q3)
  have hq4' := (volume_quadrantRectSet_le_out (u1 * vx) (u2 * vy) h1mx1' h1px1' h1mx2' h1px2'
    (by linarith only [hd1_4, show u1 * vx * (u2 * vy) = -u1 * vx * (-u2 * vy) by ring])
    (by linarith only [hd1_3, show u1 * vx * (u2 * vy) = -u1 * vx * (-u2 * vy) by ring])
    (by linarith only [hd1_2, show u1 * vx * (u2 * vy) = -u1 * vx * (-u2 * vy) by ring])
    (by linarith only [hd1_1, show u1 * vx * (u2 * vy) = -u1 * vx * (-u2 * vy) by ring])
    hA hB).trans (ENNReal.ofReal_le_ofReal hb_q4)
  refine (add_le_add (add_le_add (add_le_add hq1' hq2') hq3') hq4').trans ?_
  rw [← ENNReal.ofReal_add hn1 hn2, ← ENNReal.ofReal_add (add_nonneg hn1 hn2) hn3,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg hn1 hn2) hn3) hn4]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsum_p : (A * B / ((1 + x1) * (1 + x2) - P) + u2 * vy / 2 * (1 / (1 + x1)) * A ^ 2 +
        u1 * vx / 2 * (1 / (1 + x2)) * B ^ 2) +
      (A * B / ((1 + x1) * (1 - x2)) + u2 * vy / 2 * (1 / ((1 - x2) * (1 + x1) ^ 2)) * A ^ 2 +
        u1 * vx / 2 * ((1 - x1) / detM ^ 2) * B ^ 2) +
      (A * B / ((1 - x1) * (1 + x2)) + u2 * vy / 2 * ((1 - x2) / detM ^ 2) * A ^ 2 +
        u1 * vx / 2 * (1 / ((1 - x1) * (1 + x2) ^ 2)) * B ^ 2) +
      (A * B / ((1 - x1) * (1 - x2)) + u2 * vy / 2 * (1 / ((1 + x2) * (1 - x1) ^ 2)) * A ^ 2 +
        u1 * vx / 2 * (1 / ((1 + x1) * (1 - x2) ^ 2)) * B ^ 2) =
      pairCxp u2 vy x1 x2 detM * A ^ 2 + pairCxp u1 vx x2 x1 detM * B ^ 2 +
      (1 / ((1 + x1) * (1 + x2) - P) + 1 / ((1 + x1) * (1 - x2)) +
        1 / ((1 - x1) * (1 + x2)) + 1 / ((1 - x1) * (1 - x2))) * (A * B) := by
    unfold pairCxp; ring
  rw [hsum_p]
  have hAB_le := mul_le_mul_of_nonneg_right hcAB_p_le (mul_nonneg hA hB)
  linarith only [hAB_le]

private theorem volume_planarRectSet_le_out_neg {u1 u2 rb vx vy x1 x2 P detM A B : ℝ}
    (hu1_nn : 0 ≤ u1) (hu2_nn : 0 ≤ u2) (hvx : 0 ≤ vx) (hvy : 0 ≤ vy)
    (hx1_nn : 0 ≤ x1) (hx2_nn : 0 ≤ x2) (h1mx1 : 0 < 1 - x1) (h1px1 : 0 < 1 + x1)
    (h1mx2 : 0 < 1 - x2) (h1px2 : 0 < 1 + x2) (hP_nn : 0 ≤ P) (hdetM : 0 < detM)
    (hdpp_pos : 0 < (1 + x1) * (1 + x2) - P) (hP_le_2x : P ≤ 2 * x1 * x2)
    (hx1_def : u1 * rb = x1) (hx2_def : u2 * rb = x2)
    (hP_def : u1 * u2 * vx * vy = P) (hdet_def : (1 - x1) * (1 - x2) - P = detM)
    (hcAB_eq : 1 / ((1 + x1) * (1 + x2)) + 1 / ((1 + x1) * (1 - x2)) +
      1 / ((1 - x1) * (1 + x2)) + 1 / detM = pairCAB x1 x2 P detM)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    volume (planarRectSet u1 (-u2) rb vx vy A B) ≤
      ENNReal.ofReal (pairCxm u2 vy x1 x2 detM * A ^ 2 +
        pairCxm u1 vx x2 x1 detM * B ^ 2 +
        pairCAB x1 x2 P detM * (A * B)) := by
  have hd_pm_p : 0 < (1 + u1 * rb) * (1 + -u2 * rb) - -u1 * vx * (-(-u2) * vy) := by
    have : (1 + u1 * rb) * (1 + -u2 * rb) - -u1 * vx * (-(-u2) * vy) = (1 + x1) * (1 - x2) + P := by
      rw [← hx1_def, ← hx2_def, ← hP_def]; ring
    linarith only [this, mul_pos h1px1 h1mx2, hP_nn]
  have hd_pp_m : 0 < (1 + u1 * rb) * (1 - -u2 * rb) + -u1 * vx * (-(-u2) * vy) := by
    have : (1 + u1 * rb) * (1 - -u2 * rb) + -u1 * vx * (-(-u2) * vy) = (1 + x1) * (1 + x2) - P := by
      rw [← hx1_def, ← hx2_def, ← hP_def]; ring
    linarith only [this, hdpp_pos]
  have hd_mm_m : 0 < (1 - u1 * rb) * (1 + -u2 * rb) + -u1 * vx * (-(-u2) * vy) := by
    have : (1 - u1 * rb) * (1 + -u2 * rb) + -u1 * vx * (-(-u2) * vy) = detM := by
      rw [← hdet_def, ← hx1_def, ← hx2_def, ← hP_def]; ring
    linarith only [this, hdetM]
  have hd_mp_p : 0 < (1 - u1 * rb) * (1 - -u2 * rb) - -u1 * vx * (-(-u2) * vy) := by
    have : (1 - u1 * rb) * (1 - -u2 * rb) - -u1 * vx * (-(-u2) * vy) = (1 - x1) * (1 + x2) + P := by
      rw [← hx1_def, ← hx2_def, ← hP_def]; ring
    linarith only [this, mul_pos h1mx1 h1px2, hP_nn]
  have hn1 : 0 ≤ A * B / ((1 + x1) * (1 - x2)) + u2 * vy / 2 * (1 / (1 + x2)) * A ^ 2 +
      u1 * vx / 2 * (1 / ((1 + x1) * (1 - x2) ^ 2)) * B ^ 2 :=
    add_nonneg (add_nonneg (div_nonneg (mul_nonneg hA hB) (mul_pos h1px1 h1mx2).le)
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu2_nn hvy) zero_le_two)
        (div_nonneg zero_le_one h1px2.le)) (sq_nonneg A)))
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu1_nn hvx) zero_le_two)
        (div_nonneg zero_le_one (mul_pos h1px1 (sq_pos_of_pos h1mx2)).le)) (sq_nonneg B))
  have hn2 : 0 ≤ A * B / ((1 + x1) * (1 + x2)) +
      u2 * vy / 2 * (1 / ((1 - x2) * (1 + x1) ^ 2)) * A ^ 2 +
      u1 * vx / 2 * (1 / ((1 - x1) * (1 + x2) ^ 2)) * B ^ 2 :=
    add_nonneg (add_nonneg (div_nonneg (mul_nonneg hA hB) (mul_pos h1px1 h1px2).le)
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu2_nn hvy) zero_le_two)
        (div_nonneg zero_le_one (mul_pos h1mx2 (sq_pos_of_pos h1px1)).le)) (sq_nonneg A)))
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu1_nn hvx) zero_le_two)
        (div_nonneg zero_le_one (mul_pos h1mx1 (sq_pos_of_pos h1px2)).le)) (sq_nonneg B))
  have hn3 : 0 ≤ A * B / detM + u2 * vy / 2 * (1 / ((1 - x1) * detM)) * A ^ 2 +
      u1 * vx / 2 * (1 / ((1 - x2) * detM)) * B ^ 2 :=
    add_nonneg (add_nonneg (div_nonneg (mul_nonneg hA hB) hdetM.le)
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu2_nn hvy) zero_le_two)
        (div_nonneg zero_le_one (mul_pos h1mx1 hdetM).le)) (sq_nonneg A)))
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu1_nn hvx) zero_le_two)
        (div_nonneg zero_le_one (mul_pos h1mx2 hdetM).le)) (sq_nonneg B))
  have hn4 : 0 ≤ A * B / ((1 - x1) * (1 + x2)) +
      u2 * vy / 2 * (1 / ((1 - x1) ^ 2 * (1 + x2))) * A ^ 2 +
      u1 * vx / 2 * (1 / (1 + x1)) * B ^ 2 :=
    add_nonneg (add_nonneg (div_nonneg (mul_nonneg hA hB) (mul_pos h1mx1 h1px2).le)
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu2_nn hvy) zero_le_two)
        (div_nonneg zero_le_one (mul_pos (sq_pos_of_pos h1mx1) h1px2).le)) (sq_nonneg A)))
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hu1_nn hvx) zero_le_two)
        (div_nonneg zero_le_one h1px1.le)) (sq_nonneg B))
  have h1px1' : 0 < 1 + u1 * rb := by rw [hx1_def]; exact h1px1
  have h1mx1' : 0 < 1 - u1 * rb := by rw [hx1_def]; exact h1mx1
  have hd_pm : 0 < 1 + -u2 * rb := by
    have : 1 + -u2 * rb = 1 - x2 := by rw [← hx2_def]; ring
    linarith only [this, h1mx2]
  have hd_mp : 0 < 1 - -u2 * rb := by
    have : 1 - -u2 * rb = 1 + x2 := by rw [← hx2_def]; ring
    linarith only [this, h1px2]
  refine (volume_planarRectSet_le_sum_quadrants u1 (-u2) rb vx vy A B).trans ?_
  obtain ⟨hb_q1, hb_q2, hb_q3, hb_q4⟩ :=
    quadOut_neg_bounds hu1_nn hu2_nn hvx hvy hx1_nn hx2_nn h1mx1 h1px1 h1mx2 h1px2 hdetM
      hP_le_2x hx1_def hx2_def hP_def hdet_def hA hB
  have hq1' := (volume_quadrantRectSet_le_out (-u1 * vx) (-(-u2) * vy) h1px1' h1mx1' hd_pm hd_mp
    hd_pm_p hd_pp_m hd_mm_m hd_mp_p hA hB).trans (ENNReal.ofReal_le_ofReal hb_q1)
  have hq2' := (volume_quadrantRectSet_le_out (u1 * vx) (-(-u2) * vy) h1px1' h1mx1' hd_mp hd_pm
    (by linarith only [hd_pp_m, show u1 * vx * (-(-u2) * vy) = -(-u1 * vx * (-(-u2) * vy)) by ring])
    (by linarith only [hd_pm_p, show u1 * vx * (-(-u2) * vy) = -(-u1 * vx * (-(-u2) * vy)) by ring])
    (by linarith only [hd_mp_p, show u1 * vx * (-(-u2) * vy) = -(-u1 * vx * (-(-u2) * vy)) by ring])
    (by linarith only [hd_mm_m, show u1 * vx * (-(-u2) * vy) = -(-u1 * vx * (-(-u2) * vy)) by ring])
    hA hB).trans (ENNReal.ofReal_le_ofReal hb_q2)
  have hq3' := (volume_quadrantRectSet_le_out (-u1 * vx) ((-u2) * vy) h1mx1' h1px1' hd_pm hd_mp
    (by linarith only [hd_mm_m, show -u1 * vx * ((-u2) * vy) = -(-u1 * vx * (-(-u2) * vy)) by ring])
    (by linarith only [hd_mp_p, show -u1 * vx * ((-u2) * vy) = -(-u1 * vx * (-(-u2) * vy)) by ring])
    (by linarith only [hd_pm_p, show -u1 * vx * ((-u2) * vy) = -(-u1 * vx * (-(-u2) * vy)) by ring])
    (by linarith only [hd_pp_m, show -u1 * vx * ((-u2) * vy) = -(-u1 * vx * (-(-u2) * vy)) by ring])
    hA hB).trans (ENNReal.ofReal_le_ofReal hb_q3)
  have hq4' := (volume_quadrantRectSet_le_out (u1 * vx) ((-u2) * vy) h1mx1' h1px1' hd_mp hd_pm
    (by linarith only [hd_mp_p, show u1 * vx * ((-u2) * vy) = -u1 * vx * (-(-u2) * vy) by ring])
    (by linarith only [hd_mm_m, show u1 * vx * ((-u2) * vy) = -u1 * vx * (-(-u2) * vy) by ring])
    (by linarith only [hd_pp_m, show u1 * vx * ((-u2) * vy) = -u1 * vx * (-(-u2) * vy) by ring])
    (by linarith only [hd_pm_p, show u1 * vx * ((-u2) * vy) = -u1 * vx * (-(-u2) * vy) by ring])
    hA hB).trans (ENNReal.ofReal_le_ofReal hb_q4)
  refine (add_le_add (add_le_add (add_le_add hq1' hq2') hq3') hq4').trans ?_
  rw [← ENNReal.ofReal_add hn1 hn2, ← ENNReal.ofReal_add (add_nonneg hn1 hn2) hn3,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg hn1 hn2) hn3) hn4]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsum_m : (A * B / ((1 + x1) * (1 - x2)) + u2 * vy / 2 * (1 / (1 + x2)) * A ^ 2 +
        u1 * vx / 2 * (1 / ((1 + x1) * (1 - x2) ^ 2)) * B ^ 2) +
      (A * B / ((1 + x1) * (1 + x2)) + u2 * vy / 2 * (1 / ((1 - x2) * (1 + x1) ^ 2)) * A ^ 2 +
        u1 * vx / 2 * (1 / ((1 - x1) * (1 + x2) ^ 2)) * B ^ 2) +
      (A * B / detM + u2 * vy / 2 * (1 / ((1 - x1) * detM)) * A ^ 2 +
        u1 * vx / 2 * (1 / ((1 - x2) * detM)) * B ^ 2) +
      (A * B / ((1 - x1) * (1 + x2)) + u2 * vy / 2 * (1 / ((1 - x1) ^ 2 * (1 + x2))) * A ^ 2 +
        u1 * vx / 2 * (1 / (1 + x1)) * B ^ 2) =
      pairCxm u2 vy x1 x2 detM * A ^ 2 + pairCxm u1 vx x2 x1 detM * B ^ 2 +
      (1 / ((1 + x1) * (1 + x2)) + 1 / ((1 + x1) * (1 - x2)) +
        1 / ((1 - x1) * (1 + x2)) + 1 / detM) * (A * B) := by
    unfold pairCxm; ring
  rw [hsum_m, hcAB_eq]

private theorem volume_planarRectSet_le_out_signed {b1 b2 rb vx vy : ℝ}
    (hrb : 0 < rb) (hvx : 0 ≤ vx) (hvy : 0 ≤ vy)
    (hx1 : |b1| * rb < 1) (hx2 : |b2| * rb < 1)
    (hvxy : vx * vy ≤ 2 * rb ^ 2)
    (hdetM : 0 < (1 - |b1| * rb) * (1 - |b2| * rb) - |b1| * |b2| * vx * vy)
    (ξ η : ℝ) :
    let u1 := |b1|
    let u2 := |b2|
    let x1 := u1 * rb
    let x2 := u2 * rb
    let P := u1 * u2 * vx * vy
    let detM := (1 - x1) * (1 - x2) - P
    (0 ≤ b1 * b2 * ξ * η →
      volume (planarRectSet b1 b2 rb vx vy ξ η) ≤
        ENNReal.ofReal (pairCxp u2 vy x1 x2 detM * ξ ^ 2 +
          pairCxp u1 vx x2 x1 detM * η ^ 2 +
          pairCAB x1 x2 P detM * (|ξ| * |η|))) ∧
    (b1 * b2 * ξ * η ≤ 0 →
      volume (planarRectSet b1 b2 rb vx vy ξ η) ≤
        ENNReal.ofReal (pairCxm u2 vy x1 x2 detM * ξ ^ 2 +
          pairCxm u1 vx x2 x1 detM * η ^ 2 +
          pairCAB x1 x2 P detM * (|ξ| * |η|))) := by
  intro u1 u2 x1 x2 P detM
  have hx1' : x1 < 1 := hx1
  have hx2' : x2 < 1 := hx2
  have hdetM' : 0 < detM := hdetM
  have hu1_nn : 0 ≤ u1 := abs_nonneg b1
  have hu2_nn : 0 ≤ u2 := abs_nonneg b2
  have hx1_nn : 0 ≤ x1 := mul_nonneg hu1_nn hrb.le
  have hx2_nn : 0 ≤ x2 := mul_nonneg hu2_nn hrb.le
  have hP_nn : 0 ≤ P := mul_nonneg (mul_nonneg (mul_nonneg hu1_nn hu2_nn) hvx) hvy
  have h1mx1 : 0 < 1 - x1 := by linarith only [hx1']
  have h1px1 : 0 < 1 + x1 := by linarith only [hx1_nn]
  have h1mx2 : 0 < 1 - x2 := by linarith only [hx2']
  have h1px2 : 0 < 1 + x2 := by linarith only [hx2_nn]
  have hP_le_2x : P ≤ 2 * x1 * x2 := by
    have : P * rb ^ 2 = x1 * x2 * (vx * vy) := by dsimp only [P, x1, x2]; ring
    have hmul : x1 * x2 * (vx * vy) ≤ x1 * x2 * (2 * rb ^ 2) :=
      mul_le_mul_of_nonneg_left hvxy (mul_nonneg hx1_nn hx2_nn)
    have hrb2 : 0 < rb ^ 2 := sq_pos_of_pos hrb
    nlinarith only [this, hmul, hrb2]
  have hdpp_ge_one : 1 ≤ (1 + x1) * (1 + x2) - P := by
    have h2 : 2 * x1 * x2 ≤ x1 + x2 := by
      have : 2 * x1 * x2 ≤ x1 ^ 2 + x2 ^ 2 := by nlinarith only [sq_nonneg (x1 - x2)]
      nlinarith only [this, hx1', hx2', hx1_nn, hx2_nn]
    nlinarith only [h2, hP_le_2x, hx1_nn, hx2_nn]
  have hdpp_pos : 0 < (1 + x1) * (1 + x2) - P := by linarith only [hdpp_ge_one]
  obtain ⟨hcAB_eq, hcAB_p_le⟩ :=
    pairCAB_bounds hx1_nn hx2_nn h1mx1 h1px1 h1mx2 h1px2 hP_nn hdetM' hdpp_pos rfl
  obtain ⟨hsign_p, hsign_m⟩ := volume_planarRectSet_eq_sign b1 b2 rb vx vy ξ η
  have hA : 0 ≤ |ξ| := abs_nonneg ξ
  have hB : 0 ≤ |η| := abs_nonneg η
  rw [← sq_abs ξ, ← sq_abs η]
  refine ⟨fun hp => ?_, fun hm => ?_⟩
  · rw [hsign_p hp]
    exact volume_planarRectSet_le_out_pos hu1_nn hu2_nn hvx hvy hx1_nn hx2_nn h1mx1 h1px1
      h1mx2 h1px2 hP_nn hdetM' hdpp_ge_one rfl rfl rfl rfl hcAB_p_le hA hB
  · rw [hsign_m hm]
    exact volume_planarRectSet_le_out_neg hu1_nn hu2_nn hvx hvy hx1_nn hx2_nn h1mx1 h1px1
      h1mx2 h1px2 hP_nn hdetM' hdpp_pos hP_le_2x rfl rfl rfl rfl hcAB_eq hA hB

theorem volume_planarRectSet_le_out {b1 b2 rb vx vy : ℝ}
    (hrb : 0 < rb) (hvx : 0 ≤ vx) (hvy : 0 ≤ vy)
    (hx1 : |b1| * rb < 1) (hx2 : |b2| * rb < 1)
    (hvxy : vx * vy ≤ 2 * rb ^ 2)
    (hdetM : 0 < (1 - |b1| * rb) * (1 - |b2| * rb) - |b1| * |b2| * vx * vy)
    (ξ η : ℝ) :
    let u1 := |b1|
    let u2 := |b2|
    let x1 := u1 * rb
    let x2 := u2 * rb
    let P := u1 * u2 * vx * vy
    let detM := (1 - x1) * (1 - x2) - P
    volume (planarRectSet b1 b2 rb vx vy ξ η) ≤
      ENNReal.ofReal (pairCxMax u2 vy x1 x2 detM * ξ ^ 2 +
        pairCxMax u1 vx x2 x1 detM * η ^ 2 +
        pairCAB x1 x2 P detM * (|ξ| * |η|)) := by
  intro u1 u2 x1 x2 P detM
  obtain ⟨hp, hm⟩ := volume_planarRectSet_le_out_signed hrb hvx hvy hx1 hx2 hvxy hdetM ξ η
  rcases le_total 0 (b1 * b2 * ξ * η) with h | h
  · refine (hp h).trans (ENNReal.ofReal_le_ofReal ?_)
    have hcx := mul_le_mul_of_nonneg_right
      (le_max_left (pairCxp u2 vy x1 x2 detM) (pairCxm u2 vy x1 x2 detM)) (sq_nonneg ξ)
    have hce := mul_le_mul_of_nonneg_right
      (le_max_left (pairCxp u1 vx x2 x1 detM) (pairCxm u1 vx x2 x1 detM)) (sq_nonneg η)
    unfold pairCxMax; linarith only [hcx, hce]
  · refine (hm h).trans (ENNReal.ofReal_le_ofReal ?_)
    have hcx := mul_le_mul_of_nonneg_right
      (le_max_right (pairCxp u2 vy x1 x2 detM) (pairCxm u2 vy x1 x2 detM)) (sq_nonneg ξ)
    have hce := mul_le_mul_of_nonneg_right
      (le_max_right (pairCxp u1 vx x2 x1 detM) (pairCxm u1 vx x2 x1 detM)) (sq_nonneg η)
    unfold pairCxMax; linarith only [hcx, hce]

theorem volume_planarRectSet_le_in {b1 b2 rb vx vy : ℝ}
    (hrb : 0 < rb) (hvx : 0 ≤ vx) (hvy : 0 ≤ vy)
    (hx1 : |b1| * rb < 1) (hx2 : |b2| * rb < 1)
    (hvxy : vx * vy ≤ 2 * rb ^ 2)
    (hdetM2 : 0 < (1 - |b1| * rb) * (1 - |b2| * rb) - 2 * (|b1| * |b2| * vx * vy))
    (ξ η : ℝ) :
    let D := vx * vy - rb ^ 2
    let u1 := |b1|
    let u2 := |b2|
    let x1 := u1 * rb
    let x2 := u2 * rb
    let P := u1 * u2 * vx * vy
    let detM := (1 - x1) * (1 - x2) - P
    let detM2 := (1 - x1) * (1 - x2) - 2 * P
    let k2 := u2 * vy * (1 - x2) / detM2
    let k1 := u1 * vx * (1 - x1) / detM2
    let cxe := pairCxe b1 b2 rb D
    let cxm := pairCxMax u2 vy x1 x2 detM
    let cem := pairCxMax u1 vx x2 x1 detM
    let cAB := pairCAB x1 x2 P detM
    let tail_cx := cxm + max 0 (cAB - cxe) * k2 + cem * k2 ^ 2
    let tail_ce := cem + max 0 (cAB - cxe) * k1 + cxm * k1 ^ 2
    volume (planarRectSet b1 b2 rb vx vy ξ η) ≤
      ENNReal.ofReal (pairAbsCx2 b1 b2 rb vy D * ξ ^ 2 +
        pairAbsCe2 b1 b2 rb vx D * η ^ 2 + cxe * (|ξ| * |η|) +
        (if |η| < k2 * |ξ| then tail_cx * ξ ^ 2 else 0) +
        (if |ξ| < k1 * |η| then tail_ce * η ^ 2 else 0)) := by
  intro D u1 u2 x1 x2 P detM detM2 k2 k1 cxe cxm cem cAB tail_cx tail_ce
  have hx1' : x1 < 1 := hx1
  have hx2' : x2 < 1 := hx2
  have hdetM2' : 0 < detM2 := hdetM2
  have hP_nn : 0 ≤ P := by positivity
  have hx1_nn : 0 ≤ x1 := mul_nonneg (abs_nonneg b1) hrb.le
  have hx2_nn : 0 ≤ x2 := mul_nonneg (abs_nonneg b2) hrb.le
  have hdetM : 0 < detM := by
    have : detM2 + P = detM := by dsimp only [detM, detM2]; ring
    linarith only [hdetM2', hP_nn, this]
  have h1mx1 : 0 < 1 - x1 := by linarith only [hx1']
  have h1px1 : 0 < 1 + x1 := by linarith only [hx1_nn]
  have h1mx2 : 0 < 1 - x2 := by linarith only [hx2']
  have h1px2 : 0 < 1 + x2 := by linarith only [hx2_nn]
  have hk2_nn : 0 ≤ k2 := div_nonneg (by positivity) hdetM2'.le
  have hk1_nn : 0 ≤ k1 := div_nonneg (by positivity) hdetM2'.le
  have hcxm_nn : 0 ≤ cxm := le_trans (by unfold pairCxp; positivity) (le_max_left _ _)
  have hcem_nn : 0 ≤ cem := le_trans (by unfold pairCxp; positivity) (le_max_left _ _)
  have habs_e1 (e1 : ℝ) (he1 : e1 = 1 ∨ e1 = -1) : |e1 * b1 * rb| = x1 := by
    have he : |e1| = 1 := by rcases he1 with rfl | rfl <;> norm_num
    simp only [abs_mul, he, one_mul, abs_of_pos hrb, x1, u1]
  have habs_e2 (e2 bb2 : ℝ) (he2 : e2 = 1 ∨ e2 = -1) (hbb2 : bb2 = b2 ∨ bb2 = -b2) :
      |e2 * bb2 * rb| = x2 := by
    have he : |e2| = 1 := by rcases he2 with rfl | rfl <;> norm_num
    have hb : |bb2| = u2 := by rcases hbb2 with rfl | rfl <;> simp [u2]
    simp only [abs_mul, he, one_mul, hb, abs_of_pos hrb, x2]
  -- Positivity of `Qp` and `Qm`
  have hd_quad (e1 e2 bb2 : ℝ) (he1 : e1 = 1 ∨ e1 = -1) (he2 : e2 = 1 ∨ e2 = -1)
      (hbb2 : bb2 = b2 ∨ bb2 = -b2) :
      0 < (1 + e1 * b1 * rb) * (1 + e2 * bb2 * rb) - (-e2 * b1 * vx) * (-e1 * bb2 * vy) := by
    have h1 : 1 - x1 ≤ 1 + e1 * b1 * rb := by
      linarith [neg_abs_le (e1 * b1 * rb), habs_e1 e1 he1]
    have h2 : 1 - x2 ≤ 1 + e2 * bb2 * rb := by
      linarith [neg_abs_le (e2 * bb2 * rb), habs_e2 e2 bb2 he2 hbb2]
    have h3 : (-e2 * b1 * vx) * (-e1 * bb2 * vy) ≤ P := by
      have habs : |bb2| = u2 := by rcases hbb2 with rfl | rfl <;> simp [u2]
      have hle := le_abs_self ((-e2 * b1 * vx) * (-e1 * bb2 * vy))
      have he1a : |e1| = 1 := by rcases he1 with rfl | rfl <;> norm_num
      have he2a : |e2| = 1 := by rcases he2 with rfl | rfl <;> norm_num
      have hrewrite : |(-e2 * b1 * vx) * (-e1 * bb2 * vy)| = P := by
        simp only [abs_mul, abs_neg, he1a, he2a, habs, abs_of_nonneg hvx, abs_of_nonneg hvy]
        dsimp [P, u1]; ring
      linarith
    have hmul := mul_le_mul h1 h2 h1mx2.le (by linarith)
    dsimp [detM] at hdetM
    linarith
  have hQp_eq : pairQp b1 b2 rb D =
      ((1 + b1 * rb) * (1 + b2 * rb) - (-b1 * vx) * (-b2 * vy)) *
      ((1 + b1 * rb) * (1 - b2 * rb) - (b1 * vx) * (-b2 * vy)) := by
    unfold pairQp; dsimp [D]; ring
  have hQm_eq : pairQm b1 b2 rb D =
      ((1 - b1 * rb) * (1 + b2 * rb) - (-b1 * vx) * (b2 * vy)) *
      ((1 - b1 * rb) * (1 - b2 * rb) - (b1 * vx) * (b2 * vy)) := by
    unfold pairQm; dsimp [D]; ring
  have hQp_pos : 0 < pairQp b1 b2 rb D := by
    rw [hQp_eq]
    exact mul_pos (by have h := hd_quad 1 1 b2 (Or.inl rfl) (Or.inl rfl) (Or.inl rfl); linarith)
      (by have h := hd_quad 1 (-1) b2 (Or.inl rfl) (Or.inr rfl) (Or.inl rfl); linarith)
  have hQm_pos : 0 < pairQm b1 b2 rb D := by
    rw [hQm_eq]
    exact mul_pos (by have h := hd_quad (-1) 1 b2 (Or.inr rfl) (Or.inl rfl) (Or.inl rfl); linarith)
      (by have h := hd_quad (-1) (-1) b2 (Or.inr rfl) (Or.inr rfl) (Or.inl rfl); linarith)
  have h1pb1 : 0 < 1 + b1 * rb := by
    linarith [neg_abs_le (1 * b1 * rb), habs_e1 1 (Or.inl rfl), h1mx1]
  have h1mb1 : 0 < 1 - b1 * rb := by
    linarith [le_abs_self (1 * b1 * rb), habs_e1 1 (Or.inl rfl), h1mx1]
  have hcxe_nn : 0 ≤ cxe := by dsimp [cxe]; unfold pairCxe; positivity
  have hD_ge : 0 ≤ 1 + b2 ^ 2 * D := by
    have hx2_sq : b2 ^ 2 * rb ^ 2 = x2 ^ 2 := by dsimp [x2, u2]; rw [mul_pow, sq_abs]
    have : 1 + b2 ^ 2 * D = (1 - x2 ^ 2) + b2 ^ 2 * (vx * vy) := by
      dsimp [D]; rw [← hx2_sq]; ring
    rw [this]
    have h1x2 : 0 < 1 - x2 ^ 2 := by nlinarith only [hx2_nn, hx2']
    positivity
  have hD_ge1 : 0 ≤ 1 + b1 ^ 2 * D := by
    have hx1_sq : b1 ^ 2 * rb ^ 2 = x1 ^ 2 := by dsimp [x1, u1]; rw [mul_pow, sq_abs]
    have : 1 + b1 ^ 2 * D = (1 - x1 ^ 2) + b1 ^ 2 * (vx * vy) := by
      dsimp [D]; rw [← hx1_sq]; ring
    rw [this]
    have h1x1 : 0 < 1 - x1 ^ 2 := by nlinarith only [hx1_nn, hx1']
    positivity
  have hcx2_nn : 0 ≤ pairAbsCx2 b1 b2 rb vy D := by unfold pairAbsCx2; positivity
  have hce2_nn : 0 ≤ pairAbsCe2 b1 b2 rb vx D := by unfold pairAbsCe2; positivity
  have htcx_nn : 0 ≤ tail_cx := by dsimp [tail_cx]; positivity
  have htce_nn : 0 ≤ tail_ce := by dsimp [tail_ce]; positivity
  by_cases ht1 : |η| < k2 * |ξ|
  · -- Tail `|η| < k2 * |ξ|`: apply `volume_planarRectSet_le_out`
    refine (volume_planarRectSet_le_out hrb hvx hvy hx1 hx2 hvxy hdetM ξ η).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    change cxm * ξ ^ 2 + cem * η ^ 2 + cAB * (|ξ| * |η|) ≤ _
    simp only [ht1, ↓reduceIte]
    have ht2_nn : 0 ≤ (if |ξ| < k1 * |η| then tail_ce * η ^ 2 else 0) := by
      split_ifs <;> positivity
    have hη_sq : cem * η ^ 2 ≤ cem * (k2 ^ 2 * ξ ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hcem_nn
      rw [← sq_abs η, ← sq_abs ξ]
      have := mul_le_mul ht1.le ht1.le (abs_nonneg η) (mul_nonneg hk2_nn (abs_nonneg ξ))
      linarith [show k2 * |ξ| * (k2 * |ξ|) = k2 ^ 2 * |ξ| ^ 2 by ring]
    have hdiff : cAB * (|ξ| * |η|) - cxe * (|ξ| * |η|) ≤ max 0 (cAB - cxe) * k2 * ξ ^ 2 := by
      calc cAB * (|ξ| * |η|) - cxe * (|ξ| * |η|)
          = (cAB - cxe) * (|ξ| * |η|) := by ring
        _ ≤ max 0 (cAB - cxe) * (|ξ| * |η|) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ ≤ max 0 (cAB - cxe) * (|ξ| * (k2 * |ξ|)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht1.le (abs_nonneg ξ))
              (le_max_left _ _)
        _ = max 0 (cAB - cxe) * k2 * ξ ^ 2 := by rw [← sq_abs ξ]; ring
    have hexp : tail_cx * ξ ^ 2 =
        cxm * ξ ^ 2 + max 0 (cAB - cxe) * k2 * ξ ^ 2 + cem * (k2 ^ 2 * ξ ^ 2) := by
      dsimp only [tail_cx]; ring
    linarith only [ht2_nn, hη_sq, hdiff, hexp,
      mul_nonneg hcx2_nn (sq_nonneg ξ), mul_nonneg hce2_nn (sq_nonneg η)]
  · by_cases ht2 : |ξ| < k1 * |η|
    · -- Tail `|ξ| < k1 * |η|`: apply `volume_planarRectSet_le_out`
      refine (volume_planarRectSet_le_out hrb hvx hvy hx1 hx2 hvxy hdetM ξ η).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      change cxm * ξ ^ 2 + cem * η ^ 2 + cAB * (|ξ| * |η|) ≤ _
      simp only [ht1, ht2, ↓reduceIte, add_zero]
      have hξ_sq : cxm * ξ ^ 2 ≤ cxm * (k1 ^ 2 * η ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hcxm_nn
        rw [← sq_abs ξ, ← sq_abs η]
        have := mul_le_mul ht2.le ht2.le (abs_nonneg ξ) (mul_nonneg hk1_nn (abs_nonneg η))
        linarith [show k1 * |η| * (k1 * |η|) = k1 ^ 2 * |η| ^ 2 by ring]
      have hdiff : cAB * (|ξ| * |η|) - cxe * (|ξ| * |η|) ≤ max 0 (cAB - cxe) * k1 * η ^ 2 := by
        calc cAB * (|ξ| * |η|) - cxe * (|ξ| * |η|)
            = (cAB - cxe) * (|ξ| * |η|) := by ring
          _ ≤ max 0 (cAB - cxe) * (|ξ| * |η|) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
          _ ≤ max 0 (cAB - cxe) * ((k1 * |η|) * |η|) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht2.le (abs_nonneg η))
                (le_max_left _ _)
          _ = max 0 (cAB - cxe) * k1 * η ^ 2 := by rw [← sq_abs η]; ring
      have hexp : tail_ce * η ^ 2 =
          cem * η ^ 2 + max 0 (cAB - cxe) * k1 * η ^ 2 + cxm * (k1 ^ 2 * η ^ 2) := by
        dsimp only [tail_ce]; ring
      linarith only [hξ_sq, hdiff, hexp,
        mul_nonneg hcx2_nn (sq_nonneg ξ), mul_nonneg hce2_nn (sq_nonneg η)]
    · -- Interior `k2 * |ξ| ≤ |η| ∧ k1 * |η| ≤ |ξ|`: apply `volume_quad_shoelace_le`
      simp only [ht1, ht2, ↓reduceIte, add_zero]
      have hBA : k2 * |ξ| ≤ |η| := not_lt.mp ht1
      have hAB : k1 * |η| ≤ |ξ| := not_lt.mp ht2
      obtain ⟨bb2, hbb2_cases, hvol_abs⟩ := volume_planarRectSet_abs_xi b1 b2 rb vx vy ξ η
      rw [hvol_abs]; clear hvol_abs
      set A := |ξ|
      set B := |η|
      have hA : 0 ≤ A := abs_nonneg ξ
      have hB : 0 ≤ B := abs_nonneg η
      have habs_bb2 : |bb2| = u2 := by rcases hbb2_cases with rfl | rfl <;> simp [u2]
      have hbb2_sq : bb2 ^ 2 = b2 ^ 2 := by rcases hbb2_cases with rfl | rfl <;> ring
      -- Helper: on any quadrant `(e1, e2)` in the interior cone, reflected branches are empty
      have hquad_shoelace (e1 e2 : ℝ) (he1 : e1 = 1 ∨ e1 = -1) (he2 : e2 = 1 ∨ e2 = -1) :
          let m00 := 1 + e1 * b1 * rb
          let m00p := 1 - e1 * b1 * rb
          let m01 := -e2 * b1 * vx
          let m10 := -e1 * bb2 * vy
          let m11 := 1 + e2 * bb2 * rb
          let m11p := 1 - e2 * bb2 * rb
          let dM := m00 * m11 - m01 * m10
          volume (quadrantRectSet m00 m00p m01 m10 m11 m11p A B) ≤
            ENNReal.ofReal (A * B / dM - m10 * A ^ 2 / (2 * m00 * dM) -
              m01 * B ^ 2 / (2 * m11 * dM)) := by
        intro m00 m00p m01 m10 m11 m11p dM
        have hm00_ge : 1 - x1 ≤ m00 := by
          dsimp [m00]; linarith [neg_abs_le (e1 * b1 * rb), habs_e1 e1 he1]
        have hm00p_ge : 1 - x1 ≤ m00p := by
          dsimp [m00p]; linarith [le_abs_self (e1 * b1 * rb), habs_e1 e1 he1]
        have hm11_ge : 1 - x2 ≤ m11 := by
          dsimp [m11]; linarith [neg_abs_le (e2 * bb2 * rb), habs_e2 e2 bb2 he2 hbb2_cases]
        have hm11p_ge : 1 - x2 ≤ m11p := by
          dsimp [m11p]; linarith [le_abs_self (e2 * bb2 * rb), habs_e2 e2 bb2 he2 hbb2_cases]
        have hm01_abs : |m01| = u1 * vx := by
          dsimp [m01, u1]; rcases he2 with rfl | rfl <;> simp [abs_mul, abs_of_nonneg hvx]
        have hm10_abs : |m10| = u2 * vy := by
          dsimp [m10]; rcases he1 with rfl | rfl <;> simp [abs_mul, habs_bb2, abs_of_nonneg hvy]
        have hm01_le : m01 ≤ u1 * vx := (le_abs_self m01).trans_eq hm01_abs
        have hnm01_le : -m01 ≤ u1 * vx := (neg_le_abs m01).trans_eq hm01_abs
        have hm10_le : m10 ≤ u2 * vy := (le_abs_self m10).trans_eq hm10_abs
        have hnm10_le : -m10 ≤ u2 * vy := (neg_le_abs m10).trans_eq hm10_abs
        have hdM_pos : 0 < dM := hd_quad e1 e2 bb2 he1 he2 hbb2_cases
        have hk1_ineq : u1 * vx * (1 - x1) * B ≤ detM2 * A := by
          have hk1_rw : k1 * B = u1 * vx * (1 - x1) * B / detM2 := by dsimp only [k1]; ring
          exact mul_comm A detM2 ▸ (div_le_iff₀ hdetM2').mp (hk1_rw ▸ hAB)
        have hk2_ineq : u2 * vy * (1 - x2) * A ≤ detM2 * B := by
          have hk2_rw : k2 * A = u2 * vy * (1 - x2) * A / detM2 := by dsimp only [k2]; ring
          exact mul_comm B detM2 ▸ (div_le_iff₀ hdetM2').mp (hk2_rw ▸ hBA)
        have hdet_le_prod : detM2 ≤ (1 - x1) * (1 - x2) := by
          dsimp only [detM2]; linarith only [hP_nn]
        have hu1B_le : u1 * vx * B ≤ (1 - x2) * A := by
          have hmul1 : u1 * vx * (1 - x1) * B ≤ (1 - x1) * ((1 - x2) * A) := by
            calc u1 * vx * (1 - x1) * B ≤ detM2 * A := hk1_ineq
              _ ≤ ((1 - x1) * (1 - x2)) * A := mul_le_mul_of_nonneg_right hdet_le_prod hA
              _ = (1 - x1) * ((1 - x2) * A) := by ring
          exact le_of_mul_le_mul_left (by linarith only [hmul1,
            show (1 - x1) * (u1 * vx * B) = u1 * vx * (1 - x1) * B by ring]) h1mx1
        have hu2A_le : u2 * vy * A ≤ (1 - x1) * B := by
          have hmul2 : u2 * vy * (1 - x2) * A ≤ (1 - x2) * ((1 - x1) * B) := by
            calc u2 * vy * (1 - x2) * A ≤ detM2 * B := hk2_ineq
              _ ≤ ((1 - x1) * (1 - x2)) * B := mul_le_mul_of_nonneg_right hdet_le_prod hB
              _ = (1 - x2) * ((1 - x1) * B) := by ring
          exact le_of_mul_le_mul_left (by linarith only [hmul2,
            show (1 - x2) * (u2 * vy * A) = u2 * vy * (1 - x2) * A by ring]) h1mx2
        have hsub : quadrantRectSet m00 m00p m01 m10 m11 m11p A B ⊆
            {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ m00 * p.1 + m01 * p.2 < A ∧ m10 * p.1 + m11 * p.2 < B} := by
          rintro p ⟨hp1, hp2, h1, h2⟩
          have hb1_unif : (1 - x1) * p.1 - u1 * vx * p.2 < A := by
            rcases h1 with h1 | h1
            · linarith only [h1, hA, mul_le_mul_of_nonneg_right hm00_ge hp1,
                mul_le_mul_of_nonneg_right hnm01_le hp2]
            · linarith only [h1, hA, mul_le_mul_of_nonneg_right hm00p_ge hp1,
                mul_le_mul_of_nonneg_right hm01_le hp2]
          have hb2_unif : -u2 * vy * p.1 + (1 - x2) * p.2 < B := by
            rcases h2 with h2 | h2
            · linarith only [h2, hB, mul_le_mul_of_nonneg_right hm11_ge hp2,
                mul_le_mul_of_nonneg_right hnm10_le hp1]
            · linarith only [h2, hB, mul_le_mul_of_nonneg_right hm11p_ge hp2,
                mul_le_mul_of_nonneg_right hm10_le hp1]
          have hp2_ub : detM * p.2 < (1 - x1) * B + u2 * vy * A := by
            have hc1 := mul_lt_mul_of_pos_left hb2_unif h1mx1
            have hc2 := mul_le_mul_of_nonneg_left hb1_unif.le (mul_nonneg (abs_nonneg b2) hvy)
            have hid_p2 : (1 - x1) * (-u2 * vy * p.1 + (1 - x2) * p.2) +
                u2 * vy * ((1 - x1) * p.1 - u1 * vx * p.2) = detM * p.2 := by
              dsimp only [detM, P, u2]; ring
            have hrhs_p2 : (1 - x1) * B + u2 * vy * A = (1 - x1) * B + |b2| * vy * A := rfl
            linarith only [hc1, hc2, hid_p2, hrhs_p2]
          have hp1_ub : detM * p.1 < (1 - x2) * A + u1 * vx * B := by
            have hc1 := mul_lt_mul_of_pos_left hb1_unif h1mx2
            have hc2 := mul_le_mul_of_nonneg_left hb2_unif.le (mul_nonneg (abs_nonneg b1) hvx)
            have hid_p1 : (1 - x2) * ((1 - x1) * p.1 - u1 * vx * p.2) +
                u1 * vx * (-u2 * vy * p.1 + (1 - x2) * p.2) = detM * p.1 := by
              dsimp only [detM, P, u1]; ring
            have hrhs_p1 : (1 - x2) * A + u1 * vx * B = (1 - x2) * A + |b1| * vx * B := rfl
            linarith only [hc1, hc2, hid_p1, hrhs_p1]
          have hN1_false : ¬(m00p * p.1 - m01 * p.2 < -A) := by
            intro hn1
            have hstep1 : u1 * vx * (detM * p.2) ≤ u1 * vx * ((1 - x1) * B + u2 * vy * A) :=
              mul_le_mul_of_nonneg_left hp2_ub.le (mul_nonneg (abs_nonneg b1) hvx)
            have hid : detM2 * (u1 * vx * ((1 - x1) * B + u2 * vy * A)) ≤
                detM2 * (detM * A) := by
              have hrew2 : detM2 * (u1 * vx * ((1 - x1) * B + u2 * vy * A)) =
                  detM2 * (u1 * vx * (1 - x1) * B) + detM2 * P * A := by
                dsimp only [P]; ring
              have hsum_det : detM2 + P = detM := by dsimp only [detM, detM2]; ring
              have hm_k1 : detM2 * (u1 * vx * (1 - x1) * B) ≤ detM2 * (detM2 * A) :=
                mul_le_mul_of_nonneg_left hk1_ineq hdetM2'.le
              have hrhs_rew : detM2 * (detM2 * A) + detM2 * P * A = detM2 * (detM * A) := by
                rw [← hsum_det]; ring
              linarith only [hrew2, hm_k1, hrhs_rew]
            have hu1p2_det : detM * (u1 * vx * p.2) ≤ detM * A := by
              have hle' := le_of_mul_le_mul_left
                (le_trans (mul_le_mul_of_nonneg_left hstep1 hdetM2'.le) hid) hdetM2'
              linarith only [hle', show u1 * vx * (detM * p.2) = detM * (u1 * vx * p.2) by ring]
            have hu1p2 : u1 * vx * p.2 ≤ A := le_of_mul_le_mul_left hu1p2_det hdetM
            linarith only [hn1, hu1p2, mul_nonneg (le_trans h1mx1.le hm00p_ge) hp1,
              mul_le_mul_of_nonneg_right hm01_le hp2]
          have hN2_false : ¬(-m10 * p.1 + m11p * p.2 < -B) := by
            intro hn2
            have hstep1 : u2 * vy * (detM * p.1) ≤ u2 * vy * ((1 - x2) * A + u1 * vx * B) :=
              mul_le_mul_of_nonneg_left hp1_ub.le (mul_nonneg (abs_nonneg b2) hvy)
            have hid : detM2 * (u2 * vy * ((1 - x2) * A + u1 * vx * B)) ≤
                detM2 * (detM * B) := by
              have hrew2 : detM2 * (u2 * vy * ((1 - x2) * A + u1 * vx * B)) =
                  detM2 * (u2 * vy * (1 - x2) * A) + detM2 * P * B := by
                dsimp only [P]; ring
              have hsum_det : detM2 + P = detM := by dsimp only [detM, detM2]; ring
              have hm_k2 : detM2 * (u2 * vy * (1 - x2) * A) ≤ detM2 * (detM2 * B) :=
                mul_le_mul_of_nonneg_left hk2_ineq hdetM2'.le
              have hrhs_rew : detM2 * (detM2 * B) + detM2 * P * B = detM2 * (detM * B) := by
                rw [← hsum_det]; ring
              linarith only [hrew2, hm_k2, hrhs_rew]
            have hu2p1_det : detM * (u2 * vy * p.1) ≤ detM * B := by
              have hle' := le_of_mul_le_mul_left
                (le_trans (mul_le_mul_of_nonneg_left hstep1 hdetM2'.le) hid) hdetM2'
              linarith only [hle', show u2 * vy * (detM * p.1) = detM * (u2 * vy * p.1) by ring]
            have hu2p1 : u2 * vy * p.1 ≤ B := le_of_mul_le_mul_left hu2p1_det hdetM
            linarith only [hn2, hu2p1, mul_nonneg (le_trans h1mx2.le hm11p_ge) hp2,
              mul_le_mul_of_nonneg_right hm10_le hp1]
          exact ⟨hp1, hp2, h1.resolve_right hN1_false, h2.resolve_right hN2_false⟩
        have hu_nn : 0 ≤ (m11 * A - m01 * B) / dM :=
          div_nonneg (by linarith only [hu1B_le, mul_le_mul_of_nonneg_right hm11_ge hA,
            mul_le_mul_of_nonneg_right hm01_le hB]) hdM_pos.le
        have hv_nn : 0 ≤ (m00 * B - m10 * A) / dM :=
          div_nonneg (by linarith only [hu2A_le, mul_le_mul_of_nonneg_right hm00_ge hB,
            mul_le_mul_of_nonneg_right hm10_le hA]) hdM_pos.le
        exact (measure_mono hsub).trans (volume_quad_shoelace_le
          (lt_of_lt_of_le h1mx1 hm00_ge) (lt_of_lt_of_le h1mx2 hm11_ge) hdM_pos hA hB hu_nn hv_nn)
      -- Each shoelace RHS is nonnegative
      have hshoe_nn (e1 e2 : ℝ) (he1 : e1 = 1 ∨ e1 = -1) (he2 : e2 = 1 ∨ e2 = -1) :
          let m00 := 1 + e1 * b1 * rb
          let m01 := -e2 * b1 * vx
          let m10 := -e1 * bb2 * vy
          let m11 := 1 + e2 * bb2 * rb
          let dM := m00 * m11 - m01 * m10
          0 ≤ A * B / dM - m10 * A ^ 2 / (2 * m00 * dM) - m01 * B ^ 2 / (2 * m11 * dM) := by
        intro m00 m01 m10 m11 dM
        have hm00 : 1 - x1 ≤ m00 := by
          dsimp [m00]; linarith [neg_abs_le (e1 * b1 * rb), habs_e1 e1 he1]
        have hm11 : 1 - x2 ≤ m11 := by
          dsimp [m11]; linarith [neg_abs_le (e2 * bb2 * rb), habs_e2 e2 bb2 he2 hbb2_cases]
        have hm01_le : m01 ≤ u1 * vx := by
          dsimp [m01, u1]; rcases he2 with rfl | rfl <;>
            exact (le_abs_self _).trans_eq (by simp [abs_mul, abs_of_nonneg hvx])
        have hm10_le : m10 ≤ u2 * vy := by
          dsimp [m10]; rcases he1 with rfl | rfl <;>
            exact (le_abs_self _).trans_eq (by simp [abs_mul, habs_bb2, abs_of_nonneg hvy])
        have hdM : 0 < dM := hd_quad e1 e2 bb2 he1 he2 hbb2_cases
        have hk1_ineq : u1 * vx * (1 - x1) * B ≤ detM2 * A := by
          have hk1_rw : k1 * B = u1 * vx * (1 - x1) * B / detM2 := by dsimp only [k1]; ring
          exact mul_comm A detM2 ▸ (div_le_iff₀ hdetM2').mp (hk1_rw ▸ hAB)
        have hk2_ineq : u2 * vy * (1 - x2) * A ≤ detM2 * B := by
          have hk2_rw : k2 * A = u2 * vy * (1 - x2) * A / detM2 := by dsimp only [k2]; ring
          exact mul_comm B detM2 ▸ (div_le_iff₀ hdetM2').mp (hk2_rw ▸ hBA)
        have hdet_le_prod : detM2 ≤ (1 - x1) * (1 - x2) := by
          dsimp only [detM2]; linarith only [hP_nn]
        have hu1B_le : u1 * vx * B ≤ (1 - x2) * A := by
          have hmul1 : u1 * vx * (1 - x1) * B ≤ (1 - x1) * ((1 - x2) * A) := by
            calc u1 * vx * (1 - x1) * B ≤ detM2 * A := hk1_ineq
              _ ≤ ((1 - x1) * (1 - x2)) * A := mul_le_mul_of_nonneg_right hdet_le_prod hA
              _ = (1 - x1) * ((1 - x2) * A) := by ring
          exact le_of_mul_le_mul_left (by linarith only [hmul1,
            show (1 - x1) * (u1 * vx * B) = u1 * vx * (1 - x1) * B by ring]) h1mx1
        have hu2A_le : u2 * vy * A ≤ (1 - x1) * B := by
          have hmul2 : u2 * vy * (1 - x2) * A ≤ (1 - x2) * ((1 - x1) * B) := by
            calc u2 * vy * (1 - x2) * A ≤ detM2 * B := hk2_ineq
              _ ≤ ((1 - x1) * (1 - x2)) * B := mul_le_mul_of_nonneg_right hdet_le_prod hB
              _ = (1 - x2) * ((1 - x1) * B) := by ring
          exact le_of_mul_le_mul_left (by linarith only [hmul2,
            show (1 - x2) * (u2 * vy * A) = u2 * vy * (1 - x2) * A by ring]) h1mx2
        have hu_nn : 0 ≤ m11 * A - m01 * B :=
          by linarith only [hu1B_le, mul_le_mul_of_nonneg_right hm11 hA,
            mul_le_mul_of_nonneg_right hm01_le hB]
        have hv_nn : 0 ≤ m00 * B - m10 * A :=
          by linarith only [hu2A_le, mul_le_mul_of_nonneg_right hm00 hB,
            mul_le_mul_of_nonneg_right hm10_le hA]
        have hm00_pos : 0 < m00 := lt_of_lt_of_le h1mx1 hm00
        have hm11_pos : 0 < m11 := lt_of_lt_of_le h1mx2 hm11
        have hid : A * B / dM - m10 * A ^ 2 / (2 * m00 * dM) - m01 * B ^ 2 / (2 * m11 * dM) =
            A * (m00 * B - m10 * A) / (2 * m00 * dM) +
            B * (m11 * A - m01 * B) / (2 * m11 * dM) := by
          generalize hg0 : m00 = g0; generalize hg1 : m11 = g1; generalize hgd : dM = gd
          have hg0' : g0 ≠ 0 := by rw [← hg0]; exact hm00_pos.ne'
          have hg1' : g1 ≠ 0 := by rw [← hg1]; exact hm11_pos.ne'
          have hgd' : gd ≠ 0 := by rw [← hgd]; exact hdM.ne'
          field_simp [hg0', hg1', hgd']; ring
        rw [hid]; positivity
      have h1 := hquad_shoelace 1 1 (Or.inl rfl) (Or.inl rfl)
      have h2 := hquad_shoelace 1 (-1) (Or.inl rfl) (Or.inr rfl)
      have h3 := hquad_shoelace (-1) 1 (Or.inr rfl) (Or.inl rfl)
      have h4 := hquad_shoelace (-1) (-1) (Or.inr rfl) (Or.inr rfl)
      simp only [one_mul, neg_one_mul, neg_neg] at h1 h2 h3 h4
      have hsub_b1 : 1 + -b1 * rb = 1 - b1 * rb := by ring
      have hadd_b1 : 1 - -b1 * rb = 1 + b1 * rb := by ring
      have hsub_b2 : 1 + -bb2 * rb = 1 - bb2 * rb := by ring
      have hadd_b2 : 1 - -bb2 * rb = 1 + bb2 * rb := by ring
      rw [hsub_b2, hadd_b2] at h2
      rw [hsub_b1, hadd_b1] at h3
      rw [hsub_b1, hadd_b1, hsub_b2, hadd_b2] at h4
      have hn1 := hshoe_nn 1 1 (Or.inl rfl) (Or.inl rfl)
      have hn2 := hshoe_nn 1 (-1) (Or.inl rfl) (Or.inr rfl)
      have hn3 := hshoe_nn (-1) 1 (Or.inr rfl) (Or.inl rfl)
      have hn4 := hshoe_nn (-1) (-1) (Or.inr rfl) (Or.inr rfl)
      simp only [one_mul, neg_one_mul, neg_neg] at hn1 hn2 hn3 hn4
      rw [hsub_b2] at hn2
      rw [hsub_b1] at hn3
      rw [hsub_b1, hsub_b2] at hn4
      refine (volume_planarRectSet_le_sum_quadrants b1 bb2 rb vx vy A B).trans ?_
      refine (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans ?_
      rw [← ENNReal.ofReal_add hn1 hn2, ← ENNReal.ofReal_add (add_nonneg hn1 hn2) hn3,
        ← ENNReal.ofReal_add (add_nonneg (add_nonneg hn1 hn2) hn3) hn4]
      refine ENNReal.ofReal_le_ofReal ?_
      -- Exact 4-quadrant rational sum identity!
      set d11 := (1 + b1 * rb) * (1 + bb2 * rb) - (-b1 * vx) * (-bb2 * vy)
      set d12 := (1 + b1 * rb) * (1 - bb2 * rb) - (b1 * vx) * (-bb2 * vy)
      set d21 := (1 - b1 * rb) * (1 + bb2 * rb) - (-b1 * vx) * (bb2 * vy)
      set d22 := (1 - b1 * rb) * (1 - bb2 * rb) - (b1 * vx) * (bb2 * vy)
      have hd11 : 0 < d11 := by
        have h := hd_quad 1 1 bb2 (Or.inl rfl) (Or.inl rfl) hbb2_cases
        dsimp only [d11]; linarith only [h]
      have hd12 : 0 < d12 := by
        have h := hd_quad 1 (-1) bb2 (Or.inl rfl) (Or.inr rfl) hbb2_cases
        dsimp only [d12]; linarith only [h]
      have hd21 : 0 < d21 := by
        have h := hd_quad (-1) 1 bb2 (Or.inr rfl) (Or.inl rfl) hbb2_cases
        dsimp only [d21]; linarith only [h]
      have hd22 : 0 < d22 := by
        have h := hd_quad (-1) (-1) bb2 (Or.inr rfl) (Or.inr rfl) hbb2_cases
        dsimp only [d22]; linarith only [h]
      have h1pbb2 : 0 < 1 + bb2 * rb := by
        linarith only [neg_abs_le (1 * bb2 * rb), habs_e2 1 bb2 (Or.inl rfl) hbb2_cases, h1mx2]
      have h1mbb2 : 0 < 1 - bb2 * rb := by
        linarith only [le_abs_self (1 * bb2 * rb), habs_e2 1 bb2 (Or.inl rfl) hbb2_cases, h1mx2]
      have hQp_d : d11 * d12 = pairQp b1 b2 rb D := by
        unfold pairQp; dsimp [d11, d12, D]
        calc ((1 + b1 * rb) * (1 + bb2 * rb) - -b1 * vx * (-bb2 * vy)) *
              ((1 + b1 * rb) * (1 - bb2 * rb) - b1 * vx * (-bb2 * vy))
            = (1 + b1 * rb) ^ 2 - bb2 ^ 2 * (rb - b1 * (vx * vy - rb ^ 2)) ^ 2 := by ring
          _ = (1 + b1 * rb) ^ 2 - b2 ^ 2 * (rb - b1 * (vx * vy - rb ^ 2)) ^ 2 := by rw [hbb2_sq]
      have hQm_d : d21 * d22 = pairQm b1 b2 rb D := by
        unfold pairQm; dsimp [d21, d22, D]
        calc ((1 - b1 * rb) * (1 + bb2 * rb) - -b1 * vx * (bb2 * vy)) *
              ((1 - b1 * rb) * (1 - bb2 * rb) - b1 * vx * (bb2 * vy))
            = (1 - b1 * rb) ^ 2 - bb2 ^ 2 * (rb + b1 * (vx * vy - rb ^ 2)) ^ 2 := by ring
          _ = (1 - b1 * rb) ^ 2 - b2 ^ 2 * (rb + b1 * (vx * vy - rb ^ 2)) ^ 2 := by rw [hbb2_sq]
      have h_cxe_id : 1 / d11 + 1 / d12 + 1 / d21 + 1 / d22 = cxe := by
        dsimp only [cxe]; unfold pairCxe
        rw [← hQp_d, ← hQm_d]
        generalize ha11 : d11 = a11; generalize ha12 : d12 = a12
        generalize ha21 : d21 = a21; generalize ha22 : d22 = a22
        have ne11 : a11 ≠ 0 := by rw [← ha11]; exact hd11.ne'
        have ne12 : a12 ≠ 0 := by rw [← ha12]; exact hd12.ne'
        have ne21 : a21 ≠ 0 := by rw [← ha21]; exact hd21.ne'
        have ne22 : a22 ≠ 0 := by rw [← ha22]; exact hd22.ne'
        field_simp [ne11, ne12, ne21, ne22]
        subst ha11 ha12 ha21 ha22
        dsimp only [d11, d12, d21, d22]; ring
      have h_cx2_id : -(-bb2 * vy) / (2 * (1 + b1 * rb) * d11) -
          (-bb2 * vy) / (2 * (1 + b1 * rb) * d12) -
          (bb2 * vy) / (2 * (1 - b1 * rb) * d21) -
          (bb2 * vy) / (2 * (1 - b1 * rb) * d22) =
          -4 * b1 * bb2 * rb * vy * (1 + b2 ^ 2 * D) /
            (pairQp b1 b2 rb D * pairQm b1 b2 rb D) := by
        rw [← hQp_d, ← hQm_d, ← hbb2_sq]
        generalize ha11 : d11 = a11; generalize ha12 : d12 = a12
        generalize ha21 : d21 = a21; generalize ha22 : d22 = a22
        have ne11 : a11 ≠ 0 := by rw [← ha11]; exact hd11.ne'
        have ne12 : a12 ≠ 0 := by rw [← ha12]; exact hd12.ne'
        have ne21 : a21 ≠ 0 := by rw [← ha21]; exact hd21.ne'
        have ne22 : a22 ≠ 0 := by rw [← ha22]; exact hd22.ne'
        field_simp [h1pb1.ne', h1mb1.ne', ne11, ne12, ne21, ne22]
        subst ha11 ha12 ha21 ha22
        dsimp only [d11, d12, d21, d22, D]; ring
      have h_ce2_id : -(-b1 * vx) / (2 * (1 + bb2 * rb) * d11) -
          (b1 * vx) / (2 * (1 - bb2 * rb) * d12) -
          (-b1 * vx) / (2 * (1 + bb2 * rb) * d21) -
          (b1 * vx) / (2 * (1 - bb2 * rb) * d22) =
          -4 * b1 * bb2 * rb * vx * (1 + b1 ^ 2 * D) /
            (pairQp b1 b2 rb D * pairQm b1 b2 rb D) := by
        rw [← hQp_d, ← hQm_d]
        generalize ha11 : d11 = a11; generalize ha12 : d12 = a12
        generalize ha21 : d21 = a21; generalize ha22 : d22 = a22
        have ne11 : a11 ≠ 0 := by rw [← ha11]; exact hd11.ne'
        have ne12 : a12 ≠ 0 := by rw [← ha12]; exact hd12.ne'
        have ne21 : a21 ≠ 0 := by rw [← ha21]; exact hd21.ne'
        have ne22 : a22 ≠ 0 := by rw [← ha22]; exact hd22.ne'
        field_simp [h1pbb2.ne', h1mbb2.ne', ne11, ne12, ne21, ne22]
        subst ha11 ha12 ha21 ha22
        dsimp only [d11, d12, d21, d22, D]; ring
      have hb1bb2_le : -b1 * bb2 ≤ |b1| * |b2| := by
        calc -b1 * bb2 ≤ |-b1 * bb2| := le_abs_self _
          _ = |b1| * |b2| := by rw [abs_mul, abs_neg, habs_bb2]
      have hcx2_le : -4 * b1 * bb2 * rb * vy * (1 + b2 ^ 2 * D) /
            (pairQp b1 b2 rb D * pairQm b1 b2 rb D) ≤ pairAbsCx2 b1 b2 rb vy D := by
        unfold pairAbsCx2
        refine div_le_div_of_nonneg_right ?_ (mul_pos hQp_pos hQm_pos).le
        nlinarith only [hb1bb2_le, mul_nonneg (mul_nonneg hrb.le hvy) hD_ge]
      have hce2_le : -4 * b1 * bb2 * rb * vx * (1 + b1 ^ 2 * D) /
            (pairQp b1 b2 rb D * pairQm b1 b2 rb D) ≤ pairAbsCe2 b1 b2 rb vx D := by
        unfold pairAbsCe2
        refine div_le_div_of_nonneg_right ?_ (mul_pos hQp_pos hQm_pos).le
        nlinarith only [hb1bb2_le, mul_nonneg (mul_nonneg hrb.le hvx) hD_ge1]
      have hsum_eq : (A * B / d11 - (-bb2 * vy) * A ^ 2 / (2 * (1 + b1 * rb) * d11) -
            (-b1 * vx) * B ^ 2 / (2 * (1 + bb2 * rb) * d11)) +
          (A * B / d12 - (-bb2 * vy) * A ^ 2 / (2 * (1 + b1 * rb) * d12) -
            (b1 * vx) * B ^ 2 / (2 * (1 - bb2 * rb) * d12)) +
          (A * B / d21 - (bb2 * vy) * A ^ 2 / (2 * (1 - b1 * rb) * d21) -
            (-b1 * vx) * B ^ 2 / (2 * (1 + bb2 * rb) * d21)) +
          (A * B / d22 - (bb2 * vy) * A ^ 2 / (2 * (1 - b1 * rb) * d22) -
            (b1 * vx) * B ^ 2 / (2 * (1 - bb2 * rb) * d22)) =
          (1 / d11 + 1 / d12 + 1 / d21 + 1 / d22) * (A * B) +
          (-(-bb2 * vy) / (2 * (1 + b1 * rb) * d11) -
            (-bb2 * vy) / (2 * (1 + b1 * rb) * d12) -
            (bb2 * vy) / (2 * (1 - b1 * rb) * d21) -
            (bb2 * vy) / (2 * (1 - b1 * rb) * d22)) * A ^ 2 +
          (-(-b1 * vx) / (2 * (1 + bb2 * rb) * d11) -
            (b1 * vx) / (2 * (1 - bb2 * rb) * d12) -
            (-b1 * vx) / (2 * (1 + bb2 * rb) * d21) -
            (b1 * vx) / (2 * (1 - bb2 * rb) * d22)) * B ^ 2 := by ring
      rw [hsum_eq, h_cxe_id, h_cx2_id, h_ce2_id]
      have hA2 : A ^ 2 = ξ ^ 2 := sq_abs ξ
      have hB2 : B ^ 2 = η ^ 2 := sq_abs η
      rw [hA2, hB2]
      have h1_le := mul_le_mul_of_nonneg_right hcx2_le (sq_nonneg ξ)
      have h2_le := mul_le_mul_of_nonneg_right hce2_le (sq_nonneg η)
      have hAB_def : A * B = |ξ| * |η| := rfl
      rw [hAB_def]
      linarith only [h1_le, h2_le]

end Cslib.Circuits.Frontier.Gaussian.PairBound
