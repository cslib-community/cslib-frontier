/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate (addition to `Cslib/Probability/StatisticalDistance.lean`)

public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Probability.PMF
public import CslibFrontier.Probability.StatisticalDistance
public import CslibFrontier.Probability.StatisticalDistance.TotalVariation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.ToReal

/-!
# The coupling inequality and approximate couplings

Two functions of one sample are at statistical distance at most the probability that they differ
(`Cslib.Probability.PMF.dist_map_map_le`). The sample space may be infinite; only the common
codomain is finite.

This module also defines `Cslib.Probability.PMF.CoupledWithin μ ν ε`, stating that two discrete
distributions `μ, ν : PMF α` admit a joint coupling `ω : PMF (α × α)` whose disagreement
probability `ω.toOuterMeasure {p | p.1 ≠ p.2}` is at most `ε`. Every pair admits a maximal
coupling: its disagreement probability is exactly `∑' a, (μ a - ν a)`, so `CoupledWithin` and the
all-event relation `CloseTo` coincide, including on infinite types. The composition
combinators (`refl`, `symm`, `mono`, `zero_iff`, `map`, `map₂`, `bind_of_eq_on`) accompany event,
statistical-distance (`dist_le`, `dist_bind_of_good`), and total-variation-distance (`tvDist_le`)
bounds.

## Main definitions

* `Cslib.Probability.PMF.CoupledWithin`: coupling of two `PMF`s within disagreement probability
  `ε : ℝ≥0∞`.

## Main results

* `Cslib.Probability.PMF.exists_coupling_toOuterMeasure_eq_tsum_tsub`: maximal couplings of
  arbitrary probability mass functions.
* `Cslib.Probability.PMF.coupledWithin_iff_closeTo`: approximate couplings are exactly all-event
  statistical closeness.
* `Cslib.Probability.PMF.CoupledWithin.closeTo`, `Cslib.Probability.CloseTo.coupledWithin`:
  transport bounds between the coupling and all-event formulations.
* `Cslib.Probability.PMF.dist_map_map_le`: the coupling inequality for two maps of a single sample.
* `Cslib.Probability.PMF.dist_bind_of_good`: mixture statistical-distance bound conditioned on a
  good event `good : Set α`.
* `Cslib.Probability.PMF.CoupledWithin.toOuterMeasure_le`,
  `Cslib.Probability.PMF.CoupledWithin.dist_le`,
  `Cslib.Probability.PMF.CoupledWithin.tvDist_le`: event-probability, statistical-distance, and
  total-variation-distance bounds from a coupling.
-/

public section

open MeasureTheory
open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.Probability.PMF

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Bounding `dist (p.bind f) q` by splitting `p` across a good event `good : Set α` on which
`dist (f a) q ≤ b` (`0 ≤ b`) and bounding `dist (f a) q ≤ 1` outside `good`. -/
theorem dist_bind_of_good [Finite α] [Fintype β]
    (p : PMF α) (f : α → PMF β) (q : PMF β) (good : Set α) {b : ℝ} (hb : 0 ≤ b)
    (hgood : ∀ a ∈ good, dist (f a) q ≤ b) :
    dist (p.bind f) q ≤ (p.toOuterMeasure goodᶜ).toReal + b := by
  classical
  have := Fintype.ofFinite α
  calc dist (p.bind f) q
      ≤ ∑ a : α, (p a).toReal * dist (f a) q := dist_bind_left_le _ _ _
    _ ≤ ∑ a : α, ((if a ∈ goodᶜ then (p a).toReal else 0) + (p a).toReal * b) := by
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases ha : a ∈ good
        · simp only [Set.mem_compl_iff, ha, not_true_eq_false, ↓reduceIte, zero_add]
          exact mul_le_mul_of_nonneg_left (hgood a ha) ENNReal.toReal_nonneg
        · simp only [Set.mem_compl_iff, ha, not_false_eq_true, ↓reduceIte]
          nlinarith [dist_le_one (f a) q, (ENNReal.toReal_nonneg : 0 ≤ (p a).toReal)]
    _ = (p.toOuterMeasure goodᶜ).toReal + b := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_toReal, one_mul,
          toOuterMeasure_apply_toReal]
        congr 1
        exact Finset.sum_congr rfl fun a _ => by by_cases ha : a ∈ goodᶜ <;> simp [ha]

/-- Two discrete distributions `μ, ν : PMF α` are *coupled within* `ε : ℝ≥0∞` if there exists a
joint distribution `ω : PMF (α × α)` with marginals `μ` and `ν` whose disagreement probability
`ω.toOuterMeasure {p | p.1 ≠ p.2}` is at most `ε`. -/
@[expose] def CoupledWithin (μ ν : PMF α) (ε : ℝ≥0∞) : Prop :=
  ∃ ω : PMF (α × α),
    ω.map Prod.fst = μ ∧
    ω.map Prod.snd = ν ∧
    ω.toOuterMeasure {p : α × α | p.1 ≠ p.2} ≤ ε

/-- Two probability mass functions on an arbitrary type admit a coupling whose disagreement
probability is exactly their positive-part mass `∑' a, (μ a - ν a)`. The coupling puts
`min (μ a) (ν a)` on the diagonal and independently pairs the two residual masses. -/
theorem exists_coupling_toOuterMeasure_eq_tsum_tsub (μ ν : PMF α) :
    ∃ ω : PMF (α × α), ω.map Prod.fst = μ ∧ ω.map Prod.snd = ν ∧
      ω.toOuterMeasure {p | p.1 ≠ p.2} = ∑' a, (μ a - ν a) := by
  classical
  let e : α → ℝ≥0∞ := fun a => μ a - ν a
  let f : α → ℝ≥0∞ := fun a => ν a - μ a
  let m : α → ℝ≥0∞ := fun a => min (μ a) (ν a)
  let δ : ℝ≥0∞ := ∑' a, e a
  have hμsplit (a : α) : μ a = e a + m a := tsub_add_min.symm
  have hνsplit (a : α) : ν a = f a + m a := by
    simp only [f, m, min_comm (μ a)]
    exact tsub_add_min.symm
  have hδf : ∑' a, f a = δ := tsum_tsub_comm ν μ
  have hδ_ne_top : δ ≠ ⊤ :=
    ne_top_of_le_ne_top μ.tsum_coe_ne_top (tsum_le_tsum fun _ => tsub_le_self)
  have hcancel (x : ℝ≥0∞) (hx : δ = 0 → x = 0) : x * δ * δ⁻¹ = x := by
    by_cases hδ : δ = 0
    · simp [hx hδ]
    · rw [mul_assoc, ENNReal.mul_inv_cancel hδ hδ_ne_top, mul_one]
  have he_zero (h : δ = 0) (a : α) : e a = 0 := (tsum_eq_zero_iff.mp h) a
  have hf_zero (h : δ = 0) (a : α) : f a = 0 := (tsum_eq_zero_iff.mp (hδf.trans h)) a
  have hef (a : α) : e a * f a = 0 := by
    rcases le_total (μ a) (ν a) with h | h <;> simp [e, f, tsub_eq_zero_of_le h]
  let w : α × α → ℝ≥0∞ := fun p =>
    (if p.1 = p.2 then m p.1 else 0) + e p.1 * f p.2 * δ⁻¹
  have hrow (a : α) : ∑' b, w (a, b) = μ a := by
    simp only [w, tsum_add, tsum_ite_eq', ENNReal.tsum_mul_right,
      ENNReal.tsum_mul_left, hδf]
    rw [hcancel _ fun h => he_zero h a, add_comm, ← hμsplit]
  have hcol (b : α) : ∑' a, w (a, b) = ν b := by
    simp only [w, tsum_add, tsum_ite_eq, ENNReal.tsum_mul_right]
    change m b + (δ * f b) * δ⁻¹ = ν b
    rw [mul_comm δ, hcancel _ fun h => hf_zero h b, add_comm, ← hνsplit]
  have htotal : ∑' p, w p = 1 := by rw [tsum_prod', tsum_congr hrow, μ.tsum_coe]
  let ω : PMF (α × α) := ⟨w, CompleteLattice.summable.hasSum_iff.mpr htotal⟩
  refine ⟨ω, ?_, ?_, ?_⟩
  · ext a
    rw [PMF.map_apply, tsum_prod', tsum_comm]
    simp only [ω, tsum_ite_eq']
    exact hrow a
  · ext b
    rw [PMF.map_apply, tsum_prod']
    simp only [ω, tsum_ite_eq']
    exact hcol b
  · have hind (p : α × α) :
        Set.indicator {p : α × α | p.1 ≠ p.2} ω p = e p.1 * f p.2 * δ⁻¹ := by
      by_cases hp : p.1 = p.2
      · rw [Set.indicator_of_notMem (by simpa using hp), hp, hef, zero_mul]
      · rw [Set.indicator_of_mem hp]
        change w p = _
        simp only [w, hp, ite_false, zero_add]
    rw [PMF.toOuterMeasure_apply, tsum_congr hind, tsum_prod']
    simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hδf]
    exact hcancel δ id

namespace CoupledWithin

/-- Coupling inequality for events: if `CoupledWithin μ ν ε`, then for every event `S : Set α`,
`μ.toOuterMeasure S ≤ ν.toOuterMeasure S + ε`. -/
theorem toOuterMeasure_le {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) (S : Set α) :
    μ.toOuterMeasure S ≤ ν.toOuterMeasure S + ε := by
  obtain ⟨ω, rfl, rfl, hω⟩ := h
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  have hsub : Prod.fst ⁻¹' S ⊆ Prod.snd ⁻¹' S ∪ {p : α × α | p.1 ≠ p.2} := fun p hp =>
    (em (p.1 = p.2)).imp (fun heq : p.1 = p.2 => show p.2 ∈ S from heq ▸ hp) id
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hω))

/-- A coupling with disagreement probability at most `ε` witnesses all-events statistical
closeness with the same error. -/
theorem closeTo {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) : CloseTo μ ν ε :=
  h.toOuterMeasure_le

end CoupledWithin

/-- Approximate coupling and all-events statistical closeness coincide for arbitrary probability
mass functions, including distributions with infinite support. -/
theorem coupledWithin_iff_closeTo {μ ν : PMF α} {ε : ℝ≥0∞} :
    CoupledWithin μ ν ε ↔ CloseTo μ ν ε := by
  refine ⟨CoupledWithin.closeTo, fun h => ?_⟩
  obtain ⟨ω, hfst, hsnd, hω⟩ := exists_coupling_toOuterMeasure_eq_tsum_tsub μ ν
  exact ⟨ω, hfst, hsnd, hω.trans_le (closeTo_iff_tsum_tsub_le.mp h)⟩

end Cslib.Probability.PMF

namespace Cslib.Probability

/-- All-events statistical closeness supplies a joint coupling with the same disagreement bound. -/
theorem CloseTo.coupledWithin {α : Type*} {μ ν : PMF α} {ε : ℝ≥0∞} (h : CloseTo μ ν ε) :
    PMF.CoupledWithin μ ν ε :=
  PMF.coupledWithin_iff_closeTo.mpr h

end Cslib.Probability

namespace Cslib.Probability.PMF.CoupledWithin

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Every distribution is coupled with itself within `0`. -/
theorem refl (μ : PMF α) : CoupledWithin μ μ 0 :=
  (CloseTo.refl μ).coupledWithin

/-- Symmetry of `CoupledWithin`. -/
theorem symm {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) :
    CoupledWithin ν μ ε :=
  h.closeTo.symm.coupledWithin

/-- Monotonicity of `CoupledWithin` in the error bound `ε`. -/
theorem mono {μ ν : PMF α} {ε₁ ε₂ : ℝ≥0∞} (h : CoupledWithin μ ν ε₁) (hε : ε₁ ≤ ε₂) :
    CoupledWithin μ ν ε₂ :=
  Exists.imp (fun _ ⟨h₁, h₂, hω⟩ => ⟨h₁, h₂, hω.trans hε⟩) h

/-- `CoupledWithin μ ν 0` holds if and only if `μ = ν`. -/
@[simp]
theorem zero_iff {μ ν : PMF α} : CoupledWithin μ ν 0 ↔ μ = ν := by
  refine ⟨?_, fun h => h ▸ refl μ⟩
  rintro ⟨ω, rfl, rfl, hω⟩
  have hdisj := (PMF.toOuterMeasure_apply_eq_zero_iff ω _).mp (nonpos_iff_eq_zero.mp hω)
  exact map_congr_on_support ω Prod.fst Prod.snd fun p hp =>
    of_not_not (Set.disjoint_left.mp hdisj hp)

/-- Deterministic postprocessing preserves `CoupledWithin` with the same error bound. -/
theorem map {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) (f : α → β) :
    CoupledWithin (μ.map f) (ν.map f) ε :=
  (h.closeTo.map f).coupledWithin

/-- Composing two independent couplings via `g : α → β → γ` adds their disagreement bounds. -/
theorem map₂ {μ₁ ν₁ : PMF α} {μ₂ ν₂ : PMF β} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : CoupledWithin μ₁ ν₁ ε₁) (h₂ : CoupledWithin μ₂ ν₂ ε₂)
    (g : α → β → γ) :
    CoupledWithin
      (μ₁.bind fun a => μ₂.map (g a))
      (ν₁.bind fun a => ν₂.map (g a))
      (ε₁ + ε₂) :=
  (h₁.closeTo.bind fun a _ => h₂.closeTo.map (g a)).coupledWithin

/-- If a mixture `p.bind f` agrees with `q` on every `a ∈ p.support` belonging to a good event
`good : Set α`, then `p.bind f` is coupled with `q` within `p.toOuterMeasure goodᶜ`. -/
theorem bind_of_eq_on {p : PMF α} {f : α → PMF β} {q : PMF β} (good : Set α)
    (hgood : ∀ a ∈ p.support, a ∈ good → f a = q) :
    CoupledWithin (p.bind f) q (p.toOuterMeasure goodᶜ) := by
  apply CloseTo.coupledWithin
  intro event
  simpa only [add_comm] using toOuterMeasure_bind_failure_le p f good event
    (q.toOuterMeasure event) (fun a ha hgood' => by rw [hgood a ha hgood'])

/-- On a finite type, `CoupledWithin μ ν ε` (with `ε ≠ ⊤`) bounds the statistical distance
`dist μ ν ≤ ε.toReal`. -/
theorem dist_le [Fintype α] {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) (hε : ε ≠ ⊤) :
    dist μ ν ≤ ε.toReal := by
  have hdist := closeTo_iff_ofReal_dist_le.mp h.closeTo
  simpa only [ENNReal.toReal_ofReal dist_nonneg] using ENNReal.toReal_mono hε hdist

/-- On a measurable singleton space, `CoupledWithin μ ν ε` (with `ε ≠ ⊤`) bounds the
total variation distance `tvDist μ.toMeasure ν.toMeasure ≤ 2 * ε.toReal`. -/
theorem tvDist_le [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) (hε : ε ≠ ⊤) :
    tvDist μ.toMeasure ν.toMeasure ≤ 2 * ε.toReal := by
  have htv := closeTo_iff_etvDist_le.mp h.closeTo
  simpa only [tvDist, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hε) htv

end Cslib.Probability.PMF.CoupledWithin

namespace Cslib.Probability.PMF

/-- **Coupling inequality.** Two functions of the same sample are at statistical distance at most
the probability that they differ. -/
theorem dist_map_map_le {α : Type*} {β : Type*} [Fintype β] (p : PMF α) (f g : α → β) :
    dist (p.map f) (p.map g) ≤ (p.toOuterMeasure {a | f a ≠ g a}).toReal := by
  have h : CoupledWithin (p.map f) (p.map g) (p.toOuterMeasure {a | f a ≠ g a}) := by
    refine ⟨p.map (fun a => (f a, g a)), ?_, ?_, (PMF.toOuterMeasure_map_apply _ _ _).le⟩ <;>
      simp only [PMF.map_comp, Function.comp_def]
  exact h.dist_le (toOuterMeasure_ne_top _ _)

end Cslib.Probability.PMF
