/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Basic
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Switched.Switch
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Switched.SwitchedLayout
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Metric
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.UnionBound
import CslibFrontier.Tactic.LRATTauto

/-!
# One sample controls every frontier of the median-switched layout

Fix a simple subcubic graph `H` on `Fin n`, a decay rate `q ∈ [0, 1)`, and a truncation radius
`R`. For a sample `ω : Fin n → ℝ` of independent standard Gaussians, score each vertex `v` by
`y ω v = ⟪unitKernelRow H q R v, WithLp.toLp 2 ω⟫`. Because `q < 1`, the unit kernel rows are
pairwise distinct (`unitKernelRow_ne_of_ne`), so `y ω` is almost surely injective.

Over a symmetric grid `{-T, -(M - 1) δ, ..., 0, ..., (M - 1) δ, T}` with `δ = T / M`, every
negative-level inner frontier is covered by the next grid inner frontier to its left plus a single
half-open cell `(a, b]`:

`innerFrontier H y t ⊆ innerFrontier H y a ∪ cellSet y a b` for `a ≤ t ≤ b`,

and every positive-level outer frontier is covered symmetrically by the next grid outer frontier
to its right plus the same cell. Only `4 M + 6` local vertex-count events are tracked:
`M` inner frontiers below zero, `M` outer frontiers above zero, `2 M` cell counts, `2` tails
beyond `±T`, and the `4` counts making up `lowerZero` and `upperZero` at level zero.

Every vertex event depends only on the coordinates of `ω` in the closed ball of radius `R + 1`
around `v`, so by `Cslib.Circuits.Frontier.Gaussian.measureReal_deviation_le` each count deviates
from its mean by `ε n` with probability at most `4 ^ (2 * R + 2) / (ε ^ 2 * n)`. Per-vertex
expectations are bounded by `kappa ρ` via `starFrontier` (for `t ≠ 0`) and `switch_bound` (at
`t = 0`), by `δ / √(2π)` on cells, and by `1 / T ^ 2` on the two tails.

## Main definitions

* `Cslib.Circuits.Frontier.Switched.vertexScore`: the Gaussian vertex score `y ω v`.
* `Cslib.Circuits.Frontier.Switched.switchedBound`: the per-vertex load bound for a good sample.

## Main results

* `Cslib.Circuits.Frontier.Switched.unitKernelRow_ne_of_ne`: unit kernel rows at `0 ≤ q < 1` are
  distinct for distinct vertices.
* `Cslib.Circuits.Frontier.Switched.exists_good_labeling`: for all large `n`, some injective
  vertex labeling `y : Fin n → ℝ` bounds every negative inner frontier, positive outer frontier,
  `lowerZero`, and `upperZero` by `switchedBound ρ T ε M * n`.

## References

* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace Cslib.Circuits.Frontier.Switched

open Cslib.Circuits.Frontier.Gaussian

/-- The per-vertex switched frontier bound at correlation floor `ρ`, truncation level `T`,
deviation slack `ε`, and `M` half-axis grid cells of width `δ = T / M`. -/
noncomputable def switchedBound (ρ T ε : ℝ) (M : ℕ) : ℝ :=
  max (1 / T ^ 2 + ε) (kappa ρ + (T / M) / √(2 * π) + 2 * ε)

/-- The Gaussian vertex score `⟪unitKernelRow H q R v, WithLp.toLp 2 ω⟫`. -/
noncomputable def vertexScore {n : ℕ} (H : SimpleGraph (Fin n)) (q : ℝ) (R : ℕ)
    (ω : Fin n → ℝ) (v : Fin n) : ℝ :=
  ⟪unitKernelRow H q R v, WithLp.toLp 2 ω⟫

/-! ### Kernel row distinctness and injectivity -/

/-- For `0 ≤ q < 1`, distinct vertices have distinct unit kernel rows: comparing their ratios at
`u` and `v` yields `1 ≤ q ^ 2 < 1`. -/
theorem unitKernelRow_ne_of_ne {V : Type*} [Fintype V] (H : SimpleGraph V) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (R : ℕ) {u v : V} (huv : u ≠ v) :
    unitKernelRow H q R u ≠ unitKernelRow H q R v := by
  intro heq
  have hk (w : V) : 0 < ‖kernelRow H q R w‖ := one_pos.trans_le <| by
    simpa [kernelRow_self] using PiLp.norm_apply_le (kernelRow H q R w) w
  have hku := hk u
  have hkv := hk v
  have hk_le : ∀ a b : V, a ≠ b → kernelRow H q R a b ≤ q := fun a b hab => by
    rw [kernelRow_apply]
    split_ifs with hd
    · have hpos : 1 ≤ H.dist a b := by
        by_contra h
        have h0 : H.dist a b = 0 := by omega
        have hreach : H.Reachable a b :=
          SimpleGraph.reachable_of_edist_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top R) hd)
        exact hab ((SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h0).resolve_right
          (not_not.mpr hreach))
      exact (pow_le_pow_of_le_one hq0 hq1.le hpos).trans (by rw [pow_one])
    · exact hq0
  have hu := congrArg (fun x : EuclideanSpace ℝ V => x u) heq
  have hv := congrArg (fun x : EuclideanSpace ℝ V => x v) heq
  simp only [unitKernelRow, PiLp.smul_apply, smul_eq_mul, kernelRow_self, mul_one] at hu hv
  have hvu : ‖kernelRow H q R v‖ = ‖kernelRow H q R u‖ * kernelRow H q R v u := by
    have hmul := congrArg (fun x => x * (‖kernelRow H q R u‖ * ‖kernelRow H q R v‖)) hu
    field_simp [hku.ne', hkv.ne'] at hmul
    linarith
  have huv' : ‖kernelRow H q R u‖ = ‖kernelRow H q R v‖ * kernelRow H q R u v := by
    have hmul := congrArg (fun x => x * (‖kernelRow H q R u‖ * ‖kernelRow H q R v‖)) hv
    field_simp [hku.ne', hkv.ne'] at hmul
    linarith
  have hprod : ‖kernelRow H q R u‖ ≤ ‖kernelRow H q R u‖ * (q * q) := by
    have h1 : ‖kernelRow H q R v‖ ≤ ‖kernelRow H q R u‖ * q := by
      rw [hvu]; exact mul_le_mul_of_nonneg_left (hk_le v u huv.symm) hku.le
    calc ‖kernelRow H q R u‖ = ‖kernelRow H q R v‖ * kernelRow H q R u v := huv'
      _ ≤ (‖kernelRow H q R u‖ * q) * q :=
        mul_le_mul h1 (hk_le u v huv) (kernelRow_nonneg hq0 R u v) (mul_nonneg hku.le hq0)
      _ = ‖kernelRow H q R u‖ * (q * q) := by ring
  have hqq : q * q < 1 := by nlinarith
  nlinarith

/-- For `0 ≤ q < 1`, the Gaussian vertex score `vertexScore H q R ω` is almost surely injective. -/
theorem measureReal_not_injective_vertexScore {n : ℕ} (H : SimpleGraph (Fin n)) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (R : ℕ) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
      {ω | ¬Function.Injective (vertexScore H q R ω)} = 0 := by
  set P := Measure.pi fun _ : Fin n => gaussianReal 0 1
  let pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 ≠ p.2
  have hsub : {ω : Fin n → ℝ | ¬Function.Injective (vertexScore H q R ω)} ⊆
      ⋃ p ∈ pairs, {ω : Fin n → ℝ | vertexScore H q R ω p.1 = vertexScore H q R ω p.2} := by
    intro ω hω
    change ¬∀ u v, vertexScore H q R ω u = vertexScore H q R ω v → u = v at hω
    push Not at hω
    obtain ⟨u, v, heq, hne⟩ := hω
    exact mem_iUnion₂.mpr ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, heq⟩
  have hzero : ∀ p ∈ pairs,
      P.real {ω : Fin n → ℝ | vertexScore H q R ω p.1 = vertexScore H q R ω p.2} = 0 := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hdiff : unitKernelRow H q R p.1 - unitKernelRow H q R p.2 ≠ 0 :=
      sub_ne_zero.mpr (unitKernelRow_ne_of_ne H hq0 hq1 R hne)
    have hset : {ω : Fin n → ℝ | vertexScore H q R ω p.1 = vertexScore H q R ω p.2} =
        {ω | WithLp.toLp 2 ω ∈
          {x : EuclideanSpace ℝ (Fin n) |
            ⟪unitKernelRow H q R p.1 - unitKernelRow H q R p.2, x⟫ = 0}} := by
      ext ω
      simp only [vertexScore, mem_ofPred_eq, inner_sub_left, sub_eq_zero]
    rw [hset, measureReal_pi_gaussianReal_eq
      (measurableSet_eq_fun (by fun_prop) measurable_const),
      Measure.real, measure_stdGaussian_inner_eq_zero hdiff, ENNReal.toReal_zero]
  have hle : P.real {ω | ¬Function.Injective (vertexScore H q R ω)} ≤ 0 := by
    calc P.real {ω | ¬Function.Injective (vertexScore H q R ω)}
        ≤ P.real (⋃ p ∈ pairs,
            {ω | vertexScore H q R ω p.1 = vertexScore H q R ω p.2}) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ p ∈ pairs, P.real {ω | vertexScore H q R ω p.1 = vertexScore H q R ω p.2} :=
          measureReal_biUnion_finset_le _ _
      _ = 0 := Finset.sum_eq_zero hzero
  exact le_antisymm hle measureReal_nonneg

/-! ### Deterministic grid comparison -/

/-- Any negative-level inner frontier is covered by the next grid inner frontier to its left plus
the corresponding half-open cell `(a, b]`. -/
theorem innerFrontier_subset_grid {n : ℕ} (H : SimpleGraph (Fin n)) (y : Fin n → ℝ)
    {a t b : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    innerFrontier H y t ⊆ innerFrontier H y a ∪ cellSet y a b := by
  classical
  intro u hu
  simp only [innerFrontier, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨hut, w, huw, htw⟩ := hu
  by_cases hua : y u ≤ a
  · exact Finset.mem_union_left _ (by
      simp only [innerFrontier, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hua, w, huw, lt_of_le_of_lt hat htw⟩)
  · exact Finset.mem_union_right _ (by
      simp only [cellSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨not_le.mp hua, hut.trans htb⟩)

/-- Any positive-level outer frontier is covered by the next grid outer frontier to its right plus
the corresponding half-open cell `(a, b]`. -/
theorem outerFrontier_subset_grid {n : ℕ} (H : SimpleGraph (Fin n)) (y : Fin n → ℝ)
    {a t b : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    outerFrontier H y t ⊆ outerFrontier H y b ∪ cellSet y a b := by
  classical
  intro w hw
  simp only [outerFrontier, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  obtain ⟨htw, u, huw, hut⟩ := hw
  by_cases hwb : b < y w
  · exact Finset.mem_union_left _ (by
      simp only [outerFrontier, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hwb, u, huw, hut.trans htb⟩)
  · exact Finset.mem_union_right _ (by
      simp only [cellSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨lt_of_le_of_lt hat htw, not_lt.mp hwb⟩)

/-! ### Locality and expectation bounds -/

open Classical in
private theorem card_not_disjoint_closedBall_simple {n : ℕ} (H : SimpleGraph (Fin n))
    (hdeg : ∀ v, H.degree v ≤ 3) (R : ℕ) (v : Fin n) :
    (Finset.univ.filter fun w => ¬Disjoint (closedBall H v (R + 1)) (closedBall H w (R + 1))).card
      ≤ 4 ^ (2 * R + 2) := by
  refine (Finset.card_le_card fun w hw => ?_).trans
    (SimpleGraph.card_edist_le_le (fun u => hdeg u) v (2 * (R + 1)))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  obtain ⟨z, hvz, hwz⟩ := not_disjoint_iff.mp hw
  calc H.edist v w ≤ H.edist v z + H.edist z w := SimpleGraph.edist_triangle
    _ = H.edist v z + H.edist w z := by rw [SimpleGraph.edist_comm (u := z)]
    _ ≤ (R + 1 : ℕ) + (R + 1 : ℕ) := add_le_add hvz hwz
    _ = ((2 * (R + 1) : ℕ) : ℕ∞) := by push_cast; ring

private theorem vertexScore_congr {n : ℕ} {H : SimpleGraph (Fin n)} {q : ℝ} {R : ℕ}
    {v w : Fin n} (hvw : H.edist v w ≤ 1) {ω ω' : Fin n → ℝ}
    (hω : ∀ z ∈ closedBall H v (R + 1), ω z = ω' z) :
    vertexScore H q R ω w = vertexScore H q R ω' w := by
  apply inner_toLp_congr (S := closedBall H v (R + 1)) _ hω
  intro z hz
  refine unitKernelRow_eq_zero_of_lt (not_le.mp fun hle => hz ?_)
  change H.edist v z ≤ ((R + 1 : ℕ) : ℕ∞)
  calc H.edist v z ≤ H.edist v w + H.edist w z := SimpleGraph.edist_triangle
    _ ≤ 1 + (R : ℕ) := add_le_add hvw hle
    _ = ((R + 1 : ℕ) : ℕ∞) := by push_cast; ring

private theorem measurable_inner_row {n : ℕ} (H : SimpleGraph (Fin n)) (q : ℝ) (R : ℕ)
    (v : Fin n) : Measurable (fun x : EuclideanSpace ℝ (Fin n) => ⟪unitKernelRow H q R v, x⟫) :=
  (continuous_const.inner continuous_id).measurable

private theorem measurable_vertexScore {n : ℕ} (H : SimpleGraph (Fin n)) (q : ℝ) (R : ℕ)
    (v : Fin n) : Measurable (fun ω : Fin n → ℝ => vertexScore H q R ω v) :=
  (measurable_inner_row H q R v).comp (PiLp.continuous_toLp 2 _).measurable

private theorem measureReal_cell_le {n : ℕ} (H : SimpleGraph (Fin n)) (q : ℝ) (R : ℕ)
    (v : Fin n) (a : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
      {ω | a < vertexScore H q R ω v ∧ vertexScore H q R ω v ≤ a + δ} ≤ δ / √(2 * π) := by
  have hy : ‖unitKernelRow H q R v‖ = 1 := norm_unitKernelRow (G := H) q R v
  have hy0 : unitKernelRow H q R v ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; exact zero_ne_one hy
  have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin n) |
      ⟪unitKernelRow H q R v, x⟫ ∈ Ioc a (a + δ)} :=
    measurableSet_Ioc.preimage (measurable_inner_row H q R v)
  have heq : {ω : Fin n → ℝ | a < vertexScore H q R ω v ∧ vertexScore H q R ω v ≤ a + δ} =
      {ω | WithLp.toLp 2 ω ∈
        {x : EuclideanSpace ℝ (Fin n) | ⟪unitKernelRow H q R v, x⟫ ∈ Ioc a (a + δ)}} := rfl
  rw [heq, measureReal_pi_gaussianReal_eq hmeas, measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((stdGaussian_inner_mem_le hy0 measurableSet_Ioc).trans ?_)
  rw [hy, mul_one, Real.volume_Ioc, add_sub_cancel_left, ← ENNReal.ofReal_mul (by positivity),
    inv_mul_eq_div]

private theorem norm_row {n : ℕ} (H : SimpleGraph (Fin n)) (q : ℝ) (R : ℕ) (v : Fin n) :
    ‖unitKernelRow H q R v‖ = 1 :=
  norm_unitKernelRow (G := H) q R v

private theorem measurableSet_exists_guard {α Ω : Type*} [Countable α] [MeasurableSpace Ω]
    {P : α → Prop} {S : α → Set Ω} (hS : ∀ a, MeasurableSet (S a)) :
    MeasurableSet {x | ∃ a, P a ∧ x ∈ S a} := by
  have heq : {x | ∃ a, P a ∧ x ∈ S a} = ⋃ a ∈ {a | P a}, S a := by
    ext x; simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [heq]
  exact MeasurableSet.biUnion (to_countable {a | P a}) fun a _ => hS a

private theorem measurableSet_forall_guard {α Ω : Type*} [Countable α] [MeasurableSpace Ω]
    {P : α → Prop} {S : α → Set Ω} (hS : ∀ a, MeasurableSet (S a)) :
    MeasurableSet {x | ∀ a, P a → x ∈ S a} := by
  have heq : {x | ∀ a, P a → x ∈ S a} = ⋂ a ∈ {a | P a}, S a := by
    ext x; simp only [mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact MeasurableSet.biInter (to_countable {a | P a}) fun a _ => hS a

open Classical in
private theorem measurableSet_crossHi_of_meas {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (H : SimpleGraph (Fin n)) (f : Fin n → Ω → ℝ) (hm : ∀ v, Measurable (f v)) (v : Fin n) :
    MeasurableSet {x : Ω | 0 < f v x ∧ H.degree v = 3 ∧
      ∀ z, H.Adj v z → (f v x ≤ 0 ↔ 0 < f z x)} := by
  by_cases hd : H.degree v = 3
  · have heq : {x : Ω | 0 < f v x ∧ H.degree v = 3 ∧
          ∀ z, H.Adj v z → (f v x ≤ 0 ↔ 0 < f z x)} =
        {x : Ω | 0 < f v x} ∩ {x : Ω | ∀ z, H.Adj v z → x ∈ {y | f z y ≤ 0}} := by
      ext x; simp only [mem_inter_iff, mem_ofPred_eq, hd, true_and]
      constructor
      · rintro ⟨hpos, hall⟩; exact ⟨hpos, fun z hz =>
          not_lt.mp fun hlt => (not_le.mpr hpos) ((hall z hz).mpr hlt)⟩
      · rintro ⟨hpos, hall⟩; exact ⟨hpos, fun z hz =>
          ⟨fun h => absurd h (not_le.mpr hpos), fun h => absurd h (not_lt.mpr (hall z hz))⟩⟩
    rw [heq]
    exact (measurableSet_lt measurable_const (hm v)).inter
      (measurableSet_forall_guard fun z => measurableSet_le (hm z) measurable_const)
  · have : {x : Ω | 0 < f v x ∧ H.degree v = 3 ∧
        ∀ z, H.Adj v z → (f v x ≤ 0 ↔ 0 < f z x)} = ∅ := by ext x; simp [hd]
    rw [this]; exact MeasurableSet.empty

open Classical in
private theorem measurableSet_crossLo_of_meas {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (H : SimpleGraph (Fin n)) (f : Fin n → Ω → ℝ) (hm : ∀ v, Measurable (f v)) (v : Fin n) :
    MeasurableSet {x : Ω | f v x ≤ 0 ∧ H.degree v = 3 ∧
      ∀ z, H.Adj v z → (f v x ≤ 0 ↔ 0 < f z x)} := by
  by_cases hd : H.degree v = 3
  · have heq : {x : Ω | f v x ≤ 0 ∧ H.degree v = 3 ∧
          ∀ z, H.Adj v z → (f v x ≤ 0 ↔ 0 < f z x)} =
        {x : Ω | f v x ≤ 0} ∩ {x : Ω | ∀ z, H.Adj v z → x ∈ {y | 0 < f z y}} := by
      ext x; simp only [mem_inter_iff, mem_ofPred_eq, hd, true_and]
      constructor
      · rintro ⟨hle, hall⟩; exact ⟨hle, fun z hz => (hall z hz).mp hle⟩
      · rintro ⟨hle, hall⟩; exact ⟨hle, fun z hz => ⟨fun _ => hall z hz, fun _ => hle⟩⟩
    rw [heq]
    exact (measurableSet_le (hm v) measurable_const).inter
      (measurableSet_forall_guard fun z => measurableSet_lt measurable_const (hm z))
  · have : {x : Ω | f v x ≤ 0 ∧ H.degree v = 3 ∧
        ∀ z, H.Adj v z → (f v x ≤ 0 ↔ 0 < f z x)} = ∅ := by ext x; simp [hd]
    rw [this]; exact MeasurableSet.empty

open Classical in
private theorem measureReal_innerFrontier_le {n : ℕ} (H : SimpleGraph (Fin n))
    (hdeg : ∀ v, H.degree v ≤ 3) {q : ℝ} {R : ℕ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρs : ρ ≤ rStar)
    (hadj : ∀ u w, H.Adj u w → ρ ≤ ⟪unitKernelRow H q R u, unitKernelRow H q R w⟫)
    (v : Fin n) {t : ℝ} (ht : t ≤ 0) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
      {ω | vertexScore H q R ω v ≤ t ∧ ∃ w, H.Adj v w ∧ t < vertexScore H q R ω w} ≤
      kappa ρ := by
  set E := EuclideanSpace ℝ (Fin n)
  let e : H.neighborFinset v ≃ Fin (H.degree v) :=
    Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans (H.card_neighborFinset_eq_degree v))
  let b : Fin (H.degree v) → E := fun i => unitKernelRow H q R (e.symm i).1
  have hm : ∀ w, Measurable fun x : E => ⟪unitKernelRow H q R w, x⟫ :=
    measurable_inner_row H q R
  have hmeas : MeasurableSet {x : E | ⟪unitKernelRow H q R v, x⟫ ≤ t ∧
      ∃ w, H.Adj v w ∧ t < ⟪unitKernelRow H q R w, x⟫} := by
    rw [Set.ofPred_and]
    exact (measurableSet_le (hm v) measurable_const).inter
      (measurableSet_exists_guard fun w => measurableSet_lt measurable_const (hm w))
  change (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
      {ω | WithLp.toLp 2 ω ∈ {x : E | ⟪unitKernelRow H q R v, x⟫ ≤ t ∧
        ∃ w, H.Adj v w ∧ t < ⟪unitKernelRow H q R w, x⟫}} ≤ _
  rw [measureReal_pi_gaussianReal_eq hmeas]
  have hrefl : {x : E | ⟪unitKernelRow H q R v, x⟫ ≤ t ∧
        ∃ w, H.Adj v w ∧ t < ⟪unitKernelRow H q R w, x⟫} =
      Neg.neg ⁻¹' {x : E | -t ≤ ⟪unitKernelRow H q R v, x⟫ ∧
        ∃ w, H.Adj v w ∧ ⟪unitKernelRow H q R w, x⟫ < -t} := by
    ext x; simp only [mem_ofPred_eq, mem_preimage, inner_neg_right]; constructor <;>
      rintro ⟨h1, w, hw, h2⟩ <;> exact ⟨by linarith, w, hw, by linarith⟩
  have hmeas' : MeasurableSet {x : E | -t ≤ ⟪unitKernelRow H q R v, x⟫ ∧
      ∃ w, H.Adj v w ∧ ⟪unitKernelRow H q R w, x⟫ < -t} := by
    rw [Set.ofPred_and]
    exact (measurableSet_le measurable_const (hm v)).inter
      (measurableSet_exists_guard fun w => measurableSet_lt (hm w) measurable_const)
  rw [hrefl, measureReal_neg_preimage_stdGaussian hmeas']
  have hsub : {x : E | -t ≤ ⟪unitKernelRow H q R v, x⟫ ∧
        ∃ w, H.Adj v w ∧ ⟪unitKernelRow H q R w, x⟫ < -t} ⊆
      {x : E | -t ≤ ⟪unitKernelRow H q R v, x⟫ ∧ ∃ i, ⟪b i, x⟫ ≤ -t} := by
    rintro x ⟨h1, w, hw, h2⟩
    refine ⟨h1, e ⟨w, (H.mem_neighborFinset v w).mpr hw⟩, ?_⟩
    simp only [b, Equiv.symm_apply_apply]
    exact h2.le
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  exact starFrontier hρ0 hρs (hdeg v) (norm_row H q R v)
    (fun i => norm_row H q R _)
    (fun i => hadj v _ ((H.mem_neighborFinset v _).mp (e.symm i).2)) (by linarith)

open Classical in
private theorem measureReal_outerFrontier_le {n : ℕ} (H : SimpleGraph (Fin n))
    (hdeg : ∀ v, H.degree v ≤ 3) {q : ℝ} {R : ℕ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρs : ρ ≤ rStar)
    (hadj : ∀ u w, H.Adj u w → ρ ≤ ⟪unitKernelRow H q R u, unitKernelRow H q R w⟫)
    (v : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
      {ω | t < vertexScore H q R ω v ∧ ∃ u, H.Adj u v ∧ vertexScore H q R ω u ≤ t} ≤
      kappa ρ := by
  set E := EuclideanSpace ℝ (Fin n)
  let e : H.neighborFinset v ≃ Fin (H.degree v) :=
    Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans (H.card_neighborFinset_eq_degree v))
  let b : Fin (H.degree v) → E := fun i => unitKernelRow H q R (e.symm i).1
  have hm : ∀ w, Measurable fun x : E => ⟪unitKernelRow H q R w, x⟫ :=
    measurable_inner_row H q R
  have hmeas : MeasurableSet {x : E | t < ⟪unitKernelRow H q R v, x⟫ ∧
      ∃ u, H.Adj u v ∧ ⟪unitKernelRow H q R u, x⟫ ≤ t} := by
    rw [Set.ofPred_and]
    exact (measurableSet_lt measurable_const (hm v)).inter
      (measurableSet_exists_guard fun u => measurableSet_le (hm u) measurable_const)
  change (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
      {ω | WithLp.toLp 2 ω ∈ {x : E | t < ⟪unitKernelRow H q R v, x⟫ ∧
        ∃ u, H.Adj u v ∧ ⟪unitKernelRow H q R u, x⟫ ≤ t}} ≤ _
  rw [measureReal_pi_gaussianReal_eq hmeas]
  have hsub : {x : E | t < ⟪unitKernelRow H q R v, x⟫ ∧
        ∃ u, H.Adj u v ∧ ⟪unitKernelRow H q R u, x⟫ ≤ t} ⊆
      {x : E | t ≤ ⟪unitKernelRow H q R v, x⟫ ∧ ∃ i, ⟪b i, x⟫ ≤ t} := by
    rintro x ⟨h1, u, hu, h2⟩
    refine ⟨h1.le, e ⟨u, (H.mem_neighborFinset v u).mpr hu.symm⟩, ?_⟩
    simp only [b, Equiv.symm_apply_apply]
    exact h2
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  exact starFrontier hρ0 hρs (hdeg v) (norm_row H q R v)
    (fun i => norm_row H q R _)
    (fun i => hadj v _ ((H.mem_neighborFinset v _).mp (e.symm i).2)) ht

open Classical in
private theorem measureReal_lowerZero_vertex_le {n : ℕ} (H : SimpleGraph (Fin n))
    (hdeg : ∀ v, H.degree v ≤ 3) {q : ℝ} {R : ℕ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρs : ρ ≤ rStar)
    (hadj : ∀ u w, H.Adj u w → ρ ≤ ⟪unitKernelRow H q R u, unitKernelRow H q R w⟫)
    (v : Fin n) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
        {ω | vertexScore H q R ω v ≤ 0 ∧ ∃ w, H.Adj v w ∧ 0 < vertexScore H q R ω w} +
      (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
        {ω | 0 < vertexScore H q R ω v ∧ H.degree v = 3 ∧
          ∀ z, H.Adj v z → (vertexScore H q R ω v ≤ 0 ↔ 0 < vertexScore H q R ω z)} ≤
      kappa ρ := by
  set E := EuclideanSpace ℝ (Fin n)
  let e : H.neighborFinset v ≃ Fin (H.degree v) :=
    Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans (H.card_neighborFinset_eq_degree v))
  let b : Fin (H.degree v) → E := fun i => unitKernelRow H q R (e.symm i).1
  have hm : ∀ w, Measurable fun x : E => ⟪unitKernelRow H q R w, x⟫ :=
    measurable_inner_row H q R
  have hm1 : MeasurableSet {x : E | ⟪unitKernelRow H q R v, x⟫ ≤ 0 ∧
      ∃ w, H.Adj v w ∧ 0 < ⟪unitKernelRow H q R w, x⟫} := by
    rw [Set.ofPred_and]
    exact (measurableSet_le (hm v) measurable_const).inter
      (measurableSet_exists_guard fun w => measurableSet_lt measurable_const (hm w))
  have hm2 : MeasurableSet {x : E | 0 < ⟪unitKernelRow H q R v, x⟫ ∧ H.degree v = 3 ∧
      ∀ z, H.Adj v z → (⟪unitKernelRow H q R v, x⟫ ≤ 0 ↔ 0 < ⟪unitKernelRow H q R z, x⟫)} :=
    measurableSet_crossHi_of_meas H (fun w x => ⟪unitKernelRow H q R w, x⟫) hm v
  change (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
      {ω | WithLp.toLp 2 ω ∈ {x : E | ⟪unitKernelRow H q R v, x⟫ ≤ 0 ∧
        ∃ w, H.Adj v w ∧ 0 < ⟪unitKernelRow H q R w, x⟫}} +
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
      {ω | WithLp.toLp 2 ω ∈ {x : E | 0 < ⟪unitKernelRow H q R v, x⟫ ∧ H.degree v = 3 ∧
        ∀ z, H.Adj v z → (⟪unitKernelRow H q R v, x⟫ ≤ 0 ↔ 0 < ⟪unitKernelRow H q R z, x⟫)}} ≤ _
  rw [measureReal_pi_gaussianReal_eq hm1, measureReal_pi_gaussianReal_eq hm2]
  have h1 : (stdGaussian E).real {x | ⟪unitKernelRow H q R v, x⟫ ≤ 0 ∧
        ∃ w, H.Adj v w ∧ 0 < ⟪unitKernelRow H q R w, x⟫} ≤
      (stdGaussian E).real {x | ⟪unitKernelRow H q R v, x⟫ ≤ 0 ∧ ∃ i, 0 ≤ ⟪b i, x⟫} := by
    refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    obtain ⟨hxv, w, hw, hwx⟩ := hx
    refine ⟨hxv, e ⟨w, (H.mem_neighborFinset v w).mpr hw⟩, ?_⟩
    simp only [b, Equiv.symm_apply_apply]; exact hwx.le
  have h2 : (stdGaussian E).real {x | 0 < ⟪unitKernelRow H q R v, x⟫ ∧ H.degree v = 3 ∧
        ∀ z, H.Adj v z → (⟪unitKernelRow H q R v, x⟫ ≤ 0 ↔ 0 < ⟪unitKernelRow H q R z, x⟫)} ≤
      (if H.degree v = 3 then
        (stdGaussian E).real {x | 0 ≤ ⟪unitKernelRow H q R v, x⟫ ∧ ∀ i, ⟪b i, x⟫ ≤ 0}
      else 0) := by
    split_ifs with hd
    · refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
      obtain ⟨hpos, -, hall⟩ := hx
      refine ⟨hpos.le, fun i => ?_⟩
      simp only [b]
      exact not_lt.mp fun hlt => (not_le.mpr hpos)
        ((hall _ ((H.mem_neighborFinset v _).mp (e.symm i).2)).mpr hlt)
    · have heq : {x : E | 0 < ⟪unitKernelRow H q R v, x⟫ ∧ H.degree v = 3 ∧
          ∀ z, H.Adj v z → (⟪unitKernelRow H q R v, x⟫ ≤ 0 ↔ 0 < ⟪unitKernelRow H q R z, x⟫)} =
          ∅ := by ext x; simp [hd]
      rw [heq, measureReal_empty]
  exact (add_le_add h1 h2).trans (switch_bound hρ0 hρs (hdeg v) (norm_row H q R v)
    (fun i => norm_row H q R _)
    (fun i => hadj v _ ((H.mem_neighborFinset v _).mp (e.symm i).2)))

open Classical in
private theorem measureReal_upperZero_vertex_le {n : ℕ} (H : SimpleGraph (Fin n))
    (hdeg : ∀ v, H.degree v ≤ 3) {q : ℝ} {R : ℕ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρs : ρ ≤ rStar)
    (hadj : ∀ u w, H.Adj u w → ρ ≤ ⟪unitKernelRow H q R u, unitKernelRow H q R w⟫)
    (v : Fin n) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
        {ω | 0 < vertexScore H q R ω v ∧ ∃ u, H.Adj u v ∧ vertexScore H q R ω u ≤ 0} +
      (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
        {ω | vertexScore H q R ω v ≤ 0 ∧ H.degree v = 3 ∧
          ∀ z, H.Adj v z → (vertexScore H q R ω v ≤ 0 ↔ 0 < vertexScore H q R ω z)} ≤
      kappa ρ := by
  set E := EuclideanSpace ℝ (Fin n)
  let e : H.neighborFinset v ≃ Fin (H.degree v) :=
    Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans (H.card_neighborFinset_eq_degree v))
  let b : Fin (H.degree v) → E := fun i => unitKernelRow H q R (e.symm i).1
  have hm : ∀ w, Measurable fun x : E => ⟪unitKernelRow H q R w, x⟫ :=
    measurable_inner_row H q R
  have hm1 : MeasurableSet {x : E | 0 < ⟪unitKernelRow H q R v, x⟫ ∧
      ∃ u, H.Adj u v ∧ ⟪unitKernelRow H q R u, x⟫ ≤ 0} := by
    rw [Set.ofPred_and]
    exact (measurableSet_lt measurable_const (hm v)).inter
      (measurableSet_exists_guard fun u => measurableSet_le (hm u) measurable_const)
  have hm2 : MeasurableSet {x : E | ⟪unitKernelRow H q R v, x⟫ ≤ 0 ∧ H.degree v = 3 ∧
      ∀ z, H.Adj v z → (⟪unitKernelRow H q R v, x⟫ ≤ 0 ↔ 0 < ⟪unitKernelRow H q R z, x⟫)} :=
    measurableSet_crossLo_of_meas H (fun w x => ⟪unitKernelRow H q R w, x⟫) hm v
  change (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
      {ω | WithLp.toLp 2 ω ∈ {x : E | 0 < ⟪unitKernelRow H q R v, x⟫ ∧
        ∃ u, H.Adj u v ∧ ⟪unitKernelRow H q R u, x⟫ ≤ 0}} +
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
      {ω | WithLp.toLp 2 ω ∈ {x : E | ⟪unitKernelRow H q R v, x⟫ ≤ 0 ∧ H.degree v = 3 ∧
        ∀ z, H.Adj v z → (⟪unitKernelRow H q R v, x⟫ ≤ 0 ↔ 0 < ⟪unitKernelRow H q R z, x⟫)}} ≤ _
  rw [measureReal_pi_gaussianReal_eq hm1, measureReal_pi_gaussianReal_eq hm2]
  have h1r : {x : E | 0 < ⟪unitKernelRow H q R v, x⟫ ∧
        ∃ u, H.Adj u v ∧ ⟪unitKernelRow H q R u, x⟫ ≤ 0} =
      Neg.neg ⁻¹' {x : E | ⟪unitKernelRow H q R v, x⟫ < 0 ∧
        ∃ u, H.Adj u v ∧ 0 ≤ ⟪unitKernelRow H q R u, x⟫} := by
    ext x; simp only [mem_ofPred_eq, mem_preimage, inner_neg_right]; constructor <;>
      rintro ⟨h1, u, hu, h2⟩ <;> exact ⟨by linarith, u, hu, by linarith⟩
  have hm1' : MeasurableSet {x : E | ⟪unitKernelRow H q R v, x⟫ < 0 ∧
      ∃ u, H.Adj u v ∧ 0 ≤ ⟪unitKernelRow H q R u, x⟫} := by
    rw [Set.ofPred_and]
    exact (measurableSet_lt (hm v) measurable_const).inter
      (measurableSet_exists_guard fun u => measurableSet_le measurable_const (hm u))
  have h1 : (stdGaussian E).real {x | 0 < ⟪unitKernelRow H q R v, x⟫ ∧
        ∃ u, H.Adj u v ∧ ⟪unitKernelRow H q R u, x⟫ ≤ 0} ≤
      (stdGaussian E).real {x | ⟪unitKernelRow H q R v, x⟫ ≤ 0 ∧ ∃ i, 0 ≤ ⟪b i, x⟫} := by
    rw [h1r, measureReal_neg_preimage_stdGaussian hm1']
    refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    obtain ⟨h1x, u, hu, h2x⟩ := hx
    refine ⟨h1x.le, e ⟨u, (H.mem_neighborFinset v u).mpr hu.symm⟩, ?_⟩
    simp only [b, Equiv.symm_apply_apply]; exact h2x
  have h2 : (stdGaussian E).real {x | ⟪unitKernelRow H q R v, x⟫ ≤ 0 ∧ H.degree v = 3 ∧
        ∀ z, H.Adj v z → (⟪unitKernelRow H q R v, x⟫ ≤ 0 ↔ 0 < ⟪unitKernelRow H q R z, x⟫)} ≤
      (if H.degree v = 3 then
        (stdGaussian E).real {x | 0 ≤ ⟪unitKernelRow H q R v, x⟫ ∧ ∀ i, ⟪b i, x⟫ ≤ 0}
      else 0) := by
    split_ifs with hd
    · have h2r : {x : E | ⟪unitKernelRow H q R v, x⟫ ≤ 0 ∧ H.degree v = 3 ∧
          ∀ z, H.Adj v z → (⟪unitKernelRow H q R v, x⟫ ≤ 0 ↔ 0 < ⟪unitKernelRow H q R z, x⟫)} =
          Neg.neg ⁻¹' ({x : E | 0 ≤ ⟪unitKernelRow H q R v, x⟫} ∩
            ⋂ z, if H.Adj v z then {x : E | ⟪unitKernelRow H q R z, x⟫ < 0} else univ) := by
        ext x; simp only [mem_ofPred_eq, mem_preimage, mem_inter_iff, mem_iInter, inner_neg_right,
          hd, true_and]
        constructor
        · rintro ⟨hle, hall⟩
          refine ⟨by linarith, fun z => ?_⟩
          by_cases hz : H.Adj v z
          · rw [ite_eq_left hz]; simpa [inner_neg_right] using (hall z hz).mp hle
          · rw [ite_eq_right hz]; trivial
        · rintro ⟨hnn, hall⟩
          refine ⟨by linarith, fun z hz => ?_⟩
          have hzt := hall z; rw [ite_eq_left hz] at hzt
          have hpos : 0 < ⟪unitKernelRow H q R z, x⟫ := by simpa [inner_neg_right] using hzt
          exact ⟨fun _ => hpos, fun _ => by linarith⟩
      have hm2' : MeasurableSet ({x : E | 0 ≤ ⟪unitKernelRow H q R v, x⟫} ∩
          ⋂ z, if H.Adj v z then {x : E | ⟪unitKernelRow H q R z, x⟫ < 0} else univ) :=
        (measurableSet_le measurable_const (hm v)).inter (MeasurableSet.iInter fun z => by
          by_cases hz : H.Adj v z
          · rw [ite_eq_left hz]; exact measurableSet_lt (hm z) measurable_const
          · rw [ite_eq_right hz]; exact MeasurableSet.univ)
      rw [h2r, measureReal_neg_preimage_stdGaussian hm2']
      refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
      refine ⟨hx.1, fun i => ?_⟩
      have hadj' : H.Adj v (e.symm i).1 := (H.mem_neighborFinset v _).mp (e.symm i).2
      have := mem_iInter.mp hx.2 (e.symm i).1
      simp only [hadj', ite_true, mem_ofPred_eq] at this
      exact this.le
    · have heq : {x : E | ⟪unitKernelRow H q R v, x⟫ ≤ 0 ∧ H.degree v = 3 ∧
          ∀ z, H.Adj v z → (⟪unitKernelRow H q R v, x⟫ ≤ 0 ↔ 0 < ⟪unitKernelRow H q R z, x⟫)} =
          ∅ := by ext x; simp [hd]
      rw [heq, measureReal_empty]
  exact (add_le_add h1 h2).trans (switch_bound hρ0 hρs (hdeg v) (norm_row H q R v)
    (fun i => norm_row H q R _)
    (fun i => hadj v _ ((H.mem_neighborFinset v _).mp (e.symm i).2)))

/-! ### Simultaneous union bound for one good labeling -/

open Classical in
/-- **A good labeling.** For a simple graph `H` on `Fin n` of maximum degree at most `3`, with
adjacent `unitKernelRow` correlation at least `ρ ∈ (0, rStar]` and `0 ≤ q < 1`, once
`n > (4 * M + 6) * 4 ^ (2 * R + 2) / ε ^ 2`, there exists an injective labeling `y : Fin n → ℝ`
whose negative-level inner frontiers, positive-level outer frontiers, `lowerZero`, and `upperZero`
are all strictly bounded by `switchedBound ρ T ε M * n`. -/
theorem exists_good_labeling {n : ℕ} (H : SimpleGraph (Fin n)) (hdeg : ∀ v, H.degree v ≤ 3)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (R : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρs : ρ ≤ rStar)
    (hadj : ∀ u w, H.Adj u w → ρ ≤ ⟪unitKernelRow H q R u, unitKernelRow H q R w⟫)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (hlarge : ((4 * M + 6 : ℕ) : ℝ) * ((4 ^ (2 * R + 2) : ℕ) : ℝ) / ε ^ 2 < n) :
    ∃ y : Fin n → ℝ, Function.Injective y ∧
      (∀ t : ℝ, t < 0 → ((innerFrontier H y t).card : ℝ) < switchedBound ρ T ε M * n) ∧
      (∀ t : ℝ, 0 < t → ((outerFrontier H y t).card : ℝ) < switchedBound ρ T ε M * n) ∧
      ((lowerZero H y : ℕ) : ℝ) < switchedBound ρ T ε M * n ∧
      ((upperZero H y : ℕ) : ℝ) < switchedBound ρ T ε M * n := by
  set P := Measure.pi fun _ : Fin n => gaussianReal 0 1
  set δ : ℝ := T / M
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hδpos : 0 < δ := div_pos hT hMpos
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hlarge
  set c : ℝ := ε * n
  have hcpos : 0 < c := mul_pos hε hn0
  set D : ℕ := 4 ^ (2 * R + 2)
  have hbound_dev : ∀ A : Fin n → Set (Fin n → ℝ),
      (∀ v, MeasurableSet (A v)) →
      (∀ v, DependsOn (· ∈ A v) (closedBall H v (R + 1))) →
      P.real (deviation A c) ≤ (D : ℝ) / (ε ^ 2 * n) := by
    intro A hAm hAd
    have h := measureReal_deviation_le hAm (fun v => closedBall H v (R + 1)) hAd
      (fun v => card_not_disjoint_closedBall_simple H hdeg R v) hcpos
    rw [Fintype.card_fin] at h
    refine h.trans_eq ?_
    change (n : ℝ) * (D : ℝ) / (ε * n) ^ 2 = (D : ℝ) / (ε ^ 2 * n)
    field_simp [hn0.ne', hε.ne']
  have hball_dep_self : ∀ (p : ℝ → Prop) (v : Fin n),
      DependsOn (· ∈ {ω : Fin n → ℝ | p (vertexScore H q R ω v)}) (closedBall H v (R + 1)) := by
    intro p v ω ω' hω
    have heq : vertexScore H q R ω v = vertexScore H q R ω' v :=
      vertexScore_congr (by simp) hω
    simp only [mem_ofPred_eq, heq]
  let inEv (t : ℝ) (v : Fin n) : Set (Fin n → ℝ) :=
    {ω | vertexScore H q R ω v ≤ t ∧ ∃ w, H.Adj v w ∧ t < vertexScore H q R ω w}
  let outEv (t : ℝ) (v : Fin n) : Set (Fin n → ℝ) :=
    {ω | t < vertexScore H q R ω v ∧ ∃ u, H.Adj u v ∧ vertexScore H q R ω u ≤ t}
  let cellEv (a b : ℝ) (v : Fin n) : Set (Fin n → ℝ) :=
    {ω | a < vertexScore H q R ω v ∧ vertexScore H q R ω v ≤ b}
  let tailLoEv (v : Fin n) : Set (Fin n → ℝ) := {ω | vertexScore H q R ω v ≤ -T}
  let tailHiEv (v : Fin n) : Set (Fin n → ℝ) := {ω | T < vertexScore H q R ω v}
  let crossHiEv (v : Fin n) : Set (Fin n → ℝ) :=
    {ω | 0 < vertexScore H q R ω v ∧ H.degree v = 3 ∧
      ∀ z, H.Adj v z → (vertexScore H q R ω v ≤ 0 ↔ 0 < vertexScore H q R ω z)}
  let crossLoEv (v : Fin n) : Set (Fin n → ℝ) :=
    {ω | vertexScore H q R ω v ≤ 0 ∧ H.degree v = 3 ∧
      ∀ z, H.Adj v z → (vertexScore H q R ω v ≤ 0 ↔ 0 < vertexScore H q R ω z)}
  have hloc {v w : Fin n} (hw : w = v ∨ H.Adj v w) {ω ω' : Fin n → ℝ}
      (hω : ∀ z ∈ closedBall H v (R + 1), ω z = ω' z) :
      vertexScore H q R ω w = vertexScore H q R ω' w :=
    vertexScore_congr (SimpleGraph.edist_le_one_iff_adj_or_eq.mpr (hw.symm.imp id Eq.symm)) hω
  have hdep_in : ∀ t v, DependsOn (· ∈ inEv t v) (closedBall H v (R + 1)) := fun t v ω ω' hω => by
    simp only [inEv, mem_ofPred_eq, hloc (w := v) (.inl rfl) hω, eq_iff_iff]
    exact and_congr_right fun _ => exists_congr fun w => and_congr_right fun hw => by
      rw [hloc (.inr hw) hω]
  have hdep_out : ∀ t v, DependsOn (· ∈ outEv t v) (closedBall H v (R + 1)) := fun t v ω ω' hω => by
    simp only [outEv, mem_ofPred_eq, hloc (w := v) (.inl rfl) hω, eq_iff_iff]
    exact and_congr_right fun _ => exists_congr fun u => and_congr_right fun hu => by
      rw [hloc (.inr hu.symm) hω]
  have hdep_crossHi : ∀ v, DependsOn (· ∈ crossHiEv v) (closedBall H v (R + 1)) :=
    fun v ω ω' hω => by
      simp only [crossHiEv, mem_ofPred_eq, hloc (w := v) (.inl rfl) hω, eq_iff_iff]
      exact and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun z hz => by
        rw [hloc (.inr hz) hω]
  have hdep_crossLo : ∀ v, DependsOn (· ∈ crossLoEv v) (closedBall H v (R + 1)) :=
    fun v ω ω' hω => by
      simp only [crossLoEv, mem_ofPred_eq, hloc (w := v) (.inl rfl) hω, eq_iff_iff]
      exact and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun z hz => by
        rw [hloc (.inr hz) hω]
  have hm_in : ∀ t v, MeasurableSet (inEv t v) := fun t v => by
    have hm := measurable_vertexScore H q R
    dsimp only [inEv]; rw [Set.ofPred_and]
    exact (measurableSet_le (hm v) measurable_const).inter
      (measurableSet_exists_guard fun w => measurableSet_lt measurable_const (hm w))
  have hm_out : ∀ t v, MeasurableSet (outEv t v) := fun t v => by
    have hm := measurable_vertexScore H q R
    dsimp only [outEv]; rw [Set.ofPred_and]
    exact (measurableSet_lt measurable_const (hm v)).inter
      (measurableSet_exists_guard fun u => measurableSet_le (hm u) measurable_const)
  have hm_cell : ∀ a b v, MeasurableSet (cellEv a b v) := fun a b v =>
    (measurableSet_lt measurable_const (measurable_vertexScore H q R v)).inter
      (measurableSet_le (measurable_vertexScore H q R v) measurable_const)
  have hm_tailLo : ∀ v, MeasurableSet (tailLoEv v) := fun v =>
    measurableSet_le (measurable_vertexScore H q R v) measurable_const
  have hm_tailHi : ∀ v, MeasurableSet (tailHiEv v) := fun v =>
    measurableSet_lt measurable_const (measurable_vertexScore H q R v)
  have hm_crossHi : ∀ v, MeasurableSet (crossHiEv v) :=
    measurableSet_crossHi_of_meas H (fun v ω => vertexScore H q R ω v)
      (measurable_vertexScore H q R)
  have hm_crossLo : ∀ v, MeasurableSet (crossLoEv v) :=
    measurableSet_crossLo_of_meas H (fun v ω => vertexScore H q R ω v)
      (measurable_vertexScore H q R)
  set pBound : ℝ := (D : ℝ) / (ε ^ 2 * n)
  let negGrid : ℕ → ℝ := fun i => -((i + 1 : ℕ) : ℝ) * δ
  let posGrid : ℕ → ℝ := fun i => ((i + 1 : ℕ) : ℝ) * δ
  let badNeg : Set (Fin n → ℝ) :=
    ⋃ i ∈ Finset.range M,
      deviation (inEv (negGrid i)) c ∪ deviation (cellEv (negGrid i) (-(i : ℝ) * δ)) c
  let badPos : Set (Fin n → ℝ) :=
    ⋃ i ∈ Finset.range M,
      deviation (outEv (posGrid i)) c ∪ deviation (cellEv ((i : ℝ) * δ) (posGrid i)) c
  let badConst : Set (Fin n → ℝ) :=
    deviation tailLoEv c ∪ deviation tailHiEv c ∪
    deviation (inEv 0) c ∪ deviation crossHiEv c ∪
    deviation (outEv 0) c ∪ deviation crossLoEv c
  let badInj : Set (Fin n → ℝ) := {ω | ¬Function.Injective (vertexScore H q R ω)}
  let bad : Set (Fin n → ℝ) := badNeg ∪ badPos ∪ badConst ∪ badInj
  have hU {s t : Set (Fin n → ℝ)} {a b : ℝ} (hs : P.real s ≤ a) (ht : P.real t ≤ b) :
      P.real (s ∪ t) ≤ a + b :=
    (measureReal_union_le s t).trans (add_le_add hs ht)
  have hPgrid (ev : ℕ → Fin n → Set (Fin n → ℝ)) (a b : ℕ → ℝ) (hm : ∀ i v, MeasurableSet (ev i v))
      (hd : ∀ i v, DependsOn (· ∈ ev i v) (closedBall H v (R + 1))) :
      P.real (⋃ i ∈ Finset.range M, deviation (ev i) c ∪ deviation (cellEv (a i) (b i)) c) ≤
        M * (2 * pBound) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc _ ≤ ∑ _i ∈ Finset.range M, (pBound + pBound) := Finset.sum_le_sum fun i _ =>
          hU (hbound_dev _ (hm i) (hd i)) (hbound_dev _ (hm_cell _ _) fun v =>
            hball_dep_self (fun r => a i < r ∧ r ≤ b i) v)
      _ = M * (2 * pBound) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hPneg : P.real badNeg ≤ M * (2 * pBound) :=
    hPgrid (fun i => inEv (negGrid i)) negGrid (fun i => -(i : ℝ) * δ) (fun _ => hm_in _)
      (fun _ => hdep_in _)
  have hPpos : P.real badPos ≤ M * (2 * pBound) :=
    hPgrid (fun i => outEv (posGrid i)) (fun i => (i : ℝ) * δ) posGrid (fun _ => hm_out _)
      (fun _ => hdep_out _)
  have hPconst : P.real badConst ≤ 6 * pBound := by
    have := hU (hU (hU (hU (hU
      (hbound_dev tailLoEv hm_tailLo (fun v => hball_dep_self (· ≤ -T) v))
      (hbound_dev tailHiEv hm_tailHi (fun v => hball_dep_self (T < ·) v)))
      (hbound_dev (inEv 0) (hm_in 0) (hdep_in 0))) (hbound_dev crossHiEv hm_crossHi hdep_crossHi))
      (hbound_dev (outEv 0) (hm_out 0) (hdep_out 0))) (hbound_dev crossLoEv hm_crossLo hdep_crossLo)
    linarith
  have hPinj : P.real badInj = 0 := measureReal_not_injective_vertexScore H hq0 hq1 R
  have hPbad : P.real bad < 1 := by
    have hsum : (M : ℝ) * (2 * pBound) + (M : ℝ) * (2 * pBound) + 6 * pBound < 1 := by
      convert mul_div_mul_sq_lt_one hε.ne' hn0 hlarge using 1
      simp only [pBound, D]
      field_simp
      push_cast
      ring
    linarith [hU (hU (hU hPneg hPpos) hPconst) hPinj.le]
  have ⟨ω, hω⟩ := exists_notMem_of_measureReal_lt_one hPbad
  simp only [bad, badNeg, badPos, badConst, badInj, mem_union, mem_iUnion, Finset.mem_range,
    not_or, not_exists, mem_ofPred_eq, not_not] at hω
  obtain ⟨⟨⟨hneg, hpos⟩, ⟨⟨⟨⟨⟨htLo, htHi⟩, hin0⟩, hcrHi⟩, hout0⟩, hcrLo⟩⟩, hinj⟩ := hω
  set y : Fin n → ℝ := vertexScore H q R ω
  have hmaxL : (1 / T ^ 2 + ε) * n ≤ switchedBound ρ T ε M * n :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hn0.le
  have hmaxR : (kappa ρ + (T / M) / √(2 * π) + 2 * ε) * n ≤ switchedBound ρ T ε M * n :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hn0.le
  have hsum_le {f : Fin n → ℝ} {B : ℝ} (h : ∀ v, f v ≤ B) : ∑ v, f v ≤ n * B := by
    simpa using Finset.sum_le_card_nsmul Finset.univ f B fun v _ => h v
  have hcard_eq_ncard : ∀ (A : Fin n → Set (Fin n → ℝ)) (s : Finset (Fin n)),
      (∀ v, v ∈ s ↔ ω ∈ A v) → (s.card : ℝ) = ({v | ω ∈ A v}.ncard : ℝ) := fun A s hs => by
    congr 1; rw [← Set.ncard_coe_finset]; congr 1; ext v; exact hs v
  have tail_le : ∀ (s : Finset (Fin n)) (ev : Fin n → Set (Fin n → ℝ)),
      s ⊆ (Finset.univ.filter fun v => ω ∈ ev v) →
      ω ∉ deviation ev c →
      (∀ v x, x ∈ ev v → T ≤ |⟪unitKernelRow H q R v, WithLp.toLp 2 x⟫|) →
      (s.card : ℝ) < switchedBound ρ T ε M * n := by
    intro s ev hsub hdev habs
    have hc := ncard_lt_of_notMem_deviation hdev
    have hmean : ∑ v : Fin n, P.real (ev v) ≤ n * (1 / T ^ 2) := hsum_le fun v =>
      (measureReal_mono (fun x hx => habs v x hx) (measure_ne_top _ _)).trans
        (measureReal_le_abs_le (norm_row H q R v) hT)
    have hcard : (s.card : ℝ) ≤ ({v | ω ∈ ev v}.ncard : ℝ) := by
      calc (s.card : ℝ)
          ≤ ((Finset.univ.filter fun v => ω ∈ ev v).card : ℝ) :=
            Nat.cast_le.mpr (Finset.card_le_card hsub)
        _ = ({v | ω ∈ ev v}.ncard : ℝ) := hcard_eq_ncard ev _ fun v => by simp
    linarith
  have grid_le : ∀ (s s₀ : Finset (Fin n)) (a b : ℝ) (ev : Fin n → Set (Fin n → ℝ)),
      b = a + δ → s ⊆ s₀ ∪ cellSet y a b → (∀ v, v ∈ s₀ ↔ ω ∈ ev v) →
      ω ∉ deviation ev c → ω ∉ deviation (cellEv a b) c →
      (∀ v, P.real (ev v) ≤ kappa ρ) →
      (s.card : ℝ) < switchedBound ρ T ε M * n := by
    intro s s₀ a b ev hadd hsub hs₀ hdevE hdevC hEm
    have hdev1 := ncard_lt_of_notMem_deviation hdevE
    have hdev2 := ncard_lt_of_notMem_deviation hdevC
    have hm1 : ∑ v : Fin n, P.real (ev v) ≤ n * kappa ρ := hsum_le hEm
    have hm2 : ∑ v : Fin n, P.real (cellEv a b v) ≤ n * (δ / √(2 * π)) := by
      subst hadd; exact hsum_le fun v => measureReal_cell_le H q R v a hδpos.le
    have hcard_sum : (s.card : ℝ) ≤ (s₀.card : ℝ) + ((cellSet y a b).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have he1 := hcard_eq_ncard ev s₀ hs₀
    have he2 := hcard_eq_ncard (cellEv a b) (cellSet y a b) fun v => by simp [cellSet, cellEv, y]
    linarith
  have zero_le : ∀ (s₁ s₂ : Finset (Fin n)) (ev₁ ev₂ : Fin n → Set (Fin n → ℝ)),
      (∀ v, v ∈ s₁ ↔ ω ∈ ev₁ v) → (∀ v, v ∈ s₂ ↔ ω ∈ ev₂ v) →
      ω ∉ deviation ev₁ c → ω ∉ deviation ev₂ c →
      (∀ v, P.real (ev₁ v) + P.real (ev₂ v) ≤ kappa ρ) →
      ((s₁.card + s₂.card : ℕ) : ℝ) < switchedBound ρ T ε M * n := by
    intro s₁ s₂ ev₁ ev₂ hs₁ hs₂ hd₁ hd₂ hpt
    have h1 := ncard_lt_of_notMem_deviation hd₁
    have h2 := ncard_lt_of_notMem_deviation hd₂
    have hsum : ∑ v : Fin n, P.real (ev₁ v) + ∑ v : Fin n, P.real (ev₂ v) ≤ n * kappa ρ := by
      rw [← Finset.sum_add_distrib]; exact hsum_le hpt
    have he1 := hcard_eq_ncard ev₁ s₁ hs₁
    have he2 := hcard_eq_ncard ev₂ s₂ hs₂
    have hcell_nn : 0 ≤ (T / M) / √(2 * π) := by positivity
    push_cast
    nlinarith [hn0]
  refine ⟨y, hinj, ?_, ?_, ?_, ?_⟩
  · intro t ht
    by_cases htT : t ≤ -T
    · refine tail_le (innerFrontier H y t) tailLoEv (fun v hv => ?_) htLo (fun v x hx => ?_)
      · simp only [innerFrontier, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        simp only [tailLoEv, Finset.mem_filter, Finset.mem_univ, true_and, mem_ofPred_eq]
        exact hv.1.trans htT
      · simp only [tailLoEv, vertexScore, mem_ofPred_eq] at hx
        rw [abs_of_neg (by linarith)]; linarith
    · have htgt : -T < t := not_le.mp htT
      set i : ℕ := ⌊-t / δ⌋₊
      have hiM : i < M := by
        have hlt : -t / δ < M := by
          rw [div_lt_iff₀ hδpos]
          have : (M : ℝ) * δ = T := by simp only [δ]; field_simp [hMpos.ne']
          linarith
        exact (Nat.floor_lt (div_nonneg (by linarith) hδpos.le)).mpr hlt
      have hlo : negGrid i ≤ t := by
        have h2 := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (-t / δ)) hδpos
        rw [div_mul_cancel₀ _ hδpos.ne'] at h2
        simp only [negGrid]; push_cast; linarith
      have hhi : t ≤ -(i : ℝ) * δ := by
        have h1 : (i : ℝ) ≤ -t / δ := Nat.floor_le (div_nonneg (by linarith) hδpos.le)
        have h2 := mul_le_mul_of_nonneg_right h1 hδpos.le
        rw [div_mul_cancel₀ _ hδpos.ne'] at h2
        linarith
      exact grid_le (innerFrontier H y t) (innerFrontier H y (negGrid i)) (negGrid i)
        (-(i : ℝ) * δ) (inEv (negGrid i)) (by simp only [negGrid]; push_cast; ring)
        (innerFrontier_subset_grid H y hlo hhi) (fun v => by simp [innerFrontier, inEv, y])
        (hneg i hiM).1 (hneg i hiM).2 fun v =>
          measureReal_innerFrontier_le H hdeg hρ0 hρs hadj v (by
            simp only [negGrid]; nlinarith [hδpos.le])
  · intro t ht
    by_cases htT : T < t
    · refine tail_le (outerFrontier H y t) tailHiEv (fun v hv => ?_) htHi (fun v x hx => ?_)
      · simp only [outerFrontier, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        simp only [tailHiEv, Finset.mem_filter, Finset.mem_univ, true_and, mem_ofPred_eq]
        exact htT.trans hv.1
      · simp only [tailHiEv, vertexScore, mem_ofPred_eq] at hx
        exact hx.le.trans (le_abs_self _)
    · set i : ℕ := min ⌊t / δ⌋₊ (M - 1)
      have hiM : i < M := (min_le_right _ _).trans_lt (Nat.sub_lt hM Nat.one_pos)
      have hlo : (i : ℝ) * δ ≤ t := by
        have h1 : (i : ℝ) ≤ t / δ :=
          (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le (div_nonneg ht.le hδpos.le))
        have h2 := mul_le_mul_of_nonneg_right h1 hδpos.le
        rwa [div_mul_cancel₀ _ hδpos.ne'] at h2
      have hhi : t ≤ posGrid i := by
        simp only [posGrid, i]
        rcases le_total ⌊t / δ⌋₊ (M - 1) with h | h
        · have h2 := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (t / δ)) hδpos
          rw [div_mul_cancel₀ _ hδpos.ne'] at h2
          rw [min_eq_left h]; push_cast; linarith
        · rw [min_eq_right h, Nat.sub_add_cancel hM]
          have : (M : ℝ) * δ = T := by simp only [δ]; field_simp [hMpos.ne']
          linarith [not_lt.mp htT]
      exact grid_le (outerFrontier H y t) (outerFrontier H y (posGrid i)) ((i : ℝ) * δ)
        (posGrid i) (outEv (posGrid i)) (by simp only [posGrid]; push_cast; ring)
        (outerFrontier_subset_grid H y hlo hhi)
        (fun v => by simp [outerFrontier, outEv, y, SimpleGraph.adj_comm])
        (hpos i hiM).1 (hpos i hiM).2 fun v =>
          measureReal_outerFrontier_le H hdeg hρ0 hρs hadj v (by
            simp only [posGrid]; positivity)
  · exact zero_le (innerFrontier H y 0) ((crossFull H y).filter fun x => 0 < y x)
      (inEv 0) crossHiEv
      (fun v => by simp [innerFrontier, inEv, y])
      (fun v => by
        simp only [crossFull, crossHiEv, Finset.mem_filter, Finset.mem_univ, true_and,
          mem_ofPred_eq, y]
        lrat_tauto)
      hin0 hcrHi (measureReal_lowerZero_vertex_le H hdeg hρ0 hρs hadj)
  · exact zero_le (outerFrontier H y 0) ((crossFull H y).filter fun x => y x ≤ 0)
      (outEv 0) crossLoEv
      (fun v => by simp [outerFrontier, outEv, y, SimpleGraph.adj_comm])
      (fun v => by
        simp only [crossFull, crossLoEv, Finset.mem_filter, Finset.mem_univ, true_and,
          mem_ofPred_eq, y]
        lrat_tauto)
      hout0 hcrLo (measureReal_upperZero_vertex_le H hdeg hρ0 hρs hadj)

end Cslib.Circuits.Frontier.Switched
