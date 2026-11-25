/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.EdgeScores
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Median
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos
import CslibFrontier.Foundations.Geometry.Euclidean.Angle.Cap
import CslibFrontier.Foundations.Probability.Gaussian.Sheppard
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The straddling probability of one vertex

Let `G` be a loopless multigraph in which every vertex has three edges, and let the unit kernel
rows of adjacent vertices have inner product at least `ρ₀ ≥ 0`. The three edge vectors at a
vertex `v` then have inner product at least `κ = √((1 + ρ₀)/2) ≥ √2/2` with the row of `v`: they
lie in a spherical cap.

* If `v` straddles a threshold `t`, then `t` lies between the scores of at least four of the six
  ordered pairs of distinct edges at `v`.
* By Sheppard's bound [Sheppard1899], a pair of edges at angle `θ` is separated by `t` with
  probability at most `θ / π`.
* In the cap the inner products of the pairs lie in `[0, 1]`, where `arccos` is concave, so if
  they sum to at least `6 a` the angles sum to at most `6 arccos a`
  (`Cslib.Circuits.Frontier.Gaussian.measureReal_straddleEvent_le_of_average`). They sum to at
  least `9 κ ^ 2 - 3` (`InnerProductGeometry.le_sum_offDiag_inner`).

Hence `v` straddles `t` with probability at most
`(1/4) (6 / π) arccos ((3 κ ^ 2 - 1)/2) = (3 / (2π)) arccos ((1 + 3 ρ₀)/4)`
(`Cslib.Circuits.Frontier.Gaussian.measureReal_straddleEvent_le`).

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.straddleBound`: the bound
  `(3 / (2π)) arccos ((1 + 3 ρ₀)/4)`.
* `Cslib.Circuits.Frontier.Gaussian.straddleEvent`: the event that a vertex straddles a
  threshold.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.dependsOn_straddleEvent`: locality of straddling.
* `Cslib.Circuits.Frontier.Gaussian.sum_arccos_edgeVector_offDiag_le_of_average`,
  `Cslib.Circuits.Frontier.Gaussian.sum_arccos_edgeVector_offDiag_le`: Jensen and cap bounds on the
  six off-diagonal `arccos` angles at a degree-`3` vertex under `G.MaxDegreeLE 3`.
* `Cslib.Circuits.Frontier.Gaussian.four_mul_measureReal_straddleEvent_le`,
  `Cslib.Circuits.Frontier.Gaussian.measureReal_straddleEvent_le_of_average`,
  `Cslib.Circuits.Frontier.Gaussian.measureReal_straddleEvent_le`: the straddling probability.

## References

* [W. F. Sheppard, *On the application of the theory of error to cases of normal distribution
  and normal correlation*][Sheppard1899]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier.Gaussian

/-- The bound `(3 / (2π)) arccos ((1 + 3 ρ₀)/4)` on the probability that a vertex straddles a
threshold, when adjacent kernel rows have inner product at least `ρ₀`. -/
noncomputable def straddleBound (ρ₀ : ℝ) : ℝ :=
  3 / (2 * π) * arccos ((1 + 3 * ρ₀) / 4)

variable {V E : Type*} [Fintype V] (G : Multigraph V E)

/-- The event that the edge scores at `v` straddle the threshold `t`. -/
def straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : V) : Set (V → ℝ) :=
  {ω | G.EdgeStraddles (edgeScore G q R ω) t v}

variable {G} {q : ℝ} {R : ℕ} {ρ₀ : ℝ}

/-- Whether the edge scores on `S` straddle a threshold `t` is a measurable event. -/
theorem measurableSet_straddlesOn [Finite E] (q : ℝ) (R : ℕ) (t : ℝ) (S : Set E) :
    MeasurableSet {ω | StraddlesOn (edgeScore G q R ω) t S} := by
  have hset : {ω | StraddlesOn (edgeScore G q R ω) t S} =
      (⋃ f ∈ S, {ω | edgeScore G q R ω f < t}) ∩
      (⋃ f ∈ S, {ω | t ≤ edgeScore G q R ω f}) := by
    ext ω
    simp [StraddlesOn]
  exact hset ▸ ((toFinite S).measurableSet_biUnion fun f _ =>
    measurable_edgeScore q R f measurableSet_Iio).inter
    ((toFinite S).measurableSet_biUnion fun f _ => measurable_edgeScore q R f measurableSet_Ici)

/-- Whether a vertex straddles a threshold is a measurable event. -/
theorem measurableSet_straddleEvent [Finite E] (q : ℝ) (R : ℕ) (t : ℝ) (v : V) :
    MeasurableSet (straddleEvent G q R t v) :=
  measurableSet_straddlesOn q R t (G.incidenceSet v)

/-- **Locality.** Whether `v` straddles a threshold depends only on the coordinates of the
sample in the closed ball of radius `R + 1` around `v`. -/
theorem dependsOn_straddleEvent (q : ℝ) (R : ℕ) (t : ℝ) (v : V) :
    DependsOn (· ∈ straddleEvent G q R t v) (closedBall G.toSimpleGraph v (R + 1)) :=
  fun _ _ hω => propext (Multigraph.edgeStraddles_congr fun _ he => edgeScore_congr he hω)

open Classical in
/-- **Four separated pairs.** If three values, indexed by a three-element set `s`, are not all on
one side of a threshold `t`, then `t` lies between the values of at least four of the six ordered
pairs of distinct indices. -/
private theorem four_le_card_filter_offDiag {ι : Type*} {s : Finset ι}
    (hs : s.card = 3) (x : ι → ℝ) {t : ℝ} {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hit : x i < t)
    (hjt : t ≤ x j) : 4 ≤ (s.offDiag.filter fun p : ι × ι => t ∈ Ι (x p.1) (x p.2)).card := by
  set L := s.filter fun k => x k < t
  set U := s.filter fun k => ¬x k < t
  have hLU : L.card + U.card = 3 := (Finset.card_filter_add_card_filter_not _).trans hs
  have hL : 1 ≤ L.card := Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hit⟩⟩
  have hU : 1 ≤ U.card := Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, not_lt.mpr hjt⟩⟩
  have hdisj : Disjoint (L ×ˢ U) (U ×ˢ L) := Finset.disjoint_left.mpr fun p hp hp' =>
    (Finset.mem_filter.mp (Finset.mem_product.mp hp').1).2
      (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
  have hcard : (L ×ˢ U ∪ U ×ˢ L).card ≤
      (s.offDiag.filter fun p : ι × ι => t ∈ Ι (x p.1) (x p.2)).card :=
    Finset.card_le_card fun p hp => by
      simp only [Finset.mem_union, Finset.mem_product, L, U, Finset.mem_filter, not_lt,
        Finset.mem_offDiag, mem_uIoc] at hp ⊢
      rcases hp with ⟨⟨h1, h1'⟩, h2, h2'⟩ | ⟨⟨h1, h1'⟩, h2, h2'⟩
      · exact ⟨⟨h1, h2, fun h => (h ▸ h1').not_ge h2'⟩, Or.inl ⟨h1', h2'⟩⟩
      · exact ⟨⟨h1, h2, fun h => (h ▸ h2').not_ge h1'⟩, Or.inr ⟨h2', h1'⟩⟩
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product] at hcard
  rcases (by omega : L.card = 1 ∨ L.card = 2) with h | h <;> rw [h] at hLU hcard <;> omega

/-- **Counting separated pairs.** If the edges at `v` form a three-element set `s`, then four
times the probability that `v` straddles `t` is at most the sum, over the ordered pairs of
distinct edges at `v`, of the probabilities that `t` separates their scores. -/
theorem four_mul_measureReal_straddleEvent_le [Finite E] {v : V} {s : Finset E}
    (hs : (s : Set E) = G.incidenceSet v) (hcard : s.card = 3) (t : ℝ) :
    4 * (Measure.pi fun _ : V => gaussianReal 0 1).real (straddleEvent G q R t v) ≤
      ∑ p ∈ s.offDiag, (Measure.pi fun _ : V => gaussianReal 0 1).real
        {ω | t ∈ Ι (edgeScore G q R ω p.1) (edgeScore G q R ω p.2)} := by
  classical
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  set B : E × E → Set (V → ℝ) := fun p =>
    {ω | t ∈ Ι (edgeScore G q R ω p.1) (edgeScore G q R ω p.2)}
  have hAm : MeasurableSet (straddleEvent G q R t v) := measurableSet_straddleEvent q R t v
  have hBm (p : E × E) : MeasurableSet (B p) :=
    measurableSet_setOf_mem_uIoc (measurable_edgeScore q R _) (measurable_edgeScore q R _) t
  have hint {C : Set (V → ℝ)} (hC : MeasurableSet C) : Integrable (C.indicator 1) P :=
    (integrable_const (1 : ℝ)).indicator hC
  -- Pointwise, a straddling vertex has at least four separated ordered pairs of edges.
  have hpt (ω : V → ℝ) : (4 : ℝ) * (straddleEvent G q R t v).indicator (1 : (V → ℝ) → ℝ) ω ≤
      ∑ p ∈ s.offDiag, (B p).indicator (1 : (V → ℝ) → ℝ) ω := by
    simp only [indicator_apply, Pi.one_apply, Finset.sum_boole]
    split_ifs with hω
    · obtain ⟨⟨e, he, hlt⟩, ⟨e', he', hle⟩⟩ := hω
      rw [← hs] at he he'
      rw [mul_one]
      exact_mod_cast four_le_card_filter_offDiag hcard (edgeScore G q R ω) he he' hlt hle
    · simp
  rw [← integral_indicator_one hAm, ← integral_const_mul]
  calc ∫ ω, 4 * (straddleEvent G q R t v).indicator 1 ω ∂P
      ≤ ∫ ω, ∑ p ∈ s.offDiag, (B p).indicator 1 ω ∂P :=
        integral_mono ((hint hAm).const_mul 4)
          (integrable_finsetSum s.offDiag fun p _ => hint (hBm p)) (Pi.le_def.mpr hpt)
    _ = ∑ p ∈ s.offDiag, P.real (B p) := by
        rw [integral_finsetSum _ fun p _ => hint (hBm p)]
        exact Finset.sum_congr rfl fun p _ => integral_indicator_one (hBm p)

/-- **Jensen bound on the six off-diagonal `arccos` angles at a degree-`3` vertex** in a loopless
multigraph of maximum degree at most `3`, given a lower bound `6 * a` on the off-diagonal
inner-product sum. -/
theorem sum_arccos_edgeVector_offDiag_le_of_average [Finite E] (hloop : G.Loopless)
    (hdeg : G.MaxDegreeLE 3) (hq : 0 ≤ q) (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {v : V} {s : Finset E}
    (hs : (s : Set E) = G.incidenceSet v) (hcard : s.card = 3) {a : ℝ}
    (haverage : 6 * a ≤ ∑ p ∈ s.offDiag, ⟪edgeVector G q R p.1, edgeVector G q R p.2⟫) :
    ∑ p ∈ s.offDiag, arccos ⟪edgeVector G q R p.1, edgeVector G q R p.2⟫ ≤ 6 * arccos a := by
  have hoff : (s.offDiag.card : ℝ) = 6 := by rw [Finset.offDiag_card, hcard]; norm_num
  have hunit (e : E) : ‖edgeVector G q R e‖ = 1 := norm_edgeVector hloop hdeg hq (by linarith) hρ e
  have hcap (e : E) (he : e ∈ s) : √((1 + ρ₀) / 2) ≤
      ⟪edgeVector G q R e, unitKernelRow G.toSimpleGraph q R v⟫ :=
    le_inner_edgeVector hloop hdeg hq hρ₀ hρ (hs ▸ he)
  have hjensen := Real.sum_arccos_le_card_mul_arccos s.offDiag (fun p hp => by
    obtain ⟨h1, h2, -⟩ := Finset.mem_offDiag.mp hp
    refine ⟨?_, (real_inner_le_norm _ _).trans_eq (by rw [hunit, hunit, one_mul])⟩
    have := InnerProductGeometry.two_mul_sq_sub_one_le_inner (norm_unitKernelRow q R v)
      (hunit p.1) (hunit p.2) (sqrt_nonneg _) (hcap _ h1) (hcap _ h2)
    rw [sq_sqrt (by linarith)] at this
    linarith) (hoff ▸ haverage)
  rwa [hoff] at hjensen

/-- Cap lower bound `6 * ((1 + 3 * ρ₀) / 4)` on the off-diagonal inner-product sum at a degree-`3`
vertex under `G.MaxDegreeLE 3`. -/
private theorem le_sum_edgeVector_offDiag_inner [Finite E] (hloop : G.Loopless)
    (hdeg : G.MaxDegreeLE 3) (hq : 0 ≤ q) (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {v : V} {s : Finset E}
    (hs : (s : Set E) = G.incidenceSet v) (hcard : s.card = 3) :
    6 * ((1 + 3 * ρ₀) / 4) ≤ ∑ p ∈ s.offDiag, ⟪edgeVector G q R p.1, edgeVector G q R p.2⟫ := by
  have h := InnerProductGeometry.le_sum_offDiag_inner (norm_unitKernelRow q R v)
    (s := s) (y := edgeVector G q R) (fun e _ => norm_edgeVector hloop hdeg hq (by linarith) hρ e)
    (sqrt_nonneg ((1 + ρ₀) / 2))
    (fun e he => le_inner_edgeVector hloop hdeg hq hρ₀ hρ (by rw [← hs]; exact he))
  rw [hcard, sq_sqrt (by linarith)] at h
  linarith

/-- **Cap-and-Jensen bound on the six off-diagonal `arccos` angles** at a degree-`3` vertex in a
loopless multigraph of maximum degree at most `3`. -/
theorem sum_arccos_edgeVector_offDiag_le [Finite E] (hloop : G.Loopless)
    (hdeg : G.MaxDegreeLE 3) (hq : 0 ≤ q) (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {v : V} {s : Finset E}
    (hs : (s : Set E) = G.incidenceSet v) (hcard : s.card = 3) :
    ∑ p ∈ s.offDiag, arccos ⟪edgeVector G q R p.1, edgeVector G q R p.2⟫ ≤
      6 * arccos ((1 + 3 * ρ₀) / 4) :=
  sum_arccos_edgeVector_offDiag_le_of_average hloop hdeg hq hρ₀ hρ hs hcard
    (le_sum_edgeVector_offDiag_inner hloop hdeg hq hρ₀ hρ hs hcard)

/-- **The straddling probability, from the average inner product.** In a loopless multigraph in
which every vertex has three edges, let adjacent kernel rows have inner product at least
`ρ₀ ≥ 0`. If the inner products of the edge vectors at `v`, over the ordered pairs of distinct
edges, sum to at least `6 a`, then `v` straddles any fixed threshold with probability at most
`(3 / (2π)) arccos a`. -/
theorem measureReal_straddleEvent_le_of_average [Finite E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (hq : 0 ≤ q) (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) {v : V} {s : Finset E}
    (hs : (s : Set E) = G.incidenceSet v) {a : ℝ}
    (haverage : 6 * a ≤ ∑ p ∈ s.offDiag, ⟪edgeVector G q R p.1, edgeVector G q R p.2⟫) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real (straddleEvent G q R t v) ≤
      3 / (2 * π) * arccos a := by
  have hdeg : G.MaxDegreeLE 3 := fun v => (h3 v).le
  have hcard : s.card = 3 := by rw [← ncard_coe_finset, hs, h3]
  have hunit (e : E) : ‖edgeVector G q R e‖ = 1 := norm_edgeVector hloop hdeg hq (by linarith) hρ e
  have h4 : 4 * (Measure.pi fun _ : V => gaussianReal 0 1).real (straddleEvent G q R t v) ≤
      (∑ p ∈ s.offDiag, arccos ⟪edgeVector G q R p.1, edgeVector G q R p.2⟫) / π :=
    (four_mul_measureReal_straddleEvent_le (q := q) (R := R) hs hcard t).trans
      ((Finset.sum_le_sum fun p _ => by
        rw [← InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one (hunit p.1) (hunit p.2)]
        exact measureReal_mem_uIoc_le ((hunit p.1).trans (hunit p.2).symm) t).trans_eq
        (Finset.sum_div _ _ _).symm)
  have hjensen := sum_arccos_edgeVector_offDiag_le_of_average hloop hdeg hq hρ₀ hρ hs hcard haverage
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith [(le_div_iff₀ pi_pos).mp h4]

/-- **The straddling probability.** In a loopless multigraph in which every vertex has three
edges, if adjacent kernel rows have inner product at least `ρ₀ ≥ 0`, then each vertex straddles
each threshold with probability at most `straddleBound ρ₀`. -/
theorem measureReal_straddleEvent_le [Finite E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (hq : 0 ≤ q) (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) (v : V) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real (straddleEvent G q R t v) ≤
      straddleBound ρ₀ := by
  classical
  obtain ⟨e₀, e₁, e₂, -, -, -, hinc⟩ := ncard_eq_three.mp (h3 v)
  have hs : (({e₀, e₁, e₂} : Finset E) : Set E) = G.incidenceSet v := by simp [hinc]
  exact measureReal_straddleEvent_le_of_average hloop h3 hq hρ₀ hρ t hs
    (le_sum_edgeVector_offDiag_inner hloop (fun w => (h3 w).le) hq hρ₀ hρ hs
      (by rw [← ncard_coe_finset, hs, h3]))

end Cslib.Circuits.Frontier.Gaussian
