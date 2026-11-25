/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Cubic
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Sample
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Matching
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Simultaneous Gaussian concentration for matched-edge layouts

Given a loopless cubic multigraph `G` with a matching `M : Set E` (pairwise vertex-disjoint edges),
score the edges of `G` by the unit Gaussian projections `edgeScore G q R ω e` from
`CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.EdgeScores`. The deterministic
threshold cost `Multigraph.matchingCost G M (edgeScore G q R ω) t` decomposes into three local
binary indicator sums:

* unpaired vertices straddling `t` (`unmatchedStraddleEvent`, supported on
  `closedBall G.toSimpleGraph v (R + 1)`, radius `R + 1` around `v`);
* matched edges whose four outer edges straddle `t` (`pairAnyEvent`, supported on
  `closedBall G.toSimpleGraph (G.src e) (R + 2)`, radius `R + 2` around `G.src e`);
* matched edges whose two outer pairs *both* straddle `t` (`pairBothEvent`, supported on
  `closedBall G.toSimpleGraph (G.src e) (R + 2)`, radius `R + 2` around `G.src e`).

Each count concentrates around its expectation under `Measure.pi (fun _ => gaussianReal 0 1)` by
`Cslib.Circuits.Frontier.Gaussian.measureReal_deviation_le`. Over a uniform grid
`-T, -T + δ, ..., T` of `K` windows (`δ = 2T / K`), a union bound over `4 K + 2` deviation events
yields one Gaussian sample `ω` simultaneously controlling the matching cost at each **grid
threshold** `-T + i * δ` (`0 ≤ i < K`), each window edge count `[-T + i * δ, -T + (i + 1) * δ)`,
and both tail edge counts (`< -T` and `≥ T`) (`exists_good_matching_sample_of_mean`).

Thus *any* uniform per-vertex expectation bound `μ ≥ 0` on `expectedMatchingCost` over cubic graphs
implies `CubicLayoutBound μ` (`cubicLayoutBound_of_matching_mean`) and therefore
`LayoutBound 3 (2 * μ)` (`layoutBound_of_matching_mean`). For `M = ∅`, `expectedMatchingCost`
equals the single-vertex straddling sum (`expectedMatchingCost_empty`), recovering the same
asymptotic `CubicLayoutBound μ` as the median-edge-score bound; with a strictly tighter matching
expectation (such as a linear-size matching optimization or the `M_tree ≤ 0.2765836097`
branch-and-bound certificate architecture), it transfers directly to fan-in-two, nondeterministic,
ledger, correlation, and linear circuit lower bounds via `LayoutBound 3 (2 * μ)`.

Note that this module supplies the **conditional reduction** from a uniform single-threshold
expectation bound to a layout bound; it does not prove a specific numerical value of `μ` below
`gaussianCoefficient`.

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.unmatchedStraddleEvent`: local event (supported on radius
  `R + 1` around `v`) for an unpaired vertex straddling threshold `t`.
* `Cslib.Circuits.Frontier.Gaussian.pairAnyEvent`,
  `Cslib.Circuits.Frontier.Gaussian.pairBothEvent`: local events (supported on radius `R + 2`
  around `G.src e`) for a matched edge whose outer edges (resp. both outer pairs) straddle
  threshold `t`.
* `Cslib.Circuits.Frontier.Gaussian.expectedMatchingCost`: expected value of
  `Multigraph.matchingCost` under the standard Gaussian sample.
* `Cslib.Circuits.Frontier.Gaussian.matchingBoundOfMean`: per-vertex width bound of a good sample.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.exists_good_matching_sample_of_mean`: finite-graph
  concentration producing a matched-edge layout of width `≤ |V| * matchingBoundOfMean μ T ε K`.
* `Cslib.Circuits.Frontier.Gaussian.cubicLayoutBound_of_matching_mean`: uniform expectation bound
  `μ` implies `CubicLayoutBound μ`.
* `Cslib.Circuits.Frontier.Gaussian.layoutBound_of_matching_mean`: uniform expectation bound `μ`
  implies `LayoutBound 3 (2 * μ)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace Cslib.Circuits.Frontier.Gaussian

/-- Per-vertex width bound of the matched-edge pair-insertion layout at a concentrated Gaussian
sample, given per-vertex expected matching cost `μ`, tail cutoff `T`, slack `ε`, and `K` grid
windows of width `2T / K`. -/
noncomputable def matchingBoundOfMean (μ T ε : ℝ) (K : ℕ) : ℝ :=
  max (18 / T ^ 2 + 12 * ε) (μ + 18 * (2 * T / K) / √(2 * π) + 15 * ε)

section Events

variable {V E : Type*} [Fintype V] (G : Multigraph V E)

/-- The event that an unpaired vertex `v ∉ G.matchedVertices M` straddles threshold `t` under
Gaussian edge scores `edgeScore G q R`. Supported on `closedBall G.toSimpleGraph v (R + 1)`
(radius `R + 1` around `v`). Empty on matched vertices. -/
noncomputable def unmatchedStraddleEvent (M : Set E) (q : ℝ) (R : ℕ) (t : ℝ) (v : V) :
    Set (V → ℝ) :=
  letI := Classical.propDecidable
  if v ∉ G.matchedVertices M then straddleEvent G q R t v else ∅

/-- The event that a matched edge `e ∈ M` has its four outer incident edges straddling threshold
`t` (`Multigraph.PairStraddlesAny`). Supported on `closedBall G.toSimpleGraph (G.src e) (R + 2)`
(radius `R + 2` around `G.src e`). Empty on unmatched edges. -/
noncomputable def pairAnyEvent (M : Set E) (q : ℝ) (R : ℕ) (t : ℝ) (e : E) : Set (V → ℝ) :=
  letI := Classical.propDecidable
  if e ∈ M then {ω | G.PairStraddlesAny (edgeScore G q R ω) t e} else ∅

/-- The event that a matched edge `e ∈ M` has *both* outer pairs of incident edges straddling
threshold `t` (`Multigraph.PairStraddlesBoth`). Supported on
`closedBall G.toSimpleGraph (G.src e) (R + 2)` (radius `R + 2` around `G.src e`). Empty on
unmatched edges. -/
noncomputable def pairBothEvent (M : Set E) (q : ℝ) (R : ℕ) (t : ℝ) (e : E) : Set (V → ℝ) :=
  letI := Classical.propDecidable
  if e ∈ M then {ω | G.PairStraddlesBoth (edgeScore G q R ω) t e} else ∅

/-- Expected value of `G.matchingCost M (edgeScore G q R ·) t` under `Measure.pi (fun _ =>
gaussianReal 0 1)`, summed directly over the three families of binary indicator events. -/
noncomputable def expectedMatchingCost [Fintype E] (M : Set E) (q : ℝ) (R : ℕ) (t : ℝ) : ℝ :=
  let P := Measure.pi fun _ : V => gaussianReal 0 1
  (∑ v : V, P.real (unmatchedStraddleEvent G M q R t v)) +
    (∑ e : E, P.real (pairAnyEvent G M q R t e)) +
    (∑ e : E, P.real (pairBothEvent G M q R t e))

/-- On the empty matching, `expectedMatchingCost` equals the sum of the single-vertex
straddling probabilities from `Straddle`. -/
theorem expectedMatchingCost_empty [Fintype E] (q : ℝ) (R : ℕ) (t : ℝ) :
    expectedMatchingCost G ∅ q R t =
      ∑ v : V, (Measure.pi fun _ : V => gaussianReal 0 1).real (straddleEvent G q R t v) := by
  simp [expectedMatchingCost, unmatchedStraddleEvent, pairAnyEvent, pairBothEvent,
    Multigraph.matchedVertices_empty]

variable {G}

theorem measurableSet_unmatchedStraddleEvent [Finite E] (M : Set E) (q : ℝ) (R : ℕ)
    (t : ℝ) (v : V) : MeasurableSet (unmatchedStraddleEvent G M q R t v) := by
  classical
  unfold unmatchedStraddleEvent
  split_ifs
  · exact MeasurableSet.empty
  · exact measurableSet_straddleEvent q R t v

theorem dependsOn_unmatchedStraddleEvent (M : Set E) (q : ℝ) (R : ℕ) (t : ℝ) (v : V) :
    DependsOn (· ∈ unmatchedStraddleEvent G M q R t v)
      (closedBall G.toSimpleGraph v (R + 1)) := by
  classical
  intro ω ω' hω
  unfold unmatchedStraddleEvent
  split_ifs
  · rfl
  · exact dependsOn_straddleEvent q R t v hω

omit [Fintype V] in
private theorem closedBall_tgt_subset_src (hloop : G.Loopless) (e : E) (R : ℕ) :
    closedBall G.toSimpleGraph (G.tgt e) (R + 1) ⊆
      closedBall G.toSimpleGraph (G.src e) (R + 2) := by
  intro z hz
  change G.toSimpleGraph.edist (G.src e) z ≤ ((R + 2 : ℕ) : ℕ∞)
  have hadj : G.toSimpleGraph.Adj (G.src e) (G.tgt e) :=
    ⟨⟨e, rfl⟩, hloop e⟩
  have h1 : G.toSimpleGraph.edist (G.src e) (G.tgt e) ≤ 1 :=
    SimpleGraph.edist_le_one_iff_adj_or_eq.mpr (.inl hadj)
  have hz' : G.toSimpleGraph.edist (G.tgt e) z ≤ ((R + 1 : ℕ) : ℕ∞) := hz
  calc G.toSimpleGraph.edist (G.src e) z
      ≤ G.toSimpleGraph.edist (G.src e) (G.tgt e) +
          G.toSimpleGraph.edist (G.tgt e) z := SimpleGraph.edist_triangle
    _ ≤ 1 + ((R + 1 : ℕ) : ℕ∞) := add_le_add h1 hz'
    _ = ((R + 2 : ℕ) : ℕ∞) := by push_cast; ring

theorem edgeScore_congr_of_outer (hloop : G.Loopless) (q : ℝ) (R : ℕ) {e f : E}
    (hf : f ∈ (G.incidenceSet (G.src e) \ {e}) ∪ (G.incidenceSet (G.tgt e) \ {e}))
    {ω ω' : V → ℝ} (hω : ∀ z ∈ closedBall G.toSimpleGraph (G.src e) (R + 2), ω z = ω' z) :
    edgeScore G q R ω f = edgeScore G q R ω' f := by
  rcases hf with hf | hf
  · refine edgeScore_congr hf.1 fun z hz => hω z ?_
    exact (show G.toSimpleGraph.edist (G.src e) z ≤ ((R + 1 : ℕ) : ℕ∞) from hz).trans
      (by exact_mod_cast Nat.le_succ (R + 1))
  · exact edgeScore_congr hf.1 fun z hz => hω z (closedBall_tgt_subset_src hloop e R hz)

theorem measurableSet_pairAnyEvent [Finite E] (M : Set E) (q : ℝ) (R : ℕ) (t : ℝ)
    (e : E) : MeasurableSet (pairAnyEvent G M q R t e) := by
  classical
  unfold pairAnyEvent
  split_ifs with he
  · exact measurableSet_straddlesOn q R t _
  · exact MeasurableSet.empty

theorem measurableSet_pairBothEvent [Finite E] (M : Set E) (q : ℝ) (R : ℕ) (t : ℝ)
    (e : E) : MeasurableSet (pairBothEvent G M q R t e) := by
  classical
  unfold pairBothEvent
  split_ifs with he
  · exact (measurableSet_straddlesOn q R t _).inter (measurableSet_straddlesOn q R t _)
  · exact MeasurableSet.empty

theorem dependsOn_pairAnyEvent (hloop : G.Loopless) (M : Set E) (q : ℝ) (R : ℕ)
    (t : ℝ) (e : E) :
    DependsOn (· ∈ pairAnyEvent G M q R t e)
      (closedBall G.toSimpleGraph (G.src e) (R + 2)) := by
  classical
  intro ω ω' hω
  unfold pairAnyEvent
  split_ifs with he
  · simp only [mem_ofPred_eq, eq_iff_iff]
    exact G.pairStraddlesAny_congr fun f hf => edgeScore_congr_of_outer hloop q R hf hω
  · rfl

theorem dependsOn_pairBothEvent (hloop : G.Loopless) (M : Set E) (q : ℝ) (R : ℕ)
    (t : ℝ) (e : E) :
    DependsOn (· ∈ pairBothEvent G M q R t e)
      (closedBall G.toSimpleGraph (G.src e) (R + 2)) := by
  classical
  intro ω ω' hω
  unfold pairBothEvent
  split_ifs with he
  · simp only [mem_ofPred_eq, eq_iff_iff]
    exact G.pairStraddlesBoth_congr fun f hf => edgeScore_congr_of_outer hloop q R hf hω
  · rfl

private theorem vertexOverlap_three_le_succ (R : ℕ) :
    (vertexOverlap 3 R : ℝ) ≤ (vertexOverlap 3 (R + 1) : ℕ) := by
  refine Nat.cast_le.mpr ?_
  unfold vertexOverlap
  gcongr
  omega

/-- Concentration bound for `unmatchedStraddleEvent` on a `MaxDegreeLE 3` multigraph. -/
theorem measureReal_deviation_unmatchedStraddleEvent_le [Finite E] (hdeg : G.MaxDegreeLE 3)
    (M : Set E) (q : ℝ) (R : ℕ) (t : ℝ) {c : ℝ} (hc : 0 < c) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real
      (deviation (unmatchedStraddleEvent G M q R t) c) ≤
      Fintype.card V * ((vertexOverlap 3 (R + 1) : ℕ) : ℝ) / c ^ 2 := by
  have := Fintype.ofFinite E
  refine (measureReal_deviation_le (fun v => measurableSet_unmatchedStraddleEvent M q R t v)
    (fun v => closedBall G.toSimpleGraph v (R + 1))
    (fun v => dependsOn_unmatchedStraddleEvent M q R t v)
    (fun v => card_not_disjoint_closedBall_le hdeg (by norm_num) R v) hc).trans ?_
  have hmono := vertexOverlap_three_le_succ R
  gcongr

/-- Concentration bound for any edge-indexed event family supported on radius `R + 2` around
`G.src e` in a loopless cubic multigraph. -/
theorem measureReal_deviation_closedBall_src_le [Fintype E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (R : ℕ) {A : E → Set (V → ℝ)}
    (hm : ∀ e, MeasurableSet (A e))
    (hd : ∀ e, DependsOn (· ∈ A e) (closedBall G.toSimpleGraph (G.src e) (R + 2)))
    {c : ℝ} (hc : 0 < c) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real (deviation A c) ≤
      3 / 2 * Fintype.card V * ((vertexOverlap 3 (R + 1) : ℕ) : ℝ) / c ^ 2 := by
  have hdeg : G.MaxDegreeLE 3 := fun v => (h3 v).le
  refine (measureReal_deviation_le hm (fun e => closedBall G.toSimpleGraph (G.src e) (R + 2)) hd
    (fun e => card_not_disjoint_closedBall_src_le hdeg (R + 1) e) hc).trans_eq ?_
  rw [card_edges_eq hloop h3]

/-- Concentration bound for `edgeScoreEvent G q R p` in a loopless cubic multigraph. -/
theorem measureReal_deviation_edgeScoreEvent_le [Fintype E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) {c : ℝ} (hc : 0 < c) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real (deviation (edgeScoreEvent G q R p) c) ≤
      3 / 2 * Fintype.card V * ((vertexOverlap 3 (R + 1) : ℕ) : ℝ) / c ^ 2 := by
  have hdeg : G.MaxDegreeLE 3 := fun v => (h3 v).le
  refine (measureReal_deviation_le (fun e => measurable_edgeScore q R e hp)
    (fun e => closedBall G.toSimpleGraph (G.src e) (R + 1)) (dependsOn_edgeScoreEvent q R p)
    (fun e => card_not_disjoint_closedBall_src_le hdeg R e) hc).trans ?_
  rw [card_edges_eq hloop h3]
  have hmono := vertexOverlap_three_le_succ R
  gcongr

/-- Sample-wise tail edge bound `12 |{e | p (edgeScore e)}| ≤ |V| · (18 / T ^ 2) + 12 c` outside
`deviation (edgeScoreEvent G q R p) c`. -/
theorem twelve_mul_ncard_edgeScore_tail_le [Fintype E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) {q : ℝ} {R : ℕ}
    (hunit : ∀ e, ‖edgeVector G q R e‖ = 1) {T c : ℝ} (hT : 0 < T) {p : ℝ → Prop}
    (hp : ∀ x, p x → T ≤ |x|) {ω : V → ℝ}
    (hdev : ω ∉ deviation (edgeScoreEvent G q R p) c) :
    12 * ({e | p (edgeScore G q R ω e)}.ncard : ℝ) ≤
      Fintype.card V * (18 / T ^ 2) + 12 * c := by
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  set h : ℝ := (Fintype.card V : ℝ)
  have hcount := ncard_lt_of_notMem_deviation hdev
  have hmean_t : ∑ e, P.real (edgeScoreEvent G q R p e) ≤ 3 / 2 * h * (1 / T ^ 2) := by
    refine (Finset.sum_le_sum fun e _ => (measureReal_mono (μ := P) fun ω' hω' =>
      hp _ hω').trans (measureReal_le_abs_le (hunit e) hT)).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_edges_eq hloop h3]
  have hmul : 12 * (3 / 2 * h * (1 / T ^ 2)) = h * (18 / T ^ 2) := by field_simp; ring
  have hset : {e | ω ∈ edgeScoreEvent G q R p e} = {e | p (edgeScore G q R ω e)} := rfl
  rw [hset] at hcount
  linarith

/-- **A good matching sample from a mean bound.** Let `G` be a loopless cubic multigraph
(parallel edges allowed) with a matching `M : Set E`. Suppose the expected `matchingCost` of
`edgeScore G q R` at every threshold `t` is at most `|V| * μ`. Then for `|V| > (6 * K + 3) *
vertexOverlap 3 (R + 1) / ε ^ 2`, some Gaussian sample yields a matched-edge layout of width at
most `|V| * matchingBoundOfMean μ T ε K`. -/
theorem exists_good_matching_sample_of_mean [Fintype E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) {M : Set E} (hM : G.IsMatching M)
    {q : ℝ} (hq : 0 ≤ q) (R : ℕ) {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) {K : ℕ} (hK : 0 < K)
    (large : (6 * K + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2 < Fintype.card V)
    {μ : ℝ} (hmean : ∀ t, expectedMatchingCost G M q R t ≤ Fintype.card V * μ) :
    ∃ σ : Layout V, (G.width σ : ℝ) ≤ Fintype.card V * matchingBoundOfMean μ T ε K := by
  classical
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  set h : ℝ := (Fintype.card V : ℝ)
  set D : ℝ := ((vertexOverlap 3 (R + 1) : ℕ) : ℝ)
  set δ : ℝ := 2 * T / K
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hδpos : 0 < δ := div_pos (by positivity) hKpos
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  set c : ℝ := ε * h
  have hcpos : 0 < c := mul_pos hε hhpos
  have hdeg : G.MaxDegreeLE 3 := fun v => (h3 v).le
  have hE : (Fintype.card E : ℝ) = 3 / 2 * h := card_edges_eq hloop h3
  let grid (i : ℕ) : ℝ := -T + i * δ
  let winEv (i : ℕ) : E → Set (V → ℝ) :=
    edgeScoreEvent G q R fun x => grid i ≤ x ∧ x < grid i + δ
  let badCost (i : ℕ) : Set (V → ℝ) :=
    deviation (unmatchedStraddleEvent G M q R (grid i)) c ∪
      deviation (pairAnyEvent G M q R (grid i)) c ∪
      deviation (pairBothEvent G M q R (grid i)) c
  let badWin (i : ℕ) : Set (V → ℝ) := deviation (winEv i) c
  let badLo : Set (V → ℝ) := deviation (edgeScoreEvent G q R (· < -T)) c
  let badHi : Set (V → ℝ) := deviation (edgeScoreEvent G q R (T ≤ ·)) c
  have hCost_le (i : ℕ) (_ : i < K) : P.real (badCost i) ≤ 4 * h * D / c ^ 2 := by
    have hS := measureReal_deviation_unmatchedStraddleEvent_le hdeg M q R (grid i) hcpos
    have hA := measureReal_deviation_closedBall_src_le hloop h3 R
      (measurableSet_pairAnyEvent M q R (grid i))
      (dependsOn_pairAnyEvent hloop M q R (grid i)) hcpos
    have hB := measureReal_deviation_closedBall_src_le hloop h3 R
      (measurableSet_pairBothEvent M q R (grid i))
      (dependsOn_pairBothEvent hloop M q R (grid i)) hcpos
    refine ((measureReal_union_le _ _).trans
      (add_le_add ((measureReal_union_le _ _).trans (add_le_add hS hA)) hB)).trans_eq ?_
    ring
  have hWin_le (i : ℕ) (_ : i < K) : P.real (badWin i) ≤ 3 / 2 * h * D / c ^ 2 :=
    measureReal_deviation_edgeScoreEvent_le hloop h3 q R
      (measurableSet_Ico : MeasurableSet (Ico (grid i) (grid i + δ))) hcpos
  have hLo_le : P.real badLo ≤ 3 / 2 * h * D / c ^ 2 :=
    measureReal_deviation_edgeScoreEvent_le hloop h3 q R
      (measurableSet_Iio : MeasurableSet (Iio (-T))) hcpos
  have hHi_le : P.real badHi ≤ 3 / 2 * h * D / c ^ 2 :=
    measureReal_deviation_edgeScoreEvent_le hloop h3 q R
      (measurableSet_Ici : MeasurableSet (Ici T)) hcpos
  have hsmall : K * (4 * h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2) +
      3 / 2 * h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2 < 1 := by
    have hlt : (6 * (K : ℝ) + 3) * D < ε ^ 2 * h := by
      have := (div_lt_iff₀ (by positivity : 0 < ε ^ 2)).mp large
      linarith
    have hnum : (K : ℝ) * (4 + 3 / 2) + 3 / 2 + 3 / 2 ≤ 6 * K + 3 := by linarith
    have heq : (K : ℝ) * (4 * h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2) +
        3 / 2 * h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2 =
        ((K : ℝ) * (4 + 3 / 2) + 3 / 2 + 3 / 2) * D / (ε ^ 2 * h) := by
      dsimp [c]
      field_simp
    rw [heq, div_lt_one (by positivity)]
    exact (mul_le_mul_of_nonneg_right hnum (by positivity)).trans_lt hlt
  obtain ⟨ω, hmid, hlo, hhi⟩ := exists_sample_of_grid_bounds hCost_le hWin_le hLo_le hHi_le hsmall
  have unit (e : E) : ‖edgeVector G q R e‖ = 1 :=
    norm_edgeVector hloop hdeg hq hρ₀ hρ e
  set B : ℝ := h * matchingBoundOfMean μ T ε K
  have hB1 : h * (18 / T ^ 2 + 12 * ε) ≤ B :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hhpos.le
  have hB2 : h * (μ + 18 * δ / √(2 * π) + 15 * ε) ≤ B :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hhpos.le
  have tail (p : ℝ → Prop) (hp : ∀ x, p x → T ≤ |x|)
      (hdev : ω ∉ deviation (edgeScoreEvent G q R p) c) :
      12 * ({e | p (edgeScore G q R ω e)}.ncard : ℝ) ≤ B := by
    refine (twelve_mul_ncard_edgeScore_tail_le hloop h3 unit hT hp hdev).trans ?_
    dsimp [c, h] at hB1 ⊢
    linarith
  have htop_eq : -T + K * δ = T := by
    dsimp [δ]; field_simp; ring
  refine Multigraph.exists_width_le_of_matching_edgeScore hloop h3 hM (edgeScore G q R ω)
    hδpos K (a := -T) (B := B)
    (tail (· < -T) (fun x hx => by rw [abs_of_neg (by linarith)]; linarith) hlo)
    (by rw [htop_eq]; exact tail (T ≤ ·) (fun x hx => hx.trans (le_abs_self x)) hhi) ?_
  intro i hi
  have hthr : -T + ((i : ℝ) + 1) * δ = grid i + δ := by dsimp [grid]; ring
  rw [hthr]
  have hS := ncard_lt_of_notMem_deviation fun h => (hmid i hi).1 (Or.inl (Or.inl h))
  have hA := ncard_lt_of_notMem_deviation fun h => (hmid i hi).1 (Or.inl (Or.inr h))
  have hB := ncard_lt_of_notMem_deviation fun h => (hmid i hi).1 (Or.inr h)
  have hW := ncard_lt_of_notMem_deviation (hmid i hi).2
  have hS_eq : {v | ω ∈ unmatchedStraddleEvent G M q R (grid i) v} =
      {v | v ∉ G.matchedVertices M ∧ G.EdgeStraddles (edgeScore G q R ω) (grid i) v} := by
    ext v
    simp [unmatchedStraddleEvent, straddleEvent]
  have hA_eq : {e | ω ∈ pairAnyEvent G M q R (grid i) e} =
      {e | e ∈ M ∧ G.PairStraddlesAny (edgeScore G q R ω) (grid i) e} := by
    ext e
    simp [pairAnyEvent]
  have hB_eq : {e | ω ∈ pairBothEvent G M q R (grid i) e} =
      {e | e ∈ M ∧ G.PairStraddlesBoth (edgeScore G q R ω) (grid i) e} := by
    ext e
    simp [pairBothEvent]
  rw [hS_eq] at hS
  rw [hA_eq] at hA
  rw [hB_eq] at hB
  change ∑ e, P.real (winEv i e) + c >
    ({e | grid i ≤ edgeScore G q R ω e ∧ edgeScore G q R ω e < grid i + δ}.ncard : ℝ) at hW
  have hWmean : ∑ e, P.real (winEv i e) ≤ 3 / 2 * h * (δ / √(2 * π)) := by
    refine (Finset.sum_le_sum fun e _ =>
      measureReal_window_le (unit e) (grid i) hδpos.le).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hE]
  have hEm := hmean (grid i)
  change (G.matchingCost M (edgeScore G q R ω) (grid i) : ℝ) +
    12 * ({e | grid i ≤ edgeScore G q R ω e ∧ edgeScore G q R ω e < grid i + δ}.ncard : ℝ) ≤ B
  unfold Multigraph.matchingCost
  unfold expectedMatchingCost at hEm
  push_cast
  have hsum_w : 12 * (3 / 2 * h * (δ / √(2 * π))) = h * (18 * δ / √(2 * π)) := by ring
  refine le_trans ?_ hB2
  nlinarith

/-- Explicit cutoff `T > 0` and grid subdivision `K > 0` keeping both the Gaussian tail contribution
`18 / T ^ 2` and the window contribution `18 (2 T / K) / √(2 π)` within `ξ / 2`. -/
theorem exists_tail_window_grid {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (T : ℝ) (K : ℕ), 0 < T ∧ 0 < K ∧ 18 / T ^ 2 ≤ ξ / 2 ∧
      18 * (2 * T / K) / √(2 * π) ≤ ξ / 2 := by
  let T := √(36 / ξ) + 1
  let K : ℕ := ⌈72 * T / (ξ * √(2 * π))⌉₊ + 1
  have hT : 0 < T := by positivity
  have hK : 0 < K := Nat.succ_pos _
  have hT_sq : 36 / ξ ≤ T ^ 2 := by
    have h1 : √(36 / ξ) ≤ T := by dsimp [T]; linarith
    calc 36 / ξ = (√(36 / ξ)) ^ 2 := (sq_sqrt (by positivity)).symm
      _ ≤ T ^ 2 := by nlinarith [sqrt_nonneg (36 / ξ)]
  have htail : 18 / T ^ 2 ≤ ξ / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hT_sq (by linarith : (0 : ℝ) ≤ ξ / 2)
    have heq : ξ / 2 * (36 / ξ) = 18 := by field_simp; ring
    linarith
  have hK_le : 72 * T / (ξ * √(2 * π)) ≤ K := by
    have := Nat.le_ceil (72 * T / (ξ * √(2 * π)))
    exact this.trans (by push_cast [K]; linarith)
  have hwin : 18 * (2 * T / K) / √(2 * π) ≤ ξ / 2 := by
    have hsp : 0 < √(2 * π) := sqrt_pos.mpr (by positivity)
    have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hK
    have hstep := mul_le_mul_of_nonneg_left hK_le (by positivity : 0 ≤ ξ * √(2 * π))
    rw [mul_div_cancel₀ _ (by positivity)] at hstep
    have heq : 18 * (2 * T / K) / √(2 * π) = (36 * T) / (K * √(2 * π)) := by ring
    rw [heq, div_le_iff₀ (by positivity)]
    linarith
  exact ⟨T, K, hT, hK, htail, hwin⟩

/-- For every `μ ≥ 0` and `ξ > 0`, explicit cutoff/grid parameters keep `matchingBoundOfMean μ T ε
K` within `μ + ξ`. -/
theorem exists_matching_grid_parameters {μ ξ : ℝ} (hμ : 0 ≤ μ) (hξ : 0 < ξ) :
    ∃ (T ε : ℝ) (K : ℕ), 0 < T ∧ 0 < ε ∧ 0 < K ∧ matchingBoundOfMean μ T ε K ≤ μ + ξ := by
  obtain ⟨T, K, hT, hK, htail, hwin⟩ := exists_tail_window_grid hξ
  refine ⟨T, ξ / 30, K, hT, by positivity, hK, max_le ?_ ?_⟩
  · linarith
  · linarith

/-- **Conditional cubic layout reduction.** Any uniform bound `μ ≥ 0` on the per-vertex expected
`matchingCost` of cubic graphs under Gaussian edge scores `edgeScore G q R` gives
`CubicLayoutBound μ`. -/
theorem cubicLayoutBound_of_matching_mean {μ : ℝ} (hμ : 0 ≤ μ)
    (q : ℝ) (hq : 0 ≤ q) (R : ℕ) {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (hmean : ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E),
      G.Loopless → G.ends.Injective → (∀ v, (G.incidenceSet v).ncard = 3) →
      ∃ M : Set E, G.IsMatching M ∧
        ∀ t, expectedMatchingCost G M q R t ≤ Fintype.card V * μ) :
    CubicLayoutBound μ := by
  intro ξ hξ
  obtain ⟨T, ε, K, hT, hε, hK, hbound⟩ := exists_matching_grid_parameters hμ hξ
  refine ⟨⌈(6 * K + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2⌉₊,
    fun V E _ _ G hloop hinj h3 hN => ?_⟩
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  have hlarge : (6 * K + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2 < Fintype.card V := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.le_ceil _).trans_lt (by exact_mod_cast hN)
  obtain ⟨M, hM, hm⟩ := hmean V E G hloop hinj h3
  obtain ⟨σ, hσ⟩ := exists_good_matching_sample_of_mean hloop h3 hM hq R hρ₀ hρ hT hε hK hlarge hm
  refine ⟨σ, hσ.trans ?_⟩
  rw [Nat.card_eq_fintype_card, mul_comm]
  exact mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _)

/-- **Conditional `LayoutBound 3` reduction.** Any uniform cubic matching-cost expectation bound
`μ ≥ 0` implies `LayoutBound 3 (2 * μ)`, plugging directly into the frontier circuit lower-bound
endpoints (`FanInTwo`, `Nondeterministic`, `Ledger`, `Correlation`, `Linear`). -/
theorem layoutBound_of_matching_mean {μ : ℝ} (hμ : 0 ≤ μ)
    (q : ℝ) (hq : 0 ≤ q) (R : ℕ) {ρ₀ : ℝ} (hρ₀ : -1 < ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (hmean : ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E),
      G.Loopless → G.ends.Injective → (∀ v, (G.incidenceSet v).ncard = 3) →
      ∃ M : Set E, G.IsMatching M ∧
        ∀ t, expectedMatchingCost G M q R t ≤ Fintype.card V * μ) :
    LayoutBound 3 (2 * μ) :=
  LayoutBound.of_cubic hμ (cubicLayoutBound_of_matching_mean hμ q hq R hρ₀ hρ hmean)

end Events

end Cslib.Circuits.Frontier.Gaussian
