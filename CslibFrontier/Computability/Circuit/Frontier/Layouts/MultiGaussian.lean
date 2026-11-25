/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.MultiOrder
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.VertexGaussian
import CslibFrontier.Foundations.Geometry.Euclidean.Angle.Cap
import CslibFrontier.Foundations.Probability.Gaussian.Sheppard
import CslibFrontier.Tactic.LRATTauto

/-!
# Gaussian vertex layouts of multigraphs

Lay out a loopless multigraph `G` of maximum degree `d` by Gaussian vertex scores
(`Cslib.Circuits.Frontier.Gaussian.vertexScore`), sorting the vertices by score
(`Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_vertexScore`). The kernel rows are those
of the underlying simple graph, while the crossing events are indexed by the edges of `G`, so
parallel edges count with multiplicity.

Fix the grid `-T, -T + δ, ..., T` of `M` windows of width `δ = 2T / M`. Four families of counts
control the frontiers: the edges crossed at each grid threshold, the vertices scoring in each
window, and the vertices scoring in each tail. Each is a count of local events, which
concentrates by the second-moment bound, so for large `|V|` one sample keeps all of them within
`ε |V|` of their means (`Cslib.Circuits.Frontier.Gaussian.exists_width_le_of_unitRows`,
`Cslib.Circuits.Frontier.Gaussian.exists_multi_vertex_sample`). An edge `e` with endpoint inner
product at least `ρ e` is crossed with probability at most `arccos (ρ e) / π`, a vertex scores in a
window with probability at most `δ / √(2π)` and in a tail with probability at most `1 / T ^ 2`. As
the parameters improve for the uniform distance kernel, the width is at most
`vertexCoefficient d · |E| + ξ |V|` for every `ξ > 0`
(`Cslib.Circuits.Frontier.Gaussian.exists_width_le_vertexCoefficient`).

## Main results

* `Cslib.Circuits.Frontier.Gaussian.exists_width_le_of_unitRows`,
  `Cslib.Circuits.Frontier.Gaussian.exists_width_le_of_unitRows_add_mul`: a good sample and its
  `ξ |V|`-slack corollary for arbitrary localized unit rows with edge-dependent correlations.
* `Cslib.Circuits.Frontier.Gaussian.exists_multi_vertex_sample`: specialization to uniform
  distance-kernel rows.
* `Cslib.Circuits.Frontier.Gaussian.exists_width_le_vertexCoefficient`: Gaussian vertex layouts
  of large loopless multigraphs of maximum degree `d`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier.Gaussian

variable {V E : Type*} {G : Multigraph V E} {q : ℝ}

/-- **A good sample for localized unit rows.** Let `G` be a multigraph of maximum degree `d ≥ 2`,
and let `row : V → EuclideanSpace ℝ V` assign each vertex a unit vector supported in the closed
ball of radius `R` around `v` in `G.toSimpleGraph`, with edge inner products
`ρ e ≤ ⟪row (G.src e), row (G.tgt e)⟫`. If `G` has more than
`(M (d + 1) + 2) vertexOverlap d R / ε ^ 2` vertices, some sample of the Gaussian vertex scores
gives a layout of width at most
`(∑_e arccos (ρ e) / π) + |V| (d / T ^ 2 + d (2T / M) / √(2π) + (d + 1) ε)`. -/
theorem exists_width_le_of_unitRows [Fintype V] [Fintype E] (G : Multigraph V E) {d : ℕ}
    (hd : 2 ≤ d) (hdeg : G.MaxDegreeLE d) (R : ℕ) (row : V → EuclideanSpace ℝ V)
    (hunit : ∀ v, ‖row v‖ = 1) (hsupp : ∀ v z, R < G.toSimpleGraph.edist v z → row v z = 0)
    (ρ : E → ℝ) (hcorr : ∀ e : E, ρ e ≤ ⟪row (G.src e), row (G.tgt e)⟫) {T ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (M * (d + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2 < Nat.card V) :
    ∃ σ : Layout V, (G.width σ : ℝ) ≤ (∑ e : E, arccos (ρ e) / π) +
      Nat.card V * (d / T ^ 2 + d * (2 * T / M) / √(2 * π) + (d + 1) * ε) := by
  classical
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  set h : ℝ := ((Nat.card V : ℕ) : ℝ) with hh
  set m : ℝ := ((Nat.card E : ℕ) : ℝ) with hm
  set D : ℝ := ((vertexOverlap d R : ℕ) : ℝ)
  set δ : ℝ := 2 * T / M with hδ
  set c : ℝ := ε * h with hc
  set S_cross : ℝ := ∑ e : E, arccos (ρ e) / π
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  have hcpos : 0 < c := by positivity
  have hδpos : 0 < δ := by positivity
  have hScross0 : 0 ≤ S_cross :=
    Finset.sum_nonneg fun e _ => div_nonneg (arccos_nonneg _) pi_pos.le
  have hmh : m ≤ d * h := by
    rw [hm, hh]
    exact_mod_cast G.card_le_mul_card hdeg
  have hcardV : (Fintype.card V : ℝ) = h := by rw [hh, Nat.card_eq_fintype_card]
  have hcardE : (Fintype.card E : ℝ) = m := by rw [hm, Nat.card_eq_fintype_card]
  let score (ω : V → ℝ) (v : V) : ℝ := ⟪row v, WithLp.toLp 2 ω⟫
  let vEvent (f : ℝ → Prop) (v : V) : Set (V → ℝ) := {ω | f (score ω v)}
  let cEvent (t : ℝ) (e : E) : Set (V → ℝ) := {ω | t ∈ Ι (score ω (G.src e)) (score ω (G.tgt e))}
  have hmeas_score (v : V) : Measurable fun ω : V → ℝ => score ω v := by
    dsimp only [score]
    fun_prop
  have hcongr_score {v : V} {ω ω' : V → ℝ}
      (hω : ∀ z ∈ closedBall G.toSimpleGraph v R, ω z = ω' z) : score ω v = score ω' v :=
    inner_toLp_congr (fun z hz => hsupp v z (lt_of_not_ge hz)) hω
  have hball_succ (v : V) :
      closedBall G.toSimpleGraph v R ⊆ closedBall G.toSimpleGraph v (R + 1) :=
    fun _ (hz : G.toSimpleGraph.edist v _ ≤ R) =>
      (show G.toSimpleGraph.edist v _ ≤ ((R + 1 : ℕ) : ℕ∞) from
        hz.trans (by exact_mod_cast Nat.le_succ R))
  have hdep_v (f : ℝ → Prop) (v : V) :
      DependsOn (· ∈ vEvent f v) (closedBall G.toSimpleGraph v (R + 1)) := by
    intro ω ω' hω
    simp only [vEvent, mem_ofPred_eq]
    rw [hcongr_score fun z hz => hω z (hball_succ v hz)]
  have hdep_c (t : ℝ) (e : E) :
      DependsOn (· ∈ cEvent t e) (closedBall G.toSimpleGraph (G.src e) (R + 1)) := by
    intro ω ω' hω
    simp only [cEvent, mem_ofPred_eq]
    rw [hcongr_score fun z hz => hω z (hball_succ _ hz),
      hcongr_score fun z hz => hω z (closedBall_tgt_subset e R hz)]
  have crossDev (t : ℝ) : P.real (deviation (cEvent t) c) ≤ m * D / c ^ 2 := by
    have := measureReal_deviation_le
      (fun e => measurableSet_setOf_mem_uIoc (hmeas_score _) (hmeas_score _) t)
      (fun e => closedBall G.toSimpleGraph (G.src e) (R + 1)) (hdep_c t)
      (fun e => card_not_disjoint_closedBall_src_le hdeg R e) hcpos
    rwa [hcardE] at this
  have vertexDev {f : ℝ → Prop} (hf : MeasurableSet {x | f x}) :
      P.real (deviation (vEvent f) c) ≤ h * D / c ^ 2 := by
    have := measureReal_deviation_le (fun v => hmeas_score v hf)
      (fun v => closedBall G.toSimpleGraph v (R + 1)) (hdep_v f)
      (fun v => card_not_disjoint_closedBall_le hdeg (by omega) R v) hcpos
    rwa [hcardV] at this
  have hsmall : M * (m * D / c ^ 2 + h * D / c ^ 2) + h * D / c ^ 2 + h * D / c ^ 2 < 1 := by
    calc _ ≤ M * (d * h * D / c ^ 2 + h * D / c ^ 2) + h * D / c ^ 2 + h * D / c ^ 2 := by gcongr
      _ = (M * (d + 1) + 2) * D * h / c ^ 2 := by ring
      _ < 1 := mul_div_mul_sq_lt_one hε.ne' hhpos large
  obtain ⟨ω, hmid, hlow, hhigh⟩ := exists_sample_of_grid_bounds
    (fun i _ => crossDev (-T + i * δ))
    (fun i _ => vertexDev (f := fun x => -T + i * δ ≤ x ∧ x < -T + i * δ + δ)
      ((measurableSet_le measurable_const measurable_id).inter
        (measurableSet_lt measurable_id measurable_const)))
    (vertexDev (f := (· < -T)) (measurableSet_lt measurable_id measurable_const))
    (vertexDev (f := (T ≤ ·)) (measurableSet_le measurable_const measurable_id)) hsmall
  set B := S_cross + h * (d / T ^ 2 + d * δ / √(2 * π) + (d + 1) * ε)
  have vertexMean {f : ℝ → Prop} {b : ℝ} (hb : ∀ v, P.real (vEvent f v) ≤ b) :
      ∑ v, P.real (vEvent f v) ≤ h * b :=
    (Finset.sum_le_sum fun v _ => hb v).trans_eq
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardV])
  have tail (f : ℝ → Prop) (hf : ∀ x, f x → T ≤ |x|) (hdev : ω ∉ deviation (vEvent f) c) :
      d * ({v | ω ∈ vEvent f v}.ncard : ℝ) ≤ B := by
    have hcount := ncard_lt_of_notMem_deviation hdev
    have hmean : ∑ v, P.real (vEvent f v) ≤ h * (1 / T ^ 2) :=
      vertexMean fun v => (measureReal_mono (μ := P) fun ω' hω' => hf _ hω').trans
        (measureReal_le_abs_le (hunit v) hT)
    have hbound : ({v | ω ∈ vEvent f v}.ncard : ℝ) ≤ h / T ^ 2 + c := by grind
    have hnonneg : 0 ≤ S_cross + h * (d * δ / √(2 * π) + ε) := by positivity
    have hidentity : B = d * (h / T ^ 2 + c) + (S_cross + h * (d * δ / √(2 * π) + ε)) := by
      simp only [B, hc]; ring
    rw [hidentity]
    linarith [mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg (α := ℝ) d)]
  have crossCount (t : ℝ) : (G.edgeCut {v | score ω v < t}).ncard =
      {e | ω ∈ cEvent t e}.ncard := by
    congr 1
    ext e
    simp only [Multigraph.mem_edgeCut, cEvent, mem_ofPred_eq, mem_uIoc, ← not_lt]
    lrat_tauto
  have hEdgeCross (t : ℝ) (e : E) : P.real (cEvent t e) ≤ arccos (ρ e) / π := by
    have hu := hunit (G.src e)
    have hv := hunit (G.tgt e)
    refine (measureReal_mem_uIoc_le (hu.trans hv.symm) t).trans ?_
    rw [InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hu hv]
    exact div_le_div_of_nonneg_right (arccos_le_arccos (hcorr e)) pi_pos.le
  have htop : -T + M * δ = T := by rw [hδ]; field_simp; ring
  obtain ⟨σ, hσ⟩ := G.exists_width_le_of_vertexScore hdeg (score ω) hδpos M (a := -T) (B := B)
    (tail (· < -T) (fun x hx => by rw [abs_of_neg (by linarith)]; linarith) hlow)
    (by
      rw [htop]
      exact tail (T ≤ ·) (fun x hx => hx.trans (le_abs_self x)) hhigh)
    (by
      intro i hi
      rw [show -T + ((i : ℝ) + 1) * δ = -T + i * δ + δ by ring]
      have hC := ncard_lt_of_notMem_deviation (hmid i hi).1
      have hW := ncard_lt_of_notMem_deviation (hmid i hi).2
      have hCm : ∑ e, P.real (cEvent (-T + i * δ) e) ≤ S_cross :=
        Finset.sum_le_sum fun e _ => hEdgeCross (-T + i * δ) e
      have hWm := vertexMean (f := fun x => -T + i * δ ≤ x ∧ x < -T + i * δ + δ)
        (b := δ / √(2 * π)) fun v => measureReal_window_le (hunit v) (-T + i * δ) hδpos.le
      have h1 : ((G.edgeCut {v | score ω v < -T + i * δ}).ncard : ℝ) ≤ S_cross + c := by
        rw [crossCount]
        linarith
      have h2 : ({v | -T + i * δ ≤ score ω v ∧ score ω v < -T + i * δ + δ}.ncard : ℝ) ≤
          h * (δ / √(2 * π)) + c := by
        have : ({v | -T + i * δ ≤ score ω v ∧ score ω v < -T + i * δ + δ}.ncard : ℝ) <
            ∑ v, P.real (vEvent (fun x => -T + i * δ ≤ x ∧ x < -T + i * δ + δ) v) + c := hW
        linarith
      have hnonneg : 0 ≤ h * (d / T ^ 2) := by positivity
      have hidentity : B = (S_cross + c) + d * (h * (δ / √(2 * π)) + c) + h * (d / T ^ 2) := by
        simp only [B, hc]; ring
      rw [hidentity]
      linarith [mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) d)])
  exact ⟨σ, hσ⟩

/-- **A good sample.** Let `G` be a loopless multigraph of maximum degree `d ≥ 2`, and let `ρ`
be at most the truncated kernel bound `2 q / (1 + q ^ 2) - d ((d - 1) q ^ 2) ^ R`. If `G` has
more than `(M (d + 1) + 2) vertexOverlap d R / ε ^ 2` vertices, some sample of the Gaussian vertex
scores gives a layout of width at most
`(arccos ρ / π) |E| + |V| (d / T ^ 2 + d (2T / M) / √(2π) + (d + 1) ε)`. -/
theorem exists_multi_vertex_sample [Finite V] [Finite E] (hloop : G.Loopless) {d : ℕ}
    (hd : 2 ≤ d) (hdeg : G.MaxDegreeLE d) (hq : 0 ≤ q) (R : ℕ) {ρ : ℝ}
    (hρ : ρ ≤ 2 * q / (1 + q ^ 2) - d * ((d - 1) * q ^ 2) ^ R) {T ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (M * (d + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2 < Nat.card V) :
    ∃ σ : Layout V, (G.width σ : ℝ) ≤ arccos ρ / π * Nat.card E +
      Nat.card V * (d / T ^ 2 + d * (2 * T / M) / √(2 * π) + (d + 1) * ε) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let _ : Fintype E := Fintype.ofFinite E
  obtain ⟨σ, hσ⟩ := exists_width_le_of_unitRows G hd hdeg R
    (unitKernelRow G.toSimpleGraph q R) (norm_unitKernelRow q R)
    (fun _ _ h => unitKernelRow_eq_zero_of_lt h) (fun _ => ρ)
    (fun e => hρ.trans (le_inner_unitKernelRow_src_tgt hloop hd hdeg hq R e))
    hT hε hM large
  refine ⟨σ, hσ.trans_eq ?_⟩
  congr 1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, mul_comm]

/-- **Asymptotic Gaussian layout bound for localized unit rows.** For every `d ≥ 2`, radius `R`,
and vertex slack `ξ > 0`, there is a threshold `N₀` such that every multigraph `G` of maximum
degree `d` on more than `N₀` vertices, equipped with unit vectors `row` supported in radius-`R`
balls and edge correlation lower bounds `ρ e`, admits a layout of width at most
`(∑_e arccos (ρ e) / π) + ξ |V|`. -/
theorem exists_width_le_of_unitRows_add_mul {d : ℕ} (hd : 2 ≤ d) (R : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Fintype V] [Fintype E] (G : Multigraph V E),
      G.MaxDegreeLE d → N₀ < Nat.card V →
      ∀ (row : V → EuclideanSpace ℝ V), (∀ v, ‖row v‖ = 1) →
        (∀ v z, R < G.toSimpleGraph.edist v z → row v z = 0) →
        ∀ (ρ : E → ℝ), (∀ e : E, ρ e ≤ ⟪row (G.src e), row (G.tgt e)⟫) →
          ∃ σ : Layout V, (G.width σ : ℝ) ≤ (∑ e : E, arccos (ρ e) / π) + ξ * Nat.card V := by
  set D : ℝ := (d : ℝ)
  have hD : 2 ≤ D := by simp only [D]; exact_mod_cast hd
  set T : ℝ := 1 + 4 * D / ξ
  set ε : ℝ := ξ / (4 * (D + 1))
  set M : ℕ := ⌈8 * D * T / ξ⌉₊ + 1
  have hT : 0 < T := by positivity
  have hε : 0 < ε := by positivity
  have hM : 0 < M := Nat.succ_pos _
  have hMR : 8 * D * T / ξ ≤ (M : ℝ) := by
    simp only [M]
    push_cast
    linarith [Nat.le_ceil (8 * D * T / ξ)]
  have htail : D / T ^ 2 ≤ ξ / 4 := by
    have hsq : 4 * D / ξ ≤ T ^ 2 := by
      have hx : 0 ≤ 4 * D / ξ := by positivity
      simp only [T]; nlinarith [sq_nonneg (4 * D / ξ)]
    rw [div_le_iff₀ (sq_pos_of_pos hT)]
    linarith [(div_le_iff₀ hξ).mp hsq]
  have hgrid : D * (2 * T / M) / √(2 * π) ≤ ξ / 4 := by
    have hsqrt : 1 ≤ √(2 * π) :=
      (le_sqrt (by norm_num) (by positivity)).mpr (by linarith [two_le_pi])
    have hfrac : D * (2 * T / M) ≤ ξ / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < M)]
      have H := (div_le_iff₀ hξ).mp hMR
      linarith
    exact (div_le_self (by positivity) hsqrt).trans hfrac
  have herr : D / T ^ 2 + D * (2 * T / M) / √(2 * π) + (D + 1) * ε ≤ ξ := by
    linarith [show (D + 1) * ε = ξ / 4 by simp only [ε]; field_simp]
  refine ⟨⌈((M : ℝ) * (D + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2⌉₊,
    fun V E _ _ G hdeg large row hunit hsupp ρ hcorr => ?_⟩
  have hlarge : ((M : ℝ) * (D + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2 < Nat.card V :=
    (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr large)
  obtain ⟨σ, hσ⟩ := exists_width_le_of_unitRows G hd hdeg R row hunit hsupp ρ hcorr hT hε hM hlarge
  refine ⟨σ, hσ.trans ?_⟩
  have hV := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg (α := ℝ) (Nat.card V))
  linarith

/-- **Gaussian vertex layouts of multigraphs.** For every `ξ > 0`, every large enough loopless
multigraph of maximum degree `d ≥ 2` has a layout of width at most
`vertexCoefficient d · |E| + ξ |V|`, parallel edges counted with multiplicity. -/
theorem exists_width_le_vertexCoefficient {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Finite V] [Finite E] (G : Multigraph V E), G.Loopless →
      G.MaxDegreeLE d → N₀ < Nat.card V →
        ∃ σ : Layout V, (G.width σ : ℝ) ≤ vertexCoefficient d * Nat.card E + ξ * Nat.card V := by
  set D : ℝ := (d : ℝ)
  have hD : 2 ≤ D := by simp only [D]; exact_mod_cast hd
  set g := vertexCorrelation d
  have hg : 0 < g := vertexCorrelation_pos hd
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_arccos.continuousAt (x := g)) (π * ξ / (4 * D)) (by positivity)
  set ρ := g - min η g / 2
  have hmin : 0 < min η g := lt_min hη hg
  have hρg : ρ < g := by simp only [ρ]; linarith
  have hcoef : arccos ρ / π ≤ vertexCoefficient d + ξ / (4 * D) := by
    have hdist : dist ρ g < η := by
      rw [Real.dist_eq, show ρ - g = -(min η g / 2) by simp only [ρ]; ring, abs_neg,
        abs_of_pos (by positivity)]
      linarith [min_le_left η g]
    have H := (le_abs_self _).trans (hcont hdist).le
    rw [div_le_iff₀ pi_pos]
    have heq : (arccos g / π + ξ / (4 * D)) * π = arccos g + π * ξ / (4 * D) := by
      field_simp
    rw [vertexCoefficient, show vertexCorrelation d = g from rfl, heq]
    linarith
  obtain ⟨q, R, hq, hcorr⟩ := exists_decay_radius_degree hd hρg
  obtain ⟨N₀, hN₀⟩ := exists_width_le_of_unitRows_add_mul hd R (ξ := 3 * ξ / 4) (by positivity)
  refine ⟨N₀, fun V E _ _ G hl hdeg large => ?_⟩
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let _ : Fintype E := Fintype.ofFinite E
  obtain ⟨σ, hσ⟩ := hN₀ V E G hdeg large (unitKernelRow G.toSimpleGraph q R)
    (norm_unitKernelRow q R) (fun _ _ h => unitKernelRow_eq_zero_of_lt h) (fun _ => ρ)
    (fun e => hcorr.trans (le_inner_unitKernelRow_src_tgt hl hd hdeg hq R e))
  refine ⟨σ, hσ.trans ?_⟩
  have hsum : (∑ _e : E, arccos ρ / π) = arccos ρ / π * Nat.card E := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, mul_comm]
  rw [hsum]
  have hE : (Nat.card E : ℝ) ≤ D * Nat.card V := by
    simp only [D]
    exact_mod_cast G.card_le_mul_card hdeg
  have herror : ξ / (4 * D) * Nat.card E ≤ ξ / 4 * Nat.card V := by
    have h := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ ξ / (4 * D))
    convert h using 1
    field_simp
  have h1 := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) (Nat.card E))
  nlinarith

end Cslib.Circuits.Frontier.Gaussian
