/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Cubic
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Switched.Coefficient
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Switched.Sample
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Median-switched Gaussian layouts of cubic graphs

Every large loopless multigraph on `h` vertices in which every vertex has three edges, parallel
edges allowed, has a layout of width at most `(c₃ + ξ) h`, for every `ξ > 0`, where

`c₃ = (3 / (4π)) arccos (5 / 6) ≈ 0.1398221240`

is `Cslib.Circuits.Frontier.Switched.switchedCoefficient`
(`Cslib.Circuits.Frontier.Switched.exists_width_le_switchedCoefficient`). This strictly improves
the median edge-score Gaussian coefficient `p = (3 / (2π)) arccos ((1 + 2√2) / 4) ≈ 0.1403509686`
(`switchedCoefficient_lt_gaussianCoefficient`).

In particular `c₃` is a cubic layout coefficient
(`Cslib.Circuits.Frontier.Switched.cubicLayoutBound_switched`), and through the cubic quotient
of a subcubic multigraph, `2 c₃ = (3 / (2π)) arccos (5 / 6) ≈ 0.279644248` is a layout
coefficient for maximum degree three (`Cslib.Circuits.Frontier.layoutBound_switched`). The
corresponding fan-in-two circuit lower bound is

`L = 1 + 1 / (2 c₃) = 1 + 2π / (3 arccos (5 / 6)) ≈ 4.5759720 ≥ 457597 / 100000`.

The switched sweep adapts [Gaspers2026] (Theorem 1.1(a) / Corollary 1.2, §1.1, p. 1 / PDF p. 3;
proved as Theorem 8.1, §8, p. 45 / PDF p. 47 of arXiv:2611.05146v1, companion release
`doi:10.5281/zenodo.23883489`): score the vertices of the underlying simple graph
`H = G.toSimpleGraph` (of maximum degree at most `3`) by the Gaussian vertex scores
`y v = ⟪unitKernelRow H q R v, ω⟫`, glue inner frontiers below level zero to outer frontiers
above level zero using a bipartite connector order across level zero
(`Cslib.Circuits.Frontier.Switched.Layout.exists_intervals_of_loads`), and convert the resulting
vertex interval decomposition of width `w` to a linear edge-cut layout of width `≤ w + 1` via
`Cslib.Circuits.Frontier.Switched.exists_width_le_of_intervals` (Makedon–Sudborough
`cw ≤ pw + 2`, proved here directly for loopless cubic multigraphs including parallel edges).

**Scope difference from [Gaspers2026].** The paper states Corollary 1.2 (`bw(G) ≤ cw(G) ≤
c₃ n + o(n)`) for simple graphs of maximum degree at most `3`, and also computes the
decomposition in deterministic time `n^{2 + o(1)}`. Here we formalize the *existential*
(non-constructive) edge-cut layout and bisection bounds directly for finite loopless 3-regular
*multigraphs* (parallel edges allowed, `exists_width_le_switchedCoefficient`,
`exists_ncard_edgeCut_le`) and lift them via the saturated compression quotient
(`LayoutBound.of_cubic`) to the cycle-rank layout bound `layoutBound_switched : LayoutBound 3
(2 * switchedCoefficient)` for connected subcubic multigraphs. Algorithmic construction and
higher-degree (`Δ ≥ 4`) / mixed-degree bounds are not formalized here.

## Main results

* `Cslib.Circuits.Frontier.Switched.exists_parameters`: parameters bringing `switchedBound`
  within any `ξ > 0` of `switchedCoefficient`.
* `Cslib.Circuits.Frontier.Switched.exists_width_le_switchedCoefficient`: median-switched
  Gaussian layouts of loopless cubic multigraphs.
* `Cslib.Circuits.Frontier.Switched.cubicLayoutBound_switched`: the cubic layout bound with
  coefficient `switchedCoefficient`.
* `Cslib.Circuits.Frontier.Switched.exists_ncard_edgeCut_le`: large cubic multigraphs have
  sets of any size cut off by at most `(c₃ + ξ) |V|` edges.
* `Cslib.Circuits.Frontier.layoutBound_switched`: `LayoutBound 3 (2 * switchedCoefficient)`.

## References

* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
-/

public section

open Real

namespace Cslib.Circuits.Frontier.Switched

open Cslib.Circuits.Frontier.Gaussian

/-! ### Parameters -/

/-- If `0 < ρ ≤ 2 q / (1 + q ^ 2) - 3 (2 q ^ 2) ^ R` with `0 ≤ q`, then necessarily `q < 1`. -/
private theorem lt_one_of_decay_bound {q ρ : ℝ} {R : ℕ} (hq0 : 0 ≤ q) (hρ : 0 < ρ)
    (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) : q < 1 := by
  by_contra! hge
  have hpow : 1 ≤ (2 * q ^ 2) ^ R := one_le_pow₀ (by nlinarith)
  have hfrac : 2 * q / (1 + q ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (q - 1)]
  linarith

/-- **Parameters.** For every `ξ > 0`, some admissible parameters `q ∈ [0, 1)`, `R`,
`ρ ∈ (0, rStar]`, `T > 0`, `ε > 0`, `M > 0` satisfy `switchedBound ρ T ε M + ε ≤ c₃ + ξ`. -/
theorem exists_parameters {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ T ε : ℝ) (M : ℕ), 0 ≤ q ∧ q < 1 ∧ 0 < ρ ∧ ρ ≤ rStar ∧
      ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧ 0 < T ∧ 0 < ε ∧ 0 < M ∧
      switchedBound ρ T ε M + ε ≤ switchedCoefficient + ξ := by
  have hsqrt_lo : (7 : ℝ) / 5 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_kappa.continuousAt (x := rStar)) (ξ / 4) (by positivity)
  set ρ := rStar - min η (1 / 2) / 2 with hρdef
  have hmin : 0 < min η (1 / 2) := lt_min hη (by norm_num)
  have hρ_lt : ρ < rStar := by linarith
  have hρ_pos : 0 < ρ := by linarith [show rStar = 2 * √2 / 3 from rfl, min_le_right η (1 / 2)]
  have hkappa : kappa ρ ≤ switchedCoefficient + ξ / 4 := by
    have hc := @hcont ρ (by
      rw [Real.dist_eq, hρdef, abs_of_neg (by linarith)]; linarith [min_le_left η (1 / 2)])
    rw [Real.dist_eq, kappa_rStar] at hc
    linarith [le_abs_self (kappa ρ - switchedCoefficient)]
  have h3 : vertexCorrelation 3 = rStar := by norm_num [vertexCorrelation, rStar]
  obtain ⟨q, R, hq0, hdecay⟩ := exists_decay_radius_degree (by norm_num : 2 ≤ 3) (ρ := ρ)
    (h3.symm ▸ hρ_lt)
  norm_num at hdecay
  have hq1 : q < 1 := lt_one_of_decay_bound hq0 hρ_pos hdecay
  set T : ℝ := 10
  have hTpos : 0 < T := by norm_num
  set ε : ℝ := min (ξ / 6) (1 / 100) with hεdef
  have hεpos : 0 < ε := lt_min (by positivity) (by norm_num)
  set M : ℕ := ⌈40 / ξ⌉₊ + 1 with hMdef
  have hMpos : 0 < M := Nat.succ_pos _
  have hMR : 40 / ξ ≤ M := (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  have hMposR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hc_lo : (3 / 32 : ℝ) ≤ switchedCoefficient := by
    have hcos_gt : (5 / 6 : ℝ) ≤ cos (1 / 2) := by
      have := (abs_le.mp (Real.cos_bound (x := (1 / 2 : ℝ)) (by norm_num))).1
      norm_num at this ⊢
      linarith
    have harc : (1 / 2 : ℝ) ≤ arccos (5 / 6) := by
      rw [← Real.arccos_cos (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith [Real.pi_gt_three])]
      exact Real.arccos_le_arccos hcos_gt
    have h1 : 3 / (4 * (4 : ℝ)) ≤ 3 / (4 * π) := by gcongr; exact Real.pi_lt_four.le
    have h2 : 3 / (4 * (4 : ℝ)) * (1 / 2) ≤ 3 / (4 * π) * arccos (5 / 6) := by gcongr
    unfold switchedCoefficient
    linarith
  refine ⟨q, R, ρ, T, ε, M, hq0, hq1, hρ_pos, hρ_lt.le, hdecay, hTpos, hεpos, hMpos, ?_⟩
  rw [switchedBound, ← max_add_add_right]
  have hε_hi : ε ≤ ξ / 6 := min_le_left _ _
  have hε_num : ε ≤ 1 / 100 := min_le_right _ _
  have hsqrtpi : 2 ≤ √(2 * π) :=
    (le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [two_le_pi])
  have hgrid : (T / M) / √(2 * π) ≤ ξ / 4 := by
    refine (div_le_self (by positivity) (by linarith)).trans ?_
    rw [show T = 10 from rfl, div_le_iff₀ hMposR]
    linarith [(div_le_iff₀ hξ).mp hMR]
  refine max_le ?_ (by linarith)
  norm_num [T]
  linarith

/-! ### The layout bounds -/

/-- **Median-switched Gaussian layouts of cubic multigraphs.** For every `ξ > 0`, every large
enough loopless multigraph in which every vertex has three edges, parallel edges allowed, has a
layout of width at most `(switchedCoefficient + ξ) |V|`. -/
theorem exists_width_le_switchedCoefficient {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Finite V] [Finite E] (G : Multigraph V E), G.Loopless →
      (∀ v, (G.incidenceSet v).ncard = 3) → N₀ < Nat.card V →
        ∃ σ : Layout V, (G.width σ : ℝ) ≤ (switchedCoefficient + ξ) * Nat.card V := by
  classical
  obtain ⟨q, R, ρ, T, ε, M, hq0, hq1, hρ0, hρs, hdecay, hT, hε, hM, hbound⟩ :=
    exists_parameters hξ
  set N₀ : ℕ := max ⌈((4 * M + 6 : ℕ) : ℝ) * ((4 ^ (2 * R + 2) : ℕ) : ℝ) / ε ^ 2⌉₊ ⌈3 / ε⌉₊
  refine ⟨N₀, fun V E _ _ G hloop h3 hN => ?_⟩
  have : Fintype V := Fintype.ofFinite V
  set n : ℕ := Nat.card V
  have hlarge : ((4 * M + 6 : ℕ) : ℝ) * ((4 ^ (2 * R + 2) : ℕ) : ℝ) / ε ^ 2 < n :=
    (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr ((le_max_left _ _).trans_lt hN))
  have hlarge3 : 3 / ε < n :=
    (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr ((le_max_right _ _).trans_lt hN))
  have hεn : (3 : ℝ) ≤ ε * n := ((div_lt_iff₀' hε).mp hlarge3).le
  let e : V ≃ Fin n := Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm
  let H : SimpleGraph (Fin n) := SimpleGraph.comap e.symm G.toSimpleGraph
  have hGdeg : G.MaxDegreeLE 3 := fun v => (h3 v).le
  have hHadj_iff : ∀ u v : Fin n, H.Adj u v ↔ G.toSimpleGraph.Adj (e.symm u) (e.symm v) :=
    fun _ _ => Iff.rfl
  have hHdeg : ∀ v : Fin n, H.degree v ≤ 3 := fun v => by
    let hiso : H ≃g G.toSimpleGraph := ⟨e.symm, Iff.rfl⟩
    exact hiso.degree_eq v ▸ hGdeg.degree_toSimpleGraph_le (e.symm v)
  have hHadj : ∀ u w : Fin n, H.Adj u w →
      ρ ≤ inner ℝ (unitKernelRow H q R u) (unitKernelRow H q R w) := fun u w huw =>
    hdecay.trans (by
      have h := le_inner_unitKernelRow (D := 3) (by norm_num) hHdeg hq0 R huw
      norm_num at h
      linarith)
  obtain ⟨y, hy_inj, hin, hout, hlo, hhi⟩ :=
    exists_good_labeling H hHdeg hq0 hq1 R hρ0 hρs hHadj hT hε hM hlarge
  set B : ℝ := switchedBound ρ T ε M * n
  have hBnn : 0 ≤ B := mul_nonneg
    ((by positivity : (0 : ℝ) ≤ 1 / T ^ 2 + ε).trans (le_max_left _ _)) (Nat.cast_nonneg n)
  set w : ℕ := ⌊B⌋₊
  have hwB : (w : ℝ) ≤ B := Nat.floor_le hBnn
  have h_le_w : ∀ k : ℕ, (k : ℝ) < B → k ≤ w := fun k hk => Nat.le_floor hk.le
  obtain ⟨Tend, sH, eH, hse, heT, hedge, hbag⟩ :=
    Switched.Layout.exists_intervals_of_loads H hHdeg y hy_inj w
      (fun t ht => h_le_w _ (hin t ht))
      (fun t ht => h_le_w _ (hout t ht))
      (h_le_w _ hlo)
      (h_le_w _ hhi)
  have hsV : ∀ v : V, sH (e v) ≤ eH (e v) := fun v => hse (e v)
  have heV : ∀ v : V, eH (e v) ≤ Tend := fun v => heT (e v)
  have hedgeV : ∀ a : E, ∃ t ≤ Tend,
      sH (e (G.src a)) ≤ t ∧ t ≤ eH (e (G.src a)) ∧
      sH (e (G.tgt a)) ≤ t ∧ t ≤ eH (e (G.tgt a)) := fun a => by
    have hm := hedge (e (G.src a)) (e (G.tgt a)) (by
      rw [hHadj_iff, e.symm_apply_apply, e.symm_apply_apply]
      exact Multigraph.toSimpleGraph_adj.mpr ⟨hloop a, a, rfl⟩)
    exact ⟨max (sH (e (G.src a))) (sH (e (G.tgt a))), (hm.trans (min_le_left _ _)).trans (heT _),
      le_max_left _ _, hm.trans (min_le_left _ _), le_max_right _ _, hm.trans (min_le_right _ _)⟩
  have hbagV : ∀ t ≤ Tend, (intervalBag (fun v => sH (e v)) (fun v => eH (e v)) t).card ≤
      w + 2 := fun t ht =>
    (Finset.card_equiv e fun _ => by
      simp only [intervalBag, Finset.mem_filter, Finset.mem_univ, true_and]).trans_le (hbag t ht)
  obtain ⟨σ, hσ⟩ := exists_width_le_of_intervals G h3 Tend
    (fun v => sH (e v)) (fun v => eH (e v)) hsV heV hedgeV hbagV
  refine ⟨σ, ?_⟩
  have hσR : (G.width σ : ℝ) ≤ (w : ℝ) + 3 := by exact_mod_cast (hσ : G.width σ ≤ w + 3)
  calc (G.width σ : ℝ) ≤ B + ε * n := by linarith
    _ = (switchedBound ρ T ε M + ε) * n := by rw [add_mul]
    _ ≤ (switchedCoefficient + ξ) * n := by gcongr

/-- **Median-switched Gaussian layouts of cubic graphs.** For every `ξ > 0`, every large enough
simple cubic graph on `h` vertices has a layout of width at most `(c₃ + ξ) h`, where
`c₃ = (3 / (4π)) arccos (5 / 6) ≈ 0.139822`. -/
theorem cubicLayoutBound_switched : CubicLayoutBound switchedCoefficient := fun _ hξ =>
  (exists_width_le_switchedCoefficient hξ).imp fun _ h V E _ _ G hloop _ h3 hN =>
    h V E G hloop h3 hN

/-- **Bisections of cubic multigraphs.** For every `ξ > 0`, every large enough loopless cubic
multigraph, parallel edges allowed, has for every `k ≤ |V|` a set of `k` vertices cut off by at
most `(c₃ + ξ) |V|` edges, where `c₃ = (3 / (4π)) arccos (5 / 6) ≈ 0.139822`. -/
theorem exists_ncard_edgeCut_le {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (V E : Type*) [Finite V] [Finite E] (G : Multigraph V E), G.Loopless →
      (∀ v, (G.incidenceSet v).ncard = 3) → N₀ < Nat.card V → ∀ k ≤ Nat.card V,
        ∃ L : Set V, L.ncard = k ∧
          ((G.edgeCut L).ncard : ℝ) ≤ (switchedCoefficient + ξ) * Nat.card V := by
  obtain ⟨N₀, hN₀⟩ := exists_width_le_switchedCoefficient hξ
  refine ⟨N₀, fun V E _ _ G hloop h3 hN k hk => ?_⟩
  obtain ⟨σ, hσ⟩ := hN₀ V E G hloop h3 hN
  exact ⟨σ.initial k, σ.ncard_initial hk,
    (Nat.cast_le.mpr (G.ncard_frontier_le_width σ k)).trans hσ⟩

end Cslib.Circuits.Frontier.Switched

namespace Cslib.Circuits.Frontier

/-- **The median-switched Gaussian layout bound for maximum degree three.** Large multigraphs of
maximum degree at most three have layouts of width at most `(2 c₃ + ε) β₁`, where
`c₃ = (3 / (4π)) arccos (5 / 6) ≈ 0.139822`, so `2 c₃ = (3 / (2π)) arccos (5 / 6) ≈ 0.279644`. -/
theorem layoutBound_switched : LayoutBound 3 (2 * Switched.switchedCoefficient) :=
  LayoutBound.of_cubic Switched.switchedCoefficient_pos.le Switched.cubicLayoutBound_switched

end Cslib.Circuits.Frontier
