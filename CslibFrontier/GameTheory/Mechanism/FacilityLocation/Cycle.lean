/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Cycle
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.CycleDarts
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.NearVertex
import CslibFrontier.Foundations.Data.Fintype.UpdateInduction
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Basic
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Dictatorship
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Interval
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith

/-!
# Schummer–Vohra cycle dictatorship on metric graphs

This module proves the shortest-cycle case of the cycle dictatorship theorem of
[SchummerVohra2002] (Theorem 2, p. 21 of the January 2001 author preprint, which covers every
cycle): any deterministic strategyproof and onto facility-location mechanism on a finite metric
graph `MetricGraph W` acts as a dictatorship on the points of any shortest cycle `c` (without
assuming the range stays in the cycle, and without assuming group strategyproofness). When
`W.graph` is itself isomorphic to a cycle graph `cycleGraph (n + 3)`, every deterministic
strategyproof onto mechanism is globally a dictatorship.

## Main results

* `Cslib.GameTheory.FacilityLocation.exists_cycleDictator_of_isShortestCycle`: cycle dictatorship
  on an explicit shortest cycle `c` ([SchummerVohra2002]).
* `Cslib.GameTheory.FacilityLocation.exists_cycleDictator_of_not_isAcyclic`: any finite cyclic
  metric graph has a shortest cycle on which every strategyproof onto rule is dictatorial.
* `Cslib.GameTheory.FacilityLocation.exists_dictatorship_of_cycleGraph`: on `cycleGraph (n + 3)`,
  every deterministic strategyproof onto rule is a global dictatorship.

## References

* [J. Schummer and R. V. Vohra, *Strategy-proof Location on a Network*][SchummerVohra2002]
-/

public section

namespace Cslib.GameTheory.FacilityLocation

open SimpleGraph SimpleGraph.MetricGraph

/-! ### Coalition strategyproofness and agent merging -/

section CoalitionAndMerge

private theorem pair_const {G : Type*} (p : G) : (![p, p] : Fin 2 → G) = fun _ => p := by
  ext i; fin_cases i <;> rfl

private theorem sp_pair_left {G : Type*} [MetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] {f : (Fin 2 → G) → G}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof) (a b a' : G) :
    dist a (f ![a, b]) ≤ dist a (f ![a', b]) := by
  have hupd : Function.update ![a, b] 0 a' = ![a', b] := by ext i; fin_cases i <;> rfl
  simpa only [hupd, Matrix.cons_val_zero] using
    (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp ![a, b] 0 a'

private theorem sp_pair_right {G : Type*} [MetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] {f : (Fin 2 → G) → G}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof) (a b b' : G) :
    dist b (f ![a, b]) ≤ dist b (f ![a, b']) := by
  have hupd : Function.update ![a, b] 1 b' = ![a, b'] := by ext i; fin_cases i <;> rfl
  simpa only [hupd, Matrix.cons_val_one, Matrix.cons_val_zero] using
    (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp ![a, b] 1 b'

private theorem coalition_sp {ι G : Type*} [Finite ι] [DecidableEq ι] [MetricSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] {f : (ι → G) → G}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof) (S : Finset ι) (a b : G)
    (x : ι → G) (hx : ∀ i ∈ S, x i = a) :
    dist a (f x) ≤ dist a (f fun i => if i ∈ S then b else x i) := by
  refine Function.update_induction (P := fun z => dist a (f x) ≤ dist a (f z)) le_rfl ?_
  intro z _ hz i hzi hne
  have hiS : i ∈ S := by by_contra h; exact hne (by simp [hzi, h])
  have hstep := (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp z i b
  rw [hzi, hx i hiS] at hstep
  simpa only [hiS, ↓reduceIte] using hz.trans hstep

private theorem merge_isStrategyProof {ι ι' G : Type*} [Finite ι] [DecidableEq ι]
    [DecidableEq ι'] [MetricSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {f : (ι → G) → G} (hf_sp : (Mechanism.deterministic f).IsStrategyProof) (g : ι → ι') :
    (Mechanism.deterministic (fun y : ι' → G => f (fun i => y (g i)))).IsStrategyProof := by
  let _ := Fintype.ofFinite ι
  rw [Mechanism.isStrategyProof_deterministic_iff]
  intro y j z
  let S : Finset ι := Finset.univ.filter fun i => g i = j
  have hfun : (fun i => Function.update y j z (g i)) =
      fun i => if i ∈ S then z else y (g i) := by
    ext i; by_cases hi : g i = j <;> simp [S, hi]
  rw [hfun]
  exact coalition_sp hf_sp S (y j) z (fun i => y (g i)) fun i hi => by
    rw [show g i = j from (Finset.mem_filter.mp hi).2]

/-- Swapping the two agents of a strategyproof mechanism preserves strategyproofness. -/
private theorem swap_isStrategyProof {G : Type*} [MetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] {f : (Fin 2 → G) → G}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof) :
    (Mechanism.deterministic fun x : Fin 2 → G => f ![x 1, x 0]).IsStrategyProof := by
  have heq : (fun x : Fin 2 → G => f ![x 1, x 0]) = fun x => f (fun i => x (![1, 0] i)) := by
    funext x; exact congrArg f (by ext i; fin_cases i <;> rfl)
  exact heq ▸ merge_isStrategyProof hf_sp ![1, 0]

/-- Swapping the two agents preserves unanimity on `S`. -/
private theorem swap_unam {G : Type*} {S : Set G} {f : (Fin 2 → G) → G}
    (hf_unam : ∀ p ∈ S, f (fun _ => p) = p) :
    ∀ p ∈ S, (fun x : Fin 2 → G => f ![x 1, x 0]) (fun _ => p) = p := fun p hp => by
  change f ![p, p] = p; rw [pair_const, hf_unam p hp]

/-- Restricting a strategyproof mechanism to two disjoint coalitions `A` and `B` with fixed reports
outside `A ∪ B` yields a strategyproof two-agent mechanism. -/
private theorem restrictTwo_isStrategyProof {ι G : Type*} [Finite ι] [DecidableEq ι]
    [MetricSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {f : (ι → G) → G} (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    {A B : Finset ι} (hAB : Disjoint A B) (x : ι → G) :
    (Mechanism.deterministic fun y : Fin 2 → G =>
      f fun i => if i ∈ A then y 0 else if i ∈ B then y 1 else x i).IsStrategyProof := by
  rw [Mechanism.isStrategyProof_deterministic_iff]
  intro y j z
  let x' : ι → G := fun i => if i ∈ A then y 0 else if i ∈ B then y 1 else x i
  fin_cases j
  · have hfun : (fun i => if i ∈ A then Function.update y 0 z 0 else
        if i ∈ B then Function.update y 0 z 1 else x i) =
        fun i => if i ∈ A then z else x' i := by
      ext i; by_cases hi : i ∈ A <;> simp [x', hi]
    exact hfun ▸ coalition_sp hf_sp A (y 0) z x' fun i hi => by simp [x', hi]
  · have hfun : (fun i => if i ∈ A then Function.update y 1 z 0 else
        if i ∈ B then Function.update y 1 z 1 else x i) =
        fun i => if i ∈ B then z else x' i := by
      ext i
      by_cases hiA : i ∈ A
      · simp [x', hiA, Finset.disjoint_left.mp hAB hiA]
      · by_cases hiB : i ∈ B <;> simp [x', hiA, hiB]
    exact hfun ▸ coalition_sp hf_sp B (y 1) z x' fun i hi => by
      simp [x', hi, Finset.disjoint_right.mp hAB hi]

end CoalitionAndMerge

/-! ### Local metric-graph and circle geometry helpers -/

section GeometryHelpers

/-- Two darts carrying the same edge and sharing their starting vertex are equal. -/
private theorem dart_eq_of_edge_eq_of_fst_eq {V : Type*} {G : SimpleGraph V}
    {d₁ d₂ : G.Dart} (he : d₁.edge = d₂.edge) (hfst : d₁.fst = d₂.fst) : d₁ = d₂ :=
  ((dart_edge_eq_iff d₁ d₂).mp he).resolve_right fun hsym =>
    d₂.adj.ne (by rw [← hfst, hsym]; rfl)

/-- Re-orienting an `edgePoint` along an equal edge keeps interiority. -/
private theorem exists_edgePoint_reorient {V : Type*} {W : WeightedGraph V}
    {d d' : W.graph.Dart} (he : d'.edge = d.edge) (t' : unitInterval)
    (ht0 : 0 < (t' : ℝ)) (ht1 : (t' : ℝ) < 1) :
    ∃ u : unitInterval, 0 < (u : ℝ) ∧ (u : ℝ) < 1 ∧ edgePoint d' t' = edgePoint d u := by
  rcases (dart_edge_eq_iff d' d).mp he with rfl | rfl
  · exact ⟨t', ht0, ht1, rfl⟩
  · exact ⟨unitInterval.symm t', sub_pos.mpr ht1, sub_lt_self 1 ht0,
      by simpa only [unitInterval.symm_symm] using edgePoint_symm d (unitInterval.symm t')⟩

private theorem edge_eq_of_edgePoint_interior_eq {V : Type*} {W : WeightedGraph V}
    {d d' : W.graph.Dart} {t t' : unitInterval} (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (heq : edgePoint d t = edgePoint d' t') : d.edge = d'.edge := by
  rw [edgePoint_eq_edgePoint_iff] at heq
  rcases heq with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, _, h⟩
  · exact absurd (congrArg Subtype.val h) ht0.ne'
  · exact absurd (congrArg Subtype.val h) ht1.ne
  · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp only [Dart.edge_symm]

/-- Point at arc-length offset `r` along dart `d` (clamped to `[0, W.weight d.edge]`). -/
private noncomputable def rayPt {V : Type*} (W : WeightedGraph V) (d : W.graph.Dart) (r : ℝ) :
    MetricGraph W :=
  edgePoint d (Set.projIcc 0 1 zero_le_one (r / W.weight d.edge))

private theorem rayPt_eq_edgePoint {V : Type*} (W : WeightedGraph V) (d : W.graph.Dart)
    {r : ℝ} (h0 : 0 ≤ r / W.weight d.edge) (h1 : r / W.weight d.edge ≤ 1) :
    rayPt W d r = edgePoint d ⟨r / W.weight d.edge, h0, h1⟩ := by
  simp only [rayPt, Set.projIcc_of_mem zero_le_one ⟨h0, h1⟩]

private theorem edgePoint_eq_rayPt {V : Type*} (W : WeightedGraph V) (d : W.graph.Dart)
    (t : unitInterval) : edgePoint d t = rayPt W d ((t : ℝ) * W.weight d.edge) := by
  have hm : (t : ℝ) * W.weight d.edge / W.weight d.edge = t :=
    mul_div_cancel_right₀ _ (W.dart_weight_pos d).ne'
  rw [rayPt, Set.projIcc_of_mem zero_le_one (by rw [hm]; exact t.2)]
  exact congrArg (edgePoint d) (Subtype.ext hm.symm)

private theorem dist_vertex_rayPt {V : Type*} (W : WeightedGraph V) [Finite V]
    {v : V} {d : W.graph.Dart} (hfst : d.fst = v) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ W.weight d.edge / 2) :
    dist (vertex v : MetricGraph W) (rayPt W d r) = r := by
  have hw := W.dart_weight_pos d
  have h1 : r / W.weight d.edge ≤ 1 := (div_le_one hw).mpr (by linarith)
  rw [rayPt_eq_edgePoint W d (div_nonneg hr0 hw.le) h1, dist_vertex_edgePoint, hfst,
    vertexDist_self W.weight_nonneg, zero_add, div_mul_cancel₀ _ hw.ne',
    sub_mul, one_mul, div_mul_cancel₀ _ hw.ne']
  exact min_eq_left (by linarith [vertexDist_nonneg W.weight_nonneg (G := W.graph) v d.snd])

private theorem dist_rayPt_of_edge_ne {V : Type*} (W : WeightedGraph V) [Finite V]
    {d₁ d₂ : W.graph.Dart} (hfst : d₁.fst = d₂.fst) (hne : d₁.edge ≠ d₂.edge) {r₁ r₂ : ℝ}
    (h10 : 0 ≤ r₁) (h1 : r₁ ≤ W.weight d₁.edge / 2)
    (h20 : 0 ≤ r₂) (h2 : r₂ ≤ W.weight d₂.edge / 2) :
    dist (rayPt W d₁ r₁) (rayPt W d₂ r₂) = r₁ + r₂ := by
  have hw1 := W.dart_weight_pos d₁
  have hw2 := W.dart_weight_pos d₂
  rw [rayPt_eq_edgePoint W d₁ (div_nonneg h10 hw1.le) ((div_le_one hw1).mpr (by linarith)),
    rayPt_eq_edgePoint W d₂ (div_nonneg h20 hw2.le) ((div_le_one hw2).mpr (by linarith)),
    dist_edgePoint_edgePoint_of_fst_eq hne hfst
      ((div_le_iff₀ hw1).mpr (by linarith)) ((div_le_iff₀ hw2).mpr (by linarith)),
    div_mul_cancel₀ _ hw1.ne', div_mul_cancel₀ _ hw2.ne']

private theorem dist_rayPt_same {V : Type*} (W : WeightedGraph V) [Finite V]
    (d : W.graph.Dart) {r₁ r₂ : ℝ} (h10 : 0 ≤ r₁) (h1 : r₁ ≤ W.weight d.edge / 2)
    (h20 : 0 ≤ r₂) (h2 : r₂ ≤ W.weight d.edge / 2) :
    dist (rayPt W d r₁) (rayPt W d r₂) = |r₁ - r₂| := by
  have hw := W.dart_weight_pos d
  have h1' := div_nonneg h10 hw.le
  have h2' := div_nonneg h20 hw.le
  rw [rayPt_eq_edgePoint W d h1' ((div_le_one hw).mpr (by linarith)),
    rayPt_eq_edgePoint W d h2' ((div_le_one hw).mpr (by linarith)),
    dist_edgePoint_edgePoint_of_abs_sub_le_half d (by
      rw [← sub_div, abs_div, abs_of_pos hw, div_le_iff₀ hw, abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩),
    ← sub_div, abs_div, abs_of_pos hw, div_mul_cancel₀ _ hw.ne']

/-- Along a shortest cycle, a parameter step of magnitude at most half the cycle length is
isometric. -/
private theorem dist_circleMap_add_eq_abs {V : Type*} {W : WeightedGraph V} [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    (s d : ℝ) (hdL : |d| ≤ walkLength W.weight c / 2) :
    dist (circleMap hs.1 s) (circleMap hs.1 (s + d)) = |d| := by
  have hsub : |s - (s + d)| = |d| := by rw [sub_add_cancel_left, abs_neg]
  exact (circleMap_dist_eq_of_le hs (hsub ▸ hdL)).trans hsub

/-- Along a shortest cycle, a signed step `σ * d` with `σ = ±1` and `0 ≤ d ≤ L / 2` has distance
`d`. -/
private theorem dist_circleMap_add_mul_dir {V : Type*} {W : WeightedGraph V} [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (s d : ℝ)
    (hd0 : 0 ≤ d) (hdL : d ≤ walkLength W.weight c / 2) :
    dist (circleMap hs.1 s) (circleMap hs.1 (s + σ * d)) = d := by
  have hσ_abs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have habs : |σ * d| = d := by rw [abs_mul, hσ_abs, one_mul, abs_of_nonneg hd0]
  exact (dist_circleMap_add_eq_abs hs s (σ * d) (habs.symm ▸ hdL)).trans habs

/-- A cycle point closer to a third dart out of `v` than half its weight stays at sum-distance. -/
private theorem dist_third_dart_signed {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle)
    {s₀ : ℝ} {v : V} {d₁ d₂ d : W.graph.Dart}
    (hd₁_fst : d₁.fst = v) (hd₂_fst : d₂.fst = v) (hd_fst : d.fst = v)
    (hd₁_ne : d₁.edge ≠ d.edge) (hd₂_ne : d₂.edge ≠ d.edge)
    {δ : ℝ} (hs₀_v : circleMap hc s₀ = vertex v)
    (hfull₁ : ∀ r ∈ Set.Icc 0 δ, circleMap hc (s₀ - r) = rayPt W d₁ r)
    (hfull₂ : ∀ r ∈ Set.Icc 0 δ, circleMap hc (s₀ + r) = rayPt W d₂ r)
    (hδ1 : δ ≤ W.weight d₁.edge / 2) (hδ2 : δ ≤ W.weight d₂.edge / 2)
    {s r_y : ℝ} (hs : s ∈ Set.Icc (-δ) δ)
    (hry0 : 0 ≤ r_y) (hry_le : r_y ≤ W.weight d.edge / 2) :
    dist (circleMap hc (s₀ + s)) (rayPt W d r_y) = |s| + r_y := by
  rcases lt_trichotomy s 0 with hs_neg | rfl | hs_pos
  · rw [show s₀ + s = s₀ - (-s) by ring, hfull₁ (-s) ⟨by linarith, by linarith [hs.1]⟩,
      dist_rayPt_of_edge_ne W (hd₁_fst.trans hd_fst.symm) hd₁_ne
        (by linarith) (by linarith [hs.1]) hry0 hry_le, abs_of_neg hs_neg]
  · rw [add_zero, hs₀_v, abs_zero, zero_add, dist_vertex_rayPt W hd_fst hry0 hry_le]
  · rw [hfull₂ s ⟨hs_pos.le, hs.2⟩, dist_rayPt_of_edge_ne W (hd₂_fst.trans hd_fst.symm) hd₂_ne
      hs_pos.le (by linarith [hs.2]) hry0 hry_le, abs_of_pos hs_pos]

/-- Open interval union-decomposition on a circle: if `R_left, R_right : Set ℝ` are disjoint open
sets, `R_right` is `L`-periodic, and every real fails to belong to either only by separating
`(s - δ, s) ⊆ R_right` from `(s, s + δ) ⊆ R_left`, then one of them is all of `ℝ`. -/
private theorem disjoint_open_periodic_dichotomy {L : ℝ} (hL : 0 < L)
    {R_left R_right : Set ℝ} (hopen_l : IsOpen R_left) (hopen_r : IsOpen R_right)
    (hdisj : Disjoint R_left R_right) (hper_r : ∀ s, s ∈ R_right → s + L ∈ R_right)
    (hclass : ∀ s, s ∈ R_left ∨ s ∈ R_right ∨
      ∃ δ > 0, Set.Ioo (s - δ) s ⊆ R_right ∧ Set.Ioo s (s + δ) ⊆ R_left) :
    Set.univ ⊆ R_left ∨ Set.univ ⊆ R_right := by
  have hcover : R_left ∪ R_right = Set.univ := Set.eq_univ_iff_forall.mpr fun s₀ => by
    by_contra hnot
    rcases hclass s₀ with hl | hr | ⟨δ₀, hδ₀, hIoo_r, hIoo_l⟩
    · exact hnot (Or.inl hl)
    · exact hnot (Or.inr hr)
    · let S_l : Set ℝ := { t | s₀ < t ∧ Set.Ioo s₀ t ⊆ R_left }
      have hSl_ne : S_l.Nonempty := ⟨s₀ + δ₀, by linarith, hIoo_l⟩
      have hSl_bdd : BddAbove S_l := ⟨s₀ + L, fun t ⟨_, ht_sub⟩ => by
        by_contra hgt; push Not at hgt
        let ε := min (δ₀ / 2) (L / 2)
        have hε : 0 < ε := by positivity
        have hpt_r : s₀ + L - ε ∈ R_right := by
          have hmem : s₀ - ε ∈ Set.Ioo (s₀ - δ₀) s₀ :=
            ⟨by linarith [min_le_left (δ₀ / 2) (L / 2)], by linarith⟩
          simpa only [show s₀ - ε + L = s₀ + L - ε by ring] using hper_r (s₀ - ε) (hIoo_r hmem)
        exact Set.disjoint_left.mp hdisj
          (ht_sub ⟨by linarith [min_le_right (δ₀ / 2) (L / 2)], by linarith⟩) hpt_r⟩
      let c₁ := sSup S_l
      have hc₁_gt : s₀ < c₁ := by linarith [le_csSup hSl_bdd ⟨by linarith, hIoo_l⟩]
      have hc₁_sub : Set.Ioo s₀ c₁ ⊆ R_left := fun x ⟨hx1, hx2⟩ =>
        let ⟨_, ⟨_, ht_sub⟩, hxt⟩ := exists_lt_of_lt_csSup hSl_ne hx2; ht_sub ⟨hx1, hxt⟩
      have hno_left_r : ∀ {η : ℝ}, 0 < η → Set.Ioo (c₁ - η) c₁ ⊆ R_right → False :=
        fun {η} hη hsub => by
          let x := max (s₀ + (c₁ - s₀) / 2) (c₁ - η / 2)
          have hxl : x ∈ Set.Ioo s₀ c₁ :=
            ⟨by linarith [le_max_left (s₀ + (c₁ - s₀) / 2) (c₁ - η / 2)],
              max_lt_iff.mpr ⟨by linarith, by linarith⟩⟩
          exact Set.disjoint_left.mp hdisj (hc₁_sub hxl)
            (hsub ⟨by linarith [le_max_right (s₀ + (c₁ - s₀) / 2) (c₁ - η / 2)], hxl.2⟩)
      rcases hclass c₁ with hl | hr | ⟨δ₁, hδ₁, hIoo_r1, _⟩
      · obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hopen_l c₁ hl
        have hmem : c₁ + η / 2 ∈ S_l := ⟨by linarith, fun x ⟨hx1, hx2⟩ => by
          rcases lt_or_ge x c₁ with h | h
          · exact hc₁_sub ⟨hx1, h⟩
          · exact hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)⟩
        linarith [le_csSup hSl_bdd hmem]
      · obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hopen_r c₁ hr
        exact hno_left_r hη fun x ⟨h1, h2⟩ =>
          hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
      · exact hno_left_r hδ₁ hIoo_r1
  have hpre : IsPreconnected (Set.univ : Set ℝ) := PreconnectedSpace.isPreconnected_univ
  rcases Set.eq_univ_iff_forall.mp hcover 0 with h0 | h0
  · exact Or.inl <| hpre.subset_left_of_subset_union hopen_l hopen_r hdisj
      (fun _ _ => hcover ▸ Set.mem_univ _) ⟨0, Set.mem_univ _, h0⟩
  · exact Or.inr <| hpre.subset_left_of_subset_union hopen_r hopen_l hdisj.symm
      (fun _ _ => (Set.union_comm R_left R_right ▸ hcover) ▸ Set.mem_univ _)
      ⟨0, Set.mem_univ _, h0⟩

/-- Turns a locally valid periodic pair-predicate on `ℝ` into a uniform step size `δ₀ > 0`. -/
private theorem uniform_step_of_periodic_local {L : ℝ} (hL : 0 < L) (g : ℝ → ℝ → Prop)
    (hg : ∀ s ∈ Set.Icc 0 L, ∃ η > 0, ∀ u v : ℝ, s - η < u → u ≤ v → v < s + η → g u v)
    (hg_per : ∀ (u v : ℝ) (m : ℤ), g u v → g (u + m * L) (v + m * L)) :
    ∃ δ₀ > 0, ∀ u r : ℝ, 0 ≤ r → r ≤ δ₀ → g u (u + r) := by
  let η (s : Set.Icc 0 L) := (hg s s.2).choose
  have hη_pos (s : Set.Icc 0 L) : 0 < η s := (hg s s.2).choose_spec.1
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
    (fun s : Set.Icc 0 L => Metric.ball (s : ℝ) (η s / 2)) (fun _ => Metric.isOpen_ball)
    fun s hs => Set.mem_iUnion.mpr ⟨⟨s, hs⟩, Metric.mem_ball_self (by linarith [hη_pos ⟨s, hs⟩])⟩
  have ht_ne : t.Nonempty := by
    by_contra hte; rw [Finset.not_nonempty_iff_eq_empty] at hte
    have := ht ⟨le_rfl, hL.le⟩; simp [hte] at this
  let δ₀ := t.inf' ht_ne fun s => η s / 2
  have hδ₀ : 0 < δ₀ := by
    rw [Finset.lt_inf'_iff]
    intro s _
    linarith [hη_pos s]
  refine ⟨δ₀, hδ₀, fun u r hr0 hrδ => ?_⟩
  let k : ℤ := ⌊u / L⌋
  let u' := u - k * L
  have hu'_mem : u' ∈ Set.Icc 0 L :=
    ⟨by nlinarith [Int.floor_le (u / L), div_mul_cancel₀ u hL.ne'],
     by nlinarith [Int.lt_floor_add_one (u / L), div_mul_cancel₀ u hL.ne']⟩
  have hball := ht hu'_mem
  simp only [Set.mem_iUnion, exists_prop, Metric.mem_ball, Real.dist_eq] at hball
  obtain ⟨s, hs_t, hdist⟩ := hball
  have hδs : δ₀ ≤ η s / 2 := Finset.inf'_le _ hs_t
  have hgu' := (hg s s.2).choose_spec.2 u' (u' + r)
    (by linarith [(abs_lt.mp hdist).1]) (by linarith) (by linarith [(abs_lt.mp hdist).2, hδs])
  have h1 : u' + k * L = u := by dsimp only [u']; ring
  have h2 : u' + r + k * L = u + r := by dsimp only [u']; ring
  simpa only [h1, h2] using hg_per u' (u' + r) k hgu'

end GeometryHelpers

/-! ### Two-agent local invariance on a shortest cycle -/

section Fin2CycleDictator

/-- A third-dart outcome of `f ![a, b]` on rays `d_a, d_b` at vertex `v` pulls the outcome at the
closer pair `![a', b']` (`r' = 3/4 * r_y`) within `r_y / 4` of `a'`. -/
private theorem half_step_third_dart_bound {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v : V} {d_a d_b d : W.graph.Dart}
    (ha_fst : d_a.fst = v) (hb_fst : d_b.fst = v) (hd_fst : d.fst = v)
    (hab : d_a.edge ≠ d_b.edge) (hbd : d_b.edge ≠ d.edge)
    {wmin vmin δ r_y r_a r_b : ℝ}
    (hwmin : ∀ d' : W.graph.Dart, wmin ≤ W.weight d'.edge)
    (hvmin : ∀ u w : V, u ≠ w → vmin ≤ dist (vertex u : MetricGraph W) (vertex w))
    (hδ16 : 16 * δ ≤ wmin) (hδv : 16 * δ ≤ vmin)
    (hry_pos : 0 < r_y) (hry_le : r_y ≤ δ)
    (hra_le : r_a ≤ δ) (hry_ra : r_y ≤ r_a) (hrb_le : r_b ≤ δ) (hry_rb : r_y ≤ r_b)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam_b' : f ![rayPt W d_b (3 / 4 * r_y), rayPt W d_b (3 / 4 * r_y)] =
      rayPt W d_b (3 / 4 * r_y))
    (hy_eq : f ![rayPt W d_a r_a, rayPt W d_b r_b] = rayPt W d r_y) :
    dist (rayPt W d_a (3 / 4 * r_y))
      (f ![rayPt W d_a (3 / 4 * r_y), rayPt W d_b (3 / 4 * r_y)]) ≤ 1 / 4 * r_y := by
  set r' := 3 / 4 * r_y
  have hr'0 : 0 < r' := by positivity
  have hr'_le : r' ≤ δ := by dsimp only [r']; linarith
  have hr'_def : r' = 3 / 4 * r_y := rfl
  let a := rayPt W d_a r_a
  let b := rayPt W d_b r_b
  let y := rayPt W d r_y
  let a' := rayPt W d_a r'
  let b' := rayPt W d_b r'
  let y₂ := f ![a, b']
  let y' := f ![a', b']
  have hhalf (d' : W.graph.Dart) {x : ℝ} (hx : x ≤ 4 * δ) : x ≤ W.weight d'.edge / 2 := by
    linarith [hδ16.trans (hwmin d')]
  have hby : dist b y = r_b + r_y := dist_rayPt_of_edge_ne W (hb_fst.trans hd_fst.symm) hbd
    (by linarith) (hhalf _ (by linarith)) hry_pos.le (hhalf _ (by linarith))
  have hb'y : dist b' y = r' + r_y := dist_rayPt_of_edge_ne W (hb_fst.trans hd_fst.symm) hbd
    hr'0.le (hhalf _ (by linarith)) hry_pos.le (hhalf _ (by linarith))
  have hbb' : dist b b' = r_b - r' := by
    rw [dist_rayPt_same W d_b (by linarith) (hhalf _ (by linarith)) hr'0.le
      (hhalf _ (by linarith)), abs_of_nonneg (by linarith)]
  have hsp_b : dist b y ≤ dist b y₂ := by
    have h := sp_pair_right hf_sp a b b'; rwa [hy_eq] at h
  have hsp_b' : dist b' y₂ ≤ dist b' y := by
    have h := sp_pair_right hf_sp a b' b; rwa [hy_eq] at h
  have hby2 : dist b y₂ = r_b + r_y := by linarith [dist_triangle b b' y₂]
  have hb'y2 : dist b' y₂ = r' + r_y := by linarith [dist_triangle b b' y₂]
  have hvb' : dist (vertex v : MetricGraph W) b' = r' :=
    dist_vertex_rayPt W hb_fst hr'0.le (hhalf _ (by linarith))
  have hvy2_le : dist (vertex v : MetricGraph W) y₂ ≤ 3 * δ := by
    linarith [dist_triangle (vertex v : MetricGraph W) b' y₂]
  rcases eq_vertex_or_edgePoint_of_dist_vertex_lt (v := v) (p := y₂)
      (fun u hu => by linarith [hvmin v u hu.symm]) with
    hv_eq | ⟨d₂, t₂, hd₂_fst, ht20, _, hy2_eq, hvy2_eq⟩
  · exfalso
    rw [hv_eq, _root_.dist_comm, hvb'] at hb'y2
    linarith
  let r₂ := (t₂ : ℝ) * W.weight d₂.edge
  have hr2_pos : 0 < r₂ := mul_pos ht20 (W.dart_weight_pos d₂)
  have hr2_le : r₂ ≤ 3 * δ := hvy2_eq.symm.trans_le hvy2_le
  have hy2_ray : y₂ = rayPt W d₂ r₂ := hy2_eq.trans (edgePoint_eq_rayPt W d₂ t₂)
  have hd2_ne_db : d₂.edge ≠ d_b.edge := by
    intro heq; obtain rfl := dart_eq_of_edge_eq_of_fst_eq heq (hd₂_fst.trans hb_fst.symm)
    have h1 : |r' - r₂| = r' + r_y := by
      rw [← dist_rayPt_same W d₂ hr'0.le (hhalf _ (by linarith)) hr2_pos.le
        (hhalf _ (by linarith)), ← hy2_ray, hb'y2]
    have h2 : |r_b - r₂| = r_b + r_y := by
      rw [← dist_rayPt_same W d₂ (by linarith) (hhalf _ (by linarith)) hr2_pos.le
        (hhalf _ (by linarith)), ← hy2_ray, hby2]
    rcases abs_cases (r' - r₂) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases (r_b - r₂) with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  have hr2_eq : r₂ = r_y := by
    have hcalc : dist b' y₂ = r' + r₂ := by
      rw [hy2_ray]
      exact dist_rayPt_of_edge_ne W (hb_fst.trans hd₂_fst.symm)
        hd2_ne_db.symm hr'0.le (hhalf _ (by linarith)) hr2_pos.le (hhalf _ (by linarith))
    linarith
  by_cases hd2_da : d₂.edge = d_a.edge
  · obtain rfl := dart_eq_of_edge_eq_of_fst_eq hd2_da (hd₂_fst.trans ha_fst.symm)
    have ha'y2 : dist a' y₂ = 1 / 4 * r_y := by
      rw [hy2_ray, hr2_eq, dist_rayPt_same W d₂ hr'0.le (hhalf _ (by linarith))
        hry_pos.le (hhalf _ (by linarith)), abs_of_nonpos (by linarith)]
      linarith
    exact (sp_pair_left hf_sp a' b' a).trans ha'y2.le
  · exfalso
    have hay2 : dist a y₂ = r_a + r_y := by
      rw [hy2_ray, hr2_eq, dist_rayPt_of_edge_ne W (ha_fst.trans hd₂_fst.symm)
        (Ne.symm hd2_da) (by linarith) (hhalf _ (by linarith)) hry_pos.le (hhalf _ (by linarith))]
    have haa' : dist a a' = r_a - r' := by
      rw [dist_rayPt_same W d_a (by linarith) (hhalf _ (by linarith))
        hr'0.le (hhalf _ (by linarith)), abs_of_nonneg (by linarith)]
    have ha'b' : dist a' b' = 3 / 2 * r_y := by
      rw [dist_rayPt_of_edge_ne W (ha_fst.trans hb_fst.symm) hab
        hr'0.le (hhalf _ (by linarith)) hr'0.le (hhalf _ (by linarith))]
      linarith
    have hsp_a : dist a y₂ ≤ dist a y' := sp_pair_left hf_sp a b' a'
    have hsp_a' : dist a' y' ≤ dist a' b' := by
      have h := sp_pair_left hf_sp a' b' b'; rwa [hf_unam_b'] at h
    linarith [dist_triangle a a' y']

/-- Two-agent strategyproofness and unanimity keep `f ![c (s₀ + sa), c (s₀ + sb)]` within
`|sa - sb|` of both reports, and within `3 * δ` of `c s₀` when `sa, sb ∈ [-δ, δ]`. -/
private theorem dist_outcome_le_circle {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p)
    {s₀ δ sa sb : ℝ} (hδL : δ ≤ walkLength W.weight c / 16)
    (hsa : sa ∈ Set.Icc (-δ) δ) (hsb : sb ∈ Set.Icc (-δ) δ) :
    dist (circleMap hs.1 (s₀ + sa))
        (f ![circleMap hs.1 (s₀ + sa), circleMap hs.1 (s₀ + sb)]) ≤ |sa - sb| ∧
      dist (circleMap hs.1 (s₀ + sb))
        (f ![circleMap hs.1 (s₀ + sa), circleMap hs.1 (s₀ + sb)]) ≤ |sa - sb| ∧
      dist (circleMap hs.1 s₀)
        (f ![circleMap hs.1 (s₀ + sa), circleMap hs.1 (s₀ + sb)]) ≤ 3 * δ := by
  set a := circleMap hs.1 (s₀ + sa); set b := circleMap hs.1 (s₀ + sb)
  have h1 := abs_le.mpr hsa; have h2 := abs_le.mpr hsb
  have hdab : dist a b = |sa - sb| := by
    rw [show b = circleMap hs.1 ((s₀ + sa) + (sb - sa)) by dsimp only [b]; congr 1; ring,
      dist_circleMap_add_eq_abs hs (s₀ + sa) (sb - sa)
        (by linarith [abs_sub sb sa, abs_nonneg sa, hδL]), abs_sub_comm]
  have hda : dist a (f ![a, b]) ≤ |sa - sb| := by
    have h := sp_pair_left hf_sp a b b
    rwa [pair_const, hf_unam b ⟨s₀ + sb, rfl⟩, hdab] at h
  have hdb : dist b (f ![a, b]) ≤ |sa - sb| := by
    have h := sp_pair_right hf_sp a b a
    rwa [pair_const, hf_unam a ⟨s₀ + sa, rfl⟩, _root_.dist_comm b a, hdab] at h
  have hdsa : dist (circleMap hs.1 s₀) a = |sa| :=
    dist_circleMap_add_eq_abs hs s₀ sa (by linarith [abs_nonneg sa, hδL])
  refine ⟨hda, hdb, ?_⟩
  linarith [dist_triangle (circleMap hs.1 s₀) a (f ![a, b]), abs_sub sa sb]

/-- A cycle point `c (s₀ + r)` with `|r| ≤ 3 * δ` within `|sa - sb|` of both `c (s₀ + sa)` and
`c (s₀ + sb)` lies in the image of `[-δ, δ]`. -/
private theorem mem_image_Icc_of_dist_le_circle {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {s₀ δ sa sb r : ℝ} (hδL : δ ≤ walkLength W.weight c / 16)
    (hsa : sa ∈ Set.Icc (-δ) δ) (hsb : sb ∈ Set.Icc (-δ) δ) (hr : |r| ≤ 3 * δ)
    (hay : dist (circleMap hs.1 (s₀ + sa)) (circleMap hs.1 (s₀ + r)) ≤ |sa - sb|)
    (hby : dist (circleMap hs.1 (s₀ + sb)) (circleMap hs.1 (s₀ + r)) ≤ |sa - sb|) :
    circleMap hs.1 (s₀ + r) ∈ (fun r => circleMap hs.1 (s₀ + r)) '' Set.Icc (-δ) δ := by
  have hdist (s : ℝ) (hs' : s ∈ Set.Icc (-δ) δ) :
      dist (circleMap hs.1 (s₀ + s)) (circleMap hs.1 (s₀ + r)) = |r - s| := by
    rw [show s₀ + r = (s₀ + s) + (r - s) by ring]
    exact dist_circleMap_add_eq_abs hs (s₀ + s) (r - s)
      (by linarith [abs_le.mpr hs', abs_sub r s, abs_nonneg s, hr, hδL])
  rw [hdist sa hsa, abs_le] at hay; rw [hdist sb hsb, abs_le] at hby
  rcases le_total sa sb with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hay hby
    exact ⟨r, ⟨by linarith [hsa.1], by linarith [hsb.2]⟩, rfl⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hay hby
    exact ⟨r, ⟨by linarith [hsb.1], by linarith [hsa.2]⟩, rfl⟩

/-- Any point closer to an interior edge point `edgePoint d ⟨t, ...⟩` than both endpoints of `d`
lies on `d` itself, at parameter distance `|t - u'| * W.weight d.edge`. -/
private theorem edgePoint_close_interior_dart {V : Type*} (W : WeightedGraph V) [Finite V]
    {d : W.graph.Dart} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {y : MetricGraph W}
    (hdy_lt : dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) y <
      min (t * W.weight d.edge) ((1 - t) * W.weight d.edge)) :
    ∃ u : unitInterval, y = edgePoint d u ∧
      dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) y = |t - (u : ℝ)| * W.weight d.edge := by
  let ε := min (t * W.weight d.edge) ((1 - t) * W.weight d.edge)
  have hw := W.dart_weight_pos d
  have hfar (u : V) : ε ≤ dist (edgePoint d ⟨t, ht0.le, ht1.le⟩ : MetricGraph W) (vertex u) := by
    rw [_root_.dist_comm, dist_vertex_edgePoint]
    exact le_min (by linarith [min_le_left (t * W.weight d.edge) ((1 - t) * W.weight d.edge),
        vertexDist_nonneg W.weight_nonneg (G := W.graph) u d.fst])
      (by linarith [min_le_right (t * W.weight d.edge) ((1 - t) * W.weight d.edge),
        vertexDist_nonneg W.weight_nonneg (G := W.graph) u d.snd])
  revert hdy_lt
  induction y using MetricGraph.ind with
  | vertex u => exact fun h => absurd h (hfar u).not_gt
  | edgePoint d' t' ht'0 ht'1 =>
    intro hlt
    have hde : d'.edge = d.edge := by
      by_contra hne
      rw [dist_edgePoint_eq_min_of_edge_ne (Ne.symm hne)] at hlt
      have hw' := (W.dart_weight_pos d').le
      linarith [le_min (add_le_add (hfar d'.fst) (mul_nonneg ht'0.le hw'))
        (add_le_add (hfar d'.snd) (mul_nonneg (sub_nonneg.mpr ht'1.le) hw'))]
    obtain ⟨u, _, _, hu⟩ := exists_edgePoint_reorient hde t' ht'0 ht'1
    rw [hu] at hlt ⊢
    refine ⟨u, rfl, ?_⟩
    have hdm := dist_edgePoint_eq_min_same d ⟨t, ht0.le, ht1.le⟩ u
    have hge : ε ≤ min (dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d.fst) +
        (u : ℝ) * W.weight d.edge) (dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d.snd) +
        (1 - (u : ℝ)) * W.weight d.edge) :=
      le_min (by linarith [hfar d.fst, mul_nonneg u.2.1 hw.le])
        (by linarith [hfar d.snd, mul_nonneg (sub_nonneg.mpr u.2.2) hw.le])
    rw [hdm] at hlt ⊢
    exact min_eq_left (((min_lt_iff.mp hlt).resolve_right hge.not_gt).le.trans hge)

/-- Contradicts placing `f ![c(s₀ + sa), c(s₀ + sb)]` on a third dart `d` incident to vertex `v`
with `sa < 0 < sb` (`r_y ≤ |sa|, |sb|`). -/
private theorem third_dart_contra {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {s₀ : ℝ} {v : V} {d₁ d₂ d : W.graph.Dart}
    (hd₁_fst : d₁.fst = v) (hd₂_fst : d₂.fst = v) (hd_fst : d.fst = v)
    (hd₁₂ : d₁.edge ≠ d₂.edge) (hd₁_ne : d₁.edge ≠ d.edge) (hd₂_ne : d₂.edge ≠ d.edge)
    {wmin vmin δ r_y sa sb : ℝ}
    (hwmin : ∀ d' : W.graph.Dart, wmin ≤ W.weight d'.edge)
    (hvmin : ∀ u w : V, u ≠ w → vmin ≤ dist (vertex u : MetricGraph W) (vertex w))
    (hδ16 : 16 * δ ≤ wmin) (hδv : 16 * δ ≤ vmin)
    (hfull₁ : ∀ r ∈ Set.Icc 0 δ, circleMap hs.1 (s₀ - r) = rayPt W d₁ r)
    (hfull₂ : ∀ r ∈ Set.Icc 0 δ, circleMap hs.1 (s₀ + r) = rayPt W d₂ r)
    {g : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hg_sp : (Mechanism.deterministic g).IsStrategyProof)
    (hg_unam : ∀ p ∈ Set.range (circleMap hs.1), g (fun _ => p) = p)
    (hry_pos : 0 < r_y) (hsa : sa ∈ Set.Icc (-δ) 0) (hsb : sb ∈ Set.Icc 0 δ)
    (hry_a : r_y ≤ -sa) (hry_b : r_y ≤ sb)
    (hgy : g ![circleMap hs.1 (s₀ + sa), circleMap hs.1 (s₀ + sb)] = rayPt W d r_y) : False := by
  have hry_le : r_y ≤ δ := by linarith [hsa.1]
  have hr'_def : (3 / 4 * r_y : ℝ) ≤ δ := by linarith
  have ha_eq : circleMap hs.1 (s₀ + sa) = rayPt W d₁ (-sa) := by
    rw [show s₀ + sa = s₀ - (-sa) by ring]
    exact hfull₁ (-sa) ⟨by linarith [hsa.2], by linarith [hsa.1]⟩
  have hb_eq : circleMap hs.1 (s₀ + sb) = rayPt W d₂ sb := hfull₂ sb hsb
  have ha'_eq : circleMap hs.1 (s₀ - 3 / 4 * r_y) = rayPt W d₁ (3 / 4 * r_y) :=
    hfull₁ (3 / 4 * r_y) ⟨by positivity, by linarith⟩
  have hb'_eq : circleMap hs.1 (s₀ + 3 / 4 * r_y) = rayPt W d₂ (3 / 4 * r_y) :=
    hfull₂ (3 / 4 * r_y) ⟨by positivity, by linarith⟩
  have hy_eq : g ![rayPt W d₁ (-sa), rayPt W d₂ sb] = rayPt W d r_y := by
    rwa [← ha_eq, ← hb_eq]
  have hb1 := half_step_third_dart_bound W hd₁_fst hd₂_fst hd_fst hd₁₂ hd₂_ne hwmin hvmin
    hδ16 hδv hry_pos hry_le (by linarith [hsa.1]) hry_a hsb.2 hry_b hg_sp
    (by rw [pair_const, ← hb'_eq]; exact hg_unam _ ⟨_, rfl⟩) hy_eq
  have hb2 := half_step_third_dart_bound W hd₂_fst hd₁_fst hd_fst hd₁₂.symm hd₁_ne hwmin hvmin
    hδ16 hδv hry_pos hry_le hsb.2 hry_b (by linarith [hsa.1]) hry_a (swap_isStrategyProof hg_sp)
    (by rw [pair_const, ← ha'_eq]; exact swap_unam hg_unam _ ⟨_, rfl⟩) hy_eq
  have h12 : dist (rayPt W d₁ (3 / 4 * r_y)) (rayPt W d₂ (3 / 4 * r_y)) = 3 / 2 * r_y := by
    rw [dist_rayPt_of_edge_ne W (hd₁_fst.trans hd₂_fst.symm) hd₁₂ (by positivity)
      (by linarith [hδ16.trans (hwmin d₁)]) (by positivity) (by linarith [hδ16.trans (hwmin d₂)])]
    ring
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb2
  rw [_root_.dist_comm (rayPt W d₂ (3 / 4 * r_y))] at hb2
  have htri := dist_triangle (rayPt W d₁ (3 / 4 * r_y))
    (g ![rayPt W d₁ (3 / 4 * r_y), rayPt W d₂ (3 / 4 * r_y)]) (rayPt W d₂ (3 / 4 * r_y))
  linarith

/-- Local interval invariance near a cycle vertex `circleMap hs.1 s₀ = vertex v`: reports within
`δ` of `s₀` stay in the arc `(fun r => circleMap hs.1 (s₀ + r)) '' Set.Icc (-δ) δ`. -/
private theorem local_invariance_vertex {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p)
    {s₀ δ₁ : ℝ} {v : V} {d₁ d₂ : W.graph.Dart}
    (hd₁_fst : d₁.fst = v) (hd₂_fst : d₂.fst = v) (hd₁₂ : d₁.edge ≠ d₂.edge)
    (hs₀_v : circleMap hs.1 s₀ = vertex v) (hδ₁ : 0 < δ₁)
    (hmap : ∀ r ∈ Set.Ioc 0 δ₁, r < W.weight d₁.edge ∧ r < W.weight d₂.edge ∧
      ∃ (h10 : 0 ≤ r / W.weight d₁.edge) (h11 : r / W.weight d₁.edge ≤ 1)
        (h20 : 0 ≤ r / W.weight d₂.edge) (h21 : r / W.weight d₂.edge ≤ 1),
        circleMap hs.1 (s₀ - r) = edgePoint d₁ ⟨r / W.weight d₁.edge, h10, h11⟩ ∧
        circleMap hs.1 (s₀ + r) = edgePoint d₂ ⟨r / W.weight d₂.edge, h20, h21⟩) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ walkLength W.weight c / 16 ∧
      ∀ sa ∈ Set.Icc (-δ) δ, ∀ sb ∈ Set.Icc (-δ) δ,
        f ![circleMap hs.1 (s₀ + sa), circleMap hs.1 (s₀ + sb)] ∈
          (fun r => circleMap hs.1 (s₀ + r)) '' Set.Icc (-δ) δ := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  obtain ⟨wmin, hwmin_pos, hwmin⟩ := exists_min_dart_weight (c.firstDart hs.1.not_nil)
  obtain ⟨vmin, hvmin_pos, hvmin⟩ := exists_pos_le_dist_vertex (W := W)
  let δ := min (L / 16) (min (δ₁ / 4) (min (wmin / 16) (vmin / 16)))
  have hδ_pos : 0 < δ := by positivity
  have hδL : δ ≤ L / 16 := min_le_left _ _
  have hδ_r := min_le_right (L / 16) (min (δ₁ / 4) (min (wmin / 16) (vmin / 16)))
  have hδ16 : 16 * δ ≤ wmin := by
    linarith [(hδ_r.trans (min_le_right _ _)).trans (min_le_left _ _)]
  have hδv : 16 * δ ≤ vmin := by
    linarith [(hδ_r.trans (min_le_right _ _)).trans (min_le_right _ _)]
  have hfull := circleMap_eq_edgePoint_of_vertex hs.1 hδ₁ hmap
  have mkRay (d' : W.graph.Dart) (σ : ℝ) (h : ∀ t : unitInterval,
      circleMap hs.1 (s₀ + σ * ((t : ℝ) * W.weight d'.edge)) = edgePoint d' t)
      {r : ℝ} (hr : r ∈ Set.Icc 0 (3 * δ)) :
      circleMap hs.1 (s₀ + σ * r) = rayPt W d' r := by
    have hw := W.dart_weight_pos d'
    have h1 : r / W.weight d'.edge ≤ 1 := (div_le_one hw).mpr (by linarith [hwmin d', hr.2])
    simpa only [div_mul_cancel₀ _ hw.ne', ← rayPt_eq_edgePoint W d' (div_nonneg hr.1 hw.le) h1]
      using h ⟨r / W.weight d'.edge, div_nonneg hr.1 hw.le, h1⟩
  have hr1 : ∀ r ∈ Set.Icc 0 (3 * δ), circleMap hs.1 (s₀ - r) = rayPt W d₁ r := fun r hr => by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using mkRay d₁ (-1)
      (fun t => by simpa only [neg_one_mul, ← sub_eq_add_neg] using hfull.1 t) hr
  have hr2 : ∀ r ∈ Set.Icc 0 (3 * δ), circleMap hs.1 (s₀ + r) = rayPt W d₂ r := fun r hr => by
    simpa only [one_mul] using mkRay d₂ 1 (fun t => by simpa only [one_mul] using hfull.2 t) hr
  refine ⟨δ, hδ_pos, hδL, fun sa hsa sb hsb => ?_⟩
  obtain ⟨hda_y, hdb_y, hvy_3⟩ := dist_outcome_le_circle W hs hf_sp hf_unam hδL hsa hsb
  set y := f ![circleMap hs.1 (s₀ + sa), circleMap hs.1 (s₀ + sb)]
  rw [hs₀_v] at hvy_3
  rcases eq_vertex_or_edgePoint_of_dist_vertex_lt (v := v) (p := y)
      (fun u hu => by linarith [hvmin v u hu.symm]) with
    hv_eq | ⟨d, t, hd_fst, ht0, _, hy_eq, hvy_eq⟩
  · exact ⟨0, ⟨by linarith, hδ_pos.le⟩, by simp only [add_zero, hs₀_v, hv_eq]⟩
  let r_y := (t : ℝ) * W.weight d.edge
  have hry_pos : 0 < r_y := mul_pos ht0 (W.dart_weight_pos d)
  have hry_3 : r_y ≤ 3 * δ := hvy_eq.symm.trans_le hvy_3
  have hy_ray : y = rayPt W d r_y := hy_eq.trans (edgePoint_eq_rayPt W d t)
  have on_cycle (r : ℝ) (hr : |r| ≤ 3 * δ) (hcm : y = circleMap hs.1 (s₀ + r)) :
      y ∈ (fun r => circleMap hs.1 (s₀ + r)) '' Set.Icc (-δ) δ := by
    rw [hcm] at hda_y hdb_y ⊢
    exact mem_image_Icc_of_dist_le_circle W hs hδL hsa hsb hr hda_y hdb_y
  by_cases h1 : d.edge = d₁.edge
  · obtain rfl := dart_eq_of_edge_eq_of_fst_eq h1 (hd_fst.trans hd₁_fst.symm)
    exact on_cycle (-r_y) (by rw [abs_neg, abs_of_pos hry_pos]; exact hry_3)
      (by rw [show s₀ + (-r_y) = s₀ - r_y by ring, hr1 r_y ⟨hry_pos.le, hry_3⟩, hy_ray])
  · by_cases h2 : d.edge = d₂.edge
    · obtain rfl := dart_eq_of_edge_eq_of_fst_eq h2 (hd_fst.trans hd₂_fst.symm)
      exact on_cycle r_y (by rw [abs_of_pos hry_pos]; exact hry_3)
        (hy_ray.trans (hr2 r_y ⟨hry_pos.le, hry_3⟩).symm)
    · exfalso
      have hfull1' : ∀ r ∈ Set.Icc 0 δ, circleMap hs.1 (s₀ - r) = rayPt W d₁ r :=
        fun r hr => hr1 r ⟨hr.1, by linarith [hr.2]⟩
      have hfull2' : ∀ r ∈ Set.Icc 0 δ, circleMap hs.1 (s₀ + r) = rayPt W d₂ r :=
        fun r hr => hr2 r ⟨hr.1, by linarith [hr.2]⟩
      have hdist_r (s : ℝ) (hs' : s ∈ Set.Icc (-δ) δ) :
          dist (circleMap hs.1 (s₀ + s)) y = |s| + r_y :=
        hy_ray ▸ dist_third_dart_signed W hs.1 hd₁_fst hd₂_fst hd_fst (Ne.symm h1) (Ne.symm h2)
          hs₀_v hfull1' hfull2' (by linarith [hwmin d₁]) (by linarith [hwmin d₂]) hs'
          hry_pos.le (by linarith [hwmin d])
      rw [hdist_r sa hsa] at hda_y; rw [hdist_r sb hsb] at hdb_y
      rcases le_or_gt 0 sa with hsa0 | hsa0 <;> rcases le_or_gt 0 sb with hsb0 | hsb0
      · rcases abs_cases (sa - sb) with ⟨_, _⟩ | ⟨_, _⟩ <;>
          linarith [abs_of_nonneg hsa0, abs_of_nonneg hsb0]
      · rw [abs_of_nonneg hsa0] at hda_y; rw [abs_of_neg hsb0] at hdb_y
        rw [abs_of_pos (by linarith)] at hda_y hdb_y
        exact third_dart_contra W hs hd₁_fst hd₂_fst hd_fst hd₁₂ (Ne.symm h1) (Ne.symm h2)
          hwmin hvmin hδ16 hδv hfull1' hfull2' (swap_isStrategyProof hf_sp) (swap_unam hf_unam)
          hry_pos ⟨hsb.1, hsb0.le⟩ ⟨hsa0, hsa.2⟩ (by linarith) (by linarith) hy_ray
      · rw [abs_of_neg hsa0] at hda_y; rw [abs_of_nonneg hsb0] at hdb_y
        rw [abs_of_neg (by linarith)] at hda_y hdb_y
        exact third_dart_contra W hs hd₁_fst hd₂_fst hd_fst hd₁₂ (Ne.symm h1) (Ne.symm h2)
          hwmin hvmin hδ16 hδv hfull1' hfull2' hf_sp hf_unam
          hry_pos ⟨hsa.1, hsa0.le⟩ ⟨hsb0, hsb.2⟩ (by linarith) (by linarith) hy_ray
      · rcases abs_cases (sa - sb) with ⟨_, _⟩ | ⟨_, _⟩ <;>
          linarith [abs_of_neg hsa0, abs_of_neg hsb0]

/-- Local interval invariance at an arbitrary cycle parameter `s₀`: reports within some `δ > 0`
(`δ ≤ walkLength W.weight c / 16`) of `s₀` stay in the same arc around `s₀`. -/
private theorem local_invariance_circle {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p)
    (s₀ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ walkLength W.weight c / 16 ∧
      ∀ sa ∈ Set.Icc (-δ) δ, ∀ sb ∈ Set.Icc (-δ) δ,
        f ![circleMap hs.1 (s₀ + sa), circleMap hs.1 (s₀ + sb)] ∈
          (fun r => circleMap hs.1 (s₀ + r)) '' Set.Icc (-δ) δ := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  rcases circleMap_local_dichotomy hs.1 s₀ with
    ⟨d, t, δ₁, _, ht0, ht1, hδ₁, hmap⟩ |
    ⟨v, d₁, d₂, δ₁, _, hd₁_fst, hd₂_fst, hd₁₂, _, _, hs₀_v, hδ₁, hmap⟩
  · let ε₁ := min (t * W.weight d.edge) ((1 - t) * W.weight d.edge)
    have hw := W.dart_weight_pos d
    have hε₁ : 0 < ε₁ := by positivity
    let δ := min (L / 16) (min (δ₁ / 4) (ε₁ / 4))
    have hδL : δ ≤ L / 16 := min_le_left _ _
    have h3δ : 3 * δ ≤ δ₁ := by
      linarith [(min_le_right (L / 16) _).trans (min_le_left (δ₁ / 4) (ε₁ / 4))]
    have h4δ : 4 * δ ≤ ε₁ := by
      linarith [(min_le_right (L / 16) _).trans (min_le_right (δ₁ / 4) (ε₁ / 4))]
    have hcm0 : circleMap hs.1 s₀ = edgePoint d ⟨t, ht0.le, ht1.le⟩ := by
      obtain ⟨_, _, _, _, h⟩ := hmap 0 ⟨by linarith, hδ₁.le⟩
      simpa only [add_zero, zero_div] using h
    refine ⟨δ, by positivity, hδL, fun sa hsa sb hsb => ?_⟩
    obtain ⟨hda_y, hdb_y, hdy_3⟩ := dist_outcome_le_circle W hs hf_sp hf_unam hδL hsa hsb
    obtain ⟨u, hu_eq, hdeq⟩ := edgePoint_close_interior_dart W ht0 ht1
      (by rw [← hcm0]; linarith [show 0 < δ by positivity])
    let r_y := ((u : ℝ) - t) * W.weight d.edge
    have habs_ry : |r_y| ≤ 3 * δ := by
      dsimp only [r_y]; rw [abs_mul, abs_of_pos hw, abs_sub_comm]
      linarith [hcm0 ▸ hdy_3, hdeq]
    have hcm_r : circleMap hs.1 (s₀ + r_y) = edgePoint d u := by
      obtain ⟨_, _, _, _, hcm⟩ := hmap r_y (abs_le.mp (habs_ry.trans h3δ))
      rw [hcm]
      congr 1
      ext
      dsimp only [r_y]
      field_simp [hw.ne']
      ring
    rw [hu_eq, ← hcm_r] at hda_y hdb_y ⊢
    exact mem_image_Icc_of_dist_le_circle W hs hδL hsa hsb habs_ry hda_y hdb_y
  · exact local_invariance_vertex W hs hf_sp hf_unam hd₁_fst hd₂_fst hd₁₂ hs₀_v hδ₁ hmap

/-! ### Local Moulin characterization and orientation dichotomy -/

/-- Around any cycle parameter `s₀`, the mechanism agrees locally with a two-agent Moulin phantom
rule `min (max α₀ u) v` for ordered inputs `u ≤ v` in `[s₀ - δ, s₀ + δ]`. -/
private theorem local_moulin_circle {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p) (s₀ : ℝ) :
    ∃ δ α₀ : ℝ, 0 < δ ∧ δ ≤ walkLength W.weight c / 16 ∧
      α₀ ∈ Set.Icc (s₀ - δ) (s₀ + δ) ∧
      ∀ u v : ℝ, u ∈ Set.Icc (s₀ - δ) (s₀ + δ) → v ∈ Set.Icc (s₀ - δ) (s₀ + δ) → u ≤ v →
        f ![circleMap hs.1 u, circleMap hs.1 v] = circleMap hs.1 (min (max α₀ u) v) := by
  obtain ⟨δ, hδ_pos, hδL, hinv⟩ := local_invariance_circle W hs hf_sp hf_unam s₀
  let φ : Set.Icc (0 : ℝ) (2 * δ) → MetricGraph W := fun t => circleMap hs.1 (s₀ - δ + (t : ℝ))
  have hφ : Isometry φ := isometry_iff_dist_eq.mpr fun t₁ t₂ => by
    have hsub : (s₀ - δ + (t₁ : ℝ)) - (s₀ - δ + (t₂ : ℝ)) = (t₁ : ℝ) - t₂ := by ring
    have habs : |(t₁ : ℝ) - t₂| ≤ 2 * δ :=
      abs_sub_le_iff.mpr ⟨by linarith [t₁.2.2, t₂.2.1], by linarith [t₁.2.1, t₂.2.2]⟩
    rw [Subtype.dist_eq, Real.dist_eq, circleMap_dist_eq_of_le hs
      (by rw [hsub]; linarith [hδL, walkLength_pos_of_not_nil hs.1.not_nil]), hsub]
  have hrange : ∀ x : Fin 2 → MetricGraph W, (∀ i, x i ∈ Set.range φ) → f x ∈ Set.range φ := by
    intro x hx
    obtain ⟨t0, h0⟩ := hx 0; obtain ⟨t1, h1⟩ := hx 1
    have hx_eq : x = ![circleMap hs.1 (s₀ + ((t0 : ℝ) - δ)),
        circleMap hs.1 (s₀ + ((t1 : ℝ) - δ))] := by
      ext i; fin_cases i <;> [exact h0.symm.trans (by dsimp only [φ]; congr 1; ring);
        exact h1.symm.trans (by dsimp only [φ]; congr 1; ring)]
    obtain ⟨r, hr, hreq⟩ := hinv ((t0 : ℝ) - δ) ⟨by linarith [t0.2.1], by linarith [t0.2.2]⟩
      ((t1 : ℝ) - δ) ⟨by linarith [t1.2.1], by linarith [t1.2.2]⟩
    exact ⟨⟨r + δ, by linarith [hr.1], by linarith [hr.2]⟩,
      by dsimp only [φ]; rw [hx_eq, ← hreq]; congr 1; ring⟩
  obtain ⟨E, hE⟩ := moulinScheme_of_isometry (by linarith) φ hφ hf_sp hrange
    fun y ⟨t, ht⟩ => ⟨fun _ => y, fun _ => ⟨t, ht⟩, hf_unam y ⟨_, ht⟩⟩
  refine ⟨δ, s₀ - δ + E.alpha {0}, hδ_pos, hδL,
    ⟨by linarith [(E.mem_Icc {0}).1], by linarith [(E.mem_Icc {0}).2]⟩, fun u v hu hv huv => ?_⟩
  let tu : Set.Icc (0 : ℝ) (2 * δ) := ⟨u - (s₀ - δ), by linarith [hu.1], by linarith [hu.2]⟩
  let tv : Set.Icc (0 : ℝ) (2 * δ) := ⟨v - (s₀ - δ), by linarith [hv.1], by linarith [hv.2]⟩
  have hcm : (fun i => φ (![tu, tv] i)) = ![circleMap hs.1 u, circleMap hs.1 v] := by
    ext i; fin_cases i
    · change circleMap hs.1 (s₀ - δ + (u - (s₀ - δ))) = circleMap hs.1 u; congr 1; ring
    · change circleMap hs.1 (s₀ - δ + (v - (s₀ - δ))) = circleMap hs.1 v; congr 1; ring
  have hm := moulinScheme_finTwo_eq E ![tu, tv]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hm
  rw [max_eq_right (show (tu : ℝ) ≤ tv by dsimp only [tu, tv]; linarith),
    min_eq_right (le_max_right (E.alpha {1}) (tv : ℝ))] at hm
  rw [← hcm, hE ![tu, tv]]
  dsimp only [φ]
  rw [hm]
  dsimp only [tu, tv]
  rw [add_min, add_max, show s₀ - δ + (u - (s₀ - δ)) = u by ring,
    show s₀ - δ + (v - (s₀ - δ)) = v by ring]

/-- Global orientation dichotomy for small steps: there exists `δ₀ > 0` such that for all `u` and
`0 ≤ r ≤ δ₀`, `f ![circleMap u, circleMap (u + r)]` uniformly picks either `u` or `u + r`. -/
private theorem orientation_dichotomy_circle {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ((∀ u r : ℝ, 0 ≤ r → r ≤ δ₀ →
          f ![circleMap hs.1 u, circleMap hs.1 (u + r)] = circleMap hs.1 u) ∨
       (∀ u r : ℝ, 0 ≤ r → r ≤ δ₀ →
          f ![circleMap hs.1 u, circleMap hs.1 (u + r)] = circleMap hs.1 (u + r))) := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  let loc (g : ℝ → ℝ → Prop) : Set ℝ :=
    { s | ∃ η > 0, ∀ u v : ℝ, s - η < u → u ≤ v → v < s + η → g u v }
  let gL (u v : ℝ) : Prop := f ![circleMap hs.1 u, circleMap hs.1 v] = circleMap hs.1 u
  let gR (u v : ℝ) : Prop := f ![circleMap hs.1 u, circleMap hs.1 v] = circleMap hs.1 v
  have hopen (g : ℝ → ℝ → Prop) : IsOpen (loc g) := Metric.isOpen_iff.mpr fun s ⟨η, hη, hg⟩ =>
    ⟨η / 2, by linarith, fun t ht => ⟨η / 2, by linarith, fun u v hu huv hv => by
      rw [Metric.mem_ball, Real.dist_eq] at ht
      exact hg u v (by linarith [(abs_lt.mp ht).1]) huv (by linarith [(abs_lt.mp ht).2])⟩⟩
  have hIoo_sub (g : ℝ → ℝ → Prop) {a b : ℝ} (h : ∀ u v, a < u → u ≤ v → v < b → g u v) :
      Set.Ioo a b ⊆ loc g := fun t ⟨ht1, ht2⟩ =>
    ⟨min (t - a) (b - t), lt_min (sub_pos.mpr ht1) (sub_pos.mpr ht2), fun u v hu huv hv =>
      h u v (by linarith [min_le_left (t - a) (b - t)]) huv
        (by linarith [min_le_right (t - a) (b - t)])⟩
  have hdisj : Disjoint (loc gL) (loc gR) := Set.disjoint_left.mpr fun s ⟨η₁, hη₁, hl⟩
      ⟨η₂, hη₂, hr⟩ => by
    let ε := min (min η₁ η₂ / 2) (L / 4)
    have hε : 0 < ε := by positivity
    have hε1 : ε < η₁ := by linarith [min_le_left (min η₁ η₂ / 2) (L / 4), min_le_left η₁ η₂]
    have hε2 : ε < η₂ := by linarith [min_le_left (min η₁ η₂ / 2) (L / 4), min_le_right η₁ η₂]
    have h1 := hl s (s + ε) (by linarith) (by linarith) (by linarith)
    have h2 := hr s (s + ε) (by linarith) (by linarith) (by linarith)
    have hd := dist_circleMap_add_mul_dir hs (Or.inl rfl) s ε hε.le
      (by linarith [min_le_right (min η₁ η₂ / 2) (L / 4)])
    rw [one_mul, h1.symm.trans h2, _root_.dist_self] at hd; linarith
  have hclass (s : ℝ) : s ∈ loc gL ∨ s ∈ loc gR ∨
      ∃ δ > 0, Set.Ioo (s - δ) s ⊆ loc gR ∧ Set.Ioo s (s + δ) ⊆ loc gL := by
    obtain ⟨δ, α₀, hδ_pos, _, hα, hm⟩ := local_moulin_circle W hs hf_sp hf_unam s
    have hR : Set.Ioo (s - δ) α₀ ⊆ loc gR := hIoo_sub gR fun u v hu huv hv => by
      dsimp only [gR]
      rw [hm u v ⟨hu.le, by linarith [hα.2]⟩ ⟨by linarith, by linarith [hα.2]⟩ huv]
      simp only [max_eq_left (huv.trans hv.le), min_eq_right hv.le]
    have hL' : Set.Ioo α₀ (s + δ) ⊆ loc gL := hIoo_sub gL fun u v hu huv hv => by
      dsimp only [gL]
      rw [hm u v ⟨by linarith [hα.1], by linarith⟩ ⟨by linarith [hα.1], hv.le⟩ huv]
      simp only [max_eq_right hu.le, min_eq_left huv]
    rcases lt_trichotomy α₀ s with hlt | rfl | hgt
    · exact Or.inl (hL' ⟨hlt, by linarith⟩)
    · exact Or.inr (Or.inr ⟨δ, hδ_pos, hR, hL'⟩)
    · exact Or.inr (Or.inl (hR ⟨by linarith, hgt⟩))
  have hper_r : ∀ s, s ∈ loc gR → s + L ∈ loc gR := fun s ⟨η, hη, hr⟩ =>
    ⟨η, hη, fun u v hu huv hv => by
      dsimp only [gR]
      rw [← sub_add_cancel u L, ← sub_add_cancel v L, circleMap_periodic hs.1,
        circleMap_periodic hs.1]
      exact hr (u - L) (v - L) (by linarith) (sub_le_sub_right huv L) (by linarith)⟩
  rcases disjoint_open_periodic_dichotomy hL (hopen gL) (hopen gR) hdisj hper_r hclass with h | h
  · obtain ⟨δ₀, hδ₀, hs₀⟩ := uniform_step_of_periodic_local hL gL (fun s _ => h (Set.mem_univ s))
      fun u v m h => by simpa only [gL, L, circleMap_add_int_mul hs.1] using h
    exact ⟨δ₀, hδ₀, Or.inl hs₀⟩
  · obtain ⟨δ₀, hδ₀, hs₀⟩ := uniform_step_of_periodic_local hL gR (fun s _ => h (Set.mem_univ s))
      fun u v m h => by simpa only [gR, L, circleMap_add_int_mul hs.1] using h
    exact ⟨δ₀, hδ₀, Or.inr hs₀⟩

/-! ### Extending local dictatorship to a half-cycle -/

/-- Boundary continuity of cyclic dictatorship: if player `0` dictates for all offsets in
`[0, R)` along direction `σ = ±1`, then player `0` also dictates at offset `R`. -/
private theorem cycle_dictator_at_limit {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    {σ R : ℝ} (hσ : σ = 1 ∨ σ = -1) (hR_pos : 0 < R) (hR_le : R ≤ walkLength W.weight c / 2)
    (h_lt : ∀ r' ∈ Set.Ico 0 R, ∀ s : ℝ,
      f ![circleMap hs.1 s, circleMap hs.1 (s + σ * r')] = circleMap hs.1 s) (s : ℝ) :
    f ![circleMap hs.1 s, circleMap hs.1 (s + σ * R)] = circleMap hs.1 s := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  let d := min (ε / 2) (R / 2)
  have hd : 0 < d := by positivity
  let a' := circleMap hs.1 (s + σ * d)
  have hfa' : f ![a', circleMap hs.1 (s + σ * R)] = a' := by
    have heq : (s + σ * d) + σ * (R - d) = s + σ * R := by ring
    exact heq ▸ h_lt (R - d) ⟨by linarith [min_le_right (ε / 2) (R / 2)], by linarith⟩ (s + σ * d)
  have hsp := sp_pair_left hf_sp (circleMap hs.1 s) (circleMap hs.1 (s + σ * R)) a'
  rw [hfa'] at hsp
  have hdaa' : dist (circleMap hs.1 s) a' = d :=
    dist_circleMap_add_mul_dir hs hσ s d hd.le (by linarith [min_le_right (ε / 2) (R / 2)])
  rw [_root_.dist_comm]
  linarith [hsp, hdaa', min_le_left (ε / 2) (R / 2)]

/-- A small cycle shift `y₀ = circleMap (s + ρ)` (`|ρ| ≤ 2 * η`) satisfying both the upper bound
against `b = circleMap (s + σ * (R + η'))` and the lower bound against `b₀ = circleMap (s + σ * R)`
must equal `circleMap s`. -/
private theorem eq_of_circle_shift_bounds {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {σ R η η' s ρ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hR_le : R ≤ walkLength W.weight c / 2)
    (hη_R : η ≤ R / 4) (hη_L : 8 * η ≤ walkLength W.weight c / 2 - R) (hη' : η' ∈ Set.Icc 0 η)
    (hρ : |ρ| ≤ 2 * η) {y₀ : MetricGraph W} (hy_cm : y₀ = circleMap hs.1 (s + ρ))
    (hb : dist (circleMap hs.1 (s + σ * (R + η'))) y₀ ≤ R + η')
    (hb₀ : R ≤ dist (circleMap hs.1 (s + σ * R)) y₀) : y₀ = circleMap hs.1 s := by
  have hσ_abs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ_sq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hnegσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> [right; left] <;> norm_num
  have hσρ : |σ * ρ| ≤ 2 * η := by rw [abs_mul, hσ_abs, one_mul]; exact hρ
  have hshift (X : ℝ) : s + ρ = (s + σ * X) + (-σ) * (X - σ * ρ) := by
    rcases hσ with rfl | rfl <;> ring
  rcases lt_trichotomy (σ * ρ) 0 with hneg | hzero | hpos
  · rw [hy_cm, hshift (R + η'), dist_circleMap_add_mul_dir hs hnegσ _ _
      (by linarith [hη'.1, hη'.2]) (by linarith [(abs_le.mp hσρ).1, hη'.2, hη_L])] at hb
    linarith
  · have hρ0 : ρ = 0 := by
      have h := congrArg (σ * ·) hzero; rwa [← mul_assoc, hσ_sq, one_mul, mul_zero] at h
    simpa only [hρ0, add_zero] using hy_cm
  · rw [hy_cm, hshift R, dist_circleMap_add_mul_dir hs hnegσ _ _
      (by linarith [(abs_le.mp hσρ).2]) (by linarith)] at hb₀
    linarith

/-- Near a cycle vertex `circleMap s_v = vertex v`, any interior point `edgePoint d' t'` with
`d'.fst = v` either lands on one of the two incident cycle darts (`s_v ± r_y`) or lies strictly
farther from a nearby cycle point `b = circleMap s_b` than `v` does. -/
private theorem edgePoint_at_cycle_vertex_cases {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {s_v s_b : ℝ} {v : V} (hv_cm : circleMap hs.1 s_v = vertex v)
    {d' : W.graph.Dart} {t' : unitInterval} (hd'_fst : d'.fst = v)
    (ht'0 : 0 < (t' : ℝ)) (ht'1 : (t' : ℝ) < 1)
    (hsum : 2 * dist (vertex v : MetricGraph W) (circleMap hs.1 s_b) +
      (t' : ℝ) * W.weight d'.edge < walkLength W.weight c) :
    (∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧
      (∀ u : unitInterval,
        circleMap hs.1 (s_v + τ * ((u : ℝ) * W.weight d'.edge)) = edgePoint d' u)) ∨
    dist (vertex v : MetricGraph W) (circleMap hs.1 s_b) <
      dist (circleMap hs.1 s_b) (edgePoint d' t') := by
  rcases circleMap_local_dichotomy hs.1 s_v with
    ⟨d_x, t_x, _, _, ht_x0, ht_x1, hδ_x, hmap_x⟩ |
    ⟨v', d₁, d₂, δ₁, hv'_sup, hd₁_fst, hd₂_fst, hd₁₂, hd₁_mem, hd₂_mem, hs_v', hδ₁, hmap_x⟩
  · exfalso
    obtain ⟨_, _, _, _, hcm⟩ := hmap_x 0 ⟨by linarith, hδ_x.le⟩
    simp only [add_zero, zero_div] at hcm
    have heq := hcm.symm.trans hv_cm
    rw [edgePoint_eq_vertex_iff] at heq
    rcases heq with ⟨h, _⟩ | ⟨h, _⟩
    · have : t_x = 0 := congrArg Subtype.val h; linarith
    · have : t_x = 1 := congrArg Subtype.val h; linarith
  · obtain rfl : v' = v := vertex_inj.mp (hs_v'.symm.trans hv_cm)
    have hfull := circleMap_eq_edgePoint_of_vertex hs.1 hδ₁ hmap_x
    by_cases h1 : d'.edge = d₁.edge
    · obtain rfl := dart_eq_of_edge_eq_of_fst_eq h1 (hd'_fst.trans hd₁_fst.symm)
      exact Or.inl ⟨-1, Or.inr rfl, fun u => by
        rw [neg_one_mul, ← sub_eq_add_neg]; exact hfull.1 u⟩
    · by_cases h2 : d'.edge = d₂.edge
      · obtain rfl := dart_eq_of_edge_eq_of_fst_eq h2 (hd'_fst.trans hd₂_fst.symm)
        exact Or.inl ⟨1, Or.inl rfl, fun u => by rw [one_mul]; exact hfull.2 u⟩
      · right
        have hnot : d'.edge ∉ c.edges := fun hm =>
          (hs.1.edge_eq_or_eq_of_fst_eq hd₁_fst hd₂_fst hd'_fst hd₁₂ hd₁_mem hd₂_mem hm).elim h1 h2
        exact hs.dist_circleMap_lt_dist_edgePoint hv'_sup hd'_fst hnot t' ht'0
          (mul_lt_of_lt_one_left (W.dart_weight_pos d') ht'1) hsum

/-- When two interior points `edgePoint d t` and `edgePoint d' t'` on distinct edges are closer
than every distinct pair of vertices (`η' < vmin`), they can be re-oriented as rays emerging from
a shared endpoint `v` of `d` whose combined offsets are at most `η'`. -/
private theorem exists_shared_vertex_of_dist_edgePoint_le {V : Type*} (W : WeightedGraph V)
    [Finite V] {d d' : W.graph.Dart} (hde : d.edge ≠ d'.edge) {t t' : unitInterval}
    (ht'0 : 0 < (t' : ℝ)) (ht'1 : (t' : ℝ) < 1)
    {vmin η' : ℝ} (hvmin : ∀ u w : V, u ≠ w → vmin ≤ dist (vertex u : MetricGraph W) (vertex w))
    (hη_v : η' < vmin) (hd_le : dist (edgePoint d t) (edgePoint d' t') ≤ η') :
    ∃ (isFst : Bool) (d₀ d'' : W.graph.Dart) (t₀ t'' : unitInterval),
      d₀ = (if isFst then d else d.symm) ∧
      t₀ = (if isFst then t else unitInterval.symm t) ∧
      d''.fst = d₀.fst ∧ d''.edge = d'.edge ∧
      0 < (t'' : ℝ) ∧ (t'' : ℝ) < 1 ∧ edgePoint d'' t'' = edgePoint d' t' ∧
      (t₀ : ℝ) * W.weight d₀.edge + (t'' : ℝ) * W.weight d''.edge ≤ η' := by
  rw [dist_edgePoint_edgePoint_of_edge_ne hde, min_le_iff, min_le_iff, min_le_iff] at hd_le
  have hwd' := (W.dart_weight_pos d').le
  have hmatch {x x' : V} {p q : ℝ} (_ : 0 ≤ p) (_ : 0 ≤ q)
      (h : p + W.graph.vertexDist W.weight x x' + q ≤ η') : x' = x ∧ p + q ≤ η' := by
    obtain rfl : x = x' := by
      by_contra hne; have hv := hvmin x x' hne; rw [dist_vertex] at hv; linarith
    rw [vertexDist_self W.weight_nonneg, add_zero] at h; exact ⟨rfl, h⟩
  obtain ⟨isFst, hdis⟩ : ∃ isFst : Bool,
      ((if isFst then t else unitInterval.symm t : unitInterval) : ℝ) *
        W.weight (if isFst then d else d.symm).edge +
        W.graph.vertexDist W.weight (if isFst then d else d.symm).fst d'.fst +
        (t' : ℝ) * W.weight d'.edge ≤ η' ∨
      ((if isFst then t else unitInterval.symm t : unitInterval) : ℝ) *
        W.weight (if isFst then d else d.symm).edge +
        W.graph.vertexDist W.weight (if isFst then d else d.symm).fst d'.snd +
        (1 - (t' : ℝ)) * W.weight d'.edge ≤ η' :=
    hd_le.elim (fun h => ⟨true, h⟩) fun h => ⟨false, by
      simpa only [Bool.false_eq_true, ↓reduceIte, unitInterval.coe_symm_eq, Dart.edge_symm,
        show d.symm.fst = d.snd from rfl] using h⟩
  let d₀ := if isFst then d else d.symm
  let t₀ := if isFst then t else unitInterval.symm t
  have h0 : 0 ≤ (t₀ : ℝ) * W.weight d₀.edge := mul_nonneg t₀.2.1 (W.dart_weight_pos d₀).le
  rcases hdis with h | h
  · obtain ⟨hfst, hsum⟩ := hmatch h0 (mul_nonneg ht'0.le hwd') h
    exact ⟨isFst, d₀, d', t₀, t', rfl, rfl, hfst, rfl, ht'0, ht'1, rfl, hsum⟩
  · obtain ⟨hfst, hsum⟩ := hmatch h0 (mul_nonneg (sub_nonneg.mpr ht'1.le) hwd') h
    exact ⟨isFst, d₀, d'.symm, t₀, unitInterval.symm t', rfl, rfl, hfst, Dart.edge_symm d',
      sub_pos.mpr ht'1, sub_lt_self 1 ht'0, edgePoint_symm d' t',
      by simpa only [unitInterval.coe_symm_eq, Dart.edge_symm] using hsum⟩

/-! ### Extension steps along vertices and edge interiors -/

/-- Core extension step of `extend_dir_half` when `s` sits on a cycle vertex `vertex v`. -/
private theorem extend_dir_step_vertex {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {σ R η η' s vmin : ℝ} {v : V} {y : MetricGraph W}
    (hσ : σ = 1 ∨ σ = -1) (hR_le : R ≤ walkLength W.weight c / 2)
    (hη_pos : 0 < η) (hη_R : η ≤ R / 4) (hη_L : 8 * η ≤ walkLength W.weight c / 2 - R)
    (hη_v : 8 * η ≤ vmin) (hη' : η' ∈ Set.Icc 0 η)
    (hvmin : ∀ u w : V, u ≠ w → vmin ≤ dist (vertex u : MetricGraph W) (vertex w))
    (hs_v : circleMap hs.1 s = vertex v)
    (hday : dist (circleMap hs.1 s) y ≤ η')
    (hdby : dist (circleMap hs.1 (s + σ * (R + η'))) y ≤ R + η')
    (hdb0y : R ≤ dist (circleMap hs.1 (s + σ * R)) y) :
    y = circleMap hs.1 s := by
  have hy_close : dist (vertex v : MetricGraph W) y ≤ η := hs_v ▸ hday.trans hη'.2
  have hy_lt (u : V) (hu : u ≠ v) :
      dist (vertex v : MetricGraph W) y < dist (vertex v : MetricGraph W) (vertex u) := by
    linarith [hvmin v u hu.symm]
  rcases eq_vertex_or_edgePoint_of_dist_vertex_lt hy_lt with
    hv_eq | ⟨d', t', hd'_fst, ht'0, ht'1, hy_eq, hvy_eq⟩
  · exact hv_eq.trans hs_v.symm
  exfalso
  let r_y := (t' : ℝ) * W.weight d'.edge
  have hry_pos : 0 < r_y := mul_pos ht'0 (W.dart_weight_pos d')
  have hry_le : r_y ≤ η := hvy_eq.symm.le.trans hy_close
  have hbv : dist (vertex v : MetricGraph W) (circleMap hs.1 (s + σ * (R + η'))) = R + η' := by
    rw [← hs_v]
    exact dist_circleMap_add_mul_dir hs hσ s (R + η') (by linarith [hη'.1]) (by linarith [hη'.2])
  have hsum_lt : 2 * dist (vertex v : MetricGraph W) (circleMap hs.1 (s + σ * (R + η'))) +
      r_y < walkLength W.weight c := by
    rw [hbv]; linarith [hη'.2, hη_L]
  rcases edgePoint_at_cycle_vertex_cases W hs hs_v hd'_fst ht'0 ht'1 hsum_lt with
    ⟨τ, hτ, hfull⟩ | hlt
  · have hτ_abs : |τ| = 1 := by rcases hτ with rfl | rfl <;> norm_num
    have heq := eq_of_circle_shift_bounds W hs hσ hR_le hη_R hη_L hη'
      (ρ := τ * r_y) (by rw [abs_mul, hτ_abs, one_mul, abs_of_pos hry_pos]; linarith)
      (hy_eq.trans (hfull t').symm) hdby hdb0y
    rw [heq, hs_v, _root_.dist_self] at hvy_eq; linarith
  · rw [hbv, ← hy_eq] at hlt; exact hlt.not_ge hdby

/-- Eliminates the off-dart case in `extend_dir_half` when `a` lies inside a cycle dart `d` and
`y = f ![a, b]` lies on a distinct dart `d''` emerging from the same endpoint `v` of `d`. -/
private theorem extend_dir_interior_off_dart {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    {σ R η η' s wmin : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hR_le : R ≤ walkLength W.weight c / 2)
    (hη_pos : 0 < η) (hη_R : η ≤ R / 4) (hη_w : 8 * η ≤ wmin)
    (hη_L : 8 * η ≤ walkLength W.weight c / 2 - R) (hη' : η' ∈ Set.Icc 0 η)
    (hwmin : ∀ d' : W.graph.Dart, wmin ≤ W.weight d'.edge)
    (hR_Icc : ∀ r' ∈ Set.Icc 0 R, ∀ s' : ℝ,
      f ![circleMap hs.1 s', circleMap hs.1 (s' + σ * r')] = circleMap hs.1 s')
    (hvert : ∀ s_v : ℝ, ∀ v : V, circleMap hs.1 s_v = vertex v →
      ∀ r' ∈ Set.Icc 0 η, f ![circleMap hs.1 s_v, circleMap hs.1 (s_v + σ * (R + r'))] =
        circleMap hs.1 s_v)
    {d₀ d'' : W.graph.Dart} {t₀ t'' : unitInterval} (hne : d₀.edge ≠ d''.edge)
    (hfst : d''.fst = d₀.fst) (ht0 : 0 < (t₀ : ℝ)) (ht1 : (t₀ : ℝ) < 1)
    (ht''0 : 0 < (t'' : ℝ)) (ht''1 : (t'' : ℝ) < 1)
    {s_v : ℝ} (hs_v_cm : circleMap hs.1 s_v = vertex d₀.fst)
    (ha_ep : circleMap hs.1 s = edgePoint d₀ t₀)
    (hs_diff : s_v = s + (t₀ : ℝ) * W.weight d₀.edge ∨ s_v = s - (t₀ : ℝ) * W.weight d₀.edge)
    (hy_eq : f ![circleMap hs.1 s, circleMap hs.1 (s + σ * (R + η'))] = edgePoint d'' t'')
    (hdby : dist (circleMap hs.1 (s + σ * (R + η'))) (edgePoint d'' t'') ≤ R + η')
    (hdb0y : R ≤ dist (circleMap hs.1 (s + σ * R)) (edgePoint d'' t''))
    (hoff_sum : (t₀ : ℝ) * W.weight d₀.edge + (t'' : ℝ) * W.weight d''.edge ≤ η') : False := by
  let off_a := (t₀ : ℝ) * W.weight d₀.edge
  let r_y := (t'' : ℝ) * W.weight d''.edge
  let r := R + η'
  let a := circleMap hs.1 s
  let b := circleMap hs.1 (s + σ * r)
  have hpos_a : 0 < off_a := mul_pos ht0 (W.dart_weight_pos d₀)
  have hpos_y : 0 < r_y := mul_pos ht''0 (W.dart_weight_pos d'')
  have hdir : s_v = s + σ * off_a ∨ s = s_v + σ * off_a := by
    rcases hσ with rfl | rfl <;> rcases hs_diff with h | h <;> [left; right; right; left] <;>
      linarith
  rcases hdir with h_fwd | h_bwd
  · have hb_eq : b = circleMap hs.1 (s_v + σ * (r - off_a)) := by
      dsimp only [b]
      congr 1
      rw [h_fwd]
      ring
    have hfb_v : f ![vertex d₀.fst, b] = vertex d₀.fst := by
      rw [← hs_v_cm, hb_eq]
      rcases le_or_gt (r - off_a) R with hle | hgt
      · exact hR_Icc (r - off_a) ⟨by linarith [hη'.1, hη'.2], hle⟩ s_v
      · simpa only [add_sub_cancel] using hvert s_v d₀.fst hs_v_cm (r - off_a - R)
          ⟨by linarith, by dsimp only [r]; linarith [hη'.2]⟩
    have hsp := sp_pair_left hf_sp a b (vertex d₀.fst)
    rw [hfb_v, hy_eq] at hsp
    have hda_v : dist a (vertex d₀.fst : MetricGraph W) = off_a := by
      rw [← hs_v_cm, h_fwd]
      exact dist_circleMap_add_mul_dir hs hσ s off_a hpos_a.le (by linarith [hη'.2])
    have hda_y : dist a (edgePoint d'' t'') = off_a + r_y := by
      change dist (circleMap hs.1 s) _ = off_a + r_y
      rw [ha_ep, edgePoint_eq_rayPt W d₀ t₀, edgePoint_eq_rayPt W d'' t'',
        dist_rayPt_of_edge_ne W hfst.symm hne hpos_a.le
          (by linarith [hη_w.trans (hwmin d₀), hη'.2]) hpos_y.le
          (by linarith [hη_w.trans (hwmin d''), hη'.2])]
    linarith
  · have hbv : dist (vertex d₀.fst : MetricGraph W) b = off_a + r := by
      rw [← hs_v_cm, show b = circleMap hs.1 (s_v + σ * (off_a + r)) by
        dsimp only [b]; rw [h_bwd]; congr 1; ring]
      exact dist_circleMap_add_mul_dir hs hσ s_v (off_a + r) (by linarith [hη'.1])
        (by dsimp only [r]; linarith [hη'.2, hη_L])
    rcases edgePoint_at_cycle_vertex_cases W hs hs_v_cm hfst ht''0 ht''1
        (by rw [hbv]; dsimp only [r]; linarith [hη'.2, hη_L]) with
      ⟨τ, hτ, hfull⟩ | hlt
    · have hσ_ne : σ ≠ τ := by
        intro hστ; subst hστ
        have hw'' := W.dart_weight_pos d''
        have h1 : off_a / W.weight d''.edge ≤ 1 :=
          (div_le_one hw'').mpr (by linarith [hη'.2, hη_w.trans (hwmin d'')])
        have ha_d'' := hfull ⟨off_a / W.weight d''.edge, div_nonneg hpos_a.le hw''.le, h1⟩
        rw [div_mul_cancel₀ _ hw''.ne', ← h_bwd] at ha_d''
        exact hne (edge_eq_of_edgePoint_interior_eq ht0 ht1 (ha_ep.symm.trans ha_d''))
      have hσ_eq : σ = -τ := by
        rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;>
          first | exact absurd rfl hσ_ne | norm_num
      have hτ_abs : |τ| = 1 := by rcases hτ with rfl | rfl <;> norm_num
      have hkill := eq_of_circle_shift_bounds W hs hσ hR_le hη_R hη_L hη' (ρ := τ * (off_a + r_y))
        (by rw [abs_mul, hτ_abs, one_mul, abs_of_pos (by linarith)]; linarith [hη'.2])
        (by rw [← hfull t'', h_bwd, hσ_eq]; congr 1; ring) hdby hdb0y
      exact hne (edge_eq_of_edgePoint_interior_eq ht0 ht1 (ha_ep.symm.trans hkill.symm))
    · rw [hbv] at hlt; linarith

/-- Core extension step of `extend_dir_half` when `s` lies in the interior of a cycle dart `d`. -/
private theorem extend_dir_step_interior {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    {σ R η η' s wmin vmin : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hR_le : R ≤ walkLength W.weight c / 2) (hη_pos : 0 < η)
    (hη_R : η ≤ R / 4) (hη_w : 8 * η ≤ wmin) (hη_v : 8 * η ≤ vmin)
    (hη_L : 8 * η ≤ walkLength W.weight c / 2 - R) (hη' : η' ∈ Set.Icc 0 η)
    (hwmin : ∀ d' : W.graph.Dart, wmin ≤ W.weight d'.edge)
    (hvmin : ∀ u w : V, u ≠ w → vmin ≤ dist (vertex u : MetricGraph W) (vertex w))
    (hR_Icc : ∀ r' ∈ Set.Icc 0 R, ∀ s' : ℝ,
      f ![circleMap hs.1 s', circleMap hs.1 (s' + σ * r')] = circleMap hs.1 s')
    (hvert : ∀ s_v : ℝ, ∀ v : V, circleMap hs.1 s_v = vertex v →
      ∀ r' ∈ Set.Icc 0 η, f ![circleMap hs.1 s_v, circleMap hs.1 (s_v + σ * (R + r'))] =
        circleMap hs.1 s_v)
    {d : W.graph.Dart} {t δ₁ : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hδ₁ : 0 < δ₁)
    (hmap : ∀ r ∈ Set.Icc (-δ₁) δ₁,
      ∃ (h0 : 0 ≤ t + r / W.weight d.edge) (h1 : t + r / W.weight d.edge ≤ 1),
        circleMap hs.1 (s + r) = edgePoint d ⟨t + r / W.weight d.edge, h0, h1⟩)
    (hday : dist (circleMap hs.1 s)
      (f ![circleMap hs.1 s, circleMap hs.1 (s + σ * (R + η'))]) ≤ η')
    (hdby : dist (circleMap hs.1 (s + σ * (R + η')))
      (f ![circleMap hs.1 s, circleMap hs.1 (s + σ * (R + η'))]) ≤ R + η')
    (hdb0y : R ≤ dist (circleMap hs.1 (s + σ * R))
      (f ![circleMap hs.1 s, circleMap hs.1 (s + σ * (R + η'))])) :
    f ![circleMap hs.1 s, circleMap hs.1 (s + σ * (R + η'))] = circleMap hs.1 s := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  have hw := W.dart_weight_pos d
  have hfull := circleMap_eq_edgePoint_of_local hs.1 ⟨ht0, ht1⟩ hδ₁ hmap
  have ha_ep : circleMap hs.1 s = edgePoint d ⟨t, ht0.le, ht1.le⟩ := by
    obtain ⟨_, _, h⟩ := hmap 0 ⟨by linarith, hδ₁.le⟩; simpa only [add_zero, zero_div] using h
  have hfst_cm : circleMap hs.1 (s - t * W.weight d.edge) = vertex d.fst := by
    simpa only [Set.Icc.coe_zero, zero_sub, neg_mul, ← sub_eq_add_neg, edgePoint_zero] using hfull 0
  have hsnd_cm : circleMap hs.1 (s + (1 - t) * W.weight d.edge) = vertex d.snd := by
    simpa only [Set.Icc.coe_one, edgePoint_one] using hfull 1
  set y := f ![circleMap hs.1 s, circleMap hs.1 (s + σ * (R + η'))]
  have hy_orig : f ![circleMap hs.1 s, circleMap hs.1 (s + σ * (R + η'))] = y := rfl
  revert hy_orig hday hdby hdb0y
  induction y using MetricGraph.ind with
  | vertex u =>
    intro hdu hdby_v hdb0y_v _
    rw [ha_ep, _root_.dist_comm] at hdu
    have hnear (w : V) (hwu : w ≠ u) : dist (vertex u : MetricGraph W)
        (edgePoint d ⟨t, ht0.le, ht1.le⟩) < dist (vertex u : MetricGraph W) (vertex w) := by
      linarith [hvmin u w hwu.symm, hη'.2]
    rcases fst_eq_or_snd_eq_of_dist_vertex_edgePoint_lt hnear with rfl | rfl
    · rw [dist_vertex_edgePoint_of_fst_eq rfl (hnear _ d.adj.ne.symm)] at hdu
      exact eq_of_circle_shift_bounds W hs hσ hR_le hη_R hη_L hη' (ρ := -(t * W.weight d.edge))
        (by rw [abs_neg, abs_of_pos (mul_pos ht0 hw)]; linarith [hη'.2])
        (hfst_cm.symm.trans (congrArg (circleMap hs.1) (by ring))) hdby_v hdb0y_v
    · rw [dist_vertex_edgePoint_of_snd_eq rfl (hnear _ d.adj.ne)] at hdu
      exact eq_of_circle_shift_bounds W hs hσ hR_le hη_R hη_L hη'
        (ρ := (1 - t) * W.weight d.edge)
        (by rw [abs_of_pos (mul_pos (sub_pos.mpr ht1) hw)]; linarith [hη'.2])
        hsnd_cm.symm hdby_v hdb0y_v
  | edgePoint d' t' ht'0 ht'1 =>
    intro hdu hdby_ep hdb0y_ep hy_orig
    by_cases hde : d'.edge = d.edge
    · obtain ⟨u', _, _, hu'_eq⟩ := exists_edgePoint_reorient hde t' ht'0 ht'1
      let ρ := ((u' : ℝ) - t) * W.weight d.edge
      have heq_cm : edgePoint d' t' = circleMap hs.1 (s + ρ) := hu'_eq.trans (hfull u').symm
      obtain ⟨k, hk⟩ := exists_eq_add_int_mul_dist hL s (s + ρ)
      have hρk : |ρ + k * L| ≤ η' := by
        have hk_eq : |s - (s + ρ + k * L)| = |ρ + k * L| := by
          rw [show s - (s + ρ + k * L) = -(ρ + k * L) by ring, abs_neg]
        rw [← hk_eq, hk, ← circleMap_dist_eq_circleDist hs s (s + ρ), ← heq_cm]
        exact hdu
      exact eq_of_circle_shift_bounds W hs hσ hR_le hη_R hη_L hη' (ρ := ρ + k * L)
        (by linarith [hη'.2]) (by rw [heq_cm, show s + (ρ + k * L) = (s + ρ) + k * L by ring,
          circleMap_add_int_mul hs.1]) hdby_ep hdb0y_ep
    · exfalso
      obtain ⟨isFst, d₀, d'', t₀, t'', hd₀, ht₀, hfst, hed, ht''0, ht''1, hd''_eq, hsum⟩ :=
        exists_shared_vertex_of_dist_edgePoint_le W (Ne.symm hde)
          (t := ⟨t, ht0.le, ht1.le⟩) (t' := t') ht'0 ht'1 hvmin
          (by linarith [hη'.2]) (ha_ep ▸ hdu)
      obtain ⟨hne₀, ht₀0, ht₀1, s_v, hs_v, ha_ep₀, hs_diff⟩ :
          d₀.edge ≠ d''.edge ∧ 0 < (t₀ : ℝ) ∧ (t₀ : ℝ) < 1 ∧ ∃ s_v,
            circleMap hs.1 s_v = vertex d₀.fst ∧ circleMap hs.1 s = edgePoint d₀ t₀ ∧
            (s_v = s + (t₀ : ℝ) * W.weight d₀.edge ∨ s_v = s - (t₀ : ℝ) * W.weight d₀.edge) := by
        subst hd₀; subst ht₀; cases isFst
        · exact ⟨by simpa only [Bool.false_eq_true, ↓reduceIte, Dart.edge_symm, hed]
              using Ne.symm hde,
            sub_pos.mpr ht1, sub_lt_self 1 ht0, _, hsnd_cm,
            ha_ep.trans (edgePoint_symm d ⟨t, ht0.le, ht1.le⟩).symm,
            Or.inl (by simp only [Bool.false_eq_true, ↓reduceIte, unitInterval.coe_symm_eq,
              Dart.edge_symm])⟩
        · exact ⟨hed ▸ Ne.symm hde, ht0, ht1, _, hfst_cm, ha_ep, Or.inr rfl⟩
      exact extend_dir_interior_off_dart W hs hf_sp hσ hR_le hη_pos hη_R hη_w hη_L hη' hwmin
        hR_Icc hvert hne₀ hfst ht₀0 ht₀1 ht''0 ht''1 hs_v ha_ep₀ hs_diff
        (hy_orig.trans hd''_eq.symm) (hd''_eq ▸ hdby_ep) (hd''_eq ▸ hdb0y_ep) hsum

/-- Supremum extension: if player `0` dictates for all short shifts `0 ≤ r ≤ δ₀` along direction
`σ = ±1`, then player `0` dictates throughout the open half-cycle `0 ≤ r < L / 2`. -/
private theorem extend_dir_half {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p)
    {σ δ₀ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hδ₀ : 0 < δ₀)
    (hloc : ∀ u r : ℝ, 0 ≤ r → r ≤ δ₀ →
      f ![circleMap hs.1 u, circleMap hs.1 (u + σ * r)] = circleMap hs.1 u) :
    ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      f ![circleMap hs.1 u, circleMap hs.1 (u + σ * r)] = circleMap hs.1 u := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  let S : Set ℝ := { r | r ∈ Set.Ico 0 (L / 2) ∧ ∀ r' ∈ Set.Icc 0 r, ∀ s : ℝ,
    f ![circleMap hs.1 s, circleMap hs.1 (s + σ * r')] = circleMap hs.1 s }
  have hS_ne : S.Nonempty := ⟨0, ⟨le_rfl, by positivity⟩, fun r' hr' s => by
    have : r' = 0 := le_antisymm hr'.2 hr'.1
    simpa only [this, mul_zero, add_zero] using hloc s 0 le_rfl hδ₀.le⟩
  have hS_bdd : BddAbove S := ⟨L / 2, fun _ hr => hr.1.2.le⟩
  let R := sSup S
  have hR_pos : 0 < R := (show 0 < min (δ₀ / 2) (L / 4) by positivity).trans_le <|
    le_csSup hS_bdd ⟨⟨by positivity, by linarith [min_le_right (δ₀ / 2) (L / 4)]⟩,
      fun r' hr' s => hloc s r' hr'.1 (hr'.2.trans (by linarith [min_le_left (δ₀ / 2) (L / 4)]))⟩
  have hR_le : R ≤ L / 2 := csSup_le hS_ne fun _ hr => hr.1.2.le
  have hR_lt_holds : ∀ r' ∈ Set.Ico 0 R, ∀ s : ℝ,
      f ![circleMap hs.1 s, circleMap hs.1 (s + σ * r')] = circleMap hs.1 s := fun r' hr' s =>
    let ⟨_, hr₁, hlt⟩ := exists_lt_of_lt_csSup hS_ne hr'.2; hr₁.2 r' ⟨hr'.1, hlt.le⟩ s
  have hR_holds : ∀ s : ℝ,
      f ![circleMap hs.1 s, circleMap hs.1 (s + σ * R)] = circleMap hs.1 s :=
    cycle_dictator_at_limit W hs hf_sp hσ hR_pos hR_le hR_lt_holds
  have hR_Icc : ∀ r' ∈ Set.Icc 0 R, ∀ s : ℝ,
      f ![circleMap hs.1 s, circleMap hs.1 (s + σ * r')] = circleMap hs.1 s := fun r' hr' s =>
    (eq_or_lt_of_le hr'.2).elim (fun h => h ▸ hR_holds s) (fun h => hR_lt_holds r' ⟨hr'.1, h⟩ s)
  by_contra hlt_all
  have hR_lt : R < L / 2 := lt_of_le_of_ne hR_le fun hEq =>
    hlt_all fun u r hr0 hrL => hR_lt_holds r ⟨hr0, hEq ▸ hrL⟩ u
  obtain ⟨wmin, hwmin_pos, hwmin⟩ := exists_min_dart_weight (c.firstDart hs.1.not_nil)
  obtain ⟨vmin, hvmin_pos, hvmin⟩ := exists_pos_le_dist_vertex (W := W)
  let η := min (R / 4) (min (wmin / 8) (min (vmin / 8) ((L / 2 - R) / 8)))
  have hη_pos : 0 < η := by positivity
  have hη1 := min_le_right (R / 4) (min (wmin / 8) (min (vmin / 8) ((L / 2 - R) / 8)))
  have hη_R : η ≤ R / 4 := min_le_left _ _
  have hη_w : 8 * η ≤ wmin := by linarith [hη1.trans (min_le_left _ _)]
  have hη_v : 8 * η ≤ vmin := by linarith [(hη1.trans (min_le_right _ _)).trans (min_le_left _ _)]
  have hη_L : 8 * η ≤ L / 2 - R := by
    linarith [(hη1.trans (min_le_right _ _)).trans (min_le_right _ _)]
  have hbounds (s η' : ℝ) (hη' : η' ∈ Set.Icc 0 η) :
      dist (circleMap hs.1 s) (f ![circleMap hs.1 s, circleMap hs.1 (s + σ * (R + η'))]) ≤ η' ∧
      dist (circleMap hs.1 (s + σ * (R + η')))
        (f ![circleMap hs.1 s, circleMap hs.1 (s + σ * (R + η'))]) ≤ R + η' ∧
      R ≤ dist (circleMap hs.1 (s + σ * R))
        (f ![circleMap hs.1 s, circleMap hs.1 (s + σ * (R + η'))]) := by
    let a := circleMap hs.1 s
    let b := circleMap hs.1 (s + σ * (R + η'))
    let a₁ := circleMap hs.1 (s + σ * η')
    let b₀ := circleMap hs.1 (s + σ * R)
    refine ⟨?_, ?_, ?_⟩
    · have hfa1 : f ![a₁, b] = a₁ := by
        have h : (s + σ * η') + σ * R = s + σ * (R + η') := by ring
        dsimp only [b]
        rw [← h]
        exact hR_holds (s + σ * η')
      have hsp := sp_pair_left hf_sp a b a₁
      rw [hfa1] at hsp
      exact hsp.trans (dist_circleMap_add_mul_dir hs hσ s η' hη'.1 (by linarith [hη'.2])).le
    · have h := sp_pair_right hf_sp a b a
      rw [pair_const, hf_unam a ⟨s, rfl⟩, _root_.dist_comm b a] at h
      exact h.trans (dist_circleMap_add_mul_dir hs hσ s (R + η') (by linarith [hη'.1])
        (by linarith [hη'.2])).le
    · have h := sp_pair_right hf_sp a b₀ b
      rw [hR_holds s, _root_.dist_comm b₀ a,
        dist_circleMap_add_mul_dir hs hσ s R hR_pos.le hR_le] at h
      exact h
  have hvert (s_v : ℝ) (v : V) (hsv : circleMap hs.1 s_v = vertex v) (r' : ℝ)
      (hr' : r' ∈ Set.Icc 0 η) :
      f ![circleMap hs.1 s_v, circleMap hs.1 (s_v + σ * (R + r'))] = circleMap hs.1 s_v := by
    obtain ⟨h1, h2, h3⟩ := hbounds s_v r' hr'
    exact extend_dir_step_vertex W hs hσ hR_le hη_pos hη_R hη_L hη_v hr' hvmin hsv h1 h2 h3
  have hmem : R + η ∈ S := ⟨⟨by linarith, by linarith⟩, fun r' hr' s => by
    rcases le_or_gt r' R with hle | hgt
    · exact hR_Icc r' ⟨hr'.1, hle⟩ s
    · have hη' : r' - R ∈ Set.Icc 0 η := ⟨by linarith, by linarith [hr'.2]⟩
      rw [show r' = R + (r' - R) by ring]
      obtain ⟨h1, h2, h3⟩ := hbounds s (r' - R) hη'
      rcases circleMap_local_dichotomy hs.1 s with
        ⟨d, t, δ₁, _, ht0, ht1, hδ₁, hmap⟩ | ⟨v, _, _, _, _, _, _, _, _, _, hs_v, _, _⟩
      · exact extend_dir_step_interior W hs hf_sp hσ hR_le hη_pos hη_R hη_w hη_v hη_L hη'
          hwmin hvmin hR_Icc hvert ht0 ht1 hδ₁
          (fun r'' hr'' => let ⟨_, _, h0, h1, hcm⟩ := hmap r'' hr''; ⟨h0, h1, hcm⟩) h1 h2 h3
      · exact hvert s v hs_v (r' - R) hη'⟩
  linarith [le_csSup hS_bdd hmem]

/-! ### Concluding the two-agent cycle dictatorship -/

/-- Combines both half-cycle directions (`σ = ±1`) to conclude that agent `0` dictates on all pairs
of points along the shortest cycle `c`. -/
private theorem finTwo_cycleDictator_of_half {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {g : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hg_sp : (Mechanism.deterministic g).IsStrategyProof)
    (hpos : ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      g ![circleMap hs.1 u, circleMap hs.1 (u + r)] = circleMap hs.1 u)
    (hneg : ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      g ![circleMap hs.1 u, circleMap hs.1 (u - r)] = circleMap hs.1 u) :
    ∀ a ∈ Set.range (circleMap hs.1), ∀ b ∈ Set.range (circleMap hs.1), g ![a, b] = a := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  rintro _ ⟨sa, rfl⟩ _ ⟨sb, rfl⟩
  let k : ℤ := ⌈(sb - sa) / L - 1 / 2⌉
  let r := (sb - sa) - k * L
  have hlo : -L / 2 < r := by
    nlinarith [Int.ceil_lt_add_one ((sb - sa) / L - 1 / 2), div_mul_cancel₀ (sb - sa) hL.ne']
  have hhi : r ≤ L / 2 := by
    nlinarith [Int.le_ceil ((sb - sa) / L - 1 / 2), div_mul_cancel₀ (sb - sa) hL.ne']
  have hsb_eq : circleMap hs.1 sb = circleMap hs.1 (sa + r) := by
    rw [show sb = (sa + r) + k * L by dsimp only [r]; ring, circleMap_add_int_mul hs.1]
  rw [hsb_eq]
  rcases lt_or_eq_of_le hhi with hlt | heq
  · rcases le_or_gt 0 r with hr0 | hrn
    · exact hpos sa r hr0 hlt
    · exact (show sa + r = sa - (-r) by ring) ▸ hneg sa (-r) (by linarith) (by linarith)
  · rw [heq]
    simpa only [one_mul] using cycle_dictator_at_limit W hs hg_sp (Or.inl rfl) (by positivity)
      le_rfl (fun r' hr' s => by simpa only [one_mul] using hpos s r' hr'.1 hr'.2) sa

/-- A strategyproof two-agent mechanism on a shortest cycle cannot choose `u` whenever the second
agent moves by `σ * r` (`σ = ±1`, `0 ≤ r < L / 2`) while also choosing `u` when the first agent
moves by `σ * r`. -/
private theorem finTwo_cycleDictator_dir_contra {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {g : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hg_sp : (Mechanism.deterministic g).IsStrategyProof)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h1 : ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      g ![circleMap hs.1 u, circleMap hs.1 (u + σ * r)] = circleMap hs.1 u)
    (h2 : ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      g ![circleMap hs.1 (u + σ * r), circleMap hs.1 u] = circleMap hs.1 u) : False := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  let ε := L / 8
  have hfirst : g ![circleMap hs.1 0, circleMap hs.1 (σ * (L / 2 - ε))] = circleMap hs.1 0 := by
    simpa only [zero_add] using h1 0 (L / 2 - ε) (by dsimp only [ε]; linarith)
      (by dsimp only [ε]; linarith)
  have hsecond : g ![circleMap hs.1 0, circleMap hs.1 (σ * (L / 2 + ε))] =
      circleMap hs.1 (σ * (L / 2 + ε)) := by
    have hper : circleMap hs.1 0 = circleMap hs.1 (σ * (L / 2 + ε) + σ * (L / 2 - ε)) := by
      rcases hσ with rfl | rfl
      · simpa only [zero_add, Int.cast_one, one_mul] using
          (circleMap_add_int_mul hs.1 0 1).symm.trans (by congr 1; ring)
      · simpa only [zero_add, Int.cast_neg, Int.cast_one] using
          (circleMap_add_int_mul hs.1 0 (-1)).symm.trans (by congr 1; ring)
    exact hper ▸ h2 (σ * (L / 2 + ε)) (L / 2 - ε) (by dsimp only [ε]; linarith)
      (by dsimp only [ε]; linarith)
  have hsp := sp_pair_right hg_sp (circleMap hs.1 0)
    (circleMap hs.1 (σ * (L / 2 - ε))) (circleMap hs.1 (σ * (L / 2 + ε)))
  rw [hfirst, hsecond,
    _root_.dist_comm (circleMap hs.1 (σ * (L / 2 - ε))) (circleMap hs.1 0)] at hsp
  have hd1 := dist_circleMap_add_mul_dir hs hσ 0 (L / 2 - ε) (by dsimp only [ε]; linarith)
    (by dsimp only [ε]; linarith)
  have hd2 := dist_circleMap_add_mul_dir hs hσ (σ * (L / 2 - ε)) (2 * ε) (by positivity)
    (by dsimp only [ε]; linarith)
  rw [zero_add] at hd1
  rw [show σ * (L / 2 - ε) + σ * (2 * ε) = σ * (L / 2 + ε) by ring] at hd2
  dsimp only [ε] at hd1 hd2; linarith

/-- Two-agent cycle dictatorship: every strategyproof deterministic mechanism that is unanimous on
a shortest cycle `c` has a dictator `k : Fin 2` on the points of `c`. -/
private theorem finTwo_cycleDictator {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p) :
    ∃ k : Fin 2, ∀ a ∈ Set.range (circleMap hs.1), ∀ b ∈ Set.range (circleMap hs.1),
      f ![a, b] = ![a, b] k := by
  let f_swap : (Fin 2 → MetricGraph W) → MetricGraph W := fun x => f ![x 1, x 0]
  have hsp_s := swap_isStrategyProof hf_sp
  have hunam_s := swap_unam hf_unam
  have flip {g g' : (Fin 2 → MetricGraph W) → MetricGraph W} (hg' : ∀ a b, g' ![a, b] = g ![b, a])
      {δ : ℝ} (h : ∀ u r, 0 ≤ r → r ≤ δ → g ![circleMap hs.1 u, circleMap hs.1 (u + r)] =
        circleMap hs.1 (u + r)) (u r : ℝ) (h1 : 0 ≤ r) (h2 : r ≤ δ) :
      g' ![circleMap hs.1 u, circleMap hs.1 (u + (-1) * r)] = circleMap hs.1 u := by
    rw [hg', show u + (-1) * r = u - r by ring]
    simpa only [sub_add_cancel] using h (u - r) r h1 h2
  have mkDict {g g' : (Fin 2 → MetricGraph W) → MetricGraph W}
      (hg_sp : (Mechanism.deterministic g).IsStrategyProof)
      (hg_unam : ∀ p ∈ Set.range (circleMap hs.1), g (fun _ => p) = p)
      (hgg' : ∀ a b, g ![a, b] = g' ![b, a]) {δa δb : ℝ} (hδa : 0 < δa) (hδb : 0 < δb)
      (hl : ∀ u r, 0 ≤ r → r ≤ δa →
        g ![circleMap hs.1 u, circleMap hs.1 (u + r)] = circleMap hs.1 u)
      (hr : ∀ u r, 0 ≤ r → r ≤ δb →
        g' ![circleMap hs.1 u, circleMap hs.1 (u + r)] = circleMap hs.1 (u + r)) :
      ∀ a ∈ Set.range (circleMap hs.1), ∀ b ∈ Set.range (circleMap hs.1), g ![a, b] = a := by
    refine finTwo_cycleDictator_of_half W hs hg_sp ?_ ?_
    · intro u r h1 h2
      simpa only [one_mul] using extend_dir_half W hs hg_sp hg_unam (Or.inl rfl) hδa
        (fun u' r' h1' h2' => by simpa only [one_mul] using hl u' r' h1' h2') u r h1 h2
    · intro u r h1 h2
      simpa only [neg_one_mul, ← sub_eq_add_neg] using extend_dir_half W hs hg_sp hg_unam
        (Or.inr rfl) hδb (flip hgg' hr) u r h1 h2
  obtain ⟨δ₁, hδ₁, hor1⟩ := orientation_dichotomy_circle W hs hf_sp hf_unam
  obtain ⟨δ₂, hδ₂, hor2⟩ := orientation_dichotomy_circle W hs hsp_s hunam_s
  rcases hor1 with hl1 | hr1 <;> rcases hor2 with hl2 | hr2
  · exact (finTwo_cycleDictator_dir_contra W hs hf_sp (Or.inl rfl)
      (extend_dir_half W hs hf_sp hf_unam (Or.inl rfl) hδ₁
        fun u r h1 h2 => by simpa only [one_mul] using hl1 u r h1 h2)
      (extend_dir_half W hs hsp_s hunam_s (Or.inl rfl) hδ₂
        fun u r h1 h2 => by simpa only [one_mul] using hl2 u r h1 h2)).elim
  · exact ⟨0, mkDict (g' := f_swap) hf_sp hf_unam (fun _ _ => rfl) hδ₁ hδ₂ hl1 hr2⟩
  · exact ⟨1, fun a ha b hb =>
      mkDict (g' := f) hsp_s hunam_s (fun _ _ => rfl) hδ₂ hδ₁ hl2 hr1 b hb a ha⟩
  · exact (finTwo_cycleDictator_dir_contra W hs hf_sp (Or.inr rfl)
      (extend_dir_half W hs hf_sp hf_unam (Or.inr rfl) hδ₂
        (flip (g := f_swap) (fun _ _ => rfl) hr2))
      (fun u r h1 h2 => by
        simpa only [f_swap, Matrix.cons_val_one, Matrix.cons_val_zero] using
          extend_dir_half W hs hsp_s hunam_s (Or.inr rfl) hδ₁
            (flip (g := f) (g' := f_swap) (fun _ _ => rfl) hr1) u r h1 h2)).elim

end Fin2CycleDictator

/-! ### Decisive coalitions and ultrafilter reduction -/

section CycleDictator

/-- A coalition `S` is **decisive** on the shortest cycle `c` if forcing every member of `S` to `a`
and every non-member to `b` always returns `a`. -/
private def IsDecisive {V : Type*} {W : WeightedGraph V} {v₀ : V}
    {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c) {ι : Type*} [DecidableEq ι]
    (f : (ι → MetricGraph W) → MetricGraph W) (S : Finset ι) : Prop :=
  ∀ a ∈ Set.range (circleMap hs.1), ∀ b ∈ Set.range (circleMap hs.1),
    f (fun i => if i ∈ S then a else b) = a

private theorem exists_two_distinct_on_cycle {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c) :
    ∃ p₀ p₁ : MetricGraph W, p₀ ∈ Set.range (circleMap hs.1) ∧
      p₁ ∈ Set.range (circleMap hs.1) ∧ p₀ ≠ p₁ := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  refine ⟨circleMap hs.1 0, circleMap hs.1 (L / 4), ⟨0, rfl⟩, ⟨L / 4, rfl⟩, fun h => ?_⟩
  have hd : dist (circleMap hs.1 0) (circleMap hs.1 (L / 4)) = L / 4 := by
    simpa only [zero_add, one_mul] using
      dist_circleMap_add_mul_dir hs (Or.inl rfl) 0 (L / 4) (by positivity) (by linarith)
  rw [h, _root_.dist_self] at hd; linarith

private theorem exists_ne_on_cycle {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c) (b : MetricGraph W) :
    ∃ c' ∈ Set.range (circleMap hs.1), c' ≠ b := by
  obtain ⟨p₀, p₁, hp₀, hp₁, hp₀₁⟩ := exists_two_distinct_on_cycle W hs
  by_cases he : p₀ = b
  · exact ⟨p₁, hp₁, he ▸ hp₀₁.symm⟩
  · exact ⟨p₀, hp₀, he⟩

private theorem isDecisive_or_compl {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p) (S : Finset ι) :
    IsDecisive hs f S ∨ IsDecisive hs f Sᶜ := by
  let sel : ι → Fin 2 := fun i => if i ∈ S then 0 else 1
  have hg_sp := merge_isStrategyProof hf_sp sel
  have hg_unam : ∀ p ∈ Set.range (circleMap hs.1),
      (fun y : Fin 2 → MetricGraph W => f (fun i => y (sel i))) (fun _ => p) = p :=
    fun p hp => hf_unam p hp
  obtain ⟨k, hk⟩ := finTwo_cycleDictator W hs hg_sp hg_unam
  have hfun (a b : MetricGraph W) :
      (fun i => (![a, b] : Fin 2 → MetricGraph W) (sel i)) =
        fun i => if i ∈ S then a else b := by
    ext i; dsimp only [sel]; split_ifs <;> rfl
  fin_cases k
  · exact Or.inl fun a ha b hb => by
      have h := hk a ha b hb
      dsimp only at h
      rwa [hfun a b] at h
  · refine Or.inr fun a ha b hb => ?_
    have hcm : (fun i => if i ∈ Sᶜ then a else b) = fun i => if i ∈ S then b else a := by
      ext i; by_cases hi : i ∈ S <;> simp [hi]
    have h := hk b hb a ha; dsimp only at h
    rw [hcm]; rwa [hfun b a] at h

private theorem not_isDecisive_disjoint {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {ι : Type*} [Finite ι] [DecidableEq ι] {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof) {S₁ S₂ : Finset ι}
    (hdisj : Disjoint S₁ S₂) (h1 : IsDecisive hs f S₁) (h2 : IsDecisive hs f S₂) : False := by
  let _ := Fintype.ofFinite ι
  obtain ⟨p₀, p₁, hp₀, hp₁, hp₀₁⟩ := exists_two_distinct_on_cycle W hs
  let x := fun i => if i ∈ S₂ then p₁ else p₀
  have hfun : (fun i => if i ∈ (S₁ ∪ S₂)ᶜ then p₁ else x i) =
      fun i => if i ∈ S₁ then p₀ else p₁ := by
    ext i
    by_cases hi1 : i ∈ S₁
    · simp [x, hi1, Finset.disjoint_left.mp hdisj hi1]
    · by_cases hi2 : i ∈ S₂ <;> simp [x, hi1, hi2]
  have hcoal := coalition_sp hf_sp (S₁ ∪ S₂)ᶜ p₀ p₁ x fun i hi => by
    simp only [Finset.mem_compl, Finset.mem_union, not_or] at hi; simp [x, hi.2]
  rw [hfun, h2 p₁ hp₁ p₀ hp₀, h1 p₀ hp₀ p₁ hp₁, _root_.dist_self] at hcoal
  exact hp₀₁ (dist_eq_zero.mp (le_antisymm hcoal dist_nonneg))

private theorem isDecisive_mono {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {ι : Type*} [Finite ι] [DecidableEq ι] {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p)
    {A B : Finset ι} (hAB : A ⊆ B) (hA : IsDecisive hs f A) : IsDecisive hs f B :=
  let _ := Fintype.ofFinite ι
  (isDecisive_or_compl W hs hf_sp hf_unam B).resolve_right fun hBc =>
    not_isDecisive_disjoint W hs hf_sp
      (Finset.disjoint_left.mpr fun _ hi hc => (Finset.mem_compl.mp hc) (hAB hi)) hA hBc

private theorem isDecisive_inter {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {ι : Type*} [Finite ι] [DecidableEq ι] {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p)
    {S₁ S₂ : Finset ι} (h1 : IsDecisive hs f S₁) (h2 : IsDecisive hs f S₂) :
    IsDecisive hs f (S₁ ∩ S₂) := by
  let _ := Fintype.ofFinite ι
  intro a ha b hb
  let P₂ := S₁ \ S₂; let P₃ := S₁ ∩ S₂
  let g (y : Fin 2 → MetricGraph W) := f fun i => if i ∈ P₂ then y 0 else if i ∈ P₃ then y 1 else b
  have hg_sp : (Mechanism.deterministic g).IsStrategyProof :=
    restrictTwo_isStrategyProof hf_sp
      (disjoint_sdiff_self_left.mono_right Finset.inter_subset_right) (fun _ => b)
  have hg_unam : ∀ p ∈ Set.range (circleMap hs.1), g (fun _ => p) = p := fun p hp => by
    have hfun : (fun i => if i ∈ P₂ then p else if i ∈ P₃ then p else b) =
        fun i => if i ∈ S₁ then p else b := by
      ext i; by_cases hi1 : i ∈ S₁ <;> by_cases hi2 : i ∈ S₂ <;> simp [P₂, P₃, hi1, hi2]
    simpa only [g, hfun] using h1 p hp b hb
  obtain ⟨k, hk⟩ := finTwo_cycleDictator W hs hg_sp hg_unam
  fin_cases k
  · exfalso
    obtain ⟨c', hc', hne⟩ := exists_ne_on_cycle W hs b
    have hP₂c : IsDecisive hs f P₂ᶜ := isDecisive_mono W hs hf_sp hf_unam
      (fun i hi2 => by simp [P₂, hi2]) h2
    have hfun : (fun i => if i ∈ P₂ then c' else if i ∈ P₃ then b else b) =
        fun i => if i ∈ P₂ᶜ then b else c' := by
      ext i; by_cases hi : i ∈ P₂ <;> simp [hi]
    have hval := hk c' hc' b hb
    dsimp only [g, Matrix.cons_val_zero, Matrix.cons_val_one] at hval
    rw [hfun, hP₂c b hb c' hc'] at hval
    exact hne hval.symm
  · have hfun : (fun i => if i ∈ P₂ then b else if i ∈ P₃ then a else b) =
        fun i => if i ∈ S₁ ∩ S₂ then a else b := by
      ext i; by_cases hi1 : i ∈ S₁ <;> by_cases hi2 : i ∈ S₂ <;> simp [P₂, P₃, hi1, hi2]
    have hval := hk b hb a ha
    dsimp only [g, Matrix.cons_val_zero, Matrix.cons_val_one] at hval
    rwa [hfun] at hval

/-- Ultrafilter lemma: the decisive coalitions contain a singleton `{i₀}`. -/
private theorem exists_singleton_isDecisive {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {ι : Type*} [Finite ι] [DecidableEq ι] {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p) :
    ∃ i₀ : ι, IsDecisive hs f {i₀} := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨p₀, p₁, hp₀, hp₁, hp₀₁⟩ := exists_two_distinct_on_cycle W hs
  have hU_univ : IsDecisive hs f (Finset.univ : Finset ι) := fun a ha _ _ => by
    simpa only [Finset.mem_univ, ↓reduceIte] using hf_unam a ha
  have hU_empty : ¬ IsDecisive hs f (∅ : Finset ι) := fun h => by
    have h1 := h p₀ hp₀ p₁ hp₁
    simp only [Finset.notMem_empty, ↓reduceIte] at h1
    rw [hf_unam p₁ hp₁] at h1
    exact hp₀₁ h1.symm
  let F : Finset (Finset ι) := Finset.univ.filter fun S => IsDecisive hs f S
  obtain ⟨S₀, hS₀_mem, hS₀_min⟩ := F.exists_min_image Finset.card
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU_univ⟩⟩
  have hS₀ : IsDecisive hs f S₀ := (Finset.mem_filter.mp hS₀_mem).2
  have hS₀_ne : S₀.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h => hU_empty (h ▸ hS₀)
  obtain ⟨i₀, hi₀⟩ := hS₀_ne
  refine ⟨i₀, (isDecisive_or_compl W hs hf_sp hf_unam {i₀}).resolve_right fun hic => ?_⟩
  have hF_in : S₀ ∩ ({i₀} : Finset ι)ᶜ ∈ F := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, isDecisive_inter W hs hf_sp hf_unam hS₀ hic⟩
  have hlt : (S₀ ∩ ({i₀} : Finset ι)ᶜ).card < S₀.card :=
    Finset.card_lt_card ⟨Finset.inter_subset_left, fun h => by simpa using h hi₀⟩
  linarith [hS₀_min _ hF_in]

/-! ### Lifting dictatorship to finitely many agents -/

/-- Any merged mechanism `y ↦ f (y ∘ m)` that is a dictatorship of `k` must have `k = m i₀`
whenever `{i₀}` is decisive for `f`. -/
private theorem dictator_merge_eq {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {ι ι' : Type*} [Finite ι] [DecidableEq ι]
    {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p)
    {i₀ : ι} (hi₀ : IsDecisive hs f {i₀}) (m : ι → ι') {k : ι'}
    (hk : ∀ y : ι' → MetricGraph W, (∀ j, y j ∈ Set.range (circleMap hs.1)) →
      f (fun i => y (m i)) = y k) : k = m i₀ := by
  classical
  let _ := Fintype.ofFinite ι
  by_contra hne
  obtain ⟨p₀, p₁, hp₀, hp₁, hp₀₁⟩ := exists_two_distinct_on_cycle W hs
  let y : ι' → MetricGraph W := fun j => if j = m i₀ then p₁ else p₀
  have hyC : ∀ j, y j ∈ Set.range (circleMap hs.1) := fun j => by
    dsimp only [y]; split_ifs <;> assumption
  let S : Finset ι := Finset.univ.filter fun i => m i = m i₀
  have hS : IsDecisive hs f S :=
    isDecisive_mono W hs hf_sp hf_unam (fun i hi => by
      rw [Finset.mem_singleton.mp hi]; simp [S]) hi₀
  have hfun : (fun i => y (m i)) = fun i => if i ∈ S then p₁ else p₀ := by ext i; simp [y, S]
  have hval := hk y hyC
  rw [hfun, hS p₁ hp₁ p₀ hp₀] at hval
  exact hp₀₁ (by simpa [y, hne] using hval.symm)

/-- Strong induction on `n = Fintype.card ι` lifting the two-agent cycle dictatorship and singleton
decisive coalition to arbitrary finite agent profiles on the shortest cycle `c`. -/
private theorem cycleDictator_of_unanimous_aux {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c) :
    ∀ n : ℕ, ∀ {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι],
      Fintype.card ι = n →
      ∀ {f : (ι → MetricGraph W) → MetricGraph W},
        (Mechanism.deterministic f).IsStrategyProof →
        (∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p) →
        ∃ i₀ : ι, ∀ x : ι → MetricGraph W,
          (∀ i, x i ∈ Set.range (circleMap hs.1)) → f x = x i₀ := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro ι _ _ _ hcard f hf_sp hf_unam
    let C := Set.range (circleMap hs.1)
    obtain ⟨i₀, hi₀_U⟩ := exists_singleton_isDecisive W hs hf_sp hf_unam
    refine ⟨i₀, ?_⟩
    rcases lt_trichotomy n 2 with hn_lt | rfl | hn_gt
    · intro x hx
      have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      have hx_c : x = fun _ => x i₀ := funext fun i => congrArg x (Subsingleton.elim i i₀)
      exact hx_c ▸ hf_unam (x i₀) (hx i₀)
    · let e : ι ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
      obtain ⟨k, hk⟩ := finTwo_cycleDictator W hs (merge_isStrategyProof hf_sp e)
        (fun p hp => hf_unam p hp)
      have hk_fun : ∀ y : Fin 2 → MetricGraph W, (∀ j, y j ∈ C) → f (fun i => y (e i)) = y k :=
        fun y hy => by
          simpa only [show (![y 0, y 1] : Fin 2 → MetricGraph W) = y by ext j; fin_cases j <;> rfl]
            using hk (y 0) (hy 0) (y 1) (hy 1)
      have hk_eq : k = e i₀ := dictator_merge_eq W hs hf_sp hf_unam hi₀_U e hk_fun
      intro x hx
      simpa only [hk_eq, Equiv.symm_apply_apply] using
        hk_fun (fun j => x (e.symm j)) fun j => hx (e.symm j)
    · have hagree {j₁ j₂ : ι} (hne : j₁ ≠ j₂) (x : ι → MetricGraph W) (hx : ∀ i, x i ∈ C)
          (hx12 : x j₁ = x j₂) : f x = x i₀ := by
        let ι' := { i : ι // i ≠ j₂ }
        have : Nonempty ι' := ⟨⟨j₁, hne⟩⟩
        let m : ι → ι' := fun i => if h : i = j₂ then ⟨j₁, hne⟩ else ⟨i, h⟩
        obtain ⟨k', hk'⟩ := ih (n - 1) (by omega) (ι := ι') (by simp [ι', hcard])
          (merge_isStrategyProof hf_sp m) fun p hp => hf_unam p hp
        have hk'_eq : k' = m i₀ := dictator_merge_eq W hs hf_sp hf_unam hi₀_U m hk'
        have hfun : (fun i => x (m i).1) = x := funext fun i => by
          by_cases h : i = j₂ <;> simp [m, h, hx12]
        have hval := hk' (fun i' => x i'.1) fun i' => hx i'.1
        rw [hfun, hk'_eq] at hval
        exact hval.trans (by by_cases h : i₀ = j₂ <;> simp [m, h, hx12])
      intro x hx
      have hcard_e : 1 < (Finset.univ.erase i₀).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, hcard]; omega
      obtain ⟨j₁, hj₁, j₂, hj₂, hj₁₂⟩ := Finset.one_lt_card.mp hcard_e
      have hj₁_ne : j₁ ≠ i₀ := Finset.ne_of_mem_erase hj₁
      have hj₂_ne : j₂ ≠ i₀ := Finset.ne_of_mem_erase hj₂
      let h (z : Fin 2 → MetricGraph W) :=
        f fun i => if i ∈ ({i₀} : Finset ι) then z 0 else if i ∈ ({j₁} : Finset ι) then z 1 else x i
      have hh_sp := restrictTwo_isStrategyProof hf_sp (Finset.disjoint_singleton.mpr hj₁_ne.symm) x
      have hh_unam : ∀ p ∈ C, h (fun _ => p) = p := fun p hp => by
        dsimp only [h]
        have heq := hagree hj₁_ne.symm (fun i => if i = i₀ then p else if i = j₁ then p else x i)
          (fun i => by split_ifs <;> first | exact hp | exact hx i) (by simp [hj₁_ne])
        simpa only [Finset.mem_singleton, ↓reduceIte] using heq
      obtain ⟨k, hk⟩ := finTwo_cycleDictator W hs hh_sp hh_unam
      fin_cases k
      · have hfun : (fun i => if i ∈ ({i₀} : Finset ι) then x i₀
            else if i ∈ ({j₁} : Finset ι) then x j₁ else x i) = x := by
          ext i; by_cases h0 : i = i₀ <;> by_cases h1 : i = j₁ <;> simp_all
        have hval := hk (x i₀) (hx i₀) (x j₁) (hx j₁)
        dsimp only [h, Matrix.cons_val_zero, Matrix.cons_val_one] at hval
        rwa [hfun] at hval
      · exfalso
        obtain ⟨b, hb, hab⟩ := exists_ne_on_cycle W hs (x j₂)
        have hag := hagree hj₂_ne.symm
          (fun i => if i = i₀ then x j₂ else if i = j₁ then b else x i)
          (fun i => by split_ifs <;> first | exact hx j₂ | exact hb | exact hx i)
          (by simp [hj₂_ne, hj₁₂.symm])
        have hval := hk (x j₂) (hx j₂) b hb
        simp only [Finset.mem_singleton, Matrix.cons_val_zero, Matrix.cons_val_one] at hval
        exact hab (hval.symm.trans (by simpa only [↓reduceIte] using hag))

/-! ### Main theorems -/

/-- **Schummer–Vohra cycle dictatorship** on shortest cycles ([SchummerVohra2002], Theorem 2,
for shortest cycles): every deterministic strategyproof
and onto facility-location mechanism on a finite metric graph `MetricGraph W` acts as a
dictatorship on the points of any shortest cycle `c` (without assuming the image on `C^ι` lies in
`C`, and without assuming group strategyproofness). -/
theorem exists_cycleDictator_of_isShortestCycle {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {ι : Type*} [Finite ι] [Nonempty ι] [DecidableEq ι]
    {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) :
    ∃ i₀ : ι, ∀ x : ι → MetricGraph W,
      (∀ i, x i ∈ Set.range (circleMap hs.1)) → f x = x i₀ :=
  let _ := Fintype.ofFinite ι
  cycleDictator_of_unanimous_aux W hs (Fintype.card ι) rfl hf_sp
    (fun p _ => unanimous_of_surjective_isStrategyProof hf_sp hf_onto p)

/-- On any finite non-acyclic metric graph `MetricGraph W`, there exists a shortest cycle `c`
on which every deterministic strategyproof onto mechanism acts as a dictatorship. -/
theorem exists_cycleDictator_of_not_isAcyclic {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hc : ¬ W.graph.IsAcyclic)
    {ι : Type*} [Finite ι] [Nonempty ι] [DecidableEq ι]
    {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) :
    ∃ (v₀ : V) (c : W.graph.Walk v₀ v₀) (hs : IsShortestCycle W c) (i₀ : ι),
      ∀ x : ι → MetricGraph W, (∀ i, x i ∈ Set.range (circleMap hs.1)) → f x = x i₀ := by
  obtain ⟨v₀, c, hs⟩ := exists_isShortestCycle (W := W) hc
  obtain ⟨i₀, hi₀⟩ := exists_cycleDictator_of_isShortestCycle W hs hf_sp hf_onto
  exact ⟨v₀, c, hs, i₀, hi₀⟩

/-- Every deterministic strategyproof onto facility-location mechanism on a finite cycle graph
`cycleGraph (n + 3)` is a global dictatorship. -/
theorem exists_dictatorship_of_cycleGraph {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {n : ℕ} (e : W.graph ≃g SimpleGraph.cycleGraph (n + 3))
    {ι : Type*} [Finite ι] [Nonempty ι] [DecidableEq ι]
    {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) :
    ∃ i₀ : ι, ∀ x : ι → MetricGraph W, f x = x i₀ := by
  obtain ⟨_, c, hs, i₀, hi₀⟩ := exists_cycleDictator_of_not_isAcyclic W
    (fun h => h ((SimpleGraph.cycleGraph.cycle n).map e.symm.toHom)
      (SimpleGraph.cycleGraph.isCycle_cycle.map e.symm.injective))
    hf_sp hf_onto
  exact ⟨i₀, fun x => hi₀ x fun i => circleMap_surjective_of_cycleGraph e hs.1 (x i)⟩

end CycleDictator

end Cslib.GameTheory.FacilityLocation
