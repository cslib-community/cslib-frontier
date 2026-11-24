/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.Certificate
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.Concentration
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.TreeWave
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Cubic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Crossing-cover cutwidth bounds for cubic graphs

This module assembles the crossing-cover Gaussian-wave layout bound for finite cubic graphs and
lifts it via saturated compression (`Cslib.Circuits.Frontier.LayoutBound.of_cubic`) to
subcubic multigraphs (`LayoutBound 3 A`).

## Mathematical pipeline

1. **Submodular crossing covers and deterministic interpolation**
   (`Layouts.CrossingCover.Submodular`, `Layouts.CrossingCover.Interpolation`): for every vertex
   ordering whose prefix cuts each have minimum crossing-edge vertex cover `crossingCover G b ≤ M`,
   greedy clamped block-peeling yields a vertex layout of width at most `M + 6`.
2. **Finite high-girth covering graphs and König duality** (`Layouts.CrossingCover.CoverLifting`):
   every finite cubic simple graph `H` admits an `m`-sheeted covering graph `H'` of arbitrarily
   large girth preserving `simpleCrossingCover` with exact multiplicity `m`.
3. **Slepian / Kahane Gaussian comparison** (`Layouts.CrossingCover.GaussianComparison`):
   submodularity and symmetry of `simpleCrossingCover` reduce its Gaussian expectation at any
   threshold `t` on `H` to the higher-variance centered (`t = 0`) expectation on `H'`.
4. **Alternating non-backtracking walk bound** (`Layouts.CrossingCover.AlternatingSum`):
   for every odd cutoff `J`, `2 * simpleCrossingCover H' b` is bounded by the alternating sum of
   directed non-backtracking crossing-walk counts of lengths `1 ≤ j ≤ J`, plus an error term
   counting degree-3 vertices in the crossing subgraph.
5. **Gaussian waves on the cubic tree and AR(2) limit** (`Layouts.CrossingCover.TreeWave`):
   the radial pushed wave `waveScore H R ε g` yields expected crossing cover at most
   `(alternatingWaveSum J + η) * |V|` simultaneously for every threshold `t : ℝ`. The AR(2)
   density and `alternatingWaveSum` are defined once, in `Layouts.CrossingCover.AR2Density`.
6. **Efron–Stein concentration** (`Layouts.CrossingCover.Concentration`): the local support of
   `waveRow H R ε` implies `O(|V|)` variance along a uniform grid of thresholds, turning the
   expected crossing-cover bound into a vertex layout of width at most `(alternatingWaveSum J + ξ) *
   |V|` for all large cubic graphs (`cubicLayoutBound_crossingCover`).
7. **Certified Gauss–Legendre quadrature** (`Layouts.CrossingCover.Certificate`): kernel-checked
   fixed-point `Nat` interval arithmetic (no `native_decide`) certifies
   `alternatingWaveSum 13 < 130649 / 1000000`.

The resulting layout coefficient `A = 130649 / 500000` gives the slope
`1 + 1/A = 630649 / 130649 ≈ 4.827048` in the frontier lower bound for fan-in two
(`Cslib.Circuits.Frontier.eventually_crossingCover_sub_mul_lt_multiarySize`), which exceeds
`4827 / 1000`. The bound is for the cutoff `J = 13` only: `cubicLayoutBound_crossingCover` holds
for every odd `J`, but `alternatingWaveSum J` is certified numerically only at `J = 13`.

## Sources

No published theorem is formalized here. The crossing-cover Gaussian-wave proof architecture
follows the public `Layr-Labs/circuitbreaker-llm-verifier` contest submissions (PRs #843, #858
and #859 by `@galarnon42` and `@ArthurOstapenko`); the Lean development and the fixed-point
quadrature certificate are new.

The cut function `crossingCover G b` is the maximum-matching value `mm(S)` of maximum matching
width in its minimum-vertex-cover form: [JeongSaetherTelle2015], §1 and §2, define `mm(S)` as the
size of a maximum matching of the bipartite graph crossing the cut `(S, V ∖ S)`, note that by
Kőnig's theorem this is the minimum vertex cover, and attribute the parameter to Vatshelle's 2012
thesis. That paper states the definition for a graph; here `G` is a multigraph and the
vertex-cover form is taken as the definition.

## Main results

* `Cslib.Circuits.Frontier.CrossingCover.cubicLayoutBound_crossingCover`:
  `CubicLayoutBound (alternatingWaveSum J)` for every odd `J`.
* `Cslib.Circuits.Frontier.layoutBound_crossingCover_of_odd`:
  `LayoutBound 3 (2 * alternatingWaveSum J)` for every odd `J`.
* `Cslib.Circuits.Frontier.layoutBound_crossingCover`: `LayoutBound 3 (130649 / 500000)`.

## References

* [J. Jeong, S. H. Sæther, J. A. Telle, *Maximum Matching Width: New Characterizations and a Fast
  Algorithm for Dominating Set*][JeongSaetherTelle2015]
-/

public section

namespace Cslib.Circuits.Frontier

open Finset MeasureTheory Real

namespace CrossingCover

/-! ### Simple-graph degree and locality support bounds -/

/-- For a loopless multigraph without parallel edges in which every vertex has three incident edges,
the underlying simple graph is `3`-regular. -/
private theorem degree_toSimpleGraph_eq_three {V E : Type*} [Fintype V] [Finite E]
    (G : Multigraph V E) (hloop : G.Loopless) (hinj : Function.Injective G.ends)
    (h3 : ∀ v : V, (G.incidenceSet v).ncard = 3) (v : V) :
    open Classical in G.toSimpleGraph.degree v = 3 := by
  classical
  have := Fintype.ofFinite E
  let inc : Finset E := Finset.univ.filter fun e : E => e ∈ G.incidenceSet v
  have hinc_card : inc.card = 3 := by
    have hset : (inc : Set E) = G.incidenceSet v := by
      ext e; simp [inc]
    rw [← Set.ncard_coe_finset, hset]
    exact h3 v
  let other : E → V := fun e => if G.src e = v then G.tgt e else G.src e
  have hmem_ends : ∀ e ∈ inc, G.ends e = s(v, other e) ∧ v ≠ other e := by
    intro e he
    have hm : G.src e = v ∨ G.tgt e = v := (Finset.mem_filter.mp he).2
    have hne : G.src e ≠ G.tgt e := hloop e
    by_cases hs : G.src e = v
    · have ho : other e = G.tgt e := by simp [other, hs]
      refine ⟨?_, ?_⟩
      · simp [Multigraph.ends, hs, ho]
      · rw [ho, ← hs]; exact hne
    · have ht : G.tgt e = v := hm.resolve_left hs
      have ho : other e = G.src e := by simp [other, hs]
      refine ⟨?_, ?_⟩
      · simp [Multigraph.ends, ht, ho, Sym2.eq_swap]
      · rw [ho]; exact Ne.symm hs
  have hcard_eq : (G.toSimpleGraph.neighborFinset v).card = inc.card := by
    refine (Finset.card_bij (fun e _ => other e) ?_ ?_ ?_).symm
    · intro e he
      obtain ⟨hends, hne⟩ := hmem_ends e he
      rw [SimpleGraph.mem_neighborFinset, Multigraph.toSimpleGraph_adj]
      exact ⟨hne, e, hends⟩
    · intro e₁ he₁ e₂ he₂ heq
      have h1 := (hmem_ends e₁ he₁).1
      have h2 := (hmem_ends e₂ he₂).1
      exact hinj (by rw [h1, h2, heq])
    · intro u hu
      rw [SimpleGraph.mem_neighborFinset, Multigraph.toSimpleGraph_adj] at hu
      obtain ⟨hne, e, hends⟩ := hu
      have hcases : (G.src e = v ∧ G.tgt e = u) ∨ (G.src e = u ∧ G.tgt e = v) := by
        simpa [Multigraph.ends, Sym2.eq_iff] using hends
      rcases hcases with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hs⟩, ?_⟩
        simp [other, hs, ht]
      · refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ht⟩, ?_⟩
        simp [other, hs, hne.symm]
  simpa only [SimpleGraph.card_neighborFinset_eq_degree, hinc_card] using hcard_eq

/-- Sum of `3`-regular non-backtracking sphere sizes up to radius `R` is at most `3 * 2 ^ R`. -/
private theorem sum_nbSphere_le (R : ℕ) :
    ∑ k ∈ Finset.range (R + 1), (if k = 0 then 1 else 3 * 2 ^ (k - 1)) ≤ 3 * 2 ^ R := by
  induction R with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have hpow : 3 * 2 ^ r + 3 * 2 ^ r = 3 * 2 ^ (r + 1) := by ring
    exact (Nat.add_le_add_right ih (3 * 2 ^ r)).trans_eq hpow

/-- Row-support squared-cardinality bound for the radial Gaussian wave rows `waveRow H R ε`:
each `Sum.inl x` influences at most `3 * 2 ^ R` vertices, and each `Sum.inr x` influences at most
`1` vertex, so the sum of squared influence counts is at most `((3 * 2 ^ R) ^ 2 + 1) * |V|`. -/
private theorem sum_sq_support_waveRow_le {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hreg : ∀ v : V, open Classical in H.degree v = 3) (R : ℕ) (ε : ℝ) :
    open Classical in
    ∑ z : V ⊕ V, ((Finset.univ.filter fun v : V => waveRow H R ε v z ≠ 0).card : ℝ) ^ 2 ≤
      ((3 * (2 : ℝ) ^ R) ^ 2 + 1) * (Nat.card V : ℝ) := by
  classical
  rw [Fintype.sum_sum_type]
  have hinl : ∀ x : V,
      (Finset.univ.filter fun v : V => waveRow H R ε v (Sum.inl x) ≠ 0).card ≤ 3 * 2 ^ R := by
    intro x
    let S := Finset.univ.filter fun v : V => waveRow H R ε v (Sum.inl x) ≠ 0
    have hpos : ∀ v ∈ S, 1 ≤ ∑ k ∈ Finset.range (R + 1), nbCount H k x v := by
      intro v hv
      have hne : waveRow H R ε v (Sum.inl x) ≠ 0 := (Finset.mem_filter.mp hv).2
      have hp : pushedProb H R v x ≠ 0 := by
        intro hp0
        apply hne
        simp [waveRow, hp0]
      obtain ⟨k, hkR, w, hnb, h0, hl⟩ := exists_nbWalk_of_pushedProb_ne_zero hp
      have hcnt : 1 ≤ nbCount H k v x := by
        refine Finset.card_pos.mpr ⟨w, ?_⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnb, h0, hl⟩
      rw [nbCount_symm] at hcnt
      exact hcnt.trans (Finset.single_le_sum (f := fun k => nbCount H k x v)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hkR)))
    calc S.card
        = ∑ _v ∈ S, 1 := by simp
      _ ≤ ∑ v ∈ S, ∑ k ∈ Finset.range (R + 1), nbCount H k x v := Finset.sum_le_sum hpos
      _ ≤ ∑ v : V, ∑ k ∈ Finset.range (R + 1), nbCount H k x v :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      _ = ∑ k ∈ Finset.range (R + 1), ∑ v : V, nbCount H k x v := Finset.sum_comm
      _ = ∑ k ∈ Finset.range (R + 1), (if k = 0 then 1 else 3 * 2 ^ (k - 1)) :=
          Finset.sum_congr rfl fun k _ => sum_nbCount_eq H hreg k x
      _ ≤ 3 * 2 ^ R := sum_nbSphere_le R
  have hinr : ∀ x : V,
      (Finset.univ.filter fun v : V => waveRow H R ε v (Sum.inr x) ≠ 0).card ≤ 1 := by
    intro x
    have hsub : (Finset.univ.filter fun v : V => waveRow H R ε v (Sum.inr x) ≠ 0) ⊆ {x} := by
      intro v hv
      have hne : waveRow H R ε v (Sum.inr x) ≠ 0 := (Finset.mem_filter.mp hv).2
      have heq : x = v := by
        by_contra hxv
        exact hne (by simp [waveRow, hxv])
      simp [heq]
    exact (Finset.card_le_card hsub).trans (by simp)
  have hsum_inl : ∑ x : V,
      ((Finset.univ.filter fun v : V => waveRow H R ε v (Sum.inl x) ≠ 0).card : ℝ) ^ 2 ≤
      (3 * (2 : ℝ) ^ R) ^ 2 * (Fintype.card V : ℝ) := by
    have hpt : ∀ x : V,
        ((Finset.univ.filter fun v : V => waveRow H R ε v (Sum.inl x) ≠ 0).card : ℝ) ^ 2 ≤
        (3 * (2 : ℝ) ^ R) ^ 2 := fun x => by
      have hcast : ((Finset.univ.filter fun v : V =>
          waveRow H R ε v (Sum.inl x) ≠ 0).card : ℝ) ≤ 3 * (2 : ℝ) ^ R := by
        exact_mod_cast hinl x
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcast 2
    calc ∑ x : V,
          ((Finset.univ.filter fun v : V => waveRow H R ε v (Sum.inl x) ≠ 0).card : ℝ) ^ 2
        ≤ ∑ _x : V, (3 * (2 : ℝ) ^ R) ^ 2 := Finset.sum_le_sum fun x _ => hpt x
      _ = (3 * (2 : ℝ) ^ R) ^ 2 * (Fintype.card V : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  have hsum_inr : ∑ x : V,
      ((Finset.univ.filter fun v : V => waveRow H R ε v (Sum.inr x) ≠ 0).card : ℝ) ^ 2 ≤
      (Fintype.card V : ℝ) := by
    have hpt : ∀ x : V,
        ((Finset.univ.filter fun v : V => waveRow H R ε v (Sum.inr x) ≠ 0).card : ℝ) ^ 2 ≤ 1 := by
      intro x
      have hcast : ((Finset.univ.filter fun v : V =>
          waveRow H R ε v (Sum.inr x) ≠ 0).card : ℝ) ≤ 1 := by
        exact_mod_cast hinr x
      have h0 : (0 : ℝ) ≤ ((Finset.univ.filter fun v : V =>
          waveRow H R ε v (Sum.inr x) ≠ 0).card : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc ∑ x : V,
          ((Finset.univ.filter fun v : V => waveRow H R ε v (Sum.inr x) ≠ 0).card : ℝ) ^ 2
        ≤ ∑ _x : V, (1 : ℝ) := Finset.sum_le_sum fun x _ => hpt x
      _ = (Fintype.card V : ℝ) := by simp
  rw [Nat.card_eq_fintype_card]
  linarith [hsum_inl, hsum_inr]

/-! ### Nonnegativity -/

/-- For every odd `J : ℕ`, `0 ≤ alternatingWaveSum J` (proved by testing the wave expectation
bound on `K₄`). -/
theorem alternatingWaveSum_nonneg_of_odd {J : ℕ} (hJ : Odd J) :
    0 ≤ alternatingWaveSum J := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨R, ε, _, _, hbd⟩ := exists_wave_params_expected_crossingCover_le.{0} J hJ η hη
  have h0 : (0 : ℝ) ≤ ∫ g,
      (simpleCrossingCover (⊤ : SimpleGraph (Fin 4))
        (thresholdVec (waveScore (⊤ : SimpleGraph (Fin 4)) R ε g) 0) : ℝ)
      ∂(piGauss (Fin 4 ⊕ Fin 4)) :=
    integral_nonneg fun _ => Nat.cast_nonneg _
  have hle := hbd (⊤ : SimpleGraph (Fin 4)) (fun v => by
    have heq : Finset.card (Finset.univ.erase v) = 3 := by
      rw [Finset.card_erase_of_mem (mem_univ v)]; simp
    rw [← heq]
    unfold SimpleGraph.degree
    exact congrArg Finset.card (Finset.ext fun u => by simp [ne_comm])) 0
  have hcard : (Fintype.card (Fin 4) : ℝ) = 4 := by norm_num
  rw [hcard] at hle
  linarith

/-! ### Main cubic layout theorem -/

/-- **The crossing-cover cubic layout bound.** For every odd cutoff `J`, every sufficiently large
finite cubic simple graph `G` admits a vertex layout of width at most
`(alternatingWaveSum J + ξ) * |V|`. -/
theorem cubicLayoutBound_crossingCover (J : ℕ) (hJ : Odd J) :
    CubicLayoutBound (alternatingWaveSum J) := by
  intro ξ hξ
  have hξ2 : 0 < ξ / 2 := by positivity
  obtain ⟨R, ε, hε0, hε1, hexp_wave⟩ :=
    exists_wave_params_expected_crossingCover_le.{0} J hJ (ξ / 2) hξ2
  set γ : ℝ := alternatingWaveSum J + ξ / 2
  have hγ_nonneg : 0 ≤ γ := add_nonneg (alternatingWaveSum_nonneg_of_odd hJ) hξ2.le
  set C : ℝ := (3 * (2 : ℝ) ^ R) ^ 2 + 1
  set ξ' : ℝ := ξ / 2
  set T : ℝ := Real.sqrt (4 / ξ')
  have hT_pos : 0 < T := Real.sqrt_pos.mpr (by positivity)
  have hT_sq : T ^ 2 = 4 / ξ' := Real.sq_sqrt (by positivity)
  have hT_bd : 1 / T ^ 2 ≤ ξ' / 4 := by
    rw [hT_sq]; field_simp; exact le_rfl
  set K : ℕ := Nat.ceil ((2 * T) / (Real.sqrt (2 * Real.pi) * (ξ' / 4))) + 1
  have hK_pos : 0 < K := Nat.succ_pos _
  have hK_real_ge : (2 * T) / (Real.sqrt (2 * Real.pi) * (ξ' / 4)) ≤ (K : ℝ) := by
    have h1 := Nat.le_ceil ((2 * T) / (Real.sqrt (2 * Real.pi) * (ξ' / 4)))
    have h2 : (Nat.ceil ((2 * T) / (Real.sqrt (2 * Real.pi) * (ξ' / 4))) : ℝ) ≤ K := by
      simp only [K, Nat.cast_add, Nat.cast_one]; linarith
    exact h1.trans h2
  have hK_bd : (2 * T / K) / Real.sqrt (2 * Real.pi) ≤ ξ' / 4 := by
    have hden_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hK_rpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK_pos
    rw [div_div, div_le_iff₀ (mul_pos hK_rpos hden_pos)]
    have hmul := mul_le_mul_of_nonneg_right hK_real_ge (by positivity :
      0 ≤ Real.sqrt (2 * Real.pi) * (ξ' / 4))
    have hne : Real.sqrt (2 * Real.pi) * (ξ' / 4) ≠ 0 := by positivity
    rw [div_mul_cancel₀ _ hne] at hmul
    linarith
  set Nprob : ℕ := Nat.ceil ((2 * (K : ℝ) + 2) * C / (ξ' / 8) ^ 2)
  set Nsix : ℕ := Nat.ceil (24 / ξ')
  refine ⟨max Nprob Nsix, fun V E _ _ G hloop hinj h3 hV => ?_⟩
  have : Fintype V := Fintype.ofFinite V
  have hreg : ∀ v : V, open Classical in G.toSimpleGraph.degree v = 3 :=
    degree_toSimpleGraph_eq_three G hloop hinj h3
  have hV_prob : (2 * (K : ℝ) + 2) * C / (ξ' / 8) ^ 2 < (Nat.card V : ℝ) := by
    have hlt : Nprob < Nat.card V := lt_of_le_of_lt (le_max_left _ _) hV
    have hlt_r : (Nprob : ℝ) < (Nat.card V : ℝ) := by exact_mod_cast hlt
    exact lt_of_le_of_lt (Nat.le_ceil _) hlt_r
  have hV_six : (6 : ℝ) ≤ (ξ' / 4) * (Nat.card V : ℝ) := by
    have hlt : Nsix < Nat.card V := lt_of_le_of_lt (le_max_right _ _) hV
    have hle_r : (24 / ξ' : ℝ) ≤ (Nat.card V : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hlt.le)
    have := mul_le_mul_of_nonneg_left hle_r (by positivity : 0 ≤ ξ' / 4)
    have heq : (ξ' / 4) * (24 / ξ') = (6 : ℝ) := by field_simp; norm_num
    linarith
  have hunit : ∀ v : V, ∑ z : V ⊕ V, waveRow G.toSimpleGraph R ε v z ^ 2 = 1 :=
    sum_sq_waveRow_eq_one G.toSimpleGraph hreg R hε0.le hε1.le
  have hsupp : open Classical in
      ∑ z : V ⊕ V, ((Finset.univ.filter fun v : V =>
        waveRow G.toSimpleGraph R ε v z ≠ 0).card : ℝ) ^ 2 ≤ C * (Nat.card V : ℝ) :=
    sum_sq_support_waveRow_le G.toSimpleGraph hreg R ε
  have hexp : ∀ t : ℝ,
      ∫ g : V ⊕ V → ℝ,
        (crossingCover G
          (thresholdVec (fun v => ∑ z : V ⊕ V, waveRow G.toSimpleGraph R ε v z * g z) t) : ℝ)
        ∂(piGauss (V ⊕ V)) ≤ γ * (Nat.card V : ℝ) := fun t => by
    have hpt : ∀ g : V ⊕ V → ℝ,
        (crossingCover G
          (thresholdVec (fun v => ∑ z : V ⊕ V, waveRow G.toSimpleGraph R ε v z * g z) t) : ℝ) =
        (simpleCrossingCover G.toSimpleGraph
          (thresholdVec (waveScore G.toSimpleGraph R ε g) t) : ℝ) := fun g => by
      rw [← simpleCrossingCover_toSimpleGraph]; rfl
    simp_rw [hpt]
    have hle := hexp_wave G.toSimpleGraph hreg t
    rw [← Nat.card_eq_fintype_card] at hle
    exact hle
  obtain ⟨lay, hlay⟩ := exists_width_le_of_expected_crossingCover G h3
    (waveRow G.toSimpleGraph R ε) hunit hγ_nonneg hξ2 hsupp hexp
    hT_pos hT_bd hK_pos hK_bd hV_prob hV_six
  refine ⟨lay, hlay.trans_eq ?_⟩
  simp only [γ, ξ']; ring

end CrossingCover

/-! ### Top-level subcubic layout bounds (`LayoutBound 3 A`) -/

/-- **Subcubic layout bound from the crossing-cover Gaussian wave method.** For every odd cutoff
`J`, the layout hypothesis for maximum degree three holds with coefficient
`2 * alternatingWaveSum J`. -/
theorem layoutBound_crossingCover_of_odd {J : ℕ} (hJ : Odd J) :
    LayoutBound 3 (2 * CrossingCover.alternatingWaveSum J) :=
  LayoutBound.of_cubic (CrossingCover.alternatingWaveSum_nonneg_of_odd hJ)
    (CrossingCover.cubicLayoutBound_crossingCover J hJ)

/-- **The `130649 / 500000` subcubic layout bound.** The layout hypothesis for maximum degree
three holds with coefficient `130649 / 500000`, from the crossing-cover Gaussian-wave method at
cutoff `J = 13` and the certified bound `alternatingWaveSum 13 < 130649 / 1000000`. In the
frontier lower bound for fan-in two this gives the slope `1 + 500000 / 130649 = 630649 / 130649`,
which exceeds `4827 / 1000`. -/
theorem layoutBound_crossingCover : LayoutBound 3 (130649 / 500000) :=
  (layoutBound_crossingCover_of_odd (J := 13) (by decide)).mono
    (by linarith [CrossingCover.alternatingWaveSum_13_lt])

end Cslib.Circuits.Frontier
