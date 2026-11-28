/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Clique.lean`)

public import CslibFrontier.Foundations.Combinatorics.Digraph.Branching
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.IndepCount
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Logic.Relation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Independent-set bounds on directed out-forests

A branching `B : Digraph V` (`hB : B.IsBranching`: at most one incoming arc per vertex and no
directed cycles) forms a directed out-forest whose underlying undirected graph
`SimpleGraph.fromRel B.Adj` is acyclic (`Digraph.IsBranching.toSimpleGraph_isAcyclic`).

On a finite vertex type `V`, every branching admits a strict root-distance ranking
(`Digraph.IsBranching.exists_rank`). In the degree-capped forest, every non-root vertex `u` has at
most two children. The fraction `p(T_u) = i₀(T_u) / i(T_u)` of independent sets of its subtree
that omit `u` lies in `[1 / 2, 4 / 5]`. The induction uses the quadratic potential
`f(p) = (2 / 5) * (p - 1 / 2) + (3 / 10) * (p - 1 / 2) ^ 2`. At a component root the proof
combines the ratios of up to three children and subtracts the active-root penalty whenever there
is a child. The resulting entropy bound is

`Real.logb 2 i(G) ≤ |V| - (53 / 200) * cappedEdges(B) - (33 / 1000) * |activeRoots(B)|`

for arbitrary out-degrees (`SimpleGraph.logb_indepSetCount_fromRel_le_capped`), reducing to
`(SimpleGraph.fromRel B.Adj).edgeSet.ncard` whenever internal vertices have out-degree at most `2`
and roots have out-degree at most `3` (`SimpleGraph.logb_indepSetCount_fromRel_le`). These results
are original to this library.

## Main definitions

* `SimpleGraph.arborescenceActiveRoots`: roots (`¬∃ u, B.Adj u r`) with at least one outgoing arc.
* `SimpleGraph.arborescenceCappedEdges`: total outgoing arcs after capping internal vertices at `2`
  and roots at `3`.

## Main results

* `SimpleGraph.indepSetCount_anti`: adding edges never increases `indepSetCount`.
* `SimpleGraph.arborescenceCappedEdges_eq_ncard_edgeSet`: when non-roots have out-degree `≤ 2` and
  roots have out-degree `≤ 3`, `arborescenceCappedEdges B` equals `(fromRel B.Adj).edgeSet.ncard`.
* `SimpleGraph.logb_indepSetCount_fromRel_le_capped`: universal `(53 / 200)` edge and `(33 / 1000)`
  active-root upper bound on `Real.logb 2 (fromRel B.Adj).indepSetCount`.
* `SimpleGraph.logb_indepSetCount_fromRel_le`, `SimpleGraph.indepSetCount_fromRel_le_rpow`:
  bounded-out-degree specializations in logarithmic and exponential (`2 ^ ·`) forms.
-/

public section

open Set

namespace SimpleGraph

variable {V : Type*}

/-- Adding edges to a finite simple graph can only shrink its family of independent sets. -/
theorem indepSetCount_anti [Finite V] {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) :
    G₂.indepSetCount ≤ G₁.indepSetCount := by
  refine ncard_le_ncard (fun s hs u hu w hw hne hadj => ?_) (toFinite _)
  exact hs hu hw hne (h hadj)

/-! ### Rational logarithm and Bernstein polynomial certificates -/

private noncomputable def treePot (p : ℝ) : ℝ :=
  (2 / 5 : ℝ) * (p - 1 / 2) + (3 / 10 : ℝ) * (p - 1 / 2) ^ 2

private theorem treePot_half : treePot (1 / 2) = 0 := by
  unfold treePot
  ring

/-- Universal cubic upper bound `Real.log (1 + t) ≤ t - t ^ 2 / 2 + t ^ 3 / 3` for all `t > -1`,
proved from `g'(x) = x ^ 3 / (1 + x)` (`≤ 0` on `(-1, 0]` and `≥ 0` on `[0, ∞)`). -/
private theorem log_one_add_le_cubic {t : ℝ} (ht : -1 < t) :
    Real.log (1 + t) ≤ t - t ^ 2 / 2 + t ^ 3 / 3 := by
  let g : ℝ → ℝ := fun x => x - x ^ 2 / 2 + x ^ 3 / 3 - Real.log (1 + x)
  have hderiv : ∀ x : ℝ, -1 < x → HasDerivAt g (x ^ 3 / (1 + x)) x := by
    intro x hx
    have hpos : 0 < 1 + x := by linarith
    have h1 : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3) (1 - x + x ^ 2) x :=
      (((hasDerivAt_id x).sub ((hasDerivAt_pow 2 x).div_const 2)).add
        ((hasDerivAt_pow 3 x).div_const 3)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 + x)⁻¹ x :=
      (((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log hpos.ne').congr_deriv (by simp)
    exact (h1.sub h2).congr_deriv (by field_simp [hpos.ne']; ring)
  have hg0 : g 0 = 0 := by simp [g]
  suffices h0 : g 0 ≤ g t by
    rw [hg0] at h0
    dsimp only [g] at h0
    linarith
  rcases le_or_gt 0 t with hnonneg | hneg
  · refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x : ℝ => x ^ 3 / (1 + x))
      (convex_Ici 0)
      (fun x hx => (hderiv x (by linarith [mem_Ici.mp hx])).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_) (by simp) hnonneg hnonneg
    · rw [interior_Ici] at hx
      exact (hderiv x (by linarith [mem_Ioi.mp hx])).hasDerivWithinAt
    · rw [interior_Ici, mem_Ioi] at hx
      exact div_nonneg (by positivity) (by linarith)
  · refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x : ℝ => x ^ 3 / (1 + x))
      (convex_Icc t 0)
      (fun x hx => (hderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_) ⟨le_rfl, hneg.le⟩ ⟨hneg.le, le_rfl⟩ hneg.le
    · rw [interior_Icc] at hx
      exact (hderiv x (by linarith [hx.1])).hasDerivWithinAt
    · rw [interior_Icc] at hx
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hx.2, sq_nonneg x])
        (by linarith [hx.1])

private theorem log_five_div_four_le : Real.log (5 / 4) ≤ 22324 / 100000 := by
  have hsplit : Real.log (5 / 4) = Real.log (1 + 1 / 8) + Real.log (1 + 1 / 9) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  linarith [log_one_add_le_cubic (t := 1 / 8) (by norm_num),
    log_one_add_le_cubic (t := 1 / 9) (by norm_num)]

private theorem log_three_div_two_le : Real.log (3 / 2) ≤ 40561 / 100000 := by
  have hsplit : Real.log (3 / 2) =
      Real.log (5 / 4) + Real.log (1 + 1 / 10) + Real.log (1 + 1 / 11) := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  linarith [log_five_div_four_le, log_one_add_le_cubic (t := 1 / 10) (by norm_num),
    log_one_add_le_cubic (t := 1 / 11) (by norm_num)]

private theorem log_thirteen_div_eight_le : Real.log (13 / 8) ≤ 48567 / 100000 := by
  have hsplit : Real.log (13 / 8) = Real.log (3 / 2) + Real.log (1 + 1 / 12) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  linarith [log_three_div_two_le, log_one_add_le_cubic (t := 1 / 12) (by norm_num)]

/-- Helper converting a natural-log upper bound into a base-2 log upper bound whenever RHS ≥ 0. -/
private theorem logb_two_le_of_log_le {x B U : ℝ} (hB : 0 ≤ B)
    (hlog : Real.log x ≤ U) (hrat : U ≤ (69313 / 100000 : ℝ) * B) :
    Real.logb 2 x ≤ B := by
  have hln2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln2_ge : (69313 / 100000 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [Real.logb, div_le_iff₀ hln2_pos]
  calc Real.log x ≤ U := hlog
    _ ≤ (69313 / 100000 : ℝ) * B := hrat
    _ ≤ Real.log 2 * B := mul_le_mul_of_nonneg_right hln2_ge hB
    _ = B * Real.log 2 := mul_comm _ _

/-- Barycentric coordinates on `[1 / 2, 4 / 5]`: `q = 1 / 2 + (3 / 10) * u` with `u, v ≥ 0`
and `v = 1 - u`. -/
private theorem exists_barycentric_coords {q : ℝ} (hq1 : 1 / 2 ≤ q) (hq2 : q ≤ 4 / 5) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ q = 1 / 2 + (3 / 10) * u ∧ v = 1 - u :=
  ⟨(10 * q - 5) / 3, (8 - 10 * q) / 3, by linarith, by linarith, by ring, by ring⟩

private theorem log_one_add_le_thirteen_eighths {p : ℝ} (hp1 : 1 / 2 ≤ p) :
    let t := (8 * p - 5) / 13
    Real.log (1 + p) ≤ 48567 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3) := by
  intro t
  have hsplit : 1 + p = (13 / 8) * (1 + t) := by dsimp only [t]; ring
  rw [hsplit, Real.log_mul (by norm_num) (by dsimp only [t]; linarith)]
  have hcub := log_one_add_le_cubic (t := t) (by dsimp only [t]; linarith)
  linarith [log_thirteen_div_eight_le, hcub]

private theorem log_one_add_sq_le_three_halves {q : ℝ} :
    let t := (2 * q ^ 2 - 1) / 3
    Real.log (1 + q ^ 2) ≤ 40561 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3) := by
  intro t
  have hsplit : 1 + q ^ 2 = (3 / 2) * (1 + t) := by dsimp only [t]; ring
  have ht_gt : -1 < t := by dsimp only [t]; nlinarith [sq_nonneg q]
  rw [hsplit, Real.log_mul (by norm_num) (by linarith)]
  linarith [log_three_div_two_le, log_one_add_le_cubic ht_gt]

private theorem sqrt_mul_bounds {p₁ p₂ : ℝ} (h1lo : 1 / 2 ≤ p₁) (h1hi : p₁ ≤ 4 / 5)
    (h2lo : 1 / 2 ≤ p₂) (h2hi : p₂ ≤ 4 / 5) :
    (Real.sqrt (p₁ * p₂)) ^ 2 = p₁ * p₂ ∧
      1 / 2 ≤ Real.sqrt (p₁ * p₂) ∧ Real.sqrt (p₁ * p₂) ≤ 4 / 5 := by
  refine ⟨Real.sq_sqrt (by nlinarith), ?_, ?_⟩
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 5)]
    exact Real.sqrt_le_sqrt (by nlinarith)

/-- `1`-child inductive step on `[1 / 2, 4 / 5]`. -/
private theorem step_one_child {p : ℝ} (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 4 / 5) :
    Real.logb 2 (1 + p) + treePot (1 / (1 + p)) - treePot p ≤ 1 - 53 / 200 := by
  obtain ⟨u, v, hu, hv, hp_eq, hv_eq⟩ := exists_barycentric_coords hp1 hp2
  set t : ℝ := (8 * p - 5) / 13
  set B : ℝ := (1 - 53 / 200) + treePot p - treePot (1 / (1 + p))
  suffices hle : Real.logb 2 (1 + p) ≤ B by dsimp only [B] at hle; linarith
  have hpoly : 0 ≤ (1 + p) ^ 2 * ((69313 / 100000 : ℝ) * B -
      (48567 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3))) := by
    have hid : (1 + p) ^ 2 * ((69313 / 100000 : ℝ) * B -
        (48567 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3))) =
        (5124091767 / 43940000000 : ℝ) * v ^ 5 +
        (103488355329 / 219700000000 : ℝ) * u * v ^ 4 +
        (3148081295223 / 4394000000000 : ℝ) * u ^ 2 * v ^ 3 +
        (2234602037211 / 4394000000000 : ℝ) * u ^ 3 * v ^ 2 +
        (468040732311 / 2746250000000 : ℝ) * u ^ 4 * v +
        (130196324787 / 5492500000000 : ℝ) * u ^ 5 := by
      have hne : 1 + p ≠ 0 := by linarith
      dsimp only [B, treePot, t]
      field_simp [hne]
      rw [hp_eq, hv_eq]
      ring
    rw [hid]
    positivity
  have hrat : 48567 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3) ≤ (69313 / 100000 : ℝ) * B := by
    linarith [nonneg_of_mul_nonneg_right hpoly (by positivity : 0 < (1 + p) ^ 2)]
  have hU_pos : 0 ≤ 48567 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3) := by
    dsimp only [t]; nlinarith [sq_nonneg t]
  exact logb_two_le_of_log_le (by linarith) (log_one_add_le_thirteen_eighths hp1) hrat

/-- Two-variable AM-GM lower bound `2 * treePot (√(p₁ * p₂)) ≤ treePot p₁ + treePot p₂`. -/
private theorem two_mul_treePot_sqrt_le {p₁ p₂ : ℝ} (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) :
    2 * treePot (Real.sqrt (p₁ * p₂)) ≤ treePot p₁ + treePot p₂ := by
  set s₁ := Real.sqrt p₁
  set s₂ := Real.sqrt p₂
  have hid : treePot p₁ + treePot p₂ - 2 * treePot (s₁ * s₂) =
      (1 / 10 : ℝ) * (s₁ - s₂) ^ 2 + (3 / 10 : ℝ) * (p₁ - p₂) ^ 2 := by
    unfold treePot
    rw [← Real.sq_sqrt h1, ← Real.sq_sqrt h2]
    ring
  rw [Real.sqrt_mul h1 p₂]
  have hpos : 0 ≤ (1 / 10 : ℝ) * (s₁ - s₂) ^ 2 + (3 / 10 : ℝ) * (p₁ - p₂) ^ 2 := by positivity
  linarith

/-- `2`-child inductive step on `[1 / 2, 4 / 5]²`. -/
private theorem step_two_children {p₁ p₂ : ℝ} (h1lo : 1 / 2 ≤ p₁) (h1hi : p₁ ≤ 4 / 5)
    (h2lo : 1 / 2 ≤ p₂) (h2hi : p₂ ≤ 4 / 5) :
    Real.logb 2 (1 + p₁ * p₂) + treePot (1 / (1 + p₁ * p₂)) - treePot p₁ - treePot p₂ ≤
      1 - 2 * (53 / 200) := by
  obtain ⟨hq_sq, hq_lo, hq_hi⟩ := sqrt_mul_bounds h1lo h1hi h2lo h2hi
  have hamgm := two_mul_treePot_sqrt_le (by linarith : 0 ≤ p₁) (by linarith : 0 ≤ p₂)
  set q : ℝ := Real.sqrt (p₁ * p₂)
  suffices h1d : Real.logb 2 (1 + q ^ 2) + treePot (1 / (1 + q ^ 2)) - 2 * treePot q ≤
      1 - 2 * (53 / 200) by
    rw [hq_sq] at h1d
    linarith
  obtain ⟨u, v, hu, hv, hq_eq, hv_eq⟩ := exists_barycentric_coords hq_lo hq_hi
  set t : ℝ := (2 * q ^ 2 - 1) / 3
  set B : ℝ := (1 - 2 * (53 / 200)) + 2 * treePot q - treePot (1 / (1 + q ^ 2))
  suffices hle : Real.logb 2 (1 + q ^ 2) ≤ B by dsimp only [B] at hle; linarith
  have hpoly : 0 ≤ (1 + q ^ 2) ^ 2 * ((69313 / 100000 : ℝ) * B -
      (40561 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3))) := by
    have hid : (1 + q ^ 2) ^ 2 * ((69313 / 100000 : ℝ) * B -
        (40561 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3))) =
        (2995019 / 5184000000 : ℝ) * v ^ 10 +
        (172617173 / 12960000000 : ℝ) * u * v ^ 9 +
        (5825330383 / 72000000000 : ℝ) * u ^ 2 * v ^ 8 +
        (64692624863 / 270000000000 : ℝ) * u ^ 3 * v ^ 7 +
        (2238446632999 / 5400000000000 : ℝ) * u ^ 4 * v ^ 6 +
        (410196728809 / 900000000000 : ℝ) * u ^ 5 * v ^ 5 +
        (9191648921099 / 27000000000000 : ℝ) * u ^ 6 * v ^ 4 +
        (9998451883 / 52734375000 : ℝ) * u ^ 7 * v ^ 3 +
        (96435883381 / 1125000000000 : ℝ) * u ^ 8 * v ^ 2 +
        (72383957539 / 2531250000000 : ℝ) * u ^ 9 * v +
        (23930510177 / 5062500000000 : ℝ) * u ^ 10 := by
      have hne : 1 + q ^ 2 ≠ 0 := by positivity
      dsimp only [B, treePot, t]
      field_simp [hne]
      rw [hq_eq, hv_eq]
      ring
    rw [hid]
    positivity
  have hrat : 40561 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3) ≤ (69313 / 100000 : ℝ) * B := by
    linarith [nonneg_of_mul_nonneg_right hpoly (by positivity : 0 < (1 + q ^ 2) ^ 2)]
  have hU_pos : 0 ≤ 40561 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3) := by
    dsimp only [t]; nlinarith [sq_nonneg t]
  exact logb_two_le_of_log_le (by linarith) log_one_add_sq_le_three_halves hrat

/-- `1`-child active-root bound on `[1 / 2, 4 / 5]`. -/
private theorem root_one_child {p : ℝ} (hp1 : 1 / 2 ≤ p) (hp2 : p ≤ 4 / 5) :
    Real.logb 2 (1 + p) - treePot p ≤ 1 - 53 / 200 - 33 / 1000 := by
  obtain ⟨u, v, hu, hv, hp_eq, hv_eq⟩ := exists_barycentric_coords hp1 hp2
  set t : ℝ := (8 * p - 5) / 13
  set B : ℝ := (1 - 53 / 200 - 33 / 1000) + treePot p
  suffices hle : Real.logb 2 (1 + p) ≤ B by dsimp only [B] at hle; linarith
  have hrat : 48567 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3) ≤ (69313 / 100000 : ℝ) * B := by
    have hid : (69313 / 100000 : ℝ) * B - (48567 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3)) =
        (26673987533 / 329550000000 : ℝ) * v ^ 3 +
        (13850827193 / 109850000000 : ℝ) * u * v ^ 2 +
        (10486911553 / 219700000000 : ℝ) * u ^ 2 * v +
        (321346567 / 659100000000 : ℝ) * u ^ 3 := by
      dsimp only [B, treePot, t]
      rw [hp_eq, hv_eq]
      ring
    have hpos : 0 ≤ (69313 / 100000 : ℝ) * B - (48567 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3)) := by
      rw [hid]; positivity
    linarith
  exact logb_two_le_of_log_le (by dsimp only [B, treePot]; nlinarith)
    (log_one_add_le_thirteen_eighths hp1) hrat

/-- `2`-child active-root bound on `[1 / 2, 4 / 5]²`. -/
private theorem root_two_children {p₁ p₂ : ℝ} (h1lo : 1 / 2 ≤ p₁) (h1hi : p₁ ≤ 4 / 5)
    (h2lo : 1 / 2 ≤ p₂) (h2hi : p₂ ≤ 4 / 5) :
    Real.logb 2 (1 + p₁ * p₂) - treePot p₁ - treePot p₂ ≤ 1 - 2 * (53 / 200) - 33 / 1000 := by
  obtain ⟨hq_sq, hq_lo, hq_hi⟩ := sqrt_mul_bounds h1lo h1hi h2lo h2hi
  have hamgm := two_mul_treePot_sqrt_le (by linarith : 0 ≤ p₁) (by linarith : 0 ≤ p₂)
  set q : ℝ := Real.sqrt (p₁ * p₂)
  suffices h1d : Real.logb 2 (1 + q ^ 2) - 2 * treePot q ≤ 1 - 2 * (53 / 200) - 33 / 1000 by
    rw [hq_sq] at h1d
    linarith
  obtain ⟨u, v, hu, hv, hq_eq, hv_eq⟩ := exists_barycentric_coords hq_lo hq_hi
  set t : ℝ := (2 * q ^ 2 - 1) / 3
  set B : ℝ := (1 - 2 * (53 / 200) - 33 / 1000) + 2 * treePot q
  suffices hle : Real.logb 2 (1 + q ^ 2) ≤ B by dsimp only [B] at hle; linarith
  have hrat : 40561 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3) ≤ (69313 / 100000 : ℝ) * B := by
    have hid : (69313 / 100000 : ℝ) * B - (40561 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3)) =
        (643031261 / 8100000000 : ℝ) * v ^ 6 +
        (545105381 / 1350000000 : ℝ) * u * v ^ 5 +
        (2215455859 / 2700000000 : ℝ) * u ^ 2 * v ^ 4 +
        (1711943167 / 2025000000 : ℝ) * u ^ 3 * v ^ 3 +
        (1241988829 / 2700000000 : ℝ) * u ^ 4 * v ^ 2 +
        (165546569 / 1350000000 : ℝ) * u ^ 5 * v +
        (95735843 / 8100000000 : ℝ) * u ^ 6 := by
      dsimp only [B, treePot, t]
      rw [hq_eq, hv_eq]
      ring
    have hpos : 0 ≤ (69313 / 100000 : ℝ) * B - (40561 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3)) := by
      rw [hid]; positivity
    linarith
  exact logb_two_le_of_log_le (by dsimp only [B, treePot]; nlinarith)
    log_one_add_sq_le_three_halves hrat

/-- `3`-child active-root bound on `[1 / 2, 4 / 5]³` via `q = exp((log p₁ + log p₂ + log p₃)/3)`. -/
private theorem root_three_children {p₁ p₂ p₃ : ℝ} (h1lo : 1 / 2 ≤ p₁) (h1hi : p₁ ≤ 4 / 5)
    (h2lo : 1 / 2 ≤ p₂) (h2hi : p₂ ≤ 4 / 5) (h3lo : 1 / 2 ≤ p₃) (h3hi : p₃ ≤ 4 / 5) :
    Real.logb 2 (1 + p₁ * p₂ * p₃) - treePot p₁ - treePot p₂ - treePot p₃ ≤
      1 - 3 * (53 / 200) - 33 / 1000 := by
  let cbrt : ℝ → ℝ := fun p => Real.exp (Real.log p / 3)
  have hcbrt_pos : ∀ p : ℝ, 0 < cbrt p := fun p => Real.exp_pos _
  have hcbrt_pow : ∀ {p : ℝ}, 0 < p → cbrt p ^ 3 = p := by
    intro p hp
    dsimp only [cbrt]
    rw [← Real.exp_natCast_mul]
    have h3 : (3 : ℕ) * (Real.log p / 3) = Real.log p := by push_cast; ring
    rw [h3, Real.exp_log hp]
  set x₁ := cbrt p₁
  set x₂ := cbrt p₂
  set x₃ := cbrt p₃
  have hx1_pos : 0 < x₁ := hcbrt_pos p₁
  have hx2_pos : 0 < x₂ := hcbrt_pos p₂
  have hx3_pos : 0 < x₃ := hcbrt_pos p₃
  have hx1 : x₁ ^ 3 = p₁ := hcbrt_pow (by linarith)
  have hx2 : x₂ ^ 3 = p₂ := hcbrt_pow (by linarith)
  have hx3 : x₃ ^ 3 = p₃ := hcbrt_pow (by linarith)
  set q : ℝ := x₁ * x₂ * x₃
  have hq_pos : 0 < q := by positivity
  have hq_cb : q ^ 3 = p₁ * p₂ * p₃ := by
    dsimp only [q]
    calc (x₁ * x₂ * x₃) ^ 3 = x₁ ^ 3 * x₂ ^ 3 * x₃ ^ 3 := by ring
      _ = p₁ * p₂ * p₃ := by rw [hx1, hx2, hx3]
  have hq_lo : 1 / 2 ≤ q := by
    by_contra! hlt
    have hcb : q ^ 3 < (1 / 2 : ℝ) ^ 3 := pow_lt_pow_left₀ hlt hq_pos.le (by decide)
    have hprod := mul_le_mul (mul_le_mul h1lo h2lo (by norm_num) (by linarith)) h3lo
      (by norm_num) (by positivity)
    linarith
  have hq_hi : q ≤ 4 / 5 := by
    by_contra! hgt
    have hcb : (4 / 5 : ℝ) ^ 3 < q ^ 3 := pow_lt_pow_left₀ hgt (by norm_num) (by decide)
    have hprod := mul_le_mul (mul_le_mul h1hi h2hi (by linarith) (by norm_num)) h3hi
      (by positivity) (by norm_num)
    linarith
  have hamgm : 3 * treePot q ≤ treePot p₁ + treePot p₂ + treePot p₃ := by
    have hid : treePot p₁ + treePot p₂ + treePot p₃ - 3 * treePot q =
        (1 / 20 : ℝ) * (x₁ + x₂ + x₃) * ((x₁ - x₂) ^ 2 + (x₂ - x₃) ^ 2 + (x₃ - x₁) ^ 2) +
        (3 / 20 : ℝ) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) *
          ((x₁ ^ 2 - x₂ ^ 2) ^ 2 + (x₂ ^ 2 - x₃ ^ 2) ^ 2 + (x₃ ^ 2 - x₁ ^ 2) ^ 2) := by
      unfold treePot
      dsimp only [q]
      rw [← hx1, ← hx2, ← hx3]
      ring
    have hpos : 0 ≤ (1 / 20 : ℝ) * (x₁ + x₂ + x₃) *
        ((x₁ - x₂) ^ 2 + (x₂ - x₃) ^ 2 + (x₃ - x₁) ^ 2) +
        (3 / 20 : ℝ) * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) *
          ((x₁ ^ 2 - x₂ ^ 2) ^ 2 + (x₂ ^ 2 - x₃ ^ 2) ^ 2 + (x₃ ^ 2 - x₁ ^ 2) ^ 2) := by
      positivity
    linarith
  suffices h1d : Real.logb 2 (1 + q ^ 3) - 3 * treePot q ≤ 1 - 3 * (53 / 200) - 33 / 1000 by
    rw [hq_cb] at h1d
    linarith
  obtain ⟨u, v, hu, hv, hq_eq, hv_eq⟩ := exists_barycentric_coords hq_lo hq_hi
  set t : ℝ := (4 * q ^ 3 - 1) / 5
  have hlog : Real.log (1 + q ^ 3) ≤ 22324 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3) := by
    have hsplit : 1 + q ^ 3 = (5 / 4) * (1 + t) := by dsimp only [t]; ring
    have ht_gt : -1 < t := by
      have : 0 < q ^ 3 := by positivity
      dsimp only [t]
      linarith
    rw [hsplit, Real.log_mul (by norm_num) (by linarith)]
    linarith [log_five_div_four_le, log_one_add_le_cubic ht_gt]
  set B : ℝ := (1 - 3 * (53 / 200) - 33 / 1000) + 3 * treePot q
  suffices hle : Real.logb 2 (1 + q ^ 3) ≤ B by dsimp only [B] at hle; linarith
  have hrat : 22324 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3) ≤ (69313 / 100000 : ℝ) * B := by
    have hid : (69313 / 100000 : ℝ) * B - (22324 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3)) =
        (98377 / 75000000 : ℝ) * v ^ 9 +
        (1538301 / 25000000 : ℝ) * u * v ^ 8 +
        (40073889 / 100000000 : ℝ) * u ^ 2 * v ^ 7 +
        (23797307 / 20000000 : ℝ) * u ^ 3 * v ^ 6 +
        (201236109 / 100000000 : ℝ) * u ^ 4 * v ^ 5 +
        (209771691 / 100000000 : ℝ) * u ^ 5 * v ^ 4 +
        (686667407 / 500000000 : ℝ) * u ^ 6 * v ^ 3 +
        (1372095597 / 2500000000 : ℝ) * u ^ 7 * v ^ 2 +
        (1514434839 / 12500000000 : ℝ) * u ^ 8 * v +
        (2052258079 / 187500000000 : ℝ) * u ^ 9 := by
      dsimp only [B, treePot, t]
      rw [hq_eq, hv_eq]
      ring
    have hpos : 0 ≤ (69313 / 100000 : ℝ) * B - (22324 / 100000 + (t - t ^ 2 / 2 + t ^ 3 / 3)) := by
      rw [hid]; positivity
    linarith
  have hB_pos : 0 ≤ B := by dsimp only [B, treePot]; nlinarith
  exact logb_two_le_of_log_le hB_pos hlog hrat

/-! ### Independent-set factorization and Tree-DP on finite out-forests -/

/-- Active roots of `B`: vertices with in-degree `0` and out-degree at least `1`. -/
@[expose] def arborescenceActiveRoots (B : Digraph V) : Set V :=
  {r | (¬∃ u, B.Adj u r) ∧ ∃ v, B.Adj r v}

open Classical in
/-- Total outgoing arcs after capping internal vertices (`∃ u, B.Adj u w`) at `2` and roots at
`3`. -/
@[expose] noncomputable def arborescenceCappedEdges (B : Digraph V) : ℕ :=
  ∑ᶠ w : V, min {v | B.Adj w v}.ncard (if ∃ u, B.Adj u w then 2 else 3)

section TreeDP

private def indepPowerset (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Finset V) :=
  S.powerset.filter fun I => ∀ x ∈ I, ∀ y ∈ I, ¬G.Adj x y

private theorem card_indepPowerset_univ [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (indepPowerset G Finset.univ).card = G.indepSetCount := by
  classical
  have himg : (fun I : Finset V => (I : Set V)) '' (indepPowerset G Finset.univ : Set (Finset V)) =
      {s : Set V | G.IsIndepSet s} := by
    ext s
    simp only [mem_image, Finset.mem_coe, indepPowerset, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and, mem_ofPred_eq]
    constructor
    · rintro ⟨I, hI, rfl⟩ u hu w hw _ hadj
      exact hI u hu w hw hadj
    · intro hs
      refine ⟨s.toFinset, fun x hx y hy hadj => ?_, s.coe_toFinset⟩
      rw [mem_toFinset] at hx hy
      exact hs hx hy (G.ne_of_adj hadj) hadj
  rw [indepSetCount, ← himg, ncard_image_of_injective _ Finset.coe_injective, ncard_coe_finset]

private theorem card_indepPowerset_union [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} (hdisj : Disjoint A B) (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬G.Adj x y) :
    (indepPowerset G (A ∪ B)).card = (indepPowerset G A).card * (indepPowerset G B).card := by
  rw [← Finset.card_product]
  refine (Finset.card_bij (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_).symm
  · rintro ⟨I₁, I₂⟩ hp
    rw [Finset.mem_product] at hp
    simp only [indepPowerset, Finset.mem_filter, Finset.mem_powerset] at hp ⊢
    refine ⟨Finset.union_subset (hp.1.1.trans Finset.subset_union_left)
      (hp.2.1.trans Finset.subset_union_right), fun x hx y hy hadj => ?_⟩
    rcases Finset.mem_union.mp hx with hx1 | hx2 <;> rcases Finset.mem_union.mp hy with hy1 | hy2
    · exact hp.1.2 x hx1 y hy1 hadj
    · exact hcross x (hp.1.1 hx1) y (hp.2.1 hy2) hadj
    · exact hcross y (hp.1.1 hy1) x (hp.2.1 hx2) hadj.symm
    · exact hp.2.2 x hx2 y hy2 hadj
  · rintro ⟨I₁, I₂⟩ hp ⟨J₁, J₂⟩ hq heq
    rw [Finset.mem_product] at hp hq
    simp only [indepPowerset, Finset.mem_filter, Finset.mem_powerset] at hp hq
    have hA : ∀ K₁ K₂, K₁ ⊆ A → K₂ ⊆ B → (K₁ ∪ K₂) ∩ A = K₁ := fun K₁ K₂ h1 h2 => by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      exact ⟨fun ⟨hx, hxA⟩ => hx.resolve_right fun hx2 =>
        Finset.disjoint_left.mp hdisj hxA (h2 hx2), fun hx1 => ⟨Or.inl hx1, h1 hx1⟩⟩
    have hB : ∀ K₁ K₂, K₁ ⊆ A → K₂ ⊆ B → (K₁ ∪ K₂) ∩ B = K₂ := fun K₁ K₂ h1 h2 => by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      exact ⟨fun ⟨hx, hxB⟩ => hx.resolve_left fun hx1 =>
        Finset.disjoint_left.mp hdisj (h1 hx1) hxB, fun hx2 => ⟨Or.inr hx2, h2 hx2⟩⟩
    have h1 : I₁ = J₁ := by
      rw [← hA I₁ I₂ hp.1.1 hp.2.1, heq, hA J₁ J₂ hq.1.1 hq.2.1]
    have h2 : I₂ = J₂ := by
      rw [← hB I₁ I₂ hp.1.1 hp.2.1, heq, hB J₁ J₂ hq.1.1 hq.2.1]
    exact Prod.ext h1 h2
  · intro I hI
    simp only [indepPowerset, Finset.mem_filter, Finset.mem_powerset] at hI
    refine ⟨(I ∩ A, I ∩ B), ?_, ?_⟩
    · rw [Finset.mem_product]
      simp only [indepPowerset, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨⟨Finset.inter_subset_right, fun x hx y hy =>
        hI.2 x (Finset.mem_of_mem_inter_left hx) y (Finset.mem_of_mem_inter_left hy)⟩,
        ⟨Finset.inter_subset_right, fun x hx y hy =>
        hI.2 x (Finset.mem_of_mem_inter_left hx) y (Finset.mem_of_mem_inter_left hy)⟩⟩
    · rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hI.1]

private theorem card_indepPowerset_biUnion {ι : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : Finset ι) (f : ι → Finset V)
    (hdisj : (s : Set ι).PairwiseDisjoint f)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ f i, ∀ y ∈ f j, ¬G.Adj x y) :
    (indepPowerset G (s.biUnion f)).card = ∏ i ∈ s, (indepPowerset G (f i)).card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [indepPowerset, Finset.filter_singleton]
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.prod_insert ha]
    have hd : Disjoint (f a) (s.biUnion f) := by
      rw [Finset.disjoint_biUnion_right]
      intro b hb
      exact hdisj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb)
        (fun h => ha (h ▸ hb))
    have hc : ∀ x ∈ f a, ∀ y ∈ s.biUnion f, ¬G.Adj x y := by
      intro x hx y hy
      obtain ⟨b, hb, hyb⟩ := Finset.mem_biUnion.mp hy
      exact hcross a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
        (fun h => ha (h ▸ hb)) x hx y hyb
    rw [card_indepPowerset_union hd hc,
      ih (hdisj.subset (Finset.subset_insert a s))
        (fun i hi j hj hij => hcross i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij)]

/-! #### Directed reachability and subtree decomposition -/

private theorem rk_lt_of_transGen {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w)
    {u w : V} (h : Relation.TransGen arc u w) : rk u < rk w := by
  induction h with
  | single h1 => exact hrank h1
  | tail _ h2 ih => exact ih.trans (hrank h2)

private theorem rk_le_of_reflTransGen {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w)
    {u w : V} (h : Relation.ReflTransGen arc u w) : rk u ≤ rk w := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | htr
  · exact le_rfl
  · exact (rk_lt_of_transGen hrank htr).le

private theorem reaches_comparable {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w)
    (hin : ∀ w, {u | arc u w}.Subsingleton) {u v z : V}
    (hu : Relation.ReflTransGen arc u z) (hv : Relation.ReflTransGen arc v z) :
    Relation.ReflTransGen arc u v ∨ Relation.ReflTransGen arc v u := by
  have hmain : ∀ n : ℕ, ∀ z : V, rk z = n →
      Relation.ReflTransGen arc u z → Relation.ReflTransGen arc v z →
      Relation.ReflTransGen arc u v ∨ Relation.ReflTransGen arc v u := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro z hzn huz hvz
      rcases huz.cases_tail with rfl | ⟨w₁, huw₁, hw₁z⟩
      · exact Or.inr hvz
      · rcases hvz.cases_tail with rfl | ⟨w₂, hvw₂, hw₂z⟩
        · exact Or.inl huz
        · cases hin z hw₁z hw₂z
          exact ih (rk w₁) (hzn ▸ hrank hw₁z) w₁ rfl huw₁ hvw₂
  exact hmain (rk z) z rfl hu hv

private theorem subtree_disjoint_children {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w)
    (hin : ∀ w, {u | arc u w}.Subsingleton) {u v₁ v₂ : V}
    (hv₁ : arc u v₁) (hv₂ : arc u v₂) (hne : v₁ ≠ v₂) :
    Disjoint {z | Relation.ReflTransGen arc v₁ z} {z | Relation.ReflTransGen arc v₂ z} := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  rcases reaches_comparable hrank hin hz1 hz2 with h12 | h21
  · rcases h12.cases_tail with heq | ⟨w, hvw, hwv₂⟩
    · exact hne heq.symm
    · cases hin v₂ hwv₂ hv₂
      exact absurd (rk_le_of_reflTransGen hrank hvw) (not_le_of_gt (hrank hv₁))
  · rcases h21.cases_tail with heq | ⟨w, hvw, hwv₁⟩
    · exact hne heq
    · cases hin v₁ hwv₁ hv₁
      exact absurd (rk_le_of_reflTransGen hrank hvw) (not_le_of_gt (hrank hv₂))

private theorem subtree_disjoint_roots {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w)
    (hin : ∀ w, {u | arc u w}.Subsingleton) {r₁ r₂ : V}
    (hr₁ : ¬∃ u, arc u r₁) (hr₂ : ¬∃ u, arc u r₂) (hne : r₁ ≠ r₂) :
    Disjoint {z | Relation.ReflTransGen arc r₁ z} {z | Relation.ReflTransGen arc r₂ z} := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  rcases reaches_comparable hrank hin hz1 hz2 with h12 | h21
  · rcases h12.cases_tail with heq | ⟨w, -, hwr₂⟩
    · exact hne heq.symm
    · exact hr₂ ⟨w, hwr₂⟩
  · rcases h21.cases_tail with heq | ⟨w, -, hwr₁⟩
    · exact hne heq
    · exact hr₁ ⟨w, hwr₁⟩

private theorem exists_root_reaches {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w)
    (z : V) : ∃ r : V, (¬∃ u, arc u r) ∧ Relation.ReflTransGen arc r z := by
  suffices ∀ n : ℕ, ∀ w : V, rk w = n →
      ∃ r : V, (¬∃ u, arc u r) ∧ Relation.ReflTransGen arc r w from this (rk z) z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro w hwn
    by_cases h : ∃ u, arc u w
    · obtain ⟨u, huw⟩ := h
      obtain ⟨r, hr, hru⟩ := ih (rk u) (hwn ▸ hrank huw) u rfl
      exact ⟨r, hr, hru.tail huw⟩
    · exact ⟨w, h, .refl⟩

section ArcSubtree

open Classical in
/-- Out-neighbors of `u` along `arc` as a `Finset`. -/
private noncomputable def arcKids [Fintype V] (arc : V → V → Prop) (u : V) : Finset V :=
  Finset.univ.filter (arc u ·)

open Classical in
/-- Vertices reachable from `u` along zero or more `arc`-steps as a `Finset`. -/
private noncomputable def arcSubtree [Fintype V] (arc : V → V → Prop) (u : V) : Finset V :=
  Finset.univ.filter (Relation.ReflTransGen arc u ·)

open Classical in
/-- Number of independent sets in the subtree rooted at `u`. -/
private noncomputable def subIndepCount [Fintype V] (arc : V → V → Prop) (u : V) : ℕ :=
  (indepPowerset (SimpleGraph.fromRel arc) (arcSubtree arc u)).card

open Classical in
/-- Number of independent sets on the vertices reachable from a child of `u`.
When a rank strictly increases along each arc, these are exactly the independent sets on the
subtree of `u` that omit `u`. -/
private noncomputable def subUnchosenCount [Fintype V] (arc : V → V → Prop) (u : V) : ℕ :=
  (indepPowerset (SimpleGraph.fromRel arc) ((arcKids arc u).biUnion (arcSubtree arc))).card

/-- Total outgoing `arc`-edges summed over the subtree rooted at `u`. -/
private noncomputable def subEdges [Fintype V] (arc : V → V → Prop) (u : V) : ℕ :=
  ∑ w ∈ arcSubtree arc u, (arcKids arc w).card

/-- Ratio of the independent-set count on the union of the child subtrees to the count on
the subtree of `u`. Under a strictly increasing rank it is the fraction of sets omitting `u`. -/
private noncomputable def subRootRatio [Fintype V] (arc : V → V → Prop) (u : V) : ℝ :=
  (subUnchosenCount arc u : ℝ) / (subIndepCount arc u : ℝ)

/-- Distinct children of `u` have pairwise disjoint subtrees. -/
private theorem arcSubtree_pairwiseDisjoint_kids [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton) (u : V) :
    (arcKids arc u : Set V).PairwiseDisjoint (arcSubtree arc) := by
  classical
  intro v₁ hv₁ v₂ hv₂ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro z hz1 hz2
  simp only [arcSubtree, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
  simp only [Finset.mem_coe, arcKids, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
  exact Set.disjoint_left.mp (subtree_disjoint_children hrank hin hv₁ hv₂ hne) hz1 hz2

/-- Disjoint subtrees carry no undirected `SimpleGraph.fromRel arc` edge between them. -/
private theorem no_adj_of_disjoint_arcSubtree [Fintype V] {arc : V → V → Prop} {v₁ v₂ : V}
    (hd : Disjoint (arcSubtree arc v₁) (arcSubtree arc v₂))
    {x y : V} (hx : x ∈ arcSubtree arc v₁) (hy : y ∈ arcSubtree arc v₂) :
    ¬(SimpleGraph.fromRel arc).Adj x y := by
  classical
  intro hadj
  simp only [arcSubtree, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  rw [fromRel_adj] at hadj
  rcases hadj.2 with hxy | hyx
  · exact Finset.disjoint_left.mp hd
      (show y ∈ arcSubtree arc v₁ by simp [arcSubtree, hx.tail hxy])
      (show y ∈ arcSubtree arc v₂ by simp [arcSubtree, hy])
  · exact Finset.disjoint_left.mp hd
      (show x ∈ arcSubtree arc v₁ by simp [arcSubtree, hx])
      (show x ∈ arcSubtree arc v₂ by simp [arcSubtree, hy.tail hyx])

open Classical in
/-- No vertex lies inside the union of its own children's subtrees. -/
private theorem notMem_biUnion_arcSubtree_kids [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (u : V) :
    u ∉ (arcKids arc u).biUnion (arcSubtree arc) := by
  intro hmem
  obtain ⟨v, hv, huv⟩ := Finset.mem_biUnion.mp hmem
  simp only [arcKids, arcSubtree, Finset.mem_filter, Finset.mem_univ, true_and] at hv huv
  exact absurd (rk_le_of_reflTransGen hrank huv) (not_le_of_gt (hrank hv))

open Classical in
/-- Subtree decomposition: `arcSubtree arc u` is `u` inserted into the union of child subtrees. -/
private theorem arcSubtree_eq_insert_biUnion [Fintype V] (arc : V → V → Prop) (u : V) :
    arcSubtree arc u = insert u ((arcKids arc u).biUnion (arcSubtree arc)) := by
  ext z
  simp only [arcSubtree, arcKids, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_biUnion]
  constructor
  · intro huz
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp huz with rfl | htr
    · exact Or.inl rfl
    · obtain ⟨v, huv, hvz⟩ := Relation.TransGen.head'_iff.mp htr
      exact Or.inr ⟨v, huv, hvz⟩
  · rintro (rfl | ⟨v, huv, hvz⟩)
    · exact .refl
    · exact hvz.head huv

open Classical in
/-- No vertex is adjacent in `SimpleGraph.fromRel arc` to a proper descendant of a child. -/
private theorem not_adj_grandchild [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton)
    {u v z : V} (hv : v ∈ arcKids arc u)
    (hz : z ∈ (arcKids arc v).biUnion (arcSubtree arc)) :
    ¬(SimpleGraph.fromRel arc).Adj u z := by
  intro hadj
  obtain ⟨w, hw, hwz⟩ := Finset.mem_biUnion.mp hz
  have hv_arc : arc u v := by simpa [arcKids] using hv
  simp only [arcKids, arcSubtree, Finset.mem_filter, Finset.mem_univ, true_and] at hw hwz
  rw [fromRel_adj] at hadj
  rcases hadj.2 with huz | hzu
  · have hz_kid : z ∈ arcKids arc u := by simp [arcKids, huz]
    have hz_sub_v : z ∈ arcSubtree arc v := by simp [arcSubtree, hwz.head hw]
    have hz_sub_z : z ∈ arcSubtree arc z := by simp [arcSubtree, Relation.ReflTransGen.refl]
    by_cases hvz : v = z
    · subst hvz
      exact absurd (rk_le_of_reflTransGen hrank hwz) (not_le_of_gt (hrank hw))
    · exact Finset.disjoint_left.mp
        (arcSubtree_pairwiseDisjoint_kids hrank hin u hv hz_kid hvz) hz_sub_v hz_sub_z
  · have hlt : rk u < rk z :=
      (hrank hv_arc).trans ((hrank hw).trans_le (rk_le_of_reflTransGen hrank hwz))
    exact absurd (hrank hzu) (not_lt_of_gt hlt)

/-- Independent sets omitting `u` factor as the product of child subtree counts. -/
private theorem subUnchosenCount_eq_prod [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton) (u : V) :
    subUnchosenCount arc u = ∏ v ∈ arcKids arc u, subIndepCount arc v := by
  classical
  exact card_indepPowerset_biUnion (arcKids arc u) (arcSubtree arc)
    (arcSubtree_pairwiseDisjoint_kids hrank hin u)
    fun _ hv₁ _ hv₂ hne _ hx _ hy =>
      no_adj_of_disjoint_arcSubtree
        (arcSubtree_pairwiseDisjoint_kids hrank hin u hv₁ hv₂ hne) hx hy

open Classical in
/-- Independent sets in `arcSubtree arc u` containing `u` biject with independent sets in the
grandchild forest `⋃_{v ∈ kids u} (kids v).biUnion sub`. -/
private theorem card_indepPowerset_mem_root [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton) (u : V) :
    ((indepPowerset (SimpleGraph.fromRel arc)
        (insert u ((arcKids arc u).biUnion (arcSubtree arc)))).filter fun I => u ∈ I).card =
      ∏ v ∈ arcKids arc u, subUnchosenCount arc v := by
  let G := SimpleGraph.fromRel arc
  let grand : V → Finset V := fun v => (arcKids arc v).biUnion (arcSubtree arc)
  have hgrand_sub (v : V) : grand v ⊆ arcSubtree arc v := by
    intro z hz
    rw [arcSubtree_eq_insert_biUnion]
    exact Finset.mem_insert_of_mem hz
  have hdisj_G : (arcKids arc u : Set V).PairwiseDisjoint grand := fun v₁ hv₁ v₂ hv₂ hne =>
    Disjoint.mono (hgrand_sub v₁) (hgrand_sub v₂)
      (arcSubtree_pairwiseDisjoint_kids hrank hin u hv₁ hv₂ hne)
  have hcross_G : ∀ v₁ ∈ arcKids arc u, ∀ v₂ ∈ arcKids arc u, v₁ ≠ v₂ →
      ∀ x ∈ grand v₁, ∀ y ∈ grand v₂, ¬G.Adj x y := fun v₁ hv₁ v₂ hv₂ hne _ hx _ hy =>
    no_adj_of_disjoint_arcSubtree (arcSubtree_pairwiseDisjoint_kids hrank hin u hv₁ hv₂ hne)
      (hgrand_sub v₁ hx) (hgrand_sub v₂ hy)
  have hGsub_B : (arcKids arc u).biUnion grand ⊆ (arcKids arc u).biUnion (arcSubtree arc) :=
    fun z hz => by
      obtain ⟨v, hv, hzv⟩ := Finset.mem_biUnion.mp hz
      exact Finset.mem_biUnion.mpr ⟨v, hv, hgrand_sub v hzv⟩
  change _ = ∏ v ∈ arcKids arc u, (indepPowerset G (grand v)).card
  rw [← card_indepPowerset_biUnion (arcKids arc u) grand hdisj_G hcross_G]
  refine Finset.card_bij (fun I _ => I.erase u) ?_ ?_ ?_
  · intro I hI
    simp only [indepPowerset, Finset.mem_filter, Finset.mem_powerset] at hI ⊢
    obtain ⟨⟨hIsub, hIind⟩, huI⟩ := hI
    refine ⟨fun z hz => ?_, fun x hx y hy =>
      hIind x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)⟩
    obtain ⟨v, hv, hzv⟩ := Finset.mem_biUnion.mp ((Finset.subset_insert_iff.mp hIsub) hz)
    rw [arcSubtree_eq_insert_biUnion] at hzv
    rcases Finset.mem_insert.mp hzv with rfl | hz_grand
    · have hvk : arc u z := by simpa [arcKids] using hv
      have huv : G.Adj u z := by
        rw [fromRel_adj]
        exact ⟨fun h => (hrank hvk).ne (congrArg rk h), Or.inl hvk⟩
      exact False.elim (hIind u huI z (Finset.mem_of_mem_erase hz) huv)
    · exact Finset.mem_biUnion.mpr ⟨v, hv, hz_grand⟩
  · intro I₁ h1 I₂ h2 heq
    rw [← Finset.insert_erase (Finset.mem_filter.mp h1).2,
      ← Finset.insert_erase (Finset.mem_filter.mp h2).2, heq]
  · intro J hJ
    simp only [indepPowerset, Finset.mem_filter, Finset.mem_powerset] at hJ
    have huJ : u ∉ J := fun huJ => notMem_biUnion_arcSubtree_kids hrank u (hGsub_B (hJ.1 huJ))
    refine ⟨insert u J, ?_, Finset.erase_insert huJ⟩
    simp only [indepPowerset, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨⟨Finset.insert_subset_insert u (hJ.1.trans hGsub_B), fun x hx y hy hadj => ?_⟩,
      Finset.mem_insert_self u J⟩
    rcases Finset.mem_insert.mp hx with rfl | hxJ <;>
      rcases Finset.mem_insert.mp hy with rfl | hyJ
    · exact G.ne_of_adj hadj rfl
    · obtain ⟨v, hv, hyv⟩ := Finset.mem_biUnion.mp (hJ.1 hyJ)
      exact not_adj_grandchild hrank hin hv hyv hadj
    · obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp (hJ.1 hxJ)
      exact not_adj_grandchild hrank hin hv hxv hadj.symm
    · exact hJ.2 x hxJ y hyJ hadj

/-- Tree-DP recurrence: `subIndepCount arc u = subUnchosenCount arc u + ∏ v ∈ kids u, i₀(v)`. -/
private theorem subIndepCount_eq [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton) (u : V) :
    subIndepCount arc u =
      subUnchosenCount arc u + ∏ v ∈ arcKids arc u, subUnchosenCount arc v := by
  classical
  unfold subIndepCount
  rw [arcSubtree_eq_insert_biUnion]
  set S := indepPowerset (SimpleGraph.fromRel arc)
    (insert u ((arcKids arc u).biUnion (arcSubtree arc)))
  rw [← Finset.card_filter_add_card_filter_not (s := S) (p := fun I => u ∉ I)]
  congr 1
  · refine congrArg Finset.card (Finset.ext fun I => ?_)
    simp only [S, indepPowerset, Finset.mem_filter, Finset.mem_powerset, Finset.subset_insert_iff]
    constructor
    · rintro ⟨⟨hsub, hind⟩, hnu⟩
      rw [Finset.erase_eq_of_notMem hnu] at hsub
      exact ⟨hsub, hind⟩
    · rintro ⟨hsub, hind⟩
      exact ⟨⟨(Finset.erase_subset u I).trans hsub, hind⟩,
        fun huI => notMem_biUnion_arcSubtree_kids hrank u (hsub huI)⟩
  · simpa only [not_not] using card_indepPowerset_mem_root hrank hin u

/-- Every subtree has at least one independent set (`∅`). -/
private theorem subIndepCount_pos [Fintype V] (arc : V → V → Prop) (u : V) :
    0 < subIndepCount arc u := by
  classical
  exact Finset.card_pos.mpr ⟨∅, by simp [indepPowerset]⟩

/-- Vertex-count recurrence for subtrees: `|sub u| = 1 + ∑ v ∈ kids u, |sub v|`. -/
private theorem card_arcSubtree_eq [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton) (u : V) :
    (arcSubtree arc u).card = 1 + ∑ v ∈ arcKids arc u, (arcSubtree arc v).card := by
  classical
  rw [arcSubtree_eq_insert_biUnion,
    Finset.card_insert_of_notMem (notMem_biUnion_arcSubtree_kids hrank u),
    Finset.card_biUnion (arcSubtree_pairwiseDisjoint_kids hrank hin u), Nat.add_comm]

/-- Edge-count recurrence for subtrees: `subEdges u = |kids u| + ∑ v ∈ kids u, subEdges v`. -/
private theorem subEdges_eq [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton) (u : V) :
    subEdges arc u = (arcKids arc u).card + ∑ v ∈ arcKids arc u, subEdges arc v := by
  classical
  dsimp only [subEdges]
  conv_lhs => rw [arcSubtree_eq_insert_biUnion]
  rw [Finset.sum_insert (notMem_biUnion_arcSubtree_kids hrank u),
    Finset.sum_biUnion (arcSubtree_pairwiseDisjoint_kids hrank hin u)]

/-- Real-valued factorization of `subIndepCount` via child ratios `subRootRatio`. -/
private theorem subIndepCount_cast_eq [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton) (u : V) :
    (subIndepCount arc u : ℝ) =
      (∏ v ∈ arcKids arc u, (subIndepCount arc v : ℝ)) *
        (1 + ∏ v ∈ arcKids arc u, subRootRatio arc v) := by
  have h1 : (subUnchosenCount arc u : ℝ) = ∏ v ∈ arcKids arc u, (subIndepCount arc v : ℝ) := by
    exact_mod_cast subUnchosenCount_eq_prod hrank hin u
  have h2 : (∏ v ∈ arcKids arc u, (subUnchosenCount arc v : ℝ)) =
      (∏ v ∈ arcKids arc u, (subIndepCount arc v : ℝ)) *
        (∏ v ∈ arcKids arc u, subRootRatio arc v) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hpos : (subIndepCount arc v : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (subIndepCount_pos arc v)).ne'
    dsimp only [subRootRatio]
    field_simp [hpos]
  have hcast : (subIndepCount arc u : ℝ) =
      (subUnchosenCount arc u : ℝ) + ∏ v ∈ arcKids arc u, (subUnchosenCount arc v : ℝ) := by
    exact_mod_cast subIndepCount_eq hrank hin u
  rw [hcast, h1, h2]
  ring

/-- Ratio recurrence `p(u) = 1 / (1 + ∏_{v ∈ kids u} p(v))`. -/
private theorem subRootRatio_eq [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton) (u : V) :
    subRootRatio arc u = 1 / (1 + ∏ v ∈ arcKids arc u, subRootRatio arc v) := by
  have h1 : (subUnchosenCount arc u : ℝ) = ∏ v ∈ arcKids arc u, (subIndepCount arc v : ℝ) := by
    exact_mod_cast subUnchosenCount_eq_prod hrank hin u
  have hne : (∏ v ∈ arcKids arc u, (subIndepCount arc v : ℝ)) ≠ 0 :=
    (Finset.prod_pos fun v _ => Nat.cast_pos.mpr (subIndepCount_pos arc v)).ne'
  dsimp only [subRootRatio]
  calc (subUnchosenCount arc u : ℝ) / (subIndepCount arc u : ℝ)
      = ((∏ v ∈ arcKids arc u, (subIndepCount arc v : ℝ)) * 1) /
          ((∏ v ∈ arcKids arc u, (subIndepCount arc v : ℝ)) *
            (1 + ∏ v ∈ arcKids arc u, subRootRatio arc v)) := by
        rw [h1, subIndepCount_cast_eq hrank hin u, mul_one]
    _ = 1 / (1 + ∏ v ∈ arcKids arc u, subRootRatio arc v) := mul_div_mul_left 1 _ hne

/-- Log-count recurrence `log₂ i(T_u) = ∑_{v ∈ kids u} log₂ i(T_v) + log₂ (1 + ∏ p(v))`. -/
private theorem logb_subIndepCount_eq [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton) (u : V) :
    Real.logb 2 (subIndepCount arc u : ℝ) =
      (∑ v ∈ arcKids arc u, Real.logb 2 (subIndepCount arc v : ℝ)) +
        Real.logb 2 (1 + ∏ v ∈ arcKids arc u, subRootRatio arc v) := by
  have hprod_ne : (∏ v ∈ arcKids arc u, (subIndepCount arc v : ℝ)) ≠ 0 :=
    (Finset.prod_pos fun v _ => Nat.cast_pos.mpr (subIndepCount_pos arc v)).ne'
  have h1p_ne : (1 + ∏ v ∈ arcKids arc u, subRootRatio arc v) ≠ 0 := by
    have : 0 ≤ ∏ v ∈ arcKids arc u, subRootRatio arc v :=
      Finset.prod_nonneg fun v _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  rw [subIndepCount_cast_eq hrank hin u, Real.logb_mul hprod_ne h1p_ne,
    Real.logb_prod _ _ fun v _ => (Nat.cast_pos.mpr (subIndepCount_pos arc v)).ne']

/-- When `s` has at most `2` elements with `p v ∈ [1 / 2, 4 / 5]`, the updated ratio
`1 / (1 + ∏ v ∈ s, p v)` remains in `[1 / 2, 4 / 5]`. -/
private theorem one_div_one_add_prod_mem_Icc {s : Finset V} {p : V → ℝ}
    (hs : s.card ≤ 2) (hp : ∀ v ∈ s, 1 / 2 ≤ p v ∧ p v ≤ 4 / 5) :
    1 / 2 ≤ 1 / (1 + ∏ v ∈ s, p v) ∧ 1 / (1 + ∏ v ∈ s, p v) ≤ 4 / 5 := by
  have hlo : (1 / 2 : ℝ) ^ s.card ≤ ∏ v ∈ s, p v := by
    simpa only [Finset.prod_const] using
      Finset.prod_le_prod₀ (fun _ _ => by norm_num) fun v hv => (hp v hv).1
  have hhi : ∏ v ∈ s, p v ≤ 1 :=
    Finset.prod_le_one₀ (fun v hv => by linarith [(hp v hv).1]) fun v hv =>
      by linarith [(hp v hv).2]
  have hpow : (1 / 2 : ℝ) ^ 2 ≤ (1 / 2 : ℝ) ^ s.card :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
  have hpos : 0 < 1 + ∏ v ∈ s, p v := by linarith
  exact ⟨(le_div_iff₀ hpos).mpr (by linarith), (div_le_iff₀ hpos).mpr (by linarith)⟩

/-- `Finset`-indexed internal-vertex potential step for `s.card ≤ 2`. -/
private theorem step_finset_le_two {s : Finset V} {p : V → ℝ}
    (hs : s.card ≤ 2) (hp : ∀ v ∈ s, 1 / 2 ≤ p v ∧ p v ≤ 4 / 5) :
    Real.logb 2 (1 + ∏ v ∈ s, p v) + treePot (1 / (1 + ∏ v ∈ s, p v)) -
        ∑ v ∈ s, treePot (p v) ≤
      1 - (53 / 200 : ℝ) * (s.card : ℝ) := by
  classical
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · obtain rfl := Finset.card_eq_zero.mp h0
    simp only [Finset.prod_empty, Finset.sum_empty, Finset.card_empty, Nat.cast_zero, mul_zero,
      sub_zero]
    rw [show (1 + 1 : ℝ) = 2 by norm_num, treePot_half, Real.logb_self_eq_one (by norm_num)]
    linarith
  · obtain ⟨v₁, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨hp1_lo, hp1_hi⟩ := hp v₁ (Finset.mem_singleton_self v₁)
    simpa using step_one_child hp1_lo hp1_hi
  · obtain ⟨v₁, v₂, hne, rfl⟩ := Finset.card_eq_two.mp h2
    obtain ⟨hp1_lo, hp1_hi⟩ := hp v₁ (Finset.mem_insert_self v₁ {v₂})
    obtain ⟨hp2_lo, hp2_hi⟩ := hp v₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self v₂))
    have hstep := step_two_children hp1_lo hp1_hi hp2_lo hp2_hi
    rw [Finset.prod_pair hne, Finset.sum_pair hne, Finset.card_pair hne]
    push_cast
    linarith

/-- `Finset`-indexed root potential step for `s.card ≤ 3`. -/
private theorem root_finset_le_three {s : Finset V} {p : V → ℝ}
    (hs : s.card ≤ 3) (hp : ∀ v ∈ s, 1 / 2 ≤ p v ∧ p v ≤ 4 / 5) :
    Real.logb 2 (1 + ∏ v ∈ s, p v) + (if s.Nonempty then (33 / 1000 : ℝ) else 0) -
        ∑ v ∈ s, treePot (p v) ≤
      1 - (53 / 200 : ℝ) * (s.card : ℝ) := by
  classical
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · obtain rfl := Finset.card_eq_zero.mp h0
    simp only [Finset.prod_empty, Finset.not_nonempty_empty, ↓reduceIte, Finset.sum_empty,
      Finset.card_empty, Nat.cast_zero, mul_zero, add_zero, sub_zero]
    rw [show (1 + 1 : ℝ) = 2 by norm_num, Real.logb_self_eq_one (by norm_num)]
  · obtain ⟨v₁, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨hp1_lo, hp1_hi⟩ := hp v₁ (Finset.mem_singleton_self v₁)
    have hstep := root_one_child hp1_lo hp1_hi
    simp only [Finset.prod_singleton, Finset.sum_singleton, Finset.card_singleton,
      Finset.singleton_nonempty, ↓reduceIte, Nat.cast_one]
    linarith
  · obtain ⟨v₁, v₂, hne, rfl⟩ := Finset.card_eq_two.mp h2
    obtain ⟨hp1_lo, hp1_hi⟩ := hp v₁ (Finset.mem_insert_self v₁ {v₂})
    obtain ⟨hp2_lo, hp2_hi⟩ := hp v₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self v₂))
    have hstep := root_two_children hp1_lo hp1_hi hp2_lo hp2_hi
    simp only [Finset.prod_pair hne, Finset.sum_pair hne, Finset.card_pair hne,
      Finset.insert_nonempty, ↓reduceIte]
    push_cast
    linarith
  · obtain ⟨v₁, v₂, v₃, hne12, hne13, hne23, rfl⟩ := Finset.card_eq_three.mp h3
    obtain ⟨hp1_lo, hp1_hi⟩ := hp v₁ (Finset.mem_insert_self v₁ _)
    obtain ⟨hp2_lo, hp2_hi⟩ := hp v₂ (Finset.mem_insert_of_mem (Finset.mem_insert_self v₂ _))
    obtain ⟨hp3_lo, hp3_hi⟩ :=
      hp v₃ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self v₃)))
    have hnot1 : v₁ ∉ ({v₂, v₃} : Finset V) := by
      simp [Finset.mem_insert, Finset.mem_singleton, hne12, hne13]
    have hstep := root_three_children hp1_lo hp1_hi hp2_lo hp2_hi hp3_lo hp3_hi
    simp only [Finset.prod_insert hnot1, Finset.prod_pair hne23,
      Finset.sum_insert hnot1, Finset.sum_pair hne23,
      Finset.card_insert_of_notMem hnot1, Finset.card_pair hne23,
      Finset.insert_nonempty, ↓reduceIte]
    push_cast
    rw [← mul_assoc]
    linarith

/-- Propagates the subtree entropy bound from children `arcKids arc u` to `u` given a local
potential step `hstep`. Shared between internal vertices and roots. -/
private theorem logb_subIndepCount_le_of_step [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton)
    {u : V} {δ : ℝ}
    (hchild : ∀ v ∈ arcKids arc u,
      Real.logb 2 (subIndepCount arc v : ℝ) ≤
        ((arcSubtree arc v).card : ℝ) - (53 / 200 : ℝ) * (subEdges arc v : ℝ) -
          treePot (subRootRatio arc v))
    (hstep : Real.logb 2 (1 + ∏ v ∈ arcKids arc u, subRootRatio arc v) + δ -
        ∑ v ∈ arcKids arc u, treePot (subRootRatio arc v) ≤
      1 - (53 / 200 : ℝ) * ((arcKids arc u).card : ℝ)) :
    Real.logb 2 (subIndepCount arc u : ℝ) ≤
      ((arcSubtree arc u).card : ℝ) - (53 / 200 : ℝ) * (subEdges arc u : ℝ) - δ := by
  have hsum : ∑ v ∈ arcKids arc u, Real.logb 2 (subIndepCount arc v : ℝ) ≤
      (∑ v ∈ arcKids arc u, ((arcSubtree arc v).card : ℝ)) -
        (53 / 200 : ℝ) * (∑ v ∈ arcKids arc u, (subEdges arc v : ℝ)) -
        ∑ v ∈ arcKids arc u, treePot (subRootRatio arc v) := by
    calc ∑ v ∈ arcKids arc u, Real.logb 2 (subIndepCount arc v : ℝ)
        ≤ ∑ v ∈ arcKids arc u,
            (((arcSubtree arc v).card : ℝ) - (53 / 200 : ℝ) * (subEdges arc v : ℝ) -
              treePot (subRootRatio arc v)) := Finset.sum_le_sum hchild
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hcard_r : ((arcSubtree arc u).card : ℝ) =
      1 + ∑ v ∈ arcKids arc u, ((arcSubtree arc v).card : ℝ) := by
    exact_mod_cast card_arcSubtree_eq hrank hin u
  have hedges_r : (subEdges arc u : ℝ) =
      ((arcKids arc u).card : ℝ) + ∑ v ∈ arcKids arc u, (subEdges arc v : ℝ) := by
    exact_mod_cast subEdges_eq hrank hin u
  rw [logb_subIndepCount_eq hrank hin u, hcard_r, hedges_r]
  linarith

/-- Bottom-up Tree-DP invariant: every internal vertex `u` satisfies `p(T_u) ∈ [1 / 2, 4 / 5]`
and the quadratic-potential entropy bound. -/
private theorem treeDP_internal_bound [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton)
    (hout_int : ∀ w, (∃ u, arc u w) → (arcKids arc w).card ≤ 2)
    (u : V) (hin_u : ∃ w, arc w u) :
    (1 / 2 ≤ subRootRatio arc u ∧ subRootRatio arc u ≤ 4 / 5) ∧
      Real.logb 2 (subIndepCount arc u : ℝ) ≤
        ((arcSubtree arc u).card : ℝ) - (53 / 200 : ℝ) * (subEdges arc u : ℝ) -
          treePot (subRootRatio arc u) := by
  let M_rk : ℕ := Finset.univ.sup rk
  suffices h : ∀ d : ℕ, ∀ u : V, M_rk - rk u = d → (∃ w, arc w u) →
      (1 / 2 ≤ subRootRatio arc u ∧ subRootRatio arc u ≤ 4 / 5) ∧
        Real.logb 2 (subIndepCount arc u : ℝ) ≤
          ((arcSubtree arc u).card : ℝ) - (53 / 200 : ℝ) * (subEdges arc u : ℝ) -
            treePot (subRootRatio arc u) from
    h (M_rk - rk u) u rfl hin_u
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro u hd hin_u
    have hchild : ∀ v ∈ arcKids arc u,
        (1 / 2 ≤ subRootRatio arc v ∧ subRootRatio arc v ≤ 4 / 5) ∧
          Real.logb 2 (subIndepCount arc v : ℝ) ≤
            ((arcSubtree arc v).card : ℝ) - (53 / 200 : ℝ) * (subEdges arc v : ℝ) -
              treePot (subRootRatio arc v) := by
      intro v hv
      have harc : arc u v := by simpa [arcKids] using hv
      have hlt_rk : rk u < rk v := hrank harc
      have hv_le : rk v ≤ M_rk := Finset.le_sup (f := rk) (Finset.mem_univ v)
      exact ih (M_rk - rk v) (by omega) v rfl ⟨u, harc⟩
    have hdeg := hout_int u hin_u
    have hrat := subRootRatio_eq hrank hin u
    refine ⟨hrat ▸ one_div_one_add_prod_mem_Icc hdeg (fun v hv => (hchild v hv).1),
      logb_subIndepCount_le_of_step hrank hin (fun v hv => (hchild v hv).2) ?_⟩
    rw [hrat]
    exact step_finset_le_two hdeg fun v hv => (hchild v hv).1

/-- Active-root entropy bound discharging the `33 / 1000` penalty at each root `r` of
out-degree at most `3`. -/
private theorem treeDP_root_bound [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton)
    (hout_int : ∀ w, (∃ u, arc u w) → (arcKids arc w).card ≤ 2)
    (hout_root : ∀ r, (¬∃ u, arc u r) → (arcKids arc r).card ≤ 3)
    (r : V) (hr : ¬∃ u, arc u r) :
    Real.logb 2 (subIndepCount arc r : ℝ) ≤
      ((arcSubtree arc r).card : ℝ) - (53 / 200 : ℝ) * (subEdges arc r : ℝ) -
        if (arcKids arc r).Nonempty then (33 / 1000 : ℝ) else 0 := by
  have hchild (v : V) (hv : v ∈ arcKids arc r) :=
    treeDP_internal_bound hrank hin hout_int v ⟨r, by simpa [arcKids] using hv⟩
  exact logb_subIndepCount_le_of_step hrank hin (fun v hv => (hchild v hv).2)
    (root_finset_le_three (hout_root r hr) fun v hv => (hchild v hv).1)

/-- Core bounded-degree Tree-DP theorem on `SimpleGraph.fromRel arc`. -/
private theorem logb_indepSetCount_fromRel_le_core [Fintype V] {arc : V → V → Prop}
    [DecidableRel arc] {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) (hin : ∀ w, {u | arc u w}.Subsingleton)
    (hout_int : ∀ w, (∃ u, arc u w) → (Finset.univ.filter (arc w ·)).card ≤ 2)
    (hout_root : ∀ r, (¬∃ u, arc u r) → (Finset.univ.filter (arc r ·)).card ≤ 3) :
    Real.logb 2 ((SimpleGraph.fromRel arc).indepSetCount : ℝ) ≤
      (Fintype.card V : ℝ) -
        (53 / 200 : ℝ) * ∑ w : V, ((Finset.univ.filter (arc w ·)).card : ℝ) -
        (33 / 1000 : ℝ) *
          ((Finset.univ.filter fun r => (¬∃ u, arc u r) ∧ ∃ v, arc r v).card : ℝ) := by
  classical
  have hkids_eq : ∀ w : V, Finset.univ.filter (arc w ·) = arcKids arc w := fun w => by
    ext v; simp [arcKids]
  simp_rw [hkids_eq] at hout_int hout_root ⊢
  let roots : Finset V := Finset.univ.filter fun r => ¬∃ u, arc u r
  have hroots_disj : (roots : Set V).PairwiseDisjoint (arcSubtree arc) := by
    intro r₁ hr₁ r₂ hr₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz1 hz2
    simp only [arcSubtree, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
    simp only [Finset.mem_coe, roots, Finset.mem_filter, Finset.mem_univ, true_and] at hr₁ hr₂
    exact Set.disjoint_left.mp (subtree_disjoint_roots hrank hin hr₁ hr₂ hne) hz1 hz2
  have hroots_cross : ∀ r₁ ∈ roots, ∀ r₂ ∈ roots, r₁ ≠ r₂ →
      ∀ x ∈ arcSubtree arc r₁, ∀ y ∈ arcSubtree arc r₂,
        ¬(SimpleGraph.fromRel arc).Adj x y :=
    fun _ hr₁ _ hr₂ hne _ hx _ hy =>
      no_adj_of_disjoint_arcSubtree (hroots_disj hr₁ hr₂ hne) hx hy
  have huniv_eq : (Finset.univ : Finset V) = roots.biUnion (arcSubtree arc) := by
    ext z
    simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion, roots, arcSubtree,
      Finset.mem_filter, true_and]
    exact exists_root_reaches hrank z
  have hindep_prod : (SimpleGraph.fromRel arc).indepSetCount =
      ∏ r ∈ roots, subIndepCount arc r := by
    rw [← card_indepPowerset_univ (SimpleGraph.fromRel arc), huniv_eq,
      card_indepPowerset_biUnion roots (arcSubtree arc) hroots_disj hroots_cross]
    refine Finset.prod_congr rfl fun r _ => ?_
    exact congrArg Finset.card (Finset.ext fun I => by simp [indepPowerset])
  have hlog_G : Real.logb 2 ((SimpleGraph.fromRel arc).indepSetCount : ℝ) =
      ∑ r ∈ roots, Real.logb 2 (subIndepCount arc r : ℝ) := by
    rw [hindep_prod, Nat.cast_prod]
    exact Real.logb_prod _ _ fun v _ => (Nat.cast_pos.mpr (subIndepCount_pos arc v)).ne'
  have hsum_V : (Fintype.card V : ℝ) = ∑ r ∈ roots, ((arcSubtree arc r).card : ℝ) := by
    rw [← Nat.cast_sum, ← Finset.card_univ, huniv_eq, Finset.card_biUnion hroots_disj]
  have hsum_E : (∑ w : V, ((arcKids arc w).card : ℝ)) =
      ∑ r ∈ roots, (subEdges arc r : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    congr 1
    conv_lhs => rw [huniv_eq]
    rw [Finset.sum_biUnion hroots_disj]
    rfl
  have hsum_R :
      ((Finset.univ.filter fun r => (¬∃ u, arc u r) ∧ ∃ v, arc r v).card : ℝ) =
        ∑ r ∈ roots, (if (arcKids arc r).Nonempty then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
    congr 2
    ext r
    simp [roots, arcKids, Finset.Nonempty]
  rw [hlog_G, hsum_V, hsum_E, hsum_R]
  calc ∑ r ∈ roots, Real.logb 2 (subIndepCount arc r : ℝ)
      ≤ ∑ r ∈ roots, (((arcSubtree arc r).card : ℝ) -
          (53 / 200 : ℝ) * (subEdges arc r : ℝ) -
          if (arcKids arc r).Nonempty then (33 / 1000 : ℝ) else 0) :=
        Finset.sum_le_sum fun r hr =>
          treeDP_root_bound hrank hin hout_int hout_root r (Finset.mem_filter.mp hr).2
    _ = (∑ r ∈ roots, ((arcSubtree arc r).card : ℝ)) -
          (53 / 200 : ℝ) * (∑ r ∈ roots, (subEdges arc r : ℝ)) -
          (33 / 1000 : ℝ) * ∑ r ∈ roots, (if (arcKids arc r).Nonempty then (1 : ℝ) else 0) := by
        simp only [Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_one, mul_zero]

end ArcSubtree

end TreeDP

/-! ### Public out-forest independent-set bounds -/

/-- When `arc` is asymmetric (`rk u < rk w`), the edges of `SimpleGraph.fromRel arc` biject with
the directed pairs `(u, w)` satisfying `arc u w`. -/
private theorem sum_outDeg_eq_ncard_edgeSet [Fintype V] {arc : V → V → Prop} {rk : V → ℕ}
    (hrank : ∀ ⦃u w⦄, arc u w → rk u < rk w) :
    (∑ w : V, {v | arc w v}.ncard) = (SimpleGraph.fromRel arc).edgeSet.ncard := by
  classical
  have hsum : (∑ w : V, {v | arc w v}.ncard) =
      (Finset.univ.filter fun p : V × V => arc p.1 p.2).card := by
    have h1 : ∀ w : V, {v | arc w v}.ncard = (Finset.univ.filter (arc w ·)).card := fun w => by
      rw [← ncard_coe_finset]
      congr 1
      ext v
      simp
    simp_rw [h1]
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun s _ => (s.1, s.2)) ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hs ⊢
      exact hs
    · rintro ⟨w₁, v₁⟩ _ ⟨w₂, v₂⟩ _ h
      exact Sigma.ext (Prod.mk.inj h).1 (heq_of_eq (Prod.mk.inj h).2)
    · rintro ⟨w, v⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨⟨w, v⟩, by simp [hp], rfl⟩
  rw [hsum, ← (SimpleGraph.fromRel arc).coe_edgeFinset, ncard_coe_finset]
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · rintro ⟨u, w⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [mem_edgeFinset, mem_edgeSet, fromRel_adj]
    exact ⟨fun h => (hrank hp).ne (congrArg rk h), Or.inl hp⟩
  · rintro ⟨u₁, w₁⟩ hp₁ ⟨u₂, w₂⟩ hp₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd (hrank hp₁) (not_lt_of_gt (hrank hp₂))
  · intro e he
    rw [mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u w =>
      rw [mem_edgeSet, fromRel_adj] at he
      rcases he.2 with huw | hwu
      · exact ⟨(u, w), by simp [huw], rfl⟩
      · exact ⟨(w, u), by simp [hwu], Sym2.eq_swap⟩

/-- When every non-root has out-degree at most `2` and every root has out-degree at most `3`,
`arborescenceCappedEdges B` equals `(SimpleGraph.fromRel B.Adj).edgeSet.ncard`. -/
theorem arborescenceCappedEdges_eq_ncard_edgeSet [Finite V] {B : Digraph V} (hB : B.IsBranching)
    (hout_int : ∀ w, (∃ u, B.Adj u w) → {v | B.Adj w v}.ncard ≤ 2)
    (hout_root : ∀ r, (¬∃ u, B.Adj u r) → {v | B.Adj r v}.ncard ≤ 3) :
    arborescenceCappedEdges B = (SimpleGraph.fromRel B.Adj).edgeSet.ncard := by
  classical
  cases nonempty_fintype V
  obtain ⟨rk, hrank⟩ := hB.exists_rank
  rw [arborescenceCappedEdges, finsum_eq_sum_of_fintype, ← sum_outDeg_eq_ncard_edgeSet hrank]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs with hw
  · exact Nat.min_eq_left (hout_int w hw)
  · exact Nat.min_eq_left (hout_root w hw)

/-- **Universal out-forest independent-set bound (arbitrary out-degrees).** For any branching
`B : Digraph V` on a finite vertex type `V`, capping outgoing arcs at `2` on internal vertices and
`3` on roots yields:
`Real.logb 2 i(fromRel B.Adj) ≤ |V| - (53 / 200) * cappedEdges - (33 / 1000) * |activeRoots|`. -/
theorem logb_indepSetCount_fromRel_le_capped [Finite V] {B : Digraph V} (hB : B.IsBranching) :
    Real.logb 2 ((SimpleGraph.fromRel B.Adj).indepSetCount : ℝ) ≤
      (Nat.card V : ℝ) - (53 / 200 : ℝ) * (arborescenceCappedEdges B : ℝ) -
        (33 / 1000 : ℝ) * ((arborescenceActiveRoots B).ncard : ℝ) := by
  classical
  cases nonempty_fintype V
  obtain ⟨rk, hrank⟩ := hB.exists_rank
  -- At each vertex `w`, choose `chosen w ⊆ univ.filter (B.Adj w ·)` of exact capped size!
  let cap : V → ℕ := fun w => min {v | B.Adj w v}.ncard (if ∃ u, B.Adj u w then 2 else 3)
  have hle_card : ∀ w : V, cap w ≤ (Finset.univ.filter (B.Adj w ·)).card := by
    intro w
    have heq : {v | B.Adj w v}.ncard = (Finset.univ.filter (B.Adj w ·)).card := by
      rw [← ncard_coe_finset]
      congr 1; ext v; simp
    rw [← heq]
    exact Nat.min_le_left _ _
  choose chosen hchosen_sub hchosen_card using
    fun w : V => Finset.exists_subset_card_eq (hle_card w)
  let arc' : V → V → Prop := fun u w => w ∈ chosen u
  have harc'_imp : ∀ ⦃u w⦄, arc' u w → B.Adj u w := by
    intro u w hw
    exact (Finset.mem_filter.mp (hchosen_sub u hw)).2
  have hrank' : ∀ ⦃u w⦄, arc' u w → rk u < rk w := fun _ _ h => hrank (harc'_imp h)
  have hin' : ∀ w, {u | arc' u w}.Subsingleton :=
    fun _ _ hu₁ _ hu₂ => hB.in_unique (harc'_imp hu₁) (harc'_imp hu₂)
  have hkids' : ∀ w : V, Finset.univ.filter (arc' w ·) = chosen w := by
    intro w
    ext v
    simp [arc']
  have hout_int' : ∀ w, (∃ u, arc' u w) → (Finset.univ.filter (arc' w ·)).card ≤ 2 := by
    intro w ⟨u, huw⟩
    have hw_in : ∃ u, B.Adj u w := ⟨u, harc'_imp huw⟩
    rw [hkids' w, hchosen_card w]
    dsimp only [cap]
    simp only [hw_in, ↓reduceIte]
    exact Nat.min_le_right _ _
  have hout_root' : ∀ r, (¬∃ u, arc' u r) → (Finset.univ.filter (arc' r ·)).card ≤ 3 := by
    intro r _
    rw [hkids' r, hchosen_card r]
    dsimp only [cap]
    split_ifs <;> omega
  -- Every original active root remains an active root of `arc'`:
  have hroots_sub : arborescenceActiveRoots B ⊆
      (Finset.univ.filter fun r => (¬∃ u, arc' u r) ∧ ∃ v, arc' r v : Set V) := by
    rintro r ⟨hno_in, v, hrv⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ r, ⟨fun ⟨u, hur⟩ => hno_in ⟨u, harc'_imp hur⟩, ?_⟩⟩
    have hpos : 0 < cap r := by
      dsimp only [cap]
      simp only [hno_in, ↓reduceIte]
      have h1 : 1 ≤ {v | B.Adj r v}.ncard :=
        (ncard_pos (toFinite _)).mpr ⟨v, hrv⟩
      omega
    exact Finset.card_pos.mp (hchosen_card r ▸ hpos)
  have hG_le : SimpleGraph.fromRel arc' ≤ SimpleGraph.fromRel B.Adj := fun _ _ h =>
    let ⟨hne, hadj⟩ := (fromRel_adj ..).mp h
    (fromRel_adj ..).mpr ⟨hne, hadj.imp (harc'_imp ·) (harc'_imp ·)⟩
  have hlog_mono : Real.logb 2 ((SimpleGraph.fromRel B.Adj).indepSetCount : ℝ) ≤
      Real.logb 2 ((SimpleGraph.fromRel arc').indepSetCount : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num)
      (Nat.cast_pos.mpr (SimpleGraph.fromRel B.Adj).indepSetCount_pos)
      (by exact_mod_cast indepSetCount_anti hG_le)
  have hcore := logb_indepSetCount_fromRel_le_core hrank' hin' hout_int' hout_root'
  have hE : (∑ w : V, ((Finset.univ.filter (arc' w ·)).card : ℝ)) =
      (arborescenceCappedEdges B : ℝ) := by
    simp_rw [hkids', hchosen_card]
    dsimp only [cap]
    rw [arborescenceCappedEdges, finsum_eq_sum_of_fintype, Nat.cast_sum]
    exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> rfl
  have hR : ((arborescenceActiveRoots B).ncard : ℝ) ≤
      ((Finset.univ.filter fun r => (¬∃ u, arc' u r) ∧ ∃ v, arc' r v).card : ℝ) := by
    rw [← ncard_coe_finset]
    exact_mod_cast ncard_le_ncard hroots_sub (toFinite _)
  rw [Nat.card_eq_fintype_card]
  rw [hE] at hcore
  linarith

/-- **Bounded-out-degree out-forest independent-set bound.** When internal vertices have out-degree
at most `2` and roots have out-degree at most `3`,
`Real.logb 2 i(fromRel B.Adj) ≤ |V| - (53 / 200) * |E| - (33 / 1000) * |activeRoots|`. -/
theorem logb_indepSetCount_fromRel_le [Finite V] {B : Digraph V} (hB : B.IsBranching)
    (hout_int : ∀ w, (∃ u, B.Adj u w) → {v | B.Adj w v}.ncard ≤ 2)
    (hout_root : ∀ r, (¬∃ u, B.Adj u r) → {v | B.Adj r v}.ncard ≤ 3) :
    Real.logb 2 ((SimpleGraph.fromRel B.Adj).indepSetCount : ℝ) ≤
      (Nat.card V : ℝ) - (53 / 200 : ℝ) * ((SimpleGraph.fromRel B.Adj).edgeSet.ncard : ℝ) -
        (33 / 1000 : ℝ) * ((arborescenceActiveRoots B).ncard : ℝ) := by
  rw [← arborescenceCappedEdges_eq_ncard_edgeSet hB hout_int hout_root]
  exact logb_indepSetCount_fromRel_le_capped hB

/-- Exponential (`2 ^ ·`) form of `logb_indepSetCount_fromRel_le`. -/
theorem indepSetCount_fromRel_le_rpow [Finite V] {B : Digraph V} (hB : B.IsBranching)
    (hout_int : ∀ w, (∃ u, B.Adj u w) → {v | B.Adj w v}.ncard ≤ 2)
    (hout_root : ∀ r, (¬∃ u, B.Adj u r) → {v | B.Adj r v}.ncard ≤ 3) :
    ((SimpleGraph.fromRel B.Adj).indepSetCount : ℝ) ≤
      (2 : ℝ) ^ ((Nat.card V : ℝ) -
        (53 / 200 : ℝ) * ((SimpleGraph.fromRel B.Adj).edgeSet.ncard : ℝ) -
        (33 / 1000 : ℝ) * ((arborescenceActiveRoots B).ncard : ℝ)) := by
  have hpos : (0 : ℝ) < ((SimpleGraph.fromRel B.Adj).indepSetCount : ℝ) :=
    Nat.cast_pos.mpr (SimpleGraph.fromRel B.Adj).indepSetCount_pos
  rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hpos]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (logb_indepSetCount_fromRel_le hB hout_int hout_root)

end SimpleGraph
