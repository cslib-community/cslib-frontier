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
(`Digraph.IsBranching.exists_rank`). Along each rooted component tree, bottom-up dynamic
programming tracks the unchosen-root ratio `p(T_u) = i₀(T_u) / i(T_u) ∈ [1 / 2, 4 / 5]` against the
quadratic potential `f(p) = (2 / 5) * (p - 1 / 2) + (3 / 10) * (p - 1 / 2) ^ 2`, establishing the
rational entropy bound

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
    rw [← Real.exp_nat_mul]
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
  let G := SimpleGraph.fromRel arc
  let kids : V → Finset V := fun u => Finset.univ.filter (arc u ·)
  let sub : V → Finset V := fun u => Finset.univ.filter (Relation.ReflTransGen arc u ·)
  -- Disjointness of child subtrees as `Finset`s:
  have hsub_disj : ∀ u : V, (kids u : Set V).PairwiseDisjoint sub := by
    intro u v₁ hv₁ v₂ hv₂ hne
    change Disjoint (sub v₁) (sub v₂)
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [sub, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
    simp only [Finset.mem_coe, kids, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
    exact Set.disjoint_left.mp (subtree_disjoint_children hrank hin hv₁ hv₂ hne) hz1 hz2
  have no_cross_of_disjoint {v₁ v₂ : V} (hd : Disjoint (sub v₁) (sub v₂))
      {x y : V} (hx : x ∈ sub v₁) (hy : y ∈ sub v₂) : ¬G.Adj x y := by
    intro hadj
    simp only [sub, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rw [fromRel_adj] at hadj
    rcases hadj.2 with hxy | hyx
    · exact Finset.disjoint_left.mp hd
        (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hx.tail hxy⟩)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)
    · exact Finset.disjoint_left.mp hd
        (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hy.tail hyx⟩)
  have hsub_cross : ∀ u : V, ∀ v₁ ∈ kids u, ∀ v₂ ∈ kids u, v₁ ≠ v₂ →
      ∀ x ∈ sub v₁, ∀ y ∈ sub v₂, ¬G.Adj x y :=
    fun u _ hv₁ _ hv₂ hne _ hx _ hy => no_cross_of_disjoint (hsub_disj u hv₁ hv₂ hne) hx hy
  have hu_not_mem_biUnion : ∀ u : V, u ∉ (kids u).biUnion sub := by
    intro u hmem
    obtain ⟨v, hv, huv⟩ := Finset.mem_biUnion.mp hmem
    simp only [kids, sub, Finset.mem_filter, Finset.mem_univ, true_and] at hv huv
    exact absurd (rk_le_of_reflTransGen hrank huv) (not_le_of_gt (hrank hv))
  have hsub_eq : ∀ u : V, sub u = insert u ((kids u).biUnion sub) := by
    intro u
    ext z
    simp only [sub, kids, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_biUnion]
    constructor
    · intro huz
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp huz with rfl | htr
      · exact Or.inl rfl
      · obtain ⟨v, huv, hvz⟩ := Relation.TransGen.head'_iff.mp htr
        exact Or.inr ⟨v, huv, hvz⟩
    · rintro (rfl | ⟨v, huv, hvz⟩)
      · exact .refl
      · exact hvz.head huv
  -- Subtree independent-set counts `i_tot u` and `i_zero u` (`u` unchosen):
  let i_tot : V → ℕ := fun u => (indepPowerset G (sub u)).card
  let i_zero : V → ℕ := fun u => (indepPowerset G ((kids u).biUnion sub)).card
  have hi_zero_eq : ∀ u : V, i_zero u = ∏ v ∈ kids u, i_tot v := fun u =>
    card_indepPowerset_biUnion (kids u) sub (hsub_disj u) (hsub_cross u)
  -- Subtree without root `u`: when `u` is chosen (`u ∈ I`), no `v ∈ kids u` can be in `I`, while
  -- `u` has no edges to `(kids v).biUnion sub`!
  have hu_no_edge_grand : ∀ u : V, ∀ v ∈ kids u, ∀ z ∈ (kids v).biUnion sub, ¬G.Adj u z := by
    intro u v hv z hz hadj
    obtain ⟨w, hw, hwz⟩ := Finset.mem_biUnion.mp hz
    have hv_arc : arc u v := by simpa [kids] using hv
    simp only [kids, sub, Finset.mem_filter, Finset.mem_univ, true_and] at hw hwz
    rw [fromRel_adj] at hadj
    rcases hadj.2 with huz | hzu
    · -- If `arc u z`, then `z ∈ kids u`; since `z ∈ sub v`, `v = z` by `hsub_disj`, impossible!
      have hz_kid : z ∈ kids u := by simp [kids, huz]
      have hz_sub_v : z ∈ sub v := by simp [sub, hwz.head hw]
      have hz_sub_z : z ∈ sub z := by simp [sub, Relation.ReflTransGen.refl]
      by_cases hvz : v = z
      · subst hvz
        exact absurd (rk_le_of_reflTransGen hrank hwz) (not_le_of_gt (hrank hw))
      · exact Finset.disjoint_left.mp (hsub_disj u hv hz_kid hvz) hz_sub_v hz_sub_z
    · have hlt : rk u < rk z :=
        (hrank hv_arc).trans ((hrank hw).trans_le (rk_le_of_reflTransGen hrank hwz))
      exact absurd (hrank hzu) (not_lt_of_gt hlt)
  have hi_tot_eq : ∀ u : V, i_tot u = i_zero u + ∏ v ∈ kids u, i_zero v := by
    intro u
    dsimp only [i_tot]
    rw [hsub_eq u]
    set B := (kids u).biUnion sub
    set S := indepPowerset G (insert u B)
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
          fun huI => hu_not_mem_biUnion u (hsub huI)⟩
    · -- Sets in `S` containing `u` biject via `erase u` with grandchild independent sets:
      set Gsub := (kids u).biUnion fun v => (kids v).biUnion sub
      have hGsub_B : Gsub ⊆ B := by
        intro z hz
        obtain ⟨v, hv, hzv⟩ := Finset.mem_biUnion.mp hz
        refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
        rw [hsub_eq v]
        exact Finset.mem_insert_of_mem hzv
      have hdisj_G : (kids u : Set V).PairwiseDisjoint (fun v => (kids v).biUnion sub) := by
        intro v₁ hv₁ v₂ hv₂ hne
        refine Disjoint.mono ?_ ?_ (hsub_disj u hv₁ hv₂ hne) <;>
        · intro z hz
          rw [hsub_eq]
          exact Finset.mem_insert_of_mem hz
      have hcross_G : ∀ v₁ ∈ kids u, ∀ v₂ ∈ kids u, v₁ ≠ v₂ →
          ∀ x ∈ (kids v₁).biUnion sub, ∀ y ∈ (kids v₂).biUnion sub, ¬G.Adj x y := by
        intro v₁ hv₁ v₂ hv₂ hne x hx y hy
        exact hsub_cross u v₁ hv₁ v₂ hv₂ hne x (by rw [hsub_eq]; exact Finset.mem_insert_of_mem hx)
          y (by rw [hsub_eq]; exact Finset.mem_insert_of_mem hy)
      rw [← card_indepPowerset_biUnion (kids u) (fun v => (kids v).biUnion sub) hdisj_G hcross_G]
      refine Finset.card_bij (fun I _ => I.erase u) ?_ ?_ ?_
      · intro I hI
        simp only [S, indepPowerset, Finset.mem_filter, Finset.mem_powerset, not_not] at hI ⊢
        obtain ⟨⟨hIsub, hIind⟩, huI⟩ := hI
        refine ⟨fun z hz => ?_, fun x hx y hy =>
          hIind x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)⟩
        have hzB : z ∈ B := (Finset.subset_insert_iff.mp hIsub) hz
        obtain ⟨v, hv, hzv⟩ := Finset.mem_biUnion.mp hzB
        rw [hsub_eq v] at hzv
        rcases Finset.mem_insert.mp hzv with rfl | hz_grand
        · have huv : G.Adj u z := by
            rw [fromRel_adj]
            have hvk : arc u z := by simpa [kids] using hv
            exact ⟨fun h => (hrank hvk).ne (congrArg rk h), Or.inl hvk⟩
          exact False.elim (hIind u huI z (Finset.mem_of_mem_erase hz) huv)
        · exact Finset.mem_biUnion.mpr ⟨v, hv, hz_grand⟩
      · intro I₁ h1 I₂ h2 heq
        simp only [Finset.mem_filter, not_not] at h1 h2
        rw [← Finset.insert_erase h1.2, ← Finset.insert_erase h2.2, heq]
      · intro J hJ
        simp only [indepPowerset, Finset.mem_filter, Finset.mem_powerset] at hJ
        have huJ : u ∉ J := fun huJ => hu_not_mem_biUnion u (hGsub_B (hJ.1 huJ))
        refine ⟨insert u J, ?_, Finset.erase_insert huJ⟩
        simp only [S, indepPowerset, Finset.mem_filter, Finset.mem_powerset, not_not]
        refine ⟨⟨Finset.insert_subset_insert u (hJ.1.trans hGsub_B), fun x hx y hy hadj => ?_⟩,
          Finset.mem_insert_self u J⟩
        rcases Finset.mem_insert.mp hx with hx_eq | hxJ <;>
          rcases Finset.mem_insert.mp hy with hy_eq | hyJ
        · rw [hx_eq, hy_eq] at hadj
          exact G.ne_of_adj hadj rfl
        · rw [hx_eq] at hadj
          obtain ⟨v, hv, hyv⟩ := Finset.mem_biUnion.mp (hJ.1 hyJ)
          exact hu_no_edge_grand u v hv y hyv hadj
        · rw [hy_eq] at hadj
          obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp (hJ.1 hxJ)
          exact hu_no_edge_grand u v hv x hxv hadj.symm
        · exact hJ.2 x hxJ y hyJ hadj
  have hi_zero_pos : ∀ u : V, 0 < i_zero u := fun _ =>
    Finset.card_pos.mpr ⟨∅, by simp [indepPowerset]⟩
  have hi_tot_pos : ∀ u : V, 0 < i_tot u := fun u => by
    rw [hi_tot_eq u]
    exact Nat.add_pos_left (hi_zero_pos u) _
  -- Edge count in `sub u`: `edges_sub u = ∑ w ∈ sub u, (kids w).card`:
  let edges_sub : V → ℕ := fun u => ∑ w ∈ sub u, (kids w).card
  have hedges_sub_eq : ∀ u : V, edges_sub u = (kids u).card + ∑ v ∈ kids u, edges_sub v := by
    intro u
    dsimp only [edges_sub]
    conv_lhs => rw [hsub_eq u]
    rw [Finset.sum_insert (hu_not_mem_biUnion u), Finset.sum_biUnion (hsub_disj u)]
  have hcard_sub_eq : ∀ u : V, (sub u).card = 1 + ∑ v ∈ kids u, (sub v).card := by
    intro u
    rw [hsub_eq u, Finset.card_insert_of_notMem (hu_not_mem_biUnion u),
      Finset.card_biUnion (hsub_disj u), Nat.add_comm]
  -- Ratio `p_rat u = i_zero u / i_tot u`:
  let p_rat : V → ℝ := fun u => (i_zero u : ℝ) / (i_tot u : ℝ)
  have htot_real : ∀ u : V,
      (i_tot u : ℝ) = (∏ v ∈ kids u, (i_tot v : ℝ)) * (1 + ∏ v ∈ kids u, p_rat v) := by
    intro u
    have h1 : (i_zero u : ℝ) = ∏ v ∈ kids u, (i_tot v : ℝ) := by exact_mod_cast hi_zero_eq u
    have h2 : (∏ v ∈ kids u, (i_zero v : ℝ)) =
        (∏ v ∈ kids u, (i_tot v : ℝ)) * (∏ v ∈ kids u, p_rat v) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      have hpos : (i_tot v : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hi_tot_pos v)).ne'
      dsimp only [p_rat]
      field_simp [hpos]
    have hcast : (i_tot u : ℝ) = (i_zero u : ℝ) + ∏ v ∈ kids u, (i_zero v : ℝ) := by
      exact_mod_cast hi_tot_eq u
    rw [hcast, h1, h2]
    ring
  have hlog_prod : ∀ s : Finset V,
      Real.logb 2 (∏ v ∈ s, (i_tot v : ℝ)) = ∑ v ∈ s, Real.logb 2 (i_tot v : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        Real.logb_mul (Nat.cast_pos.mpr (hi_tot_pos a)).ne'
          (Finset.prod_pos fun v _ => Nat.cast_pos.mpr (hi_tot_pos v)).ne', ih]
  have hp_rat_eq : ∀ u : V, p_rat u = 1 / (1 + ∏ v ∈ kids u, p_rat v) := by
    intro u
    have h1 : (i_zero u : ℝ) = ∏ v ∈ kids u, (i_tot v : ℝ) := by exact_mod_cast hi_zero_eq u
    have hne : (∏ v ∈ kids u, (i_tot v : ℝ)) ≠ 0 :=
      (Finset.prod_pos fun v _ => Nat.cast_pos.mpr (hi_tot_pos v)).ne'
    change (i_zero u : ℝ) / (i_tot u : ℝ) = 1 / (1 + ∏ v ∈ kids u, p_rat v)
    calc (i_zero u : ℝ) / (i_tot u : ℝ)
        = ((∏ v ∈ kids u, (i_tot v : ℝ)) * 1) /
            ((∏ v ∈ kids u, (i_tot v : ℝ)) * (1 + ∏ v ∈ kids u, p_rat v)) := by
          rw [h1, htot_real u, mul_one]
      _ = 1 / (1 + ∏ v ∈ kids u, p_rat v) := mul_div_mul_left 1 _ hne
  have hlog_itot : ∀ u : V, Real.logb 2 (i_tot u : ℝ) =
      (∑ v ∈ kids u, Real.logb 2 (i_tot v : ℝ)) + Real.logb 2 (1 + ∏ v ∈ kids u, p_rat v) := by
    intro u
    have hprod_ne : (∏ v ∈ kids u, (i_tot v : ℝ)) ≠ 0 :=
      (Finset.prod_pos fun v _ => Nat.cast_pos.mpr (hi_tot_pos v)).ne'
    have h1p_ne : (1 + ∏ v ∈ kids u, p_rat v) ≠ 0 := by
      have : 0 ≤ ∏ v ∈ kids u, p_rat v :=
        Finset.prod_nonneg fun v _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith
    rw [htot_real u, Real.logb_mul hprod_ne h1p_ne, hlog_prod (kids u)]
  -- Bottom-up induction on `M_rk - rk u` for every internal vertex (`∃ w, arc w u`):
  let M_rk : ℕ := Finset.univ.sup rk
  have hint_dp : ∀ d : ℕ, ∀ u : V, M_rk - rk u = d → (∃ w, arc w u) →
      (1 / 2 ≤ p_rat u ∧ p_rat u ≤ 4 / 5) ∧
      Real.logb 2 (i_tot u : ℝ) ≤
        ((sub u).card : ℝ) - (53 / 200 : ℝ) * (edges_sub u : ℝ) - treePot (p_rat u) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro u hd hin_u
      have hdeg : (kids u).card ≤ 2 := hout_int u hin_u
      have hchild_ih : ∀ v ∈ kids u, (1 / 2 ≤ p_rat v ∧ p_rat v ≤ 4 / 5) ∧
          Real.logb 2 (i_tot v : ℝ) ≤
            ((sub v).card : ℝ) - (53 / 200 : ℝ) * (edges_sub v : ℝ) - treePot (p_rat v) := by
        intro v hv
        have harc : arc u v := by simpa [kids] using hv
        have hlt_rk : rk u < rk v := hrank harc
        have hv_le : rk v ≤ M_rk := Finset.le_sup (f := rk) (Finset.mem_univ v)
        have hd_lt : M_rk - rk v < d := by omega
        exact ih (M_rk - rk v) hd_lt v rfl ⟨u, harc⟩
      have hcard_r : ((sub u).card : ℝ) = 1 + ∑ v ∈ kids u, ((sub v).card : ℝ) := by
        exact_mod_cast hcard_sub_eq u
      have hedges_r : (edges_sub u : ℝ) =
          ((kids u).card : ℝ) + ∑ v ∈ kids u, (edges_sub v : ℝ) := by
        exact_mod_cast hedges_sub_eq u
      have hcases : (kids u).card = 0 ∨ (kids u).card = 1 ∨ (kids u).card = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · -- Leaf (`kids u = ∅`):
        have hemp : kids u = ∅ := Finset.card_eq_zero.mp h0
        have hp : p_rat u = 1 / 2 := by rw [hp_rat_eq u, hemp]; norm_num
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        rw [hlog_itot u, hcard_r, hedges_r, hemp, hp, treePot_half]
        simp only [Finset.sum_empty, Finset.prod_empty, Finset.card_empty, Nat.cast_zero,
          mul_zero, sub_zero, zero_add]
        rw [show (1 + 1 : ℝ) = 2 by norm_num, Real.logb_self_eq_one (by norm_num)]
        linarith
      · -- 1 child (`kids u = {v₁}`):
        obtain ⟨v₁, hv₁_eq⟩ := Finset.card_eq_one.mp h1
        have hv₁_mem : v₁ ∈ kids u := hv₁_eq ▸ Finset.mem_singleton_self v₁
        obtain ⟨⟨hp1_lo, hp1_hi⟩, hlog1⟩ := hchild_ih v₁ hv₁_mem
        have hp : p_rat u = 1 / (1 + p_rat v₁) := by rw [hp_rat_eq u, hv₁_eq, Finset.prod_singleton]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp]; rw [le_div_iff₀ (by linarith)]; linarith
        · rw [hp]; rw [div_le_iff₀ (by linarith)]; linarith
        · have hstep := step_one_child hp1_lo hp1_hi
          rw [hlog_itot u, hcard_r, hedges_r, hp, hv₁_eq]
          simp only [Finset.sum_singleton, Finset.prod_singleton, Finset.card_singleton,
            Nat.cast_one]
          linarith
      · -- 2 children (`kids u = {v₁, v₂}` with `v₁ ≠ v₂`):
        obtain ⟨v₁, v₂, hne, hv_eq⟩ := Finset.card_eq_two.mp h2
        have hv₁_mem : v₁ ∈ kids u := hv_eq ▸ Finset.mem_insert_self v₁ {v₂}
        have hv₂_mem : v₂ ∈ kids u :=
          hv_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v₂)
        obtain ⟨⟨hp1_lo, hp1_hi⟩, hlog1⟩ := hchild_ih v₁ hv₁_mem
        obtain ⟨⟨hp2_lo, hp2_hi⟩, hlog2⟩ := hchild_ih v₂ hv₂_mem
        have hp : p_rat u = 1 / (1 + p_rat v₁ * p_rat v₂) := by
          rw [hp_rat_eq u, hv_eq, Finset.prod_pair hne]
        have hprod_pos : 0 < 1 + p_rat v₁ * p_rat v₂ := by nlinarith
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, le_div_iff₀ hprod_pos]
          nlinarith
        · rw [hp, div_le_iff₀ hprod_pos]
          nlinarith
        · have hstep := step_two_children hp1_lo hp1_hi hp2_lo hp2_hi
          rw [hlog_itot u, hcard_r, hedges_r, hp, hv_eq, Finset.sum_pair hne,
            Finset.sum_pair hne, Finset.sum_pair hne, Finset.prod_pair hne, Finset.card_pair hne]
          push_cast
          linarith
  -- Now evaluate at every root `r ∈ roots` (`¬∃ u, arc u r`, `(kids r).card ≤ 3`):
  let roots : Finset V := Finset.univ.filter fun r => ¬∃ u, arc u r
  have hroot_bound : ∀ r ∈ roots,
      Real.logb 2 (i_tot r : ℝ) ≤
        ((sub r).card : ℝ) - (53 / 200 : ℝ) * (edges_sub r : ℝ) -
          if (kids r).Nonempty then (33 / 1000 : ℝ) else 0 := by
    intro r hr
    have hr_no_in : ¬∃ u, arc u r := (Finset.mem_filter.mp hr).2
    have hdeg : (kids r).card ≤ 3 := hout_root r hr_no_in
    have hchild : ∀ v ∈ kids r, (1 / 2 ≤ p_rat v ∧ p_rat v ≤ 4 / 5) ∧
        Real.logb 2 (i_tot v : ℝ) ≤
          ((sub v).card : ℝ) - (53 / 200 : ℝ) * (edges_sub v : ℝ) - treePot (p_rat v) := by
      intro v hv
      have harc : arc r v := by simpa [kids] using hv
      exact hint_dp (M_rk - rk v) v rfl ⟨r, harc⟩
    have hcard_r : ((sub r).card : ℝ) = 1 + ∑ v ∈ kids r, ((sub v).card : ℝ) := by
      exact_mod_cast hcard_sub_eq r
    have hedges_r : (edges_sub r : ℝ) = ((kids r).card : ℝ) + ∑ v ∈ kids r, (edges_sub v : ℝ) := by
      exact_mod_cast hedges_sub_eq r
    have hcases : (kids r).card = 0 ∨ (kids r).card = 1 ∨
        (kids r).card = 2 ∨ (kids r).card = 3 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3
    · have hemp : kids r = ∅ := Finset.card_eq_zero.mp h0
      rw [hlog_itot r, hcard_r, hedges_r, hemp]
      simp only [Finset.not_nonempty_empty, ↓reduceIte, Finset.sum_empty, Finset.prod_empty,
        Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero, zero_add]
      rw [show (1 + 1 : ℝ) = 2 by norm_num, Real.logb_self_eq_one (by norm_num)]
      linarith
    · obtain ⟨v₁, hv₁_eq⟩ := Finset.card_eq_one.mp h1
      have hv₁_mem : v₁ ∈ kids r := hv₁_eq ▸ Finset.mem_singleton_self v₁
      obtain ⟨⟨hp1_lo, hp1_hi⟩, hlog1⟩ := hchild v₁ hv₁_mem
      have hstep := root_one_child hp1_lo hp1_hi
      have hne : (kids r).Nonempty := ⟨v₁, hv₁_mem⟩
      simp only [hne, ↓reduceIte]
      rw [hlog_itot r, hcard_r, hedges_r, hv₁_eq]
      simp only [Finset.sum_singleton, Finset.prod_singleton, Finset.card_singleton, Nat.cast_one]
      linarith
    · obtain ⟨v₁, v₂, hne12, hv_eq⟩ := Finset.card_eq_two.mp h2
      have hv₁_mem : v₁ ∈ kids r := hv_eq ▸ Finset.mem_insert_self v₁ {v₂}
      have hv₂_mem : v₂ ∈ kids r :=
        hv_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v₂)
      obtain ⟨⟨hp1_lo, hp1_hi⟩, hlog1⟩ := hchild v₁ hv₁_mem
      obtain ⟨⟨hp2_lo, hp2_hi⟩, hlog2⟩ := hchild v₂ hv₂_mem
      have hstep := root_two_children hp1_lo hp1_hi hp2_lo hp2_hi
      have hne : (kids r).Nonempty := ⟨v₁, hv₁_mem⟩
      simp only [hne, ↓reduceIte]
      rw [hlog_itot r, hcard_r, hedges_r, hv_eq, Finset.sum_pair hne12,
        Finset.sum_pair hne12, Finset.sum_pair hne12, Finset.prod_pair hne12,
        Finset.card_pair hne12]
      push_cast
      linarith
    · obtain ⟨v₁, v₂, v₃, hne12, hne13, hne23, hv_eq⟩ := Finset.card_eq_three.mp h3
      have hv₁_mem : v₁ ∈ kids r := hv_eq ▸ Finset.mem_insert_self v₁ {v₂, v₃}
      have hv₂_mem : v₂ ∈ kids r :=
        hv_eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self v₂ {v₃})
      have hv₃_mem : v₃ ∈ kids r := hv_eq ▸ Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self v₃))
      obtain ⟨⟨hp1_lo, hp1_hi⟩, hlog1⟩ := hchild v₁ hv₁_mem
      obtain ⟨⟨hp2_lo, hp2_hi⟩, hlog2⟩ := hchild v₂ hv₂_mem
      obtain ⟨⟨hp3_lo, hp3_hi⟩, hlog3⟩ := hchild v₃ hv₃_mem
      have hstep := root_three_children hp1_lo hp1_hi hp2_lo hp2_hi hp3_lo hp3_hi
      have hne : (kids r).Nonempty := ⟨v₁, hv₁_mem⟩
      have hnot1 : v₁ ∉ ({v₂, v₃} : Finset V) := by
        simp [Finset.mem_insert, Finset.mem_singleton, hne12, hne13]
      simp only [hne, ↓reduceIte]
      rw [hlog_itot r, hcard_r, hedges_r, hv_eq, Finset.sum_insert hnot1,
        Finset.sum_pair hne23, Finset.sum_insert hnot1, Finset.sum_pair hne23,
        Finset.sum_insert hnot1, Finset.sum_pair hne23, Finset.prod_insert hnot1,
        Finset.prod_pair hne23, Finset.card_insert_of_notMem hnot1, Finset.card_pair hne23,
        ← mul_assoc]
      push_cast
      linarith
  -- Finally, `Finset.univ = roots.biUnion sub` with pairwise disjointness and zero cross-edges:
  have hroots_disj : (roots : Set V).PairwiseDisjoint sub := by
    intro r₁ hr₁ r₂ hr₂ hne
    change Disjoint (sub r₁) (sub r₂)
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [sub, Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
    simp only [Finset.mem_coe, roots, Finset.mem_filter, Finset.mem_univ, true_and] at hr₁ hr₂
    exact Set.disjoint_left.mp (subtree_disjoint_roots hrank hin hr₁ hr₂ hne) hz1 hz2
  have hroots_cross : ∀ r₁ ∈ roots, ∀ r₂ ∈ roots, r₁ ≠ r₂ →
      ∀ x ∈ sub r₁, ∀ y ∈ sub r₂, ¬G.Adj x y :=
    fun _ hr₁ _ hr₂ hne _ hx _ hy => no_cross_of_disjoint (hroots_disj hr₁ hr₂ hne) hx hy
  have huniv_eq : (Finset.univ : Finset V) = roots.biUnion sub := by
    ext z
    simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion, roots, sub, Finset.mem_filter,
      true_and]
    exact exists_root_reaches hrank z
  have hindep_prod : G.indepSetCount = ∏ r ∈ roots, i_tot r := by
    rw [← card_indepPowerset_univ G, huniv_eq,
      card_indepPowerset_biUnion roots sub hroots_disj hroots_cross]
  have hlog_G : Real.logb 2 (G.indepSetCount : ℝ) = ∑ r ∈ roots, Real.logb 2 (i_tot r : ℝ) := by
    rw [hindep_prod, Nat.cast_prod]
    exact hlog_prod roots
  have hsum_V : (Fintype.card V : ℝ) = ∑ r ∈ roots, ((sub r).card : ℝ) := by
    rw [← Nat.cast_sum, ← Finset.card_univ, huniv_eq, Finset.card_biUnion hroots_disj]
  have hsum_E : (∑ w : V, ((kids w).card : ℝ)) = ∑ r ∈ roots, (edges_sub r : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    congr 1
    conv_lhs => rw [huniv_eq]
    rw [Finset.sum_biUnion hroots_disj]
  have hsum_R : ((Finset.univ.filter fun r => (¬∃ u, arc u r) ∧ ∃ v, arc r v).card : ℝ) =
      ∑ r ∈ roots, (if (kids r).Nonempty then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
    congr 2
    ext r
    simp [roots, kids, Finset.Nonempty]
  rw [hlog_G, hsum_V, hsum_E, hsum_R]
  calc ∑ r ∈ roots, Real.logb 2 (i_tot r : ℝ)
      ≤ ∑ r ∈ roots, (((sub r).card : ℝ) - (53 / 200 : ℝ) * (edges_sub r : ℝ) -
          if (kids r).Nonempty then (33 / 1000 : ℝ) else 0) :=
        Finset.sum_le_sum hroot_bound
    _ = (∑ r ∈ roots, ((sub r).card : ℝ)) -
          (53 / 200 : ℝ) * (∑ r ∈ roots, (edges_sub r : ℝ)) -
          (33 / 1000 : ℝ) * ∑ r ∈ roots, (if (kids r).Nonempty then (1 : ℝ) else 0) := by
        simp only [Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_one, mul_zero]

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
