/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Evolutionary.RoutingDynamics
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Evolutionary dynamics applied to selfish routing: checked instances

Ordinary `module` client of `CslibFrontier.GameTheory.Evolutionary.RoutingDynamics` exercising:

1. **Shifted Pigou parallel-link network** (`pigouShifted`, latencies `u + 1` and `2` on `[0, 1]`):
   * positive minimum feasible average latency `l* = 7 / 4` and upper bound `lMax = 2`;
   * `![1, 0]` is a Wardrop equilibrium (`Definition 29.10`) and therefore an `ε`-approximate
     equilibrium for every `ε > 0`;
   * `![1 / 2, 1 / 2]` is feasible, not a Wardrop equilibrium, is a `(1 / 2)`-approximate
     equilibrium, and fails to be a `(1 / 8)`-approximate equilibrium;
   * algebraic equivalence of Equations (29.1) and (29.2) (`imitativeDrift_eq_replicatorDrift`)
     and zero total drift (`sum_replicatorDrift_eq_zero`);
   * stationary equilibrium trajectory `fun _ => ![1, 0]` checked directly via
     `isFeasible_relative`;
   * non-vacuity of global trajectory existence, uniqueness, strict support preservation,
     Exercise 29.6 feasibility invariance, Lyapunov potential monotonicity, and Theorem 29.12
     convergence time `2 / ε ^ 3 * Real.log (16 / 7)` from `![1 / 2, 1 / 2]`.
2. **Nonlinear polynomial latency network** (`quadraticShifted`, latencies `u ^ 2 + 1` and `2`):
   `u ↦ u ^ 2 + 1` is neither globally monotone nor globally Lipschitz on `ℝ`, yet satisfies the
   `[0, 1]`-localized hypotheses of Theorem 29.12.
3. **Zero-latency boundary witness** (`zeroRouting`, latencies `0` and `0`):
   `![1, 0]` is a Wardrop equilibrium of cost `0`, yet fails `IsApproxEquilibrium (1 / 2) ![1, 0]`
   because Definition 29.11 uses `≥` (`l_p(x) ≥ (1 + ε) · 0` holds on every path), witnessing that
   `0 < G.cost x` cannot be dropped from `IsWardrop.isApproxEquilibrium`.
-/

public section

namespace CslibFrontierTests.GameTheory.EvolutionaryRoutingDynamics

open Cslib.GameTheory Cslib.GameTheory.NonatomicCongestionGame Set

/-! ### Shifted Pigou parallel-link network -/

/-- Two parallel links with unit traffic rate: link `0` has latency `u + 1`, link `1` has constant
latency `2`. -/
def pigouShifted : NonatomicCongestionGame Unit (Fin 2) (Fin 2) where
  commodity _ := ()
  resources p := {p}
  rate _ := 1
  latency e u := if e = 0 then u + 1 else 2

private theorem pigouShifted_edgeFlow (f : Fin 2 → ℝ) (e : Fin 2) :
    pigouShifted.edgeFlow f e = f e := by
  simp only [edgeFlow, pigouShifted, Finset.mem_singleton, Finset.filter_eq, Finset.mem_univ,
    ↓reduceIte, Finset.sum_singleton]

private theorem pigouShifted_pathLatency (f : Fin 2 → ℝ) (p : Fin 2) :
    pigouShifted.pathLatency f p = if p = 0 then f 0 + 1 else 2 := by
  simp only [pathLatency, pigouShifted_edgeFlow]
  fin_cases p <;> simp [pigouShifted]

private theorem pigouShifted_cost (f : Fin 2 → ℝ) :
    pigouShifted.cost f = f 0 * (f 0 + 1) + f 1 * 2 := by
  unfold cost
  rw [Fin.sum_univ_two, pigouShifted_pathLatency, pigouShifted_pathLatency]
  simp only [↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]

private theorem pigouShifted_isFeasible_iff {f : Fin 2 → ℝ} :
    pigouShifted.IsFeasible f ↔ 0 ≤ f 0 ∧ 0 ≤ f 1 ∧ f 0 + f 1 = 1 := by
  rw [isFeasible_unit_iff rfl, Fin.forall_fin_two, Fin.sum_univ_two, and_assoc]

private theorem pigouShifted_cost_ge {y : Fin 2 → ℝ} (hy : pigouShifted.IsFeasible y) :
    (7 / 4 : ℝ) ≤ pigouShifted.cost y := by
  obtain ⟨_, _, hsum⟩ := pigouShifted_isFeasible_iff.1 hy
  rw [pigouShifted_cost]
  nlinarith [sq_nonneg (y 0 - 1 / 2)]

private theorem pigouShifted_nonneg (e : Fin 2) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ pigouShifted.latency e u := by
  fin_cases e
  · change 0 ≤ u + 1; linarith [hu.1]
  · change (0 : ℝ) ≤ 2; norm_num

private theorem pigouShifted_mono (e : Fin 2) :
    MonotoneOn (pigouShifted.latency e) (Icc 0 1) := fun _ _ _ _ hab => by
  fin_cases e
  · change _ + 1 ≤ _ + 1; linarith
  · change (2 : ℝ) ≤ 2; exact le_rfl

private theorem pigouShifted_lip (e : Fin 2) :
    ∃ K, LipschitzOnWith K (pigouShifted.latency e) (Icc 0 1) := by
  fin_cases e
  · refine ⟨1, LipschitzOnWith.of_dist_le_mul fun a _ b _ => ?_⟩
    change |a + 1 - (b + 1)| ≤ (1 : NNReal) * |a - b|
    simp only [add_sub_add_right_eq_sub, NNReal.coe_one, one_mul, le_rfl]
  · refine ⟨0, LipschitzOnWith.of_dist_le_mul fun a _ b _ => ?_⟩
    change |(2 : ℝ) - 2| ≤ (0 : NNReal) * |a - b|
    simp only [sub_self, abs_zero, NNReal.coe_zero, zero_mul, le_rfl]

theorem pigouShifted_isFeasible_half : pigouShifted.IsFeasible ![1 / 2, 1 / 2] :=
  pigouShifted_isFeasible_iff.2 ⟨by norm_num, by norm_num, by norm_num⟩

theorem pigouShifted_isWardrop_pure0 : pigouShifted.IsWardrop ![1, 0] := by
  refine ⟨pigouShifted_isFeasible_iff.2 ⟨by norm_num, by norm_num, by norm_num⟩,
    fun p q _ _ => ?_⟩
  fin_cases p <;> fin_cases q <;> norm_num [pigouShifted_pathLatency]

theorem pigouShifted_pure0_isApproxEquilibrium {ε : ℝ} (hε : 0 < ε) :
    pigouShifted.IsApproxEquilibrium ε ![1, 0] :=
  pigouShifted_isWardrop_pure0.isApproxEquilibrium rfl
    (by rw [pigouShifted_cost]; norm_num) hε

theorem pigouShifted_half_not_isWardrop : ¬ pigouShifted.IsWardrop ![1 / 2, 1 / 2] := by
  intro h
  have hle := h.2 1 0 rfl (by norm_num)
  norm_num [pigouShifted_pathLatency] at hle

theorem pigouShifted_half_isApproxEquilibrium_half :
    pigouShifted.IsApproxEquilibrium (1 / 2) ![1 / 2, 1 / 2] := by
  refine ⟨pigouShifted_isFeasible_half, ?_⟩
  have hempty : Finset.univ.filter
      (fun p : Fin 2 => (1 + 1 / 2) * pigouShifted.cost ![1 / 2, 1 / 2] ≤
        pigouShifted.pathLatency ![1 / 2, 1 / 2] p) = ∅ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_le]
    rw [pigouShifted_cost]
    fin_cases p <;> norm_num [pigouShifted_pathLatency]
  rw [hempty, Finset.sum_empty]
  norm_num

theorem pigouShifted_half_not_isApproxEquilibrium_eighth :
    ¬ pigouShifted.IsApproxEquilibrium (1 / 8) ![1 / 2, 1 / 2] := by
  rintro ⟨-, hle⟩
  have hmem : (1 : Fin 2) ∈ Finset.univ.filter
      (fun p : Fin 2 => (1 + 1 / 8) * pigouShifted.cost ![1 / 2, 1 / 2] ≤
        pigouShifted.pathLatency ![1 / 2, 1 / 2] p) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [pigouShifted_cost, pigouShifted_pathLatency]
    norm_num
  have hsingle : (![1 / 2, 1 / 2] : Fin 2 → ℝ) 1 ≤
      ∑ p with (1 + 1 / 8) * pigouShifted.cost ![1 / 2, 1 / 2] ≤
        pigouShifted.pathLatency ![1 / 2, 1 / 2] p, (![1 / 2, 1 / 2] : Fin 2 → ℝ) p :=
    Finset.single_le_sum (fun p _ => by fin_cases p <;> norm_num) hmem
  norm_num at hsingle
  linarith

/-- Drift equivalence (Equations 29.1–29.2) and zero total drift (Exercise 29.6) on
`![1 / 2, 1 / 2]`. -/
theorem pigouShifted_drift_identities (p : Fin 2) :
    pigouShifted.imitativeDrift (fun y => (pigouShifted.cost y)⁻¹) ![1 / 2, 1 / 2] p =
      pigouShifted.replicatorDrift (fun y => (pigouShifted.cost y)⁻¹) ![1 / 2, 1 / 2] p ∧
    ∑ q, pigouShifted.replicatorDrift (fun y => (pigouShifted.cost y)⁻¹) ![1 / 2, 1 / 2] q = 0 := by
  have hsum : ∑ q : Fin 2, (![1 / 2, 1 / 2] : Fin 2 → ℝ) q = 1 := by
    rw [Fin.sum_univ_two]; norm_num
  exact ⟨imitativeDrift_eq_replicatorDrift _ hsum p, sum_replicatorDrift_eq_zero _ hsum⟩

/-- Constant trajectory at the Wardrop equilibrium `![1, 0]` solves the relative-rate replicator
ODE and exercises `IsReplicatorTrajectory.isFeasible_relative`. -/
theorem pigouShifted_stationary_isFeasible :
    ∀ t ≥ 0, pigouShifted.IsFeasible ((fun _ : ℝ => (![1, 0] : Fin 2 → ℝ)) t) := by
  have htraj : pigouShifted.IsReplicatorTrajectory (fun y => (pigouShifted.cost y)⁻¹)
      (fun _ => ![1, 0]) := fun t _ p => by
    have hzero : pigouShifted.replicatorDrift (fun y => (pigouShifted.cost y)⁻¹) ![1, 0] p = 0 := by
      unfold replicatorDrift
      rw [pigouShifted_cost, pigouShifted_pathLatency]
      fin_cases p <;> norm_num
    rw [hzero]
    exact hasDerivWithinAt_const t (Ici 0) _
  have hcont : ∀ e : Fin 2, Continuous (pigouShifted.latency e) := fun e => by
    fin_cases e
    · exact continuous_id.add continuous_const
    · exact continuous_const
  exact htraj.isFeasible_relative rfl (by norm_num : (0 : ℝ) < 7 / 4)
    (fun y hy => pigouShifted_cost_ge hy) hcont pigouShifted_isWardrop_pure0.1

/-- Non-vacuity of Theorem 29.12, global trajectory existence, uniqueness, strict support
preservation, and Lyapunov potential monotonicity on `pigouShifted` from `![1 / 2, 1 / 2]`. -/
theorem pigouShifted_theorem29_12 :
    ∃ x : ℝ → Fin 2 → ℝ,
      x 0 = ![1 / 2, 1 / 2] ∧
      pigouShifted.IsReplicatorTrajectory (fun y => (pigouShifted.cost y)⁻¹) x ∧
      (∀ t ≥ 0, pigouShifted.IsFeasible (x t)) ∧
      (∀ t ≥ 0, 0 < x t 0 ∧ 0 < x t 1) ∧
      AntitoneOn (fun t => pigouShifted.potential (7 / 4) (x t)) (Ici 0) ∧
      (∀ y, pigouShifted.IsReplicatorTrajectory (fun z => (pigouShifted.cost z)⁻¹) y →
        (∀ t ≥ 0, pigouShifted.IsFeasible (y t)) → y 0 = ![1 / 2, 1 / 2] → EqOn x y (Ici 0)) ∧
      ∀ ε > 0, ∃ t ∈ Icc (0 : ℝ) (2 / ε ^ 3 * Real.log (16 / 7)),
        pigouShifted.IsApproxEquilibrium ε (x t) := by
  have hlMax : pigouShifted.cost ![1 / 2, 1 / 2] ≤ 2 := by
    rw [pigouShifted_cost]; norm_num
  obtain ⟨x, hx0, hxtraj, hxfeas, hconv⟩ :=
    exists_relativeReplicatorTrajectory_isApproxEquilibrium (G := pigouShifted) rfl
      pigouShifted_nonneg pigouShifted_mono pigouShifted_lip
      (lStar := 7 / 4) (lMax := 2) (by norm_num) (fun y hy => pigouShifted_cost_ge hy)
      pigouShifted_isFeasible_half hlMax
  have hcont : ∀ e : Fin 2, Continuous (pigouShifted.latency e) := fun e => by
    fin_cases e
    · exact continuous_id.add continuous_const
    · exact continuous_const
  have hlam_cont : ContinuousOn (fun t => (pigouShifted.cost (x t))⁻¹) (Ici 0) := by
    have hx_cont : ∀ p, ContinuousOn (fun t => x t p) (Ici 0) :=
      fun p t ht => (hxtraj t ht p).continuousWithinAt
    have hcost_cont : ContinuousOn (fun t => pigouShifted.cost (x t)) (Ici 0) := by
      have h0 := hx_cont 0
      have h1 := hx_cont 1
      have heq : (fun t => pigouShifted.cost (x t)) =
          fun t => x t 0 * (x t 0 + 1) + x t 1 * 2 := funext fun t => pigouShifted_cost (x t)
      rw [heq]
      fun_prop
    exact hcost_cont.inv₀ fun t ht => by linarith [pigouShifted_cost_ge (hxfeas t ht)]
  have hpos : ∀ t ≥ 0, 0 < x t 0 ∧ 0 < x t 1 := fun t ht =>
    ⟨hxtraj.pos_of_pos hlam_cont hcont (by rw [hx0]; norm_num) ht,
      hxtraj.pos_of_pos hlam_cont hcont (by rw [hx0]; norm_num) ht⟩
  have hanti : AntitoneOn (fun t => pigouShifted.potential (7 / 4) (x t)) (Ici 0) :=
    antitoneOn_potential rfl hxtraj hxfeas
      (fun t ht => inv_nonneg.2 (by linarith [pigouShifted_cost_ge (hxfeas t ht)]))
      (fun e => (hcont e).continuousOn) (7 / 4)
  have huniq : ∀ y, pigouShifted.IsReplicatorTrajectory (fun z => (pigouShifted.cost z)⁻¹) y →
      (∀ t ≥ 0, pigouShifted.IsFeasible (y t)) → y 0 = ![1 / 2, 1 / 2] → EqOn x y (Ici 0) :=
    fun y hy hyfeas hy0 =>
      eqOn_of_isRelativeReplicatorTrajectory rfl pigouShifted_nonneg pigouShifted_lip
        (by norm_num : (0 : ℝ) < 7 / 4) (fun z hz => pigouShifted_cost_ge hz)
        hxtraj hxfeas hy hyfeas (hx0.trans hy0.symm)
  refine ⟨x, hx0, hxtraj, hxfeas, hpos, hanti, huniq, fun ε hε => ?_⟩
  have hratio : (2 * (2 : ℝ)) / (7 / 4) = 16 / 7 := by norm_num
  simpa only [hratio] using hconv ε hε

/-! ### Nonlinear polynomial latency network (`u ^ 2 + 1`, only Lipschitz on `[0, 1]`) -/

/-- Parallel-link network with nonlinear latency `u ^ 2 + 1` on link `0` and constant latency `2`
on link `1`: `u ↦ u ^ 2 + 1` is neither monotone nor Lipschitz on `ℝ`, only on `[0, 1]`. -/
def quadraticShifted : NonatomicCongestionGame Unit (Fin 2) (Fin 2) where
  commodity _ := ()
  resources p := {p}
  rate _ := 1
  latency e u := if e = 0 then u ^ 2 + 1 else 2

theorem quadraticShifted_theorem29_12 :
    ∃ x : ℝ → Fin 2 → ℝ,
      x 0 = ![1 / 2, 1 / 2] ∧
      quadraticShifted.IsReplicatorTrajectory (fun y => (quadraticShifted.cost y)⁻¹) x ∧
      (∀ t ≥ 0, quadraticShifted.IsFeasible (x t)) ∧
      ∀ ε > 0, ∃ t ∈ Icc (0 : ℝ) (2 / ε ^ 3 * Real.log 4),
        quadraticShifted.IsApproxEquilibrium ε (x t) := by
  have hedge : ∀ f e, quadraticShifted.edgeFlow f e = f e := fun f e => by
    simp only [edgeFlow, quadraticShifted, Finset.mem_singleton, Finset.filter_eq, Finset.mem_univ,
      ↓reduceIte, Finset.sum_singleton]
  have hcost : ∀ f, quadraticShifted.cost f = f 0 * (f 0 ^ 2 + 1) + f 1 * 2 := fun f => by
    simp only [cost, pathLatency, hedge]
    rw [Fin.sum_univ_two]
    simp [quadraticShifted]
  have hmin : ∀ y, quadraticShifted.IsFeasible y → (1 : ℝ) ≤ quadraticShifted.cost y := by
    intro y hy
    obtain ⟨hnn, hsum⟩ := (isFeasible_unit_iff rfl).1 hy
    rw [Fin.forall_fin_two] at hnn
    rw [Fin.sum_univ_two] at hsum
    rw [hcost]
    nlinarith [sq_nonneg (y 0)]
  have hfeas0 : quadraticShifted.IsFeasible ![1 / 2, 1 / 2] :=
    (isFeasible_unit_iff rfl).2
      ⟨fun p => by fin_cases p <;> norm_num, by rw [Fin.sum_univ_two]; norm_num⟩
  have hnonneg : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ quadraticShifted.latency e u := fun e u _ => by
    fin_cases e
    · change 0 ≤ u ^ 2 + 1; nlinarith [sq_nonneg u]
    · change (0 : ℝ) ≤ 2; norm_num
  have hmono : ∀ e, MonotoneOn (quadraticShifted.latency e) (Icc 0 1) := fun e a ha b _ hab => by
    fin_cases e
    · change a ^ 2 + 1 ≤ b ^ 2 + 1; nlinarith [ha.1]
    · change (2 : ℝ) ≤ 2; exact le_rfl
  have hlip : ∀ e, ∃ K, LipschitzOnWith K (quadraticShifted.latency e) (Icc 0 1) := fun e => by
    fin_cases e
    · refine ⟨2, LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
      change |a ^ 2 + 1 - (b ^ 2 + 1)| ≤ (2 : NNReal) * |a - b|
      have hfac : a ^ 2 + 1 - (b ^ 2 + 1) = (a + b) * (a - b) := by ring
      rw [hfac, abs_mul, abs_of_nonneg (by linarith [ha.1, hb.1])]
      exact mul_le_mul_of_nonneg_right (by norm_num; linarith [ha.2, hb.2]) (abs_nonneg _)
    · refine ⟨0, LipschitzOnWith.of_dist_le_mul fun a _ b _ => ?_⟩
      change |(2 : ℝ) - 2| ≤ (0 : NNReal) * |a - b|
      simp only [sub_self, abs_zero, NNReal.coe_zero, zero_mul, le_rfl]
  have hlMax : quadraticShifted.cost ![1 / 2, 1 / 2] ≤ 2 := by
    rw [hcost]; norm_num
  have hres := exists_relativeReplicatorTrajectory_isApproxEquilibrium (G := quadraticShifted) rfl
    hnonneg hmono hlip (lStar := 1) (lMax := 2) zero_lt_one hmin hfeas0 hlMax
  have h4 : (2 * (2 : ℝ)) / 1 = 4 := by norm_num
  simpa only [h4] using hres

/-! ### Model boundary: zero-cost Wardrop equilibrium fails Definition 29.11 -/

/-- Two parallel links with identically zero latency. -/
def zeroRouting : NonatomicCongestionGame Unit (Fin 2) (Fin 2) where
  commodity _ := ()
  resources p := {p}
  rate _ := 1
  latency _ _ := 0

/-- At zero average latency, `![1, 0]` is a Wardrop equilibrium yet fails
`IsApproxEquilibrium (1 / 2) ![1, 0]` because `l_p(x) ≥ (1 + ε) · 0` holds on every path,
showing `0 < G.cost x` cannot be dropped from `IsWardrop.isApproxEquilibrium`. -/
theorem zeroRouting_isWardrop_and_not_isApproxEquilibrium :
    zeroRouting.IsWardrop ![1, 0] ∧ ¬ zeroRouting.IsApproxEquilibrium (1 / 2) ![1, 0] := by
  have hlat : ∀ p, zeroRouting.pathLatency ![1, 0] p = 0 := fun p => by
    unfold pathLatency; simp only [zeroRouting, Finset.sum_const_zero]
  have hcost : zeroRouting.cost ![1, 0] = 0 := by
    unfold cost; simp only [hlat, mul_zero, Finset.sum_const_zero]
  have hfeas : zeroRouting.IsFeasible ![1, 0] :=
    (isFeasible_unit_iff rfl).2
      ⟨fun p => by fin_cases p <;> norm_num, by rw [Fin.sum_univ_two]; norm_num⟩
  refine ⟨⟨hfeas, fun p q _ _ => by rw [hlat p, hlat q]⟩, ?_⟩
  rintro ⟨-, hle⟩
  have huniv : Finset.univ.filter
      (fun p : Fin 2 => (1 + 1 / 2) * zeroRouting.cost ![1, 0] ≤
        zeroRouting.pathLatency ![1, 0] p) = Finset.univ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcost, mul_zero, hlat, le_rfl]
  rw [huniv, Fin.sum_univ_two] at hle
  norm_num at hle

end CslibFrontierTests.GameTheory.EvolutionaryRoutingDynamics
