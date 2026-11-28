/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.Nonatomic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Evolutionary dynamics applied to selfish routing

This module formalizes [Suri2007], Section 29.3 (pp. 723–728) and Exercise 29.6 (p. 736),
analyzing imitative (replicator) evolutionary dynamics on single-commodity nonatomic selfish
routing games.

We reuse `Cslib.GameTheory.NonatomicCongestionGame Unit P E` with unit traffic rate
`G.rate () = 1`. In this setting:

* `G.IsFeasible x` means `(∀ p, 0 ≤ x p) ∧ ∑ p, x p = 1`;
* `G.edgeFlow x e` is the total load on edge `e`, lying in `[0, 1]` for feasible flows;
* `G.pathLatency x p` is the latency `l_p(x) = ∑ e ∈ G.resources p, G.latency e (G.edgeFlow x e)`;
* `G.cost x` is the average latency `l̄(x) = ∑ p, x p * G.pathLatency x p`;
* `G.IsWardrop x` is precisely a Nash flow ([Suri2007], Definition 29.10, p. 724).

Under the pairwise imitative dynamics of Equation (29.1), agents on path `p` switch to a randomly
sampled lower-latency path `q` at rate proportional to `lam x * (l_p(x) - l_q(x))`. For any flow
summing to `1`, this pairwise drift equals the replicator drift `lam x * x p * (l̄(x) - l_p(x))`
of Equation (29.2) (`imitativeDrift_eq_replicatorDrift`).

With the relative rate `lam x = (G.cost x)⁻¹` ([Suri2007], p. 725), nonnegative nondecreasing
Lipschitz latencies on `[0, 1]`, and positive minimum feasible average latency `0 < lStar`,
a global trajectory on `[0, ∞)` exists uniquely from every feasible initial flow
(`exists_relativeReplicatorTrajectory`, `eqOn_of_isRelativeReplicatorTrajectory`), remains
feasible for all `t ≥ 0` (Exercise 29.6), decreases the shifted Beckmann potential `G.potential`
of Equation (29.3) monotonically (`hasDerivWithinAt_potential`, `antitoneOn_potential`), and
reaches an `ε`-approximate equilibrium (Definition 29.11) within time
`2 / ε ^ 3 * Real.log (2 * lMax / lStar) = O(ε⁻³ ln(l_max / l*))` ([Suri2007], Theorem 29.12).

## Main definitions

* `Cslib.GameTheory.NonatomicCongestionGame.imitativeDrift`: pairwise imitative drift
  ([Suri2007], Equation 29.1, p. 724).
* `Cslib.GameTheory.NonatomicCongestionGame.replicatorDrift`: replicator drift
  ([Suri2007], Equation 29.2, p. 724).
* `Cslib.GameTheory.NonatomicCongestionGame.IsReplicatorTrajectory`: trajectories on `[0, ∞)`
  solving the replicator differential equation (29.2).
* `Cslib.GameTheory.NonatomicCongestionGame.IsApproxEquilibrium`: `ε`-approximate equilibrium
  ([Suri2007], Definition 29.11, p. 726).
* `Cslib.GameTheory.NonatomicCongestionGame.potential`: shifted Beckmann potential `Φ`
  ([Suri2007], Equation 29.3, p. 726).

## Main results

* `Cslib.GameTheory.NonatomicCongestionGame.imitativeDrift_eq_replicatorDrift`: algebraic
  equivalence of Equations (29.1) and (29.2) ([Suri2007], pp. 724–725).
* `Cslib.GameTheory.NonatomicCongestionGame.sum_replicatorDrift_eq_zero`,
  `Cslib.GameTheory.NonatomicCongestionGame.IsReplicatorTrajectory.isFeasible`,
  `Cslib.GameTheory.NonatomicCongestionGame.IsReplicatorTrajectory.isFeasible_relative`:
  zero drift sum and all-time feasibility invariance ([Suri2007], Exercise 29.6, p. 736).
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.isApproxEquilibrium`: every Wardrop
  equilibrium with positive average latency is an `ε`-approximate equilibrium for every `ε > 0`.
* `Cslib.GameTheory.NonatomicCongestionGame.hasDerivWithinAt_potential`,
  `Cslib.GameTheory.NonatomicCongestionGame.antitoneOn_potential`: exact time derivative of `Φ`
  ([Suri2007], Equation 29.4, p. 727) and Lyapunov monotonicity ([Suri2007], Section 29.3.2).
* `Cslib.GameTheory.NonatomicCongestionGame.exists_relativeReplicatorTrajectory`,
  `Cslib.GameTheory.NonatomicCongestionGame.eqOn_of_isRelativeReplicatorTrajectory`: global
  existence and uniqueness of relative-rate replicator trajectories on `[0, ∞)` under Lipschitz
  latencies on `[0, 1]`.
* `Cslib.GameTheory.NonatomicCongestionGame.IsReplicatorTrajectory`:
  `exists_mem_Icc_isApproxEquilibrium` (trajectory hitting time) and
  `exists_relativeReplicatorTrajectory_isApproxEquilibrium` (existential global trajectory):
  convergence (hitting time) to an `ε`-approximate equilibrium in time
  `2 / ε ^ 3 * Real.log (2 * lMax / lStar)` ([Suri2007], Theorem 29.12, pp. 727–728).

## References

* [S. Suri, *Computational Evolutionary Game Theory*][Suri2007]
-/

public section

namespace Cslib.GameTheory.NonatomicCongestionGame

open Set MeasureTheory
open scoped NNReal Topology

section Definitions

variable {P E : Type*} [Fintype P] [DecidableEq E] (G : NonatomicCongestionGame Unit P E)

/-- The pairwise **imitative drift** on path `p` ([Suri2007], Equation 29.1, p. 724): agents on `p`
switch to lower-latency paths `q` and agents on higher-latency paths `q` switch to `p`, each at
rate proportional to `lam x` times the latency difference. -/
@[expose] noncomputable def imitativeDrift (lam : (P → ℝ) → ℝ) (x : P → ℝ) (p : P) : ℝ :=
  -(x p * ∑ q with G.pathLatency x q < G.pathLatency x p,
      x q * lam x * (G.pathLatency x p - G.pathLatency x q)) +
    ∑ q with G.pathLatency x p < G.pathLatency x q,
      x p * x q * lam x * (G.pathLatency x q - G.pathLatency x p)

/-- The **replicator drift** on path `p` ([Suri2007], Equation 29.2, p. 724):
`lam x * x p * (G.cost x - G.pathLatency x p)`. -/
@[expose] def replicatorDrift (lam : (P → ℝ) → ℝ) (x : P → ℝ) (p : P) : ℝ :=
  lam x * x p * (G.cost x - G.pathLatency x p)

/-- A trajectory `x : ℝ → P → ℝ` follows the **replicator dynamics** with rate `lam` on `[0, ∞)`
([Suri2007], Equation 29.2, pp. 724–725) when every path coordinate `t ↦ x t p` has derivative
within `[0, ∞)` equal to `G.replicatorDrift lam (x t) p` at every `t ≥ 0`. -/
@[expose] def IsReplicatorTrajectory (lam : (P → ℝ) → ℝ) (x : ℝ → P → ℝ) : Prop :=
  ∀ t ∈ Ici (0 : ℝ), ∀ p,
    HasDerivWithinAt (fun s => x s p) (G.replicatorDrift lam (x t) p) (Ici 0) t

/-- A feasible flow `x` is an **`ε`-approximate equilibrium** ([Suri2007], Definition 29.11,
p. 726) if at most an `ε` fraction of flow uses paths whose latency is at least
`(1 + ε) * G.cost x`.

Note: because Definition 29.11 uses the non-strict inequality `l_p(x) ≥ (1 + ε) l̄(x)`, a zero-cost
flow (`G.cost x = 0`) places every nonnegative-latency path in `P_ε`, giving total weight `1`, so
even a Wardrop equilibrium fails `IsApproxEquilibrium` when `G.cost x = 0` and `0 < ε < 1`. -/
@[expose] noncomputable def IsApproxEquilibrium (ε : ℝ) (x : P → ℝ) : Prop :=
  G.IsFeasible x ∧ ∑ p with (1 + ε) * G.cost x ≤ G.pathLatency x p, x p ≤ ε

/-- The shifted Beckmann **potential function** `Φ(x) = lStar + ∑ e, ∫₀^{x_e} l_e(u) du`
([Suri2007], Equation 29.3, p. 726), where `lStar` is a lower bound on the average latency of
feasible flows (in the source, `l* = min_x l̄(x)`). -/
@[expose] noncomputable def potential [Fintype E] (lStar : ℝ) (x : P → ℝ) : ℝ :=
  lStar + ∑ e, ∫ u in (0 : ℝ)..G.edgeFlow x e, G.latency e u

end Definitions

/-! ### Single-commodity feasibility and drift identities -/

section Algebra

variable {P E : Type*} [Fintype P] [DecidableEq E] {G : NonatomicCongestionGame Unit P E}

omit [DecidableEq E] in
/-- For a single-commodity game with unit rate `G.rate () = 1`, feasibility means nonnegative path
flows summing to `1`. -/
theorem isFeasible_unit_iff (h1 : G.rate () = 1) {x : P → ℝ} :
    G.IsFeasible x ↔ (∀ p, 0 ≤ x p) ∧ ∑ p, x p = 1 := by
  simp only [IsFeasible, Unique.forall_iff, h1, Finset.filter_true]

private theorem edgeFlow_mem_Icc_of_isFeasible (h1 : G.rate () = 1) {x : P → ℝ}
    (hx : G.IsFeasible x) (e : E) : G.edgeFlow x e ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hnn, hsum⟩ := (isFeasible_unit_iff h1).1 hx
  refine ⟨Finset.sum_nonneg fun p _ => hnn p, ?_⟩
  calc G.edgeFlow x e
      = ∑ p with e ∈ G.resources p, x p := rfl
    _ ≤ ∑ p, x p := Finset.sum_le_univ_sum_of_nonneg hnn
    _ = 1 := hsum

private theorem pathLatency_nonneg_of_isFeasible (h1 : G.rate () = 1)
    (hnonneg : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ G.latency e u) {x : P → ℝ}
    (hx : G.IsFeasible x) (p : P) : 0 ≤ G.pathLatency x p :=
  Finset.sum_nonneg fun e _ => hnonneg e _ (edgeFlow_mem_Icc_of_isFeasible h1 hx e)

/-- **Equivalence of pairwise imitative dynamics and replicator dynamics** ([Suri2007],
Equations 29.1–29.2, pp. 724–725): whenever `∑ q, x q = 1`, the pairwise imitative drift equals
the replicator drift `lam x * x p * (G.cost x - G.pathLatency x p)`. -/
theorem imitativeDrift_eq_replicatorDrift (lam : (P → ℝ) → ℝ) {x : P → ℝ}
    (hsum : ∑ q, x q = 1) (p : P) :
    G.imitativeDrift lam x p = G.replicatorDrift lam x p := by
  classical
  unfold imitativeDrift replicatorDrift cost
  have hsplit : ∑ q : P, x p * x q * lam x * (G.pathLatency x q - G.pathLatency x p) =
      -(x p * ∑ q with G.pathLatency x q < G.pathLatency x p,
          x q * lam x * (G.pathLatency x p - G.pathLatency x q)) +
        ∑ q with G.pathLatency x p < G.pathLatency x q,
          x p * x q * lam x * (G.pathLatency x q - G.pathLatency x p) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    have h1 : (∑ q with G.pathLatency x q < G.pathLatency x p,
          -(x p * (x q * lam x * (G.pathLatency x p - G.pathLatency x q)))) =
        ∑ q with G.pathLatency x q < G.pathLatency x p,
          x p * x q * lam x * (G.pathLatency x q - G.pathLatency x p) :=
      Finset.sum_congr rfl fun q _ => by ring
    rw [h1]
    have hdisj : Disjoint
        (Finset.univ.filter fun q => G.pathLatency x q < G.pathLatency x p)
        (Finset.univ.filter fun q => G.pathLatency x p < G.pathLatency x q) :=
      Finset.disjoint_filter.2 fun _ _ hlt hgt => hlt.not_gt hgt
    rw [← Finset.sum_union hdisj]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun q _ hq => ?_
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_lt] at hq
    rw [le_antisymm hq.2 hq.1, sub_self, mul_zero]
  rw [← hsplit]
  calc ∑ q : P, x p * x q * lam x * (G.pathLatency x q - G.pathLatency x p)
      = ∑ q : P, (lam x * x p * (x q * G.pathLatency x q) -
          lam x * x p * G.pathLatency x p * x q) :=
        Finset.sum_congr rfl fun q _ => by ring
    _ = lam x * x p * (∑ q, x q * G.pathLatency x q) -
          lam x * x p * G.pathLatency x p * (∑ q, x q) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = lam x * x p * ((∑ q, x q * G.pathLatency x q) - G.pathLatency x p) := by
        rw [hsum]; ring

/-- For any vector `x : P → ℝ`, the sum of replicator drifts equals
`lam x * G.cost x * ((∑ p, x p) - 1)`. -/
private theorem sum_replicatorDrift (lam : (P → ℝ) → ℝ) (x : P → ℝ) :
    ∑ p, G.replicatorDrift lam x p = lam x * G.cost x * ((∑ p, x p) - 1) := by
  calc ∑ p, G.replicatorDrift lam x p
      = ∑ p, (lam x * G.cost x * x p - lam x * (x p * G.pathLatency x p)) :=
        Finset.sum_congr rfl fun p _ => by unfold replicatorDrift; ring
    _ = lam x * G.cost x * (∑ p, x p) - lam x * G.cost x := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; rfl
    _ = lam x * G.cost x * ((∑ p, x p) - 1) := by ring

/-- **Zero total drift** ([Suri2007], Exercise 29.6, first part, p. 736): whenever the path flows
sum to `1`, the replicator drifts of Equation (29.2) sum to `0`. -/
theorem sum_replicatorDrift_eq_zero (lam : (P → ℝ) → ℝ) {x : P → ℝ} (hsum : ∑ p, x p = 1) :
    ∑ p, G.replicatorDrift lam x p = 0 := by
  rw [sum_replicatorDrift, hsum, sub_self, mul_zero]

/-- **Every positive-cost Wardrop equilibrium is an `ε`-approximate equilibrium** for all `ε > 0`,
linking Definition 29.10 (`IsWardrop`) to Definition 29.11 (`IsApproxEquilibrium`, [Suri2007],
pp. 724–726). The hypothesis `0 < G.cost x` is necessary when `0 < ε < 1`, because a zero-cost
flow has `l_p(x) ≥ (1 + ε) · 0` on every path. -/
theorem IsWardrop.isApproxEquilibrium (h1 : G.rate () = 1) {x : P → ℝ} (hx : G.IsWardrop x)
    (hcost : 0 < G.cost x) {ε : ℝ} (hε : 0 < ε) : G.IsApproxEquilibrium ε x := by
  refine ⟨hx.1, ?_⟩
  obtain ⟨hnn, hsum⟩ := (isFeasible_unit_iff h1).1 hx.1
  have hzero : ∀ p ∈ Finset.univ.filter (fun p => (1 + ε) * G.cost x ≤ G.pathLatency x p),
      x p = 0 := by
    intro p hp
    have hlat : (1 + ε) * G.cost x ≤ G.pathLatency x p := (Finset.mem_filter.mp hp).2
    by_contra hne
    have hpos : 0 < x p := lt_of_le_of_ne (hnn p) (Ne.symm hne)
    have hle : ∀ q, G.pathLatency x p ≤ G.pathLatency x q :=
      fun q => hx.2 p q rfl hpos
    have hcost_ge : G.pathLatency x p ≤ G.cost x := by
      calc G.pathLatency x p
          = (∑ q, x q) * G.pathLatency x p := by rw [hsum, one_mul]
        _ = ∑ q, x q * G.pathLatency x p := Finset.sum_mul _ _ _
        _ ≤ ∑ q, x q * G.pathLatency x q :=
          Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hle q) (hnn q)
        _ = G.cost x := rfl
    nlinarith
  rw [Finset.sum_eq_zero hzero]
  exact hε.le

end Algebra

/-! ### Exercise 29.6: flow-feasibility and positivity invariance -/

section Invariance

variable {P E : Type*} [Fintype P] [DecidableEq E] {G : NonatomicCongestionGame Unit P E}

/-- Integrating factor for a linear homogeneous scalar ODE `y'(t) = h(t) * y(t)` on `[0, T]`. -/
private theorem eq_mul_exp_integral_of_hasDerivWithinAt {T : ℝ} (hT : 0 ≤ T) {y h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc 0 T))
    (hy : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt y (h t * y t) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    y t = y 0 * Real.exp (∫ u in (0 : ℝ)..t, h u) := by
  let H : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, h u
  have hH : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt H (h s) (Icc 0 T) s := fun s hs => by
    have : Fact (s ∈ Icc (0 : ℝ) T) := ⟨hs⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right
      (hh.mono (uIcc_subset_Icc ⟨le_rfl, hT⟩ hs)).intervalIntegrable
      (hh.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s)
      (hh s hs)
  have hz : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => y u * Real.exp (-H u)) 0 (Icc 0 T) s := fun s hs => by
    have hmul := (hy s hs).mul (hH s hs).neg.exp
    convert hmul using 1
    ring
  have hnorm := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le (C := (0 : ℝ))
    hz (fun _ _ => by simp only [norm_zero, le_rfl]) ⟨le_rfl, hT⟩ ht
  simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at hnorm
  have hH0 : H 0 = 0 := intervalIntegral.integral_same
  rw [hH0, neg_zero, Real.exp_zero, mul_one] at hnorm
  calc y t
      = (y t * Real.exp (-H t)) * Real.exp (H t) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = y 0 * Real.exp (H t) := by rw [hnorm]

private theorem continuousOn_trajectory {lam : (P → ℝ) → ℝ} {x : ℝ → P → ℝ}
    (hx : G.IsReplicatorTrajectory lam x) (p : P) :
    ContinuousOn (fun t => x t p) (Ici 0) :=
  fun t ht => (hx t ht p).continuousWithinAt

private theorem isFeasible_on_Icc (h1 : G.rate () = 1) {lam : (P → ℝ) → ℝ} {x : ℝ → P → ℝ}
    {T : ℝ} (hT : 0 ≤ T)
    (hx : ∀ t ∈ Icc (0 : ℝ) T, ∀ p,
      HasDerivWithinAt (fun s => x s p) (G.replicatorDrift lam (x t) p) (Icc 0 T) t)
    (h0 : G.IsFeasible (x 0))
    (hlam : ContinuousOn (fun t => lam (x t)) (Icc 0 T))
    (hlat : ∀ e, ContinuousOn (fun t => G.latency e (G.edgeFlow (x t) e)) (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, G.IsFeasible (x t) := by
  have hx_cont : ∀ p, ContinuousOn (fun t => x t p) (Icc 0 T) :=
    fun p t ht => (hx t ht p).continuousWithinAt
  have hpath_cont : ∀ p, ContinuousOn (fun t => G.pathLatency (x t) p) (Icc 0 T) := fun p => by
    unfold pathLatency; fun_prop
  have hcost_cont : ContinuousOn (fun t => G.cost (x t)) (Icc 0 T) := by
    unfold cost; fun_prop
  obtain ⟨hnn0, hsum0⟩ := (isFeasible_unit_iff h1).1 h0
  intro t ht
  rw [isFeasible_unit_iff h1]
  refine ⟨fun p => ?_, ?_⟩
  · have hcoord := eq_mul_exp_integral_of_hasDerivWithinAt hT
      (hlam.fun_mul (hcost_cont.fun_sub (hpath_cont p)))
      (fun s hs => by
        convert hx s hs p using 1
        unfold replicatorDrift; ring)
      ht
    rw [hcoord]
    exact mul_nonneg (hnn0 p) (Real.exp_pos _).le
  · have hsum_deriv : ∀ s ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun u => (∑ p, x u p) - 1)
          (lam (x s) * G.cost (x s) * ((∑ p, x s p) - 1)) (Icc 0 T) s := fun s hs => by
      have hd := (HasDerivWithinAt.fun_sum (u := Finset.univ) fun p _ => hx s hs p).sub
        (hasDerivWithinAt_const s (Icc 0 T) (1 : ℝ))
      rw [sub_zero, sum_replicatorDrift] at hd
      exact hd
    have hsum_eq := eq_mul_exp_integral_of_hasDerivWithinAt hT
      (hlam.fun_mul hcost_cont) hsum_deriv ht
    rw [hsum0, sub_self, zero_mul] at hsum_eq
    linarith

/-- **Strict support preservation** along replicator dynamics: any path carrying positive flow at
time `0` carries positive flow at every `t ≥ 0`. -/
theorem IsReplicatorTrajectory.pos_of_pos {lam : (P → ℝ) → ℝ} {x : ℝ → P → ℝ}
    (hx : G.IsReplicatorTrajectory lam x)
    (hlam : ContinuousOn (fun t => lam (x t)) (Ici 0))
    (hlat : ∀ e, Continuous (G.latency e)) {p : P} (hp : 0 < x 0 p) {t : ℝ} (ht : 0 ≤ t) :
    0 < x t p := by
  have hsub : Icc (0 : ℝ) t ⊆ Ici 0 := fun _ hs => hs.1
  have hx_cont : ∀ q, ContinuousOn (fun s => x s q) (Icc 0 t) :=
    fun q => (continuousOn_trajectory hx q).mono hsub
  have hlat_cont : ∀ e, ContinuousOn (fun s => G.latency e (G.edgeFlow (x s) e)) (Icc 0 t) :=
    fun e => (hlat e).comp_continuousOn (by unfold edgeFlow; fun_prop)
  have hpath_cont : ∀ q, ContinuousOn (fun s => G.pathLatency (x s) q) (Icc 0 t) := fun q => by
    unfold pathLatency; fun_prop
  have hcost_cont : ContinuousOn (fun s => G.cost (x s)) (Icc 0 t) := by
    unfold cost; fun_prop
  have hcoord := eq_mul_exp_integral_of_hasDerivWithinAt ht
    ((hlam.mono hsub).fun_mul (hcost_cont.fun_sub (hpath_cont p)))
    (fun s hs => by
      convert (hx s hs.1 p).mono hsub using 1
      unfold replicatorDrift; ring)
    ⟨ht, le_rfl⟩
  rw [hcoord]
  exact mul_pos hp (Real.exp_pos _)

/-- **All-time feasibility invariance** ([Suri2007], Exercise 29.6, p. 736): if a trajectory of
Equation (29.2) with continuous latencies and continuous rate function `t ↦ lam (x t)` starts from
a feasible flow, it remains feasible for all `t ≥ 0`. -/
theorem IsReplicatorTrajectory.isFeasible (h1 : G.rate () = 1) {lam : (P → ℝ) → ℝ}
    {x : ℝ → P → ℝ} (hx : G.IsReplicatorTrajectory lam x) (h0 : G.IsFeasible (x 0))
    (hlam : ContinuousOn (fun t => lam (x t)) (Ici 0))
    (hlat : ∀ e, Continuous (G.latency e)) :
    ∀ t ≥ 0, G.IsFeasible (x t) := fun t ht => by
  have hsub : Icc (0 : ℝ) t ⊆ Ici 0 := fun _ hs => hs.1
  have hx_cont : ∀ q, ContinuousOn (fun s => x s q) (Icc 0 t) :=
    fun q => (continuousOn_trajectory hx q).mono hsub
  exact isFeasible_on_Icc h1 ht (fun s hs p => (hx s hs.1 p).mono hsub) h0 (hlam.mono hsub)
    (fun e => (hlat e).comp_continuousOn (by unfold edgeFlow; fun_prop))
    t ⟨ht, le_rfl⟩

/-- **All-time feasibility invariance for the relative-rate dynamics** `λ(x) = l̄(x)⁻¹`
([Suri2007], p. 725 and Exercise 29.6, p. 736): when every feasible flow has average latency at
least `lStar > 0` and latencies are continuous, any relative-rate replicator trajectory starting
from a feasible flow remains feasible (and maintains `G.cost (x t) ≥ lStar > 0`) for all `t ≥ 0`,
without assuming continuity of `(G.cost ∘ x)⁻¹` a priori. -/
theorem IsReplicatorTrajectory.isFeasible_relative (h1 : G.rate () = 1) {lStar : ℝ}
    (hlStar : 0 < lStar) (hmin : ∀ y, G.IsFeasible y → lStar ≤ G.cost y)
    (hlat : ∀ e, Continuous (G.latency e)) {x : ℝ → P → ℝ}
    (hx : G.IsReplicatorTrajectory (fun y => (G.cost y)⁻¹) x) (h0 : G.IsFeasible (x 0)) :
    ∀ t ≥ 0, G.IsFeasible (x t) := by
  have hx_cont : ∀ p, ContinuousOn (fun t => x t p) (Ici 0) := continuousOn_trajectory hx
  have hlat_cont : ∀ e, ContinuousOn (fun t => G.latency e (G.edgeFlow (x t) e)) (Ici 0) :=
    fun e => (hlat e).comp_continuousOn (by unfold edgeFlow; fun_prop)
  have hcost_cont : ContinuousOn (fun t => G.cost (x t)) (Ici 0) := by
    unfold cost pathLatency; fun_prop
  have hpos_all : ∀ t ∈ Ici (0 : ℝ), lStar / 2 < G.cost (x t) := by
    by_contra h
    push Not at h
    let S : Set ℝ := {t | 0 ≤ t ∧ G.cost (x t) ≤ lStar / 2}
    have hSne : S.Nonempty := h
    have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
    have hSclosed : IsClosed S := by
      have h1' : IsClosed (Ici (0 : ℝ)) := isClosed_Ici
      exact hcost_cont.preimage_isClosed_of_isClosed h1' isClosed_Iic
    let T := sInf S
    have hTmem : T ∈ S := hSclosed.csInf_mem hSne hSbdd
    have hT0 : 0 ≤ T := hTmem.1
    have hTle : G.cost (x T) ≤ lStar / 2 := hTmem.2
    have hTpos : 0 < T := by
      rcases hT0.eq_or_lt with h0T | hpos
      · have h0cost : lStar ≤ G.cost (x 0) := hmin (x 0) h0
        rw [← h0T] at hTle
        linarith
      · exact hpos
    have hgt_Ico : ∀ s ∈ Ico (0 : ℝ) T, lStar / 2 < G.cost (x s) := by
      intro s hs
      by_contra hle
      push Not at hle
      exact (csInf_le hSbdd ⟨hs.1, hle⟩).not_gt hs.2
    have hge_T : lStar / 2 ≤ G.cost (x T) := by
      have hsub : Ico (0 : ℝ) T ⊆ Ici 0 := fun _ hs => hs.1
      have htend : Filter.Tendsto (fun s => G.cost (x s)) (𝓝[Ico 0 T] T) (𝓝 (G.cost (x T))) :=
        (hcost_cont T hT0).mono hsub
      have : (𝓝[Ico (0 : ℝ) T] T).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hTpos.ne]
        exact ⟨hT0, le_rfl⟩
      exact ge_of_tendsto htend (Filter.eventually_of_mem self_mem_nhdsWithin fun s hs =>
        (hgt_Ico s hs).le)
    have hne_Icc : ∀ s ∈ Icc (0 : ℝ) T, G.cost (x s) ≠ 0 := fun s hs => by
      rcases hs.2.lt_or_eq with hlt | rfl
      · linarith [hgt_Ico s ⟨hs.1, hlt⟩]
      · linarith
    have hsubT : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ hs => hs.1
    have hfeasT : G.IsFeasible (x T) :=
      isFeasible_on_Icc h1 hT0 (fun s hs p => (hx s hs.1 p).mono hsubT) h0
        ((hcost_cont.mono hsubT).inv₀ hne_Icc) (fun e => (hlat_cont e).mono hsubT)
        T ⟨hT0, le_rfl⟩
    linarith [hmin (x T) hfeasT]
  exact hx.isFeasible h1 h0 (hcost_cont.inv₀ fun t ht => by linarith [hpos_all t ht]) hlat

end Invariance

/-! ### Potential function derivative, Lyapunov monotonicity, and bounds -/

section Potential

variable {P E : Type*} [Fintype P] [Fintype E] [DecidableEq E]
  {G : NonatomicCongestionGame Unit P E}

/-- The shifted Beckmann potential is always at least `lStar` on feasible flows when latencies are
nonnegative on `[0, 1]`. -/
theorem le_potential (h1 : G.rate () = 1)
    (hnonneg : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ G.latency e u) (lStar : ℝ) {x : P → ℝ}
    (hx : G.IsFeasible x) : lStar ≤ G.potential lStar x := by
  unfold potential
  refine le_add_of_nonneg_right (Finset.sum_nonneg fun e _ => ?_)
  have he := edgeFlow_mem_Icc_of_isFeasible h1 hx e
  exact intervalIntegral.integral_nonneg he.1 fun u hu => hnonneg e u ⟨hu.1, hu.2.trans he.2⟩

/-- **Equation (29.6) and potential upper bound** ([Suri2007], p. 728): for nondecreasing continuous
latencies on `[0, 1]` and a feasible flow `x` with `lStar ≤ G.cost x`,
`G.potential lStar x ≤ 2 * G.cost x`. -/
theorem potential_le_two_mul_cost (h1 : G.rate () = 1)
    (hmono : ∀ e, MonotoneOn (G.latency e) (Icc 0 1))
    (hcont : ∀ e, ContinuousOn (G.latency e) (Icc 0 1)) {lStar : ℝ} {x : P → ℝ}
    (hx : G.IsFeasible x) (hlStar : lStar ≤ G.cost x) :
    G.potential lStar x ≤ 2 * G.cost x := by
  have hint_le : ∑ e, ∫ u in (0 : ℝ)..G.edgeFlow x e, G.latency e u ≤ G.cost x := by
    rw [G.cost_eq_sum_edgeFlow]
    refine Finset.sum_le_sum fun e _ => ?_
    have he := edgeFlow_mem_Icc_of_isFeasible h1 hx e
    have hsub : uIcc (0 : ℝ) (G.edgeFlow x e) ⊆ Icc 0 1 := uIcc_subset_Icc ⟨le_rfl, zero_le_one⟩ he
    calc ∫ u in (0 : ℝ)..G.edgeFlow x e, G.latency e u
        ≤ ∫ _ in (0 : ℝ)..G.edgeFlow x e, G.latency e (G.edgeFlow x e) :=
          intervalIntegral.integral_mono_on he.1 ((hcont e).mono hsub).intervalIntegrable
            intervalIntegrable_const fun u hu =>
              hmono e ⟨hu.1, hu.2.trans he.2⟩ he hu.2
      _ = G.edgeFlow x e * G.latency e (G.edgeFlow x e) := by
          simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  unfold potential
  linarith

omit [Fintype E] in
/-- Variance identity: when `∑ p, x p = 1`,
`G.cost x ^ 2 - ∑ p, x p * G.pathLatency x p ^ 2` equals the negative variance. -/
private theorem cost_sq_sub_sum_mul_sq {x : P → ℝ} (hsum : ∑ p, x p = 1) :
    G.cost x ^ 2 - ∑ p, x p * G.pathLatency x p ^ 2 =
      -(∑ p, x p * (G.pathLatency x p - G.cost x) ^ 2) := by
  have hexp : ∑ p, x p * (G.pathLatency x p - G.cost x) ^ 2 =
      (∑ p, x p * G.pathLatency x p ^ 2) - 2 * G.cost x * (∑ p, x p * G.pathLatency x p) +
        G.cost x ^ 2 * (∑ p, x p) := by
    calc ∑ p, x p * (G.pathLatency x p - G.cost x) ^ 2
        = ∑ p, (x p * G.pathLatency x p ^ 2 - 2 * G.cost x * (x p * G.pathLatency x p) +
            G.cost x ^ 2 * x p) :=
          Finset.sum_congr rfl fun p _ => by ring
      _ = (∑ p, x p * G.pathLatency x p ^ 2) - 2 * G.cost x * (∑ p, x p * G.pathLatency x p) +
            G.cost x ^ 2 * (∑ p, x p) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change _ = -(∑ p, x p * (G.pathLatency x p - G.cost x) ^ 2)
  rw [hexp, hsum]
  change G.cost x ^ 2 - ∑ p, x p * G.pathLatency x p ^ 2 =
    -((∑ p, x p * G.pathLatency x p ^ 2) - 2 * G.cost x * G.cost x + G.cost x ^ 2 * 1)
  ring

/-- **Time derivative of the potential function** ([Suri2007], Equation 29.4, p. 727): along any
feasible replicator trajectory with latencies continuous on `[0, 1]`,
`Φ'(t) = lam (x t) * (G.cost (x t) ^ 2 - ∑ p, x t p * G.pathLatency (x t) p ^ 2)`. -/
theorem hasDerivWithinAt_potential (h1 : G.rate () = 1) {lam : (P → ℝ) → ℝ} {x : ℝ → P → ℝ}
    (hx : G.IsReplicatorTrajectory lam x) (hfeas : ∀ t ≥ 0, G.IsFeasible (x t))
    (hcont : ∀ e, ContinuousOn (G.latency e) (Icc 0 1)) (lStar : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => G.potential lStar (x s))
      (lam (x t) * (G.cost (x t) ^ 2 - ∑ p, x t p * G.pathLatency (x t) p ^ 2)) (Ici 0) t := by
  have hterm : ∀ e : E,
      HasDerivWithinAt (fun s => ∫ u in (0 : ℝ)..G.edgeFlow (x s) e, G.latency e u)
        (G.edgeFlow (G.replicatorDrift lam (x t)) e * G.latency e (G.edgeFlow (x t) e))
        (Ici 0) t := fun e => by
    have hflow : HasDerivWithinAt (fun s => G.edgeFlow (x s) e)
        (G.edgeFlow (G.replicatorDrift lam (x t)) e) (Ici 0) t :=
      HasDerivWithinAt.fun_sum fun p _ => hx t ht p
    have hw : G.edgeFlow (x t) e ∈ Icc (0 : ℝ) 1 :=
      edgeFlow_mem_Icc_of_isFeasible h1 (hfeas t ht) e
    have : Fact (G.edgeFlow (x t) e ∈ Icc (0 : ℝ) 1) := ⟨hw⟩
    have hint : HasDerivWithinAt (fun w => ∫ u in (0 : ℝ)..w, G.latency e u)
        (G.latency e (G.edgeFlow (x t) e)) (Icc 0 1) (G.edgeFlow (x t) e) :=
      intervalIntegral.integral_hasDerivWithinAt_right
        ((hcont e).mono (uIcc_subset_Icc ⟨le_rfl, zero_le_one⟩ hw)).intervalIntegrable
        ((hcont e).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc _)
        (hcont e _ hw)
    have hmaps : MapsTo (fun s => G.edgeFlow (x s) e) (Ici 0) (Icc 0 1) :=
      fun s hs => edgeFlow_mem_Icc_of_isFeasible h1 (hfeas s hs) e
    have hcomp := hint.comp t hflow hmaps
    rw [mul_comm] at hcomp
    exact hcomp
  have hsum : HasDerivWithinAt (fun s => G.potential lStar (x s))
      (∑ e, G.edgeFlow (G.replicatorDrift lam (x t)) e * G.latency e (G.edgeFlow (x t) e))
      (Ici 0) t :=
    (HasDerivWithinAt.fun_sum fun e _ => hterm e).const_add lStar
  convert hsum using 1
  rw [← G.sum_mul_sum_resources]
  calc lam (x t) * (G.cost (x t) ^ 2 - ∑ p, x t p * G.pathLatency (x t) p ^ 2)
      = lam (x t) * (G.cost (x t) * (∑ p, x t p * G.pathLatency (x t) p) -
          ∑ p, x t p * G.pathLatency (x t) p ^ 2) := by rw [sq]; rfl
    _ = ∑ p, (lam (x t) * G.cost (x t) * (x t p * G.pathLatency (x t) p) -
          lam (x t) * (x t p * G.pathLatency (x t) p ^ 2)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    _ = ∑ p, G.replicatorDrift lam (x t) p * ∑ e ∈ G.resources p,
          G.latency e (G.edgeFlow (x t) e) :=
        Finset.sum_congr rfl fun p _ => by unfold replicatorDrift pathLatency; ring

/-- **Lyapunov monotonicity** ([Suri2007], Section 29.3.2, pp. 726–727): along any feasible
replicator trajectory with nonnegative rate `lam (x t) ≥ 0` and latencies continuous on `[0, 1]`,
the shifted Beckmann potential `t ↦ G.potential lStar (x t)` is nonincreasing on `[0, ∞)`. -/
theorem antitoneOn_potential (h1 : G.rate () = 1) {lam : (P → ℝ) → ℝ} {x : ℝ → P → ℝ}
    (hx : G.IsReplicatorTrajectory lam x) (hfeas : ∀ t ≥ 0, G.IsFeasible (x t))
    (hlam : ∀ t ≥ 0, 0 ≤ lam (x t)) (hcont : ∀ e, ContinuousOn (G.latency e) (Icc 0 1))
    (lStar : ℝ) :
    AntitoneOn (fun t => G.potential lStar (x t)) (Ici 0) := by
  have hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun s => G.potential lStar (x s))
        (lam (x t) * (G.cost (x t) ^ 2 - ∑ p, x t p * G.pathLatency (x t) p ^ 2)) (Ici 0) t :=
    fun t ht => hasDerivWithinAt_potential h1 hx hfeas hcont lStar ht
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).mono interior_subset) fun t ht => ?_
  have ht0 : 0 ≤ t := interior_subset ht
  obtain ⟨hnn, hsum⟩ := (isFeasible_unit_iff h1).1 (hfeas t ht0)
  rw [cost_sq_sub_sum_mul_sq hsum, mul_neg]
  exact neg_nonpos.2 <| mul_nonneg (hlam t ht0) <|
    Finset.sum_nonneg fun p _ => mul_nonneg (hnn p) (sq_nonneg _)

end Potential

/-! ### Global existence and uniqueness via Picard–Lindelöf -/

section Existence

variable {P E : Type*} [Fintype P] [DecidableEq E]

/-- Product of two bounded globally Lipschitz real-valued functions is globally Lipschitz. -/
private theorem lipschitzWith_mul_of_bdd {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ Bf) (hBg : ∀ x, |g x| ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * g x) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq]
    have htri : |f x * g x - f y * g y| ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
      calc |f x * g x - f y * g y|
          = |f x * (g x - g y) + (f x - f y) * g y| := by ring_nf
        _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := abs_add_le _ _
        _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by
            rw [abs_mul, abs_mul, mul_comm |f x - f y|]
    have h1 : |g x - g y| ≤ Kg * dist x y := by
      simpa only [Real.dist_eq] using hg.dist_le_mul x y
    have h2 : |f x - f y| ≤ Kf * dist x y := by
      simpa only [Real.dist_eq] using hf.dist_le_mul x y
    calc |f x * g x - f y * g y|
        ≤ Bf * (Kg * dist x y) + Bg * (Kf * dist x y) := by
          refine htri.trans (add_le_add ?_ ?_)
          · exact mul_le_mul (hBf x) h1 (abs_nonneg _) Bf.2
          · exact mul_le_mul (hBg y) h2 (abs_nonneg _) Bg.2
      _ = ↑(Bf * Kg + Bg * Kf) * dist x y := by push_cast; ring

/-- Global ODE existence on `ℝ` for any bounded globally Lipschitz autonomous vector field on a
Banach space, obtained by gluing Picard–Lindelöf solutions on `[-n-1, n+1]` via uniqueness. -/
private theorem exists_global_ode_solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {V : X → X} {L K : ℝ≥0}
    (hL : ∀ x, ‖V x‖ ≤ L) (hK : LipschitzWith K V) (x₀ : X) :
    ∃ x : ℝ → X, x 0 = x₀ ∧ ∀ t : ℝ, HasDerivAt x (V (x t)) t := by
  have hex : ∀ n : ℕ, ∃ α : ℝ → X, α 0 = x₀ ∧
      ∀ t ∈ Icc (-(n + 1 : ℝ)) (n + 1 : ℝ),
        HasDerivWithinAt α (V (α t)) (Icc (-(n + 1 : ℝ)) (n + 1 : ℝ)) t := fun n => by
    have h0mem : (0 : ℝ) ∈ Icc (-(n + 1 : ℝ)) (n + 1 : ℝ) :=
      ⟨by linarith [Nat.cast_nonneg (α := ℝ) n], by positivity⟩
    have hpl : IsPicardLindelof (fun _ => V) ⟨0, h0mem⟩ x₀ (L * (n + 1)) 0 L K :=
      IsPicardLindelof.of_time_independent (fun x _ => hL x) hK.lipschitzOnWith <| by
        simp only [sub_zero, zero_sub, neg_neg, max_self, NNReal.coe_mul, NNReal.coe_add,
          NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_zero, le_rfl]
    exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose α hα0 hαd using hex
  have hα_deriv : ∀ n : ℕ, ∀ t ∈ Ioo (-(n + 1 : ℝ)) (n + 1 : ℝ),
      HasDerivAt (α n) (V (α n t)) t := fun n t ht =>
    (hαd n t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hagree : ∀ m n : ℕ, m ≤ n →
      EqOn (α m) (α n) (Ioo (-(m + 1 : ℝ)) (m + 1 : ℝ)) := fun m n hmn => by
    have h0m : (0 : ℝ) ∈ Ioo (-(m + 1 : ℝ)) (m + 1 : ℝ) :=
      ⟨by linarith [Nat.cast_nonneg (α := ℝ) m], by positivity⟩
    have hsub : Ioo (-(m + 1 : ℝ)) (m + 1 : ℝ) ⊆ Ioo (-(n + 1 : ℝ)) (n + 1 : ℝ) := by
      have hcast : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
      exact fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ODE_solution_unique_of_mem_Ioo (s := fun _ => univ)
      (fun _ _ => hK.lipschitzOnWith) h0m
      (fun t ht => ⟨hα_deriv m t ht, trivial⟩)
      (fun t ht => ⟨hα_deriv n t (hsub ht), trivial⟩)
      ((hα0 m).trans (hα0 n).symm)
  let x : ℝ → X := fun t => α ⌊|t|⌋₊ t
  refine ⟨x, ?_, fun t => ?_⟩
  · change α ⌊|(0 : ℝ)|⌋₊ 0 = x₀
    rw [abs_zero, Nat.floor_zero, hα0]
  · let N := ⌊|t|⌋₊ + 1
    have htN : t ∈ Ioo (-(N : ℝ)) (N : ℝ) := by
      have hlt : |t| < (N : ℝ) := by
        simpa only [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one |t|
      exact abs_lt.1 hlt
    have hev : x =ᶠ[𝓝 t] α N := by
      refine Filter.eventually_of_mem (Ioo_mem_nhds htN.1 htN.2) fun s hs => ?_
      have hsabs : |s| < (N : ℝ) := abs_lt.2 hs
      have hfl_le : ⌊|s|⌋₊ ≤ N := Nat.floor_le_of_le hsabs.le
      have hsmem : s ∈ Ioo (-(⌊|s|⌋₊ + 1 : ℝ)) (⌊|s|⌋₊ + 1 : ℝ) :=
        abs_lt.1 (Nat.lt_floor_add_one |s|)
      exact hagree ⌊|s|⌋₊ N hfl_le hsmem
    have htN1 : t ∈ Ioo (-(N + 1 : ℝ)) (N + 1 : ℝ) :=
      ⟨by linarith [htN.1], by linarith [htN.2]⟩
    have hxt : x t = α N t := hev.eq_of_nhds
    rw [hxt]
    exact (hα_deriv N t htN1).congr_of_eventuallyEq hev

/-- Clamping a real number to `[0, 1]`. -/
private noncomputable def clamp01 (u : ℝ) : ℝ := (projIcc (0 : ℝ) 1 zero_le_one u : ℝ)

/-- Clamping a real number to `[0, 2]`. -/
private noncomputable def clamp02 (u : ℝ) : ℝ := (projIcc (0 : ℝ) 2 (by norm_num) u : ℝ)

private theorem clamp01_mem (u : ℝ) : clamp01 u ∈ Icc (0 : ℝ) 1 :=
  (projIcc (0 : ℝ) 1 zero_le_one u).2

private theorem clamp02_mem (u : ℝ) : clamp02 u ∈ Icc (0 : ℝ) 2 :=
  (projIcc (0 : ℝ) 2 (by norm_num) u).2

private theorem clamp01_of_mem {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : clamp01 u = u :=
  congrArg Subtype.val (projIcc_of_mem zero_le_one hu)

private theorem clamp02_of_mem {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 2) : clamp02 u = u :=
  congrArg Subtype.val (projIcc_of_mem (by norm_num) hu)

private theorem clamp02_of_nonpos {u : ℝ} (hu : u ≤ 0) : clamp02 u = 0 :=
  congrArg Subtype.val (projIcc_of_le_left (by norm_num) hu)

private theorem lipschitzWith_clamp01 : LipschitzWith 1 clamp01 :=
  LipschitzWith.of_dist_le_mul fun u v =>
    (LipschitzWith.projIcc (a := (0 : ℝ)) (b := 1) zero_le_one).dist_le_mul u v

private theorem lipschitzWith_clamp02 : LipschitzWith 1 clamp02 :=
  LipschitzWith.of_dist_le_mul fun u v =>
    (LipschitzWith.projIcc (a := (0 : ℝ)) (b := 2) (by norm_num)).dist_le_mul u v

/-- Clamped relative-rate replicator vector field agreeing with the exact relative-rate replicator
drift on feasible flows with `G.cost x ≥ lStar`, while remaining globally bounded and globally
Lipschitz on `P → ℝ` using only latency values in `[0, 1]`. -/
private noncomputable def clampedPathLatency (G : NonatomicCongestionGame Unit P E)
    (x : P → ℝ) (p : P) : ℝ :=
  ∑ e ∈ G.resources p, G.latency e (clamp01 (G.edgeFlow x e))

private noncomputable def clampedCost (G : NonatomicCongestionGame Unit P E) (x : P → ℝ) : ℝ :=
  ∑ q, clamp02 (x q) * clampedPathLatency G x q

private noncomputable def clampedRate (G : NonatomicCongestionGame Unit P E)
    (lStar : ℝ) (x : P → ℝ) : ℝ :=
  (max (lStar / 2) (clampedCost G x))⁻¹

private noncomputable def clampedDrift (G : NonatomicCongestionGame Unit P E)
    (lStar : ℝ) (x : P → ℝ) (p : P) : ℝ :=
  clampedRate G lStar x * clamp02 (x p) * (clampedCost G x - clampedPathLatency G x p)

private theorem clampedDrift_eq_replicatorDrift {G : NonatomicCongestionGame Unit P E}
    (h1 : G.rate () = 1) {lStar : ℝ} (hlStar : 0 < lStar)
    (hmin : ∀ y, G.IsFeasible y → lStar ≤ G.cost y) {x : P → ℝ} (hx : G.IsFeasible x) (p : P) :
    clampedDrift G lStar x p = G.replicatorDrift (fun y => (G.cost y)⁻¹) x p := by
  obtain ⟨hnn, hsum⟩ := (isFeasible_unit_iff h1).1 hx
  have hx02 : ∀ q, x q ∈ Icc (0 : ℝ) 2 := fun q =>
    ⟨hnn q, ((Finset.single_le_sum (fun r _ => hnn r) (Finset.mem_univ q)).trans hsum.le).trans
      (by norm_num)⟩
  have hpath : ∀ q, clampedPathLatency G x q = G.pathLatency x q := fun q =>
    Finset.sum_congr rfl fun e _ => by
      rw [clamp01_of_mem (edgeFlow_mem_Icc_of_isFeasible h1 hx e)]
  have hcost : clampedCost G x = G.cost x :=
    Finset.sum_congr rfl fun q _ => by rw [clamp02_of_mem (hx02 q), hpath q]
  have hrate : clampedRate G lStar x = (G.cost x)⁻¹ := by
    unfold clampedRate
    rw [hcost, max_eq_right (by linarith [hmin x hx])]
  unfold clampedDrift replicatorDrift
  rw [hrate, clamp02_of_mem (hx02 p), hcost, hpath p]

private theorem clampedDrift_bounded_and_lipschitz (G : NonatomicCongestionGame Unit P E)
    {lStar : ℝ} (hlStar : 0 < lStar)
    (hnonneg : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ G.latency e u)
    (hlip : ∀ e, ∃ K, LipschitzOnWith K (G.latency e) (Icc 0 1)) :
    (∃ L : ℝ≥0, ∀ x : P → ℝ, ‖clampedDrift G lStar x‖ ≤ L) ∧
      ∃ K : ℝ≥0, LipschitzWith K (clampedDrift G lStar) := by
  choose Ke hKe using hlip
  have hlat_lip : ∀ e, LipschitzWith (Ke e) (fun u => G.latency e (clamp01 u)) := fun e =>
    LipschitzWith.of_dist_le_mul fun u v => by
      have h1 := (hKe e).dist_le_mul (clamp01 u) (clamp01_mem u) (clamp01 v) (clamp01_mem v)
      have h2 := lipschitzWith_clamp01.dist_le_mul u v
      simp only [NNReal.coe_one, one_mul] at h2
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (Ke e).2)
  have hlat_bdd : ∀ e, ∃ Be : ℝ≥0, ∀ u, |G.latency e (clamp01 u)| ≤ Be := fun e => by
    refine ⟨⟨G.latency e 0 + Ke e, add_nonneg (hnonneg e 0 ⟨le_rfl, zero_le_one⟩) (Ke e).2⟩,
      fun u => ?_⟩
    have hu := clamp01_mem u
    have hnn := hnonneg e (clamp01 u) hu
    rw [abs_of_nonneg hnn]
    have hd := (hKe e).dist_le_mul (clamp01 u) hu 0 ⟨le_rfl, zero_le_one⟩
    rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hu.1] at hd
    have hle : G.latency e (clamp01 u) - G.latency e 0 ≤ (Ke e : ℝ) :=
      (le_abs_self _).trans (hd.trans (mul_le_of_le_one_right (Ke e).2 hu.2))
    change G.latency e (clamp01 u) ≤ G.latency e 0 + Ke e
    linarith
  choose Be hBe using hlat_bdd
  have hedge_lip : ∀ e, LipschitzWith (Fintype.card P : ℝ≥0) (fun x : P → ℝ => G.edgeFlow x e) :=
    fun e => LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq]
      calc |G.edgeFlow x e - G.edgeFlow y e|
          = |∑ p with e ∈ G.resources p, (x p - y p)| := by
            unfold edgeFlow; rw [Finset.sum_sub_distrib]
        _ ≤ ∑ p with e ∈ G.resources p, |x p - y p| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p : P, |x p - y p| :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => abs_nonneg _
        _ ≤ ∑ _p : P, dist x y := Finset.sum_le_sum fun p _ => by
            simpa only [Real.dist_eq] using dist_le_pi_dist x y p
        _ = (Fintype.card P : ℝ≥0) * dist x y := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_natCast]
  have hpath_lip : ∀ p, ∃ Kp : ℝ≥0, LipschitzWith Kp (fun x => clampedPathLatency G x p) :=
    fun p => by
      refine ⟨∑ e ∈ G.resources p, Ke e * (Fintype.card P : ℝ≥0),
        LipschitzWith.of_dist_le_mul fun x y => ?_⟩
      rw [Real.dist_eq]
      calc |clampedPathLatency G x p - clampedPathLatency G y p|
          = |∑ e ∈ G.resources p,
              (G.latency e (clamp01 (G.edgeFlow x e)) - G.latency e (clamp01 (G.edgeFlow y e)))| :=
            by unfold clampedPathLatency; rw [Finset.sum_sub_distrib]
        _ ≤ ∑ e ∈ G.resources p,
              |G.latency e (clamp01 (G.edgeFlow x e)) - G.latency e (clamp01 (G.edgeFlow y e))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ e ∈ G.resources p, ↑(Ke e * (Fintype.card P : ℝ≥0)) * dist x y :=
            Finset.sum_le_sum fun e _ => by
              have hcomp := (hlat_lip e).comp (hedge_lip e)
              simpa only [Real.dist_eq, Function.comp_apply] using hcomp.dist_le_mul x y
        _ = ↑(∑ e ∈ G.resources p, Ke e * (Fintype.card P : ℝ≥0)) * dist x y := by
            rw [← Finset.sum_mul]; push_cast; rfl
  choose Kpath hKpath using hpath_lip
  have hpath_bdd : ∀ p, ∃ Bp : ℝ≥0, ∀ x, |clampedPathLatency G x p| ≤ Bp := fun p => by
    refine ⟨∑ e ∈ G.resources p, Be e, fun x => ?_⟩
    calc |clampedPathLatency G x p|
        ≤ ∑ e ∈ G.resources p, |G.latency e (clamp01 (G.edgeFlow x e))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ G.resources p, (Be e : ℝ) := Finset.sum_le_sum fun e _ => hBe e _
      _ = ↑(∑ e ∈ G.resources p, Be e) := by push_cast; rfl
  choose Bpath hBpath using hpath_bdd
  have hclamp_coord_lip : ∀ p, LipschitzWith 1 (fun x : P → ℝ => clamp02 (x p)) := fun p =>
    LipschitzWith.of_dist_le_mul fun x y => by
      have h1 := lipschitzWith_clamp02.dist_le_mul (x p) (y p)
      simp only [NNReal.coe_one, one_mul] at h1 ⊢
      exact h1.trans (dist_le_pi_dist x y p)
  have hclamp_coord_bdd : ∀ p (x : P → ℝ), |clamp02 (x p)| ≤ (2 : ℝ≥0) := fun p x => by
    have hm := clamp02_mem (x p)
    rw [abs_of_nonneg hm.1]
    exact hm.2
  have hcost_lip : ∃ Kc : ℝ≥0, LipschitzWith Kc (clampedCost G) := by
    have hterm : ∀ q, LipschitzWith ((2 : ℝ≥0) * Kpath q + Bpath q * 1)
        (fun x => clamp02 (x q) * clampedPathLatency G x q) := fun q =>
      lipschitzWith_mul_of_bdd (hclamp_coord_lip q) (hKpath q)
        (hclamp_coord_bdd q) (hBpath q)
    refine ⟨∑ q, ((2 : ℝ≥0) * Kpath q + Bpath q * 1),
      LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Real.dist_eq]
    calc |clampedCost G x - clampedCost G y|
        = |∑ q, (clamp02 (x q) * clampedPathLatency G x q -
            clamp02 (y q) * clampedPathLatency G y q)| := by
          unfold clampedCost; rw [Finset.sum_sub_distrib]
      _ ≤ ∑ q, |clamp02 (x q) * clampedPathLatency G x q -
            clamp02 (y q) * clampedPathLatency G y q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q, ↑((2 : ℝ≥0) * Kpath q + Bpath q * 1) * dist x y :=
          Finset.sum_le_sum fun q _ => by
            simpa only [Real.dist_eq] using (hterm q).dist_le_mul x y
      _ = ↑(∑ q, ((2 : ℝ≥0) * Kpath q + Bpath q * 1)) * dist x y := by
          rw [← Finset.sum_mul]; push_cast; rfl
  obtain ⟨Kc, hKc⟩ := hcost_lip
  let Bc : ℝ≥0 := ∑ q, (2 : ℝ≥0) * Bpath q
  have hBc : ∀ x, |clampedCost G x| ≤ Bc := fun x => by
    calc |clampedCost G x|
        ≤ ∑ q, |clamp02 (x q) * clampedPathLatency G x q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q, (2 : ℝ) * (Bpath q : ℝ) := Finset.sum_le_sum fun q _ => by
          rw [abs_mul]
          exact mul_le_mul (hclamp_coord_bdd q x) (hBpath q x) (abs_nonneg _) (by norm_num)
      _ = (Bc : ℝ) := by simp only [Bc]; push_cast; rfl
  let Br : ℝ≥0 := ⟨(lStar / 2)⁻¹, by positivity⟩
  have hBr : ∀ x, |clampedRate G lStar x| ≤ Br := fun x => by
    have hge : lStar / 2 ≤ max (lStar / 2) (clampedCost G x) := le_max_left _ _
    have hpos : 0 < max (lStar / 2) (clampedCost G x) := lt_of_lt_of_le (half_pos hlStar) hge
    rw [clampedRate, abs_of_pos (inv_pos.2 hpos)]
    exact inv_anti₀ (half_pos hlStar) hge
  let Kr : ℝ≥0 := Br * Br * Kc
  have hKr : LipschitzWith Kr (clampedRate G lStar) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      set a := max (lStar / 2) (clampedCost G x)
      set b := max (lStar / 2) (clampedCost G y)
      have ha : lStar / 2 ≤ a := le_max_left _ _
      have hb : lStar / 2 ≤ b := le_max_left _ _
      have hap : 0 < a := lt_of_lt_of_le (half_pos hlStar) ha
      have hbp : 0 < b := lt_of_lt_of_le (half_pos hlStar) hb
      have hmax_lip : |a - b| ≤ |clampedCost G x - clampedCost G y| := by
        simpa only [a, b, max_comm (lStar / 2)] using
          abs_max_sub_max_le_abs (clampedCost G x) (clampedCost G y) (lStar / 2)
      have hinv : |a⁻¹ - b⁻¹| = |a - b| / (a * b) := by
        rw [inv_sub_inv hap.ne' hbp.ne', abs_div, abs_sub_comm, abs_of_pos (mul_pos hap hbp)]
      rw [Real.dist_eq, clampedRate, clampedRate, hinv]
      have hdenom : (lStar / 2) * (lStar / 2) ≤ a * b :=
        mul_le_mul ha hb (half_pos hlStar).le hap.le
      calc |a - b| / (a * b)
          ≤ |a - b| / ((lStar / 2) * (lStar / 2)) :=
            div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (half_pos hlStar) (half_pos hlStar))
              hdenom
        _ = (Br : ℝ) * (Br : ℝ) * |a - b| := by
            change |a - b| / (lStar / 2 * (lStar / 2)) = (lStar / 2)⁻¹ * (lStar / 2)⁻¹ * |a - b|
            field_simp
        _ ≤ (Br : ℝ) * (Br : ℝ) * (Kc * dist x y) := by
            gcongr
            exact hmax_lip.trans (by simpa only [Real.dist_eq] using hKc.dist_le_mul x y)
        _ = (Kr : ℝ) * dist x y := by simp only [Kr]; push_cast; ring
  have hcoord : ∀ p, (∃ Lp : ℝ≥0, ∀ x, |clampedDrift G lStar x p| ≤ Lp) ∧
      ∃ Kp : ℝ≥0, LipschitzWith Kp (fun x => clampedDrift G lStar x p) := fun p => by
    have hdiff_bdd : ∀ x, |clampedCost G x - clampedPathLatency G x p| ≤ ↑(Bc + Bpath p) :=
      fun x => by
        calc |clampedCost G x - clampedPathLatency G x p|
            ≤ |clampedCost G x| + |clampedPathLatency G x p| := abs_sub _ _
          _ ≤ (Bc : ℝ) + (Bpath p : ℝ) := add_le_add (hBc x) (hBpath p x)
          _ = ↑(Bc + Bpath p) := by push_cast; rfl
    have hdiff_lip : LipschitzWith (Kc + Kpath p)
        (fun x => clampedCost G x - clampedPathLatency G x p) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [Real.dist_eq]
        have h1 : |clampedCost G x - clampedCost G y| ≤ Kc * dist x y := by
          simpa only [Real.dist_eq] using hKc.dist_le_mul x y
        have h2 : |clampedPathLatency G x p - clampedPathLatency G y p| ≤ Kpath p * dist x y := by
          simpa only [Real.dist_eq] using (hKpath p).dist_le_mul x y
        calc |(clampedCost G x - clampedPathLatency G x p) -
                (clampedCost G y - clampedPathLatency G y p)|
            = |(clampedCost G x - clampedCost G y) -
                (clampedPathLatency G x p - clampedPathLatency G y p)| := by ring_nf
          _ ≤ |clampedCost G x - clampedCost G y| +
                |clampedPathLatency G x p - clampedPathLatency G y p| := abs_sub _ _
          _ ≤ Kc * dist x y + Kpath p * dist x y := add_le_add h1 h2
          _ = ↑(Kc + Kpath p) * dist x y := by push_cast; ring
    have hprod1_bdd : ∀ x, |clampedRate G lStar x * clamp02 (x p)| ≤ ↑(Br * 2) := fun x => by
      rw [abs_mul]
      calc |clampedRate G lStar x| * |clamp02 (x p)|
          ≤ (Br : ℝ) * (2 : ℝ≥0) :=
            mul_le_mul (hBr x) (hclamp_coord_bdd p x) (abs_nonneg _) Br.2
        _ = ↑(Br * 2) := by push_cast; rfl
    have hprod1_lip : LipschitzWith (Br * 1 + 2 * Kr)
        (fun x => clampedRate G lStar x * clamp02 (x p)) :=
      lipschitzWith_mul_of_bdd hKr (hclamp_coord_lip p) hBr (hclamp_coord_bdd p)
    refine ⟨⟨Br * 2 * (Bc + Bpath p), fun x => ?_⟩,
      ⟨Br * 2 * (Kc + Kpath p) + (Bc + Bpath p) * (Br * 1 + 2 * Kr),
        lipschitzWith_mul_of_bdd hprod1_lip hdiff_lip hprod1_bdd hdiff_bdd⟩⟩
    unfold clampedDrift
    rw [abs_mul]
    calc |clampedRate G lStar x * clamp02 (x p)| * |clampedCost G x - clampedPathLatency G x p|
        ≤ ↑(Br * 2) * ↑(Bc + Bpath p) :=
          mul_le_mul (hprod1_bdd x) (hdiff_bdd x) (abs_nonneg _) (Br * 2).2
      _ = ↑(Br * 2 * (Bc + Bpath p)) := by push_cast; rfl
  choose Lcoord hLcoord using fun p => (hcoord p).1
  choose Kcoord hKcoord using fun p => (hcoord p).2
  refine ⟨⟨Finset.univ.sup Lcoord, fun x => ?_⟩,
    ⟨Finset.univ.sup Kcoord, LipschitzWith.of_dist_le_mul fun x y => ?_⟩⟩
  · refine (pi_norm_le_iff_of_nonneg (Finset.univ.sup Lcoord).2).2 fun p => ?_
    rw [Real.norm_eq_abs]
    exact (hLcoord p x).trans (NNReal.coe_le_coe.2 (Finset.le_sup (Finset.mem_univ p)))
  · refine (dist_pi_le_iff (mul_nonneg (Finset.univ.sup Kcoord).2 dist_nonneg)).2 fun p => ?_
    calc dist (clampedDrift G lStar x p) (clampedDrift G lStar y p)
        ≤ (Kcoord p : ℝ) * dist x y := (hKcoord p).dist_le_mul x y
      _ ≤ (Finset.univ.sup Kcoord : ℝ≥0) * dist x y :=
          mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 (Finset.le_sup (Finset.mem_univ p)))
            dist_nonneg

/-- **Global existence of relative-rate replicator trajectories** on `[0, ∞)`: given nonnegative
Lipschitz latency functions on `[0, 1]`, a positive lower bound `lStar` on feasible average
latencies, and a feasible initial flow `x₀`, there exists a trajectory `x : ℝ → P → ℝ` with
`x 0 = x₀` solving Equation (29.2) with relative rate `λ(x) = l̄(x)⁻¹` that remains feasible for
all `t ≥ 0`. -/
theorem exists_relativeReplicatorTrajectory {G : NonatomicCongestionGame Unit P E}
    (h1 : G.rate () = 1)
    (hnonneg : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ G.latency e u)
    (hlip : ∀ e, ∃ K, LipschitzOnWith K (G.latency e) (Icc 0 1))
    {lStar : ℝ} (hlStar : 0 < lStar) (hmin : ∀ y, G.IsFeasible y → lStar ≤ G.cost y)
    {x₀ : P → ℝ} (hx₀ : G.IsFeasible x₀) :
    ∃ x : ℝ → P → ℝ, x 0 = x₀ ∧ G.IsReplicatorTrajectory (fun y => (G.cost y)⁻¹) x ∧
      ∀ t ≥ 0, G.IsFeasible (x t) := by
  obtain ⟨⟨L, hL⟩, ⟨K, hK⟩⟩ := clampedDrift_bounded_and_lipschitz G hlStar hnonneg hlip
  obtain ⟨x, hx0, hxd⟩ := exists_global_ode_solution hL hK x₀
  have hxd_coord : ∀ t : ℝ, ∀ p : P,
      HasDerivAt (fun s => x s p) (clampedDrift G lStar (x t) p) t :=
    fun t p => (hasDerivAt_pi.1 (hxd t)) p
  have hx_cont : Continuous x := continuous_iff_continuousAt.2 fun t => (hxd t).continuousAt
  have hx_coord_cont : ∀ p, Continuous (fun t => x t p) :=
    fun p => (continuous_apply p).comp hx_cont
  -- Step 1: nonnegativity for all `t ≥ 0`.
  have hnn : ∀ t ≥ 0, ∀ p : P, 0 ≤ x t p := by
    intro t ht p
    by_contra hlt
    push Not at hlt
    let S : Set ℝ := {s ∈ Icc (0 : ℝ) t | 0 ≤ x s p}
    have hSne : S.Nonempty := ⟨0, ⟨le_rfl, ht⟩, by rw [hx0]; exact hx₀.1 p⟩
    have hSbdd : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
    have hSclosed : IsClosed S :=
      isClosed_Icc.inter (isClosed_le continuous_const (hx_coord_cont p))
    let t₀ := sSup S
    have ht₀mem : t₀ ∈ S := hSclosed.csSup_mem hSne hSbdd
    have ht₀_lt : t₀ < t := lt_of_le_of_ne ht₀mem.1.2 fun heq => by
      have := ht₀mem.2
      rw [heq] at this
      linarith
    have hneg_Ioc : ∀ s ∈ Ioc t₀ t, x s p < 0 := fun s hs => by
      by_contra hge
      push Not at hge
      have hsmem : s ∈ S := ⟨⟨ht₀mem.1.1.trans hs.1.le, hs.2⟩, hge⟩
      exact (le_csSup hSbdd hsmem).not_gt hs.1
    have ht₀_zero : x t₀ p = 0 := by
      refine le_antisymm ?_ ht₀mem.2
      have : (𝓝[Ioc t₀ t] t₀).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc ht₀_lt.ne]
        exact ⟨le_rfl, ht₀_lt.le⟩
      exact le_of_tendsto ((hx_coord_cont p).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (Filter.eventually_of_mem self_mem_nhdsWithin fun s hs => (hneg_Ioc s hs).le)
    have hzero_deriv : ∀ s ∈ interior (Icc t₀ t),
        HasDerivWithinAt (fun u => x u p) 0 (interior (Icc t₀ t)) s := fun s hs => by
      rw [interior_Icc] at hs
      have hneg : x s p < 0 := hneg_Ioc s ⟨hs.1, hs.2.le⟩
      have hd := (hxd_coord s p).hasDerivWithinAt (s := interior (Icc t₀ t))
      convert hd using 1
      unfold clampedDrift
      rw [clamp02_of_nonpos hneg.le, mul_zero, zero_mul]
    have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t₀ t)
      (hx_coord_cont p).continuousOn hzero_deriv (fun _ _ => le_rfl)
    have hle : x t₀ p ≤ x t p := hmono ⟨le_rfl, ht₀_lt.le⟩ ⟨ht₀_lt.le, le_rfl⟩ ht₀_lt.le
    linarith
  -- Step 2: sum invariance on any `[0, T]` where all coordinates remain in `[0, 2]`.
  have hsum_on_Icc : ∀ {T : ℝ}, 0 ≤ T → (∀ s ∈ Icc (0 : ℝ) T, ∀ p, x s p ≤ 2) →
      ∀ s ∈ Icc (0 : ℝ) T, ∑ p, x s p = 1 := by
    intro T hT hle2 s hs
    have hsum_deriv : ∀ u ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun v => (∑ p, x v p) - 1)
          (clampedRate G lStar (x u) * clampedCost G (x u) * ((∑ p, x u p) - 1))
          (Icc 0 T) u := fun u hu => by
      have hd := (HasDerivWithinAt.fun_sum (u := Finset.univ) fun p _ =>
        (hxd_coord u p).hasDerivWithinAt (s := Icc 0 T)).sub
        (hasDerivWithinAt_const u (Icc 0 T) (1 : ℝ))
      rw [sub_zero] at hd
      convert hd using 1
      have hcl : ∀ p, clamp02 (x u p) = x u p :=
        fun p => clamp02_of_mem ⟨hnn u hu.1 p, hle2 u hu p⟩
      calc clampedRate G lStar (x u) * clampedCost G (x u) * ((∑ p, x u p) - 1)
          = clampedRate G lStar (x u) * clampedCost G (x u) * (∑ p, x u p) -
              clampedRate G lStar (x u) * (∑ p, x u p * clampedPathLatency G (x u) p) := by
            have hc : clampedCost G (x u) = ∑ p, x u p * clampedPathLatency G (x u) p :=
              Finset.sum_congr rfl fun p _ => by rw [hcl p]
            rw [← hc]; ring
        _ = ∑ p, (clampedRate G lStar (x u) * clampedCost G (x u) * x u p -
              clampedRate G lStar (x u) * (x u p * clampedPathLatency G (x u) p)) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = ∑ p, clampedDrift G lStar (x u) p := Finset.sum_congr rfl fun p _ => by
            unfold clampedDrift; rw [hcl p]; ring
    have hcont_coeff : ContinuousOn (fun u => clampedRate G lStar (x u) * clampedCost G (x u))
        (Icc 0 T) := by
      have hlat_c : ∀ e, Continuous (fun w => G.latency e (clamp01 w)) := fun e => by
        obtain ⟨Ke, hKe⟩ := hlip e
        exact (LipschitzWith.of_dist_le_mul fun a b => by
          have h1 := hKe.dist_le_mul (clamp01 a) (clamp01_mem a) (clamp01 b) (clamp01_mem b)
          have h2 := lipschitzWith_clamp01.dist_le_mul a b
          simp only [NNReal.coe_one, one_mul] at h2
          exact h1.trans (mul_le_mul_of_nonneg_left h2 Ke.2)).continuous
      have hedge_c : ∀ e, Continuous (fun u => G.edgeFlow (x u) e) := fun e => by
        unfold edgeFlow; fun_prop
      have hpath_c : ∀ q, Continuous (fun u => clampedPathLatency G (x u) q) := fun q => by
        unfold clampedPathLatency
        have hcomp : ∀ e, Continuous (fun u => G.latency e (clamp01 (G.edgeFlow (x u) e))) :=
          fun e => (hlat_c e).comp (hedge_c e)
        fun_prop
      have hclamp_c : ∀ q, Continuous (fun u => clamp02 (x u q)) :=
        fun q => lipschitzWith_clamp02.continuous.comp (hx_coord_cont q)
      have hcont_c : Continuous (fun u => clampedCost G (x u)) := by
        unfold clampedCost; fun_prop
      have hcont_r : Continuous (fun u => clampedRate G lStar (x u)) :=
        (continuous_const.max hcont_c).inv₀ fun u => by
          linarith [le_max_left (lStar / 2) (clampedCost G (x u))]
      exact (hcont_r.mul hcont_c).continuousOn
    have heq := eq_mul_exp_integral_of_hasDerivWithinAt hT hcont_coeff hsum_deriv hs
    have hsum0 : ∑ p, x 0 p = 1 := by
      rw [hx0]
      exact ((isFeasible_unit_iff h1).1 hx₀).2
    rw [hsum0, sub_self, zero_mul] at heq
    linarith
  -- Step 3: no coordinate ever reaches `3 / 2`, so every coordinate stays in `[0, 1]`.
  have hlt_three_halves : ∀ t ≥ 0, ∀ p : P, x t p < 3 / 2 := by
    by_contra h
    push Not at h
    let S : Set ℝ := {s | 0 ≤ s ∧ ∃ p, 3 / 2 ≤ x s p}
    have hSne : S.Nonempty := by
      obtain ⟨t, ht, p, hp⟩ := h
      exact ⟨t, ht, p, hp⟩
    have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
    have hSclosed : IsClosed S := by
      have hU : S = ⋃ p : P, {s | 0 ≤ s ∧ 3 / 2 ≤ x s p} := by
        ext s; simp only [S, mem_iUnion, mem_ofPred_eq, exists_and_left]
      rw [hU]
      exact isClosed_iUnion_of_finite fun p =>
        isClosed_Ici.inter (isClosed_le continuous_const (hx_coord_cont p))
    let T := sInf S
    have hTmem : T ∈ S := hSclosed.csInf_mem hSne hSbdd
    have hT0 : 0 ≤ T := hTmem.1
    obtain ⟨p₀, hp₀⟩ := hTmem.2
    have hx₀_le1 : ∀ p, x 0 p ≤ 1 := fun p => by
      rw [hx0]
      obtain ⟨hnn0, hsum0⟩ := (isFeasible_unit_iff h1).1 hx₀
      exact (Finset.single_le_sum (fun q _ => hnn0 q) (Finset.mem_univ p)).trans hsum0.le
    have hTpos : 0 < T := lt_of_le_of_ne hT0 fun h0T => by
      rw [← h0T] at hp₀
      linarith [hx₀_le1 p₀]
    have hle2 : ∀ s ∈ Icc (0 : ℝ) T, ∀ p, x s p ≤ 2 := fun s hs p => by
      rcases hs.2.lt_or_eq with hlt | rfl
      · have hlt' : x s p < 3 / 2 := by
          by_contra hge
          push Not at hge
          exact (csInf_le hSbdd ⟨hs.1, p, hge⟩).not_gt hlt
        linarith
      · have : (𝓝[Ico (0 : ℝ) T] T).NeBot := by
          rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hTpos.ne]
          exact ⟨hT0, le_rfl⟩
        have hle32 : x T p ≤ 3 / 2 :=
          le_of_tendsto ((hx_coord_cont p).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
            (Filter.eventually_of_mem (self_mem_nhdsWithin (s := Ico (0 : ℝ) T)) fun u hu => by
              by_contra hge
              push Not at hge
              exact (csInf_le hSbdd ⟨hu.1, p, hge.le⟩).not_gt hu.2)
        linarith
    have hsumT : ∑ p, x T p = 1 := hsum_on_Icc hT0 hle2 T ⟨hT0, le_rfl⟩
    have hp₀_le1 : x T p₀ ≤ 1 :=
      (Finset.single_le_sum (fun q _ => hnn T hT0 q) (Finset.mem_univ p₀)).trans hsumT.le
    linarith
  have hfeas : ∀ t ≥ 0, G.IsFeasible (x t) := fun t ht => by
    rw [isFeasible_unit_iff h1]
    exact ⟨hnn t ht,
      hsum_on_Icc ht (fun s hs p => (hlt_three_halves s hs.1 p).le.trans (by norm_num))
        t ⟨ht, le_rfl⟩⟩
  refine ⟨x, hx0, fun t ht p => ?_, hfeas⟩
  rw [← clampedDrift_eq_replicatorDrift h1 hlStar hmin (hfeas t ht) p]
  exact (hxd_coord t p).hasDerivWithinAt

/-- **Uniqueness of feasible relative-rate replicator trajectories** on `[0, ∞)`: under nonnegative
Lipschitz latencies on `[0, 1]` and positive minimum feasible average latency `lStar`, any two
feasible trajectories of Equation (29.2) with relative rate `λ(x) = l̄(x)⁻¹` that agree at `t = 0`
agree for all `t ≥ 0`. -/
theorem eqOn_of_isRelativeReplicatorTrajectory {G : NonatomicCongestionGame Unit P E}
    (h1 : G.rate () = 1)
    (hnonneg : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ G.latency e u)
    (hlip : ∀ e, ∃ K, LipschitzOnWith K (G.latency e) (Icc 0 1))
    {lStar : ℝ} (hlStar : 0 < lStar) (hmin : ∀ y, G.IsFeasible y → lStar ≤ G.cost y)
    {x y : ℝ → P → ℝ}
    (hx : G.IsReplicatorTrajectory (fun z => (G.cost z)⁻¹) x) (hxfeas : ∀ t ≥ 0, G.IsFeasible (x t))
    (hy : G.IsReplicatorTrajectory (fun z => (G.cost z)⁻¹) y) (hyfeas : ∀ t ≥ 0, G.IsFeasible (y t))
    (h0 : x 0 = y 0) :
    EqOn x y (Ici 0) := fun t ht => by
  obtain ⟨_, ⟨K, hK⟩⟩ := clampedDrift_bounded_and_lipschitz G hlStar hnonneg hlip
  have hderiv : ∀ z : ℝ → P → ℝ,
      G.IsReplicatorTrajectory (fun w => (G.cost w)⁻¹) z →
      (∀ s ≥ 0, G.IsFeasible (z s)) →
      ∀ s ∈ Ico (0 : ℝ) t, HasDerivWithinAt z (clampedDrift G lStar (z s)) (Ici s) s :=
    fun z hz hzfeas s hs => hasDerivWithinAt_pi.2 fun p => by
      rw [clampedDrift_eq_replicatorDrift h1 hlStar hmin (hzfeas s hs.1) p]
      exact (hz s hs.1 p).mono (Ici_subset_Ici.2 hs.1)
  have hx_cont : ContinuousOn x (Icc 0 t) :=
    continuousOn_pi.2 fun p => (continuousOn_trajectory hx p).mono fun _ hs => hs.1
  have hy_cont : ContinuousOn y (Icc 0 t) :=
    continuousOn_pi.2 fun p => (continuousOn_trajectory hy p).mono fun _ hs => hs.1
  exact ODE_solution_unique (fun _ => hK) hx_cont (hderiv x hx hxfeas) hy_cont (hderiv y hy hyfeas)
    h0 ⟨ht, le_rfl⟩

end Existence

/-! ### Theorem 29.12: convergence time to an `ε`-approximate equilibrium -/

section Convergence

variable {P E : Type*} [Fintype P] [Fintype E] [DecidableEq E]
  {G : NonatomicCongestionGame Unit P E}

/-- Weighted Cauchy–Schwarz inequality for nonnegative weights on a finite set. -/
private theorem sq_sum_mul_le_sum_mul_sum_mul_sq {ι : Type*} (s : Finset ι)
    {w y : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * y i) ^ 2 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * y i ^ 2) := by
  set W := ∑ i ∈ s, w i
  set S := ∑ i ∈ s, w i * y i
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  rcases hW.eq_or_lt with hW0 | hWpos
  · have hzero : ∀ i ∈ s, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).1 hW0.symm
    have hS0 : S = 0 := Finset.sum_eq_zero fun i hi => by rw [hzero i hi, zero_mul]
    rw [hS0, ← hW0]
    norm_num
  · have hnonneg : 0 ≤ ∑ i ∈ s, w i * (W * y i - S) ^ 2 :=
      Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
    have hexp : ∑ i ∈ s, w i * (W * y i - S) ^ 2 =
        W * (W * (∑ i ∈ s, w i * y i ^ 2) - S ^ 2) := by
      calc ∑ i ∈ s, w i * (W * y i - S) ^ 2
          = ∑ i ∈ s, (W ^ 2 * (w i * y i ^ 2) - 2 * W * S * (w i * y i) + S ^ 2 * w i) :=
            Finset.sum_congr rfl fun i _ => by ring
        _ = W ^ 2 * (∑ i ∈ s, w i * y i ^ 2) - 2 * W * S * S + S ^ 2 * W := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]; rfl
        _ = W * (W * (∑ i ∈ s, w i * y i ^ 2) - S ^ 2) := by ring
    rw [hexp] at hnonneg
    have hsub : 0 ≤ W * (∑ i ∈ s, w i * y i ^ 2) - S ^ 2 :=
      nonneg_of_mul_nonneg_right hnonneg hWpos
    linarith

omit [Fintype E] in
/-- Variance lower bound behind [Suri2007], Equation (29.5), pp. 727–728: if a feasible flow `x`
with positive average latency is not an `ε`-approximate equilibrium, then the latency variance
satisfies `ε ^ 3 * G.cost x ^ 2 < ∑ p, x p * (G.pathLatency x p - G.cost x) ^ 2` (strictly,
improving Suri's `ε ^ 3 / 2` factor by keeping `1 / (1 - ε) > 1`). -/
private theorem variance_gt_of_not_isApproxEquilibrium (h1 : G.rate () = 1)
    (hnonneg : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ G.latency e u) {ε : ℝ} (hε : 0 < ε)
    {x : P → ℝ} (hx : G.IsFeasible x) (hcost : 0 < G.cost x) (hnot : ¬ G.IsApproxEquilibrium ε x) :
    ε ^ 3 * G.cost x ^ 2 < ∑ p, x p * (G.pathLatency x p - G.cost x) ^ 2 := by
  classical
  obtain ⟨hnn, hsum⟩ := (isFeasible_unit_iff h1).1 hx
  set Pε : Finset P := Finset.univ.filter fun p => (1 + ε) * G.cost x ≤ G.pathLatency x p
  set a : ℝ := ∑ p ∈ Pε, x p
  have ha_gt : ε < a := by
    by_contra hle
    push Not at hle
    exact hnot ⟨hx, hle⟩
  have ha_pos : 0 < a := hε.trans ha_gt
  have ha_lt1 : a < 1 := by
    have hbound : a * ((1 + ε) * G.cost x) ≤ G.cost x := by
      calc a * ((1 + ε) * G.cost x)
          = ∑ p ∈ Pε, x p * ((1 + ε) * G.cost x) := Finset.sum_mul _ _ _
        _ ≤ ∑ p ∈ Pε, x p * G.pathLatency x p :=
            Finset.sum_le_sum fun p hp =>
              mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hp).2 (hnn p)
        _ ≤ ∑ p, x p * G.pathLatency x p :=
            Finset.sum_le_univ_sum_of_nonneg fun p =>
              mul_nonneg (hnn p) (pathLatency_nonneg_of_isFeasible h1 hnonneg hx p)
        _ = G.cost x := rfl
    have ha_le : a * (1 + ε) ≤ 1 := by
      have hmul : a * (1 + ε) * G.cost x ≤ 1 * G.cost x := by linarith
      exact le_of_mul_le_mul_right hmul hcost
    nlinarith
  have h1ma_pos : 0 < 1 - a := sub_pos.2 ha_lt1
  have hε_lt1 : ε < 1 := ha_gt.trans ha_lt1
  have h1mε_pos : 0 < 1 - ε := sub_pos.2 hε_lt1
  set Δ : ℝ := ∑ p ∈ Pε, x p * (G.pathLatency x p - G.cost x)
  have hΔ_ge : a * (ε * G.cost x) ≤ Δ := by
    calc a * (ε * G.cost x)
        = ∑ p ∈ Pε, x p * (ε * G.cost x) := Finset.sum_mul _ _ _
      _ ≤ Δ := Finset.sum_le_sum fun p hp => by
          have hlat := (Finset.mem_filter.mp hp).2
          exact mul_le_mul_of_nonneg_left (by linarith) (hnn p)
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le (mul_pos ha_pos (mul_pos hε hcost)) hΔ_ge
  have hsum_compl : ∑ p ∈ Pεᶜ, x p = 1 - a := by
    have hadd := Finset.sum_add_sum_compl Pε x
    rw [hsum] at hadd
    linarith
  have hzero_mean : ∑ p, x p * (G.pathLatency x p - G.cost x) = 0 := by
    calc ∑ p, x p * (G.pathLatency x p - G.cost x)
        = (∑ p, x p * G.pathLatency x p) - (∑ p, x p) * G.cost x := by
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      _ = 0 := by rw [hsum, one_mul]; unfold cost; ring
  have hΔ_compl : ∑ p ∈ Pεᶜ, x p * (G.cost x - G.pathLatency x p) = Δ := by
    have hadd := Finset.sum_add_sum_compl Pε (fun p => x p * (G.pathLatency x p - G.cost x))
    rw [hzero_mean] at hadd
    have hneg : ∑ p ∈ Pεᶜ, x p * (G.cost x - G.pathLatency x p) =
        -(∑ p ∈ Pεᶜ, x p * (G.pathLatency x p - G.cost x)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    linarith
  have hcs1 : Δ ^ 2 / a ≤ ∑ p ∈ Pε, x p * (G.pathLatency x p - G.cost x) ^ 2 := by
    rw [div_le_iff₀ ha_pos, mul_comm]
    exact sq_sum_mul_le_sum_mul_sum_mul_sq Pε fun p _ => hnn p
  have hcs2 : Δ ^ 2 / (1 - a) ≤ ∑ p ∈ Pεᶜ, x p * (G.pathLatency x p - G.cost x) ^ 2 := by
    rw [div_le_iff₀ h1ma_pos, mul_comm, ← hsum_compl, ← hΔ_compl]
    have hsq : ∑ p ∈ Pεᶜ, x p * (G.cost x - G.pathLatency x p) ^ 2 =
        ∑ p ∈ Pεᶜ, x p * (G.pathLatency x p - G.cost x) ^ 2 :=
      Finset.sum_congr rfl fun p _ => by ring
    rw [← hsq]
    exact sq_sum_mul_le_sum_mul_sum_mul_sq Pεᶜ fun p _ => hnn p
  have hsplit : ∑ p, x p * (G.pathLatency x p - G.cost x) ^ 2 =
      (∑ p ∈ Pε, x p * (G.pathLatency x p - G.cost x) ^ 2) +
        (∑ p ∈ Pεᶜ, x p * (G.pathLatency x p - G.cost x) ^ 2) :=
    (Finset.sum_add_sum_compl Pε _).symm
  have hvar_ge : (a / (1 - a)) * (ε * G.cost x) ^ 2 ≤
      ∑ p, x p * (G.pathLatency x p - G.cost x) ^ 2 := by
    rw [hsplit]
    calc (a / (1 - a)) * (ε * G.cost x) ^ 2
        = (a * (ε * G.cost x)) ^ 2 / a + (a * (ε * G.cost x)) ^ 2 / (1 - a) := by
          field_simp; ring
      _ ≤ Δ ^ 2 / a + Δ ^ 2 / (1 - a) := by
          gcongr
      _ ≤ (∑ p ∈ Pε, x p * (G.pathLatency x p - G.cost x) ^ 2) +
            (∑ p ∈ Pεᶜ, x p * (G.pathLatency x p - G.cost x) ^ 2) := add_le_add hcs1 hcs2
  have hratio_gt : ε < a / (1 - a) := by
    rw [lt_div_iff₀ h1ma_pos]
    nlinarith
  calc ε ^ 3 * G.cost x ^ 2
      = ε * (ε * G.cost x) ^ 2 := by ring
    _ < (a / (1 - a)) * (ε * G.cost x) ^ 2 :=
        mul_lt_mul_of_pos_right hratio_gt (sq_pos_of_pos (mul_pos hε hcost))
    _ ≤ ∑ p, x p * (G.pathLatency x p - G.cost x) ^ 2 := hvar_ge

/-- **Theorem 29.12 (trajectory hitting time)** ([Suri2007], pp. 727–728): along any feasible
relative-rate replicator trajectory `x` with nonnegative, nondecreasing, continuous latencies on
`[0, 1]` and positive minimum feasible average latency `lStar`, for every `ε > 0` there is a time
`t ∈ [0, (2 / ε ^ 3) * ln(Φ(x 0) / lStar)]` at which `x t` is an `ε`-approximate equilibrium. -/
theorem IsReplicatorTrajectory.exists_mem_Icc_isApproxEquilibrium (h1 : G.rate () = 1)
    (hnonneg : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ G.latency e u)
    (hmono : ∀ e, MonotoneOn (G.latency e) (Icc 0 1))
    (hcont : ∀ e, ContinuousOn (G.latency e) (Icc 0 1))
    {lStar : ℝ} (hlStar : 0 < lStar) (hmin : ∀ y, G.IsFeasible y → lStar ≤ G.cost y)
    {x : ℝ → P → ℝ} (hx : G.IsReplicatorTrajectory (fun y => (G.cost y)⁻¹) x)
    (hfeas : ∀ t ≥ 0, G.IsFeasible (x t)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ Icc (0 : ℝ) (2 / ε ^ 3 * Real.log (G.potential lStar (x 0) / lStar)),
      G.IsApproxEquilibrium ε (x t) := by
  set T := 2 / ε ^ 3 * Real.log (G.potential lStar (x 0) / lStar)
  have hΦ0_ge : lStar ≤ G.potential lStar (x 0) := le_potential h1 hnonneg lStar (hfeas 0 le_rfl)
  have hratio_ge : 1 ≤ G.potential lStar (x 0) / lStar := (one_le_div hlStar).2 hΦ0_ge
  have hlog_nn : 0 ≤ Real.log (G.potential lStar (x 0) / lStar) := Real.log_nonneg hratio_ge
  have hT_nn : 0 ≤ T := mul_nonneg (by positivity) hlog_nn
  by_contra h
  push Not at h
  have hΦ_deriv : ∀ t ≥ 0,
      HasDerivWithinAt (fun s => G.potential lStar (x s))
        ((G.cost (x t))⁻¹ * (G.cost (x t) ^ 2 - ∑ p, x t p * G.pathLatency (x t) p ^ 2))
        (Ici 0) t := fun t ht => hasDerivWithinAt_potential h1 hx hfeas hcont lStar ht
  have hderiv_lt : ∀ t ∈ Icc (0 : ℝ) T,
      (G.cost (x t))⁻¹ * (G.cost (x t) ^ 2 - ∑ p, x t p * G.pathLatency (x t) p ^ 2) <
        -(ε ^ 3 / 2 * G.potential lStar (x t)) := fun t ht => by
    have hft := hfeas t ht.1
    obtain ⟨_, hsum⟩ := (isFeasible_unit_iff h1).1 hft
    have hcost_ge : lStar ≤ G.cost (x t) := hmin (x t) hft
    have hcost_pos : 0 < G.cost (x t) := hlStar.trans_le hcost_ge
    have hvar := variance_gt_of_not_isApproxEquilibrium h1 hnonneg hε hft hcost_pos (h t ht)
    have hpot_le := potential_le_two_mul_cost h1 hmono hcont hft hcost_ge
    rw [cost_sq_sub_sum_mul_sq hsum, mul_neg]
    have h1' : ε ^ 3 * G.cost (x t) <
        (G.cost (x t))⁻¹ * ∑ p, x t p * (G.pathLatency (x t) p - G.cost (x t)) ^ 2 := by
      have hmul := mul_lt_mul_of_pos_left hvar (inv_pos.2 hcost_pos)
      calc ε ^ 3 * G.cost (x t)
          = (G.cost (x t))⁻¹ * (ε ^ 3 * G.cost (x t) ^ 2) := by field_simp
        _ < (G.cost (x t))⁻¹ * ∑ p, x t p * (G.pathLatency (x t) p - G.cost (x t)) ^ 2 := hmul
    have h2' : ε ^ 3 / 2 * G.potential lStar (x t) ≤ ε ^ 3 * G.cost (x t) := by
      have hε3 : 0 < ε ^ 3 := pow_pos hε 3
      nlinarith
    linarith
  rcases hT_nn.eq_or_lt with hT0 | hTpos
  · have hlog0 : Real.log (G.potential lStar (x 0) / lStar) = 0 := by
      have hne : (2 : ℝ) / ε ^ 3 ≠ 0 := by positivity
      exact (mul_eq_zero.1 hT0.symm).resolve_left hne
    have hΦ0_eq : G.potential lStar (x 0) = lStar := by
      have hdiv1 : G.potential lStar (x 0) / lStar = 1 := by
        rcases Real.log_eq_zero.1 hlog0 with h0 | h1' | hm1
        · linarith
        · exact h1'
        · linarith
      exact (div_eq_one_iff_eq hlStar.ne').1 hdiv1
    have hd0 := hΦ_deriv 0 le_rfl
    have hd0_neg : (G.cost (x 0))⁻¹ *
        (G.cost (x 0) ^ 2 - ∑ p, x 0 p * G.pathLatency (x 0) p ^ 2) < 0 := by
      have hlt := hderiv_lt 0 ⟨le_rfl, hT_nn⟩
      have hpos : 0 < ε ^ 3 / 2 * G.potential lStar (x 0) :=
        mul_pos (by positivity) (hlStar.trans_le hΦ0_ge)
      linarith
    have hd0_nonneg : 0 ≤ (G.cost (x 0))⁻¹ *
        (G.cost (x 0) ^ 2 - ∑ p, x 0 p * G.pathLatency (x 0) p ^ 2) := by
      have htend : Filter.Tendsto (slope (fun s => G.potential lStar (x s)) 0)
          (𝓝[Ici (0 : ℝ) \ {0}] 0)
          (𝓝 ((G.cost (x 0))⁻¹ *
            (G.cost (x 0) ^ 2 - ∑ p, x 0 p * G.pathLatency (x 0) p ^ 2))) :=
        hasDerivWithinAt_iff_tendsto_slope.1 hd0
      have hdiff : Ici (0 : ℝ) \ {0} = Ioi 0 := by
        ext s; simp only [mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
        exact ⟨fun ⟨h1', h2'⟩ => lt_of_le_of_ne h1' (Ne.symm h2'), fun h1' => ⟨h1'.le, h1'.ne'⟩⟩
      rw [hdiff] at htend
      refine ge_of_tendsto htend (Filter.eventually_of_mem self_mem_nhdsWithin fun s hs => ?_)
      have hspos : 0 < s := hs
      rw [slope_def_field, sub_zero, hΦ0_eq]
      exact div_nonneg (sub_nonneg.2 (le_potential h1 hnonneg lStar (hfeas s hspos.le))) hspos.le
    linarith
  · set c := ε ^ 3 / 2
    let F : ℝ → ℝ := fun t => Real.exp (c * t) * G.potential lStar (x t)
    have hFd : ∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt F
          (Real.exp (c * t) * (c * G.potential lStar (x t) +
            (G.cost (x t))⁻¹ * (G.cost (x t) ^ 2 - ∑ p, x t p * G.pathLatency (x t) p ^ 2)))
          (Icc 0 T) t := fun t ht => by
      have hexp :
          HasDerivWithinAt (fun s => Real.exp (c * s)) (Real.exp (c * t) * c) (Icc 0 T) t := by
          have hlin : HasDerivAt (fun s => c * s) c t := by
            simpa only [mul_one] using (hasDerivAt_id' t).const_mul c
          exact hlin.exp.hasDerivWithinAt
      have hmul := hexp.mul ((hΦ_deriv t ht.1).mono fun _ hs => hs.1)
      convert hmul using 1
      ring
    have hanti : StrictAntiOn F (Icc 0 T) :=
      strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 T)
        (fun t ht => (hFd t ht).continuousWithinAt)
        (fun t ht => (hFd t (interior_subset ht)).mono interior_subset)
        (fun t ht => mul_neg_of_pos_of_neg (Real.exp_pos _) (by
          linarith [hderiv_lt t (interior_subset ht)]))
    have hFT_lt : F T < F 0 := hanti ⟨le_rfl, hTpos.le⟩ ⟨hTpos.le, le_rfl⟩ hTpos
    have hcT : c * T = Real.log (G.potential lStar (x 0) / lStar) := by
      simp only [c, T]
      field_simp
    have hF0 : F 0 = G.potential lStar (x 0) := by
      simp only [F, mul_zero, Real.exp_zero, one_mul]
    have hFT : F T = (G.potential lStar (x 0) / lStar) * G.potential lStar (x T) := by
      simp only [F, hcT, Real.exp_log (div_pos (hlStar.trans_le hΦ0_ge) hlStar)]
    rw [hFT, hF0] at hFT_lt
    have hΦT_ge : lStar ≤ G.potential lStar (x T) :=
      le_potential h1 hnonneg lStar (hfeas T hTpos.le)
    have hΦ0_pos : 0 < G.potential lStar (x 0) := hlStar.trans_le hΦ0_ge
    have hge : G.potential lStar (x 0) ≤
        (G.potential lStar (x 0) / lStar) * G.potential lStar (x T) := by
      calc G.potential lStar (x 0)
          = (G.potential lStar (x 0) / lStar) * lStar := by field_simp
        _ ≤ (G.potential lStar (x 0) / lStar) * G.potential lStar (x T) :=
            mul_le_mul_of_nonneg_left hΦT_ge (div_pos hΦ0_pos hlStar).le
    linarith

end Convergence

/-- **Theorem 29.12: fast convergence of imitative dynamics to an `ε`-approximate equilibrium**
([Suri2007], Section 29.3.3, pp. 727–728).

In a single-commodity nonatomic congestion game with unit flow rate, nonnegative nondecreasing
Lipschitz latency functions on `[0, 1]`, positive minimum feasible average latency `lStar`, and a
feasible initial flow `x₀` with `G.cost x₀ ≤ lMax`, there exists a global trajectory `x` on
`[0, ∞)` starting at `x₀` that follows the relative-rate imitative/replicator dynamics
`x'_p = l̄(x)⁻¹ x_p (l̄(x) - l_p(x))`, remains feasible for all `t ≥ 0` ([Suri2007],
Exercise 29.6), and for every `ε > 0` reaches an `ε`-approximate equilibrium
([Suri2007], Definition 29.11) at some time `t ∈ [0, (2 / ε ^ 3) * ln(2 * lMax / lStar)]`
(sharpening the constant `4` in [Suri2007], p. 728 to `2`, and establishing the
`O(ε⁻³ ln(l_max / l*))` hitting-time bound). -/
theorem exists_relativeReplicatorTrajectory_isApproxEquilibrium
    {P E : Type*} [Fintype P] [Finite E] [DecidableEq E] {G : NonatomicCongestionGame Unit P E}
    (h1 : G.rate () = 1)
    (hnonneg : ∀ e, ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ G.latency e u)
    (hmono : ∀ e, MonotoneOn (G.latency e) (Icc 0 1))
    (hlip : ∀ e, ∃ K, LipschitzOnWith K (G.latency e) (Icc 0 1))
    {lStar lMax : ℝ} (hlStar : 0 < lStar) (hmin : ∀ y, G.IsFeasible y → lStar ≤ G.cost y)
    {x₀ : P → ℝ} (hx₀ : G.IsFeasible x₀) (hlMax : G.cost x₀ ≤ lMax) :
    ∃ x : ℝ → P → ℝ, x 0 = x₀ ∧ G.IsReplicatorTrajectory (fun y => (G.cost y)⁻¹) x ∧
      (∀ t ≥ 0, G.IsFeasible (x t)) ∧
      ∀ ε > 0, ∃ t ∈ Icc (0 : ℝ) (2 / ε ^ 3 * Real.log (2 * lMax / lStar)),
        G.IsApproxEquilibrium ε (x t) := by
  have := Fintype.ofFinite E
  have hcont : ∀ e, ContinuousOn (G.latency e) (Icc 0 1) := fun e => by
    obtain ⟨K, hK⟩ := hlip e
    exact hK.continuousOn
  obtain ⟨x, hx0, hxtraj, hxfeas⟩ :=
    exists_relativeReplicatorTrajectory h1 hnonneg hlip hlStar hmin hx₀
  refine ⟨x, hx0, hxtraj, hxfeas, fun ε hε => ?_⟩
  obtain ⟨t, ht, happrox⟩ :=
    hxtraj.exists_mem_Icc_isApproxEquilibrium h1 hnonneg hmono hcont hlStar hmin hxfeas hε
  refine ⟨t, ⟨ht.1, ht.2.trans ?_⟩, happrox⟩
  have hΦ0_pos : 0 < G.potential lStar (x 0) :=
    hlStar.trans_le (le_potential h1 hnonneg lStar (hxfeas 0 le_rfl))
  have hΦ0_le : G.potential lStar (x 0) ≤ 2 * lMax := by
    rw [hx0]
    exact (potential_le_two_mul_cost h1 hmono hcont hx₀ (hmin x₀ hx₀)).trans (by linarith)
  have hdiv_le : G.potential lStar (x 0) / lStar ≤ 2 * lMax / lStar :=
    div_le_div_of_nonneg_right hΦ0_le hlStar.le
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (div_pos hΦ0_pos hlStar) hdiv_le) (by positivity)

end Cslib.GameTheory.NonatomicCongestionGame
