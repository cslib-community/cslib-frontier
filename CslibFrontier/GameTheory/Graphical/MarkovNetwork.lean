/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Graphical.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TreeSide
import CslibFrontier.GameTheory.Graphical.TreeNash
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order.Compact

/-!
# Local Markov networks and tree correlated equilibria for graphical games

This module formalizes [Kearns2007], §§7.4.2–7.4.3 (Definition 7.11, Lemma 7.12, Theorems 7.13 and
7.14, pp. 172–175), characterizing correlated equilibria of graphical games via local Markov
networks and the polynomial-size local linear program on trees.

## Boundary-support subtlety for Lemma 7.12 and Theorem 7.13

In [Kearns2007], §7.4.2 (pp. 172–174), Lemma 7.12 and Theorem 7.13 are stated without a positivity
hypothesis on the joint distribution `P`. That unguarded statement is **false** at zero-support
boundary distributions on non-chordal graphs: on the 4-cycle `C₄` (`SimpleGraph.cycleGraph 4`) with
binary actions `Bool`, there is a `{0, 1}`-payoff graphical game `M` and a correlated equilibrium
`σ` (uniform on the four Hamming-weight-1 profiles) such that *every* `τ` with
`M.ExpectedPayoffEquiv τ σ` equals `σ`, yet `σ` is not representable as a local Markov network on
`C₄` even with nonnegative potentials `ψ_i ≥ 0`
(`exists_ce_not_expectedPayoffEquiv_isLocalMarkovNetwork_cycle4`,
`exists_not_localNeighborhoodEquiv_isLocalMarkovNetwork_cycle4`).

Accordingly, this module establishes all four facets faithfully:
1. **Definition 7.11 (p. 172):** `IsLocalMarkovNetwork` (nonnegative potentials `ψ_i ≥ 0`,
   partition function `Z > 0`) and its strictly positive refinement
   `IsPositiveLocalMarkovNetwork` (`ψ_i > 0`), with normalized/unnormalized equivalence and
   complete-graph universality (`isLocalMarkovNetwork_top`).
2. **Checked `C₄` counterexample:** refutes the literal unguarded forms of Lemma 7.12 and
   Theorem 7.13 at zero-support boundary distributions.
3. **Positive-support Lemma 7.12 & Theorem 7.13 and general `ε`-approximation:**
   * When `σ` admits a strictly positive local-neighborhood equivalent representative (in particular
     whenever `∀ s, 0 < σ.weights s`), maximizing Shannon entropy over
     `{τ | LocalNeighborhoodEquiv G τ σ}` yields an exact strictly positive local Markov network
     `τ` with `LocalNeighborhoodEquiv G τ σ`
     (`exists_isPositiveLocalMarkovNetwork_of_exists_pos`), and preserves correlated equilibria and
     expected payoffs (`GraphicalGame.exists_isPositiveLocalMarkovNetwork_ce_of_exists_pos`).
   * For **every** finite graphical game `M`, **every** correlated equilibrium `σ` (zeros allowed),
     and **every** `ε > 0`, mixing with the uniform distribution yields a strictly positive local
     Markov network `τ` that is an `ε`-correlated equilibrium with expected payoffs and local
     neighborhood marginals within `ε` of `σ`
     (`exists_isPositiveLocalMarkovNetwork_neighborhoodMarginal_approx`,
     `GraphicalGame.exists_isPositiveLocalMarkovNetwork_isApproxCorrelatedEquilibrium`).
4. **Unconditional tree Markov networks and exact Theorem 7.14 (pp. 174–175):**
   * On any finite tree `hT : G.IsTree` (zeros allowed, **no** positivity hypothesis), junction-tree
     lifting constructs from any locally normalized, edge-consistent marginal family `q` a global
     joint distribution `σ` that is a nonnegative local Markov network on `G` with exact marginals
     `neighborhoodMarginal G σ i u = q i u` (`treeLift_exists_isLocalMarkovNetwork`).
   * As immediate corollaries, Lemma 7.12 and Theorem 7.13 hold **unconditionally** (without
     positivity) on all finite trees (`exists_isLocalMarkovNetwork_of_isTree`,
     `GraphicalGame.exists_isLocalMarkovNetwork_ce_of_isTree`).
   * **Theorem 7.14 (p. 175):** on any finite tree graphical game `(G, M)`, the local LP constraints
     (`GraphicalGame.IsLocalCorrelatedEquilibrium`, equivalently edge-consistent local CE
     constraints) are sound and complete for global correlated equilibria, preserving every
     player's expected payoff and every local linear objective such as social welfare
     (`GraphicalGame.exists_isCorrelatedEquilibrium_of_isLocalCorrelatedEquilibrium`,
     `GraphicalGame.isLocalCorrelatedEquilibrium_iff_exists_isCorrelatedEquilibrium`), with
     `M.tableEntries ≤ Fintype.card ι * m ^ (d + 1)` variables, at most `Fintype.card ι * m ^ 2`
     local CE inequalities, and at most `2 * (Fintype.card ι - 1) * m ^ 2` directed
     edge-consistency equations (`GraphicalGame.treeLocalCE_size_bounds`). Machine LP solver
     running-time bounds remain separate.

## Main definitions

* `Cslib.GameTheory.IsLocalMarkovNetwork`, `Cslib.GameTheory.IsPositiveLocalMarkovNetwork`:
  local Markov networks on `G` ([Kearns2007], Definition 7.11, p. 172).
* `Cslib.GameTheory.edgeMarginal`, `Cslib.GameTheory.IsEdgeConsistent`,
  `Cslib.GameTheory.restrictMarginal`, `Cslib.GameTheory.IsIntersectionConsistent`,
  `Cslib.GameTheory.IsLocalDistribution`: local neighborhood marginals and consistency constraints.
* `Cslib.GameTheory.GraphicalGame.SatisfiesLocalCE`,
  `Cslib.GameTheory.GraphicalGame.IsLocalCorrelatedEquilibrium`: Kearns's local correlated
  equilibrium linear program ([Kearns2007], §7.4.3, constraints (i)–(iii), p. 175).

## Main results

* `Cslib.GameTheory.exists_ce_not_expectedPayoffEquiv_isLocalMarkovNetwork_cycle4`,
  `Cslib.GameTheory.exists_not_localNeighborhoodEquiv_isLocalMarkovNetwork_cycle4`: boundary
  counterexample on `C₄` refuting unguarded Lemma 7.12 and Theorem 7.13.
* `Cslib.GameTheory.exists_isPositiveLocalMarkovNetwork_of_exists_pos`,
  `Cslib.GameTheory.GraphicalGame.exists_isPositiveLocalMarkovNetwork_ce_of_exists_pos`:
  positive-support Lemma 7.12 and Theorem 7.13 via maximum entropy.
* `Cslib.GameTheory.exists_isPositiveLocalMarkovNetwork_neighborhoodMarginal_approx`,
  `Cslib.GameTheory.GraphicalGame.exists_isPositiveLocalMarkovNetwork_isApproxCorrelatedEquilibrium`
  (`ε`-approximate Markov network closure for arbitrary distributions and correlated equilibria).
* `Cslib.GameTheory.treeLift_exists_isLocalMarkovNetwork`,
  `Cslib.GameTheory.exists_isLocalMarkovNetwork_of_isTree`,
  `Cslib.GameTheory.GraphicalGame.exists_isLocalMarkovNetwork_ce_of_isTree`: unconditional
  junction-tree lifting and local Markov network representation on all finite trees.
* `Cslib.GameTheory.GraphicalGame.exists_isCorrelatedEquilibrium_of_isLocalCorrelatedEquilibrium`,
  `Cslib.GameTheory.GraphicalGame.isLocalCorrelatedEquilibrium_iff_exists_isCorrelatedEquilibrium`,
  `Cslib.GameTheory.GraphicalGame.treeLocalCE_size_bounds`: soundness, completeness, and
  polynomial LP size for tree correlated equilibria ([Kearns2007], Theorem 7.14, p. 175).

## References

* [M. Kearns, *Graphical Games*, Chapter 7 of *Algorithmic Game Theory*][Kearns2007]
-/

public section

namespace Cslib.GameTheory

open Finset Function

/-! ### Private utilities on finite standard simplices -/

private noncomputable def simplexOfFun {X : Type*} [Fintype X] (w : X → ℝ)
    (hnn : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) : Convexity.StdSimplex ℝ X where
  weights := Finsupp.equivFunOnFinite.symm w
  nonneg x := by simpa using hnn x
  total := by simpa [Finsupp.sum_fintype] using hsum

@[simp] private theorem simplexOfFun_weights {X : Type*} [Fintype X] (w : X → ℝ)
    (hnn : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (x : X) :
    (simplexOfFun w hnn hsum).weights x = w x := by
  simp [simplexOfFun]

private theorem neighborhoodMarginal_eq_sum {ι : Type*} {S : ι → Type*}
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    [DecidableEq (∀ j : ClosedNeighborhood G i, S j.1)]
    (u : ∀ j : ClosedNeighborhood G i, S j.1) :
    neighborhoodMarginal G σ i u =
      ∑ s : (∀ k, S k),
        if (fun j : ClosedNeighborhood G i => s j.1) = u then σ.weights s else 0 := by
  rw [neighborhoodMarginal_def, Finsupp.sum_fintype]
  intro s
  split_ifs <;> rfl

private theorem sum_mul_local_eq_sum_neighborhoodMarginal {ι : Type*} {S : ι → Type*}
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    (f : (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) :
    σ.weights.sum (fun s w => w * f (fun j => s j.1)) =
      ∑ u : (∀ j : ClosedNeighborhood G i, S j.1), neighborhoodMarginal G σ i u * f u := by
  classical
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp_rw [neighborhoodMarginal_eq_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  simp only [ite_mul, zero_mul,
    sum_ite_eq univ (fun j : ClosedNeighborhood G i => s j.1) (fun u => σ.weights s * f u),
    mem_univ, ↓reduceIte]

private theorem sum_ite_neighborhoodMarginal {ι : Type*} {S : ι → Type*}
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    (p : (∀ j : ClosedNeighborhood G i, S j.1) → Prop) [DecidablePred p] :
    (∑ u, if p u then neighborhoodMarginal G σ i u else 0) =
      ∑ s : (∀ j, S j), if p (fun j => s j.1) then σ.weights s else 0 := by
  have h := sum_mul_local_eq_sum_neighborhoodMarginal G σ i (fun u => if p u then 1 else 0)
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)] at h
  simpa only [mul_ite, mul_one, mul_zero] using h.symm

private theorem neighborhoodMarginal_nonneg {ι : Type*} {S : ι → Type*}
    [Finite ι] [∀ i, Finite (S i)] (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    (u : ∀ j : ClosedNeighborhood G i, S j.1) :
    0 ≤ neighborhoodMarginal G σ i u := by
  classical
  have := Fintype.ofFinite ι
  have := fun k => Fintype.ofFinite (S k)
  rw [neighborhoodMarginal_eq_sum]
  exact sum_nonneg fun s _ => by split_ifs <;> [exact σ.weights_nonneg s; exact le_rfl]

private theorem sum_neighborhoodMarginal {ι : Type*} {S : ι → Type*}
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι) :
    ∑ u : (∀ j : ClosedNeighborhood G i, S j.1), neighborhoodMarginal G σ i u = 1 := by
  have h := sum_mul_local_eq_sum_neighborhoodMarginal G σ i (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [← h, σ.total]

private theorem neighborhoodMarginal_le_one {ι : Type*} {S : ι → Type*}
    [Finite ι] [∀ i, Finite (S i)] (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    (u : ∀ j : ClosedNeighborhood G i, S j.1) :
    neighborhoodMarginal G σ i u ≤ 1 := by
  classical
  have := Fintype.ofFinite ι
  have := fun k => Fintype.ofFinite (S k)
  rw [← sum_neighborhoodMarginal G σ i]
  exact single_le_sum (fun v _ => neighborhoodMarginal_nonneg G σ i v) (mem_univ u)

private theorem neighborhoodMarginal_convexCombPair {ι : Type*} {S : ι → Type*}
    [Finite ι] [∀ i, Finite (S i)] (G : SimpleGraph ι)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (σ₁ σ₂ : Convexity.StdSimplex ℝ (∀ i, S i)) (i : ι)
    (u : ∀ j : ClosedNeighborhood G i, S j.1) :
    neighborhoodMarginal G (Convexity.convexCombPair a b ha hb hab σ₁ σ₂) i u =
      a * neighborhoodMarginal G σ₁ i u + b * neighborhoodMarginal G σ₂ i u := by
  classical
  have := Fintype.ofFinite ι
  have := fun k => Fintype.ofFinite (S k)
  simp only [neighborhoodMarginal_eq_sum, Convexity.StdSimplex.weights_convexCombPair,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  split_ifs <;> ring

/-! ### 1. Local Markov networks ([Kearns2007], Definition 7.11, p. 172) -/

section LocalMarkovNetwork

variable {ι : Type*} {S : ι → Type*}

/-- A joint distribution `σ` is representable as a **local Markov network** with graph `G`
([Kearns2007], Definition 7.11, p. 172) if there exist nonnegative local potential functions
`ψ i : (∀ j : ClosedNeighborhood G i, S j.1) → ℝ` (`0 ≤ ψ i u`) and a positive normalization
constant `Z > 0` such that `σ.weights s = (∏ i, ψ i (fun j => s j.1)) / Z` for every profile `s`.
-/
@[expose] def IsLocalMarkovNetwork [Fintype ι] (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) : Prop :=
  ∃ (ψ : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) (Z : ℝ),
    (∀ i u, 0 ≤ ψ i u) ∧ 0 < Z ∧
      ∀ s : (∀ i, S i), σ.weights s = (∏ i : ι, ψ i (fun j => s j.1)) / Z

/-- A joint distribution `σ` is representable as a **strictly positive local Markov network** with
graph `G` if its potentials in Definition 7.11 ([Kearns2007], p. 172) are everywhere strictly
positive (`0 < ψ i u`). -/
@[expose] def IsPositiveLocalMarkovNetwork [Fintype ι] (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) : Prop :=
  ∃ (ψ : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) (Z : ℝ),
    (∀ i u, 0 < ψ i u) ∧ 0 < Z ∧
      ∀ s : (∀ i, S i), σ.weights s = (∏ i : ι, ψ i (fun j => s j.1)) / Z

theorem IsPositiveLocalMarkovNetwork.isLocalMarkovNetwork [Fintype ι] {G : SimpleGraph ι}
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} (h : IsPositiveLocalMarkovNetwork G σ) :
    IsLocalMarkovNetwork G σ := by
  obtain ⟨ψ, Z, hpos, hZ, hfac⟩ := h
  exact ⟨ψ, Z, fun i u => (hpos i u).le, hZ, hfac⟩

theorem IsPositiveLocalMarkovNetwork.weights_pos [Fintype ι] {G : SimpleGraph ι}
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} (h : IsPositiveLocalMarkovNetwork G σ)
    (s : ∀ i, S i) :
    0 < σ.weights s := by
  obtain ⟨ψ, Z, hpos, hZ, hfac⟩ := h
  rw [hfac s]
  exact div_pos (prod_pos fun i _ => hpos i _) hZ

/-- On finite action sets, the normalization constant `Z` in `IsLocalMarkovNetwork` is uniquely
determined as the partition function `∑ s, ∏ i, ψ i (fun j => s j.1)` ([Kearns2007],
Definition 7.11, p. 172). -/
theorem partition_eq_of_weights_eq_prod_div [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]
    {G : SimpleGraph ι} {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    {ψ : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ} {Z : ℝ} (hZ : 0 < Z)
    (hfac : ∀ s : (∀ i, S i), σ.weights s = (∏ i : ι, ψ i (fun j => s j.1)) / Z) :
    Z = ∑ s : (∀ i, S i), ∏ i : ι, ψ i (fun j => s j.1) := by
  have hsum : (1 : ℝ) = (∑ s : (∀ i, S i), ∏ i : ι, ψ i (fun j => s j.1)) / Z := by
    rw [← σ.total_of_fintype, div_eq_mul_inv, sum_mul]
    exact sum_congr rfl fun s _ => by rw [hfac s, div_eq_mul_inv]
  have hne : Z ≠ 0 := hZ.ne'
  field_simp [hne] at hsum
  linarith

private theorem exists_prod_div_iff_exists_prod [Fintype ι] [Nonempty ι] {G : SimpleGraph ι}
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} (P : ℝ → Prop)
    (hdiv : ∀ x Z, P x → 0 < Z → P (x / Z)) :
    (∃ (ψ : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) (Z : ℝ),
      (∀ i u, P (ψ i u)) ∧ 0 < Z ∧
        ∀ s : (∀ i, S i), σ.weights s = (∏ i : ι, ψ i (fun j => s j.1)) / Z) ↔
      ∃ ψ : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ,
        (∀ i u, P (ψ i u)) ∧ ∀ s : (∀ i, S i), σ.weights s = ∏ i : ι, ψ i (fun j => s j.1) := by
  classical
  constructor
  · rintro ⟨ψ, Z, hP, hZ, hfac⟩
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨fun i u => if i = i₀ then ψ i u / Z else ψ i u, fun i u => ?_, fun s => ?_⟩
    · dsimp only
      split_ifs
      · exact hdiv _ _ (hP i u) hZ
      · exact hP i u
    · rw [hfac s, ← mul_prod_erase univ (fun i => ψ i (fun j => s j.1)) (mem_univ i₀),
        ← mul_prod_erase univ (fun i => if i = i₀ then ψ i (fun j => s j.1) / Z
          else ψ i (fun j => s j.1)) (mem_univ i₀)]
      simp only [↓reduceIte, div_mul_eq_mul_div]
      congr 1
      refine congrArg (ψ i₀ _ * ·) (prod_congr rfl fun i hi => ?_)
      simp [ne_of_mem_erase hi]
  · rintro ⟨ψ, hP, hfac⟩
    exact ⟨ψ, 1, hP, zero_lt_one, fun s => by rw [hfac s, div_one]⟩

/-- On a nonempty player set, absorbing `Z⁻¹` into a single vertex's potential yields an equivalent
unnormalized factorization for `IsLocalMarkovNetwork`. -/
theorem isLocalMarkovNetwork_iff_exists_prod [Fintype ι] [Nonempty ι] {G : SimpleGraph ι}
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} :
    IsLocalMarkovNetwork G σ ↔
      ∃ ψ : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ,
        (∀ i u, 0 ≤ ψ i u) ∧ ∀ s : (∀ i, S i), σ.weights s = ∏ i : ι, ψ i (fun j => s j.1) :=
  exists_prod_div_iff_exists_prod (0 ≤ ·) fun _ _ hx hZ => div_nonneg hx hZ.le

/-- Unnormalized characterization of `IsPositiveLocalMarkovNetwork` on a nonempty player set. -/
theorem isPositiveLocalMarkovNetwork_iff_exists_prod [Fintype ι] [Nonempty ι] {G : SimpleGraph ι}
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} :
    IsPositiveLocalMarkovNetwork G σ ↔
      ∃ ψ : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ,
        (∀ i u, 0 < ψ i u) ∧ ∀ s : (∀ i, S i), σ.weights s = ∏ i : ι, ψ i (fun j => s j.1) :=
  exists_prod_div_iff_exists_prod (0 < ·) fun _ _ hx hZ => div_pos hx hZ

/-- Adding edges preserves representability as a local Markov network. -/
theorem IsLocalMarkovNetwork.mono [Fintype ι] {G H : SimpleGraph ι} (hGH : G ≤ H)
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} (h : IsLocalMarkovNetwork G σ) :
    IsLocalMarkovNetwork H σ := by
  obtain ⟨ψ, Z, hnn, hZ, hfac⟩ := h
  refine ⟨fun i u => ψ i fun j => u ⟨j.1, j.2.imp id (fun hadj => hGH hadj)⟩, Z,
    fun i u => hnn i _, hZ, fun s => hfac s⟩

/-- Every joint distribution is representable as a local Markov network on the complete graph `⊤`
([Kearns2007], §7.4.2 remark after Definition 7.11, p. 172). -/
theorem isLocalMarkovNetwork_top [Fintype ι] (σ : Convexity.StdSimplex ℝ (∀ i, S i)) :
    IsLocalMarkovNetwork (⊤ : SimpleGraph ι) σ := by
  classical
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    have : Nonempty ι := ⟨i₀⟩
    rw [isLocalMarkovNetwork_iff_exists_prod]
    let fullOf : ∀ i (u : ∀ j : ClosedNeighborhood (⊤ : SimpleGraph ι) i, S j.1), (∀ k, S k) :=
      fun i u k => u ⟨k, if hki : k = i then Or.inl hki
        else Or.inr ((SimpleGraph.top_adj i k).mpr (Ne.symm hki))⟩
    refine ⟨fun i u => if i = i₀ then σ.weights (fullOf i u) else 1, fun i u => ?_, fun s => ?_⟩
    · dsimp only
      split_ifs
      · exact σ.weights_nonneg _
      · exact zero_le_one
    · rw [prod_eq_single i₀ (fun i _ hi => by simp [hi]) (fun h => (h (mem_univ i₀)).elim)]
      simp only [↓reduceIte]
      rfl
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    refine ⟨fun i => isEmptyElim i, 1, fun i => isEmptyElim i, zero_lt_one, fun s => ?_⟩
    rw [Convexity.StdSimplex.weights_apply_eq_one, Fintype.prod_empty, div_one]

end LocalMarkovNetwork

/-! ### 2. Boundary counterexample on `C₄` (refuting literal Lemma 7.12 & Theorem 7.13) -/

section Cycle4Counterexample

private abbrev cycle4 : SimpleGraph (Fin 4) := SimpleGraph.cycleGraph 4

private instance : DecidableRel cycle4.Adj := by
  intro i j
  rw [SimpleGraph.cycleGraph_adj]
  infer_instance

private def cycle4UnitPayoffNat (i : Fin 4) (s : Fin 4 → Bool) : ℕ :=
  if (univ.filter fun j : ClosedNeighborhood cycle4 i => s j.1).card = 1 then 1 else 0

private def cycle4UnitGame : GraphicalGame (Fin 4) (fun _ => Bool) where
  graph := cycle4
  localPayoff i u :=
    if (univ.filter fun j : ClosedNeighborhood cycle4 i => u j).card = 1 then 1 else 0

private def cycle4UnitProfile (k : Fin 4) : Fin 4 → Bool :=
  fun j => decide (j = k)

private def isWeightOne (s : Fin 4 → Bool) : Bool :=
  decide ((univ.filter fun j : Fin 4 => s j).card = 1)

private theorem card_isWeightOne :
    (univ.filter fun s : Fin 4 → Bool => isWeightOne s = true).card = 4 := by
  decide

private noncomputable def cycle4UnitDist : Convexity.StdSimplex ℝ (Fin 4 → Bool) :=
  simplexOfFun (fun s => if isWeightOne s then (1 / 4 : ℝ) else 0)
    (fun s => by split_ifs <;> norm_num)
    (by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul]
      have hc : (univ.filter fun s : Fin 4 → Bool => isWeightOne s = true).card = 4 :=
        card_isWeightOne
      rw [hc]
      norm_num)

private theorem cycle4UnitGame_payoff_eq_cast (i : Fin 4) (s : Fin 4 → Bool) :
    cycle4UnitGame.payoff i s = (cycle4UnitPayoffNat i s : ℝ) := by
  simp only [GraphicalGame.payoff_eq_localPayoff, cycle4UnitGame, cycle4UnitPayoffNat]
  split_ifs <;> simp

private theorem cycle4UnitPayoff_sum_le :
    ∀ s : Fin 4 → Bool, (∑ i : Fin 4, cycle4UnitPayoffNat i s) ≤ 3 := by
  decide

private theorem cycle4UnitPayoff_sum_eq_three_iff :
    ∀ s : Fin 4 → Bool, (∑ i : Fin 4, cycle4UnitPayoffNat i s) = 3 ↔ isWeightOne s = true := by
  decide

private theorem cycle4UnitPayoff_ce_nat :
    ∀ (i : Fin 4) (a b : Bool),
      (∑ s ∈ univ.filter fun s => isWeightOne s = true ∧ s i = a,
          cycle4UnitPayoffNat i (update s i b)) ≤
        (∑ s ∈ univ.filter fun s => isWeightOne s = true ∧ s i = a,
          cycle4UnitPayoffNat i s) := by
  decide

private theorem cycle4UnitPayoff_sum_weightOne :
    ∀ i : Fin 4,
      (∑ s ∈ univ.filter fun s => isWeightOne s = true, cycle4UnitPayoffNat i s) = 3 := by
  decide

private theorem isWeightOne_iff_exists_unitProfile :
    ∀ s : Fin 4 → Bool, isWeightOne s = true ↔ ∃ k : Fin 4, s = cycle4UnitProfile k := by
  decide

private theorem cycle4UnitProfile_injective : Function.Injective cycle4UnitProfile := by
  intro k₁ k₂ h
  have := congrFun h k₁
  simpa [cycle4UnitProfile] using this

private theorem cycle4UnitPayoff_unitProfile :
    ∀ (i k : Fin 4), cycle4UnitPayoffNat i (cycle4UnitProfile k) = if k = i + 2 then 0 else 1 := by
  decide

private theorem cycle4UnitProfile_opp_restrict :
    ∀ (i : Fin 4) (j : ClosedNeighborhood cycle4 i),
      cycle4UnitProfile (i + 2) j.1 = false := by
  decide

private theorem cycle4UnitDist_expectedPayoff (i : Fin 4) :
    cycle4UnitDist.weights.sum (fun s w => w * cycle4UnitGame.payoff i s) = 3 / 4 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp only [cycle4UnitDist, simplexOfFun_weights, cycle4UnitGame_payoff_eq_cast, ite_mul, zero_mul,
    ← sum_filter, ← mul_sum, ← Nat.cast_sum, cycle4UnitPayoff_sum_weightOne i]
  norm_num

/-- **Boundary counterexample on `C₄` refuting literal Lemma 7.12 and Theorem 7.13**
(contrast [Kearns2007], §7.4.2, pp. 172–174): on the 4-cycle `C₄ = SimpleGraph.cycleGraph 4` with
binary actions `Bool`, there exists a `{0, 1}`-payoff graphical game `M` and a correlated
equilibrium `σ` (uniform on the four Hamming-weight-1 profiles) such that every distribution `τ`
with `M.ExpectedPayoffEquiv τ σ` equals `σ`, yet `σ` is **not** representable as a local Markov
network on `C₄` (even with nonnegative potentials `ψ_i ≥ 0`). -/
theorem exists_ce_not_expectedPayoffEquiv_isLocalMarkovNetwork_cycle4 :
    ∃ (M : GraphicalGame (Fin 4) (fun _ => Bool)) (σ : Convexity.StdSimplex ℝ (Fin 4 → Bool)),
      M.graph = SimpleGraph.cycleGraph 4 ∧
      (∀ i u, 0 ≤ M.localPayoff i u ∧ M.localPayoff i u ≤ 1) ∧
      M.toCostGame.IsCorrelatedEquilibrium σ ∧
      (∀ τ, M.ExpectedPayoffEquiv τ σ → τ = σ) ∧
      ¬ IsLocalMarkovNetwork (SimpleGraph.cycleGraph 4) σ := by
  refine ⟨cycle4UnitGame, cycle4UnitDist, rfl, ?_, ?_, ?_, ?_⟩
  · intro i u
    simp only [cycle4UnitGame]
    split_ifs <;> norm_num
  · rw [CostGame.isCorrelatedEquilibrium_iff]
    intro i a b
    rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _),
      Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
    have hrewrite (f : (Fin 4 → Bool) → ℕ) :
        ∑ s : Fin 4 → Bool, cycle4UnitDist.weights s *
          (if s i = a then -(f s : ℝ) else 0) =
        -((1 / 4 : ℝ) *
          ((∑ s ∈ univ.filter fun s => isWeightOne s = true ∧ s i = a, f s : ℕ) : ℝ)) := by
      simp only [cycle4UnitDist, simplexOfFun_weights, Nat.cast_sum, mul_sum, ← sum_neg_distrib,
        sum_filter]
      refine sum_congr rfl fun s _ => ?_
      by_cases hw : isWeightOne s = true <;> by_cases hsi : s i = a <;> simp [hw, hsi]
    simp only [GraphicalGame.toCostGame_cost, cycle4UnitGame_payoff_eq_cast]
    rw [hrewrite (fun s => cycle4UnitPayoffNat i s),
      hrewrite (fun s => cycle4UnitPayoffNat i (update s i b))]
    have hnat : ((∑ s ∈ univ.filter fun s => isWeightOne s = true ∧ s i = a,
          cycle4UnitPayoffNat i (update s i b) : ℕ) : ℝ) ≤
        ((∑ s ∈ univ.filter fun s => isWeightOne s = true ∧ s i = a,
          cycle4UnitPayoffNat i s : ℕ) : ℝ) :=
      Nat.cast_le.mpr (cycle4UnitPayoff_ce_nat i a b)
    linarith
  · intro τ hEP
    -- Step 1: Total expected payoff equals `3`, forcing `τ` to be supported on weight-1 profiles.
    have hsum_pay : ∑ s : Fin 4 → Bool, τ.weights s *
        (3 - ∑ i : Fin 4, (cycle4UnitPayoffNat i s : ℝ)) = 0 := by
      have htot : ∑ i : Fin 4, τ.weights.sum (fun s w => w * cycle4UnitGame.payoff i s) = 3 := by
        calc ∑ i : Fin 4, τ.weights.sum (fun s w => w * cycle4UnitGame.payoff i s)
            = ∑ i : Fin 4, cycle4UnitDist.weights.sum (fun s w => w * cycle4UnitGame.payoff i s) :=
              sum_congr rfl fun i _ => hEP i
          _ = ∑ _i : Fin 4, (3 / 4 : ℝ) :=
              sum_congr rfl fun i _ => cycle4UnitDist_expectedPayoff i
          _ = 3 := by norm_num
      have hcomm : ∑ s : Fin 4 → Bool, τ.weights s * (∑ i : Fin 4, (cycle4UnitPayoffNat i s : ℝ)) =
          3 := by
        calc ∑ s : Fin 4 → Bool, τ.weights s * (∑ i : Fin 4, (cycle4UnitPayoffNat i s : ℝ))
            = ∑ s : Fin 4 → Bool, ∑ i : Fin 4, τ.weights s * (cycle4UnitPayoffNat i s : ℝ) :=
              sum_congr rfl fun s _ => mul_sum _ _ _
          _ = ∑ i : Fin 4, ∑ s : Fin 4 → Bool, τ.weights s * cycle4UnitGame.payoff i s := by
              rw [sum_comm]
              exact sum_congr rfl fun i _ => sum_congr rfl fun s _ => by
                rw [cycle4UnitGame_payoff_eq_cast]
          _ = ∑ i : Fin 4, τ.weights.sum (fun s w => w * cycle4UnitGame.payoff i s) :=
              sum_congr rfl fun i _ =>
                (Finsupp.sum_fintype τ.weights (fun s w => w * cycle4UnitGame.payoff i s)
                  (fun _ => zero_mul _)).symm
          _ = 3 := htot
      calc ∑ s : Fin 4 → Bool, τ.weights s * (3 - ∑ i : Fin 4, (cycle4UnitPayoffNat i s : ℝ))
          = (∑ s : Fin 4 → Bool, τ.weights s) * 3 -
              ∑ s : Fin 4 → Bool, τ.weights s * (∑ i : Fin 4, (cycle4UnitPayoffNat i s : ℝ)) := by
            simp only [mul_sub, sum_sub_distrib, ← sum_mul]
        _ = 1 * 3 - 3 := by rw [τ.total_of_fintype, hcomm]
        _ = 0 := by norm_num
    have hzero_of_not : ∀ s : Fin 4 → Bool, isWeightOne s ≠ true → τ.weights s = 0 := by
      intro s hs
      have hterm0 : τ.weights s * (3 - ∑ i : Fin 4, (cycle4UnitPayoffNat i s : ℝ)) = 0 := by
        have hall := (sum_eq_zero_iff_of_nonneg fun t _ => by
          refine mul_nonneg (τ.weights_nonneg t) ?_
          rw [← Nat.cast_sum]
          have : ((∑ i : Fin 4, cycle4UnitPayoffNat i t : ℕ) : ℝ) ≤ (3 : ℕ) :=
            Nat.cast_le.mpr (cycle4UnitPayoff_sum_le t)
          simpa using sub_nonneg.mpr this).mp hsum_pay
        exact hall s (mem_univ s)
      have hlt : ∑ i : Fin 4, cycle4UnitPayoffNat i s < 3 :=
        lt_of_le_of_ne (cycle4UnitPayoff_sum_le s)
          fun heq => hs ((cycle4UnitPayoff_sum_eq_three_iff s).mp heq)
      have hpos : (0 : ℝ) < 3 - ∑ i : Fin 4, (cycle4UnitPayoffNat i s : ℝ) := by
        rw [← Nat.cast_sum]
        have : ((∑ i : Fin 4, cycle4UnitPayoffNat i s : ℕ) : ℝ) < (3 : ℕ) := Nat.cast_lt.mpr hlt
        simpa using sub_pos.mpr this
      exact (mul_eq_zero.mp hterm0).resolve_right hpos.ne'
    -- Step 2: Each player's payoff `3 / 4` pins `τ.weights (cycle4UnitProfile (i + 2)) = 1 / 4`.
    have hfilt : (univ.filter fun s : Fin 4 → Bool => isWeightOne s = true) =
        univ.image cycle4UnitProfile := by
      ext s
      simp only [mem_filter, mem_univ, true_and, mem_image, isWeightOne_iff_exists_unitProfile]
      exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩
    have hsum_units : ∑ k : Fin 4, τ.weights (cycle4UnitProfile k) = 1 := by
      calc ∑ k : Fin 4, τ.weights (cycle4UnitProfile k)
          = ∑ s ∈ univ.image cycle4UnitProfile, τ.weights s :=
            (sum_image fun _ _ _ _ h => cycle4UnitProfile_injective h).symm
        _ = ∑ s ∈ univ.filter (fun s : Fin 4 → Bool => isWeightOne s = true), τ.weights s := by
            rw [hfilt]
        _ = ∑ s : Fin 4 → Bool, τ.weights s :=
            sum_subset (filter_subset _ _) fun s _ hs =>
              hzero_of_not s (by simpa using hs)
        _ = 1 := τ.total_of_fintype
    have hunit_val : ∀ k : Fin 4, τ.weights (cycle4UnitProfile k) = 1 / 4 := by
      intro k
      let i : Fin 4 := k + 2
      have hik : i + 2 = k := by fin_cases k <;> decide
      have heq := (hEP i).trans (cycle4UnitDist_expectedPayoff i)
      rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)] at heq
      have hval : ∑ s : Fin 4 → Bool, τ.weights s * cycle4UnitGame.payoff i s =
          1 - τ.weights (cycle4UnitProfile k) := by
        calc ∑ s : Fin 4 → Bool, τ.weights s * cycle4UnitGame.payoff i s
            = ∑ s ∈ univ.filter (fun s : Fin 4 → Bool => isWeightOne s = true),
                τ.weights s * cycle4UnitGame.payoff i s :=
              (sum_subset (filter_subset _ _) fun s _ hs => by
                rw [hzero_of_not s (by simpa using hs), zero_mul]).symm
          _ = ∑ m : Fin 4, τ.weights (cycle4UnitProfile m) *
                cycle4UnitGame.payoff i (cycle4UnitProfile m) := by
              rw [hfilt, sum_image fun _ _ _ _ h => cycle4UnitProfile_injective h]
          _ = ∑ m : Fin 4, if m = k then 0 else τ.weights (cycle4UnitProfile m) := by
              refine sum_congr rfl fun m _ => ?_
              rw [cycle4UnitGame_payoff_eq_cast, cycle4UnitPayoff_unitProfile i m, hik]
              split_ifs <;> simp
          _ = (∑ m : Fin 4, τ.weights (cycle4UnitProfile m)) - τ.weights (cycle4UnitProfile k) := by
              rw [← add_sum_erase univ (fun m => τ.weights (cycle4UnitProfile m)) (mem_univ k),
                ← add_sum_erase univ (fun m => if m = k then 0 else τ.weights (cycle4UnitProfile m))
                  (mem_univ k)]
              simp only [↓reduceIte, zero_add]
              rw [sum_congr rfl fun m hm => ite_eq_right (ne_of_mem_erase hm)]
              ring
          _ = 1 - τ.weights (cycle4UnitProfile k) := by rw [hsum_units]
      linarith
    ext s
    by_cases hs : isWeightOne s = true
    · obtain ⟨k, rfl⟩ := (isWeightOne_iff_exists_unitProfile s).mp hs
      simp [cycle4UnitDist, hs, hunit_val k]
    · simp [cycle4UnitDist, hs, hzero_of_not s hs]
  · rintro ⟨ψ, Z, hnn, hZ, hfac⟩
    have hpsi_pos : ∀ i : Fin 4, 0 < ψ i (fun _ => false) := by
      intro i
      have hw : 0 < cycle4UnitDist.weights (cycle4UnitProfile (i + 2)) := by
        have hw1 : isWeightOne (cycle4UnitProfile (i + 2)) = true :=
          (isWeightOne_iff_exists_unitProfile _).mpr ⟨i + 2, rfl⟩
        simp [cycle4UnitDist, hw1]
      rw [hfac (cycle4UnitProfile (i + 2))] at hw
      have hprod_pos : 0 < ∏ j : Fin 4, ψ j (fun k => cycle4UnitProfile (i + 2) k.1) :=
        (div_pos_iff_of_pos_right hZ).mp hw
      have hfactor_ne : ψ i (fun k => cycle4UnitProfile (i + 2) k.1) ≠ 0 := fun h0 =>
        hprod_pos.ne' (prod_eq_zero (mem_univ i) h0)
      have hrestrict : (fun k : ClosedNeighborhood cycle4 i => cycle4UnitProfile (i + 2) k.1) =
          fun _ => false := funext fun k => cycle4UnitProfile_opp_restrict i k
      rw [hrestrict] at hfactor_ne
      exact (hnn i _).lt_of_ne' hfactor_ne
    have hall_pos : 0 < cycle4UnitDist.weights (fun _ => false) := by
      rw [hfac (fun _ => false)]
      exact div_pos (prod_pos fun i _ => hpsi_pos i) hZ
    have hall_zero : cycle4UnitDist.weights (fun _ => false) = 0 := by
      have hnot : isWeightOne (fun _ : Fin 4 => false) = false := by decide
      simp [cycle4UnitDist, hnot]
    linarith

/-- **Boundary counterexample on `C₄` refuting literal Lemma 7.12** ([Kearns2007], §7.4.2, p. 172):
there exists a joint distribution `σ` on `C₄` with binary actions for which no local Markov network
`τ` on `C₄` is local-neighborhood equivalent to `σ`. -/
theorem exists_not_localNeighborhoodEquiv_isLocalMarkovNetwork_cycle4 :
    ∃ σ : Convexity.StdSimplex ℝ (Fin 4 → Bool),
      ∀ τ, LocalNeighborhoodEquiv (SimpleGraph.cycleGraph 4) τ σ →
        ¬ IsLocalMarkovNetwork (SimpleGraph.cycleGraph 4) τ := by
  obtain ⟨M, σ, hG, _, _, huniq, hnot⟩ :=
    exists_ce_not_expectedPayoffEquiv_isLocalMarkovNetwork_cycle4
  refine ⟨σ, fun τ hln hmk => ?_⟩
  have hln' : LocalNeighborhoodEquiv M.graph τ σ := hG.symm ▸ hln
  have heq : τ = σ := huniq τ hln'.expectedPayoffEquiv
  exact hnot (heq ▸ hmk)

end Cycle4Counterexample

/-! ### 3. Positive-support Lemma 7.12 & Theorem 7.13 via maximum entropy -/

section MaxEntropy

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [∀ i, Finite (S i)]

/-- **Positive-support Lemma 7.12** ([Kearns2007], §7.4.2, pp. 172–174): if `σ` admits a strictly
positive local-neighborhood equivalent distribution `τ₀` with respect to `G`, then the maximum
Shannon-entropy distribution in `{τ | LocalNeighborhoodEquiv G τ σ}` is a strictly positive local
Markov network with graph `G`. (The positivity hypothesis is necessary on non-chordal graphs by
`exists_not_localNeighborhoodEquiv_isLocalMarkovNetwork_cycle4`.) -/
theorem exists_isPositiveLocalMarkovNetwork_of_exists_pos (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i))
    (hpos : ∃ τ₀ : Convexity.StdSimplex ℝ (∀ i, S i),
      LocalNeighborhoodEquiv G τ₀ σ ∧ ∀ s, 0 < τ₀.weights s) :
    ∃ τ : Convexity.StdSimplex ℝ (∀ i, S i),
      LocalNeighborhoodEquiv G τ σ ∧ IsPositiveLocalMarkovNetwork G τ := by
  classical
  have := fun i => Fintype.ofFinite (S i)
  by_cases hι : Nonempty ι
  · obtain ⟨τ₀, hτ₀_ln, hτ₀_pos⟩ := hpos
    let X := ∀ i : ι, S i
    let K : Set (Convexity.StdSimplex ℝ X) := {τ | LocalNeighborhoodEquiv G τ σ}
    -- Step 1: `K` is compact and nonempty.
    have hcont_marg (i : ι) (u : ∀ j : ClosedNeighborhood G i, S j.1) :
        Continuous (fun τ : Convexity.StdSimplex ℝ X => neighborhoodMarginal G τ i u) := by
      have heq : (fun τ : Convexity.StdSimplex ℝ X => neighborhoodMarginal G τ i u) =
          fun τ => ∑ s : X, if (fun j : ClosedNeighborhood G i => s j.1) = u
            then τ.weights s else 0 :=
        funext fun τ => neighborhoodMarginal_eq_sum G τ i u
      rw [heq]
      refine continuous_finsetSum (univ : Finset X) fun s _ => ?_
      split_ifs
      · exact Convexity.StdSimplex.continuous_weights_apply (R := ℝ) (M := X) s
      · exact continuous_const
    have hK_closed : IsClosed K := by
      have hK_eq : K = ⋂ i : ι, ⋂ u : (∀ j : ClosedNeighborhood G i, S j.1),
          {τ : Convexity.StdSimplex ℝ X |
            neighborhoodMarginal G τ i u = neighborhoodMarginal G σ i u} := by
        ext τ
        simp [K, LocalNeighborhoodEquiv]
      rw [hK_eq]
      exact isClosed_iInter fun i => isClosed_iInter fun u =>
        isClosed_eq (hcont_marg i u) continuous_const
    have hK_compact : IsCompact K := hK_closed.isCompact
    have hK_nonempty : K.Nonempty := ⟨τ₀, hτ₀_ln⟩
    -- Step 2: Maximize Shannon entropy `H τ = ∑ s, Real.negMulLog (τ.weights s)` on `K`.
    let H : Convexity.StdSimplex ℝ X → ℝ := fun τ => ∑ s : X, Real.negMulLog (τ.weights s)
    have hH_cont : Continuous H :=
      continuous_finsetSum (univ : Finset X) fun s _ =>
        Real.continuous_negMulLog.comp
          (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) (M := X) s)
    obtain ⟨τStar, hτStar_mem, hτStar_max⟩ :=
      hK_compact.exists_isMaxOn hK_nonempty hH_cont.continuousOn
    -- Step 3: Strict positivity of `τStar` via the infinite boundary slope of `negMulLog` at `0⁺`.
    have hτStar_pos : ∀ s : X, 0 < τStar.weights s := by
      intro s₀
      by_contra hle
      have h0 : τStar.weights s₀ = 0 :=
        le_antisymm (not_lt.mp hle) (τStar.weights_nonneg s₀)
      have hb_pos : 0 < τ₀.weights s₀ := hτ₀_pos s₀
      have hb_le : τ₀.weights s₀ ≤ 1 := τ₀.weights_apply_le_one s₀
      let M : ℝ := max 0 (H τStar) + 1
      have hM_pos : 0 < M := by positivity
      have hH_lt_M : H τStar < M := by
        have := le_max_right (0 : ℝ) (H τStar)
        linarith
      let t : ℝ := Real.exp (-M / τ₀.weights s₀) / 2
      have ht_pos : 0 < t := by positivity
      have hexp_lt_one : Real.exp (-M / τ₀.weights s₀) < 1 := by
        rw [Real.exp_lt_one_iff]
        exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hM_pos) hb_pos
      have ht_lt_one : t < 1 := by
        dsimp [t]; linarith
      have ht_le_one : 0 ≤ 1 - t := by linarith
      let τt : Convexity.StdSimplex ℝ X :=
        Convexity.convexCombPair (1 - t) t ht_le_one ht_pos.le (by ring) τStar τ₀
      have hτt_mem : τt ∈ K := by
        intro i u
        rw [neighborhoodMarginal_convexCombPair, hτStar_mem i u, hτ₀_ln i u]
        ring
      have hdiff_ge : t * (-τ₀.weights s₀ * Real.log (t * τ₀.weights s₀) - H τStar) ≤
          H τt - H τStar := by
        have hsub : H τt - H τStar =
            ∑ s : X, (Real.negMulLog ((1 - t) * τStar.weights s + t * τ₀.weights s) -
              Real.negMulLog (τStar.weights s)) := by
          simp only [H, ← sum_sub_distrib, τt, Convexity.StdSimplex.weights_convexCombPair,
            Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hsub, ← add_sum_erase univ _ (mem_univ s₀)]
        have hs₀_term :
            Real.negMulLog ((1 - t) * τStar.weights s₀ + t * τ₀.weights s₀) -
              Real.negMulLog (τStar.weights s₀) =
            t * (-τ₀.weights s₀ * Real.log (t * τ₀.weights s₀)) := by
          rw [h0, mul_zero, zero_add, Real.negMulLog_zero, sub_zero, Real.negMulLog]
          ring
        have hrest_ge :
            -t * H τStar ≤
              ∑ s ∈ univ.erase s₀,
                (Real.negMulLog ((1 - t) * τStar.weights s + t * τ₀.weights s) -
                  Real.negMulLog (τStar.weights s)) := by
          have hH_erase : H τStar = ∑ s ∈ univ.erase s₀, Real.negMulLog (τStar.weights s) := by
            dsimp only [H]
            rw [← add_sum_erase univ (fun s => Real.negMulLog (τStar.weights s)) (mem_univ s₀),
              h0, Real.negMulLog_zero, zero_add]
          rw [hH_erase, mul_sum]
          refine sum_le_sum fun s _ => ?_
          have hconc := Real.concaveOn_negMulLog.2
            (Set.mem_Ici.mpr (τStar.weights_nonneg s))
            (Set.mem_Ici.mpr (τ₀.weights_nonneg s))
            ht_le_one ht_pos.le (by ring : (1 - t) + t = 1)
          have hb_nn : 0 ≤ Real.negMulLog (τ₀.weights s) :=
            Real.negMulLog_nonneg (τ₀.weights_nonneg s) (τ₀.weights_apply_le_one s)
          simp only [smul_eq_mul] at hconc
          nlinarith
        linarith
      have hlog_lt : Real.log (t * τ₀.weights s₀) < -M / τ₀.weights s₀ := by
        have hprod_lt : t * τ₀.weights s₀ < Real.exp (-M / τ₀.weights s₀) := by
          have h1 : t * τ₀.weights s₀ ≤ t * 1 :=
            mul_le_mul_of_nonneg_left hb_le ht_pos.le
          have h2 : t < Real.exp (-M / τ₀.weights s₀) := by
            dsimp [t]
            have : 0 < Real.exp (-M / τ₀.weights s₀) := Real.exp_pos _
            linarith
          linarith
        calc Real.log (t * τ₀.weights s₀)
            < Real.log (Real.exp (-M / τ₀.weights s₀)) :=
              Real.log_lt_log (mul_pos ht_pos hb_pos) hprod_lt
          _ = -M / τ₀.weights s₀ := Real.log_exp _
      have hslope_pos : 0 < -τ₀.weights s₀ * Real.log (t * τ₀.weights s₀) - H τStar := by
        have hmul : τ₀.weights s₀ * Real.log (t * τ₀.weights s₀) < -M := by
          have := mul_lt_mul_of_pos_left hlog_lt hb_pos
          rwa [mul_div_cancel₀ (-M) hb_pos.ne'] at this
        linarith
      have hgt : H τStar < H τt := by
        have := mul_pos ht_pos hslope_pos
        linarith
      exact not_lt_of_ge (hτStar_max hτt_mem) hgt
    -- Step 4: First-order stationarity along the kernel of the neighborhood-marginal linear map.
    let Y := Σ i : ι, ∀ j : ClosedNeighborhood G i, S j.1
    let A : (X → ℝ) →ₗ[ℝ] (Y → ℝ) :=
      { toFun := fun v y =>
          ∑ s : X, if (fun j : ClosedNeighborhood G y.1 => s j.1) = y.2 then v s else 0
        map_add' := fun v w => by
          ext ⟨i, u⟩
          simp only [Pi.add_apply, ← sum_add_distrib]
          refine sum_congr rfl fun s _ => ?_
          split_ifs <;> ring
        map_smul' := fun c v => by
          ext ⟨i, u⟩
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
          refine sum_congr rfl fun s _ => ?_
          split_ifs <;> ring }
    let φ : Module.Dual ℝ (X → ℝ) :=
      { toFun := fun v => ∑ s : X, (-Real.log (τStar.weights s) - 1) * v s
        map_add' := fun v w => by
          simp only [Pi.add_apply, mul_add, sum_add_distrib]
        map_smul' := fun c v => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
          refine sum_congr rfl fun s _ => by ring }
    have hφ_ker : φ ∈ (LinearMap.ker A).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      rw [LinearMap.mem_ker] at hv
      have hv_marg : ∀ (i : ι) (u : ∀ j : ClosedNeighborhood G i, S j.1),
          (∑ s : X, if (fun j : ClosedNeighborhood G i => s j.1) = u then v s else 0) = 0 :=
        fun i u => congrFun hv ⟨i, u⟩
      obtain ⟨i₀⟩ := hι
      have hv_sum : ∑ s : X, v s = 0 := by
        have hsum0 : ∑ u : (∀ j : ClosedNeighborhood G i₀, S j.1),
            (∑ s : X, if (fun j : ClosedNeighborhood G i₀ => s j.1) = u then v s else 0) = 0 :=
          sum_eq_zero fun u _ => hv_marg i₀ u
        rw [sum_comm] at hsum0
        simpa only [sum_ite_eq univ, mem_univ, ↓reduceIte] using hsum0
      obtain ⟨s_any⟩ := τStar.nonempty
      let m : ℝ := univ.inf' ⟨s_any, mem_univ _⟩ (fun s => τStar.weights s)
      have hm_pos : 0 < m :=
        (Finset.lt_inf'_iff _).mpr fun s _ => hτStar_pos s
      let Mv : ℝ := 1 + ∑ s : X, |v s|
      have hMv_pos : 0 < Mv :=
        add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun s _ => abs_nonneg _)
      let δ : ℝ := m / Mv
      have hδ_pos : 0 < δ := div_pos hm_pos hMv_pos
      let g : ℝ → ℝ := fun t => ∑ s : X, Real.negMulLog (τStar.weights s + t * v s)
      have hg_max : IsLocalMax g 0 := by
        rw [IsLocalMax, IsMaxFilter]
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ_pos] with t ht
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
        have hw_nn : ∀ s : X, 0 ≤ τStar.weights s + t * v s := by
          intro s
          have hms : m ≤ τStar.weights s := Finset.inf'_le _ (mem_univ s)
          have hvs : |v s| ≤ Mv := by
            have := single_le_sum (fun x _ => abs_nonneg (v x)) (mem_univ s)
            linarith
          have habs : |t * v s| < m := by
            rw [abs_mul]
            calc |t| * |v s| ≤ |t| * Mv := mul_le_mul_of_nonneg_left hvs (abs_nonneg t)
              _ < δ * Mv := mul_lt_mul_of_pos_right ht hMv_pos
              _ = m := div_mul_cancel₀ m hMv_pos.ne'
          linarith [(abs_lt.mp habs).1]
        have hw_sum : ∑ s : X, (τStar.weights s + t * v s) = 1 := by
          rw [sum_add_distrib, τStar.total_of_fintype, ← mul_sum, hv_sum, mul_zero, add_zero]
        let τt : Convexity.StdSimplex ℝ X := simplexOfFun _ hw_nn hw_sum
        have hτt_mem : τt ∈ K := by
          intro i u
          rw [neighborhoodMarginal_eq_sum]
          simp only [τt, simplexOfFun_weights]
          have hsplit : (∑ s : X, if (fun j : ClosedNeighborhood G i => s j.1) = u
                then τStar.weights s + t * v s else 0) =
              (∑ s : X, if (fun j : ClosedNeighborhood G i => s j.1) = u
                then τStar.weights s else 0) +
              t * (∑ s : X, if (fun j : ClosedNeighborhood G i => s j.1) = u
                then v s else 0) := by
            rw [mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun s _ => ?_
            split_ifs <;> ring
          rw [hsplit, hv_marg i u, mul_zero, add_zero, ← neighborhoodMarginal_eq_sum]
          exact hτStar_mem i u
        have hle : H τt ≤ H τStar := hτStar_max hτt_mem
        simpa only [g, H, τt, simplexOfFun_weights, zero_mul, add_zero] using hle
      have hg_deriv : HasDerivAt g (φ v) 0 := by
        have hterm (s : X) (_ : s ∈ (univ : Finset X)) :
            HasDerivAt (fun t : ℝ => Real.negMulLog (τStar.weights s + t * v s))
              ((-Real.log (τStar.weights s) - 1) * v s) 0 := by
          have hlin : HasDerivAt (fun t : ℝ => τStar.weights s + t * v s) (v s) 0 := by
            simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v s)).const_add (τStar.weights s)
          have houter : HasDerivAt Real.negMulLog (-Real.log (τStar.weights s) - 1)
              (τStar.weights s + 0 * v s) := by
            simpa only [zero_mul, add_zero] using
              Real.hasDerivAt_negMulLog (hτStar_pos s).ne'
          exact houter.comp (0 : ℝ) hlin
        exact HasDerivAt.fun_sum hterm
      exact hg_max.hasDerivAt_eq_zero hg_deriv
    -- Step 5: Dual map surjectivity yields Lagrange multipliers on closed neighborhoods.
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hφ_ker
    obtain ⟨η, hη⟩ := hφ_ker
    let ψ : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ :=
      fun i u => Real.exp (-η (Pi.single ⟨i, u⟩ 1))
    refine ⟨τStar, hτStar_mem, ψ, Real.exp 1, fun i u => Real.exp_pos _, Real.exp_pos 1,
      fun s => ?_⟩
    have hsingle : A (Pi.single s 1) =
        ∑ i : ι, Pi.single (⟨i, fun j : ClosedNeighborhood G i => s j.1⟩ : Y) (1 : ℝ) := by
      ext ⟨i', u'⟩
      simp only [A, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
      have hLHS : (∑ t : X, if (fun j : ClosedNeighborhood G i' => t j.1) = u'
            then (Pi.single s (1 : ℝ) : X → ℝ) t else 0) =
          if (fun j : ClosedNeighborhood G i' => s j.1) = u' then (1 : ℝ) else 0 := by
        rw [sum_eq_single s (fun t _ hts => by simp [Pi.single_eq_of_ne hts])
          (fun h => (h (mem_univ s)).elim)]
        simp
      have hRHS : (∑ i : ι, (Pi.single (⟨i, fun j : ClosedNeighborhood G i => s j.1⟩ : Y)
            (1 : ℝ) : Y → ℝ) ⟨i', u'⟩) =
          if (fun j : ClosedNeighborhood G i' => s j.1) = u' then (1 : ℝ) else 0 := by
        rw [sum_eq_single i'
          (fun i _ hii' => Pi.single_eq_of_ne (fun heq => hii' (congrArg Sigma.fst heq).symm) _)
          (fun h => (h (mem_univ i')).elim)]
        by_cases hu : (fun j : ClosedNeighborhood G i' => s j.1) = u'
        · subst hu; simp
        · have hne : (⟨i', u'⟩ : Y) ≠ ⟨i', fun j : ClosedNeighborhood G i' => s j.1⟩ := by
            intro h; cases h; exact hu rfl
          simp [Pi.single_eq_of_ne hne, hu]
      rw [hLHS, hRHS]
    have hdual : ∑ i : ι, η (Pi.single ⟨i, fun j : ClosedNeighborhood G i => s j.1⟩ 1) =
        -Real.log (τStar.weights s) - 1 := by
      have hev := congrArg (fun f : Module.Dual ℝ (X → ℝ) => f (Pi.single s 1)) hη
      simp only [LinearMap.dualMap_apply, hsingle, map_sum, φ, LinearMap.coe_mk,
        AddHom.coe_mk] at hev
      rw [sum_eq_single s (fun t _ hts => by simp [Pi.single_eq_of_ne hts])
        (fun h => (h (mem_univ s)).elim)] at hev
      simpa only [Pi.single_eq_same, mul_one] using hev
    calc τStar.weights s
        = Real.exp (Real.log (τStar.weights s)) := (Real.exp_log (hτStar_pos s)).symm
      _ = Real.exp ((∑ i : ι, -η (Pi.single ⟨i, fun j => s j.1⟩ 1)) - 1) := by
          rw [sum_neg_distrib, hdual]
          congr 1; ring
      _ = Real.exp (∑ i : ι, -η (Pi.single ⟨i, fun j => s j.1⟩ 1)) / Real.exp 1 :=
          Real.exp_sub _ _
      _ = (∏ i : ι, ψ i (fun j => s j.1)) / Real.exp 1 := by
          rw [Real.exp_sum]
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    refine ⟨σ, fun _ _ => rfl, fun i => isEmptyElim i, 1, fun i => isEmptyElim i, zero_lt_one,
      fun s => ?_⟩
    rw [Convexity.StdSimplex.weights_apply_eq_one, Fintype.prod_empty, div_one]

/-- Special case of `exists_isPositiveLocalMarkovNetwork_of_exists_pos` when `σ` itself has
strictly positive weights everywhere. -/
theorem exists_isPositiveLocalMarkovNetwork_of_pos (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) (hpos : ∀ s, 0 < σ.weights s) :
    ∃ τ : Convexity.StdSimplex ℝ (∀ i, S i),
      LocalNeighborhoodEquiv G τ σ ∧ IsPositiveLocalMarkovNetwork G τ :=
  exists_isPositiveLocalMarkovNetwork_of_exists_pos G σ ⟨σ, fun _ _ => rfl, hpos⟩

/-- **Positive-support Theorem 7.13** ([Kearns2007], §7.4.2, p. 174): for any finite graphical game
`M` and correlated equilibrium `σ` admitting a strictly positive local-neighborhood equivalent
distribution, there exists a strictly positive local Markov network `τ` on `M.graph` that is a
correlated equilibrium of `M.toCostGame` and is both local-neighborhood and expected-payoff
equivalent to `σ`. (The positivity hypothesis is necessary on general graphs by
`exists_ce_not_expectedPayoffEquiv_isLocalMarkovNetwork_cycle4`.) -/
theorem GraphicalGame.exists_isPositiveLocalMarkovNetwork_ce_of_exists_pos [DecidableEq ι]
    (M : GraphicalGame ι S) {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (hce : M.toCostGame.IsCorrelatedEquilibrium σ)
    (hpos : ∃ τ₀ : Convexity.StdSimplex ℝ (∀ i, S i),
      LocalNeighborhoodEquiv M.graph τ₀ σ ∧ ∀ s, 0 < τ₀.weights s) :
    ∃ τ : Convexity.StdSimplex ℝ (∀ i, S i),
      M.toCostGame.IsCorrelatedEquilibrium τ ∧
      M.ExpectedPayoffEquiv τ σ ∧
      LocalNeighborhoodEquiv M.graph τ σ ∧
      IsPositiveLocalMarkovNetwork M.graph τ := by
  obtain ⟨τ, hln, hmk⟩ := exists_isPositiveLocalMarkovNetwork_of_exists_pos M.graph σ hpos
  exact ⟨τ, hln.isCorrelatedEquilibrium_iff.mpr hce, hln.expectedPayoffEquiv, hln, hmk⟩

end MaxEntropy

/-! ### 4. General `ε`-approximate local Markov network closure (zeros allowed) -/

section ApproxClosure

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [∀ i, Finite (S i)]

private noncomputable def uniformDist {X : Type*} [Fintype X] [Nonempty X] :
    Convexity.StdSimplex ℝ X :=
  simplexOfFun (fun _ => (Fintype.card X : ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by
      have hpos : (0 : ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
      rw [sum_const, card_univ, nsmul_eq_mul, mul_inv_cancel₀ hpos.ne'])

private theorem uniformDist_weights_pos {X : Type*} [Fintype X] [Nonempty X] (x : X) :
    0 < (uniformDist (X := X)).weights x := by
  simp only [uniformDist, simplexOfFun_weights]
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

private theorem exists_posMarkov_mixUniform (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    ∃ (τ : Convexity.StdSimplex ℝ (∀ i, S i)),
      IsPositiveLocalMarkovNetwork G τ ∧
      (∀ (i : ι) (u : ∀ j : ClosedNeighborhood G i, S j.1),
        |neighborhoodMarginal G τ i u - neighborhoodMarginal G σ i u| ≤ δ) ∧
      ∃ (uDist : Convexity.StdSimplex ℝ (∀ i, S i)),
        LocalNeighborhoodEquiv G τ
          (Convexity.convexCombPair (1 - δ) δ (by linarith) hδ_pos.le (by ring) σ uDist) := by
  classical
  have := fun i => Fintype.ofFinite (S i)
  have : Nonempty (∀ i, S i) := σ.nonempty
  let σδ : Convexity.StdSimplex ℝ (∀ i, S i) :=
    Convexity.convexCombPair (1 - δ) δ (by linarith) hδ_pos.le (by ring) σ uniformDist
  have hσδ_pos : ∀ s, 0 < σδ.weights s := fun s => by
    simp only [σδ, Convexity.StdSimplex.weights_convexCombPair, Finsupp.coe_add,
      Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : 0 ≤ (1 - δ) * σ.weights s := mul_nonneg (by linarith) (σ.weights_nonneg s)
    have h2 : 0 < δ * uniformDist.weights s := mul_pos hδ_pos (uniformDist_weights_pos s)
    linarith
  obtain ⟨τ, hln, hmk⟩ := exists_isPositiveLocalMarkovNetwork_of_pos G σδ hσδ_pos
  refine ⟨τ, hmk, fun i u => ?_, uniformDist, hln⟩
  rw [hln i u, neighborhoodMarginal_convexCombPair]
  have hrew : (1 - δ) * neighborhoodMarginal G σ i u + δ * neighborhoodMarginal G uniformDist i u -
      neighborhoodMarginal G σ i u =
      δ * (neighborhoodMarginal G uniformDist i u - neighborhoodMarginal G σ i u) := by ring
  rw [hrew, abs_mul, abs_of_pos hδ_pos]
  have hdiff : |neighborhoodMarginal G uniformDist i u - neighborhoodMarginal G σ i u| ≤ 1 := by
    rw [abs_le]
    have h1 := neighborhoodMarginal_nonneg G uniformDist i u
    have h2 := neighborhoodMarginal_le_one G uniformDist i u
    have h3 := neighborhoodMarginal_nonneg G σ i u
    have h4 := neighborhoodMarginal_le_one G σ i u
    constructor <;> linarith
  calc δ * |neighborhoodMarginal G uniformDist i u - neighborhoodMarginal G σ i u|
      ≤ δ * 1 := mul_le_mul_of_nonneg_left hdiff hδ_pos.le
    _ = δ := mul_one δ

/-- **Approximate closure of local Markov networks**: for any finite graph `G`, any joint
distribution `σ` (without any positivity assumption), and any `ε > 0`, there exists a strictly
positive local Markov network `τ` on `G` whose closed-neighborhood marginals approximate those of
`σ` within `ε`. -/
theorem exists_isPositiveLocalMarkovNetwork_neighborhoodMarginal_approx (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : Convexity.StdSimplex ℝ (∀ i, S i),
      IsPositiveLocalMarkovNetwork G τ ∧
      ∀ (i : ι) (u : ∀ j : ClosedNeighborhood G i, S j.1),
        |neighborhoodMarginal G τ i u - neighborhoodMarginal G σ i u| ≤ ε := by
  let δ : ℝ := min (1 / 2) ε
  have hδ_pos : 0 < δ := lt_min (by norm_num) hε
  have hδ_le_one : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  obtain ⟨τ, hmk, hmarg, _, _⟩ := exists_posMarkov_mixUniform G σ hδ_pos hδ_le_one
  exact ⟨τ, hmk, fun i u => (hmarg i u).trans (min_le_right _ _)⟩

/-- **`ε`-approximate Theorem 7.13 for arbitrary correlated equilibria (zeros allowed)**: for every
finite graphical game `M`, every correlated equilibrium `σ` of `M.toCostGame` (without any
positivity hypothesis), and every `ε > 0`, there exists a strictly positive local Markov network
`τ` on `M.graph` that is an `ε`-approximate correlated equilibrium of `M.toCostGame` whose expected
payoffs and local neighborhood marginals are within `ε` of `σ`. -/
theorem GraphicalGame.exists_isPositiveLocalMarkovNetwork_isApproxCorrelatedEquilibrium
    [DecidableEq ι] (M : GraphicalGame ι S) {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (hce : M.toCostGame.IsCorrelatedEquilibrium σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : Convexity.StdSimplex ℝ (∀ i, S i),
      IsPositiveLocalMarkovNetwork M.graph τ ∧
      M.toCostGame.IsApproxCorrelatedEquilibrium (fun _ => ε) τ ∧
      (∀ i : ι, |τ.weights.sum (fun s w => w * M.payoff i s) -
          σ.weights.sum (fun s w => w * M.payoff i s)| ≤ ε) ∧
      (∀ (i : ι) (u : ∀ j : ClosedNeighborhood M.graph i, S j.1),
        |neighborhoodMarginal M.graph τ i u - neighborhoodMarginal M.graph σ i u| ≤ ε) := by
  classical
  have := fun i => Fintype.ofFinite (S i)
  let B : ℝ := 1 + ∑ i : ι, ∑ s : (∀ k, S k), |M.payoff i s|
  have hB_ge_one : 1 ≤ B := by
    dsimp [B]
    have : 0 ≤ ∑ i : ι, ∑ s : (∀ k, S k), |M.payoff i s| :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB_ge_one
  have hpay_le : ∀ (i : ι) (s : ∀ k, S k), |M.payoff i s| ≤ B := fun i s => by
    have h1 : |M.payoff i s| ≤ ∑ t : (∀ k, S k), |M.payoff i t| :=
      single_le_sum (f := fun t => |M.payoff i t|) (fun _ _ => abs_nonneg _) (mem_univ s)
    have h2 : (∑ t : (∀ k, S k), |M.payoff i t|) ≤
        ∑ j : ι, ∑ t : (∀ k, S k), |M.payoff j t| :=
      single_le_sum (f := fun j => ∑ t : (∀ k, S k), |M.payoff j t|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ i)
    dsimp [B]; linarith
  have hexp_le : ∀ (ρ : Convexity.StdSimplex ℝ (∀ k, S k)) (f : (∀ k, S k) → ℝ),
      (∀ s, |f s| ≤ B) → |ρ.weights.sum (fun s w => w * f s)| ≤ B := by
    intro ρ f hf
    rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
    calc |∑ s, ρ.weights s * f s|
        ≤ ∑ s, |ρ.weights s * f s| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, ρ.weights s * B := sum_le_sum fun s _ => by
          rw [abs_mul, abs_of_nonneg (ρ.weights_nonneg s)]
          exact mul_le_mul_of_nonneg_left (hf s) (ρ.weights_nonneg s)
      _ = B := by rw [← sum_mul, ρ.total_of_fintype, one_mul]
  let δ : ℝ := min (1 / 2) (ε / (2 * B))
  have hδ_pos : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ_le_one : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδ_le_div : δ ≤ ε / (2 * B) := min_le_right _ _
  have h2Bδ : 2 * B * δ ≤ ε := by
    calc 2 * B * δ ≤ 2 * B * (ε / (2 * B)) := mul_le_mul_of_nonneg_left hδ_le_div (by positivity)
      _ = ε := mul_div_cancel₀ ε (by positivity)
  obtain ⟨τ, hmk, hmarg, uDist, hln⟩ := exists_posMarkov_mixUniform M.graph σ hδ_pos hδ_le_one
  refine ⟨τ, hmk, ?_, ?_, fun i u => (hmarg i u).trans (by nlinarith)⟩
  · rw [hln.isApproxCorrelatedEquilibrium_iff]
    intro i sw
    rw [CostGame.sum_convexCombPair_weights, CostGame.sum_convexCombPair_weights]
    have hσ_ce := hce i sw
    have h1 : (1 - δ) * σ.weights.sum (fun s w => w * M.toCostGame.cost i s) ≤
        (1 - δ) * σ.weights.sum (fun s w => w * M.toCostGame.cost i (update s i (sw (s i)))) :=
      mul_le_mul_of_nonneg_left hσ_ce (by linarith)
    have hu1 : |uDist.weights.sum (fun s w => w * M.toCostGame.cost i s)| ≤ B :=
      hexp_le uDist _ fun s => by
        simpa [GraphicalGame.toCostGame_cost] using hpay_le i s
    have hu2 : |uDist.weights.sum (fun s w =>
        w * M.toCostGame.cost i (update s i (sw (s i))))| ≤ B :=
      hexp_le uDist _ fun s => by
        simpa [GraphicalGame.toCostGame_cost] using hpay_le i (update s i (sw (s i)))
    have hdiff_u : uDist.weights.sum (fun s w => w * M.toCostGame.cost i s) -
        uDist.weights.sum (fun s w => w * M.toCostGame.cost i (update s i (sw (s i)))) ≤
        2 * B := by
      linarith [(abs_le.mp hu1).2, (abs_le.mp hu2).1]
    have h2 : δ * (uDist.weights.sum (fun s w => w * M.toCostGame.cost i s) -
        uDist.weights.sum (fun s w => w * M.toCostGame.cost i (update s i (sw (s i))))) ≤
        ε := by
      calc δ * _ ≤ δ * (2 * B) := mul_le_mul_of_nonneg_left hdiff_u hδ_pos.le
        _ = 2 * B * δ := by ring
        _ ≤ ε := h2Bδ
    linarith
  · intro i
    rw [hln.expectedPayoffEquiv i, CostGame.sum_convexCombPair_weights]
    have hrew : (1 - δ) * σ.weights.sum (fun s w => w * M.payoff i s) +
        δ * uDist.weights.sum (fun s w => w * M.payoff i s) -
        σ.weights.sum (fun s w => w * M.payoff i s) =
        δ * (uDist.weights.sum (fun s w => w * M.payoff i s) -
          σ.weights.sum (fun s w => w * M.payoff i s)) := by ring
    rw [hrew, abs_mul, abs_of_pos hδ_pos]
    have h1 := hexp_le uDist _ (hpay_le i)
    have h2 := hexp_le σ _ (hpay_le i)
    have hdiff : |uDist.weights.sum (fun s w => w * M.payoff i s) -
        σ.weights.sum (fun s w => w * M.payoff i s)| ≤ 2 * B :=
      (abs_sub _ _).trans (by linarith)
    calc δ * _ ≤ δ * (2 * B) := mul_le_mul_of_nonneg_left hdiff hδ_pos.le
      _ = 2 * B * δ := by ring
      _ ≤ ε := h2Bδ

end ApproxClosure

/-! ### 5. Local marginal consistency, junction-tree lifting, and Theorem 7.14 -/

section TreeLocalCE

variable {ι : Type*} {S : ι → Type*}

/-- Marginal of a local neighborhood family `q` at vertex `i` on an arbitrary subset
`T ⊆ ClosedNeighborhood G i`. -/
noncomputable def restrictMarginal [Fintype ι] [∀ i, Fintype (S i)] (G : SimpleGraph ι)
    (q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) (i : ι) (T : Set ι)
    (hT : ∀ k ∈ T, k = i ∨ G.Adj i k) (y : ∀ k : T, S k.1) : ℝ :=
  open Classical in
  ∑ u : (∀ j : ClosedNeighborhood G i, S j.1),
    if (fun k : T => u ⟨k.1, hT k.1 k.2⟩) = y then q i u else 0

theorem restrictMarginal_def [Fintype ι] [∀ i, Fintype (S i)] (G : SimpleGraph ι)
    [DecidableRel G.Adj] [DecidableEq ι]
    (q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) (i : ι) (T : Set ι)
    (hT : ∀ k ∈ T, k = i ∨ G.Adj i k) [DecidableEq (∀ k : T, S k.1)]
    (y : ∀ k : T, S k.1) :
    restrictMarginal G q i T hT y =
      ∑ u : (∀ j : ClosedNeighborhood G i, S j.1),
        if (fun k : T => u ⟨k.1, hT k.1 k.2⟩) = y then q i u else 0 := by
  unfold restrictMarginal
  convert rfl

/-- Edge marginal induced by `q i` on `{i, j}` for an edge `G.Adj i j`. -/
noncomputable def edgeMarginal [Fintype ι] [∀ i, Fintype (S i)] (G : SimpleGraph ι)
    (q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) (i j : ι) (hadj : G.Adj i j)
    (a : S i) (b : S j) : ℝ :=
  open Classical in
  ∑ u : (∀ k : ClosedNeighborhood G i, S k.1),
    if u ⟨i, Or.inl rfl⟩ = a ∧ u ⟨j, Or.inr hadj⟩ = b then q i u else 0

theorem edgeMarginal_def [Fintype ι] [∀ i, Fintype (S i)] (G : SimpleGraph ι)
    [DecidableRel G.Adj] [DecidableEq ι] (q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ)
    (i j : ι) (hadj : G.Adj i j) [DecidableEq (S i)] [DecidableEq (S j)] (a : S i) (b : S j) :
    edgeMarginal G q i j hadj a b =
      ∑ u : (∀ k : ClosedNeighborhood G i, S k.1),
        if u ⟨i, Or.inl rfl⟩ = a ∧ u ⟨j, Or.inr hadj⟩ = b then q i u else 0 := by
  unfold edgeMarginal
  convert rfl

/-- **Local distribution constraints** ([Kearns2007], §7.4.3, constraint (ii), p. 175): each `q i`
is nonnegative and sums to `1` over `ClosedNeighborhood G i`. -/
@[expose] def IsLocalDistribution [Fintype ι] [∀ i, Fintype (S i)] (G : SimpleGraph ι)
    (q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) : Prop :=
  ∀ i : ι, (∀ u, 0 ≤ q i u) ∧ (open Classical in ∑ u, q i u = 1)

/-- **Edge consistency**: for every edge `G.Adj i j`, the `{i, j}`-marginals of `q i` and `q j`
agree. On trees, this is equivalent to full intersection consistency (`IsIntersectionConsistent`).
-/
@[expose] def IsEdgeConsistent [Fintype ι] [∀ i, Fintype (S i)] (G : SimpleGraph ι)
    (q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) : Prop :=
  ∀ (i j : ι) (hadj : G.Adj i j) (a : S i) (b : S j),
    edgeMarginal G q i j hadj a b = edgeMarginal G q j i hadj.symm b a

/-- **Intersection consistency constraints** ([Kearns2007], §7.4.3, constraint (iii), p. 175):
for all players `i` and `j`, `q i` and `q j` induce the same marginal distribution on
`N_G(i) ∩ N_G(j)`. -/
@[expose] def IsIntersectionConsistent [Fintype ι] [∀ i, Fintype (S i)] (G : SimpleGraph ι)
    (q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) : Prop :=
  ∀ (i j : ι) (y : ∀ k : ({k : ι | (k = i ∨ G.Adj i k) ∧ (k = j ∨ G.Adj j k)} : Set ι), S k.1),
    restrictMarginal G q i {k : ι | (k = i ∨ G.Adj i k) ∧ (k = j ∨ G.Adj j k)} (fun _ h => h.1) y =
      restrictMarginal G q j {k : ι | (k = i ∨ G.Adj i k) ∧ (k = j ∨ G.Adj j k)}
        (fun _ h => h.2) y

/-- **Local correlated-equilibrium incentive constraints** ([Kearns2007], §7.4.3, constraint (i),
p. 175): for every player `i`, recommended action `a`, and deviation `b`, switching from `a` to `b`
does not increase player `i`'s local expected payoff under `q i`. -/
@[expose] def GraphicalGame.SatisfiesLocalCE [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]
    (M : GraphicalGame ι S)
    (q : ∀ i : ι, (∀ j : ClosedNeighborhood M.graph i, S j.1) → ℝ) : Prop :=
  open Classical in
  ∀ (i : ι) (a b : S i),
    (∑ u : (∀ j : ClosedNeighborhood M.graph i, S j.1),
      if u ⟨i, Or.inl rfl⟩ = a then
        q i u * M.localPayoff i (update u ⟨i, Or.inl rfl⟩ b)
      else 0) ≤
    (∑ u : (∀ j : ClosedNeighborhood M.graph i, S j.1),
      if u ⟨i, Or.inl rfl⟩ = a then q i u * M.localPayoff i u else 0)

/-- **Kearns's local correlated-equilibrium linear program** ([Kearns2007], §7.4.3, constraints
(i)–(iii), p. 175): a family of local neighborhood distributions satisfying local CE incentive
constraints, simplex constraints, and pairwise neighborhood-intersection consistency. -/
@[expose] def GraphicalGame.IsLocalCorrelatedEquilibrium [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (S i)] (M : GraphicalGame ι S)
    (q : ∀ i : ι, (∀ j : ClosedNeighborhood M.graph i, S j.1) → ℝ) : Prop :=
  M.SatisfiesLocalCE q ∧ IsLocalDistribution M.graph q ∧ IsIntersectionConsistent M.graph q

/-! #### Private junction-tree lifting construction on finite trees -/

section TreeLiftPrivate

private def override {P : ι → Prop} [DecidablePred P]
    (s₀ : ∀ i, S i) (x : ∀ z : {z : ι // P z}, S z.1) (i : ι) : S i :=
  if hi : P i then x ⟨i, hi⟩ else s₀ i

private theorem override_of_pos {P : ι → Prop} [DecidablePred P]
    (s₀ : ∀ i, S i) (x : ∀ z : {z : ι // P z}, S z.1) {i : ι} (hi : P i) :
    override s₀ x i = x ⟨i, hi⟩ :=
  dite_eq_left hi

private theorem override_of_neg {P : ι → Prop} [DecidablePred P]
    (s₀ : ∀ i, S i) (x : ∀ z : {z : ι // P z}, S z.1) {i : ι} (hi : ¬ P i) :
    override s₀ x i = s₀ i :=
  dite_eq_right hi

private noncomputable def piEquivDisjointUnion {κ : Type*} {P : ι → Prop} {R : κ → ι → Prop}
    (hsub : ∀ k z, R k z → P z) (hcov : ∀ z, P z → ∃ k, R k z)
    (hdisj : ∀ k₁ k₂ z, R k₁ z → R k₂ z → k₁ = k₂) :
    (∀ z : {z : ι // P z}, S z.1) ≃ (∀ k : κ, ∀ z : {z : ι // R k z}, S z.1) where
  toFun x k z := x ⟨z.1, hsub k z.1 z.2⟩
  invFun y z :=
    let hex := hcov z.1 z.2
    y (Classical.choose hex) ⟨z.1, Classical.choose_spec hex⟩
  left_inv x := by
    ext ⟨z, hz⟩
    rfl
  right_inv y := by
    ext k ⟨z, hkz⟩
    dsimp only
    have hspec := Classical.choose_spec (hcov z (hsub k z hkz))
    have hkeq : Classical.choose (hcov z (hsub k z hkz)) = k := hdisj _ k z hspec hkz
    have key : ∀ (k' : κ) (h' : R k' z), k' = k → y k' ⟨z, h'⟩ = y k ⟨z, hkz⟩ := by
      rintro _ h' rfl
      rfl
    exact key _ hspec hkeq

private noncomputable def piEquivSplit {P Q R : ι → Prop} [DecidablePred Q]
    (hsubQ : ∀ z, Q z → P z) (hsubR : ∀ z, R z → P z)
    (hcov : ∀ z, P z → Q z ∨ R z) (hdisj : ∀ z, Q z → R z → False) :
    (∀ z : {z : ι // P z}, S z.1) ≃
      (∀ z : {z : ι // Q z}, S z.1) × (∀ z : {z : ι // R z}, S z.1) where
  toFun x := (fun z => x ⟨z.1, hsubQ z.1 z.2⟩, fun z => x ⟨z.1, hsubR z.1 z.2⟩)
  invFun y z :=
    if hq : Q z.1 then y.1 ⟨z.1, hq⟩
    else y.2 ⟨z.1, (hcov z.1 z.2).resolve_left hq⟩
  left_inv x := by
    ext ⟨z, hz⟩
    dsimp only
    split_ifs <;> rfl
  right_inv y := by
    ext ⟨z, hz⟩
    · simp [hz]
    · have hnq : ¬ Q z := fun hq => hdisj z hq hz
      simp [hnq]

private theorem pairwiseDisjoint_filter_treeSide [Fintype ι] {G : SimpleGraph ι} (hT : G.IsTree)
    (r v : ι) [∀ c : UpstreamNeighbors hT r v, DecidablePred (· ∈ hT.treeSide c.1 v)] :
    Set.PairwiseDisjoint (Set.univ : Set (UpstreamNeighbors hT r v))
      (fun c => univ.filter (fun z => z ∈ hT.treeSide c.1 v)) := by
  intro c₁ _ c₂ _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro z hz₁ hz₂
  exact hne (upstream_unique_of_mem_treeSide (mem_filter.mp hz₁).2 (mem_filter.mp hz₂).2)

private noncomputable def nonRootEdgeEquiv {G : SimpleGraph ι} (hT : G.IsTree) (r : ι) :
    {v : ι // v ≠ r} ≃ G.edgeSet :=
  Equiv.ofBijective
    (fun v => ⟨s(v.1, hT.parent r v.1), (SimpleGraph.mem_edgeSet G).mpr (hT.adj_parent r v.2)⟩)
    ⟨by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ heq
      have hsym : s(u, hT.parent r u) = s(v, hT.parent r v) := congrArg Subtype.val heq
      rcases Sym2.eq_iff.mp hsym with ⟨huv, _⟩ | ⟨hupv, hpuv⟩
      · exact Subtype.ext huv
      · have h1 := hT.length_pathTo_parent r hu
        have h2 := hT.length_pathTo_parent r hv
        rw [hpuv] at h1
        rw [hupv] at h1
        omega,
    by
      rintro ⟨e, he⟩
      induction e using Sym2.ind with | _ x y =>
      have hadj : G.Adj x y := (SimpleGraph.mem_edgeSet G).mp he
      rcases (hT.adj_iff_parent r).mp hadj with ⟨hx, rfl⟩ | ⟨hy, rfl⟩
      · exact ⟨⟨x, hx⟩, rfl⟩
      · exact ⟨⟨y, hy⟩, Subtype.ext Sym2.eq_swap⟩⟩

variable [Fintype ι] [∀ i, Fintype (S i)]

/-- Rooted tree potential `ψ_v` for junction-tree lifting: `q r` at the root `r`, and
`q v / edgeMarginal v (parent r v)` at non-root vertices `v ≠ r` (with `0 / 0 = 0`). -/
private noncomputable def treePotential {G : SimpleGraph ι} (hT : G.IsTree)
    (q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) (r v : ι)
    (u : ∀ j : ClosedNeighborhood G v, S j.1) : ℝ := by
  classical
  exact if hv : v = r then q v u
  else
    q v u /
      edgeMarginal G q v (hT.parent r v) (hT.adj_parent r hv)
        (u ⟨v, Or.inl rfl⟩) (u ⟨hT.parent r v, Or.inr (hT.adj_parent r hv)⟩)

private theorem treePotential_nonneg {G : SimpleGraph ι} (hT : G.IsTree)
    {q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ}
    (hnn : ∀ i u, 0 ≤ q i u) (r v : ι) (u : ∀ j : ClosedNeighborhood G v, S j.1) :
    0 ≤ treePotential hT q r v u := by
  classical
  unfold treePotential
  split_ifs with hv
  · exact hnn v u
  · refine div_nonneg (hnn v u) ?_
    rw [edgeMarginal_def]
    exact sum_nonneg fun w _ => by split_ifs <;> [exact hnn v w; exact le_rfl]

private noncomputable def treeWeight {G : SimpleGraph ι} (hT : G.IsTree)
    (q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ) (r : ι) (s : ∀ i, S i) : ℝ :=
  ∏ v : ι, treePotential hT q r v (fun j => s j.1)

private theorem treeWeight_nonneg {G : SimpleGraph ι} (hT : G.IsTree)
    {q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ}
    (hnn : ∀ i u, 0 ≤ q i u) (r : ι) (s : ∀ i, S i) :
    0 ≤ treeWeight hT q r s :=
  prod_nonneg fun v _ => treePotential_nonneg hT hnn r v _

/-- Key re-rooting invariance: under edge consistency, `treeWeight hT q r s` is completely
independent of the chosen root `r` (even when some edge marginals vanish, via `0 / 0 = 0`). -/
private theorem treeWeight_root_indep {G : SimpleGraph ι} (hT : G.IsTree)
    {q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ}
    (hedge : IsEdgeConsistent G q) (r₁ r₂ : ι) (s : ∀ i, S i) :
    treeWeight hT q r₁ s = treeWeight hT q r₂ s := by
  classical
  have hdiv (r : ι) :
      treeWeight hT q r s =
        (∏ v : ι, q v (fun j => s j.1)) /
          ∏ v : {v : ι // v ≠ r},
            edgeMarginal G q v.1 (hT.parent r v.1) (hT.adj_parent r v.2)
              (s v.1) (s (hT.parent r v.1)) := by
    have hpot (v : ι) :
        treePotential hT q r v (fun j => s j.1) =
          q v (fun j => s j.1) /
            (if hv : v = r then (1 : ℝ)
              else edgeMarginal G q v (hT.parent r v) (hT.adj_parent r hv)
                (s v) (s (hT.parent r v))) := by
      unfold treePotential
      split_ifs with hv
      · rw [div_one]
      · rfl
    rw [treeWeight, prod_congr rfl fun v _ => hpot v, prod_div_distrib]
    congr 1
    rw [← mul_prod_erase univ _ (mem_univ r), dite_eq_left rfl, one_mul]
    have herase : univ.erase r = univ.filter (fun v : ι => v ≠ r) := ext fun _ => by simp
    rw [herase, prod_subtype (univ.filter fun v : ι => v ≠ r) (p := fun v => v ≠ r)
      (fun _ => mem_filter_univ _)]
    refine prod_congr rfl fun ⟨v, hv⟩ _ => by simp [hv]
  rw [hdiv r₁, hdiv r₂]
  congr 1
  let e : {v : ι // v ≠ r₁} ≃ {v : ι // v ≠ r₂} :=
    (nonRootEdgeEquiv hT r₁).trans (nonRootEdgeEquiv hT r₂).symm
  refine Fintype.prod_equiv e _ _ fun v => ?_
  have hedge_eq : s(v.1, hT.parent r₁ v.1) = s((e v).1, hT.parent r₂ (e v).1) := by
    have h1 : nonRootEdgeEquiv hT r₂ (e v) = nonRootEdgeEquiv hT r₁ v :=
      Equiv.apply_symm_apply _ _
    exact (congrArg Subtype.val h1).symm
  have key₁ : ∀ (x₁ y₁ x₂ y₂ : ι) (h₁ : G.Adj x₁ y₁) (h₂ : G.Adj x₂ y₂),
      x₁ = x₂ → y₁ = y₂ →
        edgeMarginal G q x₁ y₁ h₁ (s x₁) (s y₁) = edgeMarginal G q x₂ y₂ h₂ (s x₂) (s y₂) := by
    rintro _ _ _ _ _ _ rfl rfl
    rfl
  have key₂ : ∀ (x₁ y₁ x₂ y₂ : ι) (h₁ : G.Adj x₁ y₁) (h₂ : G.Adj x₂ y₂),
      x₁ = y₂ → y₁ = x₂ →
        edgeMarginal G q x₁ y₁ h₁ (s x₁) (s y₁) = edgeMarginal G q x₂ y₂ h₂ (s x₂) (s y₂) := by
    rintro _ _ _ _ h₁ _ rfl rfl
    exact hedge _ _ h₁ _ _
  rcases Sym2.eq_iff.mp hedge_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key₁ _ _ _ _ _ _ h1 h2
  · exact key₂ _ _ _ _ _ _ h1 h2

private theorem q_eq_zero_of_edgeMarginal_eq_zero {G : SimpleGraph ι}
    {q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ}
    (hnn : ∀ i u, 0 ≤ q i u) {i j : ι} (hadj : G.Adj i j)
    {u : ∀ k : ClosedNeighborhood G i, S k.1}
    (h0 : edgeMarginal G q i j hadj (u ⟨i, Or.inl rfl⟩) (u ⟨j, Or.inr hadj⟩) = 0) :
    q i u = 0 := by
  classical
  rw [edgeMarginal_def] at h0
  have hall := (sum_eq_zero_iff_of_nonneg fun w _ => by
    split_ifs <;> [exact hnn i w; exact le_rfl]).mp h0
  have hu := hall u (mem_univ u)
  simpa using hu

/-- **Exact subtree marginalization lemma** (handles zero edge marginals via `0 / 0 = 0`):
summing the upstream subtree product `∏ z ∈ treeSide v (parent r v), treePotential z` over all
actions strictly above `v` yields `1` if the edge marginal on `(v, parent r v)` is nonzero and `0`
otherwise. -/
private theorem sum_subtree_treePotential {G : SimpleGraph ι} (hT : G.IsTree) (r : ι)
    {q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ}
    (hnn : ∀ i u, 0 ≤ q i u) (hedge : IsEdgeConsistent G q)
    {v : ι} (hv : v ≠ r) (s₀ : ∀ i, S i) :
    by
      classical
      exact ∑ x : (∀ z : {z : ι // z ∈ hT.treeSide v (hT.parent r v) ∧ z ≠ v}, S z.1),
        ∏ z ∈ univ.filter (fun z => z ∈ hT.treeSide v (hT.parent r v)),
          treePotential hT q r z (fun j => override s₀ x j.1) =
      if edgeMarginal G q v (hT.parent r v) (hT.adj_parent r hv) (s₀ v) (s₀ (hT.parent r v)) = 0
      then 0 else 1 := by
  classical
  let rank (v : ι) := Fintype.card ι - (hT.pathTo r v).length
  induction v using (_root_.measure rank).wf.induction generalizing s₀ with
  | h v ih =>
    have hadj_vp : G.Adj v (hT.parent r v) := hT.adj_parent r hv
    have hlt_up : ∀ c : UpstreamNeighbors hT r v, rank c.1 < rank v :=
      fun c => c.card_sub_length_pathTo_lt
    have hadj_cv : ∀ c : UpstreamNeighbors hT r v, G.Adj c.1 v := fun c => by
      simpa [c.2.2] using hT.adj_parent r c.2.1
    have hsub_up : ∀ c : UpstreamNeighbors hT r v,
        hT.treeSide c.1 v ⊆ hT.treeSide v (hT.parent r v) := fun c => c.treeSide_subset hv
    -- Step A: Split `treeSide v (parent r v) \ {v}` into `UpstreamNeighbors hT r v` and
    -- `⋃ c, (treeSide c v \ {c})`.
    let Pv : ι → Prop := fun z => z ∈ hT.treeSide v (hT.parent r v) ∧ z ≠ v
    let Qv : ι → Prop := fun z => z ≠ r ∧ hT.parent r z = v
    let Rv : ι → Prop := fun z => ∃ c : UpstreamNeighbors hT r v, z ∈ hT.treeSide c.1 v ∧ z ≠ c.1
    have hsubQ : ∀ z, Qv z → Pv z := fun z hz => by
      let hc : UpstreamNeighbors hT r v := ⟨z, hz⟩
      exact ⟨hsub_up hc (hT.self_mem_treeSide_of_adj (hadj_cv hc)), (hadj_cv hc).ne⟩
    have hsubR : ∀ z, Rv z → Pv z := fun z ⟨c, hzc, _⟩ =>
      ⟨hsub_up c hzc, fun hzv => hT.not_mem_treeSide_other (hadj_cv c) (hzv ▸ hzc)⟩
    have hcovQR : ∀ z, Pv z → Qv z ∨ Rv z := fun z ⟨hz, hzv⟩ => by
      rw [hT.treeSide_eq_insert_biUnion hadj_vp] at hz
      obtain ⟨c₀, hc₀, hzc⟩ := Set.mem_iUnion₂.mp (hz.resolve_left hzv)
      let c : UpstreamNeighbors hT r v := ⟨c₀, (upstream_neighbor_iff hT r hv).mp hc₀⟩
      by_cases hzc_eq : z = c.1
      · exact Or.inl (hzc_eq ▸ c.2)
      · exact Or.inr ⟨c, hzc, hzc_eq⟩
    have hdisjQR : ∀ z, Qv z → Rv z → False := fun z hz ⟨c, hzc, hzne⟩ => by
      let cz : UpstreamNeighbors hT r v := ⟨z, hz⟩
      have heq := upstream_unique_of_mem_treeSide (hT.self_mem_treeSide_of_adj (hadj_cv cz)) hzc
      exact hzne (congrArg Subtype.val heq)
    let e1 := piEquivSplit (S := S) hsubQ hsubR hcovQR hdisjQR
    let e2 := piEquivDisjointUnion (S := S)
      (P := Rv) (R := fun (c : UpstreamNeighbors hT r v) z => z ∈ hT.treeSide c.1 v ∧ z ≠ c.1)
      (fun c z hz => ⟨c, hz⟩) (fun z hz => hz)
      (fun c₁ c₂ z h1 h2 => upstream_unique_of_mem_treeSide h1.1 h2.1)
    let eAll : (∀ z : {z : ι // Pv z}, S z.1) ≃
        (∀ c : UpstreamNeighbors hT r v, S c.1) ×
        (∀ c : UpstreamNeighbors hT r v,
          ∀ z : {z : ι // z ∈ hT.treeSide c.1 v ∧ z ≠ c.1}, S z.1) :=
      e1.trans (Equiv.prodCongr (Equiv.refl _) e2)
    -- Step B: Rewrite the sum over `x` via `eAll.symm`, separating `v`'s factor from subtrees.
    let sMid (a : ∀ c : UpstreamNeighbors hT r v, S c.1) : ∀ i, S i :=
      override s₀ (P := Qv) a
    have hfactor : ∀ (a : ∀ c : UpstreamNeighbors hT r v, S c.1)
        (y : ∀ c : UpstreamNeighbors hT r v,
          ∀ z : {z : ι // z ∈ hT.treeSide c.1 v ∧ z ≠ c.1}, S z.1),
        (∏ z ∈ univ.filter (fun z => z ∈ hT.treeSide v (hT.parent r v)),
            treePotential hT q r z (fun j => override s₀ (eAll.symm (a, y)) j.1)) =
        treePotential hT q r v (fun j => sMid a j.1) *
          ∏ c : UpstreamNeighbors hT r v,
            ∏ z ∈ univ.filter (fun z => z ∈ hT.treeSide c.1 v),
              treePotential hT q r z (fun j => override (sMid a) (y c) j.1) := by
      intro a y
      -- Split the Finset `treeSide v (parent r v)` into `{v}` and the disjoint `treeSide c v`.
      have hv_mem : v ∈ univ.filter (fun z => z ∈ hT.treeSide v (hT.parent r v)) :=
        mem_filter.mpr ⟨mem_univ v, hT.self_mem_treeSide_of_adj hadj_vp⟩
      rw [← mul_prod_erase _ _ hv_mem]
      have herase_eq : (univ.filter (fun z => z ∈ hT.treeSide v (hT.parent r v))).erase v =
          univ.biUnion fun c : UpstreamNeighbors hT r v =>
            univ.filter (fun z => z ∈ hT.treeSide c.1 v) := by
        ext z
        simp only [mem_erase, mem_filter, mem_univ, true_and, mem_biUnion]
        constructor
        · rintro ⟨hzv, hzt⟩
          rw [hT.treeSide_eq_insert_biUnion hadj_vp] at hzt
          obtain ⟨c₀, hc₀, hzc⟩ := Set.mem_iUnion₂.mp (hzt.resolve_left hzv)
          exact ⟨⟨c₀, (upstream_neighbor_iff hT r hv).mp hc₀⟩, hzc⟩
        · rintro ⟨c, hzc⟩
          exact ⟨fun hzv => hT.not_mem_treeSide_other (hadj_cv c) (hzv ▸ hzc), hsub_up c hzc⟩
      rw [herase_eq, prod_biUnion (by simpa only [coe_univ] using
        pairwiseDisjoint_filter_treeSide hT r v)]
      congr 1
      · -- At `v`, every `j ∈ ClosedNeighborhood G v` agrees under `eAll.symm (a, y)` and `sMid a`.
        congr 1
        ext ⟨j, hj⟩
        dsimp only [sMid]
        rcases hj with rfl | hadj_vj
        · have hnv : ¬ Pv j := fun h => h.2 rfl
          have hnq : ¬ Qv j := fun h => by
            have := hT.length_pathTo_parent r h.1
            rw [h.2] at this; omega
          rw [override_of_neg _ _ hnv, override_of_neg _ _ hnq]
        · by_cases hjp : j = hT.parent r v
          · subst hjp
            have hnp : ¬ Pv (hT.parent r v) := fun h =>
              hT.not_mem_treeSide_other hadj_vp h.1
            have hnq : ¬ Qv (hT.parent r v) := fun h =>
              hT.not_mem_treeSide_other hadj_vp (hsubQ _ h).1
            rw [override_of_neg _ _ hnp, override_of_neg _ _ hnq]
          · have hqj : Qv j := (upstream_neighbor_iff hT r hv).mp ⟨hadj_vj, hjp⟩
            have hpj : Pv j := hsubQ j hqj
            rw [override_of_pos _ _ hpj, override_of_pos _ _ hqj]
            simp only [eAll, e1, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.refl_symm,
              Equiv.prodCongr_apply, Prod.map_apply, piEquivSplit,
              Equiv.coe_fn_symm_mk, hqj, ↓reduceDIte]
            rfl
      · -- Inside each subtree `treeSide c v`, every `j ∈ ClosedNeighborhood G z` agrees.
        refine prod_congr rfl fun c _ => prod_congr rfl fun z hz => ?_
        have hzc : z ∈ hT.treeSide c.1 v := (mem_filter.mp hz).2
        congr 1
        ext ⟨j, hj⟩
        dsimp only
        by_cases hjc : j ∈ hT.treeSide c.1 v
        · by_cases hj_eq : j = c.1
          · subst hj_eq
            have hqj : Qv c.1 := c.2
            have hpj : Pv c.1 := hsubQ c.1 hqj
            have hnr : ¬ (c.1 ∈ hT.treeSide c.1 v ∧ c.1 ≠ c.1) := fun h => h.2 rfl
            rw [override_of_pos _ _ hpj]
            simp only [override, hnr, ↓reduceDIte, sMid, hqj]
            simp only [eAll, e1, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.refl_symm,
              Equiv.prodCongr_apply, Prod.map_apply, piEquivSplit,
              Equiv.coe_fn_symm_mk, hqj, ↓reduceDIte]
            rfl
          · have hrc : Rv j := ⟨c, hjc, hj_eq⟩
            have hpj : Pv j := hsubR j hrc
            have hnq : ¬ Qv j := fun hq => hdisjQR j hq hrc
            rw [override_of_pos _ _ hpj, override_of_pos _ _ ⟨hjc, hj_eq⟩]
            simp only [eAll, e1, e2, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
              Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply, piEquivSplit,
              hnq, ↓reduceDIte, piEquivDisjointUnion, Equiv.coe_fn_symm_mk]
            have hspec := Classical.choose_spec hrc
            have hkeq : Classical.choose hrc = c :=
              upstream_unique_of_mem_treeSide hspec.1 hjc
            have key : ∀ (c' : UpstreamNeighbors hT r v)
                (h' : j ∈ hT.treeSide c'.1 v ∧ j ≠ c'.1),
                c' = c → y c' ⟨j, h'⟩ = y c ⟨j, ⟨hjc, hj_eq⟩⟩ := by
              rintro _ _ rfl
              rfl
            exact key _ hspec hkeq
        · -- `j ∉ treeSide c v` while `z ∈ treeSide c v` and `j ∈ N_G(z)` forces `j = v`.
          have hj_eq_v : j = v := by
            rcases hj with rfl | hadj_zj
            · exact (hjc hzc).elim
            · exact (hT.eq_of_mem_treeSide_of_adj_notMem (hadj_cv c) hzc hjc hadj_zj).2
          subst j
          have hnv : ¬ Pv v := fun h => h.2 rfl
          have hnc : ¬ (v ∈ hT.treeSide c.1 v ∧ v ≠ c.1) := fun h =>
            hT.not_mem_treeSide_other (hadj_cv c) h.1
          have hnq : ¬ Qv v := fun h => by
            have := hT.length_pathTo_parent r h.1
            rw [h.2] at this; omega
          simp only [override, hnv, hnc, sMid, hnq, ↓reduceDIte]
    -- Step C: Apply `Fintype.sum_equiv eAll.symm`, `Fintype.prod_sum`, and the IH on every `c`.
    rw [← Fintype.sum_equiv eAll.symm _ _ (fun _ => rfl), Fintype.sum_prod_type]
    have hinner : ∀ a : ∀ c : UpstreamNeighbors hT r v, S c.1,
        (∑ y : (∀ c : UpstreamNeighbors hT r v,
            ∀ z : {z : ι // z ∈ hT.treeSide c.1 v ∧ z ≠ c.1}, S z.1),
          ∏ z ∈ univ.filter (fun z => z ∈ hT.treeSide v (hT.parent r v)),
            treePotential hT q r z (fun j => override s₀ (eAll.symm (a, y)) j.1)) =
        treePotential hT q r v (fun j => sMid a j.1) := by
      intro a
      simp_rw [hfactor a, ← mul_sum]
      rw [← Fintype.prod_sum (fun (c : UpstreamNeighbors hT r v)
        (x : ∀ z : {z : ι // z ∈ hT.treeSide c.1 v ∧ z ≠ c.1}, S z.1) =>
        ∏ z ∈ univ.filter (fun z => z ∈ hT.treeSide c.1 v),
          treePotential hT q r z (fun j => override (sMid a) x j.1))]
      have hih_c : ∀ c : UpstreamNeighbors hT r v,
          (∑ x : (∀ z : {z : ι // z ∈ hT.treeSide c.1 v ∧ z ≠ c.1}, S z.1),
            ∏ z ∈ univ.filter (fun z => z ∈ hT.treeSide c.1 v),
              treePotential hT q r z (fun j => override (sMid a) x j.1)) =
          if edgeMarginal G q c.1 v (hadj_cv c) (a c) (s₀ v) = 0 then 0 else 1 := by
        rintro ⟨c, hc_ne, rfl⟩
        have hstep := ih c (hlt_up ⟨c, hc_ne, rfl⟩) hc_ne (sMid a)
        have hsmid_c : sMid a c = a ⟨c, hc_ne, rfl⟩ := by
          exact override_of_pos s₀ (P := Qv) a ⟨hc_ne, rfl⟩
        have hsmid_p : sMid a (hT.parent r c) = s₀ (hT.parent r c) := by
          refine override_of_neg s₀ (P := Qv) a fun h => ?_
          have := hT.length_pathTo_parent r h.1
          rw [h.2] at this; omega
        simpa only [hsmid_c, hsmid_p] using hstep
      simp_rw [hih_c]
      by_cases hex : ∃ c : UpstreamNeighbors hT r v,
          edgeMarginal G q c.1 v (hadj_cv c) (a c) (s₀ v) = 0
      · obtain ⟨c, hc0⟩ := hex
        have hprod0 : (∏ c' : UpstreamNeighbors hT r v,
            if edgeMarginal G q c'.1 v (hadj_cv c') (a c') (s₀ v) = 0 then (0 : ℝ) else 1) = 0 :=
          prod_eq_zero (mem_univ c) (by simp [hc0])
        have hvc0 : edgeMarginal G q v c.1 (hadj_cv c).symm (s₀ v) (a c) = 0 := by
          rwa [hedge v c.1 (hadj_cv c).symm (s₀ v) (a c)]
        have hsmid_v : sMid a v = s₀ v := override_of_neg s₀ (P := Qv) a fun h => by
          have := hT.length_pathTo_parent r h.1; rw [h.2] at this; omega
        have hsmid_c : sMid a c.1 = a c := override_of_pos s₀ (P := Qv) a c.2
        have hqv0 : q v (fun j => sMid a j.1) = 0 :=
          q_eq_zero_of_edgeMarginal_eq_zero hnn (hadj_cv c).symm
            (by simpa [hsmid_v, hsmid_c] using hvc0)
        have hpot0 : treePotential hT q r v (fun j => sMid a j.1) = 0 := by
          unfold treePotential
          split_ifs
          · exact hqv0
          · rw [hqv0, zero_div]
        rw [hprod0, hpot0, mul_zero]
      · push Not at hex
        have hprod1 : (∏ c' : UpstreamNeighbors hT r v,
            if edgeMarginal G q c'.1 v (hadj_cv c') (a c') (s₀ v) = 0 then (0 : ℝ) else 1) = 1 :=
          prod_eq_one fun c' _ => ite_eq_right (hex c')
        rw [hprod1, mul_one]
    simp_rw [hinner]
    -- Step D: Sum `treePotential v (sMid a)` over `a : ∀ c : UpstreamNeighbors hT r v, S c.1`.
    have hsmid_v (a) : sMid a v = s₀ v := override_of_neg s₀ (P := Qv) a fun h => by
      have := hT.length_pathTo_parent r h.1; rw [h.2] at this; omega
    have hsmid_p (a) : sMid a (hT.parent r v) = s₀ (hT.parent r v) :=
      override_of_neg s₀ (P := Qv) a fun h =>
        hT.not_mem_treeSide_other hadj_vp (hsubQ _ h).1
    have hpot_eq (a) : treePotential hT q r v (fun j => sMid a j.1) =
        q v (fun j => sMid a j.1) /
          edgeMarginal G q v (hT.parent r v) hadj_vp (s₀ v) (s₀ (hT.parent r v)) := by
      unfold treePotential
      simp only [hv, ↓reduceDIte, hsmid_v, hsmid_p]
    simp_rw [hpot_eq, div_eq_mul_inv, ← sum_mul, ← div_eq_mul_inv]
    -- Biject `∀ c : UpstreamNeighbors hT r v, S c.1` with neighborhood settings fixing `v` and `p`.
    let eN : (∀ c : UpstreamNeighbors hT r v, S c.1) ≃
        {u : ∀ j : ClosedNeighborhood G v, S j.1 //
          u ⟨v, Or.inl rfl⟩ = s₀ v ∧ u ⟨hT.parent r v, Or.inr hadj_vp⟩ = s₀ (hT.parent r v)} :=
      { toFun := fun a => ⟨fun j => sMid a j.1, hsmid_v a, hsmid_p a⟩
        invFun := fun u c => u.1 ⟨c.1, Or.inr (hadj_cv c).symm⟩
        left_inv := fun a => by
          ext c
          exact override_of_pos s₀ (P := Qv) a c.2
        right_inv := fun ⟨u, huv, hup⟩ => by
          ext ⟨j, hj⟩
          dsimp only
          rcases hj with rfl | hadj_vj
          · exact (hsmid_v _).trans huv.symm
          · by_cases hjp : j = hT.parent r v
            · subst hjp
              exact (hsmid_p _).trans hup.symm
            · have hqj : Qv j := (upstream_neighbor_iff hT r hv).mp ⟨hadj_vj, hjp⟩
              exact override_of_pos s₀ (P := Qv) _ hqj }
    have hsum_q : (∑ a : ∀ c : UpstreamNeighbors hT r v, S c.1, q v (fun j => sMid a j.1)) =
        edgeMarginal G q v (hT.parent r v) hadj_vp (s₀ v) (s₀ (hT.parent r v)) := by
      rw [edgeMarginal_def, ← sum_filter]
      refine (Fintype.sum_equiv eN (fun a => q v (fun j => sMid a j.1))
        (fun u => q v u.1) (fun _ => rfl)).trans ?_
      rw [← sum_subtype (univ.filter fun u : (∀ j : ClosedNeighborhood G v, S j.1) =>
          u ⟨v, Or.inl rfl⟩ = s₀ v ∧ u ⟨hT.parent r v, Or.inr hadj_vp⟩ = s₀ (hT.parent r v))
        (fun _ => mem_filter_univ _)]
    rw [hsum_q]
    by_cases he0 :
        edgeMarginal G q v (hT.parent r v) hadj_vp (s₀ v) (s₀ (hT.parent r v)) = 0
    · simp [he0]
    · simp [he0]

/-- Root marginal of `treeWeight hT q r` equals `q r u_r`. -/
private theorem sum_treeWeight_restrict_root {G : SimpleGraph ι} (hT : G.IsTree) (r : ι)
    {q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ}
    (hnn : ∀ i u, 0 ≤ q i u) (hedge : IsEdgeConsistent G q) (hne : ∀ i, Nonempty (S i))
    (u_r : ∀ j : ClosedNeighborhood G r, S j.1) :
    by
      classical
      exact ∑ s : (∀ i, S i),
        (if (fun j : ClosedNeighborhood G r => s j.1) = u_r then treeWeight hT q r s else 0) =
      q r u_r := by
  classical
  have hadj_cr : ∀ c : UpstreamNeighbors hT r r, G.Adj c.1 r := fun c => by
    simpa [c.2.2] using hT.adj_parent r c.2.1
  let sBase : ∀ i, S i := fun i =>
    if hi : i = r ∨ G.Adj r i then u_r ⟨i, hi⟩ else (hne i).some
  have hsBase_restrict : (fun j : ClosedNeighborhood G r => sBase j.1) = u_r := by
    ext ⟨j, hj⟩
    simp [sBase, hj]
  let Pout : ι → Prop := fun z => ¬ (z = r ∨ G.Adj r z)
  have hsub : ∀ (c : UpstreamNeighbors hT r r) z,
      (z ∈ hT.treeSide c.1 r ∧ z ≠ c.1) → Pout z := by
    rintro c z ⟨hzc, hzne⟩ (rfl | hadj_rz)
    · exact hT.not_mem_treeSide_other (hadj_cr c) hzc
    · let cz : UpstreamNeighbors hT r r :=
        ⟨z, ((hT.adj_iff_parent r).mp hadj_rz).resolve_left fun h => h.1 rfl⟩
      have heq := upstream_unique_of_mem_treeSide (hT.self_mem_treeSide_of_adj (hadj_cr cz)) hzc
      exact hzne (congrArg Subtype.val heq)
  have hcov : ∀ z, Pout z → ∃ c : UpstreamNeighbors hT r r, z ∈ hT.treeSide c.1 r ∧ z ≠ c.1 := by
    intro z hz
    have hzr : z ≠ r := fun h => hz (Or.inl h)
    obtain ⟨c, hzc⟩ := exists_upstream_mem_treeSide_root hT r hzr
    exact ⟨c, hzc, fun h => hz (Or.inr (h ▸ (hadj_cr c).symm))⟩
  have hdisj : ∀ (c₁ c₂ : UpstreamNeighbors hT r r) z,
      (z ∈ hT.treeSide c₁.1 r ∧ z ≠ c₁.1) → (z ∈ hT.treeSide c₂.1 r ∧ z ≠ c₂.1) → c₁ = c₂ :=
    fun _ _ _ h1 h2 => upstream_unique_of_mem_treeSide h1.1 h2.1
  let eBase : (∀ z : {z : ι // Pout z}, S z.1) ≃
      {s : ∀ i, S i // (fun j : ClosedNeighborhood G r => s j.1) = u_r} :=
    { toFun := fun x => ⟨override sBase x, by
        ext ⟨j, hj⟩
        have hnp : ¬ Pout j := fun h => h hj
        rw [override_of_neg _ _ hnp]
        exact congrFun hsBase_restrict ⟨j, hj⟩⟩
      invFun := fun s z => s.1 z.1
      left_inv := fun x => by
        ext ⟨z, hz⟩
        exact override_of_pos sBase x hz
      right_inv := fun ⟨s, hs⟩ => by
        ext i
        dsimp only
        by_cases hi : Pout i
        · exact override_of_pos sBase _ hi
        · rw [override_of_neg sBase _ hi]
          have hmem : i = r ∨ G.Adj r i := not_not.mp hi
          exact (congrFun hsBase_restrict ⟨i, hmem⟩).trans (congrFun hs ⟨i, hmem⟩).symm }
  let eOut := piEquivDisjointUnion (S := S) hsub hcov hdisj
  let eAll : (∀ c : UpstreamNeighbors hT r r,
      ∀ z : {z : ι // z ∈ hT.treeSide c.1 r ∧ z ≠ c.1}, S z.1) ≃
      {s : ∀ i, S i // (fun j : ClosedNeighborhood G r => s j.1) = u_r} :=
    eOut.symm.trans eBase
  have hfactor : ∀ y : (∀ c : UpstreamNeighbors hT r r,
        ∀ z : {z : ι // z ∈ hT.treeSide c.1 r ∧ z ≠ c.1}, S z.1),
      treeWeight hT q r (eAll y).1 =
        q r u_r *
          ∏ c : UpstreamNeighbors hT r r,
            ∏ z ∈ univ.filter (fun z => z ∈ hT.treeSide c.1 r),
              treePotential hT q r z (fun j => override sBase (y c) j.1) := by
    intro y
    rw [treeWeight, ← mul_prod_erase univ _ (mem_univ r)]
    have herase_eq : univ.erase r =
        univ.biUnion fun c : UpstreamNeighbors hT r r =>
          univ.filter (fun z => z ∈ hT.treeSide c.1 r) := by
      ext z
      simp only [mem_erase, mem_univ, and_true, mem_biUnion, mem_filter, true_and]
      exact ⟨fun hzr => exists_upstream_mem_treeSide_root hT r hzr,
        fun ⟨c, hzc⟩ hzr => hT.not_mem_treeSide_other (hadj_cr c) (hzr ▸ hzc)⟩
    rw [herase_eq, prod_biUnion (by simpa only [coe_univ] using
      pairwiseDisjoint_filter_treeSide hT r r)]
    congr 1
    · unfold treePotential
      simp only [↓reduceDIte, (eAll y).2]
    · refine prod_congr rfl fun c _ => prod_congr rfl fun z hz => ?_
      have hzc : z ∈ hT.treeSide c.1 r := (mem_filter.mp hz).2
      congr 1
      ext ⟨j, hj⟩
      dsimp only
      by_cases hjc : j ∈ hT.treeSide c.1 r
      · by_cases hj_eq : j = c.1
        · subst hj_eq
          have hnp : ¬ Pout c.1 := fun h => h (Or.inr (hadj_cr c).symm)
          have hnr : ¬ (c.1 ∈ hT.treeSide c.1 r ∧ c.1 ≠ c.1) := fun h => h.2 rfl
          change override sBase (eOut.symm y) c.1 = override sBase (y c) c.1
          simp only [override, hnp, hnr, ↓reduceDIte]
        · have hpj : Pout j := hsub c j ⟨hjc, hj_eq⟩
          change override sBase (eOut.symm y) j = override sBase (y c) j
          rw [override_of_pos _ _ hpj, override_of_pos _ _ ⟨hjc, hj_eq⟩]
          simp only [eOut, piEquivDisjointUnion, Equiv.coe_fn_symm_mk]
          have hspec := Classical.choose_spec (hcov j hpj)
          have hkeq : Classical.choose (hcov j hpj) = c :=
            upstream_unique_of_mem_treeSide hspec.1 hjc
          have key : ∀ (c' : UpstreamNeighbors hT r r)
              (h' : j ∈ hT.treeSide c'.1 r ∧ j ≠ c'.1),
              c' = c → y c' ⟨j, h'⟩ = y c ⟨j, ⟨hjc, hj_eq⟩⟩ := by
            rintro _ _ rfl
            rfl
          exact key _ hspec hkeq
      · have hj_eq_r : j = r := by
          rcases hj with rfl | hadj_zj
          · exact (hjc hzc).elim
          · exact (hT.eq_of_mem_treeSide_of_adj_notMem (hadj_cr c) hzc hjc hadj_zj).2
        subst j
        have hnp : ¬ Pout r := fun h => h (Or.inl rfl)
        have hnc : ¬ (r ∈ hT.treeSide c.1 r ∧ r ≠ c.1) := fun h =>
          hT.not_mem_treeSide_other (hadj_cr c) h.1
        change override sBase (eOut.symm y) r = override sBase (y c) r
        simp only [override, hnp, hnc, ↓reduceDIte]
  rw [← sum_filter,
    sum_subtype (univ.filter fun s : (∀ i, S i) =>
        (fun j : ClosedNeighborhood G r => s j.1) = u_r)
      (fun _ => mem_filter_univ _),
    ← Fintype.sum_equiv eAll _ _ (fun _ => rfl)]
  simp_rw [hfactor, ← mul_sum]
  rw [← Fintype.prod_sum (fun (c : UpstreamNeighbors hT r r)
    (x : ∀ z : {z : ι // z ∈ hT.treeSide c.1 r ∧ z ≠ c.1}, S z.1) =>
    ∏ z ∈ univ.filter (fun z => z ∈ hT.treeSide c.1 r),
      treePotential hT q r z (fun j => override sBase x j.1))]
  have hsub_c : ∀ c : UpstreamNeighbors hT r r,
      (∑ x : (∀ z : {z : ι // z ∈ hT.treeSide c.1 r ∧ z ≠ c.1}, S z.1),
        ∏ z ∈ univ.filter (fun z => z ∈ hT.treeSide c.1 r),
          treePotential hT q r z (fun j => override sBase x j.1)) =
      if edgeMarginal G q c.1 r (hadj_cr c)
          (u_r ⟨c.1, Or.inr (hadj_cr c).symm⟩) (u_r ⟨r, Or.inl rfl⟩) = 0
      then 0 else 1 := by
    rintro ⟨c, hc_ne, hc_par⟩
    have hstep := sum_subtree_treePotential hT r hnn hedge hc_ne sBase
    have hs_c : sBase c = u_r ⟨c, Or.inr (hadj_cr ⟨c, hc_ne, hc_par⟩).symm⟩ :=
      congrFun hsBase_restrict ⟨c, Or.inr (hadj_cr ⟨c, hc_ne, hc_par⟩).symm⟩
    have hs_r : sBase r = u_r ⟨r, Or.inl rfl⟩ :=
      congrFun hsBase_restrict ⟨r, Or.inl rfl⟩
    have hedge_eq : ∀ (p : ι) (hadj : G.Adj c p), p = r →
        edgeMarginal G q c p hadj (sBase c) (sBase p) =
          edgeMarginal G q c r (hadj_cr ⟨c, hc_ne, hc_par⟩)
            (u_r ⟨c, Or.inr (hadj_cr ⟨c, hc_ne, hc_par⟩).symm⟩) (u_r ⟨r, Or.inl rfl⟩) := by
      rintro _ _ rfl
      rw [hs_c, hs_r]
    rw [← hedge_eq _ (hT.adj_parent r hc_ne) hc_par]
    have key_sum : ∀ (p : ι) (hp : p = hT.parent r c),
        (∑ x : (∀ z : {z : ι // z ∈ hT.treeSide c p ∧ z ≠ c}, S z.1),
          ∏ z ∈ univ.filter (fun z => z ∈ hT.treeSide c p),
            treePotential hT q r z (fun j => override sBase x j.1)) =
        (∑ x : (∀ z : {z : ι // z ∈ hT.treeSide c (hT.parent r c) ∧ z ≠ c}, S z.1),
          ∏ z ∈ univ.filter (fun z => z ∈ hT.treeSide c (hT.parent r c)),
            treePotential hT q r z (fun j => override sBase x j.1)) := by
      rintro _ rfl
      rfl
    rw [key_sum r hc_par.symm]
    exact hstep
  simp_rw [hsub_c]
  by_cases hex : ∃ c : UpstreamNeighbors hT r r,
      edgeMarginal G q c.1 r (hadj_cr c)
        (u_r ⟨c.1, Or.inr (hadj_cr c).symm⟩) (u_r ⟨r, Or.inl rfl⟩) = 0
  · obtain ⟨c, hc0⟩ := hex
    have hprod0 : (∏ c' : UpstreamNeighbors hT r r,
        if edgeMarginal G q c'.1 r (hadj_cr c')
            (u_r ⟨c'.1, Or.inr (hadj_cr c').symm⟩) (u_r ⟨r, Or.inl rfl⟩) = 0
        then (0 : ℝ) else 1) = 0 :=
      prod_eq_zero (mem_univ c) (by simp [hc0])
    have hrc0 : edgeMarginal G q r c.1 (hadj_cr c).symm
        (u_r ⟨r, Or.inl rfl⟩) (u_r ⟨c.1, Or.inr (hadj_cr c).symm⟩) = 0 := by
      rwa [hedge r c.1 (hadj_cr c).symm _ _]
    have hqr0 : q r u_r = 0 := q_eq_zero_of_edgeMarginal_eq_zero hnn (hadj_cr c).symm hrc0
    rw [hprod0, hqr0, mul_zero]
  · push Not at hex
    have hprod1 : (∏ c' : UpstreamNeighbors hT r r,
        if edgeMarginal G q c'.1 r (hadj_cr c')
            (u_r ⟨c'.1, Or.inr (hadj_cr c').symm⟩) (u_r ⟨r, Or.inl rfl⟩) = 0
        then (0 : ℝ) else 1) = 1 :=
      prod_eq_one fun c' _ => ite_eq_right (hex c')
    rw [hprod1, mul_one]

private theorem nonempty_of_isLocalDistribution {G : SimpleGraph ι}
    {q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ}
    (hloc : IsLocalDistribution G q) (i : ι) : Nonempty (S i) := by
  classical
  by_contra hne
  have : IsEmpty (S i) := not_nonempty_iff.mp hne
  have : IsEmpty (∀ j : ClosedNeighborhood G i, S j.1) :=
    ⟨fun u => isEmptyElim (u ⟨i, Or.inl rfl⟩)⟩
  have hsum := (hloc i).2
  have h0 : (∑ u : (∀ j : ClosedNeighborhood G i, S j.1), q i u) = 0 := Fintype.sum_empty (q i)
  have hsum' : (∑ u : (∀ j : ClosedNeighborhood G i, S j.1), q i u) = 1 := by
    convert hsum
  linarith

end TreeLiftPrivate

/-! #### Public junction-tree lifting, tree Markov networks, and Theorem 7.14 -/

section TreeTheorems

variable [Fintype ι] [∀ i, Fintype (S i)]

/-- **Junction-tree lifting on finite trees (zeros allowed, no positivity required)**:
given any finite tree `hT : G.IsTree` and any locally normalized, edge-consistent family `q` on
closed neighborhoods of `G`, there exists a global joint distribution `σ` that is a nonnegative
local Markov network on `G` and realizes `q` as its exact closed-neighborhood marginals. -/
theorem treeLift_exists_isLocalMarkovNetwork {G : SimpleGraph ι} (hT : G.IsTree)
    {q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ}
    (hloc : IsLocalDistribution G q) (hedge : IsEdgeConsistent G q) :
    ∃ σ : Convexity.StdSimplex ℝ (∀ i, S i),
      IsLocalMarkovNetwork G σ ∧
      ∀ (i : ι) (u : ∀ j : ClosedNeighborhood G i, S j.1),
        neighborhoodMarginal G σ i u = q i u := by
  classical
  have hnn : ∀ i u, 0 ≤ q i u := fun i => (hloc i).1
  have hne : ∀ i, Nonempty (S i) := nonempty_of_isLocalDistribution hloc
  obtain ⟨r₀⟩ := hT.connected.nonempty
  have hsum : ∑ s : (∀ i, S i), treeWeight hT q r₀ s = 1 := by
    have hpart : ∑ s : (∀ i, S i), treeWeight hT q r₀ s =
        ∑ u : (∀ j : ClosedNeighborhood G r₀, S j.1),
          ∑ s : (∀ i, S i),
            if (fun j : ClosedNeighborhood G r₀ => s j.1) = u then treeWeight hT q r₀ s else 0 := by
      rw [sum_comm]
      refine sum_congr rfl fun s _ => ?_
      simp only [sum_ite_eq univ, mem_univ, ↓reduceIte]
    rw [hpart]
    have hinner : ∀ u : (∀ j : ClosedNeighborhood G r₀, S j.1),
        (∑ s : (∀ i, S i),
          if (fun j : ClosedNeighborhood G r₀ => s j.1) = u then treeWeight hT q r₀ s else 0) =
        q r₀ u :=
      fun u => sum_treeWeight_restrict_root hT r₀ hnn hedge hne u
    simp_rw [hinner]
    convert (hloc r₀).2
  let σ : Convexity.StdSimplex ℝ (∀ i, S i) :=
    simplexOfFun (treeWeight hT q r₀) (treeWeight_nonneg hT hnn r₀) hsum
  refine ⟨σ, ⟨treePotential hT q r₀, 1, treePotential_nonneg hT hnn r₀, zero_lt_one, fun s => by
      simp only [σ, simplexOfFun_weights, div_one, treeWeight]⟩, fun i u => ?_⟩
  rw [neighborhoodMarginal_eq_sum]
  have hrew : (∑ s : (∀ k, S k),
        if (fun j : ClosedNeighborhood G i => s j.1) = u then σ.weights s else 0) =
      ∑ s : (∀ k, S k),
        if (fun j : ClosedNeighborhood G i => s j.1) = u then treeWeight hT q i s else 0 :=
    sum_congr rfl fun s _ => by
      simp only [σ, simplexOfFun_weights, treeWeight_root_indep hT hedge r₀ i s]
  rw [hrew]
  exact sum_treeWeight_restrict_root hT i hnn hedge hne u

/-- Every global joint distribution induces locally normalized, edge-consistent, and
intersection-consistent neighborhood marginals on any graph `G`. -/
theorem isLocalDistribution_neighborhoodMarginal (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) :
    IsLocalDistribution G (neighborhoodMarginal G σ) := by
  classical
  intro i
  refine ⟨fun u => neighborhoodMarginal_nonneg G σ i u, ?_⟩
  convert sum_neighborhoodMarginal G σ i

theorem isEdgeConsistent_neighborhoodMarginal (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) :
    IsEdgeConsistent G (neighborhoodMarginal G σ) := by
  classical
  intro i j hadj a b
  have hside : ∀ (x y : ι) (hxy : G.Adj x y) (ax : S x) (by_ : S y),
      edgeMarginal G (neighborhoodMarginal G σ) x y hxy ax by_ =
        ∑ s : (∀ k, S k), if s x = ax ∧ s y = by_ then σ.weights s else 0 := by
    intro x y hxy ax by_
    rw [edgeMarginal_def]
    exact sum_ite_neighborhoodMarginal G σ x
      (fun u => u ⟨x, Or.inl rfl⟩ = ax ∧ u ⟨y, Or.inr hxy⟩ = by_)
  rw [hside i j hadj a b, hside j i hadj.symm b a]
  exact sum_congr rfl fun s _ => by simp only [and_comm]

theorem isIntersectionConsistent_neighborhoodMarginal (G : SimpleGraph ι)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) :
    IsIntersectionConsistent G (neighborhoodMarginal G σ) := by
  classical
  intro i j y
  let T : Set ι := {k : ι | (k = i ∨ G.Adj i k) ∧ (k = j ∨ G.Adj j k)}
  have hside : ∀ (x : ι) (hx : ∀ k ∈ T, k = x ∨ G.Adj x k),
      restrictMarginal G (neighborhoodMarginal G σ) x T hx y =
        ∑ s : (∀ k, S k), if (fun k : T => s k.1) = y then σ.weights s else 0 := by
    intro x hx
    rw [restrictMarginal_def]
    exact sum_ite_neighborhoodMarginal G σ x (fun u => (fun k : T => u ⟨k.1, hx k.1 k.2⟩) = y)
  exact (hside i (fun _ h => h.1)).trans (hside j (fun _ h => h.2)).symm

private theorem isEdgeConsistent_of_isIntersectionConsistent_of_isTree {G : SimpleGraph ι}
    (hT : G.IsTree) {q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ}
    (hint : IsIntersectionConsistent G q) :
    IsEdgeConsistent G q := by
  classical
  intro i j hadj a b
  let T : Set ι := {k : ι | (k = i ∨ G.Adj i k) ∧ (k = j ∨ G.Adj j k)}
  have hT_eq : ∀ k : ι, k ∈ T ↔ k = i ∨ k = j := by
    intro k
    constructor
    · rintro ⟨hki | hik, hkj | hjk⟩
      · exact Or.inl hki
      · exact Or.inl hki
      · exact Or.inr hkj
      · exfalso
        have hne_ik : i ≠ k := hik.ne
        have hne_jk : j ≠ k := hjk.ne
        have hne_ij : i ≠ j := hadj.ne
        let w : G.Walk i i :=
          SimpleGraph.Walk.cons hadj
            (SimpleGraph.Walk.cons hjk (SimpleGraph.Walk.cons hik.symm .nil))
        have hcyc : w.IsCycle := by
          refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
          · simp [w, hne_ij, hne_ik, hne_jk, Ne.symm hne_ij, Ne.symm hne_ik]
          · simp [w]
          · simp [w, hne_jk, hne_ik.symm, hne_ij.symm]
        exact hT.isAcyclic w hcyc
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, Or.inr hadj.symm⟩
      · exact ⟨Or.inr hadj, Or.inl rfl⟩
  let y : ∀ k : T, S k.1 := fun k =>
    if hki : k.1 = i then hki ▸ a else ((hT_eq k.1).mp k.2).resolve_left hki ▸ b
  have hy_i : y ⟨i, (hT_eq i).mpr (Or.inl rfl)⟩ = a := by simp [y]
  have hy_j : y ⟨j, (hT_eq j).mpr (Or.inr rfl)⟩ = b := by simp [y, hadj.ne']
  have hcond_i : ∀ u : (∀ k : ClosedNeighborhood G i, S k.1),
      ((fun k : T => u ⟨k.1, k.2.1⟩) = y) ↔ (u ⟨i, Or.inl rfl⟩ = a ∧ u ⟨j, Or.inr hadj⟩ = b) := by
    intro u
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have h1 := congrFun h ⟨i, (hT_eq i).mpr (Or.inl rfl)⟩
        simpa [hy_i] using h1
      · have h2 := congrFun h ⟨j, (hT_eq j).mpr (Or.inr rfl)⟩
        simpa [hy_j] using h2
    · rintro ⟨ha, hb⟩
      ext ⟨k, hk⟩
      rcases (hT_eq k).mp hk with rfl | rfl
      · simpa [hy_i] using ha
      · simpa [hy_j] using hb
  have hcond_j : ∀ v : (∀ k : ClosedNeighborhood G j, S k.1),
      ((fun k : T => v ⟨k.1, k.2.2⟩) = y) ↔
        (v ⟨j, Or.inl rfl⟩ = b ∧ v ⟨i, Or.inr hadj.symm⟩ = a) := by
    intro v
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have h2 := congrFun h ⟨j, (hT_eq j).mpr (Or.inr rfl)⟩
        simpa [hy_j] using h2
      · have h1 := congrFun h ⟨i, (hT_eq i).mpr (Or.inl rfl)⟩
        simpa [hy_i] using h1
    · rintro ⟨hb, ha⟩
      ext ⟨k, hk⟩
      rcases (hT_eq k).mp hk with rfl | rfl
      · simpa [hy_i] using ha
      · simpa [hy_j] using hb
  have heq := hint i j y
  unfold restrictMarginal at heq
  rw [edgeMarginal_def, edgeMarginal_def]
  have hL : (∑ u : (∀ k : ClosedNeighborhood G i, S k.1),
        if u ⟨i, Or.inl rfl⟩ = a ∧ u ⟨j, Or.inr hadj⟩ = b then q i u else 0) =
      ∑ u : (∀ k : ClosedNeighborhood G i, S k.1),
        if (fun k : T => u ⟨k.1, k.2.1⟩) = y then q i u else 0 :=
    sum_congr rfl fun u _ => by simp only [hcond_i]
  have hR : (∑ v : (∀ k : ClosedNeighborhood G j, S k.1),
        if v ⟨j, Or.inl rfl⟩ = b ∧ v ⟨i, Or.inr hadj.symm⟩ = a then q j v else 0) =
      ∑ v : (∀ k : ClosedNeighborhood G j, S k.1),
        if (fun k : T => v ⟨k.1, k.2.2⟩) = y then q j v else 0 :=
    sum_congr rfl fun v _ => by simp only [hcond_j]
  rw [hL, hR]
  convert heq

/-- On any finite tree `G`, full neighborhood-intersection consistency is equivalent to edge
consistency for locally normalized families `q`. -/
theorem isIntersectionConsistent_iff_isEdgeConsistent_of_isTree {G : SimpleGraph ι}
    (hT : G.IsTree) {q : ∀ i : ι, (∀ j : ClosedNeighborhood G i, S j.1) → ℝ}
    (hloc : IsLocalDistribution G q) :
    IsIntersectionConsistent G q ↔ IsEdgeConsistent G q := by
  refine ⟨isEdgeConsistent_of_isIntersectionConsistent_of_isTree hT, fun hedge => ?_⟩
  obtain ⟨σ, _, hmarg⟩ := treeLift_exists_isLocalMarkovNetwork hT hloc hedge
  have hq_eq : q = neighborhoodMarginal G σ := funext fun i => funext fun u => (hmarg i u).symm
  rw [hq_eq]
  exact isIntersectionConsistent_neighborhoodMarginal G σ

end TreeTheorems

section TreeMarkovNetworks

variable [Fintype ι] [∀ i, Finite (S i)]

/-- **Unconditional Lemma 7.12 on all finite trees** (no positivity hypothesis; zeros allowed):
on any finite tree `G`, every joint distribution `σ` is local-neighborhood equivalent to a
nonnegative local Markov network `τ` on `G`. -/
theorem exists_isLocalMarkovNetwork_of_isTree {G : SimpleGraph ι} (hT : G.IsTree)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) :
    ∃ τ : Convexity.StdSimplex ℝ (∀ i, S i),
      LocalNeighborhoodEquiv G τ σ ∧ IsLocalMarkovNetwork G τ := by
  have := fun i => Fintype.ofFinite (S i)
  obtain ⟨τ, hmk, hmarg⟩ := treeLift_exists_isLocalMarkovNetwork hT
    (isLocalDistribution_neighborhoodMarginal G σ) (isEdgeConsistent_neighborhoodMarginal G σ)
  exact ⟨τ, hmarg, hmk⟩

/-- **Unconditional Theorem 7.13 on all finite trees** (no positivity hypothesis; zeros allowed):
for any finite tree graphical game `M` and any correlated equilibrium `σ` of `M.toCostGame`, there
exists a local Markov network `τ` on `M.graph` that is a correlated equilibrium of `M.toCostGame`,
local-neighborhood equivalent to `σ`, and expected-payoff equivalent to `σ`. -/
theorem GraphicalGame.exists_isLocalMarkovNetwork_ce_of_isTree [DecidableEq ι]
    (M : GraphicalGame ι S) (hT : M.graph.IsTree)
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (hce : M.toCostGame.IsCorrelatedEquilibrium σ) :
    ∃ τ : Convexity.StdSimplex ℝ (∀ i, S i),
      M.toCostGame.IsCorrelatedEquilibrium τ ∧
      M.ExpectedPayoffEquiv τ σ ∧
      LocalNeighborhoodEquiv M.graph τ σ ∧
      IsLocalMarkovNetwork M.graph τ := by
  obtain ⟨τ, hln, hmk⟩ := exists_isLocalMarkovNetwork_of_isTree hT σ
  exact ⟨τ, hln.isCorrelatedEquilibrium_iff.mpr hce, hln.expectedPayoffEquiv, hln, hmk⟩

end TreeMarkovNetworks

section TreeCETheorems

variable [Fintype ι] [∀ i, Fintype (S i)]

private theorem isCorrelatedEquilibrium_iff_satisfiesLocalCE [DecidableEq ι]
    (M : GraphicalGame ι S) (σ : Convexity.StdSimplex ℝ (∀ i, S i)) :
    M.toCostGame.IsCorrelatedEquilibrium σ ↔
      M.SatisfiesLocalCE (neighborhoodMarginal M.graph σ) := by
  classical
  rw [CostGame.isCorrelatedEquilibrium_iff]
  refine forall_congr' fun i => forall_congr' fun a => forall_congr' fun b => ?_
  have hL : σ.weights.sum (fun s w => w * if s i = a then M.toCostGame.cost i s else 0) =
      -(∑ u : (∀ j : ClosedNeighborhood M.graph i, S j.1),
        if u ⟨i, Or.inl rfl⟩ = a then
          neighborhoodMarginal M.graph σ i u * M.localPayoff i u
        else 0) := by
    have h1 := sum_mul_local_eq_sum_neighborhoodMarginal M.graph σ i
      (fun u => if u ⟨i, Or.inl rfl⟩ = a then -M.localPayoff i u else 0)
    simp only [GraphicalGame.toCostGame_cost, GraphicalGame.payoff_eq_localPayoff]
    rw [h1, ← sum_neg_distrib]
    exact sum_congr rfl fun u _ => by split_ifs <;> ring
  have hR : σ.weights.sum (fun s w =>
        w * if s i = a then M.toCostGame.cost i (update s i b) else 0) =
      -(∑ u : (∀ j : ClosedNeighborhood M.graph i, S j.1),
        if u ⟨i, Or.inl rfl⟩ = a then
          neighborhoodMarginal M.graph σ i u * M.localPayoff i (update u ⟨i, Or.inl rfl⟩ b)
        else 0) := by
    have hupd : ∀ s : (∀ k, S k),
        M.payoff i (update s i b) =
          M.localPayoff i (update (fun j : ClosedNeighborhood M.graph i => s j.1)
            ⟨i, Or.inl rfl⟩ b) := fun s => by
      rw [GraphicalGame.payoff_eq_localPayoff]
      congr 1
      ext ⟨j, hj⟩
      by_cases hji : j = i
      · subst hji; simp
      · have hne : (⟨j, hj⟩ : ClosedNeighborhood M.graph i) ≠ ⟨i, Or.inl rfl⟩ :=
          fun h => hji (congrArg Subtype.val h)
        simp [update_of_ne hji, update_of_ne hne]
    have h1 := sum_mul_local_eq_sum_neighborhoodMarginal M.graph σ i
      (fun u => if u ⟨i, Or.inl rfl⟩ = a then
        -M.localPayoff i (update u ⟨i, Or.inl rfl⟩ b) else 0)
    simp only [GraphicalGame.toCostGame_cost, hupd]
    rw [h1, ← sum_neg_distrib]
    exact sum_congr rfl fun u _ => by split_ifs <;> ring
  rw [hL, hR, neg_le_neg_iff]

/-- **Completeness of Kearns's local CE linear program** ([Kearns2007], §7.4.3, p. 175): for any
finite graphical game `M` (on an arbitrary graph) and any correlated equilibrium `σ` of
`M.toCostGame`, its closed-neighborhood marginals satisfy `M.IsLocalCorrelatedEquilibrium` (and
`IsEdgeConsistent`), and every player's expected payoff equals its local marginal expectation. -/
theorem GraphicalGame.isLocalCorrelatedEquilibrium_neighborhoodMarginal [DecidableEq ι]
    (M : GraphicalGame ι S) {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (hce : M.toCostGame.IsCorrelatedEquilibrium σ) :
    M.IsLocalCorrelatedEquilibrium (neighborhoodMarginal M.graph σ) ∧
      IsEdgeConsistent M.graph (neighborhoodMarginal M.graph σ) ∧
      ∀ i : ι, σ.weights.sum (fun s w => w * M.payoff i s) =
        open Classical in ∑ u, neighborhoodMarginal M.graph σ i u * M.localPayoff i u := by
  classical
  refine ⟨⟨(isCorrelatedEquilibrium_iff_satisfiesLocalCE M σ).mp hce,
      isLocalDistribution_neighborhoodMarginal M.graph σ,
      isIntersectionConsistent_neighborhoodMarginal M.graph σ⟩,
    isEdgeConsistent_neighborhoodMarginal M.graph σ, fun i => ?_⟩
  simpa only [GraphicalGame.payoff_eq_localPayoff] using
    sum_mul_local_eq_sum_neighborhoodMarginal M.graph σ i (M.localPayoff i)

/-- **Soundness of edge-consistent local tree CE linear program** (sharper form of [Kearns2007],
Theorem 7.14, p. 175): on any finite tree graphical game `M` (`hT : M.graph.IsTree`), every
locally normalized, edge-consistent solution `q` to the local CE constraints lifts to a global
correlated equilibrium `σ` of `M.toCostGame` that is a nonnegative local Markov network on
`M.graph`, realizes `q` as its exact closed-neighborhood marginals, and matches every player's
expected payoff and social welfare. -/
theorem GraphicalGame.exists_isCorrelatedEquilibrium_of_edgeConsistent [DecidableEq ι]
    (M : GraphicalGame ι S) (hT : M.graph.IsTree)
    {q : ∀ i : ι, (∀ j : ClosedNeighborhood M.graph i, S j.1) → ℝ}
    (hce : M.SatisfiesLocalCE q) (hloc : IsLocalDistribution M.graph q)
    (hedge : IsEdgeConsistent M.graph q) :
    ∃ σ : Convexity.StdSimplex ℝ (∀ i, S i),
      M.toCostGame.IsCorrelatedEquilibrium σ ∧
      IsLocalMarkovNetwork M.graph σ ∧
      (∀ (i : ι) (u : ∀ j : ClosedNeighborhood M.graph i, S j.1),
        neighborhoodMarginal M.graph σ i u = q i u) ∧
      (∀ i : ι, σ.weights.sum (fun s w => w * M.payoff i s) =
        open Classical in ∑ u, q i u * M.localPayoff i u) ∧
      (∑ i : ι, σ.weights.sum (fun s w => w * M.payoff i s) =
        open Classical in ∑ i : ι, ∑ u, q i u * M.localPayoff i u) := by
  classical
  obtain ⟨σ, hmk, hmarg⟩ := treeLift_exists_isLocalMarkovNetwork hT hloc hedge
  have hq_eq : neighborhoodMarginal M.graph σ = q := funext fun i => funext fun u => hmarg i u
  have hσ_ce : M.toCostGame.IsCorrelatedEquilibrium σ :=
    (isCorrelatedEquilibrium_iff_satisfiesLocalCE M σ).mpr (hq_eq.symm ▸ hce)
  have hpay : ∀ i : ι, σ.weights.sum (fun s w => w * M.payoff i s) =
      ∑ u : (∀ j : ClosedNeighborhood M.graph i, S j.1), q i u * M.localPayoff i u := by
    intro i
    have h1 := sum_mul_local_eq_sum_neighborhoodMarginal M.graph σ i (M.localPayoff i)
    simpa only [GraphicalGame.payoff_eq_localPayoff, hmarg] using h1
  refine ⟨σ, hσ_ce, hmk, hmarg, fun i => ?_, ?_⟩
  · convert hpay i
  · convert sum_congr rfl fun i _ => hpay i

/-- **Theorem 7.14** ([Kearns2007], §7.4.3, p. 175): for any finite tree graphical game `(G, M)`,
every feasible solution `q` to Kearns's local correlated-equilibrium linear program
(`M.IsLocalCorrelatedEquilibrium q`, constraints (i)–(iii)) lifts to a global correlated
equilibrium `σ` of `M.toCostGame` (represented as a nonnegative local Markov network on `M.graph`)
with identical closed-neighborhood marginals, per-player expected payoffs, and social welfare. -/
theorem GraphicalGame.exists_isCorrelatedEquilibrium_of_isLocalCorrelatedEquilibrium
    [DecidableEq ι] (M : GraphicalGame ι S) (hT : M.graph.IsTree)
    {q : ∀ i : ι, (∀ j : ClosedNeighborhood M.graph i, S j.1) → ℝ}
    (hq : M.IsLocalCorrelatedEquilibrium q) :
    ∃ σ : Convexity.StdSimplex ℝ (∀ i, S i),
      M.toCostGame.IsCorrelatedEquilibrium σ ∧
      IsLocalMarkovNetwork M.graph σ ∧
      (∀ (i : ι) (u : ∀ j : ClosedNeighborhood M.graph i, S j.1),
        neighborhoodMarginal M.graph σ i u = q i u) ∧
      (∀ i : ι, σ.weights.sum (fun s w => w * M.payoff i s) =
        open Classical in ∑ u, q i u * M.localPayoff i u) ∧
      (∑ i : ι, σ.weights.sum (fun s w => w * M.payoff i s) =
        open Classical in ∑ i : ι, ∑ u, q i u * M.localPayoff i u) :=
  M.exists_isCorrelatedEquilibrium_of_edgeConsistent hT hq.1 hq.2.1
    (isEdgeConsistent_of_isIntersectionConsistent_of_isTree hT hq.2.2)

/-- **Exact soundness and completeness characterization on trees** ([Kearns2007], Theorem 7.14,
p. 175): on a finite tree graphical game `M`, a local marginal family `q` satisfies
`M.IsLocalCorrelatedEquilibrium q` if and only if it is the family of closed-neighborhood marginals
of some global correlated equilibrium `σ` of `M.toCostGame`. -/
theorem GraphicalGame.isLocalCorrelatedEquilibrium_iff_exists_isCorrelatedEquilibrium
    [DecidableEq ι] (M : GraphicalGame ι S) (hT : M.graph.IsTree)
    {q : ∀ i : ι, (∀ j : ClosedNeighborhood M.graph i, S j.1) → ℝ} :
    M.IsLocalCorrelatedEquilibrium q ↔
      ∃ σ : Convexity.StdSimplex ℝ (∀ i, S i),
        M.toCostGame.IsCorrelatedEquilibrium σ ∧
        ∀ (i : ι) (u : ∀ j : ClosedNeighborhood M.graph i, S j.1),
          neighborhoodMarginal M.graph σ i u = q i u := by
  constructor
  · intro hq
    obtain ⟨σ, hce, _, hmarg, _, _⟩ :=
      M.exists_isCorrelatedEquilibrium_of_isLocalCorrelatedEquilibrium hT hq
    exact ⟨σ, hce, hmarg⟩
  · rintro ⟨σ, hce, hmarg⟩
    have hq_eq : q = neighborhoodMarginal M.graph σ :=
      funext fun i => funext fun u => (hmarg i u).symm
    rw [hq_eq]
    exact (M.isLocalCorrelatedEquilibrium_neighborhoodMarginal hce).1

private theorem card_sigma_prod_le {α ι : Type*} {S : ι → Type*}
    [Fintype α] [∀ i, Fintype (S i)] {m : ℕ}
    (hm : ∀ i, Fintype.card (S i) ≤ m) (f g : α → ι) :
    Fintype.card (Σ a : α, S (f a) × S (g a)) ≤ Fintype.card α * m ^ 2 := by
  rw [Fintype.card_sigma]
  calc ∑ a : α, Fintype.card (S (f a) × S (g a))
      = ∑ a : α, Fintype.card (S (f a)) * Fintype.card (S (g a)) :=
        sum_congr rfl fun a _ => Fintype.card_prod _ _
    _ ≤ ∑ _a : α, m ^ 2 := sum_le_sum fun a _ => by
        rw [sq]
        exact Nat.mul_le_mul (hm (f a)) (hm (g a))
    _ = Fintype.card α * m ^ 2 := by rw [sum_const, card_univ, smul_eq_mul]

/-- **Polynomial size bounds for the tree local CE linear program** ([Kearns2007], §7.4.3, p. 175):
when every player has at most `m` pure strategies and degree at most `d` in a tree `M.graph`:
1. the LP has exactly `M.tableEntries ≤ |ι| * m ^ (d + 1)` variables (linear in `|ι|`, exponential
   only in `d + 1`);
2. there are at most `|ι| * m ^ 2` local CE incentive inequalities; and
3. there are at most `2 * (|ι| - 1) * m ^ 2` directed edge-consistency equations (which suffice for
   full intersection consistency on trees by
   `isIntersectionConsistent_iff_isEdgeConsistent_of_isTree`). -/
theorem GraphicalGame.treeLocalCE_size_bounds [DecidableEq ι] (M : GraphicalGame ι S)
    [DecidableRel M.graph.Adj] (hT : M.graph.IsTree) {m d : ℕ}
    (hm : ∀ i, Fintype.card (S i) ≤ m) (hd : ∀ i, M.graph.degree i ≤ d) :
    Fintype.card (Σ i : ι, ∀ j : ClosedNeighborhood M.graph i, S j.1) = M.tableEntries ∧
    M.tableEntries ≤ Fintype.card ι * m ^ (d + 1) ∧
    Fintype.card (Σ i : ι, S i × S i) ≤ Fintype.card ι * m ^ 2 ∧
    Fintype.card (Σ e : M.graph.Dart, S e.fst × S e.snd) ≤
      2 * (Fintype.card ι - 1) * m ^ 2 := by
  refine ⟨M.tableEntries_def.symm, M.tableEntries_le_card_mul_pow hm hd,
    card_sigma_prod_le hm id id, ?_⟩
  · have hcard_dart : Fintype.card M.graph.Dart = 2 * (Fintype.card ι - 1) := by
      rw [M.graph.dart_card_eq_twice_card_edges]
      have htree := hT.card_edgeFinset
      omega
    simpa only [hcard_dart] using card_sigma_prod_le hm (fun e : M.graph.Dart => e.fst)
      (fun e : M.graph.Dart => e.snd)

end TreeCETheorems

end TreeLocalCE

end Cslib.GameTheory
