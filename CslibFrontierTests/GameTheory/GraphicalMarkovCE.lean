/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Acyclic
public import CslibFrontier.GameTheory.Graphical.MarkovNetwork
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Local Markov networks and tree correlated equilibria tests

Ordinary `module` client tests (no `import all`) exercising
`CslibFrontier.GameTheory.Graphical.MarkovNetwork`:

1. **Checked `C₄` boundary counterexample and `ε`-approximate closure**:
   verifies `exists_ce_not_expectedPayoffEquiv_isLocalMarkovNetwork_cycle4` and
   `exists_not_localNeighborhoodEquiv_isLocalMarkovNetwork_cycle4` (exact `ε = 0` local Markov
   network representation fails on `C₄` at the weight-1 boundary CE), while applying
   `exists_isPositiveLocalMarkovNetwork_isApproxCorrelatedEquilibrium` to that exact same `C₄`
   game and CE at `ε = 1 / 100`.
2. **Positive-support Lemma 7.12 & Theorem 7.13 on a concrete correlated game (`P₃`)**:
   a strictly positive, non-product correlated equilibrium on the 3-player path `P₃` (`0 — 1 — 2`)
   lifted via maximum entropy (`exists_isPositiveLocalMarkovNetwork_ce_of_exists_pos`) to a
   strictly positive local Markov network CE preserving marginals and payoffs.
3. **Theorem 7.14 local-to-global tree CE lifting with zero probabilities and zero edge
   marginals (`P₃` Chicken-coordination game)**:
   explicitly specifies a locally normalized, edge-consistent solution `q` to Kearns's local CE LP
   on `P₃` with zero edge marginals on both `{0, 1}` (at `(true, true)`) and `{1, 2}` (at
   `(false, true)` and `(true, false)`), verifies `IsLocalCorrelatedEquilibrium`, lifts `q` via
   `exists_isCorrelatedEquilibrium_of_isLocalCorrelatedEquilibrium` to a global local Markov
   network CE achieving exact payoffs `(5, 5, 1)` and social welfare `11`, and checks
   `treeLocalCE_size_bounds`.
-/

@[expose] public section

namespace CslibFrontierTests.GameTheory.GraphicalMarkovCE

open Finset Function Cslib.GameTheory

/-! ### 1. `C₄` boundary counterexample vs `ε`-approximate Markov network closure -/

/-- Exact local Markov network representation fails on `C₄` at the Hamming-weight-1 boundary CE
(refuting literal Lemma 7.12 and Theorem 7.13), yet for `ε = 1 / 100` the same game and CE admit a
strictly positive local Markov network `(1 / 100)`-CE within `1 / 100` in payoffs and marginals. -/
theorem cycle4_boundary_refutation_and_approx_closure :
    (∃ σ : Convexity.StdSimplex ℝ (Fin 4 → Bool),
      ∀ τ, LocalNeighborhoodEquiv (SimpleGraph.cycleGraph 4) τ σ →
        ¬ IsLocalMarkovNetwork (SimpleGraph.cycleGraph 4) τ) ∧
    ∃ (M : GraphicalGame (Fin 4) (fun _ => Bool)) (σ : Convexity.StdSimplex ℝ (Fin 4 → Bool)),
      M.graph = SimpleGraph.cycleGraph 4 ∧
      M.toCostGame.IsCorrelatedEquilibrium σ ∧
      (∀ τ, M.ExpectedPayoffEquiv τ σ → ¬ IsLocalMarkovNetwork M.graph τ) ∧
      ∃ τ : Convexity.StdSimplex ℝ (Fin 4 → Bool),
        IsPositiveLocalMarkovNetwork M.graph τ ∧
        M.toCostGame.IsApproxCorrelatedEquilibrium (fun _ => 1 / 100) τ ∧
        (∀ i : Fin 4, |τ.weights.sum (fun s w => w * M.payoff i s) -
            σ.weights.sum (fun s w => w * M.payoff i s)| ≤ 1 / 100) := by
  refine ⟨exists_not_localNeighborhoodEquiv_isLocalMarkovNetwork_cycle4, ?_⟩
  obtain ⟨M, σ, hG, _, hce, huniq, hnot⟩ :=
    exists_ce_not_expectedPayoffEquiv_isLocalMarkovNetwork_cycle4
  obtain ⟨τ, hmk, happrox, hpay, _⟩ :=
    M.exists_isPositiveLocalMarkovNetwork_isApproxCorrelatedEquilibrium hce (ε := 1 / 100)
      (by norm_num)
  refine ⟨M, σ, hG, hce, fun ρ hEP hρ => hnot ?_, τ, hmk, happrox, hpay⟩
  rw [huniq ρ hEP] at hρ
  exact hG ▸ hρ

/-! ### 2. Three-player path tree `P₃` (`0 — 1 — 2`) -/

/-- Parent array for the 3-vertex path `0 — 1 — 2` rooted at `0`. -/
def path3Parent : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 0
  | 2 => 1

theorem path3Parent_lt : ∀ i : Fin 3, i ≠ 0 → path3Parent i < i := by
  intro i hi
  fin_cases i <;> simp [path3Parent] at hi ⊢

/-- Three-vertex path tree `P₃` (`0 — 1 — 2`) on `Fin 3`. -/
abbrev path3Graph : SimpleGraph (Fin 3) := SimpleGraph.parentTree path3Parent

instance : DecidableRel path3Graph.Adj := fun i j =>
  decidable_of_iff ((i ≠ 0 ∧ path3Parent i = j) ∨ (j ≠ 0 ∧ path3Parent j = i))
    (SimpleGraph.parentTree_adj path3Parent_lt).symm

theorem path3_isTree : path3Graph.IsTree :=
  SimpleGraph.parentTree_isTree path3Parent_lt

theorem path3_adj_01 : path3Graph.Adj 0 1 := by decide
theorem path3_adj_10 : path3Graph.Adj 1 0 := by decide
theorem path3_adj_12 : path3Graph.Adj 1 2 := by decide
theorem path3_adj_21 : path3Graph.Adj 2 1 := by decide

/-! #### 2a. Positive-support Lemma 7.12 & Theorem 7.13 on a correlated `P₃` game -/

/-- Coordination game on `P₃`: players `0` and `2` each earn `1` by matching hub `1`, while hub
`1` is indifferent (`0`). -/
abbrev path3CoordGame : GraphicalGame (Fin 3) (fun _ => Bool) where
  graph := path3Graph
  localPayoff i u :=
    match i with
    | 0 => if u ⟨0, Or.inl rfl⟩ == u ⟨1, Or.inr path3_adj_01⟩ then 1 else 0
    | 1 => 0
    | 2 => if u ⟨2, Or.inl rfl⟩ == u ⟨1, Or.inr path3_adj_21⟩ then 1 else 0

/-- Indicator of the two constant profiles `(false, false, false)` and `(true, true, true)`. -/
def isUniformProfile (s : Fin 3 → Bool) : Bool :=
  decide (s 0 = s 1 ∧ s 1 = s 2)

private theorem card_isUniformProfile :
    (univ.filter fun s : Fin 3 → Bool => isUniformProfile s = true).card = 2 := by
  decide

private theorem card_not_isUniformProfile :
    (univ.filter fun s : Fin 3 → Bool => isUniformProfile s = false).card = 6 := by
  decide

/-- Strictly positive correlated distribution on `Fin 3 → Bool`: weight `1 / 3` on `(F,F,F)` and
`(T,T,T)`, and weight `1 / 18` on each of the other 6 profiles. -/
noncomputable def path3PosDist : Convexity.StdSimplex ℝ (Fin 3 → Bool) where
  weights := Finsupp.equivFunOnFinite.symm fun s =>
    if isUniformProfile s then (1 / 3 : ℝ) else (1 / 18 : ℝ)
  nonneg s := by
    change 0 ≤ (if isUniformProfile s then (1 / 3 : ℝ) else (1 / 18 : ℝ))
    split_ifs <;> norm_num
  total := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    change ∑ s : Fin 3 → Bool, (if isUniformProfile s = true then (1 / 3 : ℝ) else 1 / 18) = 1
    have hsplit : ∑ s : Fin 3 → Bool, (if isUniformProfile s = true then (1 / 3 : ℝ) else 1 / 18) =
        (∑ s ∈ univ.filter (fun s : Fin 3 → Bool => isUniformProfile s = true), (1 / 3 : ℝ)) +
        (∑ s ∈ univ.filter (fun s : Fin 3 → Bool => isUniformProfile s = false), (1 / 18 : ℝ)) := by
      rw [← sum_filter_add_sum_filter_not univ (fun s : Fin 3 → Bool => isUniformProfile s = true)]
      refine congrArg₂ (· + ·) ?_ ?_
      · exact sum_congr rfl fun s hs => by simp [(mem_filter.mp hs).2]
      · refine sum_congr ?_ fun s hs => by simp [(mem_filter.mp hs).2]
        ext s
        simp
    rw [hsplit, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, card_isUniformProfile,
      card_not_isUniformProfile]
    norm_num

private def coordWeightNat (s : Fin 3 → Bool) : ℕ :=
  if isUniformProfile s then 6 else 1

private def coordPayoffNat (i : Fin 3) (s : Fin 3 → Bool) : ℕ :=
  match i with
  | 0 => if s 0 == s 1 then 1 else 0
  | 1 => 0
  | 2 => if s 2 == s 1 then 1 else 0

private theorem coordPayoffNat_ce :
    ∀ (i : Fin 3) (a b : Bool),
      (∑ s ∈ univ.filter (fun s : Fin 3 → Bool => s i = a),
          coordWeightNat s * coordPayoffNat i (update s i b)) ≤
        (∑ s ∈ univ.filter (fun s : Fin 3 → Bool => s i = a),
          coordWeightNat s * coordPayoffNat i s) := by
  decide

private theorem coordGame_payoff_eq_cast (i : Fin 3) (s : Fin 3 → Bool) :
    path3CoordGame.payoff i s = (coordPayoffNat i s : ℝ) := by
  fin_cases i <;> simp [path3CoordGame, coordPayoffNat]

private theorem path3PosDist_weights_eq (s : Fin 3 → Bool) :
    path3PosDist.weights s = (coordWeightNat s : ℝ) / 18 := by
  change (if isUniformProfile s then (1 / 3 : ℝ) else (1 / 18 : ℝ)) = (coordWeightNat s : ℝ) / 18
  dsimp [coordWeightNat]
  cases isUniformProfile s <;> norm_num

/-- **Positive-support Lemma 7.12 & Theorem 7.13 witness**: `path3PosDist` is a strictly positive
correlated equilibrium of `path3CoordGame`, and
`exists_isPositiveLocalMarkovNetwork_ce_of_exists_pos` yields a strictly positive local Markov
network CE `τ` on `P₃` with identical marginals and payoffs. -/
theorem path3CoordGame_positive_markov_ce :
    ∃ τ : Convexity.StdSimplex ℝ (Fin 3 → Bool),
      path3CoordGame.toCostGame.IsCorrelatedEquilibrium τ ∧
      path3CoordGame.ExpectedPayoffEquiv τ path3PosDist ∧
      LocalNeighborhoodEquiv path3Graph τ path3PosDist ∧
      IsPositiveLocalMarkovNetwork path3Graph τ ∧
      ∀ s : Fin 3 → Bool, 0 < τ.weights s := by
  have hpos : ∀ s : Fin 3 → Bool, 0 < path3PosDist.weights s := fun s => by
    rw [path3PosDist_weights_eq]
    have : 0 < coordWeightNat s := by dsimp [coordWeightNat]; split_ifs <;> omega
    positivity
  have hce : path3CoordGame.toCostGame.IsCorrelatedEquilibrium path3PosDist := by
    rw [CostGame.isCorrelatedEquilibrium_iff]
    intro i a b
    rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _),
      Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
    have hrew (f : (Fin 3 → Bool) → ℕ) :
        ∑ s : Fin 3 → Bool, path3PosDist.weights s * (if s i = a then -(f s : ℝ) else 0) =
          -((∑ s ∈ univ.filter (fun s : Fin 3 → Bool => s i = a),
              coordWeightNat s * f s : ℕ) : ℝ) / 18 := by
      simp only [path3PosDist_weights_eq, Nat.cast_sum, sum_filter, ← sum_neg_distrib,
        div_eq_mul_inv, sum_mul]
      refine sum_congr rfl fun s _ => ?_
      split_ifs <;> push_cast <;> ring
    simp only [GraphicalGame.toCostGame_cost, coordGame_payoff_eq_cast]
    rw [hrew (fun s => coordPayoffNat i s), hrew (fun s => coordPayoffNat i (update s i b))]
    have hnat : ((∑ s ∈ univ.filter (fun s : Fin 3 → Bool => s i = a),
          coordWeightNat s * coordPayoffNat i (update s i b) : ℕ) : ℝ) ≤
        ((∑ s ∈ univ.filter (fun s : Fin 3 → Bool => s i = a),
          coordWeightNat s * coordPayoffNat i s : ℕ) : ℝ) :=
      Nat.cast_le.mpr (coordPayoffNat_ce i a b)
    linarith
  obtain ⟨τ, hτ_ce, hEP, hln, hmk⟩ :=
    path3CoordGame.exists_isPositiveLocalMarkovNetwork_ce_of_exists_pos hce
      ⟨path3PosDist, fun _ _ => rfl, hpos⟩
  exact ⟨τ, hτ_ce, hEP, hln, hmk, hmk.weights_pos⟩

/-! #### 2b. Theorem 7.14 local-to-global CE lifting with zero edge marginals on `P₃` -/

/-- Classic Chicken payoff table on `Bool × Bool`: `(F,F) ↦ 6`, `(F,T) ↦ 2`, `(T,F) ↦ 7`,
`(T,T) ↦ 0` (`false` = Swerve, `true` = Dare). -/
def chickenPayoff (mine other : Bool) : ℝ :=
  match mine, other with
  | false, false => 6
  | false, true => 2
  | true, false => 7
  | true, true => 0

/-- Local payoff table of `path3ChickenGame`. -/
def path3ChickenLocalPayoff (i : Fin 3) (u : ClosedNeighborhood path3Graph i → Bool) : ℝ :=
  match i with
  | 0 => chickenPayoff (u ⟨0, Or.inl rfl⟩) (u ⟨1, Or.inr path3_adj_01⟩)
  | 1 => chickenPayoff (u ⟨1, Or.inl rfl⟩) (u ⟨0, Or.inr path3_adj_10⟩)
  | 2 => if u ⟨2, Or.inl rfl⟩ == u ⟨1, Or.inr path3_adj_21⟩ then 1 else 0

/-- Three-player tree graphical game on `P₃` (`0 — 1 — 2`):
* players `0` and `1` play symmetric Chicken across edge `{0, 1}`;
* player `2` earns `1` by matching player `1` across edge `{1, 2}`. -/
abbrev path3ChickenGame : GraphicalGame (Fin 3) (fun _ => Bool) where
  graph := path3Graph
  localPayoff := path3ChickenLocalPayoff

/-- Local neighborhood marginal family `q` on `P₃` with zero edge marginals (`(T,T)` on `{0,1}`
and `(F,T), (T,F)` on `{1,2}`):
* `q 0` on `{0, 1}`: `1/3` each on `(F,F), (F,T), (T,F)`, `0` on `(T,T)`;
* `q 1` on `{0, 1, 2}`: `1/3` each on `(F,F,F), (T,F,F), (F,T,T)`, `0` elsewhere;
* `q 2` on `{1, 2}`: `2/3` on `(F,F)`, `1/3` on `(T,T)`, `0` on `(F,T), (T,F)`. -/
noncomputable def path3ChickenLocalQ (i : Fin 3)
    (u : ClosedNeighborhood path3Graph i → Bool) : ℝ :=
  match i with
  | 0 =>
    if u ⟨0, Or.inl rfl⟩ && u ⟨1, Or.inr path3_adj_01⟩ then 0 else 1 / 3
  | 1 =>
    let a0 := u ⟨0, Or.inr path3_adj_10⟩
    let a1 := u ⟨1, Or.inl rfl⟩
    let a2 := u ⟨2, Or.inr path3_adj_12⟩
    if (!(a0 && a1)) && (a2 == a1) then 1 / 3 else 0
  | 2 =>
    match u ⟨1, Or.inr path3_adj_21⟩, u ⟨2, Or.inl rfl⟩ with
    | false, false => 2 / 3
    | true, true => 1 / 3
    | _, _ => 0

private def chickenLocalQNum (i : Fin 3) (u : ClosedNeighborhood path3Graph i → Bool) : ℕ :=
  match i with
  | 0 => if u ⟨0, Or.inl rfl⟩ && u ⟨1, Or.inr path3_adj_01⟩ then 0 else 1
  | 1 =>
    let a0 := u ⟨0, Or.inr path3_adj_10⟩
    let a1 := u ⟨1, Or.inl rfl⟩
    let a2 := u ⟨2, Or.inr path3_adj_12⟩
    if (!(a0 && a1)) && (a2 == a1) then 1 else 0
  | 2 =>
    match u ⟨1, Or.inr path3_adj_21⟩, u ⟨2, Or.inl rfl⟩ with
    | false, false => 2
    | true, true => 1
    | _, _ => 0

private def chickenPayoffNat (mine other : Bool) : ℕ :=
  match mine, other with
  | false, false => 6
  | false, true => 2
  | true, false => 7
  | true, true => 0

private def path3ChickenPayoffNat (i : Fin 3) (u : ClosedNeighborhood path3Graph i → Bool) : ℕ :=
  match i with
  | 0 => chickenPayoffNat (u ⟨0, Or.inl rfl⟩) (u ⟨1, Or.inr path3_adj_01⟩)
  | 1 => chickenPayoffNat (u ⟨1, Or.inl rfl⟩) (u ⟨0, Or.inr path3_adj_10⟩)
  | 2 => if u ⟨2, Or.inl rfl⟩ == u ⟨1, Or.inr path3_adj_21⟩ then 1 else 0

private theorem path3ChickenLocalQ_eq_div (i : Fin 3)
    (u : ClosedNeighborhood path3Graph i → Bool) :
    path3ChickenLocalQ i u = (chickenLocalQNum i u : ℝ) / 3 := by
  fin_cases i
  · dsimp [path3ChickenLocalQ, chickenLocalQNum]
    split_ifs <;> norm_num
  · dsimp [path3ChickenLocalQ, chickenLocalQNum]
    split_ifs <;> norm_num
  · dsimp [path3ChickenLocalQ, chickenLocalQNum]
    cases u ⟨1, Or.inr path3_adj_21⟩ <;> cases u ⟨2, Or.inl rfl⟩ <;> norm_num

private theorem path3ChickenPayoff_eq_cast (i : Fin 3)
    (u : ClosedNeighborhood path3Graph i → Bool) :
    path3ChickenLocalPayoff i u = (path3ChickenPayoffNat i u : ℝ) := by
  fin_cases i
  · dsimp [path3ChickenLocalPayoff, path3ChickenPayoffNat, chickenPayoff, chickenPayoffNat]
    cases u ⟨0, Or.inl rfl⟩ <;> cases u ⟨1, Or.inr path3_adj_01⟩ <;> norm_num
  · dsimp [path3ChickenLocalPayoff, path3ChickenPayoffNat, chickenPayoff, chickenPayoffNat]
    cases u ⟨1, Or.inl rfl⟩ <;> cases u ⟨0, Or.inr path3_adj_10⟩ <;> norm_num
  · dsimp [path3ChickenLocalPayoff, path3ChickenPayoffNat]
    split_ifs <;> norm_num

private theorem chickenLocalQ_sum_nat :
    ∀ i : Fin 3, (∑ u : ClosedNeighborhood path3Graph i → Bool, chickenLocalQNum i u) = 3 := by
  decide

private theorem chickenLocalQ_edge_nat :
    ∀ (i j : Fin 3) (hadj : path3Graph.Adj i j) (a b : Bool),
      (∑ u : ClosedNeighborhood path3Graph i → Bool,
          if u ⟨i, Or.inl rfl⟩ = a ∧ u ⟨j, Or.inr hadj⟩ = b then chickenLocalQNum i u else 0) =
        (∑ v : ClosedNeighborhood path3Graph j → Bool,
          if v ⟨j, Or.inl rfl⟩ = b ∧ v ⟨i, Or.inr hadj.symm⟩ = a
          then chickenLocalQNum j v else 0) := by
  decide

private theorem chickenLocalQ_ce_nat :
    ∀ (i : Fin 3) (a b : Bool),
      (∑ u : ClosedNeighborhood path3Graph i → Bool,
          if u ⟨i, Or.inl rfl⟩ = a then
            chickenLocalQNum i u * path3ChickenPayoffNat i (update u ⟨i, Or.inl rfl⟩ b)
          else 0) ≤
        (∑ u : ClosedNeighborhood path3Graph i → Bool,
          if u ⟨i, Or.inl rfl⟩ = a then
            chickenLocalQNum i u * path3ChickenPayoffNat i u
          else 0) := by
  decide

private theorem chickenLocalQ_payoff_nat :
    (∑ u : ClosedNeighborhood path3Graph 0 → Bool,
      chickenLocalQNum 0 u * path3ChickenPayoffNat 0 u) = 15 ∧
    (∑ u : ClosedNeighborhood path3Graph 1 → Bool,
      chickenLocalQNum 1 u * path3ChickenPayoffNat 1 u) = 15 ∧
    (∑ u : ClosedNeighborhood path3Graph 2 → Bool,
      chickenLocalQNum 2 u * path3ChickenPayoffNat 2 u) = 3 := by
  decide

/-- Check that `path3ChickenLocalQ` has vanishing edge marginals on both edges of `P₃`,
exercising the `0 / 0 = 0` branch of junction-tree lifting. -/
theorem chickenLocalQ_zero_edge_marginals :
    edgeMarginal (S := fun _ => Bool) path3Graph path3ChickenLocalQ 0 1 path3_adj_01 true true =
      0 ∧
    edgeMarginal (S := fun _ => Bool) path3Graph path3ChickenLocalQ 1 2 path3_adj_12 false true =
      0 ∧
    edgeMarginal (S := fun _ => Bool) path3Graph path3ChickenLocalQ 1 2 path3_adj_12 true false =
      0 := by
  have hzero : ∀ (i j : Fin 3) (hadj : path3Graph.Adj i j) (a b : Bool),
      (∑ u : ClosedNeighborhood path3Graph i → Bool,
        if u ⟨i, Or.inl rfl⟩ = a ∧ u ⟨j, Or.inr hadj⟩ = b then chickenLocalQNum i u else 0) = 0 →
      edgeMarginal (S := fun _ => Bool) path3Graph path3ChickenLocalQ i j hadj a b = 0 := by
    intro i j hadj a b hnat
    rw [edgeMarginal_def]
    have hrew : ∑ u : ClosedNeighborhood path3Graph i → Bool,
          (if u ⟨i, Or.inl rfl⟩ = a ∧ u ⟨j, Or.inr hadj⟩ = b then path3ChickenLocalQ i u else 0) =
        ((∑ u : ClosedNeighborhood path3Graph i → Bool,
          if u ⟨i, Or.inl rfl⟩ = a ∧ u ⟨j, Or.inr hadj⟩ = b then chickenLocalQNum i u else 0 : ℕ)
          : ℝ) / 3 := by
      simp only [path3ChickenLocalQ_eq_div, Nat.cast_sum, div_eq_mul_inv, sum_mul]
      exact sum_congr rfl fun u _ => by split_ifs <;> ring
    rw [hrew, hnat]
    norm_num
  exact ⟨hzero 0 1 path3_adj_01 true true (by decide),
    hzero 1 2 path3_adj_12 false true (by decide),
    hzero 1 2 path3_adj_12 true false (by decide)⟩

/-- **Theorem 7.14 witness with zero edge marginals**: `path3ChickenLocalQ` satisfies Kearns's local
CE linear program `IsLocalCorrelatedEquilibrium` on `P₃` (with vanishing edge marginals on both
edges), lifts to a global correlated equilibrium `σ` represented as a nonnegative local Markov
network on `P₃` achieving exact expected payoffs `(5, 5, 1)` and social welfare `11`, and obeys the
polynomial LP variable and constraint bounds (`tableEntries = 16 ≤ 24`). -/
theorem path3ChickenGame_theorem714_lift :
    path3ChickenGame.IsLocalCorrelatedEquilibrium path3ChickenLocalQ ∧
    (∃ σ : Convexity.StdSimplex ℝ (Fin 3 → Bool),
      path3ChickenGame.toCostGame.IsCorrelatedEquilibrium σ ∧
      IsLocalMarkovNetwork path3Graph σ ∧
      (∀ i u, neighborhoodMarginal path3Graph σ i u = path3ChickenLocalQ i u) ∧
      σ.weights.sum (fun s w => w * path3ChickenGame.payoff 0 s) = 5 ∧
      σ.weights.sum (fun s w => w * path3ChickenGame.payoff 1 s) = 5 ∧
      σ.weights.sum (fun s w => w * path3ChickenGame.payoff 2 s) = 1 ∧
      ∑ i : Fin 3, σ.weights.sum (fun s w => w * path3ChickenGame.payoff i s) = 11) ∧
    (path3ChickenGame.tableEntries = 16 ∧
      path3ChickenGame.tableEntries ≤ Fintype.card (Fin 3) * 2 ^ (2 + 1) ∧
      Fintype.card (Σ _ : Fin 3, Bool × Bool) ≤ Fintype.card (Fin 3) * 2 ^ 2 ∧
      Fintype.card (Σ _ : path3Graph.Dart, Bool × Bool) ≤
        2 * (Fintype.card (Fin 3) - 1) * 2 ^ 2) := by
  have hloc : IsLocalDistribution (S := fun _ => Bool) path3Graph path3ChickenLocalQ := by
    intro i
    refine ⟨fun u => by rw [path3ChickenLocalQ_eq_div]; positivity, ?_⟩
    have hsum : ∑ u : ClosedNeighborhood path3Graph i → Bool, path3ChickenLocalQ i u = 1 := by
      simp only [path3ChickenLocalQ_eq_div, div_eq_mul_inv, ← sum_mul, ← Nat.cast_sum,
        chickenLocalQ_sum_nat i]
      norm_num
    convert hsum
  have hedge : IsEdgeConsistent (S := fun _ => Bool) path3Graph path3ChickenLocalQ := by
    intro i j hadj a b
    rw [edgeMarginal_def, edgeMarginal_def]
    have hrew (x y : Fin 3) (hxy : path3Graph.Adj x y) (ax by_ : Bool) :
        ∑ u : ClosedNeighborhood path3Graph x → Bool,
          (if u ⟨x, Or.inl rfl⟩ = ax ∧ u ⟨y, Or.inr hxy⟩ = by_ then path3ChickenLocalQ x u else 0) =
        ((∑ u : ClosedNeighborhood path3Graph x → Bool,
          if u ⟨x, Or.inl rfl⟩ = ax ∧ u ⟨y, Or.inr hxy⟩ = by_ then chickenLocalQNum x u else 0 : ℕ)
          : ℝ) / 3 := by
      simp only [path3ChickenLocalQ_eq_div, Nat.cast_sum, div_eq_mul_inv, sum_mul]
      exact sum_congr rfl fun u _ => by split_ifs <;> ring
    rw [hrew i j hadj a b, hrew j i hadj.symm b a, chickenLocalQ_edge_nat i j hadj a b]
  have hint : IsIntersectionConsistent (S := fun _ => Bool) path3Graph path3ChickenLocalQ :=
    (isIntersectionConsistent_iff_isEdgeConsistent_of_isTree path3_isTree hloc).mpr hedge
  have hsat : path3ChickenGame.SatisfiesLocalCE path3ChickenLocalQ := by
    intro i a b
    have hrew (f : (ClosedNeighborhood path3Graph i → Bool) → ℕ) :
        ∑ u : ClosedNeighborhood path3Graph i → Bool,
          (if u ⟨i, Or.inl rfl⟩ = a then path3ChickenLocalQ i u * (f u : ℝ) else 0) =
        ((∑ u : ClosedNeighborhood path3Graph i → Bool,
          if u ⟨i, Or.inl rfl⟩ = a then chickenLocalQNum i u * f u else 0 : ℕ) : ℝ) / 3 := by
      simp only [path3ChickenLocalQ_eq_div, Nat.cast_sum, div_eq_mul_inv, sum_mul]
      exact sum_congr rfl fun u _ => by split_ifs <;> push_cast <;> ring
    have hle : (∑ u : ClosedNeighborhood path3Graph i → Bool,
          if u ⟨i, Or.inl rfl⟩ = a then
            path3ChickenLocalQ i u * path3ChickenGame.localPayoff i (update u ⟨i, Or.inl rfl⟩ b)
          else 0) ≤
        ∑ u : ClosedNeighborhood path3Graph i → Bool,
          if u ⟨i, Or.inl rfl⟩ = a then
            path3ChickenLocalQ i u * path3ChickenGame.localPayoff i u
          else 0 := by
      simp only [path3ChickenPayoff_eq_cast]
      rw [hrew (fun u => path3ChickenPayoffNat i (update u ⟨i, Or.inl rfl⟩ b)),
        hrew (fun u => path3ChickenPayoffNat i u)]
      have hnat : ((∑ u : ClosedNeighborhood path3Graph i → Bool,
            if u ⟨i, Or.inl rfl⟩ = a then
              chickenLocalQNum i u * path3ChickenPayoffNat i (update u ⟨i, Or.inl rfl⟩ b)
            else 0 : ℕ) : ℝ) ≤
          ((∑ u : ClosedNeighborhood path3Graph i → Bool,
            if u ⟨i, Or.inl rfl⟩ = a then
              chickenLocalQNum i u * path3ChickenPayoffNat i u
            else 0 : ℕ) : ℝ) :=
        Nat.cast_le.mpr (chickenLocalQ_ce_nat i a b)
      linarith
    convert hle
  have hlce : path3ChickenGame.IsLocalCorrelatedEquilibrium path3ChickenLocalQ :=
    ⟨hsat, hloc, hint⟩
  obtain ⟨σ, hσ_ce, hmk, hmarg, hpay, _⟩ :=
    path3ChickenGame.exists_isCorrelatedEquilibrium_of_isLocalCorrelatedEquilibrium
      path3_isTree hlce
  have hpay_val (i : Fin 3) :
      σ.weights.sum (fun s w => w * path3ChickenGame.payoff i s) =
        ((∑ u : ClosedNeighborhood path3Graph i → Bool,
          chickenLocalQNum i u * path3ChickenPayoffNat i u : ℕ) : ℝ) / 3 := by
    have hi := hpay i
    have hlocal : (∑ u : ClosedNeighborhood path3Graph i → Bool,
          path3ChickenLocalQ i u * path3ChickenGame.localPayoff i u) =
        ((∑ u : ClosedNeighborhood path3Graph i → Bool,
          chickenLocalQNum i u * path3ChickenPayoffNat i u : ℕ) : ℝ) / 3 := by
      simp only [path3ChickenLocalQ_eq_div, path3ChickenPayoff_eq_cast, Nat.cast_sum,
        div_eq_mul_inv, sum_mul]
      exact sum_congr rfl fun u _ => by push_cast; ring
    rw [← hlocal]
    convert hi
  have hp0 : σ.weights.sum (fun s w => w * path3ChickenGame.payoff 0 s) = 5 := by
    rw [hpay_val 0, chickenLocalQ_payoff_nat.1]; norm_num
  have hp1 : σ.weights.sum (fun s w => w * path3ChickenGame.payoff 1 s) = 5 := by
    rw [hpay_val 1, chickenLocalQ_payoff_nat.2.1]; norm_num
  have hp2 : σ.weights.sum (fun s w => w * path3ChickenGame.payoff 2 s) = 1 := by
    rw [hpay_val 2, chickenLocalQ_payoff_nat.2.2]; norm_num
  have hsw : ∑ i : Fin 3, σ.weights.sum (fun s w => w * path3ChickenGame.payoff i s) = 11 := by
    rw [Fin.sum_univ_three, hp0, hp1, hp2]; norm_num
  have hbounds := path3ChickenGame.treeLocalCE_size_bounds path3_isTree (m := 2) (d := 2)
    (fun _ => by simp) (fun i => by fin_cases i <;> decide)
  have hentries : path3ChickenGame.tableEntries = 16 := by
    rw [path3ChickenGame.tableEntries_eq_sum_prod]; decide
  exact ⟨hlce, ⟨σ, hσ_ce, hmk, hmarg, hp0, hp1, hp2, hsw⟩,
    ⟨hentries, hbounds.2.1, hbounds.2.2.1, hbounds.2.2.2⟩⟩

/-- Direct client evaluation of `restrictMarginal` via `restrictMarginal_def` in an ordinary
`module` (checking the `{1}` marginal of `path3ChickenLocalQ 0` and `path3ChickenLocalQ 2` at
`true` both equal `1 / 3`). -/
theorem path3ChickenLocalQ_restrictMarginal_eval :
    restrictMarginal (S := fun _ => Bool) path3Graph path3ChickenLocalQ 0 ({1} : Set (Fin 3))
      (fun _ hk => Or.inr (hk.symm ▸ path3_adj_01)) (fun _ => true) = 1 / 3 ∧
    restrictMarginal (S := fun _ => Bool) path3Graph path3ChickenLocalQ 2 ({1} : Set (Fin 3))
      (fun _ hk => Or.inr (hk.symm ▸ path3_adj_21)) (fun _ => true) = 1 / 3 := by
  have heval : ∀ (i : Fin 3) (hT : ∀ k ∈ ({1} : Set (Fin 3)), k = i ∨ path3Graph.Adj i k),
      (∑ u : ClosedNeighborhood path3Graph i → Bool,
        if (fun k : ({1} : Set (Fin 3)) => u ⟨k.val, hT k.val k.property⟩) = (fun _ => true) then
          chickenLocalQNum i u else 0) = 1 →
      restrictMarginal (S := fun _ => Bool) path3Graph path3ChickenLocalQ i ({1} : Set (Fin 3))
        hT (fun _ => true) = 1 / 3 := by
    intro i hT hnat
    rw [restrictMarginal_def]
    have hrew : ∑ u : ClosedNeighborhood path3Graph i → Bool,
          (if (fun k : ({1} : Set (Fin 3)) => u ⟨k.val, hT k.val k.property⟩) = (fun _ => true) then
            path3ChickenLocalQ i u else 0) =
        ((∑ u : ClosedNeighborhood path3Graph i → Bool,
          if (fun k : ({1} : Set (Fin 3)) => u ⟨k.val, hT k.val k.property⟩) = (fun _ => true) then
            chickenLocalQNum i u else 0 : ℕ) : ℝ) / 3 := by
      simp only [path3ChickenLocalQ_eq_div, Nat.cast_sum, div_eq_mul_inv, sum_mul]
      exact sum_congr rfl fun u _ => by split_ifs <;> ring
    rw [hrew, hnat]
    norm_num
  exact ⟨heval 0 _ (by decide), heval 2 _ (by decide)⟩

end CslibFrontierTests.GameTheory.GraphicalMarkovCE
