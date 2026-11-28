/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.GameTheory.Graphical.TreeNash
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Graphical games and `TreeNash` tests

Concrete witnesses and counterexamples exercising `CslibFrontier.GameTheory.Graphical.Basic` and
`CslibFrontier.GameTheory.Graphical.TreeNash` as an ordinary `module` client:

1. **4-player path tree `P₄` (`0 — 1 — 2 — 3`)**: succinct representation count
   (`tableEntries = 24 < 64 = normalFormEntries`), asymmetric downstream best-response propagation
   uniquely pinning down the exact equilibrium `(false, false, true, true)`, positive and negative
   `treeNashRootTable` checks, and `treeNash` output verification.
2. **Disconnected 2-component forest (`{0, 1}` + `{2, 3}`)**: `IsAcyclic` without `IsTree`,
   verified with `acyclicNash_isMixedNash`.
3. **Off-grid mixed Nash equilibrium and Lemma 7.4 (`τ`-grid rounding)**: asymmetric 2-player tree
   game whose exact equilibrium plays `false` with probability `1 / 3` (`∉ binaryTauGrid 2`),
   rounded to `1 / 2` on `binaryTauGrid 2` (`τ = 1 / 2`) to give a checked `(1 / 2)`-approximate
   Nash equilibrium that is *not* an exact Nash equilibrium, together with `ApproximateTreeNash`.
4. **Local neighborhood equivalence (Lemmas 7.9 & 7.10)**: correlated vs anti-correlated pairs on
   the edgeless 2-player graph `⊥` (`σ ≠ τ` with `LocalNeighborhoodEquiv ⊥ σ τ`, preserving
   expected payoffs and correlated equilibria) vs separation on `⊤`.
5. **Cyclic counterexamples on `C₄` (`0 — 1 — 2 — 3 — 0`)**:
   * *Naive spanning-tree `TreeNash` failure*: dropping back-edge `{3, 0}` yields a tree `P₄` on
     which `TreeNash` accepts `(true, true, true, true)`, whereas on the cyclic `C₄` game player `3`
     gains `+1` by deviating to `false` (and `C₄` has no pure Nash equilibrium at all).
   * *Pairwise `NashProp` branch-table inconsistency* ([Kearns2007], §7.3.3, p. 169): along both
     branches `0 — 1 — 2` and `0 — 3 — 2` of `C₄`, `(p_0 = pure true, p_1 = pure true)` and
     `(p_0 = pure true, p_3 = pure true)` extend locally to branch best responses (requiring
     `p_2 true ≥ 2 / 3` and `p_2 false ≥ 2 / 3`, respectively), yet no global mixed Nash equilibrium
     of the `C₄` game can realize both simultaneously.
-/

@[expose] public section

namespace CslibFrontierTests.GameTheory.Graphical

open Finset Function Cslib.GameTheory

/-! ### 1. Four-player path tree `P₄` (`0 — 1 — 2 — 3`) -/

/-- Parent array for the 4-vertex path `0 — 1 — 2 — 3` rooted at `0`. -/
def path4Parent : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2

theorem path4Parent_lt : ∀ i : Fin 4, i ≠ 0 → path4Parent i < i := by
  intro i hi
  fin_cases i <;> simp [path4Parent] at hi ⊢

/-- Path tree `P₄` on `Fin 4`. -/
abbrev path4Graph : SimpleGraph (Fin 4) := SimpleGraph.parentTree path4Parent

instance : DecidableRel path4Graph.Adj := fun i j =>
  decidable_of_iff ((i ≠ 0 ∧ path4Parent i = j) ∨ (j ≠ 0 ∧ path4Parent j = i))
    (SimpleGraph.parentTree_adj path4Parent_lt).symm

theorem path4_isTree : path4Graph.IsTree :=
  SimpleGraph.parentTree_isTree path4Parent_lt

theorem path4_adj_01 : path4Graph.Adj 0 1 := by decide
theorem path4_adj_12 : path4Graph.Adj 1 2 := by decide
theorem path4_adj_23 : path4Graph.Adj 2 3 := by decide

private theorem path4_not_top : path4Graph ≠ ⊤ := by
  intro h
  have hadj : path4Graph.Adj 0 3 := by simp [h]
  revert hadj
  decide

/-- Asymmetric graphical game on `P₄`:
* leaf `3` strictly prefers `true`;
* vertex `2` prefers matching `3`;
* vertex `1` prefers opposing `2`;
* root `0` prefers matching `1`. -/
abbrev path4Game : GraphicalGame (Fin 4) (fun _ => Bool) where
  graph := path4Graph
  localPayoff i u :=
    match i with
    | 0 => if u ⟨0, Or.inl rfl⟩ == u ⟨1, Or.inr path4_adj_01⟩ then 1 else 0
    | 1 => if u ⟨1, Or.inl rfl⟩ != u ⟨2, Or.inr path4_adj_12⟩ then 1 else 0
    | 2 => if u ⟨2, Or.inl rfl⟩ == u ⟨3, Or.inr path4_adj_23⟩ then 1 else 0
    | 3 => if u ⟨3, Or.inl rfl⟩ then 1 else 0

/-- Exact parameter count on `P₄`: `4 + 8 + 8 + 4 = 24`, strictly less than `4 * 2^4 = 64` in
normal form. -/
theorem path4Game_tableEntries :
    path4Game.tableEntries = 24 ∧
      CostGame.normalFormEntries (Fin 4) (fun _ => Bool) = 64 ∧
      path4Game.tableEntries < CostGame.normalFormEntries (Fin 4) (fun _ => Bool) := by
  refine ⟨?_, ?_, path4Game.tableEntries_lt_normalFormEntries path4_not_top fun _ => by simp⟩
  · rw [path4Game.tableEntries_eq_sum_prod]
    decide
  · rw [CostGame.normalFormEntries_const]
    decide

/-- Degree-bounded parameter inequality `24 ≤ 4 * 2^(2 + 1) = 32` on `P₄`. -/
example : path4Game.tableEntries ≤ Fintype.card (Fin 4) * 2 ^ (2 + 1) :=
  path4Game.tableEntries_le_card_mul_pow (m := 2) (d := 2)
    (fun _ => by simp) (fun i => by fin_cases i <;> decide)

/-- Unique equilibrium pure action profile `(false, false, true, true)` of `path4Game`. -/
def path4EqActions : Fin 4 → Bool
  | 0 => false
  | 1 => false
  | 2 => true
  | 3 => true

theorem path4Game_isPureNash : path4Game.toCostGame.IsPureNash path4EqActions := by
  intro i a
  fin_cases i <;> cases a <;> simp [path4Game, path4EqActions, update]

/-- Every mixed Nash equilibrium of `path4Game` equals the point-mass profile on
`path4EqActions`, forced sequentially from leaf `3` down to root `0`. -/
theorem path4Game_unique_isMixedNash {p : Fin 4 → Bool → ℝ}
    (hp : path4Game.toCostGame.IsMixedNash p) :
    p = fun i => Pi.single (path4EqActions i) 1 := by
  have hsum_pw : ∑ s : Fin 4 → Bool, productWeight p s = 1 :=
    sum_productWeight (fun i => (hp.1 i).sum_eq_one)
  have hforce : ∀ (i : Fin 4) (b : Bool),
      path4Game.deviationPayoff p i (!b) < path4Game.deviationPayoff p i b →
        p i = Pi.single b 1 := by
    intro i b hstrict
    have h0 : p i (!b) = 0 := by
      by_contra hne
      have hpos : 0 < p i (!b) := lt_of_le_of_ne ((hp.1 i).nonneg (!b)) (Ne.symm hne)
      have heq := hp.deviationCost_eq_of_pos i hpos
      have hle := hp.2 i b
      simp only [GraphicalGame.toCostGame_deviationCost,
        GraphicalGame.toCostGame_expectedCost] at heq hle
      linarith
    have hsum := (hp.1 i).sum_eq_one
    simp only [Fintype.sum_bool] at hsum
    ext c
    cases b <;> cases c <;> simp only [Bool.not_true, Bool.not_false] at h0 <;>
      simp <;> linarith
  -- Step 1: Leaf `3` strictly prefers `true`.
  have hp3 : p 3 = Pi.single true 1 := by
    refine hforce 3 true ?_
    simp only [Bool.not_true]
    rw [path4Game.deviationPayoff_def, path4Game.deviationPayoff_def]
    have h0 : ∀ s : Fin 4 → Bool, path4Game.payoff 3 (update s 3 false) = 0 :=
      fun _ => by simp [path4Game]
    have h1 : ∀ s : Fin 4 → Bool, path4Game.payoff 3 (update s 3 true) = 1 :=
      fun _ => by simp [path4Game]
    simp only [h0, h1, mul_zero, mul_one, sum_const_zero, hsum_pw]
    norm_num
  -- Step 2: Given `p 3 = single true 1`, player `2` gets `1` from `true` and `0` from `false`.
  have hp2 : p 2 = Pi.single true 1 := by
    refine hforce 2 true ?_
    have hdev : ∀ b : Bool, path4Game.deviationPayoff p 2 b = if b then 1 else 0 := by
      intro b
      rw [path4Game.deviationPayoff_def]
      have hterm : ∀ s : Fin 4 → Bool,
          productWeight p s * path4Game.payoff 2 (update s 2 b) =
            productWeight p s * (if b then 1 else 0) := by
        intro s
        by_cases hs3 : s 3 = false
        · have hw0 : productWeight p s = 0 := by
            rw [productWeight_def]
            exact prod_eq_zero (mem_univ 3) (by simp [hs3, hp3])
          rw [hw0, zero_mul, zero_mul]
        · have hs3_t : s 3 = true := Bool.eq_true_of_not_eq_false hs3
          cases b <;> simp [path4Game, hs3_t]
      simp only [hterm, ← sum_mul, hsum_pw, one_mul]
    simp [hdev]
  -- Step 3: Given `p 2 = single true 1`, player `1` gets `1` from `false` and `0` from `true`.
  have hp1 : p 1 = Pi.single false 1 := by
    refine hforce 1 false ?_
    have hdev : ∀ b : Bool, path4Game.deviationPayoff p 1 b = if !b then 1 else 0 := by
      intro b
      rw [path4Game.deviationPayoff_def]
      have hterm : ∀ s : Fin 4 → Bool,
          productWeight p s * path4Game.payoff 1 (update s 1 b) =
            productWeight p s * (if !b then 1 else 0) := by
        intro s
        by_cases hs2 : s 2 = false
        · have hw0 : productWeight p s = 0 := by
            rw [productWeight_def]
            exact prod_eq_zero (mem_univ 2) (by simp [hs2, hp2])
          rw [hw0, zero_mul, zero_mul]
        · have hs2_t : s 2 = true := Bool.eq_true_of_not_eq_false hs2
          cases b <;> simp [path4Game, hs2_t]
      simp only [hterm, ← sum_mul, hsum_pw, one_mul]
    simp [hdev]
  -- Step 4: Given `p 1 = single false 1`, root `0` gets `1` from `false` and `0` from `true`.
  have hp0 : p 0 = Pi.single false 1 := by
    refine hforce 0 false ?_
    have hdev : ∀ b : Bool, path4Game.deviationPayoff p 0 b = if !b then 1 else 0 := by
      intro b
      rw [path4Game.deviationPayoff_def]
      have hterm : ∀ s : Fin 4 → Bool,
          productWeight p s * path4Game.payoff 0 (update s 0 b) =
            productWeight p s * (if !b then 1 else 0) := by
        intro s
        by_cases hs1 : s 1 = true
        · have hw0 : productWeight p s = 0 := by
            rw [productWeight_def]
            exact prod_eq_zero (mem_univ 1) (by simp [hs1, hp1])
          rw [hw0, zero_mul, zero_mul]
        · have hs1_f : s 1 = false := Bool.eq_false_of_not_eq_true hs1
          cases b <;> simp [path4Game, hs1_f]
      simp only [hterm, ← sum_mul, hsum_pw, one_mul]
    simp [hdev]
  ext i b
  fin_cases i
  · simp [hp0, path4EqActions]
  · simp [hp1, path4EqActions]
  · simp [hp2, path4EqActions]
  · simp [hp3, path4EqActions]

/-- Two-pass `treeNash` on `path4Game` outputs the exact unique equilibrium profile
`(false, false, true, true)`, and `treeNashRootTable` accepts `false` while rejecting `true`. -/
theorem path4Game_treeNash_eq :
    path4Game.treeNash path4_isTree 0 = (fun i => Pi.single (path4EqActions i) 1) ∧
      path4Game.treeNashRootTable path4_isTree 0 (Pi.single false 1) ∧
      ¬ path4Game.treeNashRootTable path4_isTree 0 (Pi.single true 1) := by
  refine ⟨path4Game_unique_isMixedNash (path4Game.treeNash_isMixedNash path4_isTree 0), ?_, ?_⟩
  · unfold GraphicalGame.treeNashRootTable
    rw [GraphicalGame.rootPassTable_iff_exists_isApproxNash]
    exact ⟨fun i => Pi.single (path4EqActions i) 1, rfl,
      fun _ => isMixedStrategy_single _,
      path4Game.isApproxNash_zero_iff.mpr path4Game_isPureNash.isMixedNash⟩
  · unfold GraphicalGame.treeNashRootTable
    rw [GraphicalGame.rootPassTable_iff_exists_isApproxNash]
    rintro ⟨q, hq0, _, hq_nash⟩
    have hq_eq := path4Game_unique_isMixedNash (path4Game.isApproxNash_zero_iff.mp hq_nash)
    have h0 := congrFun (hq0.symm.trans (congrFun hq_eq 0)) true
    simp [path4EqActions] at h0

/-! ### 2. Disconnected forest (`{0, 1}` + `{2, 3}`): `IsAcyclic` without `IsTree` -/

/-- Two-edge matching `{0, 1} ∪ {2, 3}` on `Fin 4`: a subgraph of `path4Graph`, hence acyclic,
but disconnected (not a tree). -/
def forestGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun i j => (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2)

private theorem forestGraph_le_path4 : forestGraph ≤ path4Graph := by
  intro i j hadj
  fin_cases i <;> fin_cases j <;> simp [forestGraph, SimpleGraph.fromRel_adj] at hadj <;> decide

theorem forestGraph_isAcyclic : forestGraph.IsAcyclic := by
  intro v c hc
  let f : forestGraph →g path4Graph := ⟨id, fun hadj => forestGraph_le_path4 hadj⟩
  exact path4_isTree.isAcyclic _ (hc.map (f := f) Function.injective_id)

theorem forestGraph_not_isTree : ¬ forestGraph.IsTree := by
  rintro ⟨hconn, _⟩
  obtain ⟨w⟩ := hconn 0 2
  have hstay : ∀ {u v : Fin 4} (p : forestGraph.Walk u v),
      (u = 0 ∨ u = 1) → (v = 0 ∨ v = 1) := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons a b c hadj _ ih =>
      intro ha
      apply ih
      fin_cases a <;> fin_cases b <;>
        simp [forestGraph, SimpleGraph.fromRel_adj] at hadj ha ⊢
  rcases hstay w (Or.inl rfl) with h | h <;> revert h <;> decide

/-- Dominance-solvable binary graphical game on the 2-component disconnected forest
`forestGraph`. -/
def forestGame : GraphicalGame (Fin 4) (fun _ => Bool) where
  graph := forestGraph
  localPayoff i u := if u ⟨i, Or.inl rfl⟩ then 1 else 0

example : forestGame.toCostGame.IsMixedNash (forestGame.acyclicNash forestGraph_isAcyclic) :=
  forestGame.acyclicNash_isMixedNash forestGraph_isAcyclic

/-! ### 3. Off-grid mixed Nash equilibrium, Lemma 7.4, and `ApproximateTreeNash` -/

/-- Parent map for the two-player tree `0 — 1` on `Fin 2`. -/
def edge2Parent : Fin 2 → Fin 2 := fun _ => 0

theorem edge2Parent_lt : ∀ i : Fin 2, i ≠ 0 → edge2Parent i < i := by
  intro i hi
  fin_cases i <;> simp [edge2Parent] at hi ⊢

/-- Two-player tree `0 — 1` on `Fin 2`. -/
abbrev edge2Graph : SimpleGraph (Fin 2) := SimpleGraph.parentTree edge2Parent

instance : DecidableRel edge2Graph.Adj := fun i j =>
  decidable_of_iff ((i ≠ 0 ∧ edge2Parent i = j) ∨ (j ≠ 0 ∧ edge2Parent j = i))
    (SimpleGraph.parentTree_adj edge2Parent_lt).symm

theorem edge2_isTree : edge2Graph.IsTree :=
  SimpleGraph.parentTree_isTree edge2Parent_lt

theorem edge2_adj_01 : edge2Graph.Adj 0 1 := by decide
theorem edge2_adj_10 : edge2Graph.Adj 1 0 := by decide

/-- Asymmetric `[0, 1]`-payoff game on the 1-edge tree `0 — 1` whose mixed Nash equilibrium plays
`false` with probability `1 / 3` and `true` with probability `2 / 3`:
* player `0`: `(false, false) ↦ 1`, `(true, true) ↦ 1 / 2`, otherwise `0`;
* player `1`: `(true, false) ↦ 1 / 2`, `(false, true) ↦ 1`, otherwise `0`. -/
noncomputable abbrev thirdTreeGame : GraphicalGame (Fin 2) (fun _ => Bool) where
  graph := edge2Graph
  localPayoff i u :=
    match i with
    | 0 =>
      if u ⟨0, Or.inl rfl⟩ then
        if u ⟨1, Or.inr edge2_adj_01⟩ then 1 / 2 else 0
      else
        if u ⟨1, Or.inr edge2_adj_01⟩ then 0 else 1
    | 1 =>
      if u ⟨1, Or.inl rfl⟩ then
        if u ⟨0, Or.inr edge2_adj_10⟩ then 0 else 1
      else
        if u ⟨0, Or.inr edge2_adj_10⟩ then 1 / 2 else 0

/-- Off-grid mixed strategy profile playing `false` with probability `1 / 3` and `true` with
probability `2 / 3`. -/
noncomputable def thirdProfile : Fin 2 → Bool → ℝ :=
  fun _ b => if b then 2 / 3 else 1 / 3

theorem thirdTreeGame_payoff_bounds (i : Fin 2)
    (u : ClosedNeighborhood thirdTreeGame.graph i → Bool) :
    0 ≤ thirdTreeGame.localPayoff i u ∧ thirdTreeGame.localPayoff i u ≤ 1 := by
  fin_cases i
  · dsimp [thirdTreeGame]
    split_ifs <;> norm_num
  · dsimp [thirdTreeGame]
    split_ifs <;> norm_num

theorem thirdTreeGame_degree_le : ∀ i : Fin 2, thirdTreeGame.graph.degree i ≤ 1 := by
  intro i
  fin_cases i <;> decide

private theorem sum_fin2_bool (f : (Fin 2 → Bool) → ℝ) :
    ∑ s : Fin 2 → Bool, f s =
      f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  have huniv : (univ : Finset (Fin 2 → Bool)) =
      {![false, false], ![false, true], ![true, false], ![true, true]} := by
    ext s
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    cases hs0 : s 0 <;> cases hs1 : s 1
    · left; ext k; fin_cases k <;> simp [hs0, hs1]
    · right; left; ext k; fin_cases k <;> simp [hs0, hs1]
    · right; right; left; ext k; fin_cases k <;> simp [hs0, hs1]
    · right; right; right; ext k; fin_cases k <;> simp [hs0, hs1]
  rw [huniv, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  ring

/-- `thirdProfile` (`p i false = 1 / 3, p i true = 2 / 3`) is an exact mixed Nash equilibrium of
`thirdTreeGame`, and does not lie on `binaryTauGrid 2`. -/
theorem thirdTreeGame_isMixedNash_thirdProfile :
    thirdTreeGame.toCostGame.IsMixedNash thirdProfile ∧
      thirdProfile 0 ∉ GraphicalGame.binaryTauGrid 2 := by
  have hmix : ∀ i : Fin 2, IsMixedStrategy (thirdProfile i) := fun _ =>
    isMixedStrategy_iff.mpr ⟨fun b => by cases b <;> norm_num [thirdProfile], by
      rw [Fintype.sum_bool]
      norm_num [thirdProfile]⟩
  refine ⟨⟨hmix, fun i a => ?_⟩, ?_⟩
  · simp only [GraphicalGame.toCostGame_expectedCost, GraphicalGame.toCostGame_deviationCost,
      GraphicalGame.expectedPayoff_def, GraphicalGame.deviationPayoff_def, sum_fin2_bool,
      productWeight_def, Fin.prod_univ_two]
    fin_cases i <;> cases a <;>
      simp [thirdTreeGame, thirdProfile, update] <;> norm_num
  · rintro ⟨_, k, hk_le, hk_eq⟩
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl | rfl <;> norm_num [thirdProfile] at hk_eq

/-- **Lemma 7.4 witness**: rounding `thirdProfile` to `binaryTauGrid 2` (`m = 2`, `τ = 1 / 2`)
maps `1 / 3 ↦ 1 / 2`, producing a `(1 / 2)`-approximate Nash equilibrium that is *not* an exact
Nash equilibrium (`0` gains `1 / 2 - 3 / 8 = 1 / 8 > 0` by deviating to `false`). -/
theorem thirdTreeGame_rounded_approx_not_exact :
    let q := fun i : Fin 2 => GraphicalGame.nearestGridStrategy 2 (thirdProfile i)
    (∀ i, q i false = 1 / 2 ∧ q i true = 1 / 2) ∧
      thirdTreeGame.IsApproxNash ((1 : ℝ) * (1 / (2 : ℝ))) q ∧
      ¬ thirdTreeGame.toCostGame.IsMixedNash q := by
  intro q
  have hfl : ⌊(7 / 6 : ℝ)⌋₊ = 1 := by
    have hge : 1 ≤ ⌊(7 / 6 : ℝ)⌋₊ := Nat.le_floor (by norm_num)
    have hlt : ⌊(7 / 6 : ℝ)⌋₊ < 2 := (Nat.floor_lt (by norm_num)).mpr (by norm_num)
    omega
  have hq_vals : ∀ i : Fin 2, q i false = 1 / 2 ∧ q i true = 1 / 2 := by
    intro i
    simp only [q, GraphicalGame.nearestGridStrategy_false, GraphicalGame.nearestGridStrategy_true,
      thirdProfile, Bool.false_eq_true, ↓reduceIte]
    norm_num [hfl]
  refine ⟨hq_vals, ?_, ?_⟩
  · simpa using thirdTreeGame.isApproxNash_nearestGridStrategy (d := 1) (m := 2) (by decide)
      thirdTreeGame_payoff_bounds thirdTreeGame_degree_le
      thirdTreeGame_isMixedNash_thirdProfile.1
  · intro hexact
    have h0 := hexact.2 0 false
    simp only [GraphicalGame.toCostGame_expectedCost, GraphicalGame.toCostGame_deviationCost,
      GraphicalGame.expectedPayoff_def, GraphicalGame.deviationPayoff_def, sum_fin2_bool,
      productWeight_def, Fin.prod_univ_two] at h0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      (hq_vals 0).1, (hq_vals 0).2, (hq_vals 1).1, (hq_vals 1).2, thirdTreeGame,
      GraphicalGame.payoff_eq_localPayoff, update] at h0
    norm_num at h0

/-- Discretized `ApproximateTreeNash` soundness and completeness check on `thirdTreeGame` at
`ε = 1 / 4`. -/
example :
    ∃ q : Fin 2 → Bool → ℝ,
      thirdTreeGame.IsApproxTreeNashOutput edge2_isTree 0 (max 1 ⌈(1 : ℝ) / (1 / 4 : ℝ)⌉₊)
        (1 / 4) q ∧
      thirdTreeGame.IsApproxNash (1 / 4) q ∧
      ∀ i, ∑ b : Bool, |thirdProfile i b - q i b| ≤
        1 / ((max 1 ⌈(1 : ℝ) / (1 / 4 : ℝ)⌉₊ : ℕ) : ℝ) := by
  simpa using thirdTreeGame.exists_approxTreeNashOutput_of_isMixedNash edge2_isTree 0
    (d := 1) (ε := 1 / 4) (by norm_num)
    thirdTreeGame_payoff_bounds thirdTreeGame_degree_le
    thirdTreeGame_isMixedNash_thirdProfile.1

/-! ### 4. Local neighborhood equivalence vs expected payoff equivalence (Lemmas 7.9 & 7.10) -/

/-- Joint distribution `σ` on `Fin 2 → Bool`: equal mixture of `![false, false]` and
`![true, true]`. -/
noncomputable def corrSame : Convexity.StdSimplex ℝ (Fin 2 → Bool) :=
  .duple ![false, false] ![true, true] (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)

/-- Joint distribution `τ` on `Fin 2 → Bool`: equal mixture of `![false, true]` and
`![true, false]`. -/
noncomputable def corrDiff : Convexity.StdSimplex ℝ (Fin 2 → Bool) :=
  .duple ![false, true] ![true, false] (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)

private theorem corrSame_sum (f : (Fin 2 → Bool) → ℝ) :
    corrSame.weights.sum (fun s w => w * f s) =
      1 / 2 * f ![false, false] + 1 / 2 * f ![true, true] := by
  rw [corrSame, Convexity.StdSimplex.duple, Finsupp.sum_add_index' (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _), Finsupp.sum_single_index (zero_mul _),
    Finsupp.sum_single_index (zero_mul _)]

private theorem corrDiff_sum (f : (Fin 2 → Bool) → ℝ) :
    corrDiff.weights.sum (fun s w => w * f s) =
      1 / 2 * f ![false, true] + 1 / 2 * f ![true, false] := by
  rw [corrDiff, Convexity.StdSimplex.duple, Finsupp.sum_add_index' (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _), Finsupp.sum_single_index (zero_mul _),
    Finsupp.sum_single_index (zero_mul _)]

/-- On the empty graph `⊥`, `corrSame` and `corrDiff` are distinct distributions yet
local-neighborhood equivalent (`corrSame ≡_LN corrDiff`), so they give equal expected payoffs and
identical correlated-equilibrium status in every graphical game on `⊥`; on `⊤`, they are *not*
local-neighborhood equivalent and are separated by a `{0, 1}` graphical game (Lemma 7.9). -/
theorem corrSame_corrDiff_localNeighborhood :
    corrSame ≠ corrDiff ∧
      LocalNeighborhoodEquiv (⊥ : SimpleGraph (Fin 2)) corrSame corrDiff ∧
      ∃ M : GraphicalGame (Fin 2) (fun _ => Bool),
        M.graph = ⊤ ∧ ¬ M.ExpectedPayoffEquiv corrSame corrDiff := by
  have hrew : ∀ (ρ : Convexity.StdSimplex ℝ (Fin 2 → Bool)) (P : (Fin 2 → Bool) → Prop)
      [DecidablePred P],
      ρ.weights.sum (fun s w => if P s then w else 0) =
        ρ.weights.sum (fun s w => w * if P s then 1 else 0) :=
    fun ρ P _ => Finsupp.sum_congr fun _ _ => by split_ifs <;> ring
  have hne : corrSame ≠ corrDiff := by
    intro h
    have hw := congrArg (fun d : Convexity.StdSimplex ℝ (Fin 2 → Bool) =>
      d.weights.sum fun s w => w * if s = ![false, false] then (1 : ℝ) else 0) h
    simp only [corrSame_sum, corrDiff_sum] at hw
    have hft : (![false, true] : Fin 2 → Bool) ≠ ![false, false] := by decide
    have htf : (![true, false] : Fin 2 → Bool) ≠ ![false, false] := by decide
    have htt : (![true, true] : Fin 2 → Bool) ≠ ![false, false] := by decide
    simp only [↓reduceIte, hft, htf, htt] at hw
    norm_num at hw
  have hln_bot : LocalNeighborhoodEquiv (⊥ : SimpleGraph (Fin 2)) corrSame corrDiff := by
    intro i u
    classical
    rw [neighborhoodMarginal_def, neighborhoodMarginal_def, hrew, hrew, corrSame_sum, corrDiff_sum]
    have heq_cond : ∀ s : Fin 2 → Bool,
        ((fun j : ClosedNeighborhood (⊥ : SimpleGraph (Fin 2)) i => s j.val) = u) ↔
          s i = u ⟨i, Or.inl rfl⟩ := by
      intro s
      constructor
      · intro hs
        exact congrFun hs ⟨i, Or.inl rfl⟩
      · intro hsi
        ext ⟨j, hj⟩
        rcases hj with rfl | hbot
        · exact hsi
        · exact False.elim hbot
    simp only [heq_cond]
    fin_cases i <;> cases hval : u ⟨_, Or.inl rfl⟩ <;> simp
  have hnot_top : ¬ LocalNeighborhoodEquiv (⊤ : SimpleGraph (Fin 2)) corrSame corrDiff := by
    intro htop
    classical
    let u₀ : ClosedNeighborhood (⊤ : SimpleGraph (Fin 2)) 0 → Bool := fun _ => false
    have h0 := htop 0 u₀
    rw [neighborhoodMarginal_def, neighborhoodMarginal_def, hrew, hrew,
      corrSame_sum, corrDiff_sum] at h0
    have hcond : ∀ s : Fin 2 → Bool,
        ((fun j : ClosedNeighborhood (⊤ : SimpleGraph (Fin 2)) 0 => s j.val) = u₀) ↔
          s = ![false, false] := by
      intro s
      constructor
      · intro hs
        ext k
        fin_cases k
        · exact congrFun hs ⟨0, Or.inl rfl⟩
        · exact congrFun hs ⟨1, Or.inr (by decide)⟩
      · rintro rfl
        ext ⟨k, _⟩
        fin_cases k <;> rfl
    simp only [hcond] at h0
    have hft : (![false, true] : Fin 2 → Bool) ≠ ![false, false] := by decide
    have htf : (![true, false] : Fin 2 → Bool) ≠ ![false, false] := by decide
    have htt : (![true, true] : Fin 2 → Bool) ≠ ![false, false] := by decide
    simp only [↓reduceIte, hft, htf, htt] at h0
    norm_num at h0
  exact ⟨hne, hln_bot, exists_graphicalGame_not_expectedPayoffEquiv hnot_top⟩

/-! ### 5. Cyclic counterexamples on `C₄` (`0 — 1 — 2 — 3 — 0`) -/

/-- Four-cycle `C₄` (`0 — 1 — 2 — 3 — 0`) on `Fin 4`. -/
abbrev cycle4Graph : SimpleGraph (Fin 4) := SimpleGraph.cycleGraph 4

instance : DecidableRel cycle4Graph.Adj := by
  intro i j
  rw [SimpleGraph.cycleGraph_adj]
  infer_instance

theorem cycle4_adj_01 : cycle4Graph.Adj 0 1 := by decide
theorem cycle4_adj_12 : cycle4Graph.Adj 1 2 := by decide
theorem cycle4_adj_23 : cycle4Graph.Adj 2 3 := by decide
theorem cycle4_adj_30 : cycle4Graph.Adj 3 0 := by decide

private theorem cycle4_not_top : cycle4Graph ≠ ⊤ := by
  intro h
  have hadj : cycle4Graph.Adj 0 2 := by simp [h]
  revert hadj
  decide

/-- `C₄` contains the 4-cycle `0 — 1 — 2 — 3 — 0`, so it is neither acyclic nor a tree. -/
theorem cycle4_not_acyclic_and_not_tree :
    ¬ cycle4Graph.IsAcyclic ∧ ¬ cycle4Graph.IsTree := by
  have hna : ¬ cycle4Graph.IsAcyclic := by
    intro hA
    let w : cycle4Graph.Walk 0 0 :=
      SimpleGraph.Walk.cons cycle4_adj_01
        (SimpleGraph.Walk.cons cycle4_adj_12
          (SimpleGraph.Walk.cons cycle4_adj_23
            (SimpleGraph.Walk.cons cycle4_adj_30 SimpleGraph.Walk.nil)))
    have hnd : w.support.tail.Nodup := by decide
    have hne : w ≠ SimpleGraph.Walk.nil := by decide
    have htrail : w.IsTrail := ⟨by decide⟩
    exact hA w ⟨⟨htrail, hne⟩, hnd⟩
  exact ⟨hna, fun hT => hna hT.isAcyclic⟩

/-! #### 5a. Naive spanning-tree `TreeNash` fails on `C₄` -/

/-- Odd-parity cyclic game on `C₄`:
* players `0, 1, 2` get `1` by matching their next neighbor (`1, 2, 3`);
* player `3` gets `1` by **disagreeing** with player `0` across the cycle-closing edge `{3, 0}`. -/
abbrev cycle4Game : GraphicalGame (Fin 4) (fun _ => Bool) where
  graph := cycle4Graph
  localPayoff i u :=
    match i with
    | 0 => if u ⟨0, Or.inl rfl⟩ == u ⟨1, Or.inr cycle4_adj_01⟩ then 1 else 0
    | 1 => if u ⟨1, Or.inl rfl⟩ == u ⟨2, Or.inr cycle4_adj_12⟩ then 1 else 0
    | 2 => if u ⟨2, Or.inl rfl⟩ == u ⟨3, Or.inr cycle4_adj_23⟩ then 1 else 0
    | 3 => if u ⟨3, Or.inl rfl⟩ != u ⟨0, Or.inr cycle4_adj_30⟩ then 1 else 0

/-- Succinct table count on `C₄`: `4 * 2^3 = 32 < 64 = normalFormEntries`. -/
theorem cycle4Game_tableEntries :
    cycle4Game.tableEntries = 32 ∧
      cycle4Game.tableEntries < CostGame.normalFormEntries (Fin 4) (fun _ => Bool) := by
  refine ⟨?_, cycle4Game.tableEntries_lt_normalFormEntries cycle4_not_top fun _ => by simp⟩
  rw [cycle4Game.tableEntries_eq_sum_prod]
  decide

/-- Spanning-tree truncation of `cycle4Game` obtained by dropping back-edge `{3, 0}` onto `P₄`
(fixing player `0`'s unseen action to `false` in leaf `3`'s table). -/
def spanningTreeCycleGame : GraphicalGame (Fin 4) (fun _ => Bool) where
  graph := path4Graph
  localPayoff i u :=
    match i with
    | 0 => if u ⟨0, Or.inl rfl⟩ == u ⟨1, Or.inr path4_adj_01⟩ then 1 else 0
    | 1 => if u ⟨1, Or.inl rfl⟩ == u ⟨2, Or.inr path4_adj_12⟩ then 1 else 0
    | 2 => if u ⟨2, Or.inl rfl⟩ == u ⟨3, Or.inr path4_adj_23⟩ then 1 else 0
    | 3 => if u ⟨3, Or.inl rfl⟩ != false then 1 else 0

/-- **Cyclic counterexample (spanning-tree pass failure)**:
1. Running `TreeNash` on the spanning tree `P₄` (dropping back-edge `{3, 0}`) accepts the all-`true`
   profile `fun _ => Pi.single true 1` as an exact `TreeNash` output;
2. On the cyclic game `cycle4Game` itself, `fun _ => Pi.single true 1` is **not** a Nash equilibrium
   (not even a `(1 / 2)`-approximate Nash equilibrium, since player `3` gains `+1` by deviating to
   `false`);
3. Moreover, `cycle4Game` has **no pure Nash equilibrium at all**. -/
theorem cycle4Game_naive_spanningTree_fails :
    spanningTreeCycleGame.IsTreeNashOutput path4_isTree 0 (fun _ => Pi.single true 1) ∧
      ¬ cycle4Game.IsApproxNash (1 / 2) (fun _ => Pi.single true 1) ∧
      ¬ cycle4Game.toCostGame.IsMixedNash (fun _ => Pi.single true 1) ∧
      ∀ s : Fin 4 → Bool, ¬ cycle4Game.toCostGame.IsPureNash s := by
  have hspan_pure : spanningTreeCycleGame.toCostGame.IsPureNash (fun _ => true) := by
    intro i a
    fin_cases i <;> cases a <;> simp [spanningTreeCycleGame, update]
  have hspan_out :
      spanningTreeCycleGame.IsTreeNashOutput path4_isTree 0 (fun _ => Pi.single true 1) :=
    (spanningTreeCycleGame.isTreeNashOutput_iff_isMixedNash path4_isTree 0).mpr
      hspan_pure.isMixedNash
  have hnot_approx : ¬ cycle4Game.IsApproxNash (1 / 2) (fun _ => Pi.single true 1) := by
    rintro ⟨_, hbr⟩
    have h3 := hbr 3 false
    have hexp : cycle4Game.expectedPayoff (fun _ => Pi.single true 1) 3 = 0 := by
      have h := cycle4Game.toCostGame.expectedCost_single (fun _ : Fin 4 => true) 3
      rw [GraphicalGame.toCostGame_expectedCost, GraphicalGame.toCostGame_cost] at h
      have hcost : cycle4Game.payoff 3 (fun _ : Fin 4 => true) = 0 := by
        simp [cycle4Game]
      linarith
    have hdev : cycle4Game.deviationPayoff (fun _ => Pi.single true 1) 3 false = 1 := by
      have h := cycle4Game.toCostGame.deviationCost_single (fun _ : Fin 4 => true) 3 false
      rw [GraphicalGame.toCostGame_deviationCost, GraphicalGame.toCostGame_cost] at h
      have hcost : cycle4Game.payoff 3 (update (fun _ : Fin 4 => true) 3 false) = 1 := by
        simp [cycle4Game, update]
      linarith
    linarith
  have hnot_mixed : ¬ cycle4Game.toCostGame.IsMixedNash (fun _ => Pi.single true 1) := by
    intro hm
    exact hnot_approx (GraphicalGame.IsApproxNash.mono cycle4Game
      (cycle4Game.isApproxNash_zero_iff.mpr hm) (by norm_num))
  have hno_pure : ∀ s : Fin 4 → Bool, ¬ cycle4Game.toCostGame.IsPureNash s := by
    intro s hp
    have h0 := hp 0 (s 1)
    have h1 := hp 1 (s 2)
    have h2 := hp 2 (s 3)
    have h3 := hp 3 (!s 0)
    revert h0 h1 h2 h3
    cases hs0 : s 0 <;> cases hs1 : s 1 <;> cases hs2 : s 2 <;> cases hs3 : s 3 <;>
      simp [cycle4Game, update, hs0, hs1, hs2, hs3]
  exact ⟨hspan_out, hnot_approx, hnot_mixed, hno_pure⟩

/-! #### 5b. Pairwise `NashProp` branch-table inconsistency on `C₄` ([Kearns2007], §7.3.3, p. 169)
-/

/-- Four-cycle game illustrating Kearns §7.3.3 (p. 169):
* players `0` and `2` are indifferent (`localPayoff = 0`);
* player `1` gets `2 / 3` from `false`, and `1` (if `s 2 = true`) or `0` (if `s 2 = false`) from
  `true` (so `true` is a best response iff `p 2 true ≥ 2 / 3`);
* player `3` gets `2 / 3` from `false`, and `1` (if `s 2 = false`) or `0` (if `s 2 = true`) from
  `true` (so `true` is a best response iff `p 2 false ≥ 2 / 3`). -/
noncomputable abbrev nashPropCycleGame : GraphicalGame (Fin 4) (fun _ => Bool) where
  graph := cycle4Graph
  localPayoff i u :=
    match i with
    | 0 => 0
    | 1 =>
      if u ⟨1, Or.inl rfl⟩ then
        if u ⟨2, Or.inr cycle4_adj_12⟩ then 1 else 0
      else 2 / 3
    | 2 => 0
    | 3 =>
      if u ⟨3, Or.inl rfl⟩ then
        if u ⟨2, Or.inr cycle4_adj_23.symm⟩ then 0 else 1
      else 2 / 3

/-- **Pairwise `NashProp` branch-table counterexample on `C₄`** ([Kearns2007], §7.3.3, p. 169):
* Along branch `{0, 1, 2}`, `(p 0 = pure true, p 1 = pure true)` extends to `qTop`
  (`qTop 2 = pure true`) satisfying exact local best responses at `0`, `1`, and `2`;
* Along branch `{0, 3, 2}`, `(p 0 = pure true, p 3 = pure true)` extends to `qBot`
  (`qBot 2 = pure false`) satisfying exact local best responses at `0`, `3`, and `2`;
* Yet **no** global mixed Nash equilibrium `p` of `nashPropCycleGame` assigns `Pi.single true 1` to
  both `1` and `3`. -/
theorem nashPropCycleGame_branch_tables_inconsistent :
    (∃ qTop : Fin 4 → Bool → ℝ,
      qTop 0 = Pi.single true 1 ∧ qTop 1 = Pi.single true 1 ∧
      nashPropCycleGame.IsBestResponse 0 (qTop 0) (fun j => qTop j.val) ∧
      nashPropCycleGame.IsBestResponse 1 (qTop 1) (fun j => qTop j.val) ∧
      nashPropCycleGame.IsBestResponse 2 (qTop 2) (fun j => qTop j.val)) ∧
    (∃ qBot : Fin 4 → Bool → ℝ,
      qBot 0 = Pi.single true 1 ∧ qBot 3 = Pi.single true 1 ∧
      nashPropCycleGame.IsBestResponse 0 (qBot 0) (fun j => qBot j.val) ∧
      nashPropCycleGame.IsBestResponse 3 (qBot 3) (fun j => qBot j.val) ∧
      nashPropCycleGame.IsBestResponse 2 (qBot 2) (fun j => qBot j.val)) ∧
    ¬ ∃ p : Fin 4 → Bool → ℝ,
      nashPropCycleGame.toCostGame.IsMixedNash p ∧
      p 1 = Pi.single true 1 ∧ p 3 = Pi.single true 1 := by
  have hbr_of_pure : ∀ (s : Fin 4 → Bool) (i : Fin 4),
      (∀ a : Bool, nashPropCycleGame.toCostGame.cost i s ≤
        nashPropCycleGame.toCostGame.cost i (update s i a)) →
      nashPropCycleGame.IsBestResponse i (Pi.single (s i) 1)
        (fun j => Pi.single (s j.val) 1) := by
    intro s i hi
    refine ⟨isMixedStrategy_single _, fun a => ?_⟩
    have hdev : ∀ b, nashPropCycleGame.localDeviationPayoff i b
        (fun j => Pi.single (s j.val) 1) = nashPropCycleGame.payoff i (update s i b) := by
      intro b
      rw [← nashPropCycleGame.deviationPayoff_eq_localDeviationPayoff
        (fun k _ => (isMixedStrategy_single (s k)).sum_eq_one)]
      have h := nashPropCycleGame.toCostGame.deviationCost_single s i b
      rw [GraphicalGame.toCostGame_deviationCost, GraphicalGame.toCostGame_cost] at h
      linarith
    simp only [hdev, add_zero]
    have hexp : ∑ b : Bool, (Pi.single (s i) 1 : Bool → ℝ) b *
        nashPropCycleGame.payoff i (update s i b) = nashPropCycleGame.payoff i s := by
      rw [Fintype.sum_bool]
      cases hsi : s i
      · simp [show update s i false = s from hsi ▸ update_eq_self i s]
      · simp [show update s i true = s from hsi ▸ update_eq_self i s]
    rw [hexp]
    have hia := hi a
    simp only [GraphicalGame.toCostGame_cost] at hia
    linarith
  refine ⟨?_, ?_, ?_⟩
  · let sTop : Fin 4 → Bool := ![true, true, true, false]
    refine ⟨fun i => Pi.single (sTop i) 1, rfl, rfl,
      hbr_of_pure sTop 0 ?_, hbr_of_pure sTop 1 ?_, hbr_of_pure sTop 2 ?_⟩
    · intro a; cases a <;> simp [nashPropCycleGame]
    · intro a; (cases a <;> simp [nashPropCycleGame, sTop, update]); norm_num
    · intro a; cases a <;> simp [nashPropCycleGame]
  · let sBot : Fin 4 → Bool := ![true, false, false, true]
    refine ⟨fun i => Pi.single (sBot i) 1, rfl, rfl,
      hbr_of_pure sBot 0 ?_, hbr_of_pure sBot 3 ?_, hbr_of_pure sBot 2 ?_⟩
    · intro a; cases a <;> simp [nashPropCycleGame]
    · intro a; (cases a <;> simp [nashPropCycleGame, sBot, update]); norm_num
    · intro a; cases a <;> simp [nashPropCycleGame]
  · rintro ⟨p, hp, hp1, hp3⟩
    have hsum_pw : ∑ s : Fin 4 → Bool, productWeight p s = 1 :=
      sum_productWeight (fun k => (hp.1 k).sum_eq_one)
    have hsum2 : p 2 true + p 2 false = 1 := by
      simpa only [Fintype.sum_bool] using (hp.1 2).sum_eq_one
    have h1_false : nashPropCycleGame.deviationPayoff p 1 false = 2 / 3 := by
      rw [nashPropCycleGame.deviationPayoff_def]
      have hpay : ∀ s, nashPropCycleGame.payoff 1 (update s 1 false) = 2 / 3 :=
        fun _ => by simp [nashPropCycleGame]
      simp only [hpay, ← sum_mul, hsum_pw, one_mul]
    have h1_true : nashPropCycleGame.deviationPayoff p 1 true = p 2 true := by
      rw [nashPropCycleGame.deviationPayoff_def]
      have hpay : ∀ s, nashPropCycleGame.payoff 1 (update s 1 true) = if s 2 then 1 else 0 :=
        fun _ => by simp [nashPropCycleGame]
      simp only [hpay]
      rw [sum_productWeight_mul_apply (i := 2) (fun j _ => (hp.1 j).sum_eq_one)
        (fun b => if b then (1 : ℝ) else 0)]
      simp
    have h3_false : nashPropCycleGame.deviationPayoff p 3 false = 2 / 3 := by
      rw [nashPropCycleGame.deviationPayoff_def]
      have hpay : ∀ s, nashPropCycleGame.payoff 3 (update s 3 false) = 2 / 3 :=
        fun _ => by simp [nashPropCycleGame]
      simp only [hpay, ← sum_mul, hsum_pw, one_mul]
    have h3_true : nashPropCycleGame.deviationPayoff p 3 true = p 2 false := by
      rw [nashPropCycleGame.deviationPayoff_def]
      have hpay : ∀ s, nashPropCycleGame.payoff 3 (update s 3 true) = if s 2 then 0 else 1 :=
        fun _ => by simp [nashPropCycleGame]
      simp only [hpay]
      rw [sum_productWeight_mul_apply (i := 2) (fun j _ => (hp.1 j).sum_eq_one)
        (fun b => if b then (0 : ℝ) else 1)]
      simp
    have hpos1 : 0 < p 1 true := by simp [hp1]
    have hpos3 : 0 < p 3 true := by simp [hp3]
    have heq1 := hp.deviationCost_eq_of_pos 1 hpos1
    have hle1 := hp.2 1 false
    have heq3 := hp.deviationCost_eq_of_pos 3 hpos3
    have hle3 := hp.2 3 false
    simp only [GraphicalGame.toCostGame_deviationCost,
      GraphicalGame.toCostGame_expectedCost] at heq1 hle1 heq3 hle3
    linarith

end CslibFrontierTests.GameTheory.Graphical
