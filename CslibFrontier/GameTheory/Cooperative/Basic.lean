/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cooperative transferable-utility games, cost sharing, and facility location

A cooperative **cost-sharing game** with transferable utility (`CostSharingGame A`) assigns a real
cost `cost S` to every finite coalition `S : Finset A` with `cost ∅ = 0` ([TardosVazirani2007],
Section 1.7.2; [JainMahdian2007], Section 15.1). Dual **value** (or surplus-sharing) cooperative
games (`CooperativeGame A`) assign a coalition value `val S` with `val ∅ = 0` and correspond to
cost-sharing games via negation (`CooperativeGame.toCostSharingGame`,
`CostSharingGame.toCooperativeGame`).

This module defines:
* exact and `γ`-approximate cores (`CostSharingGame.InCore`, `CostSharingGame.InApproxCore`,
  [JainMahdian2007], Definitions 15.3 and 15.7) and balanced coalition weights
  (`IsBalancedWeights`, Definition 15.5);
* the cooperative **facility location game** (`FacilityLocationInstance`, Definition 15.1), metric
  instances (`FacilityLocationInstance.ofMetric`), and **Proposition 15.10** showing that any
  feasible solution `(α, β)` to the standard facility-location dual LP satisfies the core
  constraints;
* the concrete 3-agent, 2-facility metric instance of **Example 15.2** / **Example 15.4**
  (`example15_2`), where `(4, 2, 2)` and `(4, 1, 3)` lie in the core, together with the 6-vertex
  (`3` agents, `3` facilities) metric instance `emptyCoreMetricFL` whose exact core is empty
  (`γ = 1` fails) while its `(15 / 16)`-core is nonempty and optimal, and the non-metric bipartite
  table `emptyCoreBipartiteFL` corresponding literally to the text of Example 15.4 (where
  adding a third facility at distance `1` to `a` and `c` without re-closing shortest paths leaves
  `c({a, b, c}) = 8`, whereas re-closing the metric lowers `d(f₂, a)` to `3` and `c({a, b, c})` to
  `7`).

## Main definitions

* `Cslib.GameTheory.CostSharingGame`: transferable-utility cost-sharing game `c : Finset A → ℝ`
  with `c ∅ = 0`.
* `Cslib.GameTheory.CostSharingGame.IsCoreFeasible`,
  `Cslib.GameTheory.CostSharingGame.IsCoreFeasibleOn`: coalitional rationality `∑ j ∈ S, α j ≤ c S`.
* `Cslib.GameTheory.CostSharingGame.InCore`, `Cslib.GameTheory.CostSharingGame.NonemptyCore`:
  budget-balanced core allocations ([JainMahdian2007], Definition 15.3).
* `Cslib.GameTheory.CostSharingGame.InApproxCore`,
  `Cslib.GameTheory.CostSharingGame.NonemptyApproxCore`: `γ`-approximate core allocations
  ([JainMahdian2007], Definition 15.7).
* `Cslib.GameTheory.CostSharingGame.IsSubadditive`, `Cslib.GameTheory.CostSharingGame.IsNonneg`:
  disjoint subadditivity and nonnegativity of coalition costs.
* `Cslib.GameTheory.CostSharingGame.perm`, `Cslib.GameTheory.CostSharingGame.restrict`:
  agent-permutation pushforward and subcoalition restriction.
* `Cslib.GameTheory.CooperativeGame`, `Cslib.GameTheory.CooperativeGame.InCore`,
  `Cslib.GameTheory.CooperativeGame.NonemptyCore`: dual surplus-sharing TU games and their core.
* `Cslib.GameTheory.IsBalancedWeights`: balanced weight collections `λ : Finset A → ℝ`
  ([JainMahdian2007], Definition 15.5).
* `Cslib.GameTheory.FacilityLocationInstance`,
  `Cslib.GameTheory.FacilityLocationInstance.ofMetric`,
  `Cslib.GameTheory.FacilityLocationInstance.toCostSharingGame`,
  `Cslib.GameTheory.FacilityLocationInstance.IsDualFeasible`: cooperative facility location games
  and their LP dual ([JainMahdian2007], Definition 15.1 and (15.4)).
* `Cslib.GameTheory.FacilityLocationInstance.example15_2`,
  `Cslib.GameTheory.FacilityLocationInstance.emptyCoreBipartiteFL`,
  `Cslib.GameTheory.FacilityLocationInstance.emptyCoreMetricFL`: canonical nonempty-core and
  empty-core facility location instances ([JainMahdian2007], Examples 15.2 and 15.4).

## Main results

* `Cslib.GameTheory.CostSharingGame.InApproxCore.mul_le_sum_balanced`,
  `Cslib.GameTheory.CostSharingGame.InCore.le_sum_balanced`: weak LP duality for balanced weights.
* `Cslib.GameTheory.CooperativeGame.inCore_toCostSharingGame_iff`,
  `Cslib.GameTheory.CooperativeGame.nonemptyCore_toCostSharingGame_iff`,
  `Cslib.GameTheory.CostSharingGame.inCore_toCooperativeGame_iff`,
  `Cslib.GameTheory.CostSharingGame.nonemptyCore_toCooperativeGame_iff`: exact core duality between
  surplus-sharing and cost-sharing TU games.
* `Cslib.GameTheory.FacilityLocationInstance.toCostSharingGame_isSubadditive`: facility location
  cost functions are subadditive.
* `Cslib.GameTheory.FacilityLocationInstance.IsDualFeasible.isCoreFeasible`: **Proposition 15.10**
  of [JainMahdian2007] — dual-LP feasible solutions satisfy all core inequalities.
* `Cslib.GameTheory.FacilityLocationInstance.example15_2_cost`,
  `Cslib.GameTheory.FacilityLocationInstance.example15_2_inCore_four_two_two`,
  `Cslib.GameTheory.FacilityLocationInstance.example15_2_inCore_four_one_three`: **Examples 15.2
  and 15.4** of [JainMahdian2007].
* `Cslib.GameTheory.FacilityLocationInstance.emptyCoreMetricFL_cost_univ`,
  `Cslib.GameTheory.FacilityLocationInstance.emptyCoreMetricFL_not_nonemptyCore`,
  `Cslib.GameTheory.FacilityLocationInstance.emptyCoreMetricFL_inApproxCore`,
  `Cslib.GameTheory.FacilityLocationInstance.emptyCoreMetricFL_not_nonemptyApproxCore_of_gt`,
  `Cslib.GameTheory.FacilityLocationInstance.emptyCoreBipartiteFL_cost_univ`,
  `Cslib.GameTheory.FacilityLocationInstance.emptyCoreBipartiteFL_not_nonemptyCore`,
  `Cslib.GameTheory.FacilityLocationInstance.emptyCoreBipartiteFL_not_nonemptyApproxCore_of_gt`,
  `Cslib.GameTheory.FacilityLocationInstance.emptyCoreBipartiteFL_inApproxCore`: empty exact
  core (`γ = 1`) and tight `(15 / 16)`-approximate core for facility location.

## References

* [JainMahdian2007]
* [TardosVazirani2007]
-/

public section

namespace Cslib.GameTheory

/-! ## Cost-sharing games and core concepts -/

/-- A transferable-utility **cost-sharing game** on agent type `A` assigns a real cost `cost S` to
each finite coalition `S : Finset A`, normalized by `cost ∅ = 0` ([JainMahdian2007], Section 15.1;
[TardosVazirani2007], Section 1.7.2). -/
@[ext]
structure CostSharingGame (A : Type*) where
  /-- Cost `cost S` of serving coalition `S`. -/
  cost : Finset A → ℝ
  /-- Serving the empty coalition costs `0`. -/
  cost_empty : cost ∅ = 0

namespace CostSharingGame

variable {A : Type*}

attribute [simp] cost_empty

instance : Zero (CostSharingGame A) where
  zero := ⟨fun _ => 0, rfl⟩

@[simp]
theorem zero_cost (S : Finset A) : (0 : CostSharingGame A).cost S = 0 := rfl

instance : Add (CostSharingGame A) where
  add G₁ G₂ := ⟨fun S => G₁.cost S + G₂.cost S, by simp⟩

@[simp]
theorem add_cost (G₁ G₂ : CostSharingGame A) (S : Finset A) :
    (G₁ + G₂).cost S = G₁.cost S + G₂.cost S := rfl

instance : Neg (CostSharingGame A) where
  neg G := ⟨fun S => -G.cost S, by simp⟩

@[simp]
theorem neg_cost (G : CostSharingGame A) (S : Finset A) : (-G).cost S = -G.cost S := rfl

instance : Sub (CostSharingGame A) where
  sub G₁ G₂ := ⟨fun S => G₁.cost S - G₂.cost S, by simp⟩

@[simp]
theorem sub_cost (G₁ G₂ : CostSharingGame A) (S : Finset A) :
    (G₁ - G₂).cost S = G₁.cost S - G₂.cost S := rfl

instance : SMul ℝ (CostSharingGame A) where
  smul r G := ⟨fun S => r * G.cost S, by simp⟩

@[simp]
theorem smul_cost (r : ℝ) (G : CostSharingGame A) (S : Finset A) :
    (r • G).cost S = r * G.cost S := rfl

instance : AddCommGroup (CostSharingGame A) where
  add_assoc _ _ _ := CostSharingGame.ext (funext fun _ => add_assoc _ _ _)
  zero_add _ := CostSharingGame.ext (funext fun _ => zero_add _)
  add_zero _ := CostSharingGame.ext (funext fun _ => add_zero _)
  add_comm _ _ := CostSharingGame.ext (funext fun _ => add_comm _ _)
  neg_add_cancel _ := CostSharingGame.ext (funext fun _ => neg_add_cancel _)
  sub_eq_add_neg _ _ := CostSharingGame.ext (funext fun _ => sub_eq_add_neg _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp]
theorem sum_cost {ι : Type*} (s : Finset ι) (f : ι → CostSharingGame A) (S : Finset A) :
    (∑ i ∈ s, f i).cost S = ∑ i ∈ s, (f i).cost S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

instance : Module ℝ (CostSharingGame A) where
  one_smul _ := CostSharingGame.ext (funext fun _ => one_mul _)
  mul_smul _ _ _ := CostSharingGame.ext (funext fun _ => mul_assoc _ _ _)
  smul_zero _ := CostSharingGame.ext (funext fun _ => mul_zero _)
  smul_add _ _ _ := CostSharingGame.ext (funext fun _ => mul_add _ _ _)
  add_smul _ _ _ := CostSharingGame.ext (funext fun _ => add_mul _ _ _)
  zero_smul _ := CostSharingGame.ext (funext fun _ => zero_mul _)

/-- Pushforward of a cost-sharing game along a permutation `π` of the agents: a coalition `S` of
renamed agents pays the cost of its preimage `S.map π.symm.toEmbedding` ([JainMahdian2007],
Definition 15.25). -/
def perm (π : Equiv.Perm A) (G : CostSharingGame A) : CostSharingGame A where
  cost S := G.cost (S.map π.symm.toEmbedding)
  cost_empty := by simp

@[simp]
theorem perm_cost (π : Equiv.Perm A) (G : CostSharingGame A) (S : Finset A) :
    (G.perm π).cost S = G.cost (S.map π.symm.toEmbedding) := by
  rfl

/-- Restriction of a cost-sharing game to a finite subcoalition `T : Finset A`, viewed as a game on
the subtype `{x // x ∈ T}`. -/
def restrict (G : CostSharingGame A) (T : Finset A) :
    CostSharingGame {x // x ∈ T} where
  cost S := G.cost (S.map (Function.Embedding.subtype _))
  cost_empty := by simp

@[simp]
theorem restrict_cost (G : CostSharingGame A) (T : Finset A) (S : Finset {x // x ∈ T}) :
    (G.restrict T).cost S = G.cost (S.map (Function.Embedding.subtype _)) := by
  rfl

/-- All coalition costs are nonnegative (`c : 2^A → ℝ₊ ∪ {0}`, [JainMahdian2007], Section 15.3). -/
@[expose] def IsNonneg (G : CostSharingGame A) : Prop :=
  ∀ S : Finset A, 0 ≤ G.cost S

/-- Disjoint **subadditivity**: `c(S₁ ∪ S₂) ≤ c(S₁) + c(S₂)` for all disjoint coalitions `S₁, S₂`
([JainMahdian2007], Section 15.2.2, p. 389). -/
@[expose] def IsSubadditive [DecidableEq A] (G : CostSharingGame A) : Prop :=
  ∀ ⦃S₁ S₂ : Finset A⦄, Disjoint S₁ S₂ → G.cost (S₁ ∪ S₂) ≤ G.cost S₁ + G.cost S₂

/-- Coalitional rationality (LP `(15.1)` feasibility) restricted to subcoalitions of `T`:
`∑ j ∈ S, α j ≤ G.cost S` for every `S ⊆ T`. -/
@[expose] def IsCoreFeasibleOn (G : CostSharingGame A) (T : Finset A) (α : A → ℝ) : Prop :=
  ∀ ⦃S : Finset A⦄, S ⊆ T → ∑ j ∈ S, α j ≤ G.cost S

/-- Coalitional rationality (the **core property**, [JainMahdian2007], Definition 15.3): no
coalition `S` pays more in total than its standalone cost `G.cost S`. -/
@[expose] def IsCoreFeasible (G : CostSharingGame A) (α : A → ℝ) : Prop :=
  ∀ S : Finset A, ∑ j ∈ S, α j ≤ G.cost S

@[simp]
theorem isCoreFeasibleOn_univ_iff [Fintype A] (G : CostSharingGame A) (α : A → ℝ) :
    G.IsCoreFeasibleOn Finset.univ α ↔ G.IsCoreFeasible α :=
  ⟨fun h S => h (Finset.subset_univ S), fun h S _ => h S⟩

/-- A cost allocation `α : A → ℝ` lies in the **core** of `G` ([JainMahdian2007], Definition 15.3;
[TardosVazirani2007], Section 1.7.2) if it is budget-balanced (`∑ j, α j = G.cost univ`) and
satisfies `IsCoreFeasible`. -/
@[expose] def InCore [Fintype A] (G : CostSharingGame A) (α : A → ℝ) : Prop :=
  (∑ j : A, α j = G.cost Finset.univ) ∧ G.IsCoreFeasible α

/-- `G` has a **nonempty core** if there exists an allocation in `G.InCore`. -/
@[expose] def NonemptyCore [Fintype A] (G : CostSharingGame A) : Prop :=
  ∃ α : A → ℝ, G.InCore α

/-- A cost allocation `α : A → ℝ` lies in the **`γ`-approximate core** (`γ`-core) of `G`
([JainMahdian2007], Definition 15.7) if it is `γ`-budget-balanced
(`γ * G.cost univ ≤ ∑ j, α j ≤ G.cost univ`) and satisfies `IsCoreFeasible`. -/
@[expose] def InApproxCore [Fintype A] (G : CostSharingGame A) (γ : ℝ) (α : A → ℝ) : Prop :=
  (γ * G.cost Finset.univ ≤ ∑ j : A, α j ∧ ∑ j : A, α j ≤ G.cost Finset.univ) ∧
    G.IsCoreFeasible α

/-- `G` has a **nonempty `γ`-core** if there exists an allocation in `G.InApproxCore γ`. -/
@[expose] def NonemptyApproxCore [Fintype A] (G : CostSharingGame A) (γ : ℝ) : Prop :=
  ∃ α : A → ℝ, G.InApproxCore γ α

@[simp]
theorem inApproxCore_one_iff [Fintype A] (G : CostSharingGame A) (α : A → ℝ) :
    G.InApproxCore 1 α ↔ G.InCore α := by
  simp only [InApproxCore, InCore, one_mul]
  exact ⟨fun ⟨⟨hge, hle⟩, hfeas⟩ => ⟨le_antisymm hle hge, hfeas⟩,
    fun ⟨heq, hfeas⟩ => ⟨⟨heq.ge, heq.le⟩, hfeas⟩⟩

@[simp]
theorem nonemptyApproxCore_one_iff [Fintype A] (G : CostSharingGame A) :
    G.NonemptyApproxCore 1 ↔ G.NonemptyCore :=
  exists_congr (G.inApproxCore_one_iff)

theorem InCore.inApproxCore [Fintype A] {G : CostSharingGame A} {α : A → ℝ} (h : G.InCore α)
    {γ : ℝ} (hγ : γ ≤ 1) (hcost : 0 ≤ G.cost Finset.univ) : G.InApproxCore γ α :=
  ⟨⟨(mul_le_of_le_one_left hcost hγ).trans_eq h.1.symm, h.1.le⟩, h.2⟩

theorem InApproxCore.mono [Fintype A] {G : CostSharingGame A} {γ₁ γ₂ : ℝ} {α : A → ℝ}
    (h : G.InApproxCore γ₂ α) (hγ : γ₁ ≤ γ₂) (hcost : 0 ≤ G.cost Finset.univ) :
    G.InApproxCore γ₁ α :=
  ⟨⟨(mul_le_mul_of_nonneg_right hγ hcost).trans h.1.1, h.1.2⟩, h.2⟩

end CostSharingGame

/-! ## Dual surplus-sharing cooperative games -/

/-- A transferable-utility **cooperative value game** (surplus-sharing game) assigns a real value
`val S` to each finite coalition `S : Finset A`, normalized by `val ∅ = 0` ([JainMahdian2007],
Section 15.1; [TardosVazirani2007], Section 1.7.2). -/
@[ext]
structure CooperativeGame (A : Type*) where
  /-- Total value `val S` achievable by coalition `S`. -/
  val : Finset A → ℝ
  /-- The empty coalition generates value `0`. -/
  val_empty : val ∅ = 0

namespace CooperativeGame

variable {A : Type*}

attribute [simp] val_empty

/-- A payoff allocation `x : A → ℝ` lies in the **core** of a value game `G` if it distributes
`G.val univ` (`∑ j, x j = G.val univ`) and gives every coalition `S` at least its standalone value
(`G.val S ≤ ∑ j ∈ S, x j`). -/
@[expose] def InCore [Fintype A] (G : CooperativeGame A) (x : A → ℝ) : Prop :=
  (∑ j : A, x j = G.val Finset.univ) ∧ ∀ S : Finset A, G.val S ≤ ∑ j ∈ S, x j

/-- `G` has a **nonempty core** if there exists a payoff allocation in `G.InCore`. -/
@[expose] def NonemptyCore [Fintype A] (G : CooperativeGame A) : Prop :=
  ∃ x : A → ℝ, G.InCore x

/-- Negating values turns a cooperative value game into its dual cost-sharing game
([JainMahdian2007], Section 15.1, p. 386). -/
def toCostSharingGame (G : CooperativeGame A) : CostSharingGame A where
  cost S := -G.val S
  cost_empty := by simp

@[simp]
theorem toCostSharingGame_cost (G : CooperativeGame A) (S : Finset A) :
    G.toCostSharingGame.cost S = -G.val S := by
  rfl

end CooperativeGame

/-- Negating costs turns a cost-sharing game into its dual cooperative value game. -/
def CostSharingGame.toCooperativeGame {A : Type*} (G : CostSharingGame A) :
    CooperativeGame A where
  val S := -G.cost S
  val_empty := by simp

@[simp]
theorem CostSharingGame.toCooperativeGame_val {A : Type*} (G : CostSharingGame A) (S : Finset A) :
    G.toCooperativeGame.val S = -G.cost S := by
  rfl

@[simp]
theorem CooperativeGame.toCostSharingGame_toCooperativeGame {A : Type*} (G : CooperativeGame A) :
    G.toCostSharingGame.toCooperativeGame = G := by
  ext S; simp

@[simp]
theorem CostSharingGame.toCooperativeGame_toCostSharingGame {A : Type*} (G : CostSharingGame A) :
    G.toCooperativeGame.toCostSharingGame = G := by
  ext S; simp

@[simp]
theorem CooperativeGame.inCore_toCostSharingGame_iff {A : Type*} [Fintype A]
    (G : CooperativeGame A) (x : A → ℝ) :
    G.toCostSharingGame.InCore (-x) ↔ G.InCore x := by
  simp only [CostSharingGame.InCore, CostSharingGame.IsCoreFeasible, InCore,
    toCostSharingGame_cost, Pi.neg_apply, Finset.sum_neg_distrib, neg_inj, neg_le_neg_iff]

@[simp]
theorem CostSharingGame.inCore_toCooperativeGame_iff {A : Type*} [Fintype A]
    (G : CostSharingGame A) (α : A → ℝ) :
    G.toCooperativeGame.InCore (-α) ↔ G.InCore α := by
  simp only [CooperativeGame.InCore, CostSharingGame.InCore, CostSharingGame.IsCoreFeasible,
    toCooperativeGame_val, Pi.neg_apply, Finset.sum_neg_distrib, neg_inj, neg_le_neg_iff]

theorem CooperativeGame.nonemptyCore_toCostSharingGame_iff {A : Type*} [Fintype A]
    (G : CooperativeGame A) :
    G.toCostSharingGame.NonemptyCore ↔ G.NonemptyCore := by
  refine ⟨fun ⟨α, hα⟩ => ⟨-α, ?_⟩, fun ⟨x, hx⟩ => ⟨-x, (G.inCore_toCostSharingGame_iff x).2 hx⟩⟩
  rw [← G.inCore_toCostSharingGame_iff (-α), neg_neg]
  exact hα

theorem CostSharingGame.nonemptyCore_toCooperativeGame_iff {A : Type*} [Fintype A]
    (G : CostSharingGame A) :
    G.toCooperativeGame.NonemptyCore ↔ G.NonemptyCore := by
  have h := G.toCooperativeGame.nonemptyCore_toCostSharingGame_iff
  rw [G.toCooperativeGame_toCostSharingGame] at h
  exact h.symm

/-! ## Balanced weights and weak duality -/

/-- A weight vector `w : Finset A → ℝ` is a **balanced collection of weights** ([JainMahdian2007],
Definition 15.5) if `w S ≥ 0` for all `S` and `∑_{S : j ∈ S} w S = 1` for every agent `j : A`. -/
@[expose] def IsBalancedWeights {A : Type*} [Fintype A] [DecidableEq A]
    (w : Finset A → ℝ) : Prop :=
  (∀ S : Finset A, 0 ≤ w S) ∧ ∀ j : A, (∑ S with j ∈ S, w S) = 1

/-- The trivial balanced weight collection putting weight `1` on `Finset.univ` and `0` elsewhere. -/
theorem isBalancedWeights_univ {A : Type*} [Fintype A] [DecidableEq A] :
    IsBalancedWeights (fun S : Finset A => if S = Finset.univ then 1 else 0) := by
  refine ⟨fun S => by dsimp only; split_ifs <;> norm_num, fun j => ?_⟩
  simp

/-- Weighted coalition sum identity: for any `α : A → ℝ` and balanced weights `w`,
`∑ S, w S * (∑ j ∈ S, α j) = ∑ j, α j`. -/
theorem IsBalancedWeights.sum_mul_sum_eq {A : Type*} [Fintype A] [DecidableEq A]
    {w : Finset A → ℝ} (hw : IsBalancedWeights w) (α : A → ℝ) :
    ∑ S : Finset A, w S * (∑ j ∈ S, α j) = ∑ j : A, α j := by
  calc
    ∑ S : Finset A, w S * (∑ j ∈ S, α j)
      = ∑ S : Finset A, ∑ j : A, if j ∈ S then w S * α j else 0 := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext j
        simp
    _ = ∑ j : A, ∑ S : Finset A, if j ∈ S then w S * α j else 0 := Finset.sum_comm
    _ = ∑ j : A, (∑ S with j ∈ S, w S) * α j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul, ← Finset.sum_filter]
    _ = ∑ j : A, α j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hw.2 j, one_mul]

/-- Weak duality for `γ`-approximate core allocations: if `α` lies in the `γ`-core of `G`, then
every balanced weight collection `w` satisfies `γ * G.cost univ ≤ ∑ S, w S * G.cost S`. -/
theorem CostSharingGame.InApproxCore.mul_le_sum_balanced {A : Type*} [Fintype A] [DecidableEq A]
    {G : CostSharingGame A} {γ : ℝ} {α : A → ℝ} (hα : G.InApproxCore γ α) {w : Finset A → ℝ}
    (hw : IsBalancedWeights w) :
    γ * G.cost Finset.univ ≤ ∑ S : Finset A, w S * G.cost S :=
  calc
    γ * G.cost Finset.univ ≤ ∑ j : A, α j := hα.1.1
    _ = ∑ S : Finset A, w S * (∑ j ∈ S, α j) := (hw.sum_mul_sum_eq α).symm
    _ ≤ ∑ S : Finset A, w S * G.cost S :=
      Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hα.2 S) (hw.1 S)

/-- Weak duality for exact core allocations: if `α` lies in the core of `G`, then every balanced
weight collection `w` satisfies `G.cost univ ≤ ∑ S, w S * G.cost S`. -/
theorem CostSharingGame.InCore.le_sum_balanced {A : Type*} [Fintype A] [DecidableEq A]
    {G : CostSharingGame A} {α : A → ℝ} (hα : G.InCore α) {w : Finset A → ℝ}
    (hw : IsBalancedWeights w) :
    G.cost Finset.univ ≤ ∑ S : Finset A, w S * G.cost S := by
  simpa only [one_mul] using ((G.inApproxCore_one_iff α).2 hα).mul_le_sum_balanced hw

/-! ## Cooperative facility location games -/

/-- An instance of the cooperative **facility location game** ([JainMahdian2007], Definition 15.1)
consists of facility opening costs `openCost : F → ℝ` and agent-facility connection costs
`connCost : F → A → ℝ`. Metric instances are constructed via `FacilityLocationInstance.ofMetric`
and characterized by `FacilityLocationInstance.IsMetric`. -/
structure FacilityLocationInstance (A F : Type*) where
  /-- Cost `openCost i` of opening facility `i`. -/
  openCost : F → ℝ
  /-- Cost `connCost i j` of connecting agent `j` to open facility `i`. -/
  connCost : F → A → ℝ
  /-- Facility opening costs are nonnegative. -/
  openCost_nonneg : ∀ i : F, 0 ≤ openCost i
  /-- Connection costs are nonnegative. -/
  connCost_nonneg : ∀ (i : F) (j : A), 0 ≤ connCost i j

namespace FacilityLocationInstance

variable {A F : Type*}

/-- Construct a facility location instance whose connection costs come from a (pseudo)metric space
on `A ⊕ F`, matching [JainMahdian2007], Definition 15.1 verbatim. -/
def ofMetric [PseudoMetricSpace (A ⊕ F)] (openCost : F → ℝ)
    (openCost_nonneg : ∀ i : F, 0 ≤ openCost i) : FacilityLocationInstance A F where
  openCost := openCost
  connCost i j := dist (Sum.inr i) (Sum.inl j)
  openCost_nonneg := openCost_nonneg
  connCost_nonneg _ _ := dist_nonneg

@[simp]
theorem ofMetric_openCost [PseudoMetricSpace (A ⊕ F)] (openCost : F → ℝ)
    (openCost_nonneg : ∀ i : F, 0 ≤ openCost i) (i : F) :
    (ofMetric (A := A) openCost openCost_nonneg).openCost i = openCost i := by
  rfl

@[simp]
theorem ofMetric_connCost [PseudoMetricSpace (A ⊕ F)] (openCost : F → ℝ)
    (openCost_nonneg : ∀ i : F, 0 ≤ openCost i) (i : F) (j : A) :
    (ofMetric (A := A) openCost openCost_nonneg).connCost i j =
      dist (Sum.inr i) (Sum.inl j) := by
  rfl

/-- `I` is a **metric** facility location instance if its connection costs arise as distances
`dist (inr i) (inl j)` in some pseudometric space on `A ⊕ F`
([JainMahdian2007], Definition 15.1). -/
@[expose] def IsMetric (I : FacilityLocationInstance A F) : Prop :=
  ∃ m : PseudoMetricSpace (A ⊕ F),
    ∀ (i : F) (j : A), I.connCost i j = @dist (A ⊕ F) m.toDist (Sum.inr i) (Sum.inl j)

theorem isMetric_ofMetric [PseudoMetricSpace (A ⊕ F)] (openCost : F → ℝ)
    (hopen : ∀ i : F, 0 ≤ openCost i) : (ofMetric (A := A) openCost hopen).IsMetric :=
  ⟨‹_›, fun _ _ => rfl⟩

/-- Cost of serving coalition `S` using a nonempty set `F'` of open facilities:
`(∑ i ∈ F', openCost i) + ∑ j ∈ S, min_{i ∈ F'} connCost i j`. -/
def planCost (I : FacilityLocationInstance A F) (S : Finset A) (F' : Finset F)
    (hF' : F'.Nonempty) : ℝ :=
  (∑ i ∈ F', I.openCost i) + ∑ j ∈ S, F'.inf' hF' (fun i => I.connCost i j)

theorem planCost_eq (I : FacilityLocationInstance A F) (S : Finset A) (F' : Finset F)
    (hF' : F'.Nonempty) :
    I.planCost S F' hF' =
      (∑ i ∈ F', I.openCost i) + ∑ j ∈ S, F'.inf' hF' (fun i => I.connCost i j) := by
  rfl

private theorem nonempty_attach_powerset [Fintype F] [Nonempty F] :
    ((Finset.univ : Finset F).powerset.filter Finset.Nonempty).attach.Nonempty := by
  obtain ⟨i₀⟩ := ‹Nonempty F›
  have hmem : {i₀} ∈ (Finset.univ : Finset F).powerset.filter Finset.Nonempty :=
    Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _),
      Finset.singleton_nonempty i₀⟩
  exact ⟨⟨{i₀}, hmem⟩, Finset.mem_attach _ _⟩

/-- Coalition cost `c(S) = min_{∅ ≠ F' ⊆ F} (∑_{i ∈ F'} f_i + ∑_{j ∈ S} min_{i ∈ F'} d_{ij})` for
`S` nonempty, and `0` for `S = ∅` (opening no facilities serves the empty set of clients at cost
`0`, [JainMahdian2007], Definition 15.1). -/
noncomputable def toCostSharingGame [Fintype F] [Nonempty F]
    (I : FacilityLocationInstance A F) : CostSharingGame A where
  cost S :=
    if S.Nonempty then
      ((Finset.univ : Finset F).powerset.filter Finset.Nonempty).attach.inf'
        nonempty_attach_powerset
        (fun x => I.planCost S x.1 (Finset.mem_filter.1 x.2).2)
    else 0
  cost_empty := by simp

theorem toCostSharingGame_cost_of_nonempty [Fintype F] [Nonempty F]
    (I : FacilityLocationInstance A F) {S : Finset A} (hS : S.Nonempty) :
    ∃ F' : Finset F, ∃ hF' : F'.Nonempty,
      I.toCostSharingGame.cost S = I.planCost S F' hF' := by
  simp only [toCostSharingGame, hS, ↓reduceIte]
  obtain ⟨⟨F', hmem⟩, _, heq⟩ := Finset.exists_mem_eq_inf' nonempty_attach_powerset
    (fun x => I.planCost S x.1 (Finset.mem_filter.1 x.2).2)
  exact ⟨F', (Finset.mem_filter.1 hmem).2, heq⟩

theorem toCostSharingGame_cost_le_planCost [Fintype F] [Nonempty F]
    (I : FacilityLocationInstance A F) (S : Finset A) (F' : Finset F) (hF' : F'.Nonempty) :
    I.toCostSharingGame.cost S ≤ I.planCost S F' hF' := by
  by_cases hS : S.Nonempty
  · simp only [toCostSharingGame, hS, ↓reduceIte]
    have hmem : F' ∈ (Finset.univ : Finset F).powerset.filter Finset.Nonempty :=
      Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ F'), hF'⟩
    exact Finset.inf'_le (fun x => I.planCost S x.1 (Finset.mem_filter.1 x.2).2)
      (Finset.mem_attach _ ⟨F', hmem⟩)
  · rw [Finset.not_nonempty_iff_eq_empty.1 hS, CostSharingGame.cost_empty]
    exact add_nonneg (Finset.sum_nonneg fun i _ => I.openCost_nonneg i) (by simp)

theorem le_toCostSharingGame_cost_of_nonempty [Fintype F] [Nonempty F]
    (I : FacilityLocationInstance A F) {S : Finset A} (hS : S.Nonempty) {c : ℝ}
    (h : ∀ (F' : Finset F) (hF' : F'.Nonempty), c ≤ I.planCost S F' hF') :
    c ≤ I.toCostSharingGame.cost S := by
  obtain ⟨F', hF', heq⟩ := I.toCostSharingGame_cost_of_nonempty hS
  exact heq ▸ h F' hF'

theorem toCostSharingGame_isNonneg [Fintype F] [Nonempty F]
    (I : FacilityLocationInstance A F) : I.toCostSharingGame.IsNonneg := by
  intro S
  by_cases hS : S.Nonempty
  · refine I.le_toCostSharingGame_cost_of_nonempty hS fun F' hF' => ?_
    refine add_nonneg (Finset.sum_nonneg fun i _ => I.openCost_nonneg i)
      (Finset.sum_nonneg fun j _ => ?_)
    exact (Finset.le_inf'_iff hF' _).2 fun i _ => I.connCost_nonneg i j
  · rw [Finset.not_nonempty_iff_eq_empty.1 hS, CostSharingGame.cost_empty]

/-- Cooperative facility location games have subadditive cost functions ([JainMahdian2007],
Section 15.2.2): opening `F₁ ∪ F₂` serves `S₁ ∪ S₂` at cost at most `c(S₁) + c(S₂)`. -/
theorem toCostSharingGame_isSubadditive [DecidableEq A] [Fintype F] [Nonempty F]
    (I : FacilityLocationInstance A F) : I.toCostSharingGame.IsSubadditive := by
  classical
  intro S₁ S₂ hdisj
  by_cases h₁ : S₁.Nonempty
  · by_cases h₂ : S₂.Nonempty
    · obtain ⟨F₁, hF₁, heq₁⟩ := I.toCostSharingGame_cost_of_nonempty h₁
      obtain ⟨F₂, hF₂, heq₂⟩ := I.toCostSharingGame_cost_of_nonempty h₂
      have hU : (F₁ ∪ F₂).Nonempty := hF₁.mono Finset.subset_union_left
      refine (I.toCostSharingGame_cost_le_planCost (S₁ ∪ S₂) (F₁ ∪ F₂) hU).trans ?_
      rw [heq₁, heq₂, planCost, planCost, planCost, Finset.sum_union hdisj]
      have hopen : ∑ i ∈ F₁ ∪ F₂, I.openCost i ≤
          (∑ i ∈ F₁, I.openCost i) + ∑ i ∈ F₂, I.openCost i := by
        have := Finset.sum_union_inter (s₁ := F₁) (s₂ := F₂) (f := I.openCost)
        have hnn : 0 ≤ ∑ i ∈ F₁ ∩ F₂, I.openCost i :=
          Finset.sum_nonneg fun i _ => I.openCost_nonneg i
        linarith
      have hconn₁ : ∑ j ∈ S₁, (F₁ ∪ F₂).inf' hU (fun i => I.connCost i j) ≤
          ∑ j ∈ S₁, F₁.inf' hF₁ (fun i => I.connCost i j) :=
        Finset.sum_le_sum fun j _ =>
          (Finset.le_inf'_iff hF₁ _).2 fun i hi =>
            Finset.inf'_le _ (Finset.subset_union_left hi)
      have hconn₂ : ∑ j ∈ S₂, (F₁ ∪ F₂).inf' hU (fun i => I.connCost i j) ≤
          ∑ j ∈ S₂, F₂.inf' hF₂ (fun i => I.connCost i j) :=
        Finset.sum_le_sum fun j _ =>
          (Finset.le_inf'_iff hF₂ _).2 fun i hi =>
            Finset.inf'_le _ (Finset.subset_union_right hi)
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.1 h₂]
      simp
  · rw [Finset.not_nonempty_iff_eq_empty.1 h₁]
    simp

/-- Feasibility for the standard facility location dual LP `(15.4)` ([JainMahdian2007], p. 390):
`α_j, β_{ij} ≥ 0`, `β_{ij} ≥ α_j - d_{ij}`, and `∑_{j ∈ A} β_{ij} ≤ f_i`. -/
@[expose] def IsDualFeasible [Fintype A] (I : FacilityLocationInstance A F)
    (α : A → ℝ) (β : F → A → ℝ) : Prop :=
  (∀ j : A, 0 ≤ α j) ∧ (∀ (i : F) (j : A), 0 ≤ β i j) ∧
    (∀ (i : F) (j : A), α j - I.connCost i j ≤ β i j) ∧
    ∀ i : F, ∑ j : A, β i j ≤ I.openCost i

/-- **Proposition 15.10** ([JainMahdian2007], p. 390): for any feasible solution `(α, β)` of the
facility-location dual LP `(15.4)`, `α` satisfies the core property of the facility location
game. -/
theorem IsDualFeasible.isCoreFeasible [Fintype A] [Fintype F] [Nonempty F]
    {I : FacilityLocationInstance A F} {α : A → ℝ} {β : F → A → ℝ}
    (h : I.IsDualFeasible α β) : I.toCostSharingGame.IsCoreFeasible α := by
  classical
  obtain ⟨_, hβ, hdiff, hopen⟩ := h
  intro S
  by_cases hS : S.Nonempty
  · refine I.le_toCostSharingGame_cost_of_nonempty hS fun F' hF' => ?_
    have hex : ∀ j : A, ∃ i ∈ F', F'.inf' hF' (fun k => I.connCost k j) = I.connCost i j :=
      fun j => Finset.exists_mem_eq_inf' hF' (fun k => I.connCost k j)
    choose assign hassign_mem hassign_eq using hex
    have hpart : ∑ j ∈ S, α j = ∑ i ∈ F', ∑ j ∈ S.filter (fun j => assign j = i), α j :=
      (Finset.sum_fiberwise_of_maps_to (fun j _ => hassign_mem j) α).symm
    have hpart_conn :
        ∑ j ∈ S, F'.inf' hF' (fun k => I.connCost k j) =
          ∑ i ∈ F', ∑ j ∈ S.filter (fun j => assign j = i), I.connCost i j := by
      calc
        ∑ j ∈ S, F'.inf' hF' (fun k => I.connCost k j)
          = ∑ j ∈ S, I.connCost (assign j) j := Finset.sum_congr rfl fun j _ => hassign_eq j
        _ = ∑ i ∈ F', ∑ j ∈ S.filter (fun j => assign j = i), I.connCost (assign j) j :=
            (Finset.sum_fiberwise_of_maps_to (fun j _ => hassign_mem j)
              (fun j => I.connCost (assign j) j)).symm
        _ = ∑ i ∈ F', ∑ j ∈ S.filter (fun j => assign j = i), I.connCost i j := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
            rw [(Finset.mem_filter.1 hj).2]
    rw [planCost, hpart, hpart_conn, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    set R := S.filter (fun j => assign j = i)
    have hRβ : ∑ j ∈ R, (α j - I.connCost i j) ≤ I.openCost i :=
      calc
        ∑ j ∈ R, (α j - I.connCost i j) ≤ ∑ j ∈ R, β i j :=
          Finset.sum_le_sum fun j _ => hdiff i j
        _ ≤ ∑ j : A, β i j :=
          Finset.sum_le_univ_sum_of_nonneg fun j => hβ i j
        _ ≤ I.openCost i := hopen i
    rw [Finset.sum_sub_distrib] at hRβ
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.1 hS]
    simp

/-! ## Canonical examples: Examples 15.2 & 15.4 and empty-core facility location -/

/-- Vertex positions on `ℝ` realizing the metric graph of **Example 15.2** (Figure 15.1 of
[JainMahdian2007], p. 386): agents `a, b, c` (`Fin 3`) sit at `-2, 2, 4` and facilities `f₁, f₂`
(`Fin 2`) sit at `0, 3`, giving `d(f₁, a) = 2`, `d(f₁, b) = 2`, `d(f₁, c) = 4`, `d(f₂, a) = 5`,
`d(f₂, b) = 1`, `d(f₂, c) = 1`. -/
private def example15_2_pos : Fin 3 ⊕ Fin 2 → ℝ
  | .inl 0 => -2
  | .inl 1 => 2
  | .inl 2 => 4
  | .inr 0 => 0
  | .inr 1 => 3

private noncomputable local instance example15_2_metric : PseudoMetricSpace (Fin 3 ⊕ Fin 2) :=
  PseudoMetricSpace.induced example15_2_pos inferInstance

/-- **Example 15.2** ([JainMahdian2007], Figure 15.1, pp. 386–387): 3 agents `{0, 1, 2}`
(`{a, b, c}`) and 2 facilities `{0, 1}` of opening cost `2` each, with metric distances induced by
the line/path embedding `example15_2_pos`. -/
noncomputable def example15_2 : FacilityLocationInstance (Fin 3) (Fin 2) :=
  @ofMetric (Fin 3) (Fin 2) example15_2_metric (fun _ => 2) (fun _ => by norm_num)

theorem example15_2_isMetric : example15_2.IsMetric :=
  ⟨example15_2_metric, fun _ _ => rfl⟩

@[simp]
theorem example15_2_openCost (i : Fin 2) : example15_2.openCost i = 2 := by
  rfl

theorem example15_2_connCost :
    example15_2.connCost 0 0 = 2 ∧ example15_2.connCost 0 1 = 2 ∧
    example15_2.connCost 0 2 = 4 ∧ example15_2.connCost 1 0 = 5 ∧
    example15_2.connCost 1 1 = 1 ∧ example15_2.connCost 1 2 = 1 := by
  simp only [example15_2, ofMetric]
  change |example15_2_pos (.inr 0) - example15_2_pos (.inl 0)| = 2 ∧
    |example15_2_pos (.inr 0) - example15_2_pos (.inl 1)| = 2 ∧
    |example15_2_pos (.inr 0) - example15_2_pos (.inl 2)| = 4 ∧
    |example15_2_pos (.inr 1) - example15_2_pos (.inl 0)| = 5 ∧
    |example15_2_pos (.inr 1) - example15_2_pos (.inl 1)| = 1 ∧
    |example15_2_pos (.inr 1) - example15_2_pos (.inl 2)| = 1
  simp only [example15_2_pos]
  norm_num

private theorem fin2_nonempty_subsets (F' : Finset (Fin 2)) (hF' : F'.Nonempty) :
    F' = {0} ∨ F' = {1} ∨ F' = {0, 1} := by
  have h01 : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by fin_cases x <;> simp
  by_cases h0 : (0 : Fin 2) ∈ F' <;> by_cases h1 : (1 : Fin 2) ∈ F'
  · right; right; ext x; rcases h01 x with rfl | rfl <;> simp [h0, h1]
  · left; ext x; rcases h01 x with rfl | rfl <;> simp [h0, h1]
  · right; left; ext x; rcases h01 x with rfl | rfl <;> simp [h0, h1]
  · obtain ⟨x, hx⟩ := hF'
    rcases h01 x with rfl | rfl <;> contradiction

private theorem example15_2_planCost_eval (S : Finset (Fin 3)) :
    example15_2.planCost S {0} (by simp) = 2 + ∑ j ∈ S, example15_2.connCost 0 j ∧
    example15_2.planCost S {1} (by simp) = 2 + ∑ j ∈ S, example15_2.connCost 1 j ∧
    example15_2.planCost S {0, 1} (by simp) =
      4 + ∑ j ∈ S, min (example15_2.connCost 0 j) (example15_2.connCost 1 j) := by
  refine ⟨by simp [planCost], by simp [planCost], ?_⟩
  simp only [planCost, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1), example15_2_openCost]
  have hsum : ∑ j ∈ S, ({0, 1} : Finset (Fin 2)).inf' (by simp)
      (fun i => example15_2.connCost i j) =
      ∑ j ∈ S, min (example15_2.connCost 0 j) (example15_2.connCost 1 j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.inf'_insert (H := Finset.singleton_nonempty 1), Finset.inf'_singleton]
  linarith

/-- Exact coalition cost table of **Example 15.2** ([JainMahdian2007], p. 387):
`c({a}) = 4`, `c({b}) = 3`, `c({c}) = 3`, `c({a, b}) = 6`, `c({b, c}) = 4`, `c({a, c}) = 7`,
`c({a, b, c}) = 8`. -/
theorem example15_2_cost :
    example15_2.toCostSharingGame.cost {0} = 4 ∧
    example15_2.toCostSharingGame.cost {1} = 3 ∧
    example15_2.toCostSharingGame.cost {2} = 3 ∧
    example15_2.toCostSharingGame.cost {0, 1} = 6 ∧
    example15_2.toCostSharingGame.cost {1, 2} = 4 ∧
    example15_2.toCostSharingGame.cost {0, 2} = 7 ∧
    example15_2.toCostSharingGame.cost Finset.univ = 8 := by
  obtain ⟨hc00, hc01, hc02, hc10, hc11, hc12⟩ := example15_2_connCost
  have eval_set : ∀ (S : Finset (Fin 3)) (hS : S.Nonempty) (v : ℝ),
      2 + (∑ j ∈ S, example15_2.connCost 0 j) ≥ v →
      2 + (∑ j ∈ S, example15_2.connCost 1 j) ≥ v →
      4 + (∑ j ∈ S, min (example15_2.connCost 0 j) (example15_2.connCost 1 j)) ≥ v →
      (2 + (∑ j ∈ S, example15_2.connCost 0 j) = v ∨
       2 + (∑ j ∈ S, example15_2.connCost 1 j) = v ∨
       4 + (∑ j ∈ S, min (example15_2.connCost 0 j) (example15_2.connCost 1 j)) = v) →
      example15_2.toCostSharingGame.cost S = v := by
    intro S hS v h0 h1 h01 hatt
    obtain ⟨p0, p1, p01⟩ := example15_2_planCost_eval S
    refine le_antisymm ?_ (example15_2.le_toCostSharingGame_cost_of_nonempty hS fun F' hF' => ?_)
    · rcases hatt with e | e | e
      · exact (example15_2.toCostSharingGame_cost_le_planCost S {0} (by simp)).trans_eq
          (p0.trans e)
      · exact (example15_2.toCostSharingGame_cost_le_planCost S {1} (by simp)).trans_eq
          (p1.trans e)
      · exact (example15_2.toCostSharingGame_cost_le_planCost S {0, 1} (by simp)).trans_eq
          (p01.trans e)
    · rcases fin2_nonempty_subsets F' hF' with rfl | rfl | rfl
      · linarith
      · linarith
      · linarith
  have eval_pair : ∀ (a b : Fin 3) (hab : a ≠ b) (v : ℝ),
      2 + (example15_2.connCost 0 a + example15_2.connCost 0 b) ≥ v →
      2 + (example15_2.connCost 1 a + example15_2.connCost 1 b) ≥ v →
      4 + (min (example15_2.connCost 0 a) (example15_2.connCost 1 a) +
           min (example15_2.connCost 0 b) (example15_2.connCost 1 b)) ≥ v →
      (2 + (example15_2.connCost 0 a + example15_2.connCost 0 b) = v ∨
       2 + (example15_2.connCost 1 a + example15_2.connCost 1 b) = v ∨
       4 + (min (example15_2.connCost 0 a) (example15_2.connCost 1 a) +
            min (example15_2.connCost 0 b) (example15_2.connCost 1 b)) = v) →
      example15_2.toCostSharingGame.cost {a, b} = v := fun a b hab v h0 h1 h01 hatt =>
    eval_set {a, b} (by simp) v
      (by rw [Finset.sum_pair hab]; exact h0)
      (by rw [Finset.sum_pair hab]; exact h1)
      (by rw [Finset.sum_pair hab]; exact h01)
      (by simp only [Finset.sum_pair hab]; exact hatt)
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact eval_set {0} (by simp) 4 (by norm_num [hc00]) (by norm_num [hc10])
      (by norm_num [hc00, hc10]) (.inl (by norm_num [hc00]))
  · exact eval_set {1} (by simp) 3 (by norm_num [hc01]) (by norm_num [hc11])
      (by norm_num [hc01, hc11]) (.inr (.inl (by norm_num [hc11])))
  · exact eval_set {2} (by simp) 3 (by norm_num [hc02]) (by norm_num [hc12])
      (by norm_num [hc02, hc12]) (.inr (.inl (by norm_num [hc12])))
  · exact eval_pair 0 1 (by decide) 6 (by norm_num [hc00, hc01]) (by norm_num [hc10, hc11])
      (by norm_num [hc00, hc01, hc10, hc11]) (.inl (by norm_num [hc00, hc01]))
  · exact eval_pair 1 2 (by decide) 4 (by norm_num [hc01, hc02]) (by norm_num [hc11, hc12])
      (by norm_num [hc01, hc02, hc11, hc12]) (.inr (.inl (by norm_num [hc11, hc12])))
  · exact eval_pair 0 2 (by decide) 7 (by norm_num [hc00, hc02]) (by norm_num [hc10, hc12])
      (by norm_num [hc00, hc02, hc10, hc12]) (.inr (.inr (by norm_num [hc00, hc02, hc10, hc12])))
  · rw [huniv]
    have hsum3 : ∀ f : Fin 3 → ℝ,
        ∑ j ∈ ({0, 1, 2} : Finset (Fin 3)), f j = f 0 + f 1 + f 2 := by
      intro f
      rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
      ring
    exact eval_set {0, 1, 2} (by simp) 8
      (by rw [hsum3]; norm_num [hc00, hc01, hc02])
      (by rw [hsum3]; norm_num [hc10, hc11, hc12])
      (by rw [hsum3]; norm_num [hc00, hc01, hc02, hc10, hc11, hc12])
      (.inr (.inr (by rw [hsum3]; norm_num [hc00, hc01, hc02, hc10, hc11, hc12])))

private theorem fin3_subsets (S : Finset (Fin 3)) :
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 1} ∨ S = {1, 2} ∨ S = {0, 2} ∨
      S = {0, 1, 2} := by
  have h012 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := fun x => by fin_cases x <;> simp
  by_cases h0 : (0 : Fin 3) ∈ S <;> by_cases h1 : (1 : Fin 3) ∈ S <;> by_cases h2 : (2 : Fin 3) ∈ S
  · right; right; right; right; right; right; right
    ext x; rcases h012 x with rfl | rfl | rfl <;> simp [h0, h1, h2]
  · right; right; right; right; left
    ext x; rcases h012 x with rfl | rfl | rfl <;> simp [h0, h1, h2]
  · right; right; right; right; right; right; left
    ext x; rcases h012 x with rfl | rfl | rfl <;> simp [h0, h1, h2]
  · right; left
    ext x; rcases h012 x with rfl | rfl | rfl <;> simp [h0, h1, h2]
  · right; right; right; right; right; left
    ext x; rcases h012 x with rfl | rfl | rfl <;> simp [h0, h1, h2]
  · right; right; left
    ext x; rcases h012 x with rfl | rfl | rfl <;> simp [h0, h1, h2]
  · right; right; right; left
    ext x; rcases h012 x with rfl | rfl | rfl <;> simp [h0, h1, h2]
  · left
    ext x; rcases h012 x with rfl | rfl | rfl <;> simp [h0, h1, h2]

private theorem example15_2_inCore_of_bounds {α : Fin 3 → ℝ}
    (hsum : α 0 + α 1 + α 2 = 8) (hα0 : α 0 ≤ 4) (hα1 : α 1 ≤ 3) (hα2 : α 2 ≤ 3)
    (hα01 : α 0 + α 1 ≤ 6) (hα12 : α 1 + α 2 ≤ 4) (hα02 : α 0 + α 2 ≤ 7) :
    example15_2.toCostSharingGame.InCore α := by
  obtain ⟨h0, h1, h2, h01, h12, h02, huniv⟩ := example15_2_cost
  have huniv3 : ({0, 1, 2} : Finset (Fin 3)) = Finset.univ := by decide
  refine ⟨by rw [Fin.sum_univ_three, huniv]; exact hsum, fun S => ?_⟩
  rcases fin3_subsets S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simpa [h0] using hα0
  · simpa [h1] using hα1
  · simpa [h2] using hα2
  · rw [Finset.sum_pair (by decide), h01]; exact hα01
  · rw [Finset.sum_pair (by decide), h12]; exact hα12
  · rw [Finset.sum_pair (by decide), h02]; exact hα02
  · rw [huniv3, Fin.sum_univ_three, huniv]; exact hsum.le

/-- **Example 15.4** ([JainMahdian2007], p. 387): the cost allocation `(4, 2, 2)` lies in the core
of `example15_2`. -/
theorem example15_2_inCore_four_two_two :
    example15_2.toCostSharingGame.InCore ![4, 2, 2] :=
  example15_2_inCore_of_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- **Example 15.4** ([JainMahdian2007], p. 388): the cost allocation `(4, 1, 3)` also lies in the
core of `example15_2`. -/
theorem example15_2_inCore_four_one_three :
    example15_2.toCostSharingGame.InCore ![4, 1, 3] :=
  example15_2_inCore_of_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The 3-facility bipartite connection table described in **Example 15.4** ([JainMahdian2007],
pp. 388–389): adding a third facility of opening cost `3` with distance `1` to `a` (`0`) and `c`
(`2`) and distance `4` to `b` (`1`) while keeping `f₁, f₂` distances unchanged (`d(f₂, a) = 5`).

*Source note:* if `d` is re-closed under the metric triangle inequality on `A ∪ F`, then
`d(f₂, a) ≤ d(f₂, c) + d(f₃, c) + d(f₃, a) = 3`, which lowers `c({a, b, c})` from `8` to `7` (by
opening `f₂` alone) and restores a nonempty core `(3, 2, 2)`. Below we also provide
`emptyCoreMetricFL`, a genuine 6-vertex (`3` agents, `3` facilities) metric instance with the exact
same `(15 / 16)` integrality gap (`7.5 < 8`). -/
def emptyCoreBipartiteFL : FacilityLocationInstance (Fin 3) (Fin 3) where
  openCost := ![2, 2, 3]
  connCost i j := ![![2, 2, 4], ![5, 1, 1], ![1, 4, 1]] i j
  openCost_nonneg i := by fin_cases i <;> norm_num
  connCost_nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num

/-- Shortest-path distance on the 6-vertex bipartite graph `K_{3,3} \ M` (`Fin 3 ⊕ Fin 3`, where
facility `i` connects to agent `j` at unit length iff `i ≠ j`): distinct same-side vertices have
distance `2`, connected agent-facility pairs (`i ≠ j`) have distance `1`, and opposite pairs
(`i = j`) have distance `3`. -/
private def k33MinusMatchingDist : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3 → ℝ
  | x, y =>
    if x = y then 0
    else match x, y with
      | .inl _, .inl _ => 2
      | .inr _, .inr _ => 2
      | .inl j, .inr i => if i = j then 3 else 1
      | .inr i, .inl j => if i = j then 3 else 1

private noncomputable local instance k33MinusMatchingMetric :
    PseudoMetricSpace (Fin 3 ⊕ Fin 3) where
  dist := k33MinusMatchingDist
  dist_self x := by simp [k33MinusMatchingDist]
  dist_comm x y := by
    fin_cases x <;> fin_cases y <;> simp [k33MinusMatchingDist]
  dist_triangle x y z := by
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [k33MinusMatchingDist] <;> norm_num

/-- Genuine 6-vertex (`3` agents, `3` facilities) **metric facility location instance** on the
shortest-path metric of `K_{3,3} \ M` with opening costs `3`: every pair `{j, k}` costs `5`, the
grand coalition costs `8`, the exact core (`γ = 1`) is empty, and the `(15 / 16)`-core is nonempty
and optimal. -/
noncomputable def emptyCoreMetricFL : FacilityLocationInstance (Fin 3) (Fin 3) :=
  @ofMetric (Fin 3) (Fin 3) k33MinusMatchingMetric (fun _ => 3) (fun _ => by norm_num)

theorem emptyCoreMetricFL_isMetric : emptyCoreMetricFL.IsMetric :=
  ⟨k33MinusMatchingMetric, fun _ _ => rfl⟩

/-- The symmetric pairwise balanced weight collection assigning `1 / 2` to each 2-agent coalition
`{0, 1}`, `{1, 2}`, `{0, 2}` and `0` to all other coalitions ([JainMahdian2007], p. 389). -/
private noncomputable def pairBalancedWeights (S : Finset (Fin 3)) : ℝ :=
  if S.card = 2 then 1 / 2 else 0

private theorem isBalancedWeights_pairBalancedWeights :
    IsBalancedWeights pairBalancedWeights := by
  refine ⟨fun S => by simp only [pairBalancedWeights]; split_ifs <;> norm_num, fun j => ?_⟩
  have huniv_sets : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {1, 2}, {0, 2}, Finset.univ} := by decide
  rw [Finset.sum_filter, huniv_sets]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  fin_cases j <;> norm_num [pairBalancedWeights]

private theorem emptyCoreMetricFL_connCost (i j : Fin 3) :
    emptyCoreMetricFL.connCost i j = if i = j then 3 else 1 := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem emptyCoreMetricFL_pair_and_univ_cost :
    emptyCoreMetricFL.toCostSharingGame.cost {0, 1} ≤ 5 ∧
    emptyCoreMetricFL.toCostSharingGame.cost {1, 2} ≤ 5 ∧
    emptyCoreMetricFL.toCostSharingGame.cost {0, 2} ≤ 5 ∧
    emptyCoreMetricFL.toCostSharingGame.cost Finset.univ = 8 := by
  have hopen : ∀ i : Fin 3, emptyCoreMetricFL.openCost i = 3 := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (emptyCoreMetricFL.toCostSharingGame_cost_le_planCost {0, 1} {2} (by simp)).trans ?_
    rw [planCost, Finset.sum_singleton, hopen, Finset.sum_pair (by decide)]
    simp only [Finset.inf'_singleton, emptyCoreMetricFL_connCost]
    norm_num
  · refine (emptyCoreMetricFL.toCostSharingGame_cost_le_planCost {1, 2} {0} (by simp)).trans ?_
    rw [planCost, Finset.sum_singleton, hopen, Finset.sum_pair (by decide)]
    simp only [Finset.inf'_singleton, emptyCoreMetricFL_connCost]
    norm_num
  · refine (emptyCoreMetricFL.toCostSharingGame_cost_le_planCost {0, 2} {1} (by simp)).trans ?_
    rw [planCost, Finset.sum_singleton, hopen, Finset.sum_pair (by decide)]
    simp only [Finset.inf'_singleton, emptyCoreMetricFL_connCost]
    norm_num
  · refine le_antisymm ?_
      (emptyCoreMetricFL.le_toCostSharingGame_cost_of_nonempty Finset.univ_nonempty fun F' hF' =>
        ?_)
    · refine (emptyCoreMetricFL.toCostSharingGame_cost_le_planCost Finset.univ {0}
        (by simp)).trans ?_
      rw [planCost, Finset.sum_singleton, hopen, Fin.sum_univ_three]
      simp only [Finset.inf'_singleton, emptyCoreMetricFL_connCost]
      norm_num
    · rw [planCost, Fin.sum_univ_three]
      have hopen_sum : ∑ i ∈ F', emptyCoreMetricFL.openCost i = 3 * (F'.card : ℝ) := by
        simp [hopen, nsmul_eq_mul, mul_comm]
      rw [hopen_sum]
      rcases fin3_subsets F' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp at hF'
      · simp [emptyCoreMetricFL_connCost]; norm_num
      · simp [emptyCoreMetricFL_connCost]; norm_num
      · simp [emptyCoreMetricFL_connCost]; norm_num
      · simp [Finset.inf'_insert (H := Finset.singleton_nonempty _),
          emptyCoreMetricFL_connCost]; norm_num
      · simp [Finset.inf'_insert (H := Finset.singleton_nonempty _),
          emptyCoreMetricFL_connCost]; norm_num
      · simp [Finset.inf'_insert (H := Finset.singleton_nonempty _),
          emptyCoreMetricFL_connCost]; norm_num
      · simp [Finset.inf'_insert (H := Finset.insert_nonempty _ _),
          Finset.inf'_insert (H := Finset.singleton_nonempty _),
          emptyCoreMetricFL_connCost]; norm_num

private theorem emptyCoreMetricFL_weighted_sum_le :
    ∑ S : Finset (Fin 3), pairBalancedWeights S * emptyCoreMetricFL.toCostSharingGame.cost S ≤
      15 / 2 := by
  obtain ⟨h01, h12, h02, -⟩ := emptyCoreMetricFL_pair_and_univ_cost
  have huniv_sets : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {1, 2}, {0, 2}, Finset.univ} := by decide
  rw [huniv_sets]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  have hp0 : pairBalancedWeights ∅ = 0 := by norm_num [pairBalancedWeights]
  have hp1 : pairBalancedWeights {0} = 0 := by norm_num [pairBalancedWeights]
  have hp2 : pairBalancedWeights {1} = 0 := by norm_num [pairBalancedWeights]
  have hp3 : pairBalancedWeights {2} = 0 := by norm_num [pairBalancedWeights]
  have hp4 : pairBalancedWeights {0, 1} = 1 / 2 := by norm_num [pairBalancedWeights]
  have hp5 : pairBalancedWeights {1, 2} = 1 / 2 := by norm_num [pairBalancedWeights]
  have hp6 : pairBalancedWeights {0, 2} = 1 / 2 := by norm_num [pairBalancedWeights]
  have hp7 : pairBalancedWeights Finset.univ = 0 := by norm_num [pairBalancedWeights]
  rw [hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7]
  linarith

/-- Grand-coalition cost `c(univ) = 8` for the 6-vertex metric facility location game
`emptyCoreMetricFL`. -/
theorem emptyCoreMetricFL_cost_univ :
    emptyCoreMetricFL.toCostSharingGame.cost Finset.univ = 8 :=
  emptyCoreMetricFL_pair_and_univ_cost.2.2.2

/-- For every `γ > 15 / 16`, the `γ`-core of `emptyCoreMetricFL` is empty. -/
theorem emptyCoreMetricFL_not_nonemptyApproxCore_of_gt {γ : ℝ} (hγ : 15 / 16 < γ) :
    ¬ emptyCoreMetricFL.toCostSharingGame.NonemptyApproxCore γ := by
  rintro ⟨α, hα⟩
  have hle := hα.mul_le_sum_balanced isBalancedWeights_pairBalancedWeights
  have hsum := emptyCoreMetricFL_weighted_sum_le
  rw [emptyCoreMetricFL_cost_univ] at hle
  linarith

/-- The 6-vertex metric facility location game `emptyCoreMetricFL` has an **empty exact core**
(`γ = 1` fails): pairwise balanced weights sum to at most `7.5 < 8 = c(univ)`. -/
theorem emptyCoreMetricFL_not_nonemptyCore :
    ¬ emptyCoreMetricFL.toCostSharingGame.NonemptyCore :=
  fun h => emptyCoreMetricFL_not_nonemptyApproxCore_of_gt (by norm_num : (15 / 16 : ℝ) < 1)
    ((emptyCoreMetricFL.toCostSharingGame.nonemptyApproxCore_one_iff).2 h)

/-- The symmetric allocation `(5 / 2, 5 / 2, 5 / 2)` lies in the `(15 / 16)`-core of
`emptyCoreMetricFL` (verified via **Proposition 15.10** with `α_j = 5 / 2` and
`β_{ij} = max(0, α_j - d_{ij}) = 3 / 2` for `i ≠ j`). -/
theorem emptyCoreMetricFL_inApproxCore :
    emptyCoreMetricFL.toCostSharingGame.InApproxCore (15 / 16) (fun _ => 5 / 2) := by
  have huniv := emptyCoreMetricFL_pair_and_univ_cost.2.2.2
  have hdual : emptyCoreMetricFL.IsDualFeasible (fun _ => 5 / 2)
      (fun i j => if i = j then 0 else 3 / 2) := by
    refine ⟨fun _ => by norm_num,
      fun i j => by by_cases h : i = j <;> (simp only [h, ↓reduceIte]; norm_num),
      fun i j => ?_, fun i => ?_⟩
    · rw [emptyCoreMetricFL_connCost]
      by_cases h : i = j <;> (simp only [h, ↓reduceIte]; norm_num)
    · rw [Fin.sum_univ_three]
      have hopen : emptyCoreMetricFL.openCost i = 3 := rfl
      rw [hopen]
      fin_cases i <;> norm_num
  refine ⟨⟨by rw [Fin.sum_univ_three, huniv]; norm_num,
    by rw [Fin.sum_univ_three, huniv]; norm_num⟩, hdual.isCoreFeasible⟩

/-- Grand-coalition cost `c(univ) = 8` for `emptyCoreBipartiteFL` ([JainMahdian2007],
pp. 388–389). -/
theorem emptyCoreBipartiteFL_cost_univ :
    emptyCoreBipartiteFL.toCostSharingGame.cost Finset.univ = 8 := by
  refine le_antisymm ?_
    (emptyCoreBipartiteFL.le_toCostSharingGame_cost_of_nonempty Finset.univ_nonempty
      fun F' hF' => ?_)
  · refine (emptyCoreBipartiteFL.toCostSharingGame_cost_le_planCost Finset.univ {0, 1}
      (by simp)).trans ?_
    rw [planCost, Finset.sum_pair (by decide), Fin.sum_univ_three]
    simp [Finset.inf'_insert (H := Finset.singleton_nonempty _),
      emptyCoreBipartiteFL]
    norm_num
  · rw [planCost, Fin.sum_univ_three]
    rcases fin3_subsets F' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hF'
    · simp [emptyCoreBipartiteFL]; norm_num
    · simp [emptyCoreBipartiteFL]; norm_num
    · simp [emptyCoreBipartiteFL]; norm_num
    · rw [Finset.sum_pair (by decide)]
      simp [Finset.inf'_insert (H := Finset.singleton_nonempty _),
        emptyCoreBipartiteFL]; norm_num
    · rw [Finset.sum_pair (by decide)]
      simp [Finset.inf'_insert (H := Finset.singleton_nonempty _),
        emptyCoreBipartiteFL]; norm_num
    · rw [Finset.sum_pair (by decide)]
      simp [Finset.inf'_insert (H := Finset.singleton_nonempty _),
        emptyCoreBipartiteFL]; norm_num
    · rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
      simp [Finset.inf'_insert (H := Finset.insert_nonempty _ _),
        Finset.inf'_insert (H := Finset.singleton_nonempty _),
        emptyCoreBipartiteFL]; norm_num

/-- For every `γ > 15 / 16` (`7.5 / 8`), the `γ`-core of `emptyCoreBipartiteFL` is empty
([JainMahdian2007], p. 389). -/
theorem emptyCoreBipartiteFL_not_nonemptyApproxCore_of_gt {γ : ℝ} (hγ : 15 / 16 < γ) :
    ¬ emptyCoreBipartiteFL.toCostSharingGame.NonemptyApproxCore γ := by
  rintro ⟨α, hα⟩
  have h01 : emptyCoreBipartiteFL.toCostSharingGame.cost {0, 1} ≤ 6 :=
    (emptyCoreBipartiteFL.toCostSharingGame_cost_le_planCost {0, 1} {0} (by simp)).trans
      (by rw [planCost, Finset.sum_singleton, Finset.sum_pair (by decide)]
          simp [emptyCoreBipartiteFL]; norm_num)
  have h12 : emptyCoreBipartiteFL.toCostSharingGame.cost {1, 2} ≤ 4 :=
    (emptyCoreBipartiteFL.toCostSharingGame_cost_le_planCost {1, 2} {1} (by simp)).trans
      (by rw [planCost, Finset.sum_singleton, Finset.sum_pair (by decide)]
          simp [emptyCoreBipartiteFL]; norm_num)
  have h02 : emptyCoreBipartiteFL.toCostSharingGame.cost {0, 2} ≤ 5 :=
    (emptyCoreBipartiteFL.toCostSharingGame_cost_le_planCost {0, 2} {2} (by simp)).trans
      (by rw [planCost, Finset.sum_singleton, Finset.sum_pair (by decide)]
          simp [emptyCoreBipartiteFL]; norm_num)
  have huniv := emptyCoreBipartiteFL_cost_univ
  have c01 := hα.2 {0, 1}
  have c12 := hα.2 {1, 2}
  have c02 := hα.2 {0, 2}
  rw [Finset.sum_pair (by decide)] at c01 c12 c02
  have htot := hα.1.1
  rw [Fin.sum_univ_three, huniv] at htot
  linarith

/-- **Example 15.4** ([JainMahdian2007], pp. 388–389): on the 3-facility bipartite connection table
`emptyCoreBipartiteFL`, the exact core is empty (`7.5 < 8`). -/
theorem emptyCoreBipartiteFL_not_nonemptyCore :
    ¬ emptyCoreBipartiteFL.toCostSharingGame.NonemptyCore :=
  fun h => emptyCoreBipartiteFL_not_nonemptyApproxCore_of_gt (by norm_num : (15 / 16 : ℝ) < 1)
    ((emptyCoreBipartiteFL.toCostSharingGame.nonemptyApproxCore_one_iff).2 h)

/-- `(3.5, 2.5, 1.5)` lies in the `(15 / 16)`-core (`7.5 / 8`-core) of
`emptyCoreBipartiteFL` ([JainMahdian2007], p. 389). -/
theorem emptyCoreBipartiteFL_inApproxCore :
    emptyCoreBipartiteFL.toCostSharingGame.InApproxCore (15 / 16) ![7 / 2, 5 / 2, 3 / 2] := by
  have huniv := emptyCoreBipartiteFL_cost_univ
  have hdual : emptyCoreBipartiteFL.IsDualFeasible ![7 / 2, 5 / 2, 3 / 2]
      (fun i j => max 0 (![7 / 2, 5 / 2, 3 / 2] j - emptyCoreBipartiteFL.connCost i j)) := by
    refine ⟨fun j => by fin_cases j <;> norm_num,
      fun _ _ => le_max_left _ _,
      fun _ _ => le_max_right _ _,
      fun i => ?_⟩
    rw [Fin.sum_univ_three]
    fin_cases i <;> (simp [emptyCoreBipartiteFL]; norm_num)
  refine ⟨⟨by rw [Fin.sum_univ_three, huniv]; norm_num,
    by rw [Fin.sum_univ_three, huniv]; norm_num⟩, hdual.isCoreFeasible⟩

end FacilityLocationInstance

end Cslib.GameTheory
