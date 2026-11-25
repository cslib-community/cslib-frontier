/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.Dinitz
public import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Minimum-Cost Flows and Klein's Negative-Cycle Optimality Theorem

Formalizes minimum-cost integral network flows over arbitrary vertex balances, **Klein's
negative-cycle optimality theorem** and complementary slackness characterization ([Klein1967],
pp. 205–220, locator not re-verified against primary PDF; [Schrijver2003], Chapter 12, locator not
re-verified against primary PDF), and executable cycle-canceling algorithms.

## Model and source mapping

* **Capacitated cost networks (`CostNetwork V W`):** finite vertex type `V`, nonnegative integral
  arc capacities `cap : V → V → ℕ`, per-unit arc costs `cost : V → V → W` in a linearly ordered
  additive commutative group `W` (e.g., `ℤ`, `ℚ`, or `ℝ`), and net vertex supply balances
  `balance : V → ℤ` (`balance = 0` for circulations, `±val` at `s, t` for fixed-value `s`–`t`
  flows). Antiparallel arcs `(u, v)` and `(v, u)` with distinct costs (`cost u v ≠ -cost v u`) and
  self-loops `(v, v)` are supported directly.
* **Feasible flows (`CostNetwork.Flow`):** integral flows `0 ≤ f u v ≤ M.cap u v` satisfying exact
  balance `∑ w, f v w - ∑ u, f u v = M.balance v` at every vertex `v`.
* **Residual steps (`ResArc V`):** because antiparallel arcs may carry independent costs, residual
  steps distinguish forward increments `(u, v, true)` (`f u v < cap u v`, residual cost `+cost u v`)
  from backward cancellations `(u, v, false)` (`0 < f v u`, residual cost `-cost v u`).
* **Complementary slackness (`CompSlackness`):** node potentials `π : V → W` satisfying
  `f u v < cap u v → 0 ≤ cost u v + π u - π v` and `0 < f u v → cost u v + π u - π v ≤ 0`.
* **Source comparison:** [Klein1967], pp. 205–220 gives the negative-cycle optimality theorem and
  primal cycle-canceling algorithm; [Schrijver2003], Chapter 12 develops the complementary slackness
  and cycle-canceling characterizations over arbitrary vertex supply balances.

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.CostNetwork`, `CostNetwork.Flow`,
  `CostNetwork.Flow.totalCost`, `CostNetwork.Flow.IsMinCost`: minimum-cost flow networks,
  feasible flows, total cost, and optimality.
* `Cslib.Algorithms.Lean.MaxFlow.ResArc`, `CostNetwork.resCost`, `CostNetwork.walkCost`,
  `CostNetwork.Flow.resCap`, `CostNetwork.Flow.IsResWalk`, `CostNetwork.Flow.IsResCycle`,
  `CostNetwork.Flow.cycleBottleneck`, `CostNetwork.Flow.cancelCycle`,
  `CostNetwork.CompSlackness`: residual network, cycle cancellation, and potentials.
* `Cslib.Algorithms.Lean.MaxFlow.CostNetwork.findNegCycleOrPotential`,
  `CostNetwork.CycleCancelOutput`, `CostNetwork.cycleCancelLoop`,
  `CostNetwork.cycleCancelInt`: Bellman–Ford relaxation DP negative-cycle / potential finder and
  executable cycle-canceling solver.
* `Cslib.Algorithms.Lean.MaxFlow.CostNetwork.ofNetwork`, `Network.Flow.flowCost`,
  `Network.Flow.IsMinCostOfValue`, `Cslib.Algorithms.Lean.MaxFlow.MinCostMaxFlowOutput`,
  `Cslib.Algorithms.Lean.MaxFlow.minCostMaxFlow`: bridge to `s`–`t` flows and executable
  minimum-cost maximum-flow solver over `Fin n`.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.CostNetwork.isMinCost_iff_not_exists_negCycle`: **Klein's
  negative-cycle criterion** ([Klein1967], locator not re-verified against primary PDF): a feasible
  flow has minimum cost iff its residual network contains no negative simple cycle.
* `Cslib.Algorithms.Lean.MaxFlow.CostNetwork.isMinCost_iff_exists_compSlackness`:
  **complementary slackness theorem** ([Schrijver2003], Chapter 12, locator not re-verified against
  primary PDF): a feasible flow has minimum cost iff it admits complementary-slackness potentials.
* `Cslib.Algorithms.Lean.MaxFlow.CostNetwork.cycleCancelInt_correct`,
  `CostNetwork.exists_isMinCost_of_feasible`: correctness and pseudo-polynomial termination of
  integral cycle canceling (`≤ 2 * absCostBound` cancellations), and existence of optimal flows
  for arbitrary linearly ordered group costs `W`.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.isMinCostOfValue_iff_not_exists_negCycle`,
  `Network.Flow.isMinCostOfValue_iff_exists_compSlackness`,
  `Cslib.Algorithms.Lean.MaxFlow.minCostMaxFlow_correct`: exact specializations to fixed-value
  `s`–`t` flows and minimum-cost maximum flows.

## Cost model and scope

* `CostNetwork.cycleCancelInt` cancels an arbitrary Bellman–Ford negative residual cycle per
  iteration and proves a pseudo-polynomial cancellation bound (`≤ 2 * absCostBound M vs`) rather
  than minimum-mean cycle canceling or Word-RAM machine time.

## References

* [M. Klein, *A Primal Method for Minimal Cost Flows with Applications to the Assignment and
  Transportation Problems*][Klein1967]
* [A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*][Schrijver2003]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Finset

/-! ### Cost networks, feasible flows, and residual arcs -/

/-- A directed capacitated network with arc costs in `W` and vertex net-supply balances:
positive `balance v` is a supply, negative is a demand, and `balance = 0` is a circulation. -/
structure CostNetwork (V : Type*) (W : Type*) where
  /-- Nonnegative integral capacity of each directed arc `(u, v)`. -/
  cap : V → V → ℕ
  /-- Per-unit cost of flow on directed arc `(u, v)`. -/
  cost : V → V → W
  /-- Required net outflow `∑ w, f v w - ∑ u, f u v` at each vertex `v`. -/
  balance : V → ℤ

/-- A directed step in the residual network: `isFwd = true` increases flow on `(src, dst)`
and `isFwd = false` decreases flow on `(dst, src)`. -/
structure ResArc (V : Type*) where
  /-- Tail vertex of the residual step. -/
  src : V
  /-- Head vertex of the residual step. -/
  dst : V
  /-- `true` for a forward step `(src, dst)`; `false` for canceling reverse arc `(dst, src)`. -/
  isFwd : Bool
  deriving @[expose] DecidableEq

/-- A walk from `u` to `v` of `ResArc V` steps satisfying predicate `p`. -/
private def IsArcWalk {V : Type*} (p : ResArc V → Prop) : V → V → List (ResArc V) → Prop
  | u, v, [] => u = v
  | u, v, a :: rest => a.src = u ∧ p a ∧ IsArcWalk p a.dst v rest

private theorem isArcWalk_split_append {V : Type*} {p : ResArc V → Prop} {u w : V} :
    ∀ {as : List (ResArc V)} {b : ResArc V},
      IsArcWalk p u w (as ++ [b]) ↔ IsArcWalk p u b.src as ∧ p b ∧ b.dst = w
  | [], b => by
    simp only [List.nil_append, IsArcWalk, eq_comm]
  | a :: as, b => by
    simp only [List.cons_append, IsArcWalk, isArcWalk_split_append]
    tauto

private theorem pos_of_mem_isArcWalk {V : Type*} {p : ResArc V → Prop} {u v : V} :
    ∀ {arcs : List (ResArc V)}, IsArcWalk p u v arcs → ∀ a ∈ arcs, p a
  | [], _, _, ha => by simp at ha
  | _ :: _, ⟨_, hp, hr⟩, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hp
    · exact pos_of_mem_isArcWalk hr a ha'

private theorem list_map_sub_isArcWalk {V : Type*} [DecidableEq V] {p : ResArc V → Prop}
    {u v : V} (x : V) :
    ∀ {arcs : List (ResArc V)}, IsArcWalk p u v arcs →
      (arcs.map fun a : ResArc V =>
        (if a.src = x then (1 : ℤ) else 0) - (if a.dst = x then 1 else 0)).sum =
        (if u = x then 1 else 0) - (if v = x then 1 else 0)
  | [], huv => by subst huv; simp
  | a :: rest, ⟨hsrc, _, hrest⟩ => by
    have ih := list_map_sub_isArcWalk x hrest
    simp only [List.map_cons, List.sum_cons, hsrc] at ih ⊢
    omega

namespace CostNetwork

section Core

variable {V : Type*} {W : Type*}

/-- A feasible integral flow on `M`: bounded by `M.cap` and matching `M.balance` at every
vertex. -/
@[ext]
structure Flow [Fintype V] (M : CostNetwork V W) where
  /-- Integral flow assigned to each directed arc `(u, v)`. -/
  toFun : V → V → ℕ
  /-- Capacity bound on every directed arc. -/
  le_cap : ∀ u v, toFun u v ≤ M.cap u v
  /-- Exact vertex net-outflow conservation against `M.balance`. -/
  balance_eq : ∀ v, (∑ w, (toFun v w : ℤ)) - (∑ u, (toFun u v : ℤ)) = M.balance v

instance [Fintype V] (M : CostNetwork V W) : CoeFun M.Flow (fun _ => V → V → ℕ) :=
  ⟨Flow.toFun⟩

/-- Zero circulation on a network whose vertex balances all vanish. -/
@[expose] def Flow.zero [Fintype V] (M : CostNetwork V W) (h0 : ∀ v, M.balance v = 0) :
    M.Flow where
  toFun _ _ := 0
  le_cap _ _ := Nat.zero_le _
  balance_eq v := by simp [h0 v]

/-- Residual cost of a step `a : ResArc V`: `cost u v` forward, `-cost v u` backward. -/
@[expose] def resCost [Neg W] (M : CostNetwork V W) (a : ResArc V) : W :=
  if a.isFwd then M.cost a.src a.dst else -M.cost a.dst a.src

/-- Total cost of an arc list in the residual network. -/
@[expose] def walkCost [AddCommGroup W] (M : CostNetwork V W) (arcs : List (ResArc V)) : W :=
  (arcs.map M.resCost).sum

@[simp] theorem walkCost_nil [AddCommGroup W] (M : CostNetwork V W) :
    M.walkCost [] = 0 := rfl

@[simp] theorem walkCost_cons [AddCommGroup W] (M : CostNetwork V W) (a : ResArc V)
    (as : List (ResArc V)) : M.walkCost (a :: as) = M.resCost a + M.walkCost as := by
  simp [walkCost]

@[simp] theorem walkCost_append [AddCommGroup W] (M : CostNetwork V W)
    (as bs : List (ResArc V)) :
    M.walkCost (as ++ bs) = M.walkCost as + M.walkCost bs := by
  simp [walkCost]

variable [Fintype V] {M : CostNetwork V W}

/-- Total cost `∑ u, ∑ v, f u v • M.cost u v` of a feasible flow `f`. -/
@[expose] def Flow.totalCost [AddCommMonoid W] (f : M.Flow) : W :=
  ∑ u, ∑ v, f u v • M.cost u v

/-- `f` is a minimum-cost feasible flow on `M`. -/
@[expose] def Flow.IsMinCost [AddCommMonoid W] [LE W] (f : M.Flow) : Prop :=
  ∀ g : M.Flow, f.totalCost ≤ g.totalCost

/-- Residual capacity of step `a : ResArc V` with respect to `f`. -/
@[expose] def Flow.resCap (f : M.Flow) (a : ResArc V) : ℕ :=
  if a.isFwd then M.cap a.src a.dst - f a.src a.dst else f a.dst a.src

/-- Walk predicate in `f`'s residual network. -/
@[expose] def Flow.IsResWalk (f : M.Flow) : V → V → List (ResArc V) → Prop
  | u, v, [] => u = v
  | u, v, a :: rest => a.src = u ∧ 0 < f.resCap a ∧ f.IsResWalk a.dst v rest

private theorem isArcWalk_pos_resCap_iff (f : M.Flow) {u v : V} :
    ∀ {arcs : List (ResArc V)}, IsArcWalk (fun a => 0 < f.resCap a) u v arcs ↔ f.IsResWalk u v arcs
  | [] => Iff.rfl
  | _ :: _ => by
    simp only [IsArcWalk, Flow.IsResWalk, isArcWalk_pos_resCap_iff]

/-- `arcs` is a nonempty simple directed cycle in `f`'s residual network (distinct start
vertices, allowing self-loops `[⟨v, v, b⟩]` and 2-cycles `[⟨u, v, b₁⟩, ⟨v, u, b₂⟩]`). -/
@[expose] def Flow.IsResCycle (f : M.Flow) : List (ResArc V) → Prop
  | [] => False
  | a :: rest => f.IsResWalk a.src a.src (a :: rest) ∧ ((a :: rest).map ResArc.src).Nodup

instance instDecidableIsResWalk [DecidableEq V] (f : M.Flow) (u v : V) :
    ∀ arcs : List (ResArc V), Decidable (f.IsResWalk u v arcs)
  | [] => inferInstanceAs (Decidable (u = v))
  | a :: rest =>
    let _ := instDecidableIsResWalk f a.dst v rest
    inferInstanceAs (Decidable (a.src = u ∧ 0 < f.resCap a ∧ f.IsResWalk a.dst v rest))

instance instDecidableIsResCycle [DecidableEq V] (f : M.Flow) :
    ∀ arcs : List (ResArc V), Decidable (f.IsResCycle arcs)
  | [] => inferInstanceAs (Decidable False)
  | a :: rest =>
    let _ := instDecidableIsResWalk f a.src a.src (a :: rest)
    inferInstanceAs (Decidable (f.IsResWalk a.src a.src (a :: rest) ∧
      ((a :: rest).map ResArc.src).Nodup))

/-- Minimum residual capacity along a list of residual arcs (`0` when empty). -/
@[expose] def Flow.cycleBottleneck (f : M.Flow) : List (ResArc V) → ℕ
  | [] => 0
  | a :: as => as.foldl (fun acc b => min acc (f.resCap b)) (f.resCap a)

/-- Complementary slackness optimality condition for `f` and potentials `π : V → W`. -/
@[expose] def CompSlackness [AddCommGroup W] [LE W] (M : CostNetwork V W) (f : M.Flow)
    (π : V → W) : Prop :=
  (∀ u v, f u v < M.cap u v → 0 ≤ M.cost u v + π u - π v) ∧
    (∀ u v, 0 < f u v → M.cost u v + π u - π v ≤ 0)

end Core

/-! ### Residual walks, bottleneck, and cycle cancellation -/

section CycleOps

variable {V : Type*} {W : Type*} [Fintype V] {M : CostNetwork V W}

theorem Flow.isResCycle_nodup {f : M.Flow} {arcs : List (ResArc V)} (h : f.IsResCycle arcs) :
    arcs.Nodup := by
  cases arcs with
  | nil => exact h.elim
  | cons _ _ => exact List.Nodup.of_map ResArc.src h.2

theorem Flow.isResCycle_ne_nil {f : M.Flow} {arcs : List (ResArc V)} (h : f.IsResCycle arcs) :
    arcs ≠ [] := by
  cases arcs with
  | nil => exact h.elim
  | cons _ _ => exact List.cons_ne_nil _ _

theorem Flow.pos_resCap_of_mem_isResCycle {f : M.Flow} {arcs : List (ResArc V)}
    (h : f.IsResCycle arcs) {a : ResArc V} (ha : a ∈ arcs) : 0 < f.resCap a := by
  cases arcs with
  | nil => exact h.elim
  | cons _ _ => exact pos_of_mem_isArcWalk ((isArcWalk_pos_resCap_iff f).mpr h.1) a ha

theorem Flow.cycleBottleneck_le {f : M.Flow} :
    ∀ {arcs : List (ResArc V)} {a : ResArc V}, a ∈ arcs →
      f.cycleBottleneck arcs ≤ f.resCap a
  | [], _, ha => by simp at ha
  | x :: xs, a, ha => by
    unfold Flow.cycleBottleneck
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact foldl_min_le_init f.resCap xs (f.resCap a)
    · exact foldl_min_le_mem f.resCap (f.resCap x) ha'

theorem Flow.cycleBottleneck_pos {f : M.Flow} {arcs : List (ResArc V)}
    (hne : arcs ≠ []) (hpos : ∀ a ∈ arcs, 0 < f.resCap a) : 0 < f.cycleBottleneck arcs := by
  cases arcs with
  | nil => exact absurd rfl hne
  | cons x xs =>
    change 0 < xs.foldl (fun acc b => min acc (f.resCap b)) (f.resCap x)
    rcases foldl_min_eq_init_or_mem f.resCap xs (f.resCap x) with heq | ⟨a, ha, heq⟩
    · rw [heq]
      exact hpos x List.mem_cons_self
    · rw [heq]
      exact hpos a (List.mem_cons_of_mem x ha)

private theorem sum_ite_mem_src [DecidableEq V] {arcs : List (ResArc V)} (hnodup : arcs.Nodup)
    (x : V) :
    (∑ w : V, ((if ⟨x, w, true⟩ ∈ arcs then (1 : ℤ) else 0) +
      (if ⟨x, w, false⟩ ∈ arcs then (1 : ℤ) else 0))) =
      (arcs.map fun a : ResArc V => if a.src = x then (1 : ℤ) else 0).sum := by
  have hpt : ∀ a : ResArc V, (if a.src = x then (1 : ℤ) else 0) =
      ∑ w : V, ((if a = ⟨x, w, true⟩ then 1 else 0) + (if a = ⟨x, w, false⟩ then 1 else 0)) := by
    rintro ⟨s, d, b⟩
    rcases eq_or_ne s x with rfl | hs <;> cases b <;> simp [*]
  simp only [← List.sum_toFinset _ hnodup, hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', List.mem_toFinset]

private theorem sum_ite_mem_dst [DecidableEq V] {arcs : List (ResArc V)} (hnodup : arcs.Nodup)
    (x : V) :
    (∑ w : V, ((if ⟨w, x, true⟩ ∈ arcs then (1 : ℤ) else 0) +
      (if ⟨w, x, false⟩ ∈ arcs then (1 : ℤ) else 0))) =
      (arcs.map fun a : ResArc V => if a.dst = x then (1 : ℤ) else 0).sum := by
  let flip : ResArc V → ResArc V := fun a => ⟨a.dst, a.src, a.isFwd⟩
  have hflip : Function.Injective flip := Function.Involutive.injective fun ⟨_, _, _⟩ => rfl
  simp only [← List.mem_map_of_injective hflip (a := ⟨_, x, _⟩)]
  rw [sum_ite_mem_src (hnodup.map hflip) x, List.map_map]
  rfl

/-- Raw arc-flow update adding `δ` on forward arcs of `arcs` and subtracting `δ` on backward arcs
of `arcs`. -/
@[expose] def Flow.cancelCycleFun [DecidableEq V] (f : M.Flow) (arcs : List (ResArc V))
    (δ : ℕ) (u v : V) : ℕ :=
  (f u v + (if ⟨u, v, true⟩ ∈ arcs then δ else 0)) - (if ⟨v, u, false⟩ ∈ arcs then δ else 0)

private theorem Flow.cancelCycleFun_coe [DecidableEq V] (f : M.Flow) {arcs : List (ResArc V)}
    {δ : ℕ} (hδ : ∀ a ∈ arcs, δ ≤ f.resCap a) (u v : V) :
    (f.cancelCycleFun arcs δ u v : ℤ) =
      (f u v : ℤ) + (if ⟨u, v, true⟩ ∈ arcs then (δ : ℤ) else 0) -
        (if ⟨v, u, false⟩ ∈ arcs then (δ : ℤ) else 0) := by
  unfold Flow.cancelCycleFun
  by_cases h2 : (⟨v, u, false⟩ : ResArc V) ∈ arcs
  · have : δ ≤ f u v := hδ ⟨v, u, false⟩ h2
    split_ifs <;> omega
  · by_cases h1 : (⟨u, v, true⟩ : ResArc V) ∈ arcs <;> simp [h1, h2]

private theorem list_map_sum_sub {α : Type*} (f g : α → ℤ) :
    ∀ l : List α, (l.map f).sum - (l.map g).sum = (l.map fun a => f a - g a).sum
  | [] => by simp
  | a :: rs => by
    have ih := list_map_sum_sub f g rs
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Cancel `δ` units of flow around a residual cycle `arcs` (`δ ≤ f.resCap a` for all `a ∈ arcs`).
-/
@[expose] def Flow.cancelCycle [DecidableEq V] (f : M.Flow) (arcs : List (ResArc V))
    (hc : f.IsResCycle arcs) (δ : ℕ) (hδ : ∀ a ∈ arcs, δ ≤ f.resCap a) : M.Flow where
  toFun := f.cancelCycleFun arcs δ
  le_cap u v := by
    unfold Flow.cancelCycleFun
    have hle := f.le_cap u v
    split_ifs
    · have hres : δ ≤ M.cap u v - f u v := hδ ⟨u, v, true⟩ ‹_›
      omega
    · have hres : δ ≤ M.cap u v - f u v := hδ ⟨u, v, true⟩ ‹_›
      omega
    · omega
    · exact hle
  balance_eq x := by
    have hnodup := Flow.isResCycle_nodup hc
    cases arcs with
    | nil => exact hc.elim
    | cons a₀ rest =>
      have hw : IsArcWalk (fun a => 0 < f.resCap a) a₀.src a₀.src (a₀ :: rest) :=
        (isArcWalk_pos_resCap_iff f).mpr hc.1
      have hnet :
          (∑ w : V, ((f.cancelCycleFun (a₀ :: rest) δ x w : ℤ) -
              (f.cancelCycleFun (a₀ :: rest) δ w x : ℤ))) = M.balance x := by
        have hpt : ∀ w : V,
            (f.cancelCycleFun (a₀ :: rest) δ x w : ℤ) -
                (f.cancelCycleFun (a₀ :: rest) δ w x : ℤ) =
              ((f x w : ℤ) - (f w x : ℤ)) +
                (δ : ℤ) * (((if ⟨x, w, true⟩ ∈ a₀ :: rest then (1 : ℤ) else 0) +
                  (if ⟨x, w, false⟩ ∈ a₀ :: rest then 1 else 0)) -
                  ((if ⟨w, x, true⟩ ∈ a₀ :: rest then (1 : ℤ) else 0) +
                    (if ⟨w, x, false⟩ ∈ a₀ :: rest then 1 else 0))) := by
          intro w
          rw [Flow.cancelCycleFun_coe f hδ x w, Flow.cancelCycleFun_coe f hδ w x]
          split_ifs <;> ring
        rw [Finset.sum_congr rfl fun w _ => hpt w, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_sub_distrib, sum_ite_mem_src hnodup x, sum_ite_mem_dst hnodup x]
        rw [list_map_sum_sub, list_map_sub_isArcWalk x hw, sub_self, mul_zero, add_zero]
        exact f.balance_eq x
      rwa [Finset.sum_sub_distrib] at hnet

@[simp] theorem Flow.cancelCycle_apply [DecidableEq V] (f : M.Flow) {arcs : List (ResArc V)}
    (hc : f.IsResCycle arcs) {δ : ℕ} (hδ : ∀ a ∈ arcs, δ ≤ f.resCap a) (u v : V) :
    f.cancelCycle arcs hc δ hδ u v = f.cancelCycleFun arcs δ u v := rfl

private theorem sum_resCost_ite [DecidableEq V] [AddCommGroup W] (M : CostNetwork V W)
    (arcs : List (ResArc V)) (hnodup : arcs.Nodup) :
    (∑ u : V, ∑ v : V,
      ((if ⟨u, v, true⟩ ∈ arcs then (1 : ℕ) else 0) • M.cost u v -
        (if ⟨v, u, false⟩ ∈ arcs then (1 : ℕ) else 0) • M.cost u v)) =
      M.walkCost arcs := by
  have hpt : ∀ a : ResArc V, M.resCost a = ∑ u : V, ∑ v : V,
      ((if a = ⟨u, v, true⟩ then M.cost u v else 0) -
        (if a = ⟨v, u, false⟩ then M.cost u v else 0)) := by
    rintro ⟨s, d, b⟩
    cases b <;> simp [resCost, ite_and, Finset.sum_ite_irrel]
  simp only [walkCost, ← List.sum_toFinset _ hnodup, hpt]
  rw [Finset.sum_comm (s := arcs.toFinset)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm (s := arcs.toFinset)]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', List.mem_toFinset, ite_smul, one_smul,
    zero_smul]

/-- Canceling `δ` units along a residual cycle `arcs` changes `totalCost` by `δ • M.walkCost arcs`.
-/
theorem Flow.totalCost_cancelCycle [DecidableEq V] [AddCommGroup W] (f : M.Flow)
    {arcs : List (ResArc V)} (hc : f.IsResCycle arcs) {δ : ℕ}
    (hδ : ∀ a ∈ arcs, δ ≤ f.resCap a) :
    (f.cancelCycle arcs hc δ hδ).totalCost - f.totalCost = δ • M.walkCost arcs := by
  have hnodup := Flow.isResCycle_nodup hc
  have hpt : ∀ u v : V,
      (f.cancelCycle arcs hc δ hδ u v) • M.cost u v - f u v • M.cost u v =
        δ • ((if ⟨u, v, true⟩ ∈ arcs then (1 : ℕ) else 0) • M.cost u v -
          (if ⟨v, u, false⟩ ∈ arcs then (1 : ℕ) else 0) • M.cost u v) := by
    intro u v
    simp only [Flow.cancelCycle_apply, ← natCast_zsmul, Flow.cancelCycleFun_coe f hδ]
    split_ifs <;> simp [add_smul, sub_smul]
  unfold Flow.totalCost
  simp only [← Finset.sum_sub_distrib, hpt, ← Finset.smul_sum]
  rw [sum_resCost_ite M arcs hnodup]

theorem Flow.totalCost_cancelCycle_lt [DecidableEq V] [AddCommGroup W] [LinearOrder W]
    [IsOrderedAddMonoid W] (f : M.Flow) {arcs : List (ResArc V)} (hc : f.IsResCycle arcs)
    {δ : ℕ} (hδ_pos : 0 < δ) (hδ : ∀ a ∈ arcs, δ ≤ f.resCap a) (hneg : M.walkCost arcs < 0) :
    (f.cancelCycle arcs hc δ hδ).totalCost < f.totalCost :=
  sub_lt_zero.mp (f.totalCost_cancelCycle hc hδ ▸ Right.nsmul_neg hδ_pos hneg)

end CycleOps

/-! ### Complementary slackness optimality -/

section PotentialSufficiency

variable {V : Type*} {W : Type*} [Fintype V] {M : CostNetwork V W}

private theorem sum_balance_smul_potential [AddCommGroup W] (f : M.Flow) (π : V → W) :
    (∑ u : V, ∑ v : V, f u v • (π u - π v)) = ∑ u : V, M.balance u • π u := by
  simp only [← natCast_zsmul, smul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun u v => (f u v : ℤ) • π v), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_smul, ← Finset.sum_smul, ← sub_smul, f.balance_eq u]

/-- **Complementary slackness implies minimum cost** ([Klein1967], [Schrijver2003], Chapter 12,
locator not re-verified against primary PDF): any feasible flow admitting potentials `π` with
`CompSlackness M f π` minimizes `totalCost` among all feasible flows of `M`. -/
theorem isMinCost_of_compSlackness [AddCommGroup W] [PartialOrder W] [IsOrderedAddMonoid W]
    {f : M.Flow} {π : V → W} (hcs : M.CompSlackness f π) : f.IsMinCost := by
  intro g
  have hpt : ∀ u v : V, f u v • (M.cost u v + π u - π v) ≤ g u v • (M.cost u v + π u - π v) := by
    intro u v
    rcases Nat.lt_trichotomy (f u v) (g u v) with hlt | heq | hgt
    · exact nsmul_le_nsmul_left (hcs.1 u v (lt_of_lt_of_le hlt (g.le_cap u v))) hlt.le
    · rw [heq]
    · rw [← Nat.sub_add_cancel hgt.le, add_nsmul]
      exact add_le_of_nonpos_left (nsmul_nonpos (hcs.2 u v (by omega)) _)
  have hsum : (∑ u : V, ∑ v : V, f u v • (M.cost u v + π u - π v)) ≤
      ∑ u : V, ∑ v : V, g u v • (M.cost u v + π u - π v) :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hpt u v
  have hdecomp (h : M.Flow) :
      (∑ u : V, ∑ v : V, h u v • (M.cost u v + π u - π v)) =
        h.totalCost + ∑ u : V, M.balance u • π u := by
    simp only [add_sub_assoc, nsmul_add, Finset.sum_add_distrib, sum_balance_smul_potential]
    rfl
  rw [hdecomp f, hdecomp g] at hsum
  exact le_of_add_le_add_right hsum

end PotentialSufficiency

/-! ### Simple cycle extraction from walks -/

section CycleExtraction

variable {V : Type*} [DecidableEq V]

/-- A decomposition `pre ++ cyc ++ post` of a residual walk extracting a simple directed cycle
`cyc`. -/
structure CycleSplit (V : Type*) where
  /-- Prefix walk before the extracted cycle. -/
  pre : List (ResArc V)
  /-- Nonempty simple directed cycle. -/
  cyc : List (ResArc V)
  /-- Suffix walk after the extracted cycle. -/
  post : List (ResArc V)

/-- Split `arcs` right after the first arc whose `dst` equals `target`. -/
@[expose] def splitAtDst (target : V) : List (ResArc V) → List (ResArc V) × List (ResArc V)
  | [] => ([], [])
  | b :: rest =>
    if b.dst = target then ([b], rest)
    else
      let p := splitAtDst target rest
      (b :: p.1, p.2)

private theorem splitAtDst_spec {p : ResArc V → Prop} {target u₀ v : V} :
    ∀ {arcs : List (ResArc V)},
      IsArcWalk p u₀ v arcs → u₀ ≠ target → (arcs.map ResArc.src ++ [v]).Nodup →
      target ∈ arcs.map ResArc.src ++ [v] →
        let q := splitAtDst target arcs
        q.1 ≠ [] ∧ q.1 ++ q.2 = arcs ∧ IsArcWalk p u₀ target q.1 ∧
          IsArcWalk p target v q.2 ∧ target ∉ q.1.map ResArc.src
  | [], huv, hne, _, hmem => by
    simp only [IsArcWalk] at huv
    simp only [List.map_nil, List.nil_append, List.mem_singleton] at hmem
    exact absurd (huv.trans hmem.symm) hne
  | b :: rest, ⟨hsrc, hpb, hrest⟩, hne, hnodup, hmem => by
    simp only [splitAtDst]
    by_cases hbd : b.dst = target
    · simp only [hbd, ↓reduceIte]
      refine ⟨List.cons_ne_nil b [], rfl, ⟨hsrc, hpb, hbd⟩, hbd ▸ hrest, ?_⟩
      simp [hsrc, Ne.symm hne]
    · simp only [hbd, ↓reduceIte]
      have hnodup' : (rest.map ResArc.src ++ [v]).Nodup := by
        simp only [List.map_cons, List.cons_append] at hnodup
        exact (List.nodup_cons.mp hnodup).2
      have hmem' : target ∈ rest.map ResArc.src ++ [v] := by
        simp only [List.map_cons, List.cons_append, List.mem_cons, hsrc] at hmem
        exact hmem.resolve_left (Ne.symm hne)
      have ih := splitAtDst_spec (p := p) hrest hbd hnodup' hmem'
      dsimp only at ih ⊢
      refine ⟨List.cons_ne_nil b _, congrArg (b :: ·) ih.2.1, ⟨hsrc, hpb, ih.2.2.1⟩,
        ih.2.2.2.1, ?_⟩
      simp [hsrc, Ne.symm hne, ih.2.2.2.2]

/-- Extract a simple directed cycle `(pre, cyc, post)` from an arc walk ending at `v`, scanning
right-to-left, or `none` when `arcs.map src ++ [v]` has no duplicate vertices. -/
@[expose] def extractSimpleCycleTo (v : V) : List (ResArc V) → Option (CycleSplit V)
  | [] => none
  | a :: rest =>
    match extractSimpleCycleTo v rest with
    | some r => some ⟨a :: r.pre, r.cyc, r.post⟩
    | none =>
      if a.src ∈ rest.map ResArc.src ++ [v] then
        if a.src = a.dst then
          some ⟨[], [a], rest⟩
        else
          let (q1, q2) := splitAtDst a.src rest
          some ⟨[], a :: q1, q2⟩
      else none

private theorem extractSimpleCycleTo_none {p : ResArc V → Prop} {u v : V} :
    ∀ {arcs : List (ResArc V)},
      IsArcWalk p u v arcs → extractSimpleCycleTo v arcs = none →
        (arcs.map ResArc.src ++ [v]).Nodup
  | [], _, _ => by simp
  | a :: rest, ⟨hsrc, _, hrest⟩, hres => by
    simp only [extractSimpleCycleTo] at hres
    cases hex : extractSimpleCycleTo v rest with
    | some r => rw [hex] at hres; cases hres
    | none =>
      rw [hex] at hres
      dsimp only at hres
      split_ifs at hres with hm
      · have ih := extractSimpleCycleTo_none hrest hex
        simpa [List.nodup_cons, hm] using ih

private theorem extractSimpleCycleTo_some {p : ResArc V → Prop} {u v : V} :
    ∀ {arcs : List (ResArc V)} {r : CycleSplit V},
      IsArcWalk p u v arcs → extractSimpleCycleTo v arcs = some r →
        r.cyc ≠ [] ∧ r.pre ++ r.cyc ++ r.post = arcs ∧
          (∃ x, IsArcWalk p x x r.cyc ∧ (r.cyc.map ResArc.src).Nodup) ∧
          IsArcWalk p u v (r.pre ++ r.post) ∧ (r.pre ++ r.post).length < arcs.length
  | [], r, _, hres => by simp [extractSimpleCycleTo] at hres
  | a :: rest, r, ⟨hsrc, hpa, hrest⟩, hres => by
    simp only [extractSimpleCycleTo] at hres
    cases hex : extractSimpleCycleTo v rest with
    | some r' =>
      rw [hex] at hres
      obtain ⟨rfl⟩ := Option.some.inj hres
      obtain ⟨hne', heq', ⟨x, hwx, hnd'⟩, hw', hlt'⟩ := extractSimpleCycleTo_some hrest hex
      refine ⟨hne', by simp [← heq'], ⟨x, hwx, hnd'⟩, ⟨hsrc, hpa, hw'⟩, by simpa using hlt'⟩
    | none =>
      rw [hex] at hres
      dsimp only at hres
      have hnd_rest : (rest.map ResArc.src ++ [v]).Nodup := extractSimpleCycleTo_none hrest hex
      split_ifs at hres with hmem had
      · obtain ⟨rfl⟩ := Option.some.inj hres
        refine ⟨List.cons_ne_nil a [], rfl, ⟨a.src, ⟨rfl, hpa, had.symm⟩, by simp⟩,
          ?_, by simp⟩
        rwa [List.nil_append, ← hsrc, had]
      · obtain ⟨rfl⟩ := Option.some.inj hres
        obtain ⟨hq_ne, hq_eq, hw_q1, hw_q2, hnotin⟩ :=
          splitAtDst_spec hrest (Ne.symm had) hnd_rest hmem
        have hnd_q1 : ((splitAtDst a.src rest).1.map ResArc.src).Nodup := by
          have hnd_src := (List.nodup_append.mp hnd_rest).1
          rw [← hq_eq, List.map_append] at hnd_src
          exact (List.nodup_append.mp hnd_src).1
        refine ⟨List.cons_ne_nil a _, by simp [hq_eq],
          ⟨a.src, ⟨rfl, hpa, hw_q1⟩, List.nodup_cons.mpr ⟨hnotin, hnd_q1⟩⟩,
          hsrc ▸ hw_q2, ?_⟩
        have hlen := congrArg List.length hq_eq
        have hpos := List.length_pos_iff_ne_nil.mpr hq_ne
        simp only [List.nil_append, List.length_cons, List.length_append] at hlen ⊢
        omega

/-- Structural-fuel helper for `peelNegCycle`. -/
@[expose] def peelNegCycleAux {W : Type*} [AddCommGroup W] [LinearOrder W]
    (M : CostNetwork V W) (v : V) : ℕ → List (ResArc V) → List (ResArc V)
  | 0, _ => []
  | fuel + 1, arcs =>
    match extractSimpleCycleTo v arcs with
    | none => []
    | some r =>
      if M.walkCost r.cyc < 0 then r.cyc
      else peelNegCycleAux M v fuel (r.pre ++ r.post)

/-- Peel simple cycles from `arcs` (ending at `v`) until returning the first negative-cost simple
cycle. -/
@[expose] def peelNegCycle {W : Type*} [AddCommGroup W] [LinearOrder W]
    (M : CostNetwork V W) (v : V) (arcs : List (ResArc V)) : List (ResArc V) :=
  peelNegCycleAux M v arcs.length arcs

private theorem peelNegCycleAux_spec {W : Type*} [AddCommGroup W] [LinearOrder W]
    [IsOrderedAddMonoid W] (M : CostNetwork V W) {p : ResArc V → Prop} {u v : V}
    {bound : W} (hbound : ∀ w arcs, IsArcWalk p w v arcs → (arcs.map ResArc.src ++ [v]).Nodup →
      bound ≤ M.walkCost arcs) :
    ∀ (fuel : ℕ) {arcs : List (ResArc V)},
      arcs.length ≤ fuel → IsArcWalk p u v arcs → M.walkCost arcs < bound →
        let cyc := peelNegCycleAux M v fuel arcs
        cyc ≠ [] ∧ (∃ x, IsArcWalk p x x cyc ∧ (cyc.map ResArc.src).Nodup) ∧ M.walkCost cyc < 0
  | 0, arcs, hlen, hw, hlt => by
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    exact absurd hlt (not_lt.mpr (hbound u [] hw (by simp)))
  | fuel + 1, arcs, hlen, hw, hlt => by
    unfold peelNegCycleAux
    cases h : extractSimpleCycleTo v arcs with
    | none =>
      dsimp only
      have hnd := extractSimpleCycleTo_none hw h
      exact absurd hlt (not_lt.mpr (hbound u arcs hw hnd))
    | some r =>
      dsimp only
      obtain ⟨hne, heq, ⟨x, hx, hnd⟩, hw', hlt_len⟩ := extractSimpleCycleTo_some hw h
      split_ifs with hneg
      · exact ⟨hne, ⟨x, hx, hnd⟩, hneg⟩
      · have hsplit_cost : M.walkCost arcs = M.walkCost r.cyc + M.walkCost (r.pre ++ r.post) := by
          rw [← heq, walkCost_append, walkCost_append, walkCost_append]
          abel
        have hge : 0 ≤ M.walkCost r.cyc := not_lt.mp hneg
        have hlt' : M.walkCost (r.pre ++ r.post) < bound := by
          calc M.walkCost (r.pre ++ r.post)
              ≤ M.walkCost r.cyc + M.walkCost (r.pre ++ r.post) := le_add_of_nonneg_left hge
            _ = M.walkCost arcs := hsplit_cost.symm
            _ < bound := hlt
        exact peelNegCycleAux_spec M hbound fuel (by omega) hw' hlt'

private theorem peelNegCycle_spec {W : Type*} [AddCommGroup W] [LinearOrder W]
    [IsOrderedAddMonoid W] (M : CostNetwork V W) {p : ResArc V → Prop} {u v : V}
    {bound : W} (hbound : ∀ w arcs, IsArcWalk p w v arcs → (arcs.map ResArc.src ++ [v]).Nodup →
      bound ≤ M.walkCost arcs)
    {arcs : List (ResArc V)} (hw : IsArcWalk p u v arcs) (hlt : M.walkCost arcs < bound) :
    let cyc := peelNegCycle M v arcs
    cyc ≠ [] ∧ (∃ x, IsArcWalk p x x cyc ∧ (cyc.map ResArc.src).Nodup) ∧ M.walkCost cyc < 0 :=
  peelNegCycleAux_spec M hbound arcs.length le_rfl hw hlt

end CycleExtraction

/-! ### Bellman–Ford relaxation DP for negative cycles and potentials -/

section BellmanFordDP

variable {V : Type*} {W : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- All positive-residual-capacity arcs of `f` whose endpoints lie in `vs`. -/
@[expose] def allResArcs (M : CostNetwork V W) (vs : List V) (f : M.Flow) : List (ResArc V) :=
  vs.flatMap fun u => vs.flatMap fun v =>
    (if f u v < M.cap u v then [⟨u, v, true⟩] else []) ++
      (if 0 < f v u then [⟨u, v, false⟩] else [])

omit [DecidableEq V] in
private theorem mem_allResArcs {M : CostNetwork V W} {vs : List V} {f : M.Flow}
    {a : ResArc V} :
    a ∈ allResArcs M vs f ↔ a.src ∈ vs ∧ a.dst ∈ vs ∧ 0 < f.resCap a := by
  rcases a with ⟨u, v, b⟩
  cases b <;> simp [allResArcs, Flow.resCap, tsub_pos_iff_lt]

private theorem foldl_inv {α β : Type*} {P : β → Prop} {f : β → α → β} :
    ∀ (l : List α) {init : β}, P init → (∀ b, P b → ∀ a ∈ l, P (f b a)) →
      P (l.foldl f init)
  | [], _, hinit, _ => hinit
  | a :: rest, _, hinit, hf =>
    foldl_inv rest (hf _ hinit a List.mem_cons_self)
      fun b hb x hx => hf b hb x (List.mem_cons_of_mem a hx)

/-- Synchronous one-round Bellman–Ford relaxation storing `(bestWeight, arcTrail)` per vertex. -/
@[expose] def dpStep [AddCommGroup W] [LinearOrder W]
    (M : CostNetwork V W) (arcs : List (ResArc V)) (prev : V → W × List (ResArc V))
    (v : V) : W × List (ResArc V) :=
  arcs.foldl
    (fun best a =>
      if a.dst = v ∧ (prev a.src).1 + M.resCost a < best.1 then
        ((prev a.src).1 + M.resCost a, (prev a.src).2 ++ [a])
      else best)
    (prev v)

/-- `k`-round synchronous Bellman–Ford relaxation from `(0, [])` at every vertex. -/
@[expose] def dpRelax [AddCommGroup W] [LinearOrder W]
    (M : CostNetwork V W) (arcs : List (ResArc V)) (k : ℕ) : V → W × List (ResArc V) :=
  (dpStep M arcs)^[k] (fun _ => (0, []))

private def DpInv [AddCommGroup W] (M : CostNetwork V W) (f : M.Flow) (k : ℕ)
    (st : V → W × List (ResArc V)) : Prop :=
  ∀ v, (∃ u, f.IsResWalk u v (st v).2) ∧ M.walkCost (st v).2 = (st v).1 ∧ (st v).2.length ≤ k

private theorem dpStep_preserves [AddCommGroup W] [LinearOrder W]
    {M : CostNetwork V W} {arcs : List (ResArc V)} {f : M.Flow}
    (harcs : ∀ a ∈ arcs, 0 < f.resCap a) {k : ℕ} {st : V → W × List (ResArc V)}
    (hst : DpInv M f k st) : DpInv M f (k + 1) (dpStep M arcs st) := by
  intro v
  unfold dpStep
  refine foldl_inv (P := fun best : W × List (ResArc V) =>
      (∃ u, f.IsResWalk u v best.2) ∧ M.walkCost best.2 = best.1 ∧ best.2.length ≤ k + 1)
    arcs ?_ ?_
  · obtain ⟨⟨u, hw⟩, hc, hl⟩ := hst v
    exact ⟨⟨u, hw⟩, hc, Nat.le_succ_of_le hl⟩
  · intro best ih a ha
    split_ifs with h
    · obtain ⟨hdst, _⟩ := h
      obtain ⟨⟨u, hw⟩, hc, _⟩ := hst a.src
      refine ⟨⟨u, ?_⟩, ?_, ?_⟩
      · exact (isArcWalk_pos_resCap_iff f).mp
          (isArcWalk_split_append.mpr ⟨(isArcWalk_pos_resCap_iff f).mpr hw, harcs a ha, hdst⟩)
      · simp [hc]
      · simp only [List.length_append, List.length_singleton]
        exact Nat.succ_le_succ (hst a.src).2.2
    · exact ih

private theorem dpRelax_inv [AddCommGroup W] [LinearOrder W]
    {M : CostNetwork V W} {arcs : List (ResArc V)} {f : M.Flow}
    (harcs : ∀ a ∈ arcs, 0 < f.resCap a) (k : ℕ) :
    DpInv M f k (dpRelax M arcs k) := by
  induction k with
  | zero => exact fun v => ⟨⟨v, by simp [dpRelax, Flow.IsResWalk]⟩, rfl, le_rfl⟩
  | succ k ih =>
    rw [dpRelax, Function.iterate_succ_apply']
    exact dpStep_preserves harcs ih

omit [Fintype V] in
private theorem dpStep_foldl_le_init [AddCommGroup W] [LinearOrder W]
    (M : CostNetwork V W) (prev : V → W × List (ResArc V)) (v : V)
    (l : List (ResArc V)) (init : W × List (ResArc V)) :
    (l.foldl
      (fun best a =>
        if a.dst = v ∧ (prev a.src).1 + M.resCost a < best.1 then
          ((prev a.src).1 + M.resCost a, (prev a.src).2 ++ [a])
        else best)
      init).1 ≤ init.1 :=
  foldl_inv (P := fun best : W × List (ResArc V) => best.1 ≤ init.1) l le_rfl
    fun _ hb _ _ => by
      split_ifs with h
      · exact h.2.le.trans hb
      · exact hb

omit [Fintype V] in
private theorem dpStep_le_prev [AddCommGroup W] [LinearOrder W]
    (M : CostNetwork V W) (arcs : List (ResArc V)) (prev : V → W × List (ResArc V)) (v : V) :
    (dpStep M arcs prev v).1 ≤ (prev v).1 :=
  dpStep_foldl_le_init M prev v arcs (prev v)

omit [Fintype V] in
private theorem dpStep_foldl_le_of_mem [AddCommGroup W] [LinearOrder W]
    (M : CostNetwork V W) (prev : V → W × List (ResArc V)) {v : V} {a : ResArc V}
    (ha_dst : a.dst = v) :
    ∀ (l : List (ResArc V)) (init : W × List (ResArc V)), a ∈ l →
      (l.foldl
        (fun best b =>
          if b.dst = v ∧ (prev b.src).1 + M.resCost b < best.1 then
            ((prev b.src).1 + M.resCost b, (prev b.src).2 ++ [b])
          else best)
        init).1 ≤ (prev a.src).1 + M.resCost a
  | [], _, ha => by simp at ha
  | b :: bs, init, ha => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · refine (dpStep_foldl_le_init M prev v bs _).trans ?_
      split_ifs with h
      · exact le_rfl
      · exact not_lt.mp fun hc => h ⟨ha_dst, hc⟩
    · exact dpStep_foldl_le_of_mem M prev ha_dst bs _ ha'

private theorem dpRelax_le_walkCost [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
    {M : CostNetwork V W} {arcs : List (ResArc V)} {f : M.Flow}
    (harcs : ∀ a ∈ arcs, 0 < f.resCap a) (hall : ∀ a, 0 < f.resCap a → a ∈ arcs) :
    ∀ (k : ℕ) {u v : V} (l : List (ResArc V)),
      f.IsResWalk u v l → l.length ≤ k → (dpRelax M arcs k v).1 ≤ M.walkCost l
  | 0, u, v, l, hw, hlen => by
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    rfl
  | k + 1, u, v, l, hw, hlen => by
    rcases List.eq_nil_or_concat l with rfl | ⟨l₀, a, rfl⟩
    · have hk : ∀ m, (dpRelax M arcs m v).1 ≤ 0 := fun m => by
        induction m with
        | zero => rfl
        | succ m ihm =>
          rw [dpRelax, Function.iterate_succ_apply']
          exact (dpStep_le_prev M arcs _ v).trans ihm
      exact hk (k + 1)
    · rw [List.concat_eq_append] at hw hlen ⊢
      obtain ⟨hw₀, ha_pos, ha_dst⟩ :=
        isArcWalk_split_append.mp ((isArcWalk_pos_resCap_iff f).mpr hw)
      have hl₀ : l₀.length ≤ k := by
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      have ih := dpRelax_le_walkCost harcs hall k l₀ ((isArcWalk_pos_resCap_iff f).mp hw₀) hl₀
      have hstep : (dpRelax M arcs (k + 1) v).1 ≤ (dpRelax M arcs k a.src).1 + M.resCost a := by
        rw [dpRelax, Function.iterate_succ_apply']
        exact dpStep_foldl_le_of_mem M (dpRelax M arcs k) ha_dst arcs _ (hall a ha_pos)
      rw [walkCost_append, walkCost_cons, walkCost_nil, add_zero]
      exact hstep.trans (add_le_add ih le_rfl)

/-- Run Bellman–Ford relaxation DP for `vs.length - 1` steps from `(0, [])` and return either a
negative simple residual cycle (`Sum.inl cyc`) or complementary-slackness potentials
(`Sum.inr π`). -/
@[expose] def findNegCycleOrPotential [AddCommGroup W] [LinearOrder W]
    (M : CostNetwork V W) (vs : List V) (f : M.Flow) : List (ResArc V) ⊕ (V → W) :=
  let arcs := allResArcs M vs f
  let d := dpRelax M arcs (vs.length - 1)
  match arcs.find? fun a => decide ((d a.src).1 + M.resCost a < (d a.dst).1) with
  | none => Sum.inr fun v => (d v).1
  | some a => Sum.inl (peelNegCycle M a.dst ((d a.src).2 ++ [a]))

theorem findNegCycleOrPotential_spec [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
    {M : CostNetwork V W} {vs : List V} (hvs : ∀ v, v ∈ vs) (f : M.Flow) :
    match findNegCycleOrPotential M vs f with
    | Sum.inl cyc => f.IsResCycle cyc ∧ M.walkCost cyc < 0
    | Sum.inr π => M.CompSlackness f π := by
  classical
  have harcs : ∀ a ∈ allResArcs M vs f, 0 < f.resCap a := fun a ha =>
    (mem_allResArcs.mp ha).2.2
  have hall : ∀ a, 0 < f.resCap a → a ∈ allResArcs M vs f := fun a ha =>
    mem_allResArcs.mpr ⟨hvs a.src, hvs a.dst, ha⟩
  unfold findNegCycleOrPotential
  dsimp only
  set arcs := allResArcs M vs f
  set d := dpRelax M arcs (vs.length - 1)
  cases hfind : arcs.find? (fun a => decide ((d a.src).1 + M.resCost a < (d a.dst).1)) with
  | none =>
    dsimp only
    have hnone : ∀ a ∈ arcs, (d a.dst).1 ≤ (d a.src).1 + M.resCost a := fun a ha =>
      not_lt.mp (by simpa only [decide_eq_true_eq] using List.find?_eq_none.mp hfind a ha)
    refine ⟨fun u v hlt => ?_, fun u v hpos => ?_⟩
    · have hmem : ⟨u, v, true⟩ ∈ arcs := hall ⟨u, v, true⟩ (by simpa [Flow.resCap] using hlt)
      have hle := hnone ⟨u, v, true⟩ hmem
      simp only [resCost, ↓reduceIte] at hle
      exact sub_nonneg.mpr (by simpa only [add_comm] using hle)
    · have hmem : ⟨v, u, false⟩ ∈ arcs := hall ⟨v, u, false⟩ (by simpa [Flow.resCap] using hpos)
      have hle := hnone ⟨v, u, false⟩ hmem
      simp only [resCost, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg] at hle
      exact sub_nonpos.mpr (by rw [add_comm]; exact le_sub_iff_add_le.mp hle)
  | some a =>
    have ha_mem : a ∈ arcs := List.mem_of_find?_eq_some hfind
    have ha_lt : (d a.src).1 + M.resCost a < (d a.dst).1 := by
      simpa only [decide_eq_true_eq] using List.find?_some hfind
    obtain ⟨⟨u, hw_src⟩, hcost_src, _⟩ := dpRelax_inv harcs (vs.length - 1) a.src
    have htrail : IsArcWalk (fun x => 0 < f.resCap x) u a.dst ((d a.src).2 ++ [a]) :=
      isArcWalk_split_append.mpr ⟨(isArcWalk_pos_resCap_iff f).mpr hw_src, harcs a ha_mem, rfl⟩
    have htrail_cost : M.walkCost ((d a.src).2 ++ [a]) < (d a.dst).1 := by
      rwa [walkCost_append, walkCost_cons, walkCost_nil, add_zero, hcost_src]
    have hcard_le : Fintype.card V ≤ vs.length :=
      (Finset.card_le_card fun v _ => List.mem_toFinset.mpr (hvs v)).trans
        (List.toFinset_card_le vs)
    have hbound : ∀ w q, IsArcWalk (fun x => 0 < f.resCap x) w a.dst q →
        (q.map ResArc.src ++ [a.dst]).Nodup → (d a.dst).1 ≤ M.walkCost q := fun w q hwq hnd => by
      have hq_len := hnd.length_le_card
      simp only [List.length_append, List.length_map, List.length_singleton] at hq_len
      exact dpRelax_le_walkCost harcs hall (vs.length - 1) q
        ((isArcWalk_pos_resCap_iff f).mp hwq) (by omega)
    obtain ⟨hne, ⟨x, hx, hnd⟩, hwc⟩ := peelNegCycle_spec M hbound htrail htrail_cost
    dsimp only
    cases hcyc : peelNegCycle M a.dst ((d a.src).2 ++ [a]) with
    | nil => exact absurd hcyc hne
    | cons c cs =>
      rw [hcyc] at hx hnd hwc
      exact ⟨⟨hx.1 ▸ (isArcWalk_pos_resCap_iff f).mp hx, hnd⟩, hwc⟩

end BellmanFordDP

/-! ### Klein's negative-cycle optimality theorem -/

section KleinOptimality

variable {V : Type*} {W : Type*} [Fintype V] {M : CostNetwork V W}

private theorem exists_compSlackness_of_not_exists_negCycle [AddCommGroup W] [LinearOrder W]
    [IsOrderedAddMonoid W] {f : M.Flow}
    (hno : ¬ ∃ arcs : List (ResArc V), f.IsResCycle arcs ∧ M.walkCost arcs < 0) :
    ∃ π : V → W, M.CompSlackness f π := by
  classical
  let vs : List V := (Finset.univ : Finset V).toList
  have hvs : ∀ v, v ∈ vs := fun v => Finset.mem_toList.mpr (Finset.mem_univ v)
  have hspec := findNegCycleOrPotential_spec hvs f
  rcases hfind : findNegCycleOrPotential M vs f with cyc | π <;> rw [hfind] at hspec
  · exact absurd ⟨cyc, hspec⟩ hno
  · exact ⟨π, hspec⟩

/-- **Klein's negative-cycle optimality theorem** ([Klein1967], pp. 205–220, locator not
re-verified against primary PDF; [Schrijver2003], Chapter 12, locator not re-verified against
primary PDF): a feasible flow has minimum cost if and only if its residual network contains no
negative-cost simple cycle. -/
theorem isMinCost_iff_not_exists_negCycle [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
    (f : M.Flow) :
    f.IsMinCost ↔ ¬ ∃ arcs : List (ResArc V), f.IsResCycle arcs ∧ M.walkCost arcs < 0 := by
  constructor
  · intro hmin ⟨arcs, hc, hneg⟩
    classical
    let δ := f.cycleBottleneck arcs
    have hδ_pos : 0 < δ :=
      Flow.cycleBottleneck_pos (Flow.isResCycle_ne_nil hc)
        (fun _ ha => Flow.pos_resCap_of_mem_isResCycle hc ha)
    have hlt : (f.cancelCycle arcs hc δ fun _ ha => Flow.cycleBottleneck_le ha).totalCost <
        f.totalCost :=
      Flow.totalCost_cancelCycle_lt f hc hδ_pos (fun _ ha => Flow.cycleBottleneck_le ha) hneg
    exact absurd (hmin _) (not_le.mpr hlt)
  · intro hno
    obtain ⟨π, hcs⟩ := exists_compSlackness_of_not_exists_negCycle hno
    exact isMinCost_of_compSlackness hcs

/-- **Complementary slackness optimality theorem** ([Schrijver2003], Chapter 12, locator not
re-verified against primary PDF): a feasible flow has minimum cost if and only if it admits
complementary-slackness node potentials. -/
theorem isMinCost_iff_exists_compSlackness [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
    (f : M.Flow) :
    f.IsMinCost ↔ ∃ π : V → W, M.CompSlackness f π :=
  ⟨fun hmin =>
    exists_compSlackness_of_not_exists_negCycle
      ((isMinCost_iff_not_exists_negCycle f).mp hmin),
   fun ⟨_, hcs⟩ => isMinCost_of_compSlackness hcs⟩

end KleinOptimality

/-! ### Cycle canceling algorithm and existence of minimum-cost flows -/

section CycleCanceling

variable {V : Type*} {W : Type*} [Fintype V]

/-- Result of executable negative-cycle canceling on `M : CostNetwork V W`. -/
structure CycleCancelOutput (M : CostNetwork V W) where
  /-- Optimal feasible flow returned upon termination. -/
  flow : M.Flow
  /-- Complementary-slackness node potentials certifying optimality of `flow`. -/
  potential : V → W
  /-- Number of negative-cycle cancellations performed. -/
  cancellations : ℕ

/-- Iteratively find and cancel negative residual cycles up to `fuel` steps, returning an
optimal flow and complementary-slackness potentials once none remain. -/
@[expose] def cycleCancelLoop [DecidableEq V] [AddCommGroup W] [LinearOrder W]
    (M : CostNetwork V W) (vs : List V) : ℕ → M.Flow → ℕ → CycleCancelOutput M
  | 0, f, count =>
    match findNegCycleOrPotential M vs f with
    | Sum.inl _ => ⟨f, fun _ => 0, count⟩
    | Sum.inr π => ⟨f, π, count⟩
  | fuel + 1, f, count =>
    match findNegCycleOrPotential M vs f with
    | Sum.inr π => ⟨f, π, count⟩
    | Sum.inl cyc =>
      if hc : f.IsResCycle cyc then
        let δ := f.cycleBottleneck cyc
        cycleCancelLoop M vs fuel (f.cancelCycle cyc hc δ fun _ ha => Flow.cycleBottleneck_le ha)
          (count + 1)
      else ⟨f, fun _ => 0, count⟩

private def flowToCapMap {M : CostNetwork V W} (f : M.Flow) :
    ∀ p : V × V, Fin (M.cap p.1 p.2 + 1) :=
  fun p => ⟨f p.1 p.2, Nat.lt_succ_of_le (f.le_cap p.1 p.2)⟩

private theorem flowToCapMap_injective {M : CostNetwork V W} :
    Function.Injective (flowToCapMap : M.Flow → ∀ p : V × V, Fin (M.cap p.1 p.2 + 1)) := by
  intro f g h
  ext u v
  exact congr_arg Fin.val (congr_fun h (u, v))

private noncomputable def cheaperCapMaps [DecidableEq V] [AddCommMonoid W] [LT W]
    (M : CostNetwork V W) (bound : W) : Finset (∀ p : V × V, Fin (M.cap p.1 p.2 + 1)) :=
  open scoped Classical in
  Finset.univ.filter fun m => ∃ g : M.Flow, flowToCapMap g = m ∧ g.totalCost < bound

private theorem mem_cheaperCapMaps [DecidableEq V] [AddCommMonoid W] [LT W]
    {M : CostNetwork V W} {bound : W} {m : ∀ p : V × V, Fin (M.cap p.1 p.2 + 1)} :
    m ∈ cheaperCapMaps M bound ↔ ∃ g : M.Flow, flowToCapMap g = m ∧ g.totalCost < bound := by
  classical
  simp [cheaperCapMaps]

private theorem cycleCancelLoop_spec [DecidableEq V] [AddCommGroup W] [LinearOrder W]
    [IsOrderedAddMonoid W] {M : CostNetwork V W} {vs : List V} (hvs : ∀ v, v ∈ vs)
    (rank : M.Flow → ℕ) (h0 : ∀ f, rank f = 0 → f.IsMinCost)
    (hdrop : ∀ f f' : M.Flow, f'.totalCost < f.totalCost → rank f' < rank f)
    (P : M.Flow → ℕ → M.Flow → ℕ → Prop) (hP_refl : ∀ f c, P f c f c)
    (hP_step : ∀ {f₁ c₁ f₂ c₂ f₃ c₃}, f₂.totalCost < f₁.totalCost → c₂ = c₁ + 1 →
      P f₂ c₂ f₃ c₃ → P f₁ c₁ f₃ c₃) :
    ∀ (fuel : ℕ) (f : M.Flow) (count : ℕ), rank f ≤ fuel →
      let out := cycleCancelLoop M vs fuel f count
      out.flow.IsMinCost ∧ M.CompSlackness out.flow out.potential ∧
        P f count out.flow out.cancellations
  | 0, f, count, hfuel => by
    have hmin : f.IsMinCost := h0 f (Nat.eq_zero_of_le_zero hfuel)
    have hspec := findNegCycleOrPotential_spec hvs f
    dsimp only [cycleCancelLoop]
    rcases hfind : findNegCycleOrPotential M vs f with cyc | π <;> rw [hfind] at hspec
    · exact absurd ⟨cyc, hspec⟩ ((isMinCost_iff_not_exists_negCycle f).mp hmin)
    · exact ⟨hmin, hspec, hP_refl f count⟩
  | fuel + 1, f, count, hfuel => by
    have hspec := findNegCycleOrPotential_spec hvs f
    dsimp only [cycleCancelLoop]
    cases hfind : findNegCycleOrPotential M vs f with
    | inr π =>
      rw [hfind] at hspec
      exact ⟨isMinCost_of_compSlackness hspec, hspec, hP_refl f count⟩
    | inl cyc =>
      rw [hfind] at hspec
      obtain ⟨hc, hneg⟩ := hspec
      dsimp only
      split_ifs
      set δ := f.cycleBottleneck cyc
      set f' := f.cancelCycle cyc hc δ fun _ ha => Flow.cycleBottleneck_le ha
      have hδ_pos : 0 < δ :=
        Flow.cycleBottleneck_pos (Flow.isResCycle_ne_nil hc)
          (fun _ ha => Flow.pos_resCap_of_mem_isResCycle hc ha)
      have hlt_cost : f'.totalCost < f.totalCost :=
        Flow.totalCost_cancelCycle_lt f hc hδ_pos (fun _ ha => Flow.cycleBottleneck_le ha) hneg
      have hrank_lt := hdrop f f' hlt_cost
      obtain ⟨hmin, hcs, hP⟩ :=
        cycleCancelLoop_spec hvs rank h0 hdrop P hP_refl hP_step fuel f' (count + 1) (by omega)
      exact ⟨hmin, hcs, hP_step hlt_cost rfl hP⟩

/-- Any feasible flow network with linearly ordered additive group costs admits a minimum-cost
feasible flow and complementary-slackness potentials. -/
theorem exists_isMinCost_of_feasible [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
    {M : CostNetwork V W} (hfeas : Nonempty M.Flow) :
    ∃ (f : M.Flow) (π : V → W), f.IsMinCost ∧ M.CompSlackness f π := by
  classical
  obtain ⟨f₀⟩ := hfeas
  let vs : List V := (Finset.univ : Finset V).toList
  have hvs : ∀ v, v ∈ vs := fun v => Finset.mem_toList.mpr (Finset.mem_univ v)
  let fuel := Fintype.card (∀ p : V × V, Fin (M.cap p.1 p.2 + 1))
  have h0 : ∀ f : M.Flow, (cheaperCapMaps M f.totalCost).card = 0 → f.IsMinCost := by
    intro f hcard0 g
    by_contra hlt
    rw [Finset.card_eq_zero] at hcard0
    have hmem : flowToCapMap g ∈ cheaperCapMaps M f.totalCost :=
      mem_cheaperCapMaps.mpr ⟨g, rfl, not_le.mp hlt⟩
    rw [hcard0] at hmem
    simp at hmem
  have hdrop : ∀ f f' : M.Flow, f'.totalCost < f.totalCost →
      (cheaperCapMaps M f'.totalCost).card < (cheaperCapMaps M f.totalCost).card := by
    intro f f' hlt
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨flowToCapMap f', mem_cheaperCapMaps.mpr ⟨f', rfl, hlt⟩, ?_⟩
      intro hmem
      obtain ⟨g, hmap, hg⟩ := mem_cheaperCapMaps.mp hmem
      rw [flowToCapMap_injective hmap] at hg
      exact (lt_irrefl _ hg).elim
    · intro m hm
      obtain ⟨g, hmap, hg⟩ := mem_cheaperCapMaps.mp hm
      exact mem_cheaperCapMaps.mpr ⟨g, hmap, lt_trans hg hlt⟩
  have hcard : (cheaperCapMaps M f₀.totalCost).card ≤ fuel :=
    (Finset.card_le_univ _).trans_eq Finset.card_univ
  obtain ⟨hmin, hcs, _⟩ := cycleCancelLoop_spec hvs (fun f => (cheaperCapMaps M f.totalCost).card)
    h0 hdrop (fun _ _ _ _ => True) (fun _ _ => trivial) (fun _ _ h => h) fuel f₀ 0 hcard
  exact ⟨(cycleCancelLoop M vs fuel f₀ 0).flow, (cycleCancelLoop M vs fuel f₀ 0).potential,
    hmin, hcs⟩

private theorem sum_toFinset_le_list_sum {α : Type*} [DecidableEq α] (L : List α)
    (fn : α → ℕ) :
    (∑ x ∈ L.toFinset, fn x) ≤ (L.map fn).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases ha : a ∈ t.toFinset
    · rw [Finset.insert_eq_of_mem ha]
      exact le_add_of_nonneg_of_le (Nat.zero_le _) ih
    · rw [Finset.sum_insert ha]
      exact Nat.add_le_add_left ih _

private theorem sum_le_list_map_sum {α : Type*} [Fintype α] {L : List α} (hL : ∀ x, x ∈ L)
    (fn : α → ℕ) : (∑ x : α, fn x) ≤ (L.map fn).sum := by
  classical
  have huniv : L.toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun x => List.mem_toFinset.mpr (hL x)
  rw [← huniv]
  exact sum_toFinset_le_list_sum L fn

/-- Explicit upper bound on `|f.totalCost|` over a vertex enumeration `vs` for integer-cost
networks. -/
@[expose] def absCostBound (M : CostNetwork V ℤ) (vs : List V) : ℕ :=
  (vs.map fun u => (vs.map fun v => M.cap u v * (M.cost u v).natAbs).sum).sum

private theorem totalCost_bound_aux {M : CostNetwork V ℤ} {vs : List V} (hvs : ∀ v, v ∈ vs)
    (f : M.Flow) :
    -(absCostBound M vs : ℤ) ≤ f.totalCost ∧ f.totalCost ≤ (absCostBound M vs : ℤ) := by
  have hsum_le :
      (∑ u : V, ∑ v : V, M.cap u v * (M.cost u v).natAbs) ≤ absCostBound M vs := by
    calc (∑ u : V, ∑ v : V, M.cap u v * (M.cost u v).natAbs)
        ≤ ∑ u : V, (vs.map fun v => M.cap u v * (M.cost u v).natAbs).sum :=
          Finset.sum_le_sum fun u _ => sum_le_list_map_sum hvs _
      _ ≤ absCostBound M vs := sum_le_list_map_sum hvs _
  have hpt : ∀ u v : V,
      -((M.cap u v * (M.cost u v).natAbs : ℕ) : ℤ) ≤ f u v • M.cost u v ∧
        f u v • M.cost u v ≤ ((M.cap u v * (M.cost u v).natAbs : ℕ) : ℤ) := by
    intro u v
    set k := (M.cost u v).natAbs
    have hmul : (f u v : ℤ) * k ≤ (M.cap u v : ℤ) * k := by
      exact_mod_cast Nat.mul_le_mul_right k (f.le_cap u v)
    have h0 : (0 : ℤ) ≤ (f u v : ℤ) * k :=
      Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    change -((M.cap u v : ℤ) * k) ≤ (f u v : ℤ) * M.cost u v ∧
      (f u v : ℤ) * M.cost u v ≤ (M.cap u v : ℤ) * k
    rcases Int.natAbs_eq (M.cost u v) with hc | hc
    · change M.cost u v = k at hc
      rw [hc]
      exact ⟨by omega, hmul⟩
    · change M.cost u v = -k at hc
      rw [hc, mul_neg]
      exact ⟨by omega, by omega⟩
  have hL :
      -(∑ u : V, ∑ v : V, ((M.cap u v * (M.cost u v).natAbs : ℕ) : ℤ)) ≤ f.totalCost := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun u _ => by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun v _ => (hpt u v).1
  have hU :
      f.totalCost ≤ ∑ u : V, ∑ v : V, ((M.cap u v * (M.cost u v).natAbs : ℕ) : ℤ) :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => (hpt u v).2
  have hcast :
      (∑ u : V, ∑ v : V, ((M.cap u v * (M.cost u v).natAbs : ℕ) : ℤ)) ≤
        (absCostBound M vs : ℤ) := by
    simp only [← Nat.cast_sum]
    exact_mod_cast hsum_le
  exact ⟨le_trans (neg_le_neg hcast) hL, le_trans hU hcast⟩

/-- Executable integral negative-cycle canceling ([Klein1967], pp. 205–220, locator not
re-verified against primary PDF): repeatedly extracts and cancels a negative simple residual cycle
starting from `f₀`. Terminates in at most `2 * absCostBound M vs` cancellations. -/
@[expose] def cycleCancelInt [DecidableEq V] (M : CostNetwork V ℤ) (vs : List V) (f₀ : M.Flow) :
    CycleCancelOutput M :=
  cycleCancelLoop M vs (f₀.totalCost + (absCostBound M vs : ℤ)).toNat f₀ 0

/-- **Correctness of executable cycle canceling** ([Klein1967], pp. 205–220, locator not
re-verified against primary PDF): on any finite vertex list `vs` covering `V`, `cycleCancelInt`
returns a minimum-cost feasible flow certified by complementary-slackness potentials after at most
`2 * absCostBound M vs` cancellations. -/
theorem cycleCancelInt_correct [DecidableEq V] {M : CostNetwork V ℤ} {vs : List V}
    (hvs : ∀ v, v ∈ vs) (f₀ : M.Flow) :
    let out := cycleCancelInt M vs f₀
    out.flow.IsMinCost ∧ M.CompSlackness out.flow out.potential ∧
      out.flow.totalCost + (out.cancellations : ℤ) ≤ f₀.totalCost ∧
      out.cancellations ≤ 2 * absCostBound M vs := by
  have hbound : ∀ g : M.Flow, -(absCostBound M vs : ℤ) ≤ g.totalCost := fun g =>
    (totalCost_bound_aux hvs g).1
  have hrank : ∀ f : M.Flow, (f.totalCost + (absCostBound M vs : ℤ)).toNat = 0 → f.IsMinCost :=
    fun f _ g => by have := hbound g; omega
  have hdrop : ∀ f f' : M.Flow, f'.totalCost < f.totalCost →
      (f'.totalCost + (absCostBound M vs : ℤ)).toNat <
        (f.totalCost + (absCostBound M vs : ℤ)).toNat :=
    fun f f' _ => by have := hbound f'; omega
  have hf₀_lo := (totalCost_bound_aux hvs f₀).1
  have hf₀_hi := (totalCost_bound_aux hvs f₀).2
  obtain ⟨hmin, hcs, hdec⟩ := cycleCancelLoop_spec hvs
    (fun f => (f.totalCost + (absCostBound M vs : ℤ)).toNat) hrank hdrop
    (fun f₁ c₁ f₂ c₂ => f₂.totalCost + (c₂ : ℤ) ≤ f₁.totalCost + (c₁ : ℤ))
    (fun _ _ => le_rfl)
    (fun {_ c₁ f₂ c₂ _ _} hlt hc₂ hle => by subst hc₂; push_cast at hle ⊢; omega)
    (f₀.totalCost + (absCostBound M vs : ℤ)).toNat f₀ 0 le_rfl
  have hout_lo := (totalCost_bound_aux hvs (cycleCancelInt M vs f₀).flow).1
  dsimp only [cycleCancelInt] at hout_lo hmin hcs hdec ⊢
  simp only [Nat.cast_zero, add_zero] at hdec
  exact ⟨hmin, hcs, hdec, by omega⟩

end CycleCanceling

end CostNetwork

/-! ### Fixed-value `s`-`t` flows and minimum-cost maximum flow -/

section STFlowBridge

variable {V : Type*} {W : Type*}

/-- Embed an `s`-`t` `Network V` with fixed net flow value `val` into a `CostNetwork V W`
with arc costs `cost`. -/
@[expose] def CostNetwork.ofNetwork [DecidableEq V] (N : Network V) (cost : V → V → W)
    (val : ℤ) : CostNetwork V W where
  cap := N.cap
  cost := cost
  balance v := (if v = N.s then val else 0) - (if v = N.t then val else 0)

/-- Total cost `∑ u, ∑ v, f u v • cost u v` of an `s`-`t` flow `f : N.Flow`. -/
@[expose] def Network.Flow.flowCost [Fintype V] {N : Network V} [AddCommMonoid W]
    (cost : V → V → W) (f : N.Flow) : W :=
  ∑ u, ∑ v, f u v • cost u v

/-- Fixed-value minimum-cost `s`-`t` flow optimality: `f` minimizes `flowCost cost` among all
feasible flows on `N` with the same `value` as `f`. -/
@[expose] def Network.Flow.IsMinCostOfValue [Fintype V] {N : Network V} [AddCommMonoid W] [LE W]
    (cost : V → V → W) (f : N.Flow) : Prop :=
  ∀ g : N.Flow, g.value = f.value → f.flowCost cost ≤ g.flowCost cost

/-- View an `s`-`t` flow `g : N.Flow` with `g.value = val` as a feasible flow in
`CostNetwork.ofNetwork N cost val`. -/
@[expose] def Network.Flow.toCostFlowOfVal [Fintype V] [DecidableEq V] {N : Network V}
    (cost : V → V → W) {val : ℤ} (g : N.Flow) (hg : g.value = val) :
    (CostNetwork.ofNetwork N cost val).Flow where
  toFun := g.toFun
  le_cap := g.le_cap
  balance_eq v := by
    have hnet_eq : (∑ w : V, (g v w : ℤ)) - (∑ u : V, (g u v : ℤ)) = g.netOut v := rfl
    rw [hnet_eq]
    dsimp only [CostNetwork.ofNetwork]
    by_cases hst : N.s = N.t
    · have hg0 : val = 0 := hg.symm.trans (g.value_eq_zero_of_s_eq_t hst)
      subst hg0
      obtain rfl | hvs := eq_or_ne v N.s
      · simpa [Network.Flow.value] using hg
      · simp [hst, g.netOut_eq_zero hvs (hst ▸ hvs)]
    · obtain rfl | hvs := eq_or_ne v N.s
      · simp only [hst, ↓reduceIte, sub_zero]
        exact hg
      · obtain rfl | hvt := eq_or_ne v N.t
        · have htot : ∑ x : V, g.netOut x = 0 := by
            simp only [Network.Flow.netOut, Finset.sum_sub_distrib]
            exact sub_eq_zero.mpr Finset.sum_comm
          have hrest := Fintype.sum_eq_add N.s N.t hst fun x hx => g.netOut_eq_zero hx.1 hx.2
          have hs_val : g.netOut N.s = val := hg
          simp [Ne.symm hst]
          omega
        · simp [hvs, hvt, g.netOut_eq_zero hvs hvt]

/-- View an `s`-`t` flow `f : N.Flow` as a feasible flow of value `f.value` in
`CostNetwork.ofNetwork N cost f.value`. -/
@[expose] def Network.Flow.toCostFlow [Fintype V] [DecidableEq V] {N : Network V}
    (cost : V → V → W) (f : N.Flow) : (CostNetwork.ofNetwork N cost f.value).Flow :=
  f.toCostFlowOfVal cost rfl

/-- View a feasible flow `f` in `CostNetwork.ofNetwork N cost val` back as an `s`-`t` flow on `N`.
-/
@[expose] def CostNetwork.Flow.toNetworkFlow [Fintype V] [DecidableEq V] {N : Network V}
    {cost : V → V → W} {val : ℤ} (f : (CostNetwork.ofNetwork N cost val).Flow) : N.Flow where
  toFun := f.toFun
  le_cap := f.le_cap
  conserve v hvs hvt := by
    have hbal := f.balance_eq v
    simp only [CostNetwork.ofNetwork, hvs, hvt, ↓reduceIte, sub_zero] at hbal
    have hcast : (∑ u : V, (f u v : ℤ)) = ∑ w : V, (f v w : ℤ) := by omega
    rw [← Nat.cast_sum, ← Nat.cast_sum] at hcast
    exact Int.ofNat.inj hcast

@[simp]
theorem CostNetwork.Flow.toNetworkFlow_apply [Fintype V] [DecidableEq V] {N : Network V}
    {cost : V → V → W} {val : ℤ} (f : (CostNetwork.ofNetwork N cost val).Flow) (u v : V) :
    f.toNetworkFlow u v = f u v := rfl

@[simp]
theorem Network.Flow.toCostFlowOfVal_apply [Fintype V] [DecidableEq V] {N : Network V}
    (cost : V → V → W) {val : ℤ} (g : N.Flow) (hg : g.value = val) (u v : V) :
    g.toCostFlowOfVal cost hg u v = g u v := rfl

@[simp]
theorem CostNetwork.Flow.value_toNetworkFlow [Fintype V] [DecidableEq V] {N : Network V}
    {cost : V → V → W} {val : ℤ} (f : (CostNetwork.ofNetwork N cost val).Flow) :
    f.toNetworkFlow.value = if N.s = N.t then 0 else val := by
  by_cases hst : N.s = N.t
  · simp [hst, f.toNetworkFlow.value_eq_zero_of_s_eq_t hst]
  · simp only [Network.Flow.value, Network.Flow.netOut, toNetworkFlow_apply, hst, ↓reduceIte]
    simpa [CostNetwork.ofNetwork, hst] using f.balance_eq N.s

theorem Network.Flow.isMinCostOfValue_iff_isMinCost [Fintype V] [DecidableEq V]
    {N : Network V} [AddCommMonoid W] [LE W] (cost : V → V → W) (f : N.Flow) :
    f.IsMinCostOfValue cost ↔ (f.toCostFlow cost).IsMinCost := by
  constructor
  · intro hmin g
    have hgval : g.toNetworkFlow.value = f.value := by
      rw [g.value_toNetworkFlow]
      split_ifs with hst
      · exact (f.value_eq_zero_of_s_eq_t hst).symm
      · rfl
    exact hmin g.toNetworkFlow hgval
  · exact fun hmin g hg => hmin (g.toCostFlowOfVal cost hg)

/-- **Klein's negative-cycle optimality theorem for `s`-`t` flows** ([Klein1967], pp. 205–220,
locator not re-verified against primary PDF): an `s`-`t` flow `f` has minimum cost among all flows
of value `f.value` if and only if its residual network contains no negative-cost simple cycle. -/
theorem Network.Flow.isMinCostOfValue_iff_not_exists_negCycle [Fintype V] [DecidableEq V]
    [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] {N : Network V}
    (cost : V → V → W) (f : N.Flow) :
    f.IsMinCostOfValue cost ↔
      ¬ ∃ arcs : List (ResArc V),
        (f.toCostFlow cost).IsResCycle arcs ∧
          (CostNetwork.ofNetwork N cost f.value).walkCost arcs < 0 := by
  rw [f.isMinCostOfValue_iff_isMinCost cost, CostNetwork.isMinCost_iff_not_exists_negCycle]

/-- **Complementary slackness optimality theorem for `s`-`t` flows** ([Schrijver2003],
Chapter 12, locator not re-verified against primary PDF): an `s`-`t` flow `f` has minimum cost
among all flows of value `f.value` if and only if it admits complementary-slackness potentials. -/
theorem Network.Flow.isMinCostOfValue_iff_exists_compSlackness [Fintype V] [DecidableEq V]
    [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] {N : Network V}
    (cost : V → V → W) (f : N.Flow) :
    f.IsMinCostOfValue cost ↔
      ∃ π : V → W, (CostNetwork.ofNetwork N cost f.value).CompSlackness (f.toCostFlow cost) π := by
  rw [f.isMinCostOfValue_iff_isMinCost cost, CostNetwork.isMinCost_iff_exists_compSlackness]

/-- Output of `minCostMaxFlow`: an integral maximum `s`-`t` flow of minimum cost, node
potentials certifying fixed-value minimum cost, and the number of negative-cycle cancellations. -/
structure MinCostMaxFlowOutput {n : ℕ} (N : Network (Fin n)) where
  /-- Maximum `s`-`t` flow of minimum cost. -/
  flow : N.Flow
  /-- Complementary-slackness node potentials certifying optimality for `flow.value`. -/
  potential : Fin n → ℤ
  /-- Number of negative-cycle cancellations performed in phase 2. -/
  cancellations : ℕ

/-- Compute a minimum-cost maximum `s`-`t` flow on `N : Network (Fin n)` by finding an initial
maximum flow via `dinitzDense` (or `Network.Flow.zero N` when `N.s = N.t`) and canceling negative
residual cycles via `CostNetwork.cycleCancelInt`. -/
@[expose] def minCostMaxFlow {n : ℕ} (N : Network (Fin n)) (cost : Fin n → Fin n → ℤ) :
    MinCostMaxFlowOutput N :=
  let f₀ : N.Flow := if N.s = N.t then Network.Flow.zero N else (dinitzDense N).flow
  let M := CostNetwork.ofNetwork N cost f₀.value
  let out := CostNetwork.cycleCancelInt M (List.finRange n) (f₀.toCostFlow cost)
  ⟨out.flow.toNetworkFlow, out.potential, out.cancellations⟩

/-- **Correctness of `minCostMaxFlow`** ([Klein1967], pp. 205–220; [Schrijver2003], Chapter 12,
locators not re-verified against primary PDF): returns a maximum `s`-`t` flow that minimizes
`flowCost cost` among all flows of its value (hence among all maximum flows), together with
complementary-slackness potentials certifying optimality. -/
theorem minCostMaxFlow_correct {n : ℕ} (N : Network (Fin n)) (cost : Fin n → Fin n → ℤ) :
    let out := minCostMaxFlow N cost
    out.flow.IsMaxFlow ∧ out.flow.IsMinCostOfValue cost ∧
      (∀ g : N.Flow, g.IsMaxFlow → out.flow.flowCost cost ≤ g.flowCost cost) ∧
      (CostNetwork.ofNetwork N cost out.flow.value).CompSlackness
        (out.flow.toCostFlow cost) out.potential := by
  let f₀ : N.Flow := if N.s = N.t then Network.Flow.zero N else (dinitzDense N).flow
  have hf₀_max : f₀.IsMaxFlow := by
    by_cases hst : N.s = N.t
    · intro g
      simp only [f₀, hst, ↓reduceIte, Network.Flow.value_zero]
      rw [g.value_eq_zero_of_s_eq_t hst]
    · simp only [f₀, hst, ↓reduceIte]
      exact (dinitzDense_correct hst).1
  let M := CostNetwork.ofNetwork N cost f₀.value
  have hvs : ∀ v : Fin n, v ∈ List.finRange n := fun v => List.mem_finRange v
  obtain ⟨_, hcs, _, _⟩ := CostNetwork.cycleCancelInt_correct (M := M) hvs (f₀.toCostFlow cost)
  set outC := CostNetwork.cycleCancelInt M (List.finRange n) (f₀.toCostFlow cost)
  have hval : outC.flow.toNetworkFlow.value = f₀.value := by
    rw [outC.flow.value_toNetworkFlow]
    split_ifs with hst
    · exact (f₀.value_eq_zero_of_s_eq_t hst).symm
    · rfl
  have hmax : outC.flow.toNetworkFlow.IsMaxFlow := fun g => by
    rw [hval]
    exact hf₀_max g
  have hcs' : (CostNetwork.ofNetwork N cost outC.flow.toNetworkFlow.value).CompSlackness
      (outC.flow.toNetworkFlow.toCostFlow cost) outC.potential :=
    ⟨fun u v hlt => hcs.1 u v hlt, fun u v hpos => hcs.2 u v hpos⟩
  have hmin_val : outC.flow.toNetworkFlow.IsMinCostOfValue cost :=
    (outC.flow.toNetworkFlow.isMinCostOfValue_iff_exists_compSlackness cost).mpr
      ⟨outC.potential, hcs'⟩
  have hmin_max :
      ∀ g : N.Flow, g.IsMaxFlow → outC.flow.toNetworkFlow.flowCost cost ≤ g.flowCost cost :=
    fun g hg => hmin_val g (le_antisymm (hmax g) (hg outC.flow.toNetworkFlow))
  exact ⟨hmax, hmin_val, hmin_max, hcs'⟩

end STFlowBridge

end Cslib.Algorithms.Lean.MaxFlow
