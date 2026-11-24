/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.MinCostFlow
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Minimum-Cost Flow and Klein's Negative-Cycle Optimality Tests

Kernel-checked witnesses (`decide` / proof terms, without `native_decide`) exercising:

1. **Diamond `s`–`t` min-cost max flow (`diamondNet`, `minCostMaxFlow`):**
   a short expensive 2-hop prefix `0 → 1 → 4` (`cap 3, cost 7`) and a longer cheap 3-hop prefix
   `0 → 2 → 3 → 4` (`cap 2, cost 2`) converge at bottleneck arc `(4, 5)` (`cap 3, cost 0`), so
   `dinitzDense` saturates `0 → 1 → 4 → 5` in Phase 1 and Phase 2 cancels the negative residual
   cycle `[0 → 2 → 3 → 4 → 1 → 0]` (`value = 3`, `flowCost = 11`, `cancellations = 1`), with
   holding `CompSlackness` potentials and a failing suboptimal flow witness (`flowCost = 21`).
2. **Asymmetric antiparallel arcs (`antiNet`, `antiNegNet`):**
   `cost 0 1 ≠ -cost 1 0`; tests both backward 2-cycle cancellation (`[1 → 0 (rev), 0 → 1 (rev)]`)
   from nonzero initial antiparallel flow (`14 → 0`) and forward 2-cycle saturation (`0 → -9`).
3. **Self-loop boundaries (`loopNet`):**
   saturates a negative self-loop `(0, 0)` up to capacity and cancels a positive self-loop `(1, 1)`
   back to `0` (`4 → -8`, `cancellations = 2`).
4. **Negative-cost 3-cycle circulation & `N.s = N.t` (`circ3Net`, `sameTerminalNet`):**
   cancels a negative 3-cycle (`0 → -6`) both as a zero-balance circulation and inside
   `minCostMaxFlow` with degenerate terminals `s = t = 0`.
5. **Rational costs (`ℚ` instantiation, `ratNet`):**
   non-integer cost type `[AddCommGroup ℚ] [LinearOrder ℚ] [IsOrderedAddMonoid ℚ]`, checking
   `isMinCost_iff_not_exists_negCycle`, `isMinCost_iff_exists_compSlackness`,
   `exists_isMinCost_of_feasible`, an explicit holding potential `π`, and a failing flow witness.
-/

public section

namespace CslibFrontierTests.MinCostFlow

open Cslib.Algorithms.Lean.MaxFlow

/-! ### 1. Diamond `s`-`t` network (`minCostMaxFlow`) -/

/-- A 6-vertex `s`-`t` network where path `0 → 1 → 4 → 5` is shorter in hops (so chosen first by
`dinitzDense`) yet expensive (`cost 7`), whereas path `0 → 2 → 3 → 4 → 5` is longer yet cheap
(`cost 2`), joined before bottleneck arc `(4, 5)` of capacity `3`. -/
def diamondNet : Network (Fin 6) where
  cap u v :=
    match u.val, v.val with
    | 0, 1 => 3
    | 1, 4 => 3
    | 0, 2 => 2
    | 2, 3 => 2
    | 3, 4 => 2
    | 4, 5 => 3
    | _, _ => 0
  s := 0
  t := 5

/-- Per-unit arc costs on `diamondNet`. -/
def diamondCost (u v : Fin 6) : ℤ :=
  match u.val, v.val with
  | 0, 1 => 3
  | 1, 4 => 4
  | 0, 2 => 1
  | 2, 3 => 1
  | _, _ => 0

example : (minCostMaxFlow diamondNet diamondCost).flow.value = 3 := by decide

example : (minCostMaxFlow diamondNet diamondCost).flow.flowCost diamondCost = 11 := by decide

example : (minCostMaxFlow diamondNet diamondCost).cancellations = 1 := by decide

example : (minCostMaxFlow diamondNet diamondCost).flow 0 2 = 2 := by decide

example : (minCostMaxFlow diamondNet diamondCost).flow 0 1 = 1 := by decide

theorem diamond_correct :
    let out := minCostMaxFlow diamondNet diamondCost
    out.flow.IsMaxFlow ∧ out.flow.IsMinCostOfValue diamondCost ∧
      (∀ g : diamondNet.Flow, g.IsMaxFlow →
        out.flow.flowCost diamondCost ≤ g.flowCost diamondCost) ∧
      (CostNetwork.ofNetwork diamondNet diamondCost out.flow.value).CompSlackness
        (out.flow.toCostFlow diamondCost) out.potential :=
  minCostMaxFlow_correct diamondNet diamondCost

/-- Suboptimal max flow routing all `3` units along the expensive upper path `0 → 1 → 4 → 5`. -/
def diamondSubFlow : diamondNet.Flow where
  toFun u v :=
    match u.val, v.val with
    | 0, 1 => 3
    | 1, 4 => 3
    | 4, 5 => 3
    | _, _ => 0
  le_cap := by decide
  conserve := by decide

/-- Negative-cost residual 5-cycle for `diamondSubFlow`: forward `(0,2), (2,3), (3,4)` minus
`(1,4), (0,1)`. -/
def diamondNegCycle : List (ResArc (Fin 6)) :=
  [⟨0, 2, true⟩, ⟨2, 3, true⟩, ⟨3, 4, true⟩, ⟨4, 1, false⟩, ⟨1, 0, false⟩]

example : diamondSubFlow.value = 3 := by decide

example : diamondSubFlow.flowCost diamondCost = 21 := by decide

example : (diamondSubFlow.toCostFlow diamondCost).IsResCycle diamondNegCycle := by decide

example :
    (CostNetwork.ofNetwork diamondNet diamondCost diamondSubFlow.value).walkCost
      diamondNegCycle = -5 := by
  decide

theorem diamondSubFlow_not_minCost : ¬ diamondSubFlow.IsMinCostOfValue diamondCost := by
  rw [Network.Flow.isMinCostOfValue_iff_not_exists_negCycle]
  push Not
  exact ⟨diamondNegCycle, by decide, by decide⟩

theorem diamondSubFlow_no_potential :
    ¬ ∃ π : Fin 6 → ℤ,
      (CostNetwork.ofNetwork diamondNet diamondCost diamondSubFlow.value).CompSlackness
        (diamondSubFlow.toCostFlow diamondCost) π := by
  rw [← Network.Flow.isMinCostOfValue_iff_exists_compSlackness]
  exact diamondSubFlow_not_minCost

/-! ### 2. Asymmetric antiparallel arcs -/

/-- Two-vertex circulation with asymmetric antiparallel costs (`cost 0 1 + cost 1 0 = 7 ≠ 0`). -/
def antiNet : CostNetwork (Fin 2) ℤ where
  cap u v :=
    match u.val, v.val with
    | 0, 1 => 3
    | 1, 0 => 3
    | _, _ => 0
  cost u v :=
    match u.val, v.val with
    | 0, 1 => 2
    | 1, 0 => 5
    | _, _ => 0
  balance _ := 0

/-- Initial antiparallel circulation placing `2` units on both `(0, 1)` and `(1, 0)`. -/
def antiInitFlow : antiNet.Flow where
  toFun u v :=
    match u.val, v.val with
    | 0, 1 => 2
    | 1, 0 => 2
    | _, _ => 0
  le_cap := by decide
  balance_eq := by decide

example : antiInitFlow.totalCost = 14 := by decide

example : (CostNetwork.cycleCancelInt antiNet [0, 1] antiInitFlow).flow.totalCost = 0 := by
  decide

example : (CostNetwork.cycleCancelInt antiNet [0, 1] antiInitFlow).cancellations = 1 := by
  decide

example : CostNetwork.absCostBound antiNet [0, 1] = 21 := by decide

theorem anti_correct :
    let out := CostNetwork.cycleCancelInt antiNet [0, 1] antiInitFlow
    out.flow.IsMinCost ∧ antiNet.CompSlackness out.flow out.potential ∧
      out.flow.totalCost + (out.cancellations : ℤ) ≤ antiInitFlow.totalCost ∧
      out.cancellations ≤ 2 * CostNetwork.absCostBound antiNet [0, 1] :=
  CostNetwork.cycleCancelInt_correct (fun v => by fin_cases v <;> simp) antiInitFlow

/-- Asymmetric antiparallel network whose two arcs sum to `-3 < 0`. -/
def antiNegNet : CostNetwork (Fin 2) ℤ where
  cap := antiNet.cap
  cost u v :=
    match u.val, v.val with
    | 0, 1 => -4
    | 1, 0 => 1
    | _, _ => 0
  balance _ := 0

example :
    (CostNetwork.cycleCancelInt antiNegNet [0, 1]
      (CostNetwork.Flow.zero antiNegNet fun _ => rfl)).flow.totalCost = -9 := by
  decide

/-! ### 3. Self-loop boundaries -/

/-- Network with both a negative-cost self-loop `(0, 0)` and a positive-cost self-loop `(1, 1)`.
-/
def loopNet : CostNetwork (Fin 2) ℤ where
  cap u v :=
    match u.val, v.val with
    | 0, 0 => 4
    | 1, 1 => 3
    | _, _ => 0
  cost u v :=
    match u.val, v.val with
    | 0, 0 => -2
    | 1, 1 => 3
    | _, _ => 0
  balance _ := 0

/-- Initial self-loop circulation carrying `1` unit on `(0, 0)` and `2` units on `(1, 1)`. -/
def loopInitFlow : loopNet.Flow where
  toFun u v :=
    match u.val, v.val with
    | 0, 0 => 1
    | 1, 1 => 2
    | _, _ => 0
  le_cap := by decide
  balance_eq := by decide

example : loopInitFlow.totalCost = 4 := by decide

example : (CostNetwork.cycleCancelInt loopNet [0, 1] loopInitFlow).flow.totalCost = -8 := by
  decide

example : (CostNetwork.cycleCancelInt loopNet [0, 1] loopInitFlow).cancellations = 2 := by
  decide

example : (CostNetwork.cycleCancelInt loopNet [0, 1] loopInitFlow).flow 0 0 = 4 := by decide

example : (CostNetwork.cycleCancelInt loopNet [0, 1] loopInitFlow).flow 1 1 = 0 := by decide

theorem loop_correct :
    let out := CostNetwork.cycleCancelInt loopNet [0, 1] loopInitFlow
    out.flow.IsMinCost ∧ loopNet.CompSlackness out.flow out.potential := by
  have h := CostNetwork.cycleCancelInt_correct (M := loopNet)
    (vs := [0, 1]) (fun v => by fin_cases v <;> simp) loopInitFlow
  exact ⟨h.1, h.2.1⟩

/-! ### 4. Negative-cost 3-cycle and `N.s = N.t` terminal degeneracy -/

/-- Three-vertex `s`-`t` network with `s = t = 0` containing a negative-cost 3-cycle `0 → 1 → 2 → 0`
of net cost `-3` and bottleneck capacity `2`. -/
def sameTerminalNet : Network (Fin 3) where
  cap u v :=
    match u.val, v.val with
    | 0, 1 => 2
    | 1, 2 => 3
    | 2, 0 => 2
    | 0, 2 => 2
    | _, _ => 0
  s := 0
  t := 0

/-- Costs on `sameTerminalNet`: `0 → 1 → 2 → 0` sums to `1 + (-5) + 1 = -3`. -/
def sameTerminalCost (u v : Fin 3) : ℤ :=
  match u.val, v.val with
  | 0, 1 => 1
  | 1, 2 => -5
  | 2, 0 => 1
  | 0, 2 => 10
  | _, _ => 0

example : (minCostMaxFlow sameTerminalNet sameTerminalCost).flow.value = 0 := by decide

example :
    (minCostMaxFlow sameTerminalNet sameTerminalCost).flow.flowCost sameTerminalCost = -6 := by
  decide

example : (minCostMaxFlow sameTerminalNet sameTerminalCost).cancellations = 1 := by decide

theorem sameTerminal_correct :
    let out := minCostMaxFlow sameTerminalNet sameTerminalCost
    out.flow.IsMaxFlow ∧ out.flow.IsMinCostOfValue sameTerminalCost ∧
      (CostNetwork.ofNetwork sameTerminalNet sameTerminalCost out.flow.value).CompSlackness
        (out.flow.toCostFlow sameTerminalCost) out.potential := by
  have h := minCostMaxFlow_correct sameTerminalNet sameTerminalCost
  exact ⟨h.1, h.2.1, h.2.2.2⟩

/-! ### 5. Non-integer (`ℚ`) cost instantiation -/

/-- Two-vertex unit-supply network with rational arc costs (`1/2` on `0 → 1`, `0` back). -/
def ratNet : CostNetwork (Fin 2) ℚ where
  cap u v :=
    match u.val, v.val with
    | 0, 1 => 2
    | 1, 0 => 1
    | _, _ => 0
  cost u v :=
    match u.val, v.val with
    | 0, 1 => 1 / 2
    | 1, 0 => 1 / 4
    | _, _ => 0
  balance v := if v = 0 then 1 else -1

/-- Optimal flow in `ratNet` (`f 0 1 = 1, f 1 0 = 0`), cost `1/2`. -/
def ratOptFlow : ratNet.Flow where
  toFun u v :=
    match u.val, v.val with
    | 0, 1 => 1
    | _, _ => 0
  le_cap := by decide
  balance_eq v := by fin_cases v <;> decide

/-- Suboptimal flow in `ratNet` (`f 0 1 = 2, f 1 0 = 1`), cost `5/4`. -/
def ratSubFlow : ratNet.Flow where
  toFun u v :=
    match u.val, v.val with
    | 0, 1 => 2
    | 1, 0 => 1
    | _, _ => 0
  le_cap := by decide
  balance_eq v := by fin_cases v <;> decide

/-- Witness node potentials `π = (0, 1/2)` certifying complementary slackness on `ratOptFlow`. -/
def ratPot : Fin 2 → ℚ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1 / 2

theorem ratOptFlow_compSlackness : ratNet.CompSlackness ratOptFlow ratPot := by
  refine ⟨fun u v hlt => ?_, fun u v hpos => ?_⟩
  · fin_cases u <;> fin_cases v <;>
      first | exact absurd hlt (by decide) | (dsimp [ratNet, ratPot]; norm_num)
  · fin_cases u <;> fin_cases v <;>
      first | exact absurd hpos (by decide) | (dsimp [ratNet, ratPot]; norm_num)

theorem ratOptFlow_isMinCost : ratOptFlow.IsMinCost :=
  (CostNetwork.isMinCost_iff_exists_compSlackness ratOptFlow).mpr
    ⟨ratPot, ratOptFlow_compSlackness⟩

theorem ratOptFlow_no_negCycle :
    ¬ ∃ arcs : List (ResArc (Fin 2)), ratOptFlow.IsResCycle arcs ∧ ratNet.walkCost arcs < 0 :=
  (CostNetwork.isMinCost_iff_not_exists_negCycle ratOptFlow).mp ratOptFlow_isMinCost

theorem ratSubFlow_not_isMinCost : ¬ ratSubFlow.IsMinCost := by
  rw [CostNetwork.isMinCost_iff_not_exists_negCycle]
  push Not
  refine ⟨[⟨1, 0, false⟩, ⟨0, 1, false⟩], by decide, ?_⟩
  simp only [CostNetwork.walkCost, CostNetwork.resCost, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Bool.false_eq_true, ↓reduceIte, ratNet]
  norm_num

theorem ratNet_exists_opt :
    ∃ (f : ratNet.Flow) (π : Fin 2 → ℚ), f.IsMinCost ∧ ratNet.CompSlackness f π :=
  CostNetwork.exists_isMinCost_of_feasible ⟨ratSubFlow⟩

end CslibFrontierTests.MinCostFlow
