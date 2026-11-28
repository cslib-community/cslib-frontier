/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Balanced
public import CslibFrontier.Computability.Circuit.Iteration
public import CslibFrontier.Computability.Circuit.MapOp
public import CslibFrontier.Computability.Circuit.Simulation
public import CslibFrontier.Computability.Circuit.Wiring
public import CslibFrontier.Tactic.CircuitBound
public import Mathlib.Order.Fin.Tuple

/-!
# Normalizing and bounding circuits built with combinators

Fills the simp set `circuit_simps` and registers the rules of the tactic `circuit_bound` for the
circuit combinators `Circuit.comp`, `Circuit.append`, `Circuit.pi`, `Circuit.wiring`,
`Circuit.wiringOn`, `Circuit.oneGate`, `Circuit.mapOp`, `Circuit.iterate`, `Formula.gate` and
`Formula.toCircuit`.

* `simp only [circuit_simps, step]` rewrites the function, size, program cost and exact depths of
  the circuit `step` to those of its parts. The simp set unfolds no definition, so the definitions
  of the construction are named beside it.
* `circuit_bound [step]` proves a bound `(step k).depth ≤ 2`. Composition only bounds the depth, so
  the depth rules `Circuit.depth_comp_le`, `Circuit.depth_append_le`, `Circuit.depth_pi_le` and
  `Circuit.depth_iterate_le`, and those of `depthWith`, are registered with `@[circuit_bound]`
  instead of being simp lemmas.

A module that proves a bound of a named circuit tags it `@[circuit_bound]`, and later
constructions that contain the circuit then use the bound without naming it.

The simp set holds the lemmas that a proof in the library uses through it. A lemma of the same
kind that is missing, such as `Circuit.eval_iterate` or `Formula.eval_gate₂`, is added here with
its first use.

## Main definitions

* `Circuit.costProgram`: the simplification procedure of `circuit_simps` for the program cost of a
  combinator or compiled formula. It applies `Circuit.cost_program_comp`,
  `Circuit.cost_program_append`, `Circuit.cost_program_pi`, `Circuit.cost_program_wiring`,
  `Circuit.cost_program_wiringOn`, `Circuit.cost_program_oneGate`,
  `Circuit.cost_program_iterate` and `Formula.cost_toCircuit`, which cannot be simp lemmas of a set
  that also rewrites the gate count, an implicit argument of the cost.
-/

public section

namespace Cslib.Circuits

/-- The supremum over `Fin 0` is `⊥`. -/
theorem sup_univ_fin_zero {α : Type*} [SemilatticeSup α] [OrderBot α] (f : Fin 0 → α) :
    Finset.univ.sup f = ⊥ := by
  simp

/-- The supremum over `Fin 1` is the value at `0`. -/
theorem sup_univ_fin_one {α : Type*} [SemilatticeSup α] [OrderBot α] (f : Fin 1 → α) :
    Finset.univ.sup f = f 0 := by
  simp [Finset.univ_unique]

/-- The supremum over `Fin 2` is the maximum of the values at `0` and `1`. -/
theorem sup_univ_fin_two {α : Type*} [LinearOrder α] [OrderBot α] (f : Fin 2 → α) :
    Finset.univ.sup f = max (f 0) (f 1) := by
  simp [Fin.univ_succ]

attribute [circuit_simps]
  -- functions
  Circuit.eval_comp Circuit.eval_append Circuit.eval_pi Circuit.eval_wiring Circuit.eval_wiringOn
  Circuit.eval_oneGate Formula.eval_toCircuit Formula.eval_input Formula.eval_gate
  -- sizes and formula costs
  Circuit.size_comp Circuit.size_append Circuit.size_pi Circuit.size_wiring Circuit.size_wiringOn
  Circuit.size_oneGate Circuit.size_mapOp Circuit.size_iterate Formula.size_toCircuit
  Formula.size_input Formula.size_gate Formula.leafSize_input Formula.leafSize_gate
  Formula.cost_input Formula.cost_gate
  -- exact depths
  Circuit.depth_wiring Circuit.depth_oneGate Circuit.depth_mapOp Circuit.depthWith_wiring
  Circuit.depthWith_oneGate Formula.depth_input Formula.depth_gate Formula.depthWith_input
  Formula.depthWith_gate
  -- reading blocks, small-arity tuples, list summaries, and constant sums or suprema
  Fin.append_left Fin.append_right Function.comp_apply Finset.sum_const Finset.card_univ
  Fintype.card_fin smul_eq_mul Fin.sum_univ_zero Fin.sum_univ_one Fin.sum_univ_two
  sup_univ_fin_zero sup_univ_fin_one sup_univ_fin_two Nat.bot_eq_zero Matrix.cons_val_zero
  Matrix.cons_val_one List.map_ofFn List.sum_ofFn List.length_ofFn List.map_append
  List.sum_append List.length_append List.map_map List.length_map

open Lean Meta in
/-- Rewrites the program cost of a circuit built with a combinator to the costs of its parts, by
`Circuit.cost_program_comp` and the like. Those are not simp lemmas: once `simp` has rewritten the
gate count, an implicit argument of `Program.cost`, by `Circuit.size_comp` they no longer match.
This procedure reads only the circuit and the cost function. -/
simproc [circuit_simps] Circuit.costProgram (Program.cost _ _) := fun e => do
  let_expr Program.cost _ _ _ program cost := e | return .continue
  for rule in #[``Circuit.cost_program_comp, ``Circuit.cost_program_append,
      ``Circuit.cost_program_pi, ``Circuit.cost_program_wiring, ``Circuit.cost_program_wiringOn,
      ``Circuit.cost_program_oneGate, ``Circuit.cost_program_iterate,
      ``Formula.cost_toCircuit] do
    -- as in a rewrite by a simp lemma, matching assigns no metavariable of the goal
    let step? ← withNewMCtxDepth do
      let proof ← mkConstWithFreshMVarLevels rule
      let (args, _, type) ← forallMetaTelescope (← inferType proof)
      let some (_, lhs, rhs) := type.eq? | return none
      let_expr Program.cost _ _ _ program' cost' := lhs | return none
      unless ← isDefEq program' program <&&> isDefEq cost' cost do return none
      let rhs ← instantiateMVars rhs
      let proof ← instantiateMVars (mkAppN proof args)
      if (← hasAssignableMVar rhs) || (← hasAssignableMVar proof) then return none
      return some (rhs, proof)
    if let some (rhs, proof) := step? then
      trace[Meta.Tactic.simp.rewrite] "{.ofConstName rule}:{indentExpr e}\n==>{indentExpr rhs}"
      return .visit { expr := rhs, proof? := proof }
  return .continue

attribute [circuit_bound]
  Circuit.depth_comp_le Circuit.depth_append_le Circuit.depth_pi_le Circuit.depth_iterate_le
  Circuit.depthWith_comp_le Circuit.depthWith_append_le Circuit.depthWith_pi_le
  Circuit.depthWith_iterate_le Circuit.size_balanced_le Circuit.depth_balanced_le_max
  Formula.depth_toCircuit_le Formula.depthWith_toCircuit_le Formula.depth_bind_le
  Formula.size_bind_le

end Cslib.Circuits

end
