/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public meta import Lean.Elab.Tactic.Omega

/-!
# Heartbeat-bounded `omega` proof attempts

Provides the shared bounded-`omega` helper `Cslib.Tactic.WramOmega.proveOmega?` used by `wram_omega`
(for pairwise power-of-two exponent comparisons) and `fits` (`reduceFits` and side-queries) to
attempt closing an auxiliary proposition from explicit proof terms under a local heartbeat cap
without leaking metavariable or kernel state on failure.

## Main definitions

* `Cslib.Tactic.WramOmega.proveOmega?`: attempt to prove a proposition by `omega` from explicit
  hypotheses within a given `maxHeartbeats` budget (in thousands), restoring `MetaM` state on
  failure or timeout.
-/

public meta section

namespace Cslib.Tactic.WramOmega

open Lean Meta Elab.Tactic

/-- Attempt to prove `goalType` by `omega` from `hyps` within `maxHeartbeats` (in thousands, as for
the `maxHeartbeats` option), returning `none` and restoring the `MetaM` state if `omega` fails or
exhausts the budget. -/
def proveOmega? (maxHeartbeats : ℕ) (hyps : List Expr) (goalType : Expr) :
    MetaM (Option Expr) := do
  if goalType.hasLooseBVars then return none
  let saved ← saveState
  let restore : MetaM (Option Expr) := do saved.restore; return none
  let budget (x : MetaM (Option Expr)) : MetaM (Option Expr) :=
    withCurrHeartbeats <| withTheReader Core.Context
      (fun ctx => { ctx with maxHeartbeats := maxHeartbeats * 1000 }) x
  let attempt : MetaM (Option Expr) := do
    let g ← mkFreshExprSyntheticOpaqueMVar goalType
    if let some g' ← g.mvarId!.falseOrByContra then
      g'.withContext do
        let some neg := (← getLCtx).lastDecl | failure
        Omega.omega (neg.toExpr :: hyps) g'
    let prf ← instantiateMVars g
    if prf.hasExprMVar then restore else return some prf
  tryCatchRuntimeEx (try budget attempt catch _ => restore) fun _ => restore

end Cslib.Tactic.WramOmega

end
