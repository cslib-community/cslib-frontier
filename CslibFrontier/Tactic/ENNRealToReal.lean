/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Finiteness
public import CslibFrontier.Tactic.ENNRealToReal.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Elab.Tactic.SolveByElim

/-!
# Reading a finite `ℝ≥0∞` statement in `ℝ`

Probabilities take values in `ℝ≥0∞`, while error bounds are stated and combined in `ℝ`, where
`linarith`, `nlinarith`, `field_simp` and `norm_num` work. Crossing over by hand takes three
steps: choose the bridge lemma (`ENNReal.toReal_mono`, `ENNReal.toReal_le_toReal`,
`ENNReal.toReal_eq_toReal_iff'`, `ENNReal.ofReal_le_iff_le_toReal`), prove each side finite with a
term that mirrors its shape, and push `ENNReal.toReal` through the arithmetic with
`ENNReal.toReal_add`, `ENNReal.toReal_ofReal` and their relatives, which ask for the same finiteness
facts again.

`ennreal_to_real` does the three steps. For a goal or hypothesis `a R b` in `ℝ≥0∞`, with `R` one
of `≤`, `<`, `=`, `≠`, it proves the needed sides finite with `finiteness`, replaces the statement
by `a.toReal R b.toReal` (`ENNReal.ofReal r ≤ b` drops `ofReal` directly without requiring
`0 ≤ r`), and pushes `toReal` to the leaves with the simp set `ennreal_toReal`. On a statement that
is already real it only pushes `toReal`.

## Main definitions

* `ennreal_to_real`, `ennreal_to_real at h₁ h₂ ⊢`: the transfer, at the goal or at hypotheses.
* `ennreal_to_real using e`: transfers the goal and the fact `e`, and closes the goal with it.
* `ennreal_toReal`: the simp set, declared in `CslibFrontier.Tactic.ENNRealToReal.Init` and
  tagged here. Tag a lemma `(f x).toReal = …` with it to teach the tactic a new operation, and
  register `f x ≠ ∞` as a `finiteness` rule to teach it a new finite quantity.

## Implementation notes

A side condition that is not found leaves its `toReal` in place and the rest is still rewritten,
so a missing fact shows in the resulting goal. Side conditions are dispatched on their shape:
`x ≠ ∞` goes to `finiteness` and an inequality to local hypotheses (including quantified ones via
bounded `solve_by_elim`), `positivity` and `norm_cast`. A failing `finiteness` call is the
expensive case (most of a second on a term with three unknown atoms), which the dispatch keeps off
the inequalities.
-/

public section

namespace Cslib.Tactic.ENNRealToReal

/-- Push `ENNReal.toReal` inside `if … then … else …`. -/
@[ennreal_toReal]
theorem toReal_ite (p : Prop) [Decidable p] (a b : ENNReal) :
    (if p then a else b).toReal = if p then a.toReal else b.toReal :=
  apply_ite ENNReal.toReal p a b

end Cslib.Tactic.ENNRealToReal

attribute [ennreal_toReal] ENNReal.toReal_add ENNReal.toReal_mul ENNReal.toReal_sum
  ENNReal.toReal_prod ENNReal.toReal_pow ENNReal.toReal_inv ENNReal.toReal_div
  ENNReal.toReal_natCast ENNReal.toReal_ofNat ENNReal.toReal_one ENNReal.toReal_zero
  ENNReal.toReal_ofReal ENNReal.toReal_sub_of_le ENNReal.tsum_toReal_eq ENNReal.coe_toReal

attribute [ennreal_toReal ←] ENNReal.toReal_rpow

end

public meta section

namespace Cslib.Tactic.ENNRealToReal

open Lean Meta Elab Tactic

/-- Discharges a side condition of the simp set `ennreal_toReal`, for `ennreal_to_real`:
`x ≠ ∞`, also under binders as in `∀ i ∈ s, f i ≠ ∞`, by `finiteness`; `0 ≤ r` and `b ≤ a` from
a hypothesis, also up to casts as in `(c : ℝ≥0∞) ≤ 1` from `c ≤ 1`, and `0 ≤ r` also by
`positivity`. It fails with an ordinary error when the condition is not found. -/
syntax (name := ennrealSide) "ennreal_to_real_side" : tactic

elab_rules : tactic
  | `(tactic| ennreal_to_real_side) => do
    let (_, goal) ← (← getMainGoal).intros
    replaceMainGoal [goal]
    let type := (← instantiateMVars (← goal.getType)).cleanupAnnotations
    let tactic ← if type.isAppOf ``Ne || type.isAppOf ``Not then `(tactic| finiteness)
      else `(tactic| first | assumption | solve_by_elim (maxDepth := 3) | positivity | norm_cast)
    -- `simp` runs a discharger without error recovery around it: a tactic that reports its own
    -- failure (it logs the error and admits the goal, as `done` does) would have the side
    -- condition accepted. So every failure is turned into an ordinary error here; the `catch`
    -- restores the state, which removes the logged error and the admitted goal.
    try
      withoutRecover (evalTactic tactic)
    catch _ => throwError "ennreal_to_real: side condition not found"
    unless (← getUnsolvedGoals).isEmpty do
      throwError "ennreal_to_real: side condition not found"

/-- The relations that `ennreal_to_real` transfers. -/
private inductive Rel where
  | le | lt | eq | ne

/-- Splits a statement `a R b` about `a b : ℝ≥0∞` into `R`, `a` and `b`. -/
private def matchRel? (e : Expr) : MetaM (Option (Rel × Expr × Expr)) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  let ifENNReal (α : Expr) (r : Rel × Expr × Expr) : MetaM (Option (Rel × Expr × Expr)) := do
    return if (← whnfR α).isConstOf ``ENNReal then some r else none
  match_expr e with
  | LE.le α _ a b => ifENNReal α (.le, a, b)
  | LT.lt α _ a b => ifENNReal α (.lt, a, b)
  | Eq α a b => ifENNReal α (.eq, a, b)
  | Ne α a b => ifENNReal α (.ne, a, b)
  | Not p =>
    match_expr p.cleanupAnnotations with
    | Eq α a b => ifENNReal α (.ne, a, b)
    | _ => return none
  | _ => return none

/-- Proves `e ≠ ∞` with `finiteness`. On failure, the error names what `finiteness` could not
show finite. -/
private def proveNeTop (e : Expr) : TacticM Expr := do
  let type ← mkAppM ``Ne #[e, mkConst ``Top.top [0] |>.app (mkConst ``ENNReal) |>.app
    (← synthInstance (mkApp (mkConst ``Top [0]) (mkConst ``ENNReal)))]
  let saved ← saveState
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  try
    let rest ← Tactic.run goal.mvarId! (evalTactic (← `(tactic| finiteness)))
    unless rest.isEmpty do throwError "unsolved goals"
    instantiateMVars goal
  catch _ =>
    saved.restore
    let goal ← mkFreshExprSyntheticOpaqueMVar type
    let rest ← try
        Tactic.run goal.mvarId! (evalTactic (← `(tactic| finiteness_nonterminal)))
      catch _ => pure [goal.mvarId!]
    let left ← rest.mapM fun g => g.withContext do
      addMessageContext m!"{indentExpr (← instantiateMVars (← g.getType))}"
    saved.restore
    throwError "ennreal_to_real: could not show that{indentExpr e}\nis finite. \
      `finiteness` is left with{MessageData.joinSep left ""}\n\
      Add the missing fact as a hypothesis, or register it as a `finiteness` rule."

/-- The equivalence between the real statement and `a R b` for finite `a` and `b`, together with
the syntactic target type in `ℝ`. On `ENNReal.ofReal r ≤ b`, drops `ENNReal.ofReal` directly
without requiring `0 ≤ r`. -/
private def bridge (rel : Rel) (a b : Expr) : TacticM (Expr × Expr) := do
  let a := a.cleanupAnnotations
  let b := b.cleanupAnnotations
  match rel with
  | .le =>
    let iff ← if a.isAppOfArity ``ENNReal.ofReal 1 then
        let fwd ← mkAppOptM ``ENNReal.ofReal_le_iff_le_toReal
          #[some a.appArg!, some b, some (← proveNeTop b)]
        mkAppM ``Iff.symm #[fwd]
      else
        mkAppM ``ENNReal.toReal_le_toReal #[← proveNeTop a, ← proveNeTop b]
    let some (real, _) := (← inferType iff).iff? | throwError "ennreal_to_real: internal error"
    return (iff, real)
  | .lt =>
    let iff ← mkAppM ``ENNReal.toReal_lt_toReal #[← proveNeTop a, ← proveNeTop b]
    let some (real, _) := (← inferType iff).iff? | throwError "ennreal_to_real: internal error"
    return (iff, real)
  | .eq =>
    let iff ← mkAppM ``ENNReal.toReal_eq_toReal_iff' #[← proveNeTop a, ← proveNeTop b]
    let some (real, _) := (← inferType iff).iff? | throwError "ennreal_to_real: internal error"
    return (iff, real)
  | .ne =>
    let eqIff ← mkAppM ``ENNReal.toReal_eq_toReal_iff' #[← proveNeTop a, ← proveNeTop b]
    let iff ← mkAppM ``not_congr #[eqIff]
    let real ← mkAppM ``Ne #[← mkAppM ``ENNReal.toReal #[a], ← mkAppM ``ENNReal.toReal #[b]]
    return (iff, real)

/-- Replaces a goal `a R b` in `ℝ≥0∞` by `a.toReal R b.toReal`. Returns `false` on other goals. -/
private def transferGoal : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let some (rel, a, b) ← matchRel? (← goal.getType) | return false
  let (iff, real) ← bridge rel a b
  let new ← mkFreshExprSyntheticOpaqueMVar real (← goal.getTag)
  goal.assign (← mkAppM ``Iff.mp #[iff, new])
  replaceMainGoal [new.mvarId!]
  return true

/-- Replaces a hypothesis `h : a R b` in `ℝ≥0∞` by `h : a.toReal R b.toReal`. Returns `false` on
other hypotheses. -/
private def transferHyp (fvarId : FVarId) : TacticM Bool := withMainContext do
  let h := mkFVar fvarId
  let some (rel, a, b) ← matchRel? (← fvarId.getType) | return false
  let a := a.cleanupAnnotations
  let b := b.cleanupAnnotations
  let (proof, type?) ← match rel with
    | .le =>
      if a.isAppOfArity ``ENNReal.ofReal 1 then
        let iff ← mkAppOptM ``ENNReal.ofReal_le_iff_le_toReal
          #[some a.appArg!, some b, some (← proveNeTop b)]
        pure (← mkAppM ``Iff.mp #[iff, h], none)
      else
        pure (← mkAppM ``ENNReal.toReal_mono #[← proveNeTop b, h], none)
    | .lt =>
      pure (← mkAppM ``ENNReal.toReal_strict_mono #[← proveNeTop b, h], none)
    | .eq => pure (← mkCongrArg (mkConst ``ENNReal.toReal) h, none)
    | .ne =>
      let eqIff ← mkAppM ``ENNReal.toReal_eq_toReal_iff' #[← proveNeTop a, ← proveNeTop b]
      let iff ← mkAppM ``not_congr #[eqIff]
      let real ← mkAppM ``Ne #[← mkAppM ``ENNReal.toReal #[a], ← mkAppM ``ENNReal.toReal #[b]]
      pure (← mkAppM ``Iff.mpr #[iff, h], some real)
  replaceMainGoal [(← (← getMainGoal).replace fvarId proof type?).mvarId]
  return true

/-- The argument of a `toReal` of a sum in `e`, the kind of term that `ennreal_toReal` rewrites
only when the sum is known to be finite. -/
private def toRealOfSum? (e : Expr) : Option Expr :=
  let isSum (x : Expr) := x.isAppOf ``HAdd.hAdd || x.isAppOf ``Finset.sum
  (e.find? fun t => t.isAppOfArity ``ENNReal.toReal 1 && !t.hasLooseBVars && isSum t.appArg!).map
    (·.appArg!)

/-- The core of `ennreal_to_real`: transfer at each location, then push `toReal`. -/
private def run (loc : Option (TSyntax ``Parser.Tactic.location)) (failIfUnchanged : Bool) :
    TacticM Unit := withMainContext do
  let mut changed := false
  let (hyps, type) ← match expandOptLocation (mkOptionalNode loc) with
    | .wildcard => throwError "ennreal_to_real: `at *` is not supported; name the hypotheses"
    | .targets hyps type => pure (hyps, type)
  for hyp in hyps do
    if ← transferHyp (← getFVarId hyp) then changed := true
  if type then
    if ← transferGoal then changed := true
  let before ← getUnsolvedGoals
  evalTactic (← `(tactic|
    simp -failIfUnchanged (disch := ennreal_to_real_side) only [ennreal_toReal] $[$loc]?))
  if failIfUnchanged && !changed && before == (← getUnsolvedGoals) then
    withMainContext do
      -- A `toReal` of a sum that stayed in place has an infinite-looking summand: name it.
      let mut statements ← hyps.mapM fun hyp => do (← getFVarId hyp).getType
      if type then statements := statements.push (← getMainTarget)
      for statement in statements do
        if let some sum := toRealOfSum? (← instantiateMVars statement) then
          discard <| proveNeTop sum
      throwError "ennreal_to_real made no progress: no `ℝ≥0∞` relation to transfer and no \
        `toReal` to push.\nA `toReal` stays in place when its side condition is not found:\n\
        `(a - b).toReal` needs `b ≤ a`, and `(ENNReal.ofReal r).toReal` needs `0 ≤ r`."

/-- `ennreal_to_real` reads a statement about finite elements of `ℝ≥0∞` in `ℝ`.

For a goal `a R b` with `a b : ℝ≥0∞` and `R` one of `≤`, `<`, `=`, `≠`, it proves the sides finite
with `finiteness`, replaces the goal by `a.toReal R b.toReal` (`ENNReal.ofReal r ≤ b` drops
`ofReal` without requiring `0 ≤ r`), and pushes `toReal` to the leaves with the simp set
`ennreal_toReal`: through `+`, `*`, `∑`, `∏`, `∑'`, natural and real `^`, `⁻¹`, `/`,
`if … then … else …`, numerals, casts and `ENNReal.ofReal`. A goal that is already real only has
its `toReal`s pushed.

* `ennreal_to_real at h₁ h₂ ⊢` does the same at hypotheses. A hypothesis `a ≤ b` or `a < b` needs
  only `b` finite, `a = b` needs nothing, and `a ≠ b` needs both `a` and `b` finite.
* `ennreal_to_real using e` transfers the goal and the fact `e`, then closes the goal with `e`.
  The term `e` is elaborated on its own, without the goal as expected type.

```lean
example (p q : PMF α) (s : Set α) {ε : ℝ} (hε : 0 ≤ ε)
    (h : p.toOuterMeasure s ≤ q.toOuterMeasure s + ENNReal.ofReal ε) :
    (p.toOuterMeasure s).toReal ≤ (q.toOuterMeasure s).toReal + ε := by
  ennreal_to_real using h
```

The tactic fails, naming the term, when `finiteness` cannot show a side finite; give the missing
fact as a hypothesis or register it as a `finiteness` rule. A subterm whose side condition is not
found is left under `toReal`: `(a - b).toReal` needs `b ≤ a` as a hypothesis, and
`(ENNReal.ofReal r).toReal` needs `0 ≤ r` from a hypothesis or `positivity`. Under `∑'` each term
must be finite by its shape, so push `toReal` through an outer `∑'` before unfolding a
probability inside it into another `∑'`. The rewriting is a fixed `simp only`, so the tactic may
be used in the middle of a proof. -/
syntax (name := ennrealToReal) "ennreal_to_real" (Parser.Tactic.location)? : tactic

@[tactic_alt ennrealToReal]
syntax (name := ennrealToRealUsing) "ennreal_to_real" " using " term : tactic

elab_rules : tactic
  | `(tactic| ennreal_to_real $[$loc]?) => run loc true

elab_rules : tactic
  | `(tactic| ennreal_to_real using $e) => do
    let h := mkIdent (← mkFreshUserName `h)
    evalTactic (← `(tactic| have $h:ident := $e))
    run (← `(Parser.Tactic.location| at $h:ident ⊢)) false
    evalTactic (← `(tactic| exact $h))

end Cslib.Tactic.ENNRealToReal

end
