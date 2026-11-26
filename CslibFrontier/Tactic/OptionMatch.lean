/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public meta import Lean.Elab.Tactic

/-!
# Option matches as eliminators

`fun_prop` cannot see through a `match`: its auxiliary matcher is a constant of the defining
function, and it does not reduce on a stuck discriminant. Rules are therefore stated for
`Option.elim`. The tactic `option_match_to_elim` rewrites non-dependent option `match` expressions
and option combinators in the goal, under binders and nested, to `Option.elim`, so that a definition
written with `match` or `do` notation needs no separate statement in terms of tests and defaults.

Supported forms:

* non-dependent `match` expressions on one or more `Option` discriminants (with alternatives in any
  order), including irrefutable tuple or structure patterns (`some (a, b)`, `some ⟨a, b⟩`), whose
  bindings reduce to projections on the `Option.elim` payload;
* `Option.bind`, monadic `Bind.bind` on `Option` (`do let x ← o; …`), `Option.any`, and
  `Option.toList`;
* `Option.map` unfolds to a supported `match` via `unfold Option.map` while preserving direct
  `Option.map` applications for `optionMapWithInput`.

Dependent matches and alternatives that match refutable payload constructors (such as `some true`
or `some (.inl x)`) are left unchanged.
-/

public meta section

namespace Cslib.Tactic

open Lean Meta Elab Tactic

/-- Close `lhs = rhs` by `rfl` after splitting generalized `Option` discriminants. -/
private partial def closeByOptionCases (goal : MVarId) : List FVarId → MetaM Unit
  | [] => goal.refl
  | fv :: rest => do
    try
      goal.refl
    catch _ =>
      for sub in ← goal.cases fv do
        let rest' := rest.filterMap fun id =>
          match sub.subst.get id with
          | .fvar id' => some id'
          | _ => none
        closeByOptionCases sub.mvarId rest'

/-- Prove `lhs = rhs` by case analysis on the `Option` discriminants. This runs inside `simp`,
whose reducible transparency would not unfold `Option.elim`. -/
private def eqByCases (lhs rhs : Expr) (discrs : Array Expr) : MetaM Expr := withDefault do
  let optDiscrs ← discrs.filterM fun d => return (← whnfR (← inferType d)).isAppOfArity ``Option 1
  let goal ← mkFreshExprMVar (← mkEq lhs rhs)
  let (fvars, generalized) ← goal.mvarId!.generalize (optDiscrs.map fun d => { expr := d })
  closeByOptionCases generalized fvars.toList
  instantiateMVars goal

/-- Convert a non-dependent `MatcherApp` on `Option` discriminants into nested `Option.elim`
applications, using `reduceMatcher?` so structure and tuple patterns reduce to projections while
expressions inside branch bodies remain intact. -/
private partial def evalOptionMatcher? (m : MatcherApp) (idx : Nat)
    (fixedDiscrs : Array Expr) : MetaM (Option Expr) := do
  if idx > 0 then
    let candidate := fixedDiscrs ++ m.discrs.extract idx m.discrs.size
    if let .reduced res ← reduceMatcher? { m with discrs := candidate }.toExpr then
      return some res.headBeta
  if idx ≥ m.discrs.size then return none
  let discr := m.discrs[idx]!
  let .app (.const ``Option _) α ← whnfR (← inferType discr) | return none
  let some noneBr ← evalOptionMatcher? m (idx + 1) (fixedDiscrs.push (← mkNone α))
    | return none
  let some someFn ← withLocalDeclD `x α fun p => do
    let someTerm ← mkAppOptM ``Option.some #[α, p]
    if let some sb ← evalOptionMatcher? m (idx + 1) (fixedDiscrs.push someTerm) then
      return some (← mkLambdaFVars #[p] sb)
    return none
    | return none
  return some (← mkAppOptM ``Option.elim #[α, ← inferType noneBr, discr, noneBr, someFn])

/-- The `Option.elim` form of `Option.bind`, monadic `Bind.bind` on `Option`, `Option.any`,
`Option.toList`, or a non-dependent `match` on `Option` discriminants, with its proof. -/
private def optionMatch? (e : Expr) : MetaM (Option Simp.Result) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Option.bind 4 then
    let #[α, β, discr, f] := e.getAppArgs | return none
    try
      let rhs ← mkAppOptM ``Option.elim #[α, ← inferType e, discr, ← mkNone β, f]
      return some { expr := rhs, proof? := some (← eqByCases e rhs #[discr]) }
    catch _ => return none
  if e.isAppOfArity ``Bind.bind 6 then
    let #[monad, _, α, β, discr, f] := e.getAppArgs | return none
    unless (← whnfR monad).isConstOf ``Option do return none
    try
      let rhs ← mkAppOptM ``Option.elim #[α, ← inferType e, discr, ← mkNone β, f]
      return some { expr := rhs, proof? := some (← eqByCases e rhs #[discr]) }
    catch _ => return none
  if e.isAppOfArity ``Option.any 3 then
    let #[α, p, discr] := e.getAppArgs | return none
    try
      let rhs ← mkAppOptM ``Option.elim #[α, mkConst ``Bool, discr, mkConst ``Bool.false, p]
      return some { expr := rhs, proof? := some (← eqByCases e rhs #[discr]) }
    catch _ => return none
  if e.isAppOfArity ``Option.toList 2 then
    let #[α, discr] := e.getAppArgs | return none
    try
      let nil ← mkAppOptM ``List.nil #[α]
      let consFn ← withLocalDeclD `x α fun x => do
        mkLambdaFVars #[x] (← mkAppOptM ``List.cons #[α, x, nil])
      let rhs ← mkAppOptM ``Option.elim #[α, ← inferType e, discr, nil, consFn]
      return some { expr := rhs, proof? := some (← eqByCases e rhs #[discr]) }
    catch _ => return none
  let some m ← matchMatcherApp? e | return none
  unless m.discrs.size ≥ 1 && m.alts.size ≥ 2 && m.remaining.isEmpty do return none
  unless (← whnfR (← inferType m.discrs[0]!)).isAppOfArity ``Option 1 do return none
  let dependent ← lambdaTelescope m.motive fun xs body =>
    xs.anyM fun x => do
      return body.containsFVar x.fvarId! ||
        (← xs.anyM fun y => return (← inferType y).containsFVar x.fvarId!)
  if dependent then return none
  try
    let some rhs ← evalOptionMatcher? m 0 #[] | return none
    return some { expr := rhs, proof? := some (← eqByCases e rhs m.discrs) }
  catch _ => return none

/-- Rewrite every supported non-dependent `Option` match, `Option.bind`, monadic `Bind.bind` on
`Option`, `Option.any`, and `Option.toList` in the goal to `Option.elim`. -/
syntax (name := optionMatchToElim) "option_match_to_elim" : tactic

@[inherit_doc optionMatchToElim]
elab_rules : tactic | `(tactic| option_match_to_elim) => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let methods : Simp.Methods := {
      pre := fun e => do
        match ← optionMatch? e with
        | some r => return .visit r
        | none => return .continue }
    let (result, _) ← Simp.main target (← Simp.mkContext) (methods := methods)
    if result.expr == target then
      throwError "option_match_to_elim: no option match in the goal"
    replaceMainGoal [← applySimpResultToTarget goal target result]

end Cslib.Tactic
