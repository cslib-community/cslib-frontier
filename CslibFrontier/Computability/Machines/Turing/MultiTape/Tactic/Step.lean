/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Tactic.Step.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.FinCases
public meta import Lean.Elab.Tactic.Basic

/-!
# Steps and equalities of multi-tape configurations

A proof that follows a multi-tape machine shows again and again that two descriptions of a
configuration agree: `tm.step cfg = cfg'`, `action.apply cfg = cfg'`, or an initial or embedded
configuration written in two ways. By hand this is `Turing.Cfg.ext`, a `funext` on the work tapes,
and a case split on the tape index chosen to match the way the tapes were written. The tactic
`tm_step` takes these steps and reads the case split off the goal.

No step function or transition table is a `simp` lemma: `tm_step` unfolds the step itself and takes
the table among its arguments.

## Main definitions

* `tm_step`, `tm_step [defs, facts]`: prove an equality of configurations (`Turing.Cfg`,
  `Turing.MultiTapeMachine.Config`), or fail showing the cases that `simp` does not close.
* `tm_step_simps`: the simp set with which `tm_step` computes the fields of a configuration after
  an action, and the values of a family of tapes at the indices it splits on. It is declared in
  `CslibFrontier.Computability.Machines.Turing.MultiTape.Tactic.Step.Init` and filled here.
-/

public section

attribute [tm_step_simps] Turing.Action.apply_state Turing.Action.apply_inputPos
  Turing.Action.apply_workTapes Turing.Action.apply_workTapePos Turing.Action.apply_output
  Turing.Cfg.withState Turing.Cfg.prependOutput Turing.wordsCfg Turing.Cfg.workTapeSymbols
  Turing.MultiTapeTM.tr_ofTr Turing.MultiTapeTM.q₀_ofTr Turing.MultiTapeTM.step_of_halt
  Turing.moveInputPos_zero
  Function.update_self Function.update_of_ne Fin.castSucc_ne_last
  Fin.lastCases_last Fin.lastCases_castSucc Fin.addCases_left Fin.addCases_right
  Fin.append_left Fin.append_right Fin.snoc_last Fin.snoc_castSucc
  SignType.coe_zero SignType.coe_one SignType.coe_neg_one add_zero zero_add
  Option.toList_none Option.toList_some List.append_nil

end

public meta section

namespace Turing.StepTactic

open Lean Meta Elab Tactic

/-- The monad of `tm_step`: the simp lemmas of the call, and the number of cases the field being
compared has been split into. -/
private abbrev M := ReaderT (Array Syntax) <| StateRefT Nat TacticM

/-- The most cases `tm_step` splits one field into. -/
private def maxCases : Nat := 8

/-- Run `x`, keeping its effect when it returns `true` and restoring the state otherwise, also
when it throws. -/
private def attempt (x : TacticM Bool) : TacticM Bool :=
  try commitWhen x catch _ => pure false

/-- The goals `tac` leaves of `g`, or `none`, with the state restored, when it fails. -/
private def tryTac (tac : TSyntax `tactic) (g : MVarId) : TacticM (Option (List MVarId)) :=
  commitWhenSomeNoEx? (some <$> evalTacticAt tac g)

/-- The simp lemmas of the call followed by the hypotheses `hyps` of the cases split so far. -/
private def simpLemmas (hyps : Array FVarId) :
    M (Syntax.TSepArray [``Parser.Tactic.simpStar, ``Parser.Tactic.simpErase,
      ``Parser.Tactic.simpLemma] ",") := do
  let mut args ← read
  for h in hyps do
    let t ← Term.exprToSyntax (mkFVar h)
    args := args.push (← `(Parser.Tactic.simpLemma| $t:term))
  return ⟨(Syntax.mkSep args (mkAtom ",")).getArgs⟩

/-- Simplify `g` with `tm_step_simps`, the lemmas of the call and `hyps` only. Returns `none` when
this closes the goal. -/
private def simpOnly (g : MVarId) (hyps : Array FVarId) : M (Option MVarId) := g.withContext do
  let ls ← simpLemmas hyps
  match ← evalTacticAt (← `(tactic| simp -failIfUnchanged only [tm_step_simps, ↓reduceIte,
      ne_eq, not_false_eq_true, $ls,*])) g with
  | [] => return none
  | [g] => return some g
  | _ => throwError "tm_step: `simp only` left more than one goal"

/-- Close `g` with `simp`, using `tm_step_simps`, the lemmas of the call and `hyps`, then `omega` on
what is left. When that fails, simplify the case hypotheses `hyps` as well, which closes a case
whose hypotheses contradict each other. -/
private def closeBySimp (g : MVarId) (hyps : Array FVarId) : M Bool := g.withContext do
  let ls ← simpLemmas hyps
  if ← attempt do
      return (← evalTacticAt (← `(tactic| (simp [tm_step_simps, $ls,*] <;> omega))) g).isEmpty then
    return true
  if hyps.isEmpty then return false
  let ls ← simpLemmas #[]
  attempt do
    let (_, g) ← g.revert hyps (preserveOrder := true)
    return (← evalTacticAt
      (← `(tactic| (simp +contextual [tm_step_simps, $ls,*] <;> omega))) g).isEmpty

/-- Close an equality `g` of input head positions that `simp` leaves, which a move of the input
head away from the boundary does: compare the positions as integers, where
`Turing.val_moveInputPos_eq` computes the move, with `omega`. -/
private def closeInputPos (g : MVarId) : M Bool := g.withContext do
  let ls ← simpLemmas #[]
  attempt do return (← evalTacticAt (← `(tactic|
    (refine Fin.ext (Int.natCast_inj.mp ?_)
     simp -failIfUnchanged only [Turing.val_moveInputPos_eq, tm_step_simps, $ls,*]
     omega))) g).isEmpty

/-- A way to split the index of a family of tapes. -/
private inductive Split where
  /-- `fin_cases x`, for `x : Fin n` with `n` a numeral. -/
  | finCases (x : FVarId)
  /-- `induction x using elim`, where case `j` binds `binders[j]` variables. -/
  | elim (x : FVarId) (elim : Name) (binders : List Nat)
  /-- `by_cases p`; when `subst` is `x`, the proposition `p` is an equation `x = a`, and `x` is
  replaced by `a` in the positive case. -/
  | cond (p : Lean.Expr) (subst : Option FVarId)
  /-- The cases of the `match` application `e`. -/
  | matcher (e : Lean.Expr)

/-- The eliminators `tm_step` uses for a function applied to the index: the function, the position
of the index among its arguments, the eliminator and the number of variables of each case. -/
private def eliminators : List (Name × Nat × Name × List Nat) :=
  [(``Fin.lastCases, 4, ``Fin.lastCases, [0, 1]), (``Fin.addCases, 5, ``Fin.addCases, [1, 1]),
    (``Fin.append, 5, ``Fin.addCases, [1, 1])]

/-- The numeral `n` of a type `Fin n`. -/
private def finLit? (ty : Lean.Expr) : Option Nat := do
  guard (ty.isAppOfArity ``Fin 1)
  (ty.getArg! 0).nat?

/-- The split the target `tgt` calls for on one of the index variables `vars`: `fin_cases` for an
index in `Fin n` with `n` a numeral, the eliminator of `Fin.lastCases`, `Fin.addCases` or
`Fin.append` applied to an index, the comparison `x = a` for `Function.update f a v x`
(`Fin.lastCases` when `a` is `Fin.last _`), the condition of an `if` that mentions an index, and
the cases of a `match` on a term that mentions an index. With `anyCond`, conditions and matched
terms need not mention an index. -/
private def findSplit (tgt : Lean.Expr) (vars hyps : Array FVarId) (anyCond := false) :
    MetaM (Option Split) := do
  let env ← getEnv
  let isVar (e : Lean.Expr) : Bool := e.isFVar && vars.contains e.fvarId!
  -- A condition is not split on again in a case that has it, or its negation, as a hypothesis.
  let known ← hyps.mapM fun h => do
    let t ← instantiateMVars (← h.getType)
    return if t.isAppOfArity ``Not 1 then t.getArg! 0 else t
  let splittable (p : Lean.Expr) : Bool :=
    (anyCond || p.hasAnyFVar vars.contains) && !p.hasLooseBVars && !known.contains p
  if hyps.isEmpty then
    for x in vars do
      if (finLit? (← whnfR (← x.getType))).isSome && tgt.containsFVar x then
        return some (.finCases x)
  for (fn, pos, elim, binders) in eliminators do
    let found := tgt.find? fun e =>
      e.isAppOf fn && e.getAppNumArgs > pos && isVar (e.getArg! pos)
    if let some e := found then return some (.elim (e.getArg! pos).fvarId! elim binders)
  let update := tgt.find? fun e =>
    e.isAppOf ``Function.update && e.getAppNumArgs ≥ 7 && isVar (e.getArg! 6) &&
      !(e.getArg! 4).hasLooseBVars && !(e.getArg! 4).containsFVar (e.getArg! 6).fvarId! &&
      !known.any fun p => p.isAppOfArity ``Eq 3 && p.getArg! 1 == e.getArg! 6 &&
        p.getArg! 2 == e.getArg! 4
  if let some e := update then
    let x := e.getArg! 6
    if (e.getArg! 4).isAppOf ``Fin.last then
      return some (.elim x.fvarId! ``Fin.lastCases [0, 1])
    return some (.cond (← mkEq x (e.getArg! 4)) (some x.fvarId!))
  let cond := tgt.find? fun e =>
    (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) && splittable (e.getArg! 1)
  if let some p := cond.map (·.getArg! 1) then
    if let some (_, lhs, rhs) := p.eq? then
      if isVar lhs && !rhs.containsFVar lhs.fvarId! then
        return some (.cond p (some lhs.fvarId!))
    return some (.cond p none)
  let matcher := tgt.find? fun e => !e.hasLooseBVars &&
    match isMatcherAppCore? env e with
    | some info =>
      let discrs := e.getAppArgs.extract info.getFirstDiscrPos
        (info.getFirstDiscrPos + info.numDiscrs)
      -- The innermost `match` is the one that is stuck.
      e.getAppNumArgs ≥ info.arity && (anyCond || discrs.any (·.hasAnyFVar vars.contains)) &&
        discrs.all fun d => (d.find? (isMatcherAppCore env)).isNone
    | none => false
  if let some e := matcher then return some (.matcher e)
  return none

/-- Apply `split` to `g`. Returns the cases, each with its index variables and case hypotheses. -/
private def applySplit (g : MVarId) (split : Split) (vars hyps : Array FVarId) :
    TacticM (List (MVarId × Array FVarId × Array FVarId)) := g.withContext do
  match split with
  | .finCases x =>
    let n ← mkFreshUserName `i
    let g ← g.rename x n
    let gs ← evalTacticAt (← `(tactic| fin_cases $(mkIdent n):ident)) g
    return gs.map fun g => (g, vars.erase x, hyps)
  | .matcher e =>
    let lctx ← getLCtx
    let gs ← Split.splitMatch g e
    gs.mapM fun g => g.withContext do
      -- The hypotheses of the case are the ones the split adds or states again.
      let mut hyps := hyps.filter (← getLCtx).contains
      for decl in ← getLCtx do
        unless decl.isImplementationDetail || lctx.contains decl.fvarId do
          if ← isProp decl.type then hyps := hyps.push decl.fvarId
      return (g, vars.filter (← getLCtx).contains, hyps)
  | .elim x elim binders =>
    let (reverted, g) ← g.revert #[x] (preserveOrder := true)
    let kept := hyps.filter fun h => !reverted.contains h
    let gs ← evalTacticAt (← `(tactic| refine $(mkCIdent elim) ?_ ?_)) g
    unless gs.length == binders.length do
      throwError "tm_step: `{elim}` left {gs.length} cases"
    (gs.zip binders).mapM fun (g, n) => do
      let (xs, g) ← g.introN n
      let (hs, g) ← g.introN (reverted.size - 1)
      return (g, (vars.erase x) ++ xs, kept ++ hs)
  | .cond p subst =>
    let h ← mkFreshUserName `h
    let (pos, neg) ← match ← observing? (synthInstance (mkApp (mkConst ``Decidable) p)) with
      | some inst => g.byCasesDec p inst h
      | none => g.byCases p h
    let neg := (neg.mvarId, vars, hyps.push neg.fvarId)
    match subst with
    | none => return [(pos.mvarId, vars, hyps.push pos.fvarId), neg]
    | some x =>
      let (fs, g) ← substCore pos.mvarId pos.fvarId
      let hyps := hyps.filterMap fun h => (fs.get h).fvarId?
      return [(g, vars.erase x, hyps), neg]

/-- Prove the equality `g`, in which `vars` are the indices introduced so far and `hyps` the
hypotheses of the cases split so far: simplify, split an index as the goal requires, and close each
case with `simp`. Returns the cases left. -/
private partial def solve (g : MVarId) (vars hyps : Array FVarId) : M (List MVarId) := do
  -- A case with an index in `Fin 0` is vacuous.
  for x in vars do
    if finLit? (← g.withContext do whnfR (← x.getType)) == some 0 then
      g.assign (← g.withContext do mkAppOptM ``Fin.elim0 #[some (← g.getType), some (mkFVar x)])
      return []
  let some g ← simpOnly g hyps | return []
  let split? ← g.withContext do findSplit (← instantiateMVars (← g.getType)) vars hyps
  match split? with
  | some split =>
    let cases ← applySplit g split vars hyps
    let n ← modifyGet fun n => (n + cases.length - 1, n + cases.length - 1)
    if n > maxCases then
      throwError "tm_step: comparing the two sides of one field takes more than {maxCases} cases \
        of its index. Prove that field apart, or give fewer definitions to unfold."
    return (← cases.mapM fun (g, vars, hyps) => solve g vars hyps).flatten
  | none =>
    if ← closeBySimp g hyps then return []
    let ty ← whnfR (← instantiateMVars (← g.getType))
    if ty.isAppOfArity ``Eq 3 && (← whnfR (ty.getArg! 0)).isAppOfArity ``Fin 1 then
      if ← closeInputPos g then return []
    -- A condition that mentions no index is split on only if that closes the goal.
    let split? ← g.withContext do
      findSplit (← instantiateMVars (← g.getType)) vars hyps (anyCond := true)
    if let some split := split? then
      let s ← (saveState : TacticM _)
      let n ← get
      let closed ← try
          let cases ← applySplit g split vars hyps
          let n ← modifyGet fun n => (n + cases.length - 1, n + cases.length - 1)
          if n > maxCases then pure false
          else pure (← cases.mapM fun (g, vars, hyps) => solve g vars hyps).flatten.isEmpty
        catch _ => pure false
      if closed then return []
      (s.restore : TacticM Unit)
      set n
    return [g]

/-- Prove the equality `g` of two values of a field: by `rfl`, or with `solve`, at each index when
the field is a family of tapes. Returns the goals left. -/
private def field (g : MVarId) : M (List MVarId) := g.withContext do
  if ← attempt do g.refl; return true then return []
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let some (ty, _, _) := tgt.eq? | return [g]
  let ty ← whnfR ty
  set 1
  if let .forallE _ d _ _ := ty then
    -- The channels of a machine without oracles are a function out of `Empty`.
    if (← whnfR d).isConstOf ``Empty then
      if let some [] ← tryTac (← `(tactic| exact Subsingleton.elim _ _)) g then return []
    let [g] ← evalTacticAt (← `(tactic| refine funext ?_)) g
      | throwError "tm_step: `funext` did not leave one goal"
    let (x, g) ← g.intro1
    solve g #[x] #[]
  else
    solve g #[] #[]

/-- Split an equality of configurations into the equalities of their fields. Returns `none` when
`g` is not an equality of configurations. -/
private partial def extConfig (g : MVarId) : TacticM (Option (List MVarId)) := g.withContext do
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let some (ty, _, _) := tgt.eq? | return none
  let ty ← whnfR ty
  if ty.isAppOf ``Turing.Cfg then
    if let some gs ← tryTac (← `(tactic| refine Turing.Cfg.ext_zero_tapes ?_ ?_ ?_)) g then
      return some gs
    tryTac (← `(tactic| refine Turing.Cfg.ext ?_ ?_ ?_ ?_ ?_)) g
  else if ty.isAppOf ``Turing.MultiTapeMachine.Config then
    let some [tapes, channels] ←
        tryTac (← `(tactic| refine Turing.MultiTapeMachine.Config.ext ?_ ?_)) g
      | return none
    if ← attempt do tapes.refl; return true then return some [channels]
    return some ((← extConfig tapes).getD [tapes] ++ [channels])
  else
    return none

/-- Rewrite the step `tm.step cfg` in `g` to the action of the transition function, when `rfl` finds
the state of `cfg`. Leaves `g` as it is otherwise, as for a halted configuration, whose step `simp`
rewrites with `Turing.MultiTapeTM.step_of_halt`. -/
private def unfoldStep (g : MVarId) : TacticM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  unless (tgt.find? (·.isAppOf ``Turing.MultiTapeTM.step)).isSome do return g
  let s ← saveState
  try
    let g' :: side ← evalTacticAt (← `(tactic| rewrite [Turing.MultiTapeTM.step_of_state])) g
      | throwError "no goal"
    -- The side goals are the state and the equation `cfg.state = some _` that determines it.
    let eqs ← side.filterM fun h => do isProp (← h.getType)
    for h in eqs do
      unless (← tryTac (← `(tactic| rfl)) h) == some [] do throwError "state not found"
    unless ← side.allM (·.isAssigned) do throwError "state not determined"
    return g'
  catch _ =>
    s.restore
    return g

/--
`tm_step` proves an equality of multi-tape configurations (`Turing.Cfg` or
`Turing.MultiTapeMachine.Config`), such as `tm.step cfg = cfg'` or `action.apply cfg = cfg'`.
`tm_step [defs, facts]` also unfolds the definitions `defs`, among them the transition table of
the machine and the builders of the two configurations, and uses the `facts`, as `simp` does.

* A step `tm.step cfg` is rewritten to the action of the transition function when the state of
  `cfg` is `some q` by `rfl`. For a halted configuration, give the hypothesis `cfg.state = none`.
* The two configurations are compared field by field. A field of work tapes or of their heads is
  compared at an index `i`, which is split as the goal requires: into the values of `Fin n` for a
  numeral `n`; with `Fin.lastCases` or `Fin.addCases` where that function, or `Fin.append`, is
  applied to `i`; into `i = j` and `i ≠ j` for `Function.update f j v i`; and on the condition of
  an `if` or the cases of a `match` that mentions `i`. Other conditions and `match`es are split
  on only when that closes the case.
* Each case is closed with `simp`, using the simp set `tm_step_simps` and the arguments, and then
  `omega`; an input head position is also compared as an integer. When a case stays open,
  `tm_step` fails and shows the cases left, each simplified with `tm_step_simps` and the
  arguments only and with the hypothesis of its case in context: the fact that closes a case
  goes among the arguments.

One field is split into at most eight cases; beyond that `tm_step` fails.

```lean
example (j : Fin k) (c : Cfg k Bool State input) (q : State) :
    (⟨0, Function.update (fun _ => (none, 0)) j (some (some true), 1), none, some q⟩ :
        Action k Bool State).apply c =
      ⟨some q, c.inputPos,
        Function.update c.workTapes j (Function.update (c.workTapes j) (c.workTapePos j) true),
        Function.update c.workTapePos j (c.workTapePos j + 1), c.output⟩ := by
  tm_step
```
-/
syntax (name := tmStep) "tm_step" (" [" (Lean.Parser.Tactic.simpStar <|>
  Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic

elab_rules : tactic
  | `(tactic| tm_step $[[$args,*]]?) => withMainContext do
    let lemmas := args.map (·.getElems.map (·.raw)) |>.getD #[]
    let run : M Unit := do
      let some g ← simpOnly (← unfoldStep (← getMainGoal)) #[] | replaceMainGoal []
      let some fields ← extConfig g
        | throwError "tm_step: the goal is not an equality of configurations{indentExpr
            (← g.getType)}"
      let left := (← fields.mapM field).flatten
      unless left.isEmpty do
        throwError "tm_step: `simp` with `tm_step_simps` and the arguments does not close \
          {if left.length == 1 then "this case" else "these cases"}:\n\n{goalsToMessageData left}"
      replaceMainGoal []
    -- A failure inside a step of the search is a failure of that step, not a logged error.
    withoutRecover <| (run.run lemmas).run' 1

end Turing.StepTactic

end
