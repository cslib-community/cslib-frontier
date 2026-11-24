/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameV

/-!
# The `tame` tactic

`tame` proves `Tm`, `TmF`, `TmF2`, `TmF3`, `TmFv`, `TmF2v`, `Pos` and `Sm` goals
by using hypotheses, applying the exact-tier lemmas, and unfolding
definitions. A loop whose count has an `Le` hypothesis passes the bound to its
counter (`Sm`), which function hypotheses of the `v` kinds can require. Numeric
side conditions are left to `omega` once they are free of metavariables. The
tactic stops at `pow2`, `powT` and folds that are not plain sums.
-/

public meta section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term Lean Meta Elab Lean.Elab.Tactic

/-- Prove `Ext L a b` by a chain of local `Ext` hypotheses. -/
partial def extProof (L a b : Expr) (fuel : ℕ) : MetaM (Option Expr) := do
  if ← withReducible (isDefEq a b) then
    return some (← mkAppOptM ``Ext.refl #[some L, some b])
  if fuel == 0 then return none
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if ty.isAppOfArity ``Ext 3 then
      if ← withReducible (isDefEq (ty.getArg! 1) a) then
        if let some rest ← extProof L (ty.getArg! 2) b (fuel - 1) then
          return some (← mkAppM ``Ext.trans #[decl.toExpr, rest])
  return none

/-- Prove an `Ext` goal by a chain of local `Ext` hypotheses. -/
elab (name := tameExt) "tame_ext" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``Ext 3 do throwError "tame_ext: not an extension goal"
  let some pf ← extProof (ty.getArg! 0) (ty.getArg! 1) (ty.getArg! 2) 32
    | throwError "tame_ext: no chain"
  g.assign pf
  replaceMainGoal []

/-- Heads handled by a lemma. -/
def tameLemmas : List (Name × Name) :=
  [(``Term.add, ``t_add), (``Term.mul, ``t_mul), (``Term.sub, ``t_sub), (``Term.div, ``t_div),
   (``Term.bit, ``t_bit), (``Term.lt, ``t_lt), (``Term.input, ``t_input), (``Term.ite, ``t_ite),
   (``foldModT, ``t_foldModT), (``Term.letT, ``t_letT), (``Term.const, ``t_const),
       (``divPowT, ``t_divPowT)]

/-- Loops, with their counter-bounded versions. -/
def tameLoops : List (Name × Name × Name) :=
  [(``Term.sumMod, ``t_sumMod, ``t_sumModv), (``Term.prodMod, ``t_prodMod, ``t_prodModv),
   (``sumT, ``t_sumT, ``t_sumTv')]

/-- Heads at which `tame` stops. -/
def tameStops : List Name := [``Term.pow2, ``powT, ``Term.lvl]

/-- Try `tac`, restoring the state on failure. -/
def tryTac (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try tac; return true
  catch _ => s.restore; return false

/-- Apply a constant to the main goal. -/
def applyConst (n : Name) : TacticM Unit := do
  let g ← getMainGoal
  let e ← mkConstWithFreshMVarLevels n
  let gs ← g.apply e
  replaceMainGoal gs

/-- Use hypothesis `h` with lemma `lem` (`lem h he ...` with `k` further explicit
arguments), and close the `Ext` goal. -/
def useHyp (lem : Name) (h : Expr) (k : ℕ := 0) : TacticM Unit := Term.withoutErrToSorry do
  let hs ← Term.exprToSyntax h
  let ls := mkIdent lem
  match k with
  | 0 => evalTactic (← `(tactic| refine $ls $hs ?_))
  | 1 => evalTactic (← `(tactic| refine $ls $hs ?_ ?_))
  | 2 => evalTactic (← `(tactic| refine $ls $hs ?_ ?_ ?_))
  | 3 => evalTactic (← `(tactic| refine $ls $hs ?_ ?_ ?_ ?_))
  | 4 => evalTactic (← `(tactic| refine $ls $hs ?_ ?_ ?_ ?_ ?_))
  | 5 => evalTactic (← `(tactic| refine $ls $hs ?_ ?_ ?_ ?_ ?_ ?_))
  | _ => evalTactic (← `(tactic| refine $ls $hs ?_ ?_ ?_ ?_ ?_ ?_ ?_))
  match ← getGoals with
  | ge :: rest =>
    setGoals [ge]
    evalTactic (← `(tactic| tame_ext))
    unless (← getUnsolvedGoals).isEmpty do throwError "tame: extension"
    setGoals rest
  | [] => pure ()

/-- Does `f` applied to `k` fresh arguments match `t`? -/
def fnMatches (f t : Expr) (k : ℕ) : MetaM Bool := do
  let s0 ← saveState
  try
    let xs ← (List.range k).mapM fun _ => mkFreshExprMVar (some (mkConst ``Term))
    let ok ← withReducible (isDefEq (mkAppN f xs.toArray).headBeta t)
    s0.restore
    pure ok
  catch _ =>
    s0.restore
    pure false

/-- Syntactic match of two terms, never failing. -/
def sameTerm (a b : Expr) : MetaM Bool := do
  let s0 ← saveState
  try
    let ok ← withReducible (isDefEq a b)
    unless ok do s0.restore
    pure ok
  catch _ =>
    s0.restore
    pure false

/-- A local `Le n V` hypothesis for the loop count `n`. -/
def findLe (n : Expr) : MetaM (Option Expr) := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let dty ← instantiateMVars decl.type
    if dty.isAppOfArity ``Le 5 then
      if ← sameTerm (dty.getArg! 2) n then return some decl.toExpr
  return none

/-- One step of `tame`: close a tier goal by a hypothesis or reduce it by one tier rule. -/
syntax (name := tameStep) "tame_step" : tactic

elab_rules : tactic
  | `(tactic| tame_step) => do
  let g ← getMainGoal
  g.withContext do
  let ty0 ← instantiateMVars (← g.getType)
  let ty := (← Core.betaReduce ty0).cleanupAnnotations
  if ty != ty0 then
    replaceMainGoal [← g.replaceTargetDefEq ty]
  let g ← getMainGoal
  g.withContext do
  -- binders
  if ty.isAppOfArity ``TmF 6 || ty.isAppOfArity ``TmF2 7 || ty.isAppOfArity ``TmF3 8 then
    evalTactic (← `(tactic| intro _ _))
    let k := if ty.isAppOfArity ``TmF 6 then 1 else if ty.isAppOfArity ``TmF2 7 then 2 else 3
    for _ in [0:k] do evalTactic (← `(tactic| intro _))
    for _ in [0:k] do evalTactic (← `(tactic| intro _))
    return
  if ty.isAppOfArity ``TmFv 7 then
    evalTactic (← `(tactic| intro _ _ _ _ _ _))
    return
  if ty.isAppOfArity ``TmF2v 8 then
    evalTactic (← `(tactic| intro _ _ _ _ _ _ _ _ _))
    return
  if ty.isAppOfArity ``TmB 8 then
    evalTactic (← `(tactic| intro _ _ _ _ _ _ _ _))
    return
  -- stability
  if ty.isAppOfArity ``StableAt 3 then
    let t := ty.getArg! 1
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let dty ← instantiateMVars decl.type
      if dty.isAppOfArity ``StableAt 3 then
        if ← sameTerm (dty.getArg! 1) t then
          -- the scale `L` from any extension hypothesis
          let mut Lopt : Option Expr := none
          for d2 in ← getLCtx do
            let t2 ← instantiateMVars d2.type
            if t2.isAppOfArity ``Ext 3 then Lopt := some (t2.getArg! 0)
          if let some Le := Lopt then
            if let some pf ← extProof Le (ty.getArg! 2) (dty.getArg! 2) 32 then
              g.assign (← mkAppM ``StableAt.extend' #[decl.toExpr, pf])
              replaceMainGoal []
              return
          if ← withReducible (isDefEq (dty.getArg! 2) (ty.getArg! 2)) then
            g.assign decl.toExpr
            replaceMainGoal []
            return
    let some c := t.getAppFn.constName? | throwError "tame: no stability"
    let lem? : Option Name :=
      if c == ``Term.add then some ``StableAt.add else if c == ``Term.sub then some ``StableAt.sub
      else if c == ``Term.mul then some ``StableAt.mul else if c ==
          ``Term.div then some ``StableAt.div
      else if c == ``Term.mod then some ``StableAt.mod else if c ==
          ``Term.lt then some ``StableAt.lt
      else if c == ``Term.bit then some ``StableAt.bit else if c ==
          ``Term.ite then some ``StableAt.ite
      else if c == ``Term.const then some ``stableAt_const else none
    match lem? with
    | some lem => applyConst lem; return
    | none =>
      let some t' ← unfoldDefinition? t | throwError "tame: no stability"
      let ty' := mkAppN ty.getAppFn #[ty.getArg! 0, t'.headBeta, ty.getArg! 2]
      replaceMainGoal [← g.replaceTargetDefEq ty']
      return
  -- counter bounds
  if ty.isAppOfArity ``Sm 5 then
    let t := ty.getArg! 2
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let dty ← instantiateMVars decl.type
      if dty.isAppOfArity ``Sm 5 then
        if ← sameTerm (dty.getArg! 2) t then
          if ← tryTac (useHyp ``Sm.ext decl.toExpr) then return
          if ← tryTac (do
              let g ← getMainGoal
              let e ← mkConstWithFreshMVarLevels ``Sm.mono
              replaceMainGoal (← g.apply e)
              -- goals: the weaker `Sm`, then the inequality
              let gs ← getGoals
              match gs with
              | g1 :: rest =>
                setGoals [g1]
                useHyp ``Sm.ext decl.toExpr
                unless (← getUnsolvedGoals).isEmpty do throwError "tame: bound"
                setGoals rest
                for g2 in rest do
                  setGoals [g2]
                  if ← isProp (← g2.getType) then evalTactic (← `(tactic| omega))
                setGoals []
              | [] => pure ()) then return
    throwError "tame: no counter bound"
  -- positivity
  if ty.isAppOfArity ``Pos 4 then
    let b := ty.getArg! 2
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let dty ← instantiateMVars decl.type
      if dty.isAppOfArity ``Pos 4 then
        if ← sameTerm (dty.getArg! 2) b then
          if ← tryTac (useHyp ``Pos.ext decl.toExpr) then return
    let some c := b.getAppFn.constName? | throwError "tame: no positivity hypothesis"
    let lems : List Name :=
      if c == ``Term.const then [``Pos.const']
      else if c == ``Term.mul then [``Pos.mul']
      else if c == ``Term.add then [``Pos.add_right', ``Pos.add_left']
      else if c == ``Term.pow2 then [``Pos.pow2'] else []
    for lem in lems do
      if ← tryTac (do
          applyConst lem
          let gs ← getGoals
          for g' in gs do
            setGoals [g']
            let ty' ← instantiateMVars (← g'.getType)
            if ty'.isAppOfArity ``Pos 4 then evalTactic (← `(tactic| tame_step))
            else evalTactic (← `(tactic| omega))
            unless (← getUnsolvedGoals).isEmpty do throwError "tame: positivity"
          setGoals []) then return
    throwError "tame: no positivity hypothesis"
  unless ty.isAppOfArity ``Tm 5 do throwError "tame: not a tier goal"
  let d ← instantiateMVars (ty.getArg! 2)
  let t := ty.getArg! 3
  -- hypotheses about this exact term
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let dty ← instantiateMVars decl.type
    if dty.isAppOfArity ``Tm 5 then
      if ← sameTerm (dty.getArg! 3) t then
        if ← tryTac (do
            if !d.isMVar then applyConst ``Tm.mono
            useHyp ``Tm.ext decl.toExpr) then return
  -- hypotheses about a term function applied to arguments
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let dty ← instantiateMVars decl.type
    let (lem, k, extra) :=
      if dty.isAppOfArity ``TmF 6 then (``TmF.app, 1, 1)
      else if dty.isAppOfArity ``TmF2 7 then (``TmF2.app, 2, 2)
      else if dty.isAppOfArity ``TmF3 8 then (``TmF3.app, 3, 3)
      else if dty.isAppOfArity ``TmFv 7 then (``TmFv.app, 1, 3)
      else if dty.isAppOfArity ``TmF2v 8 then (``TmF2v.app, 2, 5)
      else (Name.anonymous, 0, 0)
    if k == 0 then continue
    if ← fnMatches (dty.getArg! 2) t k then
      if ← tryTac (do
          if !d.isMVar then applyConst ``Tm.mono
          useHyp lem decl.toExpr extra) then return
  let some c := t.getAppFn.constName? | throwError "tame: unknown term {t}"
  if c == ``Term.foldT then
    if !d.isMVar then applyConst ``Tm.mono
    if ← tryTac (applyConst ``t_sumT) then return
    applyConst ``t_foldT_closed
    return
  if tameStops.contains c then throwError "tame: stop at {c}"
  if c == ``Term.mod then
    if !d.isMVar then applyConst ``Tm.mono
    let s ← saveState
    try
      applyConst ``t_mod
      let gs ← getGoals
      let mut rest : List MVarId := []
      for g' in gs do
        if (← instantiateMVars (← g'.getType)).isAppOfArity ``Pos 4 then
          setGoals [g']
          evalTactic (← `(tactic| tame_step))
          unless (← getUnsolvedGoals).isEmpty do throwError "tame: positivity"
        else rest := rest ++ [g']
      setGoals rest
      return
    catch _ => s.restore
    applyConst ``t_mod_left
    return
  match tameLoops.find? (·.1 == c) with
  | some (_, plain, bounded) =>
    if !d.isMVar then applyConst ``Tm.mono
    -- the count is the second-to-last argument of `sumMod`/`prodMod`, the first of `sumT`
    let n := if c == ``sumT then t.getArg! 0 else t.getArg! 1
    match ← findLe n with
    | some hle =>
      let s1 ← saveState
      try
        applyConst bounded
        let gs ← getGoals
        let mut rest : List MVarId := []
        let mut done := false
        for g' in gs do
          if !done && (← instantiateMVars (← g'.getType)).isAppOfArity ``Le 5 then
            setGoals [g']
            useHyp ``Le.ext hle
            unless (← getUnsolvedGoals).isEmpty do throwError "tame: count bound"
            done := true
          else rest := rest ++ [g']
        unless done do throwError "tame: count bound"
        setGoals rest
      catch _ =>
        s1.restore
        applyConst plain
    | none =>
      let s1 ← saveState
      try
        applyConst bounded
        let gs ← getGoals
        let mut rest : List MVarId := []
        for g' in gs do
          if (← instantiateMVars (← g'.getType)).isAppOfArity ``Le 5 then
            setGoals [g']
            applyConst ``Le.of_tm
            rest := rest ++ (← getGoals)
          else rest := rest ++ [g']
        setGoals rest
      catch _ =>
        s1.restore
        applyConst plain
    return
  | none => pure ()
  match tameLemmas.lookup c with
  | some lem =>
    if !d.isMVar then applyConst ``Tm.mono
    applyConst lem
  | none =>
    let some t' ← unfoldDefinition? t | throwError "tame: cannot unfold {c}"
    let ty' := mkAppN ty.getAppFn #[ty.getArg! 0, ty.getArg! 1, d, t'.headBeta, ty.getArg! 4]
    replaceMainGoal [← g.replaceTargetDefEq ty']

/-- Numeric side conditions, only once they are free of metavariables. -/
elab (name := tameNum) "tame_num" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if ty.hasMVar then throwError "tame_num: metavariables"
  unless ← isProp ty do throwError "tame_num: not a proposition"
  evalTactic (← `(tactic| first
    | omega
    | assumption
    | exact lit_lt_two_pow (by omega) (by omega)
    | exact lit_lt_two_pow_big (by omega) (by omega)))

/-- Prove a tier goal as far as the combinators allow. -/
macro "tame" : tactic => `(tactic| (
  (repeat' tame_step) <;> try tame_num
  all_goals ((repeat' tame_step) <;> try tame_num)
  all_goals ((repeat' tame_step) <;> try tame_num)))

end Cslib.Complexity.NtimeDspace.ProgTerm

namespace Cslib.Complexity.NtimeDspace.ProgTerm
open Lean Meta Elab Lean.Elab.Tactic

/-- Report why `tame_step` fails on each remaining tier goal. -/
elab (name := tameWhy) "tame_why" : tactic => do
  let gs ← getGoals
  for g in gs do
    let ty ← instantiateMVars (← g.getType)
    if ty.isAppOfArity ``Tm 5 then
      let s ← saveState
      setGoals [g]
      try evalTactic (← `(tactic| tame_step))
      catch e => logInfo m!"tame_why: {e.toMessageData}\n  on {ty.getArg! 3}"
      s.restore
  setGoals gs

end Cslib.Complexity.NtimeDspace.ProgTerm
