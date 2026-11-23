/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Tactic.ValidProg.Init
public meta import Lean.Elab.Tactic.Omega

/-!
# Automation tactics for monadic `Memory.Prog` programs

Provides structural tactics over the `Memory.Prog` (`PFunctor.FreeM`) free monad:

* `valid_prog`: decomposes memory-history admissibility goals — either raw
  `(Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)` or wrapper predicates
  (such as `ValidProg w F s p`) with registered `pure`/`bind`/`ite` combinators — across `pure`,
  `bind`, `Memory.read`/`write`/`alloc`/`allocDirty`, `ite`/`dite`, `iterate`, and `boundedWhile`.
  Applies explicit and `@[valid_prog]` lemmas without unfolding opaque subprograms, propagates
  `MonotoneMemInv` invariants across state updates, rewrites intermediate
  `clientState`/`clientResult` terms using `with [...]`, and leaves only genuine arithmetic or
  domain obligations.
* `prog_cost`: evaluates and bounds `memoryCost p s` across monadic binds and conditionals.

## Main definitions

* `valid_prog`: admissibility walker tactic.
* `prog_cost`: `memoryCost` evaluator/bound tactic.
-/

public meta section

namespace Cslib.Tactic.ValidProg

open Lean Meta Elab Tactic
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- Unwrap `Bind.bind`, `PFunctor.FreeM.bind`, and `PFunctor.FreeM.liftBind` heads. -/
private def splitBind? (p : Expr) : MetaM (Option (Expr × Expr)) := do
  let p := p.consumeMData
  if p.isAppOfArity ``Bind.bind 6 then
    return some (p.getArg! 4, p.getArg! 5)
  if p.isAppOfArity ``PFunctor.FreeM.bind 5 then
    return some (p.getArg! 3, p.getArg! 4)
  if p.isAppOfArity ``PFunctor.FreeM.liftBind 4 then
    let m ← mkAppOptM ``PFunctor.FreeM.lift #[p.getArg! 0, p.getArg! 2]
    return some (m, p.getArg! 3)
  return none

/-- Recognize `Pure.pure a` or `PFunctor.FreeM.pure a`. -/
private def splitPure? (p : Expr) : Option Expr :=
  let p := p.consumeMData
  if p.isAppOfArity ``Pure.pure 4 then some p.appArg!
  else if p.isAppOfArity ``PFunctor.FreeM.pure 3 then some p.appArg!
  else none

/-- Recognize a primitive memory operation (`Memory.read`, `write`, `alloc`, `allocDirty`, or
`PFunctor.FreeM.lift` of `Memory.Op.*`). -/
private inductive MemPrimOp where
  | read (addr : Expr)
  | write (addr val : Expr)
  | alloc (count : Expr)
  | allocDirty (count : Expr)

private def matchMemPrimOp? (e : Expr) : MetaM (Option MemPrimOp) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Memory.read 1 then return some (.read e.appArg!)
  if e.isAppOfArity ``Memory.write 2 then return some (.write (e.getArg! 0) (e.getArg! 1))
  if e.isAppOfArity ``Memory.alloc 1 then return some (.alloc e.appArg!)
  if e.isAppOfArity ``Memory.allocDirty 1 then return some (.allocDirty e.appArg!)
  if e.isAppOfArity ``PFunctor.FreeM.lift 2 then
    let op ← whnfR e.appArg!
    if op.isAppOfArity ``Memory.Op.read 1 then return some (.read op.appArg!)
    if op.isAppOfArity ``Memory.Op.write 2 then
      return some (.write (op.getArg! 0) (op.getArg! 1))
    if op.isAppOfArity ``Memory.Op.alloc 1 then return some (.alloc op.appArg!)
    if op.isAppOfArity ``Memory.Op.allocDirty 1 then return some (.allocDirty op.appArg!)
  return none

/-- Recognize a `Memory.Prog` type (`PFunctor.FreeM _ _`). -/
private def isMemoryProgType (ty : Expr) : MetaM Bool := do
  let ty ← whnfR (← instantiateMVars ty)
  return ty.isAppOfArity ``PFunctor.FreeM 2

/-- Head constant name of an expression (peeling metadata). -/
private def headProgConst? (e : Expr) : Option Name :=
  e.consumeMData.getAppFn.constName?

/-- Fast head analysis of a goal target: either raw `ValidHistory` or a custom wrapper predicate
whose last `Memory.Prog` argument is extracted. -/
private inductive GoalShape where
  | validHistory (w α s prog : Expr)
  | wrapper (predName : Name) (prog : Expr)

/-- Extract the `Memory.Prog` client from a `ValidHistory` or wrapper predicate goal. -/
private def classifyGoal (target : Expr) : MetaM (Option GoalShape) := do
  let t ← instantiateMVars target.consumeMData
  if t.isAppOf ``StateTransitionSpec.ValidHistory then
    let args := t.getAppArgs
    if args.size ≥ 5 then
      let hist := args[args.size - 1]!.consumeMData
      if hist.isAppOf ``StateTransitionSpec.clientHistory then
        let hargs := hist.getAppArgs
        if hargs.size ≥ 6 then
          let spec := args[0]!.consumeMData
          let w? := if spec.isAppOf ``Memory.spec && spec.getAppNumArgs ≥ 1 then
            some (spec.getArg! 0)
          else none
          let w ← match w? with
            | some w => pure w
            | none => do
              let specR ← whnfR spec
              if specR.isAppOf ``Memory.spec then pure (specR.getArg! 0)
              else return none
          let α := hargs[hargs.size - 3]!
          let s := args[args.size - 2]!
          let p := hargs[hargs.size - 1]!
          return some (.validHistory w α s p)
    return none
  let some predName := t.getAppFn.constName? | return none
  let args := t.getAppArgs
  if args.isEmpty then return none
  let last := args[args.size - 1]!
  if ← isMemoryProgType (← inferType last) then
    return some (.wrapper predName last)
  return none

/-- Rebuild a `ValidHistory` expression from an existing template `t` with updated answer type
`α'`, state `s'`, and program `p'` in O(1) without typeclass synthesis. -/
private def rebuildValidHistory (t α' s' p' : Expr) : Expr :=
  let tArgs := t.consumeMData.getAppArgs
  let hist := tArgs[tArgs.size - 1]!.consumeMData
  let hArgs := hist.getAppArgs
  let hArgs' := ((hArgs.set! (hArgs.size - 3) α').set! (hArgs.size - 2) s').set!
    (hArgs.size - 1) p'
  let hist' := mkAppN hist.getAppFn hArgs'
  mkAppN t.consumeMData.getAppFn ((tArgs.set! (tArgs.size - 2) s').set! (tArgs.size - 1) hist')

/-- Classify a candidate rule's conclusion shape without instantiating heavy terms. -/
private def ruleConclusionShape (ruleExpr : Expr) :
    MetaM (Option (Option Name × Option Name)) := do
  let ty ← instantiateMVars (← inferType ruleExpr)
  forallTelescope ty fun _ body => do
    match ← classifyGoal body with
    | some (.validHistory _ _ _ p) => return some (none, headProgConst? p)
    | some (.wrapper pn p) => return some (some pn, headProgConst? p)
    | none => return none

/-- A pre-indexed admissibility rule or hint term. -/
private structure RuleEntry where
  expr : Expr
  predName? : Option Name
  progHead? : Option Name
  isGlobal : Bool

/-- Partition a user/attribute list into indexed `ValidProg`/`ValidHistory` rules vs hint terms. -/
private def indexRules (rules : Array (Expr × Bool)) : MetaM (Array RuleEntry × Array Expr) := do
  let mut validRules : Array RuleEntry := #[]
  let mut hints : Array Expr := #[]
  for (e, isGlobal) in rules do
    if let some (pn?, ph?) ← ruleConclusionShape e then
      validRules := validRules.push { expr := e, predName? := pn?, progHead? := ph?, isGlobal }
    else
      hints := hints.push e
  return (validRules, hints)

/-- Cached `MonotoneMemInv w inv` synthesis table for one tactic invocation. -/
private abbrev InvCache := IO.Ref (Array (Expr × Option Expr))

private def lookupMonotoneMemInv? (cache : InvCache) (w inv : Expr) : MetaM (Option Expr) := do
  let entries ← cache.get
  for (k, v) in entries do
    if k == inv then return v
  let saved ← saveState
  let res ← try
    synthInstance? (← mkAppM ``MonotoneMemInv #[w, inv])
  catch _ =>
    saved.restore
    pure none
  if res.isNone then saved.restore
  cache.modify fun arr => arr.push (inv, res)
  return res

/-- Light-weight side-goal closer: never diverges or unfolds opaque programs. -/
private partial def tryCloseLeaf (g : MVarId) (hints : Array Expr) (depth : Nat := 2) :
    MetaM Bool := do
  if ← g.isAssigned then return true
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    if tgt.isConstOf ``True then
      g.assign (mkConst ``True.intro)
      return true
    if let some (_, lhs, rhs) := tgt.eq? then
      let s ← saveState
      if ← withReducible (isDefEq lhs rhs) then
        g.assign (← mkEqRefl lhs)
        return true
      s.restore
    let tgtHead? := tgt.getAppFn.constName?
    let revDecls := (← getLCtx).decls.toArray.reverse
    let s ← saveState
    for d? in revDecls do
      let some decl := d? | continue
      if decl.isImplementationDetail || decl.isLet then continue
      let declTy := decl.type
      let headMatch := match tgtHead?, declTy.getAppFn.constName? with
        | some a, some b => a == b
        | _, _ => true
      if headMatch then
        if ← withReducible (isDefEq declTy tgt) then
          g.assign decl.toExpr
          return true
      if tgt.isAppOfArity ``LE.le 4 && (tgt.getArg! 0).isConstOf ``Nat then
        let declTy ← instantiateMVars decl.type
        if declTy.isAppOfArity ``LT.lt 4 && (declTy.getArg! 0).isConstOf ``Nat then
          if ← withReducible (isDefEq (declTy.getArg! 2) (tgt.getArg! 2)) then
            if ← withReducible (isDefEq (declTy.getArg! 3) (tgt.getArg! 3)) then
              g.assign (← mkAppM ``Nat.le_of_lt #[decl.toExpr])
              return true
    s.restore
    if depth > 0 then
      for d? in revDecls do
        let some decl := d? | continue
        if decl.isImplementationDetail then continue
        let ty ← instantiateMVars decl.type
        if ty.isArrow then
          let bodyHead? := ty.bindingBody!.getAppFn.constName?
          if tgtHead?.isSome && bodyHead?.isSome && tgtHead? != bodyHead? then continue
          let s1 ← saveState
          try
            let sub ← withReducible (g.apply decl.toExpr)
            let ok ← sub.allM fun sg => tryCloseLeaf sg hints (depth - 1)
            if ok then return true
            s1.restore
          catch _ => s1.restore
    for h in hints do
      let s1 ← saveState
      try
        let sub ← withReducible (g.apply h)
        if sub.isEmpty then return true
        if depth > 0 then
          let ok ← sub.allM fun sg => tryCloseLeaf sg hints (depth - 1)
          if ok then return true
        s1.restore
      catch _ => s1.restore
    -- Handle `<` whose LHS/RHS reduce via `whnfR` (e.g. tuple projections `(x, 0).2 < 2` that still
    -- syntactically contain FVars before projection reduction).
    if tgt.isAppOfArity ``LT.lt 4 && (tgt.getArg! 0).isConstOf ``Nat then
      if let some a := (← whnfR (tgt.getArg! 2)).nat? then
        if let some b := (← whnfR (tgt.getArg! 3)).nat? then
          if a < b then
            let s1 ← saveState
            try
              let inst ← synthInstance (← mkAppM ``Decidable #[tgt])
              let pf ← mkAppOptM ``of_decide_eq_true #[tgt, inst, ← mkEqRefl (mkConst ``Bool.true)]
              if ← isTypeCorrect pf then
                g.assign pf
                return true
              s1.restore
            catch _ => s1.restore
    if !tgt.hasFVar && !tgt.hasMVar then
      let s1 ← saveState
      try
        let inst ← synthInstance (← mkAppM ``Decidable #[tgt])
        let pf ← mkAppOptM ``of_decide_eq_true #[tgt, inst, ← mkEqRefl (mkConst ``Bool.true)]
        if ← isTypeCorrect pf then
          g.assign pf
          return true
        s1.restore
      catch _ => s1.restore
    if tgt.isAppOfArity ``LE.le 4 && (tgt.getArg! 0).isConstOf ``Nat then
      if let some 0 := (← whnfR (tgt.getArg! 2)).nat? then
        g.assign (← mkExpectedTypeHint
          (mkApp (mkConst ``Nat.zero_le) (tgt.getArg! 3)) tgt)
        return true
    if tgt.isAppOfArity ``LT.lt 4 && (tgt.getArg! 0).isConstOf ``Nat then
      if let some 2 := (← whnfR (tgt.getArg! 3)).nat? then
        let lhs := tgt.getArg! 2
        for d? in revDecls do
          let some decl := d? | continue
          if decl.isImplementationDetail then continue
          let declTy ← instantiateMVars decl.type
          if declTy.isAppOfArity ``LE.le 4 && (declTy.getArg! 0).isConstOf ``Nat then
            if let some 1 := (declTy.getArg! 3).nat? then
              if ← withReducible (isDefEq (declTy.getArg! 2) lhs) then
                g.assign (← mkAppM ``Nat.lt_succ_of_le #[decl.toExpr])
                return true
        for h in hints do
          let s1 ← saveState
          try
            let sub ← g.apply (mkConst ``Nat.lt_succ_of_le)
            if let [gLe] := sub then
              let sub2 ← withReducible (gLe.apply h)
              if sub2.isEmpty then return true
            s1.restore
          catch _ => s1.restore
    return false

/-- Try applying a concrete rewrite theorem `rwExpr` once in `g`'s target, discharging any simple
side conditions with `tryCloseLeaf`. -/
private def tryRewriteTargetWith (g : MVarId) (rwExpr : Expr) (hints : Array Expr) :
    MetaM (Option MVarId) := g.withContext do
  let saved ← saveState
  try
    let rwTy ← instantiateMVars (← inferType rwExpr)
    let (mvars, _, concl) ← forallMetaTelescopeReducing rwTy
    let eqPf := mkAppN rwExpr mvars
    let some (_, lhs, _) := concl.eq? | do saved.restore; return none
    if lhs.getAppFn.isMVar then saved.restore; return none
    let target ← instantiateMVars (← g.getType)
    if let some lhsHead := lhs.getAppFn.constName? then
      if !target.containsConst (· == lhsHead) then
        saved.restore
        return none
      if lhsHead == ``StateTransitionSpec.clientState ||
          lhsHead == ``StateTransitionSpec.clientResult then
        let lhsArgs := lhs.getAppArgs
        if !lhsArgs.isEmpty then
          if let some progHead := lhsArgs.back!.consumeMData.getAppFn.constName? then
            if !target.containsConst (· == progHead) then
              saved.restore
              return none
    let res ← g.rewrite target eqPf (symm := false)
    let g' ← g.replaceTargetEq res.eNew res.eqProof
    let mut ok := true
    for mv in mvars do
      let id := mv.mvarId!
      if !(← id.isAssigned) then
        if !(← isProp (← id.getType)) || !(← tryCloseLeaf id hints 2) then
          ok := false
          break
    if !ok then
      saved.restore
      return none
    for sg in res.mvarIds do
      if !(← sg.isAssigned) then
        if !(← tryCloseLeaf sg hints 1) then
          saved.restore
          return none
    return some g'
  catch _ =>
    saved.restore
    return none

/-- Rewrite the target of `g` repeatedly with the given `clientState`/`clientResult` lemmas. -/
private def applyProgRewrites (g : MVarId) (rwExprs : Array Expr) (hints : Array Expr) :
    MetaM MVarId := do
  if rwExprs.isEmpty then return g
  let mut cur := g
  for _ in [0:4] do
    let mut changed := false
    for rw in rwExprs do
      if let some next ← tryRewriteTargetWith cur rw hints then
        cur := next
        changed := true
    if !changed then break
  return cur

/-- Instantiate universe levels for a constant and return an `Expr`. -/
private def mkConstFresh (n : Name) : MetaM Expr :=
  mkConstWithFreshMVarLevels n

/-- Compare two `Memory.State` expressions without unfolding `StateTransitionSpec.clientState`
(an `abbrev` for `runClient` that would symbolically execute nested programs on mismatch). -/
private def sameStateExpr (a b : Expr) : MetaM Bool := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return true
  if a.isAppOf ``StateTransitionSpec.clientState ||
      b.isAppOf ``StateTransitionSpec.clientState then
    return false
  withReducible (isDefEq a b)

/-- Add inferred `MonotoneMemInv` facts about `nextState` into `gRight`'s local context whenever
`s` holds the corresponding invariant in the parent context, clearing stale intermediate hypotheses
when `s` is not a local variable. -/
private def propagateMemInvs (cache : InvCache) (gRight : MVarId) (w s m nextState : Expr)
    (hpProof : Expr) : MetaM MVarId := gRight.withContext do
  if ← sameStateExpr s nextState then return gRight
  let dropOld := !s.isFVar
  let mut cur := gRight
  let decls ← cur.withContext do return (← getLCtx).decls.toArray
  for d? in decls do
    let some decl := d? | continue
    if decl.isImplementationDetail || decl.isLet then continue
    let ty ← instantiateMVars decl.type
    -- `Memory.WellFormed w s`
    if ty.isAppOfArity ``Memory.WellFormed 2 then
      if ← sameStateExpr (ty.getArg! 1) s then
        if (ty.getArg! 0 == w) || (← withReducible (isDefEq (ty.getArg! 0) w)) then
          let ok ← saveState
          try
            let pf := mkAppN (mkConst ``wellFormed_clientState [])
              #[← inferType m >>= fun t => pure (t.appArg!), w, s, decl.toExpr, m, hpProof]
            let newTy := mkApp2 (mkConst ``Memory.WellFormed []) w nextState
            let pf ← mkExpectedTypeHint pf newTy
            let (_, nextG) ← (← cur.assert decl.userName newTy pf).intro1P
            cur ← if dropOld then nextG.tryClear decl.fvarId else pure nextG
          catch _ => ok.restore
    -- `F ≤ s.frontier`
    else if ty.isAppOfArity ``LE.le 4 && (ty.getArg! 0).isConstOf ``Nat then
      let rhs := ty.getArg! 3
      if rhs.isAppOfArity ``Memory.State.frontier 1 then
        if ← sameStateExpr rhs.appArg! s then
          let ok ← saveState
          try
            let lhs := ty.getArg! 2
            let step ← mkAppOptM ``Memory.frontier_le_clientState #[mkNatLit 0, none, s, m]
            let pf ← mkAppM ``le_trans #[decl.toExpr, step]
            let newTy ← mkAppM ``LE.le #[lhs, mkApp (mkConst ``Memory.State.frontier []) nextState]
            if ← withReducible (isDefEq (← inferType pf) newTy) then
              let (_, nextG) ← (← cur.assert decl.userName newTy pf).intro1P
              cur ← if dropOld then nextG.tryClear decl.fvarId else pure nextG
            else ok.restore
          catch _ => ok.restore
    -- `F < s.frontier`
    else if ty.isAppOfArity ``LT.lt 4 && (ty.getArg! 0).isConstOf ``Nat then
      let rhs := ty.getArg! 3
      if rhs.isAppOfArity ``Memory.State.frontier 1 then
        if ← sameStateExpr rhs.appArg! s then
          let ok ← saveState
          try
            let lhs := ty.getArg! 2
            let step ← mkAppOptM ``Memory.frontier_le_clientState #[mkNatLit 0, none, s, m]
            let pf ← mkAppM ``lt_of_lt_of_le #[decl.toExpr, step]
            let newTy ← mkAppM ``LT.lt #[lhs, mkApp (mkConst ``Memory.State.frontier []) nextState]
            if ← withReducible (isDefEq (← inferType pf) newTy) then
              let (_, nextG) ← (← cur.assert decl.userName newTy pf).intro1P
              cur ← if dropOld then nextG.tryClear decl.fvarId else pure nextG
            else ok.restore
          catch _ => ok.restore
    -- Arbitrary `Inv s` with a cached `MonotoneMemInv w Inv` instance.
    else if ty.isApp && !ty.isAppOf ``Eq && !ty.isAppOf ``Not && !ty.isAppOf ``And &&
        !ty.isAppOf ``LT.lt && !ty.isAppOf ``LE.le &&
        !ty.isAppOf ``StateTransitionSpec.ValidHistory then
      let arg := ty.appArg!
      let sameArg ←
        if arg.consumeMData == s.consumeMData then pure true
        else if (← inferType arg).isConstOf ``Memory.State then
          sameStateExpr arg s
        else pure false
      if sameArg then
        let inv := ty.appFn!
        if let some inst ← lookupMonotoneMemInv? cache w inv then
          let ok ← saveState
          try
            let pf ← mkAppOptM ``MonotoneMemInv.pres
              #[w, inv, inst, none, s, m, decl.toExpr, hpProof]
            let newTy := mkApp inv nextState
            let pf ← mkExpectedTypeHint pf newTy
            let (_, nextG) ← (← cur.assert decl.userName newTy pf).intro1P
            cur ← if dropOld then nextG.tryClear decl.fvarId else pure nextG
          catch _ => ok.restore
  return cur

/-- Find an explicit `Inv s` hypothesis in `g`'s context with a `MonotoneMemInv w Inv` instance. -/
private def findMonotoneMemInv? (cache : InvCache) (g : MVarId) (w s : Expr) :
    MetaM (Option (Expr × Expr × Expr)) :=
  g.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail || decl.isLet then continue
      let ty ← instantiateMVars decl.type
      if ty.isApp && !ty.isAppOf ``Eq && !ty.isAppOf ``Not && !ty.isAppOf ``And &&
          !ty.isAppOf ``LT.lt && !ty.isAppOf ``LE.le then
        let arg := ty.appArg!
        let sameArg ←
          if arg.consumeMData == s.consumeMData then pure true
          else if (← inferType arg).isConstOf ``Memory.State then
            sameStateExpr arg s
          else pure false
        if sameArg then
          let inv := ty.appFn!
          if inv.isAppOf ``Memory.WellFormed then continue
          if let some inst ← lookupMonotoneMemInv? cache w inv then
            return some (inv, inst, decl.toExpr)
    return none

/-- Check if `rule` is a structural rule for head `progHead`. -/
private def findWrapperRule? (rules : Array RuleEntry) (predName : Name) (progHead : Name) :
    Option Expr :=
  rules.findSome? fun r =>
    if r.predName? == some predName && r.progHead? == some progHead then some r.expr
    else none

/-- Try applying `rule` at reducible transparency. -/
private def tryApplyRule (g : MVarId) (rule : Expr) (hints : Array Expr) :
    MetaM (Option (List MVarId)) := do
  let saved ← saveState
  try
    let sub ← g.withContext do withReducible (g.apply rule)
    let mut rem : List MVarId := []
    for sg in sub do
      if !(← tryCloseLeaf sg hints 2) then
        rem := rem ++ [sg]
    return some rem
  catch _ =>
    saved.restore
    return none

/-- Try applying `rule` with default transparency fallback when the head constant matches. -/
private def tryApplyRuleFlex (g : MVarId) (rule : Expr) (hints : Array Expr) :
    MetaM (Option (List MVarId)) := do
  if let some rem ← tryApplyRule g rule hints then return some rem
  let saved ← saveState
  try
    let sub ← g.apply rule
    let mut rem : List MVarId := []
    for sg in sub do
      if !(← tryCloseLeaf sg hints 2) then
        rem := rem ++ [sg]
    return some rem
  catch _ =>
    saved.restore
    return none

/-- Apply a matching subprogram rule for `(predName?, ph)`: prefer a candidate that closes all leaf
side conditions (`rem.isEmpty`), falling back to the first matching candidate if none closes all. -/
private def applyMatchingRule? (g : MVarId) (rules : Array RuleEntry) (predName? : Option Name)
    (ph : Name) (hints : Array Expr) : MetaM (Option (List MVarId)) := do
  let mut hasIncomplete := false
  for r in rules do
    if r.predName? == predName? && r.progHead? == some ph then
      let saved ← saveState
      let ruleE ← match r.expr.constName? with
        | some cn => mkConstFresh cn
        | none => pure r.expr
      if let some rem ← tryApplyRuleFlex g ruleE hints then
        if rem.isEmpty then return some []
        hasIncomplete := true
      saved.restore
  if !hasIncomplete then return none
  for r in rules do
    if r.predName? == predName? && r.progHead? == some ph then
      let ruleE ← match r.expr.constName? with
        | some cn => mkConstFresh cn
        | none => pure r.expr
      if let some rem ← tryApplyRuleFlex g ruleE hints then
        return some rem
  return none

/-- Build `a < s.frontier` directly without `mkAppM`. -/
private def mkAddrLtFrontier (addr s : Expr) : Expr :=
  mkAppN (mkConst ``LT.lt [Level.zero])
    #[mkConst ``Nat [], mkConst ``instLTNat [], addr,
      mkApp (mkConst ``Memory.State.frontier []) s]

/-- Create a synthetic opaque mvar for a leaf obligation and return `[id]` only if not closed by
`tryCloseLeaf`. -/
private def mkCheckedLeaf (ty : Expr) (hints : Array Expr) : MetaM (Expr × List MVarId) := do
  let mv ← mkFreshExprSyntheticOpaqueMVar ty
  if ← tryCloseLeaf mv.mvarId! hints 2 then
    return (mv, [])
  return (mv, [mv.mvarId!])

/-- Peel top-level `let` bindings, auxiliary `match`ers on tuples, and `Prod.casesOn` tuple
destructuring (`let (a, b, c) := x`) definitionally in O(1). -/
private partial def peelProgHead? (p : Expr) : MetaM (Option Expr) := do
  let p := p.consumeMData
  if p.isHeadBetaTarget then
    let p' := p.headBeta
    return some ((← peelProgHead? p').getD p')
  if let .letE _ _ v b _ := p then
    let p' := (b.instantiate1 v).headBeta
    return some ((← peelProgHead? p').getD p')
  if let some fn := p.getAppFn.constName? then
    if ← isMatcher fn then
      if let some pUnf ← delta? p (fun _ => true) then
        let p' := pUnf.headBeta
        if let some p'' ← peelProgHead? p' then
          return some p''
  if p.isAppOfArity ``Prod.casesOn 5 then
    let α := p.getArg! 0
    let β := p.getArg! 1
    let scrut := (p.getArg! 3).consumeMData
    let mkCase := p.getArg! 4
    let (fst, snd) ← if scrut.isAppOfArity ``Prod.mk 4 then
        pure (scrut.getArg! 2, scrut.getArg! 3)
      else
        pure (← mkAppOptM ``Prod.fst #[α, β, scrut], ← mkAppOptM ``Prod.snd #[α, β, scrut])
    let p' := (mkApp2 mkCase fst snd).headBeta
    return some ((← peelProgHead? p').getD p')
  return none

/-- Core structural recursion for `valid_prog`. Returns all unclosed leaf side goals. -/
private partial def walkValidProg (cache : InvCache) (g : MVarId) (rules : Array RuleEntry)
    (hints : Array Expr) (rwExprs : Array Expr) (fuel : Nat := 192) : MetaM (List MVarId) := do
  if fuel == 0 then return [g]
  if ← g.isAssigned then return []
  let t ← g.withContext do instantiateMVars (← g.getType)
  let some shape ← g.withContext do classifyGoal t
    | do
      if ← tryCloseLeaf g hints 2 then return []
      return [g]
  match shape with
  | .validHistory w α s p =>
    let p := p.consumeMData
    -- 0. Peel `let` bindings and tuple destructuring in `p` definitionally.
    if let some pNew ← g.withContext (peelProgHead? p) then
      let g' ← g.replaceTargetDefEq (rebuildValidHistory t α s pNew)
      return ← walkValidProg cache g' rules hints rwExprs (fuel - 1)
    -- 1. `pure`
    if (splitPure? p).isSome then
      g.assign (mkConst ``True.intro [])
      return []
    -- 2. `bind`: `m >>= k`
    if let some (mRaw, k) ← g.withContext (splitBind? p) then
      if let some mPeeled ← g.withContext (peelProgHead? mRaw) then
        let pNew ← g.withContext (mkAppM ``Bind.bind #[mPeeled, k])
        let g' ← g.replaceTargetDefEq (rebuildValidHistory t α s pNew)
        return ← walkValidProg cache g' rules hints rwExprs (fuel - 1)
      let m := mRaw.consumeMData
      -- 2a. `pure a >>= k`
      if let some a := splitPure? m then
        let pNew := (k.beta #[a]).headBeta
        let g' ← g.replaceTargetDefEq (rebuildValidHistory t α s pNew)
        return ← walkValidProg cache g' rules hints rwExprs (fuel - 1)
      -- 2b. Fast O(1) primitive `read` / `write` bind rules!
      if let some prim ← g.withContext (matchMemPrimOp? m) then
        match prim with
        | .read addr =>
          let (mvAddr, addrGoals) ← g.withContext do
            mkCheckedLeaf (mkAddrLtFrontier addr s) hints
          let memVal := mkApp2 (mkConst ``Memory.State.mem []) s addr
          let pNext := (k.beta #[memVal]).headBeta
          let hqTy := rebuildValidHistory t α s pNext
          let mvCont ← g.withContext do mkFreshExprSyntheticOpaqueMVar hqTy
          g.assign (mkAppN (mkConst ``validHistory_read_bind [])
            #[α, w, s, addr, k, mvAddr, mvCont])
          let contGoals ← walkValidProg cache mvCont.mvarId! rules hints rwExprs (fuel - 1)
          return addrGoals ++ contGoals
        | .write addr val =>
          let (mvAddr, addrGoals) ← g.withContext do
            mkCheckedLeaf (mkAddrLtFrontier addr s) hints
          let (mvFit, fitGoals) ← g.withContext do
            mkCheckedLeaf (mkApp2 (mkConst ``Fits []) w val) hints
          let (sNext, writeProg) ← g.withContext do
            let memUpd ← mkAppM ``Function.update
              #[mkApp (mkConst ``Memory.State.mem []) s, addr, val]
            let sn := mkApp2 (mkConst ``Memory.State.mk []) memUpd
              (mkApp (mkConst ``Memory.State.frontier []) s)
            let wp := mkApp2 (mkConst ``Memory.write []) addr val
            pure (sn, wp)
          let pNext := (k.beta #[mkConst ``Unit.unit []]).headBeta
          let hqTy := rebuildValidHistory t α sNext pNext
          let mvCont ← g.withContext do mkFreshExprSyntheticOpaqueMVar hqTy
          g.assign (mkAppN (mkConst ``validHistory_write_bind [])
            #[α, w, s, addr, val, k, mvAddr, mvFit, mvCont])
          let hpWrite := mkAppN (mkConst ``validHistory_write [])
            #[w, s, addr, val, mvAddr, mvFit]
          let gCont ← propagateMemInvs cache mvCont.mvarId! w s writeProg sNext hpWrite
          let contGoals ← walkValidProg cache gCont rules hints rwExprs (fuel - 1)
          return addrGoals ++ fitGoals ++ contGoals
        | _ => pure ()
      -- 2c. `((a >>= b) >>= c)` association
      if (← g.withContext (splitBind? m)).isSome then
        let saved ← saveState
        try
          let g' ← g.withContext do
            let r ← g.rewrite t (← mkConstFresh ``bind_assoc)
            g.replaceTargetEq r.eNew r.eqProof
          return ← walkValidProg cache g' rules hints rwExprs (fuel - 1)
        catch _ => saved.restore
      -- 2d. General `m >>= k` via direct `validHistory_bind_step`
      let β ← g.withContext do
        match k with
        | .lam _ dom _ _ => pure dom
        | _ => pure (← whnf (← inferType k)).bindingDomain!
      let leftTy := rebuildValidHistory t β s m
      let mvLeft ← g.withContext do mkFreshExprSyntheticOpaqueMVar leftTy
      let (sNext, rNext) ← g.withContext do
        let spec0 := mkApp (mkConst ``Memory.spec []) (mkNatLit 0)
        return (← mkAppM ``StateTransitionSpec.clientState #[spec0, s, m],
          ← mkAppM ``StateTransitionSpec.clientResult #[spec0, s, m])
      let pNext := (k.beta #[rNext]).headBeta
      let rightTy := rebuildValidHistory t α sNext pNext
      let mvRight ← g.withContext do mkFreshExprSyntheticOpaqueMVar rightTy
      g.assign (mkAppN (mkConst ``validHistory_bind_step [])
        #[β, α, w, s, m, k, mvLeft, mvRight])
      let leftGoals ← walkValidProg cache mvLeft.mvarId! rules hints rwExprs (fuel - 1)
      let gRight1 ← applyProgRewrites mvRight.mvarId! rwExprs hints
      let stateAfter ← gRight1.withContext do
        let t1 ← instantiateMVars (← gRight1.getType)
        match ← classifyGoal t1 with
        | some (.validHistory _ _ s' _) => pure s'
        | _ => pure sNext
      let gRight2 ← propagateMemInvs cache gRight1 w s m stateAfter mvLeft
      let rightGoals ← walkValidProg cache gRight2 rules hints rwExprs (fuel - 1)
      return leftGoals ++ rightGoals
    -- 3. Conditional `ite` / `dite` via direct `mkAppN`
    if p.isAppOfArity ``ite 5 then
      let c := p.getArg! 1
      let dec := p.getArg! 2
      let p₁ := p.getArg! 3
      let p₂ := p.getArg! 4
      let (mv1, mv2) ← g.withContext do
        let t1 ← mkArrow c (rebuildValidHistory t α s p₁)
        let t2 ← mkArrow (mkNot c) (rebuildValidHistory t α s p₂)
        return (← mkFreshExprSyntheticOpaqueMVar t1, ← mkFreshExprSyntheticOpaqueMVar t2)
      g.assign (mkAppN (mkConst ``validHistory_ite []) #[α, w, s, c, dec, p₁, p₂, mv1, mv2])
      let (_, g1) ← mv1.mvarId!.intro1
      let (_, g2) ← mv2.mvarId!.intro1
      return (← walkValidProg cache g1 rules hints rwExprs (fuel - 1)) ++
        (← walkValidProg cache g2 rules hints rwExprs (fuel - 1))
    if p.isAppOfArity ``dite 5 then
      let c := p.getArg! 1
      let dec := p.getArg! 2
      let p₁ := p.getArg! 3
      let p₂ := p.getArg! 4
      let (mv1, mv2) ← g.withContext do
        let t1 ← withLocalDeclD `hc c fun hc =>
          mkForallFVars #[hc] (rebuildValidHistory t α s (mkApp p₁ hc).headBeta)
        let t2 ← withLocalDeclD `hc (mkNot c) fun hc =>
          mkForallFVars #[hc] (rebuildValidHistory t α s (mkApp p₂ hc).headBeta)
        return (← mkFreshExprSyntheticOpaqueMVar t1, ← mkFreshExprSyntheticOpaqueMVar t2)
      g.assign (mkAppN (mkConst ``validHistory_dite []) #[α, w, s, c, dec, p₁, p₂, mv1, mv2])
      let (_, g1) ← mv1.mvarId!.intro1
      let (_, g2) ← mv2.mvarId!.intro1
      return (← walkValidProg cache g1 rules hints rwExprs (fuel - 1)) ++
        (← walkValidProg cache g2 rules hints rwExprs (fuel - 1))
    -- 4. Terminal primitive memory ops via direct `mkAppN`
    if let some prim ← g.withContext (matchMemPrimOp? p) then
      match prim with
      | .read addr =>
        let (mvAddr, addrGoals) ← g.withContext do
          mkCheckedLeaf (mkAddrLtFrontier addr s) hints
        g.assign (mkAppN (mkConst ``validHistory_read []) #[w, s, addr, mvAddr])
        return addrGoals
      | .write addr val =>
        let (mvAddr, addrGoals) ← g.withContext do
          mkCheckedLeaf (mkAddrLtFrontier addr s) hints
        let (mvFit, fitGoals) ← g.withContext do
          mkCheckedLeaf (mkApp2 (mkConst ``Fits []) w val) hints
        g.assign (mkAppN (mkConst ``validHistory_write []) #[w, s, addr, val, mvAddr, mvFit])
        return addrGoals ++ fitGoals
      | .alloc count =>
        let (mvFit, fitGoals) ← g.withContext do
          let sum ← mkAppM ``HAdd.hAdd #[mkApp (mkConst ``Memory.State.frontier []) s, count]
          mkCheckedLeaf (mkApp2 (mkConst ``Fits []) w sum) hints
        g.assign (mkAppN (mkConst ``validHistory_alloc []) #[w, s, count, mvFit])
        return fitGoals
      | .allocDirty count =>
        let (mvFit, fitGoals) ← g.withContext do
          let sum ← mkAppM ``HAdd.hAdd #[mkApp (mkConst ``Memory.State.frontier []) s, count]
          mkCheckedLeaf (mkApp2 (mkConst ``Fits []) w sum) hints
        g.assign (mkAppN (mkConst ``validHistory_allocDirty []) #[w, s, count, mvFit])
        return fitGoals
    -- 5. Matching subprogram certificate by head constant name
    if let some ph := headProgConst? p then
      if let some rem ← applyMatchingRule? g rules none ph hints then
        return rem
    -- 5b. `iterate` / `boundedWhile` via a `MonotoneMemInv` hypothesis in context
    if p.isAppOfArity ``Realization.iterate 6 then
      if let some (inv, inst, hinv) ← findMonotoneMemInv? cache g w s then
        let saved ← saveState
        try
          let pArgs := p.getAppArgs
          let stepTy ← g.withContext do
            withLocalDeclD `a pArgs[1]! fun a =>
              withLocalDeclD `tState (mkConst ``Memory.State) fun tState => do
                let bodyApp := (mkApp pArgs[2]! (← mkAppM ``Prod.mk #[pArgs[3]!, a])).headBeta
                let concl := rebuildValidHistory t pArgs[1]! tState bodyApp
                mkForallFVars #[a, tState] (← mkArrow (mkApp inv tState) concl)
          let stepMv ← g.withContext do mkFreshExprSyntheticOpaqueMVar stepTy
          let pf := mkAppN (mkConst ``validHistory_iterate_inv [])
            #[pArgs[0]!, pArgs[1]!, w, inv, inst, pArgs[2]!, pArgs[3]!, stepMv,
              pArgs[4]!, pArgs[5]!, s, hinv]
          g.assign pf
          let (_, gStep') ← stepMv.mvarId!.introN 3
          return ← walkValidProg cache gStep' rules hints rwExprs (fuel - 1)
        catch _ => saved.restore
    if p.isAppOfArity ``Realization.boundedWhile 8 then
      if let some (inv, inst, hinv) ← findMonotoneMemInv? cache g w s then
        let saved ← saveState
        try
          let pArgs := p.getAppArgs
          let stepTy ← g.withContext do
            withLocalDeclD `a pArgs[1]! fun a =>
              withLocalDeclD `tState (mkConst ``Memory.State) fun tState => do
                let bodyApp := (mkApp pArgs[4]! (← mkAppM ``Prod.mk #[pArgs[5]!, a])).headBeta
                let concl := rebuildValidHistory t pArgs[1]! tState bodyApp
                let gd := mkApp2 pArgs[2]! pArgs[5]! a
                mkForallFVars #[a, tState] (← mkArrow (mkApp inv tState) (← mkArrow gd concl))
          let stepMv ← g.withContext do mkFreshExprSyntheticOpaqueMVar stepTy
          let pf := mkAppN (mkConst ``validHistory_boundedWhile_inv [])
            #[pArgs[0]!, pArgs[1]!, w, inv, inst, pArgs[2]!, pArgs[3]!, pArgs[4]!, pArgs[5]!,
              stepMv, pArgs[6]!, pArgs[7]!, s, hinv]
          g.assign pf
          let (_, gStep') ← stepMv.mvarId!.introN 4
          return ← walkValidProg cache gStep' rules hints rwExprs (fuel - 1)
        catch _ => saved.restore
    if ← tryCloseLeaf g hints 2 then return []
    return [g]

  | .wrapper predName p =>
    let p := p.consumeMData
    if let some pNew ← g.withContext (peelProgHead? p) then
      let args := t.getAppArgs
      let g' ← g.replaceTargetDefEq (mkAppN t.getAppFn (args.set! (args.size - 1) pNew))
      return ← walkValidProg cache g' rules hints rwExprs (fuel - 1)
    if (splitPure? p).isSome then
      if let some pureRule := findWrapperRule? rules predName ``Pure.pure
          <|> findWrapperRule? rules predName ``PFunctor.FreeM.pure then
        let rE ← match pureRule.constName? with
          | some cn => mkConstFresh cn
          | none => pure pureRule
        if let some rem ← tryApplyRuleFlex g rE hints then
          return rem
    if let some (m, k) ← g.withContext (splitBind? p) then
      let m := m.consumeMData
      if let some a := splitPure? m then
        let pNew := (k.beta #[a]).headBeta
        let args := t.getAppArgs
        let g' ← g.replaceTargetDefEq (mkAppN t.getAppFn (args.set! (args.size - 1) pNew))
        return ← walkValidProg cache g' rules hints rwExprs (fuel - 1)
      if (← g.withContext (splitBind? m)).isSome then
        let saved ← saveState
        try
          let g' ← g.withContext do
            let r ← g.rewrite t (← mkConstFresh ``bind_assoc)
            g.replaceTargetEq r.eNew r.eqProof
          return ← walkValidProg cache g' rules hints rwExprs (fuel - 1)
        catch _ => saved.restore
      if let some bindRule := findWrapperRule? rules predName ``Bind.bind
          <|> findWrapperRule? rules predName ``PFunctor.FreeM.bind then
        let rE ← match bindRule.constName? with
          | some cn => mkConstFresh cn
          | none => pure bindRule
        let saved ← saveState
        try
          let sub ← g.apply rE
          if let [gLeft, gRight] := sub then
            let leftGoals ← walkValidProg cache gLeft rules hints rwExprs (fuel - 1)
            let rwAll ← if (← g.withContext (matchMemPrimOp? m)).isSome then
                pure (rwExprs ++ #[mkConst ``clientState_read [], mkConst ``clientResult_read []])
              else pure rwExprs
            let gRight' ← applyProgRewrites gRight rwAll hints
            let rightGoals ← walkValidProg cache gRight' rules hints rwExprs (fuel - 1)
            return leftGoals ++ rightGoals
          saved.restore
        catch _ => saved.restore
    if p.isAppOfArity ``ite 5 then
      if let some iteRule := findWrapperRule? rules predName ``ite then
        let rE ← match iteRule.constName? with
          | some cn => mkConstFresh cn
          | none => pure iteRule
        let saved ← saveState
        try
          let sub ← g.apply rE
          if let [g1, g2] := sub then
            let (_, g1') ← g1.intro1
            let (_, g2') ← g2.intro1
            return (← walkValidProg cache g1' rules hints rwExprs (fuel - 1)) ++
              (← walkValidProg cache g2' rules hints rwExprs (fuel - 1))
          saved.restore
        catch _ => saved.restore
    if let some ph := headProgConst? p then
      if let some rem ← applyMatchingRule? g rules (some predName) ph hints then
        return rem
    if ← tryCloseLeaf g hints 2 then return []
    return [g]

/-- Collect `Expr`s for all currently scoped entries of a `SimpleScopedEnvExtension`. -/
private def envExtExprs (ext : SimpleScopedEnvExtension Name (Array Name)) :
    MetaM (Array (Expr × Bool)) := do
  let names := ext.getState (← getEnv)
  names.mapM fun n => return (← mkConstFresh n, true)

/-- Core entry point for `valid_prog`. -/
def runValidProg (extraTerms : Array Term) (rwTerms : Array Term) : TacticM Unit :=
  withMainContext do
    let extraExprs ← extraTerms.mapM fun stx => do
      let e ← instantiateMVars (← elabTerm stx none)
      let e ← if e.hasExprMVar then pure (← abstractMVars e (levels := false)).expr else pure e
      return (e, false)
    let rwExprs ← rwTerms.mapM fun stx => do
      let e ← instantiateMVars (← elabTerm stx none)
      if e.hasExprMVar then pure (← abstractMVars e (levels := false)).expr else pure e
    let envValid ← envExtExprs validProgExt
    let (rules, hints) ← indexRules (extraExprs ++ envValid)
    let cache ← IO.mkRef #[]
    let g ← getMainGoal
    let rem ← walkValidProg cache g rules hints rwExprs
    replaceMainGoal rem

/-- Walk a `Memory.Prog` admissibility goal (`ValidHistory` or a custom `ValidProg` predicate)
across `pure`, `bind`, `ite`, `dite`, and memory operations, applying explicit and `@[valid_prog]`
certificates and rewriting continuations with `with [...]` lemmas. -/
syntax (name := validProg) "valid_prog" ("[" term,* "]")? (" with " "[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| valid_prog $[[$cs,*]]? $[with [$rws,*]]?) => do
    let csArr := cs.map (·.getElems) |>.getD #[]
    let rwsArr := rws.map (·.getElems) |>.getD #[]
    runValidProg csArr rwsArr

/-! ## `prog_cost` tactic -/

/-- Simplify and close `memoryCost` equality or upper-bound goals across monadic binds,
conditionals (including nested `if`-branches), and optional user-supplied rewrite lemmas. -/
syntax (name := progCost) "prog_cost" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| prog_cost $[[$extra,*]]?) => do
    let simpStep ← match extra with
      | none => `(tactic|
          try simp only [pure_bind, memoryCost_pure, memoryCost_bind, memoryCost_bind',
            memoryCost_ite, memoryCost_read, memoryCost_write, memoryCost_alloc,
            memoryCost_allocDirty, StateTransitionSpec.clientState_pure,
            StateTransitionSpec.clientResult_pure, PFunctor.FreeM.bind_eq_bind])
      | some ex => `(tactic|
          try simp only [$ex,*, pure_bind, memoryCost_pure, memoryCost_bind, memoryCost_bind',
            memoryCost_ite, memoryCost_read, memoryCost_write, memoryCost_alloc,
            memoryCost_allocDirty, StateTransitionSpec.clientState_pure,
            StateTransitionSpec.clientResult_pure, PFunctor.FreeM.bind_eq_bind])
    evalTactic simpStep
    for _ in [0:8] do
      if (← getGoals).isEmpty then break
      let closedByOmega ← try
        evalTactic (← `(tactic| omega))
        pure true
      catch _ => pure false
      if !closedByOmega then
        let before ← getGoals
        let splitOk ← try
          evalTactic (← `(tactic| (split_ifs <;> $simpStep)))
          pure true
        catch _ => pure false
        if !splitOk || (← getGoals) == before then break
    if !(← getGoals).isEmpty then
      evalTactic (← `(tactic| all_goals try omega))

end Cslib.Tactic.ValidProg
