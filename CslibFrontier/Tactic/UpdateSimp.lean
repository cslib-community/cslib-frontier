/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Tactic.StrideOmega

/-!
# Linear-time simplification for chained and conditional `Function.update`

Word-RAM specifications frequently evaluate deep chains of `Function.update` (and conditional
updates `if p then Function.update f a v else f`) at a query address `k`. Simplifying such terms
with `split_ifs <;> repeat rw [Function.update_of_ne (by omega)]` triggers an exponential `2^n`
case split on unrelated conditional writes and generates dozens of redundant `omega` proofs.

`update_simp` peels both unconditional and conditional `Function.update` layers **in a single
linear top-down pass without splitting `if` branches**:

* `Function.update f a v k`: rewrites to `v` if `k = a` holds, and to `f k` if `k ≠ a` holds.
* `(if p then Function.update f a v else f) k`: under the branch assumption `hp : p`, checks
  `k ≠ a` and collapses directly to `f k` without splitting on `p` (essential when `p` guards
  an in-bounds address check such as `q_b < dirSlabsPerBucket n_max`).
* `(if p then Function.update f a v else g) k`: drops the update inside the `then` branch when
  `p → k ≠ a` (leaving `(if p then f else g) k`), or simplifies directly when `p` is provably
  true/false, or collapses `if p then f else f` to `f`. Symmetric rule handles the `else` branch.
* Preserves `let`-sharing for nested maps (`let gm₁ := ...; let gm₂ := ...`) by peeling one head
  binding at a time instead of eagerly zeta-reducing, keeping proof and term sizes `O(depth)`.
* Silently discharges index equality/disequality and guard truth/falsity via local hypotheses,
  `isDefEq`, `decide`, `omega` with `@[wram_arith]` unfolding, and `StrideOmega.prove?` (which
  handles strided 2D bounds and injectivity `b' * S + s ≠ b * S + q₀`), without triggering
  `linter.unnecessaryWramOmega`.
* Supports `Data.write` / `Data.set` projections (`(d.write a v).mem`, `(d.set i v).regs`,
  `(d.write a v).regs`, `(d.set i v).mem`) whenever those declarations are in the environment.

## Main definitions

* `update_simp`: tactic simplifying chained/conditional `Function.update` applications in the goal
  and/or specified hypotheses (`update_simp [def₁, h₁, ...] at loc`).
* `Cslib.Tactic.UpdateSimp.reduceUpdate`: `simp` procedure simplifying `Function.update f a v k`.
-/

public section

namespace Cslib.Tactic.UpdateSimp

universe u v

/-- Collapse `(if p then Function.update f a v else f) k` to `f k` when `p → k ≠ a`,
without splitting on `p`. -/
protected theorem ite_update_of_ne {α : Sort u} {β : Sort v} [DecidableEq α]
    {p : Prop} [Decidable p] (f : α → β) (a : α) (v : β) (k : α) (h : p → k ≠ a) :
    (if p then Function.update f a v else f) k = f k := by
  by_cases hp : p
  · rw [ite_eq_left hp]
    exact Function.update_of_ne (h hp) v f
  · rw [ite_eq_right hp]

/-- Collapse `(if p then f else Function.update f a v) k` to `f k` when `¬p → k ≠ a`,
without splitting on `p`. -/
protected theorem ite_update_else_same_of_ne {α : Sort u} {β : Sort v} [DecidableEq α]
    {p : Prop} [Decidable p] (f : α → β) (a : α) (v : β) (k : α) (h : ¬p → k ≠ a) :
    (if p then f else Function.update f a v) k = f k := by
  by_cases hp : p
  · rw [ite_eq_left hp]
  · rw [ite_eq_right hp]
    exact Function.update_of_ne (h hp) v f

/-- Peel `Function.update` in the `then` branch of `(if p then ... else g) k`
when `p → k ≠ a`. -/
protected theorem ite_update_then_of_ne {α : Sort u} {β : Sort v} [DecidableEq α]
    {p : Prop} [Decidable p] (f g : α → β) (a : α) (v : β) (k : α) (h : p → k ≠ a) :
    (if p then Function.update f a v else g) k = (if p then f else g) k := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left hp]
    exact Function.update_of_ne (h hp) v f
  · rw [ite_eq_right hp, ite_eq_right hp]

/-- Peel `Function.update` in the `else` branch of `(if p then f else ...) k`
when `¬p → k ≠ a`. -/
protected theorem ite_update_else_of_ne {α : Sort u} {β : Sort v} [DecidableEq α]
    {p : Prop} [Decidable p] (f g : α → β) (a : α) (v : β) (k : α) (h : ¬p → k ≠ a) :
    (if p then f else Function.update g a v) k = (if p then f else g) k := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left hp]
  · rw [ite_eq_right hp, ite_eq_right hp]
    exact Function.update_of_ne (h hp) v g

/-- Reduce `(if p then Function.update f a v else g) k` to `if p then v else g k`
when `p → k = a`. -/
protected theorem ite_update_then_of_eq {α : Sort u} {β : Sort v} [DecidableEq α]
    {p : Prop} [Decidable p] (f g : α → β) (a : α) (v : β) (k : α) (h : p → k = a) :
    (if p then Function.update f a v else g) k = if p then v else g k := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left hp, h hp, Function.update_self]
  · rw [ite_eq_right hp, ite_eq_right hp]

/-- Reduce `(if p then f else Function.update g a v) k` to `if p then f k else v`
when `¬p → k = a`. -/
protected theorem ite_update_else_of_eq {α : Sort u} {β : Sort v} [DecidableEq α]
    {p : Prop} [Decidable p] (f g : α → β) (a : α) (v : β) (k : α) (h : ¬p → k = a) :
    (if p then f else Function.update g a v) k = if p then f k else v := by
  by_cases hp : p
  · rw [ite_eq_left hp, ite_eq_left hp]
  · rw [ite_eq_right hp, ite_eq_right hp, h hp, Function.update_self]

end Cslib.Tactic.UpdateSimp

end

public meta section

namespace Cslib.Tactic.UpdateSimp

open Lean Meta Elab Tactic

/-- Maximum consecutive peeling steps on a single update expression (guards against cycles). -/
private def maxPeelSteps : Nat := 128

/-- Configuration for a single `update_simp` traversal. -/
private structure Config where
  /-- Constants unfolded on sight at the head of an applied function or `ite`. -/
  unfoldDefs : NameSet := {}
  /-- Extra arithmetic hint terms passed to `StrideOmega.prove?`. -/
  extraHints : Array Expr := #[]
  /-- Per-check internal heartbeat cap (`1000` per option unit) for arithmetic probes. -/
  heartbeatCap : Nat := 15_000_000
  /-- Also reduce plain `if p then x else y` values when `p` or `¬p` is provable. -/
  reduceIteVals : Bool := true

/-- Test whether `α` is a `Nat`, `Int`, or `Fin n` type amenable to `omega`/`stride_omega`. -/
private def isArithType (α : Expr) : Bool :=
  α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1

/-- Look up an exact proof of `prop` in the local context (plus symmetric equality/disequality). -/
private def findExactProof? (prop : Expr) : MetaM (Option Expr) := do
  let prop ← instantiateMVars prop
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t == prop then
      return some d.toExpr
  if prop.isAppOfArity ``Eq 3 then
    let args := prop.getAppArgs
    let sym := mkApp3 (prop.getAppFn) args[0]! args[2]! args[1]!
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type) == sym then
        return some (← mkEqSymm d.toExpr)
  if prop.isAppOfArity ``Ne 3 then
    let args := prop.getAppArgs
    let sym := mkApp3 (prop.getAppFn) args[0]! args[2]! args[1]!
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type) == sym then
        return some (← mkAppM ``Ne.symm #[d.toExpr])
  if prop.isAppOfArity ``Not 1 then
    let inner := prop.appArg!
    if inner.isAppOfArity ``Eq 3 then
      let args := inner.getAppArgs
      let ne1 ← mkAppOptM ``Ne #[some args[0]!, some args[1]!, some args[2]!]
      let ne2 ← mkAppOptM ``Ne #[some args[0]!, some args[2]!, some args[1]!]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if t == ne1 then return some d.toExpr
        if t == ne2 then return some (← mkAppM ``Ne.symm #[d.toExpr])
  return none

/-- Try to decide a ground proposition via `decide`. -/
private def tryDecide? (prop : Expr) : MetaM (Option Expr) := do
  if prop.hasFVar || prop.hasMVar then return none
  let saved ← saveState
  try
    return some (← mkDecideProof prop)
  catch _ =>
    saved.restore
    return none

/-- Silently attempt to prove an arithmetic/boolean proposition `prop` using exact lookup,
`decide`, or `StrideOmega.prove?`. -/
private def proveProp? (cfg : Config) (prop : Expr) : MetaM (Option Expr) := do
  let prop ← instantiateMVars prop
  if let some h ← findExactProof? prop then
    return some h
  if let some h ← tryDecide? prop then
    return some h
  if prop.isAppOfArity ``Eq 3 then
    let args := prop.getAppArgs
    if args[1]! == args[2]! then
      return some (← mkEqRefl args[1]!)
    if let (some m, some n) := (args[1]!.nat?, args[2]!.nat?) then
      if m == n then return some (← mkEqRefl args[1]!)
      return none
  if prop.isAppOfArity ``Ne 3 then
    let args := prop.getAppArgs
    if args[1]! == args[2]! then return none
    if let (some m, some n) := (args[1]!.nat?, args[2]!.nat?) then
      if m != n then
        try return some (← mkDecideProof prop) catch _ => pure ()
      else
        return none
  Cslib.Tactic.StrideOmega.prove? prop cfg.unfoldDefs cfg.extraHints cfg.heartbeatCap

/-- Non-dependent `Function.update f a v` parts when `fn` has arity 6:
`@Function.update α (fun _ => β) inst f a v`. -/
private structure UpdateApp where
  α : Expr
  motive : Expr
  β : Expr
  inst : Expr
  f : Expr
  a : Expr
  v : Expr

private def matchNondepUpdate? (fn : Expr) : Option UpdateApp :=
  if fn.isAppOfArity ``Function.update 6 then
    let args := fn.getAppArgs
    let α := args[0]!
    let motive := args[1]!
    match motive with
    | .lam _ _ body _ =>
      if body.hasLooseBVars then none
      else
        some { α, motive, β := body, inst := args[2]!, f := args[3]!, a := args[4]!, v := args[5]! }
    | _ => none
  else none

/-- Match an `ite` expression `@ite γ p dec t e`. -/
private structure IteApp where
  γ : Expr
  p : Expr
  dec : Expr
  tBranch : Expr
  eBranch : Expr

private def matchIte? (e : Expr) : Option IteApp :=
  if e.isAppOfArity ``ite 5 then
    let args := e.getAppArgs
    some { γ := args[0]!, p := args[1]!, dec := args[2]!, tBranch := args[3]!, eBranch := args[4]! }
  else none

/-- Try checking if `fn` is a `Data.mem` / `Data.regs` projection on `Data.write` / `Data.set`
or on an `ite` expression, returning a `Simp.Result` reducing the head map. -/
private def reduceDataProj? (fn : Expr) : MetaM (Option Simp.Result) := do
  let .const projName _ := fn.getAppFn | return none
  unless projName == `Cslib.WordRAM.Data.mem || projName == `Cslib.WordRAM.Data.regs do
    return none
  let args := fn.getAppArgs
  unless args.size == 2 do return none
  let r := args[0]!
  let d := args[1]!
  let isMem := projName == `Cslib.WordRAM.Data.mem
  -- `(if p then x else y).mem` → `if p then x.mem else y.mem` via `apply_ite`
  if let some it := matchIte? d then
    let projFn := mkApp (fn.getAppFn) r
    let t' := mkApp projFn it.tBranch
    let e' := mkApp projFn it.eBranch
    let res ← mkAppM ``ite #[it.p, t', e']
    let pf ← mkAppOptM ``apply_ite
      #[some it.γ, none, some projFn, some it.p, some it.dec, some it.tBranch, some it.eBranch]
    return some { expr := res, proof? := some pf }
  -- `(x.write a v).mem` / `(x.set i v).mem` / `(x.write a v).regs` / `(x.set i v).regs`
  if d.isAppOfArity `Cslib.WordRAM.Data.write 4 then
    let dArgs := d.getAppArgs
    let x := dArgs[1]!; let a := dArgs[2]!; let v := dArgs[3]!
    let env ← getEnv
    if isMem && env.contains `Cslib.WordRAM.Data.write_mem then
      let pf ← mkAppM `Cslib.WordRAM.Data.write_mem #[x, a, v]
      let eqTy ← inferType pf
      let some (_, _, rhs) := eqTy.eq? | return none
      return some { expr := rhs, proof? := some pf }
    if !isMem && env.contains `Cslib.WordRAM.Data.write_regs then
      let pf ← mkAppM `Cslib.WordRAM.Data.write_regs #[x, a, v]
      let eqTy ← inferType pf
      let some (_, _, rhs) := eqTy.eq? | return none
      return some { expr := rhs, proof? := some pf }
  if d.isAppOfArity `Cslib.WordRAM.Data.set 4 then
    let dArgs := d.getAppArgs
    let x := dArgs[1]!; let i := dArgs[2]!; let v := dArgs[3]!
    let env ← getEnv
    if isMem && env.contains `Cslib.WordRAM.Data.set_mem then
      let pf ← mkAppM `Cslib.WordRAM.Data.set_mem #[x, i, v]
      let eqTy ← inferType pf
      let some (_, _, rhs) := eqTy.eq? | return none
      return some { expr := rhs, proof? := some pf }
    if !isMem && env.contains `Cslib.WordRAM.Data.set_regs then
      let pf ← mkAppM `Cslib.WordRAM.Data.set_regs #[x, i, v]
      let eqTy ← inferType pf
      let some (_, _, rhs) := eqTy.eq? | return none
      return some { expr := rhs, proof? := some pf }
  return none

/-- Unfold one head step of `fn` if `fn` is a local `let`-bound `fvar` or a constant in
`cfg.unfoldDefs`. Returns `some fn'` definitionally equal to `fn`. -/
private def unfoldHeadMap? (cfg : Config) (fn : Expr) : MetaM (Option Expr) := do
  match fn.getAppFn with
  | .fvar fvarId =>
    let some val ← fvarId.getValue? | return none
    let val ← instantiateMVars val
    let expanded := val.betaRev fn.getAppRevArgs
    if expanded.isAppOfArity ``Function.update 6 || expanded.isAppOfArity ``ite 5 ||
       expanded.isLet || expanded.isLambda then
      return some expanded
    return none
  | .const name us =>
    unless cfg.unfoldDefs.contains name do return none
    let info ← getConstInfo name
    unless info.hasValue && info.levelParams.length == us.length do return none
    let val ← instantiateValueLevelParams info us
    return some (val.betaRev fn.getAppRevArgs (useZeta := false))
  | _ => return none

/-- Compose two `Simp.Result` proofs `lhs = mid` and `mid = rhs` (`none` means `rfl`). -/
private def composeRes (_lhs : Expr) (r₁ r₂ : Simp.Result) : MetaM Simp.Result := do
  match r₁.proof?, r₂.proof? with
  | none, none => return { expr := r₂.expr, proof? := none }
  | some p₁, none => return { expr := r₂.expr, proof? := some p₁ }
  | none, some p₂ => return { expr := r₂.expr, proof? := some p₂ }
  | some p₁, some p₂ => return { expr := r₂.expr, proof? := some (← mkEqTrans p₁ p₂) }

/-- Try proving `k = a` or `k ≠ a` via `proveProp?`, using structural checks first. -/
private def proveNe? (cfg : Config) (α k a : Expr) : MetaM (Option Expr) := do
  let neProp ← mkAppOptM ``Ne #[some α, some k, some a]
  if let some h ← findExactProof? neProp then return some h
  if !isArithType α then return none
  proveProp? cfg neProp

private def proveEq? (cfg : Config) (α k a : Expr) : MetaM (Option Expr) := do
  if k == a then return some (← mkEqRefl k)
  let eqProp ← mkEq k a
  if let some h ← findExactProof? eqProp then return some h
  if !isArithType α then return none
  proveProp? cfg eqProp

/-- Try a conditional proof `p → Q` by opening a local assumption `hp : p`. -/
private def proveUnderHyp? (p : Expr) (build : MetaM (Option Expr)) : MetaM (Option Expr) := do
  withLocalDeclD `hp p fun hp => do
    match ← build with
    | some pf => return some (← mkLambdaFVars #[hp] pf)
    | none => return none

/-- Build `(Function.update f a v) k = v` from `heq : k = a` using core `Function.update_self`. -/
private def mkUpdateEqProof (fn : Expr) (u : UpdateApp) (k heq : Expr) : MetaM Expr := do
  let pSelf ← mkAppOptM ``Function.update_self
    #[some u.α, some u.motive, some u.inst, some u.a, some u.v, some u.f]
  if u.a == k then
    return pSelf
  let pCongr ← mkCongrArg fn heq
  mkEqTrans pCongr pSelf

/-- Try a single peeling step on `(fn k)`, preserving local `let` structure to avoid exponential
term duplication on chains like `let gm₁ := if ...; let gm₂ := if ...; ...`. -/
private partial def peelApplied (cfg : Config) (fn k : Expr) (fuel : Nat) :
    MetaM (Option Simp.Result) := do
  if fuel == 0 then return none
  let fn := fn.cleanupAnnotations
  -- 1. Head `let`: `((let x := val; body) k)` is defeq to `let x := val; (body k)`.
  if let .letE n ty val body _ := fn then
    let orig := mkApp fn k
    let res? ← withLetDecl n ty val (nondep := false) fun x => do
      let bodyInst := body.instantiate1 x
      match ← peelApplied cfg bodyInst k (fuel - 1) with
      | none => return none
      | some r =>
        let e' := r.expr
        let (finalExpr, pf?) ←
          if e'.containsFVar x.fvarId! then
            let finalE := Expr.letE n ty val (e'.abstract #[x]) false
            match r.proof? with
            | none => pure (finalE, none)
            | some pf =>
              let pfWrapped := Expr.letE n ty val (pf.abstract #[x]) false
              let eqTy ← mkEq orig finalE
              pure (finalE, some (← mkExpectedTypeHint pfWrapped eqTy))
          else
            match r.proof? with
            | none => pure (e', some (← mkEqRefl e'))
            | some pf =>
              let pfWrapped := Expr.letE n ty val (pf.abstract #[x]) false
              let eqTy ← mkEq orig e'
              pure (e', some (← mkExpectedTypeHint pfWrapped eqTy))
        return some { expr := finalExpr, proof? := pf? }
    return res?
  -- 2. Head `lambda`: `((fun x => body) k)` beta-reduces cleanly.
  if let .lam _ _ body _ := fn then
    let reduced := body.instantiate1 k
    if let .app fn' k' := reduced then
      match ← peelApplied cfg fn' k' (fuel - 1) with
      | some r => return some { expr := r.expr, proof? := r.proof? }
      | none => return some { expr := reduced, proof? := none }
    return some { expr := reduced, proof? := none }
  -- 3. `Data.mem` / `Data.regs` projections on `Data.write` / `Data.set` / `ite`.
  if let some pr ← reduceDataProj? fn then
    let nextExpr := mkApp pr.expr k
    let stepPf? ← pr.proof?.mapM fun p => mkCongrFun p k
    let stepRes : Simp.Result := { expr := nextExpr, proof? := stepPf? }
    match ← peelApplied cfg pr.expr k (fuel - 1) with
    | some r₂ => return some (← composeRes (mkApp fn k) stepRes r₂)
    | none => return some stepRes
  -- 4. Direct `Function.update f a v k`.
  if let some u := matchNondepUpdate? fn then
    if u.a == k then
      let pf ← mkUpdateEqProof fn u k (← mkEqRefl k)
      return some { expr := u.v, proof? := some pf }
    if let some hne ← proveNe? cfg u.α k u.a then
      let pf ← mkAppOptM ``Function.update_of_ne
        #[some u.α, some u.motive, some u.inst, some k, some u.a, some hne, some u.v, some u.f]
      let next := mkApp u.f k
      let step : Simp.Result := { expr := next, proof? := some pf }
      match ← peelApplied cfg u.f k (fuel - 1) with
      | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
      | none => return some step
    if let some heq ← proveEq? cfg u.α k u.a then
      let pf ← mkUpdateEqProof fn u k heq
      return some { expr := u.v, proof? := some pf }
    return none
  -- 5. Conditional `(if p then t else e) k`.
  if let some it := matchIte? fn then
    if it.tBranch == it.eBranch then
      let pIte ← mkAppOptM ``ite_self #[some it.γ, some it.p, some it.dec, some it.tBranch]
      let pf ← mkCongrFun pIte k
      let next := mkApp it.tBranch k
      let step : Simp.Result := { expr := next, proof? := some pf }
      match ← peelApplied cfg it.tBranch k (fuel - 1) with
      | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
      | none => return some step
    if let some hp ← proveProp? cfg it.p then
      let pIte ← mkAppOptM ``ite_eq_left
        #[some it.p, some it.dec, some hp, some it.γ, some it.tBranch, some it.eBranch]
      let pf ← mkCongrFun pIte k
      let next := mkApp it.tBranch k
      let step : Simp.Result := { expr := next, proof? := some pf }
      match ← peelApplied cfg it.tBranch k (fuel - 1) with
      | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
      | none => return some step
    let notP := mkApp (mkConst ``Not) it.p
    if let some hnp ← proveProp? cfg notP then
      let pIte ← mkAppOptM ``ite_eq_right
        #[some it.p, some it.dec, some hnp, some it.γ, some it.tBranch, some it.eBranch]
      let pf ← mkCongrFun pIte k
      let next := mkApp it.eBranch k
      let step : Simp.Result := { expr := next, proof? := some pf }
      match ← peelApplied cfg it.eBranch k (fuel - 1) with
      | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
      | none => return some step
    -- Reduce `Data.mem` / `Data.regs` projections inside `then` / `else` branches of `ite`.
    if let some pr ← reduceDataProj? it.tBranch then
      if let some p := pr.proof? then
        let lam ← withLocalDeclD `br it.γ fun br =>
          mkLambdaFVars #[br] (mkApp5 fn.getAppFn it.γ it.p it.dec br it.eBranch)
        let pf ← mkCongrFun (← mkCongrArg lam p) k
        let fn' := mkApp5 fn.getAppFn it.γ it.p it.dec pr.expr it.eBranch
        let step : Simp.Result := { expr := mkApp fn' k, proof? := some pf }
        match ← peelApplied cfg fn' k (fuel - 1) with
        | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
        | none => return some step
    if let some pr ← reduceDataProj? it.eBranch then
      if let some p := pr.proof? then
        let lam ← withLocalDeclD `br it.γ fun br =>
          mkLambdaFVars #[br] (mkApp5 fn.getAppFn it.γ it.p it.dec it.tBranch br)
        let pf ← mkCongrFun (← mkCongrArg lam p) k
        let fn' := mkApp5 fn.getAppFn it.γ it.p it.dec it.tBranch pr.expr
        let step : Simp.Result := { expr := mkApp fn' k, proof? := some pf }
        match ← peelApplied cfg fn' k (fuel - 1) with
        | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
        | none => return some step
    -- `then` branch is `Function.update f a v`! Collapse under assumption `hp : p` WITHOUT split!
    if let some u := matchNondepUpdate? it.tBranch then
      if let some hfun ← proveUnderHyp? it.p (proveNe? cfg u.α k u.a) then
        if u.f == it.eBranch then
          let pf ← mkAppOptM ``UpdateSimp.ite_update_of_ne
            #[some u.α, some u.β, some u.inst, some it.p, some it.dec,
              some u.f, some u.a, some u.v, some k, some hfun]
          let next := mkApp u.f k
          let step : Simp.Result := { expr := next, proof? := some pf }
          match ← peelApplied cfg u.f k (fuel - 1) with
          | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
          | none => return some step
        else
          let pf ← mkAppOptM ``UpdateSimp.ite_update_then_of_ne
            #[some u.α, some u.β, some u.inst, some it.p, some it.dec,
              some u.f, some it.eBranch, some u.a, some u.v, some k, some hfun]
          let fn' := mkApp5 fn.getAppFn it.γ it.p it.dec u.f it.eBranch
          let next := mkApp fn' k
          let step : Simp.Result := { expr := next, proof? := some pf }
          match ← peelApplied cfg fn' k (fuel - 1) with
          | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
          | none => return some step
      if let some hfun ← proveUnderHyp? it.p (proveEq? cfg u.α k u.a) then
        let pf ← mkAppOptM ``UpdateSimp.ite_update_then_of_eq
          #[some u.α, some u.β, some u.inst, some it.p, some it.dec,
            some u.f, some it.eBranch, some u.a, some u.v, some k, some hfun]
        let rhsEqTy ← inferType pf
        let some (_, _, rhs) := rhsEqTy.eq? | return none
        return some { expr := rhs, proof? := some pf }
    -- `else` branch is `Function.update g a v`! Collapse under `hnp : ¬p` WITHOUT splitting!
    if let some u := matchNondepUpdate? it.eBranch then
      if let some hfun ← proveUnderHyp? notP (proveNe? cfg u.α k u.a) then
        if u.f == it.tBranch then
          let pf ← mkAppOptM ``UpdateSimp.ite_update_else_same_of_ne
            #[some u.α, some u.β, some u.inst, some it.p, some it.dec,
              some u.f, some u.a, some u.v, some k, some hfun]
          let next := mkApp u.f k
          let step : Simp.Result := { expr := next, proof? := some pf }
          match ← peelApplied cfg u.f k (fuel - 1) with
          | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
          | none => return some step
        else
          let pf ← mkAppOptM ``UpdateSimp.ite_update_else_of_ne
            #[some u.α, some u.β, some u.inst, some it.p, some it.dec,
              some it.tBranch, some u.f, some u.a, some u.v, some k, some hfun]
          let fn' := mkApp5 fn.getAppFn it.γ it.p it.dec it.tBranch u.f
          let next := mkApp fn' k
          let step : Simp.Result := { expr := next, proof? := some pf }
          match ← peelApplied cfg fn' k (fuel - 1) with
          | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
          | none => return some step
      if let some hfun ← proveUnderHyp? notP (proveEq? cfg u.α k u.a) then
        let pf ← mkAppOptM ``UpdateSimp.ite_update_else_of_eq
          #[some u.α, some u.β, some u.inst, some it.p, some it.dec,
            some it.tBranch, some u.f, some u.a, some u.v, some k, some hfun]
        let rhsEqTy ← inferType pf
        let some (_, _, rhs) := rhsEqTy.eq? | return none
        return some { expr := rhs, proof? := some pf }
    return none
  -- 6. Single-step unfold of a local `let`-bound function `fvar` or user-named `def`.
  if let some fn' ← unfoldHeadMap? cfg fn then
    match ← peelApplied cfg fn' k (fuel - 1) with
    | some r =>
      match r.proof? with
      | none => return some { expr := r.expr, proof? := none }
      | some pf =>
        let eqTy ← mkEq (mkApp fn k) r.expr
        return some { expr := r.expr, proof? := some (← mkExpectedTypeHint pf eqTy) }
    | none => return none
  return none

/-- Single `Simp.pre` step invoked inside `update_simp`. -/
private def simpPreStep (cfg : Config) (e : Expr) : SimpM Simp.Step := do
  if let .app fn k := e then
    if let some r ← peelApplied cfg fn k maxPeelSteps then
      return .visit r
    -- Lean's default congruence skips the index argument of `Function.update` because its
    -- declared codomain `(fun _ => β) a` has a unreduced beta-redex mentioning `a`. When `fn`
    -- has non-dependent codomain after `headBeta`, simplify `k` first and then peel `fn k'`.
    if k.isApp then
      if let .forallE _ α β _ ← whnfD (← inferType fn) then
        let β' := β.headBeta
        if !β'.hasLooseBVars then
          let kr ← Simp.simp k
          if kr.expr != k then
            let pfk ← kr.getProof
            let pf₁ ← mkAppOptM ``congrArg
              #[some α, some β', some k, some kr.expr, some fn, some pfk]
            let step₁ : Simp.Result := { expr := mkApp fn kr.expr, proof? := some pf₁ }
            match ← peelApplied cfg fn kr.expr maxPeelSteps with
            | some r₂ => return .visit (← composeRes e step₁ r₂)
            | none => return .visit step₁
  if cfg.reduceIteVals then
    if let some it := matchIte? e then
      if it.tBranch == it.eBranch then
        let pf ← mkAppOptM ``ite_self #[some it.γ, some it.p, some it.dec, some it.tBranch]
        return .visit { expr := it.tBranch, proof? := some pf }
      if let some hp ← proveProp? cfg it.p then
        let pf ← mkAppOptM ``ite_eq_left
          #[some it.p, some it.dec, some hp, some it.γ, some it.tBranch, some it.eBranch]
        return .visit { expr := it.tBranch, proof? := some pf }
      let notP := mkApp (mkConst ``Not) it.p
      if let some hnp ← proveProp? cfg notP then
        let pf ← mkAppOptM ``ite_eq_right
          #[some it.p, some it.dec, some hnp, some it.γ, some it.tBranch, some it.eBranch]
        return .visit { expr := it.eBranch, proof? := some pf }
  return .continue

/-- Reduce a single `Function.update f a v k` expression as a `simp` procedure. -/
def reduceUpdateStep : Simp.Simproc := fun e => do
  let .app fn k := e | return .continue
  let some r ← peelApplied { reduceIteVals := false } fn k maxPeelSteps | return .continue
  return .visit r

/-- Run `update_simp` over a single proposition `e`, returning the `Simp.Result`. -/
private def simpProp (cfg : Config) (e : Expr) : MetaM Simp.Result := do
  let ctx ← Simp.mkContext
    (config := { zeta := false, beta := true, eta := false, decide := false })
  let methods : Simp.Methods := { pre := simpPreStep cfg }
  let (r, _) ← Simp.main e ctx (methods := methods)
  return r

/-- Parse the bracket arguments `update_simp [x₁, x₂, ...]` into constant definitions to unfold
and extra hypothesis/proof terms to supply to `StrideOmega`. -/
private def parseArgs (args : Array Term) : TacticM (NameSet × Array Expr) := do
  let mut defs : NameSet := {}
  let mut hints : Array Expr := #[]
  for stx in args do
    if stx.raw.isIdent then
      let name? ← try
        some <$> realizeGlobalConstNoOverload stx
      catch _ =>
        pure none
      if let some name := name? then
        let env ← getEnv
        if let some info := env.find? name then
          if info.isDef then
            defs := defs.insert name
            continue
    let e ← withMainContext <| elabTerm stx none
    hints := hints.push e
  return (defs, hints)

/-- Simplify chained and conditional `Function.update` applications without splitting `if` guards.

* `update_simp` peels `Function.update f a v k` and `(if p then Function.update f a v else g) k`
  in the goal using local facts, `decide`, `omega` (with `@[wram_arith]` unfolding), and
  `stride_omega` (strided injectivity and bounds), automatically closing trivial equalities
  `lhs = rhs` when `lhs` and `rhs` become definitionally equal.
* `update_simp [d₁, d₂, h₁]` additionally unfolds head definitions `d₁, d₂` (such as
  `gmPushSlab`, `gmCompactSlab`, `gmUnlinkTopSlab`) when applied to an index, and supplies local
  or global hints `h₁` to the arithmetic solver.
* `update_simp [...] at h₁ h₂ ⊢` rewrites in the named hypotheses and/or the goal. -/
syntax (name := updateSimp)
  "update_simp" (" [" term,* "]")? (ppSpace Lean.Parser.Tactic.location)? : tactic

@[inherit_doc updateSimp]
elab_rules : tactic
  | `(tactic| update_simp $[[$args,*]]? $(loc)?) => do
    recordExtraModUse (isMeta := false) `Init.Omega
    recordExtraModUse (isMeta := false) `CslibFrontier.Tactic.StrideOmega
    recordExtraModUse (isMeta := false) `CslibFrontier.Tactic.UpdateSimp
    let rawArgs := (args.map (·.getElems)).getD #[]
    let (unfoldDefs, extraHints) ← parseArgs rawArgs
    let cfg : Config := { unfoldDefs, extraHints }
    let loc := expandOptLocation (Lean.mkNullNode (loc.toArray.map (·.raw)))
    withLocation loc
      (atLocal := fun fvarId => do
        let g ← getMainGoal
        g.withContext do
          let decl ← fvarId.getDecl
          let ty ← instantiateMVars decl.type
          let r ← simpProp cfg ty
          if r.expr != ty then
            let some (_, g') ← applySimpResultToLocalDecl g fvarId r (mayCloseGoal := true)
              | setGoals []; return
            replaceMainGoal [g'])
      (atTarget := do
        let g ← getMainGoal
        g.withContext do
          let target ← instantiateMVars (← g.getType)
          let r ← simpProp cfg target
          let g' ← if r.expr != target then
            applySimpResultToTarget g target r
          else
            pure g
          let closed ← g'.withContext do
            let saved ← saveState
            try
              g'.refl
              return true
            catch _ =>
              saved.restore
              return false
          if closed then
            replaceMainGoal []
          else if r.expr == target then
            throwError "update_simp: made no progress on target"
          else
            replaceMainGoal [g'])
      (failed := fun mvarId =>
        throwError "update_simp: made no progress in {mvarId}")

end Cslib.Tactic.UpdateSimp

end

public section

namespace Cslib.Tactic.UpdateSimp

/-- `simp` procedure reducing chained/conditional `Function.update f a v k` applications via
`update_simp`. -/
simproc_decl reduceUpdate (Function.update _ _ _ _) := reduceUpdateStep

end Cslib.Tactic.UpdateSimp

end
