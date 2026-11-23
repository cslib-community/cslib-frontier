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
* **Unchanged projection & branch collapsing without case splits:** collapses non-dependent
  (possibly nested) structure projection chains `g (Function.update f a v k) = g (f k)` when
  `g v = g (f a)` definitionally, and `g (if p then t else e) = g e` (as well as function-valued
  `(if p then t else e) k = e k`) when `p → g t = g e` (or `p → t k = e k` after peeling `t k`
  under `p`, including substituting equality guards `r = a` / `a = r` and unwrapping local
  `let`/`have` bindings).
* **Curried & nested structure map projections:** reduces map-valued structure projections on
  constructors, unfolded `def`s in `[d₁, ...]`, `ite` branches, and curried multi-argument maps
  such as `(S.chan u) v` and `((S.proc v).chanRec) u`, while preserving `Data.write` / `Data.set`
  fast paths (`(d.write a v).mem`, `(d.set i v).regs`, `(d.write a v).regs`, `(d.set i v).mem`).
* **Guard & disequality discharge:** resolves local hypotheses (including symmetry `h.symm`,
  `let`-bound indices, and structural `And` / `¬ (A ∧ B)` guards on arbitrary `[DecidableEq α]`),
  `isDefEq`, `decide`, `omega` with `@[wram_arith]` unfolding, and `StrideOmega.prove?` (strided 2D
  bounds and injectivity `b' * S + s ≠ b * S + q₀`), fast-exiting before arithmetic solvers on
  non-arithmetic types.

## Main definitions

* `update_simp`: tactic simplifying chained/conditional `Function.update` applications in the goal
  and/or specified hypotheses (`update_simp [def₁, h₁, ...] at loc`).
* `Cslib.Tactic.UpdateSimp.reduceUpdate`: `simp` procedure simplifying `Function.update f a v k`.
-/

public section

namespace Cslib.Tactic.UpdateSimp

universe u v w

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

/-- Collapse `g (Function.update f a v k)` to `g (f k)` when `g v = g (f a)`,
without splitting on `k = a`. -/
protected theorem apply_update_of_eq {α : Sort u} {β : Sort v} {γ : Sort w} [DecidableEq α]
    (g : β → γ) (f : α → β) (a : α) (v : β) (k : α) (h : g v = g (f a)) :
    g (Function.update f a v k) = g (f k) := by
  by_cases hk : k = a
  · rw [hk, Function.update_self, h]
  · rw [Function.update_of_ne hk]

/-- Collapse `g (if p then x else y)` to `g y` when `p → g x = g y`,
without splitting on `p`. -/
protected theorem apply_ite_of_eq {β : Sort u} {γ : Sort v}
    {p : Prop} [Decidable p] (g : β → γ) (x y : β) (h : p → g x = g y) :
    g (if p then x else y) = g y := by
  by_cases hp : p
  · rw [ite_eq_left hp, h hp]
  · rw [ite_eq_right hp]

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

/-- Test whether `α` is an arithmetic or `Bool` type that `omega`/`stride_omega` may inspect. -/
private def isArithOrBoolType (α : Expr) : Bool :=
  isArithType α || α.isConstOf ``Bool

/-- Chase head local `let` variable bindings up to `fuel` hops in `O(1)`. -/
private def unfoldLetFVar : Expr → Nat → MetaM Expr
  | .fvar id, n + 1 => do
    match ← id.getValue? with
    | some v => unfoldLetFVar (← instantiateMVars v) n
    | none => return .fvar id
  | e, _ => return e

/-- Look up an exact proof of `prop` in the local context (plus symmetric equality/disequality and
`let`-bound alias unfolding). -/
private def findExactProof? (prop : Expr) : MetaM (Option Expr) := do
  let prop ← instantiateMVars prop
  let eqPair? ←
    if prop.isAppOfArity ``Eq 3 then
      let a := prop.getAppArgs
      pure (some (false, a[0]!, ← unfoldLetFVar a[1]! 4, ← unfoldLetFVar a[2]! 4))
    else if prop.isAppOfArity ``Ne 3 then
      let a := prop.getAppArgs
      pure (some (true, a[0]!, ← unfoldLetFVar a[1]! 4, ← unfoldLetFVar a[2]! 4))
    else if prop.isAppOfArity ``Not 1 && prop.appArg!.isAppOfArity ``Eq 3 then
      let a := prop.appArg!.getAppArgs
      pure (some (true, a[0]!, ← unfoldLetFVar a[1]! 4, ← unfoldLetFVar a[2]! 4))
    else pure none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t == prop then return some d.toExpr
    if let some (isNe, _, x, y) := eqPair? then
      if !isNe && t.isAppOfArity ``Eq 3 then
        let ta := t.getAppArgs
        let tx ← unfoldLetFVar ta[1]! 4; let ty ← unfoldLetFVar ta[2]! 4
        if tx == x && ty == y then return some (← mkExpectedTypeHint d.toExpr prop)
        if tx == y && ty == x then return some (← mkExpectedTypeHint (← mkEqSymm d.toExpr) prop)
      if isNe && t.isAppOfArity ``Ne 3 then
        let ta := t.getAppArgs
        let tx ← unfoldLetFVar ta[1]! 4; let ty ← unfoldLetFVar ta[2]! 4
        if tx == x && ty == y then return some (← mkExpectedTypeHint d.toExpr prop)
        if tx == y && ty == x then
          return some (← mkExpectedTypeHint (← mkAppM ``Ne.symm #[d.toExpr]) prop)
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

/-- Silently attempt to prove an arithmetic/boolean/conjunctive proposition `prop` using exact
lookup, `decide`, structural `And` rules, or `StrideOmega.prove?`. -/
private partial def proveProp? (cfg : Config) (prop : Expr) : MetaM (Option Expr) := do
  let prop ← instantiateMVars prop
  if let some h ← findExactProof? prop then
    return some h
  if let some h ← tryDecide? prop then
    return some h
  if prop.isAppOfArity ``And 2 then
    let args := prop.getAppArgs
    if let some h₁ ← proveProp? cfg args[0]! then
      if let some h₂ ← proveProp? cfg args[1]! then
        return some (← mkAppM ``And.intro #[h₁, h₂])
    return none
  if prop.isAppOfArity ``Not 1 then
    let inner := prop.appArg!
    if inner.isAppOfArity ``And 2 then
      let a := inner.getAppArgs[0]!
      let b := inner.getAppArgs[1]!
      if let some hna ← proveProp? cfg (mkApp (mkConst ``Not) a) then
        return some (← withLocalDeclD `h inner fun h => do
          mkLambdaFVars #[h] (mkApp hna (← mkAppM ``And.left #[h])))
      if let some hnb ← proveProp? cfg (mkApp (mkConst ``Not) b) then
        return some (← withLocalDeclD `h inner fun h => do
          mkLambdaFVars #[h] (mkApp hnb (← mkAppM ``And.right #[h])))
      return none
    if inner.isAppOfArity ``Eq 3 && !isArithOrBoolType (inner.getAppArgs[0]!) then
      return none
  if prop.isAppOfArity ``Eq 3 then
    let args := prop.getAppArgs
    if args[1]! == args[2]! then
      return some (← mkEqRefl args[1]!)
    if let (some m, some n) := (args[1]!.nat?, args[2]!.nat?) then
      if m == n then return some (← mkEqRefl args[1]!)
      return none
    if !isArithOrBoolType args[0]! then
      return none
  if prop.isAppOfArity ``Ne 3 then
    let args := prop.getAppArgs
    if args[1]! == args[2]! then return none
    if let (some m, some n) := (args[1]!.nat?, args[2]!.nat?) then
      if m != n then
        try return some (← mkDecideProof prop) catch _ => pure ()
      else
        return none
    if !isArithOrBoolType args[0]! then
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

/-- Match a single structure projection `proj structVal` (either `.proj` or a projection constant
applied to its structure parameters and `structVal`), returning `(structVal, rebuildProj)`. -/
private def matchStructProj? (env : Environment) (e : Expr) :
    Option (Expr × (Expr → Expr)) :=
  match e with
  | .proj typeName idx structVal =>
    some (structVal, fun s' => .proj typeName idx s')
  | _ =>
    match e.getAppFn with
    | .const projName _ =>
      match env.getProjectionFnInfo? projName with
      | some info =>
        let args := e.getAppArgs
        if args.size == info.numParams + 1 then
          let pref := mkAppN e.getAppFn args[:info.numParams]
          some (args[info.numParams]!, fun s' => mkApp pref s')
        else none
      | none => none
    | _ => none

/-- Peel one or more consecutive outer structure projections `P₁ (... (Pₘ core))`, returning
`(core, rebuildChain)`. -/
private partial def splitProjChain? (env : Environment) (e : Expr) :
    Option (Expr × (Expr → Expr)) := do
  let (inner, rebuildOuter) ← matchStructProj? env e
  match splitProjChain? env inner with
  | some (core, rebuildInner) => some (core, fun z => rebuildOuter (rebuildInner z))
  | none => some (inner, rebuildOuter)

/-- Reduce a structure projection `e` when applied to a constructor (`Struct.field (Struct.mk ...)`
or primitive `.proj`), returning `some fieldVal` when definitionally reducible. -/
private def reduceProjApp? (env : Environment) (e : Expr) : MetaM (Option Expr) := do
  if let some v ← Meta.reduceProj? e then
    return some v
  if let .const projName _ := e.getAppFn then
    if let some info := env.getProjectionFnInfo? projName then
      let args := e.getAppArgs
      if args.size == info.numParams + 1 then
        let d := args[info.numParams]!
        if d.getAppFn.isConstOf info.ctorName then
          let dArgs := d.getAppArgs
          if h : info.numParams + info.i < dArgs.size then
            return some dArgs[info.numParams + info.i]
  return none

/-- Unfold one definitional head step of a structure/map expression `e` via beta (`have`),
`reduceMatcher?`, `cfg.unfoldDefs`, or a local `let`-bound `fvar`. -/
private def unfoldStructStep? (cfg : Config) (e : Expr) : MetaM (Option Expr) := do
  let hb := e.headBeta
  if hb != e then
    return some hb
  if let .reduced e' ← Meta.reduceMatcher? e then
    return some e'
  match e.getAppFn with
  | .const name us =>
    unless cfg.unfoldDefs.contains name do return none
    let info ← getConstInfo name
    unless info.hasValue && info.levelParams.length == us.length do return none
    let val ← instantiateValueLevelParams info us
    return some (val.betaRev e.getAppRevArgs (useZeta := false))
  | .fvar fvarId =>
    let some val ← fvarId.getValue? | return none
    let val ← instantiateMVars val
    if val.isAppOfArity ``ite 5 || val.isAppOfArity ``Function.update 6 then return none
    return some (val.betaRev e.getAppRevArgs (useZeta := false))
  | _ => return none

/-- Normalize `e` using only definitional reductions permitted by `cfg` (`cfg.unfoldDefs`, local
`let` bindings, beta, constructor projections, and `reduceMatcher?`). -/
private def expandUnfoldDefs (cfg : Config) (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform e
    (pre := fun s => do
      let s := s.cleanupAnnotations
      if let .letE _ _ val body _ := s then
        return .visit (body.instantiate1 val)
      if let some s' ← reduceProjApp? env s then
        return .visit s'
      if let .reduced s' ← Meta.reduceMatcher? s then
        return .visit s'
      if let some s' ← unfoldStructStep? cfg s then
        return .visit s'
      return .continue)
    (post := fun s => do
      let hb := s.headBeta
      if hb != s then return .visit hb
      if let some s' ← reduceProjApp? env s then
        return .visit s'
      if let .reduced s' ← Meta.reduceMatcher? s then
        return .visit s'
      return .done s)

/-- Check kernel definitional equality after controlled unfolding of `cfg.unfoldDefs` and `let`s. -/
private def defEqUnfold (cfg : Config) (a b : Expr) : MetaM Bool := do
  if a == b then return true
  let a' ← expandUnfoldDefs cfg a
  let b' ← expandUnfoldDefs cfg b
  if a' == b' then return true
  withTransparency .reducible (isDefEq a' b')

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

/-- Step inside a `let`/`have` binding `x : ty := val`, re-wrapping `x` only if still referenced. -/
private def stepUnderLet? (orig : Expr) (n : Name) (ty val : Expr)
    (inner : Expr → MetaM (Option Simp.Result)) : MetaM (Option Simp.Result) :=
  withLetDecl n ty val (nondep := false) fun x => do
    let some r ← inner x | return none
    let e' := r.expr
    let (finalE, pfW) ←
      if e'.containsFVar x.fvarId! then
        let wE := Expr.letE n ty val (e'.abstract #[x]) false
        let wP ← match r.proof? with
          | none => mkEqRefl wE
          | some pf => pure (Expr.letE n ty val (pf.abstract #[x]) false)
        pure (wE, wP)
      else
        let wP ← match r.proof? with
          | none => mkEqRefl e'
          | some pf => pure (Expr.letE n ty val (pf.abstract #[x]) false)
        pure (e', wP)
    return some { expr := finalE, proof? := some (← mkExpectedTypeHint pfW (← mkEq orig finalE)) }

/-- Syntactic check whether `core` has an outer `Function.update` or `ite` worth inspecting. -/
private partial def hasUpdateOrIteHead : Expr → Bool
  | .letE _ _ _ b _ => hasUpdateOrIteHead b
  | .app (.letE _ _ _ fn _) k => hasUpdateOrIteHead (mkApp fn k)
  | e => e.isAppOfArity ``ite 5 ||
      match e with | .app fn _ => fn.isAppOfArity ``Function.update 6 | _ => false

/-- Try a conditional proof `p → Q` by opening a local assumption `hp : p`. -/
private def proveUnderHyp? (p : Expr) (build : MetaM (Option Expr)) : MetaM (Option Expr) := do
  withLocalDeclD `hp p fun hp => do
    match ← build with
    | some pf => return some (← mkLambdaFVars #[hp] pf)
    | none => return none

/-- Given `hp : p` in context, try proving `gt = ge` by definitional unfolding or equality-guard
substitution (`p` of the form `lhs = rhs`). -/
private def proveBranchEqWithHyp? (cfg : Config) (p hp gt ge : Expr) : MetaM (Option Expr) := do
  if ← defEqUnfold cfg gt ge then
    return some (← mkExpectedTypeHint (← mkEqRefl ge) (← mkEq gt ge))
  if p.isAppOfArity ``Eq 3 then
    let eqArgs := p.getAppArgs
    let αEq := eqArgs[0]!; let lhs := eqArgs[1]!; let rhs := eqArgs[2]!
    let bodyL ← kabstract ge lhs
    if bodyL.hasLooseBVars then
      if ← defEqUnfold cfg gt (bodyL.instantiate1 rhs) then
        let lam := Expr.lam `z αEq bodyL .default
        let pCongr ← mkCongrArg lam (← mkEqSymm hp)
        return some (← mkExpectedTypeHint pCongr (← mkEq gt ge))
    let bodyR ← kabstract ge rhs
    if bodyR.hasLooseBVars then
      if ← defEqUnfold cfg gt (bodyR.instantiate1 lhs) then
        let lam := Expr.lam `z αEq bodyR .default
        let pCongr ← mkCongrArg lam hp
        return some (← mkExpectedTypeHint pCongr (← mkEq gt ge))
  return none

/-- Reduce a value-level `if p then t else e` when `t == e`, `p` holds, or `¬p` holds. -/
private def reduceValIte? (cfg : Config) (e : Expr) : MetaM (Option Simp.Result) := do
  let some it := matchIte? e | return none
  if it.tBranch == it.eBranch then
    let pf ← mkAppOptM ``ite_self #[some it.γ, some it.p, some it.dec, some it.tBranch]
    return some { expr := it.tBranch, proof? := some pf }
  if let some hp ← proveProp? cfg it.p then
    let pf ← mkAppOptM ``ite_eq_left
      #[some it.p, some it.dec, some hp, some it.γ, some it.tBranch, some it.eBranch]
    return some { expr := it.tBranch, proof? := some pf }
  let notP := mkApp (mkConst ``Not) it.p
  if let some hnp ← proveProp? cfg notP then
    let pf ← mkAppOptM ``ite_eq_right
      #[some it.p, some it.dec, some hnp, some it.γ, some it.tBranch, some it.eBranch]
    return some { expr := it.eBranch, proof? := some pf }
  return none

/-- Build `(Function.update f a v) k = v` from `heq : k = a` using core `Function.update_self`. -/
private def mkUpdateEqProof (fn : Expr) (u : UpdateApp) (k heq : Expr) : MetaM Expr := do
  let pSelf ← mkAppOptM ``Function.update_self
    #[some u.α, some u.motive, some u.inst, some u.a, some u.v, some u.f]
  if u.a == k then
    return pSelf
  let pCongr ← mkCongrArg fn heq
  mkEqTrans pCongr pSelf

mutual

/-- Try reducing a structure projection `fn` on `Data.write`/`Data.set`, a constructor (possibly
behind `cfg.unfoldDefs` or `let`), an applied map `fn₀ k₀`, or pushing through `ite`. -/
private partial def reduceMapProj? (cfg : Config) (fn : Expr) (fuel : Nat := 16) :
    MetaM (Option Simp.Result) := do
  if fuel == 0 then return none
  let env ← getEnv
  let some (d, rebuildProj) := matchStructProj? env fn | return none
  -- Fast path for WordRAM `(x.write a v).mem` / `(x.set i v).mem` / `.regs` without `[write]`.
  if let .const projName _ := fn.getAppFn then
    if projName == `Cslib.WordRAM.Data.mem || projName == `Cslib.WordRAM.Data.regs then
      let isMem := projName == `Cslib.WordRAM.Data.mem
      if d.isAppOfArity `Cslib.WordRAM.Data.write 4 then
        let dArgs := d.getAppArgs
        let x := dArgs[1]!; let a := dArgs[2]!; let v := dArgs[3]!
        if isMem && env.contains `Cslib.WordRAM.Data.write_mem then
          let pf ← mkAppM `Cslib.WordRAM.Data.write_mem #[x, a, v]
          let some (_, _, rhs) := (← inferType pf).eq? | return none
          return some { expr := rhs, proof? := some pf }
        if !isMem && env.contains `Cslib.WordRAM.Data.write_regs then
          let pf ← mkAppM `Cslib.WordRAM.Data.write_regs #[x, a, v]
          let some (_, _, rhs) := (← inferType pf).eq? | return none
          return some { expr := rhs, proof? := some pf }
      if d.isAppOfArity `Cslib.WordRAM.Data.set 4 then
        let dArgs := d.getAppArgs
        let x := dArgs[1]!; let i := dArgs[2]!; let v := dArgs[3]!
        if isMem && env.contains `Cslib.WordRAM.Data.set_mem then
          let pf ← mkAppM `Cslib.WordRAM.Data.set_mem #[x, i, v]
          let some (_, _, rhs) := (← inferType pf).eq? | return none
          return some { expr := rhs, proof? := some pf }
        if !isMem && env.contains `Cslib.WordRAM.Data.set_regs then
          let pf ← mkAppM `Cslib.WordRAM.Data.set_regs #[x, i, v]
          let some (_, _, rhs) := (← inferType pf).eq? | return none
          return some { expr := rhs, proof? := some pf }
  -- Constructor projection: `Struct.field (Struct.mk ...)` reduces definitionally.
  if let some fieldVal ← reduceProjApp? env fn then
    let pf ← mkExpectedTypeHint (← mkEqRefl fieldVal) (← mkEq fn fieldVal)
    return some { expr := fieldVal, proof? := some pf }
  -- Push non-dependent projection through `ite`: `(if p then x else y).field`.
  if let some it := matchIte? d then
    let projFn ← withLocalDeclD `z it.γ fun z => mkLambdaFVars #[z] (rebuildProj z)
    let .forallE _ _ cod _ ← inferType projFn | return none
    if !cod.hasLooseBVars then
      let t' := rebuildProj it.tBranch
      let e' := rebuildProj it.eBranch
      let res ← mkAppM ``ite #[it.p, t', e']
      let pf ← mkAppOptM ``apply_ite
        #[some it.γ, some cod, some projFn, some it.p, some it.dec, some it.tBranch,
          some it.eBranch]
      return some { expr := res, proof? := some pf }
  -- Step inside `let x := val; body` preserving sharing.
  if let .letE n ty val body _ := d then
    return ← stepUnderLet? fn n ty val fun x =>
      reduceMapProj? cfg (rebuildProj (body.instantiate1 x)) (fuel - 1)
  -- If `d` is an applied map `(fn₀ k₀)` (e.g. `(S.proc v)` inside `((S.proc v).chanRec) u`),
  -- peel `d` first and lift through `rebuildProj`.
  if let .app fn₀ k₀ := d then
    if let some rD ← peelApplied cfg fn₀ k₀ (fuel - 1) then
      if rD.expr != d then
        let dTy ← inferType d
        let projFn ← withLocalDeclD `z dTy fun z => mkLambdaFVars #[z] (rebuildProj z)
        let .forallE _ _ cod _ ← inferType projFn | return none
        if !cod.hasLooseBVars then
          let nextFn := rebuildProj rD.expr
          let pfD ← match rD.proof? with
            | none => mkExpectedTypeHint (← mkEqRefl nextFn) (← mkEq fn nextFn)
            | some p =>
              mkAppOptM ``congrArg #[some dTy, some cod, some d, some rD.expr, some projFn, some p]
          let step₁ : Simp.Result := { expr := nextFn, proof? := some pfD }
          match ← reduceMapProj? cfg nextFn (fuel - 1) with
          | some r₂ => return some (← composeRes fn step₁ r₂)
          | none => return some step₁
  -- Step through one unfolding of `d` via beta, `cfg.unfoldDefs`, `reduceMatcher?`, or `let`-fvar.
  if let some d' ← unfoldStructStep? cfg d then
    let some r ← reduceMapProj? cfg (rebuildProj d') (fuel - 1) | return none
    let pfRaw ← match r.proof? with
      | none => mkEqRefl r.expr
      | some pf => pure pf
    return some { expr := r.expr, proof? := some (← mkExpectedTypeHint pfRaw (← mkEq fn r.expr)) }
  return none

/-- Try a single peeling step on `(fn k)`, preserving local `let` structure to avoid exponential
term duplication on chains like `let gm₁ := if ...; let gm₂ := if ...; ...`. -/
private partial def peelApplied (cfg : Config) (fn k : Expr) (fuel : Nat) :
    MetaM (Option Simp.Result) := do
  if fuel == 0 then return none
  let fn := fn.cleanupAnnotations
  -- 1. Head `let`: `((let x := val; body) k)` is defeq to `let x := val; (body k)`.
  if let .letE n ty val body _ := fn then
    return ← stepUnderLet? (mkApp fn k) n ty val fun x =>
      peelApplied cfg (body.instantiate1 x) k (fuel - 1)
  -- 2. Head `lambda`: `((fun x => body) k)` beta-reduces cleanly.
  if let .lam _ _ body _ := fn then
    let reduced := body.instantiate1 k
    if let .app fn' k' := reduced then
      match ← peelApplied cfg fn' k' (fuel - 1) with
      | some r => return some { expr := r.expr, proof? := r.proof? }
      | none => return some { expr := reduced, proof? := none }
    return some { expr := reduced, proof? := none }
  -- 3. Structure projections on `Data.write` / `Data.set` / constructors / `ite`.
  if let some pr ← reduceMapProj? cfg fn then
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
    -- Reduce map projections inside `then` / `else` branches of `ite`.
    if let some pr ← reduceMapProj? cfg it.tBranch then
      let fn' := mkApp5 fn.getAppFn it.γ it.p it.dec pr.expr it.eBranch
      let stepPf? ← pr.proof?.mapM fun p => do
        let lam ← withLocalDeclD `br it.γ fun br =>
          mkLambdaFVars #[br] (mkApp5 fn.getAppFn it.γ it.p it.dec br it.eBranch)
        mkCongrFun (← mkCongrArg lam p) k
      let step : Simp.Result := { expr := mkApp fn' k, proof? := stepPf? }
      match ← peelApplied cfg fn' k (fuel - 1) with
      | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
      | none => return some step
    if let some pr ← reduceMapProj? cfg it.eBranch then
      let fn' := mkApp5 fn.getAppFn it.γ it.p it.dec it.tBranch pr.expr
      let stepPf? ← pr.proof?.mapM fun p => do
        let lam ← withLocalDeclD `br it.γ fun br =>
          mkLambdaFVars #[br] (mkApp5 fn.getAppFn it.γ it.p it.dec it.tBranch br)
        mkCongrFun (← mkCongrArg lam p) k
      let step : Simp.Result := { expr := mkApp fn' k, proof? := stepPf? }
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
    -- General unchanged-branch rule (non-`Function.update` branches): if
    -- `p → tBranch k = eBranch k` (after peeling `tBranch k` under `hp : p`),
    -- collapse `(if p then ... else eBranch) k`.
    if (matchNondepUpdate? it.tBranch).isNone && (matchNondepUpdate? it.eBranch).isNone then
      if let .forallE _ _ cod _ ← whnfD it.γ then
        if !cod.hasLooseBVars then
          let tk0 := mkApp it.tBranch k
          let ek := mkApp it.eBranch k
          let hfun? ← withLocalDeclD `hp it.p fun hp => do
            let mut cur := tk0
            let mut curPf? : Option Expr := none
            if let some r1 ← peelApplied cfg it.tBranch k (fuel - 1) then
              let p1 ← match r1.proof? with
                | some p => pure p
                | none => mkExpectedTypeHint (← mkEqRefl r1.expr) (← mkEq tk0 r1.expr)
              cur := r1.expr
              curPf? := some p1
            if cfg.reduceIteVals then
              if let some r2 ← reduceValIte? cfg cur then
                let p2 ← match r2.proof? with
                  | some p => pure p
                  | none => mkExpectedTypeHint (← mkEqRefl r2.expr) (← mkEq cur r2.expr)
                curPf? ← match curPf? with
                  | some p1 => some <$> mkEqTrans p1 p2
                  | none => pure (some p2)
                cur := r2.expr
            let some pEq ← proveBranchEqWithHyp? cfg it.p hp cur ek | return none
            let fullPf ← match curPf? with
              | some p1 => mkEqTrans p1 pEq
              | none => pure pEq
            some <$> mkLambdaFVars #[hp] (← mkExpectedTypeHint fullPf (← mkEq tk0 ek))
          if let some hfun := hfun? then
            let g ← withLocalDeclD `f it.γ fun f => mkLambdaFVars #[f] (mkApp f k)
            let pf ← mkAppOptM ``UpdateSimp.apply_ite_of_eq
              #[some it.γ, some cod, some it.p, some it.dec, some g, some it.tBranch,
                some it.eBranch, some hfun]
            let step : Simp.Result := { expr := ek, proof? := some pf }
            match ← peelApplied cfg it.eBranch k (fuel - 1) with
            | some r₂ => return some (← composeRes (mkApp fn k) step r₂)
            | none => return some step
    return none
  -- 6. Single-step unfold of a local `let`-bound function `fvar` or user-named `def`.
  if let some fn' ← unfoldHeadMap? cfg fn then
    match ← peelApplied cfg fn' k (fuel - 1) with
    | some r =>
      let eqTy ← mkEq (mkApp fn k) r.expr
      let pfRaw ← match r.proof? with
        | none => mkEqRefl r.expr
        | some pf => pure pf
      return some { expr := r.expr, proof? := some (← mkExpectedTypeHint pfRaw eqTy) }
    | none => return none
  -- 7. Curried multi-argument map `(fn₁ k₁) k` (e.g. `(S.chan u) v` or `((S.proc v).chanRec) u`).
  if let .app fn₁ k₁ := fn then
    if let some rFn ← peelApplied cfg fn₁ k₁ (fuel - 1) then
      if rFn.expr != fn then
        let nextExpr := mkApp rFn.expr k
        let stepPf ← match rFn.proof? with
          | none => mkExpectedTypeHint (← mkEqRefl nextExpr) (← mkEq (mkApp fn k) nextExpr)
          | some p => mkCongrFun p k
        let step₁ : Simp.Result := { expr := nextExpr, proof? := some stepPf }
        match ← peelApplied cfg rFn.expr k (fuel - 1) with
        | some r₂ => return some (← composeRes (mkApp fn k) step₁ r₂)
        | none => return some step₁
  return none

/-- Collapse a chain of non-dependent structure projections `g core` when `core` (possibly after
peeling an outer map application or local `let`s) is a `Function.update f a v k` or
`if p then x else y` whose guard resolves or that leaves `g` unchanged. -/
private partial def peelProjCore? (cfg : Config) (β γ g : Expr) (rebuildChain : Expr → Expr)
    (core : Expr) (fuel : Nat := 16) : MetaM (Option Simp.Result) := do
  if fuel == 0 then return none
  if let .letE n ty val body _ := core then
    return ← stepUnderLet? (rebuildChain core) n ty val fun x =>
      peelProjCore? cfg β γ g rebuildChain (body.instantiate1 x) (fuel - 1)
  if let .app (.letE n ty val fnBody _) k := core then
    return ← stepUnderLet? (rebuildChain core) n ty val fun x =>
      peelProjCore? cfg β γ g rebuildChain (mkApp (fnBody.instantiate1 x) k) (fuel - 1)
  -- 1. `core` is `Function.update f a v k` and `g v = g (f a)` definitionally.
  if let .app updFn k := core then
    if let some u := matchNondepUpdate? updFn then
      let gv := rebuildChain u.v
      let gfa := rebuildChain (mkApp u.f u.a)
      if ← defEqUnfold cfg gv gfa then
        let hEq ← mkExpectedTypeHint (← mkEqRefl gfa) (← mkEq gv gfa)
        let pf ← mkAppOptM ``UpdateSimp.apply_update_of_eq
          #[some u.α, some u.β, some γ, some u.inst, some g, some u.f, some u.a, some u.v, some k,
            some hEq]
        return some { expr := rebuildChain (mkApp u.f k), proof? := some pf }
  -- 2. `core` is `if p then tBranch else eBranch`.
  if let some it := matchIte? core then
    if cfg.reduceIteVals then
      if let some rIte ← reduceValIte? cfg core then
        let next := rebuildChain rIte.expr
        let pf₁ ← match rIte.proof? with
          | some p =>
            mkAppOptM ``congrArg #[some β, some γ, some core, some rIte.expr, some g, some p]
          | none => mkEqRefl next
        let step₁ : Simp.Result := { expr := next, proof? := some pf₁ }
        match ← peelProjCore? cfg β γ g rebuildChain rIte.expr (fuel - 1) with
        | some r₂ => return some (← composeRes (rebuildChain core) step₁ r₂)
        | none => return some step₁
    let gt := rebuildChain it.tBranch
    let ge := rebuildChain it.eBranch
    let hfun? ← withLocalDeclD `hp it.p fun hp => do
      if let some pEq ← proveBranchEqWithHyp? cfg it.p hp gt ge then
        return some (← mkLambdaFVars #[hp] pEq)
      let gtExp ← expandUnfoldDefs cfg gt
      if gtExp != gt then
        if let some rGt ← peelProjChain? cfg gtExp (fuel - 1) then
          if let some pEq2 ← proveBranchEqWithHyp? cfg it.p hp rGt.expr ge then
            let pGtRaw ← match rGt.proof? with
              | some p => pure p
              | none => mkEqRefl rGt.expr
            let pGt ← mkExpectedTypeHint pGtRaw (← mkEq gt rGt.expr)
            return some (← mkLambdaFVars #[hp] (← mkEqTrans pGt pEq2))
      return none
    if let some hfun := hfun? then
      let pf ← mkAppOptM ``UpdateSimp.apply_ite_of_eq
        #[some β, some γ, some it.p, some it.dec, some g, some it.tBranch, some it.eBranch,
          some hfun]
      return some { expr := ge, proof? := some pf }
  return none

private partial def peelProjChain? (cfg : Config) (e : Expr) (fuel : Nat := 16) :
    MetaM (Option Simp.Result) := do
  if fuel == 0 then return none
  let env ← getEnv
  let some (core0, rebuildChain) := splitProjChain? env e | return none
  let (core1, corePf?) ←
    match core0 with
    | .app fn0 k0 =>
      match ← peelApplied cfg fn0 k0 maxPeelSteps with
      | some r =>
        if r.expr != core0 && r.proof?.isNone then
          let p0 ← mkExpectedTypeHint (← mkEqRefl r.expr) (← mkEq core0 r.expr)
          pure (r.expr, some p0)
        else
          pure (r.expr, r.proof?)
      | none => pure (core0, none)
    | _ => pure (core0, none)
  unless hasUpdateOrIteHead core1 do return none
  let β ← inferType core1
  let g ← withLocalDeclD `z β fun z => mkLambdaFVars #[z] (rebuildChain z)
  let .forallE _ _ γ _ ← inferType g | return none
  if γ.hasLooseBVars then return none
  let some rCore ← peelProjCore? cfg β γ g rebuildChain core1 (fuel - 1) | return none
  let pfCore1 ← match rCore.proof? with
    | some p => pure p
    | none => mkEqRefl rCore.expr
  let pfFinal ← match corePf? with
    | none => mkExpectedTypeHint pfCore1 (← mkEq e rCore.expr)
    | some p0 =>
      let pCongr ← mkAppOptM ``congrArg #[some β, some γ, some core0, some core1, some g, some p0]
      mkExpectedTypeHint (← mkEqTrans pCongr pfCore1) (← mkEq e rCore.expr)
  return some { expr := rCore.expr, proof? := some pfFinal }

end

/-- Single `Simp.pre` step invoked inside `update_simp`. -/
private def simpPreStep (cfg : Config) (e : Expr) : SimpM Simp.Step := do
  if let some r ← peelProjChain? cfg e then
    return .visit r
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
    if let some r ← reduceValIte? cfg e then
      return .visit r
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

/-- Simplify chained/conditional `Function.update` applications and unchanged structure/map
projections without splitting `if` guards.

* `update_simp` peels `Function.update f a v k`, `(if p then Function.update f a v else g) k`,
  curried/nested map projections, and unchanged structure-field or function-valued `ite` branches
  using local hypotheses (including `h.symm` and `And`/`¬ And`), `decide`, `omega` (with
  `@[wram_arith]` unfolding), and `stride_omega`, closing goals that reduce to `rfl`.
* `update_simp [d₁, d₂, h₁]` additionally unfolds named definitions `d₁, d₂` (such as step
  functions or slab updaters) and supplies local or global hints `h₁` to the arithmetic solver.
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
