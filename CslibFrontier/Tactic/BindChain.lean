/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Norm
public meta import Lean.Elab.Tactic

/-!
# Shared normalization and reordering of probabilistic bind chains

The proof-producing core of `pmf_swap`, `pmf_hoist`, and `peel_binds`. It normalizes monadic
notation and nested binds without unfolding named programs, matches independent samples by their
distributions, and constructs the equality moving a selected sample to the front. Custom samplers
supply their commutation lemmas; relation-specific peeling and support witnesses stay in the
calling tactic.
-/

public meta section

namespace Cslib.Tactic.BindChain

open Lean Meta Elab Tactic

/-- Head-beta-reduce and substitute top-level `let` bindings (and local `let` `fvar`s of
`PMF` type) at the root of `e` (definitionally equal by `beta`/`zeta`/`zetaDelta`). -/
partial def stripSpineLetsM (e : Expr) : MetaM Expr := do
  match e.cleanupAnnotations.headBeta with
  | .letE _ _ val body _ => stripSpineLetsM (body.instantiate1 val)
  | .fvar fvarId =>
    let decl ← fvarId.getDecl
    if let some val := decl.value? then
      if (← whnfR decl.type).isAppOf ``PMF then
        return ← stripSpineLetsM val
    return e.cleanupAnnotations.headBeta
  | e' => return e'

/-- Cast a proof `h : a' = b'` to `a = b` when `a ≡ a'` and `b ≡ b'` definitionally. -/
def castEqProof (a b h : Expr) : MetaM Expr := do
  mkExpectedTypeHint h (← mkEq a b)

/-- Compose optional equality proofs `e₀ = e₁` and `e₁ = e₂`. -/
def chainEqOpt (e₀ e₂ : Expr) (h₁? h₂? : Option Expr) : MetaM (Option Expr) := do
  match h₁?, h₂? with
  | none, none => return none
  | some h₁, none => return some (← castEqProof e₀ e₂ h₁)
  | none, some h₂ => return some (← castEqProof e₀ e₂ h₂)
  | some h₁, some h₂ => return some (← castEqProof e₀ e₂ (← mkEqTrans h₁ h₂))

/-- Normalize only the outer head of a `PMF` expression into `PMF.bind`
without unfolding named user definitions or traversing continuation bodies. Keep a source map
intact with `preserveMap` so its enclosing bind can apply `PMF.bind_map` directly. -/
partial def normalizeBindHead (e : Expr) (preserveMap := false) : MetaM (Expr × Option Expr) := do
  let e0 ← stripSpineLetsM e
  if e0.isAppOfArity ``Bind.bind 6 then
    let args := e0.getAppArgs
    if args[0]!.cleanupAnnotations.isConstOf ``PMF then
      let eBind ← mkAppM ``PMF.bind #[args[4]!, args[5]!]
      let (eFinal, h?) ← normalizeBindHead eBind preserveMap
      let h? ← match h? with
        | some h => pure (some (← castEqProof e eFinal h))
        | none =>
          if e == eFinal then pure none
          else pure (some (← castEqProof e eFinal (← mkEqRefl eFinal)))
      return (eFinal, h?)
  if e0.isAppOfArity ``Pure.pure 4 then
    let args := e0.getAppArgs
    if args[0]!.cleanupAnnotations.isConstOf ``PMF then
      let result ← mkAppM ``PMF.pure #[args[3]!]
      return (result, some (← castEqProof e result (← mkEqRefl result)))
  if e0.isAppOfArity ``Functor.map 6 then
    let args := e0.getAppArgs
    if args[0]!.cleanupAnnotations.isConstOf ``PMF then
      let mapped ← mkAppM ``PMF.map #[args[4]!, args[5]!]
      let (result, h?) ← normalizeBindHead mapped preserveMap
      let h ← match h? with
        | some h => pure h
        | none => mkEqRefl result
      return (result, some (← castEqProof e result h))
  if !preserveMap && e0.isAppOfArity ``PMF.map 4 then
    let args := e0.getAppArgs
    let g := args[2]!
    let name := if let .lam n .. := g then n else `x
    let cont ← withLocalDeclD name args[0]! fun x => do
      mkLambdaFVars #[x] (← mkAppM ``PMF.pure #[g.beta #[x]])
    let bound ← mkAppM ``PMF.bind #[args[3]!, cont]
    let (result, h?) ← normalizeBindHead bound preserveMap
    let h ← match h? with
      | some h => pure h
      | none => mkEqRefl result
    return (result, some (← castEqProof e result h))
  if e0.isAppOfArity ``Cslib.ProbComp.eval 2 then
    let prog0 ← stripSpineLetsM (e0.getAppArgs[1]!)
    if prog0.isAppOfArity ``Bind.bind 6 then
      let pargs := prog0.getAppArgs
      let m := pargs[4]!
      let k := pargs[5]!
      let hStep ← mkAppM ``Cslib.ProbComp.eval_bind #[m, k]
      let xName := match k.cleanupAnnotations with
        | .lam n _ _ _ => n
        | _ => `x
      let α₀ := pargs[2]!
      let evalM ← mkAppM ``Cslib.ProbComp.eval #[m]
      let newLam ← withLocalDecl xName .default α₀ fun x => do
        let kx := (mkApp k x).headBeta
        let evalKx ← mkAppM ``Cslib.ProbComp.eval #[kx]
        mkLambdaFVars #[x] evalKx
      let rhs ← mkAppM ``PMF.bind #[evalM, newLam]
      let hStep ← castEqProof e rhs hStep
      let (eFinal, hRest?) ← normalizeBindHead rhs preserveMap
      return (eFinal, ← chainEqOpt e eFinal (some hStep) hRest?)
    let hEval? ← if prog0.isAppOfArity ``Functor.map 6 then do
        let args := prog0.getAppArgs
        pure (some (← mkAppM ``Cslib.ProbComp.eval_map #[args[4]!, args[5]!]))
      else if prog0.isAppOfArity ``Pure.pure 4 then
        pure (some (← mkAppM ``Cslib.ProbComp.eval_pure #[prog0.getAppArgs[3]!]))
      else pure none
    if let some hEval := hEval? then
      let rhs := (← inferType hEval).getAppArgs[2]!
      let (result, hRest?) ← normalizeBindHead rhs preserveMap
      return (result, ← chainEqOpt e result (some hEval) hRest?)
    return (e, none)
  if e0.isAppOfArity ``PMF.bind 4 then
    let args := e0.getAppArgs
    let p := args[2]!
    let f := args[3]!
    let (p', hp?) ← normalizeBindHead p (preserveMap := true)
    let mut cur := e0
    let mut hCur? : Option Expr := none
    if let some hp := hp? then
      let cur' ← mkAppM ``PMF.bind #[p', f]
      let hCongr ← mkCongrArg (mkApp2 e0.getAppFn args[0]! args[1]!) hp
      let hStep ← mkCongrFun hCongr f
      hCur? := some (← castEqProof e cur' hStep)
      cur := cur'
    let p0 ← stripSpineLetsM p'
    if p0.isAppOfArity ``PMF.bind 4 then
      let pargs := p0.getAppArgs
      let q := pargs[2]!
      let g := pargs[3]!
      let hAssoc ← mkAppM ``PMF.bind_bind #[q, g, f]
      -- Preserve `g`'s user binder name in the reassociated lambda.
      let xName := match g.cleanupAnnotations with
        | .lam n _ _ _ => n
        | _ => `x
      let α₀ := pargs[0]!
      let newLam ← withLocalDecl xName .default α₀ fun x => do
        let gx := (mkApp g x).headBeta
        let inner ← mkAppM ``PMF.bind #[gx, f]
        mkLambdaFVars #[x] inner
      let rhs ← mkAppM ``PMF.bind #[q, newLam]
      let hAssoc ← castEqProof cur rhs hAssoc
      let hTot? ← chainEqOpt e rhs hCur? (some hAssoc)
      let (eFinal, hRest?) ← normalizeBindHead rhs preserveMap
      return (eFinal, ← chainEqOpt e eFinal hTot? hRest?)
    if p0.isAppOfArity ``PMF.pure 2 then
      let a := p0.getAppArgs[1]!
      let hPure ← mkAppM ``PMF.pure_bind #[a, f]
      let rhs := (mkApp f a).headBeta
      let hPure ← castEqProof cur rhs hPure
      let hTot? ← chainEqOpt e rhs hCur? (some hPure)
      let (eFinal, hRest?) ← normalizeBindHead rhs preserveMap
      return (eFinal, ← chainEqOpt e eFinal hTot? hRest?)
    if p0.isAppOfArity ``PMF.map 4 then
      let margs := p0.getAppArgs
      let α₀ := margs[0]!
      let g := margs[2]!
      let q := margs[3]!
      let hMap ← mkAppM ``PMF.bind_map #[q, g, f]
      let xName := match g.cleanupAnnotations with
        | .lam n _ _ _ => n
        | _ => match f.cleanupAnnotations with
          | .lam n _ _ _ => n
          | _ => `x
      let compName := if xName.isAnonymous then `x else xName
      let newLam ← withLocalDecl compName .default α₀ fun x => do
        let gx := (mkApp g x).headBeta
        let fgx := (mkApp f gx).headBeta
        mkLambdaFVars #[x] fgx
      let rhs ← mkAppM ``PMF.bind #[q, newLam]
      let hMap ← castEqProof cur rhs hMap
      let hTot? ← chainEqOpt e rhs hCur? (some hMap)
      let (eFinal, hRest?) ← normalizeBindHead rhs preserveMap
      return (eFinal, ← chainEqOpt e eFinal hTot? hRest?)
    if cur != e && hCur?.isNone then
      return (cur, some (← castEqProof e cur (← mkEqRefl cur)))
    return (cur, hCur?)
  if e0 != e then
    return (e0, some (← castEqProof e e0 (← mkEqRefl e0)))
  return (e, none)

/-- The head of an application, for a cheap test that an expression may be a sampler. -/
inductive HeadKey where
  /-- A constant. -/
  | const (n : Name)
  /-- A local variable. -/
  | fvar (x : FVarId)
  deriving BEq

/-- The head of the application `e`, if it is a constant or a local variable. -/
private def headKey? (e : Expr) : Option HeadKey :=
  match e.getAppFn with
  | .const n _ => some (.const n)
  | .fvar x => some (.fvar x)
  | _ => none

/-- A commutation lemma `μ.bind (fun b => F (k b)) = F (fun a => μ.bind fun b => k b a)`, which
lets an independent sample of any `μ` move past the sampler `F`. -/
structure Comm where
  /-- The lemma, with its metavariables abstracted. -/
  thm : AbstractMVarsResult
  /-- The lemma as written, for messages. -/
  stx : Syntax
  /-- The head of the sampler `F`. -/
  key : HeadKey
  /-- The number of arguments of the sampler `F`. -/
  arity : Nat

/-- The sampler rules shared by matching and proof-producing reordering. -/
structure Context where
  /-- Rules commuting independent distributions with custom samplers. -/
  comms : Array Comm := #[]
  /-- Optional rule for commuting two custom samplers `F`, `G`, with continuation `k`.
  Its result proves `F (fun a => G (k a)) = G (fun b => F (fun a => k a b))`. -/
  swapSamplers? : Option (Expr → Expr → Expr → MetaM Expr) := none

/-- The proof of the commutation lemma `c` applied to fresh metavariables, its two sides, and the
metavariables. -/
private def Comm.inst (c : Comm) : MetaM (Expr × Expr × Expr × Array Expr) := do
  let (ms, _, pf) ← openAbstractMVarsResult c.thm
  let (xs, _, ty) ← forallMetaTelescopeReducing (← instantiateMVars (← inferType pf))
  let some (_, lhs, rhs) := (← instantiateMVars ty).cleanupAnnotations.eq?
    | throwError "pmf_swap: {c.stx} is not an equation"
  return (mkAppN pf xs, lhs, rhs, ms ++ xs)

/-- The sampler `F` of a commutation lemma with sides `lhs` and `rhs`, of the form
`μ.bind (fun b => F (k b)) = F (fun a => μ.bind fun b => k b a)`. -/
private def samplerOf? (lhs rhs : Expr) : Option Expr := do
  let some (_, _, _, .lam _ _ body _) := lhs.app4? ``PMF.bind | none
  let .app F _ := body | none
  if F.hasLooseBVars then none
  let .app F' (.lam ..) := rhs | none
  if F' != F then none
  if F.getAppFn.isMVar then none
  return F

/-- Check the shape of a sampler commutation lemma, retaining its syntax for diagnostics. -/
def commOfExpr (pf : Expr) (stx : Syntax) : MetaM Comm := do
  let thm ← abstractMVars pf
  let c : Comm := { thm, stx, key := .const .anonymous, arity := 0 }
  let shape : Option (HeadKey × Nat) ← withNewMCtxDepth do
    let (_, lhs, rhs, _) ← c.inst
    return (samplerOf? lhs rhs).bind fun F => (headKey? F).map (·, F.getAppNumArgs)
  let some (key, arity) := shape
    | throwErrorAt stx "pmf_swap: {stx} is not a commutation lemma for a sampler `F`.\n\
        The expected form is\n  μ.bind (fun b => F (k b)) = F (fun a => μ.bind fun b => k b a)\n\
        for every distribution `μ`."
  return { c with key, arity }

/-- Elaborate a commutation lemma supplied by a tactic caller. -/
def elabComm (stx : Syntax) : TacticM Comm := do
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <|
    Term.withoutModifyingElabMetaStateWithInfo <| withRef stx <| Term.withoutErrToSorry do
      commOfExpr (← Term.elabTerm stx none) stx

/-- Assign the instance arguments among the metavariables `ms` by type class synthesis. -/
private def synthInstances (ms : Array Expr) : MetaM Unit := do
  for m in ms do
    let m ← instantiateMVars m
    if let .mvar id := m then
      if (← isClass? (← inferType m)).isSome then
        id.assign (← synthInstance (← inferType m))

/-- A distribution or a sampler: the head `head` of a sample, and `comm?` when it is a sampler
`head`, which is applied to the continuation, with the commutation lemma `comm?`. -/
structure Pat where
  /-- The distribution, or the sampler. -/
  head : Expr
  /-- The commutation lemma of a sampler. -/
  comm? : Option Comm := none

/-- A step of a chain of samples: the distribution or sampler `head` and the continuation `cont`,
so that the chain is `head.bind cont`, or `head cont` for a sampler. -/
structure Sample extends Pat where
  /-- The rest of the chain, as a function of the sample. -/
  cont : Expr

/-- Recognize a custom sampler by a supplied commutation rule. -/
def samplerPat? (ctx : Context) (F : Expr) : MetaM (Option Pat) := do
  if ctx.comms.isEmpty then return none
  let some key := headKey? F | return none
  for c in ctx.comms do
    unless c.key == key && c.arity == F.getAppNumArgs do continue
    let ok ← withNewMCtxDepth do
      let (_, _, rhs, _) ← c.inst
      let .app F' _ := rhs | return false
      withReducible <| isDefEq F' F
    if ok then return some { head := F, comm? := some c }
  return none

/-- `e` as an application `F k` of a recognized sampler `F`. -/
private def customSample? (ctx : Context) (e : Expr) : MetaM (Option Sample) := do
  let .app F k := e | return none
  let some p ← samplerPat? ctx F | return none
  return some { p with cont := k }

/-- The first sample of `e`: `p.bind f` samples `p` and continues with `f`, `p.map g`, which
is `p.bind (pure ∘ g)`, samples `p` and returns `g` of the sample, and `F k`, for the sampler `F`
of one of the commutation lemmas `comms`, samples `F` and continues with `k`. -/
def sample? (ctx : Context) (e : Expr) : MetaM (Option Sample) := do
  match_expr e with
  | PMF.bind _ _ p f => return some { head := p, cont := f }
  | PMF.map α _ g p =>
    let n := if let .lam m .. := g then m else `x
    let cont ← withLocalDeclD n α fun x => do
      mkLambdaFVars #[x] (← mkAppM ``PMF.pure #[g.beta #[x]])
    return some { head := p, cont }
  | _ => customSample? ctx e

/-- Run `k x b` with a new variable `x` for the argument of the function `f`, where `b` is `f x`
reduced. -/
def withBody {α : Type} (f : Expr) (k : Expr → Expr → MetaM α) : MetaM α := do
  let .forallE n dom _ _ ← whnf (← inferType f)
    | throwError "pmf_swap: expected a continuation, got{indentExpr f}"
  let n := if let .lam m .. := f then m else n
  withLocalDeclD n dom fun x => k x (f.beta #[x])

/-- The type of outcomes `α` of a distribution `p : PMF α`. -/
def outcomeType (p : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType p)
  let .app (.const ``PMF _) α := ty
    | throwError "pmf_swap: expected a distribution `PMF α`, got{indentExpr p}\n\
        of type{indentExpr ty}"
  return α

/-- The type of the samples of `p`: the outcomes of a distribution, or the argument of the
continuation of a sampler. -/
private def Pat.sampleType (p : Pat) : MetaM Expr := do
  if p.comm?.isNone then return ← outcomeType p.head
  let .forallE _ kTy _ _ ← whnf (← inferType p.head)
    | throwError "pmf_swap: internal error: a sampler is not a function"
  let .forallE _ α _ _ ← whnf kTy
    | throwError "pmf_swap: internal error: a continuation is not a function"
  return α

/-- The chain that samples `p` and continues with `k`. -/
private def Pat.front (p : Pat) (k : Expr) : MetaM Expr :=
  if p.comm?.isSome then return mkApp p.head k else mkAppM ``PMF.bind #[p.head, k]

/-- `p.front f = p.front g` from `h : f = g`. -/
def stepCongr (p : Pat) (f h : Expr) : MetaM Expr := do
  let F ← withLocalDeclD `k (← inferType f) fun k => do mkLambdaFVars #[k] (← p.front k)
  mkCongrArg F h

/-- Whether `p` and `q` sample the same distribution, or the same sampler, up to reducible
unfolding. -/
private def sameHead (p q : Pat) : MetaM Bool := do
  if p.comm?.isSome != q.comm?.isSome then return false
  withNewMCtxDepth <| withReducible <| isDefEq p.head q.head

/-- The depths at which the chain `e` samples `q`, up to reducible unfolding. A sample whose
distribution mentions an earlier sample is not equal to `q`, which is closed. The search for a
custom sampler stops at the first custom sampler unless the context supplies their commutation
rule. Heads are normalized as the search descends into the chain. -/
partial def findDepths (ctx : Context) (q : Pat) (e : Expr) (depth : Nat := 0) :
    MetaM (Array Nat) := do
  let (head, _) ← normalizeBindHead e
  let some s ← sample? ctx head | return #[]
  let here ← sameHead s.toPat q
  if q.comm?.isSome && s.comm?.isSome && ctx.swapSamplers?.isNone then
    return if here then #[depth] else #[]
  let rest ← withBody s.cont fun _ body => findDepths ctx q body (depth + 1)
  return if here then #[depth] ++ rest else rest

/-- The first depth at which the chain `e` samples `q`, assigning the metavariables of `q`.
The same sampler boundaries as `findDepths` apply. -/
partial def firstDepth? (ctx : Context) (q : Pat) (e : Expr) (depth : Nat := 0) :
    MetaM (Option Nat) := do
  let some s ← sample? ctx e | return none
  if s.comm?.isSome == q.comm?.isSome then
    if ← withReducible <| isDefEq s.head q.head then return some depth
  if q.comm?.isSome && s.comm?.isSome && ctx.swapSamplers?.isNone then return none
  withBody s.cont fun _ body => firstDepth? ctx q body (depth + 1)

/-- A proof that the commutation lemma of `c` gives `lhs = rhs`. -/
private def commProof (c : Comm) (lhs rhs : Expr) : MetaM Expr := do
  let (pf, l, r, ms) ← c.inst
  unless ← isDefEq l lhs <&&> isDefEq r rhs do
    throwError "pmf_swap: {c.stx} does not prove{indentExpr (← mkEq lhs rhs)}"
  synthInstances ms
  let pf ← instantiateMVars pf
  if pf.hasExprMVar then
    throwError "pmf_swap: {c.stx} does not determine all of its arguments in{indentExpr lhs}"
  return pf

/-- A proof of `lhs = rhs`, where `lhs` samples `p` and then `q`, and `rhs` samples `q` and then
`p`, with the continuation `G` of both: `PMF.bind_comm` for two distributions, and the commutation
lemma for a sampler. -/
private def swapProof (ctx : Context) (p q : Pat) (G lhs rhs : Expr) : MetaM Expr :=
  match p.comm?, q.comm? with
  | none, none => mkAppM ``PMF.bind_comm #[p.head, q.head, G]
  | none, some c => commProof c lhs rhs
  | some c, none => do mkEqSymm (← commProof c rhs lhs)
  | some _, some _ => do
    let some swap := ctx.swapSamplers?
      | throwError "pmf_swap: no commutation rule for two custom samplers"
    swap p.head q.head G

/-- Move the sample at depth `k` of the chain `e`, which samples `q` independently of the earlier
samples, to the front. Normalize only the path to that sample, preserving the remaining
continuation. Returns `q.front g` and a proof of `e = q.front g`. -/
partial def hoistAt (ctx : Context) (q : Pat) (e : Expr) (k : Nat) :
    MetaM (Expr × Expr) := do
  let (head, hNorm?) ← normalizeBindHead e
  let (result, hMove) ← match k with
    | 0 => do
      let some s ← sample? ctx head | throwError "pmf_swap: internal error: no sample to move"
      let result ← q.front s.cont
      return (result, ← castEqProof head result (← mkEqRefl head))
    | k + 1 => do
      let some s ← sample? ctx head | throwError "pmf_swap: internal error: no sample to move"
      let p := s.toPat
      -- Inside the continuation, `fun x => q.front (G x)`.
      let (hcont, G) ← withBody s.cont fun x body => do
        let (inner, h) ← hoistAt ctx q body k
        return (← mkLambdaFVars #[x] h, ← mkLambdaFVars #[x] inner.appArg!)
      let h₁ ← stepCongr p s.cont (← mkFunExt hcont)
      let .forallE xName xTy _ _ ← whnf (← inferType s.cont)
        | throwError "pmf_swap: internal error: continuation is not a function"
      let xName := if let .lam m .. := s.cont then m else xName
      let yName ← withBody s.cont fun x _ => do
        return if let .lam n .. := G.beta #[x] then n else `y
      let lhs ← p.front (← withLocalDeclD xName xTy fun x => do
        mkLambdaFVars #[x] (← q.front (G.beta #[x])))
      let result ← q.front (← withLocalDeclD yName (← q.sampleType) fun y => do
        let pCont ← withLocalDeclD xName xTy fun x => do mkLambdaFVars #[x] (G.beta #[x, y])
        mkLambdaFVars #[y] (← p.front pCont))
      -- `p` then `q` is `q` then `p`.
      let h₂ ← swapProof ctx p q G lhs result
      return (result, ← castEqProof head result (← mkEqTrans h₁ h₂))
  let proof ← match hNorm? with
    | some h => mkEqTrans h hMove
    | none => pure hMove
  return (result, ← castEqProof e result proof)

/-- Normalize a complete visible sampling chain, preserving binder names and returning its
equality proof. Named program bodies and expressions inside terminal results stay opaque. -/
partial def normalize (ctx : Context) (e : Expr) : MetaM (Expr × Option Expr) := do
  let (head, hHead?) ← normalizeBindHead e
  let some s ← sample? ctx head | return (head, hHead?)
  let cont? : Option (Expr × Expr) ← withBody s.cont fun x body => do
    let (body', h?) ← normalize ctx body
    let some h := h? | return none
    return some (← mkLambdaFVars #[x] body', ← mkFunExt (← mkLambdaFVars #[x] h))
  let some (cont, hCont) := cont? | return (head, hHead?)
  let result ← s.toPat.front cont
  let hStep ← castEqProof head result (← stepCongr s.toPat s.cont hCont)
  return (result, ← chainEqOpt e result hHead? (some hStep))

end Cslib.Tactic.BindChain

end
