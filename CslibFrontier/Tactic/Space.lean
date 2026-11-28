/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
public import CslibFrontier.Tactic.FailureNote
public import CslibFrontier.Tactic.CertificatePreparation
public meta import Lean.Elab.Tactic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite

/-!
# Composing explicit workspace certificates

`space` proves a `ComputableInSpace` goal by the existing budget-preserving `fun_prop` rules.
`space [f, g]` first unfolds `f` and then `g` in the goal, as `unfold f g` and `polytime [f, g]`
do: every occurrence in the goal is unfolded before the search, and a name that does not occur
at its turn is an error. Every form then runs the preparation shared with `polytime`, `ppt` and
`logspace` (`Cslib.Tactic.prepareCertificateGoal`): it inlines literal `let`s in the goal and
local encoding `let`s, and adds the certificates stored in local structures as local facts.
The discharger handles reflexive bounds and sums of terms covered by the given budget. Supply
other size inequalities and iteration invariants explicitly.

A local certificate is also reused when its function is not a routine applied to the argument,
for example `h : ComputableInSpace (fun p => edge p.2 p.1.1) …` or the bit of the input at a
computed position. When the first search fails, `space` abstracts the certified expressions in
the goal's function and searches again with the same budget.

This tactic does not assert logarithmic space in the original input: the goal specifies the
encoding and budget. In particular, a Savitch callback is linear-space in the stored state,
while a separate invariant bounds that state's length by a quadratic logarithm.

During the search, `space` does not unfold a primitive encoding, a definition whose body is an
embedding `⟨fun a => …, _⟩` into `List Bool` such as `encPair`, `encList` or `encFinEnum`.
Definitions that merely name an encoding, such as `encTuple := encPair …` or
`encLab := encFinEnum Label`, still unfold. Two different primitive encodings are therefore never
unified by unfolding both: without this, matching `encPair ?e₁ ?e₂` against `encFinEnum (A × B)`
evaluates the enumeration of `A × B` until `maximum recursion depth`, and nested pair encodings
fail exponentially slowly. Nor does it unfold `decide`, which would evaluate the decision
procedure of a condition that a rule does not match. Side conditions are first tried with
reducible unfolding and then with the usual unfolding, except between the length of a word and an
arithmetic expression, where the comparison can evaluate the encodings under the length.
Without this exception, a context-form body ran out of heartbeats when trying to copy the input.

Conditions built from `∧`, `∨` and `≤`, and equalities through the canonical finite encoding
(`budget_decideAnd`, `budget_decideOr`, `budget_natLe`, `budget_decideEq_encFinite`), are tried
only when a first search without them fails: registered globally, each would be tried, and fail,
on every decidable condition. A certificate that needs them pays for the failed first search,
which on a long condition chain can cost several times a hand-written proof.

## Main definitions

* `space`: compose certificates within the goal's explicit workspace budget.
-/

public meta section

open Lean Meta Elab Tactic Turing.MultiTapeTM

/-- Whether `e`, under binders, `let`s and metadata, is an embedding `⟨_, _⟩ : α ↪ List Bool`. -/
private partial def isEncodingBody (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ b _ | .letE _ _ _ b _ => isEncodingBody b
  | e => e.isAppOfArity ``Function.Embedding.mk 4 &&
      (e.getArg! 1).isAppOfArity ``List 1 && (e.getArg! 1).appArg!.isConstOf ``Bool

/-- The unfolding predicate of `space`: the usual one, except that primitive encodings stay
folded. -/
private def spaceCanUnfold (cfg : Config) (info : ConstantInfo) : CoreM Bool := do
  if info.name == ``Decidable.decide then return false
  if let .defnInfo d := info then
    if isEncodingBody d.value then return false
  match cfg.canUnfoldPredicateConfig with
  | .default => canUnfoldDefault cfg info
  | .atMatcher => canUnfoldAtMatcher cfg info

/-- Whether `e`, the value of a budget at a point, is visibly arithmetic: a sum, a product, a
power, a logarithm or a numeral, after unfolding reducible definitions and local `let`s. -/
private def isArithmetic (e : Expr) : MetaM Bool := do
  let e ← withConfig (fun c => { c with zetaDelta := true }) (whnfR (← instantiateMVars e))
  return e.isAppOf ``HAdd.hAdd || e.isAppOf ``HMul.hMul || e.isAppOf ``HPow.hPow ||
    e.isAppOf ``Nat.log2 || e.isAppOf ``OfNat.ofNat || e.isRawNatLit

/-- Whether `e` is visibly the length of a word. -/
private def isLength (e : Expr) : MetaM Bool := do
  return (← whnfR (← instantiateMVars e)).isAppOf ``List.length

/-- Whether one of `x` and `y` is visibly a length and the other visibly arithmetic. Comparing
them with the usual unfolding can spend the heartbeat budget evaluating the encoded word. -/
private def clash (x y : Expr) : MetaM Bool := do
  return ((← isLength x) && (← isArithmetic y)) || ((← isArithmetic x) && (← isLength y))

/-- The two sides of a bound `u ≼ v`, applied to `a`. -/
private def bigOSides? (type a : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnfR (← instantiateMVars type)
  unless type.isAppOfArity ``Turing.MultiTapeTM.BigOLe 3 do return none
  return some ((mkApp (type.getArg! 1) a).headBeta, (mkApp (type.getArg! 2) a).headBeta)

/-- The side-condition discharger of `space`: a hypothesis, a reflexive bound, or a bound of a
sum of terms by a sum that contains them. Internal to `space`.

The first attempts unfold reducible definitions only. A hypothesis or reflexivity is then tried
with the usual unfolding, except between a length and an arithmetic expression: a budget in
context form, such as `fun p => (encR p.1).length + S p.2`, is not the length of the encoded
input, and deciding that by unfolding both sides evaluates the encodings. -/
syntax (name := spaceDischarge) "space_discharge" : tactic

elab_rules : tactic
  | `(tactic| space_discharge) =>
    withTheReader Meta.Context (fun ctx => { ctx with customCanUnfoldPredicate? := none }) do
      let cheap ← `(tactic| first
        | with_reducible assumption
        | with_reducible exact BigOLe.refl _
        | (refine BigOLe.of_le fun _ => ?_; (try dsimp only); omega))
      let s ← saveState
      try
        evalTactic cheap
      catch _ =>
        s.restore
        let goal ← getMainGoal
        goal.withContext do
          let target ← goal.getType
          let some α := (← whnfR (← instantiateMVars target)).getAppArgs[0]? |
            throwError "space_discharge: no side condition"
          let done ← withLocalDeclD `a α fun a => do
            let sides ← bigOSides? target a
            -- reflexivity
            let reflOk ← match sides with
              | some (u, v) => pure !(← clash u v)
              | none => pure true
            if reflOk then
              try
                let type ← whnfR (← instantiateMVars target)
                goal.assignIfDefEq (← mkAppOptM ``Turing.MultiTapeTM.BigOLe.refl
                  #[none, type.getAppArgs[1]?])
                return true
              catch _ => s.restore
            -- a hypothesis
            for decl in ← getLCtx do
              if decl.isImplementationDetail then continue
              let ok ← match sides, ← bigOSides? decl.type a with
                | some (u, v), some (u', v') => pure !((← clash u u') || (← clash v v'))
                | _, _ => pure true
              if ok then
                try
                  goal.assignIfDefEq decl.toExpr
                  return true
                catch _ => s.restore
            return false
          unless done do throwError "space_discharge: no hypothesis proves the side condition"
          replaceMainGoal []

/-- Rules that `space` adds as local hypotheses, which `fun_prop` tries after the registered rules,
when a first search without them fails. Registered, each would be tried, and fail, on every
decidable condition. -/
private def spaceFallbacks : Array Name := #[
  ``ComputableInSpace.budget_decideEq_encFinite, ``ComputableInSpace.budget_decideAnd,
  ``ComputableInSpace.budget_decideOr, ``ComputableInSpace.budget_natLe]

/-- Replace in `e` every instance `body[x := v]` of the body of the function `f`, for a bound
variable `v` in scope, by the application `f v`. -/
private partial def foldInstances (f body : Expr) (e : Expr) (depth : Nat) : Expr :=
  match (List.range depth).find? fun j => e == body.instantiate1 (.bvar j) with
  | some j => mkApp f (.bvar j)
  | none =>
    match e with
    | .app a b => .app (foldInstances f body a depth) (foldInstances f body b depth)
    | .lam n t b bi =>
      .lam n (foldInstances f body t depth) (foldInstances f body b (depth + 1)) bi
    | .forallE n t b bi =>
      .forallE n (foldInstances f body t depth) (foldInstances f body b (depth + 1)) bi
    | .letE n t v b nd =>
      .letE n (foldInstances f body t depth) (foldInstances f body v depth)
        (foldInstances f body b (depth + 1)) nd
    | .mdata d b => .mdata d (foldInstances f body b depth)
    | .proj n i b => .proj n i (foldInstances f body b depth)
    | e => e

/-- A local certificate `h : ComputableInSpace (fun x => t) …` whose function is not a function
applied to `x` itself, such as `fun p => edge p.2 p.1.1`. `fun_prop` uses a local certificate of
a variable only when the variable is applied to the argument. -/
private def compositeCertificate? (decl : LocalDecl) : MetaM (Option Expr) := do
  if decl.isImplementationDetail || decl.isLet then return none
  let type := (← instantiateMVars decl.type).consumeMData
  unless type.isAppOf ``Turing.MultiTapeTM.ComputableInSpace do return none
  let some f := type.getAppArgs[2]? | return none
  let .lam _ _ body _ := f | return none
  unless body.hasLooseBVars do return none
  if body.isApp && body.appArg! == .bvar 0 && !body.appFn!.hasLooseBVars then return none
  return some f

/-- Beta-reduce the functions of the local certificates and reduce projections of tuples in
them, so that a certificate obtained by substitution states the expression it certifies. -/
private def normalizeCertificates : TacticM Unit := withMainContext do
  let ctx ← Simp.mkContext (simpTheorems := #[]) (congrTheorems := ← getSimpCongrTheorems)
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isLet then continue
    let type ← instantiateMVars decl.type
    unless type.consumeMData.isAppOf ``Turing.MultiTapeTM.ComputableInSpace do continue
    let some f := type.consumeMData.getAppArgs[2]? | continue
    unless f.isLambda do continue
    let (f', _) ← Meta.dsimp f ctx
    if f' != f then
      liftMetaTactic1 fun goal => do
        let args := type.consumeMData.getAppArgs.set! 2 f'
        goal.replaceLocalDeclDefEq decl.fvarId (mkAppN type.consumeMData.getAppFn args)

/-- Rewrite the function `g` of a goal `ComputableInSpace g encIn encOut S`, and nothing else:
the budget `S` has to stay the budget of the local certificates. -/
private def rewriteFunction (k : Expr → MetaM Expr) : TacticM Unit :=
  liftMetaTactic1 fun goal => do
    let target := (← instantiateMVars (← goal.getType)).consumeMData
    let args := target.getAppArgs
    let some g := args[2]? | return some goal
    return some (← goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! 2 (← k g))))

/-- Abstract certified expressions in the goal's function so that `fun_prop` can use their
certificates. Run after `normalizeCertificates`. -/
private def abstractCertificates : TacticM Unit := do
  repeat
    let goal ← getMainGoal
    -- the largest certified expression first, so that it is not broken up by a part of it
    let found ← goal.withContext do
      let mut best : Option Expr := none
      for decl in ← getLCtx do
        if let some f ← compositeCertificate? decl then
          if best.all (·.sizeWithoutSharing < f.sizeWithoutSharing) then best := some f
      return best
    let some f := found | break
    let .lam _ _ body _ := f | break
    rewriteFunction fun g => pure (foldInstances f body g 0)
    let goal ← getMainGoal
    let hyps ← goal.withContext do
      (← getLCtx).foldlM (init := #[]) fun acc decl => do
        if !decl.isImplementationDetail && !decl.isLet &&
            ((← instantiateMVars decl.type).find? (· == f)).isSome then
          return acc.push decl.fvarId
        return acc
    -- without a hypothesis to generalize, the same certificate would be found again
    if hyps.isEmpty then break
    let (_, _, goal) ← goal.generalizeHyp #[{ expr := f, xName? := some `certified }] hyps
    replaceMainGoal [goal]

/-- Compose explicit space certificates within the goal's budget.

`space [f, g]` first unfolds the definitions `f` and then `g` in the goal, as `unfold f g` does;
a name that does not occur at its turn is an error. Before searching, every form also inlines
literal `let`s in the goal, replaces local encoding `let`s by their values and adds the
certificates stored in fields of local structures as local facts, as `polytime` does. -/
syntax (name := spaceTac) "space" (" [" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| space $[[$defs,*]]?) => withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``Turing.MultiTapeTM.ComputableInSpace do
      throwError "space expects a ComputableInSpace goal with an explicit budget"
    let defs := (defs.map (·.getElems)).getD #[]
    Cslib.Tactic.prepareCertificateGoal defs
    Cslib.Tactic.withFailureNote m!"space composes `@[fun_prop]` rules for `ComputableInSpace` \
        within the goal's budget. Supply a certificate for each local routine, unfold a program \
        definition with `space [f]`, and supply a nontrivial input-length allowance \
        `(fun a => (encIn a).length) ≼ S` as a hypothesis." do
      withCanUnfoldPred spaceCanUnfold do
        let funProp ← `(tactic| fun_prop (config := { maxSteps := 256 })
          (disch := space_discharge))
        let s ← saveState
        try
          evalTactic funProp
        catch _ =>
          s.restore
          -- local certificates of composite expressions, then the rules held back
          normalizeCertificates
          let composite ← withMainContext do
            (← getLCtx).anyM fun decl => return (← compositeCertificate? decl).isSome
          if composite then
            abstractCertificates
            let s' ← saveState
            try
              evalTactic funProp
              return
            catch _ => s'.restore
          for n in spaceFallbacks do
            evalTactic (← `(tactic| have := @$(mkCIdent n)))
          evalTactic funProp

end
