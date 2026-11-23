/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, beside `Mathlib/Tactic/Positivity/Core.lean`)

public import CslibFrontier.Init
public import Mathlib.Tactic.Positivity.Core
public meta import Lean.Elab.Tactic.Omega

/-!
# Sign lemmas for `positivity`

Mathlib's `positivity` proves `0 < e`, `0 ≤ e` and `e ≠ 0` by recursion on `e`, through an
extension written for each operation. A definition it has no extension for, such as a rate or a
spectral expansion defined in this library, is an atom to it. The lemma stating the sign of such a
definition then has to be passed by hand into every monotonicity lemma, or stated as a hypothesis
before each `positivity`, `gcongr`, `grw` or `field_simp` that needs it.

The attribute `@[positivity_lemma]` registers such a lemma with `positivity`. No extension is
written for the definition: the single extension `Mathlib.Meta.Positivity.evalSignLemma` looks each
subexpression up among the registered lemmas.

```lean
@[positivity_lemma]
theorem rate_pos (k : ℕ) : 0 < rate k := …

example (k : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 < (rate k + x) / rate k ^ 2 := by positivity
example (k : ℕ) (a b : ℝ) (h : a ≤ b) : rate k * a ≤ rate k * b := by gcongr
example (k : ℕ) (x : ℝ) : x / rate k * rate k = x := by field_simp
```

A registered lemma concludes `0 < e` or `0 ≤ e`, and `e` determines all of its data and type
arguments: a lemma with a non-propositional argument that `e` does not determine is rejected.
Typeclass instances whose types `e` determines are synthesized, and propositional hypotheses whose
types `e` determines are discharged from local hypotheses, by recursive `positivity`, or, for
linear comparisons over `ℕ`, `ℤ` and `Fin`, by `omega`. `linarith` and `nlinarith` do not call
`positivity` on the atoms of a goal, so they still need the fact stated.

## Main definitions

* `positivity_lemma`: the attribute registering a sign lemma.
* `Mathlib.Meta.Positivity.evalSignLemma`: the `positivity` extension applying the registered
  lemmas.
-/

public meta section

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Splits `z < e` or `z ≤ e` into whether the inequality is strict, the type, `z` and `e`. -/
private def signStatement? (t : Expr) : Option (Bool × Expr × Expr × Expr) :=
  match_expr t.consumeMData with
  | LT.lt α _ z e => some (true, α, z, e)
  | LE.le α _ z e => some (false, α, z, e)
  | _ => none

/-- The registered sign lemmas, indexed by the expression whose sign each one states. -/
private initialize signLemmaExt :
    SimpleScopedEnvExtension (Array DiscrTree.Key × Name) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun lemmas (keys, declName) => lemmas.insertKeyValue keys declName
    initial := {}
  }

/-- Option key tracking recursive `positivity` depth when discharging sign-lemma premises. -/
private def signLemmaDepthKey : Name := `_positivityLemmaDepth

/-- Maximum recursive `positivity` depth for sign-lemma side conditions, bounding cyclic
registrations while allowing nested sign lemmas. -/
private def maxSignLemmaDepth : Nat := 3

/-- Whether `type` is a linear arithmetic proposition over `ℕ`, `ℤ` or `Fin` handled by `omega`. -/
private partial def isOmegaGoal (type : Expr) : Bool :=
  let isNum (α : Expr) : Bool :=
    α.isConstOf ``Nat || α.isConstOf ``Int || α.isAppOfArity ``Fin 1
  match_expr type.consumeMData with
  | Eq α _ _ => isNum α
  | Ne α _ _ => isNum α
  | LE.le α _ _ _ => isNum α
  | LT.lt α _ _ _ => isNum α
  | GE.ge α _ _ _ => isNum α
  | GT.gt α _ _ _ => isNum α
  | Dvd.dvd α _ _ _ => isNum α
  | Not p => isOmegaGoal p
  | And p q => isOmegaGoal p || isOmegaGoal q
  | Or p q => isOmegaGoal p || isOmegaGoal q
  | _ => false

/-- Attempts to close `g` by recursive `positivity`, bounded by `maxSignLemmaDepth`. -/
private def solveByPositivity (g : MVarId) : MetaM Bool := do
  let opts ← getOptions
  let depth := opts.get signLemmaDepthKey (0 : Nat)
  if depth >= maxSignLemmaDepth then
    return false
  let saved ← saveState
  try
    withOptions (fun o => o.set signLemmaDepthKey (depth + 1)) do
      positivity g
    return true
  catch _ =>
    saved.restore
    return false

/-- Attempts to close an arithmetic side goal `g` with `omega`. -/
private def solveByOmega (g : MVarId) : MetaM Bool := do
  let saved ← saveState
  try
    let some g ← g.falseOrByContra | return true
    g.withContext do
      let hyps := (← getLocalHyps).toList
      Elab.Tactic.Omega.omega hyps g
    return true
  catch _ =>
    saved.restore
    return false

/-- Discharges a determined propositional premise `g` of type `type`, returning `some true` when
`omega` was used, `some false` when `assumption` or `positivity` proved it, and `none` on
failure. -/
private def dischargeSideGoal (g : MVarId) (type : Expr) : MetaM (Option Bool) := do
  if ← g.assumptionCore then
    return some false
  if ← solveByPositivity g then
    return some false
  if isOmegaGoal type then
    if ← solveByOmega g then
      return some true
  return none

/-- Proves the sign of `e : α` by the lemma `declName`, whose data and type arguments are
determined by unifying the expression in its conclusion with `e`, synthesizing determined instances
and discharging determined propositional side conditions. Returns the proof and whether the sign is
strict. -/
private def applySignLemma (α e : Expr) (declName : Name) : MetaM (Expr × Bool) := do
  -- The new depth keeps the unification from assigning metavariables of `e`.
  let (proof, strict, usedOmega) ← withNewMCtxDepth do
    let lem ← mkConstWithFreshMVarLevels declName
    let (args, binders, concl) ← forallMetaTelescope (← inferType lem)
    let some (strict, β, _, e') := signStatement? concl
      | throwError "{.ofConstName declName} does not conclude `0 < e` or `0 ≤ e`"
    unless ← withReducibleAndInstances (isDefEq α β <&&> isDefEq e e') do
      throwError "{.ofConstName declName} does not state the sign of{indentExpr e}"
    let undetermined (type : Expr) : MetaM Unit :=
      throwError "the argument of {.ofConstName declName} of type{indentExpr type}\n\
        is not determined by{indentExpr e}"
    for arg in args, binder in binders do
      let goal := arg.mvarId!
      if ← goal.isAssigned then continue
      let type ← instantiateMVars (← goal.getType)
      if !binder.isInstImplicit && !(← isProp type) then
        undetermined type
    for arg in args, binder in binders do
      let goal := arg.mvarId!
      if ← goal.isAssigned then continue
      if binder.isInstImplicit then
        let type ← instantiateMVars (← goal.getType)
        if type.hasMVar then undetermined type
        goal.assign (← synthInstance type)
    let mut usedOmega := false
    for arg in args, binder in binders do
      let goal := arg.mvarId!
      if ← goal.isAssigned then continue
      if !binder.isInstImplicit then
        let type ← instantiateMVars (← goal.getType)
        if type.hasMVar then undetermined type
        match ← dischargeSideGoal goal type with
        | some byOmega => usedOmega := usedOmega || byOmega
        | none =>
          throwError "could not prove the side condition{indentExpr type}\n\
            of {.ofConstName declName}"
    let proof ← instantiateMVars (mkAppN lem args)
    if proof.hasMVar then
      throwError "{.ofConstName declName} is not fully determined by{indentExpr e}"
    return (proof, strict, usedOmega)
  if usedOmega then
    recordExtraModUse (isMeta := false) `Init.Omega
  return (proof, strict)

/-- The `positivity` extension for the lemmas registered with `@[positivity_lemma]`. `positivity`
calls it on every subexpression it visits, and it tries the registered lemmas whose expression
matches. -/
@[positivity _]
def evalSignLemma : PositivityExt where
  eval {_ α} zα pα? e :=
    match pα? with
    | none => pure .none
    | some pα => do
      let mut result : Strictness zα e pα := .none
      for declName in ← (signLemmaExt.getState (← getEnv)).getMatch e do
        result ← orElse result do
          let (proof, strict) ← applySignLemma α e declName
          return if strict then .positive proof else .nonnegative proof
      return result

/-- Checks that `positivity` can use `declName` as a sign lemma, by applying it to its own
statement, and returns the index keys of the expression whose sign it states. -/
private def signLemmaKeys (declName : Name) : MetaM (Array DiscrTree.Key) := do
  let type := (← getConstInfo declName).type
  forallTelescope type fun _ concl => do
    let badStatement : MessageData := m!"`@[positivity_lemma]` needs a lemma concluding `0 < e` \
      or `0 ≤ e`, but {.ofConstName declName} concludes{indentExpr concl}"
    let some (_, α, z, e) := signStatement? concl | throwError badStatement
    unless z.nat? == some 0 do throwError badStatement
    try
      discard <| applySignLemma α e declName
    catch ex =>
      throwError "`@[positivity_lemma]`: {ex.toMessageData}"
  let (_, _, concl) ← forallMetaTelescope type
  let some (_, _, _, e) := signStatement? concl | unreachable!
  let keys ← DiscrTree.mkPath e
  if keys[0]? == some .star then
    throwError "`@[positivity_lemma]`: {.ofConstName declName} states the sign of a variable, \
      which `positivity` would have to try on every expression"
  return keys

/-- `@[positivity_lemma]` registers a lemma concluding `0 < e` or `0 ≤ e` with the `positivity`
tactic. `positivity` then proves that statement, and `e ≠ 0` from `0 < e`, wherever an instance of
`e` occurs in a goal: also in the side goals of `gcongr` and `grw`, in the side conditions of
`field_simp`, and under casts and the other operations `positivity` knows.

The expression `e` must determine every data and type argument of the lemma: a lemma with a
non-propositional argument that `e` does not determine is rejected, as is one whose `e` is a
variable. Typeclass instances determined by `e` are synthesized, and propositional hypotheses
determined by `e` are discharged from local hypotheses, by recursive `positivity`, or by `omega` on
linear `ℕ`, `ℤ` and `Fin` goals. -/
syntax (name := positivityLemma) "positivity_lemma" : attr

initialize registerBuiltinAttribute {
  name := `positivityLemma
  descr := "registers a sign lemma with the `positivity` tactic"
  applicationTime := .afterTypeChecking
  add := fun declName _ kind => do
    let keys ← (signLemmaKeys declName).run'
    signLemmaExt.add (keys, declName) kind
}

end Mathlib.Meta.Positivity
