/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Tactic.FunProp

/-!
# Preparing goals for certificate composition

The efficiency tactics `polytime`, `ppt`, `logspace` and `space` share this preparation before
proof search: unfold only the program names supplied by the caller, inline literal `let`s in the
goal and local encoding `let`s, and expose the `fun_prop` certificates stored in local structures
and conjunctions. Program values and resource invariants stay explicit; preparation does not add
a computation rule or change a bound.

## Main definitions

* `Cslib.Tactic.prepareCertificateGoal`: prepare a certificate goal and its local facts.
-/

public section

namespace Cslib.Tactic

open Lean Meta in
/-- Whether a type is an encoding `α ↪ List Bool`, looking through reducible aliases. -/
private meta def isEncodingType (type : Expr) : MetaM Bool := do
  let type ← whnfR (← instantiateMVars type)
  unless type.isAppOfArity ``Function.Embedding 2 do return false
  return (← whnfR type.getAppArgs[1]!).isAppOfArity ``List 1

open Lean Meta Elab Tactic in
/-- Replace local encoding `let`s by their values in the goal and in the hypotheses that mention
them, so that the spelled-out encodings of certificates and rules match. Other local definitions
keep their names. -/
private meta def unfoldEncodingLets : TacticM Unit := withMainContext do
  let mut lets : Array FVarId := #[]
  for decl in ← getLCtx do
    if decl.isLet && !decl.isImplementationDetail && (← isEncodingType decl.type) then
      lets := lets.push decl.fvarId
  if lets.isEmpty then return
  let mut goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  if target.hasAnyFVar lets.contains then
    goal ← goal.replaceTargetDefEq (← zetaDeltaFVars target lets)
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isLet then continue
    let type ← instantiateMVars decl.type
    if type.hasAnyFVar lets.contains then
      goal ← goal.replaceLocalDeclDefEq decl.fvarId (← zetaDeltaFVars type lets)
  replaceMainGoal [goal]

open Lean Meta in
/-- Whether a proposition, under its universal binders, is a `fun_prop` function property such
as a polynomial-time or PPT certificate. -/
private meta def isCertificateFact (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun _ body => do
    return (← Mathlib.Meta.FunProp.getFunProp? (← instantiateMVars body)).isSome

open Lean Meta in
/-- The certificates stored in the fields of a structure value or proof, such as the `IsPPTOn`
fields of a scheme or of an admissibility structure, searching nested structures to `depth`. -/
private meta def fieldCertificates : Expr → Nat → MetaM (Array Expr)
  | _, 0 => return #[]
  | e, depth + 1 => do
    let type ← whnfR (← instantiateMVars (← inferType e))
    let some name := type.getAppFn.constName? | return #[]
    let env ← getEnv
    unless isStructure env name do return #[]
    let mut found := #[]
    for field in getStructureFieldsFlattened env name (includeSubobjectFields := false) do
      let some projection ← observing? (mkProjection e field) | continue
      let fieldType ← inferType projection
      if ← isProp fieldType then
        if ← isCertificateFact fieldType then
          found := found.push projection
          continue
      found := found ++ (← fieldCertificates projection depth)
    return found

open Lean Meta Elab Tactic in
/-- Add the certificates stored in fields of local structures (schemes, admissibility
structures, conjunctions) as local facts that composition can use directly. Facts already in
the context are not repeated. -/
private meta def exposeFieldCertificates : TacticM Unit := withMainContext do
  let mut goal ← getMainGoal
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.isLet then continue
    for proof in ← fieldCertificates decl.toExpr 2 do
      let type ← inferType proof
      let known ← goal.withContext do
        (← getLCtx).anyM fun other => do
          if other.isImplementationDetail then return false
          withReducible <| isDefEq other.type type
      unless known do
        let (_, next) ← goal.note (← mkFreshUserName `field) proof
        goal := next
  replaceMainGoal [goal]

open Lean Meta Elab Tactic in
/-- Prepare a certificate goal: unfold the hinted definitions, inline literal `let`s in the goal,
unfold local encoding `let`s, and expose certificates stored in fields of local structures.
Inlining does not unfold named programs or change their certificate lookup. -/
meta def prepareCertificateGoal (hints : Array Ident) : TacticM Unit := do
  unless hints.isEmpty do
    evalTactic (← `(tactic| unfold $hints*))
  liftMetaTactic1 fun goal => do
    goal.replaceTargetDefEq (← zetaReduce (← instantiateMVars (← goal.getType))
      (zetaDelta := !hints.isEmpty))
  unfoldEncodingLets
  exposeFieldCertificates

end Cslib.Tactic
