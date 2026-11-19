/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import CslibFrontier.Tactic.PolyTime.Init

/-!
# Synthesizing polynomial-time certificates

Adapted from the cslib `crypto` branch: named certificates are tried before their implementations
are unfolded. `fun_prop` handles composition; Aesop chooses loop rules and uses local growth
contracts. Certificates use fixed machines and independent polynomial resource
bounds across all encoded inputs. Plain search applies plain statements directly; it does not
lower a goal or restate its hypotheses tidily. Unknown algorithms still require certificates.
On ordinary failure, `polytime` includes one failed compositional attempt when the backend has
reported one. This is a search hint, not a claim that the subterm is uncomputable. Resource-limit
and interrupt exceptions are unchanged.

Plain search excludes rules that would start search in the internal tidy calculus. Whether an
imported rule is excluded is decided once per file and shared by later calls (#1155); rules of
the current module are classified by each call.

Goal preparation, shared with `ppt`, runs before the search. `polytime [f, g]` unfolds the hinted
definitions in the goal and inlines the `let`s they expose. Every form replaces local encoding
`let`s (`let E := encPair encUnary encBits`) by their values in the goal and the hypotheses, and
adds the certificates stored in fields of local structures (a scheme's `S.decrypt_polyTime`, an
admissibility hypothesis's `h.guess`, a conjunction's components) as local facts.

## Main definitions

* `polytime`: prove a polynomial-time certificate using the `PolyTime` Aesop rule set.
* `Cslib.Tactic.PolyTime.Internal.prepareGoal`: the goal preparation shared with `ppt`.

## References

Adapted from Cslib/Tactic/PolyTime.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`; deterministic search consumes the canonical
plain calculus.
-/

public section

namespace Cslib.Tactic.PolyTime

open Turing.MultiTapeTM

@[aesop safe apply (rule_sets := [PolyTime])]
private theorem plainBoolNot {α : Type} {encIn : α ↪ List Bool} {f : α → Bool}
    (hf : ComputableInPolyTime f encIn encBool) :
    ComputableInPolyTime (fun a => !(f a)) encIn encBool :=
  ComputableInPolyTime.bool_not.comp hf

-- Fix the pair-valued function before selecting its component encoding conversion.
attribute [aesop unsafe 80% apply (rule_sets := [PolyTime])]
  ComputableInPolyTime.fstWithEncoding ComputableInPolyTime.sndWithEncoding

attribute [aesop safe apply (rule_sets := [PolyTime])] ComputableInPolyTime.of_finite

-- A range fixes its element and list encodings before a joint fold certificate checks the
-- callback and the list interfaces. Keep this assignment as a backtrackable alternative.
attribute [aesop unsafe 95% apply (rule_sets := [PolyTime])] ComputableInPolyTime.range

-- Boolean scans hide the element encoding in their result. Resolve the list certificate before
-- searching for a joint callback certificate, including when the callback captures local values.
attribute [program_certificate hlist]
  ComputableInPolyTime.anyWithInput ComputableInPolyTime.allWithInput
  ComputableInPolyTime.mapToBitsWithInput
  ComputableInPolyTime.bitsFoldlWithInput
attribute [program_certificate] ComputableInPolyTime.bitsStrictMajorityWithInput

-- Expose inner table and loop obligations to Aesop when composition alone cannot finish them.
attribute [program_certificate hvalues] ComputableInPolyTime.pi_update'
attribute [program_certificate]
  ComputableInPolyTime.bitsReverseWithInput ComputableInPolyTime.listReverseWithInput

-- Joint computation resolves the list and accumulator encodings before the growth contract
-- uses them. Each conjunction retains the evidence that must agree on those choices.
attribute [program_certificate hcompute hbound]
  ComputableInPolyTime.foldlWithInput_of_bounded_growth
attribute [program_certificate hbound]
  ComputableInPolyTime.iterateWithInput_of_bounded_growth

open Lean Meta in
/-- Recover an unknown element encoding from a known canonical list representation before
synthesizing its interface. An arbitrary list representation must determine it independently. -/
private meta def synthListInterface (goal : MVarId) : MetaM Unit := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOf ``ListEncoding || target.isAppOf ``SizedListEncoding do
    throwError "expected a list interface"
  let element := target.getAppArgs[1]!
  let list ← whnfR target.getAppArgs[2]!
  if element.isMVar then
    if list.isAppOf ``encList then
      unless ← isDefEq element list.getAppArgs.back! do throwError "incompatible element encoding"
    else if list.isConstOf ``encBits then
      unless ← isDefEq element (mkConst ``encBool) do throwError "incompatible bit encoding"
  let target ← instantiateMVars target
  if target.hasExprMVar then throwError "encoding is not yet determined"
  goal.assign (← synthInstance target)

open Lean Meta Elab Tactic in
/-- Synthesize list interfaces after recovering the element encoding from a known representation. -/
@[aesop safe tactic (rule_sets := [PolyTime])
  (index := [target ListEncoding _ _, target SizedListEncoding _ _])]
private meta def polytimeListInstance : TacticM Unit := withMainContext do
  synthListInterface (← getMainGoal)
  replaceMainGoal []

-- Computed finite tables use the ordinary application rule. Its function-valued head cannot
-- be registered as a `fun_prop` theorem, so Aesop supplies this closure step.
attribute [aesop unsafe 75% apply (rule_sets := [PolyTime])]
  ComputableInPolyTime.pi_apply'

open Lean Meta in
/-- Select the certificate family before searching, keeping plain goals in the plain calculus. -/
private meta def polytimePredicate (target : Expr) : MetaM Name := do
  let target := (← instantiateMVars target).consumeMData
  if target.isAppOf ``ComputableInPolyTime then return ``ComputableInPolyTime
  throwError "expected a polynomial-time goal"

open Lean Meta in
/-- Choose only the order of existing plain conditional recipes. Boolean guards retain their
arbitrary encoding; proposition guards use the decision encoding of `ite_decide`. Inspection
does not retain metavariable assignments, and both recipes remain available. -/
private meta def plainConditionalRules? (target : Expr) : MetaM (Option (Array Name)) := do
  let saved ← saveState
  try
    let target := (← instantiateMVars target).consumeMData
    unless target.isAppOf ``ComputableInPolyTime do return none
    Cslib.Tactic.withConditionalBody? target.getAppArgs[2]! fun body => do
      let condition ← whnfR body.getAppArgs[1]!
      let boolean := condition.isAppOfArity ``Eq 3 &&
        condition.getAppArgs[0]!.isConstOf ``Bool &&
        condition.getAppArgs[2]!.isConstOf ``Bool.true
      return if boolean then #[``ComputableInPolyTime.ite, ``ComputableInPolyTime.ite_decide]
        else #[``ComputableInPolyTime.ite_decide, ``ComputableInPolyTime.ite]
  finally saved.restore

/-- Expose local routine certificates and their argument obligations as search alternatives. -/
-- Equal priority lets argument goals run before expensive alternatives at the parent goal.
@[aesop unsafe 100% tactic (rule_sets := [PolyTime])]
private meta def polytimeKnownCall : Aesop.RuleTac := fun input => do
  let predicate ← input.goal.withContext do polytimePredicate (← input.goal.getType)
  Cslib.Tactic.applyKnownCall predicate 2 (predicate ++ `comp) `g `hf input

open Lean Meta Elab Tactic in
/-- Test whether any local routine certificate applies to the current goal. -/
private meta def hasLocalCall (goal : MVarId) : MetaM Bool := do
  try
    discard <| (polytimeKnownCall { (default : Aesop.RuleTacInput) with goal }).run' {}
    pure true
  catch _ => pure false

open Lean Meta Elab Tactic in
/-- Commit to decomposition only when no local certificate supplies an alternative. The matcher
restores the caller's state and leaves argument preparation open, so this tests applicability
without choosing an intermediate encoding. -/
private meta def withoutLocalCall (tactic : TacticM Unit) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  discard <| polytimePredicate (← goal.getType)
  if ← hasLocalCall goal then throwError "a local certificate is an alternative to decomposition"
  tactic

open Lean Meta Elab Tactic in
/-- Retain decomposition as an alternative when a local certificate competes with it. -/
private meta def withLocalCall (tactic : TacticM Unit) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  discard <| polytimePredicate (← goal.getType)
  unless ← hasLocalCall goal do throwError "no competing local certificate"
  tactic

/-- Expose named deterministic certificates as search alternatives. -/
@[aesop unsafe 99% tactic (rule_sets := [PolyTime])]
private meta def polytimeCertificate : Aesop.RuleTac := fun input => do
  let predicate ← input.goal.withContext do polytimePredicate (← input.goal.getType)
  Cslib.Tactic.applyCertificates predicate input

open Lean Meta in
/-- A supplied scan callback may constrain compatible encodings before the eager list proof.
The ordinary named-certificate rule retains the complete list-first alternative. -/
@[aesop unsafe 100% tactic (rule_sets := [PolyTime])]
private meta def polytimeScanKnownCallback : Aesop.RuleTac := fun input => input.goal.withContext do
  let target := (← instantiateMVars (← input.goal.getType)).consumeMData
  unless target.isAppOf ``ComputableInPolyTime do throwError "expected a plain scan goal"
  let key ← Cslib.Tactic.efficiencyKey target
  unless key.2.1 == ``List.any do throwError "expected a Boolean list scan"
  Cslib.Tactic.applyScanWithLocalCallback ``ComputableInPolyTime
    ``ComputableInPolyTime.anyWithInput input

open Lean Meta Elab Tactic in
/-- Decompose constructors before generic composition can guess intermediate encodings. -/
private meta def polytimeConstruct (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    discard <| polytimePredicate target
    let rawBits := target.getAppArgs[4]!.isConstOf ``encBits
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let rule ← lambdaTelescope program fun _ body => do
      if body.isAppOf ``HAppend.hAppend || body.isAppOf ``List.append then
        return if rawBits then ``ComputableInPolyTime.bitsAppend
          else ``ComputableInPolyTime.listAppend'
      if body.isAppOf ``List.cons then
        return if rawBits then ``ComputableInPolyTime.bitsCons
          else ``ComputableInPolyTime.cons'
      if body.isAppOf ``Prod.mk then return ``ComputableInPolyTime.prod
      throwError "expected a constructor"
    guard <| liftMetaTactic fun goal => do
      goal.applyConst rule

open Lean in
/-- Whether a constant name is in the raw family: its component after `Turing.MultiTapeTM` starts
with `ComputableTidily` or `ComputesTidily`. -/
private meta def isRawFamilyName : Name → Bool
  | .str (.str (.str (.str .anonymous "Turing") "MultiTapeTM") "Internal") head =>
    head.startsWith "ComputableTidily" || head.startsWith "ComputesTidily"
  | .str (.str (.str .anonymous "Turing") "MultiTapeTM") head =>
    head.startsWith "ComputableTidily" || head.startsWith "ComputesTidily"
  | .str parent _ | .num parent _ => isRawFamilyName parent
  | .anonymous => false

open Lean Meta in
/-- Inspect proposition aliases with the same reducible transparency used by `fun_prop`.
`Meta.transform` maintains binder context, including dependent and quantified premises; data and
proof implementations are not unfolded merely to classify a transition's proposition. -/
private meta def rawTransitionPremise (type : Expr) : MetaM Bool := do
  if (type.find? fun e => match e with
      | .const n _ => isRawFamilyName n
      | _ => false).isSome then
    return true
  let inspect : StateRefT Bool MetaM Unit := do
    discard <| Meta.transform type (pre := fun e => do
      if ← get then return .done e
      let reduced ← if ← isProp e then whnfR e else pure e
      if let .const name _ := reduced.getAppFn then
        if isRawFamilyName name then
          set true
          return .done reduced
      return .continue (some reduced))
  return (← inspect.run false).2

open Lean in
/-- Classifications of imported declarations, shared by every invocation in a file. -/
private meta structure ImportedRuleCache where
  premises : Std.HashMap Name Bool := {}
  properties : Std.HashMap Name Bool := {}

open Lean in
private meta structure PlainRuleCache where
  premises : Std.HashMap Name Bool := {}
  properties : Std.HashMap Name Bool := {}
  /-- The file's shared classifications of imported declarations, when this invocation may use
  them; see `importedRuleCacheExt`. -/
  shared : Option (IO.Ref ImportedRuleCache) := none

/-- Empty per-invocation classification state. -/
private meta instance : Inhabited PlainRuleCache := ⟨{}⟩

open Lean in
private meta initialize rawPremiseCache : EnvExtension (Option PlainRuleCache) ←
  registerEnvExtension (pure none) (asyncMode := .local)

open Lean in
/-- For each imported module, whether its import closure declares a raw-family constant. -/
private meta def rawImportClosure (header : EnvironmentHeader) : Std.HashMap Name Bool := Id.run do
  -- Imports are dependency-first. A theorem in a module with no raw-family declaration in
  -- its import closure cannot hide one behind an alias: aliases cannot refer to later modules.
  let mut rawModules : Std.HashMap Name Bool := {}
  for i in [:header.moduleNames.size] do
    let moduleName := header.moduleNames[i]!
    let data := header.moduleData[i]!
    let ownsRaw := data.constNames.any isRawFamilyName
    let importsRaw := data.imports.any fun imported => rawModules.getD imported.module true
    rawModules := rawModules.insert moduleName (ownsRaw || importsRaw)
  return rawModules

open Lean in
/-- `rawImportClosure` of the imports, which are fixed for the whole file. Importing only creates
the thunk: the first tactic invocation scans the imported constants, and every later one,
including proofs elaborated in parallel, reuses the result. The extension stores no entries. -/
private meta initialize rawImportClosureExt :
    PersistentEnvExtension Empty Empty (Thunk (Std.HashMap Name Bool)) ←
  registerPersistentEnvExtension {
    mkInitial := pure (.pure {})
    addImportedFn := fun _ => do
      let header := (← read).env.header
      return .mk fun _ => rawImportClosure header
    addEntryFn := fun rawModules _ => rawModules
    exportEntriesFn := fun _ => #[] }

open Lean in
/-- Classifications of imported declarations, filled on first use and shared by every later
invocation in the file, including proofs elaborated in parallel. Each entry is a function of the
declaration's type and of imported constants' definitions and reducibility, which are fixed for
the file except for the reducibility changes checked by `importedClassificationsStable`. Parallel
proofs may classify the same declaration concurrently; they compute and insert the same value, so
the race is benign and the cache contents are deterministic. The extension stores no entries. -/
private meta initialize importedRuleCacheExt :
    PersistentEnvExtension Empty Empty (Option (IO.Ref ImportedRuleCache)) ←
  registerPersistentEnvExtension {
    mkInitial := pure none
    addImportedFn := fun _ => some <$> IO.mkRef {}
    addEntryFn := fun cache _ => cache
    exportEntriesFn := fun _ => #[] }

open Lean Meta in
/-- Whether the current module's reducibility changes leave every classification of an imported
declaration unchanged. Classification unfolds only `@[reducible]` constants, and otherwise only
looks for a universe in the type of a term, which unfolding a `Prop`-valued constant never
produces. A module cannot change the reducible status of an imported constant without
`allowUnsafeReducibility`; a change to that status, or to a constant that is not `Prop`-valued,
makes the invocation classify imported declarations itself. `[local irreducible]
ComputableInPolyTime` keeps the shared classifications. -/
private meta def importedClassificationsStable : MetaM Bool := do
  let env ← getEnv
  let state := reducibilityExtraExt.getState env
  state.map₂.foldlM (init := true) fun stable name status => do
    unless stable do return false
    -- A current-module constant cannot occur in an imported declaration.
    let some i := env.getModuleIdxFor? name | return true
    let imported := state.map₁.get? name |>.getD <|
      match (reducibilityCoreExt.getModuleEntries env i).binSearch (name, .semireducible)
          (fun a b => Name.quickLt a.1 b.1) with
      | some (_, status) => status
      | none => .semireducible
    if status == .reducible || imported == .reducible then return false
    let some info := env.find? name | return false
    forallTelescopeReducing info.type fun _ body => return body.isProp

open Lean Meta in
/-- Classify a declaration, reusing the invocation's memo and, for an imported declaration, the
file's shared classifications. A declaration from a module whose import closure declares no
raw-family constant needs no inspection. -/
private meta def classifyRule (name : Name) (memo : PlainRuleCache → Std.HashMap Name Bool)
    (shared : ImportedRuleCache → Std.HashMap Name Bool)
    (record : ImportedRuleCache → Bool → ImportedRuleCache) (classify : MetaM Bool) :
    MetaM Bool := do
  let env ← getEnv
  let some state := rawPremiseCache.getState env | classify
  if let some result := (memo state).get? name then return result
  let some cache := state.shared | classify
  let some i := env.getModuleIdxFor? name | classify
  if let some result := (shared (← cache.get)).get? name then return result
  let mayUseRaw :=
    (rawImportClosureExt.getState env).get.getD env.header.moduleNames[i.toNat]! true
  let result ← if mayUseRaw then classify else pure false
  cache.modify (record · result)
  return result

open Lean Meta in
/-- Inspect premises under their data parameters; a complete certificate has no raw premise. -/
private meta def typeHasRawPremise (type : Expr) : MetaM Bool :=
  forallTelescope type fun xs _ =>
    xs.anyM fun x => do
      let premise ← inferType x
      if ← isProp premise then rawTransitionPremise premise else pure false

open Lean Meta in
/-- Inspect a registered rule's hypotheses, including reducible proposition aliases. -/
private meta def hasRawPremise (name : Name) : MetaM Bool := do
  let some info := (← getEnv).find? name | return true
  classifyRule name (·.premises) (·.premises)
    (fun cache result => { cache with premises := cache.premises.insert name result })
    (typeHasRawPremise info.type)

open Lean in
/-- Modify only the search's environment copy, including during asynchronous proof elaboration.
The change cannot escape `withEnv`, so it is local and needs no persistent write log. -/
private meta def searchRuleState {α β σ : Type} (ext : ScopedEnvExtension α β σ)
    (env : Environment) (f : σ → σ) : Environment :=
  ext.ext.modifyState (asyncMode := .local) (log := .unlogged) env fun s =>
    match s.stateStack with
    | top :: stack =>
      { s with stateStack := { top with state := f top.state } :: stack }
    | [] => s

open Lean Meta in
/-- Recognize raw properties themselves, including full-arity reducible aliases. -/
private meta def isRawProperty (name : Name) : MetaM Bool := do
  let some info := (← getEnv).find? name | return true
  classifyRule name (·.properties) (·.properties)
    (fun cache result => { cache with properties := cache.properties.insert name result })
    (forallTelescope info.type fun xs _ => do
      rawTransitionPremise (mkAppN (← mkConstWithLevelParams name) xs))

open Lean Meta Mathlib.Meta.FunProp in
/-- Remove raw function properties during public search. Ordinary theorem descriptors remain:
raw premises can use complete local evidence through the discharger, but their missing property
metadata prevents recursive raw function-property proof search. -/
private meta def plainRuleEnvironment (env : Environment) : MetaM Environment := do
  let rawProperties ← (funPropDeclsExt.getState env).decls.foldValuesM
    (init := ({} : Std.HashSet Name)) fun names decl => do
      return if ← isRawProperty decl.funPropName then names.insert decl.funPropName else names
  -- Local implications are enumerated independently of the theorem tables. Their raw premises
  -- may use supplied assumptions, but cannot initiate raw function-property proof search.
  return searchRuleState funPropDeclsExt env fun s =>
    { s with decls := s.decls.fold (init := {}) fun tree _ decl =>
        if rawProperties.contains decl.funPropName then tree
        else tree.insertKeyValue decl.path decl }

open Lean Meta Mathlib.Meta.FunProp in
/-- Retain ordinary general rules while excluding raw construction premises.
Both evaluated entries and lazy entries must be removed from this per-search tree. -/
private meta def plainGeneralTheorems (thms : GeneralTheorems) : MetaM GeneralTheorems := do
  let mut names : Std.HashSet Name := {}
  for node in thms.theorems.tries do
    for rule in node.values do names := names.insert rule.thmName
    for (_, rule) in node.pending do names := names.insert rule.thmName
  let mut blocked : Std.HashSet Name := {}
  for name in names do
    if ← hasRawPremise name then blocked := blocked.insert name
  return { thms with theorems := { thms.theorems with
    tries := thms.theorems.tries.map fun node =>
      { node with
        values := node.values.filter fun rule => !blocked.contains rule.thmName
        pending := node.pending.filter fun entry => !blocked.contains entry.2.thmName } } }

open Lean Meta in
/-- Retain Aesop's local application alternatives and priority, excluding only rules which would
start raw search from a plain goal. Adapted from `Aesop.BuiltinRules.applyHyps` (Jannis Limperg). -/
meta def Internal.applyLocalCertificates : Aesop.RuleTac := fun input => input.goal.withContext do
  let mut applications := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail || (← typeHasRawPremise decl.type) then continue
    let saved ← saveState
    try
      applications := applications.push (← Aesop.BuiltinRules.applyHyp decl.fvarId input.goal
        input.options.applyHypsTransparency)
    catch _ => pure ()
    finally saved.restore
  return ⟨applications⟩

open Lean Meta in
/-- Project only the builtin local-application descriptor. Nested eager searches read this same
scoped rule set; all rule identity, indexing, priority, simp and simproc data are retained. -/
private meta def plainBuiltinEnvironment (env : Environment) : MetaM Environment := do
  let (ext, _, _, _, _) ← Aesop.Frontend.getGlobalRuleSetData `builtin
  let state := ext.getState env
  let initial := (({} : Aesop.Index Aesop.UnsafeRuleInfo), ({} : Std.HashSet Aesop.RuleName))
  let (index, matched) := state.unsafeRules.fold (init := initial) fun (index, matched) rule =>
    let isTarget := rule.name.name == ``Aesop.BuiltinRules.applyHyps
    let matched := if isTarget then matched.insert rule.name else matched
    let rule := if isTarget then
      { rule with tac := .ruleTac ``Internal.applyLocalCertificates } else rule
    (index.add rule rule.indexingMode, matched)
  unless matched.size == 1 do throwError "expected one builtin local-application rule"
  return searchRuleState ext env fun state => { state with unsafeRules := index }

open Lean Meta Mathlib.Meta.FunProp in
/-- Prepare only immutable global declaration classifications, never proofs or local evidence.
Imported declarations are classified on demand through the file's shared cache when the
current module's reducibility changes permit it; the memo then holds current-module rules only. -/
private meta def preparePlainRuleMemo : MetaM PlainRuleCache := do
  let env ← getEnv
  let shared ← if ← importedClassificationsStable then
      pure (importedRuleCacheExt.getState env) else pure none
  -- With the shared cache, only current-module rules are classified for this invocation.
  let perInvocation (name : Name) := shared.isNone || (env.getModuleIdxFor? name).isNone
  let mut names : Std.HashSet Name := {}
  for (_, entries) in (Cslib.Tactic.certificateExt.getState env) do
    for (name, _) in entries do
      if perInvocation name then names := names.insert name
  for rules in #[morTheoremsExt.getState env] do
    for node in rules.theorems.tries do
      for rule in node.values do
        if perInvocation rule.thmName then names := names.insert rule.thmName
      for (_, rule) in node.pending do
        if perInvocation rule.thmName then names := names.insert rule.thmName
  -- Unknown module metadata remains conservative, and current-module rules are always checked.
  let rawModules := (rawImportClosureExt.getState env).get
  let mut cache : Std.HashMap Name Bool := {}
  for name in names do
    let mayUseRaw := match env.getModuleIdxFor? name with
      | some i => rawModules.getD env.header.moduleNames[i.toNat]! true
      | none => true
    cache := cache.insert name (← if mayUseRaw then hasRawPremise name else pure false)
  let properties ← (funPropDeclsExt.getState env).decls.foldValuesM
    (init := ({} : Std.HashMap Name Bool)) fun properties decl => do
      unless perInvocation decl.funPropName do return properties
      let mayUseRaw := match env.getModuleIdxFor? decl.funPropName with
        | some i => rawModules.getD env.header.moduleNames[i.toNat]! true
        | none => true
      let raw ← if mayUseRaw then isRawProperty decl.funPropName else pure false
      return properties.insert decl.funPropName raw
  return { premises := cache, properties, shared }

open Lean Meta Elab Tactic in
/-- Reuse global classification answers across one invocation, and those of imported declarations
across the file. Rule tables, certificate lookup, matching and local evidence are not projected
or cached by this wrapper. -/
meta def Internal.withPlainRuleMemo (action : TacticM Unit) : TacticM Unit := do
  let env ← getEnv
  if (rawPremiseCache.getState env).isSome then
    action
  else
    let memo ← preparePlainRuleMemo
    withEnv (rawPremiseCache.setState env (some memo)) action

open Lean Meta Elab Tactic in
/-- Apply the deterministic boundary using the current tables and scoped classification memo.
Named-certificate metadata retain their priorities and eager obligations. -/
meta def Internal.withPlainRuleCache (action : TacticM Unit) : TacticM Unit :=
  Internal.withPlainRuleMemo do
    let env ← getEnv
    let certificates ← (Cslib.Tactic.certificateExt.getState env).foldM (init := {})
      fun certificates key entries => do
        let entries ← entries.filterM fun (name, _) => return !(← hasRawPremise name)
        return certificates.insert key entries
    let env := searchRuleState Cslib.Tactic.certificateExt env fun _ => certificates
    let env ← plainBuiltinEnvironment env
    -- Match plain certificates on their programs and encodings, without comparing existential
    -- machine witnesses when a candidate fails to match one of those arguments.
    let env := searchRuleState reducibilityExtraExt env fun status =>
      status.insert ``ComputableInPolyTime .irreducible
    withEnv env action

open Lean Meta in
/-- Apply an existing fact only when matching its conclusion determines every argument. -/
private meta def matchLocalCertificate (fact : Expr) (target : Expr) : MetaM (Option Expr) := do
  let (xs, _, conclusion) ← forallMetaTelescope (← inferType fact)
  unless ← isDefEq conclusion target do return none
  let args ← xs.mapM instantiateMVars
  if args.any Expr.hasExprMVar then return none
  return some (mkAppN fact args)

open Lean Meta in
/-- Instantiate a supplied local certificate family without proving any new premise. Every
argument must be determined by the requested type; implications with missing evidence fail. -/
private meta def knownLocalCertificate (target : Expr) : MetaM (Option Expr) := do
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let saved ← saveState
      let proof? ← matchLocalCertificate decl.toExpr target
      if proof?.isSome then return proof?
      saved.restore
  return none

open Lean Meta in
/-- Keep conditional guards and branches in joint search. Complete supplied guard evidence may
fix an encoding without an unsafe child-step penalty. The unprepared application is retained,
so that evidence and encoding alternatives remain available if later premises fail. -/
@[aesop unsafe 98% tactic (rule_sets := [PolyTime])]
private meta def polytimeConditional : Aesop.RuleTac := fun input => input.goal.withContext do
  let some rules ← plainConditionalRules? (← input.goal.getType)
    | throwError "expected a plain conditional program"
  let capture (goals : List MVarId) (probability : Float) : Aesop.BaseM Aesop.RuleApplication := do
    let goals ← goals.toArray.mapM (Aesop.mvarIdToSubgoal input.goal)
    return {
      goals
      postState := ← saveState
      scriptSteps? := none
      successProbability? := some ⟨probability⟩ }
  let initial ← saveState
  let mut applications := #[]
  for i in [:rules.size] do
    try
      let goals ← input.goal.applyConst rules[i]!
      let applied ← saveState
      let probability := if i == 0 then 0.98 else 0.97
      try
        let name := if rules[i]! == ``ComputableInPolyTime.ite then `hc else `hcondition
        if let some guard ← goals.findM? fun goal => return name.isSuffixOf (← goal.getTag) then
          let proof? ← guard.withContext do knownLocalCertificate (← guard.getType)
          if let some proof := proof? then
            guard.assign proof
            let remaining ← goals.filterM fun goal => return !(← goal.isAssignedOrDelayedAssigned)
            applications := applications.push (← capture remaining probability)
      catch _ => pure ()
      finally applied.restore
      applications := applications.push (← capture goals probability)
    catch _ => pure ()
    finally initial.restore
  if applications.isEmpty then throwError "no conditional recipe applies"
  return ⟨applications⟩

open Lean Meta Elab Tactic in
/-- Finish a supplied-guard conditional before a generic unsafe rule can close its parent.
Only supplied local evidence and conditional recipes run in this optional attempt; complete
proofs alone commit. Unresolved targets and competing local/named calls retain the
ordinary joint alternatives, including every unprepared application. -/
@[aesop safe -21 tactic (rule_sets := [PolyTime])]
private meta def polytimeConditionalFast : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  if target.hasExprMVar then throwError "conditional target is not yet determined"
  unless (← plainConditionalRules? target).isSome do
    throwError "expected a plain conditional program"
  if ← hasLocalCall goal then throwError "a local certificate precedes conditional decomposition"
  let key ← Cslib.Tactic.efficiencyKey target
  unless ((Cslib.Tactic.certificateExt.getState (← getEnv)).getD key #[]).isEmpty do
    throwError "a named certificate precedes conditional decomposition"
  let output ← (polytimeConditional { (default : Aesop.RuleTacInput) with goal }).run' {}
  for application in output.applications do
    let before ← saveState
    try
      application.postState.restore
      let goals := application.goals.toList.map (·.mvarId)
      if ← goals.anyM fun goal => do
          let tag ← goal.getTag
          return (`hc).isSuffixOf tag || (`hcondition).isSuffixOf tag then
        throwError "conditional guard needs joint search"
      setGoals goals
      unless goals.isEmpty do
        let known := mkIdent ``Internal.applyLocalCertificates
        -- Reuse the registered descriptor: resolving its private declaration by syntax
        -- would depend on whether the caller is elaborating an exported theorem.
        let env ← getEnv
        let (ext, _, _, _, _) ← Aesop.Frontend.getGlobalRuleSetData `PolyTime
        let index := (ext.getState env).unsafeRules.fold (init := {}) fun index rule =>
          if rule.name.name == ``polytimeConditional then index.add rule rule.indexingMode
          else index
        let env := searchRuleState ext env fun _ =>
          { Aesop.BaseRuleSet.empty with unsafeRules := index }
        withEnv env do
          evalTactic (← `(tactic| solve | all_goals
            aesop
              (config :=
                { terminal := true
                  enableSimp := false
                  assumptionTransparency := .reducible })
              (rule_sets := [-builtin, -default, PolyTime])
              (add unsafe 100% tactic $known:ident)))
      if ← Aesop.hasSorry (mkMVar goal) then throwError "conditional premise was admitted"
      return
    catch _ => before.restore
  throwError "no supplied-guard conditional proof closed all premises"

open Lean in
/-- The current invocation's rendered hint. The reference survives search backtracking, but the
local environment containing it is discarded when the invocation finishes. -/
private meta initialize failureHint : EnvExtension (Option (IO.Ref (Option String))) ←
  registerEnvExtension (pure none) (asyncMode := .local)

open Lean Elab Tactic in
/-- Collect one backend hint without rerunning search, reporting it as a failure of the tactic
`tacticName`. Each invocation, including a nested one, has its own reference; `withEnv` restores
the caller's environment even on resource exceptions. The ordinary `catch` does not intercept
Lean's resource-limit or interrupt exceptions. -/
meta def Internal.withFailureHint (tacticName : String) (action : TacticM Unit) :
    TacticM Unit := do
  let hint ← IO.mkRef (none : Option String)
  try
    withEnv (failureHint.setState (← getEnv) (some hint)) action
  catch ex =>
    let some message ← hint.get | throw ex
    match ex with
    | .error ref messageData =>
      throw <| .error ref (messageData ++ .note m!"{tacticName} could not certify a subterm in \
        one attempted route:\n{message}")
    | .internal .. => throw ex

open Lean Meta Elab Tactic Mathlib.Meta.FunProp in
/-- Shared compositional backend with a fresh alias-aware raw-premise boundary. The standard
assumption discharger and ordinary transition depth are retained; callers keep their step limit.
Consumers can reuse the same boundary for nested plain deterministic goals. -/
meta def Internal.funPropWithPlainBoundary (maxSteps : Nat) : TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let disch : Expr → MetaM (Option Expr) := fun e => do
      if let some proof ← tacticToDischarge
          (← `(tactic| first | with_reducible assumption | infer_param)) e then return some proof
      if ← rawTransitionPremise e then knownLocalCertificate e else pure none
    let ctx : Mathlib.Meta.FunProp.Context := { config := { maxSteps }, disch }
    let env ← getEnv
    let state : Mathlib.Meta.FunProp.State := {
      morTheorems := ← plainGeneralTheorems (morTheoremsExt.getState env)
      -- Raw predicates are absent from the scoped property table below. Keeping transition
      -- descriptors therefore permits supplied raw evidence through `disch`, without starting
      -- raw function-property search to manufacture that evidence.
      transitionTheorems := transitionTheoremsExt.getState env }
    let ruleEnv ← plainRuleEnvironment env
    let (result, state) ← withEnv ruleEnv <| (funProp target ctx).run state
    let some result := result | do
      if let some hint := failureHint.getState (← getEnv) then
        if (← hint.get).isNone then
          -- FunProp rendered these strings while its telescope variables were in scope.
          -- Keep its first report, without retaining expressions from its failure cache.
          hint.set state.msgLog.getLast?
      throwError "no compositional plain certificate: {state.msgLog}"
    goal.assign result.proof
    replaceMainGoal []
open Lean Elab Tactic in
/-- Plain deterministic goals use the shared backend at their original step limit. -/
private meta def polytimePlainFunProp : TacticM Unit :=
  Internal.funPropWithPlainBoundary 256

open Lean Meta Elab Tactic in
/-- Let composition finish before trying loop specifications. -/
private meta def polytimeFunProp : TacticM Unit := withMainContext do
  discard <| polytimePredicate (← getMainTarget)
  polytimePlainFunProp

namespace Internal

/-- Fix a raw bit list's encoding and expose the two growth cases before proof search. -/
theorem plain_foldl_bits_rule {γ β : Type} {encIn : γ ↪ List Bool} {encB : β ↪ List Bool}
    {list : γ → List Bool} {init : γ → β} {step : β → Bool → β}
    (hlist : ComputableInPolyTime list encIn encBits)
    (hinit : ComputableInPolyTime init encIn encB)
    (hstep : ComputableInPolyTime (fun pair : β × Bool => step pair.1 pair.2)
      (encPair encB encBool) encB) {growth : ℕ}
    (hgrowth : ∀ state, (encB (step state false)).length ≤ (encB state).length + growth ∧
      (encB (step state true)).length ≤ (encB state).length + growth) :
    ComputableInPolyTime (fun x => (list x).foldl step (init x)) encIn encB :=
  ComputableInPolyTime.foldl_of_bounded_growth hlist hinit hstep
    (fun state bit => by cases bit; exacts [(hgrowth state).1, (hgrowth state).2])

end Internal

open Lean Meta Elab Tactic in
/-- Resolve the traversed list's encoding before certifying the step. Try a nonincreasing state
bound first, committing to it only after its growth obligation has been proved. -/
private meta def polytimeFold (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    discard <| polytimePredicate target
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let isFold ← lambdaTelescope program fun _ body => pure (body.isAppOf ``List.foldl)
    unless isFold do throwError "expected a list fold"
    guard do
      let rules : Array (TacticM Unit) := #[
        liftMetaTactic fun goal => goal.applyConst ``Internal.plain_foldl_bits_rule,
        -- List interfaces depend on the encoding established by hlist. Retain their goals
        -- until that computation and its callback have fixed the encoding parameters.
        liftMetaTactic fun goal => goal.applyConst
          ``ComputableInPolyTime.foldl_of_bounded_growth { allowSynthFailures := true }]
      for applyRule in rules do
        let saved ← saveState
        try
          applyRule
          evalTactic (← `(tactic| case hlist => solve |
            aesop
              (config :=
                { terminal := true
                  enableSimp := false
                  assumptionTransparency := .reducible })
              (rule_sets := [PolyTime])))
          -- A supplied callback may require a noncanonical element interface for this list.
          -- Match that evidence before recovering an unknown encoding from the representation.
          let some stepGoal ← (← getGoals).findM? fun goal =>
              return (`hstep).isSuffixOf (← goal.getTag)
            | throwError "fold has no callback premise"
          if let some proof ← stepGoal.withContext do
              knownLocalCertificate (← stepGoal.getType) then
            stepGoal.assign proof
          -- A callback which ignores its element cannot recover that element's encoding.
          -- The traversed list's representation supplies it before checking the callback.
          for goal in ← getGoals do
            try synthListInterface goal catch _ => pure ()
          setGoals (← (← getGoals).filterM fun goal => return !(← goal.isAssigned))
          -- Growth and the initializer must use the callback's accumulator representation.
          unless ← stepGoal.isAssigned do Cslib.Tactic.solveTagged `hstep
          let afterList ← saveState
          try
            evalTactic (← `(tactic| case growth => exact 0))
            Cslib.Tactic.solveTagged `hgrowth
          catch _ =>
            afterList.restore
            Cslib.Tactic.solveTagged `hgrowth
          -- Commit only after all callback and growth obligations close.
          evalTactic (← `(tactic| all_goals solve |
            aesop
              (config :=
                { terminal := true
                  enableSimp := false
                  assumptionTransparency := .reducible })
              (rule_sets := [PolyTime])))
          return
        catch _ => saved.restore
      throwError "no supported list encoding"

open Lean Meta Elab Tactic in
/-- Apply the bounded-growth iteration rule once the goal is seen to be an iteration. -/
private meta def polytimeIterate (guard : TacticM Unit → TacticM Unit) : TacticM Unit :=
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    discard <| polytimePredicate target
    let program ← Core.betaReduce (← etaExpand target.getAppArgs[2]!)
    let isIter ← lambdaTelescope program fun _ body => pure (body.isAppOf ``Nat.iterate)
    unless isIter do throwError "expected an iteration"
    guard <| liftMetaTactic fun goal => do
      goal.applyConst ``ComputableInPolyTime.iterate_of_bounded_growth

attribute [aesop safe apply (rule_sets := [PolyTime])] Nat.le_refl

attribute [aesop norm simp (rule_sets := [PolyTime])] forall_and

open Lean Meta Elab Tactic in
/-- Whether `type` is an efficiency goal (possibly under binders or conjunctions) whose program
body must stay un-normalized until named certificates, local calls and `fun_prop` have tried. -/
private meta partial def isEfficiencyGoal (type : Expr) : Bool :=
  match type.consumeMData with
  | .forallE _ _ body _ => isEfficiencyGoal body
  | .letE _ _ _ body _ => isEfficiencyGoal body
  | e =>
    if e.isAppOfArity ``And 2 then
      isEfficiencyGoal e.getAppArgs[0]! || isEfficiencyGoal e.getAppArgs[1]!
    else
      let fn := e.getAppFn
      fn.isConstOf ``ComputableInPolyTime ||
        fn.isConstOf `Turing.MultiTapeTM.ComputableInLogSpace ||
        fn.isConstOf `Cslib.Probability.IsPPTOn ||
        fn.isConstOf `Cslib.Probability.IsPPT ||
        fn.isConstOf `Cslib.Probability.IsOraclePPTOn ||
        fn.isConstOf `Cslib.Probability.IsOraclePPT

open Lean in
/-- Whether `type` is a closed PPT goal (possibly under binders or conjunctions) whose encoded
samplers `enc _ <$> sample _` must not be fused by monad-map `@[simp]` lemmas. -/
private meta partial def hasClosedPPTGoal (type : Expr) : Bool :=
  match type.consumeMData with
  | .forallE _ _ body _ => hasClosedPPTGoal body
  | .letE _ _ _ body _ => hasClosedPPTGoal body
  | e =>
    if e.isAppOfArity ``And 2 then
      hasClosedPPTGoal e.getAppArgs[0]! || hasClosedPPTGoal e.getAppArgs[1]!
    else
      let fn := e.getAppFn
      fn.isConstOf `Cslib.Probability.IsPPTOn || fn.isConstOf `Cslib.Probability.IsPPT

open Lean Meta Elab Tactic in
/-- Run Aesop-style `simp_all` with the default and `PolyTime` simp sets, failing when nothing
changes or when a metavariable from the goal or context would be dropped. When
`preserveDefinitions` is true, `dsimp`, projection reduction, and `iota`/`zeta` reductions are
disabled so reducible `abbrev` wrappers and projections stay intact while `@[simp]` rewrite lemmas
still normalize associative/structural syntax. -/
private meta def polytimeSimpAll (preserveDefinitions : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let mut goalMVars : Std.HashSet MVarId := {}
  for m in ← getMVars (← goal.getType) do goalMVars := goalMVars.insert m
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      for m in ← getMVars decl.type do goalMVars := goalMVars.insert m
  let (_, _, simpExt, _, simprocExt) ← Aesop.Frontend.getGlobalRuleSetData `PolyTime
  let closedPPT := hasClosedPPTGoal (← instantiateMVars (← goal.getType))
  let config : Simp.Config :=
    if preserveDefinitions then
      if closedPPT then
        { zetaDelta := false }
      else
        { dsimp := false, proj := false, iota := false, zeta := false, zetaDelta := false }
    else
      {}
  let ctx ← Simp.mkContext
    (config := config)
    (simpTheorems := #[← simpExt.getTheorems, ← getSimpTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let ctx := ctx.setFailIfUnchanged false
  let ctx ← if ctx.config.zetaDelta || preserveDefinitions then pure ctx else do
    let mut thms := ctx.simpTheorems
    if thms.isEmpty then thms := #[{}]
    for decl in ← getLCtx do
      if decl.hasValue && !decl.isImplementationDetail then
        thms := thms.modify 0 (·.addLetDeclToUnfold decl.fvarId)
    pure (ctx.setSimpTheorems thms)
  let ctx ←
    if closedPPT then
      -- Note: `eraseCore` silently ignores names that are not in the simp theorem set.
      let erased := #[
        `bind_map_left, `LawfulMonad.bind_pure_comp,
        `Functor.map_map, `LawfulMonad.map_map, `map_bind,
        `PFunctor.FreeM.bind_pure_comp, `PFunctor.FreeM.map_bind]
      let thms := ctx.simpTheorems.map fun t =>
        erased.foldl (init := t) fun acc nm => acc.eraseCore (.decl nm)
      pure (ctx.setSimpTheorems thms)
    else
      pure ctx
  let simprocs := #[← simprocExt.getSimprocs, ← Simp.getSimprocs]
  let preState ← saveState
  match ← Lean.Meta.simpAll goal ctx simprocs with
  | (none, _) =>
    if ← goalMVars.toList.anyM fun m => not <$> m.isAssignedOrDelayedAssigned then
      preState.restore
      throwError "polytime simp dropped goal metavariables"
    replaceMainGoal []
  | (some newGoal, _) =>
    if newGoal == goal then
      throwError "polytime simp left goal unchanged"
    if closedPPT then
      -- `Lean.Meta.simpAll` cannot clear a rewritten hypothesis whose fvar still sits in an
      -- unassigned metavariable's local context, so it leaves the old hypothesis and appends a
      -- simplified copy; drop newly appended duplicates and detect no-op passes.
      let collectDecls (m : MVarId) : MetaM (Array (FVarId × Expr × Option Expr)) :=
        m.withContext do
          let mut out := #[]
          for d in ← getLCtx do
            unless d.isImplementationDetail do
              let t ← instantiateMVars d.type
              let v ← d.value?.mapM instantiateMVars
              out := out.push (d.fvarId, t, v)
          return out
      let oldDecls ← collectDecls goal
      let oldPairs := oldDecls.map fun (_, t, v) => (t, v)
      let mut cleanedGoal := newGoal
      let mut seenNew : Array (Expr × Option Expr) := #[]
      let mut dupIds : Array FVarId := #[]
      for (fid, t, v) in ← collectDecls newGoal do
        let pair := (t, v)
        let oldCount := oldPairs.foldl (init := (0 : Nat)) fun c p => if p == pair then c + 1 else c
        let seenCount := seenNew.foldl (init := (0 : Nat)) fun c p => if p == pair then c + 1 else c
        if seenCount < max 1 oldCount then
          seenNew := seenNew.push pair
        else
          dupIds := dupIds.push fid
      for fid in dupIds.reverse do
        cleanedGoal ← cleanedGoal.tryClear fid
      let oldType ← instantiateMVars (← goal.getType)
      let newType ← cleanedGoal.withContext do instantiateMVars (← cleanedGoal.getType)
      if oldType == newType then
        let newPairs := (← collectDecls cleanedGoal).map fun (_, t, v) => (t, v)
        let sameSet :=
          newPairs.all (fun p => oldPairs.any (· == p)) &&
          oldPairs.all (fun p => newPairs.any (· == p))
        if sameSet then
          preState.restore
          throwError "polytime simp left goal unchanged"
      replaceMainGoal [cleanedGoal]
    else
      replaceMainGoal [newGoal]

open Lean Meta Elab Tactic in
/-- Normalize side goals with full `simp_all`, while preserving reducible wrappers, projections,
and `match`/`let` terms on efficiency goals until certificates and composition have tried. -/
@[aesop norm 10 tactic (rule_sets := [PolyTime])]
private meta def polytimeNormSimp : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  polytimeSimpAll (isEfficiencyGoal target)

open Lean Meta Elab Tactic in
/-- Fallback full `simp_all` on an efficiency goal only after un-normalized certificates, local
calls, `fun_prop`, and structural rules have failed. -/
@[aesop unsafe 10% tactic (rule_sets := [PolyTime])]
private meta def polytimeSimpFallback : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless isEfficiencyGoal target do throwError "expected an efficiency goal"
  polytimeSimpAll false

-- Keep inexpensive structural successes and failures when no local certificate competes.
-- Aesop postpones safe rules that assign encoding metavariables. Complementary guards avoid
-- duplicating those alternatives while retaining decomposition if a local certificate fails.
@[aesop safe -25 tactic (rule_sets := [PolyTime])]
private meta def polytimeConstructFast : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    polytimeConstruct withoutLocalCall

@[aesop safe -20 tactic (rule_sets := [PolyTime])]
private meta def polytimeFunPropFast : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    if (← plainConditionalRules? (← Lean.Elab.Tactic.getMainTarget)).isSome then
      throwError "conditional alternatives precede generic composition"
    withoutLocalCall polytimeFunProp

@[aesop safe 50 tactic (rule_sets := [PolyTime])]
private meta def polytimeFoldFast : Lean.Elab.Tactic.TacticM Unit :=
  polytimeFold withoutLocalCall

@[aesop safe tactic (rule_sets := [PolyTime])]
private meta def polytimeIterateFast : Lean.Elab.Tactic.TacticM Unit :=
  polytimeIterate withoutLocalCall

@[aesop unsafe 95% tactic (rule_sets := [PolyTime])]
private meta def polytimeConstructAlternative : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    polytimeConstruct withLocalCall

@[aesop unsafe 90% tactic (rule_sets := [PolyTime])]
private meta def polytimeFunPropAlternative : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    if (← plainConditionalRules? (← Lean.Elab.Tactic.getMainTarget)).isSome then
      polytimeFunProp
    else
      withLocalCall polytimeFunProp

@[aesop unsafe 85% tactic (rule_sets := [PolyTime])]
private meta def polytimeFoldAlternative : Lean.Elab.Tactic.TacticM Unit :=
  polytimeFold withLocalCall

@[aesop unsafe 85% tactic (rule_sets := [PolyTime])]
private meta def polytimeIterateAlternative : Lean.Elab.Tactic.TacticM Unit :=
  polytimeIterate withLocalCall

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
private meta def Internal.unfoldEncodingLets : TacticM Unit := withMainContext do
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
private meta def Internal.exposeFieldCertificates : TacticM Unit := withMainContext do
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
meta def Internal.prepareGoal (hints : Array Ident) : TacticM Unit := do
  unless hints.isEmpty do
    evalTactic (← `(tactic| unfold $hints*))
  liftMetaTactic1 fun goal => do
    goal.replaceTargetDefEq (← zetaReduce (← instantiateMVars (← goal.getType))
      (zetaDelta := !hints.isEmpty))
  Internal.unfoldEncodingLets
  Internal.exposeFieldCertificates

/-- Prove a polynomial-time certificate from known routines and controlled loop rules.

`polytime [f, g]` first unfolds the definitions `f` and `g` in the goal. Before searching, every
form also replaces local encoding `let`s (`let E := encPair encUnary encBits`) by their values
and adds the certificates stored in fields of local structures, such as `S.encrypt_ppt` for a
scheme `S` or `h.guess` for an admissibility hypothesis `h`, as local facts. -/
-- Unfold only reducible aliases when comparing assumptions. Ordinary program definitions may
-- contain large fixed enumerations; their named certificates should be tried before unfolding.
syntax (name := polytimeTactic) "polytime" (" [" ident,* "]")? : tactic

open Lean Elab Tactic in
/-- Elaborate `polytime`: prepare the goal, then search with the `PolyTime` Aesop rule set. -/
@[tactic polytimeTactic] meta def evalPolytime : Tactic := fun stx => do
  let hints := match stx with
    | `(tactic| polytime [$hints,*]) => hints.getElems
    | _ => #[]
  withMainContext do Internal.prepareGoal hints
  Internal.withFailureHint "polytime" <| Internal.withPlainRuleCache do
    evalTactic (← `(tactic| solve |
      aesop
        (config :=
          { terminal := true
            enableSimp := false
            assumptionTransparency := .reducible })
        (rule_sets := [PolyTime])))

end Cslib.Tactic.PolyTime
