/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Inductive
public meta import Lean.ScopedEnvExtension

/-!
# Policy-driven inductive encoding derivation

`derive_encoding eT (p : P) : T p` inspects constructors in declaration order, identifies direct
recursion, and calls the checked `enc_inductive` generator. It adds no serializer or proof
pipeline. The selected embeddings determine exactly the explicit command's words and public API.

There are no default field encodings. Open a named policy or register embeddings with
`@[scoped encoding_rule]`. An embedding supplied as a local parameter takes precedence; two
matching local embeddings are an error. Otherwise exactly one active registered rule must apply.
Rule parameters are inferred from the field type; unresolved embedding parameters are resolved
recursively, and instance parameters use Lean's instance synthesis. Other uninferred parameters,
cyclic searches, missing rules and multiple applicable rules are errors. Rules have no priorities.
The attribute accepts only local and scoped registrations on public embeddings.
Successful derivations register their embedding scoped to their namespace.
Importing alone does not activate scoped entries; `open scoped N` activates namespace `N`.

This command generates public declarations and requires a public target inductive and public
encoding rules. It otherwise has the explicit generator's support boundary: small result types,
uniform parameters and ordinary direct recursion. It checks structure and resolves every scalar
field before generation. List all type, value and encoding parameters explicitly before the
colon; ambient section parameters used by a derivation must be listed there too.
Keep `enc_inductive` for complete control over individual fields.
Registered embeddings supply neither bit decoders nor certificates for arbitrary recursion;
generated bit decoders still take explicit `PartialDecoder` witnesses.
-/

public meta section

namespace Turing.MultiTapeTM

open Lean Elab Command Term Meta

namespace Internal

/-- Active named encoding choices, using Lean's standard local/scoped extension semantics. -/
private initialize encodingRules : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun entries name => if entries.contains name then entries else entries.push name
  }

private def encodingDomain? (type : Expr) : MetaM (Option Expr) := do
  let type ← whnf type
  let some (domain, codomain) := type.app2? ``Function.Embedding | return none
  if ← isDefEq codomain (← mkAppM ``List #[mkConst ``Bool]) then return some domain
  return none

end Internal

/-- An explicit field-encoding choice for `derive_encoding`. Use `scoped` for an opt-in namespace
policy or `local` for a section. The public declaration returns an embedding into `List Bool`,
possibly after parameters. Matching never uses declaration order or a priority to resolve
ambiguity. -/
syntax (name := encodingRuleAttr) "encoding_rule" : attr

initialize registerBuiltinAttribute {
  name := `encodingRuleAttr
  descr := "an explicit encoding choice for policy-driven inductive derivation"
  applicationTime := .afterCompilation
  add := fun name _ kind => do
    if kind == .global then
      throwError "encoding_rule: global registration is not supported; use local or scoped"
    if isPrivateName name then
      throwError "encoding_rule: registered embeddings must be public; use local or scoped \
        registration to limit their activation"
    MetaM.run' <| forallTelescopeReducing (← getConstInfo name).type fun _ result => do
      unless (← Internal.encodingDomain? result).isSome do
        throwError "encoding_rule: expected an embedding into List Bool, possibly after parameters"
    Internal.encodingRules.add name kind
}

namespace Internal

private partial def resolveEncoding (domain : Expr) (visited : Array Expr := #[]) : MetaM Expr :=
    withIncRecDepth do
  let domain ← whnf (← instantiateMVars domain)
  if domain.hasMVar then
    throwError "derive_encoding: encoding domain has uninferred parameters: {domain}"
  if visited.contains domain then
    throwError "derive_encoding: cyclic encoding rules for {domain}"
  let expected ← mkAppM ``Function.Embedding #[domain, ← mkAppM ``List #[mkConst ``Bool]]
  let initial ← saveState
  let mut locals : Array (Expr × Meta.SavedState) := #[]
  for localDecl in ← getLCtx do
    if localDecl.isImplementationDetail then continue
    initial.restore
    if ← isDefEq localDecl.type expected then
      locals := locals.push (localDecl.toExpr, ← saveState)
  initial.restore
  if locals.size > 1 then
    throwError "derive_encoding: ambiguous local encodings for {domain}: \
      {locals.map (·.1)}; use enc_inductive to choose each field explicitly"
  if let some (choice, state) := locals[0]? then
    state.restore
    return choice
  let mut choices : Array (Name × Expr × Meta.SavedState) := #[]
  let mut failures : Array String := #[]
  for name in encodingRules.getState (← getEnv) do
    initial.restore
    let constant ← mkConstWithFreshMVarLevels name
    let (arguments, binders, result) ← forallMetaTelescopeReducing (← inferType constant)
    unless ← isDefEq result expected do continue
    try
      for argument in arguments, binder in binders do
        let argument ← instantiateMVars argument
        unless argument.isMVar do continue
        let type ← instantiateMVars (← inferType argument)
        if let some fieldType ← encodingDomain? type then
          let encoding ← resolveEncoding fieldType (visited.push domain)
          argument.mvarId!.assign encoding
        else if binder.isInstImplicit then
          argument.mvarId!.assign (← synthInstance type)
        else
          throwError "uninferred rule parameter of type {type}"
      let expression ← instantiateMVars (mkAppN constant arguments)
      if expression.hasMVar then throwError "uninferred rule parameters"
      choices := choices.push (name, expression, ← saveState)
    catch error =>
      failures := failures.push s!"{name}: {← error.toMessageData.toString}"
  initial.restore
  if choices.size > 1 then
    throwError "derive_encoding: ambiguous registered encodings for {domain}: \
      {choices.map (·.1)}; activate one policy or use enc_inductive"
  if let some (_, expression, state) := choices[0]? then
    state.restore
    return expression
  throwError "derive_encoding: no encoding rule for {domain}; supply a local embedding, \
    activate a scoped encoding_rule, or use enc_inductive\
    {indentD ("\n".intercalate failures.toList)}"

end Internal

/-- Derive and register an encoding using the active explicit policy. Parameter binders and the
generated public interface agree with `enc_inductive`. Constructors and recursion are inferred. -/
syntax (name := deriveEncoding) (docComment)? "derive_encoding " ident
  (" (" ident " : " term ")")* " : " term : command

/-- Resolve the explicit field policy before invoking the checked inductive encoding generator. -/
@[command_elab deriveEncoding] def elabDeriveEncoding : CommandElab := fun stx => do
  let `($[$doc:docComment]? derive_encoding $eT:ident $[($ps:ident : $pts:term)]* : $T:term) := stx
    | throwUnsupportedSyntax
  if (← getCurrNamespace).isAnonymous then
    throwErrorAt eT "derive_encoding: declare the encoding inside a namespace for scoped rules"
  let params ← ps.zip pts |>.mapM fun (p, t) => `(bracketedBinder| ($p:ident : $t))
  elabCommand (← `(section))
  let (cs, encss, bareType?) ← try
    if !params.isEmpty then elabCommand (← `(variable $params*))
    let checked ← Internal.inspectRecursiveInductive T
    if isPrivateName checked.typeName then
      throwErrorAt T "derive_encoding: target inductive type must be public"
    let .inductInfo info ← getConstInfo checked.typeName | throwUnsupportedSyntax
    if info.ctors.isEmpty then
      throwErrorAt T "derive_encoding: inductive types without constructors are not supported"
    let cs := info.ctors.toArray.map fun name =>
      mkIdent (name.replacePrefix checked.typeName .anonymous)
    let encss ← runTermElabM fun _ => Term.withoutErrToSorry do
      let declared ← ps.mapM fun (parameter : Ident) => Term.elabTerm parameter none
      let checkParameters (expression : Expr) : TermElabM Unit := do
        for localDecl in ← getLCtx do
          if expression.containsFVar localDecl.fvarId &&
              !declared.contains localDecl.toExpr then
            throwErrorAt T "derive_encoding: list parameter `{localDecl.userName}` explicitly \
              before the colon"
      checkParameters (← Term.elabTerm T none)
      for parameter in declared do checkParameters (← inferType parameter)
      checked.fieldTypes.zip checked.recursiveFields |>.mapM fun (types, flags) =>
        types.zip flags |>.mapM fun (type, recursive) => do
          if recursive then return ← `(_)
          let domain ← Term.elabTerm type none
          Term.synthesizeSyntheticMVarsNoPostponing
          let encoding ← Internal.resolveEncoding domain
          checkParameters encoding
          PrettyPrinter.delab encoding
    let bareType? := if ps.isEmpty && info.numParams == 0 &&
        !checked.recursiveFields.any (·.any id) then some (mkIdent checked.typeName) else none
    pure (cs, encss, bareType?)
  finally
    elabCommand (← `(end))
  -- The original bare, nonrecursive form keeps its original sum-of-tuples layout and API.
  if let some bareType := bareType? then
    let fields : Array (Option (Syntax.TSepArray `term ",")) := encss.map fun es =>
      if es.isEmpty then none else some (Syntax.TSepArray.ofElems es)
    elabCommand (← `($[$doc:docComment]? enc_inductive $eT:ident : $bareType:ident where
      $[ | $cs:ident $[: $fields:term,*]?]*))
  else
    Internal.elabRecursiveInductive doc eT ps (pts.map (⟨·⟩)) T cs encss
  elabCommand (← `(attribute [scoped encoding_rule] $eT:ident))

end Turing.MultiTapeTM
