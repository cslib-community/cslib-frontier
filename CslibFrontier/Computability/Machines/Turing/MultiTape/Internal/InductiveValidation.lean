/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public meta import Lean.Elab.Command

/-!
# Preflight validation for recursive inductive encodings

`checkRecursiveInductive` checks an applied inductive type and explicit field encoding choices
without emitting declarations. Uniform parameters may be types or values. Recursive positions
are marked by `_`; all other positions require an embedding into Boolean words. Genuine indices,
mutual or nested recursion, implicit fields, proof fields, and fields depending on earlier fields
are rejected. Constructor fields may depend on the uniform parameters.
-/

public meta section

namespace Turing.MultiTapeTM.Internal

open Lean Elab Command Term Meta

/-- The checked input to recursive encoding generation. Every constructor has parallel arrays
of field types and recursion flags, in declaration order. -/
structure RecursiveInductiveInfo where
  /-- The inductive declaration, before application to its uniform parameters. -/
  typeName : Name
  /-- All constructor field types, with the chosen uniform parameters substituted. -/
  fieldTypes : Array (Array Term)
  /-- Whether each field is precisely the applied inductive type being encoded. -/
  recursiveFields : Array (Array Bool)

/-- Look through type abbreviations as well as applications, so an alias cannot hide a nested
occurrence of the family being encoded. -/
private partial def containsFamily (family : Name) (expression : Expr) : MetaM Bool := do
  let expression ← whnf expression
  if expression.isConstOf family then return true
  match expression with
  | .app f a => return (← containsFamily family f) || (← containsFamily family a)
  | .lam _ domain body _ | .forallE _ domain body _ =>
    return (← containsFamily family domain) || (← containsFamily family body)
  | .letE _ type value body _ =>
    return (← containsFamily family type) || (← containsFamily family value) ||
      (← containsFamily family body)
  | .mdata _ body | .proj _ _ body => containsFamily family body
  | _ => return false

/-- Inspect a supported family before selecting field encodings or emitting declarations.
`T` is fully applied to uniform parameters from the current section. The returned field types
contain no constructor-local variables. Shared by the explicit and policy-driven frontends. -/
def inspectRecursiveInductive (T : Term) :
    CommandElabM RecursiveInductiveInfo := runTermElabM fun _ => Term.withoutErrToSorry do
  let target ← Term.elabTerm T none
  Term.synthesizeSyntheticMVarsNoPostponing
  let target ← whnf (← instantiateMVars target)
  let .const typeName levels := target.getAppFn |
    throwErrorAt T "enc_inductive: expected an inductive type applied to its uniform parameters"
  let .inductInfo info ← getConstInfo typeName |
    throwErrorAt T "enc_inductive: `{.ofConstName typeName}` is not an inductive type"
  if info.numIndices != 0 then
    throwErrorAt T "enc_inductive: `{.ofConstName typeName}` has genuine indices; only uniform \
      parameters are supported"
  if info.all.length != 1 then
    throwErrorAt T "enc_inductive: mutual inductive types are not supported"
  if info.numNested != 0 then
    throwErrorAt T "enc_inductive: nested recursion is not supported"
  let parameters := target.getAppArgs
  unless parameters.size == info.numParams && !target.hasMVar do
    throwErrorAt T "enc_inductive: apply `{.ofConstName typeName}` to all {info.numParams} \
      uniform parameters explicitly"
  unless ← isType target do
    throwErrorAt T "enc_inductive: expected a type"
  if ← isProp target then
    throwErrorAt T "enc_inductive: proposition-valued inductive types are not supported"
  unless ← isDefEq (← inferType target) (mkSort (.succ .zero)) do
    throwErrorAt T "enc_inductive: recursive encoding automation currently requires values in \
      `Type`; higher-universe value types are not supported"
  let mut fieldTypes := #[]
  let mut recursiveFields := #[]
  for ctor in info.ctors do
    let c := T
    let ctorType ← inferType (mkAppN (mkConst ctor levels) parameters)
    let types ← forallTelescopeReducing ctorType fun fields result => do
      unless ← isDefEq result target do
        throwErrorAt c "enc_inductive: constructor result does not preserve the uniform parameters"
      let mut earlier := #[]
      let mut types := #[]
      for field in fields do
        unless (← field.fvarId!.getBinderInfo).isExplicit do
          throwErrorAt c "enc_inductive: `{.ofConstName ctor}` has an implicit or instance field, \
            which is not supported"
        let type ← instantiateMVars (← inferType field)
        if earlier.any fun previous => type.containsFVar previous.fvarId! then
          throwErrorAt c "enc_inductive: `{.ofConstName ctor}` has a field depending on an earlier \
            constructor field; only uniform parameter dependencies are supported"
        if ← isProp type then
          throwErrorAt c "enc_inductive: `{.ofConstName ctor}` has a proposition field, which is \
            not supported"
        earlier := earlier.push field
        types := types.push type
      return types
    let mut flags := #[]
    let mut printed := #[]
    for type in types do
      let recursive ← isDefEq type target
      unless recursive do
        if ← containsFamily typeName type then
          throwErrorAt T "enc_inductive: recursive fields must be exactly the same family \
            applied to the unchanged uniform parameters; nested or altered-parameter recursion \
            is not supported"
      flags := flags.push recursive
      printed := printed.push (← PrettyPrinter.delab type)
    fieldTypes := fieldTypes.push printed
    recursiveFields := recursiveFields.push flags
  return { typeName, fieldTypes, recursiveFields }

/-- Check the explicit constructor list and embeddings before generation. Structural inspection
is shared with `derive_encoding`; the explicit command never consults a codec registry. -/
def checkRecursiveInductive (T : Term) (cs : Array Ident) (encss : Array (Array Term)) :
    CommandElabM RecursiveInductiveInfo := do
  let checked ← inspectRecursiveInductive T
  let .inductInfo info ← getConstInfo checked.typeName | throwUnsupportedSyntax
  let expected := info.ctors.map (·.replacePrefix checked.typeName .anonymous)
  unless cs.toList.map (·.getId) == expected do
    throwErrorAt T "enc_inductive: list every constructor of `{.ofConstName checked.typeName}` \
      once, in declaration order:{indentD (" ".intercalate (expected.map fun c => s!"| {c}"))}"
  unless encss.size == cs.size do
    throwErrorAt T "enc_inductive: give a field annotation list for each constructor"
  for c in cs, ctor in info.ctors, types in checked.fieldTypes, encs in encss,
      recursive in checked.recursiveFields do
    unless types.size == encs.size do
      throwErrorAt c "enc_inductive: `{.ofConstName ctor}` has {types.size} explicit field(s), \
        but {encs.size} encoding(s) are listed; give one encoding per field, in order"
    runTermElabM fun _ => Term.withoutErrToSorry do
      for type in types, enc in encs, isRecursive in recursive do
        let placeholder := enc.raw.isOfKind ``Lean.Parser.Term.hole
        if isRecursive then
          unless placeholder do
            throwErrorAt enc "enc_inductive: annotate a directly recursive field with `_`"
        else
          if placeholder then
            throwErrorAt enc "enc_inductive: a nonrecursive field needs an explicit encoding"
          let type ← Term.elabTerm type none
          let embedding ← mkAppM ``Function.Embedding #[type, ← mkAppM ``List #[mkConst ``Bool]]
          discard <| Term.elabTermEnsuringType enc embedding
          Term.synthesizeSyntheticMVarsNoPostponing
  return checked

end Turing.MultiTapeTM.Internal
