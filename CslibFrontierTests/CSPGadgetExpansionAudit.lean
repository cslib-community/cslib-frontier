/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Expansion
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! Adapt the existing construction audit to every stored declaration in the expansion delta,
including private/generated declarations and the original pointwise instantiation equation.
This checks standard axioms, public Init reachability, and the environment linters. -/

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let env := (← getEnv).setExporting false
  if (env.find? `Cslib.Complexity.CSP.computableInPolyTime_replaceGadgets).isSome then
    throwError "expansion audit: native compilation leaked across the mathematical import boundary"
  let targets : List Name :=
    [`CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Replacement,
     `CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.ExpansionSymbols,
     `CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Expansion,
     `CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.ExpansionNames,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.GadgetTransport,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ExpansionProbe,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Expansion]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut modules := 0
  let mut decls : Array Name := #[]
  let mut publicImports : NameMap (Array Name) := {}
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    publicImports := publicImports.insert moduleName <|
      data.imports.filter (·.isExported) |>.map (·.module)
    if targets.contains moduleName then
      modules := modules + 1
      unless data.constNames.size == data.constants.size do
        throwError "expansion audit: malformed declaration table for {moduleName}"
      for name in data.constNames do
        unless (env.find? name).isSome do
          throwError "expansion audit: unavailable stored declaration {name}"
        let axioms ← collectAxioms name
        let disallowed := axioms.filter fun ax => !allowed.contains ax
        unless disallowed.isEmpty do
          throwError "expansion audit: {name} depends on {disallowed}"
        decls := decls.push name
  unless modules == targets.length && !decls.isEmpty do
    throwError "expansion audit: expected {targets.length} owned modules; found {modules}"
  -- Each visited module contributes its public outgoing edges once. The total number
  -- of all loaded import edges bounds the worklist, including repeated queued names.
  let edgeFuel := env.header.moduleData.foldl (fun n data => n + data.imports.size) 1
  for target in targets do
    let mut pending : List Name := [target]
    let mut visited : NameSet := {}
    let mut found := false
    for _ in [:edgeFuel] do
      match pending with
      | [] => break
      | name :: rest =>
        pending := rest
        if name == `Cslib.Init then
          found := true
          break
        unless visited.contains name do
          visited := visited.insert name
          pending := ((publicImports.find? name).getD #[]).toList ++ pending
    unless found do
      throwError "expansion audit: {target} does not publicly import Cslib.Init"
  let checks ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let results ← liftCoreM <| lintCore decls checks
  for (linter, failures) in results do
    for (name, message) in failures.toList do
      throwError "expansion audit: {linter.name}: {name}: {message}"
