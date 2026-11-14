/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.OneHotExpansion
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.CrossoverOriginal
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint
import ImportGraph

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
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Expansion,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Crossover,
     `CslibFrontier.Logics.Propositional.CSP.Planar.OneInThree,
     `CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.ExpansionCrossover,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.CrossoverExpansion,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.OneHotExpansion,
     `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.CrossoverOriginal]
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
  let graph := publicImports.transitiveClosure
  for target in targets do
    unless ((graph.find? target).getD {}).contains `Cslib.Init do
      throwError "expansion audit: {target} does not publicly import Cslib.Init"
  for name in env.header.moduleNames do
    if (`CslibFrontier.Computability.PolyTime.CSP.Gadget.ConstructionCompiler).isPrefixOf name ||
        (`CslibFrontier.Computability.Complexity.FineGrained.CountingCSP).isPrefixOf name then
      throwError "expansion audit: mathematical endpoint imports runtime module {name}"
  let checks ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  let results ← liftCoreM <| lintCore decls checks
  for (linter, failures) in results do
    for (name, message) in failures.toList do
      throwError "expansion audit: {linter.name}: {name}: {message}"
