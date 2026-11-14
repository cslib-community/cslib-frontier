/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.DegreeTwo
import Lean.Util.CollectAxioms
import ImportGraph

/-! Audit every stored declaration of the new normalization witness modules, including
private/generated declarations, and check their transitive public `Cslib.Init` imports.
This focused ordinary-import client does not depend on the parent-owned root aggregate.
-/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let selected := fun n : Name =>
    (`CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization).isPrefixOf n ||
      n == `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryIdentifyAt ||
      n == `CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.FreshSpoke ||
      n == `CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.DegreeTwo ||
      n == `CslibFrontier.Foundations.Data.BitString.CyclicDifference.BoundaryKernel
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut publicImports : NameMap (Array Name) := {}
  let mut modules := #[]
  let mut declarations := 0
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    publicImports := publicImports.insert moduleName
      (data.imports.filter (·.isExported) |>.map (·.module))
    if selected moduleName then
      modules := modules.push moduleName
      unless data.constNames.size == data.constants.size do
        throwError "normalization audit: malformed module {moduleName}"
      for name in data.constNames do
        declarations := declarations + 1
        unless (env.find? name).isSome do
          throwError "normalization audit: missing stored declaration {name}"
        let axioms ← collectAxioms name
        let disallowed := axioms.filter fun ax => !allowed.contains ax
        unless disallowed.isEmpty do
          throwError "normalization audit: {name} depends on {disallowed}"
  unless modules.size == 10 && declarations > 0 do
    throwError "normalization audit: expected ten nonempty new modules, found {modules}"
  let graph := publicImports.transitiveClosure
  for name in modules do
    unless ((graph.find? name).getD {}).contains `Cslib.Init do
      throwError "normalization audit: {name} does not publicly import Cslib.Init"
  for name in env.header.moduleNames do
    if (`CslibFrontier.Computability.PolyTime.CSP.Gadget.ConstructionCompiler).isPrefixOf name then
      throwError "normalization audit: mathematical endpoint imports runtime compiler {name}"
