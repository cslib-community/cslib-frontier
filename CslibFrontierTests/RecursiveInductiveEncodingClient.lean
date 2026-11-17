/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (importing test driver)

import CslibFrontierTests.RecursiveInductiveEncoding
import Lean.Util.CollectAxioms

/-! Importing clients use the generated semantic and native machine APIs without unfolding them. -/

namespace CslibFrontierTests.RecursiveInductiveEncodingClient

open Turing.MultiTapeTM RecursiveInductiveEncoding

example (n : ℕ) {x y : Term n} (h : encTerm n x = encTerm n y) : x = y :=
  (encTerm n).injective h

example (n : ℕ) (x y : Term n) :
    encTerm_add_field0? n (.add x y) = some x := rfl

example (n : ℕ) (value : Formula n) (term : Term n) :
    encFormula_eqZero_payload? n value = some term ↔ value = .eqZero term :=
  encFormula_eqZero_payload?_eq_some_iff n value term

example (n : ℕ) (value : Formula n) : encFormula_and_matches n value = true ↔
    ∃ payload : Formula n × Formula n, value = .and payload.1 payload.2 :=
  encFormula_and_matches_iff n value

example (n : ℕ) : ComputableInDegree (encFormula_eqZero_field0? n) (encFormula n)
    (encOption (encTerm n)) 1 1 := by fun_prop

example (n : ℕ) : ComputableInDegree (encFormula_not_matches n) (encFormula n) encBool 1 0 := by
  fun_prop

example (n : ℕ) : ComputableInPolyTime (encFormula_and_field1? n) (encFormula n)
    (encOption (encFormula n)) := by fun_prop

example (α : Type) (enc : α ↪ List Bool) :
    ComputableInPolyTime (encTree_fork_payload? α enc) (encTree α enc)
      (encOption (encPair (encTree α enc)
        (encPair encBool (encPair (encTree α enc) (encPair enc (encTree α enc)))))) := by
  fun_prop

example {γ : Type} {input : γ ↪ List Bool} (n : ℕ) {left right : γ → Term n}
    (hl : ComputableInPolyTime left input (encTerm n))
    (hr : ComputableInPolyTime right input (encTerm n)) :
    ComputableInPolyTime (fun a => Term.add (left a) (right a)) input (encTerm n) :=
  encTerm_add_polyTime n hl hr

example {γ : Type} {input : γ ↪ List Bool} (n : ℕ) {left right : γ → Term n}
    {T₁ S₁ T₂ S₂ : γ → ℕ}
    (hl : ComputableInO left input (encTerm n) T₁ S₁)
    (hr : ComputableInO right input (encTerm n) T₂ S₂) :
    ComputableInO (fun a => Term.add (left a) (right a)) input (encTerm n)
      (fun a => 2 * (input a).length + T₁ a + T₂ a)
      (fun a => 2 * (input a).length + S₁ a + S₂ a) := encTerm_add_inO n hl hr

example {γ : Type} {input : γ ↪ List Bool} (n : ℕ) {left right : γ → Term n}
    {S₁ S₂ : γ → ℕ}
    (hl : ComputableInSpace left input (encTerm n) S₁)
    (hr : ComputableInSpace right input (encTerm n) S₂) :
    ComputableInSpace (fun a => Term.add (left a) (right a)) input (encTerm n)
      (fun a => 2 * (input a).length + S₁ a + S₂ a) := encTerm_add_inSpace n hl hr

example (word : List Bool) : formulaCodecZero.decode word = none ↔
    ¬ ∃ f, encFormula 0 f = word := formulaCodecZero.decode_eq_none_iff word

example : ComputableInPolyTime treeCodec.decode encBits (encOption (encTree Bool encBool)) :=
  treeCodec.computable

-- Malformed words and constructors without that field both return `none` in this real parser.
example : ComputableInPolyTime
    (fun word => (formulaCodecZero.decode word).elim none (encFormula_and_field1? 0))
    encBits (encOption (encFormula 0)) :=
  formulaCodecZero.computable.optionElimWithInput (ComputableInPolyTime.const none)
    ((encFormula_and_field1?_polyTime 0).comp
      (ComputableInPolyTime.snd encBits (encFormula 0)))

-- Audit both generated declarations (which live in the fixture) and the new library helpers.
-- This catches a sorry or an unexpected axiom hidden behind any generated certificate.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let modules := [
    `CslibFrontierTests.RecursiveInductiveEncoding,
    `CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Recursive,
    `CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.RecursiveParser,
    `CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.RecursiveChild,
    `CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial,
    `CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPair]
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if modules.contains moduleName then
      for name in data.constNames do
        checked := checked + 1
        let axioms ← collectAxioms name
        unless axioms.all allowed.contains do
          throwError "recursive encoding axiom audit: {name} depends on {axioms}"
  unless checked > 0 do throwError "recursive encoding axiom audit found no declarations"

end CslibFrontierTests.RecursiveInductiveEncodingClient
