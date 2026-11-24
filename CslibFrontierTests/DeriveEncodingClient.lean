/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (derive_encoding importing client)

public import CslibFrontierTests.DeriveEncoding
import CslibFrontierTests.DeriveEncodingErrors
import Lean.Util.CollectAxioms

/-! Imported generated APIs retain scalar selection, native rules and strict decoding. -/

public section
namespace CslibFrontierTests.DeriveEncodingClient

open Turing.MultiTapeTM
open scoped CslibFrontierTests.DeriveEncoding

-- Importing rejected registrations and inactive policies does not choose a Nat encoding.
/-- A family whose scalar encoding must be selected explicitly by this client. -/
inductive UnselectedNatural where
  | value : ℕ → UnselectedNatural

/--
error: derive_encoding: no encoding rule for ℕ; supply a local embedding, activate a scoped
encoding_rule, or use enc_inductive
-/
#guard_msgs (whitespace := lax) in
derive_encoding badImportedGlobal : UnselectedNatural

-- The bare nonrecursive form exposes the original sum-view certificate after import.
example : ComputableInDegree DeriveEncoding.encMessage_toSum DeriveEncoding.encMessage
    DeriveEncoding.encMessagePayload 1 1 := DeriveEncoding.encMessage_toSum_deg

example : ComputableInDegree DeriveEncoding.encParenthesizedMessage_toSum
    DeriveEncoding.encParenthesizedMessage DeriveEncoding.encParenthesizedMessagePayload 1 1 :=
  DeriveEncoding.encParenthesizedMessage_toSum_deg

/-- An importing client reactivates the derived formula family's encoding rule. -/
inductive ImportedFormula (n : ℕ) where
  | atom : DeriveEncoding.Formula n → ImportedFormula n
  | next : ImportedFormula n → ImportedFormula n

derive_encoding encImportedFormula (n : ℕ) : ImportedFormula n

example (n : ℕ) (f : DeriveEncoding.Formula n) :
    encImportedFormula_atom_field0? n (.atom f) = some f := rfl

example (n : ℕ) {x y : DeriveEncoding.Formula n}
    (h : DeriveEncoding.encFormula n x = DeriveEncoding.encFormula n y) : x = y :=
  (DeriveEncoding.encFormula n).injective h

example (n : ℕ) :
    ComputableInDegree (DeriveEncoding.encFormula_ltZero_field0? n)
      (DeriveEncoding.encFormula n) (encOption (DeriveEncoding.encTerm n)) 1 1 := by
  fun_prop

example (n : ℕ) :
    ComputableInPolyTime (DeriveEncoding.encFormula_or_field1? n)
      (DeriveEncoding.encFormula n) (encOption (DeriveEncoding.encFormula n)) := by
  fun_prop

example {γ : Type} {input : γ ↪ List Bool} (n : ℕ)
    {left right : γ → DeriveEncoding.Formula n}
    (hl : ComputableInPolyTime left input (DeriveEncoding.encFormula n))
    (hr : ComputableInPolyTime right input (DeriveEncoding.encFormula n)) :
    ComputableInPolyTime (fun a => DeriveEncoding.Formula.or (left a) (right a)) input
      (DeriveEncoding.encFormula n) := by
  fun_prop

example (value : DeriveEncoding.Formula 0) :
    DeriveEncoding.formulaCodec.decode (DeriveEncoding.encFormula 0 value) = some value :=
  DeriveEncoding.formulaCodec.decode_enc value

example (word : List Bool) : DeriveEncoding.formulaCodec.decode word = none ↔
    ¬ ∃ value, DeriveEncoding.encFormula 0 value = word :=
  DeriveEncoding.formulaCodec.decode_eq_none_iff word

example : ComputableInPolyTime DeriveEncoding.formulaCodec.decode encBits
    (encOption (DeriveEncoding.encFormula 0)) := DeriveEncoding.formulaCodec.computable

-- Audit generated imported declarations rather than only this client's proof terms.
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let modules := [
    `CslibFrontierTests.DeriveEncoding,
    `CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Derive,
    `CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Policy.BinaryIntUnaryFin,
    `CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.InductiveValidation]
  for moduleName in env.header.moduleNames, data in env.header.moduleData do
    if modules.contains moduleName then
      for name in data.constNames do
        checked := checked + 1
        let axioms ← collectAxioms name
        unless axioms.all allowed.contains do
          throwError "derive_encoding axiom audit: {name} depends on {axioms}"
  unless checked > 0 do throwError "derive_encoding axiom audit found no declarations"

end CslibFrontierTests.DeriveEncodingClient
