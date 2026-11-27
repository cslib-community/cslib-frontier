/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (derive_encoding selection and error tests)

public import CslibFrontierTests.DeriveEncoding

/-! Encoding choices are explicit, scoped, unambiguous, and checked before generation. -/

public section
namespace CslibFrontierTests.DeriveEncodingErrors

open Turing.MultiTapeTM

inductive IntTree where
  | leaf : ℤ → IntTree
  | next : IntTree → IntTree

-- Importing a policy module does not activate its scalar rules.
/--
error: derive_encoding: no encoding rule for ℤ; supply a local embedding, activate a scoped
encoding_rule, or use enc_inductive
-/
#guard_msgs (whitespace := lax) in
derive_encoding badInactivePolicy : IntTree

inductive NatTree where
  | leaf : ℕ → NatTree
  | next : NatTree → NatTree

/--
error: derive_encoding: no encoding rule for ℕ; supply a local embedding, activate a scoped
encoding_rule, or use enc_inductive
-/
#guard_msgs (whitespace := lax) in
derive_encoding badMissing : NatTree

section
/-- A rule whose own embedding argument is unresolved must report its recursive cycle. -/
@[local encoding_rule] def cyclicNatural (candidate : ℕ ↪ List Bool) : ℕ ↪ List Bool := candidate

/--
error: derive_encoding: no encoding rule for ℕ; supply a local embedding, activate a scoped
encoding_rule, or use enc_inductive
  CslibFrontierTests.DeriveEncodingErrors.cyclicNatural:
  derive_encoding: cyclic encoding rules for ℕ
-/
#guard_msgs (whitespace := lax) in
derive_encoding badCyclic : NatTree
end

inductive ScalarTree (α : Type) where
  | leaf : α → ScalarTree α
  | next : ScalarTree α → ScalarTree α

/--
error: derive_encoding: ambiguous local encodings for α: [first, second]; use enc_inductive to
choose each field explicitly
-/
#guard_msgs (whitespace := lax) in
derive_encoding badLocalAmbiguity (α : Type) (first : α ↪ List Bool)
    (second : α ↪ List Bool) : ScalarTree α

section
variable (α : Type) (eα : α ↪ List Bool)

/-- error: derive_encoding: list parameter `α` explicitly before the colon -/
#guard_msgs in
derive_encoding badAmbientType : ScalarTree α
end

section
variable (eNat : ℕ ↪ List Bool)

/-- error: derive_encoding: list parameter `eNat` explicitly before the colon -/
#guard_msgs in
derive_encoding badAmbientEmbedding : NatTree
end

section
attribute [local encoding_rule] encUnary encNat

/--
error: derive_encoding: ambiguous registered encodings for ℕ:
[Turing.MultiTapeTM.encUnary, Turing.MultiTapeTM.encNat]; activate one policy or use enc_inductive
-/
#guard_msgs (whitespace := lax) in
derive_encoding badRegisteredAmbiguity : NatTree
end

section
attribute [local encoding_rule] encUnary

derive_encoding encLocalNatural : NatTree

example (n : ℕ) : encLocalNatural (.leaf n) = frame (false :: encUnary n) := by
  simp [encLocalNaturalTokenEncoding]
end

-- Local scalar registrations expire with their section.
/--
error: derive_encoding: no encoding rule for ℕ; supply a local embedding, activate a scoped
encoding_rule, or use enc_inductive
-/
#guard_msgs (whitespace := lax) in
derive_encoding badExpiredLocal : NatTree

namespace UnaryNaturals
attribute [scoped encoding_rule] encUnary
end UnaryNaturals

-- Reopening the registration namespace restores its scalar rule.
namespace UnaryNaturals
derive_encoding encScopedNatural : NatTree
end UnaryNaturals

section
open scoped UnaryNaturals
derive_encoding encOpenedNatural : NatTree

example (n : ℕ) : encOpenedNatural (.leaf n) = UnaryNaturals.encScopedNatural (.leaf n) := by
  simp [encOpenedNaturalTokenEncoding, UnaryNaturals.encScopedNaturalTokenEncoding]
end

/-- error: encoding_rule: expected an embedding into List Bool, possibly after parameters -/
#guard_msgs in
attribute [local encoding_rule] Nat.succ

private def privateNatural : ℕ ↪ List Bool := encUnary

/--
error: encoding_rule: registered embeddings must be public; use local or scoped registration to
limit their activation
-/
#guard_msgs (whitespace := lax) in
attribute [local encoding_rule] privateNatural

/--
error: derive_encoding: no encoding rule for ℕ; supply a local embedding, activate a scoped
encoding_rule, or use enc_inductive
-/
#guard_msgs (whitespace := lax) in
derive_encoding badPrivateRuleLeak : NatTree

inductive ImportedTerm (n : ℕ) where
  | leaf : DeriveEncoding.Term n → ImportedTerm n
  | next : ImportedTerm n → ImportedTerm n

-- Opening a parent namespace leaves the child's derived encoding rule inactive.
open CslibFrontierTests

/--
error: derive_encoding: no encoding rule for DeriveEncoding.Term n; supply a local embedding,
activate a scoped encoding_rule, or use enc_inductive
-/
#guard_msgs (whitespace := lax) in
derive_encoding badInactiveFamily (n : ℕ) : ImportedTerm n

inductive TreeContainer (α : Type) where
  | leaf : DeriveEncoding.Tree α → TreeContainer α
  | next : TreeContainer α → TreeContainer α

section
open scoped CslibFrontierTests.DeriveEncoding

/--
error: derive_encoding: no encoding rule for DeriveEncoding.Tree α; supply a local embedding,
activate a scoped encoding_rule, or use enc_inductive
  CslibFrontierTests.DeriveEncoding.encTree: derive_encoding: no encoding rule for α; supply a
  local embedding, activate a scoped encoding_rule, or use enc_inductive
-/
#guard_msgs (whitespace := lax) in
derive_encoding badRecursiveMissing (α : Type) : TreeContainer α

attribute [local encoding_rule] encUnary encNat

/--
error: derive_encoding: no encoding rule for DeriveEncoding.Tree ℕ; supply a local embedding,
activate a scoped encoding_rule, or use enc_inductive
  CslibFrontierTests.DeriveEncoding.encTree: derive_encoding: ambiguous registered encodings for ℕ:
  [Turing.MultiTapeTM.encUnary, Turing.MultiTapeTM.encNat];
  activate one policy or use enc_inductive
-/
#guard_msgs (whitespace := lax) in
derive_encoding badRecursiveAmbiguity : TreeContainer ℕ
end

inductive FinTree where
  | leaf : Fin 2 → FinTree
  | next : FinTree → FinTree

section
-- The rule's domain fixes α; the resolver must synthesize its remaining FinEnum instance.
attribute [local encoding_rule] encFinEnum

derive_encoding encInstanceRule : FinTree

example (index : Fin 2) : encInstanceRule (.leaf index) =
    frame (false :: encFinEnum (Fin 2) index) := by
  simp [encInstanceRuleTokenEncoding]
end

inductive Indexed : ℕ → Type where
  | zero : Indexed 0

/--
error: enc_inductive: `Indexed` has genuine indices; only uniform parameters are supported
-/
#guard_msgs in
derive_encoding badIndexed (n : ℕ) : Indexed n

private inductive PrivateTarget where
  | value : Bool → PrivateTarget

/-- error: derive_encoding: target inductive type must be public -/
#guard_msgs in
derive_encoding badPrivateTarget : PrivateTarget

inductive Empty where

/-- error: derive_encoding: inductive types without constructors are not supported -/
#guard_msgs in
derive_encoding badEmpty : Empty

inductive Dependent where
  | mk (n : ℕ) (value : Fin n) : Dependent

/--
error: enc_inductive: `Dependent.mk` has a field depending on an earlier constructor field; only
uniform parameter dependencies are supported
-/
#guard_msgs (whitespace := lax) in
derive_encoding badDependent : Dependent

inductive Mixed where
  | leaf : Bool → ℕ → Mixed
  | next : Mixed → Mixed

section
open scoped Turing.MultiTapeTM.EncodingPolicy.BinaryIntUnaryFin

-- Even after resolving Bool, failure to encode Nat leaves no partial generated API.
/--
error: derive_encoding: no encoding rule for ℕ; supply a local embedding, activate a scoped
encoding_rule, or use enc_inductive
-/
#guard_msgs (whitespace := lax) in
derive_encoding badLaterField : Mixed
end

run_cmd do
  let env ← Lean.getEnv
  for base in ["badInactivePolicy", "badMissing", "badLocalAmbiguity", "badRegisteredAmbiguity",
      "badExpiredLocal", "badInactiveFamily", "badIndexed", "badLaterField", "badCyclic",
      "badEmpty", "badDependent", "badRecursiveMissing", "badRecursiveAmbiguity",
      "badPrivateTarget", "badAmbientType", "badAmbientEmbedding", "badPrivateRuleLeak"] do
    for suffix in ["", "TokenEncoding", "_tokens", "_nodes", "_decoder", "_leaf_field0?"] do
      let name := (`CslibFrontierTests.DeriveEncodingErrors ++
        Lean.Name.mkSimple base).appendAfter suffix
      if env.contains name then throwError "failed derive_encoding emitted {name}"

-- Neither attribute spelling can introduce an import-active global choice.
section
/-- error: encoding_rule: global registration is not supported; use local or scoped -/
#guard_msgs in
attribute [encoding_rule] encNat

/-- error: encoding_rule: global registration is not supported; use local or scoped -/
#guard_msgs in
@[encoding_rule] def rejectedGlobalNatural : ℕ ↪ List Bool := encUnary
end

/--
error: derive_encoding: no encoding rule for ℕ; supply a local embedding, activate a scoped
encoding_rule, or use enc_inductive
-/
#guard_msgs (whitespace := lax) in
derive_encoding badGlobalNatural : NatTree

end CslibFrontierTests.DeriveEncodingErrors
