/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Inductive

/-! Recursive encoding preflight rejects unsupported declarations before generating an API. -/

namespace CslibFrontierTests.RecursiveInductiveEncodingUnsupported

open Turing.MultiTapeTM

inductive Indexed : ℕ → Type where
  | zero : Indexed 0

/--
error: enc_inductive: `Indexed` has genuine indices; only uniform parameters are supported
-/
#guard_msgs in
enc_inductive badIndexed (n : ℕ) : Indexed n where
  | zero

inductive LargeTree (α : Type 1) : Type 1 where
  | leaf : α → LargeTree α
  | branch : LargeTree α → LargeTree α → LargeTree α

/--
error: enc_inductive: recursive encoding automation currently requires values in `Type`;
  higher-universe value types are not supported
-/
#guard_msgs (whitespace := lax) in
enc_inductive badLargeTree (α : Type 1) (encoding : α ↪ List Bool) : LargeTree α where
  | leaf : encoding
  | branch : _, _

inductive Dependent (α : Type) where
  | mk (n : ℕ) (value : Fin n) : Dependent α

/--
error: enc_inductive: `Dependent.mk` has a field depending on an earlier constructor field; only
  uniform parameter dependencies are supported
-/
#guard_msgs (whitespace := lax) in
enc_inductive badDependent (α : Type) : Dependent α where
  | mk : encUnary, encUnary

inductive Implicit (α : Type) where
  | mk {n : ℕ} (value : α) : Implicit α

/--
error: enc_inductive: `Implicit.mk` has an implicit or instance field, which is not supported
-/
#guard_msgs (whitespace := lax) in
enc_inductive badImplicit (α : Type) (eα : α ↪ List Bool) : Implicit α where
  | mk : encUnary, eα

inductive ProofField (α : Type) : Type where
  | mk (proof : True) : ProofField α

/--
error: enc_inductive: `ProofField.mk` has a proposition field, which is not supported
-/
#guard_msgs (whitespace := lax) in
enc_inductive badProofField (α : Type) : ProofField α where
  | mk : encUnit

inductive Proposition (n : ℕ) : Prop where
  | mk : Proposition n

/--
error: enc_inductive: proposition-valued inductive types are not supported
-/
#guard_msgs in
enc_inductive badProposition (n : ℕ) : Proposition n where
  | mk

mutual
inductive MutualLeft where
  | leaf
  | next : MutualRight → MutualLeft
inductive MutualRight where
  | next : MutualLeft → MutualRight
end

/-- error: enc_inductive: mutual inductive types are not supported -/
#guard_msgs in
enc_inductive badMutual : MutualLeft where
  | leaf
  | next : _

inductive Nested where
  | leaf
  | next : List Nested → Nested

/-- error: enc_inductive: nested recursion is not supported -/
#guard_msgs in
enc_inductive badNested : Nested where
  | leaf
  | next : _

inductive FunctionRecursive where
  | leaf
  | next : (ℕ → FunctionRecursive) → FunctionRecursive

/--
error: enc_inductive: recursive fields must be exactly the same family applied to the unchanged
  uniform parameters; nested or altered-parameter recursion is not supported
-/
#guard_msgs (whitespace := lax) in
enc_inductive badFunction : FunctionRecursive where
  | leaf
  | next : _

inductive Scalar where
  | leaf : ℕ → Scalar
  | next : Scalar → Scalar

/-- error: enc_inductive: a nonrecursive field needs an explicit encoding -/
#guard_msgs in
enc_inductive badScalar : Scalar where
  | leaf : _
  | next : _

inductive Uniform (α : Type) where
  | leaf
  | next : Uniform α → Uniform α

/-- error: enc_inductive: annotate a directly recursive field with `_` -/
#guard_msgs in
enc_inductive badRecursiveChoice (α : Type) : Uniform α where
  | leaf
  | next : encBits

/-- error: enc_inductive: apply `Uniform` to all 1 uniform parameters explicitly -/
#guard_msgs in
enc_inductive badUnapplied (α : Type) : Uniform where
  | leaf
  | next : _

/--
error: enc_inductive: list every constructor of `Uniform` once, in declaration order:
  | leaf | next
-/
#guard_msgs in
enc_inductive badOrder (α : Type) : Uniform α where
  | next : _
  | leaf

-- Failure must leave neither an encoding nor any partially generated stream API.
run_cmd do
  let env ← Lean.getEnv
  for base in ["badIndexed", "badLargeTree", "badDependent", "badImplicit", "badProofField",
      "badProposition",
      "badMutual", "badNested", "badFunction", "badScalar", "badRecursiveChoice", "badUnapplied",
      "badOrder"] do
    for suffix in ["", "TokenEncoding", "_tokens", "_readToken", "_nodes", "_leafSize"] do
      let name := (`CslibFrontierTests.RecursiveInductiveEncodingUnsupported ++
        Lean.Name.mkSimple base).appendAfter suffix
      if env.contains name then throwError "failed enc_inductive emitted {name}"

end CslibFrontierTests.RecursiveInductiveEncodingUnsupported
