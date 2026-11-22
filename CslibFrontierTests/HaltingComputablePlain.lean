/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (ordinary-module computability boundary regression)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import Lean.Exception

/-!
# Plain total-computability clients

The public computability facade must supply its plain bridges and closure laws to ordinary
modules without importing the retired numerical tidy calculus. These clients combine projections,
Boolean computation and pairing, and pair an arbitrary input word with a constant.
-/

open Lean Elab Command in
run_cmd do
  for name in [
      `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.isComputable,
      `Turing.MultiTapeTM.ComputableTidilyInDegree.isComputable,
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime.isComputable,
      `Turing.MultiTapeTM.IsComputable.exists_computableTidilyInTimeAndSpace] do
    if (← getEnv).contains name then
      throwError "The public computability facade imported a retired tidy bridge: {name}"

set_option linter.privateModule false

namespace CslibFrontierTests.HaltingComputablePlain

open Turing.MultiTapeTM

/-- Proof-only normalization is unavailable through an ordinary import of the facade. -/
example : True := by
  fail_if_success
    have hidden := @Turing.MultiTapeTM.Internal.TotalComputability.normalizedMachine
  trivial

/-- Nonconstant projection, composition, conditional and product clients under ordinary imports. -/
example : IsComputable
    (fun p : Bool × Bool => (p.2, if !p.1 then p.2 else false))
    (encPair encBool encBool) (encPair encBool encBool) := by
  have hfirst : IsComputable (Prod.fst : Bool × Bool → Bool)
      (encPair encBool encBool) encBool :=
    (PairEncoding.fst (enc₁ := encBool) (enc₂ := encBool)
      (enc := encPair encBool encBool)).isComputable
  have hsecond : IsComputable (Prod.snd : Bool × Bool → Bool)
      (encPair encBool encBool) encBool :=
    (PairEncoding.snd (enc₁ := encBool) (enc₂ := encBool)
      (enc := encPair encBool encBool)).isComputable
  have hnot : IsComputable Bool.not encBool encBool := IsComputable.of_finite _
  have hfalse : IsComputable (fun _ : Bool × Bool => false)
      (encPair encBool encBool) encBool := (ComputableInPolyTime.const false).isComputable
  exact hsecond.prod ((hnot.comp hfirst).ite hsecond hfalse)

/-- Constant output does not require a finite domain or a bound on the copied word length. -/
example : IsComputable (fun w : List Bool => (w, false)) encBits (encPair encBits encBool) := by
  have hfalse : IsComputable (fun _ : List Bool => false) encBits encBool :=
    (ComputableInPolyTime.const false).isComputable
  exact (isComputable_id encBits).prod hfalse

end CslibFrontierTests.HaltingComputablePlain
