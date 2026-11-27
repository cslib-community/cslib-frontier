/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Encoding
public import CslibFrontier.Computability.Circuit.Encoding.EvaluationTime

/-!
# Polynomial-time evaluation over a fixed finite semiring

Specializes `CslibFrontier.Computability.Circuit.Encoding.EvaluationTime` to `arithSignature F`
over a fixed finite semiring `F`. One machine evaluates every runtime arithmetic gate list and
input list over `F` using binary wire indices and bounded list lookup, including on malformed gate
lists. This does not certify arithmetic uniformly over growing fields.

## Main results

* `Arithmetic.computableInPolyTime_evalCode`: the total arithmetic evaluator is polynomial-time.
* `Arithmetic.computableInPolyTime_evalOutput`: a binary-indexed output lookup is polynomial-time.

The semantic bridges are `Program.evalCode_code` and `Circuit.eval_eq_getD`.
These runtime certificates are original.
-/

public section

namespace Cslib.Circuits.Arithmetic

open Turing.MultiTapeTM

variable {F α : Type} [Semiring F] [Finite F] {eF : F ↪ List Bool}
  {eIn : α ↪ List Bool}

/-- The input and the entire arithmetic gate list are charged runtime data. The carrier and
scalar encoding are fixed; missing arguments and invalid binary indices use the total default
semantics of `evalCode`. -/
@[fun_prop]
theorem computableInPolyTime_evalCode {x : α → List F}
    {gates : α → List (ArithOp F × List ℕ)}
    (hx : ComputableInPolyTime x eIn (encList eF))
    (hgates : ComputableInPolyTime gates eIn
      (encList (Circuit.encGate (ArithOp.encoding eF)))) :
    ComputableInPolyTime (fun a => evalCode (arithInterpretation F) 0 (x a) (gates a))
      eIn (encList eF) :=
  Circuits.computableInPolyTime_evalCode (σ := arithSignature F) (arithInterpretation F) 0 hx hgates

/-- Read an output from the computed trace without iterating to the numeric value of an
unchecked binary index. -/
@[fun_prop]
theorem computableInPolyTime_evalOutput {x : α → List F}
    {gates : α → List (ArithOp F × List ℕ)} {output : α → ℕ}
    (hx : ComputableInPolyTime x eIn (encList eF))
    (hgates : ComputableInPolyTime gates eIn
      (encList (Circuit.encGate (ArithOp.encoding eF))))
    (houtput : ComputableInPolyTime output eIn encNat) :
    ComputableInPolyTime (fun a =>
      (evalCode (arithInterpretation F) 0 (x a) (gates a)).getD (output a) 0) eIn eF :=
  Circuits.computableInPolyTime_evalOutput (σ := arithSignature F)
    (arithInterpretation F) 0 hx hgates houtput

end Cslib.Circuits.Arithmetic
