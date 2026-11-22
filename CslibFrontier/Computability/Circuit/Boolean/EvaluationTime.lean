/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Circuit.Encoding.EvaluationTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Circuit.Boolean.Encoding.PolyTime

/-!
# Evaluating De Morgan circuits in polynomial time

`CslibFrontier.Computability.Circuit.Encoding.EvaluationTime` certifies signature-polymorphic
gate-list evaluation (`Cslib.Circuits.evalCode`) over any finite operation set and finite carrier.
This module specializes those certificates to De Morgan circuits (`Boolean.evalOutput`,
`Cslib.Complexity.evalCircuitOutputs`) on raw bit strings (`encBits`).

The typed evaluation certificate accepts any bit list. It pads short lists with `false` and
truncates long lists to the declared input arity before invoking the raw evaluator. Circuit
generation, input preparation, binary wire lookup and evaluation are all included in its cost.

## Main definitions

* `Cslib.Circuits.Boolean.evalOutput`: the value of a wire after evaluating a list of De Morgan
  gates.
* `Cslib.Complexity.evalCircuitOutputs`: evaluate every output listed by a raw circuit code.

## Main results

* `Cslib.Circuits.Circuit.eval_eq_evalOutput`: De Morgan circuit evaluation through
  `Cslib.Circuits.Boolean.evalOutput`.
* `Cslib.Circuits.Circuit.eval_ofList_eq_evalOutput`: typed evaluation on an arbitrary input list
  uses the padded or truncated input word.
* `Cslib.Circuits.Boolean.computableInPolyTime_evalCode`,
  `Cslib.Circuits.Boolean.computableInPolyTime_evalOutput`: evaluation of De Morgan gate lists
  is polynomial-time.
* `Cslib.Complexity.evalCircuitOutputs_code`,
  `Cslib.Complexity.computableInPolyTime_evalCircuitOutputs`: semantic refinement and
  polynomial-time evaluation of every listed circuit output.
* `Cslib.Circuits.Boolean.computableInPolyTime_evalCircuit`: evaluating an efficiently
  generated typed circuit on an efficiently generated input list is polynomial-time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits

variable {n m : ℕ}

namespace Boolean

open Turing.MultiTapeTM ComputableInPolyTime

/-- **Polynomial-time evaluation** of De Morgan gate lists, for input bits and a gate list in the
binary encoding `encGate`, both computed in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_evalCode {γ : Type} {encIn : γ ↪ List Bool}
    {x : γ → List Bool} {gates : γ → List (Op × List ℕ)}
    (hx : ComputableInPolyTime x encIn encBits)
    (hgates : ComputableInPolyTime gates encIn (encList encGate)) :
    ComputableInPolyTime (fun a => evalCode interpretation false (x a) (gates a))
      encIn encBits :=
  listToBits.comp
    (Circuits.computableInPolyTime_evalCode (σ := signature) interpretation false
      (bitsToList.comp hx) hgates)

/-- The value of wire `o` after evaluating the De Morgan gate list `gates` on the input bits `x`:
on the code of a circuit and the number of an output wire, the value of that output
(`Circuit.eval_eq_getD`). -/
def evalOutput (x : List Bool) (gates : List (Op × List ℕ)) (o : ℕ) : Bool :=
  (evalCode interpretation false x gates).getD o false

/-- Output `j` of a De Morgan circuit is `evalOutput` at the number of its output wire. -/
theorem _root_.Cslib.Circuits.Circuit.eval_eq_evalOutput (c : Circuit signature n m)
    (x : Fin n → Bool) (j : Fin m) :
    c.eval interpretation x j = evalOutput (List.ofFn x) c.code.1 (c.outputs j).toNat :=
  c.eval_eq_getD interpretation false x j

/-- **Polynomial-time evaluation** of an output of a De Morgan gate list, for input bits, a gate
list in the binary encoding `encGate` and a binary wire number, all computed in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_evalOutput {γ : Type} {encIn : γ ↪ List Bool}
    {x : γ → List Bool} {gates : γ → List (Op × List ℕ)} {o : γ → ℕ}
    (hx : ComputableInPolyTime x encIn encBits)
    (hgates : ComputableInPolyTime gates encIn (encList encGate))
    (ho : ComputableInPolyTime o encIn encNat) :
    ComputableInPolyTime (fun a => evalOutput (x a) (gates a) (o a)) encIn encBool :=
  Circuits.computableInPolyTime_evalOutput (σ := signature) interpretation false
    (bitsToList.comp hx) hgates ho

/-- Evaluate a typed circuit on an arbitrary bit list by padding or truncating to its input
arity. The output wire is read from the circuit's code at the specified output position. -/
theorem _root_.Cslib.Circuits.Circuit.eval_ofList_eq_evalOutput
    (c : Circuit signature n m) (x : List Bool) (j : Fin m) :
    c.eval interpretation (BitString.ofList n x) j =
      evalOutput ((x ++ List.replicate n false).take n) c.code.1 (c.code.2.getD j.val 0) := by
  rw [Circuit.eval_eq_evalOutput, BitString.ofFn_ofList_eq_take]
  congr 1
  simp [Circuit.code, List.getD_eq_getElem?_getD]

/-- Evaluate an efficiently computed typed circuit on any efficiently computed bit list.
No length premise is needed: missing inputs are `false`, and inputs past the circuit's arity
are ignored. The certificate charges circuit generation, input padding and all evaluation. -/
@[fun_prop] theorem computableInPolyTime_evalCircuit {γ : Type}
    {encIn : γ ↪ List Bool} {c : γ → Σ n, Circuit signature n 1} {x : γ → List Bool}
    (hc : ComputableInPolyTime c encIn (encCircuit 1))
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => (c a).2.eval interpretation (BitString.ofList (c a).1 (x a)) 0)
      encIn encBool := by
  have hview := Boolean.computableInPolyTime_arity_code 1
  have hparts := hview.comp hc
  have hn := hparts.fst'
  have hpad := bitsTakeWithInput (hx.bitsAppend ((bitsReplicate false).comp hn)) hn
  have houtput := listGetD_binary (encA := encNat) 0 hparts.snd'.snd' (const 0)
  simpa only [Circuit.eval_ofList_eq_evalOutput, Fin.val_zero, Function.comp_def] using
    computableInPolyTime_evalOutput hpad hparts.snd'.fst' houtput

end Boolean

end Cslib.Circuits

namespace Cslib.Complexity

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInPolyTime

/-- The raw code of a De Morgan circuit: its gate list and output wire numbers. -/
abbrev CircuitCode : Type := List (Op × List ℕ) × List ℕ

/-- Evaluate all output wires listed in `code.2` after running the gate list `code.1` on `u`. -/
def evalCircuitOutputs (code : CircuitCode) (u : List Bool) : List Bool :=
  evalOutputs interpretation false code u

/-- On the code of a De Morgan circuit, `evalCircuitOutputs` computes the list of output bits. -/
theorem evalCircuitOutputs_code {n m : ℕ} (c : Circuit signature n m) (x : Fin n → Bool) :
    evalCircuitOutputs c.code (List.ofFn x) = List.ofFn (c.eval interpretation x) :=
  c.evalOutputs_code interpretation false x

/-- Evaluating every listed output of a runtime-supplied De Morgan circuit code is polynomial
time. The gate and output lists remain input data under `encCode`. -/
@[fun_prop]
theorem computableInPolyTime_evalCircuitOutputs {α : Type}
    {encIn : α ↪ List Bool} {code : α → CircuitCode} {u : α → List Bool}
    (hcode : ComputableInPolyTime code encIn encCode)
    (hu : ComputableInPolyTime u encIn encBits) :
    ComputableInPolyTime (fun a => evalCircuitOutputs (code a) (u a)) encIn encBits :=
  listToBits.comp
    (Circuits.computableInPolyTime_evalOutputs (σ := signature) interpretation false
      hcode (bitsToList.comp hu))

end Cslib.Complexity
