/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Modular.Multiply
public import CslibFrontier.Computability.Circuit.Boolean.Modular.PartialProduct.PolyTime
public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.Reduce.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native modular multiplier generation

Generates the code of `multiply w` directly from its typed circuit definition via typed
`@[fun_prop]` `(·.code)` rules, charging all shifted partial products, balanced carry-save gates,
fallback gates, and the final carry-lookahead adder from unary width.

## Main results

* `Cslib.Circuits.Boolean.Modular.computableInPolyTime_multiply`,
  `Cslib.Circuits.Boolean.Modular.computableCircuitCode_multiply`: uniform native generation of
  `(multiply w).code`.
-/

public section

namespace Cslib.Circuits.Boolean.Modular

open Turing.MultiTapeTM ComputableInPolyTime

/-- Generation is native polynomial-time in unary width, charging the complete binary code. -/
theorem computableInPolyTime_multiply :
    ComputableInPolyTime (fun w => (multiply w).code) encUnary encCode := by
  unfold multiply
  have hwb : ComputableInPolyTime (fun w : ℕ => w) encUnary encNat := unary_to_binary
  apply computableInPolyTime_sumPairs
  · fun_prop
  · exact id'
  · let encQ := Circuit.encWithFinUnary encUnary id
    have hq : ComputableInPolyTime (fun q : Σ w : ℕ, Fin w => q.1) encQ encNat :=
      unary_to_binary.comp (Circuit.computableInPolyTime_withFinUnary_fst (id' (encIn := encQ)))
    simpa only [List.map_ofFn, Function.comp_def] using
      Circuit.computableInPolyTime_ofFn_unary (k := id) id' (by fun_prop)

/-- `@[fun_prop]` rule for `multiply` in typed circuit compositions. -/
@[fun_prop] theorem computableCircuitCode_multiply {α : Type} {enc : α ↪ List Bool}
    {w : α → ℕ} (hw : ComputableInPolyTime w enc encUnary) :
    Circuit.ComputableCircuitCode (fun a => multiply (w a)) enc encOp :=
  Circuit.computableCircuitCode_of_computableInPolyTime
    (computableInPolyTime_multiply.comp hw)

end Cslib.Circuits.Boolean.Modular
