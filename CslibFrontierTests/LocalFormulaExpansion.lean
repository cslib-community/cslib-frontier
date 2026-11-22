/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Circuit.Boolean.LocalValueGame.Formula

/-!
A two-node recursion checks absent sources, redirection to a different node, and negation.
The source and depth hypotheses are discharged for every address, including local formulas
other than the node's designated root formula. These are semantic decoder tests.
-/

namespace CslibFrontierTests.LocalFormulaExpansion

open Cslib.Circuits Cslib.Circuits.Boolean
open LocalValueGame FormulaExpansion

private def node (a : Bool) : Formula signature 1 :=
  if a then (Formula.input 0).not else .input 0

private def source (a : Bool) (_ : Fin 1) : Option Bool :=
  if a then some false else none

private theorem equations (a : Bool) :
    a = (node a).eval interpretation (fun i => (source a i).elim false id) := by
  cases a <;> simp [node, source]

private theorem depth_le (a : Bool) : (node a).depth ≤ 1 := by
  cases a <;> decide

private theorem source_lt (a : Bool) (i : Fin 1) (a' : Bool)
    (h : source a i = some a') : a'.toNat < a.toNat := by
  cases a <;> cases a' <;> simp_all [source]

example : (decoder node source).Descends (rank 1 Bool.toNat) :=
  descends node source depth_le source_lt

example (a : Bool) : value source id (root node a) = a :=
  value_root node source id equations a

-- An arbitrary local formula at the false node still reads the absent port as false.
example : value source id ⟨false, (Formula.input 0).not⟩ = true := by decide

-- The recursive input at the true node is a real OR gate with identical child addresses.
example : (decoder node source).op ⟨true, Formula.input 0⟩ = .or ∧
    (decoder node source).child ⟨true, Formula.input 0⟩ false = root node false ∧
    (decoder node source).child ⟨true, Formula.input 0⟩ true = root node false := by decide

-- Correctness applies to all local-formula addresses, rather than just the two roots.
example (a : Address Bool 1) :
    value source id a = (decoder node source).eval (value source id) a :=
  value_eq_eval node source id equations a

end CslibFrontierTests.LocalFormulaExpansion
