/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Languages.Probabilistic.QueryCount.Demand
import Mathlib.Data.Fintype.BigOperators

/-!
# A handler with off-diagonal demand

Two calls on the first source channel and three on the second become eleven calls on the
first target channel and four on the second. A second handler swaps the channels.
-/

namespace CslibFrontierTests.OracleChannelDemand

open Cslib Cslib.OracleComp

private abbrev Spec := fun _ : Bool => Unit

private def calls : List Bool → OracleComp Spec Unit
  | [] => pure ()
  | q :: qs => query (spec := Spec) q >>= fun _ => calls qs

private def charge (j q : Bool) : ℕ := if q = j then 1 else 0

private theorem bound (qs : List Bool) (j : Bool) :
    IsCostBounded (charge j) (calls qs) (qs.count j) := by
  induction qs with
  | nil => exact .pure () 0
  | cons q qs ih =>
    simpa [calls, List.count_cons, charge, beq_iff_eq] using
      (IsCostBounded.liftBind (cost := charge j) q (fun _ : Unit => calls qs) (qs.count j)
        (fun _ => ih))

private def expand (q : Bool) := if q then [false, false, false] else [false, true, true]

private def d (q j : Bool) := (expand q).count j

private theorem perCall (q j : Bool) :
    IsCostBounded (charge j) (calls (expand q)) (∑ i, charge i q * d i j) := by
  cases q <;> cases j <;> simpa [Fintype.sum_bool, charge, d] using bound (expand _) _

private def source := [false, false, true, true, true]

example (j : Bool) :
    IsCostBounded (charge j) (interpret (fun q => calls (expand q)) (calls source))
      (if j then 4 else 11) := by
  have h := IsCostBounded.interpret_demand charge charge d (fun q => calls (expand q))
    perCall (bound source) j
  cases j <;> simpa [Fintype.sum_bool, source, d, expand] using h

-- Count the actual calls as well: dropping a call would still satisfy either upper bound.
private def countCalls (q : Bool) : StateM (ℕ × ℕ) Unit := fun (left, right) =>
  ((), if q then (left, right + 1) else (left + 1, right))

example : (interpret countCalls
    (interpret (fun q => calls (expand q)) (calls source))).run (0, 0) = ((), (11, 4)) := by
  simp only [StateT.run, expand, source, calls, bind_pure_comp, id_map', interpret_bind,
    interpret_query, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  rfl

example : (interpret countCalls (interpret (fun q => calls [!q])
    (interpret (fun q => calls (expand q)) (calls source)))).run (0, 0) = ((), (4, 11)) := by
  simp only [StateT.run, calls, bind_pure_comp, id_map', expand, source, interpret_bind,
    interpret_query, Bool.false_eq_true, ↓reduceIte, bind_assoc, Bool.not_false, Bool.not_true]
  rfl

-- The second stage exchanges the channels. Exercise the matrix product on the composed program.
example (j : Bool) :
    IsCostBounded (charge j)
      (interpret (fun q => calls [!q]) (interpret (fun q => calls (expand q)) (calls source)))
      (if j then 11 else 4) := by
  let swap (i k : Bool) := charge k (!i)
  have hs (q k : Bool) : IsCostBounded (charge k) (calls [!q]) (∑ i, charge i q * swap i k) := by
    refine (bound [!q] k).mono ?_
    cases q <;> cases k <;> decide
  have h := IsCostBounded.interpret_interpret_demand charge charge charge d swap
    (fun q => calls (expand q)) (fun q => calls [!q]) perCall hs (bound source) j
  cases j <;> simpa [Fintype.sum_bool, source, d, expand, swap, charge] using h

/-- One source budget controls a distinct price on each natural-number-indexed target channel. -/
public theorem natChannelBound (p : OracleComp (fun _ : Unit => Bool) Bool) (n : ℕ)
    (bounded : p.IsQueryBounded n) (j : ℕ) : IsCostBounded (fun _ : Unit => j + 1)
      (interpret (fun q : Unit => query (spec := fun _ : Unit => Bool) q) p)
      (n * (j + 1)) := by
  have perCall (q : Unit) (k : ℕ) : IsCostBounded (fun _ => k + 1)
      (query (spec := fun _ : Unit => Bool) q) (∑ _i : Unit, 1 * (k + 1)) := by
    simpa using (IsCostBounded.query (spec := fun _ : Unit => Bool) (cost := fun _ => k + 1) q)
  simpa using IsCostBounded.interpret_demand (I := Unit) (J := ℕ) (fun _ _ => 1)
    (fun j _ => j + 1) (fun _ j => j + 1) (budget := fun _ => n)
    (fun q : Unit => query (spec := fun _ : Unit => Bool) q)
    perCall (fun _ => bounded) j

end CslibFrontierTests.OracleChannelDemand
