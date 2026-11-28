/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Defining
import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Gate

/-!
# Tests for the gates and gadgets of the quasilinear formula

Concrete checks, by `decide` on tiny instances, for
`CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Gate`:

* the clauses of a gate (`Gate.clause`) are all satisfied exactly when the gate holds
  (`Gate.forall_clause_iff`), checked for every operation and every assignment of its four
  variables;
* `eqGadget`, `ltGadget`, `addGadget`, `matchGadget` and `tableGadget` computed by evaluating
  their gates in order from an explicit assignment: the gates hold, and the output variable has
  the value the gadget's theorem predicts, in a case where it is `true` and a case where it is
  `false`;
* `bitsVal` and `incDigit` on an all-ones number.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Complexity.CookLevin.Quasilinear.Gate

open Cslib.Complexity.CookLevin.Quasilinear Cslib.Logic.PL

/-! ### The clauses of a gate -/

/-- The clauses of an `and` gate, slot by slot. -/
example : (Gate.mk .and 2 0 1 0).clause 0 = [(2, false), (0, true), (0, true)] ∧
    (Gate.mk .and 2 0 1 0).clause 2 = [(2, true), (0, false), (1, false)] ∧
    (Gate.mk .and 2 0 1 0).clause 3 = [(2, true), (2, false), (2, false)] := by decide

/-- The assignment of the four variables `0, 1, 2, 3` by four bits. -/
def assign (o a b c : Bool) : ℕ → Bool := fun v => if v = 0 then o else if v = 1 then a
  else if v = 2 then b else c

/-- Whether an assignment satisfies a gate directly, from the meaning of its operation. -/
def holdsBool (σ : ℕ → Bool) (g : Gate) : Bool :=
  match g.op with
  | .assert => σ g.a
  | .imp => !σ g.a || σ g.b
  | _ => σ g.out == g.eval σ

/-- Whether all four clauses of a gate are satisfied. -/
def clausesBool (σ : ℕ → Bool) (g : Gate) : Bool :=
  (List.range 4).all fun s => Clause.eval σ (g.clause s)

/-- For every operation and every assignment of `out, a, b, c`, the four clauses of the gate
`⟨op, 0, 1, 2, 3⟩` hold exactly when the gate does. -/
example : ([.and, .or, .xor, .xnor, .not, .mux, .assert, .imp].all fun op =>
    [false, true].all fun o => [false, true].all fun a => [false, true].all fun b =>
      [false, true].all fun c =>
        clausesBool (assign o a b c) ⟨op, 0, 1, 2, 3⟩ ==
          holdsBool (assign o a b c) ⟨op, 0, 1, 2, 3⟩) = true := by decide

/-- A false assertion violates one of its clauses, a true one satisfies all. -/
example : clausesBool (assign false false false false) ⟨.assert, 0, 1, 0, 0⟩ = false ∧
    clausesBool (assign false true false false) ⟨.assert, 0, 1, 0, 0⟩ = true := by decide

/-! ### Gadgets, evaluated gate by gate -/

/-- The assignment obtained from `σ₀` by giving each defining gate, in order, the value of its
operation on the earlier variables. -/
def run (σ₀ : ℕ → Bool) (gs : List Gate) : ℕ → Bool :=
  gs.foldl (fun σ g => Function.update σ g.out (g.eval σ)) σ₀

/-- The assignment that is `true` exactly on a list of variables. -/
def trueOn (vs : List ℕ) : ℕ → Bool := fun v => decide (v ∈ vs)

/-- All clauses of all gates are satisfied. -/
def allHold (σ : ℕ → Bool) (gs : List Gate) : Bool := gs.all (clausesBool σ)

/-- `eqGadget` on the pairs `(1, 2)` and `(3, 4)` with `tt = 0`: equal pairs. -/
example :
    let σ := run (trueOn [0, 1, 2]) (eqGadget 10 0 [(1, 2), (3, 4)])
    allHold σ (eqGadget 10 0 [(1, 2), (3, 4)]) = true ∧ σ (eqOut 10 0 2) = true := by decide

/-- `eqGadget` with the second pair unequal gives `false`; the theorem `eqGadget_out` predicts
both outputs. -/
example :
    let σ := run (trueOn [0, 1, 2, 4]) (eqGadget 10 0 [(1, 2), (3, 4)])
    allHold σ (eqGadget 10 0 [(1, 2), (3, 4)]) = true ∧ σ (eqOut 10 0 2) = false := by decide

/-- The value predicted by `eqGadget_out` is the one computed, on the unequal pairs. -/
example : (run (trueOn [0, 1, 2, 4]) (eqGadget 10 0 [(1, 2), (3, 4)])) (eqOut 10 0 2) =
    decide (∀ p ∈ ([(1, 2), (3, 4)] : List (ℕ × ℕ)),
      (trueOn [0, 1, 2, 4]) p.1 = (trueOn [0, 1, 2, 4]) p.2) := by
  decide

/-- `ltGadget` compares the number with digits `(v₁, v₃) = (true, false)`, which is `1`, with the
one with digits `(v₂, v₄) = (false, true)`, which is `2`: the first is smaller. -/
example :
    let σ := run (trueOn [1, 4]) (ltGadget 10 0 [(1, 2), (3, 4)])
    allHold σ (ltGadget 10 0 [(1, 2), (3, 4)]) = true ∧ σ (ltOut 10 0 2) = true := by decide

/-- The same numbers compared the other way round: `2 < 1` is `false`. -/
example :
    let σ := run (trueOn [2, 3]) (ltGadget 10 0 [(1, 2), (3, 4)])
    allHold σ (ltGadget 10 0 [(1, 2), (3, 4)]) = true ∧ σ (ltOut 10 0 2) = false := by decide

/-- Equal numbers: not smaller. -/
example :
    let σ := run (trueOn [1, 2]) (ltGadget 10 0 [(1, 2), (3, 4)])
    allHold σ (ltGadget 10 0 [(1, 2), (3, 4)]) = true ∧ σ (ltOut 10 0 2) = false := by decide

/-- `addGadget` with `P` (variable `5`) true adds one: `01 + 1 = 10`, digits least significant
first `(true, false)` and `(false, true)`. -/
example :
    let gs := addGadget 10 0 5 6 [(1, 3), (2, 4)]
    let σ := run (trueOn [0, 1, 4, 5]) gs
    allHold σ gs = true ∧ σ (addOut 10 0 2) = true := by decide

/-- It rejects a wrong increment: `01 + 1 ≠ 11`. -/
example :
    let gs := addGadget 10 0 5 6 [(1, 3), (2, 4)]
    let σ := run (trueOn [0, 1, 3, 4, 5]) gs
    allHold σ gs = true ∧ σ (addOut 10 0 2) = false := by decide

/-- With neither flag set the number is kept. -/
example :
    let gs := addGadget 10 0 5 6 [(1, 3), (2, 4)]
    let σ := run (trueOn [0, 1, 3]) gs
    allHold σ gs = true ∧ σ (addOut 10 0 2) = true := by decide

/-- The guarded decrement wraps around at zero: with `Q` (variable `6`) set and `P` clear, `00 - 1`
is `11` modulo `4`, so the second number `11` is accepted and `00` is rejected. -/
example :
    let gs := addGadget 10 0 5 6 [(1, 3), (2, 4)]
    let σ := run (trueOn [0, 3, 4, 6]) gs
    let σ' := run (trueOn [0, 6]) gs
    allHold σ gs = true ∧ σ (addOut 10 0 2) = true ∧
      allHold σ' gs = true ∧ σ' (addOut 10 0 2) = false := by decide

/-- Decrementing a positive number does not wrap: `01 - 1 = 00`, digits `(true, false)` to
`(false, false)`. -/
example :
    let gs := addGadget 10 0 5 6 [(1, 3), (2, 4)]
    let σ := run (trueOn [0, 1, 6]) gs
    allHold σ gs = true ∧ σ (addOut 10 0 2) = true := by decide

/-- `matchGadget`: the literals `(1, true)` and `(2, false)` hold in `{1}`, not in `{1, 2}`. -/
example :
    let gs := matchGadget 10 0 [(1, true), (2, false)]
    allHold (run (trueOn [0, 1]) gs) gs = true ∧ (run (trueOn [0, 1]) gs) (matchOut 10 0 2) = true ∧
    (run (trueOn [0, 1, 2]) gs) (matchOut 10 0 2) = false := by decide

/-- `tableGadget` with `ff = 7`: a pattern matches in `{1, 2}`, none in `{1}`. -/
example :
    let gs := tableGadget 10 0 7 2 [[(1, true), (2, true)], [(1, false)]]
    allHold (run (trueOn [0, 1, 2]) gs) gs = true ∧
      (run (trueOn [0, 1, 2]) gs) (tableOut 10 7 2 2) = true ∧
      (run (trueOn [0, 1]) gs) (tableOut 10 7 2 2) = false := by decide

/-- Exact width: two patterns of `w = 2` literals fill their `2 * w` addresses, so the output
variables of the gates are exactly `β, β + 1, …` (`Defining`), the length is `2 * w * R + R`, and
`tableOut` is the last of them (variable `19`). -/
example :
    let gs := tableGadget 10 0 7 2 [[(1, true), (2, true)], [(1, false), (2, false)]]
    gs.map Gate.out = List.range' 10 gs.length ∧ gs.length = 2 * 2 * 2 + 2 ∧
      gs.getLast? = some ⟨.or, 19, 18, 17, 0⟩ ∧
      tableOut 10 7 2 2 = 19 := by decide

/-- The same exact-width table satisfies `Defining`, by the theorem for it. -/
example : Defining 10 (tableGadget 10 0 7 2 [[(1, true), (2, true)], [(1, false), (2, false)]]) :=
  defining_tableGadget (by decide) (by decide) (by decide)

/-- Unequal widths still evaluate correctly (above) but leave holes: the second pattern has one
literal, so its two gates sit at `14, 15` after the four of the first, and the output variables
are not contiguous. -/
example :
    let gs := tableGadget 10 0 7 2 [[(1, true), (2, true)], [(1, false)]]
    gs.map Gate.out = [10, 11, 12, 13, 14, 15, 18, 19] ∧
      gs.map Gate.out ≠ List.range' 10 gs.length := by decide

/-! ### Binary numbers -/

/-- Adding one to the all-ones number of three digits gives zero modulo `8`. -/
example : bitsVal (incDigit fun _ => true) 3 = 0 := by decide

/-- Subtracting one from zero wraps around to the all-ones number of three digits, `7`. -/
example : bitsVal (decDigit fun _ => false) 3 = 7 := by decide

/-- Subtracting one from `100` gives `011`. -/
example : bitsVal (decDigit fun j => decide (j = 2)) 3 = 3 := by decide

/-- Adding one to `011` gives `100`. -/
example : bitsVal (incDigit fun j => decide (j < 2)) 3 = 4 := by decide

end CslibFrontierTests.Computability.Complexity.CookLevin.Quasilinear.Gate
