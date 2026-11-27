/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Logics.Propositional.CNF.StdSat

/-! # Reading and writing DIMACS CNF

The DIMACS CNF format of SAT solvers and benchmarks: a header `p cnf V C` giving the number of
variables and clauses, then the clauses, each a list of nonzero integers ended by `0`, the integer
`i` standing for variable `|i|`, negated if `i < 0`. Lines starting with `c` are comments.

`Cslib.Logic.PL.CNF.ofDIMACS` reads a formula, numbering the variables as the LRAT checker does
(`Cslib.Logic.PL.Literal.ofDIMACS`): the DIMACS variable `v` is the variable `v - 1`, so that a
certificate for the formula read refers to the same variables as the file. It checks the header:
the literals are within its number of variables and the clauses are as many as it says. As in
the SATLIB benchmarks, a line `%` ends the formula.

`Cslib.Logic.PL.CNF.toDIMACS` writes a formula with Lean's `Std.Sat.CNF.dimacs`, which numbers
the variables from `1` in the same way. Reading what it writes gives the formula back on the
examples of the tests, PHP(4, 3) and a formula with an empty clause and a repeated literal; this is
checked on those examples, not proved in general.

The parser is not verified: what it reads is the formula the solver's theorems are about, and a
certificate is checked against it.

## Main definitions

* `Cslib.Logic.PL.CNF.ofDIMACS`: reading a formula.
* `Cslib.Logic.PL.CNF.toDIMACS`: writing a formula.
-/

@[expose] public section

namespace Cslib.Logic.PL

/-- **Reading a DIMACS CNF formula**, with the DIMACS variable `v` as the variable `v - 1`. Fails
on a missing or malformed header, a token that is not an integer, a literal beyond the number of
variables of the header, an unterminated last clause, or a number of clauses other than the
header's. A line starting with `%` ends the formula, as in the SATLIB benchmarks. -/
def CNF.ofDIMACS (s : String) : Except String (CNF ℕ) := do
  let mut header : Option (ℕ × ℕ) := none
  let mut clauses : Array (Clause ℕ) := #[]
  let mut cur : Array (Literal ℕ) := #[]
  for line in s.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "c" then continue
    if line.startsWith "%" then break
    let tokens := (line.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty)
    if line.startsWith "p" then
      if header.isSome then throw "DIMACS: a second header"
      match tokens with
      | ["p", "cnf", v, c] =>
        match v.toNat?, c.toNat? with
        | some v, some c => header := some (v, c)
        | _, _ => throw s!"DIMACS: malformed header '{line}'"
      | _ => throw s!"DIMACS: malformed header '{line}'"
      continue
    let some (nvars, _) := header | throw "DIMACS: a clause before the header"
    for tok in tokens do
      let some i := tok.toInt? | throw s!"DIMACS: '{tok}' is not an integer"
      match Literal.ofDIMACS i with
      | none =>
        clauses := clauses.push cur.toList
        cur := #[]
      | some l =>
        if nvars ≤ l.1 then throw s!"DIMACS: the literal {i} exceeds the {nvars} variables"
        cur := cur.push l
  let some (_, nclauses) := header | throw "DIMACS: no header"
  unless cur.isEmpty do throw "DIMACS: the last clause is not ended by 0"
  unless clauses.size = nclauses do
    throw s!"DIMACS: {clauses.size} clauses, but the header says {nclauses}"
  return clauses.toList

/-- **Writing a DIMACS CNF formula**, by `Std.Sat.CNF.dimacs`: the variable `v` as the DIMACS
variable `v + 1`. -/
def CNF.toDIMACS (φ : CNF ℕ) : String := φ.toStdSat.dimacs

end Cslib.Logic.PL
