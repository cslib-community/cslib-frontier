/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DPLL.Trail
public import CslibFrontier.Algorithms.WordRAM.ClauseCode
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Computability.WordRAM.Compile

/-!
# The DPLL solver on the word RAM: encoding and program

This file states the input encoding, the output and the program of a word-RAM version of the DPLL
solver `Cslib.Algorithms.Lean.DPLL.solve`. The program runs the search with an explicit trail
(`Cslib.Algorithms.Lean.DPLL.Trail.run`), one step of it per iteration of its main loop.

## Encoding

A literal `(v, b)` is the word `2 v + b` (`Cslib.Algorithms.WordRAM.ClauseCode.litCode`), and a
clause is its length followed by the codes of its literals
(`Cslib.Algorithms.WordRAM.ClauseCode.encodeClause`), the encoding of the word-RAM Schöning scan.
The input is a bound `N` on the variables, then the clauses
(`Cslib.Algorithms.WordRAM.DPLL.encode`); every variable of the formula must be below `N`.

## Output

The program returns a length-prefixed list (`Cslib.WordRAM.outputList`): `[0]` when the formula
is unsatisfiable, and `[1, σ 0, …, σ (N - 1)]` (as bits) for the model `σ` of the solver otherwise
(`Cslib.Algorithms.WordRAM.DPLL.answerWords`).

## Memory

With the input of length `L` at addresses `1, …, L`, the clauses occupy `[2, T)` for `T = L + 1`.
After them come three arrays, all initially zero since word-RAM memory starts at zero
(`Cslib.WordRAM.Data.init`):

* the literal array at `T`: the cell `T + 2 v + b` holds `1` when the literal `(v, b)` is on the
  trail, and `0` otherwise;
* the trail at `T + 2 N`: two words per entry, the code of its literal and `1` for a second
  branch, `0` for a first;
* the output at `T + 4 N`.

## One step of the search

One pass over the clauses (`Cslib.Algorithms.WordRAM.DPLL.scan`) finds whether a clause is
falsified, whether every clause has a true literal, the first unit clause whose literal is not
on the trail, and the variable of the first literal occurrence that the trail leaves open. Then
the step backtracks on a falsified clause, writes the model when every clause is satisfied, and
otherwise pushes the literal of the unit clause or the open variable, true first.

## Main definitions

* `Cslib.Algorithms.WordRAM.DPLL.encode`, `Cslib.Algorithms.WordRAM.DPLL.answerWords`: the input
  and the output.
* `Cslib.Algorithms.WordRAM.DPLL.solver`, `Cslib.Algorithms.WordRAM.DPLL.program`: the solver, as
  a structured program and as a flat program returning its output list.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.DPLL

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Algorithms.WordRAM.ClauseCode
open Cslib.Algorithms.Lean.DPLL

/-! ### Encoding -/

/-- The input of the solver: the bound `N` on the variables, then the clauses of `φ`. -/
def encode (N : ℕ) (φ : CNF ℕ) : List ℕ := N :: φ.flatMap encodeClause

/-- The output of the solver: `[0]` for an unsatisfiable formula, and `1` followed by the bits
of the solver's model on the variables below `N` otherwise. -/
def answerWords (N : ℕ) (φ : CNF ℕ) : List ℕ :=
  match solve φ with
  | .sat σ => 1 :: (List.range N).map fun x => (σ x).toNat
  | .unsat _ => [0]

/-! ### Registers -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 32 := 0
/-- Constant `1`. -/
abbrev one : Fin 32 := 1
/-- Constant `2`. -/
abbrev two : Fin 32 := 2
/-- Base of the literal array, which is also the end of the clauses. -/
abbrev tb : Fin 32 := 3
/-- End of the refutation log, in the variant that writes the search tree
(`Cslib.Algorithms.WordRAM.DPLL.programLog`). -/
abbrev lg : Fin 32 := 4
/-- Base of the trail. -/
abbrev sb : Fin 32 := 5
/-- Top of the trail: the address after its last entry. -/
abbrev tp : Fin 32 := 6
/-- Address of the output. -/
abbrev ob : Fin 32 := 7
/-- The bound `N` on the variables. -/
abbrev nv : Fin 32 := 8
/-- End of the clauses. -/
abbrev cend : Fin 32 := 9
/-- Address of the current clause. -/
abbrev ptr : Fin 32 := 10
/-- Length of the current clause. -/
abbrev len : Fin 32 := 11
/-- Address of the current literal. -/
abbrev lptr : Fin 32 := 12
/-- End address of the current clause. -/
abbrev lend : Fin 32 := 13
/-- The current literal code. -/
abbrev code : Fin 32 := 14
/-- The code of its negation. -/
abbrev ncode : Fin 32 := 15
/-- Whether the current literal is on the trail. -/
abbrev vl : Fin 32 := 16
/-- Whether its negation is on the trail. -/
abbrev vn : Fin 32 := 17
/-- Scratch address. -/
abbrev addr : Fin 32 := 18
/-- The current variable. -/
abbrev var : Fin 32 := 19
/-- The number of literals of the current clause not falsified so far. -/
abbrev cnt : Fin 32 := 20
/-- The code of the last such literal. -/
abbrev uc : Fin 32 := 21
/-- Whether the current clause has a true literal so far. -/
abbrev sat : Fin 32 := 22
/-- Whether a falsified clause was found. -/
abbrev conf : Fin 32 := 23
/-- Whether every clause so far has a true literal. -/
abbrev alls : Fin 32 := 24
/-- Whether a unit clause was found. -/
abbrev uf : Fin 32 := 25
/-- The code of the literal of the first unit clause. -/
abbrev unit : Fin 32 := 26
/-- Whether an open variable was found. -/
abbrev opf : Fin 32 := 27
/-- The first open variable. -/
abbrev ov : Fin 32 := 28
/-- Whether the search goes on. -/
abbrev go : Fin 32 := 29
/-- Output address. -/
abbrev out : Fin 32 := 30
/-- Whether backtracking keeps popping. -/
abbrev aux : Fin 32 := 31

end Reg

open Reg

/-! ### The scan of the clauses -/

/-- One literal: count it when it is not falsified, recording its code. Such a literal is true,
which is recorded, or its variable is open, which is recorded as the first open one when none was
found before. -/
def litBody : Code .standard 32 := ram[
  code ← *lptr; addr ← tb + code; vl ← *addr; ncode ← code ^^^ one; addr ← tb + ncode;
  vn ← *addr;
  if vn = zero then [
    cnt ← cnt + one; uc ← code;
    if vl = one then [ sat ← one ] else [
      if opf = zero then [ opf ← one; ov ← code >>> one ] else [ opf ← opf ] ] ]
  else [ cnt ← cnt ];
  lptr ← lptr + one ]

/-- The literals in `[lptr, lend)`. -/
def litLoop : Code .standard 32 := .loop (.lt lptr lend) litBody

/-- After a clause: record a falsified clause, a clause without a true literal, and the first
unit clause whose literal is not on the trail; move to the next clause. -/
def clauseEnd : Code .standard 32 := ram[
  if cnt = zero then [ conf ← one ] else [
    if cnt = one then [
      if uf = zero then [
        addr ← tb + uc; addr ← *addr;
        if addr = zero then [ uf ← one; unit ← uc ] else [ uf ← uf ] ]
      else [ uf ← uf ] ]
    else [ uf ← uf ] ];
  if sat = zero then [ alls ← zero ] else [ alls ← alls ];
  ptr ← lend ]

/-- One clause. -/
def clauseBody : Code .standard 32 := ram[
  len ← *ptr; lptr ← ptr + one; lend ← lptr + len; cnt ← zero; uc ← zero; sat ← zero;
  ⟪litLoop⟫; ⟪clauseEnd⟫ ]

/-- The clauses in `[ptr, cend)`. -/
def clauseLoop : Code .standard 32 := .loop (.lt ptr cend) clauseBody

/-- **The scan** of the clauses against the trail. -/
def scan : Code .standard 32 := ram[
  ptr ← two; conf ← zero; alls ← one; uf ← zero; unit ← zero; opf ← zero; ov ← zero;
  ⟪clauseLoop⟫ ]

/-! ### Steps -/

/-- Pop a second branch from the top of the trail, clearing its literal; stop at a first branch
or an empty trail. -/
def popBody : Code .standard 32 := ram[
  if sb < tp then [
    addr ← tp - one; addr ← *addr;
    if addr = one then [ tp ← tp - two; code ← *tp; addr ← tb + code; *addr ← zero ]
    else [ aux ← zero ] ]
  else [ aux ← zero ] ]

/-- Pop the second branches on top of the trail. -/
def popLoop : Code .standard 32 := .loop (.eq aux one) popBody

/-- Stop with the output `[0]`. -/
def outUnsat : Code .standard 32 := ram[
  *ob ← one; addr ← ob + one; *addr ← zero; out ← ob; go ← zero ]

/-- **Backtracking**: pop the second branches, then turn the first branch on top into its second
branch, or stop with `[0]` when the trail is empty. -/
def backtrack : Code .standard 32 := ram[
  aux ← one; ⟪popLoop⟫;
  if sb < tp then [
    addr ← tp - two; code ← *addr; ncode ← tb + code; *ncode ← zero; ncode ← code ^^^ one;
    vl ← tb + ncode; *vl ← one; *addr ← ncode; addr ← addr + one; *addr ← one ]
  else [ ⟪outUnsat⟫ ] ]

/-- **Branching**: push the literal of the unit clause, or the first open variable, true, as a
first branch. -/
def push : Code .standard 32 := ram[
  if uf = zero then [ code ← ov + ov; code ← code + one ] else [ code ← unit ];
  *tp ← code; addr ← tp + one; *addr ← zero; tp ← tp + two; addr ← tb + code; *addr ← one ]

/-- One bit of the model: the literal array cell of the variable, true. -/
def outBody : Code .standard 32 := ram[
  addr ← var + var; addr ← addr + one; addr ← tb + addr; vl ← *addr; addr ← ob + var;
  addr ← addr + two; *addr ← vl; var ← var + one ]

/-- Stop with the output `[1, σ 0, …, σ (N - 1)]`. -/
def outSat : Code .standard 32 := ram[
  addr ← nv + one; *ob ← addr; addr ← ob + one; *addr ← one; var ← zero;
  ⟪.loop (.lt var nv) outBody⟫; out ← ob; go ← zero ]

/-- **One step of the search.** -/
def stepBody : Code .standard 32 := ram[
  ⟪scan⟫;
  if conf = one then [ ⟪backtrack⟫ ] else [
    if alls = one then [ ⟪outSat⟫ ] else [ ⟪push⟫ ] ] ]

/-- The search: steps while `go = 1`. -/
def mainLoop : Code .standard 32 := .loop (.eq go one) stepBody

/-! ### The solver -/

/-- Set up the registers: constants, the end of the clauses, and the three arrays. -/
def setup : Code .standard 32 := ram[
  one ← #1; two ← #2; cend ← *zero; cend ← cend + one; tb ← cend; nv ← *one; addr ← nv + nv;
  sb ← tb + addr; tp ← sb; ob ← sb + addr; go ← one ]

/-- **The DPLL solver** on the input `encode N φ`, leaving the address of its output in `out`. -/
def solver : Code .standard 32 := ram[ ⟪setup⟫; ⟪mainLoop⟫ ]

/-- **The DPLL solver** as a flat program returning its output list. -/
def program : Program .standard 32 := solver.program out

end Cslib.Algorithms.WordRAM.DPLL

end
