/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Propositional.CNF.LRAT
public import CslibFrontier.Algorithms.WordRAM.ClauseCode
public import CslibFrontier.Computability.WordRAM.ListArray
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Computability.WordRAM.Compile

/-!
# An LRAT checker on the word RAM: encoding and program

This file states the input encoding and the program of a word-RAM LRAT checker that agrees with
`Cslib.Logic.PL.CNF.checkLRAT`.

## Encoding

A literal `(v, b)` is the word `2 v + b` (`Cslib.Algorithms.WordRAM.ClauseCode.litCode`), and a
clause is its length followed by the codes of its literals
(`Cslib.Algorithms.WordRAM.ClauseCode.encodeClause`), the encoding the word-RAM Schöning scan
uses. The input is the number of clauses of the
formula, the clauses, then the steps of the certificate
(`Cslib.Algorithms.WordRAM.LRAT.encode`). A step is a tag followed by its fields:

* `0, k, h₁, …, hₖ`: the empty clause with hints `h₁, …, hₖ`;
* `1, i, c, k, h₁, …, hₖ`: the clause `c` (encoded as above) with number `i` and hints;
* `2`: a RAT step;
* `3, k, i₁, …, iₖ`: deletion of the clauses numbered `i₁, …, iₖ`.

The encoding keeps exactly what `checkLRAT` reads: it drops the number of an empty-clause step and
the contents of a RAT step, which the checker rejects, and it encodes a clause of DIMACS integers by
the literals `Cslib.Logic.PL.Clause.ofDIMACS` names, dropping `0`s.

## Memory

With the input of length `L` at addresses `1, …, L`, let `T = L + 1`. The clause numbered `i` is
found through the table cell `T + 2 i`, which holds the address of its encoding (`0` when there is
none); formula clauses and added clauses are both read in place in the input. The literal with
code `c` is true in the current step when the cell `T + 2 c + 1` holds the current step's stamp.
The assignment is indexed by literal rather than by variable because the trail of
`checkLRAT` may hold a literal and its negation at once, when an added clause is a tautology.
The stamp starts at `1` and increases after every accepted step, so the assignment never needs to
be cleared, and since word-RAM memory starts at zero (`Cslib.WordRAM.Data.init`), neither the
table nor the assignment needs to be initialised.

## Main definitions

* `Cslib.Algorithms.WordRAM.LRAT.encode`: the input word list of a formula and a certificate.
* `Cslib.Algorithms.WordRAM.LRAT.checker`, `Cslib.Algorithms.WordRAM.LRAT.program`: the checker,
  as a structured program and as a flat program halting with its answer.

Its correctness and instruction bound are `Cslib.Algorithms.WordRAM.LRAT.program_spec`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.LRAT

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Algorithms.WordRAM.ClauseCode
open Std.Tactic.BVDecide (LRAT.IntAction)

/-! ### Encoding -/

/-- A list of numbers is stored as its length followed by its entries. -/
def encodeNums (l : List ℕ) : List ℕ := l.length :: l

/-- The words of a certificate step; see the module docstring. -/
def encodeAction : LRAT.IntAction → List ℕ
  | .addEmpty _ hints => 0 :: encodeNums hints.toList
  | .addRup i c hints =>
    1 :: i :: encodeClause (Clause.ofDIMACS c.toList) ++ encodeNums hints.toList
  | .addRat .. => [2]
  | .del ids => 3 :: encodeNums ids.toList

/-- The input of the checker: the number of clauses of `φ`, its clauses, and the steps of
`cert`. -/
def encode (φ : CNF ℕ) (cert : Array LRAT.IntAction) : List ℕ :=
  φ.length :: (φ.flatMap encodeClause ++ cert.toList.flatMap encodeAction)

/-! ### Registers -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 28 := 0
/-- Constant `1`. -/
abbrev one : Fin 28 := 1
/-- Constant `2`, the tag of a RAT step. -/
abbrev two : Fin 28 := 2
/-- Constant `3`, the tag of a deletion. -/
abbrev three : Fin 28 := 3
/-- One past the last input address. -/
abbrev endp : Fin 28 := 4
/-- The base `T` of the table and the assignment. -/
abbrev tbase : Fin 28 := 5
/-- The input cursor. -/
abbrev ptr : Fin 28 := 6
/-- The number of formula clauses. -/
abbrev nCl : Fin 28 := 7
/-- Loop counter. -/
abbrev cnt : Fin 28 := 8
/-- A clause number. -/
abbrev id : Fin 28 := 9
/-- A length read from the input. -/
abbrev len : Fin 28 := 10
/-- The stamp of the current step. -/
abbrev stamp : Fin 28 := 11
/-- Output. -/
abbrev out : Fin 28 := 12
/-- The tag of the current step. -/
abbrev tag : Fin 28 := 13
/-- End of the hints of the current step. -/
abbrev hend : Fin 28 := 14
/-- The current hint. -/
abbrev hint : Fin 28 := 15
/-- Scratch address. -/
abbrev addr : Fin 28 := 16
/-- Address of the hinted clause. -/
abbrev cl : Fin 28 := 17
/-- Address of the current literal. -/
abbrev lptr : Fin 28 := 18
/-- End address of the current clause. -/
abbrev lend : Fin 28 := 19
/-- The current literal code. -/
abbrev code : Fin 28 := 20
/-- Scratch value. -/
abbrev val : Fin 28 := 21
/-- Whether a non-false literal was found in the hinted clause. -/
abbrev has : Fin 28 := 22
/-- The non-false literal found. -/
abbrev unit : Fin 28 := 23
/-- Whether two different non-false literals were found. -/
abbrev bad : Fin 28 := 24
/-- The result of unit propagation. -/
abbrev res : Fin 28 := 25
/-- Address of the encoding of the clause added by the current step. -/
abbrev caddr : Fin 28 := 26
/-- The complementary literal code. -/
abbrev ncode : Fin 28 := 27

end Reg

open Reg

/-! ### Unit propagation along hints -/

/-- One literal of a hinted clause: skip it when false, and otherwise record it as the unit, or
note a second, different non-false literal. -/
def litBody : Code .standard 28 := ram[
  code ← *lptr; ncode ← code ^^^ one; addr ← ncode + ncode; addr ← addr + one;
  addr ← tbase + addr; val ← *addr;
  if val = stamp then [ lptr ← lptr + one ] else [
    if has = zero then [ unit ← code; has ← one ] else [
      if unit = code then [ lptr ← lptr ] else [ bad ← one ] ];
    lptr ← lptr + one ] ]

/-- The literals in `[lptr, lend)`. -/
def litLoop : Code .standard 28 := .loop (.lt lptr lend) litBody

/-- Scan the clause at `cl`: its non-false literals are none (`has = 0`), all equal to `unit`
(`has = 1`, `bad = 0`), or not all equal (`bad = 1`). -/
def scanClause : Code .standard 28 := ram[
  len ← *cl; lptr ← cl + one; lend ← lptr + len; has ← zero; unit ← zero; bad ← zero;
  ⟪litLoop⟫ ]

/-- After scanning a hinted clause: a conflict ends propagation with success, a unit is assigned,
and anything else ends propagation with failure. -/
def afterScan : Code .standard 28 := ram[
  if bad = zero then [
    if has = zero then [ res ← one; ptr ← hend ] else [
      addr ← unit + unit; addr ← addr + one; addr ← tbase + addr; *addr ← stamp ] ]
  else [ ptr ← hend ] ]

/-- One hint: look up its clause; a missing clause ends propagation with failure. -/
def hintBody : Code .standard 28 := ram[
  hint ← *ptr; ptr ← ptr + one; addr ← hint + hint; addr ← tbase + addr; cl ← *addr;
  if cl = zero then [ ptr ← hend ] else [ ⟪scanClause⟫; ⟪afterScan⟫ ] ]

/-- The hints in `[ptr, hend)`. -/
def hintLoop : Code .standard 28 := .loop (.lt ptr hend) hintBody

/-- **Unit propagation along the hints** at `ptr`, which start with their number: `res` is `1`
exactly when propagation reaches a conflict, and `ptr` ends past the hints. -/
def propagate : Code .standard 28 := ram[
  len ← *ptr; ptr ← ptr + one; hend ← ptr + len; res ← zero; ⟪hintLoop⟫ ]

/-! ### Steps -/

/-- Assume the negation of a literal of the added clause. -/
def assumeBody : Code .standard 28 := ram[
  code ← *lptr; ncode ← code ^^^ one; addr ← ncode + ncode; addr ← addr + one;
  addr ← tbase + addr; *addr ← stamp; lptr ← lptr + one ]

/-- Assume the negations of the literals in `[lptr, lend)`. -/
def assumeLoop : Code .standard 28 := .loop (.lt lptr lend) assumeBody

/-- Stop the run with output `0`. -/
def reject : Code .standard 28 := ram[ out ← zero; ptr ← endp ]

/-- An empty-clause step: its result is the answer. -/
def emptyStep : Code .standard 28 := ram[ ⟪propagate⟫; out ← res; ptr ← endp ]

/-- A RUP step: assume the negated clause, propagate, and on success record the clause's address
in the table and advance the stamp. -/
def rupStep : Code .standard 28 := ram[
  id ← *ptr; ptr ← ptr + one; caddr ← ptr; len ← *ptr; lptr ← ptr + one; lend ← lptr + len;
  ⟪assumeLoop⟫; ptr ← lend; ⟪propagate⟫;
  if res = zero then [ ⟪reject⟫ ] else [
    addr ← id + id; addr ← tbase + addr; *addr ← caddr; stamp ← stamp + one ] ]

/-- One deleted clause number: clear its table cell. -/
def delBody : Code .standard 28 := ram[
  hint ← *ptr; addr ← hint + hint; addr ← tbase + addr; *addr ← zero; ptr ← ptr + one ]

/-- A deletion step. -/
def delStep : Code .standard 28 := ram[
  len ← *ptr; ptr ← ptr + one; hend ← ptr + len; ⟪.loop (.lt ptr hend) delBody⟫ ]

/-- One step of the certificate, dispatched on its tag. -/
def stepBody : Code .standard 28 := ram[
  tag ← *ptr; ptr ← ptr + one;
  if tag = zero then [ ⟪emptyStep⟫ ] else [
    if tag = one then [ ⟪rupStep⟫ ] else [
      if tag = three then [ ⟪delStep⟫ ] else [ ⟪reject⟫ ] ] ] ]

/-- The steps in `[ptr, endp)`; running out of steps leaves the output `0`. -/
def stepLoop : Code .standard 28 := .loop (.lt ptr endp) stepBody

/-! ### The checker -/

/-- One formula clause: record its address under the next clause number. -/
def loadBody : Code .standard 28 := ram[
  addr ← id + id; addr ← tbase + addr; *addr ← ptr; len ← *ptr; ptr ← ptr + one;
  ptr ← ptr + len; id ← id + one; cnt ← cnt + one ]

/-- Number the `nCl` formula clauses from `1`. -/
def loadLoop : Code .standard 28 := .loop (.lt cnt nCl) loadBody

/-- Set up the registers: constants, the end of the input, the table base, and the cursor at the
first clause. -/
def setup : Code .standard 28 := ram[
  one ← #1; two ← #2; three ← #3; endp ← *zero; endp ← endp + one; tbase ← endp; ptr ← one;
  nCl ← *ptr; ptr ← ptr + one; id ← one; cnt ← zero; stamp ← one; out ← zero ]

/-- **The LRAT checker** on the input `encode φ cert`, leaving its answer in `out`. -/
def checker : Code .standard 28 := ram[ ⟪setup⟫; ⟪loadLoop⟫; ⟪stepLoop⟫ ]

/-- **The LRAT checker** as a flat program halting with `out`. -/
def program : Program .standard 28 := checker.program out

end Cslib.Algorithms.WordRAM.LRAT

end
