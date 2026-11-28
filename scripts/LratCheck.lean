/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/
import CslibFrontier.Logics.Propositional.CNF.LRATFile

/-!
# The LRAT checker on files

`lake exe lrat_check FORMULA.cnf PROOF.lrat` reads a DIMACS CNF file and an LRAT proof, text or
binary, and checks the proof with `Cslib.Logic.PL.CNF.checkDIMACSLRAT`: Lean core's LRAT parser
and the array checker `Cslib.Logic.PL.CNF.checkLRATFast`, which checks RUP and RAT steps and
deletions. Both files are read as bytes; the formula must be valid UTF-8 and is decoded with
`String.fromUTF8?`.

Standard output is exactly one verdict line. It is `s VERIFIED UNSAT`, as `cake_lpr` prints, with
exit code `0` when the proof is accepted, and `s REJECTED` with the reason and exit code `1`
otherwise, a formula that is not valid UTF-8 included. A wrong number of arguments or a file that
cannot be read prints a message on standard error, no verdict line, and exits with `2`. A `c` line
on standard error gives the time spent reading the files and checking.

The verdict is correct by `Cslib.Logic.PL.CNF.not_satisfiable_of_checkDIMACSLRAT`: an accepted
proof shows that the formula `Cslib.Logic.PL.CNF.ofDIMACS` reads from the decoded file is
unsatisfiable. The DIMACS parser is trusted to read the file as intended; the LRAT parser is not
trusted. This executable (reading the files, the UTF-8 decoding, printing and the exit code) is
not verified.
-/

open Cslib.Logic.PL

def main (args : List String) : IO UInt32 := do
  let [cnfPath, proofPath] := args
    | IO.eprintln "usage: lrat_check FORMULA.cnf PROOF.lrat"; return 2
  let t₀ ← IO.monoMsNow
  let mut cnfBytes := ByteArray.empty
  let mut proof := ByteArray.empty
  try
    cnfBytes ← IO.FS.readBinFile cnfPath
    proof ← IO.FS.readBinFile proofPath
  catch e =>
    IO.eprintln s!"lrat_check: {e}"
    return 2
  let t₁ ← IO.monoMsNow
  let verdict : Except String Unit := match String.fromUTF8? cnfBytes with
    | none => .error "cannot read the formula: it is not valid UTF-8"
    | some cnf => CNF.checkDIMACSLRAT cnf proof
  match verdict with
  | .ok () =>
    let t₂ ← IO.monoMsNow
    IO.eprintln s!"c read {t₁ - t₀} ms, parse and check {t₂ - t₁} ms"
    IO.println "s VERIFIED UNSAT"
    return 0
  | .error e =>
    let t₂ ← IO.monoMsNow
    IO.eprintln s!"c read {t₁ - t₀} ms, parse and check {t₂ - t₁} ms"
    IO.println s!"s REJECTED {e}"
    return 1
