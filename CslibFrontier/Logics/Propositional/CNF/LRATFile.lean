/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Dimacs
public import CslibFrontier.Logics.Propositional.CNF.LRATFast
public import Std.Tactic.BVDecide.LRAT.Parser

/-! # Checking an LRAT file against a DIMACS file

`Cslib.Logic.PL.CNF.checkDIMACSLRAT cnf proof` reads a formula from the text `cnf` of a DIMACS
file (`Cslib.Logic.PL.CNF.ofDIMACS`), reads a certificate from the bytes `proof` of an LRAT file,
text or binary, with Lean core's parser (`Std.Tactic.BVDecide.LRAT.parseLRATProof`), and checks it
with the array checker `Cslib.Logic.PL.CNF.checkLRATFast`, RAT steps included
[Cruz-Filipe et al.][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017]. It returns `.ok ()` when the
certificate is accepted, and otherwise an error saying which of the three stages failed. The
executable `lake exe lrat_check FORMULA.cnf PROOF.lrat` (`scripts/LratCheck.lean`) runs it.

An accepted certificate shows that the formula read is unsatisfiable
(`Cslib.Logic.PL.CNF.not_satisfiable_of_checkDIMACSLRAT`). The statement concerns the formula that
`ofDIMACS` reads, so the DIMACS parser is trusted to read the file as intended; it reads back
exactly what `Cslib.Logic.PL.CNF.toDIMACS` writes (`Cslib.Logic.PL.CNF.ofDIMACS_toDIMACS`). The
LRAT parser is not trusted: whatever certificate it produces, the checker's verdict is sound.
The clauses of the formula are numbered from `1` in file order, as LRAT files expect.

## Main definitions

* `Cslib.Logic.PL.CNF.checkDIMACSLRAT`: the file checker.

## Main results

* `Cslib.Logic.PL.CNF.not_satisfiable_of_checkDIMACSLRAT`: a formula whose certificate is
  accepted is unsatisfiable.

## References

* [L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt, Jr., M. Kaufmann and P. Schneider-Kamp,
  *Efficient Certified RAT Verification*][CruzFilipeHeuleHuntKaufmannSchneiderKamp2017]
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

open Std.Tactic.BVDecide

/-- **The LRAT file checker**: read a formula from the DIMACS text `cnf` and an LRAT certificate,
text or binary, from `proof`, and check it with `CNF.checkLRATFast`. It returns `.ok ()` when the
certificate is accepted, and otherwise the reason it is not. -/
def checkDIMACSLRAT (cnf : String) (proof : ByteArray) : Except String Unit := do
  let φ ← (CNF.ofDIMACS cnf).mapError (s!"cannot read the formula: {·}")
  let cert ← (LRAT.parseLRATProof proof).mapError (s!"cannot read the proof: {·}")
  unless φ.checkLRATFast cert do
    throw "the certificate does not derive the empty clause by valid steps"

/-- **An accepted LRAT file refutes the DIMACS file**: if `checkDIMACSLRAT cnf proof` accepts,
the formula read from `cnf` is unsatisfiable. -/
theorem not_satisfiable_of_checkDIMACSLRAT {cnf : String} {proof : ByteArray}
    (h : checkDIMACSLRAT cnf proof = .ok ()) :
    ∃ φ, CNF.ofDIMACS cnf = .ok φ ∧ ¬ φ.Satisfiable := by
  unfold checkDIMACSLRAT at h
  cases hφ : CNF.ofDIMACS cnf with
  | error e => simp [hφ, Except.mapError, bind, Except.bind] at h
  | ok φ =>
    cases hc : LRAT.parseLRATProof proof with
    | error e => simp [hφ, hc, Except.mapError, bind, Except.bind] at h
    | ok cert =>
      refine ⟨φ, rfl, not_satisfiable_of_checkLRATFast (cert := cert) ?_⟩
      by_contra hne
      simp [hφ, hc, Except.mapError, bind, Except.bind, hne, throw, throwThe,
        MonadExceptOf.throw] at h

end Cslib.Logic.PL.CNF
