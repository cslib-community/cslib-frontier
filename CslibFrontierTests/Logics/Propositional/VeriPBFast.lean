/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
-- `import all`: `agree` runs the private compiled run `runTopFast` on the private compiled state
-- `FState`.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Fast
import CslibFrontierTests.Logics.Propositional.VeriPBAuxFixtures
import CslibFrontierTests.Logics.Propositional.VeriPBDomFixtures
import CslibFrontierTests.Logics.Propositional.VeriPBOutputFixtures
import CslibFrontierTests.Logics.Propositional.VeriPBPresFixtures
-- `#guard` evaluates the checkers and the fixtures at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
public meta import CslibFrontierTests.Logics.Propositional.VeriPBAuxFixtures
public meta import CslibFrontierTests.Logics.Propositional.VeriPBDomFixtures
public meta import CslibFrontierTests.Logics.Propositional.VeriPBOutputFixtures
public meta import CslibFrontierTests.Logics.Propositional.VeriPBPresFixtures

/-! The compiled checker `Cslib.Logic.PL.VeriPB.checkRedFast` against the reference checker on
the shared fixtures of the text front end and a few synthetic proofs. The compiled
code of `checkRed` is `checkRedFast` (`@[csimp]`), so the reference is run here through its own
definition: `runTop` from the initial state. Every fixture must reach the same final state, or
be rejected by both, and the decided `checkRed` tests stay on the reference. -/

namespace CslibFrontierTests.Logics.Propositional.VeriPBFast

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text
open CslibFrontierTests.Logics.Propositional.VeriPBText

set_option linter.hashCommand false

public section

/-- The compiled and the reference runs of `P` reach the same final state, or both reject. -/
def agree (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ))
    (P : RedProof) : Bool :=
  (runTopFast F obj (.ofState (State.init F obj pres)) P.steps).map FState.toState ==
    runTop F obj (State.init F obj pres) P.steps

/-- The proof text `pbp` with its output section, if any, replaced by `output NONE;`, so that
`parseProof` reads it. -/
def noOutput (pbp : String) : String :=
  "\n".intercalate ((pbp.splitOn "\n").map fun l =>
    if l.startsWith "output " then "output NONE;" else l)

/-- `agree` on the OPB instance `opb` and the proof text `pbp`; `false` if either fails to
parse. -/
def agreeOPB (opb pbp : String) : Bool :=
  match parseOPB opb with
  | some I =>
    match parseProof I.constraints.length 1000 (noOutput pbp) with
    | some P => agree I.constraints I.objective I.preserved P
    | none => false
  | none => false

/-- `agree` on the DIMACS formula `cnf` and the proof text `pbp`. -/
def agreeDIMACS (cnf pbp : String) : Bool :=
  match parseDIMACS cnf with
  | some φ =>
    match parseProof φ.length 1000 pbp with
    | some P => agree (φ.map Clause.toPB) none none P
    | none => false
  | none => false

/-! ### Shared fixtures

The other text fixtures are checked at the end of
`CslibFrontierTests.Logics.Propositional.VeriPBText`, and the redundance ones at the end of
`CslibFrontierTests.Logics.Propositional.VeriPBRed`. -/

#guard agreeOPB php32 domPhp32
#guard agreeOPB amo3 amo3Proof
#guard agreeOPB amo3Opt amo3OptProof
#guard agreeOPB sym2Aux domAuxObjProof
#guard agreeOPB pres4Rm enumAfterRm
#guard agreeOPB lex10Opb lex10Dom
#guard agreeOPB lex10RedOpb lex10Red
#guard agreeOPB lex10RedOpb lex10RedSub

/-! ### Synthetic proofs -/

/-- The clauses `xᵢ + xᵢ₊₁ ≥ 1` and `~xᵢ + ~xᵢ₊₁ ≥ 1` for `i < n`, numbered `1, …, 2n`. -/
def chain (n : ℕ) : List PBConstr :=
  (List.range n).flatMap fun i =>
    [⟨[(1, (i, true)), (1, (i + 1, true))], 1⟩, ⟨[(1, (i, false)), (1, (i + 1, false))], 1⟩]

/-- Sums of neighbouring clauses, saturated and divided, with deletions of every kind
interleaved, a deletion of a deleted number, a redundance step and strengthening-to-core mode,
which the compiled checker hands to the reference step. -/
def mixed (n : ℕ) : List TopStep :=
  ((List.range n).flatMap fun i =>
    [.step (.pol [.id (2 * i + 1), .id (2 * i + 2), .add, .sat, .div 2]),
      .step (.rup ⟨[(1, (i, true)), (1, (i + 1, true))], 1⟩ [.neg, .id (2 * i + 1)]),
      .deld [2 * n + 2 * i + 2], .step (.del [2 * n + 2 * i + 1])]) ++
  [.delc [1], .core [2], .strengthenToCore true,
    .red ⟨[(1, (1000, true))], 1⟩ [(1000, .one)] none none,
    .strengthenToCore false, .delc [3], .step (.del [5]),
    .step (.rup ⟨[(1, (2, false)), (1, (3, false))], 1⟩ [.neg, .id 6]), .delc [6, 6]]

#guard agree (chain 5) none none ⟨mixed 5, .noClaim⟩
#guard agree (chain 40) none none ⟨mixed 40, .noClaim⟩
#guard agree (chain 40) none none ⟨(mixed 40).dropLast, .noClaim⟩
#guard (runTopFast (chain 40) none (.ofState (State.init (chain 40) none none))
  (mixed 40).dropLast).isSome
#guard (runTopFast (chain 40) none (.ofState (State.init (chain 40) none none))
  (mixed 40)).isNone
#guard agree (chain 3) none none ⟨[.step (.del [7])], .noClaim⟩
#guard agree (chain 3) none none ⟨[.deld [1, 2, 1]], .noClaim⟩
#guard checkRedFast (chain 40) none ⟨mixed 40, .noClaim⟩ ==
  (runTop (chain 40) none (State.init (chain 40) none none) (mixed 40)).isSome

end

end CslibFrontierTests.Logics.Propositional.VeriPBFast
