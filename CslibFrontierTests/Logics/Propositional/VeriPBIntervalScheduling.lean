/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Logics.Propositional.PseudoBoolean.IntervalScheduling
import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
import CslibFrontierTests.Logics.Propositional.VeriPBProofText
import Mathlib.Data.Fin.VecNotation
-- `#guard` runs the dynamic program, the checkers and the brute force at compile time.
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.IntervalScheduling
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Print
public meta import CslibFrontier.Logics.Propositional.PseudoBoolean.Text
public meta import CslibFrontierTests.Logics.Propositional.VeriPBProofText

/-! Certified weighted interval scheduling
(`CslibFrontier.Logics.Propositional.PseudoBoolean.IntervalScheduling`) for an ordinary client,
which imports the module without `import all`:

* the end-to-end theorem applied to an accepted proof, and the encoding on an instance;
* `#guard` runs of the checker on the proofs of the dynamic program: they are accepted, their
  optimum agrees with a brute force over all sets of intervals, and a proof claiming a larger or a
  smaller optimum is rejected; on boundary instances (no intervals, nested, identical, touching
  and empty intervals, zero values) and on random instances of up to `11` intervals, and accepted
  on one of `24`;
* the instances printed as OPB by the library's printer `Cslib.Logic.PL.VeriPB.Text.printOPB`
  (`opbText`), and the proofs by the test-only printer
  `CslibFrontierTests.Logics.Propositional.VeriPBProofText.pbpText`, whose output the text front
  end parses and accepts with the same conclusion. VeriPB 3.0.2 and CakePB report
  `s VERIFIED BOUNDS` on the printed texts of the instances `printCases`.

The kernel-checked client is
`CslibFrontierTests.Logics.Propositional.VeriPBIntervalSchedulingDecide`. -/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Logics.Propositional.VeriPBIntervalScheduling

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Graph
  Cslib.Logic.PL.VeriPB.IntervalScheduling
open CslibFrontierTests.Logics.Propositional.VeriPBProofText

/-! ### The theorems for an ordinary client -/

/-- Acceptance of the proof of the dynamic program gives the optimum. -/
example {n : ℕ} (a f v : Fin n → ℕ)
    (h : checkRed (cliqueConstraints (compat a f)) (some (negProfit v)) (certify a f v).proof =
      true) (S : Finset (Fin n))
    (hS : (S : Set (Fin n)).Pairwise fun i j => min (f i) (f j) ≤ max (a i) (a j)) :
    ∑ i ∈ S, v i ≤ (certify a f v).optimum :=
  (isGreatest_of_checkRed_certify h).2 ⟨S, hS, rfl⟩

/-- The encoding on an instance: `[0, 3)` and `[2, 5)` overlap, `[0, 3)` and `[3, 6)` do not, and
the empty `[4, 4)` overlaps nothing. -/
example : ¬ (compat ![0, 2, 3, 4] ![3, 5, 6, 4]).Adj 0 1 ∧
    (compat ![0, 2, 3, 4] ![3, 5, 6, 4]).Adj 0 2 ∧
    (compat ![0, 2, 3, 4] ![3, 5, 6, 4]).Adj 1 3 := by
  decide

/-! ### Evaluated runs -/

/-- The instance of the starts `as`, the finishes `fs` and the values `vs`. -/
def inst (as fs vs : List ℕ) : (Fin as.length → ℕ) × (Fin as.length → ℕ) × (Fin as.length → ℕ) :=
  (fun i => as.getD i 0, fun i => fs.getD i 0, fun i => vs.getD i 0)

/-- The largest value of a set of pairwise disjoint intervals, by brute force over all sets. -/
def brute (as fs vs : List ℕ) : ℕ :=
  let n := as.length
  (List.range (2 ^ n)).foldl (fun b mask =>
    let S := (List.range n).filter mask.testBit
    if S.all fun i => S.all fun j => i == j ||
        decide (min (fs.getD i 0) (fs.getD j 0) ≤ max (as.getD i 0) (as.getD j 0))
    then max b (S.map (vs.getD · 0)).sum else b) 0

/-- Run the dynamic program: its optimum, and whether the checker accepts its proof. -/
def run (as fs vs : List ℕ) : ℕ × Bool :=
  let (a, f, v) := inst as fs vs
  let c := certify a f v
  (c.optimum, checkRed (cliqueConstraints (compat a f)) (some (negProfit v)) c.proof)

/-- The run is accepted and agrees with the brute force. -/
def agrees (as fs vs : List ℕ) : Bool :=
  let (k, ok) := run as fs vs
  ok && k == brute as fs vs

/-- The proof of the dynamic program with its conclusion changed to the optimum `k + d`. -/
def shifted (as fs vs : List ℕ) (d : ℤ) : Bool :=
  let (a, f, v) := inst as fs vs
  let c := certify a f v
  match c.proof.conclusion with
  | .bounds _ q _ _ =>
    checkRed (cliqueConstraints (compat a f)) (some (negProfit v))
      ⟨c.proof.steps, .bounds (some (-(c.optimum + d))) q (some (-(c.optimum + d))) none⟩
  | _ => false

#guard run [] [] [] == (0, true)
#guard agrees [0] [3] [5]
#guard agrees [0, 1, 3, 2] [3, 4, 6, 5] [5, 1, 8, 4]
-- Nested, identical and touching intervals.
#guard agrees [0, 1, 2, 0, 0] [10, 9, 3, 10, 2] [7, 3, 2, 7, 1]
#guard agrees [0, 2, 4, 6] [2, 4, 6, 8] [1, 2, 3, 4]
-- Empty and inverted intervals, which overlap nothing, and zero values.
#guard agrees [2, 5, 0, 3, 7] [2, 5, 4, 7, 1] [3, 4, 2, 6, 5]
#guard agrees [0, 1, 2] [5, 6, 7] [0, 0, 0]
#guard agrees [1, 3, 0, 4, 3, 5, 6, 8] [4, 5, 6, 7, 9, 9, 10, 11] [3, 2, 4, 1, 5, 2, 3, 4]

-- A wrong optimum is rejected, above or below the true one.
#guard !shifted [0, 1, 3, 2] [3, 4, 6, 5] [5, 1, 8, 4] 1
#guard !shifted [0, 1, 3, 2] [3, 4, 6, 5] [5, 1, 8, 4] (-1)
#guard shifted [0, 1, 3, 2] [3, 4, 6, 5] [5, 1, 8, 4] 0

/-- A linear congruential generator. -/
def lcg (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- `m` random intervals from the seed `s`: starts in `[0, 20)`, lengths in `[0, 8)` and values in
`[0, 10)`. -/
def randIntervals (s m : ℕ) : List ℕ × List ℕ × List ℕ :=
  let (_, as, fs, vs) := (List.range m).foldl (fun (s, as, fs, vs) _ =>
    let s₁ := lcg s
    let s₂ := lcg s₁
    let s₃ := lcg s₂
    let a := s₁ / 65536 % 20
    (s₃, a :: as, (a + s₂ / 65536 % 8) :: fs, (s₃ / 65536 % 10) :: vs)) (s, [], [], [])
  (as, fs, vs)

#guard (List.range 40).all fun s =>
  let (as, fs, vs) := randIntervals s (s % 12)
  agrees as fs vs

#guard let (as, fs, vs) := randIntervals 7 24; (run as fs vs).2

/-! ### Kernel text -/

/-- The instance as OPB text, by the library's printer. -/
def opbText (as fs vs : List ℕ) : String :=
  let (a, f, v) := inst as fs vs
  Text.printOPB ⟨cliqueConstraints (compat a f), some (negProfit v), none⟩

/-- The text front end accepts the printed proof against the printed instance, with the
conclusion of the dynamic program. -/
def textAgrees (as fs vs : List ℕ) : Bool :=
  let (a, f, v) := inst as fs vs
  let c := certify a f v
  Text.checkOPB (opbText as fs vs) (pbpText (cliqueConstraints (compat a f)).length c.proof) ==
    some c.proof.conclusion

/-- The instances whose texts were checked by VeriPB and CakePB. -/
def printCases : List (List ℕ × List ℕ × List ℕ) :=
  [([], [], []), ([0, 1, 3, 2], [3, 4, 6, 5], [5, 1, 8, 4]),
    ([0, 1, 2, 0, 0], [10, 9, 3, 10, 2], [7, 3, 2, 7, 1]),
    ([2, 5, 0, 3, 7], [2, 5, 4, 7, 1], [3, 4, 2, 6, 5]),
    ([1, 3, 0, 4, 3, 5, 6, 8], [4, 5, 6, 7, 9, 9, 10, 11], [3, 2, 4, 1, 5, 2, 3, 4]),
    randIntervals 7 24]

#guard printCases.all fun (as, fs, vs) => textAgrees as fs vs

end CslibFrontierTests.Logics.Propositional.VeriPBIntervalScheduling
