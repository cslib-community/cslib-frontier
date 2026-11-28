/-
Copyright (c) 2026 Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Anderson
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.WordRAM.XORSATDense
import CslibFrontier.Computability.Complexity.Problems.XORSAT.Dense
meta import CslibFrontier.Algorithms.WordRAM.XORSATDense
meta import CslibFrontier.Computability.Complexity.Problems.XORSAT.Dense

/-!
# Tests for Word-RAM dense Gaussian elimination over `𝔽₂`

Run the assembled `Cslib.Algorithms.WordRAM.XORSATDense.program` with `Cslib.WordRAM.run` (which
counts the final `halt`) on `encode q` for concrete well-formed instances `q`, and check that the
answer is `(XORSAT.Dense.decide q).toNat` and that the instruction count is at most the proved
bound `30 (m + 1) (n + 1)`. Two `example`s also apply the public theorems `computesInTime_decide`
and `decidesInTime_decide` to a concrete instance through the exposed `FitsWidth` and `encode`,
as an ordinary `module` client:

* a satisfiable `2 × 2` system and an unsatisfiable `2 × 1` system (`x₀ = 1`, `x₀ = 0`);
* the three-equation cycle `x₀ + x₁ = 1`, `x₁ + x₂ = 1`, `x₀ + x₂ = 1` (unsatisfiable) and the
  same cycle with last right-hand side `0` (satisfiable);
* the empty system, and a zero row with right-hand side `1`;
* 400 pseudo-random systems with `n < 7` and `m < 6`, at width `n + m + 4` (admitted by
  `FitsWidth`).
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.XORSATDenseWordRAM

open Cslib.WordRAM Cslib.Algorithms.WordRAM.XORSATDense Cslib.Complexity.XORSAT.Dense

/-- A well-formed instance from a row-width check. -/
def mkInst (q : Input) (h : (q.rows.all fun e => e.coeffs.length == q.width) = true) : Instance :=
  ⟨q, fun e he => by simpa using List.all_eq_true.mp h e he⟩

/-- Run the assembled program on `encode q` at width `w`: answer and instruction count. -/
def runInst (w : ℕ) (q : Instance) : Option (ℕ × ℕ) :=
  run w program 100000 (State.init (encode q))

/-- The answer agrees with `decide` and the run is within the proved bound. -/
def ok (w : ℕ) (q : Instance) : Bool :=
  match runInst w q with
  | some (v, steps) =>
    v == (decide q.val).toNat && steps ≤ 30 * (q.val.rows.length + 1) * (q.val.width + 1)
  | none => false

/-- `ok` on an `Input`, or `false` if a row has the wrong width. -/
def okInput (w : ℕ) (q : Input) : Bool :=
  if h : (q.rows.all fun e => e.coeffs.length == q.width) = true then ok w (mkInst q h)
  else false

/-- A concrete satisfiable `2 × 2` instance. -/
def q₀ : Instance := mkInst ⟨2, [⟨[true, true], true⟩, ⟨[false, true], true⟩]⟩ rfl

/-- `q₀` is admitted at width `8`, through the exposed `FitsWidth`. -/
theorem fitsWidth_q₀ : FitsWidth q₀ 8 := ⟨by decide, by decide⟩

/-- The encoding of `q₀` fits at width `8`. -/
theorem inputFits_q₀ : InputFits 8 (encode q₀) := by decide

/-- Client check across the `module` boundary, without `import all`: the public running-time
theorem applies to `q₀` at width `8`. -/
example : ∃ n, Executes 8 program (.init (encode q₀)) (decide q₀.val).toNat n ∧
    n ≤ 30 * (2 + 1) * (2 + 1) :=
  computesInTime_decide q₀ 8 fitsWidth_q₀ inputFits_q₀

/-- Client check: the public decision theorem applies to `q₀` at width `8`. -/
example : (WordSizeDependentProgram.const program 8).Answers 8 (encode q₀)
    (q₀ ∈ {q : Instance | Satisfiable q.val.width q.val.rows}) (30 * (2 + 1) * (2 + 1)) :=
  decidesInTime_decide q₀ 8 fitsWidth_q₀ inputFits_q₀

#guard okInput 8 ⟨2, [⟨[true, true], true⟩, ⟨[false, true], true⟩]⟩
#guard decide ⟨2, [⟨[true, true], true⟩, ⟨[false, true], true⟩]⟩
#guard okInput 8 ⟨1, [⟨[true], true⟩, ⟨[true], false⟩]⟩
#guard !decide ⟨1, [⟨[true], true⟩, ⟨[true], false⟩]⟩
#guard okInput 8 ⟨3, [⟨[true, true, false], true⟩, ⟨[false, true, true], true⟩,
  ⟨[true, false, true], true⟩]⟩
#guard okInput 8 ⟨3, [⟨[true, true, false], true⟩, ⟨[false, true, true], true⟩,
  ⟨[true, false, true], false⟩]⟩
#guard okInput 8 ⟨0, []⟩
#guard okInput 8 ⟨2, [⟨[false, false], true⟩]⟩

/-- Linear congruential generator for reproducible pseudo-random systems. -/
def lcg (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- `m` pseudo-random rows of width `n` (coefficient density about one third). -/
def randRows (n m s : ℕ) : List Row × ℕ := Id.run do
  let mut s := s
  let mut rows : List Row := []
  for _ in [0:m] do
    let mut cs : List Bool := []
    for _ in [0:n] do
      s := lcg s
      cs := cs ++ [s % 3 == 0]
    s := lcg s
    rows := rows ++ [⟨cs, s % 2 == 0⟩]
  return (rows, s)

/-- Number of trials (out of `trials`) where `okInput` holds, and number of satisfiable systems. -/
def fuzz (trials : ℕ) : ℕ × ℕ := Id.run do
  let mut s := 7
  let mut good := 0
  let mut sat := 0
  for t in [0:trials] do
    let n := t % 7
    let m := (t / 7) % 6
    let (rows, s') := randRows n m s
    s := s'
    let q : Input := ⟨n, rows⟩
    if okInput (n + m + 4) q then good := good + 1
    if decide q then sat := sat + 1
  return (good, sat)

#guard fuzz 400 = (400, 265)

end CslibFrontierTests.XORSATDenseWordRAM
