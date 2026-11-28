/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Entry
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Flat

/-!
# Initialized flat native producer and product runs

The original four scalar headers and three signed weight arrays initialize one fixed native
program. Prefix `Runs`, the charged final halt, exact answer words and the caller frame all
refer to the same actual final data. The initialized client selects the first actual record;
the caller interface `exec_of_output` supports every occupied ordinal.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open RecordProduct
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Fixed register count, instruction bound including halt, and physical-width independence. -/
theorem entryProgram_fixed : (entryProgram.program Reg.result).length ≤ 132352 ∧
    ¬(entryProgram.program Reg.result).ReadsWidth :=
  backend.entryProgram_fixed

/-- Every sufficiently wide physical execution starts from the actual original input and
returns the first prepared record's exact requested product values. There is no supplied
layout, run, time, sparse-count or solver certificate. Source prime selection and the outer
instance loop are separate; this theorem alone is not an aggregate ExactTriangle bound. -/
theorem runs_input {W m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W) :
    backend.RunsPost (W := W) (g := g) (p := p) hD hN values :=
  backend.runs_input values hlen hD hg hp hN hv hW

/-- Every native prefix is physically word-bounded from the actual admitted original input.
In particular this includes dirty loads before the callable compiler's remainder instruction. -/
theorem bounded_reachable {W m n g p A k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W)
    {s : State 320} (hr : Runs W (entryProgram.program Reg.result)
      (State.init (PreparationInput.input n (D m) g p values)) s k) : s.data.Bounded W :=
  hr.bounded_init (RecordBoxProduct.exec_input values hlen hD hg hp hN hv hW).1

/-- Every wider prefix of `entryProgram.program Reg.result` has the same input-derived word and
support envelope. This derives from its actual initialized halting run, without a supplied execution
certificate. -/
theorem bounded_reachable_original {W m n g p A k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W)
    {s : State 320} (hr : Runs W (entryProgram.program Reg.result)
      (State.init (PreparationInput.input n (D m) g p values)) s k) :
    (∀ i, s.data.regs i < wordBound n (D m) g p A) ∧
      (∀ a, s.data.mem a < wordBound n (D m) g p A) ∧
      ∀ a, wordBound n (D m) g p A ≤ a → s.data.mem a = 0 :=
  backend.bounded_reachable_original values hlen hD hg hp hN hv hW hr

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
