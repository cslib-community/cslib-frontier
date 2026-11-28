/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Entry
import CslibFrontier.Computability.WordRAM.Width

/-!
# Initialized flat native producer and product runs

The original four scalar headers and three signed weight arrays initialize one fixed native
program. Prefix `Runs`, the charged final halt, exact answer words and the caller frame all
refer to the same actual final data. The initialized client selects the first actual record;
the caller interface `exec_of_output` supports every occupied ordinal.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Generic flat program size and physical-width independence for `B.entryProgram`. -/
theorem RecordBackend.entryProgram_fixed (B : RecordBackend) :
    (B.entryProgram.program Reg.result).length ≤ 132352 ∧
      ¬(B.entryProgram.program Reg.result).ReadsWidth := by
  constructor
  · simp only [Code.program, List.length_append, Code.length_assemble,
      List.length_singleton, RecordBackend.entryProgram, Code.size, produce, Code.size_rename]
    have hc := B.program_fixed.1
    have hp := Instances.program_fixed.1
    omega
  · apply Code.not_readsWidth_program
    simp only [Code.ReadsWidth, produce, Code.readsWidth_rename, Op.ReadsWidth, false_or]
    exact not_or.mpr ⟨Instances.program_fixed.2, B.program_fixed.2⟩

/-- Postcondition of flat initialized `Runs` and charged `Executes` for backend `B`. -/
abbrev RecordBackend.RunsPost (B : RecordBackend) {W m n g p : ℕ} (hD : 16 ≤ D m)
    (hN : D m ^ 18 ≤ n) (values : List ℤ) : Prop :=
  InputFits W (PreparationInput.input n (D m) g p values) ∧
  let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
    ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
  ∃ a : Data 64, ∃ idx : InstanceIndex p,
    ExecWithin W Instances.program (.init (PreparationInput.input n (D m) g p values)) a
      (preparationTime n (D m) g p values - 1) ∧
    idx ∈ instanceIndices (fun a b : Fin n => values.getD (pairIndex (a, b)) 0) (D m) g p ∧
    recordOrdinal n (D m) g p (fun q => values.getD q 0) idx = 0 ∧
    let qs := decodedQueries hn a.mem (recordQueries n (D m) p idx)
      (recordQueryCount n (D m) p (fun q => values.getD q 0) idx)
    ∃ y t, t + 1 ≤ preparationTime n (D m) g p values + B.timeBound m qs + 1 ∧
      Runs W (B.entryProgram.program Reg.result)
        (State.init (PreparationInput.input n (D m) g p values)) ⟨B.entryProgram.size, y⟩ t ∧
      Executes W (B.entryProgram.program Reg.result)
        (State.init (PreparationInput.input n (D m) g p values))
        (a.regs Instances.heap + QueriedProduct.outputBase (B.level m) m n qs.length) (t + 1) ∧
      y.Bounded W ∧
      B.EntryAnswerPost m (g := g) values a idx qs y

/-- Generic initialized flat runs and charged halt for `B.entryProgram`. -/
theorem RecordBackend.runs_input (B : RecordBackend) {W m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W) :
    B.RunsPost (W := W) (g := g) (p := p) hD hN values := by
  obtain ⟨hi, a, idx, ha, hidx, hord, y, hy, yr, yv, yf, yg, hQ⟩ :=
    B.exec_input values hlen hD hg hp hN hv hW
  have ybound := hy.bounded (Data.Bounded.init hi)
  obtain ⟨t, ht, he⟩ := hy
  refine ⟨hi, a, idx, ha, hidx, hord, y, t, by omega, ?_, ?_, ybound, yr, yv, yf, yg, hQ⟩
  · simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := B.entryProgram.program Reg.result) (Program.Contains.self _).append_left
  · simpa only [yr, State.init] using he.executes Reg.result

/-- Generic width-independent word and support envelope on every prefix of `B.entryProgram`. -/
theorem RecordBackend.bounded_reachable_original (B : RecordBackend) {W m n g p A k : ℕ}
    (values : List ℤ) (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W)
    {s : State 320} (hr : Runs W (B.entryProgram.program Reg.result)
      (State.init (PreparationInput.input n (D m) g p values)) s k) :
    (∀ i, s.data.regs i < wordBound n (D m) g p A) ∧
      (∀ a, s.data.mem a < wordBound n (D m) g p A) ∧
      ∀ a, wordBound n (D m) g p A ≤ a → s.data.mem a = 0 := by
  obtain ⟨hi, _, _, _, _, _, _, _, _, _, he, -⟩ :=
    B.runs_input values hlen hD hg hp hN hv le_rfl
  exact hr.prefix_bounds_init B.entryProgram_fixed.2 hW hi he le_rfl

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
  hr.bounded_init (exec_input values hlen hD hg hp hN hv hW).1

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
