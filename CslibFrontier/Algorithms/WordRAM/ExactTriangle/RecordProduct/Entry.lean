/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Initialized
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Bounds

/-!
# Initialized producer-to-adapter composition

One fixed native program runs the complete producer from its original four headers and three
signed weight arrays, selects actual ordinal zero and invokes the actual record consumer.
The general caller interface handles any occupied ordinal; the initialized client here chooses
the first one with real code. Its existence follows from the original positive geometry.

The producer's pre-halt native witness and polynomial word bound derive every source pointer,
coordinate, caller base and dirty-word bound used by the record consumer. No producer layout,
run, solver or time certificate is an input hypothesis.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Initialized producer-to-backend composition for any `RecordBackend`. -/
abbrev RecordBackend.entryProgram (B : RecordBackend) : Code .standard 320 :=
  .seq produce (.seq (.op (.const Reg.ordinal 0)) B.program)

/-- Shared final-state answers, memory/register frames and query-sparsity postcondition
after an initialized producer-to-backend run on `values`. -/
abbrev RecordBackend.EntryAnswerPost (B : RecordBackend) (m : ℕ) {n g p : ℕ}
    (values : List ℤ) (a : Data 64) (idx : InstanceIndex p)
    (qs : List (Fin n × Fin n)) (y : Data 320) : Prop :=
  y.regs Reg.result = a.regs Instances.heap +
    QueriedProduct.outputBase (B.level m) m n qs.length ∧
  (∀ j : Fin qs.length,
    y.mem (a.regs Instances.heap +
      (QueriedProduct.outputBase (B.level m) m n qs.length + j.val)) =
      Signed.encode ((leftMatrix m n g p (fun q => values.getD q 0) idx *
        rightMatrix m n g p (fun q => values.getD q 0) idx) (qs.get j).1 (qs.get j).2)) ∧
  (∀ u, u < a.regs Instances.heap ∨
    a.regs Instances.heap + CallableProduct.windowSize n qs.length ≤ u →
    y.mem u = a.mem u) ∧
  (∀ j : Fin 64, y.regs (producerBank j) = a.regs j) ∧
  qs.length * 2 ^ m ≤ n ^ 2

/-- Postcondition of initialized producer-and-first-record execution for backend `B`. -/
abbrev RecordBackend.InputPost (B : RecordBackend) {W m n g p : ℕ} (hD : 16 ≤ D m)
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
    ∃ y, ExecWithin W B.entryProgram (.init (PreparationInput.input n (D m) g p values)) y
        (preparationTime n (D m) g p values + B.timeBound m qs) ∧
      B.EntryAnswerPost m (g := g) values a idx qs y

/-- Generic initialized structured execution for any `RecordBackend`. -/
theorem RecordBackend.exec_input (B : RecordBackend) {W m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W) :
    B.InputPost (W := W) (g := g) (p := p) hD hN values := by
  obtain ⟨hinput, ⟨ready⟩⟩ := prepare_first_input values hlen hD hg hp hN hv hW
  obtain ⟨y, hy, yr, yv, yf, yg, yQ⟩ := B.exec_of_output (fun q => values.getD q 0)
    (.init (PreparationInput.input n (D m) g p values)) ready.state ready.output
    hD hg (by omega) hN rfl rfl ready.index ready.index_mem ready.selected ready.fits
  simp only [ready.heap_eq, ready.mem_eq] at hy yr yf yQ
  rw [ready.heap_eq, ready.mem_eq] at yv
  exact ⟨hinput, ready.producer, ready.index, ready.producerExec, ready.index_mem,
    ready.ordinal_zero, y, ready.exec_consumer hy, yr, yv, yf, ready.producer_frame yg, yQ⟩

/-- One fixed initialized composition; selecting the first record costs one actual instruction. -/
abbrev entryProgram : Code .standard 320 := backend.entryProgram

/-- Complete initialized structured execution. The actual producer execution is a conclusion,
and its same native memory supplies the coordinate list consumed by the composed adapter. -/
theorem exec_input {W m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W) :
    backend.InputPost (W := W) (g := g) (p := p) hD hN values :=
  backend.exec_input values hlen hD hg hp hN hv hW

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
