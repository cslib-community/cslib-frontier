/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.AfterProduct
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Producer

/-!
# The real product followed by candidate verification

The general caller selects any occupied record. The actual product is executed on its whole
renamed 320-register bank; the consumer then reads its real answers and protected query words.
The original signed arrays and caller catalogue remain untouched. The initialized entry derives
the numerical premises from original input, rather than supplying an intermediate run contract.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Product-and-verifier program for an arbitrary `RecordBackend`. -/
abbrev RecordBackend.witnessProgram (B : RecordProduct.RecordBackend) : Code .standard 400 :=
  .seq (B.program.rename productBank) consume

/-- Generic product-and-verifier execution from one producer output for any `RecordBackend`. -/
theorem RecordBackend.exec_witness_of_output (B : RecordProduct.RecordBackend) {w U m n g p : ℕ}
    (values : ℕ → ℤ) (AB BC AC : ℕ → ℕ → ℤ) (initial : Data 64) (x : Data 400)
    (h : Instances.Output n (D m) g p values initial
      ((x.comap productBank).comap RecordProduct.producerBank))
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ≠ 0) (hN : D m ^ 18 ≤ n)
    (hheaderD : initial.mem 1 = D m) (hheaderG : initial.mem 2 = g)
    (hheaderN : initial.mem 3 = n)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) (D m) g p)
    (hi : x.regs (productBank RecordProduct.Reg.ordinal) =
      RecordProduct.recordOrdinal n (D m) g p values idx)
    (hmem : ∀ a < n, ∀ b < n,
      x.mem (5 + (a * n + b)) = Signed.encode (AB a b) ∧
      x.mem (5 + n * n + (a * n + b)) = Signed.encode (BC a b) ∧
      x.mem (5 + n * n + n * n + (a * n + b)) = Signed.encode (AC a b))
    (hmag : ∀ a < n, ∀ b < n,
      (AB a b).natAbs ≤ U ∧ (BC a b).natAbs ≤ U ∧ (AC a b).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2) (witnessWindow n (D m) g (x.regs (productBank 42))
      (RecordProduct.recordQueryCount n (D m) p values idx)
      (QueriedProduct.outputBase (B.level m) m n
        (RecordProduct.recordQueryCount n (D m) p values idx)))) :
    WitnessPost (RecordBackend.witnessProgram B) (w := w) (g := g) hD hN values AB BC AC x idx
      (B.timeBound m) := by
  apply RecordWitness.exec_after_product values AB BC AC initial x h hD hg hp hN
    hheaderD hheaderG hheaderN idx hidx hi hmem hmag hU
    B.program _ (QueriedProduct.outputBase (B.level m) m n
      (RecordProduct.recordQueryCount n (D m) p values idx)) ?_ hfit
  obtain ⟨r, hr, rr, rv, rm, rg, -⟩ := B.exec_of_output values initial
    (x.comap productBank) h hD hg hp hN hheaderD hheaderN idx hidx hi
    (hfit.of_le (by
      change 2 * x.regs (productBank 42) +
        4 * CallableProduct.windowSize n
          (RecordProduct.recordQueryCount n (D m) p values idx) + 1024 ≤ witnessWindow _ _ _ _ _ _
      unfold witnessWindow
      omega))
  refine ⟨r, hr, ?_, ?_, ?_, rg⟩
  · simpa only [RecordProduct.decodedQueries_length, Data.comap_regs] using rr
  · simpa only [RecordProduct.decodedQueries_length, Data.comap_regs, Data.comap_mem,
      Nat.add_assoc] using rv
  · simpa only [RecordProduct.decodedQueries_length, Data.comap_regs, Data.comap_mem] using rm

/-- Execute the actual product and verifier from one genuine producer output. No product
execution, accepted-pair list, witness or time certificate is a hypothesis. -/
theorem exec_of_output {w U m n g p : ℕ} (values : ℕ → ℤ)
    (AB BC AC : ℕ → ℕ → ℤ) (initial : Data 64) (x : Data 400)
    (h : Instances.Output n (D m) g p values initial
      ((x.comap productBank).comap RecordProduct.producerBank))
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ≠ 0) (hN : D m ^ 18 ≤ n)
    (hheaderD : initial.mem 1 = D m) (hheaderG : initial.mem 2 = g)
    (hheaderN : initial.mem 3 = n)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) (D m) g p)
    (hi : x.regs (productBank RecordProduct.Reg.ordinal) =
      RecordProduct.recordOrdinal n (D m) g p values idx)
    (hmem : ∀ a < n, ∀ b < n,
      x.mem (5 + (a * n + b)) = Signed.encode (AB a b) ∧
      x.mem (5 + n * n + (a * n + b)) = Signed.encode (BC a b) ∧
      x.mem (5 + n * n + n * n + (a * n + b)) = Signed.encode (AC a b))
    (hmag : ∀ a < n, ∀ b < n,
      (AB a b).natAbs ≤ U ∧ (BC a b).natAbs ≤ U ∧ (AC a b).natAbs ≤ U)
    (hU : GenericRAM.Signed.Fits w (2 * U : ℕ))
    (hfit : Fits (w + 2) (witnessWindow n (D m) g (x.regs (productBank 42))
      (RecordProduct.recordQueryCount n (D m) p values idx)
      (QueriedProduct.outputBase (19 * m) m n
        (RecordProduct.recordQueryCount n (D m) p values idx)))) :
    WitnessPost program (w := w) (g := g) hD hN values AB BC AC x idx
      (RecordProduct.timeBound (m := m)) :=
  RecordBackend.exec_witness_of_output RecordProduct.backend values AB BC AC initial x h hD hg hp
    hN hheaderD hheaderG hheaderN idx hidx hi hmem hmag hU hfit

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
