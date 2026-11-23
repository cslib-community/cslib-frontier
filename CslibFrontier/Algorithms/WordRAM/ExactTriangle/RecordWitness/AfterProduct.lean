/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.AfterRecordProduct
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Readback

/-!
# Composing a proved record product with candidate verification

`exec_after_product` composes a supplied 320-register product execution with the native witness
consumer on an occupied record from `Instances.Output`. The product premise supplies its returned
result offset, exact signed matrix-product answers, outside-window memory frame and preserved
registers below 65; concrete callers such as `RecordWitness.Exec` and `BoxRecordWitness.Exec`
discharge that premise with their compiled product programs.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Compose a proved product execution with the real consumer. The actual result offset,
exact signed answers, outside-window frame and producer registers are the only product
postconditions used. Concrete callers discharge this premise with their actual programs. -/
theorem exec_after_product {w U m n g p : ℕ} (values : ℕ → ℤ)
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
    (product : Code .standard 320) (T offset : ℕ)
    (hproduct :
      let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
        ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
      let q := RecordProduct.recordQueries n (D m) p idx
      let Q := RecordProduct.recordQueryCount n (D m) p values idx
      let qs := RecordProduct.decodedQueries hn x.mem q Q
      ∃ r : Data 320,
        ExecWithin (w + 2) product (x.comap productBank) r T ∧
        r.regs RecordProduct.Reg.result = x.regs (productBank 42) + offset ∧
        (∀ j : Fin qs.length,
          r.mem (x.regs (productBank 42) + offset + j.val) = Signed.encode
            ((RecordProduct.leftMatrix m n g p values idx *
              RecordProduct.rightMatrix m n g p values idx) (qs.get j).1 (qs.get j).2)) ∧
        (∀ u, u < x.regs (productBank 42) ∨
          x.regs (productBank 42) + CallableProduct.windowSize n Q ≤ u →
          r.mem u = x.mem u) ∧
        (∀ j : Fin 320, j.val < 65 → r.regs j = x.regs (productBank j)))
    (hfit : Fits (w + 2) (witnessWindow n (D m) g (x.regs (productBank 42))
      (RecordProduct.recordQueryCount n (D m) p values idx) offset)) :
    WitnessPost (.seq (product.rename productBank) consume) (w := w) (g := g) hD hN values
      AB BC AC x idx (fun _ => T) := by
  obtain ⟨hinputEnd, hrec, hq, hfirst, hv, hcoords, hprefix⟩ :=
    record_view values initial _ h hD
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN) hg hp idx hidx
  exact exec_after_record_product values AB BC AC x hD hN
    ((hprefix 1 (by omega)).trans hheaderD)
    ((hprefix 2 (by omega)).trans hheaderG)
    ((hprefix 3 (by omega)).trans hheaderN) idx hi
    ⟨hinputEnd, hrec, hq, hfirst, hv, hcoords⟩ hmem hmag hU product T offset hproduct hfit

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
