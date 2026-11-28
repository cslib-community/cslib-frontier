/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.QueryValues
public import CslibFrontier.Algorithms.ExactTriangle.PieceBounds
import CslibFrontier.Algorithms.WordRAM.ExactTriangle.PreparationLocality
import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Readback

/-!
# Protected original data for a real record consumer

The original arrays, selected record and original interleaved queries all precede the actual
producer heap. These bounds are derived from `Instances.Output` and membership in the existing
finite instance family. A product execution can therefore preserve the actual words needed
by candidate recovery without copying the catalogue or snapshotting its workspace.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- Read the real selected record and prove every subsequent read is in the protected prefix.
The native program obtains these fields by loads; this theorem only derives their meaning. -/
theorem record_view {n D g p : ℕ} (values : ℕ → ℤ) (initial y : Data 64)
    (h : Instances.Output n D g p values initial y)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ≠ 0)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) D g p) :
    let ord := RecordProduct.recordOrdinal n D g p values idx
    let base := y.regs Instances.output + ord * (6 + 2 * (n * D))
    let q := RecordProduct.recordQueries n D p idx
    let Q := RecordProduct.recordQueryCount n D p values idx
    5 + 3 * (n * n) ≤ y.regs Instances.heap ∧
      base + 6 ≤ y.regs Instances.heap ∧ q + 2 * Q ≤ y.regs Instances.heap ∧
      idx.piece * pieceSize D g ≤ n ∧
      (∀ j : Fin 6, y.mem (base + j.val) =
        ![idx.residue.val, idx.piece, q, Q, base + 6, base + 6 + n * D] j) ∧
      (∀ j < Q, y.mem (q + 2 * j) < n ∧ y.mem (q + 2 * j + 1) < n) ∧
      (∀ j < 5 + 3 * (n * n), y.mem j = initial.mem j) := by
  have record := RecordProduct.prepared_record values h hD hDn hg hp idx hidx
  have hpiece := ((mem_instanceIndices _ idx).mp hidx).2
  exact ⟨h.inputEnd_le_heap,
    le_trans (Nat.le_add_right _ _) record.recordEnd,
    record.queryEnd.trans h.output_le_heap, (piece_start_lt hD hg hpiece).le,
    record.descriptor, record.queryCoordinates,
    fun j hj => h.2.2.2.2.2.2.2.2.2.2.2 j (Or.inl hj)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
