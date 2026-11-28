/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.RecordData

/-!
# The actual first prepared record exists

The fixed initialized composition selects ordinal zero. An original vertex pair belongs to
one existing residue class, so that class has a chunk and the vertex set has a piece. The native
ordinal characterization then supplies the unique existing finite index of the first record.
No nonempty catalogue or index certificate is an extra runtime input.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix

/-- Under the real producer geometry, ordinal zero always names an existing finite instance. -/
theorem first_index {n D g p : ℕ} (values : ℕ → ℤ)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ≠ 0) :
    ∃ idx : InstanceIndex p,
      idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) D g p ∧
      recordOrdinal n D g p values idx = 0 := by
  let wAB := fun a b : Fin n => values (pairIndex (a, b))
  let R := fun q => (values q % (p : ℤ)).toNat
  let C := fun rho => Nat.count (fun q => R q = rho) (n * n)
  let a : Fin n := ⟨0, by omega⟩
  let rho := resFin hp (wAB a a)
  have hcard : 0 < (residueClass wAB p rho).card :=
    Finset.card_pos.mpr ⟨(a, a), (mem_residueClass wAB hp rho (a, a)).mpr rfl⟩
  have hchunks : 0 < numChunks (residueClass wAB p rho) (queryCap n D) :=
    pos_of_mul_pos_left
      (hcard.trans_le (Nat.le_ceilDiv_mul (one_le_queryCap (by omega) hDn))) (Nat.zero_le _)
  have hpieces : 0 < numPieces n D g :=
    pos_of_mul_pos_left
      ((show 0 < n by omega).trans_le (Nat.le_ceilDiv_mul (pieceSize_pos hD hg))) (Nat.zero_le _)
  have hcount : 0 < ChunkCatalogue.before C (queryCap n D) p * numPieces n D g := by
    rw [QuerySpec.before_mul_numPieces wAB hp R fun _ => rfl]
    exact Finset.card_pos.mpr ⟨⟨rho, 0, 0⟩, (mem_instanceIndices wAB _).mpr ⟨hchunks, hpieces⟩⟩
  obtain ⟨idx, ⟨hidx, hzero⟩, -⟩ :=
    PreparationSpec.index_unique values wAB hp (fun _ _ => rfl) hD hDn hg 0 hcount
  exact ⟨idx, hidx, hzero.symm⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
