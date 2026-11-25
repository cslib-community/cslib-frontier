/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.RecordData
import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.QuerySpan

/-!
# Pure source-span readback for either record product

`prepared_record` gives the prepared record, raw matrix blocks, and query coordinates.
`producer_readback` relates these to the original words of the queried product input.
The readback includes the six-word record descriptor, raw left and right zero/one matrix
spans, ordered query-coordinate words, heap bounds and occurrence sparsity from a genuine
`Instances.Output`, without importing or executing either per-record product backend.
`raw_left_block` and `raw_right_block` read a record's realized raw matrix blocks as the ordinary
product's original input; `producer_readback` and the box record caller both use them.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The raw descriptor and matrix blocks of one prepared record, together with its
protected query coordinates. The coordinates lie before the producer's record region. -/
structure PreparedRecord (n D g p : ℕ) (values : ℕ → ℤ) (y : Data 64)
    (idx : InstanceIndex p) (base : ℕ) : Prop where
  /-- The entire physical record lies below or ends at the heap. -/
  recordEnd : base + 6 + 2 * (n * D) ≤ y.regs Instances.heap
  /-- The entire interleaved query span lies before the record region. -/
  queryEnd : recordQueries n D p idx + 2 * recordQueryCount n D p values idx ≤
    y.regs Instances.output
  /-- The six physical descriptor fields at the selected record address. -/
  descriptor : (Block.mk base 6).Realizes y.mem
    ![idx.residue.val, idx.piece, recordQueries n D p idx, recordQueryCount n D p values idx,
      base + 6, base + 6 + n * D]
  /-- The raw left matrix follows the descriptor. -/
  left : (Block.mk (base + 6) (n * D)).Realizes y.mem (fun j =>
    WriteMatrices.entry false (matrixArgs n D g p idx.residue.val idx.piece)
      (fun q => (values (2 * (n * n) + q) % (p : ℤ)).toNat) j)
  /-- The raw right matrix follows the left matrix. -/
  right : (Block.mk (base + 6 + n * D) (n * D)).Realizes y.mem (fun j =>
    WriteMatrices.entry true (matrixArgs n D g p idx.residue.val idx.piece)
      (fun q => (values (n * n + q) % (p : ℤ)).toNat) j)
  /-- Every word in the query span denotes an original vertex. -/
  queryCoordinates : ∀ j < recordQueryCount n D p values idx,
    y.mem (recordQueries n D p idx + 2 * j) < n ∧
      y.mem (recordQueries n D p idx + 2 * j + 1) < n

/-- A finite instance selects an actual record and intact query span in the producer output. -/
theorem prepared_record {n D g p : ℕ} (values : ℕ → ℤ)
    {initial y : Data 64} (h : Instances.Output n D g p values initial y)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ≠ 0)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) D g p) :
    PreparedRecord n D g p values y idx
      (y.regs Instances.output + recordOrdinal n D g p values idx * (6 + 2 * (n * D))) := by
  let wAB := fun a b : Fin n => values (pairIndex (a, b))
  let count := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) (n * n)
  let records := ChunkCatalogue.before count (queryCap n D) p * numPieces n D g
  obtain ⟨hchunk, hpiece⟩ := (mem_instanceIndices wAB idx).mp hidx
  have hcard : (residueClass wAB p idx.residue).card = count idx.residue.val :=
    QuerySpec.card_residueClass wAB hp _ (by intro pair; rfl) idx.residue
  have hchunk' : idx.chunk < count idx.residue.val ⌈/⌉ queryCap n D := by
    simpa only [numChunks, hcard] using hchunk
  have hgroup := ChunkCatalogue.before_add_lt count (queryCap n D) idx.residue.isLt hchunk'
  have hord : recordOrdinal n D g p values idx < records := by
    simpa only [recordOrdinal, records, count, Nat.mul_comm] using
      Nat.mul_add_lt_mul_of_lt_of_lt hgroup hpiece
  have hout := h.2.2.2.1
  have hheap := h.2.2.2.2.2.1
  obtain ⟨descriptor, left, right⟩ := PreparationSpec.instance_readback values wAB hp
    (fun _ _ => rfl) hD hDn hg h idx hidx
  have hcoord := (output_query_coordinates values wAB hp (fun _ _ => rfl)
    (by lia) hDn h idx.residue idx.chunk hchunk).1
  constructor
  · rw [hout, hheap]
    change _ + _ * _ + 6 + 2 * (n * D) ≤ _ + records * (6 + 2 * (n * D))
    have hfit := Nat.mul_le_mul_right (6 + 2 * (n * D)) (Nat.succ_le_of_lt hord)
    rw [Nat.succ_mul] at hfit
    lia
  · rw [hout]
    exact query_end_le_output values hp (by lia) hDn idx hidx
  · rw [hout]
    simpa only [recordOrdinal, recordQueries, recordQueryCount, hcard, count] using descriptor
  · rw [hout]
    exact left
  · rw [hout]
    exact right
  · simpa only [recordQueries, recordQueryCount, hcard, count] using hcoord

/-- A record's raw left block, as written by the producer, reads as the original left input of the
ordinary queried product. -/
theorem raw_left_block {m n g p s : ℕ} (values : ℕ → ℤ) (idx : InstanceIndex p)
    (mem : ℕ → ℕ) (qs : List (Fin n × Fin n))
    (hleft : (Block.mk s (n * D m)).Realizes mem (fun j =>
      WriteMatrices.entry false (matrixArgs n (D m) g p idx.residue.val idx.piece)
        (fun q => (values (2 * (n * n) + q) % (p : ℤ)).toNat) j)) :
    ∀ a < n * D m, mem (s + a) =
      (State.init (QueriedProduct.input true (19 * m)
        (leftMatrix m n g p values idx) (rightMatrix m n g p values idx) qs) :
          State 160).data.mem (5 + a) := by
  refine raw_left_words mem _ _ qs fun a k => ?_
  have hflat : a.val * D m + k.val < n * D m := by
    rw [Nat.mul_comm a.val]
    exact Nat.mul_add_lt_mul_of_lt_of_lt a.isLt k.isLt
  simpa only [leftMatrix, Int.toNat_natCast, Block.Realizes, Block.read] using hleft ⟨_, hflat⟩

/-- A record's raw right block, in its `D×n` storage order, reads as the original right input of
the ordinary queried product. -/
theorem raw_right_block {m n g p t : ℕ} (hn : 0 < n) (values : ℕ → ℤ) (idx : InstanceIndex p)
    (mem : ℕ → ℕ) (qs : List (Fin n × Fin n))
    (hright : (Block.mk t (n * D m)).Realizes mem (fun j =>
      WriteMatrices.entry true (matrixArgs n (D m) g p idx.residue.val idx.piece)
        (fun q => (values (n * n + q) % (p : ℤ)).toNat) j)) :
    ∀ a < n * D m, mem (t + a) =
      (State.init (QueriedProduct.input true (19 * m)
        (leftMatrix m n g p values idx) (rightMatrix m n g p values idx) qs) :
          State 160).data.mem (5 + n * D m + a) := by
  refine raw_right_words hn mem _ _ qs fun k a => ?_
  have hflat : k.val * n + a.val < n * D m := by
    rw [Nat.mul_comm k.val, Nat.mul_comm n (D m)]
    exact Nat.mul_add_lt_mul_of_lt_of_lt k.isLt a.isLt
  simpa only [rightMatrix, Int.toNat_natCast, Block.Realizes, Block.read] using hright ⟨_, hflat⟩

/-- Derive both raw source matrices, ordered coordinate words, protected spans and occurrence
sparsity from genuine producer output, without invoking either product backend. -/
theorem producer_readback {m n g p : ℕ} (values : ℕ → ℤ)
    (initial : Data 64) (x : Data 320)
    (h : Instances.Output n (D m) g p values initial (x.comap producerBank))
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ≠ 0) (hN : D m ^ 18 ≤ n)
    (hheaderD : initial.mem 1 = D m) (hheaderN : initial.mem 3 = n)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) (D m) g p) :
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    let ord := recordOrdinal n (D m) g p values idx
    let base := x.regs 39 + ord * (6 + 2 * (n * D m))
    let q := recordQueries n (D m) p idx
    let qs := decodedQueries hn x.mem q (recordQueryCount n (D m) p values idx)
    x.mem 1 = D m ∧ x.mem 3 = n ∧
      base + 6 ≤ x.regs 42 ∧
      (Block.mk base 6).Realizes x.mem
        ![idx.residue.val, idx.piece, q, qs.length, base + 6, base + 6 + n * D m] ∧
      base + 6 + n * D m ≤ x.regs 42 ∧
      base + 6 + n * D m + n * D m ≤ x.regs 42 ∧
      q + 2 * qs.length ≤ x.regs 42 ∧
      (∀ a < n * D m, x.mem (base + 6 + a) =
        (State.init (QueriedProduct.input true (19 * m)
          (leftMatrix m n g p values idx) (rightMatrix m n g p values idx) qs) :
            State 160).data.mem (5 + a)) ∧
      (∀ a < n * D m, x.mem (base + 6 + n * D m + a) =
        (State.init (QueriedProduct.input true (19 * m)
          (leftMatrix m n g p values idx) (rightMatrix m n g p values idx) qs) :
            State 160).data.mem (5 + n * D m + a)) ∧
      (∀ a < 2 * qs.length, x.mem (q + a) =
        (State.init (QueriedProduct.input true (19 * m)
          (leftMatrix m n g p values idx) (rightMatrix m n g p values idx) qs) :
            State 160).data.mem (5 + 2 * (n * D m) + a)) ∧
      qs.length * 2 ^ m ≤ n ^ 2 := by
  have hDn : D m ≤ n := (Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN
  have hn : 0 < n := lt_of_lt_of_le (by lia) hDn
  let q := recordQueries n (D m) p idx
  let Q := recordQueryCount n (D m) p values idx
  let qs := decodedQueries hn x.mem q Q
  obtain ⟨recordEnd, queryEnd, descriptor, left, right, coordinates⟩ :=
    prepared_record values h hD hDn hg hp idx hidx
  change x.regs 39 + _ * _ + 6 + 2 * (n * D m) ≤ x.regs 42 at recordEnd
  have hframe := h.2.2.2.2.2.2.2.2.2.2.2
  have hheap : x.regs 39 ≤ x.regs 42 := by
    change (x.comap producerBank).regs Instances.output ≤ (x.comap producerBank).regs Instances.heap
    rw [h.2.2.2.1, h.2.2.2.2.2.1]
    exact Nat.le_add_right _ _
  dsimp only
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ qs.length * 2 ^ m ≤ n ^ 2
  rw [decodedQueries_length]
  exact ⟨(hframe 1 (Or.inl (by lia))).trans hheaderD,
    (hframe 3 (Or.inl (by lia))).trans hheaderN,
    le_trans (Nat.le_add_right _ _) recordEnd, descriptor,
    le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by decide)) _) recordEnd,
    by simpa only [two_mul, Nat.add_assoc] using recordEnd,
    queryEnd.trans hheap,
    raw_left_block values idx x.mem qs left,
    raw_right_block hn values idx x.mem qs right,
    decodedQueries_words hn x.mem _ _ coordinates,
    (Nat.mul_le_mul_right (2 ^ m) (min_le_left _ _)).trans (queryCap_mul_two_pow_le n m)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
