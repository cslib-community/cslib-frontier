/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.RowBandwidth
import Mathlib.Data.List.FinRange
import Mathlib.Order.Prod.Lex.Basic

/-!
# Computing a row-sorted vertex order

Count all lexicographically smaller `(row, index)` keys to obtain each vertex's rank. The inverse
order scans the resulting rank array with `List.idxOf`. Both arrays contain exactly the original
vertex indices, and the resulting equivalence uses these actual array entries.

## Main definitions

* `List.rowRank`: count the keys preceding one original index.
* `RowOrder.ranks`: the rank array indexed by original vertex index.
* `RowOrder.indices`: the original vertex indices in sorted order.
* `RowOrder.equiv`: the actual original-index to rank equivalence.
* `BandwidthCertificate.ofRowArray`: certify the order obtained from the row array.

## Main results

* `RowOrder.indices_perm_range`: the sorted indices permute the original index range.
* `RowOrder.idxOf_indices`: positions in the sorted index list equal the computed ranks.
* `RowOrder.monotone_row_symm`: rows are monotone in the computed order.
-/

public section

namespace List

/-- The number of smaller `(row, index)` keys, breaking row ties by original index. -/
@[expose] def rowRank (rows : List ℕ) (i : ℕ) : ℕ :=
  ((List.range rows.length).filter fun j =>
    decide (rows.getD j 0 < rows.getD i 0 ∨ rows.getD j 0 = rows.getD i 0 ∧ j < i)).length

end List

namespace Cslib.Complexity.NCL.ConstraintGraph.RowOrder

/-- The rank of each original vertex, in original vertex order. -/
@[expose] def ranks (rows : List ℕ) : List ℕ :=
  (List.range rows.length).map (List.rowRank rows)

/-- The original vertex indices in increasing `(row, index)` order. -/
@[expose] def indices (rows : List ℕ) : List ℕ :=
  (List.range rows.length).map fun i => (ranks rows).idxOf i

private def key (rows : List ℕ) (i : ℕ) : ℕ ×ₗ ℕ := toLex (rows.getD i 0, i)

private theorem rank_eq_card (rows : List ℕ) (i : ℕ) :
    List.rowRank rows i =
      ((Finset.range rows.length).filter fun j => key rows j < key rows i).card := by
  rw [List.rowRank, ← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  congr 1
  ext j
  simp [key, Prod.Lex.toLex_lt_toLex]

private theorem rank_lt (rows : List ℕ) {i : ℕ} (hi : i < rows.length) :
    List.rowRank rows i < rows.length := by
  rw [rank_eq_card]
  exact (Finset.card_lt_card
    (Finset.filter_ssubset.mpr ⟨i, Finset.mem_range.mpr hi, lt_irrefl (key rows i)⟩)).trans_eq
    (Finset.card_range _)

private theorem rank_lt_rank (rows : List ℕ) {i j : ℕ} (hi : i < rows.length)
    (hij : key rows i < key rows j) : List.rowRank rows i < List.rowRank rows j := by
  rw [rank_eq_card, rank_eq_card]
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨fun k hk => ?_, fun he => ?_⟩)
  · obtain ⟨hk, hki⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨hk, hki.trans hij⟩
  · have hm : i ∈ (Finset.range rows.length).filter fun k => key rows k < key rows j :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hij⟩
    rw [← he] at hm
    exact lt_irrefl _ (Finset.mem_filter.mp hm).2

private theorem rank_injective (rows : List ℕ) {i j : ℕ}
    (hi : i < rows.length) (hj : j < rows.length)
    (h : List.rowRank rows i = List.rowRank rows j) : i = j := by
  rcases lt_trichotomy (key rows i) (key rows j) with hij | he | hji
  · exact False.elim ((ne_of_lt (rank_lt_rank rows hi hij)) h)
  · exact congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) he
  · exact False.elim ((ne_of_lt (rank_lt_rank rows hj hji)) h.symm)

private theorem rank_surjective (rows : List ℕ) :
    Function.Surjective (fun i : Fin rows.length => (⟨List.rowRank rows i, rank_lt rows i.isLt⟩ :
      Fin rows.length)) :=
  Finite.surjective_of_injective fun i j h =>
    Fin.ext (rank_injective rows i.isLt j.isLt (congrArg Fin.val h))

private theorem ranks_nodup (rows : List ℕ) : (ranks rows).Nodup :=
  List.Nodup.map_on
    (fun _ hi _ hj => rank_injective rows (List.mem_range.mp hi) (List.mem_range.mp hj))
    List.nodup_range

private theorem mem_ranks_iff (rows : List ℕ) (k : ℕ) : k ∈ ranks rows ↔ k < rows.length :=
  ⟨fun hk => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
      exact rank_lt rows (List.mem_range.mp hi),
    fun hk => by
      obtain ⟨i, hi⟩ := rank_surjective rows ⟨k, hk⟩
      exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, congrArg Fin.val hi⟩⟩

private theorem idxOf_rank (rows : List ℕ) {i : ℕ} (hi : i < rows.length) :
    (ranks rows).idxOf (List.rowRank rows i) = i := by
  simpa only [ranks, List.getElem_map, List.getElem_range] using
    (ranks_nodup rows).idxOf_getElem i (by simpa [ranks] using hi)

private theorem rank_idxOf (rows : List ℕ) {i : ℕ} (hi : i < rows.length) :
    List.rowRank rows ((ranks rows).idxOf i) = i := by
  simpa only [ranks, List.getElem_map, List.getElem_range] using
    List.getElem_idxOf (List.idxOf_lt_length_of_mem ((mem_ranks_iff rows i).mpr hi))

private theorem idxOf_lt (rows : List ℕ) {i : ℕ} (hi : i < rows.length) :
    (ranks rows).idxOf i < rows.length := by
  simpa only [ranks, List.length_map, List.length_range] using
    List.idxOf_lt_length_of_mem ((mem_ranks_iff rows i).mpr hi)

/-- The computed original-index to rank bijection, with inverse given by a rank-array scan. -/
@[expose] def equiv (rows : List ℕ) : Fin rows.length ≃ Fin rows.length where
  toFun i := ⟨List.rowRank rows i, by exact rank_lt rows i.isLt⟩
  invFun i := ⟨(ranks rows).idxOf i.val, by exact idxOf_lt rows i.isLt⟩
  left_inv i := by apply Fin.ext; exact idxOf_rank rows i.isLt
  right_inv i := by apply Fin.ext; exact rank_idxOf rows i.isLt

/-- The computed rank array permutes the original vertex-index range. -/
theorem ranks_perm_range (rows : List ℕ) : (ranks rows).Perm (List.range rows.length) :=
  (List.perm_ext_iff_of_nodup (ranks_nodup rows) List.nodup_range).mpr
    (fun i => (mem_ranks_iff rows i).trans List.mem_range.symm)

/-- The forward equivalence is read directly from the computed rank array. -/
theorem equiv_apply_eq_getElem (rows : List ℕ) (i : Fin rows.length) :
    (equiv rows i).val = (ranks rows)[i.val]'(by simp [ranks, i.isLt]) := by
  change List.rowRank rows i.val = _
  simp only [ranks, List.getElem_map, List.getElem_range]

/-- The inverse equivalence is read directly from the computed sorted index array. -/
theorem equiv_symm_apply_eq_getElem (rows : List ℕ) (i : Fin rows.length) :
    ((equiv rows).symm i).val = (indices rows)[i.val]'(by simp [indices, i.isLt]) := by
  change (ranks rows).idxOf i.val = _
  simp only [indices, List.getElem_map, List.getElem_range]

/-- The sorted index array permutes the original vertex-index range. -/
theorem indices_perm_range (rows : List ℕ) : (indices rows).Perm (List.range rows.length) := by
  have he : (List.finRange rows.length).map (fun i => ((equiv rows).symm i).val) =
      indices rows := List.ext_getElem (by simp [indices]) fun _ _ _ => by
    simp only [List.getElem_map, List.getElem_finRange, indices, List.getElem_range]; rfl
  simpa only [List.map_map, Function.comp_def, he, List.map_coe_finRange_eq_range] using
    (Equiv.Perm.map_finRange_perm (equiv rows).symm).map Fin.val

/-- The sorted index array has one entry per original vertex. -/
@[simp] theorem length_indices (rows : List ℕ) : (indices rows).length = rows.length := by
  simp only [indices, List.length_map, List.length_range]

/-- Looking up an original vertex in the sorted index array gives its actual computed rank. -/
theorem idxOf_indices (rows : List ℕ) (i : Fin rows.length) :
    (indices rows).idxOf i.val = (equiv rows i).val := by
  simpa only [← equiv_symm_apply_eq_getElem, Equiv.symm_apply_apply] using
    ((indices_perm_range rows).nodup_iff.mpr List.nodup_range).idxOf_getElem (equiv rows i).val
      (by simpa only [length_indices] using (equiv rows i).isLt)

/-- Reading rows in the computed index order is monotone. -/
theorem monotone_row_symm (rows : List ℕ) :
    Monotone (fun i => rows.getD ((equiv rows).symm i).val 0) := fun i j hij => by
  by_contra h
  have hr := rank_lt_rank rows ((equiv rows).symm j).isLt
    (Prod.Lex.toLex_lt_toLex.mpr (Or.inl (Nat.lt_of_not_ge h)))
  change (equiv rows ((equiv rows).symm j)).val <
    (equiv rows ((equiv rows).symm i)).val at hr
  simp only [Equiv.apply_symm_apply] at hr
  exact not_lt_of_ge hij hr

end Cslib.Complexity.NCL.ConstraintGraph.RowOrder

namespace Cslib.Complexity.NCL.ConstraintGraph

/-- Sort a supplied enumeration by its explicit row array and certify the resulting bandwidth. -/
@[expose] def BandwidthCertificate.ofRowArray {V E : Type*} {B d : ℕ}
    (G : ConstraintGraph V E) (rows : List ℕ) (base : V ≃ Fin rows.length)
    (hB : ∀ r, Nat.card {v // rows.getD (base v).val 0 = r} ≤ B)
    (hneighbours : ∀ u v, ∀ p ∈ (G u).ports, ∀ q ∈ (G v).ports,
      p.port.edge = q.port.edge → Nat.dist (rows.getD (base u).val 0)
        (rows.getD (base v).val 0) ≤ d) : BandwidthCertificate G ((d + 1) * B - 1) :=
  .ofRowOrder G (base.trans (RowOrder.equiv rows)) (fun v => rows.getD (base v).val 0) hB
    (by simpa only [Equiv.symm_trans_apply, Equiv.apply_symm_apply] using
      RowOrder.monotone_row_symm rows) hneighbours

end Cslib.Complexity.NCL.ConstraintGraph
