/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanSet
public import CslibFrontier.Computability.WordRAM.MemoryView

/-!
# Memory invariant of a timestamped query list

## Main definitions

* `PrunedQuery.ScanMemory`: a distinct finite list and its timestamp membership directory.

## Main results

* `PrunedQuery.ScanMemory.insert_new`: the two actual stores preserve the invariant on insertion.

The invariant describes memory contents only. Execution and instruction charges are proved
separately for the native scan; no execution certificate is included here.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- The occupied output prefix enumerates `S` once, and the timestamp table identifies exactly
its members. Older timestamps may remain elsewhere in the directory. -/
structure ScanMemory (mem : ℕ → ℕ) (out stamps epoch capacity : ℕ) (S : Finset ℕ) : Prop where
  /-- Each listed value is a valid directory index. -/
  bounded : ∀ q ∈ S, q < capacity
  /-- Every timestamp is at most the current epoch. -/
  stamp_le : ∀ q < capacity, mem (stamps + q) ≤ epoch
  /-- The current epoch is exactly the membership marker. -/
  marked : ∀ q < capacity, mem (stamps + q) = epoch ↔ q ∈ S
  /-- The actual occupied prefix is an injective enumeration of the set. -/
  listed : ∃ v : Fin S.card → ℕ, Function.Injective v ∧
    Set.range v = (S : Set ℕ) ∧ (Block.mk out S.card).Realizes mem v

/-- A realized distinct list cannot exceed its concrete directory capacity. -/
theorem ScanMemory.card_le {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ} {S : Finset ℕ}
    (h : ScanMemory mem out stamps epoch capacity S) : S.card ≤ capacity := by
  simpa using Finset.card_le_card fun q hq => Finset.mem_range.mpr (h.bounded q hq)

/-- Agreement on the occupied list and timestamp directory preserves the scan invariant.
Unoccupied list cells have no specified meaning and need not agree. -/
theorem ScanMemory.congr {mem mem' : ℕ → ℕ} {out stamps epoch capacity : ℕ} {S : Finset ℕ}
    (h : ScanMemory mem out stamps epoch capacity S)
    (hlist : ∀ i < S.card, mem' (out + i) = mem (out + i))
    (hstamp : ∀ q < capacity, mem' (stamps + q) = mem (stamps + q)) :
    ScanMemory mem' out stamps epoch capacity S := by
  refine ⟨h.bounded, fun q hq => (hstamp q hq).symm ▸ h.stamp_le q hq, ?_, ?_⟩
  · intro q hq
    rw [hstamp q hq]
    exact h.marked q hq
  · obtain ⟨v, hv, hrange, hreal⟩ := h.listed
    exact ⟨v, hv, hrange, fun i => (hlist i i.isLt).trans (hreal i)⟩

/-- A frame on the occupied output and full timestamp directory retains the semantic view.
The list's dirty tail is deliberately outside the required read set. -/
theorem ScanMemory.keep {mem mem' : ℕ → ℕ} {out stamps epoch capacity : ℕ} {S : Finset ℕ}
    {reads : Set ℕ} (h : ScanMemory mem out stamps epoch capacity S)
    (hf : Set.EqOn mem' mem reads)
    (hlist : Set.Ico out (out + S.card) ⊆ reads)
    (hstamps : Set.Ico stamps (stamps + capacity) ⊆ reads) :
    ScanMemory mem' out stamps epoch capacity S :=
  h.congr (fun i hi => hf (hlist ⟨by omega, by omega⟩))
    (fun q hq => hf (hstamps ⟨by omega, by omega⟩))

/-- Reading the occupied native list gives exactly its represented finite set. -/
theorem ScanMemory.image_read {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ} {S : Finset ℕ}
    (h : ScanMemory mem out stamps epoch capacity S) :
    (Finset.range S.card).image (fun i => mem (out + i)) = S := by
  obtain ⟨v, _, hrange, hreal⟩ := h.listed
  ext q
  simp only [Finset.mem_image, Finset.mem_range]
  rw [← Finset.mem_coe, ← hrange, Set.mem_range]
  exact ⟨fun ⟨i, hi, hq⟩ => ⟨⟨i, hi⟩, (hreal ⟨i, hi⟩).symm.trans hq⟩,
    fun ⟨i, hi⟩ => ⟨i.val, i.isLt, (hreal i).trans hi⟩⟩

/-- Occupied native list positions store different codes. -/
theorem ScanMemory.injOn_read {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ} {S : Finset ℕ}
    (h : ScanMemory mem out stamps epoch capacity S) :
    Set.InjOn (fun i => mem (out + i)) {i | i < S.card} := by
  obtain ⟨v, hv, _, hreal⟩ := h.listed
  exact fun i hi j hj he =>
    congrArg Fin.val (hv ((hreal ⟨i, hi⟩).symm.trans (he.trans (hreal ⟨j, hj⟩))))

/-- An unseen valid code leaves a free output cell for its insertion. -/
theorem ScanMemory.card_lt_of_notMem {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ}
    {S : Finset ℕ} (h : ScanMemory mem out stamps epoch capacity S) {q : ℕ}
    (hq : q < capacity) (hnew : q ∉ S) : S.card < capacity := by
  have hc := Finset.card_le_card (t := Finset.range capacity) fun a ha =>
    Finset.mem_range.mpr ((Finset.mem_insert.mp ha).elim (· ▸ hq) (h.bounded a))
  simp only [Finset.card_insert_of_notMem hnew, Finset.card_range] at hc
  omega

/-- A fresh epoch establishes the empty directory without clearing its cells. -/
theorem ScanMemory.empty {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ}
    (h : ∀ q < capacity, mem (stamps + q) < epoch) :
    ScanMemory mem out stamps epoch capacity ∅ :=
  ⟨by simp, fun q hq => (h q hq).le, fun q hq => by simp [Nat.ne_of_lt (h q hq)],
    Fin.elim0, fun i => i.elim0, Set.ext fun _ => by simp, fun i => i.elim0⟩

/-- Append one previously unseen code, then mark its directory entry. Disjointness of the
two concrete blocks ensures that neither store corrupts the other representation. -/
theorem ScanMemory.insert_new {mem : ℕ → ℕ} {out stamps epoch capacity : ℕ} {S : Finset ℕ}
    (h : ScanMemory mem out stamps epoch capacity S) {q : ℕ} (hq : q < capacity)
    (hnew : q ∉ S) (hsep : out + capacity ≤ stamps ∨ stamps + capacity ≤ out) :
    ScanMemory
      (Function.update (Function.update mem (out + S.card) q) (stamps + q) epoch)
      out stamps epoch capacity (insert q S) := by
  have hcard := h.card_lt_of_notMem hq hnew
  have haway (a : ℕ) (ha : a < capacity) : stamps + a ≠ out + S.card := by
    rcases hsep with hs | hs <;> omega
  refine ⟨fun a ha => (Finset.mem_insert.mp ha).elim (· ▸ hq) (h.bounded a),
    fun a ha => ?_, fun a ha => ?_, ?_⟩
  · rcases eq_or_ne a q with rfl | he
    · simp
    · simpa only [Function.update_of_ne (by omega : stamps + a ≠ stamps + q),
        Function.update_of_ne (haway a ha)] using h.stamp_le a ha
  · rcases eq_or_ne a q with rfl | he
    · simp
    · simpa only [Function.update_of_ne (by omega : stamps + a ≠ stamps + q),
        Function.update_of_ne (haway a ha), Finset.mem_insert, he, false_or] using h.marked a ha
  · obtain ⟨v, hv, hrange, hreal⟩ := h.listed
    have hown : ¬(Block.mk out (S.card + 1)).Owns (stamps + q) := by
      change ¬(out ≤ stamps + q ∧ stamps + q < out + (S.card + 1))
      rcases hsep with hs | hs <;> omega
    rw [Finset.card_insert_of_notMem hnew]
    refine ⟨Fin.snoc v q, Fin.snoc_injective_iff.mpr
      ⟨hv, by simpa only [hrange, Finset.mem_coe] using hnew⟩, ?_,
      (hreal.snoc q).update_of_not_owns hown epoch⟩
    simp [Fin.range_snoc, hrange]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
