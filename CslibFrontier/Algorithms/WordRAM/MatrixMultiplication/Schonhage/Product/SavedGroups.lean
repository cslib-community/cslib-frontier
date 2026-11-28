/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Groups
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Groups

/-!
# Memory invariants for the saved routing arrays

## Main definitions

* `QueriedProduct.SavedGroups`: protected words agree with an earlier actual router state.

## Main results

* `QueriedProduct.SavedGroups.reframe`: kernel and producer frames retain the saved arrays.
* `QueriedProduct.router_code_lt`: executed stable scatter gives a valid query code at every
  grouped position, including duplicate requests.
* `QueriedProduct.SavedGroups.span_bounds`: actual saved offsets form admitted kernel spans.

The earlier memory is a proof reference to an executed state, not program input. The native
copy theorem establishes these equalities before any low-memory reuse occurs.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Values copied from the actual router state into protected caller-owned arrays. -/
public structure SavedGroups (L m N Q : ℕ) (old μ : ℕ → ℕ) : Prop where
  /-- All actual offsets, including the terminal offset. -/
  offsets : ∀ t ≤ numBands L m N ^ 2,
    μ (offsetBase L m N Q + t) = old (Wanted.offsetAddress L m N Q + t)
  /-- All actual grouped codes. -/
  codes : ∀ j < Q, μ (codeBase L m N Q + j) = old (Wanted.codeAddress L m N Q + j)
  /-- All actual original-position words. -/
  originals : ∀ j < Q,
    μ (originalBase L m N Q + j) = old (Wanted.originalAddress L m N Q + j)

/-- Preserving the protected readonly interval preserves the saved routing arrays. -/
public theorem SavedGroups.reframe {L m N Q : ℕ} {old μ ν : ℕ → ℕ}
    (h : SavedGroups L m N Q old μ)
    (hf : ∀ a, offsetBase L m N Q ≤ a → a < groupedBase L m N Q → ν a = μ a) :
    SavedGroups L m N Q old ν := by
  have hc : offsetBase L m N Q + numBands L m N ^ 2 + 1 = codeBase L m N Q := by
    unfold codeBase; omega
  have ho : codeBase L m N Q + Q = originalBase L m N Q := rfl
  have hg : originalBase L m N Q + Q = groupedBase L m N Q := rfl
  exact ⟨fun t ht => (hf _ (by omega) (by omega)).trans (h.offsets t ht),
    fun j hj => (hf _ (by omega) (by omega)).trans (h.codes j hj),
    fun j hj => (hf _ (by omega) (by omega)).trans (h.originals j hj)⟩

/-- Stable scatter covers every grouped cell, so every stored code is a valid query index.
The proof uses the existing permutation theorem rather than a supplied inverse table. -/
public theorem router_code_lt {L m N : ℕ} (hm : m ≤ L) (qs : List (Fin N × Fin N))
    (old : ℕ → ℕ)
    (hvalues : ∀ i : Fin qs.length,
      old (Wanted.codeAddress L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        (PrunedQuery.queryIndex
          (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val)
    (j : ℕ) (hj : j < qs.length) :
    old (Wanted.codeAddress L m N qs.length + j) < 10 ^ L := by
  obtain ⟨i, hi⟩ := (CountingSort.position_bijective
    (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length).surjective ⟨j, hj⟩
  have hp : CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i = j :=
    (congrArg Fin.val hi :)
  rw [← hp, hvalues i]
  exact (PrunedQuery.queryIndex _).isLt

/-- The actual protected offset words satisfy the kernel's monotone span and count bounds.
These inequalities follow from the executed prefix-count meanings, not input certificates. -/
public theorem SavedGroups.span_bounds {L m N Q : ℕ} {old μ : ℕ → ℕ}
    (h : SavedGroups L m N Q old μ) (key : ℕ → ℕ)
    (hoffsets : ∀ t ≤ numBands L m N ^ 2,
      old (Wanted.offsetAddress L m N Q + t) = Nat.count (fun k => key k < t) Q)
    {t : ℕ} (ht : t < numBands L m N ^ 2) :
    μ (offsetBase L m N Q + t) ≤ μ (offsetBase L m N Q + t + 1) ∧
      μ (offsetBase L m N Q + t + 1) ≤ Q := by
  rw [show offsetBase L m N Q + t + 1 = offsetBase L m N Q + (t + 1) by omega,
    h.offsets t ht.le, h.offsets (t + 1) (by omega), hoffsets t ht.le,
    hoffsets (t + 1) (by omega)]
  exact ⟨Nat.count_mono_left (fun k _ hk => by omega), Nat.count_le _⟩

/-- The length of a saved tile span is the number of input positions with that tile's key. -/
public theorem SavedGroups.span_length {L m N Q : ℕ} {old μ : ℕ → ℕ}
    (h : SavedGroups L m N Q old μ) (key : ℕ → ℕ)
    (hoffsets : ∀ t ≤ numBands L m N ^ 2,
      old (Wanted.offsetAddress L m N Q + t) = Nat.count (fun k => key k < t) Q)
    {t : ℕ} (ht : t < numBands L m N ^ 2) :
    μ (offsetBase L m N Q + t + 1) - μ (offsetBase L m N Q + t) =
      Nat.count (fun k => key k = t) Q := by
  rw [Nat.add_assoc, h.offsets _ ht, h.offsets _ ht.le, hoffsets _ ht, hoffsets _ ht.le,
    CountingSort.count_lt_succ, Nat.add_sub_cancel_left]

/-- Earlier-key positions precede a tile's saved lower offset. -/
public theorem SavedGroups.position_lt_span {L m N Q : ℕ} {old μ : ℕ → ℕ}
    (h : SavedGroups L m N Q old μ) (key : ℕ → ℕ)
    (hoffsets : ∀ t ≤ numBands L m N ^ 2,
      old (Wanted.offsetAddress L m N Q + t) = Nat.count (fun k => key k < t) Q)
    {t i : ℕ} (ht : t ≤ numBands L m N ^ 2) (hi : i < Q) (hk : key i < t) :
    CountingSort.position key Q i < μ (offsetBase L m N Q + t) := by
  rw [h.offsets t ht, hoffsets t ht]
  exact (CountingSort.position_mem key hi).2.trans_le
    (Nat.count_mono_left fun k _ hkt => hkt.trans_le hk)

/-- Decode the protected words at a tile's actual saved offsets. The decoded queries have
exactly the original tile's finite request set, including when its span is empty. -/
public theorem SavedGroups.decode_span {L m N t : ℕ} (hm : m ≤ L)
    (qs : List (Fin N × Fin N)) {old μ : ℕ → ℕ} (h : SavedGroups L m N qs.length old μ)
    (hvalues : ∀ i : Fin qs.length,
      old (Wanted.codeAddress L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        (PrunedQuery.queryIndex
          (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val)
    (hoffsets : ∀ t ≤ numBands L m N ^ 2,
      old (Wanted.offsetAddress L m N qs.length + t) =
        Nat.count (fun k => (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) k < t) qs.length)
    (ht : t < numBands L m N ^ 2) :
    let B := numBands L m N
    let T := (t / B, t % B)
    let a := μ (offsetBase L m N qs.length + t)
    let b := μ (offsetBase L m N qs.length + t + 1)
    T ∈ tiles L m N ∧ T.1 * B + T.2 = t ∧ (a ≤ b ∧ b ≤ qs.length) ∧
      ∃ queries : Fin (b - a) → OutStr L,
        (∀ i, μ (codeBase L m N qs.length + (a + i.val)) =
          (PrunedQuery.queryIndex (queries i)).val) ∧
        Finset.univ.image queries = wantedStrings (MaskTable.layout hm) qs.toFinset T.1 T.2 := by
  intro B T a b
  have hB : 0 < B := Nat.pos_of_ne_zero fun h₀ : numBands L m N = 0 => by simp [h₀] at ht
  have hT : T ∈ tiles L m N :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hB).mpr (by
      simpa only [B, pow_two] using ht)), Finset.mem_range.mpr (Nat.mod_lt t hB)⟩
  have hnum : T.1 * numBands L m N + T.2 = t := by
    simpa only [T, Nat.mul_comm] using Nat.div_add_mod t B
  have habQ : a ≤ b ∧ b ≤ qs.length :=
    h.span_bounds (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) hoffsets ht
  have hpos (i : Fin (b - a)) : a + i.val < qs.length := by
    have hi := i.isLt
    lia
  let queries (i : Fin (b - a)) := PrunedQuery.queryAt
    ⟨μ (codeBase L m N qs.length + (a + i.val)), by
      rw [h.codes _ (hpos i)]
      exact router_code_lt hm qs old hvalues _ (hpos i)⟩
  have hinput (i : Fin (b - a)) : μ (codeBase L m N qs.length + (a + i.val)) =
      (PrunedQuery.queryIndex (queries i)).val := by
    simp only [queries, PrunedQuery.queryIndex_queryAt]
  refine ⟨hT, hnum, habQ, queries, hinput, ?_⟩
  have hspan := Wanted.code_span_eq_wantedStrings hm qs old T hT hvalues hoffsets
  have ha : old (Wanted.offsetAddress L m N qs.length + t) = a := (h.offsets _ ht.le).symm
  have hb : old (Wanted.offsetAddress L m N qs.length + (t + 1)) = b := by
    simpa only [b, Nat.add_assoc] using (h.offsets (t + 1) ht).symm
  rw [hnum, ha, hb] at hspan
  have hword (i : Fin (b - a)) : old (Wanted.codeAddress L m N qs.length + (a + i.val)) =
      (PrunedQuery.queryIndex (queries i)).val :=
    (h.codes _ (hpos i)).symm.trans (hinput i)
  have hinj : Function.Injective (fun v : OutStr L => (PrunedQuery.queryIndex v).val) :=
    fun u v he => by
      simpa only [PrunedQuery.queryAt_queryIndex] using congrArg PrunedQuery.queryAt (Fin.ext he)
  apply Finset.image_injective hinj
  rw [Finset.image_image, ← hspan]
  ext word
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact ⟨a + i.val, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by have hi := i.isLt; lia⟩,
      hword i⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hj
    let i : Fin (b - a) := ⟨j - a, by lia⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [← hword i, show a + i.val = j from Nat.add_sub_of_le hlo]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
