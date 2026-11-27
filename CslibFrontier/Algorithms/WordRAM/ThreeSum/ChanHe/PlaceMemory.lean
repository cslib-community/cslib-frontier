/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.Place

/-!
# Meaning of the native Chan–He placement writes

## Main results

* `Place.heavyList_nodup`: compact output retains injective enumeration.
* `Place.memory_heavy`: each compact cell contains its original signed integer.

## References

These memory proofs are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Place

open Cslib.WordRAM.Signed

/-- Selecting a subsequence preserves injective input enumeration. -/
theorem heavyList_nodup (values : ℕ → ℤ) (n M : ℕ)
    (hinj : Set.InjOn values (↑(Finset.range n) : Set ℕ)) :
    (heavyList values n M n).Nodup := by
  rw [heavyList_eq_filter]
  exact (List.nodup_range.filter _).map_on fun i hi j hj =>
    hinj (List.mem_filter.mp hi).1 (List.mem_filter.mp hj).1

/-- The number returned by the scan is the exact cardinality of the existing heavy subset. -/
theorem length_heavyList (values : ℕ → ℤ) (n : ℕ) {M : ℕ} (hM : 0 < M)
    (hinj : Set.InjOn values (↑(Finset.range n) : Set ℕ)) :
    (heavyList values n M n).length =
      (Cslib.Algorithms.ThreeSum.ChanHe.heavy ((Finset.range n).image values) M).card := by
  rw [← heavyList_toFinset values n hM hinj]
  exact (List.toFinset_card_of_nodup (heavyList_nodup values n M hinj)).symm

/-- Every compact cell is written once, without padding or a tag. Unused capacity retains
its arbitrary old contents. -/
theorem memory_heavy (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col dist t : ℕ)
    (neg : Bool) (hdisj : out + n ≤ dst) {k : ℕ} (hk : k ≤ n)
    {j : ℕ} (hj : j < (heavyList values n M k).length) :
    memory mem values n M out dst col dist t neg k (out + j) =
      encode ((heavyList values n M k)[j]) := by
  induction k generalizing j with
  | zero => simp only [heavyList, List.length_nil] at hj; omega
  | succ k ih =>
    have hl := length_heavyList_le values n M k
    by_cases hh : 1 < Histogram.count (fun i => residueKey M (values i)) n
        (residueKey M (values k)) <;>
      simp only [heavyList, memory, write, hh, ↓reduceIte, List.append_nil] at hj ⊢
    · by_cases hj' : j < (heavyList values n M k).length
      · rw [Function.update_of_ne (by omega), ih (by omega) hj', List.getElem_append_left hj']
      · simp [Nat.eq_of_lt_succ_of_not_lt (by simpa using hj) hj']
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact ih (by omega) hj

/-- The signed target keys identify exactly the same buckets as the original keys. -/
theorem targetKey_eq_iff {M : ℕ} (hM : 0 < M) (neg : Bool) (a b : ℤ) :
    targetKey M neg a = targetKey M neg b ↔ residueKey M a = residueKey M b := by
  cases neg <;> simp [targetKey_eq hM, signedValue, residueKey_neg_eq_iff hM]

/-- The two copies cannot alias another bucket's cells. -/
theorem targetKey_eq_of_address_eq {M dst col dist r s : ℕ} (hr : r < M) (hs : s < M)
    (hd : dist = 0 ∨ dist = 4 * M) {a : ℕ}
    (ha : a = dst + 4 * r + col ∨ a = dst + 4 * r + col + dist)
    (hb : a = dst + 4 * s + col ∨ a = dst + 4 * s + col + dist) : r = s := by
  rcases hd with hd | hd <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

/-- A light entry is written to all of its required cells, and no later input can overwrite it.
The count-one hypothesis itself proves uniqueness of the position. -/
theorem memory_light (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col dist t : ℕ)
    (neg : Bool) (hM : 0 < M) (hd : dist = 0 ∨ dist = 4 * M) (hdisj : out + n ≤ dst)
    {i k a : ℕ} (hk : k ≤ n) (hi : i < k)
    (hlight : Histogram.count (fun j => residueKey M (values j)) n
      (residueKey M (values i)) = 1)
    (ha : a = dst + 4 * targetKey M neg (values i) + col ∨
      a = dst + 4 * targetKey M neg (values i) + col + dist) :
    memory mem values n M out dst col dist t neg k a =
      encode (signedValue neg (values i) + (t : ℤ)) := by
  have ha' : dst ≤ a := by rcases ha with ha | ha <;> omega
  induction k with
  | zero => omega
  | succ k ih =>
    have hl := length_heavyList_le values n M k
    simp only [memory, write]
    split_ifs with hh
    · rw [Function.update_of_ne (by omega)]
      exact ih (by omega) ((Nat.lt_succ_iff_lt_or_eq.mp hi).resolve_right (by rintro rfl; omega))
    · rcases eq_or_ne i k with rfl | he
      · rcases ha with rfl | rfl <;> simp [Function.update_apply]
      · have hlt (j : ℕ) : targetKey M neg (values j) < M :=
          targetKey_eq hM neg _ ▸ residueKey_lt hM _
        have hne (b : ℕ) (hb : b = dst + 4 * targetKey M neg (values k) + col ∨
            b = dst + 4 * targetKey M neg (values k) + col + dist) : a ≠ b := fun hab =>
          he (eq_of_count_one values n M (by omega) (by omega) hlight
            ((targetKey_eq_iff hM neg (values i) (values k)).mp
              (targetKey_eq_of_address_eq (hlt i) (hlt k) hd ha (hab ▸ hb))))
        rw [Function.update_of_ne (hne _ (Or.inr rfl)),
          Function.update_of_ne (hne _ (Or.inl rfl))]
        exact ih (by omega) (by omega)

/-- A packed cell to which no light input is assigned retains its initialized padding. -/
theorem memory_unwritten (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col dist t : ℕ)
    (neg : Bool) (hdisj : out + n ≤ dst) {k a : ℕ} (hk : k ≤ n) (ha : dst ≤ a)
    (hnot : ∀ i < k, Histogram.count (fun j => residueKey M (values j)) n
        (residueKey M (values i)) = 1 →
      a ≠ dst + 4 * targetKey M neg (values i) + col ∧
        a ≠ dst + 4 * targetKey M neg (values i) + col + dist) :
    memory mem values n M out dst col dist t neg k a = mem a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hl := length_heavyList_le values n M k
    simp only [memory, write]
    split_ifs with hh
    · rw [Function.update_of_ne (by omega)]
      exact ih (by omega) (fun i hi => hnot i (by omega))
    · have hc : Histogram.count (fun j => residueKey M (values j)) n
          (residueKey M (values k)) = 1 :=
        le_antisymm (not_lt.mp hh) (count_residue_pos values n M (by omega))
      obtain ⟨hne₁, hne₂⟩ := hnot k (by omega) hc
      rw [Function.update_of_ne hne₂, Function.update_of_ne hne₁]
      exact ih (by omega) (fun i hi => hnot i (by omega))

/-- The first or second packed column is exactly the existing `arrXY`, including all padding
beyond the modulus. No initial contents of the output block are required except its pattern. -/
theorem memory_arrXY (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col t U : ℕ)
    (hM : 0 < M) (hdisj : out + n ≤ dst)
    (hinj : Set.InjOn values (↑(Finset.range n) : Set ℕ)) (i : ℕ)
    (hpad : mem (dst + 4 * i + col) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.pad U + (t : ℤ))) :
    memory mem values n M out dst col 0 t false n (dst + 4 * i + col) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.arrXY
        ((Finset.range n).image values) M U i + (t : ℤ)) := by
  let S := (Finset.range n).image values
  by_cases hc : (Cslib.Algorithms.ThreeSum.ChanHe.bucket S M i).card = 1
  · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
    obtain ⟨hS, hres⟩ := Finset.mem_filter.mp (hz.symm.subset (Finset.mem_singleton_self z))
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hS
    have hkey : residueKey M (values j) = i :=
      (congrArg Int.toNat hres).trans (Int.toNat_natCast i)
    have hlight : Histogram.count (fun k => residueKey M (values k)) n
        (residueKey M (values j)) = 1 := by
      rwa [hkey, count_eq_card_bucket values n hM hinj]
    rw [memory_light mem values n M out dst col 0 t false hM (Or.inl rfl)
      hdisj le_rfl (Finset.mem_range.mp hj) hlight (a := dst + 4 * i + col)
      (Or.inl (by simp only [targetKey, Bool.false_eq_true, ↓reduceIte, hkey]))]
    simp only [S, Cslib.Algorithms.ThreeSum.ChanHe.arrXY, Cslib.Algorithms.ThreeSum.ChanHe.arr,
      ↓reduceIte, hz, Finset.sum_singleton, Finset.card_singleton, signedValue,
      Bool.false_eq_true]
  · simp only [S, Cslib.Algorithms.ThreeSum.ChanHe.arrXY, Cslib.Algorithms.ThreeSum.ChanHe.arr,
      hc, ↓reduceIte, ← hpad]
    refine memory_unwritten mem values n M out dst col 0 t false hdisj le_rfl (by omega) ?_
    intro j _ hlight
    have hne : dst + 4 * i + col ≠ dst + 4 * targetKey M false (values j) + col := fun heq => by
      have hkey : residueKey M (values j) = i := by
        simp only [targetKey, Bool.false_eq_true, ↓reduceIte] at heq; omega
      exact hc (by rwa [← count_eq_card_bucket values n hM hinj, ← hkey])
    exact ⟨hne, by simpa only [Nat.add_zero] using hne⟩

/-- Below `2M`, a residue occurs at exactly its first and second copies. -/
theorem mod_eq_iff_copies {M i r : ℕ} (hi : i < 2 * M) (hr : r < M) :
    i % M = r ↔ i = r ∨ i = r + M := by
  by_cases h : i < M
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega : M ≤ i), Nat.mod_eq_of_lt (by omega : i - M < M)]; omega

/-- The duplicated, negated third column is exactly the existing `arrZ`. -/
theorem memory_arrZ (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col t U : ℕ)
    (hM : 0 < M) (hdisj : out + n ≤ dst)
    (hinj : Set.InjOn values (↑(Finset.range n) : Set ℕ)) (i : ℕ)
    (hpad : mem (dst + 4 * i + col) =
      encode (-Cslib.Algorithms.ThreeSum.ChanHe.pad U + (t : ℤ))) :
    memory mem values n M out dst col (4 * M) t true n (dst + 4 * i + col) =
      encode (Cslib.Algorithms.ThreeSum.ChanHe.arrZ
        ((Finset.range n).image values) M U i + (t : ℤ)) := by
  let vals := fun j => -values j
  let T := (Finset.range n).image vals
  have hT : ((Finset.range n).image values).image (fun z : ℤ => -z) = T := Finset.image_image
  have hinj' : Set.InjOn vals (↑(Finset.range n) : Set ℕ) := fun j hj k hk he =>
    hinj hj hk (neg_injective he)
  have hkey (j : ℕ) : targetKey M true (values j) = residueKey M (vals j) :=
    targetKey_eq hM true _
  have hcount (j : ℕ) :
      Histogram.count (fun k => residueKey M (vals k)) n (residueKey M (vals j)) =
        Histogram.count (fun k => residueKey M (values k)) n (residueKey M (values j)) :=
    count_neg_residue values n hM j
  by_cases hi : i < 2 * M
  · by_cases hc : (Cslib.Algorithms.ThreeSum.ChanHe.bucket T M ((i % M : ℕ) : ℤ)).card = 1
    · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
      obtain ⟨hS, hres⟩ := Finset.mem_filter.mp (hz.symm.subset (Finset.mem_singleton_self z))
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hS
      have hr : residueKey M (vals j) = i % M :=
        (congrArg Int.toNat hres).trans (Int.toNat_natCast _)
      have hlight : Histogram.count (fun k => residueKey M (values k)) n
          (residueKey M (values j)) = 1 := by
        rwa [← hcount, hr, count_eq_card_bucket vals n hM hinj']
      have hcopies := (mod_eq_iff_copies hi (residueKey_lt hM (vals j))).mp hr.symm
      rw [memory_light mem values n M out dst col (4 * M) t true hM (Or.inr rfl)
        hdisj le_rfl (Finset.mem_range.mp hj) hlight (a := dst + 4 * i + col) (by rw [hkey]; omega)]
      simp only [Cslib.Algorithms.ThreeSum.ChanHe.arrZ, hi, ↓reduceIte, hT,
        Cslib.Algorithms.ThreeSum.ChanHe.arr, hz, Finset.sum_singleton,
        Finset.card_singleton, signedValue, vals]
    · simp only [Cslib.Algorithms.ThreeSum.ChanHe.arrZ, hi, ↓reduceIte, hT,
        Cslib.Algorithms.ThreeSum.ChanHe.arr, hc, ← hpad]
      refine memory_unwritten mem values n M out dst col (4 * M) t true hdisj le_rfl (by omega) ?_
      intro j _ hlight
      have hcopies := (mod_eq_iff_copies hi (residueKey_lt hM (vals j))).not.mp fun heq =>
        hc (by rwa [← count_eq_card_bucket vals n hM hinj', heq, hcount])
      rw [hkey]
      omega
  · simp only [Cslib.Algorithms.ThreeSum.ChanHe.arrZ, hi, ↓reduceIte, ← hpad]
    refine memory_unwritten mem values n M out dst col (4 * M) t true hdisj le_rfl (by omega) ?_
    intro j _ _
    have hr : targetKey M true (values j) < M := hkey j ▸ residueKey_lt hM _
    omega

/-- Placement changes only its own packed column. -/
theorem memory_other_column (mem : ℕ → ℕ) (values : ℕ → ℤ) (n M out dst col dist t : ℕ)
    (neg : Bool) (hdisj : out + n ≤ dst) (hc : col < 4)
    (hd : dist = 0 ∨ dist = 4 * M) (u : ℕ) (hu : u % 4 ≠ col) :
    memory mem values n M out dst col dist t neg n (dst + u) = mem (dst + u) := by
  exact memory_unwritten _ _ _ _ _ _ _ _ _ _ hdisj le_rfl (by omega) fun j hj hlight => by omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Place
