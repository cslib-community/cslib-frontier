/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
public import Mathlib.Data.Finset.Sort
import CslibFrontier.Foundations.Data.Fin.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Splitting segments at coordinate levels

A finite set of real coordinate levels cuts a segment at distinct strict interior parameters.
The sorted parameter list also includes the endpoints. Its consecutive closed intervals cover
the original segment, and no level lies strictly between their endpoint coordinates. A map
that preserves affine interpolation on each such region therefore preserves interpolation
on every piece. Plateau shear uses the imaginary coordinate; frozen-reference compression
uses the real coordinate.
-/

public section

namespace Cslib.Polygonal

/-- Strict interior parameters where the affine coordinate from `a` to `b` reaches a level.
A constant coordinate contributes no cuts, even if it lies at a declared level. -/
@[expose] noncomputable def segmentInteriorCuts (levels : Finset ℝ) (a b : ℝ) : Finset ℝ :=
  if b = a then ∅ else
    (levels.image fun y => (y - a) / (b - a)).filter fun t => 0 < t ∧ t < 1

/-- There are at most as many strict interior parameters as supplied coordinate levels. -/
theorem segmentInteriorCuts_card_le (levels : Finset ℝ) (a b : ℝ) :
    (segmentInteriorCuts levels a b).card ≤ levels.card := by
  unfold segmentInteriorCuts
  split_ifs
  · simp
  · exact (Finset.card_filter_le _ _).trans Finset.card_image_le

/-- The strictly increasing list of interior cut parameters together with 0 and 1. -/
noncomputable def segmentCuts (levels : Finset ℝ) (a b : ℝ) : List ℝ :=
  (insert 0 (insert 1 (segmentInteriorCuts levels a b))).sort

private theorem segmentInteriorCuts_mem_Ioo {levels : Finset ℝ} {a b : ℝ} {t : ℝ}
    (ht : t ∈ segmentInteriorCuts levels a b) : t ∈ Set.Ioo 0 1 := by
  unfold segmentInteriorCuts at ht
  split_ifs at ht with heq
  · exact False.elim (Finset.notMem_empty t ht)
  · exact (Finset.mem_filter.mp ht).2

/-- Membership splits into the two endpoints and the strict interior parameters. -/
theorem mem_segmentCuts {levels : Finset ℝ} {a b : ℝ} {t : ℝ} :
    t ∈ segmentCuts levels a b ↔ t = 0 ∨ t = 1 ∨ t ∈ segmentInteriorCuts levels a b := by
  simp only [segmentCuts, Finset.mem_sort, Finset.mem_insert]

/-- All listed parameters lie in the closed unit interval. -/
theorem segmentCuts_mem_Icc {levels : Finset ℝ} {a b : ℝ} {t : ℝ}
    (ht : t ∈ segmentCuts levels a b) : t ∈ Set.Icc 0 1 := by
  rcases mem_segmentCuts.mp ht with rfl | rfl | ht
  · constructor <;> norm_num
  · constructor <;> norm_num
  · exact ⟨(segmentInteriorCuts_mem_Ioo ht).1.le, (segmentInteriorCuts_mem_Ioo ht).2.le⟩

/-- The sorted cut list has strictly increasing parameters. -/
theorem segmentCuts_sorted (levels : Finset ℝ) (a b : ℝ) : (segmentCuts levels a b).SortedLT :=
  Finset.sortedLT_sort _

/-- The two endpoints add two entries to the distinct strict interior parameters. -/
theorem segmentCuts_length_eq (levels : Finset ℝ) (a b : ℝ) :
    (segmentCuts levels a b).length = (segmentInteriorCuts levels a b).card + 2 := by
  have hn₀ : (0 : ℝ) ∉ segmentInteriorCuts levels a b :=
    fun ht => (lt_irrefl 0) (segmentInteriorCuts_mem_Ioo ht).1
  have hn₁ : (1 : ℝ) ∉ segmentInteriorCuts levels a b :=
    fun ht => (lt_irrefl 1) (segmentInteriorCuts_mem_Ioo ht).2
  simp only [segmentCuts, Finset.length_sort,
    Finset.card_insert_of_notMem
      (by simp [hn₀] : (0 : ℝ) ∉ insert 1 (segmentInteriorCuts levels a b)),
    Finset.card_insert_of_notMem hn₁]

private theorem segmentCuts_length_ge_two (levels : Finset ℝ) (a b : ℝ) :
    2 ≤ (segmentCuts levels a b).length := by
  rw [segmentCuts_length_eq]
  omega

/-- The first and last listed parameters are the ends of the original segment. -/
theorem segmentCuts_first_last (levels : Finset ℝ) (a b : ℝ) :
    (segmentCuts levels a b)[0]'(by have := segmentCuts_length_ge_two levels a b; omega) = 0 ∧
      (segmentCuts levels a b)[(segmentCuts levels a b).length - 1]'(by
        have := segmentCuts_length_ge_two levels a b; omega) = 1 := by
  let L := segmentCuts levels a b
  have hmono := (segmentCuts_sorted levels a b).strictMono_get
  have hzero : (0 : ℝ) ∈ L := mem_segmentCuts.mpr (Or.inl rfl)
  have hone : (1 : ℝ) ∈ L := mem_segmentCuts.mpr (Or.inr (Or.inl rfl))
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hzero
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hone
  have hlen : 2 ≤ L.length := segmentCuts_length_ge_two levels a b
  constructor
  · apply le_antisymm
    · exact (hmono.monotone (show (⟨0, by dsimp only [L] at *; omega⟩ : Fin L.length) ≤ i from
        Nat.zero_le _)).trans_eq hi
    · exact (segmentCuts_mem_Icc (List.get_mem L _)).1
  · apply le_antisymm
    · exact (segmentCuts_mem_Icc (List.get_mem L _)).2
    · exact hj.symm.trans_le (hmono.monotone (show j ≤
        (⟨L.length - 1, by dsimp only [L] at *; omega⟩ : Fin L.length) from
          Nat.le_sub_one_of_lt j.isLt))

private theorem segmentCuts_adjacent_no_level_real {levels : Finset ℝ} {a b : ℝ} {k : ℕ}
    (hk : k + 1 < (segmentCuts levels a b).length) :
    ∀ y ∈ levels,
      y ∉ Set.Ioo
        (min (AffineMap.lineMap a b (segmentCuts levels a b)[k])
          (AffineMap.lineMap a b (segmentCuts levels a b)[k + 1]))
        (max (AffineMap.lineMap a b (segmentCuts levels a b)[k])
          (AffineMap.lineMap a b (segmentCuts levels a b)[k + 1])) := by
  let L := segmentCuts levels a b
  have hkL : k + 1 < L.length := hk
  let α := L[k]
  let β := L[k + 1]
  have hmono := (segmentCuts_sorted levels a b).strictMono_get
  have hαβ : α < β := hmono (show (⟨k, by omega⟩ : Fin L.length) < ⟨k + 1, hk⟩ from
    Nat.lt_succ_self k)
  have hα := segmentCuts_mem_Icc (List.getElem_mem (l := L) (by omega : k < L.length))
  have hβ := segmentCuts_mem_Icc (List.getElem_mem (l := L) hk)
  intro y hy hbetween
  simp only [Set.mem_Ioo, AffineMap.lineMap_apply_ring'] at hbetween
  have hne : b - a ≠ 0 := by
    intro he
    simp only [he, mul_zero, zero_add, min_self, max_self] at hbetween
    exact (not_lt_of_ge hbetween.1.le) hbetween.2
  let t := (y - a) / (b - a)
  have ht_eq : t * (b - a) + a = y := by
    dsimp [t]
    field_simp [hne]
    ring
  have ht : α < t ∧ t < β := by
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have he : β * (b - a) + a < α * (b - a) + a := by nlinarith
      rw [min_eq_right he.le, max_eq_left he.le] at hbetween
      constructor
      · exact (mul_lt_mul_right_of_neg hneg).mp (by linarith [hbetween.2])
      · exact (mul_lt_mul_right_of_neg hneg).mp (by linarith [hbetween.1])
    · have he : α * (b - a) + a < β * (b - a) + a := by nlinarith
      rw [min_eq_left he.le, max_eq_right he.le] at hbetween
      constructor
      · exact (mul_lt_mul_iff_left₀ hpos).mp (by linarith [hbetween.1])
      · exact (mul_lt_mul_iff_left₀ hpos).mp (by linarith [hbetween.2])
  have htm : t ∈ segmentInteriorCuts levels a b := by
    rw [segmentInteriorCuts, ite_eq_right (sub_ne_zero.mp hne), Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨y, hy, rfl⟩,
      lt_of_le_of_lt hα.1 ht.1, lt_of_lt_of_le ht.2 hβ.2⟩
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (mem_segmentCuts.mpr (Or.inr (Or.inr htm)))
  have hkj : (⟨k, by omega⟩ : Fin L.length) < j := (hmono.lt_iff_lt).mp (hj ▸ ht.1)
  have hjk : j < (⟨k + 1, hk⟩ : Fin L.length) := (hmono.lt_iff_lt).mp (hj ▸ ht.2)
  change k < j.val at hkj
  change j.val < k + 1 at hjk
  omega

/-- Every closed unit parameter belongs to a consecutive closed cut interval. -/
theorem segmentCuts_cover {levels : Finset ℝ} {a b : ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∃ (k : ℕ) (hk : k + 1 < (segmentCuts levels a b).length),
      (segmentCuts levels a b)[k] ≤ t ∧ t ≤ (segmentCuts levels a b)[k + 1] := by
  let L := segmentCuts levels a b
  have hlen : 2 ≤ L.length := segmentCuts_length_ge_two levels a b
  have hends : L[0] = 0 ∧ L[L.length - 1] = 1 := segmentCuts_first_last levels a b
  dsimp only [L] at hlen hends
  by_cases ht1 : t = 1
  · refine ⟨L.length - 2, by dsimp only [L] at *; omega, ?_, ?_⟩
    · exact (segmentCuts_mem_Icc
        (List.getElem_mem (by dsimp only [L] at *; omega))).2.trans_eq ht1.symm
    · change t ≤ L[L.length - 2 + 1]
      simp only [show L.length - 2 + 1 = L.length - 1 by dsimp only [L] at *; omega]
      exact ht1.trans_le (show L[L.length - 1] = 1 from hends.2).symm.le
  · let f : Fin (L.length - 1 + 1) → ℝ := fun j => L[j.val]'(by
      have := j.isLt
      dsimp only [L] at *
      omega)
    obtain ⟨i, hlo, hhi⟩ := Fin.exists_le_lt_adjacent (f := f) (x := t)
      (by change L[0] ≤ t; rw [show L[0] = 0 from hends.1]; exact ht.1)
      (by
        change t < L[L.length - 1]
        rw [show L[L.length - 1] = 1 from hends.2]
        exact lt_of_le_of_ne ht.2 ht1)
    exact ⟨i.val, by have := i.isLt; dsimp only [L] at *; omega, hlo, hhi.le⟩

/-- Every listed parameter except the final endpoint is strictly below one. -/
theorem segmentCuts_dropLast_bounds {levels : Finset ℝ} {a b : ℝ} {t : ℝ}
    (ht : t ∈ (segmentCuts levels a b).dropLast) : 0 ≤ t ∧ t < 1 := by
  let L := segmentCuts levels a b
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ht
  have hlen : 2 ≤ L.length := segmentCuts_length_ge_two levels a b
  have hilt : i.val < L.length - 1 := by simpa only [List.length_dropLast] using i.isLt
  have hil : i.val < L.length := by omega
  have ht' : L[i.val] = t := by simpa only [List.get_eq_getElem, List.getElem_dropLast] using hi
  constructor
  · exact ht' ▸ (segmentCuts_mem_Icc (List.getElem_mem hil)).1
  · have hm := (segmentCuts_sorted levels a b).strictMono_get
      (show (⟨i.val, hil⟩ : Fin L.length) < ⟨L.length - 1, by omega⟩ from hilt)
    change L[i.val] < L[L.length - 1] at hm
    rw [ht', show L[L.length - 1] = 1 from (segmentCuts_first_last levels a b).2] at hm
    exact hm

/-- No level lies strictly between consecutive sample coordinates, for any real affine
coordinate on the plane. -/
theorem segmentCuts_adjacent_no_level (levels : Finset ℝ) (coordinate : ℂ →ᵃ[ℝ] ℝ)
    {a b : ℂ} {k : ℕ} (hk : k + 1 < (segmentCuts levels (coordinate a) (coordinate b)).length) :
    let L := segmentCuts levels (coordinate a) (coordinate b)
    ∀ y ∈ levels, y ∉ Set.Ioo
      (min (coordinate (AffineMap.lineMap a b L[k])) (coordinate (AffineMap.lineMap a b L[k + 1])))
      (max (coordinate (AffineMap.lineMap a b L[k]))
        (coordinate (AffineMap.lineMap a b L[k + 1]))) := by
  dsimp only
  intro y hy
  rw [coordinate.apply_lineMap, coordinate.apply_lineMap]
  exact segmentCuts_adjacent_no_level_real hk y hy

/-- A map preserving straight interpolation between declared coordinate levels preserves it on
each consecutive indexed piece of the cut segment, including both parameter endpoints. -/
theorem segmentCuts_map_lineMap (levels : Finset ℝ) (coordinate : ℂ →ᵃ[ℝ] ℝ) (F : ℂ → ℂ)
    (hF : ∀ a b : ℂ,
      (∀ y ∈ levels, y ∉ Set.Ioo (min (coordinate a) (coordinate b))
          (max (coordinate a) (coordinate b))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        F (AffineMap.lineMap a b t) = AffineMap.lineMap (F a) (F b) t)
    (a b : ℂ) {k : ℕ} (hk : k + 1 < (segmentCuts levels (coordinate a) (coordinate b)).length)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    let L := segmentCuts levels (coordinate a) (coordinate b)
    F (AffineMap.lineMap a b (AffineMap.lineMap L[k] L[k + 1] t)) =
      AffineMap.lineMap (F (AffineMap.lineMap a b L[k]))
        (F (AffineMap.lineMap a b L[k + 1])) t := by
  dsimp only
  rw [(AffineMap.lineMap a b).apply_lineMap]
  exact hF _ _ (segmentCuts_adjacent_no_level levels coordinate hk) t ht

end Cslib.Polygonal
