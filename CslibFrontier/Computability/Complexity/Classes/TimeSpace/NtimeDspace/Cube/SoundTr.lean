/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.SoundCodes

/-!
# The transport states of the formula

* `upRule_bounded`, `downRule_bounded`: the half-rules have exponents at most the weights of their
  ends.
* `trMean_root_up`, `trMean_root_down`: the root of a rectangle factor is `[z^e] N↑` or `[z^e] N↓`.
* `trMean_pivot`: the pivot recursion through the pivot codes.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

/-! ### The rules are bounded -/

theorem upRule_mem (p : HPlace) (i : ℕ) (p' : HPlace) (j : ℕ) :
    upRule p i p' j ∈ gradeGroup (i + 1 + (j + 1)) := by
  rcases p with _ | p <;> rcases p' with _ | p' <;> (try cases p) <;> (try cases p') <;>
    simp only [upRule] <;>
    first
    | with_reducible exact zero_mem _
    | (with_reducible apply eqL_mem_gradeGroup); omega
    | (with_reducible apply oneSubZ2_mul_mem_gradeGroup); omega
    | (with_reducible apply oneSubZm2_mul_mem_gradeGroup); omega

theorem downRule_mem (p : HPlace) (i : ℕ) (p' : HPlace) (j : ℕ) :
    downRule p i p' j ∈ gradeGroup (i + 1 + (j + 1)) := by
  rcases p with _ | p <;> rcases p' with _ | p' <;> (try cases p) <;> (try cases p') <;>
    simp only [downRule] <;>
    first
    | with_reducible exact zero_mem _
    | (with_reducible apply eqL_mem_gradeGroup); omega
    | (with_reducible apply cubeC_mem_gradeGroup); omega
    | (with_reducible apply bar_cubeC_mem_gradeGroup); omega

theorem hRule_bounded (up : Bool) : RuleBounded (hRule up) := by
  intro p i p' j e he
  have hm : hRule up p i p' j ∈ gradeGroup (i + 1 + (j + 1)) := by
    cases up
    · exact downRule_mem p i p' j
    · exact upRule_mem p i p' j
  have := (hm e he).2
  push_cast at this ⊢
  linarith

/-! ### Source intervals -/

section Src

variable (up : Bool) (x y m : Label)

theorem length_srcSub {lo hi : ℕ} (hhi : hi ≤ (srcList up x y m).length) (hlo : lo ≤ hi) :
    (srcSub up x y m lo hi).length = hi - lo := by
  simp only [srcSub, List.length_take, List.length_drop]; omega

theorem take_srcSub {lo hi ν : ℕ} (hν : ν ≤ hi - lo) :
    (srcSub up x y m lo hi).take ν = srcSub up x y m lo (lo + ν) := by
  simp only [srcSub, List.take_take]
  congr 1; omega

theorem drop_srcSub {lo hi ν : ℕ} :
    (srcSub up x y m lo hi).drop (ν + 1) = srcSub up x y m (lo + ν + 1) hi := by
  simp only [srcSub, List.drop_take, List.drop_drop]
  congr 1 <;> first | omega | (congr 1; omega)

theorem getD_srcSub {lo hi ν : ℕ} (hν : ν < hi - lo) (t : HPlace × ℕ) :
    (srcSub up x y m lo hi).getD ν t = (srcList up x y m).getD (lo + ν) t := by
  simp only [srcSub, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hν]

theorem srcSub_self (lo : ℕ) : srcSub up x y m lo lo = [] := by simp [srcSub]

theorem srcSub_root : srcSub up x y m 0 (srcList up x y m).length = srcList up x y m := by
  simp [srcSub]

theorem coe_srcList_up : (↑(srcList true x y m) : Multiset (HPlace × ℕ)) =
    located (some Corner.x) x.1 + located (some Corner.y) y.1 + located none m.2 := by
  simp only [srcList, if_true, ← Multiset.coe_add, ← Multiset.map_coe, Multiset.sort_eq, located]

theorem coe_srcList_down : (↑(srcList false x y m) : Multiset (HPlace × ℕ)) =
    located (some Corner.u) x.1 + located (some Corner.v) y.1 + located none m.1 := by
  simp only [srcList, Bool.false_eq_true, if_false, ← Multiset.coe_add, ← Multiset.map_coe,
    Multiset.sort_eq, located]

theorem trMean_root_up (e : ℤ) :
    Setup.trMean true x y m 0 (srcList true x y m).length (tgtMs true x y m) e = (nUp x y m).coeff
        e := by
  simp only [Setup.trMean, srcSub_root, transportL, coe_srcList_up, nUp, tgtMs, if_true, hRule]

theorem trMean_root_down (e : ℤ) :
    Setup.trMean false x y m 0 (srcList false x y m).length (tgtMs false x y m) e =
      (nDown x y m).coeff e := by
  simp only [Setup.trMean, srcSub_root, transportL, coe_srcList_down, nDown, tgtMs,
    Bool.false_eq_true, if_false, hRule]

theorem tgtMs_valid : ∀ s ∈ tgtMs up x y m, ValidPl up s.1 := by
  intro s hs
  cases up <;>
  · simp only [tgtMs, Bool.false_eq_true, if_false, if_true, Multiset.mem_add, located,
      Multiset.mem_map] at hs
    rcases hs with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩
    · exact ⟨0, by omega, by simp [placeOf]⟩
    · exact ⟨1, by omega, by simp [placeOf]⟩
    · exact ⟨2, by omega, by simp [placeOf]⟩

theorem trMean_empty (lo : ℕ) (T : Multiset (HPlace × ℕ)) (c : ℤ) :
    Setup.trMean up x y m lo lo T c = if T = 0 ∧ c = 0 then 1 else 0 := by
  simp only [Setup.trMean, srcSub_self, transportL_nil]
  by_cases hT : T = 0
  · simp only [hT, if_true, true_and]
    rw [← LaurentPolynomial.T_zero, LaurentPolynomial.T_apply]
    by_cases hc : c = 0 <;> simp [hc, eq_comm]
  · simp [hT]

end Src

/-! ### The pivot recursion through the codes -/

/-- The fields of a pivot index. -/
abbrev PivX := ℕ × (HPlace × ℕ) × Multiset (HPlace × ℕ) × ℤ × ℤ

/-- The code of the fields of a pivot index. -/
noncomputable def pivCodeX (up : Bool) (W : ℕ) (d : PivX) : ℕ :=
  pivotCode up W d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2

/-- The validity of a pivot index, field by field. -/
def PivOK (l : List (HPlace × ℕ)) (T : Multiset (HPlace × ℕ)) (W : ℕ) (d : PivX) : Prop :=
  d.1 < l.length ∧ d.2.1 ∈ T ∧ d.2.2.1 ≤ T - {d.2.1} ∧ PivotCond l T d.1 d.2.1 d.2.2.1 ∧
    |d.2.2.2.1| ≤ W ∧ |d.2.2.2.2| ≤ W

theorem pivotValid_iff (up : Bool) (x y m : Label) (lo hi : ℕ) (T : Multiset (HPlace × ℕ)) (i : ℕ) :
    PivotValid up x y m lo hi T i ↔
      pivCodeX up (tWt (srcSub up x y m lo hi) T) (decodePivot up (tWt (srcSub up x y m lo hi) T) i)
          = i ∧
        PivOK (srcSub up x y m lo hi) T (tWt (srcSub up x y m lo hi) T)
          (decodePivot up (tWt (srcSub up x y m lo hi) T) i) := by
  unfold PivotValid
  dsimp only
  generalize decodePivot up (tWt (srcSub up x y m lo hi) T) i = d
  obtain ⟨ν, t, T₁, c₁, c₀⟩ := d
  rfl

theorem lwt_le_of_mem {T : Multiset (HPlace × ℕ)} {t : HPlace × ℕ} (ht : t ∈ T) :
    lwt t ≤ (T.map lwt).sum :=
  Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ ht)

theorem sum_lwt_mono {T₁ T : Multiset (HPlace × ℕ)} (h : T₁ ≤ T) :
    (T₁.map lwt).sum ≤ (T.map lwt).sum := by
  obtain ⟨R, rfl⟩ := Multiset.le_iff_exists_add.mp h
  simp

theorem length_le_tWt (l : List (HPlace × ℕ)) (T : Multiset (HPlace × ℕ)) : l.length ≤ tWt l T := by
  unfold tWt
  have : l.length ≤ (l.map lwt).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons, lwt]; omega
  omega

/-- The summand of the pivot recursion. -/
noncomputable def pivTerm (up : Bool) (x y m : Label) (lo hi : ℕ) (T : Multiset (HPlace × ℕ))
    (c : ℤ)
    (d : PivX) : ℤ :=
  Setup.trMean up x y m lo (lo + d.1) d.2.2.1 d.2.2.2.1 *
    (Setup.ruleCoeff up x y m (lo + d.1) d.2.1 d.2.2.2.2 *
      Setup.trMean up x y m (lo + d.1 + 1) hi (T - d.2.2.1 - {d.2.1}) (c - d.2.2.2.1 - d.2.2.2.2))

theorem sum_powerset_sub {M : Type*} [AddCommMonoid M] (T : Multiset (HPlace × ℕ)) (t : HPlace × ℕ)
    (F : Multiset (HPlace × ℕ) → M) :
    ∑ T₁ ∈ (T - {t}).powerset.toFinset, F T₁ =
      ∑ T₁ ∈ T.powerset.toFinset, if T₁ ≤ T - {t} then F T₁ else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext T₁
  simp only [Multiset.mem_toFinset, Multiset.mem_powerset, Finset.mem_filter]
  exact ⟨fun h => ⟨h.trans tsub_le_self, h⟩, fun h => h.2⟩

theorem ite_sum {ι M : Type*} [AddCommMonoid M] (p : Prop) [Decidable p] (s : Finset ι) (f : ι → M)
    :
    (if p then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if p then f i else 0 := by
  split_ifs <;> simp

open Classical in
/-- **The pivot recursion through the codes.** -/
theorem trMean_pivot (up : Bool) (x y m : Label) {lo hi : ℕ} (T : Multiset (HPlace × ℕ)) (c : ℤ)
    (hlo : lo < hi) (hhi : hi ≤ (srcList up x y m).length) (hT : ∀ s ∈ T, ValidPl up s.1) :
    Setup.trMean up x y m lo hi T c =
      ∑ i ∈ range (2 ^ pivWidth (tWt (srcSub up x y m lo hi) T)),
        if PivotValid up x y m lo hi T i then
          pivTerm up x y m lo hi T c (decodePivot up (tWt (srcSub up x y m lo hi) T) i) else 0 := by
  classical
  set l := srcSub up x y m lo hi with hl
  set W := tWt l T with hW
  have hlen : l.length = hi - lo := length_srcSub up x y m hhi hlo.le
  have hne : l ≠ [] := fun h => by rw [h] at hlen; simp at hlen; omega
  have hTW : (T.map lwt).sum ≤ W := by simp only [hW, tWt]; omega
  have hlW : l.length ≤ W := length_le_tWt l T
  let I := Icc (-(W : ℤ)) W
  let Sx : Finset PivX := (range l.length ×ˢ
      (T.toFinset ×ˢ (T.powerset.toFinset ×ˢ (I ×ˢ I)))).filter
    fun d => d.2.2.1 ≤ T - {d.2.1} ∧ PivotCond l T d.1 d.2.1 d.2.2.1
  -- the right side of the pivot recursion as a sum over `Sx`
  have hR : (transportL l T (hRule up)).coeff c = ∑ d ∈ Sx, pivTerm up x y m lo hi T c d := by
    rw [transportL_pivot (hRule_bounded up) l hne T c, Finset.sum_filter]
    simp only [Finset.sum_product]
    refine sum_congr rfl fun ν hν => sum_congr rfl fun t _ => ?_
    rw [sum_powerset_sub]
    refine sum_congr rfl fun T₁ _ => ?_
    by_cases h1 : T₁ ≤ T - {t}
    · by_cases h2 : PivotCond l T ν t T₁
      · rw [if_pos h1, if_pos h2]
        refine sum_congr rfl fun c₁ _ => sum_congr rfl fun c₀ _ => ?_
        rw [if_pos ⟨h1, h2⟩]
        have hν' : ν < hi - lo := by rw [← hlen]; exact mem_range.mp hν
        simp only [pivTerm, Setup.trMean, Setup.ruleCoeff, hl, take_srcSub up x y m hν'.le,
          drop_srcSub, getD_srcSub up x y m hν']
        ring
      · rw [if_pos h1, if_neg h2]
        symm
        exact sum_eq_zero fun c₁ _ => sum_eq_zero fun c₀ _ => if_neg (fun h => h2 h.2)
    · rw [if_neg h1]
      symm
      exact sum_eq_zero fun c₁ _ => sum_eq_zero fun c₀ _ => if_neg (fun h => h1 h.1)
  show (transportL l T (hRule up)).coeff c = _
  rw [hR, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (decodePivot up W) (pivCodeX up W) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hmem
    obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := (pivotValid_iff up x y m lo hi T i).mp
        (mem_filter.mp hmem).2
    simp only [Sx, mem_filter, mem_product, mem_range, Multiset.mem_toFinset, Multiset.mem_powerset,
        I,
      mem_Icc]
    rw [abs_le] at h5 h6
    exact ⟨⟨h1, h2, h3.trans tsub_le_self, h5, h6⟩, h3, h4⟩
  · intro d hd
    simp only [Sx, mem_filter, mem_product, mem_range, Multiset.mem_toFinset, Multiset.mem_powerset,
        I,
      mem_Icc] at hd
    obtain ⟨⟨h1, h2, -, h5, h6⟩, h3, h4⟩ := hd
    have hT₁ : d.2.2.1 ≤ T := h3.trans tsub_le_self
    have key := decode_pivotCode up (W := W) (ν := d.1) (t := d.2.1) (T₁ := d.2.2.1)
      (c₁ := d.2.2.2.1) (c₀ := d.2.2.2.2) (by omega) (hT _ h2)
      (by have := lwt_le_of_mem h2; simp only [lwt] at this; omega)
      (fun s hs => hT s (Multiset.mem_of_le hT₁ hs)) ((sum_lwt_mono hT₁).trans hTW)
      (abs_le.mpr h5) (abs_le.mpr h6)
    refine mem_filter.mpr ⟨mem_range.mpr key.2, (pivotValid_iff up x y m lo hi T _).mpr ?_⟩
    simp only [pivCodeX] at key ⊢
    rw [key.1]
    exact ⟨rfl, h1, h2, h3, h4, abs_le.mpr h5, abs_le.mpr h6⟩
  · intro i hmem
    exact ((pivotValid_iff up x y m lo hi T i).mp (mem_filter.mp hmem).2).1
  · intro d hd
    simp only [Sx, mem_filter, mem_product, mem_range, Multiset.mem_toFinset, Multiset.mem_powerset,
        I,
      mem_Icc] at hd
    obtain ⟨⟨h1, h2, -, h5, h6⟩, h3, h4⟩ := hd
    have hT₁ : d.2.2.1 ≤ T := h3.trans tsub_le_self
    exact (decode_pivotCode up (W := W) (ν := d.1) (t := d.2.1) (T₁ := d.2.2.1)
      (c₁ := d.2.2.2.1) (c₀ := d.2.2.2.2) (by omega) (hT _ h2)
      (by have := lwt_le_of_mem h2; simp only [lwt] at this; omega)
      (fun s hs => hT s (Multiset.mem_of_le hT₁ hs)) ((sum_lwt_mono hT₁).trans hTW)
      (abs_le.mpr h5) (abs_le.mpr h6)).1

end Cslib.Complexity.NtimeDspace.Cube
