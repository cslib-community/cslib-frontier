/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Defs
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The tapes of the Hennie–Stearns machine

Zone `j` of work tape `0` is cells `zs j, …, zs (j + 1) - 1`, where `zs j = 2 ^ (j + 1) - 1`;
cell `n ≥ 1` is cell `off n` of zone `lvl n`. `encA Z J tg` is work tape `0` holding the tracks
`Z` with `J` zones created, the first cell of zone `tg` marked if `tg` is a level. `encB src dst`
is work tape `1` holding the lists `src` and `dst` after its home cell.

## Main definitions

* `Turing.MultiTapeTM.HennieStearns.zs`, `lvl`, `off`.
* `Turing.MultiTapeTM.HennieStearns.aCell`, `encA`, `encB`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

/-- The first cell of zone `j`. -/
def zs (j : ℕ) : ℕ := 2 ^ (j + 1) - 1

/-- The zone of cell `n ≥ 1`. -/
def lvl (n : ℕ) : ℕ := Nat.log 2 (n + 1) - 1

/-- The offset of cell `n ≥ 1` in its zone. -/
def off (n : ℕ) : ℕ := n - zs (lvl n)

lemma zs_succ (j : ℕ) : zs (j + 1) = zs j + 2 ^ (j + 1) := by
  simp only [zs, pow_succ]
  have := Nat.one_le_two_pow (n := j)
  omega

lemma zs_zero : zs 0 = 1 := rfl

lemma one_le_zs (j : ℕ) : 1 ≤ zs j := by
  simp only [zs, pow_succ]
  have := Nat.one_le_two_pow (n := j)
  omega

lemma zs_mono {i j : ℕ} (h : i ≤ j) : zs i ≤ zs j := by
  simp only [zs]
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.succ_le_succ h)
  omega

lemma zs_strictMono {i j : ℕ} (h : i < j) : zs i < zs j := by
  have := zs_mono (show i + 1 ≤ j by omega)
  rw [zs_succ] at this
  have := Nat.one_le_two_pow (n := i + 1)
  omega

/-- A cell in zone `j` has level `j`. -/
lemma lvl_eq {n j : ℕ} (h₁ : zs j ≤ n) (h₂ : n < zs (j + 1)) : lvl n = j := by
  simp only [lvl]
  have : Nat.log 2 (n + 1) = j + 1 := by
    rw [Nat.log_eq_iff (by simp)]
    simp only [zs] at h₁ h₂
    have := Nat.one_le_two_pow (n := j + 1)
    have := Nat.one_le_two_pow (n := j + 2)
    constructor <;> omega
  omega

/-- Every cell `n ≥ 1` lies in zone `lvl n`. -/
lemma zs_lvl_le {n : ℕ} (hn : 1 ≤ n) : zs (lvl n) ≤ n ∧ n < zs (lvl n + 1) := by
  have h₁ := Nat.pow_log_le_self 2 (show n + 1 ≠ 0 by omega)
  have h₂ := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + 1)
  have hl : 1 ≤ Nat.log 2 (n + 1) := Nat.le_log_of_pow_le (by norm_num) (by simp; omega)
  simp only [zs, lvl, show Nat.log 2 (n + 1) - 1 + 1 = Nat.log 2 (n + 1) by omega]
  omega

lemma off_lt {n : ℕ} (hn : 1 ≤ n) : off n < 2 ^ (lvl n + 1) := by
  have := zs_lvl_le hn
  rw [zs_succ] at this
  simp only [off]
  omega

lemma off_eq {n j : ℕ} (h₁ : zs j ≤ n) (h₂ : n < zs (j + 1)) : off n = n - zs j := by
  simp [off, lvl_eq h₁ h₂]

variable {k : ℕ} {Symbol : Type}

/-- The center cell of tracks `Z`. -/
def centerCell (Z : Fin k → ZTrack Symbol) : ACell k Symbol :=
  ⟨true, false, false, false, fun i => some (Z i).center, fun _ => none⟩

/-- Cell `n ≥ 1` of work tape `0`, a cell of zone `lvl n`, with the first cell of zone `tg`
marked. -/
def zoneCell (Z : Fin k → ZTrack Symbol) (tg : Option ℕ) (n : ℕ) : ACell k Symbol :=
  ⟨false, decide (off n = 0), decide (off n < 2 ^ lvl n), decide (tg = some (lvl n) ∧ off n = 0),
    fun i => ((Z i).zone .R (lvl n))[off n]?, fun i => ((Z i).zone .L (lvl n))[off n]?⟩

/-- Cell `n` of work tape `0`, with `J` zones created. -/
def aCell (Z : Fin k → ZTrack Symbol) (J : ℕ) (tg : Option ℕ) (n : ℕ) : Option (ACell k Symbol) :=
  if n = 0 then some (centerCell Z) else if lvl n < J then some (zoneCell Z tg n) else none

/-- Work tape `0`. -/
def encA (Z : Fin k → ZTrack Symbol) (J : ℕ) (tg : Option ℕ) : ℤ → Option (HSym k Symbol) :=
  fun z => if 0 ≤ z then (aCell Z J tg z.toNat).map fun c => .inr (.inl c) else none

/-- Cell `p ≥ 1` of work tape `1` holding the lists `src` and `dst`. -/
def bCell (src dst : List (Option Symbol)) (p : ℕ) : BCell Symbol :=
  ⟨src[p - 1]?, dst[p - 1]?, false, false, false⟩

/-- Work tape `1`: the home cell, then the lists `src` and `dst`. -/
def encB (src dst : List (Option Symbol)) : ℤ → Option (HSym k Symbol) :=
  fun z => if z = 0 then some (.inr (.inr homeCell))
    else if 0 < z then bWrite (bCell src dst z.toNat) else none

lemma lvl_zs (j : ℕ) : lvl (zs j) = j :=
  lvl_eq le_rfl (zs_strictMono (Nat.lt_succ_self j))

lemma off_zs (j : ℕ) : off (zs j) = 0 := by simp [off, lvl_zs]

lemma lvl_lt_of_lt_zs {n j : ℕ} (hn : 1 ≤ n) (h : n < zs j) : lvl n < j := by
  by_contra h'
  have := zs_mono (show j ≤ lvl n by omega)
  have := (zs_lvl_le hn).1
  omega

lemma lt_zs_of_lvl_lt {n j : ℕ} (hn : 1 ≤ n) (h : lvl n < j) : n < zs j :=
  lt_of_lt_of_le (zs_lvl_le hn).2 (zs_mono h)

/-- The cells of zone `j` are those of level `j`. -/
lemma lvl_eq_iff {n j : ℕ} (hn : 1 ≤ n) : lvl n = j ↔ zs j ≤ n ∧ n < zs (j + 1) := by
  constructor
  · rintro rfl
    exact zs_lvl_le hn
  · rintro ⟨h₁, h₂⟩
    exact lvl_eq h₁ h₂

/-! ### Reading the tapes -/

lemma encA_natCast (Z : Fin k → ZTrack Symbol) (J : ℕ) (tg : Option ℕ) (n : ℕ) :
    encA Z J tg (n : ℤ) = (aCell Z J tg n).map fun c => .inr (.inl c) := by
  simp [encA]

@[simp] lemma zoneCell_center (Z : Fin k → ZTrack Symbol) (tg : Option ℕ) (n : ℕ) :
    (zoneCell Z tg n).center = false := rfl

@[simp] lemma centerCell_center (Z : Fin k → ZTrack Symbol) : (centerCell Z).center = true := rfl

lemma readA_encA_of_nonneg (Z : Fin k → ZTrack Symbol) (J : ℕ) (tg : Option ℕ) {z : ℤ}
    (hz : 0 ≤ z) : readA (encA Z J tg z) = aCell Z J tg z.toNat := by
  simp only [encA, hz, ↓reduceIte]
  cases aCell Z J tg z.toNat <;> rfl

lemma readA_encA_nat (Z : Fin k → ZTrack Symbol) (J : ℕ) (tg : Option ℕ) (n : ℕ) :
    readA (encA Z J tg n) = aCell Z J tg n := by
  rw [readA_encA_of_nonneg _ _ _ (by omega)]
  simp

lemma aCell_zero (Z : Fin k → ZTrack Symbol) (J : ℕ) (tg : Option ℕ) :
    aCell Z J tg 0 = some (centerCell Z) := rfl

lemma aCell_of_lt {Z : Fin k → ZTrack Symbol} {J : ℕ} {tg : Option ℕ} {n : ℕ} (hn : 1 ≤ n)
    (hJ : lvl n < J) : aCell Z J tg n = some (zoneCell Z tg n) := by
  simp [aCell, show n ≠ 0 by omega, hJ]

lemma aCell_of_le {Z : Fin k → ZTrack Symbol} {J : ℕ} {tg : Option ℕ} {n : ℕ} (hn : 1 ≤ n)
    (hJ : J ≤ lvl n) : aCell Z J tg n = none := by
  simp [aCell, show n ≠ 0 by omega, show ¬ lvl n < J by omega]

lemma BCell.eq_empty_of_isEmpty {b : BCell Symbol} (h : b.isEmpty = true) : b = BCell.empty := by
  obtain ⟨s, d, m, o, h'⟩ := b
  simp only [BCell.isEmpty, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

lemma readB_bWrite (b : BCell Symbol) : readB (bWrite (k := k) b) = b := by
  simp only [bWrite]
  split_ifs with h
  · exact (BCell.eq_empty_of_isEmpty h).symm
  · rfl

lemma readB_encB_zero (src dst : List (Option Symbol)) :
    readB (encB (k := k) src dst 0) = homeCell := rfl

lemma readB_encB_pos (src dst : List (Option Symbol)) {z : ℤ} (hz : 0 < z) :
    readB (encB (k := k) src dst z) = bCell src dst z.toNat := by
  simp [encB, show z ≠ 0 by omega, hz, readB_bWrite]

/-! ### Reading zones in order -/

lemma flatMap_getElem?_toList_eq_take {α : Type*} (l : List α) (n : ℕ) :
    (List.range n).flatMap (fun t => l[t]?.toList) = l.take n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih, List.take_add_one]

/-- Reading a list at the offsets below `n ≥ length` gives the list. -/
lemma flatMap_getElem?_toList {α : Type*} (l : List α) {n : ℕ} (h : l.length ≤ n) :
    (List.range n).flatMap (fun t => l[t]?.toList) = l := by
  rw [flatMap_getElem?_toList_eq_take, List.take_of_length_le h]

/-- The cells below the end of zone `j`, in order: cell `0`, then each zone. -/
lemma flatMap_range_zs {α : Type*} (f : ℕ → List α) (j : ℕ) :
    (List.range (zs j)).flatMap f =
      f 0 ++ (List.range j).flatMap fun j' => (List.range (2 ^ (j' + 1))).flatMap fun t =>
        f (zs j' + t) := by
  induction j with
  | zero => simp [zs]
  | succ j ih =>
    rw [zs_succ, List.range_add, List.flatMap_append, ih, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.flatMap_map, List.append_assoc]

lemma lvl_zs_add {j t : ℕ} (ht : t < 2 ^ (j + 1)) : lvl (zs j + t) = j :=
  lvl_eq (by omega) (by rw [zs_succ]; omega)

lemma off_zs_add {j t : ℕ} (ht : t < 2 ^ (j + 1)) : off (zs j + t) = t := by
  simp [off, lvl_zs_add ht]

/-- Reading the cells of the zones up to `j` of one side of a track, with something for the
center first. -/
lemma flatMap_cells {α : Type*} (l : ℕ → List α) (c : List α) (j : ℕ)
    (hl : ∀ j' ≤ j, (l j').length ≤ 2 ^ (j' + 1)) :
    (List.range (zs (j + 1))).flatMap (fun n => if n = 0 then c else (l (lvl n))[off n]?.toList) =
      c ++ (List.range (j + 1)).flatMap l := by
  rw [flatMap_range_zs]
  simp only [↓reduceIte]
  congr 1
  refine List.flatMap_congr fun j' hj' => ?_
  have hj' := List.mem_range.1 hj'
  rw [List.flatMap_congr (g := fun t => (l j')[t]?.toList) fun t ht => by
    have ht := List.mem_range.1 ht
    have h0 : zs j' + t ≠ 0 := by have := one_le_zs j'; omega
    simp only [h0, ↓reduceIte, lvl_zs_add ht, off_zs_add ht]]
  exact flatMap_getElem?_toList _ (hl j' (by omega))

/-! ### Pushing onto work tape `1` -/

lemma bCell_eq_of_lt {src dst : List (Option Symbol)} {p : ℕ} :
    bCell src dst p = ⟨src[p - 1]?, dst[p - 1]?, false, false, false⟩ := rfl

lemma encB_update_d (src D : List (Option Symbol)) (v : Option Symbol) :
    Function.update (encB (k := k) src D) ((D.length : ℤ) + 1)
        (bWrite { bCell src D (D.length + 1) with d := some v }) = encB src (D ++ [v]) := by
  funext z
  by_cases hz : z = (D.length : ℤ) + 1
  · subst hz
    rw [Function.update_self]
    simp only [encB]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    simp [bCell, show ((D.length : ℤ) + 1).toNat = D.length + 1 by omega]
  · rw [Function.update_of_ne hz]
    simp only [encB]
    split_ifs with h₀ h₁
    · rfl
    · congr 1
      simp only [bCell, BCell.mk.injEq, true_and, and_true]
      rw [List.getElem?_append]
      split_ifs with h₂
      · rfl
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    · rfl

lemma encB_update_s (S D : List (Option Symbol)) (v : Option Symbol) :
    Function.update (encB (k := k) S D) ((S.length : ℤ) + 1)
        (bWrite { bCell S D (S.length + 1) with s := some v }) = encB (S ++ [v]) D := by
  funext z
  by_cases hz : z = (S.length : ℤ) + 1
  · subst hz
    rw [Function.update_self]
    simp only [encB]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    simp [bCell, show ((S.length : ℤ) + 1).toNat = S.length + 1 by omega]
  · rw [Function.update_of_ne hz]
    simp only [encB]
    split_ifs with h₀ h₁
    · rfl
    · congr 1
      simp only [bCell, BCell.mk.injEq, and_true]
      rw [List.getElem?_append]
      split_ifs with h₂
      · rfl
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    · rfl

end Turing.MultiTapeTM.HennieStearns
