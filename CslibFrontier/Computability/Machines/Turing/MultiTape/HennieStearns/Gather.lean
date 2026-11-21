/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Scan
import Mathlib.Tactic.Ring

/-!
# Gathering

The gathering passes of a move at level `j` of the Hennie–Stearns machine: the other side of the
moving track up to zone `j`, with the center (`runFrom_gatherD`), and then its own side
(`runFrom_gatherS`), each onto a list on work tape `1`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

variable {k : ℕ} {Symbol State : Type} {input : List (HSym k Symbol)}
  (tm : MultiTapeTM k Symbol State) (q : State) (mv : Fin k → SignType) (i : Fin k)
  (p : Fin (input.length + 2)) (out : List (HSym k Symbol))

/-- What the gathering of side `s` (with the center if `withCenter`) collects from cell `n`. -/
def gathered (Z : Fin k → ZTrack Symbol) (s : Side) (withCenter : Bool) (n : ℕ) :
    List (Option Symbol) :=
  if n = 0 then (if withCenter then [(Z i).center] else []) else
    ((Z i).zone s (lvl n))[off n]?.toList

lemma length_gathered_le (Z : Fin k → ZTrack Symbol) (s : Side) (w : Bool) (n : ℕ) :
    (gathered i Z s w n).length ≤ 1 := by
  unfold gathered
  split_ifs <;> simp [Option.toList]; split <;> simp

/-- Both gatherings collect the zones up to `j`. -/
lemma flatMap_gathered (Z : Fin k → ZTrack Symbol) {J : ℕ} (hV : (Z i).Valid J) (s : Side)
    (w : Bool) (j : ℕ) :
    (List.range (zs (j + 1))).flatMap (gathered i Z s w) =
      (if w then [(Z i).center] else []) ++ (List.range (j + 1)).flatMap ((Z i).zone s) := by
  have := flatMap_cells (l := (Z i).zone s) (c := if w then [(Z i).center] else []) j
    fun j' _ => by rcases hV.length s j' with h | h | h <;> rw [h] <;> simp [pow_succ]
  rw [← this]
  rfl

variable {tm q mv i p out}

/-- A step of a gathering pass on a zone cell before the end of the pass. -/
lemma gather_no_stop (Z : Fin k → ZTrack Symbol) {j : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (hnE : n < zs (j + 1)) :
    (decide (zs j < n) && (zoneCell Z (some j) n).start) = false := by
  simp only [zoneCell, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
  by_contra h
  simp only [not_or, not_not, not_le] at h
  obtain ⟨h₁, h₂⟩ := h
  have hl := zs_lvl_le hn
  simp only [off] at h₂
  have : j < lvl n := by
    by_contra h'
    have := zs_mono (show lvl n ≤ j by omega)
    omega
  have := zs_mono (show j + 1 ≤ lvl n by omega)
  omega

lemma trig_zoneCell (Z : Fin k → ZTrack Symbol) {j : ℕ} (n : ℕ) (hn : 1 ≤ n) :
    (zoneCell Z (some j) n).trig = decide (n = zs j) := by
  simp only [zoneCell, Option.some.injEq, decide_eq_decide]
  constructor
  · rintro ⟨rfl, h⟩
    have := zs_lvl_le hn
    simp only [off] at h
    omega
  · rintro rfl
    exact ⟨(lvl_zs j).symm, off_zs j⟩

variable (tm q mv i p out) in
/-- **Gathering the other side.** From the center, the machine collects the center and the
symbols of the other side of track `i` up to zone `j` onto work tape `1`, and stops at the end of
zone `j`. -/
lemma runFrom_gatherD (Z : Fin k → ZTrack Symbol) {J j : ℕ} (hV : (Z i).Valid J) (hj : j < J) :
    (hennieStearns tm).runFrom
        (C q mv i p out (.gatherD false) (encA Z J (some j)) (encB [] []) 0 1) (zs (j + 1) + 1) =
      C q mv i p out (.back .gatherS) (encA Z J (some j))
        (encB [] ((Z i).center :: (List.range (j + 1)).flatMap ((Z i).zone (srcSide mv i).other)))
        (zs (j + 1) - 1)
        (((Z i).center :: (List.range (j + 1)).flatMap ((Z i).zone (srcSide mv i).other)).length +
          1) := by
  set o := (srcSide mv i).other
  let Dl : ℕ → List (Option Symbol) := fun t => (List.range t).flatMap (gathered i Z o true)
  have hDl : ∀ t, Dl (t + 1) = Dl t ++ gathered i Z o true t := fun t => by
    simp [Dl, List.range_succ, List.flatMap_append]
  have hfin : Dl (zs (j + 1)) =
      (Z i).center :: (List.range (j + 1)).flatMap ((Z i).zone o) := by
    simp only [Dl, flatMap_gathered i Z hV o true j]
    rfl
  have hrun := runFrom_of_step tm (G := fun t => C q mv i p out
    (.gatherD (decide (zs j < t))) (encA Z J (some j)) (encB [] (Dl t)) t ((Dl t).length + 1))
    (W := zs (j + 1)) fun t ht => by
      rw [step_op, readA_encA_nat, readB_encB_pos _ _ (by omega),
        show (((Dl t).length : ℤ) + 1).toNat = (Dl t).length + 1 by omega]
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · simp only [aCell_zero, opTr, centerCell_center, ↓reduceIte, act_apply, Option.elim_none,
          Option.elim_some]
        have hc : (centerCell Z).r i = some (Z i).center := rfl
        rw [hc]
        have := encB_update_d (k := k) [] (Dl 0) (Z i).center
        simp only [Dl, List.range_zero, List.flatMap_nil, List.length_nil, zero_add] at this ⊢
        rw [this]
        have h1 : decide (zs j < 0 + 1) = false := by
          have := one_le_zs j; simp; omega
        rw [h1]
        simp [gathered]
      · have hl : lvl t < J := by
          have := lvl_lt_of_lt_zs ht0 ht
          omega
        rw [aCell_of_lt ht0 hl]
        simp only [opTr, zoneCell_center, Bool.false_eq_true, ↓reduceIte, gather_no_stop Z t ht0 ht,
          trig_zoneCell Z t ht0, part_zoneCell]
        have hseen : (decide (zs j < t) || decide (t = zs j)) = decide (zs j < t + 1) := by
          by_cases h : zs j < t <;> by_cases h' : t = zs j <;> simp [h, h'] <;> omega
        rw [hseen]
        rcases hv : ((Z i).zone o (lvl t))[off t]? with _ | v
        · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, act_apply,
            Option.elim_none]
          have : Dl (t + 1) = Dl t := by
            rw [hDl]; simp [gathered, show t ≠ 0 by omega, hv]
          rw [this]
          congr 1
        · simp only [Option.isSome_some, ↓reduceIte, act_apply, Option.elim_some]
          have := encB_update_d (k := k) [] (Dl t) v
          erw [this]
          have h2 : Dl (t + 1) = Dl t ++ [v] := by
            rw [hDl]; simp [gathered, show t ≠ 0 by omega, hv]
          rw [h2]
          congr 1; simp
  have hfin' : (List.range (zs (j + 1))).flatMap (gathered i Z o true) =
      (Z i).center :: (List.range (j + 1)).flatMap ((Z i).zone o) := hfin
  simp only [Dl, List.range_zero, List.flatMap_nil, List.length_nil, Nat.cast_zero, zero_add,
    Nat.not_lt_zero, decide_false] at hrun
  rw [runFrom_add, hrun, runFrom_one, step_op, readA_encA_nat]
  have hseen : decide (zs j < zs (j + 1)) = true := by simp [zs_strictMono (Nat.lt_succ_self j)]
  rcases Nat.lt_or_ge (j + 1) J with hJ | hJ
  · rw [aCell_of_lt (one_le_zs _) (by rw [lvl_zs]; exact hJ)]
    simp only [opTr, zoneCell_center, Bool.false_eq_true, ↓reduceIte, hseen,
      show (zoneCell Z (some j) (zs (j + 1))).start = true by simp [zoneCell, off_zs],
      Bool.true_and, act_apply, Option.elim_none]
    rw [hfin']
    congr 1
  · rw [aCell_of_le (one_le_zs _) (by rw [lvl_zs]; exact hJ)]
    simp only [opTr, act_apply, Option.elim_none]
    rw [hfin']
    congr 1

variable (tm q mv i p out) in
/-- **Gathering the side of the move.** From the center, the machine collects the symbols of the
side of the move of track `i` up to zone `j` onto work tape `1`, and stops at the end of zone
`j`. -/
lemma runFrom_gatherS (Z : Fin k → ZTrack Symbol) {J j : ℕ} (hV : (Z i).Valid J) (hj : j < J)
    (D : List (Option Symbol)) :
    (hennieStearns tm).runFrom
        (C q mv i p out (.gatherS false) (encA Z J (some j)) (encB [] D) 0 1) (zs (j + 1) + 1) =
      C q mv i p out (.back .writeS) (encA Z J (some j))
        (encB ((List.range (j + 1)).flatMap ((Z i).zone (srcSide mv i))) D)
        (zs (j + 1) - 1)
        (((List.range (j + 1)).flatMap ((Z i).zone (srcSide mv i))).length + 1) := by
  set o := srcSide mv i
  let Sl : ℕ → List (Option Symbol) := fun t => (List.range t).flatMap (gathered i Z o false)
  have hSl : ∀ t, Sl (t + 1) = Sl t ++ gathered i Z o false t := fun t => by
    simp [Sl, List.range_succ, List.flatMap_append]
  have hrun := runFrom_of_step tm (G := fun t => C q mv i p out
    (.gatherS (decide (zs j < t))) (encA Z J (some j)) (encB (Sl t) D) t ((Sl t).length + 1))
    (W := zs (j + 1)) fun t ht => by
      rw [step_op, readA_encA_nat, readB_encB_pos _ _ (by omega),
        show (((Sl t).length : ℤ) + 1).toNat = (Sl t).length + 1 by omega]
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · simp only [aCell_zero, opTr, centerCell_center, ↓reduceIte, act_apply, Option.elim_none]
        have h1 : decide (zs j < 0 + 1) = false := by
          have := one_le_zs j; simp; omega
        have h2 : Sl (0 + 1) = Sl 0 := by simp [hSl, gathered]
        rw [h1, h2]
        congr 1
      · have hl : lvl t < J := by
          have := lvl_lt_of_lt_zs ht0 ht
          omega
        rw [aCell_of_lt ht0 hl]
        simp only [opTr, zoneCell_center, Bool.false_eq_true, ↓reduceIte, gather_no_stop Z t ht0 ht,
          trig_zoneCell Z t ht0, part_zoneCell]
        have hseen : (decide (zs j < t) || decide (t = zs j)) = decide (zs j < t + 1) := by
          by_cases h : zs j < t <;> by_cases h' : t = zs j <;> simp [h, h'] <;> omega
        rw [hseen]
        rcases hv : ((Z i).zone o (lvl t))[off t]? with _ | v
        · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, act_apply,
            Option.elim_none]
          have : Sl (t + 1) = Sl t := by
            rw [hSl]; simp [gathered, show t ≠ 0 by omega, hv]
          rw [this]
          congr 1
        · simp only [Option.isSome_some, ↓reduceIte, act_apply, Option.elim_some]
          have := encB_update_s (k := k) (Sl t) D v
          erw [this]
          have h2 : Sl (t + 1) = Sl t ++ [v] := by
            rw [hSl]; simp [gathered, show t ≠ 0 by omega, hv]
          rw [h2]
          congr 1; simp
  have hfin' : (List.range (zs (j + 1))).flatMap (gathered i Z o false) =
      (List.range (j + 1)).flatMap ((Z i).zone o) := by
    rw [flatMap_gathered i Z hV o false j]
    rfl
  simp only [Sl, List.range_zero, List.flatMap_nil, List.length_nil, Nat.cast_zero, zero_add,
    Nat.not_lt_zero, decide_false] at hrun
  rw [runFrom_add, hrun, runFrom_one, step_op, readA_encA_nat]
  have hseen : decide (zs j < zs (j + 1)) = true := by simp [zs_strictMono (Nat.lt_succ_self j)]
  rcases Nat.lt_or_ge (j + 1) J with hJ | hJ
  · rw [aCell_of_lt (one_le_zs _) (by rw [lvl_zs]; exact hJ)]
    simp only [opTr, zoneCell_center, Bool.false_eq_true, ↓reduceIte, hseen,
      show (zoneCell Z (some j) (zs (j + 1))).start = true by simp [zoneCell, off_zs],
      Bool.true_and, act_apply, Option.elim_none]
    rw [hfin']
    congr 1
  · rw [aCell_of_le (one_le_zs _) (by rw [lvl_zs]; exact hJ)]
    simp only [opTr, act_apply, Option.elim_none]
    rw [hfin']
    congr 1

end Turing.MultiTapeTM.HennieStearns
