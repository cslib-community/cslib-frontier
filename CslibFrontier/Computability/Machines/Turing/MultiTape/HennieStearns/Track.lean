/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Cost
public import Mathlib.Basic.Sign.Defs
import Mathlib.Tactic.Ring

/-!
# Tracks representing tapes

A zoned track `Y` with `J` levels represents a work tape `t` with head at `p` (`ZTrack.Agree`)
when its center is `t p` and its sides read off the tape to the right and to the left of `p`.
Writing at the head and moving the head keep the representation (`Agree.write`, `Agree.move`).

The levels of the moves of a track depend only on the lengths of its zones (`ZTrack.SameLen`),
which writes do not change: so the cost of the moves of a track that is written to between its
moves is the cost of a run of moves alone (`ZTrack.cost`).
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

namespace ZTrack

variable {Symbol : Type*}

/-! ### Writing -/

/-- The track with the symbol under the head replaced. -/
def withCenter (Y : ZTrack Symbol) (v : Option Symbol) : ZTrack Symbol := { Y with center := v }

@[simp] lemma withCenter_zone (Y : ZTrack Symbol) (v : Option Symbol) :
    (Y.withCenter v).zone = Y.zone := rfl

@[simp] lemma withCenter_center (Y : ZTrack Symbol) (v : Option Symbol) :
    (Y.withCenter v).center = v := rfl

lemma Valid.withCenter {Y : ZTrack Symbol} {J : ℕ} (hV : Y.Valid J) (v : Option Symbol) :
    (Y.withCenter v).Valid J := ⟨hV.length, hV.sum, hV.blank⟩

/-! ### Tracks with zones of the same lengths -/

/-- Two tracks whose zones have the same lengths. -/
def SameLen (Y Y' : ZTrack Symbol) : Prop := ∀ s j, (Y.zone s j).length = (Y'.zone s j).length

/-- The level of a move depends only on the lengths of the zones. -/
lemma trig_eq_of_sameLen {Y Y' : ZTrack Symbol} {J J' : ℕ} (hV : Y.Valid J) (hV' : Y'.Valid J')
    (h : SameLen Y Y') (s : Side) : Y.trig J s = Y'.trig J' s := by
  obtain ⟨-, ha, ha'⟩ := trig_spec hV s
  obtain ⟨-, hb, hb'⟩ := trig_spec hV' s
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hb' _ hlt
    rw [← List.length_eq_zero_iff, ← h, List.length_eq_zero_iff] at this
    exact ha this
  · have := ha' _ hlt
    rw [← List.length_eq_zero_iff, h, List.length_eq_zero_iff] at this
    exact hb this

lemma length_fill_congr {l l' : List (Option Symbol)} (h : l.length = l'.length) (j m : ℕ) :
    (fill j l m).length = (fill j l' m).length := by
  simp only [fill, chunk]
  split_ifs <;> simp [h]

lemma length_flatMap_congr {Y Y' : ZTrack Symbol} (h : SameLen Y Y') (s : Side) (n : ℕ) :
    ((List.range n).flatMap (Y.zone s)).length = ((List.range n).flatMap (Y'.zone s)).length := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.flatMap_append, ih, h s n]

/-- Moves keep the lengths of the zones equal. -/
lemma sameLen_move {Y Y' : ZTrack Symbol} {J J' : ℕ} (hV : Y.Valid J) (hV' : Y'.Valid J')
    (h : SameLen Y Y') (s : Side) : SameLen (Y.move J s) (Y'.move J' s) := by
  have ht := trig_eq_of_sameLen hV hV' h s
  intro s' m
  simp only [move, ht]
  split_ifs
  · exact h s' m
  · exact length_fill_congr (by simp [h s]) _ _
  · exact length_fill_congr (by simp [length_flatMap_congr h]) _ _

/-! ### Runs of moves -/

lemma run_append (Z : ZTrack Symbol) (J : ℕ) (ss : List Side) (s : Side) :
    Z.run J (ss ++ [s]) = (Z.run J ss).move (J + ss.length) s := by
  induction ss generalizing Z J with
  | nil => rfl
  | cons s' ss ih =>
    simp only [List.cons_append, run, ih, List.length_cons]
    congr 1
    omega

lemma cost_append (Z : ZTrack Symbol) (J : ℕ) (ss : List Side) (s : Side) :
    Z.cost J (ss ++ [s]) = Z.cost J ss + 2 ^ (Z.run J ss).trig (J + ss.length) s := by
  induction ss generalizing Z J with
  | nil => simp [cost, run]
  | cons s' ss ih =>
    simp only [List.cons_append, cost, ih, run, List.length_cons]
    rw [show J + 1 + ss.length = J + (ss.length + 1) by omega]
    omega

lemma Valid.run {Z : ZTrack Symbol} {J : ℕ} (hV : Z.Valid J) (ss : List Side) :
    (Z.run J ss).Valid (J + ss.length) := by
  induction ss generalizing Z J with
  | nil => exact hV
  | cons s ss ih =>
    simp only [ZTrack.run, List.length_cons]
    rw [show J + (ss.length + 1) = J + 1 + ss.length by omega]
    exact ih (hV.move s)

/-- A move below the created levels creates none. -/
lemma Valid.move_of_lt {Z : ZTrack Symbol} {J : ℕ} (hV : Z.Valid J) {s : Side}
    (h : Z.trig J s < J) : (Z.move J s).Valid J :=
  ⟨(hV.move s).length, (hV.move s).sum, fun s' j hj => by
    rw [zone_move_of_lt (by omega)]
    exact hV.blank s' j hj⟩

/-! ### Representing a tape -/

/-- The track `Y` with `J` levels represents the tape `t` with head at `p`. -/
def Agree (Y : ZTrack Symbol) (J : ℕ) (t : ℤ → Option Symbol) (p : ℤ) : Prop :=
  Y.center = t p ∧ ∀ m : ℕ, Y.decode J .R m = t (p + 1 + m) ∧ Y.decode J .L m = t (p - 1 - m)

lemma Agree.mono {Y : ZTrack Symbol} {J J' : ℕ} {t : ℤ → Option Symbol} {p : ℤ}
    (h : Y.Agree J t p) (hV : Y.Valid J) (hJ : J ≤ J') : Y.Agree J' t p :=
  ⟨h.1, fun m => by rw [decode_mono hV hJ, decode_mono hV hJ]; exact h.2 m⟩

/-- Writing at the head. -/
lemma Agree.write {Y : ZTrack Symbol} {J : ℕ} {t : ℤ → Option Symbol} {p : ℤ}
    (h : Y.Agree J t p) (v : Option Symbol) :
    (Y.withCenter v).Agree J (Function.update t p v) p := by
  refine ⟨by simp, fun m => ?_⟩
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  exact h.2 m

/-- The side of a head move: right for `1`, left otherwise. -/
def sideOf (m : SignType) : Side := if m = 1 then .R else .L

/-- Moving the head. -/
lemma Agree.move {Y : ZTrack Symbol} {J : ℕ} {t : ℤ → Option Symbol} {p : ℤ}
    (h : Y.Agree J t p) (hV : Y.Valid J) {m : SignType} (hm : m ≠ 0) :
    (Y.move J (sideOf m)).Agree (J + 1) t (p + m) := by
  have hm' : m = -1 ∨ m = 1 := by
    rcases m with _ | _ | _
    · exact absurd rfl hm
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hm' with rfl | rfl
  · -- a move to the left
    have hs : sideOf (-1 : SignType) = .L := rfl
    rw [hs]
    have h0 := decode_move_other_zero hV .L
    have h1 := decode_move_other_succ hV .L
    simp only [Side.other] at h0 h1
    refine ⟨?_, fun n => ⟨?_, ?_⟩⟩
    · rw [center_move hV, (h.2 0).2]
      congr 1
      simp only [Nat.cast_zero, sub_zero, SignType.coe_neg_one]
      ring
    · rcases n with _ | n
      · rw [h0, h.1]; congr 1; simp
      · rw [h1, (h.2 n).1]; congr 1; push_cast; simp; ring
    · rw [decode_move_self hV, (h.2 (n + 1)).2]
      congr 1; push_cast; simp; ring
  · -- a move to the right
    have hs : sideOf (1 : SignType) = .R := rfl
    rw [hs]
    have h0 := decode_move_other_zero hV .R
    have h1 := decode_move_other_succ hV .R
    simp only [Side.other] at h0 h1
    refine ⟨?_, fun n => ⟨?_, ?_⟩⟩
    · rw [center_move hV, (h.2 0).1]
      congr 1
      simp
    · rw [decode_move_self hV, (h.2 (n + 1)).1]
      congr 1; push_cast; simp; ring
    · rcases n with _ | n
      · rw [h0, h.1]; congr 1; simp
      · rw [h1, (h.2 n).2]; congr 1; push_cast; simp; ring

end ZTrack

end Turing.MultiTapeTM.HennieStearns
