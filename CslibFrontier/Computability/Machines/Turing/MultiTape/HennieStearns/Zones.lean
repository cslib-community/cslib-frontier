/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Zoned tracks: the data structure of the Hennie–Stearns simulation

The Hennie–Stearns simulation keeps each simulated tape *head-centric*: the symbol under the head
sits in a fixed center cell, and the symbols to its right and to its left sit in *zones* of
doubling size, `zone .R j` and `zone .L j` for `j = 0, 1, …`, each with room for `2 ^ (j + 1)`
symbols. A zone holds `0`, `2 ^ j` or `2 ^ (j + 1)` of them (it is empty, half full or full),
and the two zones of a level hold `2 ^ (j + 1)` together. Levels from `J` on hold blanks only, half
full on both sides. Reading the zones of a side in order gives the tape on that side of the head
(`ZTrack.decode`).

A head move to side `s` takes the next symbol of side `s` into the center. `ZTrack.move` does it at
the least level `j` whose zone on side `s` is not empty (`ZTrack.trig`): the zones of side `s`
below `j` are empty and those of the other side are full. It spreads the symbols of side `s` up to
level `j` and those of the other side up to level `j`, with the old center, so that every level
below `j` is half full on both sides. This rewrites `O(2 ^ j)` symbols. Since a level is left half
full on both sides, the next move that reaches level `j` comes at least `2 ^ j - 1` moves later,
and `n` moves rewrite `O(n log n)` symbols in total (`ZTrack.cost_le`, in the file of the costs).

## Main definitions

* `Turing.MultiTapeTM.HennieStearns.ZTrack`, `ZTrack.Valid`, `ZTrack.decode`.
* `ZTrack.trig`, `ZTrack.move`: the level of a move, and the move.

## Main results

* `ZTrack.center_move`, `ZTrack.decode_move_self`, `ZTrack.decode_move_other_zero`,
  `ZTrack.decode_move_other_succ`: a move shifts the decoded tape by one cell.
* `ZTrack.Valid.move`: moves keep the invariants.

## References

* [F. C. Hennie and R. E. Stearns, *Two-tape simulation of multitape Turing
  machines*][HennieStearns1966]
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

/-- The two sides of the head. -/
inductive Side
  /-- Right of the head. -/
  | R
  /-- Left of the head. -/
  | L
  deriving DecidableEq

/-- The other side. -/
def Side.other : Side → Side
  | .R => .L
  | .L => .R

@[simp] lemma Side.other_other (s : Side) : s.other.other = s := by cases s <;> rfl
@[simp] lemma Side.other_ne (s : Side) : s.other ≠ s := by cases s <;> simp [Side.other]
@[simp] lemma Side.ne_other (s : Side) : s ≠ s.other := (Side.other_ne s).symm

variable {Symbol : Type*}

/-- A head-centric tape: the symbol under the head and the symbols in the zones of each side, in
order away from the head. -/
@[ext] structure ZTrack (Symbol : Type*) where
  /-- The symbol under the head. -/
  center : Option Symbol
  /-- The symbols in zone `j` of side `s`, in order away from the head. -/
  zone : Side → ℕ → List (Option Symbol)

namespace ZTrack

variable (Z : ZTrack Symbol) (J : ℕ)

/-- The invariants of a track whose levels from `J` on are half full of blanks: each zone is
empty, half full or full, and the two zones of a level hold `2 ^ (j + 1)` symbols together. -/
structure Valid (Z : ZTrack Symbol) (J : ℕ) : Prop where
  /-- A zone is empty, half full or full. -/
  length : ∀ s j, (Z.zone s j).length = 0 ∨ (Z.zone s j).length = 2 ^ j ∨
    (Z.zone s j).length = 2 ^ (j + 1)
  /-- The two zones of a level hold `2 ^ (j + 1)` symbols together. -/
  sum : ∀ j, (Z.zone .R j).length + (Z.zone .L j).length = 2 ^ (j + 1)
  /-- From level `J` on, both zones are half full of blanks. -/
  blank : ∀ s j, J ≤ j → Z.zone s j = List.replicate (2 ^ j) none

/-- The symbols of side `s` in levels below `J`, in order away from the head. -/
def flat (s : Side) : List (Option Symbol) := (List.range J).flatMap (Z.zone s)

/-- The symbol `m + 1` cells from the head on side `s`. -/
def decode (s : Side) (m : ℕ) : Option Symbol := (Z.flat J s).getD m none

/-- The level of a move to side `s`: the least level whose zone on side `s` is not empty. -/
def trig (s : Side) : ℕ := ((List.range (J + 1)).find? fun j => !(Z.zone s j).isEmpty).getD J

/-- The `k`-th of the chunks of sizes `1, 2, 4, …` into which a list is cut. -/
def chunk (k : ℕ) (l : List (Option Symbol)) : List (Option Symbol) :=
  (l.drop (2 ^ k - 1)).take (2 ^ k)

/-- The zones up to level `j` filled with `l`: levels below `j` half full with consecutive chunks,
level `j` with the rest. -/
def fill (j : ℕ) (l : List (Option Symbol)) (k : ℕ) : List (Option Symbol) :=
  if k < j then chunk k l else l.drop (2 ^ j - 1)

/-- The move of the head to side `s`. -/
def move (s : Side) : ZTrack Symbol :=
  let j := Z.trig J s
  let src := Z.zone s j
  let dst := Z.center :: (List.range (j + 1)).flatMap (Z.zone s.other)
  { center := src.headD none
    zone := fun s' k =>
      if j < k then Z.zone s' k
      else if s' = s then fill j src.tail k else fill j dst k }

variable {Z J}

/-- The level of a move is at most `J`, its zone on the side of the move is not empty, and the
zones of that side below it are empty. -/
lemma trig_spec (hV : Z.Valid J) (s : Side) :
    Z.trig J s ≤ J ∧ Z.zone s (Z.trig J s) ≠ [] ∧ ∀ k < Z.trig J s, Z.zone s k = [] := by
  have hJ : Z.zone s J ≠ [] := by
    rw [hV.blank s J le_rfl]
    simp [List.replicate_eq_nil_iff]
  rcases h : (List.range (J + 1)).find? (fun j => !(Z.zone s j).isEmpty) with _ | i
  · exfalso
    have := List.find?_eq_none.1 h J (by simp)
    simp only [List.isEmpty_eq_false_iff, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    exact hJ (not_not.1 this)
  · obtain ⟨hi, hmem, hlt⟩ := List.find?_range_eq_some.1 h
    have htrig : Z.trig J s = i := by simp [trig, h]
    rw [htrig]
    refine ⟨by simpa [Nat.lt_succ_iff] using hmem, by simpa [List.isEmpty_iff] using hi,
      fun k hk => by simpa [List.isEmpty_iff] using hlt k hk⟩

lemma trig_le (hV : Z.Valid J) (s : Side) : Z.trig J s ≤ J := (trig_spec hV s).1

lemma zone_trig_ne_nil (hV : Z.Valid J) (s : Side) : Z.zone s (Z.trig J s) ≠ [] :=
  (trig_spec hV s).2.1

lemma zone_of_lt_trig (hV : Z.Valid J) {s : Side} {k : ℕ} (hk : k < Z.trig J s) :
    Z.zone s k = [] := (trig_spec hV s).2.2 k hk

/-- Below the level of a move, the zones of the other side are full. -/
lemma length_zone_other_of_lt_trig (hV : Z.Valid J) {s : Side} {k : ℕ} (hk : k < Z.trig J s) :
    (Z.zone s.other k).length = 2 ^ (k + 1) := by
  have h₁ := hV.sum k
  have h₂ := zone_of_lt_trig hV hk
  cases s <;> simp_all [Side.other]

/-- At the level of a move, its zone holds at least half. -/
lemma length_zone_trig (hV : Z.Valid J) (s : Side) :
    2 ^ Z.trig J s ≤ (Z.zone s (Z.trig J s)).length := by
  rcases hV.length s (Z.trig J s) with h | h | h
  · exact absurd (List.length_eq_zero_iff.1 h) (zone_trig_ne_nil hV s)
  · exact h.ge
  · rw [h, pow_succ]
    omega

/-- At the level of a move, the zone of the other side holds at most half. -/
lemma length_zone_other_trig (hV : Z.Valid J) (s : Side) :
    (Z.zone s.other (Z.trig J s)).length = 0 ∨
      (Z.zone s.other (Z.trig J s)).length = 2 ^ Z.trig J s := by
  have h₁ := hV.sum (Z.trig J s)
  have h₂ := length_zone_trig hV s
  have h₃ := hV.length s.other (Z.trig J s)
  generalize Z.trig J s = j at h₁ h₂ h₃ ⊢
  have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  rw [hp] at h₁ h₃
  cases s <;> simp only [Side.other] at h₃ ⊢ <;> omega

/-! ### Chunks -/

lemma length_chunk {k : ℕ} {l : List (Option Symbol)} (h : 2 ^ (k + 1) - 1 ≤ l.length) :
    (chunk k l).length = 2 ^ k := by
  simp only [chunk, List.length_take, List.length_drop]
  rw [pow_succ] at h
  omega

/-- The chunks below level `j`, followed by the rest, give back the list. -/
lemma flatMap_chunk_append (j : ℕ) (l : List (Option Symbol)) (h : 2 ^ j - 1 ≤ l.length) :
    (List.range j).flatMap (chunk · l) ++ l.drop (2 ^ j - 1) = l := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    have h' : 2 ^ j - 1 ≤ l.length := le_trans (by
      have := Nat.one_le_two_pow (n := j)
      rw [pow_succ]
      omega) h
    conv_rhs => rw [← ih h']
    congr 1
    simp only [chunk]
    have := Nat.one_le_two_pow (n := j)
    rw [show 2 ^ (j + 1) - 1 = (2 ^ j - 1) + 2 ^ j by rw [pow_succ]; omega, ← List.drop_drop,
      List.take_append_drop]

/-- The zones up to level `j` filled with `l` give back `l`. -/
lemma flatMap_fill (j : ℕ) (l : List (Option Symbol)) (h : 2 ^ j - 1 ≤ l.length) :
    (List.range (j + 1)).flatMap (fill j l) = l := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  have : (List.range j).flatMap (fill j l) = (List.range j).flatMap (chunk · l) :=
    List.flatMap_congr fun k hk => by simp [fill, List.mem_range.1 hk]
  rw [this, show fill j l j = l.drop (2 ^ j - 1) by simp [fill]]
  exact flatMap_chunk_append j l h

/-! ### Decoding -/

lemma flat_add (Z : ZTrack Symbol) (s : Side) (a b : ℕ) :
    Z.flat (a + b) s = Z.flat a s ++ (List.range b).flatMap fun i => Z.zone s (a + i) := by
  simp [flat, List.range_add, List.flatMap_append, List.flatMap_map]

/-- Decoding does not depend on how many levels past the blank ones are read. -/
lemma decode_mono (hV : Z.Valid J) {J' : ℕ} (hJ : J ≤ J') (s : Side) (m : ℕ) :
    Z.decode J' s m = Z.decode J s m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hJ
  simp only [decode, flat_add]
  have hb : ∀ x ∈ (List.range d).flatMap fun i => Z.zone s (J + i), x = none := by
    intro x hx
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hx
    rw [hV.blank s (J + i) (by omega)] at hi
    exact List.eq_of_mem_replicate hi
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h
  · rfl
  · rw [List.getElem?_eq_none (l := Z.flat J s) (by omega)]
    rcases hx : ((List.range d).flatMap fun i => Z.zone s (J + i))[m - (Z.flat J s).length]? with
      _ | x
    · rfl
    · simp [hb x (List.mem_of_getElem? hx)]

/-- A track valid with `J` levels is valid with more. -/
lemma Valid.mono (hV : Z.Valid J) {J' : ℕ} (hJ : J ≤ J') : Z.Valid J' :=
  ⟨hV.length, hV.sum, fun s j hj => hV.blank s j (hJ.trans hj)⟩

lemma trig_mono (hV : Z.Valid J) {J' : ℕ} (hJ : J ≤ J') (s : Side) :
    Z.trig J' s = Z.trig J s := by
  obtain ⟨h₁, h₂, h₃⟩ := trig_spec hV s
  obtain ⟨h₁', h₂', h₃'⟩ := trig_spec (hV.mono hJ) s
  rcases lt_trichotomy (Z.trig J' s) (Z.trig J s) with h | h | h
  · exact absurd (h₃ _ h) h₂'
  · exact h
  · exact absurd (h₃' _ h) h₂

/-- The symbols of side `s` up to the level of a move to `s` are those of its zone. -/
lemma flatMap_zone_trig (hV : Z.Valid J) (s : Side) :
    (List.range (Z.trig J s + 1)).flatMap (Z.zone s) = Z.zone s (Z.trig J s) := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  have : (List.range (Z.trig J s)).flatMap (Z.zone s) = [] :=
    List.flatMap_eq_nil_iff.2 fun k hk => zone_of_lt_trig hV (List.mem_range.1 hk)
  rw [this, List.nil_append]

/-- Below the level of a move, the other side holds `2 ^ (j + 1) - 2` symbols. -/
lemma length_flatMap_other (hV : Z.Valid J) (s : Side) :
    ∀ n ≤ Z.trig J s, ((List.range n).flatMap (Z.zone s.other)).length = 2 ^ (n + 1) - 2
  | 0, _ => by simp
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append,
      length_flatMap_other hV s n (by omega), length_zone_other_of_lt_trig hV (by omega)]
    have := Nat.one_le_two_pow (n := n)
    rw [pow_succ, pow_succ, pow_succ]
    omega

/-! ### Moves -/

lemma length_dst (hV : Z.Valid J) (s : Side) :
    (Z.center :: (List.range (Z.trig J s + 1)).flatMap (Z.zone s.other)).length =
      2 ^ Z.trig J s + 2 ^ Z.trig J s - 1 + (Z.zone s.other (Z.trig J s)).length := by
  rw [List.length_cons, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.length_append, length_flatMap_other hV s _ le_rfl, pow_succ]
  have := Nat.one_le_two_pow (n := Z.trig J s)
  omega

/-- The flat list of `J + 1` levels, split after the level of a move. -/
lemma flat_succ_split (Z' : ZTrack Symbol) (hV : Z.Valid J) (s s' : Side) :
    Z'.flat (J + 1) s' = Z'.flat (Z.trig J s + 1) s' ++
      (List.range (J - Z.trig J s)).flatMap fun i => Z'.zone s' (Z.trig J s + 1 + i) := by
  have h := flat_add Z' s' (Z.trig J s + 1) (J - Z.trig J s)
  rwa [show Z.trig J s + 1 + (J - Z.trig J s) = J + 1 by have := trig_le hV s; omega] at h

lemma zone_move_of_lt {s s' : Side} {k : ℕ} (hk : Z.trig J s < k) :
    (Z.move J s).zone s' k = Z.zone s' k := by
  simp [move, hk]

lemma zone_move_self_of_le {s : Side} {k : ℕ} (hk : k ≤ Z.trig J s) :
    (Z.move J s).zone s k = fill (Z.trig J s) (Z.zone s (Z.trig J s)).tail k := by
  simp [move, show ¬ Z.trig J s < k by omega]

lemma zone_move_other_of_le {s : Side} {k : ℕ} (hk : k ≤ Z.trig J s) :
    (Z.move J s).zone s.other k =
      fill (Z.trig J s) (Z.center :: (List.range (Z.trig J s + 1)).flatMap (Z.zone s.other)) k := by
  simp [move, show ¬ Z.trig J s < k by omega]

lemma flatMap_move_rest (s s' : Side) (n : ℕ) :
    ((List.range n).flatMap fun i => (Z.move J s).zone s' (Z.trig J s + 1 + i)) =
      (List.range n).flatMap fun i => Z.zone s' (Z.trig J s + 1 + i) :=
  List.flatMap_congr fun _ _ => zone_move_of_lt (by omega)

lemma flat_move_self (hV : Z.Valid J) (s : Side) :
    (Z.move J s).flat (J + 1) s = (Z.flat (J + 1) s).tail := by
  have hlen := length_zone_trig hV s
  rw [flat_succ_split _ hV s s, flat_succ_split _ hV s s, flatMap_move_rest]
  have hnew : (Z.move J s).flat (Z.trig J s + 1) s = (Z.zone s (Z.trig J s)).tail := by
    simp only [flat]
    rw [List.flatMap_congr fun k hk => zone_move_self_of_le
      (Nat.lt_succ_iff.1 (List.mem_range.1 hk))]
    exact flatMap_fill _ _ (by rw [List.length_tail]; omega)
  have hold : Z.flat (Z.trig J s + 1) s = Z.zone s (Z.trig J s) := flatMap_zone_trig hV s
  rw [hnew, hold]
  rcases h : Z.zone s (Z.trig J s) with _ | ⟨a, l⟩
  · exact absurd h (zone_trig_ne_nil hV s)
  · simp

lemma flat_move_other (hV : Z.Valid J) (s : Side) :
    (Z.move J s).flat (J + 1) s.other = Z.center :: Z.flat (J + 1) s.other := by
  rw [flat_succ_split _ hV s s.other, flat_succ_split _ hV s s.other, flatMap_move_rest]
  have hnew : (Z.move J s).flat (Z.trig J s + 1) s.other =
      Z.center :: Z.flat (Z.trig J s + 1) s.other := by
    simp only [flat]
    rw [List.flatMap_congr fun k hk => zone_move_other_of_le
      (Nat.lt_succ_iff.1 (List.mem_range.1 hk))]
    exact flatMap_fill _ _ (by rw [length_dst hV s]; omega)
  rw [hnew, List.cons_append]

lemma center_move (hV : Z.Valid J) (s : Side) : (Z.move J s).center = Z.decode J s 0 := by
  rw [← decode_mono hV (Nat.le_succ J)]
  simp only [decode]
  rw [flat_succ_split _ hV s s, show Z.flat (Z.trig J s + 1) s = Z.zone s (Z.trig J s) from
    flatMap_zone_trig hV s]
  simp only [move]
  rcases h : Z.zone s (Z.trig J s) with _ | ⟨a, l⟩
  · exact absurd h (zone_trig_ne_nil hV s)
  · simp

/-- **A move, on the side it moves to**: the decoded tape shifts by one cell. -/
lemma decode_move_self (hV : Z.Valid J) (s : Side) (m : ℕ) :
    (Z.move J s).decode (J + 1) s m = Z.decode J s (m + 1) := by
  rw [← decode_mono hV (Nat.le_succ J)]
  simp only [decode, flat_move_self hV s, List.getD_eq_getElem?_getD, List.getElem?_tail]

/-- **A move, on the other side**: the old center comes first. -/
lemma decode_move_other_zero (hV : Z.Valid J) (s : Side) :
    (Z.move J s).decode (J + 1) s.other 0 = Z.center := by
  simp [decode, flat_move_other hV s]

lemma decode_move_other_succ (hV : Z.Valid J) (s : Side) (m : ℕ) :
    (Z.move J s).decode (J + 1) s.other (m + 1) = Z.decode J s.other m := by
  rw [← decode_mono hV (Nat.le_succ J)]
  simp [decode, flat_move_other hV s]

lemma _root_.Turing.MultiTapeTM.HennieStearns.Side.eq_or_eq_other (s' s : Side) :
    s' = s ∨ s' = s.other := by
  cases s <;> cases s' <;> simp [Side.other]

/-- Below the level of a move, every zone is half full afterwards. -/
lemma length_zone_move_of_lt (hV : Z.Valid J) {s : Side} (s' : Side) {k : ℕ}
    (hk : k < Z.trig J s) : ((Z.move J s).zone s' k).length = 2 ^ k := by
  have hsrc := length_zone_trig hV s
  have hdst := length_dst hV s
  have hk2 : 2 ^ (k + 1) ≤ 2 ^ Z.trig J s := Nat.pow_le_pow_right (by norm_num) hk
  rcases Side.eq_or_eq_other s' s with rfl | rfl
  · rw [zone_move_self_of_le hk.le]
    simp only [fill, hk, ↓reduceIte]
    exact length_chunk (by rw [List.length_tail]; omega)
  · rw [zone_move_other_of_le hk.le]
    simp only [fill, hk, ↓reduceIte]
    exact length_chunk (by rw [hdst]; omega)

/-- At the level of a move, the zone of its side loses half of the zone's room. -/
lemma length_zone_move_self_trig (hV : Z.Valid J) (s : Side) :
    ((Z.move J s).zone s (Z.trig J s)).length =
      (Z.zone s (Z.trig J s)).length - 2 ^ Z.trig J s := by
  have hsrc := length_zone_trig hV s
  have := Nat.one_le_two_pow (n := Z.trig J s)
  rw [zone_move_self_of_le le_rfl]
  simp only [fill, lt_irrefl, ↓reduceIte, List.length_drop, List.length_tail]
  omega

/-- At the level of a move, the zone of the other side gains half of the zone's room. -/
lemma length_zone_move_other_trig (hV : Z.Valid J) (s : Side) :
    ((Z.move J s).zone s.other (Z.trig J s)).length =
      2 ^ Z.trig J s + (Z.zone s.other (Z.trig J s)).length := by
  have hdst := length_dst hV s
  have := Nat.one_le_two_pow (n := Z.trig J s)
  rw [zone_move_other_of_le le_rfl]
  simp only [fill, lt_irrefl, ↓reduceIte, List.length_drop]
  rw [hdst]
  omega

/-- **Moves keep the invariants**, with one more level. -/
lemma Valid.move (hV : Z.Valid J) (s : Side) : (Z.move J s).Valid (J + 1) := by
  have hj := trig_le hV s
  have hsrc := length_zone_trig hV s
  have hsrc' := hV.length s (Z.trig J s)
  have hoth := length_zone_other_trig hV s
  have h2 : 2 ^ (Z.trig J s + 1) = 2 * 2 ^ Z.trig J s := by ring
  have hlow : ∀ s' k, k < Z.trig J s → ((Z.move J s).zone s' k).length = 2 ^ k :=
    fun s' _ hk => length_zone_move_of_lt hV s' hk
  have hselfj := length_zone_move_self_trig hV s
  have hotherj := length_zone_move_other_trig hV s
  refine ⟨fun s' k => ?_, fun k => ?_, fun s' k hk => ?_⟩
  · rcases lt_trichotomy k (Z.trig J s) with hk | rfl | hk
    · exact Or.inr (Or.inl (hlow s' k hk))
    · rcases Side.eq_or_eq_other s' s with rfl | rfl
      · rw [hselfj]
        rcases hsrc' with h | h | h <;> rw [h] at hsrc ⊢
        · omega
        · simp
        · right; left; rw [h2]; omega
      · rw [hotherj]
        rcases hoth with h | h <;> rw [h]
        · exact Or.inr (Or.inl (by simp))
        · exact Or.inr (Or.inr (by rw [h2]; ring))
    · rw [zone_move_of_lt hk]
      exact hV.length s' k
  · rcases lt_trichotomy k (Z.trig J s) with hk | rfl | hk
    · rw [hlow _ k hk, hlow _ k hk, pow_succ]
      ring
    · have hsum := hV.sum (Z.trig J s)
      cases s
      · simp only [Side.other] at hotherj hoth
        rw [hselfj, hotherj]
        omega
      · simp only [Side.other] at hotherj hoth
        rw [hselfj, hotherj]
        omega
    · rw [zone_move_of_lt hk, zone_move_of_lt hk]
      exact hV.sum k
  · rw [zone_move_of_lt (by omega)]
    exact hV.blank s' k (by omega)

end ZTrack


end Turing.MultiTapeTM.HennieStearns
