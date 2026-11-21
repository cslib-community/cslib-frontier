/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.ToSingleTape.Tracks
import Mathlib.Tactic.Ring

/-!
# The sweeps of the single-tape simulation, cell by cell

The occupied cells of the single tape encode tracks `td` (`cellOf`). A block of consecutive cells,
read in one direction, is `region`. This file computes what each sweep of
`Turing.MultiTapeTM.toSingleTape` does to such a block, as a `sweepOut`:

* walking leaves the block alone (`sweepOut_walk`);
* collecting records the symbol under each head (`sweepOut_collect`);
* the pass of a track rewrites the block into the encoding of the tracks after that track's step
  (`sweepOut_pass`). Its carried flag at a cell says whether the head mark is to be placed there.

## Main definitions

* `Turing.MultiTapeTM.ToSingleTape.cellOf`, `region`.

## Main results

* `Turing.MultiTapeTM.ToSingleTape.sweepOut_walk`, `sweepOut_collect`, `sweepOut_pass`.
-/

@[expose] public section

open Cslib.Turing

namespace Turing.MultiTapeTM.ToSingleTape

variable {k : ℕ} {Symbol State : Type}

/-- Cell `z` of the encoding of the tracks `td` for an input of length `n`. -/
def cellOf (n : ℕ) (td : Track k → TrackTape Symbol) (z : ℤ) : Cell k Symbol :=
  ⟨fun j => (td j).cells z, fun j => decide (z = (td j).head), decide (z = -1), decide (z = n),
    decide (z = 0)⟩

/-- The `W` encoded cells `start, start + σ, start + 2σ, …`. -/
def region (n : ℕ) (td : Track k → TrackTape Symbol) (start σ : ℤ) :
    ℕ → List (Option (Symbol ⊕ Cell k Symbol))
  | 0 => []
  | W + 1 => some (.inr (cellOf n td start)) :: region n td (start + σ) σ W

@[simp] lemma length_region (n : ℕ) (td : Track k → TrackTape Symbol) (start σ : ℤ) (W : ℕ) :
    (region n td start σ W).length = W := by
  induction W generalizing start with
  | zero => rfl
  | succ W ih => simp [region, ih]

lemma getElem_region (n : ℕ) (td : Track k → TrackTape Symbol) (start σ : ℤ) (W i : ℕ)
    (hi : i < (region n td start σ W).length) :
    (region n td start σ W)[i] = some (.inr (cellOf n td (start + σ * i))) := by
  induction W generalizing start i with
  | zero => simp at hi
  | succ W ih =>
    rcases i with _ | i
    · simp [region]
    · simp only [region, List.getElem_cons_succ]
      rw [ih]
      congr 3
      push_cast
      ring

lemma exists_of_mem_region {n : ℕ} {td : Track k → TrackTape Symbol} {start σ : ℤ} {W : ℕ}
    {a : Option (Symbol ⊕ Cell k Symbol)} (ha : a ∈ region n td start σ W) :
    ∃ z, a = some (.inr (cellOf n td z)) := by
  induction W generalizing start with
  | zero => simp [region] at ha
  | succ W ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, rfl⟩
    · exact ih ha

/-- A sweep that leaves every cell as it is returns the block unchanged. -/
lemma sweepOut_walk {D : Type*} (g : D → Option (Symbol ⊕ Cell k Symbol) → D)
    (d : D) (cs : List (Option (Symbol ⊕ Cell k Symbol))) :
    (Cslib.Turing.SingleTapeTM.sweepOut (fun d a => (g d a, a)) d cs).2 = cs := by
  induction cs generalizing d with
  | nil => rfl
  | cons a as ih => simp [Cslib.Turing.SingleTapeTM.sweepOut, ih]

/-- The collecting sweep, as a function of a cell. -/
def collectF (reads : Track k → Option (Option Symbol)) :
    Option (Symbol ⊕ Cell k Symbol) → Track k → Option (Option Symbol)
  | some (.inr c) => collectCell reads c
  | _ => reads

/-- Collecting over a block in which the head of `j` occurs exactly once records the symbol under
it. -/
lemma sweepOut_collect (n : ℕ) (td : Track k → TrackTape Symbol) (j : Track k) :
    ∀ (W : ℕ) (start : ℤ) (reads : Track k → Option (Option Symbol)),
      (∃ i < W, start + i = (td j).head) →
      (Cslib.Turing.SingleTapeTM.sweepOut (fun d a => (collectF d a, a)) reads
        (region n td start 1 W)).1 j = some ((td j).cells (td j).head)
  | 0, _, _, ⟨i, hi, _⟩ => absurd hi (by omega)
  | W + 1, start, reads, ⟨i, hi, hpos⟩ => by
    simp only [region, Cslib.Turing.SingleTapeTM.sweepOut]
    rcases i with _ | i
    · -- the head is here: later cells carry no mark of `j`
      simp only [Nat.cast_zero, add_zero] at hpos
      suffices ∀ (W : ℕ) (start : ℤ) reads', (td j).head < start →
          reads' j = some ((td j).cells (td j).head) →
          (Cslib.Turing.SingleTapeTM.sweepOut (fun d a => (collectF d a, a)) reads'
            (region n td start 1 W)).1 j = some ((td j).cells (td j).head) from
        this W _ _ (by omega) (by simp [collectF, collectCell, cellOf, hpos])
      intro W
      induction W with
      | zero => intro _ _ _ h; exact h
      | succ W ih =>
        intro start reads' hlt h
        simp only [region, Cslib.Turing.SingleTapeTM.sweepOut]
        exact ih _ _ (by omega) (by simp [collectF, collectCell, cellOf, h, show
          ¬ start = (td j).head by omega])
    · exact sweepOut_collect n td j W (start + 1) _ ⟨i, by omega, by push_cast at hpos ⊢; omega⟩

/-- The sign of a direction. -/
def dirSign : _root_.Turing.Dir → SignType
  | .left => -1
  | .right => 1

/-- The pass of track `j` performing `act`, as a function of the carried flag and a cell. -/
def passF (j : Track k) (act : Option (Option Symbol) × SignType) (p : Bool) :
    Option (Symbol ⊕ Cell k Symbol) → Bool × Option (Symbol ⊕ Cell k Symbol)
  | some (.inr c) => ((passCell j act.1 act.2 p c).1, some (.inr (passCell j act.1 act.2 p c).2))
  | a => (p, a)

/-- Whether the pass of track `j` performing `act` in direction `dir` moves the head mark: the
head moves in that direction and is not the input head clamped at the end of the input. -/
abbrev Moves (n : ℕ) (td : Track k → TrackTape Symbol) (j : Track k)
    (act : Option (Option Symbol) × SignType) (dir : _root_.Turing.Dir) : Prop :=
  act.2 = dirSign dir ∧
    ¬ (j = .input ∧ (td j).head = match dir with | .right => (n : ℤ) | .left => -1)

lemma dirSign_cast (dir : _root_.Turing.Dir) :
    ((dirSign dir : SignType) : ℤ) = Cslib.Turing.SingleTapeTM.moveShift (some dir) := by
  cases dir <;> rfl

section Pass

variable (n : ℕ) (td : Track k → TrackTape Symbol) (j : Track k)
  (act : Option (Option Symbol) × SignType) (dir : _root_.Turing.Dir)

/-- Where the head of `j` goes in its step: one cell in the direction of travel if it moves. -/
lemma step_head (hact : act.2 = 0 ∨ act.2 = dirSign dir) :
    (TrackTape.step n j act (td j)).head = if Moves n td j act dir then
      (td j).head + Cslib.Turing.SingleTapeTM.moveShift (some dir) else (td j).head := by
  simp only [TrackTape.step, Moves]
  rcases hact with h | h <;> rw [h] <;> cases dir <;> by_cases hj : j = .input <;>
    simp [hj, dirSign, Cslib.Turing.SingleTapeTM.moveShift]

lemma step_cells_of_ne {z : ℤ} (hz : z ≠ (td j).head) :
    (TrackTape.step n j act (td j)).cells z = (td j).cells z := by
  simp only [TrackTape.step]
  cases act.1 <;> simp [Function.update_of_ne hz]

lemma step_cells_head :
    (TrackTape.step n j act (td j)).cells (td j).head =
      act.1.elim ((td j).cells (td j).head) id := by
  simp only [TrackTape.step]
  cases act.1 <;> simp

/-- The pass of `j` on one encoded cell. -/
lemma passCell_cellOf (hact : act.2 = 0 ∨ act.2 = dirSign dir)
    (hin : j = .input → -1 ≤ (td j).head ∧ (td j).head ≤ n) (z : ℤ) :
    passCell j act.1 act.2 (decide (Moves n td j act dir ∧
        (td j).head + Cslib.Turing.SingleTapeTM.moveShift (some dir) = z)) (cellOf n td z) =
      (decide (Moves n td j act dir ∧ (td j).head = z),
        cellOf n (Function.update td j (TrackTape.step n j act (td j))) z) := by
  have hσ : Cslib.Turing.SingleTapeTM.moveShift (some dir) ≠ 0 := by
    cases dir <;> simp [Cslib.Turing.SingleTapeTM.moveShift]
  have hhead := step_head n td j act dir hact
  -- the condition for moving the mark, read off the encoded cell
  have hcond : movesOn j act.2 (cellOf n td (td j).head) = decide (Moves n td j act dir) := by
    simp only [movesOn, cellOf, Moves]
    rcases hact with h | h <;> rw [h] <;> cases dir <;> by_cases hj : j = .input <;>
      simp [dirSign, hj]
  by_cases hp : Moves n td j act dir ∧ (td j).head + Cslib.Turing.SingleTapeTM.moveShift
      (some dir) = z
  · -- the mark lands here
    obtain ⟨hmv, rfl⟩ := hp
    simp only [passCell, and_true, decide_eq_true hmv, ↓reduceIte, Prod.mk.injEq]
    refine ⟨by simp [hσ], Cell.ext (funext fun j' => ?_) (funext fun j' => ?_) rfl rfl rfl⟩
    · by_cases hj : j' = j
      · subst hj
        simp [cellOf, step_cells_of_ne n td j' act (z := (td j').head +
          Cslib.Turing.SingleTapeTM.moveShift (some dir)) (by omega)]
      · simp [cellOf, hj]
    · by_cases hj : j' = j
      · subst hj
        simp [cellOf, hhead, hmv]
      · simp [cellOf, hj]
  · simp only [passCell, hp, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hz : z = (td j).head
    · -- the head is here: write, and move the mark on if the head moves
      subst hz
      have hmark : (cellOf n td (td j).head).mark j = true := by simp [cellOf]
      simp only [hmark, ↓reduceIte, hcond]
      by_cases hmv : Moves n td j act dir
      · simp only [and_true, decide_eq_true hmv, ↓reduceIte, Prod.mk.injEq]
        refine ⟨by simp, ?_⟩
        refine Cell.ext (funext fun j' => ?_) (funext fun j' => ?_) rfl rfl rfl
        · by_cases hj : j' = j
          · subst hj
            simp [cellOf, step_cells_head]
          · simp [cellOf, hj]
        · by_cases hj : j' = j
          · subst hj
            simp [cellOf, hhead, hmv, hσ]
          · simp [cellOf, hj]
      · simp only [and_true, decide_eq_false hmv, Bool.false_eq_true, ↓reduceIte,
          Prod.mk.injEq, true_and]
        refine Cell.ext (funext fun j' => ?_) (funext fun j' => ?_) rfl rfl rfl
        · by_cases hj : j' = j
          · subst hj
            simp [cellOf, step_cells_head]
          · simp [cellOf, hj]
        · by_cases hj : j' = j
          · subst hj
            simp [cellOf, hhead, hmv]
          · simp [cellOf, hj]
    · -- nothing happens here
      have hmark : (cellOf n td z).mark j = false := by simp [cellOf, hz]
      simp only [hmark, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
      refine ⟨by simp [Ne.symm hz], ?_⟩
      refine Cell.ext (funext fun j' => ?_) (funext fun j' => ?_) rfl rfl rfl
      · by_cases hj : j' = j
        · subst hj
          simp [cellOf, step_cells_of_ne n td j' act hz]
        · simp [cellOf, hj]
      · by_cases hj : j' = j
        · subst hj
          simp only [cellOf, Function.update_self, hhead]
          split_ifs with hmv
          · simp only [decide_eq_decide]
            exact ⟨fun h => absurd h hz, fun h => absurd ⟨hmv, h.symm⟩ hp⟩
          · simp [hz]
        · simp [cellOf, hj]

/-- **The pass of a track.** Sweeping the pass of `j`, which performs `act` and moves its head in
the direction of travel or not at all, over a block rewrites it into the encoding of the tracks
after `j`'s step. The flag carried into a cell says whether the head mark lands there. -/
lemma sweepOut_pass (hact : act.2 = 0 ∨ act.2 = dirSign dir)
    (hin : j = .input → -1 ≤ (td j).head ∧ (td j).head ≤ n) :
    ∀ (W : ℕ) (start : ℤ),
      Cslib.Turing.SingleTapeTM.sweepOut (passF j act)
          (decide (Moves n td j act dir ∧ (td j).head + Cslib.Turing.SingleTapeTM.moveShift
            (some dir) = start))
          (region n td start (Cslib.Turing.SingleTapeTM.moveShift (some dir)) W) =
        (decide (Moves n td j act dir ∧ (td j).head + Cslib.Turing.SingleTapeTM.moveShift
            (some dir) = start + Cslib.Turing.SingleTapeTM.moveShift (some dir) * W),
          region n (Function.update td j (TrackTape.step n j act (td j))) start
            (Cslib.Turing.SingleTapeTM.moveShift (some dir)) W)
  | 0, start => by simp [region, Cslib.Turing.SingleTapeTM.sweepOut]
  | W + 1, start => by
    simp only [region, Cslib.Turing.SingleTapeTM.sweepOut, passF,
      passCell_cellOf n td j act dir hact hin start]
    have hshift : decide (Moves n td j act dir ∧ (td j).head = start) =
        decide (Moves n td j act dir ∧ (td j).head + Cslib.Turing.SingleTapeTM.moveShift
          (some dir) = start + Cslib.Turing.SingleTapeTM.moveShift (some dir)) := by
      simp
    rw [hshift, sweepOut_pass hact hin W]
    simp only [Prod.mk.injEq, and_true]
    congr 3
    push_cast
    ring

end Pass

end Turing.MultiTapeTM.ToSingleTape
