/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.ToSingleTape.Passes
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Simulating multi-tape machines on one tape in quadratic time

The single-tape machine `Turing.MultiTapeTM.toSingleTape tm` simulates the multi-tape machine
`tm`. If `tm` halts on `x` within `t` steps with output `y`, then `toSingleTape tm` outputs `y`
(in plain symbols) on `x` within `c (t + 1) (|x| + t + 1)` steps, for a constant `c` depending
only on the number `k` of work tapes (`outputsWithinTime_toSingleTape`). This is the classical
quadratic simulation of multi-tape machines on one tape; by
`Turing.MultiTapeTM.palindrome_tape_separation` the quadratic overhead cannot be improved in
general.

The proof runs the single-tape machine in absolute coordinates (`AbsCfg`). Between sweeps the
occupied cells `L, …, R` hold the encoding `cellOf` of the tracks of a configuration and every
other cell is blank (`tapeOf`). `Good` collects the invariants that make the sweeps behave: the
occupied cells contain cells `-1` and `|x|` and every head, and the tracks are blank outside
them. Each simulated step sweeps a bounded number of times over the occupied cells and lets
them grow by at most one cell per pass.

## Main results

* `Turing.MultiTapeTM.outputsWithinTime_toSingleTape`: the time bound of the simulation.
* `Turing.MultiTapeTM.outputsWithinTime_toSingleTape_of_computesInTimeAndSpace`: the same for a
  computation within upstream's time and space bounds.
-/

@[expose] public section

open Cslib.Turing Cslib.Turing.SingleTapeTM

namespace Turing.MultiTapeTM.ToSingleTape

variable {k : ℕ} {Symbol State : Type}

/-- The single tape between sweeps: the encoded cells `L, …, R`, blank elsewhere. -/
def tapeOf (n : ℕ) (td : Track k → TrackTape Symbol) (L R : ℤ) :
    ℤ → Option (Symbol ⊕ Cell k Symbol) :=
  fun z => if L ≤ z ∧ z ≤ R then some (.inr (cellOf n td z)) else none

/-- The invariants of the occupied cells `L, …, R` of the encoding of `td` for an input of
length `n`. -/
structure Good (n : ℕ) (td : Track k → TrackTape Symbol) (L R : ℤ) : Prop where
  /-- Cell `-1` is occupied. -/
  left : L ≤ -1
  /-- Cell `n` is occupied. -/
  right : (n : ℤ) ≤ R
  /-- Every head is on an occupied cell. -/
  head : ∀ j, L ≤ (td j).head ∧ (td j).head ≤ R
  /-- The tracks are blank outside the occupied cells. -/
  blank : ∀ j z, (z < L ∨ R < z) → (td j).cells z = none
  /-- The input head is on the input or one of the two cells beside it. -/
  input : -1 ≤ (td .input).head ∧ (td .input).head ≤ n

lemma tapeOf_of_mem {n : ℕ} {td : Track k → TrackTape Symbol} {L R z : ℤ} (h₁ : L ≤ z)
    (h₂ : z ≤ R) : tapeOf n td L R z = some (.inr (cellOf n td z)) := by
  simp [tapeOf, h₁, h₂]

lemma tapeOf_of_lt {n : ℕ} {td : Track k → TrackTape Symbol} {L R z : ℤ} (h : z < L ∨ R < z) :
    tapeOf n td L R z = none := by
  simp only [tapeOf]
  rw [ite_eq_right_iff]
  omega

/-- The occupied cells, read rightwards from `L`. -/
lemma tapeOf_eq_region_right {n : ℕ} {td : Track k → TrackTape Symbol} {L R : ℤ} (hLR : L ≤ R + 1)
    (j : ℕ) (hj : j < (region n td L 1 (R - L + 1).toNat).length) :
    tapeOf n td L R (L + moveShift (some .right) * j) =
      (region n td L 1 (R - L + 1).toNat)[j] := by
  rw [getElem_region]
  simp only [length_region] at hj
  rw [tapeOf_of_mem (by simp only [moveShift]; omega) (by simp only [moveShift]; omega)]
  rfl

/-- The occupied cells, read leftwards from `R`. -/
lemma tapeOf_eq_region_left {n : ℕ} {td : Track k → TrackTape Symbol} {L R : ℤ} (hLR : L ≤ R + 1)
    (j : ℕ) (hj : j < (region n td R (-1) (R - L + 1).toNat).length) :
    tapeOf n td L R (R + moveShift (some .left) * j) =
      (region n td R (-1) (R - L + 1).toNat)[j] := by
  rw [getElem_region]
  simp only [length_region] at hj
  rw [tapeOf_of_mem (by simp only [moveShift]; omega) (by simp only [moveShift]; omega)]
  rfl

variable [Fintype Symbol] [Fintype State]
  (tm : MultiTapeTM k Symbol State)

@[simp] lemma toSingleTape_tr : tm.toSingleTape.tr = simTr tm := rfl

/-- **Sweeping right over the occupied cells**, from `L` to the blank at `R + 1`, rewriting the
encoding of `td` into that of `td'`. -/
lemma run_sweep_right {n : ℕ} {td td' : Track k → TrackTape Symbol} {L R : ℤ} (hLR : L ≤ R + 1)
    {D : Type} (S : D → SimState k Symbol State)
    (f : D → Option (Symbol ⊕ Cell k Symbol) → D × Option (Symbol ⊕ Cell k Symbol))
    (hS : ∀ d, ∀ a ∈ region n td L 1 (R - L + 1).toNat,
      simTr tm (S d) a = (⟨(f d a).2, some .right⟩, some (S (f d a).1)))
    (d : D) (hout : (sweepOut f d (region n td L 1 (R - L + 1).toNat)).2 =
      region n td' L 1 (R - L + 1).toNat) :
    (⟨some (S d), L, tapeOf n td L R⟩ : tm.toSingleTape.AbsCfg).run (R - L + 1).toNat =
      ⟨some (S (sweepOut f d (region n td L 1 (R - L + 1).toNat)).1), R + 1,
        tapeOf n td' L R⟩ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := AbsCfg.run_sweep (tm := tm.toSingleTape) S f .right
    (region n td L 1 (R - L + 1).toNat) hS d ⟨some (S d), L, tapeOf n td L R⟩ rfl
    (tapeOf_eq_region_right hLR)
  simp only [length_region, moveShift] at h₁ h₂ h₃ h₄
  rcases hA : AbsCfg.run _ _ with ⟨st, p, cells⟩
  rw [hA] at h₁ h₂ h₃ h₄
  simp only at h₁ h₂ h₃ h₄
  subst h₁ h₂
  congr 1
  · omega
  · funext z
    by_cases hz : L ≤ z ∧ z ≤ R
    · have := h₃ (z - L).toNat (by omega)
      rw [show L + 1 * ((z - L).toNat : ℤ) = z by omega] at this
      rw [this, List.getElem_of_eq hout, getElem_region, tapeOf_of_mem hz.1 hz.2]
      congr 3
      omega
    · rw [h₄ z fun j hj => by omega, tapeOf_of_lt (by omega), tapeOf_of_lt (by omega)]

/-- **Sweeping left over the occupied cells**, from `R` to the blank at `L - 1`, rewriting the
encoding of `td` into that of `td'`. -/
lemma run_sweep_left {n : ℕ} {td td' : Track k → TrackTape Symbol} {L R : ℤ} (hLR : L ≤ R + 1)
    {D : Type} (S : D → SimState k Symbol State)
    (f : D → Option (Symbol ⊕ Cell k Symbol) → D × Option (Symbol ⊕ Cell k Symbol))
    (hS : ∀ d, ∀ a ∈ region n td R (-1) (R - L + 1).toNat,
      simTr tm (S d) a = (⟨(f d a).2, some .left⟩, some (S (f d a).1)))
    (d : D) (hout : (sweepOut f d (region n td R (-1) (R - L + 1).toNat)).2 =
      region n td' R (-1) (R - L + 1).toNat) :
    (⟨some (S d), R, tapeOf n td L R⟩ : tm.toSingleTape.AbsCfg).run (R - L + 1).toNat =
      ⟨some (S (sweepOut f d (region n td R (-1) (R - L + 1).toNat)).1), L - 1,
        tapeOf n td' L R⟩ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := AbsCfg.run_sweep (tm := tm.toSingleTape) S f .left
    (region n td R (-1) (R - L + 1).toNat) hS d ⟨some (S d), R, tapeOf n td L R⟩ rfl
    (tapeOf_eq_region_left hLR)
  simp only [length_region, moveShift] at h₁ h₂ h₃ h₄
  rcases hA : AbsCfg.run _ _ with ⟨st, p, cells⟩
  rw [hA] at h₁ h₂ h₃ h₄
  simp only at h₁ h₂ h₃ h₄
  subst h₁ h₂
  congr 1
  · omega
  · funext z
    by_cases hz : L ≤ z ∧ z ≤ R
    · have := h₃ (R - z).toNat (by omega)
      rw [show R + -1 * ((R - z).toNat : ℤ) = z by omega] at this
      rw [this, List.getElem_of_eq hout, getElem_region, tapeOf_of_mem hz.1 hz.2]
      congr 3
      omega
    · rw [h₄ z fun j hj => by omega, tapeOf_of_lt (by omega), tapeOf_of_lt (by omega)]

/-- **Walking left.** From the right end, in `toL next`, the machine walks to the blank left of
the occupied cells and steps back onto the left end, entering `fromLeft next`. -/
lemma run_toL {n : ℕ} {td : Track k → TrackTape Symbol} {L R : ℤ} (hLR : L ≤ R + 1)
    (next : Phase k Symbol State) :
    (⟨some (.toL next), R, tapeOf n td L R⟩ : tm.toSingleTape.AbsCfg).run
        ((R - L + 1).toNat + 1) =
      ⟨some (fromLeft next), L, tapeOf n td L R⟩ := by
  rw [AbsCfg.run_add, run_sweep_left tm hLR (D := Unit) (fun _ => .toL next) (fun d a => (d, a))
    (fun d a ha => by obtain ⟨z, rfl⟩ := exists_of_mem_region ha; rfl) () (sweepOut_walk _ _ _)]
  rw [AbsCfg.run_succ, AbsCfg.run_zero]
  simp only [AbsCfg.next, tapeOf_of_lt (show L - 1 < L ∨ R < L - 1 by omega), toSingleTape_tr,
    simTr, simStep, moveShift]
  congr 1
  · ring
  · funext z
    by_cases hz : z = L - 1
    · subst hz
      simp [tapeOf_of_lt (show L - 1 < L ∨ R < L - 1 by omega)]
    · simp [Function.update_of_ne hz]

/-- **Walking right.** From the left end, in `toR next`, the machine walks to the blank right of
the occupied cells and steps back onto the right end, entering `fromRight next`. -/
lemma run_toR {n : ℕ} {td : Track k → TrackTape Symbol} {L R : ℤ} (hLR : L ≤ R + 1)
    (next : Phase k Symbol State) :
    (⟨some (.toR next), L, tapeOf n td L R⟩ : tm.toSingleTape.AbsCfg).run
        ((R - L + 1).toNat + 1) =
      ⟨some (fromRight next), R, tapeOf n td L R⟩ := by
  rw [AbsCfg.run_add, run_sweep_right tm hLR (D := Unit) (fun _ => .toR next) (fun d a => (d, a))
    (fun d a ha => by obtain ⟨z, rfl⟩ := exists_of_mem_region ha; rfl) () (sweepOut_walk _ _ _)]
  rw [AbsCfg.run_succ, AbsCfg.run_zero]
  simp only [AbsCfg.next, tapeOf_of_lt (show R + 1 < L ∨ R < R + 1 by omega), toSingleTape_tr,
    simTr, simStep, moveShift]
  congr 1
  · ring
  · funext z
    by_cases hz : z = R + 1
    · subst hz
      simp [tapeOf_of_lt (show R + 1 < L ∨ R < R + 1 by omega)]
    · simp [Function.update_of_ne hz]

/-- **Collecting.** From the left end, the machine sweeps right recording the symbol under each
head, and at the blank beyond the occupied cells it looks up the action and steps back, ready for
the pass of the input track. -/
lemma run_collect {n : ℕ} {td : Track k → TrackTape Symbol} {L R : ℤ} (G : Good n td L R)
    (q : State) :
    (⟨some (.collect q fun _ => none), L, tapeOf n td L R⟩ : tm.toSingleTape.AbsCfg).run
        ((R - L + 1).toNat + 1) =
      ⟨some (fromRight (.pass (tm.tr q ((td .input).cells (td .input).head)
          fun i => (td (.work i)).cells (td (.work i)).head) .input)), R, tapeOf n td L R⟩ := by
  have hLR : L ≤ R + 1 := by have := G.left; have := G.right; omega
  rw [AbsCfg.run_add, run_sweep_right tm hLR (D := Track k → Option (Option Symbol))
    (fun reads => .collect q reads) (fun d a => (collectF d a, a))
    (fun d a ha => by obtain ⟨z, rfl⟩ := exists_of_mem_region ha; rfl) _ (sweepOut_walk _ _ _)]
  have hreads : ∀ j, (sweepOut (fun d a => (collectF d a, a)) (fun _ => none)
      (region n td L 1 (R - L + 1).toNat)).1 j = some ((td j).cells (td j).head) := fun j =>
    sweepOut_collect n td j _ L _ ⟨((td j).head - L).toNat, by
      have := G.head j; omega, by have := G.head j; omega⟩
  rw [AbsCfg.run_succ, AbsCfg.run_zero]
  simp only [AbsCfg.next, tapeOf_of_lt (show R + 1 < L ∨ R < R + 1 by omega), toSingleTape_tr,
    simTr, simStep, moveShift, hreads, Option.getD_some]
  congr 1
  · ring
  · funext z
    by_cases hz : z = R + 1
    · subst hz
      simp [tapeOf_of_lt (show R + 1 < L ∨ R < R + 1 by omega)]
    · simp [Function.update_of_ne hz]

omit [Fintype Symbol] [Fintype State] in
/-- The input head stays on the input or beside it. -/
lemma step_input_head {n : ℕ} {t : TrackTape Symbol} (h : -1 ≤ t.head ∧ t.head ≤ n)
    (act : Option (Option Symbol) × SignType) :
    -1 ≤ (TrackTape.step n (.input : Track k) act t).head ∧
      (TrackTape.step n (.input : Track k) act t).head ≤ n := by
  simp only [TrackTape.step, true_and]
  split_ifs with hc
  · exact h
  · rcases hm : act.2 with _ | _ | _ <;> rw [hm] at hc
    · simpa using h
    · simp only [SignType.neg_eq_neg_one, SignType.coe_neg_one]
      simp [show (-1 : SignType) ≠ 1 by decide] at hc
      omega
    · simp only [SignType.pos_eq_one, SignType.coe_one]
      simp [show (1 : SignType) ≠ -1 by decide] at hc
      omega

omit [Fintype Symbol] [Fintype State] in
/-- A track's step keeps the invariants, in any occupied cells containing the old ones and the
track's new head. -/
lemma Good.step {n : ℕ} {td : Track k → TrackTape Symbol} {L R L' R' : ℤ} (G : Good n td L R)
    (j : Track k) (act : Option (Option Symbol) × SignType) (hL : L' ≤ L) (hR : R ≤ R')
    (hhead : L' ≤ (TrackTape.step n j act (td j)).head ∧
      (TrackTape.step n j act (td j)).head ≤ R') :
    Good n (Function.update td j (TrackTape.step n j act (td j))) L' R' where
  left := G.left.trans' hL
  right := G.right.trans hR
  head j' := by
    by_cases hj : j' = j
    · subst hj
      simpa using hhead
    · simp only [Function.update_of_ne hj]
      have := G.head j'
      omega
  blank j' z hz := by
    by_cases hj : j' = j
    · subst hj
      simp only [Function.update_self, TrackTape.step]
      have hne : z ≠ (td j').head := by have := G.head j'; omega
      cases act.1 <;> simp [Function.update_of_ne hne, G.blank j' z (by omega)]
    · simp only [Function.update_of_ne hj]
      exact G.blank j' z (by omega)
  input := by
    by_cases hj : (.input : Track k) = j
    · subst hj
      rw [Function.update_self]
      exact step_input_head G.input act
    · rw [Function.update_of_ne hj]
      exact G.input

omit [Fintype Symbol] [Fintype State] in
/-- A cell added right of the occupied ones by a pass is the encoding of the new tracks there. -/
lemma newCell_eq_right {n : ℕ} {td : Track k → TrackTape Symbol} {L R : ℤ} (G : Good n td L R)
    (j : Track k) (act : Option (Option Symbol) × SignType)
    (hh : (TrackTape.step n j act (td j)).head = R + 1) :
    newCell j = cellOf n (Function.update td j (TrackTape.step n j act (td j))) (R + 1) := by
  have := G.right
  refine Cell.ext (funext fun j' => ?_) (funext fun j' => ?_) ?_ ?_ ?_
  · by_cases hj : j' = j
    · subst hj
      have hne : R + 1 ≠ (td j').head := by have := G.head j'; omega
      simp only [newCell, cellOf, Function.update_self, TrackTape.step]
      cases act.1 <;> simp [Function.update_of_ne hne, G.blank j' (R + 1) (by omega)]
    · simp [newCell, cellOf, Function.update_of_ne hj, G.blank j' (R + 1) (by omega)]
  · by_cases hj : j' = j
    · subst hj
      simp [newCell, cellOf, hh]
    · have := G.head j'
      simp [newCell, cellOf, hj]
      omega
  all_goals (simp [newCell, cellOf]; omega)

omit [Fintype Symbol] [Fintype State] in
/-- A cell added left of the occupied ones by a pass is the encoding of the new tracks there. -/
lemma newCell_eq_left {n : ℕ} {td : Track k → TrackTape Symbol} {L R : ℤ} (G : Good n td L R)
    (j : Track k) (act : Option (Option Symbol) × SignType)
    (hh : (TrackTape.step n j act (td j)).head = L - 1) :
    newCell j = cellOf n (Function.update td j (TrackTape.step n j act (td j))) (L - 1) := by
  have := G.left
  refine Cell.ext (funext fun j' => ?_) (funext fun j' => ?_) ?_ ?_ ?_
  · by_cases hj : j' = j
    · subst hj
      have hne : L - 1 ≠ (td j').head := by have := G.head j'; omega
      simp only [newCell, cellOf, Function.update_self, TrackTape.step]
      cases act.1 <;> simp [Function.update_of_ne hne, G.blank j' (L - 1) (by omega)]
    · simp [newCell, cellOf, Function.update_of_ne hj, G.blank j' (L - 1) (by omega)]
  · by_cases hj : j' = j
    · subst hj
      simp [newCell, cellOf, hh]
    · have := G.head j'
      simp [newCell, cellOf, hj]
      omega
  all_goals (simp [newCell, cellOf]; omega)

/-- The tracks after the step of track `j` for the action `a`. -/
abbrev stepTrack (n : ℕ) (td : Track k → TrackTape Symbol) (a : Action k Symbol State)
    (j : Track k) : Track k → TrackTape Symbol :=
  Function.update td j (TrackTape.step n j (j.act a) (td j))

omit [Fintype Symbol] [Fintype State] in
lemma act_snd_of_passesLeft_false {a : Action k Symbol State} {j : Track k}
    (h : passesLeft a j = false) : (j.act a).2 = 0 ∨ (j.act a).2 = dirSign .right := by
  simp only [passesLeft, decide_eq_false_iff_not] at h
  rcases hm : (j.act a).2 with _ | _ | _
  · exact Or.inl rfl
  · exact absurd hm h
  · exact Or.inr rfl

omit [Fintype Symbol] [Fintype State] in
lemma act_snd_of_passesLeft_true {a : Action k Symbol State} {j : Track k}
    (h : passesLeft a j = true) : (j.act a).2 = 0 ∨ (j.act a).2 = dirSign .left := by
  simp only [passesLeft, decide_eq_true_eq] at h
  exact Or.inr h

/-- **The pass of a track, rightwards.** From the left end, the pass of `j` rewrites the occupied
cells into the encoding of `j`'s step, adding a cell on the right if the head mark is carried
there, and stops on the right end, ready for the next phase. -/
lemma run_passR {n : ℕ} {td : Track k → TrackTape Symbol} {L R : ℤ} (G : Good n td L R)
    (a : Action k Symbol State) (j : Track k) (hdir : passesLeft a j = false) :
    ∃ R', R ≤ R' ∧ R' ≤ R + 1 ∧
      (⟨some (.passR a j false), L, tapeOf n td L R⟩ : tm.toSingleTape.AbsCfg).run
          ((R - L + 1).toNat + 1) =
        ⟨some (fromRight (afterPass a j)), R', tapeOf n (stepTrack n td a j) L R'⟩ ∧
      Good n (stepTrack n td a j) L R' := by
  have hLR : L ≤ R + 1 := by have := G.left; have := G.right; omega
  have hact := act_snd_of_passesLeft_false hdir
  have hin : j = .input → -1 ≤ (td j).head ∧ (td j).head ≤ n := by rintro rfl; exact G.input
  have hh := G.head j
  have hd0 : decide (Moves n td j (j.act a) .right ∧
      (td j).head + moveShift (some .right) = L) = false :=
    decide_eq_false fun h => by simp only [moveShift] at h; omega
  have key : sweepOut (passF j (j.act a)) false (region n td L (1) (R - L + 1).toNat) =
      (decide (Moves n td j (j.act a) .right ∧ (td j).head + moveShift (some .right) =
          L + moveShift (some .right) * (R - L + 1).toNat),
        region n (stepTrack n td a j) L (1) (R - L + 1).toNat) := by
    have := sweepOut_pass n td j (j.act a) .right hact hin (R - L + 1).toNat L
    rw [hd0] at this
    exact this
  rw [AbsCfg.run_add, run_sweep_right tm hLR (fun p => .passR a j p) (passF j (j.act a))
    (fun d a' ha => by obtain ⟨z, rfl⟩ := exists_of_mem_region ha; rfl) false (by rw [key])]
  rw [key, AbsCfg.run_succ, AbsCfg.run_zero]
  have hhead := step_head n td j (j.act a) .right hact
  simp only [moveShift] at hhead
  by_cases hmv : Moves n td j (j.act a) .right ∧ (td j).head = R
  · have hpend : decide (Moves n td j (j.act a) .right ∧ (td j).head + moveShift (some .right) =
        L + moveShift (some .right) * (R - L + 1).toNat) = true :=
      decide_eq_true ⟨hmv.1, by simp only [moveShift]; omega⟩
    have hnew : (TrackTape.step n j (j.act a) (td j)).head = R + 1 := by
      rw [hhead, ite_eq_left_iff.2 (fun h => absurd hmv.1 h), hmv.2]
    refine ⟨R + 1, by omega, le_rfl, ?_, G.step j _ le_rfl (by omega) (by omega)⟩
    rw [hpend]
    simp only [AbsCfg.next, tapeOf_of_lt (show R + 1 < L ∨ R < R + 1 by omega), toSingleTape_tr,
      simTr, ↓reduceIte, simStep, moveShift, add_zero]
    congr 1
    funext z
    by_cases hz : z = R + 1
    · subst hz
      rw [Function.update_self, tapeOf_of_mem (by omega) le_rfl, newCell_eq_right G j _ hnew]
    · rw [Function.update_of_ne hz]
      by_cases hz' : L ≤ z ∧ z ≤ R
      · rw [tapeOf_of_mem hz'.1 hz'.2, tapeOf_of_mem hz'.1 (by omega)]
      · rw [tapeOf_of_lt (by omega), tapeOf_of_lt (by omega)]
  · have hpend : decide (Moves n td j (j.act a) .right ∧ (td j).head + moveShift (some .right) =
        L + moveShift (some .right) * (R - L + 1).toNat) = false :=
      decide_eq_false fun h => hmv ⟨h.1, by simp only [moveShift] at h; omega⟩
    refine ⟨R, le_rfl, by omega, ?_, G.step j _ le_rfl le_rfl ?_⟩
    · rw [hpend]
      simp only [AbsCfg.next, tapeOf_of_lt (show R + 1 < L ∨ R < R + 1 by omega),
        toSingleTape_tr, simTr, Bool.false_eq_true, ↓reduceIte, simStep, moveShift]
      congr 1
      · ring
      · funext z
        by_cases hz : z = R + 1
        · subst hz
          rw [Function.update_self, tapeOf_of_lt (by omega)]
        · rw [Function.update_of_ne hz]
    · rw [hhead]
      split_ifs with h
      · have : (td j).head ≠ R := fun h' => hmv ⟨h, h'⟩
        omega
      · omega

/-- **The pass of a track, leftwards.** From the right end, the pass of `j` rewrites the occupied
cells into the encoding of `j`'s step, adding a cell on the left if the head mark is carried
there, and stops on the left end, ready for the next phase. -/
lemma run_passL {n : ℕ} {td : Track k → TrackTape Symbol} {L R : ℤ} (G : Good n td L R)
    (a : Action k Symbol State) (j : Track k) (hdir : passesLeft a j = true) :
    ∃ L', L - 1 ≤ L' ∧ L' ≤ L ∧
      (⟨some (.passL a j false), R, tapeOf n td L R⟩ : tm.toSingleTape.AbsCfg).run
          ((R - L + 1).toNat + 1) =
        ⟨some (fromLeft (afterPass a j)), L', tapeOf n (stepTrack n td a j) L' R⟩ ∧
      Good n (stepTrack n td a j) L' R := by
  have hLR : L ≤ R + 1 := by have := G.left; have := G.right; omega
  have hact := act_snd_of_passesLeft_true hdir
  have hin : j = .input → -1 ≤ (td j).head ∧ (td j).head ≤ n := by rintro rfl; exact G.input
  have hh := G.head j
  have hd0 : decide (Moves n td j (j.act a) .left ∧
      (td j).head + moveShift (some .left) = R) = false :=
    decide_eq_false fun h => by simp only [moveShift] at h; omega
  have key : sweepOut (passF j (j.act a)) false (region n td R (-1) (R - L + 1).toNat) =
      (decide (Moves n td j (j.act a) .left ∧ (td j).head + moveShift (some .left) =
          R + moveShift (some .left) * (R - L + 1).toNat),
        region n (stepTrack n td a j) R (-1) (R - L + 1).toNat) := by
    have := sweepOut_pass n td j (j.act a) .left hact hin (R - L + 1).toNat R
    rw [hd0] at this
    exact this
  rw [AbsCfg.run_add, run_sweep_left tm hLR (fun p => .passL a j p) (passF j (j.act a))
    (fun d a' ha => by obtain ⟨z, rfl⟩ := exists_of_mem_region ha; rfl) false (by rw [key])]
  rw [key, AbsCfg.run_succ, AbsCfg.run_zero]
  have hhead := step_head n td j (j.act a) .left hact
  simp only [moveShift] at hhead
  by_cases hmv : Moves n td j (j.act a) .left ∧ (td j).head = L
  · have hpend : decide (Moves n td j (j.act a) .left ∧ (td j).head + moveShift (some .left) =
        R + moveShift (some .left) * (R - L + 1).toNat) = true :=
      decide_eq_true ⟨hmv.1, by simp only [moveShift]; omega⟩
    have hnew : (TrackTape.step n j (j.act a) (td j)).head = L - 1 := by
      rw [hhead, ite_eq_left_iff.2 (fun h => absurd hmv.1 h), hmv.2]
      ring
    refine ⟨L - 1, le_rfl, by omega, ?_, G.step j _ (by omega) le_rfl (by omega)⟩
    rw [hpend]
    simp only [AbsCfg.next, tapeOf_of_lt (show L - 1 < L ∨ R < L - 1 by omega), toSingleTape_tr,
      simTr, ↓reduceIte, simStep, moveShift, add_zero]
    congr 1
    funext z
    by_cases hz : z = L - 1
    · subst hz
      rw [Function.update_self, tapeOf_of_mem le_rfl (by omega), newCell_eq_left G j _ hnew]
    · rw [Function.update_of_ne hz]
      by_cases hz' : L ≤ z ∧ z ≤ R
      · rw [tapeOf_of_mem hz'.1 hz'.2, tapeOf_of_mem (by omega) hz'.2]
      · rw [tapeOf_of_lt (by omega), tapeOf_of_lt (by omega)]
  · have hpend : decide (Moves n td j (j.act a) .left ∧ (td j).head + moveShift (some .left) =
        R + moveShift (some .left) * (R - L + 1).toNat) = false :=
      decide_eq_false fun h => hmv ⟨h.1, by simp only [moveShift] at h; omega⟩
    refine ⟨L, by omega, le_rfl, ?_, G.step j _ le_rfl le_rfl ?_⟩
    · rw [hpend]
      simp only [AbsCfg.next, tapeOf_of_lt (show L - 1 < L ∨ R < L - 1 by omega),
        toSingleTape_tr, simTr, Bool.false_eq_true, ↓reduceIte, simStep, moveShift]
      congr 1
      · ring
      · funext z
        by_cases hz : z = L - 1
        · subst hz
          rw [Function.update_self, tapeOf_of_lt (by omega)]
        · rw [Function.update_of_ne hz]
    · rw [hhead]
      split_ifs with h
      · have : (td j).head ≠ L := fun h' => hmv ⟨h, h'⟩
        omega
      · omega

/-- The number of passes after the pass of `j` in a step. -/
def Track.rank : Track k → ℕ
  | .input => k + 1
  | .work i => k - i
  | .output => 0

lemma Track.rank_next {j j' : Track k} (h : j.next = some j') : j'.rank + 1 = j.rank := by
  cases j with
  | input =>
    simp only [Track.next] at h
    split_ifs at h with hk
    · cases h
      simp only [Track.rank]
      omega
    · cases h
      simp only [Track.rank]
      omega
  | work i =>
    simp only [Track.next] at h
    split_ifs at h with hk
    · cases h
      simp only [Track.rank]
      omega
    · cases h
      simp only [Track.rank]
      omega
  | output => simp [Track.next] at h

lemma Track.rank_injective : Function.Injective (Track.rank (k := k)) := by
  intro j j' h
  rcases j with _ | i | _ <;> rcases j' with _ | i' | _ <;> simp only [Track.rank] at h
  · rfl
  · omega
  · omega
  · omega
  · exact congrArg _ (Fin.ext (by have := i.isLt; have := i'.isLt; omega))
  · have := i.isLt
    omega
  · omega
  · have := i'.isLt
    omega
  · rfl

lemma Track.rank_le (j : Track k) : j.rank ≤ k + 1 := by
  cases j <;> simp only [Track.rank] <;> omega

lemma Track.rank_output_of_next {j : Track k} (h : j.next = none) : j = .output := by
  cases j with
  | input => simp only [Track.next] at h; split_ifs at h
  | work i => simp only [Track.next] at h; split_ifs at h
  | output => rfl

/-- The state to stand in on a side (`true` for the right end) of the occupied cells to start a
phase. -/
def fromSide (right : Bool) : Phase k Symbol State → SimState k Symbol State :=
  if right then fromRight else fromLeft

/-- The machine standing on a side of the occupied cells, in state `st`. -/
def standing (right : Bool) (st : SimState k Symbol State) (n : ℕ)
    (td : Track k → TrackTape Symbol) (L R : ℤ) : tm.toSingleTape.AbsCfg :=
  ⟨some st, if right then R else L, tapeOf n td L R⟩

/-- **One pass.** Standing on either end, ready for the pass of `j`, the machine walks to the end
the pass starts from if needed, and runs the pass. -/
lemma run_passPhase {n : ℕ} {td : Track k → TrackTape Symbol} {L R : ℤ} (G : Good n td L R)
    (a : Action k Symbol State) (j : Track k) (right : Bool) :
    ∃ m right' L' R', m ≤ 2 * (R - L + 1).toNat + 2 ∧ L - 1 ≤ L' ∧ L' ≤ L ∧ R ≤ R' ∧
      R' ≤ R + 1 ∧ Good n (stepTrack n td a j) L' R' ∧
      (standing tm right (fromSide right (.pass a j)) n td L R).run m =
        standing tm right' (fromSide right' (afterPass a j)) n (stepTrack n td a j) L' R' := by
  have hLR : L ≤ R := by have := G.left; have := G.right; omega
  rcases hdir : passesLeft a j
  · -- rightwards
    obtain ⟨R', h₁, h₂, hrun, G'⟩ := run_passR tm G a j hdir
    cases right
    · refine ⟨(R - L + 1).toNat + 1, true, L, R', by omega, by omega, le_rfl, h₁, h₂, G', ?_⟩
      simp only [standing, fromSide, Bool.false_eq_true, ↓reduceIte]
      rw [show fromLeft (Phase.pass a j) = .passR a j false by simp [fromLeft, hdir]]
      exact hrun
    · refine ⟨((R - L + 1).toNat + 1) + ((R - L + 1).toNat + 1), true, L, R', by omega, by omega,
        le_rfl, h₁, h₂, G', ?_⟩
      simp only [standing, fromSide, fromRight, hdir, ↓reduceIte, Bool.false_eq_true]
      rw [AbsCfg.run_add, run_toL tm (by omega),
        show fromLeft (Phase.pass a j) = .passR a j false by simp [fromLeft, hdir]]
      exact hrun
  · -- leftwards
    obtain ⟨L', h₁, h₂, hrun, G'⟩ := run_passL tm G a j hdir
    cases right
    · refine ⟨((R - L + 1).toNat + 1) + ((R - L + 1).toNat + 1), false, L', R, by omega, h₁, h₂,
        le_rfl, by omega, G', ?_⟩
      simp only [standing, fromSide, fromLeft, hdir, ↓reduceIte, Bool.false_eq_true]
      rw [AbsCfg.run_add, run_toR tm (by omega),
        show fromRight (Phase.pass a j) = .passL a j false by simp [fromRight, hdir]]
      exact hrun
    · refine ⟨(R - L + 1).toNat + 1, false, L', R, by omega, h₁, h₂, le_rfl, by omega, G', ?_⟩
      simp only [standing, fromSide, ↓reduceIte]
      rw [show fromRight (Phase.pass a j) = .passL a j false by simp [fromRight, hdir]]
      exact hrun

/-- The tracks after the passes of `j` and the tracks after it: those tracks have taken their
step. -/
def tracksAfter (n : ℕ) (td : Track k → TrackTape Symbol) (a : Action k Symbol State)
    (j : Track k) : Track k → TrackTape Symbol :=
  fun j' => if j'.rank ≤ j.rank then TrackTape.step n j' (j'.act a) (td j') else td j'

/-- What comes after all the passes of a step: the next step, or the cleanup. -/
def afterStep (a : Action k Symbol State) : Phase k Symbol State :=
  match a.state with
  | some q => .collect q
  | none => .clean

/-- **The passes of a step.** From the pass of `j` on, the machine runs the passes of `j` and of
the tracks after it. -/
lemma run_passes {n : ℕ} (a : Action k Symbol State) :
    ∀ (r : ℕ) (j : Track k), j.rank = r → ∀ (td : Track k → TrackTape Symbol) (L R : ℤ),
      Good n td L R → ∀ right : Bool,
      ∃ m right' L' R', m ≤ (r + 1) * (2 * (R - L + 1).toNat + 4 * r + 4) ∧
        L - (r + 1) ≤ L' ∧ R' ≤ R + (r + 1) ∧ Good n (tracksAfter n td a j) L' R' ∧
        (standing tm right (fromSide right (.pass a j)) n td L R).run m =
          standing tm right' (fromSide right' (afterStep a)) n (tracksAfter n td a j) L' R'
  | r, j, hr, td, L, R, G, right => by
    obtain ⟨m₁, right₁, L₁, R₁, hm₁, hL₁, hL₁', hR₁, hR₁', G₁, hrun₁⟩ :=
      run_passPhase tm G a j right
    rcases hnext : j.next with _ | j'
    · -- the last pass
      have hj := Track.rank_output_of_next hnext
      subst hj
      have hafter : afterPass a (.output : Track k) = afterStep a := by
        simp only [afterPass, hnext]
        rfl
      have htd : tracksAfter n td a .output = stepTrack n td a .output := by
        funext j'
        by_cases hj : j' = .output
        · subst hj
          simp [tracksAfter]
        · have : ¬ j'.rank ≤ (Track.output : Track k).rank := by
            intro h
            apply hj
            apply Track.rank_injective
            simp only [Track.rank] at h ⊢
            omega
          simp [tracksAfter, this, Function.update_of_ne hj]
      refine ⟨m₁, right₁, L₁, R₁, ?_, by omega, by omega, htd ▸ G₁, ?_⟩
      · subst hr
        simp only [Track.rank, zero_add, one_mul, mul_zero, add_zero]
        omega
      · rw [htd, ← hafter]
        exact hrun₁
    · -- passes remain
      have hrank := Track.rank_next hnext
      obtain ⟨m₂, right₂, L₂, R₂, hm₂, hL₂, hR₂, G₂, hrun₂⟩ :=
        run_passes a j'.rank j' rfl (stepTrack n td a j) L₁ R₁ G₁ right₁
      have htd : tracksAfter n (stepTrack n td a j) a j' = tracksAfter n td a j := by
        funext j''
        by_cases hj : j'' = j
        · subst hj
          have : ¬ j''.rank ≤ j'.rank := by omega
          simp [tracksAfter, this]
        · simp only [tracksAfter, stepTrack, Function.update_of_ne hj]
          by_cases h : j''.rank ≤ j'.rank
          · have : j''.rank ≤ j.rank := by omega
            simp [h, this]
          · have : ¬ j''.rank ≤ j.rank := fun h' => by
              have : j''.rank ≠ j.rank := fun he => hj (Track.rank_injective he)
              omega
            simp [h, this]
      refine ⟨m₁ + m₂, right₂, L₂, R₂, ?_, by omega, by omega, htd ▸ G₂, ?_⟩
      · subst hr
        have hW : (R₁ - L₁ + 1).toNat ≤ (R - L + 1).toNat + 2 := by omega
        rw [← hrank]
        have := Nat.mul_le_mul_left (j'.rank + 1)
          (show 2 * (R₁ - L₁ + 1).toNat + 4 * j'.rank + 4 ≤
            2 * (R - L + 1).toNat + 4 * (j'.rank + 1) + 4 by omega)
        nlinarith
      · rw [AbsCfg.run_add, hrun₁, show afterPass a j = .pass a j' by simp [afterPass, hnext],
          hrun₂, htd]

omit [Fintype Symbol] [Fintype State] in
/-- After all the passes, the tracks have taken the step of the configuration. -/
lemma tracksAfter_input {x : List Symbol} {c : Cfg k Symbol State x} {q : State}
    (hq : c.state = some q) :
    tracksAfter x.length (tracks c) (tm.tr q c.inputSymbol c.workTapeSymbols) .input =
      tracks (tm.step c) := by
  funext j
  have hj : j.rank ≤ (Track.input : Track k).rank := j.rank_le
  simp only [tracksAfter, hj, ↓reduceIte, tracks_step tm hq]

/-- **A simulated step.** From the left end, ready to collect in the state of a running
configuration `c`, the machine reaches the encoding of the next configuration: ready to collect
again on its left end if it still runs, and ready to clean up on its right end if it has halted.
-/
lemma run_step {x : List Symbol} {c : Cfg k Symbol State x} {q : State} (hq : c.state = some q)
    {L R : ℤ} (G : Good x.length (tracks c) L R) :
    ∃ m L' R', m ≤ (2 * k + 8) * ((R - L + 1).toNat + 2 * k + 8) ∧ L - (k + 2) ≤ L' ∧
      R' ≤ R + (k + 2) ∧ Good x.length (tracks (tm.step c)) L' R' ∧
      (⟨some (.collect q fun _ => none), L, tapeOf x.length (tracks c) L R⟩ :
          tm.toSingleTape.AbsCfg).run m =
        match (tm.step c).state with
        | some q' =>
          ⟨some (.collect q' fun _ => none), L', tapeOf x.length (tracks (tm.step c)) L' R'⟩
        | none => ⟨some (.clean₁ false), R', tapeOf x.length (tracks (tm.step c)) L' R'⟩ := by
  set a := tm.tr q c.inputSymbol c.workTapeSymbols with ha
  have hcollect := run_collect tm G q
  rw [← inputSymbol_eq_tracks,
    show (fun i => (tracks c (.work i)).cells (tracks c (.work i)).head) = c.workTapeSymbols
      from rfl, ← ha] at hcollect
  obtain ⟨m₂, right₂, L₂, R₂, hm₂, hL₂, hR₂, G₂, hrun₂⟩ :=
    run_passes tm a (k + 1) .input rfl (tracks c) L R G true
  rw [tracksAfter_input tm hq] at G₂ hrun₂
  have hstate : (tm.step c).state = a.state := by
    rw [tm.step_of_state hq, Action.apply_state]
  have hLR : L₂ ≤ R₂ := by have := G₂.left; have := G₂.right; omega
  have hW₂ : (R₂ - L₂ + 1).toNat ≤ (R - L + 1).toNat + 2 * (k + 2) := by omega
  have hbound : ((R - L + 1).toNat + 1) + m₂ + ((R₂ - L₂ + 1).toNat + 1) ≤
      (2 * k + 8) * ((R - L + 1).toNat + 2 * k + 8) := by
    have : m₂ ≤ (k + 2) * (2 * (R - L + 1).toNat + 4 * k + 8) := by
      have := hm₂; ring_nf at this ⊢; omega
    nlinarith
  rw [hstate]
  have hfirst : (⟨some (.collect q fun _ => none), L, tapeOf x.length (tracks c) L R⟩ :
      tm.toSingleTape.AbsCfg).run (((R - L + 1).toNat + 1) + m₂) =
        standing tm right₂ (fromSide right₂ (afterStep a)) x.length (tracks (tm.step c)) L₂ R₂ := by
    rw [AbsCfg.run_add, hcollect]
    exact hrun₂
  rcases hs : a.state with _ | q'
  · have hafter : afterStep a = .clean := by simp [afterStep, hs]
    rw [hafter] at hfirst
    cases right₂
    · refine ⟨((R - L + 1).toNat + 1) + m₂ + ((R₂ - L₂ + 1).toNat + 1), L₂, R₂, hbound,
        by omega, by omega, G₂, ?_⟩
      rw [AbsCfg.run_add, hfirst]
      exact run_toR tm (by omega) .clean
    · exact ⟨_, L₂, R₂, by omega, by omega, by omega, G₂, hfirst⟩
  · have hafter : afterStep a = .collect q' := by simp [afterStep, hs]
    rw [hafter] at hfirst
    cases right₂
    · exact ⟨_, L₂, R₂, by omega, by omega, by omega, G₂, hfirst⟩
    · refine ⟨((R - L + 1).toNat + 1) + m₂ + ((R₂ - L₂ + 1).toNat + 1), L₂, R₂, hbound,
        by omega, by omega, G₂, ?_⟩
      rw [AbsCfg.run_add, hfirst]
      exact run_toL tm (by omega) (.collect q')

/-- The initialization sweep, as a function of the flag for the first cell and a cell. -/
def initF (first : Bool) : Option (Symbol ⊕ Cell k Symbol) → Bool × Option (Symbol ⊕ Cell k Symbol)
  | some (.inl b) => (false, some (.inr (initCell false first (some b))))
  | a => (first, a)

omit [Fintype Symbol] [Fintype State] in
lemma sweepOut_initF (first : Bool) (x : List Symbol) :
    sweepOut (initF (k := k)) first (x.map fun b => some (.inl b)) =
      (first && x.isEmpty, (x.zipIdx.map fun (b, i) =>
        some (.inr (initCell false (first && i == 0) (some b))))) := by
  induction x generalizing first with
  | nil => simp [sweepOut]
  | cons b x ih =>
    simp only [List.map_cons, sweepOut, initF, ih, Bool.false_and, List.isEmpty_cons,
      Bool.and_false, List.zipIdx_cons, Prod.mk.injEq, List.cons.injEq, true_and]
    refine ⟨by simp, ?_⟩
    rw [List.zipIdx_succ, List.map_map]
    congr 1
    funext p
    simp

omit [Fintype Symbol] [Fintype State] in
/-- The tracks of the initial configuration. -/
lemma cellOf_init (x : List Symbol) (z : ℤ) (hz₁ : -1 ≤ z) (hz₂ : z ≤ x.length) :
    cellOf x.length (tracks (tm.initCfg x)) z =
      initCell (decide (z = -1)) (decide (z = 0))
        (if 0 ≤ z then x[z.toNat]? else none) := by
  refine Cell.ext (funext fun j => ?_) (funext fun j => ?_) ?_ ?_ ?_
  · cases j <;> simp [cellOf, tracks, initCell, MultiTapeNTM.initCfg, Cfg.init]
  · cases j <;> simp [cellOf, tracks, initCell, MultiTapeNTM.initCfg, Cfg.init]
  · simp [cellOf, initCell]
  · simp only [cellOf, initCell]
    by_cases h : z = -1
    · subst h
      simp
    · by_cases h' : z = x.length
      · subst h'
        simp
      · simp only [h, decide_false, Bool.not_false, Bool.true_and, h']
        rw [ite_eq_left (by omega), List.getElem?_eq_getElem (by omega)]
        rfl
  · simp [cellOf, initCell]

omit [Fintype Symbol] [Fintype State] in
lemma good_init (x : List Symbol) :
    Good x.length (tracks (tm.initCfg x)) (-1) x.length where
  left := le_rfl
  right := le_rfl
  head j := by cases j <;> simp [tracks, MultiTapeNTM.initCfg, Cfg.init]
  blank j z hz := by
    cases j <;> simp [tracks, MultiTapeNTM.initCfg, Cfg.init]
    omega
  input := by simp [tracks, MultiTapeNTM.initCfg, Cfg.init]

/-- **Initialization.** On the plain input `x`, the machine encodes the initial configuration on
cells `-1, …, |x|` and stands on cell `-1`, ready to collect, after `2 |x| + 6` steps. -/
lemma run_init (x : List Symbol) :
    (tm.toSingleTape.absInit (x.map .inl)).run (2 * x.length + 6) =
      ⟨some (.collect tm.q₀ fun _ => none), -1,
        tapeOf x.length (tracks (tm.initCfg x)) (-1) x.length⟩ := by
  set n := x.length
  set cells₀ := (BiTape.mk₁ (x.map Sum.inl : List (Symbol ⊕ Cell k Symbol))).read with hcells₀
  have hread : ∀ z : ℤ, cells₀ z = if 0 ≤ z then (x[z.toNat]?).map Sum.inl else none := by
    intro z
    rw [hcells₀, BiTape.read_mk₁]
    simp
  -- the first two steps: step left and back, writing cell `-1`
  set cells₁ := Function.update cells₀ (-1) (some (.inr (initCell true false none))) with hcells₁
  have h₂ : (tm.toSingleTape.absInit (x.map .inl)).run 2 =
      ⟨some (.init₂ true), 0, cells₁⟩ := by
    have h₀ : tm.toSingleTape.absInit (x.map .inl) =
        (⟨some (SimState.init₀ : SimState k Symbol State), 0, cells₀⟩ :
          tm.toSingleTape.AbsCfg) := rfl
    rw [h₀, AbsCfg.run_succ, AbsCfg.run_succ, AbsCfg.run_zero]
    simp only [AbsCfg.next, toSingleTape_tr, simTr, simStep, moveShift, Function.update_eq_self]
    congr 1
  -- the sweep over the input
  obtain ⟨h₁, h₂', h₃, h₄⟩ := AbsCfg.run_sweep (tm := tm.toSingleTape) (D := Bool) .init₂ initF
    .right (x.map fun b => some (.inl b)) (fun d a ha => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
      rfl) true ⟨some (.init₂ true), 0, cells₁⟩ rfl (fun j hj => by
      simp only [moveShift, zero_add, one_mul, hcells₁]
      rw [Function.update_of_ne (by omega), hread]
      simp [List.getElem?_eq_getElem (by simpa using hj)])
  rw [sweepOut_initF] at h₁
  simp only [List.length_map, moveShift, zero_add, one_mul] at h₁ h₂' h₃ h₄
  rcases hA : AbsCfg.run (⟨some (SimState.init₂ true), 0, cells₁⟩ : tm.toSingleTape.AbsCfg) n
    with ⟨st, p, cells₂⟩
  rw [hA] at h₁ h₂' h₃ h₄
  simp only at h₁ h₂' h₃ h₄
  subst h₁ h₂'
  -- the step on cell `|x|`, then the walk back to cell `-1`
  have hcells₂ : Function.update cells₂ n (some (.inr (initCell false (true && x.isEmpty) none))) =
      tapeOf n (tracks (tm.initCfg x)) (-1) n := by
    funext z
    by_cases hz : -1 ≤ z ∧ z ≤ n
    · rw [tapeOf_of_mem hz.1 hz.2, cellOf_init tm x z hz.1 hz.2]
      by_cases hzn : z = n
      · subst hzn
        have e₁ : decide ((n : ℤ) = -1) = false := by simp only [decide_eq_false_iff_not]; omega
        have e₂ : (true && x.isEmpty) = decide ((n : ℤ) = 0) := by
          cases x <;> simp [n]
          omega
        have e₃ : (if 0 ≤ (n : ℤ) then x[(n : ℤ).toNat]? else none) = none := by simp [n]
        rw [Function.update_self, e₁, e₂, e₃]
      · rw [Function.update_of_ne hzn]
        by_cases hzm : z = -1
        · subst hzm
          rw [h₄ _ fun j _ => by omega, hcells₁, Function.update_self]
          simp
        · have hzi := (h₃ z.toNat (by omega)).trans
            (List.getElem_of_eq (congrArg Prod.snd (sweepOut_initF true x)) _)
          rw [show ((z.toNat : ℕ) : ℤ) = z by omega] at hzi
          rw [hzi]
          simp only [List.getElem_map, List.getElem_zipIdx]
          rw [ite_eq_left (by omega), List.getElem?_eq_getElem (by omega)]
          simp only [zero_add, Bool.beq_eq_decide_eq, Int.toNat_eq_zero, Bool.true_and,
            Int.reduceNeg, show ¬z = -1 from hzm, decide_false, Option.some.injEq, Sum.inr.injEq]
          congr 1
          simp only [decide_eq_decide]
          omega
    · rw [tapeOf_of_lt (by omega), Function.update_of_ne (by omega), h₄ _ fun j _ => by omega,
        hcells₁, Function.update_of_ne (by omega), hread]
      split_ifs with h
      · rw [List.getElem?_eq_none (by omega)]
        rfl
      · rfl
  rw [show 2 * x.length + 6 = 2 + (n + (1 + (((n : ℤ) - (-1) + 1).toNat + 1))) by omega,
    AbsCfg.run_add, h₂, AbsCfg.run_add, hA, AbsCfg.run_add,
    show ∀ c : tm.toSingleTape.AbsCfg, c.run 1 = c.next from fun _ => rfl]
  have hnone : cells₂ x.length = none := by
    rw [h₄ _ fun j hj => by omega, hcells₁, Function.update_of_ne (by omega), hread]
    simp
  simp only [AbsCfg.next, toSingleTape_tr, hnone, simTr, simStep, moveShift, add_zero]
  rw [hcells₂]
  exact run_toL tm (by omega) (.collect tm.q₀)

/-- The cleanup sweep, as a function of whether the origin is behind and a cell. -/
def cleanF (passed : Bool) :
    Option (Symbol ⊕ Cell k Symbol) → Bool × Option (Symbol ⊕ Cell k Symbol)
  | some (.inr c) => if passed then (true, none) else if c.origin then (true, some (.inr c))
    else (false, convert c)
  | a => (passed, a)

/-- Cell `z` after the cleanup sweep: blank left of the origin, the origin as it was, and the
output symbol right of it. -/
def cleanCell (n : ℕ) (td : Track k → TrackTape Symbol) (z : ℤ) :
    Option (Symbol ⊕ Cell k Symbol) :=
  if z < 0 then none else if z = 0 then some (.inr (cellOf n td z)) else convert (cellOf n td z)

/-- The cells `start, start - 1, …` after the cleanup sweep. -/
def cleanList (n : ℕ) (td : Track k → TrackTape Symbol) (start : ℤ) :
    ℕ → List (Option (Symbol ⊕ Cell k Symbol))
  | 0 => []
  | W + 1 => cleanCell n td start :: cleanList n td (start - 1) W

omit [Fintype Symbol] [Fintype State] in
lemma getElem_cleanList (n : ℕ) (td : Track k → TrackTape Symbol) (start : ℤ) (W i : ℕ)
    (hi : i < (cleanList n td start W).length) :
    (cleanList n td start W)[i] = cleanCell n td (start - i) := by
  induction W generalizing start i with
  | zero => simp [cleanList] at hi
  | succ W ih =>
    rcases i with _ | i
    · simp [cleanList]
    · simp only [cleanList, List.getElem_cons_succ]
      rw [ih]
      congr 1
      push_cast
      ring

omit [Fintype Symbol] [Fintype State] in
@[simp] lemma length_cleanList (n : ℕ) (td : Track k → TrackTape Symbol) (start : ℤ) (W : ℕ) :
    (cleanList n td start W).length = W := by
  induction W generalizing start with
  | zero => rfl
  | succ W ih => simp [cleanList, ih]

omit [Fintype Symbol] [Fintype State] in
lemma sweepOut_clean (n : ℕ) (td : Track k → TrackTape Symbol) :
    ∀ (W : ℕ) (start : ℤ), sweepOut cleanF (decide (start < 0)) (region n td start (-1) W) =
      (decide (start - W < 0), cleanList n td start W)
  | 0, start => by simp [region, cleanList, sweepOut]
  | W + 1, start => by
    have hcell : cleanF (decide (start < 0)) (some (.inr (cellOf n td start))) =
        (decide (start + -1 < 0), cleanCell n td start) := by
      by_cases h : start < 0
      · simp [cleanF, cleanCell, h]
        omega
      · by_cases h0 : start = 0
        · subst h0
          simp [cleanF, cleanCell, cellOf]
        · simp [cleanF, cleanCell, cellOf, h, h0]
          omega
    simp only [region, sweepOut, hcell, sweepOut_clean n td W (start + -1), cleanList,
      Prod.mk.injEq]
    simp only [decide_eq_decide]
    push_cast
    exact ⟨by omega, by rw [show start + -1 = start - 1 by ring]⟩

/-- **Cleanup.** From the right end, the machine converts the occupied cells to the output and
erases the rest, walks back to the origin and halts there, leaving exactly the output `out` on
the tape. -/
lemma run_clean {n : ℕ} {td : Track k → TrackTape Symbol} {L R : ℤ} (G : Good n td L R)
    (out : List Symbol) (hout : ∀ z, (td .output).cells z = if 0 ≤ z then out[z.toNat]? else none) :
    (⟨some (.clean₁ false), R, tapeOf n td L R⟩ : tm.toSingleTape.AbsCfg).run
        ((R - L + 1).toNat + 1 + ((-L).toNat + 1)) =
      ⟨none, 0, (BiTape.mk₁ (out.map .inl)).read⟩ := by
  have hL := G.left
  have hR := G.right
  -- the conversion sweep, leftwards from `R`
  obtain ⟨h₁, h₂, h₃, h₄⟩ := AbsCfg.run_sweep (tm := tm.toSingleTape) (D := Bool)
    SimState.clean₁ cleanF .left (region n td R (-1) (R - L + 1).toNat) (fun d a ha => by
      obtain ⟨z, rfl⟩ := exists_of_mem_region ha
      cases d <;> by_cases ho : (cellOf n td z).origin <;> simp [simTr, cleanF, simStep, ho] <;>
        rfl)
    false ⟨some (.clean₁ false), R, tapeOf n td L R⟩ rfl (tapeOf_eq_region_left (by omega))
  have hR0 : decide (R < 0) = false := by simp only [decide_eq_false_iff_not]; omega
  have hsweep := sweepOut_clean n td (R - L + 1).toNat R
  rw [hR0] at hsweep
  rw [hsweep] at h₁
  simp only [length_region, moveShift] at h₁ h₂ h₃ h₄
  rcases hA : AbsCfg.run (⟨some (SimState.clean₁ false), R, tapeOf n td L R⟩ :
      tm.toSingleTape.AbsCfg) (R - L + 1).toNat with ⟨st, p, cells₁⟩
  rw [hA] at h₁ h₂ h₃ h₄
  simp only at h₁ h₂ h₃ h₄
  subst h₁ h₂
  have hcells₁ : ∀ z, cells₁ z = if L ≤ z ∧ z ≤ R then cleanCell n td z else none := by
    intro z
    split_ifs with hz
    · have := (h₃ (R - z).toNat (by omega)).trans
        (List.getElem_of_eq (congrArg Prod.snd hsweep) _)
      rw [show R + -1 * ((R - z).toNat : ℤ) = z by omega, getElem_cleanList] at this
      rw [this]
      congr 1
      omega
    · rw [h₄ z fun j hj => by omega, tapeOf_of_lt (by omega)]
  -- the walk back over the erased cells
  set cells₂ := Function.update cells₁ (L - 1) none with hcells₂
  obtain ⟨g₁, g₂, g₃, g₄⟩ := AbsCfg.run_sweep (tm := tm.toSingleTape) (D := Unit)
    (fun _ => SimState.clean₂) (fun d a => (d, a)) .right (List.replicate (-L).toNat none)
    (fun d a ha => by rw [List.eq_of_mem_replicate ha]; rfl) () ⟨some .clean₂, L, cells₂⟩ rfl
    (fun j hj => by
      simp only [List.length_replicate] at hj
      simp only [moveShift, one_mul, List.getElem_replicate, hcells₂]
      rw [Function.update_of_ne (by omega), hcells₁]
      split_ifs with h
      · simp only [cleanCell]
        rw [ite_eq_left (by omega)]
      · rfl)
  simp only [List.length_replicate, moveShift, one_mul] at g₁ g₂ g₃ g₄
  rcases hB : AbsCfg.run (⟨some SimState.clean₂, L, cells₂⟩ : tm.toSingleTape.AbsCfg)
      (-L).toNat with ⟨st', p', cells₃⟩
  rw [hB] at g₁ g₂ g₃ g₄
  simp only at g₁ g₂ g₃ g₄
  subst g₁ g₂
  have hcells₃ : cells₃ = cells₂ := by
    funext z
    by_cases hz : L ≤ z ∧ z < 0
    · have := g₃ (z - L).toNat (by omega)
      rw [show L + ((z - L).toNat : ℤ) = z by omega,
        List.getElem_of_eq (sweepOut_walk (fun d _ => d) () _)] at this
      rw [this, List.getElem_replicate, hcells₂, Function.update_of_ne (by omega), hcells₁]
      split_ifs with h
      · simp only [cleanCell]
        rw [ite_eq_left (by omega)]
      · rfl
    · exact g₄ z fun j hj => by omega
  -- the final step on the origin
  have hone : ∀ c : tm.toSingleTape.AbsCfg, c.run 1 = c.next := fun _ => rfl
  rw [AbsCfg.run_add, AbsCfg.run_add _ ((R - L + 1).toNat) 1, hA, hone,
    AbsCfg.run_add _ ((-L).toNat) 1, hone]
  have hstep₁ : (⟨some (SimState.clean₁ (decide (R - ((R - L + 1).toNat : ℤ) < 0))),
      R + -1 * ((R - L + 1).toNat : ℤ), cells₁⟩ : tm.toSingleTape.AbsCfg).next =
      ⟨some .clean₂, L, cells₂⟩ := by
    have hnone : cells₁ (R + -1 * ((R - L + 1).toNat : ℤ)) = none := by
      rw [hcells₁, ite_eq_right (by omega)]
    simp only [AbsCfg.next, hnone, toSingleTape_tr, simTr, simStep, moveShift]
    congr 1
    · omega
    · rw [hcells₂, show R + -1 * ((R - L + 1).toNat : ℤ) = L - 1 by omega]
  rw [hstep₁, hB, hcells₃]
  have h0 : cells₂ (L + ((-L).toNat : ℤ)) = some (.inr (cellOf n td 0)) := by
    rw [show L + ((-L).toNat : ℤ) = 0 by omega, hcells₂, Function.update_of_ne (by omega),
      hcells₁, ite_eq_left (by omega)]
    simp [cleanCell]
  simp only [AbsCfg.next, h0, toSingleTape_tr, simTr, simStep, moveShift, add_zero]
  congr 1
  · omega
  · funext z
    rw [BiTape.read_mk₁, show L + ((-L).toNat : ℤ) = 0 by omega]
    by_cases hz0 : z = 0
    · subst hz0
      simp [convert, cellOf, hout]
    · rw [Function.update_of_ne hz0, hcells₂]
      by_cases hzL : z = L - 1
      · subst hzL
        rw [Function.update_self, ite_eq_right (by omega)]
      · rw [Function.update_of_ne hzL, hcells₁]
        by_cases h' : 0 ≤ z
        · by_cases h : L ≤ z ∧ z ≤ R
          · simp [h, h', cleanCell, show ¬ z < 0 by omega, hz0, convert, cellOf, hout]
          · have hb := G.blank .output z (by omega)
            simp only [hout, h', ↓reduceIte] at hb
            simp [h, h', hb]
        · simp [h', cleanCell, show z < 0 by omega]

/-- **The run so far.** After the first `u` simulated steps the single-tape machine encodes the
configuration reached by `tm`, within `2 |x| + 6 + K² u (|x| + u + 1)` steps for
`K = 2 k + 10`, on at most `|x| + 2 + 2 (k + 2) u` occupied cells. -/
lemma reach (x : List Symbol) : ∀ u : ℕ, ∃ m L R,
    m ≤ 2 * x.length + 6 + (2 * k + 10) * (2 * k + 10) * u * (x.length + u + 1) ∧
    (R - L + 1).toNat ≤ x.length + 2 + 2 * (k + 2) * u ∧
    Good x.length (tracks (tm.runFrom (tm.initCfg x) u)) L R ∧
    (tm.toSingleTape.absInit (x.map .inl)).run m =
      match (tm.runFrom (tm.initCfg x) u).state with
      | some q => ⟨some (.collect q fun _ => none), L,
          tapeOf x.length (tracks (tm.runFrom (tm.initCfg x) u)) L R⟩
      | none => ⟨some (.clean₁ false), R,
          tapeOf x.length (tracks (tm.runFrom (tm.initCfg x) u)) L R⟩
  | 0 => ⟨2 * x.length + 6, -1, x.length, by omega, by omega, good_init tm x, by
      rw [run_init]
      rfl⟩
  | u + 1 => by
    obtain ⟨m, L, R, hm, hW, G, hrun⟩ := reach x u
    rw [runFrom_succ]
    rcases hq : (tm.runFrom (tm.initCfg x) u).state with _ | q
    · -- halted: nothing changes
      rw [step_of_halt hq]
      refine ⟨m, L, R, ?_, by nlinarith, G, ?_⟩
      · have : u * (x.length + u + 1) ≤ (u + 1) * (x.length + (u + 1) + 1) := by nlinarith
        nlinarith
      · rw [hrun, hq]
    · rw [hq] at hrun
      obtain ⟨m', L', R', hm', hL', hR', G', hrun'⟩ := run_step tm hq G
      have hexp : 2 * (k + 2) * (u + 1) = 2 * (k + 2) * u + 2 * (k + 2) := by ring
      refine ⟨m + m', L', R', ?_, by omega, G', ?_⟩
      · have h₁ : (R - L + 1).toNat + 2 * k + 8 ≤ (2 * k + 10) * (x.length + u + 1) := by
          nlinarith
        have h₂ : m' ≤ (2 * k + 10) * ((2 * k + 10) * (x.length + u + 1)) :=
          hm'.trans (Nat.mul_le_mul (by omega) h₁)
        nlinarith
      · rw [AbsCfg.run_add, hrun, hrun']

end Turing.MultiTapeTM.ToSingleTape

namespace Turing.MultiTapeTM

open ToSingleTape Cslib.Turing Cslib.Turing.SingleTapeTM

variable {k : ℕ} {Symbol State : Type} [Fintype Symbol] [Fintype State]
  (tm : MultiTapeTM k Symbol State)

/-- **Multi-tape machines in quadratic time on one tape.** If the `k`-work-tape machine `tm`
halts on `x` within `t` steps, then the single-tape machine `toSingleTape tm` outputs the same
output, in plain symbols, within `4 (2k + 10)² (t + 1) (|x| + t + 1)` steps. -/
theorem outputsWithinTime_toSingleTape {x : List Symbol} {t : ℕ}
    (hhalt : (tm.runFrom (tm.initCfg x) t).Halted) :
    tm.toSingleTape.OutputsWithinTime (x.map .inl)
      ((tm.runFrom (tm.initCfg x) t).output.map .inl)
      (4 * (2 * k + 10) ^ 2 * (t + 1) * (x.length + t + 1)) := by
  obtain ⟨m, L, R, hm, hW, G, hrun⟩ := reach tm x t
  rw [show (tm.runFrom (tm.initCfg x) t).state = none from hhalt] at hrun
  have hclean := run_clean tm G (tm.runFrom (tm.initCfg x) t).output fun z => rfl
  have hL := G.left
  have hR := G.right
  have hfinal : (tm.toSingleTape.absInit (x.map .inl)).run
      (m + ((R - L + 1).toNat + 1 + ((-L).toNat + 1))) =
      ⟨none, 0, (BiTape.mk₁ ((tm.runFrom (tm.initCfg x) t).output.map .inl)).read⟩ := by
    rw [AbsCfg.run_add, hrun]
    exact hclean
  apply outputsWithinTime_of_absRun
  have hle : m + ((R - L + 1).toNat + 1 + ((-L).toNat + 1)) ≤
      4 * (2 * k + 10) ^ 2 * (t + 1) * (x.length + t + 1) := by
    have h₁ : (-L).toNat ≤ (R - L + 1).toNat := by omega
    have hK2 : (2 * k + 10) * (2 * k + 10) = (2 * k + 10) ^ 2 := by ring
    rw [hK2] at hm
    have hexp : 4 * (2 * k + 10) ^ 2 * (t + 1) * (x.length + t + 1) =
        4 * ((2 * k + 10) ^ 2 * t * (x.length + t + 1)) +
          4 * (2 * k + 10) ^ 2 * (x.length + t + 1) := by ring
    have e₁ : 3 ≤ (2 * k + 10) ^ 2 := by nlinarith
    have e₂ : k + 2 ≤ (2 * k + 10) ^ 2 := by nlinarith
    have hb : 2 * x.length + 6 + 2 * (x.length + 2 + 2 * (k + 2) * t) + 2 ≤
        4 * (2 * k + 10) ^ 2 * (x.length + t + 1) := by
      nlinarith [Nat.mul_le_mul_right x.length e₁, Nat.mul_le_mul_right t e₂]
    rw [hexp]
    have : (2 * k + 10) ^ 2 * t * (x.length + t + 1) ≤
        4 * ((2 * k + 10) ^ 2 * t * (x.length + t + 1)) := by omega
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, AbsCfg.run_add, hfinal, AbsCfg.run_of_none rfl]

/-- The same bound for a computation with the shared time and space bounds. -/
theorem outputsWithinTime_toSingleTape_of_computesInTimeAndSpace {x y : List Symbol} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace x y t s) :
    tm.toSingleTape.OutputsWithinTime (x.map .inl) (y.map .inl)
      (4 * (2 * k + 10) ^ 2 * (t + 1) * (x.length + t + 1)) := by
  obtain ⟨⟨u, hu, hout⟩, htime, -⟩ := h
  have hhalt := runsInTime_iff_halted.1 htime
  have heq : tm.runFrom (tm.initCfg x) t = tm.runFrom (tm.initCfg x) u := by
    rcases le_total t u with h | h
    · exact (runFrom_eq_of_halt tm _ h hhalt).symm
    · exact runFrom_eq_of_halt tm _ h hu
  rw [← hout, ← heq]
  exact tm.outputsWithinTime_toSingleTape hhalt

end Turing.MultiTapeTM
