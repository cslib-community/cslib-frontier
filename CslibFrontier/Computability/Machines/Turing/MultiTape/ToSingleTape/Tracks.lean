/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.ToSingleTape.Defs

/-!
# The track view of multi-tape configurations

For the single-tape simulation, a configuration of a multi-tape machine on input `x` is viewed as
`k + 2` tapes with one head each (`Turing.MultiTapeTM.ToSingleTape.tracks`): the input at cells
`0, …, |x| - 1` with its head at input position minus one, the work tapes as they are, and the
output at cells `0, 1, …` with its head after the last symbol. A step of the machine acts on each
track separately (`tracks_step`): it writes the track's symbol under its head and moves its head
(`TrackTape.step`), except that the input head stays on cell `-1` or cell `|x|` rather than move
past it.

## Main definitions

* `Turing.MultiTapeTM.ToSingleTape.TrackTape`, `TrackTape.step`, `tracks`.

## Main results

* `Turing.MultiTapeTM.ToSingleTape.tracks_step`: a step acts track by track.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ToSingleTape

variable {k : ℕ} {Symbol State : Type}

/-- One track: its cells and the position of its head. -/
@[ext] structure TrackTape (Symbol : Type) where
  /-- The contents of each cell. -/
  cells : ℤ → Option Symbol
  /-- The position of the head. -/
  head : ℤ

/-- The effect of `(write, move)` on track `j` of an input of length `n`: write under the head,
then move it, except that the input head stays on cell `-1` or cell `n` rather than move past
it. -/
def TrackTape.step (n : ℕ) (j : Track k) (act : Option (Option Symbol) × SignType)
    (t : TrackTape Symbol) : TrackTape Symbol where
  cells := act.1.elim t.cells (Function.update t.cells t.head)
  head := if j = .input ∧ ((act.2 = 1 ∧ t.head = n) ∨ (act.2 = -1 ∧ t.head = -1)) then t.head
    else t.head + act.2

/-- The tracks of a configuration on input `x`. -/
def tracks {x : List Symbol} (c : Cfg k Symbol State x) : Track k → TrackTape Symbol
  | .input => ⟨fun z => if 0 ≤ z then x[z.toNat]? else none, (c.inputPos.val : ℤ) - 1⟩
  | .work i => ⟨c.workTapes i, c.workTapePos i⟩
  | .output => ⟨fun z => if 0 ≤ z then c.output[z.toNat]? else none, c.output.length⟩

variable {x : List Symbol}

/-- The symbol under the input head is the symbol under the input track's head. -/
lemma inputSymbol_eq_tracks (c : Cfg k Symbol State x) :
    c.inputSymbol = (tracks c .input).cells (tracks c .input).head := by
  have hp := c.inputPos.isLt
  simp only [tracks]
  by_cases h₀ : c.inputPos.val = 0
  · rw [inputSymbol_eq_none_of_boundary (Or.inl h₀)]
    split_ifs <;> first | rfl | omega
  by_cases h₁ : c.inputPos.val = x.length + 1
  · rw [inputSymbol_eq_none_of_boundary (Or.inr h₁)]
    split_ifs
    · rw [List.getElem?_eq_none (by omega)]
    · rfl
  · rw [inputSymbolInner (c.inputPos.val - 1) (by omega) (by omega)]
    split_ifs
    · rw [List.getElem?_eq_getElem (by omega)]
      congr 2
      omega
    · omega

/-- A step acts on each track separately. -/
theorem tracks_step (tm : MultiTapeTM k Symbol State) {c : Cfg k Symbol State x} {q : State}
    (hq : c.state = some q) (j : Track k) :
    tracks (tm.step c) j = TrackTape.step x.length j
      (j.act (tm.tr q c.inputSymbol c.workTapeSymbols)) (tracks c j) := by
  rw [tm.step_of_state hq]
  generalize tm.tr q c.inputSymbol c.workTapeSymbols = a
  cases j with
  | input =>
    ext z
    · rfl
    · simp only [tracks, Action.apply_inputPos, TrackTape.step, Track.act, true_and]
      have hv := val_moveInputPos_eq c.inputPos a.inputTape
      have := c.inputPos.isLt
      generalize a.inputTape = m at hv ⊢
      generalize hP : moveInputPos c.inputPos m = P at hv ⊢
      split_ifs with h
      · rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
        · simp only [SignType.coe_one] at hv
          omega
        · simp only [SignType.coe_neg_one] at hv
          omega
      · rcases m with _ | _ | _
        · simp only [SignType.zero_eq_zero, SignType.coe_zero] at hv ⊢
          omega
        · simp only [SignType.neg_eq_neg_one, SignType.coe_neg_one] at hv h ⊢
          simp only [show (-1 : SignType) ≠ 1 by decide, false_and, true_and, false_or] at h
          omega
        · simp only [SignType.pos_eq_one, SignType.coe_one] at hv h ⊢
          simp [show (1 : SignType) ≠ -1 by decide] at h
          omega
  | work i =>
    ext z
    · simp only [tracks, Action.apply, TrackTape.step, Track.act]
      cases (a.workTapes i).1 <;> rfl
    · simp [tracks, Action.apply, TrackTape.step, Track.act]
  | output =>
    rcases ho : a.output with _ | s
    · ext z
      · simp [tracks, Action.apply, TrackTape.step, Track.act, ho]
      · simp [tracks, Action.apply, TrackTape.step, Track.act, ho]
    · refine TrackTape.ext (funext fun z => ?_) ?_
      · simp only [tracks, Action.apply, TrackTape.step, Track.act, ho, Option.toList_some,
          Option.elim_some]
        by_cases hz : z = c.output.length
        · subst hz
          simp
        · rw [Function.update_of_ne hz]
          split_ifs with h
          · by_cases h' : z.toNat < c.output.length
            · rw [List.getElem?_append_left h']
            · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
          · rfl
      · simp [tracks, Action.apply, TrackTape.step, Track.act, ho]

end Turing.MultiTapeTM.ToSingleTape
