/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Lookup

/-!
# Skipping a framed word on one work tape

The two states alternate between a marker and a payload cell. The first false marker halts the
machine after moving the selected head onto the suffix. It takes one step per cell in the frame,
preserves all tape contents and output, and keeps the input head fixed.
-/

public section

namespace Turing.MultiTapeTM.SkipFrame

/-- In the marker state read the prefix tag; in the payload state skip exactly one cell. -/
@[expose] def machine {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Bool :=
  .ofTr false fun data _ work =>
    ⟨0, Function.update (fun _ => (none, 0)) i (none, 1), none,
      if data then some false else if work i = some true then some true else none⟩

private def position {k : ℕ} {input : List Bool} (i : Fin k) (store : Cfg k Bool Unit input)
    (p : ℕ) (q : Option Bool) : Cfg k Bool Bool input :=
  { store.withState q with workTapePos := Function.update store.workTapePos i (p : ℤ) }

private theorem step {k : ℕ} {input : List Bool} (i : Fin k) (store : Cfg k Bool Unit input)
    (tape : List Bool) (htape : store.workTapes i = tapeOfList tape) (p : ℕ) (q : Bool) :
    (machine i).step (position i store p (some q)) = position i store (p + 1)
      (if q then some false else if tape[p]? = some true then some true else none) := by
  rw [step_of_state rfl]
  have hr : (position i store p (some q)).workTapeSymbols i = tape[p]? := by
    simp [position, Cfg.workTapeSymbols, Cfg.withState, htape]
  simp only [machine, tr_ofTr, hr]
  refine Cfg.ext rfl (by simp [position, moveInputPos_zero]) ?_ ?_ (by simp [position]) <;>
    funext j <;> by_cases hj : j = i <;> simp [position, Cfg.withState, hj]

/-- From the origin of the selected work tape, reach the beginning of the suffix in exactly
the frame length. The arbitrary host input, its cursor, all work tapes, other heads and
any previously emitted output are preserved. -/
theorem runFrom {k : ℕ} {input : List Bool} (i : Fin k) (w tail : List Bool)
    (storage : Cfg k Bool Unit input) (hw : storage.workTapes i = tapeOfList (frame w ++ tail))
    (hp : storage.workTapePos i = 0) :
    (machine i).runFrom (storage.withState (some (machine i).q₀)) (frame w).length =
      { storage.withState (none : Option Bool) with
        workTapePos := Function.update storage.workTapePos i ((frame w).length : ℤ) } := by
  have hstart : position i storage 0 (some false) = storage.withState (some (machine i).q₀) := by
    apply Cfg.ext <;> try rfl
    funext j
    by_cases h : j = i <;> simp [position, h, hp]
  have hprefix (n : ℕ) (hn : n ≤ w.length) : (machine i).runFrom
      (position i storage 0 (some false)) (2 * n) = position i storage (2 * n) (some false) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hm := (getElem?_frame_append w tail (show n < w.length by omega)).1
      rw [Nat.mul_succ, runFrom_add, ih (by omega), show 2 = 1 + 1 by rfl, runFrom_add]
      simp only [runFrom_one, step i storage _ hw, hm, ↓reduceIte, Bool.false_eq_true]
  have hend := getElem?_frame_append_length w tail
  rw [← hstart, length_frame, runFrom_add, hprefix _ le_rfl, runFrom_one, step i storage _ hw]
  simp [position, hend]

end Turing.MultiTapeTM.SkipFrame
