/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PositionPairsCore

/-!
# Linear construction of the outer schedule height

A binary counter with value `r` specifies `2*r` movement bits. A three-tape machine moves
a marked head to that distance using amortized binary decrements, then walks back and emits
one chosen symbol per cell. The source input head stays at its starting position.
-/

public section

namespace Turing.MultiTapeTM.ScheduleHeightWord

open Cslib.BitString PositionPairs

/-- Emit one symbol per blank cell to the right of the marker, returning to the marker. -/
@[expose] def emit (symbol : Bool) : MultiTapeTM 3 Bool Unit :=
  .ofTr () fun _ _ work =>
    if (work 0).isSome then ⟨0, fun _ => (none, 0), none, none⟩
    else ⟨0, ![(none, -1), (none, 0), (none, 0)], some symbol, some ()⟩

private theorem run_emit (b : Bool) (input : List Bool) (n : ℕ) (out : List Bool) :
    (emit b).runFrom ((config input [false] [] [] n out).withState (some ())) (n + 1) =
      (config input [false] [] [] 0 (out ++ List.replicate n b)).withState none := by
  induction n generalizing out with
  | zero =>
    simp only [Nat.cast_zero, List.replicate_zero, List.append_nil, Nat.zero_add, runFrom_one]
    apply step_tapesCfg (a := ⟨0, fun _ => (none, 0), none, none⟩)
    · simp [emit, tapeOfList_zero]
    · rfl
    · rfl
    · intro i; rfl
    · intro i; simp
  | succ n ih =>
    have step : (emit b).step
        ((config input [false] [] [] (n + 1 : ℕ) out).withState (some ())) =
        (config input [false] [] [] n (out ++ [b])).withState (some ()) := by
      rw [step_of_state rfl]
      let a : Action 3 Bool Unit := ⟨0, ![(none, -1), (none, 0), (none, 0)], some b, some ()⟩
      have ha : (emit b).tr () (config input [false] [] [] (n + 1 : ℕ) out).inputSymbol
          (config input [false] [] [] (n + 1 : ℕ) out).workTapeSymbols = a := by
        have blank : tapeOfList [false] ((n : ℤ) + 1) = none := by
          exact (tapeOfList_ofNat [false] (n + 1)).trans (by simp)
        simp [a, emit, config, Cfg.workTapeSymbols, tapesCfg, blank]
      change ((emit b).tr () (config input [false] [] [] (n + 1 : ℕ) out).inputSymbol
        (config input [false] [] [] (n + 1 : ℕ) out).workTapeSymbols).apply _ = _
      rw [ha]
      refine Cfg.ext rfl ?_ ?_ ?_ rfl
      · simp [a, Action.apply, config, tapesCfg, Cfg.withState]
      · funext i
        fin_cases i <;> rfl
      · funext i
        fin_cases i <;> simp [a, Action.apply, config, tapesCfg, Cfg.withState]
    rw [show n + 1 + 1 = 1 + (n + 1) by omega, runFrom_add, runFrom_one, step, ih]
    rw [List.append_assoc, List.replicate_succ]
    rfl

/-- Write a word of even length from its binary half-length. -/
noncomputable def machine (b : Bool) := (guarded fun _ => true).seq (emit b)

/-- The output appends exactly twice the binary counter value copies of the requested bit.
Both the run time and the charged work space are linear in the output plus the input word. -/
theorem runsBetween (b : Bool) (input w out : List Bool) :
    let n := lsbValue w
    let time := 13 * n + 5 * w.length + 14
    RunsBetween (machine b) (config input [false] w [] 0 out)
      (config input [false] [] [] 0 (out ++ List.replicate (2 * n) b)) time
      (3 * (time + 1)) := by
  intro n time
  have hstart := runsBetween_guarded (fun _ => true) input [false] w out n le_rfl
    (fun _ _ => rfl) (Or.inl rfl)
  have hend := run_emit b input (2 * n) out
  have hr := hstart.seq (RunsBetween.of_runFrom (by simpa using hend))
  apply RunsBetween.of_runFrom
  have heq : 11 * n + 5 * w.length + 13 + (2 * n + 1) = time := by dsimp [time]; omega
  simpa only [machine, heq] using hr.1

private def highBit : MultiTapeTM 3 Bool Unit :=
  .ofTr () fun _ _ _ => ⟨0, fun _ => (none, 0), some true, none⟩

private theorem run_highBit (input out : List Bool) :
    highBit.runFrom ((config input [false] [] [] 0 out).withState (some ())) 1 =
      (config input [false] [] [] 0 (out ++ [true])).withState none := by
  rw [runFrom_one, step_of_state rfl]
  simp only [highBit, tr_ofTr]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · simp [Action.apply, config, tapesCfg, Cfg.withState]
  · funext j
    simp [Action.apply, config, tapesCfg, Cfg.withState]
  · simp [Action.apply, config, tapesCfg, Cfg.withState]

/-- The serialized leaf count is one high bit after all the low zeros. -/
theorem bits_pow (L : ℕ) : (2 ^ L).bits = List.replicate L false ++ [true] := by
  induction L with
  | zero => exact Nat.one_bits
  | succ L ih =>
    rw [Nat.pow_succ', Nat.bit0_bits _ (by positivity), ih, List.replicate_succ]
    rfl

/-- Emit the binary cardinality of the outer binary tree. -/
noncomputable def leafCount := (machine false).seq highBit

/-- The binary word for the full tree's leaf count can be installed in linear time even though
the cardinality itself is exponential in the raw schedule length. -/
theorem runsBetween_leafCount (input w out : List Bool) :
    let n := lsbValue w
    let time := 13 * n + 5 * w.length + 15
    RunsBetween leafCount (config input [false] w [] 0 out)
      (config input [false] [] [] 0 (out ++ (2 ^ (2 * n)).bits)) time (3 * (time + 1)) := by
  intro n time
  have hc := runsBetween false input w out
  have hb := RunsBetween.of_runFrom (run_highBit input (out ++ List.replicate (2 * n) false))
  have h := hc.seq hb
  apply RunsBetween.of_runFrom
  simpa only [leafCount, bits_pow, List.append_assoc, time, n, Nat.add_assoc] using h.1

end Turing.MultiTapeTM.ScheduleHeightWord
