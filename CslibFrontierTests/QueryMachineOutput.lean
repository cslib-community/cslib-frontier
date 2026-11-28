/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of query-machine output)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Query-machine output after halting

The transition freezes at a halted state even when its raw emission function is nonempty.
Padding a clock must not invoke that function again or duplicate the final word.
-/

@[expose] public section

namespace CslibFrontierTests.QueryMachineOutput

open Turing

/-- The initial state is halted even though its raw emission function is nonempty. -/
def halted : QueryMachine Unit where
  init := ()
  query _ := 0
  next _ := ()
  emit _ := [true]
  halted _ := true
  finish _ := [false]

example : halted.output [] 0 = [false] := rfl

example : halted.output [] 3 = [false] := by decide

/-- Emit the first input bit, then halt and append a final bit. -/
def echoOnce : QueryMachine Bool where
  init := false
  query _ := 0
  next _ := true
  emit p := [p.2.getD false]
  halted := id
  finish _ := [false]

example : echoOnce.output [true] 1 = [true, false] := by decide

example : echoOnce.output [true] 4 = [true, false] := by decide

example : echoOnce.output [] 4 = [false, false] := by decide

example : echoOnce.outputFrom [true] true 3 = [false] := by decide

example (k : ℕ) : echoOnce.output [true] (1 + k) = [true, false] := by
  rw [echoOnce.output_add_of_halted [true] (t := 1) (by decide)]
  decide

open MultiTapeTM ComputableInSpace in
-- The first bit controls whether the machine runs. If it runs, it reads the second bit
-- at its original input position, with the same default for a missing bit.
example : ComputableInLogSpace
    (fun w : List Bool => if w.headD false then [false] else [w[1]?.getD false, false])
    encBits encBits := by
  let executor : QueryMachine Bool := { echoOnce with query := fun _ => 1 }
  let start := fun w : List Bool => w.headD false
  let time := fun w => if start w then 0 else 1
  let space := fun w : List Bool => Nat.log2 (encBits w).length + 1
  obtain ⟨t, c, hc⟩ := ComputableInLogSpace.bitsHeadD false
  have hstart : ComputableInSpace start encBits encBool space := by
    refine ⟨t, max c 1, hc.mono (fun _ => le_rfl) ?_, ?_⟩
    · intro w
      change c * space w ≤ _
      exact Nat.mul_le_mul (Nat.le_max_left c 1) (Nat.le_succ (space w))
    · intro w
      simp only [encBool_apply, List.length_singleton]
      exact Nat.mul_le_mul (Nat.le_max_right c 1) (Nat.succ_le_succ (Nat.zero_le (space w)))
  refine executor.computableInSpaceFrom (encS := encBool)
    (of_finite _) (of_finite _) (of_finite _) (of_finite _) (of_finite _)
    time space hstart ?_ ?_ ?_ (fun _ => le_rfl) ⟨1, ?_⟩
  · intro w
    cases hs : start w <;>
      simp [time, hs, executor, echoOnce, QueryMachine.runFrom_succ, QueryMachine.step]
  · intro w i hi
    have hiZero : i = 0 := by
      cases hs : start w <;> simp [time, hs] at hi
      omega
    subst i
    cases hs : start w <;> simp [time, hs, executor, echoOnce] at hi ⊢
  · intro w
    change encBits (if start w then [false] else [w[1]?.getD false, false]) =
      executor.outputFrom (encBits w) (start w) (time w)
    cases hs : start w <;>
      simp [time, hs, executor, echoOnce, QueryMachine.outputFrom, QueryMachine.output,
        QueryMachine.read, encBits_apply]
  · intro w i hi
    simp [space]

end CslibFrontierTests.QueryMachineOutput
