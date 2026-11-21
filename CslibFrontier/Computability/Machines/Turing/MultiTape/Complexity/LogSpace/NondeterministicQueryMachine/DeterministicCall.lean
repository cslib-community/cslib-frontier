/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine

/-!
# Deterministic calls in a binary-choice query machine

The adapter uses the false selector for each live deterministic step. A true selector at a
live state enters the rejecting state `none`. The all-false replay preserves the original
input and the deterministic state. At a known first halt, it is the unique successful replay.
-/

public section

namespace Turing.QueryMachine

variable {σ : Type*}

/-- Run the deterministic query machine with one permitted selector per live step. -/
def withRejectingChoice (M : QueryMachine σ) : NondeterministicQueryMachine (Option σ) where
  init := some M.init
  query := fun s => s.elim 0 M.query
  next := fun (s, answer, choice) => if choice then none else s.map (fun q => M.next (q, answer))
  halted := fun s => s.elim true M.halted
  accept := fun s => s.elim false M.halted

private theorem step_false (M : QueryMachine σ) (input : List Bool) (s : σ) :
    M.withRejectingChoice.step input (some s) false = some (M.step input s) := by
  by_cases h : M.halted s = true <;>
    simp [NondeterministicQueryMachine.step, NondeterministicQueryMachine.read,
      withRejectingChoice, QueryMachine.step, QueryMachine.read, h]

/-- An all-false replay from an explicit entry state performs the same original-input run. -/
theorem withRejectingChoice_replay_false (M : QueryMachine σ) (input : List Bool)
    (s : σ) (t : ℕ) :
    M.withRejectingChoice.replay input (List.replicate t false) (some s) =
      some (M.runFrom input s t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.replicate_succ', NondeterministicQueryMachine.replay_append, ih,
      NondeterministicQueryMachine.replay_cons, NondeterministicQueryMachine.replay_nil,
      step_false, runFrom_succ]

private theorem replicate_of_success (M : QueryMachine σ) (input : List Bool)
    (bits : List Bool) (s : Option σ)
    (hfirst : M.withRejectingChoice.FirstHalting input bits s)
    (hsuccess : (M.withRejectingChoice.replay input bits s).isSome) :
    bits = List.replicate bits.length false := by
  let B := M.withRejectingChoice
  induction bits generalizing s with
  | nil => rfl
  | cons bit bits ih =>
    obtain ⟨hlive, htail⟩ := (B.firstHalting_cons_iff input bit bits s).mp hfirst
    rw [NondeterministicQueryMachine.replay_cons] at hsuccess
    cases bit with
    | false =>
      exact congrArg (List.cons false) (ih _ htail hsuccess)
    | true =>
      have hreject : B.step input s true = none := by
        rw [NondeterministicQueryMachine.step, hlive]
        rfl
      rw [hreject, B.replay_of_halted input (s := none) rfl] at hsuccess
      cases hsuccess

/-- A deterministic first halt at time `t` has exactly the all-false selector word of length
`t` as its successful first-halting replay. The final state is available to decode the reply. -/
theorem withRejectingChoice_firstHalting_iff (M : QueryMachine σ) (input : List Bool)
    (s : σ) (t : ℕ) (hbefore : ∀ i < t, M.halted (M.runFrom input s i) = false)
    (hhalt : M.halted (M.runFrom input s t) = true) (bits : List Bool) :
    M.withRejectingChoice.FirstHalting input bits (some s) ∧
        (M.withRejectingChoice.replay input bits (some s)).isSome ↔
      bits = List.replicate t false := by
  constructor
  · rintro ⟨hfirst, hsuccess⟩
    have hbits := replicate_of_success M input bits (some s) hfirst hsuccess
    have hlength : bits.length = t := by
      apply le_antisymm
      · by_contra! hlate
        have hprefix := hfirst.2 t hlate
        rw [hbits, List.take_replicate, Nat.min_eq_left hlate.le,
          M.withRejectingChoice_replay_false] at hprefix
        change M.halted (M.runFrom input s t) = false at hprefix
        simp [hhalt] at hprefix
      · by_contra! hearly
        have hfinal := hfirst.1
        rw [hbits, M.withRejectingChoice_replay_false] at hfinal
        change M.halted (M.runFrom input s bits.length) = true at hfinal
        simp [hbefore _ hearly] at hfinal
    exact hbits.trans (congrArg (fun n => List.replicate n false) hlength)
  · rintro rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [M.withRejectingChoice_replay_false]
      exact hhalt
    · intro i hi
      rw [List.length_replicate] at hi
      rw [List.take_replicate, Nat.min_eq_left hi.le, M.withRejectingChoice_replay_false]
      exact hbefore i hi
    · rw [M.withRejectingChoice_replay_false]
      rfl

end Turing.QueryMachine
