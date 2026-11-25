/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.BranchReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.CallReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Foundations.Data.BitString.WordsOfLength

/-! Tests for the native compiler of nondeterministic query machines on looping recognizers and
input-dependent start states. -/

namespace CslibFrontierTests.NondeterministicQueryMachineCompiler

open Turing Turing.MultiTapeTM

/-- Accept when the first input bit is `true`; otherwise loop in state `2` forever. The choice
bit is ignored. -/
private def firstBit : NondeterministicQueryMachine (Fin 3) where
  init := 0
  query _ := 0
  next p := if p.1 = 0 ∧ p.2.1 = some true then 1 else 2
  halted q := q == 1
  accept q := q == 1

/-- On the input `[false]`, every branch from the start state stays out of the halting state. -/
private theorem firstBit_run_ne_one (choices : List Bool) : firstBit.run [false] choices ≠ 1 := by
  have h (choices : List Bool) : firstBit.replay [false] choices 2 = 2 := by
    induction choices with
    | nil => rfl
    | cons b choices ih => exact ih
  cases choices with
  | nil => decide
  | cons b choices =>
    change firstBit.replay [false] choices 2 ≠ 1
    rw [h]
    decide

example : firstBit.Accepts [true] := ⟨[false], rfl, rfl⟩

example : ¬ firstBit.Accepts [false] := fun ⟨choices, hhalt, _⟩ =>
  firstBit_run_ne_one choices (beq_iff_eq.mp hhalt)

/-- The rejecting branch never halts, so no common abstract clock exists. -/
example (t : ℕ) : ¬ firstBit.HaltsWithin [false] t := fun h =>
  firstBit_run_ne_one _ (beq_iff_eq.mp (h (List.replicate t false) List.length_replicate))

/-- A looping recognizer with a constant start state compiles in logarithmic space. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.RecognizesInSpace encBits {input | firstBit.Accepts input}
      fun input => c * (Nat.log2 input.length + 1) :=
  firstBit.exists_recognizesInSpace (enc := encBits) (encS := encFinite (Fin 3))
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (fun _ => firstBit.init) (A := {input | firstBit.Accepts input}) (fun _ => Iff.rfl)
    (fun input : List Bool => Nat.log2 input.length + 1) (fun _ => le_rfl)
    (ComputableInSpace.budget_const _)
    ⟨Nat.card (Fin 3), fun input choices =>
      (length_encFinite_lt (firstBit.run input choices)).le.trans
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))⟩

/-- The start state is the input bit itself: `true` halts and accepts at once, while `false`
loops forever. No step changes the state. -/
private def ownBit : NondeterministicQueryMachine Bool where
  init := false
  query _ := 0
  next p := p.1
  halted q := q
  accept q := q

private theorem ownBit_replay_false (choices : List Bool) :
    ownBit.replay (encBool false) choices false = false := by
  induction choices with
  | nil => rfl
  | cons b choices ih => exact ih

example : (ownBit.withInit true).Accepts (encBool true) := ⟨[], rfl, rfl⟩

example : ¬ (ownBit.withInit false).Accepts (encBool false) := by
  rintro ⟨choices, hhalt, -⟩
  rw [NondeterministicQueryMachine.run_withInit, ownBit_replay_false] at hhalt
  exact Bool.false_ne_true hhalt

/-- The start state depends on the input: the compiled machine recognizes `{true}`, starting
from the input bit, in constant space. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
    ntm.RecognizesInSpace encBool {true} fun _ => c * 1 := by
  refine ownBit.exists_recognizesInSpace (enc := encBool) (encS := encBool)
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    id (A := {true}) (fun b => ?_) (fun _ => 1) (fun _ => by simp)
    ((ComputableInSpace.of_finite id).mono_le fun _ => by simp)
    ⟨1, fun b choices => by simp⟩
  cases b
  · refine ⟨fun h => absurd h (by decide), fun ⟨choices, hhalt, _⟩ => ?_⟩
    change ownBit.replay (encBool false) choices false = true at hhalt
    rw [ownBit_replay_false] at hhalt
    exact absurd hhalt Bool.false_ne_true
  · exact ⟨fun _ => ⟨[], rfl, rfl⟩, fun _ => rfl⟩

open NondeterministicQueryMachine in
/-- For the initially halted input-dependent start, every halted full replay splits at the
checked finalizer boundary with the same choice bits and final configuration. -/
example : ∃ (R : Routines ownBit id encBool (fun _ => 1)) (n : ℕ),
    let initial := R.machine.initCfg (encBool true)
    let boundary := wordsCfg (encBool true) (some (.finish R.F.q₀ : Native.State R.SI R.SP R.SF))
      (R.boundary true false) []
    Native.replayChoices R.I R.P R.F R.C initial (List.replicate n 0) = some ([], boundary) ∧
      ∀ (indices : List ℕ) (bits : List Bool)
        (final : Cfg R.k Bool (Native.State R.SI R.SP R.SF) (encBool true)), final.Halted →
        Native.replayChoices R.I R.P R.F R.C initial indices = some (bits, final) →
        ∃ rest, indices = List.replicate n 0 ++ rest ∧
          Native.replayChoices R.I R.P R.F R.C boundary rest = some (bits, final) := by
  obtain ⟨R⟩ := ownBit.exists_routines (enc := encBool) (encS := encBool)
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    (ComputableInSpace.of_finite _) (ComputableInSpace.of_finite _)
    id (fun _ => 1) (fun _ => by simp)
    ((ComputableInSpace.of_finite id).mono_le fun _ => by simp)
    ⟨1, fun b choices => by simp⟩
  obtain ⟨n, hprefix, hfactor⟩ := R.init_replay true
  exact ⟨R, n, hprefix, fun indices bits final hhalt hr => (hfactor indices bits final hhalt).mp hr⟩

open NondeterministicQueryMachine in
/-- A pass from the live start of `firstBit` on `[true]` selects the finalizer with state `1`.
The suffix retains the terminal configuration and all choices after the true selector. -/
example (R : Routines firstBit (fun _ => 0) encBits (fun a => Nat.log2 a.length + 1)) :
    ∃ first, ∀ (indices : List ℕ) (bits : List Bool)
      (final : Cfg R.k Bool (Native.State R.SI R.SP R.SF) [true]), final.Halted →
      Native.replayChoices R.I R.P R.F R.C
        (wordsCfg [true] (some .choose) (R.boundary 0 false) []) indices =
        some (true :: bits, final) →
      ∃ rest, indices = first ++ rest ∧ Native.replayChoices R.I R.P R.F R.C
        (wordsCfg [true] (some (.finish R.F.q₀)) (R.boundary 1 false) []) rest =
          some (bits, final) := by
  obtain ⟨first, _, hfactor⟩ := R.pass_replay [true] 0
    ((firstBit.withInit 0).reachable_init _) true false []
  exact ⟨first, fun indices bits final hhalt hr => (hfactor indices bits final hhalt).mp hr⟩


/-- Both passes ignore their selector, so distinct bit traces can have identical abstract
state sequences. Occurrence-sensitive compilation must retain those distinctions. -/
private def twoPass : NondeterministicQueryMachine (Fin 3) where
  init := 0
  query _ := 0
  next p := if p.1 = 0 then 1 else 2
  halted q := q == 2
  accept q := q == 2

open NondeterministicQueryMachine in
/-- Two genuine choices survive compilation even though the abstract transitions ignore them.
The full initializer/pass/finalizer composition has one native occurrence trace for each pair. -/
example (R : Routines twoPass (fun _ => 0) encBits (fun a => Nat.log2 a.length + 1))
    (input : List Bool) (b c : Bool) :
    ∃! indices, ∃ final, Native.replayChoices R.I R.P R.F R.C
      (R.machine.initCfg input) indices = some ([b, c], final) ∧ final.Halted := by
  apply (R.existsUnique_replay_iff input [b, c]).mpr
  refine ⟨rfl, ?_⟩
  intro n hn
  have hn' : n < 2 := hn
  interval_cases n <;> rfl

open NondeterministicQueryMachine in
/-- A full native replay cannot retain the abstract model's padding after the first halt. -/
example (R : Routines firstBit (fun _ => 0) encBits (fun a => Nat.log2 a.length + 1))
    {indices : List ℕ} {final : Cfg R.k Bool (Native.State R.SI R.SP R.SF) [true]}
    (hr : Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg [true]) indices =
      some ([false, true], final)) : ¬final.Halted := by
  intro hhalt
  have h := (R.replay_correct [true] hr hhalt).1.2 1 (by decide)
  exact Bool.noConfusion h

open NondeterministicQueryMachine in
/-- The full replay's output is the verdict of the abstract state after both passes. -/
example (R : Routines twoPass (fun _ => 0) encBits (fun a => Nat.log2 a.length + 1))
    (input : List Bool) {indices : List ℕ}
    {final : Cfg R.k Bool (Native.State R.SI R.SP R.SF) input}
    (hr : Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg input) indices =
      some ([false, true], final)) (hhalt : final.Halted) : final.output = [true] :=
  (R.replay_correct input hr hhalt).2

open NondeterministicQueryMachine in
/-- An initially halted accepting source has one full native occurrence trace with no choices;
initialization never introduces the two spurious selector occurrences. -/
example (R : Routines ownBit id encBool (fun _ => 1)) :
    ∃! indices, ∃ final, Native.replayChoices R.I R.P R.F R.C
      (R.machine.initCfg (encBool true)) indices = some ([], final) ∧ final.Halted := by
  apply (R.existsUnique_replay_iff true []).mpr
  exact (ownBit.firstHalting_iff_nil_of_halted (encBool true) [] true rfl).mpr rfl

open NondeterministicQueryMachine in
example (R : Routines ownBit id encBool (fun _ => 1)) {indices : List ℕ}
    {final : Cfg R.k Bool (Native.State R.SI R.SP R.SF) (encBool true)}
    (hr : Native.replayChoices R.I R.P R.F R.C (R.machine.initCfg (encBool true)) indices =
      some ([], final)) (hhalt : final.Halted) : final.output = [true] :=
  (R.replay_correct true hr hhalt).2

open NondeterministicQueryMachine in
/-- An already accepting source has exactly one accepting native occurrence at a sufficient clock,
corresponding to its empty first-halting trace. -/
example (R : Routines ownBit id encBool (fun _ => 1)) :
    ∃ fuel, (Native.countingMachine R.I R.P R.F R.C).acceptCount
      fuel (R.machine.initCfg (encBool true)) = 1 := by
  have hhalt : (ownBit.withInit true).HaltsWithin (encBool true) 0 := by
    intro choices hlength
    obtain rfl := List.length_eq_zero_iff.mp hlength
    rfl
  obtain ⟨fuel, hclock⟩ := R.exists_runsInTime true hhalt
  refine ⟨fuel, (R.acceptCount_eq_one_iff true hclock).mpr ?_⟩
  have hnil := fun bits => ownBit.firstHalting_iff_nil_of_halted (encBool true) bits true rfl
  exact ⟨[], ⟨(hnil []).mpr rfl, rfl⟩, fun bits h => (hnil bits).mp h.1⟩

open NondeterministicQueryMachine in
/-- Both selectors produce the same state transition at each of the two passes.
There are nevertheless four accepting occurrences at any sufficient native clock. -/
example (R : Routines twoPass (fun _ => 0) encBits (fun a => Nat.log2 a.length + 1))
    (input : List Bool) {fuel : ℕ} (hclock : R.machine.RunsInTime input fuel) :
    (Native.countingMachine R.I R.P R.F R.C).acceptCount fuel
      (R.machine.initCfg input) = 4 := by
  have hatTwo (bits : List Bool) (h : bits.length = 2) : twoPass.replay input bits 0 = 2 := by
    obtain ⟨b, c, rfl⟩ := List.length_eq_two.mp h
    rfl
  have hlive (bits : List Bool) (h : bits.length < 2) :
      twoPass.halted (twoPass.replay input bits 0) = false := by
    cases bits with
    | nil => rfl
    | cons b tail =>
      have hlen : tail.length = 0 := by simp only [List.length_cons] at h; omega
      obtain rfl := List.length_eq_zero_iff.mp hlen
      rfl
  have hset :
      {bits : List Bool | twoPass.FirstHalting input bits 0 ∧
        twoPass.accept (twoPass.replay input bits 0) = true} =
      {bits : List Bool | bits.length = 2} := by
    ext bits
    simp only [Set.mem_ofPred_eq, FirstHalting]
    constructor
    · rintro ⟨⟨hh, hp⟩, _⟩
      have hlo : 2 ≤ bits.length := by
        by_contra! h
        rw [hlive bits h] at hh
        cases hh
      have hhi : bits.length ≤ 2 := by
        by_contra! h
        have hs := hp 2 h
        rw [hatTwo _ (List.length_take_of_le hlo)] at hs
        cases hs
      exact le_antisymm hhi hlo
    · intro h
      rw [hatTwo bits h]
      refine ⟨⟨rfl, fun n hn => hlive _ ?_⟩, rfl⟩
      rw [List.length_take_of_le hn.le, ← h]
      exact hn
  have hcount := R.acceptCount_eq_encard_firstHalting input hclock
  rw [encBits_apply, hset, Cslib.BitString.encard_setOf_length_eq] at hcount
  exact_mod_cast hcount

end CslibFrontierTests.NondeterministicQueryMachineCompiler
