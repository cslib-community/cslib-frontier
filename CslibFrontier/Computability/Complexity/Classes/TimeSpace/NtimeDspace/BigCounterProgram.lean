/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ComplexityReuse
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram

/-!
# Counter programs with large registers

Complexitylib proves the five query-machine callback certificates for every
counter program, on every configuration, in space linear in the binary
registers (`Turing.CounterProgram.Simulation`). Its convenience theorem
`computableInLogSpace` additionally bounds the registers polynomially in the
input length. Here that bound is replaced by an arbitrary input-indexed budget
on the encoded registers, so a register may hold a buffer of many bits.
The compiled machine has simultaneous `2^(C*S)` time and `C*S` space.
-/

public section

namespace Cslib.Complexity.NtimeDspace.BigCounterProgram

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.CounterProgram

/-- The encoded configuration is bounded by a program constant plus the encoded
registers. -/
theorem length_encConfig_le (P : CounterProgram) {s : Config} (label : s.1 ≤ P.maxLabel) :
    (Simulation.encConfig s).length ≤
      2 * (encNat P.maxLabel).length + 1 + (encList encNat s.2).length := by
  have := length_encNat_mono label
  simp only [length_encPair]
  omega

/-- **Counter programs run in the space of their encoded registers.** If the
program halts on every encoded input, first after `time a` steps, with output
`encOut (f a)`, and the encoded registers stay below `c * S a` along the run,
where `S a` is at least logarithmic in the input length, then `f` is computable
in simultaneous time `2^(C * S a)` and space `C * S a`. -/
theorem simultaneous_bounds (P : CounterProgram) {α β : Type} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (time : α → ℕ)
    (halts : ∀ a, P.halted (P.run (enc a) (time a)) = true)
    (firstHalt : ∀ a, ∀ t < time a, P.halted (P.run (enc a) t) = false)
    (output : ∀ a, encOut (f a) = P.toQueryMachine.output (enc a) (time a))
    (budget : α → ℕ) (logarithmic : ∀ a, (enc a).length.log2 + 1 ≤ budget a)
    (registers : ∃ c, ∀ a, ∀ t ≤ time a,
      (encList encNat (P.run (enc a) t).2).length ≤ c * budget a) :
    ∃ C, ComputableInTimeAndSpace f enc encOut
      (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  obtain ⟨c, hc⟩ := registers
  refine ComplexityReuse.query_simultaneous_bounds (encState := Simulation.encConfig)
    P.toQueryMachine
    (Simulation.query_inSpace (P := P))
    (Simulation.exec_inSpace (P := P))
    (Simulation.emitted_inSpace (P := P))
    (Simulation.halted_inSpace (P := P))
    (Simulation.finish_inSpace (P := P))
    time halts firstHalt output budget logarithmic
    ⟨2 * (encNat P.maxLabel).length + 1 + c, fun a t ht => ?_⟩
  have positive : 1 ≤ budget a := (Nat.le_add_left _ _).trans (logarithmic a)
  calc (Simulation.encConfig (P.toQueryMachine.run (enc a) t)).length
      ≤ 2 * (encNat P.maxLabel).length + 1 + (encList encNat (P.run (enc a) t).2).length :=
        length_encConfig_le P (P.run_fst_le _ t)
    _ ≤ (2 * (encNat P.maxLabel).length + 1) * budget a + c * budget a := by
        have := hc a t ht
        nlinarith
    _ = _ := by ring

/-- The reachability form: the program reaches a halting instruction with the
right output through running configurations whose encoded registers stay below
`c * S a`. -/
theorem simultaneous_bounds_of_reaches (P : CounterProgram) {α β : Type} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (budget : α → ℕ) (c : ℕ)
    (logarithmic : ∀ a, (enc a).length.log2 + 1 ≤ budget a)
    (h : ∀ a, ∃ s, P.Reaches (enc a)
        (fun s => (P.instr s.1).IsStep ∧ (encList encNat s.2).length ≤ c * budget a) P.init s ∧
      P.instr s.1 = .halt (encOut (f a)) ∧ (encList encNat s.2).length ≤ c * budget a) :
    ∃ C, ComputableInTimeAndSpace f enc encOut
      (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  choose s hs using h
  choose t ht hpre using fun a => (hs a).1
  have hhalt (a : α) := (hs a).2.1
  have hreg (a : α) := (hs a).2.2
  have hrun (a : α) (u : ℕ) : P.run (enc a) u = (P.step (enc a))^[u] P.init := rfl
  have hstep (a : α) {u : ℕ} (hu : u < t a) : P.halted (P.run (enc a) u) = false := by
    have := (hpre a u hu).1
    rw [hrun, halted]
    revert this
    cases P.instr ((P.step (enc a))^[u] P.init).1 <;> simp [Instr.IsStep, Instr.halts]
  refine simultaneous_bounds P t (fun a => ?_) (fun a u hu => hstep a hu) (fun a => ?_)
    budget logarithmic ⟨c, fun a u hu => ?_⟩
  · rw [hrun, ht, halted, hhalt]
    rfl
  · rw [P.toQueryMachine.output_eq_of_not_halted _ (fun i hi => hstep a hi)]
    have hnil : ((List.range (t a)).map fun i => P.toQueryMachine.emit
        (P.toQueryMachine.run (enc a) i,
          P.toQueryMachine.read (enc a) (P.toQueryMachine.run (enc a) i))).flatten = [] := by
      simp only [List.flatten_eq_nil_iff, List.mem_map, List.mem_range]
      rintro _ ⟨i, hi, rfl⟩
      have := (hpre a i hi).1
      simp only [toQueryMachine, emitted]
      revert this
      change (P.instr ((P.step (enc a))^[i] P.init).1).IsStep →
        (P.instr ((P.step (enc a))^[i] P.init).1).emitted = []
      cases P.instr ((P.step (enc a))^[i] P.init).1 <;> simp [Instr.IsStep, Instr.emitted]
    rw [hnil, List.nil_append]
    change _ = P.finish ((P.step (enc a))^[t a] P.init)
    rw [ht, finish, hhalt]
    rfl
  · rcases lt_or_eq_of_le hu with hlt | rfl
    · exact (hpre a u hlt).2
    · rw [hrun, ht]
      exact hreg a

end Cslib.Complexity.NtimeDspace.BigCounterProgram
