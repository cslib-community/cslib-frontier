/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Charged native trial division

This is a finite instruction program, not an invocation of Lean's primality decision procedure.
The Chan–He prime table will call it only on candidates at least two.

## Main definitions

* `PrimeTrial.program`: trial divisors from two up to the candidate.

## Main results

* `PrimeTrial.exec`: native trial division with an explicit linear instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PrimeTrial

open Cslib.WordRAM

/-- Candidate, preserved. -/
abbrev arg : Fin 6 := 0
/-- Current trial divisor. -/
abbrev divisor : Fin 6 := 1
/-- Primality flag. -/
abbrev flag : Fin 6 := 2
/-- Remainder scratch. -/
abbrev remainder : Fin 6 := 3
/-- Constant one. -/
abbrev one : Fin 6 := 4
/-- Constant zero. -/
abbrev zero : Fin 6 := 5

/-- Test one trial divisor and advance. The conditional also charges its control instructions. -/
def body : Code .standard 6 := ram[
  remainder ← arg % divisor;
  if remainder = zero then [ flag ← zero ] else [ flag ← flag ];
  divisor ← divisor + one ]

/-- Initialize and test every divisor strictly between one and the candidate. -/
def program : Code .standard 6 :=
  .seq (ram[ divisor ← #2; flag ← #1; one ← #1; zero ← #0 ])
    (.loop (.lt divisor arg) body)

private def Good (p k : ℕ) : Prop := ∀ d, 2 ≤ d → d < k → p % d ≠ 0

private theorem good_succ (p k : ℕ) (hk : 2 ≤ k) :
    Good p (k + 1) ↔ Good p k ∧ p % k ≠ 0 := by
  constructor
  · exact fun h => ⟨fun d hd hdk => h d hd (by omega), h k hk (by omega)⟩
  · rintro ⟨h, hmod⟩ d hd hdk
    rcases eq_or_ne d k with rfl | hne
    · exact hmod
    · exact h d hd (by omega)

/-- Test a candidate at least two in at most `7(p-2)+6` native instructions.
All divisors are actual register values; the native remainder instruction is charged. -/
theorem exec {w : ℕ} (x : Data 6) (hp : 2 ≤ x.regs arg)
    (hfit : Fits w (x.regs arg + 2)) :
    ∃ y, ExecWithin w program x y (7 * (x.regs arg - 2) + 6) ∧
      y.regs flag = (if (x.regs arg).Prime then 1 else 0) ∧
      y.regs arg = x.regs arg ∧ y.mem = x.mem := by
  classical
  let p := x.regs arg
  unfold program
  wram_exec
  let P (j : ℕ) (y : Data 6) : Prop := y.regs arg = p ∧ y.regs one = 1 ∧
    y.regs zero = 0 ∧ 2 ≤ j ∧ y.regs flag = (if Good p j then 1 else 0) ∧ y.mem = x.mem
  refine WP.of_spec
    (ExecWithin.loop_count (N := p) (T := 5) P (fun _ hy => hy.1) ?_ ?_ ?_) ?_
  · rintro y ⟨ha, ho, hz, hd, hf, hm⟩ hlt
    have hg := good_succ p (y.regs divisor) hd
    unfold body
    wram_exec [ha, ho, hz]
    · have hng : ¬Good p (y.regs divisor + 1) := fun h => (hg.mp h).2 hc
      dsimp only [P]
      wram_simp [ha, ho, hz, hm, hng]
      omega
    · have hg' : Good p (y.regs divisor + 1) ↔ Good p (y.regs divisor) := by tauto
      dsimp only [P]
      wram_simp [ha, ho, hz, hm, hf, hg']
      omega
  · wram_simp; omega
  · dsimp only [P, p]; wram_simp [show Good (x.regs arg) 2 by intro _ _ _; omega]
  · rintro y ⟨⟨ha, _, _, _, hf, hm⟩, _⟩
    have hprime : Good p p ↔ p.Prime := by
      rw [Nat.prime_def_lt']
      exact ⟨fun h => ⟨hp, fun d hd hdp hdiv => h d hd hdp (Nat.mod_eq_zero_of_dvd hdiv)⟩,
        fun ⟨_, h⟩ d hd hdp hzero => h d hd hdp (Nat.dvd_of_mod_eq_zero hzero)⟩
    exact ⟨by wram_simp; dsimp only [p]; omega, by simpa only [hprime] using hf, ha, hm⟩

end Cslib.Algorithms.WordRAM.PrimeTrial
