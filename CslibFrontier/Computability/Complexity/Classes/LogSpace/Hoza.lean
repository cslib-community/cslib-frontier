/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Counting
import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenSourceLoop.Scheduler

/-!
# Hoza's equality of nondeterministic and unambiguous logarithmic space

For each fixed native nondeterministic logspace machine, the compact configuration instance
reduces acceptance on the original word to layered reachability. The Justesen scheduler
enumerates weights in seed order, tests min-isolation by double counting on the unweighted
subdivision, and returns the reachability verdict for the least passing seed. The compiler
realizes this scheduler as one finite counting machine in logarithmic workspace with a uniform
polynomial clock. Exact native occurrence counting gives one accepting branch on members and
zero on nonmembers.

Hoza's Theorem 1.1 [Hoza2026NLUL] states `NL = UL` for languages. Here both classes are the
library's native multi-tape classes on inputs represented by any injective encoding into binary
words. The machine and workspace coefficient are fixed for the language. Space is measured
in visited work-tape cells on every computation prefix, with read-only input and uncharged
output. The counting formulation of `UL` counts distinct transition occurrences, and its
clock must suffice for all branches.

## Main results

* `Cslib.Complexity.NL_subset_UL`: the compiled Justesen scheduler gives the forward inclusion.
* `Cslib.Complexity.NL_eq_UL`: Hoza's class equality for every injective binary encoding.
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.NondeterministicQueryMachine

open Classical in
/-- Every native nondeterministic logspace decider has a native counting decider with exactly
one accepting occurrence on members and zero on nonmembers, in the same encoding. -/
theorem NL_subset_UL {α : Type} {enc : α ↪ List Bool} : NL enc ⊆ UL enc := by
  rintro A ⟨k, State, hfinite, ntm, c, hdecides⟩
  let : Finite State := hfinite
  let : Fintype State := Fintype.ofFinite State
  obtain ⟨R, L, d, hresource⟩ := STCON.configurationJustesenSeedScheduler_exists_routines ntm c
  let : Finite R.SI := R.finiteI
  let : ∀ b, Finite (R.SP b) := R.finiteP
  let : Finite R.SF := R.finiteF
  let M := Native.countingMachine R.I R.P R.F R.C
  let count (a : α) : ℕ := if a ∈ A then 1 else 0
  refine ⟨count, ⟨R.k, _, inferInstance, M, L, fun a => ?_⟩, ?_, ?_⟩
  · let w := enc a
    let clock := polyClock d w.length
    have ⟨hspace, hclock⟩ := hresource w
    have haccept : STCON.configurationInstance ntm c w ∈ STCON ↔ a ∈ A :=
      (STCON.configurationInstance_mem_iff ntm c (hdecides.1 a).1).trans (hdecides.1 a).2.symm
    have hcount := STCON.configurationJustesenSeedScheduler_acceptCount ntm c R w hclock
    have hmachine : M.toNTM = R.machine := Native.toNTM_countingMachine R.I R.P R.F R.C
    have hcfg : Cfg.init M.initial w = R.machine.initCfg w :=
      congrArg (fun machine => machine.initCfg w) hmachine
    refine ⟨hmachine.symm ▸ hspace, clock, ?_, ?_⟩
    · rw [hcfg]
      exact Native.countingMachine_haltsWithin R.I R.P R.F R.C hclock
    · rw [hcfg]
      simpa only [count, haccept, M, clock] using hcount.symm
  · intro a
    by_cases ha : a ∈ A <;> simp [count, ha]
  · intro a
    by_cases ha : a ∈ A <;> simp [count, ha]

/-- Hoza's `NL = UL` [Hoza2026NLUL], Theorem 1.1, for native language classes in any
injective binary input encoding. -/
theorem NL_eq_UL {α : Type} (enc : α ↪ List Bool) : NL enc = UL enc :=
  le_antisymm NL_subset_UL UL_subset_NL

end Cslib.Complexity
