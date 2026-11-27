/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.Alternation.Savitch
import CslibFrontier.Computability.Complexity.Classes.Constructible
import CslibFrontier.Computability.Complexity.Classes.EXP
import CslibFrontier.Computability.Complexity.Classes.EXPSPACE.Separation
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Time
import CslibFrontier.Computability.Complexity.Classes.Space.Closure
import CslibFrontier.Computability.Complexity.Classes.Space.TQBF
import CslibFrontier.Computability.Machines.Turing.MultiTape.HeadCounters.Simulation
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-! Checked clients of the head-counter simulation of arbitrary machines: under the ever-nonblank
measure of Definition 4.1 in the 2007-01-08 draft of Arora and Barak (printed p. 76 / PDF p. 92),
every decider runs in constant space, so the draft's Theorems 3.2, 4.11 and 5.12 and its
Exercise 5 §6 fail for that measure (Theorem 4.3 is
`Cslib.Complexity.exists_notMem_E_fixed_support_decider`). Each client derives the refutation of
one printed statement from `Turing.MultiTapeTM.HeadCounter.exists_fixed_support_computes` and a
native separation. -/

set_option linter.privateModule false

namespace CslibFrontierTests.HeadCounterSimulation

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Filter

/-- Every natively decided problem has a decider whose only ever-nonblank work cells are its
origins. Under Definition 4.1 this puts the draft's `SPACE(g)` inside `SPACE(f)` for all
`f, g ≥ 1`, contrary to the strict inclusion of the draft's Theorem 3.2 (printed p. 66 /
PDF p. 82). -/
example {α : Type} {A : Set α} {enc : α ↪ List Bool} {t s : α → ℕ}
    (h : DecidableInTimeAndSpace A enc t s) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      (∀ a, tm.Computes (enc a) [indicator A a]) ∧
      ∀ input t i z, (tm.runFrom (tm.initCfg input) t).workTapes i z ≠ none → z = 0 := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  obtain ⟨State', hfin', tm', hcomp, hsupp⟩ := HeadCounter.exists_fixed_support_computes tm
  exact ⟨_, State', hfin', tm', fun a => hcomp _ _ (htm a).1, hsupp⟩

/-- A problem outside `PSPACE` has a fixed-support decider, so it lies in the draft's literal
`PSPACE`. -/
private theorem exists_notMem_PSPACE_fixed_support_decider :
    ∃ A : Set (List Bool), A ∉ PSPACE encBits ∧
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
        (∀ x, tm.Computes (encBits x) [indicator A x]) ∧
        ∀ input t i z, (tm.runFrom (tm.initCfg input) t).workTapes i z ≠ none → z = 0 := by
  obtain ⟨A, hA, hAP⟩ := Set.exists_of_ssubset PSPACE_ssubset_EXPSPACE
  obtain ⟨d, c₁, c₂, t, k, State, hfin, tm, htm⟩ := mem_EXPSPACE_iff.mp hA
  obtain ⟨State', hfin', tm', hcomp, hsupp⟩ := HeadCounter.exists_fixed_support_computes tm
  exact ⟨A, hAP, _, State', hfin', tm', fun x => hcomp _ _ (htm x).1, hsupp⟩

/-- The draft's Theorem 4.11 (printed p. 81 / PDF p. 97) fails under Definition 4.1: a problem in
the literal `PSPACE` does not reduce to TQBF in polynomial time, since native `PSPACE` contains
TQBF and is closed under these reductions. -/
example : ∃ A : Set (List Bool), ¬PolyTimeReducible encBits encQBF A TQBF ∧
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      (∀ x, tm.Computes (encBits x) [indicator A x]) ∧
      ∀ input t i z, (tm.runFrom (tm.initCfg input) t).workTapes i z ≠ none → z = 0 :=
  let ⟨A, hA, h⟩ := exists_notMem_PSPACE_fixed_support_decider
  ⟨A, fun hr => hA (hr.mem_PSPACE TQBF_pspaceComplete.1), h⟩

/-- The draft's Theorem 5.12 (printed p. 96 / PDF p. 112), `AP = PSPACE`, fails under
Definition 4.1: alternating polynomial time is native `PSPACE`, which misses a problem in the
literal `PSPACE`. -/
example : ∃ A : Set (List Bool), A ∉ AP encBits ∧
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      (∀ x, tm.Computes (encBits x) [indicator A x]) ∧
      ∀ input t i z, (tm.runFrom (tm.initCfg input) t).workTapes i z ≠ none → z = 0 :=
  let ⟨A, hA, h⟩ := exists_notMem_PSPACE_fixed_support_decider
  ⟨A, fun hAP => hA (AP_eq_PSPACE ▸ hAP), h⟩

/-- The draft's Exercise 5 §6 (printed p. 100 / PDF p. 116), `APSPACE = EXP`, fails under
Definition 4.1: the clocked diagonal with the doubly exponential clock `2 ^ 2 ^ n` is outside
`EXP`, yet it has a fixed-support decider, which is also an alternating machine in constant
ever-nonblank space. -/
example : ∃ A : Set (List Bool), A ∉ EXP encBits ∧
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      (∀ x, tm.Computes (encBits x) [indicator A x]) ∧
      ∀ input t i z, (tm.runFrom (tm.initCfg input) t).workTapes i z ≠ none → z = 0 := by
  refine ⟨{x | timeDiagonal (fun n => 2 ^ 2 ^ n) x = true}, fun h => ?_, ?_⟩
  · obtain ⟨d, hd⟩ := mem_EXP_iff.mp h
    refine setOf_timeDiagonal_notMem_DTIME (fun c => ?_) hd
    filter_upwards [PolynomiallyBounded.eventually_lt_two_pow (f := fun n => n ^ d + c + 1)
      (by fun_prop)] with n hn
    have hc : c + c ≤ 2 ^ (c + 1) := by
      rw [pow_succ 2 c]
      have := Nat.lt_two_pow_self (n := c)
      omega
    calc c * 2 ^ n ^ d + c ≤ (c + c) * 2 ^ n ^ d := by
          have := Nat.one_le_two_pow (n := n ^ d)
          nlinarith
      _ ≤ 2 ^ (c + 1) * 2 ^ n ^ d := Nat.mul_le_mul_right _ hc
      _ = 2 ^ (n ^ d + c + 1) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn.le
  · obtain ⟨c₁, c₂, s, k, State, hfin, tm, htm⟩ :=
      setOf_timeDiagonal_mem_DTIME timeConstructible_two_pow_two_pow
    obtain ⟨State', hfin', tm', hcomp, hsupp⟩ := HeadCounter.exists_fixed_support_computes tm
    exact ⟨_, State', hfin', tm', fun x => hcomp _ _ (htm x).1, hsupp⟩

end CslibFrontierTests.HeadCounterSimulation
