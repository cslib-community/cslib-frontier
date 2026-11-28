/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
import CslibFrontier.Computability.Complexity.Classes.EXP.Separation
import CslibFrontier.Computability.Machines.Turing.MultiTape.HeadCounters.Simulation

/-!
# Space counted by ever-nonblank cells

The 2007-01-08 draft of [AroraBarak09] measures space by the work-tape locations that are at some
point nonblank (Definition 4.1, printed p. 76 / PDF p. 92). Under that measure every decidable
problem is decided in constant space: `Turing.MultiTapeTM.HeadCounter.exists_fixed_support_computes`
simulates any machine by one whose only ever-nonblank work cells are the origins of its tapes,
storing the simulated tapes in head positions. In particular the draft's Theorem 4.3,
`SPACE(S(n)) ⊆ DTIME(2^O(S(n)))`, fails under its own Definition 4.1. With visited cells counted,
as in `Cslib.Complexity.DSPACE`, the inclusion holds
(`Cslib.Complexity.exists_mem_DTIME_of_mem_NSPACE_of_log2_le`).

## Main results

* `Cslib.Complexity.exists_notMem_E_fixed_support_decider`: some problem outside `E` has a decider
  whose only ever-nonblank work cells are its origins; a counterexample to the draft's Theorem 4.3.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-- **Counterexample to Theorem 4.3 of the 2007-01-08 draft of [AroraBarak09] under the draft's
Definition 4.1.** Some problem outside `E` is decided by a finite-state binary machine whose only
work cells that are ever nonblank, at every time and on every input, are the origins of its tapes.

Definition 4.1 (printed p. 76 / PDF p. 92) puts a problem in `SPACE(s)` when some machine deciding
it has, on every input `x`, at most `c * s |x|` locations "that are at some point non-blank during
M's execution", input-tape locations excepted. This decider has at most `k` such work-tape
locations, and in the draft's model at most two more on its output tape (the start marker and the
answer bit), so the problem lies in the draft's `SPACE(n + 1)`. The draft's machines may cross
blank cells without writing, rewriting a blank as blank (printed pp. 15–17 / PDF pp. 31–33), as
this decider does. Since `n + 1` is space-constructible and exceeds `log n`, Theorem 4.3 (printed
p. 76 / PDF p. 92) would put the problem in `DTIME(2^O(n + 1))`, which is contained in `E`. -/
theorem exists_notMem_E_fixed_support_decider :
    ∃ A : Set (List Bool), A ∉ E encBits ∧
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
        (∀ x, tm.Computes (encBits x) [indicator A x]) ∧
        ∀ input t i z, (tm.runFrom (tm.initCfg input) t).workTapes i z ≠ none → z = 0 := by
  obtain ⟨A, hA, hAE⟩ := Set.exists_of_ssubset E_ssubset_EXP
  obtain ⟨d, c₁, c₂, s, k, State, hfin, tm, htm⟩ := mem_EXP_iff.mp hA
  obtain ⟨State', hfin', tm', hcomp, hsupp⟩ := HeadCounter.exists_fixed_support_computes tm
  exact ⟨A, hAE, _, State', hfin', tm', fun x => hcomp _ _ (htm x).1, hsupp⟩

end Cslib.Complexity
