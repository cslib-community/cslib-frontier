/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.IntervalCountNative

open Turing.MultiTapeATM.IntervalCountGame Turing.MultiTapeATM.QuantifiedWord

/-- The empty range contains zero ones, including when the implicit predicate is constant true. -/
example : plays (fun xs => verdict (fun i : ℕ => decide (i < 0) && true)
    (route 0 0 false xs)) [] (flags 0) := (plays_flags (fun _ => true) 0 0 false).2 (by decide)

/-- A non-power-of-two range pads the final leaf with a zero. Its two real ones set bit one. -/
example : plays (fun xs => verdict (fun i : ℕ => decide (i < 3) && decide (i ≠ 1))
    (route 3 1 true xs)) [] (flags 3) := (plays_flags (fun i => decide (i ≠ 1)) 3 1 true).2
      (by decide)

/-- The same prefix rejects the opposite sign. -/
example : ¬ plays (fun xs => verdict (fun i : ℕ => decide (i < 3) && decide (i ≠ 1))
    (route 3 1 false xs)) [] (flags 3) := fun h =>
  (by decide : ¬ (∑ i ∈ Finset.range 3, (decide (i ≠ 1)).toNat).testBit 1 = false)
    ((plays_flags (fun i => decide (i ≠ 1)) 3 1 false).1 h)

/-- A claimed left subtotal above the proposed whole sum rejects even on a left-side choice. -/
example : walk 2 1 0 1 [false, true, false] = none := by decide
