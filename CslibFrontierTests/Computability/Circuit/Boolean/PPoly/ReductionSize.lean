/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.PPoly.ReductionSize

set_option linter.privateModule false

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

-- Wiring the input unchanged costs no gates and preserves the target's exact bound.
example {A : Language Bool} {s : ℕ → ℕ} (hA : A ∈ SIZE s) :
    A ∈ SIZE (fun n => 0 + s n) :=
  fixedWidth_size_of_reduction id (fun _ => 0) s (fun _ x => x)
    (fun n => by
      have h := complexity_wiring (I := interpretation) (id : Fin n → Fin n)
      simpa only [Function.comp_id, Nat.le_zero] using h)
    (fun _ _ => Iff.rfl) hA

-- The leading data bits are preserved independently of the trailing flags.
example : List.ofFn (readPaddedPrefix (m := 2) (1 : Fin 3) ![true, false, false, true, false]) =
    [true] := by decide
example : List.ofFn (readPaddedPrefix (m := 2) (0 : Fin 3) ![true, true, true, false, false]) =
    [] := by decide
