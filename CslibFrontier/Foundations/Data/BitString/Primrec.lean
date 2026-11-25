/-
Copyright (c) 2026 Matthew Doty, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Enumeration
public import Mathlib.Computability.Primrec.List

/-!
# Primitive recursiveness of bit-string enumeration

## Main results

* `Cslib.BitString.primrec_enumList`: enumerating all `n`-bit strings via `Cslib.BitString.enumList`
  is primitive recursive.
-/

public section

namespace Cslib.BitString

/-- Enumerating all `n`-bit strings via `Cslib.BitString.enumList` is primitive recursive. -/
theorem primrec_enumList : Primrec enumList := by
  have hh : Primrec₂ fun (_ : ℕ) (IH : List (List Bool)) =>
      IH.flatMap fun word => [false :: word, true :: word] := by
    have hcons : Primrec₂ fun (_ : ℕ × List (List Bool)) (word : List Bool) =>
        [false :: word, true :: word] :=
      Primrec₂.mk <| Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
          (Primrec.const []))
    exact Primrec₂.mk <| Primrec.list_flatMap Primrec.snd hcons
  refine (Primrec.nat_rec₁ [[]] hh).of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ m ih => rw [enumList_succ, ← ih]

end Cslib.BitString
