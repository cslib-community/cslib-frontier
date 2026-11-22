/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Data.Code.LowDegreeExtension

/-! Checked instance of the individual-degree low-degree extension
(`Cslib.Code.exists_degreeOf_le_eval_eq_lowDegreeExtension`, Goldreich, Exercise 7.12): the
conjunction of two bits, with `H = {0, 1} ⊆ ZMod 3`, is the restriction of a polynomial of degree
at most one in each variable. -/

set_option linter.privateModule false

open Cslib.Code

/-- The bits as the elements `0` and `1` of `ZMod 3`. -/
private def boolEmb : Bool ↪ ZMod 3 := ⟨fun b => if b then 1 else 0, by decide⟩

example : ∃ P : MvPolynomial (Fin 2) (ZMod 3), (∀ i, P.degreeOf i ≤ 1) ∧
    ∀ u : Fin 2 → Bool, MvPolynomial.eval (fun i => boolEmb (u i)) P =
      if u 0 && u 1 then 1 else 0 := by
  obtain ⟨P, hdeg, -, hP⟩ :=
    exists_degreeOf_le_eval_eq_lowDegreeExtension boolEmb
      fun u : Fin 2 → Bool => if u 0 && u 1 then 1 else 0
  exact ⟨P, fun i => by simpa using hdeg i, hP⟩
