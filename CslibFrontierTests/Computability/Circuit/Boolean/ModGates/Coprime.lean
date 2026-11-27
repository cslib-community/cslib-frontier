/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.ModGates.Coprime
import Mathlib.Tactic.FinCases

set_option linter.privateModule false

open Cslib.Circuits.Boolean
open scoped BigOperators

example {m : ℕ} (x : Fin m → Bool) :
    modGate 6 m x = (modGate 2 m x || modGate 3 m x) :=
  modGate_coprime_factors (a := 2) (b := 3) (by decide) x

example {m : ℕ} (x : Fin m → Bool) :
    modGate 10 m x = (modGate 2 m x || modGate 5 m x) :=
  modGate_coprime_factors (a := 2) (b := 5) (by decide) x

example {m : ℕ} (x : Fin m → Bool) :
    modGate 15 m x = (modGate 3 m x || modGate 5 m x) :=
  modGate_coprime_factors (a := 3) (b := 5) (by decide) x

example {m : ℕ} (x : Fin m → Bool) : modGate 1 m x = false := by
  have h := modGate_prod_eq_true_iff (∅ : Finset ℕ) id (by simp) x
  have hfalse : ¬ modGate 1 m x = true := by simpa using h
  exact Bool.eq_false_iff.mpr hfalse

-- All three factors participate. The same factor tests reject a multiple of 30.
example {m : ℕ} (x : Fin m → Bool) :
    modGate 30 m x = true ↔ ∃ i : Fin 3, modGate (![2, 3, 5] i) m x = true := by
  have pairwise : Set.Pairwise (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3))
      (fun i j => (![2, 3, 5] i).Coprime (![2, 3, 5] j)) := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> first | contradiction | decide
  have eq : ∏ i : Fin 3, (![2, 3, 5] i) = 30 := by decide
  simpa only [eq, Finset.mem_univ, true_and] using
    modGate_prod_eq_true_iff Finset.univ ![2, 3, 5] pairwise x

example : modGate 30 30 (fun _ => true) = false := by decide
example : modGate 30 15 (fun _ => true) = true := by decide
