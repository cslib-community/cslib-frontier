/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Basic

/-!
# The elements an assignment chooses

Pseudo-Boolean encodings of problems over `Fin n` (the vertices of a graph, the items of a
knapsack) give element `v` the variable `v.val`. An assignment `σ : ℕ → Bool` then chooses the
elements whose variable it sets true, `Cslib.Logic.PL.VeriPB.chosen n σ`, and every set of elements
is chosen by some assignment (`Cslib.Logic.PL.VeriPB.exists_chosen_eq`). The correctness theorems
of the encodings are stated through it.

## Main definitions

* `Cslib.Logic.PL.VeriPB.chosen`: the elements an assignment chooses.

## Main results

* `Cslib.Logic.PL.VeriPB.mem_chosen`, `Cslib.Logic.PL.VeriPB.exists_chosen_eq`.
-/

@[expose] public section

namespace Cslib.Logic.PL.VeriPB

variable {n : ℕ}

/-- The elements of `Fin n` that an assignment chooses: those whose variable is true. -/
def chosen (n : ℕ) (σ : ℕ → Bool) : Finset (Fin n) := Finset.univ.filter fun v => σ v.val

@[simp] theorem mem_chosen {σ : ℕ → Bool} {v : Fin n} : v ∈ chosen n σ ↔ σ v.val = true := by
  simp [chosen]

/-- **Every set of elements is chosen** by some assignment. -/
theorem exists_chosen_eq (s : Finset (Fin n)) : ∃ σ, chosen n σ = s :=
  ⟨fun v => decide (∃ h : v < n, (⟨v, h⟩ : Fin n) ∈ s), by ext v; simp⟩

end Cslib.Logic.PL.VeriPB
