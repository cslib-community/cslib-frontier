/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.RandomizedReduction

/-! Checked instances of randomized polynomial-time reductions (`Cslib.Complexity.BPReducible`,
Arora–Barak Definition 7.19): the identity map is a randomized reduction from `ThreeSAT` to itself,
so `ThreeSAT ∈ BP·NP` in the sense of Definition 7.20; no randomized reduction maps every instance
into the empty language when the source language contains every instance; and the exercise
endpoints of Arora–Barak 7.6 and 8.5 are stated for an arbitrary encoding. -/

set_option linter.privateModule false

namespace CslibFrontierTests.RandomizedReduction

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- The identity map, ignoring its random string, reduces `ThreeSAT` to itself. -/
example : BPReducible encCNF encCNF ThreeSAT ThreeSAT := by
  classical
  refine bpReducible_iff.2 ⟨0, Prod.fst, ComputableInPolyTime.fst _ _, fun a => ?_⟩
  by_cases ha : a ∈ ThreeSAT <;> simp [ha, BoundedErrorAt]

/-- A randomized reduction must be right with probability `2 / 3`, so nothing reduces a nonempty
language containing every instance to the empty language. -/
example {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) (a : α) :
    ¬ BPReducible encA encB (Set.univ : Set α) (∅ : Set β) := by
  rintro ⟨R, -, h⟩
  have := h a
  simp only [Set.mem_empty_iff_false, Set.mem_univ, iff_true, Set.ofPred_false] at this
  simp at this
  norm_num at this

example {α : Type} (enc : α ↪ List Bool) :
    AMk enc 2 = {L : Set α | BPReducible enc encCNF L ThreeSAT} :=
  AMk_two_eq_setOf_bpReducible_ThreeSAT

example {α : Type} (enc : α ↪ List Bool) (h : BPReducible encCNF encCNF ThreeSATᶜ ThreeSAT) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_bpReducible_compl_ThreeSAT h

end CslibFrontierTests.RandomizedReduction
