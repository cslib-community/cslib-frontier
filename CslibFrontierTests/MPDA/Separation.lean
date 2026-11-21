/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module

import CslibFrontier.Computability.Automata.MPDA.Separation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Clients of the separation of hole-bounded from scope-bounded languages under module
encapsulation. A visibly MPDA has a complete run on `a b c d = word 1 ∈ L_bh`, so the hypotheses
of `holeBounded_two` and `not_scopeBounded` can hold together: that run is `2`-hole-bounded but not
`1`-scope-bounded. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MPDA.Separation

open Cslib Cslib.Automata Cslib.Automata.MPDA Cslib.Automata.MPDA.HoleSeparation

/-- One control state, and every transition whose operation has the kind of its letter. -/
private def visible : MPDA 2 Unit Letter Unit where
  Tr _ μ _ := μ.2.kind = kind μ.1
  start := {()}
  accept := {()}

private theorem visible_isVisibly : visible.IsVisibly kind := fun _ _ _ _ h => h

/-- The run on `a b c d`: push on stacks `0` and `1`, then pop from them. -/
private def abcd : List (Letter × Op 2 Unit) :=
  [(.a, .push 0 ()), (.b, .push 1 ()), (.c, .pop 0 ()), (.d, .pop 1 ())]

private theorem abcd_run :
    visible.configLTS.MTr ⟨(), Stacks.empty⟩ abcd ⟨(), Stacks.empty⟩ := by
  refine .stepL (s2 := ⟨(), ![[()], []]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[()], [()]]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[], [()]]⟩) ?_ <|
    .stepL ?_ .refl <;>
  refine configLTS_tr.mpr ⟨rfl, ?_⟩ <;>
  simp only [Op.apply_push, Op.apply_pop] <;>
  funext k <;> fin_cases k <;> simp [Stacks.empty]

private theorem abcd_word : abcd.map Prod.fst = word 1 := rfl

/-- The run is accepting, on a word of `L_bh`. -/
example : Acceptor.Accepts visible (word 1) :=
  ⟨(), rfl, (), rfl, abcd, abcd_word, abcd_run⟩

example : word 1 ∈ language := word_mem_language 1

/-- The run is `2`-hole-bounded. -/
example : HoleBounded 2 abcd :=
  holeBounded_two visible_isVisibly abcd_run (abcd_word ▸ word_mem_language 1)

/-- The run is not `1`-scope-bounded: the first `a` is popped two context switches later. -/
example : ¬ScopeBounded 1 abcd :=
  not_scopeBounded visible_isVisibly abcd_run abcd_word (by decide)

end CslibFrontierTests.MPDA.Separation
