/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module

import CslibFrontier.Computability.Automata.MPDA.PhaseSeparation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Clients of the incomparability of hole-bounded and phase-bounded languages under module
encapsulation. A visibly MPDA has complete runs on `(a b)² c² d² ∈ L'` and on
`a b c d ∈ L_bh`, so the hypotheses of `phaseBounded_two`, `not_holeBounded` and
`not_phaseBounded` can hold: the first run is `2`-phase-bounded but not `1`-hole-bounded, and the
second is not `1`-phase-bounded. With zero stacks, a single no-op step is one phase. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MPDA.PhaseSeparation

open Cslib Cslib.Automata Cslib.Automata.MPDA Cslib.Automata.MPDA.HoleSeparation

/-- One control state, and every transition whose operation has the kind of its letter. -/
private def visible : MPDA 2 Unit Letter Unit where
  Tr _ μ _ := μ.2.kind = kind μ.1
  start := {()}
  accept := {()}

private theorem visible_isVisibly : visible.IsVisibly kind := fun _ _ _ _ h => h

/-- The run on `(a b)² c² d²`. -/
private def abab : List (Letter × Op 2 Unit) :=
  [(.a, .push 0 ()), (.b, .push 1 ()), (.a, .push 0 ()), (.b, .push 1 ()),
    (.c, .pop 0 ()), (.c, .pop 0 ()), (.d, .pop 1 ()), (.d, .pop 1 ())]

private theorem abab_run :
    visible.configLTS.MTr ⟨(), Stacks.empty⟩ abab ⟨(), Stacks.empty⟩ := by
  refine .stepL (s2 := ⟨(), ![[()], []]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[()], [()]]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[(), ()], [()]]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[(), ()], [(), ()]]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[()], [(), ()]]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[], [(), ()]]⟩) ?_ <|
    .stepL (s2 := ⟨(), ![[], [()]]⟩) ?_ <|
    .stepL ?_ .refl <;>
  refine configLTS_tr.mpr ⟨rfl, ?_⟩ <;>
  simp only [Op.apply_push, Op.apply_pop] <;>
  funext k <;> fin_cases k <;> simp [Stacks.empty]

private theorem abab_word : abab.map Prod.fst = phaseWord 2 := rfl

/-- The run on `(a b)² c² d²` is accepting. -/
example : Acceptor.Accepts visible (phaseWord 2) :=
  ⟨(), rfl, (), rfl, abab, abab_word, abab_run⟩

/-- It is `2`-phase-bounded. -/
example : PhaseBounded 2 abab :=
  phaseBounded_two visible_isVisibly abab_run ⟨2, abab_word⟩

/-- It is not `1`-hole-bounded: after `(a b)²`, both `a`s are first pending pushes of holes. -/
example : ¬HoleBounded 1 abab :=
  not_holeBounded visible_isVisibly abab_run abab_word (by decide)

/-- The run on `a b c d ∈ L_bh`. -/
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

/-- The run on `a b c d` is not `1`-phase-bounded: it pops from both stacks. -/
example : ¬PhaseBounded 1 abcd :=
  not_phaseBounded visible_isVisibly abcd_run (m := 1) rfl (by decide)

/-- With zero stacks, a single no-op step is one phase: a sequence without pops is a phase. -/
example : PhaseBounded 1 [((), (.nop : Op 0 Unit))] :=
  ⟨[[((), .nop)]], le_rfl, rfl, by simp [IsPhase]⟩

/-- The automaton for `L'` accepts `(a b)ⁿ cⁿ dⁿ`. -/
example (n : ℕ) : phaseWord n ∈ Acceptor.language phaseAutomaton :=
  language_phaseAutomaton ▸ ⟨n, rfl⟩

/-- It rejects `a b c`, which has fewer `d`s than `c`s. -/
example : [Letter.a, .b, .c] ∉ Acceptor.language phaseAutomaton := by
  rw [language_phaseAutomaton]
  rintro ⟨n, h⟩
  have := congrArg List.length h
  simp [phaseWord] at this
  omega

end CslibFrontierTests.MPDA.PhaseSeparation
