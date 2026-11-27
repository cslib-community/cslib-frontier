/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module

import CslibFrontier.Computability.Automata.MPDA.SeparationAutomaton

/-! Clients of the automaton recognizing `L_bh` under module encapsulation. It accepts the words
`aᵐ bᵐ (c d)ᵐ` and rejects `a c`, which is not in `L_bh`. -/

namespace CslibFrontierTests.MPDA.SeparationAutomaton

open Cslib Cslib.Automata Cslib.Automata.MPDA Cslib.Automata.MPDA.HoleSeparation

example (m : ℕ) : word m ∈ Acceptor.language automaton :=
  language_automaton ▸ word_mem_language m

/-- `a c` is not in `L_bh`: a nonempty word of `L_bh` starts with `a b` or `a a`. -/
example : [Letter.a, .c] ∉ Acceptor.language automaton := by
  rw [language_automaton]
  rintro ⟨n, gs, hlen, -, h⟩
  rcases n with _ | _ | n
  · obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp at h
  · simp at h
  · simp [List.replicate_succ] at h

end CslibFrontierTests.MPDA.SeparationAutomaton
