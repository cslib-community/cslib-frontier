/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.DPDA.Basic

/-!
# Deterministic context-free languages

`Cslib.Language.IsDeterministicContextFree` is the DCFL predicate. A language over a finite
alphabet is deterministic context-free if a deterministic pushdown automaton with finite
control and stack alphabet accepts it by final state. See the class studied by
[Ginsburg and Greibach][GinsburgGreibach1966] and the final-state convention in
[Hopcroft et al., Section 6.4][Hopcroft2006].
-/

public section

namespace Cslib.Language

open Automata

/-- The class DCFL of languages recognized by finite deterministic pushdown automata. -/
@[expose] def IsDeterministicContextFree {Symbol : Type*} (L : Language Symbol) : Prop :=
  Finite Symbol ∧
    ∃ (State Γ : Type) (_ : Finite State) (_ : Finite Γ) (M : DPDA State Symbol Γ),
      Acceptor.language M = L

end Cslib.Language
