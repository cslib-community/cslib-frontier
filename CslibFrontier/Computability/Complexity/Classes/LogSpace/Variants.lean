/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.USTCON
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Basic
public import CslibFrontier.Foundations.Computability.ContextFreeGrammar

/-!
# Time and space variants and logspace closure of context-free languages

`LIN` uses deterministic linear multitape time. `LOGLOG` uses a two-way read-only input
and doubly logarithmic deterministic workspace. `SC` imposes its polynomial time and
polylogarithmic space bounds on a single decider. `LOGCFL` reduces to a context-free
bit language, and `coSL` uses the complement of a problem in `SL`.

## References

* [Complexity Zoo, L](https://complexityzoo.net/Complexity_Zoo:L)
* [Complexity Zoo, S](https://complexityzoo.net/Complexity_Zoo:S)
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- Linear deterministic multitape time, measured on the encoded input. -/
def LIN (enc : α ↪ List Bool) : Set (Set α) := DTIME enc id

/-- Deterministic doubly logarithmic workspace with a two-way read-only input tape. -/
def LOGLOG (enc : α ↪ List Bool) : Set (Set α) := DSPACE enc (Nat.log2 ∘ Nat.log2)

/-- Steve's class, polynomial time and polylogarithmic workspace on the same machine. -/
def SC (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ d e : ℕ, A ∈ TISP enc (fun n => (n + 1) ^ d) (fun n => (Nat.log2 n + 1) ^ e)}

/-- Problems logspace many-one reducible to a context-free language over bits. -/
def LOGCFL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ B : Language Bool, B.IsContextFree ∧ LogSpaceReducible enc encBits A B}

/-- Complements of the problems in symmetric logarithmic space. -/
def coSL (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ SL enc}

/-- Symmetric logspace is closed under complement. -/
theorem coSL_eq_SL (enc : α ↪ List Bool) : coSL enc = SL enc :=
  Set.ext fun _ => ⟨fun h => by simpa using compl_mem_SL h, compl_mem_SL⟩

end Cslib.Complexity
