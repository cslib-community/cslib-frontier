/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Oracle.Replay

/-!
# Nondeterministic logspace with a write-only oracle tape

`NLOG` is indexed by the oracle language. The query buffer is append-only and is reset
at the call. A transition may choose both its ordinary tape action and the bit it appends
nondeterministically. The reply is one bit and its head is kept at position zero.

## References

* [R. Ladner and N. Lynch, *Relativization of Questions About Log Space Computability*, §§1–2]
  (https://groups.csail.mit.edu/tds/papers/Lynch/mst76.pdf)
* [Complexity Zoo, NLOG](https://complexityzoo.net/Complexity_Zoo:N#nlog)
-/

@[expose] public section

namespace Cslib.Complexity

open Turing MultiTapeMachine Cslib.Probability

variable {α State : Type} {k : ℕ} {input : List Bool}

/-- A choice word reaches `cfg` in a native machine with one language oracle. Invalid
choice words reach no configuration. Zeros after halting are replay padding. -/
def OracleReaches (M : MultiTapeMachine k Bool State Unit List) (oracle : Set (List Bool))
    (word : List ℕ) (cfg : Config k Bool State Unit input) : Prop :=
  ∃ used, OracleComp.interpret (m := Id) (languageOracle oracle)
    (M.replayIndices (M.initialConfig input) word) = some (used, cfg)

/-- Nondeterministic logarithmic space relative to a language oracle, with a polynomial-length
write-only query buffer. Workspace is measured by signed work-head positions on all prefixes.
Since each head starts at zero and moves at most one cell per step, a logarithmic coordinate
bound on each of finitely many tapes is equivalent to a logarithmic visited-cell bound.

The reply head stays at zero so it cannot supply uncharged storage. The resource bounds and
halting condition hold against every oracle language, as in Ladner and Lynch. Each path halts
or gets stuck within a finite horizon. Acceptance against the specified oracle uses only
halted paths with output `[true]`. -/
def NLOG (oracle : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State)
      (M : MultiTapeMachine k Bool State Unit List) (c : ℕ) (p : Polynomial ℕ),
    (∀ (other : Set (List Bool)) a,
      (∀ word (cfg : Config k Bool State Unit (enc a)), OracleReaches M other word cfg →
        (∀ j, (cfg.tapes.workTapePos j).natAbs ≤ c * (Nat.log2 (enc a).length + 1)) ∧
        (cfg.channels ()).queryBuffer.length ≤ p.eval (enc a).length ∧
        (cfg.channels ()).answerPos = 0) ∧
      (∃ t, ∀ word (cfg : Config k Bool State Unit (enc a)), word.length = t →
        OracleReaches M other word cfg → cfg.tapes.Halted)) ∧
    ∀ a, a ∈ A ↔ ∃ (word : List ℕ) (cfg : Config k Bool State Unit (enc a)),
        OracleReaches M oracle word cfg ∧ cfg.tapes.Halted ∧ cfg.tapes.output = [true]}

end Cslib.Complexity
