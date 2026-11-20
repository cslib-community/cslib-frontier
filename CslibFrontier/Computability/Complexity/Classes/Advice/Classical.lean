/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Advice
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Complexity.Classes.PP

/-!
# Classical deterministic advice classes

One advice word is shared by all inputs of a given length, following the advice operator
[KarpLipton1980] and the exact-length convention [Goldreich2007DraftR2]. Both the logarithmic
and polynomial bounds include the empty input. The pair encoding frames the advice first.

## Main definitions

* `PLog` and `LPoly`: polynomial time with logarithmic advice and logarithmic space with
  polynomial advice.
* `EXPPoly`, `NEXPPoly`, `PPPoly`, `PSPACEPoly`: the corresponding classes with polynomial advice.
* `NEPoly`: nondeterministic time singly exponential in the original input length, with polynomial
  advice. The other classes can measure their resource bounds in the full framed pair length.
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-- Polynomial time with logarithmically bounded advice. -/
@[expose] def PLog : Set (Set (List Bool)) :=
  ⋃ (c : ℕ), PWithAdvice fun n => c * (Nat.log2 n + 1)

/-- Logarithmic space with polynomial advice. Both input and advice are read-only. -/
@[expose] def LPoly : Set (Set (List Bool)) :=
  ⋃ p : Polynomial ℕ, WithAdvice (L (encPair encBits encBits)) p.eval

/-- Deterministic exponential time with polynomial advice. -/
@[expose] def EXPPoly : Set (Set (List Bool)) :=
  ⋃ p : Polynomial ℕ, WithAdvice (EXP (encPair encBits encBits)) p.eval

/-- Nondeterministic exponential time with polynomial advice. -/
@[expose] def NEXPPoly : Set (Set (List Bool)) :=
  ⋃ p : Polynomial ℕ, WithAdvice (NEXP (encPair encBits encBits)) p.eval

/-- Polynomial time with strict majority acceptance and polynomial advice. -/
@[expose] def PPPoly : Set (Set (List Bool)) :=
  ⋃ p : Polynomial ℕ, WithAdvice (PP (encPair encBits encBits)) p.eval

/-- Deterministic polynomial space with polynomial advice. -/
@[expose] def PSPACEPoly : Set (Set (List Bool)) :=
  ⋃ p : Polynomial ℕ, WithAdvice (PSPACE (encPair encBits encBits)) p.eval

/-- Nondeterministic time `O(2 ^ (c * n))` with polynomial advice, where `n` is the length of
the original word. The clock bounds every branch on the advised input. -/
@[expose] def NEPoly : Set (Set (List Bool)) :=
  {A | ∃ (p : Polynomial ℕ) (advice : ℕ → List Bool), (∀ n, (advice n).length = p.eval n) ∧
    ∃ (c d e k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeNTM k Bool State),
      ∀ x,
        let input := encPair encBits encBits (advice x.length, x)
        machine.RunsInTime input (d * 2 ^ (c * x.length) + e) ∧ (x ∈ A ↔ machine.Accepts input)}

end Cslib.Complexity
